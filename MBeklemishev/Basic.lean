import Mathlib.Init
import Mathlib.Order.MinMax
import Mathlib.Tactic.Set
import Mathlib.Data.List.Basic

mutual
  def parentCandidates (seq : List Nat) (n : Nat) : List Nat :=
    match n with
    | 0 => List.range seq.length
    | n' + 1 =>
      match parent seq n' with
      | none => []
      | some pp => (List.range pp).filter (fun i => seq.drop i < seq.drop pp)

  def parent (seq : List Nat) (n : Nat) : Option Nat :=
    parentCandidates seq n |>.getLast?
end

theorem parent_lt_seqLength (h0 : seq ≠ []) (h1 : parent seq m = some p_m)
: p_m < seq.length := by
  cases m with
  | zero =>
    simp [parent] at h1
    simp [parentCandidates] at h1
    apply List.length_pos_iff.mpr at h0
    rw [List.getLast?_range seq.length] at h1
    split at h1
    case zero.isTrue => contradiction
    case zero.isFalse =>
      simp at h1
      rw [<-h1]
      exact Nat.sub_one_lt_of_lt h0
  | succ m =>
    simp [parent] at h1
    simp [parentCandidates] at h1
    cases h' : parent seq m with
    | none =>
      rw [h'] at h1
      simp at h1
    | some p' =>
      rw [h'] at h1
      simp_all only [ne_eq]
      apply Nat.lt_trans
      case succ.some.m => exact p'
      case succ.some.h₁ =>
        apply List.mem_range.mp
        apply List.mem_of_mem_filter
        case p =>
          exact fun i => decide (List.drop i seq < List.drop p' seq)
        apply List.mem_of_getLast?
        exact h1
      case succ.some.a =>
        exact parent_lt_seqLength h0 h'

theorem parent_none_up (h0 : n < m) (h1 : parent seq n = none)
: parent seq m = none := by
  obtain ⟨k, hk⟩ : ∃ k, m = n + 1 + k := Nat.exists_eq_add_of_le h0
  cases k with
  | zero =>
    simp at hk
    rw [hk]
    simp [parent]
    simp [parentCandidates]
    rw [h1]
  | succ k' =>
    set m' := n + 1 + k' with m'_def
    have m_eq_m'succ : m = m'.succ := by
      rw [hk, m'_def]
      rfl
    rw [m_eq_m'succ]
    simp [parent]
    simp [parentCandidates]
    have ih : parent seq m' = none := by
      refine parent_none_up ?_ h1
      rw [m'_def]
      apply Nat.lt_add_right k'
      exact Nat.lt_add_one n
    rw [ih]

theorem parent_some_down (h0 : n < m) (h1 : parent seq m = some p_m)
: ∃ p_n, parent seq n = some p_n := by
  by_contra hn
  push_neg at hn
  apply Option.eq_none_iff_forall_not_mem.mpr at hn
  apply parent_none_up h0 at hn
  rw [h1] at hn
  contradiction

def uncle (seq : List Nat) (x n : Nat) : Nat :=
  let filterd := (parentCandidates seq n).filter (fun i => x < i)
  filterd.head?.getD seq.length

def fosterParent (seq : List Nat) (x n : Nat) : Nat :=
  match n with
  | 0 => x
  | n' + 1 => fosterParent seq (uncle seq x n) n'

def innerLoop (h0 : limit ≤ m) (h1 : parent seq m = some p_m) : Option Nat :=
  (List.ofFn (fun (i : Fin (limit - 1)) =>
    let n := i.val + 1
    let p_n := (parent seq n).get (by
      apply Option.isSome_iff_exists.mpr
      refine parent_some_down ?_ h1
      refine Nat.lt_of_lt_of_le ?_ h0
      exact Nat.add_lt_of_lt_sub i.is_lt
    )
    let p_i := (parent seq i).get (by
      apply Option.isSome_iff_exists.mpr
      refine parent_some_down ?_ h1
      apply Fin.val_lt_of_le i
      refine Nat.le_trans ?_ h0
      exact Nat.sub_le limit 1
    )
    if seq.extract p_m (uncle seq p_m n) < seq.extract p_n p_i then
      some (fosterParent seq p_m n)
    else
      none
  )).filterMap id |>.head?

def trueParent (level : Nat) (seq : List Nat) (h0 : seq ≠ []) : Option Nat :=
  match level with
  | 0 => some seq.length
  | level' + 1 =>
    (List.ofFn (fun (i : Fin level) =>
      let m := i.val + 1
      match h : parent seq m with
      | none => none
      | some p_m =>
        if seq[p_m]'(parent_lt_seqLength h0 h) < seq.getLast h0 - 1 then
          some p_m
        else
          match innerLoop (Nat.min_le_right level' m) h with
          | none =>
            if m < level then
              none
            else
              some (fosterParent seq p_m level')
          | some rev => some rev
    )).filterMap id |>.head?

def expand (seq : List Nat) (n : Nat)
(f : (list : List Nat) -> list ≠ [] -> Option Nat) : List Nat :=
  let initSeq := seq.dropLast
  match h : seq.getLast? with
  | none => []
  | some 0 => initSeq
  | some (seqLast' + 1) =>
    have seq_ne_emp : seq ≠ [] :=
      List.getLast?_isSome.mp
        (Std.Tactic.BVDecide.Reflect.Bool.lemma_congr (some seqLast'.succ).isSome
          seq.getLast?.isSome (congrArg Option.isSome h) rfl)
    match f seq seq_ne_emp with
    | none =>
      let bp := initSeq.concat seqLast'
      List.replicate n bp |>.flatten
    | some parent =>
      let gp := initSeq.take (parent + 1)
      let bp := (initSeq.drop (parent + 1)).concat seqLast'
      gp ++ (List.replicate n bp).flatten

def expand_M_bek (seq : List Nat) (n level : Nat) : List Nat :=
  expand seq n (trueParent level)

#eval expand_M_bek [1,0,0,1,0,0,0,0,1,0,0,1] 3 4 -- [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
#eval expand_M_bek [2,1,2] 5 4 -- [2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1]

instance : Std.Irrefl (fun (x y : ℕ) => x < y) :=
  ⟨Nat.lt_irrefl⟩

theorem lt_right_append {α : Type} [LT α] {list0 list1 list2 : List α}
(h0 : list0 < list2) (h1 : list2.length ≤ list0.length)
: list0 ++ list1 < list2 := by
  cases list1_def : list1 with
  | nil => simp_all
  | _ =>
    rw [<-list1_def]
    cases list2 with
    | nil => contradiction
    | cons b bs =>
      cases list0 with
      | nil => contradiction
      | cons a as =>
        simp
        apply List.cons_lt_cons_iff.mpr
        exact match List.cons_lt_cons_iff.mp h0 with
        | Or.inl h => Or.inl h
        | Or.inr ⟨h00, h01⟩ =>
          Or.inr ⟨h00, lt_right_append h01 (Nat.le_of_lt_succ h1)⟩

theorem lt_append_replicate_flatten {α : Type} [LT α]
[i₁ : Trans (fun (x1 x2 : α) => x1 < x2) (fun (x1 x2 : α) => x1 < x2) fun (x1 x2 : α) => x1 < x2] {list1 list2 : List α}
(list0 : List α) (n : Nat) (h0 : list0 ++ list1 < list2) (h1 : list2.length ≤ (list0 ++ list1).length)
: list0 ++ (List.replicate n list1).flatten < list2 := by
  cases n with
  | zero =>
    cases list1_def : list1 with
    | nil => simp_all
    | _ =>
      simp
      trans list0 ++ list1
      · show list0 < list0 ++ list1
        nth_rw 1 [<-List.append_nil list0]
        apply List.append_left_lt
        aesop
      · show list0 ++ list1 < list2
        exact h0
  | succ n' =>
    simp [List.replicate]
    rw [<-List.append_assoc]
    exact lt_right_append h0 h1

theorem expand_mon_dec (h0 : seq ≠ [])
: expand seq n f < seq := by
  simp [expand]
  set initSeq := seq.dropLast with initSeq_def
  split
  case h_1 => simp_all
  case h_2 =>
    induction seq with
    | nil => contradiction
    | cons a as ih =>
      cases as with
      | nil =>
        simp at initSeq_def
        rw [initSeq_def]
        simp
      | cons b bs => simp_all
  case h_3 seqLast' seqLast'_def =>
    let seqlast := seq.getLast h0
    set bp' := initSeq ++ [seqLast'] with bp'_def
    have bp'_lt_seq : bp' < seq := by
      have h : seq = initSeq ++ [seqLast'.succ] := by
        rw [<-(List.getLast_eq_iff_getLast?_eq_some h0).mpr seqLast'_def]
        exact Eq.symm (List.dropLast_concat_getLast h0)
      rw [h, bp'_def]
      apply List.append_left_lt
      apply List.cons_lt_cons_iff.mpr
      left
      exact Nat.lt_add_one seqLast'
    have seq_length_le_bp'_length : seq.length ≤ bp'.length := by
      rw [bp'_def, List.length_append, List.length_dropLast seq]
      simp
      apply Nat.le_of_eq
      refine Eq.symm (Nat.sub_one_add_one_eq_of_pos ?_)
      exact List.length_pos_iff.mpr h0
    split
    case h_1 =>
      simp [List.replicate]
      exact lt_append_replicate_flatten [] n bp'_lt_seq seq_length_le_bp'_length
    case h_2 parent h8 =>
      let gp := initSeq.take (parent + 1)
      set bp := (initSeq.drop (parent + 1)) ++ [seqLast'] with bp_def
      have bp'_eq_gp_append_bp : bp' = gp ++ bp := by
        rw [bp_def, <-List.append_assoc, List.take_append_drop (parent + 1) initSeq]
      rw [bp'_eq_gp_append_bp] at bp'_lt_seq
      rw [bp'_eq_gp_append_bp] at seq_length_le_bp'_length
      exact lt_append_replicate_flatten gp n bp'_lt_seq seq_length_le_bp'_length
