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

theorem parent_lt_seqLength (h0 : seq ≠ []) (h1 : parent seq m = some p_m) : p_m < seq.length := by
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

theorem parent_none_up (h0 : n < m) (h1 : parent seq n = none) : parent seq m = none := by
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
    have m_eq_succm' : m = m'.succ := by
      rw [hk, m'_def]
      rfl
    rw [m_eq_succm']
    simp [parent]
    simp [parentCandidates]
    have ih : parent seq m' = none := by
      refine parent_none_up ?_ h1
      rw [m'_def]
      apply Nat.lt_add_right k'
      exact Nat.lt_add_one n
    rw [ih]

theorem parent_some_down (h0 : n < m) (h1 : parent seq m = some p_m) : ∃ p_n, parent seq n = some p_n := by
  by_contra hn
  push_neg at hn
  apply Option.eq_none_iff_forall_not_mem.mpr at hn
  apply parent_none_up h0 at hn
  rw [h1] at hn
  contradiction

def uncle (seq : List Nat) (x : Nat) (n : Nat) : Nat :=
  let filterd := (parentCandidates seq n).filter (fun i => x < i)
  filterd.head?.getD seq.length

def fosterParent (seq : List Nat) (x : Nat) (n : Nat) : Nat :=
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
  let initseq := seq.dropLast
  match h : seq.getLast? with
  | none => []
  | some 0 => initseq
  | some (seqlast' + 1) =>
    have seq_ne_emp : seq ≠ [] :=
      List.getLast?_isSome.mp
        (Std.Tactic.BVDecide.Reflect.Bool.lemma_congr (some seqlast'.succ).isSome
          seq.getLast?.isSome (congrArg Option.isSome h) rfl)
    match f seq seq_ne_emp with
    | none =>
      let bp := initseq.concat seqlast'
      List.replicate n bp |>.flatten
    | some parent =>
      let gp := initseq.take (parent + 1)
      let bp := (initseq.drop (parent + 1)).concat seqlast'
      gp ++ (List.replicate n bp).flatten

def expand_M_bek (seq : List Nat) (n level : Nat) : List Nat :=
  expand seq n (trueParent level)

#eval expand_M_bek [1,0,0,1,0,0,0,0,1,0,0,1] 3 4 -- [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
#eval expand_M_bek [2,1,2] 5 4 -- [2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1]

instance : Std.Irrefl (fun (x y : ℕ) => x < y) :=
  ⟨Nat.lt_irrefl⟩

theorem lt_right_append (list0 list1 list2 : List Nat) (h0 : list0 < list2) (h1 : list2.length ≤ list0.length) : list0 ++ list1 < list2 := by
  by_cases h2 : list1 = []
  case pos =>
    rw [h2]
    simp_all
  case neg =>
    rw [<-ne_eq] at h2
    have h3 : [] < list1 := by
      cases list1 with
      | nil => simp_all
      | cons _ _ => simp
    cases list2 with
    | nil => contradiction
    | cons b bs =>
      cases list0 with
      | nil => contradiction
      | cons a as =>
        simp
        apply List.cons_lt_cons_iff.mpr
        apply List.cons_lt_cons_iff.mp at h0
        cases h0 with
        | inl h0 =>
          left
          exact h0
        | inr h0 =>
          obtain ⟨h00, h01⟩ := h0
          right
          constructor
          case cons.cons.inr.intro.h.left =>
            exact h00
          case cons.cons.inr.intro.h.right =>
            simp at h1
            exact lt_right_append as list1 bs h01 h1

theorem lt_append_replicate_flatten (list0 list1 list2 : List Nat) (n : Nat) (h0 : list0 ++ list1 < list2) (h1 : list2.length ≤ (list0 ++ list1).length) : list0 ++ (List.replicate n list1).flatten < list2 := by
  cases n with
  | zero =>
    by_cases h2 : list1 = []
    case pos =>
      rw [h2] at h0
      simp_all
    case neg =>
      rw [<-ne_eq] at h2
      have h2 : [] < list1 := by
        cases list1 with
        | nil => simp_all
        | cons _ _ => simp
      have h4 : list0 < list0 ++ list1 := by
        nth_rw 1 [<-List.append_nil list0]
        exact List.append_left_lt h2
      simp
      exact List.lt_trans h4 h0
  | succ n' =>
    simp [List.replicate]
    rw [<-List.append_assoc]
    exact lt_right_append (list0 ++ list1) ((List.replicate n' list1).flatten) list2 h0 h1

-- expandの単調減少性
theorem expand_mon_dec (h0 : seq ≠ []) : expand seq n f < seq := by
  simp [expand]
  set initseq := seq.dropLast with h1
  have h2 : initseq < seq := by
    induction seq with
    | nil => contradiction
    | cons a as ih =>
      cases as with
      | nil =>
        simp at h1
        rw [h1]
        simp
      | cons b bs => simp_all
  split
  case h_1 => simp_all
  case h_2 => exact h2
  case h_3 seqlast' h3 =>
    set seqlast := seq.getLast h0
    have h4 : seqlast = seqlast'.succ :=
      (List.getLast_eq_iff_getLast?_eq_some h0).mpr h3
    set bp' := initseq ++ [seqlast'] with h5
    have h6 : bp' < seq := by
      have h6 : seq = initseq ++ [seqlast'.succ] := by
        rw [<-h4]
        exact Eq.symm (List.dropLast_concat_getLast h0)
      rw [h6, h5]
      apply List.append_left_lt
      apply List.cons_lt_cons_iff.mpr
      left
      exact Nat.lt_add_one seqlast'
    have h7 : bp'.length = seq.length := by
      rw [h5, List.length_append, List.length_dropLast seq]
      simp
      apply Nat.sub_one_add_one_eq_of_pos
      exact List.length_pos_iff.mpr h0
    split
    case h_1 =>
      simp [List.replicate]
      exact lt_append_replicate_flatten [] bp' seq n h6 (Nat.le_of_eq (id (Eq.symm h7)))
    case h_2 parent h8 =>
      set gp := initseq.take (↑parent + 1) with h9
      set bp := (initseq.drop (↑parent + 1)) ++ [seqlast'] with h10
      have h11 : gp ++ initseq.drop (↑parent + 1) = initseq :=
        List.take_append_drop (↑parent + 1) initseq
      have h12 : bp' = gp ++ bp := by
        rw [h10, <-List.append_assoc, h11]
      rw [h12] at h6
      rw [h12] at h7
      exact lt_append_replicate_flatten gp bp seq n h6 (Nat.le_of_eq (id (Eq.symm h7)))
