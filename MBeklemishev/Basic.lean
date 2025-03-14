import Mathlib.Init
import Mathlib.Order.MinMax
import Mathlib.Data.List.Basic

mutual
  def parentCandidates (seq : List Nat) (n : Nat) : List Nat :=
    match n with
    | 0 => []
    | n' + 1 =>
      match parent seq n' with
      | none => []
      | some pp => (List.range pp).filter (fun i => seq.drop i < seq.drop pp)

  def parent (seq : List Nat) (n : Nat) : Option Nat :=
    if n = 0 then
      some (seq.length - 1)
    else
      parentCandidates seq n |>.max?
end

theorem parent_lt_seqLength (h0 : seq ≠ []) (h1 : parent seq m = some p_m) : p_m < seq.length := by
  cases m with
  | zero =>
    simp [parent] at h1
    rw [<- h1]
    apply Nat.sub_lt_self
    simp
    exact List.length_pos_of_ne_nil h0
  | succ m =>
    simp [parent] at h1
    simp [parentCandidates] at h1
    cases h' : parent seq m with
    | none =>
      rw [h'] at h1
      simp at h1
    | some p' =>
      rw [h'] at h1
      simp at h1
      apply Nat.lt_trans
      apply List.mem_range.mp
      apply List.mem_of_mem_filter
      apply List.max?_mem
      case succ.some.h₁.h.min_eq_or =>
        exact max_choice
      case succ.some.h₁.h.a =>
        exact h1
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
  by_cases H : ∃ p, parent seq n = some p
  case pos => exact H
  case neg =>
    push_neg at H
    have h_up : parent seq m = none := by
      apply parent_none_up h0
      exact Option.eq_none_iff_forall_not_mem.mpr H
    rw [h1] at h_up
    contradiction

def uncle (seq : List Nat) (x : Nat) (n : Nat) : Nat :=
  let filterd := (parentCandidates seq n).filter (fun i => x < i)
  filterd.min?.getD (seq.length - 1)

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

def trueParent (seq : List Nat) (level : Nat) (h0 : seq ≠ []) : Option Nat :=
  match level with
  | 0 => some (seq.length - 2)
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

def expand (seq : List Nat) (n level : Nat) : List Nat :=
  let p_0 := seq.length - 1
  let initseq := seq.take p_0
  match h : seq.getLast? with
  | none => []
  | some 0 => initseq
  | some (seqlast' + 1) =>
    have seq_ne_emp : seq ≠ [] :=
      List.getLast?_isSome.mp
        (Std.Tactic.BVDecide.Reflect.Bool.lemma_congr (some seqlast'.succ).isSome
          seq.getLast?.isSome (congrArg Option.isSome h) rfl)
    match trueParent seq level seq_ne_emp with
    | none =>
      let bp := initseq ++ [seqlast']
      List.replicate n bp |>.flatten
    | some parent =>
      let gp := seq.take (parent + 1)
      let bp := seq.extract (parent + 1) p_0 ++ [seqlast']
      gp ++ (List.replicate n bp).flatten

#eval expand [1,0,0,1,0,0,0,0,1,0,0,1] 3 4 -- [1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
#eval expand [2,1,2] 5 4 -- [2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1]
