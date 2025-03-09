import Mathlib.Init
import Mathlib.Order.MinMax

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

theorem parent_lt_seqLength {m p_m : Nat} {seq : List Nat}
(h0 : seq ≠ []) (h1 : parent seq m = some p_m) : p_m < seq.length :=
  by
    cases m with
    | zero =>
      simp [parent] at h1
      rw [<- h1]
      apply Nat.sub_lt_self
      simp
      exact List.length_pos_iff.mpr h0
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
        have mem_max : p_m ∈ (List.filter (fun i => decide (List.drop i seq < List.drop p' seq)) (List.range p')) :=
          by
            apply List.max?_mem
            exact max_choice
            exact h1
        apply Nat.lt_trans
        apply List.mem_range.mp
        exact (List.mem_filter.mp mem_max).left
        exact parent_lt_seqLength h0 h'

theorem parent_none_up (h0 : n < m) (h1 : parent seq n = none) : parent seq m = none :=
by
  obtain ⟨k, hk⟩ : ∃ k, m = n + 1 + k := Nat.exists_eq_add_of_le h0
  cases k with
  | zero =>
    simp at hk
    rw [hk]
    simp [parent]
    simp [parentCandidates]
    rw [h1]
  | succ k' =>
    let m' := n + 1 + k'
    have m'_def : m' = n + 1 + k' := rfl
    have n_lt_m' : n < m' :=
      by
        rw [m'_def]
        apply Nat.lt_add_right k'
        exact Nat.lt_add_one n
    have ih : parent seq m' = none := parent_none_up n_lt_m' h1
    have m_eq_succm' : m = m'.succ :=
      by
        rw [hk, m'_def]
        rfl
    rw [m_eq_succm']
    simp [parent]
    simp [parentCandidates]
    rw [ih]

theorem parent_some_down (h0 : n < m) (h1 : parent seq m = some p_m) : ∃ p_n, parent seq n = some p_n :=
  by
    by_cases H : ∃ p, parent seq n = some p
    case pos => exact H
    case neg =>
      push_neg at H
      have H_none : parent seq n = none := Option.eq_none_iff_forall_not_mem.mpr H
      have h_up : parent seq m = none := parent_none_up h0 H_none
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
  let results := List.ofFn (fun (i : Fin (limit - 1)) =>
    let n := i.val + 1
    have h2 : ∃ p_n, parent seq n = some p_n :=
      by
        refine parent_some_down ?_ h1
        have h : n = i.val + 1 := rfl
        rw [h]
        refine Nat.lt_of_lt_of_le ?_ h0
        exact Nat.add_lt_of_lt_sub i.is_lt
    let p_n := (parent seq n).get (Option.isSome_iff_exists.mpr h2)
    have h3 : ∃ p_i, parent seq i = some p_i :=
      by
        refine parent_some_down ?_ h1
        refine Nat.lt_of_lt_of_le ?_ h0
        apply Nat.lt_of_add_right_lt
        exact Nat.succ_lt_of_lt_pred i.is_lt
    let p_i := (parent seq i).get (Option.isSome_iff_exists.mpr h3)
    if seq.extract p_m (uncle seq p_m n) < seq.extract p_n p_i then
      some (fosterParent seq p_m n)
    else
      none
  )
  results.filterMap id |>.head?

def trueParent (seq : List Nat) (level : Nat) (h0 : seq ≠ []) : Option Nat :=
  match level with
  | 0 => some (seq.length - 2)
  | level' + 1 =>
    let candidates := List.ofFn (fun (i : Fin level) =>
      let m := i.val + 1
      match h : parent seq m with
      | none => none
      | some p_m =>
        if seq[p_m]'(parent_lt_seqLength h0 h) < seq.getLast h0 - 1 then
          some p_m
        else
          innerLoop (Nat.min_le_right level' m) h
    )
    match candidates.find? (fun c => c.isSome) with
    | some (some candidate) => some candidate
    | some none => none
    | none =>
      match parent seq level with
      | none => none
      | some pLevel => some (fosterParent seq pLevel level')

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
