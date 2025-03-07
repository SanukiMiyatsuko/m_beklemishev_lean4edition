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
        have mem_range : p_m ∈ List.range p' := (List.mem_filter.mp mem_max).left
        refine Nat.lt_trans (List.mem_range.mp mem_range) ?_
        exact parent_lt_seqLength h0 h'

def uncle (seq : List Nat) (x : Nat) (n : Nat) : Nat :=
  let filterd := (parentCandidates seq n).filter (fun i => x < i)
  filterd.min?.getD (seq.length - 1)

def fosterParent (seq : List Nat) (x : Nat) (n : Nat) : Nat :=
  match n with
  | 0 => x
  | n' + 1 => fosterParent seq (uncle seq x n) n'

def innerLoop (seq : List Nat) (p_m limit : Nat) : Option Nat :=
  let results := List.ofFn (fun (i : Fin (limit - 1)) =>
    let n : Nat := i + 1
    match parent seq n, parent seq i with
    | some p_n, some p_pn =>
      if seq.extract p_m (uncle seq p_m n) < seq.extract p_n p_pn
      then
        some (fosterParent seq p_m n)
      else
        none
    | _, _ => none
  )
  results.filterMap id |>.head?

def trueParent (seq : List Nat) (level : Nat) (h0 : seq ≠ []) : Option Nat :=
  match level with
  | 0 => some (seq.length - 2)
  | level' + 1 =>
    let candidates := List.ofFn (fun (i : Fin level) =>
      let m : Nat := i + 1
      match h : parent seq m with
      | none => none
      | some p_m =>
        if seq[p_m]'(parent_lt_seqLength h0 h) < seq.getLast h0 - 1 then
          some p_m
        else
          innerLoop seq p_m (level' ⊓ m)
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
      by
        refine List.getLast?_isSome.mp ?_
        exact
          Std.Tactic.BVDecide.Reflect.Bool.lemma_congr (some seqlast'.succ).isSome
            seq.getLast?.isSome (congrArg Option.isSome h) rfl
    match trueParent seq level seq_ne_emp with
    | none =>
      let bp := initseq ++ [seqlast']
      List.replicate n bp |>.flatten
    | some parent =>
      let gp := seq.take (parent + 1)
      let bp := seq.extract (parent + 1) p_0 ++ [seqlast']
      gp ++ (List.replicate n bp).flatten

#eval expand [1,0,0,1,0,0,0,0,1,0,0,1] 3 4
