import Mathlib.Init
import Mathlib.Order.MinMax

mutual
  def pSet (seq : List Nat) (n : Nat) : List Nat :=
    match n with
    | 0 => []
    | n + 1 =>
      match p seq n with
      | none => []
      | some ppn => (List.range ppn).filter (fun i => seq.drop i < seq.drop ppn)

  def p (seq : List Nat) (n : Nat) : Option Nat :=
    if n = 0
    then some (seq.length - 1)
    else (pSet seq n).max?
end

theorem p_lt_seqLength {m : Nat} {seq : List Nat}
(p_m : Nat) (h0 : seq ≠ []) (h1 : p seq m = some p_m) : p_m < seq.length :=
  by
    cases m with
    | zero =>
      simp [p] at h1
      rw [<- h1]
      apply Nat.sub_lt_self
      simp
      exact List.length_pos_iff.mpr h0
    | succ m' =>
      simp [p] at h1
      simp [pSet] at h1
      cases h' : p seq m' with
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
        have mem_range : p_m ∈ List.range p' :=
          by exact (List.mem_filter.mp mem_max).left
        exact Nat.lt_trans (List.mem_range.mp mem_range) (p_lt_seqLength p' h0 h')

def u (seq : List Nat) (x n : Nat) : Nat :=
  let filterd := (pSet seq n).filter (fun i => x < i)
  filterd.min?.getD (seq.length - 1)

def fp (seq : List Nat) (x n : Nat) : Nat :=
  match n with
  | 0 => x
  | n' + 1 => fp seq (u seq x n) n'

def innerLoop (seq : List Nat) (pList : List (Option Nat)) (p_m limit k : Nat)
(h0 : k ≤ limit) (h1 : limit ≤ pList.length) (h2 : limit - k ≤ pList.length) : Option Nat :=
  let n := limit - k
  have n_def : n = limit - k := rfl
  match k with
  | 0 => none
  | k + 1 =>
    have k_lt_lim : k < limit :=
      by exact Nat.lt_of_succ_le h0
    have lim_sub_k'_le_pListLen : limit - k ≤ pList.length :=
      by exact Nat.le_trans (Nat.sub_le limit k) h1
    have n_lt_pListLen : n < pList.length :=
      by
        rw [n_def, Nat.sub_succ]
        apply Nat.lt_of_succ_lt_succ
        rw [Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt k_lt_lim)]
        apply Nat.lt_succ_of_le lim_sub_k'_le_pListLen
    match pList[n]'n_lt_pListLen, pList[n-1] with
    | some pn, some ppn =>
      if seq.extract p_m (u seq p_m n) < seq.extract pn ppn
      then some (fp seq p_m n)
      else innerLoop seq pList p_m limit k (Nat.le_of_lt k_lt_lim) h1 lim_sub_k'_le_pListLen
    | _, _ => none

def tp (seq : List Nat) (pList : List (Option Nat)) (k : Nat)
(h0 : seq ≠ []) (h1 : k < pList.length)
(h2 : ∀(i : Fin pList.length) (p_i : Nat), pList[i] = some p_i -> p_i < seq.length) : Option Nat :=
  let m := pList.length - 1 - k
  have m_def : m = pList.length - 1 - k := rfl
  match pList.length - 1 with
  | 0 => some (seq.length - 2)
  | level + 1 =>
    have m_lt_plistLen : m < pList.length :=
      by
        rw [m_def]
        exact Nat.sub_one_sub_lt_of_lt h1
    match pListm_eq_some_pm : pList[m]'m_lt_plistLen with
    | none => none
    | some p_m =>
        if seq[p_m]'(h2 ⟨m, m_lt_plistLen⟩ p_m pListm_eq_some_pm) < seq.getLast h0 - 1
        then some p_m
        else let limit := level ⊓ m
          have lim_def : limit = level ⊓ m := rfl
          have lim_le_pListLen : limit ≤ pList.length :=
            by
              rw [lim_def]
              exact Nat.le_trans (min_le_right level m) (Nat.le_of_lt m_lt_plistLen)
          have lim_sub_lim_add_1_le_pListList : limit - (limit - 1) ≤ pList.length :=
            by
              cases limit with
              | zero => simp
              | succ limit =>
                refine Nat.sub_le_iff_le_add'.mpr ?_
                refine Nat.add_le_add ?_ ?_
                simp
                exact Nat.one_le_of_lt h1
          match innerLoop seq pList p_m limit (limit - 1) (Nat.pred_le limit) lim_le_pListLen lim_sub_lim_add_1_le_pListList with
          | some rev => some rev
          | none =>
            match k with
            | 0 => some (fp seq p_m level)
            | k + 1 => tp seq pList k h0 (Nat.lt_of_succ_lt h1) h2

def expand (seq : List Nat) (level n : Nat) : List Nat :=
  let p_0 := seq.length - 1
  match h : seq with
  | [] => []
  | x :: xs =>
    have seq_ne_emp : seq ≠ [] :=
      by
        rw [h]
        exact List.cons_ne_nil x xs
    match seq.getLast seq_ne_emp with
    | 0 => seq.take p_0
    | seqlast + 1 =>
      let pList := (List.range (level + 1)).map (p seq)
      have pList_def : pList = (List.range (level + 1)).map (p seq) := rfl
      have pList_is_def (i : Fin pList.length) (p_i : Nat) (hh : pList[i] = some p_i) : p_i < seq.length :=
        by
          simp [pList_def] at hh
          have h : p seq i.val = some p_i :=
            by simpa using hh
          exact p_lt_seqLength p_i seq_ne_emp h
      have level_pred_lt_pListLen : level - 1 < pList.length :=
        by
          have h : pList.length = level + 1 :=
            by simp [pList]
          rw [h]
          exact Nat.sub_lt_succ level 1
      match tp seq pList (level - 1) seq_ne_emp level_pred_lt_pListLen pList_is_def with
      | none =>
        let bp := seq.take p_0 ++ [seqlast]
        (List.replicate n bp).flatten
      | some parent =>
        let gp := seq.take (parent + 1)
        let bp := seq.extract (parent + 1) p_0 ++ [seqlast]
        gp ++ (List.replicate n bp).flatten

#eval expand [2,1,1,1,2] 4 4 -- [1, 0, 1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0]
