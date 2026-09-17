import Submission.E8Character

/-!
# A kernel-evaluable dominant-conjugate algorithm

`Submission.E8Character.dc` is defined through `Finset.min'`/`Finset.filter`, whose reduction is not
available to the kernel: `decide` on goals mentioning `dc` gets stuck or blows up.  The numerical
certification of the character of `L(ω₁+ω₈)` needs to *evaluate* dominant conjugates, so this file
provides a variant `dcX` built only from `List` operations and `Int` comparisons, proves
`dcX = dc`, and inherits all the structural lemmas about `dc`.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
set_option linter.unusedSimpArgs false

namespace Submission.E8Orbit

open Submission.WeylRoots Submission.WeylReflect Submission.WeylWeights
open Submission.E8Character

/-- Minimum of the negative values of `v` over the list `l`, computed recursively. -/
def pickMinNeg : List (Fin 8) → (Fin 8 → ℤ) → Option (Fin 8)
  | [], _ => none
  | i :: l, v =>
    if v i < 0 then
      match pickMinNeg l v with
      | none => some i
      | some j => some (min i j)
    else pickMinNeg l v

lemma pickMinNeg_none : ∀ (l : List (Fin 8)) (v : Fin 8 → ℤ), pickMinNeg l v = none →
    ∀ j ∈ l, 0 ≤ v j := by
  intro l
  induction l with
  | nil => intro v _ j hj; exact absurd hj List.not_mem_nil
  | cons i l ih =>
    intro v h j hj
    rw [pickMinNeg] at h
    by_cases hi : v i < 0
    · rw [if_pos hi] at h
      split at h <;> exact absurd h (by simp)
    · rw [if_neg hi] at h
      rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · exact ih v h j hj

lemma pickMinNeg_some : ∀ (l : List (Fin 8)) (v : Fin 8 → ℤ) {k : Fin 8},
    pickMinNeg l v = some k → v k < 0 ∧ k ∈ l ∧ ∀ j ∈ l, v j < 0 → k ≤ j := by
  intro l
  induction l with
  | nil => intro v k h; exact absurd h (by simp [pickMinNeg])
  | cons i l ih =>
    intro v k h
    rw [pickMinNeg] at h
    by_cases hi : v i < 0
    · rw [if_pos hi] at h
      split at h
      · rw [Option.some.injEq] at h
        subst h
        refine ⟨hi, List.mem_cons_self .., ?_⟩
        intro j hj hjneg
        rcases List.mem_cons.mp hj with rfl | hj
        · exact le_rfl
        · exact absurd hjneg (by
            have h0 := pickMinNeg_none l v ‹pickMinNeg l v = none› j hj
            omega)
      · rename_i j0 hj0
        rw [Option.some.injEq] at h
        subst h
        obtain ⟨hj0neg, hj0mem, hmin⟩ := ih v hj0
        have hminneg : v (min i j0) < 0 := by
          rcases le_total i j0 with hle | hle
          · rwa [min_eq_left hle]
          · rwa [min_eq_right hle]
        have hmem : min i j0 ∈ (i :: l) := by
          rcases le_total i j0 with hle | hle
          · rw [min_eq_left hle]; exact List.mem_cons_self
          · rw [min_eq_right hle]; exact List.mem_cons_of_mem i hj0mem
        refine ⟨hminneg, hmem, ?_⟩
        intro j hj hjneg
        rcases List.mem_cons.mp hj with rfl | hj
        · exact min_le_left _ _
        · exact le_trans (min_le_right _ _) (hmin j hj hjneg)
    · rw [if_neg hi] at h
      obtain ⟨hkneg, hkmem, hmin⟩ := ih v h
      refine ⟨hkneg, List.mem_cons_of_mem i hkmem, ?_⟩
      intro j hj hjneg
      rcases List.mem_cons.mp hj with rfl | hj
      · exact absurd hjneg hi
      · exact hmin j hj hjneg

/-- The kernel-evaluable "first negative coordinate": the minimum index `i` with `v i < 0`. -/
def pickNegF (v : Fin 8 → ℤ) : Option (Fin 8) := pickMinNeg (List.finRange 8) v

lemma pickNegF_eq_none_iff (v : Fin 8 → ℤ) : pickNegF v = none ↔ ∀ i, 0 ≤ v i := by
  constructor
  · intro h i
    exact pickMinNeg_none _ v h i (List.mem_finRange i)
  · intro h
    rcases hp : pickNegF v with _ | i
    · rfl
    · exact absurd (h i) (by have := (pickMinNeg_some _ v hp).1; omega)

lemma pickNegF_spec {v : Fin 8 → ℤ} {i : Fin 8} (h : pickNegF v = some i) : v i < 0 :=
  (pickMinNeg_some _ v h).1

lemma pickNegF_min {v : Fin 8 → ℤ} {i : Fin 8} (h : pickNegF v = some i) :
    ∀ j, v j < 0 → i ≤ j :=
  fun j hj => (pickMinNeg_some _ v h).2.2 j (List.mem_finRange j) hj

lemma pickNegF_eq_none {v : Fin 8 → ℤ} (h : ∀ i, 0 ≤ v i) : pickNegF v = none :=
  (pickNegF_eq_none_iff v).mpr h

lemma pickNegF_eq_some {v : Fin 8 → ℤ} (h : ∃ i, v i < 0) :
    pickNegF v = some (pickNeg v h) := by
  have hr : ∃ i : Fin 8, pickNegF v = some i := by
    by_contra hc
    simp only [not_exists] at hc
    have hn : pickNegF v = none := by
      rcases hp : pickNegF v with _ | i
      · rfl
      · exact absurd (hc i hp) (by simp)
    exact h.elim fun i hi => absurd ((pickNegF_eq_none_iff v).mp hn i) (by omega)
  obtain ⟨i, hi⟩ := hr
  have hmem : i ∈ Finset.univ.filter (fun k : Fin 8 => v k < 0) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ i, pickNegF_spec hi⟩
  have h1 : pickNeg v h ≤ i :=
    (Finset.isLeast_min' (Finset.univ.filter (fun k : Fin 8 => v k < 0)) _).2 hmem
  have h2 : i ≤ pickNeg v h := pickNegF_min hi _ (pickNeg_spec v h)
  have heq : pickNeg v h = i := le_antisymm h1 h2
  rw [heq]
  exact hi

/-- One step of the reflection algorithm. -/
def dcStep (v : Fin 8 → ℤ) : Fin 8 → ℤ :=
  match pickNegF v with
  | some i => sref i v
  | none => v

/-- `n` steps of the reflection algorithm. -/
def dcl : ℕ → (Fin 8 → ℤ) → (Fin 8 → ℤ)
  | 0, v => v
  | n + 1, v => match pickNegF v with
      | some i => dcl n (sref i v)
      | none => v

/-- The kernel-evaluable dominant conjugate (`130` steps are more than enough: `negCount ≤ 120`). -/
def dcX (v : Fin 8 → ℤ) : Fin 8 → ℤ := dcl 130 v

lemma dcl_eq_foldl (n : ℕ) (v : Fin 8 → ℤ) :
    dcl n v = (dcListAux n v).foldl (fun w i => sref i w) v := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [dcl, dcListAux]
    by_cases h : ∃ i, v i < 0
    · rw [dif_pos h, pickNegF_eq_some h]
      exact ih (sref (pickNeg v h) v)
    · rw [dif_neg h]
      have hn : pickNegF v = none := pickNegF_eq_none fun i => by
        by_contra hi
        exact h ⟨i, by omega⟩
      rw [hn]
      rfl

lemma PD_card : PD.card = 120 := by decide

lemma negCount_le_120 (v : Fin 8 → ℤ) : negCount v ≤ 120 := by
  have h : negCount v ≤ PD.card := Finset.card_le_card (Finset.filter_subset _ _)
  rw [PD_card] at h
  omega

lemma dcListAux_eq_of_le : ∀ (m : ℕ) (v : Fin 8 → ℤ), negCount v = m → ∀ n : ℕ,
    negCount v ≤ n → dcListAux n v = dcListAux (negCount v) v := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro v hv n hn
    by_cases h : ∃ i, v i < 0
    · have hpos : 1 ≤ negCount v := by
        have hlt := negCount_sref_lt h
        rw [negCount_sref _ _ (pickNeg_spec v h)] at hlt
        omega
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      obtain ⟨n'', hn''⟩ : ∃ n'', negCount v = n'' + 1 := ⟨negCount v - 1, by omega⟩
      rw [dcListAux, dif_pos h]
      conv_rhs =>
        rw [hn'']
        rw [dcListAux, dif_pos h]
      congr 1
      have hmin : negCount (sref (pickNeg v h) v) = negCount v - 1 :=
        negCount_sref _ _ (pickNeg_spec v h)
      have hlt : negCount (sref (pickNeg v h) v) < m := by omega
      have hle : negCount (sref (pickNeg v h) v) ≤ n' := by omega
      have hres := ih _ hlt _ rfl n' hle
      rw [hres]
      congr 1
      omega
    · have hdom : Dominant v := fun i => by
        by_contra hi
        exact h ⟨i, by omega⟩
      rw [dcListAux_eq_nil_of_dominant hdom n, dcListAux_eq_nil_of_dominant hdom (negCount v)]

/-- **The kernel-evaluable conjugate equals `dc`.** -/
theorem dcX_eq_dc (v : Fin 8 → ℤ) : dcX v = dc v := by
  have h1 : dcl 130 v = (dcListAux 130 v).foldl (fun w i => sref i w) v := dcl_eq_foldl 130 v
  have h2 : dcListAux 130 v = dcListAux (negCount v) v :=
    dcListAux_eq_of_le _ v rfl 130 (le_trans (negCount_le_120 v) (by norm_num))
  rw [dcX, h1, h2]
  rfl

lemma dcX_dominant (v : Fin 8 → ℤ) : Dominant (dcX v) := by
  rw [dcX_eq_dc]; exact dc_dominant v

lemma dcX_sub_posCon (v : Fin 8 → ℤ) : posCon (dcX v - v) := by
  rw [dcX_eq_dc]; exact dc_sub_posCon v

lemma dcX_idem (v : Fin 8 → ℤ) : dcX (dcX v) = dcX v := by
  rw [dcX_eq_dc, dcX_eq_dc]; exact dc_idem v

lemma dcX_eq_self_of_dominant {v : Fin 8 → ℤ} (h : Dominant v) : dcX v = v := by
  rw [dcX_eq_dc]; exact dc_eq_self_of_dominant h

lemma WConj_dcX (v : Fin 8 → ℤ) : WConj v (dcX v) := by
  rw [dcX_eq_dc]
  exact dc_mem_WConj v

end Submission.E8Orbit
