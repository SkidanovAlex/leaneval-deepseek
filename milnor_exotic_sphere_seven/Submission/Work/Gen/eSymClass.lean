import Mathlib
import Submission.Work.Gen.eSymDef
import Submission.Work.LerayHirsch.Series
import Submission.Work.Whitney.ChernRelDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# The elementary symmetric classes of a family of degree-`2` cohomology classes

`Work.Gen.eSym n M k` is the `k`-th elementary symmetric class of the first Chern classes of a
family of complex **line bundles** `M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι`.
For the Chern-root relation one needs the *same* construction for a family of arbitrary degree-`2`
cohomology classes, because the first Chern classes of the twisted summands
`ℓ^* ⊗ π^*M i` are `π^*c₁(M i) - ζ`, i.e. a pullback minus `ζ`, and the expansion

  `∏_i (t_i - ζ) = Σ_k (-1)^{n-k} e_k(t) ζ^{n-k}`

has to be performed at the level of classes.

This module contains the definition `Work.Gen.eSymC`, its recursion, its relation to `Work.Gen.eSym`
(`Work.Gen.eSym_eq_eSymC`), its naturality under a pullback (`Work.Gen.eSymC_CohMap`) and its
vanishing above the number of variables (`Work.Gen.eSymC_above`), together with two elementary
lemmas on the graded product `Work.Whitney.cupChern` used by the consumers
(`Work.Gen.cupChern_zsmul_right`, `Work.Gen.zPow_neg`).
-/

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The `k`-th elementary symmetric class of a family of degree-`2` classes**: the recursion
`eSymC (n+1) t k = eSymC n (t ∘ castSucc) k + t (last n) ⌣ eSymC n (t ∘ castSucc) (k-1)` with
`eSymC 0 t k = [k = 0]`.  This is `Work.Gen.eSym` with the first Chern classes of the line bundles
replaced by arbitrary degree-`2` classes. -/
noncomputable def eSymC {P : Type} [TopologicalSpace P] :
    (n : ℕ) → (Fin n → Coh ℤ 2 P) → (k : ℕ) → Coh ℤ (2 * k) P
  | 0, _, k =>
      if h : k = 0 then cohTransport (by omega : 0 = 2 * k)
        (Work.Cohomology.oneH ℤ (Work.Whitney.ssB P)) else 0
  | n + 1, t, k =>
      eSymC n (fun i => t (Fin.castSucc i)) k +
        (if h : 1 ≤ k then
          cohTransport (by omega : 2 * (1 + (k - 1)) = 2 * k)
            (Work.Whitney.cupChern 1 (k - 1) (t (Fin.last n))
              (eSymC n (fun i => t (Fin.castSucc i)) (k - 1)))
         else 0)

/-- The recursion of `eSymC` in the successor case. -/
theorem eSymC_succ {P : Type} [TopologicalSpace P] {n : ℕ}
    (t : Fin (n + 1) → Coh ℤ 2 P) (k : ℕ) :
    eSymC (n + 1) t k = eSymC n (fun i => t (Fin.castSucc i)) k +
      (if _h : 1 ≤ k then
        cohTransport (by omega : 2 * (1 + (k - 1)) = 2 * k)
          (Work.Whitney.cupChern 1 (k - 1) (t (Fin.last n))
            (eSymC n (fun i => t (Fin.castSucc i)) (k - 1)))
       else 0) := rfl

/-- **The class of the empty family**: `eSymC 0 t k` is the unit class in degree `0` and zero
elsewhere. -/
theorem eSymC_zero {P : Type} [TopologicalSpace P] {k : ℕ} (t : Fin 0 → Coh ℤ 2 P) :
    eSymC 0 t k = if h : k = 0 then cohTransport (by omega : 0 = 2 * k)
        (Work.Cohomology.oneH ℤ (Work.Whitney.ssB P)) else 0 := rfl

theorem eSymC_zero_rank {P : Type} [TopologicalSpace P] {k : ℕ} (hk : k ≠ 0)
    (t : Fin 0 → Coh ℤ 2 P) : eSymC 0 t k = 0 := by
  rw [eSymC_zero]; simp [hk]

/-- **`eSymC` in degree `0` is the unit class**. -/
theorem eSymC_zero_index {P : Type} [TopologicalSpace P] {n : ℕ} (t : Fin n → Coh ℤ 2 P) :
    eSymC n t 0 = cohTransport (by omega : 0 = 2 * 0)
      (Work.Cohomology.oneH ℤ (Work.Whitney.ssB P)) := by
  induction n with
  | zero => rw [eSymC_zero]; simp
  | succ n ih =>
    rw [eSymC_succ, ih, dif_neg (by omega : ¬ (1 ≤ 0))]
    simp

/-- **`eSymC` vanishes above the number of variables**. -/
theorem eSymC_above {P : Type} [TopologicalSpace P] {n : ℕ} (t : Fin n → Coh ℤ 2 P) {k : ℕ}
    (hk : n < k) : eSymC n t k = 0 := by
  induction n generalizing k with
  | zero => exact eSymC_zero_rank (by omega) t
  | succ n ih =>
    have h1 : eSymC n (fun i => t (Fin.castSucc i)) k = 0 := ih _ (by omega)
    have h2 : eSymC n (fun i => t (Fin.castSucc i)) (k - 1) = 0 := ih _ (by omega)
    rw [eSymC_succ, dif_pos (by omega : 1 ≤ k), h1, h2]
    simp [Work.Whitney.cupChern_def, Work.Cohomology.cupH'_zero_right,
      Work.Thom.cohTransport_zero]

/-- **`Work.Gen.eSym` is `Work.Gen.eSymC` of the first Chern classes.** -/
theorem eSym_eq_eSymC {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι] {n : ℕ}
    (M : Fin n → VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin 1)) ι) (k : ℕ) :
    eSym n M k = eSymC (P := B) n (fun i => chernClass 1 1 (M i)) k := by
  induction n generalizing k with
  | zero =>
    rw [eSym, eSymC_zero]
  | succ n ih =>
    rw [eSym_succ, eSymC_succ]
    have hhead : eSym n (fun i => M (Fin.castSucc i)) k
        = eSymC n (fun i => chernClass 1 1 (M (Fin.castSucc i))) k :=
      ih (fun i => M (Fin.castSucc i)) k
    have htail : eSym n (fun i => M (Fin.castSucc i)) (k - 1)
        = eSymC n (fun i => chernClass 1 1 (M (Fin.castSucc i))) (k - 1) :=
      ih (fun i => M (Fin.castSucc i)) (k - 1)
    rw [hhead]
    congr 1
    by_cases h : 1 ≤ k
    · rw [dif_pos h, dif_pos h, htail]
    · rw [dif_neg h, dif_neg h]

/-- **Naturality of `eSymC` under a pullback.** -/
theorem eSymC_CohMap {P Q : Type} [TopologicalSpace P] [TopologicalSpace Q] (f : C(P, Q)) {n : ℕ}
    (t : Fin n → Coh ℤ 2 Q) (k : ℕ) :
    eSymC (P := P) n (fun i => (CohMap f ℤ 2).hom (t i)) k
      = (CohMap f ℤ (2 * k)).hom (eSymC (P := Q) n t k) := by
  induction n generalizing k with
  | zero =>
    rw [eSymC_zero, eSymC_zero]
    by_cases h : k = 0
    · subst h
      rw [dif_pos rfl, dif_pos rfl, cohTransport_CohMap]
      congr 1
      exact (CohMap_oneH f).symm
    · rw [dif_neg h, dif_neg h, map_zero]
  | succ n ih =>
    rw [eSymC_succ, eSymC_succ, map_add]
    have hhead : eSymC n (fun i => (CohMap f ℤ 2).hom (t (Fin.castSucc i))) k
        = (CohMap f ℤ (2 * k)).hom (eSymC n (fun i => t (Fin.castSucc i)) k) :=
      ih _ k
    rw [hhead]
    congr 1
    by_cases h : 1 ≤ k
    · rw [dif_pos h, dif_pos h, cohTransport_CohMap, Work.Whitney.cupChern_CohMap]
      have hlast : ((CohMap f ℤ 2).hom (t (Fin.last n)) : Coh ℤ (2 * 1) P)
          = (CohMap f ℤ (2 * 1)).hom (t (Fin.last n)) := rfl
      have hsym : eSymC n (fun i => (CohMap f ℤ 2).hom (t (Fin.castSucc i))) (k - 1)
          = (CohMap f ℤ (2 * (k - 1))).hom (eSymC n (fun i => t (Fin.castSucc i)) (k - 1)) :=
        ih _ (k - 1)
      have hZ : (Work.Whitney.cupChern 1 (k - 1) ((CohMap f ℤ 2).hom (t (Fin.last n)))
            (eSymC n (fun i => (CohMap f ℤ 2).hom (t (Fin.castSucc i))) (k - 1)))
          = (Work.Whitney.cupChern 1 (k - 1) ((CohMap f ℤ (2 * 1)).hom (t (Fin.last n)))
            ((CohMap f ℤ (2 * (k - 1))).hom
              (eSymC n (fun i => t (Fin.castSucc i)) (k - 1)))) := by
        rw [hlast, hsym]
      rw [hZ]
    · rw [dif_neg h, dif_neg h, map_zero]

/-- **Correction of `eSymC` along a pointwise equality of the families**. -/
theorem eSymC_congr {P : Type} [TopologicalSpace P] {n : ℕ} {u v : Fin n → Coh ℤ 2 P}
    (h : ∀ i, u i = v i) (k : ℕ) : eSymC n u k = eSymC n v k := by
  induction n generalizing k with
  | zero => rw [eSymC_zero, eSymC_zero]
  | succ n ih =>
    rw [eSymC_succ, eSymC_succ]
    have hhead : eSymC n (fun i => u (Fin.castSucc i)) k
        = eSymC n (fun i => v (Fin.castSucc i)) k :=
      ih (fun i => h (Fin.castSucc i)) k
    rw [hhead]
    congr 1
    by_cases hk : 1 ≤ k
    · rw [dif_pos hk, dif_pos hk]
      have hlast : u (Fin.last n) = v (Fin.last n) := h (Fin.last n)
      have hprev : eSymC n (fun i => u (Fin.castSucc i)) (k - 1)
          = eSymC n (fun i => v (Fin.castSucc i)) (k - 1) :=
        ih (fun i => h (Fin.castSucc i)) (k - 1)
      rw [hlast, hprev]
    · rw [dif_neg hk, dif_neg hk]

/-- **`cupH'` is `ℤ`-linear in its second argument**, in the normalisation of the `•` notation of
`Work.Thom.Coh` (the two instances of scalar multiplication on `Coh` are bridged by
`int_smul_eq_zsmul`, as in `Work.Kunneth.cupH'_zsmul_left`). -/
theorem cupH'_zsmul_right {P : Type} [TopologicalSpace P] {n m : ℕ} (c : ℤ)
    (x : Coh ℤ n P) (y : Coh ℤ m P) :
    ((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB P) n m) x) (c • y)
      = c • (((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB P) n m) x) y) := by
  rw [← int_smul_eq_zsmul (inferInstance : Module ℤ (Coh ℤ m P)) c y]
  rw [← int_smul_eq_zsmul (inferInstance : Module ℤ (Coh ℤ (n + m) P)) c
        (((Work.Cohomology.cupH' ℤ (Work.Whitney.ssB P) n m) x) y)]
  exact Work.Cohomology.cupH'_smul_right ℤ (Work.Whitney.ssB P) n m c x y

/-- **The graded product is `ℤ`-linear in its second variable.** -/
theorem cupChern_zsmul_right {P : Type} [TopologicalSpace P] (a b : ℕ) (c : ℤ)
    (x : Coh ℤ (2 * a) P) (y : Coh ℤ (2 * b) P) :
    Work.Whitney.cupChern a b x (c • y) = c • Work.Whitney.cupChern a b x y := by
  rw [Work.Whitney.cupChern_def, Work.Whitney.cupChern_def, ← Work.Thom.cohTransport_zsmul]
  exact congrArg (Work.Thom.cohTransport (Nat.mul_add 2 a b).symm) (cupH'_zsmul_right c x y)

/-- **The powers of `-z` are the signed geometric series of `z`**: `(-z)^k = (-1)^k z^k`. -/
theorem zPow_neg {P : Type} [TopologicalSpace P] (z : Coh ℤ 2 P) :
    Work.Whitney.ChernRel.zPow (-z) = Work.Whitney.ChernRel.geoSeriesOf z := by
  funext k
  induction k with
  | zero => rw [Work.Whitney.ChernRel.zPow_zero, Work.Whitney.ChernRel.geoSeriesOf_zero]
  | succ k ih =>
    rw [Work.Whitney.ChernRel.zPow_succ, ih, Work.Whitney.ChernRel.geoSeriesOf_succ,
      Work.Whitney.ChernRel.cupChern_neg_right]

end

end Work.Gen
