import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairRowS3Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.rowShape_congr_box`

The three per-pair shapes `rowShape13`, `rowShape21`, `rowShape23` of the FS `Q₂` row
(`Submission/Work/BoseBoxFock/pairRowS2Row.lean`) are *triple* integrals in which the pair kernel
`K` is evaluated **either on configuration coordinates** (which lie in the box `acube ℓ` as soon as
the state `Θ` does not vanish there) **or on the free integration variables** `y, u` (which are
*forced* into the box by the very same support hypothesis: the state factor
`Θ (update (update x p.1 y) p.2 u)` vanishes unless `y` and `u` are inside `acube ℓ`).

Consequently, if two kernels agree on `acube ℓ × acube ℓ`, the three shapes agree — this is the
module's theorem `rowShape_congr_box`.  It is the bookkeeping that lets the row be evaluated at the
honest localised kernel `wLoc` instead of a global extension (cf. the (S3) step of
`FINDING_PotPairRows_exists.md`).

The proof is purely pointwise: at every `(x, y, u)` the two integrands are either *literally* the
same (the common factor `star (Θ x) * … * Θ (update …)` vanishes) or the kernel argument belongs to
`acube ℓ`.  No integrability is used, so the identity holds for the raw Bochner integral.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The two elementary geometric inputs -/

/-- Every coordinate of a configuration in the support of a state supported in `boxPow n ℓ` lies in
the one-particle box `acube ℓ` (for `0 < ℓ`, where `boxL ℓ = acube ℓ`). -/
private lemma coord_mem_acube {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ : Work.BoseDict.Xn n → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ) {x : Work.BoseDict.Xn n} (hx : Θ x ≠ 0)
    (i : Fin n) : x i ∈ Submission.BoseGases.acube ℓ := by
  rw [← boxL_eq_acube hℓ]
  exact Work.MB.mem_boxPow_iff.mp (hΘs (Function.mem_support.mpr hx)) i

/-- The `p.1`-coordinate of `update (update x p.1 y) p.2 u` is `y` (because `p.1 ≠ p.2`). -/
private lemma upd_coord_fst {n : ℕ} {i j : Fin n} (hij : i ≠ j) (x : Work.BoseDict.Xn n)
    (y u : E3) : (Function.update (Function.update x i y) j u) i = y := by
  simp [hij]

/-- The `p.2`-coordinate of `update (update x p.1 y) p.2 u` is `u`. -/
private lemma upd_coord_snd {n : ℕ} {i j : Fin n} (x : Work.BoseDict.Xn n) (y u : E3) :
    (Function.update (Function.update x i y) j u) j = u := by
  simp

/-! ## 2. The three shapes, one at a time -/

/-- Block I shape: the kernel is `K (x p.2) y`. -/
private lemma rowShape13_congr_box {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ : Work.BoseDict.Xn n → ℂ}
    {A B : E3 → ℂ} {K K' : E3 → E3 → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hK : ∀ w y, w ∈ Submission.BoseGases.acube ℓ → y ∈ Submission.BoseGases.acube ℓ →
      K w y = K' w y)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    rowShape13 Θ A B K p = rowShape13 Θ A B K' p := by
  simp only [rowShape13]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  dsimp only
  by_cases h1 : Θ x = 0
  · simp [h1]
  by_cases h2 : Θ (Function.update (Function.update x p.1 y) p.2 u) = 0
  · simp [h2]
  have hx2 : x p.2 ∈ Submission.BoseGases.acube ℓ := coord_mem_acube hℓ hΘs h1 p.2
  have hy : y ∈ Submission.BoseGases.acube ℓ := by
    have hmem :=
      Work.MB.mem_boxPow_iff.mp (hΘs (Function.mem_support.mpr h2)) p.1
    rwa [boxL_eq_acube hℓ, upd_coord_fst hp] at hmem
  rw [hK (x p.2) y hx2 hy]

/-- Block II.1 shape: the kernel is `K u y` with both arguments free. -/
private lemma rowShape21_congr_box {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ : Work.BoseDict.Xn n → ℂ}
    {A : E3 → ℂ} {K K' : E3 → E3 → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hK : ∀ w y, w ∈ Submission.BoseGases.acube ℓ → y ∈ Submission.BoseGases.acube ℓ →
      K w y = K' w y)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    rowShape21 Θ A K p = rowShape21 Θ A K' p := by
  simp only [rowShape21]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  dsimp only
  by_cases h2 : Θ (Function.update (Function.update x p.1 y) p.2 u) = 0
  · simp [h2]
  have hmem := Work.MB.mem_boxPow_iff.mp (hΘs (Function.mem_support.mpr h2))
  have hy : y ∈ Submission.BoseGases.acube ℓ := by
    have h := hmem p.1
    rwa [boxL_eq_acube hℓ, upd_coord_fst hp] at h
  have hu : u ∈ Submission.BoseGases.acube ℓ := by
    have h := hmem p.2
    rwa [boxL_eq_acube hℓ, upd_coord_snd] at h
  rw [hK u y hu hy]

/-- Block II.2 shape: the kernel is `K (x p.1) (x p.2)`, both arguments configuration slots. -/
private lemma rowShape23_congr_box {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ : Work.BoseDict.Xn n → ℂ}
    {A B : E3 → ℂ} {K K' : E3 → E3 → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hK : ∀ w y, w ∈ Submission.BoseGases.acube ℓ → y ∈ Submission.BoseGases.acube ℓ →
      K w y = K' w y)
    {p : Fin n × Fin n} (_hp : p.1 ≠ p.2) :
    rowShape23 Θ A B K p = rowShape23 Θ A B K' p := by
  simp only [rowShape23]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
  dsimp only
  by_cases h1 : Θ x = 0
  · simp [h1]
  exact congrArg (fun c => star (Θ x) * c * star (A y) * star (B u)
      * Θ (Function.update (Function.update x p.1 y) p.2 u))
    (hK (x p.1) (x p.2) (coord_mem_acube hℓ hΘs h1 p.1)
      (coord_mem_acube hℓ hΘs h1 p.2))

/-! ## 3. The theorem -/

theorem rowShape_congr_box {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {Θ : Work.BoseDict.Xn n → ℂ}
    {A B : EuclideanSpace ℝ (Fin 3) → ℂ}
    {K K' : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hΘs : Function.support Θ ⊆ Work.MB.boxPow n ℓ)
    (hK : ∀ w y, w ∈ Submission.BoseGases.acube ℓ → y ∈ Submission.BoseGases.acube ℓ →
      K w y = K' w y)
    {p : Fin n × Fin n} (hp : p.1 ≠ p.2) :
    Work.BoseBoxFock.rowShape13 Θ A B K p = Work.BoseBoxFock.rowShape13 Θ A B K' p ∧
    Work.BoseBoxFock.rowShape21 Θ A K p = Work.BoseBoxFock.rowShape21 Θ A K' p ∧
    Work.BoseBoxFock.rowShape23 Θ A B K p = Work.BoseBoxFock.rowShape23 Θ A B K' p :=
  ⟨rowShape13_congr_box hℓ hΘs hK hp, rowShape21_congr_box hℓ hΘs hK hp,
    rowShape23_congr_box hℓ hΘs hK hp⟩

end Work.BoseBoxFock
