import Mathlib
import Submission.Work.Lattice.MaxNormPolygon
import Submission.Work.Lattice.MaxNormEndpoints
import Submission.Work.Lattice.MaxNormAccounting
import Submission.Work.Lattice.AccountingOneSided
import Submission.Work.Polygon.AngularRanks
import Submission.Commons.Analysis.Calculus.exists_sum_mul_deriv_ge_neg

/-!
# The accounting for the **slacked** max-norm polygon of the §3 flow

`MaxNormAccounting` proves the accounting inequality `Σ_s Δ effPos_s · Λ_s ≤ ℓ(d−ℓ)/d` at a good
time for the max-norm polygon `maxPolygon` (i.e. the `lcm` of the max-norm data `maxData`).

The §3 flag (`MaxPhiFlag.exists_tight_flag`) is however built from the **slacked** data
`maxData (j) + A·j(d−j)`: its members are the tight realisers of that slacked function, and at its
angular ranks the *slacked* polygon coincides with the slacked data.  For the extraction one needs
the accounting with *that* polygon, so this module redoes the (purely formal) chain:

* `phiData` / `phiPolygonT` / `phiSlope` — the slacked data, polygon and slopes (as functions of
  the flow time `t`, for the lattice `Λ₀ = g(ℤᵈ)`);
* endpoints, convexity, closure `Σ_{i<d} phiSlope_i = 0`;
* Lipschitz-in-`t` bounds for the data, the polygon and the slopes;
* **`phi_good_time`** — for every `c > 0`, `T` there is `t ≥ T` with all slacked slopes
  differentiable and `Σ_i Λ_i Λ_i' ≥ −c`;
* **`phi_accounting`** — the accounting inequality at such a good time.

Module `Submission.Work.Lattice.MaxPhiAccounting`, namespace `Submission.MaxPhiAccounting`.
-/

noncomputable section

open Module exteriorPower InnerProductGeometry Real
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Submission.MaxPhiAccounting

open Submission.ExteriorCoordinates
open Submission.MaxNorm
open Submission.MaxNormPolygon
open Submission.MaxNormEndpoints
open Submission.ImageLattice
open Submission.Polygon
open Submission.AngularRanks
open Submission.AccountingOneSided

variable {d : ℕ}

/-- The **slacked max-norm data** at flow time `t`. -/
noncomputable def phiData (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (A : ℝ) (t : ℝ) : ℕ → ℝ :=
  fun j => maxData (d := d) Λ₀ ℓ t j + A * (j : ℝ) * ((d : ℝ) - (j : ℝ))

/-- The **slacked max-norm polygon** at flow time `t`. -/
noncomputable def phiPolygonT (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (A : ℝ) (t : ℝ) : ℕ → ℝ :=
  largestConvexMinorant d (phiData (d := d) Λ₀ ℓ A t)

/-- The slopes of the slacked max-norm polygon. -/
noncomputable def phiSlope (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (A : ℝ) (t : ℝ) (i : ℕ) : ℝ :=
  dslope (phiPolygonT (d := d) Λ₀ ℓ A t) i

/-- The energy `Σ_i phiSlope_i²  ≥ 0` of the slacked polygon. -/
noncomputable def phiEnergy (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (A : ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range d, (phiSlope (d := d) Λ₀ ℓ A t i) ^ 2

lemma phiData_zero (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (A : ℝ) (t : ℝ) :
    phiData (d := d) Λ₀ ℓ A t 0 = 0 := by
  simp [phiData, maxData_zero]

lemma phiData_top {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (t : ℝ) :
    phiData (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t d = 0 := by
  simp [phiData, maxData_top_eq_zero (d := d) hℓ0 hℓd g t]

lemma phiPolygonT_zero (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (A : ℝ) (t : ℝ) :
    phiPolygonT (d := d) Λ₀ ℓ A t 0 = 0 :=
  largestConvexMinorant_zero_left d _ (phiData_zero (d := d) Λ₀ ℓ A t)

lemma phiPolygonT_top {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (t : ℝ) :
    phiPolygonT (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t d = 0 :=
  largestConvexMinorant_zero_right d _ (phiData_top (d := d) hℓ0 hℓd A g t)

lemma phiPolygonT_convex (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (A : ℝ) (t : ℝ) :
    DiscreteConvexOn (phiPolygonT (d := d) Λ₀ ℓ A t) d :=
  largestConvexMinorant_convex d _

/-- **The closure identity** of the accounting for the slacked polygon. -/
theorem phiSlope_sum_eq_zero {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (t : ℝ) :
    (∑ i ∈ Finset.range d,
      phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t i) = 0 := by
  have h := sum_slopes_eq_zero_of_ends (c := phiPolygonT (d := d)
    (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t)
    (phiPolygonT_zero (d := d) _ ℓ A t) (phiPolygonT_top (d := d) hℓ0 hℓd A g t)
  simpa [phiSlope] using h

/-- **The slacked data is Lipschitz in `t`** (the `A`-term is constant in `t`). -/
theorem phiData_lipschitz {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (s t : ℝ) (j : ℕ) :
    |phiData (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A s j -
        phiData (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t j| ≤
      lipConst d ℓ * |s - t| := by
  have h : phiData (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A s j -
      phiData (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t j =
      maxData (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ s j -
        maxData (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ t j := by
    simp only [phiData]
    ring
  rw [h]
  exact maxData_lipschitz (d := d) hℓ0 hℓd g s t j

/-- **The slacked polygon is Lipschitz in `t`.** -/
theorem phiPolygonT_lipschitz {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (s t : ℝ) {i : ℕ} (hi : i ≤ d) :
    |phiPolygonT (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A s i -
        phiPolygonT (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t i| ≤
      lipConst d ℓ * |s - t| := by
  refine abs_largestConvexMinorant_sub_le _ _ (fun j _ => ?_) hi
  exact phiData_lipschitz (d := d) hℓ0 hℓd A g s t j

/-- **The slacked slopes are Lipschitz in `t`.** -/
theorem phiSlope_lipschitz {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (s t : ℝ) {i : ℕ} (hi : i + 1 ≤ d) :
    |phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A s i -
        phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t i| ≤
      2 * (lipConst d ℓ * |s - t|) := by
  refine abs_dslope_largestConvexMinorant_sub_le (i := i) _ _ (fun j _ => ?_) hi
  exact phiData_lipschitz (d := d) hℓ0 hℓd A g s t j

/-- The slacked slopes form a Lipschitz family in `t` (the hypothesis of the good-time atom). -/
theorem phiSlope_lipschitz_family {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ)
    (g : RD d ≃ₗᵢ[ℝ] RD d) :
    ∀ (i : Fin d) (s t : ℝ),
      |phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A s i.val -
        phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t i.val| ≤
      (2 * lipConst d ℓ) * |s - t| := by
  intro i s t
  have h := phiSlope_lipschitz (d := d) hℓ0 hℓd A g s t (i := i.val) (by omega)
  rwa [← mul_assoc] at h

lemma phiEnergy_nonneg (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (A : ℝ) (t : ℝ) :
    0 ≤ phiEnergy (d := d) Λ₀ ℓ A t :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- **The good time of the slacked max-norm polygon.** -/
theorem phi_good_time {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ)
    (g : RD d ≃ₗᵢ[ℝ] RD d) {c : ℝ} (hc : 0 < c) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧
      (∀ i : Fin d, DifferentiableAt ℝ
        (fun u => phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A u i.val)
        t) ∧
      -c ≤ ∑ i : Fin d,
        phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t i.val *
        deriv (fun u => phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A u
          i.val) t := by
  have hC : 0 ≤ 2 * lipConst d ℓ := by
    have := lipConst_nonneg d ℓ
    linarith
  exact Commons.Analysis.Calculus.exists_sum_mul_deriv_ge_neg (d := d) hC
    (fun i => phiSlope_lipschitz_family (d := d) hℓ0 hℓd A g i) hc T

/-- The derivative in `t` of a slacked slope. -/
noncomputable def phiSlopeDeriv (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (A : ℝ) (t : ℝ) (i : ℕ) : ℝ :=
  deriv (fun u => phiSlope (d := d) Λ₀ ℓ A u i) t

/-- The **level derivative** `r_s = Σ_{i < jb s} phiSlope_i'(t)` of the slacked polygon. -/
noncomputable def phiLevelDeriv (Λ₀ : Submodule ℤ (RD d)) (ℓ : ℕ) (A : ℝ) (t : ℝ)
    (jb : ℕ → ℕ) (s : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (jb s), phiSlopeDeriv (d := d) Λ₀ ℓ A t i

/-- The top level derivative vanishes (the closure `Σ_i Λ_i = 0` holds identically in `t`). -/
theorem phiLevelDeriv_top_eq_zero {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ)
    (g : RD d ≃ₗᵢ[ℝ] RD d) {t : ℝ}
    (hdiff : ∀ i : Fin d, DifferentiableAt ℝ
      (fun u => phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A u i.val) t) :
    phiLevelDeriv (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t
      (blockStart d (phiPolygonT (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t))
      (numBlocks d (phiPolygonT (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t)) = 0 := by
  set Λ₀ : Submodule ℤ (RD d) := imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d) with hΛ₀
  have hderiv : deriv (fun u => ∑ i ∈ Finset.range d, phiSlope (d := d) Λ₀ ℓ A u i) t =
      ∑ i ∈ Finset.range d, phiSlopeDeriv (d := d) Λ₀ ℓ A t i := by
    have hfun : (fun u => ∑ i ∈ Finset.range d, phiSlope (d := d) Λ₀ ℓ A u i) =
        (∑ i ∈ Finset.range d, fun u => phiSlope (d := d) Λ₀ ℓ A u i) := by
      funext u
      simp [Finset.sum_apply]
    rw [hfun]
    exact deriv_sum (u := Finset.range d)
      (A := fun i => fun u => phiSlope (d := d) Λ₀ ℓ A u i) (x := t)
      (fun i hi => hdiff ⟨i, Finset.mem_range.mp hi⟩)
  rw [phiLevelDeriv, blockStart_numBlocks, ← hderiv]
  have hconst : (fun u => ∑ i ∈ Finset.range d, phiSlope (d := d) Λ₀ ℓ A u i) =
      (fun _ => (0 : ℝ)) := by
    funext u
    simpa [hΛ₀] using phiSlope_sum_eq_zero (d := d) hℓ0 hℓd A g u
  rw [hconst, deriv_const]

/-- **The accounting inequality for the slacked max-norm polygon.**  For the §3 flow lattice
`Λ₀ = g(ℤᵈ)`, every slack `A` and every `T` there is `t ≥ T` with

    `Σ_s Δ effPos_s · phiSlope_s ≤ ℓ(d−ℓ)/d`,

where `effPos` is built from the level derivatives of the slacked polygon at its angular ranks. -/
theorem phi_accounting_at {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ)
    (g : RD d ≃ₗᵢ[ℝ] RD d) {t : ℝ}
    (hdiff : ∀ i : Fin d, DifferentiableAt ℝ
      (fun u => phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A u i.val) t)
    (hgood0 : -1 ≤ ∑ i : Fin d,
      phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t i.val *
      deriv (fun u => phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A u
        i.val) t) :
      (∑ s ∈ Finset.range (numBlocks d (phiPolygonT (d := d)
            (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t)),
        (effPos d ℓ
            (fun s => (blockStart d (phiPolygonT (d := d)
              (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t) s : ℝ))
            (phiLevelDeriv (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t
              (blockStart d (phiPolygonT (d := d)
                (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t))) (s + 1) -
          effPos d ℓ
            (fun s => (blockStart d (phiPolygonT (d := d)
              (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t) s : ℝ))
            (phiLevelDeriv (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t
              (blockStart d (phiPolygonT (d := d)
                (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t))) s) *
          phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t
            (blockStart d (phiPolygonT (d := d)
              (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t) s))
        ≤ (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le hℓ0 (le_of_lt hℓd)
  set Λ₀ : Submodule ℤ (RD d) := imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d) with hΛ₀
  set c : ℕ → ℝ := phiPolygonT (d := d) Λ₀ ℓ A t with hc
  set jb : ℕ → ℕ := blockStart d c with hjb
  set jbR : ℕ → ℝ := fun s => ((jb s : ℕ) : ℝ) with hjbR
  set r : ℕ → ℝ := phiLevelDeriv (d := d) Λ₀ ℓ A t jb with hr
  set Λs : ℕ → ℝ := fun s => phiSlope (d := d) Λ₀ ℓ A t (jb s) with hΛs
  have hjb0 : jbR 0 = 0 := by
    simp [hjbR, hjb, blockStart_zero]
  have hjbRtop : jbR (numBlocks d c) = (d : ℝ) := by
    simp [hjbR, hjb, blockStart_numBlocks]
  have hr0 : r 0 = 0 := by
    simp [hr, phiLevelDeriv, hjb, blockStart_zero]
  have hrR : r (numBlocks d c) = 0 := by
    rw [hr]
    exact phiLevelDeriv_top_eq_zero (d := d) hℓ0 hℓd A g hdiff
  -- the closure identity
  have hclosed : (∑ s ∈ Finset.range (numBlocks d c), Λs s * (jbR (s + 1) - jbR s)) = 0 := by
    have h := Submission.MaxNormAccounting.sum_blockStart_mul_delta (d := d) c
    have hL : (∑ s ∈ Finset.range (numBlocks d c), Λs s * (jbR (s + 1) - jbR s)) =
        (∑ s ∈ Finset.range (numBlocks d c), dslope c (blockStart d c s) *
          (((blockStart d c (s + 1) : ℕ) : ℝ) - ((blockStart d c s : ℕ) : ℝ))) := by
      simp only [hΛs, hjbR, hjb, phiSlope, hc]
    rw [hL, h]
    simpa [phiSlope, hc, hΛ₀] using phiSlope_sum_eq_zero (d := d) hℓ0 hℓd A g t
  -- the good-time inequality, transferred to the level derivatives
  have hgood : -1 ≤ ∑ s ∈ Finset.range (numBlocks d c), Λs s * (r (s + 1) - r s) := by
    have hstep : (∑ s ∈ Finset.range (numBlocks d c), Λs s * (r (s + 1) - r s)) =
        ∑ i ∈ Finset.range d, phiSlope (d := d) Λ₀ ℓ A t i *
          phiSlopeDeriv (d := d) Λ₀ ℓ A t i := by
      have hterm : ∀ s ∈ Finset.range (numBlocks d c),
          Λs s * (r (s + 1) - r s) =
          ∑ i ∈ Finset.Ico (jb s) (jb (s + 1)), phiSlope (d := d) Λ₀ ℓ A t i *
            phiSlopeDeriv (d := d) Λ₀ ℓ A t i := by
        intro s _
        have hmono : jb s ≤ jb (s + 1) := by
          simp only [hjb]; exact blockStart_mono d c s
        have hsub : r (s + 1) - r s =
            ∑ i ∈ Finset.Ico (jb s) (jb (s + 1)), phiSlopeDeriv (d := d) Λ₀ ℓ A t i := by
          rw [hr]
          simp only [phiLevelDeriv]
          exact (Finset.sum_Ico_eq_sub _ hmono).symm
        rw [hsub, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        have hi1 : jb s ≤ i := (Finset.mem_Ico.mp hi).1
        have hi2 : i < jb (s + 1) := (Finset.mem_Ico.mp hi).2
        have heq : phiSlope (d := d) Λ₀ ℓ A t (jb s) = phiSlope (d := d) Λ₀ ℓ A t i := by
          have hblock := dslope_eq_on_block c d s hi1 hi2
          simp only [hjb, phiSlope, hc]
          exact hblock.symm
        simp only [hΛs]
        rw [heq]
      rw [Finset.sum_congr rfl hterm]
      exact (sum_range_eq_sum_blocks (d := d) c
        (fun i => phiSlope (d := d) Λ₀ ℓ A t i *
          phiSlopeDeriv (d := d) Λ₀ ℓ A t i)).symm
    rw [hstep]
    have hconv : (∑ i : Fin d,
          phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t i.val *
            deriv (fun u => phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A u
              i.val) t) =
        ∑ i ∈ Finset.range d, phiSlope (d := d) Λ₀ ℓ A t i *
          phiSlopeDeriv (d := d) Λ₀ ℓ A t i := by
      rw [Fin.sum_univ_eq_sum_range
        (fun i => phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t i *
          deriv (fun u => phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A u i) t)
        d]
      rfl
    rw [← hconv, ← hΛ₀]
    exact hgood0
  exact accounting_le_rate_inv (d := d) (ℓ := ℓ) hℓ0 hℓd
    (R := numBlocks d c) (numBlocks_pos _ hd0) jbR r Λs hjb0 hjbRtop hr0 hrR hclosed hgood

/-- **The accounting inequality for the slacked max-norm polygon** (existential good time). -/
theorem phi_accounting {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧
      (∑ s ∈ Finset.range (numBlocks d (phiPolygonT (d := d)
            (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t)),
        (effPos d ℓ
            (fun s => (blockStart d (phiPolygonT (d := d)
              (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t) s : ℝ))
            (phiLevelDeriv (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t
              (blockStart d (phiPolygonT (d := d)
                (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t))) (s + 1) -
          effPos d ℓ
            (fun s => (blockStart d (phiPolygonT (d := d)
              (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t) s : ℝ))
            (phiLevelDeriv (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t
              (blockStart d (phiPolygonT (d := d)
                (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t))) s) *
          phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t
            (blockStart d (phiPolygonT (d := d)
              (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t) s))
        ≤ (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) := by
  obtain ⟨t, htT, hdiff, hgood0⟩ := phi_good_time (d := d) hℓ0 hℓd A g (c := 1) one_pos T
  exact ⟨t, htT, phi_accounting_at (d := d) hℓ0 hℓd A g hdiff hgood0⟩

/-- The slacked slopes are nondecreasing along the flag (convexity). -/
lemma phiSlope_mono {ℓ : ℕ} (A : ℝ) (g : RD d ≃ₗᵢ[ℝ] RD d) {t : ℝ} {i j : ℕ}
    (hij : i ≤ j) (hj : j + 1 ≤ d) :
    phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t i ≤
      phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t j :=
  dslope_mono (phiPolygonT_convex (d := d) _ ℓ A t) hij hj

/-- **The accounting with an arbitrary capacity sequence.**  At a good time, any sequence `ω`
which dominates the effective capacities of the slacked polygon and has the same endpoints
(`ω 0 = 0`, `ω R = ℓ`) satisfies the accounting inequality.  (The extraction supplies `ω` = the
positions of the flag members.) -/
theorem phi_accounting_of_capacity_le {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓd : ℓ < d) (A : ℝ)
    (g : RD d ≃ₗᵢ[ℝ] RD d) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ ∀ ω : ℕ → ℝ,
      ω 0 = 0 →
      ω (numBlocks d (phiPolygonT (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t)) =
        (ℓ : ℝ) →
      (∀ s ≤ numBlocks d (phiPolygonT (d := d)
          (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t),
        effPos d ℓ
          (fun s => (blockStart d (phiPolygonT (d := d)
            (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t) s : ℝ))
          (phiLevelDeriv (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t
            (blockStart d (phiPolygonT (d := d)
              (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t))) s ≤ ω s) →
      (∑ s ∈ Finset.range (numBlocks d (phiPolygonT (d := d)
            (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t)),
          (ω (s + 1) - ω s) *
            phiSlope (d := d) (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t
              (blockStart d (phiPolygonT (d := d)
                (imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d)) ℓ A t) s))
        ≤ (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) := by
  classical
  have hd0 : 0 < d := lt_of_lt_of_le hℓ0 (le_of_lt hℓd)
  obtain ⟨t, htT, hdiff, hgood0⟩ := phi_good_time (d := d) hℓ0 hℓd A g (c := 1) one_pos T
  refine ⟨t, htT, fun ω hω0 hωR hle => ?_⟩
  set Λ₀ : Submodule ℤ (RD d) := imageSpan (d := d) (g : RD d ≃ₗ[ℝ] RD d) with hΛ₀
  set c : ℕ → ℝ := phiPolygonT (d := d) Λ₀ ℓ A t with hc
  set jb : ℕ → ℕ := blockStart d c with hjb
  set jbR : ℕ → ℝ := fun s => ((jb s : ℕ) : ℝ) with hjbR
  set r : ℕ → ℝ := phiLevelDeriv (d := d) Λ₀ ℓ A t jb with hr
  set Λs : ℕ → ℝ := fun s => phiSlope (d := d) Λ₀ ℓ A t (jb s) with hΛs
  set cap : ℕ → ℝ := fun s => effPos d ℓ jbR r s with hcap
  have hcap0 : cap 0 = 0 := by
    rw [hcap]
    exact effPos_zero (d := d) (ℓ := ℓ) (by simp [hjbR, hjb, blockStart_zero])
      (by rw [hr, phiLevelDeriv, hjb, blockStart_zero]; simp)
  have hrR : r (numBlocks d c) = 0 := by
    rw [hr]
    exact phiLevelDeriv_top_eq_zero (d := d) hℓ0 hℓd A g hdiff
  have hcapR : cap (numBlocks d c) = (ℓ : ℝ) := by
    rw [hcap]
    exact effPos_top (d := d) (ℓ := ℓ) hℓ0 hℓd (by simp [hjbR, hjb, blockStart_numBlocks]) hrR
  have hstep : ∀ s, s + 2 ≤ numBlocks d c → Λs s ≤ Λs (s + 1) := by
    intro s hs
    have hslt : s + 1 < numBlocks d c := by omega
    have hjb1 : jb (s + 1) < d := by
      rw [hjb]
      exact blockStart_lt_numBlocks _ _ hslt
    have h1 : jb s ≤ jb (s + 1) := by
      rw [hjb]
      exact blockStart_mono d c s
    simp only [hΛs]
    exact phiSlope_mono (d := d) A g h1 (by omega)
  have h1 := Submission.MaxNormAccounting.sum_delta_mul_le_of_le_range (R := numBlocks d c)
    (ω := cap) (ω' := ω) (Λ := Λs) hcap0 hω0 (by rw [hcapR, hωR]) hle hstep
  have h2 : (∑ s ∈ Finset.range (numBlocks d c),
        (cap (s + 1) - cap s) * Λs s) ≤ (ℓ : ℝ) * ((d : ℝ) - (ℓ : ℝ)) / (d : ℝ) := by
    rw [hcap, hΛs, hjbR, hr]
    simpa [hΛ₀, hc, hjb] using phi_accounting_at (d := d) hℓ0 hℓd A g hdiff hgood0
  linarith [h1, h2]

end Submission.MaxPhiAccounting

end
