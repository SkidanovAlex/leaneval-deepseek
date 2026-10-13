/-
Work module for the Elgindi finite-time singularity project.

# `HkMem` only sees the values of `f` on the open quadrant `(0,∞) × (0,π/2)`

`HkMem α k f` is the statement that the slices `θ ↦ HkIntegrand α k f z θ` are integrable
on `Iθ = [0,π/2]` for every `z ∈ Iz = [0,∞)`, and that the iterated integral
`z ↦ ∫ θ in Iθ, HkIntegrand α k f z θ` is integrable on `Iz`.

The integrand `HkIntegrand α k f` is built from the iterated differential operators
`DzIter i` and `mixed j i`, together with weights depending only on `(z,θ)`.  Every such
operator is local, so two functions which agree on the *open* quadrant `(0,∞) × (0,π/2)`
have equal integrands at every interior point of `Iz × Iθ`
(`Work.FTS.EllipticEst.HkIntegrand_congr`).

The only points of `Iz × Iθ` that are not interior are those with `z = 0` or
`θ ∈ {0, π/2}`, i.e. two null sets.  So:
* for every `z > 0` the two `θ`-slices agree a.e. on `Iθ`, hence integrability transfers;
* at `z = 0` the integrand vanishes identically for *any* `f`, since the radial weight
  `w` vanishes there (`Work.Coercivity.HkIntegrand_zero_left`);
* consequently the outer `z`-integrals agree on all of `Iz`.

This is the open-quadrant counterpart of `Work.Coercivity.HkMem_congr_Ioi`, which assumes
agreement on `(0,∞) × Iθ` (closed in `θ`).

**Note on `π`.**  The statement below uses the symbol `π`; for it to denote `Real.pi`
(rather than be auto-bound as a free implicit variable) this file needs
`open scoped Real`, which is why that command appears here.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.CommutZ_HkIntegrand_congr_pt
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.Coercivity.HkMem_congr_Ioi

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cert.GbarSin

open Work.Spaces

set_option autoImplicit false

/-- Two functions of the angle which agree on the open interval `(0,π/2)` agree almost
everywhere on `Iθ = [0,π/2]`. -/
private lemma ae_eq_of_eqOn_Ioo {f g : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), f θ = g θ) :
    f =ᵐ[volume.restrict Iθ] g := by
  have hμ : volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Iθ := by
    rw [Work.Spaces.Iθ]
    exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← hμ]
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
    (Filter.Eventually.of_forall (fun x hx => h x hx))

theorem HkMem_congr_Q0 (α : ℝ) (k : ℕ) {u v : ℝ → ℝ → ℝ} (hu : Work.Spaces.HkMem α k u)
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), u z θ = v z θ) :
    Work.Spaces.HkMem α k v := by
  obtain ⟨hu1, hu2⟩ := hu
  -- The hypothesis is agreement on the open quadrant.
  have hAg : Work.FTS.EllipticEst.AgreeOnQ u v :=
    fun z θ hz hθ hlt => h z hz θ ⟨hθ, hlt⟩
  -- The integrands agree at every interior point of the quadrant.
  have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
      HkIntegrand α k u z θ = HkIntegrand α k v z θ :=
    Work.FTS.EllipticEst.HkIntegrand_congr (α := α) (k := k) hAg
  -- Hence the `θ`-slices of the integrands agree a.e. on `Iθ` for every `z > 0`.
  have hae : ∀ z ∈ Set.Ioi (0 : ℝ),
      HkIntegrand α k v z =ᵐ[volume.restrict Iθ] HkIntegrand α k u z :=
    fun z hz => ae_eq_of_eqOn_Ioo (fun θ hθ => (hpt z θ hz hθ.1 hθ.2).symm)
  constructor
  · -- Slicewise integrability of the integrand of `v`.
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      simp only [Work.Coercivity.HkIntegrand_zero_left]
      exact integrableOn_zero
    · exact Integrable.congr (hu1 z hz) (hae z hzpos).symm
  · -- Integrability of the outer integral of `v`, by congruence with `u`.
    have hint : ∀ z ∈ Iz, (∫ θ in Iθ, HkIntegrand α k u z θ)
        = ∫ θ in Iθ, HkIntegrand α k v z θ := by
      intro z hz
      rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
      · subst hz0
        simp [Work.Coercivity.HkIntegrand_zero_left]
      · exact (integral_congr_ae (hae z hzpos)).symm
    exact IntegrableOn.congr_fun hu2 (fun z hz => hint z hz) measurableSet_Ici

end Work.FTS.EllipticEst.Cert.GbarSin
