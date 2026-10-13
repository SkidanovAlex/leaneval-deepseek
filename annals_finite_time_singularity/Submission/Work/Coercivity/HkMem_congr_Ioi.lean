import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.CommutZ_HkIntegrand_congr_pt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Coercivity

open scoped Real Topology
open MeasureTheory Set Filter
open Work.Spaces

set_option autoImplicit false

/-
# Congruence of `HkMem` on the positive half-line

`HkMem α k f` is an *integrability* statement about the integrand `HkIntegrand α k f`,
which is built out of the iterated differential operators `DzIter i` and `mixed j i`
applied to `f`, together with weights depending only on `(z,θ)`.

Because every differential operator is local, two functions that agree on
`(0,∞) × [0,π/2]` have the same `HkIntegrand` at every *interior* point of the domain
`[0,∞) × [0,π/2]` (this is `CommutZ_HkIntegrand_congr_pt`).  The only points not covered
are those with `z = 0` or `θ ∈ {0, π/2}`, i.e. two null sets.  Hence:
* for every `z > 0` the two `θ`-slices are equal a.e. on `Iθ`, so integrability transfers;
* at `z = 0` the integrand vanishes identically, since the weight `w` vanishes there;
* consequently also the outer `z`-integrals agree everywhere on `Iz`.

This file records these facts and deduces `HkMem`-congruence.
-/

/-- At `z = 0` the `H^k` integrand vanishes identically, because the radial weight `w`
vanishes there (Lean's totalised division gives `w 0 = 1/0 = 0`). -/
theorem HkIntegrand_zero_left (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    HkIntegrand α k f 0 θ = 0 := by
  simp [HkIntegrand, Wt, wTheta, w]

/-- Two functions that agree on the open angle interval `(0,π/2)` agree almost everywhere
on `Iθ = [0,π/2]`. -/
private lemma ae_eq_of_eqOn_Ioo {f g : ℝ → ℝ}
    (h : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), f θ = g θ) :
    f =ᵐ[volume.restrict Iθ] g := by
  have hμ : volume.restrict (Set.Ioo (0 : ℝ) (π / 2)) = volume.restrict Iθ := by
    rw [Work.Spaces.Iθ]
    exact Measure.restrict_congr_set MeasureTheory.Ioo_ae_eq_Icc
  rw [← hμ]
  exact (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mpr
    (Filter.Eventually.of_forall (fun x hx => h x hx))

theorem HkMem_congr_Ioi (α : ℝ) (k : ℕ) {u v : ℝ → ℝ → ℝ} (hu : Work.Spaces.HkMem α k u)
    (h : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Work.Spaces.Iθ, u z θ = v z θ) :
    Work.Spaces.HkMem α k v := by
  obtain ⟨hu1, hu2⟩ := hu
  -- The `θ`-slices of the integrands agree a.e. for every `z > 0`.
  have hae : ∀ z ∈ Set.Ioi (0 : ℝ),
      HkIntegrand α k v z =ᵐ[volume.restrict Iθ] HkIntegrand α k u z :=
    fun z hz => ae_eq_of_eqOn_Ioo
      (fun θ hθ => (CommutZ_HkIntegrand_congr_pt α k u v h z hz θ hθ).symm)
  -- The outer `z`-integrals agree on all of `Iz` (`z = 0` is the trivial case).
  have hint : ∀ z ∈ Iz, ∫ θ in Iθ, HkIntegrand α k u z θ
      = ∫ θ in Iθ, HkIntegrand α k v z θ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      simp [HkIntegrand_zero_left]
    · exact (integral_congr_ae (hae z hzpos)).symm
  constructor
  · -- Slicewise integrability of the integrand of `v`.
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · subst hz0
      simp only [HkIntegrand_zero_left]
      exact integrableOn_zero
    · exact Integrable.congr (hu1 z hz) (hae z hzpos).symm
  · -- Integrability of the outer integral of `v`, by congruence with `u`.
    exact IntegrableOn.congr_fun hu2 (fun z hz => hint z hz) measurableSet_Ici

end Work.Coercivity
