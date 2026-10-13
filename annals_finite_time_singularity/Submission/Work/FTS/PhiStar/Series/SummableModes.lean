/-
# `Work.FTS.PhiStar.Series.SummableModes` — summability of the mode series

The mode series of the remainder source `F = RemSource α ψ = α²·phiA α·ψ` has coefficients

  `acoeff α m F z = (α² · bmode m ψ) · radGreen α m (phiA α) z`   (`RemSetup.acoeff_RemSource`),

`bmode m ψ = cmode m (fun _ θ => ψ θ) 0` being the weight-`cos θ` `m`-th coefficient of `ψ`.

Three *quantitative* inputs make the series absolutely convergent at every point of the open
quadrant (they are the crux estimates, delegated separately, and are carried here as explicit
hypotheses so that this lemma does not depend on their proofs):

* `hgr`: `|eFam m θ| ≤ C (m+1)^{3/2}` on `Iθ` (`Series/eFam_growth`);
* `hdec`: `|bmode m ψ| ≤ C (m+1)^{-5/2}` (from `Series/bmode_decay15`:
  `|bmode m ψ| ≤ C/(lam m √(2m+1))`, together with `(m+1)^{5/2} ≤ lam m·√(2m+1)`);
* `hrad`: `|radGreen α m (phiA α) z| ≤ C (1 + 1/z) (m+1)^{-2}` for `m ≥ 1` — the direct bound on
  the Green formula for the *specific* source `phiA α`, which is **not** in `L²`:
  `phiA α t = (2α-10)/t + O(t^{-2})` as `t → ∞`, so the workspace's `radGreen_abs_le`, whose
  right-hand side is `√(∫ c²)`, cannot be used here.

Then `‖acoeff α m F z · eFam m θ‖ ≤ K(z) (m+1)^{-3}` (the `m = 0` term vanishes: `bmode 0 ψ = 0`
by `AngModel.moment`), so the series is absolutely summable: the `tsum` defining `psiSeries` is
the honest sum, never the junk value `0` of an unsummable family.
-/
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Series.RemSetup
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-! ## The `m = 0` coefficient of `bmode` vanishes -/

/-- For an angular model (`AngModel α ψ` carries the moment condition `∫ψ sinCos2 = 0`), the
`m = 0` mode coefficient of `ψ` vanishes: `e_0 = 3 sinθcosθ`, so `bmode 0 ψ` is `3·Fstar`. -/
theorem bmode_zero (ψ : ℝ → ℝ)
    (hmom : (∫ θ in Work.Spaces.Iθ, ψ θ * Work.Elliptic.sinCos2 θ) = 0) :
    bmode 0 ψ = 0 := by
  have hF : Work.Elliptic.Fstar (fun _ θ => ψ θ) 0 = 0 := by
    simpa only [Work.Elliptic.Fstar] using hmom
  have h := Work.FTS.PhiStar.Series.eFam_zero_moment (fun _ θ => ψ θ) hF
  rw [bmode_eq_cmode 0 ψ 0]
  exact h

/-! ## Summability of the mode series -/

/-- **The mode series is absolutely summable at every point of the open quadrant**, given the
three crux estimates. -/
theorem summable_modes (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hψ : Work.FTS.PhiStar.AngModel α ψ)
    (hgr : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ C * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)))
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |bmode m ψ| ≤ C * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
    (hrad : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → ∀ z : ℝ, 0 < z →
      |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
        ≤ C * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ))) :
    ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      Summable (fun m : ℕ => acoeff α m (Work.FTS.PhiStar.RemSource α ψ) z *
        Work.FTS.PhiStar.Gegenbauer.eFam m θ) := by
  obtain ⟨Cg, hCg, hgr⟩ := hgr
  obtain ⟨Cd, hCd, hdec⟩ := hdec
  obtain ⟨Cr, hCr, hrad⟩ := hrad
  intro z hz θ hθ
  set K : ℝ := α ^ 2 * Cd * Cr * Cg * (1 + 1 / z) with hK
  have hKpos : 0 < K := by
    rw [hK]
    have h1 : 0 < 1 + 1 / z := by
      have hz' : 0 < 1 / z := one_div_pos.mpr hz
      linarith
    positivity
  have hg0 : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(3 : ℝ))) := by
    have h : Summable (fun n : ℕ => ((n : ℝ)) ^ (-(3 : ℝ))) :=
      (Real.summable_nat_rpow (p := (-(3 : ℝ)))).mpr (by norm_num)
    have h' := (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ)) ^ (-(3 : ℝ))) 1).mpr h
    simpa only [Nat.cast_add, Nat.cast_one] using h'
  refine Summable.of_norm_bounded (hg0.mul_left K) (fun m => ?_)
  by_cases hm : m = 0
  · subst hm
    have hz0 : acoeff α 0 (Work.FTS.PhiStar.RemSource α ψ) z *
        Work.FTS.PhiStar.Gegenbauer.eFam 0 θ = 0 := by
      rw [acoeff_RemSource, bmode_zero ψ hψ.moment]
      simp
    rw [hz0, norm_zero]
    exact mul_nonneg (le_of_lt hKpos) (by positivity)
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    rw [Real.norm_eq_abs, acoeff_RemSource]
    calc |α ^ 2 * bmode m ψ
              * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        = |α ^ 2| * |bmode m ψ|
            * |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by rw [abs_mul, abs_mul, abs_mul]
      _ = α ^ 2 * |bmode m ψ|
            * |Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z|
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| := by
          rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ α ^ 2)]
      _ ≤ (α ^ 2 * (Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ))))
            * (Cr * (1 + 1 / z) * ((m : ℝ) + 1) ^ (-(2 : ℝ)))
            * (Cg * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ))) := by
          have hb := hdec m hm1
          have hr := hrad m hm1 z hz
          have he := hgr m θ hθ
          gcongr
      _ = K * ((m : ℝ) + 1) ^ (-(3 : ℝ)) := by
          have hp : ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)) * ((m : ℝ) + 1) ^ (-(2 : ℝ))
              * ((m : ℝ) + 1) ^ ((3 / 2 : ℝ)) = ((m : ℝ) + 1) ^ (-(3 : ℝ)) := by
            rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity)]
            norm_num
          rw [← hp, hK]
          ring

end Work.FTS.PhiStar.Series
