/-
Copyright: work module for the Elgindi finite-time singularity project.

# `ℋ^k`-membership is insensitive to the values off the open quadrant

`Work.Spaces.HkMem α k f` asks for the integrability of the `ℋ^k`-integrand of `f`, slice by
slice over `Iθ = [0,π/2]` and then over `Iz = [0,∞)`.  `AgreeOnQ f g` only fixes `g` on the
*open* quadrant `(0,∞) × (0,π/2)`; off it — on the two angular boundary lines and on the
radial line `z = 0` — `g` may differ from `f` arbitrarily.

None of that matters for `HkMem`:

* on the open quadrant the weighted iterated derivatives of `f` and `g` coincide, so the two
  integrands agree there (`HkIntegrand_congr`), and the complement inside `Iθ` is the null set
  `{0, π/2}`;
* on `z = 0` the integrand vanishes identically anyway, because the radial weight `w` occurs
  as a factor of every summand (`w 0 = 0`).

Hence the two integrands are equal almost everywhere on each `θ`-slice, and the two `θ`-slice
integrals are equal at every `z ∈ Iz`; both conjuncts of `HkMem` transfer.
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.HkSq_congr_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.RPFresh

/-- At `z = 0` the `ℋ^k`-integrand vanishes identically: the radial weight `w` is a factor of
every summand and `w 0 = 0`. -/
private lemma HkIntegrand_zero_z (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  simp only [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]
  simp

/-- **`ℋ^k`-membership only depends on the open quadrant.**  If `f` and `g` agree on
`(0,∞) × (0,π/2)` then `f ∈ ℋ^k` implies `g ∈ ℋ^k`. -/
theorem HkMem_of_agreeOnQ {α : ℝ} {k : ℕ} {f g : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.AgreeOnQ f g) (hf : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k g := by
  have hIoo : Set.Ioo 0 (π / 2) =ᵐ[volume] Work.Spaces.Iθ := by
    show Set.Ioo 0 (π / 2) =ᵐ[volume] Set.Icc 0 (π / 2)
    exact MeasureTheory.Ioo_ae_eq_Icc
  -- the two `θ`-slice integrals agree at every `z ∈ Iz`
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ)
        = ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      have h1 : (fun θ : ℝ => Work.Spaces.HkIntegrand α k g 0 θ) = fun _ => (0 : ℝ) :=
        funext fun θ => HkIntegrand_zero_z α k g θ
      have h2 : (fun θ : ℝ => Work.Spaces.HkIntegrand α k f 0 θ) = fun _ => (0 : ℝ) :=
        funext fun θ => HkIntegrand_zero_z α k f θ
      rw [h1, h2]
    · rw [MeasureTheory.setIntegral_congr_set hIoo.symm,
        MeasureTheory.setIntegral_congr_set hIoo.symm]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun θ hθ => (HkIntegrand_congr h z θ hz0 hθ.1 hθ.2).symm)
  constructor
  · -- integrability of each `θ`-slice
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      have h1 : (fun θ : ℝ => Work.Spaces.HkIntegrand α k g 0 θ) = fun _ => (0 : ℝ) :=
        funext fun θ => HkIntegrand_zero_z α k g θ
      rw [h1]
      exact MeasureTheory.integrableOn_zero
    · have h1 : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k f z θ)
          (Set.Ioo 0 (π / 2)) :=
        MeasureTheory.IntegrableOn.congr_set_ae (hf.1 z hz) hIoo
      have h2 : IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k g z θ)
          (Set.Ioo 0 (π / 2)) :=
        MeasureTheory.IntegrableOn.congr_fun h1
          (fun θ hθ => HkIntegrand_congr h z θ hz0 hθ.1 hθ.2) measurableSet_Ioo
      exact MeasureTheory.IntegrableOn.congr_set_ae h2 hIoo.symm
  · -- integrability of the `z`-integral
    exact MeasureTheory.IntegrableOn.congr_fun hf.2
      (fun z hz => (hinner z hz).symm) measurableSet_Ici

end Work.FTS.EllipticEst.RPFresh
