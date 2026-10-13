/-
Copyright: work module for the Elgindi finite-time singularity project.

# `momentDzZero`: the angular moment of every `D_z`-iterate vanishes a.e. in `z`

Let `F` be smooth on the open quadrant `(0,∞) × (0,π/2)` with `F ∈ ℋ^k` in the sense of
`Work.Spaces.HkMem`, and suppose its angular moment `F_*(F)(z) = ∫_θ F(z,θ) sinθcos²θ dθ`
vanishes for every `z > 0`.  Then the angular moment of every radial iterate `D_z^m F`,
`m ≤ k`, vanishes for almost every `z > 0`:

`∀ m ≤ k, ∀ᵐ z > 0, ∫_θ D_z^m F(z,θ) sinθcos²θ dθ = 0`.

This is the `CptQ`/`exists_cptQ_approx` ingredient: the moment condition on the source is
inherited by all its radial derivatives, so it survives the cut-off approximation.

## The argument

The moment is propagated by the *integrated* chain rule for `F_*` along `D_z = z ∂_z`:
`Work.FTS.EllipticEst.GbarSin.FstarDzIter_chain_open` (proved, axiom-clean) states that for
`j + 1 ≤ k`

`F_*(D_z^j F)(z) - F_*(D_z^j F)(s) = ∫_s^z F_*(D_z^{j+1} F)(r)/r dr`  for `0 < s ≤ z`,

which is exactly the hypothesis shape of
`Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_moment_chain`: the a.e. vanishing of the
primitive `W = F_*(D_z^j F)` together with the interval integrability of the divided moment
`V r = F_*(D_z^{j+1} F)(r)/r` yields the a.e. vanishing of `V` (the primitive is continuous
and a.e. constant, hence constant, so its derivative `V` vanishes a.e.).

The interval integrability of `V` is the local-integrability estimate on the moments: for
`r > 0` the Cauchy–Schwarz bound
`|F_*(D_z^a F)(r)| ≤ ((π/2) ∫_θ HkIntegrand α k F(r,θ) + 1)/2`
(`GbarSin.Fstar_div_le_majorant`, divided by `r ≤ w(r)`) with `HkMem`'s integrability of the
iterated `HkIntegrand` in `r` (`GbarSin.majorant_integrableOn`) and a.e. strong measurability
of `r ↦ F_*(D_z^a F)(r)/r` (`GbarSin.Fstar_div_aesm`) gives `IntegrableOn` on `(0,t)`,
hence on the interval `(s,t]` with `0 < s`.

Everything here is complete (every step is a closed proof) and rests on
`[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs
import Submission.Work.FTS.EllipticEst.GbarSin.FstarDzIter_chain_open
import Submission.Work.FTS.EllipticEst.GbarSin.Fstar_local_integrableOn
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.AeBasic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.CptApp

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-- **Interval integrability of the divided angular moment.**  For `F` smooth on the open
quadrant with `F ∈ ℋ^k` and `a ≤ k`, the function `r ↦ F_*(D_z^a F)(r)/r` is interval
integrable on `[s,t]` for `0 < s < t`.

This is the local-integrability input of the moment chain
(`H2W.PsiSlices.ae_eq_zero_of_moment_chain`).  It follows from the majorant
`r ↦ ((π/2) ∫_θ HkIntegrand α k F(r,θ) + 1)/2`, which dominates the *undivided* moment and is
integrable on `(0,t)` by `HkMem`; the factor `1/r ≤ 1/s` is bounded on `[s,t]`. -/
private theorem intervalIntegrable_Fstar_DzIter_div {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F)
    {a : ℕ} (ha : a ≤ k) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    IntervalIntegrable (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter a F) r / r)
      MeasureTheory.volume s t := by
  have ht : 0 < t := lt_trans hs hst
  -- ## The majorant is integrable on `(0,z)`, hence the divided moment is
  have hIoo : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn
      (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter a F) r / r) (Set.Ioo 0 z) := by
    intro z hz
    have hmaj : MeasureTheory.IntegrableOn (fun r : ℝ => ((Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k F r θ) + 1) / 2) (Set.Ioo 0 z) :=
      Work.FTS.EllipticEst.GbarSin.majorant_integrableOn α k F hmem
        (fun r hr => by rw [Work.Spaces.Iz]; exact le_of_lt hr.1)
        (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    refine hmaj.mono' (Work.FTS.EllipticEst.GbarSin.Fstar_div_aesm F hF a) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    refine Eventually.of_forall fun r hr => ?_
    have hr0 : 0 < r := hr.1
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0]
    exact Work.FTS.EllipticEst.GbarSin.Fstar_div_le_majorant α k F hF hmem a ha hr0
  -- ## restrict to the interval `(s,t]` and convert to interval integrability
  have hIoc : MeasureTheory.IntegrableOn
      (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter a F) r / r) (Set.Ioc s t) :=
    (hIoo (t + 1) (by linarith)).mono_set
      (fun r hr => ⟨lt_trans hs hr.1, by linarith [hr.2]⟩)
  rw [intervalIntegrable_iff, Set.uIoc_of_le hst.le]
  exact hIoc

/-- **The angular moment of every radial iterate vanishes a.e.**  If `F` is smooth on the open
quadrant, `F ∈ ℋ^k`, and `F_*(F) = 0` on `(0,∞)`, then `F_*(D_z^m F) = 0` a.e. on `(0,∞)` for
every `m ≤ k`. -/
theorem momentDzZero {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α k F)
    (hFs : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0) :
    ∀ m : ℕ, m ≤ k → ∀ᵐ z ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi 0)),
      MeasureTheory.integral
        (MeasureTheory.Measure.restrict MeasureTheory.volume Work.Spaces.Iθ)
        (fun θ => Work.Spaces.DzIter m F z θ * Work.Elliptic.sinCos2 θ) = 0 := by
  -- ## a.e. vanishing of `F_*(D_z^j F)` for every `j ≤ k`, by induction on `j`
  have hmain : ∀ j : ℕ, j ≤ k →
      ∀ᵐ z ∂(MeasureTheory.Measure.restrict MeasureTheory.volume (Set.Ioi (0 : ℝ))),
        Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z = 0 := by
    intro j
    induction j with
    | zero =>
        intro _
        simpa using (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi hFs)
    | succ j ih =>
        intro hj
        have hj' : j ≤ k := Nat.le_of_succ_le hj
        -- the integrated chain rule for the angular moment along `D_z`
        have hchain : ∀ s z : ℝ, 0 < s → s ≤ z →
            Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z
              - Work.Elliptic.Fstar (Work.Spaces.DzIter j F) s
            = ∫ r in s..z, Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r / r :=
          fun s z hs hsz => Work.FTS.EllipticEst.GbarSin.FstarDzIter_chain_open
            α k F hsm hF j hj hs hsz
        -- the divided moment is interval integrable
        have hInt : ∀ a b : ℝ, 0 < a → a < b →
            IntervalIntegrable
              (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.DzIter (j + 1) F) r / r)
              MeasureTheory.volume a b :=
          fun a b ha hab => intervalIntegrable_Fstar_DzIter_div hsm hF hj ha hab
        have hV :=
          Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_moment_chain hchain (ih hj') hInt
        filter_upwards [hV, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
          with z hz hzpos
        rw [div_eq_zero_iff] at hz
        rcases hz with h | h
        · exact h
        · exact absurd h (ne_of_gt hzpos)
  intro m hm
  exact hmain m hm

end Work.FTS.PhiStar.Honesty.CptApp
