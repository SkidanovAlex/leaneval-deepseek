/-
Copyright: work module for the Elgindi finite-time singularity project.

# A.e. radial-slice integrability of a mixed slot against the plain weight `w²`

For `f` which is `C^∞` on the open quadrant (`Work.FTS.EllipticEst.SmoothOpen`) and honestly
in `ℋ⁴` (`Work.Spaces.HkMem α 4 f`), and for a mixed slot `D_z^j D_θ^i f` with `1 ≤ i` and
`i + j ≤ 4`, the radial function

  `s ↦ (D_z^j D_θ^i f(s, σ))² · w(s)²`      (`w(s) = (1+s)²/s²`)

is integrable on `Iz = [0,∞)` for almost every angle `σ ∈ Iθ = [0,π/2]`
(`Work.FTS.StrongEps.SupPort.ae_integrableOn_mixed_sq_w`).

The proof assembles three ingredients, each of which says exactly one thing.

* **Pointwise domination by the `ℋ⁴`-integrand**
  (`Work.FTS.StrongEps.SupPort.AuxMixSq.mixed_sq_w_le_HkIntegrand`): on the open quadrant

    `(D_z^jD_θ^if · w)² ≤ (D_z^jD_θ^if · W)²`  because  `W = w · sin(2θ)^{-γ/2}` and
    `sin(2θ)^{-γ} ≥ 1` for `θ ∈ (0,π/2)` (`γ = 1 + α/10 > 0` and `0 < sin(2θ) ≤ 1`),

  and `(D_z^jD_θ^if · W)²` is one of the summands of `HkIntegrand α 4 f`
  (`Work.Spaces.sq_le_HkIntegrand_mixed`).  Hence, for every interior angle `σ`,

    `(D_z^jD_θ^if(s,σ) · w(s))² ≤ HkIntegrand α 4 f s σ`   for **all** `s`
    (the inequality is *pointwise in `s`*, which is why a single `Integrable.mono'` suffices).

* **A.e. strong measurability of the radial slice**
  (`Work.FTS.StrongEps.SupPort.AuxMixSq.aesm_zslice_mixed_sq_w`): at an interior angle the
  `z`-slice of `f` is `C^∞` on `(0,∞)` (`Work.FTS.EllipticEst.SmoothOpen.curry_z`), so the
  slice `s ↦ (D_z^jD_θ^if(s,σ) · w(s))²` is continuous there and hence a.e. strongly
  measurable for `volume.restrict Iz` (the point `s = 0` being null).

* **Fubini for the `ℋ⁴`-integrand of an open-class datum**
  (`Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open`, Tonelli): for almost every angle the
  radial slice `s ↦ HkIntegrand α 4 f s σ` is integrable on `Iz`.

The a.e. statement over `Iθ` is then immediate: the two a.e. events in `σ` (the Fubini slice
integrability and `σ ∈ (0,π/2)`) hold simultaneously, and at each such angle the domination
of the `ℋ⁴`-integrand bounds our slice by an integrable one.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.TransportS.SupDzAux.SdaAux
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.StrongEps.SupPort.AuxMixSq.mixed_sq_w_le_HkIntegrand
import Submission.Work.FTS.StrongEps.SupPort.AuxMixSq.aesm_zslice_mixed_sq_w

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.SupPort

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- **A.e. radial-slice integrability of a mixed slot against the plain weight `w²`.**

For `f` of class `C^∞` on the open quadrant and in `ℋ⁴`, and for every mixed slot
`D_z^j D_θ^i f` with `1 ≤ i` and `i + j ≤ 4`, the radial function
`s ↦ (D_z^j D_θ^i f(s,σ))² · w(s)²` is integrable on `Iz = [0,∞)` for almost every
`σ ∈ Iθ`. -/
theorem ae_integrableOn_mixed_sq_w {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    (j i : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) :
    ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn
        (fun s => (Work.Spaces.mixed j i f s σ) ^ 2 * (Work.Spaces.w s) ^ 2) Work.Spaces.Iz := by
  -- Tonelli for the `ℋ⁴`-integrand: a.e. angle has an integrable radial `ℋ⁴`-slice.
  obtain ⟨-, -, hsliceHK⟩ := Work.FTS.TransportS.SupDzAux.sda_HkSqSwap_open α f hF hmem
  -- Almost every angle of `Iθ` is interior.
  have hIoo : ∀ᵐ σ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      σ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
    rw [Work.FTS.EllipticEst.restrict_Iθ_eq_restrict_Ioo]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  filter_upwards [hsliceHK, hIoo] with σ hInt hσ
  -- At such an angle the weighted mixed square is bounded pointwise in `s` by the
  -- (integrable) radial `ℋ⁴`-slice, and it is a.e. strongly measurable.
  refine MeasureTheory.Integrable.mono' hInt
    (Work.FTS.StrongEps.SupPort.AuxMixSq.aesm_zslice_mixed_sq_w hF j i hσ) ?_
  exact Filter.Eventually.of_forall fun s => by
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    exact Work.FTS.StrongEps.SupPort.AuxMixSq.mixed_sq_w_le_HkIntegrand hα j i hi hij hσ

end Work.FTS.StrongEps.SupPort
