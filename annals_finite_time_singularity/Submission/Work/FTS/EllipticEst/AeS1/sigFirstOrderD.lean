import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.ProductTools
import Submission.Work.FTS.EllipticEst.AeS1.SigFirstOrderDefs
import Submission.Work.FTS.EllipticEst.AeS1.SigFirstOrderAux1
import Submission.Work.FTS.EllipticEst.AeS1.SigFirstOrderSlots
import Submission.Work.FTS.EllipticEst.Dispatch.hkMemGradUD

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.AeS1

/-!
**The σ-weighted first-order energy inequality** for the almost-everywhere class
`H2W.Ae.AeData` (Elgindi, Annals 194 (2021), Step 1/Step 2 hybrid): it bounds both
`α²‖z∂_zu‖²_ρ` (the radial slot) and `‖u/cos θ‖²_ρ` (the `Ψ`-slot) by `C(‖G‖²_ρ + ‖u‖²_ρ)`.

## Route (all ingredients are proved and axiom-clean; nothing here is a duplicate statement)

Pair `bslOp α u = G` with `u·w²σ`, `σ = sin(2θ)^{-η}` (the *first-order* pairing, not the
`-∂_θθu` pairing of Step 2), i.e. use the **σ-weighted slice self-form**
  `∫_θ (Lzero1 u z ·)(u z ·) σ  =  ∫_θ (∂_θu)²σ + ½∫_θ (u/cos θ)²σ - 6∫_θ u²σ`
(proved for the unweighted case as `Honest.HonSliceSelfForm` / `H2W.AeProof.AeSliceSelfForm`;
the σ-weighted case follows by the same primitive
`F θ = -(v'θ)v θ·σ - ½ v θ²·(∂_θ(σ))-type` computation, with the two ingredients
  * `∂_θθ(sin(2θ)^{-η}) = 4η(η+1)cos²(2θ)sin^{-(2+η)}(2θ) + 4η sin^{-η}(2θ)` (the paper's
    identity), and
  * the sharp Hardy inequality `Work.FTS.EllipticEst.hardy_shift_two_same_weight`
    (`∫f²sin^{-(2+η)}(2θ) ≤ (1+η)^{-2}∫(f')²σ + C∫f²σ`, proved) applied to the slice `u z ·`,
    together with the elementary bound `|tan θ·∂_θσ| ≤ η sec²θ·σ`;
  these give, a.e. in `z`,
  `((1-η)/(1+η))∫_θ(∂_θu)²σ + ((1-η)/2)∫_θ(u/cos θ)²σ ≤ ∫_θ (Lzero1 u·u)σ + C∫_θ u²σ`
  (the numerical gains `(1-η)/(1+η) = 1/199 > 0` and `(1-η)/2 > 0` are exactly the ones used in
  the paper's `I₁`).
Then multiply by `Wcut χ = χ·w²` for the cutoff family `Work.FTS.EllipticEst.cut n`, integrate in
`z`, and use the θ-sliced radial integration by parts
`Work.FTS.EllipticEst.Dispatch.sliceZibpD` / `remov.ibpZZ`/`ibpZ` (`χ` compactly supported in
`(0,∞)`):
  `∫_z χw²z²u''u = -∫_zχw²(D_zu)² + ½∫_z(z²χw²)''u²`,  `∫_zχw²zu'u = -½∫_z(zχw²)'u²`;
AM–GM (`2|ab| ≤ εa² + b²/ε`) absorbs every cross term into the two positive slots, and
`∫∫χw²|G||u| ≤ ½∫∫χw²G²σ + ½∫∫χw²u²` (`1/σ ≤ 1`) gives the source slot.  Passing to the limit
`χ = cut n` (monotone convergence for the nonnegative slots, `AeCutErr` for the truncation
error, the case `∫⁻w²∫⁻u²σ = ⊤` being trivial) gives the two inequalities of the statement.
The first `L2Mem` conjunct is `HkMem α 0 (grad u)`, available as
`Work.FTS.EllipticEst.AeS1.hkMem_gradU` (`Dispatch.hkMemGradU`).
The third conjunct (`u/cos θ`) follows from the same σ-weighted pairing: the
`sec²θ`-slot above controls `∫_θ(u/cos θ)²σ` directly (no further Hardy is needed here, since
`sec²θ ≥ 1`).
-/

set_option autoImplicit false

/-- At level `0` the `ℋ⁰`-integrand is the square of the `σ^{1/2}`-weighted profile. -/
theorem hkIntegrand_zero_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand]
  norm_num

/-- `L2Mem` of the `σ^{1/2}`-weighted profile is `HkMem α 0`. -/
theorem l2mem_iff_hkMem {α : ℝ} {f : ℝ → ℝ → ℝ} :
    Work.Spaces.L2Mem (fun z θ => f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
      ↔ Work.Spaces.HkMem α 0 f := by
  constructor
  · intro h
    exact ⟨fun z hz => by simpa only [hkIntegrand_zero_eq] using h.1 z hz,
      by simpa only [hkIntegrand_zero_eq] using h.2⟩
  · intro h
    exact ⟨fun z hz => by simpa only [hkIntegrand_zero_eq] using h.1 z hz,
      by simpa only [hkIntegrand_zero_eq] using h.2⟩

theorem sigFirstOrderD : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ), Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.L2Mem (fun z θ => z * Work.Spaces.pz u z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ∧
      α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) ∧
      Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)
        ≤ C * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := by
  obtain ⟨Cz, hCzpos, hz⟩ := zSlotBound
  obtain ⟨Cc, hCcpos, hc⟩ := cSlotBound
  refine ⟨max Cz Cc, lt_of_lt_of_le hCzpos (le_max_left _ _), ?_⟩
  intro α u G hAe
  have hsum0 : 0 ≤ Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u :=
    add_nonneg (Work.Spaces.HkSq_nonneg α 0 G) (Work.Spaces.HkSq_nonneg α 0 u)
  have hgrad : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) :=
    Work.FTS.EllipticEst.Dispatch.hkMem_gradUD α u G hAe
  refine ⟨?_, ?_, ?_⟩
  · exact (l2mem_iff_hkMem (α := α) (f := Work.FTS.EllipticEst.H2W.Ae.grad u)).mpr hgrad
  · calc α ^ 2 * Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ Cz * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := hz α u G hAe
      _ ≤ max Cz Cc * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hsum0
  · calc Work.Spaces.HkSq α 0 (fun z θ => u z θ / Real.cos θ)
        ≤ Cc * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) := hc α u G hAe
      _ ≤ max Cz Cc * (Work.Spaces.HkSq α 0 G + Work.Spaces.HkSq α 0 u) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hsum0

end Work.FTS.EllipticEst.AeS1
