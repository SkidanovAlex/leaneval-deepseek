/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS/StrongPersist/SP6/WlInf6OfFlatW.lean` — flat `𝒲^{6,∞}` from the flat data

The `𝒲^{6,∞}`-clause of the `StrongPersist` star package consumes `𝒲^{6,∞}`-honesty of a
function `f` which is only known to be *flat* on the open quadrant
(`Work.FTS.VocabO2.FlatW 6 f K`) and to vanish off it.  This module proves the transfer

`FlatW 6 f K` + `zeroOff` + `SmoothOpen f` + `0 < α ≤ 1`  ⟹  `WlInfMem α 6 f ∧ WlInf α 6 f ≤ C·K`

with a *universal* constant `C` (independent of `α`).

This is the order-`6` companion of the proved `Work.FTS.PhiStar.wlInf_of_zeroOff` (order `4`);
the mathematical content is identical and is recalled there:

* **radial slots** (`(z+1)^k ∂_z^k f`, `k ≤ 6`): the flat bound holds on the open quadrant; on
  the boundary `θ ∈ {0, π/2}` the whole `z`-slice of `f` vanishes (because those `θ` are off
  `Q0`), and on `z = 0` the slice `z' ↦ f z' θ` vanishes on `(-∞,0]`, so every `∂_z`-iterate at
  `0` is `0` (Lean's `deriv` is totalised, and a function vanishing on a left neighbourhood has
  derivative `0` at the junction).  This is the `l = 6` instance of the companion
  `Work.FTS.StrongPersist.SP6.RadialSlot6`.

* **angular slots** (`(z+1)^k D_θ^j f · sin(2θ)^{-α/5}/(α + sin 2θ)`, `1 ≤ j`, `k + j ≤ 6`):
  `D_θ = sin(2θ)∂_θ` is a derivation, whence
  `D_θ^j f = ∑_{a<j} C(j-1,a) (D_θ^a sin 2·) (D_θ^{j-1-a} ∂_θ f)`;
  each `D_θ^a(sin 2·)` carries a factor `sin(2θ)` for `a ≤ 5`, while
  `(z+1)^k D_θ^{j-1-a}(∂_θ f)` is exactly one of the quantities bounded by `K` in `FlatW 6`.
  The angular weight is consumed by `sin_rpow_slack`: `sin(2θ)^{1-α/5}/(α + sin 2θ) ≤ 2`
  uniformly for `α ∈ (0,1]`, `sin(2θ) ∈ [0,1]`.  This is the companion
  `Work.FTS.StrongPersist.SP6.AngSlot6`.

* **Assembly** (`WlInf6_of_bounds` below, the content of this file): `WlInf` is a sum of `7`
  radial and at most `49` angular suprema, each bounded by a universal multiple of `K`; the
  bookkeeping gives `WlInf α 6 f ≤ (7 + 49·C_ang)·K`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.VocabO2
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.PhiStar.wlInf_of_zeroOff
import Submission.Work.FTS.StrongPersist.SP6.AngSlot6
import Submission.Work.FTS.StrongPersist.SP6.RadialSlot6

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.SP6

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

/-! ## The assembly

`WlInf6_of_bounds` isolates the bookkeeping: given the two pointwise families of bounds
(the angular slot bound and the radial slot bound) it produces the `WlInfMem`-honesty and the
numerical estimate.  Both inputs are supplied by the two companion modules
`FTS/StrongPersist/SP6/AngSlot6.lean` and `FTS/StrongPersist/SP6/RadialSlot6.lean`. -/

/-- **The `𝒲^{6,∞}`-transfer, conditional on the two pointwise slot bounds.** -/
theorem WlInf6_of_bounds
    (hAng : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (K : ℝ),
      0 < α → α ≤ 1 → 0 ≤ K →
      (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW 6 f K →
      ∀ (j k : ℕ), 1 ≤ j → k + j ≤ 6 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        |(z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))| ≤ C * K)
    (hRad : ∀ (f : ℝ → ℝ → ℝ) (K : ℝ), 0 ≤ K →
      (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW 6 f K →
      ∀ k : ℕ, k ≤ 6 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        |(z + 1) ^ k * Work.Spaces.pzIter k f z θ| ≤ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (K : ℝ),
      0 < α → α ≤ 1 → (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
      Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW 6 f K →
      Work.Spaces.WlInfMem α 6 f ∧ Work.Spaces.WlInf α 6 f ≤ C * K := by
  obtain ⟨Ca, hCa, hAng'⟩ := hAng
  refine ⟨7 + 49 * Ca, by positivity, ?_⟩
  intro α f K hα0 hα1 hzero hf hF
  -- `K ≥ 0`: the flat bound at the interior point `(1,1)` bounds `|f 1 1|`.
  have hK : 0 ≤ K := by
    have h := (hF 1 1 (by norm_num) (by norm_num)
      (by linarith [Real.pi_gt_three])).1 0 (by norm_num)
    have h' : |f 1 1| ≤ K := by simpa using h
    exact le_trans (abs_nonneg _) h'
  have hCaK : 0 ≤ Ca * K := mul_nonneg hCa.le hK
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · -- radial slots of `WlInfMem`
    intro k hk
    exact Work.Spaces.supFinite_of_pointwise
      (fun z hz θ hθ => hRad f K hK hzero hf hF k hk z hz θ hθ)
  · -- angular slots of `WlInfMem`
    intro j hj k hk hj1 hkj
    exact Work.Spaces.supFinite_of_pointwise
      (fun z hz θ hθ => hAng' α f K hα0 hα1 hK hzero hf hF j k hj1 hkj z hz θ hθ)
  · -- the numerical bound
    rw [Work.Spaces.WlInf]
    have h1 : (∑ k ∈ Finset.range (6 + 1),
        Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ))
        ≤ ((6 : ℝ) + 1) * K := by
      calc _ ≤ ∑ _k ∈ Finset.range (6 + 1), K := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk6 : k ≤ 6 := by rw [Finset.mem_range] at hk; omega
            exact Work.Spaces.supAbs_le
              (fun z hz θ hθ => hRad f K hK hzero hf hF k hk6 z hz θ hθ)
        _ = ((6 : ℝ) + 1) * K := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            norm_num
    have h2 : (∑ j ∈ Finset.range (6 + 1), ∑ k ∈ Finset.range (6 + 1),
        if 1 ≤ j ∧ k + j ≤ 6 then
          Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
            * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0) ≤ ((6 : ℝ) + 1) * ((6 : ℝ) + 1) * (Ca * K) := by
      calc _ ≤ ∑ _j ∈ Finset.range (6 + 1), ∑ _k ∈ Finset.range (6 + 1), (Ca * K) := by
            refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
            split_ifs with hcond
            · exact Work.Spaces.supAbs_le (fun z hz θ hθ =>
                hAng' α f K hα0 hα1 hK hzero hf hF j k hcond.1 hcond.2 z hz θ hθ)
            · exact hCaK
        _ = ((6 : ℝ) + 1) * ((6 : ℝ) + 1) * (Ca * K) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Finset.sum_const,
              Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    calc (∑ k ∈ Finset.range (6 + 1),
            Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ))
          + (∑ j ∈ Finset.range (6 + 1), ∑ k ∈ Finset.range (6 + 1),
              if 1 ≤ j ∧ k + j ≤ 6 then
                Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
                  * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
                  * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
              else 0)
        ≤ ((6 : ℝ) + 1) * K + ((6 : ℝ) + 1) * ((6 : ℝ) + 1) * (Ca * K) :=
          add_le_add h1 h2
      _ = (7 + 49 * Ca) * K := by ring

theorem WlInf6OfFlatW : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f : ℝ → ℝ → ℝ) (K : ℝ),
    0 < α → α ≤ 1 → (∀ z θ : ℝ, (z, θ) ∉ Work.FTS.EllipticEst.Q0 → f z θ = 0) →
    Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO2.FlatW 6 f K →
    Work.Spaces.WlInfMem α 6 f ∧ Work.Spaces.WlInf α 6 f ≤ C * K := by
  refine WlInf6_of_bounds Work.FTS.StrongPersist.SP6.AngSlot6 ?_
  intro f K hK hzero hf hF k hk z hz θ hθ
  exact Work.FTS.StrongPersist.SP6.RadialSlot6 (l := 6) (k := k) hK hf hzero hF hk z hz θ hθ

end Work.FTS.StrongPersist.SP6
