/-
Copyright: work module for the Elgindi finite-time singularity project.

# The one-dimensional radial integration by parts on `(0,∞)`, with the boundary
# terms *derived* rather than assumed

`Work.FTS.StrongPersist.N6Trans.L6Flux.zibp_Ioi_of_integrable` is the weighted
`z`-integration by parts

  `∫_{(0,∞)} φ V V' = -(1/2) ∫_{(0,∞)} φ' V²`

for functions `φ`, `V` differentiable on `(0,∞)` with derivatives `φ'`, `V'`, the two products
`φ V V'` and `φ' V²` integrable on `(0,∞)`, the pointwise bound
`|φ z| ≤ Mf · z · w(z)²` (`w z = (1+z)²/z²`) on `z ≥ 0`, and `w(z)² V(z)² ∈ L¹(0,∞)`.

Neither boundary term is a hypothesis.  The bound `|φ z| ≤ Mf · z · w(z)²` gives
`|F z| ≤ max (Mf/2) 1 · z (w z V z)²` for `F z = (1/2) φ z V z²`, so the integrability of
`(w z V z)²` forbids `|V|` from behaving like `z^{-1/2}` on a ray or near `0`, and hence forces
`F z → 0` both as `z → +∞` and as `z → 0⁺`.  Those two limits are supplied by the proved,
`sorry`-free one-dimensional lemmas
`Work.FTS.H2.Transport3Aux.MismatchBad.zibp_lim_atTop` and `…zibp_lim_nearZero`.  With them the
identity is the fundamental theorem of calculus for `F` on `(0,∞)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.H2.Transport3Aux.MismatchBad.zibp_lim_atTop
import Submission.Work.FTS.H2.Transport3Aux.MismatchBad.zibp_lim_nearZero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.L6Flux

set_option autoImplicit false
-- `hMf` is genuinely unused: for `Mf < 0` the pointwise bound is unsatisfiable for `z > 0`,
-- and for `Mf = 0` (`φ ≡ 0`) the general argument below applies unchanged.
set_option linter.unusedVariables false

/-- `𝓝[≥] a` from `𝓝[>] a`: if `F → b` along `𝓝[>] a` and `F a = b`, then `F` tends to `F a`
along `𝓝[≥] a` (i.e. `F` is continuous within `Ici a` at `a`).  Proved through the basis
`Ico a u` of `𝓝[Ici a] a`. -/
private theorem tendsto_Ici_of_tendsto_Ioi {F : ℝ → ℝ} {a b : ℝ}
    (h : Filter.Tendsto F (nhdsWithin a (Set.Ioi a)) (nhds b)) (hb : F a = b) :
    Filter.Tendsto F (nhdsWithin a (Set.Ici a)) (nhds (F a)) := by
  rw [hb]
  intro t ht
  obtain ⟨u, hau, hu⟩ := (nhdsGT_basis a).mem_iff.mp (h ht)
  refine (nhdsGE_basis_Ico a).mem_iff.mpr ⟨u, hau, ?_⟩
  rintro x ⟨hax, hxu⟩
  rcases eq_or_lt_of_le hax with rfl | hlt
  · simp only [Set.mem_preimage]
    rw [hb]
    exact mem_of_mem_nhds ht
  · exact hu ⟨hlt, hxu⟩

/-- **Integration by parts on `(0,∞)` without boundary hypotheses.**  If `φ` and `V` are
differentiable on `(0,∞)` with derivatives `φ'` resp. `V'`, the products `φ V V'` and `φ' V²`
are integrable on `(0,∞)`, `|φ z| ≤ Mf · z w(z)²` and `(w V)² ∈ L¹(0,∞)`, then
`∫_{0}^{∞} φ V V' = -(1/2) ∫_{0}^{∞} φ' V²`. -/
theorem zibp_Ioi_of_integrable {Mf : ℝ} (hMf : 0 ≤ Mf) {φ φ' V V' : ℝ → ℝ}
    (hderivφ : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt φ (φ' z) z)
    (hderivV : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt V (V' z) z)
    (hint1 : MeasureTheory.IntegrableOn (fun z => φ z * V z * V' z) (Set.Ioi (0 : ℝ)))
    (hint2 : MeasureTheory.IntegrableOn (fun z => φ' z * V z ^ 2) (Set.Ioi (0 : ℝ)))
    (hφbnd : ∀ z ∈ Set.Ici (0 : ℝ), |φ z| ≤ Mf * (z * (Work.Spaces.w z) ^ 2))
    (hintV : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * V z ^ 2) (Set.Ioi (0 : ℝ))) :
    ∫ z in Set.Ioi (0 : ℝ), φ z * V z * V' z
      = -(1 / 2) * ∫ z in Set.Ioi (0 : ℝ), φ' z * V z ^ 2 := by
  -- `φ 0 = 0`, because the bound at `z = 0` reads `|φ 0| ≤ Mf · 0 = 0`
  have hφ0 : φ 0 = 0 := by
    have h := hφbnd 0 (Set.mem_Ici.mpr le_rfl)
    simp only [zero_mul, mul_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  set F : ℝ → ℝ := fun z => (1 / 2) * (φ z * V z ^ 2) with hF
  set F' : ℝ → ℝ := fun z => (1 / 2) * φ' z * V z ^ 2 + φ z * V z * V' z with hF'
  have hF0 : F 0 = 0 := by
    show (1 / 2) * (φ 0 * V 0 ^ 2) = 0
    rw [hφ0]
    ring
  -- the pointwise derivative of `F`
  have hderivF : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt F (F' z) z := by
    intro z hz
    have h1 := ((hderivφ z hz).mul ((hderivV z hz).pow 2))
    have h2 := h1.const_mul (1 / 2)
    convert h2 using 1
    rw [hF']
    simp only [Pi.pow_apply]
    ring_nf
  -- `F'` is integrable
  have hintF : MeasureTheory.IntegrableOn F' (Set.Ioi (0 : ℝ)) := by
    have h3 : MeasureTheory.IntegrableOn (fun z => (1 / 2) * φ' z * V z ^ 2)
        (Set.Ioi (0 : ℝ)) :=
      (hint2.const_mul (1 / 2)).congr (Filter.Eventually.of_forall fun z => by ring)
    have h4 : MeasureTheory.IntegrableOn (fun z => φ z * V z * V' z) (Set.Ioi (0 : ℝ)) := hint1
    refine (h3.add h4).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply, hF']
  -- the `L¹`-bound on `(w V)²`
  have hG2 : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z * V z) ^ 2) (Set.Ioi 0) :=
    hintV.congr (Filter.Eventually.of_forall fun z => by ring)
  -- the pointwise bound `|F z| ≤ C · z · (w z V z)²` with `C > 0`
  have hC : (0 : ℝ) < max (Mf / 2) 1 := lt_of_lt_of_le zero_lt_one (le_max_right (Mf / 2) 1)
  have hbdF : ∀ z, 0 ≤ z → |F z| ≤ max (Mf / 2) 1 * (z * (Work.Spaces.w z * V z) ^ 2) := by
    intro z hz
    have h1 : |φ z| ≤ Mf * (z * (Work.Spaces.w z) ^ 2) := hφbnd z (Set.mem_Ici.mpr hz)
    have hsq : (0 : ℝ) ≤ z * (Work.Spaces.w z * V z) ^ 2 := mul_nonneg hz (sq_nonneg _)
    calc |F z| = (1 / 2) * (|φ z| * V z ^ 2) := by
          show |(1 / 2) * (φ z * V z ^ 2)| = (1 / 2) * (|φ z| * V z ^ 2)
          rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_mul,
            abs_of_nonneg (sq_nonneg (V z))]
      _ ≤ (1 / 2) * ((Mf * (z * (Work.Spaces.w z) ^ 2)) * V z ^ 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (sq_nonneg _)) (by norm_num)
      _ = (Mf / 2) * (z * (Work.Spaces.w z * V z) ^ 2) := by ring
      _ ≤ max (Mf / 2) 1 * (z * (Work.Spaces.w z * V z) ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left (Mf / 2) 1) hsq
  -- the two boundary limits of `F` (this is where the hypotheses on `V` are used)
  have hFtop : Filter.Tendsto F Filter.atTop (nhds 0) :=
    Work.FTS.H2.Transport3Aux.MismatchBad.zibp_lim_atTop hC hderivF hintF hbdF hG2
  have hF0lim : Filter.Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Work.FTS.H2.Transport3Aux.MismatchBad.zibp_lim_nearZero hC hderivF hintF hbdF hG2
  have hcont : ContinuousWithinAt F (Set.Ici 0) 0 :=
    tendsto_Ici_of_tendsto_Ioi hF0lim hF0
  -- the fundamental theorem of calculus on `(0,∞)`
  have hFTC : (∫ z in Set.Ioi (0 : ℝ), F' z) = 0 := by
    rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderivF hintF hFtop, hF0,
      sub_zero]
  -- split the integral and conclude
  have hsplit : (∫ z in Set.Ioi (0 : ℝ), F' z)
      = (1 / 2) * (∫ z in Set.Ioi (0 : ℝ), φ' z * V z ^ 2)
        + ∫ z in Set.Ioi (0 : ℝ), φ z * V z * V' z := by
    have h3 : MeasureTheory.IntegrableOn (fun z => (1 / 2) * φ' z * V z ^ 2)
        (Set.Ioi (0 : ℝ)) :=
      (hint2.const_mul (1 / 2)).congr (Filter.Eventually.of_forall fun z => by ring)
    have h4 : MeasureTheory.IntegrableOn (fun z => φ z * V z * V' z) (Set.Ioi (0 : ℝ)) := hint1
    rw [show (∫ z in Set.Ioi (0 : ℝ), F' z)
        = ∫ z in Set.Ioi (0 : ℝ),
            ((1 / 2) * φ' z * V z ^ 2 + φ z * V z * V' z) from by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => ?_)
      rw [hF']]
    have h5 : (∫ z in Set.Ioi (0 : ℝ), (1 / 2) * φ' z * V z ^ 2)
        = (1 / 2) * ∫ z in Set.Ioi (0 : ℝ), φ' z * V z ^ 2 := by
      rw [show (fun z => (1 / 2) * φ' z * V z ^ 2)
          = fun z => (1 / 2) * (φ' z * V z ^ 2) from by funext z; ring,
        MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_add h3 h4, h5]
  linarith [hFTC, hsplit]

end Work.FTS.StrongPersist.N6Trans.L6Flux
