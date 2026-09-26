import Mathlib
import Submission.Work.LayerCont.FarTail.All
import Submission.Work.LayerCont.Glue.All
import Submission.Work.LayerCont.InteriorDD.All
import Submission.Work.LayerCont.WindowCapstone
import Submission.Work.LayerCont.Right.Jprime
import Submission.Work.LayerCont.Coinc.All
import Submission.Work.CKFinal.layerLowOne_eq_layerLowAt_far

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/CKFinal/DESIGN.md first (orchestrator design; your lemma is one node of its DAG; its §0 lists what is NOT actually proved and §5 what NOT to do). Clashes fixed by the lead (2026-09-25): Kaxis_bounded_compact's Pspace/Cseg/exists_local_bound_clean/… now carry a Kbc suffix; MiddleRange.Main's continuous_jInvariantFun is continuous_jInvariantFun_mr. Siblings run in parallel; import them when they land.

# windowChart_data  (namespace Work.CKFinal)

One chart per height s₀ > 0 on the line Re = 1 with: holomorphy ∀ r, 𝒟-side = paperLayer,
far side (Re > 1) = paperLayer + sinSqC r · resCorr r, even in r.

PROVED assets:
- s₀ > 1: `Work.LayerCont.FarTail.far_identity_data` (FarTail/Capstone.lean) — all three clauses.
- s₀ < 1: `Work.LayerCont.FarTail.far_identity_data_rev` (FarTail/CapstoneRev.lean) — needs
  `hdegCenter : jprime (onePlusI s₀) ≠ 0`; true for s₀ ≠ 1 (j real & strictly monotone on iℝ off i;
  see `Work.LayerCont.FarTail.jprime_ne_zero_far` (FarTail/Clean.lean) for s₀ > 1 and use
  j(1+is) = j(is), j(i/s) = j(is) to reduce s₀ < 1 to it).
- s₀ = 1: `Work.LayerCont.layerWindowContinuation_one` (WindowCapstone.lean) — holomorphy and 𝒟-side only.
- `Work.LayerCont.Glue.eqOn_of_mdifferentiableOn_of_preconnected` (Glue/TwoBall.lean),
  `Work.LayerCont.Glue.isPreconnected_inter_ball` (Glue/ConnBall.lean).
- far-side cleanliness/tail: `FarTail.clean_axis_of_web_re_gt_one`, `FarTail.tail_integrableOn_of_clean`,
  `FarTail.layerAt_eq_paperLayer_far` (FarTail/FarIdentity.lean).
These closures import cuspTile_seminorm (sorry) and Kaxis24_pair_gate (sorry) but the two capstones
are axiom-clean (#print axioms checked 2026-09-25) — keep it that way (#print axioms at the end).

Proof sketch:
1. s₀ ≠ 1: repackage far_identity_data(_rev) (W r := windowChart … r). Evenness: every r enters via
   r² (sinSqC, gaussWeight, resCorr, psi1 terms) — `simp`/`ring_nf` on the definitions.
2. s₀ = 1, far side: D⁺ := B(1+i, ε₁) ∩ {Re > 1} is preconnected (convex image in ℂ). paperLayer is
   holomorphic on D⁺ (points there are clean: orbit points near iℝ are τ−1 (Re>0) and ST⁻¹τ (Re<0);
   use the InteriorChart parametric engine). Pick s₀ ≠ 1 close to 1 with B(1+is₀,ε_{s₀}) ∩ D⁺ ≠ ∅;
   W₁ = W_{s₀} on B₁ ∩ B_{s₀} (identity theorem, agreement on the 𝒟-side part, which is a nonempty
   open subset because both balls are symmetric about Re = 1); on D⁺ ∩ B_{s₀}, W_{s₀} = pL + corr.
   Identity theorem on D⁺ ⇒ W₁ = pL + corr on D⁺.
3. Shrink ε to min over the pieces.

--imports: Submission.Work.LayerCont.FarTail.All Submission.Work.LayerCont.WindowCapstone Submission.Work.LayerCont.Glue.All Submission.Work.LayerCont.InteriorDD.All
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.CKFinal

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold
open Work.Asymptotics Work.LayerCont

/-- **The conclusion of the window chart at a height `s₀ > 0`**: there is a radius `ε > 0` and a
family `W r` holomorphic on `B(1 + i s₀, ε)`, equal to the paper's layer `paperLayer` on the
`𝒟`-side, equal to `paperLayer + sinSqC r · resCorr r` on the far side `1 < Re τ`, and even in
`r`. -/
def ChartClaim (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (s₀ : ℝ) (hs₀ : 0 < s₀) : Prop :=
  ∃ (ε : ℝ) (W : ℝ → UpperHalfPlane → ℂ), 0 < ε ∧
    (∀ r : ℝ, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (W r)
      (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) ε)) ∧
    (∀ (r : ℝ) (τ : UpperHalfPlane), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
      τ ∈ Work.Asymptotics.DomainD →
        W r τ = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) ∧
    (∀ (r : ℝ) (τ : UpperHalfPlane), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
      1 < τ.re →
        W r τ = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
          + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ) ∧
    (∀ (r : ℝ) (τ : UpperHalfPlane), W (-r) τ = W r τ)

/-! ## Evenness of the layer in the radial variable -/

/-- Every occurrence of `r` in `paperLayer G ℓ d τ r` is through `r ^ 2` (through `sinSq`, the
Gaussians `e^{-πr²t}` and the parameters `λ = πr²`, `μ = πr² - 2π` of the closed `highPart`), so
the layer is an even function of `r`. -/
lemma paperLayer_neg_r (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (ℓ : Work.Kernels.LogLambdaData)
    (d : ℕ) (τ : UpperHalfPlane) (r : ℝ) :
    Work.Asymptotics.paperLayer G ℓ d τ (-r) = Work.Asymptotics.paperLayer G ℓ d τ r := by
  have hsq : (((-r : ℝ)) : ℂ) ^ 2 = ((r : ℝ) : ℂ) ^ 2 := by
    rw [Complex.ofReal_neg, neg_sq]
  simp only [Work.Asymptotics.paperLayer, Work.Asymptotics.layerLow, Work.Asymptotics.layerTrunc,
    Work.Asymptotics.highPart, Work.Asymptotics.sinSq, hsq, neg_sq]

lemma sinSqC_neg (r : ℝ) : Work.Asymptotics.sinSqC (-r) = Work.Asymptotics.sinSqC r := by
  simp only [Work.Asymptotics.sinSqC]
  norm_num

lemma resCorr_neg (r : ℝ) (τ : UpperHalfPlane) :
    Work.Asymptotics.resCorr (-r) τ = Work.Asymptotics.resCorr r τ := by
  simp only [Work.Asymptotics.resCorr]
  norm_num

/-! ## Non-degeneracy of `j'` -/

/-- **`j'` does not vanish at the centre `1 + i s₀` for `s₀ ≠ 1`.**  `j'` is invariant under `T`,
so `j'(1 + i s₀) = j'(i s₀)`, and the imaginary axis point `i s₀` is not elliptic
(`Work.Asymptotics.exists_jprime_lower_near_imagAxis`). -/
theorem jprime_onePlusI_ne_zero {s₀ : ℝ} (hs₀ : 0 < s₀) (hne : s₀ ≠ 1) :
    Work.Residues.jprime (Work.Asymptotics.onePlusI s₀ hs₀) ≠ 0 := by
  obtain ⟨η, c, hη, hc, hb⟩ := Work.Asymptotics.exists_jprime_lower_near_imagAxis hs₀ hne
  have hcoe : ((Work.Kernels.imagAxis s₀ hs₀ : UpperHalfPlane) : ℂ) = Complex.I * (s₀ : ℂ) := by
    rw [Work.Kernels.imagAxis]; simp [mul_comm]
  have h2 : c ≤ ‖Work.Residues.jprime (Work.Kernels.imagAxis s₀ hs₀)‖ :=
    hb _ (by rw [hcoe]; simpa using hη)
  have hne0 : Work.Residues.jprime (Work.Kernels.imagAxis s₀ hs₀) ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h2
    linarith
  have hone : Work.Asymptotics.onePlusI s₀ hs₀ = (1 : ℝ) +ᵥ Work.Kernels.imagAxis s₀ hs₀ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd, Work.Asymptotics.onePlusI_coe, hcoe]
    push_cast
    ring
  rw [hone, Work.Residues.jprime_vadd_one]
  exact hne0

/-- **`j'` does not vanish on the far side of the height `1`.**  On `1 < Re τ` near `1 + i` the
translate `τ - 2` lies in the ball `B(-1 + i, ε)` with `-1 < Re τ - 2`, so the right-hand pole
non-degeneracy `Work.LayerCont.Right.exists_jprime_tauAddOne_ne_zero` applies to `τ - 1`, and
`j'` is invariant under `T`. -/
theorem jprime_ne_zero_far_one :
    ∃ ε : ℝ, 0 < ε ∧ ∀ τ : UpperHalfPlane,
      dist τ (Work.Asymptotics.onePlusI 1 one_pos) < ε → 1 < τ.re →
        Work.Residues.jprime τ ≠ 0 := by
  obtain ⟨ε₀, hε₀, hb⟩ := Work.LayerCont.Right.exists_jprime_tauAddOne_ne_zero 1 one_pos
  refine ⟨ε₀, hε₀, fun τ hτ hτre => ?_⟩
  have hcenter : ((-2 : ℝ) +ᵥ Work.Asymptotics.onePlusI 1 one_pos)
      = Work.LayerCont.Right.negOnePlusI 1 one_pos := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd, Work.Asymptotics.onePlusI_coe,
      Work.LayerCont.Right.negOnePlusI_coe]
    push_cast
    ring
  have hdist0 : dist ((-2 : ℝ) +ᵥ τ) (((-2 : ℝ) +ᵥ Work.Asymptotics.onePlusI 1 one_pos))
      = dist τ (Work.Asymptotics.onePlusI 1 one_pos) :=
    (UpperHalfPlane.isometry_real_vadd (-2 : ℝ)).dist_eq τ _
  have hdist : dist ((-2 : ℝ) +ᵥ τ) (Work.LayerCont.Right.negOnePlusI 1 one_pos) < ε₀ := by
    rw [← hcenter, hdist0]
    exact hτ
  have hre : (-1 : ℝ) < ((-2 : ℝ) +ᵥ τ).re := by
    rw [UpperHalfPlane.vadd_re]
    linarith
  have h := hb ((-2 : ℝ) +ᵥ τ) hdist hre
  have hcoe : Work.LayerCont.Right.tauAddOne ((-2 : ℝ) +ᵥ τ) = Work.Asymptotics.tauSubOne τ := by
    apply UpperHalfPlane.ext
    rw [Work.LayerCont.Right.tauAddOne_coe, Work.Asymptotics.tauSubOne_coe,
      UpperHalfPlane.coe_vadd]
    push_cast
    ring
  rw [hcoe, Work.Residues.jprime_vadd_neg_one] at h
  exact h

/-! ## The symmetrisation: an even chart from any chart -/

/-- **The averaging argument.**  From a chart `φ` at a height `s₀` — holomorphic on a ball,
agreeing with `paperLayer` on the `𝒟`-side and with `paperLayer + sinSqC r · resCorr r` on the far
side — the symmetrised chart `W r := (φ r + φ (-r))/2` is again a chart, and it is *even* in `r`
by construction. -/
theorem ChartClaim.of_chart {ℓ : Work.Kernels.LogLambdaData} {d : ℕ} {s₀ : ℝ} {hs₀ : 0 < s₀}
    {φ : ℝ → UpperHalfPlane → ℂ} {ε : ℝ} (hε : 0 < ε)
    (hholo : ∀ r : ℝ, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (φ r) (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) ε))
    (hnear : ∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
      τ.re < 1 → τ ∈ Work.Asymptotics.DomainD →
        φ r τ = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
    (hfar : ∀ (τ : UpperHalfPlane) (r : ℝ), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
      1 < τ.re →
        φ r τ = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
          + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ) :
    ChartClaim ℓ d s₀ hs₀ := by
  refine ⟨ε, fun r τ => (φ r τ + φ (-r) τ) / 2, hε, ?_, ?_, ?_, ?_⟩
  · intro r
    have h := ((hholo r).add (hholo (-r))).const_smul (1 / 2 : ℂ)
    convert h using 1
    ext τ
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm]
  · intro r τ hτ hD
    dsimp only
    have hre : τ.re < 1 := (Work.Asymptotics.re_bounds_of_mem_DomainD hD).2
    rw [hnear τ r hτ hre hD, hnear τ (-r) hτ hre hD, paperLayer_neg_r]
    ring
  · intro r τ hτ hτre
    dsimp only
    rw [hfar τ r hτ hτre, hfar τ (-r) hτ hτre, paperLayer_neg_r, sinSqC_neg, resCorr_neg]
    ring
  · intro r τ
    dsimp only
    rw [neg_neg, add_comm]

/-! ## The chart at the heights `s₀ ≠ 1` -/

/-- **The window chart for every height `s₀ ≠ 1`.**  Repackaging of
`Work.LayerCont.FarTail.far_identity_data` (`s₀ > 1`) and
`Work.LayerCont.FarTail.far_identity_data_rev` (`s₀ < 1`, where the centre non-degeneracy
`j'(1 + i s₀) ≠ 0` is `jprime_onePlusI_ne_zero`), followed by the symmetrisation
`ChartClaim.of_chart`. -/
theorem windowChart_data_ne_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) {s₀ : ℝ} (hs₀ : 0 < s₀) (hne : s₀ ≠ 1) :
    ChartClaim ℓ d s₀ hs₀ := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨A₁, ξ₁, A₂, ξ₂, p, hA₁, hξ₁, hA₂, hξ₂, hp1, ε', hε', hholo, hnear, hfar, -⟩ :=
      Work.LayerCont.FarTail.far_identity_data_rev ℓ d hd hs₀ hlt
        (jprime_onePlusI_ne_zero hs₀ hne)
    exact ChartClaim.of_chart hε' hholo (fun τ r hτ hre hD => hnear τ r hτ hre hD)
      (fun τ r hτ hre => hfar τ r hτ hre)
  · obtain ⟨A₁, ξ₁, A₂, ξ₂, p, hA₁, hξ₁, hA₂, hξ₂, hp1, ε', hε', hholo, hnear, hfar, -⟩ :=
      Work.LayerCont.FarTail.far_identity_data ℓ d hd hs₀ hgt
    exact ChartClaim.of_chart hε' hholo (fun τ r hτ hre hD => hnear τ r hτ hre hD)
      (fun τ r hτ hre => hfar τ r hτ hre)

/-! ## The chart at the height `1` -/

/-- **The window chart at the cusp height `1`.**  The contour data at `s₀ = 1` collapses: the pole
interval and the coincidence interval coalesce, `A₂ = ξ₂ = 0`, and the chart is the single-interval
object `layerLowOne ℓ d p 1 A₁ ξ₁` together with the clean tail and the closed form.

The far side (`1 < Re τ`) is where the pole `τ - 1` has *positive* real part, so it misses the left
rectangle, while the removable coincidence `S • (-1 +ᵥ τ)` is swept residue-free: this is
`Work.CKFinal.layerLowOne_eq_layerLowAt_far`, and the residue correction `sinSqC r · resCorr r`
built into `layerLowOne` survives.  The `𝒟`-side is the existing
`Work.LayerCont.layerLowOne_eq_layerLowAt` + `Work.LayerCont.layerAt_eq_paperLayer`. -/
theorem windowChart_data_one (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ChartClaim ℓ d 1 one_pos := by
  have h1 : (0 : ℝ) < 1 := one_pos
  obtain ⟨ε, hεpos, A₁, ξ₁, A₂, ξ₂, hA₁, hξ₁, hA₂, hξ₂, hA₁s, hξ₁1, hA₂inv, h4sεA, h4sεξ,
    hsep1, hsep2, hclean, hedge₀, hclass, hA₂bd, hξ₂bd, hA₂q, hξ₂q, hε4, hεa₁, hεa₂,
    rw₀, hrw₀pos, hεw, hweb⟩ := Work.LayerCont.ECS.exists_contour_left_data 1 h1
  obtain ⟨hA₂0, hξ₂0⟩ := hsep1 rfl
  obtain ⟨ε₁, hε₁pos, hdeg₀⟩ := Work.Asymptotics.jprime_tauSubOne_ne_zero 1 h1
  obtain ⟨εj, hεjpos, hdegFar₀⟩ := jprime_ne_zero_far_one
  -- ### the working radius (shrunk so that `16ε ≤ A₁`, `16ε ≤ ξ₁`)
  set δ : ℝ := min (min (ε / 4) (min (1 / 16) ε₁)) εj with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min (div_pos hεpos (by norm_num)) (lt_min (by norm_num) hε₁pos)) hεjpos
  have hδε4 : δ ≤ ε / 4 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ16 : δ ≤ 1 / 16 :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδε₁ : δ ≤ ε₁ :=
    le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδεj : δ ≤ εj := min_le_right _ _
  have hδε : δ ≤ ε :=
    le_trans hδε4 (by rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]; linarith [hεpos])
  have hδε1 : δ ≤ 1 := le_trans hδ16 (by norm_num)
  have hδ8 : δ ≤ 1 / 8 := le_trans hδ16 (by norm_num)
  have hδw : δ ≤ rw₀ := le_trans hδε hεw
  have h4δ : 4 * δ ≤ ε := by
    have h := mul_le_mul_of_nonneg_left hδε4 (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  have h16δA : 16 * δ ≤ A₁ := by
    have h := mul_le_mul_of_nonneg_left h4δ (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  have h16δξ : 16 * δ ≤ ξ₁ := by
    have h := mul_le_mul_of_nonneg_left h4δ (by norm_num : (0 : ℝ) ≤ 4)
    linarith
  have h4δA : 4 * 1 * δ ≤ A₁ := by linarith
  have hlo : 0 < 1 - A₁ := by linarith
  -- ### the split point
  set p : ℝ := max (1 + A₁) ((1 - A₁)⁻¹) + 1 with hpdef
  have hp1 : 1 ≤ p := by
    have h0 : (0 : ℝ) ≤ 1 + A₁ := by linarith
    have h1' : (0 : ℝ) ≤ max (1 + A₁) ((1 - A₁)⁻¹) := le_trans h0 (le_max_left _ _)
    rw [hpdef]
    linarith
  have hp_hi : 1 + A₁ ≤ p := by
    have h := le_max_left (1 + A₁) ((1 - A₁)⁻¹)
    rw [hpdef]
    linarith
  have hp_ge : max (1 + A₁) ((1 - A₁)⁻¹) + 1 ≤ p := le_of_eq hpdef.symm
  -- ### the cleanliness of the tail `[p,∞)`
  have hcleanTail : ∀ (s : ℝ) (hs : 0 < s), p ≤ s →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < δ →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) :=
    clean_axis_tail_of_web h1 hA₁s hδpos hδ16 hδw h4δA hp_ge hweb
  -- ### the cleanliness of the retained contour `(0,p] \ I₁`
  have hcleanAxisOne : ∀ (s : ℝ) (hs : 0 < s),
      s ∈ (Set.Ioc (0 : ℝ) p) \ Set.Ioo (1 - A₁) (1 + A₁) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < δ →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs) := by
    intro s hs hsE τ hτ hjeq
    obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
    have hd : dist (σ • Work.Kernels.imagAxis s hs) (Work.Asymptotics.onePlusI 1 h1) < rw₀ := by
      rw [hσ]
      exact lt_of_lt_of_le hτ hδw
    obtain ⟨hre, him⟩ := hweb σ s hs hd
    rw [hσ] at hre him
    obtain ⟨h2lo, h2hi⟩ := abs_lt.mp
      (Work.Asymptotics.abs_re_im_sub_lt h1 hδpos hδε1 hτ).2
    refine absurd ?_ hsE.2
    rcases him with him | him
    · rw [Set.mem_Ioo, ← him]
      exact ⟨by linarith, by linarith⟩
    · have hs_eq : s = τ.im⁻¹ := by rw [him, inv_inv]
      rw [Set.mem_Ioo, hs_eq]
      have hτim_pos : 0 < τ.im := τ.im_pos
      have hτim_gt : (13 : ℝ) / 16 < τ.im := by nlinarith [h2lo, hδ16]
      have hnum : |1 - τ.im| < 3 * δ := by
        rw [abs_sub_comm]
        simpa using abs_lt.mpr ⟨h2lo, h2hi⟩
      have hkey : |τ.im⁻¹ - 1| < A₁ := by
        have hdiv : τ.im⁻¹ - 1 = (1 - τ.im) / τ.im := by
          field_simp
        rw [hdiv, abs_div, abs_of_pos hτim_pos]
        rw [div_lt_iff₀ hτim_pos]
        nlinarith [hnum.le, hτim_gt, h16δA, hA₁, hτim_pos]
      obtain ⟨h1', h2'⟩ := abs_lt.mp hkey
      exact ⟨by linarith, by linarith⟩
  -- ### the edge cleanliness of the detour rectangle
  have hedge : ∀ (u v : ℝ), 0 < v →
      ((-ξ₁ < u ∧ u < 0 ∧ (v = 1 - A₁ ∨ v = 1 + A₁))
        ∨ (u = -ξ₁ ∧ 1 - A₁ < v ∧ v < 1 + A₁)) →
      ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < δ →
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Asymptotics.ofReImT u v) := by
    intro u v hv hc τ hτ hjeq
    obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hjeq
    have hge : ε ≤ dist (σ • Work.Asymptotics.ofReImT u v) (Work.Asymptotics.onePlusI 1 h1) := by
      refine hedge₀ σ u v hv ?_
      rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr (Or.inl hc)
    rw [hσ] at hge
    exact absurd (lt_of_lt_of_le hτ hδε) (not_lt.mpr hge)
  -- ### the geometry of the pole rectangle
  have hpole : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < δ →
      τ.re < 1 →
      -ξ₁ < (Work.Asymptotics.tauSubOne τ).re ∧ (Work.Asymptotics.tauSubOne τ).re < 0 ∧
        1 - A₁ < (Work.Asymptotics.tauSubOne τ).im ∧
        (Work.Asymptotics.tauSubOne τ).im < 1 + A₁ := by
    intro τ hτ hτre
    obtain ⟨h1', h2'⟩ := Work.Asymptotics.abs_re_im_sub_lt h1 hδpos hδε1 hτ
    obtain ⟨h1a, h1b⟩ := abs_lt.mp h1'
    obtain ⟨h2a, h2b⟩ := abs_lt.mp h2'
    have hre : (Work.Asymptotics.tauSubOne τ).re = τ.re - 1 := tauSubOne_re' τ
    have him : (Work.Asymptotics.tauSubOne τ).im = τ.im := tauSubOne_im' τ
    rw [hre, him]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hdeg : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < δ →
      τ.re < 1 → Work.Residues.jprime (Work.Asymptotics.tauSubOne τ) ≠ 0 :=
    fun τ hτ hτre => hdeg₀ τ (lt_of_lt_of_le hτ hδε₁) hτre
  have hcl : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < δ →
      τ.re < 1 → ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect 1 A₁ ξ₁ z →
          (z ≠ γ • τ ∨ z = Work.Asymptotics.tauSubOne τ) := by
    intro τ hτ hτre γ z hz
    by_cases h : z = γ • τ
    · right
      rcases hclass τ (lt_of_lt_of_le hτ hδε) γ z (Or.inl hz) h with h' | h'
      · exact h'
      · exfalso
        have hpos : 0 < (Work.Asymptotics.tauCoinc τ).re :=
          Work.Asymptotics.tauCoinc_re_pos τ hτre
        have hneg : z.re ≤ 0 := hz.2.1
        rw [h'] at hneg
        linarith
    · exact Or.inl h
  -- ### the far-side geometry
  have htauCoinc : ∀ τ : UpperHalfPlane,
      Work.Asymptotics.tauCoinc τ = ModularGroup.S • ((-1 : ℝ) +ᵥ τ) := by
    intro τ
    rw [Work.Asymptotics.tauCoinc, mul_smul]
    have h : ModularGroup.T⁻¹ • τ = (-1 : ℝ) +ᵥ τ := by
      simpa using UpperHalfPlane.modular_T_zpow_smul τ (-1)
    rw [h]
  have hclFar : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < δ → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect 1 A₁ ξ₁ z →
          (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ)) := by
    intro τ hτ hτre γ z hz
    by_cases h : z = γ • τ
    · right
      rcases hclass τ (lt_of_lt_of_le hτ hδε) γ z (Or.inl hz) h with h' | h'
      · exfalso
        have hzre : z.re ≤ 0 := hz.2.1
        rw [h'] at hzre
        rw [tauSubOne_re'] at hzre
        linarith
      · rw [h', htauCoinc]
    · exact Or.inl h
  have hcoincFar : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < δ →
      1 < τ.re → Work.LayerCont.Coinc.coincℂ τ ∈ Work.Asymptotics.openLeftRectℂ 1 A₁ ξ₁ := by
    intro τ hτ hτre
    have h := Work.LayerCont.FarTail.coinc_mem_openLeftRect_far (s₀ := 1) h1 hA₁ hξ₁ hδpos hδ8
      (by simpa using h16δA) (by simpa using h16δξ) τ hτ hτre
    simpa using h
  have hdegFar : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < δ →
      1 < τ.re → Work.Residues.jprime τ ≠ 0 :=
    fun τ hτ hτre => hdegFar₀ τ (lt_of_lt_of_le hτ hδεj) hτre
  have hcleanAllFar : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < δ →
      1 < τ.re → ∀ (t : ℝ) (ht : 0 < t),
        t ∈ (Set.Ioc (0 : ℝ) p) \ Set.Ioo (1 - A₁) (1 + A₁) →
          Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
    intro τ hτ hτre t ht htE
    refine hclean t ht htE.2 ?_ τ (lt_of_lt_of_le hτ hδε)
    rw [inv_one, hA₂0, sub_zero, add_zero]
    exact fun hmem => absurd hmem (by simp)
  have hfarClean : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI 1 h1) < δ →
      1 < τ.re → ∀ (t : ℝ) (ht : 0 < t),
        Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) :=
    Work.LayerCont.FarTail.farClean_of_web h1 hδw hweb
  -- ### the chart
  refine ChartClaim.of_chart (φ := fun r τ =>
      layerLowOne ℓ d p 1 A₁ ξ₁ r τ + layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
        + highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ) hδpos ?_ ?_ ?_
  · intro r
    have h1' : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => layerLowOne ℓ d p 1 A₁ ξ₁ r τ)
        (Metric.ball (Work.Asymptotics.onePlusI 1 h1) δ) :=
      mdifferentiableOn_layerLowOne ℓ d hd (r := r) h1 hA₁ hξ₁ hδpos hlo hp_hi hedge
        (fun s hs hsE τ hτ' => hcleanAxisOne s hs hsE τ hτ')
    have h2 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => layerTruncAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ)
        (Metric.ball (Work.Asymptotics.onePlusI 1 h1) δ) :=
      mdifferentiableOn_layerTruncAt ℓ d hd (p := p) hp1 h1 hδpos r hcleanTail
    have h3 : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : UpperHalfPlane => highPartAt (Work.Asymptotics.Gcusp ℓ d) p r τ)
        (Metric.ball (Work.Asymptotics.onePlusI 1 h1) δ) :=
      (mdifferentiableOn_highPartAt ℓ d hd p r).mono (Set.subset_univ _)
    exact (h1'.add h2).add h3
  · intro τ r hτ hτre hD
    have hconv : layerLowOne ℓ d p 1 A₁ ξ₁ r τ = layerLowAt ℓ d p r τ :=
      layerLowOne_eq_layerLowAt ℓ d hd (r := r) h1 hA₁ hξ₁ hδpos hlo hp_hi hcl hpole hdeg
        (fun s hs hsE τ' hτ' _ => hcleanAxisOne s hs hsE τ' hτ') τ r hτ hτre
    have hpaper : layerAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
        = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r :=
      layerAt_eq_paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d hd (r := r) hp1 τ
        (fun t ht _ => clean_axis_of_web_re_lt_one (ε := ε) h1 hεw hweb t ht τ
          (lt_of_lt_of_le hτ hδε) hτre)
        (Work.LayerCont.FarTail.tail_integrableOn_of_mem_DomainD ℓ d hd hD r)
    rw [hconv]
    exact hpaper
  · intro τ r hτ hτre
    have hconv : layerLowOne ℓ d p 1 A₁ ξ₁ r τ
        = layerLowAt ℓ d p r τ + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ :=
      Work.CKFinal.layerLowOne_eq_layerLowAt_far ℓ d hd hA₁ hξ₁ hδpos hlo hp_hi hclFar hcoincFar
        hdegFar hcleanAllFar τ hτ hτre
    have hpaper : layerAt (Work.Asymptotics.Gcusp ℓ d) ℓ d p r τ
        = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r :=
      layerAt_eq_paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d hd (r := r) hp1 τ
        (fun t ht _ => hfarClean τ hτ hτre t ht)
        (Work.LayerCont.FarTail.tail_integrableOn_of_clean ℓ d hd
          (fun t ht => hfarClean τ hτ hτre t ht))
    rw [hconv, ← hpaper]
    simp only [layerAt]
    ring

/-- The window chart of the layer at every height of the line `Re τ = 1` (including `s₀ = 1`):
holomorphic on a ball for every `r`, equal to `paperLayer` on the `𝒟`-side, equal to
`paperLayer + sinSqC r * resCorr r` on the far side `Re τ > 1`, and even in `r`. -/
theorem windowChart_data (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (s₀ : ℝ) (hs₀ : 0 < s₀) :
    ∃ (ε : ℝ) (W : ℝ → UpperHalfPlane → ℂ), 0 < ε ∧
      (∀ r : ℝ, MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (W r)
        (Metric.ball (Work.Asymptotics.onePlusI s₀ hs₀) ε)) ∧
      (∀ (r : ℝ) (τ : UpperHalfPlane), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
        τ ∈ Work.Asymptotics.DomainD →
          W r τ = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) ∧
      (∀ (r : ℝ) (τ : UpperHalfPlane), dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
        1 < τ.re →
          W r τ = Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
            + Work.Asymptotics.sinSqC r * Work.Asymptotics.resCorr r τ) ∧
      (∀ (r : ℝ) (τ : UpperHalfPlane), W (-r) τ = W r τ) := by
  rcases eq_or_ne s₀ 1 with rfl | hne
  · exact windowChart_data_one ℓ d hd
  · exact windowChart_data_ne_one ℓ d hd hs₀ hne

end Work.CKFinal
