import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Have
import Submission.Work.FTS.CoercivityFix.Basic
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dth
import Submission.Work.FTS.CoercivityFix.Assembly.RegQAux
import Submission.Work.FTS.CoercivityFix.E2Bound.E2hat_HkIntegrand_le_uniform
import Submission.Work.FTS.CoercivityFix.Assembly.HkMemAe

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The `RegQ`-closure under the `D_z`-commutator defect `Ê₂`

`Work.FTS.CoercivityFix.E2hat f = (2zf + 3z·D_θf)/(1+z)²` is the `D_z`-commutator defect of the
clean operator `Lhat = 𝓛 − Transport` (`D_z (Lhat f) = Lhat (D_z f) + Ê₂ f`), and the modified
induction of the coercivity node runs on the interior class `RegQ` (`Work.FTS.Vocab`):

  `RegQ α k f = SmoothQuad f ∧ HkMem α k f ∧ BdryTraces α k f`.

This module proves the port

  `RegQ α (n+1) f → RegQ α n (Ê₂ f)`,

the `hregE2` slot of `Work.FTS.CoercivityFix.StepCoer.step_coer`.

The defect is a *radial multiplier* times a linear combination of `f` and `D_θf`:

  `Ê₂ f = φ(z)·(2f + 3·D_θf) = 2·(φ·f) + 3·(φ·D_θf)`,   `φ(z) = z/(1+z)²`.

Every `Zop`-iterate of `φ` (`Zop u = z ∂_z u`) is bounded on `(0,∞)` (`E2Bound.zop_phi_bound`:
under the Möbius chart `z ↦ (z-1)/(z+1)`, `φ` becomes a polynomial in the chart variable, which
maps `(0,∞)` into `(-1,1)`), so the multiplier `φ` preserves the three components of the class:

* `SmoothQuad` — `φ` is `C^∞` on `(-1,∞)` (`E2Bound.contDiffOn_zDiv`) and `SmoothQuad` is closed
  under products (`LocData.smoothQuad_mul`);
* `HkMem` — the Leibniz slots of `HkIntegrand α n (φ·g)` are the slots of `HkIntegrand α n g`
  with coefficients bounded by `C(n)(1+K)²` (`E2Bound.HkIntegrand_zmul_le`), which is exactly a
  pointwise *majorant* on the open quadrant; the null set `{θ = 0} ∪ {θ = π/2} ∪ {z = 0}` is
  handled by the a.e. membership criterion `EllipticEst.HkMem_of_majorant_ae`;
* `BdryTraces` — the mixed derivatives expand by the `z`-only Leibniz rule
  `E2Bound.mixed_zmul`,
  `mixed b a (φ·g) = Σ_{c≤b} C(b,c)·(Zop^c φ)·mixed (b-c) a g`, so the boundary limits of the
  product are finite combinations of those of `g`, squeezed by the boundedness of the multiplier
  (`tendsto_wsum_sq_le`, `tendsto_ssum_sq_le` below).

The three pieces assemble through the `RegQ`-algebra of `Work.FTS.Apriori.RegQApi`
(`regQ_add`, `regQ_smul`, `regQ_mono`) together with the `D_θ`-port
`QuadPorts.RegQ_dth`.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/

namespace Work.FTS.CoercivityFix.Assembly

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-! ## The radial multiplier `φ(z) = z/(1+z)²` -/

/-- The radial profile `φ(z) = z/(1+z)²` of the `D_z`-commutator defect is `C^∞` on `(-1,∞)`. -/
private theorem contDiffOn_phiZ : ContDiffOn ℝ Work.Stability.smoothOrder
    (fun z : ℝ => z / (1 + z) ^ 2) (Set.Ioi (-1)) :=
  Work.FTS.CoercivityFix.E2Bound.contDiffOn_zDiv

/-- The `z`-only factor `φ(z) = z/(1+z)²` is `SmoothQuad` as a function of `(z,θ)`. -/
private theorem smoothQuad_phiZ : Work.FTS.LocData.SmoothQuad (fun z _ : ℝ => z / (1 + z) ^ 2) :=
  Work.FTS.CoercivityFix.E2Bound.smoothQuad_of_zOnly contDiffOn_phiZ

/-! ## The two squeezing lemmas for the boundary traces of a finite sum

Both have the same shape: a finite combination `Σ_c co_c·(ψ_c·m_c)` of terms whose *weighted
squares* tend to `0` (the traces of the summands), with multipliers `ψ_c` bounded by `K`, has
weighted square tending to `0` as well.  The weights `z·w(z)²` and `sin(2θ)^{1-γ}` are
nonnegative on the relevant sets, so the Cauchy–Schwarz inequality
`(Σ_c x_c)² ≤ card · Σ_c x_c²` applies verbatim. -/

/-- The `z`-limits of the boundary traces transfer to a finite combination with bounded
`z`-dependent multipliers. -/
private theorem tendsto_wsum_sq_le {ι : Type*} {l : Filter ℝ} (hl : ∀ᶠ z in l, 0 < z)
    (s : Finset ι) (co : ι → ℝ) {ψ m : ι → ℝ → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hψ : ∀ c ∈ s, ∀ z, 0 < z → |ψ c z| ≤ K)
    (hm : ∀ c ∈ s, Tendsto (fun z => z * (m c z * Work.Spaces.w z) ^ 2) l (𝓝 0)) :
    Tendsto (fun z => z * ((∑ c ∈ s, co c * (ψ c z * m c z)) * Work.Spaces.w z) ^ 2)
      l (𝓝 0) := by
  have hlim : Tendsto (fun z => (s.card : ℝ) *
      ∑ c ∈ s, (co c) ^ 2 * K ^ 2 * (z * (m c z * Work.Spaces.w z) ^ 2)) l (𝓝 0) := by
    have h1 := tendsto_finsetSum s
      (fun c hc => (hm c hc).const_mul ((co c) ^ 2 * K ^ 2))
    have h2 := h1.const_mul ((s.card : ℝ))
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [hl] with z hz
    exact mul_nonneg hz.le (sq_nonneg _)
  · filter_upwards [hl] with z hz
    have hterm : ∀ c ∈ s, (co c * (ψ c z * m c z)) ^ 2 ≤ (co c) ^ 2 * K ^ 2 * (m c z) ^ 2 := by
      intro c hc
      have hψ2 : (ψ c z) ^ 2 ≤ K ^ 2 :=
        sq_le_sq' (abs_le.mp (hψ c hc z hz)).1 (abs_le.mp (hψ c hc z hz)).2
      calc (co c * (ψ c z * m c z)) ^ 2
          = (co c) ^ 2 * (ψ c z) ^ 2 * (m c z) ^ 2 := by ring
        _ ≤ (co c) ^ 2 * K ^ 2 * (m c z) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hψ2 (sq_nonneg (co c))) (sq_nonneg (m c z))
    have hsum : ∑ c ∈ s, (co c * (ψ c z * m c z)) ^ 2
        ≤ ∑ c ∈ s, (co c) ^ 2 * K ^ 2 * (m c z) ^ 2 := Finset.sum_le_sum hterm
    have hcard : (s.card : ℝ) * ∑ c ∈ s, (co c * (ψ c z * m c z)) ^ 2
        ≤ (s.card : ℝ) * ∑ c ∈ s, (co c) ^ 2 * K ^ 2 * (m c z) ^ 2 :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    have hcs : (∑ c ∈ s, co c * (ψ c z * m c z)) ^ 2
        ≤ (s.card : ℝ) * ∑ c ∈ s, (co c) ^ 2 * K ^ 2 * (m c z) ^ 2 :=
      le_trans sq_sum_le_card_mul_sum_sq hcard
    calc z * ((∑ c ∈ s, co c * (ψ c z * m c z)) * Work.Spaces.w z) ^ 2
        = z * Work.Spaces.w z ^ 2 * (∑ c ∈ s, co c * (ψ c z * m c z)) ^ 2 := by ring
      _ ≤ z * Work.Spaces.w z ^ 2 *
            ((s.card : ℝ) * ∑ c ∈ s, (co c) ^ 2 * K ^ 2 * (m c z) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (mul_nonneg hz.le (sq_nonneg _))
      _ = (s.card : ℝ) *
            ∑ c ∈ s, (co c) ^ 2 * K ^ 2 * (z * (m c z * Work.Spaces.w z) ^ 2) := by
          have hA : ∀ c : ι, (co c) ^ 2 * K ^ 2 * (z * (m c z * Work.Spaces.w z) ^ 2)
              = z * Work.Spaces.w z ^ 2 * ((co c) ^ 2 * K ^ 2 * (m c z) ^ 2) :=
            fun c => by ring
          simp only [hA]
          rw [← Finset.mul_sum]
          ring

/-- The angular limits of the boundary traces transfer to a finite combination with bounded
(`θ`-independent) multipliers. -/
private theorem tendsto_ssum_sq_le {ι : Type*} (α : ℝ) {l : Filter ℝ}
    (hl : ∀ᶠ θ in l, θ ∈ Set.Ioo (0 : ℝ) (π / 2))
    (s : Finset ι) (co : ι → ℝ) (ψ : ι → ℝ) (m : ι → ℝ → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hψ : ∀ c ∈ s, |ψ c| ≤ K)
    (hm : ∀ c ∈ s,
      Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (m c θ) ^ 2) l (𝓝 0)) :
    Tendsto (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
      (∑ c ∈ s, co c * (ψ c * m c θ)) ^ 2) l (𝓝 0) := by
  have hlim : Tendsto (fun θ => (s.card : ℝ) *
      ∑ c ∈ s, (co c) ^ 2 * K ^ 2 *
        (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (m c θ) ^ 2)) l (𝓝 0) := by
    have h1 := tendsto_finsetSum s
      (fun c hc => (hm c hc).const_mul ((co c) ^ 2 * K ^ 2))
    have h2 := h1.const_mul ((s.card : ℝ))
    simpa using h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [hl] with θ hθ
    have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _
    exact mul_nonneg hsin (sq_nonneg _)
  · filter_upwards [hl] with θ hθ
    have hsin : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩) _
    have hterm : ∀ c ∈ s,
        (co c * (ψ c * m c θ)) ^ 2 ≤ (co c) ^ 2 * K ^ 2 * (m c θ) ^ 2 := by
      intro c hc
      have hψ2 : ψ c ^ 2 ≤ K ^ 2 :=
        sq_le_sq' (abs_le.mp (hψ c hc)).1 (abs_le.mp (hψ c hc)).2
      calc (co c * (ψ c * m c θ)) ^ 2 = (co c) ^ 2 * ψ c ^ 2 * (m c θ) ^ 2 := by ring
        _ ≤ (co c) ^ 2 * K ^ 2 * (m c θ) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hψ2 (sq_nonneg (co c))) (sq_nonneg (m c θ))
    have hsum : ∑ c ∈ s, (co c * (ψ c * m c θ)) ^ 2
        ≤ ∑ c ∈ s, (co c) ^ 2 * K ^ 2 * (m c θ) ^ 2 := Finset.sum_le_sum hterm
    have hcard : (s.card : ℝ) * ∑ c ∈ s, (co c * (ψ c * m c θ)) ^ 2
        ≤ (s.card : ℝ) * ∑ c ∈ s, (co c) ^ 2 * K ^ 2 * (m c θ) ^ 2 :=
      mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    have hcs : (∑ c ∈ s, co c * (ψ c * m c θ)) ^ 2
        ≤ (s.card : ℝ) * ∑ c ∈ s, (co c) ^ 2 * K ^ 2 * (m c θ) ^ 2 :=
      le_trans sq_sum_le_card_mul_sum_sq hcard
    calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
          (∑ c ∈ s, co c * (ψ c * m c θ)) ^ 2
        ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
            ((s.card : ℝ) * ∑ c ∈ s, (co c) ^ 2 * K ^ 2 * (m c θ) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs hsin
      _ = (s.card : ℝ) * ∑ c ∈ s, (co c) ^ 2 * K ^ 2 *
            (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (m c θ) ^ 2) := by
          have hA : ∀ c : ι, (co c) ^ 2 * K ^ 2 *
                (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (m c θ) ^ 2)
              = Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
                ((co c) ^ 2 * K ^ 2 * (m c θ) ^ 2) := fun c => by ring
          simp only [hA]
          rw [← Finset.mul_sum]
          ring

/-! ## `HkMem` is preserved by the multiplier `φ` -/

/-- **The `ℋⁿ`-membership is preserved by the radial multiplier `φ(z) = z/(1+z)²`.**
`E2Bound.HkIntegrand_zmul_le` dominates the integrand of the product pointwise on the open
quadrant by `C(1+K)²` times the integrand of `g`; the (null) complement of the open quadrant
inside `Iz × Iθ` is handled by the a.e. criterion `EllipticEst.HkMem_of_majorant_ae`. -/
private theorem HkMem_phiZ_mul {α : ℝ} {n : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.LocData.SmoothQuad g) (hm : Work.Spaces.HkMem α n g) :
    Work.Spaces.HkMem α n (fun z θ => (z / (1 + z) ^ 2) * g z θ) := by
  obtain ⟨C, _hCpos, hC⟩ := Work.FTS.CoercivityFix.E2Bound.HkIntegrand_zmul_le α n
  obtain ⟨K, hK0, hKb⟩ := Work.FTS.CoercivityFix.E2Bound.zop_phi_bound n
  refine HkMem_of_majorant_ae α n
    (f := fun z θ => (z / (1 + z) ^ 2) * g z θ)
    (M := fun z θ => C * (1 + K) ^ 2 * Work.Spaces.HkIntegrand α n g z θ) ?_ ?_ ?_ ?_
  · show ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α n
      (fun z θ => (z / (1 + z) ^ 2) * g z θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
    exact Work.FTS.LocData.continuousOn_HkIntegrand_smoothQuad α n _
      (Work.FTS.LocData.smoothQuad_mul smoothQuad_phiZ hg)
  · intro z hz
    exact (hm.1 z hz).const_mul (C * (1 + K) ^ 2)
  · have hfun : (fun z => ∫ θ in Work.Spaces.Iθ, C * (1 + K) ^ 2 *
          Work.Spaces.HkIntegrand α n g z θ)
        = fun z => C * (1 + K) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α n g z θ) := by
      funext z
      exact MeasureTheory.integral_const_mul _ _
    rw [hfun]
    exact hm.2.const_mul _
  · intro z hz
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall (fun θ hθ => ?_)
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with h0 | hz0
    · subst h0
      rw [Work.FTS.LocData.HkIntegrand_zero_fst α n (fun z θ => (z / (1 + z) ^ 2) * g z θ) θ,
        Work.FTS.LocData.HkIntegrand_zero_fst α n g θ]
      have h1 : 0 ≤ C * (1 + K) ^ 2 := by positivity
      simpa using mul_nonneg h1 (le_refl (0 : ℝ))
    · exact hC (fun z : ℝ => z / (1 + z) ^ 2) K hK0 hKb smoothQuad_phiZ g hg z hz0 θ hθ

/-! ## `BdryTraces` is preserved by the multiplier `φ` -/

/-- **The boundary traces are preserved by the radial multiplier `φ(z) = z/(1+z)²`.**
On the open quadrant the mixed derivatives expand by `E2Bound.mixed_zmul` into
`Σ_{c≤b} C(b,c)·(Zop^c φ)(z)·mixed (b-c) a g`, all of whose trace pairs are those of `g` at
levels `≤ n`; the squeezing lemmas above convert the limits of the summands into the limit of
the sum. -/
private theorem bdryTraces_phiZ_mul {α : ℝ} {n : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.LocData.SmoothQuad g) (htr : Work.FTS.Nonlin.BdryTraces α n g) :
    Work.FTS.Nonlin.BdryTraces α n (fun z θ => (z / (1 + z) ^ 2) * g z θ) := by
  obtain ⟨K, hK0, hKb⟩ := Work.FTS.CoercivityFix.E2Bound.zop_phi_bound n
  intro a b hab
  -- the interior Leibniz expansion of the mixed derivative of the product
  have hexp : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      Work.Spaces.mixed b a (fun z θ => (z / (1 + z) ^ 2) * g z θ) z θ
        = ∑ c ∈ Finset.range (b + 1), (b.choose c : ℝ) *
            (Work.Spaces.Zop^[c] (fun z : ℝ => z / (1 + z) ^ 2) z *
              Work.Spaces.mixed (b - c) a g z θ) :=
    fun z hz θ hθ => Work.FTS.CoercivityFix.E2Bound.mixed_zmul b a
      (fun z : ℝ => z / (1 + z) ^ 2) g
      (Set.mem_Ioi.mpr (by have := Set.mem_Ioi.mp hz; linarith)) hθ
      smoothQuad_phiZ hg
  -- the index `c` of the expansion stays within the range of the hypothesis
  have hcn : ∀ c ∈ Finset.range (b + 1), c ≤ n := by
    intro c hc
    have := Finset.mem_range.mp hc
    omega
  have hlev : ∀ c ∈ Finset.range (b + 1), a + (b - c) ≤ n := by
    intro c hc
    have := Finset.mem_range.mp hc
    omega
  constructor
  · intro θ hθ
    constructor
    · -- `z → 0⁺`
      have hm : ∀ c ∈ Finset.range (b + 1), Tendsto (fun z =>
          z * (Work.Spaces.mixed (b - c) a g z θ * Work.Spaces.w z) ^ 2) (𝓝[>] 0) (𝓝 0) :=
        fun c hc => ((htr a (b - c) (hlev c hc)).1 θ hθ).1
      have hcongr : (fun z => z * ((∑ c ∈ Finset.range (b + 1), (b.choose c : ℝ) *
            (Work.Spaces.Zop^[c] (fun z : ℝ => z / (1 + z) ^ 2) z *
              Work.Spaces.mixed (b - c) a g z θ)) * Work.Spaces.w z) ^ 2)
          =ᶠ[𝓝[>] (0 : ℝ)] (fun z => z * (Work.Spaces.mixed b a
            (fun z θ => (z / (1 + z) ^ 2) * g z θ) z θ * Work.Spaces.w z) ^ 2) := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        rw [hexp z (Set.mem_Ioi.mp hz) θ hθ]
      exact (tendsto_wsum_sq_le self_mem_nhdsWithin (Finset.range (b + 1))
        (fun c => (b.choose c : ℝ)) hK0
        (fun c hc z hz => hKb c (hcn c hc) z hz) hm).congr' hcongr
    · -- `z → ∞`
      have hm : ∀ c ∈ Finset.range (b + 1), Tendsto (fun z =>
          z * (Work.Spaces.mixed (b - c) a g z θ * Work.Spaces.w z) ^ 2) atTop (𝓝 0) :=
        fun c hc => ((htr a (b - c) (hlev c hc)).1 θ hθ).2
      have hcongr : (fun z => z * ((∑ c ∈ Finset.range (b + 1), (b.choose c : ℝ) *
            (Work.Spaces.Zop^[c] (fun z : ℝ => z / (1 + z) ^ 2) z *
              Work.Spaces.mixed (b - c) a g z θ)) * Work.Spaces.w z) ^ 2)
          =ᶠ[atTop] (fun z => z * (Work.Spaces.mixed b a
            (fun z θ => (z / (1 + z) ^ 2) * g z θ) z θ * Work.Spaces.w z) ^ 2) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        rw [hexp z (Set.mem_Ioi.mpr hz) θ hθ]
      exact (tendsto_wsum_sq_le (eventually_gt_atTop (0 : ℝ)) (Finset.range (b + 1))
        (fun c => (b.choose c : ℝ)) hK0
        (fun c hc z hz => hKb c (hcn c hc) z hz) hm).congr' hcongr
  · intro z hz
    constructor
    · -- `θ → 0⁺`
      have hm : ∀ c ∈ Finset.range (b + 1), Tendsto (fun θ =>
          Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
            (Work.Spaces.mixed (b - c) a g z θ) ^ 2) (𝓝[>] 0) (𝓝 0) :=
        fun c hc => ((htr a (b - c) (hlev c hc)).2 z hz).1
      have hcongr : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
            (∑ c ∈ Finset.range (b + 1), (b.choose c : ℝ) *
              (Work.Spaces.Zop^[c] (fun z : ℝ => z / (1 + z) ^ 2) z *
                Work.Spaces.mixed (b - c) a g z θ)) ^ 2)
          =ᶠ[𝓝[>] (0 : ℝ)] (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
            (Work.Spaces.mixed b a (fun z θ => (z / (1 + z) ^ 2) * g z θ) z θ) ^ 2) := by
        filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by linarith [Real.pi_pos])]
          with θ hθ
        rw [hexp z hz θ hθ]
      exact (tendsto_ssum_sq_le α
        (Ioo_mem_nhdsGT (show (0 : ℝ) < π / 2 by linarith [Real.pi_pos]))
        (Finset.range (b + 1)) (fun c => (b.choose c : ℝ))
        (fun c => Work.Spaces.Zop^[c] (fun z : ℝ => z / (1 + z) ^ 2) z)
        (fun c θ => Work.Spaces.mixed (b - c) a g z θ) hK0
        (fun c hc => hKb c (hcn c hc) z hz) hm).congr' hcongr
    · -- `θ → π/2⁻`
      have hm : ∀ c ∈ Finset.range (b + 1), Tendsto (fun θ =>
          Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
            (Work.Spaces.mixed (b - c) a g z θ) ^ 2) (𝓝[<] (π / 2)) (𝓝 0) :=
        fun c hc => ((htr a (b - c) (hlev c hc)).2 z hz).2
      have hcongr : (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
            (∑ c ∈ Finset.range (b + 1), (b.choose c : ℝ) *
              (Work.Spaces.Zop^[c] (fun z : ℝ => z / (1 + z) ^ 2) z *
                Work.Spaces.mixed (b - c) a g z θ)) ^ 2)
          =ᶠ[𝓝[<] (π / 2)] (fun θ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) *
            (Work.Spaces.mixed b a (fun z θ => (z / (1 + z) ^ 2) * g z θ) z θ) ^ 2) := by
        filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < π / 2 by linarith [Real.pi_pos])]
          with θ hθ
        rw [hexp z hz θ hθ]
      exact (tendsto_ssum_sq_le α
        (Ioo_mem_nhdsLT (show (0 : ℝ) < π / 2 by linarith [Real.pi_pos]))
        (Finset.range (b + 1)) (fun c => (b.choose c : ℝ))
        (fun c => Work.Spaces.Zop^[c] (fun z : ℝ => z / (1 + z) ^ 2) z)
        (fun c θ => Work.Spaces.mixed (b - c) a g z θ) hK0
        (fun c hc => hKb c (hcn c hc) z hz) hm).congr' hcongr

/-! ## The class `RegQ` is closed under the multiplier `φ` -/

/-- **`RegQ α n` is closed under multiplication by the radial multiplier `φ(z) = z/(1+z)²`.** -/
private theorem regQ_phiZ_mul {α : ℝ} {n : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.Nonlin.RegQ α n g) :
    Work.FTS.Nonlin.RegQ α n (fun z θ => (z / (1 + z) ^ 2) * g z θ) :=
  ⟨Work.FTS.LocData.smoothQuad_mul smoothQuad_phiZ hg.1,
    HkMem_phiZ_mul hg.1 hg.2.1,
    bdryTraces_phiZ_mul hg.1 hg.2.2⟩

theorem E2hat_RegQ (α : ℝ) (hα : 0 < α) {n : ℕ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α (n + 1) f) :
    Work.FTS.Nonlin.RegQ α n (Work.FTS.CoercivityFix.E2hat f) := by
  -- the lower-order datum and its angular derivative
  have hf' : Work.FTS.Nonlin.RegQ α n f :=
    regQ_mono (Nat.le_succ n) hf
  have hd' : Work.FTS.Nonlin.RegQ α n (Work.Spaces.Dth f) :=
    Work.FTS.CoercivityFix.QuadPorts.RegQ_dth α hα hf
  -- the two products with the radial multiplier
  have hA := regQ_phiZ_mul hf'
  have hB := regQ_phiZ_mul hd'
  -- the linear combination `Ê₂ f = 2·(φ·f) + 3·(φ·D_θf)`
  have hsum := regQ_add (regQ_smul 2 hA)
    (regQ_smul 3 hB)
  rw [Work.FTS.CoercivityFix.E2Bound.E2hat_eq_zmul f]
  exact hsum

end Work.FTS.CoercivityFix.Assembly
