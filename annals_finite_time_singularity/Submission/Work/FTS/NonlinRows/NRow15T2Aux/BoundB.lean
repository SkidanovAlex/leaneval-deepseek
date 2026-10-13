/-
# Row 15: the pointwise `ℋ⁴`-bounds for `N₂^{ss}`

This module proves the two pointwise hypotheses of `wtoHQ_of_pointwise_open` for the
open-quadrant representative `N2ssO α Φs = ψ(z)·(2·C15 α θ)·G15 α Φs z θ` of
`N₂^{ss}(α, Φ_*)`:

* `|(1+z)·w(z)·z^m·∂_z^m N₂^{ss}(z,θ)| ≤ 200000·W`,
* `|(1+z)·w(z)·z^l·∂_z^l D_θ^i N₂^{ss}(z,θ)| ≤ 200000·W·(α+sin2θ)·sin(2θ)^{α/5}`  (`i ≥ 1`),

with `W = KW15·α·|G15|_{𝒲^{4,∞}}`.

The route is the factorization of row 15 on the open quadrant,

  `N₂^{ss}(z,θ) = ψ(z)·A(θ)·G(z,θ)`,   `ψ(z) = z²/(1+z)³`,  `A(θ) = 2·C15 α θ`,
  `G(z,θ) = ((z+1)/z)·(𝒰(Φ̃_*)(z,θ)/sin 2θ) = G15 α Φs z θ`

(`N2ss_open_eq`), the Leibniz inequality `sqm_pz_DthIter_mul_le_4_open`, the jet bound
`pzIter_psi15_le` of the radial factor `ψ`, the angular jet bounds of `A = 2·C15` and the two
`𝒲^{4,∞}`-bounds of `G` (`pz_sup_bound`, `pz_Dth_sup_bound`).

The two facts about the `θ`-only factor that make the bookkeeping work are: its `z`-jets
vanish (so that the `D_z^c`-sum of Leibniz collapses to `c = 0`), and its angular jets carry
either a *flat* bound `|D_θ^a A| ≤ K α²` — used when at least one angular derivative falls on
`G`, whose `𝒲^{4,∞}`-bound then supplies the weight `(α+sin2θ)sin(2θ)^{α/5}` — or the
*weighted* bound `|D_θ^a A| ≤ K α (α+sin2θ)sin(2θ)^{α/5}` — used when all angular
derivatives fall on `A` (there `G` is bounded only by its `𝒲^{4,∞}`-norm).  The weighted bound
is `dthU_Gam_le` (`|D_θ^mΓ| ≤ α·tBound·Γ`) combined with `Gam_mul_weight_le`
(`α Γ sin(2θ)^{-α/5}/(α+sin2θ) ≤ 1`).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.NonlinRows.NRow15T2Aux.BoundA
import Submission.Work.FTS.NonlinRows.NRow15T2Aux.Jets
import Submission.Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open
import Submission.Work.FTS.NonlinRows.wtoHQ_of_pointwise_open
import Submission.Work.FTS.NonlinRows.NRow10aux.hkmem_of_majorant
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.Spaces.WlInf_terms
import Submission.Work.FTS.H2.STBounds
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.row15_defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 3200000

theorem pzIter_AG_le {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hGs : Work.FTS.EllipticEst.SmoothOpen (G15 α Φs))
    (hGm : Work.Spaces.WlInfMem α 4 (G15 α Φs)) :
    ∀ (k : ℕ), k ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pzIter k (AG15 α Φs) z θ|
        ≤ KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k := by
  have hBnn : 0 ≤ Work.Spaces.WlInf α 4 (G15 α Φs) := Work.FTS.H2.WlInf_nonneg hGm
  have hAs : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 2 * C15 α θ) :=
    smoothOpen_A15' α
  intro k hk z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have hleib := sqm_pz_DthIter_mul_le_4_open k 0 hk (by norm_num)
    (fun z θ : ℝ => 2 * C15 α θ) (G15 α Φs) hAs hGs z hz θ hθ
  refine le_trans hleib ?_
  have hbase : (0 : ℝ) ≤ KA15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k :=
    div_nonneg (mul_nonneg (mul_nonneg KA15_pos.le (sq_nonneg α)) hBnn) (pow_pos hz1 k).le
  have hterm : ∀ c ∈ Finset.range (k + 1), ∀ a ∈ Finset.range (0 + 1),
      |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => 2 * C15 α θ)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (0 - a) (G15 α Φs)) z θ|
        ≤ KA15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k := by
    intro c hc a ha
    have ha0 : a = 0 := by
      have h' := Finset.mem_range.mp ha
      omega
    subst ha0
    by_cases hc0 : c = 0
    · subst hc0
      have hA := KA15_bd α hα hα1 0 (by norm_num) θ hθI
      simp only [Function.iterate_zero, id_eq] at hA
      have hG := Work.Spaces.pz_sup_bound α 4 (G15 α Φs) hGm k (by omega) z θ
        (le_of_lt hz) hθI
      have h0 : (0 : ℝ) ≤ KA15 * α ^ 2 := mul_nonneg KA15_pos.le (sq_nonneg α)
      calc |(2 : ℝ) * C15 α θ| * |Work.Spaces.pzIter k (G15 α Φs) z θ|
          ≤ (KA15 * α ^ 2) * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k) :=
            mul_le_mul hA hG (abs_nonneg _) h0
        _ = KA15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k := by
            rw [div_eq_mul_inv]; ring_nf
    · have hpz : Work.Spaces.pzIter c (Work.Spaces.DthIter 0 (fun z θ : ℝ => 2 * C15 α θ))
          z θ = 0 := by
        rw [Work.Spaces.DthIter_zero,
          pzIter_thetaFn_apply (fun θ : ℝ => 2 * C15 α θ) c z θ, if_neg hc0]
      rw [hpz]
      simp only [abs_zero, zero_mul]
      exact hbase
  have hS : (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (0 + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => 2 * C15 α θ)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (0 - a) (G15 α Φs)) z θ|)
      ≤ (((k + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ)
          * (KA15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k) :=
    le_trans (Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => hterm c hc a ha)
      (sum_range_range_const k 0 _)
  have hA5 : (((k + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ) ≤ 5 := by
    have h2 : k + 1 ≤ 5 := by omega
    have h3 : (((k + 1 : ℕ)) : ℝ) ≤ 5 := by exact_mod_cast h2
    have h4 : (((0 + 1 : ℕ)) : ℝ) = 1 := by norm_num
    rw [h4, mul_one]
    exact h3
  calc (257 : ℝ) * (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (0 + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => 2 * C15 α θ)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (0 - a) (G15 α Φs)) z θ|)
      ≤ 257 * ((((k + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ)
          * (KA15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k)) :=
        mul_le_mul_of_nonneg_left hS (by norm_num)
    _ = (257 * ((((k + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ)))
          * (KA15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k) := by
        rw [div_eq_mul_inv]; ring_nf
    _ ≤ (257 * 5) * (KA15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA5 (by norm_num)) hbase
    _ = KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k := by
        rw [KAG15]; rw [div_eq_mul_inv]; ring_nf

theorem pzIter_DthIter_AG_le {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hGs : Work.FTS.EllipticEst.SmoothOpen (G15 α Φs))
    (hGm : Work.Spaces.WlInfMem α 4 (G15 α Φs)) :
    ∀ (j k : ℕ), 1 ≤ j → k + j ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      |Work.Spaces.pzIter k (Work.Spaces.DthIter j (AG15 α Φs)) z θ|
        ≤ KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k := by
  have hBnn : 0 ≤ Work.Spaces.WlInf α 4 (G15 α Φs) := Work.FTS.H2.WlInf_nonneg hGm
  have hAs : Work.FTS.EllipticEst.SmoothOpen (fun z θ : ℝ => 2 * C15 α θ) :=
    smoothOpen_A15' α
  have hC1 : (0 : ℝ) ≤ KA15 + KB15 + 1 := by linarith [KA15_pos, KB15_pos]
  intro j k hj hjk z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have hk4 : k ≤ 4 := by omega
  have hj4 : j ≤ 4 := by omega
  have hsin2 : 0 ≤ Real.sin (2 * θ) := by
    have hs0 : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθI.1, by linarith [hθI.2, Real.pi_pos]⟩
    have hc0 : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθI.1, Real.pi_pos], hθI.2⟩
    rw [Real.sin_two_mul]; positivity
  have hw0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hsin2 _)
  have hleib := sqm_pz_DthIter_mul_le_4_open k j hk4 hj4
    (fun z θ : ℝ => 2 * C15 α θ) (G15 α Φs) hAs hGs z hz θ hθ
  refine le_trans hleib ?_
  have hbase : (0 : ℝ) ≤ (KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC1 hα.le) hBnn) hw0) (pow_pos hz1 k).le
  have hterm : ∀ c ∈ Finset.range (k + 1), ∀ a ∈ Finset.range (j + 1),
      |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => 2 * C15 α θ)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) (G15 α Φs)) z θ|
        ≤ (KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k := by
    intro c hc a ha
    have hc_le : c ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
    have ha_le : a ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    by_cases hc0 : c = 0
    · subst hc0
      rcases eq_or_lt_of_le ha_le with haj | haj
      · -- `a = j`: all angular derivatives on `A` (weighted jet bound)
        rw [haj]
        rw [pzIter_DthIter_thetaFn_apply (fun θ : ℝ => 2 * C15 α θ) j 0 z θ, if_pos rfl,
          Nat.sub_self, Work.Spaces.DthIter_zero]
        have hA := KB15_bd α hα hα1 j (by omega) θ hθI
        have hG := Work.Spaces.pz_sup_bound α 4 (G15 α Φs) hGm k hk4 z θ
          (le_of_lt hz) hθI
        have h0 : (0 : ℝ) ≤ KB15 * α
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_nonneg (mul_nonneg KB15_pos.le hα.le) hw0
        have hstep : |Work.Spaces.dthU^[j] (fun θ => 2 * C15 α θ) θ|
              * |Work.Spaces.pzIter k (G15 α Φs) z θ|
            ≤ (KB15 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k) :=
          mul_le_mul hA hG (abs_nonneg _) h0
        have hKBle : KB15 ≤ KA15 + KB15 + 1 := by linarith [KA15_pos]
        have hmono : (KB15 * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k)
            ≤ ((KA15 + KB15 + 1) * α
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKBle hα.le) hw0)
            (div_nonneg hBnn (pow_pos hz1 k).le)
        have hfin : ((KA15 + KB15 + 1) * α
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k)
            = (KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k := by
          rw [div_eq_mul_inv]; ring_nf
        exact le_trans hstep (le_trans hmono (le_of_eq hfin))
      · -- `a < j`: flat jet bound of `A`, weighted bound of `G`
        rw [pzIter_DthIter_thetaFn_apply (fun θ : ℝ => 2 * C15 α θ) a 0 z θ, if_pos rfl]
        have hja : 1 ≤ j - a := by omega
        have hjk' : k + (j - a) ≤ 4 := by omega
        have hA := KA15_bd α hα hα1 a (by omega) θ hθI
        have hG := Work.Spaces.pz_Dth_sup_bound α hα 4 (G15 α Φs) hGm (j - a) k hja hjk'
          z θ (le_of_lt hz) hθI
        have h0 : (0 : ℝ) ≤ KA15 * α ^ 2 := mul_nonneg KA15_pos.le (sq_nonneg α)
        have h1 : |Work.Spaces.dthU^[a] (fun θ => 2 * C15 α θ) θ|
              * |Work.Spaces.pzIter k (Work.Spaces.DthIter (j - a) (G15 α Φs)) z θ|
            ≤ (KA15 * α ^ 2) * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul hA hG (abs_nonneg _) h0
        have hX0 : (0 : ℝ) ≤ Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_nonneg (div_nonneg hBnn (pow_pos hz1 k).le) hw0
        have hα2 : α ^ 2 ≤ α := by nlinarith [hα, hα1]
        have h2 : (KA15 * α ^ 2) * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            ≤ (KA15 * α) * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα2 KA15_pos.le) hX0
        have h3 : KA15 ≤ KA15 + KB15 + 1 := by linarith [KB15_pos]
        have h4 : (KA15 * α) * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            ≤ ((KA15 + KB15 + 1) * α) * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hα.le) hX0
        have hfin : ((KA15 + KB15 + 1) * α)
              * (Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ k
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            = (KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k := by
          rw [div_eq_mul_inv]; ring_nf
        exact le_trans h1 (le_trans h2 (le_trans h4 (le_of_eq hfin)))
    · have hpz : Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => 2 * C15 α θ))
          z θ = 0 := by
        rw [pzIter_DthIter_thetaFn_apply (fun θ : ℝ => 2 * C15 α θ) a c z θ, if_neg hc0]
      rw [hpz]
      simp only [abs_zero, zero_mul]
      exact hbase
  have hS : (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => 2 * C15 α θ)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) (G15 α Φs)) z θ|)
      ≤ (((k + 1 : ℕ)) : ℝ) * (((j + 1 : ℕ)) : ℝ)
          * ((KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k) :=
    le_trans (Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => hterm c hc a ha)
      (sum_range_range_const k j _)
  have hA5 : (((k + 1 : ℕ)) : ℝ) * (((j + 1 : ℕ)) : ℝ) ≤ 25 := by
    have h2 : k + 1 ≤ 5 := by omega
    have h3 : (((k + 1 : ℕ)) : ℝ) ≤ 5 := by exact_mod_cast h2
    have h4 : j + 1 ≤ 5 := by omega
    have h5 : (((j + 1 : ℕ)) : ℝ) ≤ 5 := by exact_mod_cast h4
    nlinarith
  calc (257 : ℝ) * (∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => 2 * C15 α θ)) z θ|
          * |Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - a) (G15 α Φs)) z θ|)
      ≤ 257 * ((((k + 1 : ℕ)) : ℝ) * (((j + 1 : ℕ)) : ℝ)
          * ((KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k)) :=
        mul_le_mul_of_nonneg_left hS (by norm_num)
    _ = (257 * ((((k + 1 : ℕ)) : ℝ) * (((j + 1 : ℕ)) : ℝ)))
          * ((KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k) := by
        rw [div_eq_mul_inv]; ring_nf
    _ ≤ (257 * 25) * ((KA15 + KB15 + 1) * α * Work.Spaces.WlInf α 4 (G15 α Φs)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA5 (by norm_num)) hbase
    _ = KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k := by
        rw [KAGd15]; rw [div_eq_mul_inv]; ring_nf

/-! ## The final arithmetic of the two pointwise bounds -/

theorem arith_hA_core (C K K' : ℝ) (hC : 0 < C) (hK : 0 < K) (hK' : 0 < K') :
    257 * 5 * (C * K) ≤ 200000 * (10 ^ 6 * (C * (K + K' + 1) + 1) + 1) := by
  have hCK : C * K ≤ C * (K + K' + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [hK.le, hK'.le]) hC.le
  have h1 : 257 * 5 * (C * K) ≤ 257 * 5 * (C * (K + K' + 1)) :=
    mul_le_mul_of_nonneg_left hCK (by norm_num)
  have hnn : 0 ≤ C * (K + K' + 1) := mul_nonneg hC.le (by linarith [hK.le, hK'.le])
  nlinarith [h1, hnn]

theorem arith_hB_core (C K K' : ℝ) (hC : 0 < C) (hK : 0 < K) (hK' : 0 < K') :
    257 * 25 * (C * K') ≤ 200000 * (10 ^ 6 * (C * (K + K' + 1) + 1) + 1) := by
  have hCK : C * K' ≤ C * (K + K' + 1) :=
    mul_le_mul_of_nonneg_left (by linarith [hK.le, hK'.le]) hC.le
  have h1 : 257 * 25 * (C * K') ≤ 257 * 25 * (C * (K + K' + 1)) :=
    mul_le_mul_of_nonneg_left hCK (by norm_num)
  have hnn : 0 ≤ C * (K + K' + 1) := mul_nonneg hC.le (by linarith [hK.le, hK'.le])
  nlinarith [h1, hnn]

