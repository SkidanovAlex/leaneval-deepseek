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
import Submission.Work.FTS.NonlinRows.NRow15T2Aux.BoundB
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

/-! ## The two pointwise bounds for the open representative of `N₂^{ss}` -/

theorem row15_ptBound {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hGs : Work.FTS.EllipticEst.SmoothOpen (G15 α Φs))
    (hGm : Work.Spaces.WlInfMem α 4 (G15 α Φs)) :
    (∀ (m : ℕ), m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      |(1 + z) * Work.Spaces.w z * z ^ m * Work.Spaces.pzIter m (N2ssO α Φs) z θ|
        ≤ 200000 * (KW15 * α * Work.Spaces.WlInf α 4 (G15 α Φs))) ∧
    (∀ (i l : ℕ), 1 ≤ i → l + i ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo 0 (π / 2),
      |(1 + z) * Work.Spaces.w z * z ^ l
          * Work.Spaces.pzIter l (Work.Spaces.DthIter i (N2ssO α Φs)) z θ|
        ≤ 200000 * (KW15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) := by
  have hBnn : 0 ≤ Work.Spaces.WlInf α 4 (G15 α Φs) := Work.FTS.H2.WlInf_nonneg hGm
  have hAGs : Work.FTS.EllipticEst.SmoothOpen (AG15 α Φs) := by
    have h := Work.FTS.EllipticEst.Cert.smoothOpen_mul_bsl (smoothOpen_A15' α) hGs
    refine Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl h ?_
    intro z θ _ _ _
    simp [AG15]
  have hNil : N2ssO α Φs
      = fun z θ : ℝ => (fun z θ : ℝ => psi15 z) z θ * AG15 α Φs z θ := rfl
  constructor
  · intro m hm z hz θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hz1 : (0 : ℝ) < z + 1 := by linarith
    have hwv : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
    have hρ : 0 ≤ (1 + z) * Work.Spaces.w z * z ^ m :=
      mul_nonneg (mul_nonneg (by linarith) hwv) (pow_nonneg hz.le m)
    have hleib := sqm_pz_DthIter_mul_le_4_open m 0 hm (by norm_num)
      (fun z θ : ℝ => psi15 z) (AG15 α Φs) smoothOpen_psi15 hAGs z hz θ hθ
    rw [hNil, abs_mul, abs_of_nonneg hρ]
    refine le_trans (mul_le_mul_of_nonneg_left hleib hρ) ?_
    have hterm : ∀ c ∈ Finset.range (m + 1), ∀ a ∈ Finset.range (0 + 1),
        (1 + z) * Work.Spaces.w z * z ^ m
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
              * |Work.Spaces.pzIter (m - c) (Work.Spaces.DthIter (0 - a) (AG15 α Φs)) z θ|)
        ≤ Cp15 * KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) := by
      intro c hc a ha
      have hc4 : c ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
      have ha0 : a = 0 := by
        have h' := Finset.mem_range.mp ha
        omega
      subst ha0
      have hψ := Cp15_bd c c (le_refl c) (by omega) z hz θ
      rw [Nat.sub_self, pow_zero, mul_one] at hψ
      have hG := pzIter_AG_le hα hα1 hGs hGm (m - c) (by omega) z hz θ hθ
      have hzm : z ^ m = z ^ c * z ^ (m - c) := by rw [← pow_add]; congr 1; omega
      have hsplit : (1 + z) * Work.Spaces.w z * z ^ m
            * (|Work.Spaces.pzIter c (fun z θ : ℝ => psi15 z) z θ|
              * |Work.Spaces.pzIter (m - c) (AG15 α Φs) z θ|)
          = ((1 + z) * Work.Spaces.w z * z ^ c
              * |Work.Spaces.pzIter c (fun z θ : ℝ => psi15 z) z θ|)
            * (z ^ (m - c) * |Work.Spaces.pzIter (m - c) (AG15 α Φs) z θ|) := by
        rw [hzm]; ring
      have hstep : ((1 + z) * Work.Spaces.w z * z ^ c
              * |Work.Spaces.pzIter c (fun z θ : ℝ => psi15 z) z θ|)
            * (z ^ (m - c) * |Work.Spaces.pzIter (m - c) (AG15 α Φs) z θ|)
          ≤ Cp15 * (z ^ (m - c)
              * (KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ (m - c))) :=
        mul_le_mul hψ (mul_le_mul_of_nonneg_left hG (pow_nonneg hz.le _))
          (mul_nonneg (pow_nonneg hz.le _) (abs_nonneg _)) Cp15_pos.le
      refine le_trans (le_of_eq hsplit) ?_
      refine le_trans hstep ?_
      have hratio : z ^ (m - c) / (z + 1) ^ (m - c) ≤ 1 := by
        rw [div_le_one (pow_pos hz1 _)]
        exact pow_le_pow_left₀ hz.le (by linarith) _
      have hCKA : (0 : ℝ) ≤ Cp15 * (KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs)) :=
        mul_nonneg Cp15_pos.le (mul_nonneg (mul_nonneg KAG15_pos.le (sq_nonneg α)) hBnn)
      calc Cp15 * (z ^ (m - c)
            * (KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) / (z + 1) ^ (m - c)))
          = (Cp15 * (KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs)))
            * (z ^ (m - c) / (z + 1) ^ (m - c)) := by
            rw [div_eq_mul_inv]; ring_nf
        _ ≤ (Cp15 * (KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs))) * 1 :=
            mul_le_mul_of_nonneg_left hratio hCKA
        _ = Cp15 * KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) := by ring
    have hS : (∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
        (1 + z) * Work.Spaces.w z * z ^ m
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
              * |Work.Spaces.pzIter (m - c) (Work.Spaces.DthIter (0 - a) (AG15 α Φs)) z θ|))
        ≤ (((m + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ)
          * (Cp15 * KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs)) :=
      le_trans (Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => hterm c hc a ha)
        (sum_range_range_const m 0 _)
    have hexp : (1 + z) * Work.Spaces.w z * z ^ m
          * (257 * (∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
              |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                * |Work.Spaces.pzIter (m - c) (Work.Spaces.DthIter (0 - a) (AG15 α Φs))
                    z θ|))
        = 257 * (∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
            (1 + z) * Work.Spaces.w z * z ^ m
              * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                * |Work.Spaces.pzIter (m - c) (Work.Spaces.DthIter (0 - a) (AG15 α Φs))
                    z θ|)) := by
      rw [show (1 + z) * Work.Spaces.w z * z ^ m
            * (257 * (∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                  * |Work.Spaces.pzIter (m - c) (Work.Spaces.DthIter (0 - a) (AG15 α Φs))
                      z θ|))
          = 257 * ((1 + z) * Work.Spaces.w z * z ^ m
            * (∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                  * |Work.Spaces.pzIter (m - c) (Work.Spaces.DthIter (0 - a) (AG15 α Φs))
                      z θ|)) from by ring]
      rw [mul_sum_sum_const]
    rw [hexp]
    have hA5 : (((m + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ) ≤ 5 := by
      have h2 : m + 1 ≤ 5 := by omega
      have h3 : (((m + 1 : ℕ)) : ℝ) ≤ 5 := by exact_mod_cast h2
      have h4 : (((0 + 1 : ℕ)) : ℝ) = 1 := by norm_num
      rw [h4, mul_one]
      exact h3
    have hC0 : (0 : ℝ) ≤ Cp15 * KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs) :=
      mul_nonneg (mul_nonneg (mul_nonneg Cp15_pos.le KAG15_pos.le) (sq_nonneg α)) hBnn
    have hcore' : 257 * 5 * (Cp15 * KAG15) ≤ 200000 * KW15 := by
      show 257 * 5 * (Cp15 * KAG15)
        ≤ 200000 * (10 ^ 6 * (Cp15 * (KAG15 + KAGd15 + 1) + 1) + 1)
      exact arith_hA_core Cp15 KAG15 KAGd15 Cp15_pos KAG15_pos KAGd15_pos
    have hα2 : α ^ 2 ≤ α := by nlinarith [hα, hα1]
    calc (257 : ℝ) * (∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
          (1 + z) * Work.Spaces.w z * z ^ m
            * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
              * |Work.Spaces.pzIter (m - c) (Work.Spaces.DthIter (0 - a) (AG15 α Φs)) z θ|))
        ≤ 257 * ((((m + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ)
            * (Cp15 * KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs))) :=
          mul_le_mul_of_nonneg_left hS (by norm_num)
      _ = (257 * ((((m + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ)))
            * (Cp15 * KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs)) := by ring
      _ ≤ (257 * 5) * (Cp15 * KAG15 * α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA5 (by norm_num)) hC0
      _ = (257 * 5 * (Cp15 * KAG15)) * (α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs)) := by ring
      _ ≤ (200000 * KW15) * (α ^ 2 * Work.Spaces.WlInf α 4 (G15 α Φs)) :=
          mul_le_mul_of_nonneg_right hcore' (mul_nonneg (sq_nonneg α) hBnn)
      _ ≤ (200000 * KW15) * (α * Work.Spaces.WlInf α 4 (G15 α Φs)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hα2 hBnn)
            (mul_nonneg (by norm_num) KW15_pos.le)
      _ = 200000 * (KW15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)) := by ring
  · intro i l hi hli z hz θ hθ
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hz1 : (0 : ℝ) < z + 1 := by linarith
    have hl4 : l ≤ 4 := by omega
    have hi4 : i ≤ 4 := by omega
    have hsin2 : 0 ≤ Real.sin (2 * θ) := by
      have hs0 : 0 ≤ Real.sin θ :=
        Real.sin_nonneg_of_mem_Icc ⟨hθI.1, by linarith [hθI.2, Real.pi_pos]⟩
      have hc0 : 0 ≤ Real.cos θ :=
        Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθI.1, Real.pi_pos], hθI.2⟩
      rw [Real.sin_two_mul]; positivity
    have hw0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hsin2 _)
    have hwv : 0 ≤ Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
    have hρ : 0 ≤ (1 + z) * Work.Spaces.w z * z ^ l :=
      mul_nonneg (mul_nonneg (by linarith) hwv) (pow_nonneg hz.le l)
    have hleib := sqm_pz_DthIter_mul_le_4_open l i hl4 hi4
      (fun z θ : ℝ => psi15 z) (AG15 α Φs) smoothOpen_psi15 hAGs z hz θ hθ
    rw [hNil, abs_mul, abs_of_nonneg hρ]
    refine le_trans (mul_le_mul_of_nonneg_left hleib hρ) ?_
    have hterm : ∀ c ∈ Finset.range (l + 1), ∀ a ∈ Finset.range (i + 1),
        (1 + z) * Work.Spaces.w z * z ^ l
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (AG15 α Φs))
                  z θ|)
        ≤ Cp15 * KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
      intro c hc a ha
      have hc4 : c ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
      by_cases ha0 : a = 0
      · subst ha0
        have hψ := Cp15_bd c c (le_refl c) (by omega) z hz θ
        rw [Nat.sub_self, pow_zero, mul_one] at hψ
        have hG := pzIter_DthIter_AG_le hα hα1 hGs hGm i (l - c) hi (by omega) z hz θ hθ
        have hzm : z ^ l = z ^ c * z ^ (l - c) := by rw [← pow_add]; congr 1; omega
        have hsplit : (1 + z) * Work.Spaces.w z * z ^ l
              * (|Work.Spaces.pzIter c (fun z θ : ℝ => psi15 z) z θ|
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter i (AG15 α Φs)) z θ|)
            = ((1 + z) * Work.Spaces.w z * z ^ c
                * |Work.Spaces.pzIter c (fun z θ : ℝ => psi15 z) z θ|)
              * (z ^ (l - c)
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter i (AG15 α Φs))
                    z θ|) := by
          rw [hzm]; ring
        have hstep : ((1 + z) * Work.Spaces.w z * z ^ c
              * |Work.Spaces.pzIter c (fun z θ : ℝ => psi15 z) z θ|)
              * (z ^ (l - c)
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter i (AG15 α Φs)) z θ|)
            ≤ Cp15 * (z ^ (l - c)
                * (KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
                    * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                    / (z + 1) ^ (l - c))) :=
          mul_le_mul hψ (mul_le_mul_of_nonneg_left hG (pow_nonneg hz.le _))
            (mul_nonneg (pow_nonneg hz.le _) (abs_nonneg _)) Cp15_pos.le
        refine le_trans (le_of_eq hsplit) ?_
        refine le_trans hstep ?_
        have hratio : z ^ (l - c) / (z + 1) ^ (l - c) ≤ 1 := by
          rw [div_le_one (pow_pos hz1 _)]
          exact pow_le_pow_left₀ hz.le (by linarith) _
        have hCW : (0 : ℝ) ≤ Cp15 * (KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_nonneg Cp15_pos.le
            (mul_nonneg (mul_nonneg (mul_nonneg KAGd15_pos.le hα.le) hBnn) hw0)
        calc Cp15 * (z ^ (l - c)
              * (KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                  / (z + 1) ^ (l - c)))
            = (Cp15 * (KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
              * (z ^ (l - c) / (z + 1) ^ (l - c)) := by
              rw [div_eq_mul_inv]; ring_nf
          _ ≤ (Cp15 * (KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) * 1 :=
              mul_le_mul_of_nonneg_left hratio hCW
          _ = Cp15 * KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by ring
      · have hpz : Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z))
            z θ = 0 := by
          simp only [pzIter_DthIter_zFn psi15 a c (by omega)]
        rw [hpz]
        simp only [abs_zero, zero_mul, mul_zero]
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg Cp15_pos.le KAGd15_pos.le) hα.le) hBnn)
          hw0
    have hS : (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
        (1 + z) * Work.Spaces.w z * z ^ l
          * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (AG15 α Φs))
                  z θ|))
        ≤ (((l + 1 : ℕ)) : ℝ) * (((i + 1 : ℕ)) : ℝ)
          * (Cp15 * KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
      le_trans (Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => hterm c hc a ha)
        (sum_range_range_const l i _)
    have hexp : (1 + z) * Work.Spaces.w z * z ^ l
          * (257 * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (AG15 α Φs))
                    z θ|))
        = 257 * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
            (1 + z) * Work.Spaces.w z * z ^ l
              * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (AG15 α Φs))
                    z θ|)) := by
      rw [show (1 + z) * Work.Spaces.w z * z ^ l
            * (257 * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                  * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (AG15 α Φs))
                      z θ|))
          = 257 * ((1 + z) * Work.Spaces.w z * z ^ l
            * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
                |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
                  * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (AG15 α Φs))
                      z θ|)) from by ring]
      rw [mul_sum_sum_const]
    rw [hexp]
    have hA5 : (((l + 1 : ℕ)) : ℝ) * (((i + 1 : ℕ)) : ℝ) ≤ 25 := by
      have h2 : l + 1 ≤ 5 := by omega
      have h3 : (((l + 1 : ℕ)) : ℝ) ≤ 5 := by exact_mod_cast h2
      have h4 : i + 1 ≤ 5 := by omega
      have h5 : (((i + 1 : ℕ)) : ℝ) ≤ 5 := by exact_mod_cast h4
      nlinarith
    have hC0 : (0 : ℝ) ≤ Cp15 * KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
        * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg Cp15_pos.le KAGd15_pos.le) hα.le) hBnn)
        hw0
    have hcore' : 257 * 25 * (Cp15 * KAGd15) ≤ 200000 * KW15 := by
      show 257 * 25 * (Cp15 * KAGd15)
        ≤ 200000 * (10 ^ 6 * (Cp15 * (KAG15 + KAGd15 + 1) + 1) + 1)
      exact arith_hB_core Cp15 KAG15 KAGd15 Cp15_pos KAG15_pos KAGd15_pos
    calc (257 : ℝ) * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
          (1 + z) * Work.Spaces.w z * z ^ l
            * (|Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun z θ : ℝ => psi15 z)) z θ|
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter (i - a) (AG15 α Φs))
                  z θ|))
        ≤ 257 * ((((l + 1 : ℕ)) : ℝ) * (((i + 1 : ℕ)) : ℝ)
            * (Cp15 * KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :=
          mul_le_mul_of_nonneg_left hS (by norm_num)
      _ = (257 * ((((l + 1 : ℕ)) : ℝ) * (((i + 1 : ℕ)) : ℝ)))
            * (Cp15 * KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by ring
      _ ≤ (257 * 25) * (Cp15 * KAGd15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA5 (by norm_num)) hC0
      _ = (257 * 25 * (Cp15 * KAGd15))
            * (α * (Work.Spaces.WlInf α 4 (G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) := by ring
      _ ≤ (200000 * KW15)
            * (α * (Work.Spaces.WlInf α 4 (G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :=
          mul_le_mul_of_nonneg_right hcore' (mul_nonneg hα.le (mul_nonneg hBnn hw0))
      _ = 200000 * (KW15 * α * Work.Spaces.WlInf α 4 (G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by ring

end Work.FTS.NonlinRows
