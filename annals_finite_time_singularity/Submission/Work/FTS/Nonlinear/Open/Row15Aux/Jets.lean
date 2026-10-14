import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.H2W.lzeroSliceL1Ae
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.Nonlinear.Open.Row15Aux.Defs
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.T2Sup.PairBnd
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_StreamBdry.SB4.DzEpartEq
import Submission.Work.Spaces.factor_bound
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sup_mixed_le_H4

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000


/-! ## The `z`-jets of `AG15` -/

/-- `|∂_z^k (AG15 α Φs)| ≤ 257·5·KA·α²·Λ/(z+1)^k`, where `KA` bounds the angular jets of
`A15` and `Λ = |G15|_{𝒲^{4,∞}}`. -/
theorem pzIter_AG_le' {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hGs : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.NonlinRows.G15 α Φs))
    (hGm : Work.Spaces.WlInfMem α 4 (Work.FTS.NonlinRows.G15 α Φs))
    {KA : ℝ} (hKA0 : 0 ≤ KA)
    (hKAb : ∀ a : ℕ, a ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[a] (A15 α) θ| ≤ KA * α ^ 2) :
    ∀ k : ℕ, k ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pzIter k (AG15 α Φs) z θ|
        ≤ 257 * 5 * KA * α ^ 2
            * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) / (z + 1) ^ k := by
  have hΛ : 0 ≤ Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) :=
    Work.FTS.H2.WlInf_nonneg hGm
  have hAs : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ' : ℝ) => A15 α θ') := smoothOpen_A15 α
  intro k hk z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have hAG : AG15 α Φs = fun z θ : ℝ => (fun _ (θ' : ℝ) => A15 α θ') z θ
      * Work.FTS.NonlinRows.G15 α Φs z θ := rfl
  have hleib := Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open k 0 hk (by norm_num)
    (fun _ (θ' : ℝ) => A15 α θ') (Work.FTS.NonlinRows.G15 α Φs) hAs hGs z hz θ hθ
  rw [hAG]
  refine hleib.trans ?_
  have hbase : (0 : ℝ) ≤ KA * α ^ 2 * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
      / (z + 1) ^ k :=
    div_nonneg (mul_nonneg (mul_nonneg hKA0 (sq_nonneg α)) hΛ) (pow_pos hz1 k).le
  have hterm : ∀ c ∈ Finset.range (k + 1), ∀ a ∈ Finset.range (0 + 1),
      |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun _ (θ' : ℝ) => A15 α θ')) z θ|
        * |Work.Spaces.pzIter (k - c)
            (Work.Spaces.DthIter (0 - a) (Work.FTS.NonlinRows.G15 α Φs)) z θ|
        ≤ KA * α ^ 2 * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) / (z + 1) ^ k := by
    intro c hc a ha
    have ha0 : a = 0 := by
      have h' := Finset.mem_range.mp ha
      omega
    subst ha0
    have hc_le : c ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
    rw [Nat.zero_sub, pzIter_DthIter_thetaFn_apply (A15 α) 0 c z θ,
      Work.Spaces.DthIter_zero]
    by_cases hc0 : c = 0
    · subst hc0
      rw [if_pos rfl, Nat.sub_zero]
      have hA := hKAb 0 (by norm_num) θ hθI
      have hG := Work.Spaces.pz_sup_bound α 4 (Work.FTS.NonlinRows.G15 α Φs) hGm k hk z θ
        (le_of_lt hz) hθI
      have h0 : (0 : ℝ) ≤ KA * α ^ 2 := mul_nonneg hKA0 (sq_nonneg α)
      calc |Work.Spaces.dthU^[0] (A15 α) θ|
            * |Work.Spaces.pzIter k (Work.FTS.NonlinRows.G15 α Φs) z θ|
          ≤ (KA * α ^ 2) * (Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
              / (z + 1) ^ k) := mul_le_mul hA hG (abs_nonneg _) h0
        _ = KA * α ^ 2 * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
              / (z + 1) ^ k := by ring
    · rw [if_neg hc0]
      simp only [abs_zero, zero_mul]
      exact hbase
  calc (257 : ℝ) * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (0 + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun _ (θ' : ℝ) => A15 α θ')) z θ|
          * |Work.Spaces.pzIter (k - c)
              (Work.Spaces.DthIter (0 - a) (Work.FTS.NonlinRows.G15 α Φs)) z θ|
      ≤ 257 * ∑ _c ∈ Finset.range (k + 1), ∑ _a ∈ Finset.range (0 + 1),
          (KA * α ^ 2 * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
            / (z + 1) ^ k) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => hterm c hc a ha
    _ = 257 * (((k + 1 : ℕ) : ℝ) * (((0 + 1 : ℕ)) : ℝ)
          * (KA * α ^ 2 * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
            / (z + 1) ^ k)) := by
        rw [sum_range_range_const]
    _ ≤ 257 * (5 * (KA * α ^ 2 * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
            / (z + 1) ^ k)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have h1 : (((k + 1 : ℕ) : ℝ) * (((0 + 1 : ℕ)) : ℝ)) ≤ 5 := by
          have h3 : (((k + 1 : ℕ)) : ℝ) ≤ 5 := by
            have : k + 1 ≤ 5 := by omega
            exact_mod_cast this
          have h4 : (((0 + 1 : ℕ)) : ℝ) = 1 := by norm_num
          rw [h4, mul_one]
          exact h3
        exact mul_le_mul_of_nonneg_right h1 hbase
    _ = 257 * 5 * KA * α ^ 2 * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
          / (z + 1) ^ k := by
        rw [div_eq_mul_inv]
        ring

/-- `|∂_z^k D_θ^j (AG15 α Φs)| ≤ (257·25·(KA+KB+1))·α·Λ·(α+sin2θ)sin(2θ)^{α/5}/(z+1)^k`,
where `KA`/`KB` bound the flat/weighted angular jets of `A15`. -/
theorem pzIter_DthIter_AG_le' {α : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hGs : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.NonlinRows.G15 α Φs))
    (hGm : Work.Spaces.WlInfMem α 4 (Work.FTS.NonlinRows.G15 α Φs))
    {KA KB : ℝ} (hKA0 : 0 ≤ KA) (hKB0 : 0 ≤ KB)
    (hKAb : ∀ a : ℕ, a ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[a] (A15 α) θ| ≤ KA * α ^ 2)
    (hKBb : ∀ a : ℕ, a ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[a] (A15 α) θ|
        ≤ KB * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :
    ∀ j k : ℕ, 1 ≤ j → k + j ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2),
      |Work.Spaces.pzIter k (Work.Spaces.DthIter j (AG15 α Φs)) z θ|
        ≤ 257 * 25 * (KA + KB + 1) * α
            * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k := by
  have hΛ : 0 ≤ Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) :=
    Work.FTS.H2.WlInf_nonneg hGm
  have hAs : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ' : ℝ) => A15 α θ') := smoothOpen_A15 α
  intro j k hj hjk z hz θ hθ
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have hk4 : k ≤ 4 := by omega
  have hj4 : j ≤ 4 := by omega
  have hs0 : 0 ≤ Real.sin (2 * θ) := by
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθI.1],
      by linarith [hθI.2, Real.pi_pos]⟩
  have hw0 : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
    mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)
  have hAG : AG15 α Φs = fun z θ : ℝ => (fun _ (θ' : ℝ) => A15 α θ') z θ
      * Work.FTS.NonlinRows.G15 α Φs z θ := rfl
  have hleib := Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open k j hk4 hj4
    (fun _ (θ' : ℝ) => A15 α θ') (Work.FTS.NonlinRows.G15 α Φs) hAs hGs z hz θ hθ
  rw [hAG]
  refine hleib.trans ?_
  have hbase : (0 : ℝ) ≤ (KA + KB + 1) * α
      * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
      * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by linarith) hα.le) hΛ) hw0)
      (pow_pos hz1 k).le
  have hterm : ∀ c ∈ Finset.range (k + 1), ∀ a ∈ Finset.range (j + 1),
      |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun _ (θ' : ℝ) => A15 α θ')) z θ|
        * |Work.Spaces.pzIter (k - c)
            (Work.Spaces.DthIter (j - a) (Work.FTS.NonlinRows.G15 α Φs)) z θ|
        ≤ (KA + KB + 1) * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k := by
    intro c hc a ha
    have hc_le : c ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
    have ha_le : a ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    rw [pzIter_DthIter_thetaFn_apply (A15 α) a c z θ]
    by_cases hc0 : c = 0
    · subst hc0
      rw [if_pos rfl, Nat.sub_zero]
      rcases eq_or_lt_of_le ha_le with haj | haj
      · -- all angular derivatives on `A15`: weighted jet bound of `A15`, flat bound of `G15`
        rw [haj, Nat.sub_self, Work.Spaces.DthIter_zero]
        have hA := hKBb j hj4 θ hθI
        have hG := Work.Spaces.pz_sup_bound α 4 (Work.FTS.NonlinRows.G15 α Φs) hGm k hk4
          z θ (le_of_lt hz) hθI
        have h0 : (0 : ℝ) ≤ KB * α
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_nonneg (mul_nonneg hKB0 hα.le) hw0
        have hstep : |Work.Spaces.dthU^[j] (A15 α) θ|
              * |Work.Spaces.pzIter k (Work.FTS.NonlinRows.G15 α Φs) z θ|
            ≤ (KB * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
                * (Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) / (z + 1) ^ k) :=
          mul_le_mul hA hG (abs_nonneg _) h0
        have hKBle : KB ≤ KA + KB + 1 := by linarith
        refine hstep.trans ?_
        have hmono : (KB * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              * (Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) / (z + 1) ^ k)
            ≤ ((KA + KB + 1) * α
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
              * (Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) / (z + 1) ^ k) := by
          refine mul_le_mul_of_nonneg_right ?_ (div_nonneg hΛ (pow_pos hz1 k).le)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hKBle hα.le) hw0
        refine hmono.trans (le_of_eq ?_)
        rw [div_eq_mul_inv]
        ring
      · -- some angular derivative falls on `G15`: flat bound of `A15`, weighted bound of `G15`
        have hja : 1 ≤ j - a := by omega
        have hjk' : k + (j - a) ≤ 4 := by omega
        have hA := hKAb a (by omega) θ hθI
        have hG := Work.Spaces.pz_Dth_sup_bound α hα 4 (Work.FTS.NonlinRows.G15 α Φs) hGm
          (j - a) k hja hjk' z θ (le_of_lt hz) hθI
        have h0 : (0 : ℝ) ≤ KA * α ^ 2 := mul_nonneg hKA0 (sq_nonneg α)
        have hstep : |Work.Spaces.dthU^[a] (A15 α) θ|
              * |Work.Spaces.pzIter k
                  (Work.Spaces.DthIter (j - a) (Work.FTS.NonlinRows.G15 α Φs)) z θ|
            ≤ (KA * α ^ 2) * (Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
                / (z + 1) ^ k
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
          mul_le_mul hA hG (abs_nonneg _) h0
        refine hstep.trans ?_
        have hα2 : α ^ 2 ≤ α := by nlinarith [hα, hα1]
        have h2 : (KA * α ^ 2) * (Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
              / (z + 1) ^ k
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            ≤ (KA * α) * (Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
              / (z + 1) ^ k
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
          refine mul_le_mul_of_nonneg_right ?_
            (mul_nonneg (div_nonneg hΛ (pow_pos hz1 k).le) hw0)
          exact mul_le_mul_of_nonneg_left hα2 hKA0
        refine h2.trans ?_
        have h3 : KA ≤ KA + KB + 1 := by linarith
        have h4 : (KA * α) * (Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
              / (z + 1) ^ k
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
            ≤ ((KA + KB + 1) * α) * (Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
              / (z + 1) ^ k
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
          refine mul_le_mul_of_nonneg_right ?_
            (mul_nonneg (div_nonneg hΛ (pow_pos hz1 k).le) hw0)
          exact mul_le_mul_of_nonneg_right h3 hα.le
        refine h4.trans (le_of_eq ?_)
        rw [div_eq_mul_inv]
        ring
    · rw [if_neg hc0]
      simp only [abs_zero, zero_mul]
      exact hbase
  calc (257 : ℝ) * ∑ c ∈ Finset.range (k + 1), ∑ a ∈ Finset.range (j + 1),
        |Work.Spaces.pzIter c (Work.Spaces.DthIter a (fun _ (θ' : ℝ) => A15 α θ')) z θ|
          * |Work.Spaces.pzIter (k - c)
              (Work.Spaces.DthIter (j - a) (Work.FTS.NonlinRows.G15 α Φs)) z θ|
      ≤ 257 * ∑ _c ∈ Finset.range (k + 1), ∑ _a ∈ Finset.range (j + 1),
          ((KA + KB + 1) * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => hterm c hc a ha
    _ = 257 * (((k + 1 : ℕ) : ℝ) * (((j + 1 : ℕ)) : ℝ)
          * ((KA + KB + 1) * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k)) := by
        rw [sum_range_range_const]
    _ ≤ 257 * (25 * ((KA + KB + 1) * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have h1 : (((k + 1 : ℕ) : ℝ) * (((j + 1 : ℕ)) : ℝ)) ≤ 25 := by
          have h3 : (((k + 1 : ℕ)) : ℝ) ≤ 5 := by
            have : k + 1 ≤ 5 := by omega
            exact_mod_cast this
          have h5 : (((j + 1 : ℕ)) : ℝ) ≤ 5 := by
            have : j + 1 ≤ 5 := by omega
            exact_mod_cast this
          nlinarith
        exact mul_le_mul_of_nonneg_right h1 hbase
    _ = 257 * 25 * (KA + KB + 1) * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) / (z + 1) ^ k := by
        rw [div_eq_mul_inv]
        ring


end Work.FTS.Nonlinear.Open
