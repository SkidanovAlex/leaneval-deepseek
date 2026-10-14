import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllipticEst.H2W.lzeroSliceL1Ae
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.Nonlinear.Open.Row15Aux.Defs
import Submission.Work.FTS.Nonlinear.Open.Row15Aux.Jets
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.StrongPersist.H6Rows.wprod6
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
set_option maxHeartbeats 1000000

theorem row15_pointwise {α Cs : ℝ} {Φs : Fn} (hα : 0 < α) (hα1 : α ≤ 1)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs)
    {KA KB Cpsi : ℝ} (hKA0 : 0 ≤ KA) (hKB0 : 0 ≤ KB) (hCpsi : 0 < Cpsi)
    (hpsib : ∀ (c m : ℕ), c ≤ m → m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ,
      (1 + z) * Work.Spaces.w z * z ^ m
        * |Work.Spaces.pzIter c (fun z _ => Work.FTS.NonlinRows.psi15 z) z θ|
        ≤ Cpsi * (1 + z) ^ (m - c))
    (hKAb : ∀ a : ℕ, a ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[a] (A15 α) θ| ≤ KA * α ^ 2)
    (hKBb : ∀ a : ℕ, a ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[a] (A15 α) θ|
        ≤ KB * α * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
    (hGs : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.NonlinRows.G15 α Φs))
    (hGm : Work.Spaces.WlInfMem α 4 (Work.FTS.NonlinRows.G15 α Φs)) :
    Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2ss α Φs) ∧
    (∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ m
          * Work.Spaces.pzIter m (Work.FTS.Nonlin.N2ss α Φs) z θ|
        ≤ 200000 * ((10 ^ 7 * Cpsi * (KA + KB + 1) + 1) * α
            * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs))) ∧
    (∀ i l : ℕ, 1 ≤ i → l + i ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ,
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
          (Work.Spaces.DthIter i (Work.FTS.Nonlin.N2ss α Φs)) z θ|
        ≤ 200000 * (((10 ^ 7 * Cpsi * (KA + KB + 1) + 1) * α
            * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs))
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) := by
  have hΛ : 0 ≤ Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) :=
    Work.FTS.H2.WlInf_nonneg hGm
  have hψs : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => Work.FTS.NonlinRows.psi15 z) :=
    Work.FTS.NonlinRows.smoothOpen_psi15
  have hAGs : Work.FTS.EllipticEst.SmoothOpen (AG15 α Φs) := smoothOpen_AG15 hα hα1 hs
  have hSO : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.Nonlin.N2ss α Φs) :=
    Work.FTS.NonlinRows.smoothOpen_N2ss hα hα1 hs
  have hEqOn : Set.EqOn (Function.uncurry (Work.FTS.Nonlin.N2ss α Φs))
      (Function.uncurry (N2ssO α Φs)) Work.FTS.EllipticEst.Q0 :=
    N2ss_eqOn_Q0 hα hα1 hs.vanishU
  set CW : ℝ := 10 ^ 7 * Cpsi * (KA + KB + 1) + 1 with hCW
  set W : ℝ := CW * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) with hWdef
  have hCW0 : 0 < CW := by
    rw [hCW]; positivity
  have hCWbig : Cpsi * (257 * 5 * KA) ≤ CW := by
    rw [hCW]
    have hKAle : 257 * 5 * KA ≤ 10 ^ 7 * (KA + KB + 1) := by
      have h1 : (0 : ℝ) ≤ KA + KB + 1 := by linarith
      nlinarith
    calc Cpsi * (257 * 5 * KA) ≤ Cpsi * (10 ^ 7 * (KA + KB + 1)) :=
          mul_le_mul_of_nonneg_left hKAle hCpsi.le
      _ ≤ 10 ^ 7 * Cpsi * (KA + KB + 1) + 1 := by
          have h2 : 0 ≤ 10 ^ 7 * Cpsi := mul_nonneg (by norm_num) hCpsi.le
          nlinarith
  have hCWbig2 : Cpsi * (257 * 25 * (KA + KB + 1)) ≤ CW := by
    rw [hCW]
    have hle : 257 * 25 * (KA + KB + 1) ≤ 10 ^ 7 * (KA + KB + 1) := by
      have h1 : (0 : ℝ) ≤ KA + KB + 1 := by linarith
      nlinarith
    calc Cpsi * (257 * 25 * (KA + KB + 1)) ≤ Cpsi * (10 ^ 7 * (KA + KB + 1)) :=
          mul_le_mul_of_nonneg_left hle hCpsi.le
      _ ≤ 10 ^ 7 * Cpsi * (KA + KB + 1) + 1 := by
          have h2 : 0 ≤ 10 ^ 7 * Cpsi := mul_nonneg (by norm_num) hCpsi.le
          nlinarith
  have hwpos : ∀ {z : ℝ}, 0 < z → 0 ≤ Work.Spaces.w z := by
    intro z hz
    rw [Work.Spaces.w]; positivity
  have hα2 : α ^ 2 ≤ α := by nlinarith [hα, hα1]
  have hc5 : (0 : ℝ) ≤ Cpsi * (257 * 5 * KA) := by positivity
  have hc52 : (0 : ℝ) ≤ Cpsi * (257 * 25 * (KA + KB + 1)) := by positivity
  -- ## the `𝒲^{4,∞}`-coefficient side of the two families
  have hAG1 := pzIter_AG_le' hα hα1 hGs hGm hKA0 hKAb
  have hAG2 := pzIter_DthIter_AG_le' hα hα1 hGs hGm hKA0 hKB0 hKAb hKBb
  have hAfam : ∀ m : ℕ, m ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ, θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ m
          * Work.Spaces.pzIter m (Work.FTS.Nonlin.N2ss α Φs) z θ| ≤ 200000 * W := by
    intro m hm z hz θ hθ
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
    have hzw : Work.Spaces.pzIter m (Work.FTS.Nonlin.N2ss α Φs) z θ
        = Work.Spaces.pzIter m (N2ssO α Φs) z θ :=
      Work.FTS.EllipticEst.H2W.pzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
        hEqOn m hmem
    have hAO : N2ssO α Φs = fun z θ : ℝ => (fun z _ => Work.FTS.NonlinRows.psi15 z) z θ
        * AG15 α Φs z θ := rfl
    rw [hzw, hAO]
    have hleib : |Work.Spaces.pzIter m (fun z θ : ℝ =>
          (fun z _ => Work.FTS.NonlinRows.psi15 z) z θ * AG15 α Φs z θ) z θ|
        ≤ (257 : ℝ) * ∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
            |Work.Spaces.pzIter c
                  (Work.Spaces.DthIter a (fun z _ => Work.FTS.NonlinRows.psi15 z)) z θ|
              * |Work.Spaces.pzIter (m - c)
                  (Work.Spaces.DthIter (0 - a) (AG15 α Φs)) z θ| :=
      Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open m 0 hm (by norm_num)
        (fun z _ => Work.FTS.NonlinRows.psi15 z) (AG15 α Φs) hψs hAGs z hz θ hθ
    have hw0 : (0 : ℝ) ≤ (1 + z) * Work.Spaces.w z * z ^ m :=
      mul_nonneg (mul_nonneg (by linarith) (hwpos hz)) (pow_nonneg hz.le m)
    rw [abs_mul, abs_of_nonneg hw0]
    have hterm : ∀ c ∈ Finset.range (m + 1), ∀ a ∈ Finset.range (0 + 1),
        (1 + z) * Work.Spaces.w z * z ^ m
          * (|Work.Spaces.pzIter c
                (Work.Spaces.DthIter a (fun z _ => Work.FTS.NonlinRows.psi15 z)) z θ|
              * |Work.Spaces.pzIter (m - c)
                  (Work.Spaces.DthIter (0 - a) (AG15 α Φs)) z θ|)
          ≤ Cpsi * (257 * 5 * KA) * α ^ 2
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) := by
      intro c hc a ha
      have ha0 : a = 0 := by
        have h' := Finset.mem_range.mp ha
        omega
      subst ha0
      have hcm : c ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
      simp only [Nat.zero_sub, Work.Spaces.DthIter_zero]
      have h1 := hpsib c m hcm hm z hz θ
      have h2 := hAG1 (m - c) (by omega) z hz θ hθ
      have h3 : (1 + z) * Work.Spaces.w z * z ^ m
            * (|Work.Spaces.pzIter c (fun z _ => Work.FTS.NonlinRows.psi15 z) z θ|
              * |Work.Spaces.pzIter (m - c) (AG15 α Φs) z θ|)
          = ((1 + z) * Work.Spaces.w z * z ^ m
              * |Work.Spaces.pzIter c (fun z _ => Work.FTS.NonlinRows.psi15 z) z θ|)
            * |Work.Spaces.pzIter (m - c) (AG15 α Φs) z θ| := by ring
      rw [h3]
      have h4 : ((1 + z) * Work.Spaces.w z * z ^ m
            * |Work.Spaces.pzIter c (fun z _ => Work.FTS.NonlinRows.psi15 z) z θ|)
            * |Work.Spaces.pzIter (m - c) (AG15 α Φs) z θ|
          ≤ (Cpsi * (1 + z) ^ (m - c))
            * (257 * 5 * KA * α ^ 2
                * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
                / (z + 1) ^ (m - c)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hCpsi.le (pow_nonneg (by linarith) _))
      refine h4.trans (le_of_eq ?_)
      have hden : ((z + 1) ^ (m - c)) ≠ 0 := ne_of_gt (pow_pos (by linarith) _)
      have hshift : (1 + z) ^ (m - c) = (z + 1) ^ (m - c) := by rw [add_comm (1 : ℝ) z]
      rw [div_eq_mul_inv, hshift]
      have heq : Cpsi * (z + 1) ^ (m - c)
            * (257 * 5 * KA * α ^ 2
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
              * ((z + 1) ^ (m - c))⁻¹)
          = Cpsi * (257 * 5 * KA) * α ^ 2
            * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
            * ((z + 1) ^ (m - c) * ((z + 1) ^ (m - c))⁻¹) := by ring
      rw [heq, mul_inv_cancel₀ hden, mul_one]
    have hsum : (∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
          (1 + z) * Work.Spaces.w z * z ^ m
            * (|Work.Spaces.pzIter c
                  (Work.Spaces.DthIter a (fun z _ => Work.FTS.NonlinRows.psi15 z)) z θ|
                * |Work.Spaces.pzIter (m - c)
                    (Work.Spaces.DthIter (0 - a) (AG15 α Φs)) z θ|))
        ≤ (∑ _c ∈ Finset.range (m + 1), ∑ _a ∈ Finset.range (0 + 1),
            (Cpsi * (257 * 5 * KA) * α ^ 2
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs))) :=
      Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => hterm c hc a ha
    have hkey : (257 : ℝ) * ((((m + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ)
          * (Cpsi * (257 * 5 * KA) * α ^ 2
            * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)))
        ≤ 200000 * W := by
      have hconst0 : (0 : ℝ) ≤ Cpsi * (257 * 5 * KA) * α ^ 2
          * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) :=
        mul_nonneg (mul_nonneg hc5 (sq_nonneg α)) hΛ
      have hcard : (((m + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ) ≤ 5 := by
        have h3 : (((m + 1 : ℕ)) : ℝ) ≤ 5 := by
          have : m + 1 ≤ 5 := by omega
          exact_mod_cast this
        have h4 : (((0 + 1 : ℕ)) : ℝ) = 1 := by norm_num
        rw [h4, mul_one]; exact h3
      have h1 : (((m + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ)
            * (Cpsi * (257 * 5 * KA) * α ^ 2
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs))
          ≤ 5 * (Cpsi * (257 * 5 * KA) * α ^ 2
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)) :=
        mul_le_mul_of_nonneg_right hcard hconst0
      have h2 : 5 * (Cpsi * (257 * 5 * KA) * α ^ 2
            * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs))
          ≤ 5 * (Cpsi * (257 * 5 * KA) * α
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα2 hc5) hΛ) (by norm_num)
      have h3 : 5 * (Cpsi * (257 * 5 * KA) * α
            * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs))
          ≤ 5 * (CW * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have h8 : Cpsi * (257 * 5 * KA) * α ≤ CW * α :=
          mul_le_mul_of_nonneg_right hCWbig hα.le
        exact mul_le_mul_of_nonneg_right h8 hΛ
      have hfin : (257 : ℝ) * (5 * (CW * α * Work.Spaces.WlInf α 4
            (Work.FTS.NonlinRows.G15 α Φs))) ≤ 200000 * W := by
        rw [hWdef]
        have h0 : (0 : ℝ) ≤ CW * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) :=
          mul_nonneg (mul_nonneg hCW0.le hα.le) hΛ
        nlinarith
      exact le_trans
        (mul_le_mul_of_nonneg_left (le_trans h1 (le_trans h2 h3)) (by norm_num)) hfin
    calc (1 + z) * Work.Spaces.w z * z ^ m
          * |Work.Spaces.pzIter m (fun z θ : ℝ =>
              (fun z _ => Work.FTS.NonlinRows.psi15 z) z θ * AG15 α Φs z θ) z θ|
        ≤ (1 + z) * Work.Spaces.w z * z ^ m * (257 * ∑ c ∈ Finset.range (m + 1),
            ∑ a ∈ Finset.range (0 + 1),
              |Work.Spaces.pzIter c
                    (Work.Spaces.DthIter a (fun z _ => Work.FTS.NonlinRows.psi15 z)) z θ|
                * |Work.Spaces.pzIter (m - c)
                    (Work.Spaces.DthIter (0 - a) (AG15 α Φs)) z θ|) :=
          mul_le_mul_of_nonneg_left hleib hw0
      _ = 257 * ((1 + z) * Work.Spaces.w z * z ^ m
            * (∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
              |Work.Spaces.pzIter c
                    (Work.Spaces.DthIter a (fun z _ => Work.FTS.NonlinRows.psi15 z)) z θ|
                * |Work.Spaces.pzIter (m - c)
                    (Work.Spaces.DthIter (0 - a) (AG15 α Φs)) z θ|)) := by ring
      _ = 257 * (∑ c ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (0 + 1),
            (1 + z) * Work.Spaces.w z * z ^ m
              * (|Work.Spaces.pzIter c
                    (Work.Spaces.DthIter a (fun z _ => Work.FTS.NonlinRows.psi15 z)) z θ|
                * |Work.Spaces.pzIter (m - c)
                    (Work.Spaces.DthIter (0 - a) (AG15 α Φs)) z θ|)) := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Finset.mul_sum]
      _ ≤ 257 * (∑ _c ∈ Finset.range (m + 1), ∑ _a ∈ Finset.range (0 + 1),
            (Cpsi * (257 * 5 * KA) * α ^ 2
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs))) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 257 * ((((m + 1 : ℕ)) : ℝ) * (((0 + 1 : ℕ)) : ℝ)
            * (Cpsi * (257 * 5 * KA) * α ^ 2
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs))) := by
          rw [sum_range_range_const]
      _ ≤ 200000 * W := hkey
  have hBfam : ∀ i l : ℕ, 1 ≤ i → l + i ≤ 4 → ∀ z : ℝ, 0 < z → ∀ θ : ℝ,
      θ ∈ Set.Ioo (0 : ℝ) (π / 2) →
      |(1 + z) * Work.Spaces.w z * z ^ l * Work.Spaces.pzIter l
          (Work.Spaces.DthIter i (Work.FTS.Nonlin.N2ss α Φs)) z θ|
        ≤ 200000 * (W * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
    intro i l hi hli z hz θ hθ
    have hmem : (z, θ) ∈ Work.FTS.EllipticEst.Q0 := ⟨hz, hθ⟩
    have hD : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (Work.FTS.Nonlin.N2ss α Φs)))
        (Function.uncurry (Work.Spaces.DthIter i (N2ssO α Φs)))
        Work.FTS.EllipticEst.Q0 :=
      Work.FTS.H2.DthIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqOn i
    have hzw : Work.Spaces.pzIter l
          (Work.Spaces.DthIter i (Work.FTS.Nonlin.N2ss α Φs)) z θ
        = Work.Spaces.pzIter l (Work.Spaces.DthIter i (N2ssO α Φs)) z θ :=
      Work.FTS.EllipticEst.H2W.pzIter_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0
        hD l hmem
    have hAO : N2ssO α Φs = fun z θ : ℝ => (fun z _ => Work.FTS.NonlinRows.psi15 z) z θ
        * AG15 α Φs z θ := rfl
    rw [hzw, hAO]
    have hleib : |Work.Spaces.pzIter l (Work.Spaces.DthIter i (fun z θ : ℝ =>
          (fun z _ => Work.FTS.NonlinRows.psi15 z) z θ * AG15 α Φs z θ)) z θ|
        ≤ (257 : ℝ) * ∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
            |Work.Spaces.pzIter c
                  (Work.Spaces.DthIter a (fun z _ => Work.FTS.NonlinRows.psi15 z)) z θ|
              * |Work.Spaces.pzIter (l - c)
                  (Work.Spaces.DthIter (i - a) (AG15 α Φs)) z θ| :=
      Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open l i (by omega) (by omega)
        (fun z _ => Work.FTS.NonlinRows.psi15 z) (AG15 α Φs) hψs hAGs z hz θ hθ
    have hw0 : (0 : ℝ) ≤ (1 + z) * Work.Spaces.w z * z ^ l :=
      mul_nonneg (mul_nonneg (by linarith) (hwpos hz)) (pow_nonneg hz.le l)
    rw [abs_mul, abs_of_nonneg hw0]
    have hs0 : 0 ≤ Real.sin (2 * θ) := by
      have h1 : 0 ≤ 2 * θ := by linarith [hθ.1]
      have h2 : 2 * θ ≤ Real.pi := by linarith [hθ.2, Real.pi_pos]
      exact Real.sin_nonneg_of_mem_Icc ⟨h1, h2⟩
    have hwgt : 0 ≤ (α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg hs0 _)
    have hterm : ∀ c ∈ Finset.range (l + 1), ∀ a ∈ Finset.range (i + 1),
        (1 + z) * Work.Spaces.w z * z ^ l
          * (|Work.Spaces.pzIter c
                (Work.Spaces.DthIter a (fun z _ => Work.FTS.NonlinRows.psi15 z)) z θ|
              * |Work.Spaces.pzIter (l - c)
                  (Work.Spaces.DthIter (i - a) (AG15 α Φs)) z θ|)
          ≤ Cpsi * (257 * 25 * (KA + KB + 1)) * α
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) := by
      intro c hc a ha
      have hcl : c ≤ l := Nat.le_of_lt_succ (Finset.mem_range.mp hc)
      have hai : a ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
      by_cases ha0 : a = 0
      · subst ha0
        simp only [Nat.sub_zero, Work.Spaces.DthIter_zero]
        have h1 := hpsib c l hcl (by omega) z hz θ
        have h2 := hAG2 i (l - c) hi (by omega) z hz θ hθ
        have h3 : (1 + z) * Work.Spaces.w z * z ^ l
              * (|Work.Spaces.pzIter c (fun z _ => Work.FTS.NonlinRows.psi15 z) z θ|
                * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter i (AG15 α Φs)) z θ|)
            = ((1 + z) * Work.Spaces.w z * z ^ l
                * |Work.Spaces.pzIter c (fun z _ => Work.FTS.NonlinRows.psi15 z) z θ|)
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter i (AG15 α Φs)) z θ| := by
          ring
        rw [h3]
        have h4 : ((1 + z) * Work.Spaces.w z * z ^ l
              * |Work.Spaces.pzIter c (fun z _ => Work.FTS.NonlinRows.psi15 z) z θ|)
              * |Work.Spaces.pzIter (l - c) (Work.Spaces.DthIter i (AG15 α Φs)) z θ|
            ≤ (Cpsi * (1 + z) ^ (l - c))
              * (257 * 25 * (KA + KB + 1) * α
                  * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
                  * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                  / (z + 1) ^ (l - c)) :=
          mul_le_mul h1 h2 (abs_nonneg _)
            (mul_nonneg hCpsi.le (pow_nonneg (by linarith) _))
        refine h4.trans (le_of_eq ?_)
        have hden : ((z + 1) ^ (l - c)) ≠ 0 := ne_of_gt (pow_pos (by linarith) _)
        have hshift : (1 + z) ^ (l - c) = (z + 1) ^ (l - c) := by rw [add_comm (1 : ℝ) z]
        rw [div_eq_mul_inv, hshift]
        have heq : Cpsi * (z + 1) ^ (l - c)
              * (257 * 25 * (KA + KB + 1) * α
                * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
                * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
                * ((z + 1) ^ (l - c))⁻¹)
            = Cpsi * (257 * 25 * (KA + KB + 1)) * α
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))
              * ((z + 1) ^ (l - c) * ((z + 1) ^ (l - c))⁻¹) := by ring
        rw [heq, mul_inv_cancel₀ hden, mul_one]
      · -- the angular derivatives fall on the `z`-only factor: everything vanishes
        have hz0 : Work.Spaces.pzIter c
            (Work.Spaces.DthIter a (fun z _ => Work.FTS.NonlinRows.psi15 z)) z θ = 0 := by
          rw [pzIter_dthIter_zFn _ a c (Nat.pos_of_ne_zero ha0)]
        rw [hz0, abs_zero]
        have hL : (1 + z) * Work.Spaces.w z * z ^ l
            * (0 * |Work.Spaces.pzIter (l - c)
                (Work.Spaces.DthIter (i - a) (AG15 α Φs)) z θ|) = 0 := by ring
        rw [hL]
        exact mul_nonneg (mul_nonneg (mul_nonneg hc52 hα.le) hΛ) hwgt
    have hsum : (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
          (1 + z) * Work.Spaces.w z * z ^ l
            * (|Work.Spaces.pzIter c
                  (Work.Spaces.DthIter a (fun z _ => Work.FTS.NonlinRows.psi15 z)) z θ|
                * |Work.Spaces.pzIter (l - c)
                    (Work.Spaces.DthIter (i - a) (AG15 α Φs)) z θ|))
        ≤ (∑ _c ∈ Finset.range (l + 1), ∑ _a ∈ Finset.range (i + 1),
            (Cpsi * (257 * 25 * (KA + KB + 1)) * α
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :=
      Finset.sum_le_sum fun c hc => Finset.sum_le_sum fun a ha => hterm c hc a ha
    have hkey : (257 : ℝ) * ((((l + 1 : ℕ)) : ℝ) * (((i + 1 : ℕ)) : ℝ)
          * (Cpsi * (257 * 25 * (KA + KB + 1)) * α
            * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
        ≤ 200000 * (W * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
      have hconst0 : (0 : ℝ) ≤ Cpsi * (257 * 25 * (KA + KB + 1)) * α
          * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
          * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
        mul_nonneg (mul_nonneg (mul_nonneg hc52 hα.le) hΛ) hwgt
      have hcard : (((l + 1 : ℕ)) : ℝ) * (((i + 1 : ℕ)) : ℝ) ≤ 25 := by
        have h3 : (((l + 1 : ℕ)) : ℝ) ≤ 5 := by
          have : l + 1 ≤ 5 := by omega
          exact_mod_cast this
        have h5 : (((i + 1 : ℕ)) : ℝ) ≤ 5 := by
          have : i + 1 ≤ 5 := by omega
          exact_mod_cast this
        nlinarith
      have h1 : (((l + 1 : ℕ)) : ℝ) * (((i + 1 : ℕ)) : ℝ)
            * (Cpsi * (257 * 25 * (KA + KB + 1)) * α
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
          ≤ 25 * (Cpsi * (257 * 25 * (KA + KB + 1)) * α
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) :=
        mul_le_mul_of_nonneg_right hcard hconst0
      have h2 : 25 * (Cpsi * (257 * 25 * (KA + KB + 1)) * α
            * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))
          ≤ 25 * (CW * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        have h8 : Cpsi * (257 * 25 * (KA + KB + 1)) * α ≤ CW * α :=
          mul_le_mul_of_nonneg_right hCWbig2 hα.le
        have h8' : Cpsi * (257 * 25 * (KA + KB + 1)) * α
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
            ≤ CW * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs) :=
          mul_le_mul_of_nonneg_right h8 hΛ
        exact mul_le_mul_of_nonneg_right h8' hwgt
      have hfin : (257 : ℝ) * (25 * (CW * α * Work.Spaces.WlInf α 4
            (Work.FTS.NonlinRows.G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))))
          ≤ 200000 * (W * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := by
        rw [hWdef]
        have h0 : (0 : ℝ) ≤ CW * α * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
            * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)) :=
          mul_nonneg (mul_nonneg (mul_nonneg hCW0.le hα.le) hΛ) hwgt
        nlinarith
      exact le_trans
        (mul_le_mul_of_nonneg_left (le_trans h1 h2) (by norm_num)) hfin
    calc (1 + z) * Work.Spaces.w z * z ^ l
          * |Work.Spaces.pzIter l (Work.Spaces.DthIter i (fun z θ : ℝ =>
              (fun z _ => Work.FTS.NonlinRows.psi15 z) z θ * AG15 α Φs z θ)) z θ|
        ≤ (1 + z) * Work.Spaces.w z * z ^ l * (257 * ∑ c ∈ Finset.range (l + 1),
            ∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.pzIter c
                    (Work.Spaces.DthIter a (fun z _ => Work.FTS.NonlinRows.psi15 z)) z θ|
                * |Work.Spaces.pzIter (l - c)
                    (Work.Spaces.DthIter (i - a) (AG15 α Φs)) z θ|) :=
          mul_le_mul_of_nonneg_left hleib hw0
      _ = 257 * ((1 + z) * Work.Spaces.w z * z ^ l
            * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
              |Work.Spaces.pzIter c
                    (Work.Spaces.DthIter a (fun z _ => Work.FTS.NonlinRows.psi15 z)) z θ|
                * |Work.Spaces.pzIter (l - c)
                    (Work.Spaces.DthIter (i - a) (AG15 α Φs)) z θ|)) := by ring
      _ = 257 * (∑ c ∈ Finset.range (l + 1), ∑ a ∈ Finset.range (i + 1),
            (1 + z) * Work.Spaces.w z * z ^ l
              * (|Work.Spaces.pzIter c
                    (Work.Spaces.DthIter a (fun z _ => Work.FTS.NonlinRows.psi15 z)) z θ|
                * |Work.Spaces.pzIter (l - c)
                    (Work.Spaces.DthIter (i - a) (AG15 α Φs)) z θ|)) := by
          congr 1
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun c _ => ?_)
          rw [Finset.mul_sum]
      _ ≤ 257 * (∑ _c ∈ Finset.range (l + 1), ∑ _a ∈ Finset.range (i + 1),
            (Cpsi * (257 * 25 * (KA + KB + 1)) * α
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num)
      _ = 257 * ((((l + 1 : ℕ)) : ℝ) * (((i + 1 : ℕ)) : ℝ)
            * (Cpsi * (257 * 25 * (KA + KB + 1)) * α
              * Work.Spaces.WlInf α 4 (Work.FTS.NonlinRows.G15 α Φs)
              * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5)))) := by
          rw [sum_range_range_const]
      _ ≤ 200000 * (W * ((α + Real.sin (2 * θ)) * (Real.sin (2 * θ)) ^ (α / 5))) := hkey
  refine ⟨hSO, ?_, ?_⟩
  · intro m hm z hz θ hθ
    have := hAfam m hm z hz θ hθ
    rwa [hWdef, hCW] at this
  · intro i l hi hli z hz θ hθ
    have := hBfam i l hi hli z hz θ hθ
    rwa [hWdef, hCW] at this

end Work.FTS.Nonlinear.Open
