import Mathlib
import Submission.Work.Asymptotics.KhatE1R.Kdev8WresAssembly
import Submission.Work.Asymptotics.KhatE1R.Kdev8WresDevPieces
import Submission.Work.Asymptotics.KhatE1.KdevE2_strip_bound
import Submission.Work.Asymptotics.KhatE1.KdevA4Book
import Submission.Work.Asymptotics.KhatE1.E1combo8_bound
import Submission.Work.Asymptotics.KhatE1.Kdev8CoeffAux
import Submission.Work.Asymptotics.KhatE1Sharp.Kdev8WresTailPoly
import Submission.Work.Asymptotics.KPlusXiDefs
import Submission.Work.Asymptotics.CuspL_eq

namespace Work.Asymptotics.KhatE1RCore

open Work.Asymptotics.KhatE1Core Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

open Work.Kernels


/-- **The strip-bound predicate with two exponents.**  `BdE e k F` means: on the funnel strip
(`Funnel τ`, `τ.im + 1 ≤ t`, `-1 ≤ z.re ≤ 2`, `z.im = t`),

  `‖F τ z‖ ≤ C · ‖q(τ)‖^e · ‖Ept z‖^k · (scale τ)^N · (1+t)^M`.

Since `‖q(τ)‖ ≤ 1` and `‖Ept z‖ ≤ 1` on the strip, *larger* exponents are stronger statements;
`BdE.mono_e` / `BdE.mono_k` lower them. -/
def BdE (e k : ℕ) (F : ℍ → ℍ → ℂ) : Prop :=
  ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t → -1 ≤ z.re → z.re ≤ 2 →
      z.im = t → ‖F τ z‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ e
        * ‖Work.Residues.Ept z‖ ^ k * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M

namespace BdE

lemma Snn (τ : ℍ) (N : ℝ) : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N :=
  Real.rpow_nonneg (le_of_lt (Work.Kernels.scale_pos τ)) N

lemma one_le_T {τ : ℍ} {t : ℝ} (hτ : Work.Asymptotics.Funnel τ) (ht : τ.im + 1 ≤ t) :
    (1 : ℝ) ≤ 1 + t := by
  have h2 : (2 : ℝ) ≤ τ.im := hτ.2
  linarith

lemma q_le_one {τ : ℍ} (hτ : Work.Asymptotics.Funnel τ) :
    ‖Work.Kernels.qParamFun τ‖ ≤ 1 := by
  rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, hτ.2]

lemma E_le_one {τ z : ℍ} {t : ℝ} (hτ : Work.Asymptotics.Funnel τ) (ht : τ.im + 1 ≤ t)
    (hzt : z.im = t) : ‖Work.Residues.Ept z‖ ≤ 1 := by
  rw [Work.Residues.norm_Ept, hzt, Real.exp_le_one_iff]
  nlinarith [Real.pi_pos, hτ.2, ht]

/-- Constants. -/
lemma const (c : ℂ) : BdE 0 0 (fun _ _ => c) :=
  ⟨‖c‖ + 1, 0, 0, by positivity, le_rfl, le_rfl, fun τ z t _ _ _ _ _ => by
    simp only [pow_zero, Real.rpow_zero, mul_one, one_mul]
    linarith [norm_nonneg c]⟩

lemma one : BdE 0 0 (fun _ _ => (1 : ℂ)) := by simpa using const (1 : ℂ)

lemma neg {p k : ℕ} {F : ℍ → ℍ → ℂ} (h : BdE p k F) : BdE p k (fun τ z => -F τ z) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht ha hb' hzt => by
    rw [norm_neg]; exact hb τ z t hτ ht ha hb' hzt⟩

lemma cmul (c : ℂ) {p k : ℕ} {F : ℍ → ℍ → ℂ} (h : BdE p k F) :
    BdE p k (fun τ z => c * F τ z) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨(‖c‖ + 1) * (C + 1), N, M, by positivity, hN, hM, fun τ z t hτ ht ha hb' hzt => ?_⟩
  have hT1 : (1 : ℝ) ≤ 1 + t := one_le_T hτ ht
  have hcoef : ‖c‖ * C ≤ (‖c‖ + 1) * (C + 1) := by nlinarith [norm_nonneg c, hC]
  have hS0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N := Snn τ N
  have hT0 : (0 : ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg (le_trans zero_le_one hT1) M
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ p := pow_nonneg (norm_nonneg _) p
  have he0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ ^ k := pow_nonneg (norm_nonneg _) k
  rw [norm_mul]
  calc ‖c‖ * ‖F τ z‖
      ≤ ‖c‖ * (C * ‖Work.Kernels.qParamFun τ‖ ^ p * ‖Work.Residues.Ept z‖ ^ k
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) :=
        mul_le_mul_of_nonneg_left (hb τ z t hτ ht ha hb' hzt) (norm_nonneg c)
    _ = (‖c‖ * C) * (‖Work.Kernels.qParamFun τ‖ ^ p * ‖Work.Residues.Ept z‖ ^ k
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) := by ring
    _ ≤ ((‖c‖ + 1) * (C + 1)) * (‖Work.Kernels.qParamFun τ‖ ^ p
          * ‖Work.Residues.Ept z‖ ^ k * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = (‖c‖ + 1) * (C + 1) * ‖Work.Kernels.qParamFun τ‖ ^ p
          * ‖Work.Residues.Ept z‖ ^ k * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by ring

/-- Addition lowers both exponents to the minimum. -/
lemma add {p q k l : ℕ} {F G : ℍ → ℍ → ℂ} (hF : BdE p k F) (hG : BdE q l G) :
    BdE (min p q) (min k l) (fun τ z => F τ z + G τ z) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, h1⟩ := hF
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, h2⟩ := hG
  refine ⟨C1 + C2, max N1 N2, max M1 M2, by positivity, le_max_of_le_left hN1,
    le_max_of_le_left hM1, fun τ z t hτ ht ha hb hzt => ?_⟩
  have hS1 : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hT1 : (1 : ℝ) ≤ 1 + t := one_le_T hτ ht
  have hQ1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := q_le_one hτ
  have hE1 : ‖Work.Residues.Ept z‖ ≤ 1 := E_le_one hτ ht hzt
  have hQ0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hE0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have hp : ‖Work.Kernels.qParamFun τ‖ ^ p ≤ ‖Work.Kernels.qParamFun τ‖ ^ (min p q) :=
    pow_le_pow_of_le_one hQ0 hQ1 (min_le_left _ _)
  have hq : ‖Work.Kernels.qParamFun τ‖ ^ q ≤ ‖Work.Kernels.qParamFun τ‖ ^ (min p q) :=
    pow_le_pow_of_le_one hQ0 hQ1 (min_le_right _ _)
  have hk : ‖Work.Residues.Ept z‖ ^ k ≤ ‖Work.Residues.Ept z‖ ^ (min k l) :=
    pow_le_pow_of_le_one hE0 hE1 (min_le_left _ _)
  have hl : ‖Work.Residues.Ept z‖ ^ l ≤ ‖Work.Residues.Ept z‖ ^ (min k l) :=
    pow_le_pow_of_le_one hE0 hE1 (min_le_right _ _)
  have e1S : (Work.Kernels.scale τ) ^ N1 ≤ (Work.Kernels.scale τ) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hS1 (le_max_left _ _)
  have e2S : (Work.Kernels.scale τ) ^ N2 ≤ (Work.Kernels.scale τ) ^ (max N1 N2) :=
    Real.rpow_le_rpow_of_exponent_le hS1 (le_max_right _ _)
  have e1T : (1 + t) ^ M1 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (le_max_left _ _)
  have e2T : (1 + t) ^ M2 ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_le_rpow_of_exponent_le hT1 (le_max_right _ _)
  have hSmax0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ (max N1 N2) := Snn τ _
  have hTmax0 : (0 : ℝ) ≤ (1 + t) ^ (max M1 M2) :=
    Real.rpow_nonneg (le_trans zero_le_one hT1) _
  have hS1n : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N1 := Snn τ N1
  have hS2n : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N2 := Snn τ N2
  have hT1n : (0 : ℝ) ≤ (1 + t) ^ M1 := Real.rpow_nonneg (le_trans zero_le_one hT1) M1
  have hT2n : (0 : ℝ) ≤ (1 + t) ^ M2 := Real.rpow_nonneg (le_trans zero_le_one hT1) M2
  have hQm0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ (min p q) := pow_nonneg hQ0 _
  have hEm0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ ^ (min k l) := pow_nonneg hE0 _
  have A1 : ‖F τ z‖ ≤ C1 * ‖Work.Kernels.qParamFun τ‖ ^ (min p q)
      * ‖Work.Residues.Ept z‖ ^ (min k l) * (Work.Kernels.scale τ) ^ (max N1 N2)
      * (1 + t) ^ (max M1 M2) := by
    refine le_trans (h1 τ z t hτ ht ha hb hzt) ?_
    have hqk : ‖Work.Kernels.qParamFun τ‖ ^ p * ‖Work.Residues.Ept z‖ ^ k
        ≤ ‖Work.Kernels.qParamFun τ‖ ^ (min p q) * ‖Work.Residues.Ept z‖ ^ (min k l) :=
      mul_le_mul hp hk (pow_nonneg hE0 _) hQm0
    have hST : (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
        ≤ (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) :=
      mul_le_mul e1S e1T hT1n hSmax0
    calc C1 * ‖Work.Kernels.qParamFun τ‖ ^ p * ‖Work.Residues.Ept z‖ ^ k
          * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1
        = (C1 * (‖Work.Kernels.qParamFun τ‖ ^ p * ‖Work.Residues.Ept z‖ ^ k))
            * ((Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1) := by ring
      _ ≤ (C1 * (‖Work.Kernels.qParamFun τ‖ ^ (min p q)
              * ‖Work.Residues.Ept z‖ ^ (min k l)))
            * ((Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hqk hC1.le) hST (mul_nonneg hS1n hT1n) (by positivity)
      _ = C1 * ‖Work.Kernels.qParamFun τ‖ ^ (min p q) * ‖Work.Residues.Ept z‖ ^ (min k l)
            * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) := by ring
  have A2 : ‖G τ z‖ ≤ C2 * ‖Work.Kernels.qParamFun τ‖ ^ (min p q)
      * ‖Work.Residues.Ept z‖ ^ (min k l) * (Work.Kernels.scale τ) ^ (max N1 N2)
      * (1 + t) ^ (max M1 M2) := by
    refine le_trans (h2 τ z t hτ ht ha hb hzt) ?_
    have hql : ‖Work.Kernels.qParamFun τ‖ ^ q * ‖Work.Residues.Ept z‖ ^ l
        ≤ ‖Work.Kernels.qParamFun τ‖ ^ (min p q) * ‖Work.Residues.Ept z‖ ^ (min k l) :=
      mul_le_mul hq hl (pow_nonneg hE0 _) hQm0
    have hST : (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2
        ≤ (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) :=
      mul_le_mul e2S e2T hT2n hSmax0
    calc C2 * ‖Work.Kernels.qParamFun τ‖ ^ q * ‖Work.Residues.Ept z‖ ^ l
          * (Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2
        = (C2 * (‖Work.Kernels.qParamFun τ‖ ^ q * ‖Work.Residues.Ept z‖ ^ l))
            * ((Work.Kernels.scale τ) ^ N2 * (1 + t) ^ M2) := by ring
      _ ≤ (C2 * (‖Work.Kernels.qParamFun τ‖ ^ (min p q)
              * ‖Work.Residues.Ept z‖ ^ (min k l)))
            * ((Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hql hC2.le) hST (mul_nonneg hS2n hT2n) (by positivity)
      _ = C2 * ‖Work.Kernels.qParamFun τ‖ ^ (min p q) * ‖Work.Residues.Ept z‖ ^ (min k l)
            * (Work.Kernels.scale τ) ^ (max N1 N2) * (1 + t) ^ (max M1 M2) := by ring
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add A1 A2) (le_of_eq ?_)
  ring

lemma sub {p k : ℕ} {F G : ℍ → ℍ → ℂ} (hF : BdE p k F) (hG : BdE p k G) :
    BdE p k (fun τ z => F τ z - G τ z) := by
  have h := add hF (neg hG)
  rw [min_self, min_self] at h
  simpa only [sub_eq_add_neg] using h

/-- Multiplication adds the exponents. -/
lemma mul {p q k l : ℕ} {F G : ℍ → ℍ → ℂ} (hF : BdE p k F) (hG : BdE q l G) :
    BdE (p + q) (k + l) (fun τ z => F τ z * G τ z) := by
  obtain ⟨C1, N1, M1, hC1, hN1, hM1, h1⟩ := hF
  obtain ⟨C2, N2, M2, hC2, hN2, hM2, h2⟩ := hG
  refine ⟨C1 * C2, N1 + N2, M1 + M2, by positivity, by positivity, by positivity,
    fun τ z t hτ ht ha hb hzt => ?_⟩
  rw [norm_mul]
  have hT1 : (1 : ℝ) ≤ 1 + t := one_le_T hτ ht
  have hQ0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hE0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have hA : (0 : ℝ) ≤ C1 * ‖Work.Kernels.qParamFun τ‖ ^ p * ‖Work.Residues.Ept z‖ ^ k
      * (Work.Kernels.scale τ) ^ N1 * (1 + t) ^ M1 := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC1.le (pow_nonneg hQ0 p))
      (pow_nonneg hE0 k)) (Snn τ N1)) ?_
    exact Real.rpow_nonneg (le_trans zero_le_one hT1) M1
  refine le_trans (mul_le_mul (h1 τ z t hτ ht ha hb hzt) (h2 τ z t hτ ht ha hb hzt)
    (norm_nonneg _) hA) ?_
  refine le_of_eq ?_
  rw [Real.rpow_add (Work.Kernels.scale_pos τ),
    Real.rpow_add (by linarith : (0 : ℝ) < 1 + t), pow_add, pow_add]
  ring

/-- Powers multiply the exponents. -/
lemma pow {p k : ℕ} {F : ℍ → ℍ → ℂ} (hF : BdE p k F) (n : ℕ) :
    BdE (p * n) (k * n) (fun τ z => F τ z ^ n) := by
  induction n with
  | zero => simpa only [mul_zero, pow_zero] using (one : BdE 0 0 (fun _ _ => (1 : ℂ)))
  | succ n ih =>
      have h : BdE (p * n + p) (k * n + k) (fun τ z => F τ z ^ n * F τ z) := mul ih hF
      rw [show p * n + p = p * (n + 1) by ring,
        show k * n + k = k * (n + 1) by ring] at h
      simpa only [pow_succ] using h

/-- Lowering the `q`-exponent (weaker statement). -/
lemma mono_e {p p' k : ℕ} {F : ℍ → ℍ → ℂ} (h : BdE p k F) (hpp' : p' ≤ p) : BdE p' k F := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht ha hb' hzt => ?_⟩
  refine le_trans (hb τ z t hτ ht ha hb' hzt) ?_
  have hQ0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  have hQ1 : ‖Work.Kernels.qParamFun τ‖ ≤ 1 := q_le_one hτ
  have hle : ‖Work.Kernels.qParamFun τ‖ ^ p ≤ ‖Work.Kernels.qParamFun τ‖ ^ p' :=
    pow_le_pow_of_le_one hQ0 hQ1 hpp'
  have hT1 : (1 : ℝ) ≤ 1 + t := one_le_T hτ ht
  have hR0 : (0 : ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg (le_trans zero_le_one hT1) M
  have hS0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N := Snn τ N
  have hE0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ ^ k := pow_nonneg (norm_nonneg _) k
  calc C * ‖Work.Kernels.qParamFun τ‖ ^ p * ‖Work.Residues.Ept z‖ ^ k
        * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
      = (C * ‖Work.Residues.Ept z‖ ^ k * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
          * ‖Work.Kernels.qParamFun τ‖ ^ p := by ring
    _ ≤ (C * ‖Work.Residues.Ept z‖ ^ k * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
          * ‖Work.Kernels.qParamFun τ‖ ^ p' :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = C * ‖Work.Kernels.qParamFun τ‖ ^ p' * ‖Work.Residues.Ept z‖ ^ k
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by ring

/-- Lowering the `Ept`-exponent (weaker statement). -/
lemma mono_k {p k k' : ℕ} {F : ℍ → ℍ → ℂ} (h : BdE p k F) (hkk' : k' ≤ k) : BdE p k' F := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht ha hb' hzt => ?_⟩
  refine le_trans (hb τ z t hτ ht ha hb' hzt) ?_
  have hE0 : (0 : ℝ) ≤ ‖Work.Residues.Ept z‖ := norm_nonneg _
  have hE1 : ‖Work.Residues.Ept z‖ ≤ 1 := E_le_one hτ ht hzt
  have hle : ‖Work.Residues.Ept z‖ ^ k ≤ ‖Work.Residues.Ept z‖ ^ k' :=
    pow_le_pow_of_le_one hE0 hE1 hkk'
  have hT1 : (1 : ℝ) ≤ 1 + t := one_le_T hτ ht
  have hR0 : (0 : ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg (le_trans zero_le_one hT1) M
  have hS0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N := Snn τ N
  have hQ0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ ^ p := pow_nonneg (norm_nonneg _) p
  calc C * ‖Work.Kernels.qParamFun τ‖ ^ p * ‖Work.Residues.Ept z‖ ^ k
        * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
      = (C * ‖Work.Kernels.qParamFun τ‖ ^ p * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
          * ‖Work.Residues.Ept z‖ ^ k := by ring
    _ ≤ (C * ‖Work.Kernels.qParamFun τ‖ ^ p * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M)
          * ‖Work.Residues.Ept z‖ ^ k' :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = C * ‖Work.Kernels.qParamFun τ‖ ^ p * ‖Work.Residues.Ept z‖ ^ k'
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by ring

/-- Invariance under pointwise equality on the strip. -/
lemma congr_on {p k : ℕ} {F G : ℍ → ℍ → ℂ} (h : BdE p k F)
    (hFG : ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t → -1 ≤ z.re →
      z.re ≤ 2 → z.im = t → F τ z = G τ z) : BdE p k G := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  exact ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht ha hb' hzt => by
    rw [← hFG τ z t hτ ht ha hb' hzt]; exact hb τ z t hτ ht ha hb' hzt⟩

end BdE


/-! ## The `q`-power / `Ept`-power trade

On the funnel strip (`Funnel τ`, `t ≥ τ.im + 1`, `z.im = t`), `‖q(τ)‖ = e^{-2πτ.im}` and
`‖Ept z‖ = e^{-πt}`.  Hence `‖q(τ)‖^e‖Ept z‖^k ≤ ‖q(τ)‖³‖Ept z‖²` as soon as `k ≥ 2` and
`2e + k ≥ 8`: the exponent difference is `π((2e+k-8)τ.im + (k-2)(t-τ.im-1)) ≥ 0`. -/
lemma qpow_Ept_trade {τ z : ℍ} {t : ℝ} (hτ : Work.Asymptotics.Funnel τ) (ht : τ.im + 1 ≤ t)
    (hzt : z.im = t) {e k : ℕ} (hk : 2 ≤ k) (he : 8 ≤ 2 * e + k) :
    ‖Work.Kernels.qParamFun τ‖ ^ e * ‖Work.Residues.Ept z‖ ^ k
      ≤ ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2 := by
  have hL : ‖Work.Kernels.qParamFun τ‖ ^ e * ‖Work.Residues.Ept z‖ ^ k
      = Real.exp (-(2 * Real.pi * (e : ℝ) * τ.im) - Real.pi * (k : ℝ) * t) := by
    simp only [Work.Asymptotics.norm_qParamFun, Work.Residues.norm_Ept, hzt,
      ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hR : ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
      = Real.exp (-(2 * Real.pi * 3 * τ.im) - Real.pi * 2 * t) := by
    simp only [Work.Asymptotics.norm_qParamFun, Work.Residues.norm_Ept, hzt,
      ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hL, hR]
  apply Real.exp_le_exp.mpr
  have hIm : (0 : ℝ) ≤ τ.im := le_of_lt τ.im_pos
  have he' : (8 : ℝ) ≤ 2 * (e : ℝ) + (k : ℝ) := by exact_mod_cast he
  have hk' : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hA : 0 ≤ (2 * (e : ℝ) + (k : ℝ) - 8) * τ.im := mul_nonneg (by linarith) hIm
  have hB : 0 ≤ ((k : ℝ) - 2) * (t - τ.im - 1) :=
    mul_nonneg (by linarith) (by linarith)
  have hC : 0 ≤ (k : ℝ) - 2 := by linarith
  have hsum : 0 ≤ (2 * (e : ℝ) + (k : ℝ) - 8) * τ.im
      + ((k : ℝ) - 2) * (t - τ.im - 1) + ((k : ℝ) - 2) := by linarith
  have hgoal0 : 0 ≤ (2 * (e : ℝ) - 6) * τ.im + ((k : ℝ) - 2) * t := by
    convert hsum using 1
    ring
  have hmain : 0 ≤ Real.pi * ((2 * (e : ℝ) - 6) * τ.im + ((k : ℝ) - 2) * t) :=
    mul_nonneg Real.pi_pos.le hgoal0
  rw [show -(2 * Real.pi * (e : ℝ) * τ.im) - Real.pi * (k : ℝ) * t
      = -(2 * Real.pi * 3 * τ.im) - Real.pi * 2 * t
        - Real.pi * ((2 * (e : ℝ) - 6) * τ.im + ((k : ℝ) - 2) * t) from by ring]
  linarith

namespace BdE

/-- **The finishing step.**  A `BdE e k` bound with `k ≥ 2` and `2e + k ≥ 8` upgrades to the
target shape `C‖q(τ)‖³‖Ept z‖²(scale τ)^N(1+t)^M`. -/
lemma finish {e k : ℕ} {F : ℍ → ℍ → ℂ} (h : BdE e k F) (hk : 2 ≤ k) (he : 8 ≤ 2 * e + k) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : ℍ) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t → -1 ≤ z.re → z.re ≤ 2 →
        z.im = t → ‖F τ z‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3
          * ‖Work.Residues.Ept z‖ ^ 2 * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := h
  refine ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht ha hb' hzt => ?_⟩
  refine le_trans (hb τ z t hτ ht ha hb' hzt) ?_
  have hkey := qpow_Ept_trade hτ ht hzt hk he
  have hT1 : (1 : ℝ) ≤ 1 + t := one_le_T hτ ht
  have hS0 : (0 : ℝ) ≤ (Work.Kernels.scale τ) ^ N := Snn τ N
  have hR0 : (0 : ℝ) ≤ (1 + t) ^ M := Real.rpow_nonneg (le_trans zero_le_one hT1) M
  calc C * ‖Work.Kernels.qParamFun τ‖ ^ e * ‖Work.Residues.Ept z‖ ^ k
        * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M
      = C * (‖Work.Kernels.qParamFun τ‖ ^ e * ‖Work.Residues.Ept z‖ ^ k)
          * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ M) := by ring
    _ ≤ C * (‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2)
          * ((Work.Kernels.scale τ) ^ N * (1 + t) ^ M) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkey hC.le) (by positivity)
    _ = C * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
          * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M := by ring

/-- A `τ`-only estimate is a `BdE` estimate with `k = 0`. -/
lemma ofTau {p : ℕ} {f : ℍ → ℂ} {C N : ℝ} (hC : 0 < C) (hN : 0 ≤ N)
    (h : ∀ τ : ℍ, Work.Asymptotics.Funnel τ →
      ‖f τ‖ ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ p * (Work.Kernels.scale τ) ^ N) :
    BdE p 0 (fun τ _ => f τ) :=
  ⟨C, N, 0, hC, hN, le_rfl, fun τ z t hτ ht ha hb hzt => by
    have h' := h τ hτ
    simpa only [pow_zero, Real.rpow_zero, mul_one] using h'⟩

/-- A `z`-only estimate (uniform for `z.im ≥ 1`) is a `BdE` estimate with `e = k = 0`. -/
lemma ofZ {f : ℍ → ℂ} {C : ℝ} (hC : 0 < C) (h : ∀ z : ℍ, 1 ≤ z.im → ‖f z‖ ≤ C) :
    BdE 0 0 (fun _ z => f z) :=
  ⟨C, 0, 0, hC, le_rfl, le_rfl, fun τ z t hτ ht ha hb hzt => by
    have h' := h z (by rw [hzt]; linarith [hτ.2, ht])
    simpa only [pow_zero, Real.rpow_zero, mul_one, one_mul] using h'⟩

end BdE

/-! ## The three glued deviation bounds -/

/-- **`dE4z z = O(‖q(z)‖³)` on `z.im ≥ 3`** (threshold removed). -/
theorem exists_dE4z_bound_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 3 ≤ z.im →
      ‖Work.Asymptotics.KhatE1.dE4z z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨T4, C4, hT4, hC4, hb4⟩ := Work.Asymptotics.KhatE1.exists_dE4z_bound
  obtain ⟨CB, hCB, hBb⟩ := Work.Asymptotics.E4Fun_bound
  refine ⟨max C4 ((CB + 2401) * Real.exp (6 * Real.pi * T4)),
    lt_of_lt_of_le hC4 (le_max_left _ _), fun z hz => ?_⟩
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz]
  have hZ : ‖Work.Asymptotics.KhatE1.E4Ztr z‖ ≤ 2401 := by
    rw [Work.Asymptotics.KhatE1.E4Ztr]
    have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
    calc ‖1 + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2‖
        ≤ ‖1 + 240 * Work.Kernels.qParamFun z‖ + ‖2160 * Work.Kernels.qParamFun z ^ 2‖ :=
          norm_add_le _ _
      _ ≤ (1 + 240 * ‖Work.Kernels.qParamFun z‖) + 2160 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
          refine add_le_add ?_ ?_
          · calc ‖1 + 240 * Work.Kernels.qParamFun z‖
                ≤ ‖(1 : ℂ)‖ + ‖240 * Work.Kernels.qParamFun z‖ := norm_add_le _ _
              _ = 1 + 240 * ‖Work.Kernels.qParamFun z‖ := by
                  rw [norm_one, norm_mul]; norm_num
          · rw [norm_mul, norm_pow]; norm_num
      _ ≤ 2401 := by nlinarith [hq1, hq0]
  by_cases hT : T4 ≤ z.im
  · exact le_trans (hb4 z hT)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hE4 : ‖Work.Kernels.E4Fun z‖ ≤ CB := hBb z (by linarith)
    have hd : ‖Work.Asymptotics.KhatE1.dE4z z‖ ≤ CB + 2401 := by
      have h1 : ‖Work.Asymptotics.KhatE1.dE4z z‖
          ≤ ‖Work.Kernels.E4Fun z‖ + ‖Work.Asymptotics.KhatE1.E4Ztr z‖ := by
        rw [Work.Asymptotics.KhatE1.dE4z]
        exact norm_sub_le _ _
      linarith
    have hqpow : Real.exp (-(6 * Real.pi * T4)) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by
      have h1 : ‖Work.Kernels.qParamFun z‖ ^ 3 = Real.exp (-(6 * Real.pi * z.im)) := by
        rw [Work.Asymptotics.norm_qParamFun, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [h1]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hT])
    have hE : Real.exp (6 * Real.pi * T4) * Real.exp (-(6 * Real.pi * T4)) = 1 := by
      rw [← Real.exp_add, show 6 * Real.pi * T4 + -(6 * Real.pi * T4) = 0 by ring, Real.exp_zero]
    have hmain : CB + 2401 ≤ (CB + 2401) * Real.exp (6 * Real.pi * T4) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
      calc CB + 2401 = (CB + 2401) * (Real.exp (6 * Real.pi * T4) * Real.exp (-(6 * Real.pi * T4))) := by
            rw [hE, mul_one]
        _ = (CB + 2401) * Real.exp (6 * Real.pi * T4) * Real.exp (-(6 * Real.pi * T4)) := by ring
        _ ≤ (CB + 2401) * Real.exp (6 * Real.pi * T4) * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
            mul_le_mul_of_nonneg_left hqpow (by positivity)
    refine le_trans hd (le_trans hmain ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- **`dE2z z = O(‖q(z)‖³)` on `z.im ≥ 3`** (threshold removed). -/
theorem exists_dE2z_bound_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 3 ≤ z.im →
      ‖Work.Asymptotics.KhatE1.dE2z z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
  obtain ⟨T2, C2, hT2, hC2, hb2⟩ := Work.Asymptotics.KhatE1.exists_dE2z_bound
  obtain ⟨CB, hCB, hBb⟩ := Work.Asymptotics.E2Fun_bound
  refine ⟨max C2 ((CB + 97) * Real.exp (6 * Real.pi * T2)),
    lt_of_lt_of_le hC2 (le_max_left _ _), fun z hz => ?_⟩
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz]
  have hZ : ‖Work.Asymptotics.KhatE1.E2Ztr z‖ ≤ 97 := by
    rw [Work.Asymptotics.KhatE1.E2Ztr]
    have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
    calc ‖1 - 24 * Work.Kernels.qParamFun z - 72 * Work.Kernels.qParamFun z ^ 2‖
        ≤ ‖1 - 24 * Work.Kernels.qParamFun z‖ + ‖72 * Work.Kernels.qParamFun z ^ 2‖ :=
          norm_sub_le _ _
      _ ≤ (1 + 24 * ‖Work.Kernels.qParamFun z‖) + 72 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
          refine add_le_add ?_ ?_
          · calc ‖1 - 24 * Work.Kernels.qParamFun z‖
                ≤ ‖(1 : ℂ)‖ + ‖24 * Work.Kernels.qParamFun z‖ := norm_sub_le _ _
              _ = 1 + 24 * ‖Work.Kernels.qParamFun z‖ := by
                  rw [norm_one, norm_mul]; norm_num
          · rw [norm_mul, norm_pow]; norm_num
      _ ≤ 97 := by nlinarith [hq1, hq0]
  by_cases hT : T2 ≤ z.im
  · exact le_trans (hb2 z hT)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hE2 : ‖Work.Kernels.E2Fun z‖ ≤ CB := hBb z (by linarith)
    have hd : ‖Work.Asymptotics.KhatE1.dE2z z‖ ≤ CB + 97 := by
      have h1 : ‖Work.Asymptotics.KhatE1.dE2z z‖
          ≤ ‖Work.Kernels.E2Fun z‖ + ‖Work.Asymptotics.KhatE1.E2Ztr z‖ := by
        rw [Work.Asymptotics.KhatE1.dE2z]
        exact norm_sub_le _ _
      linarith
    have hqpow : Real.exp (-(6 * Real.pi * T2)) ≤ ‖Work.Kernels.qParamFun z‖ ^ 3 := by
      have h1 : ‖Work.Kernels.qParamFun z‖ ^ 3 = Real.exp (-(6 * Real.pi * z.im)) := by
        rw [Work.Asymptotics.norm_qParamFun, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [h1]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hT])
    have hE : Real.exp (6 * Real.pi * T2) * Real.exp (-(6 * Real.pi * T2)) = 1 := by
      rw [← Real.exp_add, show 6 * Real.pi * T2 + -(6 * Real.pi * T2) = 0 by ring, Real.exp_zero]
    have hmain : CB + 97 ≤ (CB + 97) * Real.exp (6 * Real.pi * T2) * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
      calc CB + 97 = (CB + 97) * (Real.exp (6 * Real.pi * T2) * Real.exp (-(6 * Real.pi * T2))) := by
            rw [hE, mul_one]
        _ = (CB + 97) * Real.exp (6 * Real.pi * T2) * Real.exp (-(6 * Real.pi * T2)) := by ring
        _ ≤ (CB + 97) * Real.exp (6 * Real.pi * T2) * ‖Work.Kernels.qParamFun z‖ ^ 3 :=
            mul_le_mul_of_nonneg_left hqpow (by positivity)
    refine le_trans hd (le_trans hmain ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-- **`dDz z = O(‖q(z)‖⁴)` on `z.im ≥ 3`** (threshold removed). -/
theorem exists_dDz_bound_strip :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℍ, 3 ≤ z.im →
      ‖Work.Asymptotics.KhatE1.dDz z‖ ≤ C * ‖Work.Kernels.qParamFun z‖ ^ 4 := by
  obtain ⟨Td, Cd, hTd, hCd, hbd⟩ := Work.Asymptotics.KhatE1.exists_dDz_bound
  obtain ⟨CΔ, hCΔ, hΔb⟩ := Work.Asymptotics.DeltaFun_upper
  refine ⟨max Cd ((CΔ + 277) * Real.exp (8 * Real.pi * Td)),
    lt_of_lt_of_le hCd (le_max_left _ _), fun z hz => ?_⟩
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz]
  have hZ : ‖Work.Asymptotics.KhatE1.DeltaZtr z‖ ≤ 277 := by
    rw [Work.Asymptotics.KhatE1.DeltaZtr]
    have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
    calc ‖Work.Kernels.qParamFun z - 24 * Work.Kernels.qParamFun z ^ 2
          + 252 * Work.Kernels.qParamFun z ^ 3‖
        ≤ ‖Work.Kernels.qParamFun z - 24 * Work.Kernels.qParamFun z ^ 2‖
            + ‖252 * Work.Kernels.qParamFun z ^ 3‖ := norm_add_le _ _
      _ ≤ (‖Work.Kernels.qParamFun z‖ + 24 * ‖Work.Kernels.qParamFun z‖ ^ 2)
            + 252 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
          refine add_le_add ?_ ?_
          · calc ‖Work.Kernels.qParamFun z - 24 * Work.Kernels.qParamFun z ^ 2‖
                ≤ ‖Work.Kernels.qParamFun z‖ + ‖24 * Work.Kernels.qParamFun z ^ 2‖ :=
                  norm_sub_le _ _
              _ = ‖Work.Kernels.qParamFun z‖ + 24 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
                  rw [norm_mul, norm_pow]; norm_num
          · rw [norm_mul, norm_pow]; norm_num
      _ ≤ 277 := by nlinarith [hq1, hq0]
  by_cases hT : Td ≤ z.im
  · exact le_trans (hbd z hT)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · have hD : ‖Work.Kernels.DeltaFun z‖ ≤ CΔ := by
      have h := hΔb z (by linarith)
      have hq : ‖Work.Kernels.qParamFun z‖ ≤ 1 := hq1
      nlinarith [h, norm_nonneg (Work.Kernels.qParamFun z), hCΔ]
    have hd : ‖Work.Asymptotics.KhatE1.dDz z‖ ≤ CΔ + 277 := by
      have h1 : ‖Work.Asymptotics.KhatE1.dDz z‖
          ≤ ‖Work.Kernels.DeltaFun z‖ + ‖Work.Asymptotics.KhatE1.DeltaZtr z‖ := by
        rw [Work.Asymptotics.KhatE1.dDz]
        exact norm_sub_le _ _
      linarith
    have hqpow : Real.exp (-(8 * Real.pi * Td)) ≤ ‖Work.Kernels.qParamFun z‖ ^ 4 := by
      have h1 : ‖Work.Kernels.qParamFun z‖ ^ 4 = Real.exp (-(8 * Real.pi * z.im)) := by
        rw [Work.Asymptotics.norm_qParamFun, ← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      rw [h1]
      exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, hT])
    have hE : Real.exp (8 * Real.pi * Td) * Real.exp (-(8 * Real.pi * Td)) = 1 := by
      rw [← Real.exp_add, show 8 * Real.pi * Td + -(8 * Real.pi * Td) = 0 by ring, Real.exp_zero]
    have hmain : CΔ + 277 ≤ (CΔ + 277) * Real.exp (8 * Real.pi * Td) * ‖Work.Kernels.qParamFun z‖ ^ 4 := by
      calc CΔ + 277 = (CΔ + 277) * (Real.exp (8 * Real.pi * Td) * Real.exp (-(8 * Real.pi * Td))) := by
            rw [hE, mul_one]
        _ = (CΔ + 277) * Real.exp (8 * Real.pi * Td) * Real.exp (-(8 * Real.pi * Td)) := by ring
        _ ≤ (CΔ + 277) * Real.exp (8 * Real.pi * Td) * ‖Work.Kernels.qParamFun z‖ ^ 4 :=
            mul_le_mul_of_nonneg_left hqpow (by positivity)
    refine le_trans hd (le_trans hmain ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

/-! ## The atom instances -/

section Atoms

open Work.Asymptotics.KhatE1

/-- `E₄(τ)` is bounded on the funnel. -/
lemma bdE_E4 : BdE 0 0 (fun τ _ => Work.Kernels.E4Fun τ) := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.E4Fun_bound
  refine BdE.ofTau hC le_rfl (fun τ hτ => ?_)
  have h := hb τ (by linarith [hτ.2])
  simpa only [pow_zero, Real.rpow_zero, mul_one, one_mul] using h

/-- `E₆(τ)` is bounded on the funnel. -/
lemma bdE_E6 : BdE 0 0 (fun τ _ => Work.Kernels.E6Fun τ) := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.E6Fun_bound
  refine BdE.ofTau hC le_rfl (fun τ hτ => ?_)
  have h := hb τ (by linarith [hτ.2])
  simpa only [pow_zero, Real.rpow_zero, mul_one, one_mul] using h

/-- `E₂(τ)` is bounded on the funnel. -/
lemma bdE_E2 : BdE 0 0 (fun τ _ => Work.Kernels.E2Fun τ) := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.E2Fun_bound
  refine BdE.ofTau hC le_rfl (fun τ hτ => ?_)
  have h := hb τ (by linarith [hτ.2])
  simpa only [pow_zero, Real.rpow_zero, mul_one, one_mul] using h

/-- `‖Δ(τ)‖ ≤ 2‖q(τ)‖` on the funnel. -/
lemma bdE_Delta : BdE 1 0 (fun τ _ => Work.Kernels.DeltaFun τ) :=
  BdE.ofTau (C := 2) (N := 0) (by norm_num) le_rfl (fun τ hτ => by
    have h := Work.Asymptotics.DeltaFun_funnel_le τ hτ
    simpa only [pow_one, Real.rpow_zero, mul_one, one_mul] using h)

/-- `‖τ‖ ≤ scale τ`. -/
lemma bdE_tau : BdE 0 0 (fun τ _ => ((τ : ℍ) : ℂ)) :=
  BdE.ofTau (C := 1) (N := 1) (by norm_num) (by norm_num) (fun τ _ => by
    have h := Work.Kernels.coe_norm_le_scale τ
    simpa only [pow_zero, Real.rpow_one, mul_one, one_mul] using h)

/-- `φ₀(τ) = τE₂(τ) - 3i/π` is `O(scale τ)`. -/
lemma bdE_phi0 : BdE 0 0 (fun τ _ => Work.Kernels.phi0 τ) := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.E2Fun_bound
  refine BdE.ofTau (C := C + 3 / Real.pi + 1) (N := 1) (by positivity) (by norm_num)
    (fun τ hτ => ?_)
  have h2 := hb τ (by linarith [hτ.2])
  have hS : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have h3 : ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 3 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hmain : ‖Work.Kernels.phi0 τ‖ ≤ (C + 3 / Real.pi + 1) * Work.Kernels.scale τ := by
    rw [Work.Kernels.phi0]
    calc ‖(τ : ℂ) * Work.Kernels.E2Fun τ - 3 * Complex.I / (Real.pi : ℂ)‖
        ≤ ‖(τ : ℂ) * Work.Kernels.E2Fun τ‖ + ‖(3 : ℂ) * Complex.I / (Real.pi : ℂ)‖ :=
          norm_sub_le _ _
      _ ≤ Work.Kernels.scale τ * ‖Work.Kernels.E2Fun τ‖ + 3 / Real.pi := by
          rw [norm_mul, h3]
          have hle := Work.Kernels.coe_norm_le_scale τ
          have h0 : (0 : ℝ) ≤ ‖Work.Kernels.E2Fun τ‖ := norm_nonneg _
          nlinarith
      _ ≤ Work.Kernels.scale τ * C + 3 / Real.pi := by
          have := mul_le_mul_of_nonneg_left h2 (Work.Kernels.scale_pos τ).le
          linarith
      _ ≤ (C + 3 / Real.pi + 1) * Work.Kernels.scale τ := by
          have hs1 : (0 : ℝ) ≤ 3 / Real.pi := by positivity
          have h1 : 3 / Real.pi ≤ (3 / Real.pi) * Work.Kernels.scale τ := by
            calc 3 / Real.pi = (3 / Real.pi) * 1 := by ring
              _ ≤ (3 / Real.pi) * Work.Kernels.scale τ := mul_le_mul_of_nonneg_left hS hs1
          have hs0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_of_lt (Work.Kernels.scale_pos τ)
          nlinarith [h1, hs0]
  simpa only [pow_zero, Real.rpow_one, mul_one, one_mul] using hmain

/-- `φ₂(τ) = τE₂(τ)² - (6i/π)E₂(τ)` is `O(scale τ)`. -/
lemma bdE_phi2 : BdE 0 0 (fun τ _ => Work.Kernels.phi2 τ) := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.E2Fun_bound
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  refine BdE.ofTau (C := (C + 1) * (C + 1) + (6 / Real.pi) * (C + 1) + 1) (N := 1)
    (by positivity) (by norm_num) (fun τ hτ => ?_)
  have h2 := hb τ (by linarith [hτ.2])
  have hS : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have h6 : ‖(6 : ℂ) * Complex.I / (Real.pi : ℂ)‖ = 6 / Real.pi := by
    rw [norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hmain : ‖Work.Kernels.phi2 τ‖
      ≤ ((C + 1) * (C + 1) + (6 / Real.pi) * (C + 1) + 1) * Work.Kernels.scale τ := by
    rw [Work.Kernels.phi2]
    calc ‖(τ : ℂ) * Work.Kernels.E2Fun τ ^ 2 - (6 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun τ‖
        ≤ ‖(τ : ℂ) * Work.Kernels.E2Fun τ ^ 2‖
            + ‖(6 * Complex.I / (Real.pi : ℂ)) * Work.Kernels.E2Fun τ‖ := norm_sub_le _ _
      _ ≤ Work.Kernels.scale τ * (C * C) + (6 / Real.pi) * C := by
          refine add_le_add ?_ ?_
          · rw [norm_mul, norm_pow]
            have h22 : ‖Work.Kernels.E2Fun τ‖ ^ 2 ≤ C * C := by
              nlinarith [h2, norm_nonneg (Work.Kernels.E2Fun τ)]
            have hS' := (Work.Kernels.coe_norm_le_scale τ)
            nlinarith [hS', h22, norm_nonneg ((τ : ℍ) : ℂ), hC]
          · rw [norm_mul, h6]
            have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 6 / Real.pi)
            linarith
      _ ≤ ((C + 1) * (C + 1) + (6 / Real.pi) * (C + 1) + 1) * Work.Kernels.scale τ := by
          have hs0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_of_lt (Work.Kernels.scale_pos τ)
          have hp : (0 : ℝ) ≤ 6 / Real.pi := by positivity
          have hB : (6 / Real.pi) * C ≤ Work.Kernels.scale τ * ((6 / Real.pi) * C) :=
            le_mul_of_one_le_left (mul_nonneg hp hC.le) hS
          nlinarith [hB, hs0, hC, hp]
  simpa only [pow_zero, Real.rpow_one, mul_one, one_mul] using hmain

/-- `ψ₂, ψ₄` have moderate growth on the funnel. -/
lemma bdE_psi2 (ℓ : Work.Kernels.LogLambdaData) :
    BdE 0 0 (fun τ _ => Work.Kernels.psi2 ℓ τ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.psi_scale_funnel ℓ
  exact BdE.ofTau hC hN (fun τ hτ => by
    simpa only [pow_zero, mul_one] using (hb τ hτ).1)

lemma bdE_psi4 (ℓ : Work.Kernels.LogLambdaData) :
    BdE 0 0 (fun τ _ => Work.Kernels.psi4 ℓ τ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.psi_scale_funnel ℓ
  exact BdE.ofTau hC hN (fun τ hτ => by
    simpa only [pow_zero, mul_one] using (hb τ hτ).2)

/-- `E₁₄ = E₄²E₆` is bounded on the funnel. -/
lemma bdE_E14 : BdE 0 0 (fun τ _ => Work.Kernels.E14Fun τ) := by
  obtain ⟨C4, hC4, h4⟩ := Work.Asymptotics.E4Fun_bound
  obtain ⟨C6, hC6, h6⟩ := Work.Asymptotics.E6Fun_bound
  refine BdE.ofTau (C := C4 ^ 2 * C6) (N := 0) (by positivity) le_rfl (fun τ hτ => ?_)
  have h4' := h4 τ (by linarith [hτ.2])
  have h6' := h6 τ (by linarith [hτ.2])
  have h : ‖Work.Kernels.E14Fun τ‖ ≤ C4 ^ 2 * C6 := by
    rw [show Work.Kernels.E14Fun τ = Work.Kernels.E4Fun τ ^ 2 * Work.Kernels.E6Fun τ from rfl,
      norm_mul, norm_pow]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) h4' 2) h6' (norm_nonneg _) (by positivity)
  simpa only [pow_zero, Real.rpow_zero, mul_one] using h

/-- `KdevE2` is `O(‖q(τ)‖(scale τ)^N(1+t)^M)` on the strip. -/
lemma bdE_KdevE2 (ℓ : Work.Kernels.LogLambdaData) :
    BdE 1 0 (fun τ z => Work.Asymptotics.KhatE1.KdevE2 ℓ τ z) := by
  obtain ⟨C, N, M, hC, hN, hM, hb⟩ := Work.Asymptotics.KhatE1.KdevE2_strip_bound ℓ
  exact ⟨C, N, M, hC, hN, hM, fun τ z t hτ ht ha hb' hzt => by
    have h := hb τ z t hτ ht ha hb' hzt
    simpa only [pow_one, pow_zero, mul_one] using h⟩

/-- `R8p0JF = 24Δ·E1combo8` is `O(‖q(τ)‖²(scale τ)^N)`. -/
lemma bdE_R8p0JF (ℓ : Work.Kernels.LogLambdaData) :
    BdE 2 0 (fun τ _ => Work.Asymptotics.KhatE1.R8p0JF ℓ τ) := by
  obtain ⟨C, N, hC, hN, hb⟩ := Work.Asymptotics.KhatE1.E1combo8_bound ℓ
  refine BdE.ofTau (C := 48 * C) (N := N) (by positivity) hN (fun τ hτ => ?_)
  have h := hb τ hτ
  have heq : Work.Asymptotics.KhatE1.R8p0JF ℓ τ
      = 24 * Work.Kernels.DeltaFun τ * Work.Asymptotics.E1combo8 ℓ τ := by
    rw [← Work.Asymptotics.KhatE1.Delta_mul_R8p0 ℓ τ,
      Work.Asymptotics.KhatE1.R8_p0_eq_e1combo8 ℓ τ]
    ring
  have hD := Work.Asymptotics.DeltaFun_funnel_le τ hτ
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
  rw [heq, norm_mul, norm_mul, show ‖(24 : ℂ)‖ = 24 by norm_num]
  calc 24 * ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Asymptotics.E1combo8 ℓ τ‖
      ≤ 24 * (2 * ‖Work.Kernels.qParamFun τ‖)
          * (C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hD (by norm_num)) h
          (norm_nonneg _) (by positivity)
    _ = 48 * C * ‖Work.Kernels.qParamFun τ‖ ^ 2 * (Work.Kernels.scale τ) ^ N := by ring

/-- `br0 8 ℓ τ z = 3456E₄(τ)Xc ℓ z - 1728ψ₄(τ)` is `O((scale τ)^N(1+t)^M)`. -/
lemma bdE_br0 (ℓ : Work.Kernels.LogLambdaData) :
    BdE 0 0 (fun τ z => Work.Asymptotics.Compact.br0 8 ℓ τ z) := by
  have hc : Work.Asymptotics.Compact.cuspC ℓ = 4 * (Real.log 2 : ℂ) :=
    Work.Asymptotics.CuspL_eq ℓ
  obtain ⟨C4, hC4, h4⟩ := Work.Asymptotics.E4Fun_bound
  obtain ⟨Cψ, Nψ, hCψ, hNψ, hψ⟩ := Work.Asymptotics.psi_scale_funnel ℓ
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  refine ⟨3456 * C4 * (2 * Real.pi + 4 * Real.log 2) + 1728 * Cψ, Nψ, 1,
    by positivity, hNψ, by norm_num, fun τ z t hτ ht ha hb hzt => ?_⟩
  have hE4 := h4 τ (by linarith [hτ.2])
  have hψ := (hψ τ hτ).2
  have hS : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
  have hT : (1 : ℝ) ≤ 1 + t := BdE.one_le_T hτ ht
  have hz := Work.Asymptotics.KhatE1.kdevA4_norm_z_le z t ha hb hzt
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have h4n : (0 : ℝ) ≤ 4 * Real.log 2 := by positivity
  have hXc : ‖Work.Asymptotics.Compact.Xc ℓ z‖ ≤ (2 * Real.pi + 4 * Real.log 2) * (1 + t) := by
    have hgoal : Work.Asymptotics.Compact.Xc ℓ z
        = (Real.pi : ℂ) * Complex.I * (z : ℂ) + 4 * (Real.log 2 : ℂ) := by
      rw [Work.Asymptotics.Compact.Xc, hc]
    rw [hgoal]
    calc ‖(Real.pi : ℂ) * Complex.I * (z : ℂ) + 4 * (Real.log 2 : ℂ)‖
        ≤ ‖(Real.pi : ℂ) * Complex.I * (z : ℂ)‖ + ‖(4 : ℂ) * (Real.log 2 : ℂ)‖ :=
          norm_add_le _ _
      _ = Real.pi * ‖(z : ℂ)‖ + 4 * Real.log 2 := by
          rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos hπ, norm_mul, Complex.norm_ofNat, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg hlog0]
      _ ≤ Real.pi * (2 * (1 + t)) + 4 * Real.log 2 := by
          have := mul_le_mul_of_nonneg_left hz hπ.le
          linarith
      _ ≤ (2 * Real.pi + 4 * Real.log 2) * (1 + t) := by
          have ht0 : (0 : ℝ) ≤ t := by linarith [hτ.2, ht]
          nlinarith [h4n, hπ, ht0]
  have hbr : ‖Work.Asymptotics.Compact.br0 8 ℓ τ z‖
      ≤ 3456 * C4 * (2 * Real.pi + 4 * Real.log 2) * (1 + t)
        + 1728 * Cψ * (Work.Kernels.scale τ) ^ Nψ := by
    rw [Work.Asymptotics.KhatE1.br0_eight_eq ℓ τ z]
    calc ‖3456 * Work.Kernels.E4Fun τ * Work.Asymptotics.Compact.Xc ℓ z
          - 1728 * Work.Kernels.psi4 ℓ τ‖
        ≤ ‖3456 * Work.Kernels.E4Fun τ * Work.Asymptotics.Compact.Xc ℓ z‖
            + ‖1728 * Work.Kernels.psi4 ℓ τ‖ := norm_sub_le _ _
      _ = 3456 * ‖Work.Kernels.E4Fun τ‖ * ‖Work.Asymptotics.Compact.Xc ℓ z‖
            + 1728 * ‖Work.Kernels.psi4 ℓ τ‖ := by
          rw [norm_mul, norm_mul, norm_mul, show ‖(3456 : ℂ)‖ = 3456 by norm_num,
            show ‖(1728 : ℂ)‖ = 1728 by norm_num]
      _ ≤ 3456 * C4 * ((2 * Real.pi + 4 * Real.log 2) * (1 + t))
            + 1728 * (Cψ * (Work.Kernels.scale τ) ^ Nψ) := by
          refine add_le_add ?_ ?_
          · refine mul_le_mul (mul_le_mul_of_nonneg_left hE4 (by norm_num)) hXc (norm_nonneg _)
              (by positivity)
          · exact mul_le_mul_of_nonneg_left hψ (by norm_num)
      _ = 3456 * C4 * (2 * Real.pi + 4 * Real.log 2) * (1 + t)
            + 1728 * Cψ * (Work.Kernels.scale τ) ^ Nψ := by ring
  have hS1 : (1 : ℝ) ≤ (Work.Kernels.scale τ) ^ Nψ := Real.one_le_rpow hS hNψ
  have hA0 : (0 : ℝ) ≤ 3456 * C4 * (2 * Real.pi + 4 * Real.log 2) := by positivity
  have hB0 : (0 : ℝ) ≤ 1728 * Cψ := by positivity
  refine le_trans hbr ?_
  calc 3456 * C4 * (2 * Real.pi + 4 * Real.log 2) * (1 + t)
        + 1728 * Cψ * (Work.Kernels.scale τ) ^ Nψ
      ≤ (3456 * C4 * (2 * Real.pi + 4 * Real.log 2) + 1728 * Cψ)
          * (Work.Kernels.scale τ) ^ Nψ * (1 + t) := by
        have h1 : 3456 * C4 * (2 * Real.pi + 4 * Real.log 2) * (1 + t)
            ≤ 3456 * C4 * (2 * Real.pi + 4 * Real.log 2)
              * (Work.Kernels.scale τ) ^ Nψ * (1 + t) := by
          have h := mul_le_mul_of_nonneg_left hS1 hA0
          have hT0 : (0 : ℝ) ≤ 1 + t := by linarith
          calc 3456 * C4 * (2 * Real.pi + 4 * Real.log 2) * (1 + t)
              = (3456 * C4 * (2 * Real.pi + 4 * Real.log 2) * 1) * (1 + t) := by ring
            _ ≤ (3456 * C4 * (2 * Real.pi + 4 * Real.log 2)
                  * (Work.Kernels.scale τ) ^ Nψ) * (1 + t) :=
                mul_le_mul_of_nonneg_right h hT0
        have h2 : 1728 * Cψ * (Work.Kernels.scale τ) ^ Nψ
            ≤ 1728 * Cψ * (Work.Kernels.scale τ) ^ Nψ * (1 + t) := by
          calc 1728 * Cψ * (Work.Kernels.scale τ) ^ Nψ
              = (1728 * Cψ * (Work.Kernels.scale τ) ^ Nψ) * 1 := by ring
            _ ≤ (1728 * Cψ * (Work.Kernels.scale τ) ^ Nψ) * (1 + t) :=
                mul_le_mul_of_nonneg_left hT (by positivity)
        calc 3456 * C4 * (2 * Real.pi + 4 * Real.log 2) * (1 + t)
              + 1728 * Cψ * (Work.Kernels.scale τ) ^ Nψ
            ≤ 3456 * C4 * (2 * Real.pi + 4 * Real.log 2)
                * (Work.Kernels.scale τ) ^ Nψ * (1 + t)
              + 1728 * Cψ * (Work.Kernels.scale τ) ^ Nψ * (1 + t) := add_le_add h1 h2
          _ = (3456 * C4 * (2 * Real.pi + 4 * Real.log 2) + 1728 * Cψ)
                * (Work.Kernels.scale τ) ^ Nψ * (1 + t) := by ring
    _ = (3456 * C4 * (2 * Real.pi + 4 * Real.log 2) + 1728 * Cψ)
          * (Work.Kernels.scale τ) ^ Nψ * (1 + t) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
    _ = (3456 * C4 * (2 * Real.pi + 4 * Real.log 2) + 1728 * Cψ)
          * ‖Work.Kernels.qParamFun τ‖ ^ 0 * ‖Work.Residues.Ept z‖ ^ 0
          * (Work.Kernels.scale τ) ^ Nψ * (1 + t) ^ (1 : ℝ) := by
        simp only [pow_zero, Real.rpow_zero, Real.rpow_one, mul_one, one_mul]

/-! ### The `z`-atoms -/

lemma bdE_z : BdE 0 0 (fun _ (z : ℍ) => ((z : ℍ) : ℂ)) :=
  ⟨2, 0, 1, by norm_num, le_rfl, by norm_num, fun τ z t hτ ht ha hb hzt => by
    have h := Work.Asymptotics.KhatE1.kdevA4_norm_z_le z t ha hb hzt
    simpa only [pow_zero, Real.rpow_zero, Real.rpow_one, mul_one, one_mul] using h⟩

lemma bdE_Ept : BdE 0 1 (fun _ z => Work.Residues.Ept z) :=
  ⟨1, 0, 0, one_pos, le_rfl, le_rfl, fun τ z t _ _ _ _ _ => by
    simp only [pow_zero, Real.rpow_zero, mul_one, one_mul, pow_one]
    exact le_rfl⟩

lemma bdE_E4Fz : BdE 0 0 (fun _ z => Work.Kernels.E4Fun z) := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.E4Fun_bound
  exact BdE.ofZ hC (fun z hz => hb z hz)

lemma bdE_E2Fz : BdE 0 0 (fun _ z => Work.Kernels.E2Fun z) := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.E2Fun_bound
  exact BdE.ofZ hC (fun z hz => hb z hz)

lemma bdE_E6Fz : BdE 0 0 (fun _ z => Work.Kernels.E6Fun z) := by
  obtain ⟨C, hC, hb⟩ := Work.Asymptotics.E6Fun_bound
  exact BdE.ofZ hC (fun z hz => hb z hz)

lemma bdE_E4Ztr : BdE 0 0 (fun _ z => Work.Asymptotics.KhatE1.E4Ztr z) := by
  refine BdE.ofZ (C := 2401) (by norm_num) (fun z hz => ?_)
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz]
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  rw [Work.Asymptotics.KhatE1.E4Ztr]
  calc ‖1 + 240 * Work.Kernels.qParamFun z + 2160 * Work.Kernels.qParamFun z ^ 2‖
      ≤ ‖1 + 240 * Work.Kernels.qParamFun z‖ + ‖2160 * Work.Kernels.qParamFun z ^ 2‖ :=
        norm_add_le _ _
    _ ≤ (1 + 240 * ‖Work.Kernels.qParamFun z‖) + 2160 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
        refine add_le_add ?_ ?_
        · calc ‖1 + 240 * Work.Kernels.qParamFun z‖
              ≤ ‖(1 : ℂ)‖ + ‖240 * Work.Kernels.qParamFun z‖ := norm_add_le _ _
            _ = 1 + 240 * ‖Work.Kernels.qParamFun z‖ := by rw [norm_one, norm_mul]; norm_num
        · rw [norm_mul, norm_pow]; norm_num
    _ ≤ 2401 := by nlinarith [hq1, hq0]

lemma bdE_E2Ztr : BdE 0 0 (fun _ z => Work.Asymptotics.KhatE1.E2Ztr z) := by
  refine BdE.ofZ (C := 97) (by norm_num) (fun z hz => ?_)
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hz]
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  rw [Work.Asymptotics.KhatE1.E2Ztr]
  calc ‖1 - 24 * Work.Kernels.qParamFun z - 72 * Work.Kernels.qParamFun z ^ 2‖
      ≤ ‖1 - 24 * Work.Kernels.qParamFun z‖ + ‖72 * Work.Kernels.qParamFun z ^ 2‖ :=
        norm_sub_le _ _
    _ ≤ (1 + 24 * ‖Work.Kernels.qParamFun z‖) + 72 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
        refine add_le_add ?_ ?_
        · calc ‖1 - 24 * Work.Kernels.qParamFun z‖
              ≤ ‖(1 : ℂ)‖ + ‖24 * Work.Kernels.qParamFun z‖ := norm_sub_le _ _
            _ = 1 + 24 * ‖Work.Kernels.qParamFun z‖ := by rw [norm_one, norm_mul]; norm_num
        · rw [norm_mul, norm_pow]; norm_num
    _ ≤ 97 := by nlinarith [hq1, hq0]

lemma bdE_DeltaZtr : BdE 0 2 (fun _ z => Work.Asymptotics.KhatE1.DeltaZtr z) := by
  refine ⟨277, 0, 0, by norm_num, le_rfl, le_rfl, fun τ z t hτ ht ha hb hzt => ?_⟩
  have hq1 : ‖Work.Kernels.qParamFun z‖ ≤ 1 := by
    rw [Work.Asymptotics.norm_qParamFun, Real.exp_le_one_iff]
    nlinarith [Real.pi_pos, hτ.2, ht, hzt]
  have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun z‖ := norm_nonneg _
  have hE : ‖Work.Residues.Ept z‖ ^ 2 = ‖Work.Kernels.qParamFun z‖ := by
    rw [Work.Asymptotics.norm_qParamFun, Work.Residues.norm_Ept, hzt, sq, ← Real.exp_add]
    congr 1; ring
  calc ‖Work.Asymptotics.KhatE1.DeltaZtr z‖
      ≤ ‖Work.Kernels.qParamFun z - 24 * Work.Kernels.qParamFun z ^ 2‖
          + ‖252 * Work.Kernels.qParamFun z ^ 3‖ := norm_add_le _ _
    _ ≤ (‖Work.Kernels.qParamFun z‖ + 24 * ‖Work.Kernels.qParamFun z‖ ^ 2)
          + 252 * ‖Work.Kernels.qParamFun z‖ ^ 3 := by
        refine add_le_add ?_ ?_
        · calc ‖Work.Kernels.qParamFun z - 24 * Work.Kernels.qParamFun z ^ 2‖
              ≤ ‖Work.Kernels.qParamFun z‖ + ‖24 * Work.Kernels.qParamFun z ^ 2‖ :=
                norm_sub_le _ _
            _ = ‖Work.Kernels.qParamFun z‖ + 24 * ‖Work.Kernels.qParamFun z‖ ^ 2 := by
                rw [norm_mul, norm_pow]; norm_num
        · rw [norm_mul, norm_pow]; norm_num
    _ ≤ 277 * ‖Work.Kernels.qParamFun τ‖ ^ 0 * ‖Work.Residues.Ept z‖ ^ 2
          * (Work.Kernels.scale τ) ^ (0 : ℝ) * (1 + t) ^ (0 : ℝ) := by
        have hcube : ‖Work.Kernels.qParamFun z‖ ^ 3 ≤ ‖Work.Kernels.qParamFun z‖ := by
          calc ‖Work.Kernels.qParamFun z‖ ^ 3
              = ‖Work.Kernels.qParamFun z‖ ^ 2 * ‖Work.Kernels.qParamFun z‖ := by ring
            _ ≤ 1 * ‖Work.Kernels.qParamFun z‖ :=
                mul_le_mul_of_nonneg_right (by nlinarith [hq1, hq0]) hq0
            _ = ‖Work.Kernels.qParamFun z‖ := one_mul _
        simp only [hE, pow_zero, Real.rpow_zero, mul_one, one_mul]
        nlinarith [hq1, hq0, hcube]

lemma bdE_Gt : BdE 0 0 (fun _ z => Work.Kernels.TildeFacts.Gt z) := by
  have h : BdE 0 0 (fun _ z => ((z : ℍ) : ℂ) * Work.Kernels.E2Fun z
      - 6 * Complex.I / (Real.pi : ℂ)) :=
    BdE.sub (BdE.mul bdE_z bdE_E2Fz) (BdE.const (6 * Complex.I / (Real.pi : ℂ)))
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  show ((z : ℍ) : ℂ) * Work.Kernels.E2Fun z - 6 * Complex.I / (Real.pi : ℂ)
    = Work.Kernels.TildeFacts.Gt z
  rw [Work.Kernels.TildeFacts.Gt]

lemma bdE_GtTr : BdE 0 0 (fun _ z => Work.Asymptotics.KhatE1.GtTr z) := by
  have h : BdE 0 0 (fun _ z => ((z : ℍ) : ℂ) * Work.Asymptotics.KhatE1.E2Ztr z
      - 6 * Complex.I / (Real.pi : ℂ)) :=
    BdE.sub (BdE.mul bdE_z bdE_E2Ztr) (BdE.const (6 * Complex.I / (Real.pi : ℂ)))
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  show ((z : ℍ) : ℂ) * Work.Asymptotics.KhatE1.E2Ztr z - 6 * Complex.I / (Real.pi : ℂ)
    = Work.Asymptotics.KhatE1.GtTr z
  rw [Work.Asymptotics.KhatE1.GtTr]

lemma bdE_phit1Ztr : BdE 0 0 (fun _ z => Work.Asymptotics.KhatE1.phit1Ztr z) := by
  have h : BdE 0 0 (fun _ z => ((z : ℍ) : ℂ) * Work.Asymptotics.KhatE1.GtTr z) :=
    BdE.mul bdE_z bdE_GtTr
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  show ((z : ℍ) : ℂ) * Work.Asymptotics.KhatE1.GtTr z = Work.Asymptotics.KhatE1.phit1Ztr z
  rw [Work.Asymptotics.KhatE1.phit1Ztr]

lemma bdE_phit2Ztr : BdE 0 0 (fun _ z => Work.Asymptotics.KhatE1.phit2Ztr z) := by
  have h : BdE 0 0 (fun _ z => Work.Asymptotics.KhatE1.GtTr z ^ 2) := by
    simpa using BdE.pow bdE_GtTr 2
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  show Work.Asymptotics.KhatE1.GtTr z ^ 2 = Work.Asymptotics.KhatE1.phit2Ztr z
  rw [Work.Asymptotics.KhatE1.phit2Ztr]


/-! ### The two `u`-deviation atoms -/

lemma bdE_dE2z : BdE 0 6 (fun _ z => Work.Asymptotics.KhatE1.dE2z z) := by
  obtain ⟨C, hC, hb⟩ := exists_dE2z_bound_strip
  refine ⟨C, 0, 0, hC, le_rfl, le_rfl, fun τ z t hτ ht ha hb' hzt => ?_⟩
  have hz : (3 : ℝ) ≤ z.im := by rw [hzt]; linarith [hτ.2]
  have h := hb z hz
  have hE : ‖Work.Kernels.qParamFun z‖ ^ 3 = ‖Work.Residues.Ept z‖ ^ 6 := by
    rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq z, norm_pow]
    ring
  rw [hE] at h
  simpa only [pow_zero, Real.rpow_zero, mul_one] using h

lemma bdE_dE4z : BdE 0 6 (fun _ z => Work.Asymptotics.KhatE1.dE4z z) := by
  obtain ⟨C, hC, hb⟩ := exists_dE4z_bound_strip
  refine ⟨C, 0, 0, hC, le_rfl, le_rfl, fun τ z t hτ ht ha hb' hzt => ?_⟩
  have hz : (3 : ℝ) ≤ z.im := by rw [hzt]; linarith [hτ.2]
  have h := hb z hz
  have hE : ‖Work.Kernels.qParamFun z‖ ^ 3 = ‖Work.Residues.Ept z‖ ^ 6 := by
    rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq z, norm_pow]
    ring
  rw [hE] at h
  simpa only [pow_zero, Real.rpow_zero, mul_one] using h

lemma bdE_dDz : BdE 0 8 (fun _ z => Work.Asymptotics.KhatE1.dDz z) := by
  obtain ⟨C, hC, hb⟩ := exists_dDz_bound_strip
  refine ⟨C, 0, 0, hC, le_rfl, le_rfl, fun τ z t hτ ht ha hb' hzt => ?_⟩
  have hz : (3 : ℝ) ≤ z.im := by rw [hzt]; linarith [hτ.2]
  have h := hb z hz
  have hE : ‖Work.Kernels.qParamFun z‖ ^ 4 = ‖Work.Residues.Ept z‖ ^ 8 := by
    rw [Work.Asymptotics.Small.qParamFun_eq_Ept_sq z, norm_pow]
    ring
  rw [hE] at h
  simpa only [pow_zero, Real.rpow_zero, mul_one] using h

/-! ### The composite atoms -/

/-- The `z`-squared atom. -/
lemma bdE_zsq : BdE 0 0 (fun _ (z : ℍ) => ((z : ℍ) : ℂ) ^ 2) := by
  simpa using BdE.pow bdE_z 2

/-- `12i z / π` as a strip atom. -/
lemma bdE_12iz : BdE 0 0 (fun _ (z : ℍ) => 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ)) := by
  have h := BdE.mul (BdE.const (12 * Complex.I / (Real.pi : ℂ))) bdE_z
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  show (12 * Complex.I / (Real.pi : ℂ)) * (z : ℂ)
    = 12 * Complex.I * (z : ℂ) / (Real.pi : ℂ)
  ring

/-- `Φ₁ = PhiMain`. -/
lemma bdE_PhiMain : BdE 0 0 (fun τ z => Work.Asymptotics.Compact.PhiMain τ z) := by
  have hA := BdE.add (BdE.neg (BdE.mul bdE_zsq (BdE.add (BdE.const 1) bdE_E2Fz))) bdE_12iz
  have h1 := BdE.mul (BdE.mul bdE_tau bdE_E6) hA
  have h2 := BdE.mul (BdE.mul (BdE.cmul 2 bdE_phi0) bdE_E4) bdE_zsq
  have hsum := BdE.add h1 h2
  have hfin := BdE.mul (BdE.sub bdE_E2Fz (BdE.const 1)) hsum
  refine hfin.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  unfold Work.Asymptotics.Compact.PhiMain
  ring

/-- `kdevDir = τE₆(τ)·phitVec z 2 - 2φ₀(τ)E₄(τ)·phitVec z 1`. -/
lemma bdE_kdevDir : BdE 0 0 (fun τ z => Work.Asymptotics.KhatE1.kdevDir τ z) := by
  have h1 := BdE.mul (BdE.mul bdE_tau bdE_E6) (BdE.pow bdE_Gt 2)
  have h2 := BdE.mul (BdE.mul (BdE.cmul 2 bdE_phi0) bdE_E4) (BdE.mul bdE_z bdE_Gt)
  have h := BdE.add h1 (BdE.neg h2)
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  unfold Work.Asymptotics.KhatE1.kdevDir
  rw [Work.Kernels.TildeFacts.phitVec_two z, Work.Kernels.TildeFacts.phitVec_one z]
  ring

/-- `PhiMainLin`. -/
lemma bdE_PhiMainLin : BdE 0 0 (fun τ z => Work.Asymptotics.KhatE1.PhiMainLin τ z) := by
  have hA := BdE.add (BdE.neg (BdE.mul bdE_zsq (BdE.add (BdE.const 1) bdE_E2Ztr))) bdE_12iz
  have h1 := BdE.mul (BdE.mul bdE_tau bdE_E6) hA
  have h2 := BdE.mul (BdE.mul (BdE.cmul 2 bdE_phi0) bdE_E4) bdE_zsq
  have h3 := BdE.mul (BdE.sub bdE_E2Ztr (BdE.const 1))
    (BdE.neg (BdE.mul (BdE.mul bdE_tau bdE_E6) bdE_zsq))
  have h := BdE.add (BdE.add h1 h2) h3
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  unfold Work.Asymptotics.KhatE1.PhiMainLin
  ring

/-- **`kdevA2JF` is `O(‖q(τ)‖(scale τ)^N(1+t)^M)`.** -/
lemma bdE_kdevA2JF (ℓ : Work.Kernels.LogLambdaData) :
    BdE 1 0 (fun τ z => Work.Asymptotics.KhatE1.kdevA2JF ℓ τ z) := by
  have h1 := BdE.mul bdE_Delta
    (BdE.mul (BdE.const Work.Asymptotics.Compact.tailC⁻¹) bdE_PhiMain)
  have h2 := BdE.cmul ((3456 : ℂ) * (Real.pi : ℂ))⁻¹
    (BdE.add (BdE.mul bdE_Delta (bdE_br0 ℓ))
      (BdE.neg (BdE.mul bdE_Ept (bdE_R8p0JF ℓ))))
  have h3 := BdE.mul bdE_Delta
    (BdE.mul (BdE.const Work.Asymptotics.Compact.tailC⁻¹) bdE_kdevDir)
  have h := BdE.add (BdE.add h1 h2) h3
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  unfold Work.Asymptotics.KhatE1.kdevA2JF
  ring

/-- **`KdevA2Dev` is `O(‖q(τ)‖‖Ept z‖⁶(scale τ)^N(1+t)^M)`.** -/
lemma bdE_KdevA2Dev (ℓ : Work.Kernels.LogLambdaData) :
    BdE 1 6 (fun τ z => Work.Asymptotics.KhatE1.KdevA2Dev ℓ τ z) := by
  have hzz : BdE 0 6 (fun _ z => (z : ℂ) * Work.Asymptotics.KhatE1.dE2z z) :=
    BdE.mul bdE_z bdE_dE2z
  have hA := BdE.mul bdE_dE2z bdE_PhiMainLin
  have hB := BdE.mul (BdE.pow bdE_dE2z 2)
    (BdE.neg (BdE.mul (BdE.mul bdE_tau bdE_E6) bdE_zsq))
  have hC1 := BdE.mul (BdE.mul bdE_tau bdE_E6)
    (BdE.add (BdE.mul (BdE.mul (BdE.const 2) bdE_GtTr) hzz) (BdE.pow hzz 2))
  have hC2 := BdE.mul (BdE.mul (BdE.cmul 2 bdE_phi0) bdE_E4) (BdE.mul bdE_z hzz)
  have hC := BdE.add hC1 (BdE.neg hC2)
  have hInner := BdE.add (BdE.add hA hB) hC
  have hOut := BdE.mul (BdE.mul bdE_Delta (BdE.const Work.Asymptotics.Compact.tailC⁻¹))
    hInner
  refine hOut.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  unfold Work.Asymptotics.KhatE1.KdevA2Dev
  ring

/-- **`ShDev` is `O(‖Ept z‖⁶(scale τ)^N(1+t)^M)`.** -/
lemma bdE_ShDev : BdE 0 6 (fun τ z => Work.Asymptotics.KhatE1.ShDev τ z) := by
  have hEZ := BdE.pow bdE_E4Ztr 2
  have hd2 := BdE.pow bdE_dE4z 2
  have hd3 := BdE.pow bdE_dE4z 3
  have hA := BdE.mul (BdE.cmul 3 hEZ) bdE_dE4z
  have hB := BdE.mul (BdE.cmul 3 bdE_E4Ztr) hd2
  have hSum := BdE.add (BdE.add hA hB) hd3
  have h1 := BdE.mul bdE_Delta hSum
  have h2 := BdE.mul bdE_dDz (BdE.pow bdE_E4 3)
  have h := BdE.add h1 (BdE.neg h2)
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  unfold Work.Asymptotics.KhatE1.ShDev
  ring

/-- **`ShDeltaZtr` is `O(1)`.** -/
lemma bdE_ShDeltaZtr : BdE 0 0 (fun τ z => Work.Asymptotics.KhatE1.ShDeltaZtr τ z) := by
  have h1 := BdE.mul bdE_Delta (BdE.pow bdE_E4Ztr 3)
  have h2 := BdE.mul bdE_DeltaZtr (BdE.pow bdE_E4 3)
  have h := BdE.add h1 (BdE.neg h2)
  refine h.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  unfold Work.Asymptotics.KhatE1.ShDeltaZtr
  ring

/-- **`KdevSig2Dev` is `O(‖q(τ)‖‖Ept z‖⁸(scale τ)^N(1+t)^M)`.** -/
lemma bdE_KdevSig2Dev (ℓ : Work.Kernels.LogLambdaData) :
    BdE 1 8 (fun τ z => Work.Asymptotics.KhatE1.KdevSig2Dev ℓ τ z) := by
  have h1 := BdE.mul bdE_Delta
    (BdE.mul (BdE.mul (BdE.mul bdE_phi2 bdE_E14) bdE_zsq) bdE_dDz)
  have h2 := BdE.neg (BdE.cmul Work.Asymptotics.Compact.tailC⁻¹ h1)
  refine h2.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  unfold Work.Asymptotics.KhatE1.KdevSig2Dev
  ring

end Atoms


/-- **`WresDev` is `BdE 1 6`.** -/
lemma bdE_WresDev (ℓ : Work.Kernels.LogLambdaData) :
    BdE 1 6 (fun τ z => Work.Asymptotics.KhatE1RCore.WresDev ℓ τ z) := by
  have hK := BdE.add (bdE_kdevA2JF ℓ)
    (BdE.neg (BdE.cmul 2 (BdE.mul (BdE.pow bdE_Ept 2)
      (BdE.mul bdE_Delta (bdE_KdevE2 ℓ)))))
  have h1 := BdE.mul hK bdE_ShDev
  have h2 := BdE.mul (bdE_KdevA2Dev ℓ) bdE_ShDeltaZtr
  have hsum := BdE.add (BdE.add h1 h2) (bdE_KdevSig2Dev ℓ)
  refine hsum.congr_on (fun τ z t hτ ht ha hb hzt => ?_)
  unfold Work.Asymptotics.KhatE1RCore.WresDev
  ring

theorem WresDevBound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane) (t : ℝ), Work.Asymptotics.Funnel τ → τ.im + 1 ≤ t →
        -1 ≤ z.re → z.re ≤ 2 → z.im = t →
        ‖Work.Asymptotics.KhatE1RCore.WresDev ℓ τ z‖
          ≤ C * ‖Work.Kernels.qParamFun τ‖ ^ 3 * ‖Work.Residues.Ept z‖ ^ 2
              * (Work.Kernels.scale τ) ^ N * (1 + t) ^ M :=
  BdE.finish (bdE_WresDev ℓ) (by norm_num) (by norm_num)

end

end Work.Asymptotics.KhatE1RCore
