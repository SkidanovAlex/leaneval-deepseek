/-
# CKMRV Proposition 3.2(2) at even weight

The growth propagation `Work.Asymptotics.bound_of_propagates` for even weights: the reduction of
`τ` into the closure of the standard fundamental domain `𝓕`
(`Work.Asymptotics.exists_reduction`), the reduction of the group element `γ` modulo the defect
ideal with polynomially bounded carries (`Work.Asymptotics.carry_bound`), the change of basis
`M6 → M'` (`Work.Asymptotics.M6_eq_Mp`) and the estimates for the six translates of `𝓕`
(`Work.Asymptotics.Mp_smul_mem_closure_DomainD`).

All the estimates are organised around the single quantity `Q = E (1 + s)^E`, where
`s = scale τ` and `E` is a constant dominating all the constants appearing in the inputs.
Every quantity that occurs is bounded by a power of `Q`, so the bookkeeping reduces to the
addition of exponents.
-/
import Mathlib
import Submission.Work.Asymptotics.PropagateBounds.Estimate
import Submission.Work.Asymptotics.PropagateBounds.Reduce
import Submission.Work.Asymptotics.PropagateBounds.Algebra
import Submission.Work.Asymptotics.AtomCarries
import Submission.Work.Asymptotics.carry_bound
import Submission.Work.Asymptotics.sigma_entry_bound
import Submission.Work.Asymptotics.Mp_smul_mem_closure_DomainD
import Submission.Work.Asymptotics.PropagateCarries
import Submission.Work.Asymptotics.PropagateDefs
import Submission.Work.Asymptotics.DomainD

set_option maxHeartbeats 30000000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels
open Work.Residues (M6 Rneg rowDiff sigmaR augIdeal)

/-! ## Slash algebra -/

lemma slash_MpR (k : ℤ) (i : Fin 6) (F : ℍ → ℂ) : slash k (MpR i) F = F ∣[k] Mp i := by
  rw [MpR_eq_of, MonoidAlgebra.of_apply, Work.Kernels.slash_single, one_smul]

lemma slash_smul' (k : ℤ) (c : ℂ) (r : R) (F : ℍ → ℂ) : slash k (c • r) F = c • slash k r F := by
  induction r using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [smul_add, slash_add, hx, hy, slash_add, smul_add]
  | single γ d => rw [MonoidAlgebra.smul_single', slash_single, slash_single, smul_smul]

lemma slash_sumF (k : ℤ) {ι : Type*} (s : Finset ι) (c : ι → ℂ) (r : ι → R) (F : ℍ → ℂ) :
    slash k (∑ i ∈ s, c i • r i) F = ∑ i ∈ s, c i • slash k (r i) F := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, slash_add, ih, slash_smul']

lemma slash_sum' (k : ℤ) {ι : Type*} [Fintype ι] (c : ι → ℂ) (r : ι → R) (F : ℍ → ℂ) :
    slash k (∑ i, c i • r i) F = ∑ i, c i • slash k (r i) F := by
  simpa using slash_sumF k (Finset.univ) c r F

/-- The slash of a `carryComb` is the sum of the two carries applied to the defects, at even
weight (where `z-1` acts by `0`). -/
lemma slash_carryComb (k : ℤ) (hk : Even k) (a b c : R) {f h₁ h₂ : ℍ → ℂ}
    (hT : T2op f = h₁) (hS : S2op k f = h₂) :
    slash k (carryComb a b c) f = slash k a h₁ + slash k b h₂ := by
  rw [show carryComb a b c
      = (R_T - 1) ^ 2 * a + R_S * (R_T - 1) ^ 2 * b + (Rneg - 1) * c from rfl]
  rw [Work.Kernels.slash_add, Work.Kernels.slash_add]
  rw [Work.Kernels.AlgebraFacts.slash_mul, Work.Kernels.slash_T2, hT]
  rw [show slash k (R_S * (R_T - 1) ^ 2 * b) f = slash k b (S2op k f) from by
    rw [Work.Kernels.AlgebraFacts.slash_mul]; rfl]
  rw [hS]
  rw [Work.Residues.slash_mem_augIdeal hk (Work.Residues.Rneg_sub_one_mul_mem c) f]
  ring

/-! ## The `Q`-power calculus -/

lemma Q_mul {Q a b : ℝ} (hQ : 0 < Q) : Q ^ (a + b) = Q ^ a * Q ^ b := Real.rpow_add hQ a b

lemma Q_le {Q m n : ℝ} (hQ : 1 ≤ Q) (h : m ≤ n) : Q ^ m ≤ Q ^ n :=
  Real.rpow_le_rpow_of_exponent_le hQ h

lemma Q_mul_one {Q a : ℝ} (hQ : 0 < Q) : Q * Q ^ a = Q ^ (a + 1) := by
  rw [show a + 1 = 1 + a from by ring, Real.rpow_add hQ, Real.rpow_one]

lemma Q_one_mul {Q a : ℝ} (hQ : 0 < Q) : Q ^ a * Q = Q ^ (a + 1) := by
  rw [mul_comm, Q_mul_one hQ]

lemma Q_mul_pow {Q a b : ℝ} (hQ : 0 < Q) : Q ^ a * Q ^ b = Q ^ (a + b) :=
  (Real.rpow_add hQ a b).symm

lemma Q_pow_le {Q X m : ℝ} (hX0 : 0 ≤ X) (hX : X ≤ Q) (hm : 0 ≤ m) : X ^ m ≤ Q ^ m :=
  Real.rpow_le_rpow hX0 hX hm

/-- `Q ≤ Q ^ (E + 2)` for `Q ≥ 1` and `E ≥ 0`. -/
lemma Q_le_self {Q E : ℝ} (hQ1 : 1 ≤ Q) (hE0 : 0 ≤ E) : Q ≤ Q ^ (E + 2) := by
  have h := Q_le hQ1 (show (1:ℝ) ≤ E + 2 by linarith)
  rwa [Real.rpow_one] at h

/-- Combining two `Q`-powers with a numerical coefficient. -/
lemma Q_rewrite {A Q a b c : ℝ} (hQ : 0 < Q) (h : a + b = c) :
    A * Q ^ a * Q ^ b = A * Q ^ c := by
  rw [show A * Q ^ a * Q ^ b = A * (Q ^ a * Q ^ b) by ring, Q_mul_pow hQ, h]

/-- Combining two `Q`-powers. -/
lemma Q_rewrite' {Q a b c : ℝ} (hQ : 0 < Q) (h : a + b = c) : Q ^ a * Q ^ b = Q ^ c := by
  rw [Q_mul_pow hQ, h]

/-- Exponentiation of a `Q`-power. -/
lemma Q_pow_pow {Q m n : ℝ} (hQ : 0 ≤ Q) : (Q ^ m) ^ n = Q ^ (m * n) := by
  rcases eq_or_lt_of_le hQ with h | h
  · subst h
    rcases eq_or_ne m 0 with rfl | hm
    · rw [Real.rpow_zero, Real.one_rpow, zero_mul, Real.rpow_zero]
    · rcases eq_or_ne n 0 with rfl | hn
      · rw [Real.rpow_zero, mul_zero, Real.rpow_zero]
      · rw [Real.zero_rpow hm, Real.zero_rpow hn, Real.zero_rpow (mul_ne_zero hm hn)]
  · rw [Real.rpow_mul (le_of_lt h) m n]

/-- The growth of `scale` under a Möbius transformation, in `Q`-power form. -/
lemma scale_smul_Q {δ : SL(2,ℤ)} {w : ℍ} {Q E M : ℝ} (hQ7 : 7 ≤ Q) (hM0 : 0 ≤ M)
    (hE0 : 0 ≤ E) (hδ : 1 + Frob δ ≤ Q ^ (E + 2)) (hw : 1 + scale w ≤ Q) :
    (scale (δ • w)) ^ M ≤ Q ^ ((4 * E + 13) * M) := by
  have hQ1 : 1 ≤ Q := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hQpos : 0 < Q := by linarith
  have hδ0 : (0:ℝ) ≤ 1 + Frob δ := by linarith [Frob_nonneg δ]
  have hw0 : (0:ℝ) ≤ 1 + scale w := by linarith [scale_pos w]
  have h2 : (1 + Frob δ) ^ (4:ℝ) ≤ Q ^ ((E + 2) * 4) := by
    calc (1 + Frob δ) ^ (4:ℝ) ≤ (Q ^ (E + 2)) ^ (4:ℝ) := Real.rpow_le_rpow hδ0 hδ (by norm_num)
      _ = Q ^ ((E + 2) * 4) := Q_pow_pow hQ0
  have h3 : (1 + scale w) ^ (4:ℝ) ≤ Q ^ (4:ℝ) := Real.rpow_le_rpow hw0 hw (by norm_num)
  have h4 : (7:ℝ) * Q ^ ((E + 2) * 4) * Q ^ (4:ℝ) ≤ Q ^ (4 * E + 13) := by
    have h5 : (7:ℝ) * Q ^ ((E + 2) * 4) * Q ^ (4:ℝ)
        ≤ Q ^ (1:ℝ) * Q ^ ((E + 2) * 4) * Q ^ (4:ℝ) := by
      rw [Real.rpow_one]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ0 _)
      exact mul_le_mul_of_nonneg_right hQ7 (Real.rpow_nonneg hQ0 _)
    rw [← Q_mul hQpos, ← Q_mul hQpos] at h5
    refine le_trans h5 (Q_le hQ1 ?_)
    ring_nf
    nlinarith [hE0]
  have h8 : scale (δ • w) ≤ Q ^ (4 * E + 13) :=
    calc scale (δ • w) ≤ 7 * (1 + Frob δ) ^ (4:ℝ) * (1 + scale w) ^ (4:ℝ) :=
          scale_smul_le_poly δ w
      _ ≤ 7 * Q ^ ((E + 2) * 4) * Q ^ (4:ℝ) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left h2 (by norm_num)) h3
            (Real.rpow_nonneg hw0 _) ?_
          positivity
      _ ≤ Q ^ (4 * E + 13) := h4
  calc (scale (δ • w)) ^ M ≤ (Q ^ (4 * E + 13)) ^ M :=
        Real.rpow_le_rpow (le_of_lt (scale_pos (δ • w))) h8 hM0
    _ = Q ^ ((4 * E + 13) * M) := Q_pow_pow hQ0

/-- **The bound for the slashes of a defect along the support of a carry.**  If every monomial
`δ` in the support of `A` satisfies `1 + ‖δ‖ ≤ Q ^ (E+2)`, if `1 + scale w ≤ Q` and if `h`
satisfies a growth bound with exponent `M ≤ E`, then `slash k A h w` is bounded by
`coeffNorm A` times a power of `Q`. -/
lemma slash_defect_Q {k : ℤ} {A : R} {h : ℍ → ℂ} {w : ℍ} {C C_j N_j E s M Q BIG : ℝ}
    (hj : ∀ (γ : SL(2,ℤ)) (τ : ℍ),
      ‖jFun γ (τ : ℂ)‖ ^ (-k) ≤ C_j * (1 + Frob γ) ^ N_j * (1 + scale τ) ^ N_j)
    (hE0 : 0 ≤ E) (hQ7 : 7 ≤ Q) (hC : 0 ≤ C) (hCj : C_j ≤ E) (hNj : N_j ≤ E)
    (hEQ : E ≤ Q)
    (hNj0 : 0 ≤ N_j) (hM0 : 0 ≤ M) (hME : M ≤ E) (hBIG : 5 * E ^ 2 + 17 * E + 2 ≤ BIG)
    (hh : ∀ τ : ℍ, ‖h τ‖ ≤ C * (scale τ) ^ M)
    (hY : 1 + scale w ≤ Q)
    (hA : ∀ δ ∈ A.coeff.support, 1 + Frob δ ≤ Q ^ (E + 2))
    (hcoef : coeffNorm A ≤ Q ^ (E + 1)) :
    ‖slash k A h w‖ ≤ C * Q ^ BIG := by
  have hQ1 : 1 ≤ Q := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hQpos : 0 < Q := by linarith
  have hCjQ : C_j ≤ Q := le_trans hCj hEQ
  have hL : ∀ δ ∈ A.coeff.support, ‖(h ∣[k] δ) w‖ ≤ C * Q ^ (5 * E ^ 2 + 16 * E + 1) := by
    intro δ hδ
    have hδ1 : 1 + Frob δ ≤ Q ^ (E + 2) := hA δ hδ
    have hsc := scale_smul_Q hQ7 hM0 hE0 hδ1 hY
    have hsc' : (scale (δ • w)) ^ M ≤ Q ^ (4 * E ^ 2 + 13 * E) := by
      refine le_trans hsc (Q_le hQ1 ?_)
      nlinarith [hM0, hME, hE0]
    have hjδ : ‖jFun δ (w : ℂ)‖ ^ (-k) ≤ Q ^ ((E + 2) * E + E + 1) := by
      have h7 : (1 + Frob δ) ^ N_j ≤ (Q ^ (E + 2)) ^ N_j :=
        Real.rpow_le_rpow (by linarith [Frob_nonneg δ]) hδ1 hNj0
      have h8 : (1 + scale w) ^ N_j ≤ Q ^ N_j :=
        Real.rpow_le_rpow (by linarith [scale_pos w]) hY hNj0
      have h1 : C_j * (1 + Frob δ) ^ N_j * (1 + scale w) ^ N_j
          ≤ Q * (Q ^ (E + 2)) ^ N_j * Q ^ N_j := by
        refine mul_le_mul (mul_le_mul hCjQ h7 (Real.rpow_nonneg (by linarith [Frob_nonneg δ]) _)
          (le_trans zero_le_one hQ1)) h8 (Real.rpow_nonneg (by linarith [scale_pos w]) _) ?_
        positivity
      have h9 : (Q ^ (E + 2)) ^ N_j = Q ^ ((E + 2) * N_j) := Q_pow_pow hQ0
      have h10 : Q * Q ^ ((E + 2) * N_j) * Q ^ N_j = Q ^ (1 + (E + 2) * N_j + N_j) := by
        have h11 : Q * Q ^ ((E + 2) * N_j) = Q ^ (1 + (E + 2) * N_j) := by
          rw [Real.rpow_add hQpos, Real.rpow_one]
        rw [h11, ← Q_mul hQpos]
      calc ‖jFun δ (w : ℂ)‖ ^ (-k)
          ≤ C_j * (1 + Frob δ) ^ N_j * (1 + scale w) ^ N_j := hj δ w
        _ ≤ Q * (Q ^ (E + 2)) ^ N_j * Q ^ N_j := h1
        _ = Q ^ (1 + (E + 2) * N_j + N_j) := by rw [h9, h10]
        _ ≤ Q ^ ((E + 2) * E + E + 1) := by
            refine Q_le hQ1 ?_
            nlinarith [hNj, hNj0, hME, hE0]
    have hA1 : ‖h (δ • w)‖ ≤ C * Q ^ (4 * E ^ 2 + 13 * E) :=
      le_trans (hh (δ • w)) (mul_le_mul_of_nonneg_left hsc' hC)
    rw [norm_slash]
    have hc1 : ‖h (δ • w)‖ * ‖jFun δ (w : ℂ)‖ ^ (-k)
        ≤ (C * Q ^ (4 * E ^ 2 + 13 * E)) * Q ^ ((E + 2) * E + E + 1) :=
      mul_le_mul hA1 hjδ (by positivity) (by positivity)
    refine le_trans hc1 ?_
    have hkey : Q ^ (4 * E ^ 2 + 13 * E) * Q ^ ((E + 2) * E + E + 1)
        = Q ^ (5 * E ^ 2 + 16 * E + 1) := by
      rw [← Q_mul hQpos]
      congr 1
      ring
    rw [mul_assoc, hkey]
  have h2 := norm_slash_le k A h w (by positivity) hL
  refine le_trans h2 ?_
  have h3 : (0:ℝ) ≤ C * Q ^ (5 * E ^ 2 + 16 * E + 1) := by positivity
  have h4 : coeffNorm A * (C * Q ^ (5 * E ^ 2 + 16 * E + 1))
      ≤ Q ^ (E + 1) * (C * Q ^ (5 * E ^ 2 + 16 * E + 1)) :=
    mul_le_mul_of_nonneg_right hcoef h3
  have h5 : Q ^ (E + 1) * (C * Q ^ (5 * E ^ 2 + 16 * E + 1)) = C * Q ^ (5 * E ^ 2 + 17 * E + 2) := by
    rw [show Q ^ (E + 1) * (C * Q ^ (5 * E ^ 2 + 16 * E + 1))
        = C * (Q ^ (E + 1) * Q ^ (5 * E ^ 2 + 16 * E + 1)) by ring,
      ← Q_mul hQpos]
    congr 1
    ring
  rw [h5] at h4
  exact le_trans h4 (mul_le_mul_of_nonneg_left (Q_le hQ1 hBIG) hC)

/-! ## The even-weight propagation -/

theorem bound_of_propagates_even {k : ℤ} (hk : Even k) {f h₁ h₂ : ℍ → ℂ}
    (h : Propagates k Set.univ f h₁ h₂) {Nf Cf C₁ C₂ : ℝ}
    (hCf : 0 ≤ Cf) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hf : ∀ τ ∈ DomainD, ‖f τ‖ ≤ Cf * (scale τ) ^ Nf)
    (hh₁ : ∀ τ : ℍ, ‖h₁ τ‖ ≤ C₁ * (scale τ) ^ Nf)
    (hh₂ : ∀ τ : ℍ, ‖h₂ τ‖ ≤ C₂ * (scale τ) ^ Nf) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ τ : UpperHalfPlane, ‖f τ‖ ≤ C * (Cf + C₁ + C₂) * (scale τ) ^ N := by
  have hT : T2op f = h₁ := funext fun τ =>
    h.2.2.2.2.1 τ (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
  have hS : S2op k f = h₂ := funext fun τ =>
    h.2.2.2.2.2 τ (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
  have hcont : Continuous f := (mdifferentiableOn_univ.mp h.2.2.2.1).continuous
  have hfcl : ∀ τ ∈ closure DomainD, ‖f τ‖ ≤ Cf * (scale τ) ^ Nf := closure_bound hcont hf
  -- replace the exponent `Nf` by the nonnegative `M = |Nf|`
  set M : ℝ := |Nf| with hMdef
  have hM0 : 0 ≤ M := abs_nonneg Nf
  have hNfM : Nf ≤ M := le_abs_self Nf
  have hfM : ∀ τ ∈ closure DomainD, ‖f τ‖ ≤ Cf * (scale τ) ^ M := by
    intro τ hτ
    refine le_trans (hfcl τ hτ) (mul_le_mul_of_nonneg_left ?_ hCf)
    exact Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) hNfM
  have hh₁M : ∀ τ : ℍ, ‖h₁ τ‖ ≤ C₁ * (scale τ) ^ M := by
    intro τ
    refine le_trans (hh₁ τ) (mul_le_mul_of_nonneg_left ?_ hC₁)
    exact Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) hNfM
  have hh₂M : ∀ τ : ℍ, ‖h₂ τ‖ ≤ C₂ * (scale τ) ^ M := by
    intro τ
    refine le_trans (hh₂ τ) (mul_le_mul_of_nonneg_left ?_ hC₂)
    exact Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) hNfM
  obtain ⟨C_cb, N_cb, hC_cb, hN_cb, hcb⟩ := carry_bound
  obtain ⟨C_sig, N_sig, hC_sig, hN_sig, hsig⟩ := sigma_entry_bound
  obtain ⟨C_j1, N_j1, hC_j1, hN_j1, hj1⟩ := jFun_zpow_le (-k)
  obtain ⟨C_j2, N_j2, hC_j2, hN_j2, hj2⟩ := jFun_zpow_le k
  obtain ⟨C_red, N_red, hC_red, hN_red, hred⟩ := exists_reduction
  set E : ℝ := 1000 + C_cb + N_cb + C_sig + N_sig + C_j1 + N_j1 + C_j2 + N_j2 + C_red + N_red + M
    with hEdef
  have hE1000 : 1000 ≤ E := by
    rw [hEdef]
    linarith [hC_cb, hN_cb, hC_sig, hN_sig, hC_j1, hN_j1, hC_j2, hN_j2, hC_red, hN_red, hM0]
  have hE1 : 1 ≤ E := by linarith
  have hE3 : 3 ≤ E := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hE_Ccb : C_cb ≤ E := by
    rw [hEdef]; linarith [hN_cb, hC_sig, hN_sig, hC_j1, hN_j1, hC_j2, hN_j2, hC_red, hN_red, hM0]
  have hE_Ncb : N_cb ≤ E := by
    rw [hEdef]; linarith [hC_cb, hC_sig, hN_sig, hC_j1, hN_j1, hC_j2, hN_j2, hC_red, hN_red, hM0]
  have hE_Csig : C_sig ≤ E := by
    rw [hEdef]; linarith [hC_cb, hN_cb, hN_sig, hC_j1, hN_j1, hC_j2, hN_j2, hC_red, hN_red, hM0]
  have hE_Nsig : N_sig ≤ E := by
    rw [hEdef]; linarith [hC_cb, hN_cb, hC_sig, hC_j1, hN_j1, hC_j2, hN_j2, hC_red, hN_red, hM0]
  have hE_Cj1 : C_j1 ≤ E := by
    rw [hEdef]; linarith [hC_cb, hN_cb, hC_sig, hN_sig, hN_j1, hC_j2, hN_j2, hC_red, hN_red, hM0]
  have hE_Nj1 : N_j1 ≤ E := by
    rw [hEdef]; linarith [hC_cb, hN_cb, hC_sig, hN_sig, hC_j1, hC_j2, hN_j2, hC_red, hN_red, hM0]
  have hE_Cj2 : C_j2 ≤ E := by
    rw [hEdef]; linarith [hC_cb, hN_cb, hC_sig, hN_sig, hC_j1, hN_j1, hN_j2, hC_red, hN_red, hM0]
  have hE_Nj2 : N_j2 ≤ E := by
    rw [hEdef]; linarith [hC_cb, hN_cb, hC_sig, hN_sig, hC_j1, hN_j1, hC_j2, hC_red, hN_red, hM0]
  have hE_Cred : C_red ≤ E := by
    rw [hEdef]; linarith [hC_cb, hN_cb, hC_sig, hN_sig, hC_j1, hN_j1, hC_j2, hN_j2, hN_red, hM0]
  have hE_Nred : N_red ≤ E := by
    rw [hEdef]; linarith [hC_cb, hN_cb, hC_sig, hN_sig, hC_j1, hN_j1, hC_j2, hN_j2, hC_red, hM0]
  have hE_Cred1 : 1 + C_red ≤ E := by
    rw [hEdef]; linarith [hC_cb, hN_cb, hC_sig, hN_sig, hC_j1, hN_j1, hC_j2, hN_j2, hN_red, hM0]
  have hE_M : M ≤ E := by
    rw [hEdef]; linarith [hC_cb, hN_cb, hC_sig, hN_sig, hC_j1, hN_j1, hC_j2, hN_j2, hC_red, hN_red]
  refine ⟨(E * 2 ^ E) ^ (60 * E ^ 2 + 2 * E + 203), E * (60 * E ^ 2 + 2 * E + 203), ?_, ?_,
    fun τ => ?_⟩
  · positivity
  · positivity
  -- the main estimate
  set s : ℝ := scale τ with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef]; exact one_le_scale τ
  obtain ⟨γ, w, hwF, hγw, hFrobγ, hscalew⟩ := hred τ
  obtain ⟨a, b, c, hEq, hba, hbb, hbc, hsa, hsb, hsc⟩ := hcb γ
  set σ : Fin 6 → ℂ := fun j => sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) γ) 0 j with hσdef
  set X : ℝ := 1 + Frob γ with hXdef
  set Y : ℝ := 1 + scale w with hYdef
  set Q : ℝ := E * (1 + s) ^ E with hQdef
  have hQ1 : 1 ≤ Q := by
    rw [hQdef]
    have h2 : (1:ℝ) ≤ (1 + s) ^ E := Real.one_le_rpow (by linarith) hE0
    nlinarith
  have hQ0 : 0 ≤ Q := le_trans zero_le_one hQ1
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ1
  have hQ7 : 7 ≤ Q := by
    rw [hQdef]
    have h2 : (1:ℝ) ≤ (1 + s) ^ E := Real.one_le_rpow (by linarith) hE0
    nlinarith
  have hQ6 : (6:ℝ) ≤ Q ^ (2:ℝ) := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have hQ18 : (18:ℝ) ≤ Q ^ (2:ℝ) := by
    rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    nlinarith
  have hEQ : E ≤ Q := by
    rw [hQdef]
    have h2 : (1:ℝ) ≤ (1 + s) ^ E := Real.one_le_rpow (by linarith) hE0
    nlinarith
  have hX : X ≤ Q := by
    rw [hXdef, hQdef, hsdef]
    have h2 : (1:ℝ) ≤ (1 + scale τ) ^ N_red := Real.one_le_rpow (by linarith [scale_pos τ]) hN_red
    have h3 : 1 + C_red * (1 + scale τ) ^ N_red ≤ (1 + C_red) * (1 + scale τ) ^ N_red := by
      nlinarith
    have h4 : (1 + C_red) * (1 + scale τ) ^ N_red ≤ E * (1 + scale τ) ^ E :=
      mul_le_mul hE_Cred1 (one_add_rpow_le_rpow hE_Nred (le_of_lt (scale_pos τ)))
        (Real.rpow_nonneg (by linarith [scale_pos τ]) _) hE0
    linarith [hFrobγ, h3, h4]
  have hY : Y ≤ Q := by
    rw [hYdef, hQdef, hsdef]
    have h2 : (1:ℝ) ≤ (1 + scale τ) ^ N_red := Real.one_le_rpow (by linarith [scale_pos τ]) hN_red
    have h3 : 1 + C_red * (1 + scale τ) ^ N_red ≤ (1 + C_red) * (1 + scale τ) ^ N_red := by
      nlinarith
    have h4 : (1 + C_red) * (1 + scale τ) ^ N_red ≤ E * (1 + scale τ) ^ E :=
      mul_le_mul hE_Cred1 (one_add_rpow_le_rpow hE_Nred (le_of_lt (scale_pos τ)))
        (Real.rpow_nonneg (by linarith [scale_pos τ]) _) hE0
    linarith [hscalew, h3, h4]
  have hX0 : 0 ≤ X := by rw [hXdef]; linarith [Frob_nonneg γ]
  -- sigma bounds
  have hσ : ∀ j : Fin 6, ‖σ j‖ ≤ Q ^ (E + 1) := by
    intro j
    have h1 : ‖σ j‖ ≤ C_sig * X ^ N_sig := by
      simp only [hσdef]
      exact hsig γ 0 j
    refine le_trans h1 ?_
    calc C_sig * X ^ N_sig ≤ E * X ^ E :=
          mul_le_mul hE_Csig (Real.rpow_le_rpow_of_exponent_le (by rw [hXdef]; linarith [Frob_nonneg γ]) hE_Nsig)
            (Real.rpow_nonneg (by linarith) _) hE0
      _ ≤ Q * Q ^ E := mul_le_mul hEQ (Q_pow_le hX0 hX hE0) (Real.rpow_nonneg hX0 _) hQ0
      _ = Q ^ (E + 1) := Q_mul_one hQpos
  have hX1 : 1 ≤ X := by rw [hXdef]; linarith [Frob_nonneg γ]
  have hY0 : 0 ≤ Y := by rw [hYdef]; linarith [scale_pos w]
  have hY1 : 1 ≤ Y := by rw [hYdef]; linarith [scale_pos w]
  -- (1) the six basis coefficients
  have hdvec : ∀ i : Fin 6, ‖dvec σ i‖ ≤ Q ^ (E + 2) := by
    intro i
    have h1 : ‖dvec σ i‖ ≤ 3 * ∑ j : Fin 6, ‖σ j‖ := dvec_apply σ i
    have h2 : ∑ j : Fin 6, ‖σ j‖ ≤ ∑ _j : Fin 6, Q ^ (E + 1) :=
      Finset.sum_le_sum (fun j _ => hσ j)
    have h3 : ∑ _j : Fin 6, Q ^ (E + 1) = 6 * Q ^ (E + 1) := by
      simp [Finset.sum_const, Finset.card_univ, Finset.card_fin, nsmul_eq_mul]
    have h4 : ‖dvec σ i‖ ≤ 18 * Q ^ (E + 1) := by
      rw [h3] at h2
      linarith
    calc ‖dvec σ i‖ ≤ 18 * Q ^ (E + 1) := h4
      _ ≤ Q * Q ^ (E + 1) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hQ0 _)
      _ = Q ^ (E + 2) := by
          rw [Q_mul_one hQpos]
          congr 1
          ring
  -- (2) the norms of the carries
  have hcoefa : coeffNorm a ≤ Q ^ (E + 1) := by
    calc coeffNorm a ≤ C_cb * X ^ N_cb := hba
      _ ≤ E * X ^ E := mul_le_mul hE_Ccb (Real.rpow_le_rpow_of_exponent_le hX1 hE_Ncb)
          (Real.rpow_nonneg hX0 _) hE0
      _ ≤ Q * Q ^ E := mul_le_mul hEQ (Q_pow_le hX0 hX hE0) (Real.rpow_nonneg hX0 _) hQ0
      _ = Q ^ (E + 1) := Q_mul_one hQpos
  have hcoefb : coeffNorm b ≤ Q ^ (E + 1) := by
    calc coeffNorm b ≤ C_cb * X ^ N_cb := hbb
      _ ≤ E * X ^ E := mul_le_mul hE_Ccb (Real.rpow_le_rpow_of_exponent_le hX1 hE_Ncb)
          (Real.rpow_nonneg hX0 _) hE0
      _ ≤ Q * Q ^ E := mul_le_mul hEQ (Q_pow_le hX0 hX hE0) (Real.rpow_nonneg hX0 _) hQ0
      _ = Q ^ (E + 1) := Q_mul_one hQpos
  have hRTinv : (R_Tinv : R) = MonoidAlgebra.of ℂ SL(2,ℤ) (ModularGroup.T⁻¹) := rfl
  have hcoefm : ∀ i : Fin 6, coeffNorm (σ i • R_Tinv) ≤ Q ^ (E + 1) := by
    intro i
    have h1 : coeffNorm (σ i • R_Tinv) ≤ ‖σ i‖ * coeffNorm (R_Tinv) := coeffNorm_smul_le (σ i) R_Tinv
    have h2 : coeffNorm (R_Tinv : R) ≤ 1 := by
      rw [hRTinv]
      exact coeffNorm_of_le _
    calc coeffNorm (σ i • R_Tinv) ≤ ‖σ i‖ * coeffNorm (R_Tinv) := h1
      _ ≤ Q ^ (E + 1) * 1 := mul_le_mul (hσ i) h2 (coeffNorm_nonneg _) (Real.rpow_nonneg hQ0 _)
      _ = Q ^ (E + 1) := by ring
  -- (3) the support bounds
  have hsupa : ∀ δ ∈ a.coeff.support, 1 + Frob δ ≤ Q ^ (E + 2) := by
    intro δ hδ
    have h1 : Frob δ ≤ C_cb * X ^ N_cb := hsa δ hδ
    have h2 : Frob δ ≤ Q ^ (E + 1) := by
      calc Frob δ ≤ C_cb * X ^ N_cb := h1
        _ ≤ E * X ^ E := mul_le_mul hE_Ccb (Real.rpow_le_rpow_of_exponent_le hX1 hE_Ncb)
            (Real.rpow_nonneg hX0 _) hE0
        _ ≤ Q * Q ^ E := mul_le_mul hEQ (Q_pow_le hX0 hX hE0) (Real.rpow_nonneg hX0 _) hQ0
        _ = Q ^ (E + 1) := Q_mul_one hQpos
    have h3 : (1:ℝ) ≤ Q ^ (E + 1) := Real.one_le_rpow hQ1 (by linarith)
    have h4 : (2:ℝ) ≤ Q := by linarith
    have h5 : (2:ℝ) ≤ Q := by linarith
    have h6 : (0:ℝ) ≤ Q ^ (E + 1) := Real.rpow_nonneg hQ0 _
    have h7 : (1:ℝ) ≤ Q ^ (E + 1) := Real.one_le_rpow hQ1 (by linarith)
    calc 1 + Frob δ ≤ 1 + Q ^ (E + 1) := by linarith
      _ ≤ Q ^ (E + 1) * Q := by
          have h8 : 1 + Q ^ (E + 1) ≤ 2 * Q ^ (E + 1) := by linarith
          have h9 : (2:ℝ) * Q ^ (E + 1) ≤ Q * Q ^ (E + 1) :=
            mul_le_mul_of_nonneg_right (by linarith) h6
          have h10 : Q * Q ^ (E + 1) = Q ^ (E + 1) * Q := mul_comm _ _
          linarith [h8, h9, h10.le, h10.ge]
      _ = Q ^ (E + 2) := by
          rw [Q_one_mul hQpos]
          congr 1
          ring
  have hsupb : ∀ δ ∈ b.coeff.support, 1 + Frob δ ≤ Q ^ (E + 2) := by
    intro δ hδ
    have h1 : Frob δ ≤ C_cb * X ^ N_cb := hsb δ hδ
    have h2 : Frob δ ≤ Q ^ (E + 1) := by
      calc Frob δ ≤ C_cb * X ^ N_cb := h1
        _ ≤ E * X ^ E := mul_le_mul hE_Ccb (Real.rpow_le_rpow_of_exponent_le hX1 hE_Ncb)
            (Real.rpow_nonneg hX0 _) hE0
        _ ≤ Q * Q ^ E := mul_le_mul hEQ (Q_pow_le hX0 hX hE0) (Real.rpow_nonneg hX0 _) hQ0
        _ = Q ^ (E + 1) := Q_mul_one hQpos
    have h3 : (1:ℝ) ≤ Q ^ (E + 1) := Real.one_le_rpow hQ1 (by linarith)
    have h4 : (2:ℝ) ≤ Q := by linarith
    have h5 : (2:ℝ) ≤ Q := by linarith
    have h6 : (0:ℝ) ≤ Q ^ (E + 1) := Real.rpow_nonneg hQ0 _
    have h7 : (1:ℝ) ≤ Q ^ (E + 1) := Real.one_le_rpow hQ1 (by linarith)
    calc 1 + Frob δ ≤ 1 + Q ^ (E + 1) := by linarith
      _ ≤ Q ^ (E + 1) * Q := by
          have h8 : 1 + Q ^ (E + 1) ≤ 2 * Q ^ (E + 1) := by linarith
          have h9 : (2:ℝ) * Q ^ (E + 1) ≤ Q * Q ^ (E + 1) :=
            mul_le_mul_of_nonneg_right (by linarith) h6
          have h10 : Q * Q ^ (E + 1) = Q ^ (E + 1) * Q := mul_comm _ _
          linarith [h8, h9, h10.le, h10.ge]
      _ = Q ^ (E + 2) := by
          rw [Q_one_mul hQpos]
          congr 1
          ring
  have hsupm : ∀ i : Fin 6, ∀ δ ∈ (σ i • R_Tinv).coeff.support, 1 + Frob δ ≤ Q ^ (E + 2) := by
    intro i δ hδ
    have h1 : supportFrobLe (σ i • R_Tinv) 2 := by
      rw [hRTinv]
      refine supportFrobLe_mono (supportFrobLe_smul (σ i) (supportFrobLe_of_of _)) ?_
      have h3 := MpFrob_le (1 : Fin 6)
      rwa [show Mp (1 : Fin 6) = (ModularGroup.T⁻¹ : SL(2,ℤ)) from rfl] at h3
    have h2 : Frob δ ≤ 2 := supportFrobLe_mono h1 (le_refl 2) δ hδ
    have h3 : (3:ℝ) ≤ Q ^ (E + 2) := by
      have h4 : Q ≤ Q ^ (E + 2) := Q_le_self hQ1 hE0
      linarith
    linarith
  -- (4) the master identity
  have hsplit : MonoidAlgebra.of ℂ SL(2,ℤ) γ = (∑ j : Fin 6, σ j • M6 j) + carryComb a b c := by
    have h1 : (∑ j : Fin 6, σ j • M6 j)
        = ∑ j : Fin 6, (sigmaR (MonoidAlgebra.of ℂ SL(2,ℤ) γ)) 0 j • M6 j := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hσdef]
    rw [h1]
    rw [show carryComb a b c
        = (R_T - 1) ^ 2 * a + R_S * (R_T - 1) ^ 2 * b + (Rneg - 1) * c from rfl]
    rw [← hEq]
    abel
  have hmaster : slash k (MonoidAlgebra.of ℂ SL(2,ℤ) γ) f w
      = (∑ i : Fin 6, (dvec σ i) • slash k (MpR i) f w)
        + slash k a h₁ w + slash k b h₂ w
        + slash k (σ 1 • R_Tinv) h₁ w + slash k (σ 4 • R_Tinv) h₂ w := by
    have hconv : (∑ j : Fin 6, σ j • M6 j)
        = (∑ i : Fin 6, dvec σ i • MpR i)
          + (R_T - 1) ^ 2 * (σ 1 • R_Tinv) + (R_S * (R_T - 1) ^ 2) * (σ 4 • R_Tinv) :=
      M6_eq_Mp σ
    have hA : slash k ((R_T - 1) ^ 2 * (σ 1 • R_Tinv)) f = slash k (σ 1 • R_Tinv) h₁ := by
      rw [Work.Kernels.AlgebraFacts.slash_mul, Work.Kernels.slash_T2, hT]
    have hB : slash k ((R_S * (R_T - 1) ^ 2) * (σ 4 • R_Tinv)) f = slash k (σ 4 • R_Tinv) h₂ := by
      rw [Work.Kernels.AlgebraFacts.slash_mul, ← hS]
      rfl
    rw [hsplit, Work.Kernels.slash_add, slash_carryComb k hk a b c hT hS, hconv,
      Work.Kernels.slash_add, Work.Kernels.slash_add, hA, hB, slash_sum']
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
    abel
  -- (5) the factor of automorphy
  have hJfac : ‖jFun γ (w : ℂ)‖ ^ k ≤ Q ^ (2 * E + 1) := by
    have h1 : (1 + Frob γ) ^ N_j2 ≤ Q ^ E := by
      have h2 : (1 + Frob γ) ^ N_j2 ≤ Q ^ N_j2 :=
        Real.rpow_le_rpow (by linarith [Frob_nonneg γ]) hX hN_j2
      exact le_trans h2 (Q_le hQ1 hE_Nj2)
    have h2 : (1 + scale w) ^ N_j2 ≤ Q ^ E := by
      have h3 : (1 + scale w) ^ N_j2 ≤ Q ^ N_j2 := Real.rpow_le_rpow hY0 hY hN_j2
      exact le_trans h3 (Q_le hQ1 hE_Nj2)
    calc ‖jFun γ (w : ℂ)‖ ^ k
        ≤ C_j2 * (1 + Frob γ) ^ N_j2 * (1 + scale w) ^ N_j2 := hj2 γ w
      _ ≤ Q * Q ^ E * Q ^ E := by
          have hCj2Q : C_j2 ≤ Q := le_trans hE_Cj2 hEQ
          refine mul_le_mul (mul_le_mul hCj2Q h1 (Real.rpow_nonneg (by linarith [Frob_nonneg γ]) _)
            (le_trans zero_le_one hQ1)) h2 (Real.rpow_nonneg hY0 _) ?_
          positivity
      _ = Q ^ (2 * E + 1) := by
          rw [Q_mul_one hQpos, Q_rewrite' hQpos (by ring : (E + 1) + E = 2 * E + 1)]
  -- (6) the six base terms
  have hbase : ‖∑ i : Fin 6, (dvec σ i) • slash k (MpR i) f w‖ ≤ Cf * Q ^ (60 * E ^ 2 + 200) := by
    have h1 : ‖∑ i : Fin 6, (dvec σ i) • slash k (MpR i) f w‖
        ≤ ∑ i : Fin 6, ‖(dvec σ i) • slash k (MpR i) f w‖ := norm_sum_le _ _
    have h2 : ∀ i : Fin 6, ‖(dvec σ i) • slash k (MpR i) f w‖ ≤ Cf * Q ^ (4 * E ^ 2 + 16 * E + 3) := by
      intro i
      have hMpi : Mp i • w ∈ closure DomainD := Mp_smul_mem_closure_DomainD i hwF
      have hfrob : 1 + Frob (Mp i) ≤ Q ^ (E + 2) := by
        have h3 := MpFrob_le i
        have h4 : (3:ℝ) ≤ Q ^ (E + 2) := by
          have h5 : Q ≤ Q ^ (E + 2) := Q_le_self hQ1 hE0
          linarith
        linarith
      have hsc := scale_smul_Q (δ := Mp i) (M := M) hQ7 hM0 hE0 hfrob hY
      have hsc' : (scale (Mp i • w)) ^ M ≤ Q ^ (4 * E ^ 2 + 13 * E) := by
        refine le_trans hsc (Q_le hQ1 ?_)
        nlinarith [hM0, hE_M, hE0]
      have hfw : ‖f (Mp i • w)‖ ≤ Cf * Q ^ (4 * E ^ 2 + 13 * E) :=
        le_trans (hfM _ hMpi) (mul_le_mul_of_nonneg_left hsc' hCf)
      have hJ1 : ‖jFun (Mp i) (w : ℂ)‖ ^ (-k) ≤ Q ^ (2 * E + 1) := by
        have h3 : (1 + Frob (Mp i)) ^ N_j1 ≤ Q ^ E := by
          have h4 : (1 + Frob (Mp i)) ^ N_j1 ≤ Q ^ N_j1 := by
            have h7 : 1 + Frob (Mp i) ≤ Q := by
              have h8 := MpFrob_le i
              linarith
            exact Real.rpow_le_rpow (by linarith [Frob_nonneg (Mp i)]) h7 hN_j1
          exact le_trans h4 (Q_le hQ1 hE_Nj1)
        have h5 : (1 + scale w) ^ N_j1 ≤ Q ^ E := by
          have h6 : (1 + scale w) ^ N_j1 ≤ Q ^ N_j1 := Real.rpow_le_rpow hY0 hY hN_j1
          exact le_trans h6 (Q_le hQ1 hE_Nj1)
        calc ‖jFun (Mp i) (w : ℂ)‖ ^ (-k)
            ≤ C_j1 * (1 + Frob (Mp i)) ^ N_j1 * (1 + scale w) ^ N_j1 := hj1 (Mp i) w
          _ ≤ Q * Q ^ E * Q ^ E := by
              have hCj1Q : C_j1 ≤ Q := le_trans hE_Cj1 hEQ
              refine mul_le_mul (mul_le_mul hCj1Q h3
                (Real.rpow_nonneg (by linarith [Frob_nonneg (Mp i)]) _)
                (le_trans zero_le_one hQ1)) h5 (Real.rpow_nonneg hY0 _) ?_
              positivity
          _ = Q ^ (2 * E + 1) := by
              rw [Q_mul_one hQpos, Q_rewrite' hQpos (by ring : (E + 1) + E = 2 * E + 1)]
      have hsl : ‖slash k (MpR i) f w‖ ≤ Cf * Q ^ (4 * E ^ 2 + 15 * E + 1) := by
        rw [slash_MpR, norm_slash]
        calc ‖f (Mp i • w)‖ * ‖jFun (Mp i) (w : ℂ)‖ ^ (-k)
            ≤ (Cf * Q ^ (4 * E ^ 2 + 13 * E)) * Q ^ (2 * E + 1) :=
              mul_le_mul hfw hJ1 (by positivity) (by positivity)
          _ = Cf * Q ^ ((4 * E ^ 2 + 13 * E) + (2 * E + 1)) := by
              rw [show (Cf * Q ^ (4 * E ^ 2 + 13 * E)) * Q ^ (2 * E + 1)
                  = Cf * (Q ^ (4 * E ^ 2 + 13 * E) * Q ^ (2 * E + 1)) by ring]
              rw [show Cf * (Q ^ (4 * E ^ 2 + 13 * E) * Q ^ (2 * E + 1))
                  = Cf * Q ^ ((4 * E ^ 2 + 13 * E) + (2 * E + 1)) by rw [Q_mul_pow hQpos]]
          _ = Cf * Q ^ (4 * E ^ 2 + 15 * E + 1) := by
              congr 1
              ring
      rw [norm_smul]
      calc ‖dvec σ i‖ * ‖slash k (MpR i) f w‖
          ≤ Q ^ (E + 2) * (Cf * Q ^ (4 * E ^ 2 + 15 * E + 1)) :=
            mul_le_mul (hdvec i) hsl (norm_nonneg _) (by positivity)
        _ = Cf * Q ^ ((E + 2) + (4 * E ^ 2 + 15 * E + 1)) := by
            rw [show Q ^ (E + 2) * (Cf * Q ^ (4 * E ^ 2 + 15 * E + 1))
                = Cf * (Q ^ (E + 2) * Q ^ (4 * E ^ 2 + 15 * E + 1)) by ring]
            rw [show Cf * (Q ^ (E + 2) * Q ^ (4 * E ^ 2 + 15 * E + 1))
                = Cf * Q ^ ((E + 2) + (4 * E ^ 2 + 15 * E + 1)) by rw [Q_mul_pow hQpos]]
        _ = Cf * Q ^ (4 * E ^ 2 + 16 * E + 3) := by
            congr 1
            ring
    have h3 : ∑ i : Fin 6, ‖(dvec σ i) • slash k (MpR i) f w‖
        ≤ ∑ _i : Fin 6, Cf * Q ^ (4 * E ^ 2 + 16 * E + 3) :=
      Finset.sum_le_sum (fun i _ => h2 i)
    have h4 : ∑ _i : Fin 6, Cf * Q ^ (4 * E ^ 2 + 16 * E + 3)
        = 6 * (Cf * Q ^ (4 * E ^ 2 + 16 * E + 3)) := by
      simp [Finset.sum_const, Finset.card_univ, Finset.card_fin, nsmul_eq_mul]
    refine le_trans h1 (le_trans h3 ?_)
    rw [h4]
    calc 6 * (Cf * Q ^ (4 * E ^ 2 + 16 * E + 3))
        = (6 * Cf) * Q ^ (4 * E ^ 2 + 16 * E + 3) := by ring
      _ ≤ (Q ^ (2:ℝ) * Cf) * Q ^ (4 * E ^ 2 + 16 * E + 3) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ0 _)
          exact mul_le_mul_of_nonneg_right hQ6 hCf
      _ = Cf * Q ^ ((2:ℝ) + (4 * E ^ 2 + 16 * E + 3)) := by
          rw [show (Q ^ (2:ℝ) * Cf) * Q ^ (4 * E ^ 2 + 16 * E + 3)
              = Cf * (Q ^ (2:ℝ) * Q ^ (4 * E ^ 2 + 16 * E + 3)) by ring]
          rw [show Cf * (Q ^ (2:ℝ) * Q ^ (4 * E ^ 2 + 16 * E + 3))
              = Cf * Q ^ ((2:ℝ) + (4 * E ^ 2 + 16 * E + 3)) by rw [Q_mul_pow hQpos]]
      _ = Cf * Q ^ (4 * E ^ 2 + 16 * E + 5) := by
          congr 1
          ring
      _ ≤ Cf * Q ^ (60 * E ^ 2 + 200) :=
          mul_le_mul_of_nonneg_left (Q_le hQ1 (by nlinarith [hE1000])) hCf
  -- (7) the defect terms
  have hd1 : ‖slash k a h₁ w‖ ≤ C₁ * Q ^ (60 * E ^ 2 + 200) :=
    slash_defect_Q (k := k) (A := a) (h := h₁) (C := C₁) (C_j := C_j1) (N_j := N_j1)
      (E := E) (s := s) (M := M) (Q := Q) (BIG := 60 * E ^ 2 + 200)
      hj1 hE0 hQ7 hC₁ hE_Cj1 hE_Nj1 hEQ hN_j1 hM0 hE_M (by nlinarith [hE1000]) hh₁M hY hsupa hcoefa
  have hd2 : ‖slash k b h₂ w‖ ≤ C₂ * Q ^ (60 * E ^ 2 + 200) :=
    slash_defect_Q (k := k) (A := b) (h := h₂) (C := C₂) (C_j := C_j1) (N_j := N_j1)
      (E := E) (s := s) (M := M) (Q := Q) (BIG := 60 * E ^ 2 + 200)
      hj1 hE0 hQ7 hC₂ hE_Cj1 hE_Nj1 hEQ hN_j1 hM0 hE_M (by nlinarith [hE1000]) hh₂M hY hsupb hcoefb
  have hd3 : ‖slash k (σ 1 • R_Tinv) h₁ w‖ ≤ C₁ * Q ^ (60 * E ^ 2 + 200) :=
    slash_defect_Q (k := k) (A := σ 1 • R_Tinv) (h := h₁) (C := C₁) (C_j := C_j1) (N_j := N_j1)
      (E := E) (s := s) (M := M) (Q := Q) (BIG := 60 * E ^ 2 + 200)
      hj1 hE0 hQ7 hC₁ hE_Cj1 hE_Nj1 hEQ hN_j1 hM0 hE_M (by nlinarith [hE1000]) hh₁M hY (hsupm 1) (hcoefm 1)
  have hd4 : ‖slash k (σ 4 • R_Tinv) h₂ w‖ ≤ C₂ * Q ^ (60 * E ^ 2 + 200) :=
    slash_defect_Q (k := k) (A := σ 4 • R_Tinv) (h := h₂) (C := C₂) (C_j := C_j1) (N_j := N_j1)
      (E := E) (s := s) (M := M) (Q := Q) (BIG := 60 * E ^ 2 + 200)
      hj1 hE0 hQ7 hC₂ hE_Cj1 hE_Nj1 hEQ hN_j1 hM0 hE_M (by nlinarith [hE1000]) hh₂M hY (hsupm 4) (hcoefm 4)
  -- (8) assembly
  have hsum : ‖slash k (MonoidAlgebra.of ℂ SL(2,ℤ) γ) f w‖ ≤ (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 202) := by
    rw [hmaster]
    have hC0 : 0 ≤ Cf + C₁ + C₂ := by linarith
    have hbig : ∀ X : ℝ, X ≤ Cf * Q ^ (60 * E ^ 2 + 200) → X ≤ (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 200) := by
      intro X hX
      refine le_trans hX ?_
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hQ0 _)
    have hbig1 : ∀ X : ℝ, X ≤ C₁ * Q ^ (60 * E ^ 2 + 200) → X ≤ (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 200) := by
      intro X hX
      refine le_trans hX ?_
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hQ0 _)
    have hbig2 : ∀ X : ℝ, X ≤ C₂ * Q ^ (60 * E ^ 2 + 200) → X ≤ (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 200) := by
      intro X hX
      refine le_trans hX ?_
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hQ0 _)
    have h1 : ‖(∑ i : Fin 6, (dvec σ i) • slash k (MpR i) f w) + slash k a h₁ w + slash k b h₂ w
        + slash k (σ 1 • R_Tinv) h₁ w + slash k (σ 4 • R_Tinv) h₂ w‖
        ≤ 5 * ((Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 200)) := by
      have h2 := norm_add_le ((∑ i : Fin 6, (dvec σ i) • slash k (MpR i) f w) + slash k a h₁ w
        + slash k b h₂ w + slash k (σ 1 • R_Tinv) h₁ w) (slash k (σ 4 • R_Tinv) h₂ w)
      have h3 := norm_add_le ((∑ i : Fin 6, (dvec σ i) • slash k (MpR i) f w) + slash k a h₁ w
        + slash k b h₂ w) (slash k (σ 1 • R_Tinv) h₁ w)
      have h4 := norm_add_le ((∑ i : Fin 6, (dvec σ i) • slash k (MpR i) f w) + slash k a h₁ w)
        (slash k b h₂ w)
      have h5 := norm_add_le (∑ i : Fin 6, (dvec σ i) • slash k (MpR i) f w) (slash k a h₁ w)
      have h6 := hbig _ hbase
      have h7 := hbig1 _ hd1
      have h8 := hbig2 _ hd2
      have h9 := hbig1 _ hd3
      have h10 := hbig2 _ hd4
      have h11 : (0:ℝ) ≤ (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 200) := by positivity
      linarith
    refine le_trans h1 ?_
    calc 5 * ((Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 200))
        = (5 * (Cf + C₁ + C₂)) * Q ^ (60 * E ^ 2 + 200) := by ring
      _ ≤ (Q ^ (2:ℝ) * (Cf + C₁ + C₂)) * Q ^ (60 * E ^ 2 + 200) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ0 _)
          exact mul_le_mul_of_nonneg_right (by linarith [hQ6]) hC0
      _ = (Cf + C₁ + C₂) * Q ^ ((2:ℝ) + (60 * E ^ 2 + 200)) := by
          rw [show (Q ^ (2:ℝ) * (Cf + C₁ + C₂)) * Q ^ (60 * E ^ 2 + 200)
              = (Cf + C₁ + C₂) * (Q ^ (2:ℝ) * Q ^ (60 * E ^ 2 + 200)) by ring]
          rw [show (Cf + C₁ + C₂) * (Q ^ (2:ℝ) * Q ^ (60 * E ^ 2 + 200))
              = (Cf + C₁ + C₂) * Q ^ ((2:ℝ) + (60 * E ^ 2 + 200)) by rw [Q_mul_pow hQpos]]
      _ = (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 202) := by
          congr 1
          ring
  -- (9) the bound for `f τ`
  have hfj : ‖f τ‖ = ‖slash k (MonoidAlgebra.of ℂ SL(2,ℤ) γ) f w‖ * ‖jFun γ (w : ℂ)‖ ^ k := by
    have hjnz : jFun γ (w : ℂ) ≠ 0 := jFun_ne_zero γ w
    have h1 : slash k (MonoidAlgebra.of ℂ SL(2,ℤ) γ) f w = f τ * (jFun γ (w : ℂ)) ^ (-k) := by
      rw [MonoidAlgebra.of_apply, Work.Kernels.slash_single, one_smul, Work.Kernels.slash_apply', hγw]
    have h2 : f τ = slash k (MonoidAlgebra.of ℂ SL(2,ℤ) γ) f w * (jFun γ (w : ℂ)) ^ k := by
      rw [h1, mul_assoc, ← zpow_add₀ hjnz, neg_add_cancel, zpow_zero, mul_one]
    rw [h2, norm_mul, norm_zpow]
  have hfin : ‖f τ‖ ≤ (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 2 * E + 203) := by
    rw [hfj]
    calc ‖slash k (MonoidAlgebra.of ℂ SL(2,ℤ) γ) f w‖ * ‖jFun γ (w : ℂ)‖ ^ k
        ≤ ((Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 202)) * Q ^ (2 * E + 1) :=
          mul_le_mul hsum hJfac (by positivity) (by positivity)
      _ = (Cf + C₁ + C₂) * Q ^ ((60 * E ^ 2 + 202) + (2 * E + 1)) := by
          rw [show ((Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 202)) * Q ^ (2 * E + 1)
              = (Cf + C₁ + C₂) * (Q ^ (60 * E ^ 2 + 202) * Q ^ (2 * E + 1)) by ring]
          rw [show (Cf + C₁ + C₂) * (Q ^ (60 * E ^ 2 + 202) * Q ^ (2 * E + 1))
              = (Cf + C₁ + C₂) * Q ^ ((60 * E ^ 2 + 202) + (2 * E + 1)) by rw [Q_mul_pow hQpos]]
      _ = (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 2 * E + 203) := by
          congr 1
          ring
  -- (10) conversion to the scale of `τ`
  have hQscale : Q ≤ (E * 2 ^ E) * s ^ E := by
    rw [hQdef, hsdef]
    have h1 : (1 + scale τ) ≤ 2 * scale τ := by linarith [one_le_scale τ]
    have h2 : (1 + scale τ) ^ E ≤ (2 * scale τ) ^ E :=
      Real.rpow_le_rpow (by linarith [scale_pos τ]) h1 hE0
    have h3 : (2 * scale τ) ^ E = 2 ^ E * (scale τ) ^ E := by
      rw [Real.mul_rpow (by norm_num) (le_of_lt (scale_pos τ))]
    calc E * (1 + scale τ) ^ E ≤ E * (2 * scale τ) ^ E := mul_le_mul_of_nonneg_left h2 hE0
      _ = (E * 2 ^ E) * (scale τ) ^ E := by rw [h3]; ring
  have h5 : Q ^ (60 * E ^ 2 + 2 * E + 203)
      ≤ (E * 2 ^ E) ^ (60 * E ^ 2 + 2 * E + 203) * (scale τ) ^ (E * (60 * E ^ 2 + 2 * E + 203)) := by
    have h6 : Q ^ (60 * E ^ 2 + 2 * E + 203) ≤ ((E * 2 ^ E) * s ^ E) ^ (60 * E ^ 2 + 2 * E + 203) :=
      Real.rpow_le_rpow hQ0 hQscale (by positivity)
    have h7 : ((E * 2 ^ E) * s ^ E) ^ (60 * E ^ 2 + 2 * E + 203)
        = (E * 2 ^ E) ^ (60 * E ^ 2 + 2 * E + 203) * (s ^ E) ^ (60 * E ^ 2 + 2 * E + 203) :=
      Real.mul_rpow (by positivity) (Real.rpow_nonneg (by positivity) _)
    have h8 : (s ^ E) ^ (60 * E ^ 2 + 2 * E + 203) = s ^ (E * (60 * E ^ 2 + 2 * E + 203)) :=
      (Real.rpow_mul (by positivity) E (60 * E ^ 2 + 2 * E + 203)).symm
    rw [h7, h8] at h6
    rw [hsdef] at h6
    exact h6
  calc ‖f τ‖ ≤ (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 2 * E + 203) := hfin
    _ ≤ (Cf + C₁ + C₂) * ((E * 2 ^ E) ^ (60 * E ^ 2 + 2 * E + 203)
          * (scale τ) ^ (E * (60 * E ^ 2 + 2 * E + 203))) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = ((E * 2 ^ E) ^ (60 * E ^ 2 + 2 * E + 203)) * (Cf + C₁ + C₂)
          * (scale τ) ^ (E * (60 * E ^ 2 + 2 * E + 203)) := by ring

end Work.Asymptotics
