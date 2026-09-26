import Mathlib
import Submission.Work.Asymptotics.OddBoundTwist
import Submission.Work.Asymptotics.PropagateBounds.EvenBound
import Submission.Work.Asymptotics.bound_of_propagates

/-!
# CKMRV Proposition 3.2(2) with constants chosen before the function

This file proves `Work.CKFinal.bound_of_propagates_uniform`, the *uniform* (in the function `f`)
form of `Work.Asymptotics.bound_of_propagates`: the constants `C` and `N` of the moderate growth
bound may be chosen before `f, h₁, h₂, Cf, C₁, C₂`.

The proof is a literal transcription of the two existing proofs

* `Work.Asymptotics.bound_of_propagates_even` (`Asymptotics/PropagateBounds/EvenBound.lean`), and
* `Work.Asymptotics.bound_of_propagates_odd_twist` (`Asymptotics/OddBoundTwist.lean`),

in which the constants (which come only from `carry_bound` / `carry_twist_odd`,
`sigma_entry_bound`, `jFun_zpow_le k`, `jFun_zpow_le (-k)`, `exists_reduction` and
`M = |Nf|`) are `obtain`ed *before* `f` is introduced, so that the returned `C` and `N` do not
depend on the function.  Everything after the introduction of `f` is unchanged.
-/

noncomputable section

set_option maxHeartbeats 30000000

namespace Work.Asymptotics

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

open Work.Kernels
open Work.Residues (M6 Rneg rowDiff sigmaR augIdeal)

theorem bound_of_propagates_even_uniform (k : ℤ) (hk : Even k) (Nf : ℝ) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (f h₁ h₂ : ℍ → ℂ) (Cf C₁ C₂ : ℝ),
        Propagates k Set.univ f h₁ h₂ →
        0 ≤ Cf → 0 ≤ C₁ → 0 ≤ C₂ →
        (∀ τ ∈ DomainD, ‖f τ‖ ≤ Cf * (scale τ) ^ Nf) →
        (∀ τ : ℍ, ‖h₁ τ‖ ≤ C₁ * (scale τ) ^ Nf) →
        (∀ τ : ℍ, ‖h₂ τ‖ ≤ C₂ * (scale τ) ^ Nf) →
        ∀ τ : ℍ, ‖f τ‖ ≤ C * (Cf + C₁ + C₂) * (scale τ) ^ N := by
  -- replace the exponent `Nf` by the nonnegative `M = |Nf|`
  set M : ℝ := |Nf| with hMdef
  have hM0 : 0 ≤ M := abs_nonneg Nf
  have hNfM : Nf ≤ M := le_abs_self Nf
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
  refine ⟨(E * 2 ^ E) ^ (60 * E ^ 2 + 2 * E + 203), E * (60 * E ^ 2 + 2 * E + 203), ?_, ?_, ?_⟩
  · positivity
  · positivity
  intro f h₁ h₂ Cf C₁ C₂ h hCf hC₁ hC₂ hf hh₁ hh₂ τ
  have hT : T2op f = h₁ := funext fun τ =>
    h.2.2.2.2.1 τ (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
  have hS : S2op k f = h₂ := funext fun τ =>
    h.2.2.2.2.2 τ (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
  have hcont : Continuous f := (mdifferentiableOn_univ.mp h.2.2.2.1).continuous
  have hfcl : ∀ τ ∈ closure DomainD, ‖f τ‖ ≤ Cf * (scale τ) ^ Nf := closure_bound hcont hf
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


theorem bound_of_propagates_odd_uniform (k : ℤ) (hk : Odd k) (Nf : ℝ) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (f h₁ h₂ : ℍ → ℂ) (Cf C₁ C₂ : ℝ),
        Propagates k Set.univ f h₁ h₂ →
        0 ≤ Cf → 0 ≤ C₁ → 0 ≤ C₂ →
        (∀ τ ∈ DomainD, ‖f τ‖ ≤ Cf * (scale τ) ^ Nf) →
        (∀ τ : ℍ, ‖h₁ τ‖ ≤ C₁ * (scale τ) ^ Nf) →
        (∀ τ : ℍ, ‖h₂ τ‖ ≤ C₂ * (scale τ) ^ Nf) →
        ∀ τ : ℍ, ‖f τ‖ ≤ C * (Cf + C₁ + C₂) * (scale τ) ^ N := by
  set M : ℝ := |Nf| with hMdef
  have hM0 : 0 ≤ M := abs_nonneg Nf
  have hNfM : Nf ≤ M := le_abs_self Nf
  obtain ⟨C_od, N_od, hC_od, hN_od, hod⟩ := carry_twist_odd
  obtain ⟨C_j1, N_j1, hC_j1, hN_j1, hj1⟩ := jFun_zpow_le (-k)
  obtain ⟨C_j2, N_j2, hC_j2, hN_j2, hj2⟩ := jFun_zpow_le k
  obtain ⟨C_red, N_red, hC_red, hN_red, hred⟩ := exists_reduction
  set E : ℝ := 1000 + C_od + N_od + C_j1 + N_j1 + C_j2 + N_j2 + C_red + N_red + M with hEdef
  have hE1000 : 1000 ≤ E := by
    rw [hEdef]; linarith [hC_od, hN_od, hC_j1, hN_j1, hC_j2, hN_j2, hC_red, hN_red, hM0]
  have hE1 : 1 ≤ E := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hE_Cod : C_od ≤ E := by
    rw [hEdef]; linarith [hN_od, hC_j1, hN_j1, hC_j2, hN_j2, hC_red, hN_red, hM0]
  have hE_Nod : N_od ≤ E := by
    rw [hEdef]; linarith [hC_od, hC_j1, hN_j1, hC_j2, hN_j2, hC_red, hN_red, hM0]
  have hE_Cj1 : C_j1 ≤ E := by
    rw [hEdef]; linarith [hC_od, hN_od, hN_j1, hC_j2, hN_j2, hC_red, hN_red, hM0]
  have hE_Nj1 : N_j1 ≤ E := by
    rw [hEdef]; linarith [hC_od, hN_od, hC_j1, hC_j2, hN_j2, hC_red, hN_red, hM0]
  have hE_Cj2 : C_j2 ≤ E := by
    rw [hEdef]; linarith [hC_od, hN_od, hC_j1, hN_j1, hN_j2, hC_red, hN_red, hM0]
  have hE_Nj2 : N_j2 ≤ E := by
    rw [hEdef]; linarith [hC_od, hN_od, hC_j1, hN_j1, hC_j2, hC_red, hN_red, hM0]
  have hE_Cred : C_red ≤ E := by
    rw [hEdef]; linarith [hC_od, hN_od, hC_j1, hN_j1, hC_j2, hN_j2, hN_red, hM0]
  have hE_Nred : N_red ≤ E := by
    rw [hEdef]; linarith [hC_od, hN_od, hC_j1, hN_j1, hC_j2, hN_j2, hC_red, hM0]
  have hE_Cred1 : 1 + C_red ≤ E := by
    rw [hEdef]; linarith [hC_od, hN_od, hC_j1, hN_j1, hC_j2, hN_j2, hN_red, hM0]
  have hE_M : M ≤ E := by
    rw [hEdef]; linarith [hC_od, hN_od, hC_j1, hN_j1, hC_j2, hN_j2, hC_red, hN_red]
  set BIG : ℝ := 60 * E ^ 2 + 204 with hBIGdef
  have hE_BIG : 5 * E ^ 2 + 17 * E + 2 ≤ BIG := by
    rw [hBIGdef]; nlinarith [hE1, hE0]
  refine ⟨(E * 2 ^ E) ^ (60 * E ^ 2 + 2 * E + 205), E * (60 * E ^ 2 + 2 * E + 205), ?_, ?_, ?_⟩
  · positivity
  · positivity
  intro f h₁ h₂ Cf C₁ C₂ h hCf hC₁ hC₂ hf hh₁ hh₂ τ
  have hT : T2op f = h₁ := funext fun τ =>
    h.2.2.2.2.1 τ (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
  have hS : S2op k f = h₂ := funext fun τ =>
    h.2.2.2.2.2 τ (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
  have hcont : Continuous f := (mdifferentiableOn_univ.mp h.2.2.2.1).continuous
  have hfcl : ∀ τ ∈ closure DomainD, ‖f τ‖ ≤ Cf * (scale τ) ^ Nf := closure_bound hcont hf
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
  set s : ℝ := scale τ with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef]; exact one_le_scale τ
  obtain ⟨γ, w, hwF, hγw, hFrobγ, hscalew⟩ := hred τ
  obtain ⟨hσb, A, B, hEq, hcoefA, hcoefB, hsupA, hsupB⟩ := hod γ
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
  have hX1 : 1 ≤ X := by rw [hXdef]; linarith [Frob_nonneg γ]
  have hY0 : 0 ≤ Y := by rw [hYdef]; linarith [scale_pos w]
  have hQ0B : (0:ℝ) ≤ Q ^ BIG := Real.rpow_nonneg hQ0 _
  -- the coefficients of the odd reduction
  have hσ : ∀ j : Fin 6, ‖(sigmaHom γ) 0 j‖ ≤ Q ^ (E + 1) := by
    intro j
    calc ‖(sigmaHom γ) 0 j‖ ≤ C_od * X ^ N_od := hσb 0 j
      _ ≤ E * X ^ E := mul_le_mul hE_Cod (Real.rpow_le_rpow_of_exponent_le hX1 hE_Nod)
          (Real.rpow_nonneg hX0 _) hE0
      _ ≤ Q * Q ^ E := mul_le_mul hEQ (Q_pow_le hX0 hX hE0) (Real.rpow_nonneg hX0 _) hQ0
      _ = Q ^ (E + 1) := Q_mul_one hQpos
  have hcoefA' : coeffNorm A ≤ Q ^ (E + 1) := by
    calc coeffNorm A ≤ C_od * X ^ N_od := hcoefA
      _ ≤ E * X ^ E := mul_le_mul hE_Cod (Real.rpow_le_rpow_of_exponent_le hX1 hE_Nod)
          (Real.rpow_nonneg hX0 _) hE0
      _ ≤ Q * Q ^ E := mul_le_mul hEQ (Q_pow_le hX0 hX hE0) (Real.rpow_nonneg hX0 _) hQ0
      _ = Q ^ (E + 1) := Q_mul_one hQpos
  have hcoefB' : coeffNorm B ≤ Q ^ (E + 1) := by
    calc coeffNorm B ≤ C_od * X ^ N_od := hcoefB
      _ ≤ E * X ^ E := mul_le_mul hE_Cod (Real.rpow_le_rpow_of_exponent_le hX1 hE_Nod)
          (Real.rpow_nonneg hX0 _) hE0
      _ ≤ Q * Q ^ E := mul_le_mul hEQ (Q_pow_le hX0 hX hE0) (Real.rpow_nonneg hX0 _) hQ0
      _ = Q ^ (E + 1) := Q_mul_one hQpos
  have hsupA' : ∀ δ ∈ A.coeff.support, 1 + Frob δ ≤ Q ^ (E + 2) := by
    intro δ hδ
    have h1 : Frob δ ≤ C_od * X ^ N_od := hsupA δ hδ
    have h2 : Frob δ ≤ Q ^ (E + 1) := by
      calc Frob δ ≤ C_od * X ^ N_od := h1
        _ ≤ E * X ^ E := mul_le_mul hE_Cod (Real.rpow_le_rpow_of_exponent_le hX1 hE_Nod)
            (Real.rpow_nonneg hX0 _) hE0
        _ ≤ Q * Q ^ E := mul_le_mul hEQ (Q_pow_le hX0 hX hE0) (Real.rpow_nonneg hX0 _) hQ0
        _ = Q ^ (E + 1) := Q_mul_one hQpos
    have h6 : (0:ℝ) ≤ Q ^ (E + 1) := Real.rpow_nonneg hQ0 _
    calc 1 + Frob δ ≤ 1 + Q ^ (E + 1) := by linarith
      _ ≤ Q ^ (E + 1) * Q := by
          have h8 : 1 + Q ^ (E + 1) ≤ 2 * Q ^ (E + 1) := by
            have h9 : (1:ℝ) ≤ Q ^ (E + 1) := Real.one_le_rpow hQ1 (by linarith)
            linarith
          have h9 : (2:ℝ) * Q ^ (E + 1) ≤ Q * Q ^ (E + 1) :=
            mul_le_mul_of_nonneg_right (by linarith) h6
          have h10 : Q * Q ^ (E + 1) = Q ^ (E + 1) * Q := mul_comm _ _
          linarith [h8, h9, h10.le, h10.ge]
      _ = Q ^ (E + 2) := by
          rw [Q_one_mul hQpos]
          congr 1
          ring
  have hsupB' : ∀ δ ∈ B.coeff.support, 1 + Frob δ ≤ Q ^ (E + 2) := by
    intro δ hδ
    have h1 : Frob δ ≤ C_od * X ^ N_od := hsupB δ hδ
    have h2 : Frob δ ≤ Q ^ (E + 1) := by
      calc Frob δ ≤ C_od * X ^ N_od := h1
        _ ≤ E * X ^ E := mul_le_mul hE_Cod (Real.rpow_le_rpow_of_exponent_le hX1 hE_Nod)
            (Real.rpow_nonneg hX0 _) hE0
        _ ≤ Q * Q ^ E := mul_le_mul hEQ (Q_pow_le hX0 hX hE0) (Real.rpow_nonneg hX0 _) hQ0
        _ = Q ^ (E + 1) := Q_mul_one hQpos
    have h6 : (0:ℝ) ≤ Q ^ (E + 1) := Real.rpow_nonneg hQ0 _
    calc 1 + Frob δ ≤ 1 + Q ^ (E + 1) := by linarith
      _ ≤ Q ^ (E + 1) * Q := by
          have h8 : 1 + Q ^ (E + 1) ≤ 2 * Q ^ (E + 1) := by
            have h9 : (1:ℝ) ≤ Q ^ (E + 1) := Real.one_le_rpow hQ1 (by linarith)
            linarith
          have h9 : (2:ℝ) * Q ^ (E + 1) ≤ Q * Q ^ (E + 1) :=
            mul_le_mul_of_nonneg_right (by linarith) h6
          have h10 : Q * Q ^ (E + 1) = Q ^ (E + 1) * Q := mul_comm _ _
          linarith [h8, h9, h10.le, h10.ge]
      _ = Q ^ (E + 2) := by
          rw [Q_one_mul hQpos]
          congr 1
          ring
  -- the master identity
  have hmaster : 2 * slash k (ofSL γ) f w
      = 2 * (∑ j : Fin 6, (sigmaHom γ) 0 j * slash k (MpElem j) f w)
        + (slash k A h₁ w + slash k B h₂ w) := by
    have h := congrFun (master_twist_odd k hk γ hT hS hEq) w
    simpa only [Pi.smul_apply, Pi.add_apply, Finset.sum_apply, smul_eq_mul] using h
  -- the factor of automorphy
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
  -- the six base terms
  have hbase : ‖∑ j : Fin 6, (sigmaHom γ) 0 j * slash k (MpElem j) f w‖ ≤ Cf * Q ^ BIG := by
    have h1 : ‖∑ j : Fin 6, (sigmaHom γ) 0 j * slash k (MpElem j) f w‖
        ≤ ∑ j : Fin 6, ‖(sigmaHom γ) 0 j * slash k (MpElem j) f w‖ := norm_sum_le _ _
    have h2 : ∀ j : Fin 6, ‖(sigmaHom γ) 0 j * slash k (MpElem j) f w‖
        ≤ Cf * Q ^ (4 * E ^ 2 + 16 * E + 2) := by
      intro j
      have hMpj : Mp j • w ∈ closure DomainD := Mp_smul_mem_closure_DomainD j hwF
      have hfrob : 1 + Frob (Mp j) ≤ Q ^ (E + 2) := by
        have h3 := MpFrob_le j
        have h4 : (3:ℝ) ≤ Q ^ (E + 2) := by
          have h5 : Q ≤ Q ^ (E + 2) := Q_le_self hQ1 hE0
          linarith
        linarith
      have hsc := scale_smul_Q (δ := Mp j) (M := M) hQ7 hM0 hE0 hfrob hY
      have hsc' : (scale (Mp j • w)) ^ M ≤ Q ^ (4 * E ^ 2 + 13 * E) := by
        refine le_trans hsc (Q_le hQ1 ?_)
        nlinarith [hM0, hE_M, hE0]
      have hfw : ‖f (Mp j • w)‖ ≤ Cf * Q ^ (4 * E ^ 2 + 13 * E) :=
        le_trans (hfM _ hMpj) (mul_le_mul_of_nonneg_left hsc' hCf)
      have hJ1 : ‖jFun (Mp j) (w : ℂ)‖ ^ (-k) ≤ Q ^ (2 * E + 1) := by
        have h3 : (1 + Frob (Mp j)) ^ N_j1 ≤ Q ^ E := by
          have h4 : (1 + Frob (Mp j)) ^ N_j1 ≤ Q ^ N_j1 := by
            have h7 : 1 + Frob (Mp j) ≤ Q := by
              have h8 := MpFrob_le j
              linarith
            exact Real.rpow_le_rpow (by linarith [Frob_nonneg (Mp j)]) h7 hN_j1
          exact le_trans h4 (Q_le hQ1 hE_Nj1)
        have h5 : (1 + scale w) ^ N_j1 ≤ Q ^ E := by
          have h6 : (1 + scale w) ^ N_j1 ≤ Q ^ N_j1 := Real.rpow_le_rpow hY0 hY hN_j1
          exact le_trans h6 (Q_le hQ1 hE_Nj1)
        calc ‖jFun (Mp j) (w : ℂ)‖ ^ (-k)
            ≤ C_j1 * (1 + Frob (Mp j)) ^ N_j1 * (1 + scale w) ^ N_j1 := hj1 (Mp j) w
          _ ≤ Q * Q ^ E * Q ^ E := by
              have hCj1Q : C_j1 ≤ Q := le_trans hE_Cj1 hEQ
              refine mul_le_mul (mul_le_mul hCj1Q h3
                (Real.rpow_nonneg (by linarith [Frob_nonneg (Mp j)]) _)
                (le_trans zero_le_one hQ1)) h5 (Real.rpow_nonneg hY0 _) ?_
              positivity
          _ = Q ^ (2 * E + 1) := by
              rw [Q_mul_one hQpos, Q_rewrite' hQpos (by ring : (E + 1) + E = 2 * E + 1)]
      have hsl : ‖slash k (MpElem j) f w‖ ≤ Cf * Q ^ (4 * E ^ 2 + 15 * E + 1) := by
        rw [MpElem_eq_MpR, slash_MpR, norm_slash]
        calc ‖f (Mp j • w)‖ * ‖jFun (Mp j) (w : ℂ)‖ ^ (-k)
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
      rw [norm_mul]
      calc ‖(sigmaHom γ) 0 j‖ * ‖slash k (MpElem j) f w‖
          ≤ Q ^ (E + 1) * (Cf * Q ^ (4 * E ^ 2 + 15 * E + 1)) :=
            mul_le_mul (hσ j) hsl (norm_nonneg _) (by positivity)
        _ = Cf * Q ^ ((E + 1) + (4 * E ^ 2 + 15 * E + 1)) := by
            rw [show Q ^ (E + 1) * (Cf * Q ^ (4 * E ^ 2 + 15 * E + 1))
                = Cf * (Q ^ (E + 1) * Q ^ (4 * E ^ 2 + 15 * E + 1)) by ring]
            rw [show Cf * (Q ^ (E + 1) * Q ^ (4 * E ^ 2 + 15 * E + 1))
                = Cf * Q ^ ((E + 1) + (4 * E ^ 2 + 15 * E + 1)) by rw [Q_mul_pow hQpos]]
        _ = Cf * Q ^ (4 * E ^ 2 + 16 * E + 2) := by
            congr 1
            ring
    have h3 : ∑ j : Fin 6, ‖(sigmaHom γ) 0 j * slash k (MpElem j) f w‖
        ≤ ∑ _j : Fin 6, Cf * Q ^ (4 * E ^ 2 + 16 * E + 2) :=
      Finset.sum_le_sum (fun j _ => h2 j)
    have h4 : ∑ _j : Fin 6, Cf * Q ^ (4 * E ^ 2 + 16 * E + 2)
        = 6 * (Cf * Q ^ (4 * E ^ 2 + 16 * E + 2)) := by
      simp [Finset.sum_const, Finset.card_univ, Finset.card_fin, nsmul_eq_mul]
    refine le_trans h1 (le_trans h3 ?_)
    rw [h4]
    calc 6 * (Cf * Q ^ (4 * E ^ 2 + 16 * E + 2))
        = (6 * Cf) * Q ^ (4 * E ^ 2 + 16 * E + 2) := by ring
      _ ≤ (Q ^ (2:ℝ) * Cf) * Q ^ (4 * E ^ 2 + 16 * E + 2) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ0 _)
          exact mul_le_mul_of_nonneg_right hQ6 hCf
      _ = Cf * Q ^ ((2:ℝ) + (4 * E ^ 2 + 16 * E + 2)) := by
          rw [show (Q ^ (2:ℝ) * Cf) * Q ^ (4 * E ^ 2 + 16 * E + 2)
              = Cf * (Q ^ (2:ℝ) * Q ^ (4 * E ^ 2 + 16 * E + 2)) by ring]
          rw [show Cf * (Q ^ (2:ℝ) * Q ^ (4 * E ^ 2 + 16 * E + 2))
              = Cf * Q ^ ((2:ℝ) + (4 * E ^ 2 + 16 * E + 2)) by rw [Q_mul_pow hQpos]]
      _ = Cf * Q ^ (4 * E ^ 2 + 16 * E + 4) := by
          congr 1
          ring
      _ ≤ Cf * Q ^ BIG :=
          mul_le_mul_of_nonneg_left (Q_le hQ1 (by rw [hBIGdef]; nlinarith [hE0])) hCf
  -- the defect terms
  have hd1 : ‖slash k A h₁ w‖ ≤ C₁ * Q ^ BIG :=
    slash_defect_Q (k := k) (A := A) (h := h₁) (C := C₁) (C_j := C_j1) (N_j := N_j1)
      (E := E) (s := s) (M := M) (Q := Q) (BIG := BIG)
      hj1 hE0 hQ7 hC₁ hE_Cj1 hE_Nj1 hEQ hN_j1 hM0 hE_M hE_BIG hh₁M hY hsupA' hcoefA'
  have hd2 : ‖slash k B h₂ w‖ ≤ C₂ * Q ^ BIG :=
    slash_defect_Q (k := k) (A := B) (h := h₂) (C := C₂) (C_j := C_j1) (N_j := N_j1)
      (E := E) (s := s) (M := M) (Q := Q) (BIG := BIG)
      hj1 hE0 hQ7 hC₂ hE_Cj1 hE_Nj1 hEQ hN_j1 hM0 hE_M hE_BIG hh₂M hY hsupB' hcoefB'
  have hdZ : ‖slash k A h₁ w + slash k B h₂ w‖ ≤ (C₁ + C₂) * Q ^ BIG := by
    have h5 := norm_add_le (slash k A h₁ w) (slash k B h₂ w)
    nlinarith [h5, hd1, hd2, hQ0B]
  -- the two sides
  have hsum : 2 * ‖slash k (ofSL γ) f w‖ ≤ 2 * ((Cf + C₁ + C₂) * Q ^ BIG) := by
    have h7 : 2 * ‖slash k (ofSL γ) f w‖ = ‖2 * slash k (ofSL γ) f w‖ := by
      rw [norm_mul]; norm_num
    rw [h7, hmaster]
    have ha : ‖2 * (∑ j : Fin 6, (sigmaHom γ) 0 j * slash k (MpElem j) f w)‖
        ≤ 2 * (Cf * Q ^ BIG) := by
      rw [norm_mul]
      have h8 : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [h8]
      exact mul_le_mul_of_nonneg_left hbase (by norm_num)
    have h9 := norm_add_le (2 * (∑ j : Fin 6, (sigmaHom γ) 0 j * slash k (MpElem j) f w))
      (slash k A h₁ w + slash k B h₂ w)
    nlinarith [h9, ha, hdZ, hQ0B, hCf, hC₁, hC₂]
  -- the bound for `f τ`
  have hfj : ‖f τ‖ = ‖slash k (ofSL γ) f w‖ * ‖jFun γ (w : ℂ)‖ ^ k := by
    have hjnz : jFun γ (w : ℂ) ≠ 0 := jFun_ne_zero γ w
    have h1 : slash k (ofSL γ) f w = f τ * (jFun γ (w : ℂ)) ^ (-k) := by
      rw [Work.Kernels.slash_single, one_smul, Work.Kernels.slash_apply', hγw]
    have h2 : f τ = slash k (ofSL γ) f w * (jFun γ (w : ℂ)) ^ k := by
      rw [h1, mul_assoc, ← zpow_add₀ hjnz, neg_add_cancel, zpow_zero, mul_one]
    rw [h2, norm_mul, norm_zpow]
  have hfin : ‖f τ‖ ≤ (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 2 * E + 205) := by
    rw [hfj]
    have h2 : 2 * (‖slash k (ofSL γ) f w‖ * ‖jFun γ (w : ℂ)‖ ^ k)
        = (2 * ‖slash k (ofSL γ) f w‖) * ‖jFun γ (w : ℂ)‖ ^ k := by ring
    have h3 : 2 * (‖slash k (ofSL γ) f w‖ * ‖jFun γ (w : ℂ)‖ ^ k)
        ≤ (2 * ((Cf + C₁ + C₂) * Q ^ BIG)) * Q ^ (2 * E + 1) := by
      rw [h2]
      exact mul_le_mul hsum hJfac (by positivity) (by positivity)
    have h4 : (2 * ((Cf + C₁ + C₂) * Q ^ BIG)) * Q ^ (2 * E + 1)
        = 2 * ((Cf + C₁ + C₂) * Q ^ (BIG + (2 * E + 1))) := by
      rw [show (2 * ((Cf + C₁ + C₂) * Q ^ BIG)) * Q ^ (2 * E + 1)
          = 2 * ((Cf + C₁ + C₂) * (Q ^ BIG * Q ^ (2 * E + 1))) by ring]
      rw [Q_mul_pow hQpos]
    rw [h4] at h3
    have h5 : Q ^ (BIG + (2 * E + 1)) ≤ Q ^ (60 * E ^ 2 + 2 * E + 205) := by
      refine Q_le hQ1 ?_
      rw [hBIGdef]; nlinarith [hE0, hE1]
    have h6 : (0:ℝ) ≤ Cf + C₁ + C₂ := by linarith
    have h7 : 2 * ((Cf + C₁ + C₂) * Q ^ (BIG + (2 * E + 1)))
        ≤ 2 * ((Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 2 * E + 205)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h5 h6) (by norm_num)
    linarith [h3, h7]
  -- conversion to the scale of `τ`
  have hQscale : Q ≤ (E * 2 ^ E) * s ^ E := by
    rw [hQdef, hsdef]
    have h1 : (1 + scale τ) ≤ 2 * scale τ := by linarith [one_le_scale τ]
    have h2 : (1 + scale τ) ^ E ≤ (2 * scale τ) ^ E :=
      Real.rpow_le_rpow (by linarith [scale_pos τ]) h1 hE0
    have h3 : (2 * scale τ) ^ E = 2 ^ E * (scale τ) ^ E := by
      rw [Real.mul_rpow (by norm_num) (le_of_lt (scale_pos τ))]
    calc E * (1 + scale τ) ^ E ≤ E * (2 * scale τ) ^ E := mul_le_mul_of_nonneg_left h2 hE0
      _ = (E * 2 ^ E) * (scale τ) ^ E := by rw [h3]; ring
  have h5 : Q ^ (60 * E ^ 2 + 2 * E + 205)
      ≤ (E * 2 ^ E) ^ (60 * E ^ 2 + 2 * E + 205) * (scale τ) ^ (E * (60 * E ^ 2 + 2 * E + 205)) := by
    have h6 : Q ^ (60 * E ^ 2 + 2 * E + 205) ≤ ((E * 2 ^ E) * s ^ E) ^ (60 * E ^ 2 + 2 * E + 205) :=
      Real.rpow_le_rpow hQ0 hQscale (by positivity)
    have h7 : ((E * 2 ^ E) * s ^ E) ^ (60 * E ^ 2 + 2 * E + 205)
        = (E * 2 ^ E) ^ (60 * E ^ 2 + 2 * E + 205) * (s ^ E) ^ (60 * E ^ 2 + 2 * E + 205) :=
      Real.mul_rpow (by positivity) (Real.rpow_nonneg (by positivity) _)
    have h8 : (s ^ E) ^ (60 * E ^ 2 + 2 * E + 205) = s ^ (E * (60 * E ^ 2 + 2 * E + 205)) :=
      (Real.rpow_mul (by positivity) E (60 * E ^ 2 + 2 * E + 205)).symm
    rw [h7, h8] at h6
    rw [hsdef] at h6
    exact h6
  calc ‖f τ‖ ≤ (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 2 * E + 205) := hfin
    _ ≤ (Cf + C₁ + C₂) * ((E * 2 ^ E) ^ (60 * E ^ 2 + 2 * E + 205)
          * (scale τ) ^ (E * (60 * E ^ 2 + 2 * E + 205))) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = ((E * 2 ^ E) ^ (60 * E ^ 2 + 2 * E + 205)) * (Cf + C₁ + C₂)
          * (scale τ) ^ (E * (60 * E ^ 2 + 2 * E + 205)) := by ring


end Work.Asymptotics

namespace Work.CKFinal

/-- CKMRV Proposition 3.2(2) with the constants chosen before the function: `C` and `N` depend
only on the weight `k` and the exponent `Nf`, and the bound is linear in `Cf + C₁ + C₂`. -/
theorem bound_of_propagates_uniform (k : ℤ) (Nf : ℝ) :
    ∃ C N : ℝ, 0 ≤ C ∧ 0 ≤ N ∧
      ∀ (f h₁ h₂ : UpperHalfPlane → ℂ) (Cf C₁ C₂ : ℝ),
        Work.Asymptotics.Propagates k Set.univ f h₁ h₂ →
        0 ≤ Cf → 0 ≤ C₁ → 0 ≤ C₂ →
        (∀ τ ∈ Work.Asymptotics.DomainD, ‖f τ‖ ≤ Cf * (Work.Kernels.scale τ) ^ Nf) →
        (∀ τ : UpperHalfPlane, ‖h₁ τ‖ ≤ C₁ * (Work.Kernels.scale τ) ^ Nf) →
        (∀ τ : UpperHalfPlane, ‖h₂ τ‖ ≤ C₂ * (Work.Kernels.scale τ) ^ Nf) →
        ∀ τ : UpperHalfPlane,
          ‖f τ‖ ≤ C * (Cf + C₁ + C₂) * (Work.Kernels.scale τ) ^ N := by
  rcases k.even_or_odd with hk | hk
  · exact Work.Asymptotics.bound_of_propagates_even_uniform k hk Nf
  · exact Work.Asymptotics.bound_of_propagates_odd_uniform k hk Nf

end Work.CKFinal
