/-
# CKMRV Proposition 3.2(2) at odd weight

The growth propagation `Work.Asymptotics.bound_of_propagates` at odd weights.  The argument is
the same as in `Submission/Work/Asymptotics/PropagateBounds/EvenBound.lean`, with the two
substitutions of the odd-weight setting:

* the defect ideal is `𝓘_odd = (T-I)²R + S(T-I)²R + (1+z)R`, whose third generator acts by `0` at
  odd weight (`Work.Asymptotics.slash_one_add_Rneg`), so the carries are polynomially bounded by
  `Work.Asymptotics.carry_bound_odd` (`Submission/Work/Asymptotics/carry_bound_odd.lean`);
* the reduction basis is `MpElem = (1, T⁻¹, STS, S, ST⁻¹, TS)`, i.e. already the basis whose six
  translates of `𝓕` lie in `𝒟`
  (`Work.Asymptotics.Mp_smul_mem_closure_DomainD`), so no change of basis is needed.
-/
import Mathlib
import Submission.Work.Asymptotics.PropagateBounds.EvenBound
import Submission.Work.Asymptotics.carry_bound_odd
import Submission.Work.Asymptotics.PropagateCarriesOdd

set_option maxHeartbeats 30000000

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels
open Work.Residues (M6 Rneg rowDiff sigmaR augIdeal)

/-- The slash of a carry combination along the odd ideal is the sum of the two carries applied to
the defects, at odd weight (where `1+z` acts by `0`). -/
lemma slash_carryCombOdd (k : ℤ) (hk : Odd k) (A B C : R) {f h₁ h₂ : ℍ → ℂ}
    (hT : T2op f = h₁) (hS : S2op k f = h₂) :
    slash k ((R_T - 1) ^ 2 * A + R_S * (R_T - 1) ^ 2 * B + (Rneg + 1) * C) f
      = slash k A h₁ + slash k B h₂ := by
  rw [Work.Kernels.slash_add, Work.Kernels.slash_add]
  rw [Work.Kernels.AlgebraFacts.slash_mul, Work.Kernels.slash_T2, hT]
  rw [show slash k (R_S * (R_T - 1) ^ 2 * B) f = slash k B (S2op k f) from by
    rw [Work.Kernels.AlgebraFacts.slash_mul]; rfl]
  rw [hS]
  rw [Work.Asymptotics.slash_augIdealOdd_mul_eq_zero k hk C f]
  ring

/-- **CKMRV Proposition 3.2(2) at odd weight.** -/
theorem bound_of_propagates_odd {k : ℤ} (hk : Odd k) {f h₁ h₂ : ℍ → ℂ}
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
  obtain ⟨C_od, N_od, hC_od, hN_od, hod⟩ := carry_bound_odd
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
  refine ⟨(E * 2 ^ E) ^ (60 * E ^ 2 + 2 * E + 205), E * (60 * E ^ 2 + 2 * E + 205), ?_, ?_,
    fun τ => ?_⟩
  · positivity
  · positivity
  set s : ℝ := scale τ with hsdef
  have hs1 : 1 ≤ s := by rw [hsdef]; exact one_le_scale τ
  obtain ⟨γ, w, hwF, hγw, hFrobγ, hscalew⟩ := hred τ
  obtain ⟨hσb, A, B, Cc, hEq, hcoefA, hcoefB, hsupA, hsupB⟩ := hod γ
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
  have hQ_mul_eq : ∀ a b : ℝ, Q ^ a * Q ^ b = Q ^ (a + b) := fun a b => Q_mul_pow hQpos
  -- the coefficients of the reduction
  have hσ : ∀ j : Fin 6, ‖(sigmaHom γ) 0 j‖ ≤ Q ^ (E + 1) := by
    intro j
    calc ‖(sigmaHom γ) 0 j‖ ≤ C_od * X ^ N_od := hσb 0 j
      _ ≤ E * X ^ E := mul_le_mul hE_Cod (Real.rpow_le_rpow_of_exponent_le (by linarith) hE_Nod)
          (Real.rpow_nonneg (by linarith) _) hE0
      _ ≤ Q * Q ^ E := mul_le_mul hEQ (Q_pow_le hX0 hX hE0) (Real.rpow_nonneg hX0 _) hQ0
      _ = Q ^ (E + 1) := Q_mul_one hQpos
  have hcoefA' : coeffNorm A ≤ Q ^ (E + 1) := by
    calc coeffNorm A ≤ C_od * X ^ N_od := hcoefA
      _ ≤ E * X ^ E := mul_le_mul hE_Cod (Real.rpow_le_rpow_of_exponent_le (by linarith) hE_Nod)
          (Real.rpow_nonneg (by linarith) _) hE0
      _ ≤ Q * Q ^ E := mul_le_mul hEQ (Q_pow_le hX0 hX hE0) (Real.rpow_nonneg hX0 _) hQ0
      _ = Q ^ (E + 1) := Q_mul_one hQpos
  have hcoefB' : coeffNorm B ≤ Q ^ (E + 1) := by
    calc coeffNorm B ≤ C_od * X ^ N_od := hcoefB
      _ ≤ E * X ^ E := mul_le_mul hE_Cod (Real.rpow_le_rpow_of_exponent_le (by linarith) hE_Nod)
          (Real.rpow_nonneg (by linarith) _) hE0
      _ ≤ Q * Q ^ E := mul_le_mul hEQ (Q_pow_le hX0 hX hE0) (Real.rpow_nonneg hX0 _) hQ0
      _ = Q ^ (E + 1) := Q_mul_one hQpos
  have hsupA' : ∀ δ ∈ A.coeff.support, 1 + Frob δ ≤ Q ^ (E + 2) := by
    intro δ hδ
    have h1 : Frob δ ≤ C_od * X ^ N_od := hsupA δ hδ
    have h2 : Frob δ ≤ Q ^ (E + 1) := by
      calc Frob δ ≤ C_od * X ^ N_od := h1
        _ ≤ E * X ^ E := mul_le_mul hE_Cod (Real.rpow_le_rpow_of_exponent_le (by linarith) hE_Nod)
            (Real.rpow_nonneg (by linarith) _) hE0
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
        _ ≤ E * X ^ E := mul_le_mul hE_Cod (Real.rpow_le_rpow_of_exponent_le (by linarith) hE_Nod)
            (Real.rpow_nonneg (by linarith) _) hE0
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
  have hmaster : slash k (ofSL γ) f w
      = (∑ j : Fin 6, (sigmaHom γ) 0 j • slash k (MpElem j) f w)
        + slash k A h₁ w + slash k B h₂ w := by
    have hsplit : ofSL γ = (∑ j : Fin 6, (sigmaHom γ) 0 j • MpElem j)
        + ((R_T - 1) ^ 2 * A + R_S * (R_T - 1) ^ 2 * B + (Rneg + 1) * Cc) := by
      rw [← hEq]
      abel
    have hc := slash_carryCombOdd k hk A B Cc hT hS
    rw [hsplit, Work.Kernels.slash_add, hc, slash_sum']
    simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
    abel
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
  have hbase : ‖∑ j : Fin 6, (sigmaHom γ) 0 j • slash k (MpElem j) f w‖
      ≤ Cf * Q ^ (60 * E ^ 2 + 202) := by
    have h1 : ‖∑ j : Fin 6, (sigmaHom γ) 0 j • slash k (MpElem j) f w‖
        ≤ ∑ j : Fin 6, ‖(sigmaHom γ) 0 j • slash k (MpElem j) f w‖ := norm_sum_le _ _
    have h2 : ∀ j : Fin 6, ‖(sigmaHom γ) 0 j • slash k (MpElem j) f w‖
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
      rw [norm_smul]
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
    refine le_trans h1 ?_
    calc ∑ j : Fin 6, ‖(sigmaHom γ) 0 j • slash k (MpElem j) f w‖
        ≤ ∑ _j : Fin 6, Cf * Q ^ (4 * E ^ 2 + 16 * E + 2) := Finset.sum_le_sum (fun j _ => h2 j)
      _ = 6 * (Cf * Q ^ (4 * E ^ 2 + 16 * E + 2)) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ (Q ^ (2:ℝ) * Cf) * Q ^ (4 * E ^ 2 + 16 * E + 2) := by
          have h6 : (6:ℝ) * Cf ≤ Q ^ (2:ℝ) * Cf := mul_le_mul_of_nonneg_right hQ6 hCf
          have h7 : 6 * (Cf * Q ^ (4 * E ^ 2 + 16 * E + 2))
              = ((6:ℝ) * Cf) * Q ^ (4 * E ^ 2 + 16 * E + 2) := by ring
          rw [h7]
          exact mul_le_mul_of_nonneg_right h6 (Real.rpow_nonneg hQ0 _)
      _ = Cf * (Q ^ (2:ℝ) * Q ^ (4 * E ^ 2 + 16 * E + 2)) := by ring
      _ = Cf * Q ^ ((2:ℝ) + (4 * E ^ 2 + 16 * E + 2)) := by
          rw [Q_mul_pow hQpos]
      _ ≤ Cf * Q ^ (60 * E ^ 2 + 202) := by
          apply mul_le_mul_of_nonneg_left _ hCf
          exact Q_le hQ1 (by nlinarith [hE1000])
  -- the two defect terms
  have hd1 : ‖slash k A h₁ w‖ ≤ C₁ * Q ^ (60 * E ^ 2 + 202) :=
    slash_defect_Q (k := k) (A := A) (h := h₁) (C := C₁) (C_j := C_j1) (N_j := N_j1)
      (E := E) (s := s) (M := M) (Q := Q) (BIG := 60 * E ^ 2 + 202)
      hj1 hE0 hQ7 hC₁ hE_Cj1 hE_Nj1 hEQ hN_j1 hM0 hE_M (by nlinarith [hE1000]) hh₁M hY hsupA' hcoefA'
  have hd2 : ‖slash k B h₂ w‖ ≤ C₂ * Q ^ (60 * E ^ 2 + 202) :=
    slash_defect_Q (k := k) (A := B) (h := h₂) (C := C₂) (C_j := C_j1) (N_j := N_j1)
      (E := E) (s := s) (M := M) (Q := Q) (BIG := 60 * E ^ 2 + 202)
      hj1 hE0 hQ7 hC₂ hE_Cj1 hE_Nj1 hEQ hN_j1 hM0 hE_M (by nlinarith [hE1000]) hh₂M hY hsupB' hcoefB'
  -- assembly
  have hsum : ‖slash k (ofSL γ) f w‖ ≤ (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 204) := by
    rw [hmaster]
    have hC0 : 0 ≤ Cf + C₁ + C₂ := by linarith
    have hbig : ∀ X : ℝ, X ≤ Cf * Q ^ (60 * E ^ 2 + 202) →
        X ≤ (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 202) := by
      intro X hX
      refine le_trans hX ?_
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hQ0 _)
    have hbig1 : ∀ X : ℝ, X ≤ C₁ * Q ^ (60 * E ^ 2 + 202) →
        X ≤ (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 202) := by
      intro X hX
      refine le_trans hX ?_
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hQ0 _)
    have hbig2 : ∀ X : ℝ, X ≤ C₂ * Q ^ (60 * E ^ 2 + 202) →
        X ≤ (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 202) := by
      intro X hX
      refine le_trans hX ?_
      exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hQ0 _)
    have h1 : ‖(∑ j : Fin 6, (sigmaHom γ) 0 j • slash k (MpElem j) f w) + slash k A h₁ w
        + slash k B h₂ w‖ ≤ 3 * ((Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 202)) := by
      have h2 := norm_add_le ((∑ j : Fin 6, (sigmaHom γ) 0 j • slash k (MpElem j) f w)
        + slash k A h₁ w) (slash k B h₂ w)
      have h3 := norm_add_le (∑ j : Fin 6, (sigmaHom γ) 0 j • slash k (MpElem j) f w)
        (slash k A h₁ w)
      have h4 := hbig _ hbase
      have h5 := hbig1 _ hd1
      have h6 := hbig2 _ hd2
      have h7 : (0:ℝ) ≤ (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 202) := by positivity
      linarith
    refine le_trans h1 ?_
    calc 3 * ((Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 202))
        = (3 * (Cf + C₁ + C₂)) * Q ^ (60 * E ^ 2 + 202) := by ring
      _ ≤ ((Cf + C₁ + C₂) * Q ^ (2:ℝ)) * Q ^ (60 * E ^ 2 + 202) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hQ0 _)
          have h6 : (3:ℝ) ≤ Q ^ (2:ℝ) := by linarith [hQ6]
          have h7 : (3:ℝ) * (Cf + C₁ + C₂) ≤ Q ^ (2:ℝ) * (Cf + C₁ + C₂) :=
            mul_le_mul_of_nonneg_right h6 hC0
          linarith [h7]
      _ = (Cf + C₁ + C₂) * Q ^ ((2:ℝ) + (60 * E ^ 2 + 202)) := by
          rw [show ((Cf + C₁ + C₂) * Q ^ (2:ℝ)) * Q ^ (60 * E ^ 2 + 202)
              = (Cf + C₁ + C₂) * (Q ^ (2:ℝ) * Q ^ (60 * E ^ 2 + 202)) by ring]
          rw [show (Cf + C₁ + C₂) * (Q ^ (2:ℝ) * Q ^ (60 * E ^ 2 + 202))
              = (Cf + C₁ + C₂) * Q ^ ((2:ℝ) + (60 * E ^ 2 + 202)) by rw [Q_mul_pow hQpos]]
      _ = (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 204) := by
          congr 1
          ring
  -- the bound for `f τ`
  have hfj : ‖f τ‖ = ‖slash k (ofSL γ) f w‖ * ‖jFun γ (w : ℂ)‖ ^ k := by
    have hjnz : jFun γ (w : ℂ) ≠ 0 := jFun_ne_zero γ w
    have h1 : slash k (ofSL γ) f w = f τ * (jFun γ (w : ℂ)) ^ (-k) := by
      rw [show ofSL γ = MonoidAlgebra.of ℂ SL(2,ℤ) γ from rfl, MonoidAlgebra.of_apply,
        Work.Kernels.slash_single, one_smul, Work.Kernels.slash_apply', hγw]
    have h2 : f τ = slash k (ofSL γ) f w * (jFun γ (w : ℂ)) ^ k := by
      rw [h1, mul_assoc, ← zpow_add₀ hjnz, neg_add_cancel, zpow_zero, mul_one]
    rw [h2, norm_mul, norm_zpow]
  have hfin : ‖f τ‖ ≤ (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 2 * E + 205) := by
    rw [hfj]
    calc ‖slash k (ofSL γ) f w‖ * ‖jFun γ (w : ℂ)‖ ^ k
        ≤ ((Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 204)) * Q ^ (2 * E + 1) :=
          mul_le_mul hsum hJfac (by positivity) (by positivity)
      _ = (Cf + C₁ + C₂) * Q ^ ((60 * E ^ 2 + 204) + (2 * E + 1)) := by
          rw [show ((Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 204)) * Q ^ (2 * E + 1)
              = (Cf + C₁ + C₂) * (Q ^ (60 * E ^ 2 + 204) * Q ^ (2 * E + 1)) by ring]
          rw [show (Cf + C₁ + C₂) * (Q ^ (60 * E ^ 2 + 204) * Q ^ (2 * E + 1))
              = (Cf + C₁ + C₂) * Q ^ ((60 * E ^ 2 + 204) + (2 * E + 1)) by rw [Q_mul_pow hQpos]]
      _ = (Cf + C₁ + C₂) * Q ^ (60 * E ^ 2 + 2 * E + 205) := by
          congr 1
          ring
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
      ≤ (E * 2 ^ E) ^ (60 * E ^ 2 + 2 * E + 205)
        * (scale τ) ^ (E * (60 * E ^ 2 + 2 * E + 205)) := by
    have h6 : Q ^ (60 * E ^ 2 + 2 * E + 205)
        ≤ ((E * 2 ^ E) * s ^ E) ^ (60 * E ^ 2 + 2 * E + 205) :=
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
