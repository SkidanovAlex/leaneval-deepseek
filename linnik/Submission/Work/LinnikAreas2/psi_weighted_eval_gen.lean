import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas2.PsiDefs2
import Submission.Work.LinnikAreas2.SmallPieceLe2
import Submission.Work.LinnikAreas2.mid_piece_le_gen
import Submission.Work.LinnikAreas2.far_piece_le_gen
import Submission.Work.LinnikAreas2.final_arith_gen
import Submission.Work.LinnikAreas2.psiSq_linear_bound
import Submission.Work.LinnikAreas2.summable_psiSq_mul_wt

namespace Work.LinnikAreas2

open scoped BigOperators
open Work.LinnikAreas.Density4

noncomputable section

/-- The constant `C₂ = Kc_gen ε C₁ u v x` of `psi_weighted_eval_gen`: at `C₁ = 1` it is the
constant `Kc ε u v x` of `psi_weighted_eval`. -/
def Kc_gen (ε C₁ u v x : ℝ) : ℝ :=
  12/u^3 + 6*(1+ε)/(v-u) + (1+ε)/(2*(v-u)^2*Lmin u x) + C₁/(v-u)
    + 6*C₁/((v-u)^2*Lmin u x) + C₁*(x-v)/(v-u)^2 + 1

/-- Split a sum over `Ico 1 N` at the two thresholds `A` and `B+1`. -/
private lemma sum_Ico_split3 {F : ℕ → ℝ} {A B N : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B + 1) :
    ∑ n ∈ Finset.Ico 1 N, F n
      = ∑ n ∈ Finset.Ico 1 (min N A), F n
        + ∑ n ∈ Finset.Ico (min N A) (min N (B+1)), F n
        + ∑ n ∈ Finset.Ico (min N (B+1)) N, F n := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; simp
  · have h1 : 1 ≤ min N A := le_min hN hA
    have h2 : min N A ≤ min N (B+1) := min_le_min_left N hAB
    have h3 : min N (B+1) ≤ N := min_le_left _ _
    have e1 := Finset.sum_Ico_consecutive F h1 (min_le_left N A)
    have e2 := Finset.sum_Ico_consecutive F h2 h3
    linarith

/-- The Abel boundary term `A(M)·φ(M)` of HB (11.14): `psSum U V M * phiW L U X M ≤ L²/U +
((1+ε)/log(V/U) + C₁/log(V/U)²)`.  This is the `hbdry` block of `psi_weighted_eval`, with the
constant `1` of the two hypotheses replaced by `C₁`.  (The case `V < M` consumes the large-`N`
hypothesis `h2`.) -/
private lemma boundary_le {ε C₁ L U V X : ℝ} (hε : 0 < ε) (hC₁ : 0 < C₁) (hU : 0 < U)
    (hX : 0 < X) (hU1 : 1 ≤ U) (hUV : U < V) (hcase : U ≤ L^2 * X)
    (h1 : ∀ N : ℕ, U ≤ (N:ℝ) → (N:ℝ) ≤ V →
      psSum U V N ≤ (1+ε) * (N:ℝ) * Real.log ((N:ℝ)/U) / (Real.log (V/U))^2
          + C₁ * (N:ℝ) / (Real.log (V/U))^2)
    (h2 : ∀ N : ℕ, V ≤ (N:ℝ) →
      psSum U V N ≤ (1+ε) * (N:ℝ) / Real.log (V/U) + C₁ * (N:ℝ) / (Real.log (V/U))^2)
    (M : ℕ) :
    psSum U V M * phiW L U X M
      ≤ L^2/U + ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) := by
  have hΛpos : 0 < Real.log (V/U) := by
    apply Real.log_pos
    rw [one_lt_div hU]
    exact hUV
  rcases Nat.eq_zero_or_pos M with hM0 | hMpos
  · subst hM0
    have h0 : psSum U V 0 = 0 := by simp [psSum]
    rw [h0, zero_mul]
    have hpos1 : 0 ≤ (1+ε)/Real.log (V/U) := div_nonneg (by linarith) hΛpos.le
    have hpos2 : 0 ≤ C₁/(Real.log (V/U))^2 := by positivity
    have hLU : 0 ≤ L^2/U := div_nonneg (sq_nonneg L) hU.le
    linarith
  · have hMposR : (0:ℝ) < (M:ℝ) := by exact_mod_cast hMpos
    have hphi : phiW L U X M = wt L U X M / M := rfl
    rw [hphi]
    by_cases hMU : (M:ℝ) ≤ U
    · have h1n : psSum U V M = 1 := psSum_eq_one hU1 hUV.le hMpos hMU
      have h2n : wt L U X M / M ≤ L^2/U := by
        rw [div_le_iff₀ hMposR]
        rw [mul_comm]
        exact wt_le_mul hU hX M
      rw [h1n, one_mul]
      have hpos1 : 0 ≤ (1+ε)/Real.log (V/U) := div_nonneg (by linarith) hΛpos.le
      have hpos2 : 0 ≤ C₁/(Real.log (V/U))^2 := by positivity
      linarith [h2n, hpos1, hpos2]
    · have hUlt : U < (M:ℝ) := not_le.mp hMU
      by_cases hMV : (M:ℝ) ≤ V
      · have h2n := h1 M hUlt.le hMV
        have hlog : Real.log ((M:ℝ)/U) ≤ Real.log (V/U) := by
          apply Real.log_le_log (by positivity)
          exact div_le_div_of_nonneg_right hMV hU.le
        have hmm : psSum U V M * wt L U X M / M
            ≤ ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) := by
          rw [div_le_iff₀ hMposR]
          have hwt : wt L U X M ≤ 1 := wt_le_one hU hX M
          have hwt0 : 0 ≤ wt L U X M := wt_nonneg hU hX hcase M
          have hcoef : (1+ε) * (M:ℝ) * Real.log ((M:ℝ)/U) / (Real.log (V/U))^2
                + C₁ * (M:ℝ) / (Real.log (V/U))^2
              ≤ (1+ε) * (M:ℝ) * Real.log (V/U) / (Real.log (V/U))^2
                + C₁ * (M:ℝ) / (Real.log (V/U))^2 := by
            apply add_le_add _ le_rfl
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hlog (by positivity)
          have hcoef0 : 0 ≤ (1+ε) * (M:ℝ) * Real.log (V/U) / (Real.log (V/U))^2
                + C₁ * (M:ℝ) / (Real.log (V/U))^2 := by
            have hlV : 0 ≤ Real.log (V/U) := le_of_lt hΛpos
            have hM0' : (0:ℝ) ≤ (M:ℝ) := le_of_lt hMposR
            positivity
          calc psSum U V M * wt L U X M
              ≤ ((1+ε) * (M:ℝ) * Real.log ((M:ℝ)/U) / (Real.log (V/U))^2
                  + C₁ * (M:ℝ) / (Real.log (V/U))^2) * wt L U X M :=
                mul_le_mul_of_nonneg_right h2n hwt0
            _ ≤ ((1+ε) * (M:ℝ) * Real.log (V/U) / (Real.log (V/U))^2
                  + C₁ * (M:ℝ) / (Real.log (V/U))^2) * 1 :=
                mul_le_mul hcoef hwt hwt0 hcoef0
            _ = ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * (M:ℝ) := by
                field_simp <;> ring
        rw [← mul_div_assoc]
        have hLU : 0 ≤ L^2/U := div_nonneg (sq_nonneg L) hU.le
        linarith [hmm, hLU]
      · have hVlt : V < (M:ℝ) := not_le.mp hMV
        have h2n := h2 M hVlt.le
        have hmm : psSum U V M * wt L U X M / M
            ≤ ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) := by
          rw [div_le_iff₀ hMposR]
          have hwt : wt L U X M ≤ 1 := wt_le_one hU hX M
          have hwt0 : 0 ≤ wt L U X M := wt_nonneg hU hX hcase M
          have hcoef0 : 0 ≤ (1+ε) * (M:ℝ) / Real.log (V/U)
              + C₁ * (M:ℝ) / (Real.log (V/U))^2 := by
            have hlV : 0 ≤ Real.log (V/U) := le_of_lt hΛpos
            have hM0' : (0:ℝ) ≤ (M:ℝ) := le_of_lt hMposR
            positivity
          calc psSum U V M * wt L U X M
              ≤ ((1+ε) * (M:ℝ) / Real.log (V/U) + C₁ * (M:ℝ) / (Real.log (V/U))^2)
                  * wt L U X M := mul_le_mul_of_nonneg_right h2n hwt0
            _ ≤ ((1+ε) * (M:ℝ) / Real.log (V/U) + C₁ * (M:ℝ) / (Real.log (V/U))^2) * 1 :=
                mul_le_mul le_rfl hwt hwt0 hcoef0
            _ = ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * (M:ℝ) := by ring
        rw [← mul_div_assoc]
        have hLU : 0 ≤ L^2/U := div_nonneg (sq_nonneg L) hU.le
        linarith [hmm, hLU]

/-- **HB (11.14) with an arbitrary constant in the Graham input.**

This is `Work.LinnikAreas.Density4.psi_weighted_eval` (proved) with the constant `C₁` of the two
hypotheses promoted from an existential *inside* the proof (where the proof takes `C₁ = 1`) to a
parameter.  Its proof consumes the hypothesis bounds only as upper bounds, so the argument is
unchanged; the conclusion's constant `C₂` then depends on `C₁`.

Note for the prover: the hardcoded `1` of the original lives in the sub-lemmas it consumes
(`mid_piece_le`, `far_piece_le` in `Submission/Work/LinnikAreas/Density4/`, and the final
arithmetic `final_arith`), which have the constant `1` written into their statements; they need
`C₁`-parameterized restatements (routine constant tracking).  Everything else in the proof of
`psi_weighted_eval` can be reused as is.

The reason for the restatement: the available supply of the Graham `ψ` upper bounds
(`Work.LinnikAreas2.graham_psi_sieve`, i.e. `graham_psi_sieve_of`) produces them with a constant
`C₁ ≥ 1` of its own, which the `C₁ = 1` interface of `psi_weighted_eval` cannot consume. -/
theorem psi_weighted_eval_gen (ε : ℝ) (hε : 0 < ε) :
    ∀ (u v x : ℝ), 0 < u → u < v → v < x → v - u ≤ x - v →
      ∀ C₁ : ℝ, 0 < C₁ → ∃ C₂ : ℝ, 0 < C₂ ∧
      ∀ (L U V X : ℝ), 0 < L → 1 ≤ U → U = Real.exp (u*L) → V = Real.exp (v*L) →
        X = Real.exp (x*L) → L^2 ≤ ε * U →
        (∀ N : ℕ, U ≤ (N:ℝ) → (N:ℝ) ≤ V →
          (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.psiM U V d)^2)
            ≤ (1+ε) * (N:ℝ) * Real.log ((N:ℝ)/U) / (Real.log (V/U))^2
                + C₁ * (N:ℝ) / (Real.log (V/U))^2) →
        (∀ N : ℕ, V ≤ (N:ℝ) →
          (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.psiM U V d)^2)
            ≤ (1+ε) * (N:ℝ) / Real.log (V/U) + C₁ * (N:ℝ) / (Real.log (V/U))^2) →
        (∑' n : ℕ, (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.psiM U V d)^2 * (n:ℝ)⁻¹ *
            (Real.exp (-(n:ℝ)/X) - Real.exp (-(n:ℝ)*L^2/U)))
          ≤ (1+ε) * ((2*x-u-v)/(2*(v-u))) + C₂ / L := by
  intro u v x hu huv hvx hΔ
  have hvu : 0 < v - u := by linarith
  have hxv : 0 < x - v := by linarith
  have hLminpos : 0 < Lmin u x := lt_min one_pos (Real.exp_pos _)
  have hLminle1 : Lmin u x ≤ 1 := min_le_left _ _
  intro C₁ hC₁
  refine ⟨Kc_gen ε C₁ u v x, ?_, ?_⟩
  · rw [Kc_gen]; positivity
  intro L U V X hL hU1 hUe hVe hXe hL2U h1 h2
  show (∑' n : ℕ, psiSq U V n * (n:ℝ)⁻¹ * wt L U X n)
      ≤ (1+ε) * ((2*x-u-v)/(2*(v-u))) + Kc_gen ε C₁ u v x / L
  -- elementary facts
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU1
  have hXpos : 0 < X := by rw [hXe]; exact Real.exp_pos _
  have hVpos : 0 < V := by rw [hVe]; exact Real.exp_pos _
  have hUV : U ≤ V := by rw [hUe, hVe]; exact Real.exp_le_exp.mpr (by nlinarith)
  have hUVlt : U < V := by rw [hUe, hVe]; exact Real.exp_lt_exp.mpr (by nlinarith)
  have hVX : V ≤ X := by rw [hVe, hXe]; exact Real.exp_le_exp.mpr (by nlinarith)
  have hV1 : 1 ≤ V := le_trans hU1 hUV
  have hΛpos : 0 < Real.log (V/U) := by
    apply Real.log_pos
    rw [one_lt_div hUpos]
    exact hUVlt
  have hΛeq : Real.log (V/U) = (v-u)*L := by
    rw [hVe, hUe, ← Real.exp_sub, Real.log_exp]
    ring
  have hlogXV : Real.log (X/V) = (x-v)*L := by
    rw [hXe, hVe, ← Real.exp_sub, Real.log_exp]
    ring
  -- the crude linear bound on the partial sums (used for summability)
  have hAle : ∀ n : ℕ, psiSq U V n
      ≤ max 1 ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * n :=
    psiSq_linear_bound hε hC₁ hUpos hUVlt hU1 h1 h2
  have hA0 : (0:ℝ) ≤ max 1 ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) :=
    le_trans zero_le_one (le_max_left _ _)
  -- summability
  have hsumm : Summable (fun n : ℕ => psiSq U V n * (n:ℝ)⁻¹ * wt L U X n) :=
    summable_psiSq_mul_wt hL hUpos hXpos hA0 hAle
  -- case split on the sign of the weight
  by_cases hcase : U ≤ L^2 * X
  · -- Case 1: the weight is nonnegative
    have hLge : Lmin u x ≤ L := by
      rw [Lmin, min_le_iff]
      by_cases hLgt1 : 1 < L
      · exact Or.inl (le_of_lt hLgt1)
      · have hLle1 : L ≤ 1 := le_of_not_gt hLgt1
        refine Or.inr ?_
        have h1' : 1 ≤ L^2 * Real.exp ((x-u)*L) := by
          have h := hcase
          rw [hUe, hXe] at h
          have hpos : 0 < Real.exp (u*L) := Real.exp_pos _
          have h2' : Real.exp (u*L) / Real.exp (u*L) ≤ (L^2 * Real.exp (x*L)) / Real.exp (u*L) :=
            div_le_div_of_nonneg_right h hpos.le
          have h3' : (L^2 * Real.exp (x*L)) / Real.exp (u*L) = L^2 * Real.exp ((x-u)*L) := by
            rw [mul_div_assoc, ← Real.exp_sub]
            congr 1
            ring
          rw [div_self (ne_of_gt hpos)] at h2'
          rw [h3'] at h2'
          exact h2'
        have hexp : Real.exp ((x-u)*L) ≤ Real.exp (x-u) := by
          apply Real.exp_le_exp.mpr
          nlinarith
        have hsq2 : Real.exp (-(x-u)) ≤ L^2 := by
          have h4 : L^2 * Real.exp ((x-u)*L) ≤ L^2 * Real.exp (x-u) :=
            mul_le_mul_of_nonneg_left hexp (sq_nonneg L)
          have h5 : 1 ≤ L^2 * Real.exp (x-u) := le_trans h1' h4
          have hE : 0 < Real.exp (x-u) := Real.exp_pos _
          rw [Real.exp_neg]
          calc (Real.exp (x-u))⁻¹ = 1 / Real.exp (x-u) := by rw [one_div]
            _ ≤ L^2 := by
                rw [div_le_iff₀ hE]
                linarith [h5]
        have hsq : (Real.exp (-(x-u)/2))^2 ≤ L^2 := by
          have h6 : (Real.exp (-(x-u)/2))^2 = Real.exp (-(x-u)) := by
            rw [sq, ← Real.exp_add]
            congr 1
            ring
          rw [h6]
          exact hsq2
        have hc := sq_le_sq.mp hsq
        rwa [abs_of_nonneg (Real.exp_pos _).le, abs_of_pos hL] at hc
    -- partial summation
    have hpartial : ∀ M : ℕ, ∑ n ∈ Finset.Icc 1 M, psiSq U V n * (n:ℝ)⁻¹ * wt L U X n
        ≤ (1+ε) * (1/2 + (x-v)/(v-u)) + Kc_gen ε C₁ u v x / L := by
      intro M
      have hk : ∀ n : ℕ, 1 ≤ n → 0 ≤ phiW L U X n - phiW L U X (n+1) :=
        fun n hn => phiW_sub_nonneg hUpos hXpos hcase hn
      have hcongr : ∑ n ∈ Finset.Icc 1 M, psiSq U V n * (n:ℝ)⁻¹ * wt L U X n
          = ∑ n ∈ Finset.Icc 1 M, psiSq U V n * phiW L U X n := by
        apply Finset.sum_congr rfl
        intro n _
        rw [phiW, div_eq_mul_inv]
        ring
      rw [hcongr]
      have habel := abel_sum_Icc (fun n => psiSq U V n) (phiW L U X) M
      have hAb : ∑ n ∈ Finset.Icc 1 M, psiSq U V n * phiW L U X n
          = psSum U V M * phiW L U X M
            + ∑ n ∈ Finset.Icc 1 (M-1), psSum U V n * (phiW L U X n - phiW L U X (n+1)) := by
        rw [habel]
        simp only [psSum]
      rw [hAb, sum_Icc_one_eq_sum_Ico]
      -- boundary term
      have hbdry : psSum U V M * phiW L U X M
          ≤ L^2/U + ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) :=
        boundary_le hε hC₁ hUpos hXpos hU1 hUVlt hcase h1 h2 M
      -- the three pieces
      have hA1 : 1 ≤ Nat.floor U + 1 := by omega
      have hAB1 : Nat.floor U + 1 ≤ Nat.floor V + 1 := by
        have hfm := Nat.floor_mono (le_of_lt hUVlt)
        omega
      have hsplit := sum_Ico_split3 (F := fun n => psSum U V n * (phiW L U X n - phiW L U X (n+1)))
        (A := Nat.floor U + 1) (B := Nat.floor V) (N := M) hA1 hAB1
      rw [hsplit]
      have hp1 : ∑ n ∈ Finset.Ico 1 (min M (Nat.floor U + 1)),
            psSum U V n * (phiW L U X n - phiW L U X (n+1)) ≤ L^2/U :=
        small_piece_le hUpos hXpos hU1 hUV hcase (min M (Nat.floor U + 1)) (min_le_right _ _)
      have hsub : Finset.Ico (min M (Nat.floor U + 1)) (min M (Nat.floor V + 1))
          ⊆ Finset.Ico (Nat.floor U + 1) (Nat.floor V + 1) := by
        intro n hn
        simp only [Finset.mem_Ico] at hn ⊢
        omega
      have hp2 : ∑ n ∈ Finset.Ico (min M (Nat.floor U + 1)) (min M (Nat.floor V + 1)),
            psSum U V n * (phiW L U X n - phiW L U X (n+1))
          ≤ (1+ε)/2
            + (1+ε)*(1/Real.log (V/U) + 1/(V*Real.log (V/U)) + 1/(2*V^2*(Real.log (V/U))^2))
            + C₁*(1/Real.log (V/U) + 1/(Real.log (V/U))^2 + 1/(V*(Real.log (V/U))^2)) := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub ?_)
          (mid_piece_le_gen hε hC₁ hL hUpos hXpos hU1 hUVlt hcase h1)
        intro n hn _
        have hn1 : 1 ≤ n := by simp only [Finset.mem_Ico] at hn; omega
        exact mul_nonneg (psSum_nonneg U V n) (hk n hn1)
      have hsub2 : Finset.Ico (min M (Nat.floor V + 1)) M ⊆ Finset.Ico (Nat.floor V + 1) M := by
        intro n hn
        simp only [Finset.mem_Ico] at hn ⊢
        omega
      have hp3 : ∑ n ∈ Finset.Ico (min M (Nat.floor V + 1)) M,
            psSum U V n * (phiW L U X n - phiW L U X (n+1))
          ≤ ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * ((x-v)*L + 3) := by
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub2 ?_) ?_
        · intro n hn _
          have hn1 : 1 ≤ n := by simp only [Finset.mem_Ico] at hn; omega
          exact mul_nonneg (psSum_nonneg U V n) (hk n hn1)
        · have hfp := far_piece_le_gen (ε := ε) (C₁ := C₁) (L := L) (U := U) (V := V) (X := X)
            hε hC₁ hUpos hXpos hU1 hUVlt hVX hcase h2 M
          rwa [hlogXV] at hfp
      -- assemble
      set Bd : ℝ := L^2/U + ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) with hBd
      set MidB : ℝ := (1+ε)/2
            + (1+ε)*(1/Real.log (V/U) + 1/(V*Real.log (V/U)) + 1/(2*V^2*(Real.log (V/U))^2))
            + C₁*(1/Real.log (V/U) + 1/(Real.log (V/U))^2 + 1/(V*(Real.log (V/U))^2)) with hMidB
      set FarB : ℝ := ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * ((x-v)*L + 3) with hFarB
      have htot : psSum U V M * phiW L U X M
            + (∑ n ∈ Finset.Ico 1 (min M (Nat.floor U + 1)),
                psSum U V n * (phiW L U X n - phiW L U X (n+1))
              + ∑ n ∈ Finset.Ico (min M (Nat.floor U + 1)) (min M (Nat.floor V + 1)),
                psSum U V n * (phiW L U X n - phiW L U X (n+1))
              + ∑ n ∈ Finset.Ico (min M (Nat.floor V + 1)) M,
                psSum U V n * (phiW L U X n - phiW L U X (n+1)))
          ≤ Bd + (L^2/U + MidB) + FarB := by
        rw [hBd, hMidB, hFarB]
        linarith [hbdry, hp1, hp2, hp3]
      have hfar_main : ((1+ε)/Real.log (V/U) + C₁/(Real.log (V/U))^2) * ((x-v)*L + 3)
          = (1+ε)*(x-v)/(v-u) + (3*(1+ε)/Real.log (V/U) + C₁*(x-v)*L/(Real.log (V/U))^2
              + 3*C₁/(Real.log (V/U))^2) := by
        rw [hΛeq]
        field_simp
        ring
      set E : ℝ := 2*L^2/U + 5*(1+ε)/Real.log (V/U) + (1+ε)/(V*Real.log (V/U))
          + (1+ε)/(2*V^2*(Real.log (V/U))^2) + C₁/Real.log (V/U) + 5*C₁/(Real.log (V/U))^2
          + C₁/(V*(Real.log (V/U))^2) + C₁*(x-v)*L/(Real.log (V/U))^2 with hE
      have hEbound : Bd + (L^2/U + MidB) + FarB
          ≤ (1+ε) * (1/2 + (x-v)/(v-u)) + Kc_gen ε C₁ u v x / L := by
        have hdecomp : Bd + (L^2/U + MidB) + FarB = (1+ε) * (1/2 + (x-v)/(v-u)) + E := by
          rw [hBd, hMidB, hFarB, hfar_main, hE]
          ring
        have hE2 : E ≤ Kc_gen ε C₁ u v x / L := by
          rw [le_div_iff₀ hL, mul_comm]
          exact final_arith_gen (ε := ε) (C₁ := C₁) (u := u) (v := v) (x := x) (L := L)
            (U := U) (V := V) (L₁ := Lmin u x) hε hC₁ hu hvu hxv hL hLminpos hLge hV1 hUe hVe
        rw [hdecomp]
        linarith [hE2]
      linarith [htot, hEbound]
    -- pass to the tsum
    have hnonneg : ∀ n : ℕ, 0 ≤ psiSq U V n * (n:ℝ)⁻¹ * wt L U X n := by
      intro n
      exact mul_nonneg (mul_nonneg (psiSq_nonneg U V n) (by positivity))
        (wt_nonneg hUpos hXpos hcase n)
    have hkey : ∀ N : ℕ, ∑ n ∈ Finset.range N, psiSq U V n * (n:ℝ)⁻¹ * wt L U X n
        ≤ (1+ε) * (1/2 + (x-v)/(v-u)) + Kc_gen ε C₁ u v x / L := by
      intro N
      have h0 : psiSq U V 0 * (0:ℝ)⁻¹ * wt L U X 0 = 0 := by simp [psiSq]
      have hrw : ∑ n ∈ Finset.range N, psiSq U V n * (n:ℝ)⁻¹ * wt L U X n
          = ∑ n ∈ Finset.Ico 1 N, psiSq U V n * (n:ℝ)⁻¹ * wt L U X n := by
        rw [Finset.range_eq_Ico]
        rcases Nat.eq_zero_or_pos N with hN0 | hNpos
        · subst hN0; simp
        · rw [← Finset.sum_Ico_consecutive
            (f := fun n => psiSq U V n * (n:ℝ)⁻¹ * wt L U X n) (show 0 ≤ 1 by omega) hNpos]
          simp [h0]
      rw [hrw, ← sum_Icc_one_eq_sum_Ico N]
      exact hpartial (N-1)
    have hlim := hsumm.hasSum.tendsto_sum_nat
    have hconv : (1+ε) * (1/2 + (x-v)/(v-u))
        = (1+ε) * ((2*x-u-v)/(2*(v-u))) := by
      field_simp
      ring
    have hle := le_of_tendsto_of_tendsto hlim tendsto_const_nhds (Filter.Eventually.of_forall hkey)
    calc (∑' n : ℕ, psiSq U V n * (n:ℝ)⁻¹ * wt L U X n)
        ≤ (1+ε) * (1/2 + (x-v)/(v-u)) + Kc_gen ε C₁ u v x / L := hle
      _ = (1+ε) * ((2*x-u-v)/(2*(v-u))) + Kc_gen ε C₁ u v x / L := by rw [hconv]
  · -- Case 2: L² X < U, all weights are nonpositive
    push_neg at hcase
    have hw_nonpos : ∀ n : ℕ, wt L U X n ≤ 0 := by
      intro n
      rw [wt]
      apply sub_nonpos.mpr
      apply Real.exp_le_exp.mpr
      have hn : (0:ℝ) ≤ (n:ℝ) := by positivity
      have hle : (n:ℝ)*L^2/U ≤ (n:ℝ)/X := by
        rw [div_le_div_iff₀ hUpos hXpos]
        nlinarith [hcase, hn]
      have e1 : -(n:ℝ)*L^2/U = -((n:ℝ)*L^2/U) := by ring
      have e2 : -(n:ℝ)/X = -((n:ℝ)/X) := by ring
      rw [e1, e2]
      linarith
    have hterm : ∀ n : ℕ, psiSq U V n * (n:ℝ)⁻¹ * wt L U X n ≤ 0 := by
      intro n
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (psiSq_nonneg U V n) (by positivity)) (hw_nonpos n)
    have h0 : (∑' n : ℕ, psiSq U V n * (n:ℝ)⁻¹ * wt L U X n) ≤ 0 := by
      have hh := Summable.tsum_le_tsum hterm hsumm summable_zero
      simpa using hh
    have hpos : 0 < (1+ε) * ((2*x-u-v)/(2*(v-u))) + Kc_gen ε C₁ u v x / L := by
      have h1' : 0 < (2*x-u-v)/(2*(v-u)) := by
        apply div_pos _ (by linarith)
        linarith
      have h2' : 0 < Kc_gen ε C₁ u v x / L := div_pos (by rw [Kc_gen]; positivity) hL
      have h3' : 0 < (1+ε) * ((2*x-u-v)/(2*(v-u))) := mul_pos (by linarith) h1'
      linarith
    linarith [h0, hpos]

end

end Work.LinnikAreas2
