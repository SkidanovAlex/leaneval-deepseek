import Submission.ZagierHoffmanProof.KuanLin
import Submission.ZagierHoffmanProof.Step2Complete
import Submission.ZagierHoffmanProof.AbpDescentRestrict

/-!
# Dac §3.3 — Theorem `linear independence`, packaged

This file assembles the pieces of Dac's Theorem (linear independence) into a single theorem:

* `TmApply.tmABP_a_leading` (Steps 1–2, leading-weight relation) — here in its `K^{perf}` version
  `tmABP_a_leading_kperf`, which additionally produces the ABP row `P` with **`K^{perf}`
  coefficients** (as required by `Step2Complete.step2_B_zero`);
* `Step2Complete.step2_B_zero` (the vanishing of all the coefficients `B̃` of the second relation);
* `Rationality.tmF_eval_mem_ambK` (the rationality/endgame: `f_{t;Q}(θ) ∈ K`).

The conclusion is exactly Dac's: for every `(t;Q) ∈ I`, `f_{t;Q}(θ) = tmF … t` evaluates at `θ` to
an element of `K = F_q(θ)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
open Polynomial PowerSeries Finset Matrix
open scoped WithZero Topology Classical

namespace ZagierHoffmanPositiveChar

variable {F : Type*} [Field F] [Finite F]

/-! ## §1. The ABP criterion applied to the augmented first column, with `K^{perf}` coefficients -/

section AugmentedKperf

variable {S : Finset (List (ℕ × Polynomial (Ambient F)))}
variable {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}

/-- `tmRho` has `K^{perf}`-coefficients (it is `1` at `none` and `0` elsewhere). -/
lemma tmRho_mem_ambKperf (j : Option ↥(tmI S)) : tmRho F S j ∈ ambKperf F := by
  rcases j with _ | t
  · rw [tmRho_none]; exact Subfield.one_mem _
  · rw [tmRho_some]; exact (ambKperf F).zero_mem

/-- **The ABP criterion for the merged dual `t`-motive, with Dac's constant term `a` and the
`K^{perf}`-membership of the output row** (Dac §5.1 / §5.2 Step 1). -/
theorem tmABP_a_kperf {γ : ℚᵐ⁰} (hγ0 : 0 < γ) (hγ : γ < 1) (harch : GammaArchimedean ℚᵐ⁰)
    (hq : 2 ≤ Nat.card F)
    {w : ℕ} {ω : PowerSeries (Ambient F)} (hω : GIsSmall γ ω) (hωse : GSuperEntire γ ω)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω)
    (hw : ∀ s ∈ S, tmWeight s = w)
    (hcf : ∀ s ∈ S, frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (hne : ∀ s ∈ S, s ≠ [])
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S)
    (hA : ∀ i j m,
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j).coeff m ∈ ambA F 0)
    {a : Polynomial (Ambient F)}
    (ha : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hval : evalSeriesGen (tmF (Nat.card F) ω w S cf
        ([] : List (ℕ × Polynomial (Ambient F)))) (ambTheta F) + a.eval (ambTheta F) = 0) :
    ∃ P : Option ↥(tmI S) → Polynomial (Ambient F),
      (∑ j, coeHom (K := Ambient F) (P j) * tmPsiColA F ω w S cf h0 a j = 0) ∧
      (∀ j, (P j).eval (ambTheta F) = tmRho F S j) ∧
      (∀ j m, (P j).coeff m ∈ ambKperf F) := by
  classical
  have hℓ : 2 ≤ Fintype.card (Option ↥(tmI S)) := by
    rw [Fintype.card_option]
    exact Nat.succ_le_succ (Fintype.card_pos_iff.mpr ⟨⟨[], h0⟩⟩)
  have hJ : Fintype.card ↥(tmI S) = Fintype.card (Option ↥(tmI S)) - 1 := by
    rw [Fintype.card_option]
    omega
  have hϑ : ∀ i j, tmTheta F S i j ∈ ambA F 1 := by
    intro i j
    by_cases h : i = some j
    · simp only [tmTheta, if_pos h]; exact ambA_one_mem F 1
    · simp only [tmTheta, if_neg h]; exact (ambASub F 1).zero_mem
  have hdet : (tmPhi F (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) hA).det
      = Polynomial.C (1 : Ambient F) * (Polynomial.X - Polynomial.C (ambTheta F)) ^
        (∑ t : ↥(tmI S), (w - tmWeight t.1)) := by
    rw [det_tmPhi F w S cf hA]
    simp
  have hse' := tmPsiColA_superEntire F (w := w) (cf := cf) hγ0 hγ harch hq hω hωse hsm hSse h0 a
  have hFse : GSuperEntire γ (tmF (Nat.card F) ω w S cf
      ([] : List (ℕ × Polynomial (Ambient F)))) := by
    have h := tmPsiCol_superEntire F (w := w) (ω := ω) (cf := cf) hγ0 hγ harch hq hω hωse hsm
      hSse h0 (none : Option ↥(tmI S))
    simpa using h
  have hAa : GSuperEntire γ (((a : Polynomial (Ambient F)) : PowerSeries (Ambient F))) :=
    GSuperEntire.polynomial hγ0 hγ.le a
  have hval' : dotProduct (tmRho F S)
      (fun i => evalSeriesGen (tmPsiColA F ω w S cf h0 a i) (ambTheta F)) = 0 := by
    rw [dotProduct_tmRho, tmPsiColA_none,
      evalSeriesGen_add hγ harch hFse hAa (ambTheta F), evalSeriesGen_polynomial]
    exact hval
  exact ABP_criterion_of_fintype_kperf (F := F) (ι := Option ↥(tmI S))
    (J := ↥(tmI S)) 1 hℓ hJ
    (tmPhi_coeff_mem F (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) hA)
    hϑ hγ0 hγ hse'
    (tmPsiColA_functional F hγ harch hq hω hωfe hw hcf hsm hne h0 hA ha)
    (linearIndependent_tmTheta F S)
    (vecMul_tmRho_tmTheta F S) (tmRho_ne_zero F S) (tmRho_mem_ambKperf (F := F))
    hval' one_ne_zero hdet

end AugmentedKperf

/-! ## §2. The leading-weight relation, with `K^{perf}` coefficients -/

section Leading

variable {S : Finset (List (ℕ × Polynomial (Ambient F)))}
variable {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}

/-- **Dac §5.2 Step 1+2, with the `K^{perf}`-membership.** -/
theorem tmABP_a_leading_kperf {γ : ℚᵐ⁰} (hγ0 : 0 < γ) (hγ : γ < 1)
    (harch : GammaArchimedean ℚᵐ⁰) (hq : 2 ≤ Nat.card F)
    {w : ℕ} {ω : PowerSeries (Ambient F)} (hω : GIsSmall γ ω)
    (hωse : GSuperEntire γ ω) (hω0 : ω.coeff 0 ≠ 0)
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ k)) = 0)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω)
    (hw : ∀ s ∈ S, tmWeight s = w)
    (hcf : ∀ s ∈ S, frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (hne : ∀ s ∈ S, s ≠ [])
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S)
    (hA : ∀ i j m,
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j).coeff m ∈ ambA F 0)
    {a : Polynomial (Ambient F)}
    (ha : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hval : evalSeriesGen (tmF (Nat.card F) ω w S cf
        ([] : List (ℕ × Polynomial (Ambient F)))) (ambTheta F) + a.eval (ambTheta F) = 0)
    {w₀ : ℕ} (hw₀ : ∀ t : ↥(tmI S), tmWeight t.1 ≤ w₀) (hw₀le : w₀ ≤ w) :
    ∃ P : Option ↥(tmI S) → Polynomial (Ambient F),
      (∑ j, coeHom (K := Ambient F) (P j) * tmPsiColA F ω w S cf h0 a j = 0) ∧
      (∀ j, (P j).eval (ambTheta F) = tmRho F S j) ∧
      (∀ j m, (P j).coeff m ∈ ambKperf F) ∧
      (∀ j : ℕ, 2 ≤ j →
        (∑ t ∈ Finset.univ.filter (fun t : ↥(tmI S) => tmWeight t.1 = w₀),
          (tmB F w S cf P (some t)).eval ((ambTheta F) ^ (Nat.card F) ^ j)
            * (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ j)) = 0) := by
  classical
  obtain ⟨P, hP, hPθ, hPmem⟩ :=
    tmABP_a_kperf (F := F) hγ0 hγ harch hq hω hωse hωfe hw hcf hsm hSse hne h0 hA ha hval
  refine ⟨P, hP, hPθ, hPmem, ?_⟩
  have hfe : tmPsiColA F ω w S cf h0 a
      = (coeHom (K := Ambient F)).mapMatrix
          (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) *ᵥ
        frobTwistVec (q := Nat.card F) 1 (tmPsiColA F ω w S cf h0 a) := by
    have hfun := tmPsiColA_functional F (w := w) (ω := ω) (cf := cf) (a := a) hγ harch hq hω
      hωfe hw hcf hsm hne h0 hA ha
    rw [tmPhi_twist_mat F _ hA] at hfun
    exact hfun
  have hΩ0 : (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω).coeff 0 ≠ 0 := by
    rw [frobTwist_coeff, pow_one]
    exact pow_ne_zero _ hω0
  have hΩ1 : ∀ j : ℕ, 2 ≤ j →
      evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
        ((ambTheta F) ^ (Nat.card F) ^ j) = 0 := by
    intro j hj
    have hq1 : ((ambTheta F) ^ (Nat.card F ^ (j - 1))) ^ (Nat.card F ^ 1)
        = (ambTheta F) ^ (Nat.card F) ^ j := by
      rw [pow_one, ← pow_mul]
      congr 1
      conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ j by omega)]
      rw [pow_succ]
    have h := evalSeriesGen_frobTwist hγ harch (Nat.card F) hωse
      ((ambTheta F) ^ (Nat.card F ^ (j - 1))) 1
    rw [hq1] at h
    have h2 : evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ (j - 1))) = 0 :=
      hc (j - 1) (by omega)
    rw [h2] at h
    have hz : (0 : Ambient F) ^ (Nat.card F ^ 1) = 0 :=
      zero_pow (pow_ne_zero 1 (FrobPow.ne_zero (Ambient F) (q := Nat.card F)))
    rw [hz] at h
    exact h
  have hMZ : ∀ (t : ↥(tmI S)) (k : ℕ),
      evalSeriesGen (tmL (Nat.card F) ω t.1) ((ambTheta F) ^ (Nat.card F ^ k))
        = (evalSeriesGen (tmL (Nat.card F) ω t.1) (ambTheta F)) ^ (Nat.card F ^ k) :=
    fun t k => tmL_frobenius_pow F hγ0 hγ harch hq hω hωse hsm hSse hpos hc t k
  have hLse : ∀ t : ↥(tmI S), GSuperEntire γ (tmL (Nat.card F) ω t.1) :=
    fun t => gSuperEntire_tmL F hγ harch hq hω hωse hsm hSse t
  exact tmB_eval_zero F hγ0 hγ harch hωse hΩ0 hΩ1 hMZ hLse h0 hA hfe hP hw₀ hw₀le

end Leading

/-! ## §3. The capstone -/

section Capstone

variable {S : Finset (List (ℕ × Polynomial (Ambient F)))}
variable {cf : List (ℕ × Polynomial (Ambient F)) → Polynomial (Ambient F)}

/-- **Dac's Theorem (linear independence), §3.3**: under (LW) and (LD), every entry
`f_{t;Q}(θ) = tmF … t` of the `f`-row of the trivialisation of the merged dual `t`-motive lies in
`K = F_q(θ)`. -/
theorem linear_independence {γ : ℚᵐ⁰} (hγ0 : 0 < γ) (hγ : γ < 1)
    (harch : GammaArchimedean ℚᵐ⁰) (hq : 2 ≤ Nat.card F)
    {w : ℕ} {ω : PowerSeries (Ambient F)} (hω : GIsSmall γ ω)
    (hωse : GSuperEntire γ ω) (hω0 : ω.coeff 0 ≠ 0)
    (hc : ∀ k : ℕ, 1 ≤ k → evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ k)) = 0)
    (hωfe : (PowerSeries.X - PowerSeries.C ((ambTheta F) ^ Nat.card F))
      * frobTwist (R := Ambient F) (p := Nat.card F) 1 ω = ω)
    (hw : ∀ s ∈ S, tmWeight s = w)
    (hcf : ∀ s ∈ S, frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((cf s : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hsm : ∀ s ∈ S, ∀ y ∈ s, GIsSmall γ (ω ^ y.1 * (y.2 : PowerSeries (Ambient F))))
    (hSse : ∀ s ∈ S, ∀ y ∈ s, GSuperEntire γ ((y.2 : PowerSeries (Ambient F))))
    (hpos : ∀ s ∈ S, ∀ y ∈ s, 1 ≤ y.1)
    (hQmem : ∀ s ∈ S, ∀ y ∈ s, ∀ k, (y.2).coeff k ∈ ambA F 0)
    (hne : ∀ s ∈ S, s ≠ [])
    (h0 : ([] : List (ℕ × Polynomial (Ambient F))) ∈ tmI S)
    (hA : ∀ i j m,
      (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf i j).coeff m ∈ ambA F 0)
    {a : Polynomial (Ambient F)}
    (ha : frobTwist (R := Ambient F) (p := Nat.card F) 1
      ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F))
      = ((a : Polynomial (Ambient F)) : PowerSeries (Ambient F)))
    (hval : evalSeriesGen (tmF (Nat.card F) ω w S cf
        ([] : List (ℕ × Polynomial (Ambient F)))) (ambTheta F) + a.eval (ambTheta F) = 0)
    (hLW : ∀ w' : ℕ, w' ≤ w → LinearIndependent (ambK F)
      (fun t : {t : ↥(tmI S) // tmWeight t.1 = w'} => tmZ (F := F) ω t.1.1)) :
    ∀ t' : ↥(tmI S),
      evalSeriesGen (tmF (Nat.card F) ω w S cf t'.1) (ambTheta F) ∈ ambK F := by
  classical
  have hle : ∀ t : ↥(tmI S), tmWeight t.1 ≤ w :=
    fun t => tmWeight_le_of_mem_tmI (S := S) (w := w) t.2 (fun s hs => hw s hs)
  obtain ⟨P, hP, hPθ, hPmem, _⟩ :=
    tmABP_a_leading_kperf (F := F) hγ0 hγ harch hq hω hωse hω0 hc hωfe hw hcf hsm hSse hpos hne h0 hA
      ha hval hle le_rfl
  have hΩ0 : (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω).coeff 0 ≠ 0 := by
    rw [frobTwist_coeff, pow_one]
    exact pow_ne_zero _ hω0
  have hΩ1 : ∀ j : ℕ, 2 ≤ j →
      evalSeriesGen (frobTwist (R := Ambient F) (p := Nat.card F) 1 ω)
        ((ambTheta F) ^ (Nat.card F) ^ j) = 0 := by
    intro j hj
    have hq1 : ((ambTheta F) ^ (Nat.card F ^ (j - 1))) ^ (Nat.card F ^ 1)
        = (ambTheta F) ^ (Nat.card F) ^ j := by
      rw [pow_one, ← pow_mul]
      congr 1
      conv_rhs => rw [← Nat.sub_add_cancel (show 1 ≤ j by omega)]
      rw [pow_succ]
    have h := evalSeriesGen_frobTwist hγ harch (Nat.card F) hωse
      ((ambTheta F) ^ (Nat.card F ^ (j - 1))) 1
    rw [hq1] at h
    have h2 : evalSeriesGen ω ((ambTheta F) ^ (Nat.card F ^ (j - 1))) = 0 :=
      hc (j - 1) (by omega)
    rw [h2] at h
    have hz : (0 : Ambient F) ^ (Nat.card F ^ 1) = 0 :=
      zero_pow (pow_ne_zero 1 (FrobPow.ne_zero (Ambient F) (q := Nat.card F)))
    rw [hz] at h
    exact h
  have hP0 : P none ≠ 0 := by
    intro h0'
    have h1 : (P none).eval (ambTheta F) = 1 := by rw [hPθ none, tmRho_none]
    rw [h0', Polynomial.eval_zero] at h1
    exact one_ne_zero h1.symm
  have hfe : tmPsiColA F ω w S cf h0 a
      = (coeHom (K := Ambient F)).mapMatrix
          (tmAOpt (K := Ambient F) (Nat.card F) (ambTheta F) w S cf) *ᵥ
        frobTwistVec (q := Nat.card F) 1 (tmPsiColA F ω w S cf h0 a) := by
    have hfun := tmPsiColA_functional F (w := w) (ω := ω) (cf := cf) (a := a) hγ harch hq hω
      hωfe hw hcf hsm hne h0 hA ha
    rw [tmPhi_twist_mat F _ hA] at hfun
    exact hfun
  have hB : ∀ t : ↥(tmI S), tmB F w S cf P (some t) = 0 :=
    step2_B_zero (F := F) hγ0 hγ harch hq hω hωse hc hωfe hΩ0 hΩ1 hsm hSse hpos hQmem hw h0 hA
      hfe hLW hPmem hP
  exact tmF_eval_mem_ambK (F := F) hγ0 hγ harch hq hω hωse hωfe hw hcf hsm hSse hne hB hPθ hP0

end Capstone

end ZagierHoffmanPositiveChar
