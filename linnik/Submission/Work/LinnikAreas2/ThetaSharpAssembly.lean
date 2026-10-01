/-
# `LinnikAreas2.ThetaSharpAssembly` — assembling the sharp HB (11.17) from its pieces

This file builds `Work.LinnikAreas2.ThetaSharp` (the statement of
`Submission/Work/LinnikAreas2/theta_diag_sharp2.lean`) from four analytic pieces:

* `abel_tsum_le_of_linear_majorant` — the Abel summation against a linear majorant;
* `tsum_le_integral_add_of_unimodal` (proved here, `tsum_le_integral_add_of_unimodal.lean`) —
  the sharp Euler comparison `Σ'_n f(n) ≤ ∫_{(0,∞)} f + 2 f(x₀)`;
* `integral_rpow_mul_exp_neg_sub` — `∫_0^∞ t^{σ-1}(e^{-t/A} − e^{-t/B}) = Γ(σ)(A^σ − B^σ)`;
* `thetaF_monotone_seq`, `thetaG_unimodal` — the unimodality of `t ↦ t^{σ-1}(e^{-t/A} − e^{-t/B})`.

The first stage, done here, is the reduction of the two Graham/`θ` upper bounds of the statement
to the single *linear* majorant `S(N) ≤ 1 + c·N` with `c = (1+ε/2)/(wL) + C₁/(wL)²` that the Abel
step consumes: for `N ≤ W = e^{wL}` the first clause has `log N ≤ log W = wL`, and for `N ≥ W` the
second clause is already of that shape.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs
import Submission.Work.LinnikAreas2.tsum_le_integral_add_of_unimodal
import Submission.Work.LinnikAreas2.abel_tsum_le_of_linear_majorant
import Submission.Work.LinnikAreas2.integral_rpow_mul_exp_neg_sub
import Submission.Work.LinnikAreas2.thetaF_summable
import Submission.Work.LinnikAreas2.thetaF_mul_tendsto_zero
import Submission.Work.LinnikAreas2.thetaF_monotone_seq
import Submission.Work.LinnikAreas2.thetaF_monotone_seq_bound
import Submission.Work.LinnikAreas2.D1Final
import Submission.Work.LinnikAreas2.thetaG_unimodal
import Submission.Work.LinnikAreas2.thetaSharp_closing

open scoped BigOperators
noncomputable section

namespace Work.LinnikAreas2

/-- The diagonal coefficients `a n = (Σ_{d | n} θ_d)²` of HB (11.17) at the cut-off `W`. -/
def thetaDiagA (W : ℝ) (n : ℕ) : ℝ :=
  (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM W d)^2

/-- **The linear majorant.**  From the two Graham/`θ` upper bounds of HB (11.13) at `W = e^{wL}`
one gets `Σ_{n ≤ N} a_n ≤ 1 + ((1+ε/2)/(wL) + C₁/(wL)²)·N` for every `N ≥ 1`. -/
theorem thetaDiag_majorant {ε C₁ w L : ℝ} (hε : 0 < ε) (hL : 0 < L) (hw : 0 < w)
    (h1 : ∀ N : ℕ, 1 ≤ N → (N:ℝ) ≤ Real.exp (w*L) →
      (∑ n ∈ Finset.Icc 1 N, thetaDiagA (Real.exp (w*L)) n)
        ≤ 1 + (1+ε/2)*(N:ℝ)*Real.log N/(w*L)^2 + C₁*(N:ℝ)/(w*L)^2)
    (h2 : ∀ N : ℕ, Real.exp (w*L) ≤ (N:ℝ) →
      (∑ n ∈ Finset.Icc 1 N, thetaDiagA (Real.exp (w*L)) n)
        ≤ 1 + (1+ε/2)*(N:ℝ)/(w*L) + C₁*(N:ℝ)/(w*L)^2) :
    ∀ N : ℕ, 1 ≤ N →
      (∑ n ∈ Finset.Icc 1 N, thetaDiagA (Real.exp (w*L)) n)
        ≤ 1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (N:ℝ) := by
  intro N hN
  have hMpos : 0 < w * L := mul_pos hw hL
  have hM2 : 0 < (w*L)^2 := by positivity
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hN1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hcpos : 0 < 1 + ε/2 := by linarith
  have hsplit : ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (N:ℝ)
      = (1+ε/2)/(w*L) * (N:ℝ) + C₁/(w*L)^2 * (N:ℝ) := by ring
  have hB : C₁*(N:ℝ)/(w*L)^2 ≤ C₁/(w*L)^2 * (N:ℝ) := le_of_eq (by ring)
  by_cases hcase : (N:ℝ) ≤ Real.exp (w*L)
  · have h := h1 N hN hcase
    have hlogN : Real.log (N:ℝ) ≤ w * L := by
      have h' := Real.log_le_log hNpos hcase
      simpa [Real.log_exp] using h'
    have hlogNM : Real.log (N:ℝ)/(w*L) ≤ 1 := by
      rw [div_le_one hMpos]; exact hlogN
    have hA : (1+ε/2)*(N:ℝ)*Real.log (N:ℝ)/(w*L)^2 ≤ (1+ε/2)/(w*L) * (N:ℝ) := by
      have e1 : (1+ε/2)*(N:ℝ)*Real.log (N:ℝ)/(w*L)^2
          = ((1+ε/2)*(N:ℝ)/(w*L)) * (Real.log (N:ℝ)/(w*L)) := by ring
      have e2 : (1+ε/2)/(w*L) * (N:ℝ) = ((1+ε/2)*(N:ℝ)/(w*L)) * 1 := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left hlogNM
        (div_nonneg (mul_nonneg (by linarith) hNpos.le) hMpos.le)
    linarith [h, hA, hB, hsplit.le, hsplit.ge]
  · have hcasege : Real.exp (w*L) ≤ (N:ℝ) := le_of_lt (not_le.mp hcase)
    have h := h2 N hcasege
    have heq1 : (1+ε/2)*(N:ℝ)/(w*L) = (1+ε/2)/(w*L) * (N:ℝ) := by ring
    have heq2 : C₁*(N:ℝ)/(w*L)^2 = C₁/(w*L)^2 * (N:ℝ) := by ring
    linarith [h, hsplit.le, hsplit.ge, heq1.le, heq1.ge, heq2.le, heq2.ge]


/-- The weight `n ↦ n^{σ-1}(e^{-n/A} − e^{-n/B})` of HB (11.17). -/
def thetaW (σ A B : ℝ) (n : ℕ) : ℝ :=
  (n:ℝ)^(σ-1) * (Real.exp (-((n:ℝ)/A)) - Real.exp (-((n:ℝ)/B)))

/-- `0 < A` from `0 < B < A`. -/
theorem thetaW_Apos {A B : ℝ} (hB : 0 < B) (hBA : B < A) : 0 < A := lt_trans hB hBA

/-- The bracket `e^{-t/A} − e^{-t/B}` is nonnegative for `t ≥ 0`. -/
theorem thetaW_bracket_nonneg {A B t : ℝ} (hB : 0 < B) (hBA : B < A) (ht : 0 ≤ t) :
    0 ≤ Real.exp (-(t/A)) - Real.exp (-(t/B)) := by
  have hA : 0 < A := lt_trans hB hBA
  have h : t/A ≤ t/B := div_le_div_of_nonneg_left ht hB (le_of_lt hBA)
  have h2 : Real.exp (-(t/B)) ≤ Real.exp (-(t/A)) := Real.exp_le_exp.mpr (by linarith)
  linarith

/-- The weight `thetaW σ A B n` is nonnegative. -/
theorem thetaW_nonneg {σ A B : ℝ} (hB : 0 < B) (hBA : B < A) (n : ℕ) :
    0 ≤ thetaW σ A B n := by
  have h1 : 0 ≤ (n:ℝ)^(σ-1) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have h2 := thetaW_bracket_nonneg hB hBA (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))
  simp only [thetaW]
  exact mul_nonneg h1 h2

/-- `n ↦ n · thetaW σ A B n` is summable: it is `thetaF_summable` at `σ + 1`. -/
theorem thetaW_summable_mul_id {σ A B : ℝ} (hσ : 0 < σ) (hB : 0 < B) (hBA : B < A) :
    Summable (fun n : ℕ => (n:ℝ) * thetaW σ A B n) := by
  have h := thetaF_summable (σ := σ + 1) (by linarith) hB hBA
  refine h.congr (fun n => ?_)
  simp only [thetaW]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  · have hpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have hpow : (n:ℝ) * (n:ℝ)^(σ-1) = (n:ℝ)^σ := by
      nth_rewrite 1 [← Real.rpow_one (n:ℝ)]
      rw [← Real.rpow_add hpos]
      congr 1
      ring
    have hX : (n:ℝ)^(σ+1-1) = (n:ℝ)^σ := by
      congr 1
      ring
    rw [hX, ← mul_assoc, hpow]

/-- **Summability of the diagonal series of HB (11.17)**: the product of the diagonal
coefficients with the weight is summable, by comparison with `(1 + c n)·thetaW` and
`a n ≤ 1 + c n` (which the majorant gives, `a` being nonnegative). -/
theorem thetaDiagA_summable_mul {ε C₁ w L σ A B : ℝ} (hε : 0 < ε) (hL : 0 < L) (hw : 0 < w)
    (hσ : 0 < σ) (hB : 0 < B) (hBA : B < A)
    (hmaj : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, thetaDiagA (Real.exp (w*L)) n)
        ≤ 1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (N:ℝ)) :
    Summable (fun n : ℕ => thetaDiagA (Real.exp (w*L)) n * thetaW σ A B n) := by
  set c : ℝ := (1+ε/2)/(w*L) + C₁/(w*L)^2 with hc
  have hmaj' : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, thetaDiagA (Real.exp (w*L)) n)
      ≤ 1 + c * (N:ℝ) := fun N => by rw [hc]; exact hmaj N
  have hW : Summable (fun n : ℕ => thetaW σ A B n) := thetaF_summable hσ hB hBA
  have hWn : Summable (fun n : ℕ => (n:ℝ) * thetaW σ A B n) := thetaW_summable_mul_id hσ hB hBA
  have hWnn : ∀ n : ℕ, 0 ≤ thetaW σ A B n := thetaW_nonneg hB hBA
  have hlin : Summable (fun n : ℕ => (1 + c * (n:ℝ)) * thetaW σ A B n) := by
    have h2 : Summable (fun n : ℕ => thetaW σ A B n + c * ((n:ℝ) * thetaW σ A B n)) :=
      hW.add (hWn.mul_left c)
    refine h2.congr (fun n => ?_)
    ring
  refine Summable.of_nonneg_of_le (g := fun n : ℕ =>
      thetaDiagA (Real.exp (w*L)) n * thetaW σ A B n) (f := fun n : ℕ =>
      (1 + c * (n:ℝ)) * thetaW σ A B n) (fun n => ?_) (fun n => ?_) hlin
  · exact mul_nonneg (sq_nonneg _) (hWnn n)
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have hz : thetaDiagA (Real.exp (w*L)) 0 = 0 := by
        simp [thetaDiagA]
      rw [hz, zero_mul]
      exact mul_nonneg (by norm_num) (hWnn 0)
    · have hle : thetaDiagA (Real.exp (w*L)) n
          ≤ ∑ k ∈ Finset.Icc 1 n, thetaDiagA (Real.exp (w*L)) k := by
        have hsub : ({n} : Finset ℕ) ⊆ Finset.Icc 1 n := by
          intro k hk
          simp only [Finset.mem_singleton] at hk
          subst hk
          exact Finset.mem_Icc.mpr ⟨hn, le_rfl⟩
        have := Finset.sum_le_sum_of_subset_of_nonneg (s := ({n} : Finset ℕ))
          (t := Finset.Icc 1 n) (f := fun k => thetaDiagA (Real.exp (w*L)) k) hsub
          (fun k _ _ => sq_nonneg _)
        simpa using this
      have h1 : thetaDiagA (Real.exp (w*L)) n ≤ 1 + c * (n:ℝ) := le_trans hle (hmaj' n)
      have h2 : (0:ℝ) ≤ thetaW σ A B n := hWnn n
      exact mul_le_mul_of_nonneg_right h1 h2

/-- **The vanishing of the Abel boundary term**: `A N · f (N+1) → 0`, where `A N` is bounded
by the linear majorant and `f = thetaW σ A B` decays exponentially. -/
theorem thetaDiagA_boundary_tendsto {ε C₁ w L σ A B : ℝ} (hε : 0 < ε) (hC₁ : 0 < C₁)
    (hL : 0 < L) (hw : 0 < w) (hσ : 0 < σ) (hB : 0 < B) (hBA : B < A)
    (hmaj : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, thetaDiagA (Real.exp (w*L)) n)
        ≤ 1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (N:ℝ)) :
    Filter.Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, thetaDiagA (Real.exp (w*L)) n) * thetaW σ A B (N+1))
      Filter.atTop (nhds 0) := by
  set c : ℝ := (1+ε/2)/(w*L) + C₁/(w*L)^2 with hc
  have hmaj' : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, thetaDiagA (Real.exp (w*L)) n)
      ≤ 1 + c * (N:ℝ) := fun N => by rw [hc]; exact hmaj N
  have hMpos : 0 < w * L := mul_pos hw hL
  have hcnonneg : 0 ≤ c := by
    rw [hc]
    have h1 : 0 ≤ (1+ε/2)/(w*L) := div_nonneg (by linarith) hMpos.le
    have h2 : 0 ≤ C₁/(w*L)^2 := div_nonneg hC₁.le (by positivity)
    linarith
  have hvan := thetaF_mul_tendsto_zero (σ := σ) (A := A) (B := B) (c := c) hσ hB hBA hcnonneg
  refine squeeze_zero (fun N => mul_nonneg (Finset.sum_nonneg fun k _ => sq_nonneg _)
    (thetaW_nonneg hB hBA (N+1))) (fun N => ?_) hvan
  have h1 : (∑ n ∈ Finset.Icc 1 N, thetaDiagA (Real.exp (w*L)) n) ≤ 1 + c * (N:ℝ) := hmaj' N
  have h2 : (0:ℝ) ≤ thetaW σ A B (N+1) := thetaW_nonneg hB hBA (N+1)
  calc (∑ n ∈ Finset.Icc 1 N, thetaDiagA (Real.exp (w*L)) n) * thetaW σ A B (N+1)
      ≤ (1 + c * (N:ℝ)) * thetaW σ A B (N+1) := mul_le_mul_of_nonneg_right h1 h2
    _ = (1 + c * (N:ℝ)) * ((N+1 : ℕ):ℝ)^(σ-1) *
          (Real.exp (-(((N+1 : ℕ):ℝ)/A)) - Real.exp (-(((N+1 : ℕ):ℝ)/B))) := by
        simp only [thetaW]
        ring


/-! ## The wiring: `ThetaSharp` from the unimodality and the closing arithmetic -/

/-- For `0 < B < A`, `thetaW σ A B t ≤ t^{σ-1}(1 − e^{−t/B})` for `t ≥ 0` (the bracket
`e^{−t/A} − e^{−t/B} ≤ 1 − e^{−t/B}`). -/
theorem thetaW_le_rpow_mul {σ A B : ℝ} (hB : 0 < B) (hBA : B < A) {t : ℝ} (ht : 0 ≤ t) :
    t^(σ-1) * (Real.exp (-(t/A)) - Real.exp (-(t/B)))
      ≤ t^(σ-1) * (1 - Real.exp (-(t/B))) := by
  have hA : 0 < A := lt_trans hB hBA
  have h1 : Real.exp (-(t/A)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have : 0 ≤ t/A := div_nonneg ht hA.le; linarith)
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg ht _)
  linarith

open Filter in
/-- **Assembly of the sharp HB (11.17).**  From the unimodality of
`t ↦ t^{σ-1}(e^{-t/A} − e^{-t/B})` (`thetaG_unimodal`) and the closing arithmetic
(`thetaSharp_closing`), via the Abel step, the sharp Euler comparison and the Γ-integral. -/
theorem ThetaSharp_of
    (hUni : ∀ {σ A B : ℝ}, 0 < σ → σ ≤ 1 → 0 < B → B < A →
      ∃ x₀ : ℝ, 0 < x₀ ∧ x₀ ≤ 2 * B * (1 + Real.log (A / B)) ∧
        MonotoneOn (fun t : ℝ => t ^ (σ - 1) * (Real.exp (-(t / A)) - Real.exp (-(t / B))))
          (Set.Icc 0 x₀) ∧
        AntitoneOn (fun t : ℝ => t ^ (σ - 1) * (Real.exp (-(t / A)) - Real.exp (-(t / B))))
          (Set.Ici x₀) ∧
        (∀ t ∈ Set.Ioi (0 : ℝ),
          0 ≤ t ^ (σ - 1) * (Real.exp (-(t / A)) - Real.exp (-(t / B)))) ∧
        MeasureTheory.IntegrableOn
          (fun t : ℝ => t ^ (σ - 1) * (Real.exp (-(t / A)) - Real.exp (-(t / B)))) (Set.Ioi 0))
    (hClose : ∀ {ε C₁ w u x : ℝ}, 0 < ε → 0 < C₁ → 0 < w → 0 < u → 2*w < u → u < x →
      ∃ L₀ C₂ : ℝ, 0 < L₀ ∧ 0 < C₂ ∧
        ∀ (L β A U B σ M : ℝ), L₀ ≤ L → (1/2 : ℝ) ≤ β → β < 1 →
          (1-β)*L ≤ Real.log (Real.log L)/3 → A = Real.exp (x*L) → U = Real.exp (u*L) →
          B = U/L^2 → σ = 2-2*β → M = w*L → 0 < B → B < A →
          ∀ (K : ℕ) (x₀ : ℝ),
            ((K:ℝ) ≤ 2*B*(1 + Real.log (A/B)) + 2) → 0 < x₀ →
            x₀ ≤ 2*B*(1 + Real.log (A/B)) →
            (1 + ((1+ε/2)/M + C₁/M^2) * (K:ℝ)) * ((K:ℝ)^(σ-1) * (1 - Real.exp (-(K:ℝ)/B)))
              + ((1+ε/2)/M + C₁/M^2) *
                (Real.Gamma σ * (A^σ - B^σ) + 2 * (x₀^(σ-1) * (1 - Real.exp (-x₀/B))))
            ≤ (1+ε) * (A^σ - U^σ) / (2*w*(1-β)*L) + C₂/L)
    : ThetaSharp := by
  intro ε hε u w x hw h2wu hux C₁ hC₁
  have hu : 0 < u := by linarith
  obtain ⟨L₀, C₂, hL₀, hC₂, hmain⟩ := hClose hε hC₁ hw hu h2wu hux
  refine ⟨max L₀ 1, C₂, lt_max_of_lt_left hL₀, hC₂, ?_⟩
  intro L β hL hβ1 hβ2 hlog h1 h2
  have hL0 : L₀ ≤ L := le_trans (le_max_left _ _) hL
  have hL1 : (1:ℝ) ≤ L := le_trans (le_max_right _ _) hL
  have hLpos : 0 < L := lt_of_lt_of_le hL₀ hL0
  -- abbreviations
  set σ : ℝ := 2 - 2*β with hσdef
  have hσpos : 0 < σ := by rw [hσdef]; linarith
  have hσ1 : σ ≤ 1 := by rw [hσdef]; linarith
  set A : ℝ := Real.exp (x*L) with hAdef
  set U : ℝ := Real.exp (u*L) with hUdef
  set B : ℝ := U/L^2 with hBdef
  have hUpos : 0 < U := by rw [hUdef]; exact Real.exp_pos _
  have hApos : 0 < A := by rw [hAdef]; exact Real.exp_pos _
  have hBpos : 0 < B := by rw [hBdef]; positivity
  have hBA : B < A := by
    rw [hBdef, hUdef, hAdef]
    have hp : (0:ℝ) < L^2 := by positivity
    have hL2 : (1:ℝ) ≤ L^2 := by nlinarith
    have h1 : Real.exp (u*L)/L^2 ≤ Real.exp (u*L) := by
      rw [div_le_iff₀ hp]
      nlinarith [Real.exp_pos (u*L)]
    have h2 : Real.exp (u*L) < Real.exp (x*L) := Real.exp_lt_exp.mpr (by nlinarith)
    exact lt_of_le_of_lt h1 h2
  -- the linear majorant, and its all-`N` version
  have hmajPos : ∀ N : ℕ, 1 ≤ N → (∑ n ∈ Finset.Icc 1 N, thetaDiagA (Real.exp (w*L)) n)
      ≤ 1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (N:ℝ) :=
    thetaDiag_majorant hε hLpos hw h1 h2
  have hmaj : ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, thetaDiagA (Real.exp (w*L)) n)
      ≤ 1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (N:ℝ) := by
    intro N
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp
    · exact hmajPos N hN
  have hcnonneg : 0 ≤ (1+ε/2)/(w*L) + C₁/(w*L)^2 := by
    have h1' : 0 < w*L := mul_pos hw hLpos
    exact add_nonneg (div_nonneg (by linarith) h1'.le) (div_nonneg hC₁.le (by positivity))
  -- the turning index and the peak
  obtain ⟨K, hKb, hKinc, hKdec⟩ := thetaF_monotone_seq_bound (A := A) (B := B) hσpos hσ1 hBpos hBA
  obtain ⟨x₀, hx₀pos, hx₀b, hmono, hanti, hnn, hint⟩ := hUni hσpos hσ1 hBpos hBA
  -- the Euler comparison and the Γ-integral
  have hEuler : (∑' n : ℕ, thetaW σ A B n)
      ≤ (∫ t in Set.Ioi (0:ℝ), t ^ (σ - 1) * (Real.exp (-(t / A)) - Real.exp (-(t / B))))
        + 2 * (x₀ ^ (σ - 1) * (Real.exp (-(x₀ / A)) - Real.exp (-(x₀ / B)))) :=
    tsum_le_integral_add_of_unimodal (f := fun t : ℝ =>
      t ^ (σ - 1) * (Real.exp (-(t / A)) - Real.exp (-(t / B))))
      hx₀pos (fun n => thetaW_nonneg hBpos hBA n) hnn hmono hanti hint
  have hInt := integral_rpow_mul_exp_neg_sub σ A B hσpos hApos hBpos
  have hx₀nn : 0 ≤ x₀ := le_of_lt hx₀pos
  have hx₀last : x₀ ^ (σ - 1) * (Real.exp (-(x₀ / A)) - Real.exp (-(x₀ / B)))
      ≤ x₀^(σ-1) * (1 - Real.exp (-x₀/B)) := by
    have harg : Real.exp (-((x₀)/B)) = Real.exp (-x₀/B) := by
      congr 1
      ring
    rw [harg]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx₀nn _)
    have h1' : Real.exp (-(x₀/A)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by have : 0 ≤ x₀/A := div_nonneg hx₀nn hApos.le; linarith)
    linarith
  -- the Abel step
  have hAbel : (∑' n : ℕ, thetaDiagA (Real.exp (w*L)) n * thetaW σ A B n)
      ≤ (1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (K:ℝ)) * thetaW σ A B K
        + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (∑' n : ℕ, thetaW σ A B n) :=
    abel_tsum_le_of_linear_majorant (fun n => thetaDiagA (Real.exp (w*L)) n)
      (fun n => thetaW σ A B n) (K := K) (c := (1+ε/2)/(w*L) + C₁/(w*L)^2)
      (fun n => sq_nonneg _) (by simp [thetaDiagA]) (fun n => thetaW_nonneg hBpos hBA n)
      hmaj hKdec hKinc
      (thetaDiagA_summable_mul hε hLpos hw hσpos hBpos hBA hmaj)
      (thetaF_summable hσpos hBpos hBA)
      (thetaDiagA_boundary_tendsto hε hC₁ hLpos hw hσpos hBpos hBA hmaj)
  -- the summand identification
  have hsummand : ∀ n : ℕ, ((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM (Real.exp (w*L)) d : ℝ))^2
        * (n:ℝ)^(1-2*β)
        * (Real.exp (-(n:ℝ)/Real.exp (x*L)) - Real.exp (-(n:ℝ)*L^2/Real.exp (u*L)))
      = thetaDiagA (Real.exp (w*L)) n * thetaW σ A B n := by
    intro n
    have hLne : L ≠ 0 := ne_of_gt hLpos
    have hUne : Real.exp (u*L) ≠ 0 := Real.exp_ne_zero _
    have hexp : (1:ℝ) - 2*β = σ - 1 := by rw [hσdef]; try ring
    have h1 : -(n:ℝ)/Real.exp (x*L) = -((n:ℝ)/A) := by rw [hAdef]; ring
    have h2 : -(n:ℝ)*L^2/Real.exp (u*L) = -((n:ℝ)/B) := by
      rw [hBdef, hUdef]
      field_simp
      try ring
    simp only [thetaDiagA, thetaW]
    rw [h1, h2, hexp]
    try ring
  -- conclude
  have hargB : Real.exp (-((K:ℝ)/B)) = Real.exp (-(K:ℝ)/B) := by
    congr 1
    ring
  have hweightK : thetaW σ A B K ≤ (K:ℝ)^(σ-1) * (1 - Real.exp (-((K:ℝ)/B))) := by
    have h2 : thetaW σ A B K
        = (K:ℝ)^(σ-1) * (Real.exp (-((K:ℝ)/A)) - Real.exp (-((K:ℝ)/B))) := rfl
    rw [h2]
    exact thetaW_le_rpow_mul hBpos hBA (Nat.cast_nonneg K)
  have hcK : 0 ≤ 1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (K:ℝ) :=
    le_trans (Finset.sum_nonneg fun k _ => sq_nonneg _) (hmaj K)
  have hSum : (∑' n : ℕ, thetaW σ A B n)
      ≤ Real.Gamma σ * (A^σ - B^σ) + 2 * (x₀^(σ-1) * (1 - Real.exp (-x₀/B))) :=
    calc (∑' n : ℕ, thetaW σ A B n)
        ≤ (∫ t in Set.Ioi (0:ℝ), t ^ (σ - 1) * (Real.exp (-(t / A)) - Real.exp (-(t / B))))
            + 2 * (x₀ ^ (σ - 1) * (Real.exp (-(x₀ / A)) - Real.exp (-(x₀ / B)))) := hEuler
      _ = Real.Gamma σ * (A^σ - B^σ)
            + 2 * (x₀ ^ (σ - 1) * (Real.exp (-(x₀ / A)) - Real.exp (-(x₀ / B)))) := by rw [hInt]
      _ ≤ Real.Gamma σ * (A^σ - B^σ) + 2 * (x₀^(σ-1) * (1 - Real.exp (-x₀/B))) := by
            linarith [hx₀last]
  have hfinal : (∑' n : ℕ, thetaDiagA (Real.exp (w*L)) n * thetaW σ A B n)
      ≤ (1+ε) * (A^σ - U^σ) / (2*w*(1-β)*L) + C₂/L := by
    refine le_trans hAbel ?_
    have hstep : (1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (K:ℝ)) * thetaW σ A B K
        + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (∑' n : ℕ, thetaW σ A B n)
        ≤ (1 + ((1+ε/2)/(w*L) + C₁/(w*L)^2) * (K:ℝ)) *
            ((K:ℝ)^(σ-1) * (1 - Real.exp (-(K:ℝ)/B)))
          + ((1+ε/2)/(w*L) + C₁/(w*L)^2) *
            (Real.Gamma σ * (A^σ - B^σ) + 2 * (x₀^(σ-1) * (1 - Real.exp (-x₀/B)))) := by
      rw [hargB] at hweightK
      exact add_le_add (mul_le_mul_of_nonneg_left hweightK hcK)
        (mul_le_mul_of_nonneg_left hSum hcnonneg)
    exact le_trans hstep
      (hmain L β A U B σ (w*L) hL0 hβ1 hβ2 hlog rfl rfl rfl hσdef rfl hBpos hBA K x₀ hKb hx₀pos hx₀b)
  calc (∑' n : ℕ, ((∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM (Real.exp (w*L)) d : ℝ))^2
          * (n:ℝ)^(1-2*β)
          * (Real.exp (-(n:ℝ)/Real.exp (x*L)) - Real.exp (-(n:ℝ)*L^2/Real.exp (u*L))))
      = ∑' n : ℕ, thetaDiagA (Real.exp (w*L)) n * thetaW σ A B n :=
        tsum_congr hsummand
    _ ≤ (1+ε) * ((Real.exp (x*L))^(2-2*β) - (Real.exp (u*L))^(2-2*β)) / (2*w*(1-β)*L) + C₂/L := by
        rw [← hAdef, ← hUdef, ← hσdef]
        exact hfinal

/-- **The sharp HB (11.17)**, assembled. -/
theorem thetaSharp_proved : ThetaSharp :=
  ThetaSharp_of thetaG_unimodal thetaSharp_closing

end Work.LinnikAreas2
