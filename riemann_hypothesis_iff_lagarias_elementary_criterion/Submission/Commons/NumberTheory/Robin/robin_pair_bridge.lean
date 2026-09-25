import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Submission.Commons.Analysis.Real.log_log_chord

open scoped ArithmeticFunction.sigma

namespace Commons.NumberTheory.Robin

lemma exp_one_lt_5040 : Real.exp 1 < (5040 : ℝ) :=
  lt_trans Real.exp_one_lt_d9 (by norm_num)

lemma one_lt_log_of_ge_5040 {M : ℕ} (hM : 5040 ≤ M) : 1 < Real.log (M : ℝ) := by
  have hE : Real.exp 1 < (M : ℝ) := lt_of_lt_of_le exp_one_lt_5040 (by exact_mod_cast hM)
  have hlog := Real.log_lt_log (Real.exp_pos 1) hE
  rwa [Real.log_exp] at hlog

lemma log_log_pos_of_ge_5040 {M : ℕ} (hM : 5040 ≤ M) : 0 < Real.log (Real.log (M : ℝ)) := by
  have h1 : 1 < Real.log (M : ℝ) := one_lt_log_of_ge_5040 hM
  have hlog := Real.log_lt_log (by norm_num : (0 : ℝ) < 1) h1
  simpa using hlog

lemma sigma_real_pos {M : ℕ} (hM : 0 < M) :
    (0 : ℝ) < ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) := by
  have hs : 0 < ArithmeticFunction.sigma 1 M := (ArithmeticFunction.sigma_pos_iff).2 hM
  exact_mod_cast hs

lemma robin_log_upper {M : ℕ} (hM : 5040 ≤ M)
    (hRobin : ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (M : ℝ) *
        Real.log (Real.log (M : ℝ))) :
    Real.log (((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) / (M : ℝ)) ≤
      Real.eulerMascheroniConstant + Real.log (Real.log (Real.log (M : ℝ))) := by
  have hMnat : 0 < M := lt_of_lt_of_le (by norm_num) hM
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hMnat
  have hL2pos : 0 < Real.log (Real.log (M : ℝ)) := log_log_pos_of_ge_5040 hM
  have hσpos : (0 : ℝ) < ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) := sigma_real_pos hMnat
  have hquotpos : 0 < ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) / (M : ℝ) := div_pos hσpos hMpos
  have hdiv : ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) / (M : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (M : ℝ)) := by
    rw [div_le_iff₀ hMpos]
    calc
      ((ArithmeticFunction.sigma 1 M : ℕ) : ℝ)
          ≤ Real.exp Real.eulerMascheroniConstant * (M : ℝ) *
              Real.log (Real.log (M : ℝ)) := hRobin
      _ = (Real.exp Real.eulerMascheroniConstant *
              Real.log (Real.log (M : ℝ))) * (M : ℝ) := by ring
  have hlog := Real.log_le_log hquotpos hdiv
  calc
    Real.log (((ArithmeticFunction.sigma 1 M : ℕ) : ℝ) / (M : ℝ))
        ≤ Real.log (Real.exp Real.eulerMascheroniConstant *
            Real.log (Real.log (M : ℝ))) := hlog
    _ = Real.log (Real.exp Real.eulerMascheroniConstant) +
          Real.log (Real.log (Real.log (M : ℝ))) := by
          rw [Real.log_mul (Real.exp_pos Real.eulerMascheroniConstant).ne' (ne_of_gt hL2pos)]
    _ = Real.eulerMascheroniConstant + Real.log (Real.log (Real.log (M : ℝ))) := by
          rw [Real.log_exp]

lemma robin_bridge_core {γ gN' gn gN A X C ε : ℝ} (hA1 : 1 < A) (hAC : A < C)
    (hAX : A < X) (hXC : X ≤ C)
    (hR1 : gN' ≤ γ + Real.log (Real.log A))
    (hR2 : gN ≤ γ + Real.log (Real.log C))
    (hstepA : gn - ε * X ≤ gN' - ε * A)
    (hstepB : gN' - ε * A = gN - ε * C) :
    gn ≤ γ + Real.log (Real.log X) := by
  let t : ℝ := (X - A) / (C - A)
  have hDpos : 0 < C - A := sub_pos.mpr hAC
  have hDne : C - A ≠ 0 := ne_of_gt hDpos
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (sub_nonneg.mpr (le_of_lt hAX)) (le_of_lt hDpos)
  have ht1 : t ≤ 1 := by
    dsimp [t]
    exact div_le_one_of_le₀ (by linarith) (le_of_lt hDpos)
  have hεD : ε * (C - A) = gN - gN' := by nlinarith [hstepB]
  have htD : X - A = t * (C - A) := by
    dsimp [t]
    rw [div_mul_cancel₀ _ hDne]
  have hεXA : ε * (X - A) = t * (gN - gN') := by
    calc
      ε * (X - A) = ε * (t * (C - A)) := by rw [htD]
      _ = t * (ε * (C - A)) := by ring
      _ = t * (gN - gN') := by rw [hεD]
  have hstep3 : gn ≤ gN' + ε * (X - A) := by
    nlinarith [hstepA]
  have hgn : gn ≤ (1 - t) * gN' + t * gN := by
    calc
      gn ≤ gN' + ε * (X - A) := hstep3
      _ = gN' + t * (gN - gN') := by rw [hεXA]
      _ = (1 - t) * gN' + t * gN := by ring
  have hR1' : (1 - t) * gN' ≤ (1 - t) * (γ + Real.log (Real.log A)) :=
    mul_le_mul_of_nonneg_left hR1 (sub_nonneg.mpr ht1)
  have hR2' : t * gN ≤ t * (γ + Real.log (Real.log C)) :=
    mul_le_mul_of_nonneg_left hR2 ht0
  have hRcomb : (1 - t) * gN' + t * gN ≤
      (1 - t) * (γ + Real.log (Real.log A)) + t * (γ + Real.log (Real.log C)) :=
    add_le_add hR1' hR2'
  have hstep4 : gn ≤ (1 - t) * (γ + Real.log (Real.log A)) + t * (γ + Real.log (Real.log C)) :=
    le_trans hgn hRcomb
  have hw2 : (X - A) / (C - A) = t := by dsimp [t]
  have hw1 : (C - X) / (C - A) = 1 - t := by
    dsimp [t]
    field_simp [hDne]
    ring
  have hchord := Commons.Analysis.Real.log_log_chord hA1 hAC (le_of_lt hAX) hXC
  have hchord' : (1 - t) * Real.log (Real.log A) + t * Real.log (Real.log C) ≤
      Real.log (Real.log X) := by
    rw [hw1, hw2] at hchord
    exact hchord
  have hfinal : gn ≤ γ + ((1 - t) * Real.log (Real.log A) + t * Real.log (Real.log C)) := by
    calc
      gn ≤ (1 - t) * (γ + Real.log (Real.log A)) + t * (γ + Real.log (Real.log C)) := hstep4
      _ = γ + ((1 - t) * Real.log (Real.log A) + t * Real.log (Real.log C)) := by ring
  exact le_trans hfinal (add_le_add_right hchord' γ)

theorem robin_pair_bridge {N' N n : ℕ} (hN'ge : 5040 ≤ N') (hN'ltn : N' < n) (hnleN : n ≤ N)
    (hRobinN' : ((ArithmeticFunction.sigma 1 N' : ℕ) : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (N' : ℝ) * Real.log (Real.log (N' : ℝ)))
    (hRobinN : ((ArithmeticFunction.sigma 1 N : ℕ) : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (N : ℝ) * Real.log (Real.log (N : ℝ)))
    (hstep : ∃ ε : ℝ, 0 < ε ∧
      Real.log (((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ)) - ε * Real.log (n : ℝ) ≤
      Real.log (((ArithmeticFunction.sigma 1 N' : ℕ) : ℝ) / (N' : ℝ)) - ε * Real.log (N' : ℝ) ∧
      Real.log (((ArithmeticFunction.sigma 1 N' : ℕ) : ℝ) / (N' : ℝ)) - ε * Real.log (N' : ℝ) =
      Real.log (((ArithmeticFunction.sigma 1 N : ℕ) : ℝ) / (N : ℝ)) - ε * Real.log (N : ℝ)) :
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
  rcases hstep with ⟨ε, hεpos, hAstep, hBstep⟩
  let A : ℝ := Real.log (N' : ℝ)
  let X : ℝ := Real.log (n : ℝ)
  let C : ℝ := Real.log (N : ℝ)
  let sN' : ℝ := Real.log (((ArithmeticFunction.sigma 1 N' : ℕ) : ℝ) / (N' : ℝ))
  let sn : ℝ := Real.log (((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ))
  let sN : ℝ := Real.log (((ArithmeticFunction.sigma 1 N : ℕ) : ℝ) / (N : ℝ))
  have hnge : 5040 ≤ n := le_trans hN'ge (le_of_lt hN'ltn)
  have hNge : 5040 ≤ N := le_trans hnge hnleN
  have hN'natpos : 0 < N' := lt_of_lt_of_le (by norm_num) hN'ge
  have hnnatpos : 0 < n := lt_of_lt_of_le (by norm_num) hnge
  have hNnatpos : 0 < N := lt_of_lt_of_le (by norm_num) hNge
  have hN'pos : (0 : ℝ) < (N' : ℝ) := by exact_mod_cast hN'natpos
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnnatpos
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNnatpos
  have hN'ltn_r : (N' : ℝ) < (n : ℝ) := by exact_mod_cast hN'ltn
  have hnleN_r : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnleN
  have hN'ltN_r : (N' : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le hN'ltn hnleN)
  have hA1 : 1 < A := by simpa [A] using one_lt_log_of_ge_5040 hN'ge
  have hAC : A < C := by
    dsimp [A, C]
    exact Real.log_lt_log hN'pos hN'ltN_r
  have hAX : A < X := by
    dsimp [A, X]
    exact Real.log_lt_log hN'pos hN'ltn_r
  have hXC : X ≤ C := by
    dsimp [X, C]
    exact Real.log_le_log hnpos hnleN_r
  have hR1log : sN' ≤ Real.eulerMascheroniConstant + Real.log (Real.log A) := by
    simpa [sN', A] using robin_log_upper hN'ge hRobinN'
  have hR2log : sN ≤ Real.eulerMascheroniConstant + Real.log (Real.log C) := by
    simpa [sN, C] using robin_log_upper hNge hRobinN
  have hAstep' : sn - ε * X ≤ sN' - ε * A := by simpa [sn, X, sN', A] using hAstep
  have hBstep' : sN' - ε * A = sN - ε * C := by simpa [sN', A, sN, C] using hBstep
  have hcore : sn ≤ Real.eulerMascheroniConstant + Real.log (Real.log X) :=
    robin_bridge_core (γ := Real.eulerMascheroniConstant) (gN' := sN') (gn := sn) (gN := sN)
      (A := A) (X := X) (C := C) (ε := ε) hA1 hAC hAX hXC hR1log hR2log hAstep' hBstep'
  have hquotpos : 0 < ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ) :=
    div_pos (sigma_real_pos hnnatpos) hnpos
  have hlogX2pos : 0 < Real.log (Real.log (n : ℝ)) := log_log_pos_of_ge_5040 hnge
  have hcore3log : sn ≤ Real.eulerMascheroniConstant + Real.log (Real.log (Real.log (n : ℝ))) := by
    simpa [X] using hcore
  have hExp : Real.exp (Real.log (((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ))) ≤
      Real.exp (Real.eulerMascheroniConstant + Real.log (Real.log (Real.log (n : ℝ)))) := by
    simpa [sn] using Real.exp_le_exp.mpr hcore3log
  have hquot_le : ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ) ≤
      Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ)) := by
    rw [Real.exp_log hquotpos] at hExp
    rw [Real.exp_add] at hExp
    rw [Real.exp_log hlogX2pos] at hExp
    exact hExp
  calc
    ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ)
        = ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / (n : ℝ) * (n : ℝ) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hnpos)]
    _ ≤ (Real.exp Real.eulerMascheroniConstant * Real.log (Real.log (n : ℝ))) * (n : ℝ) := by
        exact mul_le_mul_of_nonneg_right hquot_le (le_of_lt hnpos)
    _ = Real.exp Real.eulerMascheroniConstant * (n : ℝ) * Real.log (Real.log (n : ℝ)) := by
        ring

end Commons.NumberTheory.Robin