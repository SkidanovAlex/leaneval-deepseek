import Mathlib
import Submission.Work.WilG4c.Engine

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-- **BNZ Lemma 22 in abstract form, with the order shifted by the length of the
`y`-direction list.**  This is the "with `M.length`" variant of
`Work.WilkG4c.tnorm_curve_system` (`Submission/Work/WilG4c/Engine.lean`): the available order
of differentiation is `r - j - M.length` rather than `r - j`, and correspondingly the base
case and the chain rule are stated at that same shifted order.

Let `u j M` be `t ↦ ∂_x^j ∂_M G(t, γ t)` along the curve, `M` a list of `y`-directions, and
`gd i = γᵢ'`.  From

* `hbase`: the pure-`y` derivatives (`j = 0`) have jet norm `≤ e` at order `r - M.length`;
* `hchain`: the chain rule `u (j+1) M = (u j M)' - Σᵢ u j (i::M) · γᵢ'` for the jet norms at
  order `r - (j+1) - M.length`;
* `hgd`: `γᵢ'` is bounded by `1` in all derivative norms up to order `r`;
* smoothness of the functions involved at `t` at the shifted orders,

we get `tnorm (r - j - M.length) (u j M) t ≤ e · (r(1 + n e))^j` for all `M` with
`M.length + j ≤ r`. -/
theorem tnorm_curve_system_w {n r : ℕ} (u : ℕ → List (Fin n) → ℝ → ℝ) (gd : Fin n → ℝ → ℝ)
    (t : ℝ)
    (hsm : ∀ (j : ℕ) (M : List (Fin n)), M.length + j ≤ r →
      ContDiffAt ℝ (r - j - M.length) (u j M) t)
    (hsmg : ∀ i : Fin n, ContDiffAt ℝ r (gd i) t)
    (hbase : ∀ M : List (Fin n), M.length ≤ r →
      WilkiesDesign.CG.tnorm (r - M.length) (u 0 M) t ≤ Real.exp 1)
    (hchain : ∀ (j : ℕ) (M : List (Fin n)), M.length + (j + 1) ≤ r →
      WilkiesDesign.CG.tnorm (r - (j + 1) - M.length) (u (j + 1) M) t ≤
        WilkiesDesign.CG.tnorm (r - (j + 1) - M.length) (fun s => deriv (u j M) s) t +
        ∑ i : Fin n, WilkiesDesign.CG.tnorm (r - (j + 1) - M.length)
          (fun s => u j (i :: M) s * gd i s) t)
    (hgd : ∀ i : Fin n, ∀ m ≤ r, ‖iteratedFDeriv ℝ m (gd i) t‖ ≤ 1) :
    ∀ (j : ℕ) (M : List (Fin n)), M.length + j ≤ r →
      WilkiesDesign.CG.tnorm (r - j - M.length) (u j M) t ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro M hM
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simpa using hbase M (by simpa using hM)
    · obtain ⟨j₀, rfl⟩ : ∃ j₀, j = j₀ + 1 := ⟨j - 1, by omega⟩
      have hj₀ : M.length + j₀ ≤ r := by omega
      -- derivative term: one `x`-derivative costs a factor `r`
      have hderiv : tnorm (r - (j₀ + 1) - M.length) (fun s => deriv (u j₀ M) s) t ≤
          (r : ℝ) * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) := by
        refine (Work.WilkG4c.tnorm_deriv_le (r - (j₀ + 1) - M.length) (u j₀ M) t).trans ?_
        have hstep : ((r - (j₀ + 1) - M.length : ℕ) : ℝ) + 1 ≤ (r : ℝ) := by
          have : r - (j₀ + 1) - M.length + 1 ≤ r := by omega
          exact_mod_cast this
        have hmono : tnorm (r - (j₀ + 1) - M.length + 1) (u j₀ M) t ≤
            Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀ := by
          have heq : r - (j₀ + 1) - M.length + 1 = r - j₀ - M.length := by omega
          rw [heq]
          exact ih j₀ (by omega) M hj₀
        exact (mul_le_mul_of_nonneg_right hstep (tnorm_nonneg _ _ _)).trans
          (mul_le_mul_of_nonneg_left hmono (by positivity))
      -- product terms: each costs a factor `n · e`
      have hprod : ∀ i : Fin n, tnorm (r - (j₀ + 1) - M.length)
            (fun s => u j₀ (i :: M) s * gd i s) t ≤
          (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) * Real.exp 1 := by
        intro i
        have hlenM : (i :: M).length + j₀ ≤ r := by
          simp only [List.length_cons]; omega
        have hnat : r - (j₀ + 1) - M.length = r - j₀ - (i :: M).length := by
          simp only [List.length_cons]; omega
        have hcf : ContDiffAt ℝ ((r - (j₀ + 1) - M.length : ℕ) : WithTop ℕ∞)
            (u j₀ (i :: M)) t := by
          rw [hnat]
          exact hsm j₀ (i :: M) hlenM
        have hcg : ContDiffAt ℝ ((r - (j₀ + 1) - M.length : ℕ) : WithTop ℕ∞) (gd i) t :=
          (hsmg i).of_le (by exact_mod_cast (by omega : r - (j₀ + 1) - M.length ≤ r))
        have hmul := G2_tnorm_mul_proved (r - (j₀ + 1) - M.length)
          (u j₀ (i :: M)) (gd i) t hcf hcg
        refine hmul.trans ?_
        have h1 : tnorm (r - (j₀ + 1) - M.length) (u j₀ (i :: M)) t ≤
            Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀ := by
          rw [hnat]; exact ih j₀ (by omega) (i :: M) hlenM
        have h2 : tnorm (r - (j₀ + 1) - M.length) (gd i) t ≤ Real.exp 1 :=
          (tnorm_mono (by omega : r - (j₀ + 1) - M.length ≤ r) (gd i) t).trans
            (Work.WilkG4c.tnorm_le_exp_of_le_one r (gd i) t (hgd i))
        exact mul_le_mul h1 h2 (tnorm_nonneg _ _ _) (by positivity)
      have hsum : (∑ i : Fin n, tnorm (r - (j₀ + 1) - M.length)
            (fun s => u j₀ (i :: M) s * gd i s) t) ≤
          (n : ℝ) * ((Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) * Real.exp 1) := by
        calc (∑ i : Fin n, tnorm (r - (j₀ + 1) - M.length)
              (fun s => u j₀ (i :: M) s * gd i s) t)
            ≤ ∑ _i : Fin n, (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) * Real.exp 1 :=
              Finset.sum_le_sum fun i _ => hprod i
          _ = (n : ℝ) * ((Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) * Real.exp 1) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hfin : (r : ℝ) * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) +
            (n : ℝ) * ((Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) * Real.exp 1) ≤
          Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ (j₀ + 1) := by
        have hr1 : (1 : ℝ) ≤ r := by
          have : 1 ≤ r := by omega
          exact_mod_cast this
        have hne : (0 : ℝ) ≤ (n : ℝ) * Real.exp 1 := by positivity
        set X : ℝ := (r * (1 + n * Real.exp 1)) ^ j₀ with hX
        have hineq : r + (n : ℝ) * Real.exp 1 ≤ r * (1 + n * Real.exp 1) := by
          nlinarith [hr1, hne, mul_nonneg (sub_nonneg.mpr hr1) hne]
        calc (r : ℝ) * (Real.exp 1 * X) + (n : ℝ) * ((Real.exp 1 * X) * Real.exp 1)
            = (Real.exp 1 * X) * (r + (n : ℝ) * Real.exp 1) := by ring
          _ ≤ (Real.exp 1 * X) * (r * (1 + n * Real.exp 1)) :=
              mul_le_mul_of_nonneg_left hineq (by positivity)
          _ = Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ (j₀ + 1) := by
              rw [hX, pow_succ]; ring
      calc tnorm (r - (j₀ + 1) - M.length) (u (j₀ + 1) M) t
          ≤ tnorm (r - (j₀ + 1) - M.length) (fun s => deriv (u j₀ M) s) t +
            ∑ i : Fin n, tnorm (r - (j₀ + 1) - M.length)
              (fun s => u j₀ (i :: M) s * gd i s) t :=
            hchain j₀ M hM
        _ ≤ (r : ℝ) * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) +
            (n : ℝ) * ((Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j₀) * Real.exp 1) :=
            add_le_add hderiv hsum
        _ ≤ Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ (j₀ + 1) := hfin

end Work.WilG4c
