/-
# Uniform bounds for the `Lop`-iterates of the `θ`-derivatives of a `q`-family

`Work.Spaces.Lop u θ = sin (2θ) · u'(θ)` is the angular derivation `D_θ` acting on functions
of `θ` alone.  For a family `q : ℕ → ℝ → ℝ` of class `C^8` on the open interval `(0, π/2)`
whose `θ`-derivatives up to order `8` are bounded by a family `B`, this file proves that on a
compact subinterval `[a,b] ⊂ (0, π/2)` every iterate `Lop^[i] (iteratedDeriv r (q m))` with
`r + i ≤ 8` is bounded by a constant times `B m`, and so is its derivative (for
`r + i + 1 ≤ 8`); the constants are independent of `m`.

The two ingredients are

* the Leibniz recursion `Lop_iter_succ_eq_sum` of `Defs.lean`, which expresses
  `Lop^[i+1] g` as the finite sum `∑_{a ≤ i} C(i,a) · Asf a · Lop^[i-a] (deriv g)`, giving the
  *value* bound by strong induction on `i` (this is where one order of differentiability is
  spent at each step);
* the identity `Lop^[i+1] g = sin (2·) · deriv (Lop^[i] g)`, which turns the *derivative* bound
  for `(i,r)` into the *value* bound for `(i+1,r)`, divided by `sin (2θ)`; on `[a,b]` with
  `0 < a` and `b < π/2` the sinus is bounded below by a positive constant, supplied here by
  compactness of `[a,b]`.
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.PhiStar.FlatWAux.TsumLopDerivAux.Defs
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Filter

namespace Work.FTS.PhiStar.FlatWAux.TsumLopDerivAux

/-- **Value bound.**  For `r + j ≤ 8` the `j`-th `Lop`-iterate of the `r`-th `θ`-derivative of
`q m` is bounded on `[a,b]` by a constant (independent of `m`) times `B m`. -/
private theorem value_bound (q : ℕ → ℝ → ℝ) (B : ℕ → ℝ)
    (hq : ∀ m : ℕ, ContDiffOn ℝ 8 (q m) (Set.Ioo 0 (Real.pi / 2)))
    (hqb : ∀ (m r : ℕ), r ≤ 8 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |iteratedDeriv r (q m) θ| ≤ B m)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < Real.pi / 2) :
    ∀ (j r : ℕ), r + j ≤ 8 → ∃ K : ℝ, 0 ≤ K ∧
      ∀ (m : ℕ) (θ : ℝ), θ ∈ Set.Icc a b →
        |(Work.Spaces.Lop^[j]) (iteratedDeriv r (q m)) θ| ≤ K * B m := by
  have hUopen : IsOpen (Set.Ioo 0 (Real.pi / 2)) := isOpen_Ioo
  have hsub : Set.Icc a b ⊆ Set.Ioo 0 (Real.pi / 2) := fun θ hθ =>
    ⟨lt_of_lt_of_le ha hθ.1, lt_of_le_of_lt hθ.2 hb⟩
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro r hr
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      refine ⟨1, zero_le_one, fun m θ hθ => ?_⟩
      rw [Function.iterate_zero_apply, one_mul]
      exact hqb m r (by omega) θ (hsub hθ)
    · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
      -- the Leibniz recursion for the level `n+1`
      have hstep : ∀ (m : ℕ) (θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) →
          (Work.Spaces.Lop^[n + 1]) (iteratedDeriv r (q m)) θ
            = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
                (Asf k θ * (Work.Spaces.Lop^[n - k]) (iteratedDeriv (r + 1) (q m)) θ) := by
        intro m θ hθ
        have hg : ContDiffOn ℝ (((n + 1 : ℕ)) : WithTop ℕ∞) (iteratedDeriv r (q m))
            (Set.Ioo 0 (Real.pi / 2)) := by
          refine contDiffOn_iteratedDeriv hUopen r (n + 1) ?_
          exact (hq m).of_le (by exact_mod_cast (show (n + 1) + r ≤ 8 by omega))
        have hrec := Lop_iter_succ_eq_sum n hUopen hg θ hθ
        rw [hrec]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← iteratedDeriv_succ]
      -- the induction hypotheses, one for each summand
      have hIH : ∀ k : ℕ, ∃ K : ℝ, 0 ≤ K ∧ (k ∈ Finset.range (n + 1) →
          ∀ (m : ℕ) (θ : ℝ), θ ∈ Set.Icc a b →
            |(Work.Spaces.Lop^[n - k]) (iteratedDeriv (r + 1) (q m)) θ| ≤ K * B m) := by
        intro k
        by_cases hk : k ∈ Finset.range (n + 1)
        · obtain ⟨K, hK0, hKb⟩ :=
            ih (n - k) (by have := Finset.mem_range.mp hk; omega) (r + 1) (by omega)
          exact ⟨K, hK0, fun _ => hKb⟩
        · exact ⟨0, le_rfl, fun hk' => absurd hk' hk⟩
      choose Kf hKf0 hKfb using hIH
      obtain ⟨C, _, hC0, _, hCb, _⟩ := Asf_bound_le n hab
      refine ⟨∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * C * Kf k, ?_, ?_⟩
      · exact Finset.sum_nonneg fun k hk =>
          mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC0) (hKf0 k)
      · intro m θ hθ
        rw [hstep m θ (hsub hθ)]
        calc |∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
                (Asf k θ * (Work.Spaces.Lop^[n - k]) (iteratedDeriv (r + 1) (q m)) θ)|
            ≤ ∑ k ∈ Finset.range (n + 1), |(n.choose k : ℝ) *
                (Asf k θ * (Work.Spaces.Lop^[n - k]) (iteratedDeriv (r + 1) (q m)) θ)| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ k ∈ Finset.range (n + 1), ((n.choose k : ℝ) * C * Kf k) * B m := by
              refine Finset.sum_le_sum fun k hk => ?_
              have hA : |Asf k θ| ≤ C :=
                hCb k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)) θ hθ
              have hX : |(Work.Spaces.Lop^[n - k]) (iteratedDeriv (r + 1) (q m)) θ|
                  ≤ Kf k * B m := hKfb k hk m θ hθ
              calc |(n.choose k : ℝ) * (Asf k θ *
                      (Work.Spaces.Lop^[n - k]) (iteratedDeriv (r + 1) (q m)) θ)|
                  = (n.choose k : ℝ) * (|Asf k θ| *
                      |(Work.Spaces.Lop^[n - k]) (iteratedDeriv (r + 1) (q m)) θ|) := by
                    rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg (n.choose k))]
                _ ≤ (n.choose k : ℝ) * (C * (Kf k * B m)) := by
                    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
                    exact mul_le_mul hA hX (abs_nonneg _) hC0
                _ = ((n.choose k : ℝ) * C * Kf k) * B m := by ring
          _ = (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * C * Kf k) * B m :=
              (Finset.sum_mul _ _ _).symm

theorem Lop_iter_deriv_bound (q : ℕ → ℝ → ℝ) (B : ℕ → ℝ)
    (hq : ∀ m : ℕ, ContDiffOn ℝ 8 (q m) (Set.Ioo 0 (Real.pi / 2)))
    (hqb : ∀ (m r : ℕ), r ≤ 8 → ∀ θ : ℝ, θ ∈ Set.Ioo 0 (Real.pi / 2) →
      |iteratedDeriv r (q m) θ| ≤ B m) :
    ∀ (i r : ℕ), r + i ≤ 8 → r + i + 1 ≤ 8 → ∀ {a b : ℝ}, 0 < a → a ≤ b →
      b < Real.pi / 2 →
      ∃ K K' : ℝ, 0 ≤ K ∧ 0 ≤ K' ∧
        ∀ (m : ℕ) (θ : ℝ), θ ∈ Set.Icc a b →
          |(Work.Spaces.Lop^[i]) (iteratedDeriv r (q m)) θ| ≤ K * B m ∧
          |deriv ((Work.Spaces.Lop^[i]) (iteratedDeriv r (q m))) θ| ≤ K' * B m := by
  intro i r hri hri' a b ha hab hb
  obtain ⟨K, hK0, hKb⟩ := value_bound q B hq hqb ha hab hb i r hri
  obtain ⟨K₂, hK₂0, hK₂b⟩ := value_bound q B hq hqb ha hab hb (i + 1) r (by omega)
  -- a positive lower bound for `sin (2θ)` on `[a,b]`
  obtain ⟨θ₀, hθ₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (⟨a, le_rfl, hab⟩ : (Set.Icc a b).Nonempty)
    (by fun_prop : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Icc a b))
  have hc0 : 0 < Real.sin (2 * θ₀) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [ha, hθ₀.1]) (by linarith [hθ₀.2, hb])
  refine ⟨K, K₂ / Real.sin (2 * θ₀), hK0, div_nonneg hK₂0 (le_of_lt hc0), ?_⟩
  intro m θ hθ
  refine ⟨hKb m θ hθ, ?_⟩
  have hs0 : 0 < Real.sin (2 * θ) := lt_of_lt_of_le hc0 (hmin hθ)
  have hsne : Real.sin (2 * θ) ≠ 0 := ne_of_gt hs0
  -- `Lop` is `sin (2·)` times the derivative, whence the division identity
  have hkey : (Work.Spaces.Lop^[i + 1]) (iteratedDeriv r (q m)) θ
      = Real.sin (2 * θ) * deriv ((Work.Spaces.Lop^[i]) (iteratedDeriv r (q m))) θ := by
    rw [Function.iterate_succ_apply' Work.Spaces.Lop i (iteratedDeriv r (q m))]
    rfl
  have hdiv : deriv ((Work.Spaces.Lop^[i]) (iteratedDeriv r (q m))) θ
      = (Work.Spaces.Lop^[i + 1]) (iteratedDeriv r (q m)) θ / Real.sin (2 * θ) := by
    rw [eq_div_iff hsne, mul_comm]
    exact hkey.symm
  have hprod : |deriv ((Work.Spaces.Lop^[i]) (iteratedDeriv r (q m))) θ| * Real.sin (2 * θ)
      = |(Work.Spaces.Lop^[i + 1]) (iteratedDeriv r (q m)) θ| := by
    rw [hdiv, abs_div, abs_of_pos hs0, div_mul_cancel₀ _ hsne]
  have hA : |deriv ((Work.Spaces.Lop^[i]) (iteratedDeriv r (q m))) θ| * Real.sin (2 * θ₀)
      ≤ K₂ * B m := by
    refine le_trans (mul_le_mul_of_nonneg_left (hmin hθ) (abs_nonneg _)) ?_
    rw [hprod]
    exact hK₂b m θ hθ
  calc |deriv ((Work.Spaces.Lop^[i]) (iteratedDeriv r (q m))) θ|
      ≤ (K₂ * B m) / Real.sin (2 * θ₀) := (le_div_iff₀ hc0).mpr hA
    _ = (K₂ / Real.sin (2 * θ₀)) * B m := by ring

end Work.FTS.PhiStar.FlatWAux.TsumLopDerivAux
