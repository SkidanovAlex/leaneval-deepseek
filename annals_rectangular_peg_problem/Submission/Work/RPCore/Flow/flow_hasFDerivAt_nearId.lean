import Mathlib
import Submission.Work.RPCore.Flow.flow_variational_eq
import Submission.Work.RPCore.Flow.flow_add
import Submission.Work.RPCore.Flow.flow_hasFDerivAt_small
import Submission.Work.RPCore.Flow.hasFDerivAt_iterate_nearId

/-!
# The flow map of a `C¹` field with bounded derivative is near the identity

Let `X : E → E` be a `C¹` vector field on a finite-dimensional real Banach space with
`‖fderiv ℝ X z‖ ≤ K` for all `z`, and let `Φ` be *any* map such that for every `t` and every `y`
there is an integral curve of `X` starting at `y` and taking the value `Φ t y` at time `t`
(hypothesis `hΦ`).

Because `X` is globally `K`-Lipschitz (mean value inequality), integral curves are unique and
`Φ` is forced to be the (global) flow of `X`.  The theorem below produces, for every time `t` and
every base point `z`, a Fréchet derivative `M` of `Φ t` at `z`, with the near-identity bound

`‖M - 1‖ ≤ exp (K * |t|) - 1`.

The proof splits into three independent ingredients:

* `flow_add` — the semigroup law `Φ (s+u) y = Φ s (Φ u y)`, derived from uniqueness of integral
  curves;
* `flow_hasFDerivAt_small` — the *small-time* statement `|t| * K < 1`, obtained from the
  local fundamental solution of the variational equation (`flow_variational_eq`) for `t ≥ 0`
  and, for `t < 0`, from the same applied to the time-reversed flow of `-X`;
* `hasFDerivAt_iterate_nearId` — iterating a map all of whose derivatives are within `β` of the
  identity: `(f^[n])` has derivative within `(1+β)^n - 1` of the identity.

For a general time `t` choose `n ≥ 1` with `|t| * K < n`, let `s = t / n` (so that `|s| * K < 1`)
and write `Φ t = (Φ s)^[n]` by the semigroup law.  The small-time statement applies to the single
map `Φ s` at every base point, the iteration lemma composes the derivatives, and
`(1 + (exp (K|s|) - 1))^n = exp (K|s|)^n = exp (n K |s|) = exp (K |t|)` gives the claimed bound.
-/

namespace Work.RPCore.Flow

theorem flow_hasFDerivAt_nearId {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [FiniteDimensional ℝ E] (X : E → E) (hX : ContDiff ℝ 1 X) {K : ℝ}
    (hK : ∀ z, ‖fderiv ℝ X z‖ ≤ K) (Φ : ℝ → E → E)
    (hΦ : ∀ t y, ∃ γ : ℝ → E, γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) ∧ γ t = Φ t y) :
    ∀ t (z : E), ∃ M : E →L[ℝ] E,
      HasFDerivAt (Φ t) M z ∧ ‖M - 1‖ ≤ Real.exp (K * |t|) - 1 := by
  intro t z
  have hK0 : 0 ≤ K := (norm_nonneg (fderiv ℝ X 0)).trans (hK 0)
  have hflow0 : ∀ y : E, Φ 0 y = y := fun y => Port.ODE.flow_zero Φ hΦ y
  -- a natural number `n ≥ 1` with `|t| * K < n`, so that `s = t / n` is in the small-time regime
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| * K)
  have htK : 0 ≤ |t| * K := mul_nonneg (abs_nonneg t) hK0
  have hnpos : 0 < n := Nat.cast_pos.mp (lt_of_le_of_lt htK hn)
  set s : ℝ := t / n with hsdef
  have hns : (n : ℝ) * s = t := by
    rw [hsdef]; exact mul_div_cancel₀ t (by exact_mod_cast hnpos.ne')
  have hsabs : |s| = |t| / n := by
    rw [hsdef, abs_div]
    simp
  have hsK : |s| * K < 1 := by
    rw [hsabs, div_mul_eq_mul_div, div_lt_one (by exact_mod_cast hnpos)]
    exact hn
  have hβ : 0 ≤ Real.exp (K * |s|) - 1 := by
    have h := Real.one_le_exp (mul_nonneg hK0 (abs_nonneg s)); linarith
  -- small time: `Φ s` is `(1 + β)`-near the identity at *every* base point
  obtain ⟨A, hA, hAb⟩ :=
    hasFDerivAt_iterate_nearId (Φ s) hβ
      (fun y => flow_hasFDerivAt_small X hX hK Φ hΦ hsK y) n z
  refine ⟨A, ?_, ?_⟩
  · -- `Φ t = (Φ s)^[n]`, by the semigroup law
    have hiter : ∀ k : ℕ, ∀ y : E, Φ ((k : ℝ) * s) y = (Φ s)^[k] y := by
      intro k
      induction k with
      | zero => intro y; simp [hflow0]
      | succ k ih =>
        intro y
        have h1 : ((k.succ : ℕ) : ℝ) * s = (k : ℝ) * s + s := by push_cast; ring
        rw [h1, flow_add X hX hK Φ hΦ, ih, Function.iterate_succ]
        rfl
    have hfun : (Φ s)^[n] = Φ t := by
      funext y
      rw [← hiter n y, hns]
    rwa [← hfun]
  · -- the arithmetic: `(1 + (exp (K|s|) - 1))^n = exp (K|t|)`
    calc ‖A - 1‖ ≤ (1 + (Real.exp (K * |s|) - 1))^n - 1 := hAb
      _ = (Real.exp (K * |s|))^n - 1 := by ring_nf
      _ = Real.exp ((n : ℝ) * (K * |s|)) - 1 := by rw [Real.exp_nat_mul]
      _ = Real.exp (K * |t|) - 1 := by
            congr 1
            rw [hsabs]
            field_simp

end Work.RPCore.Flow
