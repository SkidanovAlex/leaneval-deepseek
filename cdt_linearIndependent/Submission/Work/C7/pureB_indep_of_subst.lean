import Mathlib
import Submission.Work.C7.xdefs

/-!
# Area C7 — descent of the `ℚ(y)`-independence of `B₁,…,B₇` from the `x`-side

The paper's Lemma `seven` (the pure functions `B₁,…,B₇` are `ℚ(y)`-linearly independent) is
proved in this project on the `x`-side: put `y = yps = x²/(x-1)` and use the rationally
parametrised functions `1, L, L², Li₂, J, ∫…`.  This module supplies the **descent step**:
if the seven pullbacks `Bᵢ∘y` are `ℚ[x]`-linearly independent (with polynomial coefficients),
then `B₁,…,B₇` are `ℚ[y]`-linearly independent.

The point is that `yps` is a *rational* function of `x`, `yps·(x-1) = x²`: a relation
`Σᵢ qᵢ(y)·Bᵢ(y) = 0` with `qᵢ ∈ ℚ[y]` becomes, after substituting `y ↦ yps` and multiplying by
`(x-1)^N` (`N` bounding the degrees), a relation `Σᵢ cᵢ(x)·(Bᵢ∘yps) = 0` with *polynomial*
coefficients `cᵢ ∈ ℚ[x]`.  The hypothesis then forces `cᵢ = 0`; evaluating at `x = 1` reads off
the top coefficient of `qᵢ`, and induction on `N` concludes.

No transcendence statement about `yps` is needed: the extraction of the coefficients is done by
the multiplication by powers of `x - 1`.
-/

noncomputable section

namespace Work.C7

open PowerSeries

/-- The pullbacks `Bᵢ∘y` (`y = yps = x²/(x-1)`) of the seven pure functions. -/
def gB : Fin 7 → PowerSeries ℚ := fun i => (Submission.CDTPlan.pureB i).subst yps

/-- `yps·(x-1) = x²`, the rationality relation making the descent work. -/
lemma yps_mul_sub_one : yps * ((PowerSeries.X : PowerSeries ℚ) - 1) = PowerSeries.X ^ 2 := by
  have h := Submission.CDT.symp_quadratic
  calc yps * ((PowerSeries.X : PowerSeries ℚ) - 1)
      = yps * PowerSeries.X - yps := by ring
    _ = PowerSeries.X ^ 2 := by linear_combination -h

/-- `(x-1)^N·Q(yps) = c(x)` where `c` is an explicit polynomial, for `deg Q ≤ N`. -/
def coeffPol (N : ℕ) (Q : Polynomial ℚ) : Polynomial ℚ :=
  ∑ k ∈ Finset.range (N + 1), Polynomial.C (Q.coeff k) * Polynomial.X ^ (2 * k) *
    (Polynomial.X - 1) ^ (N - k)

theorem aeval_mul_sub_one_pow (t : PowerSeries ℚ)
    (ht : t * ((PowerSeries.X : PowerSeries ℚ) - 1) = PowerSeries.X ^ 2)
    (N : ℕ) (Q : Polynomial ℚ) (hQ : Q.natDegree ≤ N) :
    Polynomial.aeval t Q * ((PowerSeries.X : PowerSeries ℚ) - 1) ^ N =
      (coeffPol N Q : PowerSeries ℚ) := by
  rw [Polynomial.aeval_eq_sum_range' (by omega : Q.natDegree < N + 1)]
  rw [Finset.sum_mul]
  rw [show (coeffPol N Q : PowerSeries ℚ)
      = ∑ k ∈ Finset.range (N + 1), (PowerSeries.C (Q.coeff k)) * PowerSeries.X ^ (2 * k) *
        (PowerSeries.X - 1) ^ (N - k) from by
      rw [coeffPol, ← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
      simp]
  refine Finset.sum_congr rfl ?_
  intro k hk
  rw [Finset.mem_range] at hk
  have hpow : t ^ k * ((PowerSeries.X : PowerSeries ℚ) - 1) ^ N =
      PowerSeries.X ^ (2 * k) * ((PowerSeries.X : PowerSeries ℚ) - 1) ^ (N - k) := by
    calc t ^ k * ((PowerSeries.X : PowerSeries ℚ) - 1) ^ N
        = t ^ k * (((PowerSeries.X : PowerSeries ℚ) - 1) ^ (N - k) *
            ((PowerSeries.X : PowerSeries ℚ) - 1) ^ k) := by
            rw [← pow_add, Nat.sub_add_cancel (show k ≤ N by omega)]
      _ = ((PowerSeries.X : PowerSeries ℚ) - 1) ^ (N - k) *
            (t ^ k * ((PowerSeries.X : PowerSeries ℚ) - 1) ^ k) := by ring
      _ = ((PowerSeries.X : PowerSeries ℚ) - 1) ^ (N - k) *
            (t * ((PowerSeries.X : PowerSeries ℚ) - 1)) ^ k := by rw [mul_pow]
      _ = ((PowerSeries.X : PowerSeries ℚ) - 1) ^ (N - k) * (PowerSeries.X ^ 2) ^ k := by
            rw [ht]
      _ = PowerSeries.X ^ (2 * k) * ((PowerSeries.X : PowerSeries ℚ) - 1) ^ (N - k) := by ring
  rw [Algebra.smul_def, mul_assoc, hpow]
  simp only [PowerSeries.C_eq_algebraMap]
  ring

/-- Evaluating `coeffPol N Q` at `1` gives the top coefficient `Q.coeff N`. -/
theorem eval_one_coeffPol (N : ℕ) (Q : Polynomial ℚ) : (coeffPol N Q).eval 1 = Q.coeff N := by
  rw [coeffPol, Polynomial.eval_finsetSum]
  rw [Finset.sum_eq_single N]
  · simp
  · intro k hk hne
    rw [Finset.mem_range] at hk
    have h1 : N - k ≠ 0 := by omega
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_one]
    simp [h1]
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega : N < N + 1)) h

/-- **The coefficient extraction.**  If `Σᵢ Qᵢ(yps)·(Bᵢ∘yps) = 0` and `deg Qᵢ ≤ N`, then the
top coefficients `(Qᵢ).coeff N` vanish: multiplying by `(x-1)^N` turns the relation into one with
polynomial coefficients, to which the `x`-side independence hypothesis applies; evaluating the
resulting polynomial at `1` leaves only the top coefficient. -/
theorem coeff_eq_zero_of_aeval_rel (h : Submission.CDTPlan.PolyIndependent gB)
    (N : ℕ) (Q : Fin 7 → Polynomial ℚ)
    (hcond : ∀ i, ∀ m, N < m → (Q i).coeff m = 0)
    (hrel : ∑ i : Fin 7, Polynomial.aeval yps (Q i) * gB i = 0) :
    ∀ i, (Q i).coeff N = 0 := by
  have hmain : ∀ i : Fin 7, (coeffPol N (Q i) : PowerSeries ℚ) =
      Polynomial.aeval yps (Q i) * ((PowerSeries.X : PowerSeries ℚ) - 1) ^ N := fun i =>
    (aeval_mul_sub_one_pow yps yps_mul_sub_one N (Q i)
      (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (hcond i))).symm
  have hrel' : ∑ i : Fin 7, (coeffPol N (Q i) : PowerSeries ℚ) * gB i = 0 := by
    calc ∑ i : Fin 7, (coeffPol N (Q i) : PowerSeries ℚ) * gB i
        = ∑ i : Fin 7, (Polynomial.aeval yps (Q i) *
            ((PowerSeries.X : PowerSeries ℚ) - 1) ^ N) * gB i :=
          Finset.sum_congr rfl (fun i _ => by rw [hmain i])
      _ = (∑ i : Fin 7, Polynomial.aeval yps (Q i) * gB i) *
            ((PowerSeries.X : PowerSeries ℚ) - 1) ^ N := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = 0 := by rw [hrel, zero_mul]
  have h0 := h (fun i => coeffPol N (Q i)) hrel'
  intro i
  have hi : (coeffPol N (Q i)) = 0 := h0 i
  have h1 : (coeffPol N (Q i)).eval 1 = 0 := by rw [hi]; simp
  rwa [eval_one_coeffPol] at h1

/-- **Descent.**  `ℚ[x]`-independence of the pullbacks implies `ℚ[y]`-independence of `B₁,…,B₇`:
induction on a bound `N` for the degrees of the coefficient polynomials. -/
theorem pureB_indep_of_subst
    (h : Submission.CDTPlan.PolyIndependent
      (fun i : Fin 7 => (Submission.CDTPlan.pureB i).subst Work.C7.yps)) :
    Submission.CDTPlan.PolyIndependent Submission.CDTPlan.pureB := by
  have h' : Submission.CDTPlan.PolyIndependent gB := h
  have key : ∀ N (Q : Fin 7 → Polynomial ℚ),
      (∀ i, ∀ m, N < m → (Q i).coeff m = 0) →
      (∑ i : Fin 7, Polynomial.aeval yps (Q i) * gB i = 0) → ∀ i, Q i = 0 := by
    intro N
    induction N with
    | zero =>
      intro Q hcond hrel
      have h0 := coeff_eq_zero_of_aeval_rel h' 0 Q hcond hrel
      intro i
      ext m
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm; exact h0 i
      · exact hcond i m hm
    | succ N ih =>
      intro Q hcond hrel
      have hc := coeff_eq_zero_of_aeval_rel h' (N + 1) Q hcond hrel
      refine ih Q ?_ hrel
      intro i m hm
      rcases eq_or_lt_of_le (show N + 1 ≤ m by omega) with heq | hlt
      · rw [← heq]; exact hc i
      · exact hcond i m hlt
  intro P hP
  have hrel : ∑ i : Fin 7, Polynomial.aeval yps (P i) * gB i = 0 := by
    have h1 : (PowerSeries.substAlgHom Submission.CDT.sympY_hasSubst)
        (∑ i : Fin 7, (P i : PowerSeries ℚ) * Submission.CDTPlan.pureB i) = 0 := by
      rw [hP, map_zero]
    have h2 : (PowerSeries.substAlgHom Submission.CDT.sympY_hasSubst)
        (∑ i : Fin 7, (P i : PowerSeries ℚ) * Submission.CDTPlan.pureB i)
        = ∑ i : Fin 7, Polynomial.aeval yps (P i) * gB i := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [map_mul, PowerSeries.coe_substAlgHom,
        PowerSeries.subst_coe Submission.CDT.sympY_hasSubst]
      rfl
    rw [h2] at h1
    exact h1
  refine key (Finset.univ.sup fun i : Fin 7 => (P i).natDegree) P ?_ hrel
  intro i m hm
  exact Polynomial.natDegree_le_iff_coeff_eq_zero.mp
    (Finset.le_sup (f := fun i : Fin 7 => (P i).natDegree) (Finset.mem_univ i)) m hm

end Work.C7
