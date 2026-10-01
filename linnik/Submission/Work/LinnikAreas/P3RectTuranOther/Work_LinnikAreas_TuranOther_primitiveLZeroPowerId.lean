import Mathlib
import Submission.Work.LinnikAreas.TuranOther.Defs
import Submission.Work.LinnikAreas.TuranOther.PFZeroSumDefs
import Submission.Work.LinnikAreas.P3RectTuranOther.Work_LinnikAreas_TuranOther_completedLDerivZeroSum
import Submission.Work.LinnikAreas.P3RectTuranOther.Work_LinnikAreas_TuranOther_pfUncompleted
import Submission.Work.LinnikAreas.P3RectTuranOther.Work_LinnikAreas_TuranOther_lFunctionOrderAddInvGammaR
import Submission.Work.LinnikAreas.TuranOther.invGammaRZeroSum
import Submission.Work.LinnikAreas.TuranOther.lFunction_eq_completed_mul_invGamma

/-!
# `Work.LinnikAreas.TuranOther.primitiveLZeroPowerId`

The Turán power-sum identity for a primitive non-principal Dirichlet `L`-function:

`Σ_u ord_u(L(·,χ)) · (1/(s-u))^{2j} = -(1/(2j-1)!) · (logDeriv L(·,χ))^{(2j-1)}(s)`, for
`1 < Re s` and `j ≥ 1`.

It is the partial-fraction ("Hadamard") expansion of the logarithmic derivative of `L(·,χ)`,
differentiated `2j-1` times, the constant term of the Hadamard product being killed by the
differentiation.

The proof assembles three already-established ingredients:

* `completedLDerivZeroSum`: the same identity for the completed function
  `Λ = completedLFunction χ` (whose Hadamard product is available from `CompletedDerivPF`);
* `invGammaRZeroSum`: the same identity for the archimedean factor `(Γ_ℝ(·+a))⁻¹`, whose zeros
  are the trivial zeros `-a-2n` of `L(·,χ)`;
* `lFunctionOrderAddInvGammaR` and `iteratedDeriv_logDeriv_mul`: the vanishing orders and the
  logarithmic derivatives are additive over the factorisation
  `L(·,χ) = Λ · (Γ_ℝ(·+a))⁻¹`.
-/

open scoped Classical BigOperators

noncomputable section

namespace Work.LinnikAreas.TuranOther

/-- **The zero-sum (partial-fraction) expansion of `logDeriv L(·,χ)` for primitive `χ`.**

For a primitive non-principal character `χ` mod `q` and the abscissa `1 < Re s`,
the `k`-th derivative of `logDeriv (L(·,χ))` equals `(-1)^k k!` times the multiplicity-weighted
zero sum `Σ_u ord_u(L(·,χ)) (s-u)^{-(k+1)}`, and the latter series is summable.

This is `zeroSumK L s k` in the notation of `PFZeroSumDefs`, i.e.
`HasZeroSumExpansion L s k`. -/
theorem lFunction_logDeriv_zeroSumK {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (k : ℕ) (hk : 1 ≤ k) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : ℂ => ((analyticOrderNatAt (DirichletCharacter.LFunction χ) u : ℕ) : ℂ)
        * (s - u) ^ (-(k + 1) : ℤ)) ∧
    iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) s
      = (-1 : ℂ)^k * (k.factorial : ℂ) *
          zeroSumK (DirichletCharacter.LFunction χ) s k := by
  classical
  -- the factorisation `L(·,χ) = Λ · (Γ_ℝ(·+a))⁻¹`, with `a` the parity of `χ`
  obtain ⟨a, ha0, ha1, hfun⟩ := lFunction_eq_completed_mul_invGamma χ hχ
  set Λ : ℂ → ℂ := DirichletCharacter.completedLFunction χ with hΛdef
  set Γ : ℂ → ℂ := fun z : ℂ => (Complex.Gammaℝ (z + a))⁻¹ with hΓdef
  have hLfun : DirichletCharacter.LFunction χ = fun z => Λ z * Γ z := hfun
  have hΛdiff : Differentiable ℂ Λ := by
    rw [hΛdef]; exact DirichletCharacter.differentiable_completedLFunction hχ
  have hΓdiff : Differentiable ℂ Γ := by
    rw [hΓdef]
    exact Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const (a : ℂ))
  -- non-vanishing at `s` (which lies to the right of the critical strip)
  have hLs : DirichletCharacter.LFunction χ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (le_of_lt hs)
  have hprod : Λ s * Γ s ≠ 0 := by
    intro h; exact hLs (by rw [hLfun]; exact h)
  have hsΛ : Λ s ≠ 0 := (mul_ne_zero_iff.mp hprod).1
  have hsΓ : Γ s ≠ 0 := (mul_ne_zero_iff.mp hprod).2
  -- the two partial-fraction expansions
  obtain ⟨hsumΛ, hidΛ⟩ := completedLDerivZeroSum χ hχ hprim k hk hs
  have ha : a = 0 ∨ a = 1 := by
    rcases χ.even_or_odd with hE | hO
    · exact Or.inl (ha0 hE)
    · exact Or.inr (ha1 hO)
  obtain ⟨hsumΓ, hidΓ⟩ := invGammaRZeroSum a ha k hk hs
  -- additivity of the vanishing orders and of the differentiated log-derivative
  have hord : ∀ u : ℂ, analyticOrderNatAt (DirichletCharacter.LFunction χ) u
      = analyticOrderNatAt Λ u + analyticOrderNatAt Γ u := fun u =>
    lFunctionOrderAddInvGammaR χ hχ a ha0 ha1 u
  have hsummand : ∀ u : ℂ,
      ((analyticOrderNatAt (DirichletCharacter.LFunction χ) u : ℕ) : ℂ) * (s - u) ^ (-(k + 1) : ℤ)
        = ((analyticOrderNatAt Λ u : ℕ) : ℂ) * (s - u) ^ (-(k + 1) : ℤ)
          + ((analyticOrderNatAt Γ u : ℕ) : ℂ) * (s - u) ^ (-(k + 1) : ℤ) := by
    intro u
    rw [hord u, Nat.cast_add]
    ring
  have hsumL : Summable (fun u : ℂ =>
      ((analyticOrderNatAt (DirichletCharacter.LFunction χ) u : ℕ) : ℂ)
        * (s - u) ^ (-(k + 1) : ℤ)) := by
    refine (hsumΛ.add hsumΓ).congr (fun u => ?_)
    exact (hsummand u).symm
  have hZsplit : zeroSumK (DirichletCharacter.LFunction χ) s k
      = zeroSumK Λ s k + zeroSumK Γ s k := by
    unfold zeroSumK
    rw [tsum_congr hsummand, ← Summable.tsum_add hsumΛ hsumΓ]
  have hidL : iteratedDeriv k (logDeriv (DirichletCharacter.LFunction χ)) s
      = iteratedDeriv k (logDeriv Λ) s + iteratedDeriv k (logDeriv Γ) s := by
    rw [hLfun]
    exact iteratedDeriv_logDeriv_mul hΛdiff hΓdiff hsΛ hsΓ k
  refine ⟨hsumL, ?_⟩
  rw [hidL, hidΛ, hidΓ, hZsplit]
  ring

/-- **Linnik's power-sum identity for the zeros of a primitive non-principal `L`-function.**

For a primitive non-principal `χ` mod `q`, `j ≥ 1` and `1 < Re s`,
`Σ_u ord_u(L(·,χ)) (1/(s-u))^{2j} = -(1/(2j-1)!) (logDeriv L(·,χ))^{(2j-1)}(s)`,
the sum running over the zeros of `L(·,χ)` with multiplicity (`analyticOrderNatAt`), and the
series being summable.

This is the `j`-th power sum of the Turán method, written as a rational function of the zeros;
it is obtained from `lFunction_logDeriv_zeroSumK` at `k = 2j-1` by rewriting the `zpowers`
`(s-u)^{-2j}` as `(1/(s-u))^{2j}`. -/
theorem primitiveLZeroPowerId {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hprim : χ.IsPrimitive) (j : ℕ) (hj : 1 ≤ j) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : ℂ => ((analyticOrderNatAt (DirichletCharacter.LFunction χ) u : ℕ) : ℂ) *
        (1 / (s - u)) ^ (2 * j)) ∧
    (∑' u : ℂ, ((analyticOrderNatAt (DirichletCharacter.LFunction χ) u : ℕ) : ℂ) *
        (1 / (s - u)) ^ (2 * j))
      = - (1 / (((2 * j - 1).factorial : ℕ) : ℂ)) *
          iteratedDeriv (2 * j - 1) (logDeriv (DirichletCharacter.LFunction χ)) s := by
  obtain ⟨hsum, hkey⟩ := lFunction_logDeriv_zeroSumK χ hχ hprim (2 * j - 1) (by omega) hs
  have hkj : (2 * j - 1) + 1 = 2 * j := by omega
  have hZ : zeroSumK (DirichletCharacter.LFunction χ) s (2 * j - 1)
      = ∑' u : ℂ, ((analyticOrderNatAt (DirichletCharacter.LFunction χ) u : ℕ) : ℂ)
          * (1 / (s - u)) ^ (2 * j) := by
    unfold zeroSumK
    refine tsum_congr (fun u => ?_)
    rw [neg_zpow_eq_one_div_pow, hkj]
  constructor
  · refine hsum.congr (fun u => ?_)
    rw [neg_zpow_eq_one_div_pow, hkj]
  · rw [← hZ, hkey]
    rw [Odd.neg_one_pow (show Odd (2 * j - 1) from ⟨j - 1, by omega⟩)]
    have hF : (((2 * j - 1).factorial : ℕ) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (2 * j - 1)
    field_simp

end Work.LinnikAreas.TuranOther

end
