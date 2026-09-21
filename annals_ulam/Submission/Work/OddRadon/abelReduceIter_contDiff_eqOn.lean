import Mathlib
import Submission.Work.OddRadon.Abel
import Submission.Work.OddRadon.abelReduceIter_abelTrans

/-!
# Regularity of the iterated Abel reduction (`Work.OddRadon`, part 3c)

`abelReduceIter α k F` is `k` iterated exponent reductions `abelReduce β F = deriv F / (2 β c)`,
i.e. the exponents `α, α-1, …, α-k+1` are used successively (the result lives at exponent `α - k`).

The point of this file is that this operation **peels off powers of the variable `c`**:
if `g c = c^m * h c` with `h` of class `C^N` and `m ≥ 2k`, then on `(0,1)` the function
`abelReduceIter α k g` agrees with a function of the same shape `c^(m-2k) * h'` with
`h'` of class `C^(N-k)`.  This is the technical input that lets the odd-dimensional
Radon inversion be applied to the *leading behaviour at `0`* of the profile.

The proof is an induction on `k`.  Each step writes `abelReduce α g` on `(0,1)` (where
`c ≠ 0`) as `c^(m-2) * h₁` with `h₁ c = (m * h c + c * deriv h c) / (2α)`, using
`deriv (c^m * h c) = m * c^(m-1) * h c + c^m * deriv h c`, and then applies the induction
hypothesis to the pair `(c^(m-2) * h₁, h₁)` and transfers along the congruence
`abelReduceIter_congr` of `abelReduceIter_abelTrans`.

## Main result

* `abelReduceIter_contDiff_eqOn` — the peeling statement.
-/

noncomputable section

open scoped ContDiff

namespace Work.OddRadon

/-- `deriv h` is `C^(N-1)` when `h` is `C^N`, `N ≥ 1` (natural-number form, so that the
exponent stays a `Nat` cast and the `Nat` subtraction bookkeeping is available to `omega`). -/
private lemma contDiff_deriv_nat {N : ℕ} (hN : 1 ≤ N) {h : ℝ → ℝ} (hh : ContDiff ℝ N h) :
    ContDiff ℝ (N - 1) (deriv h) := by
  have hh' : ContDiff ℝ (((N - 1) + 1 : ℕ) : ℕ∞) h := by
    rw [Nat.sub_add_cancel hN]; exact hh
  exact hh'.iterate_deriv' (N - 1) 1

/-- The order shift `N - 1 - k = N - (k+1)` for `ContDiff` orders (which live in
`ℕ∞ω = WithTop ℕ∞`), in the shape produced by the induction. -/
private lemma hsub_nat {N k : ℕ} (h : k + 1 ≤ N) :
    ((N : ℕ∞ω) - ((k + 1 : ℕ) : ℕ∞ω)) = (((N - 1 : ℕ) : ℕ∞ω) - (k : ℕ∞ω)) := by
  change ((↑(N : ℕ∞) : ℕ∞ω) - (↑((k + 1 : ℕ) : ℕ∞) : ℕ∞ω)) =
         ((↑((N - 1 : ℕ) : ℕ∞) : ℕ∞ω) - (↑(k : ℕ∞) : ℕ∞ω))
  rw [← WithTop.coe_sub, ← WithTop.coe_sub, ← ENat.natCast_sub N (k + 1),
      ← ENat.natCast_sub (N - 1) k, show N - (k + 1) = (N - 1) - k by omega]

/-- **One peeling step.**  If `g c = c^m * h c` with `m ≥ 2` and `h` differentiable, then on
`(0,1)` the reduced function `abelReduce α g = deriv g / (2 α c)` is again of the same shape,
one power of `c` lower, with the new profile `(m * h c + c * deriv h c) / (2 α)`. -/
private lemma abelReduce_eqOn_peel {α : ℝ} {m : ℕ} (hm : 2 ≤ m) {g h : ℝ → ℝ}
    (hgm : ∀ c, g c = c ^ m * h c) (hd : Differentiable ℝ h) :
    Set.EqOn (abelReduce α g)
      (fun c => c ^ (m - 2) * ((m * h c + c * deriv h c) / (2 * α))) (Set.Ioo (0:ℝ) 1) := by
  intro c hc
  have hc0 : c ≠ 0 := ne_of_gt hc.1
  have hgc : g = fun x => x ^ m * h x := funext hgm
  have hd' := hd c
  have key : deriv (fun x : ℝ => x ^ m * h x) c = m * c ^ (m - 1) * h c + c ^ m * deriv h c := by
    change deriv ((id : ℝ → ℝ) ^ m * h) c = m * c ^ (m - 1) * h c + c ^ m * deriv h c
    rw [deriv_mul (by fun_prop) hd', deriv_pow (by fun_prop) m]
    simp
  -- the arithmetic: divide the derivative by `2 α c` and cancel one `c`
  have harith : (m * c ^ (m - 1) * h c + c ^ m * deriv h c) / (2 * α * c)
      = c ^ (m - 2) * ((m * h c + c * deriv h c) / (2 * α)) := by
    have hnum : m * c ^ (m - 1) * h c + c ^ m * deriv h c
        = (c ^ (m - 2) * (m * h c + c * deriv h c)) * c := by
      have e1 : c ^ (m - 1) = c ^ (m - 2) * c := by
        conv_lhs => rw [show m - 1 = (m - 2) + 1 by omega]
        rw [pow_add, pow_one]
      have e2 : c ^ m = c ^ (m - 2) * c ^ 2 := by
        conv_lhs => rw [show m = (m - 2) + 2 by omega]
        rw [pow_add]
      rw [e1, e2]
      ring
    rw [hnum, mul_div_mul_right _ _ hc0, mul_div_assoc]
  rw [abelReduce, hgc, key]
  exact harith

/-- **The iterated Abel reduction preserves the shape `c^(m-2k) * (C^(N-k) profile)`.**
If `g = c^m · h` with `h` of class `C^N` and `m ≥ 2k`, then on `(0,1)` the `k`-fold reduced
function `abelReduceIter α k g` agrees with `c^(m-2k) · h'` for some globally `C^(N-k)`
function `h'`. -/
theorem abelReduceIter_contDiff_eqOn (α : ℝ) (k : ℕ) {g h : ℝ → ℝ} {m N : ℕ}
    (hg : ContDiff ℝ N g) (hh : ContDiff ℝ N h) (hgm : ∀ c, g c = c ^ m * h c)
    (hm : 2 * k ≤ m) (hkN : k ≤ N) :
    ∃ (Θ h' : ℝ → ℝ), ContDiff ℝ (N - k) Θ ∧ ContDiff ℝ (N - k) h' ∧
      (∀ c, Θ c = c ^ (m - 2 * k) * h' c) ∧
      Set.EqOn (abelReduceIter α k g) Θ (Set.Ioo (0:ℝ) 1) := by
  induction k generalizing α m N g h with
  | zero =>
    exact ⟨g, h, hg, hh, fun c => hgm c, fun c _ => rfl⟩
  | succ k ih =>
    have hmge : 2 ≤ m := by omega
    have hN1 : 1 ≤ N := by omega
    have hm2 : 2 * k ≤ m - 2 := by omega
    have hNk : k ≤ N - 1 := by omega
    -- the peeled profile and its associated function
    have hd : ContDiff ℝ (N - 1) (deriv h) := contDiff_deriv_nat hN1 hh
    have hlo : ContDiff ℝ (N - 1) h := hh.of_le (by exact tsub_le_self)
    have hh1 : ContDiff ℝ (N - 1) (fun c => (m * h c + c * deriv h c) / (2 * α)) := by
      fun_prop
    have hG1 : ContDiff ℝ (N - 1)
        (fun c => c ^ (m - 2) * ((m * h c + c * deriv h c) / (2 * α))) := by
      fun_prop
    obtain ⟨Θ, h', hΘ, hh', hEq, hEqOn⟩ := ih (α - 1)
      (g := fun c => c ^ (m - 2) * ((m * h c + c * deriv h c) / (2 * α)))
      (h := fun c => (m * h c + c * deriv h c) / (2 * α)) (m := m - 2) (N := N - 1)
      hG1 hh1 (fun c => rfl) hm2 hNk
    refine ⟨Θ, h', ?_, ?_, ?_, ?_⟩
    · exact hsub_nat hkN ▸ hΘ
    · exact hsub_nat hkN ▸ hh'
    · intro c
      rw [show m - 2 * (k + 1) = (m - 2) - 2 * k by omega]
      exact hEq c
    · intro c hc
      have hdiff : Differentiable ℝ h := hh.differentiable (by simp; omega)
      have hstep := abelReduce_eqOn_peel (α := α) hmge hgm hdiff
      have h1 := abelReduceIter_congr hstep (α - 1) k hc
      have h2 := hEqOn hc
      rw [abelReduceIter_succ]
      exact h1.trans h2

end Work.OddRadon
