import Mathlib
import Submission.Work.Pert.Orbit
import Submission.Work.Pert.angle
import Submission.Work.Pert.Coordinate

/-!
# PERT: the orbit relation (Shishikura (4.2.3)) reduced to the walk and the angle lemma

This file proves `Work.Pert.orbit_reduce`, the abstract form of Shishikura's (4.2.3) used by the
`PertData.orbit` field: it produces the integer iterate `n ≥ 1` with `f^[n] (φ w) = φ w'` from

* the `R`-invariance `φ ∘ R = φ` of the perturbed coordinate,
* the Abel walk `φ (x + k) = f^[k] (φ x)` along `x, x+1, …, x+k` (with the intermediate points in
  `Df`), together with `R^[j] w ∈ Dφ` for `j ≤ m`,
* the fibre relation `piExp (R^[m] w) = piExp w'`, which produces the integer `k : ℤ` with
  `R^[m] w = w' + k`,
* the smallness `‖m/α + (R^[m] w - w)‖ < m/(20‖α‖)` of the accumulated error of the return map,
* the sector condition `|arg (w' + 1/(2α) - w)| < 2π/3`.

`Work.Pert.angle` (A.4.5′) converts the last two into `1 ≤ -k`, so `n := -k` is the (positive)
number of iterates, and `w' = R^[m] w + n`; the walk at the point `R^[m] w` then gives
`φ w' = f^[n] (φ (R^[m] w)) = f^[n] (φ w)`, all intermediate iterates lying in `Df`.
-/

namespace Work.Pert

open MandelDim Complex

theorem orbit_reduce {f φ R : ℂ → ℂ} {Dφ Df : Set ℂ} {α : ℂ} {w w' : ℂ} {m : ℕ}
    (hF1 : MandelDim.InF1 α) (hm : 1 ≤ m)
    (hphi : ∀ x ∈ Dφ, φ (R x) = φ x)
    (hwalk : ∀ x ∈ Dφ, ∀ k : ℕ, x + (k : ℂ) ∈ Dφ →
      φ (x + (k : ℂ)) = f^[k] (φ x) ∧ (∀ i : ℕ, i < k → f^[i] (φ x) ∈ Df))
    (hw : w ∈ Dφ) (hRj : ∀ j : ℕ, j ≤ m → R^[j] w ∈ Dφ) (hw' : w' ∈ Dφ)
    (hpi : MandelDim.piExp (R^[m] w) = MandelDim.piExp w')
    (hsmall : ‖(m : ℂ) / α + (R^[m] w - w)‖ < (m : ℝ) / (20 * ‖α‖))
    (harg : |Complex.arg (w' + 1 / (2 * α) - w)| < 2 * Real.pi / 3) :
    ∃ n : ℕ, 1 ≤ n ∧ f^[n] (φ w) = φ w' ∧ ∀ i : ℕ, i < n → f^[i] (φ w) ∈ Df := by
  -- `α ≠ 0`: `InF1 α` means `|Im α| < Re α`, which fails at `α = 0`.
  have hα0 : α ≠ 0 := by
    intro h
    have h1 : MandelDim.InF1 0 := by rw [← h]; exact hF1
    have h2 : ¬ MandelDim.InF1 0 := by
      unfold MandelDim.InF1
      norm_num
    exact h2 h1
  -- `φ` is invariant under all iterates `R^[j] w`, `j ≤ m`.
  have hφiter : ∀ j : ℕ, j ≤ m → φ (R^[j] w) = φ w := by
    intro j hj
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      rw [hphi (R^[j] w) (hRj j (by omega))]
      exact ih (by omega)
  have hφx : φ (R^[m] w) = φ w := hφiter m le_rfl
  -- (4.2.3): `piExp` equality gives the integer displacement.
  obtain ⟨k, hk⟩ := (piExp_eq_iff (R^[m] w) w').mp hpi
  have hw'k : w' = R^[m] w - (k : ℂ) := by rw [hk]; ring
  -- the sector hypothesis, rewritten as the `x` of `Work.Pert.angle` with `k' = -k`
  have hxeq : w' + 1 / (2 * α) - w =
      ((-k : ℤ) : ℂ) + ((m : ℂ) / α + (R^[m] w - w)) - ((m : ℂ) - 1 / 2) / α := by
    rw [hw'k]
    push_cast
    field_simp
    ring
  -- (A.4.5′): the exponent is positive.
  have hk1 : (1 : ℤ) ≤ -k :=
    angle hF1 hm hsmall (w' + 1 / (2 * α) - w) hxeq harg
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, 1 ≤ n ∧ (n : ℤ) = -k := by
    refine ⟨(-k).toNat, ?_, ?_⟩
    · have h0 : (0 : ℤ) ≤ -k := by omega
      have h2 : (1 : ℤ) ≤ ((-k).toNat : ℤ) := by
        rw [Int.toNat_of_nonneg h0]; exact hk1
      exact_mod_cast h2
    · exact Int.toNat_of_nonneg (by omega)
  have hnC : (n : ℂ) = -(k : ℂ) := by
    have h2 : ((n : ℤ) : ℂ) = ((-k : ℤ) : ℂ) := by rw [hn2]
    push_cast at h2
    exact h2
  -- `w'` is the `n`-th forward translate of `R^[m] w`.
  have hw'n : w' = R^[m] w + (n : ℂ) := by rw [hw'k, hnC]; ring
  obtain ⟨hwalkeq, hwalkmem⟩ := hwalk (R^[m] w) (hRj m le_rfl) n (by rw [← hw'n]; exact hw')
  refine ⟨n, hn1, ?_, ?_⟩
  · rw [← hφx, ← hwalkeq, ← hw'n]
  · intro i hi
    simpa [hφx] using hwalkmem i hi

end Work.Pert
