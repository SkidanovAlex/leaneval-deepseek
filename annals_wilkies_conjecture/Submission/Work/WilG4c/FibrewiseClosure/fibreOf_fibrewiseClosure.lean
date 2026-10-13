/-
  WilG4c / `FibrewiseClosure` — the fibres of the fibre-wise closure.

  `fibrewiseClosure Z` is the set of points `w = (l, z)` such that `z` lies in the closure of
  the fibre `Z_l`; it is written with an explicit `∀ε>0 ∃z'` (see `FibreCoreDefs`).  Here we
  prove the identity

    `fibreOf (fibrewiseClosure Z) l = closure (fibreOf Z l)`,

  i.e. the fibre of the fibre-wise closure over a *fixed* parameter `l` is exactly the closure
  of the fibre.  This is what lets the F-lemma of BNZ §5 replace a closed condition on the
  fibre by the first-order condition defining the `Ω`-set `fibrewiseClosure Z`.

  The mathematical content is a small piece of the metric topology of `ℝ^N`, isolated in the
  two lemmas `dist_lt_of_sumsq_lt` and `sumsq_lt_of_dist_lt`: on `Fin N → ℝ` (with the sup
  metric) the "strictly sumsq-close" points and the "metric-close" points are the same notion
  of approximation.  Concretely, `∑_j (z_j - y_j)^2 < ε^2` implies `dist z y < ε` because each
  single square is bounded by the whole sum; conversely `dist z y < ε` implies
  `∑_j (z_j - y_j)^2 ≤ N · (ε/(N+1))^2 < ε^2` (the harmless `N/(N+1)` factor is what makes the
  inequality strict without square roots).
-/
import Mathlib
import Submission.Work.WilG4c.FibreCoreDefs
import Submission.Work.WilG4c.StepCleanDefs

set_option autoImplicit false

namespace Work.WilG4c.FibrewiseClosure

/-! ## Metric comparison of the two notions of "close" -/

/-- If `z` is sumsq-close to `y` at scale `ε`, it is also sup-metric close: each single
squared coordinate difference is bounded by the whole sum. -/
theorem dist_lt_of_sumsq_lt {N : ℕ} {y z : Fin N → ℝ} {ε : ℝ} (hε : 0 < ε)
    (h : (∑ j : Fin N, (z j - y j) ^ 2) < ε ^ 2) : dist z y < ε := by
  rw [dist_pi_lt_iff hε]
  intro j
  rw [Real.dist_eq]
  have hle : (z j - y j) ^ 2 ≤ ∑ i : Fin N, (z i - y i) ^ 2 :=
    Finset.single_le_sum (f := fun i => (z i - y i) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  have hlt : (z j - y j) ^ 2 < ε ^ 2 := lt_of_le_of_lt hle h
  have h2 : |z j - y j| < |ε| := (sq_lt_sq).mp hlt
  rwa [abs_of_pos hε] at h2

/-- Conversely, sup-metric closeness at the (smaller) scale `ε/(N+1)` gives sumsq-closeness at
scale `ε`.  This is the only place where the number of coordinates `N` enters. -/
theorem sumsq_lt_of_dist_lt {N : ℕ} {y z : Fin N → ℝ} {ε : ℝ} (hε : 0 < ε)
    (h : dist z y < ε / ((N : ℝ) + 1)) :
    (∑ j : Fin N, (z j - y j) ^ 2) < ε ^ 2 := by
  have hδ : 0 < ε / ((N : ℝ) + 1) := by positivity
  have hper : ∀ j : Fin N, |z j - y j| < ε / ((N : ℝ) + 1) := fun j => by
    have hh := (dist_pi_lt_iff hδ).1 h j
    rwa [Real.dist_eq] at hh
  have hterm : ∀ j : Fin N, (z j - y j) ^ 2 < (ε / ((N : ℝ) + 1)) ^ 2 := fun j => by
    have h1 : |z j - y j| ^ 2 < (ε / ((N : ℝ) + 1)) ^ 2 := by
      rw [sq_lt_sq, abs_abs, abs_of_pos hδ]
      exact hper j
    rwa [sq_abs] at h1
  have harith : (N : ℝ) * (ε / ((N : ℝ) + 1)) ^ 2 < ε ^ 2 := by
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have h2 : (N : ℝ) < ((N : ℝ) + 1) ^ 2 := by nlinarith
    have h3 : (N : ℝ) * (ε / ((N : ℝ) + 1)) ^ 2 =
        (N : ℝ) * ε ^ 2 / ((N : ℝ) + 1) ^ 2 := by
      rw [div_pow]; ring
    rw [h3, div_lt_iff₀ (by positivity : (0 : ℝ) < ((N : ℝ) + 1) ^ 2)]
    nlinarith [sq_pos_of_pos hε]
  calc ∑ j : Fin N, (z j - y j) ^ 2
      ≤ ∑ _j : Fin N, (ε / ((N : ℝ) + 1)) ^ 2 := Finset.sum_le_sum (fun j _ => (hterm j).le)
    _ = (N : ℝ) * (ε / ((N : ℝ) + 1)) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ < ε ^ 2 := harith

/-! ## The closure described by the explicit `∀ε>0 ∃z'` formula -/

/-- **Closure via the sumsq formula.** A point `y` lies in the closure of `A ⊆ ℝ^N` iff
arbitrarily sumsq-close points of `A` exist. -/
theorem closure_eq_sumsq (N : ℕ) (A : Set (Fin N → ℝ)) :
    {y : Fin N → ℝ | ∀ ε : ℝ, 0 < ε → ∃ z' : Fin N → ℝ,
      (∑ j : Fin N, (z' j - y j) ^ 2) < ε ^ 2 ∧ z' ∈ A} = closure A := by
  ext y
  rw [Set.mem_ofPred_eq, Metric.mem_closure_iff]
  constructor
  · intro h ε hε
    obtain ⟨z', hz', hmem⟩ := h ε hε
    refine ⟨z', hmem, ?_⟩
    rw [dist_comm]
    exact dist_lt_of_sumsq_lt hε hz'
  · intro h ε hε
    have hδ : 0 < ε / ((N : ℝ) + 1) := by positivity
    obtain ⟨z', hmem, hdist⟩ := h (ε / ((N : ℝ) + 1)) hδ
    exact ⟨z', sumsq_lt_of_dist_lt hε (by rwa [dist_comm] at hdist), hmem⟩

/-- **The fibre of the fibre-wise closure.** Unfolding the two definitions, the fibre over `l`
of `fibrewiseClosure Z` is described by exactly the sumsq formula of `closure_eq_sumsq`
applied to the fibre `fibreOf Z l`. -/
theorem fibreOf_fibrewiseClosure_eq (p N : ℕ) (Z : Set (Fin (p + N) → ℝ)) (l : Fin p → ℝ) :
    Work.WilG4c.fibreOf (Work.WilG4c.fibrewiseClosure Z) l =
      {y : Fin N → ℝ | ∀ ε : ℝ, 0 < ε → ∃ z' : Fin N → ℝ,
        (∑ j : Fin N, (z' j - y j) ^ 2) < ε ^ 2 ∧ z' ∈ Work.WilG4c.fibreOf Z l} := by
  ext y
  simp only [Work.WilG4c.fibreOf, Set.mem_ofPred_eq, Work.WilG4c.fibrewiseClosure]
  constructor
  · rintro h ε hε
    obtain ⟨z', hz', hZ⟩ := h ε hε
    have heq : (fun i : Fin p => (Fin.append l y) (Fin.castAdd N i)) = l := by
      funext i; exact Fin.append_left l y i
    exact ⟨z', by simpa using hz', by rwa [heq] at hZ⟩
  · rintro h ε hε
    obtain ⟨z', hz', hZ⟩ := h ε hε
    have heq : (fun i : Fin p => (Fin.append l y) (Fin.castAdd N i)) = l := by
      funext i; exact Fin.append_left l y i
    exact ⟨z', by simpa using hz', by rwa [heq]⟩

/-- The fibre of the fibre-wise closure of `Z` over a parameter `l` is the closure of the
fibre of `Z` over `l`. -/
theorem fibreOf_fibrewiseClosure (p N : ℕ) (Z : Set (Fin (p + N) → ℝ)) (l : Fin p → ℝ) :
    Work.WilG4c.fibreOf (Work.WilG4c.fibrewiseClosure Z) l = closure (Work.WilG4c.fibreOf Z l) := by
  rw [fibreOf_fibrewiseClosure_eq p N Z l, closure_eq_sumsq N (Work.WilG4c.fibreOf Z l)]

end Work.WilG4c.FibrewiseClosure
