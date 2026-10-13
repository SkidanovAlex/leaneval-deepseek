import Mathlib
import Submission.Work.WilG4c.ExistsClmTendstoFderivOfCoord
import Submission.Work.WilG4c.TendstoIteratedFDerivFderiv

namespace Work.WilG4c

open scoped BigOperators

/-- From a strictly positive function on a nonempty finite type one can extract a positive
lower bound.  This is the device that turns the finitely many radii produced by the
hypothesis into a single radius valid for all coordinate directions at once. -/
lemma exists_pos_le_of_pos {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ ≤ f i := by
  refine ⟨(Finset.univ : Finset ι).inf' Finset.univ_nonempty f, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    intro i _
    exact hf i
  · intro i
    exact Finset.inf'_le f (Finset.mem_univ i)

/-- If the `(m+1)`-st iterated derivatives of `g`, evaluated on all coordinate-direction
`(m+1)`-tuples, have limits as `x → u` avoiding the centre `u` and the set `S`, then the
`m`-th iterated derivatives of the derivative `x ↦ fderiv ℝ g x` have limits in the operator
norm.

The candidate limit is the continuous linear map `coordCLM s` whose values on the standard
basis vectors `Pi.single j 1` are the prescribed coordinatewise limits `s j`.  Finiteness of
the number `N` of directions lets us intersect the finitely many `ε`-radii into one. -/
theorem IterFDerivFderivDense {N : ℕ} (hN : 1 ≤ N) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {g : (Fin N → ℝ) → F} {u : Fin N → ℝ} {S : Set (Fin N → ℝ)} {m : ℕ}
    (h : ∀ v : Fin (m + 1) → Fin N, ∃ s : F, ∀ ε > 0, ∃ δ > 0, ∀ x, x ≠ u → x ∉ S →
        dist x u < δ → ‖iteratedFDeriv ℝ (m + 1) g x (fun i => Pi.single (v i) 1) - s‖ < ε) :
    ∀ v : Fin m → Fin N, ∃ s : (Fin N → ℝ) →L[ℝ] F, ∀ ε > 0, ∃ δ > 0, ∀ x, x ≠ u → x ∉ S →
        dist x u < δ →
        ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ g y) x (fun i => Pi.single (v i) 1) - s‖ < ε := by
  intro v
  classical
  -- `Fin N` is nonempty, so the finite intersection of radii below is over a nonempty index type.
  haveI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  -- Extract the coordinatewise limits, one for each extension of `v` by a last direction.
  choose s hs using fun j : Fin N => h (Fin.snoc v j)
  -- The candidate limit is the map whose coordinate values are `s`.
  refine ⟨coordCLM s, ?_⟩
  intro ε hε
  -- A safety margin for the finitely many coordinate estimates.
  obtain ⟨ε', hε'pos, hε'def⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' = ε / ((N : ℝ) + 1) := by
    refine ⟨ε / ((N : ℝ) + 1), ?_, rfl⟩
    positivity
  -- Radii controlling each coordinate direction.
  choose δf hδfpos hδf using fun j : Fin N => hs j ε' hε'pos
  obtain ⟨δ, hδpos, hδle⟩ := exists_pos_le_of_pos δf hδfpos
  refine ⟨δ, hδpos, ?_⟩
  intro x hxu hxS hxd
  -- Bound the operator norm of the difference by the sum of its coordinate norms.
  refine lt_of_le_of_lt (clm_norm_le_sum_basis
    (iteratedFDeriv ℝ m (fun y => fderiv ℝ g y) x (fun i => Pi.single (v i) 1)
      - coordCLM s)) ?_
  calc ∑ j : Fin N, ‖(iteratedFDeriv ℝ m (fun y => fderiv ℝ g y) x
            (fun i => Pi.single (v i) 1) - coordCLM s) (Pi.single j 1)‖
      < ∑ _j : Fin N, ε' := by
        apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
        intro j _
        rw [sub_apply, coordCLM_apply_basis s j, ← iteratedFDeriv_succ_apply_snoc v j]
        exact hδf j x hxu hxS (lt_of_lt_of_le hxd (hδle j))
    _ = (N : ℝ) * ε' := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ < ε := by
        rw [hε'def, ← mul_div_assoc]
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
        nlinarith [hε]

end Work.WilG4c
