/-
  `Work.WilLibTS.TS.SignElimination.polynomialSignSet_projection_snoc`

  A specialisation of the projection theorem
  `Work.WilLibTS.TS.SignElimination.polynomialSignSet_projection_sum` (module
  `Submission.Work.WilLibTS.TS.PolynomialSignSetProjection2`) to the situation in which the last
  coordinate of `Fin (m+1) → ℝ` is split off with `Fin.snoc`:

  the projection `{x : Fin m → ℝ | ∃ t : ℝ, Fin.snoc x t ∈ S}` of a `PolynomialSignSet`
  `S ⊆ Fin (m+1) → ℝ` (identity coordinate map) is again a `PolynomialSignSet`.

  The only combinatorial input is `fin_snoc_eq_sumElim` below, which identifies `Fin.snoc` with
  `Sum.elim` along the equivalence `Fin m ⊕ Fin 1 ≃ Fin (m + 1)`; that lets us feed `S` into the
  `Sum`-coordinates form of the projection theorem.
-/
import Mathlib
import Submission.Work.WilLibTS.TS.ProjectionCorollaries

namespace Work.WilLibTS.TS.SignElimination

/-- `Fin.snoc` is `Sum.elim` along `finSumFinEquiv : Fin m ⊕ Fin 1 ≃ Fin (m + 1)`:
appending `y 0` to the tuple `x` is the same as reading the `Fin (m+1)`-tuple through the
equivalence into the pair `(x, y)`. -/
lemma fin_snoc_eq_sumElim (m : ℕ) (x : Fin m → ℝ) (y : Fin 1 → ℝ) :
    Fin.snoc x (y 0) = (fun i : Fin (m + 1) => Sum.elim x y (finSumFinEquiv.symm i)) := by
  rw [← Fin.append_right_eq_snoc x y]
  funext i
  rcases h : finSumFinEquiv.symm i with a | b
  · have hi : i = Fin.castAdd 1 a := by
      rw [← finSumFinEquiv_apply_left (m := m) (n := 1) a, ← h, Equiv.apply_symm_apply]
    rw [hi, Fin.append_left, Sum.elim_inl]
  · have hi : i = Fin.natAdd m b := by
      rw [← finSumFinEquiv_apply_right (m := m) (n := 1) b, ← h, Equiv.apply_symm_apply]
    rw [hi, Fin.append_right, Sum.elim_inr]

theorem polynomialSignSet_projection_snoc {m : ℕ} {S : Set (Fin (m + 1) → ℝ)}
    (hS : Work.WilLibTS.TS.PolynomialSignSet (id : (Fin (m + 1) → ℝ) → Fin (m + 1) → ℝ) S) :
    Work.WilLibTS.TS.PolynomialSignSet (id : (Fin m → ℝ) → Fin m → ℝ)
      {x : Fin m → ℝ | ∃ t : ℝ, Fin.snoc x t ∈ S} := by
  classical
  -- Re-read the coordinates of `Fin (m+1) → ℝ` as `Fin m ⊕ Fin 1` through `finSumFinEquiv`.
  have hS' : Work.WilLibTS.TS.PolynomialSignSet
      (id : ((Fin m ⊕ Fin 1) → ℝ) → (Fin m ⊕ Fin 1) → ℝ)
      ((fun u : (Fin m ⊕ Fin 1) → ℝ => fun i : Fin (m + 1) => u (finSumFinEquiv.symm i)) ⁻¹' S) :=
    hS.coordinate_preimage
      (fun u : (Fin m ⊕ Fin 1) → ℝ => fun i : Fin (m + 1) => u (finSumFinEquiv.symm i))
      finSumFinEquiv.symm (by intro u i; rfl)
  -- Eliminate the single `Fin 1`-coordinate by the projection theorem.
  have hproj := Work.WilLibTS.TS.SignElimination.polynomialSignSet_projection_sum
    (ι := Fin m) (κ := Fin 1) hS'
  refine hproj.congr ?_
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_preimage]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y 0, by rw [fin_snoc_eq_sumElim m x y]; exact hy⟩
  · rintro ⟨t, ht⟩
    exact ⟨(fun _ : Fin 1 => t), by
      rw [← fin_snoc_eq_sumElim m x (fun _ : Fin 1 => t)]
      exact ht⟩

end Work.WilLibTS.TS.SignElimination
