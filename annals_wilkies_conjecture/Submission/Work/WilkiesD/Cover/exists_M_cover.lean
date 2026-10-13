import Submission.Work.WilkiesD.Proj

namespace Work.WilkiesD.Cover

open WilkiesDesign WilkiesConjecture

/-- **Truncation: covering the witnesses of a finite set.**  If `X` is the projection of the zero
set of the exp-polynomial `P` (i.e. `X` is given by the witness data of `ExpExist`, in the
`Fin.append` form), and the finite set `T ⊆ X`, then for a single real `M` all points of `T` are
covered by witnesses inside the box `[-M,M]^(n+m)`: `T ⊆ projFst m (boxZero M P)`. -/
theorem exists_M_cover {n m : ℕ} {P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ}
    {X : Set (Fin n → ℝ)}
    (hX : X = {x | ∃ y : Fin m → ℝ, expPolyEval P (Fin.append x y) = 0})
    (T : Finset (Fin n → ℝ)) (hT : (↑T : Set (Fin n → ℝ)) ⊆ X) :
    ∃ M : ℝ, (↑T : Set (Fin n → ℝ)) ⊆ projFst m (boxZero M P) := by
  classical
  -- For each point `x` we fix once and for all a witness `w x` (if one exists, else `0`).
  let w : (Fin n → ℝ) → Fin m → ℝ := fun x =>
    if h : ∃ y : Fin m → ℝ, expPolyEval P (Fin.append x y) = 0 then Classical.choose h else 0
  -- `w x` is a genuine witness whenever `x ∈ T`.
  have hw (x : Fin n → ℝ) (hx : x ∈ T) : expPolyEval P (Fin.append x (w x)) = 0 := by
    have hxX : x ∈ X := hT hx
    rw [hX] at hxX
    simp only [Set.mem_ofPred_eq] at hxX
    have hwx : w x = Classical.choose hxX := by
      simp only [w, dite_eq_left hxX]
    rw [hwx]
    exact Classical.choose_spec hxX
  by_cases hne : T.Nonempty
  · -- `M` is the supremum over `T` of the `ℓ¹`-size of the witness vectors.
    refine ⟨T.sup' hne (fun x => ∑ i, |(Fin.append x (w x)) i|) + 1, ?_⟩
    intro x hxT
    rw [projFst_mem_iff]
    refine ⟨w x, ?_⟩
    rw [boxZero, Set.mem_ofPred_eq]
    refine ⟨?_, hw x hxT⟩
    intro i
    have h1 : |(Fin.append x (w x)) i| ≤ ∑ j, |(Fin.append x (w x)) j| := by
      simpa using Finset.single_le_sum (s := Finset.univ)
        (fun j _ => abs_nonneg ((Fin.append x (w x)) j)) (Finset.mem_univ i)
    have h2 : ∑ j, |(Fin.append x (w x)) j|
        ≤ T.sup' hne (fun x => ∑ i, |(Fin.append x (w x)) i|) :=
      Finset.le_sup' (fun x => ∑ i, |(Fin.append x (w x)) i|) hxT
    linarith
  · -- `T` is empty: any `M` works.
    exact ⟨1, fun x hxT => absurd ⟨x, hxT⟩ hne⟩

end Work.WilkiesD.Cover
