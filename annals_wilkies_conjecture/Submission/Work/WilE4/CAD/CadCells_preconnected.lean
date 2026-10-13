import Mathlib
import Submission.Work.WilE4.CAD.Decomp
import Submission.Work.WilE4.CAD.Level
import Submission.Work.WilE4.CAD.cell_preconnected
import Submission.Work.WilE4.CAD.Size
import Submission.Work.WilE4.CAD.CadCells_isUnionOf
import Submission.Work.WilE4.CAD.Proj
import Submission.Work.WilE4.CAD.syl_minor_type_const

namespace Work.WilE4.CAD

/-! ## Sign constancy of the projection data on a base cell

A cell `C` of `CadCells k (projDataT k H)` is a sign condition of `projDataT k H`, which contains
`projData H` (`projData_subset_projDataT`), hence the signs of all coefficients of the
specialisations of the members of `H` — and therefore the principal-subresultant data — are constant
on it.  These are the `hconst`/`hcoeff` hypotheses of `cell_preconnected` and of
`syl_minor_type_const`. -/

/-- The signs of the coefficients of the specialisations of the members of `H` are constant on a cell
of the decomposition of the projection data. -/
theorem coeff_signConst_mem_CadCells {k : ℕ} (H : List (MvPolynomial (Fin (k + 1)) ℝ))
    (C : SAd k) (hC : C ∈ CadCells k (projDataT k H)) :
    ∀ i : Fin H.length, ∀ j : ℕ, j ≤ famDeg H → ∀ x ∈ C.set, ∀ x' ∈ C.set,
      SignType.sign ((spec (H.get i) x).coeff j) = SignType.sign ((spec (H.get i) x').coeff j) := by
  obtain ⟨w, hw⟩ := exists_signCond_of_mem_CadCells k (projDataT k H) hC
  have hsc : SignConstOn (projDataT k H) C.set := signConstOn_of_signCond hw
  intro i j hj x hx x' hx'
  by_cases hjd : j ≤ (H.get i).degreeOf (Fin.last k)
  · have hmem : (F (H.get i)).coeff j ∈ projDataT k H :=
      projData_subset_projDataT k H _ (coeffFam_mem_projData (List.get_mem H i) hjd)
    have h := hsc _ hmem x hx x' hx'
    rw [coeff_spec, coeff_spec]
    exact h
  · rw [coeff_spec_eq_zero_of_degreeOf_lt (H.get i) x (not_le.mp hjd),
        coeff_spec_eq_zero_of_degreeOf_lt (H.get i) x' (not_le.mp hjd)]

/-- The principal-subresultant data of the members of `H` have constant signs on a cell of the
decomposition of the projection data. -/
theorem pscSignConst_mem_CadCells {k : ℕ} (H : List (MvPolynomial (Fin (k + 1)) ℝ))
    (C : SAd k) (hC : C ∈ CadCells k (projDataT k H)) :
    PscSignConst (fun i : Fin H.length => H.get i) C.set := by
  obtain ⟨w, hw⟩ := exists_signCond_of_mem_CadCells k (projDataT k H) hC
  have hsc : SignConstOn (projDataT k H) C.set := signConstOn_of_signCond hw
  have hsc' : SignConstOn (projData H) C.set := fun Q hQ x hx x' hx' =>
    hsc Q (projData_subset_projDataT k H Q hQ) x hx x' hx'
  exact pscSignConst_of_signConstOn (fun i => List.get_mem H i) hsc'

/-- **Type constancy at every point.**  If `v` is realised at *some* point over the preconnected base
cell `C`, then it is realised over *every* point of `C`: `syl_minor_type_const` says that the set of
parameters realising `v` is either all of `C` or empty. -/
theorem realizedOn_all_of_mem_CadCells {k : ℕ} (H : List (MvPolynomial (Fin (k + 1)) ℝ))
    (C : SAd k) (hC : C ∈ CadCells k (projDataT k H)) (hpre : IsPreconnected C.set)
    (hclosed : ∀ i : Fin H.length, ∃ j : Fin H.length,
      H.get j = MvPolynomial.pderiv (Fin.last k) (H.get i))
    (v : Fin H.length → SignType) (hv : RealizedOn H C v) :
    ∀ x ∈ C.set, ∃ t : ℝ, ∀ i, SignType.sign (MvPolynomial.eval (Fin.snoc x t) (H.get i)) = v i := by
  rcases syl_minor_type_const (P := fun i => H.get i) (famDeg H)
      (fun i => (MvPolynomial.degreeOf_le_totalDegree _ _).trans
        (totalDegree_le_famDeg (List.get_mem H i)))
      hclosed C.set hpre (coeff_signConst_mem_CadCells H C hC) (pscSignConst_mem_CadCells H C hC) v
    with h | h
  · intro x hx
    obtain ⟨t, ht⟩ := h x hx
    exact ⟨t, fun i => by rw [← spec_eval_snoc]; exact ht i⟩
  · exfalso
    obtain ⟨x₁, hx₁, t₁, ht₁⟩ := hv
    exact h x₁ hx₁ ⟨t₁, fun i => by rw [spec_eval_snoc]; exact ht₁ i⟩

/-! ## The level recursion -/

/-- One level of the decomposition: if every cell of the decomposition of `projDataT k H` is
preconnected, then so is every cell of `CadCells (k+1) H`.  A cell of the latter is `cell C H v` over
a base cell `C`, and `cell_preconnected` applies: `C` is preconnected by hypothesis, the coefficient
signs of `H` are constant on `C` (they are signs of members of `projData H ⊆ projDataT k H`), and
`v` — which indexes the cell, so is realised somewhere over `C` — is realised at every point of `C`
by `realizedOn_all_of_mem_CadCells`. -/
theorem CadCells_preconnected_of_hpre {k : ℕ} (H : List (MvPolynomial (Fin (k + 1)) ℝ))
    (hclosed : ∀ i : Fin H.length, ∃ j : Fin H.length,
      H.get j = MvPolynomial.pderiv (Fin.last k) (H.get i))
    (hpre : ∀ C ∈ CadCells k (projDataT k H), IsPreconnected C.set) :
    ∀ C ∈ CadCells (k + 1) H, IsPreconnected C.set := by
  intro C hC
  rw [mem_CadCells_succ] at hC
  obtain ⟨C₀, hC₀, v, hv, rfl⟩ := hC
  refine cell_preconnected H C₀ v (hpre C₀ hC₀) ?_ ?_ ?_
  · intro i
    exact Or.inr (hclosed i)
  · intro i j hj x hx x' hx'
    exact coeff_signConst_mem_CadCells H C₀ hC₀ i j
      (hj.trans ((MvPolynomial.degreeOf_le_totalDegree _ _).trans
        (totalDegree_le_famDeg (List.get_mem H i)))) x hx x' hx'
  · exact realizedOn_all_of_mem_CadCells H C₀ hC₀ (hpre C₀ hC₀) hclosed v hv

/-- **Preconnectedness of the cells of the cylindrical decomposition.**

Every cell of `CadCells (n+1) H` is preconnected, provided the family `H` is closed under
differentiation in the last variable in the strong sense that the derivative of a member is again a
member (`hclosed`).  This is the `hpre` input of `Work.WilE4.CAD.baseCell_type_const`
(`Level.lean`), and through it the input of the degree recursion `CadCells_length_le`
(`Bounds.lean`).

Proof route (induction on the level, matching the recursion of `CadCells`).

* Base `n = 0`: `CadCells 1 H` consists of the cells `cell (topCell 0) H v` over the single base
  cell `ℝ^0`, and `cell_preconnected` (`cell_preconnected.lean`, proved) gives their
  preconnectedness: the base `ℝ^0` is preconnected, `H` is derivative-closed, the coefficient signs
  are constant on the one-point base, and `v` is realised everywhere because it is realised
  somewhere (the base is a single point).
* Step: a cell of `CadCells (n+2) H` is `cell C H v` over `C ∈ CadCells (n+1) (projDataT (n+1) H)`.
  The base cell `C` is preconnected by the induction hypothesis applied to the family
  `projDataT (n+1) H`, which is *strongly* derivative-closed by `Work.WilE4.CAD.projDataT_deriv_closed`
  (`Proj.lean`: `projDataT (m+1) H = tower (projData H) ++ [0]`, and `0` is its own derivative).
  Then `cell_preconnected` applies to `cell C H v`: the coefficient signs of `H` are constant on
  `C` because `C` is a sign condition of `projDataT (n+1) H ⊇ projData H ⊇ coeffFam H`, and `v` is
  realised at *every* point of `C` — that is the type constancy: `C` is preconnected, `v` is
  realised somewhere on it (it indexes a cell of the decomposition), and `syl_minor_type_const`
  (`syl_minor_type_const.lean`, with the polynomial-size `PscSignConst` hypothesis, which the sign
  condition of `C` supplies through `pscFam H ⊆ projData H`) says that a sign vector is realised
  either everywhere or nowhere on a preconnected set. -/
theorem CadCells_preconnected {n : ℕ} (H : List (MvPolynomial (Fin (n + 1)) ℝ))
    (hclosed : ∀ i : Fin H.length, ∃ j : Fin H.length,
      H.get j = MvPolynomial.pderiv (Fin.last n) (H.get i)) :
    ∀ C ∈ CadCells (n + 1) H, IsPreconnected C.set := by
  revert H hclosed
  induction n with
  | zero =>
    intro H hclosed C hC
    refine CadCells_preconnected_of_hpre H hclosed ?_ C hC
    intro C' hC'
    rw [mem_CadCells_zero] at hC'
    subst hC'
    rw [topCell_set]
    exact isPreconnected_univ
  | succ n ih =>
    intro H hclosed C hC
    refine CadCells_preconnected_of_hpre H hclosed ?_ C hC
    intro C' hC'
    exact ih (projDataT (n + 1) H) (projDataT_deriv_closed H) C' hC'

end Work.WilE4.CAD
