/-
  WilE4 / CAD — level glue: the transport from the frozen `SA` vocabulary, the non-emptiness and
  the sign conditions of the cells of the decomposition, and the *type constancy* of a base cell.

  The last item is the mathematical content of the CAD projection: over a base cell `C` of the
  decomposition of `projDataT k H`, the set of sign vectors of `H` realised somewhere over `C`
  is realised (all of it) at *one* point of `C`.  It follows from
  `realized_const_of_signConst_bdd` — the coefficient signs and the resultant signs are constant
  over a cell, because the cell is a sign condition of `projDataT k H ⊇ projData H` — together
  with the preconnectedness of the cell, which is the only hypothesis here.
-/
import Submission.Work.WilE4.CAD.Bridge
import Submission.Work.WilE4.CAD.CadCells_isUnionOf
import Submission.Work.WilE4.CAD.Size
import Submission.Work.WilE4.CAD.syl_minor_type_const

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical
namespace Work.WilE4

open MvPolynomial Polynomial
open WilkiesDesign WilkiesDesign.E
open Work.WilE4

/-! ## The transport from the frozen `SA` vocabulary -/

namespace SAd

variable {m : ℕ}

/-- Transport a frozen `SA m` to an `SAd m`. -/
def ofSA (X : SA m) : SAd m := ⟨X.basics.map Basic.toD⟩

theorem set_ofSA (X : SA m) : (ofSA X).set = X.set := by
  ext x
  simp only [ofSA, set, SA.set, List.mem_map]
  constructor
  · rintro ⟨B', ⟨B, hB, rfl⟩, h⟩
    exact ⟨B, hB, (Basic.holds_toD B x).mp h⟩
  · rintro ⟨B, hB, h⟩
    exact ⟨Basic.toD B, ⟨B, hB, rfl⟩, (Basic.holds_toD B x).mpr h⟩

theorem deg_ofSA (X : SA m) : (ofSA X).deg = X.deg := by
  rw [ofSA, deg, SA.deg, List.map_map]
  congr 1
  exact List.map_congr_left fun B _ => Basic.deg_toD B

end SAd

namespace CAD

open Work.WilE4 (tower)

/-! ## The cells are non-empty and carry a sign condition -/

/-- Every cell of the decomposition is non-empty: the level-`0` cell is `ℝ^0`, and a cell at level
`k+1` is kept only when its sign vector is realised over the base cell. -/
theorem CadCells_nonempty : ∀ (n : ℕ) (H : List (MvPolynomial (Fin n) ℝ)) (C : SAd n),
    C ∈ CadCells n H → C.set.Nonempty := by
  intro n
  induction n with
  | zero =>
    intro H C hC
    rw [mem_CadCells_zero] at hC
    subst hC
    rw [topCell_set]
    exact ⟨fun i => i.elim0, Set.mem_univ _⟩
  | succ k ih =>
    intro H C hC
    obtain ⟨C₀, hC₀, w, hw, rfl⟩ := (mem_CadCells_succ).mp hC
    exact (realizedOn_iff_nonempty H C₀ w).mp hw

/-- Every cell of `CadCells n G` is contained in the sign condition of `G` given by some sign
vector. -/
theorem exists_signCond_of_mem_CadCells : ∀ (n : ℕ) (G : List (MvPolynomial (Fin n) ℝ))
    {C : SAd n}, C ∈ CadCells n G → ∃ v : Fin G.length → SignType, C.set ⊆ signCond G v := by
  intro n
  match n with
  | 0 =>
    intro G C hC
    rw [mem_CadCells_zero] at hC
    subst hC
    refine ⟨signVec G (fun i => i.elim0), ?_⟩
    rw [topCell_set]
    intro z _
    have hz : z = fun i => i.elim0 := Subsingleton.elim _ _
    rw [hz]
    exact signVec_mem_signCond G _
  | k + 1 =>
    intro G C hC
    obtain ⟨C₀, hC₀, w, hw, rfl⟩ := (mem_CadCells_succ).mp hC
    exact ⟨w, fun z hz i => ((mem_cell_iff G C₀ w z).mp hz).2 i⟩

/-- `projData H` is part of the family used one level down. -/
theorem projData_subset_projDataT (k : ℕ) (H : List (MvPolynomial (Fin (k + 1)) ℝ)) :
    ∀ P ∈ projData H, P ∈ projDataT k H := by
  match k with
  | 0 => exact fun P hP => hP
  | _ + 1 =>
    intro P hP
    show P ∈ tower (projData H) ++ [0]
    exact List.mem_append_left _ (by
      rw [tower, List.mem_flatMap]
      exact ⟨P, hP, List.mem_map.mpr ⟨0, List.mem_range.mpr (Nat.succ_pos _), by simp⟩⟩)

/-! ## Type constancy over a base cell -/

/-- **Type constancy.**  Let `C` be a cell of the decomposition of `projDataT k H`, with `H` closed
under differentiation in the last variable.  If `C` is preconnected, then there is a single point
`x ∈ C` at which *every* sign vector of `H` that is realised anywhere over `C` is realised.

The proof uses the two sources of information that the cell provides: the signs of the coefficients
of the specialisations (which fix the degrees) and the signs of the principal subresultant
coefficients (which fix the degree of the gcd of every pair), both because `C` is a sign condition
of `projDataT k H ⊇ projData H` and both parts of `projData` carry them.  The conclusion is the
"all or nothing" alternative `syl_minor_type_const` for the realisation of a sign vector over the
preconnected set `C`. -/
theorem baseCell_type_const {k : ℕ} (H : List (MvPolynomial (Fin (k + 1)) ℝ))
    (hclosed : ∀ i : Fin H.length,
      ∃ j : Fin H.length, H.get j = MvPolynomial.pderiv (Fin.last k) (H.get i))
    (hpre : ∀ C ∈ CadCells k (projDataT k H), IsPreconnected C.set)
    (C : SAd k) (hC : C ∈ CadCells k (projDataT k H)) :
    ∃ x ∈ C.set, ∀ w : Fin H.length → SignType, RealizedOn H C w →
      ∃ t : ℝ, ∀ i, SignType.sign ((spec (H.get i) x).eval t) = w i := by
  obtain ⟨v, hv⟩ := exists_signCond_of_mem_CadCells k (projDataT k H) hC
  have hsc : SignConstOn (projDataT k H) C.set := signConstOn_of_signCond hv
  obtain ⟨x₀, hx₀⟩ := CadCells_nonempty k (projDataT k H) C hC
  have hcoeff : ∀ i : Fin H.length, ∀ j : ℕ, j ≤ famDeg H → ∀ x ∈ C.set, ∀ x' ∈ C.set,
      SignType.sign ((spec (H.get i) x).coeff j)
        = SignType.sign ((spec (H.get i) x').coeff j) := by
    intro i j hj x hx x' hx'
    by_cases hjd : j ≤ (H.get i).degreeOf (Fin.last k)
    · have hmem : (CAD.F (H.get i)).coeff j ∈ projDataT k H :=
        projData_subset_projDataT k H _ (coeffFam_mem_projData (List.get_mem H i) hjd)
      have h := hsc _ hmem x hx x' hx'
      rw [coeff_spec, coeff_spec]
      exact h
    · rw [coeff_spec_eq_zero_of_degreeOf_lt (H.get i) x (not_le.mp hjd),
        coeff_spec_eq_zero_of_degreeOf_lt (H.get i) x' (not_le.mp hjd)]
  have hpsc : PscSignConst (fun i : Fin H.length => H.get i) C.set := by
    intro i j a b ha hb r hr x hx x' hx'
    have hmem : (pscMat (CAD.F (H.get i)) (CAD.F (H.get j)) a b r).det ∈ projDataT k H :=
      projData_subset_projDataT k H _
        (pscFam_mem_projData (List.get_mem H i) (List.get_mem H j) ha hb hr)
    have h := hsc _ hmem x hx x' hx'
    rwa [eval_pscMat_det, eval_pscMat_det] at h
  refine ⟨x₀, hx₀, fun w hw => ?_⟩
  rcases syl_minor_type_const (P := fun i => H.get i) (famDeg H)
      (fun i => (MvPolynomial.degreeOf_le_totalDegree _ _).trans
        (totalDegree_le_famDeg (List.get_mem H i)))
      hclosed C.set (hpre C hC) hcoeff hpsc w with h | h
  · obtain ⟨t, ht⟩ := h x₀ hx₀
    exact ⟨t, fun i => ht i⟩
  · obtain ⟨x₁, hx₁, t₁, ht₁⟩ := hw
    exact absurd ⟨t₁, fun i => by rw [spec_eval_snoc]; exact ht₁ i⟩ (h x₁ hx₁)

end CAD

end Work.WilE4
