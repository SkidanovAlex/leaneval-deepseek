import Mathlib
import Submission.Work.Stems.WedgePinch
import Submission.Work.Cohomology.sphere_compl_singleton_contractible
import Submission.Work.Cohomology.MVSequence
import Submission.Work.Cohomology.homologyContractible
import Submission.Work.Cohomology.Pullback

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The homology of the wedge `Sⁿ ∨ Sⁿ`

We prove that the two folds `wedgeFst`, `wedgeSnd : Sⁿ ∨ Sⁿ → Sⁿ` separate the two summands of
`Hₙ(Sⁿ ∨ Sⁿ)`: the map `(wedgeFst₊, wedgeSnd₊)` is injective.

The wedge is the "cross" `(Sⁿ × {b}) ∪ ({b} × Sⁿ)` in `Sⁿ × Sⁿ`.  The proof uses Mayer–Vietoris
for the open cover by the two thickened summands
`U = {x | x₂ ≠ q}`, `V = {x | x₁ ≠ q}` for some point `q ≠ b` of `Sⁿ`; their intersection is the
cross of the two punctured spheres `Sⁿ ∖ {q}`, which is contractible (the punctured sphere being
homeomorphic to a real vector space).

* `sphOther` — a point of `Sⁿ` different from the base point;
* `punctSph` — the punctured sphere `Sⁿ ∖ {sphOther}`, contractible;
* `punctHomeo`, `punctContraction` — the stereographic homeomorphism to a vector space and the
  resulting contraction of the punctured sphere to the base point;
* `wedgeFstSnd_injective` — the injectivity of the pair of folds on `Hₙ`.
-/

open CategoryTheory AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Stems

noncomputable section

variable {n : ℕ}

/-! ## A second point of `Sⁿ` and the punctured sphere -/

/-- The midpoint of the unit interval. -/
def halfI : I := ⟨(1 : ℝ) / 2, by norm_num⟩

@[simp] theorem coe_halfI : ((halfI : I) : ℝ) = 1 / 2 := rfl

/-- The image under the collapse of the centre of the cube: a point of `Sⁿ` different from the
base point `sphBase`. -/
def sphOther (n : ℕ) (hn : 1 ≤ n) : sphere n :=
  collapseMap n hn (fun _ : Fin n => halfI)

theorem sphOther_ne_sphBase (n : ℕ) (hn : 1 ≤ n) : sphOther n hn ≠ sphBase n hn := by
  intro h
  have h' : collapseMap n hn (fun _ : Fin n => halfI) = collapseMap n hn (0 : CubeI n) := h
  have ht : (fun _ : Fin n => halfI) ≠ (0 : CubeI n) := by
    intro hh
    have h1 : (halfI : ℝ) = 0 := by
      have := congrFun hh ⟨0, hn⟩
      simpa using congrArg (fun x : I => (x : ℝ)) this
    rw [coe_halfI] at h1; norm_num at h1
  have hbd : (fun _ : Fin n => halfI) ∉ Cube.boundary (Fin n) := by
    rintro ⟨j, hj | hj⟩
    · have h1 : (halfI : ℝ) = 0 := by
        simpa using congrArg (fun x : I => (x : ℝ)) hj
      rw [coe_halfI] at h1; norm_num at h1
    · have h1 : (halfI : ℝ) = 1 := by
        simpa using congrArg (fun x : I => (x : ℝ)) hj
      rw [coe_halfI] at h1; norm_num at h1
  rcases collapseMap_fiber n hn h' with hh | ⟨h1, -⟩
  · exact ht hh
  · exact hbd h1

/-- The sphere `Sⁿ` with a point (different from the base point) removed. -/
abbrev punctSph (n : ℕ) (hn : 1 ≤ n) : Type := {y : sphere n // y ≠ sphOther n hn}

/-- The base point as a point of the punctured sphere. -/
def punctBase (n : ℕ) (hn : 1 ≤ n) : punctSph n hn :=
  ⟨sphBase n hn, (sphOther_ne_sphBase n hn).symm⟩

instance instContractible_punctSph (n : ℕ) (hn : 1 ≤ n) : ContractibleSpace (punctSph n hn) :=
  Work.Cohomology.sphere_compl_singleton_contractible (EuclideanSpace ℝ (Fin (n + 1)))
    (sphOther n hn)

/-- **Stereographic projection** realises the punctured sphere as a real vector space. -/
def punctHomeo (n : ℕ) (hn : 1 ≤ n) :
    punctSph n hn ≃ₜ (ℝ ∙ (sphOther n hn : EuclideanSpace ℝ (Fin (n + 1))))ᗮ :=
  let e₀ := stereographic (v := (sphOther n hn : EuclideanSpace ℝ (Fin (n + 1))))
    (norm_eq_of_mem_sphere (sphOther n hn))
  have hsrc : e₀.source = {y : sphere n | y ≠ sphOther n hn} := by
    rw [stereographic_source]
    ext y
    simp
  have htrg : e₀.target = Set.univ := stereographic_target _
  (((Homeomorph.setCongr hsrc).symm.trans
        (OpenPartialHomeomorph.toHomeomorphSourceTarget e₀)).trans
      (Homeomorph.setCongr htrg)).trans (Homeomorph.Set.univ _)

/-- The contraction of the punctured sphere to the base point, transported from the vector space
structure through the stereographic homeomorphism. -/
def punctContraction (n : ℕ) (hn : 1 ≤ n) : C(I × punctSph n hn, punctSph n hn) :=
  ⟨fun tx => (punctHomeo n hn).symm
      ((1 - (tx.1 : ℝ)) • (punctHomeo n hn) tx.2 + (tx.1 : ℝ) • (punctHomeo n hn) (punctBase n hn)),
    by fun_prop⟩

@[simp] theorem punctContraction_apply_zero (n : ℕ) (hn : 1 ≤ n) (x : punctSph n hn) :
    punctContraction n hn (0, x) = x := by
  show (punctHomeo n hn).symm
      ((1 - (((0 : I)) : ℝ)) • (punctHomeo n hn) x + (((0 : I)) : ℝ) • (punctHomeo n hn) (punctBase n hn)) = x
  simp

@[simp] theorem punctContraction_apply_one (n : ℕ) (hn : 1 ≤ n) (x : punctSph n hn) :
    punctContraction n hn (1, x) = punctBase n hn := by
  show (punctHomeo n hn).symm
      ((1 - (((1 : I)) : ℝ)) • (punctHomeo n hn) x + (((1 : I)) : ℝ) • (punctHomeo n hn) (punctBase n hn))
    = punctBase n hn
  simp

@[simp] theorem punctContraction_apply_base (n : ℕ) (hn : 1 ≤ n) (t : I) :
    punctContraction n hn (t, punctBase n hn) = punctBase n hn := by
  show (punctHomeo n hn).symm
      ((1 - (t : ℝ)) • (punctHomeo n hn) (punctBase n hn) + (t : ℝ) • (punctHomeo n hn) (punctBase n hn))
    = punctBase n hn
  rw [← add_smul, show (1 - (t : ℝ)) + (t : ℝ) = 1 by ring, one_smul]
  exact (punctHomeo n hn).symm_apply_apply (punctBase n hn)

end

end Work.Stems
