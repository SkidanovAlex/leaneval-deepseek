import Mathlib
import ChallengeDeps
import Submission.Commons.LinearAlgebra.ExteriorPower.norm_iMulti_eq_of_span_eq

/-!
# Heights of rational subspaces (dictionary: H(v) = norm of an integer wedge)

`LinearSubspaces.height V hV` is defined through the basis `chosenBasis V hV` of `V` obtained
from a ℤ-basis of the lattice `intPointsSubspace V = V ∩ ℤᵈ` (`Module.Free.chooseBasis` +
`Basis.ofZLatticeBasis`).  This file shows:

1. the chosenBasis family is itself a ℤ-basis of the image lattice
   `map (V.subtype.restrictScalars ℤ) (intPointsSubspace V)` in ℝᵈ
   (`chosenBasis_span_lattice`, `chosenBasis_linearIndependent`);
2. **height invariance**: for any ℤ-basis `u : Fin (finrank ℝ V) → ℝᵈ` of the image lattice,
   `height V hV = ‖ιMulti u‖` (`height_eq_norm_iMulti_of_zbasis`; via the commons
   `norm_iMulti_eq_of_span_eq`).
-/

noncomputable section

open Module exteriorPower InnerProductGeometry
open scoped BigOperators
set_option autoImplicit false
set_option linter.unusedSectionVars false

open LinearSubspaces

namespace Submission.Heights

variable {d : ℕ}
local notation "ℝᵈ" => EuclideanSpace ℝ (Fin d)
local notation "ℤᵈ" => intPoints

/-- The image of the lattice of integer points of `V` in ℝᵈ (the "integer lattice of V"). -/
def imageLattice (V : Submodule ℝ ℝᵈ) : Submodule ℤ ℝᵈ :=
  Submodule.map (V.subtype.restrictScalars ℤ) (intPointsSubspace V)

/-- The chosenBasis family (indexed by `Fin (finrank ℝ V)`), as vectors of ℝᵈ. -/
def cbFamily (V : Submodule ℝ ℝᵈ) (hV : IsRational V) : Fin (Module.finrank ℝ V) → ℝᵈ :=
  fun i => V.subtype (chosenBasis V hV i)

/-- `chosenBasis V hV` is built from a ℤ-basis of the lattice `intPointsSubspace V` through
`Basis.ofZLatticeBasis`; the underlying family (in ℝᵈ) is the image of that ℤ-basis under the
inclusion `g : intPointsSubspace V →ₗ[ℤ] ℝᵈ`. -/
lemma chosenBasis_eq_ofZLatticeBasis (V : Submodule ℝ ℝᵈ) (hV : IsRational V) :
    ∃ (b : Basis (Fin (Module.finrank ℝ V)) ℤ (intPointsSubspace V)),
      chosenBasis V hV = Basis.ofZLatticeBasis ℝ (intPointsSubspace V) b := by
  classical
  change ∃ b : Basis (Fin (Module.finrank ℝ V)) ℤ (intPointsSubspace V),
    Basis.ofZLatticeBasis ℝ (intPointsSubspace V)
      ((Module.Free.chooseBasis ℤ (intPointsSubspace V)).reindex
        (Fintype.equivFinOfCardEq (by
          rw [← Module.finrank_eq_card_chooseBasisIndex, ZLattice.rank ℝ]))) =
      Basis.ofZLatticeBasis ℝ (intPointsSubspace V) b
  exact ⟨_, rfl⟩

/-- The chosenBasis family ℤ-spans the image lattice (it is a ℤ-basis of `V ∩ ℤᵈ`). -/
lemma chosenBasis_span_lattice (V : Submodule ℝ ℝᵈ) (hV : IsRational V) :
    Submodule.span ℤ (Set.range (cbFamily V hV)) = imageLattice V := by
  classical
  let L : Submodule ℤ V := intPointsSubspace V
  let m : ℕ := Module.finrank ℝ V
  rcases chosenBasis_eq_ofZLatticeBasis V hV with ⟨b, hcb⟩
  let g : L →ₗ[ℤ] ℝᵈ := (V.subtype.restrictScalars ℤ).comp L.subtype
  have hcbi : ∀ i : Fin m, chosenBasis V hV i = (b i : V) := by
    intro i
    calc
      chosenBasis V hV i = (Basis.ofZLatticeBasis ℝ (intPointsSubspace V) b) i := by
            exact congrArg (fun bb : Basis (Fin m) ℝ V => bb i) hcb
      _ = (b i : V) := by
            rw [Basis.ofZLatticeBasis_apply]
  have hfam : Set.range (cbFamily V hV) = g '' (Set.range (fun i : Fin m => (b i : L))) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨b i, ⟨i, rfl⟩, ?_⟩
      dsimp [cbFamily, g]
      rw [hcbi i]
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      dsimp [cbFamily, g]
      rw [hcbi i]
  calc
    Submodule.span ℤ (Set.range (cbFamily V hV))
        = Submodule.span ℤ (g '' (Set.range (fun i : Fin m => (b i : L)))) := by rw [hfam]
    _ = (Submodule.span ℤ (Set.range (fun i : Fin m => (b i : L)))).map g := by
          rw [Submodule.map_span]
    _ = (⊤ : Submodule ℤ L).map g := by
          rw [Basis.span_eq b]
    _ = Submodule.map (V.subtype.restrictScalars ℤ)
          ((⊤ : Submodule ℤ L).map L.subtype) := by
          dsimp [g]
          rw [Submodule.map_comp]
    _ = Submodule.map (V.subtype.restrictScalars ℤ) (intPointsSubspace V) := by
          rw [Submodule.map_top, Submodule.range_subtype]
    _ = imageLattice V := rfl


/-- The chosenBasis family is linearly independent over ℤ. -/
lemma chosenBasis_linearIndependent (V : Submodule ℝ ℝᵈ) (hV : IsRational V) :
    LinearIndependent ℤ (cbFamily V hV) := by
  classical
  let L : Submodule ℤ V := intPointsSubspace V
  let m : ℕ := Module.finrank ℝ V
  rcases chosenBasis_eq_ofZLatticeBasis V hV with ⟨b, hcb⟩
  let g : L →ₗ[ℤ] ℝᵈ := (V.subtype.restrictScalars ℤ).comp L.subtype
  have hcbi : ∀ i : Fin m, chosenBasis V hV i = (b i : V) := by
    intro i
    calc
      chosenBasis V hV i = (Basis.ofZLatticeBasis ℝ (intPointsSubspace V) b) i := by
            exact congrArg (fun bb : Basis (Fin m) ℝ V => bb i) hcb
      _ = (b i : V) := by
            rw [Basis.ofZLatticeBasis_apply]
  have hfam_f : cbFamily V hV = (fun i : Fin m => g (b i)) := by
    funext i
    dsimp [cbFamily, g]
    rw [hcbi i]
  -- g is injective (composite of injective submodule inclusions)
  have hLs : Function.Injective L.subtype := L.injective_subtype
  have hVs : Function.Injective (V.subtype.restrictScalars ℤ) := by
    exact V.injective_subtype
  have hginj : Function.Injective g := by
    dsimp [g]
    exact hVs.comp hLs
  have hker : LinearMap.ker g = ⊥ := LinearMap.ker_eq_bot.mpr hginj
  have hbLI : LinearIndependent ℤ (fun i : Fin m => (b i : L)) := b.linearIndependent
  have hLI : LinearIndependent ℤ (fun i : Fin m => g (b i)) := by
    exact LinearIndependent.map hbLI (f := g) (by simp [hker])
  simpa [hfam_f] using hLI


/-- **Height invariance**: for a rational subspace `V` and a ℤ-basis `u` of its image
lattice `V ∩ ℤᵈ` (i.e. `u` is ℤ-linearly independent and ℤ-spans the lattice of integer
points of `V`), the height of `V` equals the norm of the integer wedge `ιMulti u`. -/
theorem height_eq_norm_iMulti_of_zbasis (V : Submodule ℝ ℝᵈ) (hV : IsRational V)
    (u : Fin (Module.finrank ℝ V) → ℝᵈ)
    (hu_li : LinearIndependent ℤ u)
    (hu_span : Submodule.span ℤ (Set.range u) = imageLattice V) :
    LinearSubspaces.height V hV = ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ V) u‖ := by
  classical
  have hspan_eq : Submodule.span ℤ (Set.range u) =
      Submodule.span ℤ (Set.range (cbFamily V hV)) := by
    rw [hu_span]
    exact (chosenBasis_span_lattice V hV).symm
  have hnorm : ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ V) (cbFamily V hV)‖ =
      ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ V) u‖ := by
    exact Commons.LinearAlgebra.ExteriorPower.norm_iMulti_eq_of_span_eq (E := ℝᵈ)
      (k := Module.finrank ℝ V) u (cbFamily V hV) hu_li (chosenBasis_linearIndependent V hV) hspan_eq
  calc
    LinearSubspaces.height V hV
        = ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ V) (cbFamily V hV)‖ := by
            change ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ V) (V.subtype ∘ chosenBasis V hV)‖ =
              ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ V) (cbFamily V hV)‖
            rfl
    _ = ‖exteriorPower.ιMulti ℝ (Module.finrank ℝ V) u‖ := hnorm

end Submission.Heights
