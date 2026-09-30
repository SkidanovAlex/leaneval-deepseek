import Mathlib
import Submission.Work.Pi6.MSS.E1B.Dual
import Submission.Work.StemsB.FieldDualUCT
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The canonical isomorphism `H_n ≅ Z_n/B_n`, evaluated on the class of a cycle

`Work.Pi6.MSS.E1B.homIsoH 𝕜 E n` is the canonical isomorphism from the `n`-th homology of a chain
complex of `𝕜`-vector spaces to the explicit "cycles modulo boundaries" model
`Z_n(E) ⧸ B_n(E)` (`homologyIsoSc'` followed by the module-category left homology data).

Here we record the computation rule on representatives: the homology class of a cycle `z` is sent
to the class of `z` in `Z_n(E) ⧸ B_n(E)`.  The proof puts the cycle through the concrete
identification `cycIsoZ` of the abstract cycles `E.cycles n` with `↥(fdZ 𝕜 E n)`, which does not
change the underlying element of the complex.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace Work.Pi6.MSS.E1B

noncomputable section

variable {𝕜 : Type} [Field 𝕜] {E : ChainComplex (ModuleCat 𝕜) ℕ}

/-- The `n`-cycles of `E`, identified with the concrete submodule `Z_n = ker d_n`. -/
private noncomputable def cycIsoZ (𝕜 : Type) [Field 𝕜] (E : ChainComplex (ModuleCat 𝕜) ℕ) (n : ℕ) :
    E.cycles n ≅ ModuleCat.of 𝕜 ↥(Work.StemsB.fdZ 𝕜 E n) :=
  (E.cyclesIsoSc' (n+1) n (n-1) (Work.Cohomology.down_prev n) (Work.Cohomology.down_next n)) ≪≫
    ShortComplex.moduleCatCyclesIso (E.sc' (n+1) n (n-1))

/-- `cycIsoZ` is compatible with the inclusions of the cycles. -/
private lemma cycIsoZ_hom_i (n : ℕ) :
    (cycIsoZ 𝕜 E n).hom ≫
        (ShortComplex.moduleCatLeftHomologyData (E.sc' (n+1) n (n-1))).i = E.iCycles n := by
  rw [cycIsoZ, Iso.trans_hom, Category.assoc, ShortComplex.moduleCatCyclesIso_hom_i,
    HomologicalComplex.cyclesIsoSc'_hom_iCycles]

/-- `cycIsoZ` does not change the underlying element of the complex. -/
private lemma cycIsoZ_hom_val (n : ℕ) (c : ↥(E.cycles n)) :
    ((cycIsoZ 𝕜 E n).hom c : ↥(E.X n)) = (E.iCycles n).hom c := by
  have h := congrArg (fun (m : E.cycles n ⟶ E.X n) => ModuleCat.Hom.hom m c)
    (cycIsoZ_hom_i (𝕜 := 𝕜) (E := E) n)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- The projection of the left homology data of `E.sc' (n+1) n (n-1)` is the quotient map onto
`Z_n ⧸ B_n`. -/
private lemma LHD_pi_eq (n : ℕ) :
    (ShortComplex.moduleCatLeftHomologyData (E.sc' (n+1) n (n-1))).π
      = ModuleCat.ofHom ((Work.StemsB.fdH 𝕜 E n).mkQ) := by
  rw [ModuleCat.hom_ext_iff, ShortComplex.moduleCatLeftHomologyData_π_hom]
  rfl

/-- `homIsoH` is the composite of the identification of the abstract cycles with `Z_n` and the
quotient map onto `Z_n ⧸ B_n`. -/
private lemma homIsoH_comp (n : ℕ) :
    (E.homologyπ n) ≫ (homIsoH 𝕜 E n).hom
      = (cycIsoZ 𝕜 E n).hom ≫ ModuleCat.ofHom ((Work.StemsB.fdH 𝕜 E n).mkQ) := by
  simp only [homIsoH, Iso.trans_hom, Category.assoc, cycIsoZ,
    HomologicalComplex.π_homologyIsoSc'_hom_assoc, ShortComplex.π_moduleCatCyclesIso_hom]
  rw [LHD_pi_eq (𝕜 := 𝕜) (E := E) n]

/-- The computation rule for `homIsoH` on a class of cycles. -/
private lemma homIsoH_apply (n : ℕ) (c : ↥(E.cycles n)) :
    (homIsoH 𝕜 E n).hom.hom ((E.homologyπ n).hom c)
      = (Work.StemsB.fdH 𝕜 E n).mkQ ((cycIsoZ 𝕜 E n).hom c) := by
  have h := congrArg (fun (m : E.cycles n ⟶
      ModuleCat.of 𝕜 (↥(Work.StemsB.fdZ 𝕜 E n) ⧸ Work.StemsB.fdH 𝕜 E n)) =>
      ModuleCat.Hom.hom m c) (homIsoH_comp (𝕜 := 𝕜) (E := E) n)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom] using h

theorem homIsoH_hom_cyclesMk {𝕜 : Type} [Field 𝕜] {E : ChainComplex (ModuleCat 𝕜) ℕ} (n : ℕ)
    (z : ↥(E.X n)) (hz : (ModuleCat.Hom.hom (E.d n (n-1))) z = 0) :
    ModuleCat.Hom.hom (Work.Pi6.MSS.E1B.homIsoH 𝕜 E n).hom
        (HomologicalComplex.homologyπ E n
          (HomologicalComplex.cyclesMk E z ((ComplexShape.down ℕ).next n) rfl
            (by rw [Work.Cohomology.down_next]; exact hz)))
      = (Work.StemsB.fdH 𝕜 E n).mkQ (⟨z, hz⟩ : ↥(Work.StemsB.fdZ 𝕜 E n)) := by
  set c : ↥(E.cycles n) := cyclesMk E z ((ComplexShape.down ℕ).next n) rfl
      (by rw [Work.Cohomology.down_next]; exact hz) with hc
  rw [homIsoH_apply (𝕜 := 𝕜) (E := E) n c]
  have hcyc : (cycIsoZ 𝕜 E n).hom c = (⟨z, hz⟩ : ↥(Work.StemsB.fdZ 𝕜 E n)) := by
    apply Subtype.ext
    rw [cycIsoZ_hom_val]
    have h := HomologicalComplex.i_cyclesMk E z ((ComplexShape.down ℕ).next n) rfl
      (by rw [Work.Cohomology.down_next]; exact hz)
    simpa [hc] using h
  rw [hcyc]

end

end Work.Pi6.MSS.E1B
