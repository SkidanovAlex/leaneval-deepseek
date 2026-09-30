import Mathlib
import Submission.Work.Pi6.SQM.RedDefs
import Submission.Work.Cohomology.cupH
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# A mod-2 cocycle of vanishing class is a coboundary

The `𝔽₂` instance of `Work.Gen.cochain_homologypi_eq_zero` (which is stated for `ℤ`): for the
singular cochain complex of a simplicial set with coefficients in `ZMod 2`, a cocycle `y` of
degree `n+1` whose cohomology class vanishes is the coboundary of a degree `n` cochain.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Pi6.SQM

noncomputable section

open Work.Cohomology (Cochain genEval cochainDiff cohomologyClassOf cocycleOf
  SSetCochainComplex cochainDiffLM)

/-- **A cocycle of a cochain complex of `R`-modules whose class vanishes is a coboundary.** -/
theorem cochain_homologypi_eq_zero_of_class_eq_zero (R : Type) [CommRing R]
    (K : CochainComplex (ModuleCat R) ℕ) [∀ i, K.HasHomology i]
    (n : ℕ) (z : K.cycles (n + 1)) (h : K.homologyπ (n + 1) z = 0) :
    ∃ y : K.X n, (K.d n (n + 1)).hom y = (K.iCycles (n + 1)).hom z := by
  have hprev : (ComplexShape.up ℕ).prev (n + 1) = n := by
    rw [ComplexShape.prev_eq']
    rfl
  let z' : (K.sc (n + 1)).cycles := z
  have hkey : ∃ w : (K.sc (n + 1)).X₁,
      (K.sc (n + 1)).f.hom w = (K.sc (n + 1)).iCycles.hom z' := by
    have hzero : (K.sc (n + 1)).homologyι ((K.sc (n + 1)).homologyπ z') = 0 := by
      rw [show (K.sc (n + 1)).homologyπ z' = 0 from h, map_zero]
    have hpop : (K.sc (n + 1)).pOpcycles ((K.sc (n + 1)).iCycles.hom z') = 0 := by
      have hh := congrArg (fun (g : (K.sc (n + 1)).cycles ⟶ (K.sc (n + 1)).opcycles) => g z')
        (ShortComplex.homology_π_ι (K.sc (n + 1)))
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hh
      rw [← hh]
      exact hzero
    have hmem := (ShortComplex.moduleCat_pOpcycles_eq_zero_iff (K.sc (n + 1))
      ((K.sc (n + 1)).iCycles.hom z')).mp hpop
    obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hmem
    exact ⟨w, hw⟩
  obtain ⟨w, hw⟩ := hkey
  refine ⟨(K.XIsoOfEq hprev).hom w, ?_⟩
  have hh : (K.d n (n + 1)).hom ((K.XIsoOfEq hprev).hom w) =
      (K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1)).hom w := by
    have h1 : (K.XIsoOfEq hprev).hom ≫ K.d n (n + 1) =
        K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1) :=
      HomologicalComplex.XIsoOfEq_hom_comp_d K hprev (n + 1)
    calc (K.d n (n + 1)).hom ((K.XIsoOfEq hprev).hom w)
        = ((K.XIsoOfEq hprev).hom ≫ K.d n (n + 1)).hom w := by
          rw [ModuleCat.hom_comp]
          rfl
      _ = (K.d ((ComplexShape.up ℕ).prev (n + 1)) (n + 1)).hom w := by rw [h1]
  rw [hh]
  exact hw

/-- **A mod-2 cocycle whose cohomology class vanishes is a coboundary.** -/
theorem exists_cochainDiff_eq_of_class_eq_zero {X : SSet} {n : ℕ}
    (y : Cochain (ZMod 2) X (n + 1)) (hy : cochainDiff (ZMod 2) X y = 0)
    (h : cohomologyClassOf (ZMod 2) X y hy = 0) :
    ∃ w : Cochain (ZMod 2) X n, cochainDiff (ZMod 2) X w = y := by
  obtain ⟨w, hw⟩ := cochain_homologypi_eq_zero_of_class_eq_zero (ZMod 2)
    (SSetCochainComplex (ZMod 2) X) n (cocycleOf (ZMod 2) X y hy) h
  refine ⟨w, ?_⟩
  rw [← Work.Cohomology.iCycles_cocycleOf (ZMod 2) X y hy, ← hw, Work.Cohomology.SSetCochainComplex_d]
  rfl

end

end Work.Pi6.SQM
