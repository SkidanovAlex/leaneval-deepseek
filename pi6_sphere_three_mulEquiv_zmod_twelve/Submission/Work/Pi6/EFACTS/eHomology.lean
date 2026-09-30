import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.EFACTS.Basic
import Submission.Work.Pi6.EFACTS.eDefs
import Submission.Work.Pi6.EFACTS.eCohCore
import Submission.Work.Pi6.EFACTS.ratAcyclic
import Submission.Work.Pi6.EFACTS.h3zero
import Submission.Work.Pi6.EFACTS.uctTorsion
import Submission.Work.Pi6.EFACTS.qzDual
import Submission.Work.RatHurewicz.torsion_of_subsingleton_ratHomology
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The homology of the cover `E = S³⟨3⟩` in degrees 4 to 7

`H_4(S³⟨3⟩) ≅ ℤ/2`, `H_5(S³⟨3⟩) = 0`, `H_6(S³⟨3⟩) ≅ ℤ/3`, `H_7(S³⟨3⟩) = 0`.

The cohomology in degrees 5 to 8 is computed in `eCohCore` (Wang sequence of the cover together
with the `K(ℤ,2)`-structure of the fibre).  The integral universal coefficient theorem in its
torsion form (`uctTorsion`: `H^n(X;ℤ) ≅ Hom(H_{n-1}(X;ℤ), ℚ/ℤ)` for torsion `H_{n-1}`, `H_n`) and
the elementary duality `qzDual` of `ℚ/ℤ` convert this into the homology statement; the torsion
hypothesis is the change-of-coefficients consequence of the rational acyclicity of `E`
(`ratAcyclic`).
-/

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Pi6.EFACTS

theorem eHomology {P3 : Type} [TopologicalSpace P3] (g3 : C(Work.Pi6.S3, P3)) (hP3 : Work.Pi6.PostnikovData 3 12 g3 Work.Pi6.s3) (hfib : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) 11 (Work.Pi6.EFACTS.fib g3) (Work.Pi6.EFACTS.fibPt g3)) (hZ : Work.Pi6.K2ZFacts) : Nonempty (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 4 ≃ₗ[ℤ] ZMod 2) ∧ Subsingleton (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 5) ∧ Nonempty (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 6 ≃ₗ[ℤ] ZMod 3) ∧ Subsingleton (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 7) := by
  obtain ⟨h5, h6, h7, h8⟩ := eCohCore g3 hP3 hfib hZ
  -- the integral homology of `E` is torsion in degrees `1 … 8`
  have htors : ∀ n : ℕ, 1 ≤ n → n ≤ 8 → ∀ x : Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) n,
      ∃ N : ℕ, 0 < N ∧ N • x = 0 :=
    fun n hn1 hn8 x =>
      Work.RatHurewicz.torsion_of_subsingleton_ratHomology (X := Work.Pi6.Ecov g3) n
        (ratAcyclic g3 hP3 n hn1 hn8) x
  -- the (degree-local) integral universal coefficient theorem
  have hfree : ∀ k : ℕ,
      Module.Free ℤ ↥((Work.Cohomology.singularChains ℤ
        (TopCat.of (Work.Pi6.Ecov g3))).X k) :=
    fun k => Work.Cohomology.singularChains_free (TopCat.of (Work.Pi6.Ecov g3)) k
  obtain ⟨u5⟩ := uctTorsion (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Pi6.Ecov g3)))
    hfree 5 (by norm_num) (htors 5 (by norm_num) (by norm_num))
    (htors 4 (by norm_num) (by norm_num))
  obtain ⟨u6⟩ := uctTorsion (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Pi6.Ecov g3)))
    hfree 6 (by norm_num) (htors 6 (by norm_num) (by norm_num))
    (htors 5 (by norm_num) (by norm_num))
  obtain ⟨u7⟩ := uctTorsion (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Pi6.Ecov g3)))
    hfree 7 (by norm_num) (htors 7 (by norm_num) (by norm_num))
    (htors 6 (by norm_num) (by norm_num))
  obtain ⟨u8⟩ := uctTorsion (Work.Cohomology.singularChains ℤ (TopCat.of (Work.Pi6.Ecov g3)))
    hfree 8 (by norm_num) (htors 8 (by norm_num) (by norm_num))
    (htors 7 (by norm_num) (by norm_num))
  -- the algebra of `ℚ/ℤ`
  obtain ⟨-, -, -, -, hAux, hsub⟩ := qzDual
  -- the two `ℤ`-module structures on the homology agree; normalise to the canonical one
  have hmod4 : (inferInstance : Module ℤ ↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 4))
      = AddCommGroup.toIntModule ↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 4) := Subsingleton.elim _ _
  have hmod5 : (inferInstance : Module ℤ ↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 5))
      = AddCommGroup.toIntModule ↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 5) := Subsingleton.elim _ _
  have hmod6 : (inferInstance : Module ℤ ↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 6))
      = AddCommGroup.toIntModule ↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 6) := Subsingleton.elim _ _
  have hmod7 : (inferInstance : Module ℤ ↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 7))
      = AddCommGroup.toIntModule ↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 7) := Subsingleton.elim _ _
  -- `H_4`
  have hm4 : Nonempty ((↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 4) →ₗ[ℤ] AddCircle (1 : ℚ)) ≃ₗ[ℤ]
      ZMod 2) :=
    ⟨u5.symm.trans h5.some⟩
  have hOut4 := hAux (htors 4 (by norm_num) (by norm_num)) 2 (by norm_num) (hmod4 ▸ hm4)
  have eAdd4 : Nonempty ((Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 4) ≃+ ZMod 2) :=
    hOut4.map (fun e => AddEquiv.mk e.toEquiv (fun a b => e.map_add a b))
  have eH4 : Nonempty (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 4 ≃ₗ[ℤ] ZMod 2) :=
    ⟨AddEquiv.toIntLinearEquiv eAdd4.some⟩
  -- `H_5`
  haveI : Subsingleton ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.singularChains ℤ
      (TopCat.of (Work.Pi6.Ecov g3)))).homology 6) := h6
  have hhom5 : Subsingleton ((↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 5) →ₗ[ℤ] AddCircle (1 : ℚ))) :=
    ⟨fun f g => u6.symm.injective (Subsingleton.elim (u6.symm f) (u6.symm g))⟩
  have hsH5 : Subsingleton (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 5) :=
    hsub (htors 5 (by norm_num) (by norm_num)) (hmod5 ▸ hhom5)
  -- `H_6`
  have hm6 : Nonempty ((↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 6) →ₗ[ℤ] AddCircle (1 : ℚ)) ≃ₗ[ℤ]
      ZMod 3) :=
    ⟨u7.symm.trans h7.some⟩
  have hOut6 := hAux (htors 6 (by norm_num) (by norm_num)) 3 (by norm_num) (hmod6 ▸ hm6)
  have eAdd6 : Nonempty ((Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 6) ≃+ ZMod 3) :=
    hOut6.map (fun e => AddEquiv.mk e.toEquiv (fun a b => e.map_add a b))
  have eH6 : Nonempty (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 6 ≃ₗ[ℤ] ZMod 3) :=
    ⟨AddEquiv.toIntLinearEquiv eAdd6.some⟩
  -- `H_7`
  haveI : Subsingleton ((Work.Cohomology.dualComplex ℤ (Work.Cohomology.singularChains ℤ
      (TopCat.of (Work.Pi6.Ecov g3)))).homology 8) := h8
  have hhom7 : Subsingleton ((↥(Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 7) →ₗ[ℤ] AddCircle (1 : ℚ))) :=
    ⟨fun f g => u8.symm.injective (Subsingleton.elim (u8.symm f) (u8.symm g))⟩
  have hsH7 : Subsingleton (Work.Pi6.HR ℤ (Work.Pi6.Ecov g3) 7) :=
    hsub (htors 7 (by norm_num) (by norm_num)) (hmod7 ▸ hhom7)
  exact ⟨eH4, hsH5, eH6, hsH7⟩

end Work.Pi6.EFACTS
