import Mathlib
import Submission.Work.Projective.cp2V_cohomology
import Submission.Work.Projective.cp2UV_cohomology
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Cohomology.sphereHomologyZero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The homology of the pieces of the Mayer–Vietoris cover of `ℂP²` (positive degrees)

The homology counterparts of `Work.Projective.cp2V_cohomology` and
`Work.Projective.cp2UV_cohomology`, in the positive degrees in which the fundamental class
computation of `ℂP²` needs them: `Hₙ(V) = 0` for `n > 0`, `n ≠ 2` and `H₂(V) ≅ ℤ` (`V` is
homotopy equivalent to `S²`), and `Hₙ(U ∩ V) = 0` for `n > 0`, `n ≠ 3` and `H₃(U ∩ V) ≅ ℤ`
(`U ∩ V` is homotopy equivalent to `S³`).
-/

set_option maxHeartbeats 800000

namespace Work.Projective

open CategoryTheory Limits Work.Cohomology

noncomputable section

/-- **The positive-degree homology of `V = ℂP² ∖ {[1:0:0]}`**: `H₂(V) ≅ ℤ` and the other positive
degrees vanish. -/
theorem cp2V_homology (n : ℕ) (hn : 0 < n) :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(cp2V))).homology n ≅
      ModuleCat.of ℤ (Fin (if n = 2 then 1 else 0) → ℤ)) := by
  obtain ⟨e1⟩ := homologyIso_of_homotopyEquiv (nonempty_homotopyEquiv_cp2V_sphere.some) n
  by_cases h2 : n = 2
  · subst h2
    rw [if_pos rfl]
    obtain ⟨e2⟩ := sphereHomologyTop 2 (by norm_num)
    exact ⟨e1 ≪≫ e2 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
  · rw [if_neg h2]
    exact ⟨e1 ≪≫ CategoryTheory.Limits.IsZero.iso
      (sphereHomologyZero 2 n (by norm_num) (by omega) h2)
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℤ (Fin 0 → ℤ)))⟩

/-- **The positive-degree homology of `U ∩ V`**: `H₃(U ∩ V) ≅ ℤ` and the other positive degrees
vanish. -/
theorem cp2UV_homology (n : ℕ) (hn : 0 < n) :
    Nonempty ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(cp2U ∩ cp2V))).homology n ≅
      ModuleCat.of ℤ (Fin (if n = 3 then 1 else 0) → ℤ)) := by
  obtain ⟨e1⟩ := homologyIso_of_homotopyEquiv (cp2UV_homotopyEquiv_sphere.some) n
  by_cases h3 : n = 3
  · subst h3
    rw [if_pos rfl]
    obtain ⟨e2⟩ := sphereHomologyTop 3 (by norm_num)
    exact ⟨e1 ≪≫ e2 ≪≫ (LinearEquiv.funUnique (Fin 1) ℤ ℤ).toModuleIso.symm⟩
  · rw [if_neg h3]
    exact ⟨e1 ≪≫ CategoryTheory.Limits.IsZero.iso
      (sphereHomologyZero 3 n (by norm_num) (by omega) h3)
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of ℤ (Fin 0 → ℤ)))⟩

/-- Vanishing, in the form needed by the Mayer–Vietoris assembly. -/
theorem isZero_cochainV_homology_cp2 {n : ℕ} (hn : 0 < n) (h2 : n ≠ 2) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(cp2V))).homology n) := by
  obtain ⟨e⟩ := cp2V_homology n hn
  rw [if_neg h2] at e
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) e

/-- Vanishing, in the form needed by the Mayer–Vietoris assembly. -/
theorem isZero_cochainUV_homology_cp2 {n : ℕ} (hn : 0 < n) (h3 : n ≠ 3) :
    IsZero ((Work.Cohomology.singularChains ℤ (TopCat.of ↥(cp2U ∩ cp2V))).homology n) := by
  obtain ⟨e⟩ := cp2UV_homology n hn
  rw [if_neg h3] at e
  exact IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) e

end

end Work.Projective
