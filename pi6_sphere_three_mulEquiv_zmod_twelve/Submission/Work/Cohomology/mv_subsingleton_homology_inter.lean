import Mathlib
import Submission.Work.Cohomology.homologyMV
import Submission.Work.Cohomology.homology_biprod_iso
import Submission.Work.Cohomology.homologyMV_honest_les

/-!
# Vanishing of `H_n(U ∩ V)` from the Mayer–Vietoris sequence

Let `X` be a topological space, `U, V ⊆ X` open with `U ∪ V = X`.  The honest Mayer–Vietoris long
exact sequence (`Work.Cohomology.homologyMV_honest_les`) reads

`⋯ → H_{n+1}(U) ⊞ H_{n+1}(V) → H_{n+1}(X) --δ--> H_n(U ∩ V) --F--> H_n(U) ⊞ H_n(V) → ⋯`

If `H_n(U)` and `H_n(V)` vanish then `F = 0`, so by exactness at `H_n(U ∩ V)` the connecting map
`δ` is surjective; if in addition `H_{n+1}(X)` vanishes then `H_n(U ∩ V)`, being a quotient of it,
vanishes.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Limits

namespace Work.Cohomology

noncomputable section

theorem mv_subsingleton_homology_inter {X : TopCat} (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (n : ℕ)
    (hUn : Subsingleton ((singularChains ℤ (TopCat.of U)).homology n))
    (hVn : Subsingleton ((singularChains ℤ (TopCat.of V)).homology n))
    (hUn1 : Subsingleton ((singularChains ℤ (TopCat.of U)).homology (n + 1)))
    (hVn1 : Subsingleton ((singularChains ℤ (TopCat.of V)).homology (n + 1)))
    (hXn1 : Subsingleton ((singularChains ℤ X).homology (n + 1))) :
    Subsingleton ((singularChains ℤ (TopCat.of ↥(U ∩ V))).homology n) := by
  -- `H_n(U)` and `H_n(V)` are zero objects, so both components of `F_n` vanish.
  have hUnz : IsZero (pdHomSub X U n) := ModuleCat.isZero_iff_subsingleton.mpr hUn
  have hVnz : IsZero (pdHomSub X V n) := ModuleCat.isZero_iff_subsingleton.mpr hVn
  have hF : homMVF X U V n = 0 := by
    apply biprod.hom_ext
    · rw [zero_comp]
      show homMVF X U V n ≫ pdHomBiprodFst X U V n = 0
      rw [homMVF_fst]
      exact IsZero.eq_zero_of_tgt hUnz _
    · rw [zero_comp]
      show homMVF X U V n ≫ pdHomBiprodSnd X U V n = 0
      rw [homMVF_snd]
      exact IsZero.eq_zero_of_tgt hVnz _
  -- Exactness at `H_n(U ∩ V)` then makes the connecting map surjective.
  haveI : Epi (homMVδ X U V hU hV hcov n) :=
    (ShortComplex.exact_iff_epi _ hF).mp (homMV_exact₁ X U V hU hV hcov n)
  haveI : Subsingleton (pdHom X (n + 1)) := hXn1
  have hsurj := (ModuleCat.epi_iff_surjective (homMVδ X U V hU hV hcov n)).mp inferInstance
  exact hsurj.subsingleton

end

end Work.Cohomology
