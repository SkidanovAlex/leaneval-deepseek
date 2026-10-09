import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.PT.g1plus_iota
import Submission.Work.SSGRoute.CokerPT.IotaAlgebra
import Submission.Work.SSGRoute.localSumDecomposition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead design (Claude) 10-05 03:15 (_lead_design/flags_0230/p2/NOTE.md): p = 2 pieces for G1⁺ (involution pairing χ∘ι∘yonedaPair replaces E7Arch.pairArchFamily at p = 2).
-/

namespace Work.SSGRoute.PT

open CategoryTheory
open SSGRoute.PTExt

/-!
## Auxiliary vocabulary

`SSGRoute.PTExt.extLoc`'s *declared* codomain is
`Abelian.Ext (Rep.res (decompK w).subtype M) (localUnitsK w) r`, while the coefficient calculus
(additivity, `nsmul`, the Yoneda pairing) is stated for `extH (localUnitsK w) r =
Abelian.Ext (unitRep (decompK w)) (localUnitsK w) r`.  The two types are definitionally equal for
`M = unitRep _`, but not *syntactically*, and since `rw` matches modulo the `implicit` transparency
level, a term of the form `iota r (extLoc r x)` cannot be rewritten by the calculator lemmas
(`Work.SSGRoute.PT.iota_add`, `…iota_nsmul`).  `extLocH` is `extLoc` with the codomain *re-typed*
at `extH`, so that the same term can be used both as an `iota`-argument and as a rewrite pattern.
-/

section Helpers

set_option linter.unusedSectionVars false

variable {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]

/-- `extLoc` with its codomain re-typed at `extH`: the form in which the coefficient calculus
applies to the localisation of an idèle class. -/
noncomputable def extLocH (w : NK.GlobalCFT.Place L) (Z : extH (idelesK k L) 2) :
    extH (localUnitsK (k := k) (K := L) w) 2 :=
  extLoc (k := k) w Z

/-- `extLocH` kills the zero class. -/
theorem extLocH_zero (w : NK.GlobalCFT.Place L) :
    extLocH (k := k) (L := L) w (0 : extH (idelesK k L) 2) = 0 := by
  rw [show extLocH (k := k) (L := L) w (0 : extH (idelesK k L) 2)
      = extLoc (k := k) w (0 : extH (idelesK k L) 2) from rfl]
  exact extLoc_zero (k := k) (K := L) w

/-- `extLocH` is additive. -/
theorem extLocH_add (w : NK.GlobalCFT.Place L) (Z Z' : extH (idelesK k L) 2) :
    extLocH (k := k) (L := L) w (Z + Z') =
      extLocH (k := k) (L := L) w Z + extLocH (k := k) (L := L) w Z' := by
  rw [show extLocH (k := k) (L := L) w (Z + Z') = extLoc (k := k) w (Z + Z') from rfl,
    show extLocH (k := k) (L := L) w Z = extLoc (k := k) w Z from rfl,
    show extLocH (k := k) (L := L) w Z' = extLoc (k := k) w Z' from rfl]
  exact extLoc_add (k := k) (K := L) w Z Z'

/-- `extLocH` is `nsmul`-compatible (localisation of the idèle class group is additive). -/
theorem extLocH_nsmul (w : NK.GlobalCFT.Place L) (n : ℕ) (Z : extH (idelesK k L) 2) :
    extLocH (k := k) (L := L) w (n • Z) = n • extLocH (k := k) (L := L) w Z :=
  AddMonoidHom.map_nsmul
    { toFun := fun Z => extLocH (k := k) (L := L) w Z
      map_zero' := extLocH_zero (k := k) (L := L) w
      map_add' := fun a b => extLocH_add (k := k) (L := L) w a b } n Z

/-- The orbit-placement map `ι_w` is `nsmul`-compatible (`Work.SSGRoute.PT.iota_add` and
`…iota_zero`). -/
theorem iota_nsmul (r : NK.GlobalCFT.Place L) (n : ℕ)
    (z : extH (localUnitsK (k := k) (K := L) r) 2) :
    iota (k := k) (L := L) r (n • z) = n • iota (k := k) (L := L) r z := by
  induction n with
  | zero => rw [zero_nsmul, iota_zero, zero_nsmul]
  | succ n ih => rw [succ_nsmul, succ_nsmul, iota_add, ih]

/-- `ι_w` kills a class whose localisation at `w` is zero. -/
theorem iota_extLocH_zero (w : NK.GlobalCFT.Place L) (Z : extH (idelesK k L) 2)
    (h : extLocH (k := k) (L := L) w Z = 0) :
    iota (k := k) (L := L) w (extLocH (k := k) (L := L) w Z) = 0 := by
  rw [h]
  exact iota_zero (k := k) (L := L) w

/-- **`p`-torsion survives the orbit-placement of a localisation**: the input that lets `χ`'s
additivity on `p`-torsion be applied to the terms `ι_w (extLoc w Z)`. -/
theorem iota_extLocH_ptorsion (p : ℕ) (w : NK.GlobalCFT.Place L) (Z : extH (idelesK k L) 2)
    (hZ : p • Z = 0) :
    p • iota (k := k) (L := L) w (extLocH (k := k) (L := L) w Z) = 0 := by
  have h1 := iota_nsmul (k := k) (L := L) w p (extLocH (k := k) (L := L) w Z)
  have h2 := extLocH_nsmul (k := k) (L := L) w p Z
  rw [hZ, extLocH_zero (k := k) (L := L) w] at h2
  rw [← h1, h2.symm, iota_zero]

/-- `extToIdeles` is `nsmul`-compatible. -/
theorem extToIdeles_nsmul {M : Rep.{0} Coeff (L ≃ₐ[k] L)} {r : ℕ} (n : ℕ)
    (x : Abelian.Ext.{0} M (unitsK k L) r) :
    extToIdeles (n • x) = n • extToIdeles (M := M) x := by
  induction n with
  | zero => rw [zero_nsmul, extToIdeles_zero (M := M), zero_nsmul]
  | succ n ih => rw [succ_nsmul, succ_nsmul, extToIdeles_add, ih]

/-- **The class-formation sum, in the vector notation of the target.**  An idèle class of
`H²(Gal(L/k), 𝕀_L)` with finitely many nonzero local components is, in `H²(Gal(L/k), C_L)`, the sum
of the `ι`-images of its components on a transversal of the places. -/
theorem extToClasses_eq_finsum_iota_places (R : Set (NK.GlobalCFT.Place L))
    (hR : ∀ w : NK.GlobalCFT.Place L, ∃! w' : R, ∃ σ : L ≃ₐ[k] L, σ • w = w'.1)
    (Z : extH (idelesK k L) 2)
    (hfin : {w : R | extLocH (k := k) (L := L) w.1 Z ≠ 0}.Finite) :
    extToClasses (k := k) Z =
      ∑ᶠ w : R, iota (k := k) (L := L) w.1 (extLocH (k := k) (L := L) w.1 Z) := by
  classical
  set F : Finset R := hfin.toFinset with hF
  have hFmem : ∀ w : R, w ∉ F → extLocH (k := k) (L := L) w.1 Z = 0 := by
    intro w hw
    by_contra hne
    exact hw (hF ▸ (Set.Finite.mem_toFinset hfin).2 hne)
  have hsub : Function.support
      (fun w : R => iota (k := k) (L := L) w.1 (extLocH (k := k) (L := L) w.1 Z))
      ⊆ (F : Set R) := by
    intro w hw
    rw [Function.mem_support] at hw
    by_contra hwF
    exact hw (iota_extLocH_zero (k := k) (L := L) w.1 Z (hFmem w hwF))
  have hdecomp : Z = ∑ w ∈ F, iotaLift (k := k) (L := L) w.1
      (extLocH (k := k) (L := L) w.1 Z) :=
    eq_sum_iotaLift_of_extLoc_eq_zero_off (k := k) (K := L) R hR Z F hFmem
  have hmain : extToClasses (k := k) Z =
      ∑ w ∈ F, iota (k := k) (L := L) w.1 (extLocH (k := k) (L := L) w.1 Z) := by
    conv_lhs => rw [hdecomp]
    rw [extToClasses_sum]
    rfl
  rw [hmain, finsum_eq_sum_of_support_subset
    (fun w : R => iota (k := k) (L := L) w.1 (extLocH (k := k) (L := L) w.1 Z)) hsub]

/-- **Reciprocity at all places, for an idèle class killed by the class-formation map.**  If
`extToClasses Z = 0` and `Z` is `p`-torsion, then the sum over a transversal `R` of the `χ`-values of
`ι_w (extLoc w Z)` is `0`.

`extToClasses Z = Σ_w ι_w (extLoc w Z)` (`extToClasses_eq_finsum_iota_places`) makes both sides the
`χ`-image of one element of `H²(Gal(L/k), C_L)`; the sum is finite because the support of
`w ↦ extLoc w Z` is, and `χ` is additive on the finitely many `p`-torsion terms. -/
theorem sum_chi_iota_eq_zero_of_extToClasses (p : ℕ) [Fact p.Prime]
    (χ : extH (classesK k L) 2 → ZMod p)
    (hχadd : ∀ u v : extH (classesK k L) 2, p • u = 0 → p • v = 0 → χ (u + v) = χ u + χ v)
    (Z : extH (idelesK k L) 2) (hZ0 : extToClasses (k := k) Z = 0) (hZpt : p • Z = 0)
    (R : Set (NK.GlobalCFT.Place L))
    (hR : ∀ w : NK.GlobalCFT.Place L, ∃! w' : R, ∃ σ : L ≃ₐ[k] L, σ • w = w'.1)
    (hfin : {w : R | extLocH (k := k) (L := L) w.1 Z ≠ 0}.Finite) :
    ∑ᶠ w : R, χ (iota (k := k) (L := L) w.1 (extLocH (k := k) (L := L) w.1 Z)) = 0 := by
  classical
  set F : Finset R := hfin.toFinset with hF
  have hFmem : ∀ w : R, w ∉ F → extLocH (k := k) (L := L) w.1 Z = 0 := by
    intro w hw
    by_contra hne
    exact hw (hF ▸ (Set.Finite.mem_toFinset hfin).2 hne)
  have hterm : ∀ w : R, w ∉ F →
      χ (iota (k := k) (L := L) w.1 (extLocH (k := k) (L := L) w.1 Z)) = 0 := by
    intro w hw
    rw [iota_extLocH_zero (k := k) (L := L) w.1 Z (hFmem w hw)]
    exact chi_zero_of_additive p χ hχadd
  have hsub : Function.support
      (fun w : R => iota (k := k) (L := L) w.1 (extLocH (k := k) (L := L) w.1 Z))
      ⊆ (F : Set R) := by
    intro w hw
    rw [Function.mem_support] at hw
    by_contra hwF
    exact hw (iota_extLocH_zero (k := k) (L := L) w.1 Z (hFmem w hwF))
  have hsubχ : Function.support
      (fun w : R => χ (iota (k := k) (L := L) w.1 (extLocH (k := k) (L := L) w.1 Z)))
      ⊆ (F : Set R) := by
    intro w hw
    rw [Function.mem_support] at hw
    by_contra hwF
    exact hw (hterm w hwF)
  have hpt : ∀ w ∈ F,
      p • iota (k := k) (L := L) w.1 (extLocH (k := k) (L := L) w.1 Z) = 0 :=
    fun w _ => iota_extLocH_ptorsion (k := k) (L := L) p w.1 Z hZpt
  have hsum0 :
      (∑ᶠ w : R, iota (k := k) (L := L) w.1 (extLocH (k := k) (L := L) w.1 Z)) = 0 := by
    rw [← extToClasses_eq_finsum_iota_places (k := k) (L := L) R hR Z hfin, hZ0]
  have hchi : χ (∑ᶠ w : R, iota (k := k) (L := L) w.1 (extLocH (k := k) (L := L) w.1 Z)) =
      ∑ᶠ w : R, χ (iota (k := k) (L := L) w.1 (extLocH (k := k) (L := L) w.1 Z)) := by
    rw [finsum_eq_sum_of_support_subset
          (fun w : R => iota (k := k) (L := L) w.1 (extLocH (k := k) (L := L) w.1 Z)) hsub,
        finsum_eq_sum_of_support_subset
          (fun w : R => χ (iota (k := k) (L := L) w.1 (extLocH (k := k) (L := L) w.1 Z)))
          hsubχ]
    exact chi_finset_sum p χ hχadd F
      (fun w => iota (k := k) (L := L) w.1 (extLocH (k := k) (L := L) w.1 Z)) hpt
  rw [← hchi, hsum0]
  exact chi_zero_of_additive p χ hχadd

end Helpers

/-- The class-formation reciprocity for a global `H²(Lˣ)` class, at all places, finite and
infinite: the uniform core of G1⁺ clause (7) once the involution pairing is swapped to `χ ∘ ι`.

`Y ∈ H²(Gal(L/k), Lˣ)` is `p`-torsion.  `χ` is additive on the `p`-torsion of
`H²(Gal(L/k), C_L)`.  `R` is a transversal of all places of `L` (finite and infinite), and only
finitely many local components of `extToIdeles Y` are nonzero.  Then the sum over `R` of
`χ (iota w (extLoc w (extToIdeles Y)))` is `0`.

The swap.  At `p = 2`, G1⁺'s glued pairing must take at an involution `c` the value
`χ_L (iota w_c (yonedaPair (βc a) [b]))`, with `βc`, `w_c` from `localDictionary_natural_family_arch`,
and not `E7Arch.pairArchFamily`, whose normalisation is unrelated to `χ`.  For global `a`, `b`, every
finite-place term (`hpair`, `hsq`, `levelPair_extLoc_eq_push`) and every involution term (the arch
square + `PT.extLoc_yonedaPair`) is `χ (iota w (extLoc w (extToIdeles Y)))` for the single global
class `Y := levelPair (βg a) h_b`.  Terms at places outside `S′ ∪ C′` vanish
(`levelPair_unramified_eq_zero`; complex-over-complex places have `D = ⊥`).  So (7) is this statement.
Clause (4) at involutions for the swapped pairing is `archYoneda_perfect` plus injectivity of `ι`
(`PT.pt_orbitIdele_H2_eq_zero`, any place) and of `χ`.

Route.  `extToClasses_eq_finsum_iota` (dispatched), then `extToClasses ∘ extToIdeles = 0` (the class
formation `Lˣ → 𝕀_L → C_L` is a complex, `NK.HassePrinciple.ideleShortComplex`), then additivity of
`χ` on the finitely many `p`-torsion terms (`p • Y = 0` gives `p • (each term) = 0`). -/
theorem classFormation_reciprocity_allPlaces (p : ℕ) [Fact p.Prime] (k L : Type) [Field k]
    [NumberField k] [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (χ : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2 → ZMod p)
    (hχadd : ∀ u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2,
      p • u = 0 → p • v = 0 → χ (u + v) = χ u + χ v)
    (Y : SSGRoute.PTExt.extH (SSGRoute.PTExt.unitsK k L) 2) (hY : p • Y = 0)
    (R : Set (NK.GlobalCFT.Place L))
    (hR : ∀ w : NK.GlobalCFT.Place L, ∃! w' : R, ∃ σ : L ≃ₐ[k] L, σ • w = w'.1)
    (hfin : {w : R | SSGRoute.PTExt.extLoc (k := k) w.1
        (SSGRoute.PTExt.extToIdeles (k := k) Y) ≠ 0}.Finite) :
    ∑ᶠ w : R, χ (Work.SSGRoute.PT.iota (k := k) (L := L) w.1
        (SSGRoute.PTExt.extLoc (k := k) w.1 (SSGRoute.PTExt.extToIdeles (k := k) Y))) = 0 := by
  classical
  change ∑ᶠ w : R, χ (Work.SSGRoute.PT.iota (k := k) (L := L) w.1
      (extLocH (k := k) (L := L) w.1 (SSGRoute.PTExt.extToIdeles (k := k) Y))) = 0
  have hZ0 : extToClasses (k := k) (extToIdeles (k := k) Y) = 0 :=
    extToClasses_extToIdeles (k := k) (K := L) Y
  have hZpt : p • (extToIdeles (k := k) Y) = 0 := by
    have h1 := extToIdeles_nsmul (k := k) (L := L) (M := unitRep (L ≃ₐ[k] L)) p Y
    rw [hY, extToIdeles_zero] at h1
    exact h1.symm
  exact sum_chi_iota_eq_zero_of_extToClasses (k := k) (L := L) p χ hχadd
    (extToIdeles (k := k) Y) hZ0 hZpt R hR hfin

end Work.SSGRoute.PT
