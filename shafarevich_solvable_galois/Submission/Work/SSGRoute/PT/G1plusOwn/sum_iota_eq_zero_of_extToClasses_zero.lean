import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PT.glue_helpers
import Submission.Work.SSGRoute.localSumDecomposition
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT.G1plusOwn

open CategoryTheory
open SSGRoute.PTExt

/-- The decomposition used by `sum_iota_eq_zero_of_extToClasses_zero`: a globally paired class
`Z' ⌣ h ∈ H²(Gal(L/k), 𝕀_L)` is the sum of the orbit-insertions `ι_v` of its own local pairings,
over a Finset `W` of pairwise non-conjugate places at which all the non-vanishing local pairings
live. -/
theorem decomp_yonedaPair_eq_sum_iotaLift_local
    {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    {M' : Rep.{0} SSGRoute.PTExt.Coeff (L ≃ₐ[k] L)}
    (Z' : CategoryTheory.Abelian.Ext M' (SSGRoute.PTExt.idelesK k L) 1)
    (h : SSGRoute.PTExt.extH M' 1)
    (W : Finset (NK.GlobalCFT.Place L))
    (hW : ∀ w ∈ W, ∀ w' ∈ W, (∃ σ : L ≃ₐ[k] L, σ • w = w') → w = w')
    (hT : ∀ w : NK.GlobalCFT.Place L,
      (∀ w' ∈ W, ∀ σ : L ≃ₐ[k] L, σ • w' ≠ w) →
      SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := L) w Z')
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w) h) = 0) :
    SSGRoute.PTExt.yonedaPair Z' h =
      ∑ w ∈ W, Work.SSGRoute.PT.iotaLift (k := k) (L := L) w
        (SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := L) w Z')
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w) h)) := by
  classical
  set y : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k L) 2 :=
    SSGRoute.PTExt.yonedaPair Z' h with hy
  -- the local pairings are the localisations of `y`
  have hlp : ∀ w : NK.GlobalCFT.Place L,
      SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := L) w Z')
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w) h)
      = SSGRoute.PTExt.extLoc (k := k) (K := L) w y := by
    intro w
    rw [hy, Work.SSGRoute.PT.extLoc_yonedaPair (k := k) (K := L)]
  set D : SSGRoute.PTExt.extH (SSGRoute.PTExt.idelesK k L) 2 :=
    y - ∑ w ∈ W, Work.SSGRoute.PT.iotaLift (k := k) (L := L) w
      (SSGRoute.PTExt.extLoc (k := k) (K := L) w y) with hD
  have hWzero : ∀ w ∈ W, SSGRoute.PTExt.extLoc (k := k) (K := L) w D = 0 := by
    intro w hw
    rw [hD, Work.SSGRoute.PT.extLoc_sub, Work.SSGRoute.PT.extLoc_sum]
    have hsum : (∑ v ∈ W, SSGRoute.PTExt.extLoc (k := k) (K := L) w
          (Work.SSGRoute.PT.iotaLift (k := k) (L := L) v
            (SSGRoute.PTExt.extLoc (k := k) (K := L) v y)))
        = SSGRoute.PTExt.extLoc (k := k) (K := L) w y := by
      refine (Finset.sum_eq_single w ?_ ?_).trans
        (Work.SSGRoute.PT.iotaLift_spec (k := k) (L := L) w
          (SSGRoute.PTExt.extLoc (k := k) (K := L) w y)).1
      · intro b hb hbw
        exact (Work.SSGRoute.PT.iotaLift_spec (k := k) (L := L) b
          (SSGRoute.PTExt.extLoc (k := k) (K := L) b y)).2 w
          (fun σ hσ => hbw (hW b hb w hw ⟨σ, hσ⟩))
      · intro h; exact absurd hw h
    rw [hsum, sub_self]
  have hloc : ∀ v : NK.GlobalCFT.Place L,
      SSGRoute.PTExt.extLoc (k := k) (K := L) v D = 0 := by
    intro v
    by_cases hv : ∀ w' ∈ W, ∀ σ : L ≃ₐ[k] L, σ • w' ≠ v
    · have h1 : SSGRoute.PTExt.extLoc (k := k) (K := L) v y = 0 := by
        rw [hy, Work.SSGRoute.PT.extLoc_yonedaPair (k := k) (K := L)]
        exact hT v hv
      rw [hD, Work.SSGRoute.PT.extLoc_sub, Work.SSGRoute.PT.extLoc_sum, h1]
      have hz : (∑ b ∈ W, SSGRoute.PTExt.extLoc (k := k) (K := L) v
            (Work.SSGRoute.PT.iotaLift (k := k) (L := L) b
              (SSGRoute.PTExt.extLoc (k := k) (K := L) b y))) = 0 :=
        Finset.sum_eq_zero (fun b hb =>
          (Work.SSGRoute.PT.iotaLift_spec (k := k) (L := L) b
            (SSGRoute.PTExt.extLoc (k := k) (K := L) b y)).2 v (hv b hb))
      rw [hz, sub_zero]
    · push_neg at hv
      obtain ⟨w₀, hw₀, σ, hσ⟩ := hv
      rw [← hσ]
      exact Work.SSGRoute.e9c_extLoc_conj_zero (k := k) (K := L) D σ w₀ (hWzero w₀ hw₀)
  have hD0 : D = 0 := Work.SSGRoute.extIdele_localisation_injective k L D (fun v => by
    rw [Work.SSGRoute.extRes_eq_extHRestrict (D := decompK (k := k) v) D]
    change SSGRoute.PTExt.extLoc (k := k) (K := L) v D = 0
    exact hloc v)
  rw [hD] at hD0
  have hy0 : y = ∑ w ∈ W, Work.SSGRoute.PT.iotaLift (k := k) (L := L) w
      (SSGRoute.PTExt.extLoc (k := k) (K := L) w y) := sub_eq_zero.mp hD0
  rw [hy0]
  exact Finset.sum_congr rfl (fun w _ => by rw [hlp w])

/-- `sum_iota_eq_zero_of_extToClasses_zero`: if `Z'` is a class whose image in `H²(Gal(L/k), C_L)`
vanishes, then the sum of the `χ`-values of the local `ι_w`-placements of the pairings of `Z'` with
`h`, over a Finset `W` of pairwise non-conjugate places carrying all non-vanishing local pairings,
is zero. -/
theorem sum_iota_eq_zero_of_extToClasses_zero
    (p : ℕ) [Fact p.Prime] {k L : Type} [Field k] [NumberField k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    {M' : Rep.{0} SSGRoute.PTExt.Coeff (L ≃ₐ[k] L)}
    (χ : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2 → ZMod p)
    (hχadd : ∀ u v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2,
      p • u = 0 → p • v = 0 → χ (u + v) = χ u + χ v)
    (Z' : CategoryTheory.Abelian.Ext M' (SSGRoute.PTExt.idelesK k L) 1)
    (hZ : SSGRoute.PTExt.extToClasses Z' = 0)
    (h : SSGRoute.PTExt.extH M' 1)
    (W : Finset (NK.GlobalCFT.Place L))
    (hW : ∀ w ∈ W, ∀ w' ∈ W, (∃ σ : L ≃ₐ[k] L, σ • w = w') → w = w')
    (hT : ∀ w : NK.GlobalCFT.Place L,
      (∀ w' ∈ W, ∀ σ : L ≃ₐ[k] L, σ • w' ≠ w) →
      SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := L) w Z')
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w) h) = 0)
    (hp : ∀ w ∈ W, p • Work.SSGRoute.PT.iota (k := k) (L := L) w
      (SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := L) w Z')
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w) h)) = 0) :
    ∑ w ∈ W, χ (Work.SSGRoute.PT.iota (k := k) (L := L) w
        (SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := L) w Z')
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w) h))) = 0 := by
  classical
  have hdecomp :=
    decomp_yonedaPair_eq_sum_iotaLift_local (k := k) (L := L) Z' h W hW hT
  -- `extToClasses` of the decomposition
  have hcls : SSGRoute.PTExt.extToClasses (k := k) (SSGRoute.PTExt.yonedaPair Z' h)
      = ∑ w ∈ W, Work.SSGRoute.PT.iota (k := k) (L := L) w
        (SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := L) w Z')
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w) h)) := by
    rw [hdecomp, Work.SSGRoute.PT.extToClasses_sum]
    exact Finset.sum_congr rfl (fun w _ => rfl)
  -- the left-hand class vanishes
  have hcl0 : SSGRoute.PTExt.extToClasses (k := k) (SSGRoute.PTExt.yonedaPair Z' h) = 0 := by
    rw [← Work.SSGRoute.PT.extToClasses_yonedaPair (k := k) (K := L) Z' h, hZ]
    exact SSGRoute.PTExt.pairK_zero_right (k := k) (K := L) (M := M') (r := 1) h
  rw [← Work.SSGRoute.PT.chi_finset_sum (k := k) (K := L) p χ hχadd W
      (fun w => Work.SSGRoute.PT.iota (k := k) (L := L) w
        (SSGRoute.PTExt.yonedaPair (SSGRoute.PTExt.extLoc (k := k) (K := L) w Z')
          (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) w) h))) hp]
  rw [← hcls, hcl0]
  exact Work.SSGRoute.PT.chi_zero_of_additive (k := k) (K := L) p χ hχadd

end Work.SSGRoute.PT.G1plusOwn
