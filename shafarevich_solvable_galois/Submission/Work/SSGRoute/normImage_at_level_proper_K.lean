import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Submission.NK.CFTLib.IdeleHasse.Descent.exists_localAlgebraMapUnits_eq_of_ker_fixed
import Submission.NK.CFTLib.IdeleHasse.Descent.stabRestrict_surjective
import Submission.Work.SSGRoute.decompK_restrict_surjective
import Submission.Work.SSGRoute.localUnitsEquiv_fixed_iff_ringEquiv_fixed
import Submission.Work.SSGRoute.localUnitsMap_exists
import Submission.Work.SSGRoute.normImage_at_level_proper
import Submission.Work.SSGRoute.phi1_level_naturality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.SSGRoute

/-- **The norm image at a level is proper, in the `K_wˣ` form.**  For `k ⊆ K` finite Galois
number fields, a place `w` of `K`, a level `L ⊇ K` (Galois over `k`), a place `w' ∣ w` and a normal
subgroup `N ⊴ D_{w'}` with `D_{w'} ⧸ N` cyclic of order the prime `p`, there is a unit `v` of
`K_w` which is fixed by the whole decomposition group `D_w` (through
`NK.HassePrinciple.localUnitsEquiv`) and whose image `NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' v`
in `L_{w'}ˣ` is not a quotient-norm over `N` (i.e. is not
`∑_{x ∈ D_{w'}/N} ρ (out x) bb` for an `N`-fixed `bb`).

This is `Work.SSGRoute.normImage_at_level_proper` (proved) transported from the `k`-base-field
description to the `K_wˣ` description needed by the `Y1` detection node: the element produced there
is `D_{w'}`-fixed, hence (local fixed-field theorem
`NK.GlobalCFT.Inclusion.globalCFT_localFixed_mem_range`) the image of a `v ∈ K_wˣ` under
`NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw'`; the remaining content is that such a `v` is
`D_w`-fixed, which follows from the Galois-equivariance of `NK.GlobalCFT.Place.localAlgebraMapUnits`
(`NK.GlobalCFT.Galois.globalCFT_localRingEquiv_localAlgebraMapUnits`) and the surjectivity of
`D_{w'} → D_w` on decomposition groups (`Work.SSGRoute.decompK_restrict_surjective`).  In the
archimedean case (`w'` complex) the witness is `v = -1`, which is trivially `D_w`-fixed. -/
theorem normImage_at_level_proper_K (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) w')) [N.Normal]
    [Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N)]
    (hcyc : IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N))
    (hcard : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) = p) :
    ∃ v : (NK.GlobalCFT.Place.localField K w)ˣ,
      (∀ σ : SSGRoute.PTExt.decompK (k := k) w,
        NK.HassePrinciple.localUnitsEquiv (K := k) w σ v = v) ∧
      ¬ (∃ bb : NK.HassePrinciple.localUnitsRep k L w',
        (∀ n : N, (NK.HassePrinciple.localUnitsRep k L w').ρ
          (n : MulAction.stabilizer (L ≃ₐ[k] L) w') bb = bb) ∧
        (∑ x : MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N,
          (NK.HassePrinciple.localUnitsRep k L w').ρ (Quotient.out x) bb) =
          Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w hw' v)) := by
  classical
  -- the proved `k`-base-field form of the statement
  obtain ⟨a, hafix, hnot⟩ :=
    normImage_at_level_proper p k K w L w' hw' N hcyc hcard
  -- the tower `L / K` is again Galois and finite
  haveI : IsGalois K L := IsGalois.tower_top_of_isGalois k K L
  haveI : FiniteDimensional K L := FiniteDimensional.right k K L
  -- `a`, whose type is the carrier of the representation, read as an honest unit of `L_{w'}`
  let a₀ : (NK.GlobalCFT.Place.localField L w')ˣ :=
    (show Additive ((NK.GlobalCFT.Place.localField L w')ˣ) from a).toMul
  have hof : Additive.ofMul a₀ = a := rfl
  -- local Galois descent of the `D_{w'}`-fixed element to a unit of `K_w`
  obtain ⟨u, hu⟩ :=
    NK.CFTLib.IdeleHasse.Descent.exists_localAlgebraMapUnits_eq_of_ker_fixed
      (K := k) (M := K) (E := L) w w' hw' a₀
      (fun s => hafix (s : MulAction.stabilizer (L ≃ₐ[k] L) w'))
  refine ⟨u, ?_, ?_⟩
  · -- `u` is fixed by the whole decomposition group `D_w`
    intro τ
    obtain ⟨σ, hσ⟩ :=
      NK.CFTLib.IdeleHasse.Descent.stabRestrict_surjective
        (K := k) (M := K) (E := L) w w' hw' τ
    apply NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_injective (w := w') hw'
    rw [← hσ,
      NK.NUV2.ARL.HR.localUnitsEquiv_localCoeff (K := k) (M := K) (E := L) w w' hw' σ u,
      hu]
    have h : (NK.HassePrinciple.localUnitsRep k L w').ρ σ (Additive.ofMul a₀)
        = Additive.ofMul a₀ :=
      ((congrArg (fun z => (NK.HassePrinciple.localUnitsRep k L w').ρ σ z) hof).trans
        (hafix σ)).trans hof.symm
    exact Additive.ofMul.injective h
  · -- the non-norm property transports verbatim
    rintro ⟨bb, hbbN, hsum⟩
    exact hnot ⟨bb, hbbN, by rw [hsum, hu, hof]⟩

end Work.SSGRoute
