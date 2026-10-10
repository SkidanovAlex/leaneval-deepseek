import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Submission.NK.CFTLib.HR.TransferAux.towerAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The local units of the middle field are the kernel-invariants of the top field

Tower `F ⊆ L ⊆ M` of number fields, places `w` of `L` and `w'` of `M` above it.  With
`S = ker (localStabilizerMapTower h) ≤ Γ_{w'}` the image of the relative decomposition group
`Gal(M/L)_{w'}`, the local algebra map `localUnitsMapTowerCoeff h : L_wˣ →* M_{w'}ˣ` has image
exactly the `S`-invariants of `M_{w'}ˣ`:

* `unitsMapTowerCoeff_mem_invariants`: the image consists of invariants (the tower equivariance);
* `unitsMapTowerCoeff_surj_invariants`: every invariant is in the image (Galois descent for the
  local extension `M_{w'}/L_w`, via `NK.GlobalCFT.Inclusion.globalCFT_localFixed_mem_range`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open CategoryTheory

namespace NK.CFTLib.HR.TransferAux

variable {F L M : Type} [Field F] [NumberField F] [Field L] [NumberField L]
  [Field M] [NumberField M] [Algebra F L] [Algebra F M] [Algebra L M] [IsScalarTower F L M]
  [FiniteDimensional F L] [IsGalois F L] [FiniteDimensional F M] [IsGalois F M]
  {w : NK.GlobalCFT.Place L} {w' : NK.GlobalCFT.Place M}

/-- **The tower coefficient map lands in the invariants of the kernel of the tower map.** -/
theorem unitsMapTowerCoeff_mem_invariants (h : NK.GlobalCFT.Place.LiesOver w' w)
    (σ : (NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker)
    (u : (NK.GlobalCFT.Place.localField L w)ˣ) :
    (NK.HassePrinciple.localUnitsRep F M w').ρ σ
        ((NK.NUV2.LC.RouteB.localUnitsMapTowerCoeff (F := F) (L := L) (M := M) h).hom
          (Additive.ofMul u))
      = (NK.NUV2.LC.RouteB.localUnitsMapTowerCoeff (F := F) (L := L) (M := M) h).hom
          (Additive.ofMul u) := by
  have hmul : NK.HassePrinciple.localUnitsEquiv (K := F) w' σ.1
        (NK.GlobalCFT.Place.localAlgebraMapUnits w' w h u)
      = NK.GlobalCFT.Place.localAlgebraMapUnits w' w h u := by
    rw [← NK.NUV2.LC.RouteB.localUnitsEquiv_localAlgebraMapUnits_tower
      (F := F) (L := L) (M := M) h σ.1 u, MonoidHom.mem_ker.mp σ.2]
    exact congrArg (NK.GlobalCFT.Place.localAlgebraMapUnits w' w h)
      (congrArg (fun e : (NK.GlobalCFT.Place.localField L w)ˣ ≃*
        (NK.GlobalCFT.Place.localField L w)ˣ => e u)
      (NK.HassePrinciple.localUnitsEquiv_one (K := F) (L := L) w))
  show Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := F) w' σ.1
      (NK.GlobalCFT.Place.localAlgebraMapUnits w' w h u))
    = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w h u)
  rw [hmul]

/-- **Every unit of `M_{w'}` fixed by the kernel of the tower map comes from `L_w`.**

Galois descent for the local field extension `M_{w'}/L_w`: the kernel of
`localStabilizerMapTower h` is (the image of) the relative decomposition group `Gal(M/L)_{w'}`, so
its fixed units are the units of the fixed field `L_w`. -/
theorem unitsMapTowerCoeff_surj_invariants [FiniteDimensional L M] [IsGalois L M]
    (h : NK.GlobalCFT.Place.LiesOver w' w)
    (x : (NK.HassePrinciple.localUnitsRep F M w').V)
    (hx : ∀ σ : (NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker,
        (NK.HassePrinciple.localUnitsRep F M w').ρ σ x = x) :
    ∃ u : (NK.GlobalCFT.Place.localField L w)ˣ,
      (NK.NUV2.LC.RouteB.localUnitsMapTowerCoeff (F := F) (L := L) (M := M) h).hom
        (Additive.ofMul u) = x := by
  classical
  let y : Additive (NK.GlobalCFT.Place.localField M w')ˣ := x
  set u : (NK.GlobalCFT.Place.localField M w')ˣ :=
    Additive.toMul (α := (NK.GlobalCFT.Place.localField M w')ˣ) x with hu
  have hy : y = Additive.ofMul u := by
    rw [hu]
    exact (ofMul_toMul x).symm
  have hx' : ∀ s : ↥(MulAction.stabilizer Gal(M/F) w'),
      s ∈ (NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker →
      NK.HassePrinciple.localUnitsEquiv (K := F) w' s u = u := by
    intro s hs
    have h1 : (NK.HassePrinciple.localUnitsRep F M w').ρ (⟨s, hs⟩ :
        ↥((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker)) x = x :=
      hx ⟨s, hs⟩
    have h1' : (NK.HassePrinciple.localUnitsRep F M w').ρ (⟨s, hs⟩ :
        ↥((NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker))
        (Additive.ofMul u) = Additive.ofMul u := by
      rw [← hy]
      exact h1
    exact Additive.ofMul.injective h1'
  have hfixed : ∃ a : (NK.GlobalCFT.Place.localField L w)ˣ,
      NK.GlobalCFT.Place.localAlgebraMapUnits w' w h a = u := by
    refine NK.GlobalCFT.Inclusion.globalCFT_localFixed_mem_range (K := L) (L := M)
      (w := w') (v := w) h u ?_
    intro σ hσ
    -- an `L`-automorphism of `M` fixing `w'` is, as an `F`-automorphism, in the kernel
    have hσ' : (AlgEquiv.restrictScalars F σ) • w' = w' := by
      rw [TowerAux.restrictScalars_smul_place (F := F)]
      exact hσ
    let s : ↥(MulAction.stabilizer Gal(M/F) w') :=
      ⟨AlgEquiv.restrictScalars F σ, MulAction.mem_stabilizer_iff.mpr hσ'⟩
    have hs : s ∈ (NK.NUV2.LC.RouteB.localStabilizerMapTower (F := F) (L := L) (M := M) h).ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show (AlgEquiv.restrictNormalHom (K₁ := M) (E := L)) (AlgEquiv.restrictScalars F σ) = 1
      exact TowerAux.restrictNormal_restrictScalars_eq_one (F := F) σ
    have hu_s : NK.HassePrinciple.localUnitsEquiv (K := F) w' s u = u := hx' s hs
    have h1 : ((NK.HassePrinciple.localUnitsEquiv (K := F) w' s u :
        (NK.GlobalCFT.Place.localField M w')ˣ) :
          NK.GlobalCFT.Place.localField M w') = (u : NK.GlobalCFT.Place.localField M w') :=
      congrArg Units.val hu_s
    rw [NK.HassePrinciple.coe_localUnitsEquiv] at h1
    rw [show NK.HassePrinciple.localAutHom (K := F) (L := M) w' s
        = NK.HassePrinciple.localAut (K := F) (L := M) w' s from rfl] at h1
    rw [NK.HassePrinciple.localAut_apply, NK.HassePrinciple.ringEquiv_cast_apply_eq] at h1
    have hA_eq : (MulAction.mem_stabilizer_iff.mp s.2) = hσ := Subsingleton.elim _ _
    rw [hA_eq] at h1
    have h2 : NK.GlobalCFT.Place.localRingEquiv σ w'
        (u : NK.GlobalCFT.Place.localField M w')
        = hσ.symm ▸ (u : NK.GlobalCFT.Place.localField M w') :=
      (NK.HassePrinciple.eqRec_symm_eqRec hσ
        ((NK.GlobalCFT.Place.localRingEquiv (↑s : Gal(M/F)) w')
          (u : NK.GlobalCFT.Place.localField M w'))).symm.trans
        (congrArg (fun z => hσ.symm ▸ z) h1)
    apply Units.ext
    simp only [Units.coe_map, NK.HassePrinciple.units_val_cast]
    exact h2
  obtain ⟨a, ha⟩ := hfixed
  refine ⟨a, ?_⟩
  rw [NK.NUV2.LC.RouteB.localUnitsMapTowerCoeff_ofMul, ha]
  exact hy.symm

end NK.CFTLib.HR.TransferAux
