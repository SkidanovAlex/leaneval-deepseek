import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Submission.Work.SSGRoute.PT.resH2_eq_zero_of_index_nsmul_eq_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction kills the index-torsion of `H²(G_F, μ_n)`

`Work.SSGRoute.PT.local_resH2_mu_eq_zero`: for a number field `K`, a finite place `Q` and the
`Q`-adic completion `F = K_Q` with absolute Galois group `G = Gal(F̄/F)`, every class
`x ∈ H²(G, μ_n)` annihilated by the index `[G : U']` of an open finite-index subgroup `U' ≤ G`
restricts to zero on `U'`.

The proof reduces to the corresponding statement with coefficients `F̄ˣ`
(`Work.SSGRoute.PT.local_resH2_eq_zero_of_index_nsmul_eq_zero`) along the coefficient map
`μ_n ↪ F̄ˣ` of the Kummer sequence `1 → μ_n → F̄ˣ →^n F̄ˣ → 1`:

* restriction is natural in the coefficient module (`resH2_mapH2`);
* push-forward along `kummerIota` commutes with the scalar action, so the pushed-forward class is
  still annihilated by the index;
* the coefficient map `H²(U', μ_n) → H²(U', F̄ˣ)` is injective because `H¹(U', F̄ˣ) = 0`
  (Hilbert 90 at the open subgroup `U'`,
  `Work.SSGRoute.PT.hilbert90_H1_eq_zero_openSubgroup`) and the Kummer sequence is exact
  (`Work.AbsoluteKummer.SES.range_deltaH2_eq_ker_mapH2`).
-/

namespace Work.SSGRoute.PT

open Work.AbsoluteKummer

noncomputable section

set_option linter.style.haveILetI false

variable {Γ : Type*} [TopologicalSpace Γ] [Group Γ]

/-! ## Restriction is natural in the coefficient module -/

/-- **Naturality of the restriction `H²(G,A) → H²(U,A)` in the coefficient module**, at the level
of the *continuous* cohomology `Work.AbsoluteKummer.H2`.  For a subgroup `U ≤ G` and a
`G`-equivariant additive map `f : A →+ B` the square with the coefficient maps `H²(−, f)` commutes.

The proof is the pointwise cochain identity `resZ2 U (mapZ2 f hf c) = mapZ2 f hf' (resZ2 U c)`,
transported through `H2π` and `mapH2_H2π`/`resH2_H2π`. -/
theorem resH2_mapH2 {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction Γ A] [DistribMulAction Γ B] (U : Subgroup Γ)
    (f : A →+ B) (hf : Work.GroupCohomology.IsEquivariant Γ f) (x : H2 Γ A) :
    Work.SSGRoute.PT.resH2 U (mapH2 f hf x)
      = mapH2 (G := ↥U) f (fun u a => hf (u : Γ) a) (Work.SSGRoute.PT.resH2 U x) := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((B2 Γ A).comap (Z2 Γ A).subtype) x
  rw [show x = H2π Γ A c from hc.symm]
  rw [mapH2_H2π (G := Γ) f hf c]
  rw [Work.SSGRoute.PT.resH2_H2π U (mapZ2 f hf c)]
  rw [Work.SSGRoute.PT.resH2_H2π U c]
  rw [mapH2_H2π (G := ↥U) f (fun u a => hf (u : Γ) a) (Work.SSGRoute.PT.resZ2 U c)]
  exact congrArg (H2π ↥U B) (by ext p; rfl)

/-! ## Discreteness of the action restricts to a subgroup -/

/-- The continuity condition `IsDiscreteModule` on the action of `G` restricts to any subgroup. -/
theorem isDiscreteModule_subgroup {M : Type*} [AddCommGroup M] [DistribMulAction Γ M]
    (h : IsDiscreteModule Γ M) (U : Subgroup Γ) : IsDiscreteModule ↥U M := by
  intro m
  show IsOpen (MulAction.stabilizer ↥U m : Set ↥U)
  have hG : IsOpen (MulAction.stabilizer Γ m : Set Γ) := h m
  have hset : (MulAction.stabilizer ↥U m : Set ↥U) =
      Subtype.val ⁻¹' (MulAction.stabilizer Γ m : Set Γ) := by
    ext u
    simp only [Set.mem_preimage, SetLike.mem_coe, MulAction.mem_stabilizer_iff,
      Subgroup.smul_def]
  rw [hset]
  exact hG.preimage continuous_subtype_val

/-! ## The Kummer injection at an open subgroup -/

/-- **The Kummer injection `H²(U, μ_n) ↪ H²(U, F̄ˣ)` at an open subgroup.**

For a field `F` of characteristic zero, `n ≠ 0` and an open subgroup `U ≤ Gal(F̄/F)`, the map
induced on `H²` by the inclusion `μ_n(F̄) ↪ F̄ˣ` of the Kummer sequence is injective.

Indeed, `Work.AbsoluteKummer.SES.range_deltaH2_eq_ker_mapH2` identifies its kernel with the image
of the connecting map `δ : H¹(U, F̄ˣ) → H²(U, μ_n)`, and `δ = 0` because `H¹(U, F̄ˣ) = 0`
(Hilbert 90 at the open subgroup `U`, `Work.SSGRoute.PT.hilbert90_H1_eq_zero_openSubgroup`). -/
theorem kummerIota_mapH2_injective_openSubgroup (F : Type) [Field F] [CharZero F]
    (n : ℕ) [NeZero n] (U : Subgroup (G F)) (hU : IsOpen (U : Set (G F))) :
    Function.Injective (mapH2 (G := ↥U) (Kummer.kummerIota (k := F) n)
      (fun u a => Kummer.kummerIota_equivariant (k := F) n (u : G F) a)) := by
  haveI : IsGalois F (AlgebraicClosure F) := IsAlgClosure.isGalois F _
  have hMn : IsDiscreteModule ↥U (Additive (rootsOfUnity n (AlgebraicClosure F))) :=
    isDiscreteModule_subgroup (isDiscreteModule_addRootsOfUnity F n) U
  have hNu : IsDiscreteModule ↥U (Additive (AlgebraicClosure F)ˣ) :=
    isDiscreteModule_subgroup (isDiscreteModule_addUnits F) U
  let S : ShortExactSeq ↥U (Additive (rootsOfUnity n (AlgebraicClosure F)))
      (Additive (AlgebraicClosure F)ˣ) (Additive (AlgebraicClosure F)ˣ) :=
    { iota := Kummer.kummerIota (k := F) n
      pi := Kummer.kummerPi (k := F) n
      iota_equivariant := fun u a => Kummer.kummerIota_equivariant (k := F) n (u : G F) a
      pi_equivariant := fun u a => Kummer.kummerPi_equivariant (k := F) n (u : G F) a
      iota_injective := Kummer.kummerIota_injective (k := F) n
      pi_surjective := Kummer.kummerPi_surjective (k := F) n
      range_iota_eq_ker_pi := Kummer.kummerIota_range_eq_ker_pi (k := F) n
      isDiscreteM := hMn
      isDiscreteN := hNu
      isDiscreteP := hNu }
  have hsub : Subsingleton (H1 ↥U (Additive (AlgebraicClosure F)ˣ)) :=
    hilbert90_H1_eq_zero_openSubgroup (k := F) (Ω := AlgebraicClosure F) U hU
  have hker : (mapH2 S.iota S.iota_equivariant).ker = ⊥ := by
    rw [← Work.AbsoluteKummer.SES.range_deltaH2_eq_ker_mapH2 S]
    refine le_antisymm (fun y hy => ?_) bot_le
    rw [AddMonoidHom.mem_range] at hy
    obtain ⟨z, rfl⟩ := hy
    rw [show z = 0 from Subsingleton.elim z 0, map_zero]
    simp
  have hmaps : (mapH2 (G := ↥U) (Kummer.kummerIota (k := F) n)
      (fun u a => Kummer.kummerIota_equivariant (k := F) n (u : G F) a))
      = (mapH2 S.iota S.iota_equivariant) := rfl
  rw [hmaps]
  exact (AddMonoidHom.ker_eq_bot_iff _).mp hker

/-! ## The target -/

theorem local_resH2_mu_eq_zero {K : Type} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) (n : ℕ) [NeZero n]
    (U' : Subgroup (Work.AbsoluteKummer.G (Q.adicCompletion K)))
    (hU' : IsOpen (U' : Set (Work.AbsoluteKummer.G (Q.adicCompletion K))))
    [U'.FiniteIndex] [Fintype (Work.AbsoluteKummer.G (Q.adicCompletion K) ⧸ U')]
    (x : Work.AbsoluteKummer.H2 (Work.AbsoluteKummer.G (Q.adicCompletion K))
        (Additive (rootsOfUnity n (AlgebraicClosure (Q.adicCompletion K))))) :
    Nat.card (Work.AbsoluteKummer.G (Q.adicCompletion K) ⧸ U') • x = 0 →
      Work.SSGRoute.PT.resH2 U' x = 0 := by
  intro hx
  haveI hcz : CharZero (Q.adicCompletion K) :=
    Commons.NumberTheory.NumberField.charZero_adicCompletion Q
  haveI hgal : IsGalois (Q.adicCompletion K) (AlgebraicClosure (Q.adicCompletion K)) :=
    IsAlgClosure.isGalois _ _
  have hinj := kummerIota_mapH2_injective_openSubgroup (Q.adicCompletion K) n U' hU'
  -- push `x` forward along `μ_n ↪ F̄ˣ`; the pushed class is still killed by the index
  have hmap : Nat.card (Work.AbsoluteKummer.G (Q.adicCompletion K) ⧸ U') •
      (mapH2 (Kummer.kummerIota (k := Q.adicCompletion K) n)
        (Kummer.kummerIota_equivariant (k := Q.adicCompletion K) n) x) = 0 := by
    rw [← map_nsmul, hx, map_zero]
  -- the `F̄ˣ`-coefficient statement at the local field
  have hres := local_resH2_eq_zero_of_index_nsmul_eq_zero (K := K) Q
    (mapH2 (Kummer.kummerIota (k := Q.adicCompletion K) n)
      (Kummer.kummerIota_equivariant (k := Q.adicCompletion K) n) x) U' hU' hmap
  -- naturality of the restriction identifies the result with the push-forward of `resH2 U' x`
  rw [resH2_mapH2] at hres
  exact hinj (by rw [hres, map_zero])

end

end Work.SSGRoute.PT
