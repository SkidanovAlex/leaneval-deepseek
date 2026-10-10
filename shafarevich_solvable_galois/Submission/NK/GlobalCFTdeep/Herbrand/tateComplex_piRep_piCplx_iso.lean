import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.TateCohomology.Basic
import Submission.NK.GlobalCFTdeep.Herbrand.PiCplxDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace NK.GlobalCFTdeep.Herbrand

open CategoryTheory CategoryTheory.Limits
open NK.RepresentationTheory.GroupCohomology (piRep piRepEval piRepEval_hom_apply)

noncomputable section

variable {R : Type} [CommRing R] {G : Type} [Group G] [Fintype G] {ι : Type}

/-! ## The degreewise currying equivalences -/

/-- In nonnegative degrees the Tate complex of `piRep M` is made of inhomogeneous cochains, and
the identification with the product of the Tate complexes of the factors is currying:
`(Fin k → G) → (∀ i, M i)` is `∀ i, (Fin k → G) → M i`. -/
noncomputable def piRepPosEquiv (M : ι → Rep.{0,0,0} R G) (k : ℕ) :
    ↥((tateComplex (piRep M)).X (k : ℤ)) ≃ₗ[R]
      ↥((piCplx R (fun i => tateComplex (M i))).X (k : ℤ)) where
  toFun x := fun i g => x g i
  invFun y := fun g i => y i g
  map_add' x y := by funext i g; rfl
  map_smul' r x := by funext i g; rfl
  left_inv x := by funext g i; rfl
  right_inv y := by funext i g; rfl

/-- In degrees `-(k+1)` the Tate complex of `piRep M` is made of inhomogeneous chains, i.e. of
finitely supported functions into `∀ i, M i`; since `Fin k → G` is finite, this is the product of
the finitely supported functions into the `M i`.  This is `finsuppPiEquiv` from `PiCplxDefs`,
seen as an equivalence between the corresponding terms of the two Tate complexes. -/
noncomputable def piRepNegEquiv (M : ι → Rep.{0,0,0} R G) (k : ℕ) :
    ↥((tateComplex (piRep M)).X (Int.negSucc k)) ≃ₗ[R]
      ↥((piCplx R (fun i => tateComplex (M i))).X (Int.negSucc k)) :=
  finsuppPiEquiv R (Fin k → G) (M := fun i => ↥(M i))

/-- The `i`-th component of `finsuppPiEquiv`, in the shape needed below. -/
lemma finsuppPiEquiv_piRep_apply (M : ι → Rep.{0,0,0} R G) (k : ℕ)
    (x : (Fin k → G) →₀ ((i : ι) → ↥(M i))) (i : ι) :
    ((finsuppPiEquiv R (Fin k → G) (M := fun i => ↥(M i)) x) i : (Fin k → G) →₀ ↥(M i))
      = Finsupp.mapRange.linearMap (LinearMap.proj (R := R) i) x := by
  ext a
  simp only [finsuppPiEquiv_apply, Finsupp.mapRange.linearMap_apply]
  rfl

/-- The `i`-th component of `piRepNegEquiv`. -/
lemma piRepNegEquiv_apply (M : ι → Rep.{0,0,0} R G) (k : ℕ)
    (x : (Fin k → G) →₀ ((i : ι) → ↥(M i))) (i : ι) :
    ((piRepNegEquiv M k x) i : (Fin k → G) →₀ ↥(M i))
      = Finsupp.mapRange.linearMap (LinearMap.proj (R := R) i) x := by
  change ((finsuppPiEquiv R (Fin k → G) (M := fun i => ↥(M i)) x) i : (Fin k → G) →₀ ↥(M i)) = _
  exact finsuppPiEquiv_piRep_apply M k x i

/-! ## The isomorphism, built from the evaluation maps -/

/-- The evaluation maps `piRepEval M i : piRep M ⟶ M i` induce, by functoriality of the Tate
complex, a morphism `tateComplex (piRep M) ⟶ piCplx R (fun i => tateComplex (M i))`; in degree `n`
it is the product `LinearMap.pi` of the maps `tateComplex.map (piRepEval M i)`.

This is a morphism of complexes *because each evaluation map is*: the differential of `piCplx` is
componentwise, so the commutation square is exactly the commutation square of the chain map
`tateComplex.map (piRepEval M i)`, for each `i`. -/
noncomputable def tateComplexPiRepHom (M : ι → Rep.{0,0,0} R G) :
    tateComplex (piRep M) ⟶ piCplx R (fun i => tateComplex (M i)) where
  f n := ModuleCat.ofHom
    (LinearMap.pi (fun i => (ConcreteCategory.hom ((tateComplex.map (piRepEval M i)).f n))))
  comm' n m hnm := by
    apply ModuleCat.hom_ext
    ext x
    funext i
    have h := congrArg
      (fun (g : (tateComplex (piRep M)).X n ⟶ (tateComplex (M i)).X m) =>
        (ConcreteCategory.hom g) x)
      (HomologicalComplex.Hom.comm' (tateComplex.map (piRepEval M i)) n m hnm)
    simp only [CategoryStruct.comp, piCplx_d] at h ⊢
    exact h

set_option backward.isDefEq.respectTransparency false in
/-- In nonnegative degree `k`, the evaluation at `i` of the Tate complex of `piRep M` is evaluation
at `i` of the inhomogeneous `k`-cochains. -/
lemma tateComplex_map_piRepEval_ofNat (M : ι → Rep.{0,0,0} R G) (k : ℕ) (i : ι)
    (x : ↥((tateComplex (piRep M)).X (k : ℤ))) (g : Fin k → G) :
    ((ConcreteCategory.hom ((tateComplex.map (piRepEval M i)).f (k : ℤ))) x) g = x g i := by
  simp only [tateComplex.map, CochainComplex.ConnectData.map_f]
  rw [groupCohomology.cochainsMap_f]
  simp only [ModuleCat.comp_apply, ModuleCat.hom_ofHom, LinearMap.compLeft_apply,
    LinearMap.funLeft_apply, piRepEval_hom_apply]
  rfl

/-- In degree `-(k+1)` (inhomogeneous `k`-chains), the evaluation at `i` of the Tate complex of
`piRep M` is the `i`-th component of the finitely supported function. -/
lemma tateComplex_map_piRepEval_negSucc (M : ι → Rep.{0,0,0} R G) (k : ℕ) (i : ι)
    (x : ↥((tateComplex (piRep M)).X (Int.negSucc k))) :
    ((ConcreteCategory.hom ((tateComplex.map (piRepEval M i)).f (Int.negSucc k))) x)
      = (Finsupp.mapRange.linearMap (LinearMap.proj (R := R) i)) x := by
  simp only [tateComplex.map, CochainComplex.ConnectData.map_f]
  change (ModuleCat.Hom.hom
    ((groupHomology.chainsMap (MonoidHom.id G) (piRepEval M i)).f k)) x = _
  rw [groupHomology.chainsMap_id_f_hom_eq_mapRange]
  rfl

/-- The degreewise identification of `tateComplexPiRepHom` in nonnegative degrees. -/
lemma tateComplexPiRepHom_f_ofNat (M : ι → Rep.{0,0,0} R G) (k : ℕ) :
    (ConcreteCategory.hom ((tateComplexPiRepHom M).f (k : ℤ)))
      = (piRepPosEquiv M k).toLinearMap := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [tateComplexPiRepHom, LinearMap.pi_apply]
  funext g
  exact tateComplex_map_piRepEval_ofNat M k i x g

/-- The degreewise identification of `tateComplexPiRepHom` in degrees `-(k+1)`. -/
lemma tateComplexPiRepHom_f_negSucc (M : ι → Rep.{0,0,0} R G) (k : ℕ) :
    (ConcreteCategory.hom ((tateComplexPiRepHom M).f (Int.negSucc k)))
      = (piRepNegEquiv M k).toLinearMap := by
  apply LinearMap.ext
  intro x
  funext i
  simp only [tateComplexPiRepHom, LinearMap.pi_apply]
  change (ConcreteCategory.hom ((tateComplex.map (piRepEval M i)).f (Int.negSucc k))) x
      = (finsuppPiEquiv R (Fin k → G) (M := fun i => ↥(M i)) x) i
  rw [tateComplex_map_piRepEval_negSucc]
  exact (finsuppPiEquiv_piRep_apply M k x i).symm

/-- **The Tate complex of a pointwise product representation is the pointwise product of the Tate
complexes of its factors.**  The isomorphism is induced by the evaluation maps
`piRep M ⟶ M i`, and is degreewise the currying identification. -/
theorem tateComplex_piRep_piCplx_iso {R : Type} [CommRing R] {G : Type} [Group G] [Fintype G] {ι : Type}
    (M : ι → Rep.{0,0,0} R G) :
    Nonempty (tateComplex (NK.RepresentationTheory.GroupCohomology.piRep M) ≅
      piCplx R (fun i => tateComplex (M i))) := by
  classical
  haveI (n : ℤ) : IsIso ((tateComplexPiRepHom M).f n) := by
    rcases n with k | k
    · change IsIso ((tateComplexPiRepHom M).f ((k : ℤ)))
      rw [ConcreteCategory.isIso_iff_bijective, tateComplexPiRepHom_f_ofNat]
      exact (piRepPosEquiv M k).bijective
    · rw [ConcreteCategory.isIso_iff_bijective, tateComplexPiRepHom_f_negSucc]
      exact (piRepNegEquiv M k).bijective
  haveI : IsIso (tateComplexPiRepHom M) :=
    HomologicalComplex.Hom.isIso_of_components (tateComplexPiRepHom M)
  exact ⟨asIso (tateComplexPiRepHom M)⟩

end

end NK.GlobalCFTdeep.Herbrand
