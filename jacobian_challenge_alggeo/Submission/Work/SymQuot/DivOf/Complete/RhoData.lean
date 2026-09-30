/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The universal `n`-tuple of `Q`-points and the map `ρ : Γ(Cⁿ,Vⁿ) → Q^{⊗n}` (area SY)

For the construction of the point `p_D` of `Symⁿ C` attached to an effective divisor `D` of
degree `n` (`Submission/Work/NOTES_LEAD_jacobian_divof.md` §5, `Submission/Work/SymQuot/NOTES.md`
§3), one needs

* `κ_m : Γ(C,V) →ₐ[K] Q^{⊗n}`, `b ↦ 1 ⊗ … ⊗ (b mod I) ⊗ … ⊗ 1` (`kappa`), where
  `Q = Γ(C_F,V_F) ⧸ I` is the quotient of the affine ring of the base-changed curve by the ideal
  `I = idealOfDiv` of the divisor;
* the induced morphism `Spec (Q^{⊗n}) ⟶ Vⁿ ⊆ Cⁿ`, and the pullback
  `ρ := evalAlg C V n (fun m => ptOfAlgHom C hV (kappa m)) : Γ(Cⁿ,Vⁿ) →+* Q^{⊗n}`
  (`rho`), which maps the `S_n`-invariants into the symmetric tensors
  (`rho_mem_symTensors`);
* the `F`-valued "norm point" `φ_D := normPoint v ∘ ρ|_A : Γ(Cⁿ,Vⁿ)^{S_n} →+* F` (`phiD`).

All of these are pure definitions built from the already existing `ptOfAlgHom`, `evalAlg` and
the norm-point algebra of `Work.SymQuot.NormPoint`.
-/
import Mathlib
import Submission.Work.SymQuot.DivOf.Complete.Setup
import Submission.Work.SymQuot.DivOf.Complete.PtOfChartHom
import Submission.Work.SymQuot.DivOf.Complete.evalAlg_comp
import Submission.Work.SymQuot.DivOf.Complete.evalAlg_perm_of_mem
import Submission.Work.SymQuot.DivOf.Complete.evalAlg_coordPullbackAt
import Submission.Work.SymQuot.DivOf.Complete.RPt_map_ptOfAlgHom
import Submission.Work.SymQuot.DivOf.Complete.ptOfAlgHom_mem
import Submission.Work.SymQuot.DivOf.exists_good_chartSection_infiniteK
import Submission.Work.SymQuot.NormPoint.NormPoint
import Submission.Work.SymQuot.NormPoint.bcT_mem_symTensors
import Submission.Work.SymQuot.NormPoint.normVal_bcT
import Submission.Work.SymQuot.NormPoint.normVal_basis_indep
import Submission.Work.SymQuot.NormPoint.normVal_eq_evalT
import Submission.Work.SymQuot.NormPoint.detT_mul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical
open TensorProduct
open scoped TensorProduct

universe u

namespace Work.SymQuot.DivOf.Complete

open Work.CurveBasics Work.SymQuot.NormPoint

variable {K : Type u} [Field K] {C : Curve K} {n : ℕ} [NeZero n]
  [Work.SymQuot.CurveAffineCover C]

/-! ### The single-factor embedding of the tensor power -/

/-- `tensSingle m q = 1 ⊗ … ⊗ q ⊗ … ⊗ 1` in the `n`-fold tensor power of `Q` over `F`. -/
noncomputable def tensSingle (F Q : Type u) [Field F] [CommRing Q] [Algebra F Q] (n : ℕ)
    (m : Fin n) : Q →ₐ[F] Tens F Q n :=
  PiTensorProduct.singleAlgHom (R := F) (A := fun _ : Fin n => Q) m

theorem tensSingle_apply (F Q : Type u) [Field F] [CommRing Q] [Algebra F Q] (n : ℕ)
    (m : Fin n) (q : Q) :
    tensSingle F Q n m q = PiTensorProduct.tprod F (fun j => if j = m then q else 1) := by
  rw [tensSingle, PiTensorProduct.singleAlgHom_apply]
  congr 1
  funext j
  rw [MonoidHom.mulSingle_apply, Pi.mulSingle_apply]

/-- The permutation of the tensor factors acts on the single-factor embedding by reindexing. -/
theorem permAlg_tensSingle {F Q : Type u} [Field F] [CommRing Q] [Algebra F Q] {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (m : Fin n) (q : Q) :
    permAlg (Q := Q) σ (tensSingle F Q n m q) = tensSingle F Q n (σ m) q := by
  rw [tensSingle_apply, permAlg_tprod, tensSingle_apply]
  congr 1
  funext i
  by_cases h : σ.symm i = m
  · rw [if_pos h, if_pos (by rw [← h, Equiv.apply_symm_apply])]
  · rw [if_neg h, if_neg (fun hh => h (by rw [hh, Equiv.symm_apply_apply]))]

/-! ### The maps `κ_m : Γ(C,V) →ₐ[K] Q^{⊗n}` -/

variable {F : Type u} [Field F] [Algebra K F]

/-- `secConst` is the structure-map `F`-algebra structure on the base-changed sections. -/
theorem secConst_eq_algebraMap (V : C.left.Opens) :
    secConst C F V = algebraMap F Γ((C.baseChange F).left, C.bcOpens F V) := by
  rw [secConst]
  ext a
  rfl

/-- **The `m`-th coordinate of the universal `n`-tuple**: the `K`-algebra homomorphism
`Γ(C,V) →ₐ[K] Q^{⊗n}`, `b ↦ 1 ⊗ … ⊗ (b mod I) ⊗ … ⊗ 1`, where `Q = Γ(C_F,V_F) ⧸ I`. -/
noncomputable def kappa (V : C.left.Opens) (hV : IsAffineOpen V)
    (I : Ideal Γ((C.baseChange F).left, C.bcOpens F V)) (m : Fin n) :
    Γ(C.left, V) →ₐ[K] Tens F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n :=
  AlgHom.mk'
    ((tensSingle F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n m).toRingHom.comp
      ((Ideal.Quotient.mk I).comp (secAlpha C F V)))
    (by
      intro c b
      show (tensSingle F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n m)
          (Ideal.Quotient.mk I (secAlpha C F V (c • b))) =
        c • (tensSingle F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n m)
          (Ideal.Quotient.mk I (secAlpha C F V b))
      rw [show c • b = algebraMap K Γ(C.left, V) c * b from Algebra.smul_def c b]
      rw [show secAlpha C F V (algebraMap K Γ(C.left, V) c * b) =
          secAlpha C F V (algebraMap K Γ(C.left, V) c) * secAlpha C F V b from
        map_mul (secAlpha C F V) _ _]
      rw [show Ideal.Quotient.mk I (secAlpha C F V (algebraMap K Γ(C.left, V) c) *
            secAlpha C F V b) =
          Ideal.Quotient.mk I (secAlpha C F V (algebraMap K Γ(C.left, V) c)) *
            Ideal.Quotient.mk I (secAlpha C F V b) from map_mul (Ideal.Quotient.mk I) _ _]
      rw [show (tensSingle F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n m)
            (Ideal.Quotient.mk I (secAlpha C F V (algebraMap K Γ(C.left, V) c)) *
              Ideal.Quotient.mk I (secAlpha C F V b)) =
          (tensSingle F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n m)
              (Ideal.Quotient.mk I (secAlpha C F V (algebraMap K Γ(C.left, V) c))) *
            (tensSingle F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n m)
              (Ideal.Quotient.mk I (secAlpha C F V b)) from
        map_mul (tensSingle F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n m) _ _]
      have h2 : Ideal.Quotient.mk I (secConst C F V (algebraMap K F c)) =
          algebraMap F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) (algebraMap K F c) := by
        rw [secConst_eq_algebraMap, Ideal.Quotient.mk_algebraMap]
      rw [secAlpha_algebraMap F V hV c, h2, AlgHom.commutes]
      rw [show c • (tensSingle F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n m)
            (Ideal.Quotient.mk I (secAlpha C F V b)) =
          algebraMap K (Tens F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n) c *
            (tensSingle F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n m)
              (Ideal.Quotient.mk I (secAlpha C F V b)) from Algebra.smul_def c _]
      rw [IsScalarTower.algebraMap_apply K F
        (Tens F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n) c])

/-- **The ideal of definition of an effective divisor**, as an ideal of the affine ring of the
base-changed open `V_F`; the instances are pinned down so that the same expression can be used
throughout. -/
noncomputable def divIdeal (V : C.left.Opens) [Nonempty V] (hV : IsAffineOpen V)
    (D : Work.SpecLin.Dv C F) (hsupp : ∀ z ∈ D.support, z.point ∈ C.bcOpens F V) :
    Ideal Γ((C.baseChange F).left, C.bcOpens F V) :=
  @idealOfDiv F _ (C.baseChange F) (C.bcOpens F V) (Curve.bcOpens_nonempty C F V)
    (BaseChange.isAffineOpen_bcOpens F V hV)
    (isDedekindDomain_sections (C := C.baseChange F)
      (BaseChange.isAffineOpen_bcOpens F V hV)) D hsupp

/-! ### The universal `n`-tuple of `Q`-points and `ρ` -/

/-- **The pullback of `Vⁿ` along a tuple of points is top as soon as each point lands in `V`.** -/
theorem piOpen_landsIn {S : Type u} [CommRing S] [Algebra K S]
    {V : C.left.Opens} (x : Fin n → Work.SpecLin.RPt C.toOver S)
    (hx : ∀ m, ⊤ ≤ (x m).left ⁻¹ᵁ V) :
    ⊤ ≤ (Limits.Pi.lift x : Work.SpecLin.specOf (K := K) S ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n := by
  intro z _
  show (Limits.Pi.lift x).left z ∈ Work.SymQuot.piOpen C.toOver V n
  rw [Work.SymQuot.mem_piOpen]
  intro m
  have hcomp : (Limits.Pi.lift x).left ≫ (Work.SymQuot.proj C.toOver n m).left =
      (x m).left :=
    congrArg (fun t : Work.SpecLin.specOf (K := K) S ⟶ C.toOver => t.left)
      (Limits.Pi.lift_comp_π x m)
  have hzm : (Work.SymQuot.proj C.toOver n m).left ((Limits.Pi.lift x).left z) =
      (x m).left z := by rw [← hcomp]; rfl
  rw [hzm]
  exact hx m trivial

/-- **The map `ρ : Γ(Cⁿ,Vⁿ) →+* Q^{⊗n}`**: the evaluation of a regular function on `Vⁿ` at the
universal `n`-tuple of `Q`-points given by `κ`. -/
noncomputable def rho (V : C.left.Opens) (hV : IsAffineOpen V)
    (I : Ideal Γ((C.baseChange F).left, C.bcOpens F V)) :
    Γ((Work.SymQuot.prod C.toOver n).left, Work.SymQuot.piOpen C.toOver V n) →+*
      Tens F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n :=
  evalAlg C V n (fun m => ptOfAlgHom C hV (kappa (C := C) (F := F) (n := n) V hV I m))
    (piOpen_landsIn (C := C) (n := n) _
      (fun m => ptOfAlgHom_mem (C := C) (V := V) hV (kappa (C := C) (F := F) (n := n) V hV I m)))

/-! ### `ρ` maps the invariants into the symmetric tensors -/

/-- `permAlg σ` as a `K`-algebra automorphism of the tensor power (it is `F`-linear, and the
`K`-structure goes through `F`). -/
noncomputable def permAlgAlgHom {Q : Type u} [CommRing Q] [Algebra F Q] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) : Tens F Q n →ₐ[K] Tens F Q n :=
  AlgHom.mk' (permAlg (Q := Q) σ).toRingHom
    (by
      intro c x
      show (permAlg (Q := Q) σ) (c • x) = c • (permAlg (Q := Q) σ) x
      have hcx : c • x = (algebraMap K F c) • x := by
        rw [Algebra.smul_def c x, IsScalarTower.algebraMap_apply K F (Tens F Q n) c,
          ← Algebra.smul_def (algebraMap K F c) x]
      have hcy : c • (permAlg (Q := Q) σ) x =
          (algebraMap K F c) • (permAlg (Q := Q) σ) x := by
        rw [Algebra.smul_def c (permAlg (Q := Q) σ x),
          IsScalarTower.algebraMap_apply K F (Tens F Q n) c,
          ← Algebra.smul_def (algebraMap K F c) (permAlg (Q := Q) σ x)]
      rw [hcx, hcy]
      exact map_smul _ _ _)

theorem permAlgAlgHom_apply {Q : Type u} [CommRing Q] [Algebra F Q] (n : ℕ)
    (σ : Equiv.Perm (Fin n)) (x : Tens F Q n) :
    permAlgAlgHom (K := K) (F := F) n σ x = permAlg (Q := Q) σ x := rfl

/-- **`κ` intertwines the permutation with the reindexing.** -/
theorem permAlgAlgHom_comp_kappa (V : C.left.Opens) (hV : IsAffineOpen V)
    (I : Ideal Γ((C.baseChange F).left, C.bcOpens F V)) (σ : Equiv.Perm (Fin n))
    (m : Fin n) :
    (permAlgAlgHom (K := K) (F := F) n σ).comp (kappa (C := C) (F := F) (n := n) V hV I m) =
      kappa (C := C) (F := F) (n := n) V hV I (σ m) := by
  ext b
  rw [AlgHom.comp_apply, permAlgAlgHom_apply]
  show permAlg (Q := Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) σ
      (tensSingle F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n m
        (Ideal.Quotient.mk I (secAlpha C F V b)))
    = tensSingle F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n (σ m)
        (Ideal.Quotient.mk I (secAlpha C F V b))
  exact permAlg_tensSingle σ m _

/-- `evalAlg` is insensitive to the tuple (as a function) and to the proof of the inclusion. -/
theorem evalAlg_congr {S : Type u} [CommRing S] [Algebra K S] {V : C.left.Opens}
    {x x' : Fin n → Work.SpecLin.RPt C.toOver S} (h : x = x')
    (hx : ⊤ ≤ (Limits.Pi.lift x : Work.SpecLin.specOf (K := K) S ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n)
    (hx' : ⊤ ≤ (Limits.Pi.lift x' : Work.SpecLin.specOf (K := K) S ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n) :
    evalAlg C V n x hx = evalAlg C V n x' hx' := by
  subst h
  exact congrArg _ (Subsingleton.elim hx hx')

/-- **`ρ` maps the `S_n`-invariant functions into the symmetric tensors.** -/
theorem rho_mem_symTensors (V : C.left.Opens) (hV : IsAffineOpen V)
    (I : Ideal Γ((C.baseChange F).left, C.bcOpens F V))
    {a : Γ((Work.SymQuot.prod C.toOver n).left, Work.SymQuot.piOpen C.toOver V n)}
    (ha : a ∈ chartInvariants (C := C) (n := n) (Work.SymQuot.piOpen C.toOver V n)
      (symPiOpen_invariant C n V)) :
    rho (C := C) (F := F) (n := n) V hV I a ∈
      symTensors F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n := by
  rw [mem_symTensors]
  intro σ
  change (permAlgAlgHom (K := K) (F := F) n σ) (rho (C := C) (F := F) (n := n) V hV I a) =
    rho (C := C) (F := F) (n := n) V hV I a
  set x : Fin n → Work.SpecLin.RPt C.toOver
      (Tens F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n) :=
    (fun m => ptOfAlgHom C hV (kappa (C := C) (F := F) (n := n) V hV I m)) with hx
  have hxmem : ∀ m : Fin n, ⊤ ≤ (x m).left ⁻¹ᵁ V :=
    fun m => ptOfAlgHom_mem (C := C) (V := V) hV _
  have hlands : ⊤ ≤ (Limits.Pi.lift x : Work.SpecLin.specOf (K := K)
      (Tens F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n) ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n :=
    piOpen_landsIn (C := C) (n := n) x hxmem
  have hperm : ∀ m : Fin n, Work.SpecLin.RPt.map (permAlgAlgHom (K := K) (F := F) n σ) (x m) =
      x (σ m) := by
    intro m
    rw [hx]
    rw [Work.SymQuot.DivOf.Complete.RPt_map_ptOfAlgHom]
    rw [permAlgAlgHom_comp_kappa (C := C) (F := F) (n := n) V hV I σ m]
  have hfun : (fun m : Fin n => Work.SpecLin.RPt.map (permAlgAlgHom (K := K) (F := F) n σ)
      (x m)) = (x ∘ σ) := funext hperm
  have hlands3 : ⊤ ≤ (Limits.Pi.lift (x ∘ σ) : Work.SpecLin.specOf (K := K)
      (Tens F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n) ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n :=
    piOpen_landsIn (C := C) (n := n) (x ∘ σ) (fun m => hxmem (σ m))
  have hlands2 : ⊤ ≤ (Limits.Pi.lift (fun m : Fin n =>
      Work.SpecLin.RPt.map (permAlgAlgHom (K := K) (F := F) n σ) (x m)) :
        Work.SpecLin.specOf (K := K)
          (Tens F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n) ⟶
        Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ
      Work.SymQuot.piOpen C.toOver V n := by
    rw [hfun]
    exact hlands3
  have hcomp := evalAlg_comp (C := C) (V := V) (n := n)
    (permAlgAlgHom (K := K) (F := F) n σ) x hlands hlands2
  have h2 : (permAlgAlgHom (K := K) (F := F) n σ)
      (rho (C := C) (F := F) (n := n) V hV I a) =
      evalAlg C V n (x ∘ σ) hlands3 a := by
    have h3 := congrArg (fun (f : Γ((Work.SymQuot.prod C.toOver n).left,
        Work.SymQuot.piOpen C.toOver V n) →+*
        Tens F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n) => f a) hcomp
    simp only [RingHom.comp_apply] at h3
    rw [evalAlg_congr (C := C) (V := V) (n := n) hfun hlands2 hlands3] at h3
    exact h3
  rw [h2]
  rw [show rho (C := C) (F := F) (n := n) V hV I a =
      evalAlg C V n x hlands a from rfl]
  exact evalAlg_perm_of_mem (C := C) (V := V) (n := n) x hlands σ hlands3 ha

/-- **The `n`-tuple of points lands in `Vⁿ` as soon as each place `ptPlace (y m)` lies in `V_L`.**

The place `ptPlace (y m)` is the point `ptLeft (y m) (0)` of `C_L`, which lies over
`(y m) (0)` in `C`; hence the two conditions are the same one. -/
theorem piOpen_landsIn_of_place_mem {L : Type u} [Field L] [Algebra K L]
    (V : C.left.Opens) (y : Fin n → Work.SpecLin.CurveFPt C L)
    (hplace : ∀ m, (Work.SpecLin.ptPlace (y m)).point ∈ C.bcOpens L V) :
    ⊤ ≤ (Limits.Pi.lift y : Work.SpecLin.specOf (K := K) L ⟶
      Work.SymQuot.prod C.toOver n).left ⁻¹ᵁ Work.SymQuot.piOpen C.toOver V n := by
  refine piOpen_landsIn (C := C) (n := n) y ?_
  intro m z _
  have hz : z = (IsLocalRing.closedPoint L : ↥(Spec (CommRingCat.of L))) :=
    Subsingleton.elim (α := ↥(Spec (CommRingCat.of L))) _ _
  rw [hz]
  have hmem : (Work.SpecLin.ptLeft (y m)) (IsLocalRing.closedPoint L) ∈
      (Curve.baseChangeFst C L) ⁻¹ᵁ V := hplace m
  have hfst : (Work.SpecLin.ptLeft (y m) ≫ Curve.baseChangeFst C L)
      (IsLocalRing.closedPoint L) ∈ V := hmem
  rwa [Work.SpecLin.ptLeft_fst] at hfst

/-! ### The norm point `φ_D` -/

/-- **The norm point attached to the divisor `D`**: for an `F`-basis `v` of `Q = Γ(C_F,V_F) ⧸ I`,
the `F`-algebra homomorphism `Γ(Cⁿ,Vⁿ)^{S_n} → F`, `a ↦ normVal v (ρ a)`. -/
noncomputable def phiD (V : C.left.Opens) (hV : IsAffineOpen V)
    (I : Ideal Γ((C.baseChange F).left, C.bcOpens F V))
    (v : Module.Basis (Fin n) F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I)) :
    ↥(chartInvariants (C := C) (n := n) (Work.SymQuot.piOpen C.toOver V n)
      (symPiOpen_invariant C n V)) →+* F :=
  (normPoint v).toRingHom.comp
    (((rho (C := C) (F := F) (n := n) V hV I).comp
      (Subring.subtype (chartInvariants (C := C) (n := n) (Work.SymQuot.piOpen C.toOver V n)
        (symPiOpen_invariant C n V)))).codRestrict
      (symTensors F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I) n)
      (fun a => rho_mem_symTensors (C := C) (F := F) (n := n) V hV I a.2))

@[simp]
theorem phiD_apply (V : C.left.Opens) (hV : IsAffineOpen V)
    (I : Ideal Γ((C.baseChange F).left, C.bcOpens F V))
    (v : Module.Basis (Fin n) F (Γ((C.baseChange F).left, C.bcOpens F V) ⧸ I))
    (a : ↥(chartInvariants (C := C) (n := n) (Work.SymQuot.piOpen C.toOver V n)
      (symPiOpen_invariant C n V))) :
    phiD (C := C) (F := F) (n := n) V hV I v a =
      normVal v (rho (C := C) (F := F) (n := n) V hV I a) := rfl

end Work.SymQuot.DivOf.Complete
