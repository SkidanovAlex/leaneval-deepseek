import Mathlib
import Submission.Work.RiemannRoch.Pole
import Submission.Work.CurveBasics.Order.finiteDimensional_adjoin_functionField
import Submission.Work.CurveBasics.Order.kxClosure_finrank_general
import Submission.Work.CurveBasics.Order.inertiaDeg_kxPrimeOfPlace_eq_finrank_k
import Submission.Work.CurveBasics.Order.kxPrimeOfPlace_residueField_finrank
import Submission.Work.CurveBasics.Order.ramificationIdx_eq_ordAt
import Submission.Work.CurveBasics.Order.SumPrimesAux
import Submission.Work.CurveBasics.Order.kx_pure_insep
import Submission.Work.CurveBasics.Order.perfectClosure_separable_of_normal
import Submission.Work.CurveBasics.Order.module_finite_integralClosure_of_ringEquiv
import Submission.Work.CurveBasics.Order.pureInsep_separable_top_normal
import Submission.Work.FieldTheory.separable_perfectClosure_of_normal

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedVariables false

universe u

namespace Work.RiemannRoch.Pole

open Work.CurveBasics
open Work.CurveBasics.Order
open IntermediateField
open scoped Classical IntermediateField.algebraAdjoinAdjoin

noncomputable section

variable {k : Type u} [Field k]

/-! ## The degree of the pole divisor as a sum over the poles

`deg D` is the sum of the coefficients of `D` weighted by the residue degrees, and the
coefficients of `poleDivisor C x` are `max 0 (-ord_Q x)`.  Since `max 0 a ≠ 0 ↔ 0 < a`, this
collapses to a sum over the poles of `x`. -/

private theorem glue_general_aux'
    {A B N L : Type*} [CommRing A] [CommRing B] [Field N] [Field L]
    [Algebra A B] [Algebra A N] [Algebra B N] [IsScalarTower A B N] [IsFractionRing B N]
    [Algebra A L] [Algebra N L] [Algebra B L] [IsScalarTower A N L] [IsScalarTower B N L]
    [IsScalarTower A B L]
    [FiniteDimensional N L] [Algebra.IsSeparable N L]
    [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (h1 : Module.Finite A B) :
    Module.Finite A ↥(integralClosure A L) := by
  haveI : Module.Finite A B := h1
  haveI h3 : Module.Finite B ↥(integralClosure B L) :=
    IsIntegralClosure.finite B N L ↥(integralClosure B L)
  have h4 : Module.Finite A ↥(integralClosure B L) :=
    Module.Finite.trans B ↥(integralClosure B L)
  have hEq : Subalgebra.restrictScalars A (integralClosure B L) = integralClosure A L := by
    ext y
    rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff, mem_integralClosure_iff]
    exact ⟨fun hy => isIntegral_trans (A := B) y hy, fun hy => IsIntegral.tower_top hy⟩
  rw [← hEq]
  exact h4

private theorem perfectClosure_adjoin_gen_aux'' {k L : Type*} [Field k] [Field L] [Algebra k L]
    (x : L) (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set L)) L]
    (y : ↥(perfectClosure ↥(IntermediateField.adjoin k ({x} : Set L)) L))
    (hy : (y : L) = x) :
    Transcendental k y ∧
    FiniteDimensional
      (IntermediateField.adjoin k ({y} : Set (↥(perfectClosure ↥(IntermediateField.adjoin k ({x} : Set L)) L))))
      (↥(perfectClosure ↥(IntermediateField.adjoin k ({x} : Set L)) L)) ∧
    IsPurelyInseparable
      (IntermediateField.adjoin k ({y} : Set (↥(perfectClosure ↥(IntermediateField.adjoin k ({x} : Set L)) L))))
      (↥(perfectClosure ↥(IntermediateField.adjoin k ({x} : Set L)) L)) := by
  let Kf : IntermediateField k L := IntermediateField.adjoin k ({x} : Set L)
  let P : IntermediateField ↥Kf L := perfectClosure ↥Kf L
  haveI : FiniteDimensional ↥Kf ↥P := inferInstance
  haveI : IsPurelyInseparable ↥Kf ↥P := inferInstance
  let incl : ↥P →ₐ[k] L :=
    { toFun := Subtype.val, map_one' := rfl, map_mul' := fun a b => rfl, map_zero' := rfl,
      map_add' := fun a b => rfl, commutes' := fun c => rfl }
  have hincl : Function.Injective incl := Subtype.val_injective
  have hmap : (IntermediateField.adjoin k ({y} : Set ↥P)).map incl = Kf := by
    have h1 : (incl '' ({y} : Set ↥P)) = ({x} : Set L) := by
      rw [Set.image_singleton]
      exact Set.singleton_eq_singleton_iff.mpr (by rw [show incl y = (y : L) from rfl, hy])
    rw [IntermediateField.adjoin_map, h1]
  set Ap : IntermediateField k ↥P := IntermediateField.adjoin k ({y} : Set ↥P) with hAp
  let e : ↥Kf ≃ₐ[k] ↥Ap :=
    ((IntermediateField.equivMap Ap incl).trans (IntermediateField.equivOfEq hmap)).symm
  letI : Algebra ↥Kf ↥Ap := e.toRingHom.toAlgebra
  have hx0 : ∀ r : ↥Kf, algebraMap ↥Kf ↥Ap r = e r := fun r => by
    have hcanon : algebraMap ↥Kf ↥Ap = (e.toRingEquiv.toRingHom : ↥Kf →+* ↥Ap) :=
      RingHom.algebraMap_toAlgebra (R := ↥Kf) (S := ↥Ap) (i := e.toRingEquiv.toRingHom)
    rw [show algebraMap ↥Kf ↥Ap r = (e.toRingEquiv.toRingHom) r from RingHom.congr_fun hcanon r]
    rfl
  haveI : IsScalarTower ↥Kf ↥Ap ↥P := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    rw [hx0 r]
    apply Subtype.ext
    have h1 : ((IntermediateField.equivMap Ap incl).trans (IntermediateField.equivOfEq hmap)) (e r) = r :=
      AlgEquiv.apply_symm_apply _ _
    have h4 : (r : L) = ((e r : ↥P) : L) := by
      calc (r : L)
          = (((IntermediateField.equivMap Ap incl).trans (IntermediateField.equivOfEq hmap)) (e r) : L) :=
              (congrArg Subtype.val h1).symm
        _ = (((IntermediateField.equivOfEq hmap) ((IntermediateField.equivMap Ap incl) (e r))) : L) := by
              rw [AlgEquiv.trans_apply]
        _ = (((IntermediateField.equivMap Ap incl) (e r)) : L) := rfl
        _ = incl (e r) := by rw [IntermediateField.coe_equivMap_apply]
        _ = ((e r : ↥P) : L) := rfl
    exact h4
  refine ⟨?_, ?_, ?_⟩
  · rintro h
    exact hx (by
      have h' := (isAlgebraic_algHom_iff incl hincl).mpr h
      rwa [show incl y = (y:L) from rfl, hy] at h')
  · exact Module.Finite.of_restrictScalars_finite ↥Kf ↥Ap ↥P
  · exact IsPurelyInseparable.tower_top (F := ↥Kf) (E := ↥Ap) (K := ↥P)

private theorem map_adjoin_adjoin_aux' {F E E' : Type*} [Field F] [Field E] [Field E'] [Algebra F E]
    [Algebra F E'] (f : E →ₐ[F] E') (s : Set E) :
    (IntermediateField.adjoin F s).map f = IntermediateField.adjoin F (f '' s) := by
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.map_le_iff_le_comap, IntermediateField.adjoin_le_iff]
    intro y hy
    exact IntermediateField.subset_adjoin F _ (Set.mem_image_of_mem f hy)
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨z, hz, rfl⟩
    exact (IntermediateField.map_mem_map (f := f) (S := IntermediateField.adjoin F s)).mpr
      (IntermediateField.subset_adjoin F s hz)

/-- **Descent of finiteness of an integral closure along an injective `k`-algebra map.**

Let `f : L →ₐ[k] N` be injective and let `x : L`.  Then `f` identifies the subalgebra
`k[x] ⊆ L` with `k[f x] ⊆ N`, and carries the integral closure of `k[x]` in `L` into the
integral closure of `k[f x]` in `N`.  As `k[x]` is a finitely generated `k`-algebra (hence
Noetherian), a finite presentation of the larger integral closure restricts to a finite
presentation of the smaller one. -/
private theorem finite_integralClosure_of_injective_aux'
    {k L N : Type u} [Field k] [Field L] [Field N] [Algebra k L] [Algebra k N]
    (f : L →ₐ[k] N) (hf : Function.Injective f) (x : L)
    (h : Module.Finite ↥(Algebra.adjoin k ({f x} : Set N))
          ↥(integralClosure ↥(Algebra.adjoin k ({f x} : Set N)) N)) :
    Module.Finite ↥(Algebra.adjoin k ({x} : Set L))
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set L)) L) := by
  classical
  let A := Algebra.adjoin k ({x} : Set L)
  let A' := Algebra.adjoin k ({f x} : Set N)
  -- `f` maps `A = k[x]` onto `A' = k[f x]`.
  have hmap : A.map f = A' := by
    show Subalgebra.map f (Algebra.adjoin k ({x} : Set L)) = Algebra.adjoin k ({f x} : Set N)
    rw [AlgHom.map_adjoin f ({x} : Set L), Set.image_singleton]
  -- the induced `k`-algebra isomorphism `A ≅ A'`
  let φ : A →ₐ[k] A' := (f.comp A.val).codRestrict A' (fun a => by
    have h1 : f (A.val a) ∈ A.map f := ⟨a, a.2, rfl⟩
    rw [hmap] at h1
    exact h1)
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h3 : (f.comp A.val) a = (f.comp A.val) b := congrArg Subtype.val hab
    have h4 : f ((a : L)) = f ((b : L)) := by simpa [AlgHom.comp_apply] using h3
    exact Subtype.ext (hf h4)
  have hφsurj : Function.Surjective φ := by
    intro b
    have hb : (b : N) ∈ A.map f := by rw [hmap]; exact b.2
    obtain ⟨a, ha, hfa⟩ := (Subalgebra.mem_map.mp hb)
    refine ⟨⟨a, ha⟩, Subtype.ext ?_⟩
    change (f.comp A.val) ⟨a, ha⟩ = (b : N)
    rw [AlgHom.comp_apply]
    exact hfa
  let e : A ≃ₐ[k] A' := AlgEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  -- let `A` act on `N` through `f`, and on `A'` through `e`
  letI : Algebra A N := (f.comp A.val).toRingHom.toAlgebra
  letI : Algebra A A' := e.toRingHom.toAlgebra
  have he_coe : ∀ a : A, (e a : N) = f (A.val a) := by
    intro a
    change (φ a : N) = f (A.val a)
    exact AlgHom.coe_codRestrict (f.comp A.val) A' _ a
  haveI hST : IsScalarTower A A' N := IsScalarTower.of_algebraMap_eq (fun a => by
    show (algebraMap A N) a = (algebraMap A' N) ((algebraMap A A') a)
    rw [show (algebraMap A A') a = e a from rfl]
    change f (A.val a) = ↑(e a)
    rw [he_coe a])
  have hcomp : (algebraMap A' N).comp φ.toRingHom = f.toRingHom.comp (algebraMap A L) := by
    ext a
    show (e a : N) = f (A.val a)
    exact he_coe a
  -- finiteness over `A` of the target integral closure
  haveI hfinA' : Module.Finite A A' := inferInstance
  haveI : Module.Finite A ↥(integralClosure A' N) :=
    Module.Finite.trans A' ↥(integralClosure A' N)
  -- `A = k[x]` is Noetherian, hence so is every extension module over it
  haveI hAft : Algebra.FiniteType k A := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x)
  haveI hAnoeth : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI hnoeth : IsNoetherian A ↥(integralClosure A' N) := inferInstance
  -- the `A`-linear map carrying the smaller integral closure into the larger one
  have hT : ∀ y : ↥(integralClosure A L), IsIntegral A' (f (y : L)) := fun y =>
    IsIntegral.map_of_comp_eq φ.toRingHom f.toRingHom hcomp y.2
  let T : ↥(integralClosure A L) →ₗ[A] ↥(integralClosure A' N) :=
    { toFun := fun y => ⟨f (y : L), hT y⟩
      map_add' := fun y z => Subtype.ext (map_add f (y : L) (z : L))
      map_smul' := fun a y => Subtype.ext (by
        simp only [Algebra.smul_def, Subalgebra.coe_mul, Subalgebra.coe_algebraMap, map_mul]
        rfl) }
  have hTinj : Function.Injective T := fun y z hh => by
    have h2 : f (y : L) = f (z : L) := congrArg Subtype.val hh
    exact Subtype.ext (hf h2)
  have hrange : (Submodule.map T (⊤ : Submodule A ↥(integralClosure A L))).FG := by
    rw [Submodule.map_top]
    exact IsNoetherian.noetherian T.range
  have htop : (⊤ : Submodule A ↥(integralClosure A L)).FG :=
    Submodule.fg_of_fg_map_injective T hTinj hrange
  exact Module.finite_def.mpr htop

/-- Reduction of Nagata's N-2 (Japanese) property of `k[x]` to finite **normal** extensions:
granting the property for finite normal extensions, it holds for arbitrary finite extensions
(pass to a normal closure of `L/k(x)` and descend along the embedding). -/
private theorem kx_of_normal_fin_aux'
    (hnorm : ∀ {k L : Type u} [Field k] [Field L] [Algebra k L] (x : L)
      [FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set L)) L]
      [Normal ↥(IntermediateField.adjoin k ({x} : Set L)) L],
      Transcendental k x →
      Module.Finite ↥(Algebra.adjoin k ({x} : Set L))
        ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set L)) L))
    {k L : Type u} [Field k] [Field L] [Algebra k L] (x : L) (hx : Transcendental k x)
    [FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set L)) L] :
    Module.Finite ↥(Algebra.adjoin k ({x} : Set L))
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set L)) L) := by
  -- The base field `Kb = k(x) ⊆ L`.
  let Kb := IntermediateField.adjoin k ({x} : Set L)
  -- An ambient algebraically closed field together with the normal closure `N` of `L/Kb`.
  let M := AlgebraicClosure Kb
  let N : IntermediateField Kb M := IntermediateField.normalClosure Kb L M
  haveI hfdN : FiniteDimensional Kb ↥N := normalClosure.is_finiteDimensional Kb L M
  haveI hNn : Normal Kb ↥N := normalClosure.normal Kb L M
  haveI : Algebra.IsAlgebraic Kb L := Algebra.IsAlgebraic.of_finite Kb L
  -- an embedding of `L` into the normal closure, fixing `Kb`
  let ψ₀ : L →ₐ[Kb] M := IsAlgClosed.lift
  have hle : ψ₀.fieldRange ≤ N := AlgHom.fieldRange_le_normalClosure ψ₀
  let ψ : L →ₐ[Kb] ↥N := ψ₀.codRestrict N.toSubalgebra (fun y => hle ⟨y, rfl⟩)
  have hψinj : Function.Injective ψ := fun a b hab => ψ₀.injective (Subtype.ext_iff.mp hab)
  -- restrict scalars to `k`
  let ψk : L →ₐ[k] ↥N := ψ.restrictScalars k
  have hψk_apply : ∀ a, ψk a = ψ a := fun a => AlgHom.restrictScalars_apply k ψ a
  have hψkinj : Function.Injective ψk := fun a b h =>
    hψinj (by rw [hψk_apply a, hψk_apply b] at h; exact h)
  -- the base field of `↥N` generated by `ψ x` is the image of `Kb`
  let Kb' := IntermediateField.adjoin k ({ψ x} : Set ↥N)
  have key : Kb' = Kb.map ψk := by
    show (IntermediateField.adjoin k ({ψ x} : Set ↥N)) =
      (IntermediateField.adjoin k ({x} : Set L)).map ψk
    rw [map_adjoin_adjoin_aux' ψk ({x} : Set L), Set.image_singleton, AlgHom.restrictScalars_apply]
  -- the base change map `Kb → ↥N`, whose range is `Kb'`
  let g : Kb →ₐ[k] ↥N := ψk.comp Kb.val
  have hg : g.fieldRange = Kb' := (IntermediateField.fieldRange_comp_val Kb ψk).trans key.symm
  let g' : Kb →ₐ[k] ↥Kb' := g.codRestrict Kb'.toSubalgebra (fun a => by
    have h1 : g a ∈ g.fieldRange := ⟨a, rfl⟩
    rwa [hg] at h1)
  have hginj : Function.Injective g := fun a b h => Subtype.ext (hψkinj (by
    simpa [g, AlgHom.comp_apply] using h))
  have hbij : Function.Bijective g' := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      exact hginj (by
        have h := congrArg Subtype.val hab
        rwa [AlgHom.coe_codRestrict, AlgHom.coe_codRestrict] at h)
    · intro b
      have hb : (b : ↥N) ∈ g.fieldRange := by rw [hg]; exact b.2
      obtain ⟨a, ha⟩ := hb
      exact ⟨a, Subtype.ext ha⟩
  let e : Kb ≃ₐ[k] ↥Kb' := AlgEquiv.ofBijective g' hbij
  have he_coe : ∀ a : Kb, (e a : ↥N) = g a := by
    intro a
    change (g' a : ↥N) = g a
    exact AlgHom.coe_codRestrict g Kb'.toSubalgebra _ a
  have hbase : ∀ a : Kb, (algebraMap Kb ↥N) a = g a := fun a => by
    change (algebraMap Kb ↥N) a = ψ (algebraMap Kb L a)
    exact (AlgHom.commutes ψ a).symm
  -- transfer finiteness and normality of `↥N / Kb` to `↥N / Kb'`
  letI : Algebra Kb ↥Kb' := e.toRingHom.toAlgebra
  haveI : IsScalarTower Kb ↥Kb' ↥N := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [show (algebraMap Kb ↥Kb') a = e a from rfl, hbase a]
    exact (he_coe a).symm)
  haveI hfd' : FiniteDimensional ↥Kb' ↥N := Module.Finite.of_restrictScalars_finite Kb ↥Kb' ↥N
  haveI hnrm' : Normal ↥Kb' ↥N := Normal.tower_top_of_normal Kb ↥Kb' ↥N
  -- `ψ x` is transcendental over `k`
  have htransc : Transcendental k (ψ x) :=
    fun h => hx ((isAlgebraic_algHom_iff ψk hψkinj).mp h)
  -- apply the hypothesis to the normal extension `↥N / k(ψ x)`
  have hfin := hnorm (L := ↥N) (ψ x) htransc
  -- and descend along `ψ`
  exact finite_integralClosure_of_injective_aux' (ψ.restrictScalars k) hψkinj x hfin


/-- The normal case of Nagata's N-2 property for `k[x]`. -/
private theorem kx_normal_aux {k L : Type*} [Field k] [Field L] [Algebra k L] (x : L)
    (hx : Transcendental k x)
    [FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set L)) L]
    [Normal ↥(IntermediateField.adjoin k ({x} : Set L)) L] :
    Module.Finite ↥(Algebra.adjoin k ({x} : Set L))
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set L)) L) := by
  classical
  set A : Subalgebra k L := Algebra.adjoin k ({x} : Set L) with hAdef
  set K : IntermediateField k L := IntermediateField.adjoin k ({x} : Set L) with hKdef
  have hxK : x ∈ K := by rw [hKdef]; exact IntermediateField.mem_adjoin_simple_self k x
  have hAK : A ≤ K.toSubalgebra := by
    rw [hAdef, hKdef]; exact IntermediateField.algebra_adjoin_le_adjoin k _
  set Ks : Subalgebra k L := K.toSubalgebra with hKsdef
  set P : IntermediateField ↥K L := perfectClosure ↥K L with hPdef
  set Ps : Subalgebra k L := (P.toSubalgebra).restrictScalars k with hPsdef
  have hKsPs : Ks ≤ Ps := by
    intro z hz
    rw [hPsdef]
    exact Subalgebra.algebraMap_mem (P.toSubalgebra) (⟨z, hz⟩ : ↥K)
  have hAPs : A ≤ Ps := hAK.trans hKsPs
  letI hAKsA : Algebra ↥A ↥Ks := (Subalgebra.inclusion hAK).toRingHom.toAlgebra
  letI hKsPsA : Algebra ↥Ks ↥Ps := (Subalgebra.inclusion hKsPs).toRingHom.toAlgebra
  letI hAPsA : Algebra ↥A ↥Ps := (Subalgebra.inclusion hAPs).toRingHom.toAlgebra
  have t1 : IsScalarTower ↥A ↥Ks ↥Ps := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    apply Subtype.ext
    rfl
  have t2 : IsScalarTower ↥A ↥Ks L := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have t3 : IsScalarTower ↥A ↥Ps L := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  have t4 : IsScalarTower ↥Ks ↥Ps L := IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI := t1; haveI := t2; haveI := t4
  haveI t3' : IsScalarTower ↥A ↥P L := t3
  haveI hfdK : FiniteDimensional ↥K L := ‹_›
  haveI hNormK : Normal ↥K L := ‹_›
  haveI hfdPL : FiniteDimensional ↥P L := inferInstance
  haveI hsepPL : Algebra.IsSeparable ↥P L :=
    Work.FieldTheory.separable_perfectClosure_of_normal (F := ↥K) (E := L)
  -- the element y = image of x in P
  have hxP : x ∈ (P : Set L) := by
    have h1 : ((⟨x, hxK⟩ : ↥K) : L) = x := rfl
    rw [← h1]
    exact Subalgebra.algebraMap_mem _ (⟨x, hxK⟩ : ↥K)
  let y : ↥P := ⟨x, hxP⟩
  have hyval : (y : L) = x := rfl
  obtain ⟨hyT, hyfd, hypi⟩ := perfectClosure_adjoin_gen_aux'' x hx y hyval
  haveI hfd_y : FiniteDimensional (IntermediateField.adjoin k ({y} : Set ↥P)) ↥P := hyfd
  haveI hpi_y : IsPurelyInseparable (IntermediateField.adjoin k ({y} : Set ↥P)) ↥P := hypi
  have hpure : Module.Finite ↥(Algebra.adjoin k ({y} : Set ↥P))
      ↥(integralClosure ↥(Algebra.adjoin k ({y} : Set ↥P)) ↥P) :=
    Work.CurveBasics.Order.kx_pure_insep y hyT
  -- transfer to A = k[x]
  let incl : ↥P →ₐ[k] L :=
    { toFun := Subtype.val, map_one' := rfl, map_mul' := fun a b => rfl, map_zero' := rfl,
      map_add' := fun a b => rfl, commutes' := fun c => rfl }
  have hinclP : Function.Injective incl := Subtype.val_injective
  have hmap : (Algebra.adjoin k ({y} : Set ↥P)).map incl = A := by
    rw [AlgHom.map_adjoin, hAdef]
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, rfl, rfl⟩; exact hyval
    · intro hz; exact ⟨y, rfl, hz.symm⟩
  have h1 : Module.Finite ↥A ↥(integralClosure ↥A ↥P) := by
    let S : Subalgebra k ↥P := Algebra.adjoin k ({y} : Set ↥P)
    let f1 : ↥S ≃ₐ[k] ↥(S.map incl) := S.equivMapOfInjective incl hinclP
    let f2 : ↥(S.map incl) ≃ₐ[k] ↥A := Subalgebra.equivOfEq (S.map incl) A hmap
    let g : ↥S ≃ₐ[k] ↥A := f1.trans f2
    let ealg : ↥A ≃ₐ[k] ↥S := g.symm
    have hgval : ∀ s : ↥S, (((g s : ↥A) : L)) = (((s : ↥S) : ↥P) : L) := by
      intro s
      show (((f2 (f1 s) : ↥A) : L)) = (((s : ↥S) : ↥P) : L)
      have hf2v : ∀ y : ↥(S.map incl), ((f2 y : ↥A) : L) = ((y : ↥(S.map incl)) : L) := by
        intro y; rfl
      rw [hf2v]
      have hf1v : ((f1 s : ↥(S.map incl)) : L) = (incl (s : ↥P) : L) := by
        rw [show ((f1 s : ↥(S.map incl)) : L) = incl ((s : ↥S) : ↥P) from
          Subalgebra.coe_equivMapOfInjective_apply (S := S) (f := incl) (hf := hinclP) (x := s)]
      rw [hf1v]
      rfl
    have hval : ∀ a : ↥A, ((((ealg a : ↥S)) : ↥P) : L) = ((a : ↥A) : L) := by
      intro a
      have hga : g (ealg a) = a := AlgEquiv.apply_symm_apply g a
      have h2 := hgval (ealg a)
      rw [hga] at h2
      exact h2.symm
    refine Work.CurveBasics.Order.module_finite_integralClosure_of_ringEquiv
      (A := ↥A) (A' := ↥S) (N := ↥P) ealg.toRingEquiv ?_ hpure
    ext a
    change (((ealg a : ↥S) : ↥P) : L) = ((a : ↥A) : L)
    exact (hval a)
  -- glue
  haveI hNoethA : IsNoetherianRing ↥A :=
    isNoetherianRing_of_ringEquiv (Polynomial k)
      (Polynomial.algEquivOfTranscendental k x hx).toRingEquiv
  haveI hICA : IsIntegrallyClosed ↥A :=
    IsIntegrallyClosed.of_equiv (Polynomial.algEquivOfTranscendental k x hx).toRingEquiv
  haveI hFrB : IsFractionRing ↥(integralClosure ↥A ↥P) ↥P :=
    integralClosure.isFractionRing_of_finite_extension (A := ↥A) (K := ↥K) (L := ↥P)
  haveI hICB : IsIntegrallyClosed ↥(integralClosure ↥A ↥P) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (R := ↥A) (K := ↥K) (L := ↥P)
  haveI hNoethB : IsNoetherianRing ↥(integralClosure ↥A ↥P) :=
    IsNoetherianRing.of_finite ↥A _
  haveI tABN : IsScalarTower ↥A ↥(integralClosure ↥A ↥P) ↥P :=
    Subalgebra.isScalarTower_mid (integralClosure ↥A ↥P)
  haveI tABL : IsScalarTower ↥A ↥(integralClosure ↥A ↥P) L :=
    Subalgebra.isScalarTower_mid (integralClosure ↥A ↥P)
  haveI tBNL : IsScalarTower ↥(integralClosure ↥A ↥P) ↥P L :=
    IsScalarTower.of_algebraMap_eq (R := ↥(integralClosure ↥A ↥P)) (S := ↥P) (A := L)
      (fun b => rfl)
  exact glue_general_aux' (A := ↥A) (B := ↥(integralClosure ↥A ↥P)) (N := ↥P) (L := L) h1


/-- **Nagata's N-2 (Japanese) property of `k[x]` for an arbitrary finite extension**, hence
finiteness of the integral closure of `k[x]` in `K(C)` in the form needed below. -/
private theorem kx_finite_aux {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (x : C.functionField) (hx : Transcendental k x) :
    Module.Finite (C.ordBase x) (C.ordClosure x) := by
  haveI hfd : FiniteDimensional
      ↥(IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField :=
    finiteDimensional_adjoin_functionField C hx
  exact kx_of_normal_fin_aux' (fun {a b} _ _ _ y _ _ hy => kx_normal_aux (k := a) (L := b) y hy) x hx

lemma deg_poleDivisor_eq_sum (C : Work.CurveBasics.Curve k) (x : C.functionField) :
    C.deg (Work.RiemannRoch.Curve.poleDivisor C x) =
      ∑ Q ∈ (C.finite_support_ordAt x).toFinset.filter (fun Q => C.ordAt x Q < 0),
        (-(C.ordAt x Q)) * (C.hom.residueDegree Q.point : ℤ) := by
  show (Work.RiemannRoch.Curve.poleDivisor C x).sum
      (fun Q n => n * (C.hom.residueDegree Q.point : ℤ)) = _
  have hsupp : (Work.RiemannRoch.Curve.poleDivisor C x).support =
      (C.finite_support_ordAt x).toFinset.filter (fun Q => C.ordAt x Q < 0) := by
    ext Q
    simp only [Finsupp.mem_support_iff, Finset.mem_filter, Set.Finite.mem_toFinset,
      Set.mem_setOf_eq, Work.RiemannRoch.Curve.poleDivisor_apply]
    constructor
    · intro h
      have hpos : (0 : ℤ) < max 0 (-(C.ordAt x Q)) :=
        lt_of_le_of_ne (le_max_left 0 _) (Ne.symm h)
      have hneg : (0 : ℤ) < -(C.ordAt x Q) := (lt_max_iff.mp hpos).resolve_left (lt_irrefl 0)
      omega
    · rintro ⟨-, hlt⟩
      have h2 : (0 : ℤ) < -(C.ordAt x Q) := by omega
      rw [max_eq_right h2.le]
      exact ne_of_gt h2
  rw [Finsupp.sum, hsupp]
  refine Finset.sum_congr rfl fun Q hQ => ?_
  rw [Work.RiemannRoch.Curve.poleDivisor_apply]
  have hlt : C.ordAt x Q < 0 := (Finset.mem_filter.mp hQ).2
  rw [max_eq_right (show (0 : ℤ) ≤ -(C.ordAt x Q) by omega)]

/-! ## The bridge between the zeros of `x` and the primes of `k[x]^int` above `(x)`

This is the (separability-free) dictionary of `Work.CurveBasics.Order.sum_primesOver_eq_sum_ord`,
assembled here from the pieces that are available: the bijection `spso_surj`/`spso_inj` between
the zeros of `x` and the primes over `(x)`, the identity `e = ord_Q x` of
`Work.CurveBasics.Order.ramificationIdx_eq_ordAt`, and `f = [κ(Q) : k]`, which we obtain from
`Work.CurveBasics.Order.inertiaDeg_kxPrimeOfPlace_eq_finrank_k` and
`Work.CurveBasics.Order.kxPrimeOfPlace_residueField_finrank`. -/

lemma sum_primesOver_eq_sum_ord_curve (C : Work.CurveBasics.Curve k) (x : C.functionField)
    (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField]
    [Module.Finite (C.ordBase x) (C.ordClosure x)]
    [Fintype ((C.ordIdeal x).primesOver (C.ordClosure x))] :
    ∑ q : (C.ordIdeal x).primesOver (C.ordClosure x),
        ((q.1.ramificationIdx (C.ordBase x) : ℤ) * (q.1.inertiaDeg (C.ordBase x) : ℤ))
      = ∑ Q ∈ (C.finite_support_ordAt x).toFinset.filter (fun Q => 0 < C.ordAt x Q),
          C.ordAt x Q * (C.hom.residueDegree Q.point : ℤ) := by
  classical
  set Z : Finset C.Place := (C.finite_support_ordAt x).toFinset.filter (fun Q => 0 < C.ordAt x Q)
    with hZ
  have hmem : ∀ Q ∈ Z, 0 < C.ordAt x Q := by
    intro Q hQ
    rw [hZ] at hQ
    exact (Finset.mem_filter.mp hQ).2
  let i : ∀ Q ∈ Z, (C.ordIdeal x).primesOver (C.ordClosure x) := fun Q hQ =>
    ⟨kxPrimeOfPlace C x Q (hmem Q hQ).le, kxPrimeOfPlace_isPrime C x Q (hmem Q hQ).le,
      kxPrimeOfPlace_liesOver C x hx Q (hmem Q hQ)⟩
  have hterm : ∀ (Q : C.Place) (hQ : Q ∈ Z),
      ((i Q hQ).1.ramificationIdx (C.ordBase x) : ℤ)
        * ((i Q hQ).1.inertiaDeg (C.ordBase x) : ℤ)
      = C.ordAt x Q * (C.hom.residueDegree Q.point : ℤ) := by
    intro Q hQ
    have h1 : ((i Q hQ).1.ramificationIdx (C.ordBase x) : ℤ) = C.ordAt x Q :=
      ramificationIdx_eq_ordAt C x hx Q (hmem Q hQ)
    have h2 : ((i Q hQ).1.inertiaDeg (C.ordBase x) : ℤ)
        = (C.hom.residueDegree Q.point : ℤ) := by
      have h3 : (kxPrimeOfPlace C x Q (hmem Q hQ).le).inertiaDeg (C.ordBase x)
          = C.hom.residueDegree Q.point := by
        rw [inertiaDeg_kxPrimeOfPlace_eq_finrank_k C x hx Q (hmem Q hQ),
          kxPrimeOfPlace_residueField_finrank C x hx Q (hmem Q hQ)]
      exact_mod_cast h3
    rw [h1, h2]
  refine (Finset.sum_bij i (fun Q hQ => Finset.mem_univ _) ?_ ?_ ?_).symm
  · intro Q hQ Q' hQ' heq
    exact spso_inj C x hx (hmem Q hQ) (hmem Q' hQ') (Subtype.ext_iff.mp heq)
  · intro q _
    obtain ⟨Q, hQpos, heq⟩ := spso_surj C x hx q
    refine ⟨Q, ?_, Subtype.ext heq⟩
    rw [hZ, Finset.mem_filter]
    exact ⟨(Set.Finite.mem_toFinset (C.finite_support_ordAt x)).mpr (ne_of_gt hQpos), hQpos⟩
  · intro Q hQ
    exact (hterm Q hQ).symm

/-! ## The degree of the divisor of zeros

`∑_{ord_Q x > 0} ord_Q x · [κ(Q) : k] = [K(C) : k(x)]`, deduced from the fundamental identity of
ramification theory and the bridge above. -/

lemma sum_ord_pos_eq_finrank_curve (C : Work.CurveBasics.Curve k) (x : C.functionField)
    (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField] :
    ∑ Q ∈ (C.finite_support_ordAt x).toFinset.filter (fun Q => 0 < C.ordAt x Q),
        C.ordAt x Q * (C.hom.residueDegree Q.point : ℤ)
      = (Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
          C.functionField : ℤ) := by
  haveI hFin : Module.Finite (C.ordBase x) (C.ordClosure x) := kx_finite_aux C x hx
  haveI hFlat : Module.Flat (C.ordBase x) (C.ordClosure x) := inferInstance
  haveI hPrime : (C.ordIdeal x).IsPrime := by
    rw [show C.ordIdeal x = Ideal.span {Curve.kxGen C x} from rfl]
    exact Curve.kx_span_gen_isPrime C x hx
  haveI hFt : Fintype ((C.ordIdeal x).primesOver (C.ordClosure x)) :=
    (Algebra.QuasiFinite.finite_primesOver (C.ordIdeal x)).fintype
  rw [← sum_primesOver_eq_sum_ord_curve C x hx]
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (C.ordIdeal x) (C.ordClosure x)
  have hrank := kxClosure_finrank_general C x hx
  have hsumZ : (∑ q : (C.ordIdeal x).primesOver (C.ordClosure x),
      ((q.1.ramificationIdx (C.ordBase x) : ℤ) * (q.1.inertiaDeg (C.ordBase x) : ℤ)))
      = ((Module.finrank (C.ordBase x) (C.ordClosure x) : ℕ) : ℤ) := by
    rw [← hsum, Nat.cast_sum]
    exact Finset.sum_congr rfl fun q _ => by push_cast; ring
  rw [hsumZ, hrank]

/-! ## The subfields generated by `x` and by `x⁻¹` agree -/

private lemma adjoin_inv_eq_adjoin {K : Type*} [Field K] [Algebra k K] {h : K} :
    IntermediateField.adjoin k ({h⁻¹} : Set K) = IntermediateField.adjoin k ({h} : Set K) := by
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    exact IntermediateField.inv_mem _ (IntermediateField.mem_adjoin_simple_self k h)
  · rw [IntermediateField.adjoin_le_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    have h2 := IntermediateField.inv_mem (IntermediateField.adjoin k ({h⁻¹} : Set K))
      (IntermediateField.mem_adjoin_simple_self k h⁻¹)
    simpa using h2

/-! ## The degree of the pole divisor of `x` is `[K(C) : k(x)]`

The mirror image of the previous section, applied to `x⁻¹`: the poles of `x` are the zeros of
`x⁻¹`, with `ord_Q x⁻¹ = -ord_Q x`, and `k(x⁻¹) = k(x)`. -/

lemma sum_ord_neg_eq_finrank_curve (C : Work.CurveBasics.Curve k) (x : C.functionField)
    (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField] :
    ∑ Q ∈ (C.finite_support_ordAt x).toFinset.filter (fun Q => C.ordAt x Q < 0),
        (-(C.ordAt x Q)) * (C.hom.residueDegree Q.point : ℤ)
      = (Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
          C.functionField : ℤ) := by
  have hx0 : x ≠ 0 := hx.ne_zero
  have hT : Transcendental k x⁻¹ := fun hc => hx (IsAlgebraic.inv_iff.mp hc)
  have hadj : IntermediateField.adjoin k ({x⁻¹} : Set C.functionField) =
      IntermediateField.adjoin k ({x} : Set C.functionField) := adjoin_inv_eq_adjoin
  have hfin : (Module.finrank (IntermediateField.adjoin k ({x⁻¹} : Set C.functionField))
        C.functionField : ℤ)
      = (Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
        C.functionField : ℤ) :=
    congrArg (fun E : IntermediateField k C.functionField =>
      (Module.finrank E C.functionField : ℤ)) hadj
  haveI : FiniteDimensional (IntermediateField.adjoin k ({x⁻¹} : Set C.functionField))
      C.functionField := hadj ▸ ‹FiniteDimensional
        (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField›
  have hinv : ∀ Q : C.Place, C.ordAt x⁻¹ Q = -C.ordAt x Q := fun Q =>
    Work.CurveBasics.Order.ordAt_inv C hx0 Q
  rw [← hfin, ← sum_ord_pos_eq_finrank_curve C x⁻¹ hT]
  have hsupp : (C.finite_support_ordAt x⁻¹).toFinset = (C.finite_support_ordAt x).toFinset := by
    rw [Set.Finite.toFinset_inj]
    ext Q
    simp only [Set.mem_ofPred_eq]
    rw [hinv Q]
    simp
  have hfilter : (C.finite_support_ordAt x⁻¹).toFinset.filter (fun Q => 0 < C.ordAt x⁻¹ Q)
      = (C.finite_support_ordAt x).toFinset.filter (fun Q => C.ordAt x Q < 0) := by
    rw [hsupp]
    apply Finset.filter_congr
    intro Q _
    rw [hinv Q]
    omega
  rw [hfilter]
  exact Finset.sum_congr rfl fun Q _ => by rw [hinv Q]

theorem deg_poleDivisor {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (x : C.functionField) (hx : Transcendental k x) :
    C.deg (Work.RiemannRoch.Curve.poleDivisor C x) =
      Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField := by
  haveI hfd : FiniteDimensional (IntermediateField.adjoin k ({x} : Set C.functionField))
      C.functionField := finiteDimensional_adjoin_functionField C hx
  rw [deg_poleDivisor_eq_sum C x]
  exact sum_ord_neg_eq_finrank_curve C x hx

end

end Work.RiemannRoch.Pole
