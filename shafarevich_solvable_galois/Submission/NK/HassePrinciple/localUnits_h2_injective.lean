import Mathlib
import Submission.NK.HassePrinciple.LocalUnits
import Submission.NK.HassePrinciple.LocalUnitsSub
import Submission.NK.HassePrinciple.IdelesLevel
import Submission.NK.HassePrinciple.IdeleCocycle

open scoped NumberField
open NumberField IsDedekindDomain
open CategoryTheory Representation

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

namespace NK.HassePrinciple

open NK.GlobalCFT

attribute [local instance 10000] Rep.hV2 Rep.hV1

/-! ## The valuation of the completed local field -/

/-- The valuation of an element of the completed local field, as an integer. -/
noncomputable def adicVal (L : Type) [Field L] [NumberField L]
    (q : HeightOneSpectrum (𝓞 L)) (x : q.adicCompletion L) : ℤ :=
  WithZero.log (Valued.v x)

theorem adicVal_exp {L : Type} [Field L] [NumberField L] (q : HeightOneSpectrum (𝓞 L))
    (u : (q.adicCompletion L)ˣ) :
    WithZero.exp (adicVal L q (u : q.adicCompletion L)) = Valued.v (u : q.adicCompletion L) := by
  rw [adicVal, WithZero.exp_log]
  exact (Valuation.ne_zero_iff Valued.v).mpr (Units.ne_zero u)

theorem adicVal_mul {L : Type} [Field L] [NumberField L] (q : HeightOneSpectrum (𝓞 L))
    (u v : (q.adicCompletion L)ˣ) :
    adicVal L q ((u * v : (q.adicCompletion L)ˣ) : q.adicCompletion L)
      = adicVal L q (u : q.adicCompletion L) + adicVal L q (v : q.adicCompletion L) := by
  rw [adicVal, adicVal, adicVal, Units.val_mul, map_mul, WithZero.log_mul]
  · exact (Valuation.ne_zero_iff Valued.v).mpr (Units.ne_zero u)
  · exact (Valuation.ne_zero_iff Valued.v).mpr (Units.ne_zero v)

theorem adicVal_one {L : Type} [Field L] [NumberField L] (q : HeightOneSpectrum (𝓞 L)) :
    adicVal L q ((1 : (q.adicCompletion L)ˣ) : q.adicCompletion L) = 0 := by
  rw [adicVal, Units.val_one, map_one, WithZero.log_one]

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## Equivariance of the valuation under the decomposition group -/

/-- Transport of the valuation along an equality of finite places. -/
theorem valued_cast_ofFinite {q q' : HeightOneSpectrum (𝓞 L)}
    (h : Place.ofFinite q' = Place.ofFinite q) (z : q'.adicCompletion L) :
    Valued.v ((RingEquiv.cast (R := fun v : Place L => Place.localField L v) h z) :
        Place.localField L (Place.ofFinite q)) = Valued.v z := by
  cases h
  rfl

/-- The local automorphisms preserve the valuation. -/
theorem localAut_valued_ofFinite (q : HeightOneSpectrum (𝓞 L))
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) (Place.ofFinite q)) (y : q.adicCompletion L) :
    Valued.v (localAut (Place.ofFinite q) σ y) = Valued.v y := by
  rw [localAut_apply]
  have h := NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv_valued (K := K) σ.1 q y
  rw [show (RingEquiv.cast (R := fun v : Place L => Place.localField L v)
        (MulAction.mem_stabilizer_iff.mp σ.2))
      (Place.localRingEquiv σ.1 (Place.ofFinite q) y)
      = (RingEquiv.cast (R := fun v : Place L => Place.localField L v)
        (MulAction.mem_stabilizer_iff.mp σ.2))
        (NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv σ.1 q y) from rfl]
  rw [valued_cast_ofFinite]
  exact h

/-- The valuation is invariant under the action of the decomposition group on the local units. -/
theorem localUnitsEquiv_valued (q : HeightOneSpectrum (𝓞 L))
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) (Place.ofFinite q))
    (u : (q.adicCompletion L)ˣ) :
    Valued.v ((localUnitsEquiv (K := K) (Place.ofFinite q) σ u :
        (q.adicCompletion L)ˣ) : q.adicCompletion L)
      = Valued.v (u : q.adicCompletion L) := by
  rw [coe_localUnitsEquiv]
  exact localAut_valued_ofFinite q σ (u : q.adicCompletion L)

theorem adicVal_localUnitsEquiv (q : HeightOneSpectrum (𝓞 L))
    (σ : MulAction.stabilizer (L ≃ₐ[K] L) (Place.ofFinite q)) (u : (q.adicCompletion L)ˣ) :
    adicVal L q (((localUnitsEquiv (K := K) (Place.ofFinite q) σ u :
      (q.adicCompletion L)ˣ) : q.adicCompletion L)) = adicVal L q (u : q.adicCompletion L) :=
  congrArg WithZero.log (localUnitsEquiv_valued (K := K) q σ u)

/-! ## The valuation as a morphism of representations -/

/-- The valuation as an additive homomorphism on the local units. -/
noncomputable def valUnitsAddHom (L : Type) [Field L] [NumberField L]
    (q : HeightOneSpectrum (𝓞 L)) : Additive ((q.adicCompletion L)ˣ) →+ CoeffInt where
  toFun u := ULift.up (adicVal L q (((Additive.toMul u) : (q.adicCompletion L)ˣ) :
    q.adicCompletion L))
  map_zero' := by
    show ULift.up (adicVal L q (((Additive.toMul (0 : Additive ((q.adicCompletion L)ˣ))) :
      (q.adicCompletion L)ˣ) : q.adicCompletion L)) = 0
    rw [toMul_zero, adicVal_one]
    rfl
  map_add' u v := by
    show ULift.up (adicVal L q (((Additive.toMul (u + v)) : (q.adicCompletion L)ˣ) :
      q.adicCompletion L))
      = ULift.up (adicVal L q (((Additive.toMul u) : (q.adicCompletion L)ˣ) :
          q.adicCompletion L))
        + ULift.up (adicVal L q (((Additive.toMul v) : (q.adicCompletion L)ˣ) :
          q.adicCompletion L))
    rw [toMul_add, adicVal_mul]
    rfl

theorem valUnitsAddHom_apply {L : Type} [Field L] [NumberField L]
    (q : HeightOneSpectrum (𝓞 L)) (u : Additive ((q.adicCompletion L)ˣ)) :
    valUnitsAddHom L q u
      = ULift.up (adicVal L q (((Additive.toMul u) : (q.adicCompletion L)ˣ) :
          q.adicCompletion L)) := rfl

/-- **The valuation morphism** from the local units at a finite place to the trivial
representation on `ℤ` (the quotient of `L_qˣ` by its units). -/
noncomputable def localUnitsValHom (q : HeightOneSpectrum (𝓞 L)) :
    localUnitsRep K L (Place.ofFinite q) ⟶
      Rep.trivial CoeffInt (MulAction.stabilizer (L ≃ₐ[K] L) (Place.ofFinite q)) CoeffInt :=
  Rep.ofHom
    { toFun := valUnitsAddHom L q
      map_add' := map_add _
      map_smul' := fun n x => by
        obtain ⟨z⟩ := n
        exact AddMonoidHom.map_zsmul (valUnitsAddHom L q) z x
      isIntertwining' := fun σ => by
        apply LinearMap.ext
        intro x
        show valUnitsAddHom L q
            (localUnitsEquiv (K := K) (Place.ofFinite q) σ (Additive.toMul x) |> Additive.ofMul)
          = valUnitsAddHom L q x
        rw [valUnitsAddHom_apply, valUnitsAddHom_apply]
        congr 1
        simp only [toMul_ofMul]
        exact adicVal_localUnitsEquiv (K := K) q σ (Additive.toMul x) }

/-! ## Exactness of `0 → 𝒪_qˣ → L_qˣ → ℤ → 0` -/

theorem mem_localUnits_iff_adicVal_eq_zero {L : Type} [Field L] [NumberField L]
    (q : HeightOneSpectrum (𝓞 L)) (u : (q.adicCompletion L)ˣ) :
    u ∈ Place.localUnits L (Place.ofFinite q) ↔ adicVal L q (u : q.adicCompletion L) = 0 := by
  rw [Place.mem_localUnits_ofFinite_iff_valued_eq_one, adicVal]
  constructor
  · intro h; rw [h, WithZero.log_one]
  · intro h
    have h1 : WithZero.exp (WithZero.log (Valued.v ((u : (q.adicCompletion L)ˣ) :
        q.adicCompletion L))) = WithZero.exp 0 := by rw [h, WithZero.exp_zero]
    rw [WithZero.exp_log ((Valuation.ne_zero_iff Valued.v).mpr (Units.ne_zero u))] at h1
    simpa using h1

theorem valUnitsAddHom_incl_eq_zero (q : HeightOneSpectrum (𝓞 L))
    (u : ↥(Place.localUnits L (Place.ofFinite q))) :
    valUnitsAddHom L q (Additive.ofMul ((u : (q.adicCompletion L)ˣ))) = (0 : CoeffInt) := by
  rw [valUnitsAddHom_apply, toMul_ofMul,
    (mem_localUnits_iff_adicVal_eq_zero q (u : (q.adicCompletion L)ˣ)).mp u.2]
  rfl

theorem valUnitsAddHom_eq_zero_iff (q : HeightOneSpectrum (𝓞 L))
    (u : (q.adicCompletion L)ˣ) :
    valUnitsAddHom L q (Additive.ofMul u) = 0 ↔ adicVal L q (u : q.adicCompletion L) = 0 := by
  rw [valUnitsAddHom_apply, toMul_ofMul]
  constructor
  · intro h
    have h' := congrArg ULift.down h
    simpa using h'
  · intro h; rw [h]; rfl

theorem localUnitsIncl_comp_valHom (q : HeightOneSpectrum (𝓞 L)) :
    localUnitsIncl (K := K) (L := L) (Place.ofFinite q) ≫ localUnitsValHom (K := K) (L := L) q
      = 0 := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  change valUnitsAddHom L q
      (Additive.ofMul (((Additive.toMul x : ↥(Place.localUnits L (Place.ofFinite q))) :
        (q.adicCompletion L)ˣ))) = (0 : CoeffInt)
  exact valUnitsAddHom_incl_eq_zero q (Additive.toMul x : ↥(Place.localUnits L (Place.ofFinite q)))

theorem valUnitsAddHom_surjective {L : Type} [Field L] [NumberField L]
    (q : HeightOneSpectrum (𝓞 L)) :
    Function.Surjective (valUnitsAddHom L q) := by
  intro c
  obtain ⟨m, rfl⟩ : ∃ m : ℤ, c = ULift.up m := ⟨c.down, by simp⟩
  obtain ⟨y, hy⟩ := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_surjective L q
    (WithZero.exp m)
  have hy0 : y ≠ 0 := (Valuation.ne_zero_iff Valued.v).mp (by rw [hy]; exact WithZero.exp_ne_zero)
  refine ⟨Additive.ofMul (Units.mk0 y hy0), ?_⟩
  rw [valUnitsAddHom_apply, toMul_ofMul, adicVal, Units.val_mk0, hy, WithZero.log_exp]

theorem localUnitsValHom_surjective (q : HeightOneSpectrum (𝓞 L)) :
    Function.Surjective (localUnitsValHom (K := K) (L := L) q).hom :=
  valUnitsAddHom_surjective q

theorem localUnitsIncl_injective (q : HeightOneSpectrum (𝓞 L)) :
    Function.Injective (localUnitsIncl (K := K) (L := L) (Place.ofFinite q)).hom := by
  intro a b h
  change Additive.ofMul ((Additive.toMul a : ↥(Place.localUnits L (Place.ofFinite q))) :
      (q.adicCompletion L)ˣ)
    = Additive.ofMul ((Additive.toMul b : ↥(Place.localUnits L (Place.ofFinite q))) :
      (q.adicCompletion L)ˣ) at h
  exact Additive.toMul.injective
    (Subtype.val_injective (Additive.ofMul.injective h))

theorem localUnitsIncl_ofMul_apply (q : HeightOneSpectrum (𝓞 L))
    (u : ↥(Place.localUnits L (Place.ofFinite q))) :
    (localUnitsIncl (K := K) (L := L) (Place.ofFinite q)).hom
        (Additive.ofMul u : (localUnitsSubRep K L (Place.ofFinite q)).V)
      = Additive.ofMul (Subtype.val u) := rfl

/-- **The short exact sequence** `0 → 𝒪_qˣ → L_qˣ → ℤ → 0` of representations of the
decomposition group of `q`. -/
noncomputable def localUnitsShortComplex (q : HeightOneSpectrum (𝓞 L)) :
    ShortComplex (Rep CoeffInt (MulAction.stabilizer (L ≃ₐ[K] L) (Place.ofFinite q))) :=
  ShortComplex.mk (localUnitsIncl (K := K) (L := L) (Place.ofFinite q))
    (localUnitsValHom (K := K) (L := L) q) (localUnitsIncl_comp_valHom (K := K) q)

set_option backward.isDefEq.respectTransparency false in
theorem localUnitsShortComplex_shortExact (q : HeightOneSpectrum (𝓞 L)) :
    (localUnitsShortComplex (K := K) (L := L) q).ShortExact where
  exact := (forget₂ (Rep CoeffInt (MulAction.stabilizer (L ≃ₐ[K] L) (Place.ofFinite q)))
      (ModuleCat CoeffInt)) |>.reflects_exact_of_faithful _
      ((ShortComplex.moduleCat_exact_iff _).2 fun x hx => by
        have hx'' : valUnitsAddHom L q x = 0 := hx
        have h3 : valUnitsAddHom L q
            (Additive.ofMul ((Additive.toMul x : (q.adicCompletion L)ˣ))) = 0 := by
          rw [show (Additive.ofMul ((Additive.toMul x : (q.adicCompletion L)ˣ)) :
            Additive ((q.adicCompletion L)ˣ)) = x from rfl]
          exact hx''
        have hmem : ((Additive.toMul x : (Place.localField L (Place.ofFinite q))ˣ)) ∈
            Place.localUnits L (Place.ofFinite q) :=
          (mem_localUnits_iff_adicVal_eq_zero q _).mpr ((valUnitsAddHom_eq_zero_iff q _).mp h3)
        refine ⟨Additive.ofMul (⟨(Additive.toMul x : (Place.localField L (Place.ofFinite q))ˣ),
          hmem⟩ : ↥(Place.localUnits L (Place.ofFinite q))), ?_⟩
        · rfl)
  mono_f := (Rep.mono_iff_injective _).2 (localUnitsIncl_injective (K := K) q)
  epi_g := (Rep.epi_iff_surjective _).2 (localUnitsValHom_surjective (K := K) q)

/-! ## The order of a finite group kills `H¹` of the trivial representation on `ℤ` -/

theorem nsmul_orderOf_ofMul_eq_zero {Γ : Type} [Group Γ] (γ : Γ) :
    (orderOf γ) • (Additive.ofMul γ) = 0 := by
  rw [← ofMul_pow, pow_orderOf_eq_one, ofMul_one]

theorem subsingleton_addHom_int {Γ : Type} [Group Γ] [Finite Γ] :
    Subsingleton (Additive Γ →+ ℤ) := by
  refine ⟨fun f g => ?_⟩
  have key : ∀ (f : Additive Γ →+ ℤ) (x : Additive Γ), f x = 0 := by
    intro f x
    have hpos : 0 < orderOf x.toMul := orderOf_pos x.toMul
    have h1 : (orderOf x.toMul) • x = 0 := nsmul_orderOf_ofMul_eq_zero x.toMul
    have h2 : (orderOf x.toMul) • f x = 0 := by
      rw [← map_nsmul, h1, map_zero]
    have h3 : ((orderOf x.toMul : ℕ) : ℤ) * f x = 0 := by
      simpa [nsmul_eq_mul] using h2
    exact (mul_eq_zero.mp h3).resolve_left (by exact_mod_cast (ne_of_gt hpos))
  exact AddMonoidHom.ext fun x => by rw [key f x, key g x]

theorem subsingleton_addHom_coeffInt {Γ : Type} [Group Γ] [Finite Γ] :
    Subsingleton (Additive Γ →+ CoeffInt) := by
  have hcoe : Function.Injective (fun f : Additive Γ →+ CoeffInt =>
      (((ULift.ringEquiv : CoeffInt ≃+* ℤ).toAddEquiv.toAddMonoidHom).comp f :
        Additive Γ →+ ℤ)) := by
    intro f g hfg
    apply AddMonoidHom.ext
    intro x
    exact (ULift.ringEquiv : CoeffInt ≃+* ℤ).injective
      ((AddMonoidHom.ext_iff.mp hfg) x)
  refine ⟨fun f g => hcoe ?_⟩
  haveI := subsingleton_addHom_int (Γ := Γ)
  exact Subsingleton.elim _ _

theorem subsingleton_H1_trivial_coeffInt {Γ : Type} [Group Γ] [Finite Γ] :
    Subsingleton (groupCohomology (Rep.trivial CoeffInt Γ CoeffInt) 1) := by
  haveI : Subsingleton (Additive Γ →+ CoeffInt) := subsingleton_addHom_coeffInt
  have hinj : Function.Injective
      (groupCohomology.H1IsoOfIsTrivial (Rep.trivial CoeffInt Γ CoeffInt)).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  exact ⟨fun a b => hinj (Subsingleton.elim _ _)⟩

/-! ## Injectivity of `H²` along a short exact sequence of coefficients -/

theorem h2_map_injective_of_shortExact {Γ : Type} [Group Γ]
    (S : ShortComplex (Rep CoeffInt Γ)) (hS : S.ShortExact)
    (h1 : Subsingleton (groupCohomology S.X₃ 1)) :
    Function.Injective
      (fun x => ((groupCohomology.functor CoeffInt Γ 2).map S.f).hom x) := by
  have hij : 1 + 1 = 2 := rfl
  have hEx := ShortComplex.Exact.moduleCat_range_eq_ker
    (groupCohomology.mapShortComplex₁_exact (k := CoeffInt) (G := Γ) hS hij)
  have hfrange : LinearMap.range (groupCohomology.mapShortComplex₁ hS hij).f.hom = ⊥ :=
    (Submodule.eq_bot_iff _).mpr fun y hy => by
      obtain ⟨z, hz⟩ := LinearMap.mem_range.mp hy
      rw [← hz, show z = 0 from h1.elim z 0, map_zero]
  have hkg : LinearMap.ker (groupCohomology.mapShortComplex₁ hS hij).g.hom = ⊥ := by
    rw [← hEx, hfrange]
  intro a b hab
  have hmem : a - b ∈ LinearMap.ker ((groupCohomology.functor CoeffInt Γ 2).map S.f).hom := by
    rw [LinearMap.mem_ker]
    have hab' : ((groupCohomology.functor CoeffInt Γ 2).map S.f).hom a
        = ((groupCohomology.functor CoeffInt Γ 2).map S.f).hom b := hab
    rw [map_sub, hab', sub_self]
  have h0 : a - b = 0 := by
    rw [show LinearMap.ker ((groupCohomology.functor CoeffInt Γ 2).map S.f).hom
        = LinearMap.ker (groupCohomology.mapShortComplex₁ hS hij).g.hom from rfl, hkg] at hmem
    exact (Submodule.mem_bot CoeffInt).mp hmem
  exact sub_eq_zero.mp h0

theorem localUnits_h2_injective_ofFinite (q : HeightOneSpectrum (𝓞 L)) :
    Function.Injective (fun x => ((groupCohomology.functor CoeffInt
      (MulAction.stabilizer (L ≃ₐ[K] L) (Place.ofFinite q)) 2).map
        (localUnitsIncl (K := K) (L := L) (Place.ofFinite q))).hom x) :=
  h2_map_injective_of_shortExact (localUnitsShortComplex (K := K) (L := L) q)
    (localUnitsShortComplex_shortExact (K := K) (L := L) q)
    (subsingleton_H1_trivial_coeffInt (Γ := MulAction.stabilizer (L ≃ₐ[K] L) (Place.ofFinite q)))

section Archimedean

/-- A morphism of representations whose underlying map is bijective induces an injective map on
cohomology. -/
theorem map_h2_injective_of_bijective {Γ : Type} [Group Γ] {A B : Rep CoeffInt Γ}
    (f : A ⟶ B) (hf : Function.Bijective f.hom) :
    Function.Injective
      (fun x => ((groupCohomology.functor CoeffInt Γ 2).map f).hom x) := by
  haveI : Mono f := (Rep.mono_iff_injective f).mpr hf.1
  haveI : Epi f := (Rep.epi_iff_surjective f).mpr hf.2
  haveI : IsIso f := CategoryTheory.isIso_of_mono_of_epi f
  haveI : IsIso ((groupCohomology.functor CoeffInt Γ 2).map f) :=
    CategoryTheory.Functor.map_isIso _ f
  exact (ModuleCat.mono_iff_injective _).mp inferInstance

theorem localUnitsIncl_bijective_ofInfinite (w : InfinitePlace L) :
    Function.Bijective (localUnitsIncl (K := K) (L := L) (Place.ofInfinite w)).hom := by
  constructor
  · intro a b h
    change Additive.ofMul ((Additive.toMul a : ↥(Place.localUnits L (Place.ofInfinite w))) :
        (Place.localField L (Place.ofInfinite w))ˣ)
      = Additive.ofMul ((Additive.toMul b : ↥(Place.localUnits L (Place.ofInfinite w))) :
        (Place.localField L (Place.ofInfinite w))ˣ) at h
    exact Additive.toMul.injective (Subtype.val_injective (Additive.ofMul.injective h))
  · intro y
    refine ⟨Additive.ofMul (⟨Additive.toMul y, Place.mem_localUnits_ofInfinite (K := L) (w := w)⟩ :
      ↥(Place.localUnits L (Place.ofInfinite w))), ?_⟩
    rfl

theorem localUnits_h2_injective_ofInfinite (w : InfinitePlace L) :
    Function.Injective (fun x => ((groupCohomology.functor CoeffInt
      (MulAction.stabilizer (L ≃ₐ[K] L) (Place.ofInfinite w)) 2).map
        (localUnitsIncl (K := K) (L := L) (Place.ofInfinite w))).hom x) :=
  map_h2_injective_of_bijective (Γ := MulAction.stabilizer (L ≃ₐ[K] L) (Place.ofInfinite w))
    (A := localUnitsSubRep K L (Place.ofInfinite w))
    (B := localUnitsRep K L (Place.ofInfinite w))
    (f := localUnitsIncl (K := K) (L := L) (Place.ofInfinite w))
    (localUnitsIncl_bijective_ofInfinite (K := K) (L := L) w)

end Archimedean

/-- **Injectivity of `H²(Γ_w, 𝒪_wˣ) ⟶ H²(Γ_w, L_wˣ)`** (local class field theory).

At an archimedean place the local units are all of `L_wˣ`, so the coefficient map is bijective and
the induced map on `H²` is an isomorphism.  At a finite place `w = ofFinite q` the argument is the
long exact sequence of the short exact sequence of `Γ_w`-representations

  `0 ⟶ 𝒪_qˣ ⟶ L_qˣ --v--> ℤ ⟶ 0`   (`Γ_w = MulAction.stabilizer (L ≃ₐ[K] L) (ofFinite q)`),

whose middle connecting map is `H¹(Γ_w, ℤ) = Hom(Γ_w, ℤ) = 0` since `Γ_w` is finite; hence
`H²(Γ_w, 𝒪_qˣ) → H²(Γ_w, L_qˣ)` has zero kernel.  The `Γ_w`-equivariance of the valuation is
`NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv_valued`. -/
theorem localUnits_h2_injective {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (w : NK.GlobalCFT.Place L) :
    Function.Injective (fun x => ((groupCohomology.functor NK.HassePrinciple.CoeffInt
      (MulAction.stabilizer (L ≃ₐ[K] L) w) 2).map
        (NK.HassePrinciple.localUnitsIncl (K := K) (L := L) w)).hom x) := by
  cases w with
  | inl w => exact localUnits_h2_injective_ofInfinite (K := K) (L := L) w
  | inr q => exact localUnits_h2_injective_ofFinite (K := K) (L := L) q

end NK.HassePrinciple
