import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.E9c.TransportDefs
import Submission.Work.SSGRoute.e7comega_defs
import Submission.Work.SSGRoute.ValuationSES.C1
import Submission.Work.SSGRoute.local_duality_ext
import Submission.Work.SSGRoute.E7cC.exists_level_unramified_p_dvd_inertiaDeg
import Submission.Work.SSGRoute.E7cOmega.ratDivSES
import Submission.Work.SSGRoute.E7cOmega.ratDivDefs
import Submission.Work.SSGRoute.ext_one_iso_divisible_cohomology
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.e9_caseB_cocycle
import Submission.Work.SSGRoute.E0bDefs
import Submission.Work.SSGRoute.eCoh_map
import Submission.Work.SSGRoute.SSGStage.detectorFixedAux
import Submission.Work.SSGRoute.SSGStage.mem_cocycles_coordKer
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
import Submission.Work.SSGRoute.Sha2Lib.indLevelDatum
import Submission.Work.SSGRoute.E7cC.detectingFunctional_indDatum
import Submission.Work.SSGRoute.E7cOmega.exists_level_detecting_functional
import Submission.Work.E7cOmega.levelPair_ratDivSES_extClass_eq_zero_iff
import Submission.Work.E7cOmega.subsingleton_ext_unitRep_ratRep
import Submission.Commons.RingTheory.Henselian.valuation_completion_liesOver
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E7cC

open CategoryTheory SSGRoute.PTExt

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

/-! ## The functional form of `Ext¹_G(M, ℤ)` for `M` of exponent `p`

The unramified detector is a statement about a class `φ ∈ Ext¹_{D_w}(res M, ℤ)`.  Every one of the
proved pieces of the route (`E7cOmega.levelPair_ratDivSES_mk0_ne_zero_iff`, the local cocycle
`SSGStage.exists_local_cocycle_detecting`, the Shapiro/level computations) is stated for a class of
the shape `φ = δ(μ) = (mk₀ μ).comp (ratDivSES).extClass` with `μ : res M ⟶ ℚ/ℤ`.

The proposition below supplies that shape: for a finite `p`-torsion module `M` and a nonzero
`φ ∈ Ext¹_G(M, ℤ)` there is a *nonzero* `μ : M ⟶ ℚ/ℤ` with `φ = δ(μ)`.  It is the long-exact-sequence
consequence of `Ext¹_G(M, ℚ) = 0` (`ℚ` is divisible, `M` is torsion) and of `Hom_G(M, ℚ) = 0`.

The statement is the one used by the `sha2_image_of_Hm2` and `SSGStage` lanes
(`Work.E7cOmega.functional_of_ext_nonzero`, `Work.SSGRoute.SSGStage.divRep_detecting_class`); the
proof below is self-contained and avoids the `ULift ℤ`-instance friction that blocks those two by
going through the *inner* linear-map type (as in the proved
`Submission/Work/E7cOmega/ext_one_unitRep_iso_divRep.lean`). -/

section FunctionalReduction

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

section HomVanishing

attribute [local instance 10000] Rep.hV2 Rep.hV1

/-- A morphism `M ⟶ ℚ` (trivial `G`-action) with `M` of exponent `p` is zero. -/
private lemma hom_ratRep_eq_zero (M : Rep.{0} Coeff G)
    (hM : ∀ m : M, p • m = 0) (f : M ⟶ Work.SSGRoute.E7cOmega.ratRep G) : f = 0 := by
  apply Rep.hom_ext
  rw [Rep.zero_hom]
  rw [Representation.IntertwiningMap.ext_iff]
  apply LinearMap.ext
  intro m
  have hz : (Rep.Hom.hom f).toLinearMap ((p : ℤ) • m) = 0 := by
    have h0 : (p : ℤ) • m = 0 := by simpa using hM m
    rw [h0, map_zero]
  have h2 := map_zsmul (Rep.Hom.hom f).toLinearMap (p : ℤ) m
  rw [h2] at hz
  exact (mul_eq_zero.mp (by rw [zsmul_eq_mul] at hz; exact hz)).resolve_left
    (by rw [Int.cast_natCast]; exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- A representation whose underlying type is a subsingleton has a subsingleton endomorphism
monoid. -/
private lemma subsingleton_self_hom_of_subsingleton (Y : Rep.{0} Coeff G)
    (h : Subsingleton Y.V) : Subsingleton (Y ⟶ Y) := by
  refine ⟨fun f g => ?_⟩
  apply Rep.hom_ext
  rw [Representation.IntertwiningMap.ext_iff]
  apply LinearMap.ext
  intro m
  exact h.elim _ _

end HomVanishing

/-- Every `Coeff`-linear map `M → ℚ` is zero when `M` has exponent `p`. -/
private lemma linearMap_ratRep_eq_zero (M : Rep.{0} Coeff G)
    (hM : ∀ m : M, p • m = 0)
    (f : M.V →ₗ[Coeff] (Work.SSGRoute.E7cOmega.ratRep G).V) : f = 0 := by
  ext m
  have hz : f ((p : ℤ) • m) = 0 := by
    have h0 : (p : ℤ) • m = 0 := by simpa using hM m
    rw [h0, map_zero]
  have h2 := map_zsmul f (p : ℤ) m
  rw [h2] at hz
  exact (mul_eq_zero.mp (by rw [zsmul_eq_mul] at hz; exact hz)).resolve_left
    (by rw [Int.cast_natCast]; exact_mod_cast (Fact.out : p.Prime).ne_zero)

/-- `Hom_ℤ(M, ℚ) = 0` (as a `Coeff`-module) for `M` of exponent `p`. -/
private lemma subsingleton_linearMap_ratRep (M : Rep.{0} Coeff G)
    (hM : ∀ m : M, p • m = 0) :
    Subsingleton (M.V →ₗ[Coeff] (Work.SSGRoute.E7cOmega.ratRep G).V) :=
  ⟨fun f g => by rw [linearMap_ratRep_eq_zero M hM f, linearMap_ratRep_eq_zero M hM g]⟩

/-- `ℚ` is divisible. -/
private lemma rat_divisible (n : ℕ) (hn : 0 < n) (y : ℚ) : ∃ x : ℚ, n • x = y := by
  have hn' : (n : ℚ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.pos_iff_ne_zero.mp hn
  exact ⟨y / n, by rw [nsmul_eq_mul, mul_div_cancel₀ (b := (n : ℚ)) y hn']⟩

/-- If the identity of `Y` is zero then every `Ext`-group with coefficients in `Y` is a
subsingleton. -/
private lemma subsingleton_ext_of_id_eq_zero {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y : C} (h : 𝟙 Y = 0) (n : ℕ) : Subsingleton (Abelian.Ext X Y n) := by
  refine ⟨fun y z => ?_⟩
  have hy : y = 0 := by rw [← Abelian.Ext.comp_mk₀_id y, h]; simp
  have hz : z = 0 := by rw [← Abelian.Ext.comp_mk₀_id z, h]; simp
  rw [hy, hz]

/-- **`Ext¹_G(M, ℚ) = 0` for `M` of exponent `p`.**  Since `ℚ` is divisible, the dictionary
`Ext¹_G(M,ℚ) ≅ H¹(G, Hom_ℤ(M,ℚ))` applies, and `Hom_ℤ(M,ℚ) = 0` because `M` is torsion while `ℚ`
is torsion-free. -/
private lemma subsingleton_ext_one_ratRep (M : Rep.{0} Coeff G)
    (hM : ∀ m : M, p • m = 0) :
    Subsingleton (Abelian.Ext M (Work.SSGRoute.E7cOmega.ratRep G) 1) := by
  obtain ⟨e₁⟩ := Work.SSGRoute.ext_one_iso_divisible_cohomology G M
    (Work.SSGRoute.E7cOmega.ratRep G) rat_divisible
  have hY : Subsingleton (Work.SSGRoute.homRep M (Work.SSGRoute.E7cOmega.ratRep G)).V :=
    show Subsingleton (M.V →ₗ[Coeff] (Work.SSGRoute.E7cOmega.ratRep G).V) from
      subsingleton_linearMap_ratRep M hM
  have h2 : Subsingleton
      (Abelian.Ext (unitRep G) (Work.SSGRoute.homRep M (Work.SSGRoute.E7cOmega.ratRep G)) 1) :=
    subsingleton_ext_of_id_eq_zero
      ((subsingleton_self_hom_of_subsingleton
        (Work.SSGRoute.homRep M (Work.SSGRoute.E7cOmega.ratRep G)) hY).elim _ _) 1
  exact ⟨fun a b => e₁.injective (h2.elim (e₁ a) (e₁ b))⟩

/-- **The connecting map `Hom_G(M, ℚ/ℤ) → Ext¹_G(M, ℤ)` is onto for `M` of exponent `p`.**

For a group `G`, a prime `p` and a `G`-module `M` killed by `p`, every nonzero class
`φ ∈ Ext¹_G(M, ℤ)` is `δ(μ) = (mk₀ μ).comp (ratDivSES).extClass` for a nonzero coefficient morphism
`μ : M ⟶ ℚ/ℤ`.  This is the `ℤ`-coefficient Tate-duality input of the unramified detector (node C6);
with it, the detector is a statement about functionals `μ`, which is the form in which the whole
`sha2`/`SSGStage` infrastructure consumes it. -/
theorem ext_one_eq_comp_ratDivSES_extClass (M : Rep.{0} Coeff G) (hM : ∀ m : M, p • m = 0)
    (φ : Abelian.Ext M (unitRep G) 1) (hφ : φ ≠ 0) :
    ∃ μ : M ⟶ Work.SSGRoute.E7cOmega.divRep G, μ ≠ 0 ∧
      φ = (Abelian.Ext.mk₀ μ).comp
        (ShortComplex.ShortExact.extClass
          (Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G))) (zero_add 1) := by
  let S := Work.SSGRoute.E7cOmega.ratDivSES (G := G)
  have hS : S.ShortExact := Work.SSGRoute.E7cOmega.ratDivSES_shortExact (G := G)
  haveI hS1 : Subsingleton (Abelian.Ext M S.X₂ 1) := subsingleton_ext_one_ratRep M hM
  have hx₁ : φ.comp (Abelian.Ext.mk₀ S.f) (add_zero 1) = 0 := Subsingleton.elim _ _
  obtain ⟨x₃, hx₃⟩ := Abelian.Ext.covariant_sequence_exact₁ M hS φ hx₁ (n₀ := 0) (zero_add 1)
  have key : ∃ μ : M ⟶ S.X₃, μ ≠ 0 ∧
      φ = (Abelian.Ext.mk₀ μ).comp hS.extClass (zero_add 1) := by
    refine ⟨Abelian.Ext.addEquiv₀ x₃, ?_, ?_⟩
    · intro hμ
      have hx₃0 : x₃ = 0 :=
        (Abelian.Ext.addEquiv₀ (X := M) (Y := S.X₃)).injective (by rw [hμ, map_zero])
      exact hφ (hx₃.symm.trans
        (by rw [hx₃0]; exact Abelian.Ext.zero_comp M 0 hS.extClass 1 (zero_add 1)))
    · rw [Abelian.Ext.mk₀_addEquiv₀_apply]
      exact hx₃.symm
  exact key

end FunctionalReduction

/-- **A nonzero cocycle value gives a nonzero pushed-forward class.**

For a group `G`, a coefficient module `A`, a `1`-cocycle `z` of `A`, a coefficient morphism
`μ : A ⟶ ℚ/ℤ` and `γ : G` with `μ (z γ) ≠ 0`, the pushforward of the class `eCoh (H1π z)` along `μ`
is nonzero.  This is the elementary form of the *detection* step at the cocycle level: the pushed
class is computed by the cocycle `γ ↦ μ (z γ)`, and in the trivial coefficient module `ℚ/ℤ` the
`1`-coboundaries vanish, so a single nonzero value already certifies the class. -/
theorem extHMap_eCoh_id_ne_zero_of_value {G : Type} [Group G] (A : Rep.{0} Coeff G)
    (z : ↥(groupCohomology.cocycles₁ A))
    (μ : A ⟶ Work.SSGRoute.E7cOmega.divRep G) (γ : G)
    (hγ : μ ((z : G → ↥A) γ) ≠ 0) :
    SSGRoute.PTExt.extHMap (MonoidHom.id G) μ
      (SSGRoute.PTExt.eCoh 1 G A ((groupCohomology.H1π A).hom z)) ≠ 0 := by
  rw [← eCoh_map (n := 1) G G (MonoidHom.id G) A (Work.SSGRoute.E7cOmega.divRep G) μ
    ((groupCohomology.H1π A).hom z)]
  intro h0
  have h1 : (groupCohomology.map (MonoidHom.id G) μ 1).hom
      ((groupCohomology.H1π A).hom z) = 0 :=
    (SSGRoute.PTExt.eCoh 1 G (Work.SSGRoute.E7cOmega.divRep G)).injective (by rw [h0, map_zero])
  rw [groupCohomology.H1π_comp_map_apply] at h1
  rw [groupCohomology.H1π_eq_zero_iff] at h1
  rw [groupCohomology.coboundaries₁_eq_bot_of_isTrivial, Submodule.mem_bot] at h1
  have h2 : ⇑((groupCohomology.mapCocycles₁ (MonoidHom.id G) μ) z) γ = 0 := congrFun h1 γ
  rw [groupCohomology.coe_mapCocycles₁] at h2
  exact hγ (by simpa using h2)

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-! ## Node C4 of the E7cΩ route: pushing a level pairing along the valuation

The unramified detector `Work.SSGRoute.E7cC.exists_unramifiedDetector` is proved by combining

* the *trivial-coefficient* detector `Work.SSGRoute.E7cC.exists_unramifiedDetector_ExtZ`
  (node C6: for a nonzero `φ ∈ Ext¹_{D_w}(res M, ℤ)` there is a level `L ⊇ K`, a place `q' | q`
  and an unramified global class `h` with `φ ∪ res_{q'} h ≠ 0`, the ramification index prime to
  `p`), applied to `φ = δy = y ≫ mk₀ (localUnitsValHom q)` — nonzero by C1
  (`Work.SSGRoute.ValuationSES.isUnramifiedExt_iff_comp_valHom`) when `y` is not unramified;

* the present file: the *valuation naturality* of `levelPair`, which turns `levelPair` at `q'` with
  the local-units coefficients into `e` times the `ℤ`-coefficient pairing value, so that
  nonvanishing transfers along `e` (prime to `p`, and everything `p`-torsion).

The key computation is `Work.SSGRoute.E7cC.localUnitsMap_comp_valHom`: the valuation of the local
algebra map on units is `e` times the valuation, which is
`Commons.RingTheory.Henselian.valuation_completion_liesOver`.
-/

/-- Scalar multiplication by a natural number in `Coeff = ULift ℤ`. -/
theorem coeff_nsmul_up (n : ℕ) (m : ℤ) :
    (n • (ULift.up m : SSGRoute.PTExt.Coeff)) = ULift.up (n * m : ℤ) := by
  apply ULift.ext
  simp [nsmul_eq_mul]

/-- The `Ext`-composition of a scalar multiple is the scalar multiple of the composition. -/
theorem nsmul_comp_coeff {G : Type} [Group G] {X Y Z : Rep.{0} SSGRoute.PTExt.Coeff G}
    {r s t : ℕ} (n : ℕ) (x : Abelian.Ext.{0} X Y r) (β : Abelian.Ext.{0} Y Z s)
    (h : r + s = t) : (n • x).comp β h = n • (x.comp β h) := by
  induction n with
  | zero => rw [zero_nsmul, Abelian.Ext.zero_comp, zero_nsmul]
  | succ k ih => rw [succ_nsmul, Abelian.Ext.add_comp, ih, succ_nsmul]

/-- **The level pairing is additive in the coefficient morphism.** -/
theorem levelPair_add_coeff {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0} SSGRoute.PTExt.Coeff G} {B : Rep.{0} SSGRoute.PTExt.Coeff H}
    (ι ι' : Rep.res f A ⟶ B) {r s : ℕ} (x : Abelian.Ext.{0} M A r)
    (h : SSGRoute.PTExt.extH (Rep.res f M) s) :
    SSGRoute.PTExt.levelPair f (ι + ι') x h
      = SSGRoute.PTExt.levelPair f ι x h + SSGRoute.PTExt.levelPair f ι' x h := by
  simp only [SSGRoute.PTExt.levelPair, Abelian.Ext.mk₀_add, Abelian.Ext.comp_add]

/-- **The level pairing is `ℕ`-linear in the coefficient morphism.** -/
theorem levelPair_nsmul_coeff {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0} SSGRoute.PTExt.Coeff G} {B : Rep.{0} SSGRoute.PTExt.Coeff H}
    (n : ℕ) (ι : Rep.res f A ⟶ B) {r s : ℕ} (x : Abelian.Ext.{0} M A r)
    (h : SSGRoute.PTExt.extH (Rep.res f M) s) :
    SSGRoute.PTExt.levelPair f (n • ι) x h = n • SSGRoute.PTExt.levelPair f ι x h := by
  induction n with
  | zero =>
      rw [zero_nsmul, zero_nsmul]
      simp only [SSGRoute.PTExt.levelPair, Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  | succ k ih =>
      rw [succ_nsmul, levelPair_add_coeff, ih, succ_nsmul]

/-- **The level pairing is `ℕ`-linear in the `Ext`-variable.** -/
theorem levelPair_nsmul_x {G H : Type} [Group G] [Group H] (f : H →* G)
    {M A : Rep.{0} SSGRoute.PTExt.Coeff G} {B : Rep.{0} SSGRoute.PTExt.Coeff H}
    (ι : Rep.res f A ⟶ B) {r s : ℕ} (n : ℕ) (x : Abelian.Ext.{0} M A r)
    (h : SSGRoute.PTExt.extH (Rep.res f M) s) :
    SSGRoute.PTExt.levelPair f ι (n • x) h = n • SSGRoute.PTExt.levelPair f ι x h := by
  induction n with
  | zero =>
      rw [zero_nsmul, zero_nsmul]
      exact SSGRoute.levelPair_zero f ι h
  | succ k ih =>
      rw [succ_nsmul, SSGRoute.levelPair_add, ih, succ_nsmul]

section Helpers

variable {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K] [Field L] [NumberField L] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional k L] [IsGalois k L]

/-- A place-level "lies over" of finite places gives the ideal-level relation. -/
theorem liesOver_asIdeal {Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    {q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)}
    (h : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite Q)) : q'.asIdeal.LiesOver Q.asIdeal := by
  rcases h with ⟨w', v', h1, h2, h3⟩ | ⟨q, Q', h1, h2, h3⟩
  · exact (Sum.inr_ne_inl h1).elim
  · obtain rfl : q' = q := Sum.inr_injective h1
    obtain rfl : Q = Q' := Sum.inr_injective h2
    exact h3

/-- **The local algebra map at finite places, unfolded.** -/
theorem localAlgebraMapUnits_ofFinite
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite Q)) :
    NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
        (NK.GlobalCFT.Place.ofFinite Q) hq'
      = Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q'
          (liesOver_asIdeal hq')).toMonoidHom := by
  simp only [NK.GlobalCFT.Place.localAlgebraMapUnits]
  rw [dif_pos (liesOver_asIdeal hq')]

/-- **The valuation of the local algebra map.**  For a finite place `q'` of `L` over a finite place
`Q` of `K` and a local unit `u` of `K_Q`, the valuation of its image in `L_{q'}` is `e(q'/Q)` times
its valuation.  This is the `adicVal` form of
`Commons.RingTheory.Henselian.valuation_completion_liesOver`. -/
theorem adicVal_localAlgebraMapUnits
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite Q))
    (u : (Q.adicCompletion K)ˣ) :
    NK.HassePrinciple.adicVal L q'
        (((NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
            (NK.GlobalCFT.Place.ofFinite Q) hq' u : (q'.adicCompletion L)ˣ) :
          q'.adicCompletion L))
      = (Q.asIdeal.ramificationIdx' q'.asIdeal) *
          NK.HassePrinciple.adicVal K Q (u : Q.adicCompletion K) := by
  have hv := Commons.RingTheory.Henselian.valuation_completion_liesOver Q q' (liesOver_asIdeal hq')
    (u : Q.adicCompletion K)
  have hv' : Valued.v (((NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite Q) hq' u : (q'.adicCompletion L)ˣ) : q'.adicCompletion L))
      = (Valued.v (u : Q.adicCompletion K)) ^ (Q.asIdeal.ramificationIdx' q'.asIdeal) := by
    rw [localAlgebraMapUnits_ofFinite, Units.coe_map]
    exact hv
  rw [NK.HassePrinciple.adicVal, NK.HassePrinciple.adicVal, hv', WithZero.log_pow, nsmul_eq_mul]

/-- **The valuation of the local units map.**  For a level pair `K ⊆ L` and finite places `q' | q`,
composing the local units map `K_qˣ → L_{q'}ˣ` with the valuation `L_{q'}ˣ → ℤ` is `e(q'/q)` times
the valuation of `K_qˣ` (transported along the decomposition-group restriction). -/
theorem localUnitsMap_comp_valHom
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite Q)) :
    (Work.SSGRoute.localUnitsMap k K L (NK.GlobalCFT.Place.ofFinite Q)
        (NK.GlobalCFT.Place.ofFinite q') hq') ≫
      (NK.HassePrinciple.localUnitsValHom (K := k) (L := L) q')
    = (Q.asIdeal.ramificationIdx' q'.asIdeal) •
        (Rep.resMap (Work.SSGRoute.decompKRestrict k K L (NK.GlobalCFT.Place.ofFinite Q)
            (NK.GlobalCFT.Place.ofFinite q') hq')
          (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) Q)) := by
  refine Rep.hom_ext ?_
  refine Representation.IntertwiningMap.ext ?_
  apply LinearMap.ext
  intro x
  change (Rep.Hom.hom (Work.SSGRoute.localUnitsMap k K L (NK.GlobalCFT.Place.ofFinite Q)
      (NK.GlobalCFT.Place.ofFinite q') hq' ≫
      NK.HassePrinciple.localUnitsValHom (K := k) (L := L) q')) x
    = (Rep.Hom.hom ((Q.asIdeal.ramificationIdx' q'.asIdeal) •
        (Rep.resMap (Work.SSGRoute.decompKRestrict k K L (NK.GlobalCFT.Place.ofFinite Q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
          (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) Q)))) x
  rw [Rep.comp_apply]
  obtain ⟨u, rfl⟩ : ∃ u, Additive.ofMul u = x := ⟨Additive.toMul x, rfl⟩
  rw [Work.SSGRoute.localUnitsMap_spec k K L (NK.GlobalCFT.Place.ofFinite Q)
    (NK.GlobalCFT.Place.ofFinite q') hq' u]
  show NK.HassePrinciple.valUnitsAddHom L q'
      (Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
        (NK.GlobalCFT.Place.ofFinite Q) hq' u))
    = (Rep.Hom.hom ((Q.asIdeal.ramificationIdx' q'.asIdeal) •
        (Rep.resMap (Work.SSGRoute.decompKRestrict k K L (NK.GlobalCFT.Place.ofFinite Q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
          (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) Q)))) (Additive.ofMul u)
  rw [Rep.nsmul_hom, Representation.IntertwiningMap.coe_nsmul]
  change NK.HassePrinciple.valUnitsAddHom L q'
      (Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
        (NK.GlobalCFT.Place.ofFinite Q) hq' u))
    = (Q.asIdeal.ramificationIdx' q'.asIdeal) •
      (NK.HassePrinciple.valUnitsAddHom K Q (Additive.ofMul u))
  rw [NK.HassePrinciple.valUnitsAddHom_apply, NK.HassePrinciple.valUnitsAddHom_apply,
    toMul_ofMul, adicVal_localAlgebraMapUnits Q q' hq' u]
  exact (coeff_nsmul_up (Q.asIdeal.ramificationIdx' q'.asIdeal)
    (NK.HassePrinciple.adicVal K Q ((Additive.toMul u : (Q.adicCompletion K)ˣ) :
      Q.adicCompletion K))).symm

end Helpers


/-! ## Only the `p`-part of the inertia matters for unramifiedness

The conclusion of the detector asks for a class `h` which is *unramified* at `q'`
(`SSGRoute.PTExt.IsUnramifiedClassAt q' h`), i.e. whose restriction to every subgroup of the
inertia group `I_{q'}(L/k)` vanishes.  This file records the elementary but useful observation
that this condition only constrains the **`p`-part** of the inertia:

* for a finite group `G` whose order is prime to `p`, every `Ext¹`-class with `p`-torsion
  coefficients vanishes — `y` is killed both by `p` (`Work.SSGRoute.ext_nsmul_p_torsion`) and by
  `|G|` (`Work.SSGRoute.extH_natCard_smul_eq_zero`), and these are coprime (Bézout);
* hence `extHRestrict D h = 0` for every subgroup `D` of order prime to `p`, and
  `IsUnramifiedClassAt q' h` is **automatic** as soon as every inertia subgroup has order prime
  to `p` (e.g. when the level has `p ∤ e(q'|q∩k)` and `K/k` is tamely ramified at `q` with
  ramification index prime to `p`).

Consequently the ramification clauses of the level constructions in every route to the detector
(`SSGRoute.SSGStage.exists_regularModule_inert_level`, the `C5` norm conditions of the E7cΩ plan)
only need to control the `p`-part of `I_{q'}`: whenever the inertia is of order prime to `p`, the
coordinate/unramifiedness conditions are vacuous.

The same pattern (`p`-torsion killed by `p` and by `|G|`) is the one used by
`Work.SSGRoute.subsingleton_extH_trivial_two_of_not_dvd_card` for `H²` with trivial `𝔽_p`
coefficients. -/

/-- **`H¹` with `p`-torsion coefficients of a finite group of order prime to `p` vanishes.**
`y` is killed by `p` (`Work.SSGRoute.ext_nsmul_p_torsion`) and by `|G|`
(`Work.SSGRoute.extH_natCard_smul_eq_zero`); since `p` and `|G|` are coprime, Bézout gives
`y = 1 • y = (a·p + b·|G|) • y = 0`. -/
theorem extH_one_eq_zero_of_coprime_card {G : Type} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime]
    (A : Rep.{0} SSGRoute.PTExt.Coeff G) (hA : ∀ a : A, p • a = 0)
    (hcop : Nat.Coprime p (Nat.card G)) (y : SSGRoute.PTExt.extH A 1) : y = 0 := by
  have hpy : p • y = 0 := Work.SSGRoute.ext_nsmul_p_torsion p hA y
  have hGy : Nat.card G • y = 0 := Work.SSGRoute.extH_natCard_smul_eq_zero A (by norm_num) y
  have hbez : (p : ℤ) * (Nat.gcdA p (Nat.card G))
      + (Nat.card G : ℤ) * (Nat.gcdB p (Nat.card G)) = 1 := by
    have h := Nat.gcd_eq_gcd_ab p (Nat.card G)
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    linarith [h]
  have hpy' : (p : ℤ) • y = 0 := by
    rw [Nat.cast_smul_eq_nsmul ℤ p]; exact hpy
  have hGy' : (Nat.card G : ℤ) • y = 0 := by
    rw [Nat.cast_smul_eq_nsmul ℤ (Nat.card G)]; exact hGy
  calc y = (1 : ℤ) • y := (one_smul _ _).symm
    _ = ((p : ℤ) * (Nat.gcdA p (Nat.card G))
          + (Nat.card G : ℤ) * (Nat.gcdB p (Nat.card G))) • y := by rw [hbez]
    _ = (Nat.gcdA p (Nat.card G)) • ((p : ℤ) • y)
          + (Nat.gcdB p (Nat.card G)) • ((Nat.card G : ℤ) • y) := by
          rw [add_smul, mul_smul, mul_smul,
            smul_comm (p : ℤ) (Nat.gcdA p (Nat.card G)) y,
            smul_comm (Nat.card G : ℤ) (Nat.gcdB p (Nat.card G)) y]
    _ = 0 := by rw [hpy', hGy']; simp

/-- The `Subsingleton` form of `extH_one_eq_zero_of_coprime_card`. -/
theorem subsingleton_extH_one_of_coprime_card {G : Type} [Group G] [Fintype G] (p : ℕ)
    [Fact p.Prime] (A : Rep.{0} SSGRoute.PTExt.Coeff G) (hA : ∀ a : A, p • a = 0)
    (hcop : Nat.Coprime p (Nat.card G)) :
    Subsingleton (SSGRoute.PTExt.extH A 1) :=
  ⟨fun a b => by
    rw [extH_one_eq_zero_of_coprime_card p A hA hcop a,
      extH_one_eq_zero_of_coprime_card p A hA hcop b]⟩

/-- **Restriction to a subgroup of order prime to `p` kills a `p`-torsion `H¹`-class.** -/
theorem extHRestrict_eq_zero_of_coprime_card {G : Type} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime]
    (A : Rep.{0} SSGRoute.PTExt.Coeff G) (hA : ∀ a : A, p • a = 0)
    (D : Subgroup G) [Fintype D] (hcop : Nat.Coprime p (Nat.card D))
    (y : SSGRoute.PTExt.extH A 1) : SSGRoute.PTExt.extHRestrict D y = 0 := by
  have hA' : ∀ a : (Rep.res D.subtype A).V, p • a = 0 := fun a => hA a
  exact subsingleton_extH_one_of_coprime_card p (Rep.res D.subtype A) hA' hcop |>.elim _ _

/-- **Unramifiedness is automatic when every inertia subgroup has order prime to `p`.**

If every subgroup `D` of `Gal(L/k)` consisting of inertia elements at `q'` has order prime to `p`,
then *every* class `h ∈ H¹(Gal(L/k), res M)` with `p`-torsion coefficients is unramified at `q'`. -/
theorem isUnramifiedClassAt_of_coprime_card {k L : Type} [Field k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L] (p : ℕ) [Fact p.Prime]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (L ≃ₐ[k] L)) (hM : ∀ m : M, p • m = 0)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hcop : ∀ D : Subgroup (L ≃ₐ[k] L),
      (∀ σ ∈ D, SSGRoute.PTExt.IsInertiaAt q' σ) → Nat.Coprime p (Nat.card D))
    (h : SSGRoute.PTExt.extH M 1) :
    SSGRoute.PTExt.IsUnramifiedClassAt q' h := by
  intro D hD
  haveI : Fintype D := Fintype.ofFinite D
  exact extHRestrict_eq_zero_of_coprime_card p M hM D (hcop D hD) h

/-- The variant of `isUnramifiedClassAt_of_coprime_card` in which the hypothesis is imposed on a
single subgroup `I` containing all the inertia elements at `q'` (e.g. the inertia group itself):
if no element of `I` has order divisible by `p`, then every `p`-torsion class is unramified at
`q'`. -/
theorem isUnramifiedClassAt_of_isInertiaAt_mem_of_coprime_card {k L : Type} [Field k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] (p : ℕ) [Fact p.Prime]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (L ≃ₐ[k] L)) (hM : ∀ m : M, p • m = 0)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (I : Subgroup (L ≃ₐ[k] L)) (hI : ∀ σ : L ≃ₐ[k] L, SSGRoute.PTExt.IsInertiaAt q' σ → σ ∈ I)
    (hcop : Nat.Coprime p (Nat.card I)) (h : SSGRoute.PTExt.extH M 1) :
    SSGRoute.PTExt.IsUnramifiedClassAt q' h := by
  refine isUnramifiedClassAt_of_coprime_card p M hM q' (fun D hD => ?_) h
  have hDI : D ≤ I := fun σ hσ => hI σ (hD σ hσ)
  haveI : Fintype D := Fintype.ofFinite D
  haveI : Fintype I := Fintype.ofFinite I
  exact hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hDI)


/-- **A class whose defining cocycle vanishes on the inertia is unramified.**

This is the "unramifiedness half" of the detector's algebraic part: the class
`h = eCoh 1 G A (H1π A z)` of a 1-cocycle `z` that vanishes on every inertia element at `q'` is
unramified at `q'`.  The proof is the degree-one cocycle criterion `Work.SSGRoute.e9_caseB_cocycle`
with the testing element `m = 0` (both for the inertia group and for every subgroup of it). -/
theorem isUnramifiedClassAt_eCoh_of_vanishes_on_inertia {k L : Type} [Field k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L]
    (A : Rep.{0} Coeff (L ≃ₐ[k] L))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (z : ↥(groupCohomology.cocycles₁ A))
    (hz : ∀ γ : L ≃ₐ[k] L, SSGRoute.PTExt.IsInertiaAt q' γ → (z : (L ≃ₐ[k] L) → ↥A) γ = 0) :
    SSGRoute.PTExt.IsUnramifiedClassAt q'
      (SSGRoute.PTExt.eCoh 1 (L ≃ₐ[k] L) A ((groupCohomology.H1π A).hom z)) := by
  intro D hD
  rw [Work.SSGRoute.e9_caseB_cocycle A D z]
  refine ⟨0, fun d hd => ?_⟩
  rw [hz d (hD d hd), map_zero, sub_zero]

/-- **`(D-bridge)` at the cochain level**: a cocycle that vanishes on the inertia and has one
nonzero `μ`-value gives an unramified detecting class.

This is the composition of the two cochain-level lemmas of this file —
`isUnramifiedClassAt_eCoh_of_vanishes_on_inertia` (vanishing on the inertia makes the class
unramified) and `extHMap_eCoh_id_ne_zero_of_value` (a single nonzero value certifies the class) — in
the vocabulary in which `(D-level)` of
`E7cC/NOTE_C6_session17_level_via_weakApproximation.md` §22 delivers its witness: `(D-level)`
supplies the cocycle `z` together with a nonzero value `μ (z γ₀)`, and this lemma turns that into the
existence of an unramified class whose `μ`-pushforward is nonzero — i.e. into the detecting class of
the unramified detector. -/
theorem unramified_and_ne_zero_of_cocycle_value {k L : Type} [Field k] [Field L] [NumberField L]
    [Algebra k L] [FiniteDimensional k L]
    (A : Rep.{0} Coeff (L ≃ₐ[k] L))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (μ : A ⟶ Work.SSGRoute.E7cOmega.divRep (L ≃ₐ[k] L))
    (z : ↥(groupCohomology.cocycles₁ A))
    (hz : ∀ γ : L ≃ₐ[k] L, SSGRoute.PTExt.IsInertiaAt q' γ → (z : (L ≃ₐ[k] L) → ↥A) γ = 0)
    (γ₀ : L ≃ₐ[k] L) (hγ₀ : μ ((z : (L ≃ₐ[k] L) → ↥A) γ₀) ≠ 0) :
    SSGRoute.PTExt.IsUnramifiedClassAt q'
        (SSGRoute.PTExt.eCoh 1 (L ≃ₐ[k] L) A ((groupCohomology.H1π A).hom z)) ∧
      SSGRoute.PTExt.extHMap (MonoidHom.id (L ≃ₐ[k] L)) μ
        (SSGRoute.PTExt.eCoh 1 (L ≃ₐ[k] L) A ((groupCohomology.H1π A).hom z)) ≠ 0 :=
  ⟨isUnramifiedClassAt_eCoh_of_vanishes_on_inertia A q' z hz,
    extHMap_eCoh_id_ne_zero_of_value A z μ γ₀ hγ₀⟩

/-- **The coordinate datum of node `C6`, in the shape of the community node**
`Work.SSGRoute.E7cOmega.exists_level_detecting_functional`: for every nonzero `D_w`-equivariant
`μ : res M ⟶ ℚ/ℤ` there are a level `L ⊇ K` over `k`, a place `q' | q` with `e(q'|q)` prime to `p`,
a section `s` of `galRes k K L` and a `Gal(K/k)`-equivariant `φ` on `N = ker (galRes k K L)` which
vanishes on the inertia coordinates at `q'` and detects `μ` at the decomposition group of `q'`. -/
def CoordDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (w : NK.GlobalCFT.Place K) (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) : Prop :=
  ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
    (_ : IsGalois k ↥L)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w),
    Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
    ∃ (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
      (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ)
      (φ : Additive ((SSGRoute.PTExt.galRes k K ↥L).ker) →+ M.V),
      (∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
        φ (Additive.ofMul ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
            Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩)
          = M.ρ (SSGRoute.PTExt.galRes k K ↥L σ) (φ (Additive.ofMul g))) ∧
      (∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
        φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ)) = 0) ∧
      (∃ d : ↥L ≃ₐ[k] ↥L, d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite q') ∧
        μ.hom (φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d))) ≠ 0)

/-- **The coordinate datum produces an unramified detecting class.**
(*Duplicated* from `Work.SSGRoute.E7cOmega.exists_detecting_class_of_coord_functional` — that file
is *downstream* of this one (`Sha2Lib.unramifiedDetector` imports this module), so importing it
would create a build cycle.  The proof is the same, with the same dependencies
(`SSGStage.mem_cocycles_coordKer`, `SSGStage.detectorFixedAux`, `e9_caseB_cocycle`).)
Given a level `L ⊇ K`, a place `q' | w`, a section `s`, and a `Gal(K/k)`-equivariant `φ` on
`N = ker (galRes k K L)` vanishing on the inertia coordinates at `q'` and nonzero under `μ` at the
`N`-coordinate of some `d ∈ D_{q'}`, there is `h ∈ H¹(Gal(L/k), res M)` unramified at `q'` whose
push-forward along `μ` is nonzero at `D_{q'}`. -/
theorem coordDatum_to_unramifiedClass (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (w : NK.GlobalCFT.Place K)
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
    (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ)
    (φ : Additive ((SSGRoute.PTExt.galRes k K ↥L).ker) →+ M.V)
    (hφ : ∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
      φ (Additive.ofMul ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
          Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩)
        = M.ρ (SSGRoute.PTExt.galRes k K ↥L σ) (φ (Additive.ofMul g)))
    (h2a : ∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
      φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ)) = 0)
    (h2b : ∃ d : ↥L ≃ₐ[k] ↥L, d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q') ∧
      μ.hom (φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d))) ≠ 0) :
    ∃ h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M) 1,
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
      (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite q')) h).comp
        (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap
          (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') μ))
        (add_zero 1) ≠ 0 := by
  classical
  let A : Rep.{0} SSGRoute.PTExt.Coeff (↥L ≃ₐ[k] ↥L) :=
    Rep.res (SSGRoute.PTExt.galRes k K ↥L) M
  have hφ' : ∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
      φ (Additive.ofMul ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
          Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩)
        = A.ρ σ (φ (Additive.ofMul g)) := by
    intro σ g
    rw [hφ σ g]
    rfl
  let z : ↥(groupCohomology.cocycles₁ A) :=
    ⟨fun γ => φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ)),
      Work.SSGRoute.SSGStage.mem_cocycles_coordKer p k K Ω L M s hs φ hφ'⟩
  let h : SSGRoute.PTExt.extH A 1 :=
    SSGRoute.PTExt.eCoh 1 (↥L ≃ₐ[k] ↥L) A ((groupCohomology.H1π A).hom z)
  have hcoe : h = SSGRoute.PTExt.eCoh 1 (↥L ≃ₐ[k] ↥L) A ((groupCohomology.H1π A).hom z) := rfl
  refine ⟨h, ?_, ?_⟩
  · intro D hD
    rw [Work.SSGRoute.e9_caseB_cocycle A D z]
    refine ⟨0, fun d hd => ?_⟩
    have hR : A.ρ d (0 : ↥A) - (0 : ↥A) = (0 : ↥A) := by rw [map_zero, sub_self]
    rw [hR]
    exact h2a d (hD d hd)
  · obtain ⟨d, hdD, hdne⟩ := h2b
    intro hzero
    let D : Subgroup (↥L ≃ₐ[k] ↥L) :=
      SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')
    let B : Rep.{0} SSGRoute.PTExt.Coeff ↥D :=
      Rep.res (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        (Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    let ν : Rep.res D.subtype A ⟶ B :=
      Rep.resMap (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') μ
    haveI hB : B.IsTrivial :=
      Work.SSGRoute.SSGStage.isTrivial_res
        (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq')
        (Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    have hkey := Work.SSGRoute.SSGStage.extHRestrict_comp_mk0_eq_eCoh_map D A B ν h
    have hecoh : (SSGRoute.PTExt.eCoh 1 (↥L ≃ₐ[k] ↥L) A).symm h
        = (groupCohomology.H1π A).hom z := by
      rw [hcoe]
      exact Equiv.symm_apply_apply _ _
    rw [hecoh] at hkey
    have hw : ∃ h₀ : ↥D, ν ((z : (↥L ≃ₐ[k] ↥L) → A.V) (D.subtype h₀)) ≠ 0 := by
      refine ⟨⟨d, hdD⟩, ?_⟩
      have hν : ν ((z : (↥L ≃ₐ[k] ↥L) → A.V) (D.subtype ⟨d, hdD⟩))
          = μ.hom (φ (Additive.ofMul (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d))) := rfl
      rw [hν]
      exact hdne
    refine (Work.SSGRoute.SSGStage.eCoh_map_ne_zero D.subtype A B ν z hw) ?_
    rw [← hkey]
    exact hzero

/-- **The `h`-form detector gives the level pairing.**
(*Duplicated* from `Work.SSGRoute.E7cOmega.exists_level_unramified_detecting_class_of_functional`,
again because of the build cycle; the proof uses
`Work.E7cOmega.levelPair_ratDivSES_extClass_eq_zero_iff` and
`Work.E7cOmega.subsingleton_ext_unitRep_ratRep`, both of which are upstream.) -/
theorem levelPair_of_detectingClass (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M]
    (w : NK.GlobalCFT.Place K)
    (hdet : ∀ μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
        Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w), μ ≠ 0 →
      ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
        (_ : IsGalois k ↥L)
        (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
        (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
        (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M) 1),
        SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
        Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
            (NK.GlobalCFT.Place.ofFinite q')) h).comp
          (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap
            (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') μ))
          (add_zero 1) ≠ 0)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) (hμ : μ ≠ 0) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M) 1),
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
      Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
      SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k K ↥L w
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L w
          (NK.GlobalCFT.Place.ofFinite q') hq') SSGRoute.PTExt.Coeff)
        ((CategoryTheory.Abelian.Ext.mk₀ μ).comp
          (CategoryTheory.ShortComplex.ShortExact.extClass
            (Work.SSGRoute.E7cOmega.ratDivSES_shortExact
              (G := SSGRoute.PTExt.decompK (k := k) (K := K) w))) (zero_add 1))
        (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
          (NK.GlobalCFT.Place.ofFinite q')) h) ≠ 0 := by
  obtain ⟨L, hLnf, hLfd, hLgal, q', hq', h, hunr, hcop, hval⟩ := hdet μ hμ
  haveI : NumberField ↥L := hLnf
  haveI : FiniteDimensional k ↥L := hLfd
  haveI : IsGalois k ↥L := hLgal
  refine ⟨L, hLnf, hLfd, hLgal, q', hq', h, hunr, hcop, ?_⟩
  haveI : Fintype (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
      (NK.GlobalCFT.Place.ofFinite q')) := Fintype.ofFinite _
  refine fun hzero => hval ?_
  refine (Work.E7cOmega.levelPair_ratDivSES_extClass_eq_zero_iff
    (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') μ
    (SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
      (NK.GlobalCFT.Place.ofFinite q')) h)
    (Work.E7cOmega.subsingleton_ext_unitRep_ratRep
      (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')))).mp hzero

theorem hcrux_of_coordDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1)
    (hφ : φ ≠ 0)
    (hdet : ∀ μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
        Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w),
      μ ≠ 0 → CoordDatum p k K Ω M w μ) :
    Work.SSGRoute.Sha2Lib.DetectsAt p k K Ω w q hwq M φ := by
  classical
  -- Step 1: the coordinate datum produces an unramified detecting class, for every `μ`.
  have hdetH : ∀ μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w), μ ≠ 0 →
      ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
        (_ : IsGalois k ↥L)
        (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
        (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
        (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M) 1),
        SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
        Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
        (SSGRoute.PTExt.extHRestrict
          (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h).comp
          (CategoryTheory.Abelian.Ext.mk₀ (Rep.resMap
            (Work.SSGRoute.decompKRestrict k K ↥L w (NK.GlobalCFT.Place.ofFinite q') hq') μ))
          (add_zero 1) ≠ 0 := by
    intro μ hμ
    obtain ⟨L, hLnf, hLfd, hLgal, q', hq', hcop, s, hs, φc, heq, h2a, h2b⟩ := hdet μ hμ
    haveI : NumberField ↥L := hLnf
    haveI : FiniteDimensional k ↥L := hLfd
    haveI : IsGalois k ↥L := hLgal
    obtain ⟨h, hunr, hval⟩ :=
      coordDatum_to_unramifiedClass p k K Ω M w L q' hq' μ s hs φc heq h2a h2b
    exact ⟨L, hLnf, hLfd, hLgal, q', hq', h, hunr, hcop, hval⟩
  -- Step 1b: a nonzero `φ ∈ Ext¹_{D_w}(res M, ℤ)` is `δ(μ)` for a nonzero `μ`
  -- (this is `ext_one_eq_comp_ratDivSES_extClass`, proved in this file).
  obtain ⟨μ', hμ', hφμ⟩ := ext_one_eq_comp_ratDivSES_extClass (p := p)
    (G := SSGRoute.PTExt.decompK (k := k) (K := K) w)
    (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M) hM φ hφ
  -- Step 2: the `h`-form detector gives the level pairing with `trivResInv`.
  obtain ⟨L, hLnf, hLfd, hLgal, q', hq', h, hunr, hcop, hkey⟩ :=
    levelPair_of_detectingClass p k K Ω M w hdetH μ' hμ'
  haveI : NumberField ↥L := hLnf
  haveI : FiniteDimensional k ↥L := hLfd
  haveI : IsGalois k ↥L := hLgal
  refine ⟨L, hLnf, hLfd, hLgal, q', hq', h, hunr, ?_, ?_⟩
  · -- Step 3: `ramificationIdx` vs `ramificationIdx'`.
    have hq'' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
        (NK.GlobalCFT.Place.ofFinite q) := hwq ▸ hq'
    haveI : q'.asIdeal.LiesOver q.asIdeal := liesOver_asIdeal hq''
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (p := q.asIdeal) (q := q'.asIdeal)
      (hp := q.ne_bot)]
    exact hcop
  · rw [hφμ]
    exact hkey

/-- **The same, with the sharp (necessary and sufficient) hypothesis on `μ`.**

For the induced level of `Sha2Lib.IndLevelDatum` the detecting coordinate is `indDatumBase`, and by
Frobenius reciprocity `Hom_{G₀}(Ind_{D_w}^{G₀}𝔽_p, M) ≅ M^{D_w}` — so the exact condition for a
non-zero `μ` to be detected at that coordinate is `∃ v₀ ∈ M^{D_w}, μ v₀ ≠ 0`, *not* `p ∤ |D_w|`.
The latter is only the case in which this condition is automatic (`exists_fixed_vector_apply_ne_zero_of_not_dvd`),
which is why `hcrux_of_indLevelDatum` is the specialisation below. -/
theorem hcrux_of_indLevelDatum_sharp (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (hfix : ∀ μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
        Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w),
      μ ≠ 0 → ∃ v₀ : M.V, (∀ δ : K ≃ₐ[k] K,
          δ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w → M.ρ δ v₀ = v₀) ∧
        (Rep.Hom.hom μ) v₀ ≠ 0)
    (hlev : Work.SSGRoute.Sha2Lib.IndLevelDatum p k K Ω w q hwq) :
    ∀ φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1,
      φ ≠ 0 → Work.SSGRoute.Sha2Lib.DetectsAt p k K Ω w q hwq M φ := by
  classical
  obtain ⟨L, hLnf, hLfd, hLgal, q', hq', hcop, e, he, s, hs, hInertia, hd⟩ := hlev
  haveI : NumberField ↥L := hLnf
  haveI : FiniteDimensional k ↥L := hLfd
  haveI : IsGalois k ↥L := hLgal
  intro φ hφ
  refine hcrux_of_coordDatum p k K Ω M hM w q hwq hpq hI φ hφ (fun μ hμ => ?_)
  obtain ⟨φc, heq, hinertia, ⟨d, hdmem, hdet⟩⟩ :=
    exists_detectingFunctional_of_indLevelDatum_sharp p k K Ω M hM w L q' hq' s hs e he
      hInertia hd μ (hfix μ hμ)
  exact ⟨L, hLnf, hLfd, hLgal, q', hq', hcop, s, hs, φc, heq, hinertia, ⟨d, hdmem, hdet⟩⟩

/-! ## The `p ∤ |D_w|` case of the detector from the induced level datum

The *arithmetic* input of node `C6` in the `Sha2Lib`/`indLevelDatum` spelling is the statement
`Work.SSGRoute.Sha2Lib.IndLevelDatum`: there is a finite Galois level `L ⊇ K` over `k`, a place
`q' | w`, a `Gal(K/k)`-equivariant isomorphism `e : ker (galRes k K L) ≃* Ind_{D_w}^{G₀} 𝔽_p`, and a
splitting `s` of `galRes`, with trivial inertia coordinates and with the coordinate of some element
`d` of the decomposition group of `q'` equal to the basis vector `indDatumBase` (the indicator of
`D_w`).

`Work.SSGRoute.E7cC.exists_detectingFunctional_of_indLevelDatum` (proved in
`Submission/Work/SSGRoute/E7cC/detectingFunctional_indDatum.lean`) is the *coefficient* half of the
reduction: from such a level and a non-zero `D_w`-equivariant `μ : res M ⟶ ℚ/ℤ` it produces a
`Gal(L/k)`-equivariant `φ : N → M` vanishing on the inertia coordinates and detected by `μ` at the
coordinate of a decomposition element — **provided `p ∤ |D_w|`**, because the detection value is the
norm `μ (∑_{δ ∈ D_w} δ • m) = |D_w| · μ m`.

The theorem below assembles that half with the (already proved) halves of this file: the
factorisation of a non-zero `Ext¹`-class through `μ`, the production of the unramified class `h` from
the coordinate datum (`coordDatum_to_unramifiedClass`), and the identification of the level pairing
(`levelPair_of_detectingClass`).  It yields `DetectsAt` — hence the detector — **in the regime
`¬ p ∣ |D_w|`, modulo the single arithmetic input `IndLevelDatum`**.

For `p ∣ |D_w|` the single-coset coordinate `indDatumBase` can never detect (the norm value is
`|D_w| · μ m = 0`), and the level has to supply a coordinate supported on *several* `D_w`-cosets; the
criterion `Work.SSGRoute.HSRow.exists_equivariant_iff_detects` is stated in that regime only for the
values `μ (Φ_m c)`. -/
theorem hcrux_of_indLevelDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (hlev : Work.SSGRoute.Sha2Lib.IndLevelDatum p k K Ω w q hwq)
    (hp : ¬ p ∣ Nat.card ↥(SSGRoute.PTExt.decompK (k := k) (K := K) w)) :
    ∀ φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1,
      φ ≠ 0 → Work.SSGRoute.Sha2Lib.DetectsAt p k K Ω w q hwq M φ :=
  hcrux_of_indLevelDatum_sharp p k K Ω M hM w q hwq hpq hI
    (fun μ hμ => exists_fixed_vector_apply_ne_zero_of_not_dvd p k K M hM w hp μ hμ) hlev

/-! ## The general-coefficient level datum and its reduction

The two reductions `hcrux_of_indLevelDatum_sharp` / `hcrux_of_indLevelDatum` above consume the
*trivial-coefficient* level datum `Sha2Lib.IndLevelDatum`, whose Galois group is
`Ind_{D_w}^{G₀} 𝔽_p`.  Since `Hom_{G₀}(Ind_{D_w}^{G₀} 𝔽_p, M) ≅ M^{D_w}`, such a level can only
detect those `μ` which do not vanish on the `D_w`-fixed part of `M` — in the notation of
`HCruxOfIndLevelDatumSharp`, the clause `hfix`.  For the node itself `μ` is an arbitrary non-zero
functional, so the level has to carry the *coefficients* `M`: the Galois group is

  `N = ker (galRes k K L) ≅ Ind_{D_w}^{G₀} (res_{D_w} M) = detectorInd k K w M`,

and the detecting map is the **counit** `ε : detectorInd k K w M ⟶ M` of the adjunction
`Ind_{D_w}^{G₀} ⊣ res_{D_w}` (`Rep.indResAdjunction`), which *satisfies* `ε (⟦1 ⊗ₜ v⟧) = v` and hence
detects **every** non-zero `μ` at the single tensor `⟦1 ⊗ₜ v₀⟧` — no hypothesis on `D_w` at all.

`DetectorIndDatum` below is exactly this arithmetic input (level, place `q' | w` of coprime
ramification index, the `G₀`-equivariant isomorphism `e`, a splitting `s` with trivial inertia
coordinates, and a decomposition element `d ∈ D_{q'}` whose `e`-coordinate is `ε`-preimage of a `v₀`
with `μ v₀ ≠ 0`); `coordDatum_of_detectorIndDatum` turns it into the `CoordDatum` of this file, and
`hcrux_of_detectorIndDatum` into the whole node — this time for *arbitrary* `μ`, with no hypothesis
on `|D_w|`. -/

/-- **The counit of the adjunction `Ind_{D_w}^{G₀} ⊣ res_{D_w}` at the coefficients `M`.**  An
additive, `G₀`-equivariant surjection `detectorInd k K w M ⟶ M`; on the tensor
`Representation.IndV.mk 1 v = ⟦1 ⊗ₜ v⟧` it is the identity, `ε ⟦1 ⊗ₜ v⟧ = v`. -/
noncomputable def detectorIndCounit (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    Work.SSGRoute.Sha2Lib.detectorInd k K w M ⟶ M :=
  (Rep.indResAdjunction SSGRoute.PTExt.Coeff
    (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype).counit.app M

/-- **The general-coefficient (`Shapiro`) level datum.**  For the given `D_w`-equivariant and
non-zero `μ : res_{D_w} M ⟶ ℚ/ℤ` there are a finite Galois level `L ⊇ K` over `k`, a place `q' | w`
whose ramification index over `q` is prime to `p`, a `Gal(K/k)`-equivariant isomorphism
`e : ker (galRes k K L) ≃* Ind_{D_w}^{G₀} (res_{D_w} M)` intertwining conjugation with the `G₀`-action
of the induced module, a splitting `s` of `galRes` whose coordinates over the inertia of `q'` are
trivial, and an element `d` of the decomposition group of `q'` whose `e`-coordinate is mapped by the
counit `ε` to an element `v₀` with `μ v₀ ≠ 0`.

Note that the detecting element `d` is *not* required to be the Frobenius: the coordinate
`coordKer d` ranges over the coset `n_η^{-1}⟨Frob⟩` as the splitting varies, and it is this freedom
which makes the clause satisfiable for every non-zero `μ` (for `v₀ ∈ M^{D_w}` one may also use the
Frobenius itself). -/
def DetectorIndDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (w : NK.GlobalCFT.Place K) (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) : Prop :=
  ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
    (_ : IsGalois k ↥L)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w),
    Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
    ∃ e : (SSGRoute.PTExt.galRes k K ↥L).ker ≃*
        Multiplicative (Work.SSGRoute.Sha2Lib.detectorInd k K w M).V,
      (∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
        e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
            Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩
          = Multiplicative.ofAdd ((Work.SSGRoute.Sha2Lib.detectorInd k K w M).ρ
              (SSGRoute.PTExt.galRes k K ↥L σ) (e g).toAdd)) ∧
      ∃ (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
        (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ),
        (∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
          Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ = 1) ∧
        (∃ v₀ : M.V, μ.hom v₀ ≠ 0 ∧
          ∃ d : ↥L ≃ₐ[k] ↥L,
            d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') ∧
            (detectorIndCounit k K w M).hom
              ((e (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d)).toAdd) = v₀)

/-- **The general-coefficient level datum yields the coordinate datum.**  The detecting functional is
the composite `φ = ε ∘ e` (with `ε` the counit `detectorInd k K w M ⟶ M`); it is `G₀`-equivariant
because both `e` and `ε` are, it annihilates the inertia coordinates because they are trivial, and it
takes the value `v₀` at the coordinate of `d ∈ D_{q'}`. -/
theorem coordDatum_of_detectorIndDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (w : NK.GlobalCFT.Place K)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (hdat : DetectorIndDatum p k K Ω M w μ) :
    CoordDatum p k K Ω M w μ := by
  classical
  obtain ⟨L, hLnf, hLfd, hLgal, q', hq', hcop, e, hee, s, hs, hIin, v₀, hμv₀, d, hdmem, hdv⟩ := hdat
  haveI : NumberField ↥L := hLnf
  haveI : FiniteDimensional k ↥L := hLfd
  haveI : IsGalois k ↥L := hLgal
  -- the detecting additive map `φ = ε ∘ e`
  let φ : Additive ((SSGRoute.PTExt.galRes k K ↥L).ker) →+ M.V :=
    { toFun := fun x => (detectorIndCounit k K w M).hom (e (Additive.toMul x)).toAdd
      map_zero' := by simp
      map_add' := by
        intro x y
        have h1 : Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y := rfl
        have h2 : e (Additive.toMul (x + y)) = e (Additive.toMul x) * e (Additive.toMul y) := by
          rw [h1, map_mul]
        have h3 : Multiplicative.toAdd (e (Additive.toMul x) * e (Additive.toMul y))
            = Multiplicative.toAdd (e (Additive.toMul x))
              + Multiplicative.toAdd (e (Additive.toMul y)) := rfl
        show (detectorIndCounit k K w M).hom
            (Multiplicative.toAdd (e (Additive.toMul (x + y))))
          = (detectorIndCounit k K w M).hom (Multiplicative.toAdd (e (Additive.toMul x)))
            + (detectorIndCounit k K w M).hom (Multiplicative.toAdd (e (Additive.toMul y)))
        rw [h2, h3, map_add] }
  refine ⟨L, hLnf, hLfd, hLgal, q', hq', hcop, s, hs, φ, ?_, ?_, d, hdmem, ?_⟩
  · -- equivariance of `φ` under conjugation
    intro σ g
    have hstep : (e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
        Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩).toAdd
        = (Work.SSGRoute.Sha2Lib.detectorInd k K w M).ρ
            (SSGRoute.PTExt.galRes k K ↥L σ) (e g).toAdd := by
      rw [hee σ g]
      rfl
    show (detectorIndCounit k K w M).hom
        ((e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
          Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩).toAdd)
      = M.ρ (SSGRoute.PTExt.galRes k K ↥L σ)
          ((detectorIndCounit k K w M).hom (e g).toAdd)
    rw [hstep]
    exact Rep.hom_comm_apply (detectorIndCounit k K w M)
      (SSGRoute.PTExt.galRes k K ↥L σ) (e g).toAdd
  · -- the inertia coordinates are killed
    intro γ hγ
    show (detectorIndCounit k K w M).hom
      ((e (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ)).toAdd) = 0
    rw [hIin γ hγ]
    simp
  · -- the detecting value
    show μ.hom ((detectorIndCounit k K w M).hom
      ((e (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d)).toAdd)) ≠ 0
    rw [hdv]
    exact hμv₀

/-- **The whole node from the general-coefficient level datum.**  With
`DetectorIndDatum` available for every non-zero `μ`, `hcrux_of_coordDatum` produces
`DetectsAt` for every non-zero `φ` — hence the node `Work.SSGRoute.E7cC.exists_unramifiedDetector`,
with no hypothesis on `|D_w|` and with `μ` arbitrary. -/
theorem hcrux_of_detectorIndDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (hdat : ∀ μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
        Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w),
      μ ≠ 0 → DetectorIndDatum p k K Ω M w μ) :
    ∀ φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1,
      φ ≠ 0 → Work.SSGRoute.Sha2Lib.DetectsAt p k K Ω w q hwq M φ :=
  fun φ hφ => hcrux_of_coordDatum p k K Ω M hM w q hwq hpq hI φ hφ
    (fun μ hμ => coordDatum_of_detectorIndDatum p k K Ω M w μ (hdat μ hμ))

/-! ## The Kummer-shaped level datum (`N ≅ M`) and its reduction

The datum above is the `Shapiro` shape.  A second, *narrower* shape is the Kummer one, in which the
Galois group of the level over `K` is `M` itself,

  `e : ker (galRes k K L) ≃* Multiplicative M.V`  (`G₀`-equivariantly),

and the detecting functional is simply `e` itself.  It is this shape that the Kummer construction
delivers (realising `M^∨` inside `K^×/K^×p` and invoking Kummer theory), and — as the note
`NOTE_C6_session21_detectorInd_and_kummer_module.md` records — it is *sufficient*: the element
`d ∈ D_{q'}` may be taken of the form `s(τ)n^{-1}`, and the coordinate `coordKer d = n` then ranges
over the coset `n_τ · ker(Σ_{δ ∈ D_w/I_w} δ)`, whose elements are detected as soon as `μ ≠ 0`
(the norm obstruction `μ (M^{D_w}) = 0` can only occur when `p ∣ f(w/l)`, and then the norm has no
non-zero constraints). -/

/-- **The Kummer-shaped level datum: `ker (galRes k K L)` is the coefficient module `M`.**  There
are a finite Galois level `L ⊇ K` over `k`, a place `q' | w` with `e(q'|q)` prime to `p`, a
`Gal(K/k)`-equivariant isomorphism `e : ker (galRes k K L) ≃* Multiplicative M.V` (conjugation on
the kernel corresponding to the `G₀`-action on `M`), a splitting `s` of `galRes` with trivial
inertia coordinates, and an element `d` of the decomposition group of `q'` whose coordinate is
mapped by `e` onto an element `v₀` with `μ v₀ ≠ 0`. -/
def ModuleLevelDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (w : NK.GlobalCFT.Place K) (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) : Prop :=
  ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
    (_ : IsGalois k ↥L)
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w),
    Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p ∧
    ∃ e : (SSGRoute.PTExt.galRes k K ↥L).ker ≃* Multiplicative M.V,
      (∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
        e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
            Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩
          = Multiplicative.ofAdd (M.ρ (SSGRoute.PTExt.galRes k K ↥L σ) (e g).toAdd)) ∧
      ∃ (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
        (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ),
        (∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
          Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ = 1) ∧
        (∃ d : ↥L ≃ₐ[k] ↥L,
          d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') ∧
          μ.hom (e (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs d)).toAdd ≠ 0)

/-- **The Kummer-shaped level datum yields the coordinate datum**, with detecting functional `φ = e`
itself. -/
theorem coordDatum_of_moduleLevelDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (w : NK.GlobalCFT.Place K)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (hdat : ModuleLevelDatum p k K Ω M w μ) :
    CoordDatum p k K Ω M w μ := by
  classical
  obtain ⟨L, hLnf, hLfd, hLgal, q', hq', hcop, e, hee, s, hs, hIin, d, hdmem, hdv⟩ := hdat
  haveI : NumberField ↥L := hLnf
  haveI : FiniteDimensional k ↥L := hLfd
  haveI : IsGalois k ↥L := hLgal
  let φ : Additive ((SSGRoute.PTExt.galRes k K ↥L).ker) →+ M.V :=
    { toFun := fun x => (e (Additive.toMul x)).toAdd
      map_zero' := by simp
      map_add' := by
        intro x y
        have h1 : Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y := rfl
        have h2 : e (Additive.toMul (x + y)) = e (Additive.toMul x) * e (Additive.toMul y) := by
          rw [h1, map_mul]
        show (e (Additive.toMul (x + y))).toAdd
          = (e (Additive.toMul x)).toAdd + (e (Additive.toMul y)).toAdd
        rw [h2]
        rfl }
  refine ⟨L, hLnf, hLfd, hLgal, q', hq', hcop, s, hs, φ, ?_, ?_, d, hdmem, hdv⟩
  · intro σ g
    have hstep : e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
        Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩
        = Multiplicative.ofAdd (M.ρ (SSGRoute.PTExt.galRes k K ↥L σ) (e g).toAdd) := hee σ g
    show (e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
        Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩).toAdd
      = M.ρ (SSGRoute.PTExt.galRes k K ↥L σ) ((e g).toAdd)
    rw [hstep]
    rfl
  · intro γ hγ
    show (e (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ)).toAdd = 0
    rw [hIin γ hγ]
    simp

/-- **The whole node from the Kummer-shaped level datum.** -/
theorem hcrux_of_moduleLevelDatum (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (hdat : ∀ μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
        Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w),
      μ ≠ 0 → ModuleLevelDatum p k K Ω M w μ) :
    ∀ φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K) w)) 1,
      φ ≠ 0 → Work.SSGRoute.Sha2Lib.DetectsAt p k K Ω w q hwq M φ :=
  fun φ hφ => hcrux_of_coordDatum p k K Ω M hM w q hwq hpq hI φ hφ
    (fun μ hμ => coordDatum_of_moduleLevelDatum p k K Ω M w μ (hdat μ hμ))

/-- **The *usable* form of the detection clause: it suffices that some element of
`D_{q'} ∩ ker (galRes k K L)` is detected by `μ` through `e`.**

This is strictly weaker than the corresponding clause of `ModuleLevelDatum`: there the detected
element is required to be `coordKer d` for some `d ∈ D_{q'}`, whereas here only the *kernel* part is
tested.  The two agree on the elements of `D_{q'} ∩ ker (galRes)`, because `π d = 1` gives
`coordKer d = s 1⁻¹ · d = d`, i.e. the coordinate of an element of the inertia-kernel is the element
itself.  (This is the shape in which the arithmetic delivers the detection when the Frobenius value
`e (Frob_{q'})` is non-zero for `μ`; the general `ModuleLevelDatum` clause is needed only for the
fallback in which `μ` kills `e (D_{q'} ∩ N)` and the splitting has to be adjusted.) -/
theorem coordDatum_of_ker_detected (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (w : NK.GlobalCFT.Place K)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
    (hcop : Nat.Coprime (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) p)
    (e : (SSGRoute.PTExt.galRes k K ↥L).ker ≃* Multiplicative M.V)
    (hee : ∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
      e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
          Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩
        = Multiplicative.ofAdd (M.ρ (SSGRoute.PTExt.galRes k K ↥L σ) (e g).toAdd))
    (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
    (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ)
    (hIin : ∀ γ : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ →
      Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ = 1)
    (n : ↥L ≃ₐ[k] ↥L)
    (hnmem : n ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q'))
    (hnker : SSGRoute.PTExt.galRes k K ↥L n = 1)
    (hdet : μ.hom (e ⟨n, hnker⟩).toAdd ≠ 0) :
    CoordDatum p k K Ω M w μ := by
  classical
  let φ : Additive ((SSGRoute.PTExt.galRes k K ↥L).ker) →+ M.V :=
    { toFun := fun x => (e (Additive.toMul x)).toAdd
      map_zero' := by simp
      map_add' := by
        intro x y
        have h1 : Additive.toMul (x + y) = Additive.toMul x * Additive.toMul y := rfl
        have h2 : e (Additive.toMul (x + y)) = e (Additive.toMul x) * e (Additive.toMul y) := by
          rw [h1, map_mul]
        show (e (Additive.toMul (x + y))).toAdd
          = (e (Additive.toMul x)).toAdd + (e (Additive.toMul y)).toAdd
        rw [h2]
        rfl }
  have hcoord : Work.SSGRoute.SSGStage.coordKer k K Ω L s hs n = ⟨n, hnker⟩ := by
    apply Subtype.ext
    rw [Work.SSGRoute.SSGStage.coordKer_coe, hnker, map_one, inv_one, mul_one]
  refine ⟨L, inferInstance, inferInstance, inferInstance, q', hq', hcop, s, hs, φ, ?_, ?_,
    n, hnmem, ?_⟩
  · intro σ g
    have hstep : e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
        Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩
        = Multiplicative.ofAdd (M.ρ (SSGRoute.PTExt.galRes k K ↥L σ) (e g).toAdd) := hee σ g
    show (e ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
        Work.SSGRoute.SSGStage.ker_galRes_conj_mem p k K Ω L σ g⟩).toAdd
      = M.ρ (SSGRoute.PTExt.galRes k K ↥L σ) ((e g).toAdd)
    rw [hstep]
    rfl
  · intro γ hγ
    show (e (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs γ)).toAdd = 0
    rw [hIin γ hγ]
    simp
  · show μ.hom ((e (Work.SSGRoute.SSGStage.coordKer k K Ω L s hs n)).toAdd) ≠ 0
    rw [hcoord]
    exact hdet

/-- **The unramified detector: a non-integral local `Ext¹`-class is detected by a global class.**
This is node C6 (the risky global-realisation step) of the E7cΩ route; it is the contrapositive of the
remaining `sorry` of `Submission/Work/SSGRoute/local_phi_realization_in.lean` (clause 3).

The `Ext¹`-class `y` is not unramified, so by C1
(`Work.SSGRoute.ValuationSES.isUnramifiedExt_iff_comp_valHom`) its image
`φ = δy = y ≫ mk₀ (localUnitsValHom q)` in `Ext¹_{D_w}(res M, ℤ)` is nonzero.  Node C6
(`Work.SSGRoute.E7cC.exists_unramifiedDetector_ExtZ`) applied to `φ` produces a level `L ⊇ K`, a
place `q' | q` and an unramified global class `h` with `φ ∪ res_{q'} h ≠ 0`, the ramification index
of `q'` over `q` being prime to `p`.  Pushing the target pairing along the valuation
`L_{q'}ˣ → ℤ` then gives `e` times `φ ∪ res_{q'} h`, nonzero by `Nat.Coprime e p` (both classes are
`p`-torsion), so the target pairing itself is nonzero.  The valuation computation is
`Work.SSGRoute.E7cC.localUnitsMap_comp_valHom` (node C4), and it is what the present file proves.

The only remaining gap is the `hcrux` block below, which is node `C6` verbatim.  Its state of the
art is recorded in `Submission/Work/SSGRoute/E7cC/NOTE_C6_session18_tame_detector.md`:
`C6` is the contrapositive of clause 3 *plus* the coprimality clause; the detecting level cannot
have `L/K` unramified at `q'` unless `μ|_{M^{D_w}} ≠ 0` (`NOTE_…_session18` §2), so it must be
tamely ramified at `q'` with a ramification index `ℓ ∤ p` (§3), and — because `coordKer` needs a
section — the level has to be a *split* Galois extension of `K` over `k` containing the inertia
field `K^{I_q}` (§3bis, §3ter). -/
theorem exists_unramifiedDetector (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (y : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype M)
      (SSGRoute.PTExt.localUnitsK (k := k) w) 1)
    (hy : ¬ SSGRoute.PTExt.IsUnramifiedExt (k := k) (K := K) w y) :
    ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K L) M) 1),
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
        SSGRoute.PTExt.levelPair
          (Work.SSGRoute.decompKRestrict k K L w (NK.GlobalCFT.Place.ofFinite q') hq')
          (Work.SSGRoute.localUnitsMap k K L w (NK.GlobalCFT.Place.ofFinite q') hq') y
          (SSGRoute.PTExt.extHRestrict
            (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h)
          ≠ 0 := by
  classical
  subst hwq
  -- the `ℤ`-coefficient class `δy = y ≫ mk₀ (localUnitsValHom q)`, nonzero by C1
  set φ : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype M)
      (SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q))) 1 :=
    y.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q)) (add_zero 1)
    with hφ
  have hδ : φ ≠ 0 := by
    intro h0
    exact hy ((Work.SSGRoute.ValuationSES.isUnramifiedExt_iff_comp_valHom
      (k := k) (K := K) q y).mpr (hφ ▸ h0))
  -- node C6: the trivial-coefficient unramified detector
  have hcrux : ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
        (NK.GlobalCFT.Place.ofFinite q))
      (h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M) 1),
      SSGRoute.PTExt.IsUnramifiedClassAt q' h ∧
      Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p ∧
      SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv
          (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
            (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff)
        φ
        (SSGRoute.PTExt.extHRestrict
          (SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')) h) ≠ 0 :=
    hcrux_of_coordDatum p k K Ω M hM (NK.GlobalCFT.Place.ofFinite q) q rfl hpq hI φ hδ
      (fun μ hμ => Work.SSGRoute.E7cOmega.exists_level_detecting_functional
        p k K Ω M hM (NK.GlobalCFT.Place.ofFinite q) q rfl hpq hI μ hμ)
  obtain ⟨L, hLnf, hLfd, hLgal, q', hq', h, hunr, hcop, hkey⟩ := hcrux
  refine ⟨L, hLnf, hLfd, hLgal, q', hq', h, hunr, ?_⟩
  intro hzero
  -- the local class at the level `q'`, in the form expected by `levelPair` at that level
  let rh : SSGRoute.PTExt.extH (Rep.res (Work.SSGRoute.decompKRestrict k K ↥L
      (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
      (Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype M)) 1 :=
    SSGRoute.PTExt.extHRestrict (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
      (NK.GlobalCFT.Place.ofFinite q')) h
  have hzero' : SSGRoute.PTExt.levelPair
      (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (Work.SSGRoute.localUnitsMap k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq') y rh = 0 := hzero
  have hkey' : SSGRoute.PTExt.levelPair
      (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
        (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
        SSGRoute.PTExt.Coeff) φ rh ≠ 0 := hkey
  -- (**) pushing the pairing along the valuation `L_{q'}ˣ → ℤ` multiplies it by `e = e(q'/q)`
  have hpush : (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (Work.SSGRoute.localUnitsMap k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq') y rh).comp
      (Abelian.Ext.mk₀ (NK.HassePrinciple.localUnitsValHom (K := k) (L := ↥L) q')) (add_zero 2)
      = (q.asIdeal.ramificationIdx' q'.asIdeal) •
        (SSGRoute.PTExt.levelPair
          (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
            (NK.GlobalCFT.Place.ofFinite q') hq')
          (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
            (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
            SSGRoute.PTExt.Coeff)
          φ rh) := by
    have hcomp := Work.SSGRoute.levelPair_comp
      (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (Work.SSGRoute.localUnitsMap k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (NK.HassePrinciple.localUnitsValHom (K := k) (L := ↥L) q') y rh
    have hmap := Work.SSGRoute.E7cC.localUnitsMap_comp_valHom (k := k) (K := K) (L := ↥L) q q' hq'
    have hlin := Work.SSGRoute.E7cC.levelPair_nsmul_coeff
      (f := Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (M := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype M)
      (A := SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofFinite q))
      (B := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')))
      (n := q.asIdeal.ramificationIdx' q'.asIdeal)
      (ι := Rep.resMap (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
        (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q))
      (x := y) (h := rh)
    have hcomp_id : Rep.resMap (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq') (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q) ≫
        SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
          (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq') SSGRoute.PTExt.Coeff
        = Rep.resMap (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq') (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q) := by
      rfl
    have hident : SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (Rep.resMap (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
          (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q)) y rh
        = SSGRoute.PTExt.levelPair
          (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
            (NK.GlobalCFT.Place.ofFinite q') hq')
          (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
            (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
            SSGRoute.PTExt.Coeff) φ rh := by
      have hext : SSGRoute.PTExt.extRes
          (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
            (NK.GlobalCFT.Place.ofFinite q') hq')
          (y.comp (Abelian.Ext.mk₀ (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q))
            (add_zero 1))
        = (SSGRoute.PTExt.extRes (Work.SSGRoute.decompKRestrict k K ↥L
              (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq') y).comp
            (Abelian.Ext.mk₀ (Rep.resMap (Work.SSGRoute.decompKRestrict k K ↥L
              (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
              (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q))) (add_zero 1) := by
        simp only [SSGRoute.PTExt.extRes, Abelian.Ext.mapExactFunctor_comp,
          Abelian.Ext.mapExactFunctor_mk₀]
      rw [hφ, SSGRoute.PTExt.levelPair, SSGRoute.PTExt.levelPair, hext,
        Abelian.Ext.comp_assoc, Abelian.Ext.mk₀_comp_mk₀, hcomp_id]
      all_goals rfl
    refine hcomp.symm.trans ?_
    refine hmap ▸ ?_
    exact hlin.trans (congrArg (fun z => (q.asIdeal.ramificationIdx' q'.asIdeal) • z) hident)
  -- `e • V = 0` and `p • V = 0` with `e` prime to `p` force `V = 0`
  have hVe : (q.asIdeal.ramificationIdx' q'.asIdeal) •
      (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
          (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff) φ rh) = 0 := by
    rw [← hpush, hzero', Abelian.Ext.zero_comp]
  have hVp : p •
      (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
          (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff) φ rh) = 0 := by
    rw [← Work.SSGRoute.E7cC.levelPair_nsmul_x
      (f := Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (M := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype M)
      (A := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)))
      (B := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')))
      (ι := SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
        (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
        SSGRoute.PTExt.Coeff)
      (n := p) (x := φ) (h := rh)]
    have hpφ : p • φ = 0 := by
      rw [hφ]
      rw [← Work.SSGRoute.E7cC.nsmul_comp_coeff p y
        (Abelian.Ext.mk₀ (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) q)) (add_zero 1)]
      rw [Work.SSGRoute.ext_nsmul_p_torsion_left
        (X := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
          (NK.GlobalCFT.Place.ofFinite q)).subtype M)
        (Y := SSGRoute.PTExt.localUnitsK (k := k) (K := K) (NK.GlobalCFT.Place.ofFinite q))
        p (fun m => hM m) y, Abelian.Ext.zero_comp]
    rw [hpφ]
    exact Work.SSGRoute.levelPair_zero
      (f := Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
        (NK.GlobalCFT.Place.ofFinite q') hq')
      (M := Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K)
        (NK.GlobalCFT.Place.ofFinite q)).subtype M) (A := SSGRoute.PTExt.unitRep
        (SSGRoute.PTExt.decompK (k := k) (K := K) (NK.GlobalCFT.Place.ofFinite q)))
      (B := SSGRoute.PTExt.unitRep (SSGRoute.PTExt.decompK (k := k) (K := ↥L)
        (NK.GlobalCFT.Place.ofFinite q')))
      (ι := SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
        (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
        SSGRoute.PTExt.Coeff) rh
  have hdvd : addOrderOf (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
          (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff) φ rh) ∣ 1 := by
    have hg : addOrderOf (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
          (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff) φ rh) ∣ Nat.gcd (q.asIdeal.ramificationIdx' q'.asIdeal) p :=
      Nat.dvd_gcd (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hVe)
        (addOrderOf_dvd_iff_nsmul_eq_zero.mpr hVp)
    rwa [show Nat.gcd (q.asIdeal.ramificationIdx' q'.asIdeal) p = 1 from hcop] at hg
  have horder : addOrderOf (SSGRoute.PTExt.levelPair
        (Work.SSGRoute.decompKRestrict k K ↥L (NK.GlobalCFT.Place.ofFinite q)
          (NK.GlobalCFT.Place.ofFinite q') hq')
        (SSGRoute.PTExt.trivResInv (Work.SSGRoute.decompKRestrict k K ↥L
          (NK.GlobalCFT.Place.ofFinite q) (NK.GlobalCFT.Place.ofFinite q') hq')
          SSGRoute.PTExt.Coeff) φ rh) = 1 := Nat.dvd_one.mp hdvd
  exact hkey' (AddMonoid.addOrderOf_eq_one_iff.mp horder)

end Work.SSGRoute.E7cC
