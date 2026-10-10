import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.ArchDictionary_aux.phi_sq_signs
import Submission.Work.SSGRoute.ArchDictionary_aux.place_localField_equiv_real_of_decompK_eq_bot
import Submission.Work.SSGRoute.ArchSplit2.botLiftP
import Submission.Work.SSGRoute.ArchSplit2.realUnitsSign
import Submission.Work.SSGRoute.E1aClean.globalDictionaryCanonDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchSplit2

open CategoryTheory SSGRoute.PTExt

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

/-- **(A1) The "lift·2" functional at a split real place, as a FAMILY in the coefficient module.**

`p = 2`; `w` is an infinite place of `K` with `decompK w = ⊥` (a *split* place, i.e. a real place: the
seam `φ₀ ∘ c₀ = conj ∘ φ₀` with `w = mk (φ₀|_K)` forces `φ₀|_K` to be real-valued), for a nontrivial
involution `c₀` of `Gal(Ω/k)`.  With `E' := DualMod p (E ⊗ T)`, the conclusion provides a family
`ell E : Ext¹_{D_w}(E'|, K_wˣ) →+ (E')^∨` such that

* `ell E` is **bijective**;
* the **realization rule**: for ANY short exact presentation `S` of `res E'` in
  `Rep Coeff ↥(decompK w)` (`0 → S.X₁ → S.X₂ → S.X₃ ≅ res E' → 0`, `ψ : S.X₁ ⟶ localUnitsK w`,
  `v : S.X₂.V` lifting `m`), the class `δ(ψ) ∈ Ext¹` is killed by `ell E` exactly when the lift·2
  obstruction of `ψ` is trivial: `∃ r u, S.f r = p • v ∧ p • u = ψ r`;
* **naturality** in the coefficient along the transpose `F'` of `f ⊗ id_T`.

Route (lead's design `ssg_arch2_2320.md` (c)1, `ArchDictionary/NOTE_splitPlace_reduction.md` §3.4/§4,
`ArchDictionary_aux/NOTE_ext_localUnits_bot_ell_defect.md` §4): with `G := ↥⊥` (trivial group) the
`Ext¹`-side is `Hom(X₁,L)/im(Hom(X₂,L) → Hom(X₁,L))` by `ext_coker_LES`; the lift·2 functional
`Θ(ψ)(m) := [ψ(p • ṽ)] ∈ L/pL` (`L = K_wˣ = ℝˣ`, `p = 2`) descends to `ℓ'`; `ℓ'` is injective (the
only non-formal point: adjust a lift `X₂ → L` along an extension of the induced functional on
`X₁/2X₂ ⊆ X₂/2X₂`); `ℝˣ/ℝˣ² ≅ ℤ/2` turns `ℓ'` into the stated `ell`; bijectivity is the cardinality /
dimension match, naturality is functoriality of the cokernel description.

File: `Submission/Work/SSGRoute/ArchSplit2/ell_bot_family.lean`; namespace
`Work.SSGRoute.ArchSplit2`.  Imports (verbatim from the lead's design file `_lead_design/ssg_arch2_2320.lean`):
`Mathlib`, `Submission.Work.SSGRoute.E1aClean.localDictionary_natural_family`,
`Submission.Work.SSGRoute.ExtChain.ChainGamma`, `Submission.Work.SSGRoute.ExtChain.FreeCover`,
`Submission.Work.SSGRoute.ExtH1Iso`, `Submission.Work.SSGRoute.augSES_shortExact`,
`Submission.Work.SSGRoute.E0bDefs`, `Submission.Work.SSGRoute.PT.archPairAbstract`. -/
theorem ell_bot_family (p : ℕ) [Fact p.Prime] (hp : p = 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (w : NK.GlobalCFT.Place ↥K) (hbot : SSGRoute.PTExt.decompK (k := k) w = ⊥)
    (hwit : ∃ (c₀ : Ω ≃ₐ[k] Ω) (φ₀ : Ω →+* ℂ), c₀ ^ 2 = 1 ∧ c₀ ≠ 1 ∧
      (∀ x : Ω, φ₀ (c₀ x) = starRingEnd ℂ (φ₀ x)) ∧
      w = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ₀.comp (algebraMap ↥K Ω)))) :
    ∃ ell : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
          (SSGRoute.PTExt.localUnitsK (k := k) w) 1 →+
        Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E], Function.Bijective (ell E)) ∧
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
          (S : CategoryTheory.ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff ↥(SSGRoute.PTExt.decompK (k := k) w)))
          (hS : S.ShortExact)
          (eS : S.X₃ ≅ Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
          (ψ : S.X₁ ⟶ SSGRoute.PTExt.localUnitsK (k := k) w) (v : S.X₂.V)
          (m : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)),
          Rep.Hom.hom eS.hom (Rep.Hom.hom S.g v) = m →
          (ell E ((CategoryTheory.Abelian.Ext.mk₀ eS.inv).comp
              (hS.extClass.comp (CategoryTheory.Abelian.Ext.mk₀ ψ) (add_zero 1)) (zero_add 1)) m = 0 ↔
            ∃ (r : S.X₁.V) (u : (SSGRoute.PTExt.localUnitsK (k := k) w).V),
              Rep.Hom.hom S.f r = p • v ∧ p • u = Rep.Hom.hom ψ r)) ∧
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
          (E2 : Type) [AddCommGroup E2] [Module (ZMod p) E2] [DistribMulAction (K ≃ₐ[k] K) E2]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E2] [Finite E2]
          (F' : SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)) ⟶
            SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
          (x : CategoryTheory.Abelian.Ext
            (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
              (SSGRoute.PTExt.modRep (K ≃ₐ[k] K) (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
            (SSGRoute.PTExt.localUnitsK (k := k) w) 1)
          (m2 : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E2 T)),
          ell E2 ((CategoryTheory.Abelian.Ext.mk₀
              (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')).comp x (zero_add 1)) m2 =
            ell E x (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom m2)) := by
  classical
  subst hp
  obtain ⟨c₀, φ₀, hc2, hc1, hlink, hw⟩ := hwit
  -- The completion at the split real place `w` is `ℝ`: `K_w ≃+* ℝ`.
  obtain ⟨e, _he⟩ :=
    Work.SSGRoute.ArchDictionary_aux.place_localField_equiv_real_of_decompK_eq_bot
      2 k Ω K c₀ hc2 hc1 φ₀ hlink w hw hbot
  -- The sign data of `ℝˣ = Additive ℝˣ`.
  obtain ⟨sgnR, liftR, hliftR, hinjR, hkrnR, htorsR⟩ := realUnitsSign
  haveI : Subsingleton ↥(SSGRoute.PTExt.decompK (k := k) w) := by rw [hbot]; infer_instance
  haveI : Fintype ↥(SSGRoute.PTExt.decompK (k := k) w) := by rw [hbot]; infer_instance
  -- Transport the sign data of `ℝˣ` to `K_wˣ` along `e`.
  let ea : Additive (NK.GlobalCFT.Place.localField ↥K w)ˣ ≃+ Additive ℝˣ :=
    MulEquiv.toAdditive (Units.mapEquiv e)
  let L : Rep.{0} SSGRoute.PTExt.Coeff ↥(SSGRoute.PTExt.decompK (k := k) w) :=
    SSGRoute.PTExt.localUnitsK (k := k) w
  have hnsmul : ∀ (z : Additive (NK.GlobalCFT.Place.localField ↥K w)ˣ) (n : ℕ),
      ea (n • z) = n • ea z := fun z n => map_nsmul ea n z
  have hzero : ea 0 = 0 := AddEquiv.map_zero ea
  let D : LiftPData 2 L :=
    { sgn := sgnR.comp ea.toAddMonoidHom
      liftS := ea.symm.toAddMonoidHom.comp liftR
      hlift := fun c => by
        change sgnR (ea (ea.symm (liftR c))) = c
        rw [AddEquiv.apply_symm_apply, hliftR]
      hinj := fun a b h => hinjR (by
        have h3 := congrArg ea h
        change ea (ea.symm (liftR a)) = ea (ea.symm (liftR b)) at h3
        rwa [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h3)
      hkrn := fun x => (hkrnR (ea x)).trans
        ⟨fun ⟨y, hy⟩ => ⟨ea.symm y, by
            have hy' : 2 • ea (ea.symm y) = ea x :=
              (congrArg (fun z => 2 • z) (AddEquiv.apply_symm_apply ea y)).trans hy
            exact ea.injective ((hnsmul (ea.symm y) 2).trans hy')⟩,
         fun ⟨y, hy⟩ => ⟨ea y, ((hnsmul y 2).symm).trans (congrArg ea hy)⟩⟩
      htors := fun x hx => by
        obtain ⟨c, hc⟩ := htorsR (ea x) (by
          exact ((hnsmul x 2).symm).trans ((congrArg ea hx).trans hzero))
        refine ⟨c, ea.injective (by
          change ea x = ea (ea.symm (liftR c))
          rw [AddEquiv.apply_symm_apply]
          exact hc)⟩ }
  obtain ⟨ellFam, hbij, hreal, hnat⟩ :=
    botLiftFamily (G := ↥(SSGRoute.PTExt.decompK (k := k) w)) 2 L D
  refine ⟨fun E _ _ _ _ _ =>
      @ellFam (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))))
        (inferInstanceAs (Module (ZMod 2) (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T)))),
    ?_, ?_, ?_⟩
  · intro E _ _ _ _ _
    show Function.Bijective (@ellFam (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))))
      (inferInstanceAs (Module (ZMod 2) (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T)))))
    exact @hbij (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))))
      (inferInstanceAs (Module (ZMod 2) (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))))
  · intro E _ _ _ _ _ S hS eS ψ v m hm
    show (@ellFam (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))))
      (inferInstanceAs (Module (ZMod 2) (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T)))))
        ((CategoryTheory.Abelian.Ext.mk₀ eS.inv).comp
          (hS.extClass.comp (CategoryTheory.Abelian.Ext.mk₀ ψ) (add_zero 1)) (zero_add 1)) m = 0 ↔
      ∃ (r : S.X₁.V) (u : (SSGRoute.PTExt.localUnitsK (k := k) w).V),
        Rep.Hom.hom S.f r = 2 • v ∧ 2 • u = Rep.Hom.hom ψ r
    exact @hreal (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))))
      (inferInstanceAs (Module (ZMod 2) (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))))
      S hS eS ψ v m hm
  · intro E _ _ _ _ _ E2 _ _ _ _ _ F' x m2
    show (@ellFam (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E2 T))))
      (inferInstanceAs (Module (ZMod 2) (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E2 T)))))
        ((CategoryTheory.Abelian.Ext.mk₀
          (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')).comp x (zero_add 1)) m2 =
      (@ellFam (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))))
      (inferInstanceAs (Module (ZMod 2) (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T)))))
        x ((Rep.Hom.hom F') m2)
    exact @hnat (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))))
      (inferInstanceAs (Module (ZMod 2) (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E T))))
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E2 T))))
      (inferInstanceAs (Module (ZMod 2) (Work.SSGRoute.DualMod 2 (TensorProduct (ZMod 2) E2 T))))
      (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F') x m2

end Work.SSGRoute.ArchSplit2
