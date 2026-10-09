import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.mup_local_defs
import Submission.Work.SSGRoute.PTembedding.localKummer_base
import Submission.Work.SSGRoute.PTembedding.mup_kummer_defs
import Submission.Work.SSGRoute.PTembedding.homeomorph_fixedField_fixingSubgroup
import Submission.Work.SSGRoute.PTembedding.dualMod_rootsOfUnity_equiv
import Submission.Work.SSGRoute.PTembedding.rootsOfUnity_autCongr_equiv
import Submission.Work.AbsoluteKummer.All
import Submission.Work.SSGRoute.PT.Hilbert90IsAlgClosure
import Submission.Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical
open Work.AbsoluteKummer

set_option linter.style.haveILetI false

namespace Work.SSGRoute.PTembedding

/-- **The twisted Kummer isomorphism.** For *any* field `k`, the `p`-Kummer class group
`kˣ/(kˣ)^p` is the continuous `H¹` of `G_k` with coefficients in `μ_p(k̄)` (with the natural
Galois action).  This is the Kummer short exact sequence plus Hilbert 90, packaged using the
explicit identification `H⁰(G_k, k̄ˣ) ≃ kˣ` (`baseUnitsHom`). -/
theorem kummer_unitsQuotient_aux (k : Type) [Field k] [IsGalois k (AlgebraicClosure k)]
    (p : ℕ) [Fact p.Prime] :
    Nonempty (Work.AbsoluteKummer.H1 (Work.AbsoluteKummer.G k)
        (Additive (rootsOfUnity p (AlgebraicClosure k))) ≃+
      Additive (kˣ ⧸ (MonoidHom.range (powMonoidHom p : kˣ →* kˣ)))) := by
  classical
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  set S : Subgroup kˣ := MonoidHom.range (powMonoidHom p : kˣ →* kˣ) with hS
  let bH : Additive kˣ →+ ↥(Work.AbsoluteKummer.H0 (G k) (Additive (AlgebraicClosure k)ˣ)) :=
    (Kummer.baseUnitsHom (k := k)).codRestrict _ (Kummer.baseUnitsHom_mem (k := k))
  have hbH : Function.Bijective bH := by
    refine ⟨fun a b hab => Kummer.baseUnitsHom_injective (k := k) (congrArg Subtype.val hab), ?_⟩
    intro y
    obtain ⟨a, ha⟩ := Kummer.exists_baseUnitsHom_eq (k := k) y
    exact ⟨a, Subtype.ext ha⟩
  let F0 := AddEquiv.ofBijective bH hbH
  let EG : ↥(Work.AbsoluteKummer.H0 (G k) (Additive (AlgebraicClosure k)ˣ)) ≃+ Additive kˣ :=
    F0.symm
  have EG_bH : ∀ a : Additive kˣ, EG (bH a) = a := fun a => AddEquiv.symm_apply_apply F0 a
  have bH_EG : ∀ y : ↥(Work.AbsoluteKummer.H0 (G k) (Additive (AlgebraicClosure k)ˣ)),
      bH (EG y) = y := fun y => AddEquiv.apply_symm_apply F0 y
  let f : ↥(Work.AbsoluteKummer.H0 (G k) (Additive (AlgebraicClosure k)ˣ)) →+
      ↥(Work.AbsoluteKummer.H0 (G k) (Additive (AlgebraicClosure k)ˣ)) :=
    Work.GroupCohomology.mapH0 (G k) (Kummer.kummerPi (k := k) p)
      (Kummer.kummerPi_equivariant (k := k) p)
  have hbase_pow : ∀ a : Additive kˣ,
      f (bH a) = bH (Additive.ofMul (Additive.toMul a ^ p)) := by
    intro a
    apply Subtype.ext
    show Kummer.kummerPi (k := k) p (Kummer.baseUnitsHom (k := k) a)
      = Kummer.baseUnitsHom (k := k) (Additive.ofMul (Additive.toMul a ^ p))
    show Additive.ofMul ((Units.map (algebraMap k (AlgebraicClosure k) : k →* AlgebraicClosure k)
        (Additive.toMul a)) ^ p)
      = Additive.ofMul (Units.map (algebraMap k (AlgebraicClosure k) : k →* AlgebraicClosure k)
        (Additive.toMul a ^ p))
    exact congrArg Additive.ofMul
      (map_pow (Units.map (algebraMap k (AlgebraicClosure k) : k →* AlgebraicClosure k))
        (Additive.toMul a) p).symm
  have hpow : ∀ y : ↥(Work.AbsoluteKummer.H0 (G k) (Additive (AlgebraicClosure k)ˣ)),
      EG (f y) = Additive.ofMul (Additive.toMul (EG y) ^ p) := by
    intro y
    conv_lhs => rw [← bH_EG y]
    rw [hbase_pow (EG y), EG_bH]
  have hmap : AddSubgroup.map EG.toAddMonoidHom f.range = S.toAddSubgroup := by
    ext a
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [AddMonoidHom.mem_range] at hy
      obtain ⟨w, rfl⟩ := hy
      rw [hS]
      change Additive.toMul (EG (f w)) ∈ (powMonoidHom p).range
      rw [MonoidHom.mem_range]
      exact ⟨Additive.toMul (EG w), by rw [hpow w]; rfl⟩
    · intro ha
      rw [hS] at ha
      change Additive.toMul a ∈ (powMonoidHom p).range at ha
      rw [MonoidHom.mem_range] at ha
      obtain ⟨z, hz⟩ := ha
      have hz' : z ^ p = Additive.toMul a := hz
      refine ⟨f (bH (Additive.ofMul z)), ⟨bH (Additive.ofMul z), rfl⟩, ?_⟩
      change EG (f (bH (Additive.ofMul z))) = a
      rw [hpow (bH (Additive.ofMul z)), EG_bH]
      change Additive.ofMul (z ^ p) = a
      rw [hz']
      rfl
  have hcongr : (↥(Work.AbsoluteKummer.H0 (G k) (Additive (AlgebraicClosure k)ˣ)) ⧸ f.range) ≃+
      Additive (kˣ ⧸ S) :=
    QuotientAddGroup.congr f.range S.toAddSubgroup EG hmap
  obtain ⟨kQ⟩ := Kummer.kummerQuotientEquiv (k := k) (n := p)
  exact ⟨kQ.symm.trans hcongr⟩



/-- At a finite place `A` of `Ω` over a finite prime of `k`, local Kummer theory over the
decomposition field `F = Ω^{D_A}` (with `D_A = decomp k A` and `μ_p` contained in the algebraically
closed field `Ω`) identifies the local `H¹` with coefficients in the cyclotomic module `μ_p` with the
`p`-Kummer group `F^×/(F^×)^p`. -/
theorem h1loc_mup_card_kummer
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) :
    Nat.card (Work.SSGRoute.H1loc p k Ω K (Work.SSGRoute.DualMod p T)
        (SSGRoute.decomp k A))
      = Nat.card (Work.SSGRoute.mup.KummerGroup p (Work.SSGRoute.mup.decompField k Ω A)) := by
  obtain ⟨Ψ, hΨ⟩ := dualMod_rootsOfUnity_equiv p k Ω K ζ hζ hζK T hT
  have hDclosed : IsClosed (SSGRoute.decomp k A : Set (Ω ≃ₐ[k] Ω)) := isClosed_decomp' k Ω A
  set F : IntermediateField k Ω := Work.SSGRoute.mup.decompField k Ω A with hF
  -- Step 1: `H1loc` is the continuous `H¹` of the decomposition group.
  letI : DistribMulAction ↥F.fixingSubgroup (Work.SSGRoute.DualMod p T) :=
    subDistribMulAction (K := K) F.fixingSubgroup (Work.SSGRoute.DualMod p T)
  have eA : Work.SSGRoute.H1loc p k Ω K (Work.SSGRoute.DualMod p T) F.fixingSubgroup
      ≃+ Work.AbsoluteKummer.H1 ↥F.fixingSubgroup (Work.SSGRoute.DualMod p T) :=
    H1locEquivH1 p k Ω K (Work.SSGRoute.DualMod p T) F.fixingSubgroup (fun h m => rfl)
  -- Step 2: transport along `↥F.fixingSubgroup ≃* Gal(Ω/↥F)`, changing the coefficient module
  -- from `DualMod p T` to `μ_p(Ω)`.
  have hΦ₁ : IsHomeomorph (⇑(IntermediateField.fixingSubgroupEquiv F)) := by
    rw [hF]
    exact homeomorph_fixedField_fixingSubgroup (D := SSGRoute.decomp k A) hDclosed
  have hac : ∀ (g : ↥F.fixingSubgroup) (x : Additive (rootsOfUnity p Ω)),
      (IntermediateField.fixingSubgroupEquiv F g) • x = (g : Ω ≃ₐ[k] Ω) • x := by
    intro g x
    show Additive.ofMul (MupKummer.muMapOfField ↥F Ω p
        (IntermediateField.fixingSubgroupEquiv F g) (Additive.toMul x)) =
      Additive.ofMul (MupKummer.muMapOfField k Ω p (g : Ω ≃ₐ[k] Ω) (Additive.toMul x))
    congr 1
  have hΨ₁ : ∀ (g : ↥F.fixingSubgroup) (m : Work.SSGRoute.DualMod p T),
      Ψ (g • m) = (IntermediateField.fixingSubgroupEquiv F g) • Ψ m := by
    intro g m
    have h1 : Ψ (g • m) = (g : Ω ≃ₐ[k] Ω) • Ψ m := by
      change Ψ (SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) • m) = (g : Ω ≃ₐ[k] Ω) • Ψ m
      exact hΨ (g : Ω ≃ₐ[k] Ω) m
    rw [h1, hac g (Ψ m)]
  have eB : Work.AbsoluteKummer.H1 ↥F.fixingSubgroup (Work.SSGRoute.DualMod p T)
      ≃+ Work.AbsoluteKummer.H1 (Ω ≃ₐ[↥F] Ω) (Additive (rootsOfUnity p Ω)) :=
    Work.SSGRoute.PT.h1Transfer (Φ := IntermediateField.fixingSubgroupEquiv F) hΦ₁ Ψ hΨ₁
  -- Step 3: transport along `Gal(Ω/↥F) ≃* Gal(F̄/↥F)`, with `Ω` an algebraic closure of `↥F`.
  haveI : IsAlgClosure ↥F Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  let e : AlgebraicClosure ↥F ≃ₐ[↥F] Ω :=
    IsAlgClosure.equiv ↥F (AlgebraicClosure ↥F) Ω
  have hΦ₂ : IsHomeomorph (⇑(AlgEquiv.autCongr e).symm) :=
    NK.Mine.isHomeomorph_symm (AlgEquiv.autCongr e) (NK.Mine.isHomeomorph_autCongr e)
  obtain ⟨Ψ₂, hΨ₂⟩ := rootsOfUnity_autCongr_equiv ↥F e p
  have hcongr : ∀ g : Ω ≃ₐ[↥F] Ω,
      (AlgEquiv.autCongr e) ((AlgEquiv.autCongr e).symm g) = g :=
    fun g => MulEquiv.apply_symm_apply _ g
  have hΨ₂' : ∀ (g : Ω ≃ₐ[↥F] Ω) (m : Additive (rootsOfUnity p Ω)),
      Ψ₂.symm (g • m) = (AlgEquiv.autCongr e).symm g • Ψ₂.symm m := by
    intro g m
    have h := congrArg Ψ₂.symm (hΨ₂ ((AlgEquiv.autCongr e).symm g) (Ψ₂.symm m))
    simp only [AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply] at h
    rw [hcongr g] at h
    exact h.symm
  have eC : Work.AbsoluteKummer.H1 (Ω ≃ₐ[↥F] Ω) (Additive (rootsOfUnity p Ω))
      ≃+ Work.AbsoluteKummer.H1 (Work.AbsoluteKummer.G ↥F)
        (Additive (rootsOfUnity p (AlgebraicClosure ↥F))) :=
    Work.SSGRoute.PT.h1Transfer (Φ := (AlgEquiv.autCongr e).symm) hΦ₂ Ψ₂.symm hΨ₂'
  -- Step 4: the twisted Kummer isomorphism over the decomposition field.
  have hKum : Nat.card (Work.AbsoluteKummer.H1 (Work.AbsoluteKummer.G ↥F)
        (Additive (rootsOfUnity p (AlgebraicClosure ↥F))))
      = Nat.card (Work.SSGRoute.mup.KummerGroup p F) := by
    obtain ⟨eD⟩ := kummer_unitsQuotient_aux ↥F p
    calc Nat.card (Work.AbsoluteKummer.H1 (Work.AbsoluteKummer.G ↥F)
          (Additive (rootsOfUnity p (AlgebraicClosure ↥F))))
        = Nat.card (Additive ((↥F)ˣ ⧸ (MonoidHom.range (powMonoidHom p :
            (↥F)ˣ →* (↥F)ˣ)))) := Nat.card_congr eD.toEquiv
      _ = Nat.card (Work.SSGRoute.mup.KummerGroup p F) := rfl
  have key : Nat.card (Work.SSGRoute.H1loc p k Ω K (Work.SSGRoute.DualMod p T) F.fixingSubgroup)
      = Nat.card (Work.SSGRoute.mup.KummerGroup p F) := by
    rw [Nat.card_congr eA.toEquiv, Nat.card_congr eB.toEquiv, Nat.card_congr eC.toEquiv]
    exact hKum
  rw [hF] at key
  rw [fixingSubgroup_decompField k Ω A] at key
  exact key

end Work.SSGRoute.PTembedding
