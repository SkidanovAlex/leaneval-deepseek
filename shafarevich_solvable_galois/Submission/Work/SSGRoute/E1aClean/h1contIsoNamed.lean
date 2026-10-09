import Mathlib
import Submission.Work.SSGRoute.h1cont_iso_H1loc
import Submission.Work.SSGRoute.E1aClean.h1locCoeffNatural
import Submission.Work.SSGRoute.E1aClean.h1TransferReflNat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The *named* identification `H¹(Ω_v, E) ≃+ H1loc(D_A,E)`

`Work.SSGRoute.h1cont_iso_H1loc` proves that the locally constant cohomology of the decomposition
group `D_A` is the continuous cohomology `H¹` of the local absolute Galois group
`Gal(Ω_v/k_v)` — for a fixed coefficient module `E`, as a `Nonempty`.  Its *witness*, however, is
an explicit term,

  `(PT.h1Transfer Φ hΦ (AddEquiv.refl E) ·).symm.trans (H1locEquivH1_decomp … A).symm`,

i.e. the `H¹`-transport along the group isomorphism `Φ` (which is the identity on cocycles, since
`Ψ = AddEquiv.refl`) composed with the model bridge `H1locEquivH1_decomp`.

The local dictionary needs this as a *named* object, so that its naturality in `E` can be
established (it is `E1aClean.h1locCoeffNatural` carried through the transport, which is natural by
`AddEquiv.refl`).  This file unwraps the `Nonempty`.
-/

namespace Work.SSGRoute.E1aClean

open CategoryTheory

noncomputable section

/-- **The named identification** `H¹(Gal(Ω_v/k_v), E) ≃+ H1loc(D_A,E)`; the witness of
`Work.SSGRoute.h1cont_iso_H1loc`, exposed as a definition. -/
noncomputable def h1contIsoH1loc (p : ℕ) [Fact p.Prime] (k : Type) (Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (E : Type) [AddCommGroup E] [Module (ZMod p) E]
    [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    [inst : DistribMulAction
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) E]
    (Φ : ↥(SSGRoute.decomp k A) ≃*
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA))
    (hΦ : IsHomeomorph Φ)
    (hact : ∀ (σ : ↥(SSGRoute.decomp k A)) (e : E),
      @SMul.smul _ _ inst.toSMul (Φ σ) e = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • e) :
    Work.AbsoluteKummer.H1
        (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
          Work.SSGRoute.localClosureAt k A hA) E ≃+
      Work.SSGRoute.H1loc p k Ω K E (SSGRoute.decomp k A) := by
  letI : DistribMulAction ↥(SSGRoute.decomp k A) E :=
    Work.SSGRoute.decompDistribMulAction K E A
  have hΨ : ∀ (σ : ↥(SSGRoute.decomp k A)) (e : E),
      (AddEquiv.refl E) (σ • e) = Φ σ • ((AddEquiv.refl E) e) := by
    intro σ e
    show @SMul.smul _ _ (Work.SSGRoute.decompDistribMulAction K E A).toSMul σ e = Φ σ • e
    rw [Work.SSGRoute.decomp_smul_eq_res K E A σ e]
    exact (hact σ e).symm
  exact (Work.SSGRoute.PT.h1Transfer Φ hΦ (AddEquiv.refl E) hΨ).symm.trans
    (Work.SSGRoute.H1locEquivH1_decomp p k Ω K E A).symm

/-- The named iso is (by construction) the witness of `h1cont_iso_H1loc`. -/
theorem h1contIsoH1loc_mem_h1cont_iso_H1loc (p : ℕ) [Fact p.Prime] (k : Type) (Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] (E : Type) [AddCommGroup E]
    [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    [inst : DistribMulAction
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) E]
    (Φ : ↥(SSGRoute.decomp k A) ≃*
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA))
    (hΦ : IsHomeomorph Φ)
    (hact : ∀ (σ : ↥(SSGRoute.decomp k A)) (e : E),
      @SMul.smul _ _ inst.toSMul (Φ σ) e = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • e) :
    Nonempty (Work.AbsoluteKummer.H1
        (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
          Work.SSGRoute.localClosureAt k A hA) E ≃+
      Work.SSGRoute.H1loc p k Ω K E (SSGRoute.decomp k A)) :=
  ⟨h1contIsoH1loc p k Ω K E A hA Φ hΦ hact⟩

/-- **The `B`-half of the naturality of `h1contIsoH1loc`.**

With `B E := H1locEquivH1_decomp E A` and `F` the coefficient map on `H1loc`, the naturality
`B_{E₂} (F x) = mapH1 f (B_{E₁} x)` of `E1aClean.h1locCoeffNatural` is equivalent — `B` being an
isomorphism — to its inverse form `F (B_{E₁}⁻¹ y) = B_{E₂}⁻¹ (mapH1 f y)`, which is the form the
composition `h1contIsoH1loc = T⁻¹.trans B⁻¹` consumes. -/
theorem h1locBridge_symm_natural (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (A : ValuationSubring Ω)
    (E₁ E₂ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
    [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
    (f : E₁ →+ E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e) :
    ∃ (F : Work.SSGRoute.H1loc p k Ω K E₁ (SSGRoute.decomp k A) →+
          Work.SSGRoute.H1loc p k Ω K E₂ (SSGRoute.decomp k A)),
      (∀ (b : (Ω ≃ₐ[k] Ω) → E₁)
          (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
          (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b),
        F (Work.SSGRoute.toClass p k Ω K E₁ (SSGRoute.decomp k A) b) =
          Work.SSGRoute.toClass p k Ω K E₂ (SSGRoute.decomp k A) (fun g => f (b g))) ∧
      (letI : DistribMulAction ↥(SSGRoute.decomp k A) E₁ :=
          Work.SSGRoute.decompDistribMulAction K E₁ A
       letI : DistribMulAction ↥(SSGRoute.decomp k A) E₂ :=
          Work.SSGRoute.decompDistribMulAction K E₂ A
       ∀ (y : Work.AbsoluteKummer.H1 ↥(SSGRoute.decomp k A) E₁),
        F ((Work.SSGRoute.H1locEquivH1_decomp (p := p) (k := k) (Ω := Ω) (K := K) (M := E₁) A).symm y)
          = (Work.SSGRoute.H1locEquivH1_decomp (p := p) (k := k) (Ω := Ω) (K := K) (M := E₂) A).symm
              (Work.AbsoluteKummer.mapH1 f
                (fun σ e => by
                  show f (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • e)
                    = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • f e
                  exact hf _ _) y)) := by
  classical
  obtain ⟨F, hF1, hF2⟩ :=
    h1locCoeffNatural (p := p) (k := k) (Ω := Ω) (K := K) A E₁ E₂ f hf
  refine ⟨F, hF1, ?_⟩
  letI : DistribMulAction ↥(SSGRoute.decomp k A) E₁ :=
    Work.SSGRoute.decompDistribMulAction K E₁ A
  letI : DistribMulAction ↥(SSGRoute.decomp k A) E₂ :=
    Work.SSGRoute.decompDistribMulAction K E₂ A
  intro y
  have h := hF2 ((Work.SSGRoute.H1locEquivH1_decomp (p := p) (k := k) (Ω := Ω) (K := K) (M := E₁) A).symm y)
  rw [AddEquiv.apply_symm_apply] at h
  rw [← h, AddEquiv.symm_apply_apply]

end

end Work.SSGRoute.E1aClean

namespace Work.SSGRoute.E1aClean

open CategoryTheory

noncomputable section

set_option maxHeartbeats 1000000 in
/-- **Naturality of `h1contIsoH1loc` in the coefficient**, in the *explicit-binder* form: the two
actions of `Λ = Gal(Ω_v/k_v)` on `E₁`, `E₂` and their compatibilities with the `↥(decomp k A)`-action
are hypotheses (`instᵢ`, `hactᵢ`), rather than `letI`s inside the statement — a `letI` inside a
`Prop` conjunct is not reachable by typeclass search for `h1contIsoH1loc`'s implicit instance
argument.  This is the form `h1cont_iso_H1loc` itself uses.

The square is the composition `h1contIsoH1loc = T⁻¹.trans B⁻¹`: the `T`-half is
`h1Transfer_symm_refl_natural` and the `B`-half is the inverse form of `h1locCoeffNatural`. -/
theorem h1contIsoH1loc_natural (p : ℕ) [Fact p.Prime] (k : Type) (Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (Φ : ↥(SSGRoute.decomp k A) ≃*
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA))
    (hΦ : IsHomeomorph Φ)
    (E₁ E₂ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [Finite E₁]
    [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
    (inst₁ : DistribMulAction
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) E₁)
    (inst₂ : DistribMulAction
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) E₂)
    (hact₁ : ∀ (σ : ↥(SSGRoute.decomp k A)) (e : E₁),
      @SMul.smul _ _ inst₁.toSMul (Φ σ) e = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • e)
    (hact₂ : ∀ (σ : ↥(SSGRoute.decomp k A)) (e : E₂),
      @SMul.smul _ _ inst₂.toSMul (Φ σ) e = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • e)
    (f : E₁ →+ E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e)
    (hfΛ : ∀ (γ : Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) (e : E₁),
      f (@SMul.smul _ _ inst₁.toSMul γ e) = @SMul.smul _ _ inst₂.toSMul γ (f e)) :
    ∃ (F : Work.SSGRoute.H1loc p k Ω K E₁ (SSGRoute.decomp k A) →+
          Work.SSGRoute.H1loc p k Ω K E₂ (SSGRoute.decomp k A)),
      (∀ (b : (Ω ≃ₐ[k] Ω) → E₁)
          (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
          (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b),
        F (Work.SSGRoute.toClass p k Ω K E₁ (SSGRoute.decomp k A) b) =
          Work.SSGRoute.toClass p k Ω K E₂ (SSGRoute.decomp k A) (fun g => f (b g))) ∧
      (letI : DistribMulAction
          (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
            Work.SSGRoute.localClosureAt k A hA) E₁ := inst₁
       letI : DistribMulAction
          (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
            Work.SSGRoute.localClosureAt k A hA) E₂ := inst₂
       ∀ (x : Work.AbsoluteKummer.H1
            (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
              Work.SSGRoute.localClosureAt k A hA) E₁),
        h1contIsoH1loc p k Ω K E₂ A hA Φ hΦ hact₂
            (Work.AbsoluteKummer.mapH1 f (fun γ e => hfΛ γ e) x)
          = F (h1contIsoH1loc p k Ω K E₁ A hA Φ hΦ hact₁ x)) := by
  classical
  obtain ⟨F, hF1, hF2⟩ :=
    h1locCoeffNatural (p := p) (k := k) (Ω := Ω) (K := K) A E₁ E₂ f hf
  refine ⟨F, hF1, ?_⟩
  letI : DistribMulAction
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) E₁ := inst₁
  letI : DistribMulAction
      (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
        Work.SSGRoute.localClosureAt k A hA) E₂ := inst₂
  letI : DistribMulAction ↥(SSGRoute.decomp k A) E₁ :=
    Work.SSGRoute.decompDistribMulAction K E₁ A
  letI : DistribMulAction ↥(SSGRoute.decomp k A) E₂ :=
    Work.SSGRoute.decompDistribMulAction K E₂ A
  have hfDA : ∀ (σ : ↥(SSGRoute.decomp k A)) (e : E₁),
      f (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • e) = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • f e :=
    fun σ e => hf (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) e
  intro x
  simp only [h1contIsoH1loc, AddEquiv.trans_apply]
  rw [h1Transfer_symm_refl_natural Φ hΦ _ _ f (fun γ e => hfΛ γ e) hfDA x]
  have hB : ∀ y : Work.AbsoluteKummer.H1 ↥(SSGRoute.decomp k A) E₁,
      F ((Work.SSGRoute.H1locEquivH1_decomp (p := p) (k := k) (Ω := Ω) (K := K) (M := E₁) A).symm y)
        = (Work.SSGRoute.H1locEquivH1_decomp (p := p) (k := k) (Ω := Ω) (K := K) (M := E₂) A).symm
            (Work.AbsoluteKummer.mapH1 f hfDA y) := by
    intro y
    have h := hF2 ((Work.SSGRoute.H1locEquivH1_decomp (p := p) (k := k) (Ω := Ω) (K := K) (M := E₁) A).symm y)
    rw [AddEquiv.apply_symm_apply] at h
    rw [← h, AddEquiv.symm_apply_apply]
  rw [hB]

end

end Work.SSGRoute.E1aClean
