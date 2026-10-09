import Mathlib
import Submission.Work.AbsoluteKummer.All
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.SSGRoute.LTDDefs.DecompAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Naturality of the `H1loc` model bridge in the coefficient module

The model bridge `Work.SSGRoute.H1locEquivH1_decomp` (`LTDDefs/H1loc_iso_H1cont.lean`) identifies
the locally constant cohomology `H1loc` of a decomposition group with the workspace's continuous
cochain model `AbsoluteKummer.H1`.  It is stated for a *fixed* coefficient module, hence carries no
naturality; the local dictionary `localDictionary_natural_family` needs the coefficient map on
`H1loc` and the fact that the bridge intertwines it with `AbsoluteKummer.mapH1`.

Both are provided here.  The coefficient map is induced pointwise on locally constant cocycles
(`Gmap`), and the bridge is natural because `bridgeFwd` is *literally* "restrict the representative
to `↥H`, then quotient" (`bridgeFwd_mk`, which is `rfl`-level since `QuotientAddGroup.map_mk'` is
itself `rfl`), while `mapH1` is pointwise application of `f` (`mapH1_H1π`).
-/

namespace Work.SSGRoute.E1aClean

open Work.AbsoluteKummer

noncomputable section

/-- The computation rule of `bridgeFwd` on representatives. -/
lemma bridgeFwd_mk (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (z : ↥(Work.SSGRoute.lcCocycles p k Ω K M H)) :
    Work.SSGRoute.bridgeFwd p k Ω K M H hcompat (Submodule.Quotient.mk z)
      = Work.AbsoluteKummer.H1π ↥H M
          (Work.SSGRoute.restrictCocycle p k Ω K M H hcompat z) := by
  rw [Work.SSGRoute.bridgeFwd,
    show Submodule.Quotient.mk z
        = QuotientAddGroup.mk' (Work.SSGRoute.cobQ p k Ω K M H).toAddSubgroup z from rfl]
  rfl

/-- **Naturality of the `H1loc` model bridge in the coefficient.**

For an equivariant additive map `f : E₁ →+ E₂` of `Gal(K/k)`-modules, the induced map on `H1loc`
(pointwise application of `f` on locally constant cocycles) commutes with the model bridge
`H1locEquivH1_decomp`, where the latter is transported with `AbsoluteKummer.mapH1 f`. -/
theorem h1locCoeffNatural (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (A : ValuationSubring Ω)
    (E₁ E₂ : Type) [AddCommGroup E₁] [Module (ZMod p) E₁] [DistribMulAction (K ≃ₐ[k] K) E₁]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₁] [AddCommGroup E₂] [Module (ZMod p) E₂]
    [DistribMulAction (K ≃ₐ[k] K) E₂] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂]
    (f : E₁ →+ E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E₁), f (g • e) = g • f e) :
    ∃ (F : Work.SSGRoute.H1loc p k Ω K E₁ (SSGRoute.decomp k A) →+
          Work.SSGRoute.H1loc p k Ω K E₂ (SSGRoute.decomp k A)),
      (∀ (b : (Ω ≃ₐ[k] Ω) → E₁)
          (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)
          (hl : SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b),
        F (Work.SSGRoute.toClass p k Ω K E₁ (SSGRoute.decomp k A) b) =
          Work.SSGRoute.toClass p k Ω K E₂ (SSGRoute.decomp k A) (fun g => f (b g))) ∧
      (∀ (x : Work.SSGRoute.H1loc p k Ω K E₁ (SSGRoute.decomp k A)),
        letI : DistribMulAction ↥(SSGRoute.decomp k A) E₁ := Work.SSGRoute.decompDistribMulAction K E₁ A
        letI : DistribMulAction ↥(SSGRoute.decomp k A) E₂ := Work.SSGRoute.decompDistribMulAction K E₂ A
        (Work.SSGRoute.H1locEquivH1_decomp (p := p) (k := k) (Ω := Ω) (K := K) (M := E₂) A) (F x)
          = Work.AbsoluteKummer.mapH1 f
              (fun σ e => by
                show f (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • e) = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • f e
                exact hf _ _)
              ((Work.SSGRoute.H1locEquivH1_decomp (p := p) (k := k) (Ω := Ω) (K := K) (M := E₁) A) x)) := by
  classical
  have hfl : ∀ (c : ZMod p) (e : E₁), f (c • e) = c • f e := by
    intro c e
    have h1 : c • e = c.val • e := by
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      rw [Nat.cast_smul_eq_nsmul]
    have h2 : c • f e = c.val • f e := by
      conv_lhs => rw [← ZMod.natCast_zmod_val c]
      rw [Nat.cast_smul_eq_nsmul]
    rw [h1, h2, map_nsmul]
  let Gmap : ↥(Work.SSGRoute.lcCocycles p k Ω K E₁ (SSGRoute.decomp k A)) →ₗ[ZMod p]
      ↥(Work.SSGRoute.lcCocycles p k Ω K E₂ (SSGRoute.decomp k A)) :=
    { toFun := fun c => ⟨fun g => f (c.1 g), by
        obtain ⟨hc1, hc2⟩ := c.2
        refine ⟨?_, ?_⟩
        · intro g hg h hh
          simp only [hc1 g hg h hh, map_add, hf]
        · obtain ⟨U, hUo, hU⟩ := hc2
          exact ⟨U, hUo, fun g hg u hu huH => by simp only [hU g hg u hu huH]⟩⟩
      map_add' := fun a b => Subtype.ext (funext fun g => by simp)
      map_smul' := fun c a => Subtype.ext (funext fun g => by
        simp only [Submodule.coe_smul, Pi.smul_apply]
        exact hfl c (a.1 g)) }
  let hinc : Work.SSGRoute.cobQ p k Ω K E₁ (SSGRoute.decomp k A) ≤
      Submodule.comap Gmap (Work.SSGRoute.cobQ p k Ω K E₂ (SSGRoute.decomp k A)) := by
    intro x hx
    obtain ⟨m, hm⟩ := hx
    refine ⟨f m, fun g hg => ?_⟩
    have hxg : x.1 g = SSGRoute.res k K g • m - m := hm g hg
    show f (x.1 g) = SSGRoute.res k K g • f m - f m
    rw [hxg, map_sub, hf]
  refine ⟨(Submodule.mapQ (Work.SSGRoute.cobQ p k Ω K E₁ (SSGRoute.decomp k A))
      (Work.SSGRoute.cobQ p k Ω K E₂ (SSGRoute.decomp k A)) Gmap hinc).toAddMonoidHom, ?_, ?_⟩
  · intro b hb hl
    have hb1 : b ∈ Work.SSGRoute.lcCocycles p k Ω K E₁ (SSGRoute.decomp k A) := ⟨hb, hl⟩
    have hb2 : (fun g => f (b g)) ∈ Work.SSGRoute.lcCocycles p k Ω K E₂ (SSGRoute.decomp k A) :=
      (Gmap ⟨b, hb1⟩).2
    rw [Work.SSGRoute.toClass, dif_pos hb1, Work.SSGRoute.toClass, dif_pos hb2,
      Submodule.mkQ_apply, Submodule.mkQ_apply]
    change (Submodule.mapQ (Work.SSGRoute.cobQ p k Ω K E₁ (SSGRoute.decomp k A))
        (Work.SSGRoute.cobQ p k Ω K E₂ (SSGRoute.decomp k A)) Gmap hinc)
        (Submodule.Quotient.mk ⟨b, hb1⟩) =
      Submodule.Quotient.mk ⟨fun g => f (b g), hb2⟩
    rw [Submodule.mapQ_apply]
    congr 1
  · intro x
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective
      (p := Work.SSGRoute.cobQ p k Ω K E₁ (SSGRoute.decomp k A)) x
    letI : DistribMulAction ↥(SSGRoute.decomp k A) E₁ := Work.SSGRoute.decompDistribMulAction K E₁ A
    letI : DistribMulAction ↥(SSGRoute.decomp k A) E₂ := Work.SSGRoute.decompDistribMulAction K E₂ A
    change (Work.SSGRoute.H1locEquivH1_decomp (p := p) (k := k) (Ω := Ω) (K := K) (M := E₂) A)
        ((Submodule.mapQ (Work.SSGRoute.cobQ p k Ω K E₁ (SSGRoute.decomp k A))
          (Work.SSGRoute.cobQ p k Ω K E₂ (SSGRoute.decomp k A)) Gmap hinc)
          (Submodule.Quotient.mk z))
      = Work.AbsoluteKummer.mapH1 f
          (fun σ e => by
            show f (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • e) = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • f e
            exact hf _ _)
          ((Work.SSGRoute.H1locEquivH1_decomp (p := p) (k := k) (Ω := Ω) (K := K) (M := E₁) A)
            (Submodule.Quotient.mk z))
    rw [Submodule.mapQ_apply]
    change (Work.SSGRoute.bridgeFwd p k Ω K E₂ (SSGRoute.decomp k A)
          (fun h m => Work.SSGRoute.decomp_smul_eq_res K E₂ A h m))
        (Submodule.Quotient.mk (Gmap z))
      = Work.AbsoluteKummer.mapH1 f
          (fun σ e => by
            show f (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • e) = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) • f e
            exact hf _ _)
          ((Work.SSGRoute.bridgeFwd p k Ω K E₁ (SSGRoute.decomp k A)
            (fun h m => Work.SSGRoute.decomp_smul_eq_res K E₁ A h m))
            (Submodule.Quotient.mk z))
    rw [bridgeFwd_mk p k Ω K E₂ (SSGRoute.decomp k A) _ _,
      bridgeFwd_mk p k Ω K E₁ (SSGRoute.decomp k A) _ _]
    erw [Work.AbsoluteKummer.mapH1_H1π]
    congr 1

end

end Work.SSGRoute.E1aClean
