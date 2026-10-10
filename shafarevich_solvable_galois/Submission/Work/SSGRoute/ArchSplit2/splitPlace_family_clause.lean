import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.ArchDictionary.Defs
import Submission.Work.SSGRoute.ArchDictionary_aux.SettingLemmas
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchSplit2

/-! ## Small helpers on `⟨c⟩`-cochains

`Work.SSGRoute.PT.isCocycleOn_add` and `Work.SSGRoute.PT.isCocycleOn_zpowers_comp` live in
`Submission.Work.SSGRoute.PT.archSplitPlace_dictionary_of_kernel`, which cannot be imported together
with `PT.contSmulMem` (both define `Work.SSGRoute.PT.isCocycleOn_smul`); the two lemmas are
reproved here under fresh names. -/

/-- The `1`-cocycle condition is additive in the cochain. -/
private lemma splitPlace_cocycle_add {Γ G M : Type} [Group Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] (act : Γ →* G) {H : Subgroup Γ} {b b' : Γ → M}
    (hb : SSGRoute.IsCocycleOn act H b) (hb' : SSGRoute.IsCocycleOn act H b') :
    SSGRoute.IsCocycleOn act H (b + b') := by
  intro g hg h hh
  simp only [Pi.add_apply, hb g hg h hh, hb' g hg h hh, smul_add]
  abel

/-- A `⟨c⟩`-cocycle stays a cocycle after an additive map, when `⟨c⟩` acts trivially. -/
private lemma splitPlace_cocycle_comp {Γ G E E₂ : Type} [Group Γ] [Group G]
    [AddCommGroup E] [DistribMulAction G E] [AddCommGroup E₂] [DistribMulAction G E₂]
    (act : Γ →* G) (c : Γ) (hgen : ∀ g ∈ Subgroup.zpowers c, act g = 1)
    (f : E →+ E₂) {b : Γ → E} (hb : SSGRoute.IsCocycleOn act (Subgroup.zpowers c) b) :
    SSGRoute.IsCocycleOn act (Subgroup.zpowers c) (fun σ => f (b σ)) := by
  intro g hg h hh
  change f (b (g * h)) = f (b g) + act g • f (b h)
  rw [hb g hg h hh, map_add, hgen g hg, one_smul, one_smul]

/-- **The split-place (`decompK w = ⊥`) half of the archimedean conjunct of
`E1aClean.localDictionary_natural_family_arch`, in the family's own clause shape.**

`p = 2`; `c` is a nontrivial involution of `Gal(Ω/k)`, `φ` a seam embedding (`φ ∘ c = conj ∘ φ`) and
`w = mk (φ|_K)` an infinite place with `decompK w = ⊥` (so `res k K c = 1` and `K_w = ℝ`).

The input `ψ` is the canonical split-place dictionary of **A3** (`ArchSplit2/archSplit2_canonical`):
a family `ψ E : E →+ Ext¹_{D_w}(E'|, K_wˣ)` (`E' = DualMod p (E ⊗ T)`) that is bijective, natural in
the coefficient (via the transpose `F'` of `f ⊗ id_T`) and agrees with the canonical global dictionary
on global cocycles.

The conclusion is an `E`-indexed family `βc` with the *five* clauses of the family's archimedean
conjunct (additivity on `⟨c⟩`-cocycles, kernel = coboundaries, surjectivity, the comparison square
with the canonical global dictionary, and **naturality in the coefficient**) — i.e. exactly the
`decompK w = ⊥` branch of `localDictionary_natural_family_arch`'s first `∧`-conjunct.

Proof: `βc E b := if IsCocycleOn (res k K) (zpowers c) b then ψ E (b c) else 0` (the same witness as
the proved `PT.archSplitPlace_dictionary_natural_of_h2E₂`, but packaged as a family in `E`).
`res k K c = 1` makes the `⟨c⟩`-action on `E` trivial, so
`IsCocycleOn (res k K) (zpowers c) b ↔ b 1 = 0 ∧ 2 • b c = 0` and
`IsCoboundaryOn … ↔ b 1 = 0 ∧ b c = 0`; at `p = 2` the module `E` is `2`-torsion, which gives the
surjectivity clause.  The square is `hψsq`; naturality is `hψnat` (the `⟨c⟩`-action being trivial,
`f ∘ b` is again a `⟨c⟩`-cocycle).  Route bookkeeping on disk:
`ArchDictionary.res_eq_one_of_decompK_eq_bot`, `Ach.isCocycleOn_zpowers_iff`,
`Ach.isCoboundaryOn_zpowers_iff`, `isCocycleOn_zpowers_comp`, `Ext.mk₀`, `Ext.comp_add` (Mathlib).

File: `Submission/Work/SSGRoute/ArchSplit2/splitPlace_family_clause.lean`; namespace
`Work.SSGRoute.ArchSplit2`.  A closely related (but `Ac E`-shaped) form — the `hsq` input of
`ArchNat.archimedeanDictUniformNat` — follows from the same proof object by composing with the
identification `Ac c E ≅ E`, `[b] ↦ b c`. -/
theorem splitPlace_family_clause
    (p : ℕ) [Fact p.Prime] (hp : p = 2) (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (w : NK.GlobalCFT.Place ↥K)
    (hw : w = NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hbot : SSGRoute.PTExt.decompK (k := k) w = ⊥)
    (ψ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        E →+ CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) w) 1)
    (hψ : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E], Function.Bijective (ψ E))
    (hψnat : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
        (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
        (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
        (F' : Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E₂ ⟶
          Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E)
        (hF' : ∀ (θ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E) (t : T),
          (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom θ)
            (TensorProduct.tmul (ZMod p) e t) = θ (TensorProduct.tmul (ZMod p) (f e) t))
        (e : E),
        ψ E₂ (f e) = (CategoryTheory.Abelian.Ext.mk₀
            (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')).comp (ψ E e) (zero_add 1))
    (hψsq : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E] (b : (Ω ≃ₐ[k] Ω) → E),
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        ψ E (b c) = SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))) :
    ∃ βc : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
        [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
          (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
            (Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E))
          (SSGRoute.PTExt.localUnitsK (k := k) w) 1,
      (∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
        (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
          βc E (b + b') = βc E b + βc E b') ∧
        (∀ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
          (βc E b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b)) ∧
        (∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ βc E b = y) ∧
        (∀ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
          SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k)
            (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = βc E b) ∧
        (∀ (E₂ : Type) [AddCommGroup E₂] [Module (ZMod p) E₂] [DistribMulAction (K ≃ₐ[k] K) E₂]
          [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E₂] [Finite E₂]
          (f : E →ₗ[ZMod p] E₂) (hf : ∀ (g : K ≃ₐ[k] K) (e : E), f (g • e) = g • f e)
          (F' : Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E₂ ⟶
            Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E)
          (hF' : ∀ (θ : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E₂ T)) (e : E) (t : T),
            (show Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) from F'.hom θ)
              (TensorProduct.tmul (ZMod p) e t) = θ (TensorProduct.tmul (ZMod p) (f e) t))
          (b : (Ω ≃ₐ[k] Ω) → E),
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
          βc E₂ (fun σ => f (b σ)) = (CategoryTheory.Abelian.Ext.mk₀
              (Rep.resMap (SSGRoute.PTExt.decompK (k := k) w).subtype F')).comp (βc E b) (zero_add 1))) := by
  classical
  -- the seam involution acts trivially on `K` (`K_w = ℝ`, `decompK w = ⊥`)
  have hres : SSGRoute.res k K c = 1 := by
    refine Work.SSGRoute.ArchDictionary.res_eq_one_of_decompK_eq_bot c hc2 hc1 φ hlink ?_
    rw [← hw]
    exact hbot
  have hgen : ∀ g ∈ Subgroup.zpowers c, SSGRoute.res k K g = 1 := by
    intro g hg
    exact MonoidHom.mem_ker.mp ((Subgroup.zpowers_le.mpr (MonoidHom.mem_ker.mpr hres)) hg)
  have hmem : ∀ g ∈ Subgroup.zpowers c, g = 1 ∨ g = c :=
    fun g hg => Work.SSGRoute.Ach.mem_zpowers_eq_one_or c hc2 hg
  -- the dictionary: the canonical `ψ`, zero off the cocycles
  let βc : ∀ (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
      [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E],
      ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (Work.SSGRoute.ArchDictionary.Eprime p k Ω K T E))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1 :=
    fun E _ _ _ _ _ b =>
      if SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b then ψ E (b c) else 0
  refine ⟨βc, ?_⟩
  intro E _ _ _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- additivity on the `⟨c⟩`-cocycles
    intro b b' hb hb'
    have hb'' : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (b + b') :=
      splitPlace_cocycle_add _ hb hb'
    dsimp only [βc]
    rw [if_pos hb'', if_pos hb, if_pos hb', Pi.add_apply, map_add]
  · -- the kernel is the coboundaries
    intro b hb
    have hψ0 : ∀ x : E, ψ E x = 0 ↔ x = 0 := fun x =>
      ⟨fun h => (hψ E).1 (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
    have hb1 : b 1 = 0 :=
      ((Work.SSGRoute.Ach.isCocycleOn_zpowers_iff (SSGRoute.res k K) c hc2 b).mp hb).1
    dsimp only [βc]
    rw [if_pos hb, hψ0 (b c),
      Work.SSGRoute.ArchDictionary.isCoboundaryOn_zpowers_iff_of_res_eq_one c hc2 hres b]
    exact ⟨fun h => ⟨hb1, h⟩, fun h => h.2⟩
  · -- surjectivity (`p = 2`: `E` is `2`-torsion)
    intro y
    let e₀ : E := (AddEquiv.ofBijective (ψ E) (hψ E)).symm y
    let b : (Ω ≃ₐ[k] Ω) → E := fun σ => if σ = c then e₀ else 0
    have h2E : ∀ e : E, (2 : ℕ) • e = 0 := by
      intro e
      rw [two_nsmul]
      exact Work.SSGRoute.Ach.add_self_eq_zero_of_eq_two p hp e
    have hcoc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b := by
      intro g hg h hh
      have hga : SSGRoute.res k K g = 1 := hgen g hg
      rw [hga, one_smul]
      rcases hmem g hg with hg1 | hgc <;> rcases hmem h hh with hh1 | hhc
      · rw [hg1, hh1]; simp [b, Ne.symm hc1]
      · rw [hg1, hhc]; simp [b, Ne.symm hc1]
      · rw [hgc, hh1]; simp [b, Ne.symm hc1]
      · rw [hgc, hhc]
        have hcc : c * c = 1 := by rw [← pow_two]; exact hc2
        simp only [b, hcc, if_neg (Ne.symm hc1), if_pos rfl, ← two_nsmul, h2E]
    refine ⟨b, hcoc, ?_⟩
    have hbc : b c = e₀ := by dsimp only [b]; rw [if_pos rfl]
    dsimp only [βc]
    rw [if_pos hcoc, hbc]
    dsimp only [e₀]
    rw [← AddEquiv.ofBijective_apply (ψ E) (hψ E), AddEquiv.apply_symm_apply]
  · -- the comparison square with the canonical global dictionary
    intro b hb hl
    have hbc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b :=
      fun g _ h _ => hb g trivial h trivial
    dsimp only [βc]
    rw [if_pos hbc]
    exact (hψsq E b hb hl).symm
  · -- naturality in the coefficient module
    intro E₂ _ _ _ _ _ f hf F' hF' b hb
    have hcomp : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c)
        (fun σ => f (b σ)) :=
      splitPlace_cocycle_comp (SSGRoute.res k K) c hgen f.toAddMonoidHom hb
    dsimp only [βc]
    rw [if_pos hcomp, if_pos hb]
    exact hψnat E E₂ f hf F' hF' (b c)

end Work.SSGRoute.ArchSplit2
