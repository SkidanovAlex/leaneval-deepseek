import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Submission.Work.SSGRoute.ArchSplit2.archSplit2_square_sign
import Submission.Work.SSGRoute.ArchSplit2.ell_bot_family
import Submission.Work.SSGRoute.PT.prime_eq_two_of_decompK_eq_bot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The archimedean dictionary at a split (real) place — assembly

This file proves `Work.SSGRoute.ArchDictionary.archimedeanDictSplitPlace`, the split-place case
(`decompK w = ⊥`) of `archimedeanDictionaryCanon`.  The reduction (see
`Submission/Work/SSGRoute/ArchDictionary/NOTE_splitPlace_reduction.md`) is:

* `decompK w = ⊥` plus the seam `φ ∘ c = conj ∘ φ` force `p = 2`
  (`PT.prime_eq_two_of_decompK_eq_bot`) and `res k K c = 1`
  (`ArchDictionary_aux/SettingLemmas`, i.e. `c` fixes `K`), so the `⟨c⟩`-action on the coefficients
  is trivial;
* the whole content of the split case is then the *lift·2 functional* family `ell` of
  `ArchDictionary_aux/ell_bot_family` together with its *value on the canonical global class*,
  `ArchDictionary_aux/archSplit2_square_sign`;
* given those two, the dictionary `βc` is the **formal** assembly of
  `ArchDictionary/NOTE_splitPlace_reduction.md` §4: it is obtained by extending the injective
  `ψ₀ : (image of b ↦ b c) → (double dual)` across the cardinality match, and transported along
  `ell` to `Ext¹`.

The formal assembly is reproduced here (`archSplitPlace_of_kernel`) rather than imported from
`PT/archSplitPlace_dictionary_of_kernel.lean`, because that module declares
`Work.SSGRoute.PT.isCocycleOn_smul`, colliding with the declaration of the same name in
`PT/contSmulMem.lean`, which lies in the import cone of the coefficient modules.  Importing both
would break the build.

(The file used to import the *leaf* `E1aClean/localDictionary_natural_family` for
`E1aClean.globalDictionaryCanon`; that is now imported leaf-free from
`E1aClean/globalDictionaryCanonDefs`, so that `cone(ArchDictionary.archimedeanDictionaryCanon)` —
which the leaf's own closure imports — contains no copy of the leaf.)
-/

namespace Work.SSGRoute.ArchDictionary

open CategoryTheory
open scoped TensorProduct

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-! ## Auxiliary: an element of `⟨c⟩` for an involution -/

/-- In a group where `c ^ 2 = 1`, the only elements of `⟨c⟩` are `1` and `c`. -/
theorem zpowers_sq_eq_one {Γ : Type} [Group Γ] {c x : Γ} (hc2 : c ^ 2 = 1)
    (hx : x ∈ Subgroup.zpowers c) : x = 1 ∨ x = c := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [← hk]
  have hc2z : c ^ (2 : ℤ) = 1 := by simpa using hc2
  rw [zpow_eq_zpow_emod k hc2z]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h]; simp
  · right; rw [h]; simp

/-! ## Auxiliary: linear algebra over `𝔽_p` -/

/-- A module over a semiring is finite if it is a finite type. -/
theorem moduleFinite_of_finite' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [Finite M] : Module.Finite R M := by
  rw [Module.finite_def, ← Submodule.span_univ]
  exact Submodule.fg_span (Set.finite_univ)

/-- **Extension of an injective linear map defined on a submodule.** Let `E`, `A` be finite modules
over the prime field `𝔽_p` with `Nat.card A = Nat.card E`, let `S ≤ E` be a submodule and
`ψ₀ : S →ₗ[𝔽_p] A` injective. Then `ψ₀` extends to a linear equivalence `E ≃ₗ[𝔽_p] A`. -/
theorem linearEquiv_extend_of_card_eq
    (p : ℕ) [Fact p.Prime]
    (E A : Type) [AddCommGroup E] [Module (ZMod p) E] [Finite E]
    [AddCommGroup A] [Module (ZMod p) A] [Finite A]
    (S : Submodule (ZMod p) E) (ψ₀ : S →ₗ[ZMod p] A) (hψ : Function.Injective ψ₀)
    (hcard : Nat.card A = Nat.card E) :
    ∃ φ : E ≃ₗ[ZMod p] A, ∀ x : S, φ (x : E) = ψ₀ x := by
  haveI : Module.Finite (ZMod p) E := moduleFinite_of_finite'
  haveI : Module.Finite (ZMod p) A := moduleFinite_of_finite'
  have hfr : Module.finrank (ZMod p) E = Module.finrank (ZMod p) A := by
    have hE := Module.natCard_eq_pow_finrank (K := ZMod p) (V := E)
    have hA := Module.natCard_eq_pow_finrank (K := ZMod p) (V := A)
    rw [hE, hA] at hcard
    have hp : 2 ≤ Nat.card (ZMod p) := by
      rw [Nat.card_zmod]; exact (Fact.out : Nat.Prime p).two_le
    exact (Nat.pow_right_injective hp hcard).symm
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl ψ₀.range
  let τ : S ≃ₗ[ZMod p] ψ₀.range := LinearEquiv.ofInjective ψ₀ hψ
  have hτ : Module.finrank (ZMod p) ψ₀.range = Module.finrank (ZMod p) S := τ.finrank_eq.symm
  have hCadd : Module.finrank (ZMod p) S + Module.finrank (ZMod p) C
      = Module.finrank (ZMod p) E := by
    have h := (Submodule.prodEquivOfIsCompl S C hC).finrank_eq
    rw [Module.finrank_prod] at h
    omega
  have hDadd : Module.finrank (ZMod p) ψ₀.range + Module.finrank (ZMod p) D
      = Module.finrank (ZMod p) A := by
    have h := (Submodule.prodEquivOfIsCompl ψ₀.range D hD).finrank_eq
    rw [Module.finrank_prod] at h
    omega
  have hCD : Module.finrank (ZMod p) C = Module.finrank (ZMod p) D := by omega
  let σ : C ≃ₗ[ZMod p] D := LinearEquiv.ofFinrankEq C D hCD
  refine ⟨(Submodule.prodEquivOfIsCompl S C hC).symm.trans
    ((τ.prodCongr σ).trans (Submodule.prodEquivOfIsCompl ψ₀.range D hD)), fun x => ?_⟩
  have h1 : (Submodule.prodEquivOfIsCompl S C hC).symm (x : E) = (x, 0) :=
    Submodule.prodEquivOfIsCompl_symm_apply_left S C hC x
  have hτx : ((τ x : ψ₀.range) : A) = ψ₀ x :=
    LinearEquiv.ofInjective_apply (f := ψ₀) (h := hψ) x
  have hy : ((τ.prodCongr σ) ((x, 0) : S × C)) = ((τ x, 0) : ψ₀.range × D) := by
    rw [LinearEquiv.prodCongr_apply]; simp
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1, hy,
    Submodule.coe_prodEquivOfIsCompl', hτx]
  simp

/-! ## The formal assembly (kernel form)

This is `Work.SSGRoute.PT.archSplitPlace_dictionary_of_kernel`, reproduced in this namespace (with
the names of its local cocycle lemmas adjusted), so that this file does not import
`PT/archSplitPlace_dictionary_of_kernel.lean` (import clash, see the module docstring). -/

theorem archSplitPlace_of_kernel
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (E : Type) [AddCommGroup E] [Module (ZMod p) E]
      [DistribMulAction (K ≃ₐ[k] K) E] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (hres : SSGRoute.res k K c = 1) (h2E : ∀ e : E, (2 : ℕ) • e = 0)
    (A : Type) [AddCommGroup A] [Module (ZMod p) A] [Finite A]
    (F : ((Ω ≃ₐ[k] Ω) → E) → A)
    (hFadd : ∀ b b' : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b' → SSGRoute.IsLocConstOn ⊤ b' →
      F (b + b') = F b + F b')
    (hFker : ∀ b : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (F b = 0 ↔ b c = 0))
    (hcard : Nat.card A = Nat.card E) :
    ∃ βc : ((Ω ≃ₐ[k] Ω) → E) → A,
      (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
        βc (b + b') = βc b + βc b') ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        (βc b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b)) ∧
      (∀ y : A, ∃ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ βc b = y) ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        βc b = F b) := by
  classical
  have hgen : ∀ g ∈ Subgroup.zpowers c, SSGRoute.res k K g = 1 := by
    intro g hg
    exact MonoidHom.mem_ker.mp ((Subgroup.zpowers_le.mpr (MonoidHom.mem_ker.mpr hres)) hg)
  have hmem : ∀ g ∈ Subgroup.zpowers c, g = 1 ∨ g = c :=
    fun g hg => zpowers_sq_eq_one hc2 hg
  let Z : Submodule (ZMod p) ((Ω ≃ₐ[k] Ω) → E) :=
    { carrier := {b | SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b ∧ SSGRoute.IsLocConstOn ⊤ b}
      zero_mem' := ⟨Work.SSGRoute.isCocycleOn_zero (act := SSGRoute.res k K) (H := ⊤),
        Work.SSGRoute.isLocConstOn_zero (H := ⊤)⟩
      add_mem' := by
        intro a b ha hb
        exact ⟨Work.SSGRoute.isCocycleOn_add (act := SSGRoute.res k K) ha.1 hb.1,
          Work.SSGRoute.isLocConstOn_add ha.2 hb.2⟩
      smul_mem' := by
        intro r x hx
        exact ⟨Work.SSGRoute.isCocycleOn_smul (act := SSGRoute.res k K) hx.1 r,
          Work.SSGRoute.isLocConstOn_smul hx.2 r⟩ }
  let ρ : Z →ₗ[ZMod p] E :=
    { toFun := fun b => (b : (Ω ≃ₐ[k] Ω) → E) c
      map_add' := fun a b => rfl
      map_smul' := fun r a => rfl }
  let FZ : Z →+ A :=
    { toFun := fun b => F (b : (Ω ≃ₐ[k] Ω) → E)
      map_zero' := by
        have h0 := hFadd 0 0 (Work.SSGRoute.isCocycleOn_zero (act := SSGRoute.res k K) (H := ⊤))
          (Work.SSGRoute.isLocConstOn_zero (H := ⊤))
          (Work.SSGRoute.isCocycleOn_zero (act := SSGRoute.res k K) (H := ⊤))
          (Work.SSGRoute.isLocConstOn_zero (H := ⊤))
        simp only [add_zero] at h0
        exact (add_left_cancel (show F 0 + 0 = F 0 + F 0 from by rw [add_zero]; exact h0)).symm
      map_add' := fun a b => by
        show F (a.1 + b.1) = F a.1 + F b.1
        exact hFadd a.1 b.1 a.2.1 a.2.2 b.2.1 b.2.2 }
  have hker : ∀ b : Z, ρ b = 0 ↔ FZ b = 0 := by
    intro b
    exact (hFker b.1 b.2.1 b.2.2).symm
  let FZlin : Z →ₗ[ZMod p] A := AddMonoidHom.toZModLinearMap p FZ
  have hFZlin : ∀ b : Z, FZlin b = FZ b := fun b => rfl
  have hK : ρ.ker ≤ FZlin.ker := by
    intro b hb
    rw [LinearMap.mem_ker] at hb ⊢
    rw [hFZlin b]
    exact (hker b).mp hb
  let ψ₀ : ρ.range →ₗ[ZMod p] A :=
    (Submodule.liftQ ρ.ker FZlin hK).comp (LinearMap.quotKerEquivRange ρ).symm.toLinearMap
  have hψ₀_apply : ∀ b : Z, ψ₀ ⟨ρ b, LinearMap.mem_range_self ρ b⟩ = FZ b := by
    intro b
    have h1 : (LinearMap.quotKerEquivRange ρ).symm ⟨ρ b, LinearMap.mem_range_self ρ b⟩
        = (LinearMap.ker ρ).mkQ b :=
      LinearMap.quotKerEquivRange_symm_apply_image ρ b (LinearMap.mem_range_self ρ b)
    show (Submodule.liftQ ρ.ker FZlin hK)
        ((LinearMap.quotKerEquivRange ρ).symm ⟨ρ b, LinearMap.mem_range_self ρ b⟩) = FZ b
    rw [h1, Submodule.mkQ_apply, Submodule.liftQ_apply, hFZlin]
  have hψ : Function.Injective ψ₀ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro y hy
    rw [LinearMap.mem_ker] at hy
    obtain ⟨b, hb⟩ := LinearMap.mem_range.mp y.2
    have h1 : ψ₀ y = FZ b := by
      have hy_eq : y = ⟨ρ b, LinearMap.mem_range_self ρ b⟩ := Subtype.ext hb.symm
      rw [hy_eq, hψ₀_apply b]
    rw [h1] at hy
    exact Subtype.ext (by rw [← hb, (hker b).mpr hy]; rfl)
  obtain ⟨φ, hφ⟩ := linearEquiv_extend_of_card_eq p E A ρ.range ψ₀ hψ hcard
  let βc : ((Ω ≃ₐ[k] Ω) → E) → A := fun b =>
    if SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b then φ (b c) else 0
  refine ⟨βc, ?_, ?_, ?_, ?_⟩
  · intro b b' hb hb'
    have hsum : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) (b + b') :=
      Work.SSGRoute.isCocycleOn_add (act := SSGRoute.res k K) hb hb'
    simp only [βc]
    rw [if_pos hsum, if_pos hb, if_pos hb', Pi.add_apply, map_add]
  · intro b hb
    have hβ : βc b = φ (b c) := by simp only [βc]; rw [if_pos hb]
    rw [hβ]
    have hφ0 : φ (b c) = 0 ↔ b c = 0 := by
      constructor
      · intro h; exact φ.injective (by rw [h, map_zero])
      · intro h; rw [h, map_zero]
    rw [hφ0]
    have hb1 : b 1 = 0 :=
      ((isCocycleOn_zpowers_iff_of_res_eq_one (K := K) c hc2 hres b).mp hb).1
    rw [isCoboundaryOn_zpowers_iff_of_res_eq_one (K := K) c hc2 hres b]
    exact ⟨fun h => ⟨hb1, h⟩, fun h => h.2⟩
  · intro y
    let b : (Ω ≃ₐ[k] Ω) → E := fun σ => if σ = c then φ.symm y else 0
    have hcoc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b := by
      intro g hg h hh
      have hga : SSGRoute.res k K g = 1 := hgen g hg
      rw [hga, one_smul]
      rcases hmem g hg with hg1 | hgc <;> rcases hmem h hh with hh1 | hhc
      · rw [hg1, hh1]; simp [b, Ne.symm hc1]
      · rw [hg1, hhc]; simp [b, Ne.symm hc1]
      · rw [hgc, hh1]; simp [b, Ne.symm hc1]
      · rw [hgc, hhc]
        have hcc : c * c = 1 := by rw [← pow_two c]; exact hc2
        simp only [b, hcc, if_neg (Ne.symm hc1), if_pos rfl, ← two_nsmul, h2E]
    refine ⟨b, hcoc, ?_⟩
    have hbc : b c = φ.symm y := by simp [b]
    simp only [βc]
    rw [if_pos hcoc, hbc, LinearEquiv.apply_symm_apply]
  · intro b hb1 hb2
    have hbZ : b ∈ Z := ⟨hb1, hb2⟩
    have hcoc : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b :=
      fun g _ h _ => hb1 g trivial h trivial
    simp only [βc]
    rw [if_pos hcoc]
    have hρ : ρ ⟨b, hbZ⟩ = b c := rfl
    rw [← hρ, hφ ⟨ρ ⟨b, hbZ⟩, LinearMap.mem_range_self ρ ⟨b, hbZ⟩⟩, hψ₀_apply ⟨b, hbZ⟩]
    rfl

/-! ## The split-place dictionary from the lift·2 functional and its value on globals -/

theorem splitPlace_of_ell
    (p : ℕ) [Fact p.Prime] (hp2 : p = 2) (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (w : NK.GlobalCFT.Place ↥K) (φ : Ω →+* ℂ)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hbot : SSGRoute.PTExt.decompK (k := k) w = ⊥)
    (ell : CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1 →+
      Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
    (hell : Function.Bijective ell)
    (hsq : ∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        ∀ m : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T),
          ell (SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k)
            (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))) m = 0 ↔
          Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E (b c) m = 0) :
    ∃ βc : ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1,
      (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
        βc (b + b') = βc b + βc b') ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        (βc b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b)) ∧
      (∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ βc b = y) ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        SSGRoute.PTExt.extLoc (k := k) w
          (SSGRoute.PTExt.extToIdeles (k := k)
            (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = βc b) := by
  classical
  haveI : Finite T := Work.SSGRoute.ExtChain.e1aFiniteT p k Ω K ζ T hT
  haveI : Finite (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :=
    Work.SSGRoute.PT.finite_dualMod_tensor p E T
  have hres : SSGRoute.res k K c = 1 := by
    refine res_eq_one_of_decompK_eq_bot (k := k) (K := K) (Ω := Ω) c hc2 hc1 φ hlink ?_
    rw [← hw]; exact hbot
  have h2E : ∀ e : E, (2 : ℕ) • e = 0 := by
    intro e
    rw [← hp2, ← Nat.cast_smul_eq_nsmul (R := ZMod p) p e, ZMod.natCast_self p, zero_smul]
  -- the localisation of the canonical global dictionary
  let F₀ : ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
      (SSGRoute.PTExt.localUnitsK (k := k) w) 1 := fun b =>
    SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k)
      (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))
  -- the target coefficient module: the double dual of `E ⊗ T`
  let A' := Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))
  haveI : Finite A' :=
    Finite.of_injective
      (fun f : Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) =>
        (f : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T) → ZMod p))
      DFunLike.coe_injective
  -- cardinality: `E ≃ E ⊗ T ≃ (E ⊗ T)^∨∨`
  have hcard : Nat.card A' = Nat.card E := by
    haveI : Module.Finite (ZMod p) E := Module.Finite.of_finite
    haveI : Module.Finite (ZMod p) T := Module.Finite.of_finite
    haveI : Module.Finite (ZMod p) (TensorProduct (ZMod p) E T) :=
      Module.Finite.tensorProduct (ZMod p) E T
    haveI : Module.IsReflexive (ZMod p) (TensorProduct (ZMod p) E T) := inferInstance
    have e1 : E ≃ₗ[ZMod p] TensorProduct (ZMod p) E T := Work.SSGRoute.PT.e1aIsoE p E T hT.1
    have e2 : TensorProduct (ZMod p) E T ≃ₗ[ZMod p]
        Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)) :=
      Module.evalEquiv (ZMod p) (TensorProduct (ZMod p) E T)
    show Nat.card (Work.SSGRoute.DualMod p (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T)))
        = Nat.card E
    rw [← Nat.card_congr e2.toEquiv, ← Nat.card_congr e1.toEquiv]
  -- the coefficient identification is injective
  have hΦin : Function.Injective
      (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E) :=
    (Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E).injective
  -- the kernel of the localised class is `{b | b c = 0}`
  have hFker : ∀ b : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      (ell (F₀ b) = 0 ↔ b c = 0) := by
    intro b hb hl
    constructor
    · intro h
      have hzero : ∀ m : Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T),
          Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E (b c) m = 0 := fun m =>
        (hsq b hb hl m).mp (by rw [h]; simp)
      exact hΦin (by
        rw [show Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E (b c)
            = 0 from AddMonoidHom.ext hzero, map_zero])
    · intro h
      have h0 : Work.SSGRoute.ExtChain.e1aCoeffNat p k Ω K ζ hζ hζK T hT E (b c) = 0 := by
        rw [h, map_zero]
      exact LinearMap.ext fun m => (hsq b hb hl m).mpr (by rw [h0]; simp)
  -- additivity of the localised canonical class on global cocycles
  have hFadd : ∀ b b' : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
      SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b' → SSGRoute.IsLocConstOn ⊤ b' →
      ell (F₀ (b + b')) = ell (F₀ b) + ell (F₀ b') := by
    intro b b' hb hl hb' hl'
    have hc := (Work.SSGRoute.E1aClean.globalDictionaryCanon_spec
      p k Ω K ζ hζ hζK T hT E).1 b b' hb hl hb' hl'
    have hF₀ : F₀ (b + b') = F₀ b + F₀ b' := by
      show SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E (b + b')))
        = SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k)
            (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))
          + SSGRoute.PTExt.extLoc (k := k) w (SSGRoute.PTExt.extToIdeles (k := k)
              (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b'))
      rw [hc, SSGRoute.PTExt.extToIdeles_add (k := k) (K := K),
        SSGRoute.PTExt.extLoc_add (k := k) (K := K) w]
    rw [hF₀, map_add]
  -- assemble
  obtain ⟨βc, hadd, hker, honto, hsquare⟩ :=
    archSplitPlace_of_kernel p k Ω K E c hc2 hc1 hres h2E A' (fun b => ell (F₀ b))
      hFadd hFker hcard
  -- transport back along `ell`
  set eE : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
      (SSGRoute.PTExt.localUnitsK (k := k) w) 1 ≃+ A' := AddEquiv.ofBijective ell hell with heE
  have hcoe : ∀ x : CategoryTheory.Abelian.Ext
      (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
        (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
          (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
      (SSGRoute.PTExt.localUnitsK (k := k) w) 1, eE x = ell x := fun x => by
    rw [heE]
    exact AddEquiv.ofBijective_apply ell hell x
  refine ⟨fun b => eE.symm (βc b), ?_, ?_, ?_, ?_⟩
  · intro b b' hb hb'
    show eE.symm (βc (b + b')) = eE.symm (βc b) + eE.symm (βc b')
    rw [hadd b b' hb hb', map_add]
  · intro b hb
    show eE.symm (βc b) = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b
    have hiff : (eE.symm (βc b) = 0) ↔ (βc b = 0) :=
      ⟨fun h => by simpa [map_zero] using congrArg eE h, fun h => by rw [h, map_zero]⟩
    rw [hiff]
    exact hker b hb
  · intro y
    show ∃ b : (Ω ≃ₐ[k] Ω) → E,
      SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ eE.symm (βc b) = y
    obtain ⟨b, hb, hβ⟩ := honto (eE y)
    exact ⟨b, hb, by rw [hβ, AddEquiv.symm_apply_apply]⟩
  · intro b hb hl
    show SSGRoute.PTExt.extLoc (k := k) w
        (SSGRoute.PTExt.extToIdeles (k := k)
          (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b))
      = eE.symm (βc b)
    rw [hsquare b hb hl, ← hcoe (F₀ b)]
    exact (AddEquiv.symm_apply_apply eE (F₀ b)).symm

theorem archimedeanDictSplitPlace (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [NumberField ↥K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1)
    (w : NK.GlobalCFT.Place ↥K) (φ : Ω →+* ℂ)
    (hwinf : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hw : w = NK.GlobalCFT.Place.ofInfinite
      (NumberField.InfinitePlace.mk (φ.comp (algebraMap ↥K Ω))))
    (hlink : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x))
    (hbot : SSGRoute.PTExt.decompK (k := k) w = ⊥) :
    ∃ βc : ((Ω ≃ₐ[k] Ω) → E) → CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (K ≃ₐ[k] K)
            (Work.SSGRoute.DualMod p (TensorProduct (ZMod p) E T))))
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1,
      (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b' →
        βc (b + b') = βc b + βc b') ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        (βc b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b)) ∧
      (∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b ∧ βc b = y) ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) ⊤ b → SSGRoute.IsLocConstOn ⊤ b →
        SSGRoute.PTExt.extLoc (k := k) w
          (SSGRoute.PTExt.extToIdeles (k := k)
            (Work.SSGRoute.E1aClean.globalDictionaryCanon p k Ω K ζ hζ hζK T hT E b)) = βc b) := by
  have hp2 : p = 2 :=
    Work.SSGRoute.PT.prime_eq_two_of_decompK_eq_bot p k Ω K ζ hζ hζK c hc2 hc1 w φ hw hlink hbot
  obtain ⟨ell, hellbij, hellreal, -⟩ :=
    Work.SSGRoute.ArchSplit2.ell_bot_family p hp2 k Ω K T w hbot ⟨c, φ, hc2, hc1, hlink, hw⟩
  exact splitPlace_of_ell p hp2 k Ω K ζ hζ hζK T hT E c hc2 hc1 w φ hw hlink hbot (ell E) (hellbij E)
    (fun b hb hl m =>
      Work.SSGRoute.ArchSplit2.archSplit2_square_sign p hp2 k Ω K ζ hζ hζK T hT E c hc2 hc1 φ
        hlink w hw hbot (ell E)
        (fun S hS eS ψ v m hv => hellreal E S hS eS ψ v m hv) b hb hl m)

end Work.SSGRoute.ArchDictionary
