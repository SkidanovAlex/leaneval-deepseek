import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Commons.RepresentationTheory.TateCohomology.tateCohomology_zero_iso
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

namespace Commons.RepresentationTheory.TateCohomology

open CategoryTheory Representation

variable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The `ℤ`-linear representation of `Gal(L/K)` on the additive group of units of `L`. -/
private noncomputable abbrev unitsRep : Representation ℤ (L ≃ₐ[K] L) (Additive (Lˣ)) :=
  Representation.ofMulDistribMulAction (L ≃ₐ[K] L) (Lˣ)

/-- The units of `L` fixed by all `K`-automorphisms are exactly the units of `K` (as a subgroup
of `Lˣ`). -/
private lemma range_units_algebraMap_eq_fixed :
    (MonoidHom.range (Units.map (algebraMap K L : K →* L))) =
      { x : Lˣ | ∀ σ : L ≃ₐ[K] L, σ • x = x } := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ σ
    rw [AlgEquiv.smul_units_def]
    ext
    simp
  · intro hx
    have hfix : ∀ σ : L ≃ₐ[K] L, σ (x : L) = (x : L) := by
      intro σ
      have h := hx σ
      rw [AlgEquiv.smul_units_def] at h
      have h2 := congrArg (fun u : Lˣ => (u : L)) h
      simpa using h2
    have hmem : (x : L) ∈ (⊥ : IntermediateField K L) :=
      (IsGalois.mem_bot_iff_fixed (F := K) (E := L) (x : L)).mpr hfix
    rw [IntermediateField.mem_bot] at hmem
    obtain ⟨k, hk⟩ := hmem
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact Units.ne_zero x (by simpa using hk.symm)
    refine MonoidHom.mem_range.mpr ⟨Units.mk0 k hk0, ?_⟩
    ext
    simp [hk]

/-- Membership in the invariants of the units representation. -/
private lemma mem_invariants_iff (x : Additive (Lˣ)) :
    x ∈ (unitsRep K L).invariants ↔
      Additive.toMul x ∈ MonoidHom.range (Units.map (algebraMap K L : K →* L)) := by
  have hset := range_units_algebraMap_eq_fixed K L
  rw [Representation.mem_invariants]
  constructor
  · intro hx
    refine hset.ge ?_
    intro σ
    have h0 := hx σ
    change Additive.ofMul (σ • Additive.toMul x) = x at h0
    refine Additive.ofMul.injective ?_
    rw [h0, ofMul_toMul]
  · intro hx σ
    have h : σ • Additive.toMul x = Additive.toMul x := hset.le hx σ
    change Additive.ofMul (σ • Additive.toMul x) = x
    rw [h, ofMul_toMul]

/-- The norm of the units representation, evaluated on units. -/
private lemma norm_unitsRep_apply (y : Additive (Lˣ)) :
    (unitsRep K L).norm y
      = Additive.ofMul ((Units.map (algebraMap K L : K →* L))
          ((Units.map (Algebra.norm K : L →* K)) (Additive.toMul y))) := by
  apply Additive.toMul.injective
  rw [toMul_ofMul]
  apply Units.ext
  simp [Representation.norm, Algebra.norm_eq_prod_automorphisms, Units.coe_map]

/-- Membership in the range of the norm of the units representation. -/
private lemma mem_range_norm_iff (x : Additive (Lˣ)) :
    x ∈ LinearMap.range (unitsRep K L).norm ↔
      Additive.toMul x ∈ Subgroup.map (Units.map (algebraMap K L : K →* L))
        (MonoidHom.range (Units.map (Algebra.norm K : L →* K))) := by
  rw [LinearMap.mem_range, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy⟩
    rw [← hy, norm_unitsRep_apply]
    exact ⟨Units.map (Algebra.norm K : L →* K) (Additive.toMul y), ⟨_, rfl⟩, rfl⟩
  · rintro ⟨u, ⟨w, rfl⟩, rfl⟩
    exact ⟨Additive.ofMul w, by rw [norm_unitsRep_apply]; rfl⟩

/-- **The multiplicative `Ĥ⁰` as a group.** For a finite Galois extension `L/K` of fields, the
zeroth Tate cohomology of the units `Lˣ` (with the Galois action) is isomorphic, as a
multiplicative group, to the quotient `Kˣ ⧸ N_{L/K}(Lˣ)` of the units of `K` by the norm group.

This refines the cardinality statement `natCard_tateCohomology_zero_units` to an actual
isomorphism of groups.  The proof follows the same route: `Ĥ⁰` is the quotient `I ⧸ N` of the
invariants by the norm, `Kˣ ≅ I` sits inside the invariants, and the induced surjection
`Kˣ → I ⧸ N` has kernel exactly `N_{L/K}(Lˣ)`. -/
theorem nonempty_mulEquiv_quotient_units_range_norm_tateCohomology_zero
    (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Nonempty ((Kˣ ⧸ MonoidHom.range (Units.map (Algebra.norm K : L →* K))) ≃*
      Multiplicative ↥(tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0)) := by
  classical
  set φ : Kˣ →* Lˣ := Units.map (algebraMap K L : K →* L) with hφ
  set M : Subgroup Kˣ := MonoidHom.range (Units.map (Algebra.norm K : L →* K)) with hM
  set I : Submodule ℤ (Additive (Lˣ)) := (unitsRep K L).invariants with hI
  set N : Submodule ℤ I :=
    (LinearMap.range (unitsRep K L).norm).comap I.subtype with hN
  -- the additive map `ψ : Additive Kˣ →+ I ⧸ N`
  have memI : ∀ a : Additive Kˣ, Additive.ofMul (φ (Additive.toMul a)) ∈ I := fun a => by
    rw [mem_invariants_iff, hφ]
    exact ⟨Additive.toMul a, rfl⟩
  let ψ : Additive Kˣ →+ (I ⧸ N) :=
    AddMonoidHom.mk'
      (fun a : Additive Kˣ =>
        (Submodule.mkQ N) (⟨Additive.ofMul (φ (Additive.toMul a)), memI a⟩ : I))
      (fun a b => by
        have h1 : (⟨Additive.ofMul (φ (Additive.toMul (a + b))), memI (a + b)⟩ : I)
            = (⟨Additive.ofMul (φ (Additive.toMul a)), memI a⟩ : I)
              + (⟨Additive.ofMul (φ (Additive.toMul b)), memI b⟩ : I) := by
          apply Subtype.ext
          simp [toMul_add, ofMul_mul, map_mul]
        show (Submodule.mkQ N) _ = (Submodule.mkQ N) _ + (Submodule.mkQ N) _
        rw [h1, map_add])
  let χ : Kˣ →* Multiplicative (I ⧸ N) := (MonoidHom.toAdditiveLeft.symm ψ)
  have hχ : ∀ w : Kˣ, χ w = Multiplicative.ofAdd (ψ (Additive.ofMul w)) := by
    intro w
    rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    ext
    exact FaithfulSMul.algebraMap_injective K L (by
      have h := congrArg (fun u : Lˣ => (u : L)) hab
      simpa [hφ] using h)
  have hker : χ.ker = M := by
    ext w
    rw [MonoidHom.mem_ker, hM, MonoidHom.mem_range, hχ]
    constructor
    · intro hw
      have h2 : ψ (Additive.ofMul w) = 0 := Multiplicative.ofAdd.injective (by
        rw [hw, ofAdd_zero])
      have h2' : (Submodule.mkQ N) (⟨Additive.ofMul (φ w), memI (Additive.ofMul w)⟩ : I) = 0 := h2
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2'
      rw [hN, Submodule.mem_comap] at h2'
      have h6 := (mem_range_norm_iff K L (Additive.ofMul (φ w))).mp h2'
      obtain ⟨a, ha, heq⟩ := Subgroup.mem_map.mp h6
      obtain ⟨u, rfl⟩ := ha
      exact ⟨u, hinj (by simpa using heq)⟩
    · rintro ⟨u, rfl⟩
      have h3 : (⟨Additive.ofMul (φ (Units.map (Algebra.norm K : L →* K) u)), memI _⟩ : I) ∈ N := by
        rw [hN, Submodule.mem_comap]
        exact (mem_range_norm_iff K L _).mpr
          ⟨Units.map (Algebra.norm K : L →* K) u, ⟨u, rfl⟩, rfl⟩
      have h2' : (Submodule.mkQ N)
          (⟨Additive.ofMul (φ (Units.map (Algebra.norm K : L →* K) u)), memI _⟩ : I) = 0 := by
        rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
        exact h3
      show Multiplicative.ofAdd ((Submodule.mkQ N)
        (⟨Additive.ofMul (φ (Units.map (Algebra.norm K : L →* K) u)), memI _⟩ : I)) = 1
      rw [h2', ofAdd_zero]
  have hsurj : Function.Surjective χ := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨w, hw⟩ : ∃ w : Kˣ, Additive.ofMul (φ w) = (x : Additive (Lˣ)) := by
        have hx := (mem_invariants_iff K L (x : Additive (Lˣ))).mp x.2
        obtain ⟨w, hw⟩ := hx
        exact ⟨w, by rw [hw, ofMul_toMul]⟩
      refine ⟨w, ?_⟩
      have h3 : (⟨Additive.ofMul (φ w), memI (Additive.ofMul w)⟩ : I) = x := Subtype.ext hw
      have hψw : ψ (Additive.ofMul w)
          = (Submodule.mkQ N) ⟨Additive.ofMul (φ w), memI (Additive.ofMul w)⟩ := rfl
      rw [hχ, hψw, h3]
      rfl
  -- the group isomorphism `Kˣ ⧸ N_{L/K}(Lˣ) ≃* Multiplicative (I ⧸ N)`
  have e1 : Kˣ ⧸ M ≃* Multiplicative (I ⧸ N) :=
    (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective χ hsurj)
  -- identify `Multiplicative (I ⧸ N)` with `Multiplicative (Ĥ⁰)`
  obtain ⟨e0⟩ := tateCohomology_zero_iso (unitsRep K L)
  have hrep : Rep.of (unitsRep K L) = Rep.ofAlgebraAutOnUnits K L := rfl
  rw [hrep] at e0
  refine ⟨e1.trans ?_⟩
  exact (e0.toAddEquiv.toMultiplicative).symm

end Commons.RepresentationTheory.TateCohomology