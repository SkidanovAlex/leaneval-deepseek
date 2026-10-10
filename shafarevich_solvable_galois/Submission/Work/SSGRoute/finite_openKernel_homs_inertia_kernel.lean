import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Connected.Separation
import Submission.Work.SSGRoute.finite_H1loc_inertia
import Submission.Work.SSGRoute.isInertia_of_fixes_rootsOfUnity_gen

namespace Work.SSGRoute

open scoped Pointwise

set_option linter.style.haveILetI false

/-- **The clean local/global inertia identification** (general form of
`Work.SSGRoute.mem_localInertia_iff_isInertia`, without the `sorry`-tainted module
`Work.SSGRoute.residueField_residue_pow_eq_one_general`).

Let `k` be a number field, `Ω` an algebraic closure of `k`, `A` a finite place of `Ω` over `k`,
`p` its residue characteristic and assume that every integer prime to `p` is a unit of `↥A`.  Then
the *global* inertia condition `SSGRoute.IsInertia k A σ` is equivalent, under the local/global
identification `NK.FrobeniusBridge.localGaloisEquiv A : D_A ≃* Gal(κ̄/κ)`, to membership of the
image of `σ` in the *local* inertia subgroup `NK.LocalAnabelian.inertiaSubgroup p ≤ Gal(κ̄/κ)`.

The `←` direction is the new content: a local inertia element fixes the prime-to-`p` roots of unity
of `Ω` (`Work.SSGRoute.fixes_rootsOfUnity_of_localInertia`) and an element fixing those acts
trivially on the residue field of `A` (`Work.SSGRoute.isInertia_of_fixes_rootsOfUnity_gen`, which
uses the *clean* `Work.SSGRoute.residueField_residue_pow_eq_one_gen`). -/
theorem mem_localInertia_iff_isInertia_gen_aux
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsSepClosure k Ω] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (hunit : ∀ n : ℕ, ¬ (NK.TameStructureDeep.Tame.resCharAt
        (Submission.NeukirchUchida.primeOf A hA)) ∣ n → IsUnit (n : ↥A))
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ SSGRoute.decomp k A) :
    SSGRoute.IsInertia k A σ ↔
      NK.FrobeniusBridge.localGaloisEquiv ⟨A, hA⟩ ⟨σ, hσ⟩ ∈
        NK.LocalAnabelian.inertiaSubgroup (κ := NK.FrobeniusBridge.localField ⟨A, hA⟩)
          (K' := NK.FrobeniusBridge.localClosure ⟨A, hA⟩)
          (NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A hA)) := by
  set p := NK.TameStructureDeep.Tame.resCharAt (Submission.NeukirchUchida.primeOf A hA) with hp
  set q := NK.LocalStructure.residueCard k (Submission.NeukirchUchida.primeOf A hA) with hq
  have hT : NK.LocalTame.TameData p q (NK.FrobeniusBridge.localField ⟨A, hA⟩)
      (NK.FrobeniusBridge.localClosure ⟨A, hA⟩) :=
    NK.TameData.TameDataInput.toTameData
      (NK.TameStructureDeep.Tame.tameDataInput_adicCompletion_residueChar
        (Submission.NeukirchUchida.primeOf A hA))
  constructor
  · intro h
    refine NK.ResidueFrob.mem_inertiaSubgroup_of_fixes_rootsOfUnity ⟨A, hA⟩ hT hσ ?_
    rintro ζ ⟨n, hpn, hζp⟩
    exact fixes_rootsOfUnity_of_isInertia ⟨A, hA⟩ hunit ⟨σ, hσ⟩ h n hpn ζ hζp
  · intro h
    have hfix : ∀ (n : ℕ), ¬ p ∣ n → ∀ ζ : Ω, IsPrimitiveRoot ζ n → σ ζ = ζ :=
      fixes_rootsOfUnity_of_localInertia k Ω A hA p q hT σ hσ h
    exact isInertia_of_fixes_rootsOfUnity_gen k Ω A hA p
      (charP_residueField_isFinPlace k Ω A hA) σ hσ hfix

/-- **The arithmetic input**: the open-kernel homomorphisms of `N = I_A ⊓ G_K` (the inertia
subgroup of the place `A` inside `G_K`) into a finite `𝔽_p`-module are finite, when `p` is a unit
at `A` (residue characteristic of `A` different from `p`).

ROUTE (do NOT import/use the lemmas `Work.SSGRoute.mem_localInertia_iff_isInertia` or
`Work.SSGRoute.finite_homs_inertia_kernel`: both depend on the `sorry`-tainted module
`Work.SSGRoute.residueField_residue_pow_eq_one_general`, whose two `_TMP` inputs are now proved
elsewhere).  A complete template is the (tainted) proof of `Work.SSGRoute.finite_homs_inertia_kernel`
in `Submission/Work/SSGRoute/finite_H1loc_inertia.lean`; reproduce it replacing the tainted
local/global inertia identification by a clean one built from the *clean* lemma
`Work.SSGRoute.residueField_residue_pow_eq_one_gen` (the general form of
`residueField_residue_pow_eq_one_general`, with the residue characteristic `p₀` supplied as a
`CharP (ResidueField ↥A) p₀` hypothesis) together with
`Work.SSGRoute.fixes_rootsOfUnity_of_localInertia`.  The finiteness of the local inertia then comes
from the clean `Work.SSGRoute.finite_homs_local_inertia` via
`Work.SSGRoute.finite_homs_of_continuous_injective`. -/
theorem finite_openKernel_homs_inertia_kernel
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [Finite M] :
    Finite {χ : ↥(SSGRoute.inertiaSub k Ω A ⊓ K.fixingSubgroup) →* Multiplicative M //
      IsOpen (χ.ker : Set ↥(SSGRoute.inertiaSub k Ω A ⊓ K.fixingSubgroup))} := by
  classical
  -- `↥K` is a number field, an algebraic closure of it and a separable closure of it
  haveI hNFK : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) K
  haveI hAlgK : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI hsepK : IsSepClosure ↥K Ω := IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
  have hAK : A.comap (algebraMap ↥K Ω) ≠ ⊤ := by
    intro hh
    apply hA
    rw [eq_top_iff]
    intro x _
    rw [ValuationSubring.mem_comap]
    have hx : algebraMap k ↥K x ∈ A.comap (algebraMap ↥K Ω) := by rw [hh]; trivial
    rwa [ValuationSubring.mem_comap] at hx
  -- the prime `𝔭` of `↥K` below `A`, the residue characteristic of `A`
  let 𝔭 := Submission.NeukirchUchida.primeOf A hAK
  have h𝔭 : A.comap (algebraMap ↥K Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥K 𝔭 :=
    Submission.NeukirchUchida.primeOf_spec A hAK
  let p₀ := NK.TameStructureDeep.Tame.resCharAt 𝔭
  have hp₀ : p₀.Prime := NK.Mine.prime_ringChar_residueField_adicCompletion 𝔭
  -- the residue characteristic of `A` is not `p`: `p` is a unit of `A`, but `p₀ ∣ p₀`
  have hp₀ne : p₀ ≠ p := by
    intro hpeq
    have hpu : IsUnit (p : ↥A) := by
      rw [← IsLocalRing.notMem_maximalIdeal, ValuationSubring.valuation_lt_one_iff]
      have hc : (((p : ↥A)) : Ω) = ((p : ℚ) : Ω) := by
        norm_num
      rw [hc]
      exact h
    have hnot : ¬ IsUnit (p : ↥A) := by
      have hiff := isUnit_natCast_iff_not_dvd_resCharAt ↥K Ω A hAK p
      rw [hiff]
      exact fun hd => hd (hpeq ▸ dvd_refl p)
    exact hnot hpu
  -- the local structure input and the finiteness of the local inertia
  have hT : NK.TameData.TameInertiaInput p₀ (𝔭.adicCompletion ↥K)
      (SeparableClosure (𝔭.adicCompletion ↥K)) :=
    NK.TameStructureDeep.Tame.tameInertiaInput_adicCompletion_residueChar 𝔭
  have hloc : Finite {χ : ↥(NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion ↥K)
        (K' := SeparableClosure (𝔭.adicCompletion ↥K)) p₀) →* Multiplicative M //
      IsOpen (χ.ker : Set ↥(NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion ↥K)
        (K' := SeparableClosure (𝔭.adicCompletion ↥K)) p₀))} :=
    finite_homs_local_inertia p₀ hT p (Fact.out) hp₀ne M
  -- the local/global identification
  letI : Algebra (𝔭.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A h𝔭).toAlgebra
  have halg : ∀ z : 𝔭.adicCompletion ↥K,
      (algebraMap (𝔭.adicCompletion ↥K) (NK.NeukirchUchida.placeCompletion A)) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A h𝔭 z := fun z => rfl
  have hW :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers 𝔭 A h𝔭
  haveI : IsSepClosure (𝔭.adicCompletion ↥K)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion 𝔭 A) :=
    NK.Mine.isSepClosure_adjoinPlaceCompletion 𝔭 A h𝔭 halg
  let e₂ : ↥(SSGRoute.decomp ↥K A) ≃*
      Gal(SeparableClosure (𝔭.adicCompletion ↥K)/(𝔭.adicCompletion ↥K)) :=
    NK.Mine.localGaloisEquiv 𝔭 A h𝔭 halg hW
  have he₂ : IsHomeomorph
      (e₂ : ↥(SSGRoute.decomp ↥K A) →
        Gal(SeparableClosure (𝔭.adicCompletion ↥K)/(𝔭.adicCompletion ↥K))) :=
    NK.Mine.isHomeomorph_trans (NK.Mine.adjoinLocalEquiv 𝔭 A h𝔭 halg hW)
      (AlgEquiv.autCongr (NK.Mine.adjoinSepEquiv 𝔭 A h𝔭 halg))
      (NK.Mine.isHomeomorph_adjoinLocalEquiv 𝔭 A h𝔭 halg hW)
      (NK.Mine.isHomeomorph_autCongr (NK.Mine.adjoinSepEquiv 𝔭 A h𝔭 halg))
  let e₁ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) ≃* ↥(SSGRoute.decomp ↥K A) :=
    decompEquiv_fok k Ω K A
  have he₁ : IsHomeomorph
      (e₁ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) → ↥(SSGRoute.decomp ↥K A)) :=
    isHomeomorph_decompEquiv_fok k Ω K A
  let E : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) ≃*
      Gal(SeparableClosure (𝔭.adicCompletion ↥K)/(𝔭.adicCompletion ↥K)) := e₁.trans e₂
  have hE : IsHomeomorph
      (E : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) →
        Gal(SeparableClosure (𝔭.adicCompletion ↥K)/(𝔭.adicCompletion ↥K))) :=
    NK.Mine.isHomeomorph_trans e₁ e₂ he₁ he₂
  -- the local inertia subgroup is the image of the inertia subgroup at the level `↥K`
  have hchoice : ∀ w : ↥(SSGRoute.decomp ↥K A),
      (NK.FrobeniusBridge.localGaloisEquiv ⟨A, hAK⟩ w ∈
          NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion ↥K)
            (K' := SeparableClosure (𝔭.adicCompletion ↥K)) p₀) ↔
        (e₂ w ∈ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion ↥K)
            (K' := SeparableClosure (𝔭.adicCompletion ↥K)) p₀) := by
    intro w
    have hTd : NK.LocalTame.TameData p₀ (NK.LocalStructure.residueCard ↥K 𝔭)
        (𝔭.adicCompletion ↥K) (SeparableClosure (𝔭.adicCompletion ↥K)) :=
      NK.TameData.TameDataInput.toTameData
        (NK.TameStructureDeep.Tame.tameDataInput_adicCompletion_residueChar 𝔭)
    have hh := NK.LocalTame.inertiaOfDecomposition_iff_of_localIso hTd
      (NK.FrobeniusBridge.localGaloisEquiv ⟨A, hAK⟩) e₂ w
    have h1 : w ∈ NK.LocalTame.inertiaOfDecomposition p₀
          (NK.FrobeniusBridge.localGaloisEquiv ⟨A, hAK⟩) ↔
        NK.FrobeniusBridge.localGaloisEquiv ⟨A, hAK⟩ w ∈
          NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion ↥K)
            (K' := SeparableClosure (𝔭.adicCompletion ↥K)) p₀ := Subgroup.mem_comap
    have h2 : w ∈ NK.LocalTame.inertiaOfDecomposition p₀ e₂ ↔
        e₂ w ∈ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion ↥K)
            (K' := SeparableClosure (𝔭.adicCompletion ↥K)) p₀ := Subgroup.mem_comap
    exact h1.symm.trans (hh.trans h2)
  -- the identification of the inertia elements of the level `↥K` with the local inertia
  have hiff : ∀ w : ↥(SSGRoute.decomp ↥K A),
      ((w : Ω ≃ₐ[↥K] Ω) ∈ inertiaSub ↥K Ω A) ↔
        (e₂ w ∈ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion ↥K)
            (K' := SeparableClosure (𝔭.adicCompletion ↥K)) p₀) := by
    intro w
    have hmain := mem_localInertia_iff_isInertia_gen_aux ↥K Ω A hAK
      (fun n hn => isUnit_natCast_of_not_dvd_resCharAt ↥K Ω A hAK n hn) w.1 w.2
    exact hmain.trans (hchoice w)
  -- the composite homomorphism
  have hND : inertiaSub k Ω A ⊓ K.fixingSubgroup ≤ SSGRoute.decomp k A ⊓ K.fixingSubgroup :=
    inf_le_inf (inertiaSub_le_decomp k Ω A) le_rfl
  let θ : ↥(inertiaSub k Ω A ⊓ K.fixingSubgroup) →*
      Gal(SeparableClosure (𝔭.adicCompletion ↥K)/(𝔭.adicCompletion ↥K)) :=
    E.toMonoidHom.comp (Subgroup.inclusion hND)
  have hinc : Continuous (Subgroup.inclusion hND :
      ↥(inertiaSub k Ω A ⊓ K.fixingSubgroup) →
        ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) :=
    Continuous.subtype_mk continuous_subtype_val fun x => hND x.2
  have hθcont : Continuous (θ : ↥(inertiaSub k Ω A ⊓ K.fixingSubgroup) →
      Gal(SeparableClosure (𝔭.adicCompletion ↥K)/(𝔭.adicCompletion ↥K))) :=
    hE.continuous.comp hinc
  have hθinj : Function.Injective (θ : ↥(inertiaSub k Ω A ⊓ K.fixingSubgroup) →
      Gal(SeparableClosure (𝔭.adicCompletion ↥K)/(𝔭.adicCompletion ↥K))) :=
    fun a b hab => Subgroup.inclusion_injective _ (E.injective hab)
  -- the identification `x ∈ N ↔ E x ∈ I_κ`
  have hmap : ∀ x : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup),
      ((x : Ω ≃ₐ[k] Ω) ∈ inertiaSub k Ω A) ↔
        (E x ∈ NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion ↥K)
          (K' := SeparableClosure (𝔭.adicCompletion ↥K)) p₀) := by
    intro x
    have hbase : ((x : Ω ≃ₐ[k] Ω) ∈ inertiaSub k Ω A) ↔
        ((e₁ x : Ω ≃ₐ[↥K] Ω) ∈ inertiaSub ↥K Ω A) := by
      have hh := fixingSubgroupEquiv_mem_inertiaSub k Ω K A (x : Ω ≃ₐ[k] Ω) x.2.2
      have h1 : (e₁ x : Ω ≃ₐ[↥K] Ω) =
          ((IntermediateField.fixingSubgroupEquiv K) ⟨(x : Ω ≃ₐ[k] Ω), x.2.2⟩ :
            Ω ≃ₐ[↥K] Ω) := AlgEquiv.ext fun _ => rfl
      rw [h1]
      exact hh
    rw [hbase]
    have h2 : ((e₁ x : Ω ≃ₐ[↥K] Ω) ∈ inertiaSub ↥K Ω A) ↔ (e₂ (e₁ x) ∈
        NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion ↥K)
          (K' := SeparableClosure (𝔭.adicCompletion ↥K)) p₀) := hiff (e₁ x)
    rw [h2]
    rfl
  have hrange : Set.range (θ : ↥(inertiaSub k Ω A ⊓ K.fixingSubgroup) →
      Gal(SeparableClosure (𝔭.adicCompletion ↥K)/(𝔭.adicCompletion ↥K))) =
      (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion ↥K)
        (K' := SeparableClosure (𝔭.adicCompletion ↥K)) p₀ : Set _) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      have hx : (x : Ω ≃ₐ[k] Ω) ∈ inertiaSub k Ω A := (Subgroup.mem_inf.mp x.2).1
      have hθx : θ x = E ⟨(x : Ω ≃ₐ[k] Ω), hND x.2⟩ := rfl
      rw [hθx]
      exact (hmap ⟨(x : Ω ≃ₐ[k] Ω), hND x.2⟩).mp hx
    · intro hy
      let w : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) := E.symm y
      have hw : E w = y := E.apply_symm_apply y
      have hwm : (w : Ω ≃ₐ[k] Ω) ∈ inertiaSub k Ω A := (hmap w).mpr (by rw [hw]; exact hy)
      have hwK : (w : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup := w.2.2
      refine ⟨⟨(w : Ω ≃ₐ[k] Ω), Subgroup.mem_inf.mpr ⟨hwm, hwK⟩⟩, ?_⟩
      show θ ⟨(w : Ω ≃ₐ[k] Ω), Subgroup.mem_inf.mpr ⟨hwm, hwK⟩⟩ = y
      have hθw : θ ⟨(w : Ω ≃ₐ[k] Ω), Subgroup.mem_inf.mpr ⟨hwm, hwK⟩⟩
          = E ⟨(w : Ω ≃ₐ[k] Ω), hND (Subgroup.mem_inf.mpr ⟨hwm, hwK⟩)⟩ := rfl
      rw [hθw]
      have : (⟨(w : Ω ≃ₐ[k] Ω), hND (Subgroup.mem_inf.mpr ⟨hwm, hwK⟩)⟩ :
          ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup)) = w := Subtype.ext rfl
      rw [this, hw]
  -- the local inertia subgroup is closed, so its preimage `N` is compact
  have hKcl : IsClosed (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion ↥K)
      (K' := SeparableClosure (𝔭.adicCompletion ↥K)) p₀ :
        Set (Gal(SeparableClosure (𝔭.adicCompletion ↥K)/(𝔭.adicCompletion ↥K)))) :=
    NK.TameStructureDeep.inertiaSubgroup_isClosed p₀
  have hNcl : IsClosed
      ((inertiaSub k Ω A ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    isClosed_inertiaSub_kernel k Ω K A
  haveI : CompactSpace ↥(inertiaSub k Ω A ⊓ K.fixingSubgroup) :=
    isCompact_iff_compactSpace.mp hNcl.isCompact
  exact finite_homs_of_continuous_injective θ hθcont hθinj
    (NK.LocalAnabelian.inertiaSubgroup (κ := 𝔭.adicCompletion ↥K)
      (K' := SeparableClosure (𝔭.adicCompletion ↥K)) p₀) hKcl hrange hloc

end Work.SSGRoute
