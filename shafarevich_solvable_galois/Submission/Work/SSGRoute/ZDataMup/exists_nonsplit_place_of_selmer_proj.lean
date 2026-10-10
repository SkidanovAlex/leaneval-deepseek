import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.ZConstruction.exists_finset_ramifiedPlaces
import Submission.Work.SSGRoute.ZDataMup.finrank_lcCocycleImage_eq_one_of_not_residueChar_proj
import Submission.Work.SSGRoute.adjoin_primitiveRoot_isGalois_coprime
import Submission.Work.SSGRoute.exists_mem_closure_decomp_mul_mem_fixingSubgroup
import Submission.Work.SSGRoute.frobeniusClass_realisation_below
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END
set_option synthInstance.maxHeartbeats 400000

namespace Work.SSGRoute.ZDataMup

/-! The Cebotarev input of the non-self-dual half, restated in the target file's own vocabulary.

This is `Work.SSGRoute.ZDataMup.exists_nonsplit_place_of_selmer` (PROVED, in the file
`ZDataMup/exists_nonsplit_place_of_selmer.lean`; read it and copy the argument) with the coefficient
action passed as instance variables.  It must be proved in a module that does NOT (transitively)
import `Submission.Work.SSGRoute.sha2_defs` or `Submission.Work.SSGRoute.mup_local_defs`, because
the target file `ZDataMup/tatePoitou_h1_realisation.lean` cannot import any module that does (see
`ZDataMup/PING_triv_instance_diamond.md`).  Import only the modules of `depends_on`; in particular
do NOT import `ZDataMup/exists_nonsplit_place_of_selmer` itself. -/

open _root_.SSGRoute

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## 0. The `ζ_p`-vs-decomposition-group input, proved without the `Triv`/`TrivMod` instances

The reference proof of the target consumes
`Work.SSGRoute.PTCore.zetaIndicator_adicCompletion_eq_one_iff_decomp_fixes`, whose module
transitively imports `sha2_defs` and `mup_local_defs` (via `PTembedding.KummerMuDefs`), and which
therefore may not be imported here.  The lemma itself is coefficient-action free, so it is
re-established below in this file, importing only the *definitional* modules
(`NK.NeukirchUchida.nonempty_mulEquiv_decompositionGroupOf_adjoin`, `NK.Mine.AdjoinLocalGalois`),
which are free of the offending global instances. -/

section Zeta

/-- **The image of `Ω` in `M = 𝔨·Ω` as a ring hom.**  This is
`NK.NeukirchUchida.coInAdjoin` packaged as a ring hom; the same definition lives in
`Work.SSGRoute.PTembedding.rootsOfUnity_addEquiv_adjoinLocalEquiv`, but that module (via
`PTembedding.kummer_decomp`) imports `sha2_defs`, so it is duplicated here. -/
noncomputable def coInAdjoinHomClean {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A)] :
    Ω →+* ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := k) (K' := Ω) 𝔭 A) where
  toFun := NK.NeukirchUchida.coInAdjoin 𝔭 A
  map_one' := NK.NeukirchUchida.coInAdjoin_one 𝔭 A
  map_mul' := NK.NeukirchUchida.coInAdjoin_mul 𝔭 A
  map_zero' := NK.NeukirchUchida.coInAdjoin_zero 𝔭 A
  map_add' := NK.NeukirchUchida.coInAdjoin_add 𝔭 A

@[simp] theorem coInAdjoinHomClean_apply {k : Type} [Field k] [NumberField k] {Ω : Type}
    [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A)] (y : Ω) :
    coInAdjoinHomClean 𝔭 A y = NK.NeukirchUchida.coInAdjoin 𝔭 A y := rfl

/-- `coInAdjoinHomClean` is injective: its values are the places of `Ω` inside the completion. -/
theorem coInAdjoinHomClean_injective {k : Type} [Field k] [NumberField k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsSepClosure k Ω]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (A : ValuationSubring Ω)
    [Algebra (IsDedekindDomain.HeightOneSpectrum.adicCompletion k 𝔭)
      (NK.NeukirchUchida.placeCompletion A)] :
    Function.Injective (coInAdjoinHomClean 𝔭 A) := by
  intro x y hxy
  refine RingHom.injective (NK.NeukirchUchida.placeCompletionCoe A) ?_
  exact congrArg (fun z : ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := k) (K' := Ω) 𝔭 A) =>
    (z : NK.NeukirchUchida.placeCompletion A)) hxy

/-- **`ζ_p ∈ k_𝔭` as a decomposition-group-fixing condition.**  If some element of the decomposition
group fixes `ζ`, then `k_𝔭` contains a primitive `p`-th root of unity, and conversely.

This is a copy of `Work.SSGRoute.PTCore.zetaIndicator_adicCompletion_eq_one_iff_decomp_fixes` with
the `sha2_defs`-free import closure. -/
theorem zetaIndicator_adicCompletion_eq_one_iff_decomp_fixes_clean
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) :
    (NK.LocalInputs.zetaIndicator p ((Submission.NeukirchUchida.primeOf A hA).adicCompletion k) = 1) ↔
      (∀ σ ∈ SSGRoute.decomp k A, σ • ζ = ζ) := by
  classical
  haveI : IsSepClosure k Ω := IsSepClosure.of_isAlgClosure_of_perfectField k Ω
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let 𝔭 := Submission.NeukirchUchida.primeOf A hA
  let hp := Submission.NeukirchUchida.primeOf_spec A hA
  change (NK.LocalInputs.zetaIndicator p (𝔭.adicCompletion k) = 1) ↔
    (∀ σ ∈ SSGRoute.decomp k A, σ • ζ = ζ)
  letI : Algebra (𝔭.adicCompletion k) (NK.NeukirchUchida.placeCompletion A) :=
    (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hp).toAlgebra
  have halg : ∀ z : 𝔭.adicCompletion k,
      (algebraMap (𝔭.adicCompletion k) (NK.NeukirchUchida.placeCompletion A)) z =
        NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hp z := fun z => rfl
  have hW : (NK.NeukirchUchida.placeCompletionIntegers A).comap
      (NK.NeukirchUchida.adicCompletionToPlaceCompletion 𝔭 A hp) =
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers k 𝔭 :=
    NK.NeukirchUchida.comap_adicCompletionToPlaceCompletion_eq_adicCompletionIntegers 𝔭 A hp
  haveI hSepM : IsSepClosure (𝔭.adicCompletion k)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := k) (K' := Ω) 𝔭 A) :=
    NK.Mine.isSepClosure_adjoinPlaceCompletion 𝔭 A hp halg
  haveI hGalM : IsGalois (𝔭.adicCompletion k)
      ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := k) (K' := Ω) 𝔭 A) := hSepM.isGalois
  let M := ↥(NK.NeukirchUchida.adjoinPlaceCompletion (K := k) (K' := Ω) 𝔭 A)
  let e := NK.Mine.adjoinLocalEquiv (K := k) (K' := Ω) 𝔭 A hp halg hW
  have hζM : IsPrimitiveRoot (NK.NeukirchUchida.coInAdjoin 𝔭 A ζ) p := by
    have h := hζ.map_of_injective (f := coInAdjoinHomClean 𝔭 A)
      (coInAdjoinHomClean_injective 𝔭 A)
    rwa [coInAdjoinHomClean_apply] at h
  constructor
  · intro hn σ hσ
    obtain ⟨z, hz⟩ := (NK.LocalInputs.zetaIndicator_eq_one_iff p (𝔭.adicCompletion k)).mp hn
    have hzM : IsPrimitiveRoot (algebraMap (𝔭.adicCompletion k) M z) p :=
      hz.map_of_injective (f := algebraMap (𝔭.adicCompletion k) M) (RingHom.injective _)
    obtain ⟨i, -, hi⟩ := hzM.eq_pow_of_pow_eq_one hζM.pow_eq_one
    have hco := NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin (K := k) (K' := Ω)
      𝔭 A hp halg (⟨σ, hσ⟩ : ↥(NK.Mine.decompositionGroupOf k Ω A)) ζ
    have key : (NK.NeukirchUchida.decompositionToAdjoin (K := k) (K' := Ω) 𝔭 A hp halg
        (⟨σ, hσ⟩ : ↥(NK.Mine.decompositionGroupOf k Ω A)))
        (NK.NeukirchUchida.coInAdjoin 𝔭 A ζ) = NK.NeukirchUchida.coInAdjoin 𝔭 A ζ := by
      rw [← hi, map_pow]
      congr 1
      exact (NK.NeukirchUchida.decompositionToAdjoin (K := k) (K' := Ω) 𝔭 A hp halg
        (⟨σ, hσ⟩ : ↥(NK.Mine.decompositionGroupOf k Ω A))).commutes z
    rw [hco] at key
    have hfixζ : σ ζ = ζ :=
      (coInAdjoinHomClean_injective 𝔭 A)
        (by simp only [coInAdjoinHomClean_apply]; exact key)
    simpa [AlgEquiv.smul_def] using hfixζ
  · intro hfix
    have hfixed : ∀ f : Gal(M/𝔭.adicCompletion k),
        f (NK.NeukirchUchida.coInAdjoin 𝔭 A ζ) = NK.NeukirchUchida.coInAdjoin 𝔭 A ζ := by
      intro f
      obtain ⟨σ, rfl⟩ := e.surjective f
      rw [show e σ = NK.NeukirchUchida.decompositionToAdjoin (K := k) (K' := Ω) 𝔭 A hp halg σ
          from rfl,
        NK.NeukirchUchida.decompositionToAdjoin_coInAdjoin]
      congr 1
      simpa [AlgEquiv.smul_def] using hfix σ.1 σ.2
    obtain ⟨z, hz⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := 𝔭.adicCompletion k)
      (K := M) (NK.NeukirchUchida.coInAdjoin 𝔭 A ζ)).mpr hfixed
    refine (NK.LocalInputs.zetaIndicator_eq_one_iff p (𝔭.adicCompletion k)).mpr ⟨z, ?_⟩
    have h2 : IsPrimitiveRoot (algebraMap (𝔭.adicCompletion k) M z) p := hz ▸ hζM
    exact h2.of_map_of_injective (RingHom.injective _)

end Zeta

/-! ## 1. The additive character of `G_K` cut out by a Selmer class -/

section Character

variable {p : ℕ} [NeZero p] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
  {K : IntermediateField k Ω} [Normal k K]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] {b : (Ω ≃ₐ[k] Ω) → ZMod p}

/-- `b 1 = 0` for a `1`-cocycle on `G_K`: the cocycle relation at `g = h = 1`. -/
theorem b_one_eq_zero (hb : IsCocycleOn (res k K) K.fixingSubgroup b) : b 1 = 0 := by
  have h := hb 1 (one_mem _) 1 (one_mem _)
  simp only [mul_one, map_one, one_smul] at h
  have h2 : b 1 + 0 = b 1 + b 1 := by rw [add_zero, ← h]
  exact (add_left_cancel h2).symm

/-- On `G_K` the cocycle `b` is additive: the coefficient action is trivial there. -/
theorem b_add_of_mem_fixingSubgroup (hb : IsCocycleOn (res k K) K.fixingSubgroup b)
    {g h : Ω ≃ₐ[k] Ω} (hg : g ∈ K.fixingSubgroup) (hh : h ∈ K.fixingSubgroup) :
    b (g * h) = b g + b h := by
  rw [hb g hg h hh, res_eq_one_of_mem_fixingSubgroup hg, one_smul]

/-- **The `b`-kernel**: the elements of `G_K` on which the cocycle vanishes. -/
def bKer (hb : IsCocycleOn (res k K) K.fixingSubgroup b) : Subgroup (Ω ≃ₐ[k] Ω) where
  carrier := {g | g ∈ K.fixingSubgroup ∧ b g = 0}
  one_mem' := ⟨one_mem _, b_one_eq_zero hb⟩
  mul_mem' := by
    rintro g h ⟨hg, hg0⟩ ⟨hh, hh0⟩
    refine ⟨mul_mem hg hh, ?_⟩
    have h := b_add_of_mem_fixingSubgroup hb hg hh
    rw [hg0, hh0, add_zero] at h
    exact h
  inv_mem' := by
    rintro g ⟨hg, hg0⟩
    refine ⟨inv_mem hg, ?_⟩
    have h1 := hb g⁻¹ (inv_mem hg) g hg
    rw [inv_mul_cancel, b_one_eq_zero hb, hg0] at h1
    simp only [smul_zero, add_zero] at h1
    exact h1.symm

theorem mem_bKer_iff (hb : IsCocycleOn (res k K) K.fixingSubgroup b) {g : Ω ≃ₐ[k] Ω} :
    g ∈ bKer hb ↔ g ∈ K.fixingSubgroup ∧ b g = 0 := Iff.rfl

theorem bKer_le (hb : IsCocycleOn (res k K) K.fixingSubgroup b) :
    bKer hb ≤ K.fixingSubgroup := fun _ hg => hg.1

/-- The `b`-kernel is open in `G_k`: it contains the intersection of `G_K` with a locally constant
neighbourhood of `1`. -/
theorem isOpen_bKer [FiniteDimensional k K] (hb : IsCocycleOn (res k K) K.fixingSubgroup b)
    (hlc : IsLocConstOn K.fixingSubgroup b) :
    IsOpen ((bKer hb : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) := by
  obtain ⟨U, hUop, hUc⟩ := hlc
  have hmem : (U ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) ≤ bKer hb := by
    rintro u ⟨huU, huK⟩
    refine ⟨huK, ?_⟩
    -- local constancy at `g = u⁻¹` gives `b 1 = b u⁻¹`
    have h1 : b (u⁻¹ * u) = b u⁻¹ := hUc u⁻¹ (inv_mem huK) u huU huK
    rw [inv_mul_cancel] at h1
    have h2 : b u⁻¹ = 0 := by rw [← h1, b_one_eq_zero hb]
    -- additivity on `G_K` then gives `b u = 0`
    have h3 : b (u * u⁻¹) = b u + b u⁻¹ := b_add_of_mem_fixingSubgroup hb huK (inv_mem huK)
    rw [mul_inv_cancel, b_one_eq_zero hb, h2, add_zero] at h3
    exact h3.symm
  exact Subgroup.isOpen_mono hmem (hUop.inter (IntermediateField.fixingSubgroup_isOpen K))

/-- **A non-zero cocycle on `G_K` has an element which is both non-zero on `b` and moves the
primitive `p`-th root of unity `ζ`.**  A group is not the union of two proper subgroups: the
`b`-kernel is proper by hypothesis, and the subgroup fixing `ζ` is proper because `ζ ∉ K`. -/
theorem exists_mem_fixingSubgroup_b_ne_zero_and_moves [IsGalois k Ω]
    (hb : IsCocycleOn (res k K) K.fixingSubgroup b)
    (hbne : ∃ g ∈ K.fixingSubgroup, b g ≠ 0) {ζ : Ω} (hζ : IsPrimitiveRoot ζ p)
    (hζK : ζ ∉ K) :
    ∃ g ∈ K.fixingSubgroup, b g ≠ 0 ∧ g ζ ≠ ζ := by
  by_contra hcon
  have hcon' : ∀ g ∈ K.fixingSubgroup, b g = 0 ∨ g ζ = ζ := by
    intro g hg
    by_contra h
    rw [not_or] at h
    exact hcon ⟨g, hg, h.1, h.2⟩
  obtain ⟨x, hx, hx0⟩ := hbne
  have hyl : ∃ y ∈ K.fixingSubgroup, y ζ ≠ ζ := by
    by_contra h
    push_neg at h
    exact hζK (by
      rw [← InfiniteGalois.fixedField_fixingSubgroup K, IntermediateField.mem_fixedField_iff]
      intro g hg
      exact h g hg)
  obtain ⟨y, hy, hyζ⟩ := hyl
  rcases hcon' x hx with hx0' | hxfix
  · exact hx0 hx0'
  · rcases hcon' y hy with hy0 | hyfix
    · rcases hcon' (x * y) (mul_mem hx hy) with hxy0 | hxyfix
      · -- `b (x * y) = b x + b y = b x ≠ 0`
        have h : b (x * y) = b x + b y := b_add_of_mem_fixingSubgroup hb hx hy
        rw [hxy0, hy0, add_zero] at h
        exact hx0 h.symm
      · -- `x` fixes `ζ`, so `x * y` fixes `ζ` only if `y` does
        obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (show (y ζ) ^ p = 1 by
          rw [← map_pow, hζ.pow_eq_one, map_one])
        have hxy : (x * y) ζ = y ζ := by
          have h1 : (x * y) ζ = x (y ζ) := AlgEquiv.mul_apply x y ζ
          have h2 : x (y ζ) = x (ζ ^ i) := by rw [← hi]
          have h3 : x (ζ ^ i) = (x ζ) ^ i := map_pow x ζ i
          rw [h1, h2, h3, hxfix, hi]
        exact hyζ (hxy ▸ hxyfix)
    · exact hyζ hyfix

end Character

/-! ## 2. Transfer of elements and of `b`-values along the restriction to a finite level -/

section Transfer

variable {p : ℕ} [NeZero p] {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω]
  {K : IntermediateField k Ω} [Normal k K] {N : IntermediateField k Ω} [Normal k N]
  [DistribMulAction (K ≃ₐ[k] K) (ZMod p)]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)] {b : (Ω ≃ₐ[k] Ω) → ZMod p}

/-- An element of `G_k` whose restriction to a finite Galois level `N ⊇ K` agrees with `g` inherits
the property of fixing `K` pointwise (from `g`). -/
theorem mem_fixingSubgroup_of_restrictNormalHom_eq (hKN : K ≤ N)
    {g h : Ω ≃ₐ[k] Ω} (hg : g ∈ K.fixingSubgroup)
    (hres : AlgEquiv.restrictNormalHom N h = AlgEquiv.restrictNormalHom N g) :
    h ∈ K.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have h1 : ((AlgEquiv.restrictNormalHom N h) ⟨x, hKN hx⟩ : Ω) = h x :=
    AlgEquiv.restrictNormalHom_apply N h ⟨x, hKN hx⟩
  have h2 : ((AlgEquiv.restrictNormalHom N g) ⟨x, hKN hx⟩ : Ω) = g x :=
    AlgEquiv.restrictNormalHom_apply N g ⟨x, hKN hx⟩
  have h3 : (AlgEquiv.restrictNormalHom N g) ⟨x, hKN hx⟩ = ⟨x, hKN hx⟩ := by
    apply Subtype.ext
    rw [h2]
    exact (IntermediateField.mem_fixingSubgroup_iff K g).mp hg x hx
  calc h x = ((AlgEquiv.restrictNormalHom N h) ⟨x, hKN hx⟩ : Ω) := h1.symm
    _ = ((AlgEquiv.restrictNormalHom N g) ⟨x, hKN hx⟩ : Ω) := by rw [hres]
    _ = (⟨x, hKN hx⟩ : ↥N) := by rw [h3]
    _ = x := rfl

/-- Elements of `G_k` restricting to the same element of a finite Galois level `N` have the same
action on the elements of `N`. -/
theorem apply_eq_of_restrictNormalHom_eq
    {g h : Ω ≃ₐ[k] Ω} (hres : AlgEquiv.restrictNormalHom N h = AlgEquiv.restrictNormalHom N g)
    {x : Ω} (hx : x ∈ N) : h x = g x := by
  have h1 : ((AlgEquiv.restrictNormalHom N h) ⟨x, hx⟩ : Ω) = h x :=
    AlgEquiv.restrictNormalHom_apply N h ⟨x, hx⟩
  have h2 : ((AlgEquiv.restrictNormalHom N g) ⟨x, hx⟩ : Ω) = g x :=
    AlgEquiv.restrictNormalHom_apply N g ⟨x, hx⟩
  rw [← h1, hres, h2]

/-- **`b` is constant on the fibres of the restriction to a level `N` containing the fixed field of
its kernel.**  Indeed the kernel of the restriction on `G_K` is `Gal(Ω/N) ≤ Gal(Ω/L) = bKer`. -/
theorem b_eq_of_restrictNormalHom_eq {L : IntermediateField k Ω}
    (hb : IsCocycleOn (res k K) K.fixingSubgroup b) (hLN : L ≤ N)
    (hLfix : L.fixingSubgroup = bKer hb)
    {g h : Ω ≃ₐ[k] Ω} (hg : g ∈ K.fixingSubgroup) (hh : h ∈ K.fixingSubgroup)
    (hres : AlgEquiv.restrictNormalHom N g = AlgEquiv.restrictNormalHom N h) : b g = b h := by
  have hgh : g * h⁻¹ ∈ K.fixingSubgroup := mul_mem hg (inv_mem hh)
  have hres1 : AlgEquiv.restrictNormalHom N (g * h⁻¹) = 1 := by
    rw [map_mul, hres, map_inv, mul_inv_cancel]
  have hmemN : g * h⁻¹ ∈ N.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker N, MonoidHom.mem_ker]
    exact hres1
  have hmemL : g * h⁻¹ ∈ L.fixingSubgroup := IntermediateField.fixingSubgroup_le hLN hmemN
  have hb0 : b (g * h⁻¹) = 0 := by
    rw [hLfix, mem_bKer_iff] at hmemL
    exact hmemL.2
  have hadd : b ((g * h⁻¹) * h) = b (g * h⁻¹) + b h :=
    b_add_of_mem_fixingSubgroup hb hgh hh
  rw [mul_assoc, inv_mul_cancel, mul_one, hb0, zero_add] at hadd
  exact hadd

/-- The trace on `k` of a place is invariant under an element of `G_K`. -/
theorem comap_smul_eq_of_mem_fixingSubgroup {A : ValuationSubring Ω} {g : Ω ≃ₐ[k] Ω}
    (hg : g ∈ K.fixingSubgroup) :
    (g • A).comap (algebraMap k Ω) = A.comap (algebraMap k Ω) := by
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  have hfix : (g⁻¹ : Ω ≃ₐ[k] Ω) • (algebraMap k Ω x) = algebraMap k Ω x := by
    rw [AlgEquiv.smul_def]
    exact (IntermediateField.mem_fixingSubgroup_iff K (g⁻¹)).mp (inv_mem hg) _
      (K.algebraMap_mem x)
  rw [hfix]

end Transfer

/-! ## 3. The local condition: an element of the decomposition group moving `ζ` -/

section Local

/-- **If some element of `D_A ⊓ G_K` moves the primitive `p`-th root of unity `ζ`, then the
completion `K_𝔮` (at the prime `𝔮` of `K` below `A`) contains no primitive `p`-th root of unity.**

This is `zetaIndicator_adicCompletion_eq_one_iff_decomp_fixes_clean` at the base field `↥K`,
transported along `decomp k A ⊓ K.fixingSubgroup ≃* decomp ↥K A` (whose underlying function is the
identity). -/
theorem not_exists_primitiveRoot_localField_of_moves_zeta (p : ℕ) [Fact p.Prime] (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (hK : SSGRoute.IsFinPlace ↥K A)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p)
    (g : Ω ≃ₐ[k] Ω) (hgA : g ∈ SSGRoute.decomp k A) (hgK : g ∈ K.fixingSubgroup)
    (hgm : g ζ ≠ ζ) :
    ¬ ∃ z : Work.SSGRoute.PTembedding.localFieldOf ↥K A hK, IsPrimitiveRoot z p := by
  intro hcon
  haveI : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
  haveI : NumberField ↥K := NumberField.of_module_finite k ↥K
  have hiff := zetaIndicator_adicCompletion_eq_one_iff_decomp_fixes_clean p ↥K Ω A hK ζ hζ
  have h1 : NK.LocalInputs.zetaIndicator p
      ((Submission.NeukirchUchida.primeOf A hK).adicCompletion ↥K) = 1 :=
    (NK.LocalInputs.zetaIndicator_eq_one_iff p _).mpr hcon
  have h2 : ∀ σ ∈ SSGRoute.decomp ↥K A, σ • ζ = ζ := hiff.mp h1
  let g' : ↥(SSGRoute.decomp ↥K A) := decompEquiv_fok k Ω K A ⟨g, hgA, hgK⟩
  have hval : ((g' : ↥(SSGRoute.decomp ↥K A)) : Ω ≃ₐ[↥K] Ω) ζ = g ζ := rfl
  have hmem : ((g' : ↥(SSGRoute.decomp ↥K A)) : Ω ≃ₐ[↥K] Ω) ∈ SSGRoute.decomp ↥K A := g'.2
  have hfix : ((g' : ↥(SSGRoute.decomp ↥K A)) : Ω ≃ₐ[↥K] Ω) ζ = ζ := by
    have h := h2 _ hmem
    rwa [AlgEquiv.smul_def] at h
  exact hgm (hval ▸ hfix)

end Local

/-! ## 4. Chebotarev: a place whose decomposition group contains a prescribed Frobenius -/

section Place

/-- **The primes of `𝓞 K` above the rational prime `p`**, as a finite set of height-one
spectra. -/
noncomputable def primesAbove (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K] :
    Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) := by
  classical
  haveI : (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hpb : (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp [(Fact.out : p.Prime).ne_zero]
  have hprime : ∀ P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {((p : ℕ) : ℤ)})
      (NumberField.RingOfIntegers K), P.IsPrime ∧ P ≠ ⊥ := by
    intro P hP
    have hmem := (IsDedekindDomain.mem_primesOverFinset_iff hpb
      (NumberField.RingOfIntegers K)).mp hP
    exact ⟨hmem.1, Ideal.ne_bot_of_mem_primesOver hpb hmem⟩
  exact (IsDedekindDomain.primesOverFinset (Ideal.span {((p : ℕ) : ℤ)})
      (NumberField.RingOfIntegers K)).attach.image
    (fun P => ⟨P.1, (hprime P.1 P.2).1, (hprime P.1 P.2).2⟩)

/-- Membership in `primesAbove`: the primes of `𝓞 K` lying above `(p)`. -/
theorem mem_primesAbove (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]
    {q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)}
    (h : q.asIdeal.LiesOver (Ideal.span {((p : ℕ) : ℤ)})) : q ∈ primesAbove p K := by
  classical
  haveI : (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hpb : (Ideal.span {((p : ℕ) : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simp [(Fact.out : p.Prime).ne_zero]
  have hmem : q.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {((p : ℕ) : ℤ)})
      (NumberField.RingOfIntegers K) :=
    (IsDedekindDomain.mem_primesOverFinset_iff hpb (NumberField.RingOfIntegers K)).mpr
      ⟨q.isPrime, h⟩
  refine Finset.mem_image.mpr ⟨⟨q.asIdeal, hmem⟩, Finset.mem_attach _ _, ?_⟩
  exact IsDedekindDomain.HeightOneSpectrum.ext rfl

/-- **Place-level Chebotarev.**  For a finite Galois level `N/k` and a prescribed Frobenius element
`σ ∈ Gal(N/k)`, there is a finite place `A` of `Ω` over `k` avoiding a prescribed finite set `T'` of
primes of `k` (its trace on `k` is not the valuation ring of any prime of `T'`) and an element of
the decomposition group `D_A` restricting to `σ`. -/
theorem exists_place_of_frobenius_aux (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (N : IntermediateField k Ω) [FiniteDimensional k N] [IsGalois k N]
    (σ : ↥N ≃ₐ[k] ↥N)
    (T' : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))) :
    ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
      (∀ q ∈ T', A.comap (algebraMap k Ω) ≠
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k q) ∧
      ∃ τ ∈ SSGRoute.decomp k A, AlgEquiv.restrictNormalHom N τ = σ := by
  classical
  haveI : NumberField ↥N := NumberField.of_module_finite k ↥N
  obtain ⟨𝔭, h𝔭T, hunram, hFrob⟩ :=
    Work.SSGRoute.exists_frobAtPrime_avoid_unramified (K := k) (N := ↥N) σ T'
  obtain ⟨P, hPlies, hPfrob⟩ := hFrob
  obtain ⟨A, hAcomap, hAfin⟩ :=
    Work.SSGRoute.exists_isFinPlace_comap_eq (k := k) (Ω := Ω) N P
  -- the trace of `A` on `k` is the prime `𝔭`
  have hAp : A.comap (algebraMap k Ω) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k 𝔭 := by
    have hcomp : (A.comap (algebraMap ↥N Ω)).comap (algebraMap k ↥N) =
        A.comap (algebraMap k Ω) :=
      (ValuationSubring.comap_comap A (algebraMap ↥N Ω) (algebraMap k ↥N)).trans
        (congrArg (fun f => A.comap f) (IsScalarTower.algebraMap_eq k ↥N Ω)).symm
    have hunder : P.under (NumberField.RingOfIntegers k) = 𝔭 :=
      IsDedekindDomain.HeightOneSpectrum.ext (by
        rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
        exact hPlies.over.symm)
    have hlies : P.asIdeal.LiesOver (P.under (NumberField.RingOfIntegers k)).asIdeal := by
      rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
      exact ⟨rfl⟩
    rw [← hcomp, hAcomap,
      Commons.RingTheory.Valuation.comap_valuationSubringAtPrime (K := k) (L := ↥N)
        (P.under (NumberField.RingOfIntegers k)) P hlies, hunder]
  refine ⟨A, hAfin, ?_, ?_⟩
  · intro q hq h
    have hpq : 𝔭 = q :=
      Commons.RingTheory.Valuation.valuationSubringAtPrime_injective (K := k) (hAp.symm.trans h)
    exact h𝔭T (hpq ▸ hq)
  · -- the decomposition group of `A` maps onto `⟨σ⟩`
    have hbridge := Work.SSGRoute.FrobBelow.map_res_decomp_eq_stabilizer_valuationRing (k := k) (Ω := Ω)
      N A hAfin P hAcomap
    have hram : P.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := hunram P hPlies
    have hdec : Submission.NeukirchUchida.Local.decompositionSubgroup (K := k) P =
        Subgroup.zpowers σ :=
      NK.ChebotarevGeneral.decompositionSubgroup_eq_zpowers_of_isFrobAt (K := k) (N := ↥N)
        P σ hram hPfrob
    have hstab : MulAction.stabilizer (↥N ≃ₐ[k] ↥N)
        (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥N P) = Subgroup.zpowers σ := by
      rw [show MulAction.stabilizer (↥N ≃ₐ[k] ↥N)
            (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime ↥N P) =
          Submission.NeukirchUchida.Local.decompositionSubgroup (K := k) P from
        Subgroup.ext (fun x =>
          Submission.NeukirchUchida.Local.mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
            (K := k) P x)]
      exact hdec
    have hmem : σ ∈ (SSGRoute.decomp k A).map (SSGRoute.res k N) := by
      rw [hbridge, hstab]
      exact Subgroup.mem_zpowers σ
    obtain ⟨τ, hτ, hτres⟩ := Subgroup.mem_map.mp hmem
    exact ⟨τ, hτ, hτres⟩

end Place

/-! ## 5. The target -/

theorem exists_nonsplit_place_of_selmer_proj (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [DistribMulAction (K ≃ₐ[k] K) (ZMod p)] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) (ZMod p)]
    (T : Finset (ValuationSubring Ω)) (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T,
      (∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ B ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A) → A = B)
    (hζ : ¬ ∃ ζ : ↥K, IsPrimitiveRoot ζ p)
    {b : (Ω ≃ₐ[k] Ω) → ZMod p} (hb : b ∈ Work.SSGRoute.ZDataMup.selmerSpace (p := p) K T)
    (hbne : ∃ g ∈ K.fixingSubgroup, b g ≠ 0) :
    ∃ A : ValuationSubring Ω, SSGRoute.IsFinPlace k A ∧
      (∀ A' ∈ T, ¬ ∃ τ ∈ K.fixingSubgroup, ∀ x : Ω, x ∈ A ↔ (τ⁻¹ : Ω ≃ₐ[k] Ω) • x ∈ A') ∧
      (∃ g ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, b g ≠ 0) ∧
      Module.finrank (ZMod p)
        ↥(Work.SSGRoute.ZDataMup.lcCocycleImage (p := p) K
          (SSGRoute.decomp k A ⊓ K.fixingSubgroup)) = 1 := by
  classical
  haveI hGalΩ : IsGalois k Ω := IsAlgClosure.isGalois k Ω
  haveI hAlgClosedΩ : IsAlgClosed Ω := IsAlgClosure.isAlgClosed k
  haveI hCharZeroΩ : CharZero Ω :=
    charZero_of_injective_algebraMap (algebraMap k Ω).injective
  haveI hNeZeroΩp : NeZero (p : Ω) :=
    ⟨Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero⟩
  haveI hNeZero : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- ## the additive character of `G_K`
  have hbcoc : IsCocycleOn (res k K) K.fixingSubgroup b := hb.1
  have hblc : IsLocConstOn K.fixingSubgroup b := hb.2.1
  -- ## a primitive `p`-th root of unity, outside `K`
  obtain ⟨ζ, hζprim⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  have hζK : ζ ∉ K := by
    intro hmem
    refine hζ ⟨⟨ζ, hmem⟩, ?_⟩
    have hmap : IsPrimitiveRoot ((algebraMap ↥K Ω) ⟨ζ, hmem⟩) p := hζprim
    exact hmap.of_map_of_injective (algebraMap ↥K Ω).injective
  -- ## the fixed field `L` of the `b`-kernel
  have hHop : IsOpen ((bKer hbcoc : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    isOpen_bKer hbcoc hblc
  have hHcl : IsClosed ((bKer hbcoc : Subgroup (Ω ≃ₐ[k] Ω)) : Set (Ω ≃ₐ[k] Ω)) :=
    Subgroup.isClosed_of_isOpen _ hHop
  let L : IntermediateField k Ω := IntermediateField.fixedField (bKer hbcoc)
  have hLfix : L.fixingSubgroup = bKer hbcoc :=
    InfiniteGalois.fixingSubgroup_fixedField (k := k) (K := Ω) ⟨bKer hbcoc, hHcl⟩
  haveI hLfin : FiniteDimensional k L :=
    (InfiniteGalois.isOpen_iff_finite L).mp (by rw [hLfix]; exact hHop)
  have hKL : K ≤ L := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup K]
    exact IntermediateField.fixedField_le (bKer_le hbcoc)
  -- ## a finite Galois level over `k` containing `L`, `K` and `ζ`
  let kζ : IntermediateField k Ω := IntermediateField.adjoin k ({ζ} : Set Ω)
  have hζkζ : ζ ∈ kζ := IntermediateField.subset_adjoin k ({ζ} : Set Ω) (Set.mem_singleton ζ)
  haveI hkζfin : FiniteDimensional k kζ :=
    (Work.SSGRoute.adjoin_primitiveRoot_isGalois_coprime p k Ω ζ hζprim).2.1
  let M : IntermediateField k Ω := L ⊔ kζ
  haveI hMfin : FiniteDimensional k M := IntermediateField.finiteDimensional_sup L kζ
  haveI hMalg : Algebra.IsAlgebraic k ↥M := Algebra.IsAlgebraic.of_finite k ↥M
  have hLM : L ≤ M := le_sup_left
  have hkζM : kζ ≤ M := le_sup_right
  let N : IntermediateField k Ω := IntermediateField.normalClosure k ↥M Ω
  haveI hNfin : FiniteDimensional k N := inferInstance
  have hMN : M ≤ N := IntermediateField.le_normalClosure M
  haveI hNnorm : Normal k N :=
    (Algebra.IsAlgebraic.isNormalClosure_normalClosure (F := k) (K := ↥M) (L := Ω)
      (fun z => IsAlgClosed.splits _)).normal
  haveI hNgal : IsGalois k N := isGalois_iff.mpr ⟨Algebra.IsSeparable.of_integral k N, hNnorm⟩
  haveI hNN : NumberField ↥N := NumberField.of_module_finite k ↥N
  have hLN : L ≤ N := le_trans hLM hMN
  have hKN : K ≤ N := le_trans hKL hLN
  have hζN : ζ ∈ N := hMN (hkζM hζkζ)
  -- ## an element of `G_K` with non-zero `b`-value which moves `ζ`
  obtain ⟨τ, hτK, hτ0, hτζ⟩ :=
    exists_mem_fixingSubgroup_b_ne_zero_and_moves hbcoc hbne hζprim hζK
  -- ## the primes of `k` to avoid
  let T' : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) :=
    (T.attach.image (fun (A : {A : ValuationSubring Ω // A ∈ T}) =>
        Submission.NeukirchUchida.primeOf A.1
          (by simpa [SSGRoute.IsFinPlace] using hTfin A.1 A.2))) ∪
      (primesAbove p k)
  -- ## Chebotarev
  obtain ⟨A, hAfin, hAavoid, τ₀, hτ₀A, hτ₀res⟩ :=
    exists_place_of_frobenius_aux k Ω N (AlgEquiv.restrictNormalHom N τ) T'
  have hτ₀K : τ₀ ∈ K.fixingSubgroup :=
    mem_fixingSubgroup_of_restrictNormalHom_eq hKN hτK hτ₀res
  have hbτ₀ : b τ₀ ≠ 0 := by
    have heq : b τ₀ = b τ :=
      b_eq_of_restrictNormalHom_eq hbcoc hLN hLfix hτ₀K hτK hτ₀res
    rw [heq]
    exact hτ0
  have hτ₀ζ : τ₀ ζ ≠ ζ := by
    have h1 : τ₀ ζ = τ ζ := apply_eq_of_restrictNormalHom_eq hτ₀res hζN
    rw [h1]
    exact hτζ
  -- ## `A` is finite over `K`
  have hKfinA : SSGRoute.IsFinPlace ↥K A := by
    rw [SSGRoute.IsFinPlace] at hAfin ⊢
    intro htop
    refine hAfin ?_
    have hcomp : A.comap (algebraMap k Ω) =
        (A.comap (algebraMap ↥K Ω)).comap (algebraMap k ↥K) :=
      (ValuationSubring.comap_comap A (algebraMap ↥K Ω) (algebraMap k ↥K)).symm
    rw [hcomp, htop]
    ext x
    simp
  -- ## the local field of `↥K` at `A` has no primitive `p`-th root of unity
  have hlocal : ¬ ∃ z : Work.SSGRoute.PTembedding.localFieldOf ↥K A hKfinA,
      IsPrimitiveRoot z p :=
    not_exists_primitiveRoot_localField_of_moves_zeta p k Ω K A hAfin hKfinA ζ hζprim τ₀
      hτ₀A hτ₀K hτ₀ζ
  -- ## `A` does not lie above `p`
  have hApv : ¬ A.valuation ((p : ℚ) : Ω) < 1 := by
    intro hval
    have hval' : A.valuation ((p : ℕ) : Ω) < 1 := by
      have hcast : ((p : ℚ) : Ω) = ((p : ℕ) : Ω) := by simp
      rw [← hcast]
      exact hval
    have hlies := Work.SSGRoute.ZConstruction.primeBelow_val_lt_one_gen p (Fact.out : p.Prime)
      k Ω A hAfin hval'
    have hmem : Submission.NeukirchUchida.primeOf A hAfin ∈ T' :=
      Finset.mem_union.mpr (Or.inr (mem_primesAbove p k hlies))
    exact hAavoid _ hmem (Submission.NeukirchUchida.primeOf_spec A hAfin)
  refine ⟨A, hAfin, ?_, ?_, ?_⟩
  · -- ## `A` avoids the `G_K`-conjugates of `T`
    intro A' hA'T hconj
    obtain ⟨σ, hσK, hσ⟩ := hconj
    have hAeq : A = σ • A' := by
      apply ValuationSubring.ext
      intro x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact hσ x
    have hcomap : A.comap (algebraMap k Ω) = A'.comap (algebraMap k Ω) := by
      rw [hAeq]
      exact comap_smul_eq_of_mem_fixingSubgroup hσK
    have hA'ne : A'.comap (algebraMap k Ω) ≠ ⊤ := hTfin A' hA'T
    have hprime_mem : Submission.NeukirchUchida.primeOf A' hA'ne ∈ T' := by
      refine Finset.mem_union.mpr (Or.inl ?_)
      exact Finset.mem_image.mpr ⟨⟨A', hA'T⟩, Finset.mem_attach T ⟨A', hA'T⟩, rfl⟩
    have hspec' : A'.comap (algebraMap k Ω) =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime k
          (Submission.NeukirchUchida.primeOf A' hA'ne) :=
      Submission.NeukirchUchida.primeOf_spec A' hA'ne
    exact hAavoid _ hprime_mem (hcomap.trans hspec')
  · -- ## `b` does not vanish on `D_A ⊓ G_K`
    exact ⟨τ₀, ⟨hτ₀A, hτ₀K⟩, hbτ₀⟩
  · -- ## the local cocycle image is one-dimensional
    exact finrank_lcCocycleImage_eq_one_of_not_residueChar_proj p k Ω K A hAfin hApv
      hKfinA hlocal

end Work.SSGRoute.ZDataMup
