import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Connected.Separation
import Submission.Work.SSGRoute.finite_homs_local_inertia
import Submission.Work.SSGRoute.isClosed_inertiaSub_kernel
import Submission.Work.SSGRoute.isUnit_natCast_iff_not_dvd_resCharAt
import Submission.Work.SSGRoute.isUnit_natCast_of_not_dvd_resCharAt
import Submission.Work.SSGRoute.local_tate_duality_finite
import Submission.Work.SSGRoute.mem_localInertia_iff_isInertia

/-!
# Finiteness of the local `H¹` of the inertia subgroup (residue characteristic ≠ `p`)

The target `Work.SSGRoute.finite_H1loc_inertia`: for a number field `k`, an algebraic closure `Ω`,
a finite Galois `K/k`, a finite place `A` of `Ω` over `k` whose residue characteristic is different
from `p` and a finite `𝔽_p[Gal(K/k)]`-module `M`, the locally constant cohomology
`H1loc p k Ω K M (inertiaSub k Ω A)` of the inertia subgroup is **finite**.

## Route

Write `I = inertiaSub k Ω A ≤ G_k` for the inertia subgroup and `N = I ⊓ G_K` for its intersection
with `G_K = K.fixingSubgroup`.  Since `N` acts trivially on `M` while `I/N` embeds into the finite
group `Gal(K/k)`, a locally constant `1`-cocycle `f` on `I` is determined by

* its restriction `f|_N` (a homomorphism `N →* Multiplicative M`, because `N` acts trivially), and
* its values `f (s q)` on a fixed set-theoretic section `s` of `I → I/N ⊆ Gal(K/k)` (finitely many
  values),

because `x = s (res x) · ((s (res x))⁻¹ x)` for every `x ∈ I` and `f (g · u) = res g • f u + f g`.
Hence the locally constant cocycles inject into
`{χ : ↥N →* Multiplicative M // IsOpen χ.ker} × (↥(I.map (res k K)) → M)`, which is finite once the
first factor is; `H1loc` is a quotient of the locally constant cocycles, hence finite.

The finiteness of the first factor is the arithmetic input (the analogue of
`finite_openKernel_homs_decomp_kernel` with `N` in place of `D_A ⊓ G_K`): `N` is the inertia
subgroup of the completion of `K` at the prime below `A`, and the open-kernel homomorphisms of the
local inertia of a `𝔭`-adic field of residue characteristic `q ≠ p` into a finite `𝔽_p`-module are
finite (the wild inertia is pro-`q`, so it has no `𝔽_p`-characters, and the tame inertia is
pro-cyclic).
-/

open scoped Pointwise Topology
open Classical
open Filter

namespace Work.SSGRoute

noncomputable section

/-! ## The base change `D_A ⊓ G_K ≃* D_{A|K}`

Self-contained copies (under distinct names) of the base-change lemmas of
`Submission/Work/SSGRoute/finite_openKernel_homs_decomp_kernel.lean`, so that this file does not
depend on that module's names. -/

/-- **The group isomorphism `K.fixingSubgroup ≃* Gal(Ω/↥K)` is continuous** for the Krull
topologies (a self-contained copy of the version in
`finite_openKernel_homs_decomp_kernel.lean`). -/
lemma inertia_continuous_fixingSubgroupEquiv (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] :
    Continuous ((IntermediateField.fixingSubgroupEquiv K).toMonoidHom :
      ↥(K.fixingSubgroup) → (Ω ≃ₐ[↥K] Ω)) := by
  let f : ↥(K.fixingSubgroup) →* (Ω ≃ₐ[↥K] Ω) :=
    (IntermediateField.fixingSubgroupEquiv K).toMonoidHom
  refine continuous_of_continuousAt_one f ?_
  rw [ContinuousAt, f.map_one, Filter.tendsto_def]
  intro U hU
  rw [krullTopology_mem_nhds_one_iff ↥K Ω] at hU
  obtain ⟨N, hNfin, hNU⟩ := hU
  haveI : FiniteDimensional ↥K N := hNfin
  have hMfin : FiniteDimensional k (N.restrictScalars k) := FiniteDimensional.trans k ↥K ↥N
  have hopen : IsOpen ((N.restrictScalars k).fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen (N.restrictScalars k)
  have hmem : (Subtype.val ⁻¹' ((N.restrictScalars k).fixingSubgroup : Set (Ω ≃ₐ[k] Ω))) ∈
      𝓝 (1 : ↥(K.fixingSubgroup)) :=
    (hopen.preimage continuous_subtype_val).mem_nhds (by
      simp only [Set.mem_preimage]; rw [Subgroup.coe_one]; exact Subgroup.one_mem _)
  refine Filter.mem_of_superset hmem ?_
  intro x hx
  show (IntermediateField.fixingSubgroupEquiv K x) ∈ U
  apply hNU
  change (IntermediateField.fixingSubgroupEquiv K x) ∈ N.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have hyM : y ∈ (N.restrictScalars k : IntermediateField k Ω) := hy
  rw [IntermediateField.mem_restrictScalars] at hyM
  have hx' : (x : Ω ≃ₐ[k] Ω) ∈ (N.restrictScalars k).fixingSubgroup := hx
  rw [IntermediateField.mem_fixingSubgroup_iff] at hx'
  exact hx' y hyM

/-- **Transport of the decomposition group** across `K.fixingSubgroup ≃* Gal(Ω/↥K)` (a
self-contained copy). -/
lemma inertia_fixingSubgroupEquiv_mem_decomp (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) (A : ValuationSubring Ω) (σ : Ω ≃ₐ[k] Ω)
    (hσ : σ ∈ K.fixingSubgroup) :
    ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ ∈ SSGRoute.decomp ↥K A) ↔
      σ ∈ SSGRoute.decomp k A := by
  have hfun : ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ : Ω → Ω) = ⇑σ := rfl
  have hsmul : (IntermediateField.fixingSubgroupEquiv K ⟨σ, hσ⟩ : Ω ≃ₐ[↥K] Ω) • A =
      (σ : Ω ≃ₐ[k] Ω) • A := by
    apply ValuationSubring.ext
    intro x
    rw [ValuationSubring.mem_smul_pointwise_iff_exists,
      ValuationSubring.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, hx⟩
      exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, hfun]⟩
    · rintro ⟨s, hs, hx⟩
      exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, hfun]⟩
  rw [SSGRoute.decomp, SSGRoute.decomp, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff, hsmul]

/-- **The decomposition group of `A` over `k` intersected with `G_K` is the decomposition group of
`A` over `K`** (a self-contained copy). -/
noncomputable def inertia_decompEquiv (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) (A : ValuationSubring Ω) :
    ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) ≃* ↥(SSGRoute.decomp ↥K A) where
  toFun x := ⟨(IntermediateField.fixingSubgroupEquiv K) ⟨(x : Ω ≃ₐ[k] Ω), x.2.2⟩,
    (inertia_fixingSubgroupEquiv_mem_decomp k Ω K A (x : Ω ≃ₐ[k] Ω) x.2.2).mpr x.2.1⟩
  invFun y :=
    let z : ↥(K.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv K).symm y.1
    ⟨(z : Ω ≃ₐ[k] Ω),
      ⟨(inertia_fixingSubgroupEquiv_mem_decomp k Ω K A (z : Ω ≃ₐ[k] Ω) z.2).mp
        (by rw [show (⟨(z : Ω ≃ₐ[k] Ω), z.2⟩ : ↥(K.fixingSubgroup)) = z from rfl,
              MulEquiv.apply_symm_apply]; exact y.2), z.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    exact map_mul (IntermediateField.fixingSubgroupEquiv K) ⟨(x : Ω ≃ₐ[k] Ω), x.2.2⟩
      ⟨(y : Ω ≃ₐ[k] Ω), y.2.2⟩

/-- The base change `decomp k A ⊓ G_K ≃* decomp ↥K A` is a homeomorphism for the Krull
topologies (a self-contained copy). -/
lemma inertia_isHomeomorph_decompEquiv (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsAlgClosure k Ω]
    (A : ValuationSubring Ω) :
    IsHomeomorph
      (inertia_decompEquiv k Ω K A :
        ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) → ↥(SSGRoute.decomp ↥K A)) := by
  have hcf := inertia_continuous_fixingSubgroupEquiv k Ω K
  have hcont : Continuous
      (inertia_decompEquiv k Ω K A :
        ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) → ↥(SSGRoute.decomp ↥K A)) :=
    Continuous.subtype_mk
      (hcf.comp (Continuous.subtype_mk continuous_subtype_val (fun x => x.2.2)))
      (fun x => (inertia_fixingSubgroupEquiv_mem_decomp k Ω K A _ x.2.2).mpr x.2.1)
  haveI : CompactSpace ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) := by
    have hclosed : IsClosed
        ((SSGRoute.decomp k A ⊓ K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) :
          Set (Ω ≃ₐ[k] Ω)) :=
      (Commons.FieldTheory.Galois.isClosed_stabilizer_valuationSubring (K := k) (K' := Ω) A).inter
        (IntermediateField.fixingSubgroup_isClosed K)
    haveI : CompactSpace (Ω ≃ₐ[k] Ω) := inferInstance
    exact isCompact_iff_compactSpace.mp hclosed.isCompact
  haveI : T2Space ↥(SSGRoute.decomp ↥K A) := inferInstance
  exact (isHomeomorph_iff_continuous_bijective).mpr
    ⟨hcont, (inertia_decompEquiv k Ω K A).bijective⟩

/-! ## Base change of the inertia subgroup -/

/-- **Base change of the inertia subgroup.**  Under the isomorphism
`K.fixingSubgroup ≃* Gal(Ω/↥K)` the inertia subgroup of a place `A` over `k` is the inertia
subgroup of `A` over `K`: an element of `K.fixingSubgroup` acts trivially on the residue field of
`A` over `k` if and only if the corresponding `↥K`-automorphism does. -/
lemma fixingSubgroupEquiv_mem_inertiaSub (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] (K : IntermediateField k Ω) (A : ValuationSubring Ω) (σ : Ω ≃ₐ[k] Ω)
    (hσ : σ ∈ K.fixingSubgroup) :
    ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ ∈ inertiaSub ↥K Ω A) ↔
      σ ∈ inertiaSub k Ω A := by
  have hfun : ((IntermediateField.fixingSubgroupEquiv K) ⟨σ, hσ⟩ : Ω → Ω) = ⇑σ := rfl
  constructor
  · rintro ⟨hD, hv⟩
    exact ⟨(inertia_fixingSubgroupEquiv_mem_decomp k Ω K A σ hσ).mp hD,
      fun x hx => by rw [← hfun]; exact hv x hx⟩
  · rintro ⟨hD, hv⟩
    exact ⟨(inertia_fixingSubgroupEquiv_mem_decomp k Ω K A σ hσ).mpr hD,
      fun x hx => by rw [hfun]; exact hv x hx⟩

/-! ## Transfer of finiteness along a continuous injective homomorphism -/

/-- **Finiteness of open-kernel homomorphisms transfers along a continuous injective
homomorphism of a compact group onto a closed subgroup.**

If `φ : G →* H` is a continuous injective homomorphism whose range is the closed subgroup
`K ≤ H`, then `{χ : G →* M // IsOpen χ.ker}` is finite as soon as
`{ψ : ↥K →* M // IsOpen ψ.ker}` is: the map `ψ ↦ ψ ∘ φ` is surjective, because a homomorphism
`χ : G →* M` with open kernel is the composite of `φ` with the homomorphism
`ψ (φ g) = χ g` on the range, whose kernel is the image of `χ.ker` under the homeomorphism
`G ≃ ↥K`. -/
lemma finite_homs_of_continuous_injective
    {G H M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [Group M]
    (φ : G →* H) (hcont : Continuous (φ : G → H)) (hinj : Function.Injective (φ : G → H))
    (K : Subgroup H) (hK : IsClosed (K : Set H)) (hrange : Set.range (φ : G → H) = (K : Set H))
    (hfin : Finite {ψ : ↥K →* M // IsOpen (ψ.ker : Set ↥K)}) :
    Finite {χ : G →* M // IsOpen (χ.ker : Set G)} := by
  classical
  haveI := hfin
  -- the induced map `G →* ↥K` and its inverse
  have hmem : ∀ g : G, (φ g) ∈ (K : Set H) := by
    intro g
    rw [← hrange]
    exact Set.mem_range_self g
  let Φ : G →* ↥K :=
    { toFun := fun g => ⟨φ g, hmem g⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun a b => Subtype.ext (map_mul φ a b) }
  have hΦcont : Continuous (Φ : G → ↥K) := Continuous.subtype_mk hcont hmem
  have hΦbij : Function.Bijective (Φ : G → ↥K) := by
    refine ⟨fun a b hab => hinj (Subtype.ext_iff.mp hab), fun k => ?_⟩
    have hk : (k : H) ∈ Set.range (φ : G → H) := by
      rw [hrange]
      exact k.2
    obtain ⟨g, hg⟩ := hk
    exact ⟨g, Subtype.ext hg⟩
  have hΦhomeo : IsHomeomorph (Φ : G → ↥K) :=
    (isHomeomorph_iff_continuous_bijective).mpr ⟨hΦcont, hΦbij⟩
  let e : G ≃* ↥K :=
    { toFun := Φ
      invFun := Function.invFun Φ
      left_inv := Function.leftInverse_invFun hΦbij.1
      right_inv := Function.rightInverse_invFun hΦbij.2
      map_mul' := map_mul Φ }
  have he : ⇑e = ⇑Φ := rfl
  -- the map on homomorphisms
  let Ψ : {ψ : ↥K →* M // IsOpen (ψ.ker : Set ↥K)} → {χ : G →* M // IsOpen (χ.ker : Set G)} :=
    fun ψ => ⟨ψ.1.comp Φ, by
      have hker : (((ψ.1.comp Φ).ker : Set G)) = Φ ⁻¹' (ψ.1.ker : Set ↥K) := rfl
      rw [hker]
      exact hΦcont.isOpen_preimage _ ψ.2⟩
  refine Finite.of_surjective Ψ ?_
  intro χ
  refine ⟨⟨χ.1.comp e.symm.toMonoidHom, ?_⟩, ?_⟩
  · have hker : (((χ.1.comp e.symm.toMonoidHom).ker : Set ↥K)) = e '' (χ.1.ker : Set G) := by
      ext k
      constructor
      · intro hk
        exact ⟨e.symm k, hk, e.apply_symm_apply k⟩
      · rintro ⟨g, hg, rfl⟩
        simpa using hg
    rw [hker]
    exact hΦhomeo.isOpenMap _ χ.2
  · apply Subtype.ext
    ext g
    change χ.1 (e.symm (e g)) = χ.1 g
    rw [MulEquiv.symm_apply_apply]

/-! ## The canonical action of the inertia subgroup -/

/-- **The canonical action of the inertia subgroup** `I_A ≤ G_k` on a `Gal(K/k)`-module `M`,
through the restriction `res k K : G_k →* Gal(K/k)`. -/
@[instance_reducible] def inertiaDistribMulAction (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (M : Type) [AddCommGroup M]
    [DistribMulAction (K ≃ₐ[k] K) M] (A : ValuationSubring Ω) :
    DistribMulAction ↥(inertiaSub k Ω A) M where
  smul h m := SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m
  one_smul m := by
    show SSGRoute.res k K (((1 : ↥(inertiaSub k Ω A)) : Ω ≃ₐ[k] Ω)) • m = m
    rw [show ((1 : ↥(inertiaSub k Ω A)) : Ω ≃ₐ[k] Ω) = 1 from rfl, map_one, one_smul]
  mul_smul h1 h2 m := by
    show SSGRoute.res k K (((h1 * h2 : ↥(inertiaSub k Ω A)) : Ω ≃ₐ[k] Ω)) • m
      = SSGRoute.res k K ((h1 : Ω ≃ₐ[k] Ω)) • (SSGRoute.res k K ((h2 : Ω ≃ₐ[k] Ω)) • m)
    rw [show ((h1 * h2 : ↥(inertiaSub k Ω A)) : Ω ≃ₐ[k] Ω)
        = (h1 : Ω ≃ₐ[k] Ω) * (h2 : Ω ≃ₐ[k] Ω) from rfl, map_mul, mul_smul]
  smul_zero h := smul_zero _
  smul_add h m n := smul_add _ _ _

/-- The canonical action of the inertia subgroup is the restriction action. -/
theorem inertia_smul_eq_res (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (K : IntermediateField k Ω) [Normal k K] (M : Type) [AddCommGroup M]
    [DistribMulAction (K ≃ₐ[k] K) M] (A : ValuationSubring Ω)
    (h : ↥(inertiaSub k Ω A)) (m : M) :
    @SMul.smul ↥(inertiaSub k Ω A) M (inertiaDistribMulAction k Ω K M A).toSMul h m
      = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m := rfl

/-! ## The cocycle reduction -/

/-- **Stage 2: the locally constant `1`-cocycles of the inertia subgroup form a finite set** as
soon as the open-kernel homomorphisms of the kernel `N = I ⊓ G_K` into `M` do.

A cocycle is determined by its restriction to `N` and its values on the section `s` of the
restriction `I → I/N`. -/
theorem finite_Z1_inertia_of_finite_homs
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type) [AddCommGroup M]
    [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    [dma : DistribMulAction ↥(inertiaSub k Ω A) M]
    (hcompat : ∀ (g : ↥(inertiaSub k Ω A)) (m : M),
      g • m = SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) • m)
    (hcore : Finite {χ : ↥(inertiaSub k Ω A ⊓ K.fixingSubgroup) →* Multiplicative M //
      IsOpen (χ.ker : Set ↥(inertiaSub k Ω A ⊓ K.fixingSubgroup))}) :
    Finite ↥(Work.AbsoluteKummer.Z1 ↥(inertiaSub k Ω A) M) := by
  let I : Subgroup (Ω ≃ₐ[k] Ω) := inertiaSub k Ω A
  -- the section of the restriction map `I → I/N`
  have hQmem : ∀ q ∈ I.map (SSGRoute.res k K),
      ∃ σ : ↥I, SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) = q := by
    intro q hq
    obtain ⟨σ, hσ, hσq⟩ := Subgroup.mem_map.mp hq
    exact ⟨⟨σ, hσ⟩, hσq⟩
  let s : (K ≃ₐ[k] K) → ↥I := fun q =>
    if h : q ∈ I.map (SSGRoute.res k K) then Classical.choose (hQmem q h) else 1
  have hs : ∀ q (h : q ∈ I.map (SSGRoute.res k K)),
      SSGRoute.res k K ((s q : ↥I) : Ω ≃ₐ[k] Ω) = q := by
    intro q h
    simp only [s]
    rw [dif_pos h]
    exact Classical.choose_spec (hQmem q h)
  -- the inclusion of the kernel `N = I ⊓ G_K` into `I`
  have hmemI : ∀ u : ↥(I ⊓ K.fixingSubgroup), (u : Ω ≃ₐ[k] Ω) ∈ I :=
    fun u => (Subgroup.mem_inf.mp u.2).1
  have hmemK : ∀ u : ↥(I ⊓ K.fixingSubgroup), (u : Ω ≃ₐ[k] Ω) ∈ K.fixingSubgroup :=
    fun u => (Subgroup.mem_inf.mp u.2).2
  -- `f 1 = 0` for a crossed homomorphism
  have hzero : ∀ f : ↥(Work.AbsoluteKummer.Z1 ↥I M), f.1 (1 : ↥I) = 0 := by
    intro f
    have h := (Work.AbsoluteKummer.mem_Z1_iff (G := ↥I) (M := M) f.1).mp f.2 |>.1
    have h11 : f.1 (1 : ↥I) = f.1 (1 : ↥I) + f.1 (1 : ↥I) := by simpa using h 1 1
    have h3 : f.1 (1 : ↥I) + f.1 (1 : ↥I) = f.1 (1 : ↥I) + 0 := by
      rw [add_zero]; exact h11.symm
    exact add_left_cancel h3
  -- the kernel acts trivially on `M` (it lies in `G_K = ker (res k K)`)
  have hres1 : ∀ u : ↥(I ⊓ K.fixingSubgroup), SSGRoute.res k K (u : Ω ≃ₐ[k] Ω) = 1 := by
    intro u
    have hker : (u : Ω ≃ₐ[k] Ω) ∈ (SSGRoute.res k K).ker := by
      rw [IntermediateField.restrictNormalHom_ker (E := K)]
      exact hmemK u
    exact MonoidHom.mem_ker.mp hker
  -- the homomorphism induced on the kernel
  let χfun : ↥(Work.AbsoluteKummer.Z1 ↥I M) →
      (↥(I ⊓ K.fixingSubgroup) →* Multiplicative M) := fun f =>
    { toFun := fun u => Multiplicative.ofAdd (f.1 (Subgroup.inclusion
        (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u))
      map_one' := by
        show Multiplicative.ofAdd (f.1 (Subgroup.inclusion
          (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) 1)) = 1
        rw [map_one, hzero f]
        rfl
      map_mul' := by
        intro u v
        have hch := (Work.AbsoluteKummer.mem_Z1_iff (G := ↥I) (M := M) f.1).mp f.2 |>.1
        have h1 : (Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) (u * v) : ↥I)
            = Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u *
              Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) v := map_mul _ u v
        have h2 := hch (Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u)
          (Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) v)
        show Multiplicative.ofAdd (f.1 (Subgroup.inclusion
            (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) (u * v)))
          = Multiplicative.ofAdd (f.1 (Subgroup.inclusion
              (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u))
            * Multiplicative.ofAdd (f.1 (Subgroup.inclusion
              (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) v))
        rw [h1, h2,
          hcompat (Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u)
            (f.1 (Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) v))]
        rw [show SSGRoute.res k K (((Subgroup.inclusion
              (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u : ↥I)) : Ω ≃ₐ[k] Ω) = 1 from hres1 u,
          one_smul, add_comm]
        rfl }
  -- the kernel of that homomorphism is open
  have hker_open : ∀ f : ↥(Work.AbsoluteKummer.Z1 ↥I M),
      IsOpen ((χfun f).ker : Set ↥(I ⊓ K.fixingSubgroup)) := by
    intro f
    have hlc := (Work.AbsoluteKummer.mem_Z1_iff (G := ↥I) (M := M) f.1).mp f.2 |>.2
    obtain ⟨V, hVopen, h1V, hV⟩ := hlc (1 : ↥I)
    refine Subgroup.isOpen_of_mem_nhds (χfun f).ker (g := 1) ?_
    have hopen : IsOpen ((fun u : ↥(I ⊓ K.fixingSubgroup) =>
        (Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u : ↥I)) ⁻¹' V) :=
      hVopen.preimage (continuous_subtype_val.subtype_mk _)
    have h1mem : (1 : ↥(I ⊓ K.fixingSubgroup)) ∈
        (fun u : ↥(I ⊓ K.fixingSubgroup) =>
          (Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u : ↥I)) ⁻¹' V := by
      simp only [Set.mem_preimage]
      rw [map_one]
      exact h1V
    refine Filter.mem_of_superset (hopen.mem_nhds h1mem) ?_
    intro u hu
    show Multiplicative.ofAdd (f.1 (Subgroup.inclusion
      (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u)) = 1
    rw [hV _ hu, hzero f]
    rfl
  -- the key injectivity statement
  have hkey : ∀ f g : ↥(Work.AbsoluteKummer.Z1 ↥I M), χfun f = χfun g →
      (∀ q : K ≃ₐ[k] K, f.1 (s q) = g.1 (s q)) → f = g := by
    intro f g hχ hval
    apply Subtype.ext
    funext x
    have hχu : ∀ u : ↥(I ⊓ K.fixingSubgroup),
        f.1 (Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u)
          = g.1 (Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u) := by
      intro u
      have h' : Multiplicative.ofAdd (f.1 (Subgroup.inclusion
            (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u)) =
          Multiplicative.ofAdd (g.1 (Subgroup.inclusion
            (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u)) :=
        congrFun (congrArg DFunLike.coe hχ) u
      exact Multiplicative.ofAdd.injective h'
    have hq : SSGRoute.res k K (x : Ω ≃ₐ[k] Ω) ∈ I.map (SSGRoute.res k K) :=
      ⟨(x : Ω ≃ₐ[k] Ω), x.2, rfl⟩
    have hresu : SSGRoute.res k K ((((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)))⁻¹ * x : ↥I) :
        Ω ≃ₐ[k] Ω)) = 1 := by
      rw [show ((((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)))⁻¹ * x : ↥I) : Ω ≃ₐ[k] Ω))
          = ((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)) : ↥I) : Ω ≃ₐ[k] Ω)⁻¹ *
            (x : Ω ≃ₐ[k] Ω) from rfl,
        map_mul, map_inv, hs _ hq, inv_mul_cancel]
    have hmK : ((((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)))⁻¹ * x : ↥I) : Ω ≃ₐ[k] Ω))
        ∈ K.fixingSubgroup := by
      have hle : (SSGRoute.res k K).ker ≤ (K.fixingSubgroup : Subgroup (Ω ≃ₐ[k] Ω)) := by
        rw [IntermediateField.restrictNormalHom_ker (E := K)]
      exact hle (MonoidHom.mem_ker.mpr hresu)
    let u : ↥(I ⊓ K.fixingSubgroup) :=
      ⟨(((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)))⁻¹ * x : ↥I) : Ω ≃ₐ[k] Ω),
        Subgroup.mem_inf.mpr ⟨(((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)))⁻¹ * x : ↥I)).2, hmK⟩⟩
    have hxu : (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))) *
        (Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u) = x := by
      rw [show (Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u : ↥I)
        = (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)))⁻¹ * x from Subtype.ext rfl]
      group
    have hf := (Work.AbsoluteKummer.mem_Z1_iff (G := ↥I) (M := M) f.1).mp f.2 |>.1
    have hg := (Work.AbsoluteKummer.mem_Z1_iff (G := ↥I) (M := M) g.1).mp g.2 |>.1
    calc f.1 x = f.1 ((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))) *
          (Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u)) := by rw [hxu]
      _ = @SMul.smul ↥I M dma.toSMul (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)))
            (f.1 (Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u)) +
          f.1 (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))) := hf _ _
      _ = @SMul.smul ↥I M dma.toSMul (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω)))
            (g.1 (Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u)) +
          g.1 (s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))) := by rw [hχu u, hval _]
      _ = g.1 ((s (SSGRoute.res k K (x : Ω ≃ₐ[k] Ω))) *
          (Subgroup.inclusion (inf_le_left : I ⊓ K.fixingSubgroup ≤ I) u)) := (hg _ _).symm
      _ = g.1 x := by rw [hxu]
  -- the injection into a finite target
  haveI := hcore
  haveI : Finite (K ≃ₐ[k] K) := inferInstance
  haveI : Finite ↥(I.map (SSGRoute.res k K)) := inferInstance
  haveI : Finite ((K ≃ₐ[k] K) → M) := inferInstance
  refine Finite.of_injective
    (fun f : ↥(Work.AbsoluteKummer.Z1 ↥I M) =>
      ((⟨χfun f, hker_open f⟩ :
          {χ : ↥(I ⊓ K.fixingSubgroup) →* Multiplicative M //
            IsOpen (χ.ker : Set ↥(I ⊓ K.fixingSubgroup))}),
        (fun q : K ≃ₐ[k] K => f.1 (s q)))) ?_
  intro f g hfg
  refine hkey f g ?_ ?_
  · exact congrArg (fun z => (z.1 : ↥(I ⊓ K.fixingSubgroup) →* Multiplicative M)) hfg
  · intro q
    exact congrFun (congrArg (fun z => z.2) hfg) q

/-- **The local `H¹` of the inertia subgroup is finite**, given the finiteness of the
open-kernel homomorphisms of the kernel `N = I ⊓ G_K`. -/
theorem finite_H1loc_inertia_of_finite_homs
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A) (M : Type) [AddCommGroup M]
    [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (hcore : Finite {χ : ↥(inertiaSub k Ω A ⊓ K.fixingSubgroup) →* Multiplicative M //
      IsOpen (χ.ker : Set ↥(inertiaSub k Ω A ⊓ K.fixingSubgroup))}) :
    Finite (H1loc p k Ω K M (inertiaSub k Ω A)) := by
  letI : SMul ↥(inertiaSub k Ω A) M := (inertiaDistribMulAction k Ω K M A).toSMul
  letI : DistribMulAction ↥(inertiaSub k Ω A) M := inertiaDistribMulAction k Ω K M A
  haveI : Finite ↥(Work.AbsoluteKummer.Z1 ↥(inertiaSub k Ω A) M) :=
    finite_Z1_inertia_of_finite_homs p k Ω K A hA M
      (fun g m => inertia_smul_eq_res k Ω K M A g m) hcore
  have hH1 : Finite (Work.AbsoluteKummer.H1 ↥(inertiaSub k Ω A) M) :=
    Finite.of_surjective (Work.AbsoluteKummer.H1π ↥(inertiaSub k Ω A) M)
      (QuotientAddGroup.mk'_surjective _)
  exact Finite.of_injective
    (H1locEquivH1 p k Ω K M (inertiaSub k Ω A) (fun h m => inertia_smul_eq_res k Ω K M A h m))
    (H1locEquivH1 p k Ω K M (inertiaSub k Ω A)
      (fun h m => inertia_smul_eq_res k Ω K M A h m)).injective

/-- **The arithmetic input**: the open-kernel homomorphisms of the kernel `N = I ⊓ G_K` of the
inertia subgroup into a finite `𝔽_p`-module are finite, when `p` is a unit at the place `A`
(i.e. the residue characteristic is different from `p`).

`N` is the inertia subgroup of the completion of `K` at the prime below `A`
(`NK.Mine.localGaloisEquiv`, `IntermediateField.fixingSubgroupEquiv`), and the continuous
homomorphisms of the inertia subgroup of a `𝔭`-adic field of residue characteristic `q ≠ p` into a
finite `𝔽_p`-module are finite: the wild inertia is pro-`q`, hence has no `𝔽_p`-characters, and the
tame inertia is pro-cyclic. -/
theorem finite_homs_inertia_kernel
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1) (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [Finite M] :
    Finite {χ : ↥(inertiaSub k Ω A ⊓ K.fixingSubgroup) →* Multiplicative M //
      IsOpen (χ.ker : Set ↥(inertiaSub k Ω A ⊓ K.fixingSubgroup))} := by
  classical
  -- `↥K` is a number field and `Ω` a separable closure of it
  haveI hNFK : NumberField ↥K :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) K
  have hsepK : IsSepClosure ↥K Ω := by
    have : IsAlgClosure ↥K Ω := ⟨IsAlgClosure.isAlgClosed k, inferInstance⟩
    exact IsSepClosure.of_isAlgClosure_of_perfectField ↥K Ω
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
    inertia_decompEquiv k Ω K A
  have he₁ : IsHomeomorph
      (e₁ : ↥(SSGRoute.decomp k A ⊓ K.fixingSubgroup) → ↥(SSGRoute.decomp ↥K A)) :=
    inertia_isHomeomorph_decompEquiv k Ω K A
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
    have hmain := mem_localInertia_iff_isInertia ⟨A, hAK⟩
      (fun n hn => isUnit_natCast_of_not_dvd_resCharAt ↥K Ω A hAK n hn) w
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

/-- **Finiteness of the local `H¹` of the inertia subgroup (residue characteristic ≠ p).**

`I = Work.SSGRoute.inertiaSub k Ω A` is the inertia subgroup of a finite place `A` of `Ω` over a
number field `k` (`Submission/Work/SSGRoute/InertiaDefs.lean`), and `h` says that `p` is a unit of
`A`, i.e. the residue characteristic of `A` is different from `p`.  Then for every finite
`𝔽_p[Gal(K/k)]`-module `M` the locally constant `H¹` of `I` with coefficients `M` is finite.

The hypothesis `h` is essential: for a place of residue characteristic `p` the wild inertia is a
pro-`p` group and `Hom_cont(I, ℤ/p)` can be infinite, so the statement would be false without it. -/
theorem finite_H1loc_inertia
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (h : ¬ A.valuation ((p : ℚ) : Ω) < 1) :
    ∀ (M : Type) [AddCommGroup M] [Module (ZMod p) M]
      [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M],
      Finite (Work.SSGRoute.H1loc p k Ω K M (inertiaSub k Ω A)) := by
  intro M _ _ _ _ _
  exact finite_H1loc_inertia_of_finite_homs p k Ω K A hA M
    (finite_homs_inertia_kernel p k Ω K A hA h M)

end

end Work.SSGRoute
