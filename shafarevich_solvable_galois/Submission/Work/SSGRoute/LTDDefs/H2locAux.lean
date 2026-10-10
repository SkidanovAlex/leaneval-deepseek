import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Auxiliary facts for the `H²`-model bridge (`H2locEquivH2`)

`LTDDefs/Basic.lean` defines the local cohomology `H2loc` of a subgroup `H ≤ G_k = Ω ≃ₐ[k] Ω`
through functions on the *whole* group `G_k` satisfying the `2`-cocycle and local-constancy
conditions only on `H`, and `LTDDefs/H1loc_iso_H1cont.lean` identifies `H1loc` with the
workspace's continuous-cochain model `Work.AbsoluteKummer.H1 ↥H M`.  The `H²` analogue
(`LTDDefs/H2locEquivH2.lean`) needs the same two ingredients:

* the restriction of a locally constant `2`-cocycle on `H` (a function on `G_k × G_k`) to
  `H × H` (module `LTDDefs/H2locRestrict.lean`);
* the extension by `0` off `H` of a continuous `2`-cocycle of `H` (module
  `LTDDefs/H2locExtend.lean`).

The `H¹` version of the second map used the `1`-cocyle identity to replace global local
constancy by local constancy at `1`; for `2`-cocycles there is no such shortcut, and the honest
input is the following fact, proved here: **on a compact totally disconnected topological group
a locally constant function is uniformly locally constant**, i.e. right invariant by an open
subgroup, uniformly in the base point.  (This is the standard fact that in a profinite group the
open subgroups form a neighbourhood basis of `1`.)  Specialised to `↥H` (a closed subgroup of the
profinite group `G_k`) and converted through the Krull topology of `G_k`, this is exactly what
`IsLocConst2On`/`IsLocConstOn` demand.

## Main results

* `Work.SSGRoute.exists_openSubgroup_forall_mul_eq` — uniform local constancy (one variable);
* `Work.SSGRoute.exists_openSubgroup_pair_forall_mul_eq` — the two-variable form;
* `Work.SSGRoute.exists_openSubgroup_inter_subset_of_isOpen` — an open subgroup of `↥H`
  contains the trace of an open subgroup of `G_k`;
* `Work.SSGRoute.restrictFun2`, `Work.SSGRoute.extendFun2` — the raw restriction/extension
  operations on `2`-cochains.
-/

open scoped Pointwise
open Classical

namespace Work.SSGRoute

noncomputable section

/-! ## Uniform local constancy on a compact totally disconnected group -/

/-- **Uniform local constancy.**  A locally constant function on a compact totally disconnected
topological group is right invariant by an open subgroup, uniformly in the base point. -/
theorem exists_openSubgroup_forall_mul_eq {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {M : Type*} {f : G → M}
    (hf : Work.AbsoluteKummer.IsLocallyConstant f) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧ ∀ x : G, ∀ v ∈ V, f (x * v) = f x := by
  have key : ∀ x : G, ∃ V : Subgroup G, IsOpen (V : Set G) ∧ ∀ v ∈ V, f (x * v) = f x := by
    intro x
    obtain ⟨A, hAo, hxA, hA⟩ := hf x
    have hUo : IsOpen {g : G | x * g ∈ A} := hAo.preimage (continuous_const.mul continuous_id)
    have h1 : (1 : G) ∈ {g : G | x * g ∈ A} := by simpa using hxA
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUo h1
    exact ⟨N, N.isOpen, fun v hv => hA (x * v) (hN hv)⟩
  choose V hVo hV using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : G => {z : G | x⁻¹ * z ∈ V x})
    (fun x => (hVo x).preimage (continuous_const.mul continuous_id))
    (by intro y _; exact Set.mem_iUnion.mpr ⟨y, by simpa using (V y).one_mem⟩)
  refine ⟨⨅ x ∈ t, V x, ?_, ?_⟩
  · simp only [Subgroup.coe_iInf]
    exact isOpen_biInter_finset (fun i _ => hVo i)
  · intro x v hv
    have hx : x ∈ ⋃ i ∈ t, {z : G | i⁻¹ * z ∈ V i} := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hx
    obtain ⟨y, hyt, hyx⟩ := hx
    have hv' : v ∈ V y := by
      have h := hv
      simp only [Subgroup.mem_iInf] at h
      exact h y hyt
    have h1 : f x = f y := by
      have h := hV y (y⁻¹ * x) hyx
      rwa [← mul_assoc, mul_inv_cancel, one_mul] at h
    have h2 : f (x * v) = f y := by
      have hm : y⁻¹ * (x * v) ∈ V y := by
        have h := (V y).mul_mem hyx hv'
        rwa [mul_assoc] at h
      have h := hV y (y⁻¹ * (x * v)) hm
      rwa [← mul_assoc, mul_inv_cancel, one_mul] at h
    rw [h2, ← h1]

/-- The two-variable form of uniform local constancy, obtained from the one-variable form by
applying it to the product group `G × G`. -/
theorem exists_openSubgroup_pair_forall_mul_eq {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {M : Type*}
    {f : G → G → M} (hf : Work.AbsoluteKummer.IsLocallyConstant (fun p : G × G => f p.1 p.2)) :
    ∃ V : Subgroup G, IsOpen (V : Set G) ∧
      ∀ x y : G, ∀ u ∈ V, ∀ v ∈ V, f (x * u) (y * v) = f x y := by
  obtain ⟨W, hWo, hW⟩ :=
    exists_openSubgroup_forall_mul_eq (G := G × G) (f := fun p : G × G => f p.1 p.2) hf
  refine ⟨(W.comap (MonoidHom.inl G G)) ⊓ (W.comap (MonoidHom.inr G G)), ?_, ?_⟩
  · rw [Subgroup.coe_inf]
    refine IsOpen.inter ?_ ?_
    · rw [Subgroup.coe_comap]
      exact hWo.preimage (continuous_id.prodMk continuous_const)
    · rw [Subgroup.coe_comap]
      exact hWo.preimage (continuous_const.prodMk continuous_id)
  · intro x y u hu v hv
    have huW : (u, (1 : G)) ∈ W := by
      have h := (Subgroup.mem_inf.mp hu).1
      rwa [Subgroup.mem_comap] at h
    have hvW : ((1 : G), v) ∈ W := by
      have h := (Subgroup.mem_inf.mp hv).2
      rwa [Subgroup.mem_comap] at h
    have huv : (u, v) ∈ W := by
      have h := W.mul_mem huW hvW
      simpa using h
    have h := hW (x, y) (u, v) huv
    simpa using h

/-! ## Traces of open subgroups of the Krull group -/

/-- Every open subgroup of a closed subgroup `↥H ⊆ G_k` contains the trace of an open subgroup
of `G_k`.  (In fact one may take the fixing subgroup of a finite subextension.) -/
theorem exists_openSubgroup_inter_subset_of_isOpen (k Ω : Type) [Field k] [Field Ω] [Algebra k Ω]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) (V : Subgroup ↥H) (hV : IsOpen (V : Set ↥H)) :
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ u : Ω ≃ₐ[k] Ω, u ∈ U → ∀ (hu : u ∈ H), (⟨u, hu⟩ : ↥H) ∈ V := by
  obtain ⟨W, hWo, hWV⟩ := isOpen_induced_iff.mp hV
  have hmem : ∀ x : ↥H, (x ∈ V ↔ (x : Ω ≃ₐ[k] Ω) ∈ W) := fun x => by
    have h : x ∈ Subtype.val ⁻¹' W ↔ (x : Ω ≃ₐ[k] Ω) ∈ W := Iff.rfl
    rwa [hWV] at h
  have h1W : (1 : Ω ≃ₐ[k] Ω) ∈ W :=
    (hmem (⟨1, H.one_mem⟩ : ↥H)).mp V.one_mem
  obtain ⟨E, _, hEsub⟩ := (krullTopology_mem_nhds_one_iff k Ω W).mp (hWo.mem_nhds h1W)
  refine ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, ?_⟩
  intro u hu huH
  exact (hmem (⟨u, huH⟩ : ↥H)).mpr (hEsub hu)

/-! ## Restriction and extension of `2`-cochains -/

/-- Restriction of a `2`-cochain on `Γ = Ω ≃ₐ[k] Ω` to a subgroup `H`, as a function on the
product `↥H × ↥H` (the shape used by `Work.AbsoluteKummer.Z2`). -/
def restrictFun2 {Γ : Type*} [Group Γ] {M : Type*} (H : Subgroup Γ) (c : Γ → Γ → M) :
    ↥H × ↥H → M :=
  fun p => c p.1 p.2

/-- Extension by `0` off `H` of a `2`-cochain on `H`: the value at `(g, h)` is the value of `c`
at `(g, h)` when `g, h ∈ H`, and `0` otherwise. -/
def extendFun2 {Γ : Type*} [Group Γ] {M : Type*} [Zero M] (H : Subgroup Γ)
    (c : ↥H × ↥H → M) : Γ → Γ → M :=
  fun g h => if hg : g ∈ H then (if hh : h ∈ H then c (⟨g, hg⟩, ⟨h, hh⟩) else 0) else 0

@[simp] lemma restrictFun2_apply {Γ : Type*} [Group Γ] {M : Type*} (H : Subgroup Γ)
    (c : Γ → Γ → M) (g h : ↥H) : restrictFun2 H c (g, h) = c g h := rfl

@[simp] lemma extendFun2_apply {Γ : Type*} [Group Γ] {M : Type*} [Zero M] (H : Subgroup Γ)
    (c : ↥H × ↥H → M) {g h : Γ} (hg : g ∈ H) (hh : h ∈ H) :
    extendFun2 H c g h = c (⟨g, hg⟩, ⟨h, hh⟩) := by
  simp only [extendFun2, dif_pos hg, dif_pos hh]

lemma extendFun2_add {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] (H : Subgroup Γ)
    {c d : ↥H × ↥H → M} : extendFun2 H (c + d) = extendFun2 H c + extendFun2 H d := by
  funext g h
  by_cases hg : g ∈ H <;> by_cases hh : h ∈ H <;> simp [extendFun2, hg, hh]

lemma extendFun2_zero {Γ : Type*} [Group Γ] {M : Type*} [Zero M] (H : Subgroup Γ) :
    extendFun2 H (0 : ↥H × ↥H → M) = 0 := by
  funext g h
  by_cases hg : g ∈ H <;> by_cases hh : h ∈ H <;> simp [extendFun2, hg, hh]

end

noncomputable section

/-! ## The uniform local constancy statements in the shape of `IsLocConstOn`/`IsLocConst2On`

For a closed subgroup `H` of the profinite group `G_k` the following two lemmas convert local
constancy on `↥H` (resp. on `↥H × ↥H`) into invariance under right translation by `U ∩ H`, for a
single open subgroup `U ≤ G_k`.  This is exactly the shape in which the local constancy
conditions `IsLocConstOn` and `IsLocConst2On` of `LTDDefs/Basic.lean` are phrased, so that
extending a cochain on `↥H` by `0` off `H` is locally constant in the sense required there. -/

variable (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]

/-- One-variable form: a locally constant function on `↥H` is right invariant by `U ∩ H` for some
open subgroup `U ≤ G_k`. -/
theorem exists_openSubgroup_mul_eq_of_isLocallyConstant (H : Subgroup (Ω ≃ₐ[k] Ω))
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω))) {M : Type} {f : ↥H → M}
    (hf : Work.AbsoluteKummer.IsLocallyConstant f) :
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ (x : ↥H) (u : Ω ≃ₐ[k] Ω) (hu : u ∈ H), u ∈ U → f (x * ⟨u, hu⟩) = f x := by
  haveI : CompactSpace ↥H := isCompact_iff_compactSpace.mp hH.isCompact
  obtain ⟨V, hVo, hV⟩ := exists_openSubgroup_forall_mul_eq (G := ↥H) hf
  obtain ⟨U, hUo, hU⟩ := exists_openSubgroup_inter_subset_of_isOpen k Ω H V hVo
  exact ⟨U, hUo, fun x u hu huinU => hV x ⟨u, hu⟩ (hU u huinU hu)⟩

/-- Two-variable form: a locally constant function on `↥H × ↥H` is right invariant by `U ∩ H` for
some open subgroup `U ≤ G_k`. -/
theorem exists_openSubgroup_pair_mul_eq_of_isLocallyConstant (H : Subgroup (Ω ≃ₐ[k] Ω))
    (hH : IsClosed (H : Set (Ω ≃ₐ[k] Ω))) {M : Type} {f : ↥H × ↥H → M}
    (hf : Work.AbsoluteKummer.IsLocallyConstant f) :
    ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ (x y : ↥H) (u v : Ω ≃ₐ[k] Ω) (hu : u ∈ H) (hv : v ∈ H), u ∈ U → v ∈ U →
        f (x * ⟨u, hu⟩, y * ⟨v, hv⟩) = f (x, y) := by
  haveI : CompactSpace ↥H := isCompact_iff_compactSpace.mp hH.isCompact
  obtain ⟨V, hVo, hV⟩ := exists_openSubgroup_pair_forall_mul_eq (G := ↥H)
    (f := fun a b : ↥H => f (a, b)) hf
  obtain ⟨U, hUo, hU⟩ := exists_openSubgroup_inter_subset_of_isOpen k Ω H V hVo
  exact ⟨U, hUo, fun x y u v hu hv huinU hvinU =>
    hV x y ⟨u, hu⟩ (hU u huinU hu) ⟨v, hv⟩ (hU v hvinU hv)⟩

end

noncomputable section

/-! ## The quotient data of `H2loc` and of `H²(↥H, M)` -/

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (H : Subgroup (Ω ≃ₐ[k] Ω))

/-- The quotient submodule exhibiting `H2loc` as a quotient of the locally constant `2`-cocycles
on `G_k` (the submodule `H2loc` is the quotient by). -/
abbrev cobQ2 (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) : Submodule (ZMod p) ↥(lcCocycles2 p k Ω K M H) :=
  Submodule.comap (lcCocycles2 p k Ω K M H).subtype (coboundaries2 p k Ω K M H)

/-- The quotient subgroup exhibiting `H²(↥H, M)` as a quotient of the continuous `2`-cocycles
of `↥H`. -/
abbrev B2Q (G : Type) [Group G] [TopologicalSpace G] (M : Type) [AddCommGroup M]
    [DistribMulAction G M] : AddSubgroup ↥(Work.AbsoluteKummer.Z2 G M) :=
  (Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype

end

end Work.SSGRoute
