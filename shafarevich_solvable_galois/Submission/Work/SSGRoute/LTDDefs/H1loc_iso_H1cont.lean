import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.SSGRoute.LTDDefs.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The model bridge: locally constant cohomology of a subgroup

`LTDDefs/Basic.lean` defines the local cohomology `H1loc` of a subgroup `H ≤ G_k = Ω ≃ₐ[k] Ω`
through functions on the *whole* group `G_k` satisfying the cocycle and local-constancy conditions
only on `H`.  This file compares that model with the workspace's locally constant cochain model
`Work.AbsoluteKummer` for the topological group `H` itself: the map is restriction of a cocycle to
`H` (inverse: extension by `0` off `H`), and it induces an isomorphism of `𝔽_p`-modules

`H1loc p k Ω K M H ≃+ Work.AbsoluteKummer.H1 ↥H M`.

This makes the whole continuous cohomology toolkit (inflation, restriction, connecting maps,
Kummer theory, Hilbert 90, …) available for `H1loc`.
-/

open scoped TensorProduct
open Classical

set_option maxHeartbeats 2000000

namespace Work.SSGRoute

noncomputable section

section Bridge

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
  [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
  (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M]
  [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
  (H : Subgroup (Ω ≃ₐ[k] Ω)) [DistribMulAction ↥H M]

/-- The restriction of a locally constant `1`-cocycle on `H` (a function on `G_k`) to the group
`H` is a crossed homomorphism. -/
lemma restrict_isCrossedHom
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    {f : (Ω ≃ₐ[k] Ω) → M} (hf : f ∈ lcCocycles p k Ω K M H) :
    Work.GroupCohomology.IsCrossedHom ↥H M (fun h : ↥H => f h) := by
  intro g h
  have h1 := hf.1 (g : Ω ≃ₐ[k] Ω) g.2 (h : Ω ≃ₐ[k] Ω) h.2
  show f ((g * h : ↥H) : Ω ≃ₐ[k] Ω) = g • f h + f g
  rw [Subgroup.coe_mul, h1, hcompat g (f h)]
  abel

/-- The restriction of a function which is locally constant on `H` (in the sense of
`SSGRoute.IsLocConstOn`, i.e. uniformly right-invariant by an open subgroup of `G_k`) is locally
constant on the topological group `H`. -/
lemma restrict_isLocallyConstant {f : (Ω ≃ₐ[k] Ω) → M} (hf : SSGRoute.IsLocConstOn H f) :
    Work.AbsoluteKummer.IsLocallyConstant (fun h : ↥H => f h) := by
  obtain ⟨U, hUo, hU⟩ := hf
  intro x
  refine ⟨(fun h : ↥H => (x : Ω ≃ₐ[k] Ω)⁻¹ * (h : Ω ≃ₐ[k] Ω)) ⁻¹' (U : Set (Ω ≃ₐ[k] Ω)),
    ?_, ?_, ?_⟩
  · exact hUo.preimage (continuous_const.mul continuous_subtype_val)
  · simp only [Set.mem_preimage]
    have hx : (x : Ω ≃ₐ[k] Ω)⁻¹ * (x : Ω ≃ₐ[k] Ω) = 1 := inv_mul_cancel _
    rw [hx]
    exact U.one_mem
  · intro y hy
    simp only [Set.mem_preimage] at hy
    have hyH : (x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω) ∈ H :=
      H.mul_mem (H.inv_mem x.2) y.2
    have hthis := hU (x : Ω ≃ₐ[k] Ω) x.2 ((x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω)) hy hyH
    have hxy : (x : Ω ≃ₐ[k] Ω) * ((x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω)) = (y : Ω ≃ₐ[k] Ω) := by
      rw [← mul_assoc, mul_inv_cancel, one_mul]
    show f y = f x
    rw [← hxy, hthis]

/-- Restriction of a locally constant `1`-cocycle on `H ⊆ G_k` (a function on `G_k`) to the
group `H`, as an additive map on the cocycle groups. -/
def restrictCocycle
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    (lcCocycles p k Ω K M H) →+ ↥(Work.AbsoluteKummer.Z1 ↥H M) where
  toFun f := ⟨fun h : ↥H => f.1 h, by
    refine ⟨?_, ?_⟩
    · intro g h
      have h1 := f.2.1 (g : Ω ≃ₐ[k] Ω) g.2 (h : Ω ≃ₐ[k] Ω) h.2
      show f.1 ((g * h : ↥H) : Ω ≃ₐ[k] Ω) = g • f.1 h + f.1 g
      rw [Subgroup.coe_mul, h1, hcompat g (f.1 h)]
      abel
    · obtain ⟨U, hUo, hU⟩ := f.2.2
      intro x
      refine ⟨(fun h : ↥H => (x : Ω ≃ₐ[k] Ω)⁻¹ * (h : Ω ≃ₐ[k] Ω)) ⁻¹' (U : Set (Ω ≃ₐ[k] Ω)),
        ?_, ?_, ?_⟩
      · exact hUo.preimage (continuous_const.mul continuous_subtype_val)
      · have hx : (x : Ω ≃ₐ[k] Ω)⁻¹ * (x : Ω ≃ₐ[k] Ω) = 1 := inv_mul_cancel _
        rw [Set.mem_preimage, hx]
        exact U.one_mem
      · intro y hy
        simp only [Set.mem_preimage] at hy
        have hyH : (x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω) ∈ H :=
          H.mul_mem (H.inv_mem x.2) y.2
        have hthis := hU (x : Ω ≃ₐ[k] Ω) x.2 ((x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω)) hy hyH
        have hxy : (x : Ω ≃ₐ[k] Ω) * ((x : Ω ≃ₐ[k] Ω)⁻¹ * (y : Ω ≃ₐ[k] Ω)) =
            (y : Ω ≃ₐ[k] Ω) := by
          rw [← mul_assoc, mul_inv_cancel, one_mul]
        show f.1 y = f.1 x
        rw [← hxy, hthis]⟩
  map_zero' := Subtype.ext (funext fun h => rfl)
  map_add' a b := Subtype.ext (funext fun h => rfl)

/-- Extension by `0` of a locally constant crossed homomorphism on `H` to a locally constant
`1`-cocycle on `H` (a function on `G_k` which vanishes off `H`), as an additive map on the cocycle
groups.  This is the inverse of `restrictCocycle` modulo coboundaries. -/
def extendCocycle
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    ↥(Work.AbsoluteKummer.Z1 ↥H M) →+ (lcCocycles p k Ω K M H) where
  toFun c := ⟨fun g => if hg : g ∈ H then c.1 ⟨g, hg⟩ else 0, by
    refine ⟨?_, ?_⟩
    · intro g hg h hh
      have hgh : g * h ∈ H := H.mul_mem hg hh
      have hc := c.2.1 ⟨g, hg⟩ ⟨h, hh⟩
      rw [show (⟨g, hg⟩ * ⟨h, hh⟩ : ↥H) = ⟨g * h, hgh⟩ from Subtype.ext rfl] at hc
      simp only [dif_pos hg, dif_pos hh, dif_pos hgh]
      rw [hc, hcompat ⟨g, hg⟩ (c.1 ⟨h, hh⟩)]
      abel
    · obtain ⟨V, hVo, h1V, hV⟩ := c.2.2 1
      have hc1 : c.1 1 = 0 := by
        have h11 := c.2.1 1 1
        have h1m : c.1 1 = 1 • c.1 1 + c.1 1 := by simpa using h11
        rw [one_smul] at h1m
        have h2 : c.1 1 + (0 : M) = c.1 1 + c.1 1 := by rw [add_zero]; exact h1m
        exact (add_left_cancel h2).symm
      obtain ⟨W, hWo, hWV⟩ := isOpen_induced_iff.mp hVo
      have h1W : (1 : Ω ≃ₐ[k] Ω) ∈ W := by
        have h : (1 : ↥H) ∈ (fun x : ↥H => (x : Ω ≃ₐ[k] Ω)) ⁻¹' W := by rw [hWV]; exact h1V
        exact h
      obtain ⟨E', hE'fd, hE'sub⟩ :=
        (krullTopology_mem_nhds_one_iff k Ω W).mp (hWo.mem_nhds h1W)
      haveI := hE'fd
      refine ⟨E'.fixingSubgroup, E'.fixingSubgroup_isOpen, ?_⟩
      intro g hg u hu huH
      have hguH : g * u ∈ H := H.mul_mem hg huH
      have huV : (⟨u, huH⟩ : ↥H) ∈ V := by
        rw [← hWV]; exact hE'sub hu
      have hcu : c.1 ⟨u, huH⟩ = 0 := by rw [hV ⟨u, huH⟩ huV, hc1]
      have hc := c.2.1 ⟨g, hg⟩ ⟨u, huH⟩
      rw [show (⟨g, hg⟩ * ⟨u, huH⟩ : ↥H) = ⟨g * u, hguH⟩ from Subtype.ext rfl] at hc
      simp only [dif_pos hg, dif_pos hguH]
      rw [hc, hcu, hcompat ⟨g, hg⟩ (0 : M), smul_zero, zero_add]⟩
  map_zero' := Subtype.ext (funext fun g => by by_cases hg : g ∈ H <;> simp [hg])
  map_add' a b := Subtype.ext (funext fun g => by by_cases hg : g ∈ H <;> simp [hg])

/-- The restriction of a coboundary on `H` (a function on `G_k`) is a coboundary on `H`. -/
lemma restrictCocycle_mem_coboundaries
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    {f : (Ω ≃ₐ[k] Ω) → M} (hf : f ∈ coboundaries p k Ω K M H)
    (hflc : f ∈ lcCocycles p k Ω K M H) :
    restrictCocycle p k Ω K M H hcompat ⟨f, hflc⟩ ∈
      (Work.AbsoluteKummer.B1 ↥H M).comap (Work.AbsoluteKummer.Z1 ↥H M).subtype := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨m, ?_⟩
  funext h
  show h • m - m = f h
  rw [hcompat h m, hm (h : Ω ≃ₐ[k] Ω) h.2]

/-- The extension by zero of a coboundary on `H` is a coboundary on `H` (as a function on `G_k`). -/
lemma extendCocycle_mem_coboundaries
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    {c : ↥(Work.AbsoluteKummer.Z1 ↥H M)}
    (hc : c ∈ (Work.AbsoluteKummer.B1 ↥H M).comap (Work.AbsoluteKummer.Z1 ↥H M).subtype) :
    (extendCocycle p k Ω K M H hcompat c).1 ∈ coboundaries p k Ω K M H := by
  obtain ⟨m, hm⟩ := hc
  refine ⟨m, ?_⟩
  intro g hg
  have hcg : c.1 ⟨g, hg⟩ = (Work.GroupCohomology.d0 ↥H M m) ⟨g, hg⟩ :=
    (congrFun hm ⟨g, hg⟩).symm
  show (if hg' : g ∈ H then c.1 ⟨g, hg'⟩ else 0) = SSGRoute.res k K g • m - m
  rw [dif_pos hg, hcg]
  show (⟨g, hg⟩ : ↥H) • m - m = SSGRoute.res k K g • m - m
  rw [hcompat ⟨g, hg⟩ m]

/-- **`D₁` membership.**  `extendCocycle` after `restrictCocycle` differs from the identity by a
function vanishing on `H`, hence by a coboundary. -/
lemma extendCocycle_restrictCocycle_sub_mem
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (f : ↥(lcCocycles p k Ω K M H)) :
    extendCocycle p k Ω K M H hcompat (restrictCocycle p k Ω K M H hcompat f) - f ∈
      Submodule.comap (lcCocycles p k Ω K M H).subtype (coboundaries p k Ω K M H) := by
  refine ⟨0, fun g hg => ?_⟩
  have h1 : (extendCocycle p k Ω K M H hcompat
      (restrictCocycle p k Ω K M H hcompat f) : (Ω ≃ₐ[k] Ω) → M) g = f.1 g := by
    show (if hg' : g ∈ H then (restrictCocycle p k Ω K M H hcompat f).1 ⟨g, hg'⟩ else 0)
      = f.1 g
    rw [dif_pos hg]
    rfl
  show ((extendCocycle p k Ω K M H hcompat (restrictCocycle p k Ω K M H hcompat f) :
      (Ω ≃ₐ[k] Ω) → M) - (f : (Ω ≃ₐ[k] Ω) → M)) g
    = SSGRoute.res k K g • (0 : M) - 0
  rw [Pi.sub_apply, h1]
  simp

/-- **`D₂` membership.**  `restrictCocycle` after `extendCocycle` is the identity on the nose. -/
lemma restrictCocycle_extendCocycle_sub_mem
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m)
    (c : ↥(Work.AbsoluteKummer.Z1 ↥H M)) :
    restrictCocycle p k Ω K M H hcompat (extendCocycle p k Ω K M H hcompat c) - c ∈
      (Work.AbsoluteKummer.B1 ↥H M).comap (Work.AbsoluteKummer.Z1 ↥H M).subtype := by
  refine ⟨0, ?_⟩
  funext h
  have h1 : (extendCocycle p k Ω K M H hcompat c : (Ω ≃ₐ[k] Ω) → M)
      (h : Ω ≃ₐ[k] Ω) = c.1 h := by
    show (if hh : (h : Ω ≃ₐ[k] Ω) ∈ H then c.1 ⟨h, hh⟩ else 0) = c.1 h
    rw [dif_pos h.2]
  have h2 : (restrictCocycle p k Ω K M H hcompat
      (extendCocycle p k Ω K M H hcompat c) : (↥H) → M) h = c.1 h := h1
  show (Work.GroupCohomology.d0 ↥H M 0) h
    = ((restrictCocycle p k Ω K M H hcompat (extendCocycle p k Ω K M H hcompat c) :
        (↥H) → M) - (c.1 : (↥H) → M)) h
  rw [Pi.sub_apply, h2]
  simp


/-- The quotient submodule exhibiting `H1loc` as a quotient of the locally constant cocycles. -/
abbrev cobQ (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction (K ≃ₐ[k] K) M] [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M]
    (H : Subgroup (Ω ≃ₐ[k] Ω)) :
    Submodule (ZMod p) ↥(lcCocycles p k Ω K M H) :=
  Submodule.comap (lcCocycles p k Ω K M H).subtype (coboundaries p k Ω K M H)

/-- The quotient subgroup exhibiting `H¹_c(H,M)` as a quotient of the continuous cocycles. -/
abbrev B1Q (G : Type) [Group G] [TopologicalSpace G] (M : Type) [AddCommGroup M]
    [DistribMulAction G M] : AddSubgroup ↥(Work.AbsoluteKummer.Z1 G M) :=
  (Work.AbsoluteKummer.B1 G M).comap (Work.AbsoluteKummer.Z1 G M).subtype

/-- **The restriction map on local `H¹`-groups**: restricting a locally constant cocycle on `H`
(a function on `G_k`) to `H` and passing to cohomology. -/
def bridgeFwd
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    H1loc p k Ω K M H →+ Work.AbsoluteKummer.H1 ↥H M :=
  QuotientAddGroup.map (cobQ p k Ω K M H).toAddSubgroup (B1Q ↥H M)
    (restrictCocycle p k Ω K M H hcompat) (by
      rintro ⟨f, hf⟩ hx
      exact restrictCocycle_mem_coboundaries p k Ω K M H hcompat hx hf)

/-- **The inverse map on local `H¹`-groups**: extending a continuous cocycle on `H` by zero off
`H`, and passing to cohomology. -/
def bridgeBwd
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    Work.AbsoluteKummer.H1 ↥H M →+ H1loc p k Ω K M H :=
  QuotientAddGroup.map (B1Q ↥H M) (cobQ p k Ω K M H).toAddSubgroup
    (extendCocycle p k Ω K M H hcompat) (by
      intro c hc
      exact extendCocycle_mem_coboundaries p k Ω K M H hcompat hc)

/-- **The model bridge.**  The locally constant cohomology `H1loc` of `LTDDefs/Basic` is the same
as the workspace's continuous-cochain model `Work.AbsoluteKummer.H1` of `H¹(H,M)`. -/
def H1locEquivH1
    (hcompat : ∀ (h : ↥H) (m : M), h • m = SSGRoute.res k K (h : Ω ≃ₐ[k] Ω) • m) :
    H1loc p k Ω K M H ≃+ Work.AbsoluteKummer.H1 ↥H M where
  toFun := bridgeFwd p k Ω K M H hcompat
  invFun := bridgeBwd p k Ω K M H hcompat
  left_inv x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective (p := cobQ p k Ω K M H) x
    show bridgeBwd p k Ω K M H hcompat
      (bridgeFwd p k Ω K M H hcompat (Submodule.Quotient.mk z)) = Submodule.Quotient.mk z
    have h1 : bridgeFwd p k Ω K M H hcompat (Submodule.Quotient.mk z)
        = QuotientAddGroup.mk' (B1Q ↥H M) (restrictCocycle p k Ω K M H hcompat z) :=
      QuotientAddGroup.map_mk' _ _ _ _ z
    have h2 : bridgeBwd p k Ω K M H hcompat
        (QuotientAddGroup.mk' (B1Q ↥H M) (restrictCocycle p k Ω K M H hcompat z))
        = Submodule.Quotient.mk (extendCocycle p k Ω K M H hcompat
            (restrictCocycle p k Ω K M H hcompat z)) :=
      QuotientAddGroup.map_mk' _ _ _ _ _
    rw [h1, h2, Submodule.Quotient.eq]
    exact extendCocycle_restrictCocycle_sub_mem p k Ω K M H hcompat z
  right_inv y := by
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective (B1Q ↥H M) y
    show bridgeFwd p k Ω K M H hcompat
      (bridgeBwd p k Ω K M H hcompat (QuotientAddGroup.mk' (B1Q ↥H M) c))
      = QuotientAddGroup.mk' (B1Q ↥H M) c
    have h1 : bridgeBwd p k Ω K M H hcompat (QuotientAddGroup.mk' (B1Q ↥H M) c)
        = Submodule.Quotient.mk (extendCocycle p k Ω K M H hcompat c) :=
      QuotientAddGroup.map_mk' _ _ _ _ _
    have h2 : bridgeFwd p k Ω K M H hcompat
        (Submodule.Quotient.mk (extendCocycle p k Ω K M H hcompat c))
        = QuotientAddGroup.mk' (B1Q ↥H M)
            (restrictCocycle p k Ω K M H hcompat (extendCocycle p k Ω K M H hcompat c)) :=
      QuotientAddGroup.map_mk' _ _ _ _ _
    rw [h1, h2, QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq]
    have hd := restrictCocycle_extendCocycle_sub_mem p k Ω K M H hcompat c
    have hthis : -(restrictCocycle p k Ω K M H hcompat (extendCocycle p k Ω K M H hcompat c))
        + c = -(restrictCocycle p k Ω K M H hcompat (extendCocycle p k Ω K M H hcompat c)
          - c) := by abel
    rw [hthis]
    exact (B1Q ↥H M).neg_mem hd
  map_add' x y := (bridgeFwd p k Ω K M H hcompat).map_add x y

