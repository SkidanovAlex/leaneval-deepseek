import Mathlib
import Submission.Work.ORLocInd.CoprodTree.StarTreeIsTree
import Submission.Work.ORBassSerre.Action.Structure.TreeDatum
import Submission.Work.ORBassSerre.Action.CoprodI.coprodI_congr
import Submission.Work.ORLocInd.CohenLyndon.spanTreeLift
import Submission.Work.ORLocInd.CohenLyndon.treeDatum
import Submission.Work.ORLocInd.CohenLyndon.bassSerre_trivialEdgeStabilizers

set_option autoImplicit false
set_option maxHeartbeats 1600000

open Quiver
open Work.ORLocInd.CoprodTree
open Classical

namespace Work.ORLocInd.CohenLyndon

universe u

section Kurosh

variable {ι : Type u} {D : ι → Type u} [∀ i, Group (D i)]

/-- The stabiliser for a restricted action is the `subgroupOf` of the ambient stabiliser. -/
theorem kurosh_stabilizer_subgroupOf {H : Subgroup (Monoid.CoprodI D)}
    {α : Type u} [MulAction (Monoid.CoprodI D) α] (a : α) :
    MulAction.stabilizer H a = (MulAction.stabilizer (Monoid.CoprodI D) a).subgroupOf H := by
  ext h
  exact Iff.rfl

/-- The `i`-th factor is the range of `of`, as a `map` of `⊤`. -/
theorem kurosh_factor_eq (i : ι) :
    Subgroup.map (Monoid.CoprodI.of (M := D) (i := i)) ⊤ = factor D i := by
  ext x
  simp [factor]

variable (H : Subgroup (Monoid.CoprodI D))

theorem kurosh_hninv : Work.ORBassSerre.ActsWithoutInversions H (Vertex D) :=
  fun h e he => actsWithoutInversions (M := D) (h : Monoid.CoprodI D) e he

/-- **A spanning-tree lift datum for the `H`-action on the Bass--Serre tree of `G`.** -/
theorem kurosh_treeDatum :
    Nonempty (Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D)) :=
  nonempty_treeDatum_of_tree (starTree_isTree (M := D)) (kurosh_hninv H)
    (Quotient.mk'' (Sum.inl (1 : Monoid.CoprodI D)))

theorem kurosh_edge_stab_eq_bot (e : Quiver.Total (Vertex D)) :
    MulAction.stabilizer H e = ⊥ := by
  haveI : Subsingleton ↥(MulAction.stabilizer (Monoid.CoprodI D) e) :=
    subsingleton_stabilizer_edge (M := D) e
  have hbot : (MulAction.stabilizer (Monoid.CoprodI D) e : Subgroup (Monoid.CoprodI D)) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact congrArg Subtype.val
      (Subsingleton.elim (α := ↥(MulAction.stabilizer (Monoid.CoprodI D) e))
        ⟨x, hx⟩ ⟨1, Subgroup.one_mem _⟩)
  rw [kurosh_stabilizer_subgroupOf (H := H) e, hbot, Subgroup.bot_subgroupOf]

/-- Every `(H, D i)`-conjugate of a factor is a vertex stabiliser of the `H`-action. -/
theorem kurosh_gen_subset (K : Subgroup (Monoid.CoprodI D)) :
    (⋃ (i : ι) (g : Monoid.CoprodI D), (↑(K ⊓ Subgroup.map (MulAut.conj g).toMonoidHom
        (Subgroup.map (Monoid.CoprodI.of (M := D) (i := i)) ⊤)) : Set (Monoid.CoprodI D)))
      ⊆ Subgroup.map K.subtype
          (Subgroup.closure (⋃ v : Vertex D, (MulAction.stabilizer K v : Set K))) := by
  intro z hz
  simp only [Set.mem_iUnion, SetLike.mem_coe, Subgroup.mem_inf] at hz
  obtain ⟨i, g, hzK, hzC⟩ := hz
  refine ⟨⟨z, hzK⟩, Subgroup.subset_closure ?_, rfl⟩
  refine Set.mem_iUnion.mpr ⟨vtx (some i) g, ?_⟩
  have hG : z ∈ MulAction.stabilizer (Monoid.CoprodI D) (vtx (some i) g) := by
    rw [stabilizer_coset (M := D) i g, ← kurosh_factor_eq (D := D) i]
    exact hzC
  show (⟨z, hzK⟩ : K) • vtx (some i) g = vtx (some i) g
  exact MulAction.mem_stabilizer_iff.mp hG

theorem kurosh_hgen (hgen : H ≤ Subgroup.closure (⋃ (i : ι) (g : Monoid.CoprodI D),
      (↑(H ⊓ Subgroup.map (MulAut.conj g).toMonoidHom
        (Subgroup.map (Monoid.CoprodI.of (M := D) (i := i)) ⊤)) : Set (Monoid.CoprodI D)))) :
    Subgroup.closure (⋃ v : Vertex D, (MulAction.stabilizer H v : Set H)) = ⊤ := by
  rw [eq_top_iff]
  intro h _
  have hmem : (h : Monoid.CoprodI D) ∈
      Subgroup.closure (⋃ (i : ι) (g : Monoid.CoprodI D),
        (↑(H ⊓ Subgroup.map (MulAut.conj g).toMonoidHom
          (Subgroup.map (Monoid.CoprodI.of (M := D) (i := i)) ⊤)) : Set (Monoid.CoprodI D))) :=
    hgen h.2
  have hle : Subgroup.closure (⋃ (i : ι) (g : Monoid.CoprodI D),
        (↑(H ⊓ Subgroup.map (MulAut.conj g).toMonoidHom
          (Subgroup.map (Monoid.CoprodI.of (M := D) (i := i)) ⊤)) : Set (Monoid.CoprodI D)))
      ≤ Subgroup.map H.subtype
          (Subgroup.closure (⋃ v : Vertex D, (MulAction.stabilizer H v : Set H))) := by
    rw [Subgroup.closure_le]
    exact kurosh_gen_subset H
  obtain ⟨y, hy, hyeq⟩ := hle hmem
  have : y = h := Subtype.ext hyeq
  rwa [this] at hy

/-! ## Leaf orbits and the representatives attached to them -/

/-- A vertex orbit is a *leaf* orbit if it contains a coset vertex `vtx (some i) g`. -/
def IsLeafOrbit (A : Work.ORBassSerre.orbitV H (Vertex D)) : Prop :=
  ∃ (i : ι) (g : Monoid.CoprodI D), Quotient.mk'' (vtx (some i) g) = A

variable {H}

theorem exists_vtx_of_leaf (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D))
    {A : Work.ORBassSerre.orbitV H (Vertex D)} (hA : IsLeafOrbit H A) :
    ∃ (i : ι) (g : Monoid.CoprodI D), d.vert A = vtx (some i) g := by
  obtain ⟨i, g, hg⟩ := hA
  have h1 : (Quotient.mk'' (d.vert A) : Work.ORBassSerre.orbitV H (Vertex D))
      = Quotient.mk'' (vtx (some i) g) := by
    rw [d.vert_mk, hg]
  have h2 : MulAction.orbitRel H (Vertex D) (d.vert A) (vtx (some i) g) := Quotient.exact h1
  obtain ⟨h, hh⟩ := MulAction.orbitRel_apply.mp h2
  refine ⟨i, h • g, ?_⟩
  rw [← hh]
  show ((h : H) : Monoid.CoprodI D) • vtx (some i) g
    = vtx (some i) (((h : H) : Monoid.CoprodI D) * g)
  rw [smul_vtx_some]

noncomputable def leafIdx (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D))
    (A : Work.ORBassSerre.orbitV H (Vertex D)) (hA : IsLeafOrbit H A) : ι :=
  Classical.choose (exists_vtx_of_leaf d hA)

noncomputable def leafRep (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D))
    (A : Work.ORBassSerre.orbitV H (Vertex D)) (hA : IsLeafOrbit H A) : Monoid.CoprodI D :=
  Classical.choose (Classical.choose_spec (exists_vtx_of_leaf d hA))

theorem leafRep_spec (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D))
    (A : Work.ORBassSerre.orbitV H (Vertex D)) (hA : IsLeafOrbit H A) :
    d.vert A = vtx (some (leafIdx d A hA)) (leafRep d A hA) :=
  Classical.choose_spec (Classical.choose_spec (exists_vtx_of_leaf d hA))

/-- The stabiliser of a non-leaf orbit representative is trivial. -/
theorem leaf_stab_eq_bot (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D))
    {A : Work.ORBassSerre.orbitV H (Vertex D)} (hA : ¬ IsLeafOrbit H A) :
    MulAction.stabilizer H (d.vert A) = ⊥ := by
  rw [kurosh_stabilizer_subgroupOf (H := H) (d.vert A)]
  have hc : ∃ g : Monoid.CoprodI D, d.vert A = Sum.inl g := by
    rcases hv : d.vert A with g | ⟨i, c⟩
    · exact ⟨g, rfl⟩
    · exfalso
      apply hA
      obtain ⟨g, rfl⟩ := Quotient.exists_rep c
      refine ⟨i, g, ?_⟩
      rw [← d.vert_mk A, hv]
      rfl
  obtain ⟨g, hg⟩ := hc
  rw [hg]
  show (MulAction.stabilizer (Monoid.CoprodI D) (Sum.inl g)).subgroupOf H = ⊥
  rw [show (Sum.inl g : Vertex D) = vtx (none : Option ι) g from rfl, stabilizer_central,
    Subgroup.bot_subgroupOf]

/-- The index type: the leaf vertex orbits. -/
abbrev kuroshLeafOrbits (H : Subgroup (Monoid.CoprodI D)) : Type u :=
  {A : Work.ORBassSerre.orbitV H (Vertex D) // IsLeafOrbit H A}

noncomputable def kuroshLeafIdxI (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D))
    (k : kuroshLeafOrbits H) : ι := leafIdx d k.1 k.2

noncomputable def kuroshLeafRepI (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D))
    (k : kuroshLeafOrbits H) : Monoid.CoprodI D := leafRep d k.1 k.2

/-- The forward map of `kurosh_dropIso`. -/
noncomputable def kurosh_dropFwd (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D)) :
    Monoid.CoprodI (fun A : Work.ORBassSerre.orbitV H (Vertex D) =>
        ↥(MulAction.stabilizer H (d.vert A))) →*
    Monoid.CoprodI (fun k : kuroshLeafOrbits H =>
        ↥(MulAction.stabilizer H (d.vert k.1))) :=
  Monoid.CoprodI.lift (fun A =>
    if h : IsLeafOrbit H A then
      (Monoid.CoprodI.of
        (M := fun k : kuroshLeafOrbits H => ↥(MulAction.stabilizer H (d.vert k.1)))
        (i := ⟨A, h⟩))
    else 1)

/-- The backward map of `kurosh_dropIso`. -/
noncomputable def kurosh_dropBwd (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D)) :
    Monoid.CoprodI (fun k : kuroshLeafOrbits H =>
        ↥(MulAction.stabilizer H (d.vert k.1))) →*
    Monoid.CoprodI (fun A : Work.ORBassSerre.orbitV H (Vertex D) =>
        ↥(MulAction.stabilizer H (d.vert A))) :=
  Monoid.CoprodI.lift (fun k =>
    (Monoid.CoprodI.of
      (M := fun A : Work.ORBassSerre.orbitV H (Vertex D) =>
        ↥(MulAction.stabilizer H (d.vert A))) (i := k.1)))

theorem kurosh_dropBwd_of (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D))
    (k : kuroshLeafOrbits H)
    (w : ↥(MulAction.stabilizer H (d.vert k.1))) :
    kurosh_dropBwd d
        (Monoid.CoprodI.of
          (M := fun k : kuroshLeafOrbits H => ↥(MulAction.stabilizer H (d.vert k.1)))
          (i := k) w)
      = Monoid.CoprodI.of
          (M := fun A : Work.ORBassSerre.orbitV H (Vertex D) =>
            ↥(MulAction.stabilizer H (d.vert A))) (i := k.1) w := by
  simp only [kurosh_dropBwd]
  rw [Monoid.CoprodI.lift_of]

/-- **Dropping the trivial (non-leaf) factors.**  The non-leaf vertex orbits have trivial
stabiliser, so the free product over all vertex orbits is the free product over the leaf orbits. -/
noncomputable def kurosh_dropIso (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D)) :
    Monoid.CoprodI (fun A : Work.ORBassSerre.orbitV H (Vertex D) =>
        ↥(MulAction.stabilizer H (d.vert A))) ≃*
    Monoid.CoprodI (fun k : kuroshLeafOrbits H =>
        ↥(MulAction.stabilizer H (d.vert k.1))) :=
  MonoidHom.toMulEquiv (kurosh_dropFwd d) (kurosh_dropBwd d)
    (by
      classical
      unfold kurosh_dropFwd kurosh_dropBwd
      apply Monoid.CoprodI.ext_hom
      intro A
      rw [MonoidHom.comp_assoc, Monoid.CoprodI.lift_comp_of]
      by_cases h : IsLeafOrbit H A
      · rw [dif_pos h, Monoid.CoprodI.lift_comp_of, MonoidHom.id_comp]
      · rw [dif_neg h]
        have hbot : (MulAction.stabilizer H (d.vert A)) = ⊥ := leaf_stab_eq_bot d h
        apply MonoidHom.ext
        intro z
        have hmem : (z : ↥H) ∈ (⊥ : Subgroup ↥H) := by rw [← hbot]; exact z.2
        have hz : z = 1 := Subtype.ext (by simpa using hmem)
        rw [hz]
        simp)
    (by
      classical
      unfold kurosh_dropFwd kurosh_dropBwd
      apply Monoid.CoprodI.ext_hom
      intro k
      rw [MonoidHom.comp_assoc, Monoid.CoprodI.lift_comp_of, Monoid.CoprodI.lift_comp_of,
        dif_pos k.2, MonoidHom.id_comp])

/-- The stabiliser of a leaf orbit representative is the corresponding factor intersection. -/
theorem kurosh_stab_eq (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D))
    (k : kuroshLeafOrbits H) :
    MulAction.stabilizer H (d.vert k.1) =
      (H ⊓ Subgroup.map (MulAut.conj (kuroshLeafRepI d k)).toMonoidHom
        (Subgroup.map (Monoid.CoprodI.of (M := D) (i := kuroshLeafIdxI d k)) ⊤)).subgroupOf H := by
  have h1 : d.vert k.1 = vtx (some (kuroshLeafIdxI d k)) (kuroshLeafRepI d k) :=
    leafRep_spec d k.1 k.2
  rw [kurosh_stabilizer_subgroupOf (H := H) (d.vert k.1), h1,
    stabilizer_coset (M := D) (kuroshLeafIdxI d k) (kuroshLeafRepI d k),
    ← kurosh_factor_eq (D := D) (kuroshLeafIdxI d k)]
  ext h
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun hx => ⟨h.2, hx⟩, fun hx => hx.2⟩

/-- The per-factor identification of the two descriptions of the factors. -/
noncomputable def kurosh_someEquiv (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D))
    (k : kuroshLeafOrbits H) :
    ↥(H ⊓ Subgroup.map (MulAut.conj (kuroshLeafRepI d k)).toMonoidHom
        (Subgroup.map (Monoid.CoprodI.of (M := D) (i := kuroshLeafIdxI d k)) ⊤))
      ≃* ↥(MulAction.stabilizer H (d.vert k.1)) where
  toFun z := ⟨⟨(z : Monoid.CoprodI D), (Subgroup.mem_inf.mp z.2).1⟩, by
    rw [kurosh_stab_eq d k, Subgroup.mem_subgroupOf]
    exact z.2⟩
  invFun w := ⟨(w : Monoid.CoprodI D), by
    have hw : (w : H) ∈
        (H ⊓ Subgroup.map (MulAut.conj (kuroshLeafRepI d k)).toMonoidHom
          (Subgroup.map (Monoid.CoprodI.of (M := D) (i := kuroshLeafIdxI d k)) ⊤)).subgroupOf H := by
      rw [← kurosh_stab_eq d k]; exact w.2
    exact Subgroup.mem_subgroupOf.mp hw⟩
  left_inv z := Subtype.ext rfl
  right_inv w := Subtype.ext (Subtype.ext rfl)
  map_mul' z z' := Subtype.ext (Subtype.ext rfl)

/-- The index attached to a leaf orbit (unfolded form). -/
theorem kurosh_leafIdx_eq' (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D))
    (j : ι) (g : Monoid.CoprodI D) :
    leafIdx d (Quotient.mk'' (vtx (some j) g)) (⟨j, g, rfl⟩ : IsLeafOrbit H _) = j := by
  have hspec := leafRep_spec d (Quotient.mk'' (vtx (some j) g)) (⟨j, g, rfl⟩ : IsLeafOrbit H _)
  have h1 : (Quotient.mk'' (d.vert (Quotient.mk'' (vtx (some j) g)))
      : Work.ORBassSerre.orbitV H (Vertex D)) = Quotient.mk'' (vtx (some j) g) :=
    d.vert_mk _
  have h2 : MulAction.orbitRel H (Vertex D)
      (d.vert (Quotient.mk'' (vtx (some j) g))) (vtx (some j) g) := Quotient.exact h1
  obtain ⟨h, hh⟩ := MulAction.orbitRel_apply.mp h2
  have hh' : ((h : H) : Monoid.CoprodI D) • (vtx (some j) g : Vertex D)
      = d.vert (Quotient.mk'' (vtx (some j) g)) := hh
  rw [← hh'] at hspec
  rw [smul_vtx_some (M := D) ((h : H) : Monoid.CoprodI D) g j] at hspec
  exact (idx_eq_of_vtx_some_eq hspec).symm

/-- The index attached to a leaf orbit. -/
theorem kurosh_leafIdx_eq (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D))
    (j : ι) (g : Monoid.CoprodI D) :
    kuroshLeafIdxI d ⟨Quotient.mk'' (vtx (some j) g), ⟨j, g, rfl⟩⟩ = j :=
  kurosh_leafIdx_eq' d j g

/-- The representative of a leaf orbit lies in the corresponding `(H, D i)`-double coset. -/
theorem kurosh_leaf_mem (d : Work.ORBassSerre.Action.Structure.TreeDatum H (Vertex D))
    (j : ι) (g : Monoid.CoprodI D) :
    ∃ c : H, ∃ e : D j, g = (c : Monoid.CoprodI D) *
      kuroshLeafRepI d ⟨Quotient.mk'' (vtx (some j) g), ⟨j, g, rfl⟩⟩ * Monoid.CoprodI.of e := by
  have hspec := leafRep_spec d (Quotient.mk'' (vtx (some j) g)) (⟨j, g, rfl⟩ : IsLeafOrbit H _)
  have h1 : (Quotient.mk'' (d.vert (Quotient.mk'' (vtx (some j) g)))
      : Work.ORBassSerre.orbitV H (Vertex D)) = Quotient.mk'' (vtx (some j) g) :=
    d.vert_mk _
  have h2 : MulAction.orbitRel H (Vertex D)
      (d.vert (Quotient.mk'' (vtx (some j) g))) (vtx (some j) g) := Quotient.exact h1
  obtain ⟨h, hh⟩ := MulAction.orbitRel_apply.mp h2
  have hh' : ((h : H) : Monoid.CoprodI D) • (vtx (some j) g : Vertex D)
      = d.vert (Quotient.mk'' (vtx (some j) g)) := hh
  rw [← hh'] at hspec
  rw [smul_vtx_some (M := D) ((h : H) : Monoid.CoprodI D) g j] at hspec
  rw [kurosh_leafIdx_eq' d j g] at hspec
  obtain ⟨e, he⟩ := mem_factor.mp ((vtx_some_eq_vtx_some).mp hspec)
  refine ⟨h⁻¹, e⁻¹, ?_⟩
  have key : ((h : H) : Monoid.CoprodI D) * g
      = kuroshLeafRepI d ⟨Quotient.mk'' (vtx (some j) g), ⟨j, g, rfl⟩⟩ * Monoid.CoprodI.of e⁻¹ := by
    simp only [kuroshLeafRepI]
    rw [MonoidHom.map_inv, he]
    group
  rw [mul_assoc, ← key]
  simp only [Subgroup.coe_inv]
  group

variable (H : Subgroup (Monoid.CoprodI D))

/-- **The Kurosh decomposition of a subgroup of a free product (no free part).** -/
theorem kurosh_subgroup_coprodI {ι : Type u} {D : ι → Type u} [∀ i, Group (D i)]
    (H : Subgroup (Monoid.CoprodI D))
    (hgen : H ≤ Subgroup.closure (⋃ (i : ι) (g : Monoid.CoprodI D),
      (↑(H ⊓ Subgroup.map (MulAut.conj g).toMonoidHom
        (Subgroup.map (Monoid.CoprodI.of (M := D) (i := i)) ⊤)) : Set (Monoid.CoprodI D)))) :
    ∃ (Ω : Type u) (i : Ω → ι) (x : Ω → Monoid.CoprodI D),
      (∀ (j : ι) (g : Monoid.CoprodI D), ∃ k : Ω, i k = j ∧ ∃ c : H, ∃ d : D j,
        g = (c : Monoid.CoprodI D) * x k * Monoid.CoprodI.of (M := D) d) ∧
      (∀ k l : Ω, i k = i l → (∃ c : H, ∃ d : D (i k),
        x k = (c : Monoid.CoprodI D) * x l * Monoid.CoprodI.of (M := D) d) → k = l) ∧
      ∃ e : Monoid.CoprodI (fun k : Ω => ↥(H ⊓ Subgroup.map (MulAut.conj (x k)).toMonoidHom
            (Subgroup.map (Monoid.CoprodI.of (M := D) (i := i k)) ⊤))) ≃* ↥H,
        ∀ (k : Ω) (z : ↥(H ⊓ Subgroup.map (MulAut.conj (x k)).toMonoidHom
            (Subgroup.map (Monoid.CoprodI.of (M := D) (i := i k)) ⊤))),
          e (Monoid.CoprodI.of (M := fun k : Ω => ↥(H ⊓ Subgroup.map (MulAut.conj (x k)).toMonoidHom
            (Subgroup.map (Monoid.CoprodI.of (M := D) (i := i k)) ⊤))) (i := k) z)
            = ⟨(z : Monoid.CoprodI D), z.2.1⟩ := by
  classical
  obtain ⟨d⟩ := kurosh_treeDatum H
  have hT : Work.ORBassSerre.IsTree (Vertex D) := starTree_isTree (M := D)
  obtain ⟨e₀, he₀⟩ := bassSerre_trivialEdgeStabilizers (Γ := H) d hT (kurosh_hninv H)
    (kurosh_edge_stab_eq_bot H) (kurosh_hgen H hgen)
  refine ⟨kuroshLeafOrbits H, kuroshLeafIdxI d, kuroshLeafRepI d, ?_, ?_, ?_⟩
  · intro j g
    exact ⟨⟨Quotient.mk'' (vtx (some j) g), ⟨j, g, rfl⟩⟩, kurosh_leafIdx_eq d j g,
      kurosh_leaf_mem d j g⟩
  · intro k l hij h
    obtain ⟨c, e, he⟩ := h
    apply Subtype.ext
    rw [← d.vert_mk k.1, ← d.vert_mk l.1]
    have hkey : d.vert k.1 = (c : Monoid.CoprodI D) • d.vert l.1 := by
      calc d.vert k.1
          = vtx (some (kuroshLeafIdxI d k)) (kuroshLeafRepI d k) := leafRep_spec d k.1 k.2
        _ = vtx (some (kuroshLeafIdxI d k))
              ((c : Monoid.CoprodI D) * kuroshLeafRepI d l * Monoid.CoprodI.of e) := by rw [he]
        _ = vtx (some (kuroshLeafIdxI d k)) ((c : Monoid.CoprodI D) * kuroshLeafRepI d l) := by
              refine vtx_some_eq_vtx_some.mpr (mem_factor.mpr ⟨e⁻¹, ?_⟩)
              rw [MonoidHom.map_inv]
              group
        _ = (c : Monoid.CoprodI D) • vtx (some (kuroshLeafIdxI d k)) (kuroshLeafRepI d l) :=
              (smul_vtx_some (M := D) ((c : H) : Monoid.CoprodI D) (kuroshLeafRepI d l)
                (kuroshLeafIdxI d k)).symm
        _ = (c : Monoid.CoprodI D) • d.vert l.1 := by
              rw [hij]
              exact congrArg (fun v : Vertex D => (c : Monoid.CoprodI D) • v)
                (leafRep_spec d l.1 l.2).symm
    rw [hkey]
    exact Quotient.sound (MulAction.orbitRel_apply.mpr ⟨c, rfl⟩)
  · obtain ⟨Φ, hΦ⟩ := Work.ORBassSerre.Action.CoprodI.coprodI_congr
      (fun k => kurosh_someEquiv d k)
    refine ⟨Φ.trans ((kurosh_dropIso d).symm.trans e₀), ?_⟩
    intro k z
    have hstep : Φ.trans ((kurosh_dropIso d).symm.trans e₀) (Monoid.CoprodI.of z)
        = e₀ (Monoid.CoprodI.of ((kurosh_someEquiv d k) z)) := by
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hΦ]
      exact congrArg e₀ (kurosh_dropBwd_of d k ((kurosh_someEquiv d k) z))
    rw [hstep, he₀ k (kurosh_someEquiv d k z)]
    rfl

end Kurosh

end Work.ORLocInd.CohenLyndon
