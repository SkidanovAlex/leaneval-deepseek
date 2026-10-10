import Mathlib.Topology.Constructions
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Actions
import Submission.Work.AbsoluteKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction of continuous `2`-cohomology to a subgroup

For a topological group `G`, a subgroup `U ≤ G` and a discrete `G`-module `A` (so that `U` acts on
`A` by restriction), this file constructs the additive *restriction* map

  `resH2 U : H²(G, A) →+ H²(U, A)`,

restricting a locally constant `2`-cocycle on `G` to `U × U`; local constancy is preserved because
`U × U → G × G` is continuous, the cocycle identity is a pointwise condition, and `d¹` is computed
pointwise, so `2`-coboundaries go to `2`-coboundaries.

This is the map whose bijectivity on `p`-torsion is the class-formation axiom (1.1b) of Milne's
dévissage for `(D_A, \bar Ω^×)`, and the map appearing in the Shapiro/cup compatibility square of
the five-lemma step of `Work.SSGRoute.PT.localTatePairing_deg02`
(see `Submission/Work/SSGRoute/PT/LTD02_STATUS.md`).
-/

namespace Work.SSGRoute.PT

open Classical

noncomputable section

universe u v

variable {G : Type u} [TopologicalSpace G] [Group G]

/-- Restriction of a `2`-cochain on `G` to `U × U`. -/
def resCochain2 (U : Subgroup G) {A : Type v} [AddCommGroup A] [DistribMulAction G A] :
    (G × G → A) →+ (↥U × ↥U → A) where
  toFun c := fun p => c ((p.1 : G), (p.2 : G))
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem resCochain2_apply (U : Subgroup G) {A : Type v} [AddCommGroup A]
    [DistribMulAction G A] (c : G × G → A) (p : ↥U × ↥U) :
    resCochain2 U c p = c ((p.1 : G), (p.2 : G)) := rfl

/-- Restriction of a locally constant `2`-cocycle on `G` to `U`. -/
def resZ2 (U : Subgroup G) {A : Type v} [AddCommGroup A] [DistribMulAction G A] :
    Work.AbsoluteKummer.Z2 G A →+ Work.AbsoluteKummer.Z2 ↥U A where
  toFun c := ⟨fun p => (c : G × G → A) ((p.1 : G), (p.2 : G)), by
    obtain ⟨hcoc, hlc⟩ :=
      (Work.AbsoluteKummer.mem_Z2_iff (c := (c : G × G → A))).mp c.2
    refine (Work.AbsoluteKummer.mem_Z2_iff (M := A) (c :=
      fun p : ↥U × ↥U => (c : G × G → A) ((p.1 : G), (p.2 : G)))).mpr ⟨?_, ?_⟩
    · intro g h k
      exact hcoc (g : G) (h : G) (k : G)
    · intro p
      obtain ⟨W, hW, hpW, hWc⟩ := hlc ((p.1 : G), (p.2 : G))
      refine ⟨{q : ↥U × ↥U | ((q.1 : G), (q.2 : G)) ∈ W}, ?_, hpW, ?_⟩
      · exact hW.preimage ((continuous_subtype_val.comp continuous_fst).prodMk
          (continuous_subtype_val.comp continuous_snd))
      · intro q hq
        exact hWc ((q.1 : G), (q.2 : G)) hq⟩
  map_zero' := by
    apply Subtype.ext
    funext p
    rfl
  map_add' := by
    intro c d
    apply Subtype.ext
    funext p
    rfl

@[simp] theorem resZ2_coe (U : Subgroup G) {A : Type v} [AddCommGroup A]
    [DistribMulAction G A] (c : Work.AbsoluteKummer.Z2 G A) (p : ↥U × ↥U) :
    ((resZ2 U c : Work.AbsoluteKummer.Z2 ↥U A) : ↥U × ↥U → A) p
      = (c : G × G → A) ((p.1 : G), (p.2 : G)) := rfl

/-- `resZ2` carries `2`-coboundaries to `2`-coboundaries. -/
theorem resZ2_mem_B2 (U : Subgroup G) {A : Type v} [AddCommGroup A] [DistribMulAction G A]
    {c : Work.AbsoluteKummer.Z2 G A}
    (hc : (c : G × G → A) ∈ Work.AbsoluteKummer.B2 G A) :
    ((resZ2 U c : Work.AbsoluteKummer.Z2 ↥U A) : ↥U × ↥U → A) ∈
      Work.AbsoluteKummer.B2 ↥U A := by
  obtain ⟨b, hb, hbc⟩ := (Work.AbsoluteKummer.mem_B2_iff (c := (c : G × G → A))).mp hc
  refine (Work.AbsoluteKummer.mem_B2_iff (G := ↥U)
    (c := fun p : ↥U × ↥U => (c : G × G → A) ((p.1 : G), (p.2 : G)))).mpr
    ⟨fun u => b (u : G), ?_, ?_⟩
  · exact (Work.AbsoluteKummer.mem_C1c_iff _).mpr (by
      intro u
      obtain ⟨W, hW, huW, hWc⟩ := (Work.AbsoluteKummer.isLocallyConstantAt_iff).mp
        ((Work.AbsoluteKummer.mem_C1c_iff b).mp hb (u : G))
      exact ⟨{v : ↥U | (v : G) ∈ W}, hW.preimage continuous_subtype_val, huW,
        fun v hv => hWc (v : G) hv⟩)
  · funext p
    obtain ⟨g, h⟩ := p
    have hbfun : Work.GroupCohomology.d1 G A b = (c : G × G → A) := hbc
    have hpt := congrFun hbfun ((g : G), (h : G))
    simp only [Work.GroupCohomology.d1_apply, Subgroup.coe_mul, Subgroup.smul_def] at hpt ⊢
    exact hpt

/-- **Restriction of continuous `2`-cohomology to a subgroup.** -/
noncomputable def resH2 (U : Subgroup G) {A : Type v} [AddCommGroup A] [DistribMulAction G A] :
    Work.AbsoluteKummer.H2 G A →+ Work.AbsoluteKummer.H2 ↥U A :=
  QuotientAddGroup.lift
    ((Work.AbsoluteKummer.B2 G A).comap (Work.AbsoluteKummer.Z2 G A).subtype)
    ((Work.AbsoluteKummer.H2π ↥U A).comp (resZ2 U)) (by
      intro x hx
      have hx' : ((x : Work.AbsoluteKummer.Z2 G A) : G × G → A)
          ∈ Work.AbsoluteKummer.B2 G A := AddSubgroup.mem_comap.mp hx
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, Work.AbsoluteKummer.H2π_eq_zero_iff]
      exact resZ2_mem_B2 U hx')

theorem resH2_H2π (U : Subgroup G) {A : Type v} [AddCommGroup A] [DistribMulAction G A]
    (c : Work.AbsoluteKummer.Z2 G A) :
    resH2 U (Work.AbsoluteKummer.H2π G A c)
      = Work.AbsoluteKummer.H2π ↥U A (resZ2 U c) :=
  QuotientAddGroup.lift_mk' _ _ c

end

end Work.SSGRoute.PT
