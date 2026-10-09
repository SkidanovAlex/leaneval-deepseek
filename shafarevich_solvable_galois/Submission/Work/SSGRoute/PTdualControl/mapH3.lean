import Mathlib
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
import Submission.Work.SSGRoute.kummerBase_euler_connectingH3
import Submission.Work.AbsoluteKummer.SES
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The push-forward `H³(G,M) → H³(G,N)` and the coboundary compatibility

The degree-`3` analogues of `Work.AbsoluteKummer.mapC2c`, `mapZ2`, `mapC1c_mem_B2` and `mapH2`
(`Submission/Work/AbsoluteKummer/Basic.lean`), built on the continuous cohomology `H³` of
`Submission/Work/SSGRoute/kummerBase_euler_h3_absKummer.lean`.  They are the prerequisites of the
exactness statements at `H³` (`range_mapH3_eq_ker_mapH3`, `range_mapH3_eq_ker_deltaH4`) needed by
the long exact sequence of the Poitou–Tate workshop at degrees `3`/`4`.
-/

open scoped Classical

namespace Work.SSGRoute.PTdualControl

open Work.AbsoluteKummer

variable {G : Type*} [TopologicalSpace G] [Group G]

/-- The map `Z³_c(G,M) → Z³_c(G,N)` induced by an equivariant `φ`. -/
def mapZ3 {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [DistribMulAction G M] [DistribMulAction G N] (φ : M →+ N)
    (hφ : Work.GroupCohomology.IsEquivariant G φ) :
    Work.SSGRoute.Z3 (M := M) G →+ Work.SSGRoute.Z3 (M := N) G where
  toFun c := ⟨fun p => φ ((c : G × G × G → M) p), by
    rw [Work.SSGRoute.mem_Z3_iff]
    refine ⟨?_, Work.AbsoluteKummer.IsLocallyConstant.map φ
      ((Work.SSGRoute.mem_Z3_iff (G := G) (M := M)).mp c.2).2⟩
    rw [Work.SSGRoute.d3_comp (G := G) φ hφ ((c : G × G × G → M)),
      ((Work.SSGRoute.mem_Z3_iff (G := G) (M := M)).mp c.2).1]
    exact funext (fun p => map_zero φ)⟩
  map_zero' := by ext p; simp
  map_add' c c' := by ext p; simp [map_add]

@[simp] theorem mapZ3_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [DistribMulAction G M] [DistribMulAction G N] (φ : M →+ N)
    (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (c : Work.SSGRoute.Z3 (M := M) G) (p : G × G × G) :
    (mapZ3 (G := G) φ hφ c : G × G × G → N) p = φ ((c : G × G × G → M) p) := rfl

/-- The image of a `3`-coboundary under `φ` is a `3`-coboundary. -/
theorem mapC2c_mem_B3 {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [DistribMulAction G M] [DistribMulAction G N] (φ : M →+ N)
    (hφ : Work.GroupCohomology.IsEquivariant G φ) {c : G × G × G → M}
    (hc : c ∈ Work.SSGRoute.B3 (M := M) G) : (fun p => φ (c p)) ∈ Work.SSGRoute.B3 (M := N) G := by
  rw [Work.SSGRoute.mem_B3_iff (G := G) (M := M)] at hc
  obtain ⟨f, hf, rfl⟩ := hc
  rw [Work.SSGRoute.mem_B3_iff (G := G) (M := N)]
  refine ⟨fun g => φ ((f : G × G → M) g), Work.AbsoluteKummer.IsLocallyConstant.map φ hf, ?_⟩
  funext p
  obtain ⟨g, h, k⟩ := p
  simp only [Work.GroupCohomology.d2_apply, map_sub, map_add]
  rw [hφ]

/-- The map `H³(G,M) → H³(G,N)` induced by an equivariant additive map of `G`-modules. -/
noncomputable def mapH3 {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [DistribMulAction G M] [DistribMulAction G N] (φ : M →+ N)
    (hφ : Work.GroupCohomology.IsEquivariant G φ) :
    Work.SSGRoute.H3 (M := M) G →+ Work.SSGRoute.H3 (M := N) G :=
  QuotientAddGroup.lift
    ((Work.SSGRoute.B3 (M := M) G).comap (Work.SSGRoute.Z3 (M := M) G).subtype)
    ((Work.SSGRoute.H3π (M := N) G).comp (mapZ3 (G := G) φ hφ)) (by
    intro x hx
    have hx' : ((x : Work.SSGRoute.Z3 (M := M) G) : G × G × G → M)
        ∈ Work.SSGRoute.B3 (M := M) G := by
      simpa using (AddSubgroup.mem_comap.mp hx)
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, Work.SSGRoute.H3π_eq_zero_iff (M := N) G]
    exact mapC2c_mem_B3 (G := G) φ hφ hx')

theorem mapH3_H3π {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [DistribMulAction G M] [DistribMulAction G N] (φ : M →+ N)
    (hφ : Work.GroupCohomology.IsEquivariant G φ) (c : Work.SSGRoute.Z3 (M := M) G) :
    mapH3 (G := G) φ hφ (Work.SSGRoute.H3π (M := M) G c)
      = Work.SSGRoute.H3π (M := N) G (mapZ3 (G := G) φ hφ c) :=
  QuotientAddGroup.lift_mk' _ _ c

end Work.SSGRoute.PTdualControl
