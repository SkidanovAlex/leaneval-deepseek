/-
Copyright (c) 2025. All rights reserved.

# Short exact sequences of discrete modules: the low-degree exact sequence

For a short exact sequence `0 → M →^{ι} N →^{π} P → 0` of **discrete** `G`-modules (all maps
equivariant), the chapter's continuous cohomology gives the beginning of the long exact sequence

`0 → H⁰(M) → H⁰(N) → H⁰(P) →^{δ} H¹(M) → H¹(N) → H¹(P)`.

This file records the vocabulary (`ShortExactSeq`), the trivial part (`π ∘ ι = 0`, hence the
composite on `H¹` vanishes) and the statements of the exactness and of the connecting map, which
are proved in `Submission/Work/AbsoluteKummer/SES/`.

The connecting map `δ : H⁰(G, P) → H¹(G, M)` is the usual one: for `p ∈ P^G` choose a lift
`n ∈ N` of `p` and send `p` to the class of the continuous cocycle `g ↦ g • n - n`, whose values
lie in `ker π = im ι ≅ M`.  Its existence and exactness are
`Work.AbsoluteKummer.SES.exists_connecting_exact`; the exactness at `H⁰(N)` and at `H¹(N)` are
`Work.AbsoluteKummer.SES.range_mapH0_eq_ker_mapH0` and
`Work.AbsoluteKummer.SES.range_mapH1_eq_ker_mapH1`.
-/
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.AbsoluteKummer.Basic
import Submission.Work.GroupCohomology.ShortExact
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w

namespace Work.AbsoluteKummer

open scoped Classical

noncomputable section

variable (G : Type u) [TopologicalSpace G] [Group G]

/-- A short exact sequence `0 → M → N → P → 0` of discrete `G`-modules: equivariant additive maps
`ι : M →+ N`, `π : N →+ P` with `ι` injective, `π` surjective, `range ι = ker π`, and all three
coefficients discrete. -/
structure ShortExactSeq (M : Type v) (N : Type v) (P : Type v) [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup P] [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P] where
  /-- the inclusion `M → N` -/
  iota : M →+ N
  /-- the projection `N → P` -/
  pi : N →+ P
  iota_equivariant : Work.GroupCohomology.IsEquivariant G iota
  pi_equivariant : Work.GroupCohomology.IsEquivariant G pi
  iota_injective : Function.Injective iota
  pi_surjective : Function.Surjective pi
  range_iota_eq_ker_pi : iota.range = pi.ker
  isDiscreteM : IsDiscreteModule G M
  isDiscreteN : IsDiscreteModule G N
  isDiscreteP : IsDiscreteModule G P

namespace ShortExactSeq

variable {G} {M N P : Type v} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]

variable (S : ShortExactSeq G M N P)

theorem pi_iota (a : M) : S.pi (S.iota a) = 0 := by
  rw [← AddMonoidHom.mem_ker, ← S.range_iota_eq_ker_pi]
  exact AddMonoidHom.mem_range.mpr ⟨a, rfl⟩

theorem pi_comp_iota : S.pi.comp S.iota = 0 := by
  ext a
  exact S.pi_iota a

/-- The composite of the two maps on `H¹` is zero. -/
theorem mapH1_comp_eq_zero (x : H1 G M) :
    mapH1 S.pi S.pi_equivariant (mapH1 S.iota S.iota_equivariant x) = 0 := by
  obtain ⟨f, hf⟩ := QuotientAddGroup.mk'_surjective ((B1 G M).comap (Z1 G M).subtype) x
  rw [show x = H1π G M f from hf.symm, mapH1_H1π, mapH1_H1π, H1π_eq_zero_iff]
  refine ⟨0, ?_⟩
  have h : mapZ1 S.pi S.pi_equivariant (mapZ1 S.iota S.iota_equivariant f) = 0 := by
    ext g
    rw [mapZ1_apply, mapZ1_apply, S.pi_iota]
    rfl
  rw [h, map_zero]
  rfl

/-- The image of `H¹(M)` lies in the kernel of the map induced by `π`. -/
theorem mapH1_iota_range_le_ker_pi :
    (mapH1 S.iota S.iota_equivariant).range ≤ (mapH1 S.pi S.pi_equivariant).ker := by
  rintro y ⟨x, rfl⟩
  rw [AddMonoidHom.mem_ker]
  exact S.mapH1_comp_eq_zero x

end ShortExactSeq

end

end Work.AbsoluteKummer
