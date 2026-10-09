import Mathlib
import Submission.Work.SSGRoute.ContCohomology
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `ZMod p`-scalar multiplication preserves the locally-constant cochain groups

The continuous (locally-constant) `1`- and `2`-cochain groups `Z1cont`, `B1cont`, `Z2cont`,
`B2cont` of `Submission.Work.SSGRoute.ContCohomology` are additive subgroups of the function
spaces `Γ → M` and `Γ → Γ → M`.  They are in fact closed under multiplication by scalars of
`ZMod p`, because the module structure of `M` over `ZMod p` commutes with the `G`-action
(instance `SMulCommClass G (ZMod p) M`) and the pointwise `ZMod p`-action on a function space
preserves the defining algebraic and topological conditions:

* `IsCocycleOn`, `IsCoboundaryOn`, `IsCocycle2`, `IsCoboundary2On` are algebraic conditions,
  preserved by multiplication with a scalar on a `ZMod p`-module commuting with the action;
* `IsLocConstOn`, `IsLocConst2` are purely topological (locally constant), so scalar
  multiplication changes nothing.

This is the fact needed to regard the cohomology `H1cont`/`H2cont` as `ZMod p`-vector spaces.
-/

open _root_.SSGRoute

namespace Work.SSGRoute.PT

open Work.SSGRoute

variable {p : ℕ} {Γ G M : Type} [Group Γ] [TopologicalSpace Γ] [Group G]
  [AddCommGroup M] [DistribMulAction G M] [Module (ZMod p) M] [SMulCommClass G (ZMod p) M]

omit [TopologicalSpace Γ] in
/-- `IsCocycleOn` is preserved by `ZMod p`-scalar multiplication. -/
lemma isCocycleOn_smul (act : Γ →* G) {H : Subgroup Γ} {f : Γ → M} (r : ZMod p)
    (hf : IsCocycleOn act H f) : IsCocycleOn act H (r • f) := by
  intro g hg h hh
  show r • f (g * h) = r • f g + act g • (r • f h)
  rw [hf g hg h hh, smul_add, smul_comm (act g) r (f h)]

/-- `IsLocConstOn` is preserved by `ZMod p`-scalar multiplication. -/
lemma isLocConstOn_smul {H : Subgroup Γ} {f : Γ → M} (r : ZMod p)
    (hf : IsLocConstOn H f) : IsLocConstOn H (r • f) := by
  obtain ⟨U, hU, hUc⟩ := hf
  exact ⟨U, hU, fun g hg u hu huH => by
    show r • f (g * u) = r • f g
    rw [hUc g hg u hu huH]⟩

omit [TopologicalSpace Γ] in
/-- `IsCoboundaryOn` is preserved by `ZMod p`-scalar multiplication. -/
lemma isCoboundaryOn_smul (act : Γ →* G) {H : Subgroup Γ} {f : Γ → M} (r : ZMod p)
    (hf : IsCoboundaryOn act H f) : IsCoboundaryOn act H (r • f) := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨r • m, fun g hg => ?_⟩
  show r • f g = act g • (r • m) - r • m
  rw [hm g hg, smul_sub, smul_comm (act g) r m]

omit [TopologicalSpace Γ] in
/-- `IsCocycle2` is preserved by `ZMod p`-scalar multiplication. -/
lemma isCocycle2_smul (act : Γ →* G) {c : Γ → Γ → M} (r : ZMod p)
    (hc : IsCocycle2 act c) : IsCocycle2 act (r • c) := by
  intro g h l
  have key : act g • (r • c h l) - r • c (g * h) l + r • c g (h * l) - r • c g h
      = r • (act g • c h l - c (g * h) l + c g (h * l) - c g h) := by
    rw [smul_comm (act g) r (c h l), smul_sub, smul_add, smul_sub]
  change act g • (r • c h l) - r • c (g * h) l + r • c g (h * l) - r • c g h = 0
  rw [key, hc g h l, smul_zero]

/-- `IsLocConst2` is preserved by `ZMod p`-scalar multiplication. -/
lemma isLocConst2_smul {c : Γ → Γ → M} (r : ZMod p)
    (hc : IsLocConst2 c) : IsLocConst2 (r • c) := by
  obtain ⟨U, hU, hUc⟩ := hc
  exact ⟨U, hU, fun g h u v hu hv => by
    show r • c (g * u) (h * v) = r • c g h
    rw [hUc g h u v hu hv]⟩

/-- `IsCoboundary2On` is preserved by `ZMod p`-scalar multiplication. -/
lemma isCoboundary2On_smul (act : Γ →* G) {H : Subgroup Γ} {c : Γ → Γ → M} (r : ZMod p)
    (hc : IsCoboundary2On act H c) : IsCoboundary2On act H (r • c) := by
  obtain ⟨b, hb, hbc⟩ := hc
  refine ⟨r • b, ?_, fun g hg h hh => ?_⟩
  · obtain ⟨U, hU, hUc⟩ := hb
    exact ⟨U, hU, fun x hx u hu huH => by
      show r • b (x * u) = r • b x
      rw [hUc x hx u hu huH]⟩
  · have key : act g • (r • b h) - r • b (g * h) + r • b g
        = r • (act g • b h - b (g * h) + b g) := by
      rw [smul_comm (act g) r (b h), smul_add, smul_sub]
    change r • c g h = act g • (r • b h) - r • b (g * h) + r • b g
    rw [hbc g hg h hh, key]

/-- The locally-constant cochain groups `Z1cont`, `B1cont`, `Z2cont`, `B2cont` are stable under
multiplication by scalars of `ZMod p`; equivalently the continuous cohomology `H1cont`/`H2cont`
carries a `ZMod p`-vector space structure commuting with the cohomology operations. -/
theorem contSmulMem
    (p : ℕ) [Fact p.Prime] (Γ G M : Type) [Group Γ] [TopologicalSpace Γ] [Group G]
    [AddCommGroup M] [DistribMulAction G M] [Module (ZMod p) M] [SMulCommClass G (ZMod p) M]
    (act : Γ →* G) (H : Subgroup Γ) (r : ZMod p) :
    (∀ f : Γ → M, f ∈ Work.SSGRoute.Z1cont Γ G M act H → r • f ∈ Work.SSGRoute.Z1cont Γ G M act H) ∧
    (∀ f : Γ → M, f ∈ Work.SSGRoute.B1cont Γ G M act H → r • f ∈ Work.SSGRoute.B1cont Γ G M act H) ∧
    (∀ f : Γ → Γ → M, f ∈ Work.SSGRoute.Z2cont Γ G M act → r • f ∈ Work.SSGRoute.Z2cont Γ G M act) ∧
    (∀ f : Γ → Γ → M, f ∈ Work.SSGRoute.B2cont Γ G M act H → r • f ∈ Work.SSGRoute.B2cont Γ G M act H) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f hf
    exact ⟨isCocycleOn_smul act r hf.1, isLocConstOn_smul r hf.2⟩
  · intro f hf
    exact isCoboundaryOn_smul act r hf
  · intro f hf
    exact ⟨isCocycle2_smul act r hf.1, isLocConst2_smul r hf.2⟩
  · intro f hf
    exact isCoboundary2On_smul act r hf

end Work.SSGRoute.PT
