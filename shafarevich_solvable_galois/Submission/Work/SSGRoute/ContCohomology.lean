import Mathlib
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The locally-constant (continuous) cochain complex

`Submission.Work.SSGRoute.Interfaces` defines conditions for a cochain on a profinite group `Γ`
(values in a discrete `G`-module `M`, the action of `Γ` on `M` through `act : Γ →* G`):
`IsCocycleOn`/`IsLocConstOn`/`IsCoboundaryOn` in degree `1`, and
`IsCocycle2`/`IsLocConst2`/`IsCoboundary2On` in degree `2`.

This file packages them into the actual complexes, so that the continuous cohomology can be named
and mapped into: `Z1cont`, `B1cont`, `H1cont` and `Z2cont`, `B2cont`, `H2cont`.

The `2`-cocycle condition is imposed on all of `Γ × Γ`, while the coboundaries are coboundaries
*on the subgroup* `H` (the "classes trivialised on `H`" model of the local cohomology at a place,
matching `IsCoboundary2On`).  These are the objects in which PT-1a (local invariant
`H²(D_A, Z/p) ≅ Z/p`), the local Tate pairing, reciprocity and the 9-term criterion are stated.
-/

namespace Work.SSGRoute

open scoped Pointwise

section Cont

/-! ## Degree `1` -/

/-- Locally constant `1`-cocycles on `H`. -/
def Z1cont (Γ G M : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] (act : Γ →* G) (H : Subgroup Γ) : AddSubgroup (Γ → M) where
  carrier := {f | SSGRoute.IsCocycleOn act H f ∧ SSGRoute.IsLocConstOn H f}
  zero_mem' := ⟨fun g _ h _ => by simp, ⟨⊤, isOpen_univ, fun g _ u _ _ => rfl⟩⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    refine ⟨fun a ha b hb => ?_, ?_⟩
    · show f (a * b) + g (a * b) = f a + g a + act a • (f b + g b)
      rw [hf1 a ha b hb, hg1 a ha b hb, smul_add]
      abel
    · obtain ⟨U, hU, hUc⟩ := hf2
      obtain ⟨V, hV, hVc⟩ := hg2
      refine ⟨U ⊓ V, hU.inter hV, fun x hx u hu huH => ?_⟩
      show f (x * u) + g (x * u) = f x + g x
      rw [hUc x hx u hu.1 huH, hVc x hx u hu.2 huH]
  neg_mem' := by
    rintro f ⟨hf1, hf2⟩
    refine ⟨fun a ha b hb => ?_, ?_⟩
    · show -(f (a * b)) = - f a + act a • (-(f b))
      rw [hf1 a ha b hb, smul_neg]
      abel
    · obtain ⟨U, hU, hUc⟩ := hf2
      refine ⟨U, hU, fun x hx u hu huH => ?_⟩
      show -(f (x * u)) = -(f x)
      rw [hUc x hx u hu huH]

/-- `1`-coboundaries on `H`. -/
def B1cont (Γ G M : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] (act : Γ →* G) (H : Subgroup Γ) : AddSubgroup (Γ → M) where
  carrier := {f | SSGRoute.IsCoboundaryOn act H f}
  zero_mem' := ⟨0, fun g _ => by simp⟩
  add_mem' := by
    rintro f g ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, fun x hx => ?_⟩
    show f x + g x = act x • (m + n) - (m + n)
    rw [hm x hx, hn x hx, smul_add]
    abel
  neg_mem' := by
    rintro f ⟨m, hm⟩
    refine ⟨-m, fun x hx => ?_⟩
    show -(f x) = act x • (-m) - (-m)
    rw [hm x hx, smul_neg]
    abel

/-- The continuous first cohomology on `H`. -/
abbrev H1cont (Γ G M : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] (act : Γ →* G) (H : Subgroup Γ) : Type _ :=
  ↥(Z1cont Γ G M act H) ⧸ ((B1cont Γ G M act H).comap (Z1cont Γ G M act H).subtype)

/-! ## Degree `2` -/

/-- Locally constant `2`-cocycles. -/
def Z2cont (Γ G M : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] (act : Γ →* G) : AddSubgroup (Γ → Γ → M) where
  carrier := {c | SSGRoute.IsCocycle2 act c ∧ SSGRoute.IsLocConst2 c}
  zero_mem' := ⟨fun g h l => by simp, ⟨⊤, isOpen_univ, fun g h u v _ _ => rfl⟩⟩
  add_mem' := by
    rintro c d ⟨hc1, hc2⟩ ⟨hd1, hd2⟩
    refine ⟨?_, ?_⟩
    · intro g h l
      have h1 := hc1 g h l
      have h2 := hd1 g h l
      show act g • (c h l + d h l) - (c (g * h) l + d (g * h) l)
            + (c g (h * l) + d g (h * l)) - (c g h + d g h) = 0
      have key : act g • (c h l + d h l) - (c (g * h) l + d (g * h) l)
            + (c g (h * l) + d g (h * l)) - (c g h + d g h)
          = (act g • c h l - c (g * h) l + c g (h * l) - c g h)
            + (act g • d h l - d (g * h) l + d g (h * l) - d g h) := by
        rw [smul_add]; abel
      rw [key, h1, h2, add_zero]
    · obtain ⟨U, hU, hUc⟩ := hc2
      obtain ⟨V, hV, hVd⟩ := hd2
      refine ⟨U ⊓ V, hU.inter hV, fun g h u v hu hv => ?_⟩
      show c (g * u) (h * v) + d (g * u) (h * v) = c g h + d g h
      rw [hUc g h u v hu.1 hv.1, hVd g h u v hu.2 hv.2]
  neg_mem' := by
    rintro c ⟨hc1, hc2⟩
    refine ⟨?_, ?_⟩
    · intro g h l
      have h1 := hc1 g h l
      show act g • (-(c h l)) - (-(c (g * h) l)) + (-(c g (h * l))) - (-(c g h)) = 0
      have key : act g • (-(c h l)) - (-(c (g * h) l)) + (-(c g (h * l))) - (-(c g h))
          = -(act g • c h l - c (g * h) l + c g (h * l) - c g h) := by
        rw [smul_neg]; abel
      rw [key, h1, neg_zero]
    · obtain ⟨U, hU, hUc⟩ := hc2
      refine ⟨U, hU, fun g h u v hu hv => ?_⟩
      show -(c (g * u) (h * v)) = -(c g h)
      rw [hUc g h u v hu hv]

/-- `2`-coboundaries on `H`. -/
def B2cont (Γ G M : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] (act : Γ →* G) (H : Subgroup Γ) : AddSubgroup (Γ → Γ → M) where
  carrier := {c | SSGRoute.IsCoboundary2On act H c}
  zero_mem' := ⟨0, ⟨⊤, isOpen_univ, fun g _ u _ _ => rfl⟩, fun g _ h _ => by simp⟩
  add_mem' := by
    rintro c d ⟨b, hb, hbc⟩ ⟨b', hb', hb'c⟩
    refine ⟨b + b', ?_, fun g hg h hh => ?_⟩
    · obtain ⟨U, hU, hUc⟩ := hb
      obtain ⟨V, hV, hVc⟩ := hb'
      refine ⟨U ⊓ V, hU.inter hV, fun x hx u hu huH => ?_⟩
      show b (x * u) + b' (x * u) = b x + b' x
      rw [hUc x hx u hu.1 huH, hVc x hx u hu.2 huH]
    · show c g h + d g h = act g • (b h + b' h) - (b (g * h) + b' (g * h)) + (b g + b' g)
      rw [hbc g hg h hh, hb'c g hg h hh, smul_add]
      abel
  neg_mem' := by
    rintro c ⟨b, hb, hbc⟩
    refine ⟨-b, ?_, fun g hg h hh => ?_⟩
    · obtain ⟨U, hU, hUc⟩ := hb
      refine ⟨U, hU, fun x hx u hu huH => ?_⟩
      show -(b (x * u)) = -(b x)
      rw [hUc x hx u hu huH]
    · show -(c g h) = act g • (-(b h)) - (-(b (g * h))) + (-(b g))
      rw [hbc g hg h hh, smul_neg]
      abel

/-- The continuous second cohomology on `H`. -/
abbrev H2cont (Γ G M : Type) [Group Γ] [TopologicalSpace Γ] [Group G] [AddCommGroup M]
    [DistribMulAction G M] (act : Γ →* G) (H : Subgroup Γ) : Type _ :=
  ↥(Z2cont Γ G M act) ⧸ ((B2cont Γ G M act H).comap (Z2cont Γ G M act).subtype)

end Cont

end Work.SSGRoute
