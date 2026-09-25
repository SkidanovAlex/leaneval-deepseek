/-
Copyright: the martinet_totally_real_towers team.

# Exactness of the long exact sequence in degree `1`: the `A`-term

Let `0 → A → B → C → 0` be a short exact sequence `S` of discrete `G`-modules and let
`δ⁰ : H⁰(G,C) → H¹(G,A)` be the connecting map of `Connecting.lean`.  This module proves
exactness at `H¹(G,A)`:

  `H¹Map S.f x = 0 ↔ ∃ c : H⁰(G,C), connecting0 S c = x`,

i.e. the image of `δ⁰` is the kernel of the coefficient-change map induced by the inclusion
`S.f : A → B`.

Both inclusions are the usual diagram chase, carried out on the level of *locally constant*
cochains:

* if `x = δ⁰ c`, then `S.f (δ⁰c σ) = S.f (S.invFun (σ • S.sect c - S.sect c))
  = σ • S.sect c - S.sect c` (`f` inverts `invFun` on its image), so `δ⁰c` is taken to a
  coboundary by `S.f`;

* conversely, if `z` is a `1`-cocycle in `A` whose image under `S.f` is a coboundary, say
  `σ • b - b = S.f (z σ)` for some `b : B`, then `c := S.g b` is `G`-invariant (apply `S.g` to
  the previous identity and use exactness), and the difference between `b` and a chosen section
  `S.sect c` is `S.f a` for some `a : A`.  Substituting `S.sect c = b + S.f a` into the definition
  of `δ⁰c` shows `S.delta0Fun c σ = z σ + (σ • a - a)`, so `δ⁰c` differs from `z` by the
  coboundary `d⁰a`: its class in `H¹` is `x`.
-/

import Mathlib
import Submission.Work.ConCohomology.Connecting

namespace Work.ConCohomology

lemma exact_H1_A {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]
    (S : CoeffSES G A B C) (x : H1 G A) :
    H1Map S.f x = 0 ↔ ∃ c : H0 G C, connecting0 S c = x := by
  constructor
  · intro hx
    revert hx
    refine QuotientAddGroup.induction_on x ?_
    intro z hz
    change H1Map S.f (H1.mk z) = 0 at hz
    change ∃ c : H0 G C, connecting0 S c = H1.mk z
    have hz1 : H1.mk (Z1Map S.f z) = 0 := by
      rw [← H1Map_mk S.f z]
      exact hz
    rw [H1.mk_eq_zero_iff, mem_B1'] at hz1
    obtain ⟨b, hb⟩ := mem_B1.mp hz1
    -- `hb` says that the `B`-valued cochain `σ ↦ σ • b - b` is the image under `S.f` of `z`.
    have hb' : ∀ σ : G, σ • b - b = S.f (((z : Z1 G A) : Cochain1 G A) σ) := by
      intro σ
      have h := DFunLike.congr_fun hb σ
      simpa only [d0Hom_apply, Z1Map_coe, cochain1Map_apply] using h
    -- `c := S.g b` is `G`-invariant.
    have hc : ∀ σ : G, σ • S.g b = S.g b := by
      intro σ
      have h1 : S.g (σ • b - b) = 0 := by
        rw [hb' σ]
        exact (S.exact _).mpr ⟨_, rfl⟩
      rw [EqHom.map_sub, EqHom.map_smul] at h1
      exact sub_eq_zero.mp h1
    refine ⟨⟨S.g b, hc⟩, ?_⟩
    rw [connecting0_apply, H1.mk_eq_mk_iff, mem_B1']
    -- `S.sect c - b` has vanishing `g`-image, hence is `S.f a` for some `a : A`.
    have hsect0 : S.g (S.sect (S.g b) - b) = 0 := by
      rw [EqHom.map_sub, CoeffSES.g_sect, sub_self]
    obtain ⟨a, ha⟩ := (S.exact _).mp hsect0
    refine ⟨a, ?_⟩
    ext σ
    show σ • a - a
      = S.invFun (σ • S.sect (S.g b) - S.sect (S.g b))
        - (((z : Z1 G A) : Cochain1 G A) σ)
    have hsect : S.sect (S.g b) = b + S.f a := by
      rw [← sub_add_cancel (S.sect (S.g b)) b, ha, add_comm]
    have harg : σ • S.sect (S.g b) - S.sect (S.g b)
        = S.f (((z : Z1 G A) : Cochain1 G A) σ + (σ • a - a)) := by
      have hsplit : σ • S.sect (S.g b) - S.sect (S.g b)
          = (σ • b - b) + (σ • (S.f a) - S.f a) := by
        rw [hsect, smul_add]
        abel
      rw [hsplit, hb' σ, EqHom.map_add, EqHom.map_sub, EqHom.map_smul]
    have hinv : S.invFun (σ • S.sect (S.g b) - S.sect (S.g b))
        = ((z : Z1 G A) : Cochain1 G A) σ + (σ • a - a) :=
      invFun_eq_of_apply_eq S harg.symm
    rw [hinv]
    abel
  · rintro ⟨c, rfl⟩
    rw [connecting0_apply, H1Map_mk, H1.mk_eq_zero_iff, mem_B1']
    refine ⟨S.sect (c : C), ?_⟩
    ext σ
    rw [Z1Map_coe]
    change σ • S.sect (c : C) - S.sect (c : C) = S.f (S.delta0Fun (c : C) σ)
    rw [CoeffSES.delta0Fun_apply]
    have hg : S.g (σ • S.sect (c : C) - S.sect (c : C)) = 0 := by
      rw [EqHom.map_sub, EqHom.map_smul, CoeffSES.g_sect, c.2 σ, sub_self]
    rw [f_invFun_eq_self S (b := σ • S.sect (c : C) - S.sect (c : C)) ((S.exact _).mp hg)]

end Work.ConCohomology
