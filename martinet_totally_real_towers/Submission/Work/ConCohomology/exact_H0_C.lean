/-
Copyright: the martinet_totally_real_towers team.

# Exactness of the long exact sequence at `H⁰(G,C)`

For a short exact sequence `0 → A → B → C → 0` of discrete `G`-modules the connecting map
`δ⁰ : H⁰(G,C) ⟶ H¹(G,A)` has kernel equal to the image of `H⁰(G,B) → H⁰(G,C)`:

  `connecting0 S c = 0 ↔ ∃ b : H0 G B, H0Map S.g b = c`.

The two inclusions are proved on representatives.

* If `δ⁰ c = 0` then the raw cocycle `S.delta0Fun c` is a coboundary, say
  `S.delta0Fun c σ = σ • a - a`.  The element `b = S.sect c - S.f a` is then `G`-invariant
  (because `S.f (σ • a - a) = σ • S.sect c - S.sect c`) and maps to `c` under `S.g`.

* Conversely, if `b ∈ H⁰(G,B)` has `S.g b = c`, the element `a = S.invFun (S.sect c - b)`
  satisfies `σ • a - a = S.delta0Fun c σ`, so `S.delta0Fun c` is the coboundary of `a`.

Both arguments use only that `S.f` is injective (to identify `S.invFun` of an element of the
image) and the exactness of `S` at `B` (to know that `σ • S.sect c - S.sect c` and
`S.sect c - b` lie in the image of `S.f`).
-/

import Mathlib
import Submission.Work.ConCohomology.Connecting

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function

lemma exact_H0_C {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]
    [IsDiscreteGModule G A] [IsDiscreteGModule G B] [IsDiscreteGModule G C]
    (S : CoeffSES G A B C) (c : H0 G C) :
    connecting0 S c = 0 ↔ ∃ b : H0 G B, H0Map S.g b = c := by
  constructor
  · -- `δ⁰ c = 0` means that `S.delta0Fun c` is a coboundary `σ ↦ σ • a - a`.
    intro h
    rw [connecting0_apply, H1.mk_eq_zero_iff, mem_B1', mem_B1] at h
    obtain ⟨a, ha⟩ := h
    have hfun : ∀ σ : G, σ • a - a = S.invFun (σ • S.sect (c : C) - S.sect (c : C)) := by
      intro σ
      have h1 := congrFun (congrArg (fun f : Cochain1 G A => (f : G → A)) ha) σ
      simp only [d0Hom_apply, delta0Cocycle_coe, LocallyConstant.coe_mk] at h1
      exact h1
    -- `S.g (S.f a) = 0`.
    have hga : S.g (S.f a) = 0 := (S.exact (S.f a)).mpr ⟨a, rfl⟩
    -- `σ • S.sect c - S.sect c` lies in the image of `S.f`, as `c` is invariant.
    have him : ∀ σ : G, ∃ a' : A, S.f a' = σ • S.sect (c:C) - S.sect (c:C) := by
      intro σ
      apply exists_f_eq_of_g_eq_zero
      rw [EqHom.map_sub, EqHom.map_smul, CoeffSES.g_sect, c.2 σ, sub_self]
    -- Hence the element `S.sect c - S.f a` is invariant.
    have hb2 : ∀ σ : G, σ • (S.sect (c:C) - S.f a) = S.sect (c:C) - S.f a := by
      intro σ
      have h1 : S.f (σ • a - a) = σ • S.sect (c:C) - S.sect (c:C) := by
        rw [hfun σ]
        exact f_invFun_eq_self S (him σ)
      have h2 : S.f (σ • a) = S.f a + (σ • S.sect (c:C) - S.sect (c:C)) := by
        rw [EqHom.map_sub] at h1
        exact (sub_eq_iff_eq_add').mp h1
      rw [smul_sub, ← S.f.map_smul σ a, h2]
      abel
    refine ⟨⟨S.sect (c:C) - S.f a, ?_⟩, ?_⟩
    · rw [mem_fixedPoints]; exact hb2
    · apply Subtype.ext
      rw [H0Map_coe, EqHom.map_sub, CoeffSES.g_sect, hga, sub_zero]
  · -- Conversely, an invariant lift `b` of `c` produces a coboundary `a` with `d⁰ a = delta0Fun c`.
    rintro ⟨b, hb⟩
    have hgb : S.g (b : B) = (c : C) := by
      have h1 := congrArg (fun x : H0 G C => (x : C)) hb
      simpa [H0Map_coe] using h1
    set a : A := S.invFun (S.sect (c:C) - (b:B)) with ha_def
    have hfa : S.f a = S.sect (c:C) - (b:B) := by
      rw [ha_def]
      apply f_invFun_eq_self
      apply exists_f_eq_of_g_eq_zero
      rw [EqHom.map_sub, CoeffSES.g_sect, hgb, sub_self]
    have hfun : ∀ σ : G, d0Fun (G := G) a σ = S.delta0Fun (c:C) σ := by
      intro σ
      rw [d0Fun_apply, CoeffSES.delta0Fun_apply]
      have h1 : S.f (σ • a - a) = σ • S.sect (c:C) - S.sect (c:C) := by
        rw [EqHom.map_sub, S.f.map_smul σ a, hfa, smul_sub, b.2 σ]
        abel
      exact (invFun_eq_of_apply_eq S h1).symm
    have hd0 : d0Hom G A a = (delta0Cocycle S c : Cochain1 G A) := by
      refine LocallyConstant.ext fun σ => ?_
      simpa [d0Hom_apply, delta0Cocycle_coe] using hfun σ
    rw [connecting0_apply, H1.mk_eq_zero_iff, mem_B1', mem_B1]
    exact ⟨a, hd0⟩

end Work.ConCohomology
