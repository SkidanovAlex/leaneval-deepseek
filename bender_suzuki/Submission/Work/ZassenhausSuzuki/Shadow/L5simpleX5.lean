import Submission.Work.ZassenhausSuzuki.SzSetting
import Mathlib
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ZassenhausSuzuki.Shadow.L5Struct
import Submission.Work.ZassenhausSuzuki.Shadow.X5RankOneAux
import Submission.Work.ZassenhausSuzuki.Shadow.X5_eq_sup_conj_Q0sub

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.Shadow.ChV12.L5simpleX5` — `X = ⟨Q₀, K, t⟩` is simple (Ch. V §2 Lemma 5)

The target of this file is `Work.ZassenhausSuzuki.Shadow.ChV12.L5simpleX5 : IsSimpleGroup ↥(X5 H t)` for
`Work.ZassenhausSuzuki.SzHyp` data.  The proof is the Iwasawa/Bender argument in the form used by the source: `X5`
acts 2-transitively on `X5 ⧸ B` (where `B = bor H t = Q0sub H ⊔ Ksub H t`), the point
stabiliser `B` has the abelian normal subgroup `U = Q0sub H` which acts sharply transitively on
the other points, the conjugates of `U` generate `X5` (here `X5 = U ⊔ U^t`), and the action is
faithful (the core of `B` is trivial).  Simplicity then follows by the dichotomy: for
`N ⊴ X5`, either `N ≤ B` (then `N = ⊥` by faithfulness) or `N` acts non-trivially, hence
transitively on the cosets, and then `X5 = N ⊔ U` with `U` abelian, so `⁅X5,X5⁆ ≤ N`;
`X5` is perfect, so `N = X5`.

The auxiliary facts `X5 = Q0sub H ⊔ conj t (Q0sub H)` and the 2-transitivity of the action are
proved in the sibling modules `X5_eq_sup_conj_Q0sub` and `L5twoTransitive` of this directory.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open scoped Pointwise commutatorElement

open LeanEval.GroupTheory.Defs

namespace Work.ZassenhausSuzuki.Shadow.ChV12
open Submission.Blueprint

open Work.ThmF.ChV12
/-- Membership transfer into a conjugate subgroup. -/
theorem mem_conj_mem {G : Type} [Group G] {A : Subgroup G} {g x : G} (hx : x ∈ A) :
    g * x * g⁻¹ ∈ Submission.Blueprint.conj g A :=
  Subgroup.mem_map.mpr ⟨x, hx, MulAut.conj_apply g x⟩

/-- Membership transfer out of a conjugate subgroup. -/
theorem mem_of_mem_conj {G : Type} [Group G] {A : Subgroup G} {g x : G}
    (hx : g * x * g⁻¹ ∈ Submission.Blueprint.conj g A) : x ∈ A := by
  rw [Work.Models.mem_conj_iff] at hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at hx

/-- **Faithfulness of the action of `X5` on the cosets of `B = Q0sub ⊔ Ksub H t`.**

If `N ≤ B` is invariant under conjugation by `X5`, then `N = ⊥`:
`N ≤ B ⊓ B^t = Ksub`, and `[N, Q0sub] ≤ N ⊓ Q0sub ≤ Ksub ⊓ Q0sub = ⊥`, so `N` centralises
`X5 = Q0sub ⊔ conj t (Q0sub)`; for `1 ≠ z ∈ N` the `ChIIFourProp` clause P3 applied to
`⟨z⟩ ≤ V = C_D(t)` (with any `1 ≠ k ∈ Kset` normalising `⟨z⟩`) shows that `Kset` is a
subgroup, whence `z ∈ Ksub = Kset`; but `z` centralises `Q0sub ∋ s` and `Kset` acts regularly
on `Inv H`, so `z = 1`. -/
theorem eq_bot_of_le_bor_of_normal {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (h : Work.ZassenhausSuzuki.SzHyp H Q t s)
    (hA : Work.ThmF.Lemma5.X5 H t =
      Work.ThmF.Q0sub H ⊔ Submission.Blueprint.conj t (Work.ThmF.Q0sub H))
    {N : Subgroup G} (hNB : N ≤ Work.ZassenhausSuzuki.Shadow.L5.bor H t)
    (hNn : ∀ g ∈ Work.ThmF.Lemma5.X5 H t, Submission.Blueprint.conj g N = N) :
    N = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  by_contra hz1
  have htX : t ∈ Work.ThmF.Lemma5.X5 H t := Work.ThmF.Lemma5.t_mem_X5 H t
  have hsplit : Submission.Blueprint.IsSplitRankOne H Q t := h.split
  -- membership transfer through the conjugation-invariance of `N`
  have hconj : ∀ {g : G}, g ∈ Work.ThmF.Lemma5.X5 H t → ∀ {x : G}, x ∈ N → g * x * g⁻¹ ∈ N := by
    intro g hg x hx
    have h1 := hNn g hg
    rw [← h1]
    exact mem_conj_mem hx
  -- elementary facts about `Q0sub`
  have hQcomm := Work.ZassenhausSuzuki.SzHyp.hcomm h
  have hQel := Work.ThmF.L5.Q0sub_elementary hQcomm
  have hQinv : ∀ u ∈ Work.ThmF.Q0sub H, u⁻¹ = u := fun u hu =>
    inv_eq_of_mul_eq_one_right (hQel.1 u hu)
  have hQinv2 : ∀ u ∈ Work.ThmF.Q0sub H, u * u = 1 := hQel.1
  have hQX : ∀ u ∈ Work.ThmF.Q0sub H, u ∈ Work.ThmF.Lemma5.X5 H t :=
    fun u hu => Work.ZassenhausSuzuki.Shadow.L5.Q0sub_le_X5 hu
  -- ## Step 1: `N ≤ Ksub`
  have hNK : N ≤ Work.ThmF.Ksub H t := by
    intro n hn
    have hnt : t⁻¹ * n * t ∈ N := by
      simpa using hconj (inv_mem htX) hn
    have hmem : n ∈ Work.ZassenhausSuzuki.Shadow.L5.bor H t ⊓ Submission.Blueprint.conj t (Work.ZassenhausSuzuki.Shadow.L5.bor H t) := by
      refine Subgroup.mem_inf.mpr ⟨hNB hn, ?_⟩
      change n ∈ Subgroup.map (MulAut.conj t).toMonoidHom (Work.ZassenhausSuzuki.Shadow.L5.bor H t)
      rw [Subgroup.mem_map]
      exact ⟨t⁻¹ * n * t, hNB hnt,
        by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    rwa [Work.ZassenhausSuzuki.Shadow.L5.twoPoint_bor_eq_Ksub h] at hmem
  -- ## Step 2: `[N, Q0sub] = 1`
  have hcommQ : ∀ n ∈ N, ∀ u ∈ Work.ThmF.Q0sub H, n * u = u * n := by
    intro n hn u hu
    have huX : u ∈ Work.ThmF.Lemma5.X5 H t := hQX u hu
    have hle := Work.ZassenhausSuzuki.Shadow.L5.Ksub_le_normalizer_Q0sub h (hNK hn)
    have hnunQ : n * u * n⁻¹ ∈ Work.ThmF.Q0sub H :=
      (Subgroup.mem_normalizer_iff.mp hle u).mp hu
    have hunN : u * n * u⁻¹ ∈ N := hconj huX hn
    have hmemN : n * u * n⁻¹ * u⁻¹ ∈ N := by
      have h1 : n * u * n⁻¹ * u⁻¹ = n * (u * n * u⁻¹)⁻¹ := by group
      rw [h1]
      exact N.mul_mem hn (N.inv_mem hunN)
    have hmemK : n * u * n⁻¹ * u⁻¹ ∈ Work.ThmF.Ksub H t := hNK hmemN
    have hmemQ : n * u * n⁻¹ * u⁻¹ ∈ Work.ThmF.Q0sub H :=
      (Work.ThmF.Q0sub H).mul_mem hnunQ ((Work.ThmF.Q0sub H).inv_mem hu)
    have hbot : n * u * n⁻¹ * u⁻¹ ∈ (⊥ : Subgroup G) := by
      have h2 : n * u * n⁻¹ * u⁻¹ ∈ Work.ThmF.Q0sub H ⊓ Work.ThmF.Ksub H t :=
        Subgroup.mem_inf.mpr ⟨hmemQ, hmemK⟩
      rwa [Work.ZassenhausSuzuki.Shadow.L5.Q0sub_inf_Ksub_eq_bot h] at h2
    have hc : n * u * n⁻¹ * u⁻¹ = 1 := Subgroup.mem_bot.mp hbot
    have h4 : n * u * n⁻¹ = u := by
      have h5 := congrArg (fun y => y * u) hc
      simpa [mul_assoc] using h5
    calc n * u = (n * u * n⁻¹) * n := by group
      _ = u * n := by rw [h4]
  -- ## Step 3: `N` centralises `X5`
  have hconjQ : ∀ n ∈ N, ∀ x ∈ Work.ThmF.Lemma5.X5 H t, ∀ u ∈ Work.ThmF.Q0sub H,
      n * (x * u * x⁻¹) = (x * u * x⁻¹) * n := by
    intro n hn x hx u hu
    have hxN : x⁻¹ * n * x ∈ N := by
      simpa using hconj (inv_mem hx) hn
    have h' : (x⁻¹ * n * x) * u = u * (x⁻¹ * n * x) := hcommQ _ hxN u hu
    have h2 : x⁻¹ * (n * (x * u * x⁻¹)) * x = x⁻¹ * ((x * u * x⁻¹) * n) * x := by
      calc x⁻¹ * (n * (x * u * x⁻¹)) * x = (x⁻¹ * n * x) * u := by group
        _ = u * (x⁻¹ * n * x) := h'
        _ = x⁻¹ * ((x * u * x⁻¹) * n) * x := by group
    exact mul_left_cancel (mul_right_cancel h2)
  have hZ : ∀ n ∈ N, ∀ x ∈ Work.ThmF.Lemma5.X5 H t, n * x = x * n := by
    intro n hn
    have hcent : Work.ThmF.Lemma5.X5 H t ≤ Subgroup.centralizer ({n} : Set G) := by
      rw [hA]
      refine sup_le ?_ ?_
      · intro u hu
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcommQ n hn u hu).symm
      · intro y hy
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [Work.Models.mem_conj_iff] at hy
        have h' := hconjQ n hn t htX (t⁻¹ * y * t) hy
        rw [show t * (t⁻¹ * y * t) * t⁻¹ = y by group] at h'
        exact h'.symm
    intro x hx
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hcent hx)).symm
  -- ## Step 4: `z ∈ V = C_D(t)`
  have hzK : z ∈ Work.ThmF.Ksub H t := hNK hz
  have hzD : z ∈ Submission.Blueprint.twoPoint H t :=
    Work.ThmF.Ksub_le_twoPoint (H := H) t hzK
  have hzt : z * t = t * z := hZ z hz t htX
  have hzcentD : z ∈ Submission.Blueprint.centD H t :=
    Subgroup.mem_inf.mpr ⟨hzD, Subgroup.mem_centralizer_singleton_iff.mpr hzt⟩
  -- ## Step 5: Ch. V §1 Prop. 2 (`Ksub H t = Kset H t`)
  have hKsub_set : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
    Work.ZassenhausSuzuki.SzHyp.Ksub_eq_Kset h
  -- ## Step 6: `z ∈ Kset` centralises `Q0sub ∋ s`, and `Kset` acts regularly, so `z = 1`
  have hzKset : z ∈ Work.ThmF.Kset H t := by
    rw [← hKsub_set]
    exact hzK
  have hs_inv : s ∈ Submission.Blueprint.involutions (H : Set G) :=
    Work.ZassenhausSuzuki.Shadow.L5.s_mem_involutions h
  have hzs : z * s * z⁻¹ = s := by
    have hcomm : z * s = s * z := hcommQ z hz s (Work.ZassenhausSuzuki.Shadow.L5.s_mem_Q0sub h)
    rw [hcomm]; group
  obtain ⟨k₁, -, huniq⟩ := Work.ThmF.L5.Kset_regular hsplit s hs_inv s hs_inv
  have hk₁ : k₁ = 1 :=
    (huniq 1 ⟨Work.ThmF.one_mem_Kset H t, by simp⟩).symm
  exact hz1 (by rw [huniq z ⟨hzKset, hzs⟩, hk₁])

/-- `(MulAut.conj g).toMonoidHom x = g * x * g⁻¹`, in the form needed for `Subgroup.map`. -/
theorem conj_toMonoidHom_apply {G : Type} [Group G] (g x : G) :
    (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := by
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

/-- `conj t (Q0sub H) ≤ X5 H t`. -/
theorem conj_t_Q0sub_le_X5 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} :
    Submission.Blueprint.conj t (Work.ThmF.Q0sub H) ≤ Work.ThmF.Lemma5.X5 H t := by
  intro y hy
  obtain ⟨q, hq, hyq⟩ := Subgroup.mem_map.mp hy
  rw [← hyq, conj_toMonoidHom_apply]
  exact (Work.ThmF.Lemma5.X5 H t).mul_mem
    ((Work.ThmF.Lemma5.X5 H t).mul_mem (Work.ThmF.Lemma5.t_mem_X5 H t)
      (Work.ZassenhausSuzuki.Shadow.L5.Q0sub_le_X5 hq))
    ((Work.ThmF.Lemma5.X5 H t).inv_mem (Work.ThmF.Lemma5.t_mem_X5 H t))

/-- `U = Q0sub H` inside `X5 H t` is commutative (elementary abelian, Ch. V §1 Prop. 1 (c)). -/
theorem isMulCommutative_Q0sub_subgroupOf {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t s : G} (h : Work.ZassenhausSuzuki.SzHyp H Q t s) :
    IsMulCommutative ↥((Work.ThmF.Q0sub H).subgroupOf (Work.ThmF.Lemma5.X5 H t)) := by
  have hQcomm := Work.ZassenhausSuzuki.SzHyp.hcomm h
  have hQel := Work.ThmF.L5.Q0sub_elementary hQcomm
  rw [isMulCommutative_iff]
  intro a b
  apply Subtype.ext
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact hQel.2.1 a.1 (Subgroup.mem_subgroupOf.mp a.2) b.1 (Subgroup.mem_subgroupOf.mp b.2)

/-- The stabiliser of the base coset `Bx = bor H t` in `X5 H t` is `Bx`. -/
theorem stabilizer_mk_one_bor {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G} :
    MulAction.stabilizer ↥(Work.ThmF.Lemma5.X5 H t)
        (@QuotientGroup.mk _ _ ((Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t))
          (1 : ↥(Work.ThmF.Lemma5.X5 H t))) =
      (Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) := by
  set Bx : Subgroup ↥(Work.ThmF.Lemma5.X5 H t) :=
    (Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) with hBx
  apply le_antisymm
  · intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg
    have h2 : g⁻¹ * 1 ∈ Bx := by
      have h1 : (g • (QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) :
            ↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx)) =
          (QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) :
            ↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx) := hg
      have h3 : (QuotientGroup.mk g : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx) =
          (QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) :
            ↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx) := by
        rwa [show g • (QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) :
              ↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx) =
            (QuotientGroup.mk (g * 1) : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx) from rfl,
          mul_one] at h1
      exact QuotientGroup.eq.mp h3
    simpa using (Subgroup.inv_mem Bx h2)
  · intro g hg
    rw [MulAction.mem_stabilizer_iff]
    have h1 : g⁻¹ * 1 ∈ Bx := by simpa using (Subgroup.inv_mem Bx hg)
    have h3 := QuotientGroup.eq.mpr h1
    rw [show g • (QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) :
          ↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx) =
        (QuotientGroup.mk (g * 1) : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx) from rfl, mul_one]
    exact h3

/-- Normal subgroups of `X5 H t`, viewed in the ambient group, are invariant under conjugation. -/
theorem conj_map_subtype_eq {G : Type} [Group G] {M : Subgroup G} {N : Subgroup ↥M}
    (hN : N.Normal) {g : G} (hg : g ∈ M) :
    (N.map M.subtype).map (MulAut.conj g).toMonoidHom = N.map M.subtype := by
  apply le_antisymm
  · intro z hz
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp hz
    obtain ⟨yM, hyM, hyMeq⟩ := Subgroup.mem_map.mp hy
    have hyMeq' : (yM : G) = y := hyMeq
    refine Subgroup.mem_map.mpr ⟨⟨g, hg⟩ * yM * ⟨g, hg⟩⁻¹,
      Subgroup.Normal.conj_mem hN yM hyM ⟨g, hg⟩, ?_⟩
    show (((⟨g, hg⟩ : ↥M) * yM * (⟨g, hg⟩ : ↥M)⁻¹) : G) = z
    rw [← hyz, ← hyMeq', conj_toMonoidHom_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  · intro z hz
    obtain ⟨zM, hzM, hzMeq⟩ := Subgroup.mem_map.mp hz
    have hzMeq' : (zM : G) = z := hzMeq
    refine Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : ↥M)⁻¹ * zM * (⟨g, hg⟩ : ↥M), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨(⟨g, hg⟩ : ↥M)⁻¹ * zM * (⟨g, hg⟩ : ↥M),
        by simpa using Subgroup.Normal.conj_mem hN zM hzM (⟨g, hg⟩⁻¹ : ↥M), rfl⟩
    · show ((MulAut.conj g).toMonoidHom
        ((((⟨g, hg⟩ : ↥M)⁻¹ * zM * (⟨g, hg⟩ : ↥M)) : ↥M) : G)) = z
      rw [← hzMeq', conj_toMonoidHom_apply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

/-- **Faithfulness in `X5`**: a normal subgroup of `X5 H t` contained in `B = bor H t` is trivial. -/
theorem eq_bot_of_le_bor_subgroupOf {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (h : Work.ZassenhausSuzuki.SzHyp H Q t s)
    (hA : Work.ThmF.Lemma5.X5 H t =
      Work.ThmF.Q0sub H ⊔ Submission.Blueprint.conj t (Work.ThmF.Q0sub H))
    {N : Subgroup ↥(Work.ThmF.Lemma5.X5 H t)} (hN : N.Normal)
    (hNB : N ≤ (Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) :
    N = ⊥ := by
  refine (Subgroup.map_eq_bot_iff_of_injective N
    (Work.ThmF.Lemma5.X5 H t).subtype_injective).mp ?_
  refine eq_bot_of_le_bor_of_normal h hA ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    exact hNB hy
  · intro g hg
    exact conj_map_subtype_eq hN hg

/-- **The Iwasawa/Bender step**: if `N ⊴ X5` is not contained in `B = bor H t`, then `N = ⊤`. -/
theorem eq_top_of_not_le_bor {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (h : Work.ZassenhausSuzuki.SzHyp H Q t s)
    (hA : Work.ThmF.Lemma5.X5 H t =
      Work.ThmF.Q0sub H ⊔ Submission.Blueprint.conj t (Work.ThmF.Q0sub H))
    (h2t : Submission.Blueprint.IsTwoTransitiveOn
      ((Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)))
    {N : Subgroup ↥(Work.ThmF.Lemma5.X5 H t)} (hN : N.Normal)
    (hNB : ¬ N ≤ (Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) :
    N = ⊤ := by
  classical
  haveI : N.Normal := hN
  haveI hpre : MulAction.IsPreprimitive ↥(Work.ThmF.Lemma5.X5 H t)
      (↥(Work.ThmF.Lemma5.X5 H t) ⧸
        (Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2t
  set Bx : Subgroup ↥(Work.ThmF.Lemma5.X5 H t) :=
    (Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) with hBx
  set Ux : Subgroup ↥(Work.ThmF.Lemma5.X5 H t) :=
    (Work.ThmF.Q0sub H).subgroupOf (Work.ThmF.Lemma5.X5 H t) with hUx
  set tX : ↥(Work.ThmF.Lemma5.X5 H t) := Work.ThmF.Lemma5.tX H t with htXdef
  have hntN : N ≠ ⊥ := fun hbot => hNB (hbot ▸ bot_le)
  -- the stabiliser of the base coset is `Bx`
  have hstab : ∀ g : ↥(Work.ThmF.Lemma5.X5 H t),
      g ∈ MulAction.stabilizer ↥(Work.ThmF.Lemma5.X5 H t)
        (@QuotientGroup.mk _ _ Bx (1 : ↥(Work.ThmF.Lemma5.X5 H t))) ↔ g ∈ Bx := by
    intro g
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro h
      have h3 : (QuotientGroup.mk g : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx) =
          (QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) :
            ↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx) := by
        rwa [show g • (@QuotientGroup.mk _ _ Bx (1 : ↥(Work.ThmF.Lemma5.X5 H t))) =
            (QuotientGroup.mk (g * 1) : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx) from rfl,
          mul_one] at h
      have h4 := QuotientGroup.eq.mp h3
      simpa using (Subgroup.inv_mem Bx h4)
    · intro hg
      have h4 : g⁻¹ * 1 ∈ Bx := by simpa using (Subgroup.inv_mem Bx hg)
      have h3 := QuotientGroup.eq.mpr h4
      rwa [show g • (@QuotientGroup.mk _ _ Bx (1 : ↥(Work.ThmF.Lemma5.X5 H t))) =
          (QuotientGroup.mk (g * 1) : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx) from rfl, mul_one]
  -- `N` acts non-trivially, hence transitively, on the cosets
  haveI htrans : MulAction.IsPretransitive ↥N (↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx) := by
    have hfix : MulAction.fixedPoints ↥N (↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx) ≠ Set.univ := by
      intro huniv
      apply hntN
      have hle : N ≤ Bx := by
        intro n hn
        have hmem : (n : ↥(Work.ThmF.Lemma5.X5 H t)) ∈
            MulAction.stabilizer ↥(Work.ThmF.Lemma5.X5 H t)
              (@QuotientGroup.mk _ _ Bx (1 : ↥(Work.ThmF.Lemma5.X5 H t))) := by
          rw [MulAction.mem_stabilizer_iff]
          have h1 : (@QuotientGroup.mk _ _ Bx (1 : ↥(Work.ThmF.Lemma5.X5 H t)) :
                ↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx) ∈
              MulAction.fixedPoints ↥N (↥(Work.ThmF.Lemma5.X5 H t) ⧸ Bx) := by
            rw [huniv]
            exact Set.mem_univ _
          rw [MulAction.mem_fixedPoints] at h1
          exact h1 ⟨n, hn⟩
        exact (hstab _).mp hmem
      exact eq_bot_of_le_bor_subgroupOf h hA hN hle
    exact MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfix
  -- every conjugate of `Ux` lies in `N ⊔ Ux`
  have hconjUx : ∀ g : ↥(Work.ThmF.Lemma5.X5 H t),
      Submission.Blueprint.conj g Ux ≤ N ⊔ Ux := by
    intro g
    obtain ⟨n, hn_eq⟩ := MulAction.IsPretransitive.exists_smul_eq (M := ↥N)
      (@QuotientGroup.mk _ _ Bx (1 : ↥(Work.ThmF.Lemma5.X5 H t)))
      (g • (@QuotientGroup.mk _ _ Bx (1 : ↥(Work.ThmF.Lemma5.X5 H t))))
    have hn_eq' : (n : ↥(Work.ThmF.Lemma5.X5 H t)) •
        (@QuotientGroup.mk _ _ Bx (1 : ↥(Work.ThmF.Lemma5.X5 H t))) =
        g • (@QuotientGroup.mk _ _ Bx (1 : ↥(Work.ThmF.Lemma5.X5 H t))) := hn_eq
    have hb : (n : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * g ∈ Bx := by
      have h1 : (n : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * g ∈
          MulAction.stabilizer ↥(Work.ThmF.Lemma5.X5 H t)
            (@QuotientGroup.mk _ _ Bx (1 : ↥(Work.ThmF.Lemma5.X5 H t))) := by
        rw [MulAction.mem_stabilizer_iff]
        show ((n : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * g) •
            (@QuotientGroup.mk _ _ Bx (1 : ↥(Work.ThmF.Lemma5.X5 H t))) =
            (@QuotientGroup.mk _ _ Bx (1 : ↥(Work.ThmF.Lemma5.X5 H t)))
        rw [mul_smul, ← hn_eq', ← mul_smul, inv_mul_cancel, one_smul]
      exact (hstab _).mp h1
    have hbU : ((n : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * g) ∈
        Subgroup.normalizer ((Ux : Subgroup ↥(Work.ThmF.Lemma5.X5 H t)) :
          Set ↥(Work.ThmF.Lemma5.X5 H t)) :=
      Work.ZassenhausSuzuki.Shadow.L5.subgroupOf_bor_le_normalizer_subgroupOf h (by rwa [← hBx])
    have hconjb : Submission.Blueprint.conj ((n : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * g) Ux = Ux :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hbU
    have hg_eq : g = (n : ↥(Work.ThmF.Lemma5.X5 H t)) *
        ((n : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * g) := by group
    intro y hy
    obtain ⟨u, hu, hyu⟩ := Subgroup.mem_map.mp hy
    have hbu : (MulAut.conj ((n : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * g)).toMonoidHom u ∈ Ux := by
      rw [← hconjb]
      exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    have hy' : y = (n : ↥(Work.ThmF.Lemma5.X5 H t)) *
        ((MulAut.conj ((n : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * g)).toMonoidHom u) *
        (n : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ := by
      rw [← hyu, conj_toMonoidHom_apply, conj_toMonoidHom_apply, hg_eq]
      group
    rw [hy']
    have hnN : (n : ↥(Work.ThmF.Lemma5.X5 H t)) ∈ N := n.2
    exact (N ⊔ Ux).mul_mem
      ((N ⊔ Ux).mul_mem (Subgroup.mem_sup_left hnN) (Subgroup.mem_sup_right hbu))
      ((N ⊔ Ux).inv_mem (Subgroup.mem_sup_left hnN))
  -- hence `N ⊔ Ux = ⊤`
  have hsup : N ⊔ Ux = ⊤ := by
    have hA_M : (⊤ : Subgroup ↥(Work.ThmF.Lemma5.X5 H t)) =
        Ux ⊔ Submission.Blueprint.conj tX Ux := by
      refine le_antisymm ?_ le_top
      have hle : (Work.ThmF.Q0sub H ⊔
            Submission.Blueprint.conj t (Work.ThmF.Q0sub H)).subgroupOf
            (Work.ThmF.Lemma5.X5 H t) ≤ Ux ⊔ Submission.Blueprint.conj tX Ux := by
        rw [Subgroup.subgroupOf_sup (Work.ZassenhausSuzuki.Shadow.L5.Q0sub_le_X5 (H := H) (t := t))
          (conj_t_Q0sub_le_X5 (H := H) (Q := Q) (t := t))]
        refine sup_le le_sup_left ?_
        rw [← Work.ZassenhausSuzuki.Shadow.L5.conj_subgroupOf (Work.ThmF.Lemma5.t_mem_X5 H t)
          (Work.ThmF.Q0sub H)]
        exact le_sup_right
      intro x hx
      obtain ⟨y, hyX, hy_eq⟩ : ∃ y : G, y ∈ Work.ThmF.Lemma5.X5 H t ∧ (x : G) = y :=
        ⟨(x : G), x.2, rfl⟩
      have hyAB : y ∈ Work.ThmF.Q0sub H ⊔ Submission.Blueprint.conj t (Work.ThmF.Q0sub H) := by
        rw [hA] at hyX
        exact hyX
      exact hle (Subgroup.mem_subgroupOf.mpr (by rw [hy_eq]; exact hyAB))
    have hle : Ux ⊔ Submission.Blueprint.conj tX Ux ≤ N ⊔ Ux :=
      sup_le le_sup_right (hconjUx tX)
    exact top_le_iff.mp (hA_M ▸ hle)
  -- `N` contains the commutator subgroup
  have hperf : commutator ↥(Work.ThmF.Lemma5.X5 H t) ≤ N :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup
      (isMulCommutative_Q0sub_subgroupOf h)
  -- the sharp transitivity of `Kset` on `Ux^#` puts `Ux` inside `N`
  set sX : ↥(Work.ThmF.Lemma5.X5 H t) :=
    ⟨s, Work.ZassenhausSuzuki.Shadow.L5.Q0sub_le_X5 (Work.ZassenhausSuzuki.Shadow.L5.s_mem_Q0sub h)⟩ with hsXdef
  have hsXsq : sX * sX = 1 := by
    apply Subtype.ext
    have h2 : s * s = 1 := by
      have h3 := pow_orderOf_eq_one s
      rw [h.s_inv] at h3
      simpa [pow_two] using h3
    simpa [hsXdef] using h2
  have hsXinv : sX⁻¹ = sX := inv_eq_of_mul_eq_one_right hsXsq
  have haux : ∀ u ∈ Ux, u ≠ 1 → u * sX ∈ N := by
    intro u hu hu1
    have huQ : (u : G) ∈ Work.ThmF.Q0sub H := Subgroup.mem_subgroupOf.mp hu
    have huQ1 : (u : G) ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
    have huInv : (u : G) ∈ Submission.Blueprint.involutions (H : Set G) := by
      rcases (Work.ZassenhausSuzuki.Shadow.L5.mem_Q0sub_iff h (u : G)).mp huQ with h3 | h3
      · exact h3
      · exact absurd h3 huQ1
    obtain ⟨k, ⟨hkK, hk_eq⟩, -⟩ :=
      Work.ThmF.L5.Kset_regular h.split s (Work.ZassenhausSuzuki.Shadow.L5.s_mem_involutions h) (u : G) huInv
    have hkX : k ∈ Work.ThmF.Lemma5.X5 H t := Work.ZassenhausSuzuki.Shadow.L5.Kset_le_X5 hkK
    have hcomm : ⁅(⟨k, hkX⟩ : ↥(Work.ThmF.Lemma5.X5 H t)), sX⁆ ∈
        commutator ↥(Work.ThmF.Lemma5.X5 H t) := by
      rw [commutator]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    have hu_eq : u = (⟨k, hkX⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) * sX * ⟨k, hkX⟩⁻¹ := by
      apply Subtype.ext
      simpa [hsXdef] using hk_eq.symm
    have h1 : u * sX = ⁅(⟨k, hkX⟩ : ↥(Work.ThmF.Lemma5.X5 H t)), sX⁆ := by
      rw [commutatorElement_def, hsXinv, hu_eq]
    rw [h1]
    exact hperf hcomm
  -- two distinct nonidentity elements of `Ux`
  have hcard : 1 < (Submission.Blueprint.involutions (H : Set G)).ncard := by
    have h2 := Work.ThmF.Bender.cardInvGeTwo h.split.stronglyEmbedded h.four
    omega
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ :=
    (Set.one_lt_ncard (s := Submission.Blueprint.involutions (H : Set G))).mp hcard
  have ha₀Q : a₀ ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H ha₀)
  have hb₀Q : b₀ ∈ Work.ThmF.Q0sub H :=
    Work.ThmF.Q0_le_Q0sub H (Work.ThmF.involutions_subset_Q0 H hb₀)
  have ha₀sq : a₀ * a₀ = 1 := by
    have h3 := pow_orderOf_eq_one a₀
    rw [ha₀.2] at h3
    simpa [pow_two] using h3
  have hb₀sq : b₀ * b₀ = 1 := by
    have h3 := pow_orderOf_eq_one b₀
    rw [hb₀.2] at h3
    simpa [pow_two] using h3
  have ha₀ne : a₀ ≠ 1 := fun h1 => by
    have h2 : orderOf a₀ = 2 := ha₀.2
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hb₀ne : b₀ ≠ 1 := fun h1 => by
    have h2 : orderOf b₀ = 2 := hb₀.2
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  set u₀ : ↥(Work.ThmF.Lemma5.X5 H t) := ⟨a₀, Work.ZassenhausSuzuki.Shadow.L5.Q0sub_le_X5 ha₀Q⟩ with hu₀def
  set v₀ : ↥(Work.ThmF.Lemma5.X5 H t) := ⟨b₀, Work.ZassenhausSuzuki.Shadow.L5.Q0sub_le_X5 hb₀Q⟩ with hv₀def
  have hu₀U : u₀ ∈ Ux := Subgroup.mem_subgroupOf.mpr ha₀Q
  have hv₀U : v₀ ∈ Ux := Subgroup.mem_subgroupOf.mpr hb₀Q
  have hu₀ne : u₀ ≠ 1 := fun h1 => ha₀ne (by simpa [hu₀def] using congrArg Subtype.val h1)
  have hv₀ne : v₀ ≠ 1 := fun h1 => hb₀ne (by simpa [hv₀def] using congrArg Subtype.val h1)
  have hu₀sq : u₀ * u₀ = 1 := by
    apply Subtype.ext
    show a₀ * a₀ = 1
    exact ha₀sq
  have hv₀sq : v₀ * v₀ = 1 := by
    apply Subtype.ext
    show b₀ * b₀ = 1
    exact hb₀sq
  have huv_ne : u₀ * v₀ ≠ 1 := by
    intro h1
    have h4 : a₀ * b₀ = 1 := by simpa [hu₀def, hv₀def] using congrArg Subtype.val h1
    have h5 : b₀ = a₀ := by
      have h6 := inv_eq_of_mul_eq_one_right h4
      rw [show a₀⁻¹ = a₀ from inv_eq_of_mul_eq_one_right ha₀sq] at h6
      exact h6.symm
    exact hab₀ h5.symm
  have huvU : u₀ * v₀ ∈ Ux := Ux.mul_mem hu₀U hv₀U
  have huvN : u₀ * v₀ ∈ N := by
    have hv₀inv : v₀⁻¹ = v₀ := inv_eq_of_mul_eq_one_right hv₀sq
    have h1 : (v₀ * sX)⁻¹ = sX * v₀ := by rw [mul_inv_rev, hsXinv, hv₀inv]
    have h2 : u₀ * v₀ = (u₀ * sX) * (v₀ * sX)⁻¹ := by
      rw [h1, mul_assoc u₀ sX (sX * v₀), ← mul_assoc sX sX v₀, hsXsq, one_mul]
    rw [h2]
    exact N.mul_mem (haux u₀ hu₀U hu₀ne) (N.inv_mem (haux v₀ hv₀U hv₀ne))
  have hsXN : sX ∈ N := by
    have h1 : sX = (u₀ * v₀)⁻¹ * ((u₀ * v₀) * sX) := by group
    rw [h1]
    exact N.mul_mem (N.inv_mem huvN) (haux (u₀ * v₀) huvU huv_ne)
  have hUxle : Ux ≤ N := by
    intro u hu
    rcases eq_or_ne u 1 with h1 | h1
    · rw [h1]; exact N.one_mem
    · have h2 : u = (u * sX) * sX := by rw [mul_assoc, hsXsq, mul_one]
      rw [h2]
      exact N.mul_mem (haux u hu h1) hsXN
  rw [← hsup, sup_eq_left.mpr hUxle]

/-- The action of `X = X5 H t` on the cosets of `B = bor H t` is 2-transitive (Bruhat). -/
theorem X5_twoTransitive {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (h : Work.ZassenhausSuzuki.SzHyp H Q t s) :
    Submission.Blueprint.IsTwoTransitiveOn
      ((Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) := by
  classical
  show MulAction.IsMultiplyPretransitive ↥(Work.ThmF.Lemma5.X5 H t)
    (↥(Work.ThmF.Lemma5.X5 H t) ⧸
      (Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) 2
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective c
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective d
  have hxy : x⁻¹ * y ∉ (Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) :=
    fun hc => hab (QuotientGroup.eq.mpr hc)
  have hzw : z⁻¹ * w ∉ (Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) :=
    fun hc => hcd (QuotientGroup.eq.mpr hc)
  have hdec : ∀ u : ↥(Work.ThmF.Lemma5.X5 H t),
      u ∉ (Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t) →
      ∃ b₁ ∈ Work.ZassenhausSuzuki.Shadow.L5.bor H t, ∃ b₂ ∈ Work.ZassenhausSuzuki.Shadow.L5.bor H t, (u : G) = b₁ * t * b₂ := by
    intro u hu
    rcases Work.ZassenhausSuzuki.Shadow.L5.mem_bor_or_btb h u.2 with hb | h
    · exact absurd (Subgroup.mem_subgroupOf.mpr hb) hu
    · exact h
  obtain ⟨b₁, hb₁, b₂, hb₂, heq1⟩ := hdec (x⁻¹ * y) hxy
  obtain ⟨b₃, hb₃, b₄, hb₄, heq2⟩ := hdec (z⁻¹ * w) hzw
  have hb₁X : b₁ ∈ Work.ThmF.Lemma5.X5 H t := Work.ZassenhausSuzuki.Shadow.L5.bor_le_X5 hb₁
  have hb₂X : b₂ ∈ Work.ThmF.Lemma5.X5 H t := Work.ZassenhausSuzuki.Shadow.L5.bor_le_X5 hb₂
  have hb₃X : b₃ ∈ Work.ThmF.Lemma5.X5 H t := Work.ZassenhausSuzuki.Shadow.L5.bor_le_X5 hb₃
  have hb₄X : b₄ ∈ Work.ThmF.Lemma5.X5 H t := Work.ZassenhausSuzuki.Shadow.L5.bor_le_X5 hb₄
  have htX : t ∈ Work.ThmF.Lemma5.X5 H t := Work.ThmF.Lemma5.t_mem_X5 H t
  -- the two Bruhat decompositions, inside `X5`
  have hxyM : x⁻¹ * y = (⟨b₁, hb₁X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) * ⟨t, htX⟩ *
      ⟨b₂, hb₂X⟩ := by
    apply Subtype.ext
    rw [heq1]
    simp
  have hzwM : z⁻¹ * w = (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) * ⟨t, htX⟩ *
      ⟨b₄, hb₄X⟩ := by
    apply Subtype.ext
    rw [heq2]
    simp
  have hwM : w = z * (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) * ⟨t, htX⟩ * ⟨b₄, hb₄X⟩ := by
    have h1 : w = z * (z⁻¹ * w) := by group
    rw [h1, hzwM]
    group
  refine ⟨z * (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) * (⟨b₁, hb₁X⟩ : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹
      * x⁻¹, ?_, ?_⟩
  · rw [show (z * (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) *
          (⟨b₁, hb₁X⟩ : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * x⁻¹) • (QuotientGroup.mk x) =
        QuotientGroup.mk (z * (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) *
          (⟨b₁, hb₁X⟩ : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * x⁻¹ * x) from rfl]
    rw [show z * (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) *
          (⟨b₁, hb₁X⟩ : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * x⁻¹ * x =
        z * (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) *
          (⟨b₁, hb₁X⟩ : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ from by group]
    apply QuotientGroup.eq.mpr
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hval : (((z * (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) *
          (⟨b₁, hb₁X⟩ : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹)⁻¹ * z :
          ↥(Work.ThmF.Lemma5.X5 H t)) : G) = b₁ * b₃⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hval]
    exact (Work.ZassenhausSuzuki.Shadow.L5.bor H t).mul_mem hb₁ ((Work.ZassenhausSuzuki.Shadow.L5.bor H t).inv_mem hb₃)
  · rw [show (z * (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) *
          (⟨b₁, hb₁X⟩ : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * x⁻¹) • (QuotientGroup.mk y) =
        QuotientGroup.mk (z * (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) *
          (⟨b₁, hb₁X⟩ : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * x⁻¹ * y) from rfl]
    have hval : z * (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) *
          (⟨b₁, hb₁X⟩ : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * x⁻¹ * y =
        z * (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) * ⟨t, htX⟩ * ⟨b₂, hb₂X⟩ := by
      rw [show z * (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) *
            (⟨b₁, hb₁X⟩ : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * x⁻¹ * y =
          z * (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) *
            (⟨b₁, hb₁X⟩ : ↥(Work.ThmF.Lemma5.X5 H t))⁻¹ * (x⁻¹ * y) from by group,
        hxyM]
      group
    rw [hval, hwM]
    apply QuotientGroup.eq.mpr
    refine Subgroup.mem_subgroupOf.mpr ?_
    have hval2 : (((z * (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) * ⟨t, htX⟩ *
          ⟨b₂, hb₂X⟩)⁻¹ * (z * (⟨b₃, hb₃X⟩ : ↥(Work.ThmF.Lemma5.X5 H t)) * ⟨t, htX⟩ *
          ⟨b₄, hb₄X⟩) : ↥(Work.ThmF.Lemma5.X5 H t)) : G) = b₂⁻¹ * b₄ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [hval2]
    exact (Work.ZassenhausSuzuki.Shadow.L5.bor H t).mul_mem ((Work.ZassenhausSuzuki.Shadow.L5.bor H t).inv_mem hb₂) hb₄

theorem L5simpleX5 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G} (h : Work.ZassenhausSuzuki.SzHyp H Q t s) : IsSimpleGroup ↥(Work.ThmF.Lemma5.X5 H t) := by
  haveI : Nontrivial ↥(Work.ThmF.Lemma5.X5 H t) := Work.ZassenhausSuzuki.Shadow.L5.nontrivial_X5 h
  refine IsSimpleGroup.mk (fun N hN => ?_)
  by_cases hNB : N ≤ (Work.ZassenhausSuzuki.Shadow.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)
  · exact Or.inl (eq_bot_of_le_bor_subgroupOf h (X5_eq_sup_conj_Q0sub h) hN hNB)
  · exact Or.inr (eq_top_of_not_le_bor h (X5_eq_sup_conj_Q0sub h) (X5_twoTransitive h)
      hN hNB)

end Work.ZassenhausSuzuki.Shadow.ChV12
