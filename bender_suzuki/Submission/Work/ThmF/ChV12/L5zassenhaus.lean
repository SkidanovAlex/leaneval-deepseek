import Mathlib
import Submission.Work.ThmF.ChV12.L5Base
import Submission.Work.ThmF.ChV12.L5Struct
import Submission.Work.ThmF.ChV12.L5splitRankOne
import Submission.Work.ThmF.ChV12.L5prop2
import Submission.Work.ZassenhausPSL2.ZassenhausPSL2OfQCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.L5zassenhaus` — `X = ⟨Q₀,K,t⟩` is a Zassenhaus group on `X ⧸ B`

Goal (as requested):

  `IsZassenhaus ((bor H t).subgroupOf (X5 H t))`

where `bor H t = Q₀sub H ⊔ Ksub H t` is the "Borel" `B` of `X = X5 H t = ⟨Q₀,K,t⟩`.

## The reduction (proved below as `L5zassenhaus_of_Ksub_eq_Kset`)

Write `X = X5 H t`, `B = (bor H t).subgroupOf X`, `T = tX H t`, `Q₀ = Q0sub H` (elementary
abelian, `Q₀ = Inv H ∪ {1}`) and `K = Ksub H t = ⟨Kset H t⟩`.

By the Bruhat decomposition `X = B ⊔ B·t·B` (`L5.X5_eq_borel`, `L5.mem_bor_or_btb`) every
non-base point of `Ω = X ⧸ B` is `b • (T ⧸ B)` with `b ∈ B`, so `X` is 2-transitive on `Ω`.
Hence every triple-point stabiliser is conjugate to the stabiliser of `(1, T, qT)` for some
`q ∈ Q₀^#`, and an element fixing both `1` and `T` lies in
`B ⊓ Bᵗ = (Ksub H t).subgroupOf X` (`L5.twoPoint_bor_subgroupOf`); a computation with
`QuotientGroup.eq` (using `Ksub H t ≤ N_G(Q₀sub)` and `Q₀sub ⊓ Ksub = ⊥`) gives, for
`g ∈ Ksub H t` and `q ∈ Q₀`,

  `g • (qT) = qT`  ⟺  `(g : G) * q * (g : G)⁻¹ = q`.

Finally, if `Ksub H t = Kset H t`, then for `g ∈ Kset H t` with `g q g⁻¹ = q` the uniqueness in
`L5.Kset_regular` (applied to `a = b = q`, using `q ∈ Q₀^# = Inv H`) forces `g = 1`, so all
triple-point stabilisers are trivial.

## Status of `Ksub H t = Kset H t` (Peterfalvi II Ch. V §1 Prop. 2)

`L5prop2.lean` proves it when `centD H t = ⊥` or when `W H t = C_{centD H t}(Kset H t) ≠ ⊥`;
the case `centD H t ≠ ⊥ ∧ W H t = ⊥` is left open there.  By the reduction and
orbit–stabiliser (`|Ksub| = |Q₀^#| · |C_{Ksub}(q)|`, `|Q₀^#| = |Kset H t|`), `IsZassenhaus B`
**implies** `Ksub H t = Kset H t`; hence `L5zassenhaus` is *equivalent* to that open case,
which is not vacuous: the rank-one data of `PΓL(2,8)` has `centD = C₃ ≠ 1`, `W = 1` and
`Ksub = Kset = C₇`.  The workspace's own record (`L5prop2_caseWbot.lean`,
`PSU3/StageA/chVI_caseWbot.lean`) documents that this case needs Appendix X together with
`FeitThompsonProp`, or the `V = W` theory (Suzuki's Lemma 60, Kantor–Seitz, Peterfalvi
Ch. VII §4); neither is available from the hypotheses of `L5zassenhaus`.
-/

namespace Work.ThmF.ChV12

open LeanEval.GroupTheory.Defs Submission.Blueprint

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}

/-- The "Borel" `B = (bor H t).subgroupOf (X5 H t)` of `X = X5 H t`. -/
abbrev L5B (H : Subgroup G) (t : G) : Subgroup ↥(Work.ThmF.Lemma5.X5 H t) :=
  (Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)

/-- The Weyl element `t` as an element of `X = X5 H t`. -/
abbrev L5t (H : Subgroup G) (t : G) : ↥(Work.ThmF.Lemma5.X5 H t) :=
  Work.ThmF.Lemma5.tX H t

/-- `q * t` as an element of `X = X5 H t`, for `q ∈ Q₀sub H`. -/
abbrev L5qt (H : Subgroup G) (t : G) (q : ↥(Work.ThmF.Q0sub H)) :
    ↥(Work.ThmF.Lemma5.X5 H t) :=
  ⟨(q : G) * t, (Work.ThmF.Lemma5.X5 H t).mul_mem
    ((Subgroup.closure_le (Work.ThmF.Lemma5.X5 H t)).mpr
      (fun z hz => Work.ThmF.Lemma5.Q0_subset_X5 H t hz) q.2)
    (Work.ThmF.Lemma5.t_mem_X5 H t)⟩

@[simp] theorem L5qt_coe (q : ↥(Work.ThmF.Q0sub H)) :
    ((L5qt H t q : ↥(Work.ThmF.Lemma5.X5 H t)) : G) = (q : G) * t := rfl

@[simp] theorem L5t_coe : ((L5t H t : ↥(Work.ThmF.Lemma5.X5 H t)) : G) = t := rfl

/-- The action of `X` on `X ⧸ B`, expressed with the group multiplication. -/
theorem L5smul (g x : ↥(Work.ThmF.Lemma5.X5 H t)) :
    g • (QuotientGroup.mk x : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) =
      QuotientGroup.mk (g * x) := by
  rw [MulAction.Quotient.smul_coe]
  rfl

/-- **The reduction.**  If `K = ⟨Kset H t⟩` is the subgroup `Kset H t` (Peterfalvi II Ch. V §1
Prop. 2), then `X = ⟨Q₀,K,t⟩` is a Zassenhaus group on the cosets of its Borel `B = bor H t`. -/
theorem L5zassenhaus_of_Ksub_eq_Kset (hC4 : ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s)
    (hK : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t) :
    IsZassenhaus (L5B H t) := by
  classical
  have hKm : ∀ x : G, x ∈ Work.ThmF.Ksub H t ↔ x ∈ Work.ThmF.Kset H t := fun x => by
    show x ∈ (Work.ThmF.Ksub H t : Set G) ↔ x ∈ Work.ThmF.Kset H t
    rw [hK]
  have htKin : ∀ k : G, k ∈ Work.ThmF.Ksub H t → t * k * t⁻¹ = k⁻¹ := fun k hk =>
    (Work.ThmF.mem_Kset_iff.mp ((hKm k).mp hk)).2
  have ht2 : t * t = 1 := Work.ThmF.L5.ht_mul_self h
  have htinv : t⁻¹ = t := Work.ThmF.L5.ht_inv h
  have hNQ : Work.ThmF.Ksub H t ≤ Subgroup.normalizer (Work.ThmF.Q0sub H : Set G) :=
    Work.ThmF.L5.Ksub_le_normalizer_Q0sub hC4 h
  have hinfQK : Work.ThmF.Q0sub H ⊓ Work.ThmF.Ksub H t = ⊥ :=
    Work.ThmF.L5.Q0sub_inf_Ksub_eq_bot h
  -- (0) the base point
  have hmk1 : ∀ x : ↥(Work.ThmF.Lemma5.X5 H t),
      (QuotientGroup.mk x : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) =
        QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) ↔ x ∈ L5B H t := by
    intro x
    constructor
    · intro hx
      have h1 : x⁻¹ ∈ L5B H t := by
        have := (QuotientGroup.eq.mp hx : x⁻¹ * 1 ∈ L5B H t)
        simpa using this
      simpa using (L5B H t).inv_mem h1
    · intro hx
      rw [QuotientGroup.eq]
      simpa using hx
  -- (1) every non-base point is `b • T`
  have hnonbase : ∀ p : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t,
      p ≠ QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) →
      ∃ b : ↥(Work.ThmF.Lemma5.X5 H t), b ∈ L5B H t ∧
        p = b • (QuotientGroup.mk (L5t H t) : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) := by
    intro p hp
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
    have hxB : x ∉ L5B H t := fun hx => hp ((hmk1 x).mpr hx)
    rcases Work.ThmF.L5.mem_bor_or_btb (H := H) (Q := Q) (t := t) hC4 h x.2 with
      hbor | ⟨b₁, hb₁, b₂, hb₂, hxeq⟩
    · exact absurd (Subgroup.mem_subgroupOf.mpr hbor) hxB
    · refine ⟨⟨b₁, Work.ThmF.L5.bor_le_X5 (H := H) (t := t) hb₁⟩,
        Subgroup.mem_subgroupOf.mpr hb₁, ?_⟩
      have hmem : x⁻¹ * (⟨b₁, Work.ThmF.L5.bor_le_X5 (H := H) (t := t) hb₁⟩ *
          L5t H t) ∈ L5B H t := by
        apply Subgroup.mem_subgroupOf.mpr
        have hval : (((x⁻¹ * (⟨b₁, Work.ThmF.L5.bor_le_X5 (H := H) (t := t) hb₁⟩ *
            L5t H t)) : ↥(Work.ThmF.Lemma5.X5 H t)) : G) = b₂⁻¹ := by
          push_cast
          show (x : G)⁻¹ * (b₁ * t) = b₂⁻¹
          rw [hxeq]
          calc (b₁ * t * b₂)⁻¹ * (b₁ * t)
              = b₂⁻¹ * t⁻¹ * (b₁⁻¹ * b₁) * t := by group
            _ = b₂⁻¹ * t⁻¹ * t := by rw [inv_mul_cancel, mul_one]
            _ = b₂⁻¹ * (t * t) := by rw [htinv, mul_assoc]
            _ = b₂⁻¹ := by rw [ht2, mul_one]
        rw [hval]
        exact (Work.ThmF.L5.bor H t).inv_mem hb₂
      have hpt : (QuotientGroup.mk x : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) =
          QuotientGroup.mk (⟨b₁, Work.ThmF.L5.bor_le_X5 (H := H) (t := t) hb₁⟩ *
            L5t H t) := QuotientGroup.eq.mpr hmem
      rw [hpt, L5smul]
  -- (2) fixing the two points `1` and `T` puts an element in `Ksub H t`
  have hfixK : ∀ g' : ↥(Work.ThmF.Lemma5.X5 H t),
      g' • (QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) :
          ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) =
        QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) →
      g' • (QuotientGroup.mk (L5t H t) : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) =
        QuotientGroup.mk (L5t H t) →
      (g' : G) ∈ Work.ThmF.Ksub H t := by
    intro g' h1 h2
    have h1' : (QuotientGroup.mk g' : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) =
        QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) := by
      rw [L5smul, mul_one] at h1
      exact h1
    have hB : g' ∈ L5B H t := (hmk1 g').mp h1'
    have h2s : (QuotientGroup.mk (g' * L5t H t) :
        ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) = QuotientGroup.mk (L5t H t) := by
      rw [L5smul] at h2
      exact h2
    have hinv : (L5t H t)⁻¹ * g'⁻¹ * L5t H t ∈ L5B H t := by
      have hh := QuotientGroup.eq.mp h2s
      simpa [mul_inv_rev, mul_assoc] using hh
    have hinvc : g'⁻¹ ∈ Submission.Blueprint.conj (L5t H t) (L5B H t) :=
      Work.Models.mem_conj_iff.mpr (by simpa using hinv)
    have hconj : g' ∈ Submission.Blueprint.conj (L5t H t) (L5B H t) := by
      have := (Submission.Blueprint.conj (L5t H t) (L5B H t)).inv_mem hinvc
      simpa using this
    have hmem : g' ∈ twoPoint (L5B H t) (L5t H t) := Subgroup.mem_inf.mpr ⟨hB, hconj⟩
    rw [Work.ThmF.L5.twoPoint_bor_subgroupOf hC4 h] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  -- (3) a `Ksub`-element fixing `qT` commutes with `q`
  have hfixQ : ∀ (g'' : ↥(Work.ThmF.Lemma5.X5 H t)) (q : ↥(Work.ThmF.Q0sub H)),
      (g'' : G) ∈ Work.ThmF.Ksub H t →
      g'' • (QuotientGroup.mk (L5qt H t q) : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) =
        QuotientGroup.mk (L5qt H t q) →
      (g'' : G) * (q : G) * (g'' : G)⁻¹ = (q : G) := by
    intro g'' q hgK hfix
    have h1' : (QuotientGroup.mk (g'' * L5qt H t q) :
        ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) = QuotientGroup.mk (L5qt H t q) := by
      rw [L5smul] at hfix
      exact hfix
    have h1 : (L5qt H t q)⁻¹ * g''⁻¹ * L5qt H t q ∈ L5B H t := by
      have hh := QuotientGroup.eq.mp h1'
      simpa [mul_inv_rev, mul_assoc] using hh
    have h2 : t * (q : G)⁻¹ * (g'' : G)⁻¹ * (q : G) * t ∈ Work.ThmF.L5.bor H t := by
      have hh := Subgroup.mem_subgroupOf.mp h1
      have hval : ((((L5qt H t q)⁻¹ * g''⁻¹ * L5qt H t q :
          ↥(Work.ThmF.Lemma5.X5 H t)) : G)) =
          t * (q : G)⁻¹ * (g'' : G)⁻¹ * (q : G) * t := by
        show ((q : G) * t)⁻¹ * (g'' : G)⁻¹ * ((q : G) * t)
            = t * (q : G)⁻¹ * (g'' : G)⁻¹ * (q : G) * t
        rw [show ((q : G) * t)⁻¹ = t * (q : G)⁻¹ by rw [mul_inv_rev, htinv]]
        group
      rwa [hval] at hh
    have h3 : (q : G)⁻¹ * (g'' : G)⁻¹ * (q : G) ∈
        Submission.Blueprint.conj t (Work.ThmF.L5.bor H t) := by
      rw [Work.Models.mem_conj_iff]
      rw [show t⁻¹ * ((q : G)⁻¹ * (g'' : G)⁻¹ * (q : G)) * t
            = t * (q : G)⁻¹ * (g'' : G)⁻¹ * (q : G) * t by rw [htinv]; group]
      exact h2
    have h4 : (q : G)⁻¹ * (g'' : G)⁻¹ * (q : G) ∈ Work.ThmF.Ksub H t := by
      have hbor : (q : G)⁻¹ * (g'' : G)⁻¹ * (q : G) ∈ Work.ThmF.L5.bor H t := by
        refine (Work.ThmF.L5.bor H t).mul_mem ((Work.ThmF.L5.bor H t).mul_mem ?_ ?_) ?_
        · exact (Work.ThmF.L5.bor H t).inv_mem (Subgroup.mem_sup_left q.2)
        · exact (Work.ThmF.L5.bor H t).inv_mem (Subgroup.mem_sup_right hgK)
        · exact Subgroup.mem_sup_left q.2
      have := Subgroup.mem_inf.mpr ⟨hbor, h3⟩
      rw [Work.ThmF.L5.twoPoint_bor_eq_Ksub hC4 h] at this
      exact this
    have h5 : (q : G)⁻¹ * (g'' : G)⁻¹ * (q : G) * (g'' : G) ∈ Work.ThmF.Ksub H t :=
      (Work.ThmF.Ksub H t).mul_mem h4 hgK
    have h6 : (q : G)⁻¹ * (g'' : G)⁻¹ * (q : G) * (g'' : G) ∈ Work.ThmF.Q0sub H := by
      have hgq : (g'' : G)⁻¹ * (q : G) * (g'' : G) ∈ Work.ThmF.Q0sub H :=
        ((Subgroup.mem_normalizer_iff''.mp (hNQ hgK)) (q : G)).mp q.2
      rw [show (q : G)⁻¹ * (g'' : G)⁻¹ * (q : G) * (g'' : G)
            = (q : G)⁻¹ * ((g'' : G)⁻¹ * (q : G) * (g'' : G)) by group]
      exact (Work.ThmF.Q0sub H).mul_mem ((Work.ThmF.Q0sub H).inv_mem q.2) hgq
    have h7 : (q : G)⁻¹ * (g'' : G)⁻¹ * (q : G) * (g'' : G) = 1 := by
      have := Subgroup.mem_inf.mpr ⟨h6, h5⟩
      rw [hinfQK] at this
      exact Subgroup.mem_bot.mp this
    have h8 : (g'' : G)⁻¹ * (q : G) * (g'' : G) = (q : G) := by
      have := congrArg (fun z => (q : G) * z) h7
      simpa [mul_assoc] using this
    calc (g'' : G) * (q : G) * (g'' : G)⁻¹
        = (g'' : G) * ((g'' : G)⁻¹ * (q : G) * (g'' : G)) * (g'' : G)⁻¹ := by
          rw [h8]
      _ = (q : G) := by group
  -- (4) the main argument
  intro a b c hab hac hbc g ha hb hc
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ↥(Work.ThmF.Lemma5.X5 H t),
      y₀ • a = QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) := by
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective a
    exact ⟨u⁻¹, by rw [L5smul, inv_mul_cancel]⟩
  have hy₀b : y₀ • b ≠ QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) := fun hh => by
    have h2 : y₀ • a = y₀ • b := by rw [hy₀, hh]
    exact hab (MulAction.injective y₀ h2)
  obtain ⟨b₀, hb₀, hb₀eq⟩ := hnonbase (y₀ • b) hy₀b
  set y : ↥(Work.ThmF.Lemma5.X5 H t) := b₀⁻¹ * y₀ with hy
  have hya : y • a = QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) := by
    rw [hy, mul_smul, hy₀, L5smul, mul_one]
    exact (hmk1 b₀⁻¹).mpr ((L5B H t).inv_mem hb₀)
  have hyb : y • b = QuotientGroup.mk (L5t H t) := by
    rw [hy, mul_smul, hb₀eq, inv_smul_smul]
  set g' : ↥(Work.ThmF.Lemma5.X5 H t) := y * g * y⁻¹ with hg'
  have hg'a : g' • (QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) :
      ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) =
      QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) := by
    have h1 : (QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) :
        ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) = y • a := hya.symm
    rw [h1, hg']
    rw [show (y * g * y⁻¹) • (y • a) = y • (g • a) by
      rw [mul_smul, mul_smul, inv_smul_smul]]
    rw [ha, hya]
  have hg'b : g' • (QuotientGroup.mk (L5t H t) : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) =
      QuotientGroup.mk (L5t H t) := by
    have h1 : (QuotientGroup.mk (L5t H t) : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) = y • b :=
      hyb.symm
    rw [h1, hg']
    rw [show (y * g * y⁻¹) • (y • b) = y • (g • b) by
      rw [mul_smul, mul_smul, inv_smul_smul]]
    rw [hb, hyb]
  have hg'c : g' • (y • c) = y • c := by
    rw [hg']
    rw [show (y * g * y⁻¹) • (y • c) = y • (g • c) by
      rw [mul_smul, mul_smul, inv_smul_smul]]
    rw [hc]
  have hg'K : (g' : G) ∈ Work.ThmF.Ksub H t := hfixK g' hg'a hg'b
  have hyc1 : y • c ≠ QuotientGroup.mk (1 : ↥(Work.ThmF.Lemma5.X5 H t)) := fun hh => by
    rw [← hya] at hh
    exact hac (MulAction.injective y hh).symm
  have hycT : y • c ≠ QuotientGroup.mk (L5t H t) := fun hh => by
    rw [← hyb] at hh
    exact hbc (MulAction.injective y hh).symm
  obtain ⟨b₁, hb₁, hb₁eq⟩ := hnonbase (y • c) hyc1
  obtain ⟨q, hq, k, hk, hkq⟩ :=
    Work.ThmF.L5.bor_factor hC4 h (Subgroup.mem_subgroupOf.mp hb₁)
  set kX : ↥(Work.ThmF.Lemma5.X5 H t) := ⟨k, Work.ThmF.L5.Ksub_le_X5 (H := H) (t := t) hk⟩
    with hkX
  have hqT : y • c = kX • (QuotientGroup.mk (L5qt H t ⟨q, hq⟩)) := by
    have hb₁' : y • c = QuotientGroup.mk (b₁ * L5t H t) := by
      rw [hb₁eq, L5smul]
    rw [hb₁', L5smul]
    refine QuotientGroup.eq.mpr ?_
    apply Subgroup.mem_subgroupOf.mpr
    have hval : ((((b₁ * L5t H t)⁻¹ * (kX * L5qt H t ⟨q, hq⟩) :
        ↥(Work.ThmF.Lemma5.X5 H t)) : G)) = 1 := by
      show ((b₁ : G) * t)⁻¹ * (k * ((q : G) * t)) = 1
      rw [← hkq]
      rw [show ((k * q) * t)⁻¹ = t * ((q : G)⁻¹ * k⁻¹) by
        rw [mul_inv_rev, mul_inv_rev, htinv]]
      calc t * ((q : G)⁻¹ * k⁻¹) * (k * ((q : G) * t))
          = t * (q : G)⁻¹ * (k⁻¹ * k) * (q : G) * t := by group
        _ = t * (q : G)⁻¹ * (q : G) * t := by rw [inv_mul_cancel, mul_one]
        _ = t * ((q : G)⁻¹ * (q : G)) * t := by group
        _ = t * 1 * t := by rw [inv_mul_cancel]
        _ = t * t := by rw [mul_one]
        _ = 1 := ht2
    rw [hval]
    exact (Work.ThmF.L5.bor H t).one_mem
  have hkfixT : kX • (QuotientGroup.mk (L5t H t) : ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) =
      QuotientGroup.mk (L5t H t) := by
    rw [L5smul]
    refine QuotientGroup.eq.mpr ?_
    apply Subgroup.mem_subgroupOf.mpr
    have hval : ((((kX * L5t H t)⁻¹ * L5t H t : ↥(Work.ThmF.Lemma5.X5 H t)) : G)) = k := by
      show ((k : G) * t)⁻¹ * t = k
      rw [show ((k : G) * t)⁻¹ = t * k⁻¹ by rw [mul_inv_rev, htinv]]
      have h2 : t * k * t = k⁻¹ := by
        have := htKin k hk
        rwa [htinv] at this
      calc t * k⁻¹ * t = (t * k * t)⁻¹ := by rw [mul_inv_rev, mul_inv_rev, htinv]; group
        _ = (k⁻¹)⁻¹ := by rw [h2]
        _ = k := inv_inv k
    rw [hval]
    exact Subgroup.mem_sup_right hk
  have hqne : (⟨q, hq⟩ : ↥(Work.ThmF.Q0sub H)) ≠ 1 := by
    intro hq1
    apply hycT
    rw [hqT]
    have hL : L5qt H t ⟨q, hq⟩ = L5t H t := by
      apply Subtype.ext
      show (q : G) * t = t
      rw [show (q : G) = 1 from congrArg Subtype.val hq1, one_mul]
    rw [hL]
    exact hkfixT
  set g'' : ↥(Work.ThmF.Lemma5.X5 H t) := kX⁻¹ * g' * kX with hg''
  have hg''K : (g'' : G) ∈ Work.ThmF.Ksub H t :=
    (Work.ThmF.Ksub H t).mul_mem
      ((Work.ThmF.Ksub H t).mul_mem ((Work.ThmF.Ksub H t).inv_mem hk) hg'K) hk
  have hg''fix : g'' • (QuotientGroup.mk (L5qt H t ⟨q, hq⟩) :
      ↥(Work.ThmF.Lemma5.X5 H t) ⧸ L5B H t) =
      QuotientGroup.mk (L5qt H t ⟨q, hq⟩) := by
    calc g'' • (QuotientGroup.mk (L5qt H t ⟨q, hq⟩))
        = kX⁻¹ • (g' • (kX • (QuotientGroup.mk (L5qt H t ⟨q, hq⟩)))) := by
          rw [hg'', mul_smul, mul_smul]
      _ = kX⁻¹ • (g' • (y • c)) := by rw [hqT]
      _ = kX⁻¹ • (y • c) := by rw [hg'c]
      _ = kX⁻¹ • (kX • (QuotientGroup.mk (L5qt H t ⟨q, hq⟩))) := by rw [hqT]
      _ = QuotientGroup.mk (L5qt H t ⟨q, hq⟩) := by rw [inv_smul_smul]
  have hcomm : (g'' : G) * (q : G) * (g'' : G)⁻¹ = (q : G) :=
    hfixQ g'' ⟨q, hq⟩ hg''K hg''fix
  have hqInv : (q : G) ∈ involutions (H : Set G) := by
    have hqQ0 : (q : G) ∈ Work.ThmF.Q0 H := (Work.ThmF.L5.mem_Q0sub_iff hC4 h q).mp hq
    rcases (Work.ThmF.mem_Q0_iff.mp hqQ0) with h' | h'
    · exact h'
    · exact absurd (Subtype.ext h') hqne
  obtain ⟨k₀, ⟨hk₀, hk₀q⟩, huniq⟩ :=
    Work.ThmF.L5.Kset_regular h.split (q : G) hqInv (q : G) hqInv
  have hk₀1 : k₀ = 1 := (huniq 1 ⟨Work.ThmF.one_mem_Kset H t, by simp⟩).symm
  have hg''1 : (g'' : G) = 1 := (huniq (g'' : G) ⟨(hKm _).mp hg''K, hcomm⟩).trans hk₀1
  have hg''X : g'' = 1 := Subtype.ext hg''1
  have hg'1 : g' = 1 := by
    have h2 : kX⁻¹ * g' * kX = 1 := by rw [← hg'']; exact hg''X
    calc g' = kX * (kX⁻¹ * g' * kX) * kX⁻¹ := by group
      _ = 1 := by rw [h2]; group
  have h2 : y * g * y⁻¹ = 1 := by rw [← hg']; exact hg'1
  calc g = y⁻¹ * (y * g * y⁻¹) * y := by group
    _ = 1 := by rw [h2]; group

/-- `L5zassenhaus`, from Peterfalvi II Ch. V §1 Prop. 2 (`Ksub H t = Kset H t`). -/
theorem L5zassenhaus {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G} (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp) (h : Work.ThmF.Lemma5.Hyp5 H Q t s) : Submission.Blueprint.IsZassenhaus ((Work.ThmF.L5.bor H t).subgroupOf (Work.ThmF.Lemma5.X5 H t)) := by
  exact L5zassenhaus_of_Ksub_eq_Kset hC4 h (L5prop2 hFT hC4 h)

end Work.ThmF.ChV12
