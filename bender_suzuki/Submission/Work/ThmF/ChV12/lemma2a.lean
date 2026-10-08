import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThmF.ChV12.Basic
import Submission.Work.ThmF.ChV12.lemma2b
import Submission.Work.ThmF.ChV12.lemma2a_transfer
import Submission.Work.ThmF.ChV12.lemma2a_cent_split
import Submission.Work.DoubleTransitivity.App2.app2_7
import Submission.Work.ThreePoints.P3NeBot.p3_b_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.lemma2a` — Peterfalvi II, Ch. V §2 Lemma 2 (a)

For `X ≠ 1` a subgroup of `V = C_D(t)` (with `H = Q ⋊ D` a split rank-one datum), the pair
`(C_G(X), C_G(X) ⊓ H)` is a member of Peterfalvi's family `𝓕`:

`(C_G(X), C_G(X) ⊓ H) ∈ 𝓕`, `𝒩(C_G(X)) = C_{C_G(X) ⊓ D}(C_G(X) ⊓ Q) ⊆ C_G(X) ⊓ V`, and
`M ↦ C_G(X) ⊓ M` is a bijection of `Ω_X` onto the conjugates of `C_G(X) ⊓ H` in `C_G(X)`.

Ingredients (all from the source):

* `H ⊓ C_G(X)` is strongly embedded in `C_G(X)` by Ch. II §4 Prop. 1(b) (`hC4`), applied with
  `F = C_G(X)`; the hypothesis `|Ω_X| ≥ 3` is
  `Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD` (the points `H`, `Hᵗ`, `H(t)`).
  This gives the three fields "`M ≠ ⊤`", "`|M|` even", "`M ∩ M^x` of odd order".
* `C_G(X)` acts 2-transitively on `L ⧸ M` (`L = C_G(X)`, `M = L ⊓ H`): by Appendix II (7)
  (`app2_7_core`) the subgroup `Q ⊓ C_G(X)` is sharply transitive on `Ω_X ∖ {H}`, so `C_G(X)`
  is 2-transitive on `Ω_X` (`centralizer_transitive_fixedPts` + the point stabiliser being
  transitive on the complement); the 2-transitivity transfers to `L ⧸ M` along the orbit map
  (`lemma2a_transfer`).
* for `x ∈ L ∖ M`, the normal complement of `M ⊓ M^x` in `M` is `C_Q(X)`: `M = C_Q(X)·C_D(X)`
  (Appendix II (7)) and `Q ⊓ H^x = 1` (`Q` acts freely on `Ω ∖ {H}`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF

namespace Work.ThmF.ChV12

/-! ## Auxiliary lemmas -/

/-- `subgroupOf` commutes with `⊓`. -/
private theorem subgroupOf_inf {G : Type} [Group G] (A B C : Subgroup G) :
    (A ⊓ B).subgroupOf C = A.subgroupOf C ⊓ B.subgroupOf C := by
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]

/-- The `subgroupOf` of the trivial subgroup is trivial. -/
private theorem subgroupOf_bot {G : Type} [Group G] (C : Subgroup G) :
    (⊥ : Subgroup G).subgroupOf C = ⊥ := by
  ext x
  simp

/-- The conjugate of `A.subgroupOf C` (computed inside `C`) is the `subgroupOf` of the conjugate
of `A`, for `x ∈ C`. -/
private theorem conj_subgroupOf {G : Type} [Group G] {C A : Subgroup G} (x : C) :
    (A.subgroupOf C).map (MulAut.conj x).toMonoidHom
      = (Submission.Blueprint.conj (x : G) A ⊓ C).subgroupOf C := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · rintro ⟨a, ha, hay⟩
    have hay' : (y : G) = (x : G) * (a : G) * (x : G)⁻¹ := by
      have h := congrArg (fun z : C => (z : G)) hay
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
      exact h.symm
    refine ⟨?_, y.2⟩
    rw [hay']
    exact Subgroup.mem_map_of_mem _ ha
  · rintro ⟨hyA, -⟩
    obtain ⟨a, haA, hax⟩ := Subgroup.mem_map.mp hyA
    have hax' : a = (x : G)⁻¹ * (y : G) * (x : G) := by
      rw [← hax]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    refine ⟨⟨a, ?_⟩, haA, ?_⟩
    · rw [hax']
      exact C.mul_mem (C.mul_mem (C.inv_mem x.2) y.2) x.2
    · apply Subtype.ext
      show (x : G) * a * (x : G)⁻¹ = (y : G)
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hax

/-- Conjugation by `m ∈ H ⊓ C_G(X)` preserves `Q ⊓ C_G(X)` (as a set), when `H ≤ N_G(Q)`. -/
private theorem conj_iff_mem_inf_centralizer {G : Type} [Group G] {H Q X : Subgroup G} {m : G} :
    m ∈ H → m ∈ Subgroup.centralizer (X : Set G) → H ≤ Subgroup.normalizer (Q : Set G) →
    ∀ q : G, q ∈ Q ⊓ Subgroup.centralizer (X : Set G) ↔
      m * q * m⁻¹ ∈ Q ⊓ Subgroup.centralizer (X : Set G) := by
  intro hmH hmC hQH
  have key : ∀ {r : G}, r ∈ H → r ∈ Subgroup.centralizer (X : Set G) → ∀ q : G,
      q ∈ Q ⊓ Subgroup.centralizer (X : Set G) →
        r * q * r⁻¹ ∈ Q ⊓ Subgroup.centralizer (X : Set G) := by
    intro r hrH hrC q hq
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hQH hrH) q).mp hq.1, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hrC hq.2)
      ((Subgroup.centralizer (X : Set G)).inv_mem hrC)
  intro q
  constructor
  · exact key hmH hmC q
  · intro hq
    have h := key (H.inv_mem hmH) (Subgroup.centralizer (X : Set G) |>.inv_mem hmC) (m * q * m⁻¹) hq
    have heq : m⁻¹ * (m * q * m⁻¹) * m⁻¹⁻¹ = q := by group
    rwa [heq] at h

/-- `Q` acts freely on `Ω ∖ {pt H}`: a `q ∈ Q` fixing a point `≠ pt H` is trivial. -/
private theorem Q_free_of_splitRankOne {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) {q : G} (hq : q ∈ Q) {ω : G ⧸ H}
    (hω : ω ≠ ((1 : G) : G ⧸ H)) (hfix : q • ω = ω) : q = 1 := by
  -- an element of `Q` fixing `t • pt H` is trivial
  have hfreeness : ∀ z ∈ Q, z • (((t : G)) : G ⧸ H) = (((t : G)) : G ⧸ H) → z = 1 := by
    intro z hz hzfix
    have hzt : ((z * t : G) : G ⧸ H) = ((t : G) : G ⧸ H) := by
      have h1 : (z * t) • (((1 : G)) : G ⧸ H) = ((t : G) : G ⧸ H) := by
        rw [mul_smul]
        simpa [Work.DoubleTransitivity.smul_pt] using hzfix
      simpa [Work.DoubleTransitivity.smul_pt] using h1
    have hmem : ((z * t)⁻¹ * t) ∈ H := QuotientGroup.eq.mp hzt
    have hzHt : z ∈ Submission.Blueprint.conj t H := by
      rw [Work.DoubleTransitivity.mem_conj]
      have h3 : ((z * t)⁻¹ * t)⁻¹ ∈ H := H.inv_mem hmem
      have h4 : ((z * t)⁻¹ * t)⁻¹ = t⁻¹ * z * t := by group
      rwa [h4] at h3
    have hmem2 : z ∈ Q ⊓ twoPoint H t := ⟨hz, ⟨h.le hz, hzHt⟩⟩
    rw [h.inf_eq, Subgroup.mem_bot] at hmem2
    exact hmem2
  -- move `ω` to `t • pt H` by an element of `Q`
  have hreg : Work.DoubleTransitivity.IsRegularOnSub Q
      ({((1 : G) : G ⧸ H)}ᶜ : Set (G ⧸ H)) :=
    (base_regular_data h (a := ((1 : G) : G ⧸ H)) (b := ((t : G) : G ⧸ H)) rfl rfl).2.2.1
  have htne : (((t : G)) : G ⧸ H) ≠ ((1 : G) : G ⧸ H) := by
    intro hcon
    exact h.not_mem (by have h2 := QuotientGroup.eq.mp hcon.symm; simpa using H.inv_mem h2)
  obtain ⟨y, hy, hyω⟩ := hreg.1 (((t : G)) : G ⧸ H) htne ω hω
  have hyq : y⁻¹ * q * y ∈ Q := Q.mul_mem (Q.mul_mem (Q.inv_mem hy) hq) hy
  have hzy : y⁻¹ * q * y = 1 := by
    refine hfreeness (y⁻¹ * q * y) hyq ?_
    rw [mul_smul, mul_smul, hyω, hfix, ← hyω, inv_smul_smul]
  calc q = y * (y⁻¹ * q * y) * y⁻¹ := by group
    _ = 1 := by rw [hzy]; group

/-- `Q ⊓ H^x = 1` for `x ∉ H` (freeness of `Q` on `Ω ∖ {H}`). -/
private theorem inf_conj_eq_bot_of_not_mem {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (h : IsSplitRankOne H Q t) {x : G} (hx : x ∉ H) :
    Q ⊓ Submission.Blueprint.conj x H = ⊥ := by
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨hqQ, hqHx⟩ := Subgroup.mem_inf.mp hq
  have hfix : q • ((x : G) : G ⧸ H) = ((x : G) : G ⧸ H) :=
    (Work.DoubleTransitivity.mem_conj_iff_smul_fixed).mp hqHx
  have hxne : ((x : G) : G ⧸ H) ≠ ((1 : G) : G ⧸ H) := by
    intro hcon
    exact hx (by have h2 := QuotientGroup.eq.mp hcon; simpa using H.inv_mem h2)
  exact Subgroup.mem_bot.mpr (Q_free_of_splitRankOne h hqQ hxne hfix)

/-- `Q · (H ⊓ H^x) = H` for `x ∈ C_G(X) ∖ H`. -/
private theorem sup_Q_inf_conj_eq {G : Type} [Group G] [Finite G] {H Q X : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) {x : G} (hxC : x ∈ Subgroup.centralizer (X : Set G))
    (hxH : x ∉ H) :
    Q ⊔ (H ⊓ Submission.Blueprint.conj x H) = H := by
  have h2t : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := h.twoTransitive
  rw [MulAction.is_two_pretransitive_iff] at h2t
  have hne_t : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
    intro hcon
    exact h.not_mem (by have h2 := QuotientGroup.eq.mp hcon; simpa using h2)
  have hne_x : ((1 : G) : G ⧸ H) ≠ ((x : G) : G ⧸ H) := by
    intro hcon
    exact hxH (by have h2 := QuotientGroup.eq.mp hcon.symm; simpa using H.inv_mem h2)
  obtain ⟨g, hg1, hg2⟩ := h2t (a := ((1 : G) : G ⧸ H)) (b := ((t : G) : G ⧸ H))
    (c := ((1 : G) : G ⧸ H)) (d := ((x : G) : G ⧸ H)) hne_t hne_x
  have hgH : g ∈ H := by
    rw [← stabilizer_one H, MulAction.mem_stabilizer_iff]
    exact hg1
  have hgHconj : Submission.Blueprint.conj g H = H :=
    (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer g H).mpr
      (Subgroup.le_normalizer hgH)
  have hgt : (((g * t : G)) : G ⧸ H) = ((x : G) : G ⧸ H) := by
    have h1 : (g * t) • (((1 : G)) : G ⧸ H) = ((x : G) : G ⧸ H) := by
      rw [mul_smul]
      simpa [Work.DoubleTransitivity.smul_pt] using hg2
    simpa [Work.DoubleTransitivity.smul_pt] using h1
  have hconj_eq : Submission.Blueprint.conj x H
      = Submission.Blueprint.conj g (Submission.Blueprint.conj t H) := by
    calc Submission.Blueprint.conj x H
        = Submission.Blueprint.conj (g * t) H := by
          rw [← Work.ThreePoints.stabilizer_mk H x,
            ← Work.ThreePoints.stabilizer_mk H (g * t), hgt]
      _ = Submission.Blueprint.conj g (Submission.Blueprint.conj t H) :=
          Work.DoubleTransitivity.conj_mul g t H
  have hDH : H ⊓ Submission.Blueprint.conj x H
      = Submission.Blueprint.conj g (twoPoint H t) := by
    rw [hconj_eq]
    have hmap : Submission.Blueprint.conj g (H ⊓ Submission.Blueprint.conj t H)
        = Submission.Blueprint.conj g H ⊓ Submission.Blueprint.conj g
            (Submission.Blueprint.conj t H) :=
      Subgroup.map_inf H (Submission.Blueprint.conj t H) (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective
    rw [hmap, hgHconj]
  have hQg : Submission.Blueprint.conj g Q = Q :=
    (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer g Q).mpr (h.normal hgH)
  rw [hDH, ← hQg, ← Subgroup.map_sup, h.sup_eq]
  exact hgHconj


/-! ## Ch. V §2 Lemma 2 (a) -/

open LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem lemma2a {G : Type} [Group G] [Finite G] (hS : Situation G) (hC4 : ChIIFourProp) (H Q : Subgroup G) (t : G) (h : IsSplitRankOne H Q t) (X : Subgroup G) (hXV : X ≤ centD H t) (hXne : X ≠ ⊥) : IsBenderFamily ↥(Subgroup.centralizer (X : Set G)) ((H ⊓ Subgroup.centralizer (X : Set G)).subgroupOf (Subgroup.centralizer (X : Set G))) := by
  classical
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hC
  set M : Subgroup C := (H ⊓ C).subgroupOf C with hM
  have hXH : X ≤ H := fun x hx => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hXV hx)).1).1
  have htC : t ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hXV hx)).2
  -- `H ⊓ C_G(X)` is strongly embedded in `C_G(X)` (Ch. II §4 Prop. 1 (b))
  have h3 : 3 ≤ (fixedPts H X).ncard :=
    Work.ThreePoints.P3NeBot.three_le_ncard_fixedPts_of_le_centD h.stronglyEmbedded h.invol
      h.not_mem hXV
  have hSE : IsStronglyEmbedded M := by
    have hcl := (hC4 G hS H h.stronglyEmbedded t h.invol h.not_mem).1 X C h3
      (fun y hy => hy.1) (Subgroup.centralizer_le_normalizer (X : Set G)) 1
      (by rw [Work.DoubleTransitivity.conj_one]; exact hXH)
    rw [hM]
    simpa [Work.DoubleTransitivity.conj_one, inf_comm] using hcl
  -- `C_G(X)` acts 2-transitively on `Ω_X`
  have h2sub : Work.DoubleTransitivity.IsTwoTransitiveOnSub C (fixedPts H X) := by
    have hbase : ((1 : G) : G ⧸ H) ∈ fixedPts H X := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, stabilizer_one H]
      exact hXH
    have htb : ((t : G) : G ⧸ H) ∈ fixedPts H X := by
      rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, Work.ThreePoints.stabilizer_mk H t]
      exact fun y hy => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hXV hy)).1).2
    have hXY : X ≤ MulAction.stabilizer G ((1 : G) : G ⧸ H) ⊓
        MulAction.stabilizer G ((t : G) : G ⧸ H) := by
      rw [stabilizer_one H, Work.ThreePoints.stabilizer_mk H t]
      exact fun y hy => Subgroup.mem_inf.mpr
        ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hXV hy)).1).1,
         (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hXV hy)).1).2⟩
    have hne_pt_t : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
      intro hcon
      exact h.not_mem (by have h2 := QuotientGroup.eq.mp hcon; simpa using h2)
    have hbd := base_regular_data h (a := ((1 : G) : G ⧸ H)) (b := ((t : G) : G ⧸ H)) rfl rfl
    have hcore := Work.DoubleTransitivity.App2.app2_7_core (X := G) (E := G ⧸ H)
      (u := ((1 : G) : G ⧸ H)) (v := ((t : G) : G ⧸ H)) (Q := Q) (Y := X)
      hne_pt_t hbd.1 hbd.2.1 hbd.2.2.1 hbd.2.2.2 hXY
    have htrans := centralizer_transitive_fixedPts h hXV
    have htrans_pt : ∀ ω ∈ fixedPts H X, ∃ l ∈ C, l • ω = ((1 : G) : G ⧸ H) := by
      intro ω hω
      obtain ⟨l, hlω⟩ := htrans ω hω
      exact ⟨(l : G)⁻¹, C.inv_mem l.2, by rw [← hlω, inv_smul_smul]⟩
    have hstab : ∀ c ∈ fixedPts H X, c ≠ ((1 : G) : G ⧸ H) →
        ∀ d ∈ fixedPts H X, d ≠ ((1 : G) : G ⧸ H) →
        ∃ m ∈ C, m • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) ∧ m • c = d := by
      intro c hc hcne d hd hdne
      obtain ⟨qc, hqc, hqcc⟩ := hcore.2.2 c hc hcne
      obtain ⟨qd, hqd, hqdd⟩ := hcore.2.2 d hd hdne
      refine ⟨(qd : G) * (qc : G)⁻¹, Subgroup.mul_mem _ qd.2.2 (C.inv_mem qc.2.2), ?_, ?_⟩
      · have h1 : (qc : G)⁻¹ • (((1 : G)) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
          rw [← MulAction.mem_stabilizer_iff, stabilizer_one H]
          exact h.le (Q.inv_mem qc.2.1)
        rw [mul_smul, h1]
        rw [← MulAction.mem_stabilizer_iff, stabilizer_one H]
        exact h.le qd.2.1
      · have h1 : (qc : G)⁻¹ • c = (((t : G)) : G ⧸ H) := by
          rw [← hqc, inv_smul_smul]
        rw [mul_smul, h1, hqd]
    intro c hc d hd hcd c' hc' d' hd' hcd'
    obtain ⟨g, hg, hgpt⟩ := htrans_pt c hc
    obtain ⟨g', hg', hg'pt⟩ := htrans_pt c' hc'
    have hg'c' : (g')⁻¹ • ((1 : G) : G ⧸ H) = c' := by
      rw [← hg'pt, inv_smul_smul]
    have hgd : g • d ∈ fixedPts H X :=
      Work.ThreePoints.P3NeBot.normalizer_preserves_fixedPts
        (Subgroup.centralizer_le_normalizer (X : Set G) hg) hd
    have hg'd' : g' • d' ∈ fixedPts H X :=
      Work.ThreePoints.P3NeBot.normalizer_preserves_fixedPts
        (Subgroup.centralizer_le_normalizer (X : Set G) hg') hd'
    have hgdne : g • d ≠ ((1 : G) : G ⧸ H) := by
      intro hcon
      have hcd'' : g • c = g • d := by rw [hcon, hgpt]
      exact hcd (MulAction.injective g hcd'')
    have hg'd'ne : g' • d' ≠ ((1 : G) : G ⧸ H) := by
      intro hcon
      have hcd'' : g' • c' = g' • d' := by rw [hcon, hg'pt]
      exact hcd' (MulAction.injective g' hcd'')
    obtain ⟨m, hm, hmpt, hmd⟩ := hstab (g • d) hgd hgdne (g' • d') hg'd' hg'd'ne
    refine ⟨(g')⁻¹ * m * g, Subgroup.mul_mem _ (Subgroup.mul_mem _ (C.inv_mem hg') hm) hg,
      ?_, ?_⟩
    · rw [mul_smul, mul_smul, hgpt, hmpt, hg'c']
    · rw [mul_smul, mul_smul, hmd, inv_smul_smul]
  refine ⟨hSE.1, hSE.2.1, ?_, hSE.2.2, ?_⟩
  · -- `C_G(X)` is `2`-transitive on the cosets of `C_G(X) ⊓ H`
    rw [hM, hC]
    exact lemma2a_transfer H X hXH h2sub
  · -- the normal complement `C_Q(X)` of `M ⊓ M^x` in `M`
    intro x hxM
    have hxH : (x : G) ∉ H := by
      intro hxin
      exact hxM (by rw [hM, Subgroup.mem_subgroupOf]; exact ⟨hxin, x.2⟩)
    have hQinf : Q ⊓ Submission.Blueprint.conj (x : G) H = ⊥ :=
      inf_conj_eq_bot_of_not_mem h hxH
    have hconjM : M ⊓ conj x M
        = ((H ⊓ Submission.Blueprint.conj (x : G) H) ⊓ C).subgroupOf C := by
      have h1 : Submission.Blueprint.conj (x : G) (H ⊓ C) ⊓ C
          = Submission.Blueprint.conj (x : G) H ⊓ C := by
        have hmap : Submission.Blueprint.conj (x : G) (H ⊓ C)
            = Submission.Blueprint.conj (x : G) H ⊓ Submission.Blueprint.conj (x : G) C :=
          Subgroup.map_inf H C (MulAut.conj (x : G)).toMonoidHom
            (MulAut.conj (x : G)).injective
        have hxC' : Submission.Blueprint.conj (x : G) C = C :=
          (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer (x : G) C).mpr
            (Subgroup.le_normalizer x.2)
        rw [hmap, hxC', inf_assoc, inf_idem]
      have hconj : conj x ((H ⊓ C).subgroupOf C)
          = ((Submission.Blueprint.conj (x : G) H) ⊓ C).subgroupOf C :=
        (conj_subgroupOf (A := H ⊓ C) x).trans (by rw [h1])
      have hGC : (H ⊓ C) ⊓ (Submission.Blueprint.conj (x : G) H ⊓ C)
          = (H ⊓ Submission.Blueprint.conj (x : G) H) ⊓ C := by
        have h1 : (H ⊓ C) ⊓ (Submission.Blueprint.conj (x : G) H ⊓ C)
            ≤ (H ⊓ Submission.Blueprint.conj (x : G) H) ⊓ C :=
          le_inf (le_inf (le_trans inf_le_left inf_le_left)
            (le_trans inf_le_right inf_le_left)) (le_trans inf_le_left inf_le_right)
        have h2 : (H ⊓ Submission.Blueprint.conj (x : G) H) ⊓ C
            ≤ (H ⊓ C) ⊓ (Submission.Blueprint.conj (x : G) H ⊓ C) :=
          le_inf (le_inf (le_trans inf_le_left inf_le_left) inf_le_right)
            (le_inf (le_trans inf_le_left inf_le_right) inf_le_right)
        exact le_antisymm h1 h2
      rw [hM, hconj]
      rw [← subgroupOf_inf (H ⊓ C) (Submission.Blueprint.conj (x : G) H ⊓ C) C, hGC]
    refine ⟨(Q ⊓ C).subgroupOf C, ?_, ?_, ?_, ?_⟩
    · rw [hM]
      intro q hq
      rw [Subgroup.mem_subgroupOf] at hq ⊢
      exact ⟨h.le (Subgroup.mem_inf.mp hq).1, (Subgroup.mem_inf.mp hq).2⟩
    · rw [hM]
      intro m hm
      rw [Subgroup.mem_subgroupOf] at hm
      rw [Subgroup.mem_normalizer_iff]
      intro q
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      show (q : G) ∈ Q ⊓ C ↔ ((m * q * m⁻¹ : C) : G) ∈ Q ⊓ C
      have hcoe : ((m * q * m⁻¹ : C) : G) = (m : G) * (q : G) * (m : G)⁻¹ := rfl
      rw [hcoe]
      exact conj_iff_mem_inf_centralizer hm.1 hm.2 h.normal q
    · -- `C_Q(X) ⊓ (M ⊓ M^x) = 1`
      have hbot : (Q ⊓ C) ⊓ ((H ⊓ Submission.Blueprint.conj (x : G) H) ⊓ C) = ⊥ := by
        rw [eq_bot_iff]
        rintro q ⟨⟨hqQ, -⟩, ⟨⟨-, hqHx⟩, -⟩⟩
        have hmem : q ∈ Q ⊓ Submission.Blueprint.conj (x : G) H := ⟨hqQ, hqHx⟩
        rw [hQinf] at hmem
        simpa using hmem
      rw [hconjM, ← subgroupOf_inf (Q ⊓ C) ((H ⊓ Submission.Blueprint.conj (x : G) H) ⊓ C) C,
        hbot, subgroupOf_bot]
    · -- `C_Q(X) · (M ⊓ M^x) = M`
      have hXD : X ≤ H ⊓ Submission.Blueprint.conj (x : G) H := by
        refine fun y hy => Subgroup.mem_inf.mpr ⟨hXH hy, ?_⟩
        rw [Work.DoubleTransitivity.mem_conj]
        have hcomm : y * (x : G) = (x : G) * y := Subgroup.mem_centralizer_iff.mp x.2 y hy
        have h1 : (x : G)⁻¹ * y * (x : G) = y := by
          calc (x : G)⁻¹ * y * (x : G) = (x : G)⁻¹ * (y * (x : G)) := by group
            _ = (x : G)⁻¹ * ((x : G) * y) := by rw [hcomm]
            _ = y := by group
        rw [h1]
        exact hXH hy
      have hQinf' : Q ⊓ (H ⊓ Submission.Blueprint.conj (x : G) H) = ⊥ := by
        rw [eq_bot_iff]
        rintro q ⟨hqQ, -, hqHx⟩
        have hmem : q ∈ Q ⊓ Submission.Blueprint.conj (x : G) H := ⟨hqQ, hqHx⟩
        rw [hQinf] at hmem
        simpa using hmem
      have hsplit : H ⊓ C
          = (Q ⊓ C) ⊔ ((H ⊓ Submission.Blueprint.conj (x : G) H) ⊓ C) :=
        lemma2a_cent_split (D := H ⊓ Submission.Blueprint.conj (x : G) H) h.normal hQinf'
          (sup_Q_inf_conj_eq h x.2 hxH) hXD
      rw [hconjM, hM]
      refine le_antisymm (sup_le ?_ ?_) ?_
      · intro q hq
        have hq' : (q : G) ∈ Q ⊓ C := Subgroup.mem_subgroupOf.mp hq
        exact Subgroup.mem_subgroupOf.mpr ⟨h.le hq'.1, hq'.2⟩
      · intro q hq
        have hq' : (q : G) ∈ (H ⊓ Submission.Blueprint.conj (x : G) H) ⊓ C :=
          Subgroup.mem_subgroupOf.mp hq
        exact Subgroup.mem_subgroupOf.mpr ⟨hq'.1.1, hq'.2⟩
      · -- conversely: compare inside `G` after mapping along `C.subtype` (injective)
        have key : ∀ X Y : Subgroup C, X.map C.subtype ≤ Y.map C.subtype → X ≤ Y := by
          intro X Y h Z hZ
          obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (h (Subgroup.mem_map_of_mem C.subtype hZ))
          have hzZ : z = Z := Subtype.ext hzy
          rwa [hzZ] at hz
        refine key _ _ ?_
        have hMC : (H ⊓ C) ⊓ C = H ⊓ C := by rw [inf_assoc, inf_idem]
        have hQC : (Q ⊓ C) ⊓ C = Q ⊓ C := by rw [inf_assoc, inf_idem]
        have hBC : ((H ⊓ Submission.Blueprint.conj (x : G) H) ⊓ C) ⊓ C
            = (H ⊓ Submission.Blueprint.conj (x : G) H) ⊓ C := by rw [inf_assoc, inf_idem]
        rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
          Subgroup.subgroupOf_map_subtype, hMC, hQC, hBC]
        exact le_of_eq hsplit

end Work.ThmF.ChV12
