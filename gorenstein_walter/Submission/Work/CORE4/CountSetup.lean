/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — the §4 configuration, first structural steps

These are the first structural facts about Bender's §4 configuration (`Case2Ctx B`), salvaged from
the partial development of the `Case2Count` leaf:

* `layer_normal`, `layerIn_le`, `layerIn_le_normalizer` — `E(K) ⊴ K` and `K ≤ N_G(E(K))`;
* `normalizer_layerIn_eq` — `N_G(E(M)) = M` (simplicity of `G` + `M` a coatom);
* `M_eq_layerIn_sup` — `M = E(M)·C_M(t)`, Bender's first paragraph of §4 (p. 224), using §4 (1)
  (`OneInvClassIn (layerIn D.M)`);
* `Case2Count_iff_no_config`, `no_case2_tuple` — machine-checked records that the conclusion of
  `Case2CountImpl` is unsatisfiable (by the proved `Case2ArithProp`), so that
  `Case2CountImpl` + `Case2ArithProp` is exactly the elimination of §4.

The remaining content of §4 (7)–(12) is the leaf `Submission.Work.CORE4.Case2Count`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Arith

open scoped MatrixGroups

namespace Work.CORE4

open Work.GW2 Subgroup

/-! ## 1. Elementary structure of the §4 configuration

`E := layerIn D.M` is the layer of the maximal subgroup `M`; `nine` identifies it with
`L₂(q)`, `E ⊴ M`, and (because `G` is simple and `M` is a coatom) `N_G(E) = M`. -/

theorem layer_normal {G : Type*} [Group G] (K : Subgroup G) : (layer ↥K).Normal := by
  change (sSup {E : Subgroup ↥K | E.Normal ∧ IsQuasisimple E}).Normal
  exact Subgroup.sSup_normal _ (fun H hH => hH.1)

theorem layerIn_le_normalizer {G : Type*} [Group G] (K : Subgroup G) :
    K ≤ Subgroup.normalizer ((layerIn K : Subgroup G) : Set G) := by
  have hnorm : (layer ↥K).Normal := layer_normal K
  rw [Subgroup.le_normalizer_iff]
  intro m hm x hx
  rw [layerIn] at hx ⊢
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, Subgroup.Normal.conj_mem hnorm y hy ⟨m, hm⟩, by simp⟩

theorem layerIn_le {G : Type*} [Group G] (K : Subgroup G) : layerIn K ≤ K :=
  Subgroup.map_subtype_le _

/-- `N_G(E(M)) = M` for the §4 configuration. -/
theorem normalizer_layerIn_eq {G : Type} [Group G] [Finite G] {B : BenderSetup G}
    (hbc : BenderCtx G) (h : Case2Ctx B) :
    Subgroup.normalizer ((layerIn h.D.M : Subgroup G) : Set G) = h.D.M := by
  haveI : IsSimpleGroup G := hbc.simple
  set E : Subgroup G := layerIn h.D.M with hE
  have hME : h.D.M ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE]; exact layerIn_le_normalizer h.D.M
  have hEbot : E ≠ ⊥ := by
    intro hbot
    have ht : B.t ∈ E := by rw [hE]; exact h.D.t_mem
    rw [hbot] at ht
    simp only [Subgroup.mem_bot] at ht
    have h2 : orderOf B.t = 1 := by rw [ht]; simp
    exact absurd (h2.symm.trans B.t_order) (by norm_num)
  have hEDM : E ≤ h.D.M := by rw [hE]; exact layerIn_le h.D.M
  have hEtop : E ≠ ⊤ := fun htop => h.D.M_coatom.ne_top (top_le_iff.mp (htop ▸ hEDM))
  have hNtop : Subgroup.normalizer (E : Set G) ≠ ⊤ := by
    intro htop
    have hnorm : E.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases hnorm.eq_bot_or_eq_top with hb | ht
    · exact hEbot hb
    · exact hEtop ht
  have hNle : Subgroup.normalizer (E : Set G) ≤ h.D.M := by
    by_contra hcon
    have hne : h.D.M ≠ Subgroup.normalizer (E : Set G) := fun hh => hcon (le_of_eq hh.symm)
    have hlt : h.D.M < Subgroup.normalizer (E : Set G) := lt_of_le_of_ne hME hne
    exact hNtop (h.D.M_coatom.2 _ hlt)
  exact le_antisymm hNle hME

/-- `M = E(M) · C_M(t)` (Bender §4, first paragraph: `E` has one class of involutions). -/
theorem M_eq_layerIn_sup {G : Type} [Group G] [Finite G] {B : BenderSetup G}
    (hbc : BenderCtx G) (h : Case2Ctx B) :
    h.D.M = layerIn h.D.M ⊔ (h.D.M ⊓ B.H) := by
  set E : Subgroup G := layerIn h.D.M with hE
  have hEM : E ≤ h.D.M := by rw [hE]; exact layerIn_le h.D.M
  have hnorm : h.D.M ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE]; exact layerIn_le_normalizer h.D.M
  refine le_antisymm ?_ (sup_le hEM inf_le_left)
  intro g hg
  have hconj : g * B.t * g⁻¹ ∈ E :=
    Subgroup.le_normalizer_iff.mp hnorm g hg B.t h.D.t_mem
  have horder : orderOf (g * B.t * g⁻¹) = 2 := by
    have hconj_eq : g * B.t * g⁻¹ = (MulAut.conj g) B.t := by simp [MulAut.conj_apply]
    rw [hconj_eq, ← B.t_order, orderOf_eq_orderOf_iff]
    intro n
    rw [← map_pow]
    exact (MulAut.conj g).map_eq_one_iff
  obtain ⟨d, hd, hconjd⟩ :=
    h.pre.2.1 (g * B.t * g⁻¹) ⟨hconj, horder⟩ B.t ⟨h.D.t_mem, B.t_order⟩
  have hdM : d ∈ h.D.M := hEM hd
  have hcen : d * g ∈ B.H := by
    show d * g ∈ Subgroup.centralizer ({B.t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hX : (d * g) * B.t * (d * g)⁻¹ = B.t := by
      rw [show (d * g) * B.t * (d * g)⁻¹ = d * (g * B.t * g⁻¹) * d⁻¹ by group]
      exact hconjd
    calc (d * g) * B.t = ((d * g) * B.t * (d * g)⁻¹) * (d * g) := by group
      _ = B.t * (d * g) := by rw [hX]
  have hmem : d * g ∈ h.D.M ⊓ B.H := ⟨h.D.M.mul_mem hdM hg, hcen⟩
  have hgoal : g = d⁻¹ * (d * g) := by group
  rw [hgoal]
  exact Subgroup.mul_mem_sup (E.inv_mem hd) hmem

/-! ## 2. The statement is equivalent to the non-existence of the §4 configuration -/

/-- Machine-checked record of the observation in the file header: because the conclusion of
`Case2CountImpl` is unsatisfiable (by the proved `Case2ArithProp`), the leaf is *equivalent* to
the assertion that Bender's §4 configuration does not occur. -/
theorem Case2Count_iff_no_config (I : C4Inputs) :
    Case2CountImpl I ↔
      (∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G,
        Case2 B → Case2Ctx B → False) := by
  constructor
  · intro h G _ _ hbc B h2 hctx
    obtain ⟨q, k, k', p, p0, p1, u, hq, hqodd, hcases, hkeven, hp, hp03, hp0odd, hp01, hp1,
      hpp0, h2p, hu1, hup, hineq⟩ := h G hbc B h2 hctx
    exact case2Arith q k k' p p0 p1 u hq hqodd hcases hkeven hp hp03 hp0odd hp01 hp1 hpp0 h2p
      hu1 hup hineq
  · intro h G _ _ hbc B h2 hctx
    exact (h G hbc B h2 hctx).elim

/-- The conclusion of the leaf is empty: no tuple of natural numbers satisfies the printed
hypotheses together with (12).  This is a direct consequence of the proved `Case2ArithProp`. -/
theorem no_case2_tuple :
    ¬ ∃ (q k k' p p0 p1 u : ℕ), 7 ≤ q ∧ Odd q ∧
      ((2 * k = q + 1 ∧ 2 * k' = q - 1) ∨ (2 * k = q - 1 ∧ 2 * k' = q + 1)) ∧ Even k ∧
      p.Prime ∧ 3 ≤ p0 ∧ Odd p0 ∧ p0 ≤ p1 ∧ p1 ≤ p + 1 ∧ p0 ≤ p ∧ 2 * p ≤ k ∧ 1 ≤ u ∧ u ≤ p ∧
      (((q * k' * (p1 - 1) * (q * k')) : ℚ) *
          (((p1 : ℚ) - 1) * ((q : ℚ) * k' - 1) - ((q : ℚ) - 1) * q / p) ≤
        6 * (k : ℚ) ^ 2 * (u : ℚ) ^ 3 * (p0 : ℚ) ^ 3) := by
  rintro ⟨q, k, k', p, p0, p1, u, hq, hqodd, hcases, hkeven, hp, hp03, hp0odd, hp01, hp1,
    hpp0, h2p, hu1, hup, hineq⟩
  exact case2Arith q k k' p p0 p1 u hq hqodd hcases hkeven hp hp03 hp0odd hp01 hp1 hpp0 h2p
    hu1 hup hineq


end Work.CORE4
