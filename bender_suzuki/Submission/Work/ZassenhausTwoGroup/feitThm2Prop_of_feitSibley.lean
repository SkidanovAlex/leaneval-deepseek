import Mathlib
import Submission.Work.ZassenhausTwoGroup.Defs
import Submission.Work.ZassenhausTwoGroup.FeitThm2
import Submission.Work.ZassenhausTwoGroup.FeitSibleyBridge
import Submission.Work.ZassenhausTwoGroup.exceptional_data
import Submission.Work.ZassenhausTwoGroup.cfInner_indLin_diff
import Submission.Work.ZassenhausTwoGroup.fpf_on_Q
import Submission.Work.ZassenhausTwoGroup.isTI_Q
import Submission.Work.ZassenhausTwoGroup.coprime_card
import Submission.Work.ZassenhausTwoGroup.twoPoint_ne_bot
import Submission.Work.ZassenhausTwoGroup.even_card_Q
import Submission.Work.ZassenhausTwoGroup.normalizer_Q_eq
import Submission.Work.CharCore.Main
import Submission.Work.Induction.All
import Submission.Work.Coherence.All
import Submission.Work.Clifford.All
import Submission.Work.FeitSibley.Defs
import Submission.Work.FeitSibley.CharQ.Defs
import Submission.Work.FeitSibley.CharQ.ScriptSAPI
import Submission.Work.FeitSibley.CharQ.scriptS_eq_image
import Submission.Work.FeitSibley.CharQ.isometry_indLin
import Submission.Work.FeitSibley.CharQ.degree_D_scriptS
import Submission.Work.FeitSibley.CharQ.two_le_card_scriptS
import Submission.Work.Coherence.cfInner_eq_zero_of_two_coherent_blocks_vchar
import Submission.Work.FeitSibley.Coherence.exists_nontrivial_linear_irr
import Submission.Work.FeitSibley.Coherence.congr_aux
import Submission.Work.NormalComplement.rat_eq_int_of_isIntegral
import Submission.Work.ZassenhausTwoGroup.indFun_Q_apply_mem_Q
import Submission.Work.ZassenhausTwoGroup.card_H_classes_eq_card_induced
import Submission.Work.ZassenhausTwoGroup.zetaStar_aux
import Submission.Work.ZassenhausTwoGroup.conj_mem_Q_iff
import Submission.Work.CharCore.resFun_int_const_of_cfInner_ratio
import Submission.Work.FeitSibley.CharQ.indQH_deg
import Submission.Work.FeitSibley.CharQ.card_fibre_indQH
import Submission.Work.FeitSibley.CharQ.indQH_apply_mem_Q

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open Classical
open Submission.Blueprint

namespace Work.ZassenhausTwoGroup

/-- **Feit–Sibley gives coherence of `𝓢 = {χ ∈ Irr H | Q ⊄ ker χ}`** in the rank-one
Zassenhaus set-up with `Q` not a `2`-group.

This is `FeitSibleyProp` applied with `(H, Q, D, S, Q₁) = (H, Q, twoPoint H t, ⊥, Q)`:
the direct factor `S = 1`, `Q₁ = Q`. -/
theorem coherent_S {G : Type} [Group G] [Fintype G] (hFS : FeitSibleyProp)
    {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (hQ2 : ¬ IsPGroup 2 Q) :
    2 ≤ (excludingKernel H Q).card ∧
      Work.Coherence.Coherent (excludingKernel H Q) (indLinear H) :=
  hFS G H Q (twoPoint H t) ⊥ Q
    (ne_top_of_stronglyEmbedded h.stronglyEmbedded) h.le h.normal (twoPoint_le_H h)
    h.inf_eq h.sup_eq (coprime_card h hz) (isTI_Q h hz)
    (bot_sup_eq Q) (bot_inf_eq Q) (by simp) (by simp)
    inferInstance (fpf_on_Q h hz) hQ2 (odd_card_twoPoint h.stronglyEmbedded h.not_mem)

/-- In the rank-one Zassenhaus set-up with `Q` not a `2`-group, the Feit–Sibley data of the
area: `H = Q ⋊ D` with `D = twoPoint H t`, `S = 1`, `Q₁ = Q`. -/
@[reducible] noncomputable def fsData {G : Type} [Group G] [Fintype G]
    {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H) (hQ2 : ¬ IsPGroup 2 Q) :
    Work.FeitSibley.FSData G where
  H := H
  Q := Q
  D := twoPoint H t
  S := ⊥
  Q1 := Q
  H_ne_top := ne_top_of_stronglyEmbedded h.stronglyEmbedded
  Q_le_H := h.le
  Q_normal_in_H := h.normal
  D_le_H := twoPoint_le_H h
  Q_inf_D := h.inf_eq
  Q_sup_D := h.sup_eq
  coprime_D_Q := coprime_card h hz
  Q_TI := isTI_Q h hz
  S_sup_Q1 := bot_sup_eq Q
  S_inf_Q1 := bot_inf_eq Q
  commute := by intro a ha b hb; rw [Subgroup.mem_bot] at ha; subst ha; simp
  coprime_S_Q1 := by simp
  S_nilpotent := inferInstance
  D_fpf_Q1 := fpf_on_Q h hz
  Q1_not_two := hQ2
  D_odd := odd_card_twoPoint h.stronglyEmbedded h.not_mem

@[simp] theorem fsData_H {G : Type} [Group G] [Fintype G]
    {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q) : (fsData h hz hQ2).H = H := rfl

@[simp] theorem fsData_Q {G : Type} [Group G] [Fintype G]
    {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q) : (fsData h hz hQ2).Q = Q := rfl

@[simp] theorem fsData_Q1 {G : Type} [Group G] [Fintype G]
    {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q) : (fsData h hz hQ2).Q1 = Q := rfl

@[simp] theorem fsData_D {G : Type} [Group G] [Fintype G]
    {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q) : (fsData h hz hQ2).D = twoPoint H t := rfl

/-- The `scriptS`/`excludingKernel` set of the Feit–Sibley data coincides with the area's. -/
theorem fsData_scriptS {G : Type} [Group G] [Fintype G]
    {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) (hz : IsZassenhaus H)
    (hQ2 : ¬ IsPGroup 2 Q) :
    Work.FeitSibley.scriptS (fsData h hz hQ2).H (fsData h hz hQ2).Q1 = excludingKernel H Q :=
  rfl

/-- **Feit's Theorem 2 from Feit–Sibley coherence.** -/
theorem feitThm2Prop_of_feitSibley (hFS : FeitSibleyProp) (hTh : ThompsonFrobeniusProp) :
    FeitThm2Prop := by
  intro G _ _ hsimple H Q t h hz hQ2 hne
  classical
  obtain ⟨hcard, hcoh⟩ := coherent_S hFS h hz hQ2
  -- the Feit–Sibley data with `S = 1`, `Q₁ = Q`
  let h' : Work.FeitSibley.FSData G := fsData h hz hQ2
  -- the coherent set `𝓢 = excludingKernel H Q`
  let S : Finset (↥H → ℂ) := excludingKernel H Q
  have hcoh' : Work.Coherence.Coherent S (indLin H) := hcoh
  obtain ⟨τ', hτ'0, hτ'iso, hτ'vchar⟩ := hcoh'
  -- `τ' α 1 = 0` for `α ∈ ℤ[𝓢]°`
  have hτV : ∀ α ∈ Work.Coherence.ZSpan0 S, (indLin H) α 1 = 0 := by
    intro α hα
    have h0 : α 1 = 0 := hα.2
    rw [indLin_apply, Work.Induction.indFun_apply_one, h0, mul_zero]
  -- the elements of `𝓢` are irreducible characters of `H`
  have hIrrS : ∀ x ∈ S, x ∈ Work.CharCore.Irr ↥H :=
    fun x hx => (Finset.mem_filter.mp hx).1
  -- **the uniform sign**
  obtain ⟨δ, hδsq, hδ⟩ := Work.Coherence.uniform_sign_of_isometry_vchar
    (S := S) (X := S) (τ := indLin H) (σ := τ') (Finset.Subset.refl _) hIrrS hτV
    (fun α hα => hτ'0 α hα) hτ'iso
    (fun x hx => (Work.CharCore.IsVChar_iff_coherence (τ' x)).mpr (hτ'vchar x hx)) hcard
  have hδpm : δ = 1 ∨ δ = -1 := mul_self_eq_one_iff.mp hδsq
  -- the integer incarnation of `δ`
  obtain ⟨εz, hεz, hεzpm⟩ : ∃ ε : ℤ, (ε : ℂ) = δ ∧ (ε = 1 ∨ ε = -1) := by
    rcases hδpm with h | h
    · exact ⟨1, by simp [h], Or.inl rfl⟩
    · exact ⟨-1, by simp [h], Or.inr rfl⟩
  -- the exceptional-character map
  let chi : (↥Q → ℂ) → G → ℂ := fun ζ => δ • τ' (h'.indQH ζ)
  -- `τ' (indQH ζ) = δ • chi ζ`
  have hτ'chi : ∀ ζ : ↥Q → ℂ, τ' (h'.indQH ζ) = δ • chi ζ := by
    intro ζ
    show τ' (h'.indQH ζ) = δ • (δ • τ' (h'.indQH ζ))
    rw [smul_smul, hδsq, one_smul]
  -- degree of `indQH`
  have hindQH_deg : ∀ ζ : ↥Q → ℂ,
      h'.indQH ζ 1 = (Nat.card (twoPoint H t) : ℂ) * ζ 1 := by
    intro ζ
    have h1 : h'.indQH ζ = Work.Induction.indFun (h'.Q.subgroupOf h'.H)
        (Work.FeitSibley.CharQ.pull h' ζ) := rfl
    rw [h1, Work.Induction.indFun_apply_one, Work.FeitSibley.CharQ.pull_one,
      show (h'.Q.subgroupOf h'.H).index = Nat.card h'.D from
        Work.FeitSibley.Coherence.index_subgroupOf_Q h']
  -- **membership: `Ind_Q^H ζ ∈ 𝓢` for `ζ ≠ 1`**
  have hmemS : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → h'.indQH ζ ∈ S := by
    intro ζ hζ hζ1
    show h'.indQH ζ ∈ Work.FeitSibley.scriptS h'.H h'.Q1
    rw [Work.FeitSibley.CharQ.scriptS_eq_image h']
    refine ⟨ζ, hζ, ?_, rfl⟩
    by_cases hex : ∃ x : ↥Q, ζ x ≠ ζ 1
    · obtain ⟨x, hx⟩ := hex
      exact ⟨⟨(x : G), x.2⟩, by simpa using x.2, hx⟩
    · push_neg at hex
      exact absurd (Work.FeitSibley.CharQ.eq_principal_of_irr_of_constant hζ hex) hζ1
  -- **every element of `𝓢` is `Ind_Q^H ζ`**
  have hSimage : ∀ x ∈ S, ∃ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 ∧ x = h'.indQH ζ := by
    intro x hx
    have hx' : x ∈ Work.FeitSibley.scriptS h'.H h'.Q1 := hx
    rw [Work.FeitSibley.CharQ.scriptS_eq_image h'] at hx'
    obtain ⟨ζ, hζ, hw, hxζ⟩ := hx'
    refine ⟨ζ, hζ, ?_, hxζ⟩
    rintro rfl
    obtain ⟨x, -, hne⟩ := hw
    exact hne rfl
  -- **transitivity of induction**
  have hindQH_trans : ∀ ζ : ↥Q → ℂ,
      Work.Induction.indFun H (h'.indQH ζ) = Work.Induction.indFun Q ζ := by
    intro ζ
    have h1 : h'.indQH ζ = Work.Induction.indFun (h'.Q.subgroupOf h'.H)
        (Work.FeitSibley.CharQ.pull h' ζ) := rfl
    rw [h1]
    have := Work.Induction.indFun_trans (K := Q) (H := H) h.le ζ
    convert this using 2
    ext x
    rfl
  -- **(a): `χ ζ` is irreducible**
  have ha : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → chi ζ ∈ Work.CharCore.Irr G := by
    intro ζ hζ hζ1
    have := hδ (h'.indQH ζ) (hmemS ζ hζ hζ1)
    change δ • τ' (h'.indQH ζ) ∈ Work.CharCore.Irr G
    exact this
  -- **(b): the value relation of Theorem 2**
  have hb : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' →
      ∀ g : G, (ζ' 1) * Work.Induction.indFun Q ζ g
          - (ζ 1) * Work.Induction.indFun Q ζ' g
        = (εz : ℂ) * ((ζ' 1) * chi ζ g - (ζ 1) * chi ζ' g) := by
    intro ζ hζ hζ1 ζ' hζ' hζ'1 hne' g
    set d : ℕ := Work.CharCore.irrDeg ζ with hddef
    set d' : ℕ := Work.CharCore.irrDeg ζ' with hd'def
    have hz : ζ 1 = (d : ℂ) := by rw [hddef]; exact Work.CharCore.irrDeg_spec hζ
    have hz' : ζ' 1 = (d' : ℂ) := by rw [hd'def]; exact Work.CharCore.irrDeg_spec hζ'
    -- the degree-zero element `d' • indQH ζ - d • indQH ζ'`
    let Ψ : ↥H → ℂ := (d' : ℤ) • h'.indQH ζ - (d : ℤ) • h'.indQH ζ'
    have hθ : Ψ ∈ Work.Coherence.ZSpan0 S := by
      refine ⟨?_, ?_⟩
      · exact AddSubgroup.sub_mem _
          (AddSubgroup.zsmul_mem _ (Work.Coherence.self_mem_zSpan (hmemS ζ hζ hζ1)) _)
          (AddSubgroup.zsmul_mem _ (Work.Coherence.self_mem_zSpan (hmemS ζ' hζ' hζ'1)) _)
      · show ((d' : ℤ) • h'.indQH ζ - (d : ℤ) • h'.indQH ζ') 1 = 0
        simp only [Pi.sub_apply, Pi.smul_apply]
        simp only [zsmul_eq_mul, Int.cast_natCast]
        rw [hindQH_deg ζ, hindQH_deg ζ', hz, hz']
        ring
    have hτθ : τ' Ψ = (indLin H) Ψ := hτ'0 Ψ hθ
    have hΨ : Ψ = (d' : ℂ) • h'.indQH ζ - (d : ℂ) • h'.indQH ζ' := by
      have h1 : (d' : ℤ) • h'.indQH ζ = (d' : ℂ) • h'.indQH ζ := by
        ext x; simp only [Pi.smul_apply, zsmul_eq_mul, Int.cast_natCast, smul_eq_mul]
      have h2 : (d : ℤ) • h'.indQH ζ' = (d : ℂ) • h'.indQH ζ' := by
        ext x; simp only [Pi.smul_apply, zsmul_eq_mul, Int.cast_natCast, smul_eq_mul]
      show (d' : ℤ) • h'.indQH ζ - (d : ℤ) • h'.indQH ζ'
        = (d' : ℂ) • h'.indQH ζ - (d : ℂ) • h'.indQH ζ'
      rw [h1, h2]
    have hA : (indLin H) Ψ g
        = (d' : ℂ) * Work.Induction.indFun Q ζ g - (d : ℂ) * Work.Induction.indFun Q ζ' g := by
      have h1 : (indLin H) Ψ
          = (d' : ℂ) • (Work.Induction.indFun Q ζ)
            - (d : ℂ) • (Work.Induction.indFun Q ζ') := by
        rw [hΨ]
        show Work.Induction.indFun H ((d' : ℂ) • h'.indQH ζ - (d : ℂ) • h'.indQH ζ')
          = (d' : ℂ) • Work.Induction.indFun Q ζ - (d : ℂ) • Work.Induction.indFun Q ζ'
        rw [Work.Induction.indFun_sub, Work.Induction.indFun_smul, Work.Induction.indFun_smul,
          hindQH_trans ζ, hindQH_trans ζ']
      rw [h1]
      simp only [Pi.sub_apply, Pi.smul_apply]
      simp only [smul_eq_mul]
    have hB : τ' Ψ g = δ * ((d' : ℂ) * chi ζ g - (d : ℂ) * chi ζ' g) := by
      have h1 : τ' Ψ = (d' : ℤ) • τ' (h'.indQH ζ) - (d : ℤ) • τ' (h'.indQH ζ') := by
        rw [map_sub, map_zsmul, map_zsmul]
      rw [h1, hτ'chi ζ, hτ'chi ζ']
      simp only [Pi.sub_apply, Pi.smul_apply]
      simp only [zsmul_eq_mul, Int.cast_natCast, smul_eq_mul]
      ring
    have key : (d' : ℂ) * Work.Induction.indFun Q ζ g - (d : ℂ) * Work.Induction.indFun Q ζ' g
        = δ * ((d' : ℂ) * chi ζ g - (d : ℂ) * chi ζ' g) :=
      calc (d' : ℂ) * Work.Induction.indFun Q ζ g - (d : ℂ) * Work.Induction.indFun Q ζ' g
          = (indLin H) Ψ g := hA.symm
        _ = τ' Ψ g := congrFun hτθ g |>.symm
        _ = δ * ((d' : ℂ) * chi ζ g - (d : ℂ) * chi ζ' g) := hB
    rw [hz, hz', hεz]
    exact key
  -- **(c): Corollary 2.1**
  have hc21 : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ ζ' ∈ Work.CharCore.Irr ↥Q, ζ' ≠ 1 →
      Work.Induction.indFun Q ζ ≠ Work.Induction.indFun Q ζ' →
      ∀ g : G, (¬ ∃ x : G, x * g * x⁻¹ ∈ Q ∧ x * g * x⁻¹ ≠ 1) →
        (ζ' 1) * chi ζ g - (ζ 1) * chi ζ' g = 0 := by
    intro ζ hζ hζ1 ζ' hζ' hζ'1 hne' g hg
    have hbij := hb ζ hζ hζ1 ζ' hζ' hζ'1 hne' g
    have hL : (ζ' 1) * Work.Induction.indFun Q ζ g
        - (ζ 1) * Work.Induction.indFun Q ζ' g = 0 := by
      by_cases hg1 : g = 1
      · subst hg1
        rw [Work.Induction.indFun_apply_one, Work.Induction.indFun_apply_one]
        ring
      · have hgQ : ∀ x : G, x * g * x⁻¹ ∉ Q := by
          intro x hxq
          refine hg ⟨x, hxq, fun h1 => hg1 ?_⟩
          calc g = x⁻¹ * (x * g * x⁻¹) * x := by group
            _ = x⁻¹ * 1 * x := by rw [h1]
            _ = 1 := by simp
        rw [Work.Induction.indFun_apply_eq_zero Q ζ g hgQ,
          Work.Induction.indFun_apply_eq_zero Q ζ' g hgQ]
        ring
    have hεz0 : (εz : ℂ) ≠ 0 := by
      rcases hεzpm with h | h <;> rw [h] <;> norm_num
    rw [hL] at hbij
    exact (mul_eq_zero.mp hbij.symm).resolve_left hεz0
  -- a nontrivial **linear** character of `Q`
  have hnil : Group.IsNilpotent ↥Q := isNilpotent_Q hTh h hz (twoPoint_ne_bot h hz)
  haveI : Nontrivial ↥Q := by
    have h2 : 1 < Fintype.card ↥Q := by
      rw [← Nat.card_eq_fintype_card]
      obtain ⟨k, hk⟩ := even_card_Q h
      have hpos : 0 < Nat.card ↥Q := Nat.card_pos
      omega
    obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp h2
    exact ⟨a, b, hab⟩
  obtain ⟨lam0, hlam0Irr, hlam0deg, hlam0ne⟩ :=
    Work.FeitSibley.Coherence.exists_nontrivial_linear_irr ↥Q
  -- **the criterion**: a non-exceptional irreducible is orthogonal to `τ'(ℤ[𝓢]°)`
  have hcrit : ∀ ψ ∈ Work.CharCore.Irr G, (∀ x ∈ S, δ • τ' x ≠ ψ) →
      ∀ θ ∈ Work.Coherence.ZSpan0 S, Work.CharCore.cfInner (τ' θ) ψ = 0 := by
    intro ψ hψ hne θ hθ
    obtain ⟨c, hc⟩ := Work.Coherence.mem_zSpan.mp (Work.Coherence.zSpan0_le_zSpan S hθ)
    have hτθ : τ' θ = ∑ x : S, (c x : ℂ) • τ' (x : ↥H → ℂ) := by
      rw [hc, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Int.cast_smul_eq_zsmul ℂ (c x), map_zsmul, ← Int.cast_smul_eq_zsmul ℂ (c x)]
    rw [hτθ, Work.CharCore.cfInner_sum_smul_left]
    refine Finset.sum_eq_zero fun x _ => ?_
    have hxmem : (x : ↥H → ℂ) ∈ S := x.2
    have hmem : δ • τ' (x : ↥H → ℂ) ∈ Work.CharCore.Irr G := hδ _ hxmem
    have hτx : τ' (x : ↥H → ℂ) = δ • (δ • τ' (x : ↥H → ℂ)) := by
      rw [smul_smul, hδsq, one_smul]
    rw [hτx, Work.CharCore.cfInner_smul_left,
      Work.CharCore.irr_orthonormal _ _ hmem hψ, if_neg (hne _ hxmem)]
    ring
  -- **the restriction relation**: from `⟨τ'θ, V⟩ = 0` on `ℤ[𝓢]°` deduce the ratio relation for
  -- `Res_Q V`
  have hres_rel : ∀ (V : G → ℂ), Work.CharCore.IsClassFun V →
      (∀ θ ∈ Work.Coherence.ZSpan0 S, Work.CharCore.cfInner (τ' θ) V = 0) →
      ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 →
        (lam0 1) * Work.CharCore.cfInner ζ (Work.Induction.resFun Q V)
          = (ζ 1) * Work.CharCore.cfInner lam0 (Work.Induction.resFun Q V) := by
    intro V hVc horth0 ζ hζ hζ1
    set z : ℕ := Work.CharCore.irrDeg ζ with hzdef
    have hz : ζ 1 = (z : ℂ) := by rw [hzdef]; exact Work.CharCore.irrDeg_spec hζ
    have hθ : (h'.indQH ζ - (z : ℤ) • h'.indQH lam0) ∈ Work.Coherence.ZSpan0 S := by
      refine ⟨?_, ?_⟩
      · exact AddSubgroup.sub_mem _
          (Work.Coherence.self_mem_zSpan (hmemS ζ hζ hζ1))
          (AddSubgroup.zsmul_mem _ (Work.Coherence.self_mem_zSpan (hmemS lam0 hlam0Irr hlam0ne)) _)
      · show (h'.indQH ζ - (z : ℤ) • h'.indQH lam0) 1 = 0
        simp only [Pi.sub_apply, Pi.smul_apply]
        simp only [zsmul_eq_mul, Int.cast_natCast]
        rw [hindQH_deg ζ, hindQH_deg lam0, hz, hlam0deg]
        ring
    have h0 : Work.CharCore.cfInner (τ' (h'.indQH ζ - (z : ℤ) • h'.indQH lam0)) V = 0 :=
      horth0 _ hθ
    -- two Frobenius reciprocity steps
    have step : ∀ ξ : ↥Q → ℂ, Work.CharCore.IsClassFun ξ →
        Work.CharCore.cfInner (h'.indQH ξ) (Work.Induction.resFun H V)
          = Work.CharCore.cfInner ξ (Work.Induction.resFun Q V) := by
      intro ξ hξ
      rw [← Work.Induction.frobenius_reciprocity H (h'.indQH ξ) V hVc]
      rw [hindQH_trans ξ, Work.Induction.frobenius_reciprocity Q ξ V hVc]
    have hξ1 : Work.CharCore.IsClassFun ζ :=
      Work.CharCore.isClassFun_of_mem_Irr hζ
    have hξ2 : Work.CharCore.IsClassFun lam0 :=
      Work.CharCore.isClassFun_of_mem_Irr hlam0Irr
    have hconv : Work.CharCore.cfInner ((z : ℤ) • h'.indQH lam0) (Work.Induction.resFun H V)
        = (z : ℂ) * Work.CharCore.cfInner (h'.indQH lam0) (Work.Induction.resFun H V) := by
      rw [← Int.cast_smul_eq_zsmul ℂ (z : ℤ), Work.CharCore.cfInner_smul_left,
        Int.cast_natCast]
    have hval : Work.CharCore.cfInner (τ' (h'.indQH ζ - (z : ℤ) • h'.indQH lam0)) V
        = Work.CharCore.cfInner ζ (Work.Induction.resFun Q V)
          - (z : ℂ) * Work.CharCore.cfInner lam0 (Work.Induction.resFun Q V) := by
      rw [hτ'0 _ hθ, indLin_apply,
        Work.Induction.frobenius_reciprocity H _ V hVc,
        Work.CharCore.cfInner_sub_left, hconv, step ζ hξ1, step lam0 hξ2]
    rw [hval] at h0
    have h0' : Work.CharCore.cfInner ζ (Work.Induction.resFun Q V)
        = (z : ℂ) * Work.CharCore.cfInner lam0 (Work.Induction.resFun Q V) :=
      sub_eq_zero.mp h0
    rw [hlam0deg, one_mul, h0', hz]
  -- **(e): non-exceptional irreducible characters are constant on `Q ∖ 1`**
  have he : ∀ φ ∈ Work.CharCore.Irr G, (∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → φ ≠ chi ζ) →
      ∀ y : G, y ∈ Q → y ≠ 1 → ∀ y' : G, y' ∈ Q → y' ≠ 1 → φ y = φ y' := by
    intro φ hφ hne y hy hy1 y' hy' hy'1
    have hneS : ∀ x ∈ S, δ • τ' x ≠ φ := by
      intro x hx
      obtain ⟨ζ, hζ, hζ1, rfl⟩ := hSimage x hx
      have hthis : δ • τ' (h'.indQH ζ) = chi ζ := by
        rw [hτ'chi ζ, smul_smul, hδsq, one_smul]
      rw [hthis]
      exact fun hh => hne ζ hζ hζ1 hh.symm
    have hratio := hres_rel φ (Work.CharCore.isClassFun_of_mem_Irr hφ) (hcrit φ hφ hneS)
    obtain ⟨c, hc⟩ := Work.CharCore.resFun_int_const_of_cfInner_ratio
      (AddSubgroup.subset_closure hφ) (Work.CharCore.isClassFun_of_mem_Irr hφ)
      hlam0Irr hlam0ne hlam0deg (fun ζ hζ hζ1 => hratio ζ hζ hζ1)
    have h1 : φ y = (c : ℂ) := hc ⟨y, hy⟩ (fun hh => hy1 (congrArg Subtype.val hh))
    have h2 : φ y' = (c : ℂ) := hc ⟨y', hy'⟩ (fun hh => hy'1 (congrArg Subtype.val hh))
    rw [h1, h2]
  -- **(d)**: the value formula on `Q ∖ 1`, with a global integer `c`
  let W' : G → ℂ := chi lam0 - (εz : ℂ) • Work.Induction.indFun Q lam0
  have hW'V : Work.CharCore.IsVChar W' := by
    show Work.CharCore.IsVChar (chi lam0 - (εz : ℂ) • Work.Induction.indFun Q lam0)
    refine Work.CharCore.IsVChar.sub
      (Work.CharCore.IsVChar.of_mem_Irr (ha lam0 hlam0Irr hlam0ne)) ?_
    rw [Int.cast_smul_eq_zsmul ℂ εz]
    exact Work.CharCore.IsVChar.zsmul
      (Work.Induction.isVChar_indFun (Work.CharCore.IsVChar.of_mem_Irr hlam0Irr)) εz
  have hW'c : Work.CharCore.IsClassFun W' := hW'V.isClassFun
  have hW'orth : ∀ θ ∈ Work.Coherence.ZSpan0 S, Work.CharCore.cfInner (τ' θ) W' = 0 := by
    intro θ hθ
    have hξ2 : Work.CharCore.IsClassFun lam0 := Work.CharCore.isClassFun_of_mem_Irr hlam0Irr
    have hind : (indLin H) (h'.indQH lam0) = Work.Induction.indFun Q lam0 := by
      rw [indLin_apply, hindQH_trans lam0]
    -- the function `indQH λ₀ - Res_H (Ind(indQH λ₀))` vanishes on `Q ∖ 1`
    have hE : ∀ x : ↥H, (x : G) ∈ Q → (x : G) ≠ 1 →
        (h'.indQH lam0 - Work.Induction.resFun H ((indLin H) (h'.indQH lam0))) x = 0 := by
      intro x hxQ hx1
      have hq : (⟨(x : G), hxQ⟩ : ↥Q) ≠ 1 := fun hh => hx1 (congrArg Subtype.val hh)
      have hval : (indLin H) (h'.indQH lam0) (x : G) = h'.indQH lam0 x := by
        rw [show (indLin H) (h'.indQH lam0) (x : G)
            = Work.Induction.indFun H (h'.indQH lam0) (x : G) from rfl, hindQH_trans lam0]
        rw [show h'.indQH lam0 x = h'.indQH lam0 ⟨(x : G), h.le hxQ⟩ from
          congrArg (h'.indQH lam0) (Subtype.ext rfl)]
        exact (Work.FeitSibley.CharQ.indQH_apply_mem_Q h' hξ2 (q := ⟨(x : G), hxQ⟩) hq).symm
      rw [Pi.sub_apply, show Work.Induction.resFun H ((indLin H) (h'.indQH lam0)) x
          = (indLin H) (h'.indQH lam0) (x : G) from rfl, hval]
      ring
    have hθE : Work.CharCore.cfInner θ
        (h'.indQH lam0 - Work.Induction.resFun H ((indLin H) (h'.indQH lam0))) = 0 := by
      have hsupp := Work.FeitSibley.CharQ.zspan0_scriptS_support h' hθ
      have hcongr := Work.BrauerSuzuki.TI.cfInner_congr_of_eq_of_ne_zero
        (φ := θ) (f := h'.indQH lam0 - Work.Induction.resFun H ((indLin H) (h'.indQH lam0)))
        (g := 0) (fun x hx => by
          have hxmem : (x : G) ∈ (h'.Q : Set G) \ {1} := by
            by_contra hc
            exact hx (hsupp x hc)
          exact hE x hxmem.1 (by simpa using hxmem.2))
      rw [hcongr, Work.CharCore.cfInner_zero_right]
    have hδstar : starRingEnd ℂ δ = δ := by
      rcases hδpm with h | h <;> rw [h] <;> simp
    have hW'eq : W' = δ • (τ' (h'.indQH lam0) - (indLin H) (h'.indQH lam0)) := by
      show chi lam0 - (εz : ℂ) • Work.Induction.indFun Q lam0
        = δ • (τ' (h'.indQH lam0) - (indLin H) (h'.indQH lam0))
      rw [show chi lam0 = δ • τ' (h'.indQH lam0) from rfl, hεz, hind, smul_sub]
    have hsplit : Work.CharCore.cfInner (τ' θ) W'
        = δ * (Work.CharCore.cfInner (τ' θ) (τ' (h'.indQH lam0))
            - Work.CharCore.cfInner (τ' θ) ((indLin H) (h'.indQH lam0))) := by
      rw [hW'eq, Work.CharCore.cfInner_smul_right, Work.CharCore.cfInner_sub_right, hδstar]
    rw [hsplit]
    have h1 : Work.CharCore.cfInner (τ' θ) (τ' (h'.indQH lam0))
        = Work.CharCore.cfInner θ (h'.indQH lam0) :=
      hτ'iso.inner_eq θ (Work.Coherence.zSpan0_le_zSpan S hθ) (h'.indQH lam0)
        (Work.Coherence.self_mem_zSpan (hmemS lam0 hlam0Irr hlam0ne))
    have h2 : Work.CharCore.cfInner (τ' θ) ((indLin H) (h'.indQH lam0))
        = Work.CharCore.cfInner θ (Work.Induction.resFun H ((indLin H) (h'.indQH lam0))) := by
      rw [hτ'0 θ hθ]
      exact Work.Induction.frobenius_reciprocity H θ _
        (Work.Induction.isClassFun_indFun H (h'.indQH lam0))
    rw [h1, h2, ← Work.CharCore.cfInner_sub_right, hθE, mul_zero]
  have hratioW := hres_rel W' hW'c hW'orth
  obtain ⟨c, hc⟩ := Work.CharCore.resFun_int_const_of_cfInner_ratio hW'V hW'c
    hlam0Irr hlam0ne hlam0deg (fun ζ hζ hζ1 => hratioW ζ hζ hζ1)
  have hd : ∀ ζ ∈ Work.CharCore.Irr ↥Q, ζ ≠ 1 → ∀ y : G, y ∈ Q → y ≠ 1 →
      chi ζ y = (εz : ℂ) * Work.Induction.indFun Q ζ y + (ζ 1) * (c : ℂ) := by
    intro ζ hζ hζ1 y hy hy1
    have hcy : W' y = (c : ℂ) := hc ⟨y, hy⟩ (fun hh => hy1 (congrArg Subtype.val hh))
    have hδsq' : (εz : ℂ) * (εz : ℂ) = 1 := by rw [hεz, hδsq]
    have hratio : chi ζ - (εz : ℂ) • Work.Induction.indFun Q ζ = (ζ 1) • W' := by
      by_cases hEq : Work.Induction.indFun Q ζ = Work.Induction.indFun Q lam0
      · have hdeg_eq : ζ 1 = lam0 1 := by
          have hidx : (Q.index : ℂ) ≠ 0 :=
            Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite
          have h := congrFun hEq 1
          rw [Work.Induction.indFun_apply_one, Work.Induction.indFun_apply_one] at h
          exact mul_left_cancel₀ hidx h
        have hdiff : h'.indQH ζ - h'.indQH lam0 ∈ Work.Coherence.ZSpan0 S := by
          refine ⟨?_, ?_⟩
          · exact AddSubgroup.sub_mem _
              (Work.Coherence.self_mem_zSpan (hmemS ζ hζ hζ1))
              (Work.Coherence.self_mem_zSpan (hmemS lam0 hlam0Irr hlam0ne))
          · show (h'.indQH ζ - h'.indQH lam0) 1 = 0
            rw [Pi.sub_apply, hindQH_deg ζ, hindQH_deg lam0, hdeg_eq]
            ring
        have hzero : (indLin H) (h'.indQH ζ - h'.indQH lam0) = 0 := by
          rw [map_sub, show (indLin H) (h'.indQH ζ) = (indLin H) (h'.indQH lam0) from by
            rw [indLin_apply, indLin_apply, hindQH_trans ζ, hindQH_trans lam0, hEq], sub_self]
        have hiso : Work.Coherence.IsometryOn S (indLin H) :=
          Work.FeitSibley.CharQ.isometry_indLin h'
        have hinner := hiso.inner_eq (h'.indQH ζ - h'.indQH lam0) hdiff
          (h'.indQH ζ - h'.indQH lam0) hdiff
        change Work.CharCore.cfInner ((indLin H) (h'.indQH ζ - h'.indQH lam0))
            ((indLin H) (h'.indQH ζ - h'.indQH lam0))
          = Work.CharCore.cfInner (h'.indQH ζ - h'.indQH lam0)
            (h'.indQH ζ - h'.indQH lam0) at hinner
        rw [hzero] at hinner
        have hzero0 : Work.CharCore.cfInner (0 : G → ℂ) (0 : G → ℂ) = 0 := by
          simp [Work.CharCore.cfInner]
        rw [hzero0] at hinner
        have hindQH : h'.indQH ζ = h'.indQH lam0 := by
          by_contra hne
          have hζm := hmemS ζ hζ hζ1
          have hlm := hmemS lam0 hlam0Irr hlam0ne
          have ho1 := Work.CharCore.irr_orthonormal (h'.indQH ζ) (h'.indQH lam0)
            (hIrrS _ (hmemS ζ hζ hζ1)) (hIrrS _ (hmemS lam0 hlam0Irr hlam0ne))
          have ho2 := Work.CharCore.irr_orthonormal (h'.indQH lam0) (h'.indQH ζ)
            (hIrrS _ (hmemS lam0 hlam0Irr hlam0ne)) (hIrrS _ (hmemS ζ hζ hζ1))
          rw [Work.CharCore.cfInner_sub_left, Work.CharCore.cfInner_sub_right,
            Work.CharCore.cfInner_sub_right, ho2, ho1, if_neg hne, if_neg (Ne.symm hne),
            Work.CharCore.cfInner_self_mem_Irr (hIrrS _ (hmemS ζ hζ hζ1)),
            Work.CharCore.cfInner_self_mem_Irr (hIrrS _ (hmemS lam0 hlam0Irr hlam0ne))] at hinner
          norm_num at hinner
        have hchi : chi ζ = chi lam0 := by
          show δ • τ' (h'.indQH ζ) = δ • τ' (h'.indQH lam0)
          rw [hindQH]
        have hd1 : ζ 1 = 1 := by rw [hdeg_eq, hlam0deg]
        rw [hchi, hEq, hd1, one_smul]
      · have hb' : ∀ g, Work.Induction.indFun Q ζ g - (ζ 1) * Work.Induction.indFun Q lam0 g
            = (εz : ℂ) * (chi ζ g - (ζ 1) * chi lam0 g) := by
          intro g
          have h := hb ζ hζ hζ1 lam0 hlam0Irr hlam0ne hEq g
          rw [hlam0deg] at h
          simp only [one_mul] at h
          exact h
        funext g
        have h := hb' g
        have hεsq : (εz : ℂ) * (εz : ℂ) = 1 := hδsq'
        rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.smul_apply, smul_eq_mul]
        show chi ζ g - (εz : ℂ) * Work.Induction.indFun Q ζ g
          = (ζ 1) * (chi lam0 g - (εz : ℂ) * Work.Induction.indFun Q lam0 g)
        linear_combination (-(εz : ℂ)) * h + ((ζ 1) * chi lam0 g - chi ζ g) * hεsq
    have hpt := congrFun hratio y
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.smul_apply, smul_eq_mul, hcy] at hpt
    rw [← hpt]
    ring
  refine ⟨εz, hεzpm, c, chi, ha, hb, hc21, hd, he⟩

end Work.ZassenhausTwoGroup
