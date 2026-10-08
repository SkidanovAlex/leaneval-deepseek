import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.CharQ.scriptS_eq_image
import Submission.Work.FeitSibley.CharQ.scriptS_vanish
import Submission.Work.Clifford.irrDeg_eq_one_of_commutator_le_charKernel
import Submission.Work.Clifford.irr_apply_eq_one_of_natCoeffs
import Submission.Work.CharCore.Main
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer
import Submission.Work.Induction.frobenius_reciprocity

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.scriptSR_deg_Qcomm`

Peterfalvi II, Appendice XII (p. 288): for the Feit–Sibley data `h : FSData G` and a subgroup
`R` of `Q` containing the derived subgroup `Q' = ⁅Q,Q⁆`, every character `χ ∈ 𝒮(R)` (an
irreducible character of `H` which is non-trivial on `Q₁` and trivial on `R`) has degree `|D|`.

The argument is Peterfalvi's "the members of `𝒮(Q')` are the linear characters of `Q/Q'`
induced to `H`":

* `χ ∈ 𝒮`, so by Peterfalvi's Lemma 2a (`Work.FeitSibley.CharQ.exists_indFun_of_complement_of_inertia`,
  the engine behind `scriptS_vanish`) `χ = Ind_Q^H θ` for some `θ ∈ Irr Q`.
* Hence `χ(1) = [H : Q] · θ(1) = |D| · θ(1)` (`Work.Frobenius.Induced.indFun_apply_one_eq` and
  the index computation `index_subgroupOf_Q`).
* Since `⁅Q,Q⁆ ≤ R` and `χ` is trivial on `R`, the restriction `χ|_Q` is trivial on the derived
  subgroup `⁅Q,Q⁆`; expressing `χ|_Q` as a non-negative integral combination of irreducibles of
  `Q` and evaluating it at elements of `⁅Q,Q⁆`
  (`Work.Clifford.irr_apply_eq_one_of_natCoeffs`) shows that the constituent `θ` is trivial on
  `⁅Q,Q⁆`, whence `θ(1) = 1`
  (`Work.Clifford.irrDeg_eq_one_of_commutator_le_charKernel`).
-/

set_option linter.style.haveILetI false

noncomputable section

open Classical

namespace Work.FeitSibley.Coherence

/-- An element of the derived subgroup of `Q` viewed inside `H` has underlying `G`-element in
`⁅Q,Q⁆ ≤ G`. -/
theorem mem_commutator_of_mem_commutator_subgroupOf {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {n : ↥(h.Q.subgroupOf h.H)}
    (hn : n ∈ commutator ↥(h.Q.subgroupOf h.H)) : (n : G) ∈ ⁅h.Q, h.Q⁆ := by
  have h1 : ((h.Q.subgroupOf h.H).subtype n) ∈
      ⁅h.Q.subgroupOf h.H, h.Q.subgroupOf h.H⁆ := by
    rw [← Subgroup.map_subtype_commutator (h.Q.subgroupOf h.H)]
    exact ⟨n, hn, rfl⟩
  have h2 : Subgroup.map h.H.subtype
      ⁅h.Q.subgroupOf h.H, h.Q.subgroupOf h.H⁆ = ⁅h.Q, h.Q⁆ := by
    rw [Subgroup.map_commutator]
    congr 1
    · rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr h.Q_le_H
    · rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr h.Q_le_H
  show h.H.subtype ((h.Q.subgroupOf h.H).subtype n) ∈ ⁅h.Q, h.Q⁆
  rw [← h2]
  exact ⟨_, h1, rfl⟩

/-- The index of `Q` in `H = Q ⋊ D` equals `|D|`. -/
theorem index_subgroupOf_Q {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G) :
    (h.Q.subgroupOf h.H).index = Nat.card h.D := by
  have hcard := Subgroup.card_mul_index (h.Q.subgroupOf h.H)
  have hN : Nat.card ↥(h.Q.subgroupOf h.H) = Nat.card h.Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Q_le_H).toEquiv
  have hsup := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer h.D_le_normalizer_Q
  rw [h.Q_sup_D, h.Q_inf_D] at hsup
  simp only [Nat.card_eq_fintype_card, Fintype.card_ofSubsingleton, mul_one] at hsup
  simp only [Nat.card_eq_fintype_card] at hcard hN ⊢
  have hQpos : 0 < Fintype.card ↥h.Q := Fintype.card_pos
  rw [hN, hsup] at hcard
  exact Nat.eq_of_mul_eq_mul_left hQpos hcard

/-- **Peterfalvi, Lemma 2a.**  A character `χ ∈ 𝒮 = scriptS h.H h.Q₁` is induced from a
character of `Q` (viewed inside `H`). -/
theorem exists_indFun_of_mem_scriptS {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {χ : ↥h.H → ℂ}
    (hχ : χ ∈ Work.FeitSibley.scriptS h.H h.Q1) :
    ∃ θ ∈ Work.Frobenius.Irr ↥(h.Q.subgroupOf h.H),
      (∃ y : ↥(h.Q.subgroupOf h.H), ((y : ↥h.H) : G) ∈ h.Q1 ∧ θ y ≠ θ 1) ∧
      χ = Work.Frobenius.indFun (h.Q.subgroupOf h.H) θ := by
  classical
  have hS : χ ∈ Work.CharCore.Irr ↥h.H ∧
      ∃ x : ↥h.H, (x : G) ∈ h.Q1 ∧ χ x ≠ χ 1 := by
    simpa only [Work.FeitSibley.scriptS, Submission.Blueprint.excludingKernel,
      Finset.mem_filter] using hχ
  haveI hQn : (h.Q.subgroupOf h.H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer h.Q_normal_in_H
  have hcomp : Subgroup.IsComplement' (h.Q.subgroupOf h.H) (h.D.subgroupOf h.H) :=
    Work.FeitSibley.CharQ.isComplement'_Q_D h
  have hA : h.Q1.subgroupOf h.H ≤ h.Q.subgroupOf h.H :=
    Subgroup.subgroupOf_mono h.H h.Q1_le_Q
  have hχF : χ ∈ Work.Frobenius.Irr ↥h.H :=
    (Work.Frobenius.Bridge.mem_Irr_iff_coherence).mpr
      ((Work.CharCore.mem_Irr_iff_coherence).mp hS.1)
  obtain ⟨x₀, hx₀Q1, hx₀ne⟩ := hS.2
  have hker : ∃ x : ↥h.H, x ∈ h.Q1.subgroupOf h.H ∧ χ x ≠ χ 1 :=
    ⟨x₀, Subgroup.mem_subgroupOf.mpr hx₀Q1, hx₀ne⟩
  exact Work.FeitSibley.CharQ.exists_indFun_of_complement_of_inertia
    (G := ↥h.H) (K := h.Q.subgroupOf h.H) (He := h.D.subgroupOf h.H)
    (A := h.Q1.subgroupOf h.H) hcomp hA
    (fun θ hθ hθA d hd hd1 =>
      Work.FeitSibley.CharQ.conjChar_ne_self_of_notMem_kernel h hθ hθA hd hd1)
    hχF hker

/-- **The degree of a character induced from `Q`.**  If `χ = Ind_Q^H θ` with `θ ∈ Irr Q` and
`χ` is trivial on a subgroup `R ≥ ⁅Q,Q⁆` of `Q`, then `θ 1 = 1`. -/
theorem deg_one_of_indFun_of_trivial_on_commutator {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) {R : Subgroup G} (hQ'R : ⁅h.Q, h.Q⁆ ≤ R)
    {χ : ↥h.H → ℂ} (hχR : ∀ x : ↥h.H, (x : G) ∈ R → χ x = χ 1)
    {θ : ↥(h.Q.subgroupOf h.H) → ℂ} (hθ : θ ∈ Work.Frobenius.Irr ↥(h.Q.subgroupOf h.H))
    (hχeq : χ = Work.Frobenius.indFun (h.Q.subgroupOf h.H) θ)
    (hχIrr : χ ∈ Work.CharCore.Irr ↥h.H) :
    θ 1 = 1 := by
  classical
  haveI hNn : (h.Q.subgroupOf h.H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer h.Q_normal_in_H
  have hθc : θ ∈ Work.CharCore.Irr ↥(h.Q.subgroupOf h.H) :=
    (Work.CharCore.mem_Irr_iff_coherence).mpr
      ((Work.Frobenius.Bridge.mem_Irr_iff_coherence).mp hθ)
  have hfchar : Work.CharCore.IsChar
      (Work.CharCore.resFun (h.Q.subgroupOf h.H) χ) :=
    Work.Induction.isChar_resFun (H := h.Q.subgroupOf h.H)
      (AddSubmonoid.subset_closure hχIrr)
  obtain ⟨c, hc⟩ := (Work.CharCore.isChar_iff_exists_nat_coeffs).mp hfchar
  have hmemR : ∀ n : ↥(h.Q.subgroupOf h.H), n ∈ commutator ↥(h.Q.subgroupOf h.H) →
      (n : G) ∈ R :=
    fun n hn => hQ'R (mem_commutator_of_mem_commutator_subgroupOf h hn)
  have key : ∀ n : ↥(h.Q.subgroupOf h.H), n ∈ commutator ↥(h.Q.subgroupOf h.H) →
      (Work.CharCore.resFun (h.Q.subgroupOf h.H) χ) n =
        (Work.CharCore.resFun (h.Q.subgroupOf h.H) χ) 1 := by
    intro n hn
    have h1 : (Work.CharCore.resFun (h.Q.subgroupOf h.H) χ) n = χ (n : ↥h.H) := rfl
    have h2 : (Work.CharCore.resFun (h.Q.subgroupOf h.H) χ) 1 = χ 1 := rfl
    rw [h1, h2]
    exact hχR (n : ↥h.H) (hmemR n hn)
  have hχind : Work.Induction.indFun (h.Q.subgroupOf h.H) θ = χ := hχeq.symm
  have hrec : Work.CharCore.cfInner (Work.Induction.indFun (h.Q.subgroupOf h.H) θ) χ
      = Work.CharCore.cfInner θ (Work.CharCore.resFun (h.Q.subgroupOf h.H) χ) :=
    Work.Induction.frobenius_reciprocity (h.Q.subgroupOf h.H) θ χ
      (Work.CharCore.isClassFun_of_mem_Irr hχIrr)
  have hcf : Work.CharCore.cfInner θ (Work.CharCore.resFun (h.Q.subgroupOf h.H) χ) = 1 := by
    rw [← hrec, hχind]
    exact Work.CharCore.cfInner_self_mem_Irr hχIrr
  -- the multiplicity of `θ` in `χ|_Q` is `1`, in particular non-zero
  have hcθ : c ⟨θ, hθc⟩ ≠ 0 := by
    have hcoef : Work.CharCore.cfInner
        (Work.CharCore.resFun (h.Q.subgroupOf h.H) χ) θ = (c ⟨θ, hθc⟩ : ℂ) := by
      rw [hc, Work.CharCore.cfInner_sum_smul_left]
      rw [Finset.sum_eq_single ⟨θ, hθc⟩]
      · rw [Work.CharCore.irr_orthonormal θ θ hθc hθc, ite_eq_left rfl, mul_one]
      · intro b _ hb
        have hbne : (b : ↥(h.Q.subgroupOf h.H) → ℂ) ≠ θ := fun hh => hb (Subtype.ext hh)
        rw [Work.CharCore.irr_orthonormal (b : ↥(h.Q.subgroupOf h.H) → ℂ) θ b.2 hθc,
          ite_eq_right hbne, mul_zero]
      · intro hnot; exact absurd (Finset.mem_univ _) hnot
    have hone : (c ⟨θ, hθc⟩ : ℂ) = 1 := by
      rw [← hcoef, Work.CharCore.cfInner_conj_symm, hcf]
      simp
    have hone' : c ⟨θ, hθc⟩ = 1 := by exact_mod_cast hone
    rw [hone']; norm_num
  -- `θ` is trivial on the derived subgroup of `Q` and hence linear
  have hker : (commutator ↥(h.Q.subgroupOf h.H) : Set ↥(h.Q.subgroupOf h.H)) ⊆
      Work.CharCore.charKernel θ := by
    intro n hn
    exact Work.Clifford.irr_apply_eq_one_of_natCoeffs hc (key n hn) hcθ
  have hdeg := Work.Clifford.irrDeg_eq_one_of_commutator_le_charKernel
    (Y := ↥(h.Q.subgroupOf h.H)) (M := commutator ↥(h.Q.subgroupOf h.H)) le_rfl hθc hker
  rw [Work.CharCore.irrDeg_spec hθc, hdeg]
  norm_num

theorem scriptSR_deg_Qcomm {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {R : Subgroup G} (hR : R ≤ h.Q) (hQ'R : ⁅h.Q, h.Q⁆ ≤ R)
    {χ : ↥h.H → ℂ} (hχ : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 R) :
    χ 1 = (Nat.card h.D : ℂ) := by
  classical
  have h1 := (Work.FeitSibley.Coherence.mem_scriptSR_iff h R).mp hχ
  obtain ⟨hscriptS, hRtriv⟩ := h1
  have hχIrr : χ ∈ Work.CharCore.Irr ↥h.H := by
    have := hscriptS
    rw [Work.FeitSibley.scriptS, Submission.Blueprint.excludingKernel, Finset.mem_filter]
      at this
    exact this.1
  obtain ⟨θ, hθ, -, hχeq⟩ := exists_indFun_of_mem_scriptS h hscriptS
  have hθ1 : θ 1 = 1 :=
    deg_one_of_indFun_of_trivial_on_commutator h hQ'R hRtriv hθ hχeq hχIrr
  have hdeg := Work.Frobenius.Induced.indFun_apply_one_eq (h.Q.subgroupOf h.H) θ
  rw [hχeq, hdeg, hθ1, mul_one]
  rw [index_subgroupOf_Q h]

end Work.FeitSibley.Coherence
