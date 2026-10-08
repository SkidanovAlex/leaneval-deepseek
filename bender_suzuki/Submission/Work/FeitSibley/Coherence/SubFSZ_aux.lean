import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.engine
import Submission.Work.FeitSibley.Coherence.step1
import Submission.Work.FeitSibley.Coherence.step2
import Submission.Work.FeitSibley.Coherence.coherent_union_singleton
import Submission.Work.FeitSibley.Coherence.numeric_step1
import Submission.Work.FeitSibley.Coherence.scriptSR_deg_Qcomm
import Submission.Work.FeitSibley.Coherence.sum_deg_sq_scriptSR
import Submission.Work.FeitSibley.Coherence.sum_deg_sq_scriptSR_sup
import Submission.Work.FeitSibley.Coherence.sum_deg_sq_scriptSR_sdiff
import Submission.Work.FeitSibley.Coherence.exists_indQH_of_mem_scriptSR_le_Q
import Submission.Work.FeitSibley.Coherence.commutator_le_of_chief
import Submission.Work.FeitSibley.CharQ.scriptS_eq_image
import Submission.Work.FeitSibley.CharQ.prodChar_Q1_kernel_iff
import Submission.Work.FeitSibley.CharQ.prodChar_mem_Irr
import Submission.Work.FeitSibley.CharQ.exists_prodChar_of_mem_Irr
import Submission.Work.CharPrelim.ft4_1
import Submission.Work.FeitSibley.GroupTheory.exists_maximal_normal_below
import Submission.Work.Coherence.coherent_of_norm_two_lift

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.coherent_scriptS_sub_FSZ`

Peterfalvi II, Appendice XII, step (3): for the Feit–Sibley data `h` with `D ≠ ⊥`, `Q₁` a
non-abelian `p`-group (`p` odd) and `Z = FSZ h = [Q₁,Q₁] ∩ Z(Q₁)`, the set
`𝒳 = 𝒮 - 𝒮(Z) = {χ ∈ 𝒮 | Z ⊄ ker χ}` is coherent for `Ind_H^G`.

The source proof is in two halves:

* `𝒳₁ = 𝒳 ∩ 𝒮(S')` is coherent (the ordering/divisibility argument `(3-1)`);
* the chief series of `S'` descends from `𝒳 ∩ 𝒮(S')` to `𝒳 ∩ 𝒮(⊥) = 𝒳` with Feit's criterion.

This file formalises both halves, using the degree-square sum
`∑_{χ ∈ 𝒮(R)∖𝒮(R⊔Z)} χ(1)² = |D|·[S:R]·(|Q₁| - [Q₁:Z])` (`sum_deg_sq_scriptSR_sdiff_gen`)
for the arithmetic.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

noncomputable section

open Classical

namespace Work.FeitSibley.Coherence

variable {G : Type} [Group G] [Fintype G]

/-! ## Basic API for `FSZ h = [Q₁,Q₁] ∩ C_G(Q₁)` -/

theorem FSZ_le_Q1 (h : Work.FeitSibley.FSData G) : FSZ h ≤ h.Q1 := by
  rw [FSZ]
  exact inf_le_left.trans
    ((Subgroup.commutator_le_sup h.Q1 h.Q1).trans (le_of_eq (sup_idem h.Q1)))

theorem FSZ_le_centralizer (h : Work.FeitSibley.FSData G) :
    FSZ h ≤ Subgroup.centralizer (h.Q1 : Set G) := inf_le_right

theorem conj_mem_centralizer_iff (h : Work.FeitSibley.FSData G) {x : G} (hx : x ∈ h.H)
    {y : G} (hy : y ∈ Subgroup.centralizer (h.Q1 : Set G)) :
    x * y * x⁻¹ ∈ Subgroup.centralizer (h.Q1 : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro q hq
  have hq' : x⁻¹ * q * x ∈ h.Q1 := by
    have hiff := (Subgroup.mem_normalizer_iff.mp (h.Q1_normal_in_H hx)) (x⁻¹ * q * x)
    rw [hiff, show x * (x⁻¹ * q * x) * x⁻¹ = q by group]
    exact hq
  calc q * (x * y * x⁻¹) = x * ((x⁻¹ * q * x) * y) * x⁻¹ := by group
    _ = x * (y * (x⁻¹ * q * x)) * x⁻¹ := by rw [hy (x⁻¹ * q * x) hq']
    _ = (x * y * x⁻¹) * q := by group

theorem FSZ_normal (h : Work.FeitSibley.FSData G) :
    h.H ≤ Subgroup.normalizer (FSZ h : Set G) := by
  intro x hx
  have hAconj : ∀ y : G, y ∈ ⁅h.Q1, h.Q1⁆ ↔ x * y * x⁻¹ ∈ ⁅h.Q1, h.Q1⁆ :=
    Subgroup.mem_normalizer_iff.mp (H_le_normalizer_commutator_Q1 h hx)
  have hCconj : ∀ y : G, y ∈ Subgroup.centralizer (h.Q1 : Set G) ↔
      x * y * x⁻¹ ∈ Subgroup.centralizer (h.Q1 : Set G) := by
    intro y
    refine ⟨conj_mem_centralizer_iff h hx, fun hy => ?_⟩
    have hxinv : x⁻¹ ∈ h.H := h.H.inv_mem hx
    have hkey := conj_mem_centralizer_iff h hxinv hy
    rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at hkey
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hAconj y, hCconj y]

/-! ## `Z`-triviality of an induced character -/

/-- If a function `φ` on `Q` is trivial on a subgroup `Z ≤ Q` which is normalised by `H`, then
`Ind_Q^H φ` is trivial on `Z`.  (Only the trace formula and `H ≤ N_G(Z)`, `Z ≤ Q`, are used.) -/
theorem indQH_apply_eq_one_of_triv_on_Z (h : Work.FeitSibley.FSData G) {φ : ↥h.Q → ℂ}
    {Z : Subgroup G} (hZQ : Z ≤ h.Q) (hZn : h.H ≤ Subgroup.normalizer (Z : Set G))
    (htriv : ∀ x : ↥h.Q, (x : G) ∈ Z → φ x = φ 1)
    {x : ↥h.H} (hx : (x : G) ∈ Z) : h.indQH φ x = h.indQH φ 1 := by
  rw [Work.FeitSibley.FSData.indQH, Work.Induction.indFun_apply_def,
    Work.Induction.indFun_apply_def]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  have hy : y * x * y⁻¹ ∈ h.Q.subgroupOf h.H := by
    rw [Subgroup.mem_subgroupOf]
    show ((y * x * y⁻¹ : ↥h.H) : G) ∈ h.Q
    rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mul]
    exact hZQ ((Subgroup.mem_normalizer_iff.mp (hZn y.2) (x : G)).mp hx)
  have h1 : y * (1 : ↥h.H) * y⁻¹ ∈ h.Q.subgroupOf h.H := by
    rw [Subgroup.mem_subgroupOf]
    show ((y * 1 * y⁻¹ : ↥h.H) : G) ∈ h.Q
    rw [show ((y * 1 * y⁻¹ : ↥h.H) : G) = 1 by simp]
    exact h.Q.one_mem
  rw [dif_pos hy, dif_pos h1]
  have hA : ((⟨y * x * y⁻¹, hy⟩ : ↥(h.Q.subgroupOf h.H)) : G) ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hZn y.2) (x : G)).mp hx
  have hB : ((⟨y * 1 * y⁻¹, h1⟩ : ↥(h.Q.subgroupOf h.H)) : G) ∈ Z := by
    have hval : ((⟨y * 1 * y⁻¹, h1⟩ : ↥(h.Q.subgroupOf h.H)) : G) = 1 := by
      show ((y * 1 * y⁻¹ : ↥h.H) : G) = 1
      simp
    rw [hval]; exact Z.one_mem
  rw [show φ ⟨↑↑(⟨y * x * y⁻¹, hy⟩ : ↥(h.Q.subgroupOf h.H)), hZQ hA⟩ = φ 1
        from htriv _ hA,
      show φ ⟨↑↑(⟨y * 1 * y⁻¹, h1⟩ : ↥(h.Q.subgroupOf h.H)), hZQ hB⟩ = φ 1
        from htriv _ hB]

/-- `prodChar λ θ` evaluated at an element of `Q` lying in `S`. -/
theorem prodChar_apply_of_mem_S (h : Work.FeitSibley.FSData G) (lam : ↥h.S → ℂ)
    (theta : ↥h.Q1 → ℂ) (x : ↥h.Q) (hx : (x : G) ∈ h.S) :
    h.prodChar lam theta x = lam ⟨(x : G), hx⟩ * theta 1 := by
  have hdec : h.prodIso.symm x = (⟨(x : G), hx⟩, ⟨1, h.Q1.one_mem⟩) := by
    apply h.prodIso.injective
    rw [h.prodIso.apply_symm_apply]
    apply Subtype.ext
    simp [Work.FeitSibley.FSData.prodIso_apply, Work.FeitSibley.FSData.prodHom_apply]
  rw [Work.FeitSibley.FSData.prodChar, hdec]
  congr 1

/-- **`Ind_Q^H φ` is trivial on `Z` if and only if `φ` is**, for `φ ∈ Irr Q` with
`Ind_Q^H φ ∈ 𝒮` and `Z ≤ Q` normalised by `H`. -/
theorem mem_scriptSR_indQH_iff (h : Work.FeitSibley.FSData G) {φ : ↥h.Q → ℂ}
    (hφ : φ ∈ Work.CharCore.Irr ↥h.Q)
    (hχS : h.indQH φ ∈ Work.FeitSibley.scriptS h.H h.Q1)
    {Z : Subgroup G} (hZQ : Z ≤ h.Q) (hZn : h.H ≤ Subgroup.normalizer (Z : Set G)) :
    h.indQH φ ∈ Work.FeitSibley.scriptSR h.H h.Q1 Z ↔
      ∀ z : ↥h.Q, (z : G) ∈ Z → φ z = φ 1 := by
  classical
  have hχIrr : h.indQH φ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hχS).1
  constructor
  · intro hχZ q hq
    obtain ⟨-, hχZtriv⟩ := (mem_scriptSR_iff h Z).mp hχZ
    have hχC : h.indQH φ ∈ Work.Clifford.Irr ↥h.H :=
      (Work.Clifford.corr_mem_Irr_charCore).mpr hχIrr
    have hcf : Work.CharCore.IsClassFun (h.indQH φ) :=
      Work.CharCore.isClassFun_of_mem_Irr hχIrr
    have hpull : Work.FeitSibley.CharQ.pull h φ ∈
        Work.Clifford.Irr ↥(h.Q.subgroupOf h.H) :=
      Work.FeitSibley.CharQ.pull_mem_Irr h hφ
    have hc : Work.Clifford.IsConstituentOf (Work.FeitSibley.CharQ.pull h φ)
        (Work.Clifford.resFun (h.Q.subgroupOf h.H) (h.indQH φ)) := by
      rw [Work.Clifford.IsConstituentOf]
      have hB : Work.Clifford.cfInner
          (Work.Clifford.resFun (h.Q.subgroupOf h.H) (h.indQH φ))
          (Work.FeitSibley.CharQ.pull h φ) = 1 := by
        rw [Work.Clifford.cfInner_conj_symm]
        have hA := Work.Clifford.cfInner_indFun (Work.FeitSibley.CharQ.pull h φ) hcf
        rw [← hA, ← Work.FeitSibley.CharQ.indQH_eq_indFun,
          Work.Clifford.cfInner_eq_ite_of_mem_Irr hχC hχC]
        simp
      rw [hB]; simp
    have hxH : h.indQH φ (Work.FeitSibley.CharQ.toQ h q : ↥h.H) = h.indQH φ 1 :=
      hχZtriv (Work.FeitSibley.CharQ.toQ h q) (by simpa using hq)
    have hcon := Work.FeitSibley.CharQ.apply_eq_one_of_constituent h hχIrr hpull hc
      (x := Work.FeitSibley.CharQ.toQ h q) hxH
    rwa [Work.FeitSibley.CharQ.pull_toQ, Work.FeitSibley.CharQ.pull_one] at hcon
  · intro hqtriv
    rw [mem_scriptSR_iff]
    exact ⟨hχS, fun x hx => indQH_apply_eq_one_of_triv_on_Z h hZQ hZn hqtriv hx⟩

/-- **`Ind_Q^H (prodChar λ θ)` is trivial on `Z` if and only if `θ` is.**  For `λ ∈ Irr S`,
`θ ∈ Irr Q₁` non-principal and `Z ≤ Q₁` normalised by `H`. -/
theorem mem_scriptSR_prodChar_iff (h : Work.FeitSibley.FSData G) {lam : ↥h.S → ℂ}
    (hlam : lam ∈ Work.CharCore.Irr ↥h.S)
    {theta : ↥h.Q1 → ℂ} (htheta : theta ∈ Work.CharCore.Irr ↥h.Q1)
    (htheta1 : theta ≠ fun _ : ↥h.Q1 => (1 : ℂ))
    {Z : Subgroup G} (hZQ1 : Z ≤ h.Q1) (hZn : h.H ≤ Subgroup.normalizer (Z : Set G)) :
    h.indQH (h.prodChar lam theta) ∈ Work.FeitSibley.scriptSR h.H h.Q1 Z ↔
      ∀ z : ↥h.Q1, (z : G) ∈ Z → theta z = theta 1 := by
  classical
  set φ := h.prodChar lam theta with hφdef
  have hφirr : φ ∈ Work.CharCore.Irr ↥h.Q :=
    Work.FeitSibley.CharQ.prodChar_mem_Irr h hlam htheta
  have hlam1 : lam 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hlam]; exact Work.CharCore.irrDeg_ne_zero hlam
  have hwit : ∃ x : ↥h.Q, (x : G) ∈ h.Q1 ∧ φ x ≠ φ 1 := by
    by_contra hcon
    push_neg at hcon
    exact htheta1
      ((Work.FeitSibley.CharQ.prodChar_Q1_kernel_iff h hlam htheta).mp hcon)
  have hχS : h.indQH φ ∈ Work.FeitSibley.scriptS h.H h.Q1 :=
    (Work.FeitSibley.CharQ.scriptS_eq_image h).mpr ⟨φ, hφirr, hwit, rfl⟩
  have hφtriv_iff : (∀ q : ↥h.Q, (q : G) ∈ Z → φ q = φ 1) ↔
      ∀ z : ↥h.Q1, (z : G) ∈ Z → theta z = theta 1 := by
    constructor
    · intro hq z hz
      have hzQ : (z : G) ∈ h.Q := h.Q1_le_Q z.2
      have h1 := hq ⟨(z : G), hzQ⟩ hz
      rw [hφdef, Work.FeitSibley.CharQ.prodChar_apply_of_mem_Q1 h lam theta
            ⟨(z : G), hzQ⟩ z.2, Work.FeitSibley.FSData.prodChar_one] at h1
      exact mul_left_cancel₀ hlam1 h1
    · intro ht q hq
      rw [hφdef, Work.FeitSibley.CharQ.prodChar_apply_of_mem_Q1 h lam theta q (hZQ1 hq),
        Work.FeitSibley.FSData.prodChar_one]
      rw [ht ⟨(q : G), hZQ1 hq⟩ hq]
  rw [mem_scriptSR_indQH_iff h hφirr hχS (hZQ1.trans h.Q1_le_Q) hZn, hφtriv_iff]

/-! ## The degree-square sum over `𝒮(R) ∖ 𝒮(R ⊔ Z)` -/

/-- `[H : R] = [S : R] · |Q₁| · |D|` for `R ≤ S`. -/
theorem index_subgroupOf_H_of_le_S (h : Work.FeitSibley.FSData G) {R : Subgroup G}
    (hR : R ≤ h.S) :
    (R.subgroupOf h.H).index = (R.subgroupOf h.S).index * Nat.card h.Q1 * Nat.card h.D := by
  have hcardR_S : Nat.card ↥(R.subgroupOf h.S) = Nat.card ↥R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv
  have hcardR_H : Nat.card ↥(R.subgroupOf h.H) = Nat.card ↥R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hR.trans h.S_le_H)).toEquiv
  have h1 : Nat.card ↥R * (R.subgroupOf h.H).index = Nat.card ↥h.H := by
    rw [← hcardR_H]; exact Subgroup.card_mul_index _
  have h2 : Nat.card ↥R * (R.subgroupOf h.S).index = Nat.card ↥h.S := by
    rw [← hcardR_S]; exact Subgroup.card_mul_index _
  haveI : Nonempty ↥R := ⟨⟨1, R.one_mem⟩⟩
  have hposR : 0 < Nat.card ↥R := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left hposR ?_
  rw [h1, Work.FeitSibley.Coherence.card_H_eq h, ← h2]
  ring

/-- `[H : R ⊔ Z] = [S : R] · [Q₁ : Z] · |D|` for `R ≤ S`, `Z ≤ Q₁`. -/
theorem index_sup_subgroupOf_H_of_le_S (h : Work.FeitSibley.FSData G) {R Z : Subgroup G}
    (hR : R ≤ h.S) (hZQ1 : Z ≤ h.Q1) :
    ((R ⊔ Z).subgroupOf h.H).index
      = (R.subgroupOf h.S).index * (Z.subgroupOf h.Q1).index * Nat.card h.D := by
  have hcardR_S : Nat.card ↥(R.subgroupOf h.S) = Nat.card ↥R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR).toEquiv
  have h2 : Nat.card ↥R * (R.subgroupOf h.S).index = Nat.card ↥h.S := by
    rw [← hcardR_S]; exact Subgroup.card_mul_index _
  have hZcard : Nat.card ↥(Z.subgroupOf h.Q1) = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ1).toEquiv
  have h3 : Nat.card ↥Z * (Z.subgroupOf h.Q1).index = Nat.card ↥h.Q1 := by
    rw [← hZcard]; exact Subgroup.card_mul_index _
  have hRZ : Nat.card ↥(R ⊔ Z) = Nat.card ↥R * Nat.card ↥Z := by
    refine Work.FeitSibley.Coherence.card_sup_eq_card_mul_card_of_commute
      (fun a ha b hb => h.commute a (hR ha) b (hZQ1 hb)) ?_
    refine le_antisymm ?_ bot_le
    intro x hx
    obtain ⟨hxa, hxb⟩ := Subgroup.mem_inf.mp hx
    have hmem : x ∈ h.S ⊓ h.Q1 := Subgroup.mem_inf.mpr ⟨hR hxa, hZQ1 hxb⟩
    rw [h.S_inf_Q1] at hmem
    simpa using hmem
  have hcardRZ_H : Nat.card ↥((R ⊔ Z).subgroupOf h.H) = Nat.card ↥(R ⊔ Z) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (sup_le (hR.trans h.S_le_H) (hZQ1.trans h.Q1_le_H))).toEquiv
  have h1 : Nat.card ↥(R ⊔ Z) * ((R ⊔ Z).subgroupOf h.H).index = Nat.card ↥h.H := by
    rw [← hcardRZ_H]; exact Subgroup.card_mul_index _
  haveI : Nonempty ↥R := ⟨⟨1, R.one_mem⟩⟩
  haveI : Nonempty ↥Z := ⟨⟨1, Z.one_mem⟩⟩
  have hposR : 0 < Nat.card ↥R := Nat.card_pos
  have hposZ : 0 < Nat.card ↥Z := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_left (Nat.mul_pos hposR hposZ) ?_
  rw [← hRZ, h1, Work.FeitSibley.Coherence.card_H_eq h, hRZ, ← h2, ← h3]
  ring

theorem sum_deg_sq_scriptSR_sdiff_gen (h : Work.FeitSibley.FSData G)
    (S1 Z : Subgroup G) (hS1 : S1 ≤ h.S) (hS1n : h.H ≤ Subgroup.normalizer (S1 : Set G))
    (hZQ1 : Z ≤ h.Q1) (hZn : h.H ≤ Subgroup.normalizer (Z : Set G)) :
    ∑ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 S1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (S1 ⊔ Z),
        ((Work.CharCore.irrDeg χ : ℝ)) ^ 2
      = (Nat.card h.D : ℝ) * (((S1.subgroupOf h.S).index : ℕ) : ℝ) *
          ((Nat.card h.Q1 : ℝ) - (((Z.subgroupOf h.Q1).index : ℕ) : ℝ)) := by
  classical
  have hSZleQ : S1 ⊔ Z ≤ h.Q :=
    sup_le (hS1.trans h.S_le_Q) (hZQ1.trans h.Q1_le_Q)
  have hSZn : h.H ≤ Subgroup.normalizer ((S1 ⊔ Z : Subgroup G) : Set G) :=
    (le_inf hS1n hZn).trans (Subgroup.inf_normalizer_le_normalizer_sup S1 Z)
  have hsub : Work.FeitSibley.scriptSR h.H h.Q1 (S1 ⊔ Z)
      ⊆ Work.FeitSibley.scriptSR h.H h.Q1 S1 := scriptSR_subset_of_le h le_sup_left
  have hsplit := Finset.sum_sdiff
    (f := fun χ : ↥h.H → ℂ => ((Work.CharCore.irrDeg χ : ℝ)) ^ 2) hsub
  have hA := sum_deg_sq_scriptSR h S1 (hS1.trans h.S_le_Q) hS1n
  have hB := sum_deg_sq_scriptSR h (S1 ⊔ Z) hSZleQ hSZn
  have hsupQ1 : ((S1 ⊔ Z) ⊔ h.Q1) = S1 ⊔ h.Q1 := by
    rw [sup_assoc, sup_eq_right.mpr hZQ1]
  rw [show (∑ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 S1 \
        Work.FeitSibley.scriptSR h.H h.Q1 (S1 ⊔ Z),
        ((Work.CharCore.irrDeg χ : ℝ)) ^ 2)
      = (∑ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 S1,
          ((Work.CharCore.irrDeg χ : ℝ)) ^ 2)
        - (∑ χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (S1 ⊔ Z),
          ((Work.CharCore.irrDeg χ : ℝ)) ^ 2) from by linarith, hA, hB, hsupQ1]
  have hIH := index_subgroupOf_H_of_le_S h hS1
  have hIZ := index_sup_subgroupOf_H_of_le_S h hS1 hZQ1
  rw [hIH, hIZ]
  push_cast
  ring

/-! ## The degree structure of `𝒮(S') ∖ 𝒮(S' ⊔ Z)` -/

/-- `[S,S]`, viewed inside `S`, contains the commutator subgroup of `↥S`. -/
theorem commutator_le_FSScomm_subgroupOf (h : Work.FeitSibley.FSData G) :
    _root_.commutator ↥h.S ≤ (FSScomm h).subgroupOf h.S := by
  rw [Subgroup.subgroupOf, ← Subgroup.map_le_iff_le_comap]
  rw [show FSScomm h = ⁅h.S, h.S⁆ from rfl, Subgroup.map_subtype_commutator]

/-- **The degree of `χ ∈ 𝒮(S') ∖ 𝒮(S' ⊔ Z)` is `|D| · θ(1)`.**  Every such `χ` is induced from
`prodChar λ θ` with `S' ≤ ker λ` (so `λ` is linear) and `θ ∈ Irr Q₁`. -/
theorem X1_deg_struct (h : Work.FeitSibley.FSData G) {Z : Subgroup G} (hZQ1 : Z ≤ h.Q1)
    (hZn : h.H ≤ Subgroup.normalizer (Z : Set G)) {χ : ↥h.H → ℂ}
    (hχ : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) \
        Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ Z)) :
    ∃ θ ∈ Work.CharCore.Irr ↥h.Q1,
      Work.CharCore.irrDeg χ = Nat.card h.D * Work.CharCore.irrDeg θ := by
  classical
  have hχS' : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) := (Finset.mem_sdiff.mp hχ).1
  have hχS : χ ∈ Work.FeitSibley.scriptS h.H h.Q1 := scriptSR_subset_scriptS h _ hχS'
  obtain ⟨φ, hφirr, hφw, hχeq⟩ := (Work.FeitSibley.CharQ.scriptS_eq_image h).mp hχS
  obtain ⟨lam, hlam, theta, htheta, hφeq⟩ :=
    Work.FeitSibley.CharQ.exists_prodChar_of_mem_Irr h hφirr
  have hFSSn : h.H ≤ Subgroup.normalizer (FSScomm h : Set G) := H_le_normalizer_FSScomm h
  have hFSSQ : FSScomm h ≤ h.Q := (FSScomm_le_S h).trans h.S_le_Q
  have hφtrivS' : ∀ z : ↥h.Q, (z : G) ∈ FSScomm h → φ z = φ 1 :=
    (mem_scriptSR_indQH_iff h hφirr (by rw [← hχeq]; exact hχS) hFSSQ hFSSn).mp
      (by rw [← hχeq]; exact hχS')
  have hθ1 : theta 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec htheta]; exact Work.CharCore.irrDeg_ne_zero htheta
  have hker : ((FSScomm h).subgroupOf h.S : Set ↥h.S) ⊆ Work.CharCore.charKernel lam := by
    intro z hz
    have hzS : ((z : ↥h.S) : G) ∈ h.S := z.2
    have h1 := hφtrivS' ⟨((z : ↥h.S) : G), h.S_le_Q hzS⟩ hz
    rw [hφeq, prodChar_apply_of_mem_S h lam theta _ hzS,
      Work.FeitSibley.FSData.prodChar_one] at h1
    have h2 : lam z = lam 1 := mul_right_cancel₀ hθ1 h1
    simpa [Work.CharCore.charKernel] using h2
  have hM : _root_.commutator ↥h.S ≤ (FSScomm h).subgroupOf h.S :=
    commutator_le_FSScomm_subgroupOf h
  haveI : ((FSScomm h).subgroupOf h.S).Normal :=
    Subgroup.Normal.of_commutator_le (G := ↥h.S) (H := (FSScomm h).subgroupOf h.S) hM
  have hlam1 : Work.CharCore.irrDeg lam = 1 :=
    Work.Clifford.irrDeg_eq_one_of_commutator_le_charKernel hM hlam hker
  have hdegφ : Work.CharCore.irrDeg φ = Work.CharCore.irrDeg theta := by
    have hφirr' : h.prodChar lam theta ∈ Work.CharCore.Irr ↥h.Q := hφeq ▸ hφirr
    have h1 : (Work.CharCore.irrDeg (h.prodChar lam theta) : ℂ)
        = (Work.CharCore.irrDeg theta : ℂ) := by
      have h2 := Work.CharCore.irrDeg_spec hφirr'
      rw [Work.FeitSibley.FSData.prodChar_one, Work.CharCore.irrDeg_spec hlam,
        Work.CharCore.irrDeg_spec htheta, hlam1] at h2
      simp only [Nat.cast_one, one_mul] at h2
      exact h2.symm
    rw [hφeq]
    exact_mod_cast h1
  have hdegχ : Work.CharCore.irrDeg χ = Nat.card h.D * Work.CharCore.irrDeg φ := by
    have hχIrr : χ ∈ Work.CharCore.Irr ↥h.H := (Finset.mem_filter.mp hχS).1
    have h1 : χ 1 = (Nat.card h.D : ℂ) * (φ 1) := by
      rw [hχeq, Work.FeitSibley.CharQ.indQH_eq_indFun]
      change Work.Induction.indFun (h.Q.subgroupOf h.H) (Work.FeitSibley.CharQ.pull h φ) 1
        = (Nat.card h.D : ℂ) * (φ 1)
      rw [Work.Induction.indFun_apply_one, Work.FeitSibley.CharQ.pull_one,
        index_subgroupOf_Q h]
    have h2 : (Work.CharCore.irrDeg χ : ℂ)
        = (Nat.card h.D : ℂ) * (Work.CharCore.irrDeg φ : ℂ) := by
      rw [← Work.CharCore.irrDeg_spec hχIrr, ← Work.CharCore.irrDeg_spec hφirr, h1]
    have h3 : ((Work.CharCore.irrDeg χ : ℕ) : ℂ)
        = ((Nat.card h.D * Work.CharCore.irrDeg φ : ℕ) : ℂ) := by
      rw [h2]; push_cast; ring
    exact_mod_cast h3
  exact ⟨theta, htheta, by rw [hdegχ, hdegφ]⟩

/-! ## A `p`-power divisibility helper -/

/-- Divisors of a prime power are ordered by divisibility. -/
theorem dvd_of_le_of_dvd_prime_pow {p k a b : ℕ} (hp : p.Prime) (ha : a ∣ p ^ k)
    (hb : b ∣ p ^ k) (hab : a ≤ b) : a ∣ b := by
  have hpk : p ^ k ≠ 0 := pow_ne_zero _ hp.pos.ne'
  have ha0 : a ≠ 0 := fun h => by rw [h, zero_dvd_iff] at ha; exact hpk ha
  have hb0 : b ≠ 0 := fun h => by rw [h, zero_dvd_iff] at hb; exact hpk hb
  have hi : a = p ^ a.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd ha0 (fun {q} hq hqa => by
      have hqp : q ∣ p := hq.dvd_of_dvd_pow (dvd_trans hqa ha)
      rcases hp.eq_one_or_self_of_dvd q hqp with h1 | h2
      · exact absurd h1 hq.ne_one
      · exact h2)
  have hj : b = p ^ b.primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hb0 (fun {q} hq hqb => by
      have hqp : q ∣ p := hq.dvd_of_dvd_pow (dvd_trans hqb hb)
      rcases hp.eq_one_or_self_of_dvd q hqp with h1 | h2
      · exact absurd h1 hq.ne_one
      · exact h2)
  rw [hi, hj] at hab ⊢
  exact pow_dvd_pow p ((Nat.pow_le_pow_iff_right hp.one_lt).mp hab)

/-- If `a, b` are divisors of a prime power and `a ≤ b` then `a² ∣ b²`. -/
theorem pow_two_dvd_pow_two_of_le_of_dvd_prime_pow {p k a b : ℕ} (hp : p.Prime)
    (ha : a ∣ p ^ k) (hb : b ∣ p ^ k) (hab : a ≤ b) : a ^ 2 ∣ b ^ 2 :=
  pow_dvd_pow_of_dvd (dvd_of_le_of_dvd_prime_pow hp ha hb hab) 2


end Work.FeitSibley.Coherence
