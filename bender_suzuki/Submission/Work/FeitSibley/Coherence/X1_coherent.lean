import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.FeitSibley.Coherence.engine
import Submission.Work.FeitSibley.Coherence.coherent_union_singleton
import Submission.Work.FeitSibley.Coherence.coherent_of_degree_downward
import Submission.Work.FeitSibley.Coherence.SubFSZ_aux
import Submission.Work.FeitSibley.Coherence.deg_sq_le_of_mem_scriptSR
import Submission.Work.FeitSibley.CharQ.isometry_indLin
import Submission.Work.Coherence.NormIrr
import Submission.Work.CharCore.Coherence

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unusedVariables false

noncomputable section

open Classical

namespace Work.FeitSibley.Coherence

variable {G : Type} [Group G] [Fintype G]

/-- `X₁ = 𝒮(S') ∖ 𝒮(S' ⊔ Z)`, the set of Peterfalvi II, Appendice XII, step (3) (with
`Z = FSZ h = [Q₁,Q₁] ∩ Z(Q₁)`). -/
abbrev X1 (h : Work.FeitSibley.FSData G) : Finset (↥h.H → ℂ) :=
  Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) \
    Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ FSZ h)

theorem X1_eq (h : Work.FeitSibley.FSData G) :
    X1 h = Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) \
      Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h ⊔ FSZ h) := rfl

theorem X1_subset_scriptS (h : Work.FeitSibley.FSData G) :
    X1 h ⊆ Work.FeitSibley.scriptS h.H h.Q1 :=
  fun _ hχ => scriptSR_subset_scriptS h _ (Finset.mem_sdiff.mp hχ).1

theorem X1_irr (h : Work.FeitSibley.FSData G) {χ : ↥h.H → ℂ} (hχ : χ ∈ X1 h) :
    χ ∈ Work.CharCore.Irr ↥h.H := by
  have h1 := X1_subset_scriptS h hχ
  rw [Work.FeitSibley.scriptS, Submission.Blueprint.excludingKernel, Finset.mem_filter] at h1
  exact h1.1

theorem X1_orthonormal (h : Work.FeitSibley.FSData G) :
    Work.Coherence.Orthonormal (X1 h) :=
  Work.Coherence.irr_orthonormal_finset
    (fun _x hx => (Work.CharCore.mem_Irr_iff_coherence).mp (X1_irr h hx))

theorem X1_isometry (h : Work.FeitSibley.FSData G) :
    Work.Coherence.IsometryOn (X1 h) (Work.FeitSibley.indLin h.H) :=
  (Work.FeitSibley.CharQ.isometry_indLin h).mono (X1_subset_scriptS h)

theorem X1_tauV (h : Work.FeitSibley.FSData G) :
    ∀ α ∈ Work.Coherence.ZSpan0 (X1 h),
      Work.Coherence.IsVChar (Work.FeitSibley.indLin h.H α) ∧
        Work.FeitSibley.indLin h.H α 1 = 0 :=
  fun _ hα => isVChar_indLin_zSpan0_scriptS h
    (Work.Coherence.zSpan0_mono (X1_subset_scriptS h) hα)

/-! ## The degree structure of `X₁` -/

/-- Every `χ ∈ X₁` has degree `|D| · p^j` (Peterfalvi II, App. XII, step (3)). -/
theorem X1_irrDeg_eq (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime)
    (hpg : IsPGroup p h.Q1) {χ : ↥h.H → ℂ} (hχ : χ ∈ X1 h) :
    ∃ j : ℕ, Work.CharCore.irrDeg χ = Nat.card h.D * p ^ j := by
  rw [X1_eq] at hχ
  obtain ⟨θ, hθ, hθeq⟩ := X1_deg_struct h (FSZ_le_Q1 h) (FSZ_normal h) hχ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hdvd : Work.CharCore.irrDeg θ ∣ p ^ n := hn ▸ Work.CharCore.irr_degree_dvd_card hθ
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨k, by rw [hθeq, hk]⟩

/-- For `χ, ξ ∈ X₁` with `χ(1) ≤ ξ(1)`, `χ(1) ∣ ξ(1)`. -/
theorem X1_dvd_of_le (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime)
    (hpg : IsPGroup p h.Q1) {χ ξ : ↥h.H → ℂ} (hχ : χ ∈ X1 h) (hξ : ξ ∈ X1 h)
    (hle : Work.CharCore.irrDeg χ ≤ Work.CharCore.irrDeg ξ) :
    Work.CharCore.irrDeg χ ∣ Work.CharCore.irrDeg ξ := by
  obtain ⟨j, hj⟩ := X1_irrDeg_eq h hp hpg hχ
  obtain ⟨k, hk⟩ := X1_irrDeg_eq h hp hpg hξ
  have hDpos : 0 < Nat.card h.D := Nat.card_pos
  have hpk : p ^ j ≤ p ^ k := by
    have h' := hle
    rw [hj, hk] at h'
    exact Nat.le_of_mul_le_mul_left h' hDpos
  have hjk : j ≤ k := (Nat.pow_le_pow_iff_right hp.one_lt).mp hpk
  rw [hj, hk]
  exact Nat.mul_dvd_mul_left _ (pow_dvd_pow p hjk)

/-- For `χ, ξ ∈ X₁` with `ξ(1) < χ(1)`, `2 · ξ(1) < χ(1)` (the degrees are powers of the odd
prime `p`). -/
theorem X1_two_mul_lt (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpg : IsPGroup p h.Q1) {χ ξ : ↥h.H → ℂ} (hχ : χ ∈ X1 h) (hξ : ξ ∈ X1 h)
    (hlt : Work.CharCore.irrDeg ξ < Work.CharCore.irrDeg χ) :
    2 * Work.CharCore.irrDeg ξ < Work.CharCore.irrDeg χ := by
  obtain ⟨j, hj⟩ := X1_irrDeg_eq h hp hpg hχ
  obtain ⟨k, hk⟩ := X1_irrDeg_eq h hp hpg hξ
  have hp3 : 3 ≤ p := hp.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hDpos : 0 < Nat.card h.D := Nat.card_pos
  have hpk : p ^ k < p ^ j := by
    have h' := hlt
    rw [hj, hk] at h'
    exact Nat.lt_of_mul_lt_mul_left h'
  have hkj : k < j := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hpk
  have hkey : p * Work.CharCore.irrDeg ξ ≤ Work.CharCore.irrDeg χ := by
    rw [hj, hk]
    calc p * (Nat.card h.D * p ^ k) = Nat.card h.D * p ^ (k + 1) := by ring
      _ ≤ Nat.card h.D * p ^ j :=
          Nat.mul_le_mul_left _ (pow_le_pow_right₀ hp.one_le (by omega))
  have h3 : 3 * Work.CharCore.irrDeg ξ ≤ Work.CharCore.irrDeg χ :=
    (Nat.mul_le_mul_right _ hp3).trans hkey
  have hpos : 0 < Work.CharCore.irrDeg ξ := Work.CharCore.irrDeg_pos (X1_irr h hξ)
  omega

/-! ## The degree-square sum over `X₁` is divisible by `χ(1)²` -/

/-- For every `χ ∈ X₁`, `χ(1)²` divides the total degree-square sum `∑_{ξ ∈ X₁} ξ(1)²`.

This is Peterfalvi's divisibility `(3-1)`: the total is `|D|·[S:S']·(|Q₁| - [Q₁:Z])`, and
`χ(1)² = |D|²·p^{2j}` with `p^{2j} | [Q₁:Z]` (Isaacs 2.30) and `|D| | |Z| - 1`
(fixed-point-freeness of `D` on `Z`). -/
theorem X1_sq_dvd_sum (h : Work.FeitSibley.FSData G) {p : ℕ} (hp : p.Prime)
    (hpg : IsPGroup p h.Q1) {χ : ↥h.H → ℂ} (hχ : χ ∈ X1 h) :
    (Work.CharCore.irrDeg χ) ^ 2 ∣ ∑ ξ ∈ X1 h, (Work.CharCore.irrDeg ξ) ^ 2 := by
  classical
  obtain ⟨j, hj⟩ := X1_irrDeg_eq h hp hpg hχ
  have hZc_dvd : Nat.card ↥(FSZ h) ∣ Nat.card h.Q1 :=
    Subgroup.card_dvd_of_le (FSZ_le_Q1 h)
  have hD_dvd : Nat.card h.D ∣ Nat.card ↥(FSZ h) - 1 :=
    Work.FeitSibley.GroupTheory.D_dvd_card_sub_one h (FSZ h) (FSZ_le_Q1 h)
      (h.D_le_H.trans (FSZ_normal h))
  -- the degree bound `χ(1)² ≤ |D|² · [Q₁ : Z]`
  have hχ' : χ ∈ Work.FeitSibley.scriptSR h.H h.Q1 (FSScomm h) := by
    rw [X1_eq] at hχ; exact (Finset.mem_sdiff.mp hχ).1
  have hbound := deg_sq_le_of_mem_scriptSR h (FSScomm h) h.S (FSScomm_le_S h) le_rfl
    (FSScomm_le_S h) le_rfl hχ'
  -- simplify the index `[S : S] = 1`
  have hSS : (h.S.subgroupOf h.S).index = 1 := by
    rw [Subgroup.subgroupOf_self]; exact Subgroup.index_top
  rw [hSS, Nat.cast_one, mul_one] at hbound
  -- `p^(2j) ≤ [Q₁ : Z]`
  have hZcpos : 0 < Nat.card ↥(FSZ h) := Nat.card_pos
  have hleR : ((p ^ (2 * j) : ℕ) : ℝ) ≤ ((Nat.card h.Q1 / Nat.card ↥(FSZ h) : ℕ) : ℝ) := by
    have hDj : ((Work.CharCore.irrDeg χ : ℝ)) ^ 2
        = (Nat.card h.D : ℝ) ^ 2 * ((p : ℝ) ^ j) ^ 2 := by
      rw [hj]; push_cast; ring
    rw [hDj] at hbound
    have hdiv : ((Nat.card h.Q1 : ℝ) / (Nat.card ↥(FSZ h) : ℝ))
        = ((Nat.card h.Q1 / Nat.card ↥(FSZ h) : ℕ) : ℝ) :=
      (Nat.cast_div hZc_dvd (Nat.cast_ne_zero.mpr hZcpos.ne')).symm
    rw [hdiv] at hbound
    have hD2 : (0 : ℝ) < (Nat.card h.D : ℝ) ^ 2 := by
      have hDpos : (0 : ℝ) < (Nat.card h.D : ℝ) := by
        exact_mod_cast (Nat.card_pos (α := ↥h.D))
      positivity
    have hcancel : ((p : ℝ) ^ j) ^ 2 ≤ ((Nat.card h.Q1 / Nat.card ↥(FSZ h) : ℕ) : ℝ) := by
      nlinarith [hbound, hD2]
    have hpw : ((p : ℝ) ^ j) ^ 2 = ((p ^ (2 * j) : ℕ) : ℝ) := by
      rw [← pow_mul, mul_comm j 2, Nat.cast_pow]
    rwa [hpw] at hcancel
  have hle : p ^ (2 * j) ≤ Nat.card h.Q1 / Nat.card ↥(FSZ h) := Nat.cast_le.mp hleR
  -- `p^(2j) | [Q₁ : Z]`
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hpg.exists_card_eq
  have hb_dvd : Nat.card h.Q1 / Nat.card ↥(FSZ h) ∣ p ^ n :=
    ⟨Nat.card ↥(FSZ h), by rw [← hn]; exact (Nat.div_mul_cancel hZc_dvd).symm⟩
  have ha_dvd : p ^ (2 * j) ∣ p ^ n := by
    refine pow_dvd_pow p ?_
    have h1 : p ^ (2 * j) ≤ p ^ n :=
      hle.trans (by rw [hn]; exact Nat.div_le_self _ _)
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h1
  have hp2j_dvd : p ^ (2 * j) ∣ Nat.card h.Q1 / Nat.card ↥(FSZ h) :=
    dvd_of_le_of_dvd_prime_pow hp ha_dvd hb_dvd hle
  -- assemble
  have hT := sum_deg_sq_scriptSR_sdiff h (FSZ_le_Q1 h) (FSZ_normal h)
  rw [X1_eq]
  rw [hT, hj]
  obtain ⟨q, hq⟩ := hp2j_dvd
  obtain ⟨f, hf⟩ := hD_dvd
  refine ⟨Nat.card h.S / Nat.card (FSScomm h) * q * f, ?_⟩
  have hsub1 : Nat.card h.Q1 - Nat.card h.Q1 / Nat.card ↥(FSZ h)
      = (Nat.card h.Q1 / Nat.card ↥(FSZ h)) * (Nat.card ↥(FSZ h) - 1) := by
    nth_rewrite 1 [show Nat.card h.Q1
        = (Nat.card h.Q1 / Nat.card ↥(FSZ h)) * Nat.card ↥(FSZ h) from
      (Nat.div_mul_cancel hZc_dvd).symm]
    rw [Nat.mul_sub_left_distrib, mul_one]
  have hpow : p ^ (2 * j) = (p ^ j) ^ 2 := by rw [mul_comm 2 j, pow_mul]
  rw [hsub1, hq, hf, hpow]
  ring

/-! ## The main theorem -/

theorem X1_coherent {G : Type} [Group G] [Fintype G] (h : Work.FeitSibley.FSData G)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpg : IsPGroup p h.Q1)
    (hab : ⁅h.Q1, h.Q1⁆ ≠ ⊥) :
    Work.Coherence.Coherent
      (Work.FeitSibley.scriptSR h.H h.Q1 (Work.FeitSibley.Coherence.FSScomm h) \
        Work.FeitSibley.scriptSR h.H h.Q1
          (Work.FeitSibley.Coherence.FSScomm h ⊔ Work.FeitSibley.Coherence.FSZ h))
      (Work.FeitSibley.indLin h.H) := by
  classical
  show Work.Coherence.Coherent (X1 h) (Work.FeitSibley.indLin h.H)
  by_cases hne : X1 h = ∅
  · rw [hne]; exact Work.Coherence.coherent_empty
  · obtain ⟨χ₀, hχ₀, hχ₀min⟩ :=
      Finset.exists_min_image (X1 h) (fun χ => Work.CharCore.irrDeg χ)
        (Finset.nonempty_iff_ne_empty.mpr hne)
    refine coherent_of_degree_downward (fun χ hχ => X1_irr h hχ) (X1_orthonormal h)
      (X1_isometry h) (X1_tauV h) hχ₀ ?_ hχ₀min ?_ ?_
    · rw [Work.CharCore.irrDeg_spec (X1_irr h hχ₀)]
      exact_mod_cast (Work.CharCore.irrDeg_pos (X1_irr h hχ₀)).ne'
    · intro χ hχ
      obtain ⟨j, hj⟩ := X1_irrDeg_eq h hp hpg hχ
      obtain ⟨k, hk⟩ := X1_irrDeg_eq h hp hpg hχ₀
      have hDpos : 0 < Nat.card h.D := Nat.card_pos
      have hle : p ^ k ≤ p ^ j := by
        have h' := hχ₀min χ hχ
        rw [hk, hj] at h'
        exact Nat.le_of_mul_le_mul_left h' hDpos
      have hkj : k ≤ j := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
      refine ⟨p ^ (j - k), ?_⟩
      have hgoal : Work.CharCore.irrDeg χ = p ^ (j - k) * Work.CharCore.irrDeg χ₀ := by
        rw [hj, hk]
        have hpj : p ^ j = p ^ (j - k) * p ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hkj]
        rw [hpj]; ring
      rw [Work.CharCore.irrDeg_spec (X1_irr h hχ), hgoal,
        Work.CharCore.irrDeg_spec (X1_irr h hχ₀)]
      push_cast
      ring
    · intro χ hχ hlt
      have hdvdT : (Work.CharCore.irrDeg χ) ^ 2 ∣ ∑ ξ ∈ X1 h,
          (Work.CharCore.irrDeg ξ) ^ 2 := X1_sq_dvd_sum h hp hpg hχ
      have hdvdQ : (Work.CharCore.irrDeg χ) ^ 2 ∣
          ∑ ξ ∈ (X1 h).filter (fun ξ => ¬ Work.CharCore.irrDeg ξ < Work.CharCore.irrDeg χ),
            (Work.CharCore.irrDeg ξ) ^ 2 := by
        refine Finset.dvd_sum (fun ξ hξ => ?_)
        rw [Finset.mem_filter] at hξ
        exact pow_dvd_pow_of_dvd
          (X1_dvd_of_le h hp hpg hχ hξ.1 (le_of_not_gt hξ.2)) 2
      have hsplit : (∑ ξ ∈ (X1 h).filter
              (fun ξ => Work.CharCore.irrDeg ξ < Work.CharCore.irrDeg χ),
            (Work.CharCore.irrDeg ξ) ^ 2)
          + (∑ ξ ∈ (X1 h).filter
              (fun ξ => ¬ Work.CharCore.irrDeg ξ < Work.CharCore.irrDeg χ),
            (Work.CharCore.irrDeg ξ) ^ 2)
          = ∑ ξ ∈ X1 h, (Work.CharCore.irrDeg ξ) ^ 2 :=
        Finset.sum_filter_add_sum_filter_not (s := X1 h)
          (p := fun ξ => Work.CharCore.irrDeg ξ < Work.CharCore.irrDeg χ)
          (f := fun ξ => (Work.CharCore.irrDeg ξ) ^ 2)
      have hPeq : (∑ ξ ∈ (X1 h).filter
              (fun ξ => Work.CharCore.irrDeg ξ < Work.CharCore.irrDeg χ),
            (Work.CharCore.irrDeg ξ) ^ 2)
          = (∑ ξ ∈ X1 h, (Work.CharCore.irrDeg ξ) ^ 2)
            - (∑ ξ ∈ (X1 h).filter
                (fun ξ => ¬ Work.CharCore.irrDeg ξ < Work.CharCore.irrDeg χ),
              (Work.CharCore.irrDeg ξ) ^ 2) := by omega
      have hdvdP : (Work.CharCore.irrDeg χ) ^ 2 ∣
          ∑ ξ ∈ (X1 h).filter (fun ξ => Work.CharCore.irrDeg ξ < Work.CharCore.irrDeg χ),
            (Work.CharCore.irrDeg ξ) ^ 2 := by
        rw [hPeq]
        exact Nat.dvd_sub hdvdT hdvdQ
      have hsumpos : 0 < ∑ ξ ∈ (X1 h).filter
          (fun ξ => Work.CharCore.irrDeg ξ < Work.CharCore.irrDeg χ),
          (Work.CharCore.irrDeg ξ) ^ 2 := by
        refine Finset.sum_pos' (fun ξ _ => Nat.zero_le _) ?_
        exact ⟨χ₀, by rw [Finset.mem_filter]; exact ⟨hχ₀, hlt⟩,
          pow_pos (Work.CharCore.irrDeg_pos (X1_irr h hχ₀)) 2⟩
      have hge : (Work.CharCore.irrDeg χ) ^ 2 ≤ ∑ ξ ∈ (X1 h).filter
          (fun ξ => Work.CharCore.irrDeg ξ < Work.CharCore.irrDeg χ),
          (Work.CharCore.irrDeg ξ) ^ 2 := Nat.le_of_dvd hsumpos hdvdP
      have h2 : 2 * Work.CharCore.irrDeg χ₀ < Work.CharCore.irrDeg χ :=
        X1_two_mul_lt h hp hp2 hpg hχ hχ₀ hlt
      have hpos : 0 < Work.CharCore.irrDeg χ := Work.CharCore.irrDeg_pos (X1_irr h hχ)
      have hlt2 : 2 * Work.CharCore.irrDeg χ₀ * Work.CharCore.irrDeg χ
          < (Work.CharCore.irrDeg χ) ^ 2 := by nlinarith
      exact lt_of_lt_of_le hlt2 hge

end Work.FeitSibley.Coherence
