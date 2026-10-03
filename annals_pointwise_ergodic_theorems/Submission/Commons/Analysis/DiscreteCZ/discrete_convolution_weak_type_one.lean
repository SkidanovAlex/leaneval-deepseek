import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.DiscreteCZ.cz_bad_part_int_lintegral
import Submission.Commons.Analysis.DiscreteCZ.count_natAbs_lt_le
import Submission.Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal
import Submission.Port.Aesm

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace Commons.Analysis.DiscreteCZ

set_option autoImplicit false

noncomputable section


private def dlo (k : ℕ) (m : ℤ) : ℤ := m * 2 ^ k
private def dhi (k : ℕ) (m : ℤ) : ℤ := (m + 1) * 2 ^ k
private def dIv (k : ℕ) (m : ℤ) : Set ℤ := Set.Ico (dlo k m) (dhi k m)

private lemma dlo_lt_dhi (k : ℕ) (m : ℤ) : dlo k m < dhi k m := by
  simp only [dlo, dhi]
  have : (0:ℤ) < 2 ^ k := by positivity
  nlinarith

private lemma dhi_sub_dlo (k : ℕ) (m : ℤ) : dhi k m - dlo k m = 2 ^ k := by
  simp only [dlo, dhi]; ring

private def nrm {E : Type*} [SeminormedAddCommGroup E] (f : ℤ → E) : ℤ → ℝ := fun x => ‖f x‖

private lemma mem_dIv (k : ℕ) (m x : ℤ) : x ∈ dIv k m ↔ x / 2 ^ k = m := by
  have hpos : (0:ℤ) < 2 ^ k := by positivity
  simp only [dIv, dlo, dhi, Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · rw [Int.ediv_le_iff_le_mul hpos]; nlinarith
    · rw [Int.le_ediv_iff_mul_le hpos]; exact h1
  · intro h
    constructor
    · rw [← Int.le_ediv_iff_mul_le hpos]; omega
    · rw [← Int.ediv_lt_iff_lt_mul hpos]; omega

private lemma anc_bounds (k k' : ℕ) (h : k ≤ k') (m x : ℤ)
    (hx1 : m * 2 ^ k ≤ x) (hx2 : x < (m + 1) * 2 ^ k) :
    (m / 2 ^ (k' - k)) * 2 ^ k' ≤ x ∧ x < (m / 2 ^ (k' - k) + 1) * 2 ^ k' := by
  set d : ℤ := 2 ^ (k'-k) with hd
  have hdpos : 0 < d := by rw [hd]; positivity
  have hpk : (2:ℤ)^k' = d * 2^k := by rw [hd, ← pow_add]; congr 1; omega
  have hmod := EuclideanDomain.div_add_mod m d
  have hmodnn := Int.emod_nonneg m (ne_of_gt hdpos)
  have hmodlt := Int.emod_lt_of_pos m hdpos
  have h2k : (0:ℤ) < 2^k := by positivity
  constructor
  · have heq : (m/d) * 2^k' = (m/d) * d * 2^k := by rw [hpk]; ring
    rw [heq]
    have h1 : (m/d) * d ≤ m := by
      have := Int.ediv_mul_le m (ne_of_gt hdpos); linarith [hmod]
    calc (m/d) * d * 2^k ≤ m * 2^k := mul_le_mul_of_nonneg_right h1 (le_of_lt h2k)
      _ ≤ x := hx1
  · have hle : m % d + 1 ≤ d := by omega
    have hm1 : m + 1 = d * (m/d) + (m % d + 1) := by linarith [hmod]
    calc x < (m+1) * 2^k := hx2
      _ = (d * (m/d) + (m % d + 1)) * 2^k := by rw [hm1]
      _ = (m/d) * d * 2^k + (m % d + 1) * 2^k := by ring
      _ ≤ (m/d) * d * 2^k + d * 2^k :=
            add_le_add_right (mul_le_mul_of_nonneg_right hle (le_of_lt h2k)) _
      _ = (m/d + 1) * (d * 2^k) := by ring
      _ = (m/d + 1) * 2^k' := by rw [hpk]

private lemma dIv_subset_ancestor (k k' : ℕ) (h : k ≤ k') (m : ℤ) :
    dIv k m ⊆ dIv k' (m / 2 ^ (k' - k)) := by
  intro x hx
  rw [mem_dIv] at hx ⊢
  have hposk : (0:ℤ) < 2^k := by positivity
  have hposk' : (0:ℤ) < 2^k' := by positivity
  have hx1 : m * 2 ^ k ≤ x := by rw [← Int.le_ediv_iff_mul_le hposk, hx]
  have hx2 : x < (m + 1) * 2 ^ k := by rw [← Int.ediv_lt_iff_lt_mul hposk, hx]; exact lt_add_one m
  obtain ⟨h1, h2⟩ := anc_bounds k k' h m x hx1 hx2
  apply le_antisymm
  · rw [Int.ediv_le_iff_le_mul hposk']
    rw [show (m / 2 ^ (k' - k)) * 2 ^ k' + 2 ^ k' = (m / 2 ^ (k' - k) + 1) * 2 ^ k' by ring]
    exact h2
  · rw [Int.le_ediv_iff_mul_le hposk']; exact h1

private lemma ediv_pow_of_le {k k' : ℕ} (h : k ≤ k') (x : ℤ) :
    x / 2 ^ k' = (x / 2 ^ k) / 2 ^ (k' - k) := by
  have hpk : (2:ℤ)^k * 2^(k'-k) = 2^k' := by rw [← pow_add]; congr 1; omega
  rw [Int.ediv_ediv]
  have hposk : ¬ ((2:ℤ)^k < 0) := not_lt.mpr (by positivity)
  rw [if_neg (by simp [hposk]), sub_zero, hpk]

private lemma dIv_subset_of_inter (k k' : ℕ) (m m' : ℤ) (hkk : k ≤ k')
    (hne : (dIv k m ∩ dIv k' m').Nonempty) : dIv k m ⊆ dIv k' m' := by
  obtain ⟨x, hx1, hx2⟩ := hne
  rw [mem_dIv] at hx1 hx2
  have hm' : m' = m / 2 ^ (k' - k) := by
    calc m' = x / 2 ^ k' := hx2.symm
      _ = (x / 2 ^ k) / 2 ^ (k' - k) := ediv_pow_of_le hkk x
      _ = m / 2 ^ (k' - k) := by rw [hx1]
  rw [hm']; exact dIv_subset_ancestor k k' hkk m

private lemma eq_ancestor_of_mem {k k' : ℕ} (h : k ≤ k') {m m' : ℤ}
    (hne : (dIv k m ∩ dIv k' m').Nonempty) : m' = m / 2^(k'-k) := by
  obtain ⟨x, hx1, hx2⟩ := hne
  rw [mem_dIv] at hx1 hx2
  calc m' = x / 2 ^ k' := hx2.symm
    _ = (x / 2 ^ k) / 2 ^ (k' - k) := ediv_pow_of_le h x
    _ = m / 2 ^ (k' - k) := by rw [hx1]

private def dS (u : ℤ → ℝ) (k : ℕ) (m : ℤ) : ℝ := ∑ x ∈ Finset.Ico (dlo k m) (dhi k m), u x

private def dSel (u : ℤ → ℝ) (α : ℝ) (k : ℕ) (m : ℤ) : Prop := α * (2:ℝ)^k < dS u k m

private def dMax (u : ℤ → ℝ) (α : ℝ) (k : ℕ) (m : ℤ) : Prop :=
  dSel u α k m ∧ ∀ k' m', k < k' → dSel u α k' m' → dIv k m ⊆ dIv k' m' → False

private lemma dS_mono_ancestor {u : ℤ → ℝ} (hu : ∀ x, 0 ≤ u x) {k k' : ℕ} (h : k ≤ k') (m : ℤ) :
    dS u k m ≤ dS u k' (m / 2 ^ (k' - k)) := by
  unfold dS
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · rw [← Finset.coe_subset, Finset.coe_Ico, Finset.coe_Ico]
    exact dIv_subset_ancestor k k' h m
  · intro x _ _; exact hu x

private lemma dS_le_M {u : ℤ → ℝ} (hu : ∀ x, 0 ≤ u x) (hsum : Summable u) (k : ℕ) (m : ℤ) :
    dS u k m ≤ ∑' x, u x := by
  unfold dS
  exact Summable.sum_le_tsum _ (fun x _ => hu x) hsum

private lemma dSel_zero {u : ℤ → ℝ} {α : ℝ} {x : ℤ} (h : α < u x) : dSel u α 0 x := by
  unfold dSel dS dlo dhi
  have hI : Finset.Ico (x * 2^0) ((x+1) * 2^0) = {x} := by
    have h1 : (2:ℤ)^0 = 1 := pow_zero 2
    rw [h1, mul_one, mul_one]
    ext y; simp only [Finset.mem_Ico, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; omega
    · rintro rfl; omega
  rw [hI, Finset.sum_singleton]
  simpa using h

private lemma dMax_parent_not_sel {u : ℤ → ℝ} {α : ℝ} {k : ℕ} {m : ℤ} (h : dMax u α k m) :
    ¬ dSel u α (k+1) (m / 2) := by
  intro hsel
  refine h.2 (k+1) (m/2) (by omega) hsel ?_
  have := dIv_subset_ancestor k (k+1) (by omega) m
  simpa [show k + 1 - k = 1 by omega, pow_one] using this

private lemma dMax_disjoint {u : ℤ → ℝ} {α : ℝ} {m₁ m₂ : ℤ} {k₁ k₂ : ℕ}
    (h₁ : dMax u α k₁ m₁) (h₂ : dMax u α k₂ m₂)
    (hne : (k₁, m₁) ≠ (k₂, m₂)) : Disjoint (dIv k₁ m₁) (dIv k₂ m₂) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
  rintro ⟨x, hx1, hx2⟩
  rcases lt_trichotomy k₁ k₂ with hlt | heq | hgt
  · exact h₁.2 k₂ m₂ hlt h₂.1 (dIv_subset_of_inter k₁ k₂ m₁ m₂ (le_of_lt hlt) ⟨x, hx1, hx2⟩)
  · subst heq
    rw [mem_dIv] at hx1 hx2
    exact hne (by rw [← hx1, hx2])
  · exact h₂.2 k₁ m₁ hgt h₁.1 (dIv_subset_of_inter k₂ k₁ m₂ m₁ (le_of_lt hgt) ⟨x, hx2, hx1⟩)

private theorem calderon_zygmund_decomposition_int_finset
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℤ → E) (hf : Summable (fun x => ‖f x‖)) (α : ℝ) (hα : 0 < α) :
    ∃ (S : Finset (ℕ × ℤ)) (g : ℤ → E) (b : ℕ × ℤ → ℤ → E),
      (∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint (dIv p.1 p.2) (dIv q.1 q.2)) ∧
      (∀ p ∈ S, α * (2:ℝ)^p.1 ≤ ∑ x ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), ‖f x‖) ∧
      (∀ p ∈ S, ∑ x ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), ‖f x‖ ≤ 2 * α * (2:ℝ)^p.1) ∧
      (∀ p ∈ S, ∀ x ∈ dIv p.1 p.2,
          b p x = f x - ((2:ℝ)^p.1)⁻¹ • (∑ t ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), f t)) ∧
      (∀ p ∈ S, ∀ x, x ∉ dIv p.1 p.2 → b p x = 0) ∧
      (∀ x, x ∉ ⋃ p ∈ S, dIv p.1 p.2 → g x = f x) ∧
      (∀ p ∈ S, ∀ x ∈ dIv p.1 p.2,
          g x = ((2:ℝ)^p.1)⁻¹ • (∑ t ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), f t)) ∧
      (∀ x, x ∉ ⋃ p ∈ S, dIv p.1 p.2 → ‖f x‖ ≤ α) ∧
      (∀ x, ‖g x‖ ≤ 2 * α) ∧
      (∑ p ∈ S, (2:ℝ)^p.1 ≤ α⁻¹ * ∑' x, ‖f x‖) ∧
      (∀ x, f x = g x + ∑ p ∈ S, b p x) := by
  classical
  have hunn : ∀ x, 0 ≤ nrm f x := fun x => norm_nonneg _
  obtain ⟨K0, hK0⟩ : ∃ N : ℕ, (∑' x, nrm f x) ≤ α * (2:ℝ)^N := by
    have ht : Filter.Tendsto (fun n : ℕ => α * (2:ℝ)^n) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hα
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ) < 2))
    exact (ht.eventually_ge_atTop (∑' x, nrm f x)).exists
  have htop : ∀ m : ℤ, ¬ dSel (nrm f) α K0 m := by
    intro m hsel
    have h1 : dS (nrm f) K0 m ≤ ∑' x, nrm f x := dS_le_M hunn hf K0 m
    unfold dSel at hsel
    linarith
  let kstar : ℤ → ℕ := fun x => Nat.findGreatest (fun k => dSel (nrm f) α k (x / 2^k)) K0
  have hkstar_not : ∀ x, ∀ n, kstar x < n → ¬ dSel (nrm f) α n (x / 2^n) := by
    intro x n hn
    by_cases hnK : n ≤ K0
    · have := (Nat.findGreatest_eq_iff (P := fun k => dSel (nrm f) α k (x / 2^k)) (k := K0)).mp rfl
      exact this.2.2 hn hnK
    · push Not at hnK
      intro hsel
      unfold dSel at hsel
      have h1 : dS (nrm f) n (x / 2^n) ≤ ∑' x, nrm f x := dS_le_M hunn hf n (x/2^n)
      have h2 : (2:ℝ)^K0 < (2:ℝ)^n := pow_lt_pow_right₀ (by norm_num) hnK
      have h3 : α * (2:ℝ)^K0 < α * (2:ℝ)^n := mul_lt_mul_of_pos_left h2 hα
      linarith
  have hkstar_sel : ∀ x, α < nrm f x → dSel (nrm f) α (kstar x) (x / 2^(kstar x)) := by
    intro x hx
    rcases Nat.eq_zero_or_pos (kstar x) with h0 | hpos
    · rw [h0]; simpa using dSel_zero hx
    · have := (Nat.findGreatest_eq_iff (P := fun k => dSel (nrm f) α k (x / 2^k)) (k := K0)).mp rfl
      exact this.2.1 (ne_of_gt hpos)
  have dMaxAt : ∀ x, α < nrm f x → dMax (nrm f) α (kstar x) (x / 2^(kstar x)) := by
    intro x hx
    refine ⟨hkstar_sel x hx, ?_⟩
    intro k' m' hlt hsel hsub
    have hmem : x ∈ dIv (kstar x) (x / 2^(kstar x)) := by rw [mem_dIv]
    have hne : (dIv (kstar x) (x / 2^(kstar x)) ∩ dIv k' m').Nonempty := ⟨x, hmem, hsub hmem⟩
    have hm' := eq_ancestor_of_mem (le_of_lt hlt) hne
    rw [hm'] at hsel
    rw [← ediv_pow_of_le (le_of_lt hlt) x] at hsel
    exact hkstar_not x k' hlt hsel
  let D : Set ℤ := {x | α < nrm f x}
  have hDfin : D.Finite := by
    by_contra hcon
    let Nn : ℕ := ⌊(∑' x, nrm f x) / α⌋₊ + 1
    obtain ⟨T, hTsub, hTcard⟩ := Set.Infinite.exists_subset_card_eq (s := D) hcon Nn
    have hTne : T.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]; intro he
      have hc : T.card = 0 := by rw [he]; simp
      rw [hTcard] at hc; simp [Nn] at hc
    have hpt : ∀ x ∈ T, α ≤ nrm f x := fun x hxT => le_of_lt (hTsub hxT)
    have hstrict : ∃ x ∈ T, α < nrm f x := by
      obtain ⟨x, hx⟩ := hTne; exact ⟨x, hx, hTsub hx⟩
    have hlt1 : ∑ x ∈ T, α < ∑ x ∈ T, nrm f x := Finset.sum_lt_sum hpt hstrict
    have h2 : ∑ x ∈ T, nrm f x ≤ ∑' x, nrm f x := Summable.sum_le_tsum _ (fun x _ => hunn x) hf
    have h3 : ((T.card : ℕ) : ℝ) * α = ∑ x ∈ T, α := by rw [Finset.sum_const, nsmul_eq_mul]
    have h4 : ((Nn : ℕ) : ℝ) * α > ∑' x, nrm f x := by
      have h5 : (∑' x, nrm f x) / α < (Nn : ℝ) := by
        rw [show Nn = ⌊(∑' x, nrm f x) / α⌋₊ + 1 from rfl]; push_cast; exact Nat.lt_floor_add_one _
      rw [div_lt_iff₀ hα] at h5; linarith
    rw [hTcard] at h3
    nlinarith [hlt1, h2, h3, h4]
  let cf : ℤ → ℕ × ℤ := fun x => (kstar x, x / 2^(kstar x))
  let S : Finset (ℕ × ℤ) := hDfin.toFinset.image cf
  have hSmem : ∀ p, p ∈ S ↔ ∃ x ∈ D, cf x = p := by
    intro p
    change p ∈ hDfin.toFinset.image cf ↔ ∃ x, x ∈ D ∧ cf x = p
    rw [Finset.mem_image]
    constructor
    · rintro ⟨x, hx, hxp⟩; exact ⟨x, (Set.Finite.mem_toFinset hDfin).mp hx, hxp⟩
    · rintro ⟨x, hxD, hxp⟩; exact ⟨x, (Set.Finite.mem_toFinset hDfin).mpr hxD, hxp⟩
  have dMax_mem : ∀ p ∈ S, dMax (nrm f) α p.1 p.2 := by
    intro p hp
    obtain ⟨x, hxD, hpx⟩ := (hSmem p).mp hp
    rw [← hpx]; exact dMaxAt x hxD
  let avg : ℕ × ℤ → E :=
    fun p => ((2:ℝ)^p.1)⁻¹ • (∑ t ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), f t)
  let b : ℕ × ℤ → ℤ → E := fun p x => if x ∈ dIv p.1 p.2 then f x - avg p else 0
  let g : ℤ → E := fun x => f x - ∑ p ∈ S, b p x
  have hsize_pos : ∀ p : ℕ × ℤ, 0 < (2:ℝ)^p.1 := fun p => by positivity
  have hdisj : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Disjoint (dIv p.1 p.2) (dIv q.1 q.2) :=
    fun p hp q hq hpq => dMax_disjoint (dMax_mem p hp) (dMax_mem q hq) hpq
  have hlow : ∀ p ∈ S, α * (2:ℝ)^p.1 ≤ ∑ x ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), ‖f x‖ := by
    intro p hp
    have hsel := (dMax_mem p hp).1
    simpa only [dSel, dS, nrm] using le_of_lt hsel
  have hhigh : ∀ p ∈ S,
      ∑ x ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), ‖f x‖ ≤ 2 * α * (2:ℝ)^p.1 := by
    intro p hp
    have hpar := dMax_parent_not_sel (dMax_mem p hp)
    have hpar' : dS (nrm f) (p.1+1) (p.2 / 2) ≤ α * (2:ℝ)^(p.1+1) := by
      unfold dSel at hpar; exact not_lt.mp hpar
    have hmono : dS (nrm f) p.1 p.2 ≤ dS (nrm f) (p.1+1) (p.2 / 2) := by
      have := dS_mono_ancestor hunn (Nat.le_succ p.1) p.2
      simpa [show p.1 + 1 - p.1 = 1 by omega, pow_one] using this
    have hval : dS (nrm f) p.1 p.2 ≤ α * (2:ℝ)^(p.1+1) := le_trans hmono hpar'
    have he : α * (2:ℝ)^(p.1+1) = 2 * α * (2:ℝ)^p.1 := by rw [pow_succ]; ring
    simpa only [dS, nrm, he] using hval
  have hbin : ∀ p ∈ S, ∀ x ∈ dIv p.1 p.2, b p x = f x - avg p := by
    intro p hp x hx
    show (if x ∈ dIv p.1 p.2 then f x - avg p else 0) = f x - avg p
    rw [if_pos hx]
  have hbout : ∀ p ∈ S, ∀ x ∉ dIv p.1 p.2, b p x = 0 := by
    intro p hp x hx
    show (if x ∈ dIv p.1 p.2 then f x - avg p else 0) = 0
    rw [if_neg hx]
  have hbdef1 : ∀ p ∈ S, ∀ x ∈ dIv p.1 p.2,
      b p x = f x - ((2:ℝ)^p.1)⁻¹ • (∑ t ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), f t) :=
    fun p hp x hx => hbin p hp x hx
  have hbdef2 : ∀ p ∈ S, ∀ x, x ∉ dIv p.1 p.2 → b p x = 0 :=
    fun p hp x hx => hbout p hp x hx
  have hgout : ∀ x, x ∉ ⋃ p ∈ S, dIv p.1 p.2 → g x = f x := by
    intro x hx
    have hb0 : ∀ p ∈ S, b p x = 0 := by
      intro p hp
      exact hbout p hp x (fun hmem => hx (by simp only [Set.mem_iUnion]; exact ⟨p, hp, hmem⟩))
    show f x - ∑ p ∈ S, b p x = f x
    rw [Finset.sum_eq_zero hb0, sub_zero]
  have hgin : ∀ p ∈ S, ∀ x ∈ dIv p.1 p.2,
      g x = ((2:ℝ)^p.1)⁻¹ • (∑ t ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), f t) := by
    intro p hp x hx
    have hsingle : ∑ q ∈ S, b q x = b p x := by
      apply Finset.sum_eq_single_of_mem p hp
      intro q hq hqp
      exact hbout q hq x (fun hmem =>
        (Set.disjoint_left.mp (hdisj p hp q hq (Ne.symm hqp)) hx) hmem)
    have hbp : b p x = f x - avg p := hbin p hp x hx
    show f x - ∑ q ∈ S, b q x = avg p
    rw [hsingle, hbp]
    abel
  have hgood : ∀ x, x ∉ ⋃ p ∈ S, dIv p.1 p.2 → ‖f x‖ ≤ α := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have hxD : x ∈ D := hcon
    have hpx : cf x ∈ S := (hSmem (cf x)).mpr ⟨x, hxD, rfl⟩
    have hxin : x ∈ dIv (cf x).1 (cf x).2 := by
      change x ∈ dIv (kstar x) (x / 2^(kstar x)); rw [mem_dIv]
    exact hx (by simp only [Set.mem_iUnion]; exact ⟨cf x, hpx, hxin⟩)
  have hupper : ∀ x, ‖g x‖ ≤ 2 * α := by
    intro x
    by_cases hxU : x ∈ ⋃ p ∈ S, dIv p.1 p.2
    · obtain ⟨p, hp, hx⟩ := by simpa only [Set.mem_iUnion] using hxU
      rw [hgin p hp x hx]
      have h1 : ‖((2:ℝ)^p.1)⁻¹ • (∑ t ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), f t)‖
          ≤ ((2:ℝ)^p.1)⁻¹ * (∑ t ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), ‖f t‖) := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hsize_pos p))]
        exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (le_of_lt (inv_pos.mpr (hsize_pos p)))
      have h2 := hhigh p hp
      calc ‖((2:ℝ)^p.1)⁻¹ • (∑ t ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), f t)‖
          ≤ ((2:ℝ)^p.1)⁻¹ * (∑ t ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), ‖f t‖) := h1
        _ ≤ ((2:ℝ)^p.1)⁻¹ * (2 * α * (2:ℝ)^p.1) :=
              mul_le_mul_of_nonneg_left h2 (le_of_lt (inv_pos.mpr (hsize_pos p)))
        _ = 2 * α := by
              have hne : (2:ℝ)^p.1 ≠ 0 := ne_of_gt (hsize_pos p)
              calc ((2:ℝ)^p.1)⁻¹ * (2 * α * (2:ℝ)^p.1)
                  = 2 * α * (((2:ℝ)^p.1)⁻¹ * (2:ℝ)^p.1) := by ring
                _ = 2 * α * 1 := by rw [inv_mul_cancel₀ hne]
                _ = 2 * α := by ring
    · rw [hgout x hxU]
      exact le_trans (hgood x hxU) (by linarith)
  have hsumlen : ∑ p ∈ S, (2:ℝ)^p.1 ≤ α⁻¹ * ∑' x, ‖f x‖ := by
    have hb : ∀ p ∈ S, (2:ℝ)^p.1 ≤ α⁻¹ * dS (nrm f) p.1 p.2 := by
      intro p hp
      have hsel := (dMax_mem p hp).1
      rw [inv_mul_eq_div, le_div_iff₀ hα]
      unfold dSel at hsel; linarith
    have hpair : (↑S : Set (ℕ × ℤ)).PairwiseDisjoint
        (fun p => Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2)) := by
      intro p hp q hq hpq
      exact Finset.disjoint_coe.mp (by
        rw [Finset.coe_Ico, Finset.coe_Ico]
        exact hdisj p hp q hq hpq)
    have hbU : ∑ p ∈ S, dS (nrm f) p.1 p.2
        = ∑ x ∈ S.biUnion (fun p => Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2)), nrm f x := by
      rw [Finset.sum_biUnion hpair]
      exact Finset.sum_congr rfl (fun p _ => rfl)
    calc ∑ p ∈ S, (2:ℝ)^p.1
        ≤ ∑ p ∈ S, α⁻¹ * dS (nrm f) p.1 p.2 := Finset.sum_le_sum hb
      _ = α⁻¹ * ∑ p ∈ S, dS (nrm f) p.1 p.2 := by rw [Finset.mul_sum]
      _ = α⁻¹ * ∑ x ∈ S.biUnion (fun p => Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2)), nrm f x := by
            rw [hbU]
      _ ≤ α⁻¹ * ∑' x, nrm f x := by
            gcongr
            exact Summable.sum_le_tsum _ (fun x _ => hunn x) hf
      _ = α⁻¹ * ∑' x, ‖f x‖ := rfl
  have hfinal : ∀ x, f x = g x + ∑ p ∈ S, b p x := by
    intro x
    show f x = f x - ∑ p ∈ S, b p x + ∑ p ∈ S, b p x
    rw [sub_add_cancel]
  exact ⟨S, g, b, hdisj, hlow, hhigh, hbdef1, hbdef2, hgout, hgin, hgood, hupper, hsumlen, hfinal⟩



private theorem summable_smul_sub_int {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (K : ℤ → ℂ) {B : ℝ} (hK : ∀ z : ℤ, ‖K z‖ ≤ B) {u : ℤ → E}
    (hu : Summable (fun y : ℤ => ‖u y‖)) (x : ℤ) :
    Summable (fun y : ℤ => K (x - y) • u y) := by
  refine Summable.of_norm_bounded (hu.mul_left B) (fun y => ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hK (x - y)) (norm_nonneg _)

private lemma summable_finset_sum_int {ι E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E]
    (s : Finset ι) (h : ι → ℤ → E) (hh : ∀ p ∈ s, Summable (h p)) :
    Summable (fun y : ℤ => ∑ p ∈ s, h p y) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (summable_zero : Summable (fun _ : ℤ => (0:E)))
  | insert p s hps ih =>
      have hps' : ∀ q ∈ s, Summable (h q) := fun q hq => hh q (Finset.mem_insert_of_mem hq)
      have hp : Summable (h p) := hh p (Finset.mem_insert_self p s)
      have heq : (fun y : ℤ => ∑ q ∈ insert p s, h q y) = fun y => h p y + ∑ q ∈ s, h q y := by
        funext y; rw [Finset.sum_insert hps]
      rw [heq]; exact hp.add (ih hps')

private theorem tsum_finset_sum_int {ι E : Type*} [AddCommMonoid E] [TopologicalSpace E] [ContinuousAdd E]
    [T2Space E] (s : Finset ι) (h : ι → ℤ → E) (hh : ∀ p ∈ s, Summable (h p)) :
    (∑' y : ℤ, ∑ p ∈ s, h p y) = ∑ p ∈ s, ∑' y : ℤ, h p y := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert p s hps ih =>
      have hps' : ∀ q ∈ s, Summable (h q) := fun q hq => hh q (Finset.mem_insert_of_mem hq)
      have hp : Summable (h p) := hh p (Finset.mem_insert_self p s)
      have hsum := summable_finset_sum_int s h hps'
      have ih' := ih hps'
      rw [show (∑' y : ℤ, ∑ q ∈ insert p s, h q y) = ∑' y : ℤ, (h p y + ∑ q ∈ s, h q y)
            from tsum_congr (fun y => Finset.sum_insert hps)]
      rw [Summable.tsum_add hp hsum, ih', Finset.sum_insert hps]

private theorem summable_enorm_iff {E : Type*} [SeminormedAddCommGroup E] (u : ℤ → E) :
    Summable (fun x : ℤ => ‖u x‖) ↔ (∑' x : ℤ, ‖u x‖ₑ) ≠ ⊤ := by
  constructor
  · intro h
    have := Summable.tsum_ofReal_ne_top (α := ℤ) h
    simpa only [ofReal_norm] using this
  · intro h
    have hcoe : (∑' x : ℤ, ‖u x‖ₑ)
        = ∑' x : ℤ, ((NNReal.mk ‖u x‖ (norm_nonneg _)) : ℝ≥0∞) := by
      apply tsum_congr; intro x
      exact (ofReal_norm (u x)).symm.trans (ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _))
    rw [hcoe] at h
    have h2 := ENNReal.tsum_coe_ne_top_iff_summable.mp h
    simpa using NNReal.summable_coe.mpr h2

private theorem enorm_tsum_eq_top_of_not_summable {E : Type*} [SeminormedAddCommGroup E]
    (u : ℤ → E) (h : ¬ Summable (fun x : ℤ => ‖u x‖)) :
    (∑' x : ℤ, ‖u x‖ₑ) = ⊤ := by
  by_contra hcon
  exact h ((summable_enorm_iff u).mpr hcon)

private theorem eLpNorm_one_count_eq {E : Type*} [SeminormedAddCommGroup E]
    (u : ℤ → E) (h : Summable (fun x : ℤ => ‖u x‖)) :
    MeasureTheory.eLpNorm u 1 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      = ENNReal.ofReal (∑' x : ℤ, ‖u x‖) := by
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), MeasureTheory.lintegral_count]
  simpa only [ofReal_norm] using (ENNReal.ofReal_tsum_of_nonneg (fun x => norm_nonneg _) h).symm

private theorem lintegral_enorm_sq_le {E : Type*} [NormedAddCommGroup E] (g : ℤ → E) {C M : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ x : ℤ, ‖g x‖ ≤ C) (hsum : Summable (fun x : ℤ => ‖g x‖))
    (hM : ∑' x : ℤ, ‖g x‖ ≤ M) :
    ∫⁻ x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      ≤ ENNReal.ofReal (C * M) := by
  rw [MeasureTheory.lintegral_count]
  have hpt : ∀ x, ‖g x‖ₑ ^ (2:ℝ) ≤ ENNReal.ofReal C * ‖g x‖ₑ := by
    intro x
    rw [← ofReal_norm (g x), ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_ofNat, ← ENNReal.ofReal_mul hC0]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [norm_nonneg (g x), hC x]
  calc ∑' x : ℤ, ‖g x‖ₑ ^ (2:ℝ) ≤ ∑' x : ℤ, ENNReal.ofReal C * ‖g x‖ₑ := ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal C * ∑' x : ℤ, ‖g x‖ₑ := ENNReal.tsum_mul_left
    _ = ENNReal.ofReal C * ENNReal.ofReal (∑' x : ℤ, ‖g x‖) := by
          congr 1
          rw [ENNReal.ofReal_tsum_of_nonneg (fun x => norm_nonneg _) hsum]
          exact tsum_congr (fun x => (ofReal_norm (g x)).symm)
    _ = ENNReal.ofReal (C * ∑' x : ℤ, ‖g x‖) := (ENNReal.ofReal_mul hC0).symm
    _ ≤ ENNReal.ofReal (C * M) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hM hC0)

private lemma mem_finset_dIv (p : ℕ × ℤ) (x : ℤ) :
    x ∈ (Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2) : Set ℤ) ↔ x ∈ dIv p.1 p.2 := by
  rw [Finset.coe_Ico]; rfl

private lemma measurableSet_int (s : Set ℤ) : MeasurableSet s :=
  (Set.countable_univ.mono (Set.subset_univ s)).measurableSet

/-- **Discrete Calderón--Zygmund weak-type `(1,1)` bound on `ℤ`.**  Let `H` be a complex
Hilbert space, `K : ℤ → ℂ` a kernel satisfying the size bound `‖K z‖ ≤ Bk` and the Hörmander-type
condition `∑_{2|y| ≤ |x|} ‖K (x - y) - K x‖ ≤ Ak` for every `y ≠ 0`, and suppose that the
convolution operator `T f x = ∑'_y K (x - y) • f y` is bounded on `ℓ²(ℤ; H)` with constant `A2`.
Then `T` is of weak type `(1,1)`: for every summable `f : ℤ → H` and every `α > 0`,
`#{x : α < ‖T f x‖} ≤ (24 A2² + 4 Ak + 100) α⁻¹ ∑_x ‖f x‖`.
This is the discrete (counting-measure, `ℤ`) analogue of the Calderón--Zygmund theory already in
the commons for `ℝ` (`Commons.Analysis.CalderonZygmund.cz_weak_type_one_measurable_bounded`); the
proof proceeds by the Calderón--Zygmund decomposition of `f` into disjoint dyadic intervals of
`ℤ` with `α |I| ≤ ∑_{I} ‖f‖ ≤ 2 α |I|`, the `ℓ²` bound for the good part and the Hörmander
condition for the bad part. -/
theorem discrete_convolution_weak_type_one {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [CompleteSpace H] (K : ℤ → ℂ) (A2 Ak Bk : ℝ) (hA2 : 0 < A2) (hAk : 0 ≤ Ak)
    (hKbdd : ∀ z : ℤ, ‖K z‖ ≤ Bk)
    (hker : ∀ y : ℤ, y ≠ 0 →
      ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs}, ‖K (x - y) - K x‖ₑ ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal Ak)
    (hstrong : ∀ f : ℤ → H, Summable f →
      MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • f y) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal A2 * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
    (f : ℤ → H) (hf : Summable f) (α : ℝ) (hα : 0 < α) :
    MeasureTheory.Measure.count {x : ℤ | α < ‖∑' y : ℤ, K (x - y) • f y‖}
      ≤ ENNReal.ofReal ((24 * A2 ^ 2 + 4 * Ak + 100) / α)
          * MeasureTheory.eLpNorm f 1 MeasureTheory.Measure.count := by
  classical
  by_cases habs : Summable (fun x : ℤ => ‖f x‖)
  · set M : ℝ := ∑' x : ℤ, ‖f x‖ with hM
    have hMnn : 0 ≤ M := by rw [hM]; exact tsum_nonneg (fun x => norm_nonneg _)
    obtain ⟨S, g, b, hdisj, hlow, hhigh, hbin, hbout, hgout, hgin, hgood, hupper, hsumlen, hfinal⟩ :=
      calderon_zygmund_decomposition_int_finset f habs α hα
    have hszpos : ∀ p : ℕ × ℤ, 0 < (2:ℝ)^p.1 := fun p => by positivity
    have hszne : ∀ p : ℕ × ℤ, (2:ℝ)^p.1 ≠ 0 := fun p => ne_of_gt (hszpos p)
    let mass : ℕ × ℤ → ℝ := fun p => ∑ y ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), ‖f y‖
    have hb_abs : ∀ p ∈ S, Summable (fun x : ℤ => ‖b p x‖) := by
      intro p hp
      refine summable_of_ne_finset_zero (s := Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2)) (fun x hx => ?_)
      have hout : x ∉ dIv p.1 p.2 := fun hmem => hx ((mem_finset_dIv p x).mpr hmem)
      rw [hbout p hp x hout, norm_zero]
    have hbSsum : Summable (fun y : ℤ => ∑ p ∈ S, ‖b p y‖) :=
      summable_finset_sum_int S (fun p y => ‖b p y‖) hb_abs
    have hbT_sum : Summable (fun y : ℤ => ‖∑ p ∈ S, b p y‖) :=
      Summable.of_nonneg_of_le (fun y => norm_nonneg _) (fun y => norm_sum_le _ _) hbSsum
    have hb_sum : ∀ p ∈ S, Summable (b p) := fun p hp => Summable.of_norm (hb_abs p hp)
    have hb_L1 : ∀ p ∈ S, ∑' y : ℤ, ‖b p y‖ ≤ 2 * mass p := by
      intro p hp
      have hsupp : ∀ y : ℤ, y ∉ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2) → ‖b p y‖ = 0 := by
        intro y hy
        rw [hbout p hp y (fun hmem => hy ((mem_finset_dIv p y).mpr hmem)), norm_zero]
      rw [tsum_eq_sum hsupp]
      have hpt : ∀ y ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2),
          ‖b p y‖ ≤ ‖f y‖ + ‖((2:ℝ)^p.1)⁻¹ • (∑ t ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), f t)‖ := by
        intro y hy
        rw [hbin p hp y ((mem_finset_dIv p y).mp hy)]
        exact norm_sub_le _ _
      refine le_trans (Finset.sum_le_sum hpt) ?_
      have hcard : (Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2)).card = 2^p.1 := by
        rw [Int.card_Ico, dhi_sub_dlo]; exact Int.toNat_natCast _
      have hconst : ∑ _y ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2),
            ‖((2:ℝ)^p.1)⁻¹ • (∑ t ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), f t)‖
          = ‖∑ t ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), f t‖ := by
        rw [Finset.sum_const, hcard, nsmul_eq_mul]
        rw [show (((2^p.1 : ℕ) : ℝ)) = (2:ℝ)^p.1 by push_cast; ring]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hszpos p)),
          mul_inv_cancel_left₀ (hszne p)]
      rw [Finset.sum_add_distrib, hconst]
      have hnorm : ‖∑ t ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), f t‖ ≤ mass p := norm_sum_le _ _
      linarith
    have hmass_sum : ∑ p ∈ S, mass p ≤ M := by
      have hpair : (↑S : Set (ℕ × ℤ)).PairwiseDisjoint
          (fun p => Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2)) := by
        intro p hp q hq hpq
        exact Finset.disjoint_coe.mp (by
          rw [Finset.coe_Ico, Finset.coe_Ico]
          exact hdisj p hp q hq hpq)
      have hbu := Finset.sum_biUnion (s := S)
        (t := fun p => Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2)) (f := fun x => ‖f x‖) hpair
      change ∑ p ∈ S, ∑ y ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), ‖f y‖ ≤ M
      rw [← hbu]
      exact Summable.sum_le_tsum _ (fun x _ => norm_nonneg _) habs
    have hbsum : ∑ p ∈ S, ∑' y : ℤ, ‖b p y‖ ≤ 2 * M := by
      refine le_trans (Finset.sum_le_sum hb_L1) ?_
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left hmass_sum (by norm_num)
    have hgx_le : ∀ x : ℤ, ‖g x‖ ≤ ‖f x‖ + ∑ p ∈ S, ‖b p x‖ := by
      intro x
      have h1 : g x = f x - ∑ p ∈ S, b p x := by rw [hfinal x]; abel
      calc ‖g x‖ = ‖f x - ∑ p ∈ S, b p x‖ := by rw [h1]
        _ ≤ ‖f x‖ + ‖∑ p ∈ S, b p x‖ := norm_sub_le _ _
        _ ≤ ‖f x‖ + ∑ p ∈ S, ‖b p x‖ := by gcongr; exact norm_sum_le _ _
    have hg_abs : Summable (fun x : ℤ => ‖g x‖) :=
      Summable.of_nonneg_of_le (fun x => norm_nonneg _) hgx_le (habs.add hbSsum)
    have hg_bound : ∑' x : ℤ, ‖g x‖ ≤ 3 * M := by
      have h1 : ∑' x : ℤ, ‖g x‖ ≤ ∑' x : ℤ, (‖f x‖ + ∑ p ∈ S, ‖b p x‖) :=
        Summable.tsum_le_tsum hgx_le hg_abs (habs.add hbSsum)
      rw [Summable.tsum_add habs hbSsum,
        tsum_finset_sum_int S (fun p x => ‖b p x‖) hb_abs] at h1
      refine le_trans h1 ?_
      rw [hM]
      have h3 : ∑ p ∈ S, ∑' x : ℤ, ‖b p x‖ ≤ 2 * ∑ p ∈ S, mass p := by
        rw [Finset.mul_sum]; exact Finset.sum_le_sum hb_L1
      linarith [hmass_sum]
    have hg_sum : Summable g := Summable.of_norm hg_abs
    have hpoint : ∀ x : ℤ, (∑' y : ℤ, K (x - y) • f y)
        = (∑' y : ℤ, K (x - y) • g y) + ∑ p ∈ S, (∑' y : ℤ, K (x - y) • b p y) := by
      intro x
      have hg' : Summable (fun y : ℤ => K (x - y) • g y) := summable_smul_sub_int K hKbdd hg_abs x
      have hbT' : Summable (fun y : ℤ => K (x - y) • (∑ p ∈ S, b p y)) :=
        summable_smul_sub_int K hKbdd hbT_sum x
      have hbp : ∀ p ∈ S, Summable (fun y : ℤ => K (x - y) • b p y) :=
        fun p hp => summable_smul_sub_int K hKbdd (hb_abs p hp) x
      calc (∑' y : ℤ, K (x - y) • f y)
          = ∑' y : ℤ, K (x - y) • (g y + ∑ p ∈ S, b p y) := by
              apply tsum_congr; intro y; rw [hfinal y]
        _ = ∑' y : ℤ, (K (x - y) • g y + K (x - y) • (∑ p ∈ S, b p y)) := by
              apply tsum_congr; intro y; rw [smul_add]
        _ = (∑' y : ℤ, K (x - y) • g y) + ∑' y : ℤ, K (x - y) • (∑ p ∈ S, b p y) :=
              Summable.tsum_add hg' hbT'
        _ = (∑' y : ℤ, K (x - y) • g y) + ∑' y : ℤ, ∑ p ∈ S, K (x - y) • b p y := by
              congr 1; apply tsum_congr; intro y; rw [Finset.smul_sum]
        _ = (∑' y : ℤ, K (x - y) • g y) + ∑ p ∈ S, ∑' y : ℤ, K (x - y) • b p y := by
              congr 1
              exact tsum_finset_sum_int S (fun p y => K (x - y) • b p y) hbp
    have hwmean : ∀ p ∈ S, ∑ x ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), b p x = 0 := by
      intro p hp
      have hstep : ∀ x ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2),
          b p x = f x - ((2:ℝ)^p.1)⁻¹ • (∑ y ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), f y) :=
        fun x hx => hbin p hp x ((mem_finset_dIv p x).mp hx)
      rw [Finset.sum_congr rfl hstep, Finset.sum_sub_distrib]
      have hcard : (Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2)).card = 2^p.1 := by
        rw [Int.card_Ico, dhi_sub_dlo]; exact Int.toNat_natCast _
      have hconst : ∑ _x ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2),
          ((2:ℝ)^p.1)⁻¹ • (∑ y ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), f y)
          = ∑ y ∈ Finset.Ico (dlo p.1 p.2) (dhi p.1 p.2), f y := by
        rw [Finset.sum_const, hcard, ← Nat.cast_smul_eq_nsmul ℝ]
        rw [show (((2^p.1 : ℕ) : ℝ)) = (2:ℝ)^p.1 by push_cast; ring]
        exact smul_inv_smul₀ (hszne p) _
      rw [hconst, sub_self]
    have hgL2 : (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2:ℝ)
        ≤ ENNReal.ofReal (6 * α * M) := by
      rw [show (2:ℝ) = ((2:ℝ≥0∞)).toReal from (ENNReal.toReal_ofNat 2).symm,
        Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal (p := (2:ℝ≥0∞))
          (by norm_num) (by norm_num) g, ENNReal.toReal_ofNat 2]
      have h := lintegral_enorm_sq_le g (C := 2 * α) (M := 3 * M)
        (by positivity) (fun x => hupper x) hg_abs hg_bound
      rw [show (2 * α) * (3 * M) = 6 * α * M by ring] at h
      exact h
    have hTgL2 : (MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • g y) 2
        MeasureTheory.Measure.count) ^ (2:ℝ)
        ≤ ENNReal.ofReal (A2 ^ 2 * (6 * α * M)) := by
      have h1 : (MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • g y) 2
            MeasureTheory.Measure.count) ^ (2:ℝ)
          ≤ (ENNReal.ofReal A2 * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2:ℝ) :=
        ENNReal.rpow_le_rpow (hstrong g hg_sum) (by norm_num)
      calc (MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • g y) 2
            MeasureTheory.Measure.count) ^ (2:ℝ)
          ≤ (ENNReal.ofReal A2 * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2:ℝ) := h1
        _ = ENNReal.ofReal A2 ^ (2:ℝ)
              * (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2:ℝ) :=
              ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
        _ = ENNReal.ofReal (A2 ^ 2)
              * (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2:ℝ) := by
              rw [ENNReal.ofReal_rpow_of_nonneg hA2.le (by norm_num : (0:ℝ) ≤ 2), Real.rpow_ofNat]
        _ ≤ ENNReal.ofReal (A2 ^ 2) * ENNReal.ofReal (6 * α * M) := by gcongr
        _ = ENNReal.ofReal (A2 ^ 2 * (6 * α * M)) := (ENNReal.ofReal_mul (by positivity)).symm
    have hε0 : ENNReal.ofReal (α/2) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
    have hε2_0 : (ENNReal.ofReal (α/2)) ^ (2:ℝ) ≠ 0 := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by linarith : (0:ℝ) ≤ α/2) (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_ofNat]
      exact ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
    have hε2_top : (ENNReal.ofReal (α/2)) ^ (2:ℝ) ≠ ⊤ := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by linarith : (0:ℝ) ≤ α/2) (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_ofNat]
      exact ENNReal.ofReal_ne_top
    have hgood_part : MeasureTheory.Measure.count
        {x : ℤ | ENNReal.ofReal (α/2) < ‖∑' y : ℤ, K (x - y) • g y‖ₑ}
        ≤ ENNReal.ofReal (24 * A2 ^ 2 * M / α) := by
      have hkey := meas_ge_le_lintegral_div (μ := MeasureTheory.Measure.count)
        (f := fun x : ℤ => ‖∑' y : ℤ, K (x - y) • g y‖ₑ ^ (2:ℝ))
        (measurable_of_countable _).aemeasurable hε2_0 hε2_top
      have hsub : {x : ℤ | ENNReal.ofReal (α/2) < ‖∑' y : ℤ, K (x - y) • g y‖ₑ}
          ⊆ {x : ℤ | (ENNReal.ofReal (α/2)) ^ (2:ℝ)
              ≤ ‖∑' y : ℤ, K (x - y) • g y‖ₑ ^ (2:ℝ)} := by
        intro x hx
        simp only [Set.mem_ofPred_eq] at hx ⊢
        exact ENNReal.rpow_le_rpow (le_of_lt hx) (by norm_num)
      have hsq : (∫⁻ x : ℤ, ‖∑' y : ℤ, K (x - y) • g y‖ₑ ^ (2:ℝ)
            ∂MeasureTheory.Measure.count)
          = (MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • g y) 2
              MeasureTheory.Measure.count) ^ (2:ℝ) := by
        rw [show (2:ℝ) = ((2:ℝ≥0∞)).toReal from (ENNReal.toReal_ofNat 2).symm,
          Commons.Analysis.MeasureTheory.eLpNorm_rpow_toReal (p := (2:ℝ≥0∞))
            (by norm_num) (by norm_num) (fun x : ℤ => ∑' y : ℤ, K (x - y) • g y),
          ENNReal.toReal_ofNat 2]
      calc MeasureTheory.Measure.count
            {x : ℤ | ENNReal.ofReal (α/2) < ‖∑' y : ℤ, K (x - y) • g y‖ₑ}
          ≤ MeasureTheory.Measure.count
              {x : ℤ | (ENNReal.ofReal (α/2)) ^ (2:ℝ)
                ≤ ‖∑' y : ℤ, K (x - y) • g y‖ₑ ^ (2:ℝ)} := measure_mono hsub
        _ ≤ (∫⁻ x : ℤ, ‖∑' y : ℤ, K (x - y) • g y‖ₑ ^ (2:ℝ)
              ∂MeasureTheory.Measure.count) / (ENNReal.ofReal (α/2)) ^ (2:ℝ) := hkey
        _ = (MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, K (x - y) • g y) 2
              MeasureTheory.Measure.count) ^ (2:ℝ) / (ENNReal.ofReal (α/2)) ^ (2:ℝ) := by rw [hsq]
        _ ≤ ENNReal.ofReal (A2 ^ 2 * (6 * α * M)) / (ENNReal.ofReal (α/2)) ^ (2:ℝ) :=
              ENNReal.div_le_div_right hTgL2 _
        _ = ENNReal.ofReal (24 * A2 ^ 2 * M / α) := by
              rw [ENNReal.ofReal_rpow_of_nonneg (by linarith : (0:ℝ) ≤ α/2)
                  (by norm_num : (0:ℝ) ≤ 2), Real.rpow_ofNat,
                ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos (by positivity : (0:ℝ) < (α/2)^2),
                ← ENNReal.ofReal_mul (by positivity)]
              congr 1
              field_simp
              ring
    let Vp : ℕ × ℤ → Set ℤ := fun p => {x : ℤ | (x - dlo p.1 p.2).natAbs < 2 * 2^p.1}
    let V : Set ℤ := ⋃ p ∈ S, Vp p
    have hVmeas : MeasurableSet V := measurableSet_int V
    have hVbound : MeasureTheory.Measure.count V ≤ ENNReal.ofReal (4 * M / α) := by
      have hVeq : V = ⋃ p : ℕ × ℤ, (if p ∈ S then Vp p else ∅) := by
        change (⋃ p ∈ S, Vp p) = ⋃ p : ℕ × ℤ, (if p ∈ S then Vp p else ∅)
        ext x
        simp only [Set.mem_iUnion]
        constructor
        · rintro ⟨p, hp, hx⟩
          exact ⟨p, by rw [if_pos hp]; exact hx⟩
        · rintro ⟨p, hp⟩
          by_cases hps : p ∈ S
          · rw [if_pos hps] at hp
            exact ⟨p, hps, hp⟩
          · rw [if_neg hps] at hp
            exact absurd hp (by simp)
      have hstep1 : MeasureTheory.Measure.count (⋃ p : ℕ × ℤ, (if p ∈ S then Vp p else ∅))
          ≤ ∑ p ∈ S, MeasureTheory.Measure.count (Vp p) := by
        refine le_trans (measure_iUnion_le
          (fun p : ℕ × ℤ => if p ∈ S then Vp p else ∅)) ?_
        rw [tsum_eq_sum (s := S) (fun p hp => by rw [if_neg hp]; simp)]
        exact le_of_eq (Finset.sum_congr rfl (fun p hp => by rw [if_pos hp]))
      rw [hVeq]
      refine le_trans hstep1 ?_
      have hthis : ∀ p ∈ S,
          MeasureTheory.Measure.count (Vp p) ≤ ENNReal.ofReal (4 * (2:ℝ)^p.1) := by
        intro p hp
        have h := count_natAbs_lt_le (dlo p.1 p.2) (2 * 2^p.1)
        have hcast : (((2 * (2 * 2^p.1) : ℕ)) : ℝ≥0∞) ≤ ENNReal.ofReal (4 * (2:ℝ)^p.1) := by
          rw [show (2 * (2 * 2^p.1)) = 4 * 2^p.1 from by ring, ← ENNReal.ofReal_natCast]
          apply ENNReal.ofReal_le_ofReal
          exact le_of_eq (by push_cast; ring)
        exact h.trans hcast
      calc ∑ p ∈ S, MeasureTheory.Measure.count (Vp p)
          ≤ ∑ p ∈ S, ENNReal.ofReal (4 * (2:ℝ)^p.1) := Finset.sum_le_sum hthis
        _ = ENNReal.ofReal (∑ p ∈ S, 4 * (2:ℝ)^p.1) :=
              (ENNReal.ofReal_sum_of_nonneg (fun p _ => by positivity)).symm
        _ = ENNReal.ofReal (4 * ∑ p ∈ S, (2:ℝ)^p.1) := by rw [Finset.mul_sum]
        _ ≤ ENNReal.ofReal (4 * (α⁻¹ * M)) :=
              ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hsumlen (by norm_num))
        _ = ENNReal.ofReal (4 * M / α) := by congr 1; ring
    have hbL : ∑ p ∈ S, ∫⁻ y, ‖b p y‖ₑ ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (2 * M) := by
      have heq : ∀ p ∈ S, ∫⁻ y, ‖b p y‖ₑ ∂MeasureTheory.Measure.count
          = ENNReal.ofReal (∑' y : ℤ, ‖b p y‖) := by
        intro p hp
        rw [MeasureTheory.lintegral_count]
        rw [show (∑' y : ℤ, ‖b p y‖ₑ) = ∑' y : ℤ, ENNReal.ofReal ‖b p y‖ from
          tsum_congr (fun y => (ofReal_norm (b p y)).symm)]
        exact (ENNReal.ofReal_tsum_of_nonneg (fun y => norm_nonneg _) (hb_abs p hp)).symm
      calc ∑ p ∈ S, ∫⁻ y, ‖b p y‖ₑ ∂MeasureTheory.Measure.count
          = ∑ p ∈ S, ENNReal.ofReal (∑' y : ℤ, ‖b p y‖) := Finset.sum_congr rfl heq
        _ = ENNReal.ofReal (∑ p ∈ S, ∑' y : ℤ, ‖b p y‖) :=
              (ENNReal.ofReal_sum_of_nonneg (fun p _ => tsum_nonneg (fun y => norm_nonneg _))).symm
        _ ≤ ENNReal.ofReal (2 * M) := ENNReal.ofReal_le_ofReal hbsum
    have hbad_lin : ∫⁻ x in Vᶜ, (∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ)
        ∂MeasureTheory.Measure.count ≤ ENNReal.ofReal (2 * Ak * M) := by
      have hterm : ∀ p ∈ S, ∫⁻ x in Vᶜ, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ
          ∂MeasureTheory.Measure.count
            ≤ ENNReal.ofReal Ak * ∫⁻ y, ‖b p y‖ₑ ∂MeasureTheory.Measure.count := by
        intro p hp
        have hsub : Vᶜ ⊆ {x : ℤ | 2 * (dhi p.1 p.2 - dlo p.1 p.2).toNat
            ≤ (x - dlo p.1 p.2).natAbs} := by
          intro x hx
          have hx' : x ∉ Vp p := fun hmem => hx (by
            change x ∈ ⋃ p ∈ S, Vp p
            exact Set.mem_iUnion.mpr ⟨p, Set.mem_iUnion.mpr ⟨hp, hmem⟩⟩)
          change 2 * (dhi p.1 p.2 - dlo p.1 p.2).toNat ≤ (x - dlo p.1 p.2).natAbs
          rw [show (dhi p.1 p.2 - dlo p.1 p.2).toNat = 2^p.1 from by
            rw [dhi_sub_dlo]; exact Int.toNat_natCast _]
          exact Nat.le_of_not_lt hx'
        calc ∫⁻ x in Vᶜ, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ ∂MeasureTheory.Measure.count
            ≤ ∫⁻ x in {x : ℤ | 2 * (dhi p.1 p.2 - dlo p.1 p.2).toNat
                ≤ (x - dlo p.1 p.2).natAbs},
                ‖∑' y : ℤ, K (x - y) • b p y‖ₑ ∂MeasureTheory.Measure.count :=
              lintegral_mono_set hsub
          _ ≤ ENNReal.ofReal Ak * ∫⁻ y, ‖b p y‖ₑ ∂MeasureTheory.Measure.count :=
              cz_bad_part_int_lintegral K Ak hAk hker (dlo p.1 p.2) (dhi p.1 p.2) (dlo p.1 p.2)
                (le_of_lt (dlo_lt_dhi p.1 p.2)) le_rfl (dlo_lt_dhi p.1 p.2)
                (b p) (hb_sum p hp) (fun x hx => hbout p hp x hx) (hwmean p hp)
      rw [show (∫⁻ x in Vᶜ, ∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ
            ∂MeasureTheory.Measure.count)
          = ∑ p ∈ S, ∫⁻ x in Vᶜ, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ
              ∂MeasureTheory.Measure.count from
        lintegral_finsetSum S (f := fun p x => ‖∑' y : ℤ, K (x - y) • b p y‖ₑ)
          (fun p _ => measurable_of_countable _)]
      calc ∑ p ∈ S, ∫⁻ x in Vᶜ, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ
              ∂MeasureTheory.Measure.count
          ≤ ∑ p ∈ S, ENNReal.ofReal Ak * ∫⁻ y, ‖b p y‖ₑ ∂MeasureTheory.Measure.count :=
            Finset.sum_le_sum hterm
        _ = ENNReal.ofReal Ak * ∑ p ∈ S, ∫⁻ y, ‖b p y‖ₑ ∂MeasureTheory.Measure.count := by
            rw [Finset.mul_sum]
        _ ≤ ENNReal.ofReal Ak * ENNReal.ofReal (2 * M) := by gcongr
        _ = ENNReal.ofReal (2 * Ak * M) := by
            rw [← ENNReal.ofReal_mul hAk]; congr 1; ring
    have hbad_part : MeasureTheory.Measure.count
        {x : ℤ | x ∉ V ∧ ENNReal.ofReal (α/2) < ∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ}
        ≤ ENNReal.ofReal (4 * Ak * M / α) := by
      set Bf : ℤ → ℝ≥0∞ := Vᶜ.indicator (fun x => ∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ) with hBf
      have hBf_meas : AEMeasurable Bf MeasureTheory.Measure.count :=
        AEMeasurable.indicator
          (measurable_of_countable (fun x => ∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ)).aemeasurable
          hVmeas.compl
      have hkey := meas_ge_le_lintegral_div hBf_meas hε0 ENNReal.ofReal_ne_top
      have hset : {x : ℤ | x ∉ V ∧ ENNReal.ofReal (α/2) < ∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ}
          ⊆ {x : ℤ | ENNReal.ofReal (α/2) ≤ Bf x} := by
        intro x hx
        simp only [Set.mem_ofPred_eq]
        rw [show Bf x = ∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ from by
          rw [hBf, Set.indicator_of_mem (by simpa using hx.1)]]
        exact le_of_lt hx.2
      have hlint : ∫⁻ x, Bf x ∂MeasureTheory.Measure.count
          = ∫⁻ x in Vᶜ, ∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ
              ∂MeasureTheory.Measure.count := by
        rw [hBf, MeasureTheory.lintegral_indicator hVmeas.compl]
      calc MeasureTheory.Measure.count
            {x : ℤ | x ∉ V ∧ ENNReal.ofReal (α/2) < ∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ}
          ≤ MeasureTheory.Measure.count {x : ℤ | ENNReal.ofReal (α/2) ≤ Bf x} := measure_mono hset
        _ ≤ (∫⁻ x, Bf x ∂MeasureTheory.Measure.count) / ENNReal.ofReal (α/2) := hkey
        _ = (∫⁻ x in Vᶜ, ∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ
              ∂MeasureTheory.Measure.count) / ENNReal.ofReal (α/2) := by rw [hlint]
        _ ≤ ENNReal.ofReal (2 * Ak * M) / ENNReal.ofReal (α/2) :=
            ENNReal.div_le_div_right hbad_lin _
        _ = ENNReal.ofReal (4 * Ak * M / α) := by
            rw [← ENNReal.ofReal_div_of_pos (by linarith : (0:ℝ) < α/2)]
            congr 1
            field_simp
            ring
    have hsubset : {x : ℤ | α < ‖∑' y : ℤ, K (x - y) • f y‖} ⊆ V ∪
        ({x : ℤ | ENNReal.ofReal (α/2) < ‖∑' y : ℤ, K (x - y) • g y‖ₑ} ∪
         {x : ℤ | x ∉ V ∧ ENNReal.ofReal (α/2) < ∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ}) := by
      intro x hx
      by_cases hxV : x ∈ V
      · exact Or.inl hxV
      · refine Or.inr ?_
        by_cases hg : ENNReal.ofReal (α/2) < ‖∑' y : ℤ, K (x - y) • g y‖ₑ
        · exact Or.inl hg
        · refine Or.inr ⟨hxV, ?_⟩
          by_contra hc
          push Not at hg hc
          have hxα : ENNReal.ofReal α < ‖∑' y : ℤ, K (x - y) • f y‖ₑ := by
            rw [← ofReal_norm]
            exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα.le).mpr hx
          rw [hpoint x] at hxα
          have h2 : ‖(∑' y : ℤ, K (x - y) • g y) + ∑ p ∈ S, (∑' y : ℤ, K (x - y) • b p y)‖ₑ
              ≤ ‖∑' y : ℤ, K (x - y) • g y‖ₑ
                + ∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ :=
            (enorm_add_le _ _).trans (add_le_add le_rfl (enorm_sum_le _ _))
          have h4 : ENNReal.ofReal (α/2) + ENNReal.ofReal (α/2) = ENNReal.ofReal α := by
            rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; congr 1; ring
          have h3 : ‖∑' y : ℤ, K (x - y) • g y‖ₑ
                + ∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ ≤ ENNReal.ofReal α := by
            rw [← h4]; exact add_le_add hg hc
          exact absurd (hxα.trans_le (h2.trans h3)) (lt_irrefl _)
    calc MeasureTheory.Measure.count {x : ℤ | α < ‖∑' y : ℤ, K (x - y) • f y‖}
        ≤ MeasureTheory.Measure.count (V ∪
            ({x : ℤ | ENNReal.ofReal (α/2) < ‖∑' y : ℤ, K (x - y) • g y‖ₑ} ∪
             {x : ℤ | x ∉ V ∧ ENNReal.ofReal (α/2) < ∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ})) :=
            measure_mono hsubset
      _ ≤ MeasureTheory.Measure.count V + MeasureTheory.Measure.count
            ({x : ℤ | ENNReal.ofReal (α/2) < ‖∑' y : ℤ, K (x - y) • g y‖ₑ} ∪
             {x : ℤ | x ∉ V ∧ ENNReal.ofReal (α/2) < ∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ}) :=
            measure_union_le _ _
      _ ≤ MeasureTheory.Measure.count V
            + (MeasureTheory.Measure.count {x : ℤ | ENNReal.ofReal (α/2) < ‖∑' y : ℤ, K (x - y) • g y‖ₑ}
              + MeasureTheory.Measure.count
                {x : ℤ | x ∉ V ∧ ENNReal.ofReal (α/2) < ∑ p ∈ S, ‖∑' y : ℤ, K (x - y) • b p y‖ₑ}) :=
            add_le_add le_rfl (measure_union_le _ _)
      _ ≤ ENNReal.ofReal (4 * M / α)
            + (ENNReal.ofReal (24 * A2 ^ 2 * M / α) + ENNReal.ofReal (4 * Ak * M / α)) :=
            add_le_add hVbound (add_le_add hgood_part hbad_part)
      _ = ENNReal.ofReal ((4 * M + 24 * A2 ^ 2 * M + 4 * Ak * M) / α) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity),
              ← ENNReal.ofReal_add (by positivity) (by positivity)]
            congr 1; ring
      _ ≤ ENNReal.ofReal (((24 * A2 ^ 2 + 4 * Ak + 100) * M) / α) := by
            apply ENNReal.ofReal_le_ofReal
            rw [div_le_div_iff_of_pos_right hα]
            nlinarith [hMnn, hAk, sq_nonneg A2, hA2.le]
      _ = ENNReal.ofReal ((24 * A2 ^ 2 + 4 * Ak + 100) / α) * ENNReal.ofReal M := by
            rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
      _ = ENNReal.ofReal ((24 * A2 ^ 2 + 4 * Ak + 100) / α)
            * MeasureTheory.eLpNorm f 1 MeasureTheory.Measure.count := by
            rw [eLpNorm_one_count_eq f habs]
  · have he : MeasureTheory.eLpNorm f 1 MeasureTheory.Measure.count = ⊤ := by
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hf := by pw_aesm), MeasureTheory.lintegral_count]
      exact enorm_tsum_eq_top_of_not_summable f habs
    have hcoef : ENNReal.ofReal ((24 * A2 ^ 2 + 4 * Ak + 100) / α) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; positivity
    rw [he, ENNReal.mul_top hcoef]
    exact le_top

end

end Commons.Analysis.DiscreteCZ