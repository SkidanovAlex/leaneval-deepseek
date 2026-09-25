import Mathlib
import Submission.Commons.Analysis.Fourier.nested_scales_maximal_l2_real
import Submission.Commons.Analysis.Fourier.block_dual_recombination
import Submission.Commons.Analysis.Fourier.block_maximal_of_separated
import Submission.Commons.Analysis.Fourier.bandOp_maximal_l2_of_dual
import Submission.Commons.Analysis.Fourier.iterated_integral_eq_bandOp
import Submission.Commons.Analysis.Fourier.bandSum_indicatorSum_l2
import Submission.Commons.Analysis.Fourier.boundary_layer_l2
import Submission.Commons.Analysis.Fourier.bandOp_sq_integral_le
import Submission.Commons.Analysis.Fourier.lintegral_bandOp_sum_eq_indicator_sum
import Submission.Commons.Analysis.Fourier.linearization_bound_dual
import Submission.Commons.Analysis.Fourier.bandOp_dual_of_maximal
import Submission.Commons.Analysis.Fourier.fourier_eq_zero_of_not_integrable
import Submission.Commons.Analysis.Fourier.lintegral_iSup_finset_enorm_eq_ofReal
import Submission.Commons.Analysis.Fourier.memLp_itKer_shift
import Submission.Commons.Analysis.Fourier.lintegral_itKer_sq_le

set_option maxHeartbeats 4000000

namespace Commons.Analysis.Fourier

open MeasureTheory Finset Filter
open scoped BigOperators ENNReal FourierTransform Topology

/-!
# Combinatorial infrastructure for `neighborhood_maximal_arbitrary_of_separated`

This file contains (i) the elementary combinatorics of the *bad scales* of Bourgain's `Z_r`
reduction for the neighbourhood maximal function — the definitions `dyadic`, `badScale`, `neigh`,
`IsRep`, `coarse` and the facts

* transitivity of the class relation at a non-bad scale,
* containment of the target neighbourhoods in the "coarse" set (balls of twice the dyadic radius
  around the class representatives),
* one-step nesting of the coarse family,
* pairwise disjointness of the boundary layers `coarse j \ neigh j`,

and (ii) the requested theorem `neighborhood_maximal_arbitrary_of_separated`.  The theorem itself
is the `Z_r` reduction (Bourgain 1989, Lemma 4.11 from Lemma 4.26); see
`Submission/Work/Analysis/Fourier/neighborhood_maximal_STATUS.md` for the precise state of the
proof and the one remaining gap (the recombination of the blocks, which needs the dual
square-function form of the estimate).
-/

noncomputable section

/-- The dyadic scale `h j = 2^{-(j:ℝ)-1}`. -/
def dyadic (j : ℕ) : ℝ := (2:ℝ) ^ (-(j:ℝ) - 1)

lemma dyadic_pos (j : ℕ) : 0 < dyadic j := Real.rpow_pos_of_pos (by norm_num) _

lemma dyadic_anti {j j' : ℕ} (h : j ≤ j') : dyadic j' ≤ dyadic j := by
  unfold dyadic
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
  have : (j:ℝ) ≤ (j':ℝ) := by exact_mod_cast h
  linarith

lemma dyadic_succ (j : ℕ) : dyadic (j+1) * 2 = dyadic j := by
  unfold dyadic
  have he : -(((j+1:ℕ):ℝ)) - 1 = (-(j:ℝ) - 1) + (-1:ℝ) := by push_cast; ring
  rw [he, Real.rpow_add (by norm_num : (0:ℝ) < 2),
    show (-(1:ℝ)) = (-1:ℝ) by norm_num, Real.rpow_neg_one]
  field_simp

lemma two_dyadic_succ (j : ℕ) : 2 * dyadic (j+1) = dyadic j := by
  have := dyadic_succ j; linarith

/-- A scale `j` is *bad* if some pair of frequencies has distance comparable to `h j`. -/
def badScale {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) : Prop :=
  ∃ i l : Fin K, i ≠ l ∧ dyadic j < |lam i - lam l| ∧ |lam i - lam l| ≤ (K:ℝ) * dyadic j

/-- The `h j`-neighbourhood of the frequency set. -/
def neigh {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) : Set ℝ :=
  {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ dyadic j}

/-- Index `i` is the representative of its class at scale `j` (no smaller index in its class). -/
def IsRep {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) (i : Fin K) : Prop :=
  ∀ l : Fin K, l < i → ¬ (|lam i - lam l| ≤ dyadic j)

/-- The *coarse* set: balls of twice the dyadic radius around the class representatives. -/
def coarse {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) : Set ℝ :=
  {θ : ℝ | ∃ i : Fin K, IsRep lam j i ∧ |θ - lam i| ≤ 2 * dyadic j}

/-- **Transitivity of the class relation at a non-bad scale.** -/
lemma abs_le_trans {K : ℕ} {lam : Fin K → ℝ} {j : ℕ} (hbad : ¬ badScale lam j)
    {i l m : Fin K} (h1 : |lam i - lam l| ≤ dyadic j) (h2 : |lam l - lam m| ≤ dyadic j) :
    |lam i - lam m| ≤ dyadic j := by
  by_cases him : i = m
  · rw [him, sub_self, abs_zero]; exact le_of_lt (dyadic_pos j)
  · have h3 : |lam i - lam m| ≤ dyadic j + dyadic j := by
      calc |lam i - lam m| ≤ |lam i - lam l| + |lam l - lam m| := abs_sub_le _ _ _
        _ ≤ dyadic j + dyadic j := by linarith
    by_contra hcon
    push Not at hcon
    have hgt : (K:ℝ) * dyadic j < |lam i - lam m| := by
      by_contra hc
      push Not at hc
      exact hbad ⟨i, m, him, hcon, hc⟩
    have hK2 : (K:ℝ) < 2 := by nlinarith [dyadic_pos j]
    have hK1 : K ≤ 1 := by
      have h2 : K < 2 := by exact_mod_cast hK2
      omega
    have hval : i.val = m.val := by have := i.isLt; have := m.isLt; omega
    exact him (Fin.ext hval)

/-- **The target set is contained in the coarse set** at a non-bad scale. -/
lemma neigh_subset_coarse {K : ℕ} {lam : Fin K → ℝ} {j : ℕ} (hbad : ¬ badScale lam j) :
    neigh lam j ⊆ coarse lam j := by
  intro θ hθ
  classical
  rcases hθ with ⟨k, hk⟩
  have hex : ∃ i : Fin K, |lam i - lam k| ≤ dyadic j ∧ IsRep lam j i := by
    set S : Finset (Fin K) := Finset.univ.filter (fun i => |lam i - lam k| ≤ dyadic j) with hS
    have hne : S.Nonempty := ⟨k, by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and, sub_self, abs_zero]
      exact le_of_lt (dyadic_pos j)⟩
    have hmem : S.min' hne ∈ S := Finset.min'_mem S hne
    have hminclass : |lam (S.min' hne) - lam k| ≤ dyadic j := by simpa [hS] using hmem
    refine ⟨S.min' hne, hminclass, ?_⟩
    intro l hl hcon
    have hlS : l ∈ S := by
      simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
      exact abs_le_trans hbad (by rwa [abs_sub_comm] at hcon) hminclass
    have := S.min'_le l hlS
    omega
  obtain ⟨i, hik, hrep⟩ := hex
  refine ⟨i, hrep, ?_⟩
  calc |θ - lam i| ≤ |θ - lam k| + |lam k - lam i| := abs_sub_le _ _ _
    _ ≤ dyadic j + dyadic j := by rw [abs_sub_comm (lam k) (lam i)]; linarith
    _ = 2 * dyadic j := by ring

/-- **The coarse set at the next scale is contained in the target set.** -/
lemma coarse_succ_subset_neigh {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) :
    coarse lam (j+1) ⊆ neigh lam j := by
  intro θ hθ
  rcases hθ with ⟨i, -, hi⟩
  refine ⟨i, ?_⟩
  rw [← two_dyadic_succ j]
  linarith

/-- **Nesting of the coarse family** at consecutive non-bad scales. -/
lemma coarse_succ_subset_coarse {K : ℕ} {lam : Fin K → ℝ} {j : ℕ} (hbad : ¬ badScale lam j) :
    coarse lam (j+1) ⊆ coarse lam j := by
  intro θ hθ
  classical
  rcases hθ with ⟨i, hrep, hi⟩
  by_cases hrep' : IsRep lam j i
  · refine ⟨i, hrep', ?_⟩
    have h2 := two_dyadic_succ j
    have hp := dyadic_pos j
    linarith
  · simp only [IsRep] at hrep'
    push Not at hrep'
    obtain ⟨l, hl, hlclass⟩ := hrep'
    set S : Finset (Fin K) := Finset.univ.filter (fun m => |lam m - lam i| ≤ dyadic j) with hS
    have hne : S.Nonempty := ⟨l, by simp [hS, abs_sub_comm, hlclass]⟩
    have hmem : S.min' hne ∈ S := Finset.min'_mem S hne
    have hminclass : |lam (S.min' hne) - lam i| ≤ dyadic j := by simpa [hS] using hmem
    have hminrep : IsRep lam j (S.min' hne) := by
      intro m hm hcon
      have hmS : m ∈ S := by
        simp only [hS, Finset.mem_filter, Finset.mem_univ, true_and]
        exact abs_le_trans hbad (by rwa [abs_sub_comm] at hcon) hminclass
      have := S.min'_le m hmS
      omega
    refine ⟨S.min' hne, hminrep, ?_⟩
    have hstep : |θ - lam (S.min' hne)| ≤ 2 * dyadic (j+1) + dyadic j := by
      calc |θ - lam (S.min' hne)| ≤ |θ - lam i| + |lam i - lam (S.min' hne)| := abs_sub_le _ _ _
        _ ≤ 2 * dyadic (j+1) + dyadic j := by
            rw [abs_sub_comm (lam i) (lam (S.min' hne))]; linarith
    have h2 := two_dyadic_succ j
    have hp := dyadic_pos j
    linarith

/-- **Pairwise disjointness of the boundary layers** `coarse j \ neigh j`. -/
lemma disjoint_boundary {K : ℕ} {lam : Fin K → ℝ} {j j' : ℕ} (hlt : j < j') :
    Disjoint (coarse lam j \ neigh lam j) (coarse lam j' \ neigh lam j') := by
  obtain ⟨j'', rfl⟩ : ∃ j'', j' = j'' + 1 := ⟨j' - 1, by omega⟩
  rw [Set.disjoint_left]
  intro θ hθ hθ'
  have h1 : θ ∈ coarse lam (j''+1) := hθ'.1
  have h3 : θ ∉ neigh lam j := hθ.2
  have hsub : coarse lam (j''+1) ⊆ neigh lam j'' := coarse_succ_subset_neigh lam j''
  have hle : j ≤ j'' := by omega
  have hmono : neigh lam j'' ⊆ neigh lam j := by
    intro x hx
    rcases hx with ⟨k, hk⟩
    exact ⟨k, le_trans hk (dyadic_anti hle)⟩
  exact h3 (hmono (hsub h1))

/-- The set of bad scales below `N`. -/
noncomputable def badSet {K : ℕ} (lam : Fin K → ℝ) (N : ℕ) : Finset ℕ :=
  by classical exact (Finset.range N).filter (fun j : ℕ => badScale lam j)

lemma mem_badSet {K : ℕ} {lam : Fin K → ℝ} {N j : ℕ} :
    j ∈ badSet lam N ↔ j < N ∧ badScale lam j := by
  classical
  simp [badSet, Finset.mem_range]

/-- Iterated dilation of the dyadic scale: `h (a+m) * 2^m = h a`. -/
lemma dyadic_mul_pow {a m : ℕ} : dyadic (a + m) * (2:ℝ)^m = dyadic a := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h : a + (m+1) = (a+m) + 1 := by omega
      rw [h, pow_succ]
      calc dyadic (a+m+1) * ((2:ℝ)^m * 2) = dyadic (a+m+1) * 2 * (2:ℝ)^m := by ring
        _ = dyadic (a+m) * (2:ℝ)^m := by rw [dyadic_succ]
        _ = dyadic a := ih

/-- **Window bound.**  For `K ≥ 1` the scales with `d/K ≤ h j < d` form a set of at most
`log₂ K + 1` elements (they span a factor-`K` range of the geometric sequence `h j`). -/
lemma window_card {d : ℝ} {K : ℕ} (hK : 1 ≤ K) (S : Finset ℕ)
    (hS : ∀ j ∈ S, d / (K:ℝ) ≤ dyadic j ∧ dyadic j < d) :
    S.card ≤ Nat.log2 K + 1 := by
  rcases S.eq_empty_or_nonempty with h | hne
  · simp [h]
  by_cases hd : d ≤ 0
  · have hsub : S ⊆ (∅ : Finset ℕ) := fun j hj => by
      have h1 := (hS j hj).2
      have h2 := dyadic_pos j
      linarith
    have hcard : S.card ≤ 0 := by simpa using Finset.card_le_card hsub
    omega
  · push Not at hd
    have hjm : S.min' hne ∈ S := S.min'_mem hne
    have hjM : S.max' hne ∈ S := S.max'_mem hne
    have hle : S.min' hne ≤ S.max' hne := S.min'_le _ hjM
    have hspan : S.max' hne - S.min' hne ≤ Nat.log2 K := by
      by_contra hcon
      push Not at hcon
      have hKm : (0:ℝ) < (K:ℝ) := by exact_mod_cast (by omega : 0 < K)
      have h1 : dyadic (S.min' hne) < d := (hS _ hjm).2
      have h2 : d ≤ (K:ℝ) * dyadic (S.max' hne) := by
        have h := (hS _ hjM).1
        rw [div_le_iff₀ hKm] at h
        rwa [mul_comm] at h
      have h3 : dyadic (S.min' hne) < (K:ℝ) * dyadic (S.max' hne) := lt_of_lt_of_le h1 h2
      have hdy : dyadic (S.min' hne) =
          (2:ℝ)^(S.max' hne - S.min' hne) * dyadic (S.max' hne) := by
        have h := dyadic_mul_pow (a := S.min' hne) (m := S.max' hne - S.min' hne)
        rw [Nat.add_sub_cancel' hle] at h
        rw [← h, mul_comm]
      rw [hdy] at h3
      have h4 : (2:ℝ)^(S.max' hne - S.min' hne) < (K:ℝ) := by
        have hpos : 0 < dyadic (S.max' hne) := dyadic_pos _
        nlinarith [h3, hpos]
      have h5 : (K:ℝ) < (2:ℝ)^(Nat.log2 K + 1) := by
        have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) K
        rw [← Nat.log2_eq_log_two] at h
        exact_mod_cast h
      have h6 : (2:ℝ)^(Nat.log2 K + 1) ≤ (2:ℝ)^(S.max' hne - S.min' hne) := by
        apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
        omega
      linarith
    calc S.card ≤ (Finset.Icc (S.min' hne) (S.max' hne)).card :=
          Finset.card_le_card (fun j hj =>
            Finset.mem_Icc.mpr ⟨S.min'_le j hj, S.le_max' j hj⟩)
      _ = S.max' hne + 1 - S.min' hne := Nat.card_Icc _ _
      _ ≤ Nat.log2 K + 1 := by omega

/-- The `badScale` condition puts `h j` in the window `[d/K, d)` for a witnessing pair. -/
lemma badScale_window {K : ℕ} {lam : Fin K → ℝ} {j : ℕ} (h : badScale lam j) :
    ∃ i l : Fin K, i ≠ l ∧ |lam i - lam l| / (K:ℝ) ≤ dyadic j ∧ dyadic j < |lam i - lam l| := by
  obtain ⟨i, l, hil, h1, h2⟩ := h
  refine ⟨i, l, hil, ?_, h1⟩
  have hKpos : (0:ℝ) < (K:ℝ) := by
    by_contra hc
    push Not at hc
    have hK0 : (K:ℝ) = 0 := le_antisymm hc (by positivity)
    rw [hK0, zero_mul] at h2
    have := dyadic_pos j
    linarith
  rw [div_le_iff₀ hKpos, mul_comm]
  exact h2

/-- **Cardinality of the bad scale set.**  For a `K`-point frequency set, the scales at which some
pair distance is comparable to `h j` (within a factor `K`) number at most `K² (log₂ K + 1)`. -/
lemma bad_scale_card_le {K : ℕ} (lam : Fin K → ℝ) (N : ℕ) :
    (badSet lam N).card ≤ K * K * (Nat.log2 K + 1) := by
  classical
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    have hempty : badSet lam N = ∅ := by
      refine Finset.eq_empty_iff_forall_notMem.mpr (fun j hj => ?_)
      obtain ⟨-, i, l, -, -, -⟩ := mem_badSet.mp hj
      exact Fin.elim0 i
    rw [hempty]; simp
  have hcover : badSet lam N ⊆ (Finset.univ : Finset (Fin K × Fin K)).biUnion
      (fun p => (badSet lam N).filter (fun j => |lam p.1 - lam p.2| / (K:ℝ) ≤ dyadic j ∧
        dyadic j < |lam p.1 - lam p.2|)) := by
    intro j hj
    rw [Finset.mem_biUnion]
    obtain ⟨-, hbad⟩ := mem_badSet.mp hj
    obtain ⟨i, l, hil, h1, h2⟩ := badScale_window (K := K) (lam := lam) (j := j) hbad
    exact ⟨(i, l), Finset.mem_univ _, Finset.mem_filter.mpr ⟨hj, h1, h2⟩⟩
  calc (badSet lam N).card ≤ ((Finset.univ : Finset (Fin K × Fin K)).biUnion
        (fun p => (badSet lam N).filter (fun j => |lam p.1 - lam p.2| / (K:ℝ) ≤ dyadic j ∧
          dyadic j < |lam p.1 - lam p.2|))).card := Finset.card_le_card hcover
    _ ≤ ∑ p : Fin K × Fin K, ((badSet lam N).filter (fun j => |lam p.1 - lam p.2| / (K:ℝ) ≤ dyadic j ∧
          dyadic j < |lam p.1 - lam p.2|)).card := Finset.card_biUnion_le
    _ ≤ ∑ _p : Fin K × Fin K, (Nat.log2 K + 1) := by
        refine Finset.sum_le_sum (fun p _ => ?_)
        exact window_card hK _ (fun j hj => (Finset.mem_filter.mp hj).2)
    _ = K * K * (Nat.log2 K + 1) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
/-- The set of class representatives at scale `j`. -/
noncomputable def repSet {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) : Finset (Fin K) :=
  by classical exact Finset.univ.filter (fun i => IsRep lam j i)

lemma mem_repSet {K : ℕ} {lam : Fin K → ℝ} {j : ℕ} {i : Fin K} :
    i ∈ repSet lam j ↔ IsRep lam j i := by
  classical
  simp [repSet]

/-- The representative set grows with the scale (the cluster partition refines). -/
lemma repSet_mono {K : ℕ} {lam : Fin K → ℝ} {j j' : ℕ} (h : j ≤ j') :
    repSet lam j ⊆ repSet lam j' := by
  intro i hi
  rw [mem_repSet] at hi ⊢
  intro l hl hcon
  exact hi l hl (le_trans hcon (dyadic_anti h))

/-- Two distinct representatives are separated by more than `h j`. -/
lemma rep_sep {K : ℕ} {lam : Fin K → ℝ} {j : ℕ} {i l : Fin K}
    (hi : IsRep lam j i) (hl : IsRep lam j l) (hne : i ≠ l) : dyadic j < |lam i - lam l| := by
  rcases lt_trichotomy i.val l.val with h | h | h
  · have hlt : i < l := h
    have hh := hl i hlt
    push Not at hh
    rw [abs_sub_comm] at hh
    exact hh
  · exact absurd (Fin.ext h) hne
  · have hlt : l < i := h
    have hh := hi l hlt
    push Not at hh
    exact hh

/-- On a bad-free interval the coarse (representative-ball) sets are nested. -/
lemma coarse_anti_of_nonbad {K : ℕ} {lam : Fin K → ℝ} {a b : ℕ} (hab : a ≤ b)
    (h : ∀ j : ℕ, a ≤ j → j < b → ¬ badScale lam j) : coarse lam b ⊆ coarse lam a := by
  revert hab h
  induction b with
  | zero =>
      intro hab h
      obtain rfl : a = 0 := Nat.eq_zero_of_le_zero hab
      exact subset_rfl
  | succ b ih =>
      intro hab h
      rcases Nat.eq_or_lt_of_le hab with h_eq | h_lt
      · subst h_eq; exact subset_rfl
      · have hsub : coarse lam (b+1) ⊆ coarse lam b :=
          coarse_succ_subset_coarse (h b (by omega) (Nat.lt_succ_self b))
        exact subset_trans hsub
          (ih (by omega) (fun j hj hjb => h j hj (lt_trans hjb (Nat.lt_succ_self b))))
/-- The number of clusters at scale `j`, i.e. the number of representatives. -/
noncomputable def clusterCount {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) : ℕ := (repSet lam j).card

lemma clusterCount_mono {K : ℕ} {lam : Fin K → ℝ} {j j' : ℕ} (h : j ≤ j') :
    clusterCount lam j ≤ clusterCount lam j' :=
  Finset.card_le_card (repSet_mono h)

lemma clusterCount_le {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) : clusterCount lam j ≤ K := by
  have h := Finset.card_le_card (Finset.subset_univ (repSet lam j))
  simpa [clusterCount, Finset.card_univ, Fintype.card_fin] using h

/-- A new combinatorial block starts at scale `j` if `j` is a bad scale or the cluster count
changed from `j-1` to `j`. -/
noncomputable def IsCut {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) : Prop :=
  badScale lam j ∨ (0 < j ∧ clusterCount lam j ≠ clusterCount lam (j-1))

/-- The block index of the scale `j`: the number of cuts up to `j`. -/
noncomputable def blockIndex {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) : ℕ :=
  by classical exact ((Finset.range (j+1)).filter (fun j' => IsCut lam j')).card

lemma blockIndex_mono {K : ℕ} (lam : Fin K → ℝ) : Monotone (blockIndex lam) := by
  intro j j' hjj'
  classical
  simp only [blockIndex]
  refine Finset.card_le_card ?_
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
  exact ⟨by omega, hx.2⟩

lemma range_succ_eq {n : ℕ} : Finset.range (n+1) = insert n (Finset.range n) := by
  ext x
  simp only [Finset.mem_range, Finset.mem_insert]
  omega

/-- The block index increases by `1` at a cut. -/
lemma blockIndex_succ_of_cut {K : ℕ} {lam : Fin K → ℝ} {n : ℕ} (h : IsCut lam (n+1)) :
    blockIndex lam (n+1) = blockIndex lam n + 1 := by
  classical
  simp only [blockIndex]
  rw [show n + 1 + 1 = n + 2 from by omega, range_succ_eq, Finset.filter_insert, if_pos h]
  rw [Finset.card_insert_of_notMem (by simp [Finset.mem_filter, Finset.mem_range])]

/-- The block index is unchanged at a non-cut. -/
lemma blockIndex_succ_of_not_cut {K : ℕ} {lam : Fin K → ℝ} {n : ℕ} (h : ¬ IsCut lam (n+1)) :
    blockIndex lam (n+1) = blockIndex lam n := by
  classical
  simp only [blockIndex]
  rw [show n + 1 + 1 = n + 2 from by omega, range_succ_eq, Finset.filter_insert, if_neg h]

/-- A common block index at two consecutive scales means no cut at the second scale. -/
lemma not_isCut_of_blockIndex_eq {K : ℕ} {lam : Fin K → ℝ} {n : ℕ}
    (h : blockIndex lam n = blockIndex lam (n+1)) : ¬ IsCut lam (n+1) := by
  intro hc
  have hs := blockIndex_succ_of_cut (lam := lam) hc
  omega

lemma clusterCount_succ_of_blockIndex_eq {K : ℕ} {lam : Fin K → ℝ} {n : ℕ}
    (h : blockIndex lam n = blockIndex lam (n+1)) : clusterCount lam n = clusterCount lam (n+1) := by
  have hc := not_isCut_of_blockIndex_eq h
  rw [IsCut] at hc
  have hsub : n + 1 - 1 = n := by omega
  rw [hsub, not_or] at hc
  exact not_not.mp (fun hne => hc.2 ⟨Nat.succ_pos n, fun hh => hne hh.symm⟩)

lemma not_badScale_succ_of_blockIndex_eq {K : ℕ} {lam : Fin K → ℝ} {n : ℕ}
    (h : blockIndex lam n = blockIndex lam (n+1)) : ¬ badScale lam (n+1) := by
  intro hb
  exact not_isCut_of_blockIndex_eq h (Or.inl hb)

lemma clusterCount_eq_of_blockIndex_eq {K : ℕ} {lam : Fin K → ℝ} {j j' : ℕ} (h : j ≤ j')
    (hconst : blockIndex lam j = blockIndex lam j') :
    clusterCount lam j = clusterCount lam j' := by
  have hj' : j + (j' - j) = j' := Nat.add_sub_cancel' h
  rw [← hj'] at hconst ⊢
  suffices key : ∀ d : ℕ, (∀ n : ℕ, blockIndex lam n = blockIndex lam (n + d) →
      clusterCount lam n = clusterCount lam (n + d)) by
    exact key (j' - j) j hconst
  intro d
  induction d with
  | zero => intro n _; simp
  | succ d ih =>
      intro n hn
      have hn' : blockIndex lam n = blockIndex lam (n + d + 1) := by simpa only [Nat.add_succ] using hn
      have ha : blockIndex lam n ≤ blockIndex lam (n + d) := blockIndex_mono lam (by omega)
      have hb : blockIndex lam (n + d) ≤ blockIndex lam (n + d + 1) := blockIndex_mono lam (by omega)
      have h1 : blockIndex lam n = blockIndex lam (n + d) := by omega
      have h2 : blockIndex lam (n + d) = blockIndex lam (n + d + 1) := by omega
      have h3 : clusterCount lam n = clusterCount lam (n + d) := ih n h1
      have h4 : clusterCount lam (n + d) = clusterCount lam (n + d + 1) :=
        clusterCount_succ_of_blockIndex_eq h2
      show clusterCount lam n = clusterCount lam (n + d + 1)
      rw [h3, h4]

lemma repSet_eq_of_blockIndex_eq {K : ℕ} {lam : Fin K → ℝ} {j j' : ℕ} (h : j ≤ j')
    (hconst : blockIndex lam j = blockIndex lam j') : repSet lam j = repSet lam j' := by
  have hcard : clusterCount lam j = clusterCount lam j' := clusterCount_eq_of_blockIndex_eq h hconst
  exact Finset.eq_of_subset_of_card_le (repSet_mono h) (le_of_eq hcard.symm)
lemma clusterChange_card_le {K : ℕ} (lam : Fin K → ℝ) (N : ℕ) :
    ((Finset.range N).filter
      (fun j => 0 < j ∧ clusterCount lam j ≠ clusterCount lam (j-1))).card ≤ K := by
  classical
  set S : Finset ℕ := (Finset.range N).filter
      (fun j => 0 < j ∧ clusterCount lam j ≠ clusterCount lam (j-1)) with hS
  have hkey : ((S.card : ℤ)) ≤ (K : ℤ) := by
    have h1 : ((S.card : ℤ)) = ∑ j ∈ S, (1 : ℤ) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have h2 : ∑ j ∈ S, (1:ℤ)
        ≤ ∑ j ∈ S, ((clusterCount lam j : ℤ) - (clusterCount lam (j-1) : ℤ)) := by
      refine Finset.sum_le_sum (fun j hj => ?_)
      have hjS := Finset.mem_filter.mp hj
      have hmono : clusterCount lam (j-1) ≤ clusterCount lam j :=
        clusterCount_mono (lam := lam) (j := j-1) (j' := j) (by omega)
      have hne : clusterCount lam (j-1) ≠ clusterCount lam j := fun h => hjS.2.2 h.symm
      omega
    have h3 : ∑ j ∈ S, ((clusterCount lam j : ℤ) - (clusterCount lam (j-1) : ℤ))
        ≤ ∑ j ∈ Finset.Ico 1 N, ((clusterCount lam j : ℤ) - (clusterCount lam (j-1) : ℤ)) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ => ?_)
      · intro j hj
        have hjS := Finset.mem_filter.mp hj
        exact Finset.mem_Ico.mpr ⟨hjS.2.1, Finset.mem_range.mp hjS.1⟩
      · have hmono : clusterCount lam (i-1) ≤ clusterCount lam i := clusterCount_mono (by omega)
        omega
    have h4 : ∑ j ∈ Finset.Ico 1 N, ((clusterCount lam j : ℤ) - (clusterCount lam (j-1) : ℤ))
        = (clusterCount lam (N-1) : ℤ) - (clusterCount lam 0 : ℤ) := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN; simp
      · rw [Finset.sum_Ico_eq_sum_range]
        have hre : ∑ k ∈ Finset.range (N - 1),
              ((clusterCount lam (1 + k) : ℤ) - (clusterCount lam (1 + k - 1) : ℤ))
            = ∑ k ∈ Finset.range (N - 1),
              ((clusterCount lam (k + 1) : ℤ) - (clusterCount lam k : ℤ)) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Nat.add_comm 1 k, Nat.add_sub_cancel]
        rw [hre]
        simpa only using Finset.sum_range_sub (fun k : ℕ => (clusterCount lam k : ℤ)) (N - 1)
    have h5 : (clusterCount lam (N-1) : ℤ) - (clusterCount lam 0 : ℤ) ≤ (K : ℤ) := by
      have h1 : clusterCount lam (N-1) ≤ K := clusterCount_le lam (N-1)
      have h2 : 0 ≤ clusterCount lam 0 := Nat.zero_le _
      omega
    linarith
  omega


/-- **Number of blocks.**  The block index of a scale is bounded by the number of cuts up to it,
and there are at most `K² (log₂ K + 1) + K` cuts. -/
lemma blockIndex_le {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) :
    blockIndex lam j ≤ K * K * (Nat.log2 K + 1) + K := by
  classical
  set A : Finset ℕ := (Finset.range (j+1)).filter (fun j' => badScale lam j') with hA
  set B : Finset ℕ := (Finset.range (j+1)).filter
      (fun j' => 0 < j' ∧ clusterCount lam j' ≠ clusterCount lam (j'-1)) with hB
  have hsub : ((Finset.range (j+1)).filter (fun j' => IsCut lam j')) ⊆ A ∪ B := by
    intro x hx
    have hr : x ∈ Finset.range (j + 1) := (Finset.mem_filter.mp hx).1
    have hcut : IsCut lam x := (Finset.mem_filter.mp hx).2
    rcases hcut with hb | hc
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hr, hb⟩))
    · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hr, hc⟩))
  have hAub : (A ∪ B).card ≤ A.card + B.card := Finset.card_union_le A B
  have hAcard : A.card ≤ K * K * (Nat.log2 K + 1) := by
    rw [hA]
    simpa [badSet] using bad_scale_card_le lam (j+1)
  have hBcard : B.card ≤ K := by
    rw [hB]
    exact clusterChange_card_le lam (j+1)
  have hmain : blockIndex lam j ≤ A.card + B.card := by
    show ((Finset.range (j+1)).filter (fun j' => IsCut lam j')).card ≤ A.card + B.card
    exact le_trans (Finset.card_le_card hsub) hAub
  exact le_trans hmain (Nat.add_le_add hAcard hBcard)

/-- Inside a block no scale (other than possibly the first) is bad. -/
lemma not_badScale_of_lt_blockIndex_eq {K : ℕ} {lam : Fin K → ℝ} {a j : ℕ} (haj : a < j)
    (h : blockIndex lam a = blockIndex lam j) : ¬ badScale lam j := by
  have hj1 : 1 ≤ j := by omega
  have h1 : blockIndex lam (j-1) ≤ blockIndex lam j := blockIndex_mono lam (by omega)
  have h2 : blockIndex lam j ≤ blockIndex lam (j-1) := by
    rw [← h]; exact blockIndex_mono lam (by omega)
  have heq : blockIndex lam (j-1) = blockIndex lam ((j-1)+1) := by
    rw [Nat.sub_add_cancel hj1]
    exact le_antisymm h1 h2
  have := not_badScale_succ_of_blockIndex_eq (n := j-1) heq
  simpa only [Nat.sub_add_cancel hj1] using this

/-- The cluster count does not change inside a block. -/
lemma clusterCount_eq_pred_of_lt_blockIndex_eq {K : ℕ} {lam : Fin K → ℝ} {a j : ℕ} (haj : a < j)
    (h : blockIndex lam a = blockIndex lam j) : clusterCount lam (j-1) = clusterCount lam j := by
  have hj1 : 1 ≤ j := by omega
  have h1 : blockIndex lam (j-1) ≤ blockIndex lam j := blockIndex_mono lam (by omega)
  have h2 : blockIndex lam j ≤ blockIndex lam (j-1) := by
    rw [← h]; exact blockIndex_mono lam (by omega)
  have heq : blockIndex lam (j-1) = blockIndex lam ((j-1)+1) := by
    rw [Nat.sub_add_cancel hj1]
    exact le_antisymm h1 h2
  have := clusterCount_succ_of_blockIndex_eq heq
  simpa only [Nat.sub_add_cancel hj1] using this

/-- The kernel of the iterated-integral band operator: `itKer C t = ∫_θ 1_C(θ) e^{-itθ} dθ`. -/
noncomputable def itKer (C : Set ℝ) (t : ℝ) : ℂ :=
  ∫ θ : ℝ, Set.indicator C (fun θ : ℝ => Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ)))) θ

/-- The iterated-integral band operator of Bourgain's Lemma 4.11:
`itOp C f x = ∫ y, f y · ∫_θ 1_C(θ) e^{-i(x-y)θ} dθ`. -/
noncomputable def itOp (C : Set ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ, f y * itKer C (x - y)

lemma itKer_norm_le (C : Set ℝ) (hC : MeasurableSet C) (t : ℝ) :
    ‖itKer C t‖ ≤ (volume C).toReal := by
  have h1 : ∀ θ : ℝ,
      ‖Set.indicator C (fun θ : ℝ => Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ)))) θ‖
        = (C.indicator (fun _ => (1:ℝ))) θ := by
    intro θ
    by_cases h : θ ∈ C
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, BourgainBlock.norm_exp_neg_I_mul t θ]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; simp
  calc ‖itKer C t‖ ≤ ∫ θ, ‖Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ)))) θ‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ θ, (C.indicator (fun _ => (1:ℝ))) θ := integral_congr_ae (ae_of_all _ h1)
    _ = volume.real C := by rw [integral_indicator hC, setIntegral_const, smul_eq_mul, mul_one]
    _ = (volume C).toReal := measureReal_def _ _

/-- The elementary conjugation identity for the exponential of a pure imaginary argument. -/
lemma star_exp_neg_I (t θ : ℝ) :
    star (Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * ((θ : ℝ) : ℂ))))
      = Complex.exp (-(Complex.I * (((-t : ℝ)) : ℂ) * ((θ : ℝ) : ℂ))) := by
  have h1 : star (Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * ((θ : ℝ) : ℂ))))
      = Complex.exp (star (-(Complex.I * ((t : ℝ) : ℂ) * ((θ : ℝ) : ℂ)))) := by
    rw [show star (Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * ((θ : ℝ) : ℂ))))
        = (starRingEnd ℂ) (Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * ((θ : ℝ) : ℂ)))) from rfl,
      ← Complex.exp_conj]
    simp only [starRingEnd_apply]
  rw [h1]
  congr 1
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  have ht : star ((t : ℝ) : ℂ) = ((t : ℝ) : ℂ) := Complex.conj_ofReal t
  have hθ : star ((θ : ℝ) : ℂ) = ((θ : ℝ) : ℂ) := Complex.conj_ofReal θ
  rw [star_neg, star_mul', star_mul', hI, ht, hθ]
  push_cast
  ring

/-- `itKer C (-t) = conj (itKer C t)`: the kernel is hermitian because the symbol is real. -/
lemma itKer_neg (C : Set ℝ) (t : ℝ) : itKer C (-t) = star (itKer C t) := by
  have hpt : ∀ θ : ℝ, Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * (((-t : ℝ)) : ℂ) * (θ : ℂ)))) θ
      = star (Set.indicator C (fun θ : ℝ => Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ)))) θ) := by
    intro θ
    by_cases h : θ ∈ C
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, star_exp_neg_I]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, star_zero]
  have hswap : star (∫ θ : ℝ, Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ)))) θ)
      = ∫ θ : ℝ, star (Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ)))) θ) := by
    rw [show star (∫ θ : ℝ, Set.indicator C
          (fun θ : ℝ => Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ)))) θ)
        = (starRingEnd ℂ) (∫ θ : ℝ, Set.indicator C
          (fun θ : ℝ => Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ)))) θ) from rfl]
    exact (integral_conj (μ := (volume : Measure ℝ))).symm
  rw [itKer, itKer, show (fun θ : ℝ => Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * (((-t : ℝ)) : ℂ) * (θ : ℂ)))) θ)
      = fun θ => star (Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ)))) θ) from funext hpt,
    hswap]

lemma itOp_eq (C : Set ℝ) (f : ℝ → ℂ) (x : ℝ) :
    itOp C f x = ∫ y : ℝ, f y * (∫ θ : ℝ, Set.indicator C
      (fun θ : ℝ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ) := rfl

/-- The iterated-integral band operator is `2π` times the band-pass operator of the rescaled
frequency set. -/
lemma itOp_eq_bandOp (C : Set ℝ) (hC : MeasurableSet C) (hbd : Bornology.IsBounded C)
    (f : ℝ → ℂ) (hf1 : MeasureTheory.MemLp f 1 (volume : Measure ℝ))
    (hf2 : MeasureTheory.MemLp f 2 (volume : Measure ℝ)) (x : ℝ) :
    itOp C f x = 2 * Real.pi * bandOp {ξ : ℝ | -(2 * Real.pi) * ξ ∈ C} f x :=
  iterated_integral_eq_bandOp C hC hbd f hf1 hf2 x

lemma aesm_itKer_sub (C : Set ℝ) (hC : MeasurableSet C) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => itKer C (p.1 - p.2)) (volume.prod volume) := by
  have hbase : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      Complex.exp (-(Complex.I * (((q.1.1 - q.1.2 : ℝ)) : ℂ) * ((q.2 : ℝ) : ℂ)))) := by fun_prop
  have hset : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.2 ∈ C} := hC.preimage measurable_snd
  have heq : (fun q : (ℝ × ℝ) × ℝ => Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * (((q.1.1 - q.1.2 : ℝ)) : ℂ) * (θ : ℂ)))) q.2)
      = {q : (ℝ × ℝ) × ℝ | q.2 ∈ C}.indicator
        (fun q : (ℝ × ℝ) × ℝ =>
          Complex.exp (-(Complex.I * (((q.1.1 - q.1.2 : ℝ)) : ℂ) * ((q.2 : ℝ) : ℂ)))) := by
    funext q
    by_cases h : q.2 ∈ C
    · rw [Set.indicator_of_mem h,
        Set.indicator_of_mem (show q ∈ {q : (ℝ × ℝ) × ℝ | q.2 ∈ C} from h)]
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show q ∉ {q : (ℝ × ℝ) × ℝ | q.2 ∈ C} from h)]
  have hjoint : Measurable (fun q : (ℝ × ℝ) × ℝ => Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * (((q.1.1 - q.1.2 : ℝ)) : ℂ) * (θ : ℂ)))) q.2) := by
    rw [heq]; exact hbase.indicator hset
  have hout := (hjoint.aestronglyMeasurable
      (μ := ((volume : Measure ℝ).prod volume).prod volume)).integral_prod_right'
        (ν := (volume : Measure ℝ))
  simpa only [itKer] using hout

lemma aesm_itKer_sub' (C : Set ℝ) (hC : MeasurableSet C) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => itKer C (p.2 - p.1)) (volume.prod volume) := by
  have hbase : Measurable (fun q : (ℝ × ℝ) × ℝ =>
      Complex.exp (-(Complex.I * (((q.1.2 - q.1.1 : ℝ)) : ℂ) * ((q.2 : ℝ) : ℂ)))) := by fun_prop
  have hset : MeasurableSet {q : (ℝ × ℝ) × ℝ | q.2 ∈ C} := hC.preimage measurable_snd
  have heq : (fun q : (ℝ × ℝ) × ℝ => Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * (((q.1.2 - q.1.1 : ℝ)) : ℂ) * (θ : ℂ)))) q.2)
      = {q : (ℝ × ℝ) × ℝ | q.2 ∈ C}.indicator
        (fun q : (ℝ × ℝ) × ℝ =>
          Complex.exp (-(Complex.I * (((q.1.2 - q.1.1 : ℝ)) : ℂ) * ((q.2 : ℝ) : ℂ)))) := by
    funext q
    by_cases h : q.2 ∈ C
    · rw [Set.indicator_of_mem h,
        Set.indicator_of_mem (show q ∈ {q : (ℝ × ℝ) × ℝ | q.2 ∈ C} from h)]
    · rw [Set.indicator_of_notMem h,
        Set.indicator_of_notMem (show q ∉ {q : (ℝ × ℝ) × ℝ | q.2 ∈ C} from h)]
  have hjoint : Measurable (fun q : (ℝ × ℝ) × ℝ => Set.indicator C
        (fun θ : ℝ => Complex.exp (-(Complex.I * (((q.1.2 - q.1.1 : ℝ)) : ℂ) * (θ : ℂ)))) q.2) := by
    rw [heq]; exact hbase.indicator hset
  have hout := (hjoint.aestronglyMeasurable
      (μ := ((volume : Measure ℝ).prod volume).prod volume)).integral_prod_right'
        (ν := (volume : Measure ℝ))
  simpa only [itKer] using hout

/-- **Self-adjointness of the iterated-integral band operator.** -/
theorem itOp_selfadjoint (C : Set ℝ) (hC : MeasurableSet C) (hbd : Bornology.IsBounded C)
    (u v : ℝ → ℂ) (hu1 : MeasureTheory.MemLp u 1 (volume : Measure ℝ))
    (hv1 : MeasureTheory.MemLp v 1 (volume : Measure ℝ)) :
    (∫ x : ℝ, itOp C u x * star (v x)) = ∫ x : ℝ, u x * star (itOp C v x) := by
  have hmm : 0 ≤ (volume C).toReal := by positivity
  have hKbd : ∀ t : ℝ, ‖itKer C t‖ ≤ (volume C).toReal := fun t => itKer_norm_le C hC t
  have hKu : Integrable u := memLp_one_iff_integrable.mp hu1
  have hKv : Integrable v := memLp_one_iff_integrable.mp hv1
  have hKmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => itKer C (p.1 - p.2))
      (volume.prod volume) := aesm_itKer_sub C hC
  have hKmeas' : AEStronglyMeasurable (fun p : ℝ × ℝ => itKer C (p.2 - p.1))
      (volume.prod volume) := aesm_itKer_sub' C hC
  have hAint : Integrable (fun p : ℝ × ℝ => u p.2 * itKer C (p.1 - p.2) * star (v p.1))
      (volume.prod volume) := by
    have hdom : Integrable (fun p : ℝ × ℝ => ‖u p.2‖ * ‖v p.1‖ * (volume C).toReal)
        (volume.prod volume) := by
      refine ((hKv.norm.mul_prod hKu.norm).const_mul ((volume C).toReal)).congr ?_
      filter_upwards with p
      ring
    refine hdom.mono' ?_ ?_
    · exact ((hKu.aestronglyMeasurable.comp_snd).mul hKmeas).mul
        (hKv.aestronglyMeasurable.comp_fst).star
    · filter_upwards with p
      rw [norm_mul, norm_mul, norm_star]
      calc ‖u p.2‖ * ‖itKer C (p.1 - p.2)‖ * ‖v p.1‖
          ≤ ‖u p.2‖ * (volume C).toReal * ‖v p.1‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hKbd (p.1 - p.2)) (norm_nonneg _)) (norm_nonneg _)
        _ = ‖u p.2‖ * ‖v p.1‖ * (volume C).toReal := by ring
  have hBint : Integrable (fun p : ℝ × ℝ => u p.1 * itKer C (p.2 - p.1) * star (v p.2))
      (volume.prod volume) := by
    have hdom : Integrable (fun p : ℝ × ℝ => ‖u p.1‖ * ‖v p.2‖ * (volume C).toReal)
        (volume.prod volume) := by
      refine ((hKu.norm.mul_prod hKv.norm).const_mul ((volume C).toReal)).congr ?_
      filter_upwards with p
      ring
    refine hdom.mono' ?_ ?_
    · exact ((hKu.aestronglyMeasurable.comp_fst).mul hKmeas').mul
        (hKv.aestronglyMeasurable.comp_snd).star
    · filter_upwards with p
      rw [norm_mul, norm_mul, norm_star]
      calc ‖u p.1‖ * ‖itKer C (p.2 - p.1)‖ * ‖v p.2‖
          ≤ ‖u p.1‖ * (volume C).toReal * ‖v p.2‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hKbd (p.2 - p.1)) (norm_nonneg _)) (norm_nonneg _)
        _ = ‖u p.1‖ * ‖v p.2‖ * (volume C).toReal := by ring
  have hstarv : ∀ x : ℝ, star (∫ y : ℝ, v y * itKer C (x - y))
      = ∫ y : ℝ, itKer C (y - x) * star (v y) := by
    intro x
    rw [show star (∫ y : ℝ, v y * itKer C (x - y))
        = ∫ y : ℝ, star (v y * itKer C (x - y)) from by
      rw [show star (∫ y : ℝ, v y * itKer C (x - y))
          = (starRingEnd ℂ) (∫ y : ℝ, v y * itKer C (x - y)) from rfl,
        (integral_conj (μ := (volume : Measure ℝ))).symm]
      simp only [starRingEnd_apply]]
    refine integral_congr_ae (ae_of_all _ (fun y => ?_))
    show (starRingEnd ℂ) (v y * itKer C (x - y)) = itKer C (y - x) * star (v y)
    rw [show (starRingEnd ℂ) (v y * itKer C (x - y)) = star (v y * itKer C (x - y)) from rfl,
      star_mul', ← itKer_neg C (x - y), show -(x - y) = y - x by ring]
    ring
  have hL : (∫ x : ℝ, (∫ y : ℝ, u y * itKer C (x - y)) * star (v x))
      = ∫ p : ℝ × ℝ, u p.2 * itKer C (p.1 - p.2) * star (v p.1) ∂(volume.prod volume) := by
    rw [show (∫ x : ℝ, (∫ y : ℝ, u y * itKer C (x - y)) * star (v x))
        = ∫ x : ℝ, ∫ y : ℝ, u y * itKer C (x - y) * star (v x) from
      integral_congr_ae (ae_of_all _ (fun x => (integral_mul_const (star (v x)) _).symm))]
    rw [integral_prod (fun p : ℝ × ℝ => u p.2 * itKer C (p.1 - p.2) * star (v p.1)) hAint]
  have hR : (∫ x : ℝ, u x * star (∫ y : ℝ, v y * itKer C (x - y)))
      = ∫ p : ℝ × ℝ, u p.2 * itKer C (p.1 - p.2) * star (v p.1) ∂(volume.prod volume) := by
    rw [show (∫ x : ℝ, u x * star (∫ y : ℝ, v y * itKer C (x - y)))
        = ∫ x : ℝ, ∫ y : ℝ, u x * itKer C (y - x) * star (v y) from by
      refine integral_congr_ae (ae_of_all _ (fun x => ?_))
      show u x * star (∫ y : ℝ, v y * itKer C (x - y))
        = ∫ y : ℝ, u x * itKer C (y - x) * star (v y)
      have hcm : u x * (∫ y : ℝ, itKer C (y - x) * star (v y))
          = ∫ y : ℝ, u x * itKer C (y - x) * star (v y) := by
        rw [← integral_const_mul (u x) (fun y : ℝ => itKer C (y - x) * star (v y))]
        refine integral_congr_ae (ae_of_all _ (fun y => ?_))
        ring
      rw [hstarv x, hcm]]
    rw [integral_integral_swap (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
      (f := fun x y : ℝ => u x * itKer C (y - x) * star (v y)) hBint]
    rw [integral_prod (fun p : ℝ × ℝ => u p.2 * itKer C (p.1 - p.2) * star (v p.1)) hAint]
  change (∫ x : ℝ, (∫ y : ℝ, u y * itKer C (x - y)) * star (v x))
      = ∫ x : ℝ, u x * star (∫ y : ℝ, v y * itKer C (x - y))
  rw [hL, hR]


/-- The frequency set attached to a set `C` of spatial frequencies under the `2π`-scaling of the
Fourier transform: `freqOf C = {ξ : ℝ | -2π ξ ∈ C}`. -/
def freqOf (C : Set ℝ) : Set ℝ := {ξ : ℝ | -(2 * Real.pi) * ξ ∈ C}

lemma mem_freqOf {C : Set ℝ} {ξ : ℝ} : ξ ∈ freqOf C ↔ -(2 * Real.pi) * ξ ∈ C := Iff.rfl

lemma freqOf_mono {C D : Set ℝ} (h : C ⊆ D) : freqOf C ⊆ freqOf D := fun _ hx => h hx

lemma measurableSet_freqOf {C : Set ℝ} (hC : MeasurableSet C) : MeasurableSet (freqOf C) :=
  hC.preimage (by fun_prop)

lemma isBounded_freqOf {C : Set ℝ} (hbd : Bornology.IsBounded C) : Bornology.IsBounded (freqOf C) := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_ball (0:ℝ)).mp hbd
  refine (Metric.isBounded_iff_subset_ball (0:ℝ)).mpr ⟨r / (2 * Real.pi), fun ξ hξ => ?_⟩
  have h : |-(2 * Real.pi) * ξ| < r := by
    have hh := hr hξ
    simpa only [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs] using hh
  have h2 : |ξ| < r / (2 * Real.pi) := by
    rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at h
    exact (lt_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi)).mpr (by linarith)
  simpa only [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs] using h2

lemma freqOf_diff {A B : Set ℝ} : freqOf A \ freqOf B ⊆ freqOf (A \ B) := by
  intro ξ hξ
  exact ⟨hξ.1, fun h => hξ.2 h⟩

/-- **Plancherel for the iterated-integral band operator.** -/
lemma lintegral_enorm_itOp_sq (C : Set ℝ) (hC : MeasurableSet C) (hbd : Bornology.IsBounded C)
    (f : ℝ → ℂ) (hf1 : MeasureTheory.MemLp f 1 (volume : Measure ℝ))
    (hf2 : MeasureTheory.MemLp f 2 (volume : Measure ℝ)) :
    ∫⁻ x : ℝ, ‖itOp C f x‖ₑ ^ (2:ℝ)
      = ENNReal.ofReal ((2 * Real.pi) ^ 2) *
        ∫⁻ ξ : ℝ, ‖Set.indicator (freqOf C) (𝓕 f) ξ‖ₑ ^ (2:ℝ) := by
  have hC' : MeasurableSet (freqOf C) := measurableSet_freqOf hC
  have hbd' : Bornology.IsBounded (freqOf C) := isBounded_freqOf hbd
  have hfi : Integrable f := memLp_one_iff_integrable.mp hf1
  have h1 : MeasureTheory.MemLp (Set.indicator (freqOf C) (𝓕 f)) 1 (volume : Measure ℝ) :=
    memLp_one_indicator_fourier (freqOf C) hC' hbd' f hfi
  have h2 : MeasureTheory.MemLp (Set.indicator (freqOf C) (𝓕 f)) 2 (volume : Measure ℝ) :=
    memLp_two_indicator_fourier (freqOf C) hC' hbd' f hfi
  have hpt : ∀ x : ℝ, ‖itOp C f x‖ₑ ^ (2:ℝ)
      = ENNReal.ofReal ((2 * Real.pi) ^ 2) *
          ‖𝓕⁻ (Set.indicator (freqOf C) (𝓕 f)) x‖ₑ ^ (2:ℝ) := by
    intro x
    have h2pi : ‖((2 : ℂ) * ((Real.pi : ℝ) : ℂ))‖ₑ = ENNReal.ofReal (2 * Real.pi) := by
      rw [enorm_eq_ofReal_norm, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num,
        norm_ofReal_eq, abs_of_pos Real.pi_pos]
    have h2pi' : ENNReal.ofReal ((2 * Real.pi) ^ 2)
        = (ENNReal.ofReal (2 * Real.pi)) ^ (2:ℝ) := by
      rw [ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 2 * Real.pi) 2,
        show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
    rw [itOp_eq_bandOp C hC hbd f hf1 hf2 x, bandOp, enorm_mul, h2pi, h2pi',
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2)]
    rfl
  rw [lintegral_congr hpt, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_enorm_fourierInv_eq h1 h2]


lemma memLp_itOp (C : Set ℝ) (hC : MeasurableSet C) (hbd : Bornology.IsBounded C)
    (f : ℝ → ℂ) (hf1 : MeasureTheory.MemLp f 1 (volume : Measure ℝ))
    (hf2 : MeasureTheory.MemLp f 2 (volume : Measure ℝ)) :
    MeasureTheory.MemLp (itOp C f) 2 (volume : Measure ℝ) := by
  have hC' : MeasurableSet (freqOf C) := measurableSet_freqOf hC
  have hbd' : Bornology.IsBounded (freqOf C) := isBounded_freqOf hbd
  have h1 : MeasureTheory.MemLp (bandOp (freqOf C) f) 2 (volume : Measure ℝ) :=
    bandOp_memLp (freqOf C) hC' hbd' f (memLp_one_iff_integrable.mp hf1) hf2
  refine (h1.const_mul (2 * Real.pi)).ae_eq ?_
  filter_upwards with x
  exact (itOp_eq_bandOp C hC hbd f hf1 hf2 x).symm

/-- **Real-valued Plancherel for the iterated-integral band operator.** -/
lemma integral_enorm_itOp_sq (C : Set ℝ) (hC : MeasurableSet C) (hbd : Bornology.IsBounded C)
    (f : ℝ → ℂ) (hf1 : MeasureTheory.MemLp f 1 (volume : Measure ℝ))
    (hf2 : MeasureTheory.MemLp f 2 (volume : Measure ℝ)) :
    ∫ x : ℝ, ‖itOp C f x‖ ^ 2
      = (2 * Real.pi) ^ 2 *
        ∫ ξ : ℝ, ‖Set.indicator (freqOf C) (𝓕 f) ξ‖ ^ 2 := by
  have hC' : MeasurableSet (freqOf C) := measurableSet_freqOf hC
  have hbd' : Bornology.IsBounded (freqOf C) := isBounded_freqOf hbd
  have hfi : Integrable f := memLp_one_iff_integrable.mp hf1
  have h2 : MeasureTheory.MemLp (Set.indicator (freqOf C) (𝓕 f)) 2 (volume : Measure ℝ) :=
    memLp_two_indicator_fourier (freqOf C) hC' hbd' f hfi
  have hmem := memLp_itOp C hC hbd f hf1 hf2
  have key := lintegral_enorm_itOp_sq C hC hbd f hf1 hf2
  rw [NestedIndicator.lintegral_enorm_rpow_two volume hmem,
    NestedIndicator.lintegral_enorm_rpow_two volume h2,
    ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (2 * Real.pi) ^ 2)] at key
  have key' : ENNReal.ofReal (∫ x : ℝ, ‖itOp C f x‖ ^ 2)
      = ENNReal.ofReal ((2 * Real.pi) ^ 2 *
          ∫ ξ : ℝ, ‖Set.indicator (freqOf C) (𝓕 f) ξ‖ ^ 2) := by
    simpa only [Real.rpow_two, pow_two] using key
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun x => sq_nonneg _))
    (mul_nonneg (by positivity) (integral_nonneg (fun x => sq_nonneg _)))).mp key'



/- ## Set-level helpers: measurability, boundedness, and the identity for `coarse` -/

section ZRHelpers

variable {K : ℕ}

lemma neigh_eq_neighSet (lam : Fin K → ℝ) (j : ℕ) : neigh lam j = neighSet lam (dyadic j) := rfl

lemma measurableSet_neigh (lam : Fin K → ℝ) (j : ℕ) : MeasurableSet (neigh lam j) := by
  rw [neigh_eq_neighSet]; exact measurableSet_neighSet lam _

lemma isBounded_neigh (lam : Fin K → ℝ) (j : ℕ) : Bornology.IsBounded (neigh lam j) := by
  rw [neigh_eq_neighSet]; exact isBounded_neighSet lam _

lemma volume_neigh_ne_top (lam : Fin K → ℝ) (j : ℕ) : volume (neigh lam j) ≠ ⊤ := by
  rw [neigh_eq_neighSet]; exact (volume_neighSet_lt_top lam _).ne

lemma coarse_eq (lam : Fin K → ℝ) (j : ℕ) :
    coarse lam j = ⋃ i ∈ repSet lam j,
      Set.Icc (lam i - 2 * dyadic j) (lam i + 2 * dyadic j) := by
  ext θ
  simp only [coarse, Set.mem_ofPred_eq, Set.mem_iUnion, mem_repSet]
  constructor
  · rintro ⟨i, hi, hθ⟩
    refine ⟨i, hi, ?_⟩
    rw [Set.mem_Icc]
    exact ⟨by linarith [neg_abs_le (θ - lam i)], by linarith [le_abs_self (θ - lam i)]⟩
  · rintro ⟨i, hi, hθ⟩
    rw [Set.mem_Icc] at hθ
    exact ⟨i, hi, by rw [abs_sub_le_iff]; exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩⟩

lemma measurableSet_coarse (lam : Fin K → ℝ) (j : ℕ) : MeasurableSet (coarse lam j) := by
  rw [coarse_eq]
  exact Finset.measurableSet_biUnion _ (fun i _ => measurableSet_Icc)

lemma isBounded_coarse (lam : Fin K → ℝ) (j : ℕ) : Bornology.IsBounded (coarse lam j) := by
  have hdy : (2:ℝ) * dyadic j ≤ 1 := by
    have h := dyadic_anti (j := 0) (j' := j) (Nat.zero_le j)
    have h0 : dyadic 0 = 1/2 := by norm_num [dyadic]
    rw [h0] at h
    linarith
  have hR : ∀ i : Fin K, |lam i| ≤ ∑ a : Fin K, |lam a| :=
    fun i => Finset.single_le_sum (f := fun a => |lam a|) (fun a _ => abs_nonneg _)
      (Finset.mem_univ i)
  refine (Metric.isBounded_iff_subset_ball (0:ℝ)).mpr
    ⟨(∑ a : Fin K, |lam a|) + 2, fun θ hθ => ?_⟩
  obtain ⟨i, -, hθi⟩ := hθ
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
  calc |θ| = |(θ - lam i) + lam i| := by ring_nf
    _ ≤ |θ - lam i| + |lam i| := abs_add_le _ _
    _ ≤ 2 * dyadic j + ∑ a : Fin K, |lam a| := by linarith [hR i]
    _ < (∑ a : Fin K, |lam a|) + 2 := by linarith

noncomputable def bdry (lam : Fin K → ℝ) (j : ℕ) : Set ℝ := coarse lam j \ neigh lam j

lemma measurableSet_bdry (lam : Fin K → ℝ) (j : ℕ) : MeasurableSet (bdry lam j) :=
  (measurableSet_coarse lam j).diff (measurableSet_neigh lam j)

lemma isBounded_bdry (lam : Fin K → ℝ) (j : ℕ) : Bornology.IsBounded (bdry lam j) :=
  (isBounded_coarse lam j).subset Set.sdiff_subset

end ZRHelpers


/- ## Auxiliary helpers for the `Z_r` reduction -/

section ZRAux

/-- The `ENNReal.ofReal` of a real finite supremum is bounded by the corresponding `ENNReal`
finite supremum (nonnegative case). -/
lemma ofReal_iSup_mem_le {ι : Type*} (J : Finset ι) (hJ : J.Nonempty) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    ENNReal.ofReal (⨆ i ∈ J, a i) ≤ ⨆ i ∈ J, ENNReal.ofReal (a i) := by
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image J a hJ
  exact le_trans (ENNReal.ofReal_le_ofReal (biSup_finset_le_real J a (ha i₀) hmax))
    (le_iSup₂ (α := ℝ≥0∞) (f := fun i (_ : i ∈ J) => ENNReal.ofReal (a i)) i₀ hi₀)

/-- Splitting a finite supremum into two pieces. -/
lemma sup_sq_le_add {ι : Type*} {F S T : Finset ι}
    (hF : ∀ i, i ∈ F → i ∈ S ∨ i ∈ T) (f : ι → ℝ≥0∞) :
    (⨆ i ∈ F, f i) ^ (2:ℝ) ≤ (⨆ i ∈ S, f i) ^ (2:ℝ) + (⨆ i ∈ T, f i) ^ (2:ℝ) := by
  have h1 : (⨆ i ∈ F, f i) ≤ (⨆ i ∈ S, f i) ⊔ (⨆ i ∈ T, f i) := by
    refine iSup₂_le (fun i hi => ?_)
    rcases hF i hi with h | h
    · exact le_trans (le_iSup₂ (f := fun i (_ : i ∈ S) => f i) i h) le_sup_left
    · exact le_trans (le_iSup₂ (f := fun i (_ : i ∈ T) => f i) i h) le_sup_right
  refine le_trans (ENNReal.rpow_le_rpow h1 (by norm_num)) ?_
  rcases le_total (⨆ i ∈ S, f i) (⨆ i ∈ T, f i) with h | h
  · rw [sup_eq_right.mpr h]; exact le_add_left le_rfl
  · rw [sup_eq_left.mpr h]; exact le_add_right le_rfl

/-- The square of a finite supremum is bounded by the sum of the squares. -/
lemma sup_sq_le_sum_sq {ι : Type*} (F : Finset ι) (hF : F.Nonempty) (f : ι → ℝ≥0∞) :
    (⨆ i ∈ F, f i) ^ (2:ℝ) ≤ ∑ i ∈ F, f i ^ (2:ℝ) := by
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image F f hF
  have hsup : (⨆ i ∈ F, f i) ≤ f i₀ := iSup₂_le (fun i hi => hmax i hi)
  calc (⨆ i ∈ F, f i) ^ (2:ℝ) ≤ (f i₀) ^ (2:ℝ) := ENNReal.rpow_le_rpow hsup (by norm_num)
    _ ≤ ∑ i ∈ F, f i ^ (2:ℝ) :=
        Finset.single_le_sum (f := fun i => f i ^ (2:ℝ)) (fun i _ => by positivity) hi₀

lemma volume_ne_top_of_isBounded {A : Set ℝ} (h : Bornology.IsBounded A) : volume A ≠ ⊤ :=
  h.measure_lt_top.ne

/-- The oscillatory integrand restricted to a set of finite measure is integrable. -/
lemma integrable_indicator_exp (A : Set ℝ) (hA : MeasurableSet A) (hfin : volume A ≠ ⊤)
    (t : ℝ) :
    Integrable (Set.indicator A
      (fun θ : ℝ => Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ))))) volume := by
  refine Integrable.mono (memLp_one_iff_integrable.mp
      (memLp_indicator_const 1 hA (1:ℂ) (Or.inr hfin)))
    (Measurable.aestronglyMeasurable ?_) ?_
  · exact (by fun_prop : Measurable
      (fun θ : ℝ => Complex.exp (-(Complex.I * ((t : ℝ) : ℂ) * (θ : ℂ))))).indicator hA
  · filter_upwards with θ
    by_cases hθ : θ ∈ A
    · simp [Set.indicator_of_mem hθ, BourgainBlock.norm_exp_neg_I_mul t θ]
    · simp [Set.indicator_of_notMem hθ]

lemma integrable_mul_itKer (B : Set ℝ) (hB : MeasurableSet B) (hfin : volume B ≠ ⊤)
    (f : ℝ → ℂ) (hf : Integrable f) (x : ℝ) :
    Integrable (fun y : ℝ => f y * itKer B (x - y)) volume := by
  refine Integrable.mono ((hf.norm).const_mul ((volume B).toReal)) ?_ ?_
  · exact hf.aestronglyMeasurable.mul (aesm_inner_theta B hB x)
  · filter_upwards with y
    have hnn : (0:ℝ) ≤ (volume B).toReal * ‖f y‖ := mul_nonneg (by positivity) (norm_nonneg _)
    rw [Real.norm_of_nonneg hnn]
    calc ‖f y * itKer B (x - y)‖ = ‖f y‖ * ‖itKer B (x - y)‖ := norm_mul _ _
      _ ≤ ‖f y‖ * (volume B).toReal :=
          mul_le_mul_of_nonneg_left (itKer_norm_le B hB (x - y)) (norm_nonneg _)
      _ = (volume B).toReal * ‖f y‖ := by ring

/-- `itKer` is additive in the set. -/
lemma itKer_diff (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hb : Bornology.IsBounded A) (hBA : B ⊆ A) (t : ℝ) :
    itKer A t = itKer B t + itKer (A \ B) t := by
  have hfinA : volume A ≠ ⊤ := volume_ne_top_of_isBounded hb
  have hfinB : volume B ≠ ⊤ := volume_ne_top_of_isBounded (hb.subset hBA)
  have hfinD : volume (A \ B) ≠ ⊤ := volume_ne_top_of_isBounded (hb.subset Set.sdiff_subset)
  unfold itKer
  rw [← integral_add (integrable_indicator_exp B hB hfinB t)
    (integrable_indicator_exp (A \ B) (hA.diff hB) hfinD t)]
  apply integral_congr_ae
  filter_upwards with θ
  by_cases hθA : θ ∈ A
  · by_cases hθB : θ ∈ B
    · have hAB : θ ∉ A \ B := fun h => h.2 hθB
      rw [Set.indicator_of_mem hθA, Set.indicator_of_mem hθB, Set.indicator_of_notMem hAB]
      ring
    · have hAB : θ ∈ A \ B := ⟨hθA, hθB⟩
      rw [Set.indicator_of_mem hθA, Set.indicator_of_notMem hθB, Set.indicator_of_mem hAB]
      ring
  · have hAB : θ ∉ A \ B := fun h => hθA h.1
    rw [Set.indicator_of_notMem hθA, Set.indicator_of_notMem (fun h => hθA (hBA h)),
      Set.indicator_of_notMem hAB]
    ring

/-- `itOp` is additive in the set. -/
lemma itOp_diff (A B : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hb : Bornology.IsBounded A) (hBA : B ⊆ A) (f : ℝ → ℂ) (hf : Integrable f) (x : ℝ) :
    itOp A f x = itOp B f x + itOp (A \ B) f x := by
  have hfinB : volume B ≠ ⊤ := volume_ne_top_of_isBounded (hb.subset hBA)
  have hfinD : volume (A \ B) ≠ ⊤ := volume_ne_top_of_isBounded (hb.subset Set.sdiff_subset)
  have h1 : Integrable (fun y : ℝ => f y * itKer B (x - y)) volume :=
    integrable_mul_itKer B hB hfinB f hf x
  have h2 : Integrable (fun y : ℝ => f y * itKer (A \ B) (x - y)) volume :=
    integrable_mul_itKer (A \ B) (hA.diff hB) hfinD f hf x
  unfold itOp
  rw [← integral_add h1 h2]
  apply integral_congr_ae
  filter_upwards with y
  rw [itKer_diff A B hA hB hb hBA (x - y)]
  ring

end ZRAux

/- ## The `1`-separated hypothesis, and the per-block maximal estimate -/

/-- The hypothesis of the theorem: the sharp maximal estimate for `1`-separated frequency sets. -/
def SeparatedMaximal : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (mu : Fin N → ℝ),
    (∀ i j : Fin N, i ≠ j → 1 ≤ |mu i - mu j|) →
    ∀ (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.volume),
      ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
          (∑ k : Fin N,
            ∫ θ in (mu k - (2:ℝ)^(-(j:ℝ)-1))..(mu k + (2:ℝ)^(-(j:ℝ)-1)),
              Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2:ℝ)
        ∂MeasureTheory.volume
      ≤ ENNReal.ofReal ((C * (Real.log ((N:ℝ)+2))^2)^2)
        * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.volume

/-- The frequency set of the target neighbourhoods. -/
noncomputable def freqC {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) : Set ℝ := freqOf (neigh lam j)

lemma measurableSet_freqC {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) :
    MeasurableSet (freqC lam j) := measurableSet_freqOf (measurableSet_neigh lam j)

lemma isBounded_freqC {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) :
    Bornology.IsBounded (freqC lam j) := isBounded_freqOf (isBounded_neigh lam j)

/-- `freqOf` turns disjointness into disjointness. -/
lemma disjoint_freqOf {A B : Set ℝ} (h : Disjoint A B) : Disjoint (freqOf A) (freqOf B) := by
  rw [Set.disjoint_left] at h ⊢
  intro ξ h1 h2
  exact h (mem_freqOf.mp h1) (mem_freqOf.mp h2)

/-- A sum of disjoint indicator-squares is dominated by the square. -/
lemma sum_enorm_indicator_sq_le {ι : Type*} {F : Finset ι} {G : ι → Set ℝ}
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (G i) (G j)) (w : ℝ → ℂ) (ξ : ℝ) :
    ∑ i ∈ F, ‖Set.indicator (G i) w ξ‖ₑ ^ (2:ℝ) ≤ ‖w ξ‖ₑ ^ (2:ℝ) := by
  classical
  have hterm : ∀ i : ι, ‖Set.indicator (G i) w ξ‖ₑ ^ (2:ℝ)
      = (if ξ ∈ G i then (1:ℝ≥0∞) else 0) * ‖w ξ‖ₑ ^ (2:ℝ) := by
    intro i
    by_cases h : ξ ∈ G i
    · rw [Set.indicator_of_mem h, if_pos h, one_mul]
    · rw [Set.indicator_of_notMem h, if_neg h]
      simp
  have hcard : (F.filter (fun i => ξ ∈ G i)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    by_contra hij
    exact Set.disjoint_left.mp
      (hdisj i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij)
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  have hsum1 : ∑ i ∈ F, (if ξ ∈ G i then (1:ℝ≥0∞) else 0) ≤ 1 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast hcard
  calc ∑ i ∈ F, ‖Set.indicator (G i) w ξ‖ₑ ^ (2:ℝ)
      = ∑ i ∈ F, (if ξ ∈ G i then (1:ℝ≥0∞) else 0) * ‖w ξ‖ₑ ^ (2:ℝ) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ i ∈ F, (if ξ ∈ G i then (1:ℝ≥0∞) else 0)) * ‖w ξ‖ₑ ^ (2:ℝ) := by
        rw [Finset.sum_mul]
    _ ≤ 1 * ‖w ξ‖ₑ ^ (2:ℝ) := mul_le_mul' hsum1 le_rfl
    _ = ‖w ξ‖ₑ ^ (2:ℝ) := one_mul _

/- ## Reindexing a finite union along a bijection -/

lemma sup_finset_eq_biUnion {ι : Type*} (S : Finset ι) (f : ι → Set ℝ) :
    S.sup f = ⋃ i ∈ S, f i := by
  rw [Finset.sup_eq_iSup]
  simp only [Set.iSup_eq_iUnion]

lemma iSup_finset_add_le {ι : Type*} (S : Finset ι) (u v : ι → ℝ≥0∞) :
    (⨆ i ∈ S, (u i + v i)) ≤ (⨆ i ∈ S, u i) + (⨆ i ∈ S, v i) :=
  iSup₂_le (fun i hi => add_le_add
    (le_iSup₂ (f := fun i (_ : i ∈ S) => u i) i hi)
    (le_iSup₂ (f := fun i (_ : i ∈ S) => v i) i hi))

lemma mul_iSup_finset {ι : Type*} (S : Finset ι) (c : ℝ≥0∞) (u : ι → ℝ≥0∞) :
    c * (⨆ i ∈ S, u i) = ⨆ i ∈ S, c * u i := by
  rw [ENNReal.mul_iSup]
  refine iSup_congr (fun i => ?_)
  rw [ENNReal.mul_iSup]

lemma freqOf_eq (C : Set ℝ) : freqOf C = {ξ : ℝ | -(2 * Real.pi * ξ) ∈ C} := by
  ext ξ
  change -(2 * Real.pi) * ξ ∈ C ↔ -(2 * Real.pi * ξ) ∈ C
  rw [show -(2 * Real.pi) * ξ = -(2 * Real.pi * ξ) by ring]

lemma iUnion_finset_eq_iUnion_fin {ι : Type*} [LinearOrder ι] [DecidableEq ι]
    (S : Finset ι) (f : ι → Set ℝ) :
    (⋃ i ∈ S, f i) = ⋃ k : Fin S.card, f ((S.orderIsoOfFin rfl k : ↥S) : ι) := by
  apply le_antisymm
  · refine Set.iUnion₂_subset (fun i hi => ?_)
    have h := Set.subset_iUnion (fun k : Fin S.card => f ((S.orderIsoOfFin rfl k : ↥S) : ι))
      ((S.orderIsoOfFin rfl).symm ⟨i, hi⟩)
    have hk : ((S.orderIsoOfFin rfl ((S.orderIsoOfFin rfl).symm ⟨i, hi⟩) : ↥S) : ι) = i := by
      simp
    rwa [hk] at h
  · refine Set.iUnion_subset (fun k => ?_)
    exact Set.subset_iUnion₂ (s := fun i (_ : i ∈ S) => f i)
      (((S.orderIsoOfFin rfl k : ↥S) : ι)) ((S.orderIsoOfFin rfl k).2)

lemma iSup_finset_empty {ι : Type*} (f : ι → ℝ≥0∞) : (⨆ i ∈ (∅ : Finset ι), f i) = 0 := by
  refine le_antisymm ?_ bot_le
  exact iSup₂_le (fun i hi => absurd hi (Finset.notMem_empty i))

/-- Measurability of a finite supremum of measurable `ℝ≥0∞`-valued functions. -/
lemma measurable_iSup_finset {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ≥0∞)
    (hf : ∀ i, Measurable (f i)) : Measurable (fun x => ⨆ i ∈ S, f i x) := by
  rw [show (fun x => ⨆ i ∈ S, f i x) = fun x => S.sup (fun i => f i x) from
    funext (fun x => iSup_mem_eq_sup S (fun i => f i x))]
  classical
  induction S using Finset.induction with
  | empty => simpa using measurable_const
  | insert a s ha ih =>
      have hfun : (fun x => (insert a s).sup (fun i => f i x))
          = fun x => f a x ⊔ s.sup (fun i => f i x) := by
        funext x; rw [Finset.sup_insert]
      rw [hfun]
      exact (hf a).sup ih

/-- Measurability of the square. -/
lemma measurable_fourier_of_memLp_one {g : ℝ → ℂ} (hg : MemLp g 1 (volume : Measure ℝ)) :
    Measurable (𝓕 g) := by
  have hc : Continuous (𝓕 g) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by fun_prop) (memLp_one_iff_integrable.mp hg)
  exact hc.measurable

lemma measurable_sq_enn {u : ℝ → ℝ≥0∞} (hu : Measurable u) :
    Measurable (fun x => u x ^ (2:ℝ)) := by
  have h : (fun x => u x ^ (2:ℝ)) = fun x => u x * u x := by
    funext x; rw [ENNReal.rpow_two, pow_two]
  rw [h]
  exact hu.mul hu

lemma enorm_add_le (a b : ℂ) : ‖a + b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := by
  rw [enorm_eq_ofReal_norm, enorm_eq_ofReal_norm, enorm_eq_ofReal_norm,
    ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (norm_add_le a b)

lemma enorm_sub_le (a b : ℂ) : ‖a - b‖ₑ ≤ ‖a‖ₑ + ‖b‖ₑ := by
  rw [sub_eq_add_neg]
  calc ‖a + -b‖ₑ ≤ ‖a‖ₑ + ‖(-b)‖ₑ := enorm_add_le a (-b)
    _ = ‖a‖ₑ + ‖b‖ₑ := by rw [enorm_neg]

lemma ENNReal.add_sq_le_three (a b : ℝ≥0∞) :
    (a + b) ^ (2:ℝ) ≤ 3 * a ^ (2:ℝ) + 3 * b ^ (2:ℝ) := by
  rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.rpow_two, pow_two, pow_two, pow_two]
  have h : a * b ≤ a * a + b * b := by
    rcases le_total a b with h | h
    · calc a * b ≤ b * b := mul_le_mul' h le_rfl
        _ ≤ a * a + b * b := le_add_left le_rfl
    · calc a * b ≤ a * a := mul_le_mul' le_rfl h
        _ ≤ a * a + b * b := le_add_right le_rfl
  calc (a + b) * (a + b) = a * a + a * b + (b * a + b * b) := by rw [add_mul, mul_add, mul_add]
    _ = a * a + a * b + (a * b + b * b) := by rw [mul_comm b a]
    _ ≤ a * a + (a * a + b * b) + ((a * a + b * b) + b * b) := by
        exact add_le_add (add_le_add le_rfl h) (add_le_add h le_rfl)
    _ = 3 * (a * a) + 3 * (b * b) := by ring

/- ## The per-block maximal estimate (Step A) -/

/-- `3 * ofReal (x^2) ≤ 1` for `x = (2π)⁻¹`. -/
lemma three_mul_sq_inv_two_pi_le_one : 3 * ENNReal.ofReal (((2 * Real.pi)⁻¹)^2 : ℝ) ≤ 1 := by
  have h1 : (3:ℝ) * ((2 * Real.pi)⁻¹)^2 ≤ 1 := by
    have hpi : (2:ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have h2 : (0:ℝ) < (2 * Real.pi)^2 := by positivity
    rw [inv_pow, inv_eq_one_div, mul_one_div, div_le_iff₀ h2]
    nlinarith
  calc 3 * ENNReal.ofReal (((2 * Real.pi)⁻¹)^2 : ℝ)
      = ENNReal.ofReal 3 * ENNReal.ofReal (((2 * Real.pi)⁻¹)^2 : ℝ) := by
        rw [show (3:ℝ≥0∞) = ENNReal.ofReal 3 from by norm_num]
    _ = ENNReal.ofReal (3 * ((2 * Real.pi)⁻¹)^2) := (ENNReal.ofReal_mul (by norm_num)).symm
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h1
    _ = 1 := by norm_num

lemma ENNReal.ofReal_sq_eq (c : ℝ) (hc : 0 ≤ c) :
    ENNReal.ofReal c ^ (2:ℝ) = ENNReal.ofReal (c^2) := by
  have h1 : ENNReal.ofReal c ^ (2:ℝ) = ENNReal.ofReal c * ENNReal.ofReal c := by
    rw [ENNReal.rpow_two, pow_two]
  rw [h1, ← ENNReal.ofReal_mul hc, ← pow_two]

lemma ennreal_mul_three_add (c U V : ℝ≥0∞) : c * (3 * U + 3 * V) = 3 * c * (U + V) := by
  rw [show (3:ℝ≥0∞) * U + 3 * V = 3 * (U + V) from by rw [mul_add]]
  rw [← mul_assoc, mul_comm c 3]
/- ## The boundary-layer square function in `ENNReal` form -/

lemma continuous_itOp {C : Set ℝ} (hC : MeasurableSet C) (hbd : Bornology.IsBounded C)
    (g : ℝ → ℂ) (hg1 : MemLp g 1 (volume : Measure ℝ)) (hg2 : MemLp g 2 volume) :
    Continuous (itOp C g) := by
  have h : itOp C g = fun x => (2 * Real.pi) * bandOp (freqOf C) g x := by
    funext x; rw [itOp_eq_bandOp C hC hbd g hg1 hg2 x]; rfl
  rw [h]
  exact continuous_const.mul (bandOp_cont (freqOf C) (measurableSet_freqOf hC)
    (isBounded_freqOf hbd) g (memLp_one_iff_integrable.mp hg1))

lemma itOp_disjoint_lintegral_square {ι : Type*} (F : Finset ι) (G : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (G i)) (hbd : ∀ i, Bornology.IsBounded (G i))
    (hdisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (G i) (G j))
    (g : ℝ → ℂ) (hg1 : MemLp g 1 (volume : Measure ℝ)) (hg2 : MemLp g 2 volume) :
    ∫⁻ x : ℝ, (⨆ i ∈ F, ‖itOp (G i) g x‖ₑ) ^ (2:ℝ)
      ≤ ENNReal.ofReal ((2 * Real.pi) ^ 2) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by
  have hcont : ∀ i, Continuous (itOp (G i) g) :=
    fun i => continuous_itOp (hmeas i) (hbd i) g hg1 hg2
  have hmeasi : ∀ i, Measurable (fun x : ℝ => ‖itOp (G i) g x‖ₑ ^ (2:ℝ)) :=
    fun i => measurable_sq_enn ((hcont i).measurable.enorm)
  have hdisjF : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (freqOf (G i)) (freqOf (G j)) :=
    fun i hi j hj hij => disjoint_freqOf (hdisj i hi j hj hij)
  rcases F.eq_empty_or_nonempty with hF | hF
  · rw [hF]
    have h0 : ∀ x : ℝ, (⨆ i ∈ (∅ : Finset ι), ‖itOp (G i) g x‖ₑ) ^ (2:ℝ) = 0 := by
      intro x
      rw [iSup_finset_empty]
      exact ENNReal.zero_rpow_of_pos (by norm_num)
    rw [lintegral_congr h0]; simp
  calc ∫⁻ x : ℝ, (⨆ i ∈ F, ‖itOp (G i) g x‖ₑ) ^ (2:ℝ)
      ≤ ∫⁻ x : ℝ, ∑ i ∈ F, ‖itOp (G i) g x‖ₑ ^ (2:ℝ) :=
        lintegral_mono (fun x => sup_sq_le_sum_sq F hF _)
    _ = ∑ i ∈ F, ∫⁻ x : ℝ, ‖itOp (G i) g x‖ₑ ^ (2:ℝ) := lintegral_finsetSum F (fun i _ => hmeasi i)
    _ = ∑ i ∈ F, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
          ∫⁻ ξ : ℝ, ‖Set.indicator (freqOf (G i)) (𝓕 g) ξ‖ₑ ^ (2:ℝ) :=
        Finset.sum_congr rfl (fun i _ => lintegral_enorm_itOp_sq (G i) (hmeas i) (hbd i) g hg1 hg2)
    _ = ENNReal.ofReal ((2 * Real.pi) ^ 2) *
          ∑ i ∈ F, ∫⁻ ξ : ℝ, ‖Set.indicator (freqOf (G i)) (𝓕 g) ξ‖ₑ ^ (2:ℝ) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 2) * ∫⁻ ξ : ℝ, ‖𝓕 g ξ‖ₑ ^ (2:ℝ) := by
        refine mul_le_mul' le_rfl ?_
        have hm2 : ∀ i, Measurable (fun ξ : ℝ => ‖Set.indicator (freqOf (G i)) (𝓕 g) ξ‖ₑ ^ (2:ℝ)) :=
          fun i => measurable_sq_enn
            ((measurable_fourier_of_memLp_one hg1).indicator
              (measurableSet_freqOf (hmeas i))).enorm
        rw [← lintegral_finsetSum F (fun i _ => hm2 i)]
        refine lintegral_mono (fun ξ => ?_)
        exact sum_enorm_indicator_sq_le hdisjF (𝓕 g) ξ
    _ = ENNReal.ofReal ((2 * Real.pi) ^ 2) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by
        rw [lintegral_enorm_fourier_eq (memLp_one_iff_integrable.mp hg1) hg2]

/-- The conclusion of `block_maximal_of_separated` for a fixed constant `C'`. -/
def BlockMaximal (C' : ℝ) : Prop :=
  ∀ (s : ℕ) (A : Fin s → ℝ) (c d : ℕ),
    (∀ i l : Fin s, i ≠ l → (2:ℝ)^(-(c:ℝ)-1) < |A i - A l|) →
    c + 3 ≤ d →
    ∀ (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)),
      ∫⁻ x, (⨆ j ∈ Finset.Icc (c+3) d, ‖∫ y : ℝ, f y *
          (∫ θ : ℝ, Set.indicator
            (⋃ a : Fin s, Set.Icc (A a - 2 * (2:ℝ)^(-(j:ℝ)-1)) (A a + 2 * (2:ℝ)^(-(j:ℝ)-1)))
            (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ) ^ (2:ℝ)
        ∂MeasureTheory.volume
      ≤ ENNReal.ofReal ((C' * (Real.log ((s:ℝ)+2))^2)^2)
        * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.volume

lemma block_max_enn {K : ℕ} (lam : Fin K → ℝ) (C' : ℝ) (hC'pos : 0 < C')
    (hC'max : BlockMaximal C') :
    ∀ (a : ℕ) (F : Finset ℕ),
      (∀ j ∈ F, a ≤ j) → (∀ j ∈ F, blockIndex lam j = blockIndex lam a) →
      ∀ (g : ℝ → ℂ), Integrable g → MemLp g 2 →
        ∫⁻ x : ℝ, (⨆ j ∈ F, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
          ≤ ENNReal.ofReal ((10 * (1 + C' * (Real.log ((K:ℝ)+2))^2)) ^ 2)
              * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by
  intro a F haF hbF g hg1 hg2
  classical
  have hlog : 0 ≤ Real.log ((K:ℝ)+2) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ K + 2))
  set T : ℝ := C' * (Real.log ((K:ℝ)+2))^2 with hTdef
  have hTnn : 0 ≤ T := mul_nonneg (le_of_lt hC'pos) (sq_nonneg _)
  have hbm : ∀ j : ℕ, Measurable (fun x : ℝ => ‖bandOp (freqC lam j) g x‖ₑ) := fun j =>
    (bandOp_cont (freqC lam j) (measurableSet_freqC lam j) (isBounded_freqC lam j) g hg1
      ).measurable.enorm
  let Fs : Finset ℕ := F.filter (fun j => j ≤ a + 2)
  let Fl : Finset ℕ := F.filter (fun j => a + 3 ≤ j)
  have hsplit : ∀ i, i ∈ F → i ∈ Fs ∨ i ∈ Fl := by
    intro i hi
    by_cases h : i ≤ a + 2
    · exact Or.inl (Finset.mem_filter.mpr ⟨hi, h⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hi, by omega⟩)
  have hFlF : ∀ j ∈ Fl, j ∈ F := fun j hj => (Finset.mem_filter.mp hj).1
  have hFl_ge : ∀ j ∈ Fl, a + 3 ≤ j := fun j hj => (Finset.mem_filter.mp hj).2
  have hsplit_int : ∫⁻ x : ℝ, (⨆ j ∈ F, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
      ≤ (∫⁻ x : ℝ, (⨆ j ∈ Fs, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ))
        + ∫⁻ x : ℝ, (⨆ j ∈ Fl, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ) := by
    have hpt : ∀ x : ℝ, (⨆ j ∈ F, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
        ≤ (⨆ j ∈ Fs, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
          + (⨆ j ∈ Fl, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ) :=
      fun x => sup_sq_le_add hsplit _
    calc ∫⁻ x : ℝ, (⨆ j ∈ F, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
        ≤ ∫⁻ x : ℝ, ((⨆ j ∈ Fs, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
            + (⨆ j ∈ Fl, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)) := lintegral_mono hpt
      _ = _ + _ := lintegral_add_left (measurable_sq_enn (measurable_iSup_finset Fs _ hbm)) _
  have hA : ∫⁻ x : ℝ, (⨆ j ∈ Fs, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
      ≤ 3 * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by
    rcases Fs.eq_empty_or_nonempty with hFs | hFs
    · rw [hFs]
      have h0 : ∀ x : ℝ, (⨆ j ∈ (∅ : Finset ℕ), ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ) = 0 := by
        intro x
        rw [iSup_finset_empty]
        exact ENNReal.zero_rpow_of_pos (by norm_num)
      rw [lintegral_congr h0]
      simp
    have hsub : Fs ⊆ Finset.Icc a (a + 2) := by
      intro j hj
      exact Finset.mem_Icc.mpr ⟨haF j (Finset.mem_filter.mp hj).1, (Finset.mem_filter.mp hj).2⟩
    have hcard : Fs.card ≤ 3 := by
      calc Fs.card ≤ (Finset.Icc a (a + 2)).card := Finset.card_le_card hsub
        _ = 3 := by rw [Nat.card_Icc]; omega
    calc ∫⁻ x : ℝ, (⨆ j ∈ Fs, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
        ≤ ∫⁻ x : ℝ, ∑ j ∈ Fs, ‖bandOp (freqC lam j) g x‖ₑ ^ (2:ℝ) :=
          lintegral_mono (fun x => sup_sq_le_sum_sq Fs hFs _)
      _ = ∑ j ∈ Fs, ∫⁻ x : ℝ, ‖bandOp (freqC lam j) g x‖ₑ ^ (2:ℝ) :=
          lintegral_finsetSum Fs (fun j _ => measurable_sq_enn (hbm j))
      _ ≤ ∑ j ∈ Fs, ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) :=
          Finset.sum_le_sum (fun j _ => bandOp_lintegral (freqC lam j)
            (measurableSet_freqC lam j) (isBounded_freqC lam j) g hg1 hg2)
      _ = Fs.card * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 3 * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by
          refine mul_le_mul' ?_ le_rfl
          exact_mod_cast hcard
  have hB : ∫⁻ x : ℝ, (⨆ j ∈ Fl, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
      ≤ ENNReal.ofReal (T ^ 2 + (2 * Real.pi) ^ 2) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by
    rcases Fl.eq_empty_or_nonempty with hFl | hFlne
    · rw [hFl]
      have h0 : ∀ x : ℝ, (⨆ j ∈ (∅ : Finset ℕ), ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ) = 0 := by
        intro x
        rw [iSup_finset_empty]
        exact ENNReal.zero_rpow_of_pos (by norm_num)
      rw [lintegral_congr h0]
      simp
    let cc : ℕ := clusterCount lam a
    let e : Fin cc ≃o ↥(repSet lam a) := (repSet lam a).orderIsoOfFin rfl
    let A : Fin cc → ℝ := fun i => lam ((e i : ↥(repSet lam a)) : Fin K)
    let d : ℕ := Fl.max' hFlne
    have hd3 : a + 3 ≤ d := by
      obtain ⟨j₁, hj₁⟩ := hFlne
      exact le_trans (hFl_ge j₁ hj₁) (Finset.le_max' Fl j₁ hj₁)
    have hsepA : ∀ i l : Fin cc, i ≠ l → (2:ℝ)^(-(a:ℝ)-1) < |A i - A l| := by
      intro i l hil
      have h1 : IsRep lam a ((e i : ↥(repSet lam a)) : Fin K) := mem_repSet.mp (e i).2
      have h2 : IsRep lam a ((e l : ↥(repSet lam a)) : Fin K) := mem_repSet.mp (e l).2
      have hne : ((e i : ↥(repSet lam a)) : Fin K) ≠ ((e l : ↥(repSet lam a)) : Fin K) := by
        intro hcon
        exact hil (e.injective (Subtype.ext hcon))
      have h3 := rep_sep h1 h2 hne
      simpa only [A, dyadic] using h3
    have hcoarse_eq : ∀ j ∈ Fl, coarse lam j = ⋃ i : Fin cc,
        Set.Icc (A i - 2 * dyadic j) (A i + 2 * dyadic j) := by
      intro j hj
      have haj : a ≤ j := le_trans (Nat.le_add_right a 3) (hFl_ge j hj)
      have hbj : blockIndex lam a = blockIndex lam j := (hbF j (hFlF j hj)).symm
      have hreps : repSet lam j = repSet lam a := (repSet_eq_of_blockIndex_eq haj hbj).symm
      show coarse lam j = ⋃ k : Fin cc, Set.Icc (A k - 2 * dyadic j) (A k + 2 * dyadic j)
      rw [coarse_eq, hreps]
      exact iUnion_finset_eq_iUnion_fin (repSet lam a)
        (fun i => Set.Icc (lam i - 2 * dyadic j) (lam i + 2 * dyadic j))
    have hneigh_coarse : ∀ j ∈ Fl, neigh lam j ⊆ coarse lam j := by
      intro j hj
      exact neigh_subset_coarse (not_badScale_of_lt_blockIndex_eq
        (Nat.lt_of_lt_of_le (by omega : a < a + 3) (hFl_ge j hj))
        (hbF j (hFlF j hj)).symm)
    have hitOp_eq : ∀ j ∈ Fl, ∀ x : ℝ, itOp (neigh lam j) g x
        = itOp (coarse lam j) g x - itOp (coarse lam j \ neigh lam j) g x := by
      intro j hj x
      have h := itOp_diff (coarse lam j) (neigh lam j) (measurableSet_coarse lam j)
        (measurableSet_neigh lam j) (isBounded_coarse lam j) (hneigh_coarse j hj) g hg1 x
      change itOp (neigh lam j) g x = itOp (coarse lam j) g x
        - itOp (coarse lam j \ neigh lam j) g x
      rw [h]
      ring
    have hterm : ∀ j ∈ Fl, ∀ x : ℝ, ‖bandOp (freqC lam j) g x‖ₑ
        ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹) *
            (‖itOp (coarse lam j) g x‖ₑ + ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ) := by
      intro j hj x
      have hne : (((2 * Real.pi : ℝ)) : ℂ) ≠ 0 := by
        rw [Complex.ofReal_ne_zero]; positivity
      have hthis := itOp_eq_bandOp (neigh lam j) (measurableSet_neigh lam j)
        (isBounded_neigh lam j) g (memLp_one_iff_integrable.mpr hg1) hg2 x
      have hb : bandOp (freqC lam j) g x = (((2 * Real.pi)⁻¹ : ℝ) : ℂ)
          * itOp (neigh lam j) g x := by
        have hfreq : freqC lam j = {ξ : ℝ | -(2 * Real.pi) * ξ ∈ neigh lam j} := by
          unfold freqC
          rfl
        rw [hfreq, hthis]
        rw [show (2 : ℂ) * (Real.pi : ℂ) = (((2 * Real.pi : ℝ)) : ℂ) by push_cast; ring]
        rw [← mul_assoc, ← Complex.ofReal_mul,
          inv_mul_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0), Complex.ofReal_one, one_mul]
      rw [hb, enorm_mul]
      have h2π : ‖(((2 * Real.pi)⁻¹ : ℝ) : ℂ)‖ₑ = ENNReal.ofReal ((2 * Real.pi)⁻¹) := by
        rw [enorm_eq_ofReal_norm, norm_ofReal_eq, abs_of_pos (by positivity)]
      rw [h2π]
      refine mul_le_mul' le_rfl ?_
      rw [hitOp_eq j hj x]
      exact enorm_sub_le _ _
    have hpt : ∀ x : ℝ, (⨆ j ∈ Fl, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
        ≤ (⨆ j ∈ Fl, ‖itOp (coarse lam j) g x‖ₑ) ^ (2:ℝ)
          + (⨆ j ∈ Fl, ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ) ^ (2:ℝ) := by
      intro x
      have h1 : (⨆ j ∈ Fl, ‖bandOp (freqC lam j) g x‖ₑ)
          ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹) *
              ((⨆ j ∈ Fl, ‖itOp (coarse lam j) g x‖ₑ)
                + (⨆ j ∈ Fl, ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ)) := by
        calc (⨆ j ∈ Fl, ‖bandOp (freqC lam j) g x‖ₑ)
            ≤ (⨆ j ∈ Fl, ENNReal.ofReal ((2 * Real.pi)⁻¹) *
                (‖itOp (coarse lam j) g x‖ₑ + ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ)) :=
              iSup₂_le (fun j hj => le_trans (hterm j hj x)
                (le_iSup₂ (f := fun j (_ : j ∈ Fl) => ENNReal.ofReal ((2 * Real.pi)⁻¹) *
                  (‖itOp (coarse lam j) g x‖ₑ
                    + ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ)) j hj))
          _ = ENNReal.ofReal ((2 * Real.pi)⁻¹) *
                (⨆ j ∈ Fl, (‖itOp (coarse lam j) g x‖ₑ
                  + ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ)) :=
              (mul_iSup_finset Fl _ _).symm
          _ ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹) *
                ((⨆ j ∈ Fl, ‖itOp (coarse lam j) g x‖ₑ)
                  + (⨆ j ∈ Fl, ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ)) :=
              mul_le_mul' le_rfl (iSup_finset_add_le Fl _ _)
      calc (⨆ j ∈ Fl, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
          ≤ (ENNReal.ofReal ((2 * Real.pi)⁻¹) *
              ((⨆ j ∈ Fl, ‖itOp (coarse lam j) g x‖ₑ)
                + (⨆ j ∈ Fl, ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ))) ^ (2:ℝ) :=
            ENNReal.rpow_le_rpow h1 (by norm_num)
        _ = ENNReal.ofReal ((2 * Real.pi)⁻¹) ^ (2:ℝ) *
              ((⨆ j ∈ Fl, ‖itOp (coarse lam j) g x‖ₑ)
                + (⨆ j ∈ Fl, ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ)) ^ (2:ℝ) :=
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
        _ ≤ ENNReal.ofReal ((2 * Real.pi)⁻¹) ^ (2:ℝ) *
              (3 * (⨆ j ∈ Fl, ‖itOp (coarse lam j) g x‖ₑ) ^ (2:ℝ)
                + 3 * (⨆ j ∈ Fl, ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ) ^ (2:ℝ)) :=
            mul_le_mul' le_rfl (ENNReal.add_sq_le_three _ _)
        _ = 3 * ENNReal.ofReal ((2 * Real.pi)⁻¹) ^ (2:ℝ) *
              ((⨆ j ∈ Fl, ‖itOp (coarse lam j) g x‖ₑ) ^ (2:ℝ)
                + (⨆ j ∈ Fl, ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ) ^ (2:ℝ)) :=
            ennreal_mul_three_add _ _ _
        _ ≤ 1 * ((⨆ j ∈ Fl, ‖itOp (coarse lam j) g x‖ₑ) ^ (2:ℝ)
                + (⨆ j ∈ Fl, ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ) ^ (2:ℝ)) := by
            refine mul_le_mul' ?_ le_rfl
            rw [ENNReal.ofReal_sq_eq ((2 * Real.pi)⁻¹) (by positivity)]
            exact three_mul_sq_inv_two_pi_le_one
        _ = (⨆ j ∈ Fl, ‖itOp (coarse lam j) g x‖ₑ) ^ (2:ℝ)
              + (⨆ j ∈ Fl, ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ) ^ (2:ℝ) := one_mul _
    have hmeasU : Measurable (fun x : ℝ =>
        (⨆ j ∈ Fl, ‖itOp (coarse lam j) g x‖ₑ) ^ (2:ℝ)) :=
      measurable_sq_enn (measurable_iSup_finset Fl _
        (fun j => (continuous_itOp (measurableSet_coarse lam j) (isBounded_coarse lam j) g
          (memLp_one_iff_integrable.mpr hg1) hg2).measurable.enorm))
    have hU : ∫⁻ x : ℝ, (⨆ j ∈ Fl, ‖itOp (coarse lam j) g x‖ₑ) ^ (2:ℝ)
        ≤ ENNReal.ofReal (T ^ 2) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by
      have hpt1 : ∀ x : ℝ, (⨆ j ∈ Fl, ‖itOp (coarse lam j) g x‖ₑ)
          ≤ (⨆ j ∈ Finset.Icc (a+3) d,
              ‖itOp (⋃ i : Fin cc, Set.Icc (A i - 2 * dyadic j) (A i + 2 * dyadic j)) g x‖ₑ) := by
        intro x
        refine iSup₂_le (fun j hj => ?_)
        rw [hcoarse_eq j hj]
        exact le_iSup₂ (f := fun j (_ : j ∈ Finset.Icc (a+3) d) =>
          ‖itOp (⋃ i : Fin cc, Set.Icc (A i - 2 * dyadic j) (A i + 2 * dyadic j)) g x‖ₑ)
          j (Finset.mem_Icc.mpr ⟨hFl_ge j hj, Finset.le_max' Fl j hj⟩)
      have hCM := hC'max cc A a d hsepA hd3 g hg2
      refine le_trans (le_trans (lintegral_mono (fun x => ENNReal.rpow_le_rpow (hpt1 x)
        (by norm_num))) hCM) ?_
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have hccK : cc ≤ K := clusterCount_le lam a
      have h1 : Real.log ((cc:ℝ) + 2) ≤ Real.log ((K:ℝ) + 2) :=
        Real.log_le_log (by positivity) (by exact_mod_cast (by omega : cc + 2 ≤ K + 2))
      have h2 : 0 ≤ Real.log ((cc:ℝ) + 2) :=
        Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ cc + 2))
      have h3 : C' * (Real.log ((cc:ℝ) + 2))^2 ≤ T := by
        rw [hTdef]
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hC'pos)
        nlinarith [h1, h2]
      have h3nn : 0 ≤ C' * (Real.log ((cc:ℝ) + 2))^2 :=
        mul_nonneg (le_of_lt hC'pos) (sq_nonneg _)
      nlinarith [h3, h3nn, hTnn, sq_nonneg T]
    have hV : ∫⁻ x : ℝ, (⨆ j ∈ Fl, ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((2 * Real.pi) ^ 2) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) :=
      itOp_disjoint_lintegral_square Fl (fun j => coarse lam j \ neigh lam j)
        (fun j => (measurableSet_coarse lam j).diff (measurableSet_neigh lam j))
        (fun j => (isBounded_coarse lam j).subset Set.sdiff_subset)
        (fun i _ j _ hij => by
          rcases lt_or_gt_of_ne hij with h | h
          · exact disjoint_boundary h
          · exact (disjoint_boundary h).symm)
        g (memLp_one_iff_integrable.mpr hg1) hg2
    calc ∫⁻ x : ℝ, (⨆ j ∈ Fl, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
        ≤ ∫⁻ x : ℝ, ((⨆ j ∈ Fl, ‖itOp (coarse lam j) g x‖ₑ) ^ (2:ℝ)
              + (⨆ j ∈ Fl, ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ) ^ (2:ℝ)) :=
          lintegral_mono hpt
      _ = (∫⁻ x : ℝ, (⨆ j ∈ Fl, ‖itOp (coarse lam j) g x‖ₑ) ^ (2:ℝ))
            + ∫⁻ x : ℝ, (⨆ j ∈ Fl, ‖itOp (coarse lam j \ neigh lam j) g x‖ₑ) ^ (2:ℝ) :=
          lintegral_add_left hmeasU _
      _ ≤ (ENNReal.ofReal (T ^ 2) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ))
            + ENNReal.ofReal ((2 * Real.pi) ^ 2) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) :=
          add_le_add hU hV
      _ = ENNReal.ofReal (T ^ 2 + (2 * Real.pi) ^ 2) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by
          rw [← add_mul, ← ENNReal.ofReal_add (sq_nonneg T) (by positivity)]
  calc ∫⁻ x : ℝ, (⨆ j ∈ F, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
      ≤ (∫⁻ x : ℝ, (⨆ j ∈ Fs, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ))
          + (∫⁻ x : ℝ, (⨆ j ∈ Fl, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)) := hsplit_int
    _ ≤ (3 * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ))
          + ENNReal.ofReal (T ^ 2 + (2 * Real.pi) ^ 2) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) :=
        add_le_add hA hB
    _ = (3 + ENNReal.ofReal (T ^ 2 + (2 * Real.pi) ^ 2)) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by
        rw [add_mul]
    _ ≤ ENNReal.ofReal ((10 * (1 + T)) ^ 2) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by
        refine mul_le_mul' ?_ le_rfl
        rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) from by norm_num,
          ← ENNReal.ofReal_add (by norm_num) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [hTnn, Real.pi_pos, Real.pi_lt_four])
/-! ## Step B: the per-block maximal and dual estimates -/

/-- A finite sup of nonnegative reals is nonnegative. -/
lemma biSup_finset_nonneg {ι : Type*} (S : Finset ι) (f : ι → ℝ) (hnn : ∀ i, 0 ≤ f i) :
    0 ≤ ⨆ i ∈ S, f i := by
  rcases S.eq_empty_or_nonempty with h | ⟨i, hi⟩
  · simp [h]
  · exact le_trans (hnn i) (le_biSup_finset_real S f hi)

/-- The inverse Fourier transform of the zero function vanishes. -/
lemma fourierInv_zero_apply (x : ℝ) : (𝓕⁻ (0 : ℝ → ℂ)) x = 0 := by
  rw [Real.fourierInv_eq']
  simp

/-- The ordinary integral of `F ^ (2:ℝ)` is the integral of `F ^ 2`. -/
lemma integral_rpow_two_eq_sq (F : ℝ → ℝ) :
    (∫ x : ℝ, F x ^ (2:ℝ)) = ∫ x : ℝ, F x ^ 2 :=
  integral_congr_ae (Filter.Eventually.of_forall (fun x => Real.rpow_two (F x)))

/-- `bandOp C u = 0` when `u` is not integrable (then `𝓕 u = 0` identically). -/
lemma bandOp_eq_zero_of_not_integrable {C : Set ℝ} {u : ℝ → ℂ}
    (hu : ¬ Integrable u (volume : Measure ℝ)) : bandOp C u = 0 := by
  funext x
  rw [bandOp, fourier_eq_zero_of_not_integrable hu]
  simp only [Set.indicator_zero', Pi.zero_apply]
  exact fourierInv_zero_apply x

/-- `bandOp` of the empty frequency set vanishes. -/
lemma bandOp_empty (g : ℝ → ℂ) : bandOp (∅ : Set ℝ) g = 0 := by
  funext x
  rw [bandOp, Set.indicator_empty', Pi.zero_apply]
  exact fourierInv_zero_apply x

/-- The pointwise sup of the norms of a finite family of band-pass operators is in `L²`. -/
lemma memLp_iSup_bandOp {ι : Type*} (S : Finset ι) (C : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (C i)) (hbd : ∀ i, Bornology.IsBounded (C i))
    (g : ℝ → ℂ) (hg1 : Integrable g) (hg2 : MemLp g 2 (volume : Measure ℝ)) :
    MemLp (fun x : ℝ => ⨆ i ∈ S, ‖bandOp (C i) g x‖) 2 (volume : Measure ℝ) := by
  have hsum : MemLp (fun x : ℝ => ∑ i ∈ S, ‖bandOp (C i) g x‖) 2 (volume : Measure ℝ) :=
    memLp_finsetSum S (fun i _ => (bandOp_memLp (C i) (hmeas i) (hbd i) g hg1 hg2).norm)
  refine MemLp.of_le hsum ?_ ?_
  · exact (Measurable.biSup (↑S : Set ι) S.countable_toSet
      (fun i _ => (bandOp_cont (C i) (hmeas i) (hbd i) g hg1).norm.measurable)).aestronglyMeasurable
  · filter_upwards with x
    have h1 : (0:ℝ) ≤ ⨆ i ∈ S, ‖bandOp (C i) g x‖ :=
      biSup_finset_nonneg S _ (fun i => norm_nonneg _)
    have h2 : (0:ℝ) ≤ ∑ i ∈ S, ‖bandOp (C i) g x‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    rw [Real.norm_of_nonneg h1, Real.norm_of_nonneg h2]
    exact biSup_finset_le_real S _ h2
      (fun i hi => Finset.single_le_sum (f := fun j => ‖bandOp (C j) g x‖)
        (fun j _ => norm_nonneg _) hi)

/-- **Per-block maximal estimate** (`ENNReal` form): if all the scales of a finite set `J` have the
same block index `r`, then the maximal estimate for those scales holds with the constant of
`block_max_enn`. -/
lemma blockIndex_maximal_enn {K : ℕ} (lam : Fin K → ℝ) (C' : ℝ) (hC'pos : 0 < C')
    (hC'max : BlockMaximal C') :
    ∀ (r : ℕ) (J : Finset ℕ),
      (∀ j ∈ J, blockIndex lam j = r) →
      ∀ (g : ℝ → ℂ), Integrable g → MemLp g 2 →
        ∫⁻ x : ℝ, (⨆ j ∈ J, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
          ≤ ENNReal.ofReal ((10 * (1 + C' * (Real.log ((K:ℝ)+2))^2)) ^ 2)
              * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) := by
  have hBmax := block_max_enn lam C' hC'pos hC'max
  intro r J hJ g hg1 hg2
  rcases J.eq_empty_or_nonempty with hJ0 | hJne
  · rw [hJ0]
    have h0 : ∀ x : ℝ, (⨆ j ∈ (∅ : Finset ℕ), ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ) = 0 := by
      intro x
      rw [iSup_finset_empty]
      exact ENNReal.zero_rpow_of_pos (by norm_num)
    rw [lintegral_congr h0]; simp
  · refine hBmax (J.min' hJne) J (fun j hj => Finset.min'_le J j hj) (fun j hj => ?_) g hg1 hg2
    exact (hJ j hj).trans (hJ (J.min' hJne) (Finset.min'_mem J hJne)).symm

/-- The per-block maximal estimate in real `L²` (square-root) form. -/
lemma block_maximal_real {K : ℕ} (lam : Fin K → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hmax : ∀ (r : ℕ) (J : Finset ℕ), (∀ j ∈ J, blockIndex lam j = r) →
      ∀ (g : ℝ → ℂ), Integrable g → MemLp g 2 →
        ∫⁻ x : ℝ, (⨆ j ∈ J, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
          ≤ ENNReal.ofReal (B ^ 2) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ)) :
    ∀ (r : ℕ) (g : ℝ → ℂ), Integrable g → MemLp g 2 → ∀ (J : Finset ℕ),
      Real.sqrt (∫ x : ℝ, (⨆ j ∈ J.filter (fun j => blockIndex lam j = r),
          ‖bandOp (freqC lam j) g x‖) ^ 2)
        ≤ B * Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2) := by
  intro r g hg1 hg2 J
  set J' : Finset ℕ := J.filter (fun j => blockIndex lam j = r) with hJ'def
  have hJ'r : ∀ j ∈ J', blockIndex lam j = r := fun j hj => (Finset.mem_filter.mp hj).2
  have hM := memLp_iSup_bandOp J' (freqC lam) (measurableSet_freqC lam) (isBounded_freqC lam)
    g hg1 hg2
  have hE := hmax r J' hJ'r g hg1 hg2
  rw [lintegral_iSup_finset_enorm_eq_ofReal J' _ hM,
    NestedIndicator.lintegral_enorm_rpow_two volume hg2,
    integral_rpow_two_eq_sq (fun x => ⨆ j ∈ J', ‖bandOp (freqC lam j) g x‖),
    integral_rpow_two_eq_sq (fun x => ‖g x‖)] at hE
  have hsq : ∫ x : ℝ, (⨆ j ∈ J', ‖bandOp (freqC lam j) g x‖) ^ 2
      ≤ B ^ 2 * ∫ x : ℝ, ‖g x‖ ^ 2 := by
    rw [← ENNReal.ofReal_mul (sq_nonneg B)] at hE
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg B)
      (integral_nonneg (fun x => sq_nonneg _)))).mp hE
  calc Real.sqrt (∫ x : ℝ, (⨆ j ∈ J', ‖bandOp (freqC lam j) g x‖) ^ 2)
      ≤ Real.sqrt (B ^ 2 * ∫ x : ℝ, ‖g x‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = B * Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg B), Real.sqrt_sq hB]

/-- **Block dual estimate.**  For `L¹ ∩ L²` weights with pairwise disjoint supports, the sum of the
band-pass operators belonging to a single block is bounded by `B √(∑ ‖u j‖²)`. -/
lemma blockIndex_dual {K : ℕ} (lam : Fin K → ℝ) (B : ℝ) (hB : 0 < B)
    (hmax : ∀ (r : ℕ) (J : Finset ℕ), (∀ j ∈ J, blockIndex lam j = r) →
      ∀ (g : ℝ → ℂ), Integrable g → MemLp g 2 →
        ∫⁻ x : ℝ, (⨆ j ∈ J, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
          ≤ ENNReal.ofReal (B ^ 2) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ)) :
    ∀ (r : ℕ) (J : Finset ℕ) (u : ℕ → ℝ → ℂ),
      (∀ j ∈ J, MemLp (u j) 1 (volume : Measure ℝ)) →
      (∀ j ∈ J, MemLp (u j) 2 (volume : Measure ℝ)) →
      (∀ j ∈ J, ∀ k ∈ J, j ≠ k → ∀ x : ℝ, u j x * star (u k x) = 0) →
      Real.sqrt (∫ x : ℝ, ‖∑ j ∈ J.filter (fun j => blockIndex lam j = r),
          bandOp (freqC lam j) (u j) x‖ ^ 2)
        ≤ B * Real.sqrt (∑ j ∈ J.filter (fun j => blockIndex lam j = r),
            ∫ x : ℝ, ‖u j x‖ ^ 2) := by
  intro r J u hu1 hu2 hdisj
  set C : ℕ → Set ℝ := fun i => if blockIndex lam i = r then freqC lam i else ∅ with hCdef
  have hCeq : ∀ i, blockIndex lam i = r → C i = freqC lam i :=
    fun i h => by rw [hCdef]; exact if_pos h
  have hCneq : ∀ i, blockIndex lam i ≠ r → C i = ∅ :=
    fun i h => by rw [hCdef]; exact if_neg h
  have hCmeas : ∀ i, MeasurableSet (C i) := by
    intro i
    by_cases h : blockIndex lam i = r
    · rw [hCeq i h]; exact measurableSet_freqC lam i
    · rw [hCneq i h]; exact MeasurableSet.empty
  have hCbd : ∀ i, Bornology.IsBounded (C i) := by
    intro i
    by_cases h : blockIndex lam i = r
    · rw [hCeq i h]; exact isBounded_freqC lam i
    · rw [hCneq i h]; exact Bornology.isBounded_empty
  have hCmax : ∀ (g : ℝ → ℂ), Integrable g → MemLp g 2 → ∀ (J'' : Finset ℕ),
      Real.sqrt (∫ x : ℝ, (⨆ i ∈ J'', ‖bandOp (C i) g x‖) ^ 2)
        ≤ B * Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2) := by
    intro g hg1 hg2 J''
    set F : Finset ℕ := J''.filter (fun i => blockIndex lam i = r) with hFdef
    have hsup : ∀ x : ℝ, (⨆ i ∈ J'', ‖bandOp (C i) g x‖ₑ)
        ≤ ⨆ i ∈ F, ‖bandOp (freqC lam i) g x‖ₑ := by
      intro x
      refine iSup₂_le (fun i hi => ?_)
      by_cases h : blockIndex lam i = r
      · rw [hCeq i h]
        exact le_iSup₂ (f := fun i (_ : i ∈ F) => ‖bandOp (freqC lam i) g x‖ₑ) i
          (Finset.mem_filter.mpr ⟨hi, h⟩)
      · rw [hCneq i h, bandOp_empty]
        simp
    have h1 : ∫⁻ x : ℝ, (⨆ i ∈ J'', ‖bandOp (C i) g x‖ₑ) ^ (2:ℝ) ∂volume
        ≤ ∫⁻ x : ℝ, (⨆ i ∈ F, ‖bandOp (freqC lam i) g x‖ₑ) ^ (2:ℝ) ∂volume :=
      lintegral_mono (fun x => ENNReal.rpow_le_rpow (hsup x) (by norm_num))
    rw [lintegral_iSup_finset_enorm_eq_ofReal J'' _
          (memLp_iSup_bandOp J'' C hCmeas hCbd g hg1 hg2),
        lintegral_iSup_finset_enorm_eq_ofReal F _
          (memLp_iSup_bandOp F (freqC lam) (measurableSet_freqC lam) (isBounded_freqC lam) g hg1 hg2),
        integral_rpow_two_eq_sq (fun x => ⨆ i ∈ J'', ‖bandOp (C i) g x‖),
        integral_rpow_two_eq_sq (fun x => ⨆ i ∈ F, ‖bandOp (freqC lam i) g x‖)] at h1
    have h2 : ∫ x : ℝ, (⨆ i ∈ J'', ‖bandOp (C i) g x‖) ^ 2
        ≤ ∫ x : ℝ, (⨆ i ∈ F, ‖bandOp (freqC lam i) g x‖) ^ 2 :=
      (ENNReal.ofReal_le_ofReal_iff
        (integral_nonneg (fun x => sq_nonneg (⨆ i ∈ F, ‖bandOp (freqC lam i) g x‖)))).mp h1
    calc Real.sqrt (∫ x : ℝ, (⨆ i ∈ J'', ‖bandOp (C i) g x‖) ^ 2)
        ≤ Real.sqrt (∫ x : ℝ, (⨆ i ∈ F, ‖bandOp (freqC lam i) g x‖) ^ 2) :=
          Real.sqrt_le_sqrt h2
      _ ≤ B * Real.sqrt (∫ x : ℝ, ‖g x‖ ^ 2) :=
          block_maximal_real lam B (le_of_lt hB) hmax r g hg1 hg2 J''
  have h := bandOp_dual_of_maximal C hCmeas hCbd B (le_of_lt hB) hCmax
    (J.filter (fun j => blockIndex lam j = r)) u
    (fun j hj => hu1 j (Finset.mem_filter.mp hj).1)
    (fun j hj => hu2 j (Finset.mem_filter.mp hj).1)
    (fun i hi j hj hij x => hdisj i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij x)
  have hsum : ∀ x : ℝ, (∑ j ∈ J.filter (fun j => blockIndex lam j = r),
        bandOp (freqC lam j) (u j) x)
      = ∑ j ∈ J.filter (fun j => blockIndex lam j = r), bandOp (C j) (u j) x := by
    intro x
    exact Finset.sum_congr rfl (fun i hi => by rw [hCeq i (Finset.mem_filter.mp hi).2])
  have hInt : ∫ x : ℝ, ‖∑ j ∈ J.filter (fun j => blockIndex lam j = r),
        bandOp (freqC lam j) (u j) x‖ ^ 2
      = ∫ x : ℝ, ‖∑ j ∈ J.filter (fun j => blockIndex lam j = r),
        bandOp (C j) (u j) x‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    change ‖(∑ j ∈ J.filter (fun j => blockIndex lam j = r), bandOp (freqC lam j) (u j) x)‖ ^ 2
      = ‖(∑ j ∈ J.filter (fun j => blockIndex lam j = r), bandOp (C j) (u j) x)‖ ^ 2
    rw [hsum x]
  rw [show Real.sqrt (∫ x : ℝ, ‖∑ j ∈ J.filter (fun j => blockIndex lam j = r),
        bandOp (freqC lam j) (u j) x‖ ^ 2)
      = Real.sqrt (∫ x : ℝ, ‖∑ j ∈ J.filter (fun j => blockIndex lam j = r),
        bandOp (C j) (u j) x‖ ^ 2) from by rw [hInt]]
  exact h

/-- The neighbourhoods shrink as the scale grows. -/
lemma neigh_anti {K : ℕ} {lam : Fin K → ℝ} {i j : ℕ} (h : i ≤ j) : neigh lam j ⊆ neigh lam i :=
  fun θ hθ => by
    obtain ⟨k, hk⟩ := hθ
    exact ⟨k, le_trans hk (dyadic_anti h)⟩

/-- The number bounding all block indices. -/
noncomputable def blockBound (K : ℕ) : ℕ := K * K * (Nat.log2 K + 1) + K + 1

lemma blockIndex_lt_blockBound {K : ℕ} (lam : Fin K → ℝ) (j : ℕ) :
    blockIndex lam j < blockBound K := by
  have h := blockIndex_le lam j
  simp only [blockBound]
  omega

/-- The Plancherel pairing for the Fourier transform on the line, used for the orthogonality of
the blocks. -/
lemma integral_fourier_mul_star_eq {f g : ℝ → ℂ} (hf1 : Integrable f) (hg1 : Integrable g)
    (hf2 : MemLp f 2 (volume : Measure ℝ)) (hg2 : MemLp g 2 (volume : Measure ℝ)) :
    ∫ a : ℝ, (𝓕 f) a * star ((𝓕 g) a) = ∫ x : ℝ, f x * star (g x) := by
  set F := hf2.toLp f with hF
  set G := hg2.toLp g with hG
  have hFG : inner ℂ G F = ∫ x : ℝ, f x * star (g x) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp, hg2.coeFn_toLp] with x hxF hxG
    rw [hxF, hxG, RCLike.inner_apply', starRingEnd_apply]
    ring
  have h2 : (∫ a : ℝ, (𝓕 f) a * star ((𝓕 g) a)) = inner ℂ (𝓕 G) (𝓕 F) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [fourier_toLp_ae_eq_fourier_of_memLp (memLp_one_iff_integrable.mpr hf1) hf2,
      fourier_toLp_ae_eq_fourier_of_memLp (memLp_one_iff_integrable.mpr hg1) hg2] with a haF haG
    rw [haF, haG, RCLike.inner_apply', starRingEnd_apply]
    ring
  exact h2.trans (by rw [Lp.inner_fourier_eq, hFG])

/-- **Steps C–D: dual recombination over the blocks.**  Given the per-block maximal estimate with
constant `B`, the dual bound for the *whole* family of band-pass operators holds with constant
`B + log₂ M + 1`. -/
lemma blockIndex_dual_recombination {K : ℕ} (lam : Fin K → ℝ) (B : ℝ) (hB : 0 < B)
    (hmax : ∀ (r : ℕ) (J : Finset ℕ), (∀ j ∈ J, blockIndex lam j = r) →
      ∀ (g : ℝ → ℂ), Integrable g → MemLp g 2 →
        ∫⁻ x : ℝ, (⨆ j ∈ J, ‖bandOp (freqC lam j) g x‖ₑ) ^ (2:ℝ)
          ≤ ENNReal.ofReal (B ^ 2) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ)) :
    ∀ (J : Finset ℕ) (u : ℕ → ℝ → ℂ),
      (∀ j ∈ J, MemLp (u j) 1 (volume : Measure ℝ)) →
      (∀ j ∈ J, MemLp (u j) 2 (volume : Measure ℝ)) →
      (∀ j ∈ J, ∀ k ∈ J, j ≠ k → ∀ x : ℝ, u j x * star (u k x) = 0) →
      Real.sqrt (∫ x : ℝ, ‖∑ j ∈ J, bandOp (freqC lam j) (u j) x‖ ^ 2)
        ≤ (B + (Nat.log2 (blockBound K) : ℝ) + 1)
            * Real.sqrt (∑ j ∈ J, ∫ x : ℝ, ‖u j x‖ ^ 2) := by
  intro J u hu1 hu2 hdisj
  classical
  set M : ℕ := blockBound K with hMdef
  have hDnn : 0 ≤ B + (Nat.log2 M : ℝ) + 1 := by positivity
  have hDpos : 0 < B + (Nat.log2 M : ℝ) + 1 := by positivity
  set V : ℕ → ℝ → ℂ := fun j => if j ∈ J then 𝓕 (u j) else 0 with hVdef
  have hVJ : ∀ j ∈ J, V j = 𝓕 (u j) := fun j hj => by rw [hVdef]; exact if_pos hj
  have hVout : ∀ j, j ∉ J → V j = 0 := fun j hj => by rw [hVdef]; exact if_neg hj
  have hVmem : ∀ j ∈ J, MemLp (V j) 2 (volume : Measure ℝ) := fun j hj => by
    rw [hVJ j hj]
    exact memLp_fourier (memLp_one_iff_integrable.mp (hu1 j hj)) (hu2 j hj)
  have horth : ∀ i j, i ≠ j → ∫ a : ℝ, V i a * star (V j a) = 0 := by
    intro i j hij
    by_cases hi : i ∈ J
    · by_cases hj : j ∈ J
      · rw [hVJ i hi, hVJ j hj]
        rw [integral_fourier_mul_star_eq (memLp_one_iff_integrable.mp (hu1 i hi))
          (memLp_one_iff_integrable.mp (hu1 j hj)) (hu2 i hi) (hu2 j hj)]
        exact integral_eq_zero_of_ae (Filter.Eventually.of_forall (fun x => hdisj i hi j hj hij x))
      · rw [hVout j hj]; simp
    · rw [hVout i hi]; simp
  have hsum_memLp : MemLp (fun a : ℝ => ∑ j ∈ J, bandOp (freqC lam j) (u j) a) 2
      (volume : Measure ℝ) :=
    memLp_finsetSum J (fun j hj => bandOp_memLp (freqC lam j) (measurableSet_freqC lam j)
      (isBounded_freqC lam j) (u j) (memLp_one_iff_integrable.mp (hu1 j hj)) (hu2 j hj))
  have hL : ∫⁻ a : ℝ, ‖∑ j ∈ J, Set.indicator (freqC lam j) (V j) a‖ₑ ^ (2:ℝ)
      = ∫⁻ a : ℝ, ‖∑ j ∈ J, bandOp (freqC lam j) (u j) a‖ₑ ^ (2:ℝ) := by
    rw [show (fun a : ℝ => ‖∑ j ∈ J, Set.indicator (freqC lam j) (V j) a‖ₑ ^ (2:ℝ))
        = fun a : ℝ => ‖∑ j ∈ J, Set.indicator (freqC lam j) (𝓕 (u j)) a‖ₑ ^ (2:ℝ) from by
      funext a
      congr 2
      exact Finset.sum_congr rfl (fun j hj => by rw [hVJ j hj])]
    exact (lintegral_bandOp_sum_eq_indicator_sum J (freqC lam) (measurableSet_freqC lam)
      (isBounded_freqC lam) u hu1 hu2).symm
  have hR : ∑ j ∈ J, ∫⁻ a : ℝ, ‖V j a‖ₑ ^ (2:ℝ)
      = ENNReal.ofReal (∑ j ∈ J, ∫ x : ℝ, ‖u j x‖ ^ 2) := by
    have hterm : ∀ j ∈ J, ∫⁻ a : ℝ, ‖V j a‖ₑ ^ (2:ℝ)
        = ENNReal.ofReal (∫ x : ℝ, ‖u j x‖ ^ 2) := by
      intro j hj
      rw [hVJ j hj, lintegral_enorm_fourier_eq (memLp_one_iff_integrable.mp (hu1 j hj)) (hu2 j hj),
        NestedIndicator.lintegral_enorm_rpow_two volume (hu2 j hj)]
      congr 1
      exact integral_rpow_two_eq_sq (fun x => ‖u j x‖)
    exact (Finset.sum_congr rfl hterm).trans
      (ENNReal.ofReal_sum_of_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))).symm
  have hblock : ∀ r : ℕ, r < M →
      ∫⁻ a : ℝ, ‖∑ j ∈ J.filter (fun j => blockIndex lam j = r),
          Set.indicator (freqC lam j) (V j) a‖ₑ ^ (2:ℝ)
        ≤ ENNReal.ofReal (B ^ 2) * ∑ j ∈ J.filter (fun j => blockIndex lam j = r),
            ∫⁻ a : ℝ, ‖V j a‖ₑ ^ (2:ℝ) := by
    intro r hr
    set Jr : Finset ℕ := J.filter (fun j => blockIndex lam j = r) with hJrdef
    have hJrJ : ∀ j ∈ Jr, j ∈ J := fun j hj => (Finset.mem_filter.mp hj).1
    have hsum_memLp_r : MemLp (fun a : ℝ => ∑ j ∈ Jr, bandOp (freqC lam j) (u j) a) 2
        (volume : Measure ℝ) :=
      memLp_finsetSum Jr (fun j hj => bandOp_memLp (freqC lam j) (measurableSet_freqC lam j)
        (isBounded_freqC lam j) (u j) (memLp_one_iff_integrable.mp (hu1 j (hJrJ j hj)))
        (hu2 j (hJrJ j hj)))
    have hLr : ∫⁻ a : ℝ, ‖∑ j ∈ Jr, Set.indicator (freqC lam j) (V j) a‖ₑ ^ (2:ℝ)
        = ∫⁻ a : ℝ, ‖∑ j ∈ Jr, bandOp (freqC lam j) (u j) a‖ₑ ^ (2:ℝ) := by
      rw [show (fun a : ℝ => ‖∑ j ∈ Jr, Set.indicator (freqC lam j) (V j) a‖ₑ ^ (2:ℝ))
          = fun a : ℝ => ‖∑ j ∈ Jr, Set.indicator (freqC lam j) (𝓕 (u j)) a‖ₑ ^ (2:ℝ) from by
        funext a
        congr 2
        exact Finset.sum_congr rfl (fun j hj => by rw [hVJ j (hJrJ j hj)])]
      exact (lintegral_bandOp_sum_eq_indicator_sum Jr (freqC lam) (measurableSet_freqC lam)
        (isBounded_freqC lam) u (fun j hj => hu1 j (hJrJ j hj))
        (fun j hj => hu2 j (hJrJ j hj))).symm
    have hRr : ∑ j ∈ Jr, ∫⁻ a : ℝ, ‖V j a‖ₑ ^ (2:ℝ)
        = ENNReal.ofReal (∑ j ∈ Jr, ∫ x : ℝ, ‖u j x‖ ^ 2) := by
      have hterm : ∀ j ∈ Jr, ∫⁻ a : ℝ, ‖V j a‖ₑ ^ (2:ℝ)
          = ENNReal.ofReal (∫ x : ℝ, ‖u j x‖ ^ 2) := by
        intro j hj
        rw [hVJ j (hJrJ j hj),
          lintegral_enorm_fourier_eq (memLp_one_iff_integrable.mp (hu1 j (hJrJ j hj)))
            (hu2 j (hJrJ j hj)), NestedIndicator.lintegral_enorm_rpow_two volume (hu2 j (hJrJ j hj))]
        congr 1
        exact integral_rpow_two_eq_sq (fun x => ‖u j x‖)
      exact (Finset.sum_congr rfl hterm).trans
        (ENNReal.ofReal_sum_of_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))).symm
    have hdualb := blockIndex_dual lam B hB hmax r J u hu1 hu2 hdisj
    have hsqr : ∫ x : ℝ, ‖∑ j ∈ Jr, bandOp (freqC lam j) (u j) x‖ ^ 2
        ≤ B ^ 2 * ∑ j ∈ Jr, ∫ x : ℝ, ‖u j x‖ ^ 2 := by
      have hA : (0:ℝ) ≤ ∫ x : ℝ, ‖∑ j ∈ Jr, bandOp (freqC lam j) (u j) x‖ ^ 2 :=
        integral_nonneg (fun x => sq_nonneg _)
      have hS : (0:ℝ) ≤ ∑ j ∈ Jr, ∫ x : ℝ, ‖u j x‖ ^ 2 :=
        Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))
      have h3 : Real.sqrt (∫ x : ℝ, ‖∑ j ∈ Jr, bandOp (freqC lam j) (u j) x‖ ^ 2) ^ 2
          ≤ (B * Real.sqrt (∑ j ∈ Jr, ∫ x : ℝ, ‖u j x‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) hdualb 2
      rwa [Real.sq_sqrt hA, mul_pow, Real.sq_sqrt hS] at h3
    rw [hLr, hRr,
      NestedIndicator.lintegral_enorm_rpow_two volume hsum_memLp_r,
      integral_rpow_two_eq_sq (fun a => ‖∑ j ∈ Jr, bandOp (freqC lam j) (u j) a‖),
      ← ENNReal.ofReal_mul (sq_nonneg B)]
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg B)
      (Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))))).mpr hsqr
  have hnest : ∀ i j : ℕ, i ≤ j → freqC lam j ⊆ freqC lam i :=
    fun i j hij => freqOf_mono (neigh_anti hij)
  have hbmono : ∀ i ∈ J, ∀ j ∈ J, i ≤ j → blockIndex lam i ≤ blockIndex lam j :=
    fun i _ j _ hij => blockIndex_mono lam hij
  have hbM : ∀ j ∈ J, blockIndex lam j < M := fun j _ => by rw [hMdef]; exact blockIndex_lt_blockBound lam j
  have hrec := block_dual_recombination (volume : Measure ℝ) (fun j => freqC lam j) V J
    (blockIndex lam) M B (fun j => measurableSet_freqC lam j) hnest hbmono hbM hVmem hVout horth
    (le_of_lt hB) hblock
  have h1 := hrec
  rw [hL, hR, ← ENNReal.ofReal_mul (sq_nonneg (B + (Nat.log2 M : ℝ) + 1))] at h1
  rw [NestedIndicator.lintegral_enorm_rpow_two volume hsum_memLp,
    integral_rpow_two_eq_sq (fun a => ‖∑ j ∈ J, bandOp (freqC lam j) (u j) a‖)] at h1
  have hsq : ∫ x : ℝ, ‖∑ j ∈ J, bandOp (freqC lam j) (u j) x‖ ^ 2
      ≤ (B + (Nat.log2 M : ℝ) + 1) ^ 2 * ∑ j ∈ J, ∫ x : ℝ, ‖u j x‖ ^ 2 :=
    (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg (fun j _ => integral_nonneg (fun x => sq_nonneg _))))).mp h1
  have hDnn' : 0 ≤ B + (Nat.log2 M : ℝ) + 1 := by positivity
  calc Real.sqrt (∫ x : ℝ, ‖∑ j ∈ J, bandOp (freqC lam j) (u j) x‖ ^ 2)
      ≤ Real.sqrt ((B + (Nat.log2 M : ℝ) + 1) ^ 2 * ∑ j ∈ J, ∫ x : ℝ, ‖u j x‖ ^ 2) :=
        Real.sqrt_le_sqrt hsq
    _ = (B + (Nat.log2 M : ℝ) + 1) * Real.sqrt (∑ j ∈ J, ∫ x : ℝ, ‖u j x‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hDnn']

/-- **The dual estimate extends from `L¹ ∩ L²` weights to `L²` weights.**  If for every finite
family of `L¹ ∩ L²` functions with pairwise disjoint supports the dual bound holds, then the same
holds for every finite family of merely `L²` functions with pairwise disjoint supports: for a
non-integrable `u j` we have `bandOp (C j) (u j) = 0` identically, so the corresponding summands
may be dropped. -/
lemma bandOp_dual_of_maximal_L2 {ι : Type*} (C : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (C i)) (hbd : ∀ i, Bornology.IsBounded (C i))
    (B : ℝ) (hB : 0 ≤ B)
    (hdual : ∀ (J : Finset ι) (u : ι → ℝ → ℂ),
      (∀ j ∈ J, MemLp (u j) 1 (volume : Measure ℝ)) →
      (∀ j ∈ J, MemLp (u j) 2 (volume : Measure ℝ)) →
      (∀ j ∈ J, ∀ k ∈ J, j ≠ k → ∀ x : ℝ, u j x * star (u k x) = 0) →
      Real.sqrt (∫ x : ℝ, ‖∑ j ∈ J, bandOp (C j) (u j) x‖ ^ 2)
        ≤ B * Real.sqrt (∑ j ∈ J, ∫ x : ℝ, ‖u j x‖ ^ 2)) :
    ∀ (J : Finset ι) (u : ι → ℝ → ℂ),
      (∀ j ∈ J, MemLp (u j) 2 (volume : Measure ℝ)) →
      (∀ j ∈ J, ∀ k ∈ J, j ≠ k → ∀ x : ℝ, u j x * star (u k x) = 0) →
      Real.sqrt (∫ x : ℝ, ‖∑ j ∈ J, bandOp (C j) (u j) x‖ ^ 2)
        ≤ B * Real.sqrt (∑ j ∈ J, ∫ x : ℝ, ‖u j x‖ ^ 2) := by
  intro J u hu2 hdisj
  classical
  set J₁ : Finset ι := J.filter (fun j => Integrable (u j) (volume : Measure ℝ)) with hJ₁def
  set u' : ι → ℝ → ℂ := fun j => if j ∈ J₁ then u j else 0 with hu'def
  have hu'val : ∀ j ∈ J₁, u' j = u j := fun j hj => by rw [hu'def]; exact if_pos hj
  have hJ₁J : ∀ j ∈ J₁, j ∈ J := fun j hj => (Finset.mem_filter.mp hj).1
  have hu'1 : ∀ j ∈ J₁, MemLp (u' j) 1 (volume : Measure ℝ) := fun j hj => by
    rw [hu'val j hj]; exact memLp_one_iff_integrable.mpr (Finset.mem_filter.mp hj).2
  have hu'2 : ∀ j ∈ J₁, MemLp (u' j) 2 (volume : Measure ℝ) := fun j hj => by
    rw [hu'val j hj]; exact hu2 j (hJ₁J j hj)
  have hdisj' : ∀ j ∈ J₁, ∀ k ∈ J₁, j ≠ k → ∀ x : ℝ, u' j x * star (u' k x) = 0 := by
    intro j hj k hk hjk x
    rw [hu'val j hj, hu'val k hk]
    exact hdisj j (hJ₁J j hj) k (hJ₁J k hk) hjk x
  have h := hdual J₁ u' hu'1 hu'2 hdisj'
  have hsum1 : ∀ x : ℝ, (∑ j ∈ J, bandOp (C j) (u j) x)
      = ∑ j ∈ J₁, bandOp (C j) (u j) x := by
    intro x
    refine (Finset.sum_subset (s₁ := J₁) (s₂ := J) (f := fun j => bandOp (C j) (u j) x)
      (Finset.filter_subset _ _) ?_).symm
    intro j hjJ hjnJ₁
    rw [bandOp_eq_zero_of_not_integrable (C := C j)
      (fun hint => hjnJ₁ (Finset.mem_filter.mpr ⟨hjJ, hint⟩))]
    simp
  have hsum2 : ∀ x : ℝ, (∑ j ∈ J₁, bandOp (C j) (u j) x)
      = ∑ j ∈ J₁, bandOp (C j) (u' j) x := by
    intro x
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [hu'val j hj]
  have hInt : ∫ x : ℝ, ‖∑ j ∈ J, bandOp (C j) (u j) x‖ ^ 2
      = ∫ x : ℝ, ‖∑ j ∈ J₁, bandOp (C j) (u' j) x‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    change ‖(∑ j ∈ J, bandOp (C j) (u j) x)‖ ^ 2 = ‖(∑ j ∈ J₁, bandOp (C j) (u' j) x)‖ ^ 2
    rw [hsum1 x, hsum2 x]
  have hS : (∑ j ∈ J₁, ∫ x : ℝ, ‖u' j x‖ ^ 2) ≤ ∑ j ∈ J, ∫ x : ℝ, ‖u j x‖ ^ 2 := by
    calc ∑ j ∈ J₁, ∫ x : ℝ, ‖u' j x‖ ^ 2
        = ∑ j ∈ J₁, ∫ x : ℝ, ‖u j x‖ ^ 2 :=
          Finset.sum_congr rfl (fun j hj => by rw [hu'val j hj])
      _ ≤ ∑ j ∈ J, ∫ x : ℝ, ‖u j x‖ ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => integral_nonneg (fun x => sq_nonneg _))
  rw [hInt]
  exact le_trans h (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hS) hB)

/-- **Steps B–F assembled.**  The maximal estimate for the iterated-integral operators
`itOp (neigh lam j)`, for `f ∈ L¹ ∩ L²`. -/
lemma itOp_maximal_l1l2_of_separated {K : ℕ} (lam : Fin K → ℝ) (C' : ℝ) (hC'pos : 0 < C')
    (hC'max : BlockMaximal C') :
    ∀ (f : ℝ → ℂ), Integrable f → MemLp f 2 →
      ∫⁻ x : ℝ, (⨆ j : ℕ, ‖itOp (neigh lam j) f x‖ₑ) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((2 * Real.pi * (10 * (1 + C' * (Real.log ((K:ℝ)+2))^2)
              + (Nat.log2 (blockBound K) : ℝ) + 1)) ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
  have hmax := blockIndex_maximal_enn lam C' hC'pos hC'max
  set B : ℝ := 10 * (1 + C' * (Real.log ((K:ℝ)+2))^2) with hBdef
  have hBpos : 0 < B := by rw [hBdef]; positivity
  set D : ℝ := B + (Nat.log2 (blockBound K) : ℝ) + 1 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; positivity
  intro f hf1 hf2
  have hdualL : ∀ (J : Finset ℕ) (u : ℕ → ℝ → ℂ),
      (∀ j ∈ J, MemLp (u j) 1 (volume : Measure ℝ)) →
      (∀ j ∈ J, MemLp (u j) 2 (volume : Measure ℝ)) →
      (∀ j ∈ J, ∀ k ∈ J, j ≠ k → ∀ x : ℝ, u j x * star (u k x) = 0) →
      Real.sqrt (∫ x : ℝ, ‖∑ j ∈ J, bandOp (freqC lam j) (u j) x‖ ^ 2)
        ≤ D * Real.sqrt (∑ j ∈ J, ∫ x : ℝ, ‖u j x‖ ^ 2) := by
    intro J u hu1 hu2 hdisj
    have h := blockIndex_dual_recombination lam B hBpos hmax J u hu1 hu2 hdisj
    rwa [hDdef]
  have hdualL2 := bandOp_dual_of_maximal_L2 (fun j => freqC lam j) (measurableSet_freqC lam)
    (isBounded_freqC lam) D (le_of_lt hDpos) hdualL
  have hband := bandOp_maximal_l2_of_dual D (le_of_lt hDpos) (fun j => freqC lam j)
    (measurableSet_freqC lam) (isBounded_freqC lam) hdualL2 f hf1 hf2
  have h2π : ‖((2 : ℂ) * (Real.pi : ℂ))‖ₑ = ENNReal.ofReal (2 * Real.pi) := by
    rw [enorm_mul, enorm_eq_ofReal_norm, enorm_eq_ofReal_norm, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hpt : ∀ x : ℝ, (⨆ j : ℕ, ‖itOp (neigh lam j) f x‖ₑ)
      = ENNReal.ofReal (2 * Real.pi) * (⨆ j : ℕ, ‖bandOp (freqC lam j) f x‖ₑ) := by
    intro x
    have hfun : ∀ j : ℕ, ‖itOp (neigh lam j) f x‖ₑ
        = ENNReal.ofReal (2 * Real.pi) * ‖bandOp (freqC lam j) f x‖ₑ := by
      intro j
      have hb : itOp (neigh lam j) f x = (2 * (Real.pi : ℂ)) * bandOp (freqC lam j) f x :=
        itOp_eq_bandOp (neigh lam j) (measurableSet_neigh lam j) (isBounded_neigh lam j)
          f (memLp_one_iff_integrable.mpr hf1) hf2 x
      rw [hb, enorm_mul, h2π]
    calc (⨆ j : ℕ, ‖itOp (neigh lam j) f x‖ₑ)
        = ⨆ j : ℕ, ENNReal.ofReal (2 * Real.pi) * ‖bandOp (freqC lam j) f x‖ₑ :=
          iSup_congr hfun
      _ = ENNReal.ofReal (2 * Real.pi) * ⨆ j : ℕ, ‖bandOp (freqC lam j) f x‖ₑ :=
          (ENNReal.mul_iSup _ _).symm
  have hfin : ∫⁻ x : ℝ, (⨆ j : ℕ, ‖itOp (neigh lam j) f x‖ₑ) ^ (2:ℝ)
      ≤ ENNReal.ofReal ((2 * Real.pi * D) ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
    have h2πsq : ENNReal.ofReal (2 * Real.pi) ^ (2:ℝ)
        = ENNReal.ofReal ((2 * Real.pi) ^ 2) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity : (0:ℝ) ≤ 2 * Real.pi)
          (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_two]
    have hmeasX : Measurable (fun x : ℝ =>
        (⨆ j : ℕ, ‖bandOp (freqC lam j) f x‖ₑ) ^ (2:ℝ)) :=
      measurable_sq_enn (Measurable.iSup (fun j => (bandOp_cont (freqC lam j)
        (measurableSet_freqC lam j) (isBounded_freqC lam j) f hf1).measurable.enorm))
    have hstep : ∫⁻ x : ℝ, (⨆ j : ℕ, ‖itOp (neigh lam j) f x‖ₑ) ^ (2:ℝ)
        = ENNReal.ofReal ((2 * Real.pi) ^ 2)
          * ∫⁻ x : ℝ, (⨆ j : ℕ, ‖bandOp (freqC lam j) f x‖ₑ) ^ (2:ℝ) := by
      rw [lintegral_congr (fun x => by rw [hpt x])]
      have h : ∀ x : ℝ, (ENNReal.ofReal (2 * Real.pi)
            * (⨆ j : ℕ, ‖bandOp (freqC lam j) f x‖ₑ)) ^ (2:ℝ)
          = ENNReal.ofReal ((2 * Real.pi) ^ 2)
            * (⨆ j : ℕ, ‖bandOp (freqC lam j) f x‖ₑ) ^ (2:ℝ) := by
        intro x
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 2), h2πsq]
      rw [lintegral_congr h, lintegral_const_mul _ hmeasX]
    calc ∫⁻ x : ℝ, (⨆ j : ℕ, ‖itOp (neigh lam j) f x‖ₑ) ^ (2:ℝ)
        = ENNReal.ofReal ((2 * Real.pi) ^ 2)
            * ∫⁻ x : ℝ, (⨆ j : ℕ, ‖bandOp (freqC lam j) f x‖ₑ) ^ (2:ℝ) := hstep
      _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 2)
            * (ENNReal.ofReal (D ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ)) :=
          mul_le_mul' le_rfl hband
      _ = ENNReal.ofReal ((2 * Real.pi * D) ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg (2 * Real.pi)),
            show (2 * Real.pi) ^ 2 * D ^ 2 = (2 * Real.pi * D) ^ 2 by ring]
  exact hfin

/-- **Step G: extension to `f ∈ L²`.**  Every square-integrable function satisfies the maximal
estimate for the iterated-integral operators with the same constant. -/
lemma itOp_maximal_l2_of_separated {K : ℕ} (lam : Fin K → ℝ) (C' : ℝ) (hC'pos : 0 < C')
    (hC'max : BlockMaximal C') :
    ∀ (f : ℝ → ℂ) (hf : MemLp f 2 (volume : Measure ℝ)),
      ∫⁻ x : ℝ, (⨆ j : ℕ, ‖itOp (neigh lam j) f x‖ₑ) ^ (2:ℝ)
        ≤ ENNReal.ofReal ((2 * Real.pi * (10 * (1 + C' * (Real.log ((K:ℝ)+2))^2)
              + (Nat.log2 (blockBound K) : ℝ) + 1)) ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
  classical
  have hl1l2 := itOp_maximal_l1l2_of_separated lam C' hC'pos hC'max
  intro f hf
  set E : ℝ := 2 * Real.pi * (10 * (1 + C' * (Real.log ((K:ℝ)+2))^2)
      + (Nat.log2 (blockBound K) : ℝ) + 1) with hEdef
  set g : ℝ → ℂ := hf.aestronglyMeasurable.mk f with hgdef
  have hgm : StronglyMeasurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hae : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hgmem : MemLp g 2 (volume : Measure ℝ) :=
    hf.congr_norm hgm.aestronglyMeasurable (hae.mono (fun y hy => by rw [hy]))
  set T : ℕ → Set ℝ := fun n => {y : ℝ | ‖g y‖ ≤ (n:ℝ)} ∩ {y : ℝ | |y| ≤ (n:ℝ)} with hTdef
  set fn : ℕ → ℝ → ℂ := fun n => Set.indicator (T n) g with hfndef
  have hTmeas : ∀ n, MeasurableSet (T n) := fun n =>
    (measurableSet_le hgm.measurable.norm measurable_const).inter
      (measurableSet_le continuous_abs.measurable measurable_const)
  have hfn_meas : ∀ n, Measurable (fn n) := fun n =>
    Measurable.ite (hTmeas n) hgm.measurable measurable_const
  have hfn_le : ∀ n y, ‖fn n y‖ ≤ ‖g y‖ := by
    intro n y
    show ‖Set.indicator (T n) g y‖ ≤ ‖g y‖
    by_cases h : y ∈ T n
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h, norm_zero]; positivity
  have hfn_tend : ∀ y, Tendsto (fun n => fn n y) atTop (𝓝 (g y)) := by
    intro y
    have h1 : ∀ᶠ n : ℕ in atTop, ‖g y‖ ≤ (n:ℝ) := by
      filter_upwards [eventually_ge_atTop ⌈‖g y‖⌉₊] with n hn
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have h2 : ∀ᶠ n : ℕ in atTop, |y| ≤ (n:ℝ) := by
      filter_upwards [eventually_ge_atTop ⌈|y|⌉₊] with n hn
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have h3 : ∀ᶠ n : ℕ in atTop, g y = fn n y := by
      filter_upwards [h1, h2] with n h1n h2n
      show g y = Set.indicator (T n) g y
      exact (Set.indicator_of_mem (s := T n) (show y ∈ T n from ⟨h1n, h2n⟩) g).symm
    exact tendsto_const_nhds.congr' h3
  have hfn_mem : ∀ n, MemLp (fn n) 2 (volume : Measure ℝ) := by
    intro n
    refine MemLp.of_le hgmem.norm (hfn_meas n).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hfn_le n y
  have hfn_int : ∀ n, Integrable (fn n) := by
    intro n
    have hfin : volume (Set.Icc (-(n:ℝ)) (n:ℝ)) < ⊤ := by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    have hdom : Integrable (fun y : ℝ =>
        (n:ℝ) * (Set.Icc (-(n:ℝ)) (n:ℝ)).indicator (fun _ => (1:ℝ)) y) volume :=
      ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const hfin.ne)).const_mul (n:ℝ)
    refine Integrable.mono' hdom (hfn_meas n).aestronglyMeasurable ?_
    filter_upwards with y
    show ‖Set.indicator (T n) g y‖ ≤
      (n:ℝ) * (Set.Icc (-(n:ℝ)) (n:ℝ)).indicator (fun _ => (1:ℝ)) y
    by_cases h : y ∈ T n
    · rw [Set.indicator_of_mem h]
      have hy : y ∈ Set.Icc (-(n:ℝ)) (n:ℝ) := by rw [Set.mem_Icc, ← abs_le]; exact h.2
      rw [Set.indicator_of_mem hy]; simpa using h.1
    · rw [Set.indicator_of_notMem h, norm_zero]
      have hnn : (0:ℝ) ≤ (n:ℝ) * (Set.Icc (-(n:ℝ)) (n:ℝ)).indicator (fun _ => (1:ℝ)) y :=
        mul_nonneg (by positivity) (Set.indicator_nonneg (fun _ _ => zero_le_one) y)
      linarith
  set u : ℕ → ℝ → ℝ≥0∞ := fun n x => ⨆ j : ℕ, ‖itOp (neigh lam j) (fn n) x‖ₑ with hudef
  set b : ℝ → ℝ≥0∞ := fun x => ⨆ j : ℕ, ‖itOp (neigh lam j) g x‖ₑ with hbdef
  have hu_meas : ∀ n, AEMeasurable (fun x : ℝ => (u n x) ^ (2:ℝ)) volume := by
    intro n
    exact (measurable_sq_enn (Measurable.iSup (fun j : ℕ =>
      (continuous_itOp (measurableSet_neigh lam j) (isBounded_neigh lam j) (fn n)
        (memLp_one_iff_integrable.mpr (hfn_int n)) (hfn_mem n)).measurable.enorm))).aemeasurable
  have hlim : ∀ x : ℝ, b x ≤ Filter.liminf (fun n => u n x) Filter.atTop := by
    intro x
    rw [hbdef]
    refine iSup_le (fun j => ?_)
    set K' : ℝ → ℂ := fun y => itKer (neigh lam j) (x - y) with hK'def
    have hKmem : MemLp K' 2 (volume : Measure ℝ) :=
      memLp_itKer_shift (neigh lam j) (measurableSet_neigh lam j) (isBounded_neigh lam j) x
    have hbnd_int : Integrable (fun y : ℝ => ‖g y‖ * ‖K' y‖) volume :=
      MemLp.integrable_mul hgmem.norm hKmem.norm
    have hconv : Tendsto (fun n => ∫ y : ℝ, fn n y * K' y) atTop (𝓝 (∫ y : ℝ, g y * K' y)) := by
      refine tendsto_integral_of_dominated_convergence (fun y : ℝ => ‖g y‖ * ‖K' y‖)
        (fun n => (hfn_meas n).aestronglyMeasurable.mul hKmem.aestronglyMeasurable)
        hbnd_int (fun n => ?_) ?_
      · filter_upwards with y
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hfn_le n y) (norm_nonneg _)
      · filter_upwards with y
        exact (hfn_tend y).mul_const (K' y)
    have hlimE : Tendsto (fun n => ‖∫ y : ℝ, fn n y * K' y‖ₑ) atTop
        (𝓝 (‖∫ y : ℝ, g y * K' y‖ₑ)) := by
      have hnorm : Tendsto (fun n => ‖∫ y : ℝ, fn n y * K' y‖) atTop
          (𝓝 ‖∫ y : ℝ, g y * K' y‖) := hconv.norm
      simp only [enorm_eq_ofReal_norm]
      exact (ENNReal.continuous_ofReal.tendsto _).comp hnorm
    rw [show ‖itOp (neigh lam j) g x‖ₑ = ‖∫ y : ℝ, g y * K' y‖ₑ from rfl, ← hlimE.liminf_eq]
    exact Filter.liminf_le_liminf
      (Filter.Eventually.of_forall (fun n =>
        le_iSup (fun j : ℕ => ‖itOp (neigh lam j) (fn n) x‖ₑ) j))
  have hFatou : ∫⁻ x : ℝ, (b x) ^ (2:ℝ)
      ≤ Filter.liminf (fun n => ∫⁻ x : ℝ, (u n x) ^ (2:ℝ)) Filter.atTop := by
    refine le_trans ?_ (MeasureTheory.lintegral_liminf_le' (μ := volume)
      (f := fun n x => (u n x) ^ (2:ℝ)) (u := Filter.atTop) (fun n => hu_meas n))
    refine lintegral_mono (fun x => ?_)
    exact le_trans (ENNReal.rpow_le_rpow (hlim x) (by norm_num))
      (sq_liminf_bound (fun n => u n x))
  have hbound_n : ∀ n, ∫⁻ x : ℝ, (u n x) ^ (2:ℝ)
      ≤ ENNReal.ofReal (E ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
    intro n
    have h1 : ∫⁻ x : ℝ, (u n x) ^ (2:ℝ)
        ≤ ENNReal.ofReal (E ^ 2) * ∫⁻ x : ℝ, ‖fn n x‖ₑ ^ (2:ℝ) :=
      hl1l2 (fn n) (hfn_int n) (hfn_mem n)
    calc ∫⁻ x : ℝ, (u n x) ^ (2:ℝ)
        ≤ ENNReal.ofReal (E ^ 2) * ∫⁻ x : ℝ, ‖fn n x‖ₑ ^ (2:ℝ) := h1
      _ ≤ ENNReal.ofReal (E ^ 2) * ∫⁻ x : ℝ, ‖g x‖ₑ ^ (2:ℝ) :=
          mul_le_mul' le_rfl (by
            refine lintegral_mono (fun x => ?_)
            refine ENNReal.rpow_le_rpow ?_ (by norm_num)
            rw [enorm_eq_ofReal_norm, enorm_eq_ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hfn_le n x))
      _ = ENNReal.ofReal (E ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
          congr 1
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with x hx
          rw [hx]
  have hKlim : Filter.liminf (fun n => ∫⁻ x : ℝ, (u n x) ^ (2:ℝ)) Filter.atTop
      ≤ ENNReal.ofReal (E ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
    have h2 := Filter.liminf_le_liminf (f := Filter.atTop)
      (v := fun n => ∫⁻ x : ℝ, (u n x) ^ (2:ℝ))
      (u := fun _ => ENNReal.ofReal (E ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ))
      (Filter.Eventually.of_forall hbound_n)
    rwa [Filter.liminf_const] at h2
  have hfg : ∀ x : ℝ, (⨆ j : ℕ, ‖itOp (neigh lam j) f x‖ₑ) = b x := by
    intro x
    refine iSup_congr (fun j => ?_)
    have hit : itOp (neigh lam j) f x = itOp (neigh lam j) g x := by
      show (∫ y : ℝ, f y * itKer (neigh lam j) (x - y))
          = ∫ y : ℝ, g y * itKer (neigh lam j) (x - y)
      refine integral_congr_ae (hae.mono (fun y hy => ?_))
      show f y * itKer (neigh lam j) (x - y) = g y * itKer (neigh lam j) (x - y)
      rw [hy]
    rw [hit]
  calc ∫⁻ x : ℝ, (⨆ j : ℕ, ‖itOp (neigh lam j) f x‖ₑ) ^ (2:ℝ)
      = ∫⁻ x : ℝ, (b x) ^ (2:ℝ) := lintegral_congr (fun x => by rw [hfg x])
    _ ≤ ENNReal.ofReal (E ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := le_trans hFatou hKlim

/-- The logarithm of `blockBound K` is bounded by `30 log((K:ℝ)+2)^2`. -/
lemma nat_log2_blockBound_le (K : ℕ) :
    (Nat.log2 (blockBound K) : ℝ) + 1 ≤ 30 * (Real.log ((K:ℝ)+2))^2 := by
  have hlog2half : (1:ℝ)/2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hKcast : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
  have hlogK : (1:ℝ)/2 ≤ Real.log ((K:ℝ)+2) :=
    le_trans hlog2half (Real.log_le_log (by norm_num : (0:ℝ) < 2) (by linarith))
  have hM2 : ((blockBound K : ℕ) : ℝ) + 2 ≤ ((K:ℝ)+3)^3 := by
    have h1 : (Nat.log2 K : ℝ) ≤ (K:ℝ) := by exact_mod_cast Nat.log2_le_self K
    have h2 : ((K * K * (Nat.log2 K + 1) + K + 1 : ℕ) : ℝ)
        = (K:ℝ)*(K:ℝ)*((Nat.log2 K : ℝ)+1) + (K:ℝ) + 1 := by push_cast; ring
    rw [blockBound, h2]
    nlinarith [h1, hKcast]
  have hlogM2 : Real.log (((blockBound K : ℕ) : ℝ) + 2) ≤ 6 * Real.log ((K:ℝ)+2) := by
    have hstep1 : Real.log (((blockBound K : ℕ) : ℝ) + 2) ≤ 3 * Real.log ((K:ℝ)+3) := by
      have h := Real.log_le_log (by positivity : (0:ℝ) < ((blockBound K : ℕ) : ℝ) + 2) hM2
      rw [Real.log_pow] at h
      norm_num at h
      exact h
    have hstep2 : Real.log ((K:ℝ)+3) ≤ 2 * Real.log ((K:ℝ)+2) := by
      have h3 : (K:ℝ)+3 ≤ ((K:ℝ)+2)^2 := by nlinarith [hKcast]
      calc Real.log ((K:ℝ)+3) ≤ Real.log (((K:ℝ)+2)^2) :=
            Real.log_le_log (by positivity) h3
        _ = 2 * Real.log ((K:ℝ)+2) := by rw [Real.log_pow]; norm_num
    calc Real.log (((blockBound K : ℕ) : ℝ) + 2) ≤ 3 * Real.log ((K:ℝ)+3) := hstep1
      _ ≤ 3 * (2 * Real.log ((K:ℝ)+2)) := mul_le_mul_of_nonneg_left hstep2 (by norm_num)
      _ = 6 * Real.log ((K:ℝ)+2) := by ring
  have hkey : (Nat.log2 (blockBound K) : ℝ) ≤ 2 * Real.log (((blockBound K : ℕ) : ℝ) + 2) := by
    rcases Nat.eq_zero_or_pos (blockBound K) with hM | hM
    · rw [hM, Nat.log2_zero, Nat.cast_zero]
      have h : (0:ℝ) < Real.log 2 := lt_of_lt_of_le (by norm_num) hlog2half
      have h2 : (0:ℝ) + 2 = 2 := by norm_num
      rw [h2]
      linarith
    · have hlog2M : (Nat.log2 (blockBound K) : ℝ) * Real.log 2
          ≤ Real.log ((blockBound K : ℕ) : ℝ) := by
        have h2 : ((2:ℝ) ^ (Nat.log2 (blockBound K))) ≤ ((blockBound K : ℕ) : ℝ) := by
          have h : 2 ^ Nat.log 2 (blockBound K) ≤ blockBound K := Nat.pow_log_le_self 2 (by omega)
          rw [← Nat.log2_eq_log_two] at h
          exact_mod_cast h
        have h3 := Real.log_le_log (by positivity) h2
        rwa [Real.log_pow] at h3
      have h4 : Real.log (((blockBound K : ℕ) : ℝ)) ≤ Real.log (((blockBound K : ℕ) : ℝ) + 2) :=
        Real.log_le_log (by positivity) (le_add_of_nonneg_right (by norm_num : (0:ℝ) ≤ 2))
      have hpos : (0:ℝ) < Real.log (((blockBound K : ℕ) : ℝ) + 2) := by
        refine Real.log_pos ?_
        have : (0:ℝ) ≤ ((blockBound K : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      have hnn : (0:ℝ) ≤ (Nat.log2 (blockBound K) : ℝ) := Nat.cast_nonneg _
      nlinarith [hlog2M, h4, hlog2half, hpos, hnn]
  have hx : (1:ℝ)/2 ≤ Real.log ((K:ℝ)+2) := hlogK
  have hx2 : (1:ℝ)/4 ≤ (Real.log ((K:ℝ)+2))^2 := by nlinarith [hx]
  nlinarith [hkey, hlogM2, hx, hx2]

/-- **Bourgain's `Z_r` reduction: the general case of Lemma 4.11 follows from the `1`-separated
case.**  Given the `1`-separated maximal estimate (`hsep`, the estimate with the sum of interval
integrals over the disjoint `2^{-(j+1)}`-bands around the frequencies), the same estimate with the
same `(log (K+2))⁴` constant holds for an arbitrary finite frequency set.  The scales at which the
`2^{-(j+1)}`-neighbourhoods have a fixed number of connected components form at most `K` blocks;
on each block cluster representatives are separated relative to the local radius, so a dilation
reduces the block to the `1`-separated estimate, and the blocks are recombined with the
nested-scale (dual Doob) estimate `Commons.Analysis.Fourier.nested_finite_scales_maximal_l2`. -/
theorem neighborhood_maximal_arbitrary_of_separated
    (hsep : ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (mu : Fin N → ℝ),
      (∀ i j : Fin N, i ≠ j → 1 ≤ |mu i - mu j|) →
      ∀ (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.volume),
        ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
            (∑ k : Fin N,
              ∫ θ in (mu k - (2:ℝ)^(-(j:ℝ)-1))..(mu k + (2:ℝ)^(-(j:ℝ)-1)),
                Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ))))‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.volume
        ≤ ENNReal.ofReal ((C * (Real.log ((N:ℝ)+2))^2)^2)
          * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.volume) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
      ∀ (f : ℝ → ℂ) (hf : MeasureTheory.MemLp f 2 MeasureTheory.volume),
        ∫⁻ x, (⨆ j : ℕ, ‖∫ y : ℝ, f y *
            (∫ θ : ℝ, Set.indicator
              {θ : ℝ | ∃ k : Fin K, |θ - lam k| ≤ (2:ℝ)^(-(j:ℝ)-1)}
              (fun θ => Complex.exp (-(Complex.I * (((x - y : ℝ) : ℂ)) * (θ : ℂ)))) θ)‖ₑ) ^ (2:ℝ)
          ∂MeasureTheory.volume
        ≤ ENNReal.ofReal ((C * (Real.log ((K:ℝ)+2))^2)^2)
          * ∫⁻ x, ‖f x‖ₑ ^ (2:ℝ) ∂MeasureTheory.volume := by
  obtain ⟨C₀, hC₀pos, hC₀max⟩ := block_maximal_of_separated hsep
  refine ⟨2000 * (1 + C₀), by positivity, ?_⟩
  intro K lam f hf
  have hK := itOp_maximal_l2_of_separated lam C₀ hC₀pos hC₀max f hf
  have hM := nat_log2_blockBound_le K
  have hL : (1:ℝ)/4 ≤ (Real.log ((K:ℝ)+2))^2 := by
    have hlog2half : (1:ℝ)/2 ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
      norm_num at h ⊢
      linarith
    have hlogK : (1:ℝ)/2 ≤ Real.log ((K:ℝ)+2) :=
      le_trans hlog2half (Real.log_le_log (by norm_num : (0:ℝ) < 2)
        (by linarith [show (0:ℝ) ≤ (K:ℝ) from Nat.cast_nonneg K]))
    nlinarith
  have hkey : 2 * Real.pi * (10 * (1 + C₀ * (Real.log ((K:ℝ)+2))^2)
        + (Nat.log2 (blockBound K) : ℝ) + 1)
      ≤ 2000 * (1 + C₀) * (Real.log ((K:ℝ)+2))^2 := by
    have hLnn : (0:ℝ) ≤ (Real.log ((K:ℝ)+2))^2 := sq_nonneg _
    have hCL : (0:ℝ) ≤ C₀ * (Real.log ((K:ℝ)+2))^2 := mul_nonneg (le_of_lt hC₀pos) hLnn
    nlinarith [hM, hC₀pos, Real.pi_pos, Real.pi_lt_four, hL, hLnn, hCL]
  calc ∫⁻ x : ℝ, (⨆ j : ℕ, ‖itOp (neigh lam j) f x‖ₑ) ^ (2:ℝ)
      ≤ ENNReal.ofReal ((2 * Real.pi * (10 * (1 + C₀ * (Real.log ((K:ℝ)+2))^2)
            + (Nat.log2 (blockBound K) : ℝ) + 1)) ^ 2) * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := hK
    _ ≤ ENNReal.ofReal ((2000 * (1 + C₀) * (Real.log ((K:ℝ)+2))^2) ^ 2)
          * ∫⁻ x : ℝ, ‖f x‖ₑ ^ (2:ℝ) := by
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ ?_ hkey 2)) le_rfl
        positivity

end

end Commons.Analysis.Fourier
