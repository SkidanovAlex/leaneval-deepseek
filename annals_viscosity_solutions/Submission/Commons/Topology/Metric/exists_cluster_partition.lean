import Mathlib.Topology.MetricSpace.Pseudo.Defs

namespace Commons.Topology.Metric

open Finset

variable {E : Type*} [PseudoMetricSpace E]

/-- **Drop lemma.**  Let `E : ℕ → ℝ` be non-increasing (from index `1` on) up to `N` with `E N = 0`,
and let `0 < eps`, `1 < lam`.  Then there is `k ∈ {1,…,N}` with
`max (E k) eps ≤ (2*lam)^N * eps` and either `k = 1` or `max (E k) eps ≤ E (k-1)/(2*lam)`. -/
lemma exists_drop_of_antitone {N : ℕ} (hN : 0 < N) {lam eps : ℝ} (hlam : 1 < lam) (heps : 0 < eps)
    (E : ℕ → ℝ) (hanti : ∀ k, 1 ≤ k → k < N → E (k+1) ≤ E k) (hEN : E N = 0) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ max (E k) eps ≤ (2*lam)^N * eps ∧
      (k = 1 ∨ max (E k) eps ≤ E (k-1) / (2*lam)) := by
  have h2lam : (1:ℝ) < 2*lam := by linarith
  have h2lampos : (0:ℝ) < 2*lam := by linarith
  have hΓpos : (0:ℝ) < (2*lam)^N * eps := mul_pos (pow_pos h2lampos N) heps
  have hΓeps : eps ≤ (2*lam)^N * eps := by
    have h1 : (1:ℝ) ≤ (2*lam)^N := one_le_pow₀ (le_of_lt h2lam)
    calc eps = 1 * eps := by ring
      _ ≤ (2*lam)^N * eps := mul_le_mul_of_nonneg_right h1 (le_of_lt heps)
  have hmono : ∀ i j, 1 ≤ i → i ≤ j → j ≤ N → E j ≤ E i := by
    intro i j hi hij hjN
    have aux : ∀ d, i + d ≤ N → E (i + d) ≤ E i := by
      intro d
      induction d with
      | zero => intro _; simp
      | succ d ih =>
        intro hdN
        have h1 : E (i + (d+1)) ≤ E (i + d) := hanti (i+d) (by omega) (by omega)
        exact le_trans h1 (ih (by omega))
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hij
    subst hd
    exact aux d hjN
  by_contra hcon
  push Not at hcon
  have hE1max : (2*lam)^N * eps < max (E 1) eps := by
    by_contra hle
    exact (hcon 1 le_rfl hN (le_of_not_gt hle)).1 rfl
  have hE1 : (2*lam)^N * eps < E 1 := by
    by_cases hle : eps ≤ E 1
    · rwa [max_eq_left hle] at hE1max
    · exfalso
      have hm : max (E 1) eps = eps := max_eq_right (le_of_lt (not_le.mp hle))
      rw [hm] at hE1max
      exact absurd hE1max (not_lt.mpr hΓeps)
  have hex : ∃ j : ℕ, E (j+1) ≤ (2*lam)^N * eps :=
    ⟨N-1, by
      have hN' : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos hN
      rw [hN', hEN]
      exact le_of_lt hΓpos⟩
  let m : ℕ := Nat.find hex
  have hspec : E (m+1) ≤ (2*lam)^N * eps := Nat.find_spec hex
  have hmin : ∀ j < m, (2*lam)^N * eps < E (j+1) :=
    fun j hj => not_le.mp (Nat.find_min hex hj)
  have hmle : m ≤ N - 1 := Nat.find_le (p := fun j => E (j+1) ≤ (2*lam)^N*eps)
    (by
      have hN' : N - 1 + 1 = N := Nat.succ_pred_eq_of_pos hN
      rw [hN', hEN]; exact le_of_lt hΓpos)
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      have hsp := hspec
      rw [h] at hsp
      simp only [zero_add] at hsp
      exact absurd hsp (not_le.mpr hE1)
    · exact h
  have hbk : ∀ k, m+1 ≤ k → k ≤ N → max (E k) eps ≤ (2*lam)^N * eps := by
    intro k hk1 hk2
    have h1 : E k ≤ E (m+1) := hmono (m+1) k (by omega) hk1 hk2
    exact max_le_iff.mpr ⟨le_trans h1 hspec, hΓeps⟩
  have hdrop : ∀ k, m+1 ≤ k → k ≤ N → E (k-1) < 2*lam * max (E k) eps := by
    intro k hk1 hk2
    have hk1' : 1 ≤ k := by omega
    have h2 := (hcon k hk1' hk2 (hbk k hk1 hk2)).2
    rw [div_lt_iff₀ h2lampos] at h2
    linarith
  have hbN : max (E N) eps = eps := by rw [hEN]; exact max_eq_right (le_of_lt heps)
  have hiter : ∀ t, t ≤ N - (m+1) + 1 → max (E (N - t)) eps ≤ (2*lam)^t * max (E N) eps := by
    intro t
    induction t with
    | zero => intro _; simp
    | succ t ih =>
      intro ht
      have ht' : t ≤ N - (m+1) + 1 := by omega
      have hstep : E (N - t - 1) < 2*lam * max (E (N - t)) eps :=
        hdrop (N - t) (by omega) (by omega)
      have hEq : N - t - 1 = N - (t+1) := by omega
      rw [hEq] at hstep
      have hMnn : (0:ℝ) ≤ max (E (N - t)) eps := le_trans (le_of_lt heps) (le_max_right _ _)
      have hle : eps ≤ 2*lam * max (E (N - t)) eps := by
        calc eps ≤ max (E (N - t)) eps := le_max_right _ _
          _ = 1 * max (E (N - t)) eps := by ring
          _ ≤ 2*lam * max (E (N - t)) eps := mul_le_mul_of_nonneg_right (by linarith) hMnn
      have h1 : max (E (N - (t+1))) eps ≤ 2*lam * max (E (N - t)) eps := by
        rw [max_le_iff]
        exact ⟨le_of_lt hstep, hle⟩
      calc max (E (N - (t+1))) eps ≤ 2*lam * max (E (N - t)) eps := h1
        _ ≤ 2*lam * ((2*lam)^t * max (E N) eps) :=
            mul_le_mul_of_nonneg_left (ih ht') (le_of_lt h2lampos)
        _ = (2*lam)^(t+1) * max (E N) eps := by ring
  have hfin := hiter (N - m) (by omega)
  have hNm : N - (N - m) = m := by omega
  rw [hNm, hbN] at hfin
  have hmpos : (2*lam)^N * eps < E m := by
    have h1 := hmin (m-1) (by omega)
    have h2 : (m-1)+1 = m := Nat.succ_pred_eq_of_pos hm1
    rwa [h2] at h1
  have hlt : (2*lam)^N * eps < (2*lam)^(N-m) * eps :=
    lt_of_lt_of_le (lt_of_lt_of_le hmpos (le_max_left _ _)) hfin
  have hlt2 : (2*lam)^N < (2*lam)^(N-m) := (mul_lt_mul_iff_of_pos_right heps).mp hlt
  have hlt3 : N < N - m := (pow_lt_pow_iff_right₀ h2lam).mp hlt2
  omega

/-! ### The greedy construction -/

/-- Distance from a point to a finite set of indices, measured with `A`; `0` if the set is empty. -/
noncomputable def distToFinset {N : ℕ} (A : Fin N → E) (C : Finset (Fin N)) (i : Fin N) : ℝ :=
  if h : C.Nonempty then C.inf' h (fun c => dist (A i) (A c)) else 0

lemma dC_nonneg {N : ℕ} (A : Fin N → E) (C : Finset (Fin N)) (i : Fin N) :
    0 ≤ distToFinset A C i := by
  unfold distToFinset
  split
  · rename_i h
    obtain ⟨c, hc, hce⟩ := Finset.exists_mem_eq_inf' h (fun c => dist (A i) (A c))
    rw [hce]; exact dist_nonneg
  · exact le_rfl

lemma dC_le_of_mem {N : ℕ} (A : Fin N → E) {C : Finset (Fin N)} {i c : Fin N} (hc : c ∈ C) :
    distToFinset A C i ≤ dist (A i) (A c) := by
  unfold distToFinset
  rw [dif_pos ⟨c, hc⟩]
  exact Finset.inf'_le _ hc

lemma dC_eq_zero_of_mem {N : ℕ} (A : Fin N → E) {C : Finset (Fin N)} {i : Fin N}
    (hi : i ∈ C) : distToFinset A C i = 0 := by
  refine le_antisymm ?_ (dC_nonneg A C i)
  simpa using dC_le_of_mem A (i := i) (c := i) hi

lemma dC_anti {N : ℕ} (A : Fin N → E) {C C' : Finset (Fin N)} (h : C ⊆ C')
    (hne : C.Nonempty) (i : Fin N) : distToFinset A C' i ≤ distToFinset A C i := by
  have hne' : C'.Nonempty := ⟨hne.choose, h hne.choose_spec⟩
  have key : ∀ c ∈ C, C'.inf' hne' (fun c => dist (A i) (A c)) ≤ dist (A i) (A c) :=
    fun c hc => Finset.inf'_le _ (h hc)
  have h1 : distToFinset A C i = C.inf' hne (fun c => dist (A i) (A c)) := dif_pos hne
  have h2 : distToFinset A C' i = C'.inf' hne' (fun c => dist (A i) (A c)) := dif_pos hne'
  rw [h1, h2]
  exact (Finset.le_inf'_iff hne _).mpr key

/-- Farthest point (in the sense of distance to `C`) outside `C`. -/
noncomputable def farthestOutside {N : ℕ} (A : Fin N → E) (hN : 0 < N) (C : Finset (Fin N)) : Fin N :=
  if h : (univ \ C).Nonempty then
    Classical.choose (Finset.exists_max_image (univ \ C) (distToFinset A C) h)
  else ⟨0, hN⟩

lemma nxt_mem {N : ℕ} (A : Fin N → E) (hN : 0 < N) {C : Finset (Fin N)}
    (h : (univ \ C).Nonempty) : farthestOutside A hN C ∈ univ \ C := by
  have h' := Classical.choose_spec (Finset.exists_max_image (univ \ C) (distToFinset A C) h)
  unfold farthestOutside
  rw [dif_pos h]
  exact h'.1

lemma nxt_max {N : ℕ} (A : Fin N → E) (hN : 0 < N) {C : Finset (Fin N)}
    (h : (univ \ C).Nonempty) : ∀ i ∈ univ \ C, distToFinset A C i ≤ distToFinset A C (farthestOutside A hN C) := by
  have h' := Classical.choose_spec (Finset.exists_max_image (univ \ C) (distToFinset A C) h)
  unfold farthestOutside
  rw [dif_pos h]
  exact h'.2

/-- The greedy sequence of chosen sets. -/
noncomputable def greedySets {N : ℕ} (A : Fin N → E) (hN : 0 < N) : ℕ → Finset (Fin N)
  | 0 => ∅
  | (k+1) => greedySets A hN k ∪ {farthestOutside A hN (greedySets A hN k)}

noncomputable def greedyPt {N : ℕ} (A : Fin N → E) (hN : 0 < N) (k : ℕ) : Fin N :=
  farthestOutside A hN (greedySets A hN k)

lemma greedySets_succ {N : ℕ} (A : Fin N → E) (hN : 0 < N) (k : ℕ) :
    greedySets A hN (k+1) = greedySets A hN k ∪ {greedyPt A hN k} := rfl

lemma greedySets_mono {N : ℕ} (A : Fin N → E) (hN : 0 < N) (k : ℕ) :
    greedySets A hN k ⊆ greedySets A hN (k+1) := by
  rw [greedySets_succ]; exact Finset.subset_union_left

lemma greedySets_eq_image {N : ℕ} (A : Fin N → E) (hN : 0 < N) (k : ℕ) :
    greedySets A hN k = (Finset.range k).image (greedyPt A hN) := by
  induction k with
  | zero => simp [greedySets]
  | succ k ih =>
      rw [greedySets_succ, ih, Finset.range_add_one, Finset.image_insert, Finset.union_singleton]

lemma card_Cseq {N : ℕ} (A : Fin N → E) (hN : 0 < N) : ∀ k, k ≤ N → (greedySets A hN k).card = k := by
  intro k
  induction k with
  | zero => intro _; simp [greedySets]
  | succ k ih =>
      intro hk
      have hkN : k ≤ N := by omega
      have hcomp : (univ \ greedySets A hN k).Nonempty := by
        rw [Finset.sdiff_nonempty]
        intro hsub
        have h1 : (univ : Finset (Fin N)).card ≤ (greedySets A hN k).card := Finset.card_le_card hsub
        rw [Finset.card_univ, Fintype.card_fin, ih hkN] at h1
        omega
      have hnot : greedyPt A hN k ∉ greedySets A hN k := by
        have hh := nxt_mem A hN hcomp
        rw [Finset.mem_sdiff] at hh
        exact hh.2
      rw [greedySets_succ]
      rw [Finset.card_union_of_disjoint]
      · rw [Finset.card_singleton, ih hkN]
      · rw [Finset.disjoint_singleton_right]; exact hnot

lemma greedySets_nonempty {N : ℕ} (A : Fin N → E) (hN : 0 < N) {k : ℕ} (hk1 : 1 ≤ k)
    (hk2 : k ≤ N) : (greedySets A hN k).Nonempty := by
  rw [← Finset.card_pos, card_Cseq A hN k hk2]
  omega

/-- covering radius with centres in `greedySets k` -/
noncomputable def greedyCov {N : ℕ} (A : Fin N → E) (hN : 0 < N) (k : ℕ) : ℝ :=
  univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩) (distToFinset A (greedySets A hN k))

lemma Ev_le {N : ℕ} (A : Fin N → E) (hN : 0 < N) (k : ℕ) (i : Fin N) :
    distToFinset A (greedySets A hN k) i ≤ greedyCov A hN k := by
  unfold greedyCov
  exact Finset.le_sup' _ (Finset.mem_univ i)

lemma Ev_nonneg {N : ℕ} (A : Fin N → E) (hN : 0 < N) (k : ℕ) : 0 ≤ greedyCov A hN k := by
  refine le_trans (dC_nonneg A (greedySets A hN k) (⟨0, hN⟩ : Fin N)) ?_
  exact Ev_le A hN k _

lemma Ev_anti {N : ℕ} (A : Fin N → E) (hN : 0 < N) {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    greedyCov A hN (k+1) ≤ greedyCov A hN k := by
  unfold greedyCov
  rw [Finset.sup'_le_iff]
  intro i _
  exact le_trans (dC_anti A (greedySets_mono A hN k) (greedySets_nonempty A hN hk hkN) i) (Ev_le A hN k i)

lemma Ev_eq_dC {N : ℕ} (A : Fin N → E) (hN : 0 < N) {k : ℕ} (hk : k < N) :
    greedyCov A hN k = distToFinset A (greedySets A hN k) (greedyPt A hN k) := by
  have hcomp : (univ \ greedySets A hN k).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    have h1 : (univ : Finset (Fin N)).card ≤ (greedySets A hN k).card := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin, card_Cseq A hN k (le_of_lt hk)] at h1
    omega
  unfold greedyCov greedyPt
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro i _
    by_cases hi : i ∈ greedySets A hN k
    · rw [dC_eq_zero_of_mem A hi]
      exact dC_nonneg A _ _
    · exact nxt_max A hN hcomp i (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ i, hi⟩)
  · rw [Finset.le_sup'_iff]
    exact ⟨farthestOutside A hN (greedySets A hN k), Finset.mem_univ _, le_rfl⟩

lemma greedySets_eq_univ {N : ℕ} (A : Fin N → E) (hN : 0 < N) : greedySets A hN N = univ := by
  apply Finset.eq_univ_of_card
  rw [Fintype.card_fin]
  exact card_Cseq A hN N le_rfl

lemma Ev_last {N : ℕ} (A : Fin N → E) (hN : 0 < N) : greedyCov A hN N = 0 := by
  refine le_antisymm ?_ (Ev_nonneg A hN N)
  unfold greedyCov
  rw [greedySets_eq_univ A hN, Finset.sup'_le_iff]
  intro i _
  rw [dC_eq_zero_of_mem A (Finset.mem_univ i)]

lemma Ev_mono {N : ℕ} (A : Fin N → E) (hN : 0 < N) : ∀ i j, 1 ≤ i → i ≤ j → j ≤ N →
    greedyCov A hN j ≤ greedyCov A hN i := by
  intro i j hi hij hjN
  have aux : ∀ d, i + d ≤ N → greedyCov A hN (i + d) ≤ greedyCov A hN i := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
      intro hdN
      have hid : i + (d+1) = (i + d) + 1 := by omega
      have h1 : greedyCov A hN ((i + d) + 1) ≤ greedyCov A hN (i + d) :=
        Ev_anti A hN (show 1 ≤ i + d by omega) (show i + d ≤ N by omega)
      rw [hid]
      exact le_trans h1 (ih (show i + d ≤ N by omega))
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hij
  subst hd
  exact aux d hjN

/-- separation of the greedy centres -/
lemma sep_Cseq {N : ℕ} (A : Fin N → E) (hN : 0 < N) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ N) :
    ∀ i ∈ greedySets A hN k, ∀ j ∈ greedySets A hN k, i ≠ j → greedyCov A hN (k-1) ≤ dist (A i) (A j) := by
  intro i hi j hj hij
  rw [greedySets_eq_image A hN k] at hi hj
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hj
  rw [Finset.mem_range] at ht hs
  have hne : t ≠ s := by rintro rfl; exact hij rfl
  rcases lt_or_gt_of_ne hne with hts | hst
  · have hgs : greedyPt A hN t ∈ greedySets A hN s := by
      rw [greedySets_eq_image A hN s, Finset.mem_image]
      exact ⟨t, by rw [Finset.mem_range]; omega, rfl⟩
    have h1 : distToFinset A (greedySets A hN s) (greedyPt A hN s) ≤ dist (A (greedyPt A hN s)) (A (greedyPt A hN t)) :=
      dC_le_of_mem A (i := greedyPt A hN s) (c := greedyPt A hN t) hgs
    have h2 : greedyCov A hN s = distToFinset A (greedySets A hN s) (greedyPt A hN s) := Ev_eq_dC A hN (by omega)
    have h3 : greedyCov A hN (k-1) ≤ greedyCov A hN s := Ev_mono A hN s (k-1) (by omega) (by omega) (by omega)
    rw [dist_comm]
    exact le_trans (le_trans h3 (le_of_eq h2)) h1
  · have hgs : greedyPt A hN s ∈ greedySets A hN t := by
      rw [greedySets_eq_image A hN t, Finset.mem_image]
      exact ⟨s, by rw [Finset.mem_range]; omega, rfl⟩
    have h1 : distToFinset A (greedySets A hN t) (greedyPt A hN t) ≤ dist (A (greedyPt A hN t)) (A (greedyPt A hN s)) :=
      dC_le_of_mem A (i := greedyPt A hN t) (c := greedyPt A hN s) hgs
    have h2 : greedyCov A hN t = distToFinset A (greedySets A hN t) (greedyPt A hN t) := Ev_eq_dC A hN (by omega)
    have h3 : greedyCov A hN (k-1) ≤ greedyCov A hN t := Ev_mono A hN t (k-1) (by omega) (by omega) (by omega)
    exact le_trans (le_trans h3 (le_of_eq h2)) h1



/-- auxiliary: `greedyPt t` is in `greedySets k` for `t < k`. -/
lemma greedyPt_mem_greedySets {N : ℕ} (A : Fin N → E) (hN : 0 < N) {k t : ℕ} (ht : t < k) :
    greedyPt A hN t ∈ greedySets A hN k := by
  rw [greedySets_eq_image A hN k, Finset.mem_image]
  exact ⟨t, by rwa [Finset.mem_range], rfl⟩

/-- auxiliary: two distinct greedy centres are distinct points. -/
lemma greedyPt_ne {N : ℕ} (A : Fin N → E) (hN : 0 < N) {k t s : ℕ} (hkN : k ≤ N) (hts : t < s)
    (hsk : s < k) : greedyPt A hN t ≠ greedyPt A hN s := by
  intro hcon
  have hcomp : (univ \ greedySets A hN s).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    have h1 : (univ : Finset (Fin N)).card ≤ (greedySets A hN s).card := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin, card_Cseq A hN s (by omega)] at h1
    omega
  have hnot : greedyPt A hN s ∉ greedySets A hN s := by
    have hh := nxt_mem A hN hcomp
    rw [Finset.mem_sdiff] at hh
    exact hh.2
  refine hnot ?_
  rw [← hcon]
  exact greedyPt_mem_greedySets A hN hts


/-! ### Main theorem -/

/-- **λ-cluster partition.**  Given `N ≥ 1` points of a pseudo-metric space, a parameter
`lam > 1` and `eps > 0`, there are centres `c : Fin K → E` and a radius
`R ∈ [eps, (2*lam)^N * eps]` such that the centres are `2*lam*R`-separated and every point
is within `R` of some centre. -/
theorem exists_cluster_partition {E : Type*} [PseudoMetricSpace E]
    (N : ℕ) (hN : 0 < N) (A : Fin N → E) {lam eps : ℝ} (hlam : 1 < lam) (heps : 0 < eps) :
    ∃ (K : ℕ) (c : Fin K → E) (R : ℝ),
      eps ≤ R ∧ R ≤ (2 * lam) ^ N * eps ∧
        (∀ j k : Fin K, j ≠ k → 2 * lam * R ≤ dist (c j) (c k)) ∧
        (∀ i : Fin N, ∃ j : Fin K, dist (A i) (c j) ≤ R) := by
  obtain ⟨k, hk1, hk2, hR, hlast⟩ := exists_drop_of_antitone hN hlam heps (greedyCov A hN)
    (fun k hk1 hkN => Ev_anti A hN hk1 (le_of_lt hkN)) (Ev_last A hN)
  have h2lampos : (0:ℝ) < 2*lam := by linarith
  have hdr : ∀ _ : 2 ≤ k, 2 * lam * max (greedyCov A hN k) eps ≤ greedyCov A hN (k-1) := by
    intro hk
    rcases hlast with hk1' | hdrop
    · omega
    · have h := (le_div_iff₀ h2lampos).mp hdrop
      linarith
  refine ⟨k, fun j => A (greedyPt A hN j.1), max (greedyCov A hN k) eps, le_max_right _ _, hR, ?_, ?_⟩
  · intro j j' hjj
    have hk2' : 2 ≤ k := by
      rcases Nat.lt_or_ge k 2 with h | h
      · exfalso
        exact hjj (Fin.ext (by have := j.2; have := j'.2; omega))
      · exact h
    have hdrop := hdr hk2'
    rcases lt_or_gt_of_ne (fun h => hjj (Fin.ext h)) with hlt | hgt
    · have hne : greedyPt A hN j.1 ≠ greedyPt A hN j'.1 := greedyPt_ne A hN hk2 hlt j'.2
      have h1 := sep_Cseq A hN hk1 hk2 (greedyPt A hN j.1)
        (greedyPt_mem_greedySets A hN j.2) (greedyPt A hN j'.1) (greedyPt_mem_greedySets A hN j'.2) hne
      exact le_trans hdrop h1
    · have hne : greedyPt A hN j'.1 ≠ greedyPt A hN j.1 := greedyPt_ne A hN hk2 hgt j.2
      have h1 := sep_Cseq A hN hk1 hk2 (greedyPt A hN j'.1)
        (greedyPt_mem_greedySets A hN j'.2) (greedyPt A hN j.1) (greedyPt_mem_greedySets A hN j.2) hne
      calc 2 * lam * max (greedyCov A hN k) eps ≤ greedyCov A hN (k-1) := hdrop
        _ ≤ dist (A (greedyPt A hN j'.1)) (A (greedyPt A hN j.1)) := h1
        _ = dist (A (greedyPt A hN j.1)) (A (greedyPt A hN j'.1)) := dist_comm _ _
  · intro i
    have hCne : (greedySets A hN k).Nonempty := greedySets_nonempty A hN hk1 hk2
    have hd : distToFinset A (greedySets A hN k) i ≤ max (greedyCov A hN k) eps :=
      le_trans (Ev_le A hN k i) (le_max_left _ _)
    have hinf : (greedySets A hN k).inf' hCne (fun c => dist (A i) (A c)) ≤ max (greedyCov A hN k) eps := by
      simpa only [distToFinset, dif_pos hCne] using hd
    obtain ⟨c, hc, hcR⟩ := (Finset.inf'_le_iff hCne).mp hinf
    rw [greedySets_eq_image A hN k, Finset.mem_image] at hc
    obtain ⟨t, ht, rfl⟩ := hc
    rw [Finset.mem_range] at ht
    exact ⟨⟨t, ht⟩, by simpa [greedyPt] using hcR⟩

end Commons.Topology.Metric