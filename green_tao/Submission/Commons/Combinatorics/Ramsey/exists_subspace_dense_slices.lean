import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Star.Real
import Submission.Commons.Combinatorics.Ramsey.mdhj_of_dhj

open Finset
open _root_.Combinatorics

namespace Commons.Combinatorics.Ramsey

noncomputable section

variable {K : ℕ}

lemma cat_eq_append {α : Type*} {a N : ℕ} (ha : a ≤ N) (w : Fin a → α) (y : Fin (N - a) → α) :
    cat ha w y = Fin.append w y ∘ Fin.cast (Nat.add_sub_of_le ha).symm := by
  funext i
  by_cases h : (i:ℕ) < a
  · rw [cat_apply_of_lt ha w y i h, Function.comp_apply]
    have hc : (Fin.cast (Nat.add_sub_of_le ha).symm i : Fin (a + (N - a)))
        = Fin.castAdd (N - a) ⟨i, h⟩ := Fin.ext rfl
    rw [hc, Fin.append_left]
  · rw [cat_apply_of_ge ha w y i h, Function.comp_apply]
    have hc : (Fin.cast (Nat.add_sub_of_le ha).symm i : Fin (a + (N - a)))
        = Fin.natAdd a ⟨i.1 - a, by omega⟩ := by
      apply Fin.ext
      simp [Fin.natAdd]
      omega
    rw [hc, Fin.append_right]

lemma cat_append {α : Type*} {a m N : ℕ} (ha : a ≤ N) (ham : a + m ≤ N)
    (w : Fin a → α) (z : Fin m → α) (y : Fin (N - a - m) → α) :
    cat ham (Fin.append w z) (y ∘ Fin.cast (Nat.sub_sub N a m).symm)
      = cat ha w (cat (by omega : m ≤ N - a) z y) := by
  funext i
  by_cases h1 : (i:ℕ) < a
  · have h2 : (i:ℕ) < a + m := by omega
    rw [cat_apply_of_lt ha w _ i h1, cat_apply_of_lt ham (Fin.append w z) _ i h2]
    have he : (⟨i.1, h2⟩ : Fin (a+m)) = Fin.castAdd m ⟨i.1, h1⟩ := Fin.ext rfl
    rw [he, Fin.append_left]
  · rw [cat_apply_of_ge ha w _ i h1]
    by_cases h2 : (i:ℕ) - a < m
    · have h3 : (i:ℕ) < a + m := by omega
      have h4 : (i:ℕ) - a < N - a := by omega
      rw [cat_apply_of_lt (show m ≤ N - a by omega) z y ⟨i.1 - a, h4⟩ h2]
      rw [cat_apply_of_lt ham (Fin.append w z) _ i h3]
      have he : (⟨i.1, h3⟩ : Fin (a+m)) = Fin.natAdd a ⟨i.1 - a, h2⟩ := by
        apply Fin.ext; simp [Fin.natAdd]; omega
      rw [he, Fin.append_right]
    · have h3 : ¬(i:ℕ) < a + m := by omega
      have h4 : (i:ℕ) - a < N - a := by omega
      rw [cat_apply_of_ge (show m ≤ N - a by omega) z y ⟨i.1 - a, h4⟩ h2]
      rw [cat_apply_of_ge ham (Fin.append w z) _ i h3]
      simp only [Function.comp_apply]
      congr 1
      apply Fin.ext
      simp only [Fin.val_cast]
      omega

lemma card_sum_prefix_slices_nat {k N m : ℕ} (hm : m ≤ N) (T : Finset (Fin N → Fin k)) :
    T.card = ∑ z : Fin m → Fin k,
      ((Finset.univ : Finset (Fin (N - m) → Fin k)).filter
        (fun y => cat hm z y ∈ T)).card := by
  have hfib : T.card = ∑ z : Fin m → Fin k, (T.filter (fun v => res hm v = z)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := res hm) (s := T) (t := Finset.univ)
      (fun a _ => Finset.mem_univ _)]
  rw [hfib]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  refine Finset.card_bij (fun v _ => del hm v) ?_ ?_ ?_
  · intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← hv.2, cat_res_del]
    exact hv.1
  · intro v hv v' hv' heq
    rw [Finset.mem_filter] at hv hv'
    calc v = cat hm (res hm v) (del hm v) := (cat_res_del hm v).symm
      _ = cat hm z (del hm v) := by rw [hv.2]
      _ = cat hm z (del hm v') := by rw [heq]
      _ = cat hm (res hm v') (del hm v') := by rw [hv'.2]
      _ = v' := cat_res_del hm v'
  · intro y hy
    rw [Finset.mem_filter] at hy
    refine ⟨cat hm z y, ?_, del_cat hm z y⟩
    rw [Finset.mem_filter]
    exact ⟨hy.2, res_cat hm z y⟩

/-- The slice of `A` (a subset of `[K]^n`) by the prefix `w` of length `a`. -/
def sliceSet (n : ℕ) (A : Finset (Fin n → Fin K)) {a : ℕ} (ha : a ≤ n) (w : Fin a → Fin K) :
    Finset (Fin (n - a) → Fin K) :=
  Finset.univ.filter (fun y => cat ha w y ∈ A)

lemma mem_sliceSet {K n a : ℕ} {A : Finset (Fin n → Fin K)} {ha : a ≤ n} {w : Fin a → Fin K}
    {y : Fin (n - a) → Fin K} : y ∈ sliceSet n A ha w ↔ cat ha w y ∈ A := by
  simp [sliceSet]

/-- The density of the slice by `w`. -/
def sliceDens (n : ℕ) (A : Finset (Fin n → Fin K)) {a : ℕ} (ha : a ≤ n) (w : Fin a → Fin K) : ℝ :=
  (sliceSet n A ha w).card / (K : ℝ) ^ (n - a)

lemma card_slc_append {K m n a : ℕ} (A : Finset (Fin n → Fin K)) (ha : a ≤ n) (ham : a + m ≤ n)
    (w : Fin a → Fin K) :
    (sliceSet n A ha w).card = ∑ z : Fin m → Fin K, (sliceSet n A ham (Fin.append w z)).card := by
  rw [card_sum_prefix_slices_nat (show m ≤ n - a by omega) (sliceSet n A ha w)]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  refine Finset.card_bij (fun y _ => y ∘ Fin.cast (Nat.sub_sub n a m).symm) ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [mem_sliceSet] at hy
    rw [mem_sliceSet]
    rw [cat_append ha ham w z y]
    exact hy
  · intro y hy y' hy' heq
    funext j
    have h := congrFun heq (Fin.cast (Nat.sub_sub n a m) j)
    simp only [Function.comp_apply] at h
    have hcc : Fin.cast (Nat.sub_sub n a m).symm (Fin.cast (Nat.sub_sub n a m) j) = j := by
      apply Fin.ext; simp only [Fin.val_cast]
    rwa [hcc] at h
  · intro y hy
    have hcc : (y ∘ Fin.cast (Nat.sub_sub n a m)) ∘ Fin.cast (Nat.sub_sub n a m).symm = y := by
      funext i
      exact congrArg y (by apply Fin.ext; simp only [Fin.val_cast])
    refine ⟨y ∘ Fin.cast (Nat.sub_sub n a m), ?_, hcc⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [mem_sliceSet]
    rw [← cat_append ha ham w z (y ∘ Fin.cast (Nat.sub_sub n a m))]
    rw [hcc]
    simpa only [mem_sliceSet] using hy

/-- The density of a slice is at most `1`. -/
lemma sliceDens_le_one {K n a : ℕ} (hK : 0 < K) (A : Finset (Fin n → Fin K)) (ha : a ≤ n)
    (w : Fin a → Fin K) : sliceDens n A ha w ≤ 1 := by
  have hcard : (sliceSet n A ha w).card ≤ (Finset.univ : Finset (Fin (n - a) → Fin K)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hcard
  have hpow : (0:ℝ) < (K:ℝ)^(n-a) := pow_pos (by exact_mod_cast hK) _
  rw [sliceDens, div_le_one hpow]
  calc ((sliceSet n A ha w).card : ℝ) ≤ ((K ^ (n-a) : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (K:ℝ)^(n-a) := by push_cast; ring

/-- The sum of the densities of the slices through the blocks of size `m` equals
`K^m` times the density of the original slice. -/
lemma sliceDens_append_sum {K m n a : ℕ} (hK : 0 < K) (A : Finset (Fin n → Fin K))
    (ha : a ≤ n) (ham : a + m ≤ n) (w : Fin a → Fin K) :
    ∑ z : Fin m → Fin K, sliceDens n A ham (Fin.append w z) = (K:ℝ)^m * sliceDens n A ha w := by
  have hcard := card_slc_append A ha ham w
  have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hpow : (K:ℝ)^(n-a) = (K:ℝ)^m * (K:ℝ)^(n-(a+m)) := by
    have h1 : n - a = m + (n - a - m) := by omega
    rw [h1, pow_add, show n - a - m = n - (a + m) by omega]
  have hmne : (K:ℝ)^m ≠ 0 := ne_of_gt (pow_pos hKpos m)
  have hdne : (K:ℝ)^(n-(a+m)) ≠ 0 := ne_of_gt (pow_pos hKpos _)
  have : (∑ z : Fin m → Fin K, sliceDens n A ham (Fin.append w z))
      = (∑ z : Fin m → Fin K, ((sliceSet n A ham (Fin.append w z)).card : ℝ))
        / (K:ℝ)^(n-(a+m)) := by
    rw [Finset.sum_div]
    rfl
  rw [this, ← Nat.cast_sum, ← hcard, sliceDens, hpow]
  field_simp

/-- `maxSliceDens n A a ha` is the maximal density of a slice by a prefix of length `a`. -/
def maxSliceDens {K : ℕ} (hK : 0 < K) (n : ℕ) (A : Finset (Fin n → Fin K)) (a : ℕ) (ha : a ≤ n) : ℝ :=
  (Finset.univ : Finset (Fin a → Fin K)).sup'
    ⟨fun _ => ⟨0, hK⟩, Finset.mem_univ _⟩ (fun w => sliceDens n A ha w)

lemma le_maxSliceDens {K : ℕ} (hK : 0 < K) {n a : ℕ} (A : Finset (Fin n → Fin K)) (ha : a ≤ n)
    (w : Fin a → Fin K) : sliceDens n A ha w ≤ maxSliceDens hK n A a ha :=
  Finset.le_sup' (f := fun w => sliceDens n A ha w) (Finset.mem_univ w)

lemma maxSliceDens_le_one {K : ℕ} (hK : 0 < K) {n a : ℕ} (A : Finset (Fin n → Fin K)) (ha : a ≤ n) :
    maxSliceDens hK n A a ha ≤ 1 :=
  Finset.sup'_le _ _ (fun w _ => sliceDens_le_one hK A ha w)

lemma sliceSet_zero {K n : ℕ} (A : Finset (Fin n → Fin K)) :
    sliceSet n A (Nat.zero_le n) (fun i : Fin 0 => i.elim0) = A := by
  have h : ∀ y : Fin n → Fin K,
      cat (Nat.zero_le n) (fun i : Fin 0 => i.elim0) y = y := by
    intro y
    funext i
    rw [cat_apply_of_ge (Nat.zero_le n) (fun i : Fin 0 => i.elim0) y i (by simp)]
    exact congrArg y (Fin.ext (by simp))
  ext y
  rw [mem_sliceSet, h]

lemma sliceDens_empty {K n : ℕ} (A : Finset (Fin n → Fin K)) :
    sliceDens n A (Nat.zero_le n) (fun i : Fin 0 => i.elim0) = (A.card : ℝ) / (K:ℝ)^n := by
  rw [sliceDens, sliceSet_zero]
  simp only [Nat.sub_zero]

lemma maxSliceDens_zero {K : ℕ} (hK : 0 < K) {n : ℕ} (A : Finset (Fin n → Fin K)) :
    maxSliceDens hK n A 0 (Nat.zero_le n) = (A.card : ℝ) / (K:ℝ)^n := by
  have h1 : maxSliceDens hK n A 0 (Nat.zero_le n)
      = sliceDens n A (Nat.zero_le n) (fun i : Fin 0 => i.elim0) := by
    refine le_antisymm ?_ ?_
    · refine Finset.sup'_le _ _ (fun w _ => ?_)
      have hw : w = (fun i : Fin 0 => i.elim0) := by funext i; exact i.elim0
      rw [hw]
    · exact le_maxSliceDens hK A (Nat.zero_le n) (fun i : Fin 0 => i.elim0)
  rw [h1, sliceDens_empty]

/-- One step of the greedy argument: if no word of length `m*t` has all its contiguous
slices dense (density at least `α - ε`), then the maximal density strictly increases by `ρ`. -/
lemma sliceDens_increment {K m n t : ℕ} (hK : 0 < K) (hK2 : 2 ≤ K) (hm : 1 ≤ m)
    (A : Finset (Fin n → Fin K))
    (ε α ρ : ℝ) (ha : m*t ≤ n) (ham : m*t + m ≤ n)
    (hMα : α ≤ maxSliceDens hK n A (m*t) ha)
    (hng : ∀ w : Fin (m*t) → Fin K, ∃ z : Fin m → Fin K,
        sliceDens n A ham (Fin.append w z) < α - ε)
    (hρ : ρ * ((K:ℝ)^m - 1) ≤ ε) :
    maxSliceDens hK n A (m*t) ha + ρ ≤ maxSliceDens hK n A (m*t + m) ham := by
  classical
  set H : (Finset.univ : Finset (Fin (m*t) → Fin K)).Nonempty :=
    ⟨fun _ => ⟨0, hK⟩, Finset.mem_univ _⟩ with hH
  obtain ⟨w, -, hwsup⟩ := Finset.exists_mem_eq_sup' H (fun w => sliceDens n A ha w)
  have hw : maxSliceDens hK n A (m*t) ha = sliceDens n A ha w := hwsup
  set M0 : ℝ := maxSliceDens hK n A (m*t) ha with hM0
  have hM0dens : M0 = sliceDens n A ha w := hw
  suffices hex : ∃ z : Fin m → Fin K, M0 + ρ ≤ sliceDens n A ham (Fin.append w z) by
    obtain ⟨z, hz⟩ := hex
    exact le_trans hz (le_maxSliceDens hK A ham (Fin.append w z))
  by_contra hcon
  push Not at hcon
  set g : (Fin m → Fin K) → ℝ := fun z => sliceDens n A ham (Fin.append w z) with hg
  have hsum : ∑ z : Fin m → Fin K, g z = (K:ℝ)^m * M0 := by
    rw [hM0dens]; exact sliceDens_append_sum hK A ha ham w
  obtain ⟨zb, hzb⟩ := hng w
  have hzbb : g zb < α - ε := hzb
  have hsplit : ∑ z : Fin m → Fin K, g z
      = ∑ z ∈ (Finset.univ.erase zb), g z + g zb :=
    (Finset.sum_erase_add _ g (Finset.mem_univ zb)).symm
  have hKm_le : (1:ℕ) ≤ K^m := Nat.one_le_pow m K hK
  have hm1 : 1 ≤ m := hm
  have hKmpow_ge2 : (2:ℝ) ≤ (K:ℝ)^m := by
    have hKr : (2:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK2
    calc (2:ℝ) ≤ (K:ℝ) := hKr
      _ = (K:ℝ)^1 := (pow_one _).symm
      _ ≤ (K:ℝ)^m := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ K) hm1
  have hcard_lt : 1 < Fintype.card (Fin m → Fin K) := by
    have hKm2 : 2 ≤ K^m := by
      calc (2:ℕ) ≤ K := hK2
        _ = K^1 := (pow_one K).symm
        _ ≤ K^m := Nat.pow_le_pow_right hK hm1
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    omega
  obtain ⟨b, hb⟩ := Fintype.exists_ne_of_one_lt_card hcard_lt zb
  have hne : (Finset.univ.erase zb).Nonempty :=
    ⟨b, Finset.mem_erase.mpr ⟨hb, Finset.mem_univ b⟩⟩
  have hlt1 : ∑ z ∈ (Finset.univ.erase zb), g z
      < ∑ z ∈ (Finset.univ.erase zb), (M0 + ρ) :=
    Finset.sum_lt_sum_of_nonempty hne (fun z _ => hcon z)
  have hconst : ∑ z ∈ (Finset.univ.erase zb), (M0 + ρ)
      = ((Finset.univ.erase zb).card : ℝ) * (M0 + ρ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hcarderase : ((Finset.univ.erase zb).card : ℝ) = (K:ℝ)^m - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ zb), Finset.card_univ, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, Nat.cast_sub hKm_le]
    push_cast
    ring
  have h1 : ∑ z ∈ (Finset.univ.erase zb), g z < ((K:ℝ)^m - 1) * (M0 + ρ) := by
    rw [hconst, hcarderase] at hlt1
    exact hlt1
  have key : (K:ℝ)^m * M0 < ((K:ℝ)^m - 1) * (M0 + ρ) + (α - ε) := by
    rw [← hsum, hsplit]
    exact add_lt_add h1 hzbb
  have h2 : ((K:ℝ)^m - 1) * (M0 + ρ) + (α - ε) ≤ ((K:ℝ)^m - 1) * M0 + α := by
    nlinarith [hρ]
  have h3 : (K:ℝ)^m * M0 < ((K:ℝ)^m - 1) * M0 + α := lt_of_lt_of_le key h2
  have h4 : M0 < α := by nlinarith [h3]
  linarith [hMα, h4]

/-- The "prefix" combinatorial subspace `w ⌢ ·`. -/
def prefSub {K a m : ℕ} (w : Fin a → Fin K) : Subspace (Fin m) (Fin K) (Fin (a + m)) where
  idxFun i := if h : (i:ℕ) < a then Sum.inl (w ⟨i, h⟩) else Sum.inr ⟨i.1 - a, by omega⟩
  proper e := ⟨⟨a + e.1, by have : e.1 < m := e.2; omega⟩, by
    have h : ¬ ((a + e.1 : ℕ) < a) := by omega
    simp only [dif_neg h]
    congr 1
    apply Fin.ext
    simp⟩

lemma prefSub_idxFun {K a m : ℕ} (w : Fin a → Fin K) (i : Fin (a + m)) :
    (prefSub (m := m) w).idxFun i
      = if h : (i:ℕ) < a then Sum.inl (w ⟨i, h⟩) else Sum.inr ⟨i.1 - a, by omega⟩ := rfl

lemma prefSub_apply {K a m : ℕ} (w : Fin a → Fin K) (x : Fin m → Fin K) :
    prefSub (K := K) w x = Fin.append w x := by
  funext i
  rw [Subspace.coe_apply, prefSub_idxFun]
  by_cases h : (i:ℕ) < a
  · rw [dif_pos h]
    simp only [Sum.elim_inl]
    exact (Fin.append_left w x (⟨i.1, h⟩ : Fin a)).symm
  · rw [dif_neg h]
    simp only [Sum.elim_inr]
    have heq : i = Fin.natAdd a (⟨i.1 - a, by omega⟩ : Fin m) := by
      apply Fin.ext; simp [Fin.natAdd]; omega
    exact (Fin.append_right w x (⟨i.1 - a, by omega⟩ : Fin m)).symm.trans
      (congrArg (Fin.append w x) heq).symm

/-- The key estimate: a dense subset of `[K]^n` has an `m`-dimensional subspace `V` of `[K]^l`
(all of whose points are prefixes) such that all the slices above `V` are dense. -/
lemma dense_slices_aux {K m n : ℕ} (hK2 : 2 ≤ K) (hm : 1 ≤ m) (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (A : Finset (Fin n → Fin K)) (hA : ε * (K:ℝ)^n < (A.card : ℝ))
    (hn : (K:ℝ)^m * m / ε ≤ (n:ℝ)) :
    ∃ l : ℕ, ∃ h : l < n, ∃ V : Subspace (Fin m) (Fin K) (Fin l),
      ∀ x : Fin m → Fin K,
        ((A.card:ℝ)/(K:ℝ)^n - ε) * (K:ℝ)^(n-l)
          ≤ ((sliceSet n A (le_of_lt h) (V x)).card : ℝ) := by
  classical
  have hK : 0 < K := by omega
  have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast hK
  have hKpow : (0:ℝ) < (K:ℝ)^n := pow_pos hKpos n
  set α : ℝ := (A.card : ℝ) / (K:ℝ)^n with hα
  have hαε : ε < α := by
    rw [hα, lt_div_iff₀ hKpow]
    linarith [hA]
  have hα1 : α ≤ 1 := by
    rw [hα, div_le_one hKpow]
    have h := Finset.card_le_univ A
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at h
    exact_mod_cast h
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hKmpow_ge2 : (2:ℝ) ≤ (K:ℝ)^m := by
    have hKr : (2:ℝ) ≤ (K:ℝ) := by exact_mod_cast hK2
    calc (2:ℝ) ≤ (K:ℝ) := hKr
      _ = (K:ℝ)^1 := (pow_one _).symm
      _ ≤ (K:ℝ)^m := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ K) hm
  have hKm1pos : (0:ℝ) < (K:ℝ)^m - 1 := by linarith
  set ρ : ℝ := ε / ((K:ℝ)^m - 1) with hρ
  have hρpos : 0 < ρ := div_pos hε hKm1pos
  have hρle : ρ * ((K:ℝ)^m - 1) ≤ ε := by
    rw [hρ, div_mul_cancel₀]
    exact ne_of_gt hKm1pos
  set T : ℕ := Nat.floor ((1 - α) / ρ) with hT
  have hTlt : (1 - α) / ρ < (T:ℝ) + 1 := by
    rw [hT]; exact Nat.lt_floor_add_one _
  have hTle : (T:ℝ) ≤ (1 - α) / ρ := by
    rw [hT]; exact Nat.floor_le (div_nonneg (by linarith) (le_of_lt hρpos))
  have hbndR : ((m*(T+1) : ℕ) : ℝ) < (n:ℝ) := by
    have hT1 : (T:ℝ) + 1 ≤ ((K:ℝ)^m - 1)/ε + 1 := by
      have h1 : (1 - α)/ρ ≤ ((K:ℝ)^m - 1)/ε := by
        have he : (1 - α)/ρ = (1 - α) * ((K:ℝ)^m - 1)/ε := by
          rw [hρ]; field_simp
        rw [he]
        apply div_le_div_of_nonneg_right _ (le_of_lt hε)
        nlinarith
      linarith [hTle]
    have hmul : (m:ℝ) * ((T:ℝ) + 1) ≤ (m:ℝ) * (((K:ℝ)^m - 1)/ε + 1) :=
      mul_le_mul_of_nonneg_left hT1 (le_of_lt hmR)
    have h3 : (m:ℝ) * (((K:ℝ)^m - 1)/ε + 1) < (n:ℝ) := by
      have h4 : (m:ℝ) * (((K:ℝ)^m - 1)/ε + 1) = (m:ℝ)*((K:ℝ)^m - 1)/ε + (m:ℝ) := by ring
      rw [h4]
      have h5 : (m:ℝ) < (m:ℝ)/ε := by
        rw [lt_div_iff₀ hε]; nlinarith
      calc (m:ℝ)*((K:ℝ)^m - 1)/ε + (m:ℝ)
          < (m:ℝ)*((K:ℝ)^m - 1)/ε + (m:ℝ)/ε := by linarith
        _ = ((m:ℝ)*((K:ℝ)^m - 1) + (m:ℝ))/ε := by ring
        _ = (m:ℝ)*((K:ℝ)^m)/ε := by ring
        _ = (K:ℝ)^m * m / ε := by ring
        _ ≤ (n:ℝ) := hn
    push_cast
    linarith [hmul, h3]
  have hbnd : m*(T+1) < n := by exact_mod_cast hbndR
  have hb : ∀ j, j ≤ T+1 → m*j ≤ n := fun j hj => by
    have : m*j ≤ m*(T+1) := Nat.mul_le_mul_left m hj
    omega
  -- The good word exists at some level `j ≤ T`.
  have hgood : ∃ j : ℕ, ∃ (hj : j ≤ T), ∃ w : Fin (m*j) → Fin K,
      ∀ z : Fin m → Fin K, α - ε ≤ sliceDens n A (hb (j+1) (by omega)) (Fin.append w z) := by
    by_contra hH
    push Not at hH
    have key : ∀ j (hj : j ≤ T+1), α + (j:ℝ)*ρ ≤ maxSliceDens hK n A (m*j) (hb j hj) := by
      intro j
      induction j with
      | zero =>
        intro hj
        have h0 : α ≤ maxSliceDens hK n A (m*0) (hb 0 hj) := by
          have h1 := le_maxSliceDens hK A (hb 0 hj) (fun i : Fin (m*0) => i.elim0)
          have h2 : sliceDens n A (hb 0 hj) (fun i : Fin (m*0) => i.elim0) = α := by
            simpa [hα] using sliceDens_empty (K:=K) A
          linarith [h1, h2]
        simpa using h0
      | succ j ih =>
        intro hj
        have hj' : j ≤ T+1 := le_trans (Nat.le_succ j) hj
        have hjT : j ≤ T := by omega
        have hIH := ih hj'
        have hinc := sliceDens_increment hK hK2 hm A ε α ρ (hb j hj') (hb (j+1) hj)
          (by have hnn : (0:ℝ) ≤ (j:ℝ)*ρ := mul_nonneg (Nat.cast_nonneg j) (le_of_lt hρpos)
              linarith [hIH]) (hH j hjT) hρle
        have hstep : (α + (j:ℝ)*ρ) + ρ ≤ maxSliceDens hK n A (m*j+m) (hb (j+1) hj) := by
          linarith [hIH, hinc]
        have he : (α + (j:ℝ)*ρ) + ρ = α + ((j:ℝ)+1)*ρ := by ring
        have hgoal : α + ((j:ℝ)+1)*ρ ≤ maxSliceDens hK n A (m*j+m) (hb (j+1) hj) := by
          rw [← he]; exact hstep
        push_cast
        exact hgoal
    have hT1 := key (T+1) le_rfl
    have hM1 : maxSliceDens hK n A (m*(T+1)) (hb (T+1) le_rfl) ≤ 1 := maxSliceDens_le_one hK A _
    have hgt : 1 < α + ((T+1:ℕ):ℝ)*ρ := by
      have h2 : 1 - α < ((T:ℝ)+1)*ρ := by
        rw [div_lt_iff₀ hρpos] at hTlt
        linarith
      have h3 : ((T+1:ℕ):ℝ) = (T:ℝ)+1 := by push_cast; ring
      rw [h3]
      linarith
    linarith
  obtain ⟨j, hjT, w, hw⟩ := hgood
  have hl : m*j + m < n := by
    have h1 : m*j + m ≤ m*(T+1) := by
      calc m*j + m ≤ m*T + m := Nat.add_le_add_right (Nat.mul_le_mul_left m hjT) m
        _ = m*(T+1) := (Nat.mul_succ m T).symm
    omega
  refine ⟨m*j + m, hl, prefSub w, fun x => ?_⟩
  have hx := hw x
  have hconv : sliceDens n A (hb (j+1) (by omega)) (Fin.append w x)
      = ((sliceSet n A (le_of_lt hl) (prefSub w x)).card : ℝ) / (K:ℝ)^(n-(m*j+m)) := by
    rw [prefSub_apply]
    rfl
  rw [hconv] at hx
  have hKp : (0:ℝ) < (K:ℝ)^(n-(m*j+m)) := pow_pos hKpos _
  rw [le_div_iff₀ hKp] at hx
  exact hx

theorem exists_subspace_dense_slices (K m : ℕ) (hK : 2 ≤ K) (hm : 1 ≤ m)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ A : Finset (Fin n → Fin K),
      ε * (K : ℝ) ^ n < (A.card : ℝ) →
      ∃ l : ℕ, ∃ h : l < n, ∃ V : _root_.Combinatorics.Subspace (Fin m) (Fin K) (Fin l),
        ∀ x : Fin m → Fin K,
          ((A.card : ℝ) / (K : ℝ) ^ n - ε) * ((K : ℝ) ^ (n - l)) ≤
            (((Finset.univ : Finset (Fin (n - l) → Fin K)).filter
               (fun y => _root_.Commons.Combinatorics.Ramsey.cat (le_of_lt h) (V x) y ∈ A)).card : ℝ) := by
  refine ⟨Nat.ceil ((K:ℝ)^m * m / ε), ?_⟩
  intro n hn A hA
  have hn' : (K:ℝ)^m * m / ε ≤ (n:ℝ) := Nat.ceil_le.mp hn
  obtain ⟨l, hl, V, hV⟩ := dense_slices_aux hK hm ε hε hε1 A hA hn'
  exact ⟨l, hl, V, fun x => by simpa only [sliceSet] using hV x⟩

end

end Commons.Combinatorics.Ramsey