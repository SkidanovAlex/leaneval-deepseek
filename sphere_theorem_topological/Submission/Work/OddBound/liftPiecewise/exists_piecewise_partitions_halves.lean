import Mathlib

namespace Work.OddBound.liftPiecewise

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval

/-!
# Refining a partition of `[0,1]` at the midpoint

Given a partition `a 0 = 0 < a 1 < ⋯ < a k = 1` of `[0,1]` on whose pieces a curve
`h : ℝ → M` is `C¹`, we produce

* a partition of `[0,1/2]` on whose pieces `h` is `C¹`,
* a partition of `[1/2,1]` on whose pieces `h` is `C¹`,
* a partition of `[0,1/2]` on whose pieces the reversed curve `s ↦ h (1 - s)` is `C¹`.

The splitting point `1/2` is inserted into the given partition if it is not already one of
the breakpoints `a i`.  Concretely, `m₁` is the largest index with `a m₁ < 1/2` and `m₂` the
largest index with `a m₂ ≤ 1/2`; the left partition is `a 0 ≤ ⋯ ≤ a m₁ ≤ 1/2` and the right
partition is `1/2 ≤ a (m₂+1) ≤ ⋯ ≤ a k`.  The reversed partition is obtained from the right
one by the order-reversing involution `Fin.rev`.
-/

/-- **Splitting a partition below a point.**  If `h` is piecewise `C¹` on the partition
`a 0 = 0 < ⋯ < a k = 1` and `0 < γ ≤ 1`, then there is a partition of `[0,γ]` on whose pieces
`h` is `C¹`. -/
theorem exists_partition_split_left
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {h : ℝ → M} {k : ℕ} {a : Fin (k + 1) → ℝ}
    (hamono : StrictMono a) (ha0 : a 0 = 0) (ha1 : a (Fin.last k) = 1)
    (hpiece : ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (a j.castSucc) (a j.succ)))
    {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) :
    ∃ (k1 : ℕ) (b : Fin (k1 + 1) → ℝ), StrictMono b ∧ b 0 = 0 ∧ b (Fin.last k1) = γ ∧
      ∀ j : Fin k1, ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (b j.castSucc) (b j.succ)) := by
  classical
  -- `m` is the largest index with `a m < γ`.
  set S : Finset (Fin (k + 1)) := Finset.univ.filter (fun i => a i < γ) with hS
  have h0 : (0 : Fin (k + 1)) ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [ha0] using hγ0⟩
  have hne : S.Nonempty := ⟨0, h0⟩
  set m : Fin (k + 1) := S.max' hne with hmdef
  have hmmem : m ∈ S := by rw [hmdef]; exact Finset.max'_mem S hne
  have hmval : a m < γ := (Finset.mem_filter.mp hmmem).2
  have hmax : ∀ i ∈ S, i ≤ m := by
    intro i hi; rw [hmdef]; exact Finset.le_max' S i hi
  have hmk : m.val < k := by
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp m.isLt) with hlt | heq
    · exact hlt
    · exfalso
      have hlast : m = Fin.last k := Fin.ext heq
      rw [hlast, ha1] at hmval
      linarith
  have hup : γ ≤ a ⟨m.val + 1, by omega⟩ := by
    by_contra hcon
    have hcon' : a ⟨m.val + 1, by omega⟩ < γ := not_le.mp hcon
    have hmem : (⟨m.val + 1, by omega⟩ : Fin (k + 1)) ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hcon'⟩
    have hle : (⟨m.val + 1, by omega⟩ : Fin (k + 1)) ≤ m := hmax _ hmem
    have h2 : m.val + 1 ≤ m.val := Fin.le_iff_val_le_val.mp hle
    omega
  -- Extension of the partition to `ℕ`: values below `γ` stay, everything else becomes `γ`.
  let B : ℕ → ℝ := fun i => if h : i ≤ m.val then a ⟨i, by omega⟩ else γ
  have hB_lt : ∀ (i : ℕ) (hi : i ≤ m.val), B i = a ⟨i, by omega⟩ := by
    intro i hi
    simp only [B]
    exact dif_pos hi
  have hB_last : B (m.val + 1) = γ := by
    simp only [B]
    exact dif_neg (by omega : ¬ (m.val + 1 ≤ m.val))
  let b : Fin (m.val + 2) → ℝ := fun j => B j.val
  refine ⟨m.val + 1, b, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hval : i.val < j.val := hij
    have hjle : j.val ≤ m.val + 1 := by omega
    have hile : i.val ≤ m.val := by omega
    have hbi : b i = a ⟨i.val, by omega⟩ := by
      simp only [b]
      exact hB_lt i.val hile
    have hiγ : a ⟨i.val, by omega⟩ < γ :=
      lt_of_le_of_lt (hamono.monotone (Fin.le_iff_val_le_val.mpr hile)) hmval
    rcases lt_or_eq_of_le hjle with hjlt | hjeq
    · have hj2 : j.val ≤ m.val := by omega
      have hbj : b j = a ⟨j.val, by omega⟩ := by
        simp only [b]
        exact hB_lt j.val hj2
      rw [hbi, hbj]
      exact hamono (Fin.mk_lt_mk.mpr hval)
    · have hjv : j.val = m.val + 1 := by omega
      have hbj : b j = γ := by
        simp only [b]
        rw [hjv]
        exact hB_last
      rw [hbi, hbj]
      exact hiγ
  · have hb0 : b (0 : Fin (m.val + 2)) = a (0 : Fin (k + 1)) := by
      change B (0 : ℕ) = a (0 : Fin (k + 1))
      exact hB_lt 0 (Nat.zero_le _)
    exact hb0.trans ha0
  · have hbγ : b (Fin.last (m.val + 1)) = γ := by
      change B (m.val + 1) = γ
      exact hB_last
    exact hbγ
  · intro j
    have hjle : j.val ≤ m.val := by omega
    rcases lt_or_eq_of_le hjle with hjlt | hjeq
    · have hj2 : j.val + 1 ≤ m.val := by omega
      have hbc : b j.castSucc = a ⟨j.val, by omega⟩ := by
        simp only [b, Fin.val_castSucc]
        exact hB_lt j.val hjle
      have hbs : b j.succ = a ⟨j.val + 1, by omega⟩ := by
        simp only [b, Fin.val_succ]
        exact hB_lt (j.val + 1) hj2
      rw [hbc, hbs]
      exact hpiece ⟨j.val, by omega⟩
    · have hjv : j.val = m.val := by omega
      have hbc : b j.castSucc = a ⟨m.val, by omega⟩ := by
        simp only [b, Fin.val_castSucc]
        rw [hjv]
        exact hB_lt m.val (le_refl m.val)
      have hbs : b j.succ = γ := by
        simp only [b, Fin.val_succ]
        rw [show j.val + 1 = m.val + 1 from by omega]
        exact hB_last
      rw [hbc, hbs]
      refine (hpiece ⟨m.val, by omega⟩).mono ?_
      exact Set.Icc_subset_Icc le_rfl hup

/-- **Splitting a partition above a point.**  If `h` is piecewise `C¹` on the partition
`a 0 = 0 < ⋯ < a k = 1` and `0 ≤ γ < 1`, then there is a partition of `[γ,1]` on whose pieces
`h` is `C¹`. -/
theorem exists_partition_split_right
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {h : ℝ → M} {k : ℕ} {a : Fin (k + 1) → ℝ}
    (hamono : StrictMono a) (ha0 : a 0 = 0) (ha1 : a (Fin.last k) = 1)
    (hpiece : ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (a j.castSucc) (a j.succ)))
    {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∃ (k2 : ℕ) (d : Fin (k2 + 1) → ℝ), StrictMono d ∧ d 0 = γ ∧ d (Fin.last k2) = 1 ∧
      ∀ j : Fin k2, ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (d j.castSucc) (d j.succ)) := by
  classical
  -- `m` is the largest index with `a m ≤ γ`.
  set S : Finset (Fin (k + 1)) := Finset.univ.filter (fun i => a i ≤ γ) with hS
  have h0 : (0 : Fin (k + 1)) ∈ S := by
    rw [hS, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by simpa [ha0] using hγ0⟩
  have hne : S.Nonempty := ⟨0, h0⟩
  set m : Fin (k + 1) := S.max' hne with hmdef
  have hmmem : m ∈ S := by rw [hmdef]; exact Finset.max'_mem S hne
  have hmle : a m ≤ γ := (Finset.mem_filter.mp hmmem).2
  have hmax : ∀ i ∈ S, i ≤ m := by intro i hi; rw [hmdef]; exact Finset.le_max' S i hi
  have hmk : m.val < k := by
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp m.isLt) with hlt | heq
    · exact hlt
    · exfalso
      have hlast : m = Fin.last k := Fin.ext heq
      rw [hlast, ha1] at hmle
      linarith
  have hup : γ < a ⟨m.val + 1, by omega⟩ := by
    by_contra hcon
    have hcon' : a ⟨m.val + 1, by omega⟩ ≤ γ := not_lt.mp hcon
    have hmem : (⟨m.val + 1, by omega⟩ : Fin (k + 1)) ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hcon'⟩
    have hle : (⟨m.val + 1, by omega⟩ : Fin (k + 1)) ≤ m := hmax _ hmem
    have h2 : m.val + 1 ≤ m.val := Fin.le_iff_val_le_val.mp hle
    omega
  -- Extension of the partition to `ℕ`: `γ` first, then the points of `a` above `γ`.
  let E : ℕ → ℝ := fun u => if _ : u ≤ k - m.val then max γ (a ⟨m.val + u, by omega⟩) else 1
  have hE : ∀ (u : ℕ) (hu : u ≤ k - m.val), E u = max γ (a ⟨m.val + u, by omega⟩) := by
    intro u hu
    simp only [E]
    exact dif_pos hu
  let d : Fin (k - m.val + 1) → ℝ := fun j => E j.val
  refine ⟨k - m.val, d, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have hval : i.val < j.val := hij
    have hjle : j.val ≤ k - m.val := by omega
    have hile : i.val ≤ k - m.val := by omega
    have hdi : d i = max γ (a ⟨m.val + i.val, by omega⟩) := by
      simp only [d]
      exact hE i.val hile
    have hdj : d j = max γ (a ⟨m.val + j.val, by omega⟩) := by
      simp only [d]
      exact hE j.val hjle
    rw [hdi, hdj]
    rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
    · have hfin : (⟨m.val + i.val, by omega⟩ : Fin (k + 1)) = m := by
        apply Fin.ext
        simp [hi0]
      have h1 : max γ (a ⟨m.val + i.val, by omega⟩) = γ := by
        rw [hfin]
        exact max_eq_left hmle
      have h2 : max γ (a ⟨m.val + j.val, by omega⟩) = a ⟨m.val + j.val, by omega⟩ := by
        apply max_eq_right
        have h : m.val + 1 ≤ m.val + j.val := by omega
        exact le_of_lt (lt_of_lt_of_le hup (hamono.monotone (Fin.mk_le_mk.mpr h)))
      rw [h1, h2]
      have h : m.val + 1 ≤ m.val + j.val := by omega
      exact lt_of_lt_of_le hup (hamono.monotone (Fin.mk_le_mk.mpr h))
    · have h1 : max γ (a ⟨m.val + i.val, by omega⟩) = a ⟨m.val + i.val, by omega⟩ := by
        apply max_eq_right
        have h : m.val + 1 ≤ m.val + i.val := by omega
        exact le_of_lt (lt_of_lt_of_le hup (hamono.monotone (Fin.mk_le_mk.mpr h)))
      have h2 : max γ (a ⟨m.val + j.val, by omega⟩) = a ⟨m.val + j.val, by omega⟩ := by
        apply max_eq_right
        have h : m.val + 1 ≤ m.val + j.val := by omega
        exact le_of_lt (lt_of_lt_of_le hup (hamono.monotone (Fin.mk_le_mk.mpr h)))
      rw [h1, h2]
      have h : m.val + i.val < m.val + j.val := by omega
      exact hamono (Fin.mk_lt_mk.mpr h)
  · have hd0 : d (0 : Fin (k - m.val + 1)) = max γ (a ⟨m.val + 0, by omega⟩) := by
      simp only [d]
      exact hE 0 (Nat.zero_le _)
    rw [hd0]
    exact max_eq_left hmle
  · have hdl : d (Fin.last (k - m.val)) = max γ (a ⟨m.val + (k - m.val), by omega⟩) := by
      simp only [d]
      rw [show ((Fin.last (k - m.val) : Fin (k - m.val + 1)) : ℕ) = k - m.val from rfl]
      exact hE (k - m.val) (le_refl _)
    rw [hdl]
    have hfin : (⟨m.val + (k - m.val), by omega⟩ : Fin (k + 1)) = Fin.last k := by
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    rw [hfin, ha1]
    exact max_eq_right hγ1.le
  · intro j
    have hjle : j.val ≤ k - m.val := by omega
    have hbc : d j.castSucc = max γ (a ⟨m.val + j.val, by omega⟩) := by
      simp only [d, Fin.val_castSucc]
      exact hE j.val hjle
    have hbs : d j.succ = max γ (a ⟨m.val + j.val + 1, by omega⟩) := by
      simp only [d, Fin.val_succ]
      exact hE (j.val + 1) (by omega)
    rw [hbc, hbs]
    rcases Nat.eq_zero_or_pos j.val with hj0 | hjpos
    · have hfin : (⟨m.val + j.val, by omega⟩ : Fin (k + 1)) = m := by
        apply Fin.ext
        simp [hj0]
      have hfin2 : (⟨m.val + j.val + 1, by omega⟩ : Fin (k + 1)) = ⟨m.val + 1, by omega⟩ := by
        apply Fin.ext
        simp [hj0]
      have h1 : max γ (a ⟨m.val + j.val, by omega⟩) = γ := by
        rw [hfin]
        exact max_eq_left hmle
      have h2 : max γ (a ⟨m.val + j.val + 1, by omega⟩) = a ⟨m.val + 1, by omega⟩ := by
        rw [hfin2]
        exact max_eq_right hup.le
      rw [h1, h2]
      refine (hpiece ⟨m.val, hmk⟩).mono ?_
      exact Set.Icc_subset_Icc hmle le_rfl
    · have h1 : max γ (a ⟨m.val + j.val, by omega⟩) = a ⟨m.val + j.val, by omega⟩ := by
        apply max_eq_right
        have h : m.val + 1 ≤ m.val + j.val := by omega
        exact le_of_lt (lt_of_lt_of_le hup (hamono.monotone (Fin.mk_le_mk.mpr h)))
      have h2 : max γ (a ⟨m.val + j.val + 1, by omega⟩) = a ⟨m.val + j.val + 1, by omega⟩ := by
        apply max_eq_right
        have h : m.val + 1 ≤ m.val + j.val + 1 := by omega
        exact le_of_lt (lt_of_lt_of_le hup (hamono.monotone (Fin.mk_le_mk.mpr h)))
      rw [h1, h2]
      exact hpiece ⟨m.val + j.val, by omega⟩

/-- **Reversing a partition.**  Given a partition of `[1/2,1]` on whose pieces `h` is `C¹`,
the reflected partition (via the order-reversing involution `Fin.rev`) is a partition of
`[0,1/2]` on whose pieces the reversed curve `s ↦ h (1 - s)` is `C¹`. -/
theorem exists_partition_reverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {h : ℝ → M} {k2 : ℕ} {d : Fin (k2 + 1) → ℝ}
    (hdmono : StrictMono d) (hd0 : d 0 = 1 / 2) (hd1 : d (Fin.last k2) = 1)
    (hpiece : ∀ j : Fin k2, ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (d j.castSucc) (d j.succ))) :
    ∃ (k3 : ℕ) (e : Fin (k3 + 1) → ℝ), StrictMono e ∧ e 0 = 0 ∧ e (Fin.last k3) = 1 / 2 ∧
      ∀ j : Fin k3, ContMDiffOn 𝓘(ℝ) I 1 (fun s : ℝ => h (1 - s))
        (Set.Icc (e j.castSucc) (e j.succ)) := by
  have hsm : ContMDiff 𝓘(ℝ) 𝓘(ℝ) 1 (fun s : ℝ => 1 - s) :=
    contMDiff_const.sub contMDiff_id
  refine ⟨k2, fun j => 1 - d (Fin.rev j), ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have h1 := i.add_rev_cast
    have h2 := j.add_rev_cast
    have hrev : (Fin.rev j).val < (Fin.rev i).val := by omega
    exact sub_lt_sub_left (hdmono hrev) 1
  · simp only [Fin.rev_zero, hd1]
    norm_num
  · simp only [Fin.rev_last, hd0]
    norm_num
  · intro j
    have hcs : (fun j : Fin (k2 + 1) => 1 - d (Fin.rev j)) j.castSucc
        = 1 - d ((Fin.rev j).succ) := by
      simp only []
      rw [Fin.rev_castSucc]
    have hsc : (fun j : Fin (k2 + 1) => 1 - d (Fin.rev j)) j.succ
        = 1 - d ((Fin.rev j).castSucc) := by
      simp only []
      rw [Fin.rev_succ]
    rw [hcs, hsc]
    refine ContMDiffOn.comp (hpiece (Fin.rev j)) hsm.contMDiffOn ?_
    intro x hx
    simp only [Set.mem_Icc, Set.mem_preimage] at hx ⊢
    constructor <;> linarith [hx.1, hx.2]

theorem exists_piecewise_partitions_halves
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    {h : ℝ → M} {k : ℕ} {a : Fin (k + 1) → ℝ}
    (hamono : StrictMono a) (ha0 : a 0 = 0) (ha1 : a (Fin.last k) = 1)
    (hpiece : ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (a j.castSucc) (a j.succ))) :
    (∃ (k1 : ℕ) (b : Fin (k1 + 1) → ℝ), StrictMono b ∧ b 0 = 0 ∧ b (Fin.last k1) = 1 / 2 ∧
        ∀ j : Fin k1, ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (b j.castSucc) (b j.succ))) ∧
    (∃ (k2 : ℕ) (d : Fin (k2 + 1) → ℝ), StrictMono d ∧ d 0 = 1 / 2 ∧ d (Fin.last k2) = 1 ∧
        ∀ j : Fin k2, ContMDiffOn 𝓘(ℝ) I 1 h (Set.Icc (d j.castSucc) (d j.succ))) ∧
    (∃ (k3 : ℕ) (e : Fin (k3 + 1) → ℝ), StrictMono e ∧ e 0 = 0 ∧ e (Fin.last k3) = 1 / 2 ∧
        ∀ j : Fin k3, ContMDiffOn 𝓘(ℝ) I 1 (fun s : ℝ => h (1 - s))
          (Set.Icc (e j.castSucc) (e j.succ))) := by
  refine ⟨?_, ?_, ?_⟩
  · exact exists_partition_split_left (γ := 1 / 2) hamono ha0 ha1 hpiece
      (by norm_num) (by norm_num)
  · exact exists_partition_split_right (γ := 1 / 2) hamono ha0 ha1 hpiece
      (by norm_num) (by norm_num)
  · obtain ⟨k2, d, hdmono, hd0, hd1, hdpiece⟩ :=
      exists_partition_split_right (γ := 1 / 2) hamono ha0 ha1 hpiece
        (by norm_num) (by norm_num)
    exact exists_partition_reverse hdmono hd0 hd1 hdpiece

end Work.OddBound.liftPiecewise
