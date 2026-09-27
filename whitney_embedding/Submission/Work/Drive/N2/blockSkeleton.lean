import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.exists_enum_critical
import Submission.Work.Drive.N2.criticalValueCover

/-!
# The block skeleton of the value axis (H7's lane)

`Work.Drive.N2.levelSeparatingMap_of_blocks` reduces the compact `n = 2` target to four
`GoodDrawingOn` rows per *critical value* (lower collar, window, upper collar, band), indexed by
`Fin n × Fin 4` with a strictly monotone `s : Fin (n+1) → ℝ` whose first `n` entries are the sorted
critical values (`s (last)` a dummy above them) and a single `η > 0` with `4η` smaller than every
consecutive gap.

This file supplies that datum: `Work.Drive.N2.exists_blockSkeleton`.  It is pure bookkeeping from the
enumerability of the critical set (`Work.Drive.N2.exists_enum_critical`) and Fermat's rule at the
extremes (`Work.Drive.N2.isCritical_of_forall_le'`, `..._ge`), together with the separation constant
`Work.Drive.N2.exists_gap_eps`.

The *content* exported is

* `s` strictly monotone, `η > 0`, `4η < 1`;
* `s (castSucc j) + 4η < s (succ j)` for every `j : Fin n` (the gaps, including the last one, where
  `s (succ (last)) = s (last)` is the dummy);
* **the critical values are exactly the `s (castSucc j)`** — hence any closed interval between two
  consecutive entries (shrunk by `3η/4` on each side) is critical-free, which is what makes the band
  rows reducible to `hflow`;
* `s 0` is the minimum of `f` and `s (castSucc ⟨n-1⟩)` its maximum, i.e. the skeleton covers the whole
  range `f '' M`.
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- `Fin.succ` as a `castSucc`, when the successor index is still `< n`. -/
lemma fin_succ_eq_castSucc {n : ℕ} {j : Fin n} (h : (j : ℕ) + 1 < n) :
    Fin.succ j = (⟨(j : ℕ) + 1, h⟩ : Fin n).castSucc := by
  ext; simp [Fin.succ, Fin.castSucc]

/-- `Fin.succ` is the last index, when the successor index leaves `Fin n`. -/
lemma fin_succ_eq_last {n : ℕ} {j : Fin n} (h : ¬ (j : ℕ) + 1 < n) :
    Fin.succ j = Fin.last n := by
  ext; simp [Fin.succ, Fin.last]; omega

open scoped Manifold ContDiff Topology in
open Work.Drive.Morse in
/-- **The block skeleton.**  For a Morse function with distinct critical values on a nonempty compact
surface there is a strictly monotone `s : Fin (n+1) → ℝ` (the critical values in the first `n` slots,
a dummy above at the last) and an `η > 0` such that the `4η`-separated blocks of
`Work.Drive.N2.blockSet s η` cover `f '' M` with the critical values exactly at the block centres, as
consumed by `Work.Drive.N2.levelSeparatingMap_of_blocks`. -/
theorem exists_blockSkeleton [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [Nonempty M] (f : M → ℝ) (hf : IsMorseDistinct f) :
    ∃ (n : ℕ) (hn : 0 < n) (s : Fin (n + 1) → ℝ) (η : ℝ),
      StrictMono s ∧ 0 < η ∧ 4 * η < 1 ∧
      (∀ j : Fin n, s (Fin.castSucc j) + 4 * η < s (Fin.succ j)) ∧
      (∀ t : ℝ, (∃ x : M, IsCritical f x ∧ f x = t) ↔ ∃ j : Fin n, t = s (Fin.castSucc j)) ∧
      (∀ x : M, s 0 ≤ f x ∧ f x ≤ s (Fin.castSucc ⟨n - 1, by omega⟩)) := by
  classical
  obtain ⟨k, p, hp_crit, hp_all⟩ := exists_enum_critical f hf.1 hf.2.1
  have hcont : Continuous f := hf.1.continuous
  obtain ⟨xmin, -, hxmin⟩ :=
    isCompact_univ.exists_isMinOn (Set.univ_nonempty) hcont.continuousOn
  obtain ⟨xmax, -, hxmax⟩ :=
    isCompact_univ.exists_isMaxOn (Set.univ_nonempty) hcont.continuousOn
  have hminf : ∀ y : M, f xmin ≤ f y := fun y => hxmin (mem_univ y)
  have hmaxf : ∀ y : M, f y ≤ f xmax := fun y => hxmax (mem_univ y)
  have hcrit_min : IsCritical f xmin := isCritical_of_forall_le' hf.1 hminf
  have hcrit_max : IsCritical f xmax := isCritical_of_forall_ge hf.1 hmaxf
  let CV : Finset ℝ := (Finset.univ : Finset (Fin k)).image (fun i => f (p i))
  have hmemCV : ∀ t : ℝ, t ∈ CV ↔ ∃ x : M, IsCritical f x ∧ f x = t := by
    intro t
    constructor
    · intro ht
      obtain ⟨i, -, hi⟩ := Finset.mem_image.mp ht
      exact ⟨p i, hp_crit i, hi⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := hp_all x hx
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, by rw [← hi]⟩
  have hCVne : CV.Nonempty := ⟨f xmin, (hmemCV _).mpr ⟨xmin, hcrit_min, rfl⟩⟩
  let n : ℕ := CV.card
  have hnpos : 0 < n := Finset.card_pos.mpr hCVne
  let s₀ : Fin n ↪o ℝ := CV.orderEmbOfFin (rfl : CV.card = n)
  have hs₀mono : StrictMono (fun i : Fin n => s₀ i) := OrderEmbedding.strictMono s₀
  have hs₀inj : Function.Injective (fun i : Fin n => s₀ i) := hs₀mono.injective
  have hs₀mem : ∀ i : Fin n, s₀ i ∈ CV := fun i => Finset.orderEmbOfFin_mem CV rfl i
  have hs₀surj : ∀ t ∈ CV, ∃ i : Fin n, s₀ i = t := by
    intro t ht
    have hr : t ∈ Set.range (fun i : Fin n => s₀ i) := by
      rw [show Set.range (fun i : Fin n => s₀ i) = (↑CV : Set ℝ) from
        Finset.range_orderEmbOfFin CV rfl]
      exact ht
    obtain ⟨i, hi⟩ := hr
    exact ⟨i, hi⟩
  have hs₀zero : s₀ ⟨0, hnpos⟩ = CV.min' hCVne := Finset.orderEmbOfFin_zero rfl hnpos
  have hs₀last : s₀ ⟨n - 1, by omega⟩ = CV.max' hCVne := Finset.orderEmbOfFin_last rfl hnpos
  obtain ⟨ε, hεpos, hεhalf, hεgap⟩ := exists_gap_eps (fun i : Fin n => s₀ i) hs₀inj
  let m : Fin n := ⟨n - 1, by omega⟩
  let s : Fin (n + 1) → ℝ :=
    fun i => if h : (i : ℕ) < n then s₀ ⟨(i : ℕ), h⟩ else s₀ m + 1
  have hsc : ∀ i : Fin n, s (Fin.castSucc i) = s₀ i := by
    intro i
    show (if h : ((Fin.castSucc i : Fin (n + 1)) : ℕ) < n then
      s₀ ⟨((Fin.castSucc i : Fin (n + 1)) : ℕ), h⟩ else s₀ m + 1) = s₀ i
    rw [dif_pos (by simpa [Fin.castSucc] using i.isLt)]
    exact congrArg s₀ (Fin.ext rfl)
  have hslast : s (Fin.last n) = s₀ m + 1 := by
    show (if h : ((Fin.last n : Fin (n + 1)) : ℕ) < n then
      s₀ ⟨((Fin.last n : Fin (n + 1)) : ℕ), h⟩ else s₀ m + 1) = s₀ m + 1
    rw [dif_neg (by simp [Fin.last])]
  have hsucc : ∀ j : Fin n, s (Fin.succ j) =
      (if h : (j : ℕ) + 1 < n then s₀ ⟨(j : ℕ) + 1, h⟩ else s₀ m + 1) := by
    intro j
    show (if h : ((Fin.succ j : Fin (n + 1)) : ℕ) < n then
      s₀ ⟨((Fin.succ j : Fin (n + 1)) : ℕ), h⟩ else s₀ m + 1) = _
    rw [Fin.val_succ]
  have hηpos : 0 < ε / 3 := div_pos hεpos (by norm_num)
  have hηsmall : 4 * (ε / 3) < 1 := by linarith [hεhalf]
  have hgap : ∀ j : Fin n, s (Fin.castSucc j) + 4 * (ε / 3) < s (Fin.succ j) := by
    intro j
    rw [hsc j, hsucc j]
    by_cases hj : (j : ℕ) + 1 < n
    · rw [dif_pos hj]
      have hne : j ≠ (⟨(j : ℕ) + 1, hj⟩ : Fin n) := by
        intro hcon
        have hv : (j : ℕ) = (j : ℕ) + 1 := congrArg Fin.val hcon
        omega
      have hg := hεgap j ⟨(j : ℕ) + 1, hj⟩ hne
      have hlt : s₀ j < s₀ ⟨(j : ℕ) + 1, hj⟩ := hs₀mono (by simp only [Fin.lt_def]; omega)
      rw [abs_of_neg (sub_neg.mpr hlt)] at hg
      linarith
    · rw [dif_neg hj]
      have hjm : j = m := by
        refine Fin.ext ?_
        simp only [m]
        omega
      rw [hjm]
      linarith
  have hmono : StrictMono s := by
    rw [Fin.strictMono_iff_lt_succ]
    intro i
    linarith [hgap i, hηpos]
  refine ⟨n, hnpos, s, ε / 3, hmono, hηpos, hηsmall, hgap, ?_, ?_⟩
  · intro t
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, hi⟩ := hs₀surj (f x) ((hmemCV _).mpr ⟨x, hx, rfl⟩)
      exact ⟨i, by rw [hsc i]; exact hi.symm⟩
    · rintro ⟨j, rfl⟩
      exact (hmemCV _).mp (by rw [hsc j]; exact hs₀mem j)
  · intro x
    constructor
    · have h0 : s 0 = s₀ ⟨0, hnpos⟩ := by
        have h1 : (0 : Fin (n + 1)) = (⟨0, hnpos⟩ : Fin n).castSucc := Fin.ext rfl
        rw [h1, hsc]
      have hmin : CV.min' hCVne ≤ f xmin :=
        Finset.min'_le CV (f xmin) ((hmemCV _).mpr ⟨xmin, hcrit_min, rfl⟩)
      rw [h0, hs₀zero]
      exact le_trans hmin (hminf x)
    · have htop : s (Fin.castSucc ⟨n - 1, by omega⟩) = CV.max' hCVne := by
        have h1 : (⟨n - 1, by omega⟩ : Fin n) = m := Fin.ext rfl
        rw [h1, hsc m, hs₀last]
      have hmax : f xmax ≤ CV.max' hCVne :=
        Finset.le_max' CV (f xmax) ((hmemCV _).mpr ⟨xmax, hcrit_max, rfl⟩)
      rw [htop]
      exact le_trans (hmaxf x) hmax

end Work.Drive.N2
