import Mathlib
import Submission.Work.OddBound.polygonValue.balancing.Book

namespace Work.OddBound.polygonValue.balancing

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval


section Pieces

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]

/-! ## 0. Auxiliary facts about the cumulative side lengths -/

/-- **A run of zero-length sides does not change the cumulative length.** -/
theorem cumLen_eq_of_sideLen_eq_zero {p : M} {N : ℕ} {w : ℝ → Fin (N - 1) → M} {τ : ℝ}
    {i j : ℕ} (hij : i ≤ j)
    (h : ∀ l, i ≤ l → l < j → sideLen (I := I) p w τ l = 0) :
    cumLen (I := I) p w τ i = cumLen (I := I) p w τ j := by
  revert h
  refine Nat.le_induction (fun _ => rfl) ?_ j hij
  intro n hin ih h
  rw [cumLen_succ (I := I) p w τ n, h n hin (Nat.lt_succ_self n), add_zero]
  exact ih fun l hl hln => h l hl (lt_trans hln (Nat.lt_succ_self n))

/-- **Between two breakpoints (ends of positive sides, or `0`) the cumulative length strictly
increases.** -/
theorem cumLen_lt_of_lt_of_break {p : M} {N : ℕ} {w : ℝ → Fin (N - 1) → M} {τ : ℝ}
    {m m' : ℕ} (_hm : m = 0 ∨ 0 < sideLen (I := I) p w τ (m - 1))
    (hm' : m' = 0 ∨ 0 < sideLen (I := I) p w τ (m' - 1)) (hlt : m < m') :
    cumLen (I := I) p w τ m < cumLen (I := I) p w τ m' := by
  rcases lt_or_eq_of_le (cumLen_mono (I := I) p w τ (le_of_lt hlt)) with h | h
  · exact h
  · exfalso
    have hm1 : 1 ≤ m' := by omega
    have hle1 : cumLen (I := I) p w τ m ≤ cumLen (I := I) p w τ (m' - 1) :=
      cumLen_mono (I := I) p w τ (by omega)
    have hsucc : cumLen (I := I) p w τ m' = cumLen (I := I) p w τ (m' - 1)
        + sideLen (I := I) p w τ (m' - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hm1]
      exact cumLen_succ (I := I) p w τ (m' - 1)
    have hnn := sideLen_nonneg (I := I) p w τ (m' - 1)
    have hsz : sideLen (I := I) p w τ (m' - 1) = 0 := by linarith
    rcases hm' with h' | h'
    · omega
    · rw [hsz] at h'; exact lt_irrefl 0 h'

/-! ## 1. The side index of an arclength in the interior of a side -/

/-- **The side index of an arclength in the interior of the side `m` is `m`.** -/
theorem gIdx_eq_of_lt_cumLen {p : M} {N : ℕ} {w : ℝ → Fin (N - 1) → M} {τ A : ℝ} {m : ℕ}
    (hm : m + 1 ≤ N) (hA0 : cumLen (I := I) p w τ m ≤ A)
    (hA1 : A < cumLen (I := I) p w τ (m + 1)) :
    gIdx (I := I) p w τ A = m := by
  have hset : (Finset.range N).filter (fun j => cumLen (I := I) p w τ j ≤ A)
      = Finset.range (m + 1) := by
    apply Finset.ext
    intro j
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_range]
    constructor
    · rintro ⟨hjN, hj⟩
      by_contra hcon
      push Not at hcon
      exact absurd hA1 (not_lt.mpr (le_trans (cumLen_mono (I := I) p w τ hcon) hj))
    · intro hj
      exact ⟨by omega, le_trans (cumLen_mono (I := I) p w τ (Nat.le_of_lt_succ hj)) hA0⟩
  rw [gIdx_def, hset, Finset.card_range]
  omega

/-! ## 2. The point of the broken geodesic on a side -/

/-- **The point of the broken geodesic at an arclength on the positive side `m`.**  For
`cumLen τ m ≤ A ≤ cumLen τ (m+1)` with `sideLen τ m > 0`, the broken geodesic is the side curve
`S m · τ` at the (clamped) side parameter. -/
theorem gPt_eq_side {p : M} {N : ℕ} {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M}
    {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hN : 0 < N) {m : ℕ} (hm : m < N) (hpos : 0 < sideLen (I := I) p w τ m) {A : ℝ}
    (hA0 : cumLen (I := I) p w τ m ≤ A) (hA1 : A ≤ cumLen (I := I) p w τ (m + 1)) :
    gPt (I := I) p hN w S τ A
      = S ⟨m, hm⟩ (clamp01 ((A - cumLen (I := I) p w τ m)
          / sideLen (I := I) p w τ m)) τ := by
  rcases lt_or_eq_of_le hA1 with hlt | heq
  · have hidx : gIdx (I := I) p w τ A = m :=
      gIdx_eq_of_lt_cumLen (I := I) (by omega) hA0 hlt
    have hfin : gFin (I := I) p hN w τ A = ⟨m, hm⟩ := by
      apply Fin.ext
      rw [gFin_val, hidx]
    rw [gPt_def, hfin, gPrm_def, hidx]
  · subst heq
    rw [gPt_cumLen_eq_gonVert (I := I) hτ hSsm hS0 hS1 hSlen hN (by omega : m + 1 ≤ N)]
    have hq : (cumLen (I := I) p w τ (m + 1) - cumLen (I := I) p w τ m)
        / sideLen (I := I) p w τ m = 1 := by
      rw [cumLen_succ (I := I) p w τ m]
      field_simp
      ring
    rw [hq, clamp01_eq_one_of_one_le le_rfl, hS1 ⟨m, hm⟩ τ hτ]

end Pieces


/-- The arclength-balanced loop is, on each side of positive length, an affine reparametrisation of
that side curve, and the pieces form a partition of `[0,1]` on which the loop is `C¹`.

Hint: enumerate the positive sides.  With `E := {0} ∪ {i + 1 | i ∈ Finset.range N, 0 < sideLen τ i}`
(a `Finset ℕ`, containing `0`) and `e := (E.orderIsoOfFin hcard : Fin E.card ≃o ↥E)`, take
`k := E.card - 1`, `a j := cumLen τ (e j) / totLen τ` and `i j` the side `e (j+1) - 1`.  Then
`sideLen` is strictly positive on these sides, `cumLen` is strictly increasing along `E`, and
`cumLen τ (max E) = totLen τ`, so `a` is strictly monotone with `a 0 = 0` and `a (Fin.last k) = 1`.
On the piece `[a j, a j.succ]` the side index `gIdx τ (totLen τ * s)` equals `i j` (in the interior
because positive side lengths block ties in the cumulative lengths), which gives the displayed
formula; at the closed endpoints use `hS0`/`hS1` together with
`Work.OddBound.polygonValue.gPt_cumLen_eq_gonVert` and
`Work.OddBound.polygonValue.eq_gonVert_of_cumLen_eq` (runs of zero-length sides).
`ContMDiffOn` follows from `hSsm` composed with the affine reparametrisation
`s ↦ (totLen τ * s - cumLen τ (i j)) / sideLen τ (i j)`, which maps the piece into `Icc 0 1`, using
`Work.OddBound.polygonValue.gLoop`'s defining formula and `ContMDiffOn.congr`. -/
theorem gLoop_pieces
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {p : M} {N : ℕ} (hN : 0 < N) {w : ℝ → Fin (N - 1) → M} {S : Fin N → ℝ → ℝ → M} {τ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hSsm : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      ContMDiffOn 𝓘(ℝ) I 1 (fun r : ℝ => S i r τ) (Set.Icc (0 : ℝ) 1))
    (hS0 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 0 τ = Work.OddBound.gonVert p (w τ) (i : ℕ))
    (hS1 : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 →
      S i 1 τ = Work.OddBound.gonVert p (w τ) ((i : ℕ) + 1))
    (hSlen : ∀ (i : Fin N) (τ : ℝ), τ ∈ Set.Icc (0 : ℝ) 1 → ∀ a b : ℝ,
      0 ≤ a → a ≤ b → b ≤ 1 →
      Submission.Length.curveLength (I := I) (fun r : ℝ => S i r τ) a b
        = (b - a) * Work.OddBound.gonSideLen (I := I) p (w τ) (i : ℕ))
    (hT : 0 < Work.OddBound.polygonValue.totLen (I := I) p w τ) :
    ∃ (k : ℕ) (a : Fin (k + 1) → ℝ) (i : Fin k → Fin N),
      StrictMono a ∧ a 0 = 0 ∧ a (Fin.last k) = 1 ∧
      (∀ j : Fin k, 0 < Work.OddBound.polygonValue.sideLen (I := I) p w τ (i j)) ∧
      (∀ j : Fin k,
        a j.castSucc = Work.OddBound.polygonValue.cumLen (I := I) p w τ (i j)
          / Work.OddBound.polygonValue.totLen (I := I) p w τ) ∧
      (∀ j : Fin k,
        a j.succ = Work.OddBound.polygonValue.cumLen (I := I) p w τ ((i j : ℕ) + 1)
          / Work.OddBound.polygonValue.totLen (I := I) p w τ) ∧
      (∀ (j : Fin k) (s : ℝ), s ∈ Set.Icc (a j.castSucc) (a j.succ) →
        Work.OddBound.polygonValue.gLoop (I := I) p hN w S τ s
          = S (i j) ((Work.OddBound.polygonValue.totLen (I := I) p w τ * s
                - Work.OddBound.polygonValue.cumLen (I := I) p w τ (i j))
              / Work.OddBound.polygonValue.sideLen (I := I) p w τ (i j)) τ) ∧
      (∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1
        (fun s : ℝ => Work.OddBound.polygonValue.gLoop (I := I) p hN w S τ s)
        (Set.Icc (a j.castSucc) (a j.succ))) := by
  classical
  -- ## The set of breakpoints: `0` together with the ends of the positive sides
  set B : Finset ℕ := (Finset.range (N + 1)).filter
    (fun m => m = 0 ∨ 0 < sideLen (I := I) p w τ (m - 1)) with hB
  have h0B : (0 : ℕ) ∈ B := by
    rw [hB, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Or.inl rfl⟩
  have hNB : ∀ m ∈ B, m ≤ N := by
    intro m hm
    rw [hB, Finset.mem_filter, Finset.mem_range] at hm
    omega
  have hmemB : ∀ m, m ≤ N → (m ∈ B ↔ m = 0 ∨ 0 < sideLen (I := I) p w τ (m - 1)) := by
    intro m hm
    rw [hB, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun h => h.2, fun h => ⟨by omega, h⟩⟩
  -- ## The increasing enumeration of the breakpoints
  set k : ℕ := B.card - 1 with hk
  have hc : B.card = k + 1 := by
    have h1 : 1 ≤ B.card := Finset.card_pos.mpr ⟨0, h0B⟩
    omega
  set eo := B.orderEmbOfFin hc with heo
  have e_mono : StrictMono eo := by
    rw [heo]; exact (B.orderEmbOfFin hc).strictMono
  have e_mem : ∀ j, eo j ∈ B := by
    intro j; rw [heo]; exact B.orderEmbOfFin_mem hc j
  have e_lt_iff : ∀ {a b : Fin (k + 1)}, eo a < eo b ↔ a < b := by
    intro a b; rw [heo]; exact (B.orderEmbOfFin hc).lt_iff_lt
  have e_range : Set.range eo = (↑B : Set ℕ) := by
    rw [heo]; exact Finset.range_orderEmbOfFin B hc
  have e_zero : eo 0 = 0 := by
    have h0r : (0 : ℕ) ∈ Set.range eo := by rw [e_range]; exact h0B
    obtain ⟨j, hj⟩ := h0r
    have hle : eo 0 ≤ eo j := e_mono.monotone (Fin.zero_le j)
    omega
  have e_succ_pos : ∀ j : Fin k, 1 ≤ eo j.succ := by
    intro j
    have hlt : (0 : Fin (k + 1)) < j.succ := by simp [Fin.lt_def]
    have h := e_mono hlt
    rw [e_zero] at h
    omega
  have e_last : ∀ y ∈ B, y ≤ eo (Fin.last k) := by
    intro y hy
    have hyr : y ∈ Set.range eo := by rw [e_range]; exact hy
    obtain ⟨j, hj⟩ := hyr
    rw [← hj]
    exact e_mono.monotone (Fin.le_last j)
  -- ## The sides and the balanced partition
  have hi_lt : ∀ j : Fin k, eo j.succ - 1 < N := by
    intro j
    have h1 := e_succ_pos j
    have h2 := hNB _ (e_mem j.succ)
    omega
  set i : Fin k → Fin N := fun j => ⟨eo j.succ - 1, hi_lt j⟩ with hi
  have hi_val : ∀ j : Fin k, ((i j : Fin N) : ℕ) = eo j.succ - 1 := by
    intro j; rw [hi]
  have hi_pos : ∀ j : Fin k, 0 < sideLen (I := I) p w τ (i j) := by
    intro j
    have hmem : eo j.succ = 0 ∨ 0 < sideLen (I := I) p w τ (eo j.succ - 1) :=
      (hmemB _ (hNB _ (e_mem j.succ))).mp (e_mem j.succ)
    rcases hmem with h | h
    · exact absurd h (by have hh := e_succ_pos j; omega)
    · rw [← hi_val j] at h
      exact h
  set a : Fin (k + 1) → ℝ := fun j => cumLen (I := I) p w τ (eo j)
      / totLen (I := I) p w τ with ha
  have ha_apply : ∀ j : Fin (k + 1),
      a j = cumLen (I := I) p w τ (eo j) / totLen (I := I) p w τ := by
    intro j; rw [ha]
  -- the cumulative length is strictly increasing along the breakpoints
  have hcum_mono : StrictMono (fun j : Fin (k + 1) => cumLen (I := I) p w τ (eo j)) := by
    intro j j' hjj
    exact cumLen_lt_of_lt_of_break (I := I)
      ((hmemB _ (hNB _ (e_mem j))).mp (e_mem j))
      ((hmemB _ (hNB _ (e_mem j'))).mp (e_mem j'))
      (e_mono hjj)
  have ha_mono : StrictMono a := by
    rw [ha]
    intro j j' hjj
    exact div_lt_div_of_pos_right (hcum_mono hjj) hT
  have ha_zero : a 0 = 0 := by
    rw [ha_apply 0, e_zero, cumLen_zero, zero_div]
  have hcum_last : cumLen (I := I) p w τ (eo (Fin.last k)) = totLen (I := I) p w τ := by
    have hMN : eo (Fin.last k) ≤ N := hNB _ (e_mem _)
    have hzero : ∀ l, eo (Fin.last k) ≤ l → l < N →
        sideLen (I := I) p w τ l = 0 := by
      intro l hl hlN
      have hl1 : l + 1 ≤ N := by omega
      have hnotmem : l + 1 ∉ B := by
        intro hmem
        have hh := e_last (l + 1) hmem
        omega
      have h : ¬ (l + 1 = 0 ∨ 0 < sideLen (I := I) p w τ (l + 1 - 1)) :=
        fun hh => hnotmem ((hmemB (l + 1) hl1).mpr hh)
      have h2 : ¬ (0 < sideLen (I := I) p w τ l) := fun hpos' =>
        h (Or.inr (by simpa using hpos'))
      exact le_antisymm (le_of_not_gt h2) (sideLen_nonneg (I := I) p w τ l)
    rw [totLen_eq_cumLen (I := I) p w τ]
    exact cumLen_eq_of_sideLen_eq_zero (I := I) hMN hzero
  have ha_last : a (Fin.last k) = 1 := by
    rw [ha_apply (Fin.last k), hcum_last, div_self (ne_of_gt hT)]
  -- ## The cumulative length at the ends of each positive side
  have hi_castSucc : ∀ j : Fin k, cumLen (I := I) p w τ (eo j.castSucc)
      = cumLen (I := I) p w τ (i j) := by
    intro j
    have hle : eo j.castSucc ≤ (i j : ℕ) := by
      have h1 := e_mono (Fin.castSucc_lt_succ (i := j))
      have h2 := hi_val j
      have h3 := e_succ_pos j
      omega
    refine cumLen_eq_of_sideLen_eq_zero (I := I) hle ?_
    intro l hl hlj
    have h1 : eo j.castSucc < l + 1 := by omega
    have h2 : l + 1 < eo j.succ := by
      have hh := hi_val j
      have h3 := e_succ_pos j
      omega
    have hnotmem : l + 1 ∉ B := by
      intro hmem
      have hyr : l + 1 ∈ Set.range eo := by rw [e_range]; exact hmem
      obtain ⟨j'', hj''⟩ := hyr
      have ha1 : eo j.castSucc < eo j'' := by rw [hj'']; exact h1
      have ha2 : eo j'' < eo j.succ := by rw [hj'']; exact h2
      have hb1 : j.castSucc < j'' := eo.lt_iff_lt.mp ha1
      have hb2 : j'' < j.succ := eo.lt_iff_lt.mp ha2
      have hv1 : (j : ℕ) < (j'' : ℕ) := by
        have := hb1
        rw [Fin.lt_def, Fin.val_castSucc] at this
        exact this
      have hv2 : (j'' : ℕ) < (j : ℕ) + 1 := by
        have := hb2
        rw [Fin.lt_def, Fin.val_succ] at this
        exact this
      omega
    have hl1 : l + 1 ≤ N := by
      have hh := hi_val j
      have hh2 := hNB _ (e_mem j.succ)
      omega
    have h : ¬ (l + 1 = 0 ∨ 0 < sideLen (I := I) p w τ (l + 1 - 1)) :=
      fun hh => hnotmem ((hmemB (l + 1) hl1).mpr hh)
    have h2' : ¬ (0 < sideLen (I := I) p w τ l) := fun hpos' =>
      h (Or.inr (by simpa using hpos'))
    exact le_antisymm (le_of_not_gt h2') (sideLen_nonneg (I := I) p w τ l)
  have hi_succ : ∀ j : Fin k, cumLen (I := I) p w τ (eo j.succ)
      = cumLen (I := I) p w τ ((i j : ℕ) + 1) := by
    intro j
    have h : (i j : ℕ) + 1 = eo j.succ := by
      rw [hi_val j]
      exact Nat.sub_add_cancel (e_succ_pos j)
    rw [h]
  have ha_castSucc : ∀ j : Fin k, a j.castSucc
      = cumLen (I := I) p w τ (i j) / totLen (I := I) p w τ := by
    intro j; rw [ha_apply j.castSucc, hi_castSucc j]
  have ha_succ : ∀ j : Fin k, a j.succ
      = cumLen (I := I) p w τ ((i j : ℕ) + 1) / totLen (I := I) p w τ := by
    intro j; rw [ha_apply j.succ, hi_succ j]
  -- ## The arclength of the side `i j` ranges over `[cumLen τ (i j), cumLen τ (i j + 1)]`
  have hA_bounds : ∀ (j : Fin k) (s : ℝ), s ∈ Set.Icc (a j.castSucc) (a j.succ) →
      cumLen (I := I) p w τ (i j) ≤ totLen (I := I) p w τ * s ∧
        totLen (I := I) p w τ * s ≤ cumLen (I := I) p w τ ((i j : ℕ) + 1) := by
    intro j s hs
    constructor
    · have h1 : totLen (I := I) p w τ * a j.castSucc ≤ totLen (I := I) p w τ * s :=
        mul_le_mul_of_nonneg_left hs.1 (le_of_lt hT)
      have h2 : totLen (I := I) p w τ * a j.castSucc = cumLen (I := I) p w τ (i j) := by
        rw [ha_apply j.castSucc, hi_castSucc j]
        exact mul_div_cancel₀ _ (ne_of_gt hT)
      rwa [h2] at h1
    · have h1 : totLen (I := I) p w τ * s ≤ totLen (I := I) p w τ * a j.succ :=
        mul_le_mul_of_nonneg_left hs.2 (le_of_lt hT)
      have h2 : totLen (I := I) p w τ * a j.succ = cumLen (I := I) p w τ ((i j : ℕ) + 1) := by
        rw [ha_apply j.succ, hi_succ j]
        exact mul_div_cancel₀ _ (ne_of_gt hT)
      rwa [h2] at h1
  -- ## The loop on each piece is the side curve
  have hpiece : ∀ (j : Fin k) (s : ℝ), s ∈ Set.Icc (a j.castSucc) (a j.succ) →
      gLoop (I := I) p hN w S τ s
        = S (i j) ((totLen (I := I) p w τ * s - cumLen (I := I) p w τ (i j))
              / sideLen (I := I) p w τ (i j)) τ := by
    intro j s hs
    obtain ⟨hA0, hA1⟩ := hA_bounds j s hs
    rw [gLoop_def]
    have hside := gPt_eq_side (I := I) (p := p) (w := w) (S := S) (τ := τ) hτ hSsm hS0 hS1 hSlen
      hN (m := (i j : ℕ)) (i j).isLt (hi_pos j) hA0 hA1
    rw [hside]
    have hclamp : clamp01 ((totLen (I := I) p w τ * s - cumLen (I := I) p w τ (i j))
        / sideLen (I := I) p w τ (i j))
        = (totLen (I := I) p w τ * s - cumLen (I := I) p w τ (i j))
          / sideLen (I := I) p w τ (i j) := by
      refine clamp01_eq_self (div_nonneg (by linarith) (le_of_lt (hi_pos j))) ?_
      rw [div_le_one (hi_pos j)]
      have hsub := sideLen_eq_sub (I := I) p w τ (i j : ℕ)
      linarith
    rw [hclamp]
  -- ## Smoothness of the loop on each piece
  have hcont : ∀ j : Fin k, ContMDiffOn 𝓘(ℝ) I 1
      (fun s : ℝ => gLoop (I := I) p hN w S τ s)
      (Set.Icc (a j.castSucc) (a j.succ)) := by
    intro j
    have hcomp : ContMDiffOn 𝓘(ℝ) I 1
        (fun s : ℝ => S (i j) ((totLen (I := I) p w τ * s
            - cumLen (I := I) p w τ (i j)) / sideLen (I := I) p w τ (i j)) τ)
        (Set.Icc (a j.castSucc) (a j.succ)) := by
      refine (hSsm (i j) τ hτ).comp ?_ ?_
      · exact (show ContDiffOn ℝ 1 (fun s : ℝ =>
            (totLen (I := I) p w τ * s - cumLen (I := I) p w τ (i j))
              / sideLen (I := I) p w τ (i j))
            (Set.Icc (a j.castSucc) (a j.succ)) from by fun_prop).contMDiffOn
      · intro s hs
        obtain ⟨hA0, hA1⟩ := hA_bounds j s hs
        constructor
        · exact div_nonneg (by linarith) (le_of_lt (hi_pos j))
        · rw [div_le_one (hi_pos j)]
          have hsub := sideLen_eq_sub (I := I) p w τ (i j : ℕ)
          linarith
    exact hcomp.congr (fun s hs => hpiece j s hs)
  exact ⟨k, a, i, ha_mono, ha_zero, ha_last, hi_pos, ha_castSucc, ha_succ, hpiece, hcont⟩


end Work.OddBound.polygonValue.balancing
