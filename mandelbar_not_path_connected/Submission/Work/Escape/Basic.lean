import Submission.Work.Escape.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Basic API of the escape / Green-function chapter

Continuity and norm bounds for `Td`, `Tpoly`, `Tantibar`; the `MonicGrowth` instances; the API of
`log⁺`; continuity of the partial Green functions; and elementary facts about the escaping region
and the filled Julia set.
-/

open Filter Function Metric Set
open scoped Topology

noncomputable section

namespace Work.Escape

variable {f : ℂ → ℂ} {d : ℕ} {A M : ℝ} {z w : ℂ} {n : ℕ}

/-! ## The positive part of the logarithm -/

@[simp] theorem logPos_def (x : ℝ) : logPos x = Real.log (max 1 x) := rfl

theorem logPos_nonneg (x : ℝ) : 0 ≤ logPos x := Real.log_nonneg (le_max_left 1 x)

theorem logPos_eq_log {x : ℝ} (hx : 1 ≤ x) : logPos x = Real.log x := by
  rw [logPos_def, max_eq_right hx]

theorem logPos_eq_zero {x : ℝ} (hx : x ≤ 1) : logPos x = 0 := by
  rw [logPos_def, max_eq_left hx, Real.log_one]

theorem logPos_pos {x : ℝ} (hx : 1 < x) : 0 < logPos x := by
  rw [logPos_eq_log hx.le]; exact Real.log_pos hx

theorem logPos_mono {x y : ℝ} (h : x ≤ y) : logPos x ≤ logPos y :=
  Real.log_le_log (by positivity) (max_le_max le_rfl h)

theorem log_le_logPos {x : ℝ} (hx : 0 < x) : Real.log x ≤ logPos x := by
  rcases le_or_gt 1 x with h | h
  · rw [logPos_eq_log h]
  · rw [logPos_eq_zero h.le]; exact Real.log_nonpos hx.le h.le

/-! ## The maps -/

theorem continuous_Td (d : ℕ) (c : ℂ) : Continuous (Td d c) :=
  (continuous_star.pow d).add continuous_const

theorem continuous_Tpoly (d : ℕ) (c : ℂ) : Continuous (Tpoly d c) :=
  (continuous_id.pow d).add continuous_const

theorem norm_Td_le (d : ℕ) (c z : ℂ) : ‖Td d c z‖ ≤ ‖z‖ ^ d + ‖c‖ := by
  refine (norm_add_le ((starRingEnd ℂ z) ^ d) c).trans (le_of_eq ?_)
  rw [norm_pow, Complex.norm_conj]

theorem norm_Td_ge (d : ℕ) (c z : ℂ) : ‖z‖ ^ d - ‖c‖ ≤ ‖Td d c z‖ := by
  have h : ‖(starRingEnd ℂ z) ^ d‖ ≤ ‖(starRingEnd ℂ z) ^ d + c‖ + ‖c‖ := by
    simpa using norm_add_le ((starRingEnd ℂ z) ^ d + c) (-c)
  rw [norm_pow, Complex.norm_conj] at h
  rw [Td]
  linarith

theorem norm_Tpoly_le (d : ℕ) (c z : ℂ) : ‖Tpoly d c z‖ ≤ ‖z‖ ^ d + ‖c‖ := by
  refine (norm_add_le (z ^ d) c).trans (le_of_eq ?_)
  rw [norm_pow]

theorem norm_Tpoly_ge (d : ℕ) (c z : ℂ) : ‖z‖ ^ d - ‖c‖ ≤ ‖Tpoly d c z‖ := by
  have h : ‖z ^ d‖ ≤ ‖z ^ d + c‖ + ‖c‖ := by simpa using norm_add_le (z ^ d + c) (-c)
  rw [norm_pow] at h
  rw [Tpoly]
  linarith

theorem monicGrowth_Td (d : ℕ) (c : ℂ) : MonicGrowth (Td d c) d ‖c‖ :=
  ⟨continuous_Td d c, norm_Td_le d c, norm_Td_ge d c⟩

theorem monicGrowth_Tpoly (d : ℕ) (c : ℂ) : MonicGrowth (Tpoly d c) d ‖c‖ :=
  ⟨continuous_Tpoly d c, norm_Tpoly_le d c, norm_Tpoly_ge d c⟩

/-- The mandelbar (tricorn) iterator `z ↦ z̄² + c` has degree `2` and growth constant `‖c‖`. -/
theorem monicGrowth_Tantibar (c : ℂ) :
    MonicGrowth (LeanEval.ComplexAnalysis.Tantibar c) 2 ‖c‖ :=
  monicGrowth_Td 2 c

theorem MonicGrowth.continuous_iterate (h : MonicGrowth f d A) (n : ℕ) : Continuous (f^[n]) :=
  h.continuous.iterate n

/-! ## The partial Green functions -/

@[simp] theorem greenIter_def (f : ℂ → ℂ) (d : ℕ) (z : ℂ) (n : ℕ) :
    greenIter f d z n = ((d : ℝ) ^ n)⁻¹ * logPos ‖(f^[n]) z‖ := rfl

theorem greenIter_nonneg (f : ℂ → ℂ) (d : ℕ) (z : ℂ) (n : ℕ) : 0 ≤ greenIter f d z n :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg d) n)) (logPos_nonneg _)

theorem greenIter_eq_of_one_le {f : ℂ → ℂ} {d : ℕ} {z : ℂ} {n : ℕ}
    (h : 1 ≤ ‖(f^[n]) z‖) : greenIter f d z n = ((d : ℝ) ^ n)⁻¹ * Real.log ‖(f^[n]) z‖ := by
  rw [greenIter_def, logPos_eq_log h]

theorem greenIter_le_of_norm_le {f : ℂ → ℂ} {d : ℕ} {z : ℂ} {n : ℕ} {M : ℝ} (hM : 1 ≤ M)
    (h : ‖(f^[n]) z‖ ≤ M) : greenIter f d z n ≤ ((d : ℝ) ^ n)⁻¹ * Real.log M := by
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg d) n))
  exact (logPos_mono h).trans (le_of_eq (logPos_eq_log hM))

theorem continuous_greenIter (hf : Continuous f) (d : ℕ) (n : ℕ) :
    Continuous fun z : ℂ => greenIter f d z n := by
  have h2 : Continuous fun z : ℂ => max 1 ‖(f^[n]) z‖ :=
    continuous_const.max (hf.iterate n).norm
  have h3 : Continuous fun z : ℂ => Real.log (max 1 ‖(f^[n]) z‖) :=
    h2.log fun z => by
      have : (1 : ℝ) ≤ max 1 ‖(f^[n]) z‖ := le_max_left _ _
      linarith
  have : (fun z : ℂ => greenIter f d z n) = fun z => ((d : ℝ) ^ n)⁻¹ * Real.log (max 1 ‖(f^[n]) z‖) := by
    funext z
    rw [greenIter_def, logPos_def]
  rw [this]
  exact continuous_const.mul h3

/-! ## The escaping region -/

theorem mem_escapeRegion {A : ℝ} {z : ℂ} : z ∈ escapeRegion A ↔ max 2 A < ‖z‖ := Iff.rfl

theorem escapeRegion_open (A : ℝ) : IsOpen (escapeRegion A) :=
  isOpen_lt continuous_const continuous_norm

theorem two_lt_norm_of_mem_escapeRegion {A : ℝ} {z : ℂ} (hz : z ∈ escapeRegion A) :
    2 < ‖z‖ := (le_max_left 2 A).trans_lt hz

theorem lt_norm_of_mem_escapeRegion {A : ℝ} {z : ℂ} (hz : z ∈ escapeRegion A) :
    A < ‖z‖ := (le_max_right 2 A).trans_lt hz

theorem norm_pos_of_mem_escapeRegion {A : ℝ} {z : ℂ} (hz : z ∈ escapeRegion A) :
    0 < ‖z‖ := (two_lt_norm_of_mem_escapeRegion hz).trans' zero_lt_two

/-! ## The filled Julia set -/

theorem mem_filledJulia {f : ℂ → ℂ} {z : ℂ} :
    z ∈ filledJulia f ↔ Bornology.IsBounded (range fun n : ℕ => (f^[n]) z) := Iff.rfl

theorem mem_filledJulia_of_norm_le {f : ℂ → ℂ} {z : ℂ} {M : ℝ}
    (h : ∀ n : ℕ, ‖(f^[n]) z‖ ≤ M) : z ∈ filledJulia f := by
  rw [mem_filledJulia]
  exact isBounded_iff_forall_norm_le.mpr
    ⟨M, fun w hw => by obtain ⟨n, rfl⟩ := hw; exact h n⟩

theorem norm_le_of_mem_filledJulia {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ filledJulia f) :
    ∃ M : ℝ, ∀ n : ℕ, ‖(f^[n]) z‖ ≤ M := by
  rw [mem_filledJulia] at hz
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hz
  exact ⟨C, fun n => hC _ ⟨n, rfl⟩⟩

/-- The filled Julia set is forward invariant (and, by the same argument, backward invariant):
`z` has bounded orbit iff `f z` does. -/
theorem mem_filledJulia_iff (f : ℂ → ℂ) (z : ℂ) : z ∈ filledJulia f ↔ f z ∈ filledJulia f := by
  constructor
  · intro hz
    obtain ⟨C, hC⟩ := norm_le_of_mem_filledJulia hz
    exact mem_filledJulia_of_norm_le fun n => hC (n + 1)
  · intro hz
    obtain ⟨C, hC⟩ := norm_le_of_mem_filledJulia hz
    refine mem_filledJulia_of_norm_le (M := max ‖z‖ C) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact le_max_left _ _
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [Function.iterate_succ_apply]
      exact (hC m).trans (le_max_right _ _)

/-- `K_f` is completely invariant: `z ∈ K_f ↔ f^[k] z ∈ K_f`. -/
theorem mem_filledJulia_iff_iterate (f : ℂ → ℂ) (z : ℂ) (k : ℕ) :
    z ∈ filledJulia f ↔ (f^[k]) z ∈ filledJulia f := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', ← mem_filledJulia_iff f ((f^[k]) z), ← ih]

end Work.Escape
