import Mathlib
import Submission.Work.Drive.qwDefs
import Submission.Work.Drive.rank_triplet_minors
import Submission.Work.Drive.fourEval_surjective
import Submission.Work.Drive.fourComb_surjective
import Submission.Work.Drive.contDiff_qPsiM
import Submission.Work.Drive.qBox_compact
import Submission.Work.Drive.finrank_span_le_iff_minors_eq_zero
import Submission.Work.Drive.interior_projection_zeroSet_of_rank_except_normed

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 1600000

noncomputable section

/-! ## The row family of the partial matrix, and its coordinate model

The `m`-minor `qMinor r p m (a, b)` of `qwDefs` is the determinant of the submatrix of the partial
matrix with rows `a : Fin m → Fin 4` and columns `b : Fin m → Fin 6` in the coordinates supplied by
the linear isomorphism `eTgt : Space × Space ≃ ℝ⁶`.  The module below introduces the row family in
those coordinates (`qRow`), relates `qMinor` to it definitionally, and shows that the rank of the
span of the row family is `finrank ℝ (qSpan r p)`. -/

/-- **The coordinate rows of the partial matrix.**  The `i`-th partial, read in the coordinates of
`ℝ⁶ = Space × Space` given by `eTgt`. -/
def qRow (r : ℝ → Space) (p : Coeff × QP) : Fin 4 → (Fin 6 → ℝ) :=
  fun i j => (eTgt (qPartial r p i)).ofLp j

/-- **The `m`-minor is the determinant of the coordinate submatrix.** -/
lemma qMinor_eq_det (r : ℝ → Space) (p : Coeff × QP) (m : ℕ) (a : Fin m → Fin 4)
    (b : Fin m → Fin 6) :
    qMinor r p m (a, b) = (Matrix.of (fun i j : Fin m => qRow r p (a i) (b j))).det := rfl

/-- The linear equivalence reading `Space × Space` in the coordinates of `eTgt`. -/
def qCoord : (Space × Space) ≃ₗ[ℝ] (Fin 6 → ℝ) :=
  (eTgt.trans (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 6 => ℝ))).toLinearEquiv

lemma qCoord_apply (v : Space × Space) (j : Fin 6) : qCoord v j = (eTgt v).ofLp j := rfl

lemma qRow_eq_coord (r : ℝ → Space) (p : Coeff × QP) (i : Fin 4) :
    qRow r p i = qCoord (qPartial r p i) := rfl

/-- **The rank of the span of the coordinate rows is the rank of the partials.** -/
lemma finrank_span_qRow_eq (r : ℝ → Space) (p : Coeff × QP) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (qRow r p)))
      = Module.finrank ℝ (qSpan r p) := by
  have hrange : Set.range (qRow r p) = qCoord '' Set.range (qPartial r p) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨qPartial r p i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨v, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
  rw [hrange]
  rw [show Submodule.span ℝ (qCoord '' Set.range (fun i : Fin 4 => qPartial r p i))
      = Submodule.map (qCoord : (Space × Space) →ₗ[ℝ] (Fin 6 → ℝ))
          (Submodule.span ℝ (Set.range (fun i : Fin 4 => qPartial r p i))) from
    (Submodule.map_span (qCoord : (Space × Space) →ₗ[ℝ] (Fin 6 → ℝ)) _).symm]
  rw [LinearEquiv.finrank_map_eq]
  exact (finrank_qSpan_eq r p).symm

/-! ## The triplet determines the collinearity multipliers -/

lemma triplet_fst (r : ℝ → Space) (p : Coeff × QP) :
    (triplet r p).1 = cross3 (qU r p) (qV r p) := rfl

lemma triplet_snd_fst (r : ℝ → Space) (p : Coeff × QP) :
    (triplet r p).2.1 = cross3 (qU r p) (qS r p) := rfl

/-- A vanishing cross product with a nonzero left factor exhibits the right factor as a multiple. -/
lemma exists_smul_of_cross3_eq_zero {u v : Space} (hu : u ≠ 0) (h : cross3 u v = 0) :
    ∃ t : ℝ, v = t • u := by
  rcases (Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul u v).mp h with h0 | ⟨t, ht⟩
  · exact absurd h0 hu
  · exact ⟨t, ht⟩

/-! ## The four points of a window in `qBox k` are distinct

A window of `qBox k` has its four coordinates in `[0, 4π]` with pairwise circular separation at
least `1/(k+1)` (proved below as `qBox_separation_local`).  Since any two of them differ by less
than one period, the corresponding knot points are distinct: the fibre of a periodic function that
is injective on a period is the coset modulo the period, and two points at distance `< 2π` lie in
different cosets as soon as they are distinct. -/

/-- The reduction of a parameter of `[0, 4π]` into `[0, 2π]` by subtracting one period. -/
def qShift (t : ℝ) : ℝ := if 2 * Real.pi ≤ t then t - 2 * Real.pi else t

lemma qShift_of_lt {t : ℝ} (h : ¬ 2 * Real.pi ≤ t) : qShift t = t := if_neg h

lemma qShift_of_le {t : ℝ} (h : 2 * Real.pi ≤ t) : qShift t = t - 2 * Real.pi := if_pos h

lemma qShift_mem_Icc {t : ℝ} (ht : t ∈ Set.Icc 0 (4 * Real.pi)) :
    qShift t ∈ Set.Icc 0 (2 * Real.pi) := by
  by_cases h : 2 * Real.pi ≤ t
  · rw [qShift_of_le h]
    exact ⟨by linarith, by linarith [ht.2]⟩
  · rw [qShift_of_lt h]
    exact ⟨ht.1, le_of_lt (lt_of_not_ge h)⟩

/-- Shifting a parameter by one period does not move the point of a periodic curve. -/
lemma pertV_sub_period {r : ℝ → Space} {c : Coeff}
    (hper : Function.Periodic (pertV r c) (2 * Real.pi)) (t : ℝ) :
    pertV r c (t - 2 * Real.pi) = pertV r c t := by
  have h := hper (t - 2 * Real.pi)
  rw [show t - 2 * Real.pi + 2 * Real.pi = t by ring] at h
  exact h.symm

lemma pertV_qShift {r : ℝ → Space} {c : Coeff}
    (hper : Function.Periodic (pertV r c) (2 * Real.pi)) (t : ℝ) :
    pertV r c (qShift t) = pertV r c t := by
  by_cases h : 2 * Real.pi ≤ t
  · rw [qShift_of_le h]
    exact pertV_sub_period hper t
  · rw [qShift_of_lt h]

/-- **The circular separation of two parameters of `[0, 4π]` survives the reduction to `[0, 2π]`.**
If `0 < csep s t` and both parameters lie in `[0, 4π]`, then the reduced parameters still have
positive circular separation. -/
lemma csep_qShift_pos {s t : ℝ} (hsep : 0 < csep s t) :
    0 < csep (qShift s) (qShift t) := by
  have hmin : 0 < min |s - t| (2 * Real.pi - |s - t|) := hsep
  have hd0 : 0 < |s - t| := lt_of_lt_of_le hmin (min_le_left _ _)
  have hd2 : |s - t| < 2 * Real.pi := by
    have h := lt_of_lt_of_le hmin (min_le_right _ _)
    linarith
  have hd : -(2 * Real.pi) < s - t ∧ s - t < 2 * Real.pi := abs_lt.mp hd2
  have hgoal : 0 < |qShift s - qShift t| ∧ |qShift s - qShift t| < 2 * Real.pi := by
    by_cases hs2 : 2 * Real.pi ≤ s
    · by_cases ht2 : 2 * Real.pi ≤ t
      · rw [qShift_of_le hs2, qShift_of_le ht2]
        simpa only [show s - 2 * Real.pi - (t - 2 * Real.pi) = s - t by ring] using
          And.intro hd0 hd2
      · rw [qShift_of_le hs2, qShift_of_lt ht2]
        have hpos : 0 < s - t := by linarith
        rw [show s - 2 * Real.pi - t = (s - t) - 2 * Real.pi by ring,
          abs_of_neg (by linarith)]
        constructor <;> linarith [hd.1]
    · by_cases ht2 : 2 * Real.pi ≤ t
      · rw [qShift_of_lt hs2, qShift_of_le ht2]
        have hneg : s - t < 0 := by linarith
        rw [show s - (t - 2 * Real.pi) = (s - t) + 2 * Real.pi by ring,
          abs_of_pos (by linarith [hd.1])]
        constructor <;> linarith
      · rw [qShift_of_lt hs2, qShift_of_lt ht2]
        exact ⟨hd0, hd2⟩
  exact lt_min hgoal.1 (by linarith [hgoal.2])

/-- **Two points at parameters of `[0, 4π]` with positive circular separation are distinct.** -/
lemma pertV_ne_of_csep_pos_Icc {r : ℝ → Space} (hr : IsSmoothKnot r) {c : Coeff}
    (hS : IsSmoothKnot (pertV r c)) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 (4 * Real.pi)) (ht : t ∈ Set.Icc 0 (4 * Real.pi))
    (hsep : 0 < csep s t) : pertV r c s ≠ pertV r c t := by
  have hper : Function.Periodic (pertV r c) (2 * Real.pi) := by
    simpa [period] using pertV_periodic hr c
  have hs'Icc : qShift s ∈ Set.Icc 0 (2 * Real.pi) := qShift_mem_Icc hs
  have ht'Icc : qShift t ∈ Set.Icc 0 (2 * Real.pi) := qShift_mem_Icc ht
  have hEs : pertV r c (qShift s) = pertV r c s := pertV_qShift hper s
  have hEt : pertV r c (qShift t) = pertV r c t := pertV_qShift hper t
  have hsep' : 0 < csep (qShift s) (qShift t) := csep_qShift_pos hsep
  have hra : red (qShift s) ≠ red (qShift t) := red_ne_of_csep_pos hs'Icc ht'Icc hsep'
  intro hcon
  refine hra (hS.injective_on_period ?_ ?_ ?_)
  · simpa [period] using red_mem_Ico hs'Icc
  · simpa [period] using red_mem_Ico ht'Icc
  · rw [pertV_red hper hs'Icc, pertV_red hper ht'Icc, hEs, hEt, hcon]

/-! ## The window box: separation of its four parameters -/

/-- **The four parameters of a window in `qBox k` are separated.** -/
lemma qBox_separation_local {k : ℕ} {τ : QP} (hτ : τ ∈ qBox k) :
    (∀ i : Fin 4, qtp τ i ∈ Set.Icc (0 : ℝ) (4 * Real.pi)) ∧
    (∀ i j : Fin 4, i ≠ j → 0 < csep (qtp τ i) (qtp τ j)) ∧
    (∀ i j : Fin 4, i ≠ j → ∀ m : ℤ, qtp τ i - qtp τ j ≠ (m : ℝ) * period) := by
  obtain ⟨hA, hG1, hG2, hG3, hL⟩ := hτ
  have hc : (0:ℝ) < 1/((k:ℝ)+1) := by positivity
  have hAZ : qA τ ≤ qZ τ := by linarith
  have hZW : qZ τ ≤ qW τ := by linarith
  have hWB : qW τ ≤ qB τ := by linarith
  have hBub : qB τ ≤ 4 * Real.pi := by linarith [hA.1, hA.2, hL, Real.pi_pos]
  have hbox : ∀ i : Fin 4, qA τ ≤ qtp τ i ∧ qtp τ i ≤ qB τ := by
    intro i
    fin_cases i
    · show qA τ ≤ qA τ ∧ qA τ ≤ qB τ; exact ⟨le_rfl, by linarith⟩
    · show qA τ ≤ qZ τ ∧ qZ τ ≤ qB τ; exact ⟨hAZ, by linarith⟩
    · show qA τ ≤ qW τ ∧ qW τ ≤ qB τ; exact ⟨by linarith, by linarith⟩
    · show qA τ ≤ qB τ ∧ qB τ ≤ qB τ; exact ⟨by linarith, le_rfl⟩
  have h01 : (1:ℝ)/(k+1) ≤ qtp τ 1 - qtp τ 0 := by rw [qtp_one, qtp_zero]; exact hG1
  have h02 : (1:ℝ)/(k+1) ≤ qtp τ 2 - qtp τ 0 := by rw [qtp_two, qtp_zero]; linarith
  have h03 : (1:ℝ)/(k+1) ≤ qtp τ 3 - qtp τ 0 := by rw [qtp_three, qtp_zero]; linarith
  have h12 : (1:ℝ)/(k+1) ≤ qtp τ 2 - qtp τ 1 := by rw [qtp_two, qtp_one]; exact hG2
  have h13 : (1:ℝ)/(k+1) ≤ qtp τ 3 - qtp τ 1 := by rw [qtp_three, qtp_one]; linarith
  have h23 : (1:ℝ)/(k+1) ≤ qtp τ 3 - qtp τ 2 := by rw [qtp_three, qtp_two]; exact hG3
  have hinc : ∀ i j : Fin 4, i < j → (1:ℝ)/(k+1) ≤ qtp τ j - qtp τ i := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | exact absurd hij (by decide)
        | exact h01 | exact h02 | exact h03 | exact h12 | exact h13 | exact h23
  have hlow : ∀ i j : Fin 4, i ≠ j → (1:ℝ)/(k+1) ≤ |qtp τ i - qtp τ j| := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · rw [abs_of_nonpos (by linarith [hinc i j hlt])]
      linarith [hinc i j hlt]
    · rw [abs_of_nonneg (by linarith [hinc j i hlt])]
      linarith [hinc j i hlt]
  have hsub : ∀ i j : Fin 4, |qtp τ i - qtp τ j| ≤ 2 * Real.pi - 1/((k:ℝ)+1) := by
    intro i j
    have hi := hbox i
    have hj := hbox j
    rw [abs_sub_le_iff]
    exact ⟨by linarith, by linarith⟩
  refine ⟨fun i => ⟨le_trans hA.1 (hbox i).1, le_trans (hbox i).2 hBub⟩, ?_, ?_⟩
  · intro i j hij
    have h1 := hlow i j hij
    have h2 := hsub i j
    rw [csep]
    exact lt_min (by linarith) (by linarith)
  · intro i j hij m hm
    have h1 := hlow i j hij
    have h2 : |((m:ℝ))| * (2 * Real.pi) ≤ 2 * Real.pi - 1/((k:ℝ)+1) := by
      have h3 := hsub i j
      rw [hm, abs_mul, show period = 2 * Real.pi from rfl] at h3
      rwa [abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)] at h3
    have h4 : |((m:ℝ))| < 1 := by
      have h5 : (0:ℝ) ≤ |((m:ℝ))| := abs_nonneg _
      nlinarith [h2, hc, h5, Real.pi_pos]
    have h5 : |m| < 1 := by exact_mod_cast h4
    have hm0 : m = 0 := Int.abs_lt_one_iff.mp h5
    rw [hm0] at hm
    have hz : qtp τ i - qtp τ j = 0 := by simpa using hm
    rw [hz, abs_zero] at h1
    exact absurd h1 (not_le.mpr hc)

/-- **The four points of a window in `qBox k` are pairwise distinct.** -/
lemma pertV_ne_of_qBox {r : ℝ → Space} (hr : IsSmoothKnot r) {c : Coeff}
    (hS : IsSmoothKnot (pertV r c)) {k : ℕ} {τ : QP} (hτ : τ ∈ qBox k) :
    ∀ i j : Fin 4, i ≠ j → pertV r c (qtp τ i) ≠ pertV r c (qtp τ j) := by
  obtain ⟨hIcc, hcsep, -⟩ := qBox_separation_local hτ
  intro i j hij
  exact pertV_ne_of_csep_pos_Icc hr hS (hIcc i) (hIcc j) (hcsep i j hij)

/-! ## Minors and the rank of the partials -/

/-- **Vanishing `(t+1)`-minors bound the rank by `t`.** -/
lemma finrank_qSpan_le_of_minors_zero {r : ℝ → Space} {p : Coeff × QP} {t : ℕ}
    (ht : t + 1 ≤ 4)
    (h : ∀ (a : Fin (t + 1) → Fin 4) (b : Fin (t + 1) → Fin 6),
      qMinor r p (t + 1) (a, b) = 0) :
    Module.finrank ℝ (qSpan r p) ≤ t := by
  have hiff := (finrank_span_le_iff_minors_eq_zero (N := 4) (M := 6) (t := t) ht
    (qRow r p)).mpr (fun a b => by rw [← qMinor_eq_det r p (t + 1) a b]; exact h a b)
  rwa [finrank_span_qRow_eq] at hiff

/-- **A nonvanishing `t`-minor forces the rank to be at least `t`.** -/
lemma le_finrank_qSpan_of_minor_ne_zero {r : ℝ → Space} {p : Coeff × QP} {t : ℕ}
    (a : Fin t → Fin 4) (b : Fin t → Fin 6) (h : qMinor r p t (a, b) ≠ 0) :
    t ≤ Module.finrank ℝ (qSpan r p) := by
  have hdet : (Matrix.of (fun i j : Fin t => qRow r p (a i) (b j))).det ≠ 0 := by
    rwa [← qMinor_eq_det r p t a b]
  have hres : LinearIndependent ℝ (fun i : Fin t => fun j : Fin t => qRow r p (a i) (b j)) := by
    have hns : (Matrix.of (fun i j : Fin t => qRow r p (a i) (b j))).Nonsingular :=
      (Matrix.nonsingular_iff_det_ne_zero).mpr hdet
    have h' := hns.linearIndependent_row
    rwa [show (Matrix.row (Matrix.of (fun i j : Fin t => qRow r p (a i) (b j))))
        = (fun i : Fin t => fun j : Fin t => qRow r p (a i) (b j)) from rfl] at h'
  let ρ : (Fin 6 → ℝ) →ₗ[ℝ] (Fin t → ℝ) :=
    { toFun := fun v => fun j => v (b j)
      map_add' := by intro u v; funext j; simp
      map_smul' := by intro c u; funext j; simp }
  have hrow : LinearIndependent ℝ (fun i : Fin t => qRow r p (a i)) :=
    LinearIndependent.of_comp (f := ρ) hres
  have hpar : LinearIndependent ℝ (fun i : Fin t => qPartial r p (a i)) :=
    LinearIndependent.of_comp (f := (qCoord : (Space × Space) →ₗ[ℝ] (Fin 6 → ℝ))) hrow
  have hspan : Submodule.span ℝ (Set.range (fun i : Fin t => qPartial r p (a i)))
      ≤ Submodule.span ℝ (Set.range (fun i : Fin 4 => qPartial r p i)) := by
    rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    exact Submodule.subset_span ⟨a i, rfl⟩
  have h1 : Module.finrank ℝ
      (Submodule.span ℝ (Set.range (fun i : Fin t => qPartial r p (a i)))) = t := by
    rw [finrank_span_eq_card hpar, Fintype.card_fin]
  have h2 := Submodule.finrank_mono hspan
  have h3 : Module.finrank ℝ
      (Submodule.span ℝ (Set.range (fun i : Fin 4 => qPartial r p i)))
      = Module.finrank ℝ (qSpan r p) := (finrank_qSpan_eq r p).symm
  omega

/-- **All `m`-minors vanish if and only if the rank of the partials is at most `m - 1`** (the form
consumed by the four-level chain). -/
lemma finrank_qSpan_le_of_minors_zero_m {r : ℝ → Space} {p : Coeff × QP} {m : ℕ}
    (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (h : ∀ (a : Fin m → Fin 4) (b : Fin m → Fin 6), qMinor r p m (a, b) = 0) :
    Module.finrank ℝ (qSpan r p) ≤ m - 1 := by
  interval_cases m
  · exact finrank_qSpan_le_of_minors_zero (t := 0) (by norm_num) (by simpa using h)
  · exact finrank_qSpan_le_of_minors_zero (t := 1) (by norm_num) (by simpa using h)
  · exact finrank_qSpan_le_of_minors_zero (t := 2) (by norm_num) (by simpa using h)
  · exact finrank_qSpan_le_of_minors_zero (t := 3) (by norm_num) (by simpa using h)

/-- **The rank of the partials at a zero of `qPsiM r m` outside the `(m-1)`-minor locus.** -/
lemma qSpan_finrank_eq {r : ℝ → Space} {p : Coeff × QP} {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (hmin : ∀ (a : Fin m → Fin 4) (b : Fin m → Fin 6), qMinor r p m (a, b) = 0)
    (hne : ∃ (a : Fin (m - 1) → Fin 4) (b : Fin (m - 1) → Fin 6),
      qMinor r p (m - 1) (a, b) ≠ 0) :
    Module.finrank ℝ (qSpan r p) = m - 1 := by
  obtain ⟨a, b, hab⟩ := hne
  exact le_antisymm (finrank_qSpan_le_of_minors_zero_m hm1 hm4 hmin)
    (le_finrank_qSpan_of_minor_ne_zero a b hab)

/-! ## The augmented map, its zeros, and the rank count -/

/-- The triplet component of `qPsiM r m` vanishes at a zero of `qPsiM r m`. -/
lemma triplet_eq_zero_of_qPsiM {r : ℝ → Space} {p : Coeff × QP} {m : ℕ}
    (h : qPsiM r m p = 0) : triplet r p = 0 := by
  have := congrArg Prod.fst h
  simpa [qPsiM] using this

/-- Every `m`-minor vanishes at a zero of `qPsiM r m`. -/
lemma qMinor_eq_zero_of_qPsiM {r : ℝ → Space} {p : Coeff × QP} {m : ℕ}
    (h : qPsiM r m p = 0) (a : Fin m → Fin 4) (b : Fin m → Fin 6) :
    qMinor r p m (a, b) = 0 := by
  have h2 := congrFun (congrFun (congrArg Prod.snd h) a) b
  simpa [qPsiM] using h2

/-- **The rank hypothesis of the tool at level `m`.**  At a zero of `qPsiM r m` whose partials
have rank exactly `m - 1`, the derivative of `qPsiM r m` has rank at least `5 > finrank ℝ QP = 4`
(`Work.Drive.rank_triplet_minors`), the side conditions coming from the box. -/
lemma qRank_lt {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ : ℝ}
    (hS : ∀ c ∈ Kv ρ, IsSmoothKnot (pertV r c)) {k : ℕ} {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    {c : Coeff} {τ : QP} (hc : c ∈ Kv ρ) (hτ : τ ∈ qBox k)
    (htri : triplet r (c, τ) = 0)
    (hrk : Module.finrank ℝ (qSpan r (c, τ)) = m - 1) :
    Module.finrank ℝ QP < Module.finrank ℝ (fderiv ℝ (qPsiM r m) (c, τ)).range := by
  obtain ⟨hIcc, hcsep, hsepZ⟩ := qBox_separation_local hτ
  have hpts : ∀ i j : Fin 4, i ≠ j →
      pertV r c (qtp τ i) ≠ pertV r c (qtp τ j) :=
    pertV_ne_of_qBox hr (hS c hc) hτ
  -- the first chord and the collinearity multipliers
  have hU : qU r (c, τ) ≠ 0 := by
    have h1 : qU r (c, τ) = pertV r c (qtp τ 1) - pertV r c (qtp τ 0) := by
      simp [qU, qPZ, qPA, qtp_one, qtp_zero]
    rw [h1]
    exact sub_ne_zero.mpr (hpts 1 0 (by decide))
  have hv : ∃ β : ℝ, qV r (c, τ) = β • qU r (c, τ) := by
    have h1 : cross3 (qU r (c, τ)) (qV r (c, τ)) = 0 := by
      have h2 := congrArg Prod.fst htri
      simpa [triplet_fst] using h2
    exact exists_smul_of_cross3_eq_zero hU h1
  have hs : ∃ γ : ℝ, qS r (c, τ) = γ • qU r (c, τ) := by
    have h1 : cross3 (qU r (c, τ)) (qS r (c, τ)) = 0 := by
      have h2 := congrArg (fun z => z.2.1) htri
      simpa [triplet_snd_fst] using h2
    exact exists_smul_of_cross3_eq_zero hU h1
  obtain ⟨β, hβ⟩ := hv
  obtain ⟨γ, hγ⟩ := hs
  have hbγ : β ≠ γ := by
    intro hbg
    have h1 : qV r (c, τ) = qS r (c, τ) := by rw [hβ, hγ, hbg]
    have h2 : qPW r (c, τ) = qPB r (c, τ) := by
      have h3 := congrArg (fun z : Space => z + qPA r (c, τ)) h1
      simpa [qV, qS] using h3
    have h4 : pertV r c (qtp τ 2) = pertV r c (qtp τ 3) := by
      have h5 : qPW r (c, τ) = pertV r c (qtp τ 2) := by simp [qPW, qtp_two]
      have h6 : qPB r (c, τ) = pertV r c (qtp τ 3) := by simp [qPB, qtp_three]
      rw [h5, h6] at h2
      exact h2
    exact hpts 2 3 (by decide) h4
  have h5 := rank_triplet_minors hr hU hβ hγ hbγ hpts (fourEval_surjective hsepZ)
    (fourComb_surjective hsepZ) hm1 hm4 hrk
  have hdim : Module.finrank ℝ QP = 4 := finrank_euclideanSpace_fin
  rw [hdim]
  exact lt_of_lt_of_le (by norm_num) h5

/-! ## The four-level chain -/

/-- **The level-`m` bad set**: the coefficients whose box contains a zero of `qPsiM r m`. -/
def qLevel (r : ℝ → Space) (ρ : ℝ) (k m : ℕ) : Set Coeff :=
  Prod.fst '' ((Kv ρ ×ˢ qBox k) ∩ {p : Coeff × QP | qPsiM r m p = 0})

/-- **The level-`m` exceptional locus**: the windows at which all `(m-1)`-minors vanish. -/
def qZ0 (r : ℝ → Space) (m : ℕ) : Set (Coeff × QP) :=
  {p : Coeff × QP | ∀ (a : Fin (m - 1) → Fin 4) (b : Fin (m - 1) → Fin 6),
    qMinor r p (m - 1) (a, b) = 0}

lemma isClosed_qZ0 {r : ℝ → Space} (hr : IsSmoothKnot r) (m : ℕ) : IsClosed (qZ0 r m) := by
  rw [show qZ0 r m = ⋂ (a : Fin (m - 1) → Fin 4), ⋂ (b : Fin (m - 1) → Fin 6),
      {p : Coeff × QP | qMinor r p (m - 1) (a, b) = 0} from by
    ext p
    simp [qZ0]]
  exact isClosed_iInter fun a => isClosed_iInter fun b =>
    isClosed_eq (contDiff_qMinor hr (m - 1) a b).continuous continuous_const

/-- **One step of the four-level chain.** -/
lemma qLevel_step {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ : ℝ}
    (hS : ∀ c ∈ Kv ρ, IsSmoothKnot (pertV r c)) (k : ℕ) {m : ℕ}
    (hm2 : 2 ≤ m) (hm4 : m ≤ 4)
    (hprev : interior (qLevel r ρ k (m - 1)) = ∅) :
    interior (qLevel r ρ k m) = ∅ := by
  classical
  have hZ₀ : interior (Prod.fst '' ((Kv ρ ×ˢ qBox k) ∩ qZ0 r m
      ∩ {p : Coeff × QP | qPsiM r m p = 0})) = ∅ := by
    refine le_bot_iff.mp (le_trans (interior_mono ?_) (le_of_eq hprev))
    rintro c ⟨p, ⟨⟨hpZ, hpZ0⟩, hpΨ⟩, hcp⟩
    refine ⟨p, ⟨hpZ, ?_⟩, hcp⟩
    exact Prod.ext (triplet_eq_zero_of_qPsiM hpΨ) (funext fun a => funext fun b => hpZ0 a b)
  have hrank : ∀ p ∈ Kv ρ ×ˢ qBox k, p ∉ qZ0 r m → qPsiM r m p = 0 →
      Module.finrank ℝ QP < Module.finrank ℝ (fderiv ℝ (qPsiM r m) p).range := by
    rintro ⟨c, τ⟩ ⟨hc, hτ⟩ hpZ0 hΨ
    have hmin : ∀ (a : Fin m → Fin 4) (b : Fin m → Fin 6),
        qMinor r (c, τ) m (a, b) = 0 := fun a b => qMinor_eq_zero_of_qPsiM hΨ a b
    have hne : ∃ (a : Fin (m - 1) → Fin 4) (b : Fin (m - 1) → Fin 6),
        qMinor r (c, τ) (m - 1) (a, b) ≠ 0 := by
      by_contra h
      exact hpZ0 (fun a b => by by_contra hab; exact h ⟨a, b, hab⟩)
    exact qRank_lt hr hS (le_trans (by norm_num : 1 ≤ 2) hm2) hm4 hc hτ
      (triplet_eq_zero_of_qPsiM hΨ)
      (qSpan_finrank_eq (le_trans (by norm_num : 1 ≤ 2) hm2) hm4 hmin hne)
  have hmain := interior_projection_zeroSet_of_rank_except_normed
    (V := Coeff) (W := QP)
    (F := (Space × Space × Space) × ((Fin m → Fin 4) → (Fin m → Fin 6) → ℝ))
    (Ψ := qPsiM r m) (contDiff_qPsiM hr m) (Z := Kv ρ ×ˢ qBox k) (Z₀ := qZ0 r m)
    ((isCompact_Kv ρ).prod (qBox_compact k)) (isClosed_qZ0 hr m) hrank hZ₀
  simpa [qLevel] using hmain

end

open Work.Drive LeanEval.KnotTheory.Quadrisecant in
/-- **The quadrisecant-isolation bad set has empty interior.**

For a smooth knot `r`, a coefficient radius `ρ > 0` all of whose ball elements give knots, and a
separation scale `k`, the set `qBad r ρ k` of coefficients admitting a *collinear* window in
`qBox k` at which the four partials of the collinearity map are dependent has empty interior.

(The box is the *strict* one: `a ∈ [0,2π]`, the three gaps at least `1/(k+1)` and the total length
`b - a ≤ 2π - 1/(k+1)`.  This excludes the degenerate face `b = a + period` on which the four points
are not distinct and the four partials are automatically dependent.)

Route (the four-level chain).  Let `Ψ_m := qPsiM r m` (the triplet together with all `m`-minors of
the partial matrix), whose zero set is `{triplet = 0} ∩ {all m-minors vanish}`.  Apply
`Work.Drive.interior_projection_zeroSet_of_rank_except_normed` with `V = Coeff`, `W = QP`
(dimension `4`), `Z = Kv ρ ×ˢ qBox k` and `Z₀_m = {all (m-1)-minors vanish}` (`m ≥ 2`; `Z₀_1 = ∅`
because the `0`-minor is the empty determinant `1`).  The rank hypothesis is
`Work.Drive.rank_triplet_minors` with `m`; its side conditions come from the box: the four
parameters are pairwise separated modulo the period (because the gaps are at least `1/(k+1)` and the
total length is at most `2π - 1/(k+1)`, so no two differ by a multiple of `2π`), hence `hsurj` and
`hcomb` follow from `Work.Drive.fourEval_surjective` and `Work.Drive.fourComb_surjective`, and
`hpts` from `hS` (injectivity of `pertV r c` on a period); the `hrk` hypothesis is the exact rank
`m - 1` enjoyed by a zero outside `Z₀_m` (`Work.Drive.qSpan_finrank_eq`).  The hypothesis `hZ₀` is
exactly the conclusion of the tool at level `m - 1`, because `Z₀_m ∩ {Ψ_m = 0} ⊆ {Ψ_{m-1} = 0}`;
the chain starts at `m = 1` where `Z₀_1 = ∅`.  The conclusion at `m = 4` gives
`interior (Prod.fst '' (Z ∩ {qPsiM r 4 = 0})) = ∅`, and `qBad r ρ k` is contained in that
projection, because a vanishing Gram determinant says that the four partials are linearly dependent,
hence have rank at most `3`, hence all `4`-minors vanish
(`Work.Drive.finrank_span_le_iff_minors_eq_zero`). -/
theorem qBad_interior_empty {r : ℝ → Space} (hr : IsSmoothKnot r) {ρ : ℝ} (hρ : 0 < ρ)
    (hS : ∀ c ∈ Kv ρ, IsSmoothKnot (pertV r c)) (k : ℕ) :
    interior (qBad r ρ k) = ∅ := by
  classical
  -- ## Level `1`: the rank-except tool with the empty exceptional set
  have h1 : interior (qLevel r ρ k 1) = ∅ := by
    have hqZ0 : qZ0 r 1 = (∅ : Set (Coeff × QP)) := by
      ext p
      constructor
      · intro h
        have h1 := h (fun i => i.elim0) (fun i => i.elim0)
        rw [qMinor_eq_det] at h1
        simp [Matrix.det_fin_zero] at h1
      · intro h
        exact absurd h (Set.notMem_empty p)
    have hZ₀ : interior (Prod.fst '' ((Kv ρ ×ˢ qBox k) ∩ qZ0 r 1
        ∩ {p : Coeff × QP | qPsiM r 1 p = 0})) = ∅ := by
      rw [hqZ0]
      simp
    have hrank : ∀ p ∈ Kv ρ ×ˢ qBox k, p ∉ qZ0 r 1 → qPsiM r 1 p = 0 →
        Module.finrank ℝ QP < Module.finrank ℝ (fderiv ℝ (qPsiM r 1) p).range := by
      rintro ⟨c, τ⟩ ⟨hc, hτ⟩ - hΨ
      have hmin : ∀ (a : Fin 1 → Fin 4) (b : Fin 1 → Fin 6),
          qMinor r (c, τ) 1 (a, b) = 0 := fun a b => qMinor_eq_zero_of_qPsiM hΨ a b
      have hne : ∃ (a : Fin (1 - 1) → Fin 4) (b : Fin (1 - 1) → Fin 6),
          qMinor r (c, τ) (1 - 1) (a, b) ≠ 0 :=
        ⟨fun i => i.elim0, fun i => i.elim0, by
          rw [qMinor_eq_det]
          simp [Matrix.det_fin_zero]⟩
      exact qRank_lt hr hS (le_refl 1) (by norm_num) hc hτ
        (triplet_eq_zero_of_qPsiM hΨ)
        (qSpan_finrank_eq (le_refl 1) (by norm_num) hmin hne)
    have hmain := interior_projection_zeroSet_of_rank_except_normed
      (V := Coeff) (W := QP)
      (F := (Space × Space × Space) × ((Fin 1 → Fin 4) → (Fin 1 → Fin 6) → ℝ))
      (Ψ := qPsiM r 1) (contDiff_qPsiM hr 1) (Z := Kv ρ ×ˢ qBox k) (Z₀ := qZ0 r 1)
      ((isCompact_Kv ρ).prod (qBox_compact k)) (isClosed_qZ0 hr 1) hrank hZ₀
    simpa [qLevel] using hmain
  -- ## Levels `2`, `3`, `4`
  have h2 : interior (qLevel r ρ k 2) = ∅ :=
    qLevel_step hr hS k (le_refl 2) (by norm_num) h1
  have h3 : interior (qLevel r ρ k 3) = ∅ :=
    qLevel_step hr hS k (by norm_num) (by norm_num) h2
  have h4 : interior (qLevel r ρ k 4) = ∅ :=
    qLevel_step hr hS k (by norm_num) (by norm_num) h3
  -- ## `qBad` is contained in the level-`4` projection
  have hsub : qBad r ρ k ⊆ qLevel r ρ k 4 := by
    rintro c ⟨hc, τ, hτ, htri, hgram⟩
    refine ⟨(c, τ), ⟨⟨hc, hτ⟩, ?_⟩, rfl⟩
    have hli : ¬ LinearIndependent ℝ (qPartialW r (c, τ)) := (qGram_eq_zero_iff r (c, τ)).mp hgram
    have hfin : Module.finrank ℝ (qSpan r (c, τ)) ≤ 3 := by
      have h := (linearIndependent_iff_card_le_finrank_span (R := ℝ)
        (b := qPartialW r (c, τ))).mpr
      simp only [Set.finrank, Fintype.card_fin] at h
      have h2 : ¬ (4 ≤ Module.finrank ℝ (Submodule.span ℝ
          (Set.range (qPartialW r (c, τ))))) := fun hc4 => hli (h hc4)
      rw [qSpan]
      omega
    have hmin : ∀ (a : Fin 4 → Fin 4) (b : Fin 4 → Fin 6),
        qMinor r (c, τ) 4 (a, b) = 0 := by
      have hiff := (finrank_span_le_iff_minors_eq_zero (N := 4) (M := 6) (t := 3)
        (by norm_num) (qRow r (c, τ))).mp (by rwa [finrank_span_qRow_eq])
      intro a b
      rw [qMinor_eq_det]
      exact hiff a b
    exact Prod.ext htri (funext fun a => funext fun b => hmin a b)
  have : interior (qBad r ρ k) ≤ (∅ : Set Coeff) := le_trans (interior_mono hsub) (le_of_eq h4)
  exact le_bot_iff.mp this

end Work.Drive
