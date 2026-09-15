/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.L2Support
import Submission.Vinogradov.DecLinLift
import Submission.Vinogradov.Section4Exp
import Submission.Commons.Analysis.InnerProduct.norm_sum_sq_of_pairwise_orthogonal

/-!
# The `k = 1` base case of the §4 exponent bootstrap: `etaLin 1 ≤ 0`

For `k = 1` the plates of the `N`-fold partition of `[0,1]` are intervals of length `1/N` which
are pairwise disjoint, so the `ℓ²`-decoupling for the line holds with constant `1` by `L²`
orthogonality of functions with disjoint frequency support.  Composing with the even/odd lift
`DecLinLift.decLinScale_two_of_decLin` gives the enlarged statement `DecLinScale 1 N 2 2` which
`linExpSet` is stated with, hence `0 ∈ linExpSet 1` and `etaLin 1 ≤ 0`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped RealInnerProductSpace InnerProductSpace BigOperators ENNReal NNReal ContDiff

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. The plates of the line -/

/-- The `0`-th coordinate of `affMap 1 δ t y`. -/
lemma affMap_one_apply_zero (δ t : ℝ) (y : E 1) :
    (affMap 1 δ t y) 0 = t + y 0 * δ := by
  rw [affMap_apply, PiLp.add_apply, gammaVec_apply, affVecDual_apply]
  rw [Finset.sum_eq_single (0 : Fin 1)]
  · simp
  · intro b _ hb; exact absurd (Subsingleton.elim b 0) hb
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The plates of the line are intervals.**  For `k = 1` the plate `plate 1 δ t` is the
interval of radius `δ` centred at `t` in the single coordinate. -/
lemma mem_plate_one_iff {δ : ℝ} (hδ : 0 < δ) (t : ℝ) (x : E 1) :
    x ∈ plate 1 δ t ↔ |x 0 - t| ≤ δ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy0 : |y 0| ≤ 1 := by simpa using hy (0 : Fin 1)
    rw [affMap_one_apply_zero, add_sub_cancel_left, abs_mul, abs_of_pos hδ]
    exact mul_le_of_le_one_left hδ.le hy0
  · intro hx
    refine ⟨WithLp.toLp 2 (fun _ : Fin 1 => (x 0 - t) / δ), ?_, ?_⟩
    · intro i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      show |(x 0 - t) / δ| ≤ (((0 : Fin 1).val + 1).factorial : ℝ)
      rw [abs_div, abs_of_pos hδ]
      norm_num
      exact (div_le_one hδ).mpr hx
    · ext i
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      show (affMap 1 δ t (WithLp.toLp 2 (fun _ : Fin 1 => (x 0 - t) / δ))) 0 = x 0
      rw [affMap_one_apply_zero]
      show t + (x 0 - t) / δ * δ = x 0
      rw [div_mul_cancel₀ _ hδ.ne']
      ring

/-- The plate `plate 1 δ t` is closed (it is an interval). -/
lemma isClosed_plate_one {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : IsClosed (plate 1 δ t) := by
  have hset : plate 1 δ t = {x : E 1 | |x 0 - t| ≤ δ} := by
    ext x; rw [Set.mem_ofPred_eq, mem_plate_one_iff hδ]
  rw [hset]
  exact isClosed_le (by fun_prop) (by fun_prop)

/-- The plate `plate 1 δ t` is nonempty. -/
lemma nonempty_plate_one {δ : ℝ} (hδ : 0 < δ) (t : ℝ) : (plate 1 δ t).Nonempty :=
  ⟨gammaVec 1 t, gammaVec_mem_plate 1 hδ (by simpa using hδ.le)⟩

/-! ## 2. The pieces of the `N`-fold partition are disjoint intervals -/

/-- **The `j`-th piece of the `N`-fold partition is the interval `[j/N, (j+1)/N]`.** -/
lemma piecePlate_one_subset {N : ℕ} (hN : 1 ≤ N) (j : Fin N) {x : E 1}
    (hx : x ∈ piecePlate 1 N j) :
    (j : ℝ) / N ≤ x 0 ∧ x 0 ≤ ((j : ℝ) + 1) / N := by
  rw [piecePlate, pieceCenter] at hx
  have hδpos : (0 : ℝ) < 1 / (2 * (N : ℝ)) := by positivity
  have h := (mem_plate_one_iff hδpos _ x).mp hx
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  constructor
  · have hkey : ((j : ℝ) + 1 / 2) / (N : ℝ) - 1 / (2 * (N : ℝ)) = (j : ℝ) / (N : ℝ) := by
      field_simp; ring
    linarith
  · have hkey : ((j : ℝ) + 1 / 2) / (N : ℝ) + 1 / (2 * (N : ℝ)) = ((j : ℝ) + 1) / (N : ℝ) := by
      field_simp; ring
    linarith

/-- The set `{x : E 1 | x 0 = a}` is a singleton, hence has measure zero. -/
lemma volume_setOf_coord_eq_zero (a : ℝ) : volume {x : E 1 | x 0 = a} = 0 := by
  have hset : ({x : E 1 | x 0 = a} : Set (E 1))
      = {((WithLp.toLp 2 (fun _ : Fin 1 => a)) : E 1)} := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_singleton_iff]
      ext i
      fin_cases i
      simpa using hx
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      simp
  rw [hset]
  exact measure_singleton _

/-- **The pieces of the `N`-fold partition have pairwise null intersections.** -/
theorem measure_piecePlate_one_inter {N : ℕ} (hN : 1 ≤ N) {j j' : Fin N} (hjj : j ≠ j') :
    volume (piecePlate 1 N j ∩ piecePlate 1 N j') = 0 := by
  have hN' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rcases lt_or_gt_of_ne (fun h : (j : ℕ) = (j' : ℕ) => hjj (Fin.ext h)) with hlt | hlt
  · have hsub : piecePlate 1 N j ∩ piecePlate 1 N j' ⊆
        {x : E 1 | x 0 = ((j : ℝ) + 1) / N} := by
      rintro x ⟨hx1, hx2⟩
      obtain ⟨-, ha2⟩ := piecePlate_one_subset hN j hx1
      obtain ⟨hb1, -⟩ := piecePlate_one_subset hN j' hx2
      have hle : ((j : ℝ) + 1) / N ≤ (j' : ℝ) / N := by
        apply div_le_div_of_nonneg_right _ hN'.le
        have : (j : ℕ) + 1 ≤ (j' : ℕ) := hlt
        have : ((j : ℕ) : ℝ) + 1 ≤ ((j' : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      exact le_antisymm ha2 (le_trans hle hb1)
    exact le_antisymm ((measure_mono hsub).trans_eq (volume_setOf_coord_eq_zero _)) zero_le
  · have hsub : piecePlate 1 N j ∩ piecePlate 1 N j' ⊆
        {x : E 1 | x 0 = ((j' : ℝ) + 1) / N} := by
      rintro x ⟨hx1, hx2⟩
      obtain ⟨-, ha2⟩ := piecePlate_one_subset hN j' hx2
      obtain ⟨hb1, -⟩ := piecePlate_one_subset hN j hx1
      have hle : ((j' : ℝ) + 1) / N ≤ (j : ℝ) / N := by
        apply div_le_div_of_nonneg_right _ hN'.le
        have : (j' : ℕ) + 1 ≤ (j : ℕ) := hlt
        have : ((j' : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by exact_mod_cast this
        linarith
      exact le_antisymm ha2 (le_trans hle hb1)
    exact le_antisymm ((measure_mono hsub).trans_eq (volume_setOf_coord_eq_zero _)) zero_le

/-- The pieces of the `N`-fold partition are nonempty closed sets. -/
lemma isClosed_nonempty_piecePlate_one {N : ℕ} (hN : 1 ≤ N) (j : Fin N) :
    IsClosed (piecePlate 1 N j) ∧ (piecePlate 1 N j).Nonempty := by
  have hδpos : (0 : ℝ) < 1 / (2 * (N : ℝ)) := by positivity
  have hpc : piecePlate 1 N j = plate 1 (1 / (2 * (N : ℝ))) (pieceCenter N j) := rfl
  rw [hpc]
  exact ⟨isClosed_plate_one hδpos _, nonempty_plate_one hδpos _⟩

/-- The pieces of the `N`-fold partition are at positive distance from every point outside. -/
lemma piecePlate_one_infDist_pos {N : ℕ} (hN : 1 ≤ N) (j : Fin N) {ξ : E 1}
    (hξ : ξ ∉ piecePlate 1 N j) : 0 < Metric.infDist ξ (piecePlate 1 N j) := by
  obtain ⟨hclosed, hne⟩ := isClosed_nonempty_piecePlate_one hN j
  rw [← Metric.infDist_pos_iff_notMem_closure hne, hclosed.closure_eq]
  exact hξ

/-! ## 3. `ℓ²`-decoupling for the line with constant `1` -/

/-- `pE 1 = 2`. -/
lemma pE_one : pE 1 = 2 := rfl

/-- `lpNorm 1 (pE 1) f = eLpNorm f 2 volume`. -/
lemma lpNorm_one_eq (f : E 1 → ℂ) : lpNorm 1 (pE 1) f = eLpNorm f 2 (volume : Measure (E 1)) := by
  rw [lpNorm, pE_one]

/-- The extended norm as an `ofReal`. -/
lemma enorm_eq_ofReal_norm {E : Type*} [SeminormedAddCommGroup E] (x : E) :
    ‖x‖ₑ = ENNReal.ofReal ‖x‖ := by
  simp [enorm, ENNReal.ofReal]

/-- **The `k = 1` linear `ℓ²`-decoupling with constant `1`.**  For `k = 1` the pieces of the
`N`-fold partition have pairwise disjoint plates, so the bound is the `L²` orthogonality of
frequency-disjoint functions. -/
theorem decLin_one (N : ℕ) : DecLin 1 N 1 := by
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0
    intro F hF
    have h0 : (fun x : E 1 => ∑ j : Fin 0, F j x) = fun _ => 0 := by
      funext x; simp
    have hl2 : l2Norm (fun j : Fin 0 => lpNorm 1 (pE 1) (F j)) = 0 := by
      rw [l2Norm]; simp
    rw [h0, lpNorm_zero, hl2]
    simp
  intro F hF
  by_cases hbad : ∃ j, lpNorm 1 (pE 1) (F j) = ⊤
  · obtain ⟨j0, hj0⟩ := hbad
    have htop : l2Norm (fun j : Fin N => lpNorm 1 (pE 1) (F j)) = ⊤ := by
      rw [l2Norm]
      have h1 : (∑ j : Fin N, (lpNorm 1 (pE 1) (F j)) ^ (2 : ℝ)) = ⊤ := by
        refine top_unique ?_
        calc (⊤ : ℝ≥0∞) = (lpNorm 1 (pE 1) (F j0)) ^ (2 : ℝ) := by
              rw [hj0]; exact (ENNReal.top_rpow_of_pos (by norm_num)).symm
          _ ≤ ∑ j : Fin N, (lpNorm 1 (pE 1) (F j)) ^ (2 : ℝ) :=
              Finset.single_le_sum (s := Finset.univ)
                (f := fun j : Fin N => (lpNorm 1 (pE 1) (F j)) ^ (2 : ℝ))
                (fun i _ => zero_le) (Finset.mem_univ j0)
      rw [h1]
      exact ENNReal.top_rpow_of_pos (by norm_num)
    rw [htop]
    simp
  · push Not at hbad
    have hmem : ∀ j : Fin N, MemLp (F j) 2 (volume : Measure (E 1)) := fun j =>
      ⟨(hF j).aestronglyMeasurable, by
        have hj := hbad j
        rw [lpNorm_one_eq] at hj
        exact lt_top_iff_ne_top.mpr hj⟩
    let Fp : Fin N → Lp ℂ 2 (volume : Measure (E 1)) := fun j => (hmem j).toLp (F j)
    have horth : ∀ i j : Fin N, i ≠ j → inner ℂ (Fp i) (Fp j) = 0 := by
      intro i j hij
      exact inner_eq_zero_of_isFourierRep_of_disjoint (hF i) (hF j) (hmem i) (hmem j)
        (fun ξ hξ => piecePlate_one_infDist_pos hN i hξ)
        (fun ξ hξ => piecePlate_one_infDist_pos hN j hξ)
        (measure_piecePlate_one_inter hN hij)
    have hsum_sq := Commons.Analysis.InnerProduct.norm_sum_sq_of_pairwise_orthogonal Fp horth
    -- the a.e. identity between the `Lp` sum and the pointwise sum
    have hae : (↑(∑ j : Fin N, Fp j) : E 1 → ℂ) =ᵐ[volume]
        (fun x => ∑ j : Fin N, F j x) := by
      have hall : ∀ᵐ x ∂(volume : Measure (E 1)),
          ∀ j : Fin N, (Fp j : E 1 → ℂ) x = F j x := by
        rw [MeasureTheory.ae_all_iff]
        exact fun j => (hmem j).coeFn_toLp
      filter_upwards [Lp.coeFn_finsetSum (Finset.univ : Finset (Fin N)) Fp, hall]
        with x hx hxs
      show (↑(∑ j : Fin N, Fp j) : E 1 → ℂ) x = ∑ j : Fin N, F j x
      rw [hx, Finset.sum_apply]
      exact Finset.sum_congr rfl fun j _ => hxs j
    -- the left-hand side
    have hLHS : lpNorm 1 (pE 1) (fun x => ∑ j : Fin N, F j x) = ‖(∑ j : Fin N, Fp j)‖ₑ := by
      rw [lpNorm_one_eq, ← eLpNorm_congr_ae hae]
      exact (Lp.enorm_def (∑ j : Fin N, Fp j)).symm
    -- the right-hand side
    have hterm : ∀ j : Fin N, lpNorm 1 (pE 1) (F j) = ‖Fp j‖ₑ := by
      intro j
      rw [lpNorm_one_eq]
      exact (Lp.enorm_toLp (hmem j)).symm
    have hRHS : l2Norm (fun j : Fin N => lpNorm 1 (pE 1) (F j))
        = ENNReal.ofReal (Real.sqrt (∑ j : Fin N, ‖Fp j‖ ^ 2)) := by
      have hterm : ∀ j : Fin N,
          (lpNorm 1 (pE 1) (F j)) ^ (2 : ℝ) = ENNReal.ofReal (‖Fp j‖ ^ 2) := by
        intro j
        have h1 : lpNorm 1 (pE 1) (F j) = ‖Fp j‖ₑ := by
          rw [lpNorm_one_eq]
          exact (Lp.enorm_toLp (hmem j)).symm
        rw [h1, enorm_eq_ofReal_norm,
          ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (Fp j)) (by norm_num)]
        exact congrArg ENNReal.ofReal (Real.rpow_natCast ‖Fp j‖ 2)
      rw [l2Norm]
      have h2 : (∑ j : Fin N, (lpNorm 1 (pE 1) (F j)) ^ (2 : ℝ))
          = ENNReal.ofReal (∑ j : Fin N, ‖Fp j‖ ^ 2) :=
        (Finset.sum_congr rfl fun j _ => hterm j).trans
          (ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg (‖Fp j‖))).symm
      rw [h2]
      have h3 : ENNReal.ofReal (∑ j : Fin N, ‖Fp j‖ ^ 2) ^ (1 / 2 : ℝ)
          = ENNReal.ofReal ((∑ j : Fin N, ‖Fp j‖ ^ 2) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg (‖Fp j‖))) (by norm_num)
      rw [h3]
      exact congrArg ENNReal.ofReal (Real.sqrt_eq_rpow _).symm
    calc lpNorm 1 (pE 1) (fun x => ∑ j : Fin N, F j x)
        = ‖(∑ j : Fin N, Fp j)‖ₑ := hLHS
      _ = ENNReal.ofReal ‖(∑ j : Fin N, Fp j)‖ := enorm_eq_ofReal_norm _
      _ ≤ ENNReal.ofReal (Real.sqrt (∑ j : Fin N, ‖Fp j‖ ^ 2)) :=
            ENNReal.ofReal_le_ofReal (by
              rw [← hsum_sq]
              exact (Real.sqrt_sq (norm_nonneg _)).ge)
      _ = l2Norm (fun j : Fin N => lpNorm 1 (pE 1) (F j)) := hRHS.symm
      _ = 1 * l2Norm (fun j : Fin N => lpNorm 1 (pE 1) (F j)) := (one_mul _).symm

/-! ## 4. The base case of the §4 bootstrap: `etaLin 1 ≤ 0` -/

/-- The enlarged decoupling at scale `N` and enlargement `2` with constant `2`, from the
un-enlarged statement at the same scale. -/
theorem decLinScale_one_two (N : ℕ) : DecLinScale 1 N 2 2 := by
  have h := decLinScale_two_of_decLin (k := 1) (M := N) (m' := N) (C := 1)
    (by norm_num) (by omega) (decLin_one N)
  simpa using h

/-- `0` belongs to the exponent set of the linear decoupling of the line. -/
theorem mem_linExpSet_zero_one : (0 : ℝ) ∈ linExpSet 1 := by
  refine ⟨le_refl 0, 2, by norm_num, fun N hN => ?_⟩
  have h2 : ENNReal.ofReal ((2 : ℝ) * (N : ℝ) ^ (0 : ℝ)) = 2 := by
    rw [Real.rpow_zero, mul_one]
    norm_num
  rw [h2]
  exact decLinScale_one_two N

/-- **The base case of the §4 exponent bootstrap**: the decoupling exponent of the line is
nonpositive. -/
theorem etaLin_one_le_zero : etaLin 1 ≤ 0 := etaLin_le_of_mem mem_linExpSet_zero_one

end Submission.Vinogradov
