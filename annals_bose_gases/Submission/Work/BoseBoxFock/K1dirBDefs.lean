import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.latPer3_pairing_eq
import Submission.Work.BoseBoxFock.pairRowDirDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1dirB` — the vocabulary of the `K1exp − K1lim` Dirichlet pairing bound

The target `Work.BoseBoxFock.K1exp_sub_K1lim_pairing_dirB` bounds the box-squared pairing of the
kernel difference `K1exp − K1lim` against every `BoxSmooth` test function `G` by

    ε · ( √(pairEnergy ℓ G) + √(massBox ℓ G) ) .

By `k1Kernel_decomp` the kernel difference is `ℓ⁻³` times the four-row combination
`χχ·k1ErrA − χθ·k1ErrB − θχ·k1ErrC + θθ·k1ErrD`, and each row is paired against one of the four
weighted test kernels `k1H` (the `χχ` row), `k1HB`, `k1HC` (the two `χθ` rows) and `k1HD` (the `θθ`
row) below — the weight `ℓ⁻³` being carried by these kernels, so that the row pairing is
`∫∫ k1Err• · k1H•`.

* `k1H ℓ G w y = ℓ⁻³ χ(w) χ(y) G w y` is smooth and supported in `boxL ℓ × boxL ℓ`, and its
  Dirichlet energy `∫∫ Σ_j ‖∂_j(k1H)‖²` is `≤ ℓ⁻⁶ · pairEnergy ℓ G` (the estimate that makes the
  `BoxSmooth`/`pairEnergy` interface the honest one at `L¹` weights);
* the three `θ`-weighted twins.

This module only fixes the definitions and the elementary facts about them (support, smoothness of
the `χχ`-kernel, the size bounds of the two weights).  Everything is `sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.K1dirB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- The complexified corpus window `χ_ℓ` (the `χ` of the `χχ` row). -/
noncomputable def chiB (ℓ : ℝ) (w : E3) : ℂ :=
  ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)

/-- The `χχ`-weighted test kernel `ℓ⁻³ χ(w)χ(y)G(w,y)` of the first row of `k1Kernel_decomp`. -/
noncomputable def k1H (ℓ : ℝ) (G : E3 → E3 → ℂ) : E3 → E3 → ℂ :=
  fun w y => (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * chiB ℓ w * chiB ℓ y * G w y

/-- The `χθ`-weighted test kernel `ℓ⁻³ χ(w)θ(y)G(w,y)` of the second row. -/
noncomputable def k1HB (ℓ : ℝ) (G : E3 → E3 → ℂ) : E3 → E3 → ℂ :=
  fun w y => (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * chiB ℓ w * Work.BoseK15.corpusBox.thetaFun ℓ y * G w y

/-- The `θχ`-weighted test kernel `ℓ⁻³ θ(w)χ(y)G(w,y)` of the third row. -/
noncomputable def k1HC (ℓ : ℝ) (G : E3 → E3 → ℂ) : E3 → E3 → ℂ :=
  fun w y => (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ w * chiB ℓ y * G w y

/-- The `θθ`-weighted test kernel `ℓ⁻³ θ(w)θ(y)G(w,y)` of the fourth row. -/
noncomputable def k1HD (ℓ : ℝ) (G : E3 → E3 → ℂ) : E3 → E3 → ℂ :=
  fun w y => (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) * Work.BoseK15.corpusBox.thetaFun ℓ w
    * Work.BoseK15.corpusBox.thetaFun ℓ y * G w y

/-- The window vanishes on the complement of the box. -/
theorem chiB_eq_zero_of_notMem_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) {w : E3}
    (hw : w ∉ Work.BoseK15.corpusBox.boxL ℓ) : chiB ℓ w = 0 := by
  rw [chiB, Work.BoseBoxFock.chiScale_eq_zero_of_notMem_boxL hℓ hw]
  simp

/-- The square bound `‖χ_ℓ‖² ≤ 48/π` (`k1Chi`) for the corpus bump. -/
theorem chiB_sq_le (ℓ : ℝ) (w : E3) : ‖chiB ℓ w‖ ^ 2 ≤ k1Chi := by
  have h : ‖chiB ℓ w‖ ^ 2 = (Submission.BoseGases.chiScale ℓ w) ^ 2 := by
    rw [chiB]; simp
  rw [h]
  exact chiScale_sq_le_k1Chi ℓ w

/-- `χ_ℓ` is smooth for `ℓ ≠ 0`. -/
theorem chiB_contDiff {ℓ : ℝ} (hℓ : ℓ ≠ 0) : ContDiff ℝ (⊤ : ℕ∞) (chiB ℓ) :=
  Complex.ofRealCLM.contDiff.comp (Submission.BoseGases.chiScale_contDiff hℓ)

/-- The box indicator `θ_Λ` is bounded by one. -/
theorem thetaFun_norm_le (ℓ : ℝ) (w : E3) : ‖Work.BoseK15.corpusBox.thetaFun ℓ w‖ ≤ 1 := by
  classical
  rw [show Work.BoseK15.corpusBox.thetaFun ℓ w
      = if w ∈ Work.BoseK15.corpusBox.boxL ℓ then (1 : ℂ) else 0 from rfl]
  split <;> simp

/-- The `χχ`-test kernel of a smooth `G` is smooth. -/
theorem k1H_contDiff {ℓ : ℝ} (hℓ : ℓ ≠ 0) {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry (k1H ℓ G)) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 × E3 => chiB ℓ p.1) :=
    (chiB_contDiff hℓ).comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : E3 × E3 => chiB ℓ p.2) :=
    (chiB_contDiff hℓ).comp contDiff_snd
  have h4 : Function.uncurry (k1H ℓ G)
      = fun p : E3 × E3 => ((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ) * chiB ℓ p.1 * chiB ℓ p.2 * G p.1 p.2 := rfl
  rw [h4]
  exact ((contDiff_const.mul h1).mul h2).mul hG

/-- The `χχ`-test kernel is supported in the box squared. -/
theorem k1H_support {ℓ : ℝ} (hℓ : 0 < ℓ) {G : E3 → E3 → ℂ} {w y : E3}
    (h : k1H ℓ G w y ≠ 0) :
    w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ := by
  by_contra hcon
  rw [not_and_or] at hcon
  obtain hw | hy := hcon
  · exact h (by rw [k1H, chiB_eq_zero_of_notMem_boxL hℓ hw]; ring)
  · exact h (by rw [k1H, chiB_eq_zero_of_notMem_boxL hℓ hy]; ring)

/-! ## 4. Elementary facts about the lattice and the test kernels -/

/-- The dual-lattice vector has norm `2π ‖latVec n‖`. -/
theorem norm_vec_eq_latVec' (n : Fin 3 → ℤ) :
    ‖Work.BoseB4.vec n‖ = 2 * Real.pi * ‖Work.BoseBoxFock.latVec n‖ := by
  have h : Work.BoseB4.vec n = (2 * Real.pi) • Work.BoseBoxFock.latVec n := by
    rw [Work.BoseB4.vec, Work.BoseBoxFock.latVec]
    ext i
    simp [mul_comm]
  rw [h, norm_smul, Real.norm_of_nonneg (by positivity)]

/-- Lattice labels of momentum below the ultraviolet radius `uvRad ℓ N` lie in the cube
`cube N = [-N,N]³`.  This is the `hS`-condition of `L1Tails.kernelTail` at `Λ = uvRad ℓ N`. -/
theorem mem_cube_of_lt_uvRad {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} {n : Fin 3 → ℤ}
    (hn : ‖Work.BoseBoxFock.kmomInt ℓ n‖ < Work.BoseBoxFock.uvRad ℓ N) :
    n ∈ Work.BoseRowQ2.cube N := by
  by_contra hcon
  rw [Work.BoseRowQ2.mem_cube, not_forall] at hcon
  obtain ⟨i, hi⟩ := hcon
  have hge : (N : ℤ) + 1 ≤ |n i| := by
    rcases not_and_or.mp hi with h | h
    · have hlt : n i < -(N : ℤ) := not_le.mp h
      rw [abs_of_neg (by omega)]
      omega
    · have hlt : (N : ℤ) < n i := not_le.mp h
      rw [abs_of_pos (by omega)]
      omega
  have hnorm : ‖Work.BoseBoxFock.kmomInt ℓ n‖
      = (2 * Real.pi / ℓ) * ‖Work.BoseBoxFock.latVec n‖ := by
    rw [Work.BoseBoxFock.kmomInt, norm_smul, norm_vec_eq_latVec',
      Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)]
    ring
  have huvR : Work.BoseBoxFock.uvRad ℓ N = (2 * Real.pi / ℓ) * ((N : ℝ) / 4) := by
    rw [Work.BoseBoxFock.uvRad]; ring
  have hcoord : (|n i| : ℝ) ≤ ‖Work.BoseBoxFock.latVec n‖ := by
    have h1 : ‖Work.BoseBoxFock.latVec n i‖ ≤ ‖Work.BoseBoxFock.latVec n‖ := PiLp.norm_apply_le _ i
    rwa [Work.BoseBoxFock.latVec_apply, Real.norm_eq_abs] at h1
  have hgeR : ((N : ℝ) + 1) ≤ ‖Work.BoseBoxFock.latVec n‖ := by
    have h2 : (((N : ℤ) + 1 : ℤ) : ℝ) ≤ (|n i| : ℝ) := by exact_mod_cast hge
    push_cast at h2
    linarith
  rw [hnorm, huvR] at hn
  have hpos : 0 < 2 * Real.pi / ℓ := by positivity
  have hlt : ‖Work.BoseBoxFock.latVec n‖ < (N : ℝ) / 4 :=
    lt_of_mul_lt_mul_left hn hpos.le
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  linarith

/-- **The periodisation expands as a finite sum** against a box-squared supported kernel:
for `(w,y)` with `H w y ≠ 0` (hence `‖w − y‖ ≤ √3 ℓ`), `latPer3 ℓ W (w−y)` is the finite lattice
sum of the translates `W(w − y − ℓ m)`, `m ∈ latFinSet ℓ R`. -/
theorem latPer3_mul_expand {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWs : ∀ x, R < ‖x‖ → W x = 0) {H : E3 → E3 → ℂ}
    (hHs : ∀ w y, H w y ≠ 0 → w ∈ Work.BoseK15.corpusBox.boxL ℓ
      ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ) (w y : E3) :
    Work.BoseBoxFock.latPer3 ℓ W (w - y) * H w y
      = ((ℓ ^ 3 : ℝ) : ℂ)
        * (∑ m ∈ Work.BoseBoxFock.LatFourier.latFinSet ℓ R,
            ((W (w - y - ℓ • Work.BoseBoxFock.latVec m) : ℝ) : ℂ)) * H w y := by
  by_cases hH : H w y = 0
  · rw [hH, mul_zero, mul_zero]
  · obtain ⟨hw, hy⟩ := hHs w y hH
    have hz : ‖w - y‖ ≤ Real.sqrt 3 * ℓ :=
      Work.BoseBoxFock.L1Tails.latPair_norm_sub_le hℓ hw hy
    rw [Work.BoseBoxFock.L1Tails.latPair_latPer3_eq_sum_neg hℓ hWs hz]

/-- A bound for the `χχ`-test kernel of a smooth `G`. -/
theorem k1H_bdd {ℓ : ℝ} (hℓ : 0 < ℓ) {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w y, ‖k1H ℓ G w y‖ ≤ C := by
  have hK : IsCompact (Work.BoseK15.corpusBox.boxL ℓ ×ˢ Work.BoseK15.corpusBox.boxL ℓ) :=
    (Work.BoseB4.BoxData.boxL_compact _ ℓ).prod (Work.BoseB4.BoxData.boxL_compact _ ℓ)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hG.continuous.continuousOn
  refine ⟨‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * k1Chi * max C 0,
    mul_nonneg (mul_nonneg (norm_nonneg _) k1Chi_pos.le) (le_max_right _ _), fun w y => ?_⟩
  have h2 : ‖chiB ℓ w‖ ≤ Real.sqrt k1Chi := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (chiB_sq_le ℓ w)
  have h3 : ‖chiB ℓ y‖ ≤ Real.sqrt k1Chi := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (chiB_sq_le ℓ y)
  have h4 : ‖chiB ℓ w * chiB ℓ y‖ ≤ k1Chi := by
    rw [norm_mul]
    calc ‖chiB ℓ w‖ * ‖chiB ℓ y‖ ≤ Real.sqrt k1Chi * Real.sqrt k1Chi :=
          mul_le_mul h2 h3 (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = k1Chi := Real.mul_self_sqrt k1Chi_pos.le
  have hnorm : ‖k1H ℓ G w y‖
      = ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * (‖chiB ℓ w * chiB ℓ y‖ * ‖G w y‖) := by
    simp only [k1H, norm_mul]
    ring
  rw [hnorm]
  by_cases hp : w ∈ Work.BoseK15.corpusBox.boxL ℓ ∧ y ∈ Work.BoseK15.corpusBox.boxL ℓ
  · have h1 : ‖G w y‖ ≤ max C 0 := le_trans (hC (w, y) hp) (le_max_left _ _)
    calc ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * (‖chiB ℓ w * chiB ℓ y‖ * ‖G w y‖)
        ≤ ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * (k1Chi * max C 0) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h4 h1 (norm_nonneg _) k1Chi_pos.le) (norm_nonneg _)
      _ = ‖((((ℓ ^ 3)⁻¹ : ℝ)) : ℂ)‖ * k1Chi * max C 0 := by ring
  · have hzero : chiB ℓ w * chiB ℓ y = 0 := by
      rw [not_and_or] at hp
      obtain hw | hy := hp
      · rw [chiB_eq_zero_of_notMem_boxL hℓ hw, zero_mul]
      · rw [chiB_eq_zero_of_notMem_boxL hℓ hy, mul_zero]
    rw [hzero, norm_zero, zero_mul, mul_zero]
    exact mul_nonneg (mul_nonneg (norm_nonneg _) k1Chi_pos.le) (le_max_right _ _)

/-- The `χχ`-test kernel is a.e. strongly measurable on the product space. -/
theorem k1H_aesm {ℓ : ℝ} (hℓ : ℓ ≠ 0) {G : E3 → E3 → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    AEStronglyMeasurable (Function.uncurry (k1H ℓ G)) (volume.prod (volume : Measure E3)) :=
  (k1H_contDiff hℓ hG).continuous.aestronglyMeasurable

end Work.BoseBoxFock.K1dirB
