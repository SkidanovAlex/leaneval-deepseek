import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Submission.Work.BoseBoxFock.PCFU.KfrU_pairing_uniform
import Submission.Work.BoseBoxFock.PCFU.frameSmear
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-! ## The `+`-shifted pairing bound for a general lattice frame

`KfrU_pairing_uniform` bounds the pairing of the lattice frame with box-supported `L²` functions
in the **minus**-shifted form
`‖∫_w∫_y f w·(Σ_k W k·e^{i⟪κ_k,y−w⟫})·g y‖ ≤ C ℓ³‖f‖₂‖g‖₂`.
The consumer (`MiddleV`/`(C)`-channel chain) needs the same estimate with the shift `y + w`.

The two differ only in the sign of the phase in the `w`-variable, so the same
finite-expansion proof applies, with the Bessel input for the `w`-integral being the *`+i`* twin
`KfrU_aux_sum_exp_sq_le` (which is the `−i` twin of `KfrU_aux_sum_kinFT_sq_le`, already proved).
No evenness of the frame and no symmetry of the box are needed. -/

/-- **Pairing bound, `+`-shifted.**  For `f, g ∈ L²` supported in the box `boxL ℓ` and weights `W`
with `‖W k‖ ≤ C`,

`‖∫_y g y·(∫_w (Σ_{k : Lab N} W k·e^{i⟪κ_k,y+w⟫})·f w)‖ ≤ C ℓ³ ‖f‖₂ ‖g‖₂`.

Proof: expand the frame in the inner integral (finite sum),
`∫_w (Σ_k W k e^{i⟪κ_k,y+w⟫})·f w = Σ_k (W k e^{i⟪κ_k,y⟫})·A_k` with
`A_k = ∫_w e^{i⟪κ_k,w⟫}f w`; then the outer integral becomes `Σ_k (W k A_k)·B_k` with
`B_k = ∫_y e^{i⟪κ_k,y⟫}g y`.  Cauchy–Schwarz over `Lab N` and the two Bessel bounds
(`KfrU_aux_sum_exp_sq_le` for both `A` and `B`). -/
lemma KfrU_aux_pairing_sum_eplus_le {ℓ : ℝ} (hℓ : 0 < ℓ) {N : ℕ} {W : Lab N → ℂ} {C : ℝ}
    (hC0 : 0 ≤ C) (hW : ∀ k : Lab N, ‖W k‖ ≤ C) {f g : E3 → ℂ}
    (hf : MemLp f 2 (volume : Measure E3)) (hg : MemLp g 2 (volume : Measure E3))
    (hfs : tsupport f ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hgs : tsupport g ⊆ Work.BoseK15.corpusBox.boxL ℓ) :
    ‖∫ y : E3, g y * (∫ w : E3, (∑ k : Lab N, W k *
        Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) (y + w) : ℂ))) * f w)‖
      ≤ C * ℓ ^ 3 * Real.sqrt (∫ w : E3, ‖f w‖ ^ 2)
          * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2) := by
  have hfint : Integrable f := KfrU_aux_integrable hℓ hf hfs
  have hgint : Integrable g := KfrU_aux_integrable hℓ hg hgs
  -- the bounded factor `e^{i⟪κ_k,·⟫}`
  have hbdd : ∀ k : Lab N, ∀ᵐ y : E3 ∂(volume : Measure E3),
      ‖Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ))‖ ≤ 1 := by
    intro k
    refine Filter.Eventually.of_forall (fun y => ?_)
    rw [show Complex.I * ((inner ℝ (kmomLab ℓ N k) y : ℝ) : ℂ)
          = ((inner ℝ (kmomLab ℓ N k) y : ℝ) : ℂ) * Complex.I from by ring,
      Complex.norm_exp_ofReal_mul_I]
  -- the coefficients of the `w`-integral, resp. the `y`-integral
  set A : Lab N → ℂ := fun k => ∫ w : E3,
    Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) w : ℂ)) * f w with hA
  set B : Lab N → ℂ := fun k => ∫ y : E3,
    Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ)) * g y with hB
  -- the inner (over `w`) expansion, for every `y`
  have hstep1 : ∀ y : E3,
      (∫ w : E3, (∑ k : Lab N, W k *
          Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) (y + w) : ℂ))) * f w)
        = ∑ k : Lab N, (W k * Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ)))
            * A k := by
    intro y
    rw [show (fun w : E3 => (∑ k : Lab N, W k *
          Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) (y + w) : ℂ))) * f w)
        = (fun w : E3 => ∑ k : Lab N,
            (W k * Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ))) *
              (Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) w : ℂ)) * f w)) from
          funext (fun w => by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [show Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) (y + w) : ℂ))
                = Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ)) *
                  Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) w : ℂ)) from by
              rw [inner_add_right]
              push_cast
              rw [← Complex.exp_add]
              congr 1
              ring]
            ring)]
    rw [MeasureTheory.integral_finsetSum (Finset.univ : Finset (Lab N))
      (f := fun (k : Lab N) (w : E3) =>
        (W k * Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ))) *
          (Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) w : ℂ)) * f w))
      (fun k _ => ((hfint.mul_bdd (by fun_prop) (hbdd k)).const_mul
        (W k * Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ)))).congr
          (Filter.Eventually.of_forall (fun w => by ring)))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [MeasureTheory.integral_const_mul, hA]
  -- the outer (over `y`) expansion
  have hstep2 : (∫ y : E3, g y * (∑ k : Lab N,
        (W k * Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ))) * A k))
      = ∑ k : Lab N, (W k * A k) * B k := by
    rw [show (fun y : E3 => g y * (∑ k : Lab N,
          (W k * Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ))) * A k))
        = (fun y : E3 => ∑ k : Lab N,
            (W k * A k) * (Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ))
              * g y)) from
          funext (fun y => by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun k _ => by ring))]
    rw [MeasureTheory.integral_finsetSum (Finset.univ : Finset (Lab N))
      (fun k _ => ((hgint.mul_bdd (by fun_prop) (hbdd k)).const_mul (W k * A k)).congr
          (Filter.Eventually.of_forall (fun y => by ring)))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [MeasureTheory.integral_const_mul]
  -- assemble the expansion
  have hmain : (∫ y : E3, g y * (∫ w : E3, (∑ k : Lab N, W k *
        Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) (y + w) : ℂ))) * f w))
      = ∑ k : Lab N, (W k * A k) * B k := by
    rw [show (∫ y : E3, g y * (∫ w : E3, (∑ k : Lab N, W k *
          Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) (y + w) : ℂ))) * f w))
        = ∫ y : E3, g y * (∑ k : Lab N,
            (W k * Complex.exp (Complex.I * (inner ℝ (kmomLab ℓ N k) y : ℂ))) * A k) from
          integral_congr_ae (Filter.Eventually.of_forall
            (fun y : E3 => congrArg (fun z : ℂ => g y * z) (hstep1 y)))]
    exact hstep2
  rw [hmain]
  -- Cauchy–Schwarz over `Lab N`
  have hCS : ∑ k : Lab N, ‖A k‖ * ‖B k‖
      ≤ Real.sqrt (∑ k : Lab N, ‖A k‖ ^ 2) * Real.sqrt (∑ k : Lab N, ‖B k‖ ^ 2) := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Lab N))
      (fun k => ‖A k‖) (fun k => ‖B k‖)
    rw [← Real.sqrt_sq (Finset.sum_nonneg (fun k _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)))]
    calc Real.sqrt ((∑ k : Lab N, ‖A k‖ * ‖B k‖) ^ 2)
        ≤ Real.sqrt ((∑ k : Lab N, ‖A k‖ ^ 2) * ∑ k : Lab N, ‖B k‖ ^ 2) :=
          Real.sqrt_le_sqrt h
      _ = Real.sqrt (∑ k : Lab N, ‖A k‖ ^ 2) * Real.sqrt (∑ k : Lab N, ‖B k‖ ^ 2) :=
          Real.sqrt_mul (Finset.sum_nonneg (fun k _ => sq_nonneg _)) _
  have hAsum : ∑ k : Lab N, ‖A k‖ ^ 2 ≤ ℓ ^ 3 * ∫ x : E3, ‖f x‖ ^ 2 := by
    simp only [hA]
    exact KfrU_aux_sum_exp_sq_le hℓ N hf hfs
  have hBsum : ∑ k : Lab N, ‖B k‖ ^ 2 ≤ ℓ ^ 3 * ∫ y : E3, ‖g y‖ ^ 2 := by
    simp only [hB]
    exact KfrU_aux_sum_exp_sq_le hℓ N hg hgs
  have hroot : Real.sqrt (∑ k : Lab N, ‖A k‖ ^ 2) * Real.sqrt (∑ k : Lab N, ‖B k‖ ^ 2)
      ≤ ℓ ^ 3 * Real.sqrt (∫ x : E3, ‖f x‖ ^ 2) * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2) := by
    have h1 : Real.sqrt (∑ k : Lab N, ‖A k‖ ^ 2)
        ≤ Real.sqrt (ℓ ^ 3) * Real.sqrt (∫ x : E3, ‖f x‖ ^ 2) := by
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ℓ ^ 3)]
      exact Real.sqrt_le_sqrt hAsum
    have h2 : Real.sqrt (∑ k : Lab N, ‖B k‖ ^ 2)
        ≤ Real.sqrt (ℓ ^ 3) * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2) := by
      rw [← Real.sqrt_mul (by positivity : (0 : ℝ) ≤ ℓ ^ 3)]
      exact Real.sqrt_le_sqrt hBsum
    have h3 : Real.sqrt (ℓ ^ 3) * Real.sqrt (ℓ ^ 3) = ℓ ^ 3 := by
      rw [← sq, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ℓ ^ 3)]
    have h4 : (0 : ℝ) ≤ Real.sqrt (∫ x : E3, ‖f x‖ ^ 2) := Real.sqrt_nonneg _
    have h5 : (0 : ℝ) ≤ Real.sqrt (∫ y : E3, ‖g y‖ ^ 2) := Real.sqrt_nonneg _
    calc Real.sqrt (∑ k : Lab N, ‖A k‖ ^ 2) * Real.sqrt (∑ k : Lab N, ‖B k‖ ^ 2)
        ≤ (Real.sqrt (ℓ ^ 3) * Real.sqrt (∫ x : E3, ‖f x‖ ^ 2))
            * (Real.sqrt (ℓ ^ 3) * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2)) :=
          mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
      _ = ℓ ^ 3 * Real.sqrt (∫ x : E3, ‖f x‖ ^ 2) * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2) := by
          rw [show (Real.sqrt (ℓ ^ 3) * Real.sqrt (∫ x : E3, ‖f x‖ ^ 2))
                * (Real.sqrt (ℓ ^ 3) * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2))
              = (Real.sqrt (ℓ ^ 3) * Real.sqrt (ℓ ^ 3))
                * (Real.sqrt (∫ x : E3, ‖f x‖ ^ 2) * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2))
              from by ring, h3]
          ring
  calc ‖∑ k : Lab N, (W k * A k) * B k‖
      ≤ ∑ k : Lab N, ‖(W k * A k) * B k‖ := norm_sum_le _ _
    _ ≤ ∑ k : Lab N, C * (‖A k‖ * ‖B k‖) := by
        refine Finset.sum_le_sum (fun k _ => ?_)
        rw [norm_mul, norm_mul]
        calc ‖W k‖ * ‖A k‖ * ‖B k‖ ≤ C * ‖A k‖ * ‖B k‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hW k) (norm_nonneg _))
                (norm_nonneg _)
          _ = C * (‖A k‖ * ‖B k‖) := by ring
    _ = C * ∑ k : Lab N, ‖A k‖ * ‖B k‖ := by rw [Finset.mul_sum]
    _ ≤ C * (Real.sqrt (∑ k : Lab N, ‖A k‖ ^ 2) * Real.sqrt (∑ k : Lab N, ‖B k‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hCS hC0
    _ ≤ C * (ℓ ^ 3 * Real.sqrt (∫ x : E3, ‖f x‖ ^ 2)
          * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2)) := mul_le_mul_of_nonneg_left hroot hC0
    _ = C * ℓ ^ 3 * Real.sqrt (∫ w : E3, ‖f w‖ ^ 2)
          * Real.sqrt (∫ y : E3, ‖g y‖ ^ 2) := by ring

theorem KfrU_pairing_eplus {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {fu : Work.BoseBoxFix.LowCut} {N : ℕ} {f g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hf : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (hg : MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))))
    (hfs : tsupport f ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ))
    (hgs : tsupport g ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)) :
    ‖∫ y : EuclideanSpace ℝ (Fin 3), g y * (∫ w : EuclideanSpace ℝ (Fin 3),
        Work.BoseBoxFock.PCFU.KfrU v h μ fu N (y + w) * f w)‖
      ≤ (∫ x : EuclideanSpace ℝ (Fin 3),
            |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x|)
          * (Work.BoseBoxFock.ellH v μ) ^ 3
          * Real.sqrt (∫ w : EuclideanSpace ℝ (Fin 3), ‖f w‖ ^ 2)
          * Real.sqrt (∫ y : EuclideanSpace ℝ (Fin 3), ‖g y‖ ^ 2) := by
  have hℓ : 0 < Work.BoseBoxFock.ellH v μ := Work.BoseBoxFock.ellH_pos v μ
  set C₀ : ℝ := ∫ x : E3,
      |Work.BoseFixR.W1fun v h (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x| with hC₀
  have hC₀0 : 0 ≤ C₀ := by
    rw [hC₀]
    exact MeasureTheory.integral_nonneg (fun x : E3 => abs_nonneg _)
  have hkey : (∫ y : E3, g y * (∫ w : E3,
        Work.BoseBoxFock.PCFU.KfrU v h μ fu N (y + w) * f w))
      = ∫ y : E3, g y * (∫ w : E3, (∑ k : Lab N,
          ((Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ) *
            Complex.exp (Complex.I *
              (inner ℝ (kmomLab (Work.BoseBoxFock.ellH v μ) N k) (y + w) : ℂ))) * f w) := by
    simp only [Work.BoseBoxFock.PCFU.KfrU]
  rw [hkey]
  refine KfrU_aux_pairing_sum_eplus_le (ℓ := Work.BoseBoxFock.ellH v μ) (N := N)
    (W := fun k => ((Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ))
    hℓ (C := C₀) hC₀0 (fun k => ?_) hf hg hfs hgs
  rw [Complex.norm_real, Real.norm_eq_abs, hC₀]
  exact KfrU_aux_W1h_abs_le h μ fu N k

end Work.BoseBoxFock.PCFU
