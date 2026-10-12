import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.LatFourierDefs
import Submission.Work.BoseBoxFock.kinFT_lattice_tail_sq_lt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.frameSampling_latBox`

The frame (Poisson/aliasing) identity for states supported in the **closed cube**
`latBox ℓ = [0,ℓ]³` at the origin:

    ∑_n ‖ĝ(kmomInt ℓ n)‖² = ℓ³ ∫ ‖g‖² ,      k_n = kmomInt ℓ n = (2π/ℓ)·n .

This is the "sampling" form of Parseval for the orthonormal Fourier basis of `L²([0,ℓ]³)`,
i.e. the Fourier coefficients of the periodisation of `g` on the torus of period `ℓ`.

The proof reduces it to the already proved `L²` frame identity at the **centred** box
`Work.BoseBoxFock.hasSum_kinFT_lattice_L2`, by translating `g` so that its support lands in
`boxL ℓ = [-ℓ/2,ℓ/2]³`: if `c = (ℓ/2,ℓ/2,ℓ/2)` then `y ↦ g (y + c)` is supported in `boxL ℓ`
(because `tsupport g ⊆ latBox ℓ = c + boxL ℓ`), and both the sampling coefficients and the
`L²` mass are unchanged, since

* `‖kinFT (g(· + c)) p‖ = ‖kinFT g p‖` (`Work.BSKinetic.Decomp.norm_kinFT_comp_add`), and
* `∫ ‖g(· + c)‖² = ∫ ‖g‖²` (translation invariance of Lebesgue measure).
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory
open scoped Pointwise

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Translation invariance of the Lebesgue integral on `ℝ³` for real-valued functions. -/
private lemma integral_comp_add_right_r (f : E3 → ℝ) (a : E3) :
    (∫ y : E3, f (y + a)) = ∫ y : E3, f y := by
  let e : E3 ≃ᵐ E3 := MeasurableEquiv.addRight a
  have hmp : MeasurePreserving (⇑e) volume volume := by
    change MeasurePreserving (fun x : E3 => x + a) volume volume
    exact measurePreserving_add_right volume a
  simpa [e] using (hmp.integral_comp' (f := e) (g := f))

theorem frameSampling_latBox {ℓ : ℝ} (hℓ : 0 < ℓ) {g : EuclideanSpace ℝ (Fin 3) → ℂ}
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.volume)
    (hsupp : tsupport g ⊆ Work.BoseBoxFock.LatFourier.latBox ℓ) :
    HasSum (fun n : Fin 3 → ℤ =>
        ‖Submission.BoseGases.kinFT g (Work.BoseBoxFock.kmomInt ℓ n)‖ ^ 2)
      (ℓ ^ 3 * ∫ x : EuclideanSpace ℝ (Fin 3), ‖g x‖ ^ 2) := by
  -- the shift vector `c = (ℓ/2, ℓ/2, ℓ/2)`, so that `latBox ℓ = c + boxL ℓ`
  set c : E3 := WithLp.toLp 2 (fun _ : Fin 3 => ℓ / 2) with hcdef
  -- the shifted state is `L²` (translation preserves Lebesgue measure)
  have hmemLp : MeasureTheory.MemLp (fun y : E3 => g (y + c)) 2 (volume : Measure E3) :=
    hg.comp_measurePreserving (measurePreserving_add_right (volume : Measure E3) c)
  -- ... and is supported in the *centred* box `boxL ℓ`
  have hsupp' : tsupport (fun y : E3 => g (y + c)) ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
    refine closure_minimal (fun y hy => ?_) (Work.BoseK15.corpusBox.boxL_compact ℓ).isClosed
    have hyt : y + c ∈ tsupport g := subset_tsupport g (Function.mem_support.mpr hy)
    have hm : y + c ∈ LatFourier.latBox ℓ := hsupp hyt
    have hcell : Work.BoseK15.corpusBox.boxL ℓ = (ℓ : ℝ) • Work.BoseB4.unitCell := rfl
    rw [hcell]
    refine ⟨(ℓ⁻¹ : ℝ) • y, ?_, ?_⟩
    · show ∀ i : Fin 3, |((ℓ⁻¹ : ℝ) • y) i| ≤ (1 / 2 : ℝ)
      intro i
      have hi := (LatFourier.mem_latBox.mp hm) i
      have hci : c i = ℓ / 2 := by rw [hcdef]
      have hsum : (y + c) i = y i + ℓ / 2 := by rw [WithLp.ofLp_add, Pi.add_apply, hci]
      have hyabs : |y i| ≤ ℓ / 2 := by
        rw [hsum] at hi
        exact abs_le.mpr ⟨by linarith [hi.1], by linarith [hi.2]⟩
      have hsmul : ((ℓ⁻¹ : ℝ) • y) i = ℓ⁻¹ * y i := by
        rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
      rw [hsmul, abs_mul, abs_of_pos (inv_pos.mpr hℓ)]
      calc ℓ⁻¹ * |y i| ≤ ℓ⁻¹ * (ℓ / 2) :=
            mul_le_mul_of_nonneg_left hyabs (le_of_lt (inv_pos.mpr hℓ))
        _ = 1 / 2 := by field_simp
    · show ℓ • (ℓ⁻¹ • y) = y
      rw [smul_inv_smul₀ (ne_of_gt hℓ)]
  -- the `L²` frame identity at the centred box
  have hmain := hasSum_kinFT_lattice_L2 hℓ hmemLp hsupp'
  -- the sampling coefficients do not see the translation
  have hpt : ∀ n : Fin 3 → ℤ,
      ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2
        = ‖Submission.BoseGases.kinFT (fun y : E3 => g (y + c)) (kmomInt ℓ n)‖ ^ 2 :=
    fun n => congrArg (fun r : ℝ => r ^ 2)
      (Work.BSKinetic.Decomp.norm_kinFT_comp_add g c (kmomInt ℓ n)).symm
  -- the two `L²` masses agree
  have hval : (∫ x : E3, ‖(fun y : E3 => g (y + c)) x‖ ^ 2) = ∫ x : E3, ‖g x‖ ^ 2 :=
    integral_comp_add_right_r (fun x : E3 => ‖g x‖ ^ 2) c
  have hres : HasSum (fun n : Fin 3 → ℤ =>
      ‖Submission.BoseGases.kinFT g (kmomInt ℓ n)‖ ^ 2)
      (ℓ ^ 3 * ∫ x : E3, ‖(fun y : E3 => g (y + c)) x‖ ^ 2) := hmain.congr_fun hpt
  rw [hval] at hres
  exact hres

end Work.BoseBoxFock
