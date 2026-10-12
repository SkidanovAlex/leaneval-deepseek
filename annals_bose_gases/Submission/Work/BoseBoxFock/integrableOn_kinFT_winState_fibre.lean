import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.kinRow_lattice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability on the box of the fibre kinetic density

Target: for `Φ : X n → ℝ` smooth, a slot `j : Fin n` and a momentum `p`, the map

`x ↦ 1_{Λ(0)}(x_j) · ‖kinFT (winState ℓ (fibre n j Φ x)) p‖ ^ 2`

is integrable on the box `abox n ℓ = (acube ℓ)^n`.

The proof is qualitative: the window indicator is `1` on `abox n ℓ` (the box is inside the
support of `χ_{Λ}`), and the remaining factor is *continuous* in `x`.  Continuity is obtained
in three steps:

* the fibre mean `x ↦ (ℓ³)⁻¹ ∫_{acube ℓ} Φ (x_{j←z}) dz` is continuous by the parametric
  integral theorem over the compact cube `acube ℓ` (`continuous_parametric_integral_of_continuous`);
* consequently the *uncurried integrand* `(x,y) ↦ e^{−i⟪p,y⟫} χ_Λ(y) (Φ(x_{j←y}) − m x)` is
  continuous, which gives continuity of `x ↦ ∫_{acube ℓ} e^{−i⟪p,y⟫} winState ℓ (fibre n j Φ x) y dy`;
* `χ_Λ` vanishes off `acube ℓ` (`chiScale_support_le`), so that box integral *is*
  `kinFT (winState ℓ (fibre n j Φ x)) p`.

Finally a continuous function is integrable on the compact box (`integrableOn_abox_of_continuous'`),
and the pointwise identity `1_{Λ}(x_j)·g = g` on `abox n ℓ` transfers integrability
(`IntegrableOn.congr_fun`).
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- `corpusBox.chiLam ℓ` is the corpus window `chiScale ℓ`. -/
lemma chiLam_eq_chiScale (ℓ : ℝ) (y : E3) :
    Work.BoseK15.corpusBox.chiLam ℓ y = Submission.BoseGases.chiScale ℓ y := rfl

/-- The corpus window `χ_Λ` is continuous. -/
lemma continuous_chiLam (ℓ : ℝ) : Continuous (Work.BoseK15.corpusBox.chiLam ℓ) := by
  rw [show Work.BoseK15.corpusBox.chiLam ℓ = Submission.BoseGases.chiScale ℓ from rfl]
  exact Submission.BoseGases.chiScale_continuous ℓ

/-- The window `χ_Λ` vanishes outside the box `acube ℓ`. -/
lemma chiLam_eq_zero_of_notMem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {y : E3}
    (hy : y ∉ Submission.BoseGases.acube ℓ) :
    Work.BoseK15.corpusBox.chiLam ℓ y = 0 := by
  rw [chiLam_eq_chiScale]
  by_contra h
  exact hy (Submission.BoseGases.mem_acube_of_norm_le (le_of_lt hℓ)
    (Submission.BoseGases.chiScale_support_le hℓ h))

/-- **The fibre mean is continuous in the configuration**: the box integral of the `j`-th fibre
of a smooth `Φ`. -/
lemma continuous_fibre_mean {ℓ : ℝ} {n : ℕ} (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    Continuous (fun x : Submission.BoseGases.X n => (ℓ ^ 3)⁻¹ *
      ∫ z in Submission.BoseGases.acube ℓ, Φ (Function.update x j z)) := by
  refine Continuous.const_mul ?_ _
  refine continuous_parametric_integral_of_continuous
    (f := fun (x : Submission.BoseGases.X n) (z : E3) => Φ (Function.update x j z)) ?_
    (Work.UBBInputs9.B.acube_isCompact ℓ)
  exact hΦ.continuous.comp (continuous_update j)

/-- **Continuity of the fibre Fourier transform**: `x ↦ kinFT (winState ℓ (fibre n j Φ x)) p` is
continuous on the full configuration space. -/
lemma continuous_kinFT_winState_fibre {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) (p : E3) :
    Continuous (fun x : Submission.BoseGases.X n =>
      Submission.BoseGases.kinFT (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x)) p) := by
  set m : Submission.BoseGases.X n → ℝ := fun x => (ℓ ^ 3)⁻¹ *
      ∫ z in Submission.BoseGases.acube ℓ, Φ (Function.update x j z) with hm
  have hmc : Continuous m := continuous_fibre_mean j hΦ
  set f : Submission.BoseGases.X n → E3 → ℂ := fun x y =>
      Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) *
        ((Work.BoseK15.corpusBox.chiLam ℓ y : ℂ) *
          (((Φ (Function.update x j y) - m x) : ℝ) : ℂ)) with hf
  have hfc : Continuous (Function.uncurry f) := by
    show Continuous (fun q : Submission.BoseGases.X n × E3 =>
      Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ))) *
        ((Work.BoseK15.corpusBox.chiLam ℓ q.2 : ℂ) *
          (((Φ (Function.update q.1 j q.2) - m q.1) : ℝ) : ℂ)))
    refine Continuous.mul ?_ (Continuous.mul ?_ ?_)
    · fun_prop
    · exact Complex.continuous_ofReal.comp ((continuous_chiLam ℓ).comp continuous_snd)
    · exact Complex.continuous_ofReal.comp
        ((hΦ.continuous.comp (continuous_update j)).sub (hmc.comp continuous_fst))
  have hparam : Continuous (fun x : Submission.BoseGases.X n =>
      ∫ y in Submission.BoseGases.acube ℓ, f x y) :=
    continuous_parametric_integral_of_continuous (f := f) hfc
      (Work.UBBInputs9.B.acube_isCompact ℓ)
  refine hparam.congr (fun x => ?_)
  rw [Submission.BoseGases.kinFT]
  have hzero : ∀ y ∉ Submission.BoseGases.acube ℓ,
      Complex.exp (-(Complex.I * ((inner ℝ p y : ℝ) : ℂ))) *
        Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x) y = 0 := by
    intro y hy
    simp only [Work.BoseBoxFock.winState]
    rw [chiLam_eq_zero_of_notMem_acube hℓ hy]
    simp
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Submission.BoseGases.acube ℓ) hzero]
  refine setIntegral_congr_fun (Submission.BoseGases.acube_measurable ℓ) ?_
  intro y hy
  simp only [hf, hm, Work.BoseBoxFock.winState, Work.BoseKinLoc.fibre]

theorem integrableOn_kinFT_winState_fibre {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} (j : Fin n)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      Work.BoseKinLoc.indU ℓ 0 (x j) *
        ‖Submission.BoseGases.kinFT
          (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x)) p‖ ^ 2)
      (Submission.BoseGases.abox n ℓ) := by
  have hcont : Continuous (fun x : Submission.BoseGases.X n =>
      ‖Submission.BoseGases.kinFT
        (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x)) p‖ ^ 2) :=
    (continuous_kinFT_winState_fibre hℓ j hΦ p).norm.pow 2
  have hint : MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n =>
      ‖Submission.BoseGases.kinFT
        (Work.BoseBoxFock.winState ℓ (Work.BoseKinLoc.fibre n j Φ x)) p‖ ^ 2)
      (Submission.BoseGases.abox n ℓ) :=
    Work.UBBInputs9.B.integrableOn_abox_of_continuous' hcont
  refine hint.congr_fun ?_ (Submission.BoseGases.abox_measurable n ℓ)
  intro x hx
  have hxj : x j ∈ Work.BoseKinLoc.lamBox ℓ 0 := by
    simpa [Work.BoseKinLoc.lamBox, Work.BSKinetic.bsBox] using hx j
  simp [Work.BoseKinLoc.indU, hxj]

end Work.BoseBoxFock
