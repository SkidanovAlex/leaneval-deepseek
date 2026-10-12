import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.Middle_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.Middle_channels_aux` — shared auxiliary facts for the four channels of
# `Middle_expansion_repaired`

The repaired four-channel expansion of the cubic middle kernel
(`Submission/Work/BoseBoxFock/Middle_expansion_repaired.lean`, design:
`FINDING_Middle_expansion_FALSE.md`) evaluates, channel by channel, the double sum

    Σ_{s,k ∈ excited} Ŵ₁(k) f_L(s) · [channel],

using `summand_four_split` (PROVED, `PotCubicExpansion.lean`) and the guarded momentum
additivity `hsub : kmomLab ℓ N (s - k) = kmomLab ℓ N s - kmomLab ℓ N k`.

The channels (b), (c), (d) carry the weight `χ̂(ℓ•κ)`, and the evaluation of (c), (d) needs
`χ̂` in the **plus-phase** integral form `χ̂(ℓp) = ℓ^{-3}∫ χ_Λ(z)e^{+i⟪p,z⟫}dz` (the sign that
combines with the phases of the frames).  The `k`-frames acquire a **minus** phase in those
channels, so we record `Kfr`/`Kχfr` with the phase conjugated.  Everything here is
`sorry`-free and axiom-clean.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-- The complex `χ_Λ` is compactly supported (it is `chiLam ℓ` in disguise). -/
lemma hasCompactSupport_chiLam_complex (ℓ : ℝ) (hℓ : 0 < ℓ) :
    HasCompactSupport fun z : Ω => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) := by
  have hts : tsupport (fun z : Ω => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ))
      = tsupport (fun z : Ω => Work.BoseK15.corpusBox.chiLam ℓ z) := by
    simp only [tsupport]
    congr 1
    ext z; simp [Function.mem_support, Complex.ofReal_eq_zero]
  unfold HasCompactSupport
  rw [hts]
  exact (Work.BoseB4.BoxData.boxL_compact (Work.BoseK15.corpusBox) ℓ).of_isClosed_subset
    (isClosed_tsupport _) (Work.BoseB4.BoxData.tsupport_chiLam_subset (Work.BoseK15.corpusBox) hℓ)

/-- Integrability of `χ_Λ` against the **plus-phase** plane wave
(`integrable_chiLam_mul_exp` is the minus-phase companion). -/
lemma integrable_chiLam_mul_exp_plus (ℓ : ℝ) (hℓ : 0 < ℓ) (p : Ω) :
    Integrable fun z : Ω =>
      ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ p z : ℂ)) := by
  have hc : Continuous fun z : Ω => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (Work.BoseB4.BoxData.chiLam_cont (Work.BoseK15.corpusBox) ℓ)
  have he : Continuous fun z : Ω => Complex.exp (Complex.I * (inner ℝ p z : ℂ)) :=
    Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_const.inner continuous_id)))
  exact (hc.mul he).integrable_of_hasCompactSupport
    (HasCompactSupport.mul_right (hasCompactSupport_chiLam_complex ℓ hℓ))

/-- **The box Fourier transform of the window, plus-phase form**:
`χ̂(ℓ • p) = ℓ^{-3} ∫ χ_Λ(z) e^{+i⟪p,z⟫} dz`.  (`hatChi_eq_integral` in `Middle_aux` is the
minus-phase form; the two agree because `χ_Λ` is even.) -/
theorem hatChi_eq_integral_plus {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Ω) :
    ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ) =
      ((ℓ ^ 3 : ℝ) : ℂ)⁻¹ *
        ∫ z, ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ p z : ℂ)) := by
  rw [hatChi_eq_integral hℓ p]
  congr 1
  have hsub := (Measure.measurePreserving_neg (volume : Measure Ω)).integral_comp
    measurableEmbedding_neg
    (fun z : Ω => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
      * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ))
  rw [← hsub]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  simp only []
  rw [Work.BoseB4.BoxData.chiLam_even, inner_neg_right]
  have key : Complex.exp (-(Complex.I * ↑(-(inner ℝ p z))))
      = Complex.exp (Complex.I * ↑(inner ℝ p z)) := by
    congr 1; push_cast; ring
  rw [key]; ring

/-- **The `k`-frame with a minus phase**: `Kfr z = Σ_k Ŵ₁(k) e^{-i⟪κ_k,z⟫}` (the sum is
reindexed by `k ↦ -k`, using `W1h_neg`, `kmomLab_neg` and the neg-invariance of `excited`). -/
theorem Kfr_negPhase (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (z : Ω) :
    Kfr v h μ fu N z = ∑ k ∈ Work.BoseB7.excited (Lab N),
      ((W1h v h μ fu N k : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ))) := by
  rw [Kfr]
  rw [← sum_neg_excited (fun k : Lab N => ((W1h v h μ fu N k : ℝ) : ℂ)
      * Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ))))]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [W1h_neg, kmomLab_neg, inner_neg_left]
  congr 1
  push_cast
  ring_nf

/-- **The `χ̂`-weighted `k`-frame with a minus phase**:
`Kχfr z = Σ_k Ŵ₁(k)χ̂(ℓκ_k) e^{-i⟪κ_k,z⟫}`. -/
theorem Kχfr_negPhase (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (z : Ω) :
    Kχfr v h μ fu N z = ∑ k ∈ Work.BoseB7.excited (Lab N),
      (((W1h v h μ fu N k * hatChih v μ N k : ℝ)) : ℂ)
        * Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ))) := by
  rw [Kχfr]
  rw [← sum_neg_excited (fun k : Lab N => (((W1h v h μ fu N k * hatChih v μ N k : ℝ)) : ℂ)
      * Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ))))]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [W1h_neg, hatChih_neg, kmomLab_neg, inner_neg_left]
  congr 1
  push_cast
  ring_nf

/-- The `χ̂`-weight of the `(d)`-channel, in the plus-phase integral form, with the exact
spelling `hatChi (ℓ • κ n)` of `summand_four_split`. -/
theorem hatChi_lab_eq_integral_plus (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (n : Lab N) :
    ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • kmomLab (ellH v μ) N n) : ℝ) : ℂ) =
      (((ellH v μ) ^ 3 : ℝ) : ℂ)⁻¹ *
        ∫ z, ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N n) z : ℂ)) :=
  hatChi_eq_integral_plus (ellH_pos v μ) _

end Work.BoseBoxFock
