import Mathlib
import Submission.Work.KMTPlan.A6Clean.AdelicPacketFam
import Submission.Work.A6Clean.VrLiftSamplingLattice
import Submission.Work.KMTPlan.A6Clean.charSumResidueTwo
import Submission.Work.A6Clean.VrLiftClip
import Submission.Work.A6Clean.mdlSliceG_varNorm_lt_top
import Submission.Work.A6Clean.mdlSliceG_fiberVarSamplingId
import Submission.Work.KMTAreas.A7Rep.fiberResidueMaxRephaseL2
import Submission.Work.A7Hi.varEstTle_compositeCompare
import Submission.Work.KMTPlan.A6.ZModVariationalChainProb
import Submission.Port.Aesm

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.A6Clean

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section

/-! ## Helper lemmas

The interface facts of the `g`-side assembly: the identification of the packet slice with the
character sum over the *exact*-height amplitudes, its real-frequency support (which feeds the
vector-valued lattice sampling `VrLiftSamplingLattice`), the monotonicity of the `goodScale` gate
along a lacunary scale sequence, the `ℓ²`-membership of the model slice `mdlSliceG`, and the
identification of the arithmetic fibre `fiberOp` with the character sum of the lift's amplitudes. -/

/-- The packet slice is the character sum of the **exact**-height amplitudes: the sum in
`Work.KMTPlan.A6Clean.packetFamG` runs over `iwArithFreqs ρ l₂`, but the lift vanishes off
`iwArithFreqsNew ρ l₂`. -/
lemma pfG_charSum (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (W : ℕ → Circ → ℝ → ℂ)
    (hW0 : ∀ (n : ℕ) (α : Circ),
      α ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ → W n α = 0)
    (n : ℕ) (X : ℝ) (θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) :
    Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W n X θ
      = if Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
            (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
          ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
            fourier (T := 1) (-(θ.val : ℤ)) α * W n α X
        else 0 := by
  rw [Work.KMTPlan.A6Clean.packetFamG_apply]
  by_cases hg : Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
      (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a n))
  · simp only [hg, if_true]
    exact (Finset.sum_subset
      (fun x hx => Work.KMTAreas.A7.mem_iwArithFreqsNew_le hx)
      (fun x _ hx' => by rw [hW0 n x hx']; simp)).symm
  · simp only [hg, if_false]

/-- **The packet slices have real frequency support in `Icc (-1/4) (1/4)`**, because they are
finite character combinations of the lifts, each of which has that support. -/
lemma pfG_hasRealFreqSupport (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (W : ℕ → Circ → ℝ → ℂ)
    (hW0 : ∀ (n : ℕ) (α : Circ),
      α ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ → W n α = 0)
    (hWb : ∀ (n : ℕ) (α : Circ),
      Work.KMTAreas.A7Rep.HasRealFreqSupport (W n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4)))
    (n : ℕ) (θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) :
    Work.KMTAreas.A7Rep.HasRealFreqSupport
      (fun X : ℝ => Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W n X θ)
      (Set.Icc (-(1 / 4 : ℝ)) (1 / 4)) := by
  by_cases hg : Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
      (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a n))
  · have hfun : (fun X : ℝ => Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W n X θ)
        = fun X : ℝ => ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
            fourier (T := 1) (-(θ.val : ℤ)) α * W n α X := by
      funext X
      rw [pfG_charSum ρ a l₁ l₂ k₁ k₂ W hW0 n X θ, if_pos hg]
    rw [hfun]
    exact Work.KMTAreas.A7Rep.hasRealFreqSupport_finset_sum _
      (fun α _ => Work.KMTAreas.A7Rep.hasRealFreqSupport_const_mul _ (hWb n α))
  · have hfun : (fun X : ℝ => Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W n X θ)
        = fun _ : ℝ => (0 : ℂ) := by
      funext X
      rw [pfG_charSum ρ a l₁ l₂ k₁ k₂ W hW0 n X θ, if_neg hg]
    rw [hfun]
    exact Work.KMTPlan.A6Clean.hasRealFreqSupport_zero _

/-- **The gate `goodScale Q L ⌊a n⌋` is monotone in `n`** along a lacunary scale sequence. -/
lemma pfG_goodScale_mono {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n)
    (Q L : ℕ) ⦃n m : ℕ⦄ (hnm : n ≤ m)
    (h : Work.KMTPlan.A6.goodScale Q L (Nat.floor (a n))) :
    Work.KMTPlan.A6.goodScale Q L (Nat.floor (a m)) := by
  have hmono : Monotone a := by
    refine monotone_nat_of_le_succ fun k => ?_
    have hpos : (0 : NNReal) < a k := lt_of_lt_of_le zero_lt_one (ha1 k)
    have h1 : (Λ : NNReal) < a (k + 1) / a k := ha k
    have hmul : (Λ : NNReal) * a k < a (k + 1) := by
      rw [lt_div_iff₀ hpos] at h1
      exact h1
    calc a k = 1 * a k := (one_mul _).symm
      _ ≤ (Λ : NNReal) * a k :=
          mul_le_mul_of_nonneg_right (le_of_lt hΛ) (show (0:NNReal) ≤ a k from bot_le)
      _ ≤ a (k + 1) := le_of_lt hmul
  have hfl : Nat.floor (a n) ≤ Nat.floor (a m) := Nat.floor_mono (hmono hnm)
  exact le_trans h hfl

/-- The exact-height arithmetic frequencies of the `g`-side are killed by `arithQ ρ (max l₁ l₂)`. -/
lemma pfG_arithQ_nsmul (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l₁ l₂ : ℕ)
    {α : Circ} (hα : α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) :
    (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℕ) • α = 0 :=
  Work.KMTAreas.A7.arithQ_nsmul_eq_zero
    (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 (le_max_right l₁ l₂)
      (Work.KMTAreas.A7.mem_iwArithFreqsNew_le hα))

/-- **`mdlSliceG` is square summable** whenever `g` is.  Rather than repeating the model-operator
analysis, we use the proved finiteness `Work.A6Clean.mdlSliceG_varNorm_lt_top` of the
`ℓ²`-variational norm of the whole slice family: the variational norm dominates the values
(`Work.KMTAreas.A7.enorm_apply_le_variationalNorm`), hence each slice is in `ℓ²`. -/
lemma pfG_memℓp_mdlSliceG (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal) (hΛ : 1 < Λ)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₂ : k₂ = 0 → j₂ ≠ -1) (g : ℤ → ℂ)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (R : NNReal) (hR : 2 < R) (n : ℕ) :
    Memℓp (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) 2 := by
  refine Work.KMTPlan.A6.memlpOfMemLpCount (p := 2) (by norm_num) (by norm_num) ?_
  refine MeasureTheory.memLp_iff.mpr ?_
  have hV := Work.A6Clean.mdlSliceG_varNorm_lt_top P hd ρ hρ hρ1 C₀ a Λ hΛ ha ha1
    l₁ l₂ k₁ k₂ t j₂ hj₂ hk₂ g hg ht R hR
  refine lt_of_le_of_lt (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x : ℤ => ?_)) hV
  have h := Work.KMTAreas.A7.enorm_apply_le_variationalNorm
    (r := R) (fun m : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g m x) n
  simpa only [enorm_eq_self] using h

/-- **The convolution defining the fibre is absolutely summable**: the kernel `cw (mStargF d U)` is
`ℓ¹` and the input is `ℓ²`. -/
lemma pfG_summable_cw (P : Polynomial ℤ) (U : ℕ) (h : ℤ → ℂ) (hh : Memℓp h 2) (x : ℤ) :
    Summable (fun j : ℤ => Work.KMTAreas.A7.cw
        (Work.KMTAreas.A7.mStargF P.natDegree U) j * h (x - j)) :=
  Work.KMTAreas.A7.summable_cw_mul_of_memℓp
    (Work.KMTAreas.A7.summable_norm_cw_mStargF P U) hh x

/-- **The arithmetic fibre is the character sum of the lift's amplitudes**: at an integer point `m`
and residue `n₀`, `fiberOp ρ l₂ m⋆ n₀ (h n) m = ∑_{α ∈ (ℚ/ℤ)_{l₂}} e((n₀-m)α)·W n α m`. -/
lemma pfG_fiberOp_eq (ρ : ℝ) (l₂ : ℕ) (mm : ℝ → ℂ) (h : ℕ → ℤ → ℂ) (W : ℕ → Circ → ℝ → ℂ)
    (hWs : ∀ (n : ℕ) (α : Circ), α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ →
      ∀ x : ℤ, W n α (x : ℝ) = Work.KMTAreas.A7.winConvR mm
        (Work.KMTAreas.A7.winModR (-α) (h n)) x)
    (hsumm : ∀ (n : ℕ) (x : ℤ), Summable (fun j : ℤ => Work.KMTAreas.A7.cw mm j * h n (x - j)))
    (n : ℕ) (n₀ m : ℤ) :
    Work.KMTAreas.A7.fiberOp ρ l₂ mm n₀ (h n) m
      = ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
          fourier (T := 1) (n₀ - m) α * W n α (m : ℝ) := by
  rw [Work.KMTAreas.A7.fiberOp_eq_phaseRotation_windowCut ρ l₂ mm n₀ (h n) m (hsumm n m)]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  have hwin : Work.KMTAreas.A7.winModR α
        (Work.KMTAreas.A7.winConvR mm (Work.KMTAreas.A7.winModR (-α) (h n))) m
      = fourier (T := 1) (-m) α * W n α (m : ℝ) := by
    rw [Work.KMTAreas.A7.winModR, hWs n α hα m]
  rw [hwin, Work.KMTPlan.A6Clean.fourier_sub_eq_mulR]
  ring

/-- **The `HasRealFreqSupport` form of the vector-valued lattice sampling**, obtained from
`Work.A6Clean.VrLiftSamplingLattice` by unpacking the amplitude witnesses. -/
lemma pfG_sampling_HRF :
    ∃ C : ℝ, 0 < C ∧ ∀ {Q : ℕ} [NeZero Q] (R : ℝ) (hR : 1 ≤ R) (B : ℕ → ZMod Q → ℝ → ℂ),
      (∀ (n : ℕ) (θ : ZMod Q),
        Work.KMTAreas.A7Rep.HasRealFreqSupport (B n θ) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4))) →
      ∫⁻ X : ℝ, (Work.KMTPlan.A6.VrLiftDataP R Q (fun n θ => B n θ X)) ^ (2 : ℕ)
        ≤ ENNReal.ofReal C * ∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP R Q
            (fun n θ => B n θ ((m : ℤ) : ℝ))) ^ (2 : ℕ) := by
  obtain ⟨C, hC, h⟩ := Work.A6Clean.VrLiftSamplingLattice
  refine ⟨C, hC, ?_⟩
  intro Q _ R hR B hB
  choose g hgint hgsupp hgpt using hB
  have hmain := h R hR g hgint hgsupp
  have h1 : (∫⁻ X : ℝ, (Work.KMTPlan.A6.VrLiftDataP R Q (fun n θ => B n θ X)) ^ (2 : ℕ))
      = ∫⁻ X : ℝ, (Work.KMTPlan.A6.VrLiftDataP R Q
          (fun n θ => FourierTransformInv.fourierInv (g n θ) X)) ^ (2 : ℕ) := by
    rw [show (fun X : ℝ => (Work.KMTPlan.A6.VrLiftDataP R Q (fun n θ => B n θ X)) ^ (2 : ℕ))
        = (fun X : ℝ => (Work.KMTPlan.A6.VrLiftDataP R Q
            (fun n θ => FourierTransformInv.fourierInv (g n θ) X)) ^ (2 : ℕ)) from
      funext fun X => congrArg
        (fun u : ℕ → ZMod Q → ℂ => (Work.KMTPlan.A6.VrLiftDataP R Q u) ^ (2 : ℕ))
        (funext fun n => funext fun θ => hgpt n θ X)]
  have h2 : (∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP R Q
          (fun n θ => B n θ ((m : ℤ) : ℝ))) ^ (2 : ℕ))
      = ∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP R Q
          (fun n θ => FourierTransformInv.fourierInv (g n θ) ((m : ℤ) : ℝ))) ^ (2 : ℕ) := by
    apply tsum_congr
    intro m
    have hfun : (fun (n : ℕ) (θ : ZMod Q) => B n θ ((m : ℤ) : ℝ))
        = (fun (n : ℕ) (θ : ZMod Q) =>
            FourierTransformInv.fourierInv (g n θ) ((m : ℤ) : ℝ)) := by
      funext n θ
      exact hgpt n θ ((m : ℤ) : ℝ)
    rw [hfun]
  rw [h1, h2]
  exact hmain

/-- The loss weight is multiplicative in its first (exponent) argument. -/
lemma pfG_lossWeight_add (c d ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    Work.KMTAreas.A7.lossWeight (c + d) ρ l₁ l₂ k₁ k₂
      = Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂
        * Work.KMTAreas.A7.lossWeight d ρ l₁ l₂ k₁ k₂ := by
  have hXnn : (0 : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lmaxR, Work.Analysis.EndVar.lmax]
    have h : (0 : ℤ) ≤ max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)) := by positivity
    exact_mod_cast h
  have hX : (0 : ℝ) < 1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by linarith
  have h1 : (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ (c + d)
      = (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ c
        * (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ d := Real.rpow_add hX c d
  have h2 : (2 : ℝ) ^ ((c + d) * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)
      = (2 : ℝ) ^ (c * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂)
        * (2 : ℝ) ^ (d * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) := by
    rw [show (c + d) * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂
        = c * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂
          + d * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ from by ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  simp only [Work.KMTAreas.A7.lossWeight]
  rw [h1, h2]
  ring

end

/-! ## The integer comparison

At an integer sample `y`, the `V^R`-datum of the packet family is dominated by the residue datum of
the arithmetic fibres of the model slice: clip at the gate (`VrLiftClip`, the gate being a monotone
upper set), apply the Parseval/residue bound `CharSumResidue` for the exact-height character sums,
and identify the `ZMod Q`-fibre with the arithmetic fibre `fiberOp` (`pfG_fiberOp_eq`). -/
lemma pfG_integer_le (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ)
    (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal)
    (hΛ : 1 < Λ) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₂ : k₂ = 0 → j₂ ≠ -1) (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1)
    (W : ℕ → Circ → ℝ → ℂ)
    (hWb : ∀ (n : ℕ) (α : Circ),
      Work.KMTAreas.A7Rep.HasRealFreqSupport (W n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4)))
    (hWs : ∀ (n : ℕ) (α : Circ), α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ →
      ∀ x : ℤ, W n α (x : ℝ) = Work.KMTAreas.A7.winConvR
        (Work.KMTAreas.A7.mStargF P.natDegree
          (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
        (Work.KMTAreas.A7.winModR (-α)
          (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n)) x)
    (hW0 : ∀ (n : ℕ) (α : Circ),
      α ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ → W n α = 0)
    (R : NNReal) (hR : 2 < R) (y : ℤ) :
    Work.KMTPlan.A6.VrLiftDataP (R : ℝ) (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
        (fun n : ℕ => Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W n (y : ℝ))
      ≤ (4 : ENNReal) * Work.KMTAreas.A7.residueLp 2 (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
          (fun y' n₀ => PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
            Work.KMTAreas.A7.fiberOp ρ l₂
              (Work.KMTAreas.A7.mStargF P.natDegree
                (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
              (n₀ : ℤ) (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) y')) y := by
  classical
  haveI : NeZero (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) :=
    ⟨Nat.pos_iff_ne_zero.mp (Work.KMTAreas.A7.arithQ_pos ρ (max l₁ l₂))⟩
  -- summability of the fibre's defining convolution
  have hsumm : ∀ (n : ℕ) (x : ℤ), Summable (fun j : ℤ =>
      Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF P.natDegree
          (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j *
        Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n (x - j)) :=
    fun n x => pfG_summable_cw P _ _
      (pfG_memℓp_mdlSliceG P hd ρ hρ hρ1 C₀ a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ t j₂ hj₂ hk₂ g hg ht
        R hR n) x
  -- the fibre identity
  have hfib : ∀ (n : ℕ) (n₀ z : ℤ), Work.KMTAreas.A7.fiberOp ρ l₂
      (Work.KMTAreas.A7.mStargF P.natDegree
        (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) n₀
      (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) z
      = ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
          fourier (T := 1) (n₀ - z) α * W n α (z : ℝ) :=
    fun n n₀ z => pfG_fiberOp_eq ρ l₂ _ _ W hWs hsumm n n₀ z
  -- the gate is a monotone upper set
  have hγmono : ∀ ⦃n m : ℕ⦄, n ≤ m →
      Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
          (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) →
      Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
          (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a m)) :=
    fun n m hnm hn => pfG_goodScale_mono hΛ ha ha1 _ _ hnm hn
  -- the packet family at the integer `y` is the gated exact-height character sum
  have hpack : (fun (n : ℕ) => Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W n (y : ℝ))
      = fun (n : ℕ) (θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) =>
          if Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
            ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
              fourier (T := 1) (-(θ.val : ℤ)) α * W n α (y : ℝ)
          else 0 := by
    funext n θ
    exact pfG_charSum ρ a l₁ l₂ k₁ k₂ W hW0 n (y : ℝ) θ
  rw [hpack]
  -- clip at the gate
  have hR2nn : (2 : NNReal) ≤ R := le_of_lt hR
  have hR1nn : (1 : NNReal) ≤ R := le_trans (by norm_num) hR2nn
  have hR1R : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1nn
  have hclip := Work.A6Clean.VrLiftClip (Q := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) (R : ℝ) hR1R
    (fun n : ℕ => Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
      (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)))
    hγmono
    (fun (n : ℕ) (θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) =>
      ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
        fourier (T := 1) (-(θ.val : ℤ)) α * W n α (y : ℝ))
  refine hclip.trans ?_
  -- Parseval for the exact-height character sums
  have hcs := Work.KMTPlan.A6Clean.charSumResidueTwo (Q := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) R hR2nn
    (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂)
    (fun α hα => pfG_arithQ_nsmul ρ hρ hρ1 l₁ l₂ hα)
    (fun α => fourier (T := 1) (-y) α)
    (fun α => Work.KMTAreas.A7.norm_fourier_applyR (-y) α)
    (fun (n : ℕ) (α : Circ) => W n α (y : ℝ))
  -- identify the `ZMod Q`-fibre with the arithmetic fibre
  have hid : (fun (_ : ℤ) (n₀ : ℕ) => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
          fourier (T := 1) (n₀ : ℤ) α * (fourier (T := 1) (-y) α * W n α (y : ℝ))))
      = fun (_ : ℤ) (n₀ : ℕ) => PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOp ρ l₂
            (Work.KMTAreas.A7.mStargF P.natDegree
              (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            (n₀ : ℤ) (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) y) := by
    funext zz n₀
    congr 1
    funext n
    rw [hfib n (n₀ : ℤ) y]
    refine Finset.sum_congr rfl (fun α hα => ?_)
    rw [Work.KMTPlan.A6Clean.fourier_sub_eq_mulR]
    ring
  -- the two residue data are the same datum (the `CharSumResidue` side does not use its outer
  -- variable, and the fibre side is evaluated at the integer `y`)
  have hRcs : Work.KMTAreas.A7.residueLp 2 (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
      (fun (_ : ℤ) (n₀ : ℕ) => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂,
          fourier (T := 1) (n₀ : ℤ) α * (fourier (T := 1) (-y) α * W n α (y : ℝ)))) 0
      = Work.KMTAreas.A7.residueLp 2 (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
          (fun y' n₀ => PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
            Work.KMTAreas.A7.fiberOp ρ l₂
              (Work.KMTAreas.A7.mStargF P.natDegree
                (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
              (n₀ : ℤ) (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) y')) y := by
    rw [hid]
    rfl
  refine (add_le_add hcs hcs).trans ?_
  simp only [hRcs]
  simp only [Work.KMTAreas.A7.residueLp]
  exact le_of_eq (by ring)

/- **The uniform `(lin-2)` clause of the §8 adelic form** — the `g`-side twin of
`Work.KMTPlan.A6Clean.PacketFamFUniform` (and the proved copy, under a new name, of
`Work.KMTPlan.A6Clean.packetFamG_linUniform` which sits with a `sorry` in
`VrSamplingVecUniform.lean`).

This is the shape `AdelicClausesAt` consumes: `A`, `ρ₀`, `K` are chosen *before* the datum
`(a, Λ, l₁, l₂, k₁, k₂, t, g, W)`.  Same route as the `f`-side (see
`NOTES_A6_VrSamplingVecUniform_SESSION.md` §2, workspace root):

1. `packetFamG ⋯ n X θ = 𝓕⁻(B n θ) X` for `B n θ := Σ_{α ∈ iwArithFreqsNew ρ l₂} e (-(θ.val : ℤ)) α • A_{n,α}`;
2. vector-valued lattice sampling (`VrLiftSamplingLattice` / in-file if it has not landed);
3. at integers replace the `α`-sum by the `g`-side fibre
   `fiberOpP ρ P l₂ (mStargF P.natDegree U) n₀ (mdlSliceG ⋯ n) ·`
   (`fiberOpSet_eq_windowPieceR` with the `P`-twist / `fiberOpPSet`, or the corresponding proved
   identity for `fiberOpP`), using `hWs` and `hW0`, and orthogonality of the `Q`-torsion
   characters (`lintegral_charSum_eq`); **no factor of `Q`**;
4. apply the PROVED `Work.KMTPlan.A6Clean.mdlSliceG_fiberVarSampling R hR` (at `p := 2`; `A = 0`,
   `C₁ = C₁(ρ)` uniform in the datum) and the PROVED
   `Work.KMTPlan.A6.MdlSliceLinG P hd C₀ hC₀ R hR j₂ hj₂` (giving `A₀, ρ₀, K` independent of the
   datum) to conclude
   `∫⁻ X (VrLiftDataP ⋯)^2 ≤ (K Λ)^2 * ofReal (lossWeight A ρ l₁ l₂ k₁ k₂)^2 * (eLpNorm g 2)^2`.-/
theorem PacketFamGUniformAlt (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (R : NNReal) (hR : 2 < R) (j₂ : ℤ) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ)
          (W : ℕ → Work.Analysis.IonescuWainger.Circle → ℝ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
          MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
          t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₂ = 0 → j₂ ≠ -1) →
          (∀ (n : ℕ) (α : Work.Analysis.IonescuWainger.Circle),
            Work.KMTAreas.A7Rep.HasRealFreqSupport (W n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4))) →
          (∀ (n : ℕ) (α : Work.Analysis.IonescuWainger.Circle),
            α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ → ∀ x : ℤ,
            W n α (x : ℝ) = Work.KMTAreas.A7.winConvR
              (Work.KMTAreas.A7.mStargF P.natDegree
                (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
              (Work.KMTAreas.A7.winModR (-α)
                (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n)) x) →
          (∀ (n : ℕ) (α : Work.Analysis.IonescuWainger.Circle),
            α ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ → W n α = 0) →
          ∫⁻ X : ℝ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
              (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun n : ℕ => Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W n X)) ^ (2 : ℕ)
            ≤ (K Λ : ENNReal) ^ (2 : ℕ)
              * (ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ)
              * (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
  classical
  -- (0) the two proved inputs
  obtain ⟨A₀, hA₀, ρ₀L, hρ₀L, hLin⟩ := Work.KMTPlan.A6.MdlSliceLinG P hd C₀ hC₀ R hR j₂ hj₂
  obtain ⟨A₁, hA₁, ρ₀V, hρ₀V, hFib⟩ :=
    Work.A6Clean.mdlSliceG_fiberVarSamplingId P hd R hR
  obtain ⟨Cs, hCspos, hSamp⟩ := pfG_sampling_HRF
  have hR1' : (1 : NNReal) ≤ R := le_of_lt (lt_of_le_of_lt (by norm_num) hR)
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1'
  refine ⟨A₀ + A₁, by linarith, min 1 (min ρ₀L ρ₀V), lt_min one_pos (lt_min hρ₀L hρ₀V), ?_⟩
  intro ρ hρ hρ₀
  have hρ1 : ρ ≤ 1 := le_trans hρ₀ (min_le_left _ _)
  have hρL : ρ ≤ ρ₀L := le_trans hρ₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρV : ρ ≤ ρ₀V := le_trans hρ₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨K₀, hK₀⟩ := hLin ρ hρ hρL
  obtain ⟨C₁, hC₁pos, hfibEst⟩ := hFib ρ hρ hρV
  let c₀ : NNReal := ⟨max 1 (Real.sqrt (16 * Cs * (max C₁ 1) ^ 2)), by positivity⟩
  refine ⟨fun Λ => K₀ Λ * c₀, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t g W hΛ ha ha1 hg ht hk₂ hWb hWs hW0
  haveI : NeZero (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) :=
    ⟨Nat.pos_iff_ne_zero.mp (Work.KMTAreas.A7.arithQ_pos ρ (max l₁ l₂))⟩
  -- (1) the model slice family and its two norms
  let GG : ℤ → ENNReal := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
    (fun n : ℕ => Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n x)
  let RR : ℤ → ENNReal := fun x : ℤ => Work.KMTAreas.A7.residueLp 2
    (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
    (fun y' n₀ => PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
      Work.KMTAreas.A7.fiberOp ρ l₂
        (Work.KMTAreas.A7.mStargF P.natDegree
          (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
        n₀ (Work.KMTPlan.A6.mdlSliceG ρ P C₀ a l₁ l₂ k₁ k₂ j₂ t g n) y')) x
  have hlin1 : MeasureTheory.eLpNorm GG 2 MeasureTheory.Measure.count
      ≤ (K₀ Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    have h := hK₀ a Λ l₁ l₂ k₁ k₂ t g hΛ ha ha1 ht hk₂
    have heq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
          if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
            Work.KMTAreas.A7.Tle ρ l₂
              (Work.KMTPlan.A6.varphitildeNtj P (Nat.floor (a n)) k₂ j₂ t)
              (Work.KMTPlan.A6.mdlG ρ P
                (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₂ g) x
          else 0)) = GG := by
      funext x
      congr 1
      funext n
      by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
      · simp only [hc, if_true, Work.KMTPlan.A6.mdlSliceG]
      · simp only [hc, if_false, Work.KMTPlan.A6.mdlSliceG]
        rfl
    rw [heq] at h
    exact h
  have hfib1 : MeasureTheory.eLpNorm RR 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C₁ * Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm GG 2 MeasureTheory.Measure.count := by
    have h := hfibEst C₀ a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ t j₂ hj₂ hk₂ g hg ht
    simpa only [RR, GG] using h
  -- (2) the sampling step
  have hstep1 := hSamp (Q := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) (R : ℝ) hR1
    (fun (n : ℕ) (θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) (X : ℝ) =>
      Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W n X θ)
    (fun n θ => pfG_hasRealFreqSupport ρ a l₁ l₂ k₁ k₂ W hW0 hWb n θ)
  -- (3) the arithmetic constants
  have hlw₀ : (0 : ℝ) ≤ Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂ :=
    le_trans zero_le_one
      (Work.KMTAreas.A7Hi.one_le_lossWeight_of_nonneg A₀ ρ hA₀ hρ.le l₁ l₂ k₁ k₂)
  have hlw₁ : (0 : ℝ) ≤ Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂ :=
    le_trans zero_le_one
      (Work.KMTAreas.A7Hi.one_le_lossWeight_of_nonneg A₁ ρ hA₁ hρ.le l₁ l₂ k₁ k₂)
  have hlam : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (A₀ + A₁) ρ l₁ l₂ k₁ k₂)
      = ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂)
        * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂) := by
    rw [pfG_lossWeight_add A₀ A₁ ρ l₁ l₂ k₁ k₂, ENNReal.ofReal_mul hlw₀]
  -- the constant is large enough
  have hc₀ : 16 * ENNReal.ofReal Cs * (ENNReal.ofReal C₁) ^ (2 : ℕ) ≤ (c₀ : ENNReal) ^ (2 : ℕ) := by
    have hmax : C₁ ≤ max C₁ 1 := le_max_left _ _
    have h4 : (0 : ℝ) ≤ 16 * Cs * (max C₁ 1) ^ 2 := by positivity
    have hle : 16 * Cs * C₁ ^ 2 ≤ (c₀ : ℝ) ^ 2 := by
      have hs : Real.sqrt (16 * Cs * (max C₁ 1) ^ 2) ≤ (c₀ : ℝ) := by
        show _ ≤ max 1 (Real.sqrt (16 * Cs * (max C₁ 1) ^ 2))
        exact le_max_right _ _
      have hs2 : 16 * Cs * (max C₁ 1) ^ 2 ≤ (c₀ : ℝ) ^ 2 := by
        nlinarith [Real.sq_sqrt h4, Real.sqrt_nonneg (16 * Cs * (max C₁ 1) ^ 2)]
      have hle1 : C₁ ^ 2 ≤ (max C₁ 1) ^ 2 := by
        have hC1 : (0 : ℝ) ≤ C₁ := hC₁pos.le
        nlinarith [hC1, le_max_left C₁ (1 : ℝ), sq_nonneg (1 : ℝ), sq_nonneg C₁,
          sq_nonneg (max C₁ 1)]
      nlinarith [hs2, hle1, hCspos.le, mul_le_mul_of_nonneg_left hle1 hCspos.le]
    calc 16 * ENNReal.ofReal Cs * (ENNReal.ofReal C₁) ^ (2 : ℕ)
        = ENNReal.ofReal (16 * Cs * C₁ ^ 2) := by
          rw [← ENNReal.ofReal_pow hC₁pos.le,
            show (16 : ENNReal) = ENNReal.ofReal 16 from by norm_num,
            ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16),
            ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 16 * Cs)]
      _ ≤ ENNReal.ofReal ((c₀ : ℝ) ^ 2) := ENNReal.ofReal_le_ofReal hle
      _ = (c₀ : ENNReal) ^ (2 : ℕ) := by
          rw [ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (c₀:ℝ)),
            ENNReal.ofReal_coe_nnreal]
  -- (4) the final chain
  have hpow : (∑' m : ℤ, (RR m) ^ (2 : ℕ))
      = (MeasureTheory.eLpNorm RR 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    rw [show (∑' m : ℤ, (RR m) ^ (2 : ℕ)) = ∑' m : ℤ, (RR m) ^ (2 : ℝ) from
      tsum_congr (fun m => (ENNReal.rpow_natCast (RR m) 2).symm)]
    rw [Work.A7Hi.tsum_rpow_eq_eLpNorm_rpow_local (p := 2) (by norm_num) RR,
      show (ENNReal.ofReal 2 : ENNReal) = 2 from by norm_num]
    exact ENNReal.rpow_natCast _ 2
  have htsum : (∑' m : ℤ, ((4 : ENNReal) * RR m) ^ (2 : ℕ))
      = 16 * (MeasureTheory.eLpNorm RR 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    have h2 : ∀ m : ℤ, ((4 : ENNReal) * RR m) ^ (2 : ℕ) = 16 * (RR m) ^ (2 : ℕ) := by
      intro m
      rw [mul_pow, show ((4 : ENNReal) ^ (2 : ℕ)) = 16 from by norm_num]
    rw [show (∑' m : ℤ, ((4 : ENNReal) * RR m) ^ (2 : ℕ))
        = ∑' m : ℤ, 16 * (RR m) ^ (2 : ℕ) from tsum_congr h2, ENNReal.tsum_mul_left, hpow]
  -- the fibre bound, with the `ofReal` of the product split
  have hEr : MeasureTheory.eLpNorm RR 2 MeasureTheory.Measure.count
      ≤ (ENNReal.ofReal C₁
          * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂))
        * MeasureTheory.eLpNorm GG 2 MeasureTheory.Measure.count := by
    rw [← ENNReal.ofReal_mul hC₁pos.le]
    exact hfib1
  have hfinal : ENNReal.ofReal Cs
        * (16 * (MeasureTheory.eLpNorm RR 2 MeasureTheory.Measure.count) ^ (2 : ℕ))
      ≤ ((K₀ Λ : ENNReal) * (c₀ : ENNReal)) ^ (2 : ℕ)
        * (ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (A₀ + A₁) ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ)
        * (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    have step1 : ENNReal.ofReal Cs
          * (16 * (MeasureTheory.eLpNorm RR 2 MeasureTheory.Measure.count) ^ (2 : ℕ))
        ≤ ENNReal.ofReal Cs * (16 * ((ENNReal.ofReal C₁
            * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂))
          * MeasureTheory.eLpNorm GG 2 MeasureTheory.Measure.count) ^ (2 : ℕ)) := by
      refine mul_le_mul' le_rfl ?_
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left' hEr 2) (by norm_num)
    have step2 : ENNReal.ofReal Cs * (16 * ((ENNReal.ofReal C₁
            * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂))
          * MeasureTheory.eLpNorm GG 2 MeasureTheory.Measure.count) ^ (2 : ℕ))
        ≤ ENNReal.ofReal Cs * (16 * ((ENNReal.ofReal C₁
            * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂))
          * ((K₀ Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂)
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)) ^ (2 : ℕ)) := by
      refine mul_le_mul' le_rfl ?_
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      refine pow_le_pow_left' ?_ 2
      exact mul_le_mul_of_nonneg_left hlin1 (by positivity)
    have step3 : ENNReal.ofReal Cs * (16 * ((ENNReal.ofReal C₁
            * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂))
          * ((K₀ Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂)
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)) ^ (2 : ℕ))
        = (ENNReal.ofReal Cs * 16 * (ENNReal.ofReal C₁) ^ (2 : ℕ))
          * ((ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂)
              * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ))
          * ((K₀ Λ : ENNReal) ^ (2 : ℕ))
          * (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
      ring
    have step4 : (ENNReal.ofReal Cs * 16 * (ENNReal.ofReal C₁) ^ (2 : ℕ))
          * ((ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂)
              * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ))
          * ((K₀ Λ : ENNReal) ^ (2 : ℕ))
          * (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2 : ℕ)
        ≤ ((c₀ : ENNReal) ^ (2 : ℕ))
          * ((ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂)
              * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ))
          * ((K₀ Λ : ENNReal) ^ (2 : ℕ))
          * (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right ?_ (by positivity)) (by positivity)) (by positivity)
      calc (ENNReal.ofReal Cs * 16 * (ENNReal.ofReal C₁) ^ (2 : ℕ))
          = 16 * ENNReal.ofReal Cs * (ENNReal.ofReal C₁) ^ (2 : ℕ) := by ring
        _ ≤ (c₀ : ENNReal) ^ (2 : ℕ) := hc₀
    have step5 : ((c₀ : ENNReal) ^ (2 : ℕ))
          * ((ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂)
              * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ))
          * ((K₀ Λ : ENNReal) ^ (2 : ℕ))
          * (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2 : ℕ)
        = ((K₀ Λ : ENNReal) * (c₀ : ENNReal)) ^ (2 : ℕ)
          * (ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (A₀ + A₁) ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ)
          * (MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
      rw [hlam]
      ring
    exact step1.trans (step2.trans ((le_of_eq step3).trans (step4.trans (le_of_eq step5))))
  refine hstep1.trans ?_
  have htsum2 : (∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
        (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
        (fun n : ℕ => Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ W n ((m : ℤ) : ℝ))) ^ (2 : ℕ))
      ≤ 16 * (MeasureTheory.eLpNorm RR 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    rw [← htsum]
    refine ENNReal.tsum_le_tsum (fun m => ?_)
    exact pow_le_pow_left'
      (pfG_integer_le ρ hρ hρ1 P hd C₀ a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ t g j₂ hj₂ hk₂ hg ht W
        hWb hWs hW0 R hR m) 2
  exact (mul_le_mul' le_rfl htsum2).trans hfinal

end Work.A6Clean
