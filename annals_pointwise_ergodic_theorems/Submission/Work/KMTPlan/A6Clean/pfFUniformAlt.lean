import Mathlib
import Submission.Work.KMTPlan.A6Clean.mdlSliceF_fiberVarSampling
import Submission.Work.A6Clean.VrLiftClip
import Submission.Work.KMTPlan.A6Clean.charSumResidueTwo
import Submission.Work.A6Clean.VrLiftSamplingLattice
import Submission.Work.KMTPlan.A6.TleMemLp
import Submission.Work.KMTAreas.A7Rep.fiberResidueMaxRephaseL2
import Submission.Work.KMTAreas.A7.FibrePlumbing
import Submission.Work.A7Hi.varEstTle_compositeCompare
import Submission.Work.KMTPlan.A6.ZModVariationalChainProb
import Submission.Work.KMTPlan.A6Clean.MdlPacketsStructuralND
import Submission.Work.KMTPlan.A6Clean.packetFamF_minorArc

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.A6Clean

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section

/-! ## Helper lemmas

These are the interface facts the assembly of `PacketFamFUniform` needs: the identification of the
packet slice with a character sum over the *exact*-height amplitudes, its real-frequency support
(which feeds the vector-valued lattice sampling `VrLiftSamplingLattice`), the monotonicity of the
`goodScale` gate along a lacunary scale sequence, the `ℓ²`-membership and the `ℓ¹`-convolution
summability of the model slice `mdlSliceF`, and the identification of the arithmetic fibre
`fiberOp` with the chararacter sum of the lift's amplitudes. -/

/-- The packet slice is the character sum of the **exact**-height amplitudes: the sum in
`Work.KMTPlan.A6Clean.packetFamF` runs over `iwArithFreqs ρ l₁`, but the lift vanishes off
`iwArithFreqsNew ρ l₁ = iwArithFreqs ρ l₁ \ iwArithFreqs ρ (l₁ - 1)`. -/
lemma pfF_charSum (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (W : ℕ → Circ → ℝ → ℂ)
    (hW0 : ∀ (n : ℕ) (α : Circ),
      α ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ → W n α = 0)
    (n : ℕ) (X : ℝ) (θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) :
    Work.KMTPlan.A6Clean.packetFamF ρ a l₁ l₂ k₁ k₂ W n X θ
      = if Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
            (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
          ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
            fourier (T := 1) (-(θ.val : ℤ)) α * W n α X
        else 0 := by
  rw [Work.KMTPlan.A6Clean.packetFamF_apply]
  by_cases hg : Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
      (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a n))
  · simp only [hg, if_true]
    exact (Finset.sum_subset
      (fun x hx => Work.KMTAreas.A7.mem_iwArithFreqsNew_le hx)
      (fun x _ hx' => by rw [hW0 n x hx']; simp)).symm
  · simp only [hg, if_false]

/-- **The packet slices have real frequency support in `Icc (-1/4) (1/4)`**, because they are
finite character combinations of the lifts, each of which has that support. -/
lemma pfF_hasRealFreqSupport (ρ : ℝ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (W : ℕ → Circ → ℝ → ℂ)
    (hW0 : ∀ (n : ℕ) (α : Circ),
      α ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ → W n α = 0)
    (hWb : ∀ (n : ℕ) (α : Circ),
      Work.KMTAreas.A7Rep.HasRealFreqSupport (W n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4)))
    (n : ℕ) (θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) :
    Work.KMTAreas.A7Rep.HasRealFreqSupport (fun X : ℝ => Work.KMTPlan.A6Clean.packetFamF ρ a l₁ l₂ k₁ k₂ W n X θ)
      (Set.Icc (-(1 / 4 : ℝ)) (1 / 4)) := by
  by_cases hg : Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
      (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a n))
  · have hfun : (fun X : ℝ => Work.KMTPlan.A6Clean.packetFamF ρ a l₁ l₂ k₁ k₂ W n X θ)
        = fun X : ℝ => ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
            fourier (T := 1) (-(θ.val : ℤ)) α * W n α X := by
      funext X
      rw [pfF_charSum ρ a l₁ l₂ k₁ k₂ W hW0 n X θ, if_pos hg]
    rw [hfun]
    exact Work.KMTAreas.A7Rep.hasRealFreqSupport_finset_sum _
      (fun α _ => Work.KMTAreas.A7Rep.hasRealFreqSupport_const_mul _ (hWb n α))
  · have hfun : (fun X : ℝ => Work.KMTPlan.A6Clean.packetFamF ρ a l₁ l₂ k₁ k₂ W n X θ) = fun _ : ℝ => (0 : ℂ) := by
      funext X
      rw [pfF_charSum ρ a l₁ l₂ k₁ k₂ W hW0 n X θ, if_neg hg]
    rw [hfun]
    exact Work.KMTPlan.A6Clean.hasRealFreqSupport_zero _

/-- **The gate `goodScale Q L ⌊a n⌋` is monotone in `n`** along a lacunary scale sequence. -/
lemma pfF_goodScale_mono {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
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
      _ ≤ (Λ : NNReal) * a k := mul_le_mul_of_nonneg_right (le_of_lt hΛ) (show (0:NNReal) ≤ a k from bot_le)
      _ ≤ a (k + 1) := le_of_lt hmul
  have hfl : Nat.floor (a n) ≤ Nat.floor (a m) := Nat.floor_mono (hmono hnm)
  exact le_trans h hfl

/-- The exact-height arithmetic frequencies of the `f`-side are killed by `arithQ ρ (max l₁ l₂)`. -/
lemma pfF_arithQ_nsmul (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l₁ l₂ : ℕ)
    {α : Circ} (hα : α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁) :
    (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℕ) • α = 0 :=
  Work.KMTAreas.A7.arithQ_nsmul_eq_zero
    (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 (le_max_left l₁ l₂)
      (Work.KMTAreas.A7.mem_iwArithFreqsNew_le hα))

/-- **`mdlSliceF` is square summable** whenever `f` is: off the core it vanishes, and on the core it
is the Ionescu–Wainger multiplier `Tle` of a bounded symbol applied to the square summable
`mdlF`. -/
lemma pfF_memℓp_mdlSliceF (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (j₁ : ℤ) (t : ℝ)
    (f : ℤ → ℂ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hk₁ : k₁ = 0 → j₁ ≠ -1)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) (n : ℕ) :
    Memℓp (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) 2 := by
  by_cases hc : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · have hN : 1 ≤ Nat.floor (a n) := by
      have hlt : Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) < Nat.floor (a n) :=
        ((Work.KMTPlan.A6.mdlCore_iff ρ C₀ a l₁ l₂ k₁ k₂ n).mp hc).2.1
      have h1 : 1 ≤ Work.KMTAreas.A7.splitCut ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) := by
        rw [Work.KMTAreas.A7.splitCut]; exact Nat.one_le_two_pow
      omega
    obtain ⟨M, hM0, hMbd, -, -⟩ :=
      Work.KMTPlan.A6.varphiNtjPeriodize_aux (Nat.floor (a n)) k₁ j₁ t hj₁ hk₁ hN
    have hslice : Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n
        = Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t)
            (Work.KMTPlan.A6.mdlF ρ
              (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₁ f) := by
      simp only [Work.KMTPlan.A6.mdlSliceF, hc, if_true, Work.KMTPlan.A6.lcL]
    rw [hslice]
    exact Work.KMTPlan.A6.TleMemLp ρ l₁
      (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t) M hM0 hMbd _
      (Work.KMTPlan.A6.memlpOfMemLpCount (by norm_num) (by norm_num)
        (Work.KMTPlan.A6.memLp_mdlF ρ
          (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) l₁ hf))
  · have h0 : Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n = 0 := by
      simp only [Work.KMTPlan.A6.mdlSliceF, hc, if_false]
    rw [h0]
    rw [Memℓp]
    simp

/-- **The convolution defining the fibre is absolutely summable**: the kernel `cw (mStarF U)` is
`ℓ¹` and the input is `ℓ²`. -/
lemma pfF_summable_cw (U : ℕ) (h : ℤ → ℂ) (hh : Memℓp h 2) (x : ℤ) :
    Summable (fun j : ℤ => Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF U) j * h (x - j)) :=
  Work.KMTAreas.A7.summable_cw_mul_of_memℓp (Work.KMTAreas.A7.summable_norm_cw_mStarF U) hh x

/-- **The arithmetic fibre is the character sum of the lift's amplitudes**: at an integer point
`m` and residue `n₀`,
`fiberOp ρ l₁ m⋆ n₀ (h n) m = ∑_{α ∈ (ℚ/ℤ)_{l₁}} e((n₀-m)α)·W n α m`. -/
lemma pfF_fiberOp_eq (ρ : ℝ) (l₁ : ℕ) (mm : ℝ → ℂ) (h : ℕ → ℤ → ℂ) (W : ℕ → Circ → ℝ → ℂ)
    (hWs : ∀ (n : ℕ) (α : Circ), α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ →
      ∀ x : ℤ, W n α (x : ℝ) = Work.KMTAreas.A7.winConvR mm
        (Work.KMTAreas.A7.winModR (-α) (h n)) x)
    (hsumm : ∀ (n : ℕ) (x : ℤ), Summable (fun j : ℤ => Work.KMTAreas.A7.cw mm j * h n (x - j)))
    (n : ℕ) (n₀ m : ℤ) :
    Work.KMTAreas.A7.fiberOp ρ l₁ mm n₀ (h n) m
      = ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
          fourier (T := 1) (n₀ - m) α * W n α (m : ℝ) := by
  rw [Work.KMTAreas.A7.fiberOp_eq_phaseRotation_windowCut ρ l₁ mm n₀ (h n) m (hsumm n m)]
  refine Finset.sum_congr rfl (fun α hα => ?_)
  have hwin : Work.KMTAreas.A7.winModR α
        (Work.KMTAreas.A7.winConvR mm (Work.KMTAreas.A7.winModR (-α) (h n))) m
      = fourier (T := 1) (-m) α * W n α (m : ℝ) := by
    rw [Work.KMTAreas.A7.winModR, hWs n α hα m]
  rw [hwin, Work.KMTPlan.A6Clean.fourier_sub_eq_mulR]
  ring

/-- **The `HasRealFreqSupport` form of the vector-valued lattice sampling**, obtained from
`Work.A6Clean.VrLiftSamplingLattice` by unpacking the amplitude witnesses. -/
lemma pfF_sampling_HRF :
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
    refine lintegral_congr_ae (Filter.Eventually.of_forall (fun X => ?_))
    beta_reduce
    rw [show (fun n θ => B n θ X)
        = fun n θ => FourierTransformInv.fourierInv (g n θ) X from by
      funext n θ
      exact hgpt n θ X]
  have h2 : (∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP R Q
          (fun n θ => B n θ ((m : ℤ) : ℝ))) ^ (2 : ℕ))
      = ∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP R Q
          (fun n θ => FourierTransformInv.fourierInv (g n θ) ((m : ℤ) : ℝ))) ^ (2 : ℕ) := by
    apply tsum_congr
    intro m
    rw [show (fun n θ => B n θ ((m : ℤ) : ℝ))
        = fun n θ => FourierTransformInv.fourierInv (g n θ) ((m : ℤ) : ℝ) from by
      funext n θ
      exact hgpt n θ ((m : ℤ) : ℝ)]
  rw [h1, h2]
  exact hmain

/-- `4 * ofReal a * (ofReal b)^2 = ofReal (4 * a * b^2)` for `a, b ≥ 0`. -/
lemma pfF_ofReal_four_mul_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (4 : ENNReal) * ENNReal.ofReal a * (ENNReal.ofReal b) ^ (2 : ℕ)
      = ENNReal.ofReal (4 * a * b ^ 2) := by
  have h4 : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := by norm_num
  rw [h4, ← ENNReal.ofReal_pow hb, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * a)]

/-- `16 * ofReal a * (ofReal b)^2 = ofReal (16 * a * b^2)` for `a, b ≥ 0`. -/
lemma pfF_ofReal_sixteen_mul_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (16 : ENNReal) * ENNReal.ofReal a * (ENNReal.ofReal b) ^ (2 : ℕ)
      = ENNReal.ofReal (16 * a * b ^ 2) := by
  have h16 : (16 : ENNReal) = ENNReal.ofReal (16 : ℝ) := by norm_num
  rw [h16, ← ENNReal.ofReal_pow hb, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 16 * a)]

/-- The loss weight is multiplicative in its first (exponent) argument. -/
lemma pfF_lossWeight_add (c d ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
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
the arithmetic fibres of the model slice.  The proof is: (i) the matrix of the gate `goodScale` is a
monotone upper set in the scale `n`, so clipping the family at the gate at most doubles the datum
(`VrLiftClip`); (ii) the exact-height character sums of the amplitudes and their `ZMod Q`-fibre
counterparts have the same `ℓ²`-mass (Parseval, `CharSumResidue`); (iii) at integers the fibre *is*
the character sum of the lift's amplitudes (`pfF_fiberOp_eq`). -/
lemma pfF_integer_le (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal)
    (hΛ : 1 < Λ) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ))
    (hk₁ : k₁ = 0 → j₁ ≠ -1) (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (W : ℕ → Circ → ℝ → ℂ)
    (hWb : ∀ (n : ℕ) (α : Circ),
      Work.KMTAreas.A7Rep.HasRealFreqSupport (W n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4)))
    (hWs : ∀ (n : ℕ) (α : Circ), α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ →
      ∀ x : ℤ, W n α (x : ℝ) = Work.KMTAreas.A7.winConvR
        (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
        (Work.KMTAreas.A7.winModR (-α)
          (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)) x)
    (hW0 : ∀ (n : ℕ) (α : Circ),
      α ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ → W n α = 0)
    (R : NNReal) (hR : 2 ≤ R) (y : ℤ) :
    Work.KMTPlan.A6.VrLiftDataP (R : ℝ) (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
        (fun n : ℕ => Work.KMTPlan.A6Clean.packetFamF ρ a l₁ l₂ k₁ k₂ W n (y : ℝ))
      ≤ (4 : ENNReal) * Work.KMTAreas.A7.residueLp 2 (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
          (fun y' n₀ => PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
            Work.KMTAreas.A7.fiberOp ρ l₁
              (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
              (n₀ : ℤ) (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) y')) y := by
  classical
  haveI : NeZero (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) :=
    ⟨Nat.pos_iff_ne_zero.mp (Work.KMTAreas.A7.arithQ_pos ρ (max l₁ l₂))⟩
  -- summability of the fibre's defining convolution
  have hsumm : ∀ (n : ℕ) (x : ℤ), Summable (fun j : ℤ =>
      Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF
          (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) j *
        Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n (x - j)) :=
    fun n x => pfF_summable_cw _ _
      (pfF_memℓp_mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f hj₁ hk₁ hf n) x
  -- the fibre identity
  have hfib : ∀ (n : ℕ) (n₀ z : ℤ), Work.KMTAreas.A7.fiberOp ρ l₁
      (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂))) n₀
      (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) z
      = ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
          fourier (T := 1) (n₀ - z) α * W n α (z : ℝ) :=
    fun n n₀ z => pfF_fiberOp_eq ρ l₁ _ _ W hWs hsumm n n₀ z
  -- the gate is a monotone upper set
  have hγmono : ∀ ⦃n m : ℕ⦄, n ≤ m →
      Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
          (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) →
      Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
          (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a m)) :=
    fun n m hnm hn => pfF_goodScale_mono hΛ ha ha1 _ _ hnm hn
  -- the packet family at the integer `y` is the gated exact-height character sum
  have hpack : (fun (n : ℕ) => Work.KMTPlan.A6Clean.packetFamF ρ a l₁ l₂ k₁ k₂ W n (y : ℝ))
      = fun (n : ℕ) (θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) =>
          if Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)) then
            ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
              fourier (T := 1) (-(θ.val : ℤ)) α * W n α (y : ℝ)
          else 0 := by
    funext n θ
    exact pfF_charSum ρ a l₁ l₂ k₁ k₂ W hW0 n (y : ℝ) θ
  rw [hpack]
  -- clip at the gate
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by
    have h2 : (2 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    linarith
  have hclip := Work.A6Clean.VrLiftClip (Q := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) (R : ℝ) hR1
    (fun n : ℕ => Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
      (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a n)))
    hγmono
    (fun (n : ℕ) (θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) =>
      ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
        fourier (T := 1) (-(θ.val : ℤ)) α * W n α (y : ℝ))
  refine hclip.trans ?_
  -- Parseval for the exact-height character sums
  have hcs := Work.KMTPlan.A6Clean.charSumResidueTwo (Q := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) R hR
    (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁) (fun α hα => pfF_arithQ_nsmul ρ hρ hρ1 l₁ l₂ hα)
    (fun α => fourier (T := 1) (-y) α)
    (fun α => Work.KMTAreas.A7.norm_fourier_applyR (-y) α)
    (fun (n : ℕ) (α : Circ) => W n α (y : ℝ))
  refine (add_le_add hcs hcs).trans ?_
  -- identify the `ZMod Q`-fibre with the arithmetic fibre
  have hid : (fun (_ : ℤ) (n₀ : ℕ) => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁,
          fourier (T := 1) (n₀ : ℤ) α * (fourier (T := 1) (-y) α * W n α (y : ℝ))))
      = fun (_ : ℤ) (n₀ : ℕ) => PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
          Work.KMTAreas.A7.fiberOp ρ l₁
            (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
            (n₀ : ℤ) (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) y) := by
    funext zz n₀
    congr 1
    funext n
    rw [hfib n (n₀ : ℤ) y]
    refine Finset.sum_congr rfl (fun α hα => ?_)
    rw [Work.KMTPlan.A6Clean.fourier_sub_eq_mulR]
    ring
  rw [hid]
  simp only [Work.KMTAreas.A7.residueLp]
  exact le_of_eq (by ring)

/- **The uniform `(lin-1)` clause of the §8 adelic form** (this is
`Work.KMTPlan.A6Clean.packetFamF_linUniform` of `VrSamplingVecUniform.lean` under a new name, so
that the producer of `AdelicFormPropRangeP` can use a *proved* copy; the old file may be
superseded).

This is the shape `AdelicClausesAt` consumes: `A`, `ρ₀`, `K` are chosen *before* the datum
`(a, Λ, l₁, l₂, k₁, k₂, t, f, W)` (so this is strictly stronger than
`Work.KMTPlan.A6Clean.vrLiftDataP_packetFamF_nd`, whose `A, Cin, Ku` come after the datum, and
which is therefore only a finiteness statement).

Route (see `NOTES_A6_VrSamplingVecUniform_SESSION.md` §2, workspace root):

1. write `B n θ := Σ_{α ∈ iwArithFreqsNew ρ l₁} e (-(θ.val : ℤ)) α • A_{n,α}` where `A_{n,α}` is the
   amplitude of the lift `W n α` (`HasRealFreqSupport`); then `Work.KMTPlan.A6Clean.packetFamF ⋯ n X θ = 𝓕⁻(B n θ) X`
   (the gate `goodScale` multiplies by `0/1`, so handle it by cases);
2. apply the vector-valued lattice sampling
   `Work.KMTPlan.A6Clean.VrLiftSamplingLattice` (`A6Clean/VrLiftSamplingLattice.lean`), whose
   triangle-inequality input is `Work.KMTPlan.A6Clean.VrLiftTriangle`
   (`A6Clean/VrLiftTriangle.lean`); *if either has not landed yet, prove the equivalent statement
   in-file* — only the *samples* at integers survive;
3. at integers, replace the `α`-sum by the *fibre*
   `fiberOp ρ l₁ (mStarF U) n₀ (mdlSliceF ⋯ n) ·` (the PROVED
   `Work.KMTPlan.A6Clean.fiberOpSet_eq_windowPieceR` with `A = iwArithFreqsNew ρ l₁`, using `hWs`
   and `hW0`; note `W n α = 0` off the exact-height set), and use orthogonality of the `Q`-torsion
   characters (`Work.KMTPlan.A6Clean.lintegral_charSum_eq`, PROVED) to get
   `VrLiftDataP R Q (Work.KMTPlan.A6Clean.packetFamF ⋯ · x) ≤ residueLp 2 Q (fun x n₀ => variationalNorm R (fun n => fiberOp ⋯ n₀ x)) x`
   (the `Q ^ (-1/2)` of the DFT-Parseval identity cancels the `Q` of the fibre Parseval identity:
   **no factor of `Q`**);
4. square-sum in `x` and apply the PROVED `Work.KMTPlan.A6Clean.mdlSliceF_fiberVarSampling R hR`
   (at `p := 2`; it gives `A = 0`, `C₁ = C₁(ρ)`, uniform in the datum) and the PROVED
   `Work.KMTPlan.A6.MdlSlicePktLinF C₀ hC₀ R hR j₁ hj₁` (giving `A₀, ρ₀, K` independent of the
   datum), to conclude
   `∫⁻ X (VrLiftDataP ⋯)^2 ≤ (K Λ)^2 * ofReal (lossWeight A ρ l₁ l₂ k₁ k₂)^2 * (eLpNorm f 2)^2`.

`hW0` excludes the *nonexact* heights (where the window piece already vanishes by the PROVED
`Work.KMTPlan.A6Clean.winConvR_eq_zero_of_not_exact`; the producer will supply it from
`mdlWindowLiftF`).-/
theorem PacketFamFUniformAlt (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R)
    (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ)
          (W : ℕ → Work.Analysis.IonescuWainger.Circle → ℝ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
          MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
          t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ ≠ -1) →
          (∀ (n : ℕ) (α : Work.Analysis.IonescuWainger.Circle),
            Work.KMTAreas.A7Rep.HasRealFreqSupport (W n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4))) →
          (∀ (n : ℕ) (α : Work.Analysis.IonescuWainger.Circle),
            α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ → ∀ x : ℤ,
            W n α (x : ℝ) = Work.KMTAreas.A7.winConvR
              (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
              (Work.KMTAreas.A7.winModR (-α)
                (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n)) x) →
          (∀ (n : ℕ) (α : Work.Analysis.IonescuWainger.Circle),
            α ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ → W n α = 0) →
          ∫⁻ X : ℝ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
              (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
              (fun n : ℕ => Work.KMTPlan.A6Clean.packetFamF ρ a l₁ l₂ k₁ k₂ W n X)) ^ (2 : ℕ)
            ≤ (K Λ : ENNReal) ^ (2 : ℕ)
              * (ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ)
              * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
  classical
  -- (0) the two proved inputs
  obtain ⟨A₀, hA₀, ρ₀L, hρ₀L, hLin⟩ := Work.KMTPlan.A6.MdlSlicePktLinF C₀ hC₀ R hR j₁ hj₁
  obtain ⟨A₁, hA₁, ρ₀V, hρ₀V, hFib⟩ := Work.KMTPlan.A6Clean.mdlSliceF_fiberVarSampling R hR
  obtain ⟨Cs, hCspos, hSamp⟩ := pfF_sampling_HRF
  have hR1' : (1 : NNReal) ≤ R := le_of_lt (lt_of_le_of_lt (by norm_num) hR)
  have hR2' : (2 : NNReal) ≤ R := le_of_lt hR
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1'
  refine ⟨A₀ + A₁, by linarith, min 1 (min ρ₀L ρ₀V), lt_min one_pos (lt_min hρ₀L hρ₀V), ?_⟩
  intro ρ hρ hρ₀
  have hρ1 : ρ ≤ 1 := le_trans hρ₀ (min_le_left _ _)
  have hρL : ρ ≤ ρ₀L := le_trans hρ₀ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρV : ρ ≤ ρ₀V := le_trans hρ₀ (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨K₀, hK₀⟩ := hLin ρ hρ hρL
  obtain ⟨C₁, hC₁pos, hfibEst⟩ := hFib 2 (by norm_num) (by norm_num) ρ hρ hρV
  let c₀ : NNReal := ⟨Nat.ceil (16 * Cs * (max C₁ 1) ^ 2) + 1, by positivity⟩
  refine ⟨fun Λ => K₀ Λ * c₀, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f W hΛ ha ha1 hf ht hk₁ hWb hWs hW0
  haveI : NeZero (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) :=
    ⟨Nat.pos_iff_ne_zero.mp (Work.KMTAreas.A7.arithQ_pos ρ (max l₁ l₂))⟩
  -- (1) the model slice family and its two norms
  let GG : ℤ → ENNReal := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
    (fun n : ℕ => Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n x)
  let RR : ℤ → ENNReal := fun x : ℤ => Work.KMTAreas.A7.residueLp 2
    (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
    (fun y' n₀ => PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
      Work.KMTAreas.A7.fiberOp ρ l₁
        (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)))
        n₀ (Work.KMTPlan.A6.mdlSliceF ρ C₀ a l₁ l₂ k₁ k₂ j₁ t f n) y')) x
  have hlin1 : MeasureTheory.eLpNorm GG 2 MeasureTheory.Measure.count
      ≤ (K₀ Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    have h := hK₀ a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 ht hk₁
    have heq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
          if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
            Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t)
              (Work.KMTPlan.A6.mdlF ρ
                (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max k₁ k₂))) l₁ f) x
          else 0)) = GG := by
      funext x
      congr 1
      funext n
      simp only [GG, Work.KMTPlan.A6.mdlSliceF, Work.KMTPlan.A6.lcL, ite_apply, Pi.zero_apply]
    rw [heq] at h
    exact h
  have hfib1 : MeasureTheory.eLpNorm RR 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C₁ * Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂)
        * MeasureTheory.eLpNorm GG 2 MeasureTheory.Measure.count := by
    have h := hfibEst C₀ a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ t j₁ hj₁ hk₁ f hf ht
    simpa only [ENNReal.toReal_ofNat, RR, GG] using h
  -- (2) the sampling step
  have hstep1 := hSamp (Q := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) (R : ℝ) hR1
    (fun (n : ℕ) (θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))) (X : ℝ) =>
      Work.KMTPlan.A6Clean.packetFamF ρ a l₁ l₂ k₁ k₂ W n X θ)
    (fun n θ => pfF_hasRealFreqSupport ρ a l₁ l₂ k₁ k₂ W hW0 hWb n θ)
  -- (3) the arithmetic constants
  have hA₀nn : (0 : ℝ) ≤ A₀ := hA₀
  have hA₁nn : (0 : ℝ) ≤ A₁ := hA₁
  have hlw₀ : (0 : ℝ) ≤ Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂ :=
    le_trans zero_le_one (Work.KMTAreas.A7Hi.one_le_lossWeight_of_nonneg A₀ ρ hA₀ hρ.le l₁ l₂ k₁ k₂)
  have hlw₁ : (0 : ℝ) ≤ Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂ :=
    le_trans zero_le_one (Work.KMTAreas.A7Hi.one_le_lossWeight_of_nonneg A₁ ρ hA₁ hρ.le l₁ l₂ k₁ k₂)
  have hlam : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (A₀ + A₁) ρ l₁ l₂ k₁ k₂)
      = ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂)
        * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂) := by
    rw [pfF_lossWeight_add A₀ A₁ ρ l₁ l₂ k₁ k₂, ENNReal.ofReal_mul hlw₀]
  -- the constant is large enough
  have hc₀ : 16 * ENNReal.ofReal Cs * (ENNReal.ofReal C₁) ^ (2 : ℕ) ≤ (c₀ : ENNReal) ^ (2 : ℕ) := by
    have hC₁le : C₁ ^ 2 ≤ (max C₁ 1) ^ 2 := by
      have h1 : C₁ ≤ max C₁ 1 := le_max_left _ _
      have h2 : (0 : ℝ) ≤ max C₁ 1 := le_trans hC₁pos.le h1
      nlinarith
    have h4 : 16 * Cs * C₁ ^ 2 ≤ 16 * Cs * (max C₁ 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hC₁le (by positivity : (0:ℝ) ≤ 16 * Cs)
    have hceil : 16 * Cs * (max C₁ 1) ^ 2 ≤ (c₀ : ℝ) := by
      show 16 * Cs * (max C₁ 1) ^ 2
        ≤ (((⟨Nat.ceil (16 * Cs * (max C₁ 1) ^ 2) + 1, by positivity⟩ : NNReal) : ℝ))
      have h := Nat.le_ceil (16 * Cs * (max C₁ 1) ^ 2)
      push_cast
      linarith
    have hge1 : (1 : ℝ) ≤ (c₀ : ℝ) := by
      show (1 : ℝ) ≤ (((⟨Nat.ceil (16 * Cs * (max C₁ 1) ^ 2) + 1, by positivity⟩ : NNReal) : ℝ))
      push_cast
      have : (0 : ℝ) ≤ (Nat.ceil (16 * Cs * (max C₁ 1) ^ 2) : ℝ) := by positivity
      linarith
    have hle : 16 * Cs * C₁ ^ 2 ≤ (c₀ : ℝ) ^ 2 := by nlinarith [h4, hceil, hge1]
    rw [pfF_ofReal_sixteen_mul_sq hCspos.le hC₁pos.le,
      show (c₀ : ENNReal) ^ (2 : ℕ) = ENNReal.ofReal ((c₀ : ℝ) ^ 2) from by
        rw [← ENNReal.ofReal_coe_nnreal (p := c₀),
          ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ (c₀ : ℝ))]]
    exact ENNReal.ofReal_le_ofReal hle
  -- (4) the final chain
  have htsum : (∑' m : ℤ, ((4 : ENNReal) * RR m) ^ (2 : ℕ))
      = 16 * (MeasureTheory.eLpNorm RR 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    have h3 : ∀ m : ℤ, (RR m) ^ (2 : ℕ) = (RR m) ^ (2 : ℝ) := by
      intro m
      rw [← ENNReal.rpow_natCast]
      norm_num
    have h2 : ∀ m : ℤ, ((4 : ENNReal) * RR m) ^ (2 : ℕ) = 16 * (RR m) ^ (2 : ℝ) := by
      intro m
      rw [mul_pow, h3 m]
      norm_num
    rw [show (∑' m : ℤ, ((4 : ENNReal) * RR m) ^ (2 : ℕ))
        = ∑' m : ℤ, 16 * (RR m) ^ (2 : ℝ) from tsum_congr h2]
    rw [ENNReal.tsum_mul_left]
    rw [Work.A7Hi.tsum_rpow_eq_eLpNorm_rpow_local (p := 2) (by norm_num) RR]
    rw [show (ENNReal.ofReal 2 : ENNReal) = 2 from by norm_num]
    congr 1
    rw [← ENNReal.rpow_natCast]
    norm_num
  have hfinal : ENNReal.ofReal Cs * (16 * (MeasureTheory.eLpNorm RR 2 MeasureTheory.Measure.count) ^ (2 : ℕ))
      ≤ ((K₀ Λ : ENNReal) * (c₀ : ENNReal)) ^ (2 : ℕ)
        * (ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (A₀ + A₁) ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ)
        * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    have hfib1' : MeasureTheory.eLpNorm RR 2 MeasureTheory.Measure.count
        ≤ (ENNReal.ofReal C₁
            * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂))
          * MeasureTheory.eLpNorm GG 2 MeasureTheory.Measure.count := by
      rw [← ENNReal.ofReal_mul hC₁pos.le]
      exact hfib1
    have hE : (MeasureTheory.eLpNorm RR 2 MeasureTheory.Measure.count) ^ (2 : ℕ)
        ≤ ((ENNReal.ofReal C₁
              * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂))
            * MeasureTheory.eLpNorm GG 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
      gcongr
    have hG : (MeasureTheory.eLpNorm GG 2 MeasureTheory.Measure.count) ^ (2 : ℕ)
        ≤ ((K₀ Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂)
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
      gcongr
    have hconst : ENNReal.ofReal Cs * 16 * (ENNReal.ofReal C₁) ^ (2 : ℕ)
        ≤ (c₀ : ENNReal) ^ (2 : ℕ) := by
      rw [mul_comm (ENNReal.ofReal Cs) (16 : ENNReal)]
      exact hc₀
    calc ENNReal.ofReal Cs * (16 * (MeasureTheory.eLpNorm RR 2 MeasureTheory.Measure.count) ^ (2 : ℕ))
        ≤ ENNReal.ofReal Cs * (16 * ((ENNReal.ofReal C₁
              * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂))
            * MeasureTheory.eLpNorm GG 2 MeasureTheory.Measure.count) ^ (2 : ℕ)) := by
          refine mul_le_mul_of_nonneg_left ?_ bot_le
          exact mul_le_mul_of_nonneg_left hE bot_le
      _ = (ENNReal.ofReal Cs * 16
              * (ENNReal.ofReal C₁
                * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ))
            * (MeasureTheory.eLpNorm GG 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
          ring
      _ ≤ (ENNReal.ofReal Cs * 16
              * (ENNReal.ofReal C₁
                * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ))
            * (((K₀ Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ)) := by
          refine mul_le_mul_of_nonneg_left hG bot_le
      _ = (ENNReal.ofReal Cs * 16 * (ENNReal.ofReal C₁) ^ (2 : ℕ))
            * ((ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂)
                * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ)
              * (K₀ Λ : ENNReal) ^ (2 : ℕ)
              * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ)) := by
          ring
      _ ≤ ((c₀ : ENNReal) ^ (2 : ℕ))
            * ((ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ l₁ l₂ k₁ k₂)
                * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₁ ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ)
              * (K₀ Λ : ENNReal) ^ (2 : ℕ)
              * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ)) := by
          refine mul_le_mul_of_nonneg_right hconst bot_le
      _ = ((K₀ Λ : ENNReal) * (c₀ : ENNReal)) ^ (2 : ℕ)
            * (ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (A₀ + A₁) ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ)
            * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
          rw [hlam]
          ring
  refine hstep1.trans ?_
  calc ENNReal.ofReal Cs * ∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
          (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
          (fun n : ℕ => Work.KMTPlan.A6Clean.packetFamF ρ a l₁ l₂ k₁ k₂ W n ((m : ℤ) : ℝ))) ^ (2 : ℕ)
      ≤ ENNReal.ofReal Cs * ∑' m : ℤ, ((4 : ENNReal) * RR m) ^ (2 : ℕ) := by
        refine mul_le_mul' le_rfl ?_
        refine ENNReal.tsum_le_tsum (fun m => ?_)
        exact pow_le_pow_left₀ (n := 2) (show (0 : ENNReal) ≤ _ from bot_le)
          (pfF_integer_le ρ hρ hρ1 C₀ a Λ hΛ ha ha1 l₁ l₂ k₁ k₂ t f j₁ hj₁ hk₁ hf W hWb hWs hW0 R
            hR2' m)
    _ = ENNReal.ofReal Cs
          * (16 * (MeasureTheory.eLpNorm RR 2 MeasureTheory.Measure.count) ^ (2 : ℕ)) := by
        rw [htsum]
    _ ≤ ((fun Λ => K₀ Λ * c₀) Λ : ENNReal) ^ (2 : ℕ)
          * (ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (A₀ + A₁) ρ l₁ l₂ k₁ k₂)) ^ (2 : ℕ)
          * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
        simpa only [ENNReal.coe_mul] using hfinal

end Work.A6Clean
