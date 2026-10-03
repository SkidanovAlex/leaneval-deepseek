/-
# Auxiliary lemmas for the mixed `g`-side (lin-2) estimate (Area A7, KMT §8)

The vocabulary (`GmixedKer`, `GmixedFam`, `GmixedTuple`, `GmixedVar`, `GmixedFib`, `GmixedRes`), the
loss-weight arithmetic, the pointwise Hölder inequality for the residue average, the linear
`form-1` identity of the mixed range, the pointwise variational bound by the residue average and
the boundedness/summability facts for the `g`-side IW projections.

See `Work.KMTAreas.A7.MixedGSideHolds` for the assembly of the target from the two analytic
inputs `LinVarGuard` and `FiberGuard`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoMixedBase
import Submission.Work.KMTAreas.A7.residueSum_mul_le
import Submission.Work.KMTAreas.A7.summable_fiberSet_family
import Submission.Work.KMTPlan.A6.MdlKerVarphitildeNt

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## §1.  Vocabulary -/

/-- The repaired fibre bump of the mixed range: `mStargF d (loMixedU ρ d l₂ k₁ k₂)`. -/
noncomputable def GmixedKer (ρ : ℝ) (P : Polynomial ℤ) (l₂ k₁ k₂ : ℕ) : ℝ → ℂ :=
  mStargF P.natDegree (loMixedU ρ P.natDegree l₂ k₁ k₂)

/-- The guarded `g`-side family of the mixed range: the IW projection of the modulated `g`-bump
at the scale `⌊a n⌋`, clipped to the guard `loGuard ρ C₀ a 0 l₂ k₁ k₂`. -/
noncomputable def GmixedFam (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun n => if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
    Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g else 0

/-- The convolution of `GmixedFam` with the arithmetic kernel `loMixedGKer`, clipped to the
guard (this is the family of the target `MixedGSideEstimate`). -/
noncomputable def GmixedTuple (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun n x => if loGuard ρ C₀ a 0 l₂ k₁ k₂ n then
    convOp (loMixedGKer ρ P l₂ (GmixedKer ρ P l₂ k₁ k₂))
      (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x else 0

/-- The variational norm of the target family. -/
noncomputable def GmixedVarTuple (r : NNReal) (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ)
    (a : ℕ → NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) : ℤ → ENNReal :=
  fun x => variationalNorm r (fun n : ℕ => GmixedTuple ρ P C₀ a l₂ k₁ k₂ t g n x)

/-- The variational norm of the guarded `g`-side family. -/
noncomputable def GmixedVar (r : NNReal) (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ)
    (a : ℕ → NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) : ℤ → ENNReal :=
  fun x => variationalNorm r (fun n : ℕ => GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n x)

/-- The variational norms of the fibres of `GmixedFam`. -/
noncomputable def GmixedFib (r : NNReal) (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ)
    (a : ℕ → NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) : ℤ → ℕ → ENNReal :=
  fun y n₀ => variationalNorm r (fun n : ℕ => fiberOpP ρ P l₂ (GmixedKer ρ P l₂ k₁ k₂) n₀
    (GmixedFam ρ P C₀ a l₂ k₁ k₂ t g n) y)

/-- The residue `ℓ^p`-average of the variational norms of the fibres. -/
noncomputable def GmixedRes (p₂ : ENNReal) (r : NNReal) (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ)
    (a : ℕ → NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ) : ℤ → ENNReal :=
  fun x => residueLp p₂.toReal (arithQ ρ l₂) (GmixedFib r ρ P C₀ a l₂ k₁ k₂ t g) x

/-! ## §2.  `diffFreqs` at positive heights -/

/-- At positive arithmetic height the `diffFreqs` convention and the exact-height convention of
`iwArithFreqsNew` agree. -/
theorem diffFreqs_eq_iwArithFreqsNew {ρ : ℝ} {l : ℕ} (hl : l ≠ 0) :
    diffFreqs ρ l = Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l := by
  rw [diffFreqs, if_neg hl, Work.Analysis.IonescuWainger.iwArithFreqsNew]

/-! ## §3.  The loss weight -/

/-- `lmaxR` is nonnegative. -/
theorem lmaxR_nonneg' (l₁ l₂ k₁ k₂ : ℕ) : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
  rw [lmaxR, Work.Analysis.EndVar.lmax]
  push_cast
  positivity

/-- The loss weight is nonnegative. -/
theorem lossWeight_nonneg' (c ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    0 ≤ lossWeight c ρ l₁ l₂ k₁ k₂ := by
  rw [lossWeight]
  exact mul_nonneg (Real.rpow_nonneg (by linarith [lmaxR_nonneg' l₁ l₂ k₁ k₂]) _)
    (Real.rpow_nonneg (by norm_num) _)

/-- The loss weight is at least `1` for `c ≥ 0`, `ρ ≥ 0`. -/
theorem one_le_lossWeight' {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    1 ≤ lossWeight c ρ l₁ l₂ k₁ k₂ := by
  have hL : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := lmaxR_nonneg' l₁ l₂ k₁ k₂
  have h1 : (1 : ℝ) ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ c := Real.one_le_rpow (by linarith) hc
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (c * ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ c * (2 : ℝ) ^ (c * ρ * lmaxR l₁ l₂ k₁ k₂) :=
        mul_le_mul h1 h2 (by norm_num) (le_trans zero_le_one h1)
    _ = lossWeight c ρ l₁ l₂ k₁ k₂ := rfl

/-- The loss weights multiply: `lossWeight a · lossWeight b = lossWeight (a+b)`. -/
theorem lossWeight_mul' (a b ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    lossWeight a ρ l₁ l₂ k₁ k₂ * lossWeight b ρ l₁ l₂ k₁ k₂
      = lossWeight (a + b) ρ l₁ l₂ k₁ k₂ := by
  have h1 : (0 : ℝ) < 1 + lmaxR l₁ l₂ k₁ k₂ := by
    have := lmaxR_nonneg' l₁ l₂ k₁ k₂; linarith
  have hexp : a * ρ * lmaxR l₁ l₂ k₁ k₂ + b * ρ * lmaxR l₁ l₂ k₁ k₂
      = (a + b) * ρ * lmaxR l₁ l₂ k₁ k₂ := by ring
  rw [lossWeight, lossWeight, lossWeight, mul_mul_mul_comm, ← Real.rpow_add h1,
    ← Real.rpow_add (by norm_num : (0:ℝ) < 2), hexp]

/-! ## §4.  The residue Hölder inequality -/

/-- **The pointwise Hölder inequality for the normalized residue sum.**  For `p > 1`, `q ≥ 1`,
`W : ℤ → ℕ → ℝ≥0∞` and `x : ℤ`, the uniform average of `W x ·` over `n < q` is bounded by its
`ℓ^p`-average:

  `q⁻¹ ∑_{n<q} W x n ≤ (q⁻¹ ∑_{n<q} (W x n) ^ p)^{1/p}`. -/
theorem inv_mul_sum_le_residueLp {p : ℝ} (hp : 1 < p) {q : ℕ} (hq : 0 < q)
    (W : ℤ → ℕ → ENNReal) (x : ℤ) :
    (q : ENNReal)⁻¹ * ∑ n ∈ Finset.range q, W x n ≤ residueLp p q W x := by
  set p₂ : ℝ := max 2 (p / (p - 1)) with hp₂def
  have hp2gt : 1 < p₂ := lt_of_lt_of_le (by norm_num) (le_max_left 2 _)
  have h2 : (p / (p - 1))⁻¹ = (p - 1) / p := by
    rw [div_eq_mul_inv, mul_inv_rev, inv_inv, div_eq_mul_inv]
  have hsum : p⁻¹ + p₂⁻¹ ≤ 1 := by
    have hle : p / (p - 1) ≤ p₂ := le_max_right _ _
    have h1 : p₂⁻¹ ≤ (p - 1) / p := by
      rw [← h2]
      exact inv_anti₀ (div_pos (by linarith) (by linarith)) hle
    have h3 : p⁻¹ + (p - 1) / p = 1 := by
      rw [inv_eq_one_div, ← add_div, show 1 + (p - 1) = p from by ring,
        div_self (ne_of_gt (by linarith : (0:ℝ) < p))]
    linarith [h1, h3]
  have hq0 : (q : ENNReal) ≠ 0 := by exact_mod_cast hq.ne'
  have hqt : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  have hone : (q : ENNReal)⁻¹ * (q : ENNReal) = 1 := ENNReal.inv_mul_cancel hq0 hqt
  have hsum1 : (∑ n ∈ Finset.range q, (1 : ENNReal) ^ p₂) = (q : ENNReal) := by
    have hc : ∀ n ∈ Finset.range q, (1 : ENNReal) ^ p₂ = (1 : ENNReal) :=
      fun n _ => ENNReal.one_rpow p₂
    rw [Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  have hright : ((q : ENNReal)⁻¹ * ∑ n ∈ Finset.range q, (1 : ENNReal) ^ p₂) ^ (1 / p₂) = 1 := by
    rw [hsum1, hone, ENNReal.one_rpow]
  have h := residueSum_mul_le q p p₂ hp hp2gt hsum (fun n => W x n) (fun _ => 1)
  simp only [mul_one] at h
  refine h.trans (le_of_eq ?_)
  rw [hright, mul_one]
  unfold residueLp
  rw [show ENNReal.rpow (q : ENNReal) (-1) = (q : ENNReal)⁻¹ from
    ENNReal.rpow_neg_one (q : ENNReal)]
  rfl

/-! ## §5.  The linear `form-1` identity of the mixed range -/

/-- The modulus of an arithmetic character sum is at most the number of frequencies. -/
theorem norm_arithCharSet_le_card (A : Finset Work.Analysis.IonescuWainger.Circle) (y : ℤ) :
    ‖arithCharSet A y‖ ≤ (A.card : ℝ) := by
  rw [arithCharSet]
  calc ‖∑ α ∈ A, fourier (T := 1) y α‖ ≤ ∑ α ∈ A, ‖fourier (T := 1) y α‖ := norm_sum_le _ _
    _ = ∑ _α ∈ A, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun α _ => ?_)
        rw [fourier_apply]
        exact _root_.Circle.norm_coe _
    _ = (A.card : ℝ) := by simp

/-- **The linear `form-1` identity of the mixed range.**  The convolution with the arithmetic
kernel `loMixedGKer` is the average over the residues `n₀ < arithQ ρ l₂` of the fibres
`fiberOpP ρ P l₂ m₂ n₀`.  The summability hypothesis is the one needed to interchange the two
sums; it is supplied by `summable_fiberSet_family` whenever `v` is bounded. -/
theorem convOp_loMixedGKer_eq_fiberSum (ρ : ℝ) (P : Polynomial ℤ) (l₂ : ℕ) (hl₂ : 1 ≤ l₂)
    (m₂ : ℝ → ℂ) (v : ℤ → ℂ) (x : ℤ)
    (hs : ∀ n₀ : ℤ, Summable (fun j : ℤ =>
      arithCharSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) (P.eval n₀ - j)
        * cw m₂ j * v (x - j))) :
    convOp (loMixedGKer ρ P l₂ m₂) v x
      = ((arithQ ρ l₂ : ℂ))⁻¹ * ∑ n₀ ∈ Finset.range (arithQ ρ l₂),
          fiberOpP ρ P l₂ m₂ (n₀ : ℤ) v x := by
  have hl₂0 : l₂ ≠ 0 := by omega
  have hpoint : ∀ j : ℤ, loMixedGKer ρ P l₂ m₂ j * v (x - j)
      = ∑ n₀ ∈ Finset.range (arithQ ρ l₂),
          ((arithQ ρ l₂ : ℂ))⁻¹ * arithCharSet
              (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) (P.eval (n₀ : ℤ) - j)
            * cw m₂ j * v (x - j) := by
    intro j
    rw [loMixedGKer_eq_fiberAvg, diffFreqs_eq_iwArithFreqsNew hl₂0]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
  have hs' : ∀ n₀ : ℤ, Summable (fun j : ℤ =>
      ((arithQ ρ l₂ : ℂ))⁻¹ * arithCharSet
          (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) (P.eval n₀ - j)
        * cw m₂ j * v (x - j)) := by
    intro n₀
    refine ((hs n₀).mul_left ((arithQ ρ l₂ : ℂ))⁻¹).congr (fun j => by ring)
  rw [convOp, tsum_congr hpoint]
  rw [Summable.tsum_finsetSum
    (f := fun (n₀ : ℕ) (j : ℤ) => ((arithQ ρ l₂ : ℂ))⁻¹ * arithCharSet
        (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) (P.eval (n₀ : ℤ) - j)
      * cw m₂ j * v (x - j))
    (fun n₀ _ => hs' n₀)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n₀ _ => ?_)
  rw [show (fun j : ℤ => ((arithQ ρ l₂ : ℂ))⁻¹ * arithCharSet
          (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) (P.eval (n₀ : ℤ) - j)
        * cw m₂ j * v (x - j))
      = fun j : ℤ => ((arithQ ρ l₂ : ℂ))⁻¹ *
          (arithCharSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂)
            (P.eval (n₀ : ℤ) - j) * cw m₂ j * v (x - j)) from
      funext (fun j => by ring)]
  rw [tsum_mul_left]
  rfl

/-! ## §6.  The pointwise variational bound by the residue average -/

/-- Moving the clipping `if` of the target family inside the convolution (the convolution is
linear and kills `0`). -/
theorem variationalNorm_convOp_ite (r : NNReal) (κ : ℤ → ℂ) (c : ℕ → Prop) [DecidablePred c]
    (u : ℕ → ℤ → ℂ) (x : ℤ) :
    variationalNorm r (fun n : ℕ => (if c n then convOp κ (u n) x else 0))
      = variationalNorm r (fun n : ℕ => convOp κ (if c n then u n else 0) x) := by
  congr 1
  funext n
  by_cases hn : c n
  · rw [if_pos hn, if_pos hn]
  · rw [if_neg hn, if_neg hn]
    simp only [convOp, Pi.zero_apply, mul_zero, tsum_zero]

/-- **The variational norm of the fibre average is bounded by the residue `ℓ^p`-average of the
variational norms of the fibres**: subadditivity of `V^r`, homogeneity, and Hölder over the
residues. -/
theorem variationalNorm_convOp_loMixedGKer_le {r : NNReal} (hr : 1 ≤ r) (ρ : ℝ)
    (P : Polynomial ℤ) (l₂ : ℕ) (hl₂ : 1 ≤ l₂) (p : ℝ) (hp : 1 < p) (m₂ : ℝ → ℂ)
    (v : ℕ → ℤ → ℂ) (x : ℤ)
    (hs : ∀ (n : ℕ) (n₀ : ℤ), Summable (fun j : ℤ =>
      arithCharSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) (P.eval n₀ - j)
        * cw m₂ j * v n (x - j))) :
    variationalNorm r (fun n : ℕ => convOp (loMixedGKer ρ P l₂ m₂) (v n) x)
      ≤ residueLp p (arithQ ρ l₂)
          (fun y n₀ => variationalNorm r (fun n : ℕ => fiberOpP ρ P l₂ m₂ n₀ (v n) y)) x := by
  have hq : 0 < arithQ ρ l₂ := arithQ_pos ρ l₂
  have hcoef : ‖(((arithQ ρ l₂ : ℂ))⁻¹)‖ₑ = (arithQ ρ l₂ : ENNReal)⁻¹ := by
    rw [← ofReal_norm, norm_inv, Complex.norm_natCast,
      ENNReal.ofReal_inv_of_pos (by exact_mod_cast hq), ENNReal.ofReal_natCast]
  have hfun : (fun n : ℕ => convOp (loMixedGKer ρ P l₂ m₂) (v n) x)
      = ((arithQ ρ l₂ : ℂ))⁻¹ • (fun n : ℕ => ∑ n₀ ∈ Finset.range (arithQ ρ l₂),
          fiberOpP ρ P l₂ m₂ (n₀ : ℤ) (v n) x) := by
    funext n
    rw [Pi.smul_apply, smul_eq_mul]
    exact convOp_loMixedGKer_eq_fiberSum ρ P l₂ hl₂ m₂ (v n) x (fun n₀ => hs n n₀)
  calc variationalNorm r (fun n : ℕ => convOp (loMixedGKer ρ P l₂ m₂) (v n) x)
      = ‖(((arithQ ρ l₂ : ℂ))⁻¹)‖ₑ * variationalNorm r (fun n : ℕ =>
          ∑ n₀ ∈ Finset.range (arithQ ρ l₂), fiberOpP ρ P l₂ m₂ (n₀ : ℤ) (v n) x) := by
        rw [hfun, variationalNorm_smul (r := r) hr]
    _ ≤ ‖(((arithQ ρ l₂ : ℂ))⁻¹)‖ₑ * ∑ n₀ ∈ Finset.range (arithQ ρ l₂),
          variationalNorm r (fun n : ℕ => fiberOpP ρ P l₂ m₂ (n₀ : ℤ) (v n) x) :=
        mul_le_mul_right (variationalNorm_finset_sum_le hr (Finset.range (arithQ ρ l₂))
          (fun n₀ n => fiberOpP ρ P l₂ m₂ (n₀ : ℤ) (v n) x)) _
    _ = (arithQ ρ l₂ : ENNReal)⁻¹ * ∑ n₀ ∈ Finset.range (arithQ ρ l₂),
          variationalNorm r (fun n : ℕ => fiberOpP ρ P l₂ m₂ (n₀ : ℤ) (v n) x) := by
        rw [hcoef]
    _ ≤ residueLp p (arithQ ρ l₂)
          (fun y n₀ => variationalNorm r (fun n : ℕ => fiberOpP ρ P l₂ m₂ n₀ (v n) y)) x :=
        inv_mul_sum_le_residueLp hp hq
          (fun y n₀ => variationalNorm r (fun n : ℕ => fiberOpP ρ P l₂ m₂ n₀ (v n) y)) x

/-! ## §7.  Bounds and summability of the fibre families -/

/-- The `cw`-coefficients of `mStargF d u` decay quadratically. -/
theorem cw_mStargF_decay (d u : ℕ) :
    ∃ Cd : ℝ, ∀ j : ℤ, ‖cw (mStargF d u) j‖ ≤ Cd / (1 + |(j : ℝ)|) ^ 2 := by
  obtain ⟨C, _hCpos, hC⟩ := cw_etaCut_decay (-((d : ℤ) * 2 * (u : ℤ)))
  exact ⟨C, fun j => by simpa only [mStargF] using hC j⟩

/-- A bounded sequence has summable fibre families. -/
theorem summable_fiber_family_of_bounded (ρ : ℝ) (P : Polynomial ℤ) (l₂ : ℕ) (m₂ : ℝ → ℂ)
    (hdec : ∃ Cd : ℝ, ∀ j : ℤ, ‖cw m₂ j‖ ≤ Cd / (1 + |(j : ℝ)|) ^ 2)
    (Bv : ℝ) (v : ℤ → ℂ) (hv : ∀ y : ℤ, ‖v y‖ ≤ Bv) (x : ℤ) :
    ∀ n₀ : ℤ, Summable (fun j : ℤ =>
      arithCharSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) (P.eval n₀ - j)
        * cw m₂ j * v (x - j)) :=
  fun n₀ => summable_fiberSet_family (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂) m₂ v x hdec
    ⟨((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂).card : ℝ),
      fun y => norm_arithCharSet_le_card _ y⟩ ⟨Bv, hv⟩ (P.eval n₀)

/-- **The `g`-side IW projection of a bounded sequence is bounded**, uniformly in `t ∈ [1/2,1]`. -/
theorem Tm_varphitildeNt_bounded_g (P : Polynomial ℤ) (ρ : ℝ) (l N k : ℕ) (hl : l ≠ 0) (g : ℤ → ℂ)
    (Cg : ℝ) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) :
    ∃ C : ℝ, ∀ x : ℤ, ‖Tm ρ l (varphitildeNt P P.natDegree N k t) g x‖ ≤ C := by
  obtain ⟨S, hSnn, hspec⟩ := Work.KMTPlan.A6.varphitildeNt_bounds P P.natDegree N k
  have hcd : ContDiff ℝ 2 (fun ξ => varphitildeNt P P.natDegree N k t ξ) := (hspec t ht).1
  have hcs : HasCompactSupport (fun ξ => varphitildeNt P P.natDegree N k t ξ) := (hspec t ht).2.1
  have hI1 : (∫ y, ‖varphitildeNt P P.natDegree N k t y‖) ≤ S := (hspec t ht).2.2.1
  have hI2 : (∫ y, ‖iteratedDeriv 2 (fun ξ => varphitildeNt P P.natDegree N k t ξ) y‖) ≤ S :=
    (hspec t ht).2.2.2
  refine ⟨(4 * (((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l).card : ℝ) * S) + 1) *
      (∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2) * max Cg 0, ?_⟩
  intro x
  have hdec := iwKernel_decay_of_bump (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
    hcd hcs hSnn hI1 hI2
  have hdec' : ∀ j : ℤ, ‖iwKernel (iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
        (periodize (varphitildeNt P P.natDegree N k t))) j‖
      ≤ (4 * (((Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l).card : ℝ) * S) + 1)
          / (1 + |(j : ℝ)|) ^ 2 := by
    intro j
    have h := hdec j
    rw [norm_kmtKernWeight] at h
    simpa only [div_eq_mul_inv, one_mul] using h
  rw [Tm, diffFreqs_eq_iwArithFreqsNew hl, iwConv_eq_tsum_mul]
  exact norm_tsum_kernel_mul_le hdec' hg x

/-- **The linear `g`-side input of the mixed range**: the lacunary variational estimate for the
guarded family `GmixedFam` (paper `(lin-2)` without the fibre cut). -/
def LinVarGuard (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) : Prop :=
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₂ →
          t ∈ Set.Icc (1/2 : ℝ) 1 → BddAbove (Set.range fun y : ℤ => ‖g y‖) →
          MeasureTheory.eLpNorm (GmixedVar r ρ P C₀ a l₂ k₁ k₂ t g) p₂ MeasureTheory.Measure.count
            ≤ (C Λ : ENNReal) * ENNReal.ofReal (lossWeight A ρ 0 l₂ k₁ k₂) *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count

/-- **The fibre (`form-1`/sampling) input of the mixed range**: with the repaired window
`loMixedU` the residue `ℓ^{p₂}`-average of the variational norms of the fibres of `GmixedFam` is
bounded by the variational norm of `GmixedFam` itself, with the loss `lossWeight A`. -/
def FiberGuard (P : Polynomial ℤ) (p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) : Prop :=
  ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
    ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ C : NNReal → NNReal,
        ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (g : ℤ → ℂ),
          1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → 1 ≤ l₂ →
          t ∈ Set.Icc (1/2 : ℝ) 1 → BddAbove (Set.range fun y : ℤ => ‖g y‖) →
          MeasureTheory.eLpNorm (GmixedRes p₂ r ρ P C₀ a l₂ k₁ k₂ t g) p₂
              MeasureTheory.Measure.count
            ≤ (C Λ : ENNReal) * ENNReal.ofReal (lossWeight A ρ 0 l₂ k₁ k₂) *
                MeasureTheory.eLpNorm (GmixedVar r ρ P C₀ a l₂ k₁ k₂ t g) p₂
                  MeasureTheory.Measure.count
end

end Work.KMTAreas.A7
