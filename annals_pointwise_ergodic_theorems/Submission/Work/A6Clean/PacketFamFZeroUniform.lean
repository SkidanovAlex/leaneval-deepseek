/-
# The uniform `(lin-1)` data bound at arithmetic height `0` (the `l₁ = 0` case)

`Work.KMTPlan.A6Clean.PacketFamFUniform` (`Submission/Work/A6Clean/PacketFamFUniform.lean`) proves
the uniform `(lin-1)` clause of the §8 adelic form for the `f`-side packet family
`packetFamF ρ a l₁ l₂ k₁ k₂ W` **under the vanishing hypothesis**
`hW0 : α ∉ iwArithFreqsNew ρ l₁ → W n α = 0`.

At arithmetic height `l₁ = 0` that hypothesis is uninhabitable together with the *samples* clause:
`iwArithFreqsNew ρ 0 = ∅` (`ℕ`-truncated subtraction), so `hW0` forces `W ≡ 0`, while the packets
are the (non-zero) window pieces of `mdlSliceF ρ C₀ a 0 l₂ ⋯`.  The correct statement at height `0`
is therefore the one below: the same uniform bound, with the samples clause asked only on
`iwArithFreqs ρ 0 = {0}` and **without** the vanishing hypothesis.

## The proof (independent of the `l₁ ≥ 1` route, and uniform in everything)

At `l₁ = 0` the packet family is θ-independent:
`packetFamF ρ a 0 l₂ k₁ k₂ W n X θ = 1_{goodScale} · W n 0 X` (`packetFamF_zero_apply`), and the
samples clause gives `W n 0 (x:ℝ) = winConvR (mStarF U) (mdlSliceF ρ C₀ a 0 ⋯ n) x`
(`hWs0`).  So the whole estimate is scalar:

1. **lattice sampling** (`Work.A6Clean.VrLiftSamplingLattice`): the `V^R`-datum of the inverse
   Fourier transform of a band-limited amplitude family is dominated by its integer samples; the
   gate `goodScale` is an upper set in `n` (`goodScale_floor_mono`), so clipping it away costs
   `2` (`Work.A6HighLow.VrLiftClip`);
2. **the θ-constant family** is dominated by twice its scalar variational norm
   (`VrLiftConstVarNorm_local`);
3. **Young's inequality** for the window convolution `winConvR`, with the *uniform* `ℓ¹`-mass of
   `cw (mStarF u)` (`Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le`), gives
   `‖V^R (W · 0)‖_{ℓ²} ≤ mStarMass · ‖V^R (mdlSliceF)‖_{ℓ²}` (`VarNormWinConvLe_local`);
4. the `ℓ²`-bound of the model slice family `mdlSliceF` is the PROVED
   `Work.KMTPlan.A6.MdlSlicePktLinF`.

No Farey/band-limited/fibre machinery is needed: at height `0` the "fibre" is the plain window
convolution, whose kernel mass is uniformly bounded.
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.mdlLiftFZero
import Submission.Work.A6HighLow.VrLiftClip
import Submission.Work.A6Clean.VrLiftSamplingLattice
import Submission.Work.KMTPlan.A6.MdlSlicePktLinF
import Submission.Work.KMTPlan.A6Clean.VrChainSumLe
import Submission.Port.Aesm

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Work.A6Clean

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section

/-! ## Elementary helpers -/

/-- The circle character at the origin is `1`. -/
lemma fourier_arg_zero (n : ℤ) : fourier (T := 1) n (0 : Circ) = 1 := by
  rw [fourier_apply, smul_zero]
  exact fourier_zero'

/-- The zero window modulation is the identity. -/
lemma winModR_zero_apply (v : ℤ → ℂ) : Work.KMTAreas.A7.winModR (0 : Circ) v = v := by
  funext x
  rw [Work.KMTAreas.A7.winModR, fourier_arg_zero, one_mul]

/-- **The packet family at arithmetic height `0`** is the gated single lift `W n 0`: the sum in
`packetFamF` runs over `iwArithFreqs ρ 0 = {0}`, where the character is `1`. -/
lemma packetFamF_zero_apply (ρ : ℝ) (a : ℕ → NNReal) (l₂ k₁ k₂ : ℕ) (W : ℕ → Circ → ℝ → ℂ)
    (n : ℕ) (X : ℝ) (θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) :
    Work.KMTPlan.A6Clean.packetFamF ρ a 0 l₂ k₁ k₂ W n X θ
      = if Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
            (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂) (Nat.floor (a n)) then W n 0 X else 0 := by
  rw [Work.KMTPlan.A6Clean.packetFamF_apply]
  by_cases h : Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
      (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂) (Nat.floor (a n))
  · rw [if_pos h, if_pos h, Work.KMTAreas.A7.iwArithFreqs_zero, Finset.sum_singleton,
      fourier_arg_zero, one_mul]
  · rw [if_neg h, if_neg h]

/-- `eLpNorm` of a constant on the probability measure `zmodProb Q`. -/
lemma eLpNorm_const_zmodProb {Q : ℕ} [NeZero Q] (c : ℂ) :
    MeasureTheory.eLpNorm (fun _ : ZMod Q => c) 2 (Work.KMTPlan.A6.zmodProb Q) = ‖c‖ₑ := by
  have hμ : Work.KMTPlan.A6.zmodProb Q ≠ 0 := by
    intro h0
    have h1 := Work.KMTPlan.A6.zmodProb_univ (Q := Q)
    rw [h0] at h1
    simp at h1
  rw [MeasureTheory.eLpNorm_const c (by norm_num : (2 : ENNReal) ≠ 0) hμ,
    Work.KMTPlan.A6.zmodProb_univ, ENNReal.one_rpow, mul_one]

/-- The `p`-th power of the `ℒᵖ`-seminorm over the counting measure on `ℤ` is the `p`-sum. -/
lemma tsum_pow_eq_eLpNorm_pow {p : ℝ} (hp : 0 < p) (F : ℤ → ENNReal) :
    (∑' m : ℤ, (F m) ^ p)
      = (MeasureTheory.eLpNorm F (ENNReal.ofReal p) MeasureTheory.Measure.count) ^ p := by
  rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) (ENNReal.ofReal_ne_zero_iff.mpr hp)
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le]
  have h1 : (∫⁻ m : ℤ, ‖F m‖ₑ ^ p ∂MeasureTheory.Measure.count) = ∑' m : ℤ, (F m) ^ p := by
    rw [MeasureTheory.lintegral_count]
    exact tsum_congr fun m => by rw [enorm_eq_self]
  rw [h1, ← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]

/-- The gate `goodScale Q L ⌊a n⌋` is monotone in `n` along a lacunary scale sequence. -/
lemma goodScale_floor_mono {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
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
          mul_le_mul_of_nonneg_right (le_of_lt hΛ) (show (0 : NNReal) ≤ a k from bot_le)
      _ ≤ a (k + 1) := le_of_lt hmul
  have hfl : Nat.floor (a n) ≤ Nat.floor (a m) := Nat.floor_mono (hmono hnm)
  exact le_trans h hfl

/-! ## The two analytic bricks (also delegated, as `Work.A6Zero.*`) -/

/-- **The `VrLiftDataP` datum of a `θ`-constant family** is at most twice its scalar variational
norm: the `L²(zmodProb Q)`-norms of the constants are their norms, and the chain part is exactly the
variational part. -/
theorem VrLiftConstVarNorm_local {Q : ℕ} [NeZero Q] (R : NNReal) (hR : 1 ≤ R) (G : ℕ → ℂ) :
    Work.KMTPlan.A6.VrLiftDataP (R : ℝ) Q (fun n (_ : ZMod Q) => G n)
      ≤ 2 * PointwiseErgodicTheorems.variationalNorm R G := by
  have hRpos : (0 : ℝ) < (R : ℝ) := by
    have h1 : (0 : NNReal) < R := lt_of_lt_of_le zero_lt_one hR
    exact_mod_cast h1
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := hRpos.le
  have h1R : (0 : ℝ) ≤ 1 / (R : ℝ) := le_of_lt (one_div_pos.mpr hRpos)
  have hsup : (⨆ n : ℕ, eLpNorm (fun _ : ZMod Q => G n) 2 (Work.KMTPlan.A6.zmodProb Q))
      ≤ PointwiseErgodicTheorems.variationalNorm R G := by
    refine iSup_le fun n => ?_
    rw [eLpNorm_const_zmodProb]
    exact Work.KMTAreas.A7.enorm_apply_le_variationalNorm G n
  have hchain : (⨆ (J : ℕ) (k : Fin (J + 1) → ℕ) (_ : Monotone k),
        ENNReal.rpow (∑ i : Fin J, ENNReal.rpow (eLpNorm
          ((fun n (_ : ZMod Q) => G n) (k i.succ)
            - (fun n (_ : ZMod Q) => G n) (k i.castSucc)) 2
          (Work.KMTPlan.A6.zmodProb Q)) (R : ℝ)) (1 / (R : ℝ)))
      ≤ PointwiseErgodicTheorems.variationalNorm R G := by
    refine iSup_le fun J => iSup_le fun k => iSup_le fun hk => ?_
    have hdiff : ∀ i : Fin J, ((fun n (_ : ZMod Q) => G n) (k i.succ)
        - (fun n (_ : ZMod Q) => G n) (k i.castSucc))
        = fun _ : ZMod Q => G (k i.succ) - G (k i.castSucc) :=
      fun i => by funext θ; rfl
    have hsum : (∑ i : Fin J, ENNReal.rpow (eLpNorm ((fun n (_ : ZMod Q) => G n) (k i.succ)
          - (fun n (_ : ZMod Q) => G n) (k i.castSucc)) 2 (Work.KMTPlan.A6.zmodProb Q)) (R : ℝ))
        = ENNReal.ofReal (∑ i : Fin J, ‖G (k i.succ) - G (k i.castSucc)‖ ^ (R : ℝ)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (norm_nonneg _) _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hdiff i, eLpNorm_const_zmodProb, ← ofReal_norm]
      exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hR0
    rw [hsum]
    refine (le_of_eq (ENNReal.ofReal_rpow_of_nonneg
      (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _) h1R)).trans ?_
    exact Work.KMTPlan.A6Clean.ofReal_chain_sum_le_variationalNorm hR k hk G
  rw [Work.KMTPlan.A6.VrLiftDataP]
  exact (add_le_add hsup hchain).trans_eq (by rw [two_mul])

/-- **Minkowski/Young for `ℝ≥0∞`-valued functions on the counting measure of `ℤ`**: for `q ≥ 1`,
`K : ℤ → ℂ` and `W : ℤ → ℝ≥0∞`,
`‖ x ↦ ∑'_j ‖K j‖ · W (x - j) ‖_{ℓ^q} ≤ (∑'_j ‖K j‖) · ‖W‖_{ℓ^q}`. -/
private lemma eLpNorm_tsum_enorm_mul_sub_le_aux {q : ℝ} (hq : 1 ≤ q) (K : ℤ → ℂ)
    (W : ℤ → ENNReal) :
    eLpNorm (fun x : ℤ => ∑' j : ℤ, ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q) Measure.count
      ≤ (∑' j : ℤ, ‖K j‖ₑ) * eLpNorm W (ENNReal.ofReal q) Measure.count := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq
  have hmink := Commons.MeasureTheory.Lp.eLpNorm_tsum_le_tsum_eLpNorm (μ := Measure.count)
    (p := ENNReal.ofReal q)
    (ENNReal.one_le_ofReal.mpr hq) (f := fun j : ℤ => fun x : ℤ => ‖K j‖ₑ * W (x - j))
    (fun j => (measurable_of_countable (fun x : ℤ => ‖K j‖ₑ * W (x - j))).aemeasurable)
  have hconst : ∀ j : ℤ,
      eLpNorm (fun x : ℤ => ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q) Measure.count
        = ‖K j‖ₑ * eLpNorm W (ENNReal.ofReal q) Measure.count := by
    intro j
    rw [show eLpNorm (fun x : ℤ => ‖K j‖ₑ * W (x - j)) (ENNReal.ofReal q) Measure.count
        = eLpNorm (fun x : ℤ => ‖K j‖ₑ * W x) (ENNReal.ofReal q) Measure.count from
        Commons.Analysis.Convolution.eLpNorm_sub_right_ennreal (fun y : ℤ => ‖K j‖ₑ * W y) j hq0]
    exact Commons.Analysis.Convolution.eLpNorm_const_mul_ennreal_of_pos
      (f := W) (measurable_of_countable W).aemeasurable (‖K j‖ₑ) hq0
  refine hmink.trans_eq ?_
  rw [tsum_congr hconst, ENNReal.tsum_mul_right]

/-- **Young's inequality for the window convolution**: the `ℓ^q(ℤ; V^r)`-norm of the family
`n ↦ winConvR m (w n)` is at most the `ℓ¹`-mass of the kernel `cw m` times the `ℓ^q(ℤ; V^r)`-norm of
`w`. -/
theorem VarNormWinConvLe_local (r : NNReal) (hr : 1 ≤ r) (m : ℝ → ℂ) (w : ℕ → ℤ → ℂ)
    {C : ℝ} (hC : 0 ≤ C) {q : ℝ} (hq : 1 ≤ q)
    (hmass : (∑' j : ℤ, ENNReal.ofReal ‖Work.KMTAreas.A7.cw m j‖) ≤ ENNReal.ofReal C) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.winConvR m (w n) x))
      (ENNReal.ofReal q) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x))
        (ENNReal.ofReal q) MeasureTheory.Measure.count := by
  set W : ℤ → ENNReal := fun x =>
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x) with hW
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Work.KMTAreas.A7.winConvR m (w n) x)
      ≤ ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ₑ * W (x - j) := by
    intro x
    have h := Work.KMTAreas.A7Hi.variationalNorm_tsum_le r hr
      (fun j : ℤ => Work.KMTAreas.A7.cw m j) (fun (j : ℤ) (n : ℕ) => w n (x - j))
    have hleft : (fun n : ℕ => ∑' j : ℤ, Work.KMTAreas.A7.cw m j * w n (x - j))
        = fun n : ℕ => Work.KMTAreas.A7.winConvR m (w n) x := by
      funext n
      rw [Work.KMTAreas.A7.winConvR]
    rw [hleft] at h
    simpa only [hW] using h
  have hmass' : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ₑ) ≤ ENNReal.ofReal C := by
    have h : (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ₑ)
        = ∑' j : ℤ, ENNReal.ofReal ‖Work.KMTAreas.A7.cw m j‖ :=
      tsum_congr fun j => (ofReal_norm _).symm
    rw [h]; exact hmass
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.winConvR m (w n) x))
        (ENNReal.ofReal q) MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ₑ * W (x - j))
          (ENNReal.ofReal q) MeasureTheory.Measure.count :=
        eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by simpa only [enorm_eq_self] using hpt x)
    _ ≤ (∑' j : ℤ, ‖Work.KMTAreas.A7.cw m j‖ₑ)
          * MeasureTheory.eLpNorm W (ENNReal.ofReal q) MeasureTheory.Measure.count :=
        eLpNorm_tsum_enorm_mul_sub_le_aux hq _ W
    _ ≤ ENNReal.ofReal C
          * MeasureTheory.eLpNorm W (ENNReal.ofReal q) MeasureTheory.Measure.count :=
        mul_le_mul_left hmass' _
    _ = ENNReal.ofReal C * MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x))
          (ENNReal.ofReal q) MeasureTheory.Measure.count := by rw [hW]

/-! ## The target -/

theorem PacketFamFZeroUniform (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R) (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) : ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal, ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ) (W : ℕ → Work.Analysis.IonescuWainger.Circle → ℝ → ℂ), 1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → MeasureTheory.MemLp f 2 MeasureTheory.Measure.count → t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ ≠ -1) → (∀ (n : ℕ) (α : Work.Analysis.IonescuWainger.Circle), Work.KMTAreas.A7Rep.HasRealFreqSupport (W n α) (Set.Icc (-(1 / 4 : ℝ)) (1 / 4))) → (∀ n : ℕ, ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0, ∀ x : ℤ, W n α (x : ℝ) = Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂))) (Work.KMTAreas.A7.winModR (-α) (Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n)) x) → ∫⁻ X : ℝ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ) (Work.KMTAreas.A7.arithQ ρ (max 0 l₂)) (fun n : ℕ => Work.KMTPlan.A6Clean.packetFamF ρ a 0 l₂ k₁ k₂ W n X)) ^ (2 : ℕ) ≤ (K Λ : ENNReal) ^ (2 : ℕ) * (ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ 0 l₂ k₁ k₂)) ^ (2 : ℕ) * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
  classical
  -- the two proved uniform inputs
  obtain ⟨A₀, hA₀, ρ₀L, hρ₀L, hLin⟩ := Work.KMTPlan.A6.MdlSlicePktLinF C₀ hC₀ R hR j₁ hj₁
  obtain ⟨Cs, hCspos, hSamp⟩ := Work.A6Clean.VrLiftSamplingLattice
  obtain ⟨Mw, hMwpos, hMw⟩ := Work.KMTPlan.A6.vpc_exists_cw_mStarF_tsum_le
  have hMw0 : (0 : ℝ) ≤ Mw := le_of_lt hMwpos
  have hR1' : (1 : NNReal) ≤ R := le_of_lt (lt_of_le_of_lt (by norm_num) hR)
  have hR1 : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR1'
  refine ⟨A₀, hA₀, min 1 ρ₀L, lt_min one_pos hρ₀L, ?_⟩
  intro ρ hρ hρ₀
  have hρ1 : ρ ≤ 1 := le_trans hρ₀ (min_le_left _ _)
  have hρL : ρ ≤ ρ₀L := le_trans hρ₀ (min_le_right _ _)
  obtain ⟨K₀, hK₀⟩ := hLin ρ hρ hρL
  let c₀ : NNReal := ⟨Nat.ceil (16 * Cs * (max Mw 1) ^ 2) + 1, by positivity⟩
  refine ⟨fun Λ => K₀ Λ * c₀, ?_⟩
  intro a Λ l₂ k₁ k₂ t f W hΛ ha ha1 hf ht hk₁ hWb hWs
  haveI : NeZero (Work.KMTAreas.A7.arithQ ρ (max 0 l₂)) :=
    ⟨Nat.pos_iff_ne_zero.mp (Work.KMTAreas.A7.arithQ_pos ρ (max 0 l₂))⟩
  -- the gate is an upper set in the scale `n`
  have hγmono : ∀ ⦃n m : ℕ⦄, n ≤ m →
      Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
        (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂) (Nat.floor (a n)) →
      Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
        (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂) (Nat.floor (a m)) :=
    fun n m hnm h => goodScale_floor_mono hΛ ha ha1 _ _ hnm h
  -- the amplitudes of the lift
  choose g hgint hgsupp hgpt using hWb
  -- the samples clause at the single frequency `0`
  have h0mem : (0 : Circ) ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ 0 := by
    rw [Work.KMTAreas.A7.iwArithFreqs_zero]; simp
  have hWs0 : ∀ (n : ℕ) (x : ℤ), W n 0 (x : ℝ) = Work.KMTAreas.A7.winConvR
      (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂)))
      (Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n) x := by
    intro n x
    have h := hWs n 0 h0mem x
    rwa [neg_zero, winModR_zero_apply] at h
  -- the `(lin-1)` bound of the model slice family
  have hGG : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
      (fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n then
        Work.KMTAreas.A7.Tle ρ 0 (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t)
          (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max k₁ k₂))) 0 f)
          x
        else 0)) 2 MeasureTheory.Measure.count
      ≤ (K₀ Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ 0 l₂ k₁ k₂)
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
    hK₀ a Λ 0 l₂ k₁ k₂ t f hΛ ha ha1 ht hk₁
  set VV : ℤ → ENNReal := fun x => PointwiseErgodicTheorems.variationalNorm R
      (fun n : ℕ => Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n x) with hVV
  have hVV_bound : MeasureTheory.eLpNorm (fun y : ℤ => VV y) 2 MeasureTheory.Measure.count
      ≤ (K₀ Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ 0 l₂ k₁ k₂)
        * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    have heq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C₀ a 0 l₂ k₁ k₂ n then
          Work.KMTAreas.A7.Tle ρ 0 (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t)
            (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max k₁ k₂))) 0 f)
            x
          else 0)) = fun y : ℤ => VV y := by
      funext x
      rw [hVV]
      congr 1
      funext n
      simp only [Work.KMTPlan.A6.mdlSliceF, Work.KMTPlan.A6.lcL, ite_apply, Pi.zero_apply]
    rw [heq] at hGG
    exact hGG
  -- (1) clipping the gate away costs a factor `2`
  have hclip : ∀ X : ℝ,
      Work.KMTPlan.A6.VrLiftDataP (R : ℝ) (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
        (fun n θ => Work.KMTPlan.A6Clean.packetFamF ρ a 0 l₂ k₁ k₂ W n X θ)
      ≤ 2 * Work.KMTPlan.A6.VrLiftDataP (R : ℝ) (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
        (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
          FourierTransformInv.fourierInv (g n 0) X) := by
    intro X
    rw [two_mul]
    have hfun : (fun n θ => Work.KMTPlan.A6Clean.packetFamF ρ a 0 l₂ k₁ k₂ W n X θ)
        = fun (n : ℕ) (θ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
            if Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
                (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂) (Nat.floor (a n)) then
              FourierTransformInv.fourierInv (g n 0) X else 0 := by
      funext n θ
      rw [packetFamF_zero_apply]
      by_cases hγ : Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
          (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂) (Nat.floor (a n))
      · simp only [hγ, if_true]
        exact hgpt n 0 X
      · simp only [hγ, if_false]
    rw [hfun]
    exact Work.A6HighLow.VrLiftClip (Q := Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
      (R := (R : ℝ)) hR1
      (fun n => Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
        (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂) (Nat.floor (a n))) hγmono
      (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
        FourierTransformInv.fourierInv (g n 0) X)
  -- (2) the lattice sampling of the band-limited amplitudes
  have hsamp := hSamp (Q := Work.KMTAreas.A7.arithQ ρ (max 0 l₂)) (R := (R : ℝ)) hR1
    (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) => g n 0)
    (fun n θ => hgint n 0) (fun n θ ξ hξ => hgsupp n 0 ξ hξ)
  have hsamp' : ∫⁻ X : ℝ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
        (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
        (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
          FourierTransformInv.fourierInv (g n 0) X)) ^ (2 : ℕ)
      ≤ ENNReal.ofReal Cs * ∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
          (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
          (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
            W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℕ) := by
    refine hsamp.trans (le_of_eq ?_)
    refine congrArg (fun t => ENNReal.ofReal Cs * t) (tsum_congr fun m => ?_)
    rw [show (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
          FourierTransformInv.fourierInv (g n 0) ((m : ℤ) : ℝ))
        = fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
          W n 0 ((m : ℤ) : ℝ) from by
      funext n θ
      exact (hgpt n 0 ((m : ℤ) : ℝ)).symm]
  have hstep1 : ∫⁻ X : ℝ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
        (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
        (fun n θ => Work.KMTPlan.A6Clean.packetFamF ρ a 0 l₂ k₁ k₂ W n X θ)) ^ (2 : ℕ)
      ≤ ENNReal.ofReal (4 * Cs) * ∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
          (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
          (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
            W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℕ) := by
    have h1 : ∫⁻ X : ℝ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
          (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
          (fun n θ => Work.KMTPlan.A6Clean.packetFamF ρ a 0 l₂ k₁ k₂ W n X θ)) ^ (2 : ℕ)
        ≤ ∫⁻ X : ℝ, (2 * Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
            (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
            (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
              FourierTransformInv.fourierInv (g n 0) X)) ^ (2 : ℕ) :=
      lintegral_mono fun X => pow_le_pow_left₀ (n := 2) bot_le (hclip X)
    have h2 : ∫⁻ X : ℝ, (2 * Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
          (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
          (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
            FourierTransformInv.fourierInv (g n 0) X)) ^ (2 : ℕ)
        = 4 * ∫⁻ X : ℝ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
            (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
            (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
              FourierTransformInv.fourierInv (g n 0) X)) ^ (2 : ℕ) := by
      rw [show (fun X : ℝ => (2 * Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
              (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
              (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
                FourierTransformInv.fourierInv (g n 0) X)) ^ (2 : ℕ))
          = fun X : ℝ => (4 : ENNReal) * (Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
              (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
              (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
                FourierTransformInv.fourierInv (g n 0) X)) ^ (2 : ℕ) from by
        funext X
        rw [mul_pow]
        norm_num]
      rw [MeasureTheory.lintegral_const_mul' 4 _ (by norm_num)]
    have h4 : (4 : ENNReal) * (ENNReal.ofReal Cs * ∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP
            (R : ℝ) (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
            (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
              W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℕ))
        = ENNReal.ofReal (4 * Cs) * ∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
            (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
            (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
              W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℕ) := by
      rw [show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) from by norm_num, ← mul_assoc,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
    exact h1.trans (h2.le.trans ((mul_le_mul_right hsamp' 4).trans h4.le))
  -- (3) the `θ`-constant family and Young's inequality for the window convolution
  have hs1 : (∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
        (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
        (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
          W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℕ))
      ≤ ∑' m : ℤ, (2 * PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℕ) :=
    ENNReal.tsum_le_tsum fun m =>
      pow_le_pow_left₀ (n := 2) bot_le
        (VrLiftConstVarNorm_local R hR1' (fun n : ℕ => W n 0 ((m : ℤ) : ℝ)))
  have hs2 : (∑' m : ℤ, (2 * PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℕ))
      = 4 * (∑' m : ℤ, (PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℕ)) := by
    have h2 : ∀ m : ℤ, (2 * PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℕ)
        = (4 : ENNReal) * (PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℕ) := by
      intro m
      rw [mul_pow]
      norm_num
    rw [tsum_congr h2, ENNReal.tsum_mul_left]
  have hs3 : (∑' m : ℤ, (PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℕ))
      = (MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => W n 0 ((y : ℤ) : ℝ))) 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    have h3 : ∀ m : ℤ, (PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℕ)
        = (PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℝ) := by
      intro m
      rw [← ENNReal.rpow_natCast]
      norm_num
    rw [show (∑' m : ℤ, (PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℕ))
        = ∑' m : ℤ, (PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ => W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℝ) from tsum_congr h3]
    rw [tsum_pow_eq_eLpNorm_pow (p := 2) (by norm_num)
      (fun m : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => W n 0 ((m : ℤ) : ℝ)))]
    rw [show (ENNReal.ofReal 2 : ENNReal) = 2 from by norm_num]
    exact ENNReal.rpow_natCast _ 2
  have hs4 : MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm R
        (fun n : ℕ => W n 0 ((y : ℤ) : ℝ))) 2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal Mw * MeasureTheory.eLpNorm (fun y : ℤ => VV y) 2
          MeasureTheory.Measure.count := by
    have hfun : (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => W n 0 ((y : ℤ) : ℝ)))
        = fun y : ℤ => PointwiseErgodicTheorems.variationalNorm R (fun n : ℕ =>
            Work.KMTAreas.A7.winConvR (Work.KMTAreas.A7.mStarF
                (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂)))
              (Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n) y) := by
      funext y
      congr 1
      funext n
      exact hWs0 n y
    rw [hfun]
    have hmass : (∑' j : ℤ, ENNReal.ofReal ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF
        (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂))) j‖) ≤ ENNReal.ofReal Mw := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => norm_nonneg _)
        (hMw (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂))).1]
      exact ENNReal.ofReal_le_ofReal
        (hMw (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂))).2
    have h := VarNormWinConvLe_local (r := R) hR1'
      (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂)))
      (fun n : ℕ => Work.KMTPlan.A6.mdlSliceF ρ C₀ a 0 l₂ k₁ k₂ j₁ t f n)
      hMw0 (by norm_num : (1 : ℝ) ≤ 2) hmass
    rw [show (ENNReal.ofReal (2 : ℝ) : ENNReal) = 2 from by norm_num] at h
    simpa only [hVV] using h
  have hsumStep : (∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
        (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
        (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
          W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℕ))
      ≤ 4 * (ENNReal.ofReal Mw * MeasureTheory.eLpNorm (fun y : ℤ => VV y) 2
          MeasureTheory.Measure.count) ^ (2 : ℕ) := by
    refine (hs1.trans (le_of_eq (hs2.trans (congrArg (fun t => (4 : ENNReal) * t) hs3)))).trans ?_
    refine mul_le_mul_right ?_ 4
    exact pow_le_pow_left₀ (n := 2) bot_le hs4
  -- (4) the constant bookkeeping
  have hle_const : 16 * Cs * Mw ^ 2 ≤ ((c₀ : ℝ)) ^ 2 := by
    have h1 : 16 * Cs * Mw ^ 2 ≤ 16 * Cs * (max Mw 1) ^ 2 := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h2 : Mw ≤ max Mw 1 := le_max_left _ _
      have h3 : (0 : ℝ) ≤ max Mw 1 := le_trans hMw0 h2
      nlinarith
    have h2 : 16 * Cs * (max Mw 1) ^ 2 ≤ (c₀ : ℝ) := by
      have hceil := Nat.le_ceil (16 * Cs * (max Mw 1) ^ 2)
      show 16 * Cs * (max Mw 1) ^ 2
        ≤ ((⟨Nat.ceil (16 * Cs * (max Mw 1) ^ 2) + 1, by positivity⟩ : NNReal) : ℝ)
      push_cast
      linarith
    have h3 : (1 : ℝ) ≤ (c₀ : ℝ) := by
      show (1 : ℝ) ≤ ((⟨Nat.ceil (16 * Cs * (max Mw 1) ^ 2) + 1, by positivity⟩ : NNReal) : ℝ)
      push_cast
      have : (0 : ℝ) ≤ (Nat.ceil (16 * Cs * (max Mw 1) ^ 2) : ℝ) := by positivity
      linarith
    nlinarith [h1, h2, h3]
  have hc₀ : (16 : ENNReal) * ENNReal.ofReal Cs * (ENNReal.ofReal Mw) ^ (2 : ℕ)
      ≤ (c₀ : ENNReal) ^ (2 : ℕ) := by
    have hprod : (16 : ENNReal) * ENNReal.ofReal Cs * (ENNReal.ofReal Mw) ^ (2 : ℕ)
        = ENNReal.ofReal (16 * Cs * Mw ^ 2) := by
      rw [show (16 : ENNReal) = ENNReal.ofReal (16 : ℝ) from by norm_num,
        ← ENNReal.ofReal_pow hMw0,
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
        ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 16 * Cs)]
    rw [hprod, show (c₀ : ENNReal) ^ (2 : ℕ) = ENNReal.ofReal ((c₀ : ℝ) ^ 2) from by
      rw [← ENNReal.ofReal_coe_nnreal (p := c₀),
        ← ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ (c₀ : ℝ))]]
    exact ENNReal.ofReal_le_ofReal hle_const
  -- (5) the final chain
  have hXv : (MeasureTheory.eLpNorm (fun y : ℤ => VV y) 2 MeasureTheory.Measure.count) ^ (2 : ℕ)
      ≤ ((K₀ Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ 0 l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (n := 2) bot_le hVV_bound
  refine hstep1.trans ?_
  calc ENNReal.ofReal (4 * Cs) * ∑' m : ℤ, (Work.KMTPlan.A6.VrLiftDataP (R : ℝ)
          (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))
          (fun (n : ℕ) (_ : ZMod (Work.KMTAreas.A7.arithQ ρ (max 0 l₂))) =>
            W n 0 ((m : ℤ) : ℝ))) ^ (2 : ℕ)
      ≤ ENNReal.ofReal (4 * Cs) * (4 * (ENNReal.ofReal Mw * MeasureTheory.eLpNorm
          (fun y : ℤ => VV y) 2 MeasureTheory.Measure.count) ^ (2 : ℕ)) :=
        mul_le_mul_right hsumStep _
    _ = ENNReal.ofReal (4 * Cs) * (4 : ENNReal)
          * (ENNReal.ofReal Mw * MeasureTheory.eLpNorm (fun y : ℤ => VV y) 2
              MeasureTheory.Measure.count) ^ (2 : ℕ) := by ring
    _ = (ENNReal.ofReal (4 * Cs) * (4 : ENNReal) * (ENNReal.ofReal Mw) ^ (2 : ℕ))
          * (MeasureTheory.eLpNorm (fun y : ℤ => VV y) 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
        rw [mul_pow]; ring
    _ ≤ (c₀ : ENNReal) ^ (2 : ℕ)
          * (MeasureTheory.eLpNorm (fun y : ℤ => VV y) 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
        refine mul_le_mul_left ?_ _
        rw [show ENNReal.ofReal (4 * Cs) * (4 : ENNReal)
            = (16 : ENNReal) * ENNReal.ofReal Cs from by
          rw [show (16 : ENNReal) = ENNReal.ofReal (16 : ℝ) from by norm_num,
            show (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) from by norm_num,
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * Cs),
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)]
          ring_nf]
        exact hc₀
    _ ≤ (c₀ : ENNReal) ^ (2 : ℕ) * (((K₀ Λ : ENNReal)
          * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ 0 l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ)) :=
        mul_le_mul_right hXv _
    _ = ((K₀ Λ : ENNReal) * (c₀ : ENNReal)) ^ (2 : ℕ)
          * (ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A₀ ρ 0 l₂ k₁ k₂)) ^ (2 : ℕ)
          * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) ^ (2 : ℕ) := by
        ring

end

end Work.A6Clean
