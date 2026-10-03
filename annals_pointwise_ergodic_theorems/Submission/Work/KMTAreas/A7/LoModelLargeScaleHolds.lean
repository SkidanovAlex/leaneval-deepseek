/-
# The §8 large-scale estimate for the level-`0` model tuple (Area A7)

Target: `Work.KMTAreas.A7.LoModelLargeScaleHolds`, i.e. the `Prop`
`Work.KMTAreas.A7.LoModelStatement P p₁ p₂` of `Submission/Work/KMTAreas/A7/LoDefs.lean`.

## The object

`loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 1_{loGuard}(n) ∫_{1/2}^1 A_n(t,x)·B_n(t,x) dt`
with the two *linear* families (`N = ⌊a n⌋`)

* `A_n(t,·) = Tle ρ 0 (varphiNt N k₁ t) f`  (the paper's `φ_{N,t}`, arithmetic height `0`),
* `B_n(t,·) = Tle ρ 0 (varphitildeNt P d N k₂ t) g`  (the paper's `φ̃_{N,t}`),

and the guard `loGuard` (the index set `I^{…}`, the large-scale cut `splitCut ρ L < N` and the main
regime `k + 2u ≤ Log N`).

## The reduction

For each `t ∈ [1/2,1]`, the variational product rule, Hölder in `x` and the two *linear* variational
estimates `LoFLinVarClipped` (`f`-side, from the proved `LoLinVar`) and `LoGLinVarClipped`
(`g`-side) bound the `t`-integrand; Minkowski for the `t`-integral
(`variationalNorm_intervalIntegral_eLpNorm_le'`) and `lossWeight 4 · lossWeight 4 = lossWeight 8`
finish the proof.

The `g`-side estimate is assembled from the proved narrow parts (`LoGFareyPartBound`, `k₂ ≥ 1`;
`LoGFareyDiffPartBound`, `k₂ = 0`), the proved unmodulated low-pass `A7G.plainBumpVarG` (via
`LoGLowpassClipped`) and the delegated non-narrow scales `Work.KMTAreas.A7.LoGBadPartVar`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LoLinVar
import Submission.Work.KMTAreas.A7.LoGFareyPartBound
import Submission.Work.KMTAreas.A7.LoGFareyDiffPartBound
import Submission.Work.KMTAreas.A7.LoGBadPartVar
import Submission.Work.KMTAreas.A7G.plainBumpVarG
import Submission.Work.KMTAreas.A7.variationalNorm_clip_le
import Submission.Work.KMTAreas.A7.LoMixedAux
import Submission.Work.KMTAreas.A7.SmallModelVar
import Submission.Work.KMTAreas.A7.iwConv_varphiNt_bounded_measurable
import Submission.Work.KMTAreas.A7.iwConv_varphitildeNt_bounded_measurable
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTContract

/-! ## §1.  Elementary helpers -/

/-- A `Λ`-lacunary sequence with all terms `≥ 1` is monotone. -/
theorem monotone_of_lacunary_aux {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h2 : Λ < a (n + 1) / a n := ha n
  have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
  have h3 : a n ≤ Λ * a n := by
    simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
  exact le_trans h3 h1.le

/-- **Clipping at a tail.**  If `P` is the tail `{n | m ≤ n}`, then clipping a sequence at `P`
costs at most a factor `2` (and a shift by `m`). -/
theorem variationalNorm_clip_tail_le (r : NNReal) (hr : 1 ≤ r) (m : ℕ) (u : ℕ → ℂ)
    {P : ℕ → Prop} [DecidablePred P] (hP : ∀ n, P n ↔ m ≤ n) :
    PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => if P n then u n else 0)
      ≤ PointwiseErgodicTheorems.variationalNorm r (fun j : ℕ => u (j + m))
        + PointwiseErgodicTheorems.variationalNorm r (fun j : ℕ => u (j + m)) := by
  have hfun : (fun n : ℕ => if P n then u n else 0)
      = (fun n : ℕ => if m ≤ n then u n else 0) := by
    funext n
    by_cases h : P n
    · rw [if_pos h, if_pos ((hP n).mp h)]
    · rw [if_neg h, if_neg (fun hc => h ((hP n).mpr hc))]
  rw [hfun]
  exact variationalNorm_clip_le r hr u m

/-- The `lmaxR` bounds in the `l₂`, `k₂` slots (the `l₁`, `k₁` cases are
`natCast_le_lmaxR_left`, `natCast_le_lmaxR_k₁` of `lacunaryBumpAssembly`). -/
theorem natCast_le_lmaxR_l₂' (l₁ l₂ k₁ k₂ : ℕ) : (l₂ : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
  rw [lmaxR, Work.Analysis.EndVar.lmax]
  have h : (l₂ : ℤ) ≤ max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  exact_mod_cast h

theorem natCast_le_lmaxR_k₂' (l₁ l₂ k₁ k₂ : ℕ) : (k₂ : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := by
  rw [lmaxR, Work.Analysis.EndVar.lmax]
  have h : (k₂ : ℤ) ≤ max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  exact_mod_cast h

theorem lmaxR_nonneg' (l₁ l₂ k₁ k₂ : ℕ) : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ :=
  le_trans (Nat.cast_nonneg k₁) (natCast_le_lmaxR_k₁ l₁ l₂ k₁ k₂)

/-- The loss weight, with the exponent written as an `rpow`. -/
theorem lossWeight_eq (c ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    lossWeight c ρ l₁ l₂ k₁ k₂
      = (1 + lmaxR l₁ l₂ k₁ k₂) ^ c * (2 : ℝ) ^ (c * ρ * lmaxR l₁ l₂ k₁ k₂) := rfl

/-- One is a lower bound for the loss weight (for positive exponents). -/
theorem one_le_lossWeight_lo (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    (1 : ℝ) ≤ lossWeight c ρ l₁ l₂ k₁ k₂ := by
  rw [lossWeight_eq]
  have hL0 : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := lmaxR_nonneg' l₁ l₂ k₁ k₂
  have h1 : (1 : ℝ) ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := by linarith
  have h2 : (1 : ℝ) ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ c := Real.one_le_rpow h1 hc.le
  have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (c * ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (mul_nonneg hc.le hρ.le) hL0)
  calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
    _ ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ c * (2 : ℝ) ^ (c * ρ * lmaxR l₁ l₂ k₁ k₂) :=
        mul_le_mul h2 h3 (by norm_num) (by positivity)

/-- The loss weight is positive. -/
theorem lossWeight_pos (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    0 < lossWeight c ρ l₁ l₂ k₁ k₂ := by
  rw [lossWeight_eq]
  have h1 : (0 : ℝ) < 1 + lmaxR l₁ l₂ k₁ k₂ := by linarith [lmaxR_nonneg' l₁ l₂ k₁ k₂]
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (c * ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.rpow_pos_of_pos (by norm_num) _
  exact mul_pos (Real.rpow_pos_of_pos h1 c) h2

/-- `(1 + k₁)^2` is dominated by the loss weight `lossWeight 4 ρ l₁ l₂ k₁ k₂`. -/
theorem sq_le_lossWeight4 (ρ : ℝ) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    (1 + (k₁ : ℝ)) ^ 2 ≤ lossWeight 4 ρ l₁ l₂ k₁ k₂ := by
  have hL0 : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := lmaxR_nonneg' l₁ l₂ k₁ k₂
  have hk1 : (k₁ : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := natCast_le_lmaxR_k₁ l₁ l₂ k₁ k₂
  have h1L : (1 : ℝ) ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := by linarith
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) hρ) hL0)
  rw [lossWeight_eq,
    show (1 + lmaxR l₁ l₂ k₁ k₂) ^ (4:ℝ) = (1 + lmaxR l₁ l₂ k₁ k₂) ^ (4:ℕ) from by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) from by norm_num, Real.rpow_natCast]]
  calc (1 + (k₁ : ℝ)) ^ 2
      ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ 2 :=
        pow_le_pow_left₀ (by linarith) (by linarith : 1 + (k₁ : ℝ) ≤ 1 + lmaxR l₁ l₂ k₁ k₂) 2
    _ ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ 4 := pow_le_pow_right₀ h1L (by norm_num)
    _ ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ 4 * (2 : ℝ) ^ (4 * ρ * lmaxR l₁ l₂ k₁ k₂) :=
        le_mul_of_one_le_right (by positivity) htwo

/-- `(1 + l₂)(1 + d k₂)` is dominated by `(1+d)` times `lossWeight 4 ρ l₁ l₂ k₁ k₂`. -/
theorem losses_le_lossWeight4 (d : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    (1 + (l₂ : ℝ)) * (1 + (d : ℝ) * (k₂ : ℝ))
      ≤ (1 + (d : ℝ)) * lossWeight 4 ρ l₁ l₂ k₁ k₂ := by
  have hL0 : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := lmaxR_nonneg' l₁ l₂ k₁ k₂
  have hk2 : (k₂ : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := natCast_le_lmaxR_k₂' l₁ l₂ k₁ k₂
  have hl2 : (l₂ : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := natCast_le_lmaxR_l₂' l₁ l₂ k₁ k₂
  have h1L : (1 : ℝ) ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := by linarith
  have htwo : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * ρ * lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) hρ) hL0)
  have hx2 : (1 + (l₂ : ℝ)) ≤ 1 + lmaxR l₁ l₂ k₁ k₂ := by linarith
  have hx3 : (1 + (d : ℝ) * (k₂ : ℝ)) ≤ (1 + (d : ℝ)) * (1 + lmaxR l₁ l₂ k₁ k₂) := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    have h3 : (d : ℝ) * (k₂ : ℝ) ≤ (d : ℝ) * (1 + lmaxR l₁ l₂ k₁ k₂) :=
      mul_le_mul_of_nonneg_left (by linarith) hd0
    nlinarith [h3]
  rw [lossWeight_eq,
    show (1 + lmaxR l₁ l₂ k₁ k₂) ^ (4:ℝ) = (1 + lmaxR l₁ l₂ k₁ k₂) ^ (4:ℕ) from by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) from by norm_num, Real.rpow_natCast]]
  calc (1 + (l₂ : ℝ)) * (1 + (d : ℝ) * (k₂ : ℝ))
      ≤ (1 + lmaxR l₁ l₂ k₁ k₂) * ((1 + (d : ℝ)) * (1 + lmaxR l₁ l₂ k₁ k₂)) :=
        mul_le_mul hx2 hx3 (by positivity) (by linarith)
    _ = (1 + (d : ℝ)) * ((1 + lmaxR l₁ l₂ k₁ k₂) * (1 + lmaxR l₁ l₂ k₁ k₂)) := by ring
    _ ≤ (1 + (d : ℝ)) * ((1 + lmaxR l₁ l₂ k₁ k₂) ^ (4:ℕ) *
          (2 : ℝ) ^ (4 * ρ * lmaxR l₁ l₂ k₁ k₂)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc (1 + lmaxR l₁ l₂ k₁ k₂) * (1 + lmaxR l₁ l₂ k₁ k₂)
            = (1 + lmaxR l₁ l₂ k₁ k₂) ^ 2 := by ring
          _ ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ 4 := pow_le_pow_right₀ h1L (by norm_num)
          _ ≤ (1 + lmaxR l₁ l₂ k₁ k₂) ^ 4 * (2 : ℝ) ^ (4 * ρ * lmaxR l₁ l₂ k₁ k₂) :=
              le_mul_of_one_le_right (by positivity) htwo

/-- `lossWeight 4 · lossWeight 4 = lossWeight 8`. -/
theorem lossWeight4_mul_self (ρ : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    lossWeight 4 ρ l₁ l₂ k₁ k₂ * lossWeight 4 ρ l₁ l₂ k₁ k₂
      = lossWeight 8 ρ l₁ l₂ k₁ k₂ := by
  have hL0 : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ k₂ := lmaxR_nonneg' l₁ l₂ k₁ k₂
  rw [lossWeight_eq, lossWeight_eq 8 ρ l₁ l₂ k₁ k₂]
  set L : ℝ := lmaxR l₁ l₂ k₁ k₂ with hL
  have hL0' : 0 ≤ L := by rw [hL]; exact hL0
  have h2 : ((2 : ℝ) ^ (4 * ρ * L)) * ((2 : ℝ) ^ (4 * ρ * L)) = (2 : ℝ) ^ (8 * ρ * L) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  have h1 : (1 + L) ^ (4:ℝ) * (1 + L) ^ (4:ℝ) = (1 + L) ^ (8:ℝ) := by
    rw [← Real.rpow_add (by linarith : (0:ℝ) < 1 + L)]
    norm_num
  calc (1 + L) ^ (4:ℝ) * (2 : ℝ) ^ (4 * ρ * L) * ((1 + L) ^ (4:ℝ) * (2 : ℝ) ^ (4 * ρ * L))
      = ((1 + L) ^ (4:ℝ) * (1 + L) ^ (4:ℝ)) *
          (((2 : ℝ) ^ (4 * ρ * L)) * ((2 : ℝ) ^ (4 * ρ * L))) := by ring
    _ = (1 + L) ^ (8:ℝ) * (2 : ℝ) ^ (8 * ρ * L) := by rw [h1, h2]

/-! ## §2.  The `f`-side clipped linear variational estimate -/

/-- **The `core`-clipped `f`-side linear variational estimate** (the paper's `(lin-1)` at
arithmetic height `0`), from `Work.KMTAreas.A7.LoLinVar` by the tail-clipping of the guard and the
shift of the lacunary sequence. -/
theorem LoFLinVarClipped (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p₁ : ENNReal) (hp₁ : 1 < p₁)
    (htp₁ : p₁ < ⊤) (r : NNReal) (hr : 2 < r) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (C₀ l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
      (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
          then Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
        p₁ MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * lossWeight 4 ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count := by
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  obtain ⟨Clin, hClin⟩ := LoLinVar ρ hρ hρ1 p₁ hp₁ htp₁ r hr Λ hΛ
  refine ⟨2 * (Clin : ℝ) + 1, by positivity, ?_⟩
  intro a ha ha1 C₀ l₁ l₂ k₁ k₂ t ht f
  have hamono : Monotone a := monotone_of_lacunary_aux hΛ ha ha1
  by_cases hex : ∃ n : ℕ, core ρ C₀ l₁ l₂ k₁ k₂ a n
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ n : ℕ, core ρ C₀ l₁ l₂ k₁ k₂ a n ↔ m ≤ n := by
      refine ⟨Nat.find hex, fun n => ⟨fun h => ?_, fun h => ?_⟩⟩
      · by_contra hcon
        rw [not_le] at hcon
        exact Nat.find_min hex hcon h
      · exact core_mono hamono h (Nat.find_spec hex)
    have hclip : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
          then Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x else 0)
        ≤ 2 * PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Tle ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f x) := by
      intro x
      have h1 := variationalNorm_clip_tail_le (r := r) hr1 m
        (fun n : ℕ => Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
        (P := fun n : ℕ => core ρ C₀ l₁ l₂ k₁ k₂ a n) hm
      refine h1.trans (le_of_eq ?_)
      rw [two_mul]
    have hstep : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
          then Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
        p₁ MeasureTheory.Measure.count
        ≤ 2 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Tle ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f x))
            p₁ MeasureTheory.Measure.count :=
      MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm) (c := 2)
        (Filter.Eventually.of_forall (fun x => by
          rw [enorm_eq_self, enorm_eq_self]; exact hclip x)) p₁
    have hshift : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Tle ρ 0 (varphiNt (Nat.floor (a (j + m))) k₁ t) f x))
            p₁ MeasureTheory.Measure.count
        ≤ (Clin : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count := by
      refine hClin (fun j : ℕ => a (j + m)) ?_ (fun j => ha1 (j + m)) k₁ ?_ t ht f
      · intro j
        have h := ha (j + m)
        have hidx : j + 1 + m = (j + m) + 1 := by omega
        show Λ < a (j + 1 + m) / a (j + m)
        rw [hidx]; exact h
      · intro j
        exact two_pow_le_floor_of_core ((hm (j + m)).mpr (Nat.le_add_left m j))
    have hmul : (1 + (k₁ : ℝ)) ^ 2 ≤ lossWeight 4 ρ l₁ l₂ k₁ k₂ :=
      sq_le_lossWeight4 ρ hρ.le l₁ l₂ k₁ k₂
    refine hstep.trans ?_
    refine (mul_le_mul' le_rfl hshift).trans ?_
    -- `2 * (↑Clin * ofReal X * ‖f‖) ≤ ofReal ((2 * ↑Clin + 1) * lw4) * ‖f‖`
    calc (2 : ENNReal) * ((Clin : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count)
        = ENNReal.ofReal (2 * ((Clin : ℝ) * (1 + (k₁ : ℝ)) ^ 2)) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count := by
          have hnum : (2 : ENNReal) = ENNReal.ofReal 2 := (ENNReal.ofReal_natCast 2).symm
          have hcoe : (Clin : ENNReal) = ENNReal.ofReal (Clin : ℝ) :=
            ENNReal.ofReal_coe_nnreal.symm
          rw [hnum, hcoe]
          rw [← mul_assoc (ENNReal.ofReal 2) (ENNReal.ofReal (Clin : ℝ) *
                ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2))
              (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count)]
          rw [← mul_assoc (ENNReal.ofReal 2) (ENNReal.ofReal (Clin : ℝ))
              (ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2))]
          rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
          rw [← ENNReal.ofReal_mul (mul_nonneg (by norm_num) (by exact_mod_cast Clin.coe_nonneg))]
          congr 1
          rw [show (2 : ℝ) * (Clin : ℝ) * (1 + (k₁ : ℝ)) ^ 2
              = 2 * ((Clin : ℝ) * (1 + (k₁ : ℝ)) ^ 2) from by ring]
      _ ≤ ENNReal.ofReal ((2 * (Clin : ℝ) + 1) * lossWeight 4 ρ l₁ l₂ k₁ k₂) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          have hlw0 : 0 ≤ lossWeight 4 ρ l₁ l₂ k₁ k₂ :=
            (lossWeight_pos 4 ρ (by norm_num) hρ l₁ l₂ k₁ k₂).le
          have hcm : 2 * ((Clin : ℝ) * (1 + (k₁ : ℝ)) ^ 2)
              ≤ 2 * ((Clin : ℝ) * lossWeight 4 ρ l₁ l₂ k₁ k₂) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmul (by positivity)) (by norm_num)
          have hfin : 2 * ((Clin : ℝ) * lossWeight 4 ρ l₁ l₂ k₁ k₂)
              ≤ (2 * (Clin : ℝ) + 1) * lossWeight 4 ρ l₁ l₂ k₁ k₂ := by
            rw [show 2 * ((Clin : ℝ) * lossWeight 4 ρ l₁ l₂ k₁ k₂)
                = (2 * (Clin : ℝ)) * lossWeight 4 ρ l₁ l₂ k₁ k₂ from by ring]
            refine mul_le_mul_of_nonneg_right ?_ hlw0
            linarith
          exact hcm.trans hfin
  · have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
            then Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
        = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun _ : ℕ => (0 : ℂ)) := by
      funext x
      congr 1
      funext n
      rw [if_neg (fun hc => hex ⟨n, hc⟩)]
    rw [hzero, eLpNorm_variationalNorm_zero hr1 p₁]
    exact bot_le

/-! ## §3.  The `g`-side low-pass piece -/

/-- **The `core ∧ Farey`-clipped low-pass piece of the `g`-side at `k₂ = 0`**, from the PROVED
unmodulated low-pass estimate `Work.KMTAreas.A7G.plainBumpVarG` by the tail-clipping of the
`core ∧ Farey` predicate. -/
theorem LoGLowpassClipped (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (p : ENNReal) (hp : 1 < p) (htp : p < ⊤) (r : NNReal) (hr : 2 < r)
    (Λ : NNReal) (hΛ : 1 < Λ) (Cρc : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (C₀ l₁ l₂ k₁ : ℕ) (g : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ 0 (fun ξ : ℝ => if core ρ C₀ l₁ l₂ k₁ 0 a n ∧
            Farey Cρc ρ l₂ 0 a n
          then varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ else 0) g x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  obtain ⟨Clow, hClowpos, hClow⟩ :=
    Work.KMTAreas.A7G.plainBumpVarG P.natDegree (by omega) ρ Λ hΛ r hr p hp htp
  refine ⟨2 * Clow, by positivity, ?_⟩
  intro a ha ha1 C₀ l₁ l₂ k₁ g
  have hamono : Monotone a := monotone_of_lacunary_aux hΛ ha ha1
  set Q : ℕ → Prop := fun n => core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey Cρc ρ l₂ 0 a n with hQ
  have hQmono : ∀ n m : ℕ, n ≤ m → Q n → Q m := by
    intro n m hnm h
    exact ⟨core_mono hamono hnm h.1, Work.KMTAreas.A7LoLin.monotone_farey hamono hnm h.2⟩
  by_cases hex : ∃ n : ℕ, Q n
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ n : ℕ, Q n ↔ m ≤ n := by
      refine ⟨Nat.find hex, fun n => ⟨fun h => ?_, fun h => ?_⟩⟩
      · by_contra hcon
        rw [not_le] at hcon
        exact Nat.find_min hex hcon h
      · exact hQmono _ _ h (Nat.find_spec hex)
    have hclip : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ 0 (fun ξ : ℝ => if Q n
          then varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ else 0) g x)
        ≤ 2 * PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Tle ρ 0 (varphitildeN P.natDegree (Nat.floor (a (j + m))) 0) g x) := by
      intro x
      have hEq : (fun n : ℕ => Tle ρ 0 (fun ξ : ℝ => if Q n
            then varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ else 0) g x)
          = (fun n : ℕ => if Q n
              then Tle ρ 0 (varphitildeN P.natDegree (Nat.floor (a n)) 0) g x else 0) := by
        funext n
        exact congrFun (Tle_ite ρ 0 (Q n)
          (φ := varphitildeN P.natDegree (Nat.floor (a n)) 0) (f := g)) x
      rw [hEq]
      have h1 := variationalNorm_clip_tail_le (r := r) hr1 m
        (fun n : ℕ => Tle ρ 0 (varphitildeN P.natDegree (Nat.floor (a n)) 0) g x)
        (P := Q) hm
      refine h1.trans (le_of_eq ?_)
      rw [two_mul]
    have hstep : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => Tle ρ 0 (fun ξ : ℝ => if Q n
          then varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ else 0) g x))
        p MeasureTheory.Measure.count
        ≤ 2 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Tle ρ 0 (varphitildeN P.natDegree (Nat.floor (a (j + m))) 0) g x))
            p MeasureTheory.Measure.count :=
      MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm) (c := 2)
        (Filter.Eventually.of_forall (fun x => by
          rw [enorm_eq_self, enorm_eq_self]; exact hclip x)) p
    have hshift : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Tle ρ 0 (varphitildeN P.natDegree (Nat.floor (a (j + m))) 0) g x))
            p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal Clow * MeasureTheory.eLpNorm g p MeasureTheory.Measure.count := by
      refine hClow (fun j : ℕ => a (j + m)) ?_ (fun j => ha1 (j + m)) g
      intro j
      have h := ha (j + m)
      have hidx : j + 1 + m = (j + m) + 1 := by omega
      show Λ < a (j + 1 + m) / a (j + m)
      rw [hidx]; exact h
    refine hstep.trans ?_
    refine (mul_le_mul' le_rfl hshift).trans ?_
    rw [show (2 : ENNReal) = ENNReal.ofReal 2 from (ENNReal.ofReal_natCast 2).symm,
      ← mul_assoc (ENNReal.ofReal 2) (ENNReal.ofReal Clow)
        (MeasureTheory.eLpNorm g p MeasureTheory.Measure.count),
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  · have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ 0 (fun ξ : ℝ => if Q n
            then varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ else 0) g x))
        = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun _ : ℕ => (0 : ℂ)) := by
      funext x
      congr 1
      funext n
      have h : ¬ Q n := fun hc => hex ⟨n, hc⟩
      rw [congrFun (Tle_ite ρ 0 (Q n)
        (φ := varphitildeN P.natDegree (Nat.floor (a n)) 0) (f := g)) x, if_neg h]
    rw [hzero, eLpNorm_variationalNorm_zero hr1 p]
    exact bot_le

/-- Swapping the middle factors: `(a * b) * (c * d) = (a * c) * (b * d)` in `ℝ≥0∞`. -/
theorem ennreal_mul_swap (a b c d : ENNReal) : (a * b) * (c * d) = (a * c) * (b * d) := by
  ac_rfl


/-- **The bottom-height split of the `g`-side bump.**  For a bounded input `g`, the multiplier of
the modulated bump at `k₂ = 0` splits into the unmodulated bump and the low-frequency difference. -/
theorem Tle_varphitildeNt_zero_split (P : Polynomial ℤ) (ρ : ℝ) (N : ℕ) (t : ℝ)
    {g : ℤ → ℂ} {B : ℝ} (hg : ∀ m : ℤ, ‖g m‖ ≤ B) :
    Tle ρ 0 (varphitildeNt P P.natDegree N 0 t) g
      = Tle ρ 0 (varphitildeN P.natDegree N 0) g
        + Tle ρ 0 (fun ξ : ℝ => varphitildeNt P P.natDegree N 0 t ξ
            - varphitildeN P.natDegree N 0 ξ) g := by
  have hD : (fun ξ : ℝ => varphitildeNt P P.natDegree N 0 t ξ
        - varphitildeN P.natDegree N 0 ξ)
      = (fun ξ : ℝ => varphitildeN P.natDegree N 0 ξ *
          (ee (PevalR P ((N : ℝ) * t) * ξ) - 1)) := by
    funext ξ
    rw [show varphitildeNt P P.natDegree N 0 t ξ
        = varphitildeN P.natDegree N 0 ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
    ring
  have hsum : (varphitildeNt P P.natDegree N 0 t)
      = (fun ξ : ℝ => varphitildeN P.natDegree N 0 ξ)
        + (fun ξ : ℝ => varphitildeN P.natDegree N 0 ξ *
            (ee (PevalR P ((N : ℝ) * t) * ξ) - 1)) := by
    funext ξ
    simp only [Pi.add_apply]
    rw [show varphitildeNt P P.natDegree N 0 t ξ
        = varphitildeN P.natDegree N 0 ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
    ring
  rw [hD, hsum]
  refine Work.KMTAreas.A7LoLin.Tle_add_of_bounded ?_ ?_ hg
  · exact adm_of_bump (contDiff_varphitildeN P.natDegree N 0)
      (hasCompactSupport_varphitildeN P.natDegree N 0)
  · refine adm_of_bump ?_ ((hasCompactSupport_varphitildeN P.natDegree N 0).mul_right)
    exact (contDiff_varphitildeN P.natDegree N 0).mul
      ((contDiff_ee_const_mul 2 (PevalR P ((N : ℝ) * t))).sub contDiff_const)

set_option maxHeartbeats 32000000 in
/-- The triangle inequality for a sum of three variational families. -/
theorem eLpNorm_variationalNorm_add_three_le {r : NNReal} {p : ENNReal}
    {u v w : ℕ → ℤ → ℂ} (hr1 : 1 ≤ r) (hp : 1 ≤ p) (hpt : p ≠ ⊤) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => u n x + v n x + w n x)) p MeasureTheory.Measure.count
      ≤ (MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => u n x)) p MeasureTheory.Measure.count
          + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => v n x)) p MeasureTheory.Measure.count)
        + MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => w n x)) p MeasureTheory.Measure.count := by
  have hV : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => u n x + v n x + w n x)
      ≤ (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x)
          + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => v n x))
        + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x) := by
    intro x
    refine (variationalNorm_add_le hr1 _ _).trans ?_
    exact add_le_add_left
      (variationalNorm_add_le hr1 (fun n : ℕ => u n x) (fun n : ℕ => v n x)) _
  refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x + v n x + w n x))
    (g := fun x : ℤ =>
      (PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x)
        + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => v n x))
      + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => w n x))
    (fun x => by rw [enorm_eq_self, enorm_eq_self]; exact hV x)).trans ?_
  refine (eLpNorm_add_le_ennreal hp hpt (μ := MeasureTheory.Measure.count)).trans ?_
  exact add_le_add_left
    (eLpNorm_add_le_ennreal (u := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => u n x)) (v := fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => v n x)) hp hpt (μ := MeasureTheory.Measure.count)) _

/-! ## §4.  The `g`-side clipped linear variational estimate -/

/-- **The `g`-side clipped linear variational estimate** (the paper's `(lin-2)` at arithmetic
height `0`), assembled from the narrow parts (`LoGFareyPartBound` at `k₂ ≥ 1`,
`LoGFareyDiffPartBound` at `k₂ = 0`), the unmodulated low-pass `LoGLowpassClipped` and the
non-narrow scales (`Work.KMTAreas.A7.LoGBadPartVar`). -/
theorem LoGLinVarClipped (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρC : ρ ≤ 1 / (2 * (C₀ : ℝ)))
    (p₂ : ENNReal) (hp₂ : 1 < p₂) (htp₂ : p₂ < ⊤) (r : NNReal) (hr : 2 < r)
    (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
      (ha1 : ∀ n, 1 ≤ a n) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1)
      (g : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
          then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0))
        p₂ MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * lossWeight 4 ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  have hp1 : (1 : ENNReal) ≤ p₂ := hp₂.le
  -- the four analytic pieces
  obtain ⟨CρcM, hCρcM, KM, hKM, hM⟩ :=
    LoGFareyPartBound P P.natDegree hdeg le_rfl C₀ r hr ρ hρ hρ1 Λ hΛ p₂ hp₂ htp₂
  obtain ⟨CρcD, hCρcD, KD, hKD, hD⟩ :=
    LoGFareyDiffPartBound P P.natDegree hdeg le_rfl C₀ r hr ρ hρ hρ1 Λ hΛ p₂ hp₂ htp₂
  obtain ⟨ClowC, hClowCpos, hClowC⟩ :=
    LoGLowpassClipped P hdeg ρ hρ hρ1 p₂ hp₂ htp₂ r hr Λ hΛ CρcD
  obtain ⟨CbadM, hCbadM, hbadM⟩ :=
    LoGBadPartVar P hdeg C₀ hC₀ ρ hρ hρ1 hρC CρcM hCρcM Λ hΛ r hr p₂ hp₂ htp₂
  obtain ⟨CbadD, hCbadD, hbadD⟩ :=
    LoGBadPartVar P hdeg C₀ hC₀ ρ hρ hρ1 hρC CρcD hCρcD Λ hΛ r hr p₂ hp₂ htp₂
  -- the constant
  set S : ℝ := KM * (1 + (P.natDegree : ℝ)) + KD + ClowC + CbadM + CbadD + 1 with hS
  have hS0 : 0 < S := by
    rw [hS]
    have h1 : (0 : ℝ) ≤ KM * (1 + (P.natDegree : ℝ)) := mul_nonneg hKM.le (by positivity)
    linarith [hKD, hClowCpos, hCbadM, hCbadD]
  have hSn : (0 : ℝ) ≤ S := hS0.le
  refine ⟨S, hS0, ?_⟩
  intro a ha ha1 l₁ l₂ k₁ k₂ t ht g
  have hlw0 : 0 ≤ lossWeight 4 ρ l₁ l₂ k₁ k₂ :=
    (lossWeight_pos 4 ρ (by norm_num) hρ l₁ l₂ k₁ k₂).le
  have hlw1 : 1 ≤ lossWeight 4 ρ l₁ l₂ k₁ k₂ :=
    one_le_lossWeight_lo 4 ρ (by norm_num) hρ l₁ l₂ k₁ k₂
  rcases Nat.eq_zero_or_pos k₂ with hk0 | hkpos
  · -- ## case `k₂ = 0`
    subst hk0
    have hl₂ : (1 + (l₂ : ℝ)) ≤ lossWeight 4 ρ l₁ l₂ k₁ 0 := by
      have hL : (l₂ : ℝ) ≤ lmaxR l₁ l₂ k₁ 0 := natCast_le_lmaxR_l₂' l₁ l₂ k₁ 0
      have hL0 : (0 : ℝ) ≤ lmaxR l₁ l₂ k₁ 0 := lmaxR_nonneg' l₁ l₂ k₁ 0
      have h1 : (1 : ℝ) ≤ 1 + lmaxR l₁ l₂ k₁ 0 := by linarith
      have h2 : (1 + (l₂ : ℝ)) ≤ (1 + lmaxR l₁ l₂ k₁ 0) ^ (4 : ℝ) := by
        have hq : (1 + lmaxR l₁ l₂ k₁ 0) ^ (4 : ℝ) = (1 + lmaxR l₁ l₂ k₁ 0) ^ (4:ℕ) := by
          rw [show (4:ℝ) = ((4:ℕ):ℝ) from by norm_num, Real.rpow_natCast]
        rw [hq]
        calc (1 + (l₂ : ℝ)) ≤ (1 + lmaxR l₁ l₂ k₁ 0) ^ 1 := by
              rw [pow_one]; linarith
          _ ≤ (1 + lmaxR l₁ l₂ k₁ 0) ^ 4 := pow_le_pow_right₀ h1 (by norm_num)
      have h3 : (1 : ℝ) ≤ (2 : ℝ) ^ (4 * ρ * lmaxR l₁ l₂ k₁ 0) :=
        Real.one_le_rpow (by norm_num) (mul_nonneg (mul_nonneg (by norm_num) hρ.le) hL0)
      rw [lossWeight_eq]
      exact h2.trans (le_mul_of_one_le_right (Real.rpow_nonneg (by linarith) _) h3)
    have hlw0' : 0 ≤ lossWeight 4 ρ l₁ l₂ k₁ 0 :=
      (lossWeight_pos 4 ρ (by norm_num) hρ l₁ l₂ k₁ 0).le
    have hlw1' : 1 ≤ lossWeight 4 ρ l₁ l₂ k₁ 0 :=
      one_le_lossWeight_lo 4 ρ (by norm_num) hρ l₁ l₂ k₁ 0
    -- the combined constant of the three pieces
    have hcomb3 : ENNReal.ofReal ClowC + ENNReal.ofReal (KD * (1 + (l₂ : ℝ)))
        + ENNReal.ofReal CbadD ≤ ENNReal.ofReal (S * lossWeight 4 ρ l₁ l₂ k₁ 0) := by
      rw [← ENNReal.ofReal_add hClowCpos.le (by positivity),
        ← ENNReal.ofReal_add (by positivity) hCbadD.le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hS3 : ClowC + KD + CbadD ≤ S := by
        rw [hS]
        have h1 : (0 : ℝ) ≤ KM * (1 + (P.natDegree : ℝ)) := mul_nonneg hKM.le (by positivity)
        linarith [hCbadM]
      have hA : ClowC ≤ ClowC * lossWeight 4 ρ l₁ l₂ k₁ 0 := by
        calc ClowC = ClowC * 1 := (mul_one _).symm
          _ ≤ ClowC * lossWeight 4 ρ l₁ l₂ k₁ 0 := mul_le_mul_of_nonneg_left hlw1' hClowCpos.le
      have hB : KD * (1 + (l₂ : ℝ)) ≤ KD * lossWeight 4 ρ l₁ l₂ k₁ 0 :=
        mul_le_mul_of_nonneg_left hl₂ hKD.le
      have hC : CbadD ≤ CbadD * lossWeight 4 ρ l₁ l₂ k₁ 0 := by
        calc CbadD = CbadD * 1 := (mul_one _).symm
          _ ≤ CbadD * lossWeight 4 ρ l₁ l₂ k₁ 0 := mul_le_mul_of_nonneg_left hlw1' hCbadD.le
      calc ClowC + KD * (1 + (l₂ : ℝ)) + CbadD
          ≤ ClowC * lossWeight 4 ρ l₁ l₂ k₁ 0 + KD * lossWeight 4 ρ l₁ l₂ k₁ 0
              + CbadD * lossWeight 4 ρ l₁ l₂ k₁ 0 := by linarith
        _ = (ClowC + KD + CbadD) * lossWeight 4 ρ l₁ l₂ k₁ 0 := by ring
        _ ≤ S * lossWeight 4 ρ l₁ l₂ k₁ 0 := mul_le_mul_of_nonneg_right hS3 hlw0'
    -- the three pieces, in the shape of the external lemmas
    have hb1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ 0 (fun ξ : ℝ => if core ρ C₀ l₁ l₂ k₁ 0 a n ∧
              Farey CρcD ρ l₂ 0 a n
            then varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ else 0) g x))
          p₂ MeasureTheory.Measure.count
        ≤ ENNReal.ofReal ClowC * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
      hClowC a ha ha1 C₀ l₁ l₂ k₁ g
    have hb2 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ 0 (fun ξ : ℝ => if core ρ C₀ l₁ l₂ k₁ 0 a n ∧
              Farey CρcD ρ l₂ 0 a n
            then varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
              - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ else 0) g x))
          p₂ MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (KD * (1 + (l₂ : ℝ))) * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
      hD 0 l₂ l₁ k₁ (Nat.zero_le _) t ht a ha ha1 g
    have hb3 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ ¬ Farey CρcD ρ l₂ 0 a n
            then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) g x else 0))
          p₂ MeasureTheory.Measure.count
        ≤ ENNReal.ofReal CbadD * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
      hbadD a ha ha1 l₁ l₂ k₁ 0 t ht g
    by_cases htop : MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count = ⊤
    · rw [htop, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hS0 (by
          rw [lossWeight_eq]; positivity)))]
      exact le_top
    · obtain ⟨Bg, hBg⟩ :=
        bounded_of_eLpNorm_count_lt_top (p := p₂) (ne_of_gt (lt_trans zero_lt_one hp₂))
          (lt_top_iff_ne_top.mpr htop)
      -- the split of the modulated family at `k₂ = 0`
      have hsplit0 : ∀ n : ℕ, Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) g
          = Tle ρ 0 (varphitildeN P.natDegree (Nat.floor (a n)) 0) g
            + Tle ρ 0 (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) g :=
        fun n => Tle_varphitildeNt_zero_split P ρ (Nat.floor (a n)) t hBg
      set F : ℕ → Prop := fun n => core ρ C₀ l₁ l₂ k₁ 0 a n ∧ Farey CρcD ρ l₂ 0 a n with hF
      set w0 : ℕ → ℤ → ℂ := fun n => Tle ρ 0
        (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) g with hw0
      set wu : ℕ → ℤ → ℂ := fun n => Tle ρ 0
        (varphitildeN P.natDegree (Nat.floor (a n)) 0) g with hwu
      set wd : ℕ → ℤ → ℂ := fun n => Tle ρ 0
        (fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
          - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) g with hwd
      set u0 : ℕ → ℤ → ℂ := fun n x => if core ρ C₀ l₁ l₂ k₁ 0 a n then w0 n x else 0 with hu0
      set u1 : ℕ → ℤ → ℂ := fun n x => if F n then wu n x else 0 with hu1
      set u2 : ℕ → ℤ → ℂ := fun n x => if F n then wd n x else 0 with hu2
      set u3 : ℕ → ℤ → ℂ := fun n x => if core ρ C₀ l₁ l₂ k₁ 0 a n ∧
        ¬ Farey CρcD ρ l₂ 0 a n then w0 n x else 0 with hu3
      have hpoint : ∀ n x, u0 n x = u1 n x + u2 n x + u3 n x := by
        intro n x
        by_cases hc : core ρ C₀ l₁ l₂ k₁ 0 a n
        · by_cases hf : Farey CρcD ρ l₂ 0 a n
          · have hF' : F n := ⟨hc, hf⟩
            have hnot : ¬ (core ρ C₀ l₁ l₂ k₁ 0 a n ∧ ¬ Farey CρcD ρ l₂ 0 a n) :=
              fun h => h.2 hf
            simp only [hu0, hu1, hu2, hu3, if_pos hc, if_pos hF', if_neg hnot, add_zero]
            exact congrFun (hsplit0 n) x
          · have hF' : ¬ F n := fun h => hf h.2
            have hc2 : core ρ C₀ l₁ l₂ k₁ 0 a n ∧ ¬ Farey CρcD ρ l₂ 0 a n := ⟨hc, hf⟩
            simp only [hu0, hu1, hu2, hu3, if_pos hc, if_neg hF', if_pos hc2]
            ring
        · have hF' : ¬ F n := fun h => hc h.1
          simp only [hu0, hu1, hu2, hu3, if_neg hc, if_neg hF',
            if_neg (fun h : core ρ C₀ l₁ l₂ k₁ 0 a n ∧ ¬ Farey CρcD ρ l₂ 0 a n => hc h.1)]
          ring
      have hconn : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => u0 n x))
          = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => u1 n x + u2 n x + u3 n x) := by
        funext x
        congr 1
        funext n
        exact hpoint n x
      have hE := eLpNorm_variationalNorm_add_three_le (u := u1) (v := u2) (w := u3)
        hr1 hp1 (ne_of_lt htp₂)
      rw [hconn]
      have hu1e : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u1 n x))
          = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Tle ρ 0
              (fun ξ : ℝ => if F n then varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ
                else 0) g x) := by
        funext x
        congr 1
        funext n
        rw [hu1]
        exact (congrFun (Tle_ite ρ 0 (F n)
          (φ := varphitildeN P.natDegree (Nat.floor (a n)) 0) (f := g)) x).symm
      have hu2e : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u2 n x))
          = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Tle ρ 0
              (fun ξ : ℝ => if F n then (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
                - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) else 0) g x) := by
        funext x
        congr 1
        funext n
        rw [hu2]
        exact (congrFun (Tle_ite ρ 0 (F n)
          (φ := fun ξ : ℝ => varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t ξ
            - varphitildeN P.natDegree (Nat.floor (a n)) 0 ξ) (f := g)) x).symm
      have hu3e : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u3 n x))
          = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
              if core ρ C₀ l₁ l₂ k₁ 0 a n ∧ ¬ Farey CρcD ρ l₂ 0 a n
                then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) 0 t) g x else 0) := by
        funext x
        rfl
      refine hE.trans ?_
      rw [hu1e, hu2e, hu3e]
      refine (add_le_add (add_le_add hb1 hb2) hb3).trans ?_
      calc ENNReal.ofReal ClowC * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count + ENNReal.ofReal (KD * (1 + (l₂ : ℝ))) * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
            + ENNReal.ofReal CbadD * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
          = (ENNReal.ofReal ClowC + ENNReal.ofReal (KD * (1 + (l₂ : ℝ)))
              + ENNReal.ofReal CbadD) * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
            rw [← add_mul, ← add_mul]
        _ ≤ ENNReal.ofReal (S * lossWeight 4 ρ l₁ l₂ k₁ 0) * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
            mul_le_mul' hcomb3 le_rfl
  · -- ## case `k₂ ≥ 1`
    have hX : (1 + (l₂ : ℝ)) * (1 + (P.natDegree : ℝ) * (k₂ : ℝ))
        ≤ (1 + (P.natDegree : ℝ)) * lossWeight 4 ρ l₁ l₂ k₁ k₂ :=
      losses_le_lossWeight4 P.natDegree ρ hρ.le l₁ l₂ k₁ k₂
    have hcomb : ENNReal.ofReal (KM * (1 + (l₂ : ℝ)) * (1 + (P.natDegree : ℝ) * (k₂ : ℝ)))
        + ENNReal.ofReal CbadM ≤ ENNReal.ofReal (S * lossWeight 4 ρ l₁ l₂ k₁ k₂) := by
      rw [← ENNReal.ofReal_add
        (mul_nonneg (mul_nonneg hKM.le (by positivity)) (by positivity)) hCbadM.le]
      refine ENNReal.ofReal_le_ofReal ?_
      have hS1 : KM * (1 + (P.natDegree : ℝ)) + CbadM ≤ S := by
        rw [hS]
        have h1 : (0 : ℝ) ≤ KD + ClowC + CbadD := by linarith [hKD, hClowCpos.le, hCbadD]
        linarith
      calc KM * (1 + (l₂ : ℝ)) * (1 + (P.natDegree : ℝ) * (k₂ : ℝ)) + CbadM
          = KM * ((1 + (l₂ : ℝ)) * (1 + (P.natDegree : ℝ) * (k₂ : ℝ))) + CbadM := by ring
        _ ≤ KM * ((1 + (P.natDegree : ℝ)) * lossWeight 4 ρ l₁ l₂ k₁ k₂)
              + CbadM * lossWeight 4 ρ l₁ l₂ k₁ k₂ := by
            refine add_le_add (mul_le_mul_of_nonneg_left hX hKM.le) ?_
            calc CbadM = CbadM * 1 := (mul_one _).symm
              _ ≤ CbadM * lossWeight 4 ρ l₁ l₂ k₁ k₂ :=
                  mul_le_mul_of_nonneg_left hlw1 hCbadM.le
        _ = (KM * (1 + (P.natDegree : ℝ)) + CbadM) * lossWeight 4 ρ l₁ l₂ k₁ k₂ := by ring
        _ ≤ S * lossWeight 4 ρ l₁ l₂ k₁ k₂ := mul_le_mul_of_nonneg_right hS1 hlw0
    have hb_far : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcM ρ l₂ k₂ a n
            then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0))
          p₂ MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (KM * (1 + (l₂ : ℝ)) * (1 + (P.natDegree : ℝ) * (k₂ : ℝ))) *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
      have h := hM k₂ hkpos 0 l₂ l₁ k₁ (Nat.zero_le _) t ht a ha ha1 g
      have heq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcM ρ l₂ k₂ a n
              then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0))
          = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Tle ρ 0 (fun ξ : ℝ =>
                if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcM ρ l₂ k₂ a n
                  then varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t ξ else 0) g x) := by
        funext x
        congr 1
        funext n
        exact (congrFun (Tle_ite ρ 0 (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcM ρ l₂ k₂ a n)
          (φ := varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) (f := g)) x).symm
      rw [heq]
      exact h
    have hb_bad : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey CρcM ρ l₂ k₂ a n
            then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0))
          p₂ MeasureTheory.Measure.count
        ≤ ENNReal.ofReal CbadM * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
      hbadM a ha ha1 l₁ l₂ k₁ k₂ t ht g
    set u0 : ℕ → ℤ → ℂ := fun n x => if core ρ C₀ l₁ l₂ k₁ k₂ a n
      then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0 with hu0
    set u1 : ℕ → ℤ → ℂ := fun n x => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcM ρ l₂ k₂ a n
      then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0 with hu1
    set u2 : ℕ → ℤ → ℂ := fun n x => if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey CρcM ρ l₂ k₂ a n
      then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0 with hu2
    have hpoint : ∀ n x, u0 n x = u1 n x + u2 n x := by
      intro n x
      by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n
      · by_cases hf : Farey CρcM ρ l₂ k₂ a n
        · have hF' : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcM ρ l₂ k₂ a n := ⟨hc, hf⟩
          have hnot : ¬ (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey CρcM ρ l₂ k₂ a n) :=
            fun h => h.2 hf
          simp only [hu0, hu1, hu2, if_pos hc, if_pos hF', if_neg hnot]
          ring
        · have hnot : ¬ (core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcM ρ l₂ k₂ a n) :=
            fun h => hf h.2
          have hc2 : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey CρcM ρ l₂ k₂ a n := ⟨hc, hf⟩
          simp only [hu0, hu1, hu2, if_pos hc, if_neg hnot, if_pos hc2]
          ring
      · simp only [hu0, hu1, hu2, if_neg hc,
            if_neg (fun h : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcM ρ l₂ k₂ a n => hc h.1),
            if_neg (fun h : core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey CρcM ρ l₂ k₂ a n => hc h.1)]
        ring
    have hV : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u0 n x)
        ≤ PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u1 n x)
          + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u2 n x) := by
      intro x
      have h1 : (fun n : ℕ => u0 n x) = (fun n : ℕ => u1 n x) + (fun n : ℕ => u2 n x) := by
        funext n
        exact hpoint n x
      rw [h1]
      exact variationalNorm_add_le hr1 _ _
    have hE : MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u0 n x))
          p₂ MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u1 n x))
            p₂ MeasureTheory.Measure.count
          + MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u2 n x))
            p₂ MeasureTheory.Measure.count := by
      refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u0 n x))
        (g := fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u1 n x)
          + PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u2 n x))
        (fun x => by rw [enorm_eq_self, enorm_eq_self]; exact hV x)).trans ?_
      exact eLpNorm_add_le_ennreal hp1 (ne_of_lt htp₂) (μ := MeasureTheory.Measure.count)
    have hu1e : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u1 n x))
        = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ Farey CρcM ρ l₂ k₂ a n
              then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0)) := by
      funext x
      rfl
    have hu2e : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u2 n x))
        = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
            if core ρ C₀ l₁ l₂ k₁ k₂ a n ∧ ¬ Farey CρcM ρ l₂ k₂ a n
              then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0)) := by
      funext x
      rfl
    refine hE.trans ?_
    rw [hu1e, hu2e]
    refine (add_le_add hb_far hb_bad).trans ?_
    calc ENNReal.ofReal (KM * (1 + (l₂ : ℝ)) * (1 + (P.natDegree : ℝ) * (k₂ : ℝ))) * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
          + ENNReal.ofReal CbadM * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count
        = (ENNReal.ofReal (KM * (1 + (l₂ : ℝ)) * (1 + (P.natDegree : ℝ) * (k₂ : ℝ)))
            + ENNReal.ofReal CbadM) * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := (add_mul _ _ _).symm
      _ ≤ ENNReal.ofReal (S * lossWeight 4 ρ l₁ l₂ k₁ k₂) * MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := mul_le_mul' hcomb le_rfl

/-! ## §5.  The target: the §8 large-scale estimate for the level-`0` model tuple -/

/-- **`Work.KMTAreas.A7.LoModelStatement P p₁ p₂`** (the §8 large-scale estimate for the level-`0`
model tuple). -/
theorem LoModelLargeScaleHolds (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1) :
    Work.KMTAreas.A7.LoModelStatement P p₁ p₂ := by
  classical
  intro C₀ r hC₀ hr
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  refine ⟨8, by norm_num, min 1 (1 / (2 * (C₀ : ℝ))), lt_min one_pos (by positivity), ?_⟩
  intro ρ hρ hρ1
  have hρ1le : ρ ≤ 1 := le_trans hρ1 (min_le_left _ _)
  have hρC : ρ ≤ 1 / (2 * (C₀ : ℝ)) := le_trans hρ1 (min_le_right _ _)
  have hF : ∀ Λ : NNReal, 1 < Λ → ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal)
      (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
      (C₀' l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2:ℝ) 1) (f : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if core ρ C₀' l₁ l₂ k₁ k₂ a n
          then Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
        p₁ MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * lossWeight 4 ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count :=
    fun Λ hΛ => LoFLinVarClipped ρ hρ hρ1le p₁ hp₁ htp₁ r hr Λ hΛ
  have hG : ∀ Λ : NNReal, 1 < Λ → ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal)
      (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
      (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (1/2:ℝ) 1) (g : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
          then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0))
        p₂ MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (C * lossWeight 4 ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count :=
    fun Λ hΛ => LoGLinVarClipped P hdeg C₀ hC₀ ρ hρ hρ1le hρC p₂ hp₂ htp₂ r hr Λ hΛ
  let Kf : NNReal → NNReal := fun Λ => if h : 1 < Λ then
      Real.toNNReal (Classical.choose (hF Λ h) * Classical.choose (hG Λ h) + 1) else 1
  refine ⟨Kf, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hlo
  set Cf : ℝ := Classical.choose (hF Λ hΛ) with hCfdef
  set Cg : ℝ := Classical.choose (hG Λ hΛ) with hCgdef
  obtain ⟨hCf0, hCfv⟩ := Classical.choose_spec (hF Λ hΛ)
  obtain ⟨hCg0, hCgv⟩ := Classical.choose_spec (hG Λ hΛ)
  have hKval : Kf Λ = Real.toNNReal (Cf * Cg + 1) := by
    simp only [Kf]
    rw [dif_pos hΛ]
  rw [hKval]
  have hKcoe : ((Real.toNNReal (Cf * Cg + 1) : NNReal) : ENNReal)
      = ENNReal.ofReal (Cf * Cg + 1) := by
    rw [← ENNReal.ofReal_coe_nnreal]
    refine congrArg ENNReal.ofReal (Real.coe_toNNReal _ ?_)
    have h := mul_pos hCf0 hCg0
    linarith
  rw [hKcoe]
  have hq : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  set X : ℝ → ℕ → ℤ → ℂ := fun t n x => if core ρ C₀ l₁ l₂ k₁ k₂ a n then
      (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
        * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x) else 0 with hXdef
  have hper : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => X t n x))
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Cf * Cg + 1) * ENNReal.ofReal (lossWeight 8 ρ l₁ l₂ k₁ k₂) *
          MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
    intro t ht
    have hAv : AEMeasurable (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
          then Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x else 0))
        MeasureTheory.Measure.count := (measurable_of_countable _).aemeasurable
    have hBu : AEMeasurable (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
          then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0))
        MeasureTheory.Measure.count := (measurable_of_countable _).aemeasurable
    have hprod : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => X t n x)
        ≤ PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
              then Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x else 0)
          * PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
              then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0) := by
      intro x
      have hfun : (fun n : ℕ => X t n x) = (fun n : ℕ =>
            (if core ρ C₀ l₁ l₂ k₁ k₂ a n
              then Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x else 0)
            * (if core ρ C₀ l₁ l₂ k₁ k₂ a n
              then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0)) := by
        funext n
        rw [hXdef]
        by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n <;> simp [hc]
      rw [hfun]
      exact variationalNorm_mul_le_one r hr1 _ _
    refine (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (f := fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => X t n x))
      (g := fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
            then Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x else 0)
        * PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if core ρ C₀ l₁ l₂ k₁ k₂ a n
            then Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x else 0))
      (fun x => by rw [enorm_eq_self, enorm_eq_self]; exact hprod x)).trans ?_
    refine (Commons.MeasureTheory.Function.eLpNorm_mul_le_eLpNorm_mul_eLpNorm
      (μ := MeasureTheory.Measure.count) (p := (p₁⁻¹ + p₂⁻¹)⁻¹) (q := p₁) (r := p₂)
      (by rw [inv_inv]) hAv hBu).trans ?_
    refine (mul_le_mul' (hCfv a ha ha1 C₀ l₁ l₂ k₁ k₂ t ht f)
      (hCgv a ha ha1 l₁ l₂ k₁ k₂ t ht g)).trans ?_
    have hlw4pos : 0 ≤ lossWeight 4 ρ l₁ l₂ k₁ k₂ :=
      (lossWeight_pos 4 ρ (by norm_num) hρ l₁ l₂ k₁ k₂).le
    have hlw8pos : 0 ≤ lossWeight 8 ρ l₁ l₂ k₁ k₂ :=
      (lossWeight_pos 8 ρ (by norm_num) hρ l₁ l₂ k₁ k₂).le
    calc (ENNReal.ofReal (Cf * lossWeight 4 ρ l₁ l₂ k₁ k₂) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count)
          * (ENNReal.ofReal (Cg * lossWeight 4 ρ l₁ l₂ k₁ k₂) *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count)
        = ENNReal.ofReal ((Cf * lossWeight 4 ρ l₁ l₂ k₁ k₂) *
              (Cg * lossWeight 4 ρ l₁ l₂ k₁ k₂)) *
            (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by
          rw [ennreal_mul_swap, ← ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal ((Cf * Cg) * lossWeight 8 ρ l₁ l₂ k₁ k₂) *
            (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by
          rw [show (Cf * lossWeight 4 ρ l₁ l₂ k₁ k₂) * (Cg * lossWeight 4 ρ l₁ l₂ k₁ k₂)
              = (Cf * Cg) * (lossWeight 4 ρ l₁ l₂ k₁ k₂ * lossWeight 4 ρ l₁ l₂ k₁ k₂) from by ring,
            lossWeight4_mul_self]
      _ ≤ ENNReal.ofReal ((Cf * Cg + 1) * lossWeight 8 ρ l₁ l₂ k₁ k₂) *
            (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hlw8pos
      _ = ENNReal.ofReal (Cf * Cg + 1) * ENNReal.ofReal (lossWeight 8 ρ l₁ l₂ k₁ k₂) *
            (MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
              MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) := by
          rw [ENNReal.ofReal_mul (by have h := mul_pos hCf0 hCg0; linarith)]
      _ = ENNReal.ofReal (Cf * Cg + 1) * ENNReal.ofReal (lossWeight 8 ρ l₁ l₂ k₁ k₂) *
            MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
            MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := (mul_assoc _ _ _).symm
  -- the measurability of the slices
  have hXm : ∀ n : ℕ, ∀ x : ℤ, AEMeasurable (fun t : ℝ => X t n x) volume := by
    intro n x
    have hXval : ∀ t : ℝ, X t n x = if core ρ C₀ l₁ l₂ k₁ k₂ a n then
        (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
          * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x) else 0 :=
      fun t => rfl
    by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n
    · have heq : (fun t : ℝ => X t n x) = fun t : ℝ =>
          (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
            * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x) := by
        funext t
        rw [hXval t, if_pos hc]
      rw [heq]
      exact ((measurable_iwConv_varphiNt (iwArithFreqs ρ 0) (Nat.floor (a n)) k₁ f x).mul
        (measurable_iwConv_varphitildeNt P (iwArithFreqs ρ 0) (Nat.floor (a n)) k₂ g x)).aemeasurable
    · have heq : (fun t : ℝ => X t n x) = fun _ : ℝ => (0 : ℂ) := by
        funext t
        rw [hXval t, if_neg hc]
      rw [heq]
      exact aemeasurable_const
  have hmain := variationalNorm_intervalIntegral_eLpNorm_le' r hr1 ((p₁⁻¹ + p₂⁻¹)⁻¹) hq X
      (ENNReal.ofReal (Cf * Cg + 1) * ENNReal.ofReal (lossWeight 8 ρ l₁ l₂ k₁ k₂) *
        MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
        MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count) hXm hper
  have hint : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∫ t in (1/2 : ℝ)..1, X t n x))
      = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => loModelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) := by
    funext x
    congr 1
    funext n
    have hXval : ∀ t : ℝ, X t n x = if core ρ C₀ l₁ l₂ k₁ k₂ a n then
        (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
          * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x) else 0 :=
      fun t => rfl
    by_cases hc : core ρ C₀ l₁ l₂ k₁ k₂ a n
    · have hlg : loGuard ρ C₀ a l₁ l₂ k₁ k₂ n := hc
      have hfun2 : (fun t : ℝ => X t n x) = fun t : ℝ =>
          (Tle ρ 0 (varphiNt (Nat.floor (a n)) k₁ t) f x)
            * (Tle ρ 0 (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g x) := by
        funext t
        rw [hXval t, if_pos hc]
      rw [loModelTuple, if_pos hlg, hfun2]
    · have hlg : ¬ loGuard ρ C₀ a l₁ l₂ k₁ k₂ n := hc
      have hfun2 : (fun t : ℝ => X t n x) = fun _ : ℝ => (0 : ℂ) := by
        funext t
        rw [hXval t, if_neg hc]
      rw [loModelTuple, if_neg hlg, hfun2]
      simp
  rw [hint] at hmain
  exact hmain

end

end Work.KMTAreas.A7
