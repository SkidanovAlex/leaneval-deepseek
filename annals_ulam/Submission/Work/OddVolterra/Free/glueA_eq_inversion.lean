import Mathlib
import Submission.Work.OddCurve.LowSlope.GlueDataDefs
import Submission.Work.OddCurve.LowSlope.GlueDefs
import Submission.Work.OddCurve.LowSlope.GlueIdent
import Submission.Work.OddCurve.LowSlope.QuantDefs
import Submission.Work.OddCurve.LowSlope.radonPhiRhoNewEq
import Submission.Work.OddRadon.Abel
import Submission.Work.OddRadon.radonInverse_radonPhi_local
import Submission.Work.OddRadon.radonProfile_radonInverse
import Submission.Work.OddCurve.LowSlope.abel_integral_trig_substitution_no_hyp
import Submission.Work.OddVolterra.Free.gap_inversion_bounds_free
import Submission.Work.OddVolterra.Free.continuousOn_abelTrans_negHalf

namespace Work.OddVolterra.Free

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-!
# The glued deviation `GlueA` as an inverse Radon transform (`Work.OddVolterra.Free`)

The low-slope step of the odd case reconstructs the final body from the *glued* first Radon datum
`GlueF n ρ` (the anchor's data on the cap `|c| < 4/5`, the ball's above), and the two-power system
it solves has the deviation `GlueA n ρ α = 2 𝓡^{-1}(GlueF n ρ)(cos α)/cos²α - 2`.

This file proves the identity

`GlueA n ρ α = 2 · radonInverse n (deltaA n ρ) (cos α) / cos²α`   for `0 < cos α ≠ 4/5`,

where `deltaA n ρ = GlueF n ρ - ballPhiData n` is the datum deviation.  Equivalently
(at `u = cos α`, multiplied by `u²/2`)

`radonInverse n (GlueF n ρ) u - u² = radonInverse n (deltaA n ρ) u`,

i.e. the *linearity* of the inverse Radon transform on the datum-level decomposition
`GlueF = deltaA + ballPhiData`, combined with the ball identity
`radonInverse n (ballPhiData n) u = u²`.

Below the glue point `u < 4/5` this follows from the left-inverse (surjectivity) description of
`radonInverse` on the cap; above it, it is a genuine additivity statement for `radonInverse`,
because `deltaA n ρ` jumps at `c = 4/5` and is therefore *not* the Radon datum of any even
profile on `(0,u]`.  The single point `c = 4/5` (where the datum of the glued profile is
discontinuous) is the only place where the identity can fail, which is why the statement excludes
`cos α = 4/5`.
-/

/-! ## The three even profiles whose data are glued -/

/-- The anchor's even profile `u ↦ u²/2 (ρ u ^{2n+2} + ρ (-u)^{2n+2})`. -/
private def gammaAnchor (n : ℕ) (ρ : ℝ → ℝ) : ℝ → ℝ :=
  fun v => v ^ 2 / 2 * (ρ v ^ (2 * n + 2) + ρ (-v) ^ (2 * n + 2))

/-- The ball's even profile `u ↦ u²`. -/
private def gammaBall : ℝ → ℝ := fun v => v ^ 2

/-- The deviation profile `u ↦ u²/2 (ρ u^{2n+2} + ρ(-u)^{2n+2}) - u²`. -/
private def gammaDelta (n : ℕ) (ρ : ℝ → ℝ) : ℝ → ℝ :=
  fun v => v ^ 2 / 2 * (ρ v ^ (2 * n + 2) + ρ (-v) ^ (2 * n + 2)) - v ^ 2

/-- The iterated exponent reduction of the Abel datum — `radonInverse` is the Abel inversion of. -/
private def redDat (n : ℕ) (F : ℝ → ℝ) : ℝ → ℝ :=
  Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) (Work.OddRadon.abelDatum n F)

private lemma gammaAnchor_even (n : ℕ) (ρ : ℝ → ℝ) (t : ℝ) :
    gammaAnchor n ρ (-t) = gammaAnchor n ρ t := by
  simp only [gammaAnchor]; rw [neg_sq, neg_neg]; ring

private lemma gammaDelta_even (n : ℕ) (ρ : ℝ → ℝ) (t : ℝ) :
    gammaDelta n ρ (-t) = gammaDelta n ρ t := by
  simp only [gammaDelta]; rw [neg_sq, neg_neg]; ring

private lemma gammaBall_even (t : ℝ) : gammaBall (-t) = gammaBall t := by
  simp only [gammaBall, neg_sq]

private lemma gammaDelta_eq (n : ℕ) (ρ : ℝ → ℝ) :
    gammaDelta n ρ = gammaAnchor n ρ - gammaBall := by
  funext v; simp only [gammaDelta, gammaAnchor, gammaBall, Pi.sub_apply]

private lemma gammaDelta_add (n : ℕ) (ρ : ℝ → ℝ) :
    gammaAnchor n ρ = gammaDelta n ρ + gammaBall := by
  funext v; simp only [gammaDelta, gammaAnchor, gammaBall, Pi.add_apply]; ring

private lemma gammaAnchor_zero (n : ℕ) (ρ : ℝ → ℝ) : gammaAnchor n ρ 0 = 0 := by
  simp [gammaAnchor]

private lemma gammaDelta_zero (n : ℕ) (ρ : ℝ → ℝ) : gammaDelta n ρ 0 = 0 := by
  simp [gammaDelta]

/-- Cancelling the diagonal prefactor of the datum identification. -/
private lemma datum_cancel {S c A : ℝ} (k : ℕ) (hS : 2 * S ≠ 0) (hc : c ^ k ≠ 0) :
    (2 * S)⁻¹ * c ^ k * (2 * S * (c ^ k)⁻¹ * A) = A := by
  rw [show (2 * S)⁻¹ * c ^ k * (2 * S * (c ^ k)⁻¹ * A)
      = ((2 * S)⁻¹ * (2 * S)) * (c ^ k * (c ^ k)⁻¹) * A by ring,
    inv_mul_cancel₀ hS, mul_inv_cancel₀ hc]
  ring

/-! ## Sub-additivity of `radonProfile` in the profile variable -/

private lemma radonProfile_sub {d : ℕ} {γ₁ γ₂ : ℝ → ℝ} {c : ℝ}
    (h₁ : IntervalIntegrable (fun s : ℝ => (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ₁ (c * s))
      volume (-1 : ℝ) 1)
    (h₂ : IntervalIntegrable (fun s : ℝ => (1 - s ^ 2) ^ ((d : ℝ) / 2 - 2) * γ₂ (c * s))
      volume (-1 : ℝ) 1) :
    Work.OddRadon.radonProfile d (γ₁ - γ₂) c
      = Work.OddRadon.radonProfile d γ₁ c - Work.OddRadon.radonProfile d γ₂ c := by
  simp only [Work.OddRadon.radonProfile]
  rw [← mul_sub]
  congr 1
  rw [← intervalIntegral.integral_sub h₁ h₂]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [Pi.sub_apply]
  ring

/-- The anchor's even profile, composed with `c * ·`, is continuous on `[-1,1]` for `|c| < 1`. -/
private lemma continuousOn_gammaAnchor_comp (n : ℕ) {ρ : ℝ → ℝ} {c : ℝ} (hc : |c| < 1)
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ContinuousOn (fun s : ℝ => gammaAnchor n ρ (c * s)) (Set.uIcc (-1 : ℝ) 1) := by
  have hA : ContinuousOn (fun s : ℝ => (c * s) ^ 2 * ρ (c * s) ^ (2 * n + 2))
      (Set.uIcc (-1 : ℝ) 1) :=
    Work.OddCurve.LowSlope.continuousOn_profile_comp_mul n hc hρ
  have hB : ContinuousOn (fun s : ℝ => (-(c * s)) ^ 2 * ρ (-(c * s)) ^ (2 * n + 2))
      (Set.uIcc (-1 : ℝ) 1) := by
    have h := Work.OddCurve.LowSlope.continuousOn_profile_comp_mul n (ρ := ρ) (a := -c)
      (by simpa using hc) hρ
    refine h.congr ?_
    intro s _
    simp only []
    rw [show (-c) * s = -(c * s) by ring]
  have hfun : (fun s : ℝ => gammaAnchor n ρ (c * s))
      = fun s : ℝ => ((c * s) ^ 2 * ρ (c * s) ^ (2 * n + 2)
          + (-(c * s)) ^ 2 * ρ (-(c * s)) ^ (2 * n + 2)) / 2 := by
    funext s; simp only [gammaAnchor]; ring
  rw [hfun]
  exact (hA.add hB).div_const 2

private lemma continuousOn_gammaBall_comp (c : ℝ) :
    ContinuousOn (fun s : ℝ => gammaBall (c * s)) (Set.uIcc (-1 : ℝ) 1) := by
  simp only [gammaBall]
  fun_prop

/-! ## The Radon profile of the anchor's even profile -/

/-- **The anchor's first Radon datum only depends on the even part of its profile.**  This is the
`hagree` computation of `Work.OddRadon.radonInverse_radonPhi_local`, isolated here. -/
private lemma radonPhi_eq_radonProfile_gammaAnchor (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    {c : ℝ} (hc : |c| < 1) :
    Work.OddCurve.LowSlope.radonPhi n ρ c
      = Work.OddRadon.radonProfile (2 * n + 1) (gammaAnchor n ρ) c := by
  have hG₁ : ContinuousOn (fun s : ℝ => (c * s) ^ 2 * ρ (c * s) ^ (2 * n + 2))
      (Set.uIcc (-1 : ℝ) 1) :=
    Work.OddCurve.LowSlope.continuousOn_profile_comp_mul n hc hρ
  have hG₂ : ContinuousOn (fun s : ℝ => (-(c * s)) ^ 2 * ρ (-(c * s)) ^ (2 * n + 2))
      (Set.uIcc (-1 : ℝ) 1) := by
    have h := Work.OddCurve.LowSlope.continuousOn_profile_comp_mul n (ρ := ρ) (a := -c)
      (by simpa using hc) hρ
    refine h.congr ?_
    intro s _
    simp only []
    rw [show (-c) * s = -(c * s) by ring]
  have hf := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn hG₁
  have hg := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn hG₂
  have h1 : Work.OddCurve.LowSlope.radonPhi n ρ c
      = Work.OddRadon.radonProfile (2 * n + 1)
          (fun v : ℝ => (v ^ 2 * ρ v ^ (2 * n + 2)
            + (fun w : ℝ => w ^ 2 * ρ w ^ (2 * n + 2)) (-v)) / 2) c := by
    unfold Work.OddCurve.LowSlope.radonPhi
    exact Work.OddCurve.LowSlope.radonProfile_evenPart (2 * n + 1) hf hg
  have h2 : (fun v : ℝ => (v ^ 2 * ρ v ^ (2 * n + 2)
      + (fun w : ℝ => w ^ 2 * ρ w ^ (2 * n + 2)) (-v)) / 2) = gammaAnchor n ρ := by
    funext v
    simp only [gammaAnchor]
    ring
  rw [h1, h2]

/-! ## The three Abel data of the glued pieces -/

/-- On the cap the glued datum is the anchor's. -/
private lemma GlueF_eq_radonPhi_cap {n : ℕ} {ρ : ℝ → ℝ} {c : ℝ} (hc0 : 0 < c)
    (hc : c < 4 / 5) :
    Work.OddCurve.LowSlope.GlueF n ρ c = Work.OddCurve.LowSlope.radonPhi n ρ c := by
  have h1 : Work.OddCurve.LowSlope.GlueF n ρ c
      = Work.OddCurve.LowSlope.gluedPhi n (Work.OddCurve.LowSlope.radonPhi n ρ) c := by
    simp only [Work.OddCurve.LowSlope.GlueF, abs_of_pos hc0]
  rw [h1, Work.OddCurve.LowSlope.gluedPhi_of_lt hc0.le hc]

/-- On the cap the deviation datum is the difference of the anchor's and the ball's data. -/
private lemma deltaA_eq_cap {n : ℕ} {ρ : ℝ → ℝ} {c : ℝ} (hc0 : 0 < c) (hc : c < 4 / 5) :
    Work.OddCurve.LowSlope.deltaA n ρ c
      = Work.OddCurve.LowSlope.radonPhi n ρ c - Work.OddCurve.LowSlope.ballPhiData n c := by
  rw [Work.OddCurve.LowSlope.deltaA_def, GlueF_eq_radonPhi_cap hc0 hc]

/-- **The glued first datum on the cap is the Abel transform of the anchor's even profile.** -/
private lemma abelDatum_GlueF_eq (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ∀ c ∈ Set.Ioo (0 : ℝ) (4 / 5),
      Work.OddRadon.abelDatum n (Work.OddCurve.LowSlope.GlueF n ρ) c
        = Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) (gammaAnchor n ρ) c := by
  intro c hc
  have hcabs : |c| < 1 := by rw [abs_of_pos hc.1]; exact lt_trans hc.2 (by norm_num)
  rw [Work.OddRadon.abelDatum, GlueF_eq_radonPhi_cap hc.1 hc.2,
    radonPhi_eq_radonProfile_gammaAnchor n hn hρ hcabs,
    Work.OddRadon.radonProfile_eq_abelTrans' n hn (gammaAnchor_even n ρ) hc.1]
  exact datum_cancel (2 * n - 2)
    (mul_ne_zero (by norm_num) (ne_of_gt (Work.OddRadon.sphereArea_pos _)))
    (pow_ne_zero _ (ne_of_gt hc.1))

/-- **The difference `deltaA` is the Abel transform of the deviation profile.** -/
private lemma abelDatum_deltaA_eq (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ∀ c ∈ Set.Ioo (0 : ℝ) (4 / 5),
      Work.OddRadon.abelDatum n (Work.OddCurve.LowSlope.deltaA n ρ) c
        = Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) (gammaDelta n ρ) c := by
  intro c hc
  have hcabs : |c| < 1 := by rw [abs_of_pos hc.1]; exact lt_trans hc.2 (by norm_num)
  have h₁ := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn
    (continuousOn_gammaAnchor_comp n hcabs hρ)
  have h₂ := Work.OddCurve.LowSlope.intervalIntegrable_radonKernel_mul n hn
    (continuousOn_gammaBall_comp c)
  have hsub := radonProfile_sub (d := 2 * n + 1) (γ₁ := gammaAnchor n ρ) (γ₂ := gammaBall)
    (c := c) h₁ h₂
  have hdel : Work.OddCurve.LowSlope.deltaA n ρ c
      = Work.OddRadon.radonProfile (2 * n + 1) (gammaDelta n ρ) c := by
    rw [deltaA_eq_cap hc.1 hc.2, radonPhi_eq_radonProfile_gammaAnchor n hn hρ hcabs,
      show Work.OddCurve.LowSlope.ballPhiData n c
        = Work.OddRadon.radonProfile (2 * n + 1) gammaBall c from rfl]
    rw [← hsub, ← gammaDelta_eq n ρ]
  rw [Work.OddRadon.abelDatum, hdel,
    Work.OddRadon.radonProfile_eq_abelTrans' n hn (gammaDelta_even n ρ) hc.1]
  exact datum_cancel (2 * n - 2)
    (mul_ne_zero (by norm_num) (ne_of_gt (Work.OddRadon.sphereArea_pos _)))
    (pow_ne_zero _ (ne_of_gt hc.1))

/-- **The ball's first datum is the Abel transform of `v ↦ v²` (for every `c > 0`).** -/
private lemma abelDatum_ball_eq (n : ℕ) (hn : 1 ≤ n) :
    ∀ c : ℝ, 0 < c →
      Work.OddRadon.abelDatum n (Work.OddCurve.LowSlope.ballPhiData n) c
        = Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) gammaBall c := by
  intro c hc
  rw [Work.OddRadon.abelDatum,
    show Work.OddCurve.LowSlope.ballPhiData n c
      = Work.OddRadon.radonProfile (2 * n + 1) gammaBall c from rfl,
    Work.OddRadon.radonProfile_eq_abelTrans' n hn gammaBall_even hc]
  exact datum_cancel (2 * n - 2)
    (mul_ne_zero (by norm_num) (ne_of_gt (Work.OddRadon.sphereArea_pos _)))
    (pow_ne_zero _ (ne_of_gt hc))


/-! ## Continuity of the three profiles near the cap -/

private lemma continuousOn_gammaAnchor_Icc (n : ℕ) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ContinuousOn (gammaAnchor n ρ) (Set.Icc 0 (4 / 5)) := by
  have hρc : ContinuousOn ρ (Set.Icc (0 : ℝ) (4 / 5)) :=
    hρ.continuousOn.mono (by
      intro x hx
      have h1 : (0 : ℝ) ≤ x := hx.1
      have h2 : x ≤ 4 / 5 := hx.2
      exact ⟨by linarith, lt_of_le_of_lt h2 (by norm_num)⟩)
  have hρneg : ContinuousOn (fun s : ℝ => ρ (-s)) (Set.Icc (0 : ℝ) (4 / 5)) := by
    refine hρ.continuousOn.comp (by fun_prop) ?_
    intro x hx
    have h1 : (0 : ℝ) ≤ x := hx.1
    have h2 : x ≤ 4 / 5 := hx.2
    exact ⟨by linarith, by linarith⟩
  have hA : ContinuousOn (fun s : ℝ => s ^ 2 * ρ s ^ (2 * n + 2)) (Set.Icc 0 (4 / 5)) :=
    (continuousOn_id.pow 2).mul (hρc.pow (2 * n + 2))
  have hB : ContinuousOn (fun s : ℝ => s ^ 2 * ρ (-s) ^ (2 * n + 2)) (Set.Icc 0 (4 / 5)) :=
    (continuousOn_id.pow 2).mul (hρneg.pow (2 * n + 2))
  have hfun : gammaAnchor n ρ
      = fun s : ℝ => (s ^ 2 * ρ s ^ (2 * n + 2) + s ^ 2 * ρ (-s) ^ (2 * n + 2)) / 2 := by
    funext s; simp only [gammaAnchor]; ring
  rw [hfun]
  exact (hA.add hB).div_const 2

private lemma continuousOn_gammaBall (b : ℝ) : ContinuousOn gammaBall (Set.Icc 0 b) :=
  continuousOn_id.pow 2

private lemma continuousOn_gammaDelta_Icc (n : ℕ) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ContinuousOn (gammaDelta n ρ) (Set.Icc 0 (4 / 5)) := by
  have hfun : gammaDelta n ρ = fun s : ℝ => gammaAnchor n ρ s - gammaBall s := by
    funext s; simp only [gammaDelta, gammaAnchor, gammaBall, Pi.sub_apply]
  rw [hfun]
  exact (continuousOn_gammaAnchor_Icc n hρ).sub (continuousOn_gammaBall (4 / 5))

/-- A bound for a continuous function on `[0,b]`, valid on `(0,b)`. -/
private lemma exists_bound_Icc {f : ℝ → ℝ} {b : ℝ}
    (hf : ContinuousOn f (Set.Icc 0 b)) : ∃ M : ℝ, ∀ s ∈ Set.Ioo 0 b, |f s| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  exact ⟨M, fun s hs => hM s ⟨hs.1.le, hs.2.le⟩⟩

/-! ## The reduced data on the cap -/

private lemma redDat_eq_abelReduceIter (n : ℕ) (F : ℝ → ℝ) (c : ℝ) :
    redDat n F c
      = Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1) (Work.OddRadon.abelDatum n F) c :=
  rfl

private lemma reduce_index (n : ℕ) (hn : 1 ≤ n) :
    (((n - 1 : ℕ) : ℝ)) - 1 < (n : ℝ) - 3 / 2 := by
  rw [Nat.cast_sub hn]; push_cast; linarith

private lemma reduce_exp (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) - 3 / 2) - (((n - 1 : ℕ) : ℝ)) = -(1 / 2) := by
  rw [Nat.cast_sub hn]; ring

private lemma redDat_GlueF_cap (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ∀ c ∈ Set.Ioo (0 : ℝ) (4 / 5),
      redDat n (Work.OddCurve.LowSlope.GlueF n ρ) c
        = Work.OddRadon.abelTrans (-(1 / 2)) (gammaAnchor n ρ) c := by
  intro c hc
  have hcont := continuousOn_gammaAnchor_Icc n hρ
  have hrec := abelReduceIter_abelTrans_local (β := (n : ℝ) - 3 / 2) (a₀ := 4 / 5)
    (γ := gammaAnchor n ρ) (by norm_num)
    (hcont.mono (by intro x hx; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
    (exists_bound_Icc hcont) (k := n - 1) (reduce_index n hn)
  have hcongr : Set.EqOn
      (Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
        (Work.OddRadon.abelDatum n (Work.OddCurve.LowSlope.GlueF n ρ)))
      (Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
        (Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) (gammaAnchor n ρ)))
      (Set.Ioo (0 : ℝ) (4 / 5)) :=
    Work.OddRadon.abelReduceIter_congr_open isOpen_Ioo (n - 1) ((n : ℝ) - 3 / 2)
      (fun x hx => abelDatum_GlueF_eq n hn hρ x hx)
  rw [redDat_eq_abelReduceIter, hcongr hc, hrec hc, reduce_exp n hn]

private lemma redDat_deltaA_cap (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ∀ c ∈ Set.Ioo (0 : ℝ) (4 / 5),
      redDat n (Work.OddCurve.LowSlope.deltaA n ρ) c
        = Work.OddRadon.abelTrans (-(1 / 2)) (gammaDelta n ρ) c := by
  intro c hc
  have hcont := continuousOn_gammaDelta_Icc n hρ
  have hrec := abelReduceIter_abelTrans_local (β := (n : ℝ) - 3 / 2) (a₀ := 4 / 5)
    (γ := gammaDelta n ρ) (by norm_num)
    (hcont.mono (by intro x hx; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
    (exists_bound_Icc hcont) (k := n - 1) (reduce_index n hn)
  have hcongr : Set.EqOn
      (Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
        (Work.OddRadon.abelDatum n (Work.OddCurve.LowSlope.deltaA n ρ)))
      (Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
        (Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) (gammaDelta n ρ)))
      (Set.Ioo (0 : ℝ) (4 / 5)) :=
    Work.OddRadon.abelReduceIter_congr_open isOpen_Ioo (n - 1) ((n : ℝ) - 3 / 2)
      (fun x hx => abelDatum_deltaA_eq n hn hρ x hx)
  rw [redDat_eq_abelReduceIter, hcongr hc, hrec hc, reduce_exp n hn]

private lemma redDat_ball_eq (n : ℕ) (hn : 1 ≤ n) :
    ∀ c ∈ Set.Ioo (0 : ℝ) 2,
      redDat n (Work.OddCurve.LowSlope.ballPhiData n) c
        = Work.OddRadon.abelTrans (-(1 / 2)) gammaBall c := by
  intro c hc
  have hcont := continuousOn_gammaBall 2
  have hrec := abelReduceIter_abelTrans_local (β := (n : ℝ) - 3 / 2) (a₀ := 2)
    (γ := gammaBall) (by norm_num)
    (hcont.mono (by intro x hx; exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩))
    (exists_bound_Icc hcont) (k := n - 1) (reduce_index n hn)
  have hcongr : Set.EqOn
      (Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
        (Work.OddRadon.abelDatum n (Work.OddCurve.LowSlope.ballPhiData n)))
      (Work.OddRadon.abelReduceIter ((n : ℝ) - 3 / 2) (n - 1)
        (Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) gammaBall))
      (Set.Ioo (0 : ℝ) 2) :=
    Work.OddRadon.abelReduceIter_congr_open isOpen_Ioo (n - 1) ((n : ℝ) - 3 / 2)
      (fun x hx => abelDatum_ball_eq n hn x hx.1)
  rw [redDat_eq_abelReduceIter, hcongr hc, hrec hc, reduce_exp n hn]

/-! ## Values of the half-Abel transform of the two basic profiles -/

private lemma abelTrans_negHalf_gammaBall {c : ℝ} (hc : 0 < c) :
    Work.OddRadon.abelTrans (-(1 / 2)) gammaBall c = Real.pi / 4 * c ^ 2 := by
  rw [Work.OddRadon.abelTrans_neg_half_eq_trigAbel hc]
  have h1 : Work.OddRadon.trigAbel gammaBall c
      = c ^ 2 * ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ ^ 2 := by
    simp only [Work.OddRadon.trigAbel, gammaBall]
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  rw [h1, integral_sin_sq]
  simp only [Real.sin_zero, Real.sin_pi_div_two, Real.cos_pi_div_two, mul_zero]
  ring

private lemma continuousOn_gammaBall_comp_sin (c : ℝ) :
    ContinuousOn (fun θ : ℝ => gammaBall (c * Real.sin θ)) (Set.uIcc 0 (Real.pi / 2)) := by
  show ContinuousOn (fun θ : ℝ => (c * Real.sin θ) ^ 2) (Set.uIcc 0 (Real.pi / 2))
  fun_prop

private lemma continuousOn_gammaDelta_comp_sin (n : ℕ) {ρ : ℝ → ℝ} {c : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) (4 / 5))
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ContinuousOn (fun θ : ℝ => gammaDelta n ρ (c * Real.sin θ)) (Set.uIcc 0 (Real.pi / 2)) := by
  refine (continuousOn_gammaDelta_Icc n hρ).comp ?_ ?_
  · exact (continuous_const.mul Real.continuous_sin).continuousOn
  · intro θ hθ
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi / 2)] at hθ
    have hs : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [Real.pi_pos, hθ.2]⟩
    exact ⟨mul_nonneg hc.1.le hs, by nlinarith [Real.sin_le_one θ, hc.1.le, hc.2]⟩

private lemma continuousOn_gammaAnchor_comp_sin (n : ℕ) {ρ : ℝ → ℝ} {c : ℝ}
    (hc : c ∈ Set.Ioo (0 : ℝ) (4 / 5))
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ContinuousOn (fun θ : ℝ => gammaAnchor n ρ (c * Real.sin θ)) (Set.uIcc 0 (Real.pi / 2)) := by
  refine (continuousOn_gammaAnchor_Icc n hρ).comp ?_ ?_
  · exact (continuous_const.mul Real.continuous_sin).continuousOn
  · intro θ hθ
    rw [Set.uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi / 2)] at hθ
    have hs : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_mem_Icc ⟨hθ.1, by linarith [Real.pi_pos, hθ.2]⟩
    exact ⟨mul_nonneg hc.1.le hs, by nlinarith [Real.sin_le_one θ, hc.1.le, hc.2]⟩

/-- **Additivity of the half-Abel transform on the three profiles** (`c < 4/5`). -/
private lemma abelTrans_negHalf_add (n : ℕ) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1))
    {c : ℝ} (hc : c ∈ Set.Ioo (0 : ℝ) (4 / 5)) :
    Work.OddRadon.abelTrans (-(1 / 2)) (gammaAnchor n ρ) c
      = Work.OddRadon.abelTrans (-(1 / 2)) (gammaDelta n ρ) c
        + Work.OddRadon.abelTrans (-(1 / 2)) gammaBall c := by
  have hpt : ∀ θ : ℝ, gammaAnchor n ρ (c * Real.sin θ)
      = gammaDelta n ρ (c * Real.sin θ) + gammaBall (c * Real.sin θ) := by
    intro θ
    simp only [gammaDelta, gammaAnchor, gammaBall]
    ring
  have hDc := continuousOn_gammaDelta_comp_sin n hc hρ
  have hBc := continuousOn_gammaBall_comp_sin c
  have hAc := continuousOn_gammaAnchor_comp_sin n hc hρ
  rw [Work.OddRadon.abelTrans_neg_half_eq_trigAbel hc.1,
    Work.OddRadon.abelTrans_neg_half_eq_trigAbel hc.1,
    Work.OddRadon.abelTrans_neg_half_eq_trigAbel hc.1]
  simp only [Work.OddRadon.trigAbel]
  calc (∫ θ in (0 : ℝ)..(Real.pi / 2), gammaAnchor n ρ (c * Real.sin θ))
      = ∫ θ in (0 : ℝ)..(Real.pi / 2),
          (gammaDelta n ρ (c * Real.sin θ) + gammaBall (c * Real.sin θ)) := by
        apply intervalIntegral.integral_congr
        intro θ _
        exact hpt θ
    _ = (∫ θ in (0 : ℝ)..(Real.pi / 2), gammaDelta n ρ (c * Real.sin θ))
          + ∫ θ in (0 : ℝ)..(Real.pi / 2), gammaBall (c * Real.sin θ) :=
        intervalIntegral.integral_add hDc.intervalIntegrable hBc.intervalIntegrable


/-! ## The reduced data of the ball is `(π/4) c²` -/

private lemma redDat_ball_eq_pi (n : ℕ) (hn : 1 ≤ n) :
    ∀ c ∈ Set.Ioo (0 : ℝ) 2,
      redDat n (Work.OddCurve.LowSlope.ballPhiData n) c = Real.pi / 4 * c ^ 2 := by
  intro c hc
  rw [redDat_ball_eq n hn c hc, abelTrans_negHalf_gammaBall hc.1]

/-- **The reduced datum of the glued datum is the sum of the two reduced data on the cap.** -/
private lemma redDat_add_cap (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ∀ c ∈ Set.Ioo (0 : ℝ) (4 / 5),
      redDat n (Work.OddCurve.LowSlope.GlueF n ρ) c
        = redDat n (Work.OddCurve.LowSlope.deltaA n ρ) c
          + redDat n (Work.OddCurve.LowSlope.ballPhiData n) c := by
  intro c hc
  rw [redDat_GlueF_cap n hn hρ c hc, redDat_deltaA_cap n hn hρ c hc,
    redDat_ball_eq n hn c ⟨hc.1, by linarith [hc.2]⟩, abelTrans_negHalf_add n hρ hc]

/-! ## The data above the glue point -/

private lemma GlueF_eq_ballPhiData_above {n : ℕ} {ρ : ℝ → ℝ} {c : ℝ} (hc : 4 / 5 < c) :
    Work.OddCurve.LowSlope.GlueF n ρ c = Work.OddCurve.LowSlope.ballPhiData n c := by
  have h1 : Work.OddCurve.LowSlope.GlueF n ρ c
      = Work.OddCurve.LowSlope.gluedPhi n (Work.OddCurve.LowSlope.radonPhi n ρ) c := by
    simp only [Work.OddCurve.LowSlope.GlueF, abs_of_pos (by linarith : (0 : ℝ) < c)]
  rw [h1, Work.OddCurve.LowSlope.gluedPhi_of_ge (by linarith : (0 : ℝ) ≤ c) (le_of_lt hc)]

private lemma abelDatum_deltaA_eq_zero {n : ℕ} {ρ : ℝ → ℝ} {c : ℝ} (hc : 4 / 5 < c) :
    Work.OddRadon.abelDatum n (Work.OddCurve.LowSlope.deltaA n ρ) c = 0 := by
  simp only [Work.OddRadon.abelDatum, Work.OddCurve.LowSlope.deltaA_def,
    GlueF_eq_ballPhiData_above hc, sub_self, mul_zero]

/-- Above the glue point the deviation datum vanishes, hence so does its reduction. -/
private lemma redDat_deltaA_eq_zero {n : ℕ} {ρ : ℝ → ℝ} {c : ℝ} (hc : 4 / 5 < c) :
    redDat n (Work.OddCurve.LowSlope.deltaA n ρ) c = 0 := by
  have hcongr := Work.OddRadon.abelReduceIter_congr_open (s := Set.Ioi (4 / 5)) isOpen_Ioi
    (n - 1) ((n : ℝ) - 3 / 2)
    (f := Work.OddRadon.abelDatum n (Work.OddCurve.LowSlope.deltaA n ρ)) (g := 0)
    (fun x hx => abelDatum_deltaA_eq_zero hx)
  rw [redDat_eq_abelReduceIter, hcongr hc, abelReduceIter_zero]
  rfl

/-- Above the glue point the glued datum is the ball's datum, hence so is its reduction. -/
private lemma redDat_GlueF_eq_redDat_ball {n : ℕ} {ρ : ℝ → ℝ} {c : ℝ} (hc : 4 / 5 < c) :
    redDat n (Work.OddCurve.LowSlope.GlueF n ρ) c
      = redDat n (Work.OddCurve.LowSlope.ballPhiData n) c := by
  have hdata : Set.EqOn (Work.OddRadon.abelDatum n (Work.OddCurve.LowSlope.GlueF n ρ))
      (Work.OddRadon.abelDatum n (Work.OddCurve.LowSlope.ballPhiData n)) (Set.Ioi (4 / 5)) := by
    intro x hx
    simp only [Work.OddRadon.abelDatum, GlueF_eq_ballPhiData_above hx]
  exact Work.OddRadon.abelReduceIter_congr_open (s := Set.Ioi (4 / 5)) isOpen_Ioi
    (n - 1) ((n : ℝ) - 3 / 2) hdata hc

/-! ## The left-inverse (surjectivity) description on the cap -/

private lemma radonInverse_GlueF_cap (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ∀ u ∈ Set.Ioo (0 : ℝ) (4 / 5),
      Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ) u
        = u ^ 2 / 2 * (ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2)) := by
  intro u hu
  rw [Work.OddCurve.LowSlope.radonInverse_congr_of_eqOn (n := n) hu.1 hu.2
    (fun c hc => GlueF_eq_radonPhi_cap hc.1 hc.2)]
  exact Work.OddRadon.radonInverse_radonPhi_local n hn (c₁ := 4 / 5) (by norm_num) hρ hu.1 hu.2

private lemma contDiffOn_gammaDelta_Icc (n : ℕ) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ 1 (gammaDelta n ρ) (Set.Icc (-(4 / 5)) (4 / 5)) := by
  have hfun : gammaDelta n ρ
      = fun s : ℝ => s ^ 2 / 2 * (ρ s ^ (2 * n + 2) + ρ (-s) ^ (2 * n + 2)) - s ^ 2 := rfl
  rw [hfun]
  have hmap1 : Set.MapsTo (fun s : ℝ => s) (Set.Icc (-(4 / 5)) (4 / 5)) (Set.Ioo (-1 : ℝ) 1) := by
    intro s hs
    rw [Set.mem_Icc] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hmap2 : Set.MapsTo (fun s : ℝ => -s) (Set.Icc (-(4 / 5)) (4 / 5)) (Set.Ioo (-1 : ℝ) 1) := by
    intro s hs
    rw [Set.mem_Icc] at hs
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have h1 : ContDiffOn ℝ 1 (fun s : ℝ => ρ s) (Set.Icc (-(4 / 5)) (4 / 5)) :=
    (hρ.of_le (by simp)).comp contDiffOn_id hmap1
  have h2 : ContDiffOn ℝ 1 (fun s : ℝ => ρ (-s)) (Set.Icc (-(4 / 5)) (4 / 5)) :=
    (hρ.of_le (by simp)).comp contDiffOn_id.neg hmap2
  have h3 : ContDiffOn ℝ 1 (fun s : ℝ => s ^ 2 / 2) (Set.Icc (-(4 / 5)) (4 / 5)) := by fun_prop
  exact (h3.mul ((h1.pow (2 * n + 2)).add (h2.pow (2 * n + 2)))).sub (by fun_prop)

/-- On the cap, the deviation datum is the Radon profile of the deviation profile. -/
private lemma deltaA_eq_radonProfile_cap (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ∀ c ∈ Set.Ioo (0 : ℝ) (4 / 5),
      Work.OddCurve.LowSlope.deltaA n ρ c
        = Work.OddRadon.radonProfile (2 * n + 1) (gammaDelta n ρ) c := by
  intro c hc
  have h1 := abelDatum_deltaA_eq n hn hρ c hc
  have h2 := Work.OddRadon.radonProfile_eq_abelTrans' n hn (gammaDelta_even n ρ) hc.1
  have hS : (2 * Work.OddRadon.sphereArea (2 * n - 2)) ≠ 0 :=
    mul_ne_zero (by norm_num) (ne_of_gt (Work.OddRadon.sphereArea_pos _))
  have hc0 : c ^ (2 * n - 2) ≠ 0 := pow_ne_zero _ (ne_of_gt hc.1)
  have hAb : (2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2)
      * Work.OddRadon.radonProfile (2 * n + 1) (gammaDelta n ρ) c
      = Work.OddRadon.abelTrans ((n : ℝ) - 3 / 2) (gammaDelta n ρ) c := by
    rw [h2]
    exact datum_cancel (2 * n - 2) hS hc0
  have hEq : (2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2)
      * Work.OddCurve.LowSlope.deltaA n ρ c
      = (2 * Work.OddRadon.sphereArea (2 * n - 2))⁻¹ * c ^ (2 * n - 2)
        * Work.OddRadon.radonProfile (2 * n + 1) (gammaDelta n ρ) c := h1.trans hAb.symm
  exact mul_left_cancel₀ (mul_ne_zero (inv_ne_zero hS) hc0) hEq

private lemma radonInverse_deltaA_cap_priv (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ∀ u ∈ Set.Ioo (0 : ℝ) (4 / 5),
      Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) u
        = u ^ 2 / 2 * (ρ u ^ (2 * n + 2) + ρ (-u) ^ (2 * n + 2)) - u ^ 2 := by
  intro u hu
  have hcongr := Work.OddCurve.LowSlope.radonInverse_congr_of_eqOn (n := n) hu.1 hu.2
    (F := Work.OddCurve.LowSlope.deltaA n ρ)
    (G := Work.OddRadon.radonProfile (2 * n + 1) (gammaDelta n ρ))
    (fun c hc => deltaA_eq_radonProfile_cap n hn hρ c hc)
  rw [hcongr]
  have hc₀ : 0 < (u + 4 / 5) / 2 := by linarith [hu.1]
  have hc₀c₁ : (u + 4 / 5) / 2 < 4 / 5 := by linarith [hu.2]
  have hloc := Work.OddRadon.radonProfile_inv_local n hn hc₀ hc₀c₁ (by norm_num)
    (contDiffOn_gammaDelta_Icc n hρ) (gammaDelta_even n ρ) (u := u) ⟨hu.1, by linarith [hu.2]⟩
  rw [← hloc]
  rfl

/-- **The main identity below the glue point.** -/
private lemma main_cap (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ∀ u ∈ Set.Ioo (0 : ℝ) (4 / 5),
      Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ) u - u ^ 2
        = Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) u := by
  intro u hu
  rw [radonInverse_GlueF_cap n hn hρ u hu, radonInverse_deltaA_cap_priv n hn hρ u hu]


/-! ## The ball identity `radonInverse n (ballPhiData n) u = u²` -/

/-- The elementary Abel integral `∫_0^v c³/√(v²-c²) dc = (2/3)v³`. -/
private lemma integral_cube_abel (v : ℝ) (hv : 0 < v) :
    (∫ c in (0 : ℝ)..v, c * c ^ 2 / Real.sqrt (v ^ 2 - c ^ 2)) = (2 : ℝ) / 3 * v ^ 3 := by
  rw [Work.OddCurve.LowSlope.abel_integral_trig_substitution_no_hyp (Φ := fun c : ℝ => c ^ 2) hv]
  have h2 : (∫ θ in (0 : ℝ)..(Real.pi / 2), v * Real.sin θ * (v * Real.sin θ) ^ 2)
      = v ^ 3 * ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ ^ 3 := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _; ring
  rw [h2]
  have h3 : (∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ ^ 3) = 2 / 3 := by
    have hsin1 : (∫ x in (0 : ℝ)..(Real.pi / 2), Real.sin x ^ (1 : ℕ)) = 1 := by
      simpa using integral_sin (a := (0 : ℝ)) (b := (Real.pi / 2))
    have h := integral_sin_pow (a := (0 : ℝ)) (b := (Real.pi / 2)) (n := 1)
    rw [hsin1] at h
    rw [show Real.sin 0 = 0 by simp, show Real.sin (Real.pi / 2) = 1 by simp,
      show Real.cos 0 = 1 by simp, show Real.cos (Real.pi / 2) = 0 by simp] at h
    rw [h]; norm_num
  rw [h3]; ring

private lemma radonInverse_ballPhiData_priv (n : ℕ) (hn : 1 ≤ n) {u : ℝ} (hu : 0 < u)
    (hu1 : u ≤ 1) :
    Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.ballPhiData n) u = u ^ 2 := by
  have hJB : ∀ v ∈ Set.Ioo (0 : ℝ) 2,
      (∫ c in (0 : ℝ)..v, c * redDat n (Work.OddCurve.LowSlope.ballPhiData n) c
          / Real.sqrt (v ^ 2 - c ^ 2)) = Real.pi / 4 * ((2 : ℝ) / 3) * v ^ 3 := by
    intro v hv
    have h₁ : (∫ c in (0 : ℝ)..v, c * redDat n (Work.OddCurve.LowSlope.ballPhiData n) c
          / Real.sqrt (v ^ 2 - c ^ 2))
        = ∫ c in (0 : ℝ)..v, Real.pi / 4 * (c * c ^ 2 / Real.sqrt (v ^ 2 - c ^ 2)) := by
      apply intervalIntegral.integral_congr
      intro c hc
      rw [Set.uIcc_of_le hv.1.le] at hc
      rcases eq_or_lt_of_le hc.1 with h0 | h0
      · subst h0; ring
      · show c * redDat n (Work.OddCurve.LowSlope.ballPhiData n) c / Real.sqrt (v ^ 2 - c ^ 2)
            = Real.pi / 4 * (c * c ^ 2 / Real.sqrt (v ^ 2 - c ^ 2))
        rw [redDat_ball_eq_pi n hn c ⟨h0, lt_of_le_of_lt hc.2 hv.2⟩]
        ring
    rw [h₁, intervalIntegral.integral_const_mul, integral_cube_abel v hv.1]
    ring
  rw [Work.OddRadon.radonInverse_eq]
  show 2 / Real.pi * deriv (fun v : ℝ => ∫ c in (0 : ℝ)..v,
      c * redDat n (Work.OddCurve.LowSlope.ballPhiData n) c / Real.sqrt (v ^ 2 - c ^ 2)) u = u ^ 2
  have hderiv : deriv (fun v : ℝ => ∫ c in (0 : ℝ)..v,
        c * redDat n (Work.OddCurve.LowSlope.ballPhiData n) c / Real.sqrt (v ^ 2 - c ^ 2)) u
      = Real.pi / 2 * u ^ 2 := by
    have hev : (fun v : ℝ => ∫ c in (0 : ℝ)..v,
          c * redDat n (Work.OddCurve.LowSlope.ballPhiData n) c / Real.sqrt (v ^ 2 - c ^ 2))
        =ᶠ[𝓝 u] fun v : ℝ => Real.pi / 4 * ((2 : ℝ) / 3) * v ^ 3 := by
      filter_upwards [isOpen_Ioo.mem_nhds
        (show u ∈ Set.Ioo (0 : ℝ) 2 from ⟨hu, by linarith [hu1]⟩)] with v hv
      exact hJB v hv
    rw [hev.deriv_eq]
    have hd : HasDerivAt (fun v : ℝ => Real.pi / 4 * ((2 : ℝ) / 3) * v ^ 3)
        (Real.pi / 4 * ((2 : ℝ) / 3) * (3 * u ^ 2)) u := by
      simpa using (hasDerivAt_pow 3 u).const_mul (Real.pi / 4 * ((2 : ℝ) / 3))
    rw [hd.deriv]
    ring
  rw [hderiv]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp


/-! ## The Abel integrals of the three reduced data -/

/-- A.e. equality from pointwise equality away from a single point. -/
private lemma ae_forall_eq_of_eq_of_ne_singleton {f g : ℝ → ℝ} {p b : ℝ}
    (h : ∀ x ∈ Set.uIoc (0 : ℝ) b, x ≠ p → f x = g x) :
    ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (0 : ℝ) b → f x = g x := by
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun x hx => ?_) (measure_singleton p)
  simp only [Set.mem_setOf_eq] at hx
  by_contra hne
  exact hx (fun hmem => h x hmem hne)

/-- **The Abel integral of the deviation datum is a parametric integral on the cap.** -/
private lemma integral_deltaA_form (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) {v : ℝ}
    (hv : 4 / 5 < v) :
    (∫ c in (0 : ℝ)..v, c * redDat n (Work.OddCurve.LowSlope.deltaA n ρ) c
        / Real.sqrt (v ^ 2 - c ^ 2))
      = ∫ c in (0 : ℝ)..(4 / 5), c * Work.OddRadon.abelTrans (-(1 / 2)) (gammaDelta n ρ) c
          / Real.sqrt (v ^ 2 - c ^ 2) := by
  have hv0 : (0 : ℝ) < v := by linarith
  rw [intervalIntegral.integral_of_le hv0.le]
  have hsub : Set.Ioc (0 : ℝ) (4 / 5) ⊆ Set.Ioc (0 : ℝ) v :=
    fun x hx => ⟨hx.1, le_of_lt (lt_of_le_of_lt hx.2 hv)⟩
  have hzero : ∀ x ∈ Set.Ioc (0 : ℝ) v \ Set.Ioc (0 : ℝ) (4 / 5),
      x * redDat n (Work.OddCurve.LowSlope.deltaA n ρ) x / Real.sqrt (v ^ 2 - x ^ 2) = 0 := by
    intro x hx
    have hx' : 4 / 5 < x := by
      simp only [Set.mem_sdiff, Set.mem_Ioc, not_and, not_le] at hx
      exact hx.2 hx.1.1
    rw [redDat_deltaA_eq_zero hx', mul_zero, zero_div]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc hsub hzero]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 4 / 5)]
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (0 : ℝ) (4 / 5) →
      (fun c : ℝ => c * redDat n (Work.OddCurve.LowSlope.deltaA n ρ) c
          / Real.sqrt (v ^ 2 - c ^ 2)) x
        = (fun c : ℝ => c * Work.OddRadon.abelTrans (-(1 / 2)) (gammaDelta n ρ) c
            / Real.sqrt (v ^ 2 - c ^ 2)) x := by
    refine ae_forall_eq_of_eq_of_ne_singleton (p := 4 / 5) (b := 4 / 5) (fun x hx hne => ?_)
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 4/5)] at hx
    rw [redDat_deltaA_cap n hn hρ x ⟨hx.1, lt_of_le_of_ne hx.2 hne⟩]
  exact intervalIntegral.integral_congr_ae hae

/-- **The Abel integral of the ball's reduced datum is `(π/6)v³`.** -/
private lemma integral_ball_cubic (n : ℕ) (hn : 1 ≤ n) {v : ℝ} (hv : v ∈ Set.Ioo (0 : ℝ) 2) :
    (∫ c in (0 : ℝ)..v, c * redDat n (Work.OddCurve.LowSlope.ballPhiData n) c
        / Real.sqrt (v ^ 2 - c ^ 2)) = Real.pi / 6 * v ^ 3 := by
  have h₁ : (∫ c in (0 : ℝ)..v, c * redDat n (Work.OddCurve.LowSlope.ballPhiData n) c
        / Real.sqrt (v ^ 2 - c ^ 2))
      = ∫ c in (0 : ℝ)..v, Real.pi / 4 * (c * c ^ 2 / Real.sqrt (v ^ 2 - c ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro c hc
    rw [Set.uIcc_of_le hv.1.le] at hc
    rcases eq_or_lt_of_le hc.1 with h0 | h0
    · subst h0; ring
    · beta_reduce
      rw [redDat_ball_eq_pi n hn c ⟨h0, lt_of_le_of_lt hc.2 hv.2⟩]
      ring
  rw [h₁, intervalIntegral.integral_const_mul, integral_cube_abel v hv.1]
  ring

private lemma continuousOn_abelTrans_gammaDelta_uIcc (n : ℕ) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ContinuousOn (fun c : ℝ => Work.OddRadon.abelTrans (-(1 / 2)) (gammaDelta n ρ) c)
      (Set.uIcc 0 (4 / 5)) :=
  (continuousOn_abelTrans_negHalf (a := 4/5) (by norm_num)
    ((continuousOn_gammaDelta_Icc n hρ).mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩))
    (gammaDelta_zero n ρ)).mono (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 4/5)])

private lemma continuousOn_abelTrans_gammaAnchor_uIcc (n : ℕ) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ContinuousOn (fun c : ℝ => Work.OddRadon.abelTrans (-(1 / 2)) (gammaAnchor n ρ) c)
      (Set.uIcc 0 (4 / 5)) :=
  (continuousOn_abelTrans_negHalf (a := 4/5) (by norm_num)
    ((continuousOn_gammaAnchor_Icc n hρ).mono (fun x hx => ⟨hx.1, by linarith [hx.2]⟩))
    (gammaAnchor_zero n ρ)).mono (by rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 4/5)])

/-- **The Abel integrand of the deviation datum is interval integrable** (`v > 4/5`). -/
private lemma intervalIntegrable_deltaA_integrand (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) {v : ℝ}
    (hv : 4 / 5 < v) :
    IntervalIntegrable (fun c : ℝ => c * redDat n (Work.OddCurve.LowSlope.deltaA n ρ) c
      / Real.sqrt (v ^ 2 - c ^ 2)) volume 0 v := by
  have hv0 : (0 : ℝ) < v := by linarith
  have hdenpos : ∀ c ∈ Set.uIcc (0 : ℝ) (4 / 5), 0 < v ^ 2 - c ^ 2 := by
    intro c hc
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 4 / 5)] at hc
    nlinarith [hc.1, hc.2, hv]
  have hnum : ContinuousOn
      (fun c : ℝ => c * Work.OddRadon.abelTrans (-(1 / 2)) (gammaDelta n ρ) c)
      (Set.uIcc (0 : ℝ) (4 / 5)) :=
    continuousOn_id.mul (continuousOn_abelTrans_gammaDelta_uIcc n hρ)
  have hden : ContinuousOn (fun c : ℝ => Real.sqrt (v ^ 2 - c ^ 2)) (Set.uIcc (0 : ℝ) (4 / 5)) :=
    Real.continuous_sqrt.comp_continuousOn (continuousOn_const.sub (continuousOn_id.pow 2))
  have hcont : ContinuousOn (fun c : ℝ =>
      c * Work.OddRadon.abelTrans (-(1 / 2)) (gammaDelta n ρ) c / Real.sqrt (v ^ 2 - c ^ 2))
      (Set.uIcc (0 : ℝ) (4 / 5)) :=
    hnum.div hden (fun c hc => ne_of_gt (Real.sqrt_pos.mpr (hdenpos c hc)))
  have hcap : IntervalIntegrable (fun c : ℝ =>
      c * redDat n (Work.OddCurve.LowSlope.deltaA n ρ) c / Real.sqrt (v ^ 2 - c ^ 2))
      volume 0 (4 / 5) :=
    hcont.intervalIntegrable.congr_uIoo (fun x hx => by
      rw [Set.uIoo_of_le (by norm_num : (0 : ℝ) ≤ 4 / 5), Set.mem_Ioo] at hx
      beta_reduce
      rw [redDat_deltaA_cap n hn hρ x hx])
  have habove : IntervalIntegrable (fun c : ℝ =>
      c * redDat n (Work.OddCurve.LowSlope.deltaA n ρ) c / Real.sqrt (v ^ 2 - c ^ 2))
      volume (4 / 5) v :=
    IntervalIntegrable.zero.congr (fun x hx => by
      rw [Pi.zero_apply]
      rw [Set.uIoc_of_le (by linarith : (4 / 5 : ℝ) ≤ v)] at hx
      rw [redDat_deltaA_eq_zero hx.1, mul_zero, zero_div])
  exact hcap.trans habove

/-- **The Abel integrand of the ball's reduced datum is interval integrable** (`0 < v < 2`). -/
private lemma intervalIntegrable_ball_integrand (n : ℕ) (hn : 1 ≤ n) {v : ℝ} (hv0 : 0 < v)
    (hv2 : v < 2) :
    IntervalIntegrable (fun c : ℝ => c * redDat n (Work.OddCurve.LowSlope.ballPhiData n) c
      / Real.sqrt (v ^ 2 - c ^ 2)) volume 0 v := by
  have hnice : IntervalIntegrable (fun c : ℝ => c * (Real.pi / 4 * c ^ 2)
      / Real.sqrt (v ^ 2 - c ^ 2)) volume 0 v := by
    have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (f := fun θ : ℝ => v * Real.sin θ) (f' := fun θ : ℝ => v * Real.cos θ)
      (g := fun c : ℝ => c * (Real.pi / 4 * c ^ 2) / Real.sqrt (v ^ 2 - c ^ 2))
      (a := (0 : ℝ)) (b := Real.pi / 2)
      ((continuous_const.mul Real.continuous_sin).continuousOn)
      (by
        intro x hx
        rw [min_eq_left (by positivity : (0 : ℝ) ≤ Real.pi / 2),
          max_eq_right (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hx
        exact (Real.hasDerivAt_sin x).const_mul v)
      (by
        intro x hx
        rw [min_eq_left (by positivity : (0 : ℝ) ≤ Real.pi / 2),
          max_eq_right (by positivity : (0 : ℝ) ≤ Real.pi / 2)] at hx
        exact mul_nonneg hv0.le (Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [Real.pi_pos, hx.1], by linarith [Real.pi_pos, hx.2]⟩))
    have hθside : IntervalIntegrable (fun θ : ℝ =>
        ((fun c : ℝ => c * (Real.pi / 4 * c ^ 2) / Real.sqrt (v ^ 2 - c ^ 2))
          ∘ fun θ : ℝ => v * Real.sin θ) θ * (v * Real.cos θ)) volume 0 (Real.pi / 2) := by
      have hcont : Continuous fun θ : ℝ => v ^ 3 * Real.sin θ ^ 3 * (Real.pi / 4) := by fun_prop
      refine (hcont.intervalIntegrable 0 (Real.pi / 2)).congr_uIoo (fun θ hθ => ?_)
      simp only [Set.uIoo_of_le (by positivity : (0 : ℝ) ≤ Real.pi / 2), Set.mem_Ioo] at hθ
      have hcospos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hθ.1],
        by linarith [Real.pi_pos, hθ.2]⟩
      have hsq : v ^ 2 - (v * Real.sin θ) ^ 2 = (v * Real.cos θ) ^ 2 := by
        nlinarith [Real.sin_sq_add_cos_sq θ]
      have hsqrt : Real.sqrt (v ^ 2 - (v * Real.sin θ) ^ 2) = v * Real.cos θ := by
        rw [hsq, Real.sqrt_sq (by positivity)]
      simp only [Function.comp_apply]
      rw [hsqrt]
      field_simp
    have hfinal := hiff.mp hθside
    simpa [Real.sin_zero, Real.sin_pi_div_two, mul_zero, mul_one] using hfinal
  refine hnice.congr_uIoo (fun x hx => ?_)
  rw [Set.uIoo_of_le hv0.le, Set.mem_Ioo] at hx
  beta_reduce
  rw [redDat_ball_eq_pi n hn x ⟨hx.1, lt_trans hx.2 hv2⟩]

/-- **`J(GlueF) = J(deltaA) + J(ball)` on `(4/5,2)`.** -/
private lemma integral_GlueF_eq_add (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) {v : ℝ}
    (hv : v ∈ Set.Ioo (4 / 5 : ℝ) 2) :
    (∫ c in (0 : ℝ)..v, c * redDat n (Work.OddCurve.LowSlope.GlueF n ρ) c
        / Real.sqrt (v ^ 2 - c ^ 2))
      = (∫ c in (0 : ℝ)..v, c * redDat n (Work.OddCurve.LowSlope.deltaA n ρ) c
          / Real.sqrt (v ^ 2 - c ^ 2))
        + ∫ c in (0 : ℝ)..v, c * redDat n (Work.OddCurve.LowSlope.ballPhiData n) c
            / Real.sqrt (v ^ 2 - c ^ 2) := by
  have hv0 : (0 : ℝ) < v := by linarith [hv.1]
  have hAint := intervalIntegrable_deltaA_integrand n hn hρ hv.1
  have hBint := intervalIntegrable_ball_integrand n hn hv0 hv.2
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Set.uIoc (0 : ℝ) v →
      (fun c : ℝ => c * redDat n (Work.OddCurve.LowSlope.GlueF n ρ) c
        / Real.sqrt (v ^ 2 - c ^ 2)) x
      = (fun c : ℝ => c * redDat n (Work.OddCurve.LowSlope.deltaA n ρ) c
          / Real.sqrt (v ^ 2 - c ^ 2)
        + c * redDat n (Work.OddCurve.LowSlope.ballPhiData n) c / Real.sqrt (v ^ 2 - c ^ 2)) x := by
    refine ae_forall_eq_of_eq_of_ne_singleton (p := 4 / 5) (b := v) (fun x hx hne => ?_)
    rw [Set.uIoc_of_le hv0.le] at hx
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [redDat_add_cap n hn hρ x ⟨hx.1, hlt⟩]
      ring
    · rw [redDat_GlueF_eq_redDat_ball hgt, redDat_deltaA_eq_zero hgt]
      ring
  rw [intervalIntegral.integral_congr_ae hae,
    intervalIntegral.integral_add hAint hBint]


/-! ## Differentiation of the shifted Abel integral -/

private lemma hasDerivAt_abelShift_integral_priv {a U : ℝ} (ha : 0 < a) (haU : a < U)
    {H : ℝ → ℝ} (hH : ContinuousOn H (Set.Icc 0 a)) :
    HasDerivAt (fun v : ℝ => ∫ c in (0 : ℝ)..a, H c / Real.sqrt (v ^ 2 - c ^ 2))
      (∫ c in (0 : ℝ)..a, H c * (-U / Real.sqrt (U ^ 2 - c ^ 2) ^ 3)) U := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hH
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, le_of_lt ha⟩)
  set δ : ℝ := (U - a) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set s : Set ℝ := Set.Ioo (U - δ) (U + δ) with hs
  have hs_mem : s ∈ 𝓝 U := by
    rw [hs]; exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hs_lower : ∀ v ∈ s, a < v := by
    intro v hv
    rw [hs] at hv; rw [hδ] at hv
    linarith [hv.1]
  have hbase_pos : 0 < (U - δ) ^ 2 - a ^ 2 := by
    rw [hδ]; nlinarith [ha, haU]
  have hbase3 : 0 < ((U - δ) ^ 2 - a ^ 2) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hbase_pos _
  have hden : ∀ v ∈ s, ∀ c ∈ Set.Icc (0 : ℝ) a, 0 < v ^ 2 - c ^ 2 := by
    intro v hv c hc
    have hv1 : a < v := hs_lower v hv
    nlinarith [hc.1, hc.2, hv1]
  have hsqrt_ne : ∀ c ∈ Set.Icc (0 : ℝ) a, Real.sqrt (U ^ 2 - c ^ 2) ≠ 0 := by
    intro c hc
    exact ne_of_gt (Real.sqrt_pos.mpr (by nlinarith [hc.1, hc.2, ha, haU]))
  have hF_meas : ∀ᶠ v : ℝ in 𝓝 U,
      AEStronglyMeasurable (fun c : ℝ => H c / Real.sqrt (v ^ 2 - c ^ 2))
        (volume.restrict (Set.uIoc (0 : ℝ) a)) := by
    filter_upwards [hs_mem] with v hv
    have hcont : ContinuousOn (fun c : ℝ => H c / Real.sqrt (v ^ 2 - c ^ 2))
        (Set.uIcc (0 : ℝ) a) := by
      rw [Set.uIcc_of_le ha.le]
      refine ContinuousOn.div hH ?_ ?_
      · exact Real.continuous_sqrt.comp_continuousOn
          (continuousOn_const.sub (continuousOn_id.pow 2))
      · intro c hc
        exact ne_of_gt (Real.sqrt_pos.mpr (hden v hv c hc))
    exact (hcont.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  have hF_int : IntervalIntegrable (fun c : ℝ => H c / Real.sqrt (U ^ 2 - c ^ 2))
      volume (0 : ℝ) a := by
    have hcont : ContinuousOn (fun c : ℝ => H c / Real.sqrt (U ^ 2 - c ^ 2))
        (Set.uIcc (0:ℝ) a) := by
      rw [Set.uIcc_of_le ha.le]
      exact ContinuousOn.div hH (Real.continuous_sqrt.comp_continuousOn
        (continuousOn_const.sub (continuousOn_id.pow 2))) hsqrt_ne
    exact hcont.intervalIntegrable
  have hF'_meas : AEStronglyMeasurable
      (fun c : ℝ => H c * (-U / Real.sqrt (U ^ 2 - c ^ 2) ^ 3))
      (volume.restrict (Set.uIoc (0 : ℝ) a)) := by
    have hcont : ContinuousOn (fun c : ℝ => H c * (-U / Real.sqrt (U ^ 2 - c ^ 2) ^ 3))
        (Set.uIcc (0 : ℝ) a) := by
      rw [Set.uIcc_of_le ha.le]
      refine ContinuousOn.mul hH ?_
      refine ContinuousOn.div continuousOn_const (ContinuousOn.pow ?_ 3) ?_
      · exact Real.continuous_sqrt.comp_continuousOn
          (continuousOn_const.sub (continuousOn_id.pow 2))
      · intro c hc
        exact pow_ne_zero 3 (hsqrt_ne c hc)
    exact (hcont.mono Set.uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  set C : ℝ := M * (U + δ) / ((U - δ) ^ 2 - a ^ 2) ^ (3 / 2 : ℝ) with hC
  have hUδ : 0 < U + δ := by linarith [hδpos, haU]
  have h_bound : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) a → ∀ x ∈ s,
      ‖H t * (-x / Real.sqrt (x ^ 2 - t ^ 2) ^ 3)‖ ≤ (fun _ : ℝ => C) t := by
    filter_upwards with t ht x hx
    have ht' : 0 ≤ t ∧ t ≤ a := by
      rw [Set.uIoc_of_le ha.le] at ht; exact ⟨ht.1.le, ht.2⟩
    have hxgt : a < x := hs_lower x hx
    have hdenpos : 0 < x ^ 2 - t ^ 2 := by nlinarith [ht'.1, ht'.2, hxgt]
    have hxle : x < U + δ := by rw [hs] at hx; exact hx.2
    have hxge : U - δ < x := by rw [hs] at hx; exact hx.1
    have hxabs : |x| ≤ U + δ := by
      rw [abs_of_pos (lt_trans ha hxgt)]; exact hxle.le
    have hsqrt_eq : Real.sqrt (x ^ 2 - t ^ 2) ^ 3 = (x ^ 2 - t ^ 2) ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ((x ^ 2 - t ^ 2) ^ (1 / 2 : ℝ)) 3,
        ← Real.rpow_mul hdenpos.le]
      norm_num
    have hxge' : 0 < U - δ := by rw [hδ]; linarith [ha]
    have hden_le : ((U - δ) ^ 2 - a ^ 2) ^ (3 / 2 : ℝ) ≤ (x ^ 2 - t ^ 2) ^ (3 / 2 : ℝ) :=
      Real.rpow_le_rpow hbase_pos.le (by nlinarith [hxge, hxge', ht'.2]) (by norm_num)
    have hMabs : |H t| ≤ M := by simpa using hM t ⟨ht'.1, ht'.2⟩
    have h2 : |x| / (x ^ 2 - t ^ 2) ^ (3 / 2 : ℝ)
        ≤ (U + δ) / ((U - δ) ^ 2 - a ^ 2) ^ (3 / 2 : ℝ) := by
      have h1 : |x| / (x ^ 2 - t ^ 2) ^ (3 / 2 : ℝ)
          ≤ (U + δ) / (x ^ 2 - t ^ 2) ^ (3 / 2 : ℝ) :=
        div_le_div_of_nonneg_right hxabs (Real.rpow_nonneg hdenpos.le _)
      exact le_trans h1 (div_le_div_of_nonneg_left hUδ.le hbase3 hden_le)
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, hsqrt_eq,
      abs_of_pos (Real.rpow_pos_of_pos hdenpos _), hC]
    calc |H t| * (|x| / (x ^ 2 - t ^ 2) ^ (3 / 2 : ℝ))
        ≤ M * ((U + δ) / ((U - δ) ^ 2 - a ^ 2) ^ (3 / 2 : ℝ)) :=
          mul_le_mul hMabs h2 (div_nonneg (abs_nonneg _) (Real.rpow_nonneg hdenpos.le _)) hM0
      _ = M * (U + δ) / ((U - δ) ^ 2 - a ^ 2) ^ (3 / 2 : ℝ) := by ring
  have hbound_int : IntervalIntegrable (fun _ : ℝ => C) volume (0 : ℝ) a :=
    intervalIntegrable_const
  have h_diff : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ∈ Set.uIoc (0 : ℝ) a → ∀ x ∈ s,
      HasDerivAt (fun v : ℝ => H t / Real.sqrt (v ^ 2 - t ^ 2))
        (H t * (-x / Real.sqrt (x ^ 2 - t ^ 2) ^ 3)) x := by
    filter_upwards with t ht x hx
    have ht' : 0 < t ∧ t ≤ a := by
      rw [Set.uIoc_of_le ha.le] at ht; exact ht
    have hxgt : a < x := hs_lower x hx
    have hdenpos : 0 < x ^ 2 - t ^ 2 := by nlinarith [ht'.1, ht'.2, hxgt]
    have hsq : HasDerivAt (fun v : ℝ => v ^ 2 - t ^ 2) (2 * x) x := by
      simpa using ((hasDerivAt_pow 2 x).sub_const (t ^ 2))
    have hsqrt' := hsq.sqrt (ne_of_gt hdenpos)
    have hdiv := (hasDerivAt_const x (H t)).div hsqrt' (ne_of_gt (Real.sqrt_pos.mpr hdenpos))
    refine hdiv.congr_deriv ?_
    have hsqr : Real.sqrt (x ^ 2 - t ^ 2) ^ 2 = x ^ 2 - t ^ 2 := Real.sq_sqrt hdenpos.le
    field_simp
    rw [hsqr]
    ring
  have hmain := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := a) (x₀ := U) (s := s)
    (F := fun v c => H c / Real.sqrt (v ^ 2 - c ^ 2))
    (F' := fun v c => H c * (-v / Real.sqrt (v ^ 2 - c ^ 2) ^ 3))
    (bound := fun _ : ℝ => C)
    hs_mem hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  exact hmain.2



/-! ## The main identity above the glue point -/

private lemma main_above (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) {u : ℝ}
    (hu : 4 / 5 < u) (hu1 : u ≤ 1) :
    Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ) u - u ^ 2
      = Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) u := by
  have hu2 : u < 2 := by linarith
  have hu0 : 0 < u := by linarith
  have hcontIcc : ContinuousOn
      (fun c : ℝ => c * Work.OddRadon.abelTrans (-(1 / 2)) (gammaDelta n ρ) c)
      (Set.Icc 0 (4 / 5)) :=
    (continuousOn_id.mul (continuousOn_abelTrans_gammaDelta_uIcc n hρ)).mono
      (by rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 4 / 5)])
  have hderivA0 := hasDerivAt_abelShift_integral_priv (a := 4 / 5) (U := u) (by norm_num) hu hcontIcc
  have hAeq : (fun v : ℝ => ∫ c in (0 : ℝ)..(4 / 5),
        c * Work.OddRadon.abelTrans (-(1 / 2)) (gammaDelta n ρ) c / Real.sqrt (v ^ 2 - c ^ 2))
      =ᶠ[𝓝 u] (fun v : ℝ => ∫ c in (0 : ℝ)..v,
        c * redDat n (Work.OddCurve.LowSlope.deltaA n ρ) c / Real.sqrt (v ^ 2 - c ^ 2)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hu] with v hv
    exact (integral_deltaA_form n hn hρ hv).symm
  have hderivA : HasDerivAt (fun v : ℝ => ∫ c in (0 : ℝ)..v,
      c * redDat n (Work.OddCurve.LowSlope.deltaA n ρ) c / Real.sqrt (v ^ 2 - c ^ 2))
      (∫ c in (0 : ℝ)..(4 / 5),
        c * Work.OddRadon.abelTrans (-(1 / 2)) (gammaDelta n ρ) c
          * (-u / Real.sqrt (u ^ 2 - c ^ 2) ^ 3)) u :=
    hderivA0.congr_of_eventuallyEq hAeq.symm
  have hBeq : (fun v : ℝ => ∫ c in (0 : ℝ)..v,
        c * redDat n (Work.OddCurve.LowSlope.ballPhiData n) c / Real.sqrt (v ^ 2 - c ^ 2))
      =ᶠ[𝓝 u] fun v : ℝ => Real.pi / 6 * v ^ 3 := by
    filter_upwards [isOpen_Ioo.mem_nhds (show u ∈ Set.Ioo (0 : ℝ) 2 from ⟨hu0, hu2⟩)] with v hv
    exact integral_ball_cubic n hn hv
  have hderivB : HasDerivAt (fun v : ℝ => ∫ c in (0 : ℝ)..v,
      c * redDat n (Work.OddCurve.LowSlope.ballPhiData n) c / Real.sqrt (v ^ 2 - c ^ 2))
      (Real.pi / 2 * u ^ 2) u := by
    have hd : HasDerivAt (fun v : ℝ => Real.pi / 6 * v ^ 3) (Real.pi / 6 * (3 * u ^ 2)) u := by
      simpa using (hasDerivAt_pow 3 u).const_mul (Real.pi / 6)
    have hd' := hd.congr_of_eventuallyEq hBeq
    have heq : Real.pi / 6 * (3 * u ^ 2) = Real.pi / 2 * u ^ 2 := by ring
    rwa [heq] at hd'
  have hGeq : (fun v : ℝ => ∫ c in (0 : ℝ)..v,
        c * redDat n (Work.OddCurve.LowSlope.GlueF n ρ) c / Real.sqrt (v ^ 2 - c ^ 2))
      =ᶠ[𝓝 u] ((fun v : ℝ => ∫ c in (0 : ℝ)..v,
          c * redDat n (Work.OddCurve.LowSlope.deltaA n ρ) c / Real.sqrt (v ^ 2 - c ^ 2))
        + fun v : ℝ => ∫ c in (0 : ℝ)..v, c * redDat n (Work.OddCurve.LowSlope.ballPhiData n) c
            / Real.sqrt (v ^ 2 - c ^ 2)) := by
    filter_upwards [isOpen_Ioo.mem_nhds (show u ∈ Set.Ioo (4 / 5 : ℝ) 2 from ⟨hu, hu2⟩)]
      with v hv
    exact integral_GlueF_eq_add n hn hρ hv
  have key : deriv (fun v : ℝ => ∫ c in (0 : ℝ)..v,
      c * redDat n (Work.OddCurve.LowSlope.GlueF n ρ) c / Real.sqrt (v ^ 2 - c ^ 2)) u
      = deriv (fun v : ℝ => ∫ c in (0 : ℝ)..v,
          c * redDat n (Work.OddCurve.LowSlope.deltaA n ρ) c / Real.sqrt (v ^ 2 - c ^ 2)) u
        + Real.pi / 2 * u ^ 2 := by
    rw [hGeq.deriv_eq, deriv_add hderivA.differentiableAt hderivB.differentiableAt,
      hderivA.deriv, hderivB.deriv]
  rw [Work.OddRadon.radonInverse_eq n (Work.OddCurve.LowSlope.GlueF n ρ) u,
    Work.OddRadon.radonInverse_eq n (Work.OddCurve.LowSlope.deltaA n ρ) u]
  show (2 / Real.pi) * deriv (fun v : ℝ => ∫ c in (0 : ℝ)..v,
      c * redDat n (Work.OddCurve.LowSlope.GlueF n ρ) c / Real.sqrt (v ^ 2 - c ^ 2)) u - u ^ 2
    = (2 / Real.pi) * deriv (fun v : ℝ => ∫ c in (0 : ℝ)..v,
      c * redDat n (Work.OddCurve.LowSlope.deltaA n ρ) c / Real.sqrt (v ^ 2 - c ^ 2)) u
  rw [key]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring


/-- **The deviation of the two-power system is the inverse Radon transform of the glued datum
deviation.**  `glueA` is the anchor's radial-function combination on the cap `cos α < 4/5` and
`GlueA = 2 𝓡^{-1}(GlueF)/cos² - 2` above it; the two pieces agree with `2 𝓡^{-1}(deltaA)/cos²`
because `radonInverse` is additive in the datum and inverts `ballPhiData` to `u²`. -/
theorem glueA_eq_inversion (n : ℕ) (hn : 1 ≤ n) {ρ : ℝ → ℝ}
    (hρ : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ (Set.Ioo (-1 : ℝ) 1)) :
    ∀ α : ℝ, 0 < Real.cos α → Real.cos α ≠ 4 / 5 →
      Work.OddCurve.LowSlope.glueA n ρ α =
        (2 * Work.OddRadon.radonInverse n
          (fun c : ℝ => Work.OddCurve.LowSlope.GlueF n ρ c -
            Work.OddCurve.LowSlope.ballPhiData n c) (Real.cos α))
          / Real.cos α ^ 2 := by
  intro α hcos hne
  have hdelta : (fun c : ℝ => Work.OddCurve.LowSlope.GlueF n ρ c
      - Work.OddCurve.LowSlope.ballPhiData n c) = Work.OddCurve.LowSlope.deltaA n ρ := rfl
  rw [hdelta]
  have hu0 : 0 < Real.cos α := hcos
  have hne0 : Real.cos α ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt hu0)
  rcases lt_or_ge (Real.cos α) (4 / 5) with hlt | hge
  · -- on the cap: `glueA` is the anchor's radial-function combination
    rw [Work.OddCurve.LowSlope.glueA_of_lt hlt]
    have hRA := radonInverse_deltaA_cap_priv n hn hρ (Real.cos α) ⟨hu0, hlt⟩
    rw [hRA]
    field_simp
  · -- above the glue point: `glueA = GlueA` is the glued datum's deviation
    have hlt' : 4 / 5 < Real.cos α := lt_of_le_of_ne hge (Ne.symm hne)
    have hu1 : Real.cos α ≤ 1 := Real.cos_le_one α
    rw [Work.OddCurve.LowSlope.glueA_of_ge hge]
    have hmain : Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.GlueF n ρ) (Real.cos α)
          - Real.cos α ^ 2
        = Work.OddRadon.radonInverse n (Work.OddCurve.LowSlope.deltaA n ρ) (Real.cos α) :=
      main_above n hn hρ hlt' hu1
    rw [Work.OddCurve.LowSlope.GlueA, Work.OddCurve.LowSlope.GluePhi]
    rw [← hmain]
    field_simp

end

end Work.OddVolterra.Free
