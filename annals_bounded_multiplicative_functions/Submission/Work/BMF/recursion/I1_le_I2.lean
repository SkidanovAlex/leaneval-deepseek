import Mathlib
import Submission.Work.BMF.recursion.Defs
import Submission.Work.BMF.recursion.I1I2Defs
import Submission.Work.BMF.recursion.Weyl_factor
import Submission.Work.BMF.recursion.integral_normSq_eq_card
import Submission.Work.BMF.recursion.norm_sum_pow_le
import Submission.Work.BMF.recursion.headtail_factor
import Submission.Work.BMF.recursion.I1_eq_integral
import Submission.Work.BMF.recursion.I2_eq_integral
import Submission.Work.BMF.recursion.weylmod_pow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.BMF.recursion

open scoped BigOperators
open MeasureTheory

noncomputable section

/-- A continuous `ℝ`-valued function on the compact torus is integrable. -/
lemma integrable_of_continuous {d : ℕ} {f : UnitAddTorus (Fin d) → ℝ} (hf : Continuous f) :
    Integrable f volume :=
  hf.integrable_of_hasCompactSupport (by
    unfold HasCompactSupport tsupport
    exact IsCompact.of_isClosed_subset isCompact_univ isClosed_closure (Set.subset_univ _))

/-- The head Weyl factor is continuous. -/
lemma continuous_Gw (p k Q : ℕ) : Continuous (Gw p k Q) := by
  show Continuous (fun θ : UnitAddTorus (Fin (k + 1)) =>
    ∑ a ∈ Ahead p k Q, UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k a) θ)
  exact continuous_finsetSum _ (fun a _ => (UnitAddTorus.mFourier _).continuous)

/-- The one-variable Weyl sum is continuous. -/
lemma continuous_Weyl (k Q : ℕ) : Continuous (Weyl k Q) := by
  show Continuous (fun θ : UnitAddTorus (Fin (k + 1)) =>
    ∑ x : Tup 1 Q, UnitAddTorus.mFourier (Submission.Vinogradov.powerSums k x) θ)
  exact continuous_finsetSum _ (fun x _ => (UnitAddTorus.mFourier _).continuous)

/-- The restricted Weyl sum is continuous. -/
lemma continuous_WeylMod (p k Q y : ℕ) : Continuous (WeylMod p k Q y) := by
  rw [show WeylMod p k Q y = fun θ : UnitAddTorus (Fin (k + 1)) =>
      ∑ x ∈ (Finset.Icc 1 Q).filter (fun x => x % p = y % p),
        UnitAddTorus.mFourier (mom1 k x) θ from by
    funext θ
    exact WeylMod_apply p k Q y θ]
  exact continuous_finsetSum _ (fun x _ => (UnitAddTorus.mFourier _).continuous)

/-- Continuity of the left-hand integrand of the Hölder step. -/
lemma continuous_integrand1 (p k Q m : ℕ) :
    Continuous (fun θ : UnitAddTorus (Fin (k + 1)) =>
      ‖Gw p k Q θ‖ ^ 2 * ‖Weyl k Q θ‖ ^ (2 * m)) :=
  ((continuous_Gw p k Q).norm.pow 2).mul ((continuous_Weyl k Q).norm.pow (2 * m))

/-- Continuity of the right-hand integrand of the Hölder step. -/
lemma continuous_integrand2 (p k Q m : ℕ) :
    Continuous (fun θ : UnitAddTorus (Fin (k + 1)) =>
      ‖Gw p k Q θ‖ ^ 2 * ((p : ℝ) ^ (2 * m - 1) *
        ∑ y ∈ Finset.range p, ‖WeylMod p k Q y θ‖ ^ (2 * m))) :=
  ((continuous_Gw p k Q).norm.pow 2).mul
    (continuous_const.mul (continuous_finsetSum _
      (fun y _ => ((continuous_WeylMod p k Q y).norm.pow (2 * m)))))

/-- Continuity of the individual summands of the right-hand integrand. -/
lemma continuous_integrandY (p k Q m y : ℕ) :
    Continuous (fun θ : UnitAddTorus (Fin (k + 1)) =>
      ‖Gw p k Q θ‖ ^ 2 * ‖WeylMod p k Q y θ‖ ^ (2 * m)) :=
  ((continuous_Gw p k Q).norm.pow 2).mul ((continuous_WeylMod p k Q y).norm.pow (2 * m))

/-- **Second Hölder step of the recursion** (Wooley, Michigan Math. J. **40** (1993), 175–180, §2,
case (b)).  `I1 S k Q p hkS` counts the matching pairs of `S`-tuples in `[1,Q]` whose heads (the
first `k` coordinates) are pairwise distinct modulo `p` on both sides; `I2 S k Q p y hkS` counts the
matching pairs whose heads are pairwise distinct mod `p` on both sides *and* whose `S-k` tail
coordinates are all `≡ y (mod p)`.  Then, for `1 ≤ p`,

`I1 ≤ p^{2(S-k)} · max_{y<p} I2(p,y)`.

Route.  By the general mean-value identity `integral_normSq_eq_card`, `I1` equals the integral over
the unit torus of `‖Σ_{x ∈ ι₁} e(θ·moments x)‖²` where `ι₁ = {x ∈ Tup S Q : HDp p k hkS x}`, and
similarly `I2(p,y)` is the integral for `ι₂(y) = {x ∈ ι₁ : TailEq p hkS y x}`.  Splitting each
`x ∈ ι₁` into its head (a tuple with pairwise distinct residues mod `p`) and its `S-k` tail
coordinates, and using additivity of the moment map, the integrand for `I1` factorises as
`‖G‖²·‖Weyl k Q‖^{2(S-k)}` and that for `I2(p,y)` as `‖G‖²·‖WeylMod p k Q y‖^{2(S-k)}`, with the
same `G`.  Since `Weyl k Q = Σ_{y<p} WeylMod p k Q y` (`Weyl_factor` helper (A)), the pointwise
power-mean inequality `‖Weyl‖^{2(S-k)} ≤ p^{2(S-k)-1}·Σ_{y<p}‖WeylMod y‖^{2(S-k)}` follows from
`norm_sum_pow_le`; integrating termwise (finite sums of continuous, hence integrable, integrands)
gives the claim, with `Finset.sup` over `range p` replacing the pointwise maximum.  The case
`2(S-k) = 0` (i.e. `S = k`) is trivial. -/
theorem I1_le_I2 (S k Q p : ℕ) (hkS : k ≤ S) (hp : 1 ≤ p) :
    (I1 S k Q p hkS : ℝ) ≤ (p : ℝ) ^ (2 * (S - k)) *
      (((Finset.range p).sup (fun y => I2 S k Q p y hkS) : ℕ) : ℝ) := by
  classical
  obtain ⟨hF1, hF2⟩ := headtail_factor S k Q p hkS
  have hI1 : (I1 S k Q p hkS : ℝ) = ∫ θ, ‖F1 S k Q p hkS θ‖ ^ 2 :=
    I1_eq_integral S k Q p hkS
  have hI2 : ∀ y : ℕ, (I2 S k Q p y hkS : ℝ) = ∫ θ, ‖F2 S k Q p y hkS θ‖ ^ 2 :=
    fun y => I2_eq_integral S k Q p y hkS
  have hW : ∀ θ : UnitAddTorus (Fin (k + 1)), ‖Weyl k Q θ‖ ^ (2 * (S - k)) ≤
      (p : ℝ) ^ (2 * (S - k) - 1) *
        ∑ y ∈ Finset.range p, ‖WeylMod p k Q y θ‖ ^ (2 * (S - k)) :=
    fun θ => weylmod_pow_le p k Q (S - k) hp θ
  by_cases hm0 : S - k = 0
  · have hG1 : F1 S k Q p hkS = Gw p k Q := by
      rw [hF1]
      funext θ
      rw [hm0, pow_zero, mul_one]
    have hG2 : ∀ y, F2 S k Q p y hkS = Gw p k Q := by
      intro y
      rw [hF2 y]
      funext θ
      rw [hm0, pow_zero, mul_one]
    have hII : ∀ y, I2 S k Q p y hkS = I1 S k Q p hkS := by
      intro y
      have h1 : (I2 S k Q p y hkS : ℝ) = (I1 S k Q p hkS : ℝ) := by
        rw [hI2 y, hI1, hG2 y, hG1]
      exact_mod_cast h1
    have hsup : (Finset.range p).sup (fun y => I2 S k Q p y hkS) = I1 S k Q p hkS := by
      apply le_antisymm
      · rw [Finset.sup_le_iff]
        intro y _
        exact le_of_eq (hII y)
      · have hy0 : 0 ∈ Finset.range p := Finset.mem_range.mpr (by omega)
        calc I1 S k Q p hkS = I2 S k Q p 0 hkS := (hII 0).symm
          _ ≤ (Finset.range p).sup (fun y => I2 S k Q p y hkS) :=
              Finset.le_sup (f := fun y => I2 S k Q p y hkS) hy0
    rw [hsup, hm0]
    simp
  · have hm : 1 ≤ S - k := by omega
    have hmain1 : (I1 S k Q p hkS : ℝ)
        = ∫ θ, ‖Gw p k Q θ‖ ^ 2 * ‖Weyl k Q θ‖ ^ (2 * (S - k)) := by
      rw [hI1]
      apply integral_congr_ae
      filter_upwards with θ
      rw [hF1]
      rw [norm_mul, norm_pow, mul_pow, ← pow_mul, Nat.mul_comm]
    have hmain2 : ∀ y, (I2 S k Q p y hkS : ℝ)
        = ∫ θ, ‖Gw p k Q θ‖ ^ 2 * ‖WeylMod p k Q y θ‖ ^ (2 * (S - k)) := by
      intro y
      rw [hI2 y]
      apply integral_congr_ae
      filter_upwards with θ
      rw [hF2 y]
      rw [norm_mul, norm_pow, mul_pow, ← pow_mul, Nat.mul_comm]
    have hsum : ∑ y ∈ Finset.range p, (I2 S k Q p y hkS : ℝ)
        ≤ (p : ℝ) * (((Finset.range p).sup (fun y => I2 S k Q p y hkS) : ℕ) : ℝ) := by
      calc ∑ y ∈ Finset.range p, (I2 S k Q p y hkS : ℝ)
          ≤ ∑ y ∈ Finset.range p,
              (((Finset.range p).sup (fun y => I2 S k Q p y hkS) : ℕ) : ℝ) := by
            apply Finset.sum_le_sum
            intro y hy
            exact_mod_cast (Finset.le_sup (f := fun y => I2 S k Q p y hkS) hy :
              I2 S k Q p y hkS ≤ (Finset.range p).sup (fun y => I2 S k Q p y hkS))
        _ = (Finset.range p).card •
              (((Finset.range p).sup (fun y => I2 S k Q p y hkS) : ℕ) : ℝ) :=
            Finset.sum_const _
        _ = (p : ℝ) * (((Finset.range p).sup (fun y => I2 S k Q p y hkS) : ℕ) : ℝ) := by
            rw [Finset.card_range, nsmul_eq_mul]
    calc (I1 S k Q p hkS : ℝ)
        = ∫ θ, ‖Gw p k Q θ‖ ^ 2 * ‖Weyl k Q θ‖ ^ (2 * (S - k)) := hmain1
      _ ≤ ∫ θ, ‖Gw p k Q θ‖ ^ 2 * ((p : ℝ) ^ (2 * (S - k) - 1) *
            ∑ y ∈ Finset.range p, ‖WeylMod p k Q y θ‖ ^ (2 * (S - k))) := by
          apply integral_mono
          · exact integrable_of_continuous (continuous_integrand1 p k Q (S - k))
          · exact integrable_of_continuous (continuous_integrand2 p k Q (S - k))
          · intro θ
            exact mul_le_mul_of_nonneg_left (hW θ) (by positivity)
      _ = (p : ℝ) ^ (2 * (S - k) - 1) * ∑ y ∈ Finset.range p,
            ∫ θ, ‖Gw p k Q θ‖ ^ 2 * ‖WeylMod p k Q y θ‖ ^ (2 * (S - k)) := by
          rw [show (fun θ : UnitAddTorus (Fin (k + 1)) => ‖Gw p k Q θ‖ ^ 2 *
                ((p : ℝ) ^ (2 * (S - k) - 1) *
                  ∑ y ∈ Finset.range p, ‖WeylMod p k Q y θ‖ ^ (2 * (S - k))))
              = fun θ => (p : ℝ) ^ (2 * (S - k) - 1) * ∑ y ∈ Finset.range p,
                  (‖Gw p k Q θ‖ ^ 2 * ‖WeylMod p k Q y θ‖ ^ (2 * (S - k))) from by
            funext θ
            simp only [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring]
          rw [integral_const_mul]
          congr 1
          rw [integral_finsetSum]
          intro y _
          exact integrable_of_continuous (continuous_integrandY p k Q (S - k) y)
      _ = (p : ℝ) ^ (2 * (S - k) - 1) * ∑ y ∈ Finset.range p,
            (I2 S k Q p y hkS : ℝ) := by
          rw [show (∑ y ∈ Finset.range p,
                ∫ θ, ‖Gw p k Q θ‖ ^ 2 * ‖WeylMod p k Q y θ‖ ^ (2 * (S - k)))
              = ∑ y ∈ Finset.range p, (I2 S k Q p y hkS : ℝ) from by
            apply Finset.sum_congr rfl
            intro y _
            exact (hmain2 y).symm]
      _ ≤ (p : ℝ) ^ (2 * (S - k) - 1) *
            ((p : ℝ) * (((Finset.range p).sup (fun y => I2 S k Q p y hkS) : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (p : ℝ) ^ (2 * (S - k)) *
            (((Finset.range p).sup (fun y => I2 S k Q p y hkS) : ℕ) : ℝ) := by
          rw [← mul_assoc, show (p : ℝ) ^ (2 * (S - k) - 1) * p = (p : ℝ) ^ (2 * (S - k)) from by
            rw [← pow_succ, show 2 * (S - k) - 1 + 1 = 2 * (S - k) from by omega]]

end

end Work.BMF.recursion
