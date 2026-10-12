import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.perBoxMF_of_fibre_zero` — the degenerate (thin-support) boxes

The crux of the a-priori chapter, `Work.BoseFixB1.PerBoxMF`, must hold on the *whole* good set,
and the good set contains the **degenerate** boxes: those for which the cutoff support
`S(u) = supp χ_{B(u)}` is thinner than `supp g₀`, so that every pair `x,y ∈ S(u)` has
`|x − y| < inf supp g₀` and hence

    wSmall1Pair h M ℓ d u x y = 0  and  wSmallPair M ℓ d u v x y = 0   (pointwise).

This is not hypothetical: it is the mechanism by which the fleet refuted the per-`u` mass lower
bound (`Submission/Work/BoseFixB1/w1MassB_ge_const_mul_chiMass.lean`, whose finding shows
`w1MassB = 0` whenever the box's cutoff support is thinner than `supp g₀`).  It is also the
corner phenomenon of `PERBOXF_ANALYSIS.md` §4 (`corner_box_degenerate`).

On such a box the statement is *trivial*, and this file proves it: if the fibre
`x ↦ ∫_{acube ℓ} w_{1,B(u)}(x,y) dy` vanishes identically then

* `w1MassB h M ℓ d u = 0` (the `y`-integral of the fibre over `ℝ³` is the `acube ℓ`-integral
  because `χ_{B(u)}` vanishes off the cube), so the whole `F`-term/background of `PerBoxMF`
  vanishes;
* `sbPot = −μ·(the fibre sum) + Pair ≥ 0`, since the fibre sum vanishes and the pair integrand
  is nonnegative (`wSmallPair` with numerator `v ≥ 0`);
* hence `sbWord ≥ 0` (using `0 ≤ sbKin`, which the caller has or obtains from
  `perBoxF_pieces.sbKin_ge_gapPart`).

The conclusion is `PerBoxMF`'s inequality **without** the `−C·perBoxErr` term; since
`perBoxErr ≥ 0`, that is *stronger* than `PerBoxMF` for every `C ≥ 0`.

This is the case split that the localised `A₀` chain needs: FS's mean-field/gap trichotomy
(high density / localised / low density) does *not* cover the degenerate boxes.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The degenerate-box case of `PerBoxMF`.**  If the localised fibre vanishes identically on
`acube ℓ` and the localised pair kernel is pointwise nonnegative (as it is for `v ≥ 0`), then
`PerBoxMF`'s inequality holds *without* the free error bracket. -/
theorem perBoxMF_of_fibre_zero {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {μ : ℝ} (hμ : 0 < μ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ)
    (hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ0 : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hdeg : ∀ x : EuclideanSpace ℝ (Fin 3),
      (∫ y in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x y) = 0)
    (hpair_nn : ∀ x y : EuclideanSpace ℝ (Fin 3),
      0 ≤ Submission.BoseGases.wSmallPair (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v x y)
    (hkin : 0 ≤ sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u Φ) :
    (1 / 4) * (w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u *
        (∫ x in abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2 *
          ((nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x /
            chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) - μ) ^ 2))
      - (1 / 2) * μ ^ 2 * w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      ≤ sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  set M : ℕ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M with hM
  set ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓ
  set d : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hd
  -- the one-body mass vanishes: the `y`-integral over `ℝ³` is the one over the cube
  have hW : w1MassB h M ℓ d u = 0 := by
    have h1 : w1MassB h M ℓ d u
        = ∫ x : EuclideanSpace ℝ (Fin 3),
            ∫ y in Submission.BoseGases.acube ℓ,
              Submission.BoseGases.wSmall1Pair h M ℓ d u x y := by
      rw [w1MassB]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      -- `χ_{B(u)}` vanishes off the cube, so the `y`-integrand does too
      have hsupp : ∀ y : EuclideanSpace ℝ (Fin 3), y ∉ Submission.BoseGases.acube ℓ →
          Submission.BoseGases.wSmall1Pair h M ℓ d u x y = 0 := by
        intro y hy
        have hzero : Submission.BoseGases.chiSmallB M ℓ d u y = 0 := by
          by_contra hc
          have hcoord := Submission.BoseGases.chiSmallB_support_big_box hM1 (d := d) hℓ0
            (u := u) (x := y) hc
          exact hy (fun j => by
            have h := hcoord j
            rw [abs_le] at h
            constructor <;> linarith [h.1, h.2])
        rw [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, hzero]
        ring
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero hsupp).symm
    rw [h1]
    have h2 : (fun x : EuclideanSpace ℝ (Fin 3) =>
        ∫ y in Submission.BoseGases.acube ℓ,
          Submission.BoseGases.wSmall1Pair h M ℓ d u x y) = fun _ => (0 : ℝ) :=
      funext fun x => hdeg x
    rw [h2, integral_zero]
  -- the potential word is nonnegative on such a box
  have hsbPot : 0 ≤ sbPot h μ u Φ := by
    rw [sbPot, Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword]
    refine integral_nonneg fun x => ?_
    have hfibre : (∑ i : Fin n,
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i)) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      exact hdeg (x i)
    have hpair : 0 ≤ (1 / 2 : ℝ) * ∑ p ∈ Submission.BoseGases.pairSet n,
        Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2) := by
      refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun p _ => hpair_nn (x p.1) (x p.2))
    have : -μ * (∑ i : Fin n,
        Submission.BoseGases.w1Fibre ℓ (Submission.BoseGases.wSmall1Pair h M ℓ d u) (x i))
        + (1 / 2 : ℝ) * ∑ p ∈ Submission.BoseGases.pairSet n,
            Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2) = 
        (1 / 2 : ℝ) * ∑ p ∈ Submission.BoseGases.pairSet n,
            Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2) := by
      rw [hfibre, mul_zero, zero_add]
    rw [this]
    exact mul_nonneg (sq_nonneg _) hpair
  have hsb : 0 ≤ sbWord h μ u Φ := by
    rw [sbWord]
    linarith
  -- assemble
  rw [hW]
  have : (1 / 4) * (0 * (∫ x in abox n ℓ, (Φ x) ^ 2 *
          ((nCountB M ℓ d u x / chiMass M ℓ d u) - μ) ^ 2))
      - (1 / 2) * μ ^ 2 * 0 * normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0 := by ring
  rw [this]
  exact hsb

/-- **The thin-support (degenerate-box) case of `PerBoxMF`, in geometric form.**  If no pair of
points at which the localised cutoff is nonzero lies within the support of `g₀ = v(1−w₀)` —
the thin-support/degenerate boxes of `FINDING_perBoxF_ledger.md` §1a and of
`w1MassB_ge_const_mul_chiMass.lean` — then **both** the localised one-body kernel and the
localised two-body kernel vanish identically, and `PerBoxMF`'s inequality holds *without* the
free error bracket.

The hypothesis is the pointwise form of the fleet's condition
`diam (supp χ_{B(u)}) < inf {‖z‖ : z ∈ supp g₀}` (for `v ≥ 0` one has `supp g₀ ⊆ supp v`); it is
stated directly in terms of `χ_{B(u)}` and `g₀`, so a caller who has the support geometry can
supply it, and the conclusion needs no support/`tsupport` machinery. -/
theorem perBoxMF_of_thin_support {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {μ : ℝ} (hμ : 0 < μ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ)
    (hM1 : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ0 : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hthin : ∀ x y : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x ≠ 0 →
      Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u y ≠ 0 →
      Submission.BoseGases.g0 v h (x - y) = 0)
    (hpair_nn : ∀ x y : EuclideanSpace ℝ (Fin 3),
      0 ≤ Submission.BoseGases.wSmallPair (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u v x y)
    (hkin : 0 ≤ sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u Φ) :
    (1 / 4) * (w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u *
        (∫ x in abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), (Φ x) ^ 2 *
          ((nCountB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x /
            chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) - μ) ^ 2))
      - (1 / 2) * μ ^ 2 * w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          * normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      ≤ sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  refine perBoxMF_of_fibre_zero h hμ u Φ hM1 hℓ0 (fun x => ?_) hpair_nn hkin
  -- the fibre integrand vanishes pointwise: either a cutoff factor is zero, or `g₀` is
  have hfun : (fun y : EuclideanSpace ℝ (Fin 3) =>
      Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x y) = fun _ => (0 : ℝ) := by
    funext y
    by_cases hx : Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x = 0
    · simp [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, hx]
    by_cases hy : Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u y = 0
    · simp [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, hy]
    · have hsc : Submission.BoseGases.wSmallScaled (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
          (Submission.BoseGases.g0 v h) (x - y) = 0 := by
        rw [Submission.BoseGases.wSmallScaled, hthin x y hx hy, zero_div]
      simp [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, hsc]
  rw [hfun]
  simp

end Work.BoseFixB1
