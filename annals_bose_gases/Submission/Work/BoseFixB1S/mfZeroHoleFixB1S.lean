import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.Work.BoseFixB1S.mfHoleVoidVanishesB1
import Submission.Work.BoseFixB1S.mfPairingSquaresB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory Metric Filter
open scoped Real Topology BigOperators ENNReal

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-- The corpus cutoff's big-scale factor `χ(·/ℓ)` is supported in the ball of radius `ℓ/2`: the
corpus `χ = chiBase / √chiNormSq` inherits the ball-support of the Mathlib `ContDiffBump`
`chiBump` (`rOut = 1/2`, `zero_of_le_dist`), i.e. it is *radial* — not the cube-supported
product bump the same construction is documented with in `CubicChi`. -/
theorem chiScale_eq_zero_of_half_le_norm {ℓ : ℝ}
    {x : EuclideanSpace ℝ (Fin 3)} (hℓ : 0 < ℓ) (hx : ℓ / 2 ≤ ‖x‖) :
    Submission.BoseGases.chiScale ℓ x = 0 := by
  have hdist : Submission.BoseGases.chiBump.rOut
      ≤ dist ((ℓ⁻¹ : ℝ) • x) (0 : EuclideanSpace ℝ (Fin 3)) := by
    rw [show Submission.BoseGases.chiBump.rOut = (1 : ℝ) / 2 from rfl, dist_zero_right,
      norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hℓ)]
    have hli : (0 : ℝ) < ℓ⁻¹ := inv_pos.mpr hℓ
    have h1 : ℓ⁻¹ * (ℓ / 2) = (1 : ℝ) / 2 := by
      rw [mul_div_assoc', inv_mul_cancel₀ (ne_of_gt hℓ)]
    rw [← h1]
    exact mul_le_mul_of_nonneg_left hx hli.le
  have hbase : Submission.BoseGases.chiBase ((ℓ⁻¹ : ℝ) • x) = 0 := by
    simpa [Submission.BoseGases.chiBase] using
      (Submission.BoseGases.chiBump.zero_of_le_dist hdist)
  rw [Submission.BoseGases.chiScale, Submission.BoseGases.chi, hbase, zero_div]

/-- **The localised kernel dies in the outer part of the box**: as soon as one of the two points
is outside the inscribed ball `ball 0 (ℓ/2)` of `acube ℓ`, `boxW` vanishes — whatever the
numerator `v` is.  Consequently `boxW h μ u x y = 0` does *not* imply `v (x − y) = 0`. -/
theorem boxW_eq_zero_of_half_le_norm {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    {μ : ℝ} {u x y : EuclideanSpace ℝ (Fin 3)}
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hx : Work.BoseBox.sideAt μ (_root_.BoseGases.a v) / 2 ≤ ‖x‖) :
    boxW h μ u x y = 0 := by
  have h0 : Submission.BoseGases.chiScale (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) x = 0 :=
    chiScale_eq_zero_of_half_le_norm hℓ hx
  rw [boxW, Submission.BoseGases.wSmallPair, Submission.BoseGases.chiSmallB, h0]
  ring

/-- **A cube has corners outside its inscribed ball**: the point `(ℓ/2, ℓ/2, 0)` lies in the cube
`acube ℓ` and has norm `ℓ/√2 > ℓ/2`. -/
theorem exists_mem_acube_half_lt_norm {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ∃ x : EuclideanSpace ℝ (Fin 3), x ∈ Submission.BoseGases.acube ℓ ∧ ℓ / 2 < ‖x‖ := by
  refine ⟨(ℓ / 2) • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
      + EuclideanSpace.single (1 : Fin 3) (1 : ℝ)), ?_, ?_⟩
  · rw [Submission.BoseGases.mem_acube_iff]
    intro j
    have hcoord : ((ℓ / 2) • (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
          + EuclideanSpace.single (1 : Fin 3) (1 : ℝ))) j
        = (ℓ / 2) * (if j = (0 : Fin 3) then (1 : ℝ)
            else if j = (1 : Fin 3) then 1 else 0) := by
      fin_cases j <;> simp [PiLp.add_apply, PiLp.smul_apply]
    rw [hcoord, Set.mem_Icc]
    constructor
    · split_ifs <;> linarith [hℓ]
    · split_ifs <;> linarith [hℓ]
  · set u : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
      + EuclideanSpace.single (1 : Fin 3) (1 : ℝ) with hu
    have hu2 : ‖u‖ ^ 2 = 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [hu, Fin.sum_univ_three, PiLp.single_apply, PiLp.add_apply] <;> norm_num
    have hu1 : 1 < ‖u‖ := by nlinarith [norm_nonneg u, hu2]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ ℓ / 2)]
    nlinarith [hu1, hℓ]

/-- At `u = 0` and `d ≥ 1` the FS box is the **full cube** `acube ℓ`: `dlBox ℓ d 0 =
acube ℓ ∩ acube (ℓd) = acube ℓ`.  Combined with `exists_mem_acube_half_lt_norm` this is a
positive-measure corner chunk of the box on which `boxW` vanishes identically
(`boxW_eq_zero_of_half_le_norm`) — the counterexample regime. -/
theorem dlBox_zero_eq_acube_of_one_le {ℓ d : ℝ} (hd : 1 ≤ d) (hℓ : 0 < ℓ) :
    Submission.BoseGases.dlBox ℓ d 0 = Submission.BoseGases.acube ℓ := by
  ext x
  rw [Submission.BoseGases.mem_dlBox_iff]
  constructor
  · intro hx
    exact hx.1
  · intro hx
    refine ⟨hx, ?_⟩
    simp only [smul_zero, sub_zero]
    have hmono : ℓ / 2 ≤ ℓ * d / 2 := by nlinarith [hℓ, hd]
    have hx' : ∀ m : Fin 3, x m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := by
      simpa [Submission.BoseGases.acube] using hx
    intro j
    have hxj := hx' j
    exact ⟨by linarith [hxj.1, hmono], by linarith [hxj.2, hmono]⟩

/-! ## The honest form of the target, in the target's own measure space -/

/-- **`mfSig = 0` forces the *kernel* `boxW` — not the numerator `v` — to vanish at every pair.**
This is `Work.BoseFixB1S.mfSigZeroHoleB1` with `boxW h μ u (x i) (x j)` in place of
`v (x i - x j)`, in the target's exact measure space (`volume.restrict (boxA^N)`), and it is what
the integral actually gives: the summands of `mfSig` are nonnegative, so each vanishes, so each
integrand vanishes a.e.; on the box the two indicators are `1`, so `Φ x ≠ 0` forces
`boxW h μ u (x i) (x j) = 0`.  The passage to `v (x i - x j) = 0` is *not* legitimate (see the
file header and `FINDING_mfSigZeroHoleB1_FALSE.md`): `boxW` vanishes identically on the corner
chunks of the box, where the numerator `v` may be nonzero.  The per-summand integrability
`hint` is the hypothesis under which `mfSig = 0` is not vacuous (`integral_undef`).

Derived from `Work.BoseFixB1S.mfHoleVoidVanishesB1` (a.e. over `abox N ℓ`) by restricting to the
sub-box `boxA^N ⊆ abox N ℓ` and discharging the two membership hypotheses. -/
theorem mfSigZeroHoleBoxW {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v)
    (h : Work.UBB.ScatSol v) {μ : ℝ} (u : EuclideanSpace ℝ (Fin 3)) {N : ℕ}
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hint : ∀ p ∈ Submission.BoseGases.pairSet N, MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        ((boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.1)
          * ((boxA v μ u).indicator (fun _ => (1 : ℝ)) (x p.2) * Φ x)) ^ 2
          * boxW h μ u (x p.1) (x p.2))
      (Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
      MeasureTheory.volume)
    (hzero : mfSig h μ N Φ u = 0) :
    ∀ᵐ x ∂(MeasureTheory.volume.restrict
        (Set.pi Set.univ (fun _ : Fin N => boxA v μ u))),
      Φ x ≠ 0 → ∀ i j : Fin N, i ≠ j → boxW h μ u (x i) (x j) = 0 := by
  classical
  have hAmeas : MeasurableSet (boxA v μ u) := Work.SmallBoxSliding.measurableSet_dlBox _ _ _
  have hs : MeasurableSet (Set.pi Set.univ (fun _ : Fin N => boxA v μ u)) :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => hAmeas)
  have hmem : Set.pi Set.univ (fun _ : Fin N => boxA v μ u)
      ⊆ Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) := by
    intro x hx i
    exact Work.SmallBoxSliding.dlBox_subset_acube _ _ _ (hx i (Set.mem_univ i))
  have h1 := Work.BoseFixB1S.mfHoleVoidVanishesB1 hv h hΦ hint hzero
  have hsub : ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))).restrict
        (Set.pi Set.univ (fun _ : Fin N => boxA v μ u))
      = (MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
        (Set.pi Set.univ (fun _ : Fin N => boxA v μ u)) :=
    MeasureTheory.Measure.restrict_restrict_of_subset hmem
  rw [← hsub]
  have h1' : ∀ᵐ x ∂(((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X N)).restrict
      (Submission.BoseGases.abox N (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))).restrict
      (Set.pi Set.univ (fun _ : Fin N => boxA v μ u))),
      ∀ p ∈ Submission.BoseGases.pairSet N, x p.1 ∈ boxA v μ u → x p.2 ∈ boxA v μ u →
        Φ x ≠ 0 → boxW h μ u (x p.1) (x p.2) = 0 := by
    rw [MeasureTheory.ae_restrict_iff' hs]
    exact h1.mono (fun x hx _ => hx)
  filter_upwards [h1', MeasureTheory.ae_restrict_mem hs] with x hx hxs
  intro hΦx i j hij
  exact hx (i, j) (by simp [Submission.BoseGases.pairSet, hij])
    (hxs i (Set.mem_univ i)) (hxs j (Set.mem_univ j)) hΦx

end

end Work.BoseFixB1S
