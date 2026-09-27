import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.SymDefs
import Submission.Work.EQ.normEqCurve_structure
import Submission.Work.EQ.polarPt_compact
import Submission.Work.EQ.polarPt_reflect
import Submission.Work.EQ.eqT_reflections
import Submission.Work.EQ.eqT_localModel
import Submission.Work.EQ.localModel_dynamics
import Submission.Work.EQ.LocalModel_mono
import Submission.Work.EQ.eqT_lift
import Submission.Work.EQ.eqT_spread
import Submission.Work.EQ.axis_mirror_invariance
import Submission.Work.EQ.bis_mirror_invariance
import Submission.Work.EQ.rho_crossing
import Submission.Work.EQ.eqT_orbit_tendsto_real

/-!
# Symmetries of a normalised two-point equichordal curve (Rychlik §2.5–2.6)

The curve `C = {polarPt (-(a/2)) (ρ₁ θ) θ}` is invariant under Rychlik's map
`T = eqT a`, and near its left real point `A = polarPt (-(a/2)) (ρ₁ π) π` the map is
normally hyperbolic (`eqT_localModel`, `localModel_dynamics`): every point of a small ball
around `A` has an orbit converging to a real point of the ball, and two points of the ball
with the same imaginary part whose orbits both converge to `A` coincide.

That local uniqueness identifies, for each sufficiently small height `η`, the point of the
curve at height `η` with the point of any other closed `T`-invariant set that has a point at
height `η` close enough to `A`.  Applying this to the axis mirror `star '' C` (which has the
same two real points as `C`) gives `C ⊆ star '' C`, i.e. `ρ₁` is even.  Before the bisector
mirror can be treated the same way one must know that its real points are `A` and `1/2`, i.e.
that `A = -1/2`: this is obtained from the *dynamics* — if `A + B ≠ 0` the bisector mirror
`-star '' C` and the curve meet off the real axis, and the orbit of such a point converges to
a real point of both, forcing `A + B = 0`.  With `A = -1/2` the same local argument gives
`C ⊆ -star '' C`, i.e. `ρ₂ θ = ρ₁ (π - θ)`.
-/

namespace Work.EQ

open Complex Filter
open scoped Topology

/-! ## Auxiliary lemmas -/

/-- **Injectivity of the polar parametrisation, modulo `2π`.**  Two polar representations of
the same point have the same (positive) radius, and their angles agree modulo `2π`. -/
theorem polarPt_inj_mod {c r r' θ θ' : ℝ} (hr : 0 < r) (hr' : 0 < r')
    (h : polarPt c r θ = polarPt c r' θ') :
    r = r' ∧ ∃ k : ℤ, θ' = θ + k * (2 * Real.pi) := by
  have h1 : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
      = (r' : ℂ) * Complex.exp ((θ' : ℂ) * Complex.I) := by
    simpa only [polarPt] using add_left_cancel h
  have hr_eq : r = r' := by
    have hn := congrArg norm h1
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] at hn
    have h2 : |r| = |r'| := by simpa using hn
    rwa [abs_of_pos hr, abs_of_pos hr'] at h2
  subst hr_eq
  have hc : ((r : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  have he : Complex.exp ((θ : ℂ) * Complex.I) = Complex.exp ((θ' : ℂ) * Complex.I) :=
    mul_left_cancel₀ hc h1
  have hcircle : Circle.exp θ = Circle.exp θ' := by
    apply Subtype.ext
    simpa [Circle.coe_exp] using he
  obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hcircle
  exact ⟨rfl, -m, by rw [hm]; push_cast; ring⟩

/-- For two complex numbers on the real axis the norm of the difference is the absolute value
of the difference of the real parts. -/
theorem norm_sub_real {z w : ℂ} (hz : z.im = 0) (hw : w.im = 0) : ‖z - w‖ = |z.re - w.re| := by
  have h : z - w = (((z.re - w.re : ℝ)) : ℂ) := by
    apply Complex.ext
    · simp [Complex.sub_re]
    · simp [Complex.sub_im, hz, hw]
  rw [h]
  exact RCLike.norm_ofReal (z.re - w.re)

/-- **Attainment of all small heights near a real point of a polar curve.**  If `sin θ₀ = 0`
and `ρ > 0` is continuous, then the points `polarPt c (ρ θ) θ` with `θ` close to `θ₀` realise
every height in a neighbourhood of `0`, and this within an arbitrarily prescribed `ε`-ball
around the point `polarPt c (ρ θ₀) θ₀`. -/
theorem attain_near {c θ₀ : ℝ} {ρ : ℝ → ℝ} (hcont : Continuous ρ) (hpos : ∀ θ, 0 < ρ θ)
    (hsin : Real.sin θ₀ = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ η' : ℝ, 0 < η' ∧ ∀ η : ℝ, |η| < η' → ∃ θ : ℝ,
      (polarPt c (ρ θ) θ).im = η ∧
        ‖polarPt c (ρ θ) θ - polarPt c (ρ θ₀) θ₀‖ ≤ ε := by
  have hFcont : Continuous (fun θ : ℝ => polarPt c (ρ θ) θ) := by
    unfold polarPt; fun_prop
  have hcont' : Continuous fun θ : ℝ => ‖polarPt c (ρ θ) θ - polarPt c (ρ θ₀) θ₀‖ :=
    (hFcont.sub continuous_const).norm
  have hd : ∀ᶠ θ in 𝓝 θ₀, ‖polarPt c (ρ θ) θ - polarPt c (ρ θ₀) θ₀‖ < ε := by
    refine hcont'.continuousAt.eventually (isOpen_Iio.mem_nhds ?_)
    show ‖polarPt c (ρ θ₀) θ₀ - polarPt c (ρ θ₀) θ₀‖ < ε
    rw [sub_self, norm_zero]; exact hε
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hd
  set t : ℝ := min (δ / 2) (Real.pi / 2) with ht
  have ht0 : 0 < t := lt_min (by linarith) (by linarith [Real.pi_pos])
  have htd : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have htpi : t < Real.pi := lt_of_le_of_lt (min_le_right _ _) (by linarith [Real.pi_pos])
  have hst : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 htpi
  have hfcont : Continuous (fun θ : ℝ => ρ θ * Real.sin θ) := hcont.mul Real.continuous_sin
  have hf0 : ρ θ₀ * Real.sin θ₀ = 0 := by rw [hsin, mul_zero]
  have hcos : Real.cos θ₀ = 1 ∨ Real.cos θ₀ = -1 := by
    have h2 : Real.cos θ₀ ^ 2 = 1 := by
      have h3 := Real.sin_sq_add_cos_sq θ₀
      rw [hsin] at h3; nlinarith
    exact sq_eq_one_iff.mp h2
  have hplus : ρ (θ₀ + t) * Real.sin (θ₀ + t)
      = Real.cos θ₀ * (ρ (θ₀ + t) * Real.sin t) := by
    rw [Real.sin_add, hsin]; ring
  have hminus : ρ (θ₀ - t) * Real.sin (θ₀ - t)
      = -(Real.cos θ₀ * (ρ (θ₀ - t) * Real.sin t)) := by
    rw [Real.sin_sub, hsin]; ring
  have hposp : 0 < ρ (θ₀ + t) * Real.sin t := mul_pos (hpos _) hst
  have hposm : 0 < ρ (θ₀ - t) * Real.sin t := mul_pos (hpos _) hst
  -- a finished IVT application: the angle gives the height and the norm bound
  have finish : ∀ (η θ : ℝ), θ ∈ Set.Icc (θ₀ - t) (θ₀ + t) → ρ θ * Real.sin θ = η →
      ∃ θ' : ℝ, (polarPt c (ρ θ') θ').im = η ∧
        ‖polarPt c (ρ θ') θ' - polarPt c (ρ θ₀) θ₀‖ ≤ ε := by
    intro η θ hθmem hθeq
    refine ⟨θ, ?_, ?_⟩
    · rw [polarPtReflect_im, hθeq]
    · refine le_of_lt (hδ ?_)
      rw [Real.dist_eq, abs_lt]
      exact ⟨by linarith [hθmem.1], by linarith [hθmem.2]⟩
  rcases hcos with hco | hco
  · -- `cos θ₀ = 1`: the height increases through `θ₀`
    have hp : 0 < ρ (θ₀ + t) * Real.sin (θ₀ + t) := by rw [hplus, hco, one_mul]; exact hposp
    have hm : ρ (θ₀ - t) * Real.sin (θ₀ - t) < 0 := by rw [hminus, hco, one_mul]; linarith
    refine ⟨min (ρ (θ₀ + t) * Real.sin (θ₀ + t))
      (-(ρ (θ₀ - t) * Real.sin (θ₀ - t))), lt_min hp (by linarith), ?_⟩
    intro η hη
    rw [abs_lt] at hη
    have hηN : η < ρ (θ₀ + t) * Real.sin (θ₀ + t) :=
      lt_of_lt_of_le hη.2 (min_le_left _ _)
    have hηM : ρ (θ₀ - t) * Real.sin (θ₀ - t) < η := by
      have h2 := min_le_right (ρ (θ₀ + t) * Real.sin (θ₀ + t))
        (-(ρ (θ₀ - t) * Real.sin (θ₀ - t)))
      linarith [hη.1]
    rcases lt_or_ge 0 η with hη0 | hη0
    · obtain ⟨θ, hθmem, hθeq⟩ := (intermediate_value_Icc (le_add_of_nonneg_right ht0.le)
        hfcont.continuousOn) ⟨le_trans (le_of_eq hf0) hη0.le, hηN.le⟩
      exact finish η θ (Set.Icc_subset_Icc (by linarith) le_rfl hθmem) hθeq
    · obtain ⟨θ, hθmem, hθeq⟩ := (intermediate_value_Icc (sub_le_self _ ht0.le)
        hfcont.continuousOn) ⟨hηM.le, le_trans hη0 (le_of_eq hf0.symm)⟩
      exact finish η θ (Set.Icc_subset_Icc le_rfl (by linarith) hθmem) hθeq
  · -- `cos θ₀ = -1`: the height decreases through `θ₀`
    have hp : ρ (θ₀ + t) * Real.sin (θ₀ + t) < 0 := by
      rw [hplus, hco, neg_mul, one_mul]; linarith
    have hm : 0 < ρ (θ₀ - t) * Real.sin (θ₀ - t) := by
      rw [hminus, hco, neg_mul, one_mul]; linarith
    refine ⟨min (-(ρ (θ₀ + t) * Real.sin (θ₀ + t)))
      (ρ (θ₀ - t) * Real.sin (θ₀ - t)), lt_min (by linarith) hm, ?_⟩
    intro η hη
    rw [abs_lt] at hη
    have hηN : η < ρ (θ₀ - t) * Real.sin (θ₀ - t) :=
      lt_of_lt_of_le hη.2 (min_le_right _ _)
    have hηM : ρ (θ₀ + t) * Real.sin (θ₀ + t) < η := by
      have h2 := min_le_left (-(ρ (θ₀ + t) * Real.sin (θ₀ + t)))
        (ρ (θ₀ - t) * Real.sin (θ₀ - t))
      linarith [hη.1]
    rcases lt_or_ge 0 η with hη0 | hη0
    · obtain ⟨θ, hθmem, hθeq⟩ := (intermediate_value_Icc' (sub_le_self _ ht0.le)
        hfcont.continuousOn) ⟨le_trans (le_of_eq hf0) hη0.le, hηN.le⟩
      exact finish η θ (Set.Icc_subset_Icc le_rfl (by linarith) hθmem) hθeq
    · obtain ⟨θ, hθmem, hθeq⟩ := (intermediate_value_Icc' (le_add_of_nonneg_right ht0.le)
        hfcont.continuousOn) ⟨hηM.le, le_trans hη0 (le_of_eq hf0.symm)⟩
      exact finish η θ (Set.Icc_subset_Icc (by linarith) le_rfl hθmem) hθeq

/-- **Orbits in a small ball around `A` converge to `A`.**  Under the local model, a closed
`T`-invariant set `D` whose only real point within `2 ε` of `A` is `A` itself has all its
points within `ε` of `A` converging to `A`. -/
theorem orbit_tendsto_center {T : ℂ → ℂ} {A : ℂ} {lam C₀ ε : ℝ} (hmodel : LocalModel T A lam C₀ ε)
    (hε : ε ≤ (1 - lam) / 4) {D : Set ℂ} (hDc : IsClosed D) (hDmap : Set.MapsTo T D D)
    (hDaxis : ∀ z ∈ D, z.im = 0 → ‖z - A‖ ≤ 2 * ε → z = A) :
    ∀ z ∈ D, ‖z - A‖ ≤ ε → Filter.Tendsto (fun n : ℕ => (T^[n]) z) Filter.atTop (nhds A) := by
  obtain ⟨-, hlim, -⟩ := localModel_dynamics hmodel hε
  intro z hz hzn
  obtain ⟨Q, hQim, hQn, hQtend⟩ := hlim z hzn
  have hQmem : Q ∈ D := hDc.mem_of_tendsto hQtend (Eventually.of_forall fun n => by
    induction n with
    | zero => simpa using hz
    | succ n ih => rw [Function.iterate_succ_apply']; exact hDmap ih)
  rw [hDaxis Q hQmem hQim hQn] at hQtend
  exact hQtend

/-- **The leaf through `A` is unique.**  Let `D` (the curve) be a closed `T`-invariant set
containing the continuous path `P` with `P π = A`, and let `E` be another closed `T`-invariant
set with the same local axis condition as `D` and meeting every small height near `A` inside
the `ε`-ball.  Then `P` lies in `E` for `θ` close to `π`. -/
theorem path_enters_leaf {T : ℂ → ℂ} {A : ℂ} {lam C₀ ε : ℝ} (hmodel : LocalModel T A lam C₀ ε)
    (hε : ε ≤ (1 - lam) / 4) {D E : Set ℂ} (hDc : IsClosed D) (hDmap : Set.MapsTo T D D)
    (hDaxis : ∀ z ∈ D, z.im = 0 → ‖z - A‖ ≤ 2 * ε → z = A)
    (hEc : IsClosed E) (hEmap : Set.MapsTo T E E)
    (hEaxis : ∀ z ∈ E, z.im = 0 → ‖z - A‖ ≤ 2 * ε → z = A)
    (hEatt : ∃ η' : ℝ, 0 < η' ∧ ∀ η : ℝ, |η| < η' →
      ∃ z ∈ E, z.im = η ∧ ‖z - A‖ ≤ ε)
    {P : ℝ → ℂ} (hPcont : Continuous P) (hPpi : P Real.pi = A) (hPmem : ∀ θ, P θ ∈ D) :
    ∃ δ > 0, ∀ θ, |θ - Real.pi| < δ → P θ ∈ E := by
  obtain ⟨-, -, huniq⟩ := localModel_dynamics hmodel hε
  have hDorb := orbit_tendsto_center hmodel hε hDc hDmap hDaxis
  have hEorb := orbit_tendsto_center hmodel hε hEc hEmap hEaxis
  obtain ⟨η', hη'pos, hη'⟩ := hEatt
  have hev1 : ∀ᶠ θ in 𝓝 Real.pi, ‖P θ - A‖ < ε := by
    have hc : Continuous fun θ : ℝ => ‖P θ - A‖ := (hPcont.sub continuous_const).norm
    refine hc.continuousAt.eventually (isOpen_Iio.mem_nhds ?_)
    show ‖P Real.pi - A‖ < ε
    rw [hPpi, sub_self, norm_zero]; exact hmodel.2.1
  have hev2 : ∀ᶠ θ in 𝓝 Real.pi, |(P θ).im| < η' := by
    have hc : Continuous fun θ : ℝ => |(P θ).im| := (Complex.continuous_im.comp hPcont).abs
    refine hc.continuousAt.eventually (isOpen_Iio.mem_nhds ?_)
    show |(P Real.pi).im| < η'
    have h0 : (P Real.pi).im = 0 := by rw [hPpi, hmodel.1]
    rw [h0, abs_zero]; exact hη'pos
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp (hev1.and hev2)
  refine ⟨δ, hδpos, fun θ hθ => ?_⟩
  obtain ⟨h1, h2⟩ := hδ (by rwa [Real.dist_eq])
  obtain ⟨z, hzE, hzim, hzn⟩ := hη' (P θ).im h2
  have heq : P θ = z :=
    huniq (P θ) z (le_of_lt h1) hzn hzim.symm
      (hDorb (P θ) (hPmem θ) (le_of_lt h1)) (hEorb z hzE hzn)
  rw [heq]; exact hzE

end Work.EQ
namespace Work.EQ

open Complex Filter
open scoped Topology

/-- **The local set-up.**  From a normalised equichordal curve we extract the local normal
model at the left axis point `A = polarPt (-(a/2)) (ρ₁ π) π`, shrunk so that it can be used for
the local uniqueness argument, together with the basic facts about `A`. -/
private theorem local_setup {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) :
    ∃ (A : ℂ) (lam C₀ ε : ℝ),
      A = (((polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re : ℝ) : ℂ) ∧
      A.im = 0 ∧ LocalModel (eqT a) A lam C₀ ε ∧ ε ≤ (1 - lam) / 4 ∧ 2 * ε < 1 ∧
      A = polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi ∧
      ‖polarPt (-(a/2)) (ρ₁ 0) 0 - A‖ = 1 ∧
      (∀ z ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ), z.im = 0 →
        ‖z - A‖ ≤ 2 * ε → z = A) := by
  obtain ⟨hc1, hc2, hper₁, hper₂, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14,
    hc15, hc16, hc17, hc18⟩ := normEqCurve_structure ha0 ha1 hC
  have hcont₁ : Continuous ρ₁ := hC.1
  have hcont₂ : Continuous ρ₂ := hC.2.1
  have hpos₁ : ∀ θ, 0 < ρ₁ θ := hC.2.2.1
  have hpos₂ : ∀ θ, 0 < ρ₂ θ := hC.2.2.2.1
  have hchord₁ : ∀ θ, ρ₁ θ + ρ₁ (θ + Real.pi) = 1 := hC.2.2.2.2.1
  have hchord₂ : ∀ θ, ρ₂ θ + ρ₂ (θ + Real.pi) = 1 := hC.2.2.2.2.2.1
  have hrange : Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)
      = Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ) := hC.2.2.2.2.2.2
  set A : ℂ := (((polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re : ℝ) : ℂ) with hAdef
  have hAim : A.im = 0 := by rw [hAdef]; simp
  have hAeq : A = polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi := by
    rw [hAdef]
    apply Complex.ext
    · simp
    · rw [polarPtReflect_im, Real.sin_pi, mul_zero]; simp
  -- the local model, shrunk
  obtain ⟨lam, C₀, ε₀, hmodel₀⟩ := eqT_localModel ha0 ha1 (a₀ := (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re)
    (by linarith) (by linarith)
  have hlam1 : lam < 1 := hmodel₀.2.2.2.2.1
  have hε₀pos : 0 < ε₀ := hmodel₀.2.1
  set ε : ℝ := min (min ε₀ ((1 - lam) / 4)) (1/4) with hεdef
  have hεpos : 0 < ε := by
    rw [hεdef]; exact lt_min (lt_min hε₀pos (by linarith)) (by norm_num)
  have hεle : ε ≤ ε₀ := by rw [hεdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hεlam : ε ≤ (1 - lam) / 4 := by
    rw [hεdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have h2ε1 : 2 * ε < 1 := by
    have : ε ≤ 1/4 := by rw [hεdef]; exact min_le_right _ _
    linarith
  have hmodel : LocalModel (eqT a) A lam C₀ ε := LocalModel_mono hmodel₀ hεpos hεle
  -- the two real points are at distance `1`
  have hBA : (polarPt (-(a/2)) (ρ₁ 0) 0).re - (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re = 1 :=
    hc12
  have hBreal : polarPt (-(a/2)) (ρ₁ 0) 0 - A = ((1 : ℝ) : ℂ) := by
    have hz0 : polarPt (-(a/2)) (ρ₁ 0) 0 = (((polarPt (-(a/2)) (ρ₁ 0) 0).re : ℝ) : ℂ) := by
      apply Complex.ext
      · simp
      · rw [polarPtReflect_im, Real.sin_zero, mul_zero]; simp
    rw [hz0, hAdef, ← Complex.ofReal_sub, hBA]
  have hdist : ‖polarPt (-(a/2)) (ρ₁ 0) 0 - A‖ = 1 := by rw [hBreal]; simp
  refine ⟨A, lam, C₀, ε, rfl, hAim, hmodel, hεlam, h2ε1, hAeq, hdist, ?_⟩
  intro z hz hzim hzn
  rcases nec_real_pt_of_chord hpos₁ hchord₁ hz hzim with h | h
  · rw [h] at hzn
    rw [hdist] at hzn
    linarith
  · rw [h, hAeq]

/-- **Axis symmetry of the curve.**  `ρ₁` is even. -/
theorem normEqCurve_rho_even {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hcurve : NormEqCurve a ρ₁ ρ₂) : ∀ θ, ρ₁ (-θ) = ρ₁ θ := by
  obtain ⟨A, lam, C₀, ε, hAcast, hAim, hmodel, hεlam, h2ε1, hAeq, hdist, hcurve_axis⟩ :=
    local_setup ha0 ha1 hcurve
  obtain ⟨σ, hσper, hσeq, hσ0, hσπ, hfix1, hfix2⟩ := eqT_lift ha0 ha1 hcurve
  obtain ⟨hDcclosed₀, hDcmap₀, hDcback₀⟩ := axis_mirror_invariance ha0 ha1 hcurve
  obtain ⟨hc1, hc2, hper₁, hper₂, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14,
    hc15, hc16, hc17, hc18⟩ := normEqCurve_structure ha0 ha1 hcurve
  obtain ⟨hcont₁, hcont₂, hpos₁, hpos₂, hchord₁, hchord₂, hrange⟩ := hcurve
  have hAstar : star A = A := by
    rw [Complex.star_def]; exact Complex.conj_eq_iff_im.mpr hAim
  set P : ℝ → ℂ := fun θ => polarPt (-(a/2)) (ρ₁ θ) θ with hPdef
  have hPapp : ∀ θ, P θ = polarPt (-(a/2)) (ρ₁ θ) θ := fun θ => rfl
  have hPcont : Continuous P := by
    show Continuous (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)
    unfold polarPt; fun_prop
  have hPpi : P Real.pi = A := by rw [hPapp]; exact hAeq.symm
  have hcurveclosed : IsClosed (Set.range P) :=
    (polarPt_compact (a := a) hcont₁ hper₁).isClosed
  have hcurvemap : Set.MapsTo (eqT a) (Set.range P) (Set.range P) := hc16
  have hcurveorb : ∀ z ∈ Set.range P, ‖z - A‖ ≤ ε →
      Tendsto (fun n : ℕ => ((eqT a)^[n]) z) atTop (nhds A) :=
    orbit_tendsto_center hmodel hεlam hcurveclosed hcurvemap hcurve_axis
  -- the axis mirror
  set Dc : Set ℂ := star '' Set.range P with hDcdef
  have hDcEq : Dc = star '' Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) := by
    rw [hDcdef, hPdef]
  have hDcclosed : IsClosed Dc := by rw [hDcEq]; exact hDcclosed₀
  have hDcmap : Set.MapsTo (eqT a) Dc Dc := by rw [hDcEq]; exact hDcmap₀
  have hDcback : ∀ θ, eqT a (P θ) ∈ Dc → P θ ∈ Dc := by
    intro θ h
    rw [hDcEq] at h ⊢
    exact hDcback₀ θ h
  -- the only real point of `Dc` near `A` is `A`
  have hDcaxis : ∀ z ∈ Dc, z.im = 0 → ‖z - A‖ ≤ 2 * ε → z = A := by
    intro z hz hzim hzn
    obtain ⟨w, hw, rfl⟩ := hz
    have hwim : w.im = 0 := by
      have h := hzim
      rw [Complex.star_def, Complex.conj_im, neg_eq_zero] at h
      exact h
    have hnorm : ‖star w - A‖ = ‖w - A‖ := by
      have h : star w - A = star (w - A) := by
        calc star w - A = star w - star A := by rw [hAstar]
          _ = star (w - A) := (star_sub w A).symm
      rw [h]
      simpa using Complex.norm_conj (w - A)
    rcases nec_real_pt_of_chord hpos₁ hchord₁ hw hwim with h | h
    · exfalso
      rw [hnorm] at hzn
      rw [h] at hzn
      rw [hdist] at hzn
      linarith
    · rw [h, ← hAeq]
      exact hAstar
  -- attainment for `Dc`
  have hDcatt : ∃ η' : ℝ, 0 < η' ∧ ∀ η : ℝ, |η| < η' →
      ∃ z ∈ Dc, z.im = η ∧ ‖z - A‖ ≤ ε := by
    obtain ⟨η', hη'pos, hη'⟩ := attain_near (c := -(a/2)) (θ₀ := Real.pi) hcont₁ hpos₁
      Real.sin_pi hmodel.2.1
    refine ⟨η', hη'pos, fun η hη => ?_⟩
    have hη' := hη' (-η) (by rwa [abs_neg])
    obtain ⟨θ, hθim, hθn⟩ := hη'
    refine ⟨star (P θ), ⟨P θ, Set.mem_range_self θ, rfl⟩, ?_, ?_⟩
    · rw [Complex.star_def, Complex.conj_im, hθim, neg_neg]
    · have h : star (P θ) - A = star (P θ - A) := by
        calc star (P θ) - A = star (P θ) - star A := by rw [hAstar]
          _ = star (P θ - A) := (star_sub (P θ) A).symm
      rw [h]
      have h2 : ‖star (P θ - A)‖ = ‖P θ - A‖ := by simpa using Complex.norm_conj (P θ - A)
      rw [h2]
      simpa [hPapp, hAeq] using hθn
  obtain ⟨δ, hδpos, hgerm⟩ := path_enters_leaf hmodel hεlam hcurveclosed hcurvemap hcurve_axis
    hDcclosed hDcmap hDcaxis hDcatt hPcont hPpi (fun θ => Set.mem_range_self θ)
  have hsub : ∀ θ, P θ ∈ Dc :=
    eqT_spread ha0 ha1 hcont₁ hper₁ hσper hσeq hσ0 hσπ hfix1 hfix2 hDcclosed hDcmap hDcback
      hδpos hgerm
  -- conclude evenness
  have hper : Function.Periodic ρ₁ (2 * Real.pi) := hper₁
  intro θ
  obtain ⟨w, hw, hwz⟩ := hsub θ
  obtain ⟨θ', hθ'⟩ := hw
  have hstar : star (polarPt (-(a/2)) (ρ₁ θ') θ') = polarPt (-(a/2)) (ρ₁ θ) θ := by
    rw [← hPapp θ', ← hPapp θ, ← hwz, ← hθ']
  have hkey : polarPt (-(a/2)) (ρ₁ θ') (-θ') = polarPt (-(a/2)) (ρ₁ θ) θ := by
    rw [← polarPtReflect_neg (-(a/2)) (ρ₁ θ') θ']
    exact hstar
  obtain ⟨hr, k, hk⟩ := polarPt_inj_mod (hpos₁ θ') (hpos₁ θ) hkey
  have h1 : ρ₁ (-θ + (k : ℝ) * (2 * Real.pi)) = ρ₁ (-θ) := hper.int_mul k (-θ)
  have h2 : -θ + (k : ℝ) * (2 * Real.pi) = θ' := by linarith [hk]
  rw [h2] at h1
  linarith [h1, hr]

/-- **Normalisation of the left axis point.**  For a normalised equichordal curve the point
where it meets the axis on the left is `-1/2`.  If `A + B ≠ 0` (with `A`, `B` the two real
points of the curve) then the bisector mirror `-star '' C` has real points `-A ≠ B` and `-B ≠ A`,
so it meets `C` only off the axis (`rho_crossing`); an orbit of such a point stays in the closed
invariant set `C ∩ (-star '' C)` and converges to a real point `Q` of the curve
(`eqT_orbit_tendsto_real`), whence both `Q` and `-Q` are among `A, B` — which forces
`A + B = 0`. -/
theorem normEqCurve_axis_half {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) :
    (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re = -(1/2) := by
  have hcont₁ : Continuous ρ₁ := hC.1
  have hcont₂ : Continuous ρ₂ := hC.2.1
  have hpos₁ : ∀ θ, 0 < ρ₁ θ := hC.2.2.1
  have hpos₂ : ∀ θ, 0 < ρ₂ θ := hC.2.2.2.1
  have hchord₁ : ∀ θ, ρ₁ θ + ρ₁ (θ + Real.pi) = 1 := hC.2.2.2.2.1
  have hchord₂ : ∀ θ, ρ₂ θ + ρ₂ (θ + Real.pi) = 1 := hC.2.2.2.2.2.1
  have hrange : Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)
      = Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ) := hC.2.2.2.2.2.2
  have hPπim : (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).im = 0 := by
    rw [polarPtReflect_im, Real.sin_pi, mul_zero]
  have hBA : (polarPt (-(a/2)) (ρ₁ 0) 0).re
      - (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re = 1 := by
    rw [nec_polarPt_zero, nec_polarPt_pi]
    simp only [Complex.ofReal_re]
    have h := hchord₁ 0
    simp only [zero_add] at h
    linarith
  have hPπlt : (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re < -(a/2) := by
    rw [nec_polarPt_pi]
    simp only [Complex.ofReal_re]
    linarith [hpos₁ Real.pi]
  have hP0gt : a/2 < (polarPt (-(a/2)) (ρ₁ 0) 0).re := by
    have hmem : polarPt (a/2) (ρ₂ 0) 0
        ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) := by
      rw [hrange]; exact Set.mem_range_self 0
    have him : (polarPt (a/2) (ρ₂ 0) 0).im = 0 := by
      rw [polarPtReflect_im, Real.sin_zero, mul_zero]
    have hval : (polarPt (a/2) (ρ₂ 0) 0).re = a/2 + ρ₂ 0 := by
      rw [nec_polarPt_zero]; simp
    rcases nec_real_pt_of_chord hpos₁ hchord₁ hmem him with h | h
    · have h1 : (polarPt (a/2) (ρ₂ 0) 0).re = (polarPt (-(a/2)) (ρ₁ 0) 0).re := by rw [h]
      rw [hval] at h1
      linarith [hpos₂ 0]
    · have h1 : (polarPt (a/2) (ρ₂ 0) 0).re
          = (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re := by rw [h]
      rw [hval] at h1
      linarith [hpos₂ 0, hPπlt]
  have hsum : (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re
      + (polarPt (-(a/2)) (ρ₁ 0) 0).re = 0 := by
    by_contra hne
    obtain ⟨σ, hσper, hσeq, hσ0, hσπ, hfix1, hfix2⟩ := eqT_lift ha0 ha1 hC
    obtain ⟨ψ, hψ0, hψπ, hψeq⟩ := rho_crossing ha0 ha1 hC hne
    set P₀ : ℂ := polarPt (a/2) (ρ₂ ψ) ψ with hP₀def
    have hP₀C : P₀ ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) := by
      have h : P₀ ∈ Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ) := Set.mem_range_self ψ
      rwa [← hrange] at h
    have hP₀Db : P₀ ∈ (fun z : ℂ => -star z) '' Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) := by
      refine ⟨polarPt (-(a/2)) (ρ₁ (Real.pi - ψ)) (Real.pi - ψ), Set.mem_range_self _, ?_⟩
      show -star (polarPt (-(a/2)) (ρ₁ (Real.pi - ψ)) (Real.pi - ψ)) = P₀
      rw [hP₀def, (polarPt_reflect a ρ₁).2.1 (Real.pi - ψ),
        show Real.pi - (Real.pi - ψ) = ψ by ring, hψeq]
    have hP₀im : P₀.im ≠ 0 := by
      rw [hP₀def, polarPtReflect_im]
      exact ne_of_gt (mul_pos (hpos₂ ψ) (Real.sin_pos_of_pos_of_lt_pi hψ0 hψπ))
    obtain ⟨θ, hθ⟩ := hP₀C
    have himθ : (polarPt (-(a/2)) (ρ₁ θ) θ).im ≠ 0 := by
      have h2 : polarPt (-(a/2)) (ρ₁ θ) θ = P₀ := hθ
      rw [h2]; exact hP₀im
    obtain ⟨Q, hQim, hQmem, hQtend⟩ :=
      eqT_orbit_tendsto_real ha0 ha1 hC hσper hσeq hσ0 hσπ hfix1 hfix2 himθ
    obtain ⟨hDbclosed, hDbmap, hDbback⟩ := bis_mirror_invariance ha0 ha1 hC
    have hQDb : Q ∈ (fun z : ℂ => -star z) '' Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) :=
      hDbclosed.mem_of_tendsto hQtend (Eventually.of_forall fun n => by
        induction n with
        | zero => simpa [hθ] using hP₀Db
        | succ n ih => rw [Function.iterate_succ_apply']; exact hDbmap ih)
    have hQstar : star Q = Q := by
      rw [Complex.star_def]; exact Complex.conj_eq_iff_im.mpr hQim
    have hnegC : -Q ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) := by
      obtain ⟨w, hw, hwz⟩ := hQDb
      have hw_eq : w = -Q := by
        have hsw : star w = -Q := by rw [← hwz]; simp
        calc w = star (star w) := by simp
          _ = star (-Q) := by rw [hsw]
          _ = -Q := by rw [star_neg, hQstar]
      rw [← hw_eq]; exact hw
    have hnegim : (-Q).im = 0 := by rw [Complex.neg_im, hQim, neg_zero]
    rcases nec_real_pt_of_chord hpos₁ hchord₁ hQmem hQim with hQ | hQ <;>
      rcases nec_real_pt_of_chord hpos₁ hchord₁ hnegC hnegim with hn | hn
    · have h2 := congrArg Complex.re (hn.trans hQ.symm)
      have hQre : Q.re = (polarPt (-(a/2)) (ρ₁ 0) 0).re := by rw [hQ]
      rw [Complex.neg_re, hQre] at h2
      linarith [hP0gt]
    · have h2 := congrArg Complex.re hn
      have hQre : Q.re = (polarPt (-(a/2)) (ρ₁ 0) 0).re := by rw [hQ]
      rw [Complex.neg_re, hQre] at h2
      exact hne (by linarith)
    · have h2 := congrArg Complex.re hn
      have hQre : Q.re = (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re := by rw [hQ]
      rw [Complex.neg_re, hQre] at h2
      exact hne (by linarith)
    · have h2 := congrArg Complex.re (hn.trans hQ.symm)
      have hQre : Q.re = (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re := by rw [hQ]
      rw [Complex.neg_re, hQre] at h2
      linarith [hPπlt]
  linarith [hsum, hBA]

/-- **Bisector symmetry.**  With the left axis point normalised to `-1/2` the bisector mirror
`-star '' C` has the same two real points as the curve, so the local uniqueness argument gives
`C ⊆ -star '' C`, i.e. `ρ₂ θ = ρ₁ (π - θ)`. -/
theorem normEqCurve_rho_bis {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) : ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ) := by
  have hcont₁ : Continuous ρ₁ := hC.1
  have hcont₂ : Continuous ρ₂ := hC.2.1
  have hpos₁ : ∀ θ, 0 < ρ₁ θ := hC.2.2.1
  have hpos₂ : ∀ θ, 0 < ρ₂ θ := hC.2.2.2.1
  have hchord₁ : ∀ θ, ρ₁ θ + ρ₁ (θ + Real.pi) = 1 := hC.2.2.2.2.1
  have hchord₂ : ∀ θ, ρ₂ θ + ρ₂ (θ + Real.pi) = 1 := hC.2.2.2.2.2.1
  have hrange : Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)
      = Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ) := hC.2.2.2.2.2.2
  have hAr : (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re = -(1/2) := normEqCurve_axis_half ha0 ha1 hC
  have hBA : (polarPt (-(a/2)) (ρ₁ 0) 0).re
      - (polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re = 1 := by
    rw [nec_polarPt_zero, nec_polarPt_pi]
    simp only [Complex.ofReal_re]
    have h := hchord₁ 0
    simp only [zero_add] at h
    linarith
  have hP0re : (polarPt (-(a/2)) (ρ₁ 0) 0).re = 1/2 := by linarith
  have hper₁ : ∀ θ, ρ₁ (θ + 2 * Real.pi) = ρ₁ θ := by
    intro θ
    have h1 := hchord₁ θ
    have h2 := hchord₁ (θ + Real.pi)
    have harg : θ + Real.pi + Real.pi = θ + 2 * Real.pi := by ring
    rw [harg] at h2
    linarith
  have hper₂ : ∀ θ, ρ₂ (θ + 2 * Real.pi) = ρ₂ θ := by
    intro θ
    have h1 := hchord₂ θ
    have h2 := hchord₂ (θ + Real.pi)
    have harg : θ + Real.pi + Real.pi = θ + 2 * Real.pi := by ring
    rw [harg] at h2
    linarith
  obtain ⟨A, lam, C₀, ε, hAcast, hAim, hmodel, hεlam, h2ε1, hAeq, hdist, hcurve_axis⟩ :=
    local_setup ha0 ha1 hC
  obtain ⟨σ, hσper, hσeq, hσ0, hσπ, hfix1, hfix2⟩ := eqT_lift ha0 ha1 hC
  obtain ⟨hDbclosed₀, hDbmap₀, hDbback₀⟩ := bis_mirror_invariance ha0 ha1 hC
  have hAstar : star A = A := by
    rw [Complex.star_def]; exact Complex.conj_eq_iff_im.mpr hAim
  set P : ℝ → ℂ := fun θ => polarPt (-(a/2)) (ρ₁ θ) θ with hPdef
  have hPapp : ∀ θ, P θ = polarPt (-(a/2)) (ρ₁ θ) θ := fun θ => rfl
  have hPcont : Continuous P := by
    show Continuous (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)
    unfold polarPt; fun_prop
  have hPpi : P Real.pi = A := by rw [hPapp]; exact hAeq.symm
  have hCclosed : IsClosed (Set.range P) :=
    (polarPt_compact (a := a) hcont₁ hper₁).isClosed
  have hCmap : Set.MapsTo (eqT a) (Set.range P) (Set.range P) := by
    intro z hz
    obtain ⟨θ, rfl⟩ := hz
    have h1 : chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ)
        ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) := by
      have hmem : polarPt (-(a/2)) (ρ₁ θ) θ ∈ Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ) := by
        rw [← hrange]; exact Set.mem_range_self θ
      obtain ⟨s, hs⟩ := hmem
      rw [← hs, nec_chordMap_polarPt_O2 hpos₂ hchord₂, hrange]
      exact Set.mem_range_self (s + Real.pi)
    obtain ⟨s, hs⟩ : ∃ s : ℝ, polarPt (-(a/2)) (ρ₁ s) s
        = chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ) := by
      simpa only [Set.mem_range] using h1
    show eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) ∈ Set.range P
    rw [eqT, ← hs, nec_chordMap_polarPt_O1 hpos₁ hchord₁]
    exact Set.mem_range_self _
  have hCorb : ∀ z ∈ Set.range P, ‖z - A‖ ≤ ε →
      Tendsto (fun n : ℕ => ((eqT a)^[n]) z) atTop (nhds A) :=
    orbit_tendsto_center hmodel hεlam hCclosed hCmap hcurve_axis
  -- the bisector mirror
  set Db : Set ℂ := (fun z : ℂ => -star z) '' Set.range P with hDbdef
  have hDbEq : Db = (fun z : ℂ => -star z) '' Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) := by
    rw [hDbdef, hPdef]
  have hDbclosed : IsClosed Db := by rw [hDbEq]; exact hDbclosed₀
  have hDbmap : Set.MapsTo (eqT a) Db Db := by rw [hDbEq]; exact hDbmap₀
  have hDbback : ∀ θ, eqT a (P θ) ∈ Db → P θ ∈ Db := by
    intro θ h
    rw [hDbEq] at h ⊢
    exact hDbback₀ θ h
  -- real points of `Db` are `A` and `1/2`; only `A` is close to `A`
  have hAc : A = ((-(1/2) : ℝ) : ℂ) := by
    rw [hAeq]
    rw [show polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi
        = (((polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re : ℝ) : ℂ) from by
      apply Complex.ext
      · simp
      · rw [polarPtReflect_im, Real.sin_pi, mul_zero]; simp]
    rw [hAr]
  have hDbaxis : ∀ z ∈ Db, z.im = 0 → ‖z - A‖ ≤ 2 * ε → z = A := by
    intro z hz hzim hzn
    obtain ⟨w, hw, rfl⟩ := hz
    have hwim : w.im = 0 := by
      have h := hzim
      rw [Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg] at h
      exact h
    have hnorm : ‖-star w - A‖ = |(-star w).re - A.re| := norm_sub_real hzim hAim
    rcases nec_real_pt_of_chord hpos₁ hchord₁ hw hwim with h | h
    · -- `w = P 0`: `z = -P 0` has real part `-1/2 = A.re`
      have hzre : (-star w).re = -(polarPt (-(a/2)) (ρ₁ 0) 0).re := by
        rw [Complex.neg_re, Complex.star_def, Complex.conj_re, h]
      apply Complex.ext
      · rw [hzre, hAc, hP0re]; simp
      · rw [hzim, hAim]
    · -- `w = P π`: `z = -A = 1/2`, at distance `1` from `A`
      exfalso
      have hzre : (-star w).re = -(polarPt (-(a/2)) (ρ₁ Real.pi) Real.pi).re := by
        rw [Complex.neg_re, Complex.star_def, Complex.conj_re, h]
      have h2 : ‖-star w - A‖ = 1 := by
        rw [hnorm, hzre, hAr, hAc]
        norm_num
      linarith [h2, hzn, h2ε1]
  -- attainment for `Db` near `A`
  have hbase : polarPt (a/2) (ρ₁ (Real.pi - Real.pi)) Real.pi = A := by
    rw [show Real.pi - Real.pi = 0 by ring, nec_polarPt_pi, hAc]
    have hρ : ρ₁ 0 = (polarPt (-(a/2)) (ρ₁ 0) 0).re + a/2 := by
      rw [nec_polarPt_zero]; simp
    congr 1
    linarith [hρ, hP0re]
  have hDbatt : ∃ η' : ℝ, 0 < η' ∧ ∀ η : ℝ, |η| < η' →
      ∃ z ∈ Db, z.im = η ∧ ‖z - A‖ ≤ ε := by
    have hcont' : Continuous (fun φ : ℝ => ρ₁ (Real.pi - φ)) :=
      hcont₁.comp (continuous_const.sub continuous_id)
    have hpos' : ∀ φ : ℝ, 0 < ρ₁ (Real.pi - φ) := fun φ => hpos₁ _
    obtain ⟨η', hη'pos, hη'⟩ := attain_near (c := a/2) (θ₀ := Real.pi) hcont' hpos'
      Real.sin_pi hmodel.2.1
    refine ⟨η', hη'pos, fun η hη => ?_⟩
    obtain ⟨φ, hφim, hφn⟩ := hη' η hη
    refine ⟨polarPt (a/2) (ρ₁ (Real.pi - φ)) φ, ?_, hφim, ?_⟩
    · refine ⟨P (Real.pi - φ), Set.mem_range_self _, ?_⟩
      have h := (polarPt_reflect a ρ₁).2.1 (Real.pi - φ)
      rw [show Real.pi - (Real.pi - φ) = φ by ring] at h
      rw [hPapp]
      exact h
    · have hmid : polarPt (a/2) (ρ₁ (Real.pi - Real.pi)) Real.pi = A := hbase
      rw [← hmid]
      exact hφn
  obtain ⟨δ, hδpos, hgerm⟩ := path_enters_leaf hmodel hεlam hCclosed hCmap hcurve_axis
    hDbclosed hDbmap hDbaxis hDbatt hPcont hPpi (fun θ => Set.mem_range_self θ)
  have hsub : ∀ θ, P θ ∈ Db :=
    eqT_spread ha0 ha1 hcont₁ hper₁ hσper hσeq hσ0 hσπ hfix1 hfix2 hDbclosed hDbmap hDbback
      hδpos hgerm
  have hper : Function.Periodic ρ₂ (2 * Real.pi) := hper₂
  have hgen : ∀ θ : ℝ, ρ₂ (Real.pi - θ) = ρ₁ θ := by
    intro θ
    obtain ⟨w, hw, hwz⟩ := hsub θ
    have hwP : w ∈ Set.range (fun t => polarPt (a/2) (ρ₂ t) t) := by
      rw [← hrange]; exact hw
    obtain ⟨t, ht⟩ := hwP
    have hstar : star (P θ) = -w := by
      calc star (P θ) = star (-star w) := by rw [← hwz]
        _ = -w := by simp
    have h3 : polarPt (a/2) (ρ₁ θ) (Real.pi - θ) = polarPt (a/2) (ρ₂ t) t := by
      have h4 : polarPt (a/2) (ρ₁ θ) (Real.pi - θ) = w := by
        rw [← (polarPt_reflect a ρ₁).2.1 θ, hstar]
        simp
      rw [h4, ← ht]
    obtain ⟨hr, k, hk⟩ := polarPt_inj_mod (hpos₁ θ) (hpos₂ t) h3
    have h1 : ρ₂ (Real.pi - θ + (k : ℝ) * (2 * Real.pi)) = ρ₂ (Real.pi - θ) :=
      hper.int_mul k (Real.pi - θ)
    have h2 : Real.pi - θ + (k : ℝ) * (2 * Real.pi) = t := by linarith [hk]
    rw [h2] at h1
    linarith [h1, hr]
  intro θ
  have h1 : Real.pi - (Real.pi - θ) = θ := by ring
  have h2 := hgen (Real.pi - θ)
  rwa [h1] at h2

/-- **Symmetries (Süss; Rychlik §2.5–2.6).** A normalised two-point equichordal curve is
symmetric in the line `O₁O₂` and in its perpendicular bisector. -/
theorem normEqCurve_symmetric {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) :
    (∀ θ, ρ₁ (-θ) = ρ₁ θ) ∧ ∀ θ, ρ₂ θ = ρ₁ (Real.pi - θ) := by
  exact ⟨normEqCurve_rho_even ha0 ha1 hC, normEqCurve_rho_bis ha0 ha1 hC⟩

end Work.EQ
