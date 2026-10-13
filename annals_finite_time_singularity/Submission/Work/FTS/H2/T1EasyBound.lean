import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.HkSq_mixed_le
import Submission.Work.Spaces.HkMem_mixed_le
import Submission.Work.Spaces.HPwH2
import Submission.Work.Spaces.HardyZ
import Submission.Work.Spaces.HardyZLin.hardyZ_lintegral
import Submission.Work.Spaces.bt_aux
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.cs_integral
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.Spaces.Slots.lintegral_DzIter_le_HkSq_smooth
import Submission.Work.Spaces.Slots.lintegral_mixed_gamma_le_HkSq_smooth
import Submission.Work.FTS.H2.Defs
import Submission.Work.FTS.H2.Qd
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.H2.Transport1Aux
import Submission.Work.FTS.H2.SupMixedNB
import Submission.Work.FTS.H2.CS1D
import Submission.Work.FTS.H2.SupThetaInt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The Leibniz summands -/

/-- The `(i,b)`-th `D_z`-slot Leibniz summand of `H4PairInt α (f · D_θ g) g`. -/
def xD (f g : ℝ → ℝ → ℝ) (i b : ℕ) (z θ : ℝ) : ℝ :=
  (i.choose b : ℝ) * (Spaces.DzIter b f z θ * Spaces.mixed (i - b) 1 g z θ
    * Spaces.DzIter i g z θ * (Whz z θ) ^ 2)

/-- The `(i,j,a,b)`-th mixed-slot Leibniz summand of `H4PairInt α (f · D_θ g) g`. -/
def yM (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) (z θ : ℝ) : ℝ :=
  ((i.choose a : ℝ) * (j.choose b : ℝ)) *
    (Spaces.mixed b a f z θ * Spaces.mixed (j - b) (i - a + 1) g z θ
      * Spaces.mixed j i g z θ * (Wm α z θ) ^ 2)

/-- The pointwise majorant of `T1Easy`. -/
def EasyMajor (α : ℝ) (f g : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun z θ =>
    (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
        if i = 4 ∧ b = 0 then 0 else |xD f g i b z θ|)
    + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b z θ|)
         else 0)

/-- The product measure on the closed quadrant `[0,∞) × [0,π/2]`. -/
def pm : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ)

theorem pm_eq : pm = MeasureTheory.volume.restrict (Spaces.Iz ×ˢ Spaces.Iθ) := by
  rw [pm, MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.volume_eq_prod]

theorem dom_subset_nbhU : Spaces.Iz ×ˢ Spaces.Iθ ⊆ Spaces.nbhU := by
  rintro p hp
  obtain ⟨hz, hθ⟩ := hp
  rw [Spaces.Iz, Set.mem_Ici] at hz
  rw [Spaces.Iθ, Set.mem_Icc] at hθ
  constructor
  · show (-1 : ℝ) < p.1
    linarith [hz]
  · show (-1 : ℝ) < p.2 ∧ p.2 < π / 2 + 1
    exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩

theorem ae_pm_mem : ∀ᵐ p ∂pm, p ∈ Spaces.Iz ×ˢ Spaces.Iθ := by
  rw [pm_eq]
  exact MeasureTheory.ae_restrict_mem (measurableSet_Ici.prod measurableSet_Icc)

/-! ## The weight identities -/

/-- `(Whz z θ)² = w(z)² sin(2θ)^{-η}`. -/
theorem Whz_sq (z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Whz z θ) ^ 2 = (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) := by
  have h1 : Real.sin (2 * θ) ^ (Spaces.eta / 2) * Real.sin (2 * θ) ^ (Spaces.eta / 2)
      = Real.sin (2 * θ) ^ Spaces.eta := by
    rw [← Real.rpow_add' hs (by norm_num [Spaces.eta])]
    congr 1
    ring
  have h3 : (Real.sin (2 * θ) ^ (Spaces.eta / 2)) ^ 2 = Real.sin (2 * θ) ^ Spaces.eta := by
    rw [pow_two, h1]
  rw [Whz, Real.rpow_neg hs Spaces.eta, div_pow, h3, div_eq_mul_inv]

/-- `(Wm α z θ)² = w(z)² sin(2θ)^{-γ}`. -/
theorem Wm_sq (α : ℝ) (hα : 0 < α) (z θ : ℝ) (hs : 0 ≤ Real.sin (2 * θ)) :
    (Wm α z θ) ^ 2 = (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.gam α) := by
  have h1 : Real.sin (2 * θ) ^ (-(Spaces.gam α / 2)) * Real.sin (2 * θ) ^ (-(Spaces.gam α / 2))
      = Real.sin (2 * θ) ^ (-Spaces.gam α) := by
    rw [← Real.rpow_add' hs (by intro hh; have := Spaces.gam_pos hα; linarith)]
    congr 1
    ring
  have h2 : (Real.sin (2 * θ) ^ (-(Spaces.gam α / 2))) ^ 2
      = Real.sin (2 * θ) ^ (-Spaces.gam α) := by
    rw [pow_two, h1]
  simp only [Wm, Spaces.Wt, Spaces.wTheta, mul_pow, h2]

theorem w_zero : Spaces.w 0 = 0 := by
  simp only [Spaces.w]
  norm_num

theorem Whz_zero (θ : ℝ) : Whz 0 θ = 0 := by
  rw [Whz, w_zero, zero_div]

theorem Wm_zero (α θ : ℝ) : Wm α 0 θ = 0 := by
  rw [Wm, Spaces.Wt, w_zero, zero_mul]

/-- On the closed quadrant the `η`-weight is dominated by the `γ`-weight: `Whz ≤ Wm`. -/
theorem Whz_le_Wm (α : ℝ) (hα : 0 < α) {z θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    Whz z θ ≤ Wm α z θ := by
  have hs0 : 0 ≤ Real.sin (2 * θ) := Spaces.Slots.sin_two_nonneg_Iθ (θ := θ) hθ
  have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hw : 0 ≤ Spaces.w z := by simp only [Spaces.w]; positivity
  have hle : Real.sin (2 * θ) ^ (-(Spaces.eta / 2))
      ≤ Real.sin (2 * θ) ^ (-(Spaces.gam α / 2)) := by
    rcases eq_or_lt_of_le hs0 with hs | hs
    · rw [← hs, Real.zero_rpow (by intro h; have := Spaces.eta_pos; linarith),
        Real.zero_rpow (by intro h; have := Spaces.gam_pos hα; linarith)]
    · refine Real.rpow_le_rpow_of_exponent_ge hs hs1 ?_
      have h2 : Spaces.eta ≤ Spaces.gam α := by
        have h1 : Spaces.eta < 1 := Spaces.eta_lt_one
        have h3 : 1 < Spaces.gam α := Spaces.one_lt_gam hα
        linarith
      linarith
  rw [Whz, Wm, Spaces.Wt, Spaces.wTheta, div_eq_mul_inv, ← Real.rpow_neg hs0 (Spaces.eta / 2)]
  exact mul_le_mul_of_nonneg_left hle hw

/-- `Whz² ≤ Wm · Whz` on the closed quadrant. -/
theorem Whz_sq_le_Wm_mul (α : ℝ) (hα : 0 < α) {z θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    (Whz z θ) ^ 2 ≤ Wm α z θ * Whz z θ := by
  have h1 : Whz z θ ≤ Wm α z θ := Whz_le_Wm α hα hθ
  have h2 : 0 ≤ Whz z θ := Whz_nonneg hθ
  nlinarith [h1, h2]

/-! ## Pointwise bounds on the low-order derivatives -/

/-- Pointwise bound on the pure `D_z`-derivatives of order at most `2`. -/
theorem abs_dzIter_le_pt (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (u : ℝ → ℝ → ℝ) (b : ℕ)
    (hb : b ≤ 2) (hsm : Spaces.SmoothNbhd u) (hdec : Spaces.DecayAll 4 u)
    (hmem : Spaces.HkMem α 4 u) :
    ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ,
      |Spaces.DzIter b u z θ|
        ≤ Real.sqrt ((202 / (Spaces.gam α - 1)) * Spaces.HkSq α 4 u) :=
  fun z hz θ hθ =>
    Real.abs_le_sqrt (dzIter_sq_le_HkSq α hα hα1 u hsm hdec hmem b hb z hz θ hθ)

/-- Pointwise bound on the mixed derivatives of total order at most `2` and `θ`-order at
least `1`. -/
theorem abs_mixed_le_pt (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (u : ℝ → ℝ → ℝ) (b a : ℕ)
    (ha : 1 ≤ a) (hab : a + b ≤ 2) (hsm : Spaces.SmoothNbhd u) (hdec : Spaces.DecayAll 4 u)
    (hmem : Spaces.HkMem α 4 u) :
    ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ,
      |Spaces.mixed b a u z θ|
        ≤ Real.sqrt ((100 / (Spaces.gam α - 1)) * Spaces.HkSq α 4 u) := by
  have hvt : Spaces.VanishTheta (Spaces.mixed b a u) := by
    have h1 : Spaces.VanishTheta (Spaces.DthIter a u) := by
      obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      constructor
      · intro z
        show Real.sin (2 * 0) * Spaces.pth (Spaces.DthIter a' u) z 0 = 0
        simp
      · intro z
        show Real.sin (2 * (Real.pi / 2)) * Spaces.pth (Spaces.DthIter a' u) z (Real.pi / 2) = 0
        rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, zero_mul]
    obtain ⟨h2, h3⟩ := Spaces.bt_DzIter_vanish h1 b
    exact ⟨h2, h3⟩
  have hsm' : Spaces.SmoothNbhd (Spaces.mixed b a u) :=
    Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsm a) b
  have hmem' : Spaces.HkMem α 2 (Spaces.mixed b a u) :=
    Spaces.HkMem_mixed_le α hα hα1 u hsm hmem b a hab
  have hdec' : ∀ θ ∈ Spaces.Iθ,
      Filter.Tendsto (fun z => Spaces.mixed b a u z θ) Filter.atTop (nhds 0) :=
    fun θ hθ => hdec.2 a b (by omega) θ hθ
  have hpt := Spaces.HPwH2 α hα hα1 (Spaces.mixed b a u) hsm' hvt hdec' hmem'
  have hle : Spaces.HkSq α 2 (Spaces.mixed b a u) ≤ Spaces.HkSq α 4 u :=
    Spaces.HkSq_mixed_le α hα hα1 u hsm hmem b a hab
  have hcoef : 0 ≤ 100 / (Spaces.gam α - 1) := by
    have hγ1 : 0 < Spaces.gam α - 1 := by rw [Spaces.gam_sub_one]; linarith
    positivity
  intro z hz θ hθ
  refine le_trans (Real.abs_le_sqrt (hpt z hz θ hθ)) ?_
  exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hle hcoef)

/-- Every mixed derivative of total order at most `2` is bounded on the closed quadrant. -/
theorem supFinite_mixed_of_le2 (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (u : ℝ → ℝ → ℝ) (b a : ℕ)
    (hab : a + b ≤ 2) (hsm : Spaces.SmoothNbhd u) (hdec : Spaces.DecayAll 4 u)
    (hmem : Spaces.HkMem α 4 u) : Spaces.SupFinite (Spaces.mixed b a u) := by
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rw [Spaces.mixed_zero_right]
    exact Spaces.supFinite_of_pointwise (abs_dzIter_le_pt α hα hα1 u b (by omega) hsm hdec hmem)
  · exact Spaces.supFinite_of_pointwise (abs_mixed_le_pt α hα hα1 u b a ha hab hsm hdec hmem)

/-- The pointwise bound obtained from an `L^∞` bound together with the honesty of the
supremum. -/
theorem abs_mixed_le_of_supAbs {u : ℝ → ℝ → ℝ} {K : ℝ} (hsup : Spaces.supAbs u ≤ K)
    (hfin : Spaces.SupFinite u) {z θ : ℝ} (hz : z ∈ Spaces.Iz) (hθ : θ ∈ Spaces.Iθ) :
    |u z θ| ≤ K :=
  le_trans (Spaces.abs_le_supAbs hz hθ hfin) hsup

/-! ## Measurability -/

/-- A function continuous on the open quadrant is a.e. strongly measurable for the product
measure on the quadrant. -/
theorem aesm_of_Qd {F : ℝ × ℝ → ℝ} (h : ContinuousOn F Qd) :
    AEStronglyMeasurable F pm :=
  Work.Spaces.aesm_of_continuousOn_Qd F (by simpa only [Qd] using h)

/-- A function continuous on the open quadrant whose `z = 0` slice vanishes is a.e.
strongly measurable on every angular slice of the closed quadrant. -/
theorem aesm_slice_of_Qd_or_zero (F : ℝ → ℝ → ℝ) (h : ContinuousOn (Function.uncurry F) Qd)
    (h0 : ∀ θ, F 0 θ = 0) {z : ℝ} (hz : z ∈ Spaces.Iz) :
    AEStronglyMeasurable (fun θ => F z θ) (volume.restrict Spaces.Iθ) := by
  have hz' : (0 : ℝ) ≤ z := by
    rw [Spaces.Iz, Set.mem_Ici] at hz
    exact hz
  rcases eq_or_lt_of_le hz' with hz0 | hzpos
  · subst hz0
    refine (aestronglyMeasurable_const (b := (0 : ℝ))).congr
      (Eventually.of_forall fun θ => (h0 θ).symm)
  · exact Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry F)
      (by simpa only [Qd] using h) hzpos

/-- The `θ`-slice of `D_z^i u`, as a function of `θ`, is continuous on the closed interval. -/
theorem continuousOn_slice_dzIter (u : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd u) (i : ℕ)
    {z : ℝ} (hz : z ∈ Spaces.Iz) :
    ContinuousOn (fun θ => Spaces.DzIter i u z θ) Spaces.Iθ := by
  have hz1 : (-1 : ℝ) < z := by
    rw [Spaces.Iz, Set.mem_Ici] at hz
    linarith
  have hmap : Set.MapsTo (fun θ : ℝ => (z, θ)) Spaces.Iθ Spaces.nbhU := fun θ hθ =>
    ⟨hz1,
      by
        rw [Spaces.Iθ, Set.mem_Icc] at hθ
        simp only [Set.mem_Ioo]
        exact ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩⟩
  exact (Spaces.SmoothNbhd.DzIter hsm i).continuousOn.comp
    (continuousOn_const.prodMk continuousOn_id) hmap

theorem aesm_slice_dzIter_abs (u : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd u) (i : ℕ) {z : ℝ}
    (hz : z ∈ Spaces.Iz) :
    AEStronglyMeasurable (fun θ => |Spaces.DzIter i u z θ|) (volume.restrict Spaces.Iθ) :=
  ((continuousOn_slice_dzIter u hsm i hz).abs).aestronglyMeasurable measurableSet_Icc

theorem continuousOn_slice_mixed_abs (u : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd u) (j i : ℕ)
    {z : ℝ} (hz : z ∈ Spaces.Iz) :
    ContinuousOn (fun θ => |Spaces.mixed j i u z θ|) Spaces.Iθ := by
  have hsm' : Spaces.SmoothNbhd (Spaces.DthIter i u) := Spaces.SmoothNbhd.DthIter hsm i
  have h := continuousOn_slice_dzIter (Spaces.DthIter i u) hsm' j hz
  exact h.abs

theorem aesm_slice_mixed_abs (u : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd u) (j i : ℕ) {z : ℝ}
    (hz : z ∈ Spaces.Iz) :
    AEStronglyMeasurable (fun θ => |Spaces.mixed j i u z θ|) (volume.restrict Spaces.Iθ) :=
  ((continuousOn_slice_mixed_abs u hsm j i hz)).aestronglyMeasurable measurableSet_Icc

/-- The product of three absolute values of smooth functions and two weights continuous on
the open quadrant is a.e. strongly measurable for the product measure. -/
theorem aesm_prod_three (u v w : ℝ → ℝ → ℝ) (hu : Spaces.SmoothNbhd u)
    (hv : Spaces.SmoothNbhd v) (hw : Spaces.SmoothNbhd w) {ρ σ : ℝ → ℝ → ℝ}
    (hρ : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Qd)
    (hσ : ContinuousOn (fun p : ℝ × ℝ => σ p.1 p.2) Qd) :
    AEStronglyMeasurable (Function.uncurry (fun z θ =>
      |u z θ * (|v z θ| * ρ z θ) * (|w z θ| * σ z θ)|)) pm := by
  have hu' : ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) Qd :=
    hu.continuousOn.mono Qd_subset_nbhU
  have hv' : ContinuousOn (fun p : ℝ × ℝ => |v p.1 p.2|) Qd :=
    (hv.continuousOn.mono Qd_subset_nbhU).abs
  have hw' : ContinuousOn (fun p : ℝ × ℝ => |w p.1 p.2|) Qd :=
    (hw.continuousOn.mono Qd_subset_nbhU).abs
  exact aesm_of_Qd (((hu'.mul (hv'.mul hρ)).mul (hw'.mul hσ)).abs)

/-! ## The generic Cauchy–Schwarz bound -/

/-- Cauchy–Schwarz bound for a triple product `V · A · B` whose two "slot" factors are
dominated by the `ℋ⁴`-integrands of `u` resp. `v`, and whose first factor is bounded by `K`. -/
theorem slot_pair_bound (α : ℝ) (u v : ℝ → ℝ → ℝ)
    (hmu : Spaces.HkMem α 4 u) (hmv : Spaces.HkMem α 4 v)
    (A B V : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hV : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, |V z θ| ≤ K)
    (hA0 : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, 0 ≤ A z θ)
    (hB0 : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, 0 ≤ B z θ)
    (hA : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, (A z θ) ^ 2 ≤ Spaces.HkIntegrand α 4 u z θ)
    (hB : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, (B z θ) ^ 2 ≤ Spaces.HkIntegrand α 4 v z θ)
    (hAmeas : ∀ z ∈ Spaces.Iz,
      AEStronglyMeasurable (fun θ => A z θ) (volume.restrict Spaces.Iθ))
    (hBmeas : ∀ z ∈ Spaces.Iz,
      AEStronglyMeasurable (fun θ => B z θ) (volume.restrict Spaces.Iθ))
    (hVABmeas : AEStronglyMeasurable
      (Function.uncurry (fun z θ => |V z θ * A z θ * B z θ|)) pm) :
    MeasureTheory.Integrable
        (fun z => ∫ θ in Spaces.Iθ, |V z θ * A z θ * B z θ|) (volume.restrict Spaces.Iz) ∧
      ∫ z in Spaces.Iz, (∫ θ in Spaces.Iθ, |V z θ * A z θ * B z θ|)
        ≤ K * Spaces.HkNorm α 4 u * Spaces.HkNorm α 4 v := by
  set Φu : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α 4 u z θ with hΦu
  set Φv : ℝ → ℝ := fun z => ∫ θ in Spaces.Iθ, Spaces.HkIntegrand α 4 v z θ with hΦv
  have hΦu_nn : ∀ z, 0 ≤ Φu z :=
    fun z => integral_nonneg fun θ => Spaces.HkIntegrand_nonneg α 4 u z θ
  have hΦv_nn : ∀ z, 0 ≤ Φv z :=
    fun z => integral_nonneg fun θ => Spaces.HkIntegrand_nonneg α 4 v z θ
  have hA2int : ∀ z ∈ Spaces.Iz, IntegrableOn (fun θ => (A z θ) ^ 2) Spaces.Iθ := by
    intro z hz
    refine MeasureTheory.Integrable.mono' (hmu.1 z hz) ((hAmeas z hz).pow 2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hA z hz θ hθ
  have hB2int : ∀ z ∈ Spaces.Iz, IntegrableOn (fun θ => (B z θ) ^ 2) Spaces.Iθ := by
    intro z hz
    refine MeasureTheory.Integrable.mono' (hmv.1 z hz) ((hBmeas z hz).pow 2) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hB z hz θ hθ
  have hA2le : ∀ z ∈ Spaces.Iz, ∫ θ in Spaces.Iθ, (A z θ) ^ 2 ≤ Φu z := fun z hz =>
    setIntegral_mono_of_nonneg (fun θ _ => sq_nonneg _) (fun θ hθ => hA z hz θ hθ) (hmu.1 z hz)
  have hB2le : ∀ z ∈ Spaces.Iz, ∫ θ in Spaces.Iθ, (B z θ) ^ 2 ≤ Φv z := fun z hz =>
    setIntegral_mono_of_nonneg (fun θ _ => sq_nonneg _) (fun θ hθ => hB z hz θ hθ) (hmv.1 z hz)
  have hABint : ∀ z ∈ Spaces.Iz, IntegrableOn (fun θ => A z θ * B z θ) Spaces.Iθ := by
    intro z hz
    refine MeasureTheory.Integrable.mono' ((hmu.1 z hz).add (hmv.1 z hz))
      ((hAmeas z hz).mul (hBmeas z hz)) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (mul_nonneg (hA0 z hz θ hθ) (hB0 z hz θ hθ))]
    have h1 := hA z hz θ hθ
    have h2 := hB z hz θ hθ
    have hn1 : 0 ≤ Spaces.HkIntegrand α 4 u z θ := Spaces.HkIntegrand_nonneg α 4 u z θ
    have hn2 : 0 ≤ Spaces.HkIntegrand α 4 v z θ := Spaces.HkIntegrand_nonneg α 4 v z θ
    have hmain : A z θ * B z θ
        ≤ Spaces.HkIntegrand α 4 u z θ + Spaces.HkIntegrand α 4 v z θ := by
      nlinarith [sq_nonneg (A z θ - B z θ)]
    simpa only [Pi.add_apply] using hmain
  have hMemLpA : ∀ z ∈ Spaces.Iz, MemLp (fun θ => A z θ) 2 (volume.restrict Spaces.Iθ) := by
    intro z hz
    exact (memLp_two_iff_integrable_sq (hAmeas z hz)).mpr (hA2int z hz)
  have hMemLpB : ∀ z ∈ Spaces.Iz, MemLp (fun θ => B z θ) 2 (volume.restrict Spaces.Iθ) := by
    intro z hz
    exact (memLp_two_iff_integrable_sq (hBmeas z hz)).mpr (hB2int z hz)
  have hCSθ : ∀ z ∈ Spaces.Iz,
      ∫ θ in Spaces.Iθ, A z θ * B z θ
        ≤ Real.sqrt (∫ θ in Spaces.Iθ, (A z θ) ^ 2)
          * Real.sqrt (∫ θ in Spaces.Iθ, (B z θ) ^ 2) := by
    intro z hz
    have hA0ae : 0 ≤ᵐ[volume.restrict Spaces.Iθ] (fun θ => A z θ) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hA0 z hz θ hθ)
    have hB0ae : 0 ≤ᵐ[volume.restrict Spaces.Iθ] (fun θ => B z θ) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hB0 z hz θ hθ)
    have hABnn : 0 ≤ᵐ[volume.restrict Spaces.Iθ] (fun θ => A z θ * B z θ) := by
      filter_upwards [hA0ae, hB0ae] with θ h1 h2
      exact mul_nonneg h1 h2
    have hg : ∀ᵐ θ ∂(volume.restrict Spaces.Iθ), |A z θ * B z θ| ≤ A z θ * B z θ := by
      filter_upwards [hABnn] with θ h1
      rw [abs_of_nonneg h1]
    have h := CS1D (μ := volume.restrict Spaces.Iθ) (g := fun θ => A z θ * B z θ)
      (A := fun θ => A z θ) (B := fun θ => B z θ) (hMemLpA z hz) (hMemLpB z hz) hA0ae hB0ae hg
    rwa [abs_of_nonneg (integral_nonneg_of_ae hABnn)] at h
  have hinner : ∀ z ∈ Spaces.Iz,
      ∫ θ in Spaces.Iθ, |V z θ * A z θ * B z θ| ≤ K * (Real.sqrt (Φu z) * Real.sqrt (Φv z)) := by
    intro z hz
    have h1 : ∫ θ in Spaces.Iθ, |V z θ * A z θ * B z θ|
        ≤ ∫ θ in Spaces.Iθ, K * (A z θ * B z θ) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _)
        ((hABint z hz).const_mul K) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [abs_mul, abs_mul, abs_of_nonneg (hA0 z hz θ hθ), abs_of_nonneg (hB0 z hz θ hθ)]
      calc |V z θ| * A z θ * B z θ = |V z θ| * (A z θ * B z θ) := by ring
        _ ≤ K * (A z θ * B z θ) :=
            mul_le_mul_of_nonneg_right (hV z hz θ hθ) (mul_nonneg (hA0 z hz θ hθ) (hB0 z hz θ hθ))
    calc ∫ θ in Spaces.Iθ, |V z θ * A z θ * B z θ|
        ≤ ∫ θ in Spaces.Iθ, K * (A z θ * B z θ) := h1
      _ = K * ∫ θ in Spaces.Iθ, A z θ * B z θ := integral_const_mul K _
      _ ≤ K * (Real.sqrt (∫ θ in Spaces.Iθ, (A z θ) ^ 2)
            * Real.sqrt (∫ θ in Spaces.Iθ, (B z θ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (hCSθ z hz) hK
      _ ≤ K * (Real.sqrt (Φu z) * Real.sqrt (Φv z)) := by
          refine mul_le_mul_of_nonneg_left ?_ hK
          exact mul_le_mul (Real.sqrt_le_sqrt (hA2le z hz)) (Real.sqrt_le_sqrt (hB2le z hz))
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hmu_lp : MemLp (fun z => Real.sqrt (Φu z)) 2 (volume.restrict Spaces.Iz) := by
    refine (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hmu.2.aestronglyMeasurable)).mpr ?_
    refine hmu.2.congr ?_
    filter_upwards with z
    rw [Real.sq_sqrt (hΦu_nn z)]
  have hmv_lp : MemLp (fun z => Real.sqrt (Φv z)) 2 (volume.restrict Spaces.Iz) := by
    refine (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hmv.2.aestronglyMeasurable)).mpr ?_
    refine hmv.2.congr ?_
    filter_upwards with z
    rw [Real.sq_sqrt (hΦv_nn z)]
  have hprod_int : Integrable (fun z => Real.sqrt (Φu z) * Real.sqrt (Φv z))
      (volume.restrict Spaces.Iz) := memLp_one_iff_integrable.mp (hmu_lp.mul hmv_lp)
  have houter : ∫ z in Spaces.Iz, (∫ θ in Spaces.Iθ, |V z θ * A z θ * B z θ|)
      ≤ K * ∫ z in Spaces.Iz, (Real.sqrt (Φu z) * Real.sqrt (Φv z)) := by
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ => abs_nonneg _)
      (hprod_int.const_mul K) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    exact hinner z hz
  have hQu : (∫ z in Spaces.Iz, Real.sqrt (Φu z) ^ 2) = Spaces.HkSq α 4 u := by
    rw [Spaces.HkSq, hΦu]
    exact integral_congr_ae (Eventually.of_forall fun z => Real.sq_sqrt (hΦu_nn z))
  have hQv : (∫ z in Spaces.Iz, Real.sqrt (Φv z) ^ 2) = Spaces.HkSq α 4 v := by
    rw [Spaces.HkSq, hΦv]
    exact integral_congr_ae (Eventually.of_forall fun z => Real.sq_sqrt (hΦv_nn z))
  have hsqrt : ∫ z in Spaces.Iz, (Real.sqrt (Φu z) * Real.sqrt (Φv z))
      ≤ Spaces.HkNorm α 4 u * Spaces.HkNorm α 4 v := by
    have hsq : (∫ z in Spaces.Iz, Real.sqrt (Φu z) * Real.sqrt (Φv z)) ^ 2
        ≤ Spaces.HkSq α 4 u * Spaces.HkSq α 4 v := by
      rw [← hQu, ← hQv]
      exact Work.Spaces.cs_integral hmu_lp hmv_lp
    calc ∫ z in Spaces.Iz, (Real.sqrt (Φu z) * Real.sqrt (Φv z))
        ≤ Real.sqrt (Spaces.HkSq α 4 u * Spaces.HkSq α 4 v) := Real.le_sqrt_of_sq_le hsq
      _ = Real.sqrt (Spaces.HkSq α 4 u) * Real.sqrt (Spaces.HkSq α 4 v) :=
          Real.sqrt_mul (Spaces.HkSq_nonneg α 4 u) _
      _ = Spaces.HkNorm α 4 u * Spaces.HkNorm α 4 v := rfl
  constructor
  · refine MeasureTheory.Integrable.mono' (hprod_int.const_mul K)
      hVABmeas.integral_prod_right' ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => abs_nonneg _)]
    exact hinner z hz
  · calc ∫ z in Spaces.Iz, (∫ θ in Spaces.Iθ, |V z θ * A z θ * B z θ|)
        ≤ K * ∫ z in Spaces.Iz, (Real.sqrt (Φu z) * Real.sqrt (Φv z)) := houter
      _ ≤ K * (Spaces.HkNorm α 4 u * Spaces.HkNorm α 4 v) :=
          mul_le_mul_of_nonneg_left hsqrt hK
      _ = K * Spaces.HkNorm α 4 u * Spaces.HkNorm α 4 v := by ring

/-- The two-dimensional form of `slot_pair_bound`: the integrand is integrable on the
product measure, with the bound expressed as a two-dimensional integral. -/
theorem term_of_slot (α : ℝ) (u v : ℝ → ℝ → ℝ)
    (hmu : Spaces.HkMem α 4 u) (hmv : Spaces.HkMem α 4 v)
    (A B V : ℝ → ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hV : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, |V z θ| ≤ K)
    (hA0 : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, 0 ≤ A z θ)
    (hB0 : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, 0 ≤ B z θ)
    (hA : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, (A z θ) ^ 2 ≤ Spaces.HkIntegrand α 4 u z θ)
    (hB : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, (B z θ) ^ 2 ≤ Spaces.HkIntegrand α 4 v z θ)
    (hAmeas : ∀ z ∈ Spaces.Iz,
      AEStronglyMeasurable (fun θ => A z θ) (volume.restrict Spaces.Iθ))
    (hBmeas : ∀ z ∈ Spaces.Iz,
      AEStronglyMeasurable (fun θ => B z θ) (volume.restrict Spaces.Iθ))
    (hVABmeas : AEStronglyMeasurable
      (Function.uncurry (fun z θ => |V z θ * A z θ * B z θ|)) pm) :
    MeasureTheory.Integrable (Function.uncurry (fun z θ => |V z θ * A z θ * B z θ|)) pm ∧
      (∫ p, |V p.1 p.2 * A p.1 p.2 * B p.1 p.2| ∂pm)
        ≤ K * Spaces.HkNorm α 4 u * Spaces.HkNorm α 4 v := by
  obtain ⟨houter, hbd⟩ :=
    slot_pair_bound α u v hmu hmv A B V K hK hV hA0 hB0 hA hB hAmeas hBmeas hVABmeas
  have hslice : ∀ᵐ z ∂(volume.restrict Spaces.Iz),
      Integrable (fun θ => |V z θ * A z θ * B z θ|) (volume.restrict Spaces.Iθ) := by
    filter_upwards [hVABmeas.prodMk_left,
      MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hzmeas hzmem
    have hmain : Integrable (fun θ => Spaces.HkIntegrand α 4 u z θ
        + Spaces.HkIntegrand α 4 v z θ) (volume.restrict Spaces.Iθ) :=
      (hmu.1 z hzmem).add (hmv.1 z hzmem)
    refine MeasureTheory.Integrable.mono' (hmain.const_mul K) hzmeas ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    have h1 := hA z hzmem θ hθ
    have h2 := hB z hzmem θ hθ
    have hn1 : 0 ≤ Spaces.HkIntegrand α 4 u z θ := Spaces.HkIntegrand_nonneg α 4 u z θ
    have hn2 : 0 ≤ Spaces.HkIntegrand α 4 v z θ := Spaces.HkIntegrand_nonneg α 4 v z θ
    rw [abs_mul, abs_mul, abs_of_nonneg (hA0 z hzmem θ hθ), abs_of_nonneg (hB0 z hzmem θ hθ)]
    have hstep : |V z θ| * A z θ * B z θ ≤ K * (A z θ * B z θ) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (hV z hzmem θ hθ)
        (mul_nonneg (hA0 z hzmem θ hθ) (hB0 z hzmem θ hθ))
    have hAB : A z θ * B z θ ≤ Spaces.HkIntegrand α 4 u z θ + Spaces.HkIntegrand α 4 v z θ := by
      nlinarith [sq_nonneg (A z θ - B z θ)]
    have hK2 : 0 ≤ K := hK
    calc |V z θ| * A z θ * B z θ ≤ K * (A z θ * B z θ) := hstep
      _ ≤ K * (Spaces.HkIntegrand α 4 u z θ + Spaces.HkIntegrand α 4 v z θ) :=
          mul_le_mul_of_nonneg_left hAB hK2
  obtain ⟨h2d, hval⟩ := Work.Spaces.integrable_prod_of_iterated
    (fun z θ => abs_nonneg _) hVABmeas hslice houter
  exact ⟨h2d, by
    rw [show pm = (MeasureTheory.volume.restrict Spaces.Iz).prod
      (MeasureTheory.volume.restrict Spaces.Iθ) from rfl, hval]
    exact hbd⟩

/-! ## The four pointwise estimates for a single Leibniz summand -/

/-- The `D_z`-slot estimate in the case where the `f`-factor has order `≤ 2`. -/
theorem xDKf_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ) (Kf : ℝ)
    (hsmf : Spaces.SmoothNbhd f) (hsmg : Spaces.SmoothNbhd g)
    (hdecf : Spaces.DecayAll 4 f) (hdecg : Spaces.DecayAll 4 g)
    (hmemf : Spaces.HkMem α 4 f) (hmemg : Spaces.HkMem α 4 g)
    (hKf : ∀ b a : ℕ, a + b ≤ 2 → Spaces.supAbs (Spaces.mixed b a f) ≤ Kf)
    (hKf0 : 0 ≤ Kf) (i b : ℕ) (hi : i ≤ 4) (hbi : b ≤ i) (hib : i - b ≤ 3) (hb2 : b ≤ 2) :
    MeasureTheory.Integrable (Function.uncurry (fun z θ => |Spaces.DzIter b f z θ *
        (|Spaces.mixed (i - b) 1 g z θ| * Wm α z θ) * (|Spaces.DzIter i g z θ| * Whz z θ)|))
      pm ∧
      (∫ p, |Spaces.DzIter b f p.1 p.2 *
        (|Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2)
        * (|Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)| ∂pm)
        ≤ Kf * Spaces.HkNorm α 4 g * Spaces.HkNorm α 4 g := by
  have hV : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, |Spaces.DzIter b f z θ| ≤ Kf := by
    intro z hz θ hθ
    have h1 := abs_mixed_le_of_supAbs (hKf b 0 (by omega))
      (supFinite_mixed_of_le2 α hα hα1 f b 0 (by omega) hsmf hdecf hmemf) hz hθ
    rwa [Spaces.mixed_zero_right] at h1
  have hAcont : ContinuousOn (fun p : ℝ × ℝ =>
      |Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2) Qd :=
    (((Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg 1) (i - b)).continuousOn.mono
      Qd_subset_nbhU).abs).mul (continuousOn_Wm_Qd α)
  have hBcont : ContinuousOn (fun p : ℝ × ℝ =>
      |Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2) Qd :=
    (((Spaces.SmoothNbhd.DzIter hsmg i).continuousOn.mono Qd_subset_nbhU).abs).mul
      continuousOn_Whz_Qd
  obtain ⟨hint, hbd⟩ := term_of_slot α g g hmemg hmemg
    (fun z θ => |Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
    (fun z θ => |Spaces.DzIter i g z θ| * Whz z θ)
    (fun z θ => Spaces.DzIter b f z θ) Kf hKf0 hV
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Wm_nonneg α hθ))
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Whz_nonneg hθ))
    (fun z hz θ hθ => by
      simpa only [Wm, mul_pow, sq_abs] using
        Spaces.sq_le_HkIntegrand_mixed α 4 g z θ 1 (i - b) (le_refl 1) (by omega))
    (fun z hz θ hθ => by
      simpa only [Whz, mul_pow, sq_abs] using Spaces.sq_le_HkIntegrand_z α 4 g z θ i hi)
    (fun z hz => aesm_slice_of_Qd_or_zero (fun z θ => |Spaces.mixed (i - b) 1 g z θ| * Wm α z θ) hAcont
      (fun θ => by rw [Wm, Spaces.Wt, w_zero, zero_mul, mul_zero]) hz)
    (fun z hz => aesm_slice_of_Qd_or_zero (fun z θ => |Spaces.DzIter i g z θ| * Whz z θ) hBcont
      (fun θ => by rw [Whz, w_zero, zero_div, mul_zero]) hz)
    (aesm_prod_three (Spaces.DzIter b f) (Spaces.mixed (i - b) 1 g) (Spaces.DzIter i g)
      (Spaces.SmoothNbhd.DzIter hsmf b)
      (Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg 1) (i - b))
      (Spaces.SmoothNbhd.DzIter hsmg i) (continuousOn_Wm_Qd α) continuousOn_Whz_Qd)
  exact ⟨hint, hbd⟩

/-- The `D_z`-slot estimate in the case where the `g`-factor `D_z^{i-b}D_θ g` has order
`≤ 2` (i.e. `b ≥ 3`). -/
theorem xDKg_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ) (Kg : ℝ)
    (hsmf : Spaces.SmoothNbhd f) (hsmg : Spaces.SmoothNbhd g)
    (hdecf : Spaces.DecayAll 4 f) (hdecg : Spaces.DecayAll 4 g)
    (hmemf : Spaces.HkMem α 4 f) (hmemg : Spaces.HkMem α 4 g)
    (hKg : ∀ b a : ℕ, a + b ≤ 2 → Spaces.supAbs (Spaces.mixed b a g) ≤ Kg)
    (hKg0 : 0 ≤ Kg) (i b : ℕ) (hi : i ≤ 4) (hbi : b ≤ i) (hb3 : 3 ≤ b) :
    MeasureTheory.Integrable (Function.uncurry (fun z θ => |Spaces.mixed (i - b) 1 g z θ *
        (|Spaces.DzIter b f z θ| * Whz z θ) * (|Spaces.DzIter i g z θ| * Whz z θ)|)) pm ∧
      (∫ p, |Spaces.mixed (i - b) 1 g p.1 p.2 *
        (|Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2)
        * (|Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)| ∂pm)
        ≤ Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g := by
  have hV : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, |Spaces.mixed (i - b) 1 g z θ| ≤ Kg :=
    fun z hz θ hθ =>
      abs_mixed_le_of_supAbs (hKg (i - b) 1 (by omega))
        (supFinite_mixed_of_le2 α hα hα1 g (i - b) 1 (by omega) hsmg hdecg hmemg) hz hθ
  have hAcont : ContinuousOn (fun p : ℝ × ℝ =>
      |Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2) Qd :=
    (((Spaces.SmoothNbhd.DzIter hsmf b).continuousOn.mono Qd_subset_nbhU).abs).mul
      continuousOn_Whz_Qd
  have hBcont : ContinuousOn (fun p : ℝ × ℝ =>
      |Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2) Qd :=
    (((Spaces.SmoothNbhd.DzIter hsmg i).continuousOn.mono Qd_subset_nbhU).abs).mul
      continuousOn_Whz_Qd
  obtain ⟨hint, hbd⟩ := term_of_slot α f g hmemf hmemg
    (fun z θ => |Spaces.DzIter b f z θ| * Whz z θ)
    (fun z θ => |Spaces.DzIter i g z θ| * Whz z θ)
    (fun z θ => Spaces.mixed (i - b) 1 g z θ) Kg hKg0 hV
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Whz_nonneg hθ))
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Whz_nonneg hθ))
    (fun z hz θ hθ => by
      simpa only [Whz, mul_pow, sq_abs] using Spaces.sq_le_HkIntegrand_z α 4 f z θ b (by omega))
    (fun z hz θ hθ => by
      simpa only [Whz, mul_pow, sq_abs] using Spaces.sq_le_HkIntegrand_z α 4 g z θ i hi)
    (fun z hz => aesm_slice_of_Qd_or_zero (fun z θ => |Spaces.DzIter b f z θ| * Whz z θ) hAcont
      (fun θ => by rw [Whz, w_zero, zero_div, mul_zero]) hz)
    (fun z hz => aesm_slice_of_Qd_or_zero (fun z θ => |Spaces.DzIter i g z θ| * Whz z θ) hBcont
      (fun θ => by rw [Whz, w_zero, zero_div, mul_zero]) hz)
    (aesm_prod_three (Spaces.mixed (i - b) 1 g) (Spaces.DzIter b f) (Spaces.DzIter i g)
      (Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg 1) (i - b))
      (Spaces.SmoothNbhd.DzIter hsmf b) (Spaces.SmoothNbhd.DzIter hsmg i)
      continuousOn_Whz_Qd continuousOn_Whz_Qd)
  exact ⟨hint, hbd⟩

/-- The mixed-slot estimate in the case where the `f`-factor has order `≤ 2`. -/
theorem yMKf_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ) (Kf : ℝ)
    (hsmf : Spaces.SmoothNbhd f) (hsmg : Spaces.SmoothNbhd g)
    (hdecf : Spaces.DecayAll 4 f) (hdecg : Spaces.DecayAll 4 g)
    (hmemf : Spaces.HkMem α 4 f) (hmemg : Spaces.HkMem α 4 g)
    (hKf : ∀ b a : ℕ, a + b ≤ 2 → Spaces.supAbs (Spaces.mixed b a f) ≤ Kf)
    (hKf0 : 0 ≤ Kf) (i j a b : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (ha : a ≤ i) (hb : b ≤ j)
    (hab : a + b ≤ 2) (hnh : ¬(a = 0 ∧ b = 0 ∧ i + j = 4)) :
    MeasureTheory.Integrable (Function.uncurry (fun z θ => |Spaces.mixed b a f z θ *
        (|Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
        * (|Spaces.mixed j i g z θ| * Wm α z θ)|)) pm ∧
      (∫ p, |Spaces.mixed b a f p.1 p.2 *
        (|Spaces.mixed (j - b) (i - a + 1) g p.1 p.2| * Wm α p.1 p.2)
        * (|Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2)| ∂pm)
        ≤ Kf * Spaces.HkNorm α 4 g * Spaces.HkNorm α 4 g := by
  have hV : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, |Spaces.mixed b a f z θ| ≤ Kf :=
    fun z hz θ hθ =>
      abs_mixed_le_of_supAbs (hKf b a hab)
        (supFinite_mixed_of_le2 α hα hα1 f b a hab hsmf hdecf hmemf) hz hθ
  have hord : (i - a + 1) + (j - b) ≤ 4 := by
    by_cases hab0 : a + b = 0
    · have ha0 : a = 0 := by omega
      have hb0 : b = 0 := by omega
      have hij3 : i + j ≤ 3 := by
        by_contra hcon
        exact hnh ⟨ha0, hb0, by omega⟩
      omega
    · omega
  have hAcont : ContinuousOn (fun p : ℝ × ℝ =>
      |Spaces.mixed (j - b) (i - a + 1) g p.1 p.2| * Wm α p.1 p.2) Qd :=
    (((Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg (i - a + 1)) (j - b)).continuousOn.mono
      Qd_subset_nbhU).abs).mul (continuousOn_Wm_Qd α)
  have hBcont : ContinuousOn (fun p : ℝ × ℝ =>
      |Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2) Qd :=
    (((Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg i) j).continuousOn.mono
      Qd_subset_nbhU).abs).mul (continuousOn_Wm_Qd α)
  obtain ⟨hint, hbd⟩ := term_of_slot α g g hmemg hmemg
    (fun z θ => |Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
    (fun z θ => |Spaces.mixed j i g z θ| * Wm α z θ)
    (fun z θ => Spaces.mixed b a f z θ) Kf hKf0 hV
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Wm_nonneg α hθ))
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Wm_nonneg α hθ))
    (fun z hz θ hθ => by
      simpa only [Wm, mul_pow, sq_abs] using
        Spaces.sq_le_HkIntegrand_mixed α 4 g z θ (i - a + 1) (j - b) (by omega) hord)
    (fun z hz θ hθ => by
      simpa only [Wm, mul_pow, sq_abs] using
        Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij)
    (fun z hz => aesm_slice_of_Qd_or_zero (fun z θ => |Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ) hAcont
      (fun θ => by rw [Wm, Spaces.Wt, w_zero, zero_mul, mul_zero]) hz)
    (fun z hz => aesm_slice_of_Qd_or_zero (fun z θ => |Spaces.mixed j i g z θ| * Wm α z θ) hBcont
      (fun θ => by rw [Wm, Spaces.Wt, w_zero, zero_mul, mul_zero]) hz)
    (aesm_prod_three (Spaces.mixed b a f) (Spaces.mixed (j - b) (i - a + 1) g)
      (Spaces.mixed j i g)
      (Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmf a) b)
      (Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg (i - a + 1)) (j - b))
      (Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg i) j)
      (continuousOn_Wm_Qd α) (continuousOn_Wm_Qd α))
  exact ⟨hint, hbd⟩

/-- The mixed-slot estimate in the case where the `g`-factor has `θ`-order `≥ 1` and
order `≤ 2`. -/
theorem yMKg_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ) (Kg : ℝ)
    (hsmf : Spaces.SmoothNbhd f) (hsmg : Spaces.SmoothNbhd g)
    (hdecf : Spaces.DecayAll 4 f) (hdecg : Spaces.DecayAll 4 g)
    (hmemf : Spaces.HkMem α 4 f) (hmemg : Spaces.HkMem α 4 g)
    (hKg : ∀ b a : ℕ, a + b ≤ 2 → Spaces.supAbs (Spaces.mixed b a g) ≤ Kg)
    (hKg0 : 0 ≤ Kg) (i j a b : ℕ) (hi : 1 ≤ i) (hij : i + j ≤ 4) (ha : a ≤ i) (hb : b ≤ j)
    (ha1 : 1 ≤ a) (hab : 3 ≤ a + b) :
    MeasureTheory.Integrable (Function.uncurry (fun z θ =>
        |Spaces.mixed (j - b) (i - a + 1) g z θ *
        (|Spaces.mixed b a f z θ| * Wm α z θ)
        * (|Spaces.mixed j i g z θ| * Wm α z θ)|)) pm ∧
      (∫ p, |Spaces.mixed (j - b) (i - a + 1) g p.1 p.2 *
        (|Spaces.mixed b a f p.1 p.2| * Wm α p.1 p.2)
        * (|Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2)| ∂pm)
        ≤ Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g := by
  have hV : ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ,
      |Spaces.mixed (j - b) (i - a + 1) g z θ| ≤ Kg :=
    fun z hz θ hθ =>
      abs_mixed_le_of_supAbs (hKg (j - b) (i - a + 1) (by omega))
        (supFinite_mixed_of_le2 α hα hα1 g (j - b) (i - a + 1) (by omega) hsmg hdecg hmemg)
        hz hθ
  have hAcont : ContinuousOn (fun p : ℝ × ℝ =>
      |Spaces.mixed b a f p.1 p.2| * Wm α p.1 p.2) Qd :=
    (((Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmf a) b).continuousOn.mono
      Qd_subset_nbhU).abs).mul (continuousOn_Wm_Qd α)
  have hBcont : ContinuousOn (fun p : ℝ × ℝ =>
      |Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2) Qd :=
    (((Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg i) j).continuousOn.mono
      Qd_subset_nbhU).abs).mul (continuousOn_Wm_Qd α)
  obtain ⟨hint, hbd⟩ := term_of_slot α f g hmemf hmemg
    (fun z θ => |Spaces.mixed b a f z θ| * Wm α z θ)
    (fun z θ => |Spaces.mixed j i g z θ| * Wm α z θ)
    (fun z θ => Spaces.mixed (j - b) (i - a + 1) g z θ) Kg hKg0 hV
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Wm_nonneg α hθ))
    (fun z hz θ hθ => mul_nonneg (abs_nonneg _) (Wm_nonneg α hθ))
    (fun z hz θ hθ => by
      simpa only [Wm, mul_pow, sq_abs] using
        Spaces.sq_le_HkIntegrand_mixed α 4 f z θ a b ha1 (by omega))
    (fun z hz θ hθ => by
      simpa only [Wm, mul_pow, sq_abs] using
        Spaces.sq_le_HkIntegrand_mixed α 4 g z θ i j hi hij)
    (fun z hz => aesm_slice_of_Qd_or_zero (fun z θ => |Spaces.mixed b a f z θ| * Wm α z θ) hAcont
      (fun θ => by rw [Wm, Spaces.Wt, w_zero, zero_mul, mul_zero]) hz)
    (fun z hz => aesm_slice_of_Qd_or_zero (fun z θ => |Spaces.mixed j i g z θ| * Wm α z θ) hBcont
      (fun θ => by rw [Wm, Spaces.Wt, w_zero, zero_mul, mul_zero]) hz)
    (aesm_prod_three (Spaces.mixed (j - b) (i - a + 1) g) (Spaces.mixed b a f)
      (Spaces.mixed j i g)
      (Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg (i - a + 1)) (j - b))
      (Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmf a) b)
      (Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg i) j)
      (continuousOn_Wm_Qd α) (continuousOn_Wm_Qd α))
  exact ⟨hint, hbd⟩


/-! ## The Leibniz expansion of the pairing and of `T1Hard` -/

/-- The Leibniz expansion of `H4PairInt α (f · D_θ g) g` along the summands `xD`, `yM`. -/
theorem H4PairInt_expand (α : ℝ) (f g : ℝ → ℝ → ℝ) (hsmf : Spaces.SmoothNbhd f)
    (hsmg : Spaces.SmoothNbhd g) {z : ℝ} (hz : z ∈ Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    H4PairInt α (fun z θ => f z θ * Spaces.Dth g z θ) g z θ
      = (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), xD f g i b z θ)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j ≤ 4 then
              ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                yM α f g i j a b z θ
             else 0) := by
  have hfI : Spaces.SmoothInt f := SmoothInt_of_SmoothNbhd hsmf
  have hDgI : Spaces.SmoothInt (Spaces.Dth g) :=
    SmoothInt_of_SmoothNbhd (Spaces.SmoothNbhd.Dth hsmg)
  rw [H4PairInt]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hDz : Spaces.DzIter i (fun z θ => f z θ * Spaces.Dth g z θ) z θ
        = ∑ b ∈ Finset.range (i + 1),
            (i.choose b : ℝ) * (Spaces.DzIter b f z θ * Spaces.mixed (i - b) 1 g z θ) := by
      rw [Spaces.DzIter_mul i f (Spaces.Dth g) hz (hfI.2 θ hθ) (hDgI.2 θ hθ)]
      exact Finset.sum_congr rfl fun b _ => by rw [DzIter_Dth]
    rw [hDz, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by simp only [xD]; ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [if_pos hc, if_pos hc]
      have hM : Spaces.mixed j i (fun z θ => f z θ * Spaces.Dth g z θ) z θ
          = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              ((i.choose a : ℝ) * (j.choose b : ℝ)) *
                (Spaces.mixed b a f z θ * Spaces.mixed (j - b) (i - a + 1) g z θ) := by
        rw [Spaces.mixed_mul_eq j i f (Spaces.Dth g) hfI hDgI z hz θ hθ]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
          rw [mixed_Dth]
      rw [hM, Finset.sum_mul, Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => by
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => by simp only [yM]; ring
    · rw [if_neg hc, if_neg hc]

/-- The five hard summands of `T1Hard`, written with `xD` and `yM`. -/
theorem T1Hard_expand (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (hsmg : Spaces.SmoothNbhd g)
    {z : ℝ} (hz : z ∈ Spaces.Iz) {θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    T1Hard α f g z θ
      = xD f g 4 0 z θ
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
            (if 1 ≤ i ∧ i + j = 4 then yM α f g i j 0 0 z θ else 0) := by
  have hs : 0 ≤ Real.sin (2 * θ) := Spaces.Slots.sin_two_nonneg_Iθ (θ := θ) hθ
  have hwhz : (Whz z θ) ^ 2 = (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.eta) :=
    Whz_sq z θ hs
  have hwm : (Wm α z θ) ^ 2 = (Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Spaces.gam α) :=
    Wm_sq α hα z θ hs
  have hy : (z, θ) ∈ Spaces.nbhU := Spaces.mem_nbhU hz hθ
  -- `D_θ(D_z^4 g) = mixed 4 1 g`
  have h4 : Spaces.Dth (Spaces.DzIter 4 g) z θ = Spaces.mixed 4 1 g z θ := by
    have h := Spaces.DthIter_DzIter_comm_eqOn hsmg 4 1 hy
    simpa only [Function.uncurry, Spaces.DthIter, Spaces.mixed] using h
  -- `D_θ(mixed j i g) = mixed j (i+1) g`
  have hj : ∀ i j : ℕ, Spaces.Dth (Spaces.mixed j i g) z θ = Spaces.mixed j (i + 1) g z θ := by
    intro i j
    have h := Spaces.DthIter_DzIter_comm_eqOn (Spaces.SmoothNbhd.DthIter hsmg i) j 1 hy
    simpa only [Function.uncurry, Spaces.DthIter, Spaces.mixed] using h
  have hsum : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j = 4 then yM α f g i j 0 0 z θ else 0))
      = yM α f g 1 3 0 0 z θ + yM α f g 2 2 0 0 z θ + yM α f g 3 1 0 0 z θ
        + yM α f g 4 0 0 0 z θ := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
    try ring
  rw [T1Hard, h4, hj 1 3, hj 2 2, hj 3 1, hj 4 0, hsum, xD]
  simp only [Whz_sq z θ hs, yM, Wm_sq α hα z θ hs, Nat.choose_zero_right,
    Nat.cast_one, Nat.sub_zero, one_mul, mul_one]
  simp only [Spaces.mixed, Spaces.DzIter_zero, Spaces.DthIter_zero]
  ring


/-- The pointwise majorisation of `T1Easy` by `EasyMajor`. -/
theorem T1Easy_le_major (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (hsmf : Spaces.SmoothNbhd f)
    (hsmg : Spaces.SmoothNbhd g) :
    ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ, |T1Easy α f g z θ| ≤ EasyMajor α f g z θ := by
  intro z hz θ hθ
  have hH := H4PairInt_expand α f g hsmf hsmg hz hθ
  have hT := T1Hard_expand α hα f g hsmg hz hθ
  -- the `D_z`-part: remove the single hard summand `xD 4 0`
  have hD1 : (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), xD f g i b z θ)
      - xD f g 4 0 z θ
      = ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
          (if i = 4 ∧ b = 0 then 0 else xD f g i b z θ) := by
    have hsplit : (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), xD f g i b z θ)
        = (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
              (if i = 4 ∧ b = 0 then xD f g i b z θ else 0))
          + ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
              (if i = 4 ∧ b = 0 then 0 else xD f g i b z θ) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by split_ifs <;> ring
    have hsingle : (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
          (if i = 4 ∧ b = 0 then xD f g i b z θ else 0)) = xD f g 4 0 z θ := by
      rw [Finset.sum_eq_single 4]
      · rw [Finset.sum_eq_single 0]
        · simp
        · intro b _ hb0
          rw [if_neg (by rintro ⟨_, h2⟩; exact hb0 h2)]
        · intro h
          exact absurd (Finset.mem_range.mpr (by omega)) h
      · intro i _ hi4
        exact Finset.sum_eq_zero fun b _ => by
          rw [if_neg (by rintro ⟨h1, _⟩; exact hi4 h1)]
      · intro h
        exact absurd (Finset.mem_range.mpr (by norm_num : 4 < 5)) h
    rw [hsplit, hsingle]
    ring
  -- the mixed part: remove the four hard summands `yM i j 0 0` with `i + j = 4`
  have hD2 : (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        (if 1 ≤ i ∧ i + j ≤ 4 then
          ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), yM α f g i j a b z θ
         else 0))
      - (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j = 4 then yM α f g i j 0 0 z θ else 0))
      = ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
          (if 1 ≤ i ∧ i + j ≤ 4 then
            ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else yM α f g i j a b z θ)
           else 0) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [if_pos hc, if_pos hc]
      by_cases hd : 1 ≤ i ∧ i + j = 4
      · rw [if_pos hd]
        have hrm : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              yM α f g i j a b z θ) - yM α f g i j 0 0 z θ
            = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                (if a = 0 ∧ b = 0 then 0 else yM α f g i j a b z θ) := by
          have hsplit : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                yM α f g i j a b z θ)
              = (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                    (if a = 0 ∧ b = 0 then yM α f g i j a b z θ else 0))
                + ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                    (if a = 0 ∧ b = 0 then 0 else yM α f g i j a b z θ) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun a _ => ?_
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun b _ => by split_ifs <;> ring
          have hsingle : (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
                (if a = 0 ∧ b = 0 then yM α f g i j a b z θ else 0))
              = yM α f g i j 0 0 z θ := by
            rw [Finset.sum_eq_single 0]
            · rw [Finset.sum_eq_single 0]
              · simp
              · intro b _ hb0
                rw [if_neg (by rintro ⟨_, h2⟩; exact hb0 h2)]
              · intro h
                exact absurd (Finset.mem_range.mpr (by omega)) h
            · intro a _ ha0
              exact Finset.sum_eq_zero fun b _ => by
                rw [if_neg (by rintro ⟨h1, _⟩; exact ha0 h1)]
            · intro h
              exact absurd (Finset.mem_range.mpr (by omega)) h
          rw [hsplit, hsingle]
          ring
        rw [hrm]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        by_cases hab : a = 0 ∧ b = 0
        · rw [if_pos hab, if_pos (by tauto)]
        · rw [if_neg hab, if_neg (by rintro ⟨h1, h2, _⟩; exact hab ⟨h1, h2⟩)]
      · rw [if_neg hd, sub_zero]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [if_neg (by rintro ⟨_, _, h4⟩; exact hd ⟨hc.1, h4⟩)]
    · rw [if_neg hc, if_neg (by rintro ⟨h1, h2⟩; exact hc ⟨h1, by omega⟩), sub_zero, if_neg hc]
  have key : T1Easy α f g z θ
      = ((∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), xD f g i b z θ) - xD f g 4 0 z θ)
        + ((∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
              (if 1 ≤ i ∧ i + j ≤ 4 then
                ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), yM α f g i j a b z θ
               else 0))
            - (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
                (if 1 ≤ i ∧ i + j = 4 then yM α f g i j 0 0 z θ else 0))) := by
    rw [T1Easy, hH, hT]
    ring
  rw [key, hD1, hD2]
  refine le_trans (abs_add_le _ _) ?_
  rw [EasyMajor]
  refine add_le_add ?_ ?_
  · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    exact Finset.sum_le_sum fun b _ => by
      by_cases hb : i = 4 ∧ b = 0
      · rw [if_pos hb, if_pos hb, abs_zero]
      · rw [if_neg hb, if_neg hb]
  · refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine Finset.sum_le_sum fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ 4
    · rw [if_pos hc, if_pos hc]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun a _ => ?_
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      exact Finset.sum_le_sum fun b _ => by
        by_cases hb : a = 0 ∧ b = 0 ∧ i + j = 4
        · rw [if_pos hb, if_pos hb, abs_zero]
        · rw [if_neg hb, if_neg hb]
    · rw [if_neg hc, if_neg hc, abs_zero]

/-! ## The pointwise majorisation of the individual summands -/

/-- `|xD|` is bounded by the binomial coefficient times its factored form. -/
theorem abs_xD_le (α : ℝ) (hα : 0 < α) (f g : ℝ → ℝ → ℝ) (i b : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Spaces.Iθ) :
    |xD f g i b z θ| ≤ (i.choose b : ℝ) * (|Spaces.DzIter b f z θ| *
      (|Spaces.mixed (i - b) 1 g z θ| * Wm α z θ) * (|Spaces.DzIter i g z θ| * Whz z θ)) := by
  have hch : 0 ≤ (i.choose b : ℝ) := by positivity
  have hW : (Whz z θ) ^ 2 ≤ Wm α z θ * Whz z θ := Whz_sq_le_Wm_mul α hα hθ
  have hXYZ : 0 ≤ |Spaces.DzIter b f z θ| * |Spaces.mixed (i - b) 1 g z θ|
      * |Spaces.DzIter i g z θ| := by positivity
  simp only [xD, abs_mul, abs_sq, sq_abs, abs_of_nonneg hch]
  calc (i.choose b : ℝ) * (|Spaces.DzIter b f z θ| * |Spaces.mixed (i - b) 1 g z θ|
        * |Spaces.DzIter i g z θ| * Whz z θ ^ 2)
      = (i.choose b : ℝ) * ((|Spaces.DzIter b f z θ| * |Spaces.mixed (i - b) 1 g z θ|
          * |Spaces.DzIter i g z θ|) * Whz z θ ^ 2) := by ring
    _ ≤ (i.choose b : ℝ) * ((|Spaces.DzIter b f z θ| * |Spaces.mixed (i - b) 1 g z θ|
          * |Spaces.DzIter i g z θ|) * (Wm α z θ * Whz z θ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hW hXYZ) hch
    _ = (i.choose b : ℝ) * (|Spaces.DzIter b f z θ| * (|Spaces.mixed (i - b) 1 g z θ| * Wm α z θ)
          * (|Spaces.DzIter i g z θ| * Whz z θ)) := by ring

/-- `|yM|` is bounded by the product of the binomial coefficients times its factored form. -/
theorem abs_yM_le (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Spaces.Iθ) :
    |yM α f g i j a b z θ| ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) *
      (|Spaces.mixed b a f z θ| * (|Spaces.mixed (j - b) (i - a + 1) g z θ| * Wm α z θ)
        * (|Spaces.mixed j i g z θ| * Wm α z θ)) := by
  have hch : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
  simp only [yM, abs_mul, abs_sq, sq_abs, abs_of_nonneg hch]
  exact le_of_eq (by ring)

/-! ## The exceptional Leibniz summand `D_z³f · D_θ²g · D_z³D_θg · Wm²`

The single summand of `EasyMajor` in which the `f`-factor carries three `D_z`-derivatives
is estimated by the two `infinity_separated` trade-offs of the paper: the angular supremum
of `D_z³f·w` (the hypothesis `K3`) for the `f`-factor, and the *radial* Hardy inequality
for the `θ`-slice of `D_θ²g` — whose `D_z`-derivative is `mixed 1 2 g`, a single `ℋ⁴`-slot —
for the `g`-factor. -/

/-- The angular slice of a smooth function is bounded, so that `supAbsTh` is the honest
supremum of the slice. -/
theorem bddAbove_slice_dzIter (u : ℝ → ℝ → ℝ) (hsm : Spaces.SmoothNbhd u) (i : ℕ) {z : ℝ}
    (hz : z ∈ Spaces.Iz) : BddAbove {y : ℝ | ∃ θ ∈ Spaces.Iθ, y = |Spaces.DzIter i u z θ|} := by
  have hcont : ContinuousOn (fun θ : ℝ => |Spaces.DzIter i u z θ|) Spaces.Iθ :=
    (continuousOn_slice_dzIter u hsm i hz).abs
  have himg : (fun θ : ℝ => |Spaces.DzIter i u z θ|) '' Spaces.Iθ
      = {y : ℝ | ∃ θ ∈ Spaces.Iθ, y = |Spaces.DzIter i u z θ|} := by
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq]
    exact exists_congr fun θ => and_congr_right fun _ => eq_comm
  rw [← himg]
  exact isCompact_Icc.bddAbove_image hcont

/-- The `f`-factor of the exceptional summand is dominated by the squared angular
supremum of `D_z³f·w`. -/
theorem exc_fdom (f : ℝ → ℝ → ℝ) (hsmf : Spaces.SmoothNbhd f) :
    ∀ z ∈ Spaces.Iz, ∀ θ ∈ Spaces.Iθ,
      (Spaces.DzIter 3 f z θ) ^ 2 * (Spaces.w z) ^ 2
        ≤ (supAbsTh (Spaces.DzIter 3 f) z * Spaces.w z) ^ 2 := by
  intro z hz θ hθ
  have hb := bddAbove_slice_dzIter f hsmf 3 hz
  have h1 : |Spaces.DzIter 3 f z θ| ≤ supAbsTh (Spaces.DzIter 3 f) z :=
    abs_le_supAbsTh hθ hb
  have h2 : 0 ≤ Spaces.w z := by
    rw [Spaces.w]
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  have h3 : |Spaces.DzIter 3 f z θ| * Spaces.w z
      ≤ supAbsTh (Spaces.DzIter 3 f) z * Spaces.w z :=
    mul_le_mul_of_nonneg_right h1 h2
  have h4 : 0 ≤ |Spaces.DzIter 3 f z θ| * Spaces.w z := mul_nonneg (abs_nonneg _) h2
  have h5 : (|Spaces.DzIter 3 f z θ| * Spaces.w z) ^ 2
      ≤ (supAbsTh (Spaces.DzIter 3 f) z * Spaces.w z) ^ 2 := by
    rw [pow_two, pow_two]
    exact mul_le_mul h3 h3 h4 (mul_nonneg (supAbsTh_nonneg hb) h2)
  calc (Spaces.DzIter 3 f z θ) ^ 2 * (Spaces.w z) ^ 2
      = (|Spaces.DzIter 3 f z θ| * Spaces.w z) ^ 2 := by rw [mul_pow, sq_abs]
    _ ≤ _ := h5

/-- The radial Hardy inequality applied to the `θ`-slice of `mixed 0 2 g = D_θ²g`: for a.e.
angle and every `z ≥ 0`, `(D_θ²g)²·sin(2θ)^{-γ}` is dominated by the weighted `L²`-norm
along the half-line of `mixed 1 2 g = D_z D_θ²g`, i.e. of the `ℋ⁴`-slot `(mixed 1 2 g)·Wt`. -/
theorem exc_gdom (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (g : ℝ → ℝ → ℝ)
    (hsmg : Spaces.SmoothNbhd g) (hdecg : Spaces.DecayMixed 4 g)
    (hint : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (Spaces.mixed 1 2 g p.1 p.2 * Spaces.Wt α p.1 p.2) ^ 2)
      ((MeasureTheory.volume.restrict Spaces.Iz).prod (MeasureTheory.volume.restrict Spaces.Iθ))) :
    ∀ᵐ θ ∂(MeasureTheory.volume.restrict Spaces.Iθ), ∀ z ∈ Spaces.Iz,
      (Spaces.mixed 0 2 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))
        ≤ ∫ z' in Spaces.Iz, (Spaces.mixed 1 2 g z' θ * Spaces.Wt α z' θ) ^ 2 := by
  have hsliceae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Spaces.Iθ),
      MeasureTheory.Integrable
        (fun z => (Spaces.mixed 1 2 g z θ * Spaces.Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Spaces.Iz) := hint.prod_left_ae
  filter_upwards [hsliceae, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hintθ hθ
  intro z hz
  by_cases hzero : Real.sin (2 * θ) = 0
  · have hΦ : Spaces.mixed 0 2 g z θ = 0 := by
      show Real.sin (2 * θ) * Spaces.pth (Spaces.DthIter 1 g) z θ = 0
      rw [hzero, zero_mul]
    rw [hΦ]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_mul]
    exact integral_nonneg fun z' => sq_nonneg _
  · have hsinpos : 0 < Real.sin (2 * θ) :=
      lt_of_le_of_ne (Work.Spaces.bt_sin_nonneg hθ) (Ne.symm hzero)
    set c : ℝ := (Real.sin (2 * θ)) ^ (-(Spaces.gam α)) with hcdef
    have hcpos : 0 < c := Real.rpow_pos_of_pos hsinpos _
    have hpoint : ∀ s : ℝ, (Spaces.mixed 1 2 g s θ * Spaces.Wt α s θ) ^ 2
        = c * ((Spaces.Dz (Spaces.mixed 0 2 g) s θ) ^ 2 * (Spaces.w s) ^ 2) := by
      intro s
      rw [hcdef]
      have h := Work.Spaces.bt_Wt_sq α s θ hα hθ
      show (Spaces.Dz (Spaces.mixed 0 2 g) s θ * Spaces.Wt α s θ) ^ 2 = _
      rw [mul_pow, h]
      ring
    have hint' : MeasureTheory.Integrable
        (fun z' => (Spaces.Dz (Spaces.mixed 0 2 g) z' θ) ^ 2 * (Spaces.w z') ^ 2)
        (MeasureTheory.volume.restrict Spaces.Iz) := by
      have h1 : MeasureTheory.Integrable
          (fun z' => c⁻¹ * (Spaces.mixed 1 2 g z' θ * Spaces.Wt α z' θ) ^ 2)
          (MeasureTheory.volume.restrict Spaces.Iz) := hintθ.const_mul _
      refine h1.congr ?_
      filter_upwards with z'
      rw [hpoint z']
      field_simp
    have hdecθ : Filter.Tendsto (fun z => Spaces.mixed 0 2 g z θ) Filter.atTop (nhds 0) :=
      hdecg 2 0 (by norm_num) θ hθ
    have hH := Work.Spaces.HardyZ (Spaces.mixed 0 2 g) θ
      (Spaces.SmoothNbhd.DthIter hsmg 2) hθ hdecθ hint'
    have hRHS : (∫ z' in Spaces.Iz, (Spaces.mixed 1 2 g z' θ * Spaces.Wt α z' θ) ^ 2)
        = c * ∫ s in Spaces.Iz,
            (Spaces.Dz (Spaces.mixed 0 2 g) s θ) ^ 2 * (Spaces.w s) ^ 2 := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards with s
      exact hpoint s
    rw [hRHS]
    calc (Spaces.mixed 0 2 g z θ) ^ 2 * c = c * (Spaces.mixed 0 2 g z θ) ^ 2 := by ring
      _ ≤ c * ∫ s in Spaces.Iz,
            (Spaces.Dz (Spaces.mixed 0 2 g) s θ) ^ 2 * (Spaces.w s) ^ 2 :=
          mul_le_mul_of_nonneg_left (hH z hz) hcpos.le

/-- Cauchy–Schwarz (Bunyakovsky) for the product measure `pm`, in the form used by the
exceptional summand. -/
theorem cs_pm_of_nonneg {X Y : ℝ × ℝ → ℝ} (hX0 : 0 ≤ᵐ[pm] X) (hY0 : 0 ≤ᵐ[pm] Y)
    (hX : MemLp X 2 pm) (hY : MemLp Y 2 pm) :
    ∫ p, X p * Y p ∂pm
      ≤ Real.sqrt (∫ p, X p ^ 2 ∂pm) * Real.sqrt (∫ p, Y p ^ 2 ∂pm) := by
  have hX2 : MemLp X (ENNReal.ofReal (2 : ℝ)) pm := by
    rwa [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
  have hY2 : MemLp Y (ENNReal.ofReal (2 : ℝ)) pm := by
    rwa [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := pm) (p := 2) (q := 2)
    (by norm_num [Real.holderConjugate_iff]) hX0 hY0 hX2 hY2
  have hXr : ∫ p, X p ^ (2 : ℝ) ∂pm = ∫ p, X p ^ 2 ∂pm :=
    integral_congr_ae (Eventually.of_forall fun p => Real.rpow_natCast (X p) 2)
  have hYr : ∫ p, Y p ^ (2 : ℝ) ∂pm = ∫ p, Y p ^ 2 ∂pm :=
    integral_congr_ae (Eventually.of_forall fun p => Real.rpow_natCast (Y p) 2)
  rw [hXr, hYr, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h
  exact h

/-- The absolute value of an `L²`-function of the plane is again in `L²`. -/
theorem memLp_abs_pm {X : ℝ × ℝ → ℝ} (h : MemLp X 2 pm) : MemLp (fun p => |X p|) 2 pm := by
  have haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => |X p|) pm :=
    h.aestronglyMeasurable.norm.congr (Eventually.of_forall fun p => Real.norm_eq_abs (X p))
  refine (memLp_two_iff_integrable_sq haesm).mpr ?_
  have hint : Integrable (fun p : ℝ × ℝ => X p ^ 2) pm :=
    (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mp h
  exact hint.congr (Eventually.of_forall fun p => (sq_abs (X p)).symm)

/-- The exceptional summand of the Leibniz expansion is bounded by `√K3·|g|²_{ℋ⁴}`. -/
theorem T1ExcBoundAux : ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (K3 : ℝ),
    0 < α → α ≤ 1 → Spaces.SmoothNbhd f → Spaces.SmoothNbhd g →
    Spaces.DecayAll 4 f → Spaces.DecayAll 4 g →
    Spaces.HkMem α 4 f → Spaces.HkMem α 4 g →
    MeasureTheory.IntegrableOn
      (fun z => (supAbsTh (Spaces.DzIter 3 f) z * Spaces.w z) ^ 2) Spaces.Iz →
    (∫ z in Spaces.Iz, (supAbsTh (Spaces.DzIter 3 f) z * Spaces.w z) ^ 2 ≤ K3) →
    0 ≤ K3 →
    (MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        |Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2 * Spaces.mixed 3 1 g p.1 p.2
          * (Wm α p.1 p.2) ^ 2|) pm ∧
      ∫ p, |Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
          * Spaces.mixed 3 1 g p.1 p.2 * (Wm α p.1 p.2) ^ 2| ∂pm
        ≤ Real.sqrt K3 * Spaces.HkSq α 4 g) ∧
    (MeasureTheory.IntegrableOn (fun z => ∫ θ in Spaces.Iθ,
        |Spaces.DzIter 3 f z θ * Spaces.mixed 0 2 g z θ * Spaces.mixed 3 1 g z θ
          * (Wm α z θ) ^ 2|) Spaces.Iz ∧
      ∫ z in Spaces.Iz, (∫ θ in Spaces.Iθ,
        |Spaces.DzIter 3 f z θ * Spaces.mixed 0 2 g z θ * Spaces.mixed 3 1 g z θ
          * (Wm α z θ) ^ 2|)
        ≤ Real.sqrt K3 * Spaces.HkSq α 4 g) := by
  intro α f g K3 hα hα1 hsmf hsmg hdecf hdecg hmemf hmemg hGint hGle hK3
  have hpm : pm = (MeasureTheory.volume.restrict Spaces.Iz).prod
      (MeasureTheory.volume.restrict Spaces.Iθ) := rfl
  obtain ⟨hY_int, hY_val⟩ :=
    Work.Spaces.bt_prod_integrable α g hsmg hmemg 3 1 (by norm_num) (by norm_num)
  obtain ⟨hV_int, hV_val⟩ :=
    Work.Spaces.bt_prod_integrable α g hsmg hmemg 1 2 (by norm_num) (by norm_num)
  -- the `θ`-dominating function `Gb` of the `g`-factor
  have hGb_int : MeasureTheory.Integrable
      (fun θ => ∫ z' in Spaces.Iz, (Spaces.mixed 1 2 g z' θ * Spaces.Wt α z' θ) ^ 2)
      (MeasureTheory.volume.restrict Spaces.Iθ) := hV_int.integral_prod_right
  have hGb_le : ∫ θ in Spaces.Iθ,
        (∫ z' in Spaces.Iz, (Spaces.mixed 1 2 g z' θ * Spaces.Wt α z' θ) ^ 2)
      ≤ Spaces.HkSq α 4 g := by
    have h1 : ∫ θ in Spaces.Iθ,
          (∫ z' in Spaces.Iz, (Spaces.mixed 1 2 g z' θ * Spaces.Wt α z' θ) ^ 2)
        = ∫ p, (Spaces.mixed 1 2 g p.1 p.2 * Spaces.Wt α p.1 p.2) ^ 2 ∂pm := by
      rw [hpm]
      rw [← MeasureTheory.integral_integral_swap
        (μ := MeasureTheory.volume.restrict Spaces.Iz)
        (ν := MeasureTheory.volume.restrict Spaces.Iθ)
        (f := fun z θ => (Spaces.mixed 1 2 g z θ * Spaces.Wt α z θ) ^ 2) hV_int]
      exact MeasureTheory.integral_integral hV_int
    rw [h1]
    rw [hpm]
    rw [hV_val]
    exact Work.Spaces.L2Sq_mixed_le_HkSq α 4 g hmemg 2 1 (by norm_num) (by norm_num)
  have hYsq_le : ∫ p, (Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2) ^ 2 ∂pm
      ≤ Spaces.HkSq α 4 g := by
    rw [hpm]
    rw [hY_val]
    exact Work.Spaces.L2Sq_mixed_le_HkSq α 4 g hmemg 1 3 (by norm_num) (by norm_num)
  -- the `g`-domination
  have hgdom := exc_gdom α hα hα1 g hsmg hdecg.2 hV_int
  -- the two Cauchy–Schwarz factors
  have hXaesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
        * Spaces.Wt α p.1 p.2) pm :=
    aesm_of_Qd ((((Spaces.SmoothNbhd.DzIter hsmf 3).continuousOn.mono Qd_subset_nbhU).mul
      ((Spaces.SmoothNbhd.DthIter hsmg 2).continuousOn.mono Qd_subset_nbhU)).mul
        (continuousOn_Wt_Qd α))
  have hYaesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2) pm :=
    aesm_of_Qd ((((Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg 1) 3).continuousOn.mono
      Qd_subset_nbhU).mul (continuousOn_Wt_Qd α)))
  -- the squared `θ`-weight identity
  have hXpoint : ∀ (z θ : ℝ), θ ∈ Spaces.Iθ →
      (Spaces.DzIter 3 f z θ * Spaces.mixed 0 2 g z θ * Spaces.Wt α z θ) ^ 2
        = (Spaces.DzIter 3 f z θ) ^ 2 * (Spaces.w z) ^ 2
          * ((Spaces.mixed 0 2 g z θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Spaces.gam α))) := by
    intro z θ hθ
    rw [mul_pow, mul_pow, Work.Spaces.bt_Wt_sq α z θ hα hθ]
    ring
  -- the `θ`-integral bound for each `z ∈ Iz`
  have hXsq_theta : ∀ z ∈ Spaces.Iz,
      ∫ θ in Spaces.Iθ,
          (Spaces.DzIter 3 f z θ * Spaces.mixed 0 2 g z θ * Spaces.Wt α z θ) ^ 2
        ≤ (supAbsTh (Spaces.DzIter 3 f) z * Spaces.w z) ^ 2
          * ∫ θ in Spaces.Iθ,
              (∫ z' in Spaces.Iz, (Spaces.mixed 1 2 g z' θ * Spaces.Wt α z' θ) ^ 2) := by
    intro z hz
    have hmono : ∫ θ in Spaces.Iθ,
          (Spaces.DzIter 3 f z θ * Spaces.mixed 0 2 g z θ * Spaces.Wt α z θ) ^ 2
        ≤ ∫ θ in Spaces.Iθ, (supAbsTh (Spaces.DzIter 3 f) z * Spaces.w z) ^ 2
            * (∫ z' in Spaces.Iz, (Spaces.mixed 1 2 g z' θ * Spaces.Wt α z' θ) ^ 2) := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _)
        (hGb_int.const_mul _) ?_
      filter_upwards [hgdom, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hgd hθ
      rw [hXpoint z θ hθ]
      refine mul_le_mul (exc_fdom f hsmf z hz θ hθ) (hgd z hz) ?_ (sq_nonneg _)
      exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.bt_sin_nonneg hθ) _)
    rw [integral_const_mul] at hmono
    exact hmono
  -- the slice integrability and the Fubini identity for `X²`
  have hXsq_slice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz),
      MeasureTheory.Integrable
        (fun θ => (Spaces.DzIter 3 f z θ * Spaces.mixed 0 2 g z θ * Spaces.Wt α z θ) ^ 2)
        (MeasureTheory.volume.restrict Spaces.Iθ) := by
    filter_upwards [hXaesm.prodMk_left, MeasureTheory.ae_restrict_mem measurableSet_Ici]
      with z hzmeas hz
    refine MeasureTheory.Integrable.mono'
      (hGb_int.const_mul ((supAbsTh (Spaces.DzIter 3 f) z * Spaces.w z) ^ 2))
      (hzmeas.pow 2) ?_
    filter_upwards [hgdom, MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hgd hθ
    rw [Real.norm_of_nonneg (sq_nonneg _), hXpoint z θ hθ]
    refine mul_le_mul (exc_fdom f hsmf z hz θ hθ) (hgd z hz) ?_ (sq_nonneg _)
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Work.Spaces.bt_sin_nonneg hθ) _)
  have hXsq_outer : MeasureTheory.Integrable
      (fun z => ∫ θ in Spaces.Iθ,
        (Spaces.DzIter 3 f z θ * Spaces.mixed 0 2 g z θ * Spaces.Wt α z θ) ^ 2)
      (MeasureTheory.volume.restrict Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono'
      (hGint.mul_const (∫ θ in Spaces.Iθ,
        (∫ z' in Spaces.Iz, (Spaces.mixed 1 2 g z' θ * Spaces.Wt α z' θ) ^ 2)))
      ((hXaesm.pow 2).integral_prod_right') ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
    exact hXsq_theta z hz
  obtain ⟨hX_int, hX_val⟩ := Work.Spaces.integrable_prod_of_iterated
    (G := fun z θ => (Spaces.DzIter 3 f z θ * Spaces.mixed 0 2 g z θ * Spaces.Wt α z θ) ^ 2)
    (fun z θ => sq_nonneg _) (hXaesm.pow 2) hXsq_slice hXsq_outer
  have hX_le : ∫ p, (Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
        * Spaces.Wt α p.1 p.2) ^ 2 ∂pm ≤ K3 * Spaces.HkSq α 4 g := by
    rw [hpm]
    rw [hX_val]
    calc ∫ z in Spaces.Iz, (∫ θ in Spaces.Iθ,
            (Spaces.DzIter 3 f z θ * Spaces.mixed 0 2 g z θ * Spaces.Wt α z θ) ^ 2)
        ≤ ∫ z in Spaces.Iz, (supAbsTh (Spaces.DzIter 3 f) z * Spaces.w z) ^ 2
            * (∫ θ in Spaces.Iθ,
                (∫ z' in Spaces.Iz, (Spaces.mixed 1 2 g z' θ * Spaces.Wt α z' θ) ^ 2)) := by
          refine integral_mono_of_nonneg
            (Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _)
            (hGint.mul_const _) ?_
          exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici
            (fun z hz => hXsq_theta z hz)
      _ = (∫ z in Spaces.Iz, (supAbsTh (Spaces.DzIter 3 f) z * Spaces.w z) ^ 2)
            * (∫ θ in Spaces.Iθ,
                (∫ z' in Spaces.Iz, (Spaces.mixed 1 2 g z' θ * Spaces.Wt α z' θ) ^ 2)) :=
          integral_mul_const _ _
      _ ≤ K3 * Spaces.HkSq α 4 g :=
          mul_le_mul hGle hGb_le (integral_nonneg fun θ => integral_nonneg fun z' => sq_nonneg _)
            hK3
  -- Cauchy–Schwarz
  have hX_memLp : MemLp (fun p : ℝ × ℝ => Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
      * Spaces.Wt α p.1 p.2) 2 pm := (memLp_two_iff_integrable_sq hXaesm).mpr hX_int
  have hY_memLp : MemLp (fun p : ℝ × ℝ => Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2) 2 pm :=
    (memLp_two_iff_integrable_sq hYaesm).mpr (by rw [hpm]; exact hY_int)
  have hCS := cs_pm_of_nonneg
    (X := fun p : ℝ × ℝ => |Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
      * Spaces.Wt α p.1 p.2|)
    (Y := fun p : ℝ × ℝ => |Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2|)
    (Eventually.of_forall fun p => abs_nonneg _) (Eventually.of_forall fun p => abs_nonneg _)
    (memLp_abs_pm hX_memLp) (memLp_abs_pm hY_memLp)
  have hXY_le : ∫ p, |Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
      * Spaces.mixed 3 1 g p.1 p.2 * (Wm α p.1 p.2) ^ 2| ∂pm
      ≤ Real.sqrt K3 * Spaces.HkSq α 4 g := by
    have h1 : ∫ p, |Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
        * Spaces.mixed 3 1 g p.1 p.2 * (Wm α p.1 p.2) ^ 2| ∂pm
        = ∫ p, |Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
            * Spaces.Wt α p.1 p.2| * |Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2| ∂pm := by
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      show |Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
          * Spaces.mixed 3 1 g p.1 p.2 * (Wm α p.1 p.2) ^ 2|
        = |Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2 * Spaces.Wt α p.1 p.2|
          * |Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2|
      have h2 : Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
          * Spaces.mixed 3 1 g p.1 p.2 * (Wm α p.1 p.2) ^ 2
          = (Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2 * Spaces.Wt α p.1 p.2)
            * (Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2) := by
        simp only [Wm]
        ring
      rw [h2, abs_mul]
    rw [h1]
    have h2 : ∫ p, |Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
          * Spaces.Wt α p.1 p.2| ^ 2 ∂pm
        = ∫ p, (Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
          * Spaces.Wt α p.1 p.2) ^ 2 ∂pm :=
      integral_congr_ae (Eventually.of_forall fun p => sq_abs _)
    have h3 : ∫ p, |Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2| ^ 2 ∂pm
        = ∫ p, (Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2) ^ 2 ∂pm :=
      integral_congr_ae (Eventually.of_forall fun p => sq_abs _)
    rw [h2, h3] at hCS
    refine le_trans hCS ?_
    calc Real.sqrt (∫ p, (Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
            * Spaces.Wt α p.1 p.2) ^ 2 ∂pm) * Real.sqrt (∫ p, (Spaces.mixed 3 1 g p.1 p.2
            * Spaces.Wt α p.1 p.2) ^ 2 ∂pm)
        ≤ Real.sqrt (K3 * Spaces.HkSq α 4 g) * Real.sqrt (Spaces.HkSq α 4 g) :=
          mul_le_mul (Real.sqrt_le_sqrt hX_le) (Real.sqrt_le_sqrt hYsq_le)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt K3 * Spaces.HkSq α 4 g := by
          rw [Real.sqrt_mul hK3, mul_assoc, Real.mul_self_sqrt (Spaces.HkSq_nonneg α 4 g)]
  -- the integrability of the exceptional integrand on the plane
  have hXYaesm : AEStronglyMeasurable
      (fun p : ℝ × ℝ => |Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
        * Spaces.mixed 3 1 g p.1 p.2 * (Wm α p.1 p.2) ^ 2|) pm :=
    aesm_of_Qd ((((((Spaces.SmoothNbhd.DzIter hsmf 3).continuousOn.mono Qd_subset_nbhU).mul
      ((Spaces.SmoothNbhd.DthIter hsmg 2).continuousOn.mono Qd_subset_nbhU)).mul
      ((Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg 1) 3).continuousOn.mono
        Qd_subset_nbhU)).mul ((continuousOn_Wm_Qd α).pow 2)).abs)
  have hXY_int : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => |Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
        * Spaces.mixed 3 1 g p.1 p.2 * (Wm α p.1 p.2) ^ 2|) pm := by
    refine MeasureTheory.Integrable.mono'
      (((hX_int.add hY_int).const_mul (1 / 2))) hXYaesm ?_
    filter_upwards with p
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    have hval : |Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
        * Spaces.mixed 3 1 g p.1 p.2 * (Wm α p.1 p.2) ^ 2|
        = |(Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2 * Spaces.Wt α p.1 p.2)
            * (Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2)| := by
      have h2 : Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
          * Spaces.mixed 3 1 g p.1 p.2 * (Wm α p.1 p.2) ^ 2
          = (Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2 * Spaces.Wt α p.1 p.2)
            * (Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2) := by
        simp only [Wm]
        ring
      rw [h2]
    rw [hval, abs_mul]
    have h1 : |Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2 * Spaces.Wt α p.1 p.2|
          * |Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2|
        ≤ (1 / 2) * ((Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
            * Spaces.Wt α p.1 p.2) ^ 2
          + (Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2) ^ 2) := by
      have h2 : (Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
            * Spaces.Wt α p.1 p.2) ^ 2
          = |Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2 * Spaces.Wt α p.1 p.2| ^ 2 :=
        (sq_abs _).symm
      have h3 : (Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2) ^ 2
          = |Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2| ^ 2 := (sq_abs _).symm
      rw [h2, h3]
      linarith [two_mul_le_add_sq
        (|Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2 * Spaces.Wt α p.1 p.2|)
        (|Spaces.mixed 3 1 g p.1 p.2 * Spaces.Wt α p.1 p.2|)]
    exact h1
  have hXY_outer := hXY_int.integral_prod_left
  have hiter : ∫ z in Spaces.Iz, (∫ θ in Spaces.Iθ,
      |Spaces.DzIter 3 f z θ * Spaces.mixed 0 2 g z θ * Spaces.mixed 3 1 g z θ
        * (Wm α z θ) ^ 2|) ≤ Real.sqrt K3 * Spaces.HkSq α 4 g := by
    rw [MeasureTheory.integral_integral hXY_int]
    exact hXY_le
  exact ⟨⟨hXY_int, hXY_le⟩, hXY_outer, hiter⟩

/-! ## The integral of the pointwise majorant `EasyMajor`

Every summand of `EasyMajor` is one of the Leibniz terms of the pairing.  Each of them is
estimated by one of `xDKf_bound`, `xDKg_bound`, `yMKf_bound`, `yMKg_bound` — the terms in
which the `f`-factor has order `≤ 2` — or, in the single exceptional case `(a,b) = (0,3)`,
by `T1ExcBoundAux`.  We bound every summand by the same multiple of the total
`Kf·|g|²_{ℋ⁴} + Kg·|f|_{ℋ⁴}|g|_{ℋ⁴} + √K3·|g|²_{ℋ⁴}`, and then sum the finitely many
of them. -/

/-- The total bound of the right-hand side of `T1EasyBound`. -/
abbrev TTot (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg K3 : ℝ) : ℝ :=
  Kf * Spaces.HkSq α 4 g + Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g
    + Real.sqrt K3 * Spaces.HkSq α 4 g

theorem TTot_nonneg (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg K3 : ℝ)
    (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg) (hK3 : 0 ≤ K3) : 0 ≤ TTot α f g Kf Kg K3 := by
  have h1 : 0 ≤ Kf * Spaces.HkSq α 4 g := mul_nonneg hKf (Spaces.HkSq_nonneg α 4 g)
  have h2 : 0 ≤ Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g :=
    mul_nonneg (mul_nonneg hKg (Spaces.HkNorm_nonneg α 4 f)) (Spaces.HkNorm_nonneg α 4 g)
  have h3 : 0 ≤ Real.sqrt K3 * Spaces.HkSq α 4 g :=
    mul_nonneg (Real.sqrt_nonneg _) (Spaces.HkSq_nonneg α 4 g)
  rw [TTot]
  linarith

theorem le_TTot_Kf (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg K3 : ℝ)
    (hKg : 0 ≤ Kg) (hK3 : 0 ≤ K3) : Kf * Spaces.HkSq α 4 g ≤ TTot α f g Kf Kg K3 := by
  have h2 : 0 ≤ Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g :=
    mul_nonneg (mul_nonneg hKg (Spaces.HkNorm_nonneg α 4 f)) (Spaces.HkNorm_nonneg α 4 g)
  have h3 : 0 ≤ Real.sqrt K3 * Spaces.HkSq α 4 g :=
    mul_nonneg (Real.sqrt_nonneg _) (Spaces.HkSq_nonneg α 4 g)
  rw [TTot]
  linarith

theorem le_TTot_Kg (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg K3 : ℝ)
    (hKf : 0 ≤ Kf) (hK3 : 0 ≤ K3) :
    Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g ≤ TTot α f g Kf Kg K3 := by
  have h1 : 0 ≤ Kf * Spaces.HkSq α 4 g := mul_nonneg hKf (Spaces.HkSq_nonneg α 4 g)
  have h3 : 0 ≤ Real.sqrt K3 * Spaces.HkSq α 4 g :=
    mul_nonneg (Real.sqrt_nonneg _) (Spaces.HkSq_nonneg α 4 g)
  rw [TTot]
  linarith

theorem le_TTot_sqrt (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg K3 : ℝ)
    (hKf : 0 ≤ Kf) (hKg : 0 ≤ Kg) :
    Real.sqrt K3 * Spaces.HkSq α 4 g ≤ TTot α f g Kf Kg K3 := by
  have h1 : 0 ≤ Kf * Spaces.HkSq α 4 g := mul_nonneg hKf (Spaces.HkSq_nonneg α 4 g)
  have h2 : 0 ≤ Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g :=
    mul_nonneg (mul_nonneg hKg (Spaces.HkNorm_nonneg α 4 f)) (Spaces.HkNorm_nonneg α 4 g)
  rw [TTot]
  linarith

/-- The slot form of the `D_z`-summand when the `f`-factor `D_z^b f` has order `≤ 2`
(the two Cauchy–Schwarz slots are the `g`-factors). -/
abbrev xDA (α : ℝ) (f g : ℝ → ℝ → ℝ) (i b : ℕ) (p : ℝ × ℝ) : ℝ :=
  |Spaces.DzIter b f p.1 p.2 * (|Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2)
    * (|Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)|

/-- The slot form of the `D_z`-summand when the `g`-factor `D_z^{i-b}D_θ g` has order `≤ 2`. -/
abbrev xDB (α : ℝ) (f g : ℝ → ℝ → ℝ) (i b : ℕ) (p : ℝ × ℝ) : ℝ :=
  |Spaces.mixed (i - b) 1 g p.1 p.2 * (|Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2)
    * (|Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2)|

/-- The slot form of a mixed summand when the `f`-factor has order `≤ 2`. -/
abbrev yMA (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) (p : ℝ × ℝ) : ℝ :=
  |Spaces.mixed b a f p.1 p.2 * (|Spaces.mixed (j - b) (i - a + 1) g p.1 p.2| * Wm α p.1 p.2)
    * (|Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2)|

/-- The slot form of a mixed summand when the `g`-factor `D_z^{j-b}D_θ^{i-a+1}g` has order
`≤ 2`. -/
abbrev yMB (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) (p : ℝ × ℝ) : ℝ :=
  |Spaces.mixed (j - b) (i - a + 1) g p.1 p.2 * (|Spaces.mixed b a f p.1 p.2| * Wm α p.1 p.2)
    * (|Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2)|

theorem xD_aesm (f g : ℝ → ℝ → ℝ) (hsmf : Spaces.SmoothNbhd f) (hsmg : Spaces.SmoothNbhd g)
    (i b : ℕ) : AEStronglyMeasurable (fun p : ℝ × ℝ => xD f g i b p.1 p.2) pm := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Spaces.DzIter b f p.1 p.2) Qd :=
    ((Spaces.SmoothNbhd.DzIter hsmf b).continuousOn).mono Qd_subset_nbhU
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Spaces.mixed (i - b) 1 g p.1 p.2) Qd :=
    ((Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg 1) (i - b)).continuousOn).mono
      Qd_subset_nbhU
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Spaces.DzIter i g p.1 p.2) Qd :=
    ((Spaces.SmoothNbhd.DzIter hsmg i).continuousOn).mono Qd_subset_nbhU
  refine aesm_of_Qd ?_
  simp only [xD]
  exact continuousOn_const.mul (((h1.mul h2).mul h3).mul (continuousOn_Whz_Qd.pow 2))

theorem yM_aesm (α : ℝ) (f g : ℝ → ℝ → ℝ) (hsmf : Spaces.SmoothNbhd f)
    (hsmg : Spaces.SmoothNbhd g) (i j a b : ℕ) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => yM α f g i j a b p.1 p.2) pm := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Spaces.mixed b a f p.1 p.2) Qd :=
    ((Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmf a) b).continuousOn).mono
      Qd_subset_nbhU
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Spaces.mixed (j - b) (i - a + 1) g p.1 p.2) Qd :=
    ((Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg (i - a + 1)) (j - b)).continuousOn).mono
      Qd_subset_nbhU
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Spaces.mixed j i g p.1 p.2) Qd :=
    ((Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg i) j).continuousOn).mono
      Qd_subset_nbhU
  refine aesm_of_Qd ?_
  simp only [yM]
  exact continuousOn_const.mul (((h1.mul h2).mul h3).mul ((continuousOn_Wm_Qd α).pow 2))

theorem xDA_eq (α : ℝ) (f g : ℝ → ℝ → ℝ) (i b : ℕ) :
    ∀ᵐ p ∂pm, xDA α f g i b p
      = |Spaces.DzIter b f p.1 p.2| * (|Spaces.mixed (i - b) 1 g p.1 p.2| * Wm α p.1 p.2)
        * (|Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2) := by
  filter_upwards [ae_pm_mem] with p hp
  have hθ : p.2 ∈ Spaces.Iθ := hp.2
  simp only [xDA, abs_mul, abs_of_nonneg (Wm_nonneg α hθ), abs_of_nonneg (Whz_nonneg hθ),
    abs_of_nonneg (abs_nonneg _)]

theorem xDB_eq (α : ℝ) (f g : ℝ → ℝ → ℝ) (i b : ℕ) :
    ∀ᵐ p ∂pm, xDB α f g i b p
      = |Spaces.mixed (i - b) 1 g p.1 p.2| * (|Spaces.DzIter b f p.1 p.2| * Whz p.1 p.2)
        * (|Spaces.DzIter i g p.1 p.2| * Whz p.1 p.2) := by
  filter_upwards [ae_pm_mem] with p hp
  have hθ : p.2 ∈ Spaces.Iθ := hp.2
  simp only [xDB, abs_mul, abs_of_nonneg (Whz_nonneg hθ), abs_of_nonneg (abs_nonneg _)]

theorem yMA_eq (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) :
    ∀ᵐ p ∂pm, yMA α f g i j a b p
      = |Spaces.mixed b a f p.1 p.2|
        * (|Spaces.mixed (j - b) (i - a + 1) g p.1 p.2| * Wm α p.1 p.2)
        * (|Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2) := by
  filter_upwards [ae_pm_mem] with p hp
  have hθ : p.2 ∈ Spaces.Iθ := hp.2
  simp only [yMA, abs_mul, abs_of_nonneg (Wm_nonneg α hθ), abs_of_nonneg (abs_nonneg _)]

theorem yMB_eq (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) :
    ∀ᵐ p ∂pm, yMB α f g i j a b p
      = |Spaces.mixed (j - b) (i - a + 1) g p.1 p.2|
        * (|Spaces.mixed b a f p.1 p.2| * Wm α p.1 p.2)
        * (|Spaces.mixed j i g p.1 p.2| * Wm α p.1 p.2) := by
  filter_upwards [ae_pm_mem] with p hp
  have hθ : p.2 ∈ Spaces.Iθ := hp.2
  simp only [yMB, abs_mul, abs_of_nonneg (Wm_nonneg α hθ), abs_of_nonneg (abs_nonneg _)]

/-- The absolute value of an a.e. strongly measurable function of the plane is a.e. strongly
measurable. -/
theorem abs_aesm_pm {F : ℝ × ℝ → ℝ} (h : AEStronglyMeasurable F pm) :
    AEStronglyMeasurable (fun p => |F p|) pm :=
  h.norm.congr (Eventually.of_forall fun p => Real.norm_eq_abs (F p))

theorem choose_le_16 {i b : ℕ} (hi : i ≤ 4) (hb : b ≤ i) : (i.choose b : ℝ) ≤ 16 := by
  have h1 : i.choose b ≤ 2 ^ i := Nat.choose_le_two_pow i b
  have h2 : (2 : ℕ) ^ i ≤ 2 ^ 4 := pow_le_pow_right' (show (1 : ℕ) ≤ 2 by norm_num) hi
  have h3 : i.choose b ≤ 2 ^ 4 := le_trans h1 h2
  have h3' : i.choose b ≤ 16 := by norm_num at h3 ⊢; exact h3
  exact_mod_cast h3'

theorem choose_mul_le_256 {i j a b : ℕ} (hi : i ≤ 4) (hai : a ≤ i) (hj : j ≤ 4) (hbj : b ≤ j) :
    (i.choose a : ℝ) * (j.choose b : ℝ) ≤ 256 := by
  have h1 : (i.choose a : ℝ) ≤ 16 := choose_le_16 hi hai
  have h2 : (j.choose b : ℝ) ≤ 16 := choose_le_16 hj hbj
  have h4 : 0 ≤ (j.choose b : ℝ) := by positivity
  calc (i.choose a : ℝ) * (j.choose b : ℝ) ≤ 16 * 16 :=
        mul_le_mul h1 h2 h4 (by norm_num)
    _ = 256 := by norm_num

/-- `|xD|` in the slot form used when the `g`-factor `D_z^{i-b}D_θ g` has order `≤ 2`. -/
theorem abs_xD_le_alt (f g : ℝ → ℝ → ℝ) (i b : ℕ) {z θ : ℝ} (hθ : θ ∈ Spaces.Iθ) :
    |xD f g i b z θ| ≤ (i.choose b : ℝ) *
      (|Spaces.mixed (i - b) 1 g z θ| * (|Spaces.DzIter b f z θ| * Whz z θ)
        * (|Spaces.DzIter i g z θ| * Whz z θ)) := by
  have hch : 0 ≤ (i.choose b : ℝ) := by positivity
  have h1 : |(Spaces.DzIter b f z θ * Spaces.mixed (i - b) 1 g z θ) * Spaces.DzIter i g z θ
      * (Whz z θ) ^ 2| = |Spaces.DzIter b f z θ| * (|Spaces.mixed (i - b) 1 g z θ|
        * |Spaces.DzIter i g z θ|) * (Whz z θ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (Whz z θ)), abs_mul, abs_mul]
    ring
  rw [xD, abs_mul, abs_of_nonneg hch, h1]
  exact le_of_eq (by ring)

/-- `|yM|` in the slot form used when the `g`-factor `D_z^{j-b}D_θ^{i-a+1}g` has order `≤ 2`. -/
theorem abs_yM_le_alt (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Spaces.Iθ) :
    |yM α f g i j a b z θ| ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) *
      (|Spaces.mixed (j - b) (i - a + 1) g z θ| * (|Spaces.mixed b a f z θ| * Wm α z θ)
        * (|Spaces.mixed j i g z θ| * Wm α z θ)) := by
  have hch : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
  have h1 : |Spaces.mixed b a f z θ * Spaces.mixed (j - b) (i - a + 1) g z θ
      * Spaces.mixed j i g z θ * (Wm α z θ) ^ 2| = |Spaces.mixed b a f z θ|
        * (|Spaces.mixed (j - b) (i - a + 1) g z θ| * |Spaces.mixed j i g z θ|)
        * (Wm α z θ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg (Wm α z θ)), abs_mul, abs_mul]
    ring
  rw [yM, abs_mul, abs_of_nonneg hch, h1]
  exact le_of_eq (by ring)

/-- Assembly step: a `D_z`-slot summand dominated by `c` times an integrable slot. -/
theorem xD_finish {f g : ℝ → ℝ → ℝ} {i b : ℕ} {c K : ℝ} {S : ℝ × ℝ → ℝ} (hc0 : 0 ≤ c)
    (hslot_int : MeasureTheory.Integrable S pm)
    (hslot_le : ∫ p, S p ∂pm ≤ K)
    (hle : ∀ᵐ p ∂pm, |xD f g i b p.1 p.2| ≤ c * S p)
    (haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => |xD f g i b p.1 p.2|) pm) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => |xD f g i b p.1 p.2|) pm ∧
      ∫ p, |xD f g i b p.1 p.2| ∂pm ≤ c * K := by
  have hint : MeasureTheory.Integrable (fun p : ℝ × ℝ => |xD f g i b p.1 p.2|) pm := by
    refine MeasureTheory.Integrable.mono' (hslot_int.const_mul c) haesm ?_
    filter_upwards [hle] with p hp
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    exact hp
  refine ⟨hint, ?_⟩
  have h1 : ∫ p, |xD f g i b p.1 p.2| ∂pm ≤ ∫ p, c * S p ∂pm := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun p => abs_nonneg _)
      (hslot_int.const_mul c) ?_
    filter_upwards [hle] with p hp
    exact hp
  rw [integral_const_mul] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_left hslot_le hc0)

/-- Assembly step: a mixed-slot summand dominated by `c` times an integrable slot. -/
theorem yM_finish {α : ℝ} {f g : ℝ → ℝ → ℝ} {i j a b : ℕ} {c K : ℝ} {S : ℝ × ℝ → ℝ}
    (hc0 : 0 ≤ c) (hslot_int : MeasureTheory.Integrable S pm)
    (hslot_le : ∫ p, S p ∂pm ≤ K)
    (hle : ∀ᵐ p ∂pm, |yM α f g i j a b p.1 p.2| ≤ c * S p)
    (haesm : AEStronglyMeasurable (fun p : ℝ × ℝ => |yM α f g i j a b p.1 p.2|) pm) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => |yM α f g i j a b p.1 p.2|) pm ∧
      ∫ p, |yM α f g i j a b p.1 p.2| ∂pm ≤ c * K := by
  have hint : MeasureTheory.Integrable (fun p : ℝ × ℝ => |yM α f g i j a b p.1 p.2|) pm := by
    refine MeasureTheory.Integrable.mono' (hslot_int.const_mul c) haesm ?_
    filter_upwards [hle] with p hp
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    exact hp
  refine ⟨hint, ?_⟩
  have h1 : ∫ p, |yM α f g i j a b p.1 p.2| ∂pm ≤ ∫ p, c * S p ∂pm := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun p => abs_nonneg _)
      (hslot_int.const_mul c) ?_
    filter_upwards [hle] with p hp
    exact hp
  rw [integral_const_mul] at h1
  exact le_trans h1 (mul_le_mul_of_nonneg_left hslot_le hc0)

/-- Each `D_z`-slot Leibniz summand (with the hard one removed) is integrable on the plane
and bounded by `16` times the total. -/
theorem xD_summand_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (Kf Kg K3 : ℝ) (hsmf : Spaces.SmoothNbhd f) (hsmg : Spaces.SmoothNbhd g)
    (hdecf : Spaces.DecayAll 4 f) (hdecg : Spaces.DecayAll 4 g)
    (hmemf : Spaces.HkMem α 4 f) (hmemg : Spaces.HkMem α 4 g)
    (hKf : ∀ b a : ℕ, a + b ≤ 2 → Spaces.supAbs (Spaces.mixed b a f) ≤ Kf)
    (hKg : ∀ b a : ℕ, a + b ≤ 2 → Spaces.supAbs (Spaces.mixed b a g) ≤ Kg)
    (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg) (hK3 : 0 ≤ K3) (i b : ℕ) (hi : i ≤ 4) (hbi : b ≤ i) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => if i = 4 ∧ b = 0 then 0 else |xD f g i b p.1 p.2|) pm ∧
      ∫ p, (if i = 4 ∧ b = 0 then 0 else |xD f g i b p.1 p.2|) ∂pm
        ≤ 16 * TTot α f g Kf Kg K3 := by
  have hT := TTot_nonneg α f g Kf Kg K3 hKf0 hKg0 hK3
  by_cases hcase : i = 4 ∧ b = 0
  · have hz : (fun p : ℝ × ℝ => if i = 4 ∧ b = 0 then 0 else |xD f g i b p.1 p.2|)
        = fun _ => 0 := by funext p; rw [if_pos hcase]
    rw [hz]
    refine ⟨integrable_zero _ _ _, ?_⟩
    rw [MeasureTheory.integral_zero]
    exact mul_nonneg (by norm_num) hT
  · have hz : (fun p : ℝ × ℝ => if i = 4 ∧ b = 0 then 0 else |xD f g i b p.1 p.2|)
        = fun p => |xD f g i b p.1 p.2| := by funext p; rw [if_neg hcase]
    rw [hz]
    have hch : (i.choose b : ℝ) ≤ 16 := choose_le_16 hi hbi
    have hc0 : 0 ≤ (i.choose b : ℝ) := by positivity
    by_cases hb2 : b ≤ 2
    · have hib : i - b ≤ 3 := by omega
      obtain ⟨hslot_int, hslot_le⟩ := xDKf_bound α hα hα1 f g Kf hsmf hsmg hdecf hdecg
        hmemf hmemg hKf hKf0 i b hi hbi hib hb2
      have hle : ∀ᵐ p ∂pm, |xD f g i b p.1 p.2| ≤ (i.choose b : ℝ) * xDA α f g i b p := by
        filter_upwards [xDA_eq α f g i b, ae_pm_mem] with p hp hmem
        rw [hp]
        exact abs_xD_le α hα f g i b hmem.2
      obtain ⟨hint, hbd⟩ := xD_finish hc0 hslot_int hslot_le hle
        (abs_aesm_pm (xD_aesm f g hsmf hsmg i b))
      refine ⟨hint, ?_⟩
      have hK : Kf * Spaces.HkNorm α 4 g * Spaces.HkNorm α 4 g = Kf * Spaces.HkSq α 4 g := by
        have h2 : Spaces.HkNorm α 4 g * Spaces.HkNorm α 4 g = Spaces.HkSq α 4 g :=
          Real.mul_self_sqrt (Spaces.HkSq_nonneg α 4 g)
        rw [mul_assoc, h2]
      calc ∫ p, |xD f g i b p.1 p.2| ∂pm
          ≤ (i.choose b : ℝ) * (Kf * Spaces.HkNorm α 4 g * Spaces.HkNorm α 4 g) := hbd
        _ = (i.choose b : ℝ) * (Kf * Spaces.HkSq α 4 g) := by rw [hK]
        _ ≤ 16 * (Kf * Spaces.HkSq α 4 g) :=
            mul_le_mul_of_nonneg_right hch (mul_nonneg hKf0 (Spaces.HkSq_nonneg α 4 g))
        _ ≤ 16 * TTot α f g Kf Kg K3 :=
            mul_le_mul_of_nonneg_left (le_TTot_Kf α f g Kf Kg K3 hKg0 hK3) (by norm_num)
    · have hb3 : 3 ≤ b := by omega
      obtain ⟨hslot_int, hslot_le⟩ := xDKg_bound α hα hα1 f g Kg hsmf hsmg hdecf hdecg
        hmemf hmemg hKg hKg0 i b hi hbi hb3
      have hle : ∀ᵐ p ∂pm, |xD f g i b p.1 p.2| ≤ (i.choose b : ℝ) * xDB α f g i b p := by
        filter_upwards [xDB_eq α f g i b, ae_pm_mem] with p hp hmem
        rw [hp]
        exact abs_xD_le_alt f g i b hmem.2
      obtain ⟨hint, hbd⟩ := xD_finish hc0 hslot_int hslot_le hle
        (abs_aesm_pm (xD_aesm f g hsmf hsmg i b))
      refine ⟨hint, ?_⟩
      calc ∫ p, |xD f g i b p.1 p.2| ∂pm
          ≤ (i.choose b : ℝ) * (Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g) := hbd
        _ ≤ 16 * (Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g) :=
            mul_le_mul_of_nonneg_right hch
              (mul_nonneg (mul_nonneg hKg0 (Spaces.HkNorm_nonneg α 4 f))
                (Spaces.HkNorm_nonneg α 4 g))
        _ ≤ 16 * TTot α f g Kf Kg K3 :=
            mul_le_mul_of_nonneg_left (le_TTot_Kg α f g Kf Kg K3 hKf0 hK3) (by norm_num)

/-- Each mixed-slot Leibniz summand (with the hard ones removed) is integrable on the plane
and bounded by `256` times the total. -/
theorem yM_summand_bound (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (Kf Kg K3 : ℝ) (hsmf : Spaces.SmoothNbhd f) (hsmg : Spaces.SmoothNbhd g)
    (hdecf : Spaces.DecayAll 4 f) (hdecg : Spaces.DecayAll 4 g)
    (hmemf : Spaces.HkMem α 4 f) (hmemg : Spaces.HkMem α 4 g)
    (hKf : ∀ b a : ℕ, a + b ≤ 2 → Spaces.supAbs (Spaces.mixed b a f) ≤ Kf)
    (hKg : ∀ b a : ℕ, a + b ≤ 2 → Spaces.supAbs (Spaces.mixed b a g) ≤ Kg)
    (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg) (hK3 : 0 ≤ K3)
    (hGint : MeasureTheory.IntegrableOn
      (fun z => (supAbsTh (Spaces.DzIter 3 f) z * Spaces.w z) ^ 2) Spaces.Iz)
    (hGle : (∫ z in Spaces.Iz, (supAbsTh (Spaces.DzIter 3 f) z * Spaces.w z) ^ 2) ≤ K3)
    (i j a b : ℕ) (hi4 : i ≤ 4) (hj4 : j ≤ 4) (hai : a ≤ i) (hbj : b ≤ j) :
    MeasureTheory.Integrable
        (fun p : ℝ × ℝ => if 1 ≤ i ∧ i + j ≤ 4 then
          (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|) else 0) pm ∧
      ∫ p, (if 1 ≤ i ∧ i + j ≤ 4 then
          (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|) else 0) ∂pm
        ≤ 256 * TTot α f g Kf Kg K3 := by
  have hT := TTot_nonneg α f g Kf Kg K3 hKf0 hKg0 hK3
  by_cases houter : 1 ≤ i ∧ i + j ≤ 4
  · have hzo : (fun p : ℝ × ℝ => if 1 ≤ i ∧ i + j ≤ 4 then
          (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|) else 0)
        = fun p => (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0
            else |yM α f g i j a b p.1 p.2|) := by
      funext p; rw [if_pos houter]
    rw [hzo]
    obtain ⟨hi1, hij4⟩ := houter
    by_cases hex : a = 0 ∧ b = 0 ∧ i + j = 4
    · have hz : (fun p : ℝ × ℝ =>
          if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|)
          = fun _ => 0 := by funext p; rw [if_pos hex]
      rw [hz]
      refine ⟨integrable_zero _ _ _, ?_⟩
      rw [MeasureTheory.integral_zero]
      exact mul_nonneg (by norm_num) hT
    · have hz : (fun p : ℝ × ℝ =>
          if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|)
          = fun p => |yM α f g i j a b p.1 p.2| := by funext p; rw [if_neg hex]
      rw [hz]
      have hch : (i.choose a : ℝ) * (j.choose b : ℝ) ≤ 256 :=
        choose_mul_le_256 hi4 hai hj4 hbj
      have hc0 : 0 ≤ (i.choose a : ℝ) * (j.choose b : ℝ) := by positivity
      by_cases hab2 : a + b ≤ 2
      · obtain ⟨hslot_int, hslot_le⟩ := yMKf_bound α hα hα1 f g Kf hsmf hsmg hdecf hdecg
          hmemf hmemg hKf hKf0 i j a b hi1 hij4 hai hbj hab2 hex
        have hle : ∀ᵐ p ∂pm, |yM α f g i j a b p.1 p.2|
            ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) * yMA α f g i j a b p := by
          filter_upwards [yMA_eq α f g i j a b, ae_pm_mem] with p hp hmem
          rw [hp]
          exact abs_yM_le α f g i j a b hmem.2
        obtain ⟨hint, hbd⟩ := yM_finish hc0 hslot_int hslot_le hle
          (abs_aesm_pm (yM_aesm α f g hsmf hsmg i j a b))
        refine ⟨hint, ?_⟩
        have hK : Kf * Spaces.HkNorm α 4 g * Spaces.HkNorm α 4 g = Kf * Spaces.HkSq α 4 g := by
          have h2 : Spaces.HkNorm α 4 g * Spaces.HkNorm α 4 g = Spaces.HkSq α 4 g :=
            Real.mul_self_sqrt (Spaces.HkSq_nonneg α 4 g)
          rw [mul_assoc, h2]
        calc ∫ p, |yM α f g i j a b p.1 p.2| ∂pm
            ≤ ((i.choose a : ℝ) * (j.choose b : ℝ))
                * (Kf * Spaces.HkNorm α 4 g * Spaces.HkNorm α 4 g) := hbd
          _ = ((i.choose a : ℝ) * (j.choose b : ℝ)) * (Kf * Spaces.HkSq α 4 g) := by rw [hK]
          _ ≤ 256 * (Kf * Spaces.HkSq α 4 g) :=
              mul_le_mul_of_nonneg_right hch (mul_nonneg hKf0 (Spaces.HkSq_nonneg α 4 g))
          _ ≤ 256 * TTot α f g Kf Kg K3 :=
              mul_le_mul_of_nonneg_left (le_TTot_Kf α f g Kf Kg K3 hKg0 hK3) (by norm_num)
      · by_cases ha1 : 1 ≤ a
        · have hab3 : 3 ≤ a + b := by omega
          obtain ⟨hslot_int, hslot_le⟩ := yMKg_bound α hα hα1 f g Kg hsmf hsmg hdecf hdecg
            hmemf hmemg hKg hKg0 i j a b hi1 hij4 hai hbj ha1 hab3
          have hle : ∀ᵐ p ∂pm, |yM α f g i j a b p.1 p.2|
              ≤ ((i.choose a : ℝ) * (j.choose b : ℝ)) * yMB α f g i j a b p := by
            filter_upwards [yMB_eq α f g i j a b, ae_pm_mem] with p hp hmem
            rw [hp]
            exact abs_yM_le_alt α f g i j a b hmem.2
          obtain ⟨hint, hbd⟩ := yM_finish hc0 hslot_int hslot_le hle
            (abs_aesm_pm (yM_aesm α f g hsmf hsmg i j a b))
          refine ⟨hint, ?_⟩
          calc ∫ p, |yM α f g i j a b p.1 p.2| ∂pm
              ≤ ((i.choose a : ℝ) * (j.choose b : ℝ))
                  * (Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g) := hbd
            _ ≤ 256 * (Kg * Spaces.HkNorm α 4 f * Spaces.HkNorm α 4 g) :=
                mul_le_mul_of_nonneg_right hch
                  (mul_nonneg (mul_nonneg hKg0 (Spaces.HkNorm_nonneg α 4 f))
                    (Spaces.HkNorm_nonneg α 4 g))
            _ ≤ 256 * TTot α f g Kf Kg K3 :=
                mul_le_mul_of_nonneg_left (le_TTot_Kg α f g Kf Kg K3 hKf0 hK3) (by norm_num)
        · -- the exceptional case `(i,j,a,b) = (1,3,0,3)`
          have ha0 : a = 0 := by omega
          subst ha0
          have hb3 : 3 ≤ b := by omega
          have hj3 : j = 3 := by omega
          subst hj3
          have hi1' : i = 1 := by omega
          subst hi1'
          have hb3' : b = 3 := by omega
          subst hb3'
          obtain ⟨⟨hexc_int, hexc_le⟩, _⟩ := T1ExcBoundAux α f g K3 hα hα1 hsmf hsmg
            hdecf hdecg hmemf hmemg hGint hGle hK3
          have hyMeq : (fun p : ℝ × ℝ => |Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
                * Spaces.mixed 3 1 g p.1 p.2 * (Wm α p.1 p.2) ^ 2|)
              =ᵐ[pm] fun p => |yM α f g 1 3 0 3 p.1 p.2| := by
            filter_upwards with p
            have hinner : yM α f g 1 3 0 3 p.1 p.2
                = Spaces.DzIter 3 f p.1 p.2 * Spaces.mixed 0 2 g p.1 p.2
                  * Spaces.mixed 3 1 g p.1 p.2 * (Wm α p.1 p.2) ^ 2 := by
              simp only [yM, Spaces.mixed_zero_right]
              norm_num
              try ring
            exact (congrArg abs hinner).symm
          refine ⟨hexc_int.congr hyMeq, ?_⟩
          rw [← integral_congr_ae hyMeq]
          have h5 : Real.sqrt K3 * Spaces.HkSq α 4 g ≤ TTot α f g Kf Kg K3 :=
            le_TTot_sqrt α f g Kf Kg K3 hKf0 hKg0
          have h6 : TTot α f g Kf Kg K3 ≤ 256 * TTot α f g Kf Kg K3 := by linarith
          linarith
  · have hz : (fun p : ℝ × ℝ => if 1 ≤ i ∧ i + j ≤ 4 then
        (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|) else 0)
        = fun _ => 0 := by funext p; rw [if_neg houter]
    rw [hz]
    refine ⟨integrable_zero _ _ _, ?_⟩
    rw [MeasureTheory.integral_zero]
    exact mul_nonneg (by norm_num) hT

/-- The `D_z`-slot term of `EasyMajor`. -/
abbrev EMx (f g : ℝ → ℝ → ℝ) (i b : ℕ) (p : ℝ × ℝ) : ℝ :=
  if i = 4 ∧ b = 0 then 0 else |xD f g i b p.1 p.2|

/-- The `(a,b)`-summand of a mixed slot of `EasyMajor` (with the hard terms removed). -/
abbrev EMyA (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) (p : ℝ × ℝ) : ℝ :=
  if 1 ≤ i ∧ i + j ≤ 4 then
    (if a = 0 ∧ b = 0 ∧ i + j = 4 then 0 else |yM α f g i j a b p.1 p.2|)
  else 0

/-- The `(i,j)`-summand of the mixed part of `EasyMajor`. -/
abbrev EMy (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j : ℕ) (p : ℝ × ℝ) : ℝ :=
  ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), EMyA α f g i j a b p

/-- `EasyMajor` as a function of the plane variable. -/
abbrev EMS (α : ℝ) (f g : ℝ → ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), EMx f g i b p)
    + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, EMy α f g i j p

/-- `EMS` is `EasyMajor` evaluated at the pair. -/
theorem EasyMajor_eq_EMS (α : ℝ) (f g : ℝ → ℝ → ℝ) (p : ℝ × ℝ) :
    EasyMajor α f g p.1 p.2 = EMS α f g p := by
  simp only [EasyMajor, EMS, EMx, EMy, EMyA]
  rw [add_right_inj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hc : 1 ≤ i ∧ i + j ≤ 4
  · simp only [if_pos hc]
  · simp only [if_neg hc, Finset.sum_const_zero]

theorem sum_range_range_le_25 (c : ℝ) (hc : 0 ≤ c) :
    (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), c) ≤ 25 * c := by
  calc (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), c)
      ≤ ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range 5, c := by
        refine Finset.sum_le_sum fun i hi => ?_
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun b _ _ => hc)
        exact Finset.range_subset_range.mpr (by have := Finset.mem_range.mp hi; omega)
    _ = 25 * c := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem sum_le_25_of_le4 (c : ℝ) (hc : 0 ≤ c) (i j : ℕ) (hi : i ≤ 4) (hj : j ≤ 4) :
    (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), c) ≤ 25 * c := by
  have hsub1 : Finset.range (i + 1) ⊆ Finset.range 5 :=
    Finset.range_subset_range.mpr (by omega)
  have hsub2 : Finset.range (j + 1) ⊆ Finset.range 5 :=
    Finset.range_subset_range.mpr (by omega)
  calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1), c)
      ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range 5, c := by
        refine Finset.sum_le_sum fun a ha => ?_
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun b _ _ => hc)
    _ ≤ ∑ a ∈ Finset.range 5, ∑ b ∈ Finset.range 5, c := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun a _ _ => ?_)
        exact Finset.sum_nonneg fun b _ => hc
    _ = 25 * c := by
        simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring

theorem EMS_int_and_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (f g : ℝ → ℝ → ℝ)
    (Kf Kg K3 : ℝ) (hsmf : Spaces.SmoothNbhd f) (hsmg : Spaces.SmoothNbhd g)
    (hdecf : Spaces.DecayAll 4 f) (hdecg : Spaces.DecayAll 4 g)
    (hmemf : Spaces.HkMem α 4 f) (hmemg : Spaces.HkMem α 4 g)
    (hKf : ∀ b a : ℕ, a + b ≤ 2 → Spaces.supAbs (Spaces.mixed b a f) ≤ Kf)
    (hKg : ∀ b a : ℕ, a + b ≤ 2 → Spaces.supAbs (Spaces.mixed b a g) ≤ Kg)
    (hKf0 : 0 ≤ Kf) (hKg0 : 0 ≤ Kg) (hK3 : 0 ≤ K3)
    (hGint : MeasureTheory.IntegrableOn
      (fun z => (supAbsTh (Spaces.DzIter 3 f) z * Spaces.w z) ^ 2) Spaces.Iz)
    (hGle : (∫ z in Spaces.Iz, (supAbsTh (Spaces.DzIter 3 f) z * Spaces.w z) ^ 2) ≤ K3) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => EasyMajor α f g p.1 p.2) pm ∧
      ∫ p, EasyMajor α f g p.1 p.2 ∂pm ≤ 5000000 * TTot α f g Kf Kg K3 := by
  have hT := TTot_nonneg α f g Kf Kg K3 hKf0 hKg0 hK3
  -- ### the `D_z` part
  have hxD : ∀ i ∈ Finset.range 5, ∀ b ∈ Finset.range (i + 1),
      MeasureTheory.Integrable (fun p : ℝ × ℝ => EMx f g i b p) pm ∧
        ∫ p, EMx f g i b p ∂pm ≤ 16 * TTot α f g Kf Kg K3 :=
    fun i hi b hb => xD_summand_bound α hα hα1 f g Kf Kg K3 hsmf hsmg hdecf hdecg hmemf
      hmemg hKf hKg hKf0 hKg0 hK3 i b (by have := Finset.mem_range.mp hi; omega)
      (by have := Finset.mem_range.mp hb; omega)
  have hxD_int : ∀ i ∈ Finset.range 5,
      MeasureTheory.Integrable (fun p : ℝ × ℝ => ∑ b ∈ Finset.range (i + 1), EMx f g i b p) pm :=
    fun i hi => integrable_finsetSum _ fun b hb => (hxD i hi b hb).1
  have hSx_int : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), EMx f g i b p) pm :=
    integrable_finsetSum _ hxD_int
  have hSx_val : (∫ p, (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), EMx f g i b p) ∂pm)
      = ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), ∫ p, EMx f g i b p ∂pm := by
    rw [integral_finsetSum _ hxD_int]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_finsetSum _ fun b hb => (hxD i hi b hb).1]
  have hSx_le : (∫ p, (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), EMx f g i b p) ∂pm)
      ≤ 25 * (16 * TTot α f g Kf Kg K3) := by
    rw [hSx_val]
    calc (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), ∫ p, EMx f g i b p ∂pm)
        ≤ ∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), (16 * TTot α f g Kf Kg K3) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun b hb => (hxD i hi b hb).2
      _ ≤ 25 * (16 * TTot α f g Kf Kg K3) :=
          sum_range_range_le_25 (16 * TTot α f g Kf Kg K3) (mul_nonneg (by norm_num) hT)
  -- ### the mixed part
  have hyM : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5, ∀ a ∈ Finset.range (i + 1),
      ∀ b ∈ Finset.range (j + 1),
      MeasureTheory.Integrable (fun p : ℝ × ℝ => EMyA α f g i j a b p) pm ∧
        ∫ p, EMyA α f g i j a b p ∂pm ≤ 256 * TTot α f g Kf Kg K3 := by
    intro i hi j hj a ha b hb
    exact yM_summand_bound α hα hα1 f g Kf Kg K3 hsmf hsmg hdecf hdecg hmemf hmemg
      hKf hKg hKf0 hKg0 hK3 hGint hGle i j a b (by have := Finset.mem_range.mp hi; omega)
      (by have := Finset.mem_range.mp hj; omega) (by have := Finset.mem_range.mp ha; omega)
      (by have := Finset.mem_range.mp hb; omega)
  have hyM_ij : ∀ i ∈ Finset.range 5, ∀ j ∈ Finset.range 5,
      MeasureTheory.Integrable (fun p : ℝ × ℝ => EMy α f g i j p) pm ∧
        ∫ p, EMy α f g i j p ∂pm ≤ 625 * (256 * TTot α f g Kf Kg K3) := by
    intro i hi j hj
    constructor
    · exact integrable_finsetSum _ fun a ha =>
        integrable_finsetSum _ fun b hb => (hyM i hi j hj a ha b hb).1
    · rw [integral_finsetSum _ (fun a ha =>
          integrable_finsetSum _ fun b hb => (hyM i hi j hj a ha b hb).1)]
      have hval : (∑ a ∈ Finset.range (i + 1),
            ∫ p, (∑ b ∈ Finset.range (j + 1), EMyA α f g i j a b p) ∂pm)
          = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              ∫ p, EMyA α f g i j a b p ∂pm := by
        refine Finset.sum_congr rfl fun a ha => ?_
        rw [integral_finsetSum _ fun b hb => (hyM i hi j hj a ha b hb).1]
      rw [hval]
      calc (∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
            ∫ p, EMyA α f g i j a b p ∂pm)
          ≤ ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
              (256 * TTot α f g Kf Kg K3) :=
            Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => (hyM i hi j hj a ha b hb).2
        _ ≤ 25 * (256 * TTot α f g Kf Kg K3) :=
            sum_le_25_of_le4 (256 * TTot α f g Kf Kg K3) (mul_nonneg (by norm_num) hT) i j
              (by have := Finset.mem_range.mp hi; omega) (by have := Finset.mem_range.mp hj; omega)
        _ ≤ 625 * (256 * TTot α f g Kf Kg K3) := by
            have h1 : (0 : ℝ) ≤ 256 * TTot α f g Kf Kg K3 := mul_nonneg (by norm_num) hT
            nlinarith [h1]
  have hSy_int : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, EMy α f g i j p) pm :=
    integrable_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj => (hyM_ij i hi j hj).1
  have hSy_val : (∫ p, (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, EMy α f g i j p) ∂pm)
      = ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, ∫ p, EMy α f g i j p ∂pm := by
    rw [integral_finsetSum _ fun i hi => integrable_finsetSum _ fun j hj => (hyM_ij i hi j hj).1]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_finsetSum _ fun j hj => (hyM_ij i hi j hj).1]
  have hSy_le : (∫ p, (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, EMy α f g i j p) ∂pm)
      ≤ 25 * (625 * (256 * TTot α f g Kf Kg K3)) := by
    rw [hSy_val]
    calc (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, ∫ p, EMy α f g i j p ∂pm)
        ≤ ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, (625 * (256 * TTot α f g Kf Kg K3)) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => (hyM_ij i hi j hj).2
      _ = 25 * (625 * (256 * TTot α f g Kf Kg K3)) := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          ring
  -- ### assembly
  have hEMS_int : MeasureTheory.Integrable (fun p : ℝ × ℝ => EMS α f g p) pm :=
    hSx_int.add hSy_int
  have hval : (∫ p, EMS α f g p ∂pm)
      = (∫ p, (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), EMx f g i b p) ∂pm)
        + ∫ p, (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, EMy α f g i j p) ∂pm := by
    show (∫ p, ((∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1), EMx f g i b p)
        + ∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5, EMy α f g i j p) ∂pm) = _
    rw [integral_add hSx_int hSy_int]
  refine ⟨hEMS_int.congr (Eventually.of_forall fun p => (EasyMajor_eq_EMS α f g p).symm), ?_⟩
  rw [integral_congr_ae (Eventually.of_forall fun p => EasyMajor_eq_EMS α f g p), hval]
  have h1 : (∫ p, (∑ i ∈ Finset.range 5, ∑ b ∈ Finset.range (i + 1),
        EMx f g i b p) ∂pm) + (∫ p, (∑ i ∈ Finset.range 5, ∑ j ∈ Finset.range 5,
        EMy α f g i j p) ∂pm)
      ≤ 25 * (16 * TTot α f g Kf Kg K3) + 25 * (625 * (256 * TTot α f g Kf Kg K3)) :=
    add_le_add hSx_le hSy_le
  have h2 : 25 * (16 * TTot α f g Kf Kg K3) + 25 * (625 * (256 * TTot α f g Kf Kg K3))
      ≤ 5000000 * TTot α f g Kf Kg K3 := by
    nlinarith [hT]
  linarith

/-! ## Continuity of `T1Easy` on the open quadrant (used for measurability) -/

theorem smoothNbhd_sin_two : Spaces.SmoothNbhd (fun _z θ : ℝ => Real.sin (2 * θ)) := by
  show ContDiffOn ℝ ⊤ (Function.uncurry (fun _z θ : ℝ => Real.sin (2 * θ)))
    (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (π / 2 + 1))
  have h : ContDiff ℝ ⊤ (fun p : ℝ × ℝ => Real.sin (2 * p.2)) :=
    Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)
  exact h.contDiffOn

theorem smoothNbhd_continuousOn {u : ℝ → ℝ → ℝ} (h : Spaces.SmoothNbhd u) :
    ContinuousOn (fun p : ℝ × ℝ => u p.1 p.2) Qd :=
  h.continuousOn.mono Qd_subset_nbhU

theorem smoothNbhd_Dth {u : ℝ → ℝ → ℝ} (h : Spaces.SmoothNbhd u) :
    Spaces.SmoothNbhd (Spaces.Dth u) :=
  smoothNbhd_mul smoothNbhd_sin_two (Spaces.SmoothNbhd.pth h)

theorem contOn_add {F G : ℝ × ℝ → ℝ} (hF : ContinuousOn F Qd) (hG : ContinuousOn G Qd) :
    ContinuousOn (fun p => F p + G p) Qd := by
  have h := hF.add hG
  have heq : (F + G : ℝ × ℝ → ℝ) = fun p => F p + G p := by
    funext p; rw [Pi.add_apply]
  rw [heq] at h
  exact h

theorem contOn_sub {F G : ℝ × ℝ → ℝ} (hF : ContinuousOn F Qd) (hG : ContinuousOn G Qd) :
    ContinuousOn (fun p => F p - G p) Qd := by
  have h := hF.sub hG
  have heq : (F - G : ℝ × ℝ → ℝ) = fun p => F p - G p := by
    funext p; rw [Pi.sub_apply]
  rw [heq] at h
  exact h

theorem contOn_mul {F G : ℝ × ℝ → ℝ} (hF : ContinuousOn F Qd) (hG : ContinuousOn G Qd) :
    ContinuousOn (fun p => F p * G p) Qd := by
  have h := hF.mul hG
  have heq : (F * G : ℝ × ℝ → ℝ) = fun p => F p * G p := by
    funext p; rw [Pi.mul_apply]
  rw [heq] at h
  exact h

theorem contOn_pow {F : ℝ × ℝ → ℝ} (hF : ContinuousOn F Qd) (n : ℕ) :
    ContinuousOn (fun p => F p ^ n) Qd := by
  have h := hF.pow n
  have heq : (F ^ n : ℝ × ℝ → ℝ) = fun p => F p ^ n := by
    funext p; rw [Pi.pow_apply]
  rw [heq] at h
  exact h

theorem T1Easy_contOn (α : ℝ) (f g : ℝ → ℝ → ℝ)
    (hsmf : Spaces.SmoothNbhd f) (hsmg : Spaces.SmoothNbhd g) :
    ContinuousOn (fun p : ℝ × ℝ => T1Easy α f g p.1 p.2) Qd := by
  have hcWhz : ContinuousOn (fun p : ℝ × ℝ => Whz p.1 p.2) Qd := continuousOn_Whz_Qd
  have hcWm : ContinuousOn (fun p : ℝ × ℝ => Wm α p.1 p.2) Qd := continuousOn_Wm_Qd α
  have hcse : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-Spaces.eta)) Qd :=
    continuousOn_sin_rpow_Qd (-Spaces.eta)
  have hcsg : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ (-(Spaces.gam α))) Qd :=
    continuousOn_sin_rpow_Qd (-(Spaces.gam α))
  have hcf : ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) Qd := smoothNbhd_continuousOn hsmf
  have hcw : ContinuousOn (fun p : ℝ × ℝ => Spaces.w p.1) Qd := continuousOn_w_Qd
  have hu : Spaces.SmoothNbhd (fun z θ : ℝ => f z θ * Spaces.Dth g z θ) :=
    smoothNbhd_mul hsmf (smoothNbhd_Dth hsmg)
  have hV : ∀ (V : ℝ → ℝ → ℝ), Spaces.SmoothNbhd V →
      ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2) Qd := fun V hV => smoothNbhd_continuousOn hV
  have hDV : ∀ (V : ℝ → ℝ → ℝ), Spaces.SmoothNbhd V →
      ContinuousOn (fun p : ℝ × ℝ => Spaces.Dth V p.1 p.2) Qd :=
    fun V hV => smoothNbhd_continuousOn (smoothNbhd_Dth hV)
  have h4 : Spaces.SmoothNbhd (Spaces.DzIter 4 g) := Spaces.SmoothNbhd.DzIter hsmg 4
  have h31 : Spaces.SmoothNbhd (Spaces.mixed 3 1 g) :=
    Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg 1) 3
  have h22 : Spaces.SmoothNbhd (Spaces.mixed 2 2 g) :=
    Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg 2) 2
  have h13 : Spaces.SmoothNbhd (Spaces.mixed 1 3 g) :=
    Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg 3) 1
  have h04 : Spaces.SmoothNbhd (Spaces.mixed 0 4 g) :=
    Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg 4) 0
  have hH : ContinuousOn (fun p : ℝ × ℝ =>
      H4PairInt α (fun z θ : ℝ => f z θ * Spaces.Dth g z θ) g p.1 p.2) Qd := by
    simp only [H4PairInt]
    refine contOn_add ?_ ?_
    · refine continuousOn_finsetSum (Finset.range 5) fun i _ => ?_
      exact contOn_mul
        (contOn_mul (smoothNbhd_continuousOn (Spaces.SmoothNbhd.DzIter hu i)) hcWhz)
        (contOn_mul (smoothNbhd_continuousOn (Spaces.SmoothNbhd.DzIter hsmg i)) hcWhz)
    · refine continuousOn_finsetSum (Finset.range 5) fun i _ =>
        continuousOn_finsetSum (Finset.range 5) fun j _ => ?_
      by_cases hc : 1 ≤ i ∧ i + j ≤ 4
      · simp only [if_pos hc]
        exact contOn_mul
          (contOn_mul (smoothNbhd_continuousOn
            (Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hu i) j)) hcWm)
          (contOn_mul (smoothNbhd_continuousOn
            (Spaces.SmoothNbhd.DzIter (Spaces.SmoothNbhd.DthIter hsmg i) j)) hcWm)
      · simp only [if_neg hc]
        exact continuousOn_const
  have hT : ContinuousOn (fun p : ℝ × ℝ => T1Hard α f g p.1 p.2) Qd := by
    simp only [T1Hard]
    refine contOn_mul (contOn_mul hcf (contOn_pow hcw 2)) ?_
    refine contOn_add ?_ ?_
    · exact contOn_mul (contOn_mul (hDV _ h4) (hV _ h4)) hcse
    · refine contOn_mul (contOn_add (contOn_add (contOn_add ?_ ?_) ?_) ?_) hcsg
      · exact contOn_mul (hDV _ h31) (hV _ h31)
      · exact contOn_mul (hDV _ h22) (hV _ h22)
      · exact contOn_mul (hDV _ h13) (hV _ h13)
      · exact contOn_mul (hDV _ h04) (hV _ h04)
  exact contOn_sub hH hT

/-- The uncurried absolute value of `T1Easy` is a.e. strongly measurable. -/
theorem T1Easy_aesm (α : ℝ) (f g : ℝ → ℝ → ℝ)
    (hsmf : Spaces.SmoothNbhd f) (hsmg : Spaces.SmoothNbhd g) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => |T1Easy α f g p.1 p.2|) pm :=
  aesm_of_Qd ((T1Easy_contOn α f g hsmf hsmg).abs)

/-- The "easy part" of the `D_θ`-transport pairing (Elgindi, Lemma `Transport1`, §`H2`): with `Kf, Kg` bounds for the `L^∞`-norms of the first and second `D_z`/`D_θ`-derivatives of `f` resp. `g` (hypotheses discharged by the `supAbs` bounds for `ℋ⁴`), and `K3` a bound for the radial integral of the angular supremum of `D_z³f·w` (hypothesis discharged by `SupThetaInt`), the easy part `T1Easy α f g = H4PairInt α (f·D_θ g) g - T1Hard α f g` (all Leibniz terms of the pairing except the five in which five derivatives fall on `g`) satisfies `∫_z ∫_θ |T1Easy α f g z θ| ≤ C·(Kf·|g|² + Kg·|f||g| + √K3·|g|²)`, with the left-hand iterated integral honest.  Route: expand `H4PairInt α (f D_θ g) g` by `Work.Spaces.DzIter_mul` (the `D_z`-slots) resp. `Work.Spaces.mixed_mul_eq` together with `mixed_Dth` (the mixed slots), remove the five `T1Hard` terms, and bound each remaining Leibniz term: when the `f`-factor has order `≤ 2` (or is `f` itself with `i+j ≤ 3`) pull out `Kf` pointwise and estimate the two `g`-factors against the `ℋ⁴`-slots; when the `f`-factor is a mixed derivative of order `≥ 3` with `a ≥ 1`, pull out the `g`-factor of order `≤ 2` (bounded by `Kg`) and Cauchy–Schwarz the `f`-slot against the remaining `g`-slot (using the global Cauchy–Schwarz/Hölder inequality in the plane); the `D_z`-slot terms with `i - b ≥ 3` are handled by pulling out `supAbs (mixed b 1 g) ≤ Kg` (order `≤ 2`); finally the single exceptional pair `(a,b) = (0,3)` (which forces `(j,i) = (3,1)`) is estimated by `√K3·|g|²` via `K3` and the radial Hardy inequality `Work.Spaces.HardyZ` applied to the angular slices. -/
theorem T1EasyBound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (f g : ℝ → ℝ → ℝ) (Kf Kg K3 : ℝ),
    0 < α → α ≤ 1 → Work.Spaces.SmoothNbhd f → Work.Spaces.SmoothNbhd g →
    Work.Spaces.DecayAll 4 f → Work.Spaces.DecayAll 4 g →
    Work.Spaces.HkMem α 4 f → Work.Spaces.HkMem α 4 g →
    (∀ b a : ℕ, a + b ≤ 2 → Work.Spaces.supAbs (Work.Spaces.mixed b a f) ≤ Kf) →
    (∀ b a : ℕ, a + b ≤ 2 → Work.Spaces.supAbs (Work.Spaces.mixed b a g) ≤ Kg) →
    (∫ z in Work.Spaces.Iz,
        (Work.FTS.H2.supAbsTh (Work.Spaces.DzIter 3 f) z * Work.Spaces.w z) ^ 2 ≤ K3) →
    0 ≤ Kf → 0 ≤ Kg → 0 ≤ K3 →
    MeasureTheory.IntegrableOn
        (fun z => ∫ θ in Work.Spaces.Iθ, |Work.FTS.H2.T1Easy α f g z θ|) Work.Spaces.Iz ∧
      ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, |Work.FTS.H2.T1Easy α f g z θ|)
        ≤ C * (Kf * Work.Spaces.HkSq α 4 g
            + Kg * Work.Spaces.HkNorm α 4 f * Work.Spaces.HkNorm α 4 g
            + Real.sqrt K3 * Work.Spaces.HkSq α 4 g) := by
  refine ⟨5000000, by norm_num, ?_⟩
  intro α f g Kf Kg K3 hα hα1 hsmf hsmg hdecf hdecg hmemf hmemg hKf hKg hGle hKf0 hKg0 hK3
  obtain ⟨C0, _hC0pos, hC0⟩ := SupThetaInt
  have hGint : MeasureTheory.IntegrableOn
      (fun z => (supAbsTh (Spaces.DzIter 3 f) z * Spaces.w z) ^ 2) Spaces.Iz :=
    (hC0 α f 3 hα hα1 (by norm_num) hsmf hdecf hmemf).1
  obtain ⟨hEM_int, hEM_le⟩ := EMS_int_and_le α hα hα1 f g Kf Kg K3 hsmf hsmg hdecf hdecg
    hmemf hmemg hKf hKg hKf0 hKg0 hK3 hGint hGle
  have hEM_outer : MeasureTheory.Integrable
      (fun z => ∫ θ in Spaces.Iθ, EasyMajor α f g z θ)
      (MeasureTheory.volume.restrict Spaces.Iz) := hEM_int.integral_prod_left
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz),
      MeasureTheory.Integrable (fun θ => EasyMajor α f g z θ)
        (MeasureTheory.volume.restrict Spaces.Iθ) := hEM_int.prod_right_ae
  have hle_ae : ∀ᵐ z ∂(MeasureTheory.volume.restrict Spaces.Iz),
      (∫ θ in Spaces.Iθ, |T1Easy α f g z θ|) ≤ ∫ θ in Spaces.Iθ, EasyMajor α f g z θ := by
    filter_upwards [hslice, MeasureTheory.ae_restrict_mem measurableSet_Ici]
      with z hzint hz
    refine integral_mono_of_nonneg (Eventually.of_forall fun θ => abs_nonneg _) hzint ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact T1Easy_le_major α hα f g hsmf hsmg z hz θ hθ
  have hTE_int : MeasureTheory.Integrable
      (fun z => ∫ θ in Spaces.Iθ, |T1Easy α f g z θ|)
      (MeasureTheory.volume.restrict Spaces.Iz) := by
    refine MeasureTheory.Integrable.mono' hEM_outer
      ((T1Easy_aesm α f g hsmf hsmg).integral_prod_right') ?_
    filter_upwards [hle_ae] with z hz
    rw [Real.norm_of_nonneg (integral_nonneg fun θ => abs_nonneg _)]
    exact hz
  refine ⟨hTE_int, ?_⟩
  have h1 : (∫ z in Spaces.Iz, (∫ θ in Spaces.Iθ, |T1Easy α f g z θ|))
      ≤ ∫ z in Spaces.Iz, (∫ θ in Spaces.Iθ, EasyMajor α f g z θ) :=
    integral_mono_of_nonneg (Eventually.of_forall fun z => integral_nonneg fun θ => abs_nonneg _)
      hEM_outer hle_ae
  have h2 : (∫ z in Spaces.Iz, (∫ θ in Spaces.Iθ, EasyMajor α f g z θ))
      = ∫ p, EasyMajor α f g p.1 p.2 ∂pm := MeasureTheory.integral_integral hEM_int
  rw [h2] at h1
  exact le_trans (le_trans h1 hEM_le) (le_of_eq rfl)

end Work.FTS.H2
