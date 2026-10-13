import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Cores.SigABasic
import Submission.Work.FTS.EllipticEst.Cores.sliceRateSigA
import Submission.Work.FTS.EllipticEst.Cores.sliceInterpVanishing

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux

open MeasureTheory Set Filter
open scoped Real Topology

set_option autoImplicit false

noncomputable section

local notation "sigA" => Work.FTS.EllipticEst.Cores.sigA
local notation "sigDR" => Work.FTS.EllipticEst.TT.sigDR

/-!
# The vanishing-boundary Agmon interpolation on an angular slice

For `a ∈ (0,1)` and `u` of class `C²` on `(0, π/2)`, with `u → 0` at both endpoints and with
the three weighted integrals `∫ (u')²σ`, `∫ u²σ`, `∫ (u'')²σ` finite (`σ = sin(2θ)^a`), one has

  `∫ (u')²σ ≤ C √(∫ u²σ · ∫ (u'')²σ)`.

The proof has two halves.

* **The endpoint control.**  The `σ`-weighted integrability of `u''` forces `∫_0^ε |u''| < ∞`
  (`2|x| ≤ x²σ + σ⁻¹`), hence `u'` is bounded on `(0,π/2)` (`ftc_at_quarter`) and, since
  `u → 0` at the endpoints, `|u| ≤ M θ` near `0` and `|u| ≤ M(π/2 - θ)` near `π/2`.
  Consequently `|u| ≤ M sin(2θ)` and the two boundary products of `slice_ibp_light`,
  `u u' σ` and `u² σ'`, tend to `0` at both endpoints, while the three remaining
  integrability clauses of that lemma follow by domination with `σ`.

* **The interpolation.**  `slice_ibp_light` gives
  `∫ (u')²σ = -∫ u u'' σ - 2a∫ u²σ - 2a(1-a)∫ u² cos²(2θ) sin(2θ)^{a-2}`; the last two terms
  are `≤ 0` (their integrands are `≥ 0` and `0 < a < 1`), and the first is bounded by
  Cauchy–Schwarz.  This is the already-proved `sliceInterpVanishing`, applied below.
-/

/-! ## Elementary exponent identities -/

lemma rpow_one_add {y a : ℝ} (hy : 0 < y) : y ^ (1 + a) = y * y ^ a := by
  rw [Real.rpow_add hy, Real.rpow_one]

lemma mul_rpow_sub_one {y a : ℝ} (hy : 0 < y) (ha : a ≠ 0) : y * y ^ (a - 1) = y ^ a := by
  have h : (1 : ℝ) + (a - 1) ≠ 0 := by
    intro hc
    exact ha (by linarith [show (1 : ℝ) + (a - 1) = a by ring])
  rw [← Real.rpow_one_add' hy.le h, show (1 : ℝ) + (a - 1) = a by ring]

lemma mul_rpow_sub_two {y a : ℝ} (hy : 0 < y) : y ^ 2 * y ^ (a - 2) = y ^ a := by
  rw [← Real.rpow_natCast y 2, ← Real.rpow_add hy ((2 : ℕ) : ℝ) (a - 2),
    show ((2 : ℕ) : ℝ) + (a - 2) = a by ring]

lemma sq_mul_rpow_sub_one {y a : ℝ} (hy : 0 < y) : y ^ 2 * y ^ (a - 1) = y ^ (1 + a) := by
  rw [← Real.rpow_natCast y 2, ← Real.rpow_add hy ((2 : ℕ) : ℝ) (a - 1),
    show ((2 : ℕ) : ℝ) + (a - 1) = 1 + a by ring]

/-! ## The two squeeze lemmas for the boundary limits -/

/-- Squeeze at `0⁺`: a function dominated by `A y^e` (`e > 0`) near `0` tends to `0`. -/
lemma tendsto_zero_of_abs_le_eventually {F : ℝ → ℝ} {A e ε : ℝ} (he : 0 < e) (hε : 0 < ε)
    (h : ∀ y ∈ Set.Ioo (0 : ℝ) ε, |F y| ≤ A * y ^ e) :
    Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  refine tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero' (f := fun y : ℝ => ‖F y‖) (g := fun y : ℝ => A * y ^ e) ?_ ?_
      (Work.FTS.EllipticEst.Cores.tendsto_const_mul_rpow_zero (A := A) he))
  · filter_upwards with y
    exact norm_nonneg (F y)
  · filter_upwards [Ioo_mem_nhdsGT hε] with y hy
    rw [Real.norm_eq_abs]
    exact h y hy

/-- The reflected squeeze, at `(π/2)⁻`. -/
lemma tendsto_zero_of_abs_le_eventually_right {F : ℝ → ℝ} {A e ε : ℝ} (he : 0 < e) (hε : 0 < ε)
    (h : ∀ y ∈ Set.Ioo (0 : ℝ) ε, |F (Real.pi / 2 - y)| ≤ A * y ^ e) :
    Tendsto F (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
  (Work.FTS.EllipticEst.Cores.tendsto_reflect_iff (Φ := F) (c := 0)).mp
    (tendsto_zero_of_abs_le_eventually he hε h)

/-- `(θ, π/2) ∈ nhdsWithin (π/2) (Iio (π/2))`. -/
lemma Ioo_mem_nhdsWithin_Iio {a b : ℝ} (hab : a < b) :
    Set.Ioo a b ∈ nhdsWithin b (Set.Iio b) := by
  have h1 : Set.Ioi a ∈ nhds b := Ioi_mem_nhds hab
  have h2 : Set.Iio b ∈ nhdsWithin b (Set.Iio b) := self_mem_nhdsWithin
  have h3 := Filter.inter_mem (nhdsWithin_le_nhds h1) h2
  rwa [Set.Ioi_inter_Iio] at h3

/-! ## Integrability of `u''` and the endpoint bounds -/

/-- `σ`-weighted `L²`-integrability of `u''` implies honest integrability of `u''`. -/
lemma integrableOn_deriv_deriv {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ}
    (hD : IntegrableOn (fun θ : ℝ => (deriv (deriv F) θ) ^ 2 * sigA α θ)
      (Set.Ioo 0 (Real.pi / 2))) :
    IntegrableOn (deriv (deriv F)) (Set.Ioo 0 (Real.pi / 2)) :=
  Work.FTS.EllipticEst.Cores.integrableOn_deriv measurableSet_Ioo (fun _ hx => hx) hD
    ((Work.FTS.EllipticEst.Cores.integrableOn_sigA_inv hα hα1).mono_set Ioo_subset_Icc_self)

/-- **Endpoint control of `u'`.**  The `σ`-weighted integrability of `u''` bounds `|u'|` on
`(0, π/2)` (the FTC identity of `ftc_at_quarter` at `θ₀ = π/4` and `|∫| ≤ ∫|·|`). -/
lemma exists_deriv_abs_bound {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {F : ℝ → ℝ}
    (hcd : ContDiffOn ℝ 2 F (Set.Ioo 0 (Real.pi / 2)))
    (hD : IntegrableOn (fun θ : ℝ => (deriv (deriv F) θ) ^ 2 * sigA α θ)
      (Set.Ioo 0 (Real.pi / 2))) :
    ∃ M : ℝ, 0 < M ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv F θ| ≤ M := by
  have hIdd : IntegrableOn (deriv (deriv F)) (Set.Ioo 0 (Real.pi / 2)) :=
    integrableOn_deriv_deriv hα hα1 hD
  have hC1 : ContDiffOn ℝ 1 (deriv F) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  set c : ℝ := deriv F (Real.pi / 4) - ∫ t in Set.Ioo 0 (Real.pi / 4), deriv (deriv F) t with hc
  have hftc : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv F θ - c = ∫ t in Set.Ioo 0 θ, deriv (deriv F) t :=
    Work.FTS.EllipticEst.Cores.ftc_at_quarter hC1 hIdd
  refine ⟨|c| + (∫ t in Set.Ioo 0 (Real.pi / 2), |deriv (deriv F) t|) + 1, by positivity, ?_⟩
  intro θ hθ
  have hnn : ∀ x ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ |deriv (deriv F) x| := fun x _ => abs_nonneg _
  have hmono : (∫ t in Set.Ioo 0 θ, |deriv (deriv F) t|)
      ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), |deriv (deriv F) t| :=
    Work.FTS.EllipticEst.Cores.setIntegral_mono_Ioo hθ.2.le hIdd.abs hnn
  have h1 : |deriv F θ| ≤ |deriv F θ - c| + |c| := by
    have h := abs_add_le (deriv F θ - c) c
    rwa [sub_add_cancel] at h
  have h2 : |deriv F θ - c| ≤ ∫ t in Set.Ioo 0 θ, |deriv (deriv F) t| := by
    rw [hftc θ hθ]
    exact MeasureTheory.abs_integral_le_integral_abs
  linarith [h1, h2, hmono]

/-- **The left endpoint value bound**: `|u θ| ≤ M θ` (the Lipschitz bound `|u'| ≤ M` plus the
prescribed limit `u → 0` at `0⁺`). -/
lemma value_abs_le_mul_left {F : ℝ → ℝ} (hcd : ContDiffOn ℝ 2 F (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (deriv F) (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    {M : ℝ} (hMnn : 0 ≤ M) (hM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv F θ| ≤ M) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |F θ| ≤ M * θ := by
  have hC1 : ContDiffOn ℝ 1 F (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hcd.of_le (by norm_num)
  have hC1d : ContDiffOn ℝ 1 (deriv F) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  intro θ hθ
  have htend : Tendsto (fun θ' : ℝ => |F θ - F θ'|) (nhdsWithin 0 (Set.Ioi 0)) (nhds |F θ|) := by
    have h1 : Tendsto (fun θ' : ℝ => F θ - F θ') (nhdsWithin 0 (Set.Ioi 0)) (nhds (F θ - 0)) :=
      tendsto_const_nhds.sub h0
    simpa using h1.abs
  refine le_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsGT hθ.1] with θ' hθ'
  have hsub : Set.Ioo θ' θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨hθ'.1.trans hx.1, hx.2.trans hθ.2⟩
  have hul : Set.uIcc θ' θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [Set.uIcc_of_le hθ'.2.le]
    exact fun x hx => ⟨hθ'.1.trans_le hx.1, hx.2.trans_lt hθ.2⟩
  have hftc : F θ - F θ' = ∫ t in Set.Ioo θ' θ, deriv F t :=
    Work.FTS.EllipticEst.Cores.ftc_interior hC1 ⟨hθ'.1, hθ'.2.trans hθ.2⟩ hθ hθ'.2
      ((hC1d.continuousOn.mono hul).intervalIntegrable)
  have hInt1 : IntegrableOn (fun t : ℝ => |deriv F t|) (Set.Ioo θ' θ) :=
    (hint.mono_set hsub).abs
  have hInt2 : IntegrableOn (fun _ : ℝ => M) (Set.Ioo θ' θ) :=
    MeasureTheory.integrableOn_const (s := Set.Ioo θ' θ) (by rw [Real.volume_Ioo]; simp) (by simp)
  calc |F θ - F θ'| = |∫ t in Set.Ioo θ' θ, deriv F t| := by rw [hftc]
    _ ≤ ∫ t in Set.Ioo θ' θ, |deriv F t| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ t in Set.Ioo θ' θ, M :=
        MeasureTheory.setIntegral_mono_on hInt1 hInt2 measurableSet_Ioo
          (fun t ht => hM t (hsub ht))
    _ = M * (θ - θ') := by
        rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioo,
          max_eq_left (by linarith [hθ'.2]), smul_eq_mul]
        ring
    _ ≤ M * θ := by nlinarith [hMnn, hθ'.1]

/-- **The right endpoint value bound**: `|u θ| ≤ M (π/2 - θ)`. -/
lemma value_abs_le_mul_right {F : ℝ → ℝ} (hcd : ContDiffOn ℝ 2 F (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (deriv F) (Set.Ioo 0 (Real.pi / 2)))
    (h1 : Tendsto F (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0))
    {M : ℝ} (hMnn : 0 ≤ M) (hM : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv F θ| ≤ M) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |F θ| ≤ M * (Real.pi / 2 - θ) := by
  have hC1 : ContDiffOn ℝ 1 F (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hcd.of_le (by norm_num)
  have hC1d : ContDiffOn ℝ 1 (deriv F) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)
  intro θ hθ
  have htend : Tendsto (fun θ' : ℝ => |F θ - F θ'|)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds |F θ|) := by
    have h1' : Tendsto (fun θ' : ℝ => F θ - F θ')
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds (F θ - 0)) :=
      tendsto_const_nhds.sub h1
    simpa using h1'.abs
  refine le_of_tendsto htend ?_
  filter_upwards [Ioo_mem_nhdsWithin_Iio hθ.2] with θ' hθ'
  have hsub : Set.Ioo θ θ' ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
    fun x hx => ⟨hθ.1.trans hx.1, hx.2.trans hθ'.2⟩
  have hul : Set.uIcc θ θ' ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rw [Set.uIcc_of_le hθ'.1.le]
    exact fun x hx => ⟨hθ.1.trans_le hx.1, hx.2.trans_lt hθ'.2⟩
  have hftc : F θ' - F θ = ∫ t in Set.Ioo θ θ', deriv F t :=
    Work.FTS.EllipticEst.Cores.ftc_interior hC1 hθ ⟨hθ.1.trans hθ'.1, hθ'.2⟩ hθ'.1
      ((hC1d.continuousOn.mono hul).intervalIntegrable)
  have hInt1 : IntegrableOn (fun t : ℝ => |deriv F t|) (Set.Ioo θ θ') :=
    (hint.mono_set hsub).abs
  have hInt2 : IntegrableOn (fun _ : ℝ => M) (Set.Ioo θ θ') :=
    MeasureTheory.integrableOn_const (s := Set.Ioo θ θ') (by rw [Real.volume_Ioo]; simp) (by simp)
  have hneg : F θ - F θ' = -(F θ' - F θ) := by ring
  calc |F θ - F θ'| = |F θ' - F θ| := by rw [hneg, abs_neg]
    _ = |∫ t in Set.Ioo θ θ', deriv F t| := by rw [hftc]
    _ ≤ ∫ t in Set.Ioo θ θ', |deriv F t| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ t in Set.Ioo θ θ', M :=
        MeasureTheory.setIntegral_mono_on hInt1 hInt2 measurableSet_Ioo
          (fun t ht => hM t (hsub ht))
    _ = M * (θ' - θ) := by
        rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioo,
          max_eq_left (by linarith [hθ'.1]), smul_eq_mul]
        ring
    _ ≤ M * (Real.pi / 2 - θ) := by nlinarith [hMnn, hθ'.2]

/-- Transfer of `IntegrableOn` from the open interval to `Iθ` (they differ by a null set). -/
lemma integrableOn_Iθ_of_Ioo {f : ℝ → ℝ}
    (h : IntegrableOn f (Set.Ioo 0 (Real.pi / 2))) : IntegrableOn f Work.Spaces.Iθ := by
  show Integrable f (volume.restrict Work.Spaces.Iθ)
  rw [Work.FTS.EllipticEst.Cores.restrict_Iθ_eq_Ioo]
  exact h

theorem sliceAgmonVanishing (α : ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : ℝ → ℝ),
      ContDiffOn ℝ 2 u (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      Filter.Tendsto u (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
      Filter.Tendsto u (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv u θ) ^ 2 *
        (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (u θ) ^ 2 *
        (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv u) θ) ^ 2 *
        (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv u θ) ^ 2 *
          (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
        ≤ C * Real.sqrt ((∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (u θ) ^ 2 *
              (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
            * (∫ θ in Set.Ioo (0 : ℝ) (Real.pi / 2), (deriv (deriv u) θ) ^ 2 *
              (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))) := by
  have hα1 : α ≤ 1 := by linarith
  have ha0 : 0 < 2 - Work.Spaces.gam α := Work.FTS.EllipticEst.Cores.sub_gam_pos hα1
  have ha1 : 2 - Work.Spaces.gam α < 1 := Work.FTS.EllipticEst.Cores.sub_gam_lt_one hα
  have hane : 2 - Work.Spaces.gam α ≠ 0 := ne_of_gt ha0
  obtain ⟨C, hC, hmain⟩ := Work.FTS.EllipticEst.Cores.sliceInterpVanishing α hα hα4
  refine ⟨C, hC, fun u hcd h0 h1 hL hB hD => ?_⟩
  -- the three hypotheses in the `sigA` spelling
  have hL' : IntegrableOn (fun θ : ℝ => (deriv u θ) ^ 2 * sigA α θ)
      (Set.Ioo 0 (Real.pi / 2)) := hL
  have hB' : IntegrableOn (fun θ : ℝ => (u θ) ^ 2 * sigA α θ)
      (Set.Ioo 0 (Real.pi / 2)) := hB
  have hD' : IntegrableOn (fun θ : ℝ => (deriv (deriv u) θ) ^ 2 * sigA α θ)
      (Set.Ioo 0 (Real.pi / 2)) := hD
  -- nonnegativity of the weight on the open interval
  have hσp : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < sigA α θ :=
    fun θ hθ => Work.FTS.EllipticEst.Cores.sigA_pos' hθ
  have hσn : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 ≤ sigA α θ :=
    fun θ hθ => (hσp θ hθ).le
  -- ## endpoint control
  obtain ⟨M, hMpos, hMbd⟩ := exists_deriv_abs_bound hα hα1 hcd hD'
  have hMnn : 0 ≤ M := hMpos.le
  have hσinv : IntegrableOn (fun θ : ℝ => (sigA α θ)⁻¹) (Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.Cores.integrableOn_sigA_inv hα hα1).mono_set Ioo_subset_Icc_self
  have hintd : IntegrableOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Cores.integrableOn_deriv measurableSet_Ioo (fun _ hx => hx) hL' hσinv
  have hvalL := value_abs_le_mul_left hcd hintd h0 hMnn hMbd
  have hvalR := value_abs_le_mul_right hcd hintd h1 hMnn hMbd
  -- ## `|u| ≤ M sin 2θ`
  have huS : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |u θ| ≤ M * Real.sin (2 * θ) := by
    intro θ hθ
    have hSnn : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
        (by linarith [hθ.2, Real.pi_pos])
    rcases le_or_gt θ (Real.pi / 4) with hle | hlt
    · have hge : (4 / Real.pi) * θ ≤ Real.sin (2 * θ) := by
        have h := Real.mul_le_sin (x := 2 * θ) (by linarith [hθ.1])
          (by linarith [hle, Real.pi_pos])
        rwa [show (2 : ℝ) / Real.pi * (2 * θ) = (4 / Real.pi) * θ by ring] at h
      have hge' : θ ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
        have h1 : (Real.pi / 4) * ((4 / Real.pi) * θ) ≤ (Real.pi / 4) * Real.sin (2 * θ) :=
          mul_le_mul_of_nonneg_left hge (by positivity)
        rwa [show (Real.pi / 4) * ((4 / Real.pi) * θ) = θ by field_simp] at h1
      calc |u θ| ≤ M * θ := hvalL θ hθ
        _ ≤ M * ((Real.pi / 4) * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hge' hMnn
        _ ≤ M * Real.sin (2 * θ) :=
            mul_le_mul_of_nonneg_left (by nlinarith [hSnn, Real.pi_lt_four]) hMnn
    · have hge : (4 / Real.pi) * (Real.pi / 2 - θ)
          ≤ Real.sin (2 * (Real.pi / 2 - θ)) := by
        have h := Real.mul_le_sin (x := 2 * (Real.pi / 2 - θ)) (by linarith [hθ.2])
          (by linarith [hlt, Real.pi_pos])
        rwa [show (2 : ℝ) / Real.pi * (2 * (Real.pi / 2 - θ))
          = (4 / Real.pi) * (Real.pi / 2 - θ) by ring] at h
      have h2θ : Real.sin (2 * (Real.pi / 2 - θ)) = Real.sin (2 * θ) := by
        rw [show 2 * (Real.pi / 2 - θ) = Real.pi - 2 * θ by ring, Real.sin_pi_sub]
      rw [h2θ] at hge
      have hge' : Real.pi / 2 - θ ≤ (Real.pi / 4) * Real.sin (2 * θ) := by
        have h1 : (Real.pi / 4) * ((4 / Real.pi) * (Real.pi / 2 - θ))
            ≤ (Real.pi / 4) * Real.sin (2 * θ) := mul_le_mul_of_nonneg_left hge (by positivity)
        rwa [show (Real.pi / 4) * ((4 / Real.pi) * (Real.pi / 2 - θ)) = Real.pi / 2 - θ from by
          field_simp] at h1
      calc |u θ| ≤ M * (Real.pi / 2 - θ) := hvalR θ hθ
        _ ≤ M * ((Real.pi / 4) * Real.sin (2 * θ)) := mul_le_mul_of_nonneg_left hge' hMnn
        _ ≤ M * Real.sin (2 * θ) :=
            mul_le_mul_of_nonneg_left (by nlinarith [hSnn, Real.pi_lt_four]) hMnn
  -- ## the two boundary products tend to zero
  have hb1 : Tendsto (fun t : ℝ => u t * deriv u t * sigA α t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine tendsto_zero_of_abs_le_eventually (A := M * M * 2 ^ (2 - Work.Spaces.gam α))
      (e := 1 + (2 - Work.Spaces.gam α)) (ε := Real.pi / 4)
      (by linarith) (by linarith [Real.pi_pos]) ?_
    intro y hy
    have hyO : y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
    have hSnn : 0 ≤ Real.sin (2 * y) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hy.1])
        (by linarith [hy.2, Real.pi_pos])
    have hSle : Real.sin (2 * y) ≤ 2 * y := Real.sin_le (by linarith [hy.1])
    have hσle : |sigA α y| ≤ (2 * y) ^ (2 - Work.Spaces.gam α) := by
      rw [abs_of_nonneg (hσn y hyO)]
      exact Real.rpow_le_rpow hSnn hSle ha0.le
    calc |u y * deriv u y * sigA α y|
        = |u y| * |deriv u y| * |sigA α y| := by rw [abs_mul, abs_mul]
      _ ≤ (M * y) * M * (2 * y) ^ (2 - Work.Spaces.gam α) :=
          mul_le_mul (mul_le_mul (hvalL y hyO) (hMbd y hyO) (abs_nonneg _)
              (mul_nonneg hMnn hy.1.le))
            hσle (abs_nonneg _) (mul_nonneg (mul_nonneg hMnn hy.1.le) hMnn)
      _ = M * M * 2 ^ (2 - Work.Spaces.gam α)
            * (y * y ^ (2 - Work.Spaces.gam α)) := by
          rw [Real.mul_rpow (by norm_num) (by linarith [hy.1])]
          ring
      _ = M * M * 2 ^ (2 - Work.Spaces.gam α)
            * y ^ (1 + (2 - Work.Spaces.gam α)) := by
          rw [rpow_one_add (by linarith [hy.1])]
  have hb2 : Tendsto (fun t : ℝ => u t * deriv u t * sigA α t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    refine tendsto_zero_of_abs_le_eventually_right (A := M * M * 2 ^ (2 - Work.Spaces.gam α))
      (e := 1 + (2 - Work.Spaces.gam α)) (ε := Real.pi / 4)
      (by linarith) (by linarith [Real.pi_pos]) ?_
    intro y hy
    have hyO : Real.pi / 2 - y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hy.2, Real.pi_pos], by linarith [hy.1]⟩
    have hσref : sigA α (Real.pi / 2 - y) = sigA α y :=
      Work.FTS.EllipticEst.Cores.sigA_reflect
    have hSnn : 0 ≤ Real.sin (2 * y) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hy.1]) (by linarith [hy.2, Real.pi_pos])
    have hSle : Real.sin (2 * y) ≤ 2 * y := Real.sin_le (by linarith [hy.1])
    have hσle : |sigA α y| ≤ (2 * y) ^ (2 - Work.Spaces.gam α) := by
      rw [abs_of_nonneg (hσn y ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩)]
      exact Real.rpow_le_rpow hSnn hSle ha0.le
    have hu : |u (Real.pi / 2 - y)| ≤ M * y := by
      have h := hvalR (Real.pi / 2 - y) hyO
      rwa [show Real.pi / 2 - (Real.pi / 2 - y) = y by ring] at h
    calc |u (Real.pi / 2 - y) * deriv u (Real.pi / 2 - y) * sigA α (Real.pi / 2 - y)|
        = |u (Real.pi / 2 - y)| * |deriv u (Real.pi / 2 - y)| * |sigA α (Real.pi / 2 - y)| := by
          rw [abs_mul, abs_mul]
      _ = |u (Real.pi / 2 - y)| * |deriv u (Real.pi / 2 - y)| * |sigA α y| := by rw [hσref]
      _ ≤ (M * y) * M * (2 * y) ^ (2 - Work.Spaces.gam α) :=
          mul_le_mul (mul_le_mul hu (hMbd (Real.pi / 2 - y) hyO) (abs_nonneg _)
              (mul_nonneg hMnn hy.1.le))
            hσle (abs_nonneg _) (mul_nonneg (mul_nonneg hMnn hy.1.le) hMnn)
      _ = M * M * 2 ^ (2 - Work.Spaces.gam α)
            * (y * y ^ (2 - Work.Spaces.gam α)) := by
          rw [Real.mul_rpow (by norm_num) (by linarith [hy.1])]
          ring
      _ = M * M * 2 ^ (2 - Work.Spaces.gam α)
            * y ^ (1 + (2 - Work.Spaces.gam α)) := by
          rw [rpow_one_add (by linarith [hy.1])]
  have hb3 : Tendsto (fun t : ℝ => (u t) ^ 2 * sigDR (2 - Work.Spaces.gam α) t)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    refine tendsto_zero_of_abs_le_eventually
      (A := M * M * (2 * (2 - Work.Spaces.gam α)) * (4 / Real.pi) ^ ((2 - Work.Spaces.gam α) - 1))
      (e := 1 + (2 - Work.Spaces.gam α)) (ε := Real.pi / 4)
      (by linarith) (by linarith [Real.pi_pos]) ?_
    intro y hy
    have hyO : y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hy.1, by linarith [hy.2, Real.pi_pos]⟩
    have hSp : 0 < Real.sin (2 * y) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hy.1]) (by linarith [hy.2, Real.pi_pos])
    have hge : (4 / Real.pi) * y ≤ Real.sin (2 * y) := by
      have h := Real.mul_le_sin (x := 2 * y) (by linarith [hy.1]) (by linarith [hy.2, Real.pi_pos])
      rwa [show (2 : ℝ) / Real.pi * (2 * y) = (4 / Real.pi) * y by ring] at h
    have hspow : Real.sin (2 * y) ^ ((2 - Work.Spaces.gam α) - 1)
        ≤ ((4 / Real.pi) * y) ^ ((2 - Work.Spaces.gam α) - 1) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos (by positivity) hy.1) hge (by linarith [ha1])
    have hdr : |sigDR (2 - Work.Spaces.gam α) y|
        ≤ 2 * (2 - Work.Spaces.gam α) * ((4 / Real.pi) * y) ^ ((2 - Work.Spaces.gam α) - 1) := by
      rw [Work.FTS.EllipticEst.TT.sigDR_apply, abs_mul, abs_mul]
      rw [abs_of_pos (by linarith [ha0]), abs_of_nonneg (Real.rpow_nonneg hSp.le _)]
      have hc : |Real.cos (2 * y)| ≤ 1 := Real.abs_cos_le_one _
      have h2 : 2 * (2 - Work.Spaces.gam α) * |Real.cos (2 * y)|
          ≤ 2 * (2 - Work.Spaces.gam α) * 1 :=
        mul_le_mul_of_nonneg_left hc (by linarith [ha0])
      have h3 := mul_le_mul_of_nonneg_right h2
        (Real.rpow_nonneg hSp.le ((2 - Work.Spaces.gam α) - 1))
      have h4 := mul_le_mul_of_nonneg_left hspow
        (show (0 : ℝ) ≤ 2 * (2 - Work.Spaces.gam α) by linarith [ha0])
      linarith [h3, h4]
    have hc2 : Real.cos (2 * y) ^ 2 ≤ 1 := by
      have h1 : |Real.cos (2 * y)| ≤ 1 := Real.abs_cos_le_one _
      have h2 : |Real.cos (2 * y)| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rwa [sq_abs, one_pow] at h2
    have hu2 : (u y) ^ 2 ≤ (M * y) ^ 2 := by
      have h0' : (0 : ℝ) ≤ |u y| := abs_nonneg _
      calc (u y) ^ 2 = |u y| ^ 2 := (sq_abs (u y)).symm
        _ ≤ (M * y) ^ 2 := pow_le_pow_left₀ h0' (hvalL y hyO) 2
    calc |(u y) ^ 2 * sigDR (2 - Work.Spaces.gam α) y|
        = (u y) ^ 2 * |sigDR (2 - Work.Spaces.gam α) y| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (u y))]
      _ ≤ (M * y) ^ 2 * (2 * (2 - Work.Spaces.gam α)
            * ((4 / Real.pi) * y) ^ ((2 - Work.Spaces.gam α) - 1)) :=
          mul_le_mul hu2 hdr (abs_nonneg _) (sq_nonneg _)
      _ = M * M * (2 * (2 - Work.Spaces.gam α)) * (4 / Real.pi) ^ ((2 - Work.Spaces.gam α) - 1)
            * (y ^ 2 * y ^ ((2 - Work.Spaces.gam α) - 1)) := by
          rw [Real.mul_rpow (by positivity) (by linarith [hy.1])]
          ring
      _ = M * M * (2 * (2 - Work.Spaces.gam α)) * (4 / Real.pi) ^ ((2 - Work.Spaces.gam α) - 1)
            * y ^ (1 + (2 - Work.Spaces.gam α)) := by
          rw [sq_mul_rpow_sub_one (by linarith [hy.1])]
  have hb4 : Tendsto (fun t : ℝ => (u t) ^ 2 * sigDR (2 - Work.Spaces.gam α) t)
      (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
    refine tendsto_zero_of_abs_le_eventually_right
      (A := M * M * (2 * (2 - Work.Spaces.gam α)) * (4 / Real.pi) ^ ((2 - Work.Spaces.gam α) - 1))
      (e := 1 + (2 - Work.Spaces.gam α)) (ε := Real.pi / 4)
      (by linarith) (by linarith [Real.pi_pos]) ?_
    intro y hy
    have hyO : Real.pi / 2 - y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) :=
      ⟨by linarith [hy.2, Real.pi_pos], by linarith [hy.1]⟩
    have hSp : 0 < Real.sin (2 * y) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hy.1]) (by linarith [hy.2, Real.pi_pos])
    have hge : (4 / Real.pi) * y ≤ Real.sin (2 * y) := by
      have h := Real.mul_le_sin (x := 2 * y) (by linarith [hy.1]) (by linarith [hy.2, Real.pi_pos])
      rwa [show (2 : ℝ) / Real.pi * (2 * y) = (4 / Real.pi) * y by ring] at h
    have hspow : Real.sin (2 * y) ^ ((2 - Work.Spaces.gam α) - 1)
        ≤ ((4 / Real.pi) * y) ^ ((2 - Work.Spaces.gam α) - 1) :=
      Real.rpow_le_rpow_of_nonpos (mul_pos (by positivity) hy.1) hge (by linarith [ha1])
    have hdr : |sigDR (2 - Work.Spaces.gam α) (Real.pi / 2 - y)|
        ≤ 2 * (2 - Work.Spaces.gam α) * ((4 / Real.pi) * y) ^ ((2 - Work.Spaces.gam α) - 1) := by
      rw [Work.FTS.EllipticEst.TT.sigDR_apply]
      rw [show 2 * (Real.pi / 2 - y) = Real.pi - 2 * y by ring, Real.cos_pi_sub, Real.sin_pi_sub]
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by linarith [ha0]),
        abs_of_nonneg (Real.rpow_nonneg hSp.le _)]
      have hc : |Real.cos (2 * y)| ≤ 1 := Real.abs_cos_le_one _
      have h2 : 2 * (2 - Work.Spaces.gam α) * |Real.cos (2 * y)|
          ≤ 2 * (2 - Work.Spaces.gam α) * 1 :=
        mul_le_mul_of_nonneg_left hc (by linarith [ha0])
      have h3 := mul_le_mul_of_nonneg_right h2
        (Real.rpow_nonneg hSp.le ((2 - Work.Spaces.gam α) - 1))
      have h4 := mul_le_mul_of_nonneg_left hspow
        (show (0 : ℝ) ≤ 2 * (2 - Work.Spaces.gam α) by linarith [ha0])
      linarith [h3, h4]
    have huS' : |u (Real.pi / 2 - y)| ≤ M * y := by
      have h := hvalR (Real.pi / 2 - y) hyO
      rwa [show Real.pi / 2 - (Real.pi / 2 - y) = y by ring] at h
    have hu2 : (u (Real.pi / 2 - y)) ^ 2 ≤ (M * y) ^ 2 := by
      have h0' : (0 : ℝ) ≤ |u (Real.pi / 2 - y)| := abs_nonneg _
      calc (u (Real.pi / 2 - y)) ^ 2 = |u (Real.pi / 2 - y)| ^ 2 :=
            (sq_abs (u (Real.pi / 2 - y))).symm
        _ ≤ (M * y) ^ 2 := pow_le_pow_left₀ h0' huS' 2
    calc |(u (Real.pi / 2 - y)) ^ 2 * sigDR (2 - Work.Spaces.gam α) (Real.pi / 2 - y)|
        = (u (Real.pi / 2 - y)) ^ 2 * |sigDR (2 - Work.Spaces.gam α) (Real.pi / 2 - y)| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (u (Real.pi / 2 - y)))]
      _ ≤ (M * y) ^ 2 * (2 * (2 - Work.Spaces.gam α)
            * ((4 / Real.pi) * y) ^ ((2 - Work.Spaces.gam α) - 1)) :=
          mul_le_mul hu2 hdr (abs_nonneg _) (sq_nonneg _)
      _ = M * M * (2 * (2 - Work.Spaces.gam α)) * (4 / Real.pi) ^ ((2 - Work.Spaces.gam α) - 1)
            * (y ^ 2 * y ^ ((2 - Work.Spaces.gam α) - 1)) := by
          rw [Real.mul_rpow (by positivity) (by linarith [hy.1])]
          ring
      _ = M * M * (2 * (2 - Work.Spaces.gam α)) * (4 / Real.pi) ^ ((2 - Work.Spaces.gam α) - 1)
            * y ^ (1 + (2 - Work.Spaces.gam α)) := by
          rw [sq_mul_rpow_sub_one (by linarith [hy.1])]
  -- ## the remaining integrability clauses
  have hddcont : ContinuousOn (deriv (deriv u)) (Set.Ioo 0 (Real.pi / 2)) :=
    (((hcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).deriv_of_isOpen isOpen_Ioo
      (m := 0) (by norm_num))).continuousOn
  have hducont : ContinuousOn (deriv u) (Set.Ioo 0 (Real.pi / 2)) :=
    (hcd.deriv_of_isOpen isOpen_Ioo (m := 1) (by norm_num)).continuousOn
  have hσcont : ContinuousOn (fun θ : ℝ => sigA α θ) (Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.Cores.sigA_continuous α hα1).continuousOn
  have hsigDRcont : ContinuousOn (fun θ : ℝ => sigDR (2 - Work.Spaces.gam α) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    have hcos : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
    have hp : ContinuousOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 1))
        (Set.Ioo 0 (Real.pi / 2)) :=
      hsin.rpow_const (fun x hx => Or.inl (ne_of_gt
        (Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hx)))
    have hcont : ContinuousOn (fun θ : ℝ => (2 * (2 - Work.Spaces.gam α)) * Real.cos (2 * θ)
        * (Real.sin (2 * θ)) ^ ((2 - Work.Spaces.gam α) - 1)) (Set.Ioo 0 (Real.pi / 2)) :=
      (continuousOn_const.mul hcos).mul hp
    refine hcont.congr ?_
    intro x hx
    simp only [Work.FTS.EllipticEst.TT.sigDR_apply]
  have hσint : IntegrableOn (fun θ : ℝ => sigA α θ) (Set.Ioo 0 (Real.pi / 2)) :=
    ((Work.FTS.EllipticEst.Cores.sigA_continuous α hα1).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  -- `u u'' σ`
  have hI2 : IntegrableOn (fun θ : ℝ => u θ * deriv (deriv u) θ * sigA α θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    refine MeasureTheory.Integrable.mono' (hB'.add hD') ?_ ?_
    · exact ((hcd.continuousOn.mul hddcont).mul hσcont).aestronglyMeasurable measurableSet_Ioo
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hσnn : 0 ≤ sigA α θ := le_of_lt (Work.FTS.EllipticEst.Cores.sigA_pos' hθ)
      have h2 : 2 * |u θ| * |deriv (deriv u) θ| ≤ (u θ) ^ 2 + (deriv (deriv u) θ) ^ 2 := by
        have h := two_mul_le_add_sq (|u θ|) (|deriv (deriv u) θ|)
        rwa [sq_abs, sq_abs] at h
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hσnn]
      have hhalf : |u θ| * |deriv (deriv u) θ| * sigA α θ
          ≤ ((u θ) ^ 2 + (deriv (deriv u) θ) ^ 2) * sigA α θ := by
        have h := mul_le_mul_of_nonneg_right h2 hσnn
        have hY : 0 ≤ ((u θ) ^ 2 + (deriv (deriv u) θ) ^ 2) * sigA α θ :=
          mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) hσnn
        linarith [h, hY]
      have hexp : ((u θ) ^ 2 + (deriv (deriv u) θ) ^ 2) * sigA α θ
          = (u θ) ^ 2 * sigA α θ + (deriv (deriv u) θ) ^ 2 * sigA α θ := by ring
      rw [hexp] at hhalf
      exact hhalf
  -- `u u' σ'`
  have hI3 : IntegrableOn (fun θ : ℝ => u θ * deriv u θ * sigDR (2 - Work.Spaces.gam α) θ)
      (Set.Ioo 0 (Real.pi / 2)) := by
    have hdom := hσint.const_mul (M * M * (2 * (2 - Work.Spaces.gam α)))
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · exact ((hcd.continuousOn.mul hducont).mul hsigDRcont).aestronglyMeasurable measurableSet_Ioo
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hSp : 0 < Real.sin (2 * θ) :=
        Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hθ
      have h3 : |sigDR (2 - Work.Spaces.gam α) θ|
          ≤ 2 * (2 - Work.Spaces.gam α) * Real.sin (2 * θ) ^ ((2 - Work.Spaces.gam α) - 1) := by
        rw [Work.FTS.EllipticEst.TT.sigDR_apply, abs_mul, abs_mul,
          abs_of_pos (by linarith [ha0]), abs_of_nonneg (Real.rpow_nonneg hSp.le _)]
        have hc : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
        have h2 : 2 * (2 - Work.Spaces.gam α) * |Real.cos (2 * θ)|
            ≤ 2 * (2 - Work.Spaces.gam α) * 1 :=
          mul_le_mul_of_nonneg_left hc (by linarith [ha0])
        have hA := mul_le_mul_of_nonneg_right h2
          (Real.rpow_nonneg hSp.le ((2 - Work.Spaces.gam α) - 1))
        linarith [hA]
      have h4 : Real.sin (2 * θ) * Real.sin (2 * θ) ^ ((2 - Work.Spaces.gam α) - 1)
          = sigA α θ := by
        rw [mul_rpow_sub_one hSp hane]
        rfl
      calc |u θ * deriv u θ * sigDR (2 - Work.Spaces.gam α) θ|
          = |u θ| * |deriv u θ| * |sigDR (2 - Work.Spaces.gam α) θ| := by rw [abs_mul, abs_mul]
        _ ≤ (M * Real.sin (2 * θ)) * M
              * (2 * (2 - Work.Spaces.gam α) * Real.sin (2 * θ) ^ ((2 - Work.Spaces.gam α) - 1)) :=
            mul_le_mul (mul_le_mul (huS θ hθ) (hMbd θ hθ) (abs_nonneg _)
                (mul_nonneg hMnn (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
                  (by linarith [hθ.2, Real.pi_pos]))))
              h3 (abs_nonneg _)
              (mul_nonneg (mul_nonneg hMnn (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith [hθ.1])
                (by linarith [hθ.2, Real.pi_pos]))) hMnn)
        _ = M * M * (2 * (2 - Work.Spaces.gam α))
              * (Real.sin (2 * θ) * Real.sin (2 * θ) ^ ((2 - Work.Spaces.gam α) - 1)) := by ring
        _ = M * M * (2 * (2 - Work.Spaces.gam α)) * sigA α θ := by rw [h4]
  -- `u² cos²(2θ) sin(2θ)^{a-2}`
  have hI5 : IntegrableOn (fun θ : ℝ => (u θ) ^ 2 * Real.cos (2 * θ) ^ 2
      * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α - 2)) (Set.Ioo 0 (Real.pi / 2)) := by
    have hcos2 : ContinuousOn (fun θ : ℝ => Real.cos (2 * θ) ^ 2) (Set.Ioo 0 (Real.pi / 2)) :=
      ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn).pow 2
    have hsin2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α - 2))
        (Set.Ioo 0 (Real.pi / 2)) := by
      have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
        (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
      exact hsin.rpow_const (fun x hx => Or.inl (ne_of_gt
        (Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hx)))
    have hdom := hσint.const_mul (M * M)
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · exact (((hcd.continuousOn.pow 2).mul hcos2).mul hsin2).aestronglyMeasurable measurableSet_Ioo
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo (fun θ hθ => ?_)
      have hSp : 0 < Real.sin (2 * θ) :=
        Work.FTS.EllipticEst.TT.sin_two_pos_of_mem_Ioo hθ
      have hSpow : 0 ≤ Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α - 2) :=
        Real.rpow_nonneg hSp.le _
      have hc2 : Real.cos (2 * θ) ^ 2 ≤ 1 := by
        have h1 : |Real.cos (2 * θ)| ≤ 1 := Real.abs_cos_le_one _
        have h2 : |Real.cos (2 * θ)| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
        rwa [sq_abs, one_pow] at h2
      have hu2 : (u θ) ^ 2 ≤ (M * Real.sin (2 * θ)) ^ 2 := by
        have h0' : (0 : ℝ) ≤ |u θ| := abs_nonneg _
        calc (u θ) ^ 2 = |u θ| ^ 2 := (sq_abs (u θ)).symm
          _ ≤ (M * Real.sin (2 * θ)) ^ 2 := pow_le_pow_left₀ h0' (huS θ hθ) 2
      have h5 : (M * Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) ^ 2
          * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α - 2) ≤ M * M * sigA α θ := by
        have hstep : (M * Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) ^ 2
            * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α - 2)
            ≤ M * M * (Real.sin (2 * θ) ^ 2
              * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α - 2)) := by
          calc (M * Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) ^ 2
                * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α - 2)
              = ((M * Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) ^ 2)
                  * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α - 2) := by ring
            _ ≤ ((M * Real.sin (2 * θ)) ^ 2 * 1) * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α - 2) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc2 (sq_nonneg _)) hSpow
            _ = M * M * (Real.sin (2 * θ) ^ 2
                  * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α - 2)) := by ring
        rw [mul_rpow_sub_two hSp] at hstep
        exact hstep
      have hnn : 0 ≤ (u θ) ^ 2 * Real.cos (2 * θ) ^ 2
          * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α - 2) :=
        mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hSpow
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      calc (u θ) ^ 2 * Real.cos (2 * θ) ^ 2 * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α - 2)
          = (u θ) ^ 2 * (Real.cos (2 * θ) ^ 2
              * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α - 2)) := by ring
        _ ≤ (M * Real.sin (2 * θ)) ^ 2 * (Real.cos (2 * θ) ^ 2
              * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α - 2)) :=
            mul_le_mul_of_nonneg_right hu2 (mul_nonneg (sq_nonneg _) hSpow)
        _ = (M * Real.sin (2 * θ)) ^ 2 * Real.cos (2 * θ) ^ 2
              * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α - 2) := by ring
        _ ≤ M * M * sigA α θ := h5
  -- ## assembly
  have hkey := hmain u hcd (integrableOn_Iθ_of_Ioo hL') (integrableOn_Iθ_of_Ioo hI2)
    (integrableOn_Iθ_of_Ioo hI3) (integrableOn_Iθ_of_Ioo hB') (integrableOn_Iθ_of_Ioo hI5)
    (integrableOn_Iθ_of_Ioo hD') hb1 hb2 hb3 hb4
  rw [← Work.FTS.EllipticEst.Cores.restrict_Iθ_eq_Ioo]
  simpa only [Work.FTS.EllipticEst.TT.sigA, Work.FTS.EllipticEst.Cores.sigA] using hkey

end

end Work.FTS.EllipticEst.Cores.InterpGammaCore.InterpJumpAux
