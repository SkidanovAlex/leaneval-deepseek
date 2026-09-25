import Mathlib
import Submission.Work.BourgainPlan.Maximal.mst_lvl_defs
import Submission.Work.BourgainPlan.Maximal.mikhlin_conditions_scaled_bump
import Submission.Work.BourgainPlan.Maximal.mikhlin_multiplier_lift
import Submission.Work.BourgainPlan.Maximal.iwMult_mul
import Submission.Work.BourgainPlan.Maximal.iw_superset
import Submission.Work.BourgainPlan.Maximal.iw_superset_bound
import Submission.Work.BourgainPlan.Maximal.iwRangeBound_of_endpoint
import Submission.Work.BourgainPlan.Maximal.mstEta_support
import Submission.Work.BourgainPlan.Maximal.contDiff_polyProfile
import Submission.Work.BourgainPlan.Maximal.memLp_mst_symbols
import Submission.Work.BourgainPlan.Maximal.profileMikhlinBandGe

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset Filter
open scoped BigOperators ENNReal Topology
open Work.BourgainPlan.IonescuWainger
open Work.BourgainPlan.Thm52

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

local notation "haarT" => (AddCircle.haarAddCircle (T := 1))
local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- The strict support hypothesis upgrades to the closed one. -/
lemma eta_zero_of_half_le_abs {η : ℝ → ℂ} (hηc : ContDiff ℝ 2 η)
    (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0 := by
  intro x hx
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact hη0 x hlt
  · have hx2 : x = 1 / 2 ∨ x = -(1 / 2) := (abs_eq (by norm_num)).mp heq.symm
    rcases hx2 with h | h
    · rw [h]
      have hev : η =ᶠ[𝓝[>] (1 / 2)] fun _ : ℝ => (0 : ℂ) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact hη0 y (by rw [abs_of_pos (by linarith [Set.mem_Ioi.mp hy] : (0 : ℝ) < y)]; exact hy)
      have h1 : Filter.Tendsto η (𝓝[>] (1 / 2)) (𝓝 (η (1 / 2))) :=
        hηc.continuous.continuousAt.mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto η (𝓝[>] (1 / 2)) (𝓝 0) :=
        Filter.Tendsto.congr' hev.symm tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2
    · rw [h]
      have hev : η =ᶠ[𝓝[<] (-(1 / 2))] fun _ : ℝ => (0 : ℂ) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact hη0 y (by rw [abs_of_neg (by linarith [Set.mem_Iio.mp hy] : y < 0)]; linarith [Set.mem_Iio.mp hy])
      have h1 : Filter.Tendsto η (𝓝[<] (-(1 / 2))) (𝓝 (η (-(1 / 2)))) :=
        hηc.continuous.continuousAt.mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto η (𝓝[<] (-(1 / 2))) (𝓝 0) :=
        Filter.Tendsto.congr' hev.symm tendsto_const_nhds
      exact tendsto_nhds_unique h1 h2

/-- The derivative of the bump vanishes on the closed complement of `(-1/2, 1/2)`. -/
lemma deriv_eta_zero_of_half_le_abs {η : ℝ → ℂ} (hηc : ContDiff ℝ 2 η)
    (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0) :
    ∀ x : ℝ, 1 / 2 ≤ |x| → deriv η x = 0 := by
  have hcont : Continuous (deriv η) := hηc.continuous_deriv (by norm_num)
  have hderiv_open : ∀ y : ℝ, 1 / 2 < |y| → deriv η y = 0 := by
    intro y hy
    have hev : η =ᶠ[𝓝 y] fun _ : ℝ => (0 : ℂ) := by
      filter_upwards [(isOpen_lt continuous_const continuous_abs).mem_nhds hy] with z hz
      exact hη0 z hz
    rw [hev.deriv_eq]
    simp
  intro x hx
  rcases lt_or_eq_of_le hx with hlt | heq
  · exact hderiv_open x hlt
  · have hx2 : x = 1 / 2 ∨ x = -(1 / 2) := (abs_eq (by norm_num)).mp heq.symm
    rcases hx2 with h | h
    · rw [h]
      have hev : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝[>] (1 / 2)] deriv η := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hyabs : (1 : ℝ) / 2 < |y| := by
          rw [abs_of_pos (by linarith [Set.mem_Ioi.mp hy] : (0 : ℝ) < y)]
          exact Set.mem_Ioi.mp hy
        exact (hderiv_open y hyabs).symm
      have h1 : Filter.Tendsto (deriv η) (𝓝[>] (1 / 2)) (𝓝 (deriv η (1 / 2))) :=
        hcont.continuousAt.mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto (deriv η) (𝓝[>] (1 / 2)) (𝓝 0) :=
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝[>] (1 / 2))
          (𝓝 0)).congr' hev
      exact tendsto_nhds_unique h1 h2
    · rw [h]
      have hev : (fun _ : ℝ => (0 : ℂ)) =ᶠ[𝓝[<] (-(1 / 2))] deriv η := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hyabs : (1 : ℝ) / 2 < |y| := by
          rw [abs_of_neg (by linarith [Set.mem_Iio.mp hy] : y < 0)]
          linarith [Set.mem_Iio.mp hy]
        exact (hderiv_open y hyabs).symm
      have h1 : Filter.Tendsto (deriv η) (𝓝[<] (-(1 / 2))) (𝓝 (deriv η (-(1 / 2)))) :=
        hcont.continuousAt.mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto (deriv η) (𝓝[<] (-(1 / 2))) (𝓝 0) :=
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝[<] (-(1 / 2)))
          (𝓝 0)).congr' hev
      exact tendsto_nhds_unique h1 h2


/-- The canonical representative of `-x` for `x` in the (half-open) fundamental domain. -/
lemma iwRep_neg_coe {x : ℝ} (hx : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)) (hlt : x < 1 / 2) :
    iwRep (-(x : Circ)) = -x := by
  have hmem : -x ∈ Set.Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1) :=
    ⟨by linarith [hx.1], by linarith [hx.1]⟩
  rw [← AddCircle.coe_neg (1 : ℝ) (x := x), iwRep]
  exact AddCircle.liftIoc_coe_apply hmem

/-- **The lift of the base symbol `star (Φ_1) · η_s` is an explicit function of `x`.**  On the
fundamental domain the profile `star (Φ_1)` contributes `star (polyProfile P 1 (-x))` and the bump
`η_s` contributes `η (-(c_s x))`, with `c_s = mstScale d χ s ≥ 1`; off the fundamental domain both
sides vanish (the rescaled bump is already supported in `[-1/(2c_s), 1/(2c_s)] ⊂ (-1/2, 1/2)`). -/
lemma circleLift_mstPiBump_one (P : Polynomial ℤ) (d : ℕ) (χ : ℝ) (η : ℝ → ℂ) (s : ℕ)
    (hsupp : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (hc1 : 1 ≤ mstScale d χ s) :
    Work.BourgainPlan.Thm52.circleLift (mstPiBump P d χ η 1 s)
      = fun x : ℝ => star (polyProfile P 1 (-x)) * η (-(mstScale d χ s * x)) := by
  have hcs0 : 0 < mstScale d χ s := lt_of_lt_of_le one_pos hc1
  have hcabs : 1 ≤ |mstScale d χ s| := by
    rw [abs_of_pos hcs0]; exact hc1
  have hE : Work.BourgainPlan.Thm52.circleLift (mstEta d χ η s)
      = fun x : ℝ => η (-(mstScale d χ s * x)) := by
    have h := circleLift_scaled_bump_eq (η := η) (c := mstScale d χ s) hcabs hsupp
    have hme : mstEta d χ η s = (fun ξ : Circ => η (mstScale d χ s * iwRep ξ)) := by
      funext ξ; simp only [mstEta, mstScale]
    rw [hme]
    simpa only [mul_neg] using h
  have hcpos : 0 < mstScale d χ s := hcs0
  rw [mstPiBump, show mstStarProf P 1 * mstEta d χ η s
      = (fun ξ : Circ => mstStarProf P 1 ξ * mstEta d χ η s ξ) from rfl, circleLift_mul, hE]
  funext x
  by_cases hx : x ∈ Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)
  · rcases lt_or_eq_of_le hx.2 with hlt | heq
    · simp only [circleLift_of_mem hx, mstStarProf_apply, mstProf_apply, iwRep_neg_coe hx hlt]
    · subst heq
      have hz : η (-(mstScale d χ s * (1 / 2))) = 0 := by
        refine hsupp _ ?_
        rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_pos hcpos]
        linarith
      simp only [circleLift_of_mem hx, hz, mul_zero, star_mul]
  · have hxabs : (1 : ℝ) / 2 ≤ |x| := by
      have hxor : x ≤ -(1 / 2 : ℝ) ∨ (1 / 2 : ℝ) < x := by
        by_contra h
        rw [not_or, not_le, not_lt] at h
        exact hx ⟨h.1, h.2⟩
      rcases hxor with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hz : η (-(mstScale d χ s * x)) = 0 := by
      refine hsupp _ ?_
      rw [abs_neg, abs_mul, abs_of_pos hcpos]
      calc (1 : ℝ) / 2 ≤ |x| := hxabs
        _ = 1 * |x| := (one_mul _).symm
        _ ≤ mstScale d χ s * |x| := mul_le_mul_of_nonneg_right hc1 (abs_nonneg x)
    simp only [circleLift_of_notMem hx, zero_mul, hz, mul_zero]

/-- **The Mikhlin conditions of the base symbol's lift.**  For the symbol
`star (Φ_1) · η_s` (MST's base term of the level-`s` Rademacher–Menshov reduction) the
fundamental-domain lift is `x ↦ star (polyProfile P 1 (-x)) · η (-(c_s x))`, which is `C²` and
satisfies the Mikhlin bounds with a constant `A` depending only on `M` and on the polynomial `P`
(`‖·‖ ≤ M`, `|x|‖(·)'‖ ≤ A`, `|x|²‖(·)''‖ ≤ A`): the bump factor vanishes, together with its
first derivative, off `[-1/(2c_s), 1/(2c_s)]`, where the scaling identity `|x| c_s = |c_s x|` and
the profile bounds `profileMikhlinBandGe` (with `N = 1`, band `|x| ≤ 1`) apply. -/
lemma circleLift_mstPiBump_one_mikhlin (P : Polynomial ℤ) (d : ℕ) {χ : ℝ} (η : ℝ → ℂ) (M : ℝ)
    (hM : 0 ≤ M) (hηc : ContDiff ℝ 2 η) (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M)
    (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    (hχ : χ + 1 ≤ (d : ℝ)) :
    ∃ A : ℝ, 0 < A ∧ ∀ s : ℕ,
      ContDiff ℝ 2 (Work.BourgainPlan.Thm52.circleLift (mstPiBump P d χ η 1 s)) ∧
      (∀ x : ℝ, ‖Work.BourgainPlan.Thm52.circleLift (mstPiBump P d χ η 1 s) x‖ ≤ A) ∧
      (∀ x : ℝ, |x| * ‖deriv (Work.BourgainPlan.Thm52.circleLift (mstPiBump P d χ η 1 s)) x‖
        ≤ A) ∧
      (∀ x : ℝ,
        |x| ^ 2 * ‖iteratedDeriv 2 (Work.BourgainPlan.Thm52.circleLift
          (mstPiBump P d χ η 1 s)) x‖ ≤ A) := by
  obtain ⟨C1, hC1pos, hC1⟩ := profileMikhlinBandGe P 1 1
  obtain ⟨C2, hC2pos, hC2⟩ := profileMikhlinBandGe P 2 1
  have hC1nn : 0 ≤ C1 := hC1pos.le
  have hC2nn : 0 ≤ C2 := hC2pos.le
  have hsupp := eta_zero_of_half_le_abs hηc hη0
  have hdsupp := deriv_eta_zero_of_half_le_abs hηc hη0
  refine ⟨max 1 (C2 * M + 2 * C1 * M + M), lt_of_lt_of_le one_pos (le_max_left _ _),
    fun s => ?_⟩
  have hcs1 : 1 ≤ mstScale d χ s := one_le_mstScale hχ s
  have hlift := circleLift_mstPiBump_one P d χ η s hsupp hcs1
  have hcpos : 0 < mstScale d χ s := lt_of_lt_of_le one_pos hcs1
  set c : ℝ := mstScale d χ s with hcdef
  have hc1 : 1 ≤ c := by rw [hcdef]; exact hcs1
  have hcpos' : 0 < c := lt_of_lt_of_le one_pos hc1
  set f : ℝ → ℂ := fun x => star (polyProfile P 1 (-x)) with hfdef
  set g : ℝ → ℂ := fun x => η (-(c * x)) with hgdef
  have hlift' : Work.BourgainPlan.Thm52.circleLift (mstPiBump P d χ η 1 s) = f * g := by
    rw [hlift, hfdef, hgdef]
    rfl
  have hfcd : ContDiff ℝ 2 f := by
    rw [hfdef]
    have h1 : ContDiff ℝ 2 (fun x : ℝ => polyProfile P 1 (-x)) :=
      ((contDiff_polyProfile P 1).of_le (m := 2) (WithTop.coe_le_coe.mpr le_top)).comp
        contDiff_neg
    have h2 := (Complex.conjCLE.contDiff (n := (2 : WithTop ℕ∞))).comp h1
    simpa only [Complex.conjCLE_apply, Function.comp_def, starRingEnd_apply] using h2
  have hgcd : ContDiff ℝ 2 g := by
    rw [hgdef]
    exact hηc.comp ((contDiff_const.mul contDiff_id).neg)
  have hband : ∀ x : ℝ, |x| ≤ 1 / (2 * c) → ((1 : ℕ) : ℝ) ^ P.natDegree * |-x| ≤ 1 := by
    intro x hx
    have hx2 : |x| ≤ 1 / 2 := by
      have h2c : 2 ≤ 2 * c := by linarith
      have h3 : 1 / (2 * c) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) h2c
      linarith
    rw [abs_neg, Nat.cast_one, one_pow, one_mul]
    linarith
  have hderivf : ∀ x : ℝ, deriv f x = - star (deriv (fun y : ℝ => polyProfile P 1 y) (-x)) := by
    intro x
    rw [hfdef]
    have hd : deriv (fun x : ℝ => polyProfile P 1 (-x)) x
        = - deriv (fun y : ℝ => polyProfile P 1 y) (-x) := deriv_comp_neg _ x
    rw [deriv.star']
    simp only [hd]
    simp
  have hiterf : ∀ x : ℝ,
      iteratedDeriv 2 f x = star (iteratedDeriv 2 (fun y : ℝ => polyProfile P 1 y) (-x)) := by
    intro x
    rw [hfdef]
    have hstar2 : ∀ (u : ℝ → ℂ),
        iteratedDeriv 2 (fun x => star (u x)) = fun x => star (iteratedDeriv 2 u x) := by
      intro u
      funext y
      simp only [iteratedDeriv_succ, iteratedDeriv_zero, deriv.star']
    have hneg : iteratedDeriv 2 (fun x : ℝ => polyProfile P 1 (-x))
        = fun x : ℝ => iteratedDeriv 2 (fun y : ℝ => polyProfile P 1 y) (-x) := by
      have h := iteratedDeriv_comp_const_smul (n := 2) (f := fun y : ℝ => polyProfile P 1 y)
        ((contDiff_polyProfile P 1).of_le (m := 2) (WithTop.coe_le_coe.mpr le_top)) (-1 : ℝ)
      simpa using h
    have h1 : iteratedDeriv 2 (fun x : ℝ => star (polyProfile P 1 (-x)))
        = fun x : ℝ => star (iteratedDeriv 2 (fun y : ℝ => polyProfile P 1 (-y)) x) := hstar2 _
    rw [h1, hneg]
  have hf0 : ∀ x : ℝ, ‖f x‖ ≤ 1 := by
    intro x
    rw [hfdef]
    simpa only [norm_star] using norm_polyProfile_le_one P 1 (-x)
  have hf1 : ∀ x : ℝ, |x| ≤ 1 / (2 * c) → |x| * ‖deriv f x‖ ≤ C1 := by
    intro x hx
    rw [hderivf, norm_neg, norm_star, ← abs_neg x]
    have := hC1 1 le_rfl (-x) (hband x hx)
    simpa only [Nat.cast_one, one_pow, pow_one, iteratedDeriv_one] using this
  have hf2 : ∀ x : ℝ, |x| ≤ 1 / (2 * c) → |x| ^ 2 * ‖iteratedDeriv 2 f x‖ ≤ C2 := by
    intro x hx
    rw [hiterf, norm_star, ← abs_neg x]
    have := hC2 1 le_rfl (-x) (hband x hx)
    simpa only [Nat.cast_one, one_pow] using this
  have hg0 : ∀ x : ℝ, ‖g x‖ ≤ M := by
    intro x
    rw [hgdef]
    exact hηbd _
  have hderivg : ∀ x : ℝ, deriv g x = (-c) • deriv η (-(c * x)) := by
    intro x
    rw [hgdef]
    have h := deriv_comp_mul_left c (fun y : ℝ => η (-y)) x
    rw [deriv_comp_neg] at h
    rw [h, smul_neg, neg_smul]
  have hiterg : ∀ x : ℝ, iteratedDeriv 2 g x = c ^ 2 • iteratedDeriv 2 η (-(c * x)) := by
    intro x
    rw [hgdef]
    have h := iteratedDeriv_comp_const_smul (n := 2) (f := fun y : ℝ => η (-y))
      (hηc.comp contDiff_neg) c
    have hg' : (fun x : ℝ => η (-(c * x))) = fun x : ℝ => (fun y : ℝ => η (-y)) (c * x) := rfl
    have hneg2 : iteratedDeriv 2 (fun y : ℝ => η (-y)) = fun y : ℝ => iteratedDeriv 2 η (-y) := by
      have h' := iteratedDeriv_comp_const_smul (n := 2) (f := η) hηc (-1 : ℝ)
      simpa using h'
    rw [congrFun h x, hneg2]
  have hg1 : ∀ x : ℝ, |x| * ‖deriv g x‖ ≤ M := by
    intro x
    rw [hderivg, norm_smul, Real.norm_eq_abs, abs_neg]
    calc |x| * (|c| * ‖deriv η (-(c * x))‖)
        = |c * x| * ‖deriv η (-(c * x))‖ := by rw [abs_mul]; ring
      _ ≤ M := by simpa only [abs_neg] using hder1 (-(c * x))
  have hg2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 g x‖ ≤ M := by
    intro x
    rw [hiterg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg c)]
    calc |x| ^ 2 * (c ^ 2 * ‖iteratedDeriv 2 η (-(c * x))‖)
        = |c * x| ^ 2 * ‖iteratedDeriv 2 η (-(c * x))‖ := by
          rw [abs_mul, abs_of_pos hcpos']
          ring
      _ ≤ M := by simpa only [abs_neg] using hder2 (-(c * x))
  have hgz : ∀ x : ℝ, 1 / (2 * c) ≤ |x| → g x = 0 := by
    intro x hx
    rw [hgdef]
    refine hsupp _ ?_
    rw [abs_neg, abs_mul, abs_of_pos hcpos']
    calc (1 : ℝ) / 2 = c * (1 / (2 * c)) := by field_simp
      _ ≤ c * |x| := mul_le_mul_of_nonneg_left hx hcpos'.le
  have hg1z : ∀ x : ℝ, 1 / (2 * c) ≤ |x| → deriv g x = 0 := by
    intro x hx
    rw [hderivg, hdsupp _ ?_, smul_zero]
    rw [abs_neg, abs_mul, abs_of_pos hcpos']
    calc (1 : ℝ) / 2 = c * (1 / (2 * c)) := by field_simp
      _ ≤ c * |x| := mul_le_mul_of_nonneg_left hx hcpos'.le
  rw [hlift']
  have hexpand : ∀ x : ℝ, iteratedDeriv 2 (f * g) x
      = f x * iteratedDeriv 2 g x + 2 * deriv f x * deriv g x + iteratedDeriv 2 f x * g x := by
    intro x
    rw [iteratedDeriv_mul hfcd.contDiffAt hgcd.contDiffAt]
    simp [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one]
  refine ⟨hfcd.mul hgcd, ?_, ?_, ?_⟩
  · intro x
    rw [Pi.mul_apply, norm_mul]
    calc ‖f x‖ * ‖g x‖ ≤ 1 * M := mul_le_mul (hf0 x) (hg0 x) (norm_nonneg _) zero_le_one
      _ ≤ max 1 (C2 * M + 2 * C1 * M + M) := by
          refine le_trans ?_ (le_max_right _ _)
          nlinarith [hC1nn, hC2nn, hM]
  · intro x
    rw [deriv_mul (hfcd.differentiable (by norm_num) x) (hgcd.differentiable (by norm_num) x)]
    by_cases hx : |x| < 1 / (2 * c)
    · have hxle : |x| ≤ 1 / (2 * c) := le_of_lt hx
      calc |x| * ‖deriv f x * g x + f x * deriv g x‖
          ≤ |x| * (‖deriv f x * g x‖ + ‖f x * deriv g x‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg x)
        _ = |x| * ‖deriv f x‖ * ‖g x‖ + ‖f x‖ * (|x| * ‖deriv g x‖) := by
            rw [norm_mul, norm_mul]; ring
        _ ≤ C1 * M + 1 * M := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul (hf1 x hxle) (hg0 x) (norm_nonneg _) hC1nn
            · exact mul_le_mul (hf0 x) (hg1 x) (by positivity) zero_le_one
        _ ≤ max 1 (C2 * M + 2 * C1 * M + M) := by
            refine le_trans ?_ (le_max_right _ _)
            nlinarith [hC1nn, hC2nn, hM]
    · have hxge : 1 / (2 * c) ≤ |x| := le_of_not_gt hx
      have hz : g x = 0 := hgz x hxge
      calc |x| * ‖deriv f x * g x + f x * deriv g x‖
          ≤ |x| * (‖deriv f x * g x‖ + ‖f x * deriv g x‖) :=
            mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg x)
        _ = |x| * ‖deriv f x‖ * ‖g x‖ + ‖f x‖ * (|x| * ‖deriv g x‖) := by
            rw [norm_mul, norm_mul]; ring
        _ = ‖f x‖ * (|x| * ‖deriv g x‖) := by rw [hz, norm_zero, mul_zero, zero_add]
        _ ≤ 1 * M := mul_le_mul (hf0 x) (hg1 x) (by positivity) zero_le_one
        _ ≤ max 1 (C2 * M + 2 * C1 * M + M) := by
            refine le_trans ?_ (le_max_right _ _)
            nlinarith [hC1nn, hC2nn, hM]
  · intro x
    rw [hexpand x]
    by_cases hx : |x| < 1 / (2 * c)
    · have hxle : |x| ≤ 1 / (2 * c) := le_of_lt hx
      have hsum : ‖f x * iteratedDeriv 2 g x + 2 * deriv f x * deriv g x
            + iteratedDeriv 2 f x * g x‖
          ≤ ‖f x * iteratedDeriv 2 g x‖ + ‖2 * deriv f x * deriv g x‖
            + ‖iteratedDeriv 2 f x * g x‖ := by
        have h1 := norm_add_le (f x * iteratedDeriv 2 g x + 2 * deriv f x * deriv g x)
          (iteratedDeriv 2 f x * g x)
        have h2 := norm_add_le (f x * iteratedDeriv 2 g x) (2 * deriv f x * deriv g x)
        linarith
      have ht1 : |x| ^ 2 * ‖f x * iteratedDeriv 2 g x‖ ≤ M := by
        rw [norm_mul]
        calc |x| ^ 2 * (‖f x‖ * ‖iteratedDeriv 2 g x‖)
            = ‖f x‖ * (|x| ^ 2 * ‖iteratedDeriv 2 g x‖) := by ring
          _ ≤ 1 * M := mul_le_mul (hf0 x) (hg2 x) (by positivity) zero_le_one
          _ ≤ M := by linarith
      have ht2 : |x| ^ 2 * ‖2 * deriv f x * deriv g x‖ ≤ 2 * (C1 * M) := by
        have hnorm : ‖2 * deriv f x * deriv g x‖ = 2 * (‖deriv f x‖ * ‖deriv g x‖) := by
          rw [norm_mul, norm_mul]; simp [mul_assoc]
        rw [hnorm]
        calc |x| ^ 2 * (2 * (‖deriv f x‖ * ‖deriv g x‖))
            = 2 * ((|x| * ‖deriv f x‖) * (|x| * ‖deriv g x‖)) := by ring
          _ ≤ 2 * (C1 * M) := by
              refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              exact mul_le_mul (hf1 x hxle) (hg1 x) (by positivity) hC1nn
      have ht3 : |x| ^ 2 * ‖iteratedDeriv 2 f x * g x‖ ≤ C2 * M := by
        rw [norm_mul]
        calc |x| ^ 2 * (‖iteratedDeriv 2 f x‖ * ‖g x‖)
            = (|x| ^ 2 * ‖iteratedDeriv 2 f x‖) * ‖g x‖ := by ring
          _ ≤ C2 * M := mul_le_mul (hf2 x hxle) (hg0 x) (norm_nonneg _) hC2nn
      calc |x| ^ 2 * ‖f x * iteratedDeriv 2 g x + 2 * deriv f x * deriv g x
            + iteratedDeriv 2 f x * g x‖
          ≤ |x| ^ 2 * (‖f x * iteratedDeriv 2 g x‖ + ‖2 * deriv f x * deriv g x‖
              + ‖iteratedDeriv 2 f x * g x‖) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = |x| ^ 2 * ‖f x * iteratedDeriv 2 g x‖
              + |x| ^ 2 * ‖2 * deriv f x * deriv g x‖
              + |x| ^ 2 * ‖iteratedDeriv 2 f x * g x‖ := by ring
        _ ≤ M + 2 * (C1 * M) + C2 * M := add_le_add (add_le_add ht1 ht2) ht3
        _ ≤ max 1 (C2 * M + 2 * C1 * M + M) := by
            refine le_trans ?_ (le_max_right _ _)
            nlinarith [hC1nn, hC2nn, hM]
    · have hxge : 1 / (2 * c) ≤ |x| := le_of_not_gt hx
      have hz : g x = 0 := hgz x hxge
      have hzg : deriv g x = 0 := hg1z x hxge
      have hsum : ‖f x * iteratedDeriv 2 g x + 2 * deriv f x * deriv g x
            + iteratedDeriv 2 f x * g x‖
          ≤ ‖f x * iteratedDeriv 2 g x‖ + ‖2 * deriv f x * deriv g x‖
            + ‖iteratedDeriv 2 f x * g x‖ := by
        have h1 := norm_add_le (f x * iteratedDeriv 2 g x + 2 * deriv f x * deriv g x)
          (iteratedDeriv 2 f x * g x)
        have h2 := norm_add_le (f x * iteratedDeriv 2 g x) (2 * deriv f x * deriv g x)
        linarith
      have ht1 : |x| ^ 2 * ‖f x * iteratedDeriv 2 g x‖ ≤ M := by
        rw [norm_mul]
        calc |x| ^ 2 * (‖f x‖ * ‖iteratedDeriv 2 g x‖)
            = ‖f x‖ * (|x| ^ 2 * ‖iteratedDeriv 2 g x‖) := by ring
          _ ≤ 1 * M := mul_le_mul (hf0 x) (hg2 x) (by positivity) zero_le_one
          _ ≤ M := by linarith
      have ht2 : |x| ^ 2 * ‖2 * deriv f x * deriv g x‖ ≤ 0 := by
        simp [hzg]
      have ht3 : |x| ^ 2 * ‖iteratedDeriv 2 f x * g x‖ ≤ 0 := by
        simp [hz]
      calc |x| ^ 2 * ‖f x * iteratedDeriv 2 g x + 2 * deriv f x * deriv g x
            + iteratedDeriv 2 f x * g x‖
          ≤ |x| ^ 2 * (‖f x * iteratedDeriv 2 g x‖ + ‖2 * deriv f x * deriv g x‖
              + ‖iteratedDeriv 2 f x * g x‖) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
        _ = |x| ^ 2 * ‖f x * iteratedDeriv 2 g x‖
              + |x| ^ 2 * ‖2 * deriv f x * deriv g x‖
              + |x| ^ 2 * ‖iteratedDeriv 2 f x * g x‖ := by ring
        _ ≤ M + 0 + 0 := add_le_add (add_le_add ht1 ht2) ht3
        _ ≤ max 1 (C2 * M + 2 * C1 * M + M) := by
            refine le_trans ?_ (le_max_right _ _)
            nlinarith [hC1nn, hC2nn, hM]

/-! ## The base term of the level-`s` estimate -/

/-- **MST Theorem 7, the base term**: the level-`s` block operator with the *single* profile scale
`N = 2^0 = 1` is `ℓᵖ`-bounded with constant `C log(s+2)`, uniformly in the level `s`.

The symbol of the operator is `arcSymbol (star (Φ_1) η_s) (𝒰(s+1) ∖ 𝒰(s))`, a difference of the two
arc sums over the nested Ionescu–Wainger supersets `𝒰(s+1) = mstU l (s+1)` and `𝒰(s)`; each of the
two is `ℓᵖ`-bounded by `IWSupersetBound` (Tao's `main` over `Σ_N`, here `iwSupersetBound_proof`),
because the symbol is supported in the ball of radius `ε_s = exp(-(s+1)^{1/10})` — the narrowness of
the level bump — and its compactly supported lift satisfies the Mikhlin conditions with a constant
`A` depending only on `M` and `P` (`circleLift_mstPiBump_one_mikhlin`). -/
theorem mst_lvl_base_lp (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (hc : 0 < P.leadingCoeff)
    (l : ℕ) (hl : 1 ≤ l) {χ : ℝ} (hχ0 : 0 < χ) (hχ1 : χ < 1 / 10)
    (η : ℝ → ℂ) (M : ℝ) (hM : 0 < M) (hηc : ContDiff ℝ 2 η)
    (hηbd : ∀ x : ℝ, ‖η x‖ ≤ M) (hη0 : ∀ x : ℝ, 1 / 2 < |x| → η x = 0)
    (hder1 : ∀ x : ℝ, |x| * ‖deriv η x‖ ≤ M)
    (hder2 : ∀ x : ℝ, |x| ^ 2 * ‖iteratedDeriv 2 η x‖ ≤ M)
    {p : ℝ} (hp : 1 < p) (r₀ : ℕ) (hr₀ : 2 ≤ r₀)
    (hp_hi : p ≤ 2 * (r₀ : ℝ))
    (hp_lo : (2 * (r₀ : ℝ)) / (2 * (r₀ : ℝ) - 1) ≤ p)
    (hηml : ∀ s : ℕ, MeasureTheory.MemLp (Work.BourgainPlan.Maximal.mstEta P.natDegree χ η s) ⊤
      (AddCircle.haarAddCircle (T := 1))) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ g : ℤ →₀ ℂ,
      MeasureTheory.eLpNorm (fun m : ℤ => Work.BourgainPlan.Maximal.opMulFinsuppLM
            (Work.BourgainPlan.Maximal.mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ 0)) g m)
          (ENNReal.ofReal p) MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * Real.log ((s : ℝ) + 2))
          * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  have hd1 : 1 ≤ P.natDegree := by omega
  have hχd : χ < (P.natDegree : ℝ) := by
    have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  have hχ1d : χ + 1 ≤ (P.natDegree : ℝ) := by
    have h2 : (2 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
    linarith
  obtain ⟨Ciw, hCiwpos, Niw, hIW⟩ :=
    iwSupersetBound_proof (mstRho l) (mstRho_pos l hl) p hp
  obtain ⟨A, hApos, hMikh⟩ :=
    circleLift_mstPiBump_one_mikhlin P P.natDegree (χ := χ) η M hM.le hηc hηbd hη0 hder1 hder2 hχ1d
  obtain ⟨sn, hsn0⟩ :=
    mstEta_narrow (l := l) (hl := hl) (d := P.natDegree) (hd := hd1) (χ := χ) (hχd := hχd)
      (η := η) (hη2 := hη0)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨2 * (Ciw * A) / Real.log 2 + 1, by positivity, max sn (max Niw 1), ?_⟩
  intro s hs g
  have hsnN : sn ≤ s := le_trans (le_max_left _ _) hs
  have hNiw : Niw ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
  have hs1 : 1 ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
  -- the base symbol and its properties
  let Ψ : Circ → ℂ := mstPiBump P P.natDegree χ η 1 s
  have hΨml : MemLp Ψ ⊤ haarT := memLp_mstPiBump P P.natDegree χ η 1 s (hηml s)
  have hΨsupp : ∀ ξ : Circ, iwEps (mstRho l) ((s + 1) ^ l) < ‖ξ‖ → Ψ ξ = 0 := by
    intro ξ hξ
    have h := hsn0 s hsnN ξ hξ
    exact show mstPiBump P P.natDegree χ η 1 s ξ = 0 by
      rw [mstPiBump_apply, h, mul_zero]
  obtain ⟨hκcd, hκ0, hκ1, hκ2⟩ := hMikh s
  have hεpos : 0 < iwEps (mstRho l) ((s + 1) ^ l) := Real.exp_pos _
  -- the two arc bounds from Tao's `main` over the nested supersets
  have hε2 : iwEps (mstRho l) ((s + 1) ^ l) ≤ iwEps (mstRho l) (s ^ l) := by
    rw [iwEps, iwEps]
    refine Real.exp_le_exp.mpr (neg_le_neg ?_)
    exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (by exact_mod_cast Nat.pow_le_pow_left (by omega : s ≤ s + 1) l)
      (le_of_lt (mstRho_pos l hl))
  have hN2 : Niw ≤ s ^ l := le_trans hNiw (Nat.le_self_pow (by omega) s)
  have hN1 : Niw ≤ (s + 1) ^ l := le_trans hN2 (Nat.pow_le_pow_left (by omega) l)
  have he1 : MeasureTheory.eLpNorm
      (Work.BourgainPlan.IonescuWainger.opArc Ψ hΨml (iwSigma (mstRho l) ((s + 1) ^ l))
        (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Ciw * A)
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    have h := hIW ((s + 1) ^ l) hN1 (iwEps (mstRho l) ((s + 1) ^ l)) hεpos le_rfl Ψ hΨml hΨsupp
      A hApos.le hκcd hκ0 hκ1 hκ2 (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)
    exact eLpNorm_le_of_lintegral_rpow_le_count (q := p) (C := Ciw * A) (by linarith)
      (by positivity) h
  have he2 : MeasureTheory.eLpNorm
      (Work.BourgainPlan.IonescuWainger.opArc Ψ hΨml (iwSigma (mstRho l) (s ^ l))
        (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (Ciw * A)
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    have h := hIW (s ^ l) hN2 (iwEps (mstRho l) ((s + 1) ^ l)) hεpos hε2 Ψ hΨml hΨsupp
      A hApos.le hκcd hκ0 hκ1 hκ2 (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)
    exact eLpNorm_le_of_lintegral_rpow_le_count (q := p) (C := Ciw * A) (by linarith)
      (by positivity) h
  -- the level symbol is the difference of the two nested arc sums
  have hle : mstU l s ⊆ mstU l (s + 1) := by
    rw [mstU, mstU]
    exact sigmaN_nested (mstRho l) (Nat.pow_le_pow_left (by omega : s ≤ s + 1) l)
  have hsne : s ≠ 0 := by omega
  have hdiff : Work.BourgainPlan.IonescuWainger.opArc Ψ hΨml (mstLevel l (s + 1) \ mstLevel l s)
        (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)
      = Work.BourgainPlan.IonescuWainger.opArc Ψ hΨml (iwSigma (mstRho l) ((s + 1) ^ l))
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)
        - Work.BourgainPlan.IonescuWainger.opArc Ψ hΨml (iwSigma (mstRho l) (s ^ l))
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) := by
    rw [mstLevel_succ, mstLevel, if_neg hsne, mstU, mstU]
    exact opArc_sdiff hΨml hle _ _
  -- the trivial `ℓᵖ`-contraction step: the symbol of the base operator is the arc symbol of `Ψ`
  have hbase : (fun m : ℤ => opMulFinsuppLM
        (mstPiCls P l P.natDegree χ η s (hηml s) (2 ^ 0)) g m)
      = Work.BourgainPlan.IonescuWainger.opArc Ψ hΨml (mstLevel l (s + 1) \ mstLevel l s)
          (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g) := by
    rw [opMulFinsuppLM_apply]
    rfl
  rw [hbase, hdiff]
  have hsub := eLpNorm_sub_le (μ := MeasureTheory.Measure.count) (p := ENNReal.ofReal p)
    (f := Work.BourgainPlan.IonescuWainger.opArc Ψ hΨml (iwSigma (mstRho l) ((s + 1) ^ l))
      (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g))
    (g := Work.BourgainPlan.IonescuWainger.opArc Ψ hΨml (iwSigma (mstRho l) (s ^ l))
      (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g))
    (ENNReal.one_le_ofReal.mpr hp.le)
  have hsum : MeasureTheory.eLpNorm
        (Work.BourgainPlan.IonescuWainger.opArc Ψ hΨml (iwSigma (mstRho l) ((s + 1) ^ l))
            (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)
          - Work.BourgainPlan.IonescuWainger.opArc Ψ hΨml (iwSigma (mstRho l) (s ^ l))
            (⇑g) (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g))
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (2 * (Ciw * A))
        * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
    refine hsub.trans ?_
    calc MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArc Ψ hΨml
            (iwSigma (mstRho l) ((s + 1) ^ l)) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)) (ENNReal.ofReal p)
          MeasureTheory.Measure.count
          + MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArc Ψ hΨml
            (iwSigma (mstRho l) (s ^ l)) (⇑g)
            (Work.BourgainPlan.IonescuWainger.memℓp_finsupp g)) (ENNReal.ofReal p)
          MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (Ciw * A) * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p)
            MeasureTheory.Measure.count
          + ENNReal.ofReal (Ciw * A) * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p)
            MeasureTheory.Measure.count := add_le_add he1 he2
      _ = ENNReal.ofReal (2 * (Ciw * A))
            * MeasureTheory.eLpNorm (⇑g) (ENNReal.ofReal p) MeasureTheory.Measure.count := by
          rw [← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
  -- the arithmetic: `2 (Ciw A) ≤ C log(s+2)` for `C = 2 (Ciw A)/log 2 + 1`
  have hlogs : Real.log 2 ≤ Real.log ((s : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) s])
  have hCs : 2 * (Ciw * A) ≤ (2 * (Ciw * A) / Real.log 2 + 1) * Real.log ((s : ℝ) + 2) := by
    have h1 : (2 * (Ciw * A) / Real.log 2 + 1) * Real.log 2 = 2 * (Ciw * A) + Real.log 2 := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ hlog2.ne']
    calc 2 * (Ciw * A) ≤ 2 * (Ciw * A) + Real.log 2 := by linarith
      _ = (2 * (Ciw * A) / Real.log 2 + 1) * Real.log 2 := h1.symm
      _ ≤ (2 * (Ciw * A) / Real.log 2 + 1) * Real.log ((s : ℝ) + 2) :=
          mul_le_mul_of_nonneg_left hlogs (by positivity)
  exact hsum.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hCs) le_rfl)


end

end Work.BourgainPlan.Maximal
