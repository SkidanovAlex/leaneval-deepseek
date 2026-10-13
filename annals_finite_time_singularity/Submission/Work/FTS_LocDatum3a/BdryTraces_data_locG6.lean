/-
# `Submission/Work/FTS_LocDatum3a/BdryTraces_data_locG6` — the datum-side boundary traces of the
localised order-`6` datum

`Work.FTS.LocData6.locG6 α L β = locR α L β(z)·Γ(θ)` is *separable*
(`Work.FTS.LocDataExt.locG_eq_locR_Gam`), so every mixed jet of the datum factors as

  `D_z^b D_θ^a (locG6) z θ = (D_z^b locR)(z) · (D_θ^a Γ)(θ)`

(`Work.FTS.LocDataExt.mixed_sepGam`, `bdry_mixed_eq` below), the radial factor being independent
of `θ`.  The five clauses of the lemma are therefore consequences of four inputs:

* `Work.FTS_LocDatum3a.hB_locR8` — the weighted radial bound
  `((D_z^b locR) z · w z)² ≤ R/(1+z)²`: since `w z = (1+z)²/z²`, it gives the *uniform in `z`*
  bound `|D_z^b locR z| ≤ √R` for every `z > 0` (and every `b ≤ 8`);
* `Work.FTS_LocDatum3a.FM_jet8safe` — beyond `max (2L) (7/4)` the radial factor is
  `-(α/c)·F_*` (`Work.FTS.LocDataExt.locR_eventuallyEq_far`), whose `D_z`-jets decay like `1/z`
  up to order `8`, whence `|D_z^b locR z| ≤ A/z` there;
* `Work.FTS_LocDatum3a.DthIter_Gam_abs_le8` — `|D_θ^a Γ| ≤ 10⁷·Γ ≤ 10⁷` for `a ≤ 8`;
* the elementary `w z² ≤ 16` for `z ≥ 1` and `Γ θ ≤ sin(2θ)^{α/5}`
  (`Work.FTS.LocData.Gam_le_sin_two_rpow`) with `1 - γ + 2α/5 = 3α/10 > 0`, which turns the two
  angular limits into the single limit `sin(2θ)^{3α/10} → 0`
  (`Work.FTS.LocDataExt.tendsto_sin_gam_trace`).

The five conjuncts are exactly the datum hypotheses `hbdd`, `hz0`, `hzin`, `ht0`, `ht1` of
`Work.FTS.StrongEps.softClass_Jeps` at order `7`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.LocData6.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS_LocDatum3a.DthIter_Gam_abs_le8
import Submission.Work.FTS_LocDatum3a.FM_jet8safe
import Submission.Work.FTS_LocDatum3a.hB_locR8

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_LocDatum3a

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The separability of the datum -/

/-- The localised datum is the product of its radial and angular factors. -/
theorem bdry_locG6_eq_sep (α L β : ℝ) :
    Work.FTS.LocData6.locG6 α L β
      = fun z θ => Work.FTS.LocDataExt.locR α L β z * Work.Spaces.Gam α θ :=
  Work.FTS.LocDataExt.locG_eq_locR_Gam α L β

/-- **Every mixed slot of the datum is the product of a radial and an angular jet.** -/
theorem bdry_mixed_eq (α L β : ℝ) (b a : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ
      = Work.Spaces.DzIter b (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ
        * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ := by
  rw [bdry_locG6_eq_sep α L β]
  exact congrFun (congrFun (Work.FTS.LocDataExt.mixed_sepGam α
    (Work.FTS.LocDataExt.locR α L β) b a) z) θ

/-! ## The two radial bounds -/

/-- **The radial jets of `locR` are bounded on `(0,∞)`, uniformly in `z`.**  This is the
weighted bound `hB_locR8` divided by the weight: `w z = (1+z)²/z²` gives
`(D_z^b locR z)² ≤ R z⁴/(1+z)⁶ ≤ R`. -/
theorem bdry_rad_uniform (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ b : ℕ, b ≤ 7 → ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ : ℝ,
      |Work.Spaces.DzIter b (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ| ≤ M := by
  obtain ⟨R, hR0, hR⟩ := hB_locR8 α L β hα hα1 hL
  refine ⟨Real.sqrt R, Real.sqrt_nonneg R, fun b hb z hz θ => ?_⟩
  set A : ℝ := Work.Spaces.DzIter b (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ with hA
  have hzIz : z ∈ Work.Spaces.Iz := by
    rw [Work.Spaces.Iz, Set.mem_Ici]
    exact le_of_lt hz
  have hzpos : 0 < z := hz
  have h1z : 0 < 1 + z := by linarith
  -- the weighted bound, multiplied by `(1+z)²`
  have h1 : A ^ 2 * (Work.Spaces.w z) ^ 2 ≤ R / (1 + z) ^ 2 := by
    have h := hR b (by omega) z hzIz θ
    rw [← hA, mul_pow] at h
    exact h
  have h2 : A ^ 2 * (Work.Spaces.w z) ^ 2 * (1 + z) ^ 2 ≤ R := by
    rw [le_div_iff₀ (pow_pos h1z 2)] at h1
    exact h1
  -- `w z² (1+z)² = ((1+z)³/z²)²`
  have hw2 : (Work.Spaces.w z) ^ 2 * (1 + z) ^ 2 = ((1 + z) ^ 3 / z ^ 2) ^ 2 := by
    rw [Work.Spaces.w, div_pow, div_pow]
    field_simp
  have h3 : A ^ 2 * ((1 + z) ^ 3 / z ^ 2) ^ 2 ≤ R := by
    rw [← hw2]
    calc A ^ 2 * ((Work.Spaces.w z) ^ 2 * (1 + z) ^ 2)
        = A ^ 2 * (Work.Spaces.w z) ^ 2 * (1 + z) ^ 2 := by ring
      _ ≤ R := h2
  have hge : 1 ≤ ((1 + z) ^ 3 / z ^ 2) ^ 2 := by
    have h1' : 1 ≤ (1 + z) ^ 3 / z ^ 2 := by
      rw [le_div_iff₀ (pow_pos hzpos 2)]
      nlinarith [hzpos]
    nlinarith [h1']
  have h4 : A ^ 2 ≤ R := by
    have := mul_le_mul_of_nonneg_left hge (sq_nonneg A)
    linarith
  have h5 : Real.sqrt (A ^ 2) ≤ Real.sqrt R := Real.sqrt_le_sqrt h4
  simpa [Real.sqrt_sq_eq_abs] using h5

/-- **The far-field decay of the radial jets of `locR`.**  Beyond `max (2L) (7/4)` the factor
`locR` agrees with `-(α/c)·F_*` near `z`, and the `D_z`-jets of `F_*` decay like `1/z`. -/
theorem bdry_rad_far (α L β : ℝ) (hL : 1 ≤ L) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ b : ℕ, b ≤ 8 → ∀ z : ℝ, max (2 * L) (7 / 4) < z → ∀ θ : ℝ,
      |Work.Spaces.DzIter b (fun z _ => Work.FTS.LocDataExt.locR α L β z) z θ| ≤ A / z := by
  obtain ⟨CF, hCF, hF⟩ := FM_jet8safe
  refine ⟨|α / Work.Spaces.c α| * CF, by positivity, fun b hb z hz θ => ?_⟩
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hz2 : 2 * L < z := lt_of_le_of_lt (le_max_left _ _) hz
  have hz7 : 7 / 4 < z := lt_of_le_of_lt (le_max_right _ _) hz
  have hz1 : (1 : ℝ) ≤ z := by linarith
  have hev := Work.FTS.LocDataExt.locR_eventuallyEq_far (α := α) (L := L) (β := β)
    hLpos hz2 hz7
  have hcongr := Work.FTS.LocDataExt.DzIter_z_congr_of_eventuallyEq hev b θ
  have hcm : Work.Spaces.DzIter b (fun z _ => -(α / Work.Spaces.c α) * Work.FM.Fstar z) z θ
      = -(α / Work.Spaces.c α) * Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ :=
    congrFun (congrFun (Work.FTS.LocDataExt.DzIter_const_mul (-(α / Work.Spaces.c α))
      (fun z _ => Work.FM.Fstar z) b) z) θ
  rw [hcongr, hcm, abs_mul, abs_neg]
  have h2 := hF b hb z hz1 θ
  calc |α / Work.Spaces.c α| * |Work.Spaces.DzIter b (fun z _ => Work.FM.Fstar z) z θ|
      ≤ |α / Work.Spaces.c α| * (CF / z) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |α / Work.Spaces.c α| * CF / z := by ring

/-! ## The datum lemma -/

theorem BdryTraces_data_locG6 (α L β : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hL : 1 ≤ L) :
    (∀ a b : ℕ, a + b ≤ 7 → ∃ M : ℝ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
        |Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ| ≤ M) ∧
      (∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ δ > 0, ∀ z : ℝ, 0 < z → z < δ →
        ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
          z * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ * Work.Spaces.w z) ^ 2
            ≤ ε') ∧
      (∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ Z : ℝ, ∀ z : ℝ, Z < z →
        ∀ θ : ℝ, θ ∈ Set.Ioo 0 (π / 2) →
          z * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ * Work.Spaces.w z) ^ 2
            ≤ ε') ∧
      (∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
        ∀ z : ℝ, 0 < z → Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2 ≤ ε') ∧
      (∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < π / 2 → π / 2 - δ < θ →
        ∀ z : ℝ, 0 < z → Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2 ≤ ε') := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨M, hM0, hM⟩ := bdry_rad_uniform α L β hα hα1 hL
  obtain ⟨A, hA0, hA⟩ := bdry_rad_far α L β hL
  -- the angular bound `|D_θ^a Γ| ≤ 10⁷` for `a ≤ 8`
  have hang : ∀ a : ℕ, a ≤ 8 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ| ≤ 10000000 := by
    intro a ha θ hθ
    have h1 := DthIter_Gam_abs_le8 a ha α hα hα1 hθ
    have h2 : Work.Spaces.Gam α θ ≤ 1 := (Work.Spaces.Gam_bounds α θ hα hθ).2
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- ## the slots are bounded
    intro a b hab
    have hb7 : b ≤ 7 := by omega
    have ha8 : a ≤ 8 := by omega
    refine ⟨M * 10000000, fun z θ hz hθ => ?_⟩
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    rw [bdry_mixed_eq α L β b a z θ, abs_mul]
    exact mul_le_mul (hM b hb7 z hz θ) (hang a ha8 θ hθI) (abs_nonneg _) hM0
  · -- ## the `z → 0⁺` traces: the datum vanishes near `z = 0`
    intro a b hab ε' hε'
    refine ⟨min L (3 / 4), lt_min hLpos (by norm_num), fun z hz hzδ θ hθ => ?_⟩
    have hev : ∀ᶠ z' in 𝓝 z, ∀ θ' : ℝ, Work.FTS.LocData6.locG6 α L β z' θ' = 0 := by
      filter_upwards [Ioo_mem_nhds hz hzδ] with z' hz' θ'
      rw [bdry_locG6_eq_sep α L β]
      have h1 : Work.FTS.LocDataExt.locR α L β z' = 0 :=
        Work.FTS.LocDataExt.locR_eq_zero_of_le hLpos (le_of_lt hz'.1)
          (le_of_lt (lt_of_lt_of_le hz'.2 (min_le_left _ _)))
          (le_of_lt (lt_of_lt_of_le hz'.2 (min_le_right _ _)))
      show Work.FTS.LocDataExt.locR α L β z' * Work.Spaces.Gam α θ' = 0
      rw [h1, zero_mul]
    have hzero : Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ = 0 :=
      Work.FTS.LocData.ZFBase.mixed_eq_zero_of_eventually_zero hev b a
    have hz0 : z * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ
        * Work.Spaces.w z) ^ 2 = 0 := by
      rw [hzero]; ring
    rw [hz0]
    exact le_of_lt hε'
  · -- ## the `z → ∞` traces, from the `1/z`-decay of the radial jets
    intro a b hab ε' hε'
    have hb8 : b ≤ 8 := by omega
    have ha8 : a ≤ 8 := by omega
    refine ⟨max (max (2 * L) (7 / 4) + 1)
      (16 * A ^ 2 * (10000000 : ℝ) ^ 2 / ε' + 1), fun z hz θ hθ => ?_⟩
    have hzfar : max (2 * L) (7 / 4) < z := by
      have h : max (2 * L) (7 / 4) + 1 ≤ z := le_trans (le_max_left _ _) (le_of_lt hz)
      linarith
    have hzbig : 16 * A ^ 2 * (10000000 : ℝ) ^ 2 / ε' < z := by
      have h : 16 * A ^ 2 * (10000000 : ℝ) ^ 2 / ε' + 1 ≤ z :=
        le_trans (le_max_right _ _) (le_of_lt hz)
      linarith
    have hz7 : (7 / 4 : ℝ) < z := lt_of_le_of_lt (le_max_right _ _) hzfar
    have hzpos : 0 < z := by linarith
    have hz1 : (1 : ℝ) ≤ z := by linarith
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
    have hrad := hA b hb8 z hzfar θ
    have hangb := hang a ha8 θ hθI
    have hmix : |Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ|
        ≤ A / z * 10000000 := by
      rw [bdry_mixed_eq α L β b a z θ, abs_mul]
      exact mul_le_mul hrad hangb (abs_nonneg _) (by positivity)
    have hmix2 : (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2
        ≤ (A / z * 10000000) ^ 2 := by
      have h1 := pow_le_pow_left₀ (abs_nonneg _) hmix 2
      rwa [sq_abs] at h1
    have hw16 : (Work.Spaces.w z) ^ 2 ≤ 16 := Work.FTS.LocDataExt.w_sq_le_sixteen hz1
    have hfinal : 16 * A ^ 2 * (10000000 : ℝ) ^ 2 / z ≤ ε' := by
      rw [div_le_iff₀ hzpos]
      have h2 : 16 * A ^ 2 * (10000000 : ℝ) ^ 2 < z * ε' := (div_lt_iff₀ hε').mp hzbig
      linarith
    calc z * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ * Work.Spaces.w z) ^ 2
        = z * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2
            * (Work.Spaces.w z) ^ 2 := by ring
      _ ≤ z * (A / z * 10000000) ^ 2 * 16 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hmix2 (le_of_lt hzpos)) hw16
            (sq_nonneg _) ?_
          positivity
      _ = 16 * A ^ 2 * (10000000 : ℝ) ^ 2 / z := by
          field_simp
      _ ≤ ε' := hfinal
  · -- ## the `θ → 0⁺` traces, uniformly in `z`
    intro a b hab ε' hε'
    have hb7 : b ≤ 7 := by omega
    have ha8 : a ≤ 8 := by omega
    have hC0 : 0 ≤ M * 10000000 := by positivity
    have hbound : ∀ θ ∈ Work.Spaces.Iθ,
        |M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
          ≤ (M * 10000000) * Work.Spaces.Gam α θ := by
      intro θ hθ
      rw [abs_mul, abs_of_nonneg hM0]
      have h1 := DthIter_Gam_abs_le8 a ha8 α hα hα1 hθ
      calc M * |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
          ≤ M * (10000000 * Work.Spaces.Gam α θ) := mul_le_mul_of_nonneg_left h1 hM0
        _ = M * 10000000 * Work.Spaces.Gam α θ := by ring
    have hlim := (Work.FTS.LocDataExt.tendsto_sin_gam_trace α hα hC0 hbound).1
    obtain ⟨δ₁, hδ₁0, hδ₁⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim ε' hε'
    refine ⟨min δ₁ (π / 4), lt_min hδ₁0 (by positivity), fun θ hθ0 hθδ z hz => ?_⟩
    have hθδ₁ : θ < δ₁ := lt_of_lt_of_le hθδ (min_le_left _ _)
    have hθπ : θ < π / 4 := lt_of_lt_of_le hθδ (min_le_right _ _)
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ0, by linarith [hθπ, Real.pi_pos]⟩
    have hdist : dist θ (0 : ℝ) < δ₁ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hθ0]
      exact hθδ₁
    have hkey : Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2 < ε' := by
      have h := hδ₁ (Set.mem_Ioi.mpr hθ0) hdist
      rw [Real.dist_eq, sub_zero] at h
      exact (abs_lt.mp h).2
    have hmix2 : (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2
        ≤ (M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2 := by
      rw [bdry_mixed_eq α L β b a z θ, mul_pow, mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have h1 := pow_le_pow_left₀ (abs_nonneg _) (hM b hb7 z hz θ) 2
      rwa [sq_abs] at h1
    have hsin0 : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_nonneg (Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθI) _
    calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2
        ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2 :=
          mul_le_mul_of_nonneg_left hmix2 hsin0
      _ ≤ ε' := le_of_lt hkey
  · -- ## the `θ → (π/2)⁻` traces, uniformly in `z`
    intro a b hab ε' hε'
    have hb7 : b ≤ 7 := by omega
    have ha8 : a ≤ 8 := by omega
    have hC0 : 0 ≤ M * 10000000 := by positivity
    have hbound : ∀ θ ∈ Work.Spaces.Iθ,
        |M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
          ≤ (M * 10000000) * Work.Spaces.Gam α θ := by
      intro θ hθ
      rw [abs_mul, abs_of_nonneg hM0]
      have h1 := DthIter_Gam_abs_le8 a ha8 α hα hα1 hθ
      calc M * |Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ|
          ≤ M * (10000000 * Work.Spaces.Gam α θ) := mul_le_mul_of_nonneg_left h1 hM0
        _ = M * 10000000 * Work.Spaces.Gam α θ := by ring
    have hlim := (Work.FTS.LocDataExt.tendsto_sin_gam_trace α hα hC0 hbound).2
    obtain ⟨δ₁, hδ₁0, hδ₁⟩ := Metric.tendsto_nhdsWithin_nhds.mp hlim ε' hε'
    refine ⟨min δ₁ (π / 4), lt_min hδ₁0 (by positivity), fun θ hθπ hθδ z hz => ?_⟩
    have hδ' : π / 2 - δ₁ ≤ π / 2 - min δ₁ (π / 4) := by
      have := min_le_left δ₁ (π / 4)
      linarith
    have hθδ₁ : π / 2 - δ₁ < θ := by linarith
    have hθpos : 0 < θ := by
      have hmin : min δ₁ (π / 4) ≤ π / 4 := min_le_right _ _
      have h : (0 : ℝ) < π / 2 - min δ₁ (π / 4) := by linarith [Real.pi_pos, hmin]
      linarith
    have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθpos, le_of_lt hθπ⟩
    have hdist : dist θ (π / 2) < δ₁ := by
      rw [Real.dist_eq, abs_of_neg (by linarith : θ - π / 2 < 0)]
      linarith
    have hkey : Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2 < ε' := by
      have h := hδ₁ (Set.mem_Iio.mpr hθπ) hdist
      rw [Real.dist_eq, sub_zero] at h
      exact (abs_lt.mp h).2
    have hmix2 : (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2
        ≤ (M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2 := by
      rw [bdry_mixed_eq α L β b a z θ, mul_pow, mul_pow]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have h1 := pow_le_pow_left₀ (abs_nonneg _) (hM b hb7 z hz θ) 2
      rwa [sq_abs] at h1
    have hsin0 : 0 ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
      Real.rpow_nonneg (Work.FTS.LocData.ZFBase.sin_two_nonneg_Iθ hθI) _
    calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
          * (Work.Spaces.mixed b a (Work.FTS.LocData6.locG6 α L β) z θ) ^ 2
        ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
            * (M * Work.Spaces.DthIter a (fun _ θ' => Work.Spaces.Gam α θ') 0 θ) ^ 2 :=
          mul_le_mul_of_nonneg_left hmix2 hsin0
      _ ≤ ε' := le_of_lt hkey

end Work.FTS_LocDatum3a
