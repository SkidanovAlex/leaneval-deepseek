import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.bwdFanDefs
import Submission.Work.EQ.bwdFanSheets
import Submission.Work.EQ.bwdP_fan_degenerate_countable
import Submission.Work.EQ.bwdP_fan_radicand_zero_ne
import Submission.Work.EQ.subO2_invBranch
import Submission.Work.EQ.countable_zero_analytic_preconnected
import Submission.Work.EQ.isPreconnected_ball_diff_countable
import Submission.Work.EQ.fan_estimates

/-! # The `O₂`-degenerate locus of backward chains from a stable fan is countable

Companion of the PROVED `Work.EQ.bwdP_fan_degenerate_countable` (which counts the parameters at
which some backward fan radicand `bsq (subO1 a ·)` vanishes).  Here the same is done for the
`O₂`-radicand `bsq (subO2 a ·)`: the parameters at which a backward partner of a fan value lies on
an isotropic line through `O₂ = (a/2, 0)`, i.e. at which the *forward* local branch of the relation
degenerates.

Route.  By `Work.EQ.bsq_subO2_invBranch_mul`, for a word `σ ++ [t]`,
`bsq (subO2 a (bwdP a (σ++[t]) P)) = (t - brho (subO1 a (bwdP a σ P)))² * bsq (subO1 a (bwdP a σ P))`,
so a level-`(n+1)` `O₂`-degeneracy is a level-`≤ n` `O₁`-degeneracy (already counted) or a parameter
where `R_τ = 1` for some `τ` of length `n`, `R_τ := bsq (subO1 a (bwdP a τ (fan a h ε ·)))`.  Such
parameters are the zeros of the level product `∏_{|τ| = n} (R_τ - 1)`, which is analytic on the
preconnected region `ball δ \ {R_σ = 0}` because each `R_τ` is the value of an analytic *sheet*
there (`Submission/Work/EQ/bwdFanSheets.lean`); at `w = 0` the backward fan iterates are axis
points `(-1/2 + 2k, 0)` (`Work.EQ.fan_centres`, `Work.EQ.bwdP_fan_eq_fan_aux`), whose radicand
squares to `(-1/2 + 2k + a/2)² ≠ 1`, so the product is not identically zero and
`Work.EQ.countable_zero_analytic_preconnected` applies. -/

namespace Work.EQ

open Complex Filter _root_.Topology
open scoped BigOperators

noncomputable section

/-! ## The `O₂`-degenerate locus and the level products -/

/-- The parameters `w` in the disc of radius `δ` at which some backward radicand `bsq (subO2 a ·)`
of level at most `n` vanishes. -/
def degSet2 (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) (δ : ℝ) (n : ℕ) : Set ℂ :=
  {w : ℂ | ‖w‖ < δ ∧ ∃ σ : List Bool, σ.length ≤ n ∧
    bsq (subO2 a (bwdP a σ (fan a h ε w))) = 0}

/-- The level-`n` product of the `O₁`-radicands shifted by `1`. -/
def lvlProd1 (a : ℝ) (h : ℂ → ℂ) (ε : List Bool) (n : ℕ) (w : ℂ) : ℂ :=
  ((fanWords n).map (fun σ => bsq (subO1 a (bwdP a σ (fan a h ε w))) - 1)).prod

/-! ## The algebraic reduction -/

/-- **An `O₂`-degeneracy has a parent `O₁`-degeneracy or a parent with radicand `1`.**  For a word
`σ ++ [t]`, `bsq (subO2 a (bwdP a (σ++[t]) P)) = (±1 * ρ⁻¹ - 1)² * R` with `R = bsq (subO1 a Q)`,
`ρ = brho (subO1 a Q)`, `Q = bwdP a σ P`; hence the vanishing forces `R = 0` or `R = 1`. -/
theorem subO2_degenerate_parent {a : ℝ} {P : ℂ × ℂ} (τ : List Bool) (t : Bool)
    (hz : bsq (subO2 a (bwdP a (τ ++ [t]) P)) = 0) :
    bsq (subO1 a (bwdP a τ P)) = 0 ∨ bsq (subO1 a (bwdP a τ P)) = 1 := by
  set R : ℂ := bsq (subO1 a (bwdP a τ P)) with hR
  set ρ : ℂ := brho (subO1 a (bwdP a τ P)) with hρ
  have hρ2 : ρ ^ 2 = R := by rw [hρ, hR]; exact brho_sq _
  have hfactor : bsq (subO2 a (bwdP a (τ ++ [t]) P))
      = ((if t then (1 : ℂ) else -1) * ρ⁻¹ - 1) ^ 2 * R := by
    rw [bwdP_snoc, bsq_subO2_invBranch_mul, ← hρ, ← hR]
  rw [hfactor] at hz
  rcases mul_eq_zero.mp hz with h | h
  · have h0 : (if t then (1 : ℂ) else -1) * ρ⁻¹ - 1 = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    rcases t with _ | _
    · exfalso
      have h1 : -(ρ⁻¹) - 1 = 0 := by simpa using h0
      have h2 : ρ⁻¹ = -1 := by linear_combination -h1
      rw [show (-1 : ℂ) = (-1)⁻¹ by simp] at h2
      exact brho_ne_neg_one (subO1 a (bwdP a τ P)) (hρ ▸ inv_inj.mp h2)
    · right
      have h1 : ρ⁻¹ = 1 := by
        have h0' : ρ⁻¹ - 1 = 0 := by simpa using h0
        exact sub_eq_zero.mp h0'
      have hρ1 : ρ = 1 := inv_eq_one.mp h1
      rw [← hρ2, hρ1]
      norm_num
  · left
    rw [hR] at h
    exact h

/-! ## The integer input at `w = 0` -/

/-- The abscissa of a fan centre never has square `1`, for `0 < a < 1`. -/
theorem fan_centre_add_half_sq_ne_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (k : ℤ) :
    (-1 / 2 + 2 * (k : ℝ) + a / 2) ^ 2 ≠ 1 := by
  intro h
  rcases sq_eq_one_iff.mp h with hk | hk
  · have h1 : (0 : ℝ) < (k : ℝ) := by linarith
    have h2 : (k : ℝ) < 1 := by linarith
    have h3 : (0 : ℤ) < k := by exact_mod_cast h1
    have h4 : k < 1 := by exact_mod_cast h2
    omega
  · have h1 : (-1 : ℝ) < (k : ℝ) := by linarith
    have h2 : (k : ℝ) < 0 := by linarith
    have h3 : (-1 : ℤ) < k := by exact_mod_cast h1
    have h4 : k < 0 := by exact_mod_cast h2
    omega

/-- **The level product `∏ (R_σ - 1)` is analytic at every point where the labelled `O₁`-radicands
of levels `≤ n` are non-zero.**  The labelled backward iterates themselves are not analytic (the
principal square root jumps across its cut), but their multiset is the multiset of the analytic
sheets (`Work.EQ.sheet_claim`), and `∏ (R_σ - 1)` is a symmetric function of that multiset. -/
theorem analyticAt_lvlProd1_of_good {a : ℝ} {h : ℂ → ℂ} {ε : List Bool} {w₀ : ℂ} {n : ℕ}
    (hfan : ∀ τ : List Bool, AnalyticAt ℂ (fan a h τ) w₀)
    (hgood : ∀ σ : List Bool, σ.length ≤ n →
      bsq (subO1 a (bwdP a σ (fan a h ε w₀))) ≠ 0) :
    AnalyticAt ℂ (lvlProd1 a h ε n) w₀ := by
  obtain ⟨hA, -, hC⟩ := sheet_claim (a := a) (h := h) (ε := ε) (w₀ := w₀) (n := n) hfan hgood
    n (by omega)
  have han : AnalyticAt ℂ (fun w => ((fanWords n).map
      (fun σ => bsq (subO1 a (sheetU a h ε w₀ σ w)) - 1)).prod) w₀ :=
    analyticAt_list_prod fun σ hσ =>
      (analyticAt_bsq_subO1_comp (hA σ (by rw [mem_fanWords.mp hσ]))).sub
        analyticAt_const
  have key : (fun w => ((fanWords n).map
        (fun σ => bsq (subO1 a (sheetU a h ε w₀ σ w)) - 1)).prod)
      =ᶠ[𝓝 w₀] (lvlProd1 a h ε n) := by
    refine Filter.Eventually.of_forall fun w => ?_
    have hp := (hC n le_rfl w).map (fun Q : ℂ × ℂ => bsq (subO1 a Q) - 1)
    rw [lvlProd1]
    simpa only [List.map_map, Function.comp_def] using hp.prod_eq
  exact han.congr key

/-- **At `w = 0` the level product is non-zero.**  At `0` every backward fan iterate is a fan value
of argument `0`, hence an axis point `(-1/2 + 2k, 0)`, whose `O₁`-radicand squares to
`(-1/2 + 2k + a/2)^2 ≠ 1`. -/
theorem lvlProd1_zero_ne {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (ε : List Bool) (n : ℕ) :
    lvlProd1 a h ε n 0 ≠ 0 := by
  have hlam : ((eqLam a : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (eqLam_pos' ha0 ha1))
  have hone : ∀ σ : List Bool,
      bsq (subO1 a (bwdP a σ (fan a h ε 0))) - 1 ≠ 0 := by
    intro σ
    have hid : bwdP a σ (fan a h ε 0) = fan a h (σ.reverse ++ ε) 0 := by
      have := bwdP_fan_eq_fan_aux (a := a) h hlam σ ε 0
      simpa using this
    rw [hid]
    obtain ⟨hz, k, hk⟩ := fan_centres ha0 ha1 hh (σ.reverse ++ ε)
    have hpt : fan a h (σ.reverse ++ ε) 0 =
        ((((-1 / 2 + 2 * (k : ℝ)) : ℝ) : ℂ), (0 : ℂ)) := by
      rw [Prod.ext_iff]; exact ⟨hk, hz⟩
    rw [hpt]
    have hsub : subO1 a ((((-1 / 2 + 2 * (k : ℝ)) : ℝ) : ℂ), (0 : ℂ)) =
        (((-1 / 2 + 2 * (k : ℝ) + a / 2 : ℝ) : ℂ), (0 : ℂ)) := by
      apply Prod.ext
      · simp only [subO1]; push_cast; ring
      · simp only [subO1]
    rw [hsub, sub_ne_zero]
    simp only [bsq, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
    intro hcon
    have hcoe : (((-1 / 2 + 2 * (k : ℝ) + a / 2) ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by
      rw [Complex.ofReal_pow, Complex.ofReal_one]
      exact hcon
    exact fan_centre_add_half_sq_ne_one ha0 ha1 k (Complex.ofReal_inj.mp hcoe)
  unfold lvlProd1
  induction (fanWords n) with
  | nil => simp
  | cons σ rest ih =>
      rw [List.map_cons, List.prod_cons]
      exact mul_ne_zero (hone σ) ih

/-! ## Analyticity of the `O₂`-radicand of a fan, and the integer input at `0` -/

/-- Analyticity of `w ↦ bsq (subO2 a (P w))` at a point where `P` is analytic. -/
theorem analyticAt_bsq_subO2_comp {a : ℝ} {P : ℂ → ℂ × ℂ} {z : ℂ} (hP : AnalyticAt ℂ P z) :
    AnalyticAt ℂ (fun w => bsq (subO2 a (P w))) z := by
  have h1 : AnalyticAt ℂ (fun w => (P w).1 - ((a / 2 : ℝ) : ℂ)) z :=
    (analyticAt_fst.comp hP).sub analyticAt_const
  have h2 : AnalyticAt ℂ (fun w => (P w).2) z := analyticAt_snd.comp hP
  refine ((h1.pow 2).add (h2.pow 2)).congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [bsq, subO2, Pi.pow_apply, Pi.add_apply]

/-- The abscissa `-1/2 + 2k` of a fan centre is never `a/2`, for `0 < a < 1`. -/
theorem fan_centre_sub_half_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (k : ℤ) :
    -1 / 2 + 2 * (k : ℝ) - a / 2 ≠ 0 := by
  intro h
  have hk4 : (k : ℝ) = (1 + a) / 4 := by linarith
  have h1 : (1 : ℝ) / 4 < (k : ℝ) := by rw [hk4]; linarith
  have h2 : (k : ℝ) < 1 / 2 := by rw [hk4]; linarith
  have h3 : (0 : ℤ) < k := by
    have : (0 : ℝ) < (k : ℝ) := by linarith
    exact_mod_cast this
  have h4 : k < 1 := by
    have : (k : ℝ) < 1 := by linarith
    exact_mod_cast this
  omega

/-- **The `O₂`-locus at level `0` is countable**: the zeros of `w ↦ bsq (subO2 a (fan a h ε w))`. -/
theorem zeroLocus_subO2_fan_countable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {δ δf : ℝ} (hδ : 0 < δ) (hδf : δ ≤ δf)
    {Ke Lam Q : ℝ} (hF : ∀ (ε : List Bool) (v : ℂ), v ∈ Metric.ball (0 : ℂ) δf →
      FanGood a h Ke Lam Q ε v) (ε : List Bool) :
    {w : ℂ | ‖w‖ < δ ∧ bsq (subO2 a (fan a h ε w)) = 0}.Countable := by
  have hpre : IsPreconnected (Metric.ball (0 : ℂ) δ) :=
    (convex_ball (0 : ℂ) δ).isPreconnected
  have hAn : AnalyticOnNhd ℂ (fun w => bsq (subO2 a (fan a h ε w))) (Metric.ball (0 : ℂ) δ) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact analyticAt_bsq_subO2_comp (hF ε w (by simpa using lt_of_lt_of_le hw hδf)).1
  have h0 : (fun w => bsq (subO2 a (fan a h ε w))) 0 ≠ 0 := by
    show bsq (subO2 a (fan a h ε 0)) ≠ 0
    obtain ⟨hz, k, hk⟩ := fan_centres ha0 ha1 hh ε
    have hpt : fan a h ε 0 = ((((-1 / 2 + 2 * (k : ℝ)) : ℝ) : ℂ), (0 : ℂ)) := by
      rw [Prod.ext_iff]; exact ⟨hk, hz⟩
    rw [hpt]
    have hsub : subO2 a ((((-1 / 2 + 2 * (k : ℝ)) : ℝ) : ℂ), (0 : ℂ)) =
        (((-1 / 2 + 2 * (k : ℝ) - a / 2 : ℝ) : ℂ), (0 : ℂ)) := by
      apply Prod.ext
      · simp only [subO2]; push_cast; ring
      · simp only [subO2]
    rw [hsub]
    simp only [bsq, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero]
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (fan_centre_sub_half_ne_zero ha0 ha1 k))
  have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hδ
  have := countable_zero_analytic_preconnected hpre hAn hmem h0
  refine Set.Countable.mono ?_ this
  rintro w ⟨hw, hz⟩
  exact ⟨by simpa using hw, hz⟩

/-- **The locus where a backward fan radicand equals `1` is countable** (for a fixed level). -/
theorem lvlProd1_zeroLocus_countable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {δ δf δ₁ : ℝ} (hδ : 0 < δ) (hδf : δ ≤ δf) (hδ₁ : δ ≤ δ₁)
    {Ke Lam Q : ℝ} (hF : ∀ (ε : List Bool) (v : ℂ), v ∈ Metric.ball (0 : ℂ) δf →
      FanGood a h Ke Lam Q ε v) (hD1 : ∀ (ε : List Bool) (n : ℕ), {w : ℂ | ‖w‖ < δ₁ ∧ ∃ σ : List Bool, σ.length ≤ n ∧
      bsq (subO1 a (bwdP a σ (fan a h ε w))) = 0}.Countable)
    (ε : List Bool) (n : ℕ) :
    {w : ℂ | ‖w‖ < δ ∧ ∃ σ : List Bool, σ.length = n ∧
      bsq (subO1 a (bwdP a σ (fan a h ε w))) = 1}.Countable := by
  set D : Set ℂ := {w : ℂ | ‖w‖ < δ ∧ ∃ σ : List Bool, σ.length ≤ n ∧
      bsq (subO1 a (bwdP a σ (fan a h ε w))) = 0} with hD
  have hDc : D.Countable := by
    refine Set.Countable.mono ?_ (hD1 ε n)
    intro w hw
    exact ⟨lt_of_lt_of_le hw.1 hδ₁, hw.2⟩
  have hpre : IsPreconnected (Metric.ball (0 : ℂ) δ \ D) :=
    isPreconnected_ball_diff_countable hδ hDc
  have hAn : AnalyticOnNhd ℂ (lvlProd1 a h ε n) (Metric.ball (0 : ℂ) δ \ D) := by
    intro w hw
    obtain ⟨hwb, hwD⟩ := hw
    rw [Metric.mem_ball, dist_zero_right] at hwb
    refine analyticAt_lvlProd1_of_good
      (hfan := fun τ => (hF τ w (by simpa using lt_of_lt_of_le hwb hδf)).1)
      (hgood := fun σ hσ => ?_)
    intro hzero
    exact hwD (by rw [hD]; exact ⟨hwb, σ, hσ, hzero⟩)
  have h0mem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) δ \ D := by
    refine ⟨by simpa [Metric.mem_ball, dist_eq_norm] using hδ, ?_⟩
    intro h0D
    obtain ⟨-, σ, -, hz⟩ := h0D
    exact bwdP_fan_radicand_zero_ne ha0 ha1 hh ε σ hz
  have h0ne : lvlProd1 a h ε n 0 ≠ 0 := lvlProd1_zero_ne ha0 ha1 hh ε n
  have hcount := countable_zero_analytic_preconnected hpre hAn h0mem h0ne
  refine Set.Countable.mono ?_ (hDc.union hcount)
  rintro w ⟨hw, σ, hσ, hσ1⟩
  by_cases hwD : w ∈ D
  · exact Or.inl hwD
  · refine Or.inr ⟨⟨by simpa using hw, hwD⟩, ?_⟩
    have hmem : σ ∈ fanWords n := mem_fanWords.mpr hσ
    have hz : bsq (subO1 a (bwdP a σ (fan a h ε w))) - 1 = 0 := sub_eq_zero.mpr hσ1
    exact List.prod_eq_zero (List.mem_map.mpr ⟨σ, hmem, hz⟩)

/-- **The `O₂`-degenerate locus of backward chains from a stable fan is countable.**  For every
stable word `ε` and every length bound `j`, only countably many small parameters `w` have a backward
sign list `σ` of length at most `j` along which `bsq (subO2 a ·)` of the backward image of
`fan a h ε w` vanishes. -/
theorem bwdP_fan_subO2_degenerate_countable {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {r : ℝ} (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : List Bool) (j : ℕ),
      {w : ℂ | ‖w‖ < δ ∧ ∃ σ : List Bool, σ.length ≤ j ∧
        bsq (subO2 a (bwdP a σ (fan a h ε w))) = 0}.Countable := by
  obtain ⟨Ke, Lam, Q, δf, hKe, hLam, hQ, hδf, hF⟩ := fan_induction ha0 ha1 hh
  obtain ⟨δ₁, hδ₁pos, hD1⟩ := bwdP_fan_degenerate_countable ha0 ha1 hh
  set δ : ℝ := min δf δ₁ with hδdef
  have hδ0 : 0 < δ := lt_min hδf hδ₁pos
  have hδf' : δ ≤ δf := min_le_left _ _ 
  have hδ₁' : δ ≤ δ₁ := min_le_right _ _
  refine ⟨δ, hδ0, fun ε j => ?_⟩
  -- the two countable building blocks
  have hR : ∀ n : ℕ, {w : ℂ | ‖w‖ < δ ∧ ∃ σ : List Bool, σ.length = n ∧
      bsq (subO1 a (bwdP a σ (fan a h ε w))) = 1}.Countable :=
    fun n => lvlProd1_zeroLocus_countable ha0 ha1 hh hδ0 hδf' hδ₁' hF hD1 ε n
  have hD1' : ∀ n : ℕ, {w : ℂ | ‖w‖ < δ ∧ ∃ σ : List Bool, σ.length ≤ n ∧
      bsq (subO1 a (bwdP a σ (fan a h ε w))) = 0}.Countable := by
    intro n
    refine Set.Countable.mono ?_ (hD1 ε n)
    intro w hw
    exact ⟨lt_of_lt_of_le hw.1 hδ₁', hw.2⟩
  have hmain : ∀ n : ℕ, (degSet2 a h ε δ n).Countable := by
    intro n
    induction n with
    | zero =>
        refine Set.Countable.mono ?_ (zeroLocus_subO2_fan_countable ha0 ha1 hh hδ0 hδf' hF ε)
        rintro w ⟨hw, σ, hσ, hz⟩
        have hσ0 : σ = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hσ)
        subst hσ0
        exact ⟨hw, by simpa [bwdP_nil] using hz⟩
    | succ n ih =>
        refine Set.Countable.mono ?_ ((ih.union (hD1' n)).union (hR n))
        rintro w ⟨hw, σ, hσ, hz⟩
        by_cases hle : σ.length ≤ n
        · exact Or.inl (Or.inl ⟨hw, σ, hle, hz⟩)
        · have hlen : σ.length = n + 1 := by omega
          obtain ⟨τ, t, hτ, hτlen⟩ := exists_append_singleton_of_length_eq_succ hlen
          subst hτ
          rcases subO2_degenerate_parent τ t (P := fan a h ε w) (by simpa using hz) with hrc | hrc
          · exact Or.inl (Or.inr ⟨hw, τ, by rw [hτlen], hrc⟩)
          · exact Or.inr ⟨hw, τ, hτlen, hrc⟩
  exact hmain j

end

end Work.EQ
