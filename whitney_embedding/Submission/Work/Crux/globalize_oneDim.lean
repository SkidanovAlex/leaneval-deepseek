import Mathlib
import Submission.Work.Noncompact.ProperLine.flatGlue2
import Submission.Work.Noncompact.CompressionTube.exists_smooth_squash
import Submission.Work.Crux.exists_contDiff_iteratedDeriv

/-!
# Globalising a germ on a half-line (one-dimensional, vector-valued)

A function `F : ℝ → E` which is `C^∞` at `0` and `C^∞` on `(0,r)` admits a global `C^∞`
extension which agrees with `F` on `[0,r/8)` and is confined to a small ball on `(-∞,0]`.

This is the one-dimensional engine behind `Work.Crux.contMDiffAt_Icc_globalize`: the
hypothesis there is *pointwise* `C^∞` on `[0,1]`, which does **not** give a neighbourhood of
smoothness, so the naive "cut off with a bump function" argument does not apply.  Instead we use
Borel's theorem (`exists_contDiff_iteratedDeriv`) to build a global `C^∞` function with the same
infinite jet as `F` at `0`, and glue it to `F` by the (flat) gluing lemma.
-/

open scoped ContDiff Topology
open Set Filter

namespace Work.Crux

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The standard smooth bump on `ℝ`, equal to `1` on `[-1/2,1/2]` and supported in `(-1,1)`. -/
def confBump : ContDiffBump (0 : ℝ) := ⟨1/2, 1, by norm_num, by norm_num⟩

lemma confBump_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) confBump :=
  ContDiffBump.contDiff confBump

/-- `confine δ x = x * χ (x/δ)`: the identity on `[-δ/2, δ/2]`, supported in `(-δ,δ)`. -/
def confine (δ : ℝ) (x : ℝ) : ℝ := x * confBump (x / δ)

lemma confine_contDiff (δ : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (confine δ) := by
  unfold confine
  exact contDiff_id.mul (confBump_contDiff.comp (by fun_prop))

lemma confine_id_of_abs_le {δ x : ℝ} (hδ : 0 < δ) (hx : |x| ≤ δ / 2) :
    confine δ x = x := by
  unfold confine
  have h1 : x / δ ∈ Metric.closedBall (0 : ℝ) confBump.rIn := by
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_div, abs_of_pos hδ]
    rw [div_le_iff₀ hδ]
    rw [show confBump.rIn = 1/2 from rfl]
    linarith
  rw [ContDiffBump.one_of_mem_closedBall confBump h1, mul_one]

lemma confine_abs_le {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : |confine δ x| ≤ δ := by
  unfold confine
  rw [abs_mul]
  rcases lt_or_ge |x| δ with h | h
  · calc |x| * |confBump (x / δ)| ≤ |x| * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg x)
          rw [abs_of_nonneg (ContDiffBump.nonneg confBump)]
          exact ContDiffBump.le_one confBump
       _ = |x| := by ring
       _ ≤ δ := h.le
  · have hzero : confBump (x / δ) = 0 := by
      apply ContDiffBump.zero_of_le_dist (f := confBump)
      rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hδ]
      rw [show confBump.rOut = 1 from rfl]
      rw [one_le_div hδ]
      exact h
    rw [hzero, abs_zero, mul_zero]
    exact hδ.le

lemma confine_eventuallyEq_id {δ : ℝ} (hδ : 0 < δ) :
    (confine δ) =ᶠ[𝓝 (0:ℝ)] id := by
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Set.Ioo (-(δ/2)) (δ/2), Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
  intro x hx
  simp only [id_eq]
  exact confine_id_of_abs_le hδ (abs_le.mpr ⟨le_of_lt hx.1, le_of_lt hx.2⟩)

/-- **Globalisation of a germ on the right half-line.**  If `F` is `C^∞` at `0` and `C^∞` on
`(0,r)`, then there is a global `C^∞` `Ψ` with `Ψ = F` on `[0, r/8)` and `‖Ψ x - F 0‖ < ε` for
`x ≤ 0`. -/
theorem exists_contDiff_eqOn_Ico_of_contDiffAt {F : ℝ → E} {r : ℝ} (hr : 0 < r)
    (hF0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F 0)
    (hFr : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F (Set.Ioo 0 r))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Ψ : ℝ → E, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
      (∀ x ∈ Set.Ico 0 (r/8), Ψ x = F x) ∧
      (∀ x : ℝ, x ≤ 0 → ‖Ψ x - F 0‖ < ε) := by
  classical
  -- 1. Borel: a global smooth function with the jet of `F` at `0`.
  let c : ℕ → E := fun k => iteratedDeriv k F 0
  obtain ⟨B, hBsm, hBjet⟩ := exists_contDiff_iteratedDeriv (E := E) c
  have hB0 : B 0 = F 0 := by
    have h := hBjet 0
    simpa [c] using h
  -- 2. a radius on which `B` is close to `F 0`
  obtain ⟨η, hη, hηB⟩ : ∃ η : ℝ, 0 < η ∧ ∀ y : ℝ, |y| ≤ η → B y ∈ Metric.ball (F 0) ε := by
    have hcont : ContinuousAt B 0 := hBsm.continuous.continuousAt
    have hev : ∀ᶠ y in 𝓝 (0:ℝ), B y ∈ Metric.ball (B 0) ε :=
      hcont.eventually (Metric.ball_mem_nhds (B 0) hε)
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ, hδ, hδ'⟩ := hev
    refine ⟨δ/2, by linarith, fun y hy => ?_⟩
    have hy' : dist y (0:ℝ) < δ := by rw [Real.dist_eq, sub_zero]; linarith
    simpa [hB0] using hδ' hy'
  -- 3. the confined left piece
  set σ : ℝ → ℝ := confine η with hσdef
  have hσsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ := confine_contDiff η
  set U : ℝ → E := fun x => B (σ x) with hUdef
  have hUsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U := hBsm.comp hσsm
  have hUev : U =ᶠ[𝓝 (0:ℝ)] B := by
    filter_upwards [confine_eventuallyEq_id hη] with x hx
    show B (σ x) = B x
    rw [hσdef]
    simpa using congrArg B hx
  have hUjet : ∀ k : ℕ, iteratedDeriv k U 0 = c k := fun k => by
    rw [hUev.iteratedDeriv_eq k]
    exact hBjet k
  have hUbound : ∀ x : ℝ, x ≤ 0 → ‖U x - F 0‖ < ε := by
    intro x _
    have h1 : |σ x| ≤ η := by
      simp only [hσdef, hUdef]
      exact confine_abs_le hη x
    have h2 := hηB (σ x) h1
    rw [Metric.mem_ball] at h2
    simpa [hUdef, Real.dist_eq, dist_eq_norm] using h2
  -- 4. the right piece: `F` reparametrised by a squash so that it stays in `(0,r)`
  obtain ⟨τ, hτsm, hτmono, -, hτid, hτlt, -⟩ :=
    Work.Noncompact.CompressionTube.exists_smooth_squash (r/4) (r/2) (by linarith)
  set V : ℝ → E := fun x => F (τ x) with hVdef
  have hVeqF : V =ᶠ[𝓝 (0:ℝ)] F := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    refine ⟨Set.Iio (r/4), Iio_mem_nhds (by linarith), fun x hx => ?_⟩
    simp only [hVdef]
    rw [hτid x (le_of_lt hx)]
  have hV0 : V 0 = F 0 := by
    simp only [hVdef]
    rw [hτid 0 (by linarith)]
  have hVat : ∀ x : ℝ, 0 < x → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V x := by
    intro x hx
    have hτx : τ x ∈ Set.Ioo 0 r := by
      refine ⟨?_, ?_⟩
      · have h := hτmono hx
        rw [hτid 0 (by linarith)] at h
        exact h
      · have h := hτlt x
        linarith
    exact (hFr.contDiffAt (isOpen_Ioo.mem_nhds hτx)).comp x hτsm.contDiffAt
  have hVat0 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V 0 :=
    hF0.congr_of_eventuallyEq hVeqF
  have hVsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V (Set.Ici 0) := by
    intro x hx
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with rfl | hx'
    · exact hVat0.contDiffWithinAt
    · exact (hVat x hx').contDiffWithinAt
  have hVjet : ∀ k : ℕ, iteratedDerivWithin k V (Set.Ici 0) 0 = c k := by
    intro k
    have hVk : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) V 0 :=
      hVat0.of_le (WithTop.coe_le_coe.mpr le_top)
    have hFk : ContDiffAt ℝ ((k : ℕ) : WithTop ℕ∞) F 0 :=
      hF0.of_le (WithTop.coe_le_coe.mpr le_top)
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) hVk (Set.mem_Ici.mpr le_rfl),
      hVeqF.iteratedDeriv_eq k]
  -- 5. glue `U` and `V` at `0`
  have hB_at : ∀ k : ℕ, ContDiffAt ℝ ((k:ℕ) : WithTop ℕ∞) B 0 := fun k =>
    hBsm.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hU_at : ∀ k : ℕ, ContDiffAt ℝ ((k:ℕ) : WithTop ℕ∞) U 0 := fun k =>
    hUsm.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  have hUw : ∀ k : ℕ, ContDiffWithinAt ℝ ((k:ℕ) : WithTop ℕ∞) U (Set.Iic 0) 0 :=
    fun k => (hU_at k).contDiffWithinAt
  have hBw : ∀ k : ℕ, ContDiffWithinAt ℝ ((k:ℕ) : WithTop ℕ∞) B (Set.Iic 0) 0 :=
    fun k => (hB_at k).contDiffWithinAt
  have hUflat : ∀ k : ℕ, 0 < k →
      iteratedDerivWithin k (U - B) (Set.Iic 0) 0 = 0 := by
    intro k _
    rw [iteratedDerivWithin_sub (Set.mem_Iic.mpr le_rfl) (uniqueDiffOn_Iic 0) (hUw k) (hBw k)]
    have h1 : iteratedDerivWithin k U (Set.Iic 0) 0 = c k := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Iic 0) (hU_at k) (Set.mem_Iic.mpr le_rfl)]
      exact hUjet k
    have h2 : iteratedDerivWithin k B (Set.Iic 0) 0 = c k := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Iic 0) (hB_at k) (Set.mem_Iic.mpr le_rfl)]
      exact hBjet k
    rw [h1, h2, sub_self]
  have hVw : ∀ k : ℕ, ContDiffWithinAt ℝ ((k:ℕ) : WithTop ℕ∞) V (Set.Ici 0) 0 :=
    fun k => (hVsm.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffWithinAt (Set.mem_Ici.mpr le_rfl)
  have hBw' : ∀ k : ℕ, ContDiffWithinAt ℝ ((k:ℕ) : WithTop ℕ∞) B (Set.Ici 0) 0 :=
    fun k => (hB_at k).contDiffWithinAt
  have hVflat : ∀ k : ℕ, 0 < k →
      iteratedDerivWithin k (V - B) (Set.Ici 0) 0 = 0 := by
    intro k _
    rw [iteratedDerivWithin_sub (Set.mem_Ici.mpr le_rfl) (uniqueDiffOn_Ici 0) (hVw k) (hBw' k)]
    have h2 : iteratedDerivWithin k B (Set.Ici 0) 0 = c k := by
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0) (hB_at k) (Set.mem_Ici.mpr le_rfl)]
      exact hBjet k
    rw [hVjet k, h2, sub_self]
  have hU0 : U 0 = B 0 := by
    simp [hUdef, hσdef, confine]
  have h0 : (U - B) 0 = (V - B) 0 := by
    simp only [Pi.sub_apply, hV0, hU0, hB0]
  have hglueflat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.Noncompact.ProperLine.flatGlue (U - B) (V - B) 0) 0 := by
    rw [contDiffAt_infty]
    intro n
    exact Work.Noncompact.ProperLine.contDiffAt_flatGlue_nat n
      ((hUsm.sub hBsm).contDiffOn) ((hVsm.sub hBsm.contDiffOn)) h0 hUflat hVflat
  have hdecomp : Work.Noncompact.ProperLine.flatGlue U V 0 =
      B + Work.Noncompact.ProperLine.flatGlue (U - B) (V - B) 0 := by
    funext x
    unfold Work.Noncompact.ProperLine.flatGlue
    simp only [Pi.add_apply, Pi.sub_apply]
    by_cases h : x ≤ 0
    · simp only [h, if_true]
      abel
    · simp only [h, if_false]
      abel
  have hglue : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.Noncompact.ProperLine.flatGlue U V 0) 0 := by
    rw [hdecomp]
    exact hBsm.contDiffAt.add hglueflat
  refine ⟨Work.Noncompact.ProperLine.flatGlue U V 0, ?_, ?_, ?_⟩
  · -- smoothness everywhere
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_trichotomy x 0 with h | h | h
    · refine hUsm.contDiffAt.congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Iio.mem_nhds h] with y hy
      exact Work.Noncompact.ProperLine.flatGlue_of_le (le_of_lt hy)
    · subst h; exact hglue
    · refine (hVat x h).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioi.mem_nhds h] with y hy
      exact Work.Noncompact.ProperLine.flatGlue_of_gt hy
  · intro x hx
    have hxr : x ≤ r/4 := by linarith [hx.2, hr]
    rcases eq_or_lt_of_le hx.1 with rfl | hx'
    · rw [Work.Noncompact.ProperLine.flatGlue_of_le le_rfl]
      rw [hU0, hB0]
    · rw [Work.Noncompact.ProperLine.flatGlue_of_gt hx']
      show V x = F x
      simp only [hVdef]
      rw [hτid x hxr]
  · intro x hx
    rw [Work.Noncompact.ProperLine.flatGlue_of_le hx]
    exact hUbound x hx

end

end Work.Crux
