import Mathlib
import Submission.Work.Anchor.anchor_data
import Submission.Work.Anchor.engine_defs
import Submission.Work.Anchor.Xi_contDiffOn
import Submission.Work.Analysis.Calculus.contDiff_dslope

/-!
# `Xif` is `C^∞`

`Work.Anchor.Xif n h` is the source of the windowed anchor system: the counter-term `Xibase`
plus the cut-off version of the perturbation `Xi n h - Xi n 0` together with the frozen tail
`∫_σ in 19/20..1, (ΘM n h - ΘM n 0)(s,σ,baseState σ)`.

All the summands are `C^∞`: the paper's `Ξ` is `C^∞` on the anchor window (`Xi_contDiffOn`), and
the data built from the *manifest* kernel `ΘM` and from `Godd` are `C^∞` on `RegionT`/`RegionG`
(`AnchorInputs.thetaM_smooth`, `AnchorInputs.godd_smooth`).  The only non-trivial part is the
*moving* integral appearing in `Xibase`, handled by the substitution `σ = s + u (b - s)`.

The file also contains the general toolkits used for that:
* `C^∞`-smoothness of parametric interval integrals on an open parameter set, for `E`-valued
  integrands (the `E`-valued analogue of `Work.Anchor.contDiffOn_intervalIntegral_parametric`);
* the same for a *fixed* interval when the integrand is only known to be smooth on `U ×ˢ J`
  (patched by a bump supported in `J`);
* the same for a *variable lower limit*, by the substitution `σ = s + u (b - s)`.
-/

namespace Work.Anchor

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra Work.OddVolterra.KernelExt

/-! ## Toolkit -/

section Toolkit

/-- **Smoothness of a parametric interval integral, `E`-valued, on an open parameter set.** -/
theorem contDiffOn_intervalIntegral_parametric_E
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [ProperSpace P] [HasContDiffBump P]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : P × ℝ → E} {U : Set P} (hU : IsOpen U) {a b : ℝ}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G (U ×ˢ Set.univ)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun q : P => ∫ t in a..b, G (q, t)) U := by
  intro q₀ hq₀
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hq₀)
  let β : ContDiffBump q₀ := ⟨r / 4, r / 2, by linarith, by linarith⟩
  have hrIn : β.rIn = r / 4 := rfl
  have hrOut : β.rOut = r / 2 := rfl
  have hball : ∀ x : P, x ∈ Metric.closedBall q₀ β.rOut → x ∈ U := fun x hx => by
    refine hsub (Metric.closedBall_subset_ball (by linarith) ?_)
    rwa [hrOut] at hx
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun p : P × ℝ => (β : P → ℝ) p.1 • G p) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    rcases le_or_gt (dist p.1 q₀) β.rOut with hle | hlt
    · have hpU : p.1 ∈ U := hball p.1 (Metric.mem_closedBall.mpr hle)
      have h1 : ContDiffAt ℝ (⊤ : ℕ∞) (fun p : P × ℝ => (β : P → ℝ) p.1) p :=
        (β.contDiff (n := (⊤ : ℕ∞))).contDiffAt.comp p contDiffAt_fst
      have h2 : ContDiffAt ℝ (⊤ : ℕ∞) G p :=
        hG.contDiffAt ((hU.prod isOpen_univ).mem_nhds ⟨hpU, Set.mem_univ _⟩)
      exact h1.smul h2
    · have hev : (fun p' : P × ℝ => (β : P → ℝ) p'.1 • G p') =ᶠ[𝓝 p] (fun _ => (0 : E)) := by
        have hopen : IsOpen {x : P | β.rOut < dist x q₀} :=
          isOpen_lt continuous_const (continuous_id.dist continuous_const)
        filter_upwards [hopen.prod isOpen_univ |>.mem_nhds ⟨hlt, Set.mem_univ _⟩] with p' hp'
        rw [ContDiffBump.zero_of_le_dist β (le_of_lt hp'.1), zero_smul]
      exact (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq hev
  have hint : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : P => ∫ t in a..b, (β : P → ℝ) q • G (q, t)) :=
    Work.Analysis.Calculus.contDiff_intervalIntegral_parametric_top
      (f := fun q t => (β : P → ℝ) q • G (q, t)) hsm
  have heq : (fun q : P => ∫ t in a..b, G (q, t)) =ᶠ[𝓝 q₀]
      (fun q : P => ∫ t in a..b, (β : P → ℝ) q • G (q, t)) := by
    filter_upwards [Metric.ball_mem_nhds q₀ (ε := β.rIn) (by rw [hrIn]; linarith)] with q hq
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    have h1 : (β : P → ℝ) q = 1 := by
      refine ContDiffBump.one_of_mem_closedBall β (Metric.mem_closedBall.mpr ?_)
      rw [Metric.mem_ball, hrIn] at hq
      exact le_of_lt hq
    rw [h1, one_smul]
  exact (hint.contDiffAt.congr_of_eventuallyEq heq).contDiffWithinAt

/-- Patching the integration variable with a bump supported inside `J`: if `F` is smooth on
`U ×ˢ J` and `tsupport ψ ⊆ J`, then `(s,σ) ↦ ψ σ • F s σ` is smooth on `U ×ˢ univ`. -/
lemma contDiffOn_smul_snd_of_contDiffOn {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : ℝ → ℝ → E} {U J : Set ℝ} (hU : IsOpen U) (hJ : IsOpen J)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => F p.1 p.2) (U ×ˢ J))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hsub : tsupport ψ ⊆ J) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => ψ p.2 • F p.1 p.2) (U ×ˢ Set.univ) := by
  intro p hp
  by_cases hmem : p.2 ∈ tsupport ψ
  · have h2 : p.2 ∈ J := hsub hmem
    have hψat : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => ψ q.2) p :=
      hψ.contDiffAt.comp p contDiffAt_snd
    have hFat : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => F q.1 q.2) p :=
      hF.contDiffAt ((hU.prod hJ).mem_nhds ⟨hp.1, h2⟩)
    exact (hψat.smul hFat).contDiffWithinAt
  · have hmem' : (tsupport ψ)ᶜ ∈ 𝓝 p.2 := (isClosed_tsupport ψ).isOpen_compl.mem_nhds hmem
    have hev : (fun q : ℝ × ℝ => ψ q.2 • F q.1 q.2) =ᶠ[𝓝 p] (fun _ => (0 : E)) := by
      filter_upwards [(continuous_snd.tendsto p).eventually hmem'] with q hq
      have h0 : ψ q.2 = 0 := by
        by_contra hc
        exact hq (subset_tsupport ψ (Function.mem_support.mpr hc))
      rw [h0, zero_smul]
    exact (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq hev |>.contDiffWithinAt

/-- **Smoothness of a parametric interval integral over a fixed interval**, when the integrand is
only known to be smooth on `U ×ˢ J`; the bump `ψ` (`= 1` on `[a,b]`, supported in `J`) patches
it to a function smooth on `U ×ˢ univ`. -/
lemma contDiffOn_integral_fixed_of_contDiffOn {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : ℝ → ℝ → E} {U J : Set ℝ} (hU : IsOpen U)
    (hJ : IsOpen J) {a b : ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => F p.1 p.2) (U ×ˢ J))
    {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψJ : tsupport ψ ⊆ J)
    (hψ1 : ∀ t ∈ Set.uIcc a b, ψ t = 1) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun s => ∫ t in a..b, F s t) U := by
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => ψ p.2 • F p.1 p.2) (U ×ˢ Set.univ) :=
    contDiffOn_smul_snd_of_contDiffOn hU hJ hF hψ hψJ
  have hInt : ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => ∫ t in a..b, ψ t • F s t) U :=
    contDiffOn_intervalIntegral_parametric_E (P := ℝ) hU
      (G := fun p : ℝ × ℝ => ψ p.2 • F p.1 p.2) hG
  refine hInt.congr (fun s _ => ?_)
  exact intervalIntegral.integral_congr (fun t ht => by rw [hψ1 t ht, one_smul])

/-- **Smoothness of a parametric integral with a variable lower limit.**  If `F` is smooth on
`U ×ˢ J`, and the substitution map `(s,u) ↦ s + u * (b - s)` sends `U ×ˢ tsupport χ` into `J`
(so that `F` is only ever evaluated where it is smooth), then `s ↦ ∫_σ in s..b, F s σ` is smooth
on `U`.  The bump `χ` is `1` on `[0,1]`; replacing the integration over `[0,1]` by an integration
over all of `ℝ` with the factor `χ` is what makes the parametric integral lemma applicable. -/
lemma contDiffOn_integral_lower_of_contDiffOn {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {F : ℝ → ℝ → E} {U J : Set ℝ} (hU : IsOpen U)
    (hJ : IsOpen J) {b : ℝ}
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => F p.1 p.2) (U ×ˢ J))
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ1 : ∀ u ∈ Set.uIcc (0 : ℝ) 1, χ u = 1)
    (hmaps : ∀ s ∈ U, ∀ u ∈ tsupport χ, s + u * (b - s) ∈ J) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun s => ∫ σ in s..b, F s σ) U := by
  have hG : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => χ p.2 • ((b - p.1) • F p.1 (p.1 + p.2 * (b - p.1))))
      (U ×ˢ Set.univ) := by
    intro p hp
    by_cases hmem : p.2 ∈ tsupport χ
    · have hJp : p.1 + p.2 * (b - p.1) ∈ J := hmaps p.1 hp.1 p.2 hmem
      have hFat : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => F q.1 q.2)
          (p.1, p.1 + p.2 * (b - p.1)) :=
        hF.contDiffAt ((hU.prod hJ).mem_nhds ⟨hp.1, hJp⟩)
      have hsub : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun q : ℝ × ℝ => (q.1, q.1 + q.2 * (b - q.1))) p := by fun_prop
      have hcomp : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun q : ℝ × ℝ => F q.1 (q.1 + q.2 * (b - q.1))) p := by
        simpa only [Function.comp_def] using hFat.comp p hsub
      have hχat : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => χ q.2) p :=
        hχ.contDiffAt.comp p contDiffAt_snd
      have hlin : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : ℝ × ℝ => b - q.1) p := by fun_prop
      exact (hχat.smul (hlin.smul hcomp)).contDiffWithinAt
    · have hmem' : (tsupport χ)ᶜ ∈ 𝓝 p.2 := (isClosed_tsupport χ).isOpen_compl.mem_nhds hmem
      have hev : (fun q : ℝ × ℝ => χ q.2 • ((b - q.1) • F q.1 (q.1 + q.2 * (b - q.1))))
          =ᶠ[𝓝 p] (fun _ => (0 : E)) := by
        filter_upwards [(continuous_snd.tendsto p).eventually hmem'] with q hq
        have h0 : χ q.2 = 0 := by
          by_contra hc
          exact hq (subset_tsupport χ (Function.mem_support.mpr hc))
        rw [h0, zero_smul]
      exact (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq hev |>.contDiffWithinAt
  have hInt : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => ∫ u in (0 : ℝ)..1, χ u • ((b - s) • F s (s + u * (b - s)))) U :=
    contDiffOn_intervalIntegral_parametric_E (P := ℝ) hU
      (G := fun p : ℝ × ℝ => χ p.2 • ((b - p.1) • F p.1 (p.1 + p.2 * (b - p.1)))) hG
  refine hInt.congr (fun s hs => ?_)
  have hstep : (∫ u in (0 : ℝ)..1, χ u • ((b - s) • F s (s + u * (b - s))))
      = ∫ u in (0 : ℝ)..1, (b - s) • F s (s + u * (b - s)) :=
    intervalIntegral.integral_congr
      (f := fun u : ℝ => χ u • ((b - s) • F s (s + u * (b - s))))
      (g := fun u : ℝ => (b - s) • F s (s + u * (b - s)))
      (fun u hu => by simp only [hχ1 u hu, one_smul])
  rw [hstep]
  by_cases hbs : b - s = 0
  · have hsb : s = b := by linarith
    subst hsb
    simp [intervalIntegral.integral_same]
  · have hcomp := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 1)
        (c := b - s) (f := fun σ : ℝ => F s σ) hbs s
    have harg : ∀ u : ℝ, s + u * (b - s) = (b - s) * u + s := fun u => by ring
    have h1 : (∫ u in (0 : ℝ)..1, (b - s) • F s (s + u * (b - s)))
        = (b - s) • ∫ x in (0 : ℝ)..1, F s ((b - s) * x + s) := by
      rw [intervalIntegral.integral_smul]
      congr 1
      exact intervalIntegral.integral_congr
        (f := fun u : ℝ => F s (s + u * (b - s)))
        (g := fun x : ℝ => F s ((b - s) * x + s))
        (fun u _ => by simp only [harg])
    rw [h1, hcomp]
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
    rw [smul_smul, mul_inv_cancel₀ hbs, one_smul]

end Toolkit

/-! ## The concrete window and bumps -/

/-- The open neighbourhood of `tsupport cs` on which the inner data is smooth. -/
def Ux : Set ℝ := Set.Ioo (482 / 1000 : ℝ) (968 / 1000)

/-- The `σ`-range on which the manifest `Θ` is smooth; it contains `Ux` and `[19/20, 1]`. -/
def Jx : Set ℝ := Set.Ioo (481 / 1000 : ℝ) (102 / 100)

lemma isOpen_Ux : IsOpen Ux := isOpen_Ioo

lemma isOpen_Jx : IsOpen Jx := isOpen_Ioo

lemma Ux_subset_RegionX : Ux ⊆ RegionX := by
  intro s hs
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- `tsupport cs ⊆ Ux`, the hypothesis the cut-off multiplication needs. -/
lemma tsupport_cs_subset_Ux : tsupport (fun s : ℝ => (cs : ℝ → ℝ) s) ⊆ Ux := by
  have hsupp : Function.support (fun s : ℝ => (cs : ℝ → ℝ) s) ⊆
      Set.Icc (485 / 1000) (965 / 1000) := by
    intro s hs
    rw [Function.mem_support] at hs
    have h1 : |s - 29 / 40| < 6 / 25 := by
      by_contra hle
      exact hs (cs_eq_zero (not_lt.mp hle))
    rw [abs_lt] at h1
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  refine (closure_minimal hsupp isClosed_Icc).trans ?_
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

/-- The substitution bump in the `u` variable: `1` on `[0,1]`, supported in
`[-1/500, 1 + 1/500]`. -/
def chiU : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 2, 1 / 2 + 1 / 500, by norm_num, by norm_num⟩

lemma chiU_rIn : chiU.rIn = 1 / 2 := rfl

lemma chiU_rOut : chiU.rOut = 1 / 2 + 1 / 500 := rfl

lemma tsupport_chiU_subset :
    tsupport (fun u : ℝ => (chiU : ℝ → ℝ) u) ⊆ Set.Icc (-(1 / 500)) (1 + 1 / 500) := by
  have hsupp : Function.support (fun u : ℝ => (chiU : ℝ → ℝ) u) ⊆
      Set.Icc (-(1 / 500)) (1 + 1 / 500) := by
    intro u hu
    rw [Function.mem_support] at hu
    have h1 : |u - 1 / 2| < 1 / 2 + 1 / 500 := by
      by_contra hle
      exact hu (ContDiffBump.zero_of_le_dist chiU (by
        rw [chiU_rOut, Real.dist_eq]
        exact not_lt.mp hle))
    rw [abs_lt] at h1
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  exact closure_minimal hsupp isClosed_Icc

lemma chiU_one : ∀ u ∈ Set.uIcc (0 : ℝ) 1, (chiU : ℝ → ℝ) u = 1 := by
  intro u hu
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
  refine ContDiffBump.one_of_mem_closedBall chiU (Metric.mem_closedBall.mpr ?_)
  rw [chiU_rIn, Real.dist_eq, abs_le]
  exact ⟨by linarith [hu.1], by linarith [hu.2]⟩

/-- The elementary bound behind the substitution: for `s ∈ Ux` and `u` in the support of the
substitution bump, `σ = s + u (19/20 - s)` still lies in `Jx`, where the manifest `Θ` is
smooth. -/
lemma subst_bounds {s u : ℝ} (hs : s ∈ Ux)
    (hu : u ∈ tsupport (fun u : ℝ => (chiU : ℝ → ℝ) u)) :
    s + u * (19 / 20 - s) ∈ Jx := by
  have hu' := tsupport_chiU_subset hu
  have hlo : -(1 / 500 : ℝ) ≤ u := hu'.1
  have hhi : u ≤ 1 + 1 / 500 := hu'.2
  have hs1 : (482 / 1000 : ℝ) < s := hs.1
  have hs2 : s < (968 / 1000 : ℝ) := hs.2
  have hσ : s + u * (19 / 20 - s) = (1 - u) * s + u * (19 / 20) := by ring
  rw [hσ]
  rcases lt_or_ge u 1 with hu1 | hu1
  · have h3 : 0 < 1 - u := by linarith
    have hup : 0 < u * ((19 : ℝ) / 20 - 482 / 1000) + 482 / 1000 - 481 / 1000 := by
      nlinarith [mul_lt_mul_of_pos_left hs1 h3, hlo]
    have hup' : 0 < 482 / 1000 + u * ((19 : ℝ) / 20 - 482 / 1000) - 481 / 1000 := by
      nlinarith [mul_lt_mul_of_pos_left hs1 h3, hlo]
    constructor
    · nlinarith [mul_lt_mul_of_pos_left hs1 h3, hlo]
    · nlinarith [mul_lt_mul_of_pos_left hs2 h3, hlo]
  · have h3 : 1 - u ≤ 0 := by linarith
    have hb1 : (1 - u) * (968 / 1000) ≤ (1 - u) * s :=
      mul_le_mul_of_nonpos_left (le_of_lt hs2) h3
    have hb2 : (1 - u) * s ≤ (1 - u) * (482 / 1000) :=
      mul_le_mul_of_nonpos_left (le_of_lt hs1) h3
    constructor
    · nlinarith [hb1, hhi]
    · nlinarith [hb2, hhi]

/-- The `σ`-bump of the frozen tail: `1` on `[19/20, 1]`, supported in `Jx`. -/
def psiT : ContDiffBump (975 / 1000 : ℝ) := ⟨1 / 40, 26 / 1000, by norm_num, by norm_num⟩

lemma psiT_rIn : psiT.rIn = 1 / 40 := rfl

lemma psiT_rOut : psiT.rOut = 26 / 1000 := rfl

lemma tsupport_psiT_subset : tsupport (fun σ : ℝ => (psiT : ℝ → ℝ) σ) ⊆ Jx := by
  have hsupp : Function.support (fun σ : ℝ => (psiT : ℝ → ℝ) σ) ⊆
      Set.Icc (949 / 1000) (1001 / 1000) := by
    intro σ hσ
    rw [Function.mem_support] at hσ
    have h1 : |σ - 975 / 1000| < 26 / 1000 := by
      by_contra hle
      exact hσ (ContDiffBump.zero_of_le_dist psiT (by
        rw [psiT_rOut, Real.dist_eq]
        exact not_lt.mp hle))
    rw [abs_lt] at h1
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  refine (closure_minimal hsupp isClosed_Icc).trans ?_
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma psiT_one : ∀ t ∈ Set.uIcc (19 / 20 : ℝ) 1, (psiT : ℝ → ℝ) t = 1 := by
  intro t ht
  rw [Set.uIcc_of_le (by norm_num : (19 : ℝ) / 20 ≤ 1)] at ht
  refine ContDiffBump.one_of_mem_closedBall psiT (Metric.mem_closedBall.mpr ?_)
  rw [psiT_rIn, Real.dist_eq, abs_le]
  exact ⟨by linarith [ht.1], by linarith [ht.2]⟩

/-! ## The two data are smooth on the region -/

lemma thetaM_contDiffOn_Ux (n : ℕ) (H : AnchorInputs n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => ThetaM n h p.1 p.2 (baseState p.2)) (Ux ×ˢ Jx) := by
  have hsm := H.thetaM_smooth h hh hsmall
  have hγ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × ℝ => (p.1, p.2, baseState p.2)) := by
    refine contDiff_fst.prodMk (contDiff_snd.prodMk ?_)
    exact contDiff_baseState_eng.comp contDiff_snd
  have hmap : MapsTo (fun p : ℝ × ℝ => (p.1, p.2, baseState p.2)) (Ux ×ˢ Jx) RegionT := by
    rintro ⟨s, σ⟩ hp
    refine ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
      ⟨by linarith [hp.2.1], by linarith [hp.2.2]⟩, ?_⟩
    rw [sub_self, norm_zero]
    norm_num
  simpa only [Function.comp_def] using hsm.comp hγ.contDiffOn hmap

lemma godd_contDiffOn_Ux (n : ℕ) (H : AnchorInputs n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => Godd n h s (baseState s)) Ux := by
  have hsm := H.godd_smooth h hh hsmall
  have hγ : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (s, baseState s)) :=
    contDiff_id.prodMk contDiff_baseState_eng
  have hmap : MapsTo (fun s : ℝ => (s, baseState s)) Ux RegionG := by
    intro s hs
    refine ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ?_⟩
    rw [sub_self, norm_zero]
    norm_num
  simpa only [Function.comp_def] using hsm.comp (hγ.contDiffOn (s := Ux)) hmap

/-! ## The inner bracket of `Xibase` -/

/-- The bracket in `Xibase`: the defect of the base state, with the manifest integral cut to
`[s, wr]`. -/
def XifW (n : ℕ) (s : ℝ) : St :=
  Godd n 0 s (baseState s) - ∫ σ in s..wr, (cs : ℝ → ℝ) σ • ThetaM n 0 s σ (baseState σ)

lemma chiG_baseState (s : ℝ) : chiG s (baseState s) = (cs : ℝ → ℝ) s := by
  rw [chiG, sub_self, norm_zero, cz_eq_one (by norm_num : |(0 : ℝ)| ≤ 1 / 5), mul_one]

lemma chiT_baseState (s σ : ℝ) :
    chiT s σ (baseState σ) = (cs : ℝ → ℝ) s * (cs : ℝ → ℝ) σ := by
  rw [chiT, sub_self, norm_zero, cz_eq_one (by norm_num : |(0 : ℝ)| ≤ 1 / 5), mul_one]

lemma Gf_baseState (n : ℕ) (h : ℝ → ℝ) (s : ℝ) :
    Gf n h s (baseState s) = (cs : ℝ → ℝ) s • Godd n h s (baseState s) := by
  rw [Gf, chiG_baseState]

lemma Thf_baseState (n : ℕ) (h : ℝ → ℝ) (s σ : ℝ) :
    Thf n h s σ (baseState σ) =
      ((cs : ℝ → ℝ) s * (cs : ℝ → ℝ) σ) • ThetaM n h s σ (baseState σ) := by
  rw [Thf, chiT_baseState]

lemma integral_Thf_baseState (n : ℕ) (h : ℝ → ℝ) (s : ℝ) :
    (∫ σ in s..wr, Thf n h s σ (baseState σ)) =
      (cs : ℝ → ℝ) s • ∫ σ in s..wr, (cs : ℝ → ℝ) σ • ThetaM n h s σ (baseState σ) := by
  rw [← intervalIntegral.integral_smul]
  exact intervalIntegral.integral_congr
    (f := fun σ : ℝ => Thf n h s σ (baseState σ))
    (g := fun σ : ℝ => (cs : ℝ → ℝ) s • ((cs : ℝ → ℝ) σ • ThetaM n h s σ (baseState σ)))
    (fun σ _ => by simp only [Thf_baseState, smul_smul])

lemma Xibase_eq (n : ℕ) (s : ℝ) :
    Xibase n s = (cs : ℝ → ℝ) s • ((cs : ℝ → ℝ) s • XifW n s) := by
  simp only [Xibase, Gf_baseState, integral_Thf_baseState, XifW, smul_sub]

/-! ## The theorem -/

theorem Xif_contDiff (n : ℕ) (hn : 1 ≤ n) (H : Work.Anchor.AnchorInputs n) {h : ℝ → ℝ}
    (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100) :
    ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Work.Anchor.Xif n h s) := by
  -- the zero datum fulfils the hypotheses
  have hsmall0 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) s| ≤ 1 / 100 := by
    intro k hk s
    rw [iteratedDeriv_const_zero]
    norm_num
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) := by
    intro x hx
    rw [Function.mem_support] at hx
    exact absurd rfl hx
  -- the manifest data on the region
  have hΘh : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => ThetaM n h p.1 p.2 (baseState p.2)) (Ux ×ˢ Jx) :=
    thetaM_contDiffOn_Ux n H hh hsmall
  have hΘ0 : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => ThetaM n 0 p.1 p.2 (baseState p.2)) (Ux ×ˢ Jx) :=
    thetaM_contDiffOn_Ux n H contDiff_const hsmall0
  have hGodd : ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => Godd n 0 s (baseState s)) Ux :=
    godd_contDiffOn_Ux n H contDiff_const hsmall0
  -- the moving integral of `XifW`
  have hFmove : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => (cs : ℝ → ℝ) p.2 • ThetaM n 0 p.1 p.2 (baseState p.2)) (Ux ×ˢ Jx) :=
    ((ContDiffBump.contDiff cs).comp contDiff_snd).contDiffOn.smul hΘ0
  have hmove : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => ∫ σ in s..wr, (cs : ℝ → ℝ) σ • ThetaM n 0 s σ (baseState σ)) Ux :=
    contDiffOn_integral_lower_of_contDiffOn (F := fun s σ =>
        (cs : ℝ → ℝ) σ • ThetaM n 0 s σ (baseState σ)) isOpen_Ux isOpen_Jx hFmove
      (ContDiffBump.contDiff chiU) chiU_one (fun s hs u hu => subst_bounds hs hu)
  have hW : ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => XifW n s) Ux := by
    have := hGodd.sub hmove
    simpa only [XifW] using this
  -- `Xibase`
  have hcsU : ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => (cs : ℝ → ℝ) s) Ux :=
    (ContDiffBump.contDiff cs).contDiffOn
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => (cs : ℝ → ℝ) s • XifW n s) Ux :=
    hcsU.smul hW
  have hXibase : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Xibase n s) := by
    have h2 : ContDiff ℝ (⊤ : ℕ∞)
        (fun s : ℝ => (cs : ℝ → ℝ) s • ((cs : ℝ → ℝ) s • XifW n s)) :=
      eng_contDiff_smul_of_contDiffOn (f := fun s : ℝ => (cs : ℝ → ℝ) s)
        (g := fun s : ℝ => (cs : ℝ → ℝ) s • XifW n s) (U := Ux) isOpen_Ux
        (ContDiffBump.contDiff cs) h1 tsupport_cs_subset_Ux
    have heq : (fun s : ℝ => Xibase n s)
        = fun s : ℝ => (cs : ℝ → ℝ) s • ((cs : ℝ → ℝ) s • XifW n s) :=
      funext (fun s => Xibase_eq n s)
    rw [heq]
    exact h2
  -- the tail and the perturbation of `Ξ`
  have hTailF : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : ℝ × ℝ => ThetaM n h p.1 p.2 (baseState p.2) - ThetaM n 0 p.1 p.2 (baseState p.2))
      (Ux ×ˢ Jx) := hΘh.sub hΘ0
  have hTail : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => ∫ σ in wr..1,
        (ThetaM n h s σ (baseState σ) - ThetaM n 0 s σ (baseState σ))) Ux :=
    contDiffOn_integral_fixed_of_contDiffOn (F := fun s σ =>
        ThetaM n h s σ (baseState σ) - ThetaM n 0 s σ (baseState σ))
      isOpen_Ux isOpen_Jx hTailF (ContDiffBump.contDiff psiT) tsupport_psiT_subset psiT_one
  have hXi : ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => Xi n h s - Xi n 0 s) Ux :=
    ((Xi_contDiffOn n hn hh hsupp hsmall).sub
      (Xi_contDiffOn n hn contDiff_const hsupp0 hsmall0)).mono Ux_subset_RegionX
  have hbracket : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun s : ℝ => (Xi n h s - Xi n 0 s) + ∫ σ in wr..1,
        (ThetaM n h s σ (baseState σ) - ThetaM n 0 s σ (baseState σ))) Ux :=
    hXi.add hTail
  have hsecond : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => (cs : ℝ → ℝ) s • ((Xi n h s - Xi n 0 s) + ∫ σ in wr..1,
        (ThetaM n h s σ (baseState σ) - ThetaM n 0 s σ (baseState σ)))) :=
    eng_contDiff_smul_of_contDiffOn (f := fun s : ℝ => (cs : ℝ → ℝ) s)
      (g := fun s : ℝ => (Xi n h s - Xi n 0 s) + ∫ σ in wr..1,
        (ThetaM n h s σ (baseState σ) - ThetaM n 0 s σ (baseState σ)))
      (U := Ux) isOpen_Ux (ContDiffBump.contDiff cs) hbracket tsupport_cs_subset_Ux
  have hmain : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => Xibase n s + (cs : ℝ → ℝ) s • ((Xi n h s - Xi n 0 s) + ∫ σ in wr..1,
        (ThetaM n h s σ (baseState σ) - ThetaM n 0 s σ (baseState σ)))) :=
    hXibase.add hsecond
  simpa only [Xif] using hmain


end

end Work.Anchor
