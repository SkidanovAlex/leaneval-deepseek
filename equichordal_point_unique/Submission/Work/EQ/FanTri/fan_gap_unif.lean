import Mathlib
import Submission.Work.EQ.FanTri.Base
import Submission.Work.EQ.FanTri.BranchCompDefs
import Submission.Work.EQ.FanTri.analytic_quadratic_bound
import Submission.Work.EQ.FanTri.fan_deriv_fst_zero
import Submission.Work.EQ.FanTri.invBranch_true_second_order
import Submission.Work.EQ.FanTri.branchComp_lipschitz_scaled
import Submission.Work.EQ.FanUniform.fan_uniform_estimates
import Submission.Work.EQ.fan_sep
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.charVal_main
import Submission.Work.EQ.charVal_props
import Submission.Work.EQ.FanSep.germ_lip
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.germCHelpers
import Submission.Work.EQ.walk_bounds

/-!
# The big-gap limit, uniformly in the trailing word

`Work.EQ.FanTri.fan_gap_unif` (Rychlik Thm 7(3)): there is `δ > 0` such that for every prefix
`ε₀`, every diverging length sequence `s k → ∞`, and every family of trailing words `C k` with
`fan a h (C k) 0 = A₁` and the same characteristic value `charVal a h (C k) = μ`, the fan maps of
`ε₀ ++ true^{s k} ++ C k` converge uniformly on `B(0,δ)` to `u ↦ fan a h ε₀ (μ u)`.

The proof splits as follows.
* `fan_uniform_estimates` gives holomorphy of every fan on a common disc and the first-order
  bounds `‖x - centre‖ ≤ Ke‖u‖`, `‖y‖ ≤ Lam‖u‖‖x - a/2‖`.
* **Uniform quadratic contact.** `fan_deriv_fst_zero` says the abscissa of every fan has vanishing
  derivative at `0`; with `charVal a h C = μ` the second coordinate of `fan a h C` matches the one
  of `germC a h (μ ·)` to first order.  Cauchy's estimate (`analytic_quadratic_bound`) on the two
  coordinate differences therefore gives `‖fan a h C u - germC a h (μ * u)‖ ≤ Kq‖u‖²`, uniformly
  in the closed word `C` and in `μ` with `‖μ‖ ≤ 1`.
* **Contraction.** `Φ_j = fan a h (true^j ++ C)` satisfies `Φ_{j+1} = invBranch a true ∘ Φ_j ∘ (λ·)`
  and `L u = germC a h (μ u)` is a fixed point of the same relation.  The second-order expansion
  of `invBranch a true` at `A₁` (linear part `diag(-1, 1/λ)`) gives, after scaling by `λ`,
  `‖Φ_{j+1}(u) - L u‖ ≤ rate‖Φ_j(λ u) - L(λ u)‖ + O(‖u‖)‖Φ_j(λu) - L(λu)‖` with
  `rate = λ(1 + ε) < 1`, so the quadratic contact at `j = 0` propagates to all `j`.
* **Prefix.** `fan a h (ε₀ ++ δ) u = branchComp a ε₀ (fan a h δ (λ^{|ε₀|}u))`, and a finite
  composition of inverse branches is Lipschitz near `A₁`, so the general prefix follows. -/

namespace Work.EQ.FanTri

open Complex Filter _root_.Topology
open scoped Topology

noncomputable section

/-- The complex-rational form of `A₁` used by the older workspace lemmas (the definition of `A₁`
in `FanTri.branchComp_radius` is the real-cast form). -/
lemma A1_cform : ((-1 / 2 : ℂ), (0 : ℂ)) = A1 := by
  simp only [A1]
  refine Prod.ext ?_ ?_ <;> norm_num

lemma mem_ball_zero {δ : ℝ} {u : ℂ} : u ∈ Metric.ball (0 : ℂ) δ ↔ ‖u‖ < δ := by
  rw [Metric.mem_ball, dist_zero_right]

/-- Norm of a real number as a complex number. -/
lemma norm_ofReal' (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := RCLike.norm_ofReal x

/-- `invBranch a true` fixes `A₁`. -/
lemma invBranch_true_A1 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) : Work.EQ.invBranch a true A1 = A1 := by
  obtain ⟨ρ, hρ, -, hg0, hinv, -, -⟩ := germC_facts ha0 ha1 hh
  have hmem : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := by simpa using hρ
  have h := (hinv 0 hmem).2
  rw [mul_zero, hg0] at h
  rw [← A1_cform]
  exact h

/-- The composition of the `true` letters fixes `A₁`. -/
lemma branchComp_true_A1 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (k : ℕ) :
    branchComp a (List.replicate k true) A1 = A1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, branchComp_cons, ih]
      exact invBranch_true_A1 ha0 ha1 hh

/-- Prepending a run of principal letters to a word with centre `A₁` keeps the centre `A₁`. -/
lemma fan_replicate_true_centre {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (k : ℕ) {C : List Bool} (hC : fan a h C 0 = A1) :
    fan a h (List.replicate k true ++ C) 0 = A1 := by
  rw [fan_append_branchComp, mul_zero, hC, branchComp_true_A1 ha0 ha1 hh k]

/-- **Uniform deviation of a closed fan from its centre.**  On a small disc, uniformly in the
branch word `ε` and in the (principal) run of letters, a fan whose walk returns to `A₁` stays
within `Cd ‖u‖` of `A₁`. -/
lemma fan_deviation_bound {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ Cd δ1 : ℝ, 0 < Cd ∧ 0 < δ1 ∧ ∀ (ε : List Bool), fan a h ε 0 = A1 → ∀ u : ℂ,
      ‖u‖ < δ1 → ‖fan a h ε u - A1‖ ≤ Cd * ‖u‖ := by
  obtain ⟨δu, Ke, Lam, hδupos, hKepos, hLampos, hfan⟩ :=
    FanUniform.fan_uniform_estimates ha0 ha1 hh
  refine ⟨max Ke (Lam * (Ke * δu + (1 + a) / 2)) + 1, δu, by positivity, hδupos, ?_⟩
  intro ε hε u hu
  obtain ⟨-, hb⟩ := hfan ε
  obtain ⟨hb1, hb2⟩ := hb u (mem_ball_zero.mpr hu)
  have h1 : ‖(fan a h ε u).1 - A1.1‖ ≤ Ke * ‖u‖ := by
    have hh1 := hb1
    rwa [hε] at hh1
  have h2 : ‖(fan a h ε u).2 - A1.2‖ ≤ Lam * (Ke * δu + (1 + a) / 2) * ‖u‖ := by
    have hx : ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ ≤ Ke * δu + (1 + a) / 2 := by
      have hsplit : (fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)
          = ((fan a h ε u).1 - A1.1) + (A1.1 - ((a / 2 : ℝ) : ℂ)) := by
        simp only [A1]; ring
      have h4 : ‖A1.1 - ((a / 2 : ℝ) : ℂ)‖ = (1 + a) / 2 := by
        have h5 : A1.1 - ((a / 2 : ℝ) : ℂ) = ((-(1 + a) / 2 : ℝ) : ℂ) := by
          simp only [A1]; push_cast; ring
        rw [h5, norm_ofReal', abs_of_neg (by linarith)]
        ring
      have hKe : Ke * ‖u‖ < Ke * δu := mul_lt_mul_of_pos_left hu hKepos
      calc ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖
          = ‖((fan a h ε u).1 - A1.1) + (A1.1 - ((a / 2 : ℝ) : ℂ))‖ := by rw [hsplit]
        _ ≤ ‖(fan a h ε u).1 - A1.1‖ + ‖A1.1 - ((a / 2 : ℝ) : ℂ)‖ := norm_add_le _ _
        _ = ‖(fan a h ε u).1 - A1.1‖ + (1 + a) / 2 := by rw [h4]
        _ ≤ Ke * ‖u‖ + (1 + a) / 2 := add_le_add_left h1 _
        _ ≤ Ke * δu + (1 + a) / 2 := le_of_lt (add_lt_add_left hKe _)
    have hb2'' : ‖(fan a h ε u).2 - A1.2‖
        ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ := by
      simpa [A1] using hb2
    calc ‖(fan a h ε u).2 - A1.2‖
        ≤ Lam * ‖u‖ * ‖(fan a h ε u).1 - ((a / 2 : ℝ) : ℂ)‖ := hb2''
      _ ≤ Lam * ‖u‖ * (Ke * δu + (1 + a) / 2) := by
          refine mul_le_mul_of_nonneg_left hx ?_
          exact mul_nonneg hLampos.le (norm_nonneg u)
      _ = Lam * (Ke * δu + (1 + a) / 2) * ‖u‖ := by ring
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · refine le_trans h1 ?_
    have : Ke ≤ max Ke (Lam * (Ke * δu + (1 + a) / 2)) + 1 := by
      linarith [le_max_left Ke (Lam * (Ke * δu + (1 + a) / 2))]
    exact mul_le_mul_of_nonneg_right this (norm_nonneg u)
  · refine le_trans h2 ?_
    have : Lam * (Ke * δu + (1 + a) / 2)
        ≤ max Ke (Lam * (Ke * δu + (1 + a) / 2)) + 1 := by
      linarith [le_max_right Ke (Lam * (Ke * δu + (1 + a) / 2))]
    exact mul_le_mul_of_nonneg_right this (norm_nonneg u)

/-- **Uniform deviation of the germ from `A₁`** (first order, with any parameter `μ`, `‖μ‖ ≤ 1`). -/
lemma germC_deviation_bound {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ Cg δ2 : ℝ, 0 < Cg ∧ 0 < δ2 ∧ ∀ v : ℂ, ‖v‖ < δ2 → ‖germC a h v - A1‖ ≤ Cg * ‖v‖ := by
  obtain ⟨ρg, hρgpos, hgan, hg0, -, -, -⟩ := germC_facts ha0 ha1 hh
  have hmem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρg := by simpa using hρgpos
  have han : AnalyticAt ℂ (germC a h) 0 := hgan 0 hmem0
  have hfst : AnalyticAt ℂ (fun u : ℂ => (germC a h u).1 - A1.1) 0 :=
    ((ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt (germC a h 0)).comp han |>.sub analyticAt_const
  have hfst0 : (fun u : ℂ => (germC a h u).1 - A1.1) 0 = 0 := by
    simp only [Pi.sub_apply, hg0, A1]
    norm_num
  obtain ⟨δ₁, p₁, hδ₁, hp₁, hb₁⟩ := Work.EQ.FanSep.analytic_lipschitz hfst hfst0
  have hsnd : AnalyticAt ℂ (fun u : ℂ => (germC a h u).2) 0 :=
    ((ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt (germC a h 0)).comp han
  have hsnd0 : (fun u : ℂ => (germC a h u).2) 0 = 0 := by
    simp [hg0]
  obtain ⟨δ₂, p₂, hδ₂, hp₂, hb₂⟩ := Work.EQ.FanSep.analytic_lipschitz hsnd hsnd0
  refine ⟨max p₁ p₂, min δ₁ δ₂, by positivity, lt_min hδ₁ hδ₂, ?_⟩
  intro v hv
  have hv1 : ‖v‖ < δ₁ := lt_of_lt_of_le hv (min_le_left _ _)
  have hv2 : ‖v‖ < δ₂ := lt_of_lt_of_le hv (min_le_right _ _)
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · have hv₁ := hb₁ v hv1
    calc ‖(germC a h v).1 - A1.1‖ ≤ p₁ * ‖v‖ := hv₁
      _ ≤ max p₁ p₂ * ‖v‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg v)
  · have hv₂ := hb₂ v hv2
    calc ‖(germC a h v).2 - A1.2‖ ≤ p₂ * ‖v‖ := by simpa [A1] using hv₂
      _ ≤ max p₁ p₂ * ‖v‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg v)

/-- **Uniform quadratic contact.**  A closed fan with characteristic value `μ` agrees with
`germC a h (μ ·)` to second order, uniformly in the word and in `‖μ‖ ≤ 1`. -/
lemma fan_quadratic_contact {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δq Kq : ℝ, 0 < δq ∧ 0 < Kq ∧ ∀ μ : ℂ, ‖μ‖ ≤ 1 → ∀ C : List Bool,
      fan a h C 0 = A1 → charVal a h C = μ → ∀ u : ℂ, ‖u‖ ≤ δq →
        ‖fan a h C u - germC a h (μ * u)‖ ≤ Kq * ‖u‖ ^ 2 := by
  obtain ⟨Cd, δ1, hCdpos, hδ1pos, hdev⟩ := fan_deviation_bound ha0 ha1 hh
  obtain ⟨Cg, δ2, hCgpos, hδ2pos, hLdev⟩ := germC_deviation_bound ha0 ha1 hh
  obtain ⟨ρg, hρgpos, hgan, hg0, -, -, -⟩ := germC_facts ha0 ha1 hh
  obtain ⟨δu0, Ke, Lam, hδu0pos, hKepos, hLampos, hfan0⟩ :=
    FanUniform.fan_uniform_estimates ha0 ha1 hh
  -- the disc on which everything is analytic
  set R : ℝ := min δu0 (min δ1 (min δ2 (min ρg 1))) / 8 with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    exact div_pos (lt_min hδu0pos (lt_min hδ1pos (lt_min hδ2pos (lt_min hρgpos one_pos))))
      (by norm_num)
  have hRu : R ≤ δu0 / 8 := by
    rw [hRdef]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hR1 : R ≤ δ1 / 8 := by
    rw [hRdef]
    exact div_le_div_of_nonneg_right (le_trans (min_le_right _ _) (min_le_left _ _)) (by norm_num)
  have hR2 : R ≤ δ2 / 8 := by
    rw [hRdef]
    exact div_le_div_of_nonneg_right
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))) (by norm_num)
  have hRg : R ≤ ρg / 8 := by
    rw [hRdef]
    exact div_le_div_of_nonneg_right
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (min_le_left _ _)))) (by norm_num)
  have hR1' : R ≤ 1 / 8 := by
    rw [hRdef]
    exact div_le_div_of_nonneg_right
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (min_le_right _ _)))) (by norm_num)
  have h2u : 2 * R ≤ δu0 := by
    have h1 : 2 * R ≤ 2 * (δu0 / 8) := mul_le_mul_of_nonneg_left hRu (by norm_num)
    linarith only [h1, hδu0pos]
  have h21 : 2 * R ≤ δ1 := by
    have h1 : 2 * R ≤ 2 * (δ1 / 8) := mul_le_mul_of_nonneg_left hR1 (by norm_num)
    linarith only [h1, hδ1pos]
  have h22 : 2 * R ≤ δ2 := by
    have h1 : 2 * R ≤ 2 * (δ2 / 8) := mul_le_mul_of_nonneg_left hR2 (by norm_num)
    linarith only [h1, hδ2pos]
  have h2g : 2 * R ≤ ρg := by
    have h1 : 2 * R ≤ 2 * (ρg / 8) := mul_le_mul_of_nonneg_left hRg (by norm_num)
    linarith only [h1, hρgpos]
  have h21' : 2 * R ≤ 1 := by
    have h1 : 2 * R ≤ 2 * ((1 : ℝ) / 8) := mul_le_mul_of_nonneg_left hR1' (by norm_num)
    linarith only [h1]
  refine ⟨R, 4 * ((Cd + Cg) * (2 * R) + 1) / R ^ 2, hRpos, by positivity, ?_⟩
  intro μ hμ C hC0 hCμ u hu
  -- ============ (a) analyticity ============
  have hmem2R : ∀ z : ℂ, z ∈ Metric.ball (0 : ℂ) (2 * R) → z ∈ Metric.ball (0 : ℂ) δu0 := by
    intro z hz
    rw [mem_ball_zero] at hz ⊢
    linarith only [hz, h2u]
  have hfanC : AnalyticOnNhd ℂ (fan a h C) (Metric.ball (0 : ℂ) (2 * R)) :=
    (hfan0 C).1.mono hmem2R
  have hgermA : AnalyticOnNhd ℂ (fun v : ℂ => germC a h (μ * v)) (Metric.ball (0 : ℂ) (2 * R)) := by
    intro v hv
    rw [mem_ball_zero] at hv
    have hvρ : ‖μ * v‖ < ρg := by
      rw [norm_mul]
      have h1 : ‖μ‖ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hμ (norm_nonneg v)
      have h2 : ‖v‖ < ρg := lt_of_lt_of_le hv h2g
      linarith only [h1, h2]
    have hmem : μ * v ∈ Metric.ball (0 : ℂ) ρg := mem_ball_zero.mpr hvρ
    have h1 : AnalyticAt ℂ (fun z : ℂ => μ * z) v := analyticAt_const.mul analyticAt_id
    exact (hgan (μ * v) hmem).comp h1
  have hfstAn : AnalyticOnNhd ℂ (fun v : ℂ => (fan a h C v).1) (Metric.ball (0 : ℂ) (2 * R)) := by
    intro v hv
    have hg : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (fan a h C v) :=
      (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _
    exact hg.comp (hfanC v hv)
  have hfstAn' : AnalyticOnNhd ℂ (fun v : ℂ => (germC a h (μ * v)).1)
      (Metric.ball (0 : ℂ) (2 * R)) := by
    intro v hv
    have hg : AnalyticAt ℂ (fun p : ℂ × ℂ => p.1) (germC a h (μ * v)) :=
      (ContinuousLinearMap.fst ℂ ℂ ℂ).analyticAt _
    exact hg.comp (f := fun w : ℂ => germC a h (μ * w)) (hgermA v hv)
  have hsndAn : AnalyticOnNhd ℂ (fun v : ℂ => (fan a h C v).2) (Metric.ball (0 : ℂ) (2 * R)) := by
    intro v hv
    have hg : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (fan a h C v) :=
      (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _
    exact hg.comp (hfanC v hv)
  have hsndAn' : AnalyticOnNhd ℂ (fun v : ℂ => (germC a h (μ * v)).2)
      (Metric.ball (0 : ℂ) (2 * R)) := by
    intro v hv
    have hg : AnalyticAt ℂ (fun p : ℂ × ℂ => p.2) (germC a h (μ * v)) :=
      (ContinuousLinearMap.snd ℂ ℂ ℂ).analyticAt _
    exact hg.comp (f := fun w : ℂ => germC a h (μ * w)) (hgermA v hv)
  -- ============ (b) the a priori bound ============
  have hM : ∀ z ∈ Metric.ball (0 : ℂ) (2 * R),
      ‖fan a h C z - germC a h (μ * z)‖ ≤ (Cd + Cg) * (2 * R) + 1 := by
    intro z hz
    rw [mem_ball_zero] at hz
    have hz2R : ‖z‖ ≤ 2 * R := le_of_lt hz
    have hz1 : ‖z‖ < δ1 := lt_of_lt_of_le hz h21
    have hzμ2 : ‖μ * z‖ < δ2 := by
      rw [norm_mul]
      have h1 : ‖μ‖ * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hμ (norm_nonneg z)
      have h2 : ‖z‖ < δ2 := lt_of_lt_of_le hz h22
      linarith only [h1, h2]
    have ha : ‖fan a h C z - A1‖ ≤ Cd * ‖z‖ := hdev C hC0 z hz1
    have hb : ‖germC a h (μ * z) - A1‖ ≤ Cg * ‖μ * z‖ := hLdev (μ * z) hzμ2
    have hbz : ‖germC a h (μ * z) - A1‖ ≤ Cg * (2 * R) := by
      have h1 : ‖μ * z‖ ≤ 2 * R := by
        rw [norm_mul]
        calc ‖μ‖ * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hμ (norm_nonneg z)
          _ = ‖z‖ := one_mul _
          _ ≤ 2 * R := hz2R
      calc ‖germC a h (μ * z) - A1‖ ≤ Cg * ‖μ * z‖ := hb
        _ ≤ Cg * (2 * R) := mul_le_mul_of_nonneg_left h1 hCgpos.le
    have haz : ‖fan a h C z - A1‖ ≤ Cd * (2 * R) :=
      le_trans ha (mul_le_mul_of_nonneg_left hz2R hCdpos.le)
    calc ‖fan a h C z - germC a h (μ * z)‖
        ≤ ‖fan a h C z - A1‖ + ‖A1 - germC a h (μ * z)‖ := by
          have hsplit : fan a h C z - germC a h (μ * z)
              = (fan a h C z - A1) + (A1 - germC a h (μ * z)) := by ring
          rw [hsplit]; exact norm_add_le _ _
      _ ≤ Cd * (2 * R) + Cg * (2 * R) :=
          add_le_add haz (by rw [norm_sub_rev]; exact hbz)
      _ = (Cd + Cg) * (2 * R) := by ring
      _ ≤ (Cd + Cg) * (2 * R) + 1 := by linarith only
  have hMem0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) (2 * R) := by
    rw [mem_ball_zero, norm_zero]; linarith only [hRpos]
  have hCdCg0 : (0 : ℝ) ≤ (Cd + Cg) * (2 * R) + 1 := by positivity
  -- ============ (c) the first coordinate ============
  have hfst0 : (fun v : ℂ => (fan a h C v).1 - (germC a h (μ * v)).1) 0 = 0 := by
    have h1 : (fan a h C 0).1 = A1.1 := by rw [hC0]
    have h2 : (germC a h (μ * 0)).1 = A1.1 := by
      rw [mul_zero, hg0, ← A1_cform]
    simp only [Pi.sub_apply, h1, h2, sub_self]
  have hfstAn2 : AnalyticOnNhd ℂ (fun v : ℂ => (fan a h C v).1 - (germC a h (μ * v)).1)
      (Metric.ball (0 : ℂ) (2 * R)) := hfstAn.sub hfstAn'
  have hfstD : deriv (fun v : ℂ => (fan a h C v).1 - (germC a h (μ * v)).1) 0 = 0 := by
    change deriv ((fun v : ℂ => (fan a h C v).1) - (fun v : ℂ => (germC a h (μ * v)).1)) 0 = 0
    rw [deriv_sub (hfstAn 0 hMem0).differentiableAt (hfstAn' 0 hMem0).differentiableAt]
    have h2 : deriv (fun w : ℂ => (germC a h (μ * w)).1) 0
        = μ * deriv (fun w : ℂ => (germC a h w).1) 0 := by
      have hh2 := deriv_comp_mul_left μ (fun w : ℂ => (germC a h w).1) 0
      simpa using hh2
    have h3 : deriv (fun w : ℂ => (germC a h w).1) 0 = 0 := by
      change deriv (fun u : ℂ => (fan a h [] u).1) 0 = 0
      exact fan_deriv_fst_zero ha0 ha1 hh ([] : List Bool)
    rw [fan_deriv_fst_zero ha0 ha1 hh C, h2, h3, mul_zero, sub_zero]
  have hfstM : ∀ z ∈ Metric.ball (0 : ℂ) (2 * R),
      ‖(fan a h C z).1 - (germC a h (μ * z)).1‖ ≤ (Cd + Cg) * (2 * R) + 1 := by
    intro z hz
    calc ‖(fan a h C z).1 - (germC a h (μ * z)).1‖
        ≤ ‖fan a h C z - germC a h (μ * z)‖ := by
          rw [Prod.norm_def]; exact le_max_left _ _
      _ ≤ _ := hM z hz
  -- ============ (d) the second coordinate ============
  have hyderiv : deriv (fun v : ℂ => (germC a h v).2) 0 = (((1 - a) / 2 : ℝ) : ℂ) := by
    obtain ⟨-, -, -, -, -, -, hd⟩ := germC_facts ha0 ha1 hh
    exact hd
  have hD0 : deriv (fun v : ℂ => (germC a h v).2) 0 ≠ 0 := by
    rw [hyderiv]
    intro hc
    have h3 : ((1 - a) / 2 : ℝ) = 0 := by exact_mod_cast hc
    linarith only [h3, ha1]
  have hcv : deriv (fun v : ℂ => (fan a h C v).2) 0
      = μ * deriv (fun v : ℂ => (germC a h v).2) 0 := by
    have h := hCμ
    rw [charVal] at h
    rwa [div_eq_iff hD0] at h
  have hsnd0 : (fun v : ℂ => (fan a h C v).2 - (germC a h (μ * v)).2) 0 = 0 := by
    have h1 : (fan a h C 0).2 = A1.2 := by rw [hC0]
    have h2 : (germC a h (μ * 0)).2 = A1.2 := by
      rw [mul_zero, hg0, ← A1_cform]
    simp only [Pi.sub_apply, h1, h2, sub_self]
  have hsndAn2 : AnalyticOnNhd ℂ (fun v : ℂ => (fan a h C v).2 - (germC a h (μ * v)).2)
      (Metric.ball (0 : ℂ) (2 * R)) := hsndAn.sub hsndAn'
  have hsndD : deriv (fun v : ℂ => (fan a h C v).2 - (germC a h (μ * v)).2) 0 = 0 := by
    change deriv ((fun v : ℂ => (fan a h C v).2) - (fun v : ℂ => (germC a h (μ * v)).2)) 0 = 0
    rw [deriv_sub (hsndAn 0 hMem0).differentiableAt (hsndAn' 0 hMem0).differentiableAt]
    have h2 : deriv (fun w : ℂ => (germC a h (μ * w)).2) 0
        = μ * deriv (fun w : ℂ => (germC a h w).2) 0 := by
      have hh2 := deriv_comp_mul_left μ (fun w : ℂ => (germC a h w).2) 0
      simpa using hh2
    rw [hcv, h2]
    ring
  have hsndM : ∀ z ∈ Metric.ball (0 : ℂ) (2 * R),
      ‖(fan a h C z).2 - (germC a h (μ * z)).2‖ ≤ (Cd + Cg) * (2 * R) + 1 := by
    intro z hz
    calc ‖(fan a h C z).2 - (germC a h (μ * z)).2‖
        ≤ ‖fan a h C z - germC a h (μ * z)‖ := by
          rw [Prod.norm_def]; exact le_max_right _ _
      _ ≤ _ := hM z hz
  -- ============ (e) Cauchy's estimate ============
  have h1u := analytic_quadratic_bound hRpos hCdCg0 hfstAn2 hfst0 hfstD hfstM u hu
  have h2u := analytic_quadratic_bound hRpos hCdCg0 hsndAn2 hsnd0 hsndD hsndM u hu
  rw [Prod.norm_def]
  exact max_le h1u h2u


/-- **Uniform geometric decay of the iterated fan towards the leaf.**  For a closed word `C` with
characteristic value `μ` (`‖μ‖ ≤ 1`), the fan of `true^j ++ C` converges to `germC a h (μ ·)` on
a disc, at a geometric rate independent of `C` and of `μ`. -/
lemma fan_gap_run {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δr Kr : ℝ, ∃ rate : ℝ, 0 < δr ∧ 0 < Kr ∧ 0 < rate ∧ rate < 1 ∧
      ∀ μ : ℂ, ‖μ‖ ≤ 1 → ∀ C : List Bool, fan a h C 0 = A1 → charVal a h C = μ →
        ∀ j : ℕ, ∀ u : ℂ, ‖u‖ ≤ δr →
          ‖fan a h (List.replicate j true ++ C) u - germC a h (μ * u)‖ ≤ Kr * rate ^ j * ‖u‖ ^ 2 := by
  obtain ⟨δq, Kq, hδqpos, hKqpos, hquad⟩ := fan_quadratic_contact ha0 ha1 hh
  obtain ⟨Cd, δ1, hCdpos, hδ1pos, hdev⟩ := fan_deviation_bound ha0 ha1 hh
  obtain ⟨Cg, δ2, hCgpos, hδ2pos, hLdev⟩ := germC_deviation_bound ha0 ha1 hh
  obtain ⟨ρg, hρgpos, -, hg0, hinv, -, -⟩ := germC_facts ha0 ha1 hh
  obtain ⟨ρN, N, hρNpos, hNpos, hsecond⟩ := invBranch_true_second_order ha0 ha1
  have lam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have lam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hnormlam : ‖((eqLam a : ℝ) : ℂ)‖ = eqLam a := by rw [norm_ofReal', abs_of_pos lam0]
  -- ============ the constants ============
  have hden : 0 < (eqLam a) ^ 3 * N * (Cd + Cg) := by positivity
  set c0 : ℝ := (1 - eqLam a) / (2 * (N * (Cd + Cg) * (eqLam a) ^ 2)) with hc0def
  have hc0pos : 0 < c0 := by
    rw [hc0def]
    exact div_pos (by linarith only [lam1]) (by positivity)
  set δr : ℝ := min δq (min δ1 (min δ2 (min ρg (min (ρN / (Cd + Cg + 1)) c0)))) / 8
    with hδrdef
  have hδrpos : 0 < δr := by
    rw [hδrdef]
    refine div_pos (lt_min hδqpos (lt_min hδ1pos (lt_min hδ2pos (lt_min hρgpos
      (lt_min (div_pos hρNpos (by positivity)) hc0pos))))) (by norm_num)
  have hδr_q : δr ≤ δq / 8 := by
    rw [hδrdef]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδr_1 : δr ≤ δ1 / 8 := by
    rw [hδrdef]
    exact div_le_div_of_nonneg_right (le_trans (min_le_right _ _) (min_le_left _ _)) (by norm_num)
  have hδr_2 : δr ≤ δ2 / 8 := by
    rw [hδrdef]
    exact div_le_div_of_nonneg_right
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))) (by norm_num)
  have hδr_g : δr ≤ ρg / 8 := by
    rw [hδrdef]
    exact div_le_div_of_nonneg_right
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (min_le_left _ _)))) (by norm_num)
  have hδr_N : δr ≤ (ρN / (Cd + Cg + 1)) / 8 := by
    rw [hδrdef]
    exact div_le_div_of_nonneg_right
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _))))) (by norm_num)
  have hδr_c : δr ≤ c0 / 8 := by
    rw [hδrdef]
    exact div_le_div_of_nonneg_right
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _))))) (by norm_num)
  have hδrq : δr ≤ δq := by linarith only [hδr_q, hδqpos]
  have hδr1 : δr < δ1 := by linarith only [hδr_1, hδ1pos]
  have hδr2 : δr < δ2 := by linarith only [hδr_2, hδ2pos]
  have hδrg : δr < ρg := by linarith only [hδr_g, hρgpos]
  have hδrN : (Cd + Cg + 1) * δr ≤ ρN := by
    have hX : 0 ≤ ρN / (Cd + Cg + 1) := by positivity
    have hq : δr ≤ ρN / (Cd + Cg + 1) := le_trans hδr_N (by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 8)]
      linarith only [hX])
    have h1 : (Cd + Cg + 1) * δr ≤ (Cd + Cg + 1) * (ρN / (Cd + Cg + 1)) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    have h2 : (Cd + Cg + 1) * (ρN / (Cd + Cg + 1)) = ρN :=
      mul_div_cancel₀ _ (by positivity : ((Cd : ℝ) + Cg + 1) ≠ 0)
    linarith only [h1, h2]
  have hδrc : δr ≤ c0 := le_trans hδr_c (by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 8)]
    linarith only [hc0pos])
  -- ============ the rate ============
  set rate : ℝ := (1 + eqLam a) / 2 with hratedef
  have hratepos : 0 < rate := by rw [hratedef]; linarith only [lam0]
  have hratelt : rate < 1 := by rw [hratedef]; linarith only [lam1]
  have hkey_rate : eqLam a + N * (Cd + Cg) * (eqLam a) ^ 2 * δr ≤ rate := by
    have h1 : N * (Cd + Cg) * (eqLam a) ^ 2 * δr ≤ N * (Cd + Cg) * (eqLam a) ^ 2 * c0 :=
      mul_le_mul_of_nonneg_left hδrc (by positivity)
    have h2 : N * (Cd + Cg) * (eqLam a) ^ 2 * c0 = (1 - eqLam a) / 2 := by
      rw [hc0def]; field_simp <;> ring
    rw [hratedef]
    linarith only [h1, h2]
  refine ⟨δr, Kq, rate, hδrpos, hKqpos, hratepos, hratelt, ?_⟩
  -- ============ the induction ============
  intro μ hμ C hC0 hCμ
  have hinvL : ∀ w : ℂ, ‖μ * w‖ < ρg →
      Work.EQ.invBranch a true (germC a h (μ * (((eqLam a : ℝ) : ℂ) * w))) = germC a h (μ * w) := by
    intro w hw
    have h := (hinv (μ * w) (mem_ball_zero.mpr hw)).2
    rwa [show ((eqLam a : ℝ) : ℂ) * (μ * w) = μ * (((eqLam a : ℝ) : ℂ) * w) by ring] at h
  have hμw : ∀ w : ℂ, ‖w‖ ≤ δr → ‖μ * w‖ < ρg := by
    intro w hw
    rw [norm_mul]
    have h1 : ‖μ‖ * ‖w‖ ≤ 1 * ‖w‖ := mul_le_mul_of_nonneg_right hμ (norm_nonneg w)
    have h2 : ‖w‖ < ρg := lt_of_le_of_lt hw hδrg
    linarith only [h1, h2]
  intro j
  induction j with
  | zero =>
      intro u hu
      have h0 : List.replicate 0 true ++ C = C := by simp
      rw [h0, pow_zero, mul_one]
      exact hquad μ hμ C hC0 hCμ u (le_trans hu hδrq)
  | succ j ih =>
      intro u hu
      rw [List.replicate_succ, List.cons_append, Work.EQ.fan_cons]
      set v : ℂ := ((eqLam a : ℝ) : ℂ) * u with hvdef
      have hvnorm : ‖v‖ = eqLam a * ‖u‖ := by rw [hvdef, norm_mul, hnormlam]
      have hvle : ‖v‖ ≤ δr := by
        rw [hvnorm]
        have h1 : eqLam a * ‖u‖ ≤ 1 * δr :=
          mul_le_mul (le_of_lt lam1) hu (norm_nonneg u) zero_le_one
        linarith only [h1]
      set W : List Bool := List.replicate j true ++ C with hWdef
      set X : ℂ × ℂ := fan a h W v with hXdef
      set Y : ℂ × ℂ := germC a h (μ * v) with hYdef
      have hW0 : fan a h W 0 = A1 := fan_replicate_true_centre ha0 ha1 hh j hC0
      have ihX : ‖X - Y‖ ≤ Kq * rate ^ j * ‖v‖ ^ 2 := by
        rw [hXdef, hYdef]
        exact ih v hvle
      have hXdev : ‖X - A1‖ ≤ Cd * δr := by
        have h1 : ‖X - A1‖ ≤ Cd * ‖v‖ := hdev W hW0 v (lt_of_le_of_lt hvle hδr1)
        have h2 : Cd * ‖v‖ ≤ Cd * δr := mul_le_mul_of_nonneg_left hvle hCdpos.le
        linarith only [h1, h2]
      have hYdev : ‖Y - A1‖ ≤ Cg * δr := by
        have h1 : ‖μ * v‖ < δ2 := by
          rw [norm_mul]
          have ha1 : ‖μ‖ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hμ (norm_nonneg v)
          have ha2 : ‖v‖ < δ2 := lt_of_le_of_lt hvle hδr2
          linarith only [ha1, ha2]
        have h2 : ‖Y - A1‖ ≤ Cg * ‖μ * v‖ := hLdev (μ * v) h1
        have h3 : ‖μ * v‖ ≤ δr := by
          rw [norm_mul]
          have ha1 : ‖μ‖ * ‖v‖ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hμ (norm_nonneg v)
          linarith only [ha1, hvle]
        calc ‖Y - A1‖ ≤ Cg * ‖μ * v‖ := h2
          _ ≤ Cg * δr := mul_le_mul_of_nonneg_left h3 hCgpos.le
      have hXN : ‖X - A1‖ ≤ ρN := by
        have h1 : Cd * δr ≤ (Cd + Cg + 1) * δr :=
          mul_le_mul_of_nonneg_right (by linarith only [hCdpos, hCgpos]) hδrpos.le
        linarith only [hXdev, h1, hδrN]
      have hYN : ‖Y - A1‖ ≤ ρN := by
        have h1 : Cg * δr ≤ (Cd + Cg + 1) * δr :=
          mul_le_mul_of_nonneg_right (by linarith only [hCdpos, hCgpos]) hδrpos.le
        linarith only [hYdev, h1, hδrN]
      -- abbreviations
      set A : ℂ × ℂ := Work.EQ.invBranch a true X with hAdef
      set B : ℂ × ℂ := Work.EQ.invBranch a true Y with hBdef
      set Cv : ℂ × ℂ := ( (-(X.1 - Y.1)), (X.2 - Y.2) / (eqLam a : ℂ) ) with hCvdef
      -- the second-order remainder
      have hE : ‖A - B - Cv‖ ≤ N * (‖X - A1‖ + ‖Y - A1‖) * ‖X - Y‖ := by
        have h := hsecond X Y hXN hYN
        exact h
      have hE' : ‖A - B - Cv‖ ≤ N * ((Cd + Cg) * δr) * (Kq * rate ^ j * ‖v‖ ^ 2) := by
        refine le_trans hE ?_
        have hdevsum : ‖X - A1‖ + ‖Y - A1‖ ≤ (Cd + Cg) * δr := by
          have h1 : (Cd + Cg) * δr = Cd * δr + Cg * δr := by ring
          linarith only [hXdev, hYdev, h1]
        have h2 : N * (‖X - A1‖ + ‖Y - A1‖) ≤ N * ((Cd + Cg) * δr) :=
          mul_le_mul_of_nonneg_left hdevsum (le_of_lt hNpos)
        calc N * (‖X - A1‖ + ‖Y - A1‖) * ‖X - Y‖
            ≤ N * ((Cd + Cg) * δr) * ‖X - Y‖ :=
              mul_le_mul_of_nonneg_right h2 (norm_nonneg (X - Y))
          _ ≤ N * ((Cd + Cg) * δr) * (Kq * rate ^ j * ‖v‖ ^ 2) :=
              mul_le_mul_of_nonneg_left ihX (by positivity)
      -- the invariance of the leaf
      have hinvY : B = germC a h (μ * u) := by
        rw [hBdef, hYdef, hvdef]
        exact hinvL u (hμw u hu)
      rw [← hinvY]
      -- the triangle inequality
      have hCnorm : ‖Cv‖ ≤ ‖X - Y‖ / eqLam a := by
        rw [hCvdef, Prod.norm_def]
        refine max_le ?_ ?_
        · calc ‖-(X.1 - Y.1)‖ = ‖X.1 - Y.1‖ := norm_neg _
            _ ≤ ‖X - Y‖ := by rw [Prod.norm_def]; exact le_max_left _ _
            _ ≤ ‖X - Y‖ / eqLam a := by
                rw [le_div_iff₀ lam0]
                nlinarith only [norm_nonneg (X - Y), lam1]
        · calc ‖(X.2 - Y.2) / (eqLam a : ℂ)‖ = ‖X.2 - Y.2‖ / eqLam a := by
                rw [norm_div, hnormlam]
            _ ≤ ‖X - Y‖ / eqLam a := by
                refine div_le_div_of_nonneg_right ?_ lam0.le
                rw [Prod.norm_def]; exact le_max_right _ _
      have htri : ‖A - B‖ ≤ ‖A - B - Cv‖ + ‖Cv‖ := by
        have h := norm_add_le (A - B - Cv) Cv
        rw [sub_add_cancel] at h
        exact h
      -- the final estimate
      have hdiv : ‖X - Y‖ / eqLam a ≤ Kq * rate ^ j * ‖v‖ ^ 2 / eqLam a :=
        div_le_div_of_nonneg_right ihX lam0.le
      calc ‖A - B‖ ≤ ‖A - B - Cv‖ + ‖Cv‖ := htri
        _ ≤ N * ((Cd + Cg) * δr) * (Kq * rate ^ j * ‖v‖ ^ 2)
              + Kq * rate ^ j * ‖v‖ ^ 2 / eqLam a := by
            refine add_le_add hE' ?_
            exact le_trans hCnorm hdiv
        _ = Kq * rate ^ j * ‖u‖ ^ 2 *
              (eqLam a + N * (Cd + Cg) * (eqLam a) ^ 2 * δr) := by
            have hv2 : ‖v‖ ^ 2 = (eqLam a) ^ 2 * ‖u‖ ^ 2 := by rw [hvnorm]; ring
            rw [hv2]
            field_simp <;> ring_nf
        _ ≤ Kq * rate ^ j * ‖u‖ ^ 2 * rate :=
            mul_le_mul_of_nonneg_left hkey_rate (by positivity)
        _ = Kq * rate ^ (j + 1) * ‖u‖ ^ 2 := by rw [pow_succ]; ring_nf
      -- rewrite the goal into the form just estimated
      -- (the goal is `‖invBranch X - germC (μ u)‖ ≤ ...`, and `B = germC (μ u)`)

theorem fan_gap_unif {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε₀ : List Bool) (s : ℕ → ℕ) (C : ℕ → List Bool) (μ : ℂ),
      Filter.Tendsto s Filter.atTop Filter.atTop →
      (∀ k, Work.EQ.fan a h (C k) 0 = ((-1 / 2 : ℂ), (0 : ℂ))) →
      (∀ k, Work.EQ.charVal a h (C k) = μ) →
      TendstoUniformlyOn (fun k : ℕ => Work.EQ.fan a h (ε₀ ++ List.replicate (s k) true ++ C k))
        (fun u => Work.EQ.fan a h ε₀ (μ * u)) Filter.atTop (Metric.ball 0 δ) := by
  obtain ⟨δr, Kr, rate, hδrpos, hKrpos, hratepos, hratelt, hrun⟩ := fan_gap_run ha0 ha1 hh
  obtain ⟨Cd, δ1, hCdpos, hδ1pos, hdev⟩ := fan_deviation_bound ha0 ha1 hh
  obtain ⟨Cg, δ2, hCgpos, hδ2pos, hLdev⟩ := germC_deviation_bound ha0 ha1 hh
  obtain ⟨ρS, D, hρSpos, hDpos, hscaled⟩ := branchComp_lipschitz_scaled ha0 ha1
  have lam0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have lam1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hnormlam : ‖((eqLam a : ℝ) : ℂ)‖ = eqLam a := by rw [norm_ofReal', abs_of_pos lam0]
  -- scale bounds
  have hpow_le_one : ∀ n : ℕ, (eqLam a) ^ n ≤ 1 := fun _ => pow_le_one₀ lam0.le lam1.le
  have hpowpos : ∀ n : ℕ, 0 < (eqLam a) ^ n := fun n => pow_pos lam0 n
  have hpow_mul_le : ∀ (n : ℕ) (u : ℂ), ‖((eqLam a : ℝ) : ℂ) ^ n * u‖ ≤ ‖u‖ := by
    intro n u
    rw [norm_mul, norm_pow, hnormlam]
    calc (eqLam a) ^ n * ‖u‖ ≤ 1 * ‖u‖ :=
          mul_le_mul_of_nonneg_right (hpow_le_one n) (norm_nonneg u)
      _ = ‖u‖ := one_mul _
  have hpow_mul_eq : ∀ (n : ℕ) (u : ℂ), ‖((eqLam a : ℝ) : ℂ) ^ n * u‖ = (eqLam a) ^ n * ‖u‖ := by
    intro n u
    rw [norm_mul, norm_pow, hnormlam]
  -- the radius
  set δ : ℝ := min δr (min (δ1 / 2) (min (δ2 / 2)
      (min (ρS / (Cd + 1)) (ρS / (Cg + 1))))) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min hδrpos (lt_min (by linarith only [hδ1pos]) (lt_min (by linarith only [hδ2pos])
      (lt_min (div_pos hρSpos (by positivity)) (div_pos hρSpos (by positivity)))))
  have hδδr : δ ≤ δr := by rw [hδdef]; exact min_le_left _ _
  have hδ1 : δ ≤ δ1 / 2 := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδ2 : δ ≤ δ2 / 2 := by
    rw [hδdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδCd : δ ≤ ρS / (Cd + 1) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδCg : δ ≤ ρS / (Cg + 1) := by
    rw [hδdef]
    exact le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  refine ⟨δ, hδpos, ?_⟩
  intro ε₀ s C μ hs hC0 hCμ
  -- `‖μ‖ ≤ 1`
  have hC0k : ∀ k, fan a h (C k) 0 = A1 := fun k => by rw [hC0 k]; exact A1_cform
  have hμ1 : ‖μ‖ ≤ 1 := by
    obtain ⟨δc, hδc, hchar, hfin⟩ := charVal_props ha0 ha1 hh
    obtain ⟨him, hpos, hle, -⟩ := hchar (C 0) (hC0 0)
    have hcv : Work.EQ.charVal a h (C 0)
        = (((Work.EQ.charVal a h (C 0)).re : ℝ) : ℂ) := by
      rw [← Complex.re_add_im (Work.EQ.charVal a h (C 0)), him]
      simp
    rw [← hCμ 0, hcv, norm_ofReal', abs_of_pos hpos]
    exact hle
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hDlim : Filter.Tendsto (fun k => rate ^ (s k)) Filter.atTop (nhds 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hratepos) hratelt).comp hs
  have hBDpos : 0 < D * Kr * δ ^ 2 := by positivity
  have hev : ∀ᶠ k in Filter.atTop, D * Kr * δ ^ 2 * rate ^ (s k) < ε := by
    have h2 : ∀ᶠ k in Filter.atTop, rate ^ (s k) < ε / (D * Kr * δ ^ 2) :=
      hDlim.eventually (eventually_lt_nhds (by positivity))
    filter_upwards [h2] with k hk
    calc D * Kr * δ ^ 2 * rate ^ (s k) < D * Kr * δ ^ 2 * (ε / (D * Kr * δ ^ 2)) :=
          mul_lt_mul_of_pos_left hk hBDpos
      _ = ε := by field_simp
  filter_upwards [hev] with k hk
  intro u hu
  rw [mem_ball_zero] at hu
  set n : ℕ := ε₀.length with hndef
  set v : ℂ := ((eqLam a : ℝ) : ℂ) ^ n * u with hvdef
  have hvnorm : ‖v‖ = (eqLam a) ^ n * ‖u‖ := by rw [hvdef]; exact hpow_mul_eq n u
  have hv_le_u : ‖v‖ ≤ ‖u‖ := by rw [hvdef]; exact hpow_mul_le n u
  have hvn : ‖v‖ ≤ δr := le_trans hv_le_u (le_trans hu.le hδδr)
  have hvδ1 : ‖v‖ < δ1 := by
    have h3 : ‖v‖ ≤ δ1 / 2 := le_trans hv_le_u (le_trans hu.le hδ1)
    have h4 : δ1 / 2 < δ1 := by linarith only [hδ1pos]
    linarith only [h3, h4]
  have hvδ2 : ‖v‖ < δ2 := by
    have h3 : ‖v‖ ≤ δ2 / 2 := le_trans hv_le_u (le_trans hu.le hδ2)
    have h4 : δ2 / 2 < δ2 := by linarith only [hδ2pos]
    linarith only [h3, h4]
  have hμv : ‖μ * v‖ < δ2 := by
    rw [norm_mul]
    have h1 : ‖μ‖ * ‖v‖ ≤ 1 * (δ2 / 2) :=
      mul_le_mul hμ1 (le_trans hv_le_u (le_trans hu.le hδ2)) (norm_nonneg v) zero_le_one
    have h4 : δ2 / 2 < δ2 := by linarith only [hδ2pos]
    linarith only [h1, h4]
  have hW0 : fan a h (List.replicate (s k) true ++ C k) 0 = A1 :=
    fan_replicate_true_centre ha0 ha1 hh (s k) (hC0k k)
  have hun : ‖fan a h (List.replicate (s k) true ++ C k) v - germC a h (μ * v)‖
      ≤ Kr * rate ^ (s k) * ‖v‖ ^ 2 :=
    hrun μ hμ1 (C k) (hC0k k) (hCμ k) (s k) v hvn
  have hXdev : ‖fan a h (List.replicate (s k) true ++ C k) v - A1‖ ≤ Cd * ‖v‖ :=
    hdev _ hW0 v hvδ1
  have hYdev : ‖germC a h (μ * v) - A1‖ ≤ Cg * ‖v‖ := by
    calc ‖germC a h (μ * v) - A1‖ ≤ Cg * ‖μ * v‖ := hLdev (μ * v) hμv
      _ ≤ Cg * ‖v‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hCgpos.le
          rw [norm_mul]
          calc ‖μ‖ * ‖v‖ ≤ 1 * ‖v‖ :=
                mul_le_mul_of_nonneg_right hμ1 (norm_nonneg v)
            _ = ‖v‖ := one_mul _
  have hvnδ : ‖v‖ ≤ (eqLam a) ^ n * δ := by
    rw [hvnorm]
    exact mul_le_mul_of_nonneg_left hu.le (le_of_lt (hpowpos n))
  -- radius conditions for the scaled Lipschitz lemma
  have hCdδ : Cd * δ ≤ ρS := by
    have h3 : Cd * δ ≤ Cd * (ρS / (Cd + 1)) := mul_le_mul_of_nonneg_left hδCd hCdpos.le
    have h4 : Cd * (ρS / (Cd + 1)) ≤ ρS := by
      have h5 : Cd * (ρS / (Cd + 1)) = ρS * (Cd / (Cd + 1)) := by ring
      rw [h5]
      have h6 : Cd / (Cd + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith only [hCdpos]
      calc ρS * (Cd / (Cd + 1)) ≤ ρS * 1 := mul_le_mul_of_nonneg_left h6 hρSpos.le
        _ = ρS := mul_one _
    linarith only [h3, h4]
  have hCgδ : Cg * δ ≤ ρS := by
    have h3 : Cg * δ ≤ Cg * (ρS / (Cg + 1)) := mul_le_mul_of_nonneg_left hδCg hCgpos.le
    have h4 : Cg * (ρS / (Cg + 1)) ≤ ρS := by
      have h5 : Cg * (ρS / (Cg + 1)) = ρS * (Cg / (Cg + 1)) := by ring
      rw [h5]
      have h6 : Cg / (Cg + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith only [hCgpos]
      calc ρS * (Cg / (Cg + 1)) ≤ ρS * 1 := mul_le_mul_of_nonneg_left h6 hρSpos.le
        _ = ρS := mul_one _
    linarith only [h3, h4]
  have hXρ : ‖fan a h (List.replicate (s k) true ++ C k) v - A1‖ ≤ ρS * (eqLam a) ^ n := by
    have h1 : Cd * ‖v‖ ≤ Cd * ((eqLam a) ^ n * δ) := mul_le_mul_of_nonneg_left hvnδ hCdpos.le
    refine le_trans hXdev (le_trans h1 ?_)
    calc Cd * ((eqLam a) ^ n * δ) = (Cd * δ) * (eqLam a) ^ n := by ring
      _ ≤ ρS * (eqLam a) ^ n := mul_le_mul_of_nonneg_right hCdδ (le_of_lt (hpowpos n))
  have hYρ : ‖germC a h (μ * v) - A1‖ ≤ ρS * (eqLam a) ^ n := by
    have h1 : Cg * ‖v‖ ≤ Cg * ((eqLam a) ^ n * δ) := mul_le_mul_of_nonneg_left hvnδ hCgpos.le
    refine le_trans hYdev (le_trans h1 ?_)
    calc Cg * ((eqLam a) ^ n * δ) = (Cg * δ) * (eqLam a) ^ n := by ring
      _ ≤ ρS * (eqLam a) ^ n := mul_le_mul_of_nonneg_right hCgδ (le_of_lt (hpowpos n))
  -- the two identities
  have happ1 : fan a h (ε₀ ++ List.replicate (s k) true ++ C k) u
      = branchComp a ε₀ (fan a h (List.replicate (s k) true ++ C k) v) := by
    rw [List.append_assoc]
    exact fan_append_branchComp a h ε₀ (List.replicate (s k) true ++ C k) u
  have harg : ((eqLam a : ℂ)) ^ ε₀.length * (μ * u) = μ * (((eqLam a : ℂ)) ^ n * u) := by
    rw [← hndef]
    ring
  have happ2 : fan a h ε₀ (μ * u) = branchComp a ε₀ (germC a h (μ * v)) := by
    calc fan a h ε₀ (μ * u)
        = branchComp a ε₀ (fan a h ([] : List Bool) (((eqLam a : ℂ)) ^ ε₀.length * (μ * u))) := by
          simpa using fan_append_branchComp a h ε₀ [] (μ * u)
      _ = branchComp a ε₀ (germC a h (((eqLam a : ℂ)) ^ ε₀.length * (μ * u))) := by
          rw [fan_nil]
      _ = branchComp a ε₀ (germC a h (μ * v)) := by
          rw [harg, ← hvdef]
  -- the scaled Lipschitz bound
  have hXρ' : ‖fan a h (List.replicate (s k) true ++ C k) v - A1‖
      ≤ ρS * (eqLam a) ^ ε₀.length := by
    rw [← hndef]
    exact hXρ
  have hYρ' : ‖germC a h (μ * v) - A1‖ ≤ ρS * (eqLam a) ^ ε₀.length := by
    rw [← hndef]
    exact hYρ
  have hsc := hscaled ε₀ (fan a h (List.replicate (s k) true ++ C k) v)
    (germC a h (μ * v)) hXρ' hYρ'
  -- conclusion
  rw [dist_eq_norm, happ1, happ2, norm_sub_rev]
  calc ‖branchComp a ε₀ (fan a h (List.replicate (s k) true ++ C k) v)
        - branchComp a ε₀ (germC a h (μ * v))‖
      ≤ D * ‖fan a h (List.replicate (s k) true ++ C k) v - germC a h (μ * v)‖
          / (eqLam a) ^ n := by
        rw [le_div_iff₀ (hpowpos n)]
        rw [mul_comm]
        exact hsc
    _ ≤ D * (Kr * rate ^ (s k) * ‖v‖ ^ 2) / (eqLam a) ^ n := by
        have h1 : D * ‖fan a h (List.replicate (s k) true ++ C k) v - germC a h (μ * v)‖
            ≤ D * (Kr * rate ^ (s k) * ‖v‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hun (le_of_lt hDpos)
        exact div_le_div_of_nonneg_right h1 (le_of_lt (hpowpos n))
    _ ≤ D * Kr * δ ^ 2 * rate ^ (s k) := by
        rw [div_le_iff₀ (hpowpos n)]
        have hv2 : ‖v‖ ^ 2 ≤ ((eqLam a) ^ n * δ) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg v) hvnδ 2
        have hmono : D * (Kr * rate ^ (s k) * ‖v‖ ^ 2)
            ≤ D * (Kr * rate ^ (s k) * (((eqLam a) ^ n * δ) ^ 2)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hv2 (by positivity)) (le_of_lt hDpos)
        have h3 : D * (Kr * rate ^ (s k) * (((eqLam a) ^ n * δ) ^ 2))
            = ((eqLam a) ^ n) ^ 2 * (D * Kr * δ ^ 2 * rate ^ (s k)) := by ring
        have h4 : ((eqLam a) ^ n) ^ 2 ≤ (eqLam a) ^ n := by
          have h5 : (eqLam a) ^ n ≤ 1 := hpow_le_one n
          have h6 : 0 ≤ (eqLam a) ^ n := (hpowpos n).le
          nlinarith only [h5, h6]
        have h7 : ((eqLam a) ^ n) ^ 2 * (D * Kr * δ ^ 2 * rate ^ (s k))
            ≤ (eqLam a) ^ n * (D * Kr * δ ^ 2 * rate ^ (s k)) :=
          mul_le_mul_of_nonneg_right h4 (by positivity)
        calc D * (Kr * rate ^ (s k) * ‖v‖ ^ 2)
            ≤ D * (Kr * rate ^ (s k) * (((eqLam a) ^ n * δ) ^ 2)) := hmono
          _ = ((eqLam a) ^ n) ^ 2 * (D * Kr * δ ^ 2 * rate ^ (s k)) := h3
          _ ≤ (eqLam a) ^ n * (D * Kr * δ ^ 2 * rate ^ (s k)) := h7
          _ = D * Kr * δ ^ 2 * rate ^ (s k) * (eqLam a) ^ n := by ring
    _ < ε := hk

end

end Work.EQ.FanTri
