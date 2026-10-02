import Mathlib
import Submission.Work.RatHurewicz.ExcisionSetup
import Submission.Work.AttachPush.exists_contDiff_approx_ne_zero

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# A bounded continuous approximation of a map on a cube, nowhere zero on a compact subset

Let `K₁ ⊆ K₂ ⊆ I^d` be compact subsets of the `d`-cube `I^d = (Fin d → [0,1])`, let `d < k`
and let `ψ : K₂ → ℝ^k` be continuous with `‖ψ x‖ ≤ 1`.  Then for every `ε > 0` there is a
continuous `P : I^d → ℝ^k` with `‖P x‖ ≤ 1` everywhere, `‖P x - ψ x‖ < ε` on `K₂`, and
`P x ≠ 0` on `K₁`.

The proof extends `ψ` to the whole cube `I^d` by Tietze (`I^d` is compact Hausdorff, hence
normal), pulls it back to `ℝ^d` by the coordinatewise projection onto the cube, approximates by
a `C^∞` map `g`, shifts `g` by a small `c` not in its image — possible since `d < k` makes
`range g` Lebesgue-null — and finally applies the radial clamp `v ↦ (max 1 ‖v‖)⁻¹ • v`, which
enforces `‖P x‖ ≤ 1` while moving every point by at most `‖v‖ - 1`.
-/

namespace Work.AttachPush

open MeasureTheory
open Work.RatHurewicz

section RadialClamp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The radial clamp `v ↦ (max 1 ‖v‖)⁻¹ • v` never increases the norm. -/
lemma norm_inv_max_smul_le_one (v : E) : ‖(max 1 ‖v‖)⁻¹ • v‖ ≤ 1 := by
  have hpos : 0 < max 1 ‖v‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hpos, ← div_eq_inv_mul,
    div_le_one hpos]
  exact le_max_right _ _

/-- The radial clamp moves a vector by at most `max 0 (‖v‖ - 1)`. -/
lemma norm_inv_max_smul_sub_le (v : E) :
    ‖(max 1 ‖v‖)⁻¹ • v - v‖ ≤ max 0 (‖v‖ - 1) := by
  rcases le_or_gt ‖v‖ 1 with h | h
  · have hm : max 1 ‖v‖ = 1 := max_eq_left h
    have hz : max 0 (‖v‖ - 1) = 0 := max_eq_left (by linarith)
    rw [hm, inv_one, one_smul, sub_self, norm_zero, hz]
  · have hm : max 1 ‖v‖ = ‖v‖ := max_eq_right h.le
    have hmz : max 0 (‖v‖ - 1) = ‖v‖ - 1 := max_eq_right (by linarith)
    have hne : ‖v‖ ≠ 0 := ne_of_gt (lt_trans zero_lt_one h)
    have hslow : (max 1 ‖v‖)⁻¹ • v - v = (‖v‖⁻¹ - 1) • v := by
      rw [hm]
      have := sub_smul (‖v‖⁻¹) 1 v
      rw [this, one_smul]
    rw [hslow, norm_smul, Real.norm_eq_abs, hmz]
    have hneg : ‖v‖⁻¹ - 1 < 0 := by
      have := inv_lt_one_of_one_lt₀ h
      linarith
    rw [abs_of_neg hneg]
    have hval : -(‖v‖⁻¹ - 1) * ‖v‖ = ‖v‖ - 1 := by
      rw [neg_sub, sub_mul, one_mul, inv_mul_cancel₀ hne]
    rw [hval]

/-- The radial clamp vanishes exactly on the origin. -/
lemma inv_max_smul_ne_zero_iff (v : E) : (max 1 ‖v‖)⁻¹ • v ≠ 0 ↔ v ≠ 0 := by
  have hpos : 0 < max 1 ‖v‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hne : (max 1 ‖v‖)⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hpos)
  constructor
  · intro h hv0
    exact h (by rw [hv0, smul_zero])
  · intro h hv0
    exact h ((smul_eq_zero.mp hv0).resolve_left hne)

end RadialClamp

theorem exists_continuous_approx_ne_zero_cube {d k : ℕ} (hdk : d < k)
    {K₁ K₂ : Set (Work.RatHurewicz.ICube d)}
    (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂) (hsub : K₁ ⊆ K₂)
    (ψ : C(↥K₂, EuclideanSpace ℝ (Fin k))) (hψ : ∀ x, ‖ψ x‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Work.RatHurewicz.ICube d → EuclideanSpace ℝ (Fin k), Continuous P ∧
      (∀ x, ‖P x‖ ≤ 1) ∧ (∀ x : ↥K₂, ‖P x - ψ x‖ < ε) ∧ (∀ x : ↥K₁, P x ≠ 0) := by
  -- The cube as a subset of `ℝ^d`, and the coordinatewise projection `ℝ^d → I^d`.
  let ι : ICube d → EuclideanSpace ℝ (Fin d) :=
    fun x => WithLp.toLp 2 fun i => (x i : ℝ)
  let clamp : EuclideanSpace ℝ (Fin d) → ICube d := fun y i =>
    ⟨min 1 (max 0 (y i)),
      ⟨le_min zero_le_one (le_max_left 0 (y i)), min_le_left 1 (max 0 (y i))⟩⟩
  have hcoord : ∀ i : Fin d, Continuous fun y : EuclideanSpace ℝ (Fin d) => y i :=
    fun i => by fun_prop
  have hιcont : Continuous ι :=
    (PiLp.continuous_toLp 2 fun _ : Fin d => ℝ).comp
      (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i))
  have hclampcont : Continuous clamp :=
    continuous_pi fun i => Continuous.subtype_mk
      (continuous_const.min (continuous_const.max (hcoord i))) _
  have hclampι : ∀ x : ICube d, clamp (ι x) = x := by
    intro x
    funext i
    refine Subtype.ext ?_
    simp only [clamp, ι]
    rw [max_eq_right (x i).2.1, min_eq_right (x i).2.2]
  -- Tietze: extend `ψ` from `K₂` to all of the cube.
  obtain ⟨Φ, hΦ⟩ := ContinuousMap.exists_restrict_eq hK₂.isClosed ψ
  have hΦeq : ∀ x : ↥K₂, Φ (x : ICube d) = ψ x := fun x => by
    rw [← ContinuousMap.restrict_apply]
    exact congr($(hΦ) x)
  -- Pull back to `ℝ^d` and approximate smoothly.
  let Ψ : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin k) := fun y => Φ (clamp y)
  have hΨcont : Continuous Ψ := Φ.continuous.comp hclampcont
  have hΨeq : ∀ x : ICube d, Ψ (ι x) = Φ x := fun x => by
    change Φ (clamp (ι x)) = Φ x
    rw [hclampι x]
  obtain ⟨g, hgsmooth, hgapprox, -⟩ := hΨcont.exists_contDiff_approx (⊤ : ℕ∞)
    (continuous_const : Continuous fun _ : EuclideanSpace ℝ (Fin d) => ε / 4)
    (fun _ => by linarith)
  have hg1 : ContDiff ℝ 1 g := hgsmooth.of_le (by exact_mod_cast le_top)
  -- Low-dimensional Sard: the image of `g` is null, so a small `c` is not a value of `g`.
  have hnull : volume (Set.range g) = 0 :=
    Work.ThomBordism.Transversality.Sard.volume_range_eq_zero_of_contDiff_finrank_lt hdk g hg1
  obtain ⟨c, hcball, hcnotin⟩ :
      ∃ c ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (ε / 8), c ∉ Set.range g := by
    by_contra hcon
    have hsub' : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (ε / 8) ⊆ Set.range g := by
      intro c hc
      by_contra hcr
      exact hcon ⟨c, hc, hcr⟩
    have hle : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (ε / 8)) ≤ 0 := by
      rw [← hnull]
      exact measure_mono hsub'
    have hballpos : 0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (ε / 8)) :=
      Metric.measure_ball_pos volume 0 (by linarith : (0 : ℝ) < ε / 8)
    exact (lt_irrefl (0 : ENNReal)) (lt_of_lt_of_le hballpos hle)
  have hcnorm : ‖c‖ < ε / 8 := by
    rw [Metric.mem_ball, dist_zero_right] at hcball
    exact hcball
  refine ⟨fun x => (max 1 ‖g (ι x) - c‖)⁻¹ • (g (ι x) - c), ?_, ?_, ?_, ?_⟩
  · have hv : Continuous fun x : ICube d => g (ι x) - c :=
      (hgsmooth.continuous.comp hιcont).sub continuous_const
    have hden : Continuous fun x : ICube d => (max 1 ‖g (ι x) - c‖)⁻¹ :=
      (continuous_const.max hv.norm).inv₀ fun x =>
        ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) ‖g (ι x) - c‖))
    exact hden.smul hv
  · intro x
    exact norm_inv_max_smul_le_one (g (ι x) - c)
  · intro x
    set v : EuclideanSpace ℝ (Fin k) := g (ι (x : ICube d)) - c with hv
    have hgx : ‖g (ι (x : ICube d)) - ψ x‖ < ε / 4 := by
      have h1 : ‖g (ι (x : ICube d)) - Ψ (ι (x : ICube d))‖ < ε / 4 := by
        have h2 := hgapprox (ι (x : ICube d))
        rwa [dist_eq_norm] at h2
      have h3 : Ψ (ι (x : ICube d)) = ψ x := by
        rw [hΨeq (x : ICube d), hΦeq x]
      rwa [h3] at h1
    have hvψ : ‖v - ψ x‖ < 3 * ε / 8 := by
      have heq : v - ψ x = (g (ι (x : ICube d)) - ψ x) - c := by
        rw [hv]; abel
      rw [heq]
      calc ‖(g (ι (x : ICube d)) - ψ x) - c‖
          ≤ ‖g (ι (x : ICube d)) - ψ x‖ + ‖c‖ := norm_sub_le _ _
        _ < ε / 4 + ε / 8 := add_lt_add hgx hcnorm
        _ = 3 * ε / 8 := by ring
    have hvnorm : ‖v‖ < 1 + 3 * ε / 8 := by
      have heq : ‖(v - ψ x) + ψ x‖ = ‖v‖ := by rw [sub_add_cancel]
      calc ‖v‖ = ‖(v - ψ x) + ψ x‖ := heq.symm
        _ ≤ ‖v - ψ x‖ + ‖ψ x‖ := norm_add_le _ _
        _ < 3 * ε / 8 + 1 := add_lt_add_of_lt_of_le hvψ (hψ x)
        _ = 1 + 3 * ε / 8 := by ring
    have hclampdiff : ‖(max 1 ‖v‖)⁻¹ • v - v‖ < 3 * ε / 8 := by
      have h1 := norm_inv_max_smul_sub_le v
      have h2 : max 0 (‖v‖ - 1) < 3 * ε / 8 := max_lt (by linarith) (by linarith)
      linarith
    have hsplit : ‖(max 1 ‖v‖)⁻¹ • v - ψ x‖
        ≤ ‖(max 1 ‖v‖)⁻¹ • v - v‖ + ‖v - ψ x‖ := by
      calc ‖(max 1 ‖v‖)⁻¹ • v - ψ x‖
          = ‖((max 1 ‖v‖)⁻¹ • v - v) + (v - ψ x)‖ := by
            congr 1
            abel
        _ ≤ ‖(max 1 ‖v‖)⁻¹ • v - v‖ + ‖v - ψ x‖ := norm_add_le _ _
    calc ‖(max 1 ‖v‖)⁻¹ • v - ψ x‖
        ≤ ‖(max 1 ‖v‖)⁻¹ • v - v‖ + ‖v - ψ x‖ := hsplit
      _ < 3 * ε / 8 + 3 * ε / 8 := add_lt_add hclampdiff hvψ
      _ = 3 * ε / 4 := by ring
      _ < ε := by linarith
  · intro x hx
    have hpos : 0 < max 1 ‖g (ι (x : ICube d)) - c‖ :=
      lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hinner : g (ι (x : ICube d)) - c = 0 := by
      have h1 : (max 1 ‖g (ι (x : ICube d)) - c‖)⁻¹ • (g (ι (x : ICube d)) - c) = 0 :=
        hx
      rcases smul_eq_zero.mp h1 with h | h
      · exact absurd h (inv_ne_zero (ne_of_gt hpos))
      · exact h
    refine hcnotin ⟨ι (x : ICube d), ?_⟩
    exact sub_eq_zero.mp hinner

end Work.AttachPush
