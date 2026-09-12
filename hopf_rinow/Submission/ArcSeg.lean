import Submission.ModelArc
import Mathlib

open ContinuousLinearMap
open scoped ContDiff Topology BigOperators
open Set Metric Filter
open MeasureTheory intervalIntegral

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

/-- An affine reparametrization of a geodesic is a geodesic (with rescaled velocity), on any
symmetric window whose affine image lies inside the original window. -/
lemma geodesic_affine (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    {c vel : ℝ → E} (hc : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c (vel t) t)
    (hv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t)
    (a m : ℝ) (hwin : ∀ u ∈ Ioo (-δ) δ, m * u + a ∈ Ioo (-ε) ε) :
    (∀ u ∈ Ioo (-δ) δ,
      HasDerivAt (fun r => c (m * r + a)) (m • vel (m * u + a)) u) ∧
    (∀ u ∈ Ioo (-δ) δ,
      HasDerivAt (fun r => m • vel (m * r + a))
        (accel (g (c (m * u + a))) (fderiv ℝ g (c (m * u + a))) (m • vel (m * u + a))) u) := by
  refine ⟨?_, ?_⟩
  · intro u hu
    have hmem : m * u + a ∈ Ioo (-ε) ε := hwin u hu
    have hlin : HasDerivAt (fun r : ℝ => m * r + a) m u := by
      simpa using ((hasDerivAt_id (𝕜 := ℝ) u).const_mul m).const_add a
    exact HasDerivAt.scomp u (hc (m * u + a) hmem) hlin
  · intro u hu
    have hmem : m * u + a ∈ Ioo (-ε) ε := hwin u hu
    have hlin : HasDerivAt (fun r : ℝ => m * r + a) m u := by
      simpa using ((hasDerivAt_id (𝕜 := ℝ) u).const_mul m).const_add a
    have hder := HasDerivAt.scomp u (hv (m * u + a) hmem) hlin
    have hders := HasDerivAt.const_smul m hder
    refine hders.congr_deriv ?_
    rw [accel_smul]
    simp [smul_smul, pow_two]

/-- `expOf b Φ τu v₀ = γ t`: the exponential-ray from `γ s` with velocity `(t-s) • (γ' s)`
equals `γ t` for a flow-geodesic `γ`. -/
theorem arc_segment_ident_aux (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) {R0 τf : ℝ} (hR0 : 0 < R0)
    (hR0ge2 : (2 : ℝ) ≤ R0) (hτf : 0 < τf)
    (Φ : E × E → ℝ → E × E)
    (hΦ : ∀ z ∈ closedBall (x₀, 0) R0, Φ z 0 = z ∧
       (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall (x₀, 0) (R0 + 1)))
    {w : E} (hw : ‖w‖ ≤ R0) {s t : ℝ} (hst : s ≤ t)
    (hs : |s| < τf / 8) (ht : |t| < τf / 8)
    {τu : ℝ} (hτu : 0 < τu) (hτuτf : 2 * τu ≤ τf)
    (hb0 : ‖(Φ (x₀, w) s).1 - x₀‖ ≤ R0 / 2)
    (hvel : ‖(t - s) • (Φ (x₀, w) s).2‖ ≤ τu) :
    expOf ((Φ (x₀, w) s).1) Φ τu ((t - s) • (Φ (x₀, w) s).2) = (Φ (x₀, w) t).1 := by
  classical
  let b : E := (Φ (x₀, w) s).1
  let v₀ : E := (t - s) • (Φ (x₀, w) s).2
  let d : ℝ := t - s
  let z₁ : E × E := (x₀, w)
  let z₂ : E × E := (b, τu⁻¹ • v₀)
  change expOf b Φ τu v₀ = (Φ z₁ t).1
  have hz₁ : z₁ ∈ closedBall (x₀, 0) R0 := by
    dsimp [z₁]
    exact mem_pair_ball x₀ R0 (le_of_lt hR0) w hw
  have hτu_inv_pos : 0 < τu⁻¹ := by positivity
  have hw2n : ‖τu⁻¹ • v₀‖ ≤ 1 := by
    calc
      ‖τu⁻¹ • v₀‖ = ‖τu⁻¹‖ * ‖v₀‖ := by rw [norm_smul]
      _ = τu⁻¹ * ‖v₀‖ := by
        rw [Real.norm_eq_abs, abs_of_pos hτu_inv_pos]
      _ ≤ τu⁻¹ * τu := mul_le_mul_of_nonneg_left (by simpa [v₀] using hvel) (le_of_lt hτu_inv_pos)
      _ = 1 := by field_simp [ne_of_gt hτu]
  have hbR : ‖b - x₀‖ ≤ R0 / 2 := by
    simpa [b] using hb0
  have hz₂ : z₂ ∈ closedBall (x₀, 0) R0 := by
    dsimp [z₂]
    rw [← closedBall_prod_same]
    constructor
    · rw [mem_closedBall, dist_eq_norm]
      exact le_trans hbR (by linarith)
    · rw [mem_closedBall, dist_eq_norm]
      calc
        ‖τu⁻¹ • v₀ - 0‖ = ‖τu⁻¹ • v₀‖ := by simp
        _ ≤ 1 := hw2n
        _ ≤ R0 := by linarith
  have hΦ' : ∀ z ∈ closedBall (x₀, 0) R0, Φ z 0 = z ∧
       ∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    intro z hz
    exact ⟨(hΦ z hz).1, (hΦ z hz).2.1⟩
  -- γ is a flow-geodesic
  have hsplitγ := split_flow_geodesic g hg hinv (x₀, 0) hτf (closedBall (x₀, 0) R0) Φ hΦ' (z := z₁) hz₁
  let γ1 : ℝ → E := fun l => (Φ z₁ l).1
  let vel1 : ℝ → E := fun l => (Φ z₁ l).2
  have hcγ : ∀ l ∈ Ioo (-τf) τf, HasDerivAt γ1 (vel1 l) l := by
    intro l hl
    simpa [γ1, vel1] using hsplitγ.1 l hl
  have hvγ : ∀ l ∈ Ioo (-τf) τf,
      HasDerivAt vel1 (accel (g (γ1 l)) (fderiv ℝ g (γ1 l)) (vel1 l)) l := by
    intro l hl
    simpa [γ1, vel1] using hsplitγ.2 l hl
  -- window arithmetic
  have hdlt : |d| < τf / 4 := by
    have hts : |t - s| ≤ |t| + |s| := by
      calc
        |t - s| = |t + (-s)| := by rw [sub_eq_add_neg]
        _ ≤ |t| + |-s| := abs_add_le t (-s)
        _ = |t| + |s| := by rw [abs_neg]
    have hsum : |t| + |s| < τf / 4 := by nlinarith [ht, hs]
    simpa [d] using lt_of_le_of_lt hts hsum
  have hwinβ : ∀ u ∈ Ioo (-(2 : ℝ)) 2, d * u + s ∈ Ioo (-τf) τf := by
    intro u hu
    have huabs : |u| < 2 := abs_lt.mpr hu
    have hle : |d * u + s| ≤ |d| * |u| + |s| := by
      calc
        |d * u + s| ≤ |d * u| + |s| := abs_add_le (d * u) s
        _ = |d| * |u| + |s| := by rw [abs_mul]
    have hdu : |d| * |u| < τf / 2 := by
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_of_lt huabs) (abs_nonneg d))
        (by
          calc
            |d| * 2 < (τf / 4) * 2 := mul_lt_mul_of_pos_right hdlt (by norm_num)
            _ = τf / 2 := by ring)
    have hsum : |d| * |u| + |s| < τf := by nlinarith [hs, hdu, hτf]
    exact abs_lt.mp (lt_of_le_of_lt hle hsum)
  -- β := reparametrized arc (d·u + s ↦ γ) is a geodesic on Ioo (-2) 2
  have hβgeo := geodesic_affine (g := g) (hg := hg) (hinv := hinv) (ε := τf) (hε := hτf)
    (δ := (2 : ℝ)) (hδ := by norm_num) (c := γ1) (vel := vel1) (hc := hcγ) (hv := hvγ)
    (a := s) (m := d) (hwin := hwinβ)
  let β : ℝ → E := fun u => γ1 (d * u + s)
  let βvel : ℝ → E := fun u => d • vel1 (d * u + s)
  have hcβ : ∀ u ∈ Ioo (-(2 : ℝ)) 2, HasDerivAt β (βvel u) u := by
    intro u hu
    simpa [β, βvel] using hβgeo.1 u hu
  have hvβ : ∀ u ∈ Ioo (-(2 : ℝ)) 2,
      HasDerivAt βvel (accel (g (β u)) (fderiv ℝ g (β u)) (βvel u)) u := by
    intro u hu
    simpa [β, βvel] using hβgeo.2 u hu
  -- flow from z₂ is a geodesic
  have hsplit2 := split_flow_geodesic g hg hinv (x₀, 0) hτf (closedBall (x₀, 0) R0) Φ hΦ' (z := z₂) hz₂
  let c2 : ℝ → E := fun l => (Φ z₂ l).1
  let vel2 : ℝ → E := fun l => (Φ z₂ l).2
  have hc2 : ∀ l ∈ Ioo (-τf) τf, HasDerivAt c2 (vel2 l) l := by
    intro l hl
    simpa [c2, vel2] using hsplit2.1 l hl
  have hv2 : ∀ l ∈ Ioo (-τf) τf,
      HasDerivAt vel2 (accel (g (c2 l)) (fderiv ℝ g (c2 l)) (vel2 l)) l := by
    intro l hl
    simpa [c2, vel2] using hsplit2.2 l hl
  -- α := rescaled flow from z₂ is a geodesic on Ioo (-2) 2
  have hτu_abs : |τu| = τu := abs_of_pos hτu
  have hge : 2 ≤ τf / |τu| := by
    rw [hτu_abs]
    rw [le_div_iff₀ hτu]
    exact hτuτf
  have hres := geodesic_rescale (g := g) (hg := hg) (hinv := hinv) (ε := τf) (hε := hτf)
    (c := c2) (vel := vel2) (hc := hc2) (hv := hv2) (s := τu) (hs := ne_of_gt hτu)
  let α : ℝ → E := fun u => (Φ z₂ (τu * u)).1
  let αvel : ℝ → E := fun u => τu • (Φ z₂ (τu * u)).2
  have hwinα (u : ℝ) (hu : u ∈ Ioo (-(2 : ℝ)) 2) : u ∈ Ioo (-τf / |τu|) (τf / |τu|) := by
    have huabs : |u| < 2 := abs_lt.mpr hu
    have hlt : |u| < τf / |τu| := lt_of_lt_of_le huabs hge
    have hu' := abs_lt.mp hlt
    constructor
    · rw [neg_div]
      exact hu'.1
    · exact hu'.2
  have hcα : ∀ u ∈ Ioo (-(2 : ℝ)) 2, HasDerivAt α (αvel u) u := by
    intro u hu
    simpa [α, αvel, c2, vel2] using hres.1 u (hwinα u hu)
  have hvα : ∀ u ∈ Ioo (-(2 : ℝ)) 2,
      HasDerivAt αvel (accel (g (α u)) (fderiv ℝ g (α u)) (αvel u)) u := by
    intro u hu
    simpa [α, αvel, c2, vel2] using hres.2 u (hwinα u hu)
  -- initial data coincide at u = 0
  have hΦ0₂ : Φ z₂ 0 = z₂ := (hΦ z₂ hz₂).1
  have hsmul : τu • (τu⁻¹ • v₀) = v₀ := by
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hτu), one_smul]
  have hc0 : α 0 = β 0 := by
    calc
      α 0 = (Φ z₂ (τu * 0)).1 := rfl
      _ = (Φ z₂ 0).1 := by simp
      _ = z₂.1 := by rw [hΦ0₂]
      _ = b := rfl
      _ = (Φ z₁ s).1 := rfl
      _ = (Φ z₁ (d * 0 + s)).1 := by simp
      _ = β 0 := rfl
  have hv0 : αvel 0 = βvel 0 := by
    calc
      αvel 0 = τu • (Φ z₂ (τu * 0)).2 := rfl
      _ = τu • (Φ z₂ 0).2 := by simp
      _ = τu • z₂.2 := by rw [hΦ0₂]
      _ = v₀ := by simp [z₂, hsmul]
      _ = d • (Φ z₁ s).2 := rfl
      _ = d • (Φ z₁ (d * 0 + s)).2 := by simp
      _ = βvel 0 := rfl
  -- uniqueness on the common window Ioo (-2) 2
  rcases unique_geodesic (g := g) (hg := hg) (hinv := hinv) (ε := (2 : ℝ))
      (hε := by norm_num) (c₁ := α) (vel₁ := αvel) (c₂ := β) (vel₂ := βvel)
      (hc₁ := hcα) (hv₁ := hvα) (hc₂ := hcβ) (hv₂ := hvβ) (hc0 := hc0) (hv0 := hv0)
    with ⟨hagree, _⟩
  have h1 : (1 : ℝ) ∈ Ioo (-(2 : ℝ)) 2 := by norm_num
  have hmain : α 1 = β 1 := hagree 1 h1
  -- decode at u = 1
  have hα1 : α 1 = expOf b Φ τu v₀ := by
    dsimp [α, z₂]
    unfold expOf
    simp
  have hβ1 : β 1 = (Φ z₁ t).1 := by
    dsimp [β, γ1, d, z₁]
    congr 1
    ring
  calc
    expOf b Φ τu v₀ = α 1 := hα1.symm
    _ = β 1 := hmain
    _ = (Φ z₁ t).1 := hβ1

end
end Submission.Model
