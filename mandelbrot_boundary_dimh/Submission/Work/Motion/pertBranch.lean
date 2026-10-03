import Mathlib
import Submission.Work.Motion.pertSetup
import Submission.Work.Motion.pertSupport
import Submission.Work.Motion.schwarz_pick_deriv
import Submission.Work.Motion.newtonHolo
import Submission.Work.Motion.deriv_Fmap
import Submission.Work.Motion.deriv_comp_TcIter
import Submission.Work.Motion.dTc_mul_deriv_eq_one

set_option maxHeartbeats 1000000

/-!
# One perturbed inverse branch

Everything for a single branch of the moving IFS: the Newton/contraction construction of the
perturbed branch, its holomorphy, and the quantitative estimates.
-/

namespace Work.Motion
namespace Pert

open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter Function
open scoped NNReal

noncomputable section

/-- Data for a single perturbed inverse branch. -/
structure BranchData (γ : ℂ) (τ : ℂ → ℂ) (m : ℕ) (p : ℂ) (r K : ℝ) where
  ρ : ℝ
  hρ : 0 < ρ
  s : ℝ
  hs : s < r / 2
  hs0 : 0 ≤ s
  θ : ℝ
  hθ0 : 0 ≤ θ
  hθ1 : θ < 1
  β : ℝ
  hβ : 0 < β
  Lc : ℝ
  hLc : 0 ≤ Lc
  G : ℝ
  hG : 0 ≤ G
  τc : ℂ → ℂ → ℂ
  base : ∀ z ∈ ball p (rInner r), τc γ z = τ z
  hol : DifferentiableOn ℂ (fun q : ℂ × ℂ => τc q.1 q.2) (ball γ ρ ×ˢ ball p (rInner r))
  dyn : ∀ c ∈ ball γ ρ, ∀ z ∈ ball p (rInner r), (Tc c)^[m] (τc c z) = z
  img : ∀ c ∈ ball γ ρ, MapsTo (τc c) (closedBall p (r / 2)) (closedBall p s)
  deriv_le : ∀ c ∈ ball γ ρ, ∀ z ∈ closedBall p (r / 2), ‖deriv (τc c) z‖ ≤ θ
  deriv_ge : ∀ c ∈ ball γ ρ, ∀ z ∈ closedBall p (r / 2), β ≤ ‖deriv (τc c) z‖
  lips_c : ∀ z ∈ closedBall p (r / 2), ∀ c ∈ ball γ ρ, ∀ c' ∈ ball γ ρ,
      ‖τc c z - τc c' z‖ ≤ Lc * ‖c - c'‖
  deriv_lips : ∀ z ∈ closedBall p (r / 2), ∀ z' ∈ closedBall p (r / 2),
      ∀ c ∈ ball γ ρ, ∀ c' ∈ ball γ ρ,
      ‖deriv (τc c) z - deriv (τc c') z'‖ ≤ G * (‖c - c'‖ + ‖z - z'‖)


variable {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}

/-- Norm of a difference in a product, second coordinate cancelling. -/
theorem prod_sub_norm_snd (a a' b : ℂ) :
    ‖((a, b) : ℂ × ℂ) - (a', b)‖ = ‖a - a'‖ := by
  rw [Prod.norm_def]
  simp

/-- Membership in a product of closed balls. -/
theorem mem_prod_closedBall_iff {γ p : ℂ} {ρ R : ℝ} {q : ℂ × ℂ} :
    q ∈ closedBall γ ρ ×ˢ closedBall p R ↔ ‖q.1 - γ‖ ≤ ρ ∧ ‖q.2 - p‖ ≤ R := by
  rw [mem_prod, mem_closedBall, mem_closedBall, dist_eq_norm, dist_eq_norm]

/-- Membership in a closed ball of the product. -/
theorem mem_closedBall_prod_iff {γ p : ℂ} {R : ℝ} {q : ℂ × ℂ} :
    q ∈ closedBall (γ, p) R ↔ max ‖q.1 - γ‖ ‖q.2 - p‖ ≤ R := by
  rw [mem_closedBall, Prod.dist_eq, dist_eq_norm, dist_eq_norm, max_le_iff]

/-- **Construction of one perturbed inverse branch.**  For a branch `i` of a conformal IFS of
`Tc c₀` there is a perturbed branch for parameters near `c₀`, holomorphic in `(c,z)`, with all the
quantitative properties needed for the moving coding map. -/
theorem branch_exists (hN : 2 ≤ N) (hIFS : IsConformalIFS N τ p r K)
    (hDyn : IsDynIFS c₀ τ n p r) (i : Fin N) :
    Nonempty (BranchData c₀ (τ i) (n i) p r K) := by
  have hIFS' : IsConformalIFS N τ p r K := hIFS
  obtain ⟨hr, hK, hdiff, hinj, hmaps, hdisj, hder⟩ := hIFS
  have hn1 : 1 ≤ n i := (hDyn i).1
  have hdyni : ∀ z ∈ ball p r, TcIter (n i) (c₀, τ i z) = z := by
    intro z hz
    rw [TcIter_eq]
    exact (hDyn i).2 z hz
  have hrin_pos : 0 < rInner r := by rw [rInner]; linarith
  have hrin_gt : r / 2 < rInner r := by rw [rInner]; linarith
  have hrin_lt : rInner r < r := by rw [rInner]; linarith
  have hr2 : 0 < r / 2 := by linarith
  have hsub : closedBall p (rInner r) ⊆ ball p r := by
    intro z hz; rw [mem_closedBall] at hz; rw [mem_ball]; linarith
  have hcore_sub : closedBall p (r / 2) ⊆ closedBall p (rInner r) :=
    closedBall_subset_closedBall (le_of_lt hrin_gt)
  have hcore_ball : closedBall p (r / 2) ⊆ ball p (rInner r) := by
    intro z hz; rw [mem_closedBall] at hz; rw [mem_ball]; linarith
  have hcore_ne : (closedBall p (r / 2)).Nonempty := ⟨p, mem_closedBall_self hr2.le⟩
  obtain ⟨s₀, hs₀lt, hs₀map⟩ := exists_image_bound (by omega : 1 ≤ N) hIFS'
  have hs₀nonneg : 0 ≤ s₀ := by
    have h := hs₀map i (mem_closedBall_self hr2.le)
    rw [mem_closedBall] at h
    linarith [dist_nonneg (x := τ i p) (y := p)]
  -- a bound for `‖deriv (τ i) z‖` on the inner closed ball
  set D : ℝ := r ^ 2 - (rInner r) ^ 2 with hDdef
  have hDpos : 0 < D := by
    have : rInner r ^ 2 < r ^ 2 := by nlinarith [hrin_lt, hrin_pos, hr]
    rw [hDdef]; linarith
  set Lτ : ℝ := (r / 2) * r / D with hLτdef
  have hLτpos : 0 < Lτ := div_pos (by positivity) hDpos
  have hder_le : ∀ z ∈ closedBall p (rInner r), ‖deriv (τ i) z‖ ≤ Lτ := by
    intro z hz
    have hzr : z ∈ ball p r := hsub hz
    have hsp := schwarz_pick_deriv (f := τ i) (c := p) (R := r) (M := r / 2) hr
      (hdiff i) (hmaps i) hzr
    have hzp : ‖z - p‖ ≤ rInner r := by
      have h' := hz; rw [mem_closedBall, dist_eq_norm] at h'; exact h'
    have hnum : (0:ℝ) ≤ r / 2 * r := by positivity
    have hden : D ≤ r ^ 2 - ‖z - p‖ ^ 2 := by
      rw [hDdef]; nlinarith [hzp, norm_nonneg (z - p), hrin_pos]
    calc ‖deriv (τ i) z‖ ≤ r / 2 * r / (r ^ 2 - ‖z - p‖ ^ 2) := hsp
      _ ≤ r / 2 * r / D := div_le_div_of_nonneg_left hnum hDpos hden
      _ = Lτ := by rw [hLτdef]
  have hτlip : ∀ z ∈ closedBall p (rInner r), ∀ z' ∈ closedBall p (rInner r),
      ‖τ i z - τ i z'‖ ≤ Lτ * ‖z - z'‖ := by
    intro z hz z' hz'
    refine (convex_closedBall p (rInner r)).norm_image_sub_le_of_norm_deriv_le
      (fun u hu => (hdiff i).differentiableAt (isOpen_ball.mem_nhds (hsub hu))) hder_le hz' hz
  -- the uniform lower bound `b₀` for `Bmap` at `c₀`
  set b₀ : ℝ := 2 * D / r ^ 2 with hb₀def
  have hb₀pos : 0 < b₀ := div_pos (by linarith) (by positivity)
  have hB₀ : ∀ z ∈ closedBall p (rInner r), b₀ ≤ ‖Bmap (τ i) (n i) (c₀, z)‖ := by
    intro z hz
    have hzr : z ∈ ball p r := hsub hz
    have hchain := deriv_comp_TcIter (n i) c₀
      ((hdiff i).differentiableAt (isOpen_ball.mem_nhds hzr))
    have hev : (fun y : ℂ => TcIter (n i) (c₀, τ i y)) =ᶠ[nhds z] id := by
      filter_upwards [isOpen_ball.mem_nhds hzr] with y hy
      exact hdyni y hy
    have hone : dTc (n i) (c₀, τ i z) * deriv (τ i) z = 1 := by
      rw [← hchain, hev.deriv_eq, deriv_id]
    have hd0 : 0 < ‖deriv (τ i) z‖ := by
      rcases eq_or_ne (deriv (τ i) z) 0 with h | h
      · rw [h, mul_zero] at hone; exact absurd hone.symm one_ne_zero
      · exact norm_pos_iff.mpr h
    have hnorm : ‖dTc (n i) (c₀, τ i z)‖ = ‖deriv (τ i) z‖⁻¹ := by
      have h := congrArg norm hone
      rw [norm_mul, norm_one] at h
      exact eq_inv_of_mul_eq_one_left h
    have hBmap : ‖Bmap (τ i) (n i) (c₀, z)‖ = ‖deriv (τ i) z‖⁻¹ := hnorm
    rw [hBmap]
    have hL := hder_le z hz
    have hstep : b₀ * Lτ = 1 := by
      rw [hb₀def, hLτdef]; field_simp
    rw [inv_eq_one_div, le_div_iff₀ hd0]
    calc b₀ * ‖deriv (τ i) z‖ ≤ b₀ * Lτ := mul_le_mul_of_nonneg_left hL hb₀pos.le
      _ = 1 := hstep

  -- Lipschitz constants on a big ball
  set R : ℝ := max 1 r with hRdef
  have hR1 : 1 ≤ R := le_max_left _ _
  have hRr : r ≤ R := le_max_right _ _
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  obtain ⟨Lg, hLg0, hLg⟩ := lipschitzOnBall (contDiff_TcIter (n i)) (c₀, p) R
  obtain ⟨Ld, hLd0, hLd⟩ := lipschitzOnBall (contDiff_dTc (n i)) (c₀, p) R
  have hmemK : ∀ (c y : ℂ), ‖c - c₀‖ ≤ 1 → ‖y - p‖ ≤ r →
      ((c, y) : ℂ × ℂ) ∈ closedBall (c₀, p) R := by
    intro c y hc hy
    rw [mem_closedBall_prod_iff, max_le_iff]
    exact ⟨le_trans hc hR1, le_trans hy hRr⟩
  have hcl : ∀ {z : ℂ}, ‖z - p‖ ≤ rInner r → z ∈ closedBall p (rInner r) := by
    intro z hz; rw [mem_closedBall, dist_eq_norm]; exact hz
  have hcl2 : ∀ {z : ℂ}, z ∈ closedBall p (rInner r) → ‖z - p‖ ≤ rInner r := by
    intro z hz; rw [mem_closedBall, dist_eq_norm] at hz; exact hz
  have hcτ : ∀ (c : ℂ) (y : ℂ), ‖c - c₀‖ ≤ 1 → ‖y - p‖ ≤ rInner r →
      ((c, τ i y) : ℂ × ℂ) ∈ closedBall (c₀, p) R := by
    intro c y hc hy
    refine hmemK c (τ i y) hc ?_
    have hyr : y ∈ ball p r := by rw [mem_ball, dist_eq_norm]; linarith
    have h := hmaps i hyr
    rw [mem_ball, dist_eq_norm] at h
    linarith
  set b : ℝ := b₀ / 2 with hbdef
  have hb : 0 < b := by rw [hbdef]; linarith
  have hb_le : b ≤ b₀ := by rw [hbdef]; linarith
  set ε : ℝ := min (r / 32) (min ((r / 2 - s₀) / 2) (b / (4 * (Ld + 1)))) with hεdef
  have hε : 0 < ε := by
    rw [hεdef]
    exact lt_min (by linarith) (lt_min (by linarith) (div_pos hb (by linarith)))
  have hε_r : ε ≤ r / 32 := le_trans (min_le_left _ _) le_rfl
  have hε_s : ε ≤ (r / 2 - s₀) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hε_L : ε ≤ b / (4 * (Ld + 1)) := le_trans (min_le_right _ _) (min_le_right _ _)
  set ρ : ℝ := min 1 (min (b₀ / (2 * (Ld + 1))) ((b * ε / 4) / (Lg + 1))) with hρdef
  have hρ : 0 < ρ := by
    rw [hρdef]
    exact lt_min one_pos (lt_min (div_pos hb₀pos (by linarith))
      (div_pos (by positivity) (by linarith)))
  have hρ1 : ρ ≤ 1 := le_trans (min_le_left _ _) le_rfl
  have hρb : ρ ≤ b₀ / (2 * (Ld + 1)) := le_trans (min_le_right _ _) (min_le_left _ _)
  have hρA : ρ ≤ (b * ε / 4) / (Lg + 1) := le_trans (min_le_right _ _) (min_le_right _ _)
  have hTmem : ∀ q : ℂ × ℂ, q ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r) ↔
      ‖q.1 - c₀‖ ≤ ρ ∧ ‖q.2 - p‖ ≤ rInner r := fun q => mem_prod_closedBall_iff
  have hmul_ld : Ld * (b₀ / (2 * (Ld + 1))) ≤ b₀ / 2 := by
    have h4 : Ld / (2 * (Ld + 1)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    calc Ld * (b₀ / (2 * (Ld + 1))) = b₀ * (Ld / (2 * (Ld + 1))) := by ring
      _ ≤ b₀ * (1 / 2) := mul_le_mul_of_nonneg_left h4 hb₀pos.le
      _ = b₀ / 2 := by ring
  have hmul_lg : Lg * ((b * ε / 4) / (Lg + 1)) ≤ b * ε / 4 := by
    have h4 : Lg / (Lg + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have h5 : 0 < b * ε / 4 := by positivity
    calc Lg * ((b * ε / 4) / (Lg + 1)) = (b * ε / 4) * (Lg / (Lg + 1)) := by ring
      _ ≤ (b * ε / 4) * 1 := mul_le_mul_of_nonneg_left h4 h5.le
      _ = b * ε / 4 := by ring
  have hmul_ld_eps : Ld * ε ≤ b / 4 := by
    have h4 : Ld * (b / (4 * (Ld + 1))) ≤ b / 4 := by
      have h5 : Ld / (4 * (Ld + 1)) ≤ 1 / 4 := by
        rw [div_le_div_iff₀ (by linarith) (by norm_num)]
        linarith
      calc Ld * (b / (4 * (Ld + 1))) = b * (Ld / (4 * (Ld + 1))) := by ring
        _ ≤ b * (1 / 4) := mul_le_mul_of_nonneg_left h5 hb.le
        _ = b / 4 := by ring
    exact le_trans (mul_le_mul_of_nonneg_left hε_L hLd0) h4
  have hBq : ∀ q ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r),
      b ≤ ‖Bmap (τ i) (n i) q‖ := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := (hTmem q).mp hq
    have hc1 : ‖q.1 - c₀‖ ≤ 1 := le_trans hq1 hρ1
    have hm1 := hcτ q.1 q.2 hc1 hq2
    have hm2 := hcτ c₀ q.2 (by simp) hq2
    have hL := hLd (q.1, τ i q.2) hm1 (c₀, τ i q.2) hm2
    rw [prod_sub_norm_snd] at hL
    have hB0 : b₀ ≤ ‖dTc (n i) (c₀, τ i q.2)‖ := by
      simpa only [Bmap_apply] using hB₀ q.2 (hcl hq2)
    have hBmap : Bmap (τ i) (n i) q = dTc (n i) (q.1, τ i q.2) := rfl
    rw [hBmap]
    have h2 : ‖dTc (n i) (c₀, τ i q.2) - dTc (n i) (q.1, τ i q.2)‖ ≤ Ld * ‖q.1 - c₀‖ := by
      rw [norm_sub_rev]; exact hL
    have h3 : ‖dTc (n i) (c₀, τ i q.2)‖ - ‖dTc (n i) (q.1, τ i q.2)‖ ≤ Ld * ‖q.1 - c₀‖ := by
      have h := abs_norm_sub_norm_le (dTc (n i) (c₀, τ i q.2)) (dTc (n i) (q.1, τ i q.2))
      linarith [le_abs_self (‖dTc (n i) (c₀, τ i q.2)‖ - ‖dTc (n i) (q.1, τ i q.2)‖), h, h2]
    have h4 : Ld * ‖q.1 - c₀‖ ≤ b₀ / 2 :=
      le_trans (mul_le_mul_of_nonneg_left hq1 hLd0)
        (le_trans (mul_le_mul_of_nonneg_left hρb hLd0) hmul_ld)
    have h5 : b₀ - Ld * ‖q.1 - c₀‖ ≤ ‖dTc (n i) (q.1, τ i q.2)‖ := by linarith
    have h6 : b ≤ b₀ - Ld * ‖q.1 - c₀‖ := by rw [hbdef]; linarith
    linarith
  have hAq : ∀ q ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r),
      ‖Amap (τ i) (n i) q‖ ≤ b * ε / 4 := by
    intro q hq
    obtain ⟨hq1, hq2⟩ := (hTmem q).mp hq
    have hc1 : ‖q.1 - c₀‖ ≤ 1 := le_trans hq1 hρ1
    have hm1 := hcτ q.1 q.2 hc1 hq2
    have hm2 := hcτ c₀ q.2 (by simp) hq2
    have hL := hLg (q.1, τ i q.2) hm1 (c₀, τ i q.2) hm2
    rw [prod_sub_norm_snd] at hL
    have h0 : TcIter (n i) (c₀, τ i q.2) = q.2 := hdyni q.2 (hsub (hcl hq2))
    have hAmap : Amap (τ i) (n i) q = TcIter (n i) (q.1, τ i q.2) - q.2 := rfl
    rw [hAmap]
    have h1 : ‖TcIter (n i) (q.1, τ i q.2) - q.2‖ ≤ Lg * ‖q.1 - c₀‖ := by
      have h2 : TcIter (n i) (q.1, τ i q.2) - q.2
          = TcIter (n i) (q.1, τ i q.2) - TcIter (n i) (c₀, τ i q.2) := by rw [h0]
      rw [h2]; exact hL
    have h3 : Lg * ‖q.1 - c₀‖ ≤ b * ε / 4 :=
      le_trans (mul_le_mul_of_nonneg_left hq1 hLg0)
        (le_trans (mul_le_mul_of_nonneg_left hρA hLg0) hmul_lg)
    linarith
  have hdq : ∀ q ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r),
      ∀ w ∈ closedBall (0 : ℂ) ε, DifferentiableAt ℂ (Fmap (τ i) (n i) q) w :=
    fun q _ w _ => differentiableAt_Fmap (τ i) (n i) q w
  have hbdq : ∀ q ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r),
      ∀ w ∈ closedBall (0 : ℂ) ε,
        ‖deriv (Fmap (τ i) (n i) q) w - Bmap (τ i) (n i) q‖ ≤ b / 4 := by
    intro q hq w hw
    obtain ⟨hq1, hq2⟩ := (hTmem q).mp hq
    have hw' : ‖w‖ ≤ ε := by
      have h := hw; rw [mem_closedBall, dist_eq_norm] at h; simpa using h
    have hc1 : ‖q.1 - c₀‖ ≤ 1 := le_trans hq1 hρ1
    have hτq : ‖τ i q.2 - p‖ < r / 2 := by
      have h := hmaps i (hsub (hcl hq2)); rw [mem_ball, dist_eq_norm] at h; exact h
    have hmem1 : ((q.1, τ i q.2 + w) : ℂ × ℂ) ∈ closedBall (c₀, p) R := by
      refine hmemK q.1 (τ i q.2 + w) hc1 ?_
      have h3 : ‖τ i q.2 + w - p‖ ≤ ‖τ i q.2 - p‖ + ‖w‖ := by
        rw [show τ i q.2 + w - p = (τ i q.2 - p) + w by ring]
        exact norm_add_le _ _
      linarith [hε_r, hr]
    have hmem2 : ((q.1, τ i q.2) : ℂ × ℂ) ∈ closedBall (c₀, p) R := hcτ q.1 q.2 hc1 hq2
    have hL := hLd (q.1, τ i q.2 + w) hmem1 (q.1, τ i q.2) hmem2
    have hdist : ‖((q.1, τ i q.2 + w) : ℂ × ℂ) - (q.1, τ i q.2)‖ = ‖w‖ := by
      rw [Prod.norm_def]; simp
    rw [hdist] at hL
    rw [deriv_Fmap, Bmap_apply]
    exact le_trans hL (le_trans (mul_le_mul_of_nonneg_left hw' hLd0) hmul_ld_eps)
  obtain ⟨v, hv1, hv2, hv3⟩ := newtonHolo (τ := τ i) (m := n i) (γ := c₀) (p := p)
    (ρ₁ := ρ) (r₁ := rInner r) (ε := ε) (b := b) hε hb
    ((hdiff i).mono (ball_subset_ball hrin_lt.le)) hBq hAq hdq hbdq
  set τc : ℂ → ℂ → ℂ := fun c z => τ i z + v (c, z) with hτcdef
  have hvle : ∀ q ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r), ‖v q‖ ≤ ε := by
    intro q hq
    have h := (hv1 q hq).1
    rw [mem_closedBall, dist_eq_norm] at h
    simpa using h
  have hbase : ∀ z ∈ ball p (rInner r), τc c₀ z = τ i z := by
    intro z hz
    have hzr : z ∈ ball p r := ball_subset_ball hrin_lt.le hz
    have hq : (c₀, z) ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r) := by
      rw [hTmem]
      refine ⟨?_, ?_⟩
      · simpa using hρ.le
      · rw [mem_ball, dist_eq_norm] at hz; linarith
    have h0 : TcIter (n i) (c₀, τ i z) = z := hdyni z hzr
    have hA0 : Amap (τ i) (n i) (c₀, z) = 0 := by
      simp only [Amap_apply]; rw [h0]; ring
    have heq : Fmap (τ i) (n i) (c₀, z) 0 = -Amap (τ i) (n i) (c₀, z) := by
      rw [Fmap_zero, hA0, neg_zero]
    have hv0 : v (c₀, z) = 0 := (hv2 (c₀, z) hq 0 (mem_closedBall_self hε.le) heq).symm
    rw [hτcdef]
    simp only
    rw [hv0, add_zero]
  have hdyn : ∀ c ∈ ball c₀ ρ, ∀ z ∈ ball p (rInner r), (Tc c)^[n i] (τc c z) = z := by
    intro c hc z hz
    have hc' : ‖c - c₀‖ ≤ ρ := by rw [mem_ball, dist_eq_norm] at hc; exact le_of_lt hc
    have hz' : ‖z - p‖ ≤ rInner r := by rw [mem_ball, dist_eq_norm] at hz; exact le_of_lt hz
    have hq : (c, z) ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r) := (hTmem _).mpr ⟨hc', hz'⟩
    have hfix := (hv1 (c, z) hq).2
    have hres := (Fmap_neg_Amap_iff (τ i) (n i) (c, z) (v (c, z))).mp hfix
    rw [← TcIter_eq]
    rw [hτcdef]
    simp only
    exact hres
  have himg : ∀ c ∈ ball c₀ ρ,
      MapsTo (τc c) (closedBall p (r / 2)) (closedBall p (s₀ + ε)) := by
    intro c hc z hz
    have hz' : z ∈ closedBall p (rInner r) := hcore_sub hz
    have hc' : ‖c - c₀‖ ≤ ρ := by rw [mem_ball, dist_eq_norm] at hc; exact le_of_lt hc
    have hz'' : ‖z - p‖ ≤ rInner r := by
      rw [mem_closedBall, dist_eq_norm] at hz'; exact hz'
    have hq : (c, z) ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r) := (hTmem _).mpr ⟨hc', hz''⟩
    have h1 : ‖τ i z - p‖ ≤ s₀ := by
      have h := hs₀map i hz; rw [mem_closedBall, dist_eq_norm] at h; exact h
    rw [mem_closedBall, dist_eq_norm]
    rw [hτcdef]
    simp only
    calc ‖τ i z + v (c, z) - p‖ = ‖(τ i z - p) + v (c, z)‖ := by ring_nf
      _ ≤ ‖τ i z - p‖ + ‖v (c, z)‖ := norm_add_le _ _
      _ ≤ s₀ + ε := by linarith [hvle (c, z) hq]
  -- the derivative upper bound `θ`
  set θ : ℝ := (r / 2 + ε) * rInner r / ((rInner r) ^ 2 - (r / 2) ^ 2) with hθdef
  have hdenθpos : 0 < (rInner r) ^ 2 - (r / 2) ^ 2 := by
    rw [rInner]; nlinarith [hr]
  have hθpos : 0 < θ := by
    rw [hθdef]
    exact div_pos (by positivity) hdenθpos
  have hθ1 : θ < 1 := by
    rw [hθdef, div_lt_one hdenθpos, rInner]
    have h1 : (r / 2 + ε) * (7 * r / 8) ≤ (r / 2 + r / 32) * (7 * r / 8) := by
      have h2 : r / 2 + ε ≤ r / 2 + r / 32 := by linarith
      have h3 : (0:ℝ) ≤ 7 * r / 8 := by linarith
      exact mul_le_mul_of_nonneg_right h2 h3
    have h2 : (r / 2 + r / 32) * (7 * r / 8) = 119 * r ^ 2 / 256 := by ring
    have h3 : (7 * r / 8) ^ 2 - (r / 2) ^ 2 = 33 * r ^ 2 / 64 := by ring
    have h4 : 0 < r ^ 2 := pow_pos hr 2
    linarith [h1, h2, h3, h4]
  have hτc_diff : ∀ c ∈ ball c₀ ρ, DifferentiableOn ℂ (τc c) (ball p (rInner r)) := by
    intro c hc
    refine ((hdiff i).mono (ball_subset_ball hrin_lt.le)).add ?_
    intro z hz
    have hmem : (c, z) ∈ ball c₀ ρ ×ˢ ball p (rInner r) := mem_prod.mpr ⟨hc, hz⟩
    have hopen : ball c₀ ρ ×ˢ ball p (rInner r) ∈ nhds (c, z) :=
      (isOpen_ball.prod isOpen_ball).mem_nhds hmem
    have h1 : DifferentiableAt ℂ v (c, z) := hv3.differentiableAt hopen
    have h2 : DifferentiableAt ℂ (fun z : ℂ => (c, z)) z :=
      DifferentiableAt.prodMk (differentiableAt_const c) differentiableAt_id
    exact (h1.comp z h2).differentiableWithinAt
  have hmaps_τc : ∀ c ∈ ball c₀ ρ, MapsTo (τc c) (ball p (rInner r)) (ball p (r / 2 + ε)) := by
    intro c hc z hz
    have hz' : ‖z - p‖ ≤ rInner r := by rw [mem_ball, dist_eq_norm] at hz; exact le_of_lt hz
    have hc' : ‖c - c₀‖ ≤ ρ := by rw [mem_ball, dist_eq_norm] at hc; exact le_of_lt hc
    have hq : (c, z) ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r) := (hTmem _).mpr ⟨hc', hz'⟩
    rw [mem_ball, dist_eq_norm]
    rw [hτcdef]
    simp only
    calc ‖τ i z + v (c, z) - p‖ = ‖(τ i z - p) + v (c, z)‖ := by ring_nf
      _ ≤ ‖τ i z - p‖ + ‖v (c, z)‖ := norm_add_le _ _
      _ < r / 2 + ε := by
          have h1 := hmaps i (ball_subset_ball hrin_lt.le hz)
          rw [mem_ball, dist_eq_norm] at h1
          linarith [hvle (c, z) hq]
  have hderiv_le : ∀ c ∈ ball c₀ ρ, ∀ z ∈ closedBall p (r / 2), ‖deriv (τc c) z‖ ≤ θ := by
    intro c hc z hz
    have hzr : z ∈ ball p (rInner r) := hcore_ball hz
    have hzp : ‖z - p‖ ≤ r / 2 := by
      have h := hz; rw [mem_closedBall, dist_eq_norm] at h; exact h
    have hsp := schwarz_pick_deriv (f := τc c) (c := p) (R := rInner r) (M := r / 2 + ε)
      hrin_pos (hτc_diff c hc) (hmaps_τc c hc) hzr
    have hden2 : ‖z - p‖ ^ 2 ≤ (r / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzp 2
    have hnum : (0:ℝ) ≤ (r / 2 + ε) * rInner r := by positivity
    calc ‖deriv (τc c) z‖ ≤ (r / 2 + ε) * rInner r / ((rInner r) ^ 2 - ‖z - p‖ ^ 2) := hsp
      _ ≤ (r / 2 + ε) * rInner r / ((rInner r) ^ 2 - (r / 2) ^ 2) :=
          div_le_div_of_nonneg_left hnum hdenθpos (by linarith)
      _ = θ := by rw [hθdef]
  -- the derivative lower bound `β`
  set s : ℝ := s₀ + ε with hsdef
  have hs_lt : s < r / 2 := by rw [hsdef]; linarith [hε_s, hs₀lt]
  have hs_0 : 0 ≤ s := by rw [hsdef]; linarith [le_of_lt hε, hs₀nonneg]
  have his_way : True := trivial
  have hcontd : ContinuousOn (fun q : ℂ × ℂ => ‖dTc (n i) q‖) (closedBall (c₀, p) R) :=
    ((contDiff_dTc (n i)).continuous.norm).continuousOn
  obtain ⟨q₁, hq₁, hmax⟩ := (isCompact_closedBall (c₀, p) R).exists_isMaxOn
    ⟨(c₀, p), mem_closedBall_self hRpos.le⟩ hcontd
  have hMBpos : 0 < ‖dTc (n i) q₁‖ := by
    have hmem : ((c₀, τ i p) : ℂ × ℂ) ∈ closedBall (c₀, p) R := by
      refine hcτ c₀ p (by simp) ?_
      simpa using hrin_pos.le
    have h1 : ‖dTc (n i) (c₀, τ i p)‖ ≤ ‖dTc (n i) q₁‖ := hmax hmem
    have h2 : b₀ ≤ ‖dTc (n i) (c₀, τ i p)‖ := by
      simpa only [Bmap_apply] using hB₀ p (hcl (by simpa using hrin_pos.le))
    linarith
  set β : ℝ := (‖dTc (n i) q₁‖)⁻¹ with hβdef
  have hβpos : 0 < β := by rw [hβdef]; exact inv_pos.mpr hMBpos
  have hderiv_ge : ∀ c ∈ ball c₀ ρ, ∀ z ∈ closedBall p (r / 2), β ≤ ‖deriv (τc c) z‖ := by
    intro c hc z hz
    have hzr : z ∈ ball p (rInner r) := hcore_ball hz
    have hcd : DifferentiableAt ℂ (τc c) z :=
      (hτc_diff c hc).differentiableAt (isOpen_ball.mem_nhds hzr)
    have hfix : ∀ᶠ y in nhds z, TcIter (n i) (c, τc c y) = y := by
      filter_upwards [isOpen_ball.mem_nhds hzr] with y hy
      simpa only [TcIter_eq] using hdyn c hc y hy
    have hone := dTc_mul_deriv_eq_one (n i) c hcd hfix
    have hY0 : (0:ℝ) < ‖dTc (n i) (c, τc c z)‖ := by
      rcases eq_or_ne (dTc (n i) (c, τc c z)) 0 with h | h
      · rw [h, zero_mul] at hone; exact absurd hone.symm one_ne_zero
      · exact norm_pos_iff.mpr h
    have hlin : ‖deriv (τc c) z‖ = ‖dTc (n i) (c, τc c z)‖⁻¹ := by
      have h := congrArg norm hone
      rw [norm_mul, norm_one] at h
      exact eq_inv_of_mul_eq_one_right h
    have hmem : ((c, τc c z) : ℂ × ℂ) ∈ closedBall (c₀, p) R := by
      refine hmemK c (τc c z) ?_ ?_
      · have hc' : ‖c - c₀‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hc
        linarith [hρ1, hc']
      · have h1 : τc c z ∈ closedBall p s := himg c hc hz
        have h1' : ‖τc c z - p‖ ≤ s := by
          have h := h1; rw [mem_closedBall, dist_eq_norm] at h; exact h
        linarith [h1', hs_lt, hRr]
    have h2 := hmax hmem
    rw [hlin, hβdef]
    exact (inv_le_inv₀ hMBpos hY0).mpr h2
  -- the expansion estimate
  have hexp : ∀ q ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r),
      ∀ w ∈ closedBall (0 : ℂ) ε, ∀ w' ∈ closedBall (0 : ℂ) ε,
      b / 4 * ‖w - w'‖ ≤ ‖Fmap (τ i) (n i) q w - Fmap (τ i) (n i) q w'‖ :=
    fun q hq w hw w' hw' =>
      newtonLowerBound hb (Fmap_zero _ _ _) (hBq q hq) (hdq q hq) (hbdq q hq) hw hw'
  have hmemτ : ∀ (c : ℂ) (z : ℂ), ‖c - c₀‖ ≤ 1 → ‖τ i z + v (c, z) - p‖ ≤ r →
      ((c, τ i z + v (c, z)) : ℂ × ℂ) ∈ closedBall (c₀, p) R :=
    fun c z hc hz => hmemK c (τ i z + v (c, z)) hc hz
  -- joint Lipschitz continuity of `v`
  have hv_lip : ∀ q ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r),
      ∀ q' ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r),
      ‖v q - v q'‖ ≤ (4 * Lg / b) * ‖q.1 - q'.1‖ + (4 * (Lg * Lτ + 1) / b) * ‖q.2 - q'.2‖ := by
    intro q hq q' hq'
    obtain ⟨hq1, hq2⟩ := (hTmem q).mp hq
    obtain ⟨hq1', hq2'⟩ := (hTmem q').mp hq'
    have hvq := (hv1 q hq).1
    have hvq' := (hv1 q' hq').1
    have hexp' := hexp q hq (v q) hvq (v q') hvq'
    have hF : Fmap (τ i) (n i) q (v q) - Fmap (τ i) (n i) q (v q')
        = -(TcIter (n i) (q.1, τ i q.2 + v q') - q.2) := by
      rw [(hv1 q hq).2, Fmap_apply, Amap_apply]; ring
    rw [hF, norm_neg] at hexp'
    have hfix' : TcIter (n i) (q'.1, τ i q'.2 + v q') = q'.2 :=
      (Fmap_neg_Amap_iff (τ i) (n i) q' (v q')).mp (hv1 q' hq').2
    set y : ℂ := τ i q.2 + v q' with hydef
    set y' : ℂ := τ i q'.2 + v q' with hy'def
    have hτq : ‖τ i q.2 - p‖ < r / 2 := by
      have h := hmaps i (hsub (hcl hq2)); rw [mem_ball, dist_eq_norm] at h; exact h
    have hτq' : ‖τ i q'.2 - p‖ < r / 2 := by
      have h := hmaps i (hsub (hcl hq2')); rw [mem_ball, dist_eq_norm] at h; exact h
    have hyr : ‖y - p‖ ≤ r := by
      have h3 : ‖y - p‖ ≤ ‖τ i q.2 - p‖ + ‖v q'‖ := by
        rw [hydef, show τ i q.2 + v q' - p = (τ i q.2 - p) + v q' by ring]
        exact norm_add_le _ _
      linarith [hε_r, hr, hvle q' hq']
    have hy'r : ‖y' - p‖ ≤ r := by
      have h3 : ‖y' - p‖ ≤ ‖τ i q'.2 - p‖ + ‖v q'‖ := by
        rw [hy'def, show τ i q'.2 + v q' - p = (τ i q'.2 - p) + v q' by ring]
        exact norm_add_le _ _
      linarith [hε_r, hr, hvle q' hq']
    have hm1 : ((q.1, y) : ℂ × ℂ) ∈ closedBall (c₀, p) R := hmemK q.1 y (le_trans hq1 hρ1) hyr
    have hm2 : ((q'.1, y) : ℂ × ℂ) ∈ closedBall (c₀, p) R := hmemK q'.1 y (le_trans hq1' hρ1) hyr
    have hm3 : ((q'.1, y') : ℂ × ℂ) ∈ closedBall (c₀, p) R := hmemK q'.1 y' (le_trans hq1' hρ1) hy'r
    have hL1 := hLg (q.1, y) hm1 (q'.1, y) hm2
    rw [prod_sub_norm_snd] at hL1
    have hL2 := hLg (q'.1, y) hm2 (q'.1, y') hm3
    have hdist2 : ‖((q'.1, y) : ℂ × ℂ) - (q'.1, y')‖ = ‖y - y'‖ := by
      rw [Prod.norm_def]; simp
    rw [hdist2] at hL2
    have hylip : ‖y - y'‖ ≤ Lτ * ‖q.2 - q'.2‖ := by
      have h : ‖y - y'‖ = ‖τ i q.2 - τ i q'.2‖ := by
        rw [hydef, hy'def]
        have : τ i q.2 + v q' - (τ i q'.2 + v q') = τ i q.2 - τ i q'.2 := by ring
        rw [this]
      rw [h]
      exact hτlip q.2 (hcl hq2) q'.2 (hcl hq2')
    have hnorm : ‖q'.2 - q.2‖ = ‖q.2 - q'.2‖ := norm_sub_rev _ _
    have hkey : ‖TcIter (n i) (q.1, y) - q.2‖
        ≤ Lg * ‖q.1 - q'.1‖ + (Lg * Lτ + 1) * ‖q.2 - q'.2‖ := by
      have htri := dist_triangle4 (TcIter (n i) (q.1, y)) (TcIter (n i) (q'.1, y))
        (TcIter (n i) (q'.1, y')) q.2
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, dist_eq_norm] at htri
      have hlast : ‖TcIter (n i) (q'.1, y') - q.2‖ = ‖q'.2 - q.2‖ := by rw [hfix']
      rw [hlast] at htri
      nlinarith [htri, hL1, hL2, hylip, hnorm, norm_nonneg (q.2 - q'.2)]
    have h5 : b / 4 * ‖v q - v q'‖
        ≤ Lg * ‖q.1 - q'.1‖ + (Lg * Lτ + 1) * ‖q.2 - q'.2‖ := le_trans hexp' hkey
    have h4 : 0 < b / 4 := by linarith
    have h6 : ‖v q - v q'‖ * b
        ≤ 4 * (Lg * ‖q.1 - q'.1‖ + (Lg * Lτ + 1) * ‖q.2 - q'.2‖) := by
      have h5' : (b / 4 * ‖v q - v q'‖) * 4
          ≤ (Lg * ‖q.1 - q'.1‖ + (Lg * Lτ + 1) * ‖q.2 - q'.2‖) * 4 :=
        mul_le_mul_of_nonneg_right h5 (by norm_num)
      linarith [h5']
    have h7 : ‖v q - v q'‖
        ≤ 4 * (Lg * ‖q.1 - q'.1‖ + (Lg * Lτ + 1) * ‖q.2 - q'.2‖) / b := by
      rw [le_div_iff₀ hb]; exact h6
    have h8 : 4 * (Lg * ‖q.1 - q'.1‖ + (Lg * Lτ + 1) * ‖q.2 - q'.2‖) / b
        = (4 * Lg / b) * ‖q.1 - q'.1‖ + (4 * (Lg * Lτ + 1) / b) * ‖q.2 - q'.2‖ := by
      field_simp
    linarith [h7, h8.le, h8.ge]
  have hτc_lip : ∀ z ∈ closedBall p (r / 2), ∀ z' ∈ closedBall p (r / 2),
      ∀ c ∈ ball c₀ ρ, ∀ c' ∈ ball c₀ ρ,
      ‖τc c z - τc c' z'‖ ≤ Lτ * ‖z - z'‖ + (4 * Lg / b) * ‖c - c'‖
        + (4 * (Lg * Lτ + 1) / b) * ‖z - z'‖ := by
    intro z hz z' hz' c hc c' hc'
    have hzr : ‖z - p‖ ≤ rInner r := hcl2 (hcore_sub hz)
    have hzr' : ‖z' - p‖ ≤ rInner r := hcl2 (hcore_sub hz')
    have hq : (c, z) ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r) :=
      (hTmem _).mpr ⟨le_of_lt (by simpa [mem_ball, dist_eq_norm] using hc), hzr⟩
    have hq' : (c', z') ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r) :=
      (hTmem _).mpr ⟨le_of_lt (by simpa [mem_ball, dist_eq_norm] using hc'), hzr'⟩
    have h := hv_lip (c, z) hq (c', z') hq'
    have hz1 : ‖(c, z).1 - (c', z').1‖ = ‖c - c'‖ := rfl
    have hz2 : ‖(c, z).2 - (c', z').2‖ = ‖z - z'‖ := rfl
    rw [hz1, hz2] at h
    have hτ := hτlip z (hcl hzr) z' (hcl hzr')
    rw [hτcdef]
    simp only
    have h3 : τ i z + v (c, z) - (τ i z' + v (c', z'))
        = (τ i z - τ i z') + (v (c, z) - v (c', z')) := by ring
    rw [h3]
    have h4 := norm_add_le (τ i z - τ i z') (v (c, z) - v (c', z'))
    linarith
  have hlips_c : ∀ z ∈ closedBall p (r / 2), ∀ c ∈ ball c₀ ρ, ∀ c' ∈ ball c₀ ρ,
      ‖τc c z - τc c' z‖ ≤ (4 * Lg / b) * ‖c - c'‖ := by
    intro z hz c hc c' hc'
    have hzr : ‖z - p‖ ≤ rInner r := hcl2 (hcore_sub hz)
    have hq : (c, z) ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r) :=
      (hTmem _).mpr ⟨le_of_lt (by simpa [mem_ball, dist_eq_norm] using hc), hzr⟩
    have hq' : (c', z) ∈ closedBall c₀ ρ ×ˢ closedBall p (rInner r) :=
      (hTmem _).mpr ⟨le_of_lt (by simpa [mem_ball, dist_eq_norm] using hc'), hzr⟩
    have h := hv_lip (c, z) hq (c', z) hq'
    simp only [Prod.fst, Prod.snd, sub_self, norm_zero, mul_zero, add_zero] at h
    rw [hτcdef]
    simp only
    have h3 : τ i z + v (c, z) - (τ i z + v (c', z)) = v (c, z) - v (c', z) := by ring
    rw [h3]
    linarith [h]
  -- the derivative Lipschitz bound
  have hrecip : ∀ Y Y' : ℂ, 1 / θ ≤ ‖Y‖ → 1 / θ ≤ ‖Y'‖ → ‖Y⁻¹ - Y'⁻¹‖ ≤ ‖Y - Y'‖ * θ ^ 2 := by
    intro Y Y' hY hY'
    have hYpos : 0 < ‖Y‖ := lt_of_lt_of_le (by positivity) hY
    have hY'pos : 0 < ‖Y'‖ := lt_of_lt_of_le (by positivity) hY'
    have hYne : Y ≠ 0 := norm_pos_iff.mp hYpos
    have hY'ne : Y' ≠ 0 := norm_pos_iff.mp hY'pos
    have hkey : Y⁻¹ - Y'⁻¹ = (Y' - Y) / (Y * Y') := by
      field_simp
    rw [hkey, norm_div, norm_mul, norm_sub_rev]
    rw [div_le_iff₀ (by positivity)]
    have h1 : (1 / θ) * (1 / θ) ≤ ‖Y‖ * ‖Y'‖ :=
      mul_le_mul hY hY' (by positivity) (norm_nonneg _)
    have h2 : 1 ≤ θ ^ 2 * (‖Y‖ * ‖Y'‖) := by
      have h3 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ θ * θ)
      have h4 : θ * θ * ((1 / θ) * (1 / θ)) = 1 := by field_simp
      linarith [h3, h4]
    nlinarith [h2, norm_nonneg (Y - Y')]
  have hY1 : ∀ c ∈ ball c₀ ρ, ∀ z ∈ closedBall p (r / 2),
      1 / θ ≤ ‖dTc (n i) (c, τc c z)‖ := by
    intro c hc z hz
    have hzr : z ∈ ball p (rInner r) := hcore_ball hz
    have hcd : DifferentiableAt ℂ (τc c) z :=
      (hτc_diff c hc).differentiableAt (isOpen_ball.mem_nhds hzr)
    have hfix : ∀ᶠ y in nhds z, TcIter (n i) (c, τc c y) = y := by
      filter_upwards [isOpen_ball.mem_nhds hzr] with y hy
      simpa only [TcIter_eq] using hdyn c hc y hy
    have hone := dTc_mul_deriv_eq_one (n i) c hcd hfix
    have hYne : dTc (n i) (c, τc c z) ≠ 0 := by
      intro hh
      rw [hh, zero_mul] at hone
      exact one_ne_zero hone.symm
    have hYpos : 0 < ‖dTc (n i) (c, τc c z)‖ := norm_pos_iff.mpr hYne
    have hY : deriv (τc c) z = (dTc (n i) (c, τc c z))⁻¹ := eq_inv_of_mul_eq_one_right hone
    have hle := hderiv_le c hc z hz
    rw [hY, norm_inv] at hle
    rw [one_div]
    exact (inv_le_comm₀ hθpos hYpos).mpr hle
  have hderiv_lips : ∀ z ∈ closedBall p (r / 2), ∀ z' ∈ closedBall p (r / 2),
      ∀ c ∈ ball c₀ ρ, ∀ c' ∈ ball c₀ ρ,
      ‖deriv (τc c) z - deriv (τc c') z'‖
        ≤ θ ^ 2 * (Ld * (1 + 4 * Lg / b) + Ld * (Lτ + 4 * (Lg * Lτ + 1) / b))
          * (‖c - c'‖ + ‖z - z'‖) := by
    intro z hz z' hz' c hc c' hc'
    have hzr : z ∈ ball p (rInner r) := hcore_ball hz
    have hzr' : z' ∈ ball p (rInner r) := hcore_ball hz'
    have hcd : DifferentiableAt ℂ (τc c) z :=
      (hτc_diff c hc).differentiableAt (isOpen_ball.mem_nhds hzr)
    have hcd' : DifferentiableAt ℂ (τc c') z' :=
      (hτc_diff c' hc').differentiableAt (isOpen_ball.mem_nhds hzr')
    have hfix : ∀ᶠ y in nhds z, TcIter (n i) (c, τc c y) = y := by
      filter_upwards [isOpen_ball.mem_nhds hzr] with y hy
      simpa only [TcIter_eq] using hdyn c hc y hy
    have hfix' : ∀ᶠ y in nhds z', TcIter (n i) (c', τc c' y) = y := by
      filter_upwards [isOpen_ball.mem_nhds hzr'] with y hy
      simpa only [TcIter_eq] using hdyn c' hc' y hy
    have hone := dTc_mul_deriv_eq_one (n i) c hcd hfix
    have hone' := dTc_mul_deriv_eq_one (n i) c' hcd' hfix'
    have hY : deriv (τc c) z = (dTc (n i) (c, τc c z))⁻¹ := eq_inv_of_mul_eq_one_right hone
    have hY' : deriv (τc c') z' = (dTc (n i) (c', τc c' z'))⁻¹ := eq_inv_of_mul_eq_one_right hone'
    have hb1 := hY1 c hc z hz
    have hb2 := hY1 c' hc' z' hz'
    have hm1 : ((c, τc c z) : ℂ × ℂ) ∈ closedBall (c₀, p) R := by
      refine hmemK c (τc c z) ?_ ?_
      · have hc'' : ‖c - c₀‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hc
        linarith [hρ1, hc'']
      · have h1 : τc c z ∈ closedBall p s := himg c hc hz
        have h := h1; rw [mem_closedBall, dist_eq_norm] at h; linarith [h, hs_lt, hRr]
    have hm2 : ((c', τc c' z') : ℂ × ℂ) ∈ closedBall (c₀, p) R := by
      refine hmemK c' (τc c' z') ?_ ?_
      · have hc'' : ‖c' - c₀‖ < ρ := by simpa [mem_ball, dist_eq_norm] using hc'
        linarith [hρ1, hc'']
      · have h1 : τc c' z' ∈ closedBall p s := himg c' hc' hz'
        have h := h1; rw [mem_closedBall, dist_eq_norm] at h; linarith [h, hs_lt, hRr]
    have hL := hLd (c, τc c z) hm1 (c', τc c' z') hm2
    have hd : ‖((c, τc c z) : ℂ × ℂ) - (c', τc c' z')‖
        ≤ ‖c - c'‖ + ‖τc c z - τc c' z'‖ := by
      rw [Prod.norm_def]
      exact max_le (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))
    have hτclip := hτc_lip z hz z' hz' c hc c' hc'
    have hbound : ‖((c, τc c z) : ℂ × ℂ) - (c', τc c' z')‖
        ≤ (1 + 4 * Lg / b) * ‖c - c'‖ + (Lτ + 4 * (Lg * Lτ + 1) / b) * ‖z - z'‖ := by
      linarith [hd, hτclip, norm_nonneg (c - c'), norm_nonneg (z - z'),
        norm_nonneg (τc c z - τc c' z')]
    have hYdiff : ‖dTc (n i) (c, τc c z) - dTc (n i) (c', τc c' z')‖
        ≤ Ld * (1 + 4 * Lg / b) * ‖c - c'‖ + Ld * (Lτ + 4 * (Lg * Lτ + 1) / b) * ‖z - z'‖ := by
      have h1 : Ld * ‖((c, τc c z) : ℂ × ℂ) - (c', τc c' z')‖
          ≤ Ld * ((1 + 4 * Lg / b) * ‖c - c'‖ + (Lτ + 4 * (Lg * Lτ + 1) / b) * ‖z - z'‖) :=
        mul_le_mul_of_nonneg_left hbound hLd0
      linarith [hL, h1]
    have hsum : Ld * (1 + 4 * Lg / b) * ‖c - c'‖ + Ld * (Lτ + 4 * (Lg * Lτ + 1) / b) * ‖z - z'‖
        ≤ (Ld * (1 + 4 * Lg / b) + Ld * (Lτ + 4 * (Lg * Lτ + 1) / b))
          * (‖c - c'‖ + ‖z - z'‖) := by
      have hA : 0 ≤ Ld * (1 + 4 * Lg / b) := mul_nonneg hLd0 (by positivity)
      have hB : 0 ≤ Ld * (Lτ + 4 * (Lg * Lτ + 1) / b) := mul_nonneg hLd0 (by positivity)
      nlinarith [norm_nonneg (c - c'), norm_nonneg (z - z')]
    calc ‖deriv (τc c) z - deriv (τc c') z'‖
        = ‖(dTc (n i) (c, τc c z))⁻¹ - (dTc (n i) (c', τc c' z'))⁻¹‖ := by rw [hY, hY']
      _ ≤ ‖dTc (n i) (c, τc c z) - dTc (n i) (c', τc c' z')‖ * θ ^ 2 := hrecip _ _ hb1 hb2
      _ ≤ (Ld * (1 + 4 * Lg / b) * ‖c - c'‖ + Ld * (Lτ + 4 * (Lg * Lτ + 1) / b) * ‖z - z'‖)
            * θ ^ 2 := mul_le_mul_of_nonneg_right hYdiff (sq_nonneg θ)
      _ ≤ ((Ld * (1 + 4 * Lg / b) + Ld * (Lτ + 4 * (Lg * Lτ + 1) / b))
            * (‖c - c'‖ + ‖z - z'‖)) * θ ^ 2 :=
          mul_le_mul_of_nonneg_right hsum (sq_nonneg θ)
      _ = θ ^ 2 * (Ld * (1 + 4 * Lg / b) + Ld * (Lτ + 4 * (Lg * Lτ + 1) / b))
            * (‖c - c'‖ + ‖z - z'‖) := by ring

  -- holomorphy of `(c,z) ↦ τc c z`
  have hhol : DifferentiableOn ℂ (fun q : ℂ × ℂ => τc q.1 q.2)
      (ball c₀ ρ ×ˢ ball p (rInner r)) := by
    have h1 : DifferentiableOn ℂ (fun q : ℂ × ℂ => τ i q.2)
        (ball c₀ ρ ×ˢ ball p (rInner r)) :=
      (hdiff i).comp differentiable_snd.differentiableOn
        (fun q hq => ball_subset_ball hrin_lt.le (mem_prod.mp hq).2)
    have heq : (fun q : ℂ × ℂ => τc q.1 q.2) = fun q => τ i q.2 + v q := by
      funext q
      rw [hτcdef]
    rw [heq]
    exact h1.add hv3
  let Gc : ℝ := θ ^ 2 * (Ld * (1 + 4 * Lg / b) + Ld * (Lτ + 4 * (Lg * Lτ + 1) / b))
  have hGval : 0 ≤ Gc := by
    have h1' : 0 ≤ Ld * (1 + 4 * Lg / b) := mul_nonneg hLd0 (by positivity)
    have h2' : 0 ≤ Ld * (Lτ + 4 * (Lg * Lτ + 1) / b) := mul_nonneg hLd0 (by positivity)
    exact mul_nonneg (sq_nonneg θ) (add_nonneg h1' h2')
  have hBD : BranchData c₀ (τ i) (n i) p r K :=
    { ρ := ρ, hρ := hρ, s := s, hs := hs_lt, hs0 := hs_0, θ := θ,
      hθ0 := hθpos.le, hθ1 := hθ1, β := β, hβ := hβpos, Lc := 4 * Lg / b,
      hLc := by positivity, G := Gc, hG := hGval,
      τc := τc, base := hbase, hol := hhol, dyn := hdyn, img := himg,
      deriv_le := hderiv_le, deriv_ge := hderiv_ge, lips_c := hlips_c,
      deriv_lips := hderiv_lips }
  exact ⟨hBD⟩


end

end Pert
end Work.Motion
