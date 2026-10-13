import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.PhiStar.Psi0Defs
import Submission.Work.FTS.PhiStar.PsiDivS2Sup.derivG_reg_bound
import Submission.Work.FTS.PhiStar.PsiDivS2Sup.eq_zero_of_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar

set_option autoImplicit false

theorem PsiDivS2EqPfun {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {ψ : ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n ψ (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn ψ (Set.Icc 0 (Real.pi / 2))) (h0 : ψ 0 = 0)
    (hconst : ∃ c : ℝ, ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Real.sin θ ^ 2 * Real.cos θ ^ 3 * deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ
        - Work.FTS.PhiStar.Gzero α θ / 2 = c) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      deriv (fun θ' => ψ θ' / Real.sin (2 * θ')) θ
        = Work.FTS.PhiStar.Pfun α θ / Real.sin θ ^ 2 := by
  obtain ⟨c, hc⟩ := hconst
  let F : ℝ → ℝ := fun t => ψ t / Real.sin (2 * t)
  let H : ℝ → ℝ := fun t => F t + c * (Real.cos t / Real.sin t)
  let A : ℝ → ℝ := fun s => (c + Gzero α s / 2) / (Real.sin s ^ 2 * Real.cos s ^ 3)
      - c / Real.sin s ^ 2
  have hsin_pos : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2), 0 < Real.sin t :=
    fun t ht => Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [ht.2, Real.pi_pos])
  have hcos_pos : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2), 0 < Real.cos t :=
    fun t ht => Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
  -- `F` is smooth on the open interval
  have hsmF : ∀ n : ℕ, ContDiffOn ℝ n F (Set.Ioo 0 (Real.pi / 2)) := by
    intro n
    have hsin : ContDiffOn ℝ n (fun t : ℝ => Real.sin (2 * t)) (Set.Ioo 0 (Real.pi / 2)) := by
      fun_prop
    have hd := (hsm n).div hsin (fun t ht => by
      have h2 : 0 < Real.sin (2 * t) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_pos])
      exact ne_of_gt h2)
    exact hd
  have hFdiff : DifferentiableOn ℝ F (Set.Ioo 0 (Real.pi / 2)) :=
    (hsmF 1).differentiableOn (by norm_num)
  -- the first integral of the ODE gives a formula for `F'`
  have hFderiv : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2),
      deriv F t = (c + Gzero α t / 2) / (Real.sin t ^ 2 * Real.cos t ^ 3) := by
    intro t ht
    have h := hc t ht
    have hne : Real.sin t ^ 2 * Real.cos t ^ 3 ≠ 0 := by
      have h1 := hsin_pos t ht
      have h2 := hcos_pos t ht
      positivity
    have h2 : Real.sin t ^ 2 * Real.cos t ^ 3 * deriv F t = c + Gzero α t / 2 := by
      linarith
    rw [eq_div_iff hne]
    linarith
  -- derivative of `H`
  have hHderiv : ∀ t ∈ Set.Ioo (0:ℝ) (Real.pi / 2), HasDerivAt H (A t) t := by
    intro t ht
    have htπ : t ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ht
    have hsin0 : 0 < Real.sin t := hsin_pos t htπ
    have hF' : HasDerivAt F ((c + Gzero α t / 2) / (Real.sin t ^ 2 * Real.cos t ^ 3)) t := by
      have h := (hFdiff.differentiableAt (isOpen_Ioo.mem_nhds htπ)).hasDerivAt
      rwa [hFderiv t htπ] at h
    have hcot' : HasDerivAt (fun s : ℝ => Real.cos s / Real.sin s) (-(1 / Real.sin t ^ 2)) t := by
      have h := (Real.hasDerivAt_cos t).div (Real.hasDerivAt_sin t) (ne_of_gt hsin0)
      have h2 : (-Real.sin t * Real.sin t - Real.cos t * Real.cos t) / Real.sin t ^ 2
          = -(1 / Real.sin t ^ 2) := by
        have h3 : -Real.sin t * Real.sin t - Real.cos t * Real.cos t = -1 := by
          nlinarith [Real.sin_sq_add_cos_sq t]
        rw [h3, neg_div]
      rwa [h2] at h
    have hsum : HasDerivAt (fun y : ℝ => F y + c * (Real.cos y / Real.sin y)) (A t) t := by
      have h1 : HasDerivAt (fun y : ℝ => F y + c * (Real.cos y / Real.sin y))
          ((c + Gzero α t / 2) / (Real.sin t ^ 2 * Real.cos t ^ 3)
            + c * (-(1 / Real.sin t ^ 2))) t := hF'.add (hcot'.const_mul c)
      rwa [show ((c + Gzero α t / 2) / (Real.sin t ^ 2 * Real.cos t ^ 3)
            + c * (-(1 / Real.sin t ^ 2))) = A t from by simp only [A]; ring] at h1
    exact hsum
  -- the mean value theorem bounds `H` near `0`
  have hHbd : ∀ t ∈ Set.Ioo (0:ℝ) (1 / 2),
      |H t| ≤ |H (1 / 2)| + (24 * |c| + 7 * Real.pi ^ 2) * (1 / 2) := by
    intro t ht
    have hC : 0 ≤ 24 * |c| + 7 * Real.pi ^ 2 := by positivity
    have hder : ∀ x ∈ Set.Icc t (1 / 2), HasDerivWithinAt H (A x) (Set.Icc t (1 / 2)) x := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le ht.1 hx.1
      have hx' : x ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨hx0, by linarith [hx.2, Real.pi_gt_three]⟩
      exact (hHderiv x hx').hasDerivWithinAt
    have hbnd : ∀ x ∈ Set.Ico t (1 / 2), ‖A x‖ ≤ 24 * |c| + 7 * Real.pi ^ 2 := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le ht.1 hx.1
      have hx' : x ∈ Set.Ioo (0:ℝ) (1 / 2) := ⟨hx0, hx.2⟩
      have h := PsiDivS2Sup.derivG_reg_bound (c := c) hα hα4 hx'
      simpa only [A, Real.norm_eq_abs] using h
    have hmain := norm_image_sub_le_of_norm_deriv_le_segment' (f := H) (f' := A)
      (a := t) (b := (1 / 2 : ℝ)) hder hbnd (1 / 2) (Set.right_mem_Icc.mpr (le_of_lt ht.2))
    have h1 : |H t - H (1 / 2)| ≤ (24 * |c| + 7 * Real.pi ^ 2) * (1 / 2 - t) := by
      rw [abs_sub_comm]
      simpa only [Real.norm_eq_abs] using hmain
    have h2 : (1 / 2 - t) ≤ 1 / 2 := by linarith [ht.1]
    calc |H t| = |(H t - H (1 / 2)) + H (1 / 2)| := by ring_nf
      _ ≤ |H t - H (1 / 2)| + |H (1 / 2)| := abs_add_le _ _
      _ ≤ (24 * |c| + 7 * Real.pi ^ 2) * (1 / 2 - t) + |H (1 / 2)| := by linarith
      _ ≤ (24 * |c| + 7 * Real.pi ^ 2) * (1 / 2) + |H (1 / 2)| := by
            have := mul_le_mul_of_nonneg_left h2 hC
            linarith
      _ = |H (1 / 2)| + (24 * |c| + 7 * Real.pi ^ 2) * (1 / 2) := by ring
  -- assemble the hypothesis of the limit lemma
  have hb : ∀ t ∈ Set.Ioo (0:ℝ) (1 / 2),
      |ψ t + 2 * c * Real.cos t ^ 2|
        ≤ (|H (1 / 2)| + (24 * |c| + 7 * Real.pi ^ 2) * (1 / 2)) * Real.sin (2 * t) := by
    intro t ht
    have htπ : t ∈ Set.Ioo (0:ℝ) (Real.pi / 2) := ⟨ht.1, by linarith [ht.2, Real.pi_gt_three]⟩
    have hs0 : 0 < Real.sin (2 * t) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1]) (by linarith [ht.2, Real.pi_gt_three])
    have heq : ψ t + 2 * c * Real.cos t ^ 2 = Real.sin (2 * t) * H t := by
      have hsin : Real.sin t ≠ 0 :=
        ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1])
          (by linarith [ht.2, Real.pi_gt_three]))
      have hcos : Real.cos t ≠ 0 :=
        ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1, Real.pi_pos], htπ.2⟩)
      simp only [H, F, Real.sin_two_mul]
      field_simp
    rw [heq, abs_mul, abs_of_pos hs0]
    calc Real.sin (2 * t) * |H t| = |H t| * Real.sin (2 * t) := by ring
      _ ≤ (|H (1 / 2)| + (24 * |c| + 7 * Real.pi ^ 2) * (1 / 2)) * Real.sin (2 * t) :=
          mul_le_mul_of_nonneg_right (hHbd t ht) (le_of_lt hs0)
  have hcont' : ContinuousWithinAt ψ (Set.Icc 0 (1 / 2)) 0 := by
    have h1 : ContinuousWithinAt ψ (Set.Icc 0 (Real.pi / 2)) 0 :=
      hcont.continuousWithinAt ⟨le_rfl, by positivity⟩
    exact h1.mono (Set.Icc_subset_Icc le_rfl (by linarith [Real.pi_gt_three]))
  have hc0 : c = 0 := PsiDivS2Sup.eq_zero_of_bound hb hcont' h0
  -- conclusion
  intro θ hθ
  show deriv F θ = Work.FTS.PhiStar.Pfun α θ / Real.sin θ ^ 2
  rw [hFderiv θ hθ, hc0, zero_add]
  have hs : Real.sin θ ≠ 0 := ne_of_gt (hsin_pos θ hθ)
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (hcos_pos θ hθ)
  simp only [Work.FTS.PhiStar.Pfun]
  field_simp

end Work.FTS.PhiStar
