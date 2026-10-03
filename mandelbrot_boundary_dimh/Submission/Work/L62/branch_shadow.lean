import Mathlib
import Submission.Work.L62.local_branch_disc

/-!
# L62 — shadowing of an inverse branch under a `C¹`-small perturbation (quantitative IFT)

Let `F, F' : ℂ → ℂ` be holomorphic on an open set `U`, and let `ψ` be an inverse branch of `F`
over the disc `ball c r`: `F (ψ z) = z`, with `‖deriv ψ‖ ≤ L`.  If `F'` is `δ`-close to `F` in
sup-norm and `δ'`-close to `F` in the derivative on `U`, with `δ' * L < 1`, then over a slightly
smaller disc `ball c ρ` (where `δ < (1 - δ' L) (r - ρ)`) there is an inverse branch `ψ'` of `F'`,
differentiable, injective, taking values in `U`, and `O(δ)`-close to `ψ`.

The proof is a near-identity / contraction argument.  Put `S := F' ∘ ψ` on `Ω := ball c r`.  Then

* `‖S w - w‖ = ‖F' (ψ w) - F (ψ w)‖ ≤ δ` (using `F (ψ w) = w`), and
* `deriv S w - 1 = (deriv F' (ψ w) - deriv F (ψ w)) · deriv ψ w` (chain rule together with
  `deriv F (ψ w) · deriv ψ w = 1`), so `‖deriv S w - 1‖ ≤ δ' L =: k < 1`.

By the mean value inequality on the convex disc `Ω`, `S` is injective on `Ω` and the map
`R w := z - (S w - w)` is a `k`-contraction of the closed disc `closedBall z R₀` (with
`δ < R₀ < r - ρ`) into itself; its fixed point `w` satisfies `S w = z`, i.e. `F' (ψ w) = z`.
Setting `ψ' z := ψ (w z)` gives the branch: `F' ∘ ψ' = id` is free, injectivity follows from it,
valued in `U` since `ψ` is, and `‖ψ' z - ψ z‖ ≤ L ‖w - z‖ ≤ L δ` because `w - z = w - S w`.

Differentiability of `ψ'` is obtained from the local inverse function theorem for `S`
(`Work.L62.local_branch_disc`): near `z₀`, `S` has a local differentiable inverse `φ`, and the
injectivity of `S` on `Ω` forces `φ = w` (hence `ψ' = ψ ∘ φ`) on a neighbourhood of `z₀`.
-/

set_option linter.style.haveILetI false

namespace Work.L62

open Complex Metric Set Filter
open scoped Topology

theorem branch_shadow {F F' : ℂ → ℂ} {c : ℂ} {r L : ℝ} {ψ : ℂ → ℂ} {U : Set ℂ} {δ δ' : ℝ}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hF' : DifferentiableOn ℂ F' U)
    (hr : 0 < r) (hL : 0 ≤ L) (hψd : DifferentiableOn ℂ ψ (Metric.ball c r))
    (hψL : ∀ z ∈ Metric.ball c r, ‖deriv ψ z‖ ≤ L)
    (hψmem : Set.MapsTo ψ (Metric.ball c r) U)
    (hψinv : ∀ z ∈ Metric.ball c r, F (ψ z) = z)
    (hδ : 0 < δ) (hδ' : 0 < δ') (hδL : δ' * L < 1)
    (hclose : ∀ z ∈ U, ‖F' z - F z‖ ≤ δ)
    (hcloseD : ∀ z ∈ U, ‖deriv F' z - deriv F z‖ ≤ δ') :
    ∀ ρ : ℝ, 0 < ρ → ρ < r → δ < (1 - δ' * L) * (r - ρ) →
      ∃ (ψ' : ℂ → ℂ) (C : ℝ), 0 < C ∧ DifferentiableOn ℂ ψ' (Metric.ball c ρ) ∧
        (∀ z ∈ Metric.ball c ρ, F' (ψ' z) = z) ∧
        Set.MapsTo ψ' (Metric.ball c ρ) U ∧ Set.InjOn ψ' (Metric.ball c ρ) ∧
        (∀ z ∈ Metric.ball c ρ, ‖ψ' z - ψ z‖ ≤ C * δ) := by
  intro ρ hρ hρr hρδ
  set k : ℝ := δ' * L with hkdef
  have hk0 : 0 ≤ k := by rw [hkdef]; exact mul_nonneg hδ'.le hL
  have hk1 : k < 1 := by rw [hkdef]; exact hδL
  have hΩo : IsOpen (Metric.ball c r) := Metric.isOpen_ball
  have hΩc : Convex ℝ (Metric.ball c r) := convex_ball c r
  -- ### 1. ψ is `L`-Lipschitz on the ball (mean value inequality, the ball is convex)
  have hψlip : ∀ a ∈ Metric.ball c r, ∀ b ∈ Metric.ball c r,
      ‖ψ a - ψ b‖ ≤ L * ‖a - b‖ := by
    intro a ha b hb
    have h := Convex.norm_image_sub_le_of_norm_derivWithin_le (𝕜 := ℂ) (G := ℂ)
      (f := ψ) (s := Metric.ball c r) (C := L) hψd (fun x hx => by
        rw [derivWithin_of_isOpen hΩo hx]; exact hψL x hx) hΩc ha hb
    simpa [norm_sub_rev] using h
  -- ### 2. chain-rule identity `deriv F (ψ w) * deriv ψ w = 1`
  have hchain : ∀ w ∈ Metric.ball c r, deriv F (ψ w) * deriv ψ w = 1 := by
    intro w hw
    have hψat : DifferentiableAt ℂ ψ w := hψd.differentiableAt (hΩo.mem_nhds hw)
    have hFat : DifferentiableAt ℂ F (ψ w) := hF.differentiableAt (hU.mem_nhds (hψmem hw))
    have h1 : HasDerivAt (F ∘ ψ) 1 w :=
      (hasDerivAt_id w).congr_of_eventuallyEq
        (by filter_upwards [hΩo.mem_nhds hw] with x hx; exact hψinv x hx)
    have h2 : HasDerivAt (F ∘ ψ) (deriv F (ψ w) * deriv ψ w) w :=
      hFat.hasDerivAt.comp w hψat.hasDerivAt
    exact (h1.unique h2).symm
  -- ### 3. `S := F' ∘ ψ`: differentiable, `deriv S w - 1` small
  have hSdiff : DifferentiableOn ℂ (fun w => F' (ψ w)) (Metric.ball c r) :=
    hF'.comp hψd hψmem
  have hSderiv : ∀ w ∈ Metric.ball c r,
      deriv (fun w => F' (ψ w)) w = deriv F' (ψ w) * deriv ψ w := by
    intro w hw
    have hψat : DifferentiableAt ℂ ψ w := hψd.differentiableAt (hΩo.mem_nhds hw)
    have hF'at : DifferentiableAt ℂ F' (ψ w) := hF'.differentiableAt (hU.mem_nhds (hψmem hw))
    exact deriv_comp w hF'at hψat
  have hSbd : ∀ w ∈ Metric.ball c r, ‖deriv (fun w => F' (ψ w)) w - 1‖ ≤ k := by
    intro w hw
    rw [hSderiv w hw]
    have heq : deriv F' (ψ w) * deriv ψ w - 1
        = (deriv F' (ψ w) - deriv F (ψ w)) * deriv ψ w := by
      rw [← hchain w hw]; ring
    rw [heq, hkdef, norm_mul]
    exact mul_le_mul (hcloseD (ψ w) (hψmem hw)) (hψL w hw) (norm_nonneg _) hδ'.le
  -- ### 4. pointwise bound `‖S w - w‖ ≤ δ`
  have hSval : ∀ w ∈ Metric.ball c r, ‖F' (ψ w) - w‖ ≤ δ := by
    intro w hw
    have := hclose (ψ w) (hψmem hw)
    rwa [hψinv w hw] at this
  -- ### 5. `G := S - id`: derivative bound and Lipschitz bound
  have hGdiff : DifferentiableOn ℂ (fun w => F' (ψ w) - w) (Metric.ball c r) :=
    hSdiff.sub differentiableOn_id
  have hGderiv : ∀ w ∈ Metric.ball c r,
      deriv (fun w => F' (ψ w) - w) w = (deriv F' (ψ w) - deriv F (ψ w)) * deriv ψ w := by
    intro w hw
    have hψat : DifferentiableAt ℂ ψ w := hψd.differentiableAt (hΩo.mem_nhds hw)
    have hF'at : DifferentiableAt ℂ F' (ψ w) := hF'.differentiableAt (hU.mem_nhds (hψmem hw))
    have h1 : HasDerivAt (fun x => F' (ψ x) - x)
        (deriv F' (ψ w) * deriv ψ w - 1) w :=
      (hF'at.hasDerivAt.comp w hψat.hasDerivAt).sub (hasDerivAt_id w)
    have heq : deriv F' (ψ w) * deriv ψ w - 1
        = (deriv F' (ψ w) - deriv F (ψ w)) * deriv ψ w := by
      rw [← hchain w hw]; ring
    rw [h1.deriv, heq]
  have hGlip : ∀ a ∈ Metric.ball c r, ∀ b ∈ Metric.ball c r,
      ‖(F' (ψ a) - a) - (F' (ψ b) - b)‖ ≤ k * ‖a - b‖ := by
    intro a ha b hb
    have h := Convex.norm_image_sub_le_of_norm_derivWithin_le (𝕜 := ℂ) (G := ℂ)
      (f := fun w => F' (ψ w) - w) (s := Metric.ball c r) (C := k) hGdiff (fun x hx => by
        rw [derivWithin_of_isOpen hΩo hx, hGderiv x hx, hkdef, norm_mul]
        exact mul_le_mul (hcloseD (ψ x) (hψmem hx)) (hψL x hx) (norm_nonneg _) hδ'.le)
      hΩc ha hb
    simpa [norm_sub_rev] using h
  -- ### 6. `S` is injective on the ball
  have hSinj : Set.InjOn (fun w => F' (ψ w)) (Metric.ball c r) := by
    intro a ha b hb hab
    have hab' : F' (ψ a) = F' (ψ b) := hab
    have h := hGlip a ha b hb
    have heq : (F' (ψ a) - a) - (F' (ψ b) - b) = -(a - b) := by rw [hab']; ring
    rw [heq, norm_neg] at h
    have hnorm : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b), hk0, hk1]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  -- ### 7. every point of the smaller disc is a value of `S`
  have hpre : ∀ z, ∃ w, z ∈ Metric.ball c ρ →
      (w ∈ Metric.ball c r ∧ F' (ψ w) = z) := by
    intro z
    by_cases hz : z ∈ Metric.ball c ρ
    · have hzc : ‖z - c‖ < ρ := by rwa [Metric.mem_ball, dist_eq_norm] at hz
      have hrρ : 0 < r - ρ := by linarith
      have hδrρ : δ < r - ρ := by
        calc δ < (1 - k) * (r - ρ) := by rw [hkdef]; exact hρδ
          _ ≤ 1 * (r - ρ) := mul_le_mul_of_nonneg_right (by linarith) hrρ.le
          _ = r - ρ := one_mul _
      obtain ⟨R₀, hR0δ, hR0r⟩ := exists_between hδrρ
      have hsr : Metric.closedBall z R₀ ⊆ Metric.ball c r := by
        intro w hw
        rw [Metric.mem_closedBall, dist_eq_norm] at hw
        rw [Metric.mem_ball, dist_eq_norm]
        calc ‖w - c‖ = ‖(w - z) + (z - c)‖ := by rw [show w - c = (w - z) + (z - c) from by ring]
          _ ≤ ‖w - z‖ + ‖z - c‖ := norm_add_le _ _
          _ < r := by linarith
      let R : ℂ → ℂ := fun w => z - (F' (ψ w) - w)
      have hRmem : Set.MapsTo R (Metric.closedBall z R₀) (Metric.closedBall z R₀) := by
        intro w hw
        rw [Metric.mem_closedBall, dist_eq_norm]
        have h1 : R w - z = -(F' (ψ w) - w) := by simp only [R]; ring
        rw [h1, norm_neg]
        have := hSval w (hsr hw)
        linarith
      have hRlip : ∀ a ∈ Metric.closedBall z R₀, ∀ b ∈ Metric.closedBall z R₀,
          dist (R a) (R b) ≤ k * dist a b := by
        intro a ha b hb
        rw [dist_eq_norm, dist_eq_norm]
        have h1 : R a - R b = -((F' (ψ a) - a) - (F' (ψ b) - b)) := by simp only [R]; ring
        rw [h1, norm_neg]
        exact hGlip a (hsr ha) b (hsr hb)
      let Rs : Metric.closedBall z R₀ → Metric.closedBall z R₀ := fun x => ⟨R x, hRmem x.2⟩
      have hRslip : LipschitzWith ⟨k, hk0⟩ Rs := by
        apply LipschitzWith.of_dist_le_mul
        intro x y
        have h1 : dist (Rs x) (Rs y) = dist (R x) (R y) := Subtype.dist_eq _ _
        rw [h1]
        calc dist (R (↑x : ℂ)) (R (↑y : ℂ)) ≤ k * dist (↑x : ℂ) (↑y : ℂ) :=
              hRlip x x.2 y y.2
          _ = (⟨k, hk0⟩ : NNReal) * dist x y := by
                rw [show ((⟨k, hk0⟩ : NNReal) : ℝ) = k from rfl, Subtype.dist_eq]
      have hRsc : ContractingWith ⟨k, hk0⟩ Rs := by
        refine ⟨?_, hRslip⟩
        exact_mod_cast hk1
      haveI : Nonempty (Metric.closedBall z R₀) :=
        ⟨⟨z, Metric.mem_closedBall_self (by linarith)⟩⟩
      let fp := ContractingWith.fixedPoint Rs hRsc
      have hfp : Rs fp = fp := ContractingWith.fixedPoint_isFixedPt hRsc
      have hv : R fp.1 = fp.1 := by
        have := congrArg Subtype.val hfp
        simpa [Rs] using this
      have hval : F' (ψ fp.1) = z := by
        have h3 := eq_add_of_sub_eq hv
        rw [show fp.1 + (F' (ψ fp.1) - fp.1) = F' (ψ fp.1) from by ring] at h3
        exact h3.symm
      exact ⟨fp.1, fun _ => ⟨hsr fp.2, hval⟩⟩
    · exact ⟨z, fun hz' => absurd hz' hz⟩
  choose w hwmem hweq using hpre
  -- ### 8. assembly
  refine ⟨fun z => ψ (w z), L + 1, by linarith, ?_, ?_, ?_, ?_, ?_⟩
  · -- differentiability, from the local inverse function theorem at each point
    intro z₀ hz₀
    have hz₀r : z₀ ∈ Metric.ball c r := Metric.ball_subset_ball hρr.le hz₀
    have hw0 : w z₀ ∈ Metric.ball c r := hwmem z₀ hz₀
    have hSw0 : F' (ψ (w z₀)) = z₀ := hweq z₀ hz₀
    have hSana : AnalyticAt ℂ (fun u => F' (ψ u)) (w z₀) :=
      hSdiff.analyticAt (hΩo.mem_nhds hw0)
    have hdS : deriv (fun u => F' (ψ u)) (w z₀) ≠ 0 := by
      intro h0
      have hb := hSbd (w z₀) hw0
      rw [h0] at hb
      simp only [zero_sub, norm_neg, norm_one] at hb
      linarith [hk1]
    obtain ⟨r_loc, hr_loc, φ, hφdiff, _hφeq, hφright, hφmem, _hφinj⟩ :=
      local_branch_disc hSana hdS hΩo hw0
    have hz₀loc : z₀ ∈ Metric.ball (F' (ψ (w z₀))) r_loc := by
      rw [hSw0]; exact Metric.mem_ball_self hr_loc
    have hev : (fun z => ψ (w z)) =ᶠ[𝓝 z₀] (fun z => ψ (φ z)) := by
      filter_upwards [(Metric.isOpen_ball).mem_nhds hz₀,
        (Metric.isOpen_ball).mem_nhds hz₀loc] with z hzρ hzloc
      have hφzm : φ z ∈ Metric.ball c r := hφmem hzloc
      have hwzm : w z ∈ Metric.ball c r := hwmem z hzρ
      have hEq : φ z = w z := hSinj hφzm hwzm (by
        show F' (ψ (φ z)) = F' (ψ (w z))
        rw [hφright z hzloc, hweq z hzρ])
      rw [hEq]
    have hφat : DifferentiableAt ℂ φ z₀ :=
      hφdiff.differentiableAt ((Metric.isOpen_ball).mem_nhds hz₀loc)
    have hψat : DifferentiableAt ℂ ψ (φ z₀) :=
      hψd.differentiableAt ((Metric.isOpen_ball).mem_nhds (hφmem hz₀loc))
    exact (hψat.comp z₀ hφat).congr_of_eventuallyEq hev |>.differentiableWithinAt
  · intro z hz
    exact hweq z hz
  · intro z hz
    exact hψmem (hwmem z hz)
  · intro z₁ hz₁ z₂ hz₂ heq
    have heq' : ψ (w z₁) = ψ (w z₂) := heq
    calc z₁ = F' (ψ (w z₁)) := (hweq z₁ hz₁).symm
      _ = F' (ψ (w z₂)) := by rw [heq']
      _ = z₂ := hweq z₂ hz₂
  · intro z hz
    have hzr : z ∈ Metric.ball c r := Metric.ball_subset_ball hρr.le hz
    have hwz : w z ∈ Metric.ball c r := hwmem z hz
    have h1 : ‖w z - z‖ ≤ δ := by
      have h2 : w z - z = -(F' (ψ (w z)) - w z) := by rw [hweq z hz]; ring
      rw [h2, norm_neg]
      exact hSval (w z) hwz
    calc ‖ψ (w z) - ψ z‖ ≤ L * ‖w z - z‖ := hψlip (w z) hwz z hzr
      _ ≤ L * δ := mul_le_mul_of_nonneg_left h1 hL
      _ ≤ (L + 1) * δ := by nlinarith [hL, hδ.le]

end Work.L62
