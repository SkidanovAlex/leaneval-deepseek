import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.l62c_end
import Submission.Work.L62.branch_shadow
import Submission.Work.L62.branch_shadow_base
import Submission.Work.L62.local_branch_disc
import Submission.Work.L62.chain_branches
import Submission.Work.L62.chain_geometry
import Submission.Work.L62.l62c_basic

namespace Work.L62

open MandelDim Set Metric Filter Topology
open scoped Topology

noncomputable section

set_option maxHeartbeats 4000000

/-!
# `Work.L62.head_stability` (Shishikura, Lemma 6.2, the "stability of the head" step)

Given an exact chain `z 0 = ζ, z 1, …, z j₀` of the lifted horn map (`d.E (z j) - β₀ = z (j-1)`,
`deriv d.E (z j) ≠ 0`) whose `2r`-collar lies in `d.DE`, the perturbed inverse branches of
`ĥ = R - β` (`R` holomorphic on `DR ⊇ collar`, `C⁰`-close to `d.E` there) give inverse images
`W (j+1) ⊆ ball (z (j+1)) r` of `W j` for every `ρ ≤ ρ₁`, `‖β - β₀‖ < ε`, with two-sided
derivative bounds on the iterates.  The proof constructs the discs step by step; the generic
analytic lemmas it uses (`branch_stability` = quantitative inverse branch, `deriv_iterate_prod` =
product formula for iterates, `cauchy_deriv_bound` = Cauchy estimate on a closed disc,
`deriv_control_radius` = disc on which `deriv` stays within `1/8` of its value) are proved first.

## Helper lemmas
-/

private theorem deriv_iterate_prod {f : ℂ → ℂ} {z : ℂ} {n : ℕ}
    (h : ∀ i < n, DifferentiableAt ℂ f ((f^[i]) z)) :
    deriv (f^[n]) z = ∏ i ∈ Finset.range n, deriv f ((f^[i]) z) := by
  have hdiff : ∀ k : ℕ, (∀ i < k, DifferentiableAt ℂ f ((f^[i]) z)) →
      DifferentiableAt ℂ (f^[k]) z := by
    intro k
    induction k with
    | zero => intro _; simpa using differentiableAt_id
    | succ k ih =>
      intro hk
      show DifferentiableAt ℂ (f^[Nat.succ k]) z
      rw [Function.iterate_succ']
      exact (hk k (Nat.lt_succ_self k)).comp z (ih (fun i hi => hk i (by omega)))
  induction n with
  | zero => simp
  | succ n ih =>
    have hfn : DifferentiableAt ℂ f ((f^[n]) z) := h n (Nat.lt_succ_self n)
    have hgn : DifferentiableAt ℂ (f^[n]) z := hdiff n (fun i hi => h i (by omega))
    show deriv (f^[Nat.succ n]) z = ∏ i ∈ Finset.range (n + 1), deriv f ((f^[i]) z)
    rw [Function.iterate_succ', deriv_comp z hfn hgn,
      ih (fun i hi => h i (by omega)), Finset.prod_range_succ, mul_comm]

private theorem cauchy_deriv_bound {f : ℂ → ℂ} {U : Set ℂ} {c : ℂ} {ρ δ : ℝ}
    (hρ : 0 < ρ) (hU : IsOpen U) (hf : DifferentiableOn ℂ f U)
    (hsub : Metric.closedBall c (2 * ρ) ⊆ U)
    (hbd : ∀ w ∈ Metric.closedBall c (2 * ρ), ‖f w‖ ≤ δ) :
    ∀ w ∈ Metric.closedBall c ρ, ‖deriv f w‖ ≤ δ / ρ := by
  intro w hw
  have hwρ : dist w c ≤ ρ := Metric.mem_closedBall.mp hw
  have hsub' : Metric.closedBall w ρ ⊆ U := by
    intro z hz
    refine hsub ?_
    rw [Metric.mem_closedBall] at hz ⊢
    calc dist z c ≤ dist z w + dist w c := dist_triangle _ _ _
      _ ≤ ρ + ρ := add_le_add hz hwρ
      _ = 2 * ρ := by ring
  have hdc : DiffContOnCl ℂ f (Metric.ball w ρ) := hf.diffContOnCl_ball hsub'
  have hsph : ∀ z ∈ Metric.sphere w ρ, ‖f z‖ ≤ δ := by
    intro z hz
    refine hbd z ?_
    rw [Metric.mem_closedBall]
    have h1 := Metric.mem_sphere.mp hz
    calc dist z c ≤ dist z w + dist w c := dist_triangle _ _ _
      _ = ρ + dist w c := by rw [h1]
      _ ≤ 2 * ρ := by linarith
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ hdc hsph

private theorem deriv_control_radius {E : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hE : DifferentiableOn ℂ E U) {x : ℂ} (hx : x ∈ U) (hx' : deriv E x ≠ 0)
    {r : ℝ} (hr : 0 < r) :
    ∃ R : ℝ, 0 < R ∧ R ≤ r ∧ Metric.ball x R ⊆ U ∧
      ∀ w ∈ Metric.ball x R, ‖deriv E w - deriv E x‖ ≤ ‖deriv E x‖ / 8 := by
  have hana : AnalyticAt ℂ E x := hE.analyticAt (hU.mem_nhds hx)
  have hcont : ContinuousAt (deriv E) x := (AnalyticAt.deriv hana).continuousAt
  have hε : 0 < ‖deriv E x‖ / 8 := by positivity
  have hnhds : (deriv E) ⁻¹' Metric.ball (deriv E x) (‖deriv E x‖ / 8) ∈ 𝓝 x :=
    hcont (Metric.ball_mem_nhds _ hε)
  obtain ⟨R₁, hR₁, hR₁sub⟩ := Metric.mem_nhds_iff.mp hnhds
  obtain ⟨R₂, hR₂, hR₂sub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  refine ⟨min R₁ (min R₂ r), lt_min hR₁ (lt_min hR₂ hr),
    le_trans (min_le_right _ _) (min_le_right _ _), ?_, ?_⟩
  · exact (Metric.ball_subset_ball (le_trans (min_le_right _ _) (min_le_left _ _))).trans hR₂sub
  · intro w hw
    have h1 : deriv E w ∈ Metric.ball (deriv E x) (‖deriv E x‖ / 8) :=
      hR₁sub (Metric.ball_subset_ball (min_le_left _ _) hw)
    rw [Metric.mem_ball, dist_eq_norm] at h1
    exact h1.le


private theorem branch_stability {G : ℂ → ℂ} {a : ℂ} {R : ℝ} {A : ℂ} {k : ℝ}
    (hR : 0 < R) (hA : A ≠ 0) (hk0 : 0 ≤ k) (hk1 : k < 1 / 2)
    (hGd : DifferentiableOn ℂ G (Metric.ball a R))
    (huniv : ∀ w ∈ Metric.ball a R, ‖deriv G w - A‖ ≤ k * ‖A‖) :
    ∃ χ : ℂ → ℂ,
      DifferentiableOn ℂ χ (Metric.ball (G a) (‖A‖ * (1 - k) * R / 2)) ∧
      χ (G a) = a ∧
      (∀ z ∈ Metric.ball (G a) (‖A‖ * (1 - k) * R / 2), G (χ z) = z) ∧
      Set.InjOn χ (Metric.ball (G a) (‖A‖ * (1 - k) * R / 2)) ∧
      (∀ z ∈ Metric.ball (G a) (‖A‖ * (1 - k) * R / 2), ‖χ z - a‖ < R / 2) ∧
      (∀ z ∈ Metric.ball (G a) (‖A‖ * (1 - k) * R / 2), ‖deriv χ z‖ ≤ 2 / ‖A‖) ∧
      (∀ z ∈ Metric.ball (G a) (‖A‖ * (1 - k) * R / 2), ∀ w ∈ Metric.closedBall a (R / 2),
        G w = z → w = χ z) := by
  set ρ : ℝ := ‖A‖ * (1 - k) * R / 2 with hρ
  have h1k : 0 < 1 - k := by linarith
  have hR2 : 0 < R / 2 := by linarith
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  have hAne : A ≠ 0 := hA
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA
  set Φ : ℂ → ℂ := fun u => (G (a + u) - G a) / A with hΦ
  have hmem_iff : ∀ u : ℂ, a + u ∈ Metric.ball a R ↔ u ∈ Metric.ball 0 R := by
    intro u
    have h1 : a + u - a = u := by ring
    simp only [Metric.mem_ball, dist_eq_norm, h1, sub_zero]
  have hΦ0 : Φ 0 = 0 := by
    show (G (a + 0) - G a) / A = 0
    rw [add_zero, sub_self, zero_div]
  have hΦd : DifferentiableOn ℂ Φ (Metric.ball (0:ℂ) R) := by
    intro u hu
    have hmem : Metric.ball a R ∈ 𝓝 (a + u) := (Metric.isOpen_ball).mem_nhds ((hmem_iff u).mpr hu)
    have h1 : DifferentiableAt ℂ (fun v : ℂ => G (a + v)) u :=
      (hGd.differentiableAt hmem).comp u ((differentiableAt_const a).add differentiableAt_id)
    exact (h1.sub_const (G a)).div_const A |>.differentiableWithinAt
  have hΦderiv : ∀ u ∈ Metric.ball (0:ℂ) R, deriv Φ u = deriv G (a + u) / A := by
    intro u hu
    have hmem : Metric.ball a R ∈ 𝓝 (a + u) := (Metric.isOpen_ball).mem_nhds ((hmem_iff u).mpr hu)
    have hshiftd : deriv (fun v : ℂ => a + v) u = 1 := by
      rw [show (fun v : ℂ => a + v) = (fun v : ℂ => v + a) from by funext v; ring]
      rw [deriv_add_const]
      simpa using deriv_id u
    have hcomp : deriv (fun v : ℂ => G (a + v)) u = deriv G (a + u) := by
      simpa [Function.comp_def, hshiftd] using
        deriv_comp u (hGd.differentiableAt hmem) ((differentiableAt_const a).add differentiableAt_id)
    show deriv (fun u => (G (a + u) - G a) / A) u = deriv G (a + u) / A
    rw [deriv_div_const, deriv_sub_const, hcomp]
  have hΦuniv : ∀ u ∈ Metric.ball (0:ℂ) R, ‖deriv Φ u - 1‖ ≤ k := by
    intro u hu
    rw [hΦderiv u hu]
    have h1 : deriv G (a + u) / A - 1 = (deriv G (a + u) - A) / A := by
      rw [show (1 : ℂ) = A / A from (div_self hAne).symm, ← sub_div]
    rw [h1, norm_div, div_le_iff₀ hApos]
    exact huniv (a + u) ((hmem_iff u).mpr hu)
  have hhalf : Metric.closedBall (0:ℂ) (R / 2) ⊆ Metric.ball (0:ℂ) R := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith
  have hΨlip : ∀ u ∈ Metric.closedBall (0:ℂ) (R / 2), ∀ u' ∈ Metric.closedBall (0:ℂ) (R / 2),
      ‖(Φ u - u) - (Φ u' - u')‖ ≤ k * ‖u - u'‖ := by
    intro u hu u' hu'
    have hconv : Convex ℝ (Metric.ball (0:ℂ) R) := convex_ball _ _
    have hd : DifferentiableOn ℂ (fun v => Φ v - v) (Metric.ball (0:ℂ) R) :=
      hΦd.sub differentiableOn_id
    refine Convex.norm_image_sub_le_of_norm_derivWithin_le hd ?_ hconv (hhalf hu') (hhalf hu)
    intro v hv
    rw [derivWithin_of_isOpen Metric.isOpen_ball hv]
    have hdv : deriv (fun v : ℂ => Φ v - v) v = deriv Φ v - 1 := by
      have h1 : HasDerivAt Φ (deriv Φ v) v :=
        ((hΦd v hv).differentiableAt ((Metric.isOpen_ball).mem_nhds hv)).hasDerivAt
      exact (h1.sub (hasDerivAt_id v)).deriv
    rw [hdv]
    exact hΦuniv v hv
  -- existence and uniqueness of the preimage
  have hex : ∀ y : ℂ, ‖y‖ < (1 - k) * (R / 2) →
      ∃ u : ℂ, u ∈ Metric.closedBall (0:ℂ) (R / 2) ∧ ‖u‖ < R / 2 ∧ Φ u = y ∧
        ∀ u' ∈ Metric.closedBall (0:ℂ) (R / 2), Φ u' = y → u' = u := by
    intro y hy
    set T : ℂ → ℂ := fun u => y - (Φ u - u) with hT
    have hlipT : ∀ u ∈ Metric.closedBall (0:ℂ) (R / 2), ∀ u' ∈ Metric.closedBall (0:ℂ) (R / 2),
        dist (T u) (T u') ≤ k * dist u u' := by
      intro u hu u' hu'
      rw [dist_eq_norm, dist_eq_norm]
      have h1 : T u - T u' = -((Φ u - u) - (Φ u' - u')) := by
        simp only [hT]; ring
      rw [h1, norm_neg]
      exact hΨlip u hu u' hu'
    have hTmem : Set.MapsTo T (Metric.closedBall (0:ℂ) (R / 2)) (Metric.closedBall (0:ℂ) (R / 2)) := by
      intro u hu
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      have h1 : T u = y - (Φ u - u) := rfl
      rw [h1]
      have h2 := hΨlip u hu 0 (Metric.mem_closedBall_self hR2.le)
      have h3 : Φ 0 - 0 = 0 := by rw [hΦ0]; ring
      rw [h3, sub_zero] at h2
      have h4 : ‖y - (Φ u - u)‖ ≤ ‖y‖ + ‖Φ u - u‖ := by
        calc ‖y - (Φ u - u)‖ = ‖y + (-(Φ u - u))‖ := by ring_nf
          _ ≤ ‖y‖ + ‖-(Φ u - u)‖ := norm_add_le _ _
          _ = ‖y‖ + ‖Φ u - u‖ := by rw [norm_neg]
      have huu : ‖u‖ ≤ R / 2 := by
        have := Metric.mem_closedBall.mp hu
        rwa [dist_eq_norm, sub_zero] at this
      rw [sub_zero] at h2
      have hsum : (1 - k) * (R / 2) + k * (R / 2) = R / 2 := by ring
      have hkk : k * ‖u‖ ≤ k * (R / 2) := by
        exact mul_le_mul_of_nonneg_left huu hk0
      linarith [h4, h2, hkk, hy, hsum]
    let Ts : Metric.closedBall (0:ℂ) (R / 2) → Metric.closedBall (0:ℂ) (R / 2) :=
      fun x => ⟨T x, hTmem x.2⟩
    have hTslip : LipschitzWith ⟨k, hk0⟩ Ts := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      have h1 : dist (Ts x) (Ts y) = dist (T (x : ℂ)) (T (y : ℂ)) := Subtype.dist_eq _ _
      rw [h1]
      calc dist (T (x : ℂ)) (T (y : ℂ)) ≤ k * dist (x : ℂ) (y : ℂ) := hlipT x x.2 y y.2
        _ = (⟨k, hk0⟩ : NNReal) * dist x y := by
              rw [show ((⟨k, hk0⟩ : NNReal) : ℝ) = k from rfl, Subtype.dist_eq]
    have hk1' : (⟨k, hk0⟩ : NNReal) < 1 := by
      exact_mod_cast (show k < 1 by linarith)
    have hTsc : ContractingWith ⟨k, hk0⟩ Ts := ⟨hk1', hTslip⟩
    haveI : Nonempty (Metric.closedBall (0:ℂ) (R / 2)) :=
      ⟨⟨0, Metric.mem_closedBall_self hR2.le⟩⟩
    haveI : IsClosed (Metric.closedBall (0:ℂ) (R / 2)) := Metric.isClosed_closedBall
    haveI : CompleteSpace (Metric.closedBall (0:ℂ) (R / 2)) := IsClosed.completeSpace_coe
    let fp := ContractingWith.fixedPoint Ts hTsc
    have hfpx : Ts fp = fp := ContractingWith.fixedPoint_isFixedPt hTsc
    have hfpT : T (fp : ℂ) = fp := by
      have := congrArg Subtype.val hfpx
      simpa [Ts] using this
    have hfpT' : y - (Φ (fp : ℂ) - (fp : ℂ)) = (fp : ℂ) := by
      simpa only [hT] using hfpT
    have hΦfp : Φ (fp : ℂ) = y := by
      have h3 : y - (Φ (fp : ℂ) - (fp : ℂ)) = (fp : ℂ) := hfpT'
      calc Φ (fp : ℂ) = (fp : ℂ) + (Φ (fp : ℂ) - (fp : ℂ)) := by ring
        _ = (y - (Φ (fp : ℂ) - (fp : ℂ))) + (Φ (fp : ℂ) - (fp : ℂ)) := by rw [h3]
        _ = y := by ring
    have hfpbd : ‖(fp : ℂ)‖ < R / 2 := by
      have h2 := hΨlip (fp : ℂ) fp.2 0 (Metric.mem_closedBall_self hR2.le)
      rw [hΦ0, sub_zero, sub_zero] at h2
      have h4 : (fp : ℂ) = y - (Φ (fp : ℂ) - (fp : ℂ)) := hfpT'.symm
      have h2' : ‖Φ (fp : ℂ) - (fp : ℂ)‖ ≤ k * ‖(fp : ℂ)‖ := by simpa using h2
      have h5 : ‖(fp : ℂ)‖ ≤ ‖y‖ + k * ‖(fp : ℂ)‖ := by
        calc ‖(fp : ℂ)‖ = ‖y - (Φ (fp : ℂ) - (fp : ℂ))‖ := congrArg norm h4
          _ ≤ ‖y‖ + ‖Φ (fp : ℂ) - (fp : ℂ)‖ := by
              calc ‖y - (Φ (fp : ℂ) - (fp : ℂ))‖ = ‖y + (-(Φ (fp : ℂ) - (fp : ℂ)))‖ := by ring_nf
                _ ≤ ‖y‖ + ‖-(Φ (fp : ℂ) - (fp : ℂ))‖ := norm_add_le _ _
                _ = ‖y‖ + ‖Φ (fp : ℂ) - (fp : ℂ)‖ := by rw [norm_neg]
          _ ≤ ‖y‖ + k * ‖(fp : ℂ)‖ := by linarith [h2']
      have h9 : (1 - k) * ‖(fp : ℂ)‖ ≤ ‖y‖ := by linarith
      exact lt_of_mul_lt_mul_left (lt_of_le_of_lt h9 hy) h1k.le
    refine ⟨(fp : ℂ), fp.2, hfpbd, hΦfp, ?_⟩
    intro u' hu' hΦu'
    have hTu' : T u' = u' := by
      show y - (Φ u' - u') = u'
      rw [hΦu']; ring
    have hd : dist u' (fp : ℂ) ≤ k * dist u' (fp : ℂ) := by
      have h := hlipT u' hu' (fp : ℂ) fp.2
      rw [hTu', hfpT] at h
      exact h
    have hzero : dist u' (fp : ℂ) = 0 := by
      nlinarith [hd, dist_nonneg (x := u') (y := (fp:ℂ)), hk0, hk1]
    exact dist_eq_zero.mp hzero
  -- the branch
  let u : ℂ → ℂ := fun z =>
    if h : ‖(z - G a) / A‖ < (1 - k) * (R / 2) then Classical.choose (hex ((z - G a) / A) h) else 0
  let χ : ℂ → ℂ := fun z => a + u z
  have hsmall : ∀ z ∈ Metric.ball (G a) ρ, ‖(z - G a) / A‖ < (1 - k) * (R / 2) := by
    intro z hz
    have hz1 : ‖z - G a‖ < ρ := by
      have := Metric.mem_ball.mp hz
      first | exact this | (rwa [dist_eq_norm] at this) | simpa [dist_eq_norm] using this
    rw [norm_div, div_lt_iff₀ hApos]
    rw [hρ] at hz1
    nlinarith [hz1]
  have hu_spec : ∀ z (h : ‖(z - G a) / A‖ < (1 - k) * (R / 2)),
      u z ∈ Metric.closedBall (0:ℂ) (R / 2) ∧ ‖u z‖ < R / 2 ∧ Φ (u z) = (z - G a) / A ∧
        ∀ u' ∈ Metric.closedBall (0:ℂ) (R / 2), Φ u' = (z - G a) / A → u' = u z := by
    intro z h
    have hred : u z = Classical.choose (hex ((z - G a) / A) h) := by
      simp only [u]
      rw [dif_pos h]
    rw [hred]
    exact (Classical.choose_spec (hex ((z - G a) / A) h))
  have hχG : ∀ z ∈ Metric.ball (G a) ρ, G (χ z) = z := by
    intro z hz
    obtain ⟨-, -, h2, -⟩ := hu_spec z (hsmall z hz)
    have h5 : G (a + u z) - G a = z - G a := by
      have h6 := congrArg (fun t : ℂ => t * A) h2
      rwa [div_mul_cancel₀ _ hAne, div_mul_cancel₀ _ hAne] at h6
    have h7 : G (a + u z) = z := by
      have := congrArg (fun t : ℂ => t + G a) h5
      simpa using this
    show G (a + u z) = z
    exact h7
  have hχa : χ (G a) = a := by
    have h0 : ‖(G a - G a) / A‖ < (1 - k) * (R / 2) := by
      rw [sub_self, zero_div, norm_zero]
      exact mul_pos h1k hR2
    obtain ⟨-, -, h2, h3⟩ := hu_spec (G a) h0
    have h2' : Φ (u (G a)) = 0 := by
      rw [h2]
      rw [sub_self, zero_div]
    have h4 : (0 : ℂ) = u (G a) :=
      h3 0 (Metric.mem_closedBall_self hR2.le) (by rw [hΦ0, sub_self, zero_div])
    show a + u (G a) = a
    rw [← h4]; ring
  have hχclose : ∀ z ∈ Metric.ball (G a) ρ, ‖χ z - a‖ < R / 2 := by
    intro z hz
    obtain ⟨-, h2, -⟩ := hu_spec z (hsmall z hz)
    show ‖a + u z - a‖ < R / 2
    rwa [add_sub_cancel_left]
  have hχinj : Set.InjOn χ (Metric.ball (G a) ρ) := by
    intro z1 hz1 z2 hz2 heq
    have h1 := hχG z1 hz1
    have h2 := hχG z2 hz2
    rw [heq] at h1
    exact h1.symm.trans h2
  have hχuniq : ∀ z ∈ Metric.ball (G a) ρ, ∀ w ∈ Metric.closedBall a (R / 2),
      G w = z → w = χ z := by
    intro z hz w hw hGw
    have h1 : w - a ∈ Metric.closedBall (0:ℂ) (R / 2) := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      have hw' := Metric.mem_closedBall.mp hw
      rwa [dist_eq_norm] at hw'
    have h2 : Φ (w - a) = (z - G a) / A := by
      show (G (a + (w - a)) - G a) / A = (z - G a) / A
      have h3 : a + (w - a) = w := by ring
      rw [h3, hGw]
    obtain ⟨-, -, -, h3⟩ := hu_spec z (hsmall z hz)
    have h4 : w - a = u z := h3 (w - a) h1 h2
    show w = a + u z
    rw [← h4]; ring
  have hχdiff : DifferentiableOn ℂ χ (Metric.ball (G a) ρ) := by
    intro z hz
    obtain ⟨-, h2, h2b, h3⟩ := hu_spec z (hsmall z hz)
    have huR : u z ∈ Metric.ball (0:ℂ) R := by
      rw [Metric.mem_ball, dist_eq_norm, sub_zero]
      linarith
    have hana : AnalyticAt ℂ Φ (u z) := hΦd.analyticAt ((Metric.isOpen_ball).mem_nhds huR)
    have hder : deriv Φ (u z) ≠ 0 := by
      intro h0
      have hh := hΦuniv (u z) huR
      rw [h0] at hh
      simp at hh
      linarith
    obtain ⟨r', hr', φ, hφd, hφ0, hφΦ, hφmap, hφinj⟩ :=
      local_branch_disc (U := Metric.ball (0:ℂ) (R / 2)) hana hder Metric.isOpen_ball (by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact h2)
    have hy0 : (z - G a) / A ∈ Metric.ball (Φ (u z)) r' := by
      rw [← h2b]
      exact Metric.mem_ball_self hr'
    have hneigh : ({z' : ℂ | z' ∈ Metric.ball (G a) ρ ∧ (z' - G a) / A ∈ Metric.ball (Φ (u z)) r'})
        ∈ 𝓝 z := by
      refine Filter.inter_mem ((Metric.isOpen_ball).mem_nhds hz) ?_
      exact ((Metric.isOpen_ball).preimage (by fun_prop : Continuous fun z' : ℂ => (z' - G a) / A)
        ) |>.mem_nhds hy0
    have hev : χ =ᶠ[𝓝 z] (fun z' => a + φ ((z' - G a) / A)) := by
      refine Filter.eventuallyEq_of_mem hneigh ?_
      intro z' hz'
      obtain ⟨hz'ball, hz'mem⟩ := hz'
      obtain ⟨-, -, -, h3'⟩ := hu_spec z' (hsmall z' hz'ball)
      have hφmem : φ ((z' - G a) / A) ∈ Metric.closedBall (0:ℂ) (R / 2) :=
        Metric.ball_subset_closedBall (hφmap hz'mem)
      have hφeq : Φ (φ ((z' - G a) / A)) = (z' - G a) / A := hφΦ _ hz'mem
      have h4 : φ ((z' - G a) / A) = u z' := h3' _ hφmem hφeq
      show a + u z' = a + φ ((z' - G a) / A)
      rw [h4]
    have hφat : DifferentiableAt ℂ φ ((z - G a) / A) :=
      hφd.differentiableAt ((Metric.isOpen_ball).mem_nhds hy0)
    have haff : DifferentiableAt ℂ (fun z' : ℂ => (z' - G a) / A) z :=
      (differentiableAt_id.sub_const (G a)).div_const A
    have hmain : DifferentiableAt ℂ (fun z' : ℂ => a + φ ((z' - G a) / A)) z :=
      (hφat.comp z haff).const_add a
    exact (hmain.congr_of_eventuallyEq hev).differentiableWithinAt
  have hχderiv : ∀ z ∈ Metric.ball (G a) ρ, ‖deriv χ z‖ ≤ 2 / ‖A‖ := by
    intro z hz
    have hχzR : χ z ∈ Metric.ball a R := by
      have h1 := hχclose z hz
      rw [Metric.mem_ball, dist_eq_norm]
      linarith
    have hGat : DifferentiableAt ℂ G (χ z) :=
      hGd.differentiableAt ((Metric.isOpen_ball).mem_nhds hχzR)
    have hχat : DifferentiableAt ℂ χ z :=
      hχdiff.differentiableAt ((Metric.isOpen_ball).mem_nhds hz)
    have hev : (G ∘ χ) =ᶠ[𝓝 z] id := by
      filter_upwards [(Metric.isOpen_ball).mem_nhds hz] with z' hz'
      exact hχG z' hz'
    have home : deriv (G ∘ χ) z = 1 :=
      ((hasDerivAt_id z).congr_of_eventuallyEq hev).deriv
    have hcomp : deriv (G ∘ χ) z = deriv G (χ z) * deriv χ z := deriv_comp z hGat hχat
    have hmul : deriv G (χ z) * deriv χ z = 1 := by rw [← hcomp]; exact home
    have hlb : ‖A‖ * (1 - k) ≤ ‖deriv G (χ z)‖ := by
      have h := huniv (χ z) hχzR
      have h2 : ‖A‖ - ‖deriv G (χ z)‖ ≤ ‖deriv G (χ z) - A‖ := by
        have hh : ‖A‖ - ‖deriv G (χ z)‖ ≤ ‖A - deriv G (χ z)‖ :=
          (abs_le.mp (abs_norm_sub_norm_le A (deriv G (χ z)))).2
        rwa [norm_sub_rev] at hh
      have h3 : ‖A‖ - k * ‖A‖ ≤ ‖deriv G (χ z)‖ := by linarith
      calc ‖A‖ * (1 - k) = ‖A‖ - k * ‖A‖ := by ring
        _ ≤ ‖deriv G (χ z)‖ := h3
    have hpos : 0 < ‖deriv G (χ z)‖ := lt_of_lt_of_le (by positivity) hlb
    have hnorm : ‖deriv χ z‖ = 1 / ‖deriv G (χ z)‖ := by
      rw [eq_div_iff hpos.ne']
      have := congrArg norm hmul
      rwa [norm_mul, norm_one, mul_comm] at this
    have h2A : ‖A‖ / 2 ≤ ‖A‖ * (1 - k) := by nlinarith [hk1, hApos]
    rw [hnorm]
    calc 1 / ‖deriv G (χ z)‖ ≤ 1 / (‖A‖ * (1 - k)) :=
          one_div_le_one_div_of_le (by positivity) hlb
      _ ≤ 2 / ‖A‖ := by
          rw [div_le_div_iff₀ (by positivity) hApos]
          nlinarith
  exact ⟨χ, hχdiff, hχa, hχG, hχinj, hχclose, hχderiv, hχuniq⟩


theorem head_stability {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β₀ : ℂ} {j₀ : ℕ} (hj₀ : 0 < j₀) {ζ : ℂ} {z : ℕ → ℂ} (hz0 : z 0 = ζ)
    (hz : ∀ j, 1 ≤ j → j ≤ j₀ → z j ∈ d.DE ∧ d.E (z j) - β₀ = z (j - 1) ∧ deriv d.E (z j) ≠ 0)
    {r : ℝ} (hr : 0 < r) (hr8 : r < 1 / 8)
    (hcollar : (⋃ j ∈ Finset.Icc 1 j₀, Metric.closedBall (z j) (2 * r)) ⊆ d.DE) :
    ∃ (ρ₁ ε δ C C' : ℝ), 0 < ρ₁ ∧ ρ₁ ≤ r ∧ 0 < ε ∧ 0 < δ ∧ 0 < C ∧ 0 < C' ∧
      IsCompact (⋃ j ∈ Finset.Icc 1 j₀, Metric.closedBall (z j) (2 * r)) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₁ → ∀ β : ℂ, ‖β - β₀‖ < ε →
        ∀ (R : ℂ → ℂ) (DR : Set ℂ), IsOpen DR →
          (⋃ j ∈ Finset.Icc 1 j₀, Metric.closedBall (z j) (2 * r)) ⊆ DR →
          DifferentiableOn ℂ R DR →
          (∀ w ∈ ⋃ j ∈ Finset.Icc 1 j₀, Metric.closedBall (z j) (2 * r), ‖R w - d.E w‖ < δ) →
          ∃ W : ℕ → Set ℂ, W 0 = Metric.ball ζ ρ ∧ ∀ j, j < j₀ →
            W (j + 1) ⊆ Metric.ball (z (j + 1)) r ∧ IsOpen (W (j + 1)) ∧ IsConnected (W (j + 1)) ∧
            Bornology.IsBounded (W (j + 1)) ∧
            Set.InjOn (fun u => R u - β) (W (j + 1)) ∧
            (fun u => R u - β) '' W (j + 1) = W j ∧
            ∀ u ∈ W (j + 1), C < ‖deriv ((fun u => R u - β)^[j + 1]) u‖ ∧
              ‖deriv ((fun u => R u - β)^[j + 1]) u‖ < C' := by
  classical
  -- ## 0. the collar
  set Kc : Set ℂ := ⋃ j ∈ Finset.Icc 1 j₀, Metric.closedBall (z j) (2 * r) with hKc_def
  have hKc_comp : IsCompact Kc := by
    rw [hKc_def]
    exact Set.Finite.isCompact_biUnion (Finset.finite_toSet _)
      (fun j _ => isCompact_closedBall (z j) (2 * r))
  have hKc_sub : ∀ j : ℕ, 1 ≤ j → j ≤ j₀ → Metric.closedBall (z j) (2 * r) ⊆ Kc := by
    intro j h1 h2
    rw [hKc_def]
    exact Set.subset_biUnion_of_mem (u := fun j => Metric.closedBall (z j) (2 * r))
      (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hKc_DE : Kc ⊆ d.DE := by rw [hKc_def]; exact hcollar
  have hDEopen : IsOpen d.DE := by
    have hbasin : IsOpen (ParabolicBasin g₀ D) := by
      rw [isOpen_iff_mem_nhds]
      rintro w ⟨U, hU, h1, h2⟩
      refine Filter.mem_of_superset (isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hU)) ?_
      intro w' hw'
      exact ⟨interior U, isOpen_interior.mem_nhds hw',
        fun n x hx => h1 n (interior_subset hx), h2.mono interior_subset⟩
    have h := d.φ_holo.continuousOn.isOpen_inter_preimage d.Dφ_open hbasin
    rw [show d.DE = d.Dφ ∩ d.φ ⁻¹' ParabolicBasin g₀ D from by
      ext w; simp [MandelDim.ParabData.DE]]
    exact h
  -- ## 1. the exact chain's data
  let AN : ℕ → ℝ := fun m => ‖deriv d.E (z m)‖
  have hz_DE : ∀ j, 1 ≤ j → j ≤ j₀ → z j ∈ d.DE := fun j h1 h2 => (hz j h1 h2).1
  have hz_ne : ∀ j, 1 ≤ j → j ≤ j₀ → deriv d.E (z j) ≠ 0 := fun j h1 h2 => (hz j h1 h2).2.2
  have hz_E : ∀ j, 1 ≤ j → j ≤ j₀ → d.E (z j) - β₀ = z (j - 1) := fun j h1 h2 => (hz j h1 h2).2.1
  have hApos : ∀ j, 1 ≤ j → j ≤ j₀ → 0 < AN j :=
    fun j h1 h2 => norm_pos_iff.mpr (hz_ne j h1 h2)
  have hRm_exists : ∀ j, 1 ≤ j → j ≤ j₀ → ∃ Rm : ℝ, 0 < Rm ∧ Rm ≤ r ∧
      Metric.ball (z j) Rm ⊆ d.DE ∧
      (∀ w ∈ Metric.ball (z j) Rm, ‖deriv d.E w - deriv d.E (z j)‖ ≤ AN j / 8) := by
    intro j h1 h2
    obtain ⟨Rm, h3, h4, h5, h6⟩ := deriv_control_radius (U := d.DE) hDEopen
      (Work.Horn.differentiableOn_E d) (hz_DE j h1 h2) (hz_ne j h1 h2) (r := r) hr
    exact ⟨Rm, h3, h4, h5, fun w hw => by simpa only [AN] using h6 w hw⟩
  let Rm : ℕ → ℝ := fun j =>
    if h : 1 ≤ j ∧ j ≤ j₀ then Classical.choose (hRm_exists j h.1 h.2) else 1
  have hRm : ∀ j, 1 ≤ j → j ≤ j₀ → 0 < Rm j ∧ Rm j ≤ r ∧
      Metric.ball (z j) (Rm j) ⊆ d.DE ∧
      (∀ w ∈ Metric.ball (z j) (Rm j), ‖deriv d.E w - deriv d.E (z j)‖ ≤ AN j / 8) := by
    intro j h1 h2
    have hred : Rm j = Classical.choose (hRm_exists j h1 h2) := by
      simp only [Rm]; rw [dif_pos ⟨h1, h2⟩]
    rw [hred]
    exact Classical.choose_spec (hRm_exists j h1 h2)
  -- ## 2. the constants
  have hIccne : (Finset.Icc 1 j₀).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hj₀⟩⟩
  obtain ⟨m₀, hm₀, hmin_le⟩ := Finset.exists_min_image (Finset.Icc 1 j₀) AN hIccne
  let amin : ℝ := AN m₀
  have hamin_pos : 0 < amin :=
    hApos m₀ (Finset.mem_Icc.mp hm₀).1 (Finset.mem_Icc.mp hm₀).2
  have hamin_le : ∀ j, 1 ≤ j → j ≤ j₀ → amin ≤ AN j :=
    fun j h1 h2 => hmin_le j (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  obtain ⟨m₁, hm₁, hmax_le⟩ := Finset.exists_max_image (Finset.Icc 1 j₀) AN hIccne
  let amax : ℝ := AN m₁
  have hA_le_amax : ∀ j, 1 ≤ j → j ≤ j₀ → AN j ≤ amax :=
    fun j h1 h2 => hmax_le j (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  obtain ⟨m₂, hm₂, hminR_le⟩ := Finset.exists_min_image (Finset.Icc 1 j₀) Rm hIccne
  let Rmin : ℝ := Rm m₂
  have hRmin_pos : 0 < Rmin :=
    (hRm m₂ (Finset.mem_Icc.mp hm₂).1 (Finset.mem_Icc.mp hm₂).2).1
  have hRmin_le : ∀ j, 1 ≤ j → j ≤ j₀ → Rmin ≤ Rm j :=
    fun j h1 h2 => hminR_le j (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  let M : ℝ := max 1 (4 / (3 * amin))
  have hM1 : (1 : ℝ) ≤ M := le_max_left _ _
  have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
  have hMge : 4 / (3 * amin) ≤ M := le_max_right _ _
  let Rb0 : ℝ := Rmin / (4 * M ^ j₀)
  have hMj : 0 < M ^ j₀ := pow_pos hMpos j₀
  have hRb0pos : 0 < Rb0 := by
    simp only [Rb0]
    exact div_pos hRmin_pos (by linarith)
  have hj₀R : (1 : ℝ) ≤ (j₀ : ℝ) := by exact_mod_cast hj₀
  let c0 : ℝ := min (Rb0 / (4 * (j₀ : ℝ))) ((3 / 8) * amin * Rb0 / 4)
  have hc0pos : 0 < c0 := by
    have h1 : 0 < Rb0 / (4 * (j₀ : ℝ)) := div_pos hRb0pos (by linarith)
    have h2 : 0 < (3 / 8) * amin * Rb0 / 4 := by positivity
    simpa only [c0] using lt_min h1 h2
  let ε : ℝ := c0 / 2
  let δ : ℝ := min (c0 / 2) (r * amin / 8)
  have hεpos : 0 < ε := by simp only [ε]; linarith
  have hδpos : 0 < δ := by
    have h1 : 0 < c0 / 2 := by linarith
    have h2 : 0 < r * amin / 8 := by positivity
    simpa only [δ] using lt_min h1 h2
  have hδle : δ ≤ c0 / 2 := by simpa only [δ] using min_le_left (c0 / 2) (r * amin / 8)
  have hδle' : δ ≤ r * amin / 8 := by simpa only [δ] using min_le_right (c0 / 2) (r * amin / 8)
  let c : ℝ := δ + ε
  have hcpos : 0 < c := by simp only [c]; linarith
  have hc_le_c0 : c ≤ c0 := by simp only [c, ε]; linarith
  have hc_le_Rb : c ≤ Rb0 / (4 * (j₀ : ℝ)) :=
    le_trans hc_le_c0 (by simpa only [c0] using min_le_left (Rb0 / (4 * (j₀ : ℝ))) _)
  have hc_le_amin : c ≤ (3 / 8) * amin * Rb0 / 4 :=
    le_trans hc_le_c0 (by simpa only [c0] using min_le_right _ ((3 / 8) * amin * Rb0 / 4))
  let ρ₁ : ℝ := min r ((3 / 8) * amin * Rb0 / 4)
  have hρ₁pos : 0 < ρ₁ := by
    have h2 : 0 < (3 / 8) * amin * Rb0 / 4 := by positivity
    simpa only [ρ₁] using lt_min hr h2
  have hρ₁le : ρ₁ ≤ r := by simpa only [ρ₁] using min_le_left r ((3 / 8) * amin * Rb0 / 4)
  have hρ₁le' : ρ₁ ≤ (3 / 8) * amin * Rb0 / 4 :=
    by simpa only [ρ₁] using min_le_right r ((3 / 8) * amin * Rb0 / 4)
  -- ## 3. the sequence of radii
  let Ae : ℕ → ℝ := fun m => if h : 1 ≤ m ∧ m ≤ j₀ then AN m else amin
  have hAe_pos : ∀ m : ℕ, 0 < Ae m := by
    intro m
    by_cases h : 1 ≤ m ∧ m ≤ j₀
    · simp only [Ae]; rw [dif_pos h]; exact hApos m h.1 h.2
    · simp only [Ae]; rw [dif_neg h]; exact hamin_pos
  have hamin_le_Ae : ∀ m : ℕ, amin ≤ Ae m := by
    intro m
    by_cases h : 1 ≤ m ∧ m ≤ j₀
    · simp only [Ae]; rw [dif_pos h]; exact hamin_le m h.1 h.2
    · simp only [Ae]; rw [dif_neg h]
  have hAe_eq : ∀ m : ℕ, 1 ≤ m → m ≤ j₀ → Ae m = AN m := by
    intro m h1 h2
    simp only [Ae]; rw [dif_pos ⟨h1, h2⟩]
  let Rb : ℕ → ℝ := Nat.rec Rb0 (fun n r => 4 * (r + 2 * c) / (3 * Ae (n + 2)))
  have hRb_zero : Rb 0 = Rb0 := rfl
  have hRb_succ : ∀ n : ℕ, Rb (n + 1) = 4 * (Rb n + 2 * c) / (3 * Ae (n + 2)) := fun n => rfl
  let Δ : ℕ → ℝ := Nat.rec ρ₁ (fun n _ => Rb n / 2)
  have hΔ_zero : Δ 0 = ρ₁ := rfl
  have hΔ_succ : ∀ n : ℕ, Δ (n + 1) = Rb n / 2 := fun n => rfl
  -- ## 4. the recurrence bounds
  have hRb_bd : ∀ n ≤ j₀, 0 < Rb n ∧ Rb n ≤ (Rb0 + 2 * c * n) * M ^ n := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨hRb0pos, ?_⟩
      rw [hRb_zero]
      norm_num
    | succ k ih =>
      intro hk
      obtain ⟨hkpos, hkbd⟩ := ih (by omega)
      have hstep := hRb_succ k
      have hAek : amin ≤ Ae (k + 2) := hamin_le_Ae (k + 2)
      have hAekpos : 0 < Ae (k + 2) := hAe_pos (k + 2)
      have hx : 0 < Rb k + 2 * c := by linarith
      have h1 : Rb (k + 1) ≤ (Rb k + 2 * c) * M := by
        rw [hstep]
        calc 4 * (Rb k + 2 * c) / (3 * Ae (k + 2))
            = (Rb k + 2 * c) * (4 / (3 * Ae (k + 2))) := by ring
          _ ≤ (Rb k + 2 * c) * M := by
              refine mul_le_mul_of_nonneg_left ?_ hx.le
              have h3 : 3 * amin ≤ 3 * Ae (k + 2) := by linarith
              have h4 : 4 / (3 * Ae (k + 2)) ≤ 4 / (3 * amin) := by
                rw [div_le_div_iff₀ (by linarith) (by linarith)]
                linarith
              exact le_trans h4 hMge
      have hMk : (1 : ℝ) ≤ M ^ k := one_le_pow₀ hM1
      have h2 : Rb k + 2 * c ≤ (Rb0 + 2 * c * ↑(k + 1)) * M ^ k := by
        have h3 : 2 * c ≤ 2 * c * M ^ k := by nlinarith [hMk, hcpos]
        have h4 : (Rb0 + 2 * c * ↑k) * M ^ k + 2 * c * M ^ k
            = (Rb0 + 2 * c * ↑(k + 1)) * M ^ k := by push_cast; ring
        linarith [hkbd, h3, h4]
      have h5 : Rb (k + 1) ≤ (Rb0 + 2 * c * ↑(k + 1)) * M ^ k * M :=
        le_trans h1 (mul_le_mul_of_nonneg_right h2 hMpos.le)
      refine ⟨?_, ?_⟩
      · rw [hstep]
        exact div_pos (by linarith) (by linarith)
      · calc Rb (k + 1) ≤ (Rb0 + 2 * c * ↑(k + 1)) * M ^ k * M := h5
          _ = (Rb0 + 2 * c * ↑(k + 1)) * M ^ (k + 1) := by rw [pow_succ]; ring
  have hRb_le : ∀ n, n < j₀ → Rb n ≤ Rm (n + 1) := by
    intro n hn
    have hbd := (hRb_bd n hn.le).2
    have hcast : (n : ℝ) ≤ (j₀ : ℝ) := by exact_mod_cast hn.le
    have h1 : (Rb0 + 2 * c * n) * M ^ n ≤ (Rb0 + 2 * c * j₀) * M ^ j₀ := by
      have h2 : Rb0 + 2 * c * n ≤ Rb0 + 2 * c * j₀ := by nlinarith [hcpos]
      have h3 : M ^ n ≤ M ^ j₀ := pow_le_pow_right₀ hM1 hn.le
      exact mul_le_mul h2 h3 (pow_nonneg hMpos.le n) (by nlinarith [hRb0pos, hcpos])
    have h4 : (Rb0 + 2 * c * j₀) * M ^ j₀ ≤ Rmin := by
      have h6 : 2 * c * (j₀ : ℝ) ≤ Rb0 / 2 := by
        have h8 : 0 < 4 * (j₀ : ℝ) := by linarith
        have h9 := (le_div_iff₀ h8).mp hc_le_Rb
        nlinarith
      have h9 : Rb0 + 2 * c * j₀ ≤ Rb0 + Rb0 / 2 := by linarith
      have h10 : (Rb0 + Rb0 / 2) * M ^ j₀ = (3 / 8) * Rmin := by
        simp only [Rb0]
        field_simp
        ring
      calc (Rb0 + 2 * c * j₀) * M ^ j₀ ≤ (Rb0 + Rb0 / 2) * M ^ j₀ :=
            mul_le_mul_of_nonneg_right h9 hMj.le
        _ = (3 / 8) * Rmin := h10
        _ ≤ Rmin := by linarith [hRmin_pos]
    exact le_trans (le_trans hbd h1) (le_trans h4 (hRmin_le (n + 1) (by omega) (by omega)))
  have hdom : ∀ n (hn : n < j₀), Δ n + c ≤ (3 / 8) * Ae (n + 1) * Rb n := by
    intro n hn
    rcases eq_or_ne n 0 with h0 | hne
    · subst h0
      rw [hΔ_zero, hRb_zero]
      have h1 : amin ≤ Ae 1 := hamin_le_Ae 1
      have h3 : c ≤ (3 / 8) * amin * Rb0 / 4 := hc_le_amin
      have h4 : ρ₁ ≤ (3 / 8) * amin * Rb0 / 4 := hρ₁le'
      have h5 : (3 / 8) * amin * Rb0 / 4 + (3 / 8) * amin * Rb0 / 4
          = (3 / 8) * amin * Rb0 / 2 := by ring
      have h6 : (3 / 8) * amin * Rb0 / 2 ≤ (3 / 8) * Ae 1 * Rb0 := by nlinarith [h1, hRb0pos]
      linarith
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hne
      have hk : k + 1 < j₀ := by omega
      rw [hΔ_succ k, hRb_succ k]
      have hkey : (3 / 8) * Ae (k + 2) * (4 * (Rb k + 2 * c) / (3 * Ae (k + 2)))
          = Rb k / 2 + c := by
        have hA' : (Ae (k + 2)) ≠ 0 := ne_of_gt (hAe_pos (k + 2))
        field_simp
        ring
      rw [hkey]
  have hdomA : ∀ n (hn : n < j₀), Δ n + c ≤ (3 / 8) * AN (n + 1) * Rb n := by
    intro n hn
    have h1 := hdom n hn
    have h2 : Ae (n + 1) = AN (n + 1) := hAe_eq (n + 1) (by omega) (by omega)
    rwa [h2] at h1
  -- ## 5. the derivative constants
  let c_lo : ℝ := 3 * amin / 4
  let c_hi : ℝ := 5 * amax / 4
  have hc_lo_pos : 0 < c_lo := by simp only [c_lo]; linarith
  have hc_hi_pos : 0 < c_hi := by
    simp only [c_hi]
    have h1 := hApos m₁ (Finset.mem_Icc.mp hm₁).1 (Finset.mem_Icc.mp hm₁).2
    linarith
  let C : ℝ := (min c_lo 1 / 2) ^ j₀
  let C' : ℝ := (2 * max c_hi 1) ^ j₀
  have hCpos : 0 < C := by
    have h1 : 0 < min c_lo 1 / 2 := by
      have := lt_min hc_lo_pos one_pos
      linarith
    simpa only [C] using pow_pos h1 j₀
  have hC'pos : 0 < C' := by
    have h1 : 0 < max c_hi 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have h2 : 0 < 2 * max c_hi 1 := by linarith
    simpa only [C'] using pow_pos h2 j₀
  -- ## 6. the perturbed chain
  refine ⟨ρ₁, ε, δ, C, C', hρ₁pos, hρ₁le, hεpos, hδpos, hCpos, hC'pos, ?_, ?_⟩
  · simpa only [← hKc_def] using hKc_comp
  · intro ρ hρ hρρ₁ β hβ R DR hDR hDRsub hRdiff hclose
    have hDRsub' : Kc ⊆ DR := by rw [hKc_def]; exact hDRsub
    have hclose' : ∀ w ∈ Kc, ‖R w - d.E w‖ < δ := fun w hw => hclose w (by rwa [hKc_def] at hw)
    set G : ℂ → ℂ := fun w => R w - β with hG
    -- (a) the `C¹` control of `R - d.E` on the collar
    have hCauchy : ∀ l, 1 ≤ l → l ≤ j₀ → ∀ w ∈ Metric.closedBall (z l) r,
        ‖deriv (fun u => R u - d.E u) w‖ ≤ δ / r := by
      intro l h1 h2 w hw
      have hsub : Metric.closedBall (z l) (2 * r) ⊆ DR ∩ d.DE := fun w' hw' =>
        ⟨hDRsub' (hKc_sub l h1 h2 hw'), hKc_DE (hKc_sub l h1 h2 hw')⟩
      have hfd : DifferentiableOn ℂ (fun u => R u - d.E u) (DR ∩ d.DE) :=
        (hRdiff.mono Set.inter_subset_left).sub
          ((Work.Horn.differentiableOn_E d).mono Set.inter_subset_right)
      have hbdd : ∀ w' ∈ Metric.closedBall (z l) (2 * r), ‖R w' - d.E w'‖ ≤ δ :=
        fun w' hw' => (hclose' w' (hKc_sub l h1 h2 hw')).le
      exact cauchy_deriv_bound hr (hDR.inter hDEopen) hfd hsub hbdd w hw
    -- (b) the per-step univalence
    have hRb_pos : ∀ n, n < j₀ → 0 < Rb n := fun n hn => (hRb_bd n hn.le).1
    have huniv : ∀ n (hn : n < j₀), ∀ w ∈ Metric.ball (z (n + 1)) (Rb n),
        ‖deriv G w - deriv d.E (z (n + 1))‖ ≤ (1 / 4) * AN (n + 1) := by
      intro n hn w hw
      have hwR : w ∈ Metric.ball (z (n + 1)) (Rm (n + 1)) :=
        Metric.ball_subset_ball (hRb_le n hn) hw
      have hwcl : w ∈ Metric.closedBall (z (n + 1)) r :=
        Metric.ball_subset_closedBall (Metric.ball_subset_ball (hRm (n + 1) (by omega) (by omega)).2.1 hwR)
      have hwK : w ∈ Kc := hKc_sub (n + 1) (by omega) (by omega)
        (Metric.closedBall_subset_closedBall (by linarith) hwcl)
      have hRat : DifferentiableAt ℂ R w := hRdiff.differentiableAt (hDR.mem_nhds (hDRsub' hwK))
      have hEat : DifferentiableAt ℂ d.E w :=
        (Work.Horn.differentiableOn_E d).differentiableAt (hDEopen.mem_nhds (hKc_DE hwK))
      have hder : deriv G w = deriv R w := by
        show deriv (fun w => R w - β) w = deriv R w
        exact deriv_sub_const β
      have h1 : ‖deriv G w - deriv d.E w‖ ≤ δ / r := by
        have hc := hCauchy (n + 1) (by omega) (by omega) w hwcl
        have hsub_eq : deriv (fun u => R u - d.E u) w = deriv R w - deriv d.E w := by
          show deriv (R - d.E) w = deriv R w - deriv d.E w
          exact deriv_sub hRat hEat
        rw [hsub_eq, ← hder] at hc
        exact hc
      have h2 : ‖deriv d.E w - deriv d.E (z (n + 1))‖ ≤ AN (n + 1) / 8 :=
        (hRm (n + 1) (by omega) (by omega)).2.2.2 w hwR
      have h3 : δ / r ≤ AN (n + 1) / 8 := by
        rw [div_le_div_iff₀ hr (by norm_num : (0 : ℝ) < 8)]
        nlinarith [hδle', hamin_le (n + 1) (by omega) (by omega), hr]
      calc ‖deriv G w - deriv d.E (z (n + 1))‖
          = ‖(deriv G w - deriv d.E w) + (deriv d.E w - deriv d.E (z (n + 1)))‖ := by ring_nf
        _ ≤ ‖deriv G w - deriv d.E w‖ + ‖deriv d.E w - deriv d.E (z (n + 1))‖ := norm_add_le _ _
        _ ≤ (1 / 4) * AN (n + 1) := by linarith
    -- (c) the inverse branches
    have hgd : ∀ n, n < j₀ → DifferentiableOn ℂ G (Metric.ball (z (n + 1)) (Rb n)) := by
      intro n hn
      refine (hRdiff.mono ?_).sub_const β
      intro w hw
      refine hDRsub' (hKc_sub (n + 1) (by omega) (by omega) ?_)
      rw [Metric.mem_closedBall]
      have h1 : dist w (z (n + 1)) < Rb n := by
        have := Metric.mem_ball.mp hw
        first | exact this | (rwa [dist_eq_norm] at this) | simpa [dist_eq_norm] using this
      calc dist w (z (n + 1)) ≤ Rb n := h1.le
        _ ≤ Rm (n + 1) := hRb_le n hn
        _ ≤ r := (hRm (n + 1) (by omega) (by omega)).2.1
        _ ≤ 2 * r := by linarith
    have hbranch : ∀ n, n < j₀ → ∃ χ : ℂ → ℂ,
        DifferentiableOn ℂ χ (Metric.ball (G (z (n + 1)))
          (AN (n + 1) * (1 - 1 / 4) * Rb n / 2)) ∧
        χ (G (z (n + 1))) = z (n + 1) ∧
        (∀ z' ∈ Metric.ball (G (z (n + 1))) (AN (n + 1) * (1 - 1 / 4) * Rb n / 2),
          G (χ z') = z') ∧
        Set.InjOn χ (Metric.ball (G (z (n + 1))) (AN (n + 1) * (1 - 1 / 4) * Rb n / 2)) ∧
        (∀ z' ∈ Metric.ball (G (z (n + 1))) (AN (n + 1) * (1 - 1 / 4) * Rb n / 2),
          ‖χ z' - z (n + 1)‖ < Rb n / 2) ∧
        (∀ z' ∈ Metric.ball (G (z (n + 1))) (AN (n + 1) * (1 - 1 / 4) * Rb n / 2),
          ‖deriv χ z'‖ ≤ 2 / AN (n + 1)) ∧
        (∀ z' ∈ Metric.ball (G (z (n + 1))) (AN (n + 1) * (1 - 1 / 4) * Rb n / 2),
          ∀ w ∈ Metric.closedBall (z (n + 1)) (Rb n / 2), G w = z' → w = χ z') :=
      fun n hn => branch_stability (hRb_pos n hn) (hz_ne (n + 1) (by omega) (by omega))
        (by norm_num) (by norm_num) (hgd n hn) (huniv n hn)
    choose χ hχ using hbranch
    -- (d) the discs
    let W : ℕ → Set ℂ := Nat.rec (Metric.ball ζ ρ)
      (fun n Wn => (G ⁻¹' Wn) ∩ Metric.ball (z (n + 1)) (Rb n / 2))
    have hW0 : W 0 = Metric.ball ζ ρ := rfl
    have hWsucc : ∀ n : ℕ, W (n + 1) = (G ⁻¹' W n) ∩ Metric.ball (z (n + 1)) (Rb n / 2) :=
      fun n => rfl
    -- (e) the one-step analysis
    have hstep : ∀ n (hn : n < j₀), W n ⊆ Metric.ball (z n) (Δ n) →
        W n ⊆ Metric.ball (G (z (n + 1))) (AN (n + 1) * (1 - 1 / 4) * Rb n / 2) ∧
        W (n + 1) = χ n hn '' W n ∧
        W (n + 1) ⊆ Metric.ball (z (n + 1)) (Δ (n + 1)) ∧
        InjOn G (W (n + 1)) ∧ G '' W (n + 1) = W n := by
      intro n hn hl
      obtain ⟨hdiff, hG0, hinv, hinj, hcloseχ, hderχ, huniqχ⟩ := hχ n hn
      have hrad : AN (n + 1) * (1 - 1 / 4) * Rb n / 2 = (3 / 8) * AN (n + 1) * Rb n := by ring
      have hdom : W n ⊆ Metric.ball (G (z (n + 1))) (AN (n + 1) * (1 - 1 / 4) * Rb n / 2) := by
        intro w hw
        have h1 : ‖w - z n‖ < Δ n := by
          have := hl hw
          rwa [Metric.mem_ball, dist_eq_norm] at this
        have hab : ‖z n - G (z (n + 1))‖ < c := by
          have hzE : d.E (z (n + 1)) - β₀ = z n := by
            have h := hz_E (n + 1) (by omega) (by omega)
            rwa [show n + 1 - 1 = n from by omega] at h
          have hsplit : z n - G (z (n + 1)) = -(R (z (n + 1)) - d.E (z (n + 1))) + (β - β₀) := by
            rw [← hzE]; simp only [G]; ring
          rw [hsplit]
          have hb1 : ‖R (z (n + 1)) - d.E (z (n + 1))‖ < δ :=
            hclose' _ (hKc_sub (n + 1) (by omega) (by omega)
              (Metric.mem_closedBall_self (by linarith)))
          calc ‖-(R (z (n + 1)) - d.E (z (n + 1))) + (β - β₀)‖
              ≤ ‖-(R (z (n + 1)) - d.E (z (n + 1)))‖ + ‖β - β₀‖ := norm_add_le _ _
            _ = ‖R (z (n + 1)) - d.E (z (n + 1))‖ + ‖β - β₀‖ := by rw [norm_neg]
            _ < δ + ε := add_lt_add hb1 hβ
            _ = c := by simp only [c]
        rw [Metric.mem_ball, dist_eq_norm]
        have hsplit2 : w - G (z (n + 1)) = (w - z n) + (z n - G (z (n + 1))) := by ring
        rw [hsplit2]
        calc ‖(w - z n) + (z n - G (z (n + 1)))‖
            ≤ ‖w - z n‖ + ‖z n - G (z (n + 1))‖ := norm_add_le _ _
          _ < Δ n + c := add_lt_add_of_lt_of_le h1 hab.le
          _ ≤ AN (n + 1) * (1 - 1 / 4) * Rb n / 2 := by rw [hrad]; exact hdomA n hn
      have hEq : W (n + 1) = χ n hn '' W n := by
        refine Subset.antisymm ?_ ?_
        · intro u hu
          rw [hWsucc n] at hu
          obtain ⟨hu1, hu2⟩ := hu
          have hmem : u ∈ Metric.closedBall (z (n + 1)) (Rb n / 2) :=
            Metric.ball_subset_closedBall hu2
          exact ⟨G u, hu1, (huniqχ (G u) (hdom hu1) u hmem rfl).symm⟩
        · rintro u ⟨z', hz', rfl⟩
          rw [hWsucc n]
          exact ⟨by show G (χ n hn z') ∈ W n; rw [hinv z' (hdom hz')]; exact hz',
            Metric.mem_ball.mpr (by rw [dist_eq_norm]; exact hcloseχ z' (hdom hz'))⟩
      refine ⟨hdom, hEq, ?_, ?_, ?_⟩
      · rw [hEq]
        rintro u ⟨z', hz', rfl⟩
        rw [hΔ_succ, Metric.mem_ball, dist_eq_norm]
        exact hcloseχ z' (hdom hz')
      · rw [hEq]
        rintro u ⟨z1, hz1, rfl⟩ u' ⟨z2, hz2, rfl⟩ heq
        have h1 : G (χ n hn z1) = z1 := hinv z1 (hdom hz1)
        have h2 : G (χ n hn z2) = z2 := hinv z2 (hdom hz2)
        have hz : z1 = z2 := by rw [h1, h2] at heq; exact heq
        rw [hz]
      · rw [hEq]
        ext u
        constructor
        · rintro ⟨z', ⟨z'', hz'', rfl⟩, rfl⟩
          exact by rw [hinv z'' (hdom hz'')]; exact hz''
        · intro hu
          exact ⟨χ n hn u, ⟨u, hu, rfl⟩, hinv u (hdom hu)⟩
    -- (f) the joint induction
    have hall : ∀ n ≤ j₀, W n ⊆ Metric.ball (z n) (Δ n) ∧ IsOpen (W n) ∧ IsConnected (W n) ∧
        Bornology.IsBounded (W n) := by
      intro n
      induction n with
      | zero =>
        intro _
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [hW0, hz0]
          exact Metric.ball_subset_ball hρρ₁
        · rw [hW0]; exact Metric.isOpen_ball
        · rw [hW0]
          exact (convex_ball ζ ρ).isConnected ⟨ζ, Metric.mem_ball_self hρ⟩
        · rw [hW0]; exact Metric.isBounded_ball
      | succ k ih =>
        intro hk
        obtain ⟨hloc, hopen, hconn, hbdd⟩ := ih (by omega)
        have hk' : k < j₀ := by omega
        obtain ⟨hdomk, e1, e2, e3, e4⟩ := hstep k hk' hloc
        refine ⟨e2, ?_, ?_, ?_⟩
        · rw [hWsucc k]
          rw [isOpen_iff_mem_nhds]
          intro u hu
          obtain ⟨hu1, hu2⟩ := hu
          have hmemc : u ∈ Kc := by
            refine hKc_sub (k + 1) (by omega) (by omega) ?_
            rw [Metric.mem_closedBall]
            have h1 : dist u (z (k + 1)) < Rb k / 2 := by
              have := Metric.mem_ball.mp hu2
              first | exact this | (rwa [dist_eq_norm] at this) | simpa [dist_eq_norm] using this
            have h2 : Rb k / 2 ≤ Rm (k + 1) := by
              have h3 := hRb_le k hk'
              linarith [(hRb_pos k hk').le]
            calc dist u (z (k + 1)) ≤ Rb k / 2 := h1.le
              _ ≤ Rm (k + 1) := h2
              _ ≤ r := (hRm (k + 1) (by omega) (by omega)).2.1
              _ ≤ 2 * r := by linarith
          have hcont : ContinuousAt G u :=
            ((hRdiff.differentiableAt (hDR.mem_nhds (hDRsub' hmemc))).sub_const β).continuousAt
          exact Filter.inter_mem (hcont.preimage_mem_nhds (hopen.mem_nhds hu1))
            (Metric.isOpen_ball.mem_nhds hu2)
        · rw [e1]
          exact IsConnected.image hconn _ (((hχ k hk').1).continuousOn.mono hdomk)
        · exact (Metric.isBounded_ball (x := z (k + 1)) (r := Δ (k + 1))).subset e2
    -- (g) the chain relations
    have hchain : ∀ n, n < j₀ → InjOn G (W (n + 1)) ∧ G '' W (n + 1) = W n ∧
        W (n + 1) ⊆ Metric.ball (z (n + 1)) r ∧ Bornology.IsBounded (W (n + 1)) := by
      intro n hn
      obtain ⟨-, -, e2, e3, e4⟩ := hstep n hn (hall n (le_of_lt hn)).1
      have e2' : W (n + 1) ⊆ Metric.ball (z (n + 1)) (Rb n / 2) := by
        rw [hΔ_succ n] at e2; exact e2
      have hr : Rb n / 2 ≤ r := by
        have h1 := hRb_le n hn
        have h2 := (hRm (n + 1) (by omega) (by omega)).2.1
        linarith [(hRb_pos n hn).le]
      exact ⟨e3, e4, e2'.trans (Metric.ball_subset_ball (x := z (n + 1)) hr),
        (Metric.isBounded_ball (x := z (n + 1)) (r := Rb n / 2)).subset e2'⟩
    -- (h) the derivative bounds
    have hderiv_pt : ∀ n (hn : n < j₀), ∀ w ∈ Metric.ball (z (n + 1)) (Rb n),
        3 * amin / 4 ≤ ‖deriv G w‖ ∧ ‖deriv G w‖ ≤ 5 * amax / 4 := by
      intro n hn w hw
      have h1 := huniv n hn w hw
      have hnorm : ‖deriv d.E (z (n + 1))‖ = AN (n + 1) := rfl
      constructor
      · have hh : ‖deriv d.E (z (n + 1))‖ - ‖deriv G w‖
            ≤ ‖deriv G w - deriv d.E (z (n + 1))‖ := by
          have h2 : ‖deriv d.E (z (n + 1))‖ - ‖deriv G w‖
              ≤ ‖deriv d.E (z (n + 1)) - deriv G w‖ :=
            (abs_le.mp (abs_norm_sub_norm_le (deriv d.E (z (n + 1))) (deriv G w))).2
          rwa [norm_sub_rev] at h2
        rw [hnorm] at hh
        have := hamin_le (n + 1) (by omega) (by omega)
        linarith
      · have hh : ‖deriv G w‖ - ‖deriv d.E (z (n + 1))‖
            ≤ ‖deriv G w - deriv d.E (z (n + 1))‖ :=
          (abs_le.mp (abs_norm_sub_norm_le (deriv G w) (deriv d.E (z (n + 1))))).2
        rw [hnorm] at hh
        have := hA_le_amax (n + 1) (by omega) (by omega)
        linarith
    have horbit : ∀ n (hn : n < j₀), ∀ u ∈ W (n + 1), ∀ i ≤ n + 1,
        (G^[i]) u ∈ W (n + 1 - i) := by
      intro n hn u hu i
      induction i with
      | zero => intro _; simpa using hu
      | succ k ih =>
        intro hk
        have hmem : (G^[k]) u ∈ W (n + 1 - k) := ih (by omega)
        rw [show n + 1 - k = n - k + 1 from by omega] at hmem
        have hrel : G '' W (n - k + 1) = W (n - k) :=
          (hstep (n - k) (by omega) (hall (n - k) (by omega)).1).2.2.2.2
        have himg : G ((G^[k]) u) ∈ G '' W (n - k + 1) := ⟨_, hmem, rfl⟩
        rw [hrel] at himg
        rw [Function.iterate_succ_apply']
        simpa [show n + 1 - (k + 1) = n - k from by omega] using himg
    have hfinal : ∀ n (hn : n < j₀), ∀ u ∈ W (n + 1),
        C < ‖deriv (G^[n + 1]) u‖ ∧ ‖deriv (G^[n + 1]) u‖ < C' := by
      intro n hn u hu
      have hmemK : ∀ i < n + 1, (G^[i]) u ∈ Kc := by
        intro i hi
        have hm := horbit n hn u hu i hi.le
        have hl := (hall (n + 1 - i) (by omega)).1 hm
        have h1 : Δ (n + 1 - i) = Rb (n - i) / 2 := by
          rw [show n + 1 - i = (n - i) + 1 from by omega, hΔ_succ]
        rw [h1] at hl
        have h2 : z (n + 1 - i) = z (n - i + 1) := by congr 1; omega
        rw [h2] at hl
        refine hKc_sub (n - i + 1) (by omega) (by omega) ?_
        rw [Metric.mem_closedBall]
        have hb : dist ((G^[i]) u) (z (n - i + 1)) < Rb (n - i) / 2 := by
          have := Metric.mem_ball.mp hl
          first | exact this | (rwa [dist_eq_norm] at this) | simpa [dist_eq_norm] using this
        have h3 : Rb (n - i) / 2 ≤ Rm (n - i + 1) := by
          have h4 := hRb_le (n - i) (by omega)
          linarith [(hRb_pos (n - i) (by omega)).le]
        calc dist ((G^[i]) u) (z (n - i + 1)) ≤ Rb (n - i) / 2 := hb.le
          _ ≤ Rm (n - i + 1) := h3
          _ ≤ r := (hRm (n - i + 1) (by omega) (by omega)).2.1
          _ ≤ 2 * r := by linarith
      have hdiff_all : ∀ i < n + 1, DifferentiableAt ℂ G ((G^[i]) u) := fun i hi =>
        ((hRdiff.differentiableAt (hDR.mem_nhds (hDRsub' (hmemK i hi)))).sub_const β)
      have hfact : ∀ i ∈ Finset.range (n + 1), 3 * amin / 4 ≤ ‖deriv G ((G^[i]) u)‖ ∧
          ‖deriv G ((G^[i]) u)‖ ≤ 5 * amax / 4 := by
        intro i hi
        have hi' : i < n + 1 := Finset.mem_range.mp hi
        have hm := horbit n hn u hu i hi'.le
        have hl := (hall (n + 1 - i) (by omega)).1 hm
        have h1 : Δ (n + 1 - i) = Rb (n - i) / 2 := by
          rw [show n + 1 - i = (n - i) + 1 from by omega, hΔ_succ]
        rw [h1] at hl
        have h2 : z (n + 1 - i) = z (n - i + 1) := by congr 1; omega
        rw [h2] at hl
        refine hderiv_pt (n - i) (by omega) _ ?_
        rw [Metric.mem_ball]
        have hb : dist ((G^[i]) u) (z (n - i + 1)) < Rb (n - i) / 2 := by
          have := Metric.mem_ball.mp hl
          first | exact this | (rwa [dist_eq_norm] at this) | simpa [dist_eq_norm] using this
        calc dist ((G^[i]) u) (z (n - i + 1)) < Rb (n - i) / 2 := hb
          _ ≤ Rb (n - i) := by linarith [(hRb_pos (n - i) (by omega)).le]
      rw [deriv_iterate_prod hdiff_all, norm_prod]
      constructor
      · have hlow : (3 * amin / 4) ^ (n + 1)
            ≤ ∏ i ∈ Finset.range (n + 1), ‖deriv G ((G^[i]) u)‖ := by
          have h1 : (∏ _ ∈ Finset.range (n + 1), 3 * amin / 4) = (3 * amin / 4) ^ (n + 1) := by
            simp only [Finset.prod_const, Finset.card_range]
          rw [← h1]
          exact Finset.prod_le_prod₀ (fun i hi => by positivity) (fun i hi => (hfact i hi).1)
        refine lt_of_lt_of_le ?_ hlow
        rcases lt_or_ge c_lo 1 with hcl | hcl
        · have h1 : c_lo / 2 < c_lo := by linarith [hc_lo_pos]
          have h2 : (c_lo / 2) ^ j₀ ≤ (c_lo / 2) ^ (n + 1) :=
            pow_le_pow_of_le_one (by linarith [hc_lo_pos]) (by linarith) (by omega)
          have h3 : (c_lo / 2) ^ (n + 1) < c_lo ^ (n + 1) :=
            pow_lt_pow_left₀ h1 (by linarith [hc_lo_pos]) (by omega)
          calc C = (min c_lo 1 / 2) ^ j₀ := rfl
            _ = (c_lo / 2) ^ j₀ := by rw [min_eq_left hcl.le]
            _ < c_lo ^ (n + 1) := lt_of_le_of_lt h2 h3
        · have h1 : (1 : ℝ) ≤ c_lo := hcl
          calc C = (min c_lo 1 / 2) ^ j₀ := rfl
            _ = ((1 : ℝ) / 2) ^ j₀ := by rw [min_eq_right hcl]
            _ < 1 := pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
            _ ≤ c_lo ^ (n + 1) := one_le_pow₀ h1
      · have hhigh : ∏ i ∈ Finset.range (n + 1), ‖deriv G ((G^[i]) u)‖
            ≤ (5 * amax / 4) ^ (n + 1) := by
          have h1 : (∏ _ ∈ Finset.range (n + 1), 5 * amax / 4) = (5 * amax / 4) ^ (n + 1) := by
            simp only [Finset.prod_const, Finset.card_range]
          rw [← h1]
          exact Finset.prod_le_prod₀ (fun i hi => norm_nonneg _) (fun i hi => (hfact i hi).2)
        refine lt_of_le_of_lt hhigh ?_
        have h1 : c_hi ^ (n + 1) ≤ (max c_hi 1) ^ j₀ := by
          have h2 : c_hi ^ (n + 1) ≤ (max c_hi 1) ^ (n + 1) :=
            pow_le_pow_left₀ hc_hi_pos.le (le_max_left _ _) _
          have h3 : (max c_hi 1) ^ (n + 1) ≤ (max c_hi 1) ^ j₀ :=
            pow_le_pow_right₀ (le_max_right c_hi 1) (by omega)
          exact le_trans h2 h3
        have h4 : (max c_hi 1) ^ j₀ < (2 * max c_hi 1) ^ j₀ := by
          have h5 : (0 : ℝ) < max c_hi 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
          exact pow_lt_pow_left₀ (by linarith) h5.le (by omega)
        calc (5 * amax / 4) ^ (n + 1) = c_hi ^ (n + 1) := by simp only [c_hi]
          _ ≤ (max c_hi 1) ^ j₀ := h1
          _ < (2 * max c_hi 1) ^ j₀ := h4
          _ = C' := rfl
    -- (i) conclusion
    refine ⟨W, hW0, fun j hj => ?_⟩
    obtain ⟨hinj, himg, hsub, hbdd⟩ := hchain j hj
    exact ⟨hsub, (hall (j + 1) (by omega)).2.1, (hall (j + 1) (by omega)).2.2.1,
      (hall (j + 1) (by omega)).2.2.2, hinj, himg, fun u hu => hfinal j hj u hu⟩

end

end Work.L62
