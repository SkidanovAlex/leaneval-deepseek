import Mathlib
import Submission.CDTPlan.Interfaces
import Submission.Work.OdeCont.uniqueness
import Submission.Work.OdeCont.circle_midpoint
import Submission.Work.OdeCont.collar_covered
import Submission.Work.OdeCont.glue_two
import Submission.Work.OdeCont.glue_seq
import Submission.Work.OdeCont.local_existence

/-!
# Area K1 — ODE continuation on the disc (`Submission.CDTPlan.OdeContinuation`)

`Work.OdeCont.ode_continuation : Submission.CDTPlan.OdeContinuation` states: if `A, b` are
holomorphic on the annulus `r₀ < ‖z‖ < 1` and `Y₀` is holomorphic on the disc `ball 0 r₁`
(`r₀ < r₁ ≤ 1`) and solves the linear system `Y' = A(z)Y + b(z)` on the annulus
`r₀ < ‖z‖ < r₁`, then `Y₀` extends holomorphically to the whole unit disc.

## Strategy

The mathematical content is the classical continuation theorem for linear systems, made
elementary (no monodromy theory).  The supporting lemmas live in sibling modules:

* `local_existence` : on a disc where `A, b` are holomorphic, every initial datum at an interior
  point has a holomorphic solution on the whole disc (Picard iteration);
* `uniqueness` : two solutions agreeing at a point of a preconnected open set agree there;
* `circle_midpoint`, `collar_covered` : the elementary geometry of the discs used to cover a
  circle by discs centred at the `N`-th roots of unity;
* `glue_two`, `glue_seq` : gluing holomorphic functions out of open covers / increasing annuli.

The extension itself is a maximality argument in the radius `τ`: if a solution is known on
`r₀ < ‖z‖ < τ` with `τ < 1`, cover the circle `‖z‖ = τ` by small discs, build a local solution
on each disc pinned to the known solution on the inner lens (uniqueness), check that overlapping
discs give the same solution (their midpoint lies in the lens and is `circle_midpoint`), and
glue.  This extends the solution strictly past `τ`.  Taking the supremum of the admissible radii
and gluing the resulting sequence (`glue_seq`) yields a solution on the whole annulus; gluing
with `Y₀` on `ball 0 r₁` (`glue_two`) finishes.
-/

open Complex Metric Filter Topology
open scoped BigOperators

open Submission.CDTPlan

namespace Work.OdeCont

/-- The open annulus `r < ‖z‖ < s`. -/
def annulus (r s : ℝ) : Set ℂ := {z : ℂ | r < ‖z‖ ∧ ‖z‖ < s}

/-- `Y` is holomorphic on `U` and solves `Y' = A(z)Y + b(z)` there. -/
def IsSol {k : ℕ} (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ) (Y : ℂ → Fin k → ℂ)
    (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ Y U ∧ ∀ z ∈ U, HasDerivAt Y (fun i => ∑ j, A z i j * Y z j + b z i) z

lemma isOpen_annulus (r s : ℝ) : IsOpen (annulus r s) := by
  have h1 : IsOpen {z : ℂ | r < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have h2 : IsOpen {z : ℂ | ‖z‖ < s} := isOpen_lt continuous_norm continuous_const
  have h3 : annulus r s = {z : ℂ | r < ‖z‖} ∩ {z : ℂ | ‖z‖ < s} := rfl
  rw [h3]; exact h1.inter h2

lemma annulus_mono {r s t : ℝ} (h : s ≤ t) : annulus r s ⊆ annulus r t :=
  fun _ hz => ⟨hz.1, lt_of_lt_of_le hz.2 h⟩

lemma annulus_empty_of_le {r s : ℝ} (h : s ≤ r) : annulus r s = ∅ := by
  ext z
  simp only [annulus, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun h1 h2 => absurd (lt_trans h1 h2) (not_lt.mpr h)

lemma mem_ball_zero_iff {r : ℝ} {z : ℂ} : z ∈ ball (0 : ℂ) r ↔ ‖z‖ < r := by
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]

/-- The annulus `r < ‖z‖ < s` is preconnected when `0 < r`. -/
lemma isPreconnected_annulus {r s : ℝ} (h : 0 < r) : IsPreconnected (annulus r s) := by
  rcases le_or_gt s r with hs | hs
  · rw [annulus_empty_of_le hs]; exact isPreconnected_empty
  · have hstrip : Convex ℝ {w : ℂ | Real.log r < w.re ∧ w.re < Real.log s} :=
      (convex_halfSpace_re_gt (Real.log r)).inter (convex_halfSpace_re_lt (Real.log s))
    have himg : annulus r s = Complex.exp '' {w : ℂ | Real.log r < w.re ∧ w.re < Real.log s} := by
      ext z
      constructor
      · intro hz
        change r < ‖z‖ ∧ ‖z‖ < s at hz
        obtain ⟨h1, h2⟩ := hz
        refine ⟨Complex.log z, ⟨?_, ?_⟩, Complex.exp_log ?_⟩
        · rw [Complex.log_re]; exact Real.log_lt_log h h1
        · rw [Complex.log_re]; exact Real.log_lt_log (lt_trans h h1) h2
        · intro hz0
          rw [hz0, norm_zero] at h1
          linarith
      · rintro ⟨w, ⟨hw1, hw2⟩, rfl⟩
        change r < ‖Complex.exp w‖ ∧ ‖Complex.exp w‖ < s
        rw [Complex.norm_exp]
        exact ⟨by rw [← Real.exp_log h]; exact Real.exp_lt_exp.mpr hw1,
          by rw [← Real.exp_log (lt_trans h hs)]; exact Real.exp_lt_exp.mpr hw2⟩
    rw [himg]
    exact hstrip.isPreconnected.image _ Complex.continuous_exp.continuousOn

/-- Two solutions of the system on an open annulus which agree with a common function on the
inner annulus `r₀ < ‖z‖ < r₁` agree on the whole annulus. -/
lemma eqOn_of_eqOn_inner {k : ℕ} {r0 r1 τ : ℝ} (h0 : 0 < r0) (h1 : r0 < r1) (h12 : r1 ≤ τ)
    {Y Y' Y0 : ℂ → Fin k → ℂ} (hY : DifferentiableOn ℂ Y (annulus r0 τ))
    (hY' : DifferentiableOn ℂ Y' (annulus r0 τ))
    (h : Set.EqOn Y Y0 (annulus r0 r1)) (h' : Set.EqOn Y' Y0 (annulus r0 r1)) :
    Set.EqOn Y Y' (annulus r0 τ) := by
  have hz₀ : (((r0 + r1) / 2 : ℝ) : ℂ) ∈ annulus r0 r1 := by
    have hpos : (0 : ℝ) < (r0 + r1) / 2 := by linarith
    have hnorm : ‖(((r0 + r1) / 2 : ℝ) : ℂ)‖ = (r0 + r1) / 2 := Complex.norm_of_nonneg hpos.le
    change r0 < ‖(((r0 + r1) / 2 : ℝ) : ℂ)‖ ∧ ‖(((r0 + r1) / 2 : ℝ) : ℂ)‖ < r1
    rw [hnorm]; exact ⟨by linarith, by linarith⟩
  refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hY.analyticOnNhd (isOpen_annulus _ _)) (hY'.analyticOnNhd (isOpen_annulus _ _))
    (isPreconnected_annulus h0) (annulus_mono h12 hz₀) ?_
  filter_upwards [(isOpen_annulus r0 r1).mem_nhds hz₀] with w hw
  exact (h hw).trans (h' hw).symm

/-! ## The supporting lemmas (proved in sibling modules) -/







/-! ## One continuation step -/

/-- One step of the continuation: a solution known on the annulus `r₀ < ‖z‖ < τ` with `τ < 1`
extends strictly past `τ`. -/
lemma step {k : ℕ} (A : ℂ → Fin k → Fin k → ℂ) (b : ℂ → Fin k → ℂ) {r0 r1 : ℝ}
    (h0 : 0 < r0) (h01 : r0 < r1)
    (hA : ∀ i j : Fin k, DifferentiableOn ℂ (fun z : ℂ => A z i j) (annulus r0 1))
    (hb : ∀ i : Fin k, DifferentiableOn ℂ (fun z : ℂ => b z i) (annulus r0 1))
    {Y0 : ℂ → Fin k → ℂ} {τ : ℝ} (h1τ : r1 ≤ τ) (hτ1 : τ < 1)
    {Y : ℂ → Fin k → ℂ} (hY : IsSol A b Y (annulus r0 τ))
    (hY0 : Set.EqOn Y Y0 (annulus r0 r1)) :
    ∃ τ' : ℝ, τ < τ' ∧ τ' ≤ 1 ∧ ∃ Y' : ℂ → Fin k → ℂ,
      IsSol A b Y' (annulus r0 τ') ∧ Set.EqOn Y' Y0 (annulus r0 r1) := by
  classical
  have hτpos : 0 < τ := lt_of_lt_of_le h0 (le_trans h01.le h1τ)
  set δ : ℝ := min (τ - r0) (1 - τ) / 4 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  have hδ_τ : δ < τ - r0 := by
    have h : δ ≤ (τ - r0) / 4 := by
      rw [hδdef]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    linarith
  have hδ_1 : δ < 1 - τ := by
    have h : δ ≤ (1 - τ) / 4 := by
      rw [hδdef]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    linarith
  obtain ⟨N, hNpos, hNbig⟩ : ∃ N : ℕ, 0 < N ∧ 2 * τ * Real.pi / N < δ := by
    obtain ⟨M, hM⟩ := exists_nat_gt (2 * τ * Real.pi / δ)
    refine ⟨M + 1, Nat.succ_pos M, ?_⟩
    have hM' : 2 * τ * Real.pi < (M : ℝ) * δ := (div_lt_iff₀ hδpos).mp hM
    have hM1 : (0 : ℝ) < ((M + 1 : ℕ) : ℝ) := by positivity
    rw [div_lt_iff₀ hM1]
    push_cast
    nlinarith [hM', hδpos]
  have hτπ : τ * Real.pi / N < δ / 2 := by
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
    have h2 : 2 * τ * Real.pi < δ * N := (div_lt_iff₀ hN).mp hNbig
    rw [div_lt_iff₀ hN]
    nlinarith [h2]
  set ε : ℝ := δ / 2 with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; linarith
  have hcov_hyp : ε + τ * Real.pi / N < δ := by rw [hεdef]; linarith
  set zc : Fin N → ℂ := fun j =>
    (τ : ℂ) * Complex.exp (2 * Real.pi * Complex.I * ((j : ℕ) : ℂ) / (N : ℂ)) with hzcdef
  have hzc_re (j : Fin N) : (2 * Real.pi * Complex.I * ((j : ℕ) : ℂ) / (N : ℂ)).re = 0 := by
    have h1 : 2 * Real.pi * Complex.I * ((j : ℕ) : ℂ) / (N : ℂ)
        = (((2 * Real.pi * (j : ℕ) / N : ℝ)) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [h1, Complex.mul_I_re]
    simp
  have hzc_norm (j : Fin N) : ‖zc j‖ = τ := by
    rw [hzcdef, norm_mul, Complex.norm_exp, hzc_re, Real.exp_zero, mul_one,
      Complex.norm_of_nonneg hτpos.le]
  set zp : Fin N → ℂ := fun j => ((1 - δ / (2 * τ) : ℝ) : ℂ) * zc j with hzpdef
  have hzp_factor : (0 : ℝ) ≤ 1 - δ / (2 * τ) := by
    have h : δ / (2 * τ) < 1 := by
      rw [div_lt_one (by positivity : (0 : ℝ) < 2 * τ)]
      linarith
    linarith
  have hzp_norm (j : Fin N) : ‖zp j‖ = τ - δ / 2 := by
    rw [hzpdef, norm_mul, Complex.norm_of_nonneg hzp_factor, hzc_norm]
    field_simp
  have hzp_ball (j : Fin N) : zp j ∈ ball (zc j) δ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have hsub : zp j - zc j = ((δ / (2 * τ) : ℝ) : ℂ) * (-zc j) := by
      rw [hzpdef]; push_cast; ring
    rw [hsub, norm_mul, norm_neg, Complex.norm_of_nonneg (by positivity), hzc_norm]
    have h2 : δ / (2 * τ) * τ = δ / 2 := by field_simp
    rw [h2]; linarith
  have hzp_ann (j : Fin N) : zp j ∈ annulus r0 τ := by
    have h1 := hzp_norm j
    exact ⟨by linarith [hδ_τ], by linarith⟩
  have hball_sub (j : Fin N) : ball (zc j) δ ⊆ annulus r0 1 := by
    intro z hz
    have hd : ‖zc j - z‖ < δ := by
      rw [Metric.mem_ball, dist_eq_norm] at hz
      rwa [norm_sub_rev] at hz
    constructor
    · have h := norm_sub_norm_le (zc j) z
      rw [hzc_norm] at h
      linarith
    · have h : ‖z‖ ≤ ‖z - zc j‖ + ‖zc j‖ := by
        have h1 : (z - zc j) + zc j = z := by ring
        calc ‖z‖ = ‖(z - zc j) + zc j‖ := by rw [h1]
          _ ≤ ‖z - zc j‖ + ‖zc j‖ := norm_add_le _ _
      have hrev : ‖z - zc j‖ = ‖zc j - z‖ := norm_sub_rev z (zc j)
      rw [hzc_norm, hrev] at h
      linarith
  have hsol : ∀ j : Fin N, ∃ G : ℂ → Fin k → ℂ,
      DifferentiableOn ℂ G (ball (zc j) δ) ∧ G (zp j) = Y (zp j) ∧
      ∀ z ∈ ball (zc j) δ,
        HasDerivAt G (fun i => (Finset.univ.sum (fun l => A z i l * G z l)) + b z i) z :=
    fun j => local_existence A b (zc j) (zp j) δ hδpos (hzp_ball j)
      (fun i l => (hA i l).mono (hball_sub j)) (fun i => (hb i).mono (hball_sub j)) (Y (zp j))
  choose g hg_diff hg_val hg_sol using hsol
  have hglens : ∀ j : Fin N, Set.EqOn (g j) Y (ball (zc j) δ ∩ annulus r0 τ) := by
    intro j
    have hset : ball (zc j) δ ∩ annulus r0 τ = ball (zc j) δ ∩ ball (0 : ℂ) τ := by
      ext z
      constructor
      · intro hz
        exact ⟨hz.1, (mem_ball_zero_iff).mpr hz.2.2⟩
      · intro hz
        exact ⟨hz.1, ⟨(hball_sub j hz.1).1, (mem_ball_zero_iff).mp hz.2⟩⟩
    rw [hset]
    refine uniqueness (Metric.isOpen_ball.inter Metric.isOpen_ball)
      ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected A b
      (fun i l => (hA i l).mono ?_) (fun i => (hb i).mono ?_)
      (g j) Y ((hg_diff j).mono (fun z hz => hz.1)) (hY.1.mono ?_)
      (fun z hz => hg_sol j z hz.1)
      (fun z hz => hY.2 z ⟨(hball_sub j hz.1).1, mem_ball_zero_iff.mp hz.2⟩)
      ⟨hzp_ball j, mem_ball_zero_iff.mpr (hzp_ann j).2⟩ (hg_val j)
    · exact fun z hz => hball_sub j hz.1
    · exact fun z hz => hball_sub j hz.1
    · exact fun z hz => ⟨(hball_sub j hz.1).1, mem_ball_zero_iff.mp hz.2⟩
  have hpair : ∀ j j' : Fin N, Set.EqOn (g j) (g j') (ball (zc j) δ ∩ ball (zc j') δ) := by
    intro j j'
    by_cases hjj : j = j'
    · subst hjj; intro z _; rfl
    · by_cases hI : (ball (zc j) δ ∩ ball (zc j') δ).Nonempty
      · by_cases heq : zc j = zc j'
        · have hball : ball (zc j) δ = ball (zc j') δ := by rw [heq]
          have hEq : Set.EqOn (g j) (g j') (ball (zc j) δ) := by
            refine uniqueness Metric.isOpen_ball (convex_ball _ _).isPreconnected A b
              (fun i l => (hA i l).mono (hball_sub j)) (fun i => (hb i).mono (hball_sub j))
              (g j) (g j') (hg_diff j) ?_ (hg_sol j) ?_ (hzp_ball j) ?_
            · rw [hball]; exact hg_diff j'
            · rw [hball]; exact hg_sol j'
            · rw [hg_val j]
              exact (hglens j' ⟨by rw [← hball]; exact hzp_ball j,
                (hzp_ann j).1, (hzp_ann j).2⟩).symm
          intro z hz; exact hEq hz.1
        · obtain ⟨z, hz⟩ := hI
          have hz1 : dist z (zc j) < δ := hz.1
          have hz2 : dist z (zc j') < δ := hz.2
          have hd1 : ‖zc j - z‖ < δ := by
            rw [dist_eq_norm] at hz1
            rwa [norm_sub_rev] at hz1
          have hd2 : ‖z - zc j'‖ < δ := by rw [dist_eq_norm] at hz2; exact hz2
          have hzd : ‖zc j - zc j'‖ < 2 * δ := by
            have h1 : (zc j - z) + (z - zc j') = zc j - zc j' := by ring
            rw [← h1]
            calc ‖(zc j - z) + (z - zc j')‖ ≤ ‖zc j - z‖ + ‖z - zc j'‖ := norm_add_le _ _
              _ < δ + δ := add_lt_add hd1 hd2
              _ = 2 * δ := by ring
          obtain ⟨hm1, hm2, hm3, hm4⟩ :=
            circle_midpoint hτpos hδpos hδ_τ (hzc_norm j) (hzc_norm j') heq hzd
          have hm1' : (zc j + zc j') / 2 ∈ ball (zc j) δ := by
            rw [Metric.mem_ball, Complex.dist_eq]; exact hm1
          have hm2' : (zc j + zc j') / 2 ∈ ball (zc j') δ := by
            rw [Metric.mem_ball, Complex.dist_eq]; exact hm2
          have hagree : g j ((zc j + zc j') / 2) = g j' ((zc j + zc j') / 2) := by
            rw [hglens j ⟨hm1', hm3, hm4⟩, hglens j' ⟨hm2', hm3, hm4⟩]
          refine uniqueness (Metric.isOpen_ball.inter Metric.isOpen_ball)
            ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected A b
            (fun i l => (hA i l).mono ?_) (fun i => (hb i).mono ?_)
            (g j) (g j')
            ((hg_diff j).mono (fun z hz => hz.1)) ((hg_diff j').mono (fun z hz => hz.2))
            (fun z hz => hg_sol j z hz.1) (fun z hz => hg_sol j' z hz.2)
            ⟨hm1', hm2'⟩ hagree
          · exact fun z hz => hball_sub j hz.1
          · exact fun z hz => hball_sub j hz.1
      · intro z hz; exact absurd ⟨z, hz⟩ hI
  let τ' : ℝ := min (τ + ε) 1
  have hττ' : τ < τ' := lt_min (by linarith) hτ1
  have hτ'1 : τ' ≤ 1 := min_le_right _ _
  have hcover : ∀ z : ℂ, z ∈ annulus r0 τ' →
      z ∈ annulus r0 τ ∨ ∃ j : Fin N, z ∈ ball (zc j) δ := by
    intro z hz
    change r0 < ‖z‖ ∧ ‖z‖ < τ' at hz
    by_cases h : ‖z‖ < τ
    · exact Or.inl ⟨hz.1, h⟩
    · refine Or.inr ?_
      have h1 : τ ≤ ‖z‖ := not_lt.mp h
      have h2 : ‖z‖ ≤ τ + ε := by
        have h3 : τ' ≤ τ + ε := min_le_left _ _
        linarith
      obtain ⟨k, hk⟩ := collar_covered hNpos hτpos hεpos.le hcov_hyp z h1 h2
      exact ⟨k, by rw [Metric.mem_ball, Complex.dist_eq, hzcdef]; exact hk⟩
  let Ynew : ℂ → Fin k → ℂ := fun z =>
    if z ∈ annulus r0 τ then Y z
    else if h : ∃ j : Fin N, z ∈ ball (zc j) δ then g h.choose z else 0
  have hYnew_ann : Set.EqOn Ynew Y (annulus r0 τ) := by
    intro z hz
    simp only [Ynew]
    rw [if_pos hz]
  have hYnew_ball : ∀ j : Fin N, Set.EqOn Ynew (g j) (ball (zc j) δ) := by
    intro j z hz
    by_cases hzτ : z ∈ annulus r0 τ
    · have h1 : Ynew z = Y z := by
        simp only [Ynew]; rw [if_pos hzτ]
      rw [h1]
      exact (hglens j ⟨hz, hzτ⟩).symm
    · have hex : ∃ j' : Fin N, z ∈ ball (zc j') δ := ⟨j, hz⟩
      have h1 : Ynew z = g hex.choose z := by
        simp only [Ynew]; rw [if_neg hzτ, dif_pos hex]
      rw [h1]
      exact hpair hex.choose j ⟨Classical.choose_spec hex, hz⟩
  have hYnew_deriv : ∀ z ∈ annulus r0 τ', HasDerivAt Ynew
      (fun i => ∑ l, A z i l * Ynew z l + b z i) z := by
    intro z hz
    rcases hcover z hz with hzτ | ⟨j, hj⟩
    · have hz_eq : Ynew z = Y z := hYnew_ann hzτ
      have hfun : (fun i => (Finset.univ.sum (fun l => A z i l * Ynew z l)) + b z i)
          = (fun i => (Finset.univ.sum (fun l => A z i l * Y z l)) + b z i) := by
        funext i; rw [hz_eq]
      rw [hfun]
      exact (hY.2 z hzτ).congr_of_eventuallyEq
        (hYnew_ann.eventuallyEq_of_mem ((isOpen_annulus r0 τ).mem_nhds hzτ))
    · have hz_eq : Ynew z = g j z := hYnew_ball j hj
      have hfun : (fun i => (Finset.univ.sum (fun l => A z i l * Ynew z l)) + b z i)
          = (fun i => (Finset.univ.sum (fun l => A z i l * g j z l)) + b z i) := by
        funext i; rw [hz_eq]
      rw [hfun]
      exact (hg_sol j z hj).congr_of_eventuallyEq
        ((hYnew_ball j).eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hj))
  have hYnew_diff : DifferentiableOn ℂ Ynew (annulus r0 τ') := by
    intro z hz
    rcases hcover z hz with hzτ | ⟨j, hj⟩
    · exact ((hY.1.differentiableAt ((isOpen_annulus r0 τ).mem_nhds hzτ)).congr_of_eventuallyEq
        (hYnew_ann.eventuallyEq_of_mem ((isOpen_annulus r0 τ).mem_nhds hzτ))).differentiableWithinAt
    · exact ((hg_diff j).differentiableAt (Metric.isOpen_ball.mem_nhds hj) |>.congr_of_eventuallyEq
        ((hYnew_ball j).eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds hj))).differentiableWithinAt
  have hYnew_eq0 : Set.EqOn Ynew Y0 (annulus r0 r1) := by
    intro z hz
    have hzτ : z ∈ annulus r0 τ := ⟨hz.1, lt_of_lt_of_le hz.2 h1τ⟩
    rw [hYnew_ann hzτ]
    exact hY0 hz
  exact ⟨τ', hττ', hτ'1, Ynew, ⟨hYnew_diff, hYnew_deriv⟩, hYnew_eq0⟩

/-! ## The main theorem -/

/-- **ODE continuation on the disc** (`Submission.CDTPlan.OdeContinuation`). -/
theorem ode_continuation : OdeContinuation := by
  intro k A b r0 r1 Y0 h0 hr01 hr11 hA hb hY0 hY0'
  classical
  have hAij : ∀ i j : Fin k, DifferentiableOn ℂ (fun z : ℂ => A z i j) (annulus r0 1) :=
    fun i j => differentiableOn_pi.mp (differentiableOn_pi.mp hA i) j
  have hbi : ∀ i : Fin k, DifferentiableOn ℂ (fun z : ℂ => b z i) (annulus r0 1) :=
    fun i => differentiableOn_pi.mp hb i
  let P : ℝ → Prop := fun τ => r1 ≤ τ ∧ τ ≤ 1 ∧ ∃ Y : ℂ → Fin k → ℂ,
      IsSol A b Y (annulus r0 τ) ∧ Set.EqOn Y Y0 (annulus r0 r1)
  have hP1 : P r1 := by
    refine ⟨le_refl _, hr11, Y0, ⟨⟨?_, ?_⟩, fun z _ => rfl⟩⟩
    · refine hY0.mono (fun z hz => ?_)
      rw [mem_ball_zero_iff]
      exact hz.2
    · intro z hz
      exact hY0' z hz.1 hz.2
  have hbdd : BddAbove {τ : ℝ | P τ} := ⟨1, fun τ hτ => hτ.2.1⟩
  set σ : ℝ := sSup {τ : ℝ | P τ} with hσdef
  have hσub : ∀ τ, P τ → τ ≤ σ := fun τ hτ => le_csSup hbdd hτ
  have hσge : r1 ≤ σ := hσub r1 hP1
  have hσle : σ ≤ 1 := csSup_le ⟨r1, hP1⟩ (fun τ hτ => hτ.2.1)
  have hseq : ∃ τ : ℕ → ℝ, (∀ n, P (τ n)) ∧ Tendsto τ atTop (nhds σ) := by
    have hne : ({τ : ℝ | P τ}).Nonempty := ⟨r1, hP1⟩
    have hlt : ∀ n : ℕ, σ - 1 / (n + 1) < σ := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    choose τ hτP hτlt using fun n => exists_lt_of_lt_csSup hne (hlt n)
    refine ⟨τ, hτP, ?_⟩
    have hlim : Tendsto (fun n : ℕ => σ - 1 / ((n : ℝ) + 1)) atTop (nhds σ) := by
      have h1 : Tendsto (fun _ : ℕ => σ) atTop (nhds σ) := tendsto_const_nhds
      have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using h1.sub h2
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds
      (fun n => (hτlt n).le) (fun n => hσub (τ n) (hτP n))
  obtain ⟨τ, hτP, hτlim⟩ := hseq
  choose Yn hYn_sol hYn_eq using fun n => (hτP n).2.2
  have hagree : ∀ n m, Set.EqOn (Yn n) (Yn m)
      {z : ℂ | r0 < ‖z‖ ∧ ‖z‖ < min (τ n) (τ m)} := by
    intro n m
    refine eqOn_of_eqOn_inner h0 hr01 (le_min (hτP n).1 (hτP m).1) ?_ ?_ (hYn_eq n) (hYn_eq m)
    · exact (hYn_sol n).1.mono (annulus_mono (min_le_left _ _))
    · exact (hYn_sol m).1.mono (annulus_mono (min_le_right _ _))
  obtain ⟨Yσ, hYσ_diff, hYσ_eq⟩ := glue_seq (r0 := r0)
    (fun n => lt_of_lt_of_le hr01 (hτP n).1)
    (fun n => hσub (τ n) (hτP n)) hτlim Yn (fun n => (hYn_sol n).1) hagree
  have hYσ_deriv : ∀ z ∈ annulus r0 σ, HasDerivAt Yσ
      (fun i => ∑ l, A z i l * Yσ z l + b z i) z := by
    intro z hz
    change r0 < ‖z‖ ∧ ‖z‖ < σ at hz
    have hmem : {x : ℝ | ‖z‖ < x} ∈ 𝓝 σ :=
      (isOpen_lt continuous_const continuous_id).mem_nhds hz.2
    obtain ⟨n, hn⟩ := (hτlim.eventually hmem).exists
    have hzn : z ∈ annulus r0 (τ n) := ⟨hz.1, hn⟩
    have hzeq : Yσ z = Yn n z := hYσ_eq n hzn
    have hfun : (fun i => (Finset.univ.sum (fun l => A z i l * Yσ z l)) + b z i)
        = (fun i => (Finset.univ.sum (fun l => A z i l * Yn n z l)) + b z i) := by
      funext i; rw [hzeq]
    rw [hfun]
    exact ((hYn_sol n).2 z hzn).congr_of_eventuallyEq
      ((hYσ_eq n).eventuallyEq_of_mem ((isOpen_annulus r0 (τ n)).mem_nhds hzn))
  have hYσ_eq0 : Set.EqOn Yσ Y0 (annulus r0 r1) := by
    intro z hz
    change r0 < ‖z‖ ∧ ‖z‖ < r1 at hz
    have hmem : {x : ℝ | ‖z‖ < x} ∈ 𝓝 σ :=
      (isOpen_lt continuous_const continuous_id).mem_nhds (lt_of_lt_of_le hz.2 hσge)
    obtain ⟨n, hn⟩ := (hτlim.eventually hmem).exists
    rw [hYσ_eq n (show z ∈ annulus r0 (τ n) from ⟨hz.1, hn⟩)]
    exact hYn_eq n hz
  have hPσ : P σ := ⟨hσge, hσle, Yσ, ⟨hYσ_diff, hYσ_deriv⟩, hYσ_eq0⟩
  have hσ1 : σ = 1 := by
    by_contra hne
    have hlt : σ < 1 := lt_of_le_of_ne hσle hne
    obtain ⟨σ', hσ'lt, hσ'le, Y', hY'sol, hY'eq⟩ :=
      step A b h0 hr01 hAij hbi (Y0 := Y0) (τ := σ) (Y := Yσ) hσge hlt
        ⟨hYσ_diff, hYσ_deriv⟩ hYσ_eq0
    exact absurd (hσub σ' ⟨hσge.trans hσ'lt.le, hσ'le, Y', hY'sol, hY'eq⟩) (not_le.mpr hσ'lt)
  have h1P : P 1 := hσ1 ▸ hPσ
  obtain ⟨Y1, hY1_sol, hY1_eq⟩ := h1P.2.2
  have hunion : ball (0 : ℂ) r1 ∪ annulus r0 1 = ball 0 1 := by
    ext z
    constructor
    · rintro (hz | hz)
      · exact ball_subset_ball hr11 hz
      · rw [mem_ball_zero_iff]
        change r0 < ‖z‖ ∧ ‖z‖ < 1 at hz
        exact hz.2
    · intro hz
      rw [mem_ball_zero_iff] at hz
      by_cases h : ‖z‖ < r1
      · exact Or.inl (by rw [mem_ball_zero_iff]; exact h)
      · exact Or.inr ⟨lt_of_lt_of_le hr01 (not_lt.mp h), hz⟩
  have hagree2 : Set.EqOn Y0 Y1 (ball (0 : ℂ) r1 ∩ annulus r0 1) := by
    intro z hz
    have hz1 : ‖z‖ < r1 := mem_ball_zero_iff.mp hz.1
    exact (hY1_eq ⟨hz.2.1, hz1⟩).symm
  obtain ⟨F, hF, hF1, _⟩ := glue_two Metric.isOpen_ball (isOpen_annulus r0 1) Y0 Y1
    hY0 hY1_sol.1 hagree2
  exact ⟨F, by rw [← hunion]; exact hF, hF1⟩

end Work.OdeCont
