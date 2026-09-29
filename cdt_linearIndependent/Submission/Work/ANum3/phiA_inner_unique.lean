import Mathlib
import Submission.CDTPlan.InterfacesA
import Submission.Work.APsi.psiA_facts
import Submission.Work.Haupt.haupt_facts
import Submission.Work.ANum.psiA_deriv
import Submission.Work.ANum.psiA_deriv_le_schwarz
import Submission.Work.ANum.HLog
import Submission.Work.ANum3.hauptH_small_norm
import Submission.Work.ANum3.hauptH_norm_le_exp
import Submission.Work.ANum3.divisor_zero_pos
import Submission.Work.ANum3.exists_zero_of_norm_lt_sphere
import Submission.Work.ANum3.no_two_zeros

/-! # Z3 — exactly one zero of `φ_A + 1/72` in `|z| < 1/1000`, and it is simple

`φ_A = h ∘ ψ_A` with `h = hauptH` the `Γ₀(2)`-type hauptmodul `h(q) = -256q∏(1+qⁿ)²⁴` and `ψ_A`
the Theorem-A contour map.  Write `a = φ_A'(0)` (so `‖a‖ = 256‖ψ_A'(0)‖ ≈ 161.642`), `f = φ_A + 1/72`
and `g z = a·z + 1/72`.

The argument has two halves, both elementary (no argument principle, no Rouché, no winding
certificate):

**Existence.**  On the sphere `|z| = 1/1000` we have `‖a z‖ ≥ 0.1616`, `‖1/72‖ = 0.0139`, and the
second-order Taylor bound `‖φ_A z - a z‖ ≤ 98.77·‖z‖ ≤ 0.0988` (`phiA_taylor_bound`: the mean value
inequality `Convex.norm_image_sub_le_of_norm_deriv_le` applied twice, with the Cauchy estimate
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` for `φ_A''`), so `‖f z‖ ≥ 0.0478 > 1/30`.
As `‖f 0‖ = 1/72 < 1/30`, the minimum modulus principle for `1/f`
(`Work.ANum3.exists_zero_of_norm_lt_sphere`) produces a zero of `f` in `|z| ≤ 1/1000`; since `f` is
bounded away from `0` on the sphere, that zero lies in the open disc `|z| < 1/1000`.

**Uniqueness and simplicity.**  Here `‖f z‖ ≤ 28 + 1/72 ≤ 30 =: M` on `|z| = 1/20 =: R`
(`phiA_norm_le_20`, from the Schwarz–Pick bound `Work.ANum.psiA_deriv_le_schwarz` for `ψ_A` and the
product bound `Work.ANum3.hauptH_norm_le_exp` for the hauptmodul).  The maximum modulus principle
applied to `f(z)/((z-u)(z-v))` — holomorphic on the closed ball because the numerator vanishes there
to the appropriate order, `dslope` — gives: if two zeros `u, v` (counted with multiplicity) of `f`
lay in `|z| < ρ = 1/1000`, then `‖f 0‖ ≤ M ρ²/(R-ρ)² = 3.0·10⁻⁵`, whereas in fact
`‖f 0‖ = 1/72 = 1.39·10⁻²`.  This is `Work.ANum3.no_two_zeros`; it simultaneously rules out a second
zero (`u ≠ v`) and a double zero (`u = v`, using `deriv f u = 0`), hence `f` has exactly one zero in
the open disc and that zero is simple.

The two coarse bounds `‖φ_A z‖ ≤ 4` on `|z| ≤ 1/100` and `‖φ_A z‖ ≤ 28` on `|z| ≤ 1/20` are the only
outside input; both come from the Schwarz lemma for `ψ_A` (`Complex.norm_le_norm_of_mapsTo_ball`) and
the product bound for the hauptmodul. -/

namespace Work.ANum3

open Submission.CDTPlan Complex Metric
open scoped BigOperators

noncomputable section

/-! ## 1.  Elementary bounds for `φ_A` and its derivatives -/

/-- Schwarz lemma for the contour map: `‖ψ_A z‖ ≤ ‖z‖` on the open unit disc, since `ψ_A` is a
holomorphic self-map of the disc fixing `0`. -/
theorem psiA_norm_le_self {z : ℂ} (hz : ‖z‖ < 1) : ‖psiA z‖ ≤ ‖z‖ := by
  obtain ⟨-, hdiff, h0, hmap, -⟩ := Work.APsi.psiA_facts
  have hmaps : Set.MapsTo psiA (ball 0 1) (closedBall 0 1) := by
    intro w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    exact mem_closedBall_zero_iff.mpr (le_of_lt (hmap w (mem_closedBall_zero_iff.mpr hw1.le)))
  exact Complex.norm_le_norm_of_mapsTo_ball hdiff hmaps h0 hz

/-- `φ_A 0 = h(0) = 0`. -/
theorem phiA_zero : phiA 0 = 0 := by
  obtain ⟨-, -, h0, -, -⟩ := Work.APsi.psiA_facts
  change hauptH (psiA 0) = 0
  rw [h0]
  simp [hauptH]

/-- `‖φ_A z‖ ≤ 4` for `‖z‖ ≤ 1/100`. -/
theorem phiA_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1 / 100) : ‖phiA z‖ ≤ 4 := by
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz (by norm_num)
  exact Work.ANum3.hauptH_small_norm (le_trans (psiA_norm_le_self hz1) hz)

/-- `φ_A` is holomorphic on the unit disc. -/
theorem analyticOnNhd_phiA : AnalyticOnNhd ℂ phiA (ball 0 1) := by
  obtain ⟨-, hdiff, h0, hmap, -⟩ := Work.APsi.psiA_facts
  have hpsi : AnalyticOnNhd ℂ psiA (ball 0 1) := hdiff.analyticOnNhd isOpen_ball
  have hH : AnalyticOnNhd ℂ hauptH (ball 0 1) :=
    Work.Haupt.haupt_facts.1.analyticOnNhd isOpen_ball
  have hmaps : Set.MapsTo psiA (ball 0 1) (ball 0 1) := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    exact mem_ball_zero_iff.mpr (hmap z (mem_closedBall_zero_iff.mpr hz1.le))
  have h := hH.comp hpsi hmaps
  change AnalyticOnNhd ℂ (fun x => hauptH (psiA x)) (ball 0 1)
  exact h

/-- `deriv φ_A 0 = -256 · deriv ψ_A 0` (chain rule at the origin, using `deriv hauptH 0 = -256`). -/
theorem deriv_phiA_zero : deriv phiA 0 = -256 * deriv psiA 0 := by
  obtain ⟨-, hdiff, h0, hmap, -⟩ := Work.APsi.psiA_facts
  have hmemb : (0 : ℂ) ∈ ball 0 1 := mem_ball_zero_iff.mpr (by norm_num)
  have hdH : DifferentiableAt ℂ hauptH (psiA 0) :=
    Work.Haupt.haupt_facts.1.differentiableAt (by rw [h0]; exact isOpen_ball.mem_nhds hmemb)
  have hH : HasDerivAt hauptH (-256) (psiA 0) := by
    have h := hdH.hasDerivAt
    rw [h0, Work.Haupt.haupt_facts.2.1] at h
    rw [h0]
    exact h
  have hp : HasDerivAt psiA (deriv psiA 0) 0 :=
    (hdiff.differentiableAt (isOpen_ball.mem_nhds hmemb)).hasDerivAt
  have hcomp := hH.comp 0 hp
  change deriv (fun x : ℂ => hauptH (psiA x)) 0 = -256 * deriv psiA 0
  exact hcomp.deriv

/-- `‖deriv φ_A 0‖ = 256·‖deriv ψ_A 0‖ = 161.642…`. -/
theorem norm_deriv_phiA_zero :
    ‖deriv phiA 0‖ = 256 * (2383521894760738000000000 / 3774888615849058882987209) := by
  rw [deriv_phiA_zero, norm_mul, Work.ANum.psiA_deriv_norm]
  norm_num

/-! ## 2.  The Taylor remainder bound for `φ_A` on the disc of radius `1/1000` -/

/-- Second-order Taylor bound: for `‖z‖ ≤ 1/1000`,
`‖φ_A z - φ_A'(0)·z‖ ≤ (2·4/(1/100 - 1/1000)²)·(1/1000)·‖z‖` (so at most `0.0988`). -/
theorem phiA_taylor_bound {z : ℂ} (hz : ‖z‖ ≤ 1 / 1000) :
    ‖phiA z - deriv phiA 0 * z‖ ≤ (2 * 4 / (1 / 100 - 1 / 1000) ^ 2) * (1 / 1000) * ‖z‖ := by
  have hR : (0 : ℝ) < 1 / 100 - 1 / 1000 := by norm_num
  have h2 : ∀ u : ℂ, ‖u‖ ≤ 1 / 1000 →
      ‖iteratedDeriv 2 phiA u‖ ≤ 2 * 4 / (1 / 100 - 1 / 1000) ^ 2 := by
    intro u hu
    have hd : DiffContOnCl ℂ phiA (ball u (1 / 100 - 1 / 1000)) := by
      refine DiffContOnCl.mk_ball ?_ ?_
      · refine (analyticOnNhd_phiA.mono ?_).differentiableOn
        intro x hx
        rw [mem_ball_zero_iff]
        have hxu : ‖x - u‖ < 1 / 100 - 1 / 1000 := mem_ball_iff_norm.mp hx
        have h3 : ‖x‖ ≤ ‖x - u‖ + ‖u‖ := by simpa using norm_add_le (x - u) u
        linarith
      · refine (analyticOnNhd_phiA.mono ?_).continuousOn
        intro x hx
        rw [mem_ball_zero_iff]
        have hxu : ‖x - u‖ ≤ 1 / 100 - 1 / 1000 := mem_closedBall_iff_norm.mp hx
        have h3 : ‖x‖ ≤ ‖x - u‖ + ‖u‖ := by simpa using norm_add_le (x - u) u
        linarith
    have hb : ∀ w ∈ sphere u (1 / 100 - 1 / 1000), ‖phiA w‖ ≤ 4 := by
      intro w hw
      have hwu : ‖w - u‖ = 1 / 100 - 1 / 1000 := mem_sphere_iff_norm.mp hw
      exact phiA_norm_le (by
        have h3 : ‖w‖ ≤ ‖w - u‖ + ‖u‖ := by simpa using norm_add_le (w - u) u
        rw [hwu] at h3
        linarith)
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (n := 2) (c := u)
      (R := 1 / 100 - 1 / 1000) (C := 4) (f := phiA) hR hd hb
    simpa using h
  have h1 : ∀ w : ℂ, ‖w‖ ≤ 1 / 1000 →
      ‖deriv phiA w - deriv phiA 0‖ ≤ (2 * 4 / (1 / 100 - 1 / 1000) ^ 2) * ‖w‖ := by
    intro w hw
    have hd : ∀ x ∈ closedBall (0 : ℂ) (1 / 1000), DifferentiableAt ℂ (deriv phiA) x := by
      intro x hx
      have hxle : ‖x‖ ≤ 1 / 1000 := mem_closedBall_zero_iff.mp hx
      exact (analyticOnNhd_phiA x (mem_ball_zero_iff.mpr (by linarith))).deriv.differentiableAt
    have hb : ∀ x ∈ closedBall (0 : ℂ) (1 / 1000),
        ‖deriv (deriv phiA) x‖ ≤ (2 * 4 / (1 / 100 - 1 / 1000) ^ 2) := by
      intro x hx
      have hxle : ‖x‖ ≤ 1 / 1000 := mem_closedBall_zero_iff.mp hx
      have h := h2 x hxle
      have heq : deriv (deriv phiA) x = iteratedDeriv 2 phiA x := by
        rw [iteratedDeriv_succ (n := 1) (f := phiA), iteratedDeriv_one]
      rwa [heq]
    have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv phiA) hd hb
      (convex_closedBall (0 : ℂ) (1 / 1000))
      (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1 / 1000))
      (mem_closedBall_zero_iff.mpr hw)
    simpa using h
  have hder : ∀ w : ℂ, ‖w‖ < 1 → deriv (fun v : ℂ => phiA v - deriv phiA 0 * v) w
      = deriv phiA w - deriv phiA 0 := by
    intro w hw
    have hd1 : HasDerivAt phiA (deriv phiA w) w :=
      (analyticOnNhd_phiA w (mem_ball_zero_iff.mpr hw)).differentiableAt.hasDerivAt
    have hd2 : HasDerivAt (fun v : ℂ => deriv phiA 0 * v) (deriv phiA 0) w := by
      simpa using (hasDerivAt_id w).const_mul (deriv phiA 0)
    exact (hd1.sub hd2).deriv
  have hb : ∀ x ∈ closedBall (0 : ℂ) (1 / 1000),
      ‖deriv (fun v : ℂ => phiA v - deriv phiA 0 * v) x‖
        ≤ (2 * 4 / (1 / 100 - 1 / 1000) ^ 2) * (1 / 1000) := by
    intro x hx
    have hxle : ‖x‖ ≤ 1 / 1000 := mem_closedBall_zero_iff.mp hx
    rw [hder x (by linarith)]
    calc ‖deriv phiA x - deriv phiA 0‖ ≤ (2 * 4 / (1 / 100 - 1 / 1000) ^ 2) * ‖x‖ := h1 x hxle
      _ ≤ (2 * 4 / (1 / 100 - 1 / 1000) ^ 2) * (1 / 1000) := by
          have hpos : (0 : ℝ) ≤ 2 * 4 / (1 / 100 - 1 / 1000) ^ 2 := by positivity
          exact mul_le_mul_of_nonneg_left hxle hpos
  have hd : ∀ x ∈ closedBall (0 : ℂ) (1 / 1000),
      DifferentiableAt ℂ (fun v : ℂ => phiA v - deriv phiA 0 * v) x := by
    intro x hx
    have hxle : ‖x‖ ≤ 1 / 1000 := mem_closedBall_zero_iff.mp hx
    have h1 : DifferentiableAt ℂ phiA x :=
      (analyticOnNhd_phiA x (mem_ball_zero_iff.mpr (by linarith))).differentiableAt
    have h2 : DifferentiableAt ℂ (fun v : ℂ => deriv phiA 0 * v) x :=
      (differentiableAt_const (deriv phiA 0)).mul differentiableAt_id
    exact h1.sub h2
  have hmain := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := fun v : ℂ => phiA v - deriv phiA 0 * v) hd hb
    (convex_closedBall (0 : ℂ) (1 / 1000))
    (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1 / 1000))
    (mem_closedBall_zero_iff.mpr hz)
  have h0 : phiA 0 - deriv phiA 0 * 0 = 0 := by rw [phiA_zero]; ring
  rw [h0] at hmain
  simpa using hmain

/-! ## 3.  Existence of a zero in `|z| < 1/1000` (minimum modulus principle) -/

/-- On the sphere of radius `1/1000` the function `f = φ_A + 1/72` is bounded below by `1/30`:
`‖a z‖ ≥ 0.1616`, the Taylor remainder is at most `1/10` and `‖1/72‖ = 0.0139`. -/
theorem norm_phiA_add_le_sphere {z : ℂ} (hz : ‖z‖ = 1 / 1000) :
    (1 / 30 : ℝ) ≤ ‖phiA z + 1 / 72‖ := by
  have hzle : ‖z‖ ≤ 1 / 1000 := le_of_eq hz
  have htb := phiA_taylor_bound hzle
  have ha : (16164 / 100 : ℝ) ≤ ‖deriv phiA 0‖ := by
    rw [norm_deriv_phiA_zero]; norm_num
  have ha1 : (16164 / 100 : ℝ) * (1 / 1000) ≤ ‖deriv phiA 0 * z‖ := by
    rw [norm_mul, hz]
    exact mul_le_mul_of_nonneg_right ha (by norm_num)
  have htb' : ‖phiA z - deriv phiA 0 * z‖ ≤ 1 / 10 := by
    refine le_trans htb ?_
    have hpos : (0 : ℝ) ≤ (2 * 4 / (1 / 100 - 1 / 1000) ^ 2) * (1 / 1000) := by positivity
    calc (2 * 4 / (1 / 100 - 1 / 1000) ^ 2) * (1 / 1000) * ‖z‖
        ≤ (2 * 4 / (1 / 100 - 1 / 1000) ^ 2) * (1 / 1000) * (1 / 1000) :=
          mul_le_mul_of_nonneg_left hzle hpos
      _ ≤ 1 / 10 := by norm_num
  have htri : ‖deriv phiA 0 * z‖
      ≤ ‖phiA z + 1 / 72‖ + (‖phiA z - deriv phiA 0 * z‖ + ‖(1 / 72 : ℂ)‖) := by
    calc ‖deriv phiA 0 * z‖
        = ‖(phiA z + 1 / 72) - ((phiA z - deriv phiA 0 * z) + 1 / 72)‖ := by ring_nf
      _ ≤ ‖phiA z + 1 / 72‖ + ‖(phiA z - deriv phiA 0 * z) + 1 / 72‖ := norm_sub_le _ _
      _ ≤ ‖phiA z + 1 / 72‖ + (‖phiA z - deriv phiA 0 * z‖ + ‖(1 / 72 : ℂ)‖) := by
            gcongr
            exact norm_add_le _ _
  have h72 : ‖(1 / 72 : ℂ)‖ = 1 / 72 := by norm_num
  rw [h72] at htri
  linarith

/-- `f = φ_A + 1/72` has a zero in the open disc of radius `1/1000`. -/
theorem exists_zero_in_ball :
    ∃ z ∈ ball (0 : ℂ) (1 / 1000), phiA z + 1 / 72 = 0 := by
  obtain ⟨z, hzcl, hzzero⟩ : ∃ z ∈ closedBall (0 : ℂ) (1 / 1000), phiA z + 1 / 72 = 0 := by
    by_contra h
    push_neg at h
    refine Work.ANum3.exists_zero_of_norm_lt_sphere (f := fun w => phiA w + 1 / 72)
      (ρ := 1 / 1000) (c := 1 / 30) (by norm_num) ?_ h ?_ ?_
    · intro w hw
      have hwle : ‖w‖ ≤ 1 / 1000 := mem_closedBall_zero_iff.mp hw
      exact (analyticOnNhd_phiA w (mem_ball_zero_iff.mpr (by linarith))).add analyticAt_const
    · have h0 : phiA (0 : ℂ) + 1 / 72 = 1 / 72 := by rw [phiA_zero]; norm_num
      rw [h0]; norm_num
    · intro w hw
      exact norm_phiA_add_le_sphere hw
  refine ⟨z, ?_, hzzero⟩
  have hzle : ‖z‖ ≤ 1 / 1000 := mem_closedBall_zero_iff.mp hzcl
  have hne : ‖z‖ ≠ 1 / 1000 := by
    intro hlt
    have h1 := norm_phiA_add_le_sphere hlt
    rw [hzzero] at h1
    norm_num at h1
  rw [mem_ball_zero_iff]
  exact lt_of_le_of_ne hzle hne

/-! ## 4.  The boundary bound `‖f‖ ≤ 30` on `|z| = 1/20` -/

/-- Schwarz–Pick bound for the derivative of `ψ_A` on the disc of radius `1/20`. -/
theorem psiA_deriv_le_20 {z : ℂ} (hz : ‖z‖ ≤ 1 / 20) : ‖deriv psiA z‖ ≤ 79 / 100 := by
  have h := Work.ANum.psiA_deriv_le_schwarz (z := z) (a := 0) (b := 1 / 20)
    (le_refl 0) (by positivity) hz (by norm_num)
  refine le_trans h ?_
  norm_num

/-- `‖ψ_A z‖ ≤ 79/2000` for `‖z‖ ≤ 1/20` (mean value inequality). -/
theorem psiA_norm_le_20 {z : ℂ} (hz : ‖z‖ ≤ 1 / 20) : ‖psiA z‖ ≤ 79 / 2000 := by
  obtain ⟨-, hdiff, h0, hmap, -⟩ := Work.APsi.psiA_facts
  have hd : ∀ w ∈ closedBall (0 : ℂ) (1 / 20), DifferentiableAt ℂ psiA w := by
    intro w hw
    have hwle : ‖w‖ ≤ 1 / 20 := mem_closedBall_zero_iff.mp hw
    exact hdiff.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr (by linarith)))
  have hb : ∀ w ∈ closedBall (0 : ℂ) (1 / 20), ‖deriv psiA w‖ ≤ 79 / 100 := by
    intro w hw
    exact psiA_deriv_le_20 (mem_closedBall_zero_iff.mp hw)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := psiA) hd hb
    (convex_closedBall (0 : ℂ) (1 / 20))
    (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1 / 20))
    (mem_closedBall_zero_iff.mpr hz)
  have h' : ‖psiA z‖ ≤ (79 / 100) * ‖z - 0‖ := by simpa [h0] using h
  rw [sub_zero] at h'
  calc ‖psiA z‖ ≤ (79 / 100) * ‖z‖ := h'
    _ ≤ (79 / 100) * (1 / 20) := by
        exact mul_le_mul_of_nonneg_left hz (by norm_num)
    _ = 79 / 2000 := by norm_num

/-- `exp 1 ≤ 272/100`. -/
theorem exp_one_le : Real.exp 1 ≤ 272 / 100 := by
  have h := Real.exp_bound' (x := (1 : ℝ)) (by norm_num) (by norm_num) (n := 7) (by norm_num)
  refine le_trans h ?_
  norm_num [Finset.sum_range_succ]

/-- `‖φ_A z‖ ≤ 28` for `‖z‖ ≤ 1/20`. -/
theorem phiA_norm_le_20 {z : ℂ} (hz : ‖z‖ ≤ 1 / 20) : ‖phiA z‖ ≤ 28 := by
  have hpsi : ‖psiA z‖ ≤ 79 / 2000 := psiA_norm_le_20 hz
  have hq1 : ‖psiA z‖ < 1 := by linarith
  have h2 := Work.ANum3.hauptH_norm_le_exp hq1
  change ‖hauptH (psiA z)‖ ≤ 28
  refine le_trans h2 ?_
  have hs1 : ‖psiA z‖ ≤ 1 / 25 := by linarith
  have hden : (0 : ℝ) < 1 - ‖psiA z‖ := by linarith
  have hratio : 24 * ‖psiA z‖ / (1 - ‖psiA z‖) ≤ 1 := by
    rw [div_le_iff₀ hden]
    nlinarith
  have hexp : Real.exp (24 * ‖psiA z‖ / (1 - ‖psiA z‖)) ≤ 272 / 100 :=
    le_trans (Real.exp_le_exp.mpr hratio) exp_one_le
  have hmain : 256 * ‖psiA z‖ * Real.exp (24 * ‖psiA z‖ / (1 - ‖psiA z‖))
      ≤ 256 * (79 / 2000) * (272 / 100) := by
    have h2 : 256 * ‖psiA z‖ ≤ 256 * (79 / 2000) := by linarith [hpsi]
    calc 256 * ‖psiA z‖ * Real.exp (24 * ‖psiA z‖ / (1 - ‖psiA z‖))
        ≤ 256 * (79 / 2000) * Real.exp (24 * ‖psiA z‖ / (1 - ‖psiA z‖)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
      _ ≤ 256 * (79 / 2000) * (272 / 100) :=
          mul_le_mul_of_nonneg_left hexp (by norm_num)
  linarith

/-! ## 5.  Uniqueness and simplicity -/

/-- `f = φ_A + 1/72` has *exactly one* zero in `|z| < 1/1000`, and it is simple. -/
theorem phiA_inner_unique :
    ∃ z₀ ∈ ball (0 : ℂ) (1 / 1000), phiA z₀ + 1 / 72 = 0 ∧
      deriv (fun w => phiA w + 1 / 72) z₀ ≠ 0 ∧
      ∀ z ∈ ball (0 : ℂ) (1 / 1000), phiA z + 1 / 72 = 0 → z = z₀ := by
  obtain ⟨z₀, hz₀ball, hz₀zero⟩ := exists_zero_in_ball
  have hz₀lt : ‖z₀‖ < 1 / 1000 := mem_ball_zero_iff.mp hz₀ball
  -- the analyticity hypothesis of the maximum-modulus lemma
  have hF : AnalyticOnNhd ℂ (fun w => phiA w + 1 / 72) (closedBall (0 : ℂ) (1 / 20)) := by
    refine (analyticOnNhd_phiA.mono ?_).add analyticOnNhd_const
    intro w hw
    rw [mem_ball_zero_iff]
    have hwle : ‖w‖ ≤ 1 / 20 := mem_closedBall_zero_iff.mp hw
    linarith
  have hsup : ∀ z : ℂ, ‖z‖ = 1 / 20 → ‖phiA z + 1 / 72‖ ≤ 30 := by
    intro z hz
    have h1 : ‖phiA z‖ ≤ 28 := phiA_norm_le_20 (le_of_eq hz)
    have h72 : ‖(1 / 72 : ℂ)‖ = 1 / 72 := by norm_num
    calc ‖phiA z + 1 / 72‖ ≤ ‖phiA z‖ + ‖(1 / 72 : ℂ)‖ := norm_add_le _ _
      _ = ‖phiA z‖ + 1 / 72 := by rw [h72]
      _ ≤ 28 + 1 / 72 := by linarith
      _ ≤ 30 := by norm_num
  have hf0 : (fun w : ℂ => phiA w + 1 / 72) 0 = 1 / 72 := by
    change phiA 0 + 1 / 72 = 1 / 72
    rw [phiA_zero]; norm_num
  have hbig : (30 : ℝ) * (1 / 1000) ^ 2 < ‖(fun w : ℂ => phiA w + 1 / 72) 0‖ * (1 / 20 - 1 / 1000) ^ 2 := by
    rw [hf0]
    norm_num
  have hderiv : deriv (fun w : ℂ => phiA w + 1 / 72) z₀ = deriv phiA z₀ :=
    deriv_add_const (1 / 72)
  refine ⟨z₀, hz₀ball, hz₀zero, ?_, ?_⟩
  · -- simplicity: a double zero at `z₀` is excluded by the two-zero bound
    intro hder
    refine Work.ANum3.no_two_zeros (F := fun w : ℂ => phiA w + 1 / 72) (R := 1 / 20)
      (ρ := 1 / 1000) (M := 30) (a := z₀) (b := z₀)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hF hsup hbig
      hz₀lt hz₀lt hz₀zero hz₀zero ?_
    exact fun _ => hder
  · -- uniqueness: a second zero would give two distinct zeros
    intro z hzball hzzero
    by_contra hne
    have hzlt : ‖z‖ < 1 / 1000 := mem_ball_zero_iff.mp hzball
    exact Work.ANum3.no_two_zeros (F := fun w : ℂ => phiA w + 1 / 72) (R := 1 / 20)
      (ρ := 1 / 1000) (M := 30) (a := z₀) (b := z)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hF hsup hbig
      hz₀lt hzlt hz₀zero hzzero (fun h => (hne h.symm).elim)

end

end Work.ANum3
