import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.H_conv_alt
import Submission.Work.C17g.linear_ode_convex
import Submission.Work.OdeCont.uniqueness

/-!
# `Work.A14D.H_cont`

The `x`-side series `H = Hfun a b c` converges on the unit disc and solves Zagier's order-two
operator `LZ y = rhsZ b c` there (`Work.A14D.H_conv_alt`).  This file continues that solution to the
two half-planes

`SU = {z | (1 - Re z)/8 < Im z}` and `SL = {z | Im z < (Re z - 1)/8}`,

which are open, convex, avoid the three singularities `0, 1/9, 1` of the operator, and meet the
unit disc.  On each of them the pullback `(u, u') ↦ sysA z · (u,u') + sysb (rhsZ b c) z` of the
scalar operator is a first order linear system with holomorphic coefficients, so
`Work.C17g.linear_ode_convex` produces a global solution `Y` on the half-plane; its first component
`F = Y · 0` solves `LZ F = rhsZ b c` (`LZ_of_hasDerivAt_toSol`), and it agrees with `Hfun a b c`
on the half-plane ∩ unit disc by uniqueness of solutions of linear systems
(`Work.OdeCont.uniqueness`), applied on the convex set `S ∩ ball 0 1` where `Hfun` is a solution
by `H_conv` (the operator is regular there because `1/9 ∉ SU ∪ SL`).
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

noncomputable section

/-! ## 1. Elementary geometry of `SU` and `SL` -/

lemma mem_SU_iff {z : ℂ} : z ∈ SU ↔ 1 < 8 * z.im + z.re := by
  have h : z ∈ SU ↔ (1 - z.re) / 8 < z.im := Iff.rfl
  rw [h, div_lt_iff₀ (by norm_num : (0 : ℝ) < 8)]
  constructor <;> intro h' <;> linarith

lemma mem_SL_iff {z : ℂ} : z ∈ SL ↔ 8 * z.im + 1 < z.re := by
  have h : z ∈ SL ↔ z.im < (z.re - 1) / 8 := Iff.rfl
  rw [h, lt_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
  constructor <;> intro h' <;> linarith

lemma convex_SU : Convex ℝ SU := by
  have h : SU = {z : ℂ | 1 < 8 * z.im + z.re} := by
    ext z; exact mem_SU_iff
  rw [h]
  exact convex_halfSpace_gt (f := fun z : ℂ => 8 * z.im + z.re) ⟨by intro x y; simp; ring,
    by intro c x; simp; ring⟩ 1

lemma convex_SL : Convex ℝ SL := by
  have h : SL = {z : ℂ | 1 < z.re - 8 * z.im} := by
    ext z
    show z ∈ SL ↔ 1 < z.re - 8 * z.im
    rw [mem_SL_iff]
    constructor <;> intro h' <;> linarith
  rw [h]
  exact convex_halfSpace_gt (f := fun z : ℂ => z.re - 8 * z.im) ⟨by intro x y; simp; ring,
    by intro c x; simp; ring⟩ 1

lemma isOpen_SU_H_cont : IsOpen SU := by
  have h : SU = {z : ℂ | (1 - z.re) / 8 < z.im} := rfl
  rw [h]
  exact isOpen_lt (by fun_prop : Continuous fun z : ℂ => (1 - z.re) / 8)
    (by fun_prop : Continuous fun z : ℂ => z.im)

lemma isOpen_SL_H_cont : IsOpen SL := by
  have h : SL = {z : ℂ | z.im < (z.re - 1) / 8} := rfl
  rw [h]
  exact isOpen_lt (by fun_prop : Continuous fun z : ℂ => z.im)
    (by fun_prop : Continuous fun z : ℂ => (z.re - 1) / 8)

/-! ## 2. `PZ` does not vanish on `SU`, `SL` -/

lemma ne_one_of_PZ_ne_zero {z : ℂ} (h : PZ z ≠ 0) : z ≠ 1 := by
  intro hz
  exact h (by rw [hz]; norm_num [PZ])

private lemma PZ_eq_zero_cases {z : ℂ} (h : PZ z = 0) :
    z = 0 ∨ z = 1 ∨ (z.re = 1 / 9 ∧ z.im = 0) := by
  have h' : z * (1 - z) * (1 - 9 * z) = 0 := h
  rcases mul_eq_zero.mp h' with h2 | h2
  · rcases mul_eq_zero.mp h2 with h2 | h2
    · exact Or.inl h2
    · exact Or.inr (Or.inl (by linear_combination -h2))
  · have hz9 : z = 1 / 9 := by
      have h3 : 9 * z = 1 := by linear_combination -h2
      rw [eq_div_iff (by norm_num : (9 : ℂ) ≠ 0)]
      linear_combination h3
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · rw [hz9]; norm_num
    · rw [hz9]; norm_num

lemma PZ_ne_zero_of_mem_SU {z : ℂ} (hz : z ∈ SU) : PZ z ≠ 0 := by
  intro h
  have hz' : 1 < 8 * z.im + z.re := mem_SU_iff.mp hz
  rcases PZ_eq_zero_cases h with h2 | h2 | ⟨h2, h3⟩
  · rw [h2] at hz'; norm_num at hz'
  · rw [h2] at hz'; norm_num at hz'
  · rw [h2, h3] at hz'; norm_num at hz'

lemma PZ_ne_zero_of_mem_SL {z : ℂ} (hz : z ∈ SL) : PZ z ≠ 0 := by
  intro h
  have hz' : 8 * z.im + 1 < z.re := mem_SL_iff.mp hz
  rcases PZ_eq_zero_cases h with h2 | h2 | ⟨h2, h3⟩
  · rw [h2] at hz'; norm_num at hz'
  · rw [h2] at hz'; norm_num at hz'
  · rw [h2, h3] at hz'; norm_num at hz'

/-! ## 3. The first order system attached to `LZ` -/

lemma sysA_00 (z : ℂ) : sysA z 0 0 = 0 := by simp [sysA]
lemma sysA_01 (z : ℂ) : sysA z 0 1 = 1 := by simp [sysA]
lemma sysA_10 (z : ℂ) : sysA z 1 0 = -(RZ z / PZ z) := by simp [sysA]
lemma sysA_11 (z : ℂ) : sysA z 1 1 = -(PZ' z / PZ z) := by simp [sysA]
lemma sysb_0 (g : ℂ → ℂ) (z : ℂ) : sysb g z 0 = 0 := by simp [sysb]
lemma sysb_1 (g : ℂ → ℂ) (z : ℂ) : sysb g z 1 = g z / PZ z := by simp [sysb]

lemma differentiableOn_PZ (S : Set ℂ) : DifferentiableOn ℂ PZ S := by
  unfold PZ
  exact (differentiableOn_id.mul ((differentiableOn_const (1 : ℂ)).sub differentiableOn_id)).mul
    ((differentiableOn_const (1 : ℂ)).sub
      ((differentiableOn_const (9 : ℂ)).mul differentiableOn_id))

lemma differentiableOn_PZ' (S : Set ℂ) : DifferentiableOn ℂ PZ' S := by
  unfold PZ'
  exact ((differentiableOn_const (1 : ℂ)).sub
      ((differentiableOn_const (20 : ℂ)).mul differentiableOn_id)).add
    ((differentiableOn_const (27 : ℂ)).mul (differentiableOn_id.pow 2))

lemma differentiableOn_RZ (S : Set ℂ) : DifferentiableOn ℂ RZ S := by
  unfold RZ
  exact ((differentiableOn_const (9 : ℂ)).mul differentiableOn_id).sub
    (differentiableOn_const (3 : ℂ))

lemma differentiableOn_sysA {S : Set ℂ} (hPZ : ∀ z ∈ S, PZ z ≠ 0) :
    DifferentiableOn ℂ sysA S := by
  rw [differentiableOn_pi]
  intro i
  rw [differentiableOn_pi]
  intro j
  fin_cases i <;> fin_cases j
  · have h00 : ∀ z : ℂ, sysA z 0 0 = 0 := fun z => by simp [sysA]
    show DifferentiableOn ℂ (fun z => sysA z 0 0) S
    simpa only [h00] using differentiableOn_const (0 : ℂ)
  · have h01 : ∀ z : ℂ, sysA z 0 1 = 1 := fun z => by simp [sysA]
    show DifferentiableOn ℂ (fun z => sysA z 0 1) S
    simpa only [h01] using differentiableOn_const (1 : ℂ)
  · show DifferentiableOn ℂ (fun z : ℂ => -(RZ z / PZ z)) S
    exact ((differentiableOn_RZ S).div (differentiableOn_PZ S) hPZ).neg
  · show DifferentiableOn ℂ (fun z : ℂ => -(PZ' z / PZ z)) S
    exact ((differentiableOn_PZ' S).div (differentiableOn_PZ S) hPZ).neg

lemma differentiableOn_rhsZ (b c : ℤ) {S : Set ℂ} (h1 : ∀ z ∈ S, z ≠ 1) :
    DifferentiableOn ℂ (rhsZ b c) S := by
  have h2 : DifferentiableOn ℂ (fun z : ℂ => (c : ℂ) / (1 - z)) S :=
    (differentiableOn_const (c : ℂ)).div
      ((differentiableOn_const (1 : ℂ)).sub differentiableOn_id)
      (fun z hz h => h1 z hz (by linear_combination -h))
  have h3 : DifferentiableOn ℂ ((fun _ : ℂ => (b : ℂ)) + fun z : ℂ => (c : ℂ) / (1 - z)) S :=
    (differentiableOn_const (b : ℂ)).add h2
  unfold rhsZ
  exact h3

lemma differentiableOn_sysb (b c : ℤ) {S : Set ℂ} (hPZ : ∀ z ∈ S, PZ z ≠ 0) :
    DifferentiableOn ℂ (sysb (rhsZ b c)) S := by
  have h1 : ∀ z ∈ S, z ≠ 1 := fun z hz => ne_one_of_PZ_ne_zero (hPZ z hz)
  rw [differentiableOn_pi]
  intro i
  fin_cases i
  · have hb0 : ∀ z : ℂ, sysb (rhsZ b c) z 0 = 0 := fun z => by simp [sysb]
    show DifferentiableOn ℂ (fun z => sysb (rhsZ b c) z 0) S
    simpa only [hb0] using differentiableOn_const (0 : ℂ)
  · show DifferentiableOn ℂ (fun z : ℂ => rhsZ b c z / PZ z) S
    exact (differentiableOn_rhsZ b c h1).div (differentiableOn_PZ S) hPZ

/-! ## 4. Continuation to a convex half-plane -/

theorem cont_of_convex {S : Set ℂ} (hSc : Convex ℝ S) (hSo : IsOpen S)
    (hPZ : ∀ z ∈ S, PZ z ≠ 0) (a b c : ℤ)
    (hHd : DifferentiableOn ℂ (Hfun a b c) (Metric.ball 0 1))
    (hHode : ∀ z ∈ Metric.ball 0 1, LZ (Hfun a b c) z = rhsZ b c z)
    (z₀ : ℂ) (hz₀ : z₀ ∈ S ∩ Metric.ball 0 1) :
    ∃ F : ℂ → ℂ, DifferentiableOn ℂ F S ∧ (∀ z ∈ S, LZ F z = rhsZ b c z) ∧
      (∀ z ∈ S ∩ Metric.ball 0 1, F z = Hfun a b c z) := by
  obtain ⟨Y, hYd, hY0, hYode⟩ :=
    Work.C17g.linear_ode_convex (k := 2) hSc hSo sysA (sysb (rhsZ b c))
      (differentiableOn_sysA hPZ) (differentiableOn_sysb b c hPZ) z₀ hz₀.1
      (toSol (Hfun a b c) z₀)
  let F : ℂ → ℂ := fun z => Y z 0
  have hFd : DifferentiableOn ℂ F S := by
    have hproj : DifferentiableOn ℂ (fun w : Fin 2 → ℂ => w 0) Set.univ :=
      (differentiableOn_pi.mp (differentiableOn_id (𝕜 := ℂ))) 0
    exact hproj.comp hYd (fun z _ => trivial)
  have hrow0 : ∀ w : ℂ, (∑ j : Fin 2, sysA w 0 j * Y w j) + sysb (rhsZ b c) w 0 = Y w 1 := by
    intro w
    rw [Fin.sum_univ_two, sysA_00, sysA_01, sysb_0]
    ring
  have hderF : ∀ w ∈ S, deriv F w = Y w 1 := by
    intro w hw
    have h0 : HasDerivAt F (Y w 1) w := by
      have h := (hasDerivAt_pi.mp (hYode w hw)) 0
      rw [hrow0 w] at h
      exact h
    exact h0.deriv
  have hFode : ∀ z ∈ S, LZ F z = rhsZ b c z := by
    intro z hz
    have htoSol_ev : toSol F =ᶠ[𝓝 z] Y := by
      filter_upwards [hSo.mem_nhds hz] with w hw
      funext i
      fin_cases i
      · simp [toSol, F]
      · simp [toSol, F, hderF w hw]
    have hz_eq : Y z = toSol F z := by
      funext i
      fin_cases i
      · simp [toSol, F]
      · simp [toSol, F, hderF z hz]
    have hsysF : HasDerivAt (toSol F)
        (fun i => ∑ j, sysA z i j * toSol F z j + sysb (rhsZ b c) z i) z := by
      have h1 : HasDerivAt (toSol F)
          (fun i => ∑ j, sysA z i j * Y z j + sysb (rhsZ b c) z i) z :=
        (hYode z hz).congr_of_eventuallyEq htoSol_ev
      refine h1.congr_deriv ?_
      funext i
      rw [hz_eq]
    have hderF_diff : DifferentiableAt ℂ (deriv F) z := by
      have hY1 : DifferentiableAt ℂ (fun w => Y w 1) z :=
        ((differentiableOn_pi.mp hYd) 1).differentiableAt (hSo.mem_nhds hz)
      have hev : deriv F =ᶠ[𝓝 z] fun w => Y w 1 := by
        filter_upwards [hSo.mem_nhds hz] with w hw
        exact hderF w hw
      exact hY1.congr_of_eventuallyEq hev
    exact LZ_of_hasDerivAt_toSol (u := F) (g := rhsZ b c) hsysF hderF_diff (hPZ z hz)
  have hUopen : IsOpen (S ∩ Metric.ball 0 1) := hSo.inter Metric.isOpen_ball
  have hUpre : IsPreconnected (S ∩ Metric.ball 0 1) :=
    (hSc.inter (convex_ball 0 1)).isPreconnected
  have hAdiffU : ∀ i j : Fin 2, DifferentiableOn ℂ (fun z => sysA z i j)
      (S ∩ Metric.ball 0 1) := fun i j =>
    ((differentiableOn_pi.mp (differentiableOn_pi.mp (differentiableOn_sysA hPZ) i)) j).mono
      Set.inter_subset_left
  have hbdiffU : ∀ i : Fin 2, DifferentiableOn ℂ (fun z => sysb (rhsZ b c) z i)
      (S ∩ Metric.ball 0 1) := fun i =>
    ((differentiableOn_pi.mp (differentiableOn_sysb b c hPZ)) i).mono Set.inter_subset_left
  have hYdiffU : DifferentiableOn ℂ Y (S ∩ Metric.ball 0 1) := hYd.mono Set.inter_subset_left
  have htoSoldiffU : DifferentiableOn ℂ (toSol (Hfun a b c)) (S ∩ Metric.ball 0 1) := by
    rw [differentiableOn_pi]
    intro i
    fin_cases i
    · show DifferentiableOn ℂ (fun z : ℂ => toSol (Hfun a b c) z 0) (S ∩ Metric.ball 0 1)
      simpa [toSol] using hHd.mono (fun z hz => hz.2)
    · show DifferentiableOn ℂ (fun z : ℂ => deriv (Hfun a b c) z) (S ∩ Metric.ball 0 1)
      exact (hHd.deriv Metric.isOpen_ball).mono (fun z hz => hz.2)
  have htoSolODE : ∀ z ∈ S ∩ Metric.ball 0 1,
      HasDerivAt (toSol (Hfun a b c))
        (fun i => ∑ j, sysA z i j * toSol (Hfun a b c) z j + sysb (rhsZ b c) z i) z := by
    intro z hz
    have hzball : z ∈ Metric.ball 0 1 := hz.2
    have hFz : DifferentiableAt ℂ (Hfun a b c) z :=
      hHd.differentiableAt (Metric.isOpen_ball.mem_nhds hzball)
    have hFz' : DifferentiableAt ℂ (deriv (Hfun a b c)) z :=
      (hHd.deriv Metric.isOpen_ball).differentiableAt (Metric.isOpen_ball.mem_nhds hzball)
    exact hasDerivAt_toSol hFz hFz' (hPZ z hz.1) (hHode z hzball)
  have heq := Work.OdeCont.uniqueness hUopen hUpre sysA (sysb (rhsZ b c)) hAdiffU hbdiffU
    Y (toSol (Hfun a b c)) hYdiffU htoSoldiffU (fun z hz => hYode z hz.1) htoSolODE hz₀ hY0
  refine ⟨F, hFd, hFode, ?_⟩
  intro z hz
  have h := congrFun (heq hz) 0
  simpa [toSol, F] using h

/-! ## 5. The two half-plane continuations and the conclusion -/

theorem H_cont (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) : ∃ HU HL : ℂ → ℂ,
    DifferentiableOn ℂ HU SU ∧ DifferentiableOn ℂ HL SL ∧
    (∀ z ∈ SU, LZ HU z = rhsZ b c z) ∧ (∀ z ∈ SL, LZ HL z = rhsZ b c z) ∧
    (∀ z ∈ SU ∩ ball 0 1, HU z = Hfun a b c z) ∧
    (∀ z ∈ SL ∩ ball 0 1, HL z = Hfun a b c z) := by
  obtain ⟨hHd, hHode⟩ := H_conv_alt a b c h
  set zU : ℂ := ((1 / 2 : ℝ) : ℂ) * Complex.I with hzUdef
  set zL : ℂ := -zU with hzLdef
  have hzUre : zU.re = 0 := by simp [zU]
  have hzUim : zU.im = 1 / 2 := by simp [zU]
  have hzUnorm : ‖zU‖ = 1 / 2 := by
    have h2 : ‖zU‖ ^ 2 = (1 / 2 : ℝ) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hzUre, hzUim]
      norm_num
    nlinarith [norm_nonneg zU]
  have hzLre : zL.re = 0 := by simp [zL, hzUre]
  have hzLim : zL.im = -(1 / 2) := by simp [zL, hzUim]
  have hzLnorm : ‖zL‖ = 1 / 2 := by rw [hzLdef, norm_neg, hzUnorm]
  have hzU : zU ∈ SU ∩ Metric.ball 0 1 := by
    refine ⟨?_, ?_⟩
    · rw [mem_SU_iff, hzUre, hzUim]; norm_num
    · rw [Metric.mem_ball, dist_zero_right, hzUnorm]; norm_num
  have hzL : zL ∈ SL ∩ Metric.ball 0 1 := by
    refine ⟨?_, ?_⟩
    · rw [mem_SL_iff, hzLre, hzLim]; norm_num
    · rw [Metric.mem_ball, dist_zero_right, hzLnorm]; norm_num
  obtain ⟨FU, hFUd, hFUode, hFUeq⟩ :=
    cont_of_convex convex_SU isOpen_SU_H_cont (fun z hz => PZ_ne_zero_of_mem_SU hz) a b c hHd hHode
      zU hzU
  obtain ⟨FL, hFLd, hFLode, hFLeq⟩ :=
    cont_of_convex convex_SL isOpen_SL_H_cont (fun z hz => PZ_ne_zero_of_mem_SL hz) a b c hHd hHode
      zL hzL
  exact ⟨FU, FL, hFUd, hFLd, hFUode, hFLode, hFUeq, hFLeq⟩

end

end Work.A14D
