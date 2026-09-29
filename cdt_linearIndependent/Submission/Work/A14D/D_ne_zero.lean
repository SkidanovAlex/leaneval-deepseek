import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.H_conv_alt
import Submission.Work.A14D.H_local_at_one
import Submission.Work.A14D.H_not_holo_at_one
import Submission.Work.A14D.uh_ode
import Submission.Work.A14D.log_one_sub_jump
import Submission.Work.A14D.glue_three_LZ
import Submission.Work.C17g.linear_ode_convex
import Submission.Work.A14D.geom_halfball_cover
import Submission.Work.A14D.log_growth_contra
import Submission.Work.A14D.eqOn_zero_of_ball_of_Ioo

namespace Work.A14D

/-
ROUTE (area A14D).  `D` is the jump of `H = Hfun a b c`: `D = HU - HL` on the wedge
`SU ∩ SL = {re > 1, |im| < (re-1)/8}`, continued to `Om1` (`WORK.A14D.kappa_jump_sol`).

Suppose `D = 0`, i.e. `HU = HL` on the wedge.  Then the three pieces glue:
`F := Hfun` on `ball 0 1`, `F := HU` on `SU`, `F := HL` on `SL` is a well-defined holomorphic
function on `Omega := ball 0 1 ∪ SU ∪ SL` (the pairwise agreements are the hypotheses), and
`Omega ⊇ {0 < |z-1| < eps}` for small `eps > 0`: for `z` near 1 with `re z < 1` we have `|z| < 1`
(i.e. `z ∈ ball 0 1`), while for `re z ≥ 1` (and `z ≠ 1`) one has `z ∈ SU ∪ SL`.

Now `H_local_at_one` gives `Hfun = e0 + e1·ell + e2·ell²` on `lens1 δ` (`ell = Complex.log (1-z)`,
`e2 = -(c/16)·uh`), and `F = Hfun` there.  The function `phi := F - e0 - e1·ell - e2·ell²` is
holomorphic on the upper (resp. lower) half-disc `ball 1 δ ∩ {im > 0}` (resp. `{im < 0}`) and
vanishes on `lens1 δ ∩ {im > 0}` (a nonempty open subset), so it vanishes identically there.

Now fix `t ∈ (1, 1+eps)`.  Taking the boundary values of `phi` from above and from below gives
`0 = F t - e0 t - e1 t·L± - e2 t·L±²` with `L₊ = log(t-1) - π i`, `L₋ = log(t-1) + π i`; subtracting,
`e1(t) + 2·e2(t)·log(t-1) = 0` for all `t ∈ (1,1+eps)`.  As `e1` is holomorphic at `t = 1`,
`e2(1) ≠ 0` is impossible, and if `e2(1) = 0` (i.e. `c = 0`) then `e2 ≡ 0`, `e1 ≡ 0` near `1`,
so `Hfun = e0` on `lens1 δ`, contradicting `H_not_holo_at_one a b c h hb rfl`.

(`D ≠ 0` is used in `kappa_jump_nnz`: `D ≠ 0 ⇒ κU ≠ 0 ∨ κL ≠ 0`, via the companion lemma
`A14D/kappaU_zero_imp_D_zero`.)
-/
open Complex Metric Filter
open scoped Topology
open Classical

noncomputable section

/-! ## Gluing three functions on three open sets -/

/-- Glue `fA` on `A`, `fB` on `B` and `fC` elsewhere. -/
def glue3 (A B : Set ℂ) (fA fB fC : ℂ → ℂ) : ℂ → ℂ :=
  fun z => if z ∈ A then fA z else if z ∈ B then fB z else fC z

lemma glue3_eqOn_A (A B : Set ℂ) (fA fB fC : ℂ → ℂ) :
    Set.EqOn (glue3 A B fA fB fC) fA A :=
  fun z hz => by simp only [glue3, if_pos hz]

lemma glue3_eqOn_B {A B : Set ℂ} {fA fB fC : ℂ → ℂ} (hAB : Set.EqOn fA fB (A ∩ B)) :
    Set.EqOn (glue3 A B fA fB fC) fB B := by
  intro z hz
  by_cases h : z ∈ A
  · simp only [glue3, if_pos h]
    exact hAB ⟨h, hz⟩
  · simp only [glue3, if_neg h, if_pos hz]

lemma glue3_eqOn_C {A B C : Set ℂ} {fA fB fC : ℂ → ℂ} (hAC : Set.EqOn fA fC (A ∩ C))
    (hBC : Set.EqOn fB fC (B ∩ C)) : Set.EqOn (glue3 A B fA fB fC) fC C := by
  intro z hz
  by_cases h : z ∈ A
  · simp only [glue3, if_pos h]
    exact hAC ⟨h, hz⟩
  · by_cases h' : z ∈ B
    · simp only [glue3, if_neg h, if_pos h']
      exact hBC ⟨h', hz⟩
    · simp only [glue3, if_neg h, if_neg h']

lemma glue3_differentiableOn {A B C : Set ℂ} (hAo : IsOpen A) (hBo : IsOpen B) (hCo : IsOpen C)
    {fA fB fC : ℂ → ℂ} (hAd : DifferentiableOn ℂ fA A) (hBd : DifferentiableOn ℂ fB B)
    (hCd : DifferentiableOn ℂ fC C)
    (hAB : Set.EqOn fA fB (A ∩ B)) (hAC : Set.EqOn fA fC (A ∩ C))
    (hBC : Set.EqOn fB fC (B ∩ C)) :
    DifferentiableOn ℂ (glue3 A B fA fB fC) (A ∪ B ∪ C) := by
  intro z hz
  rw [Set.mem_union] at hz
  rcases hz with (hzA | hzB) | hzC
  · exact (differentiableAt_of_eqOn_open hAo (glue3_eqOn_A A B fA fB fC) hAd hzA)
      |>.differentiableWithinAt
  · exact (differentiableAt_of_eqOn_open hBo (glue3_eqOn_B hAB) hBd hzB)
      |>.differentiableWithinAt
  · exact (differentiableAt_of_eqOn_open hCo (glue3_eqOn_C hAC hBC) hCd hzC)
      |>.differentiableWithinAt

lemma isOpen_SU : IsOpen SU := by
  have h : SU = {z : ℂ | (1 - z.re) / 8 < z.im} := rfl
  rw [h]
  exact isOpen_lt (by fun_prop) (by fun_prop)

lemma isOpen_SL : IsOpen SL := by
  have h : SL = {z : ℂ | z.im < (z.re - 1) / 8} := rfl
  rw [h]
  exact isOpen_lt (by fun_prop) (by fun_prop)

lemma isOpen_lens1 (δ : ℝ) : IsOpen (lens1 δ) := Metric.isOpen_ball.inter Metric.isOpen_ball

/-- `ell` is differentiable on any set contained in the open upper half-plane. -/
lemma differentiableOn_ell_im_pos {Ω : Set ℂ} (hΩ : ∀ z ∈ Ω, 0 < z.im) :
    DifferentiableOn ℂ ell Ω := by
  intro z hz
  have hsp : 1 - z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    have h : (1 - z).im = -z.im := by simp
    rw [h]
    linarith [hΩ z hz]
  exact ((Complex.differentiableAt_log hsp).comp z
    ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id)).differentiableWithinAt

/-- `ell` is differentiable on any set contained in the open lower half-plane. -/
lemma differentiableOn_ell_im_neg {Ω : Set ℂ} (hΩ : ∀ z ∈ Ω, z.im < 0) :
    DifferentiableOn ℂ ell Ω := by
  intro z hz
  have hsp : 1 - z ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    have h : (1 - z).im = -z.im := by simp
    rw [h]
    linarith [hΩ z hz]
  exact ((Complex.differentiableAt_log hsp).comp z
    ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id)).differentiableWithinAt

end

open scoped Topology

theorem D_ne_zero (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c) (hb : b ≠ 0)
    (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU ∧ (∀ z ∈ SU, LZ HU z = rhsZ b c z) ∧
      ∀ z ∈ SU ∩ ball 0 1, HU z = Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL SL ∧ (∀ z ∈ SL, LZ HL z = rhsZ b c z) ∧
      ∀ z ∈ SL ∩ ball 0 1, HL z = Hfun a b c z)
    (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z) :
    D ≠ 0 := by
  intro hD0
  -- ## Setup
  obtain ⟨δ, hδ0, hδ89, e0, e1, he0, he1, hid⟩ := H_local_at_one a b c h
  obtain ⟨huhd, huh1, _⟩ := uh_ode
  obtain ⟨hHfd, _⟩ := H_conv_alt a b c h
  set e2 : ℂ → ℂ := fun z => (-((c : ℂ) / 16)) * uh z with he2def
  have hδ89le : δ ≤ 8 / 9 := le_of_lt hδ89
  have hδ1 : δ ≤ 1 := by linarith
  set ε : ℝ := δ / 2 with hεdef
  have hε0 : 0 < ε := by rw [hεdef]; linarith
  have hεδ : ε < δ := by rw [hεdef]; linarith
  have he2d : DifferentiableOn ℂ e2 (Metric.ball (1 : ℂ) δ) := by
    rw [he2def]
    exact (huhd.mono (Metric.ball_subset_ball hδ89le)).const_mul _
  -- ## The glued function
  have hAB : Set.EqOn (Hfun a b c) HU (Metric.ball (0 : ℂ) 1 ∩ SU) :=
    fun z hz => (hHU.2.2 z ⟨hz.2, hz.1⟩).symm
  have hAC : Set.EqOn (Hfun a b c) HL (Metric.ball (0 : ℂ) 1 ∩ SL) :=
    fun z hz => (hHL.2.2 z ⟨hz.2, hz.1⟩).symm
  have hBC : Set.EqOn HU HL (SU ∩ SL) := by
    intro z hz
    have h1 := hDj z hz
    have h2 : D z = 0 := by rw [hD0]; rfl
    rw [h2] at h1
    exact sub_eq_zero.mp h1.symm
  set F : ℂ → ℂ := glue3 (Metric.ball (0 : ℂ) 1) SU (Hfun a b c) HU HL with hFdef
  have hFball : Set.EqOn F (Hfun a b c) (Metric.ball (0 : ℂ) 1) := glue3_eqOn_A _ _ _ _ _
  have hFSU : Set.EqOn F HU SU := glue3_eqOn_B hAB
  have hFSL : Set.EqOn F HL SL := glue3_eqOn_C hAC hBC
  have hFd : DifferentiableOn ℂ F (Metric.ball (0 : ℂ) 1 ∪ SU ∪ SL) :=
    glue3_differentiableOn isOpen_ball isOpen_SU isOpen_SL hHfd hHU.1 hHL.1 hAB hAC hBC
  -- ## Geometry
  have hgeomU : Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 0 < z.im} ⊆ Metric.ball (0 : ℂ) 1 ∪ SU :=
    (geom_halfball_cover hδ1).1
  have hgeomL : Metric.ball (1 : ℂ) δ ∩ {z : ℂ | z.im < 0} ⊆ Metric.ball (0 : ℂ) 1 ∪ SL :=
    (geom_halfball_cover hδ1).2
  -- ## The two half-discs
  set ΩU : Set ℂ := Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 0 < z.im} with hΩUdef
  set ΩL : Set ℂ := Metric.ball (1 : ℂ) δ ∩ {z : ℂ | z.im < 0} with hΩLdef
  have hΩUo : IsOpen ΩU := by
    rw [hΩUdef]
    exact Metric.isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)
  have hΩLo : IsOpen ΩL := by
    rw [hΩLdef]
    exact Metric.isOpen_ball.inter (isOpen_lt Complex.continuous_im continuous_const)
  have hΩUc : IsPreconnected ΩU := by
    rw [hΩUdef]
    exact ((convex_ball (1 : ℂ) δ).inter (convex_halfSpace_im_gt (r := (0 : ℝ)))).isPreconnected
  have hΩLc : IsPreconnected ΩL := by
    rw [hΩLdef]
    exact ((convex_ball (1 : ℂ) δ).inter (convex_halfSpace_im_lt (r := (0 : ℝ)))).isPreconnected
  have hΩU_sub : ΩU ⊆ Metric.ball (0 : ℂ) 1 ∪ SU ∪ SL := by
    intro z hz
    rw [hΩUdef] at hz
    rcases hgeomU hz with h1 | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h1)
  have hΩL_sub : ΩL ⊆ Metric.ball (0 : ℂ) 1 ∪ SU ∪ SL := by
    intro z hz
    rw [hΩLdef] at hz
    rcases hgeomL hz with h1 | h1
    · exact Or.inl (Or.inl h1)
    · exact Or.inr h1
  -- ## The function `phi = F - e0 - e1 ell - e2 ell^2`
  have hphiU : DifferentiableOn ℂ (fun z => F z - e0 z - e1 z * ell z - e2 z * ell z ^ 2) ΩU := by
    have hFU : DifferentiableOn ℂ F ΩU := hFd.mono hΩU_sub
    have he0U : DifferentiableOn ℂ e0 ΩU :=
      he0.mono (by rw [hΩUdef]; exact Set.inter_subset_left)
    have he1U : DifferentiableOn ℂ e1 ΩU :=
      he1.mono (by rw [hΩUdef]; exact Set.inter_subset_left)
    have he2U : DifferentiableOn ℂ e2 ΩU :=
      he2d.mono (by rw [hΩUdef]; exact Set.inter_subset_left)
    have hellU : DifferentiableOn ℂ ell ΩU :=
      differentiableOn_ell_im_pos (fun z hz => by rw [hΩUdef] at hz; exact hz.2)
    exact ((hFU.sub he0U).sub (he1U.mul hellU)).sub (he2U.mul (hellU.pow 2))
  have hphiL : DifferentiableOn ℂ (fun z => F z - e0 z - e1 z * ell z - e2 z * ell z ^ 2) ΩL := by
    have hFL : DifferentiableOn ℂ F ΩL := hFd.mono hΩL_sub
    have he0L : DifferentiableOn ℂ e0 ΩL :=
      he0.mono (by rw [hΩLdef]; exact Set.inter_subset_left)
    have he1L : DifferentiableOn ℂ e1 ΩL :=
      he1.mono (by rw [hΩLdef]; exact Set.inter_subset_left)
    have he2L : DifferentiableOn ℂ e2 ΩL :=
      he2d.mono (by rw [hΩLdef]; exact Set.inter_subset_left)
    have hellL : DifferentiableOn ℂ ell ΩL :=
      differentiableOn_ell_im_neg (fun z hz => by rw [hΩLdef] at hz; exact hz.2)
    exact ((hFL.sub he0L).sub (he1L.mul hellL)).sub (he2L.mul (hellL.pow 2))
  have hphi_expand : ∀ z ∈ lens1 δ, Hfun a b c z = e0 z + e1 z * ell z + e2 z * ell z ^ 2 := by
    intro z hz
    have h1 := hid z hz
    rw [h1]
    simp only [he2def]
    ring
  -- auxiliary points in the two half-discs
  set zU : ℂ := ((1 - δ/4 : ℝ) : ℂ) + ((δ/4 : ℝ) : ℂ) * Complex.I with hzUdef
  set zL : ℂ := ((1 - δ/4 : ℝ) : ℂ) - ((δ/4 : ℝ) : ℂ) * Complex.I with hzLdef
  have hzU_im : 0 < zU.im := by
    rw [hzUdef]; simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, zero_add]; linarith
  have hzL_im : zL.im < 0 := by
    rw [hzLdef]; simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, zero_sub]; linarith
  have hzU_ball : zU ∈ Metric.ball (1 : ℂ) δ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have hre : (zU - 1).re = -δ/4 := by
      rw [hzUdef]; simp; try ring
    have him : (zU - 1).im = δ/4 := by
      rw [hzUdef]; simp; try ring
    have h := Complex.norm_le_abs_re_add_abs_im (zU - 1)
    rw [hre, him] at h
    have : |(-δ/4 : ℝ)| + |δ/4| = δ/2 := by
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]; ring
    rw [this] at h
    linarith
  have hzL_ball : zL ∈ Metric.ball (1 : ℂ) δ := by
    rw [Metric.mem_ball, Complex.dist_eq]
    have hre : (zL - 1).re = -δ/4 := by
      rw [hzLdef]; simp; try ring
    have him : (zL - 1).im = -δ/4 := by
      rw [hzLdef]; simp; try ring
    have h := Complex.norm_le_abs_re_add_abs_im (zL - 1)
    rw [hre, him] at h
    have : |(-δ/4 : ℝ)| + |(-δ/4 : ℝ)| = δ/2 := by
      rw [abs_of_nonpos (by linarith)]; ring
    rw [this] at h
    linarith
  have hzU_unit : zU ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
    have hsq : ‖zU‖ ^ 2 < 1 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hre : zU.re = 1 - δ/4 := by rw [hzUdef]; simp; try ring
      have him : zU.im = δ/4 := by rw [hzUdef]; simp; try ring
      rw [hre, him]; nlinarith [hδ0, hδ89]
    have hlt := sq_lt_sq.mp (show ‖zU‖ ^ 2 < (1 : ℝ) ^ 2 by rw [one_pow]; exact hsq)
    simpa [abs_of_nonneg (norm_nonneg zU)] using hlt
  have hzL_unit : zL ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, Complex.dist_eq, sub_zero]
    have hsq : ‖zL‖ ^ 2 < 1 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have hre : zL.re = 1 - δ/4 := by rw [hzLdef]; simp; try ring
      have him : zL.im = -(δ/4) := by rw [hzLdef]; simp; try ring
      rw [hre, him]; nlinarith [hδ0, hδ89]
    have hlt := sq_lt_sq.mp (show ‖zL‖ ^ 2 < (1 : ℝ) ^ 2 by rw [one_pow]; exact hsq)
    simpa [abs_of_nonneg (norm_nonneg zL)] using hlt
  have hzU_lens : zU ∈ lens1 δ := ⟨hzU_ball, hzU_unit⟩
  have hzL_lens : zL ∈ lens1 δ := ⟨hzL_ball, hzL_unit⟩
  -- ## Vanishing of `phi` on the two half-discs
  have hphi0U : ∀ z ∈ Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 0 < z.im},
      F z - e0 z - e1 z * ell z - e2 z * ell z ^ 2 = 0 := by
    have hev : (fun z => F z - e0 z - e1 z * ell z - e2 z * ell z ^ 2) =ᶠ[𝓝 zU] 0 := by
      filter_upwards [(isOpen_lens1 δ).mem_nhds hzU_lens] with z hz
      simp only [Pi.zero_apply]
      rw [hFball hz.2, hphi_expand z hz]
      ring
    exact (hphiU.analyticOnNhd hΩUo).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hΩUc ⟨hzU_ball, hzU_im⟩ hev
  have hphi0L : ∀ z ∈ Metric.ball (1 : ℂ) δ ∩ {z : ℂ | z.im < 0},
      F z - e0 z - e1 z * ell z - e2 z * ell z ^ 2 = 0 := by
    have hev : (fun z => F z - e0 z - e1 z * ell z - e2 z * ell z ^ 2) =ᶠ[𝓝 zL] 0 := by
      filter_upwards [(isOpen_lens1 δ).mem_nhds hzL_lens] with z hz
      simp only [Pi.zero_apply]
      rw [hFball hz.2, hphi_expand z hz]
      ring
    exact (hphiL.analyticOnNhd hΩLo).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hΩLc ⟨hzL_ball, hzL_im⟩ hev
  -- ## Boundary values
  have hbu : ∀ t ∈ Set.Ioo (1 : ℝ) (1 + ε),
      F (t : ℂ) - e0 (t : ℂ)
        - e1 (t : ℂ) * (((Real.log (t - 1) : ℝ) : ℂ) - Real.pi * Complex.I)
        - e2 (t : ℂ) * ((((Real.log (t - 1) : ℝ) : ℂ) - Real.pi * Complex.I) ^ 2) = 0 := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht.1
    have htlt : t - 1 < ε := by linarith [ht.2]
    have ht_ball : (t : ℂ) ∈ Metric.ball (1 : ℂ) δ := by
      rw [Metric.mem_ball, Complex.dist_eq]
      have h : ‖(t : ℂ) - 1‖ = t - 1 := by
        have h1 : (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) := by push_cast; ring
        rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      rw [h]; linarith
    have ht_SU : (t : ℂ) ∈ SU := by
      show (1 - (t : ℂ).re) / 8 < (t : ℂ).im
      simp only [Complex.ofReal_re, Complex.ofReal_im]
      linarith
    have hFcont : ContinuousAt F (t : ℂ) :=
      ContinuousAt.congr (hHU.1.continuousOn.continuousAt (isOpen_SU.mem_nhds ht_SU))
        (Filter.eventuallyEq_of_mem (isOpen_SU.mem_nhds ht_SU) (fun z hz => (hFSU hz).symm))
    have hcast : Tendsto (fun s : ℝ => (t : ℂ) + (s : ℂ) * Complex.I)
        (𝓝[>] (0 : ℝ)) (𝓝 (t : ℂ)) := by
      have h0 : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (fun s : ℝ => (t : ℂ) + (s : ℂ) * Complex.I) (𝓝[>] (0 : ℝ))
          (𝓝 ((t : ℂ) + 0 * Complex.I)) :=
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (t : ℂ)) (𝓝[>] (0 : ℝ))
          (𝓝 (t : ℂ))).add (h0.mul_const Complex.I)
      simpa using h2
    have hloglim : Tendsto (fun s : ℝ => ell ((t : ℂ) + (s : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 (((Real.log (t - 1) : ℝ) : ℂ) - Real.pi * Complex.I)) := by
      have h := (log_one_sub_jump t ht1).1
      simpa [ell] using h
    have he0t : Tendsto (fun s : ℝ => e0 ((t : ℂ) + (s : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 (e0 (t : ℂ))) :=
      ((he0.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds ht_ball)).tendsto).comp hcast
    have he1t : Tendsto (fun s : ℝ => e1 ((t : ℂ) + (s : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 (e1 (t : ℂ))) :=
      ((he1.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds ht_ball)).tendsto).comp hcast
    have he2t : Tendsto (fun s : ℝ => e2 ((t : ℂ) + (s : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 (e2 (t : ℂ))) :=
      ((he2d.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds ht_ball)).tendsto).comp hcast
    have hFt : Tendsto (fun s : ℝ => F ((t : ℂ) + (s : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 (F (t : ℂ))) := hFcont.tendsto.comp hcast
    have hlim : Tendsto (fun s : ℝ => F ((t : ℂ) + (s : ℂ) * Complex.I)
          - e0 ((t : ℂ) + (s : ℂ) * Complex.I)
          - e1 ((t : ℂ) + (s : ℂ) * Complex.I) * ell ((t : ℂ) + (s : ℂ) * Complex.I)
          - e2 ((t : ℂ) + (s : ℂ) * Complex.I) * ell ((t : ℂ) + (s : ℂ) * Complex.I) ^ 2)
        (𝓝[>] (0 : ℝ))
        (𝓝 (F (t : ℂ) - e0 (t : ℂ)
          - e1 (t : ℂ) * (((Real.log (t - 1) : ℝ) : ℂ) - Real.pi * Complex.I)
          - e2 (t : ℂ) * ((((Real.log (t - 1) : ℝ) : ℂ) - Real.pi * Complex.I) ^ 2))) :=
      ((hFt.sub he0t).sub (he1t.mul hloglim)).sub (he2t.mul (hloglim.pow 2))
    have hlim0 : Tendsto (fun s : ℝ => F ((t : ℂ) + (s : ℂ) * Complex.I)
          - e0 ((t : ℂ) + (s : ℂ) * Complex.I)
          - e1 ((t : ℂ) + (s : ℂ) * Complex.I) * ell ((t : ℂ) + (s : ℂ) * Complex.I)
          - e2 ((t : ℂ) + (s : ℂ) * Complex.I) * ell ((t : ℂ) + (s : ℂ) * Complex.I) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine Tendsto.congr' ?_ (tendsto_const_nhds)
      have hlt : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s < δ/2 :=
        (eventually_lt_nhds (by linarith : (0 : ℝ) < δ/2)).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, hlt] with s hs hlt'
      have hs0 : (0 : ℝ) < s := hs
      have hmem : (t : ℂ) + (s : ℂ) * Complex.I ∈ Metric.ball (1 : ℂ) δ ∩ {z : ℂ | 0 < z.im} := by
        constructor
        · rw [Metric.mem_ball, Complex.dist_eq]
          have h := Complex.norm_le_abs_re_add_abs_im ((t : ℂ) + (s : ℂ) * Complex.I - 1)
          have hre : ((t : ℂ) + (s : ℂ) * Complex.I - 1).re = t - 1 := by simp; try ring
          have him : ((t : ℂ) + (s : ℂ) * Complex.I - 1).im = s := by simp; try ring
          rw [hre, him] at h
          have h2 : |t - 1| + |s| = (t - 1) + s := by
            rw [abs_of_pos (by linarith), abs_of_pos hs]
          rw [h2] at h
          rw [hεdef] at htlt
          linarith
        · show 0 < ((t : ℂ) + (s : ℂ) * Complex.I).im
          rw [show ((t : ℂ) + (s : ℂ) * Complex.I).im = s by simp]
          exact hs
      have := hphi0U _ hmem
      simpa only [Pi.zero_apply] using this.symm
    exact tendsto_nhds_unique hlim hlim0
  have hbl : ∀ t ∈ Set.Ioo (1 : ℝ) (1 + ε),
      F (t : ℂ) - e0 (t : ℂ)
        - e1 (t : ℂ) * (((Real.log (t - 1) : ℝ) : ℂ) + Real.pi * Complex.I)
        - e2 (t : ℂ) * ((((Real.log (t - 1) : ℝ) : ℂ) + Real.pi * Complex.I) ^ 2) = 0 := by
    intro t ht
    have ht1 : (1 : ℝ) < t := ht.1
    have htlt : t - 1 < ε := by linarith [ht.2]
    have ht_SU : (t : ℂ) ∈ SU := by
      show (1 - (t : ℂ).re) / 8 < (t : ℂ).im
      simp only [Complex.ofReal_re, Complex.ofReal_im]
      linarith
    have hFcont : ContinuousAt F (t : ℂ) :=
      ContinuousAt.congr (hHU.1.continuousOn.continuousAt (isOpen_SU.mem_nhds ht_SU))
        (Filter.eventuallyEq_of_mem (isOpen_SU.mem_nhds ht_SU) (fun z hz => (hFSU hz).symm))
    have ht_ball : (t : ℂ) ∈ Metric.ball (1 : ℂ) δ := by
      rw [Metric.mem_ball, Complex.dist_eq]
      have h : ‖(t : ℂ) - 1‖ = t - 1 := by
        have h1 : (t : ℂ) - 1 = ((t - 1 : ℝ) : ℂ) := by push_cast; ring
        rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      rw [h]; linarith
    have hcast : Tendsto (fun s : ℝ => (t : ℂ) - (s : ℂ) * Complex.I)
        (𝓝[>] (0 : ℝ)) (𝓝 (t : ℂ)) := by
      have h0 : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
        (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
      have h2 : Tendsto (fun s : ℝ => (t : ℂ) - (s : ℂ) * Complex.I) (𝓝[>] (0 : ℝ))
          (𝓝 ((t : ℂ) - 0 * Complex.I)) :=
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (t : ℂ)) (𝓝[>] (0 : ℝ))
          (𝓝 (t : ℂ))).sub (h0.mul_const Complex.I)
      simpa using h2
    have hloglim : Tendsto (fun s : ℝ => ell ((t : ℂ) - (s : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 (((Real.log (t - 1) : ℝ) : ℂ) + Real.pi * Complex.I)) := by
      have h := (log_one_sub_jump t ht1).2
      simpa [ell] using h
    have he0t : Tendsto (fun s : ℝ => e0 ((t : ℂ) - (s : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 (e0 (t : ℂ))) :=
      ((he0.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds ht_ball)).tendsto).comp hcast
    have he1t : Tendsto (fun s : ℝ => e1 ((t : ℂ) - (s : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 (e1 (t : ℂ))) :=
      ((he1.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds ht_ball)).tendsto).comp hcast
    have he2t : Tendsto (fun s : ℝ => e2 ((t : ℂ) - (s : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 (e2 (t : ℂ))) :=
      ((he2d.continuousOn.continuousAt (Metric.isOpen_ball.mem_nhds ht_ball)).tendsto).comp hcast
    have hFt : Tendsto (fun s : ℝ => F ((t : ℂ) - (s : ℂ) * Complex.I)) (𝓝[>] (0 : ℝ))
        (𝓝 (F (t : ℂ))) := hFcont.tendsto.comp hcast
    have hlim : Tendsto (fun s : ℝ => F ((t : ℂ) - (s : ℂ) * Complex.I)
          - e0 ((t : ℂ) - (s : ℂ) * Complex.I)
          - e1 ((t : ℂ) - (s : ℂ) * Complex.I) * ell ((t : ℂ) - (s : ℂ) * Complex.I)
          - e2 ((t : ℂ) - (s : ℂ) * Complex.I) * ell ((t : ℂ) - (s : ℂ) * Complex.I) ^ 2)
        (𝓝[>] (0 : ℝ))
        (𝓝 (F (t : ℂ) - e0 (t : ℂ)
          - e1 (t : ℂ) * (((Real.log (t - 1) : ℝ) : ℂ) + Real.pi * Complex.I)
          - e2 (t : ℂ) * ((((Real.log (t - 1) : ℝ) : ℂ) + Real.pi * Complex.I) ^ 2))) :=
      ((hFt.sub he0t).sub (he1t.mul hloglim)).sub (he2t.mul (hloglim.pow 2))
    have hlim0 : Tendsto (fun s : ℝ => F ((t : ℂ) - (s : ℂ) * Complex.I)
          - e0 ((t : ℂ) - (s : ℂ) * Complex.I)
          - e1 ((t : ℂ) - (s : ℂ) * Complex.I) * ell ((t : ℂ) - (s : ℂ) * Complex.I)
          - e2 ((t : ℂ) - (s : ℂ) * Complex.I) * ell ((t : ℂ) - (s : ℂ) * Complex.I) ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine Tendsto.congr' ?_ (tendsto_const_nhds)
      have hlt : ∀ᶠ s : ℝ in 𝓝[>] (0 : ℝ), s < δ/2 :=
        (eventually_lt_nhds (by linarith : (0 : ℝ) < δ/2)).filter_mono nhdsWithin_le_nhds
      filter_upwards [self_mem_nhdsWithin, hlt] with s hs hlt'
      have hs0 : (0 : ℝ) < s := hs
      have hmem : (t : ℂ) - (s : ℂ) * Complex.I ∈ Metric.ball (1 : ℂ) δ ∩ {z : ℂ | z.im < 0} := by
        constructor
        · rw [Metric.mem_ball, Complex.dist_eq]
          have h := Complex.norm_le_abs_re_add_abs_im ((t : ℂ) - (s : ℂ) * Complex.I - 1)
          have hre : ((t : ℂ) - (s : ℂ) * Complex.I - 1).re = t - 1 := by simp; try ring
          have him : ((t : ℂ) - (s : ℂ) * Complex.I - 1).im = -s := by simp; try ring
          rw [hre, him] at h
          have h2 : |t - 1| + |(-s)| = (t - 1) + s := by
            rw [abs_of_pos (by linarith), abs_neg, abs_of_pos hs]
          rw [h2] at h
          rw [hεdef] at htlt
          linarith
        · show ((t : ℂ) - (s : ℂ) * Complex.I).im < 0
          rw [show ((t : ℂ) - (s : ℂ) * Complex.I).im = -s by simp]
          linarith
      have := hphi0L _ hmem
      simpa only [Pi.zero_apply] using this.symm
    exact tendsto_nhds_unique hlim hlim0
  -- ## The key real identity
  have hmain : ∀ t ∈ Set.Ioo (1 : ℝ) (1 + ε),
      e1 (t : ℂ) + 2 * e2 (t : ℂ) * (((Real.log (t - 1) : ℝ)) : ℂ) = 0 := by
    intro t ht
    have hu := hbu t ht
    have hl := hbl t ht
    set L : ℂ := ((Real.log (t - 1) : ℝ) : ℂ) with hL
    set P : ℂ := Real.pi * Complex.I with hP
    have hsub : e1 (t : ℂ) * ((L - P) - (L + P)) + e2 (t : ℂ) * ((L - P) ^ 2 - (L + P) ^ 2) = 0 := by
      have hu' : F (t : ℂ) - e0 (t : ℂ) - e1 (t : ℂ) * (L - P) - e2 (t : ℂ) * (L - P) ^ 2 = 0 := by
        simpa [hL, hP] using hu
      have hl' : F (t : ℂ) - e0 (t : ℂ) - e1 (t : ℂ) * (L + P) - e2 (t : ℂ) * (L + P) ^ 2 = 0 := by
        simpa [hL, hP] using hl
      linear_combination hl' - hu'
    have hL1 : (L - P) - (L + P) = -(2 * P) := by ring
    have hL2 : (L - P) ^ 2 - (L + P) ^ 2 = -(4 * P) * L := by ring
    rw [hL1, hL2] at hsub
    have hPne : -(2 * P) ≠ 0 := by
      rw [hP]; simp [Complex.ext_iff, Real.pi_ne_zero]
    have key : -(2 * P) * (e1 (t : ℂ) + 2 * e2 (t : ℂ) * L) = 0 := by
      linear_combination hsub
    rw [mul_eq_zero] at key
    rcases key with hk | hk
    · exact absurd hk hPne
    · rw [hL] at hk; exact hk
  -- ## The two cases
  rcases eq_or_ne c 0 with hc | hc
  · -- `c = 0`
    have he2z : e2 = 0 := by
      funext z
      rw [he2def]
      simp [hc]
    have hzero : ∀ t ∈ Set.Ioo (1 : ℝ) (1 + ε), e1 (t : ℂ) = 0 := by
      intro t ht
      have := hmain t ht
      rw [he2z] at this
      simpa using this
    have he1z : ∀ z ∈ Metric.ball (1 : ℂ) δ, e1 z = 0 :=
      eqOn_zero_of_ball_of_Ioo hδ0 hε0 he1 hzero
    refine absurd ⟨e0, δ, hδ0, he0, ?_⟩ (H_not_holo_at_one a b c h hb hc)
    intro z hz
    have h1 := hid z hz
    rw [h1, he1z z hz.1]
    simp [hc]
  · -- `c ≠ 0`
    refine log_growth_contra hδ0 hε0 he1 he2d ?_ hmain
    have he2one : e2 1 = -((c : ℂ) / 16) := by
      rw [he2def]
      show (-((c : ℂ) / 16)) * uh 1 = -((c : ℂ) / 16)
      rw [huh1, mul_one]
    rw [he2one, neg_ne_zero, div_ne_zero_iff]
    exact ⟨Int.cast_ne_zero.mpr hc, by norm_num⟩

end Work.A14D
