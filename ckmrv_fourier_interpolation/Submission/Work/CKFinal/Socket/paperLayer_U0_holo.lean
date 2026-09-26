import Mathlib
import Submission.Work.CKFinal.Socket.Basic
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.CKFinal.mdifferentiableOn_paperLayer_of_cleanBall
import Submission.Work.CKFinal.orbit_imagAxis_of_mem_U0
import Submission.Work.Asymptotics.removable_vertical_line
import Submission.Work.Modular.mdifferentiable_S_smul
import Submission.Work.CKFinal.Socket.paperLayer_continuous_axis
import Submission.Work.CKFinal.Socket.paperLayer_continuous_arc

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold MatrixGroups

namespace Work.CKFinal.Socket

/-! ## elementary geometry -/

private lemma imagAxis_coe_re_zero (t : ℝ) (ht : 0 < t) :
    (((Work.Kernels.imagAxis t ht : ℍ)) : ℂ).re = 0 := by
  simp [Work.Kernels.imagAxis]

private lemma norm_sub_half_sq (x : ℍ) :
    ‖(x : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (x.re - 1 / 2) ^ 2 + x.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

private lemma norm_add_half_sq (x : ℍ) :
    ‖(x : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (x.re + 1 / 2) ^ 2 + x.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, add_zero,
    UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  norm_num
  ring

private lemma OnArc_re_ne_zero {x : ℍ} (h : Work.CKFinal.OnArc x) : x.re ≠ 0 := by
  intro hre
  rcases h with h | h
  · have hh : ((1 : ℝ) / 2) ^ 2 = (x.re - 1 / 2) ^ 2 + x.im ^ 2 := by
      rw [← norm_sub_half_sq x, h]
    rw [hre] at hh
    nlinarith [x.im_pos]
  · have hh : ((1 : ℝ) / 2) ^ 2 = (x.re + 1 / 2) ^ 2 + x.im ^ 2 := by
      rw [← norm_add_half_sq x, h]
    rw [hre] at hh
    nlinarith [x.im_pos]

private theorem jInvariantFun_ne_imagAxis_of_mem_U0 {z : ℍ} (hz : z ∈ U0) (hre : z.re ≠ 0)
    (ha1 : ‖(z : ℂ) - (1 / 2 : ℂ)‖ ≠ 1 / 2) (ha2 : ‖(z : ℂ) + (1 / 2 : ℂ)‖ ≠ 1 / 2)
    (t : ℝ) (ht : 0 < t) :
    Work.Kernels.jInvariantFun z ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro h
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq h
  have hz' : γ⁻¹ • z = Work.Kernels.imagAxis t ht := by rw [← hγ]; simp
  have hzero : ((γ⁻¹ • z : ℍ) : ℂ).re = 0 := by rw [hz']; exact imagAxis_coe_re_zero t ht
  rcases Work.CKFinal.orbit_imagAxis_of_mem_U0 z hz γ⁻¹ hzero with h1 | h1 | h1
  · exact hre h1
  · exact ha1 h1
  · exact ha2 h1

private theorem exists_clean_closedBall_of_mem_U0 {z : ℍ} (hz : z ∈ U0) (hre : z.re ≠ 0)
    (ha1 : ‖(z : ℂ) - (1 / 2 : ℂ)‖ ≠ 1 / 2) (ha2 : ‖(z : ℂ) + (1 / 2 : ℂ)‖ ≠ 1 / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.closedBall z ρ ⊆ U0 ∧ Work.CKFinal.CleanOnClosedBall z ρ := by
  obtain ⟨ρ₁, hρ₁, hB₁⟩ := Metric.mem_nhds_iff.mp (Work.CKFinal.isOpen_U0.mem_nhds hz)
  have hcl2 : IsClosed {τ : ℍ | τ.re = 0} :=
    isClosed_eq UpperHalfPlane.continuous_re continuous_const
  obtain ⟨ρ₂, hρ₂, hB₂⟩ := Metric.mem_nhds_iff.mp (hcl2.isOpen_compl.mem_nhds hre)
  have hcl3 : IsClosed {τ : ℍ | ‖(τ : ℂ) - (1 / 2 : ℂ)‖ = 1 / 2} :=
    isClosed_eq (by fun_prop) continuous_const
  obtain ⟨ρ₃, hρ₃, hB₃⟩ := Metric.mem_nhds_iff.mp (hcl3.isOpen_compl.mem_nhds ha1)
  have hcl4 : IsClosed {τ : ℍ | ‖(τ : ℂ) + (1 / 2 : ℂ)‖ = 1 / 2} :=
    isClosed_eq (by fun_prop) continuous_const
  obtain ⟨ρ₄, hρ₄, hB₄⟩ := Metric.mem_nhds_iff.mp (hcl4.isOpen_compl.mem_nhds ha2)
  have hρm : 0 < min (min ρ₁ ρ₂) (min ρ₃ ρ₄) := lt_min (lt_min hρ₁ hρ₂) (lt_min hρ₃ hρ₄)
  have hm1 : min (min ρ₁ ρ₂) (min ρ₃ ρ₄) ≤ ρ₁ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hm2 : min (min ρ₁ ρ₂) (min ρ₃ ρ₄) ≤ ρ₂ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hm3 : min (min ρ₁ ρ₂) (min ρ₃ ρ₄) ≤ ρ₃ := le_trans (min_le_right _ _) (min_le_left _ _)
  have hm4 : min (min ρ₁ ρ₂) (min ρ₃ ρ₄) ≤ ρ₄ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hlt : ∀ {y : ℍ}, dist y z ≤ min (min ρ₁ ρ₂) (min ρ₃ ρ₄) / 2 →
      dist y z < min (min ρ₁ ρ₂) (min ρ₃ ρ₄) := fun hy => by linarith
  refine ⟨min (min ρ₁ ρ₂) (min ρ₃ ρ₄) / 2, by positivity, ?_, ?_⟩
  · intro y hy
    exact hB₁ (lt_of_lt_of_le (hlt (Metric.mem_closedBall.mp hy)) hm1)
  · intro t ht y hy
    have hd := hlt (Metric.mem_closedBall.mp hy)
    have hysub : y ∈ U0 := hB₁ (lt_of_lt_of_le hd hm1)
    have hyre : y.re ≠ 0 := hB₂ (lt_of_lt_of_le hd hm2)
    have hya1 : ‖(y : ℂ) - (1 / 2 : ℂ)‖ ≠ 1 / 2 := hB₃ (lt_of_lt_of_le hd hm3)
    have hya2 : ‖(y : ℂ) + (1 / 2 : ℂ)‖ ≠ 1 / 2 := hB₄ (lt_of_lt_of_le hd hm4)
    exact jInvariantFun_ne_imagAxis_of_mem_U0 hysub hyre hya1 hya2 t ht

private theorem ball_holo_of_clean (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) {z : ℍ} (hz : z ∈ U0) (hre : z.re ≠ 0)
    (ha1 : ‖(z : ℂ) - (1 / 2 : ℂ)‖ ≠ 1 / 2) (ha2 : ‖(z : ℂ) + (1 / 2 : ℂ)‖ ≠ 1 / 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z ρ ⊆ U0 ∧
      MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : ℍ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
        (Metric.ball z ρ) := by
  obtain ⟨ρ, hρ, hsub, hclean⟩ := exists_clean_closedBall_of_mem_U0 hz hre ha1 ha2
  exact ⟨ρ, hρ, fun y hy => hsub (Metric.ball_subset_closedBall hy),
    Work.CKFinal.mdifferentiableOn_paperLayer_of_cleanBall ℓ d hd r hρ hclean⟩

/-! ## the transport of holomorphy across a vertical line by `S` -/

private lemma continuous_S : Continuous fun τ : ℍ => ModularGroup.S • τ :=
  Work.Modular.mdifferentiable_S_smul.continuous

private lemma S_S (τ : ℍ) : ModularGroup.S • (ModularGroup.S • τ) = τ := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_S_smul]
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  field_simp

private lemma re_S_smul_of_arc_left {v : ℍ} (h : ‖(v : ℂ) - (1 / 2 : ℂ)‖ = 1 / 2) :
    (ModularGroup.S • v).re = -1 := by
  have hv : (v : ℂ) ≠ 0 := v.ne_zero
  have hsq : v.re ^ 2 + v.im ^ 2 = v.re := by
    have h1 := norm_sub_half_sq v
    rw [h] at h1
    nlinarith [h1]
  have hre : v.re ≠ 0 := fun h0 => by
    rw [h0] at hsq; nlinarith [sq_nonneg v.im, v.im_pos]
  have hnorm : Complex.normSq (v : ℂ) = v.re := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    nlinarith [hsq]
  rw [← UpperHalfPlane.coe_re]
  rw [UpperHalfPlane.modular_S_smul, Complex.inv_re, Complex.neg_re,
    Complex.normSq_neg, hnorm]
  field_simp
  rw [UpperHalfPlane.coe_re]

private lemma re_S_smul_of_arc_right {v : ℍ} (h : ‖(v : ℂ) + (1 / 2 : ℂ)‖ = 1 / 2) :
    (ModularGroup.S • v).re = 1 := by
  have hv : (v : ℂ) ≠ 0 := v.ne_zero
  have hsq : v.re ^ 2 + v.im ^ 2 = -v.re := by
    have h1 := norm_add_half_sq v
    rw [h] at h1
    nlinarith [h1]
  have hre : v.re ≠ 0 := fun h0 => by
    rw [h0] at hsq; nlinarith [sq_nonneg v.im, v.im_pos]
  have hnorm : Complex.normSq (v : ℂ) = -v.re := by
    rw [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    nlinarith [hsq]
  rw [← UpperHalfPlane.coe_re]
  rw [UpperHalfPlane.modular_S_smul, Complex.inv_re, Complex.neg_re,
    Complex.normSq_neg, hnorm]
  field_simp
  rw [UpperHalfPlane.coe_re]

private theorem mdiff_transport_S (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ)
    {x : ℍ} {ρ c : ℝ} (hρ : 0 < ρ)
    (hcont : ContinuousOn (fun τ : ℍ =>
      Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) (Metric.ball x ρ))
    (hclean : ∀ y ∈ Metric.ball x ρ, Work.CKFinal.OnArc y → (ModularGroup.S • y).re = c)
    (hU0 : ∀ y ∈ Metric.ball x ρ, y ∈ U0)
    (hre : ∀ y ∈ Metric.ball x ρ, y.re ≠ 0) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : ℍ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
      (Metric.ball x ρ) := by
  classical
  set U : Set ℍ := Metric.ball x ρ with hUdef
  have hUopen : IsOpen U := Metric.isOpen_ball
  set W : Set ℍ := (fun v : ℍ => ModularGroup.S • v) ⁻¹' U with hWdef
  have hWopen : IsOpen W := hUopen.preimage continuous_S
  set g : ℍ → ℂ := fun v =>
    Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d (ModularGroup.S • v) r
    with hgdef
  have hSU : ∀ v ∈ W, ModularGroup.S • v ∈ U := fun v hv => hv
  have hcontg : ContinuousOn g W := by
    intro v hv
    have hy : ModularGroup.S • v ∈ U := hSU v hv
    exact ((hcont.continuousAt (hUopen.mem_nhds hy)).comp
      continuous_S.continuousAt).continuousWithinAt
  have hgdiff : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      g (W \ {v : ℍ | v.re = c}) := by
    intro v hv
    have hvW : v ∈ W := hv.1
    have hvc : v.re ≠ c := hv.2
    have hy : ModularGroup.S • v ∈ U := hSU v hvW
    have hU0y : ModularGroup.S • v ∈ U0 := hU0 _ hy
    have hrey : (ModularGroup.S • v).re ≠ 0 := hre _ hy
    have hnotarc : ¬ Work.CKFinal.OnArc (ModularGroup.S • v) := by
      intro harc
      have h1 : (ModularGroup.S • (ModularGroup.S • v)).re = c := hclean _ hy harc
      rw [S_S v] at h1
      exact hvc h1
    have ha1 : ‖(((ModularGroup.S • v : ℍ)) : ℂ) - (1 / 2 : ℂ)‖ ≠ 1 / 2 := by
      intro h; exact hnotarc (Or.inl h)
    have ha2 : ‖(((ModularGroup.S • v : ℍ)) : ℂ) + (1 / 2 : ℂ)‖ ≠ 1 / 2 := by
      intro h; exact hnotarc (Or.inr h)
    obtain ⟨ρy, hρy, -, hmdy⟩ := ball_holo_of_clean ℓ d hd r hU0y hrey ha1 ha2
    have hAt : MDifferentiableAt (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : ℍ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
        (ModularGroup.S • v) :=
      hmdy.mdifferentiableAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρy))
    exact ((hAt.comp v (Work.Modular.mdifferentiable_S_smul v)).mdifferentiableWithinAt)
  have hgmd : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) g W :=
    Work.Asymptotics.removable_vertical_line hWopen c hcontg hgdiff
  have hSmd : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : ℍ => ModularGroup.S • τ) U :=
    Work.Modular.mdifferentiable_S_smul.mdifferentiableOn
  have hcomp : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : ℍ => g (ModularGroup.S • τ)) U :=
    MDifferentiableOn.comp (I := modelWithCornersSelf ℂ ℂ) (I' := modelWithCornersSelf ℂ ℂ)
      (I'' := modelWithCornersSelf ℂ ℂ) (u := W) (s := U)
      hgmd hSmd (fun τ hτ => by
        show ModularGroup.S • τ ∈ W
        show ModularGroup.S • (ModularGroup.S • τ) ∈ U
        rw [S_S τ]; exact hτ)
  have hfun : (fun τ : ℍ => g (ModularGroup.S • τ))
      = fun τ : ℍ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r := by
    funext τ; simp only [hgdef, S_S]
  rwa [hfun] at hcomp

/-! ## holomorphy on a ball at a point of the imaginary axis -/

private theorem ball_holo_of_axis (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) {x : ℍ} (hx : x ∈ U0) (haxis : x.re = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ U0 ∧
      MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : ℍ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
        (Metric.ball x ρ) := by
  obtain ⟨ρ₁, hρ₁, hsub₁, hcont⟩ := paperLayer_continuous_axis ℓ d hd r hx haxis
  have hnotarc : ¬ Work.CKFinal.OnArc x := fun h => OnArc_re_ne_zero h haxis
  have ha1 : ‖(x : ℂ) - (1 / 2 : ℂ)‖ ≠ 1 / 2 := fun h => hnotarc (Or.inl h)
  have ha2 : ‖(x : ℂ) + (1 / 2 : ℂ)‖ ≠ 1 / 2 := fun h => hnotarc (Or.inr h)
  have hcl3 : IsClosed {τ : ℍ | ‖(τ : ℂ) - (1 / 2 : ℂ)‖ = 1 / 2} :=
    isClosed_eq (by fun_prop) continuous_const
  obtain ⟨ρ₂, hρ₂, hB₂⟩ := Metric.mem_nhds_iff.mp (hcl3.isOpen_compl.mem_nhds ha1)
  have hcl4 : IsClosed {τ : ℍ | ‖(τ : ℂ) + (1 / 2 : ℂ)‖ = 1 / 2} :=
    isClosed_eq (by fun_prop) continuous_const
  obtain ⟨ρ₃, hρ₃, hB₃⟩ := Metric.mem_nhds_iff.mp (hcl4.isOpen_compl.mem_nhds ha2)
  set ρ := min ρ₁ (min ρ₂ ρ₃) / 2 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; positivity
  have hle1 : ρ ≤ ρ₁ := by rw [hρdef]; linarith [min_le_left ρ₁ (min ρ₂ ρ₃)]
  have hle2 : ρ ≤ ρ₂ := by
    rw [hρdef]; linarith [min_le_left ρ₁ (min ρ₂ ρ₃), min_le_right ρ₁ (min ρ₂ ρ₃),
      min_le_left ρ₂ ρ₃]
  have hle3 : ρ ≤ ρ₃ := by
    rw [hρdef]; linarith [min_le_left ρ₁ (min ρ₂ ρ₃), min_le_right ρ₁ (min ρ₂ ρ₃),
      min_le_right ρ₂ ρ₃]
  refine ⟨ρ, hρpos, fun y hy => hsub₁ (Metric.ball_subset_ball hle1 hy), ?_⟩
  have hcont' : ContinuousOn (fun τ : ℍ =>
      Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) (Metric.ball x ρ) :=
    hcont.mono (Metric.ball_subset_ball hle1)
  have hoff : MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : ℍ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
      (Metric.ball x ρ \ {z : ℍ | z.re = 0}) := by
    intro y hy
    have hyball : y ∈ Metric.ball x ρ := hy.1
    have hyre : y.re ≠ 0 := hy.2
    have hdist : dist y x < ρ := Metric.mem_ball.mp hyball
    have hyU0 : y ∈ U0 := hsub₁ (Metric.ball_subset_ball hle1 hyball)
    have hya1 : ‖(y : ℂ) - (1 / 2 : ℂ)‖ ≠ 1 / 2 :=
      hB₂ (Metric.mem_ball.mpr (lt_of_lt_of_le hdist hle2))
    have hya2 : ‖(y : ℂ) + (1 / 2 : ℂ)‖ ≠ 1 / 2 :=
      hB₃ (Metric.mem_ball.mpr (lt_of_lt_of_le hdist hle3))
    obtain ⟨ρy, hρy, -, hmdy⟩ := ball_holo_of_clean ℓ d hd r hyU0 hyre hya1 hya2
    exact (hmdy.mdifferentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρy))).mdifferentiableWithinAt
  exact Work.Asymptotics.removable_vertical_line Metric.isOpen_ball 0 hcont' hoff

/-! ## holomorphy on a ball at a point of one of the two bottom arcs -/

private theorem ball_holo_of_arc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) {x : ℍ} (hx : x ∈ U0) (harc : Work.CKFinal.OnArc x) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ U0 ∧
      MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
        (fun τ : ℍ => Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
        (Metric.ball x ρ) := by
  obtain ⟨ρ₁, hρ₁, hsub₁, hcont⟩ := paperLayer_continuous_arc ℓ d hd r hx harc
  have hxre : x.re ≠ 0 := OnArc_re_ne_zero harc
  have hcl2 : IsClosed {τ : ℍ | τ.re = 0} :=
    isClosed_eq UpperHalfPlane.continuous_re continuous_const
  obtain ⟨ρ₂, hρ₂, hB₂⟩ := Metric.mem_nhds_iff.mp (hcl2.isOpen_compl.mem_nhds hxre)
  have hcl1 : IsClosed {τ : ℍ | ‖(τ : ℂ) - (1 / 2 : ℂ)‖ = 1 / 2} :=
    isClosed_eq (by fun_prop) continuous_const
  have hcl4 : IsClosed {τ : ℍ | ‖(τ : ℂ) + (1 / 2 : ℂ)‖ = 1 / 2} :=
    isClosed_eq (by fun_prop) continuous_const
  have hnotboth : ¬ (‖(x : ℂ) - (1 / 2 : ℂ)‖ = 1 / 2 ∧ ‖(x : ℂ) + (1 / 2 : ℂ)‖ = 1 / 2) := by
    rintro ⟨h₁', h₂'⟩
    have h1 : x.re ^ 2 + x.im ^ 2 = x.re := by
      have h3 := norm_sub_half_sq x; rw [h₁'] at h3; nlinarith [h3]
    have h4 : x.re ^ 2 + x.im ^ 2 = -x.re := by
      have h3 := norm_add_half_sq x; rw [h₂'] at h3; nlinarith [h3]
    exact hxre (by linarith)
  rcases harc with harc1 | harc2
  · have hoth : ‖(x : ℂ) + (1 / 2 : ℂ)‖ ≠ 1 / 2 := fun h => hnotboth ⟨harc1, h⟩
    obtain ⟨ρ₃, hρ₃, hB₃⟩ := Metric.mem_nhds_iff.mp (hcl4.isOpen_compl.mem_nhds hoth)
    set ρ := min ρ₁ (min ρ₂ ρ₃) / 2 with hρdef
    have hρpos : 0 < ρ := by rw [hρdef]; positivity
    have hle1 : ρ ≤ ρ₁ := by rw [hρdef]; linarith [min_le_left ρ₁ (min ρ₂ ρ₃)]
    have hle2 : ρ ≤ ρ₂ := by
      rw [hρdef]; linarith [min_le_left ρ₁ (min ρ₂ ρ₃), min_le_right ρ₁ (min ρ₂ ρ₃),
        min_le_left ρ₂ ρ₃]
    have hle3 : ρ ≤ ρ₃ := by
      rw [hρdef]; linarith [min_le_left ρ₁ (min ρ₂ ρ₃), min_le_right ρ₁ (min ρ₂ ρ₃),
        min_le_right ρ₂ ρ₃]
    refine ⟨ρ, hρpos, fun y hy => hsub₁ (Metric.ball_subset_ball hle1 hy), ?_⟩
    refine mdiff_transport_S ℓ d hd r (c := -1) hρpos ?_ ?_ ?_ ?_
    · exact hcont.mono (Metric.ball_subset_ball hle1)
    · intro y hy hyarc
      have hdist : dist y x < ρ := Metric.mem_ball.mp hy
      rcases hyarc with h | h
      · exact re_S_smul_of_arc_left h
      · exfalso
        have hmem : y ∉ {τ : ℍ | ‖(τ : ℂ) + (1 / 2 : ℂ)‖ = 1 / 2} :=
          hB₃ (Metric.mem_ball.mpr (lt_of_lt_of_le hdist hle3))
        exact hmem h
    · intro y hy
      exact hsub₁ (Metric.ball_subset_ball hle1 hy)
    · intro y hy
      exact hB₂ (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hy) hle2))
  · have hoth : ‖(x : ℂ) - (1 / 2 : ℂ)‖ ≠ 1 / 2 := fun h => hnotboth ⟨h, harc2⟩
    obtain ⟨ρ₃, hρ₃, hB₃⟩ := Metric.mem_nhds_iff.mp (hcl1.isOpen_compl.mem_nhds hoth)
    set ρ := min ρ₁ (min ρ₂ ρ₃) / 2 with hρdef
    have hρpos : 0 < ρ := by rw [hρdef]; positivity
    have hle1 : ρ ≤ ρ₁ := by rw [hρdef]; linarith [min_le_left ρ₁ (min ρ₂ ρ₃)]
    have hle2 : ρ ≤ ρ₂ := by
      rw [hρdef]; linarith [min_le_left ρ₁ (min ρ₂ ρ₃), min_le_right ρ₁ (min ρ₂ ρ₃),
        min_le_left ρ₂ ρ₃]
    have hle3 : ρ ≤ ρ₃ := by
      rw [hρdef]; linarith [min_le_left ρ₁ (min ρ₂ ρ₃), min_le_right ρ₁ (min ρ₂ ρ₃),
        min_le_right ρ₂ ρ₃]
    refine ⟨ρ, hρpos, fun y hy => hsub₁ (Metric.ball_subset_ball hle1 hy), ?_⟩
    refine mdiff_transport_S ℓ d hd r (c := 1) hρpos ?_ ?_ ?_ ?_
    · exact hcont.mono (Metric.ball_subset_ball hle1)
    · intro y hy hyarc
      have hdist : dist y x < ρ := Metric.mem_ball.mp hy
      rcases hyarc with h | h
      · exfalso
        have hmem : y ∉ {τ : ℍ | ‖(τ : ℂ) - (1 / 2 : ℂ)‖ = 1 / 2} :=
          hB₃ (Metric.mem_ball.mpr (lt_of_lt_of_le hdist hle3))
        exact hmem h
      · exact re_S_smul_of_arc_right h
    · intro y hy
      exact hsub₁ (Metric.ball_subset_ball hle1 hy)
    · intro y hy
      exact hB₂ (Metric.mem_ball.mpr (lt_of_lt_of_le (Metric.mem_ball.mp hy) hle2))

/-! ## the main statement -/

theorem paperLayer_U0_holo (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) :
    MDifferentiableOn (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (fun τ : UpperHalfPlane =>
        Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
      Work.CKFinal.Socket.U0 := by
  intro x hx
  by_cases hre : x.re = 0
  · obtain ⟨ρ, hρ, -, hmd⟩ := ball_holo_of_axis ℓ d hd r hx hre
    exact (hmd.mdifferentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))).mdifferentiableWithinAt
  · by_cases harc : Work.CKFinal.OnArc x
    · obtain ⟨ρ, hρ, -, hmd⟩ := ball_holo_of_arc ℓ d hd r hx harc
      exact (hmd.mdifferentiableAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))).mdifferentiableWithinAt
    · have ha1 : ‖(x : ℂ) - (1 / 2 : ℂ)‖ ≠ 1 / 2 := fun h => harc (Or.inl h)
      have ha2 : ‖(x : ℂ) + (1 / 2 : ℂ)‖ ≠ 1 / 2 := fun h => harc (Or.inr h)
      obtain ⟨ρ, hρ, -, hmd⟩ := ball_holo_of_clean ℓ d hd r hx hre ha1 ha2
      exact (hmd.mdifferentiableAt
        (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))).mdifferentiableWithinAt

end Work.CKFinal.Socket
