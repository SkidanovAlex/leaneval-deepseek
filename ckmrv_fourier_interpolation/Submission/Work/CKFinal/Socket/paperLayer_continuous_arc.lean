import Mathlib
import Submission.Work.CKFinal.Socket.Basic
import Submission.Work.CKFinal.U0Defs
import Submission.Work.CKFinal.U0ArcSetup
import Submission.Work.CKFinal.orbit_imagAxis_of_mem_U0
import Submission.Work.CKFinal.gam1_smul_mem_DomainD
import Submission.Work.CKFinal.gam2_smul_mem_DomainD
import Submission.Work.CKFinal.ArcCont.arc_branch_classify
import Submission.Work.CKFinal.ArcCont.phiPair_arc_branches
import Submission.Work.CKFinal.ArcCont.branch_bound_of_phiPair
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.continuousOn_Kfun_clean
import Submission.Work.Asymptotics.Graze.KeyBound
import Submission.Work.Asymptotics.Graze.Points
import Submission.Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis
import Submission.Work.Asymptotics.jInvariantFun_eq_smul_of_eq
import Submission.Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded
import Submission.Work.Asymptotics.cuspExpansionKernel
import Submission.Work.Asymptotics.measurable_Kaxis_Kfun
import Submission.Work.CKFinal.AxisCont.Basic
import Submission.Work.LayerCont.AexpLow
import Submission.Work.CKFinal.AxisCont.continuous_highPart
import Submission.Work.LayerCont.KaxisLowBound
import Submission.Work.CKFinal.ArcFin.continuousOn_layerLow_ball
import Submission.Work.CKFinal.ArcFin.trunc_integrand_domin
import Submission.Work.CKFinal.ArcFin.ae_continuousAt_trunc_integrand

set_option maxHeartbeats 1600000

namespace Work.CKFinal.Socket

open MeasureTheory Filter Topology
open scoped Topology

/-! ## Preliminary: the fibre of `j` on the imaginary axis

For *every* `τ : ℍ` the set of `t > 0` with `j τ = j (i t)` is contained in `{t₁, t₁⁻¹}` for any one
of its elements `t₁`: any two such points are `SL(2,ℤ)`-equivalent, and the stabiliser of the
imaginary axis is `{±1, ±S}` (`Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis`). -/

/-- The imaginary part of `imagAxis t _` is `t`. -/
lemma imagAxis_im_of_pos (t : ℝ) (ht : 0 < t) : (Work.Kernels.imagAxis t ht).im = t := by
  rw [← UpperHalfPlane.coe_im]
  simp [Work.Kernels.imagAxis]

/-- `(S • (i t)).im = t⁻¹`. -/
lemma S_smul_imagAxis_im (t : ℝ) (ht : 0 < t) :
    (ModularGroup.S • Work.Kernels.imagAxis t ht).im = t⁻¹ := by
  rw [← UpperHalfPlane.coe_im, Work.Asymptotics.KaxisMid.coe_S_smul]
  have hI : -1 / (((t : ℂ) * Complex.I)) = ((t⁻¹ : ℝ) : ℂ) * Complex.I := by
    rw [div_eq_mul_inv, mul_inv, Complex.inv_I, Complex.ofReal_inv]
    ring
  rw [show ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I from rfl, hI]
  simp

/-- **A point of one of the arcs is not purely imaginary.** -/
lemma onArc_re_ne_zero {τ : UpperHalfPlane} (h : Work.CKFinal.OnArc τ) : τ.re ≠ 0 := by
  intro hre
  have hsub : ((τ : ℂ) - (1 / 2 : ℂ)).re = τ.re - 1 / 2 := by simp [Complex.sub_re]
  have him1 : ((τ : ℂ) - (1 / 2 : ℂ)).im = τ.im := by simp [Complex.sub_im]
  have hadd : ((τ : ℂ) + (1 / 2 : ℂ)).re = τ.re + 1 / 2 := by simp [Complex.add_re]
  have him2 : ((τ : ℂ) + (1 / 2 : ℂ)).im = τ.im := by simp [Complex.add_im]
  rcases h with h | h
  · have h2 : ‖(τ : ℂ) - (1 / 2 : ℂ)‖ ^ 2 = (τ.re - 1 / 2) ^ 2 + τ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hsub, him1]
      ring
    rw [h] at h2
    rw [hre] at h2
    nlinarith [τ.im_pos, sq_nonneg τ.im]
  · have h2 : ‖(τ : ℂ) + (1 / 2 : ℂ)‖ ^ 2 = (τ.re + 1 / 2) ^ 2 + τ.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hadd, him2]
      ring
    rw [h] at h2
    rw [hre] at h2
    nlinarith [τ.im_pos, sq_nonneg τ.im]

/-- **Finiteness of the coincidence set.**  For every `τ : ℍ`, all but at most two `t > 0` have
`j τ ≠ j (i t)`. -/
theorem coincidenceSet_finite (τ : UpperHalfPlane) :
    ∃ S : Set ℝ, S.Finite ∧ ∀ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
        t ∈ S := by
  by_cases h : ∃ (t : ℝ) (ht : 0 < t),
      Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
  · obtain ⟨t₁, ht₁, h₁⟩ := h
    refine ⟨{t₁, t₁⁻¹}, (Set.finite_singleton t₁⁻¹).insert t₁, ?_⟩
    intro t ht ht'
    have hEq : Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)
        = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t₁ ht₁) := by rw [← ht', ← h₁]
    obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hEq
    rcases Work.Asymptotics.eq_one_or_neg_one_or_S_of_smul_imagAxis ht₁ ht hγ with h1 | h1 | h1 | h1
    · rw [h1, one_smul] at hγ
      rw [Set.mem_insert_iff]; left
      have := congrArg UpperHalfPlane.im hγ
      rw [imagAxis_im_of_pos t₁ ht₁, imagAxis_im_of_pos t ht] at this
      exact this.symm
    · rw [h1, ModularGroup.SL_neg_smul, one_smul] at hγ
      rw [Set.mem_insert_iff]; left
      have := congrArg UpperHalfPlane.im hγ
      rw [imagAxis_im_of_pos t₁ ht₁, imagAxis_im_of_pos t ht] at this
      exact this.symm
    · rw [h1] at hγ
      rw [Set.mem_insert_iff]; right
      have := congrArg UpperHalfPlane.im hγ
      rw [S_smul_imagAxis_im t₁ ht₁, imagAxis_im_of_pos t ht] at this
      exact this.symm
    · rw [h1, ModularGroup.SL_neg_smul] at hγ
      rw [Set.mem_insert_iff]; right
      have := congrArg UpperHalfPlane.im hγ
      rw [S_smul_imagAxis_im t₁ ht₁, imagAxis_im_of_pos t ht] at this
      exact this.symm
  · refine ⟨∅, Set.finite_empty, ?_⟩
    intro t ht ht'
    exact absurd ⟨t, ht, ht'⟩ h

/-- The kernel on the product is continuous at every clean pair. -/
lemma continuousAt_Kfun_pair (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ z : UpperHalfPlane} (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    ContinuousAt (fun p : UpperHalfPlane × UpperHalfPlane => Work.Kernels.Kfun ℓ d p.1 p.2)
      (τ, z) := by
  have hopen : IsOpen {p : UpperHalfPlane × UpperHalfPlane |
      Work.Kernels.jInvariantFun p.1 ≠ Work.Kernels.jInvariantFun p.2} := by
    have h1 : {p : UpperHalfPlane × UpperHalfPlane |
        Work.Kernels.jInvariantFun p.1 ≠ Work.Kernels.jInvariantFun p.2}
        = {p : UpperHalfPlane × UpperHalfPlane |
            Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun p.2 ≠ 0} := by
      ext p; simp [sub_ne_zero]
    rw [h1]
    exact (isOpen_ne (x := (0 : ℂ))).preimage Work.Asymptotics.continuous_jInvariantFun_sub'
  exact (Work.Asymptotics.continuousOn_Kfun_clean ℓ d hd).continuousAt
    (hopen.mem_nhds (by simpa using h))

/-- **A.e. continuity of `τ ↦ Kaxis (Kfun ℓ d) τ t`.**  For every `τ₁ : ℍ` the function
`τ ↦ Kaxis (Kfun ℓ d) τ t` is continuous at `τ₁` for almost every `t ∈ (0,∞)`, because the
exceptional `t`'s (the coincidence heights) form a finite set. -/
theorem ae_continuousAt_Kaxis (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ₁ : UpperHalfPlane) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ContinuousAt (fun τ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t) τ₁ := by
  obtain ⟨S, hSfin, hS⟩ := coincidenceSet_finite τ₁
  have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ S := by
    rw [MeasureTheory.ae_iff]
    simpa using hSfin.measure_zero (volume : Measure ℝ)
  filter_upwards [MeasureTheory.ae_restrict_of_ae hnull] with t htS
  by_cases ht : 0 < t
  · have hJ : Work.Kernels.jInvariantFun τ₁
        ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := fun h => htS (hS t ht h)
    have hfun : (fun τ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t)
        = fun τ : UpperHalfPlane => Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t ht) := by
      funext τ
      simp only [Work.Kernels.Kaxis, dif_pos ht]
    rw [hfun]
    have hmap : ContinuousAt (fun τ : UpperHalfPlane =>
        (τ, Work.Kernels.imagAxis t ht)) τ₁ :=
      continuousAt_id.prodMk continuousAt_const
    exact ContinuousAt.comp
      (g := fun p : UpperHalfPlane × UpperHalfPlane => Work.Kernels.Kfun ℓ d p.1 p.2)
      (f := fun τ : UpperHalfPlane => (τ, Work.Kernels.imagAxis t ht)) (x := τ₁)
      (continuousAt_Kfun_pair ℓ d hd hJ) hmap
  · have hfun : (fun τ : UpperHalfPlane => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t)
        = fun _ : UpperHalfPlane => (0 : ℂ) := by
      funext τ
      simp only [Work.Kernels.Kaxis, dif_neg ht]
    rw [hfun]
    exact continuousAt_const


/-! ## The arc points with `j = j i`: the two tangency points

The only arc points whose `j`-invariant is `j i = 1728` are the two tangency points
`cR = (1+i)/2` and `cL = (-1+i)/2` of `Work.Asymptotics.Graze`.  Concretely: if `τ` is on an arc and
`j τ = j i` then `τ = A • i` for one of the two elements `A ∈ {T S T, S T}` of
`Work.Asymptotics.Graze.IsArc`. -/

/-- `S T⁻¹ • i = (1+i)/2 = cR`. -/
lemma ST_inv_smul_I_eq_cR :
    ((ModularGroup.S * ModularGroup.T⁻¹) • UpperHalfPlane.I : UpperHalfPlane)
      = Work.Asymptotics.Graze.cR := by
  have hmat : ((ModularGroup.S * ModularGroup.T⁻¹ : Matrix.SpecialLinearGroup (Fin 2) ℤ)
      : Matrix (Fin 2) (Fin 2) ℤ) = !![0, -1; 1, -1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ModularGroup.coe_T, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_I,
    Work.Asymptotics.Graze.cR_coe, hmat]
  norm_num
  simp only [div_eq_mul_inv]
  rw [Complex.ext_iff]
  constructor <;>
    simp [Complex.inv_re, Complex.inv_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im, Complex.normSq_apply] <;> norm_num

/-- `(T S T)⁻¹ • i = (-1+i)/2 = cL`. -/
lemma TST_inv_smul_I_eq_cL :
    (((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹) • UpperHalfPlane.I : UpperHalfPlane)
      = Work.Asymptotics.Graze.cL := by
  have hmat : (((ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹
      : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -1, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [ModularGroup.coe_T, ModularGroup.coe_S, Matrix.mul_apply, Fin.sum_univ_two]
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_I,
    Work.Asymptotics.Graze.cL_coe, hmat]
  norm_num
  simp only [div_eq_mul_inv]
  rw [Complex.ext_iff]
  constructor <;>
    simp [Complex.inv_re, Complex.inv_im, Complex.mul_re, Complex.mul_im, Complex.add_re,
      Complex.add_im, Complex.I_re, Complex.I_im, Complex.normSq_apply] <;> norm_num

/-- **Identification of `OnArc`-points with `j = j i`.** -/
theorem exists_IsArc_smul_I_eq_of_onArc {τ : UpperHalfPlane} (harc : Work.CKFinal.OnArc τ)
    (h : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun UpperHalfPlane.I) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℤ, Work.Asymptotics.Graze.IsArc A ∧
      A • UpperHalfPlane.I = τ := by
  have hI : Work.Kernels.imagAxis 1 one_pos = UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    show ((1 : ℂ) * Complex.I) = Complex.I
    rw [one_mul]
  obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq h
  have hγ' : γ • Work.Kernels.imagAxis 1 one_pos = τ := by rw [hI]; exact hγ
  have hcl := Work.CKFinal.ArcCont.arc_branch_classify one_pos γ hγ'
  have hdisj : γ = ModularGroup.T * ModularGroup.S * ModularGroup.T ∨
      γ = -(ModularGroup.T * ModularGroup.S * ModularGroup.T) ∨
      γ = ModularGroup.S * ModularGroup.T⁻¹ ∨ γ = -(ModularGroup.S * ModularGroup.T⁻¹) ∨
      γ = (ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹ ∨
      γ = -(ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹ ∨
      γ = ModularGroup.S * ModularGroup.T ∨ γ = -(ModularGroup.S * ModularGroup.T) := by
    rcases harc with h1 | h2
    · rcases hcl.1 h1 with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · rcases hcl.2 h2 with h | h | h | h
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
  rcases hdisj with h | h | h | h | h | h | h | h
  · refine ⟨ModularGroup.T * ModularGroup.S * ModularGroup.T, Or.inl rfl, ?_⟩
    rw [h] at hγ
    exact hγ
  · refine ⟨ModularGroup.T * ModularGroup.S * ModularGroup.T, Or.inl rfl, ?_⟩
    rw [h] at hγ
    rw [ModularGroup.SL_neg_smul] at hγ
    exact hγ
  · refine ⟨ModularGroup.T * ModularGroup.S * ModularGroup.T, Or.inl rfl, ?_⟩
    rw [h] at hγ
    rw [ST_inv_smul_I_eq_cR] at hγ
    exact hγ
  · refine ⟨ModularGroup.T * ModularGroup.S * ModularGroup.T, Or.inl rfl, ?_⟩
    rw [h] at hγ
    rw [ModularGroup.SL_neg_smul, ST_inv_smul_I_eq_cR] at hγ
    exact hγ
  · refine ⟨ModularGroup.S * ModularGroup.T, Or.inr rfl, ?_⟩
    rw [h] at hγ
    rw [TST_inv_smul_I_eq_cL] at hγ
    exact hγ
  · refine ⟨ModularGroup.S * ModularGroup.T, Or.inr rfl, ?_⟩
    rw [h] at hγ
    rw [ModularGroup.SL_neg_smul, TST_inv_smul_I_eq_cL] at hγ
    exact hγ
  · refine ⟨ModularGroup.S * ModularGroup.T, Or.inr rfl, ?_⟩
    rw [h] at hγ
    exact hγ
  · refine ⟨ModularGroup.S * ModularGroup.T, Or.inr rfl, ?_⟩
    rw [h] at hγ
    rw [ModularGroup.SL_neg_smul] at hγ
    exact hγ

/-! ## The local bound at a crossing on an arc -/

/-- **The kernel is bounded near the crossing `(τ₀, i t₀)` of an arc point.**  If `τ₀` lies on one
of the two bottom arcs and `j τ₀ = j (i t₀)`, then `τ ↦ Kaxis (Kfun ℓ d) τ t` is bounded on a
Euclidean neighbourhood of `(τ₀, t₀)`.  (The crossing carries zero residue, which is what makes the
pole removable; the case `t₀ = 1` is the coalescence of the two branches at a tangency point.) -/
theorem local_bound_arc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : UpperHalfPlane} (harc : Work.CKFinal.OnArc τ₀) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (hcoin : Work.Kernels.jInvariantFun τ₀
      = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t₀ ht₀)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 ≤ C ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      ‖(τ : ℂ) - (τ₀ : ℂ)‖ < ρ → |t - t₀| < ρ → 0 < t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  by_cases ht1 : t₀ = 1
  · -- the tangency case: `τ₀ = cR` or `τ₀ = cL`
    have hI : Work.Kernels.jInvariantFun τ₀ = Work.Kernels.jInvariantFun UpperHalfPlane.I := by
      rw [hcoin]
      congr 1
      apply UpperHalfPlane.ext
      show ((Work.Kernels.imagAxis t₀ ht₀ : UpperHalfPlane) : ℂ) = (UpperHalfPlane.I : ℂ)
      rw [UpperHalfPlane.coe_I]
      show (t₀ : ℂ) * Complex.I = Complex.I
      rw [ht1]; norm_num
    obtain ⟨A, hA, hAI⟩ := exists_IsArc_smul_I_eq_of_onArc harc hI
    obtain ⟨ρ, C, hρ, hC, hb⟩ := Work.Asymptotics.Graze.key_bound_arc ℓ d hd A hA
    refine ⟨ρ, C, hρ, hC, fun τ t hτ ht hpos => ?_⟩
    have hfun : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        = Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t hpos) := by
      simp only [Work.Kernels.Kaxis, dif_pos hpos]
    rw [hfun]
    have hτA : ‖(τ : ℂ) - ((A • UpperHalfPlane.I : UpperHalfPlane) : ℂ)‖ < ρ := by
      rw [hAI]; exact hτ
    refine hb τ (Work.Kernels.imagAxis t hpos) hτA ?_
    have hnorm : ‖((Work.Kernels.imagAxis t hpos : UpperHalfPlane) : ℂ)
        - ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)‖ = |t - 1| := by
      rw [UpperHalfPlane.coe_I]
      have hco : ((Work.Kernels.imagAxis t hpos : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := rfl
      rw [hco, show (t : ℂ) * Complex.I - Complex.I = ((t - 1 : ℝ) : ℂ) * Complex.I by
        push_cast; ring]
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [UpperHalfPlane.coe_I] at hnorm
    rw [hnorm, ← ht1]
    exact ht
  · -- the generic case: the branching element satisfies the CKMRV pair condition
    obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hcoin
    have hcl := Work.CKFinal.ArcCont.arc_branch_classify ht₀ γ hγ
    have hdisj : γ = ModularGroup.T * ModularGroup.S * ModularGroup.T ∨
        γ = -(ModularGroup.T * ModularGroup.S * ModularGroup.T) ∨
        γ = ModularGroup.S * ModularGroup.T⁻¹ ∨ γ = -(ModularGroup.S * ModularGroup.T⁻¹) ∨
        γ = (ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹ ∨
        γ = -(ModularGroup.T * ModularGroup.S * ModularGroup.T)⁻¹ ∨
        γ = ModularGroup.S * ModularGroup.T ∨ γ = -(ModularGroup.S * ModularGroup.T) := by
      rcases harc with h1 | h2
      · rcases hcl.1 h1 with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · rcases hcl.2 h2 with h | h | h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    have hpair := Work.CKFinal.ArcCont.phiPair_arc_branches γ hdisj
    obtain ⟨ρ, C, hρ, hC, hb⟩ :=
      Work.CKFinal.ArcCont.branch_bound_of_phiPair ℓ d hd γ hpair ht₀ ht1
    refine ⟨ρ, C, hρ, hC, fun τ t hτ ht hpos => ?_⟩
    have hfun : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        = Work.Kernels.Kfun ℓ d τ (Work.Kernels.imagAxis t hpos) := by
      simp only [Work.Kernels.Kaxis, dif_pos hpos]
    rw [hfun]
    have hτ' : ‖(τ : ℂ) - ((γ • Work.Kernels.imagAxis t₀ ht₀ : UpperHalfPlane) : ℂ)‖ < ρ := by
      rw [hγ]; exact hτ
    refine hb τ (Work.Kernels.imagAxis t hpos) hτ' ?_
    rw [Work.CKFinal.norm_imagAxis_sub_imagAxis t t₀ hpos ht₀]
    exact ht

/-! ## The uniform bound on the middle range of the contour

On a compact subset of `U₀` disjoint from the imaginary axis, the kernel is bounded on
`[δ, T] × (0,∞)`; this follows from the local bound at the crossings on the arc plus compactness. -/

/-- Conversion: a hyperbolic ball of small radius is contained in a given Euclidean ball. -/
lemma exists_dist_radius_euclid (c : UpperHalfPlane) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ r : ℝ, 0 < r ∧ ∀ τ : UpperHalfPlane, dist τ c < r → ‖(τ : ℂ) - (c : ℂ)‖ < ρ := by
  refine ⟨min 1 (ρ / (4 * max c.im 1)),
    lt_min one_pos (div_pos hρ (by positivity)), fun τ hτ => ?_⟩
  have hrpos : 0 < min 1 (ρ / (4 * max c.im 1)) :=
    lt_min one_pos (div_pos hρ (by positivity))
  have hr1 : min 1 (ρ / (4 * max c.im 1)) ≤ 1 := min_le_left _ _
  have hexp : Real.exp (dist τ c) - 1 ≤ 2 * min 1 (ρ / (4 * max c.im 1)) := by
    have h1 : Real.exp (dist τ c) ≤ Real.exp (min 1 (ρ / (4 * max c.im 1))) :=
      Real.exp_le_exp.mpr hτ.le
    have h2 := Work.CKFinal.exp_sub_one_le_two_mul hrpos hr1
    linarith
  have him : c.im ≤ max c.im 1 := le_max_left _ _
  have hmax : 0 < max c.im 1 := lt_of_lt_of_le c.im_pos him
  have hexpnn : Real.exp (dist τ c) - 1 ≥ 0 := by
    linarith [Real.one_le_exp (dist_nonneg : (0 : ℝ) ≤ dist τ c)]
  have h1 : ‖(τ : ℂ) - (c : ℂ)‖ ≤ max c.im 1 * (Real.exp (dist τ c) - 1) := by
    have h := UpperHalfPlane.dist_coe_le τ c
    rw [dist_eq_norm] at h
    exact le_trans h (mul_le_mul_of_nonneg_right him hexpnn)
  have h2 : max c.im 1 * (Real.exp (dist τ c) - 1)
      ≤ max c.im 1 * (2 * min 1 (ρ / (4 * max c.im 1))) :=
    mul_le_mul_of_nonneg_left hexp (le_of_lt hmax)
  have h3 : max c.im 1 * (2 * min 1 (ρ / (4 * max c.im 1)))
      ≤ max c.im 1 * (2 * (ρ / (4 * max c.im 1))) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hmax)
    have h := min_le_right (1 : ℝ) (ρ / (4 * max c.im 1))
    linarith
  have h4 : max c.im 1 * (2 * (ρ / (4 * max c.im 1))) = ρ / 2 := by
    have hne : max c.im 1 ≠ 0 := ne_of_gt hmax
    field_simp
    ring
  calc ‖(τ : ℂ) - (c : ℂ)‖ ≤ max c.im 1 * (2 * (ρ / (4 * max c.im 1))) :=
        le_trans h1 (le_trans h2 h3)
    _ = ρ / 2 := h4
    _ < ρ := by linarith

/-- **The uniform bound on the middle range.**  If the closed ball `B(τ₀,ρ)` lies in `U₀` and
meets neither arc-boundary... precisely: if it lies in `U₀` and avoids the imaginary axis, then the
kernel is bounded on `B(τ₀,ρ) × [δ,T]`. -/
theorem arc_middle_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : UpperHalfPlane} {ρ δ T : ℝ} (hδ : 0 < δ)
    (hU : Metric.closedBall τ₀ ρ ⊆ Work.CKFinal.U0)
    (hre : ∀ τ ∈ Metric.closedBall τ₀ ρ, τ.re ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ Metric.closedBall τ₀ ρ, ∀ t : ℝ, δ ≤ t → t ≤ T →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  set K : Set UpperHalfPlane := Metric.closedBall τ₀ ρ with hKdef
  have hKc : IsCompact K := isCompact_closedBall τ₀ ρ
  set P : Set (UpperHalfPlane × ℝ) := K ×ˢ Set.Icc δ T with hPdef
  have hPc : IsCompact P := hKc.prod isCompact_Icc
  set Ψ : UpperHalfPlane × ℝ → ℂ :=
    fun q => Work.Kernels.Kfun ℓ d q.1 (Work.LayerCont.axisPtδ δ hδ q.2) with hΨdef
  have hΨeq : ∀ q ∈ P, Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) q.1 q.2 = Ψ q := by
    intro q hq
    obtain ⟨-, hq1, -⟩ := hq
    have hpos : 0 < q.2 := lt_of_lt_of_le hδ hq1
    simp only [hΨdef, Work.Kernels.Kaxis, dif_pos hpos]
    rw [Work.LayerCont.axisPtδ_eq_imagAxis hδ hq1]
  have hloc : ∀ p : P, ∃ C : ℝ, 0 < C ∧ ∃ r : ℝ, 0 < r ∧ ∀ q : P,
      dist (q.1).1 (p.1).1 < r → |(q.1).2 - (p.1).2| < r →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (q.1).1 (q.1).2‖ ≤ C := by
    intro p
    have hpδ : δ ≤ (p.1).2 := (p.2).2.1
    have hp2 : 0 < (p.1).2 := lt_of_lt_of_le hδ hpδ
    by_cases hcoin : Work.Kernels.jInvariantFun (p.1).1
        = Work.Kernels.jInvariantFun (Work.LayerCont.axisPtδ δ hδ (p.1).2)
    · -- a coincidence: the point lies on one of the arcs, and the crossing is removable
      have hcoin' : Work.Kernels.jInvariantFun (p.1).1
          = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis (p.1).2 hp2) := by
        rw [Work.LayerCont.axisPtδ_eq_imagAxis hδ hpδ] at hcoin
        exact hcoin
      have harc : Work.CKFinal.OnArc (p.1).1 := by
        obtain ⟨γ, hγ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq hcoin'
        have hzero : (((γ⁻¹ • (p.1).1 : UpperHalfPlane) : ℂ)).re = 0 := by
          have he : γ⁻¹ • (p.1).1 = Work.Kernels.imagAxis (p.1).2 hp2 := by
            rw [← hγ]; simp
          rw [he]; exact Work.CKFinal.imagAxis_re_coe (p.1).2 hp2
        rcases Work.CKFinal.orbit_imagAxis_of_mem_U0 (p.1).1 (hU (p.2).1) γ⁻¹ hzero
          with h | h | h
        · exact absurd h (hre (p.1).1 (p.2).1)
        · exact Or.inl h
        · exact Or.inr h
      obtain ⟨ρe, Ce, hρe, hCe, hbe⟩ := local_bound_arc ℓ d hd harc hp2 hcoin'
      obtain ⟨re, hre', hre''⟩ := exists_dist_radius_euclid (p.1).1 hρe
      refine ⟨max Ce 1, lt_of_lt_of_le one_pos (le_max_right _ _), min re ρe,
        lt_min hre' hρe, fun q hq1 hq2 => ?_⟩
      have hqδ : δ ≤ (q.1).2 := (q.2).2.1
      refine le_trans (hbe (q.1).1 (q.1).2 (hre'' _ (lt_of_lt_of_le hq1 (min_le_left _ _)))
        (lt_of_lt_of_le hq2 (min_le_right _ _)) (lt_of_lt_of_le hδ hqδ)) (le_max_left _ _)
    · -- no coincidence: the kernel is jointly continuous at `p`
      have hcont : ContinuousAt Ψ (p.1) := by
        have hpair : ContinuousAt (fun x : UpperHalfPlane × UpperHalfPlane =>
            Work.Kernels.Kfun ℓ d x.1 x.2) ((p.1).1, Work.LayerCont.axisPtδ δ hδ (p.1).2) :=
          continuousAt_Kfun_pair ℓ d hd hcoin
        have hmap : ContinuousAt (fun q : UpperHalfPlane × ℝ =>
            (q.1, Work.LayerCont.axisPtδ δ hδ q.2)) (p.1) :=
          ContinuousAt.prodMk continuous_fst.continuousAt
            ((Work.LayerCont.continuous_axisPtδ δ hδ).continuousAt.comp continuous_snd.continuousAt)
        exact ContinuousAt.comp
          (g := fun x : UpperHalfPlane × UpperHalfPlane => Work.Kernels.Kfun ℓ d x.1 x.2)
          (f := fun q : UpperHalfPlane × ℝ =>
            (q.1, Work.LayerCont.axisPtδ δ hδ q.2))
          (x := p.1) hpair hmap
      obtain ⟨r, hr, hbd⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
      refine ⟨max (‖Ψ (p.1)‖ + 1) 1, lt_of_lt_of_le one_pos (le_max_right _ _), r, hr,
        fun q hq1 hq2 => ?_⟩
      have hdist : dist (q.1) (p.1) < r := by
        rw [Prod.dist_eq, max_lt_iff]
        exact ⟨hq1, by rw [Real.dist_eq]; exact hq2⟩
      have hb := hbd (x := q.1) hdist
      rw [Complex.dist_eq] at hb
      have h1 : ‖Ψ (q.1)‖ ≤ ‖Ψ (q.1) - Ψ (p.1)‖ + ‖Ψ (p.1)‖ := by
        have := norm_add_le (Ψ (q.1) - Ψ (p.1)) (Ψ (p.1))
        simpa using this
      have h2 : ‖Ψ (q.1)‖ ≤ ‖Ψ (p.1)‖ + 1 := by linarith
      calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (q.1).1 (q.1).2‖
          = ‖Ψ (q.1)‖ := by rw [hΨeq (q.1) q.2]
        _ ≤ ‖Ψ (p.1)‖ + 1 := h2
        _ ≤ max (‖Ψ (p.1)‖ + 1) 1 := le_max_left _ _
  classical
  let Cf : P → ℝ := fun p => Classical.choose (hloc p)
  have hCfpos : ∀ p, 0 < Cf p := fun p => (Classical.choose_spec (hloc p)).1
  let rf : P → ℝ := fun p => Classical.choose (Classical.choose_spec (hloc p)).2
  have hrfpos : ∀ p, 0 < rf p :=
    fun p => (Classical.choose_spec (Classical.choose_spec (hloc p)).2).1
  have hbound : ∀ (p q : P), dist (q.1).1 (p.1).1 < rf p → |(q.1).2 - (p.1).2| < rf p →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (q.1).1 (q.1).2‖ ≤ Cf p :=
    fun p => (Classical.choose_spec (Classical.choose_spec (hloc p)).2).2
  have hopen : ∀ p : P, IsOpen {q : UpperHalfPlane × ℝ |
      dist q.1 (p.1).1 < rf p ∧ |q.2 - (p.1).2| < rf p} := by
    intro p
    have h1 : IsOpen {q : UpperHalfPlane × ℝ | dist q.1 (p.1).1 < rf p} :=
      isOpen_lt (continuous_fst.dist continuous_const) continuous_const
    have h2 : IsOpen {q : UpperHalfPlane × ℝ | |q.2 - (p.1).2| < rf p} :=
      isOpen_lt ((continuous_snd.sub continuous_const).abs) continuous_const
    exact h1.inter h2
  have hcover : P ⊆ ⋃ p : P, {q : UpperHalfPlane × ℝ |
      dist q.1 (p.1).1 < rf p ∧ |q.2 - (p.1).2| < rf p} := by
    intro q hq
    refine Set.mem_iUnion.mpr ⟨⟨q, hq⟩, ?_⟩
    exact ⟨by simpa [dist_self] using hrfpos ⟨q, hq⟩, by simpa using hrfpos ⟨q, hq⟩⟩
  obtain ⟨s, hs⟩ := hPc.elim_finite_subcover
    (fun p : P => {q : UpperHalfPlane × ℝ |
      dist q.1 (p.1).1 < rf p ∧ |q.2 - (p.1).2| < rf p}) hopen hcover
  refine ⟨(∑ p ∈ s, Cf p) + 1, ?_, fun τ hτK t hδt htT => ?_⟩
  · have hsum := Finset.sum_nonneg (s := s) (f := Cf) (fun p _ => (hCfpos p).le)
    linarith
  have hq : (τ, t) ∈ P := ⟨hτK, hδt, htT⟩
  have hmem := hs hq
  rw [Set.mem_iUnion₂] at hmem
  obtain ⟨p, hps, hpU⟩ := hmem
  have hle := hbound p ⟨(τ, t), hq⟩ hpU.1 hpU.2
  refine le_trans hle ?_
  have := Finset.single_le_sum (s := s) (f := Cf) (fun x _ => (hCfpos x).le) hps
  linarith

/-- **The uniform bound on `(0,T]`.**  Combining the cusp bound (`t → 0`) with the middle-range
bound. -/
theorem arc_low_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : UpperHalfPlane} {ρ T : ℝ}
    (hU : Metric.closedBall τ₀ ρ ⊆ Work.CKFinal.U0)
    (hre : ∀ τ ∈ Metric.closedBall τ₀ ρ, τ.re ≠ 0) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ Metric.closedBall τ₀ ρ, ∀ t : ℝ, 0 < t → t ≤ T →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C := by
  obtain ⟨δ, hδ, hcusp⟩ := Work.Asymptotics.HalfFunnel.Kaxis_cusp_of_bounded ℓ d hd
    (Metric.isBounded_closedBall (x := τ₀) (r := ρ))
  obtain ⟨c, hc, hcb⟩ := hcusp 0 le_rfl
  by_cases hT : T ≤ δ
  · refine ⟨c, hc, fun τ hτ t ht htT => ?_⟩
    have := hcb τ t hτ ht (le_trans htT hT)
    simpa using this
  · rw [not_le] at hT
    obtain ⟨Cm, hCm, hmid⟩ := arc_middle_bound ℓ d hd hδ hU hre (T := T)
    refine ⟨max c Cm, lt_of_lt_of_le hc (le_max_left _ _), fun τ hτ t ht htT => ?_⟩
    rcases le_or_gt t δ with h | h
    · exact le_trans (by simpa using hcb τ t hτ ht h) (le_max_left _ _)
    · exact le_trans (hmid τ hτ t h.le htT) (le_max_right _ _)

/-- **The trunc dominator.**  A single estimated function dominating `Kaxis - Aexp` on the whole
contour `[1,∞)`, uniformly over the closed ball. -/
theorem arc_trunc_dominator (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {τ₀ : UpperHalfPlane} {ρ : ℝ}
    (hU : Metric.closedBall τ₀ ρ ⊆ Work.CKFinal.U0)
    (hre : ∀ τ ∈ Metric.closedBall τ₀ ρ, τ.re ≠ 0) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧
      ∀ τ ∈ Metric.closedBall τ₀ ρ, ∀ t : ℝ, 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  obtain ⟨Ck, Mk, Tk, hCk, hMk, hTk, hkb⟩ :=
    Work.Asymptotics.kernel_axis_bound ℓ d hd (isCompact_closedBall (x := τ₀) (r := ρ))
  set T' : ℝ := max Tk 1 with hT'def
  have hT'pos : 0 < T' := lt_max_of_lt_right one_pos
  have hTk_le : Tk ≤ T' := le_max_left _ _
  obtain ⟨C0, hC0, hlow⟩ := arc_low_bound ℓ d hd (T := T') hU hre
  obtain ⟨Cae, hCae, hae⟩ := Work.LayerCont.Aexp_compact_bound ℓ d hd
    (isCompact_closedBall (x := τ₀) (r := ρ)) (T := T')
  refine ⟨max (C0 + Cae) (Ck * Real.exp (-(Real.pi * T'))) + 1, max Mk 0, T',
    by positivity, le_max_right _ _, hT'pos.le, fun τ hτ t ht1 => ?_⟩
  rcases le_or_gt t T' with htT | htT
  · have hA : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ C0 :=
      hlow τ hτ t (lt_of_lt_of_le one_pos ht1) htT
    have hB : ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ Cae :=
      hae τ hτ t (by rw [abs_of_nonneg (by linarith)]; exact htT)
    have hsum : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ C0 + Cae :=
      le_trans (norm_sub_le _ _) (add_le_add hA hB)
    have hpow : (1 : ℝ) ≤ (1 + t) ^ max Mk 0 :=
      Real.one_le_rpow (by linarith) (le_max_right _ _)
    have hexp : (1 : ℝ) ≤ Real.exp (-(Real.pi * (t - T'))) := by
      rw [Real.one_le_exp_iff]; nlinarith [Real.pi_pos]
    have hle : (1 : ℝ) ≤ (1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - T'))) := by
      have := mul_le_mul hpow hexp zero_le_one (Real.rpow_nonneg (by linarith) _)
      simpa using this
    have hCC : C0 + Cae ≤ max (C0 + Cae) (Ck * Real.exp (-(Real.pi * T'))) + 1 := by
      linarith [le_max_left (C0 + Cae) (Ck * Real.exp (-(Real.pi * T')))]
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
          ≤ C0 + Cae := hsum
      _ ≤ (max (C0 + Cae) (Ck * Real.exp (-(Real.pi * T'))) + 1) * 1 := by
          rw [mul_one]; exact hCC
      _ ≤ (max (C0 + Cae) (Ck * Real.exp (-(Real.pi * T'))) + 1)
            * ((1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - T')))) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = (max (C0 + Cae) (Ck * Real.exp (-(Real.pi * T'))) + 1)
            * (1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - T'))) := by ring
  · have hb := hkb τ hτ t (le_trans hTk_le htT.le)
    have hsplit : Real.exp (-(Real.pi * t))
        = Real.exp (-(Real.pi * T')) * Real.exp (-(Real.pi * (t - T'))) := by
      rw [← Real.exp_add]; congr 1; ring
    have hpow : (1 + t) ^ Mk ≤ (1 + t) ^ max Mk 0 :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
    have hX : (0 : ℝ) ≤ (1 + t) ^ max Mk 0 := Real.rpow_nonneg (by linarith) _
    have hY : (0 : ℝ) ≤ Real.exp (-(Real.pi * (t - T'))) := (Real.exp_pos _).le
    have hCC : Ck * Real.exp (-(Real.pi * T'))
        ≤ max (C0 + Cae) (Ck * Real.exp (-(Real.pi * T'))) + 1 := by
      linarith [le_max_right (C0 + Cae) (Ck * Real.exp (-(Real.pi * T')))]
    calc ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
          ≤ Ck * (1 + t) ^ Mk * Real.exp (-(Real.pi * t)) := hb
      _ = Ck * (1 + t) ^ Mk * (Real.exp (-(Real.pi * T'))
            * Real.exp (-(Real.pi * (t - T')))) := by rw [hsplit]
      _ ≤ Ck * (1 + t) ^ max Mk 0 * (Real.exp (-(Real.pi * T'))
            * Real.exp (-(Real.pi * (t - T')))) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hCk.le)
            (mul_nonneg (Real.exp_pos _).le hY)
      _ = (Ck * Real.exp (-(Real.pi * T'))) * ((1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - T')))) := by ring
      _ ≤ (max (C0 + Cae) (Ck * Real.exp (-(Real.pi * T'))) + 1)
            * ((1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - T')))) :=
          mul_le_mul_of_nonneg_right hCC (mul_nonneg hX hY)
      _ = (max (C0 + Cae) (Ck * Real.exp (-(Real.pi * T'))) + 1)
            * (1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - T'))) := by ring

/-- **Continuity of the trunc piece on a ball.**  This is the analogue of
`Work.CKFinal.ArcFin.continuousOn_layerTrunc_ball`, proved here from the two inputs
`trunc_integrand_domin` (an integrable dominator) and `ae_continuousAt_trunc_integrand`
(a.e. continuity of the integrand). -/
theorem continuousOn_layerTrunc_ball' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) {τ₀ : UpperHalfPlane} {ρ C M T₀ : ℝ} (hρ : 0 < ρ)
    (hC : 0 < C) (hM : 0 ≤ M) (hT₀ : 0 ≤ T₀)
    (hdom : ∀ τ : UpperHalfPlane, τ ∈ Metric.closedBall τ₀ ρ → ∀ t : ℝ, 1 ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))))
    (hcoin : ∀ τ : UpperHalfPlane, τ ∈ Metric.closedBall τ₀ ρ →
      ∃ S : Set ℝ, S.Finite ∧ ∀ (t : ℝ) (ht : 0 < t),
        Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
          t ∈ S) :
    ContinuousOn (fun τ : UpperHalfPlane =>
        Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
      (Metric.ball τ₀ ρ) := by
  obtain ⟨hint, hb⟩ := Work.CKFinal.ArcFin.trunc_integrand_domin ℓ d r hρ hC hM hT₀ hdom
  have hae := Work.CKFinal.ArcFin.ae_continuousAt_trunc_integrand ℓ d hd r hρ hcoin
  have hAmeas : ∀ τ : UpperHalfPlane, Measurable (fun t : ℝ =>
      Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t) := fun τ =>
    ((Work.Asymptotics.HalfFunnel.continuous_Aexp_tang ℓ d hd).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hgmeas : Measurable (fun t : ℝ =>
      Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by fun_prop
  intro τ₁ hτ₁
  have hmain : ContinuousAt (fun τ : UpperHalfPlane =>
      ∫ t, (Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
            - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t)
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))
        ∂(MeasureTheory.volume.restrict (Set.Ici (1 : ℝ)))) τ₁ := by
    refine MeasureTheory.continuousAt_of_dominated
      (μ := MeasureTheory.volume.restrict (Set.Ici (1 : ℝ)))
      (x₀ := τ₁)
      (bound := fun t : ℝ => (C * Real.exp (Real.pi * T₀))
        * ((1 + t) ^ M * Real.exp (-(Real.pi * (1 + r ^ 2) * t))))
      ?_ ?_ hint ?_
    · filter_upwards with τ
      exact (((Work.Asymptotics.measurable_Kaxis_Kfun ℓ d hd τ).sub
        (hAmeas τ)).mul hgmeas).aestronglyMeasurable
    · filter_upwards [Metric.isOpen_ball.mem_nhds hτ₁] with τ hτ
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
      exact hb τ (Metric.ball_subset_closedBall hτ) t ht
    · exact hae τ₁ hτ₁
  have h2 : ContinuousAt (fun τ : UpperHalfPlane =>
      Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r) τ₁ := by
    simpa only [Work.Asymptotics.layerTrunc] using
      hmain.const_mul (Work.Asymptotics.sinSq r)
  exact h2.continuousWithinAt

theorem paperLayer_continuous_arc (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (r : ℝ) {τ₀ : UpperHalfPlane}
    (hτ₀ : τ₀ ∈ Work.CKFinal.Socket.U0) (harc : Work.CKFinal.OnArc τ₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball τ₀ ρ ⊆ Work.CKFinal.Socket.U0 ∧
      ContinuousOn (fun τ : UpperHalfPlane =>
        Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
        (Metric.ball τ₀ ρ) := by
  -- A ball inside `U₀`.
  obtain ⟨ρ₁, hρ₁pos, hρ₁sub⟩ := (Metric.isOpen_iff.mp Work.CKFinal.isOpen_U0) τ₀ hτ₀
  -- A ball on which `Re τ ≠ 0`.
  have hrene : τ₀.re ≠ 0 := onArc_re_ne_zero harc
  obtain ⟨ρ₂, hρ₂pos, hρ₂le⟩ := Metric.continuousAt_iff.mp
    UpperHalfPlane.continuous_re.continuousAt (|τ₀.re|) (abs_pos.mpr hrene)
  have hρ₁h : (0 : ℝ) < ρ₁ / 2 := by linarith
  have hρ₂h : (0 : ℝ) < ρ₂ / 2 := by linarith
  have hρ₁' : min (ρ₁ / 2) (ρ₂ / 2) < ρ₁ := by
    have := min_le_left (ρ₁ / 2) (ρ₂ / 2); linarith
  have hρ₂' : min (ρ₁ / 2) (ρ₂ / 2) < ρ₂ := by
    have := min_le_right (ρ₁ / 2) (ρ₂ / 2); linarith
  have hclosedU0 : Metric.closedBall τ₀ (min (ρ₁ / 2) (ρ₂ / 2)) ⊆ Work.CKFinal.Socket.U0 :=
    fun τ hτ => hρ₁sub (Metric.closedBall_subset_ball hρ₁' hτ)
  have hballU0 : Metric.ball τ₀ (min (ρ₁ / 2) (ρ₂ / 2)) ⊆ Work.CKFinal.Socket.U0 :=
    fun τ hτ => hclosedU0 (Metric.ball_subset_closedBall hτ)
  have hre : ∀ τ ∈ Metric.closedBall τ₀ (min (ρ₁ / 2) (ρ₂ / 2)), τ.re ≠ 0 := by
    intro τ hτ hzero
    have hlt : dist τ τ₀ < ρ₂ := lt_of_le_of_lt (Metric.mem_closedBall.mp hτ) hρ₂'
    have hthis := hρ₂le hlt
    have h3 : dist (0 : ℝ) τ₀.re < |τ₀.re| := by rw [← hzero]; exact hthis
    rw [Real.dist_eq] at h3
    simp only [zero_sub, abs_neg] at h3
    exact absurd h3 (lt_irrefl _)
  -- the two bounds
  obtain ⟨C1, hC1, hlow⟩ := arc_low_bound ℓ d hd (T := 1) hclosedU0 hre
  obtain ⟨Ct, Mt, Tt, hCt, hMt, hTt, hdom⟩ := arc_trunc_dominator ℓ d hd hclosedU0 hre
  -- finiteness of the coincidence set
  have hcoin : ∀ τ : UpperHalfPlane, τ ∈ Metric.closedBall τ₀ (min (ρ₁ / 2) (ρ₂ / 2)) →
      ∃ S : Set ℝ, S.Finite ∧ ∀ (t : ℝ) (ht : 0 < t),
        Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) →
          t ∈ S := fun τ _ => coincidenceSet_finite τ
  -- the three pieces are continuous on the ball
  have hLow := Work.CKFinal.ArcFin.continuousOn_layerLow_ball ℓ d hd r
    (by positivity) hC1.le hlow hcoin
  have hTrunc := continuousOn_layerTrunc_ball' ℓ d hd r
    (by positivity) hCt hMt hTt hdom hcoin
  have hHigh : ContinuousOn (fun τ : UpperHalfPlane =>
      Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r)
      (Metric.ball τ₀ (min (ρ₁ / 2) (ρ₂ / 2))) :=
    (Work.CKFinal.AxisCont.continuous_highPart ℓ d hd r).continuousOn
  refine ⟨min (ρ₁ / 2) (ρ₂ / 2), lt_min hρ₁h hρ₂h, hballU0, ?_⟩
  have hfun : (fun τ : UpperHalfPlane =>
      Work.Asymptotics.paperLayer (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r)
      = fun τ : UpperHalfPlane => Work.Asymptotics.layerLow ℓ d τ r
          + Work.Asymptotics.layerTrunc (Work.Asymptotics.Gcusp ℓ d) ℓ d τ r
          + Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r := by
    funext τ
    simp only [Work.Asymptotics.paperLayer]
  rw [hfun]
  exact (hLow.add hTrunc).add hHigh

end Work.CKFinal.Socket
