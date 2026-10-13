import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.ProducerH.H2.Clause1Aux
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.BoxC2
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.ProducerH.H2

set_option autoImplicit false

/-! ## Elementary one-variable tools for the two radial blocks

The four statements below are the elementary inputs of `ABlock` (and of its siblings): the
interior Lipschitz bound of an angular slice from a bound on its `θ`-derivative (mean value
theorem), the extension of that bound to the closed interval from the two endpoint values and
the two endpoint rates, the continuity consequence, and the within-derivatives at the endpoints
of `[0,π/2]` from the one-sided limits of the derivative.  They are stated for a fixed radius
`z` so that the pointwise rate bounds of `BoxData` can be fed in at that radius.
-/

private theorem Mf_eq_zero (N0 N1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Mf N0 N1 Ψ z 0 = N0 z := by
  simp [Mf]

private theorem Mf_eq_pi (N0 N1 : ℝ → ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    Mf N0 N1 Ψ z (π / 2) = N1 z := by
  have h0 : ¬ ((π : ℝ) / 2 = 0) := ne_of_gt (by positivity)
  simp [Mf, h0]

private theorem Mf_eq_interior {N0 N1 : ℝ → ℝ} {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Mf N0 N1 Ψ z θ = Work.Spaces.pth (Work.Spaces.pz Ψ) z θ := by
  have h0 : ¬ (θ = 0) := ne_of_gt hθ.1
  have h1 : ¬ (θ = (π : ℝ) / 2) := ne_of_lt hθ.2
  simp only [Mf, if_neg h0, if_neg h1]

/-- Continuity of the `z`-slice of a function `C^∞` on the open quadrant. -/
theorem continuousOn_zslice_m {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {a b θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Set.Ioo (0 : ℝ) (π / 2)) :
    ContinuousOn (fun z => F z θ) (Set.Icc a b) :=
  ((hF.curry_z hθ).continuousOn).mono (fun z hz => lt_of_lt_of_le ha hz.1)

/-- The interior Lipschitz bound for an angular slice from a bound on its `θ`-derivative. -/
theorem abs_slice_theta_le_m {F : ℝ → ℝ → ℝ} (hF : Work.FTS.EllipticEst.SmoothOpen F)
    {z C : ℝ} (hz : 0 < z)
    (hb : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |Work.Spaces.pth F z θ| ≤ C) :
    ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
      |F z θ - F z θ'| ≤ C * |θ - θ'| := by
  intro θ hθ θ' hθ'
  have hdiff : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2), DifferentiableAt ℝ (fun θ'' => F z θ'') t :=
    fun t ht => ((hF.curry_θ hz).differentiableOn (by simp)).differentiableAt
      (isOpen_Ioo.mem_nhds ht)
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun θ'' => F z θ'')
    (s := Set.Ioo (0 : ℝ) (π / 2)) (x := θ') (y := θ) (C := C)
    hdiff (fun t ht => by rw [Real.norm_eq_abs]; exact hb t ht)
    (convex_Ioo 0 (π / 2)) hθ' hθ
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  exact h

/-- The two endpoint values plus the interior Lipschitz bound plus the two endpoint rates give
the Lipschitz bound on the whole closed angular interval. -/
theorem theta_modulus_Icc_m {F : ℝ → ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M) (z : ℝ)
    (h0 : F z 0 = 0) (hpi : F z (π / 2) = 0)
    (hint : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
      |F z θ - F z θ'| ≤ M * |θ - θ'|)
    (hr0 : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |F z θ| ≤ M * θ)
    (hr1 : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), |F z θ| ≤ M * (π / 2 - θ)) :
    ∀ θ ∈ Set.Icc (0 : ℝ) (π / 2), ∀ θ' ∈ Set.Icc (0 : ℝ) (π / 2),
      |F z θ - F z θ'| ≤ M * |θ - θ'| := by
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  have hf0 : ∀ t ∈ Set.Icc (0 : ℝ) (π / 2), |F z t - F z 0| ≤ M * t := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      rw [h0, sub_self, abs_zero]
      nlinarith [hM, Real.pi_pos]
    rcases eq_or_lt_of_le ht.2 with hp | hp
    · subst hp
      rw [h0, hpi, sub_zero, abs_zero]
      nlinarith [hM, Real.pi_pos]
    · rw [h0, sub_zero]
      exact hr0 t ⟨h, hp⟩
  have hfpi : ∀ t ∈ Set.Icc (0 : ℝ) (π / 2), |F z t - F z (π / 2)| ≤ M * (π / 2 - t) := by
    intro t ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h
      rw [h0, hpi, sub_self, abs_zero]
      nlinarith [hM, Real.pi_pos]
    rcases eq_or_lt_of_le ht.2 with hp | hp
    · subst hp
      rw [hpi, sub_self, abs_zero]
      nlinarith [hM, Real.pi_pos]
    · rw [hpi, sub_zero]
      exact hr1 t ⟨h, hp⟩
  intro θ hθ θ' hθ'
  rcases eq_or_lt_of_le hθ.1 with h | h
  · subst h
    rw [abs_sub_comm (F z 0) (F z θ'), zero_sub, abs_neg, abs_of_nonneg hθ'.1]
    exact hf0 θ' hθ'
  rcases eq_or_lt_of_le hθ.2 with hp | hp
  · subst hp
    rw [abs_sub_comm (F z (π / 2)) (F z θ'),
      abs_of_nonneg (show (0 : ℝ) ≤ π / 2 - θ' by linarith [hθ'.2])]
    exact hfpi θ' hθ'
  rcases eq_or_lt_of_le hθ'.1 with h' | h'
  · subst h'
    rw [sub_zero, abs_of_nonneg hθ.1]
    exact hf0 θ hθ
  rcases eq_or_lt_of_le hθ'.2 with hp' | hp'
  · subst hp'
    have h1 : |θ - (π : ℝ) / 2| = π / 2 - θ := by
      rw [abs_of_nonpos (by linarith [hθ.2]), neg_sub]
    rw [h1]
    exact hfpi θ hθ
  exact hint θ ⟨h, hp⟩ θ' ⟨h', hp'⟩

/-- A Lipschitz bound on the closed angular interval gives continuity there. -/
theorem continuousOn_Icc_of_abs_sub_le_m {f : ℝ → ℝ} {M : ℝ}
    (h : ∀ x ∈ Set.Icc (0 : ℝ) (π / 2), ∀ y ∈ Set.Icc (0 : ℝ) (π / 2),
      |f x - f y| ≤ M * |x - y|) :
    ContinuousOn f (Set.Icc (0 : ℝ) (π / 2)) := by
  have hq : (π : ℝ) / 4 ∈ Set.Icc (0 : ℝ) (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  by_cases hM : M ≤ 0
  · have hconst : ∀ x ∈ Set.Icc (0 : ℝ) (π / 2), f x = f (π / 4) := by
      intro x hx
      have h1 := h x hx (π / 4) hq
      have h2 : M * |x - π / 4| ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hM (abs_nonneg _)
      have h3 : |f x - f (π / 4)| = 0 := le_antisymm (le_trans h1 h2) (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp h3)
    exact (continuousOn_const (c := f (π / 4))).congr (fun x hx => hconst x hx)
  · have hMpos : 0 < M := not_le.mp hM
    intro x hx
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    refine ⟨ε / M, by positivity, fun y hy hd => ?_⟩
    have h1 := h y hy x hx
    have h2 : |y - x| < ε / M := by rwa [Real.dist_eq] at hd
    have h3 : M * |y - x| < ε := by
      have h4 := mul_lt_mul_of_pos_left h2 hMpos
      have h5 : M * (ε / M) = ε := mul_div_cancel₀ ε (ne_of_gt hMpos)
      linarith [h4, h5.le]
    rw [Real.dist_eq]
    exact lt_of_le_of_lt h1 h3

/-- Within-derivative at the left endpoint of `[0,T]` from the one-sided limit of the
derivative. -/
theorem hasDerivWithinAt_Icc_left_m {f f' : ℝ → ℝ} {T L : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn f (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ioo 0 T, HasDerivAt f (f' x) x)
    (hL : Filter.Tendsto f' (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    HasDerivWithinAt f L (Set.Icc 0 T) 0 := by
  have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 T) :=
    fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  have hcont0 : ContinuousWithinAt f (Set.Ioo 0 T) 0 :=
    (hcont.continuousWithinAt (Set.left_mem_Icc.mpr hT.le)).mono Set.Ioo_subset_Icc_self
  have hmem : Set.Ioo 0 T ∈ nhdsWithin 0 (Set.Ioi 0) := Ioo_mem_nhdsGT hT
  have hd' : Filter.Tendsto (fun x => deriv f x) (nhdsWithin 0 (Set.Ioi 0)) (nhds L) :=
    hL.congr' (Filter.eventually_of_mem hmem fun x hx => (hd x hx).deriv.symm)
  exact (hasDerivWithinAt_Ici_of_tendsto_deriv hdiff hcont0 hmem hd').mono
    (fun x hx => hx.1)

/-- Within-derivative at the right endpoint of `[0,T]` from the one-sided limit of the
derivative. -/
theorem hasDerivWithinAt_Icc_right_m {f f' : ℝ → ℝ} {T L : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn f (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ioo 0 T, HasDerivAt f (f' x) x)
    (hL : Filter.Tendsto f' (nhdsWithin T (Set.Iio T)) (nhds L)) :
    HasDerivWithinAt f L (Set.Icc 0 T) T := by
  have hdiff : DifferentiableOn ℝ f (Set.Ioo 0 T) :=
    fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  have hcontT : ContinuousWithinAt f (Set.Ioo 0 T) T :=
    (hcont.continuousWithinAt (Set.right_mem_Icc.mpr hT.le)).mono Set.Ioo_subset_Icc_self
  have hmem : Set.Ioo 0 T ∈ nhdsWithin T (Set.Iio T) := Ioo_mem_nhdsLT hT
  have hd' : Filter.Tendsto (fun x => deriv f x) (nhdsWithin T (Set.Iio T)) (nhds L) :=
    hL.congr' (Filter.eventually_of_mem hmem fun x hx => (hd x hx).deriv.symm)
  exact (hasDerivWithinAt_Iic_of_tendsto_deriv hdiff hcontT hmem hd').mono
    (fun x hx => hx.2)

theorem ABlock {α Ce : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    (hE : Work.FTS_EllLimOK.ProducerH.H2.Ctx α Ce E) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hdata : Work.FTS_EllLimOK.ProducerH.H2.BoxData α Ce E a b)
    (g : Work.FTS.Galerkin.Fn) (hg : Work.FTS.ClassC.ClassC α g)
    {C : ℝ} {L0 N0 L1 N1 : ℝ → ℝ}
    (hLim : Work.FTS_EllLimOK.ProducerH.H2.LimitsAt (E g) (Work.FTS.StrongGlobal.Xn6 α g) C a b
      L0 N0 L1 N1) :
    ContinuousOn (Function.uncurry (Work.Spaces.pz (E g))) (Work.FTS_EllLimOK.cbox a b) ∧
    ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz (E g))))
      (Work.FTS_EllLimOK.cbox a b) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun z' => Work.Spaces.pz (E g) z' θ)
        (Work.Spaces.pz (Work.Spaces.pz (E g)) z θ) (Set.Icc a b) z) ∧
    (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun θ' => Work.Spaces.pz (E g) z θ')
        (Work.FTS_EllLimOK.ProducerH.H2.Mf N0 N1 (E g) z θ) (Set.Icc 0 (π / 2)) θ) := by
  obtain ⟨K, hK, β, hβ, hmod, hrates, hlimr, hhol⟩ := hdata
  obtain ⟨Cb, hCb, hratesb⟩ := hrates
  have hbsl : Work.Elliptic.IsBslSol α g (E g) := (hE g hg).1.1
  have hSm : Work.FTS.EllipticEst.SmoothOpen (E g) := (hE g hg).1.2.1
  have hval0 : ∀ z : ℝ, (E g) z 0 = 0 := hbsl.2.1
  have hval1 : ∀ z : ℝ, (E g) z (π / 2) = 0 := hbsl.2.2.1
  have hX0 : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Xn6_nonneg α g
  have hM0 : 0 ≤ Cb * Work.FTS.StrongGlobal.Xn6 α g := mul_nonneg hCb.le hX0
  have hpi2 : (0 : ℝ) < π / 2 := by positivity
  -- the endpoint values of the two radial primitives
  have hpz0 : ∀ z : ℝ, Work.Spaces.pz (E g) z 0 = 0 := by
    intro z
    have hfun : (fun z' => (E g) z' 0) = fun _ => (0 : ℝ) := funext hval0
    rw [Work.Spaces.pz, hfun, deriv_const]
  have hpzpi : ∀ z : ℝ, Work.Spaces.pz (E g) z (π / 2) = 0 := by
    intro z
    have hfun : (fun z' => (E g) z' (π / 2)) = fun _ => (0 : ℝ) := funext hval1
    rw [Work.Spaces.pz, hfun, deriv_const]
  have hpzpz0 : ∀ z : ℝ, Work.Spaces.pz (Work.Spaces.pz (E g)) z 0 = 0 := by
    intro z
    have hfun : (fun z' => Work.Spaces.pz (E g) z' 0) = fun _ => (0 : ℝ) := funext hpz0
    rw [Work.Spaces.pz, hfun, deriv_const]
  have hpzpzpi : ∀ z : ℝ, Work.Spaces.pz (Work.Spaces.pz (E g)) z (π / 2) = 0 := by
    intro z
    have hfun : (fun z' => Work.Spaces.pz (E g) z' (π / 2)) = fun _ => (0 : ℝ) := funext hpzpi
    rw [Work.Spaces.pz, hfun, deriv_const]
  -- the angular Lipschitz bounds on the closed interval
  have hmodpz : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2), ∀ θ' ∈ Set.Icc 0 (π / 2),
      |Work.Spaces.pz (E g) z θ - Work.Spaces.pz (E g) z θ'|
        ≤ (Cb * Work.FTS.StrongGlobal.Xn6 α g) * |θ - θ'| := by
    intro z hz
    refine theta_modulus_Icc_m hM0 z (hpz0 z) (hpzpi z) ?_ ?_ ?_
    · intro θ hθ θ' hθ'
      have hb : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2),
          |Work.Spaces.pth (Work.Spaces.pz (E g)) z t| ≤ Cb * Work.FTS.StrongGlobal.Xn6 α g := by
        intro t ht
        obtain ⟨_, _, _, h4, _, _, _, _, _, _, _, _, _, _⟩ := hratesb g hg z hz t ht
        exact h4
      exact abs_slice_theta_le_m hSm.pz (lt_of_lt_of_le ha hz.1) hb θ hθ θ' hθ'
    · intro θ hθ
      obtain ⟨_, _, _, _, _, _, _, _, h9, _, _, _, _, _⟩ := hratesb g hg z hz θ hθ
      exact h9
    · intro θ hθ
      obtain ⟨_, _, _, _, _, _, _, _, _, _, h11, _, _, _⟩ := hratesb g hg z hz θ hθ
      exact h11
  have hmodpzpz : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2), ∀ θ' ∈ Set.Icc 0 (π / 2),
      |Work.Spaces.pz (Work.Spaces.pz (E g)) z θ - Work.Spaces.pz (Work.Spaces.pz (E g)) z θ'|
        ≤ (Cb * Work.FTS.StrongGlobal.Xn6 α g) * |θ - θ'| := by
    intro z hz
    refine theta_modulus_Icc_m hM0 z (hpzpz0 z) (hpzpzpi z) ?_ ?_ ?_
    · intro θ hθ θ' hθ'
      have hb : ∀ t ∈ Set.Ioo (0 : ℝ) (π / 2),
          |Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pz (E g))) z t|
            ≤ Cb * Work.FTS.StrongGlobal.Xn6 α g := by
        intro t ht
        obtain ⟨_, _, _, _, _, _, h7, _, _, _, _, _, _, _⟩ := hratesb g hg z hz t ht
        exact h7
      exact abs_slice_theta_le_m hSm.pz.pz (lt_of_lt_of_le ha hz.1) hb θ hθ θ' hθ'
    · intro θ hθ
      obtain ⟨_, _, _, _, _, _, _, _, _, h10, _, _, _, _⟩ := hratesb g hg z hz θ hθ
      exact h10
    · intro θ hθ
      obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h12, _, _⟩ := hratesb g hg z hz θ hθ
      exact h12
  -- continuity on the closed box
  have hcontpz : ContinuousOn (Function.uncurry (Work.Spaces.pz (E g))) (cbox a b) := by
    refine Work.FTS_EllLimOK.ProducerH.BoxAux.continuousOn_of_thetaModulus
      (a₀ := a) (b₀ := b) (C := Cb * Work.FTS.StrongGlobal.Xn6 α g) (β := 1) one_pos ?_ ?_
    · intro z hz θ hθ θ' hθ'
      rw [Real.rpow_one]
      exact hmodpz z hz θ hθ θ' hθ'
    · intro θ hθ
      exact continuousOn_zslice_m hSm.pz ha hθ
  have hcontpzpz : ContinuousOn (Function.uncurry (Work.Spaces.pz (Work.Spaces.pz (E g))))
      (cbox a b) := by
    refine Work.FTS_EllLimOK.ProducerH.BoxAux.continuousOn_of_thetaModulus
      (a₀ := a) (b₀ := b) (C := Cb * Work.FTS.StrongGlobal.Xn6 α g) (β := 1) one_pos ?_ ?_
    · intro z hz θ hθ θ' hθ'
      rw [Real.rpow_one]
      exact hmodpzpz z hz θ hθ θ' hθ'
    · intro θ hθ
      exact continuousOn_zslice_m hSm.pz.pz ha hθ
  -- the angular slices of the two primitives are continuous on the closed interval
  have hcontθ : ∀ z ∈ Set.Icc a b,
      ContinuousOn (fun θ' => Work.Spaces.pz (E g) z θ') (Set.Icc 0 (π / 2)) :=
    fun z hz => continuousOn_Icc_of_abs_sub_le_m (fun x hx y hy => hmodpz z hz x hx y hy)
  -- the radial within-derivative
  have hzderiv : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun z' => Work.Spaces.pz (E g) z' θ)
        (Work.Spaces.pz (Work.Spaces.pz (E g)) z θ) (Set.Icc a b) z := by
    intro z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    rcases eq_or_lt_of_le hθ.1 with h | h
    · subst h
      have hfun : (fun z' => Work.Spaces.pz (E g) z' 0) = fun _ => (0 : ℝ) := funext hpz0
      rw [hfun, hpzpz0 z]
      exact hasDerivWithinAt_const z (Set.Icc a b) 0
    rcases eq_or_lt_of_le hθ.2 with hp | hp
    · subst hp
      have hfun : (fun z' => Work.Spaces.pz (E g) z' (π / 2)) = fun _ => (0 : ℝ) := funext hpzpi
      rw [hfun, hpzpzpi z]
      exact hasDerivWithinAt_const z (Set.Icc a b) 0
    · exact ((hSm.pz).hasDerivAt_slice ⟨h, hp⟩ hz0).hasDerivWithinAt
  -- the angular within-derivative
  have hthderiv : ∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivWithinAt (fun θ' => Work.Spaces.pz (E g) z θ')
        (Mf N0 N1 (E g) z θ) (Set.Icc 0 (π / 2)) θ := by
    intro z hz θ hθ
    have hz0 : 0 < z := lt_of_lt_of_le ha hz.1
    have hCd : ContDiffOn ℝ Work.Stability.smoothOrder (fun θ' => Work.Spaces.pz (E g) z θ')
        (Set.Ioo 0 (π / 2)) := (hSm.pz).curry_θ hz0
    have hd : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2),
        HasDerivAt (fun θ' => Work.Spaces.pz (E g) z θ')
          (Work.Spaces.pth (Work.Spaces.pz (E g)) z x) x := fun x hx =>
      (hCd.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hx) |>.hasDerivAt
    have hcl : ∀ x ∈ Set.Ioo (0 : ℝ) (π / 2),
        Work.Spaces.pz (Work.Spaces.pth (E g)) z x
          = Work.Spaces.pth (Work.Spaces.pz (E g)) z x := fun x hx =>
      Work.Spaces.pz_pth_comm (((hSm.forall 2)).contDiffAt
        (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz0, hx.1, hx.2⟩)))
    have hL0 : Filter.Tendsto (fun x => Work.Spaces.pth (Work.Spaces.pz (E g)) z x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (N0 z)) :=
      (hLim.2.2.1 z hz).congr' (Filter.eventually_of_mem (Ioo_mem_nhdsGT hpi2) hcl)
    have hL1 : Filter.Tendsto (fun x => Work.Spaces.pth (Work.Spaces.pz (E g)) z x)
        (nhdsWithin (π / 2) (Set.Iio (π / 2))) (nhds (N1 z)) :=
      (hLim.2.2.2.2.2.2.1 z hz).congr' (Filter.eventually_of_mem (Ioo_mem_nhdsLT hpi2) hcl)
    rcases eq_or_lt_of_le hθ.1 with h | h
    · subst h
      rw [Mf_eq_zero]
      exact hasDerivWithinAt_Icc_left_m hpi2 (hcontθ z hz) hd hL0
    rcases eq_or_lt_of_le hθ.2 with hp | hp
    · subst hp
      rw [Mf_eq_pi]
      exact hasDerivWithinAt_Icc_right_m hpi2 (hcontθ z hz) hd hL1
    · rw [Mf_eq_interior ⟨h, hp⟩]
      exact (hd θ ⟨h, hp⟩).hasDerivWithinAt
  exact ⟨hcontpz, hcontpzpz, hzderiv, hthderiv⟩

end Work.FTS_EllLimOK.ProducerH.H2
