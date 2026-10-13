import Mathlib
import Submission.Work.WilE3.Frame.CutSys
import Submission.Work.WilE3.Frame.kernel_frame_rows
import Submission.Work.WilE3.Frame.curve_tangent
import Submission.Work.WilE3.Frame.grad_cutPoly
import Submission.Work.WilE3.Frame.fderiv_curve_eq_VcoefC
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

namespace Work.WilE3.Frame

set_option autoImplicit false
noncomputable section
open Classical Topology Matrix
open WilkiesDesign.E
open Work.WilE3 (jacDet)

variable {k r j : ℕ}

/-! ## §1. Two auxiliary lemmas (the two halves of the algebra of the cut system)

The first is purely algebraic: it computes the derivative of the complexified evaluation of an EA
polynomial in terms of the `eaD`-derivatives.  The second is the algebraic heart of the frame step:
a vector in the span of the tangential frame which is killed by the cut rows lies on the line
`ℂ • Σ_l w_l V_l`.  The third is the chain rule identity identifying the `f`-row with the derivative
of the curve function. -/

/-- The derivative of `eaEvalC c Q` at `z`, applied to a vector. -/
private lemma fderiv_eaEvalC_apply (c : EAChain k r) (Q : EAPoly k r) (z v : Fin k → ℂ) :
    fderiv ℂ (Work.WilE3.eaEvalC c Q) z v =
      ∑ i : Fin k, Work.WilE3.eaEvalC c (eaD c i Q) z * v i := by
  have h := (Work.WilE3.API.eaEvalC_fderiv_analytic c Q z).2
  rw [h.fderiv]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- **The cut rows cut the frame line down to the direction `w`.**  Let `v` be a complex vector
which is a linear combination `v = Σ_l c_l • V_l (z)` of the tangential frame vectors
`VcoefC c h ι l` (`l` ranging over the `ι`-complement), and suppose that `v` is killed by all the
complexified cut forms `cutPoly ι (μ a) x`, i.e. `Σ_i (∂_i (cutPoly ι (μ a) x))(z) · v_i = 0` for
every `a`.  If the real linear forms `μ a` annihilate the real direction `w ≠ 0` and have common
kernel of dimension at most one (`CutForms ι w μ`), then `v` is a `ℂ`-multiple of the contraction
`Σ_l w_l • V_l (z)`.

`grad_cutPoly` computes `(∂_i (cutPoly ι (μ a) x))(z) = 0` on `Set.range ι` and
`= (μ a ⟨i,h⟩ : ℂ)` off it, so `Σ_i (∂_i L_a)(z) · (V_l)_i = (μ a l : ℂ)` for `l : U k ι`
(`sum_VcoefC_mul`).  Substituting `v = Σ_l c_l • V_l` turns the cut conditions into
`Σ_l c_l · (μ a l : ℂ) = 0`; taking real and imaginary parts, both `Re c` and `Im c` lie in the
kernel of the `μ a`, which is `ℝ • w` by `CutForms`; hence `c_l = (α + β I) * (w l : ℂ)`. -/
private lemma smul_of_cut_rows_aux (c : EAChain k r)
    (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (x : Fin k → ℝ)
    (w : U k ι → ℝ) (hw : w ≠ 0)
    (μ : Fin (k - j - 1) → (U k ι → ℝ)) (hμ : CutForms ι w μ)
    (z : Fin k → ℂ) (v : Fin k → ℂ) (c' : U k ι → ℂ)
    (hv : v = ∑ l : U k ι, c' l • VcoefC c h ι l z)
    (hcut : ∀ a : Fin (k - j - 1),
      ∑ i : Fin k, Work.WilE3.eaEvalC c (eaD c i (cutPoly ι (μ a) x)) z * v i = 0) :
    ∃ (lam : ℂ), v = lam • ∑ l : U k ι, (w l : ℂ) • VcoefC c h ι l z := by
  -- (1) the cut conditions, written in terms of `c'`
  have h1 : ∀ a : Fin (k - j - 1), (∑ l : U k ι, c' l * (μ a l : ℂ)) = 0 := by
    intro a
    have ha := hcut a
    rw [hv] at ha
    have hsplit : (∑ i : Fin k, Work.WilE3.eaEvalC c (eaD c i (cutPoly ι (μ a) x)) z *
          (∑ l : U k ι, c' l • VcoefC c h ι l z) i)
        = ∑ l : U k ι, c' l * (μ a l : ℂ) := by
      have hinner : ∀ l : U k ι, (∑ i : Fin k,
            Work.WilE3.eaEvalC c (eaD c i (cutPoly ι (μ a) x)) z *
              VcoefC c h ι l z i) = (μ a l : ℂ) := by
        intro l
        rw [Finset.sum_congr rfl (fun i _ => mul_comm _ _), sum_VcoefC_mul]
        have hl : Work.WilE3.eaEvalC c (eaD c (l : Fin k) (cutPoly ι (μ a) x)) z
            = (μ a l : ℂ) := by
          rw [grad_cutPoly]
          exact dif_neg l.2
        have hb : ∀ b : Fin j,
            Work.WilE3.eaEvalC c (eaD c (ι b) (cutPoly ι (μ a) x)) z = 0 := by
          intro b
          rw [grad_cutPoly]
          exact dif_pos (Set.mem_range_self b)
        rw [hl, Finset.sum_eq_zero (fun b _ => by rw [hb b, mul_zero]), sub_zero]
      calc ∑ i : Fin k, Work.WilE3.eaEvalC c (eaD c i (cutPoly ι (μ a) x)) z *
            (∑ l : U k ι, c' l • VcoefC c h ι l z) i
          = ∑ i : Fin k, ∑ l : U k ι,
              Work.WilE3.eaEvalC c (eaD c i (cutPoly ι (μ a) x)) z *
                (c' l * VcoefC c h ι l z i) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        _ = ∑ l : U k ι, ∑ i : Fin k,
              Work.WilE3.eaEvalC c (eaD c i (cutPoly ι (μ a) x)) z *
                (c' l * VcoefC c h ι l z i) := Finset.sum_comm
        _ = ∑ l : U k ι, c' l * (∑ i : Fin k,
              Work.WilE3.eaEvalC c (eaD c i (cutPoly ι (μ a) x)) z *
                VcoefC c h ι l z i) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ = ∑ l : U k ι, c' l * (μ a l : ℂ) :=
            Finset.sum_congr rfl fun l _ => by rw [hinner l]
    rw [hsplit] at ha
    exact ha
  -- (2) real and imaginary parts lie in the common kernel of the `μ a`
  have hterm_re : ∀ (a : Fin (k - j - 1)) (l : U k ι),
      (c' l * (μ a l : ℂ)).re = (c' l).re * μ a l := by
    intro a l
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hterm_im : ∀ (a : Fin (k - j - 1)) (l : U k ι),
      (c' l * (μ a l : ℂ)).im = (c' l).im * μ a l := by
    intro a l
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  have hre : ∀ a : Fin (k - j - 1), ∑ l : U k ι, (c' l).re * μ a l = 0 := by
    intro a
    have h := congrArg Complex.re (h1 a)
    simp only [Complex.zero_re, Complex.re_sum] at h
    rwa [Finset.sum_congr rfl (fun l _ => hterm_re a l)] at h
  have him : ∀ a : Fin (k - j - 1), ∑ l : U k ι, (c' l).im * μ a l = 0 := by
    intro a
    have h := congrArg Complex.im (h1 a)
    simp only [Complex.zero_im, Complex.im_sum] at h
    rwa [Finset.sum_congr rfl (fun l _ => hterm_im a l)] at h
  have hre' : ∀ a : Fin (k - j - 1), ∑ l : U k ι, μ a l * (fun l => (c' l).re) l = 0 := by
    intro a
    rw [← hre a]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  have him' : ∀ a : Fin (k - j - 1), ∑ l : U k ι, μ a l * (fun l => (c' l).im) l = 0 := by
    intro a
    rw [← him a]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  -- (3) `CutForms` forces both parts to be multiples of `w`
  obtain ⟨c1, c2, hne, hprop⟩ := hμ.2 (fun l => (c' l).re) w hre' hμ.1
  obtain ⟨c3, c4, hne', hprop'⟩ := hμ.2 (fun l => (c' l).im) w him' hμ.1
  have hw0 : ∀ cc : ℝ, cc ≠ 0 → cc • w = 0 → False := by
    intro cc hcc h
    exact hw (by
      have := congrArg (fun u : U k ι → ℝ => cc⁻¹ • u) h
      simpa [smul_smul, inv_mul_cancel₀ hcc, one_smul] using this)
  have hc1 : c1 ≠ 0 := by
    intro h0
    have hc2 : c2 ≠ 0 := by
      intro h2
      exact hne (by simp [h0, h2])
    rw [h0, zero_smul] at hprop
    exact hw0 c2 hc2 hprop.symm
  have hc3 : c3 ≠ 0 := by
    intro h0
    have hc4 : c4 ≠ 0 := by
      intro h4
      exact hne' (by simp [h0, h4])
    rw [h0, zero_smul] at hprop'
    exact hw0 c4 hc4 hprop'.symm
  have hRec : (fun l => (c' l).re) = (c1⁻¹ * c2) • w := by
    have := congrArg (fun u : U k ι → ℝ => c1⁻¹ • u) hprop
    simpa [smul_smul, inv_mul_cancel₀ hc1, one_smul] using this
  have hImc : (fun l => (c' l).im) = (c3⁻¹ * c4) • w := by
    have := congrArg (fun u : U k ι → ℝ => c3⁻¹ • u) hprop'
    simpa [smul_smul, inv_mul_cancel₀ hc3, one_smul] using this
  -- (4) conclude
  refine ⟨(c1⁻¹ * c2 : ℝ) + (c3⁻¹ * c4 : ℝ) * Complex.I, ?_⟩
  have hc'l : ∀ l : U k ι,
      c' l = ((c1⁻¹ * c2 : ℝ) + (c3⁻¹ * c4 : ℝ) * Complex.I) * (w l : ℂ) := by
    intro l
    have h1l : (c' l).re = c1⁻¹ * c2 * w l := by
      have := congrFun hRec l
      simpa using this
    have h2l : (c' l).im = c3⁻¹ * c4 * w l := by
      have := congrFun hImc l
      simpa using this
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero]
      rw [h1l]
    · simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, add_zero, zero_add]
      rw [h2l]
  rw [hv]
  calc ∑ l : U k ι, c' l • VcoefC c h ι l z
      = ∑ l : U k ι,
          (((c1⁻¹ * c2 : ℝ) + (c3⁻¹ * c4 : ℝ) * Complex.I) * (w l : ℂ)) •
            VcoefC c h ι l z :=
        Finset.sum_congr rfl fun l _ => by rw [hc'l l]
    _ = ∑ l : U k ι,
          (((c1⁻¹ * c2 : ℝ) + (c3⁻¹ * c4 : ℝ) * Complex.I)) •
            ((w l : ℂ) • VcoefC c h ι l z) :=
        Finset.sum_congr rfl fun l _ => by rw [smul_smul]
    _ = (((c1⁻¹ * c2 : ℝ) + (c3⁻¹ * c4 : ℝ) * Complex.I)) •
          ∑ l : U k ι, (w l : ℂ) • VcoefC c h ι l z := (Finset.smul_sum).symm

/-- **The derivative of the curve function.**  With `Ψ` straightening `{h = 0}` at `x` and `w` a
real direction, the one-variable function `t ↦ eaEvalC c f (Ψ (u₀ + t • w_ℂ, 0))` has, near
`t = 0`, derivative equal to the contraction of the derivative of `eaEvalC c f` at `Ψ (u₀ + t • w_ℂ, 0)`
with the tangent vector `Σ_l w_l • V_l` of the straightened curve.

The slice `v ↦ Ψ (v, 0)` is differentiable near `u₀` (it is analytic there by `hΨ.2.1`), so the
chain rule along the affine line `t ↦ u₀ + t • w_ℂ` computes the derivative; `fderiv_curve_eq_VcoefC`
identifies `fderiv` of the slice with the frame field `VcoefC` on the standard basis, and
`fderiv_eaEvalC_apply` expands the derivative of `eaEvalC c f`. -/
private lemma deriv_curve_eval_aux (c : EAChain k r)
    (h : Fin j → EAPoly k r) (ι : Fin j → Fin k)
    (f : EAPoly k r) (x : Fin k → ℝ)
    (Ψ : ((U k ι → ℂ) × (Fin j → ℂ)) → (Fin k → ℂ))
    (hΨ : IsStraightening c h ι x Ψ)
    (hd : (Matrix.of fun a b => Work.WilE3.eaEvalC c (eaD c (ι b) (h a))
      (toC x)).det ≠ 0)
    (w : U k ι → ℝ) :
    ∀ᶠ t in nhds (0 : ℂ),
      deriv (fun t' : ℂ => Work.WilE3.eaEvalC c f
          (Ψ (uCoord k ι (toC x) +
            t' • (fun i => (w i : ℂ)), 0))) t =
        ∑ i : Fin k, Work.WilE3.eaEvalC c (eaD c i f)
          (Ψ (uCoord k ι (toC x) +
            t • (fun i => (w i : ℂ)), 0)) *
          (∑ l : U k ι, (w l : ℂ) • VcoefC c h ι l
            (Ψ (uCoord k ι (toC x) +
              t • (fun i => (w i : ℂ)), 0))) i := by
  classical
  let F : (U k ι → ℂ) → (Fin k → ℂ) := fun v => Ψ (v, 0)
  let u₀ : U k ι → ℂ := uCoord k ι (toC x)
  let wC : U k ι → ℂ := fun i => (w i : ℂ)
  let G : (U k ι → ℂ) → ℂ := fun v => Work.WilE3.eaEvalC c f (F v)
  change ∀ᶠ t in nhds (0 : ℂ),
      deriv (fun t' : ℂ => G (u₀ + t' • wC)) t =
        ∑ i : Fin k, Work.WilE3.eaEvalC c (eaD c i f) (F (u₀ + t • wC)) *
          (∑ l : U k ι, (w l : ℂ) • VcoefC c h ι l (F (u₀ + t • wC))) i
  -- (1) the slice `v ↦ Ψ (v, 0)` is differentiable near `u₀`
  have hslice : ∀ᶠ v in 𝓝 u₀, HasFDerivAt F (fderiv ℂ F v) v := by
    have hinl : Filter.Tendsto (fun v : U k ι → ℂ => (v, (0 : Fin j → ℂ)))
        (𝓝 u₀) (𝓝 (u₀, 0)) := by
      have hc : Continuous fun v : U k ι → ℂ => (v, (0 : Fin j → ℂ)) := by fun_prop
      simpa using hc.tendsto u₀
    have h1 : ∀ᶠ v in 𝓝 u₀, AnalyticAt ℂ Ψ (v, 0) :=
      hinl.eventually hΨ.2.1.eventually_analyticAt
    refine h1.mono fun v hv => ?_
    have hfun : (⇑(ContinuousLinearMap.inl ℂ (U k ι → ℂ) (Fin j → ℂ))) =
        (fun v' : U k ι → ℂ => (v', (0 : Fin j → ℂ))) := by
      funext v'
      simp [ContinuousLinearMap.inl_apply]
    have hvd : HasFDerivAt (fun v' : U k ι → ℂ => (v', (0 : Fin j → ℂ)))
        (ContinuousLinearMap.inl ℂ (U k ι → ℂ) (Fin j → ℂ)) v := by
      have hh := (ContinuousLinearMap.inl ℂ (U k ι → ℂ) (Fin j → ℂ)).hasFDerivAt (x := v)
      rwa [hfun] at hh
    have hcomp := (hv.differentiableAt.hasFDerivAt).comp v hvd
    have hfun2 : (Ψ ∘ fun v' : U k ι → ℂ => (v', (0 : Fin j → ℂ))) =
        (fun v' : U k ι → ℂ => Ψ (v', 0)) := rfl
    rw [hfun2] at hcomp
    rw [← hcomp.fderiv] at hcomp
    simpa [F] using hcomp
  -- (2) `G` is differentiable near `u₀`
  have hGdiff : ∀ᶠ v in 𝓝 u₀, HasFDerivAt G (fderiv ℂ G v) v := by
    refine hslice.mono fun v hv => ?_
    have h2 : HasFDerivAt (Work.WilE3.eaEvalC c f)
        (fderiv ℂ (Work.WilE3.eaEvalC c f) (F v)) (F v) :=
      ((Work.WilE3.API.eaEvalC_fderiv_analytic c f (F v)).1).differentiableAt.hasFDerivAt
    have hcomp := h2.comp v hv
    have hfun : (Work.WilE3.eaEvalC c f) ∘ F = G := rfl
    rw [hfun] at hcomp
    rw [← hcomp.fderiv] at hcomp
    exact hcomp
  -- (3) the derivative of `G` along the line
  have hline : ∀ t : ℂ, HasDerivAt (fun t' : ℂ => u₀ + t' • wC) wC t := fun t => by
    have h := ((ContinuousLinearMap.toSpanSingleton ℂ wC).hasFDerivAt (x := t)).const_add u₀
    have h2 : HasDerivAt (fun t' : ℂ => u₀ + (ContinuousLinearMap.toSpanSingleton ℂ wC) t')
        ((ContinuousLinearMap.toSpanSingleton ℂ wC) 1) t := h.hasDerivAt
    simpa [ContinuousLinearMap.toSpanSingleton_apply] using h2
  have htend : Filter.Tendsto (fun t : ℂ => u₀ + t • wC) (𝓝 0) (𝓝 u₀) := by
    have hc : Continuous fun t : ℂ => u₀ + t • wC := by fun_prop
    simpa using hc.tendsto (0 : ℂ)
  have hder : ∀ᶠ t in 𝓝 (0 : ℂ),
      deriv (fun t' : ℂ => G (u₀ + t' • wC)) t = fderiv ℂ G (u₀ + t • wC) wC := by
    filter_upwards [htend.eventually hGdiff] with t ht
    have hcomp := ht.comp_hasDerivAt t (hline t)
    exact hcomp.deriv
  -- (4) on the line, `fderiv F` is the frame field contracted with `w`
  have hlin : ∀ᶠ v in 𝓝 u₀,
      fderiv ℂ F v wC = ∑ l : U k ι, (w l : ℂ) • VcoefC c h ι l (F v) := by
    have hall : ∀ᶠ v in 𝓝 u₀, ∀ l : U k ι,
        fderiv ℂ F v (Pi.single l 1) = VcoefC c h ι l (F v) :=
      (Filter.eventually_all (ι := U k ι)).mpr fun l =>
        fderiv_curve_eq_VcoefC c h ι x Ψ hΨ.2.2.1 hΨ.1 hΨ.2.1 hd l
    refine hall.mono fun v hv => ?_
    have hwC : wC = ∑ l : U k ι, (w l : ℂ) • Pi.single l (1 : ℂ) := by
      rw [pi_eq_sum_univ' wC]
    rw [hwC, map_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [map_smul, hv l]
  -- (5) assemble
  filter_upwards [hder, htend.eventually hlin, htend.eventually hslice] with t h1 h2 hs
  have hFder : HasFDerivAt F (fderiv ℂ F (u₀ + t • wC)) (u₀ + t • wC) := hs
  have hcomp2 : HasFDerivAt G ((fderiv ℂ (Work.WilE3.eaEvalC c f) (F (u₀ + t • wC))).comp
      (fderiv ℂ F (u₀ + t • wC))) (u₀ + t • wC) := by
    have h2' : HasFDerivAt (Work.WilE3.eaEvalC c f)
        (fderiv ℂ (Work.WilE3.eaEvalC c f) (F (u₀ + t • wC))) (F (u₀ + t • wC)) :=
      ((Work.WilE3.API.eaEvalC_fderiv_analytic c f (F (u₀ + t • wC))).1).differentiableAt.hasFDerivAt
    have hcomp := h2'.comp (u₀ + t • wC) hFder
    have hfun : (Work.WilE3.eaEvalC c f) ∘ F = G := rfl
    rwa [hfun] at hcomp
  rw [h1, hcomp2.fderiv, ContinuousLinearMap.comp_apply, h2, fderiv_eaEvalC_apply]

/-! ## §2. The main lemma -/

/-- **The Jacobian of the cut system has no kernel vector.**  At a point `z` where `Δ = jacValC` is
nonzero, the rows of the `k × k` matrix of the cut system `(h, L, f)` kill no nonzero vector:

* the `h`-rows force `v` into the span of the tangential frame
  (`Work.WilE3.Frame.kernel_frame_rows`),
* the cut rows (`L a = cutPoly ι (μ a) x`) cut that span down to the line `ℂ • Σ_l w_l V_l (z)`
  (`smul_of_cut_rows_aux`),
* on that line the `f`-row is the derivative of the curve function (`deriv_curve_eval_aux`), so it
  is nonzero on it by `hnd`. -/
private lemma det_ne_zero_of_rows (c : EAChain k r)
    (h : Fin j → EAPoly k r) (ι : Fin j → Fin k) (f : EAPoly k r) (x : Fin k → ℝ)
    (hjk : j < k) (hι : Function.Injective ι)
    (w : U k ι → ℝ) (hw : w ≠ 0)
    (μ : Fin (k - j - 1) → (U k ι → ℝ)) (hμ : CutForms ι w μ)
    (z : Fin k → ℂ) (hΔ : jacValC c h ι z ≠ 0)
    (hnd : (∑ i : Fin k, Work.WilE3.eaEvalC c (eaD c i f) z *
      (∑ l : U k ι, (w l : ℂ) • VcoefC c h ι l z) i) ≠ 0) :
    (Matrix.of fun i i' => Work.WilE3.eaEvalC c
      (eaD c i' (cutSys h (fun a => cutPoly ι (μ a) x) f i)) z).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hvne, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  -- The `h`-rows put `v` in the span of the tangential frame.
  have hkerH : ∀ a : Fin j, ∑ i, v i * Work.WilE3.eaEvalC c (eaD c i (h a)) z = 0 := by
    intro a
    have h1 := congrFun hv0 (rowH hjk a)
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h1
    rw [cutSys_rowH hjk h (fun a => cutPoly ι (μ a) x) f a] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  obtain ⟨c', hc'⟩ := (kernel_frame_rows c h ι hι z hΔ v).mp hkerH
  -- The cut rows cut that span down to `ℂ • Σ_l w_l V_l (z)`.
  have hkerL : ∀ a : Fin (k - j - 1),
      ∑ i, Work.WilE3.eaEvalC c (eaD c i (cutPoly ι (μ a) x)) z * v i = 0 := by
    intro a
    have h1 := congrFun hv0 (rowL hjk a)
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h1
    rw [cutSys_rowL hjk h (fun a => cutPoly ι (μ a) x) f a] at h1
    exact h1
  obtain ⟨lam, hlam⟩ := smul_of_cut_rows_aux c h ι x w hw μ hμ z v c' hc' hkerL
  -- The `f`-row is a nonzero multiple of the derivative of the curve function.
  have hrowF := congrFun hv0 (rowF hjk)
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at hrowF
  rw [cutSys_rowF hjk h (fun a => cutPoly ι (μ a) x) f] at hrowF
  rw [hlam] at hrowF
  have hfac : (∑ i : Fin k, Work.WilE3.eaEvalC c (eaD c i f) z *
        (lam • ∑ l : U k ι, (w l : ℂ) • VcoefC c h ι l z) i)
      = lam * ∑ i : Fin k, Work.WilE3.eaEvalC c (eaD c i f) z *
        (∑ l : U k ι, (w l : ℂ) • VcoefC c h ι l z) i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [Pi.smul_apply, smul_eq_mul]; ring
  have hprod : lam * (∑ i : Fin k, Work.WilE3.eaEvalC c (eaD c i f) z *
        (∑ l : U k ι, (w l : ℂ) • VcoefC c h ι l z) i) = 0 := by
    rw [← hfac]
    exact hrowF
  rcases mul_eq_zero.mp hprod with h0 | h0
  · exact hvne (by rw [hlam, h0, zero_smul])
  · exact hnd h0

/-- **The simple zeros of the curve function are nondegenerate zeros of the cut system.**  With `Ψ`
straightening `{h = 0}` at `x`, `μ` cut forms annihilating the real direction `w ≠ 0`, `hjk : j < k`
and `ι` injective, at every `t` near `0` at which the one variable function
`t ↦ eaEvalC c f (Ψ (u₀ + t • w_ℂ, 0))` has nonzero derivative, the Jacobian determinant of the cut
system `(h, L, f)` (`L a = cutPoly ι (μ a) x`) at `Z(t) = Ψ (u₀ + t • w_ℂ, 0)` is nonzero.

Indeed the first `k - 1` rows have as common kernel the line `ℂ • V(w)` with
`V(w) = Σ_l w_l • VcoefC c h ι l Z(t)`: by `kernel_frame_rows` (applied at `Z(t)`, where `jacValC` is
nonzero for `t` near `0` by continuity and `hd`) such a `v` is `Σ_l c_l • V_l`, and the cut rows
(`grad_cutPoly`) turn that into `Σ_l μ a l * c l = 0`, so the real and imaginary parts of `c` lie in
the at-most-one-dimensional kernel of the `μ a`, i.e. in `ℝ • w`; hence `c = λ • w` and
`v = λ • V(w)`.  `V(w) ≠ 0` because `V(w)` has `w ≠ 0` as its `ιᶜ`-coordinates.  Finally the last row
`∂f (Z t)` is the chain rule derivative of the curve function (`curve_tangent`), which is nonzero by
`ht`; hence the common kernel of all `k` rows is `{0}` and the determinant is nonzero. -/
theorem nondeg_of_curve {k r j : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (h : Fin j → WilkiesDesign.E.EAPoly k r) (ι : Fin j → Fin k)
    (f : WilkiesDesign.E.EAPoly k r) (x : Fin k → ℝ) (hjk : j < k)
    (hι : Function.Injective ι)
    (hxe : ∀ a, Work.WilE3.eaEvalC c (h a) (Work.WilE3.Frame.toC x) = 0)
    (hd : (Matrix.of fun a b => Work.WilE3.eaEvalC c (WilkiesDesign.E.eaD c (ι b) (h a))
      (Work.WilE3.Frame.toC x)).det ≠ 0)
    (Ψ : ((Work.WilE3.Frame.U k ι → ℂ) × (Fin j → ℂ)) → (Fin k → ℂ))
    (hΨ : Work.WilE3.Frame.IsStraightening c h ι x Ψ)
    (w : Work.WilE3.Frame.U k ι → ℝ) (hw : w ≠ 0)
    (μ : Fin (k - j - 1) → (Work.WilE3.Frame.U k ι → ℝ))
    (hμ : Work.WilE3.Frame.CutForms ι w μ) :
    ∀ᶠ t in nhds (0 : ℂ),
      deriv (fun t' : ℂ => Work.WilE3.eaEvalC c f
        (Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x) +
          t' • (fun i => (w i : ℂ)), 0))) t ≠ 0 →
      (Matrix.of fun i i' => Work.WilE3.eaEvalC c
        (WilkiesDesign.E.eaD c i' (Work.WilE3.Frame.cutSys h
          (fun a => Work.WilE3.Frame.cutPoly ι (μ a) x) f i))
        (Ψ (Work.WilE3.Frame.uCoord k ι (Work.WilE3.Frame.toC x) +
          t • (fun i => (w i : ℂ)), 0))).det ≠ 0 := by
  have hd' : jacValC c h ι (toC x) ≠ 0 := by
    rw [jacValC_eq_det]
    exact hd
  have hJcont : ContinuousAt (jacValC c h ι) (toC x) :=
    (Work.WilE3.API.eaEvalC_fderiv_analytic c (jacDet c h ι) (toC x)).1.continuousAt
  have hφ : Filter.Tendsto (fun t : ℂ =>
      (uCoord k ι (toC x) + t • (fun i => (w i : ℂ)), (0 : Fin j → ℂ)))
      (nhds (0 : ℂ)) (nhds (uCoord k ι (toC x), (0 : Fin j → ℂ))) := by
    have h1 : Continuous fun t : ℂ => uCoord k ι (toC x) + t • (fun i => (w i : ℂ)) := by
      fun_prop
    have h2 : Continuous fun _ : ℂ => (0 : Fin j → ℂ) := continuous_const
    have := (h1.prodMk h2).tendsto (0 : ℂ)
    simpa using this
  have hΨtend : Filter.Tendsto Ψ (nhds (uCoord k ι (toC x), (0 : Fin j → ℂ)))
      (nhds (toC x)) := by
    have h := hΨ.2.1.continuousAt.tendsto
    rwa [hΨ.1] at h
  have hcont : Filter.Tendsto (fun t : ℂ => jacValC c h ι
      (Ψ (uCoord k ι (toC x) + t • (fun i => (w i : ℂ)), (0 : Fin j → ℂ))))
      (nhds (0 : ℂ)) (nhds (jacValC c h ι (toC x))) :=
    hJcont.tendsto.comp (hΨtend.comp hφ)
  have hevJ : ∀ᶠ t in nhds (0 : ℂ), jacValC c h ι
      (Ψ (uCoord k ι (toC x) + t • (fun i => (w i : ℂ)), (0 : Fin j → ℂ))) ≠ 0 :=
    hcont.eventually (isOpen_ne.mem_nhds hd')
  refine (hevJ.and (deriv_curve_eval_aux c h ι f x Ψ hΨ hd w)).mono ?_
  rintro t ⟨hΔ, hGt⟩ ht
  exact det_ne_zero_of_rows c h ι f x hjk hι w hw μ hμ _
    hΔ (by rw [← hGt]; exact ht)

end

end Work.WilE3.Frame
