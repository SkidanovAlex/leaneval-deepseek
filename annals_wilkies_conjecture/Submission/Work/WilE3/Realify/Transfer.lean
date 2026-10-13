/-
  annals_wilkies_conjecture, AREA E3, `Realify` (the Jacobian transfer).

  The realified system's Jacobian at a point is `Wval^N` times the (realified) complex Jacobian:
  the realified equation is `Wval^N` times the real part of the complexified one, the clearing
  factor is nonzero, and at a common zero the derivative of the clearing factor drops out.  Hence
  nondegenerate complex zeros realify to nondegenerate real zeros, and Khovanskii's bound (which
  counts nondegenerate zeros) applies.
-/
import Submission.Work.WilE3.Realify.EvalID
import Submission.Work.WilE3.Realify.SepChainLocal_fderiv_ev

namespace Work.WilE3.Realify

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open WilkiesDesign.E

variable {k r : ℕ}

theorem uOf_mkPt (u v : Fin k → ℝ) : uOf (mkPt u v) = u := by
  funext i
  simp only [uOf, mkPt_apply_castAdd]

theorem vOf_mkPt (u v : Fin k → ℝ) : vOf (mkPt u v) = v := by
  funext i
  simp only [vOf, mkPt_apply_natAdd]

/-- The chart neighbourhood: the half-angle arguments stay away from the poles. -/
theorem eventually_chart (c : EAChain k r) (cc : Fin r → ℝ) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0) :
    ∀ᶠ w in 𝓝 (mkPt u v),
      ∀ j, Real.cos ((∑ i, c.a j i * (vOf w) i - cc j) / 2) ≠ 0 := by
  have hcont : ∀ j : Fin r, Continuous (fun w : Fin (k + k) → ℝ =>
      Real.cos ((∑ i, c.a j i * (vOf w) i - cc j) / 2)) := by
    intro j
    unfold vOf
    continuity
  have h1 : ∀ j : Fin r, ∀ᶠ w in 𝓝 (mkPt u v),
      Real.cos ((∑ i, c.a j i * (vOf w) i - cc j) / 2) ≠ 0 := by
    intro j
    have harg : (∑ i, c.a j i * (vOf (mkPt u v)) i - cc j) / 2
        = (∑ i, c.a j i * v i - cc j) / 2 := by
      rw [vOf_mkPt]
    exact (hcont j).continuousAt.eventually_ne (by rw [harg]; exact hcos j)
  exact Filter.eventually_all.mpr h1

/-- The realified function is `Wval^N` times the real part of the complexified one near the
point. -/
theorem eventuallyEq_ev_realifyRe (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (P : EAPoly k r) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0)
    (hN : P.totalDegree ≤ N) :
    (fun w => (mkChain c cc).ev (realifyRe N e P) w)
      =ᶠ[𝓝 (mkPt u v)]
        (fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w) * fun w => (evalUV c P w).re := by
  filter_upwards [eventually_chart c cc u v hcos] with w hw
  change (mkChain c cc).ev (realifyRe N e P) w
      = (mkChain c cc).ev (WPow (k := k) (r := r) N) w * (evalUV c P w).re
  rw [mkChain_ev_of, ev_WPow, eval_realifyRe c cc e he N P (uOf w) (vOf w) hw hN,
    zOf_mkPt_uOf_vOf]
  rfl

theorem eventuallyEq_ev_realifyIm (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (P : EAPoly k r) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0)
    (hN : P.totalDegree ≤ N) :
    (fun w => (mkChain c cc).ev (realifyIm N e P) w)
      =ᶠ[𝓝 (mkPt u v)]
        (fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w) * fun w => (evalUV c P w).im := by
  filter_upwards [eventually_chart c cc u v hcos] with w hw
  change (mkChain c cc).ev (realifyIm N e P) w
      = (mkChain c cc).ev (WPow (k := k) (r := r) N) w * (evalUV c P w).im
  rw [mkChain_ev_of, ev_WPow, eval_realifyIm c cc e he N P (uOf w) (vOf w) hw hN,
    zOf_mkPt_uOf_vOf]
  rfl

/-- The chain-rule hypothesis of `SepChainLocal_fderiv_ev` at the point `mkPt u v`. -/
theorem mkChain_hx (c : EAChain k r) (cc : Fin r → ℝ) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0) :
    ∀ j, (∑ i, (mkChain c cc).a j i * mkPt u v i) + (mkChain c cc).b j ∈ (mkChain c cc).dom j := by
  intro j
  revert j
  refine Fin.addCases (motive := fun j => (∑ i, (mkChain c cc).a j i * mkPt u v i)
      + (mkChain c cc).b j ∈ (mkChain c cc).dom j) ?_ ?_
  · intro j
    exact mkChain_hx_castAdd c cc u v j
  · intro j
    exact mkChain_hx_natAdd c cc u v j (hcos j)

/-- The gradient evaluated on a basis vector is the corresponding symbolic derivative. -/
theorem grad_single {n r : ℕ} (S : SepChainLocal n r) (Q : EAPoly n r) (x : Fin n → ℝ)
    (l : Fin n) : grad S Q x (Pi.single l 1) = S.ev (S.d l Q) x := by
  rw [grad_apply]
  rw [Finset.sum_eq_single l]
  · rw [Pi.single_eq_same, mul_one]
  · intro b _ hb
    have hz : (Pi.single l (1 : ℝ) : Fin n → ℝ) b = 0 := by
      simp [Pi.single_apply, hb]
    rw [hz, mul_zero]
  · intro h; exact absurd (Finset.mem_univ l) h

/-- **The Jacobian entry of the realified system (real equations).** -/
theorem ev_d_realifyRe (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (P : EAPoly k r) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0)
    (hN : P.totalDegree ≤ N)
    (hzero : eaEvalC c P (zOf (mkPt u v)) = 0)
    (hdiff : DifferentiableAt ℝ (fun w => (evalUV c P w).re) (mkPt u v))
    (l : Fin (k + k)) :
    (mkChain c cc).ev ((mkChain c cc).d l (realifyRe N e P)) (mkPt u v)
      = Wval c cc v ^ N
        * fderiv ℝ (fun w => (evalUV c P w).re) (mkPt u v) (Pi.single l 1) := by
  have hU : DifferentiableAt ℝ
      (fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w) (mkPt u v) :=
    (SepChainLocal_fderiv_ev (mkChain c cc) (WPow (k := k) (r := r) N) (mkPt u v)
      (mkChain_hx c cc u v hcos)).differentiableAt
  have hmul : fderiv ℝ ((fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w)
        * (fun w => (evalUV c P w).re)) (mkPt u v)
      = (mkChain c cc).ev (WPow (k := k) (r := r) N) (mkPt u v)
          • fderiv ℝ (fun w => (evalUV c P w).re) (mkPt u v)
        + (evalUV c P (mkPt u v)).re
          • fderiv ℝ (fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w) (mkPt u v) :=
    fderiv_mul hU hdiff
  have hval : (mkChain c cc).ev (WPow (k := k) (r := r) N) (mkPt u v) = Wval c cc v ^ N := by
    rw [ev_WPow, vOf_mkPt]
  have hV0 : (evalUV c P (mkPt u v)).re = 0 := by
    rw [evalUV, hzero]
    rfl
  have hderiv : fderiv ℝ (fun w => (mkChain c cc).ev (realifyRe N e P) w) (mkPt u v)
      = Wval c cc v ^ N • fderiv ℝ (fun w => (evalUV c P w).re) (mkPt u v) := by
    rw [(eventuallyEq_ev_realifyRe c cc e he N P u v hcos hN).fderiv_eq, hmul, hval, hV0,
      zero_smul, add_zero]
  have hcr := SepChainLocal_fderiv_ev (mkChain c cc) (realifyRe N e P) (mkPt u v)
    (mkChain_hx c cc u v hcos)
  calc (mkChain c cc).ev ((mkChain c cc).d l (realifyRe N e P)) (mkPt u v)
      = (grad (mkChain c cc) (realifyRe N e P) (mkPt u v)) (Pi.single l 1) :=
        (grad_single (mkChain c cc) (realifyRe N e P) (mkPt u v) l).symm
    _ = fderiv ℝ (fun w => (mkChain c cc).ev (realifyRe N e P) w) (mkPt u v)
          (Pi.single l 1) := by rw [hcr.fderiv]
    _ = (Wval c cc v ^ N • fderiv ℝ (fun w => (evalUV c P w).re) (mkPt u v))
          (Pi.single l 1) := by rw [hderiv]
    _ = Wval c cc v ^ N
          * fderiv ℝ (fun w => (evalUV c P w).re) (mkPt u v) (Pi.single l 1) := by
        rw [ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- **The Jacobian entry of the realified system (imaginary equations).** -/
theorem ev_d_realifyIm (c : EAChain k r) (cc e : Fin r → ℝ)
    (he : ∀ j, (e j : ℂ) = Complex.exp ((cc j : ℂ) * Complex.I))
    (N : ℕ) (P : EAPoly k r) (u v : Fin k → ℝ)
    (hcos : ∀ j, Real.cos ((∑ i, c.a j i * v i - cc j) / 2) ≠ 0)
    (hN : P.totalDegree ≤ N)
    (hzero : eaEvalC c P (zOf (mkPt u v)) = 0)
    (hdiff : DifferentiableAt ℝ (fun w => (evalUV c P w).im) (mkPt u v))
    (l : Fin (k + k)) :
    (mkChain c cc).ev ((mkChain c cc).d l (realifyIm N e P)) (mkPt u v)
      = Wval c cc v ^ N
        * fderiv ℝ (fun w => (evalUV c P w).im) (mkPt u v) (Pi.single l 1) := by
  have hU : DifferentiableAt ℝ
      (fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w) (mkPt u v) :=
    (SepChainLocal_fderiv_ev (mkChain c cc) (WPow (k := k) (r := r) N) (mkPt u v)
      (mkChain_hx c cc u v hcos)).differentiableAt
  have hmul : fderiv ℝ ((fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w)
        * (fun w => (evalUV c P w).im)) (mkPt u v)
      = (mkChain c cc).ev (WPow (k := k) (r := r) N) (mkPt u v)
          • fderiv ℝ (fun w => (evalUV c P w).im) (mkPt u v)
        + (evalUV c P (mkPt u v)).im
          • fderiv ℝ (fun w => (mkChain c cc).ev (WPow (k := k) (r := r) N) w) (mkPt u v) :=
    fderiv_mul hU hdiff
  have hval : (mkChain c cc).ev (WPow (k := k) (r := r) N) (mkPt u v) = Wval c cc v ^ N := by
    rw [ev_WPow, vOf_mkPt]
  have hV0 : (evalUV c P (mkPt u v)).im = 0 := by
    rw [evalUV, hzero]
    rfl
  have hderiv : fderiv ℝ (fun w => (mkChain c cc).ev (realifyIm N e P) w) (mkPt u v)
      = Wval c cc v ^ N • fderiv ℝ (fun w => (evalUV c P w).im) (mkPt u v) := by
    rw [(eventuallyEq_ev_realifyIm c cc e he N P u v hcos hN).fderiv_eq, hmul, hval, hV0,
      zero_smul, add_zero]
  have hcr := SepChainLocal_fderiv_ev (mkChain c cc) (realifyIm N e P) (mkPt u v)
    (mkChain_hx c cc u v hcos)
  calc (mkChain c cc).ev ((mkChain c cc).d l (realifyIm N e P)) (mkPt u v)
      = (grad (mkChain c cc) (realifyIm N e P) (mkPt u v)) (Pi.single l 1) :=
        (grad_single (mkChain c cc) (realifyIm N e P) (mkPt u v) l).symm
    _ = fderiv ℝ (fun w => (mkChain c cc).ev (realifyIm N e P) w) (mkPt u v)
          (Pi.single l 1) := by rw [hcr.fderiv]
    _ = (Wval c cc v ^ N • fderiv ℝ (fun w => (evalUV c P w).im) (mkPt u v))
          (Pi.single l 1) := by rw [hderiv]
    _ = Wval c cc v ^ N
          * fderiv ℝ (fun w => (evalUV c P w).im) (mkPt u v) (Pi.single l 1) := by
        rw [ContinuousLinearMap.smul_apply, smul_eq_mul]

end

end Work.WilE3.Realify
