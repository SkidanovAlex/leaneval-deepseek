import Mathlib

/-!
# Swapping the mixed partial derivatives of a `C²` function on `P × ℝ`

Let `Φ : P × ℝ → E` be `C²` at `(p, t)`.  This file proves that the two iterated
partial derivatives of `Φ` — first differentiating in the `P`-variable and then in
the `ℝ`-variable, or the other way round — agree:

`deriv (fun s => fderiv ℝ (fun q => Φ (q, s)) p v) t
   = fderiv ℝ (fun q => deriv (fun s => Φ (q, s)) t) p v`.

This is Schwarz's theorem (`ContDiffAt.isSymmSndFDerivAt`) transported to the
"fiber" formulation in which the two derivatives are taken with respect to the two
factors separately.  The bridge is the chain rule: differentiating the section
`s ↦ (p, s)` (resp. `q ↦ (q, t)`) inserts the canonical inclusion `inr` (resp.
`inl`), and evaluating a continuous linear map at a point is itself linear.  So both
sides are the evaluation of the second Fréchet derivative `fderiv ℝ (fderiv ℝ Φ)`
on the pair of direction vectors `(0, 1)` and `(v, 0)`, in one order or the other.
-/

open scoped ContDiff Topology
open Filter

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- First chain-rule reduction.  Evaluating the `P`-derivative of `Φ` at `p` on the
direction `v` equals evaluating the full Fréchet derivative of `Φ` at `(p, s)` on the
direction `(v, 0)`. -/
lemma fderiv_fst_fiber {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : P × ℝ → E} {p : P} {s : ℝ} {v : P}
    (h : HasFDerivAt Φ (fderiv ℝ Φ (p,s)) (p,s)) :
    fderiv ℝ (fun q => Φ (q,s)) p v = fderiv ℝ Φ (p,s) (v, 0) := by
  have h1 : HasFDerivAt (fun q : P => (q, s)) (ContinuousLinearMap.inl ℝ P ℝ) p :=
    hasFDerivAt_prodMk_left p s
  have h2 : HasFDerivAt (fun q => Φ (q,s))
      ((fderiv ℝ Φ (p,s)).comp (ContinuousLinearMap.inl ℝ P ℝ)) p := by
    simpa [Function.comp_def] using h.comp p h1
  rw [h2.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]

/-- Second chain-rule reduction.  The partial derivative in the `ℝ`-variable of `Φ` at
`(q, t)` equals evaluating the full Fréchet derivative of `Φ` at `(q, t)` on the
direction `(0, 1)`. -/
lemma deriv_snd_fiber {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Φ : P × ℝ → E} {q : P} {t : ℝ}
    (h : HasFDerivAt Φ (fderiv ℝ Φ (q,t)) (q,t)) :
    deriv (fun s => Φ (q,s)) t = fderiv ℝ Φ (q,t) (0,1) := by
  have h1 : HasFDerivAt (fun s : ℝ => (q, s)) (ContinuousLinearMap.inr ℝ P ℝ) t :=
    hasFDerivAt_prodMk_right q t
  have h2 : HasFDerivAt (fun s => Φ (q,s))
      ((fderiv ℝ Φ (q,t)).comp (ContinuousLinearMap.inr ℝ P ℝ)) t := by
    simpa [Function.comp_def] using h.comp t h1
  rw [h2.hasDerivAt.deriv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]

/-- Differentiating along the second factor a family of continuous linear maps `F` and
then evaluating on `w` gives the second derivative applied to `(0, 1)` and then `w`. -/
lemma deriv_prodMk_right_apply {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : P × ℝ → (P × ℝ) →L[ℝ] E}
    {T : (P × ℝ) →L[ℝ] ((P × ℝ) →L[ℝ] E)} {p : P} {t : ℝ}
    (hF : HasFDerivAt F T (p,t)) (w : P × ℝ) :
    deriv (fun s => F (p,s) w) t = T (0,1) w := by
  have happly : HasFDerivAt (fun x => F x w)
      ((ContinuousLinearMap.apply ℝ E w).comp T) (p,t) :=
    (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ E w)).comp (p,t) hF
  have h1 : HasFDerivAt (fun s : ℝ => (p, s)) (ContinuousLinearMap.inr ℝ P ℝ) t :=
    hasFDerivAt_prodMk_right p t
  have h2 : HasFDerivAt (fun s => F (p,s) w)
      (((ContinuousLinearMap.apply ℝ E w).comp T).comp (ContinuousLinearMap.inr ℝ P ℝ)) t := by
    simpa [Function.comp_def] using happly.comp t h1
  rw [h2.hasDerivAt.deriv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.inr_apply]

/-- Differentiating along the first factor a family of continuous linear maps `F` and
then evaluating on `w`: the Fréchet derivative at `p` in direction `v` gives the second
derivative applied to `(v, 0)` and then `w`. -/
lemma fderiv_prodMk_left_apply {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : P × ℝ → (P × ℝ) →L[ℝ] E}
    {T : (P × ℝ) →L[ℝ] ((P × ℝ) →L[ℝ] E)} {p : P} {t : ℝ}
    (hF : HasFDerivAt F T (p,t)) (w : P × ℝ) (v : P) :
    fderiv ℝ (fun q => F (q,t) w) p v = T (v,0) w := by
  have happly : HasFDerivAt (fun x => F x w)
      ((ContinuousLinearMap.apply ℝ E w).comp T) (p,t) :=
    (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.apply ℝ E w)).comp (p,t) hF
  have h1 : HasFDerivAt (fun q : P => (q, t)) (ContinuousLinearMap.inl ℝ P ℝ) p :=
    hasFDerivAt_prodMk_left p t
  have h2 : HasFDerivAt (fun q => F (q,t) w)
      (((ContinuousLinearMap.apply ℝ E w).comp T).comp (ContinuousLinearMap.inl ℝ P ℝ)) p := by
    simpa [Function.comp_def] using happly.comp p h1
  rw [h2.fderiv]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.inl_apply]

/-- **Schwarz's theorem for the mixed partial derivatives on `P × ℝ`.**  For a function
`Φ : P × ℝ → E` which is `C²` at `(p, t)`, differentiating in the `P`-variable and then
in the `ℝ`-variable commutes with differentiating in the `ℝ`-variable and then in the
`P`-variable. -/
theorem mixedPartialFiberSwap {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : P × ℝ → E) (p : P) (t : ℝ) (v : P)
    (hΦ : ContDiffAt ℝ (2 : WithTop ℕ∞) Φ (p, t)) :
    deriv (fun s => fderiv ℝ (fun q => Φ (q, s)) p v) t
      = fderiv ℝ (fun q => deriv (fun s => Φ (q, s)) t) p v := by
  -- `F` is the first derivative of `Φ`, a `C¹` map on `P × ℝ`; both sides will be shown to
  -- equal evaluations of its derivative `fderiv ℝ F (p,t)`.
  let F : P × ℝ → (P × ℝ) →L[ℝ] E := fderiv ℝ Φ
  have hFcd : ContDiffAt ℝ 1 F (p,t) := by
    have := hΦ.fderiv_right (m := 1) (by norm_num)
    simpa [F] using this
  have hF : HasFDerivAt F (fderiv ℝ F (p,t)) (p,t) :=
    (hFcd.differentiableAt (by norm_num)).hasFDerivAt
  have hEvΦ : ∀ᶠ y in 𝓝 (p,t), ContDiffAt ℝ 2 Φ y := hΦ.eventually (by norm_num)
  -- Left-hand side: `deriv` of `s ↦ fderiv ℝ (fun q => Φ (q,s)) p v` at `t`.
  have hL : deriv (fun s => fderiv ℝ (fun q => Φ (q,s)) p v) t
      = fderiv ℝ F (p,t) (0,1) (v,0) := by
    have htend : Tendsto (fun s : ℝ => (p,s)) (𝓝 t) (𝓝 (p,t)) :=
      ((continuous_const : Continuous fun _ : ℝ => p).prodMk continuous_id).tendsto t
    have hEv : ∀ᶠ s in 𝓝 t, ContDiffAt ℝ 2 Φ (p,s) := htend.eventually hEvΦ
    have heq : (fun s => fderiv ℝ (fun q => Φ (q,s)) p v) =ᶠ[𝓝 t]
        (fun s => F (p,s) (v,0)) := by
      filter_upwards [hEv] with s hs
      have hd : HasFDerivAt Φ (fderiv ℝ Φ (p,s)) (p,s) :=
        (hs.differentiableAt (by norm_num)).hasFDerivAt
      simpa [F] using fderiv_fst_fiber hd
    rw [heq.deriv_eq]
    exact deriv_prodMk_right_apply hF (v,0)
  -- Right-hand side: `fderiv` at `p` of `q ↦ deriv (fun s => Φ (q,s)) t`, on `v`.
  have hR : fderiv ℝ (fun q => deriv (fun s => Φ (q,s)) t) p v
      = fderiv ℝ F (p,t) (v,0) (0,1) := by
    have htend : Tendsto (fun q : P => (q,t)) (𝓝 p) (𝓝 (p,t)) :=
      (continuous_id.prodMk (continuous_const : Continuous fun _ : P => t)).tendsto p
    have hEv : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 2 Φ (q,t) := htend.eventually hEvΦ
    have heq : (fun q => deriv (fun s => Φ (q,s)) t) =ᶠ[𝓝 p]
        (fun q => F (q,t) (0,1)) := by
      filter_upwards [hEv] with q hq
      have hd : HasFDerivAt Φ (fderiv ℝ Φ (q,t)) (q,t) :=
        (hq.differentiableAt (by norm_num)).hasFDerivAt
      simpa [F] using deriv_snd_fiber hd
    rw [heq.fderiv_eq]
    exact fderiv_prodMk_left_apply hF (0,1) v
  -- Both sides are evaluations of the symmetric second derivative, in opposite orders.
  rw [hL, hR]
  exact (hΦ.isSymmSndFDerivAt (by norm_num)).eq (0,1) (v,0)

end Work.RPB.B5
