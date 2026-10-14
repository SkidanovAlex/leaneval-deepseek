import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.Galerkin.Inhabit.regPkg_zero
import Submission.Work.FTS.PhiStar.Gegenbauer.FamNormValue
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.StrongPersist.H6Rows.NZaux.L12AddFstar
import Submission.Work.FTS_EllLimOK.Decay.DecayTools
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.ZcutSmoothCompact

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `cmode_decay_of_cptQ` — rapid decay of the mode coefficients of a source compactly
supported in the open quadrant

For a source `G` which is `C^∞` on `ℝ²` and whose support is a compact subset of the *open*
quadrant `(0,∞) × (0,π/2)`, and for every `j, N`, the mode coefficients of `D_z^j G` decay
faster than `(m+1)^{-N}`, *uniformly in the radial variable*:

  `∃ C ≥ 0, ∀ m ≥ 1, ∀ t, |cmode m (D_z^j G) t| ≤ C / (m+1)^N`.

## Route

Fix the support box `[a,b] × [c,d] ⊂ (0,∞) × (0,π/2)` and put `F = D_z^j G`.  Then `F` is
`C^∞` and supported in the box.

* `Lzero1` (`-u'' + (tan θ·u)' - 6u`) is the angular operator whose Dirichlet eigenfunctions
  are `eFam m` with eigenvalues `lam m = 2m(2m+5)`; it is self-adjoint for the weight
  `cos θ dθ`, so for a smooth `u` supported inside `(0,π/2)` the moment of `u` equals
  `(lam m)^{-k}` times the moment of its `k`-th iterate (`ClassCHon.cmode_iter`), the iterates
  of a slice staying smooth and supported in the box (`ClassCHon.Lop_good`).
* Each moment is then bounded by `3(m+1)M`, where `M` bounds the `(N+1)`-st iterate of the
  slice: `|eFam m| ≤ 3(m+1)` and `∫_0^{π/2} cos = 1` (`cmode_le_of_bound_end`).
* The uniformity in `t` is the only real content: the **joint** iterates
  `Φ_k(t,θ) = (Lzero1^k (F t ·))(θ)` are `C^∞` on the open quadrant, because the curried form
  `Lzero1 u θ = -u''(θ) + (1/cos²θ)·u(θ) + tan θ·u'(θ) - 6u(θ)` expresses `Lzero1` through the
  partial derivatives of the two-variable function; compactness of the box then bounds all of
  them by a single `M`.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-! ## 1. Finite-order smoothness of the curried partial derivatives -/

/-- **Curried partials of a `C^{n+1}` function on an open set are `C^n`.**  The finite-order
version of `Work.Spaces.contDiffOn_uncurry_pz` / `contDiffOn_uncurry_pth`: the partial
derivatives are the Fréchet derivative evaluated at the constant directions `(1,0)` resp.
`(0,1)`, and `fderivWithin = fderiv` on the open set.  The multipliers `z` (`Dz`) and
`sin(2θ)` (`Dth`) are smooth, so no order is lost for them. -/
theorem currySmooth_fin_end {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (n : ℕ)
    (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V ∧
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V ∧
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G)) V ∧
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hdiff : DifferentiableOn ℝ (Function.uncurry G) V :=
    h.differentiableOn (n := (n + 1 : ℕ)) (by simp)
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := (n : ℕ)) hV.uniqueDiffOn (by simp)
    refine h'.congr ?_
    intro p hp
    rw [fderivWithin_of_isOpen hV hp]
  have hpz : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
    have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
        = fderiv ℝ (Function.uncurry G) p (1, 0) := by
      intro p hp
      exact Work.Spaces.pz_eq_fderiv (hdiff.differentiableAt (hV.mem_nhds hp))
    have hcomp : ContDiffOn ℝ n
        (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
      simpa using hfd.clm_apply (contDiffOn_const (c := ((1, 0) : ℝ × ℝ)))
    exact hcomp.congr hchain
  have hpth : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
    have hchain : ∀ p ∈ V, Work.Spaces.pth G p.1 p.2
        = fderiv ℝ (Function.uncurry G) p (0, 1) := by
      intro p hp
      exact Work.Spaces.pth_eq_fderiv (hdiff.differentiableAt (hV.mem_nhds hp))
    have hcomp : ContDiffOn ℝ n
        (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
      simpa using hfd.clm_apply (contDiffOn_const (c := ((0, 1) : ℝ × ℝ)))
    exact hcomp.congr hchain
  refine ⟨hpz, hpth, ?_, ?_⟩
  · have hz : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1) V := contDiffOn_fst
    have hDz : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p) V :=
      hz.mul hpz
    exact hDz.congr (fun p _ => rfl)
  · have hs : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V := by
      have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => (2 : ℝ) * p.2) V :=
        (contDiffOn_const (c := (2 : ℝ))).mul contDiffOn_snd
      simpa using h2.sin
    have hDth : ContDiffOn ℝ n
        (fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth G) p) V :=
      hs.mul hpth
    exact hDth.congr (fun p _ => rfl)

/-- **Iterated `θ`-partials of a `C^{n+i}` function are `C^n`.** -/
theorem pthIter_contDiffOn_le {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (i n : ℕ)
    (h : ContDiffOn ℝ (n + i) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter i G)) V := by
  induction i generalizing n with
  | zero => simpa using h
  | succ i ih =>
      have h' : ContDiffOn ℝ ((↑(n + 1) : WithTop ℕ∞) + ↑i) (Function.uncurry G) V := by
        have he : ((↑(n + 1) : WithTop ℕ∞) + ↑i)
            = ((↑n : WithTop ℕ∞) + ↑(i + 1)) := by
          push_cast
          ring
        rw [he]
        exact h
      have hstep : ContDiffOn ℝ n
          (Function.uncurry (Work.Spaces.pth (Work.Spaces.pthIter i G))) V :=
        (currySmooth_fin_end hV (n := n) (G := Work.Spaces.pthIter i G) (ih (n + 1) h')).2.1
      simpa [Work.Spaces.pthIter_succ] using hstep

/-- **`D_z^j` of a globally smooth function is globally smooth.** -/
theorem DzIter_contDiff_of_forall_end {G : ℝ → ℝ → ℝ}
    (hG : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry G)) (j : ℕ) :
    ∀ n : ℕ, ContDiff ℝ n (Function.uncurry (Work.Spaces.DzIter j G)) := by
  intro n
  induction j generalizing n with
  | zero => simpa using hG n
  | succ j ih =>
      have h1 : ContDiffOn ℝ (n + 1) (Function.uncurry (Work.Spaces.DzIter j G)) Set.univ :=
        contDiffOn_univ.mpr (ih (n + 1))
      have h2 := (currySmooth_fin_end isOpen_univ (n := n) h1).2.2.1
      rw [show Work.Spaces.Dz (Work.Spaces.DzIter j G) = Work.Spaces.DzIter (j + 1) G from
        (Work.Spaces.DzIter_succ j G).symm] at h2
      exact contDiffOn_univ.mp h2

/-! ## 2. The curried form of `Lzero1` -/

/-- **`Lzero1` in curried form.**  At an interior point where `cos θ ≠ 0` and `u` is
differentiable,

  `Lzero1 u θ = -u''(θ) + (1/cos²θ)·u(θ) + tan θ·u'(θ) - 6u(θ)`.

This is `Work.FTS.ClassC.HonestCut.Lzero1_apply'` with the interval `(0,1)` replaced by a
neighbourhood of the evaluation point. -/
theorem Lzero1_eq_form_end {u : ℝ → ℝ} {θ : ℝ} (hcos : Real.cos θ ≠ 0)
    (h : HasDerivAt u (deriv u θ) θ) :
    Work.FTS.EllipticEst.Lzero1 u θ
      = -(deriv (fun t : ℝ => deriv u t) θ) + (1 / Real.cos θ ^ 2) * u θ
        + Real.tan θ * deriv u θ - 6 * u θ := by
  have h2 : HasDerivAt Real.tan (1 / Real.cos θ ^ 2) θ := Real.hasDerivAt_tan hcos
  have h3 : deriv (fun t : ℝ => Real.tan t * u t) θ
      = (1 / Real.cos θ ^ 2) * u θ + Real.tan θ * deriv u θ := (h2.mul h).deriv
  show -(deriv (fun t : ℝ => deriv u t) θ) + deriv (fun t : ℝ => Real.tan t * u t) θ
      - 6 * u θ = _
  rw [h3]
  ring

/-! ## 3. The joint iterates of `Lzero1` and their smoothness -/

/-- One step of the *curried* action of `Lzero1` on a two-variable function: the function
`(t,θ) ↦ (Lzero1 (F t ·))(θ)`, computed through partial derivatives. -/
noncomputable def phiStep (v : ℝ → ℝ → ℝ) : ℝ → ℝ → ℝ :=
  fun t θ => -(Work.Spaces.pthIter 2 v t θ) + (1 / Real.cos θ ^ 2) * v t θ
    + Real.tan θ * Work.Spaces.pthIter 1 v t θ - 6 * v t θ

/-- The `k`-th joint iterate of `Lzero1` applied to the slices of `F`. -/
noncomputable def phi (F : ℝ → ℝ → ℝ) (k : ℕ) : ℝ → ℝ → ℝ := (phiStep^[k]) F

theorem phi_succ (F : ℝ → ℝ → ℝ) (k : ℕ) :
    phi F (k + 1) = phiStep (phi F k) := Function.iterate_succ_apply' phiStep k F

/-- **Joint smoothness of the iterates.**  If `F` is `C^n` on the open set `V` for every `n`
and `cos` does not vanish on the `θ`-coordinates of `V`, then so is every joint iterate of
`Lzero1` applied to the slices of `F`. -/
theorem phi_contDiffOn {F : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hcos : ∀ p ∈ V, Real.cos p.2 ≠ 0)
    (hF : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) V) :
    ∀ k n : ℕ, ContDiffOn ℝ n (Function.uncurry (phi F k)) V := by
  intro k
  induction k with
  | zero => intro n; simpa [phi] using hF n
  | succ k ih =>
      intro n
      have hstep := phi_succ F k
      have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => phi F k p.1 p.2) V :=
        (ih n).congr (fun p _ => rfl)
      have h2 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.pthIter 1 (phi F k) p.1 p.2) V :=
        (pthIter_contDiffOn_le hV 1 n (by simpa using ih (n + 1))).congr (fun p _ => rfl)
      have h3 : ContDiffOn ℝ n (fun p : ℝ × ℝ => Work.Spaces.pthIter 2 (phi F k) p.1 p.2) V :=
        (pthIter_contDiffOn_le hV 2 n (by simpa using ih (n + 2))).congr (fun p _ => rfl)
      have htan : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.tan p.2) V := by
        have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2) V := contDiffOn_snd.sin
        have hcos' : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.cos p.2) V := contDiffOn_snd.cos
        have hdiv : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin p.2 / Real.cos p.2) V :=
          (hsin.div hcos' (fun p hp => hcos p hp)).congr (fun p _ => rfl)
        simpa only [Real.tan_eq_sin_div_cos] using hdiv
      have hone : ContDiffOn ℝ n (fun p : ℝ × ℝ => 1 / Real.cos p.2 ^ 2) V := by
        have hc : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.cos p.2 ^ 2) V := contDiffOn_snd.cos.pow 2
        have hdiv : ContDiffOn ℝ n
            ((fun _ : ℝ × ℝ => (1 : ℝ)) / fun p => Real.cos p.2 ^ 2) V :=
          (contDiffOn_const (c := (1 : ℝ))).div hc (fun p hp => pow_ne_zero 2 (hcos p hp))
        exact hdiv.congr (fun p _ => rfl)
      have hbody : ContDiffOn ℝ n (fun p : ℝ × ℝ =>
          -(Work.Spaces.pthIter 2 (phi F k) p.1 p.2)
            + (1 / Real.cos p.2 ^ 2) * phi F k p.1 p.2
            + Real.tan p.2 * Work.Spaces.pthIter 1 (phi F k) p.1 p.2
            - 6 * phi F k p.1 p.2) V :=
        (((h3.neg.add (hone.mul h1)).add (htan.mul h2)).sub (contDiffOn_const.mul h1))
      rw [hstep]
      refine hbody.congr (fun p _ => ?_)
      rfl

/-! ## 4. The joint iterates agree with the iterates of the slices -/

/-- **The joint iterate is the iterate of the slice.**  This is the pointwise form of the
identity `Lzero1 (F t ·) θ = phiStep F t θ` together with the recursion defining `Lop`. -/
theorem phi_eq_Lop {F : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hcos : ∀ p ∈ V, Real.cos p.2 ≠ 0)
    (hphi : ∀ k n : ℕ, ContDiffOn ℝ n (Function.uncurry (phi F k)) V) :
    ∀ k t θ, (t, θ) ∈ V →
      phi F k t θ = Work.FTS.ClassCHon.Lop (fun θ' => F t θ') k θ := by
  intro k
  induction k with
  | zero => intro t θ _; rfl
  | succ k ih =>
      intro t θ htθ
      have hstep := phi_succ F k
      have hd : DifferentiableAt ℝ (Function.uncurry (phi F k)) (t, θ) :=
        ((hphi k 1).differentiableOn (by norm_num)).differentiableAt (hV.mem_nhds htθ)
      have hsl : HasDerivAt (fun θ' => phi F k t θ') (deriv (fun θ' => phi F k t θ') θ) θ :=
        (Work.Spaces.differentiableAt_curry_right hd).hasDerivAt
      have hcosθ : Real.cos θ ≠ 0 := hcos (t, θ) htθ
      have hsec : {θ' : ℝ | (t, θ') ∈ V} ∈ 𝓝 θ :=
        (continuous_const.prodMk continuous_id).continuousAt (hV.mem_nhds htθ)
      have hev : (fun θ' => phi F k t θ') =ᶠ[𝓝 θ]
          (fun θ' => Work.FTS.ClassCHon.Lop (fun θ'' => F t θ'') k θ') := by
        filter_upwards [hsec] with θ' hθ'
        exact ih t θ' hθ'
      calc phi F (k + 1) t θ
          = -(deriv (fun s : ℝ => deriv (fun θ' => phi F k t θ') s) θ)
              + (1 / Real.cos θ ^ 2) * phi F k t θ
              + Real.tan θ * deriv (fun θ' => phi F k t θ') θ - 6 * phi F k t θ := by
            rw [hstep]
            simp only [phiStep, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
        _ = Work.FTS.EllipticEst.Lzero1 (fun θ' => phi F k t θ') θ :=
            (Lzero1_eq_form_end hcosθ hsl).symm
        _ = Work.FTS.EllipticEst.Lzero1
              (fun θ' => Work.FTS.ClassCHon.Lop (fun θ'' => F t θ'') k θ') θ := by
            rw [Lzero1_congr_of_eventuallyEq hev]
        _ = Work.FTS.ClassCHon.Lop (fun θ'' => F t θ'') (k + 1) θ := by
            rw [Work.FTS.ClassCHon.Lop_succ]

/-! ## 5. Support of `D_z^j G` -/

/-- If every slice of `G` vanishes off `[c,d]`, then every slice of `D_z^j G` does. -/
theorem DzIter_eq_zero_of_theta_not_mem {G : ℝ → ℝ → ℝ} {c d : ℝ}
    (hG : ∀ z θ : ℝ, G z θ ≠ 0 → θ ∈ Set.Icc c d) (j : ℕ) {t θ : ℝ}
    (hθ : θ ∉ Set.Icc c d) : Work.Spaces.DzIter j G t θ = 0 := by
  refine Work.Stability.DzIter_eq_zero_of_vanishOn
    (V := Set.univ ×ˢ (Set.Icc c d)ᶜ) (isOpen_univ.prod isClosed_Icc.isOpen_compl) ?_ j t θ ?_
  · intro z θ' hzθ'
    by_contra hne
    exact hzθ'.2 (hG z θ' hne)
  · exact ⟨Set.mem_univ t, hθ⟩

/-- If every line `z ↦ G z θ` vanishes off `[a,b]`, then so does every line of `D_z^j G`. -/
theorem DzIter_eq_zero_of_z_not_mem {G : ℝ → ℝ → ℝ} {a b : ℝ}
    (hG : ∀ z θ : ℝ, G z θ ≠ 0 → z ∈ Set.Icc a b) (j : ℕ) {t θ : ℝ}
    (ht : t ∉ Set.Icc a b) : Work.Spaces.DzIter j G t θ = 0 := by
  refine Work.Stability.DzIter_eq_zero_of_vanishOn
    (V := (Set.Icc a b)ᶜ ×ˢ Set.univ) (isClosed_Icc.isOpen_compl.prod isOpen_univ) ?_ j t θ ?_
  · intro z θ' hzθ'
    by_contra hne
    exact hzθ'.1 (hG z θ' hne)
  · exact ⟨ht, Set.mem_univ θ⟩

/-- The `k`-th iterate of `Lzero1` of the zero function is zero. -/
theorem Lop_zero_fun (k : ℕ) :
    Work.FTS.ClassCHon.Lop (fun _ : ℝ => (0 : ℝ)) k = fun _ => 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [Work.FTS.ClassCHon.Lop_succ, ih]
      funext θ
      simp only [Work.FTS.EllipticEst.Lzero1]
      simp

/-! ## 6. The uniform moment bound and the mode decay -/

/-- **The uniform moment bound.**  If every slice of `F` is `C^∞` and supported in `[c,d]`, and
the `(N+1)`-st `Lzero1`-iterate of every slice is bounded by `M` on `[c,d]`, then
`|cmode m F t| ≤ 3M/(m+1)^N` for all `m ≥ 1` and all `t`. -/
theorem cmode_le_of_bound_end {F : ℝ → ℝ → ℝ} {c d M : ℝ} {N : ℕ}
    (hc : 0 < c) (hd : d < Real.pi / 2) (hM : 0 ≤ M)
    (hgood : ∀ t : ℝ, Work.FTS.ClassCHon.Good c d (fun θ => F t θ))
    (hbd : ∀ t θ : ℝ, θ ∈ Set.Icc c d →
      |Work.FTS.ClassCHon.Lop (fun θ => F t θ) (N + 1) θ| ≤ M) :
    ∀ m : ℕ, 1 ≤ m → ∀ t : ℝ,
      |Work.FTS.PhiStar.Series.cmode m F t| ≤ (3 * M) / ((m : ℝ) + 1) ^ N := by
  intro m hm t
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlampos : (0 : ℝ) < Work.FTS.PhiStar.Gegenbauer.lam m := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]; positivity
  have hLop : ∀ k : ℕ,
      Work.FTS.ClassCHon.Good c d (Work.FTS.ClassCHon.Lop (fun θ => F t θ) k) :=
    Work.FTS.ClassCHon.Lop_good hc hd (hgood t)
  have hiter := Work.FTS.ClassCHon.cmode_iter hc hd hLop hm (N + 1)
  have hcontg : Continuous (fun θ : ℝ =>
      Work.FTS.ClassCHon.Lop (fun θ => F t θ) (N + 1) θ) := (hLop (N + 1)).contDiff.continuous
  have hcontE : Continuous (fun θ : ℝ => Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
    Real.continuous_cos.mul
      (((Work.FTS.PhiStar.Gegenbauer.contDiff_gC (2 * m + 1)).continuous).comp Real.continuous_sin)
  have hpt : ∀ θ ∈ Set.Icc (0 : ℝ) (Real.pi / 2),
      |Work.FTS.ClassCHon.Lop (fun θ => F t θ) (N + 1) θ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|
        ≤ 3 * ((m : ℝ) + 1) * M * Real.cos θ := by
    intro θ hθ
    have hcosθ : 0 ≤ Real.cos θ :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    have h1 : |Work.FTS.ClassCHon.Lop (fun θ => F t θ) (N + 1) θ| ≤ M := by
      by_cases hmem : θ ∈ Set.Icc c d
      · exact hbd t θ hmem
      · rw [(hLop (N + 1)).eq_zero θ hmem, abs_zero]
        exact hM
    have h2 : |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ 3 * ((m : ℝ) + 1) :=
      le_trans (Work.FTS.PhiStar.Series.abs_eFam_le_sqrt_Npsi m hθ)
        (Work.FTS.PhiStar.Series.sqrt_Npsi_le_three m)
    rw [abs_mul, abs_mul, abs_of_nonneg hcosθ]
    calc |Work.FTS.ClassCHon.Lop (fun θ => F t θ) (N + 1) θ|
          * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| * Real.cos θ
        ≤ M * (3 * ((m : ℝ) + 1)) * Real.cos θ := by
          refine mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hM) le_rfl hcosθ ?_
          positivity
      _ = 3 * ((m : ℝ) + 1) * M * Real.cos θ := by ring
  have hbound : |∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.ClassCHon.Lop (fun θ => F t θ) (N + 1) θ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|
      ≤ 3 * ((m : ℝ) + 1) * M := by
    have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
    have hint1 : IntervalIntegrable
        (fun θ : ℝ => Work.FTS.ClassCHon.Lop (fun θ => F t θ) (N + 1) θ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) volume 0 (Real.pi / 2) :=
      ((hcontg.mul hcontE).mul Real.continuous_cos).intervalIntegrable _ _
    have hint2 : IntervalIntegrable (fun θ : ℝ => 3 * ((m : ℝ) + 1) * M * Real.cos θ)
        volume 0 (Real.pi / 2) := (Real.continuous_cos.intervalIntegrable 0 _).const_mul _
    calc |∫ θ in (0 : ℝ)..(Real.pi / 2),
          Work.FTS.ClassCHon.Lop (fun θ => F t θ) (N + 1) θ
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|
        ≤ ∫ θ in (0 : ℝ)..(Real.pi / 2),
            |Work.FTS.ClassCHon.Lop (fun θ => F t θ) (N + 1) θ
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| :=
          intervalIntegral.abs_integral_le_integral_abs hpi
      _ ≤ ∫ θ in (0 : ℝ)..(Real.pi / 2), 3 * ((m : ℝ) + 1) * M * Real.cos θ :=
          intervalIntegral.integral_mono_on hpi hint1.abs hint2 hpt
      _ = 3 * ((m : ℝ) + 1) * M := by
          rw [intervalIntegral.integral_const_mul, integral_cos, Real.sin_pi_div_two,
            Real.sin_zero, sub_zero, mul_one]
  have hnum : |∫ θ in (0 : ℝ)..(Real.pi / 2),
        F t θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|
      ≤ (1 / Work.FTS.PhiStar.Gegenbauer.lam m) ^ (N + 1) * (3 * ((m : ℝ) + 1) * M) := by
    rw [hiter, abs_mul, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ (1 / Work.FTS.PhiStar.Gegenbauer.lam m) ^ (N + 1))]
    exact mul_le_mul_of_nonneg_left hbound (by positivity)
  have hD : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        Work.FTS.PhiStar.Gegenbauer.eFam m θ ^ 2 * Real.cos θ)
      = ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) :=
    Work.FTS.PhiStar.Gegenbauer.FamNormValue m
  have hDpos : 0 < ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) := by positivity
  have hD1 : 1 ≤ ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) := by
    rw [le_div_iff₀ (by linarith [hm1] : (0 : ℝ) < 4 * (m : ℝ) + 5)]
    nlinarith [hm1]
  have hkey : |Work.FTS.PhiStar.Series.cmode m F t|
      ≤ (1 / Work.FTS.PhiStar.Gegenbauer.lam m) ^ (N + 1) * (3 * ((m : ℝ) + 1) * M) := by
    rw [Work.FTS.PhiStar.Series.cmode, hD, abs_div, abs_of_pos hDpos]
    calc |∫ θ in (0 : ℝ)..(Real.pi / 2),
            F t θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ|
          / (((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5))
        ≤ |∫ θ in (0 : ℝ)..(Real.pi / 2),
            F t θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| / 1 :=
          div_le_div_of_nonneg_left (abs_nonneg _) one_pos hD1
      _ = |∫ θ in (0 : ℝ)..(Real.pi / 2),
            F t θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ| := by ring
      _ ≤ _ := hnum
  have hlam_ge : (m : ℝ) + 1 ≤ Work.FTS.PhiStar.Gegenbauer.lam m := by
    rw [Work.FTS.PhiStar.Gegenbauer.lam]; nlinarith [hm1]
  have hp : ((m : ℝ) + 1) ^ (N + 1) ≤ (Work.FTS.PhiStar.Gegenbauer.lam m) ^ (N + 1) :=
    pow_le_pow_left₀ (by positivity) hlam_ge (N + 1)
  calc |Work.FTS.PhiStar.Series.cmode m F t|
      ≤ (1 / Work.FTS.PhiStar.Gegenbauer.lam m) ^ (N + 1) * (3 * ((m : ℝ) + 1) * M) := hkey
    _ = 3 * M * ((m : ℝ) + 1) / (Work.FTS.PhiStar.Gegenbauer.lam m) ^ (N + 1) := by
        rw [one_div, inv_pow]; ring
    _ ≤ 3 * M * ((m : ℝ) + 1) / ((m : ℝ) + 1) ^ (N + 1) := by
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) hp
    _ = 3 * M / ((m : ℝ) + 1) ^ N := by
        rw [pow_succ]
        field_simp

theorem cmode_decay_of_cptQ {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G) (j N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m → ∀ t : ℝ,
      |Work.FTS.PhiStar.Series.cmode m (Work.Spaces.DzIter j G) t|
        ≤ C / ((m : ℝ) + 1) ^ N := by
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, H⟩ := hG.cpt
  have hz0 : ∀ z θ : ℝ, G z θ ≠ 0 → z ∈ Set.Icc a b := fun z θ h => (H z θ h).1
  have hth0 : ∀ z θ : ℝ, G z θ ≠ 0 → θ ∈ Set.Icc c d := fun z θ h => (H z θ h).2
  have hFsmooth : ∀ n : ℕ, ContDiff ℝ n (Function.uncurry (Work.Spaces.DzIter j G)) :=
    DzIter_contDiff_of_forall_end hG.1 j
  have hFθ : ∀ t θ : ℝ, θ ∉ Set.Icc c d → Work.Spaces.DzIter j G t θ = 0 :=
    fun t θ hθ => DzIter_eq_zero_of_theta_not_mem hth0 j hθ
  have hFt : ∀ t θ : ℝ, t ∉ Set.Icc a b → Work.Spaces.DzIter j G t θ = 0 :=
    fun t θ ht => DzIter_eq_zero_of_z_not_mem hz0 j ht
  have hV : IsOpen Work.FTS.EllipticEst.Q0 := by
    rw [Work.FTS.EllipticEst.Q0]; exact isOpen_Ioi.prod isOpen_Ioo
  have hcosV : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.cos p.2 ≠ 0 := by
    intro p hp
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩)
  have hFon : ∀ n : ℕ,
      ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter j G)) Work.FTS.EllipticEst.Q0 :=
    fun n => (hFsmooth n).contDiffOn
  have hphi := phi_contDiffOn hV hcosV hFon
  have hId := phi_eq_Lop hV hcosV hphi
  have hcont : ContinuousOn (Function.uncurry (phi (Work.Spaces.DzIter j G) (N + 1)))
      (Set.Icc a b ×ˢ Set.Icc c d) :=
    (hphi (N + 1) 0).continuousOn.mono (fun p hp => by
      refine ⟨?_, ?_, ?_⟩
      · exact lt_of_lt_of_le ha hp.1.1
      · exact lt_of_lt_of_le hc hp.2.1
      · exact lt_of_le_of_lt hp.2.2 hd)
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont
  refine ⟨3 * max M₀ 0, by positivity, ?_⟩
  have hbd : ∀ t θ : ℝ, θ ∈ Set.Icc c d →
      |Work.FTS.ClassCHon.Lop (fun θ' => Work.Spaces.DzIter j G t θ') (N + 1) θ|
        ≤ max M₀ 0 := by
    intro t θ hθ
    by_cases ht : t ∈ Set.Icc a b
    · have hmemQ : (t, θ) ∈ Work.FTS.EllipticEst.Q0 :=
        ⟨lt_of_lt_of_le ha ht.1, ⟨lt_of_lt_of_le hc hθ.1, lt_of_le_of_lt hθ.2 hd⟩⟩
      have hb := hM₀ (t, θ) ⟨ht, hθ⟩
      rw [Real.norm_eq_abs] at hb
      rw [← hId (N + 1) t θ hmemQ]
      exact le_trans hb (le_max_left _ _)
    · have hslice : (fun θ' : ℝ => Work.Spaces.DzIter j G t θ') = fun _ => (0 : ℝ) :=
        funext (fun θ' => hFt t θ' ht)
      rw [hslice, Lop_zero_fun (N + 1)]
      simpa using le_max_right M₀ 0
  intro m hm t
  exact cmode_le_of_bound_end hc hd (le_max_right _ _)
    (fun t => ⟨contDiff_infty.mpr (fun n =>
        (hFsmooth n).comp (contDiff_const.prodMk contDiff_id)),
      fun θ hθ => hFθ t θ hθ⟩) hbd m hm t

end Work.FTS.PhiStar.Honesty
