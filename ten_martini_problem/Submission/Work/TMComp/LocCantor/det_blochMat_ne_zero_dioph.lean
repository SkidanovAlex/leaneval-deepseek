import Mathlib
import Submission.Work.TMComp.LocCantor.Bloch
import Submission.Work.TMComp.LocCantor.countable_zero_set
import Submission.Work.TMComp.LocCantor.eq_const_of_periodic
import Submission.Work.TMComp.LocCantor.fourier_zero_set_props
import Submission.Work.TMComp.LocCantor.orbit_leaves_zero_set
import Submission.Work.TMComp.LocCantor.exists_const_of_continuous_of_localConst_compl
import Submission.Work.TMComp.LocCantor.exists_continuous_extension_of_shift

/-!
# The determinant of the Bloch matrix does not vanish identically for Diophantine phases

Let `U = fourier u` be a nonzero real analytic `1`-periodic function on `ℝ` and let
`blochMat α θ u x` be the matrix with columns `W(x) = (U(x) e^{2πiθ}, U(x-α))` and its complex
conjugate.  Its determinant vanishes iff `W(x)` and `conj (W(x))` are linearly dependent, i.e.
iff `e^{2πiθ} U(x) conj (U(x-α))` is real; equivalently the "phase quotient"
`Q(x) = U(x)/conj (U(x))` is quasi-periodic with multiplier `e^{-4πiθ}`.

`Q` is real analytic off the discrete zero set `Z` of `U`; the quasi-periodicity lets one
extend it continuously across `Z`, and the same for its logarithmic derivative `rho`, which is
both `1`- and `α`-periodic where defined, hence constant by irrationality of `α`.  Then `Q`
itself is a character `x ↦ c e^{λx}`, whence `2θ ∈ αℤ + ℤ`, contradicting the hypothesis `hθ`.
-/

noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory Filter Topology Set

namespace Work.TMComp.LocCantor

variable {α θ : ℝ} {u : ℤ → ℂ}

theorem blochDet_im_zero (hzero : ∀ x : ℝ, (blochMat α θ u x).det = 0) :
    ∀ x : ℝ, (Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u x
        * (starRingEnd ℂ) (fourier u (x - α))).im = 0 := by
  intro x
  have hconjexp : (starRingEnd ℂ) (Complex.exp (2 * Real.pi * θ * Complex.I))
      = Complex.exp (-(2 * Real.pi * θ * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  have hdet : (blochMat α θ u x).det
      = Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u x
          * (starRingEnd ℂ) (fourier u (x - α))
        - (starRingEnd ℂ) (Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u x
            * (starRingEnd ℂ) (fourier u (x - α))) := by
    rw [Matrix.det_fin_two]
    simp only [blochMat, blochVec, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Fin.isValue, map_mul, Complex.conj_conj]
    ring
  have hz : Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u x
        * (starRingEnd ℂ) (fourier u (x - α))
      - (starRingEnd ℂ) (Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u x
          * (starRingEnd ℂ) (fourier u (x - α))) = 0 := by
    rw [← hdet]; exact hzero x
  rw [Complex.sub_conj] at hz
  have h1 : (((2 * (Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u x
      * (starRingEnd ℂ) (fourier u (x - α))).im : ℝ)) : ℂ) = 0 :=
    (mul_eq_zero.mp hz).resolve_right Complex.I_ne_zero
  have h2 : 2 * (Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u x
      * (starRingEnd ℂ) (fourier u (x - α))).im = 0 := by exact_mod_cast h1
  linarith

/-- The identity obtained by clearing the denominator in the reality of the phase product. -/
theorem bloch_global_identity (hzero : ∀ x : ℝ, (blochMat α θ u x).det = 0) :
    ∀ x : ℝ, Complex.exp (4 * Real.pi * θ * Complex.I)
        * (fourier u x * (starRingEnd ℂ) (fourier u (x - α)))
      = (starRingEnd ℂ) (fourier u x) * fourier u (x - α) := by
  intro x
  have him := blochDet_im_zero hzero x
  have hz : Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u x
        * (starRingEnd ℂ) (fourier u (x - α))
      = (starRingEnd ℂ) (Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u x
          * (starRingEnd ℂ) (fourier u (x - α))) :=
    (Complex.conj_eq_iff_im.mpr him).symm
  have hconjexp : (starRingEnd ℂ) (Complex.exp (2 * Real.pi * θ * Complex.I))
      = Complex.exp (-(2 * Real.pi * θ * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [map_mul, map_mul, hconjexp, Complex.conj_conj] at hz
  have hE : Complex.exp (4 * Real.pi * θ * Complex.I)
      = Complex.exp (2 * Real.pi * θ * Complex.I) * Complex.exp (2 * Real.pi * θ * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [hE]
  calc Complex.exp (2 * Real.pi * θ * Complex.I) * Complex.exp (2 * Real.pi * θ * Complex.I)
          * (fourier u x * (starRingEnd ℂ) (fourier u (x - α)))
      = Complex.exp (2 * Real.pi * θ * Complex.I)
          * (Complex.exp (2 * Real.pi * θ * Complex.I) * fourier u x
            * (starRingEnd ℂ) (fourier u (x - α))) := by ring
    _ = Complex.exp (2 * Real.pi * θ * Complex.I)
          * (Complex.exp (-(2 * Real.pi * θ * Complex.I)) * (starRingEnd ℂ) (fourier u x)
            * fourier u (x - α)) := by rw [hz]
    _ = (starRingEnd ℂ) (fourier u x) * fourier u (x - α) := by
          rw [show Complex.exp (2 * Real.pi * θ * Complex.I)
                * (Complex.exp (-(2 * Real.pi * θ * Complex.I)) * (starRingEnd ℂ) (fourier u x)
                  * fourier u (x - α))
              = (Complex.exp (2 * Real.pi * θ * Complex.I)
                  * Complex.exp (-(2 * Real.pi * θ * Complex.I)))
                * ((starRingEnd ℂ) (fourier u x) * fourier u (x - α)) by ring,
            ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

/-- The phase quotient `Q x = U x / conj (U x)` is quasi-periodic with multiplier
`e^{-4πiθ}` wherever both `U x` and `U (x-α)` are nonzero. -/
theorem quotient_relation (hzero : ∀ x : ℝ, (blochMat α θ u x).det = 0) :
    ∀ x : ℝ, fourier u x ≠ 0 → fourier u (x - α) ≠ 0 →
      fourier u x / (starRingEnd ℂ) (fourier u x)
        = Complex.exp (-(4 * Real.pi * θ * Complex.I))
          * (fourier u (x - α) / (starRingEnd ℂ) (fourier u (x - α))) := by
  intro x h1 h2
  have hkey := bloch_global_identity hzero x
  have hc1 : (starRingEnd ℂ) (fourier u x) ≠ 0 := by simpa using h1
  have hc2 : (starRingEnd ℂ) (fourier u (x - α)) ≠ 0 := by simpa using h2
  have he : Complex.exp (-(4 * Real.pi * θ * Complex.I))
      * Complex.exp (4 * Real.pi * θ * Complex.I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  have hmain : fourier u x * (starRingEnd ℂ) (fourier u (x - α))
      = Complex.exp (-(4 * Real.pi * θ * Complex.I))
        * ((starRingEnd ℂ) (fourier u x) * fourier u (x - α)) := by
    have := congrArg (fun w => Complex.exp (-(4 * Real.pi * θ * Complex.I)) * w) hkey
    simpa [← mul_assoc, he] using this
  rw [div_eq_iff hc1]
  field_simp
  linear_combination hmain

/-! ## 2. The derivative of the phase quotient -/

theorem hasDerivAt_fourier_quotient (hAn : AnalyticOnNhd ℝ (fourier u) Set.univ) (x : ℝ)
    (hx : fourier u x ≠ 0) :
    HasDerivAt (fun y => fourier u y / (starRingEnd ℂ) (fourier u y))
      ((deriv (fourier u) x * (starRingEnd ℂ) (fourier u x)
          - fourier u x * (starRingEnd ℂ) (deriv (fourier u) x))
        / ((starRingEnd ℂ) (fourier u x)) ^ 2) x := by
  have hU : HasDerivAt (fourier u) (deriv (fourier u) x) x :=
    (hAn x (mem_univ x)).differentiableAt.hasDerivAt
  have hS : HasDerivAt (fun y => (starRingEnd ℂ) (fourier u y))
      ((starRingEnd ℂ) (deriv (fourier u) x)) x := hU.star
  have hden : (starRingEnd ℂ) (fourier u x) ≠ 0 := by simpa using hx
  exact hU.div hS hden

theorem deriv_quotient_quasi_periodic (hAn : AnalyticOnNhd ℝ (fourier u) Set.univ)
    (hzero : ∀ x : ℝ, (blochMat α θ u x).det = 0) {x : ℝ}
    (h1 : fourier u x ≠ 0) (h2 : fourier u (x + α) ≠ 0) :
    deriv (fun y => fourier u y / (starRingEnd ℂ) (fourier u y)) x
        / (fourier u x / (starRingEnd ℂ) (fourier u x))
      = deriv (fun y => fourier u y / (starRingEnd ℂ) (fourier u y)) (x + α)
        / (fourier u (x + α) / (starRingEnd ℂ) (fourier u (x + α))) := by
  set Q : ℝ → ℂ := fun y => fourier u y / (starRingEnd ℂ) (fourier u y) with hQ
  set eta : ℂ := Complex.exp (-(4 * Real.pi * θ * Complex.I)) with hetadef
  have hcont : Continuous (fourier u) := continuousOn_univ.mp hAn.continuousOn
  have hxα : (x + α) - α = x := by ring
  have hev : ∀ᶠ y in 𝓝 (x + α), fourier u y ≠ 0 ∧ fourier u (y - α) ≠ 0 := by
    have h1' : ∀ᶠ y in 𝓝 (x + α), fourier u y ≠ 0 := hcont.continuousAt.eventually_ne h2
    have h2' : ∀ᶠ y in 𝓝 (x + α), fourier u (y - α) ≠ 0 := by
      have hc : Continuous fun y : ℝ => fourier u (y - α) :=
        hcont.comp (continuous_id.sub continuous_const)
      have : (fun y : ℝ => fourier u (y - α)) (x + α) ≠ 0 := by simpa [hxα] using h1
      exact hc.continuousAt.eventually_ne this
    filter_upwards [h1', h2'] with y hy1 hy2
    exact ⟨hy1, hy2⟩
  have hrel_near : Q =ᶠ[𝓝 (x + α)] fun y => eta * Q (y - α) := by
    filter_upwards [hev] with y hy
    have := quotient_relation hzero y hy.1 hy.2
    simpa [Q, eta, hQ, hetadef] using this
  have hQderiv : HasDerivAt Q (deriv Q x) x := by
    have h := hasDerivAt_fourier_quotient hAn x h1
    rw [← hQ] at h
    simpa [← h.deriv] using h
  have hQderivw : HasDerivAt Q (deriv Q (x + α)) (x + α) := by
    have h := hasDerivAt_fourier_quotient hAn (x + α) h2
    rw [← hQ] at h
    simpa [← h.deriv] using h
  have hcomp : HasDerivAt Q (eta * deriv Q x) (x + α) :=
    HasDerivAt.congr_of_eventuallyEq
      ((HasDerivAt.const_mul eta) ((HasDerivAt.comp_sub_const (x + α) α)
        (by simpa using hQderiv))) hrel_near
  have hkey : deriv Q (x + α) = eta * deriv Q x := hQderivw.unique hcomp
  have hQw : Q (x + α) = eta * Q x := by
    have := quotient_relation hzero (x + α) h2 (by simpa [hxα] using h1)
    simpa [Q, eta, hQ, hetadef] using this
  have hQx : Q x ≠ 0 := by
    have h' : Q x = fourier u x / (starRingEnd ℂ) (fourier u x) := rfl
    rw [h']
    exact div_ne_zero h1 (by simpa using h1)
  have he : eta ≠ 0 := Complex.exp_ne_zero _
  rw [hkey]
  change deriv Q x / Q x = eta * deriv Q x / Q (x + α)
  rw [hQw]
  field_simp

/-- The complement of a closed discrete subset of `ℝ` is dense. -/
theorem dense_compl_of_closed_discrete {Z : Set ℝ} (hZc : IsClosed Z)
    (hZd : ∀ z ∈ Z, ∃ ε > 0, ∀ y ∈ Z, |y - z| < ε → y = z) : Dense (Zᶜ : Set ℝ) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro x
  rw [Metric.mem_closure_iff]
  intro ε hε
  by_cases hx : x ∈ Z
  · obtain ⟨δ, hδ, hδZ⟩ := hZd x hx
    have hmin : 0 < min δ ε := lt_min hδ hε
    have hpos : 0 < min δ ε / 2 := by linarith
    have hltδ : min δ ε / 2 < δ :=
      lt_of_lt_of_le (by linarith) (min_le_left δ ε)
    have hltε : min δ ε / 2 < ε :=
      lt_of_lt_of_le (by linarith) (min_le_right δ ε)
    refine ⟨x + min δ ε / 2, ?_, ?_⟩
    · simp only [Set.mem_compl_iff]
      intro hxin
      have h1 : |x + min δ ε / 2 - x| < δ := by
        rw [add_sub_cancel_left, abs_of_pos hpos]
        exact hltδ
      have h2 : x + min δ ε / 2 = x := hδZ _ hxin h1
      linarith
    · rw [dist_eq_norm, show x - (x + min δ ε / 2) = -(min δ ε / 2) by ring, Real.norm_eq_abs,
        abs_neg, abs_of_pos hpos]
      exact hltε
  · exact ⟨x, hx, by simpa using hε⟩


theorem det_blochMat_ne_zero_dioph {α θ : ℝ} {u : ℤ → ℂ} (hα : Irrational α)
    (hAn : AnalyticOnNhd ℝ (Work.TMComp.fourier u) Set.univ)
    (hcont : Continuous (Work.TMComp.fourier u))
    (hper : ∀ x, Work.TMComp.fourier u (x + 1) = Work.TMComp.fourier u x)
    (hnt : Work.TMComp.fourier u ≠ 0)
    (hθ : ∀ k l : ℤ, 2 * θ ≠ (k : ℝ) * α + (l : ℝ))
    (hzero : ∀ x, (Work.TMComp.blochMat α θ u x).det = 0) : False := by
  set Z : Set ℝ := {x | fourier u x = 0} with hZdef
  have hmem : ∀ x, x ∈ Z ↔ fourier u x = 0 := fun x => Iff.rfl
  obtain ⟨hZc, hZd, hZfin, hZper⟩ := fourier_zero_set_props hAn hnt hper
  have hdenseZ : Dense (Zᶜ : Set ℝ) := dense_compl_of_closed_discrete hZc hZd
  set eta : ℂ := Complex.exp (-(4 * Real.pi * θ * Complex.I)) with hetadef
  have heta_ne : eta ≠ 0 := Complex.exp_ne_zero _
  set Q : ℝ → ℂ := fun x => fourier u x / (starRingEnd ℂ) (fourier u x) with hQdef
  have hUnz : ∀ x, x ∉ Z → fourier u x ≠ 0 := fun x hx h => hx ((hmem x).mpr h)
  have hQ_ne : ∀ x, x ∉ Z → Q x ≠ 0 := by
    intro x hx
    have hx' := hUnz x hx
    show fourier u x / (starRingEnd ℂ) (fourier u x) ≠ 0
    exact div_ne_zero hx' (by simpa using hx')
  have hQrel : ∀ x, x ∉ Z → x + α ∉ Z → Q (x + α) = eta * Q x := by
    intro x hx hxα
    have hx' := hUnz x hx
    have hxα' := hUnz (x + α) hxα
    have h := quotient_relation hzero (x + α) hxα' (by simpa using hx')
    simpa [Q, eta, hQdef, hetadef] using h
  have hQcont : ContinuousOn Q Zᶜ := by
    have h2 : Continuous fun x => (starRingEnd ℂ) (fourier u x) := continuous_star.comp hcont
    exact ContinuousOn.div hcont.continuousOn h2.continuousOn
      (fun x hx => by simpa using hUnz x hx)
  have hZesc : ∀ z ∈ Z, ∃ K : ℕ, 1 ≤ K ∧ z + (K : ℝ) * α ∉ Z :=
    orbit_leaves_zero_set hα hZfin hZper
  obtain ⟨Qe, hQe_cont, hQe_eq⟩ :=
    exists_continuous_extension_of_shift hα hZc hZd hZesc heta_ne hQcont hQrel
  have hZper1 : ∀ x, x ∉ Z → x + 1 ∉ Z := by
    intro x hx h
    have h' : x + 1 ∈ ({x : ℝ | fourier u x = 0} : Set ℝ) := (hmem (x + 1)).mp h
    have h2 := (hZper (x + 1) h').2
    exact hx ((hmem x).mpr (by simpa using h2))
  have hQper : ∀ x, x ∉ Z → x + 1 ∉ Z → Q (x + 1) = Q x := by
    intro x hx hx1
    show fourier u (x + 1) / (starRingEnd ℂ) (fourier u (x + 1))
      = fourier u x / (starRingEnd ℂ) (fourier u x)
    rw [hper x]
  have hQe_per : ∀ x, Qe (x + 1) = Qe x := by
    have hclosed : IsClosed {x : ℝ | Qe (x + 1) = Qe x} :=
      isClosed_eq (hQe_cont.comp (continuous_add_const 1)) hQe_cont
    have hsub : Zᶜ ⊆ {x : ℝ | Qe (x + 1) = Qe x} := by
      intro x hx
      have hx1 := hZper1 x hx
      show Qe (x + 1) = Qe x
      rw [hQe_eq (x + 1) hx1, hQe_eq x hx]
      exact hQper x hx hx1
    intro x
    exact hclosed.closure_subset (closure_mono hsub (by rw [hdenseZ.closure_eq]; trivial))
  have hshift_closed : IsClosed {y : ℝ | y + α ∈ Z} := hZc.preimage (continuous_add_const α)
  have hshift_disc : ∀ z ∈ {y : ℝ | y + α ∈ Z}, ∃ ε > 0, ∀ y ∈ {y : ℝ | y + α ∈ Z},
      |y - z| < ε → y = z := by
    intro z hz
    obtain ⟨δ, hδ, hδZ⟩ := hZd (z + α) hz
    refine ⟨δ, hδ, ?_⟩
    intro y hy hyδ
    have h1 : |(y + α) - (z + α)| < δ := by simpa using hyδ
    have := hδZ (y + α) hy h1
    linarith
  have hdenseS : Dense ({x : ℝ | x + α ∉ Z}) := by
    have h := dense_compl_of_closed_discrete hshift_closed hshift_disc
    have heq : ({x : ℝ | x + α ∉ Z}) = ({y : ℝ | y + α ∈ Z})ᶜ := by
      ext x; simp
    rw [heq]; exact h
  have hdenseZS : Dense ((Zᶜ ∩ {x : ℝ | x + α ∉ Z}) : Set ℝ) :=
    hdenseZ.inter_of_isOpen_right hdenseS (hZc.isOpen_compl.preimage (continuous_add_const α))
  have hQe_alpha : ∀ x, Qe (x + α) = eta * Qe x := by
    have hclosed : IsClosed {x : ℝ | Qe (x + α) = eta * Qe x} :=
      isClosed_eq (hQe_cont.comp (continuous_add_const α)) (continuous_const.mul hQe_cont)
    have hsub : (Zᶜ ∩ {x : ℝ | x + α ∉ Z}) ⊆ {x : ℝ | Qe (x + α) = eta * Qe x} := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      show Qe (x + α) = eta * Qe x
      rw [hQe_eq (x + α) hx2, hQe_eq x hx1]
      exact hQrel x hx1 hx2
    intro x
    exact hclosed.closure_subset (closure_mono hsub (by rw [hdenseZS.closure_eq]; trivial))
  -- the logarithmic derivative of Q
  set rho : ℝ → ℂ := fun x => deriv Q x / Q x with hrhodef
  have hderivQ_eq : ∀ x ∈ Zᶜ, deriv Q x
      = (deriv (fourier u) x * (starRingEnd ℂ) (fourier u x)
          - fourier u x * (starRingEnd ℂ) (deriv (fourier u) x))
        / ((starRingEnd ℂ) (fourier u x)) ^ 2 := by
    intro x hx
    have hx' := hUnz x hx
    have h := hasDerivAt_fourier_quotient hAn x hx'
    rw [← hQdef] at h
    exact h.deriv
  have hrho_cont : ContinuousOn rho Zᶜ := by
    have hdU : Continuous (deriv (fourier u)) := continuousOn_univ.mp (hAn.deriv).continuousOn
    have hconjU : Continuous fun x => (starRingEnd ℂ) (fourier u x) := continuous_star.comp hcont
    have hconjdU : Continuous fun x => (starRingEnd ℂ) (deriv (fourier u) x) :=
      continuous_star.comp hdU
    have hf : ContinuousOn (fun x => (deriv (fourier u) x * (starRingEnd ℂ) (fourier u x)
        - fourier u x * (starRingEnd ℂ) (deriv (fourier u) x))
        / ((starRingEnd ℂ) (fourier u x)) ^ 2) Zᶜ := by
      refine ContinuousOn.div ?_ ?_ ?_
      · exact (hdU.continuousOn.mul hconjU.continuousOn).sub
          (hcont.continuousOn.mul hconjdU.continuousOn)
      · exact hconjU.continuousOn.pow 2
      · intro x hx
        exact pow_ne_zero 2 (by simpa using hUnz x hx)
    have h1 : ContinuousOn (deriv Q) Zᶜ := hf.congr (fun x hx => (hderivQ_eq x hx))
    exact h1.div hQcont hQ_ne
  have hrho_rel : ∀ x, x ∉ Z → x + α ∉ Z → rho (x + α) = rho x := by
    intro x hx hxα
    have h := deriv_quotient_quasi_periodic hAn hzero (hUnz x hx) (hUnz (x + α) hxα)
    have h' : deriv Q x / Q x = deriv Q (x + α) / Q (x + α) := by
      simpa [Q, hQdef] using h
    show deriv Q (x + α) / Q (x + α) = deriv Q x / Q x
    exact h'.symm
  obtain ⟨rhoe, hrhoe_cont, hrhoe_eq⟩ :=
    exists_continuous_extension_of_shift hα hZc hZd hZesc one_ne_zero hrho_cont
      (fun x hx hxα => by rw [one_mul]; exact hrho_rel x hx hxα)
  have hrho_per1 : ∀ x, x ∉ Z → x + 1 ∉ Z → deriv Q (x + 1) = deriv Q x := by
    intro x hx hx1
    have heq : (fun y => Q (y + 1)) =ᶠ[𝓝 x] Q := by
      filter_upwards [IsOpen.mem_nhds hZc.isOpen_compl hx,
        IsOpen.mem_nhds (hZc.isOpen_compl.preimage (continuous_add_const 1)) hx1] with y hy1 hy2
      exact hQper y hy1 hy2
    have h2 : deriv (fun y => Q (y + 1)) x = deriv Q x := heq.deriv_eq
    have h3 : HasDerivAt (fun y => Q (y + 1)) (deriv Q (x + 1)) x := by
      have hQd : HasDerivAt Q (deriv Q (x + 1)) (x + 1) := by
        have h := hasDerivAt_fourier_quotient hAn (x + 1) (hUnz (x + 1) hx1)
        rw [← hQdef] at h
        simpa [← h.deriv] using h
      exact hQd.comp_add_const x 1
    rw [← h2, h3.deriv]
  have hrhoe_per1 : ∀ x, rhoe (x + 1) = rhoe x := by
    have hclosed : IsClosed {x : ℝ | rhoe (x + 1) = rhoe x} :=
      isClosed_eq (hrhoe_cont.comp (continuous_add_const 1)) hrhoe_cont
    have hsub : Zᶜ ⊆ {x : ℝ | rhoe (x + 1) = rhoe x} := by
      intro x hx
      have hx1 := hZper1 x hx
      show rhoe (x + 1) = rhoe x
      rw [hrhoe_eq (x + 1) hx1, hrhoe_eq x hx]
      show deriv Q (x + 1) / Q (x + 1) = deriv Q x / Q x
      rw [hrho_per1 x hx hx1, hQper x hx hx1]
    intro x
    exact hclosed.closure_subset (closure_mono hsub (by rw [hdenseZ.closure_eq]; trivial))
  have hrhoe_alpha : ∀ x, rhoe (x + α) = rhoe x := by
    have hclosed : IsClosed {x : ℝ | rhoe (x + α) = rhoe x} :=
      isClosed_eq (hrhoe_cont.comp (continuous_add_const α)) hrhoe_cont
    have hsub : (Zᶜ ∩ {x : ℝ | x + α ∉ Z}) ⊆ {x : ℝ | rhoe (x + α) = rhoe x} := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      show rhoe (x + α) = rhoe x
      rw [hrhoe_eq (x + α) hx2, hrhoe_eq x hx1]
      exact hrho_rel x hx1 hx2
    intro x
    exact hclosed.closure_subset (closure_mono hsub (by rw [hdenseZS.closure_eq]; trivial))
  obtain ⟨lam, hlam⟩ := eq_const_of_periodic rhoe hrhoe_cont α hα hrhoe_per1 hrhoe_alpha
  have hrho_lam : ∀ x, x ∉ Z → rho x = lam := by
    intro x hx
    rw [← hrhoe_eq x hx]
    exact hlam x
  -- the function Q e^{-lam x} is constant
  set G : ℝ → ℂ := fun x => Qe x * Complex.exp (-(lam * x)) with hGdef
  have hGcont : Continuous G :=
    hQe_cont.mul (Complex.continuous_exp.comp ((continuous_const.mul Complex.continuous_ofReal).neg))
  have hGconst : ∃ c, ∀ x, G x = c := by
    refine exists_const_of_continuous_of_localConst_compl hZc hZd hGcont ?_
    intro x hx
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (IsOpen.mem_nhds hZc.isOpen_compl hx)
    refine ⟨ε, hε, ?_⟩
    intro y hy hyε
    have hI : Set.Ioo (x - ε) (x + ε) ⊆ Zᶜ := by
      intro t ht
      refine hεsub ?_
      rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hev : ∀ t ∈ Zᶜ, Qe =ᶠ[𝓝 t] Q := by
      intro t ht
      filter_upwards [IsOpen.mem_nhds hZc.isOpen_compl ht] with z hz
      exact hQe_eq z hz
    have hderG : ∀ t ∈ Set.Ioo (x - ε) (x + ε), deriv G t = 0 := by
      intro t ht
      have ht' : t ∈ Zᶜ := hI ht
      have htU := hUnz t ht'
      have hQd : DifferentiableAt ℝ Q t := (hasDerivAt_fourier_quotient hAn t htU).differentiableAt
      have hQed : DifferentiableAt ℝ Qe t := hQd.congr_of_eventuallyEq (hev t ht')
      have hder : deriv Qe t = lam * Qe t := by
        have h1 : deriv Qe t = deriv Q t := (hev t ht').deriv_eq
        have h2 : deriv Q t = rho t * Q t := by
          show deriv Q t = (deriv Q t / Q t) * Q t
          rw [div_mul_cancel₀ _ (hQ_ne t ht')]
        rw [h1, h2, hrho_lam t ht', hQe_eq t ht']
      have hdlin : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have hdlam : HasDerivAt (fun s : ℝ => -(lam * (s : ℂ))) (-lam) t := by
        have h := hdlin.const_mul (-lam)
        simpa [neg_mul, one_mul] using h
      have hdexp' : HasDerivAt (fun s : ℝ => Complex.exp (-(lam * (s : ℂ))))
          (Complex.exp (-(lam * (t : ℂ))) * (-lam)) t := HasDerivAt.cexp hdlam
      have hdmul : deriv G t = deriv Qe t * Complex.exp (-(lam * t))
          + Qe t * deriv (fun s : ℝ => Complex.exp (-(lam * s))) t := by
        show deriv (fun s : ℝ => Qe s * Complex.exp (-(lam * s))) t = _
        exact deriv_mul hQed hdexp'.differentiableAt
      rw [hdmul, hder, hdexp'.deriv]
      ring
    have hdiff : DifferentiableOn ℝ G (Set.Ioo (x - ε) (x + ε)) := by
      intro t ht
      have ht' : t ∈ Zᶜ := hI ht
      have hQd : DifferentiableAt ℝ Q t :=
        (hasDerivAt_fourier_quotient hAn t (hUnz t ht')).differentiableAt
      have hQed : DifferentiableAt ℝ Qe t := hQd.congr_of_eventuallyEq (hev t ht')
      have hdlin : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have hdlam : HasDerivAt (fun s : ℝ => -(lam * (s : ℂ))) (-lam) t := by
        have h := hdlin.const_mul (-lam)
        simpa [neg_mul, one_mul] using h
      have hdexp' : HasDerivAt (fun s : ℝ => Complex.exp (-(lam * (s : ℂ))))
          (Complex.exp (-(lam * (t : ℂ))) * (-lam)) t := HasDerivAt.cexp hdlam
      exact (hQed.mul hdexp'.differentiableAt).differentiableWithinAt
    exact (isOpen_Ioo.is_const_of_deriv_eq_zero (x := x) (y := y) isPreconnected_Ioo hdiff hderG
      (show x ∈ Set.Ioo (x - ε) (x + ε) from ⟨by linarith, by linarith⟩)
      (show y ∈ Set.Ioo (x - ε) (x + ε) from ⟨by linarith [abs_lt.mp hyε],
        by linarith [abs_lt.mp hyε]⟩)).symm
  obtain ⟨c, hc⟩ := hGconst
  have hQe_norm : ∀ x, ‖Qe x‖ = 1 := by
    have hclosed : IsClosed {x : ℝ | ‖Qe x‖ = 1} :=
      isClosed_eq (continuous_norm.comp hQe_cont) continuous_const
    have hsub : Zᶜ ⊆ {x : ℝ | ‖Qe x‖ = 1} := by
      intro x hx
      show ‖Qe x‖ = 1
      rw [hQe_eq x hx]
      show ‖fourier u x / (starRingEnd ℂ) (fourier u x)‖ = 1
      rw [norm_div]
      have hnorm : ‖(starRingEnd ℂ) (fourier u x)‖ = ‖fourier u x‖ := by simp
      rw [hnorm]
      exact div_self (norm_ne_zero_iff.mpr (hUnz x hx))
    intro x
    exact hclosed.closure_subset (closure_mono hsub (by rw [hdenseZ.closure_eq]; trivial))
  have hc_ne : c ≠ 0 := by
    intro h0
    have h1 := hQe_norm 0
    have h3 : G 0 = Qe 0 := by simp [G, hGdef]
    have h2 : Qe 0 = c := h3.symm.trans (hc 0)
    rw [h2, h0] at h1
    simp at h1
  have hQe_form : ∀ x, Qe x = c * Complex.exp (lam * x) := by
    intro x
    have h := hc x
    have hExp : Complex.exp (lam * x) * Complex.exp (-(lam * x)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have h2 : Qe x * Complex.exp (-(lam * x)) = c := by
      simpa [G, hGdef] using h
    calc Qe x = Qe x * (Complex.exp (lam * x) * Complex.exp (-(lam * x))) := by rw [hExp, mul_one]
      _ = (Qe x * Complex.exp (-(lam * x))) * Complex.exp (lam * x) := by ring
      _ = c * Complex.exp (lam * x) := by rw [h2]
  have hexp1 : Complex.exp lam = 1 := by
    have h := hQe_per 0
    simp only [zero_add] at h
    rw [hQe_form 1, hQe_form 0] at h
    have h' : c * Complex.exp lam = c * 1 := by simpa using h
    exact mul_left_cancel₀ hc_ne h'
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.mp hexp1
  have heta_eq : eta = Complex.exp (lam * α) := by
    have h := hQe_alpha 0
    simp only [zero_add] at h
    rw [hQe_form α, hQe_form 0] at h
    have h'' : eta * c = c * Complex.exp (lam * α) := by simpa using h.symm
    have h' : Complex.exp (lam * α) * c = eta * c := by rw [h'']; ring
    exact (mul_right_cancel₀ hc_ne h').symm
  have hkey : Complex.exp (-(4 * Real.pi * θ * Complex.I)) = Complex.exp (lam * α) := by
    rw [← hetadef, heta_eq]
  rw [hm] at hkey
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hkey
  have hI : ((-4 * Real.pi * θ : ℝ) : ℂ) * Complex.I
      = ((2 * Real.pi * (m : ℝ) * α + 2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I := by
    have hL : ((-4 * Real.pi * θ : ℝ) : ℂ) * Complex.I = -(4 * Real.pi * θ * Complex.I) := by
      push_cast; ring
    have hR : ((2 * Real.pi * (m : ℝ) * α + 2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I
        = (↑m * (2 * Real.pi * Complex.I)) * α + ↑n * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [hL, hR]
    exact hn
  have hre : -4 * Real.pi * θ = 2 * Real.pi * (m : ℝ) * α + 2 * Real.pi * (n : ℝ) :=
    Complex.ofReal_inj.mp (mul_right_cancel₀ Complex.I_ne_zero hI)
  exact hθ (-m) (-n) (by
    have h2 : -(4 * θ) = 2 * (m : ℝ) * α + 2 * (n : ℝ) := by
      have h3 : Real.pi * (-(4 * θ)) = Real.pi * (2 * (m : ℝ) * α + 2 * (n : ℝ)) := by
        linear_combination hre
      exact mul_left_cancel₀ Real.pi_ne_zero h3
    have h' : 2 * θ = -(m : ℝ) * α + -(n : ℝ) := by linarith
    simpa using h')


end Work.TMComp.LocCantor
