import Mathlib
import Submission.Work.CLift.bridge
import Submission.Work.CLift.Phi_ne_root
import Submission.Work.CLift.Phi_small
import Submission.Work.CLift.basic_aux
import Submission.Work.CLift.hasDerivAt_Vp
import Submission.Work.CLift.R2p_ne_zero

/-!
# Area CLift — the initial solution `Y₀ = (u, v) ∘ Φ` of the pulled-back system

`Y0v m n ra rb rab r0 Φ z = (U₀(Φ z), Vp(Φ z))` is the initial-value solution of the
linear system of Theorem C pulled back along a lift `Φ` of `φ_C = h ∘ ψ_C`.

This module proves `Work.CLift.Y0_solves`:

* `Y0v … Φ` is holomorphic on the small disc `ball 0 (1/1000)`;
* on the annulus `3.2·10⁻⁴ < ‖z‖ < 1/1000` it satisfies the pulled-back system
  `Y₀'(z) = sysA(m,n,Φ)(z)·Y₀(z) + sysb(m,n,Φ)(z)`.

The proof is the chain rule, applied to the two components:

* the first component is `U₀ ∘ Φ`, with `(U₀)' = U₁` (`hasDerivAt_U`), and the identity
  `U₁ = A₁₁U₀ + A₁₂·Vp + β` (from the definition of `Vp = (U₁ − U₀/2 − β)/(x+1)`) gives the
  first row of the system;
* the second component is `Vp ∘ Φ`, whose derivative is the second row of the system
  (`hasDerivAt_Vp`, `A₂₁U₀ + A₂₂·Vp + c₂`).

The hypotheses `‖Φ z‖ ≤ 1/50` (`Phi_small`), `Φ z ≠ -1`, `R2p (Φ z) ≠ 0` (`R2p_ne_zero`, from
`Phi_ne_one`, `hΦ0`, `q4_roots`, `Phi_ne_root`) supply exactly the side conditions needed for
`hasDerivAt_U` (radius `1/2`) and `hasDerivAt_Vp`.
-/

namespace Work.CLift

open Work.CLift Submission.CDTPlan Metric
open scoped BigOperators

noncomputable section

/-! ## The two components of `Y₀` -/

lemma Y0v_zero (m n : ℕ) (ra rb rab r0 : ℤ) (Φ : ℂ → ℂ) (z : ℂ) :
    Y0v m n ra rb rab r0 Φ z 0 = U0 m n ra rb rab r0 (Φ z) := by
  simp only [Y0v]; rfl

lemma Y0v_one (m n : ℕ) (ra rb rab r0 : ℤ) (Φ : ℂ → ℂ) (z : ℂ) :
    Y0v m n ra rb rab r0 Φ z 1 = Vp m n ra rb rab r0 (Φ z) := by
  simp only [Y0v]; rfl

/-! ## The first row of the system -/

/-- The gauge identity of the first row: `U₁ = A₁₁U₀ + A₁₂·v + β` for `x ≠ -1`. -/
lemma U1_eq (m n : ℕ) (ra rb rab r0 : ℤ) {x : ℂ} (hx1 : x ≠ -1) :
    U1 m n ra rb rab r0 x = A11 * U0 m n ra rb rab r0 x + A12 x * Vp m n ra rb rab r0 x
      + bbeta m n ra rb := by
  have hx1' : x + 1 ≠ 0 := by intro h; exact hx1 (by linear_combination h)
  have hV : (x + 1) * Vp m n ra rb rab r0 x
      = U1 m n ra rb rab r0 x - U0 m n ra rb rab r0 x / 2 - bbeta m n ra rb := by
    rw [Vp, mul_div_cancel₀ _ hx1']
  simp only [A11, A12]
  rw [hV]
  ring

/-! ## The entries of the pulled-back system -/

lemma sysA_00 (m n : ℕ) (Φ : ℂ → ℂ) (z : ℂ) : sysA m n Φ z 0 0 = deriv Φ z * A11 := by
  simp [sysA]

lemma sysA_01 (m n : ℕ) (Φ : ℂ → ℂ) (z : ℂ) :
    sysA m n Φ z 0 1 = deriv Φ z * A12 (Φ z) := by simp [sysA]

lemma sysA_10 (m n : ℕ) (Φ : ℂ → ℂ) (z : ℂ) :
    sysA m n Φ z 1 0 = deriv Φ z * A21 m n (Φ z) := by simp [sysA]

lemma sysA_11 (m n : ℕ) (Φ : ℂ → ℂ) (z : ℂ) :
    sysA m n Φ z 1 1 = deriv Φ z * A22 m n (Φ z) := by simp [sysA]

lemma sysb_0 (m n : ℕ) (ra rb rab : ℤ) (Φ : ℂ → ℂ) (z : ℂ) :
    sysb m n ra rb rab Φ z 0 = deriv Φ z * bbeta m n ra rb := by simp [sysb]

lemma sysb_1 (m n : ℕ) (ra rb rab : ℤ) (Φ : ℂ → ℂ) (z : ℂ) :
    sysb m n ra rb rab Φ z 1 = deriv Φ z * c2 m n ra rb rab (Φ z) := by simp [sysb]

/-! ## The main statement -/

theorem Y0_solves (m n : ℕ) (ra rb rab r0 : ℤ) (hR : PRadius) (hL : CLocation) (hN : CNumerics)
    (hM : HauptFacts) (hP : PsiCFacts) (hAdm : CAdm m n) (hRel : CRel m n ra rb rab r0)
    (Φ : ℂ → ℂ)
    (hΦdiff : DifferentiableOn ℂ Φ (ball (0 : ℂ) 1))
    (hΦeq : ∀ z ∈ ball (0 : ℂ) 1, Φ z + Φ (-z) = phiC (z ^ 2) ∧ Φ z * Φ (-z) = phiC (z ^ 2))
    (hΦ0 : ∀ z ∈ ball (0 : ℂ) 1, Φ z = 0 → z = 0) :
    DifferentiableOn ℂ (Y0v m n ra rb rab r0 Φ) (ball (0 : ℂ) (1 / 1000)) ∧
      (∀ z : ℂ, 3.2e-4 < ‖z‖ → ‖z‖ < 1 / 1000 →
        HasDerivAt (Y0v m n ra rb rab r0 Φ)
          (fun i => ∑ j, sysA m n Φ z i j * Y0v m n ra rb rab r0 Φ z j
            + sysb m n ra rb rab Φ z i) z) := by
  have hPsmall : ∀ z : ℂ, ‖z‖ ≤ 1 / 1000 → ‖Φ z‖ ≤ 1 / 50 := Phi_small hM hP Φ hΦeq
  have hballsub : ball (0 : ℂ) (1 / 1000) ⊆ ball (0 : ℂ) 1 := by
    apply ball_subset_ball; norm_num
  have hΦdiff' : DifferentiableOn ℂ Φ (ball (0 : ℂ) (1 / 1000)) := hΦdiff.mono hballsub
  -- `Φ` maps the small disc into `ball 0 (1/2)`, where `U₀` and `Vp` are holomorphic
  have hΦmaps : Set.MapsTo Φ (ball (0 : ℂ) (1 / 1000)) (ball (0 : ℂ) (1 / 2)) := by
    intro z hz
    have hzle : ‖z‖ ≤ 1 / 1000 := by
      rw [mem_ball, dist_zero_right] at hz; exact le_of_lt hz
    have h := hPsmall z hzle
    rw [mem_ball, dist_zero_right]
    linarith
  have hU0diff : DifferentiableOn ℂ (U0 m n ra rb rab r0) (ball (0 : ℂ) (1 / 2)) := by
    intro x hx
    have hx' : ‖x‖ < 1 / 2 := by rwa [mem_ball, dist_zero_right] at hx
    exact (((hasDerivAt_U m n ra rb rab r0 hR hAdm hRel x hx').1).differentiableAt).differentiableWithinAt
  have hVpdiff : DifferentiableOn ℂ (Vp m n ra rb rab r0) (ball (0 : ℂ) (1 / 2)) := by
    intro x hx
    have hx' : ‖x‖ < 1 / 2 := by rwa [mem_ball, dist_zero_right] at hx
    have hx1 : x ≠ -1 := by
      intro h; rw [h] at hx'; norm_num at hx'
    have hU1d : DifferentiableAt ℂ (U1 m n ra rb rab r0) x :=
      (hasDerivAt_U m n ra rb rab r0 hR hAdm hRel x hx').2.differentiableAt
    have hU0d : DifferentiableAt ℂ (U0 m n ra rb rab r0) x :=
      (hasDerivAt_U m n ra rb rab r0 hR hAdm hRel x hx').1.differentiableAt
    have hUnum : DifferentiableAt ℂ
        (fun y : ℂ => U1 m n ra rb rab r0 y - U0 m n ra rb rab r0 y / 2 - bbeta m n ra rb) x :=
      (hU1d.sub (hU0d.div_const 2)).sub_const (bbeta m n ra rb)
    have hden : DifferentiableAt ℂ (fun y : ℂ => y + 1) x := differentiableAt_id.add_const 1
    have hne : x + 1 ≠ 0 := by intro h; exact hx1 (by linear_combination h)
    show DifferentiableWithinAt ℂ
      (fun y : ℂ => (U1 m n ra rb rab r0 y - U0 m n ra rb rab r0 y / 2 - bbeta m n ra rb) / (y + 1))
      (ball (0 : ℂ) (1 / 2)) x
    exact (hUnum.div hden hne).differentiableWithinAt
  have hcomp0 : DifferentiableOn ℂ (fun z => U0 m n ra rb rab r0 (Φ z)) (ball (0 : ℂ) (1 / 1000)) :=
    hU0diff.comp hΦdiff' hΦmaps
  have hcomp1 : DifferentiableOn ℂ (fun z => Vp m n ra rb rab r0 (Φ z)) (ball (0 : ℂ) (1 / 1000)) :=
    hVpdiff.comp hΦdiff' hΦmaps
  constructor
  · -- differentiability on the small disc
    rw [differentiableOn_pi]
    intro i
    fin_cases i
    · show DifferentiableOn ℂ (fun z => Y0v m n ra rb rab r0 Φ z 0) (ball (0 : ℂ) (1 / 1000))
      have hfun : (fun z => Y0v m n ra rb rab r0 Φ z 0) = fun z => U0 m n ra rb rab r0 (Φ z) :=
        funext fun z => Y0v_zero m n ra rb rab r0 Φ z
      rw [hfun]
      exact hcomp0
    · show DifferentiableOn ℂ (fun z => Y0v m n ra rb rab r0 Φ z 1) (ball (0 : ℂ) (1 / 1000))
      have hfun : (fun z => Y0v m n ra rb rab r0 Φ z 1) = fun z => Vp m n ra rb rab r0 (Φ z) :=
        funext fun z => Y0v_one m n ra rb rab r0 Φ z
      rw [hfun]
      exact hcomp1
  · -- the pulled-back system on the annulus
    intro z hzr hz1
    have hzle : ‖z‖ ≤ 1 / 1000 := le_of_lt hz1
    have hzlt1 : ‖z‖ < 1 := by linarith
    have hzmem : z ∈ ball (0 : ℂ) 1 := by rw [mem_ball, dist_zero_right]; exact hzlt1
    have hxle : ‖Φ z‖ ≤ 1 / 50 := hPsmall z hzle
    have hx2 : ‖Φ z‖ < 1 / 2 := by linarith
    have hxne : Φ z ≠ -1 := by intro h; rw [h] at hx2; norm_num at hx2
    have hR2 : R2p m n (Φ z) ≠ 0 :=
      R2p_ne_zero m n ra rb rab r0 hL hN hM hP hAdm hRel Φ hΦeq hΦ0 hzr hzlt1
    have hΦd : HasDerivAt Φ (deriv Φ z) z :=
      (hΦdiff.differentiableAt (isOpen_ball.mem_nhds hzmem)).hasDerivAt
    -- the derivatives of the two components of `Y₀`
    have hd0 : HasDerivAt (fun w => U0 m n ra rb rab r0 (Φ w))
        (U1 m n ra rb rab r0 (Φ z) * deriv Φ z) z :=
      ((hasDerivAt_U m n ra rb rab r0 hR hAdm hRel (Φ z) hx2).1).comp z hΦd
    have hd1 : HasDerivAt (fun w => Vp m n ra rb rab r0 (Φ w))
        ((A21 m n (Φ z) * U0 m n ra rb rab r0 (Φ z) + A22 m n (Φ z) * Vp m n ra rb rab r0 (Φ z)
          + c2 m n ra rb rab (Φ z)) * deriv Φ z) z :=
      (hasDerivAt_Vp m n ra rb rab r0 hR hAdm hRel (Φ z) hx2 hxne hR2).comp z hΦd
    -- the two rows of the system, as stated
    have hval0 : U1 m n ra rb rab r0 (Φ z) * deriv Φ z
        = (∑ j : Fin 2, sysA m n Φ z 0 j * Y0v m n ra rb rab r0 Φ z j)
          + sysb m n ra rb rab Φ z 0 := by
      rw [Fin.sum_univ_two, sysA_00 m n Φ z, sysA_01 m n Φ z, sysb_0 m n ra rb rab Φ z,
        Y0v_zero m n ra rb rab r0 Φ z, Y0v_one m n ra rb rab r0 Φ z,
        U1_eq m n ra rb rab r0 hxne]
      ring
    have hval1 : (A21 m n (Φ z) * U0 m n ra rb rab r0 (Φ z) + A22 m n (Φ z) * Vp m n ra rb rab r0 (Φ z)
          + c2 m n ra rb rab (Φ z)) * deriv Φ z
        = (∑ j : Fin 2, sysA m n Φ z 1 j * Y0v m n ra rb rab r0 Φ z j)
          + sysb m n ra rb rab Φ z 1 := by
      rw [Fin.sum_univ_two, sysA_10 m n Φ z, sysA_11 m n Φ z, sysb_1 m n ra rb rab Φ z,
        Y0v_zero m n ra rb rab r0 Φ z, Y0v_one m n ra rb rab r0 Φ z]
      ring
    refine hasDerivAt_pi.mpr (fun i => ?_)
    fin_cases i
    · show HasDerivAt (fun x => Y0v m n ra rb rab r0 Φ x 0)
        (∑ j : Fin 2, sysA m n Φ z 0 j * Y0v m n ra rb rab r0 Φ z j
          + sysb m n ra rb rab Φ z 0) z
      have hfun : (fun x => Y0v m n ra rb rab r0 Φ x 0) = fun x => U0 m n ra rb rab r0 (Φ x) :=
        funext fun x => Y0v_zero m n ra rb rab r0 Φ x
      rw [hfun]
      exact hd0.congr_deriv hval0
    · show HasDerivAt (fun x => Y0v m n ra rb rab r0 Φ x 1)
        (∑ j : Fin 2, sysA m n Φ z 1 j * Y0v m n ra rb rab r0 Φ z j
          + sysb m n ra rb rab Φ z 1) z
      have hfun : (fun x => Y0v m n ra rb rab r0 Φ x 1) = fun x => Vp m n ra rb rab r0 (Φ x) :=
        funext fun x => Y0v_one m n ra rb rab r0 Φ x
      rw [hfun]
      exact hd1.congr_deriv hval1

end

end Work.CLift
