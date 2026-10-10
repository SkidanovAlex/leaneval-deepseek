import Mathlib
import Submission.Work.MotK.KleinTwRuleMem
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.KleinTwI5
import Submission.Work.MotK.KleinTwPolarLin
import Submission.Work.MotK.TwDataMod5
import Submission.Work.MotK.TwRule.KleinTwSP2Vanishing
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK.TwRule

open Work.MotK

/-- The ruling identity of the T-twisted Crauder--Katz link in the form evaluated on an arbitrary
commutative ring `R`: if `c : Fin 5 → R` lies on the twisted Klein curve (`kleinTwP a b h c = 0`)
and `w = λ·A(c) + μ·B(c)` is a point of the ruling line `ℓ_c` (`kleinTwRulePt`), then the cubic map
`kleinTwR` is projectively constant on `ℓ_c` with value `c`:

  `R_i(w)·c_j = R_j(w)·c_i`.

This is the same argument as the polynomial version `Work.MotK.KleinTwRuleMem`, run directly over
`R` instead of over the polynomial ring `MvPolynomial (Fin 5) K`: the Taylor-coefficient extraction
is carried out in the quotient `R ⧸ (P_0(c), …, P_4(c))`, and the identity `I5` (the second polar
of the twisted secant quintic vanishes on the curve) is supplied by `KleinTwSP2Vanishing`. -/
theorem kleinTwRuleEvalGen {R : Type*} [CommRing R] (a b h l m : R) (c : Fin 5 → R)
    (hc : ∀ k : Fin 5, kleinTwP a b h c k = 0) (i j : Fin 5) :
    kleinTwR a b h (kleinTwRulePt a b h c l m) i * c j
      = kleinTwR a b h (kleinTwRulePt a b h c l m) j * c i := by
  -- the direction vector `u = l • u₁ + m • u₂`
  set u : Fin 5 → R := fun t => l * kleinTwTan a b h c 1 t + m * kleinTwTan a b h c 2 t with hu
  -- the ruled point is the polar of `P` in the direction `u`
  have hw : kleinTwRulePt a b h c l m = kleinTwPolarP a b h c u := by
    funext t
    show l * kleinTwRuleA a b h c t + m * kleinTwRuleB a b h c t = kleinTwPolarP a b h c u t
    rw [hu]
    simp only [kleinTwRuleA, kleinTwRuleB]
    exact (congrFun (KleinTwPolarLin a b h c (kleinTwTan a b h c 1) (kleinTwTan a b h c 2)
      l m) t).symm
  -- the ideal of the twisted Klein curve through `c`, and the quotient ring
  let J : Ideal R := Ideal.span (Set.range (fun k : Fin 5 => kleinTwP a b h c k))
  have hp : ∀ k : Fin 5, kleinTwP a b h c k ∈ J := fun k => Ideal.subset_span ⟨k, rfl⟩
  let S := R ⧸ J
  let π : R →+* S := Ideal.Quotient.mk J
  have hπ : ∀ k : Fin 5, π (kleinTwP a b h c k) = 0 :=
    fun k => Ideal.Quotient.eq_zero_iff_mem.mpr (hp k)
  -- the data in the polynomial ring over the quotient
  let aP : Polynomial S := Polynomial.C (π a)
  let bP : Polynomial S := Polynomial.C (π b)
  let hP : Polynomial S := Polynomial.C (π h)
  let cS : Fin 5 → Polynomial S := fun t => Polynomial.C (π (c t))
  let uS : Fin 5 → Polynomial S := fun t => Polynomial.C (π (u t))
  let V0 : Fin 5 → R := kleinTwPolarP a b h c u
  let V1 : Fin 5 → R := kleinTwP a b h u
  let VS : Fin 5 → Polynomial S := fun k =>
    Polynomial.C (π (V0 k)) + Polynomial.X * Polynomial.C (π (V1 k))
  -- `P (c + T u) = T • (V0 + T • V1)`
  have hPxS : (fun k => kleinTwP aP bP hP (fun t => cS t + Polynomial.X * uS t) k)
      = fun k => Polynomial.X * VS k := by
    funext k
    rw [KleinTwPAddSmul aP bP hP cS uS Polynomial.X]
    show kleinTwP aP bP hP cS k + Polynomial.X * kleinTwPolarP aP bP hP cS uS k
        + Polynomial.X ^ 2 * kleinTwP aP bP hP uS k = Polynomial.X * VS k
    have h0 : kleinTwP aP bP hP cS k = 0 := by
      dsimp only [aP, bP, hP, cS]
      rw [kleinTwP_C_map π a b h c k]
      rw [hπ k, map_zero]
    have h2 : kleinTwPolarP aP bP hP cS uS k = Polynomial.C (π (V0 k)) := by
      dsimp only [aP, bP, hP, cS, uS, V0]
      rw [kleinTwPolarP_C_map π a b h c u k]
    have h3 : kleinTwP aP bP hP uS k = Polynomial.C (π (V1 k)) := by
      dsimp only [aP, bP, hP, uS, V1]
      rw [kleinTwP_C_map π a b h u k]
    rw [h0, h2, h3]
    first | refl_ring1 | ring
  -- I1' applied to the deformed point, and homogeneity
  have hI1 : ∀ t : Fin 5,
      kleinTwR aP bP hP (fun k => Polynomial.X * VS k) t
      = kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)
        * (cS t + Polynomial.X * uS t) := by
    intro t
    rw [← hPxS]
    exact KleinTwI1 aP bP hP (fun s => cS s + Polynomial.X * uS s) t
  have hhom : ∀ t : Fin 5,
      kleinTwR aP bP hP (fun k => Polynomial.X * VS k) t
      = Polynomial.X ^ 3 * kleinTwR aP bP hP VS t := by
    intro t
    exact congrFun (kleinTwR_homog aP bP hP Polynomial.X VS) t
  -- coefficient of `T^3`
  have hkey : ∀ t : Fin 5,
      π (kleinTwR a b h V0 t) = π (kleinTwSP3 a b h c u) * π (c t) := by
    intro t
    have hmain : Polynomial.X ^ 3 * kleinTwR aP bP hP VS t
        = kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)
          * (cS t + Polynomial.X * uS t) := by
      rw [← hhom t, hI1 t]
    have hL : (Polynomial.X ^ 3 * kleinTwR aP bP hP VS t).coeff 3
        = π (kleinTwR a b h V0 t) := by
      have e1 : (Polynomial.X ^ 3 * kleinTwR aP bP hP VS t).coeff 3
          = (kleinTwR aP bP hP VS t).coeff 0 := by
        rw [show (3 : ℕ) = 0 + 3 from (zero_add 3).symm, Polynomial.coeff_X_pow_mul]
      have e2 : (kleinTwR aP bP hP VS t).coeff 0
          = Polynomial.constantCoeff (kleinTwR aP bP hP VS t) := by
        rw [← Polynomial.constantCoeff_apply]
      have e3 : Polynomial.constantCoeff (kleinTwR aP bP hP VS t)
          = π (kleinTwR a b h V0 t) := by
        rw [congrFun (KleinTwRMap (Polynomial.constantCoeff) aP bP hP VS) t]
        have ha : Polynomial.constantCoeff aP = π a := by
          dsimp only [aP]
          rw [Polynomial.constantCoeff_apply, Polynomial.coeff_C]
          norm_num
        have hb : Polynomial.constantCoeff bP = π b := by
          dsimp only [bP]
          rw [Polynomial.constantCoeff_apply, Polynomial.coeff_C]
          norm_num
        have hh : Polynomial.constantCoeff hP = π h := by
          dsimp only [hP]
          rw [Polynomial.constantCoeff_apply, Polynomial.coeff_C]
          norm_num
        have hVS : ∀ k : Fin 5, Polynomial.constantCoeff (VS k) = π (V0 k) := by
          intro k
          dsimp only [VS]
          rw [Polynomial.constantCoeff_apply, coeff_zero_C_add_X_mul]
        rw [ha, hb, hh,
          show (fun k => Polynomial.constantCoeff (VS k)) = (fun k => π (V0 k)) from
            funext hVS,
          ← KleinTwRMap π a b h V0]
      exact e1.trans (e2.trans e3)
    have hR : (kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)
          * (cS t + Polynomial.X * uS t)).coeff 3
        = (kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)).coeff 3
            * π (c t)
          + (kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)).coeff 2
            * π (u t) := by
      have e1 : kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)
            * (cS t + Polynomial.X * uS t)
          = kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)
              * Polynomial.C (π (c t))
            + (kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s) * Polynomial.X)
              * Polynomial.C (π (u t)) := by
        dsimp only [cS, uS]
        first | refl_ring1 | ring
      rw [e1, Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_mul_C,
        show (3 : ℕ) = 2 + 1 from rfl, Polynomial.coeff_mul_X]
    have h3 : (kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)).coeff 3
        = π (kleinTwSP3 a b h c u) := by
      rw [show kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)
          = kleinTwS (Polynomial.C (π a))
              (Polynomial.C (π b)) (Polynomial.C (π h))
              (fun s => Polynomial.C (π (c s))
                + Polynomial.X * Polynomial.C (π (u s)))
          from rfl,
        kleinTwS_coeff_three (π a) (π b) (π h)
          (fun s => π (c s)) (fun s => π (u s)),
        ← kleinTwSP3_map π a b h c u]
    have h2 : (kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)).coeff 2 = 0 := by
      rw [show kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)
          = kleinTwS (Polynomial.C (π a))
              (Polynomial.C (π b)) (Polynomial.C (π h))
              (fun s => Polynomial.C (π (c s))
                + Polynomial.X * Polynomial.C (π (u s)))
          from rfl,
        kleinTwS_coeff_two (π a) (π b) (π h)
          (fun s => π (c s)) (fun s => π (u s)),
        ← kleinTwSP2_map π a b h c u,
        show π (kleinTwSP2 a b h c u) = 0 from by
          rw [KleinTwSP2Vanishing a b h c u hc, map_zero]]
    have hc3 := congrArg (fun p : Polynomial S => p.coeff 3) hmain
    rw [hL, hR, h3, h2] at hc3
    simpa only [zero_mul, add_zero] using hc3
  -- assemble
  have hassemble : π (kleinTwR a b h (kleinTwRulePt a b h c l m) i * c j
      - kleinTwR a b h (kleinTwRulePt a b h c l m) j * c i) = 0 := by
    rw [hw]
    change π (kleinTwR a b h V0 i * c j - kleinTwR a b h V0 j * c i) = 0
    simp only [map_sub, map_mul]
    rw [hkey i, hkey j]
    first | refl_ring1 | ring
  -- the ideal is generated by the vanishing quadrics, hence is `⊥`
  have hJ : J ≤ ⊥ := Ideal.span_le.mpr (by
    rintro y ⟨k, rfl⟩
    change kleinTwP a b h c k ∈ (⊥ : Ideal R)
    rw [hc k]
    exact Submodule.zero_mem _)
  have hmem : kleinTwR a b h (kleinTwRulePt a b h c l m) i * c j
      - kleinTwR a b h (kleinTwRulePt a b h c l m) j * c i ∈ J :=
    Ideal.Quotient.eq_zero_iff_mem.mp hassemble
  have hzero : kleinTwR a b h (kleinTwRulePt a b h c l m) i * c j
      - kleinTwR a b h (kleinTwRulePt a b h c l m) j * c i = 0 := by
    simpa using hJ hmem
  exact sub_eq_zero.mp hzero

theorem KleinTwRuleEval (K : Type) [Field K] (A : Type) [CommRing A] [Algebra K A]
    (a b h : K) (l m : A) (c : Fin 5 → A)
    (hc : ∀ k : Fin 5, Work.MotK.kleinTwP (algebraMap K A a) (algebraMap K A b)
      (algebraMap K A h) c k = 0) (i j : Fin 5) :
    Work.MotK.kleinTwR (algebraMap K A a) (algebraMap K A b) (algebraMap K A h)
        (Work.MotK.kleinTwRulePt (algebraMap K A a) (algebraMap K A b) (algebraMap K A h) c l m) i * c j
      = Work.MotK.kleinTwR (algebraMap K A a) (algebraMap K A b) (algebraMap K A h)
        (Work.MotK.kleinTwRulePt (algebraMap K A a) (algebraMap K A b) (algebraMap K A h) c l m) j * c i :=
  kleinTwRuleEvalGen (algebraMap K A a) (algebraMap K A b) (algebraMap K A h) l m c hc i j

end Work.MotK.TwRule
