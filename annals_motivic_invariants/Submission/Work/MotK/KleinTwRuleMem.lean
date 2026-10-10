/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Mathlib
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.KleinTwI1
import Submission.Work.MotK.TwDataMod5
import Submission.Work.MotK.KleinTwPolar
import Submission.Work.MotK.KleinTwI5
import Submission.Work.MotK.KleinTwPAddSmul
import Submission.Work.MotK.KleinTwPolarLin
import Submission.Work.MotK.KleinTwPMapApply
import Submission.Work.MotK.KleinTwRMap
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The ruling identity of the T-twisted Crauder--Katz link

For `c` in the twisted Klein curve `C = V(P_0, …, P_4)` (`P_k = kleinTwP k`, the Kummer twists of
the Pfaffian quadrics) and `w = λ·A(c) + μ·B(c)` a point of the ruling line `ℓ_c`
(`kleinTwRulePt` of `Submission/Work/MotK/TwRule.lean`, built from the polar of the quadratic map
`P = kleinTwP` along the tangent vectors of the T-invariant quadric `kleinTwQ = kleinTwP0`), the
cubic map `R = kleinTwR` is projectively constant on `ℓ_c` with value `c`:

  `R_i(w)·c_j − R_j(w)·c_i ∈ (P_0, …, P_4)`   for all `i, j`.

This is the T-twist analogue of the proved split identity
`Work.MotK.CensusFibre.ruling_mem` (`Submission/Work/MotK/CensusFibre/ruling_mem.lean`), and — via
the inverse relation I2' `kleinTwP (kleinTwR w) = kleinTwSDualInv w • w` — it shows that the ruling
line `ℓ_c` lies in the target-side ruling divisor `{kleinTwSDualInv = 0}` of the census
(`AUDIT_LinkCertT.md` §8.2, claim (R1)).

## The proof

It is the *structural* route of the split case (there, `GUIDE_K5K6.md` §3), with the twisted data
throughout:

* `w = dP_c(u)` is the polar of the quadratic map `P = kleinTwP` at `c` in the direction
  `u = λ u_1 + μ u_2` (`KleinTwPolarLin`);
* the *Taylor identity* — I1' (`KleinTwI1`) applied to the deformed point `c + T • u`, using
  quadraticity (`KleinTwPAddSmul`) and homogeneity (`kleinTwR_homog`) — gives, in the quotient
  `(K[X]/J)[T]` with `J = (P_0, …, P_4)`, that
  `T³ • R(dP_c u + T P u) = s (c + T u) • (c + T u)`;
* extracting the coefficient of `T³` (`kleinTwS_polar`, `kleinTwS_coeff_two`,
  `kleinTwS_coeff_three`) gives
  `R_i(dP_c u) = S_3(c,u)·c_i + S_2(c,u)·u_i`, where `S_j` are the polars of the twisted secant
  quintic `kleinTwS`;
* `S_2` lies in `J` (`kleinTwSP2_mem`, the twisted identity **I5**: the twisted secant surface has
  multiplicity `≥ 3` along `C`), so `R_i(dP_c u) ≡ S_3(c,u)·c_i (mod J)` and the ruling identity
  follows.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK

variable {R : Type*} [CommRing R]

/-- Naturality of the polarisation `kleinTwPolarP` of the quadratic twisted Pfaffian map. -/
theorem kleinTwPolarP_map_apply {S : Type*} [CommRing S] (φ : R →+* S) (a b h : R)
    (x y : Fin 5 → R) (k : Fin 5) :
    φ (kleinTwPolarP a b h x y k)
      = kleinTwPolarP (φ a) (φ b) (φ h) (fun i => φ (x i)) (fun i => φ (y i)) k := by
  have h1 : (fun i => φ ((x + y) i)) = (fun i => φ (x i)) + (fun i => φ (y i)) := by
    funext i; simp only [Pi.add_apply, map_add]
  simp only [kleinTwPolarP]
  rw [map_sub, map_sub, KleinTwPMapApply, h1, KleinTwPMapApply, KleinTwPMapApply]

/-- Naturality of `kleinTwP` for the ring hom `Polynomial.C ∘ π` (the form in which the
coefficient extraction in the quotient ring uses it). -/
theorem kleinTwP_C_map {R T : Type*} [CommRing R] [CommRing T] (π : R →+* T) (a b h : R)
    (x : Fin 5 → R) (k : Fin 5) :
    kleinTwP (Polynomial.C (π a)) (Polynomial.C (π b)) (Polynomial.C (π h))
        (fun t => Polynomial.C (π (x t))) k = Polynomial.C (π (kleinTwP a b h x k)) := by
  rw [show Polynomial.C (π (kleinTwP a b h x k)) =
        (Polynomial.C.comp π) (kleinTwP a b h x k) from rfl]
  rw [KleinTwPMapApply (Polynomial.C.comp π) a b h x k]
  rfl

/-- Naturality of the polarisation `kleinTwPolarP` for the ring hom `Polynomial.C ∘ π`. -/
theorem kleinTwPolarP_C_map {R T : Type*} [CommRing R] [CommRing T] (π : R →+* T) (a b h : R)
    (x y : Fin 5 → R) (k : Fin 5) :
    kleinTwPolarP (Polynomial.C (π a)) (Polynomial.C (π b)) (Polynomial.C (π h))
        (fun t => Polynomial.C (π (x t))) (fun t => Polynomial.C (π (y t))) k
      = Polynomial.C (π (kleinTwPolarP a b h x y k)) := by
  rw [show Polynomial.C (π (kleinTwPolarP a b h x y k)) =
        (Polynomial.C.comp π) (kleinTwPolarP a b h x y k) from rfl]
  rw [kleinTwPolarP_map_apply (Polynomial.C.comp π) a b h x y k]
  rfl

/-- The coefficient of `T^2` of `kleinTwS (c + T • u)` is the second polar `kleinTwSP2`. -/
theorem kleinTwS_coeff_two (a b h : R) (c u : Fin 5 → R) :
    (kleinTwS (Polynomial.C a) (Polynomial.C b) (Polynomial.C h)
      (fun i => Polynomial.C (c i) + Polynomial.X * Polynomial.C (u i))).coeff 2
      = kleinTwSP2 a b h c u := by
  rw [kleinTwS_polar (Polynomial.C a) (Polynomial.C b) (Polynomial.C h)
      (fun i => Polynomial.C (c i)) (fun i => Polynomial.C (u i)) Polynomial.X,
    ← kleinTwSP0_map (Polynomial.C (R := R)) a b h c u,
    ← kleinTwSP1_map (Polynomial.C (R := R)) a b h c u,
    ← kleinTwSP2_map (Polynomial.C (R := R)) a b h c u,
    ← kleinTwSP3_map (Polynomial.C (R := R)) a b h c u,
    ← kleinTwSP4_map (Polynomial.C (R := R)) a b h c u,
    ← kleinTwSP5_map (Polynomial.C (R := R)) a b h c u]
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', Polynomial.coeff_C]
  norm_num

/-- The coefficient of `T^3` of `kleinTwS (c + T • u)` is the third polar `kleinTwSP3`. -/
theorem kleinTwS_coeff_three (a b h : R) (c u : Fin 5 → R) :
    (kleinTwS (Polynomial.C a) (Polynomial.C b) (Polynomial.C h)
      (fun i => Polynomial.C (c i) + Polynomial.X * Polynomial.C (u i))).coeff 3
      = kleinTwSP3 a b h c u := by
  rw [kleinTwS_polar (Polynomial.C a) (Polynomial.C b) (Polynomial.C h)
      (fun i => Polynomial.C (c i)) (fun i => Polynomial.C (u i)) Polynomial.X,
    ← kleinTwSP0_map (Polynomial.C (R := R)) a b h c u,
    ← kleinTwSP1_map (Polynomial.C (R := R)) a b h c u,
    ← kleinTwSP2_map (Polynomial.C (R := R)) a b h c u,
    ← kleinTwSP3_map (Polynomial.C (R := R)) a b h c u,
    ← kleinTwSP4_map (Polynomial.C (R := R)) a b h c u,
    ← kleinTwSP5_map (Polynomial.C (R := R)) a b h c u]
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', Polynomial.coeff_C]
  norm_num

/-- The constant coefficient of `C x + X * C y` is `x`. -/
theorem coeff_zero_C_add_X_mul (S : Type*) [CommRing S] (x y : S) :
    (Polynomial.C x + Polynomial.X * Polynomial.C y).coeff 0 = x := by
  simp

/-- **The ruling identity of the T-twisted link** (claim (R1) of `AUDIT_LinkCertT.md` §8.2).

Let `A(c) = dP_c(u₁)`, `B(c) = dP_c(u₂)` be the ruling vectors of
`Submission/Work/MotK/TwRule.lean` (built from the polar `kleinTwBilin` of the T-invariant quadric
`kleinTwQ = kleinTwP0`) and `w = λ·A(c) + μ·B(c)` a point of the ruling line `ℓ_c`.  Then for every
`c ∈ C = V(P₀,…,P₄)` the cubic map `R = kleinTwR` is projectively constant on `ℓ_c` with value `c`:

  `R_i(w)·c_j − R_j(w)·c_i = 0`  for all `i, j`  whenever  `P₀(c) = … = P₄(c) = 0`,

i.e. the polynomial `R_i(w)c_j − R_j(w)c_i` lies in the ideal `(P₀,…,P₄)` generated by the five
twisted quadrics in the coordinates `c`.  Consequently `ℓ_c` is contained in the fibre of `R` over
`c`, and hence — by I2' (`KleinTwI2inv`: `P_i(R(z)) = kleinTwSDualInv(z)·z_i`) — in the ruling
divisor `{kleinTwSDualInv = 0}` of the census. -/
theorem KleinTwRuleMem {K : Type} [Field K] (a b h l m : K) (i j : Fin 5) :
    Work.MotK.kleinTwR (MvPolynomial.C a : MvPolynomial (Fin 5) K) (MvPolynomial.C b)
        (MvPolynomial.C h)
        (Work.MotK.kleinTwRulePt (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun t => MvPolynomial.X t) (MvPolynomial.C l) (MvPolynomial.C m)) i
      * MvPolynomial.X j
      - Work.MotK.kleinTwR (MvPolynomial.C a : MvPolynomial (Fin 5) K) (MvPolynomial.C b)
        (MvPolynomial.C h)
        (Work.MotK.kleinTwRulePt (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun t => MvPolynomial.X t) (MvPolynomial.C l) (MvPolynomial.C m)) j
      * MvPolynomial.X i
    ∈ Ideal.span (Set.range (fun k : Fin 5 =>
        Work.MotK.kleinTwP (MvPolynomial.C a : MvPolynomial (Fin 5) K) (MvPolynomial.C b)
          (MvPolynomial.C h) (fun t => MvPolynomial.X t) k)) := by
  -- the direction vector `u = l • u₁ + m • u₂`
  set u : Fin 5 → MvPolynomial (Fin 5) K := fun t =>
    MvPolynomial.C l * kleinTwTan (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun s => MvPolynomial.X s) 1 t
      + MvPolynomial.C m * kleinTwTan (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun s => MvPolynomial.X s) 2 t with hu
  -- the ruled point is the polar of `P` in the direction `u`
  have hw : kleinTwRulePt (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun t => MvPolynomial.X t) (MvPolynomial.C l) (MvPolynomial.C m)
      = kleinTwPolarP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun t => MvPolynomial.X t) u := by
    funext t
    simp only [kleinTwRulePt, hu]
    rw [KleinTwPolarLin (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (fun s => MvPolynomial.X s)
      (kleinTwTan (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun s => MvPolynomial.X s) 1)
      (kleinTwTan (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun s => MvPolynomial.X s) 2)
      (MvPolynomial.C l) (MvPolynomial.C m)]
    simp only [kleinTwRuleA, kleinTwRuleB]
  -- the ideal of the twisted Klein curve and the quotient ring
  let J : Ideal (MvPolynomial (Fin 5) K) := kleinTwCurveIdeal K a b h
  have hp : ∀ k : Fin 5,
      kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun t => MvPolynomial.X t) k ∈ J :=
    fun k => Ideal.subset_span ⟨k, rfl⟩
  let S := MvPolynomial (Fin 5) K ⧸ J
  let π : MvPolynomial (Fin 5) K →+* S := Ideal.Quotient.mk J
  have hπ : ∀ k : Fin 5,
      π (kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun t => MvPolynomial.X t) k) = 0 :=
    fun k => Ideal.Quotient.eq_zero_iff_mem.mpr (hp k)
  -- the data in the polynomial ring over the quotient
  let aP : Polynomial S := Polynomial.C (π (MvPolynomial.C a))
  let bP : Polynomial S := Polynomial.C (π (MvPolynomial.C b))
  let hP : Polynomial S := Polynomial.C (π (MvPolynomial.C h))
  let cS : Fin 5 → Polynomial S := fun t => Polynomial.C (π (MvPolynomial.X t))
  let uS : Fin 5 → Polynomial S := fun t => Polynomial.C (π (u t))
  let V0 : Fin 5 → MvPolynomial (Fin 5) K :=
    kleinTwPolarP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
      (fun t => MvPolynomial.X t) u
  let V1 : Fin 5 → MvPolynomial (Fin 5) K :=
    kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) u
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
      rw [kleinTwP_C_map π (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun t => MvPolynomial.X t) k]
      rw [hπ k, map_zero]
    have h2 : kleinTwPolarP aP bP hP cS uS k = Polynomial.C (π (V0 k)) := by
      dsimp only [aP, bP, hP, cS, uS, V0]
      rw [kleinTwPolarP_C_map π (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (fun t => MvPolynomial.X t) u k]
    have h3 : kleinTwP aP bP hP uS k = Polynomial.C (π (V1 k)) := by
      dsimp only [aP, bP, hP, uS, V1]
      rw [kleinTwP_C_map π (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) u k]
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
      π (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) V0 t)
      = π (kleinTwSP3 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun s => MvPolynomial.X s) u)
        * π (MvPolynomial.X t) := by
    intro t
    have hmain : Polynomial.X ^ 3 * kleinTwR aP bP hP VS t
        = kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)
          * (cS t + Polynomial.X * uS t) := by
      rw [← hhom t, hI1 t]
    have hL : (Polynomial.X ^ 3 * kleinTwR aP bP hP VS t).coeff 3
        = π (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) V0 t) := by
      have e1 : (Polynomial.X ^ 3 * kleinTwR aP bP hP VS t).coeff 3
          = (kleinTwR aP bP hP VS t).coeff 0 := by
        rw [show (3 : ℕ) = 0 + 3 from (zero_add 3).symm, Polynomial.coeff_X_pow_mul]
      have e2 : (kleinTwR aP bP hP VS t).coeff 0
          = Polynomial.constantCoeff (kleinTwR aP bP hP VS t) := by
        rw [← Polynomial.constantCoeff_apply]
      have e3 : Polynomial.constantCoeff (kleinTwR aP bP hP VS t)
          = π (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) V0 t) := by
        rw [congrFun (KleinTwRMap (Polynomial.constantCoeff) aP bP hP VS) t]
        have ha : Polynomial.constantCoeff aP = π (MvPolynomial.C a) := by
          dsimp only [aP]
          rw [Polynomial.constantCoeff_apply, Polynomial.coeff_C]
          norm_num
        have hb : Polynomial.constantCoeff bP = π (MvPolynomial.C b) := by
          dsimp only [bP]
          rw [Polynomial.constantCoeff_apply, Polynomial.coeff_C]
          norm_num
        have hh : Polynomial.constantCoeff hP = π (MvPolynomial.C h) := by
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
          ← KleinTwRMap π (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) V0]
      exact e1.trans (e2.trans e3)
    have hR : (kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)
          * (cS t + Polynomial.X * uS t)).coeff 3
        = (kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)).coeff 3
            * π (MvPolynomial.X t)
          + (kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)).coeff 2
            * π (u t) := by
      have e1 : kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)
            * (cS t + Polynomial.X * uS t)
          = kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)
              * Polynomial.C (π (MvPolynomial.X t))
            + (kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s) * Polynomial.X)
              * Polynomial.C (π (u t)) := by
        dsimp only [cS, uS]
        first | refl_ring1 | ring
      rw [e1, Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_mul_C,
        show (3 : ℕ) = 2 + 1 from rfl, Polynomial.coeff_mul_X]
    have h3 : (kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)).coeff 3
        = π (kleinTwSP3 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (fun s => MvPolynomial.X s) u) := by
      rw [show kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)
          = kleinTwS (Polynomial.C (π (MvPolynomial.C a)))
              (Polynomial.C (π (MvPolynomial.C b))) (Polynomial.C (π (MvPolynomial.C h)))
              (fun s => Polynomial.C (π (MvPolynomial.X s))
                + Polynomial.X * Polynomial.C (π (u s)))
          from rfl,
        kleinTwS_coeff_three (π (MvPolynomial.C a)) (π (MvPolynomial.C b)) (π (MvPolynomial.C h))
          (fun s => π (MvPolynomial.X s)) (fun s => π (u s)),
        ← kleinTwSP3_map π (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun s => MvPolynomial.X s) u]
    have h2 : (kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)).coeff 2 = 0 := by
      rw [show kleinTwS aP bP hP (fun s => cS s + Polynomial.X * uS s)
          = kleinTwS (Polynomial.C (π (MvPolynomial.C a)))
              (Polynomial.C (π (MvPolynomial.C b))) (Polynomial.C (π (MvPolynomial.C h)))
              (fun s => Polynomial.C (π (MvPolynomial.X s))
                + Polynomial.X * Polynomial.C (π (u s)))
          from rfl,
        kleinTwS_coeff_two (π (MvPolynomial.C a)) (π (MvPolynomial.C b)) (π (MvPolynomial.C h))
          (fun s => π (MvPolynomial.X s)) (fun s => π (u s)),
        ← kleinTwSP2_map π (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun s => MvPolynomial.X s) u,
        show π (kleinTwSP2 (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
            (fun s => MvPolynomial.X s) u) = 0
          from Ideal.Quotient.eq_zero_iff_mem.mpr (kleinTwSP2_mem K u)]
    have hc := congrArg (fun p : Polynomial S => p.coeff 3) hmain
    rw [hL, hR, h3, h2] at hc
    simpa only [zero_mul, add_zero] using hc
  -- assemble
  have hassemble : π (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (kleinTwRulePt (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun t => MvPolynomial.X t) (MvPolynomial.C l) (MvPolynomial.C m)) i * MvPolynomial.X j
      - kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
        (kleinTwRulePt (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h)
          (fun t => MvPolynomial.X t) (MvPolynomial.C l) (MvPolynomial.C m)) j
        * MvPolynomial.X i) = 0 := by
    rw [hw]
    change π (kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) V0 i
        * MvPolynomial.X j
      - kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) V0 j
        * MvPolynomial.X i) = 0
    simp only [map_sub, map_mul]
    rw [hkey i, hkey j]
    first | refl_ring1 | ring
  exact Ideal.Quotient.eq_zero_iff_mem.mp hassemble

end Work.MotK
