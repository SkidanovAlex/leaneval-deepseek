import Mathlib
import Submission.Work.MotK.CensusFibre.ruling_mem
import Submission.Work.MotK.KleinI4
import Submission.Work.MotK.KleinIdents
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
set_option linter.unusedSimpArgs false

namespace Work.MotAS

open Work.MotK

/-! ## The split analogue of `KleinTwSP2Vanishing`

The second polar `kleinSecP2` of the secant quintic is the quadratic form in `u`

  `kleinSecP2 = ∑_i kleinSecD i · u_i² + ∑_{i<j} kleinSecDD_{ij} · u_i u_j`,

and each of the fifteen coefficients lies in the ideal `(p₀, …, p₄)` of the split Klein curve —
identity **I5** (`Work.MotK.CensusFibre.sec_p2_mem`,
`Submission/Work/MotK/CensusFibre/sec_p2_mem.lean`).  Hence `kleinSecP2 a b c u = 0` whenever
`kleinP a b c = 0`.

This is the split analogue of `Work.MotK.TwRule.KleinTwSP2Vanishing`
(`Submission/Work/MotK/TwRule/KleinTwSP2Vanishing.lean`), with the twisted certificates replaced
by the split ones: `Work.MotK.CensusFibre.kleinSecP2_eq`
(`Submission/Work/MotK/CensusFibre/sec_p2_mem.lean`), `Work.MotK.kleinSecD0_eq … kleinSecD4_eq`
(`Submission/Work/MotK/CensusFibre/SecPolarDefs.lean`) and `Work.MotK.kleinSecDD_01_eq …
kleinSecDD_34_eq` (`Submission/Work/MotK/KleinI5.lean`). -/
theorem sec_p2_vanish {R : Type*} [CommRing R] (a b : R) (c u : Fin 5 → R)
    (hc : ∀ k : Fin 5, Work.MotK.kleinP a b c k = 0) :
    Work.MotK.kleinSecP2 a b c u = 0 := by
  have h0 : kleinP0 a b c = 0 := hc 0
  have h1 : kleinP1 a b c = 0 := hc 1
  have h2 : kleinP2 a b c = 0 := hc 2
  have h3 : kleinP3 a b c = 0 := hc 3
  have h4 : kleinP4 a b c = 0 := hc 4
  rw [Work.MotK.CensusFibre.kleinSecP2_eq, kleinSecD0_eq, kleinSecD1_eq, kleinSecD2_eq,
    kleinSecD3_eq, kleinSecD4_eq,
    kleinSecDD_01_eq, kleinSecDD_02_eq, kleinSecDD_03_eq, kleinSecDD_04_eq, kleinSecDD_12_eq,
    kleinSecDD_13_eq, kleinSecDD_14_eq, kleinSecDD_23_eq, kleinSecDD_24_eq, kleinSecDD_34_eq]
  simp only [h0, h1, h2, h3, h4, mul_zero, zero_mul, zero_add, add_zero]

/-- **The G-side ruling identity of the Crauder–Katz link in general-direction, evaluated form.**

For `c` on the split Klein curve `C = V(p₀,…,p₄)` (`kleinP a b c k = 0`, `k = 0..4`) and *any*
direction vector `u`, the cubic map `R = kleinR a b` is projectively constant on the polar point
`dP_c(u) = kleinPolarP a b c u` with value `c`:

  `R_i(dP_c u)·c_j = R_j(dP_c u)·c_i`.

This is the *evaluated* form of `Work.MotK.CensusFibre.ruling_mem`
(`Submission/Work/MotK/CensusFibre/ruling_mem.lean`, proved), which states the *same* identity for
the *specific* ruling directions `u = l·u₁ + m·u₂` and only as a membership in the ideal of the
curve in `MvPolynomial (Fin 5) K`; here the ring is an arbitrary commutative ring `R` and the
direction `u` is arbitrary (which is what a transport from the split model to another model of the
curve needs, because the transported direction is an arbitrary vector).

Route: copy the proof of `Work.MotK.TwRule.kleinTwRuleEvalGen`
(`Submission/Work/MotK/TwRule/KleinTwRuleEval.lean`, proved) and replace the twisted data by the
split data (`kleinTwP → kleinP`, `kleinTwR → kleinR`, `kleinTwS → kleinSec`,
`kleinTwTan → kleinTan`, `KleinTwPAddSmul → KleinP_add_smul`,
`kleinTwS_coeff_two/three → kleinSec_coeff_two/three`, `kleinTwR_homog → kleinR_homog`,
`KleinTwRMap → kleinR_map`, `kleinTwPolarP_map_apply → kleinPolarP_map_apply`,
`kleinTwP_C_map → kleinP_map_apply`, `coeff_zero_C_add_X_mul` as is, all in `Work.MotK`), and
replace `KleinTwSP2Vanishing` by the split analogue `sec_p2_vanish` (which you must prove as a
helper in the same file by copying `Submission/Work/MotK/TwRule/KleinTwSP2Vanishing.lean` verbatim
with the *split* certificates `Work.MotK.kleinSecP2_eq`
(`Submission/Work/MotK/CensusFibre/sec_p2_mem.lean`), `Work.MotK.kleinSecD0_eq … kleinSecD4_eq`
(`Submission/Work/MotK/CensusFibre/SecPolarDefs.lean`) and
`Work.MotK.kleinSecDD_01_eq … kleinSecDD_34_eq` (`Submission/Work/MotK/KleinI5.lean`) — all of
them are `ring` certificates over an arbitrary `CommRing`).

The proof of `kleinTwRuleEvalGen` never uses the special form of the direction `u`: it only sets
`V0 := dP_c u`, `V1 := P u`, works in `(R ⧸ (P₀(c),…,P₄(c)))[T]`, applies I1
(`kleinR_kleinP`) to `c + T·u`, extracts the `T³` coefficient with
`kleinSec_coeff_two/three`, and kills the `T²` term with the I5 vanishing. -/
theorem splitRuleEvalGen {R : Type*} [CommRing R] (a b : R) (c u : Fin 5 → R)
    (hc : ∀ k : Fin 5, Work.MotK.kleinP a b c k = 0) (i j : Fin 5) :
    Work.MotK.kleinR a b (Work.MotK.kleinPolarP a b c u) i * c j
      = Work.MotK.kleinR a b (Work.MotK.kleinPolarP a b c u) j * c i := by
  -- the ideal of the Klein curve through `c`, and the quotient ring
  let J : Ideal R := Ideal.span (Set.range (fun k : Fin 5 => kleinP a b c k))
  have hp : ∀ k : Fin 5, kleinP a b c k ∈ J := fun k => Ideal.subset_span ⟨k, rfl⟩
  let S := R ⧸ J
  let π : R →+* S := Ideal.Quotient.mk J
  have hπ : ∀ k : Fin 5, π (kleinP a b c k) = 0 :=
    fun k => Ideal.Quotient.eq_zero_iff_mem.mpr (hp k)
  -- the data in the polynomial ring over the quotient
  let aP : Polynomial S := Polynomial.C (π a)
  let bP : Polynomial S := Polynomial.C (π b)
  let cS : Fin 5 → Polynomial S := fun t => Polynomial.C (π (c t))
  let uS : Fin 5 → Polynomial S := fun t => Polynomial.C (π (u t))
  let V0 : Fin 5 → R := kleinPolarP a b c u
  let V1 : Fin 5 → R := kleinP a b u
  let VS : Fin 5 → Polynomial S := fun k =>
    Polynomial.C (π (V0 k)) + Polynomial.X * Polynomial.C (π (V1 k))
  -- `P (c + T u) = T • (V0 + T • V1)`
  have hPxS : (fun k => kleinP aP bP (fun t => cS t + Polynomial.X * uS t) k)
      = fun k => Polynomial.X * VS k := by
    funext k
    rw [Work.MotK.CensusFibre.kleinP_add_smul (R := Polynomial S) aP bP cS uS Polynomial.X]
    change kleinP aP bP cS k + Polynomial.X * kleinPolarP aP bP cS uS k
        + Polynomial.X ^ 2 * kleinP aP bP uS k = Polynomial.X * VS k
    have h0 : kleinP aP bP cS k = 0 := by
      rw [show aP = (Polynomial.C.comp π) a from rfl,
        show bP = (Polynomial.C.comp π) b from rfl,
        show cS = (fun t => (Polynomial.C.comp π) (c t)) from rfl,
        ← Work.MotK.CensusFibre.kleinP_map_apply (R := R) (S := Polynomial S)
          (Polynomial.C.comp π) a b c k]
      simp only [RingHom.comp_apply, hπ k, map_zero]
    have h2 : kleinPolarP aP bP cS uS k = Polynomial.C (π (V0 k)) := by
      rw [show aP = (Polynomial.C.comp π) a from rfl,
        show bP = (Polynomial.C.comp π) b from rfl,
        show cS = (fun t => (Polynomial.C.comp π) (c t)) from rfl,
        show uS = (fun t => (Polynomial.C.comp π) (u t)) from rfl,
        ← Work.MotK.CensusFibre.kleinPolarP_map_apply (R := R) (S := Polynomial S)
          (Polynomial.C.comp π) a b c u k]
      rfl
    have h3 : kleinP aP bP uS k = Polynomial.C (π (V1 k)) := by
      rw [show aP = (Polynomial.C.comp π) a from rfl,
        show bP = (Polynomial.C.comp π) b from rfl,
        show uS = (fun t => (Polynomial.C.comp π) (u t)) from rfl,
        ← Work.MotK.CensusFibre.kleinP_map_apply (R := R) (S := Polynomial S)
          (Polynomial.C.comp π) a b u k]
      rfl
    rw [h0, h2, h3]
    first | refl_ring1 | ring
  -- I1 applied to the deformed point, and homogeneity
  have hI1 : ∀ t : Fin 5,
      kleinR aP bP (fun k => Polynomial.X * VS k) t
      = kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)
        * (cS t + Polynomial.X * uS t) := by
    intro t
    rw [← hPxS]
    exact kleinR_kleinP aP bP (fun s => cS s + Polynomial.X * uS s) t
  have hhom : ∀ t : Fin 5,
      kleinR aP bP (fun k => Polynomial.X * VS k) t
      = Polynomial.X ^ 3 * kleinR aP bP VS t := by
    intro t
    exact congrFun (kleinR_homog aP bP Polynomial.X VS) t
  -- coefficient of `T^3`
  have hkey : ∀ t : Fin 5,
      π (kleinR a b V0 t) = π (kleinSecP3 a b c u) * π (c t) := by
    intro t
    have hmain : Polynomial.X ^ 3 * kleinR aP bP VS t
        = kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)
          * (cS t + Polynomial.X * uS t) := by
      rw [← hhom t, hI1 t]
    have hL : (Polynomial.X ^ 3 * kleinR aP bP VS t).coeff 3
        = π (kleinR a b V0 t) := by
      have e1 : (Polynomial.X ^ 3 * kleinR aP bP VS t).coeff 3
          = (kleinR aP bP VS t).coeff 0 := by
        rw [show (3 : ℕ) = 0 + 3 from (zero_add 3).symm, Polynomial.coeff_X_pow_mul]
      have e2 : (kleinR aP bP VS t).coeff 0
          = Polynomial.constantCoeff (kleinR aP bP VS t) := by
        rw [← Polynomial.constantCoeff_apply]
      have e3 : Polynomial.constantCoeff (kleinR aP bP VS t)
          = π (kleinR a b V0 t) := by
        rw [kleinR_map (Polynomial.constantCoeff) aP bP VS t]
        have ha : Polynomial.constantCoeff aP = π a := by
          dsimp only [aP]
          rw [Polynomial.constantCoeff_apply, Polynomial.coeff_C]
          norm_num
        have hb : Polynomial.constantCoeff bP = π b := by
          dsimp only [bP]
          rw [Polynomial.constantCoeff_apply, Polynomial.coeff_C]
          norm_num
        have hVS : ∀ k : Fin 5, Polynomial.constantCoeff (VS k) = π (V0 k) := by
          intro k
          dsimp only [VS]
          rw [Polynomial.constantCoeff_apply, Work.MotK.CensusFibre.coeff_zero_C_add_X_mul]
        rw [ha, hb,
          show (fun k => Polynomial.constantCoeff (VS k)) = (fun k => π (V0 k)) from
            funext hVS,
          ← kleinR_map π a b V0 t]
      exact e1.trans (e2.trans e3)
    have hR : (kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)
          * (cS t + Polynomial.X * uS t)).coeff 3
        = (kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)).coeff 3
            * π (c t)
          + (kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)).coeff 2
            * π (u t) := by
      have e1 : kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)
            * (cS t + Polynomial.X * uS t)
          = kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)
              * Polynomial.C (π (c t))
            + (kleinSec aP bP (fun s => cS s + Polynomial.X * uS s) * Polynomial.X)
              * Polynomial.C (π (u t)) := by
        dsimp only [cS, uS]
        first | refl_ring1 | ring
      rw [e1, Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_mul_C,
        show (3 : ℕ) = 2 + 1 from rfl, Polynomial.coeff_mul_X]
    have h3 : (kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)).coeff 3
        = π (kleinSecP3 a b c u) := by
      rw [show kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)
          = kleinSec (Polynomial.C (π a))
              (Polynomial.C (π b))
              (fun s => Polynomial.C (π (c s))
                + Polynomial.X * Polynomial.C (π (u s)))
          from rfl,
        Work.MotK.CensusFibre.kleinSec_coeff_three (π a) (π b)
          (fun s => π (c s)) (fun s => π (u s)),
        ← kleinSecP3_map (R := R) (S := S) π a b c u]
    have h2 : (kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)).coeff 2 = 0 := by
      rw [show kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)
          = kleinSec (Polynomial.C (π a))
              (Polynomial.C (π b))
              (fun s => Polynomial.C (π (c s))
                + Polynomial.X * Polynomial.C (π (u s)))
          from rfl,
        Work.MotK.CensusFibre.kleinSec_coeff_two (π a) (π b)
          (fun s => π (c s)) (fun s => π (u s)),
        ← kleinSecP2_map (R := R) (S := S) π a b c u,
        show π (kleinSecP2 a b c u) = 0 from by
          rw [sec_p2_vanish a b c u hc, map_zero]]
    have hc3 := congrArg (fun p : Polynomial S => p.coeff 3) hmain
    rw [hL, hR, h3, h2] at hc3
    simpa only [zero_mul, add_zero] using hc3
  -- assemble
  have hassemble : π (kleinR a b (kleinPolarP a b c u) i * c j
      - kleinR a b (kleinPolarP a b c u) j * c i) = 0 := by
    change π (kleinR a b V0 i * c j - kleinR a b V0 j * c i) = 0
    simp only [map_sub, map_mul]
    rw [hkey i, hkey j]
    first | refl_ring1 | ring
  -- the ideal is generated by the vanishing quadrics, hence is `⊥`
  have hJ : J ≤ ⊥ := Ideal.span_le.mpr (by
    rintro y ⟨k, rfl⟩
    change kleinP a b c k ∈ (⊥ : Ideal R)
    rw [hc k]
    exact Submodule.zero_mem _)
  have hmem : kleinR a b (kleinPolarP a b c u) i * c j
      - kleinR a b (kleinPolarP a b c u) j * c i ∈ J :=
    Ideal.Quotient.eq_zero_iff_mem.mp hassemble
  have hzero : kleinR a b (kleinPolarP a b c u) i * c j
      - kleinR a b (kleinPolarP a b c u) j * c i = 0 := by
    simpa using hJ hmem
  exact sub_eq_zero.mp hzero

end Work.MotAS
