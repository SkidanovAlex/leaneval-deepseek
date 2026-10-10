import Mathlib
import Submission.Work.MotK.RuleData
import Submission.Work.MotK.CensusFibre.SecPolar
import Submission.Work.MotK.KleinI4
import Submission.Work.MotK.CensusFibre.sec_polar_expansion
import Submission.Work.MotK.CensusFibre.sec_p2_mem
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The G-side ruling identity of the Crauder–Katz link (`Work.MotK.CensusFibre.ruling_mem`)

For `c` in the Klein curve `C = V(p_0, …, p_4)` and `w = λ·A(c) + μ·B(c)` a point of the ruling
line, the cubic map `R = kleinR a b` is projectively constant on `ℓ_c` with value `c`.

Structure of the proof (the structural route of `GUIDE_K5K6.md` §3):

* `w = dP_c(u)` is the polar of the Pfaffian quadratic map `P` at `c` in the direction
  `u = λ u_1 + μ u_2` (`kleinPolarP_lin`);
* the *Taylor identity* — I1 (`kleinR_kleinP`) applied to the deformed point `c + T • u`, using
  bilinearity (`kleinP_add_smul`) and homogeneity (`kleinR_homog`) — gives, in the quotient
  `(K[c]/J)[T]`, that `T^3 • R(dP_c u + T P u) = s (c + T u) • (c + T u)`;
* extracting the coefficient of `T^3` (`kleinSec_coeff_two`, `kleinSec_coeff_three`) gives
  `R_i(dP_c u) = P_3(c,u)·c_i + P_2(c,u)·u_i`, where `P_j` are the polars of the secant quintic;
* `P_2` lies in `J = (p_0, …, p_4)` (`kleinSecP2_mem`, identity I5), so
  `R_i(dP_c u) ≡ P_3(c,u)·c_i (mod J)` and the ruling identity follows.
-/

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK.CensusFibre

open Work.MotK

variable {R : Type*} [CommRing R]

/-! ## The polar form of the Pfaffian map -/

/-- **Bilinearity of the polar form of `P = kleinP`**: for a quadratic map,
`P (x + t • y) = P x + t · dP_x(y) + t² · P y`. -/
theorem kleinP_add_smul (a b : R) (x y : Fin 5 → R) (t : R) :
    kleinP a b (fun i => x i + t * y i) = fun k =>
      kleinP a b x k + t * kleinPolarP a b x y k + t ^ 2 * kleinP a b y k := by
  funext k
  fin_cases k <;>
    simp only [kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four,
      kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four',
      kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinPolarP, Pi.add_apply] <;>
    first | refl_ring1 | ring

/-- **Linearity of the polar form in its second argument.** -/
theorem kleinPolarP_lin (a b : R) (c u v : Fin 5 → R) (s t : R) :
    kleinPolarP a b c (fun i => s * u i + t * v i)
      = fun i => s * kleinPolarP a b c u i + t * kleinPolarP a b c v i := by
  funext k
  fin_cases k <;>
    simp only [kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four,
      kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four',
      kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, kleinPolarP, Pi.add_apply] <;>
    first | refl_ring1 | ring

/-- Naturality of `kleinP` under a ring homomorphism (componentwise). -/
theorem kleinP_map_apply {S : Type*} [CommRing S] (φ : R →+* S) (a b : R) (x : Fin 5 → R)
    (k : Fin 5) : φ (kleinP a b x k) = kleinP (φ a) (φ b) (fun i => φ (x i)) k := by
  fin_cases k <;>
    simp only [kleinP_zero, kleinP_one, kleinP_two, kleinP_three, kleinP_four,
      kleinP_zero', kleinP_one', kleinP_two', kleinP_three', kleinP_four',
      kleinP0, kleinP1, kleinP2, kleinP3, kleinP4, map_add, map_mul, map_sub, map_neg,
      map_pow, map_ofNat, map_natCast]

/-- Naturality of `kleinP`. -/
theorem kleinP_map {S : Type*} [CommRing S] (φ : R →+* S) (a b : R) (x : Fin 5 → R) :
    (fun k => φ (kleinP a b x k)) = kleinP (φ a) (φ b) (fun i => φ (x i)) :=
  funext fun k => kleinP_map_apply φ a b x k

/-- Naturality of the polar form of `kleinP` (componentwise). -/
theorem kleinPolarP_map_apply {S : Type*} [CommRing S] (φ : R →+* S) (a b : R)
    (x y : Fin 5 → R) (k : Fin 5) :
    φ (kleinPolarP a b x y k)
      = kleinPolarP (φ a) (φ b) (fun i => φ (x i)) (fun i => φ (y i)) k := by
  have hv : (fun i => φ ((x + y) i)) = (fun i => φ (x i)) + (fun i => φ (y i)) := by
    funext i
    simp only [Pi.add_apply, map_add]
  simp only [kleinPolarP, Pi.add_apply]
  rw [map_sub, map_sub, ← hv]
  rw [kleinP_map_apply φ a b (x + y) k, kleinP_map_apply φ a b x k,
    kleinP_map_apply φ a b y k]

/-! ## Coefficient extraction from the polar expansion of the secant quintic -/

/-- The coefficient of `T^2` of `s (c + T • u)` is the second polar `kleinSecP2`. -/
theorem kleinSec_coeff_two (a b : R) (c u : Fin 5 → R) :
    (kleinSec (Polynomial.C a) (Polynomial.C b)
      (fun i => Polynomial.C (c i) + Polynomial.X * Polynomial.C (u i))).coeff 2
      = kleinSecP2 a b c u := by
  rw [sec_polar_expansion (Polynomial R) (Polynomial.C a) (Polynomial.C b)
    (fun i => Polynomial.C (c i)) (fun i => Polynomial.C (u i)) Polynomial.X,
    ← kleinSecP0_map (S := Polynomial R) (Polynomial.C) a b c u,
    ← kleinSecP1_map (S := Polynomial R) (Polynomial.C) a b c u,
    ← kleinSecP2_map (S := Polynomial R) (Polynomial.C) a b c u,
    ← kleinSecP3_map (S := Polynomial R) (Polynomial.C) a b c u,
    ← kleinSecP4_map (S := Polynomial R) (Polynomial.C) a b c u,
    ← kleinSecP5_map (S := Polynomial R) (Polynomial.C) a b c u]
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', Polynomial.coeff_C]
  norm_num

/-- The coefficient of `T^3` of `s (c + T • u)` is the third polar `kleinSecP3`. -/
theorem kleinSec_coeff_three (a b : R) (c u : Fin 5 → R) :
    (kleinSec (Polynomial.C a) (Polynomial.C b)
      (fun i => Polynomial.C (c i) + Polynomial.X * Polynomial.C (u i))).coeff 3
      = kleinSecP3 a b c u := by
  rw [sec_polar_expansion (Polynomial R) (Polynomial.C a) (Polynomial.C b)
    (fun i => Polynomial.C (c i)) (fun i => Polynomial.C (u i)) Polynomial.X,
    ← kleinSecP0_map (S := Polynomial R) (Polynomial.C) a b c u,
    ← kleinSecP1_map (S := Polynomial R) (Polynomial.C) a b c u,
    ← kleinSecP2_map (S := Polynomial R) (Polynomial.C) a b c u,
    ← kleinSecP3_map (S := Polynomial R) (Polynomial.C) a b c u,
    ← kleinSecP4_map (S := Polynomial R) (Polynomial.C) a b c u,
    ← kleinSecP5_map (S := Polynomial R) (Polynomial.C) a b c u]
  simp only [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', Polynomial.coeff_C]
  norm_num

/-- The constant coefficient of `C x + X * C y` is `x`. -/
theorem coeff_zero_C_add_X_mul (S : Type*) [CommRing S] (x y : S) :
    (Polynomial.C x + Polynomial.X * Polynomial.C y).coeff 0 = x := by
  rw [Polynomial.coeff_add, Polynomial.coeff_C, if_pos rfl]
  have h : (Polynomial.X * Polynomial.C y).coeff 0 = 0 := by
    rw [← pow_one Polynomial.X, Polynomial.coeff_X_pow_mul']
    norm_num
  rw [h, add_zero]

/-! ## The ruling identity -/

/-- **The G-side ruling identity** (design node `K5`).

Let `A(c) = dP_c(u₁)`, `B(c) = dP_c(u₂)` be the ruling vectors of
`Submission.Work.MotK.RuleData` (built from the polar `kleinBilin` of the shift-invariant quadric
`kleinQ = Σ_k kleinP k`) and `w = λ·A(c) + μ·B(c)` a point of the ruling line `ℓ_c`.  Then for
every `c ∈ C = V(p₀,…,p₄)` the cubic map `R = kleinR a b` is projectively constant on `ℓ_c` with
value `c`:

  `R_i(w)·c_j − R_j(w)·c_i = 0`  for all `i, j`  whenever  `p₀(c) = … = p₄(c) = 0`,

i.e. the polynomial `R_i(w)c_j − R_j(w)c_i` lies in the ideal `(p₀,…,p₄)(c)` generated by the
Klein Pfaffians in the coordinates `c`.

Consequently `ℓ_c` is contained in the fibre of `R` over `c`, and hence — by I2
(`kleinP_kleinR`: `p_i(R(z)) = s'(z)z_i`) — in the ruling divisor `{s' = 0}` of the census: `ℓ_c` is
the ruling line of the target-side exceptional divisor of the Crauder–Katz link over `C`
(`GUIDE_K5K6.md` §2b, §3).  This is the `G`-side analogue of `kleinFibre_eq_ker`, which settles
the `F`-side.

**Verification.**  Checked numerically over `𝔽₁₃` (and, by the reviewer, over several
characteristics including `𝔽₂, 𝔽₃, 𝔽₅, 𝔽₇, 𝔽₁₁, 𝔽₁₀₁`) for `(a,b) = (1,1), (2,3), (3,5)` and the
boundary cases `a = 0`, `b = 0`, `l = 0`, `m = 0`: membership holds in every case
(`probe_fib18.py`, `probe_fib19.py`).  Degrees: `A, B` are quadratic in `c`, so `R(w)` is sextic
and the displayed polynomial is homogeneous of degree seven in `c`.

**Proof strategy.**  `C` is a smooth curve for `(a,b)` in the good locus, so `(p₀,…,p₄)` is a
radical ideal there; the clean proof is however a *certificate*
`R_i(w)c_j − R_j(w)c_i = Σ_k g_k p_k` with cofactors `g_k` homogeneous of degree five — for each
`(i,j)` this is a linear system with 630 unknowns solved against the 330 coefficients of the
degree-seven part (the reviewer verified that the degree-seven part of the ideal has rank 295 < 330,
so such a certificate exists).  A single universal certificate over `MvPolynomial (Fin 7) ℤ`
(parameters `a b`, coordinates `c₀…c₄`, `λ`, `μ`), transferred along a ring homomorphism — the
`KleinI4` pattern of `Submission/Work/MotK/KleinI4.lean` — should be much cheaper than ten
separate ones; a structural proof is better still. -/
theorem ruling_mem (K : Type) [Field K] (a b l m : K) (i j : Fin 5) :
    Work.MotK.kleinR (MvPolynomial.C a : MvPolynomial (Fin 5) K)
        (MvPolynomial.C b : MvPolynomial (Fin 5) K)
        (Work.MotK.kleinRulePt (MvPolynomial.C a : MvPolynomial (Fin 5) K)
          (MvPolynomial.C b : MvPolynomial (Fin 5) K) (fun t => MvPolynomial.X t)
          (MvPolynomial.C l) (MvPolynomial.C m)) i
      * MvPolynomial.X j
      - Work.MotK.kleinR (MvPolynomial.C a : MvPolynomial (Fin 5) K)
        (MvPolynomial.C b : MvPolynomial (Fin 5) K)
        (Work.MotK.kleinRulePt (MvPolynomial.C a : MvPolynomial (Fin 5) K)
          (MvPolynomial.C b : MvPolynomial (Fin 5) K) (fun t => MvPolynomial.X t)
          (MvPolynomial.C l) (MvPolynomial.C m)) j
      * MvPolynomial.X i
    ∈ Ideal.span (Set.range (fun k => Work.MotK.kleinP (MvPolynomial.C a : MvPolynomial (Fin 5) K)
        (MvPolynomial.C b : MvPolynomial (Fin 5) K) (fun t => MvPolynomial.X t) k)) := by
  -- the direction vector `u = l • u₁ + m • u₂`
  set u : Fin 5 → MvPolynomial (Fin 5) K := fun t =>
    MvPolynomial.C l * kleinTan (MvPolynomial.C a) (MvPolynomial.C b)
        (fun s => MvPolynomial.X s) 1 t
      + MvPolynomial.C m * kleinTan (MvPolynomial.C a) (MvPolynomial.C b)
        (fun s => MvPolynomial.X s) 2 t with hu
  -- the ruled point is the polar of `P` in the direction `u`
  have hw : kleinRulePt (MvPolynomial.C a) (MvPolynomial.C b) (fun t => MvPolynomial.X t)
        (MvPolynomial.C l) (MvPolynomial.C m)
      = kleinPolarP (MvPolynomial.C a) (MvPolynomial.C b) (fun t => MvPolynomial.X t) u := by
    funext t
    simp only [kleinRulePt, hu]
    rw [kleinPolarP_lin (MvPolynomial.C a) (MvPolynomial.C b) (fun s => MvPolynomial.X s)
      (kleinTan (MvPolynomial.C a) (MvPolynomial.C b) (fun s => MvPolynomial.X s) 1)
      (kleinTan (MvPolynomial.C a) (MvPolynomial.C b) (fun s => MvPolynomial.X s) 2)
      (MvPolynomial.C l) (MvPolynomial.C m)]
    simp only [kleinRuleA, kleinRuleB]
  -- the ideal and the quotient ring
  let J : Ideal (MvPolynomial (Fin 5) K) :=
    Ideal.span (Set.range (fun k => kleinP (MvPolynomial.C a) (MvPolynomial.C b)
      (fun t => MvPolynomial.X t) k))
  have hp : ∀ k : Fin 5,
      kleinP (MvPolynomial.C a) (MvPolynomial.C b) (fun t => MvPolynomial.X t) k ∈ J :=
    fun k => Ideal.subset_span ⟨k, rfl⟩
  let S := MvPolynomial (Fin 5) K ⧸ J
  let π : MvPolynomial (Fin 5) K →+* S := Ideal.Quotient.mk J
  have hπ : ∀ k : Fin 5,
      π (kleinP (MvPolynomial.C a) (MvPolynomial.C b) (fun t => MvPolynomial.X t) k) = 0 :=
    fun k => Ideal.Quotient.eq_zero_iff_mem.mpr (hp k)
  -- the data in the polynomial ring over the quotient
  let aP : Polynomial S := Polynomial.C (π (MvPolynomial.C a))
  let bP : Polynomial S := Polynomial.C (π (MvPolynomial.C b))
  let cS : Fin 5 → Polynomial S := fun t => Polynomial.C (π (MvPolynomial.X t))
  let uS : Fin 5 → Polynomial S := fun t => Polynomial.C (π (u t))
  let V0 : Fin 5 → MvPolynomial (Fin 5) K :=
    kleinPolarP (MvPolynomial.C a) (MvPolynomial.C b) (fun t => MvPolynomial.X t) u
  let V1 : Fin 5 → MvPolynomial (Fin 5) K :=
    kleinP (MvPolynomial.C a) (MvPolynomial.C b) u
  let VS : Fin 5 → Polynomial S := fun k =>
    Polynomial.C (π (V0 k)) + Polynomial.X * Polynomial.C (π (V1 k))
  -- `P (c + T u) = T • (V0 + T • V1)`
  have hPxS : (fun k => kleinP aP bP (fun t => cS t + Polynomial.X * uS t) k)
      = fun k => Polynomial.X * VS k := by
    funext k
    rw [kleinP_add_smul (R := Polynomial S) aP bP cS uS Polynomial.X]
    change kleinP aP bP cS k + Polynomial.X * kleinPolarP aP bP cS uS k
      + Polynomial.X ^ 2 * kleinP aP bP uS k = Polynomial.X * VS k
    have h0 : kleinP aP bP cS k = 0 := by
      rw [show aP = (Polynomial.C.comp π) (MvPolynomial.C a) from rfl,
        show bP = (Polynomial.C.comp π) (MvPolynomial.C b) from rfl,
        show cS = (fun t => (Polynomial.C.comp π) (MvPolynomial.X t)) from rfl,
        ← kleinP_map_apply (R := MvPolynomial (Fin 5) K) (S := Polynomial S) (Polynomial.C.comp π)
          (MvPolynomial.C a) (MvPolynomial.C b) (fun t => MvPolynomial.X t) k]
      simp only [RingHom.comp_apply, hπ k, map_zero]
    have h2 : kleinPolarP aP bP cS uS k = Polynomial.C (π (V0 k)) := by
      rw [show aP = (Polynomial.C.comp π) (MvPolynomial.C a) from rfl,
        show bP = (Polynomial.C.comp π) (MvPolynomial.C b) from rfl,
        show cS = (fun t => (Polynomial.C.comp π) (MvPolynomial.X t)) from rfl,
        show uS = (fun t => (Polynomial.C.comp π) (u t)) from rfl,
        ← kleinPolarP_map_apply (R := MvPolynomial (Fin 5) K) (S := Polynomial S) (Polynomial.C.comp π)
          (MvPolynomial.C a) (MvPolynomial.C b) (fun t => MvPolynomial.X t) u k]
      rfl
    have h3 : kleinP aP bP uS k = Polynomial.C (π (V1 k)) := by
      rw [show aP = (Polynomial.C.comp π) (MvPolynomial.C a) from rfl,
        show bP = (Polynomial.C.comp π) (MvPolynomial.C b) from rfl,
        show uS = (fun t => (Polynomial.C.comp π) (u t)) from rfl,
        ← kleinP_map_apply (R := MvPolynomial (Fin 5) K) (S := Polynomial S) (Polynomial.C.comp π)
          (MvPolynomial.C a) (MvPolynomial.C b) u k]
      rfl
    rw [h0, h2, h3]
    first | refl_ring1 | ring
  -- I1 applied to the deformed point, and homogeneity
  have hI1 : ∀ t : Fin 5, kleinR aP bP (fun k => Polynomial.X * VS k) t
      = kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)
        * (cS t + Polynomial.X * uS t) := by
    intro t
    rw [← hPxS]
    exact kleinR_kleinP aP bP (fun s => cS s + Polynomial.X * uS s) t
  have hhom : ∀ t : Fin 5, kleinR aP bP (fun k => Polynomial.X * VS k) t
      = Polynomial.X ^ 3 * kleinR aP bP VS t := by
    intro t
    exact congrFun (kleinR_homog aP bP Polynomial.X VS) t
  -- coefficient of `T^3`
  have hkey : ∀ t : Fin 5, π (kleinR (MvPolynomial.C a) (MvPolynomial.C b)
        (kleinPolarP (MvPolynomial.C a) (MvPolynomial.C b) (fun s => MvPolynomial.X s) u) t)
      = π (kleinSecP3 (MvPolynomial.C a) (MvPolynomial.C b) (fun s => MvPolynomial.X s) u)
        * π (MvPolynomial.X t) := by
    intro t
    have hmain : Polynomial.X ^ 3 * kleinR aP bP VS t
        = kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)
          * (cS t + Polynomial.X * uS t) := by
      rw [← hhom t, hI1 t]
    have hL : (Polynomial.X ^ 3 * kleinR aP bP VS t).coeff 3
        = π (kleinR (MvPolynomial.C a) (MvPolynomial.C b)
            (kleinPolarP (MvPolynomial.C a) (MvPolynomial.C b)
              (fun s => MvPolynomial.X s) u) t) := by
      have e1 : (Polynomial.X ^ 3 * kleinR aP bP VS t).coeff 3
          = (kleinR aP bP VS t).coeff 0 := by
        rw [show (3 : ℕ) = 0 + 3 from (zero_add 3).symm, Polynomial.coeff_X_pow_mul]
      have e2 : (kleinR aP bP VS t).coeff 0
          = Polynomial.constantCoeff (kleinR aP bP VS t) := by
        rw [← Polynomial.constantCoeff_apply]
      have e3 : Polynomial.constantCoeff (kleinR aP bP VS t)
          = π (kleinR (MvPolynomial.C a) (MvPolynomial.C b)
              (kleinPolarP (MvPolynomial.C a) (MvPolynomial.C b)
                (fun s => MvPolynomial.X s) u) t) := by
        rw [kleinR_map (Polynomial.constantCoeff) aP bP VS t]
        have ha : Polynomial.constantCoeff aP = π (MvPolynomial.C a) := by
          dsimp only [aP]
          rw [Polynomial.constantCoeff_apply, Polynomial.coeff_C]
          norm_num
        have hb : Polynomial.constantCoeff bP = π (MvPolynomial.C b) := by
          dsimp only [bP]
          rw [Polynomial.constantCoeff_apply, Polynomial.coeff_C]
          norm_num
        have hVS : ∀ k : Fin 5, Polynomial.constantCoeff (VS k) = π (V0 k) := by
          intro k
          dsimp only [VS]
          rw [Polynomial.constantCoeff_apply, coeff_zero_C_add_X_mul]
        rw [ha, hb,
          show (fun k => Polynomial.constantCoeff (VS k)) = (fun k => π (V0 k)) from
            funext hVS,
          ← kleinR_map π (MvPolynomial.C a) (MvPolynomial.C b) V0 t]
      exact e1.trans (e2.trans e3)
    have hR : (kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)
          * (cS t + Polynomial.X * uS t)).coeff 3
        = (kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)).coeff 3
            * π (MvPolynomial.X t)
          + (kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)).coeff 2 * π (u t) := by
      have e1 : kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)
            * (cS t + Polynomial.X * uS t)
          = kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)
              * Polynomial.C (π (MvPolynomial.X t))
            + (kleinSec aP bP (fun s => cS s + Polynomial.X * uS s) * Polynomial.X)
              * Polynomial.C (π (u t)) := by
        dsimp only [cS, uS]
        first | refl_ring1 | ring
      rw [e1, Polynomial.coeff_add, Polynomial.coeff_mul_C, Polynomial.coeff_mul_C,
        show (3 : ℕ) = 2 + 1 from rfl, Polynomial.coeff_mul_X]
    have h3 : (kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)).coeff 3
        = π (kleinSecP3 (MvPolynomial.C a) (MvPolynomial.C b) (fun s => MvPolynomial.X s) u) := by
      rw [show kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)
          = kleinSec (Polynomial.C (π (MvPolynomial.C a))) (Polynomial.C (π (MvPolynomial.C b)))
              (fun s => Polynomial.C (π (MvPolynomial.X s)) + Polynomial.X * Polynomial.C (π (u s)))
          from rfl,
        kleinSec_coeff_three (π (MvPolynomial.C a)) (π (MvPolynomial.C b))
          (fun s => π (MvPolynomial.X s)) (fun s => π (u s)),
        ← kleinSecP3_map (R := MvPolynomial (Fin 5) K) (S := S) π (MvPolynomial.C a) (MvPolynomial.C b)
          (fun s => MvPolynomial.X s) u]
    have h2 : (kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)).coeff 2 = 0 := by
      rw [show kleinSec aP bP (fun s => cS s + Polynomial.X * uS s)
          = kleinSec (Polynomial.C (π (MvPolynomial.C a))) (Polynomial.C (π (MvPolynomial.C b)))
              (fun s => Polynomial.C (π (MvPolynomial.X s)) + Polynomial.X * Polynomial.C (π (u s)))
          from rfl,
        kleinSec_coeff_two (π (MvPolynomial.C a)) (π (MvPolynomial.C b))
          (fun s => π (MvPolynomial.X s)) (fun s => π (u s)),
        ← kleinSecP2_map (R := MvPolynomial (Fin 5) K) (S := S) π (MvPolynomial.C a) (MvPolynomial.C b)
          (fun s => MvPolynomial.X s) u,
        show π (kleinSecP2 (MvPolynomial.C a) (MvPolynomial.C b) (fun s => MvPolynomial.X s) u) = 0
          from Ideal.Quotient.eq_zero_iff_mem.mpr (sec_p2_mem K a b u)]
    have hc := congrArg (fun p : Polynomial S => p.coeff 3) hmain
    rw [hL, hR, h3, h2] at hc
    simpa only [zero_mul, add_zero] using hc
  -- assemble
  have hassemble : π (kleinR (MvPolynomial.C a) (MvPolynomial.C b)
        (kleinRulePt (MvPolynomial.C a) (MvPolynomial.C b) (fun t => MvPolynomial.X t)
          (MvPolynomial.C l) (MvPolynomial.C m)) i * MvPolynomial.X j
      - kleinR (MvPolynomial.C a) (MvPolynomial.C b)
        (kleinRulePt (MvPolynomial.C a) (MvPolynomial.C b) (fun t => MvPolynomial.X t)
          (MvPolynomial.C l) (MvPolynomial.C m)) j * MvPolynomial.X i) = 0 := by
    rw [hw]
    simp only [map_sub, map_mul]
    rw [hkey i, hkey j]
    first | refl_ring1 | ring
  exact Ideal.Quotient.eq_zero_iff_mem.mp hassemble

end Work.MotK.CensusFibre
