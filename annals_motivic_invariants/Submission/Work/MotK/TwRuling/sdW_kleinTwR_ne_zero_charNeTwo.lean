import Mathlib
import Submission.Work.MotK.TGen.SdualTBrick
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.TGen.TwCoordGKleinTw
import Submission.Work.MotK.TwRule.KleinTwRuleEval
import Submission.Work.MotK.TwRuling.SdWNdeg
import Submission.Work.MotK.TwRuling.SdSextDefs
import Submission.Work.MotK.TwRuling.SdSextValues
import Submission.Work.MotK.TwRuling.SdSextHomog
import Submission.Work.MotK.TwRuling.SdSextTransport
import Submission.Work.MotK.TwRuling.good_bFive_ne_charFive
import Submission.Work.MotK.TwRuling.sexticTw_notMem_kernel
import Submission.Work.MotK.TwRuling.twIdeal6_aeval_point
import Submission.Work.MotK.TwRuling.aeval_sdGform
import Submission.Work.MotK.TwRuling.eval_sdDpoly
import Submission.Work.MotK.TwRuling.aeval_sdGform_gen
import Submission.Work.MotK.TwRuling.SdSplitDefs
import Submission.Work.MotK.TwRuling.rpEval_eq_zero_of_sdW
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `sdW_kleinTwR_ne_zero_charNeTwo`

The inverse cubic map `kleinTwR` of the T-twisted Crauder--Katz link does not vanish on the ruling
point `sdW K D h` of the target ruling divisor, in characteristic `≠ 2`.

## Structure of the proof

* `sdCubic` / `SdSextValues` : the ruling sextic at the explicit point `(a,0,-a,-b,b)` of the Klein
  quintic is the cubic with coefficients `27a¹¹b⁴ - 11a⁶b⁹`, `57a⁹b⁶ - a⁴b¹¹`, `29a⁷b⁸ + 3a²b¹³`,
  `8a¹⁵ + 8a¹⁰b⁵ + 7a⁵b¹⁰ + b¹⁵`; the corresponding four values cannot all vanish in
  characteristic `≠ 2` away from the char-5 locus (`sdFour_values_ne`).
* `sdSextForm_generic_ne` : consequently the ruling sextic does not vanish at the *generic* point of
  the Klein curve (degree-six kernel argument, `sexticTw_notMem_kernel`).
* the twisted/untwisted transport (`SdSextTransport`) turns this into the non-vanishing of
  `kleinTwR0 (sdW)`, and `kleinTwR0` is the zeroth component of `kleinTwR`.
-/

set_option maxHeartbeats 4000000
set_option autoImplicit false

namespace Work.MotK.TwRuling

open WeierstrassCurve WeierstrassCurve.Affine

/-- The cubic obtained by evaluating the ruling sextic at the explicit point `(a,0,-a,-b,b)` of
the Klein quintic (see `SdSextValues`). -/
noncomputable def sdCubic {R : Type*} [CommRing R] (a b : R) : Polynomial R :=
  Polynomial.C (27 * a ^(11:ℕ) * b ^(4:ℕ) - 11 * a ^(6:ℕ) * b ^(9:ℕ)) * Polynomial.X ^(3:ℕ)
    + Polynomial.C (57 * a ^(9:ℕ) * b ^(6:ℕ) - a ^(4:ℕ) * b ^(11:ℕ)) * Polynomial.X ^(2:ℕ)
    + Polynomial.C (29 * a ^(7:ℕ) * b ^(8:ℕ) + 3 * a ^(2:ℕ) * b ^(13:ℕ)) * Polynomial.X ^(1:ℕ)
    + Polynomial.C (8 * a ^(15:ℕ) + 8 * a ^(10:ℕ) * b ^(5:ℕ) + 7 * a ^(5:ℕ) * b ^(10:ℕ) + b ^(15:ℕ))

/-- Coefficient extraction for a cubic written with explicit coefficients. -/
theorem coeff_three_of_cubic {R : Type*} [CommRing R] (c3 c2 c1 c0 : R) :
    (Polynomial.C c3 * Polynomial.X ^(3:ℕ) + Polynomial.C c2 * Polynomial.X ^(2:ℕ)
      + Polynomial.C c1 * Polynomial.X ^(1:ℕ) + Polynomial.C c0).coeff 3 = c3 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]

/-- Coefficient extraction for a cubic written with explicit coefficients. -/
theorem coeff_two_of_cubic {R : Type*} [CommRing R] (c3 c2 c1 c0 : R) :
    (Polynomial.C c3 * Polynomial.X ^(3:ℕ) + Polynomial.C c2 * Polynomial.X ^(2:ℕ)
      + Polynomial.C c1 * Polynomial.X ^(1:ℕ) + Polynomial.C c0).coeff 2 = c2 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]

/-- Coefficient extraction for a cubic written with explicit coefficients. -/
theorem coeff_one_of_cubic {R : Type*} [CommRing R] (c3 c2 c1 c0 : R) :
    (Polynomial.C c3 * Polynomial.X ^(3:ℕ) + Polynomial.C c2 * Polynomial.X ^(2:ℕ)
      + Polynomial.C c1 * Polynomial.X ^(1:ℕ) + Polynomial.C c0).coeff 1 = c1 := by
  simp [Polynomial.coeff_add, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_C]

/-- `sdCubic` evaluates to the factored bracket. -/
theorem eval_sdCubic {R : Type*} [CommRing R] (a b σ : R) :
    Polynomial.eval σ (sdCubic a b)
      = σ ^(3:ℕ) * (27 * a ^(11:ℕ) * b ^(4:ℕ) - 11 * a ^(6:ℕ) * b ^(9:ℕ))
        + σ ^(2:ℕ) * (57 * a ^(9:ℕ) * b ^(6:ℕ) - a ^(4:ℕ) * b ^(11:ℕ))
        + σ * (29 * a ^(7:ℕ) * b ^(8:ℕ) + 3 * a ^(2:ℕ) * b ^(13:ℕ))
        + (8 * a ^(15:ℕ) + 8 * a ^(10:ℕ) * b ^(5:ℕ) + 7 * a ^(5:ℕ) * b ^(10:ℕ) + b ^(15:ℕ)) := by
  simp only [sdCubic, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_pow]
  refl_ring1

/-- **The ruling sextic does not vanish at the generic point of the Klein curve.**

`hKernel` is the degree-six kernel statement (`sexticTw_notMem_kernel`): every degree-six form that
is not in the degree-six part of the Pfaffian ideal is nonzero at the generic point `κ`.
`hIdealVan` says that the explicit point `(a,0,-a,-b,b)` lies on the Klein curve, i.e. that every
element of the Pfaffian ideal vanishes there.  If in addition the ruling sextic forms satisfy the
stated evaluation identity and are homogeneous of degree six, then not all the values
`aeval κ (sdGform a b σ)` can vanish — in characteristic `≠ 2` and away from the
characteristic-5 locus `b⁵ = 2a⁵`. -/
theorem sdSextForm_generic_ne {R : Type} {A : Type} [Field R] [CommRing A] [Algebra R A]
    [Infinite R] (h2 : (2 : R) ≠ 0) (a b : R) (hab : a * b ≠ 0)
    (h5ne : (5 : R) = 0 → b ^(5:ℕ) ≠ 2 * a ^(5:ℕ)) (κ : Fin 5 → A)
    (hKernel : ∀ F : MvPolynomial (Fin 5) R, F.IsHomogeneous 6 →
      F ∉ twIdeal6 R a b 1 → MvPolynomial.aeval κ F ≠ 0)
    (hHom : ∀ σ : R, (sdGform a b σ).IsHomogeneous 6)
    (hIdealVan : ∀ F ∈ twIdeal6 R a b 1, MvPolynomial.aeval ![a, 0, -a, -b, b] F = 0)
    (hEval : ∀ σ : R, MvPolynomial.aeval ![a, 0, -a, -b, b] (sdGform a b σ)
        = Polynomial.eval σ (sdDpoly a b))
    (hPoint : ∀ σ : R, Polynomial.eval σ (sdDpoly a b)
        = -(a ^(3:ℕ) * b ^(4:ℕ)) * Polynomial.eval σ (sdCubic a b))
    (hVan : ∀ σ : R, MvPolynomial.aeval κ (sdGform a b σ) = 0) : False := by
  have ha : a ≠ 0 := fun h0 => hab (by rw [h0, zero_mul])
  have hb : b ≠ 0 := fun h0 => hab (by rw [h0, mul_zero])
  -- every `sdGform a b σ` lies in the degree-six part of the Pfaffian ideal
  have hmem : ∀ σ : R, sdGform a b σ ∈ twIdeal6 R a b 1 := by
    intro σ
    by_contra hnot
    exact (hKernel (sdGform a b σ) (hHom σ) hnot) (hVan σ)
  -- consequently the value polynomial vanishes at every scalar
  have hDval : ∀ σ : R, Polynomial.eval σ (sdDpoly a b) = 0 := by
    intro σ
    rw [← hEval σ]
    exact hIdealVan (sdGform a b σ) (hmem σ)
  -- so the cubic bracket vanishes pointwise, hence the cubic is zero
  have hbracket : ∀ σ : R, σ ^(3:ℕ) * (27 * a ^(11:ℕ) * b ^(4:ℕ) - 11 * a ^(6:ℕ) * b ^(9:ℕ))
        + σ ^(2:ℕ) * (57 * a ^(9:ℕ) * b ^(6:ℕ) - a ^(4:ℕ) * b ^(11:ℕ))
        + σ * (29 * a ^(7:ℕ) * b ^(8:ℕ) + 3 * a ^(2:ℕ) * b ^(13:ℕ))
        + (8 * a ^(15:ℕ) + 8 * a ^(10:ℕ) * b ^(5:ℕ) + 7 * a ^(5:ℕ) * b ^(10:ℕ) + b ^(15:ℕ)) = 0 := by
    intro σ
    have h := hDval σ
    rw [hPoint σ, eval_sdCubic] at h
    have ha3 : -(a ^(3:ℕ) * b ^(4:ℕ)) ≠ 0 :=
      neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb))
    exact (mul_eq_zero.mp h).resolve_left ha3
  have hcubic0 : sdCubic a b = 0 := by
    refine Polynomial.funext (q := 0) fun σ => ?_
    rw [Polynomial.eval_zero, eval_sdCubic]
    exact hbracket σ
  -- read off the three coefficients
  have hc3fact : a ^(6:ℕ) * b ^(4:ℕ) * (27 * a ^(5:ℕ) - 11 * b ^(5:ℕ)) = 0 := by
    have h3 := congrArg (fun p : Polynomial R => p.coeff 3) hcubic0
    simp only [Polynomial.coeff_zero] at h3
    rw [sdCubic, coeff_three_of_cubic] at h3
    linear_combination (norm := refl_ring1) h3
  have hc3 : (27 : R) * a ^(5:ℕ) - 11 * b ^(5:ℕ) = 0 :=
    (mul_eq_zero.mp hc3fact).resolve_left (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb))
  have hc2fact : a ^(4:ℕ) * b ^(6:ℕ) * (57 * a ^(5:ℕ) - b ^(5:ℕ)) = 0 := by
    have h2 := congrArg (fun p : Polynomial R => p.coeff 2) hcubic0
    simp only [Polynomial.coeff_zero] at h2
    rw [sdCubic, coeff_two_of_cubic] at h2
    linear_combination (norm := refl_ring1) h2
  have hc2 : (57 : R) * a ^(5:ℕ) - b ^(5:ℕ) = 0 :=
    (mul_eq_zero.mp hc2fact).resolve_left (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb))
  have hc1fact : a ^(2:ℕ) * b ^(8:ℕ) * (29 * a ^(5:ℕ) + 3 * b ^(5:ℕ)) = 0 := by
    have h1 := congrArg (fun p : Polynomial R => p.coeff 1) hcubic0
    simp only [Polynomial.coeff_zero] at h1
    rw [sdCubic, coeff_one_of_cubic] at h1
    linear_combination (norm := refl_ring1) h1
  have hc1 : (29 : R) * a ^(5:ℕ) + 3 * b ^(5:ℕ) = 0 :=
    (mul_eq_zero.mp hc1fact).resolve_left (mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb))
  exact sdFour_values_ne h2 a b ha h5ne ⟨hc3, hc2, hc1⟩

/-- In a field with `(5 : K) = 0` the ring characteristic is `5`. -/
theorem ringChar_eq_five {K : Type} [Field K] (h5 : (5 : K) = 0) : ringChar K = 5 := by
  letI := ringChar.spec K
  have hdvd : ringChar K ∣ 5 := (CharP.cast_eq_zero_iff K (ringChar K) 5).mp h5
  have hne : ringChar K ≠ 1 := CharP.ringChar_ne_one (R := K)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h
  · exact absurd h hne
  · exact h

set_option maxHeartbeats 100000000

/-! ## The Kummer transport: from `kleinTwR0 … (sdW K D h) = 0` to the split ruling sextic

The `sdCubic` route needs as its only external input the statement that the vanishing of the
twisted inverse cubic at the ruling point `sdW K D h` (over the target ruling divisor
`sdA K D h = RatFunc ↥(twistFieldTG K D h)`) forces the *split* ruling sextic
`σ ↦ aeval (kleinCoord D (KbG K)) (sdGform a b σ)` to vanish at the Klein point, for every
scalar `σ`.  That transport is carried out here in three steps:

1. `rpEval_eq_zero_of_sdW` (`Submission/Work/MotK/TwRuling/rpEval_eq_zero_of_sdW.lean`): the
   ruling polynomial `rpEval K D h = R₀(A(κ) + T·B(κ))` at the twisted Klein point
   `κ = twCoordG K D h` vanishes;
2. `sdSplitPoly_eq_zero_of_rpEvalAux` (below): the Kummer transport `SdSextTransport` and the
   `λ²`-homogeneity `SdSextHomog` of the ruling vectors turn this into the vanishing of the split
   ruling polynomial `sdSplitPoly K D h = R₀(A(κ) + (w·T)·B(κ))` at the Klein point, where
   `w = sdWL K D h` is the chosen fifth root of `h`;
3. `twistedVanishing_of_sdSplitPolyAux` (below): evaluating at `T = σ/w` gives the split ruling
   sextic at `κ` and the parameter `σ`. -/

/-- Evaluation of the split ruling polynomial at `x`: the polynomial identity
`sdSplitPoly K D h = R₀(A(κ) + (w·T)·B(κ))` gives, at `T = x`, the split ruling data at the Klein
point `κ = sdKbL K D` with ruling parameter `w·x` (`w = sdWL K D h`). -/
theorem eval_sdSplitPolyAux {K : Type} [Field K] (D : Work.MotV.KleinData K) (h : K)
    (x : Work.MotK.OmG K D) :
    Polynomial.evalRingHom x (Work.MotK.TwRuling.sdSplitPoly K D h)
      = Work.MotK.kleinTwR0 (algebraMap K (Work.MotK.OmG K D) D.a)
          (algebraMap K (Work.MotK.OmG K D) D.b) 1
          (fun i => Work.MotK.kleinTwRuleA (algebraMap K (Work.MotK.OmG K D) D.a)
              (algebraMap K (Work.MotK.OmG K D) D.b) 1 (Work.MotK.TwRuling.sdKbL K D) i
            + (Work.MotK.TwRuling.sdWL K D h * x) *
              Work.MotK.kleinTwRuleB (algebraMap K (Work.MotK.OmG K D) D.a)
                (algebraMap K (Work.MotK.OmG K D) D.b) 1 (Work.MotK.TwRuling.sdKbL K D) i) := by
  rw [Work.MotK.TwRuling.sdSplitPoly]
  rw [Work.MotK.TwRuling.kleinTwR0_map (Polynomial.evalRingHom x)]
  simp only [map_one]
  congr 1
  · simp
  · simp
  · funext i
    simp

/-- **The Kummer transport of the ruling polynomial.**  If the twisted ruling polynomial
`rpEval K D h` vanishes, then so does the split ruling polynomial `sdSplitPoly K D h`: the
transport `SdSextTransport` rewrites the twisted ruling point into the split one, the
`λ²`-homogeneity of the ruling vectors rescales the ratios `κ_i/κ_0` back to `κ_i`, and the
degree-three homogeneity of `kleinTwR0` removes the factor `κ_0^6`. -/
theorem sdSplitPoly_eq_zero_of_rpEvalAux {K : Type} [Field K] (D : Work.MotV.KleinData K)
    (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hz : Work.MotK.TwRuling.rpEval K D h = 0) :
    Work.MotK.TwRuling.sdSplitPoly K D h = 0 := by
  let L : Type := Work.MotK.OmG K D
  let aL : L := algebraMap K L D.a
  let bL : L := algebraMap K L D.b
  let hL : L := algebraMap K L h
  let wL : L := Work.MotK.TwRuling.sdWL K D h
  let kap : Fin 5 → L := Work.MotK.TwRuling.sdKbL K D
  have hwL5 : wL ^(5:ℕ) = hL := Work.MotK.TwRuling.sdWL_pow_five K D h
  have hwLne : wL ≠ 0 := Work.MotK.TwRuling.sdWL_ne_zero K D hh
  have hkap0 : kap 0 ≠ 0 := Work.MotK.TwRuling.sdKbL_zero_ne K D hD
  -- the twisted coordinate tuple
  set cc : Fin 5 → Polynomial L :=
    (fun i => Polynomial.C (Work.MotK.twCoordG K D h i)) with hcc
  -- the ruling point of the *split* model, built out of the ratios `κ_i/κ_0`
  set Z : Fin 5 → Polynomial L := (fun k =>
    Work.MotK.kleinTwRuleA (Polynomial.C aL) (Polynomial.C bL) 1
        (fun j => Polynomial.C (kap j / kap 0)) k
      + ((Polynomial.C wL) * Polynomial.X) *
        Work.MotK.kleinTwRuleB (Polynomial.C aL) (Polynomial.C bL) 1
          (fun j => Polynomial.C (kap j / kap 0)) k) with hZ
  -- the transport, with `w = C wL`
  have hCw5 : (Polynomial.C wL) ^(5:ℕ) = Polynomial.C hL := by
    rw [← Polynomial.C_pow, hwL5]
  have htr := Work.MotK.TwRuling.SdSextTransport (R := Polynomial L) (Polynomial.C aL)
    (Polynomial.C bL) (Polynomial.C hL) (Polynomial.C wL) hCw5 cc 1 Polynomial.X
  -- the twisted coordinates are the ratios `κ_i/κ_0` after multiplication by `w`
  have hci : ∀ i : Fin 5,
      (Polynomial.C wL) ^ (i : ℕ) * cc i = Polynomial.C (kap i / kap 0) := by
    intro i
    have h1 : (Polynomial.C wL) ^ (i : ℕ) * cc i
        = Polynomial.C (wL ^ (i : ℕ) * Work.MotK.twCoordG K D h i) := by
      rw [hcc]
      show (Polynomial.C wL) ^ (i : ℕ) * Polynomial.C (Work.MotK.twCoordG K D h i)
        = Polynomial.C (wL ^ (i : ℕ) * Work.MotK.twCoordG K D h i)
      rw [← Polynomial.C_pow, ← Polynomial.C_mul]
    have h2 : Polynomial.C (wL ^ (i : ℕ) * Work.MotK.twCoordG K D h i)
        = Polynomial.C (kap i / kap 0) :=
      congrArg Polynomial.C (Work.MotK.TwRuling.sdWL_pow_mul_twCoordG K D h hh i)
    exact h1.trans h2
  have hcl : (fun i : Fin 5 => (Polynomial.C wL) ^ (i : ℕ) * cc i)
      = fun i => Polynomial.C (kap i / kap 0) := by
    funext i
    exact hci i
  -- ## Step 1: the transport rewrites the twisted polynomial
  have hpt1 : Work.MotK.kleinTwRulePt (Polynomial.C aL) (Polynomial.C bL) (Polynomial.C hL)
      cc 1 Polynomial.X
      = fun k => Polynomial.C (Work.MotK.kleinTwRuleA aL bL hL (Work.MotK.twCoordG K D h) k)
          + Polynomial.X * Polynomial.C
              (Work.MotK.kleinTwRuleB aL bL hL (Work.MotK.twCoordG K D h) k) := by
    funext k
    have hA := congrFun (Work.MotK.kleinTwRuleA_map
      (Polynomial.C : L →+* Polynomial L) aL bL hL (Work.MotK.twCoordG K D h)) k
    have hB := congrFun (Work.MotK.kleinTwRuleB_map
      (Polynomial.C : L →+* Polynomial L) aL bL hL (Work.MotK.twCoordG K D h)) k
    simp only [Work.MotK.kleinTwRulePt, one_mul, hcc]
    rw [← hA, ← hB]
  have hLHS : Work.MotK.kleinTwR0 (Polynomial.C aL) (Polynomial.C bL) (Polynomial.C hL)
      (Work.MotK.kleinTwRulePt (Polynomial.C aL) (Polynomial.C bL) (Polynomial.C hL)
        cc 1 Polynomial.X)
      = Work.MotK.TwRuling.rpEval K D h := by
    rw [hpt1]
    rfl
  -- ## Step 2: the transported ruling point is `Z`
  have hpt2 : Work.MotK.kleinTwRulePt (Polynomial.C aL) (Polynomial.C bL)
      (1 : Polynomial L) (fun i => (Polynomial.C wL) ^ (i : ℕ) * cc i) 1
      ((Polynomial.C wL) * Polynomial.X) = Z := by
    rw [hZ]
    funext k
    simp only [Work.MotK.kleinTwRulePt, one_mul, hcl]
  have hZ0 : Work.MotK.kleinTwR0 (Polynomial.C aL) (Polynomial.C bL)
      (1 : Polynomial L) Z = 0 := by
    have h1 : (Polynomial.C wL) ^(3:ℕ) * Work.MotK.kleinTwR0 (Polynomial.C aL)
        (Polynomial.C bL) (1 : Polynomial L) Z = 0 := by
      rw [← hpt2, ← htr, hLHS, hz]
    rcases mul_eq_zero.mp h1 with h' | h'
    · exact absurd h' (pow_ne_zero 3 (fun h0 => hwLne (by
        simpa using congrArg (fun p : Polynomial L => p.coeff 0) h0)))
    · exact h'
  -- ## Step 3: rescaling the ratios by `κ_0` is the `λ²`-substitution
  have hA : (fun i => Polynomial.C (Work.MotK.kleinTwRuleA aL bL 1 kap i))
      = fun i => (Polynomial.C (kap 0)) ^(2:ℕ) *
          Work.MotK.kleinTwRuleA (Polynomial.C aL) (Polynomial.C bL) 1
            (fun j => Polynomial.C (kap j / kap 0)) i := by
    rw [Work.MotK.kleinTwRuleA_map (Polynomial.C : L →+* Polynomial L) aL bL 1 kap]
    simp only [Polynomial.C_1]
    have hκ : (fun i : Fin 5 => Polynomial.C (kap i))
        = fun i => (Polynomial.C (kap 0)) * (fun j => Polynomial.C (kap j / kap 0)) i := by
      funext i
      rw [← Polynomial.C_mul]
      congr 1
      exact (mul_div_cancel₀ (kap i) hkap0).symm
    rw [hκ]
    exact (Work.MotK.TwRuling.SdSextHomog (Polynomial.C aL) (Polynomial.C bL)
      1 Polynomial.X).2.2.2.1 (fun j => Polynomial.C (kap j / kap 0))
      (Polynomial.C (kap 0))
  have hB : (fun i => Polynomial.C (Work.MotK.kleinTwRuleB aL bL 1 kap i))
      = fun i => (Polynomial.C (kap 0)) ^(2:ℕ) *
          Work.MotK.kleinTwRuleB (Polynomial.C aL) (Polynomial.C bL) 1
            (fun j => Polynomial.C (kap j / kap 0)) i := by
    rw [Work.MotK.kleinTwRuleB_map (Polynomial.C : L →+* Polynomial L) aL bL 1 kap]
    simp only [Polynomial.C_1]
    have hκ : (fun i : Fin 5 => Polynomial.C (kap i))
        = fun i => (Polynomial.C (kap 0)) * (fun j => Polynomial.C (kap j / kap 0)) i := by
      funext i
      rw [← Polynomial.C_mul]
      congr 1
      exact (mul_div_cancel₀ (kap i) hkap0).symm
    rw [hκ]
    exact (Work.MotK.TwRuling.SdSextHomog (Polynomial.C aL) (Polynomial.C bL)
      1 Polynomial.X).2.2.2.2 (fun j => Polynomial.C (kap j / kap 0))
      (Polynomial.C (kap 0))
  -- ## Step 4: assembly
  have hZt : (fun k => Polynomial.C (Work.MotK.kleinTwRuleA aL bL 1 kap k)
        + ((Polynomial.C wL) * Polynomial.X) *
          Polynomial.C (Work.MotK.kleinTwRuleB aL bL 1 kap k))
      = fun k => (Polynomial.C (kap 0)) ^(2:ℕ) * Z k := by
    rw [hZ]
    funext k
    rw [congrFun hA k, congrFun hB k]
    first | refl_ring1 | ring
  have hsplit : Work.MotK.TwRuling.sdSplitPoly K D h
      = Work.MotK.kleinTwR0 (Polynomial.C aL) (Polynomial.C bL) (1 : Polynomial L)
          (fun k => Polynomial.C (Work.MotK.kleinTwRuleA aL bL 1 kap k)
            + ((Polynomial.C wL) * Polynomial.X) *
              Polynomial.C (Work.MotK.kleinTwRuleB aL bL 1 kap k)) := by
    rw [Work.MotK.TwRuling.sdSplitPoly, Polynomial.C_1]
  rw [hsplit, hZt, Work.MotK.TwRuling.kleinTwR0_homog_aux (Polynomial.C aL)
    (Polynomial.C bL) (1 : Polynomial L) ((Polynomial.C (kap 0)) ^(2:ℕ)) Z, hZ0, mul_zero]

/-- **The evaluation step.**  If the split ruling polynomial (with the parameter scaled by the
Kummer root `sdWL K D h`) vanishes, then the split ruling sextic at the Klein point vanishes for
every scalar `σ : KbG K`. -/
theorem twistedVanishing_of_sdSplitPolyAux {K : Type} [Field K] (D : Work.MotV.KleinData K)
    (h : K) (hh : h ≠ 0) (hz : Work.MotK.TwRuling.sdSplitPoly K D h = 0) :
    ∀ σ : Work.MotK.KbG K, MvPolynomial.aeval (Work.MotV.kleinCoord D (Work.MotK.KbG K))
      (Work.MotK.TwRuling.sdGform (algebraMap K (Work.MotK.KbG K) D.a)
        (algebraMap K (Work.MotK.KbG K) D.b) σ) = 0 := by
  intro σ
  rw [Work.MotK.TwRuling.aeval_sdGform_gen (R := Work.MotK.KbG K) (A := Work.MotK.OmG K D)
    (a := algebraMap K (Work.MotK.KbG K) D.a) (b := algebraMap K (Work.MotK.KbG K) D.b)
    (σ := σ) (x := Work.MotV.kleinCoord D (Work.MotK.KbG K))]
  rw [← IsScalarTower.algebraMap_apply K (Work.MotK.KbG K) (Work.MotK.OmG K D) D.a,
      ← IsScalarTower.algebraMap_apply K (Work.MotK.KbG K) (Work.MotK.OmG K D) D.b]
  simp only [map_one]
  have harg : (fun i : Fin 5 => Work.MotK.kleinTwRuleA (algebraMap K (Work.MotK.OmG K D) D.a)
          (algebraMap K (Work.MotK.OmG K D) D.b) 1 (Work.MotV.kleinCoord D (Work.MotK.KbG K)) i
        + algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) σ *
          Work.MotK.kleinTwRuleB (algebraMap K (Work.MotK.OmG K D) D.a)
            (algebraMap K (Work.MotK.OmG K D) D.b) 1 (Work.MotV.kleinCoord D (Work.MotK.KbG K)) i)
      = (fun i => Work.MotK.kleinTwRuleA (algebraMap K (Work.MotK.OmG K D) D.a)
            (algebraMap K (Work.MotK.OmG K D) D.b) 1 (Work.MotK.TwRuling.sdKbL K D) i
          + (Work.MotK.TwRuling.sdWL K D h *
              (algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) σ /
                Work.MotK.TwRuling.sdWL K D h)) *
            Work.MotK.kleinTwRuleB (algebraMap K (Work.MotK.OmG K D) D.a)
              (algebraMap K (Work.MotK.OmG K D) D.b) 1 (Work.MotK.TwRuling.sdKbL K D) i) := by
    funext i
    rw [mul_div_cancel₀ _ (Work.MotK.TwRuling.sdWL_ne_zero K D hh)]
    rfl
  rw [harg]
  rw [← eval_sdSplitPolyAux D h
    (algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) σ / Work.MotK.TwRuling.sdWL K D h)]
  rw [hz, map_zero]

/-- **The transport input of the `sdCubic` route.**  If the twisted inverse cubic vanishes at the
ruling point `sdW K D h`, then the split ruling sextic vanishes at the Klein point for every
scalar. -/
theorem twistedVanishingAux {K : Type} [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h : K) (hh : h ≠ 0)
    (hzero : Work.MotK.kleinTwR0 (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
        (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
        (algebraMap K (Work.MotK.TGen.sdA K D h) h)
        (Work.MotK.TGen.sdW K D h) = 0) :
    ∀ σ : Work.MotK.KbG K, MvPolynomial.aeval (Work.MotV.kleinCoord D (Work.MotK.KbG K))
      (Work.MotK.TwRuling.sdGform (algebraMap K (Work.MotK.KbG K) D.a)
        (algebraMap K (Work.MotK.KbG K) D.b) σ) = 0 :=
  twistedVanishing_of_sdSplitPolyAux D h hh
    (sdSplitPoly_eq_zero_of_rpEvalAux D hD h hh
      (Work.MotK.TwRuling.rpEval_eq_zero_of_sdW D h hzero))

theorem sdW_kleinTwR_ne_zero_charNeTwo (K : Type) [Field K] (h2 : (2 : K) ≠ 0) (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a) (algebraMap K (Work.MotK.TGen.sdA K D h) D.b) (algebraMap K (Work.MotK.TGen.sdA K D h) h) (Work.MotK.TGen.sdW K D h) ≠ ((0 : Fin 5 → Work.MotK.TGen.sdA K D h)) := by
  classical
  intro h0
  set R := Work.MotK.KbG K with hR
  set Om := WeierstrassCurve.Affine.FunctionField (D.E.baseChange (Work.MotK.KbG K)) with hOm
  haveI : Infinite R := inferInstance
  -- the zeroth component vanishes
  have hcomp : Work.MotK.kleinTwR0 (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
      (algebraMap K (Work.MotK.TGen.sdA K D h) D.b) (algebraMap K (Work.MotK.TGen.sdA K D h) h)
      (Work.MotK.TGen.sdW K D h) = 0 := by
    have hc := congrFun h0 0
    rwa [Work.MotK.kleinTwR_zero, Pi.zero_apply] at hc
  -- the twisted-to-untwisted vanishing
  have hvan : ∀ σ : R, MvPolynomial.aeval (Work.MotV.kleinCoord D R)
      (Work.MotK.TwRuling.sdGform (algebraMap K R D.a) (algebraMap K R D.b) σ) = 0 :=
    twistedVanishingAux D hD h hh hcomp
  -- the mixed characteristic input
  have hab : algebraMap K R D.a * algebraMap K R D.b ≠ 0 := by
    rw [← map_mul]
    exact fun hh0 => hD.ab_ne (RingHom.injective (algebraMap K R) (by rw [hh0, map_zero]))
  have h5ne : (5 : R) = 0 → (algebraMap K R D.b) ^(5:ℕ) ≠ 2 * (algebraMap K R D.a) ^(5:ℕ) := by
    intro h5 hcontra
    have h5K : (5 : K) = 0 := by
      exact RingHom.injective (algebraMap K R) (by rw [map_ofNat, h5, map_zero])
    have hb : D.b ^(5:ℕ) ≠ 2 * D.a ^(5:ℕ) :=
      Work.MotK.TwRuling.good_bFive_ne_charFive K D hD (ringChar_eq_five h5K)
    refine hb ?_
    refine RingHom.injective (algebraMap K R) ?_
    rw [map_pow, map_mul, map_ofNat, map_pow]
    exact hcontra
  have hKernel : ∀ F : MvPolynomial (Fin 5) R, F.IsHomogeneous 6 →
      F ∉ twIdeal6 R (algebraMap K R D.a) (algebraMap K R D.b) 1 →
      MvPolynomial.aeval (Work.MotV.kleinCoord D R) F ≠ 0 := by
    intro F hF hFnot
    refine sexticTw_notMem_kernel R (D.E.baseChange R) (algebraMap K R D.a) (algebraMap K R D.b) 1
      hab one_ne_zero (Work.MotV.kleinCoord D R) ?_ ?_ ?_ F
      ((MvPolynomial.mem_homogeneousSubmodule 6 F).mpr hF) hFnot
    · intro i
      rw [Work.MotV.kleinCoord_eq_sum]
      refine Submodule.sum_mem _ (fun m _ => ?_)
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)
    · obtain ⟨e, he⟩ := hD.spans
      intro m
      rw [show Work.MotK.TwRuling.sdBas (D.E.baseChange R) m = Work.MotV.kleinBas D R m from rfl,
        he R m]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · intro k
      rw [map_one, kleinTwP_one_eq_kleinP]
      rw [← IsScalarTower.algebraMap_apply K R Om D.a,
        ← IsScalarTower.algebraMap_apply K R Om D.b]
      exact hD.klein_eq R k
  have hHom : ∀ σ : R, (Work.MotK.TwRuling.sdGform (algebraMap K R D.a)
      (algebraMap K R D.b) σ).IsHomogeneous 6 := by
    intro σ
    exact (SdSextHomog (algebraMap K R D.a) (algebraMap K R D.b) 1 σ).2.2.1
  have hIdealVan : ∀ F ∈ twIdeal6 R (algebraMap K R D.a) (algebraMap K R D.b) 1,
      MvPolynomial.aeval ![algebraMap K R D.a, 0, -(algebraMap K R D.a),
        -(algebraMap K R D.b), algebraMap K R D.b] F = 0 :=
    twIdeal6_aeval_point (algebraMap K R D.a) (algebraMap K R D.b)
      (fun k => congrFun (SdSextValues (algebraMap K R D.a) (algebraMap K R D.b) 0).2.2.1 k)
  have hEval : ∀ σ : R, MvPolynomial.aeval ![algebraMap K R D.a, 0, -(algebraMap K R D.a),
        -(algebraMap K R D.b), algebraMap K R D.b]
        (Work.MotK.TwRuling.sdGform (algebraMap K R D.a) (algebraMap K R D.b) σ)
      = Polynomial.eval σ (Work.MotK.TwRuling.sdDpoly (algebraMap K R D.a)
          (algebraMap K R D.b)) := by
    intro σ
    rw [aeval_sdGform, eval_sdDpoly]
  have hPoint : ∀ σ : R, Polynomial.eval σ (Work.MotK.TwRuling.sdDpoly (algebraMap K R D.a)
        (algebraMap K R D.b))
      = -((algebraMap K R D.a) ^(3:ℕ) * (algebraMap K R D.b) ^(4:ℕ))
        * Polynomial.eval σ (Work.MotK.TwRuling.sdCubic (algebraMap K R D.a)
            (algebraMap K R D.b)) := by
    intro σ
    rw [eval_sdDpoly, (SdSextValues (algebraMap K R D.a) (algebraMap K R D.b) σ).2.2.2,
      eval_sdCubic]
    refl_ring1
  have h2R : (2 : R) ≠ 0 := by
    intro hh0
    exact h2 (RingHom.injective (algebraMap K R) (by
      rw [map_ofNat (algebraMap K R) 2, hh0, map_zero]))
  exact sdSextForm_generic_ne (R := R) (A := Om) h2R (algebraMap K R D.a) (algebraMap K R D.b)
    hab h5ne (Work.MotV.kleinCoord D R) hKernel hHom hIdealVan hEval hPoint hvan

end Work.MotK.TwRuling
