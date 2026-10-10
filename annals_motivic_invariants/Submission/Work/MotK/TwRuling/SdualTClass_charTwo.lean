import Mathlib
import Submission.Work.MotK.TwCensus.SdualTPrime
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.MotK.TGen.KleinTwFibre_eq_ker
import Submission.Work.MotK.CensusBridge.resF_span_eq_ratFunc
import Submission.Work.MotK.TwDataMod5
import Submission.Work.MotK.TGen.ChartSetup
import Submission.Work.MotK.TGen.TwCoordGKleinTw
import Submission.Work.MotK.TwRuling.SdThetaFracTop_charNeTwo
import Submission.Work.MotK.TwCensus.SdualTPrimeGood
import Submission.Work.MotK.TGen.SdualTBrick
import Submission.Work.MotK.TwRuling.sdY_curve
import Submission.Work.MotK.TwCensus.TwistFieldTGRatFuncTrdeg
import Submission.Work.MotK.CensusBridge.isFractionRing_adjoin_range_ratFunc
import Submission.Work.MotK.CensusBridge.height_eq_one_of_trdeg_eq_two
import Submission.Work.MotV.trdeg_fractionRing_mvPolynomial
import Submission.Work.MotK.TwDataMod5
import Submission.Work.MotK.TwRuling.ParamVec
import Submission.Work.MotK.TwRuling.kleinTwR_param
import Submission.Work.MotK.TwRuling.kleinTwR_paramVec_zero_ne_zero
import Submission.Work.MotK.TwRuling.FracClosureParamR

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Work.MotK.TwRuling

open MvPolynomial

/- **The parametrisation of the target ruling divisor in characteristic two.**

`paramVec K D h` is the point with `z 0 = 0`, `z 1 = t`, `z 2 = y 2 + (b/a) h y 4 t`,
`z 3 = (b/a) y 1 + h y 3 t`, `z 4 = 1`, where `y = sdY K D h` are the twisted Klein coordinates
(so `y 0 = 1` and `kleinTwP a b h y = 0`) and `t = RatFunc.X`.  Numerically (exact arithmetic over
`F_64`, seven triples `(a,b,h)`) the map `t ↦ paramVec` lands in the surface `{sdualT = 0}` and
`kleinTwR a b h (paramVec K D h) ∝ y`; this is the characteristic-two replacement for the
degenerate polar presentation `Work.MotK.TGen.sdPhi`.

The definition is in the companion module `Submission.Work.MotK.TwRuling.ParamVec`, imported here
(and re-exported, so the statement of `SdualTClass_charTwo` can mention it). -/

-- CONTEXT.  `Work.MotK.TGen.SdualTClass` (the `sdualT` clause of the census of the T-twisted
-- Crauder--Katz link, needed by `Work.MotK.TGenCensus_wired` -> `Work.MotK.LinkCertT`) is proved from
-- the two statements `Work.MotK.TwRuling.SdThetaKernel` and `Work.MotK.TwRuling.SdThetaFracTop`,
-- *both of which are FALSE in characteristic 2*: there, `kleinTwBilin c (kleinE 0) = -2ab c0 = 0`
-- identically, so the two ruling vectors `A(c)`, `B(c)` are proportional, `sdW = A(y) + t·B(y)` is a
-- scalar multiple of one vector, `sdPhi = sdW(·)/sdW 4` loses its `t`-dependence, and
-- `sdR ⊆ twistFieldTG K D h` has transcendence degree <= 1 while `K[x]/(sdualT)` has degree 2.
-- The char != 2 forms are PROVED (`Work.MotK.TwRuling.SdThetaFracTop_charNeTwo`).
-- So the clause is at present unreachable in characteristic 2, and the challenge's case (c) (finite
-- base field) and case (d) (algebraically closed base field) include characteristic 2.
--
-- *** FIRST STEP: DECIDE THE TRUTH, CHEAPLY. ***  Two reviewers of this statement were "unsure"
-- because its truth in characteristic 2 is open, and both advised a cheap computational check
-- *before* attempting a proof.  sympy is available.  Suggested check: for `(a,b,h) = (1,1,1)` over
-- `F_16`/`F_32`, enumerate the points `c` of the twisted Klein curve (e.g. as
-- `c = kleinTwStereo a b h p v` for `v ∈ Q̃(F_q)`) with `kleinTwP c = 0`, and for each count the
-- `F_q`-points of its fibre `{w ∈ P³ : kleinTwR a b h w ∝ c}` of `kleinTwR`; a generic *rational*
-- fibre has `q+1` points with essentially no fluctuation, whereas positive-genus fibres fluctuate by
-- `±2√q`.  If the fibres are not rational, SAY SO (`declare_false`, with the numerical locus): that
-- would tell the team that the characteristic-2 cases of the challenge need a different route
-- altogether, exactly as characteristic 5 does.  If they are rational, the clause is plausible and
-- the presentation can be built.
--
-- ROUTE (a presentation of the same divisor that avoids the degenerate ruling).
-- Use the twisted I2' (`Work.MotK.KleinTwI2inv`,
-- `kleinTwP k (kleinTwR z) = kleinTwSDualV z * z k`) to identify the surface `{s'(z) = 0}` with
-- `kleinTwR^{-1}({P = 0}) = kleinTwR^{-1}(C_h)`, i.e. the preimage of the *curve* `C_h = V(kleinTwP)`
-- under the cubic rational map `kleinTwR`, and then present that surface by its *fibres* over the
-- base curve: `Work.MotK.TGen.KleinTwFibre_eq_ker` and `Work.MotK.CensusFibre.kleinFibre_eq_ker` are
-- the (proved, characteristic-free) linear-algebra descriptions of the fibres of the forward quadro
-- map, and the analogue for `kleinTwR` is what is needed.  Combine with
-- `Work.MotK.TwCensus.SdualTPrimeGood` for the primality of `(sdualT)` (that result is
-- characteristic-free) and with `Work.MotK.CensusBridge.resF_span_eq_ratFunc` for the
-- residue-field identification.  A naive "cone over `c ↦ [A(c)]`" replacement does NOT work:
-- `sdualT` has the nonzero constant term `-a^5 b^5 h`, so the cone is not contained in the surface.
--
-- The hypotheses are satisfiable in characteristic 2 (`Work.MotK.ExistsKleinData`,
-- `Work.MotT.exists_kleinData_kleinParam` supply `D.Good` in every characteristic != 5).
--
-- *** THE ASSEMBLY (carried out in `SdualTClass_charTwo_of` below). ***  Given the three
-- ingredients
--   (i)  `kleinTwR a b h (paramVec K D h) i = sdY i * kleinTwR a b h (paramVec K D h) 0`  (all `i`),
--   (ii) `kleinTwR a b h (paramVec K D h) 0 ≠ 0`,
--   (iii)`Subfield.closure (range (algebraMap ↥(paramR K D h) (sdA K D h))) = ⊤`,
-- the proof is: `SdualTPrimeGood` gives `Prime (sdualT)`; (i) + the twisted I2'
-- (`kleinTwP k (kleinTwR z) = kleinTwSDualV z * z k`) + `sdY_curve` give that `sdualT` lies in the
-- kernel of `θ = aeval (paramVec · 1,· 2,· 3)` (`sdualT_aeval_paramVec`); (iii) makes `θ.range`
-- (which is `paramR`) have fraction field `sdA`, so its transcendence degree is `2`
-- (`TwistFieldTGRatFuncTrdeg`) and `height (ker θ) = 1` (`height_ker_eq_one`); comparing with the
-- height-one prime `(sdualT)` — Krull's principal ideal theorem — gives `ker θ = (sdualT)`; then
-- `CensusBridge.resF_span_eq_ratFunc` finishes with the fraction-field identification
-- `FractionRing ↥(paramR) ≃ₐ[K] sdA` supplied by `isFractionRing_of_subfield_closure_range`.
/-- **(i) ⟹ `sdualT` vanishes on the parametrisation.**  With `z = paramVec K D h` and the
proportionality of `kleinTwR z` to `sdY` (the characteristic-two parametrisation identity), the
twisted I2' `kleinTwP k (kleinTwR z) = kleinTwSDualV z * z k` together with homogeneity of
`kleinTwP` and the curve equation `sdY_curve K D hD h hh` forces `kleinTwSDualV z = 0`, i.e.
`sdualT` evaluates to zero at `z`.

(The module `Submission.Work.MotK.TwRuling.sdualT_aeval_paramVec` contains the same statement; it is
repeated here with a primed name so that this file remains the root of the import graph.) -/
theorem sdualT_aeval_paramVec' (K : Type) [Field K] (h2 : (2 : K) = 0)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hparam : ∀ i : Fin 5,
      Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
          (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
          (algebraMap K (Work.MotK.TGen.sdA K D h) h)
          (paramVec K D h) i
        = Work.MotK.TGen.sdY K D h i *
          Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
            (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
            (algebraMap K (Work.MotK.TGen.sdA K D h) h)
            (paramVec K D h) 0) :
    MvPolynomial.aeval (fun j : Fin 3 => ![paramVec K D h 1, paramVec K D h 2, paramVec K D h 3] j)
      (Work.MotK.TGen.sdualT D.a D.b h) = 0 := by
  classical
  set z := paramVec K D h with hz
  have h0 : z 0 = 0 := by rw [hz]; simp [paramVec]
  have h4 : z 4 = 1 := by rw [hz]; simp [paramVec]
  have hparam' : ∀ i : Fin 5,
      Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
          (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
          (algebraMap K (Work.MotK.TGen.sdA K D h) h) z i
        = Work.MotK.TGen.sdY K D h i *
          Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
            (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
            (algebraMap K (Work.MotK.TGen.sdA K D h) h) z 0 := by
    intro i; simpa only [hz] using hparam i
  have hR : Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
      (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
      (algebraMap K (Work.MotK.TGen.sdA K D h) h) z
      = fun j => Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
          (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
          (algebraMap K (Work.MotK.TGen.sdA K D h) h) z 0 * Work.MotK.TGen.sdY K D h j := by
    funext j
    rw [hparam' j, mul_comm]
  have hsW : Work.MotK.kleinTwSDualV (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
      (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
      (algebraMap K (Work.MotK.TGen.sdA K D h) h) z = 0 := by
    have hWs : ∀ i, Work.MotK.kleinTwSDualV (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
        (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
        (algebraMap K (Work.MotK.TGen.sdA K D h) h) z * z i = 0 := by
      intro i
      have hI2 := Work.MotK.kleinTwP_kleinTwR_V (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
        (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
        (algebraMap K (Work.MotK.TGen.sdA K D h) h) z i
      rw [← hI2, hR]
      rw [congrFun (Work.MotK.kleinTwP_homog (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
        (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
        (algebraMap K (Work.MotK.TGen.sdA K D h) h)
        (Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
          (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
          (algebraMap K (Work.MotK.TGen.sdA K D h) h) z 0) (Work.MotK.TGen.sdY K D h)) i]
      rw [sdY_curve K D hD h hh i, mul_zero]
    have h4' := hWs 4
    rw [h4, mul_one] at h4'
    exact h4'
  have h1 : MvPolynomial.aeval (fun j : Fin 3 => ![z 1, z 2, z 3] j)
      (Work.MotK.TGen.sdualT D.a D.b h)
      = Work.MotK.kleinTwSDualV (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
          (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
          (algebraMap K (Work.MotK.TGen.sdA K D h) h) z := by
    rw [Work.MotK.TGen.sdualT]
    simp only [Work.MotK.kleinTwSDualV, map_add, map_mul, map_sub, map_pow, map_ofNat,
      MvPolynomial.aeval_C]
    simp only [Work.MotK.chart3]
    simp [h0, h4]
  rw [h1, hsW]

/-- **(ii) The kernel of a `K`-algebra map `K[X₀,X₁,X₂] → F` with two-dimensional image has height
one** (the codimension-one case of the dimension formula). -/
theorem height_ker_eq_one' (K : Type) [Field K] {F : Type} [Field F] [Algebra K F]
    (φ : MvPolynomial (Fin 3) K →ₐ[K] F) (h : Algebra.trdeg K ↥(φ.range) = 2) :
    (RingHom.ker φ).height = 1 := by
  classical
  haveI hp : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have htrA : Algebra.trdeg K (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ) = 2 := by
    have h1 : Algebra.trdeg K
        (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ.rangeRestrict) = 2 := by
      rw [AlgEquiv.trdeg_eq
        (Ideal.quotientKerAlgEquivOfSurjective φ.rangeRestrict_surjective)]
      exact h
    rwa [AlgHom.ker_rangeRestrict φ] at h1
  have htrF : Algebra.trdeg K (FractionRing (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ)) = 2 := by
    haveI : Algebra.IsAlgebraic (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ)
        (FractionRing (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ)) :=
      Work.MotV.isAlgebraic_fractionRing_self _
    have ht := trdeg_add_eq K (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ)
      (A := FractionRing (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ))
    have h0 : Algebra.trdeg (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ)
        (FractionRing (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ)) = 0 := trdeg_eq_zero
    rw [h0, add_zero] at ht
    rw [← ht, htrA]
  exact Work.MotK.CensusBridge.height_eq_one_of_trdeg_eq_two K (RingHom.ker φ) htrF


/-!
# The parametrised ruling point in characteristic two

`Work.MotK.TwRuling.paramVec K D h = ![0, t, y₂ + (b/a) h y₄ t, (b/a) y₁ + h y₃ t, 1]` is the
characteristic-two parametrisation of the target ruling divisor (see
`Submission/Work/MotK/TwRuling/SdualTClass_charTwo.lean`).  The content of this file is that the
inverse cubic map `kleinTwR` is projectively constant along this parametrisation:

  `kleinTwR (paramVec) i = (sdY i) · kleinTwR (paramVec) 0`.

This is *not* the ruling identity `KleinTwRuleEval`: in characteristic `2` the two ruling vectors
`A(y)`, `B(y)` coincide (`kleinTwBilin c (kleinE 0) = -2ab c₀ = 0`), so the ruling "line" of `y`
degenerates to a point and `paramVec` is genuinely *not* on it.  The proof is therefore a direct
certificate: after clearing the denominators by `a` and using the homogeneity
`kleinTwR (c • y) = c³ • kleinTwR y`, the claim becomes the polynomial identity
`R_i(w) - y_i R_0(w) ≡ 0` where `w = ![0, at, a y₂ + b h y₄ t, b y₁ + a h y₃ t, a]`, the relations
being the five twisted Pfaffians `kleinTwP` evaluated at `![1, y₁, y₂, y₃, y₄]`.

Over `ℤ` the cofactor combination carries an exact residual `2 · Q` — the difference vanishes only
modulo `2`.  We record the residual explicitly (`kleinTwR_cert_*` below) so that the Lean proof
never needs `ring` to know that `2 = 0`; the hypothesis `(2 : K) = 0` is applied afterwards.
-/

theorem SdualTClass_charTwo_of (K : Type) [Field K] [Infinite K] (h2 : (2 : K) = 0)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (hparam : ∀ i : Fin 5,
      Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
          (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
          (algebraMap K (Work.MotK.TGen.sdA K D h) h)
          (paramVec K D h) i
        = Work.MotK.TGen.sdY K D h i *
          Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
            (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
            (algebraMap K (Work.MotK.TGen.sdA K D h) h)
            (paramVec K D h) 0)
    (hne : Work.MotK.kleinTwR (algebraMap K (Work.MotK.TGen.sdA K D h) D.a)
          (algebraMap K (Work.MotK.TGen.sdA K D h) D.b)
          (algebraMap K (Work.MotK.TGen.sdA K D h) h)
          (paramVec K D h) 0 ≠ 0)
    (hfrac : Subfield.closure (Set.range (algebraMap ↥(paramR K D h)
      (Work.MotK.TGen.sdA K D h))) = ⊤) :
    ∃ hpr : (Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} :
        Ideal (MvPolynomial (Fin 3) K)).IsPrime,
      Ideal.height (Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} :
        Ideal (MvPolynomial (Fin 3) K)) = 1 ∧
      Nonempty (Work.MotV.resF K ⟨Ideal.span {Work.MotK.TGen.sdualT D.a D.b h}, hpr⟩ ≃ₐ[K]
        RatFunc ↥(Work.MotK.twistFieldTG K D h)) := by
  -- `K` has characteristic two, hence not five
  have hk : ringChar K ≠ 5 := by
    intro h5
    haveI : CharP K 5 := ringChar.eq_iff.mp h5
    have h50 : (5 : K) = 0 := CharP.cast_eq_zero K 5
    have h51 : (5 : K) = 2 * 2 + 1 := by norm_num
    rw [h51, h2, mul_zero, zero_add] at h50
    exact one_ne_zero h50
  have hG : Prime (Work.MotK.TGen.sdualT D.a D.b h) :=
    Work.MotK.TwCensus.SdualTPrimeGood K hk D hD h hh
  -- the parametrising map
  let ψ : Fin 3 → Work.MotK.TGen.sdA K D h :=
    fun j => ![paramVec K D h 1, paramVec K D h 2, paramVec K D h 3] j
  let θ : MvPolynomial (Fin 3) K →ₐ[K] Work.MotK.TGen.sdA K D h := MvPolynomial.aeval ψ
  have hmem : θ (Work.MotK.TGen.sdualT D.a D.b h) = 0 :=
    sdualT_aeval_paramVec' K h2 D hD h hh hparam
  have hrange : θ.range = paramR K D h := by
    show (MvPolynomial.aeval ψ).range = _
    rw [MvPolynomial.aeval_range]
    rfl
  haveI hdom : IsDomain ↥(paramR K D h) := inferInstance
  haveI hFR : IsFractionRing ↥(paramR K D h) (Work.MotK.TGen.sdA K D h) :=
    Work.MotK.CensusBridge.isFractionRing_of_subfield_closure_range (paramR K D h) hfrac
  -- the transcendence degree of the image is two
  have htrdeg : Algebra.trdeg K ↥(θ.range) = 2 := by
    rw [hrange]
    have halg : Algebra.IsAlgebraic ↥(paramR K D h) (FractionRing ↥(paramR K D h)) :=
      Work.MotV.isAlgebraic_fractionRing_self _
    have h0 : Algebra.trdeg ↥(paramR K D h) (FractionRing ↥(paramR K D h)) = 0 :=
      @trdeg_eq_zero _ _ _ _ _ halg
    have ht := trdeg_add_eq K ↥(paramR K D h) (A := FractionRing ↥(paramR K D h))
    rw [h0, add_zero] at ht
    have e : FractionRing ↥(paramR K D h) ≃ₐ[K] Work.MotK.TGen.sdA K D h :=
      (IsFractionRing.algEquivOfAlgEquiv (A := ↥(paramR K D h)) (B := ↥(paramR K D h))
        (K := FractionRing ↥(paramR K D h)) (L := Work.MotK.TGen.sdA K D h)
        (AlgEquiv.refl (R := ↥(paramR K D h)))).restrictScalars K
    rw [ht, AlgEquiv.trdeg_eq e,
      Work.MotK.TwCensus.TwistFieldTGRatFuncTrdeg K D hD h hh]
  have hheight : (RingHom.ker θ).height = 1 := height_ker_eq_one' K θ htrdeg
  have hle : (Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} :
      Ideal (MvPolynomial (Fin 3) K)) ≤ RingHom.ker θ :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hmem)
  have hPprime : (Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} :
      Ideal (MvPolynomial (Fin 3) K)).IsPrime :=
    (Ideal.span_singleton_prime hG.ne_zero).mpr hG
  have hP1 : (Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} :
      Ideal (MvPolynomial (Fin 3) K)).height = 1 := by
    refine Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors ?_ ?_
    · rw [mem_nonZeroDivisors_iff]
      exact ⟨fun y hy => (mul_eq_zero.mp hy).elim (fun hh' => absurd hh' hG.ne_zero) id,
             fun y hy => (mul_eq_zero.mp hy).elim id (fun hh' => absurd hh' hG.ne_zero)⟩
    · intro hunit
      exact hPprime.ne_top (Ideal.span_singleton_eq_top.mpr hunit)
  have hker : RingHom.ker θ = Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} := by
    refine le_antisymm ?_ hle
    by_contra hcon
    haveI : (RingHom.ker θ).IsPrime := RingHom.ker_isPrime θ
    have hne' : (Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} :
        Ideal (MvPolynomial (Fin 3) K)) ≠ RingHom.ker θ :=
      fun hEq => hcon (le_of_eq hEq.symm)
    have hlt : (Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} :
        Ideal (MvPolynomial (Fin 3) K)) < RingHom.ker θ :=
      lt_of_le_of_ne hle hne'
    have hstep := (Ideal.height_le_iff.mp (le_of_eq hheight))
      (Ideal.span {Work.MotK.TGen.sdualT D.a D.b h}) hPprime hlt
    rw [hP1] at hstep
    exact absurd hstep (by norm_num)
  -- the fraction ring identification
  have he : FractionRing ↥(paramR K D h) ≃ₐ[K] Work.MotK.TGen.sdA K D h :=
    (IsFractionRing.algEquivOfAlgEquiv (A := ↥(paramR K D h)) (B := ↥(paramR K D h))
      (K := FractionRing ↥(paramR K D h)) (L := Work.MotK.TGen.sdA K D h)
      (AlgEquiv.refl (R := ↥(paramR K D h)))).restrictScalars K
  -- the codRestricted presentation
  let θR : MvPolynomial (Fin 3) K →ₐ[K] ↥(paramR K D h) :=
    θ.codRestrict (paramR K D h) (fun p => by
      rw [← hrange]
      exact ⟨p, rfl⟩)
  have hsurj : Function.Surjective θR := by
    intro y
    have hy : (y : Work.MotK.TGen.sdA K D h) ∈ θ.range := by
      rw [hrange]; exact y.2
    obtain ⟨p, hp⟩ := hy
    exact ⟨p, Subtype.ext hp⟩
  have hkerR : RingHom.ker θR = Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} := by
    rw [← hker]
    ext p
    simp only [RingHom.mem_ker]
    refine ⟨fun hp => ?_, fun hp => ?_⟩
    · exact Subtype.ext_iff.mp hp
    · exact Subtype.ext_iff.mpr hp
  exact Work.MotK.CensusBridge.resF_span_eq_ratFunc (K := K) (R := ↥(paramR K D h))
    (F := ↥(Work.MotK.twistFieldTG K D h)) θR (Work.MotK.TGen.sdualT D.a D.b h)
    hG.ne_zero hkerR hsurj he

theorem SdualTClass_charTwo (K : Type) [Field K] [Infinite K] (h2 : (2 : K) = 0)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    ∃ hpr : (Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} :
        Ideal (MvPolynomial (Fin 3) K)).IsPrime,
      Ideal.height (Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} :
        Ideal (MvPolynomial (Fin 3) K)) = 1 ∧
      Nonempty (Work.MotV.resF K ⟨Ideal.span {Work.MotK.TGen.sdualT D.a D.b h}, hpr⟩ ≃ₐ[K]
        RatFunc ↥(Work.MotK.twistFieldTG K D h)) :=
  SdualTClass_charTwo_of K h2 D hD h hh
    (kleinTwR_param K h2 D hD h hh)
    (kleinTwR_paramVec_zero_ne_zero K h2 D hD h hh)
    (frac_closure_paramR K h2 D hD h hh
      (kleinTwR_param K h2 D hD h hh)
      (kleinTwR_paramVec_zero_ne_zero K h2 D hD h hh))

end Work.MotK.TwRuling
