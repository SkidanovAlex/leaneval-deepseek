import Mathlib
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.AK
import Submission.Work.MotAS.ASRulV2.Defs
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotAS.KleinTwScalarASv
import Submission.Work.MotAS.ASChart2Defs
import Submission.Work.MotAS.ASChartGeo
import Submission.Work.MotAS.CensusAS2Aux
import Submission.Work.MotAS.CensusLinAS
import Submission.Work.MotAS.AzDefs
import Submission.Work.MotAS.ASRulV2M.aeval_sAS_eq_zero_imp
import Submission.Work.MotAS.ASRulV2M.fwVecAS2_three_notMem_x
import Submission.Work.MotAS.ASRulV2.RouteZ
import Submission.Work.MotA.coheight_eq_one_iff
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASRulingMain` — K5 of the AS branch (the ruling presentation of `sAS2`)

## The route (this file)

The AS transposition of `Work.MotK.TGen.STRulingDivMain_of_domain`, but with a strictly *simpler*
final step than the T-route's range-closure argument:

* `y := kleinStereoAS (C a) (C b) (pAS0 K) (chart3 K)` evaluated at the residue field `k = resF K x`
  of the given height-one prime `x ∋ sAS2`;
* `c := kleinPAS (fa) (fb) (fg) y`; by `I1^AS` (`KleinTwScalarASv`) and `sAS2 ∈ x` one has
  `kleinRAS c = 0`, and by homogeneity `kleinRAS ![1, c₁/c₀, c₂/c₀, c₃/c₀, 0] = 0`, i.e. the base
  point `(b₁,b₂,b₃) := (c₁/c₀, c₂/c₀, c₃/c₀)` lies on `V(ZIAS)`; hence `radical ZIAS ⊆ ker ev` for
  `ev = eval ![b₁,b₂,b₃]`, giving `ψ : A →+* k`, `A = K[X] / radical ZIAS`;
* `kernel_basis` (proved) describes `y` as `α • ev(kbRv) + β • ev(kbRw)`; together with the explicit
  chart relation `y_{j+1} = y₄ · f(X j)` (from `kleinStereoAS_pAS0_chart3`, where `y₄ = 2(a²-ab-b²)`)
  this gives `f(X j) = t · ev(kbRv (j+1))/δV + ev(kbRw (j+1))/δW` with `t = y₃/y₄`;
* therefore the ruling presentation
  `θ (X j) = ε⁻¹ · (C (mk (kbRv (j+1))) · T + C (mk (kbRw (j+1))))`, `ε = X₂²(a+2b)²(2a-b)`,
  into `L = (Polynomial A)[1/ε]`, satisfies `σ (θ (X j)) = f (X j)` for the `K`-algebra map
  `σ : L →+* k` evaluating `mk q ↦ ev q` and `T ↦ (a+2b)·t`;
* consequently `k = Frac (σ(L))` (because `k = Frac (f (K[X]))` and `f (K[X]) ⊆ σ(L)`), so the
  induced field map `Frac L → k` is bijective; and `Frac L = FractionRing (Polynomial A)` because
  `ε` is a non-zero-divisor of the domain `A`.  **This needs neither `θ(sAS2) = 0` nor the
  `ThetaFwVec`/range-closure step of the T-route.**

The two outside inputs are the (delegated) non-vanishing facts

* `X 2 ∉ x` (`MotAS.ASRulV2.X2_notMem_x`) and
* `fwVecAS2 · 3 ∉ x` (`MotAS.ASRulV2M.fwVecAS2_three_notMem_x`),

the second being exactly `c₃ ≠ 0`, i.e. `kernel_basis`'s `w ≠ 0` hypothesis (here `w = ev (X 2)`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option maxRecDepth 100000

namespace Work.MotAS

open MvPolynomial

/-- **The AS stereographic source point** `y = kleinStereoAS (C a) (C b) (pAS0 K) (chart3 K)` as a
tuple of polynomials.  `sAS2 a b g` is `kleinSecAS (C a) (C b) (C g) (ASrulYv K a b)` by definition
of `sAS2`. -/
noncomputable def ASrulYv (K : Type*) [CommRing K] (a b : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K) (Work.MotK.chart3 K)

/-- The explicit form of the AS stereographic point: `y i = q(v)·p i + 2(a²-ab-b²)·v i` with
`v = chart3 = (0, X₀, X₁, X₂, 1)` and `p = pAS0 = e₀`. -/
theorem ASrulYv_apply (K : Type*) [Field K] (a b : K) (i : Fin 5) :
    ASrulYv K a b i
      = kleinQAS (MvPolynomial.C a) (MvPolynomial.C b) (Work.MotK.chart3 K) * (pAS0 K i)
        + MvPolynomial.C (2 * (a ^ 2 - a * b - b ^ 2)) * (Work.MotK.chart3 K i) := by
  have h := congrFun (kleinStereoAS_pAS0_chart3 (K := K) a b) i
  simpa [ASrulYv, azA] using h

/-- The fourth coordinate of the AS stereographic point is the constant `2(a²-ab-b²)`. -/
theorem ASrulYv_four (K : Type*) [Field K] (a b : K) :
    ASrulYv K a b 4 = MvPolynomial.C (2 * (a ^ 2 - a * b - b ^ 2)) := by
  rw [ASrulYv_apply]
  simp [pAS0, Work.MotK.chart3]

/-- The `(j+1)`-st coordinate of the AS stereographic point: `y_{j+1} = y₄ · X j`.  This is the AS
analogue of the T-route's `Sklein_chart` (the projection `π_{e₀}` is trivial here). -/
theorem ASrulYv_ch3 (K : Type*) [Field K] (a b : K) (j : Fin 3) :
    ASrulYv K a b (asCh3 j) = ASrulYv K a b 4 * (MvPolynomial.X j) := by
  rw [ASrulYv_apply, ASrulYv_four]
  fin_cases j <;>
    (simp [pAS0, Work.MotK.chart3, asCh3] <;> ring)

/-! ## Linearity of the AS ruling matrix in the base point -/

/-- `AmatAS2` is linear in its base-point argument. -/
theorem AmatAS2_smul {R : Type*} [CommRing R] (a b g c : R) (x : Fin 5 → R) :
    AmatAS2 a b g (c • x) = c • AmatAS2 a b g x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [AmatAS2, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] <;> ring)

/-- The ruling system of a scaled base point. -/
theorem AmatAS2_mulVec_smul {R : Type*} [CommRing R] (a b g c : R) (x y : Fin 5 → R) :
    Matrix.mulVec (AmatAS2 a b g (c • x)) y = c • Matrix.mulVec (AmatAS2 a b g x) y := by
  rw [AmatAS2_smul, Matrix.smul_mulVec]

/-- `AmatAS` (used by `kernel_basis`) is `AmatAS2`. -/
theorem ASRul.AmatAS_eq_AmatAS2 {R : Type*} [CommRing R] (a b g : R) (c : Fin 5 → R) :
    ASRul.AmatAS a b g c = AmatAS2 a b g c := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [ASRul.AmatAS, AmatAS2] <;> ring)

/-! ## Evaluation of the residual-curve cubics -/

/-- The five cubics `zcubAS` of the residual curve, evaluated at a base point `(u,v,w)`, are the
components of `kleinRAS a b g ![1,u,v,w,0]`. -/
theorem zcubAS_eval_eq {K : Type*} [Field K] (a b g : K) (u v w : K) (j : Fin 5) :
    MvPolynomial.eval ![u, v, w] (zcubAS a b g j) = kleinRAS a b g ![1, u, v, w, 0] j := by
  have h := congrFun (KleinTwScalarAS_map_kleinRAS (MvPolynomial.eval ![u, v, w])
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (asBaseVec K)) j
  rw [MvPolynomial.eval_C, MvPolynomial.eval_C, MvPolynomial.eval_C] at h
  have hv : (fun i => (MvPolynomial.eval ![u, v, w]) (asBaseVec K i)) = ![1, u, v, w, 0] := by
    funext i
    fin_cases i <;> simp [asBaseVec, Work.MotK.chart3]
  rw [hv] at h
  have hz : zcubAS a b g j
      = kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (asBaseVec K) j := rfl
  rw [hz]
  exact h.symm

/-- **Homogeneity descent for the base curve**: if `kleinRAS` vanishes at `c₀ • z` with `c₀ ≠ 0`,
it vanishes at `z`.  Used to pass from the un-normalised base point `c = kleinPAS y` to the chart
vector `(1, c₁/c₀, c₂/c₀, c₃/c₀, 0)`. -/
theorem kleinRAS_chart_eq_zero {K : Type*} [Field K] (a b g c0 c1 c2 c3 : K) (hc0 : c0 ≠ 0)
    (h : kleinRAS a b g ![c0, c1, c2, c3, 0] = 0) :
    kleinRAS a b g ![1, c1 / c0, c2 / c0, c3 / c0, 0] = 0 := by
  have hz : (fun i => c0 * (![1, c1 / c0, c2 / c0, c3 / c0, 0] : Fin 5 → K) i)
      = ![c0, c1, c2, c3, 0] := by
    funext i
    fin_cases i <;> (simp <;> field_simp)
  funext i
  have hhom := congrFun (kleinRAS_smul a b g c0 ![1, c1 / c0, c2 / c0, c3 / c0, 0]) i
  rw [hz, h] at hhom
  exact (mul_eq_zero.mp hhom.symm).resolve_left (pow_ne_zero 3 hc0)

/-- **The base point lies on the residual curve**: if `kleinRAS a b g` vanishes at
`(c₀,c₁,c₂,c₃,0)` with `c₀ ≠ 0`, then `(c₁/c₀, c₂/c₀, c₃/c₀)` are common zeros of the five cubics
`zcubAS a b g`.  This is the input of `radical (ZIAS a b g) ≤ RingHom.ker (eval ![u,v,w])`. -/
theorem zcubAS_eval_eq_zero_of_kleinRAS {K : Type*} [Field K] (a b g c0 c1 c2 c3 : K)
    (hc0 : c0 ≠ 0) (h : kleinRAS a b g ![c0, c1, c2, c3, 0] = 0) (j : Fin 5) :
    MvPolynomial.eval ![c1 / c0, c2 / c0, c3 / c0] (zcubAS a b g j) = 0 := by
  rw [zcubAS_eval_eq]
  exact congrFun (kleinRAS_chart_eq_zero a b g c0 c1 c2 c3 hc0 h) j

/-! ## The evaluated normalising coefficients of the ruling vectors -/

/-- The evaluation of the third component of `kbRv`: `(2a-b)(a+2b)·w²`. -/
theorem eval_kbRv_three {K : Type*} [Field K] (a b g u v w : K) :
    MvPolynomial.eval ![u, v, w] (ASRul.kbRv a b g 3)
      = (2 * a - b) * (a + 2 * b) * w ^ 2 := by
  have h : ASRul.kbRv a b g 3
      = MvPolynomial.C (2 * a - b) * MvPolynomial.C (a + 2 * b) * (MvPolynomial.X 2) ^ 2 := by
    simp [ASRul.kbRv]
  rw [h]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] <;> ring

/-- The evaluation of the fourth component of `kbRw`: `(2a-b)(a+2b)²·w²`. -/
theorem eval_kbRw_four {K : Type*} [Field K] (a b g u v w : K) :
    MvPolynomial.eval ![u, v, w] (ASRul.kbRw a b g 4)
      = (2 * a - b) * (a + 2 * b) ^ 2 * w ^ 2 := by
  have h : ASRul.kbRw a b g 4
      = MvPolynomial.C ((a + 2 * b) ^ 2) * MvPolynomial.C (2 * a - b) * (MvPolynomial.X 2) ^ 2 := by
    simp [ASRul.kbRw]
  rw [h]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] <;> ring

/-- `kbRw · 3 = 0`. -/
theorem eval_kbRw_three {K : Type*} [Field K] (a b g u v w : K) :
    MvPolynomial.eval ![u, v, w] (ASRul.kbRw a b g 3) = 0 := by
  rw [ASRul.kbRw]; simp

/-- `kbRv · 4 = 0`. -/
theorem eval_kbRv_four {K : Type*} [Field K] (a b g u v w : K) :
    MvPolynomial.eval ![u, v, w] (ASRul.kbRv a b g 4) = 0 := by
  rw [ASRul.kbRv]; simp

/-! ## `X 2` does not divide `sAS2`, and `X 2 ∉ x`

These use the delegated certificate `Work.MotAS.ASRulV2M.aeval_sAS_eq_zero_imp` (the `T¹⁰`-coefficient
of the specialisation `X₀ ↦ 0, X₁ ↦ T, X₂ ↦ 0` of `sAS` is `288⁵ (a²-ab-b²)¹⁰ ≠ 0`). -/

/-- **`X 2` does not divide the source ruling quintic `sAS2`.** -/
theorem sAS2_not_dvd_X2 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    ¬ (MvPolynomial.X 2 ∣ Work.MotAS.sAS2 (Work.MotAS.aK D) (Work.MotAS.bK D)
        (Work.MotV.fAS 𝕜)) := by
  intro hdvd
  have hdvd' : MvPolynomial.X 2 ∣ Work.MotAS.sAS (Work.MotAS.aK D) (Work.MotAS.bK D)
      (Work.MotV.fAS 𝕜) := by
    obtain ⟨f, hf⟩ := hdvd
    refine ⟨(288 : MvPolynomial (Fin 3) (RatFunc 𝕜)) ^ 5 * f, ?_⟩
    rw [Work.MotAS.sAS_eq_scale, hf]
    refl_ring1
  obtain ⟨f', hf'⟩ := hdvd'
  have hz : (MvPolynomial.aeval
        (fun i : Fin 3 => (![0, Polynomial.X, 0] : Fin 3 → Polynomial (RatFunc 𝕜)) i))
      (Work.MotAS.sAS (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜)) = 0 := by
    rw [hf', map_mul]
    have hX2 : (MvPolynomial.aeval
          (fun i : Fin 3 => (![0, Polynomial.X, 0] : Fin 3 → Polynomial (RatFunc 𝕜)) i))
        (MvPolynomial.X 2 : MvPolynomial (Fin 3) (RatFunc 𝕜)) = 0 := by
      simp [MvPolynomial.aeval_X]
    rw [hX2, zero_mul]
  exact Work.MotAS.aK_sq_sub_ne D hD
    (Work.MotAS.ASRulV2M.aeval_sAS_eq_zero_imp (Work.MotAS.aK D) (Work.MotAS.bK D)
      (Work.MotV.fAS 𝕜) hz)

/-- **`X 2 ∉ x`** for every height-one prime `x ∋ sAS2` (in a polynomial ring over `RatFunc 𝕜`,
height-one primes are principal by `Work.MotA.coheight_eq_one_iff`). -/
theorem X2_notMem_x (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (x : Work.MotA.polySpec (RatFunc 𝕜) 3)
    (hcoh : Order.coheight x = 1)
    (hx : Work.MotAS.sAS2 (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal) :
    (MvPolynomial.X 2 : MvPolynomial (Fin 3) (RatFunc 𝕜)) ∉ x.asIdeal := by
  have hnot := sAS2_not_dvd_X2 𝕜 D hD
  intro hX2
  obtain ⟨p, hpprime, hxeq⟩ := (Work.MotA.coheight_eq_one_iff (RatFunc 𝕜) 3 x).mp hcoh
  have hp_dvd_sAS2 : p ∣ Work.MotAS.sAS2 (Work.MotAS.aK D) (Work.MotAS.bK D)
      (Work.MotV.fAS 𝕜) := by
    have h1 : Work.MotAS.sAS2 (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜)
        ∈ x.asIdeal := hx
    rw [hxeq] at h1
    exact Ideal.mem_span_singleton.mp h1
  have hp_dvd_X2 : p ∣ (MvPolynomial.X 2 : MvPolynomial (Fin 3) (RatFunc 𝕜)) := by
    have h1 : (MvPolynomial.X 2 : MvPolynomial (Fin 3) (RatFunc 𝕜)) ∈ x.asIdeal := hX2
    rw [hxeq] at h1
    exact Ideal.mem_span_singleton.mp h1
  have hassoc : Associated p (MvPolynomial.X 2 : MvPolynomial (Fin 3) (RatFunc 𝕜)) :=
    Prime.associated_of_dvd hpprime (MvPolynomial.X_prime) hp_dvd_X2
  exact hnot (hassoc.dvd_iff_dvd_left.mp hp_dvd_sAS2)

/-! ## Route Z: the residue map, the source chart point in the residue field, and its chart relation

These are the first bricks of the "route Z" of `ASRULLINGMAIN_ROUTE_Z_STATE.md`, which proves the
target without any ruling presentation `θ`: with `k = resF K x`, `f : K[X] →+* k` the residue map,
`y := f ∘ ASrulYv`, the base point `c' := f ∘ fwVecAS2 = kleinPAS y` and `φ : A[T] → k`
(`mk q ↦ ev q` at `(c'₁/c'₀, c'₂/c'₀, c'₃/c'₀)`, `T ↦ (a+2b)·y₃/y₄`), the whole content is
`Subfield.closure (Set.range φ) = ⊤` (from `ASRulV2M.hparam_kernel`) together with `ker φ = ⊥`
(from the dimension bound `ASRulV2M.trdeg_quotient_add_height`). -/

/-- **The residue map** `K[X₀,X₁,X₂] →+* resF K x`. -/
noncomputable def rulF (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (x : Work.MotA.polySpec (RatFunc 𝕜) 3) :
    MvPolynomial (Fin 3) (RatFunc 𝕜) →+* Work.MotV.resF (RatFunc 𝕜) x :=
  (algebraMap (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ x.asIdeal)
      (Work.MotV.resF (RatFunc 𝕜) x)).comp (Ideal.Quotient.mk x.asIdeal)

@[simp] theorem rulF_apply (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (x : Work.MotA.polySpec (RatFunc 𝕜) 3) (p : MvPolynomial (Fin 3) (RatFunc 𝕜)) :
    rulF 𝕜 x p = algebraMap (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ x.asIdeal)
      (Work.MotV.resF (RatFunc 𝕜) x) (Ideal.Quotient.mk x.asIdeal p) := rfl

/-- **The source chart point** `y = f ∘ ASrulYv` at the residue field of `x`. -/
noncomputable def rulY (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (x : Work.MotA.polySpec (RatFunc 𝕜) 3) : Fin 5 → Work.MotV.resF (RatFunc 𝕜) x :=
  fun i => rulF 𝕜 x (ASrulYv (RatFunc 𝕜) (aK D) (bK D) i)

/-- The residue class of the `j`-th coordinate function of the source chart. -/
noncomputable def rulX (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (x : Work.MotA.polySpec (RatFunc 𝕜) 3) (j : Fin 3) : Work.MotV.resF (RatFunc 𝕜) x :=
  algebraMap (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ x.asIdeal) (Work.MotV.resF (RatFunc 𝕜) x)
    (Ideal.Quotient.mk x.asIdeal (MvPolynomial.X j))

/-- The fourth coordinate of the source chart point is the constant `2(a²-ab-b²)`. -/
theorem rulY_four (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (x : Work.MotA.polySpec (RatFunc 𝕜) 3) :
    rulY 𝕜 D x 4 = algebraMap (RatFunc 𝕜) (Work.MotV.resF (RatFunc 𝕜) x)
      (2 * (aK D ^ 2 - aK D * bK D - bK D ^ 2)) := by
  rw [rulY, rulF_apply, ASrulYv_four, MvPolynomial.C_eq_algebraMap,
    Ideal.Quotient.mk_algebraMap]
  rw [IsScalarTower.algebraMap_apply (RatFunc 𝕜)
    (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ x.asIdeal) (Work.MotV.resF (RatFunc 𝕜) x)]

/-- **The chart relation** at the residue field: `y_{j+1} = y₄ · (residue class of X j)`. -/
theorem rulY_ch3 (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (x : Work.MotA.polySpec (RatFunc 𝕜) 3) (j : Fin 3) :
    rulY 𝕜 D x (asCh3 j) = rulY 𝕜 D x 4 * rulX 𝕜 x j := by
  simp only [rulY, rulX, rulF_apply, ASrulYv_ch3, map_mul]

/-- `2 ≠ 0` in `RatFunc 𝕜` for `𝕜` of characteristic `5`. -/
theorem two_ne_zero_ratFunc (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] : (2 : RatFunc 𝕜) ≠ 0 := by
  intro h
  have h1 : (2 : 𝕜) = 0 :=
    (algebraMap 𝕜 (RatFunc 𝕜)).injective (by rw [map_ofNat, h, map_zero])
  have hd : (5 : ℕ) ∣ 2 := (CharP.cast_eq_zero_iff 𝕜 5 2).mp h1
  norm_num at hd

/-- `y 4 = 2(a²-ab-b²) ≠ 0` for `ASGood D`. -/
theorem rulY_four_ne_zero (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (x : Work.MotA.polySpec (RatFunc 𝕜) 3) :
    rulY 𝕜 D x 4 ≠ 0 := by
  haveI : x.asIdeal.IsPrime := x.2
  rw [rulY_four 𝕜 D x]
  intro h
  have h2 : (2 : RatFunc 𝕜) * (aK D ^ 2 - aK D * bK D - bK D ^ 2) = 0 :=
    (algebraMap (RatFunc 𝕜) (Work.MotV.resF (RatFunc 𝕜) x)).injective (by rw [h, map_zero])
  exact mul_ne_zero (two_ne_zero_ratFunc 𝕜) (aK_sq_sub_ne D hD) h2

/-- The base point `c' = f ∘ fwVecAS2` of the ruling through `y` (equal to `kleinPAS y`). -/
noncomputable def rulC (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (x : Work.MotA.polySpec (RatFunc 𝕜) 3) : Fin 5 → Work.MotV.resF (RatFunc 𝕜) x :=
  fun i => rulF 𝕜 x (fwVecAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) i)

/-- **The base point is `kleinPAS` of the source chart point** (naturality of `kleinPAS`). -/
theorem rulC_eq (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (x : Work.MotA.polySpec (RatFunc 𝕜) 3) :
    rulC 𝕜 D x = kleinPAS (rulF 𝕜 x (MvPolynomial.C (aK D)))
      (rulF 𝕜 x (MvPolynomial.C (bK D))) (rulF 𝕜 x (MvPolynomial.C (Work.MotV.fAS 𝕜)))
      (rulY 𝕜 D x) := by
  funext i
  have hY : rulY 𝕜 D x
      = fun j => rulF 𝕜 x (ASrulYv (RatFunc 𝕜) (aK D) (bK D) j) := rfl
  have hfw : fwVecAS2 (aK D) (bK D) (Work.MotV.fAS 𝕜) i
      = kleinPAS (MvPolynomial.C (aK D)) (MvPolynomial.C (bK D))
          (MvPolynomial.C (Work.MotV.fAS 𝕜)) (ASrulYv (RatFunc 𝕜) (aK D) (bK D)) i := rfl
  rw [rulC, hY, hfw]
  exact (congrFun (KleinTwScalarAS_map_kleinPAS (rulF 𝕜 x) (MvPolynomial.C (aK D))
    (MvPolynomial.C (bK D)) (MvPolynomial.C (Work.MotV.fAS 𝕜))
    (ASrulYv (RatFunc 𝕜) (aK D) (bK D))) i).symm

/-- **`rulF p = 0 ↔ p ∈ x`**: the residue map has kernel `x`. -/
theorem rulF_eq_zero_iff (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (x : Work.MotA.polySpec (RatFunc 𝕜) 3) (p : MvPolynomial (Fin 3) (RatFunc 𝕜)) :
    rulF 𝕜 x p = 0 ↔ p ∈ x.asIdeal := by
  haveI : x.asIdeal.IsPrime := x.2
  rw [rulF_apply]
  constructor
  · intro h
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      (IsFractionRing.injective (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ x.asIdeal)
        (Work.MotV.resF (RatFunc 𝕜) x) (by rw [h, map_zero]))
  · intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h, map_zero]

/-- **The forward chart denominator does not vanish at `x`**: `c'₃ ≠ 0`.  This is the load-bearing
non-vanishing input of the ruling-line description (`w ≠ 0` of `ASRulV2M.hparam_kernel`); it is the
theorem `Work.MotAS.ASRulV2M.fwVecAS2_three_notMem_x`, proved in
`Submission/Work/MotAS/Nodes/fwVecAS2ThreeNotMemXProof.lean`. -/
theorem rulC_three_ne_zero (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (x : Work.MotA.polySpec (RatFunc 𝕜) 3)
    (hcoh : Order.coheight x = 1)
    (hx : Work.MotAS.sAS2 (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal) :
    rulC 𝕜 D x 3 ≠ 0 := by
  intro h
  exact Work.MotAS.ASRulV2M.fwVecAS2_three_notMem_x 𝕜 D hD x hcoh hx
    ((rulF_eq_zero_iff 𝕜 x _).mp h)

/-- **`c'₀ ≠ 0`** (the hypothesis `hfw` of the target). -/
theorem rulC_zero_ne_zero (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (x : Work.MotA.polySpec (RatFunc 𝕜) 3)
    (hfw : Work.MotAS.fwVecAS2 (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜)
      0 ∉ x.asIdeal) :
    rulC 𝕜 D x 0 ≠ 0 := by
  intro h
  exact hfw ((rulF_eq_zero_iff 𝕜 x _).mp h)

theorem ASRulingMain (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (x : Work.MotA.polySpec (RatFunc 𝕜) 3)
    (hcoh : Order.coheight x = 1)
    (hx : Work.MotAS.sAS2 (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜) ∈ x.asIdeal)
    (hfw : Work.MotAS.fwVecAS2 (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜) 0 ∉ x.asIdeal)
    (hDZ : IsDomain (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸
      Ideal.radical (Work.MotAS.ZIAS (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜)))) :
    Nonempty (Work.MotV.resF (RatFunc 𝕜) x ≃ₐ[RatFunc 𝕜]
      FractionRing (Polynomial (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸
        Ideal.radical (Work.MotAS.ZIAS (Work.MotAS.aK D) (Work.MotAS.bK D) (Work.MotV.fAS 𝕜))))) := by
  exact Work.MotAS.RouteZ.routeZ_AS 𝕜 D hD x hcoh hx hfw hDZ

end Work.MotAS
