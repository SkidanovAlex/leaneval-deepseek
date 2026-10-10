import Mathlib
import Submission.Work.MotAS.SdualAS2Defs
import Submission.Work.MotAS.TwistField
import Submission.Work.MotAS.twistFieldAS_eq
import Submission.Work.MotAS.asY0_curve
import Submission.Work.MotAS.map_asRuleQW
import Submission.Work.MotAS.ASRulDefs
import Submission.Work.MotAS.asW0Defs
import Submission.Work.MotAS.asW0Aux2
import Submission.Work.MotAS.asW0Aux4
import Submission.Work.MotAS.asW0CertA
import Submission.Work.MotAS.asW0CertB2
import Submission.Work.MotAS.asW0CertC
import Submission.Work.MotAS.ASChart3.asTwY_mem_span
import Submission.Work.MotK.TwRuling.sdW_four_ne_zero
import Submission.Work.MotV5.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.MotV5.ASLocal.asPhi2_denom` — the chart-`2` normalising coordinate is nonzero

The target is `asRuleQW a b g c RatFunc.X 0 ≠ 0` in `R = RatFunc ↥(twistFieldAS D (fAS 𝕜))`,
where `c = algebraMap ∘ asY0 D (fAS 𝕜)` is the generic point of the AS-twisted Klein curve.  Since
`asRuleQW a b g c t = A(c) + t·B(c)` with `A = asRuleQA a b g c · 0`, `B = asRuleQB a b g c · 0`
and `t = RatFunc.X` transcendental over the base field, it suffices to show `B(c) ≠ 0`.

`B` is a quadratic form in the curve coordinates.  The proof is the "kernel of the multiplication
map" argument of `Work.MotK.TwRuling.SdWfour` / `Work.MotAS.ASChart3.QAform_ne_zero`:

* for `κ := asTwY D g` (in `Om D = L(E)` over the base field `Kb 𝕜`), the fifteen pair monomials
  `κ (pfA q) * κ (pfB q)` span the ten-dimensional space `L(10·O)`, so the multiplication map
  `Φ κ : (Kb 𝕜)^15 → L(E)`, `d ↦ ∑ q d q • κ (pfA q) κ (pfB q)`, has a `5`-dimensional kernel;
* the five coefficient vectors `cPAS a b g k` of the AS Pfaffians `kleinPAS` lie in that kernel
  (because `asTwY D g` lies on the twisted Klein curve) and are linearly independent, so they span
  it;
* the certificate functional `psiAS a b` annihilates all five Pfaffians but takes the nonzero value
  `-2a²b(a²-ab-b²)` on the coefficient vector `cB a b g` of `B`; hence `cB ∉ ker Φ κ`, that is
  `B(asTwY D g) ≠ 0` (over `Kb 𝕜`, `a b ≠ 0`, `a² - ab - b² ≠ 0`).

Descending to the twist field `T = ↥(twistFieldAS D g)` uses that `asY0` is the normalisation
`y_j / y_0` of `asTwY` and that `B` is homogeneous of degree `2`; the final step in `RatFunc T` uses
that `algebraMap T (RatFunc T) a + RatFunc.X * algebraMap T (RatFunc T) b` is nonzero as soon as
`b ≠ 0` (`RatFunc.X` is transcendental over `T`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.MotV5.ASLocal

open WeierstrassCurve WeierstrassCurve.Affine
open Work.MotK.TwRuling
open Work.MotK.TwRuling.SdWfour

/-! ## §0 Components and homogeneity of the chart-`2` ruling vector `asRuleQB`

`asRuleQB a b g c 0` is the quadratic form `b^AS_{q}(c, asTanQ c 2)` of the AS invariant quadric
`kleinQAS = -kleinPAS4`.  Everything here is an explicit polynomial identity; the only point to
notice is that `asTanQ` and `kleinBilinAS` are `ℝ`-linear in their point argument, so that the
quadratic form is homogeneous of degree `2`. -/

/-- The zeroth component of `asRuleQB` is the polar form of `kleinPAS0` in the tangent
direction `asTanQ · 2`. -/
theorem asRuleQB_zero_eq {R : Type*} [CommRing R] (a b g : R) (c : Fin 5 → R) :
    Work.MotAS.asRuleQB a b g c 0
      = Work.MotAS.kleinBilinAS0 a b g c (Work.MotAS.asTanQ a b c 2) := by
  simp only [Work.MotAS.asRuleQB, Work.MotAS.asPolarP, Work.MotAS.kleinPAS_apply_zero,
    Work.MotAS.kleinBilinAS0]

/-- `kleinPAS0` is homogeneous of degree `2`. -/
theorem kleinPAS0_smul {R : Type*} [CommRing R] (a b g lam : R) (y : Fin 5 → R) :
    Work.MotAS.kleinPAS0 a b g (lam • y) = lam ^ 2 * Work.MotAS.kleinPAS0 a b g y := by
  simp only [Work.MotAS.kleinPAS0, Pi.smul_apply, smul_eq_mul]
  refl_ring1

/-- `kleinQAS` is homogeneous of degree `2`. -/
theorem kleinQAS_smul {R : Type*} [CommRing R] (a b lam : R) (y : Fin 5 → R) :
    Work.MotAS.kleinQAS a b (lam • y) = lam ^ 2 * Work.MotAS.kleinQAS a b y := by
  simp only [Work.MotAS.kleinQAS, Pi.smul_apply, smul_eq_mul]
  refl_ring1

/-- `kleinBilinAS` is linear in its first argument. -/
theorem kleinBilinAS_smul {R : Type*} [CommRing R] (a b lam : R) (u v : Fin 5 → R) :
    Work.MotAS.kleinBilinAS a b (lam • u) v = lam * Work.MotAS.kleinBilinAS a b u v := by
  simp only [Work.MotAS.kleinBilinAS, Work.MotAS.kleinQAS, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  refl_ring1

/-- The tangent vector is linear in the point. -/
theorem asTanQ_smul {R : Type*} [CommRing R] (a b lam : R) (c : Fin 5 → R) (k : Fin 5) :
    Work.MotAS.asTanQ a b (lam • c) k = lam • Work.MotAS.asTanQ a b c k := by
  funext i
  simp only [Work.MotAS.asTanQ, Pi.smul_apply, smul_eq_mul]
  rw [kleinBilinAS_smul a b lam c (Work.MotK.kleinE k),
    kleinBilinAS_smul a b lam c (Work.MotK.kleinE 4)]
  refl_ring1

/-- `kleinBilinAS0` is homogeneous of degree `2`. -/
theorem kleinBilinAS0_smul {R : Type*} [CommRing R] (a b g lam : R) (u v : Fin 5 → R) :
    Work.MotAS.kleinBilinAS0 a b g (lam • u) (lam • v)
      = lam ^ 2 * Work.MotAS.kleinBilinAS0 a b g u v := by
  have h : lam • u + lam • v = lam • (u + v) := (smul_add lam u v).symm
  rw [Work.MotAS.kleinBilinAS0, h, Work.MotAS.kleinBilinAS0, kleinPAS0_smul, kleinPAS0_smul,
    kleinPAS0_smul]
  refl_ring1

/-- **Homogeneity of the chart-`2` ruling vector**: `asRuleQB · 0` is a quadratic form. -/
theorem asRuleQB_smul_zero {R : Type*} [CommRing R] (a b g lam : R) (c : Fin 5 → R) :
    Work.MotAS.asRuleQB a b g (lam • c) 0 = lam ^ 2 * Work.MotAS.asRuleQB a b g c 0 := by
  rw [asRuleQB_zero_eq, asRuleQB_zero_eq, asTanQ_smul]
  exact kleinBilinAS0_smul a b g lam c (Work.MotAS.asTanQ a b c 2)

/-! ## §1 Transcendence of `RatFunc.X` over the coefficient field -/

/-- `RatFunc.C a + RatFunc.X * RatFunc.C b` is nonzero as soon as `b ≠ 0`: `RatFunc.X` is
transcendental over `F`. -/
theorem ratFunc_C_add_X_mul_C_ne_zero_of_right {F : Type*} [Field F] {a b : F} (hb : b ≠ 0) :
    RatFunc.C a + RatFunc.X * RatFunc.C b ≠ 0 := by
  intro h0
  have hX : (algebraMap (Polynomial F) (RatFunc F)) Polynomial.X = RatFunc.X :=
    RatFunc.algebraMap_X
  have hCa : (algebraMap (Polynomial F) (RatFunc F)) (Polynomial.C a) = RatFunc.C a := by
    change (algebraMap (Polynomial F) (RatFunc F)) ((algebraMap F (Polynomial F)) a) = RatFunc.C a
    rw [← IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F), RatFunc.algebraMap_eq_C]
  have hCb : (algebraMap (Polynomial F) (RatFunc F)) (Polynomial.C b) = RatFunc.C b := by
    change (algebraMap (Polynomial F) (RatFunc F)) ((algebraMap F (Polynomial F)) b) = RatFunc.C b
    rw [← IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F), RatFunc.algebraMap_eq_C]
  have h2 : (algebraMap (Polynomial F) (RatFunc F))
      (Polynomial.C a + Polynomial.X * Polynomial.C b) = 0 := by
    rw [map_add, map_mul, hCa, hCb, hX, h0]
  have h3 : Polynomial.C a + Polynomial.X * Polynomial.C b = 0 :=
    IsFractionRing.injective (Polynomial F) (RatFunc F) (by rw [h2, map_zero])
  have h4 : (Polynomial.C a + Polynomial.X * Polynomial.C b).coeff 1 = 0 := by
    rw [h3, Polynomial.coeff_zero]
  exact hb (by simpa using h4)

/-- The `algebraMap` form of the same statement. -/
theorem ratFunc_algebraMap_add_X_mul_ne_zero {F : Type*} [Field F] {a b : F} (hb : b ≠ 0) :
    algebraMap F (RatFunc F) a + RatFunc.X * algebraMap F (RatFunc F) b ≠ 0 := by
  rw [RatFunc.algebraMap_eq_C]
  exact ratFunc_C_add_X_mul_C_ne_zero_of_right hb

/-! ## §2 The coefficient vectors of the AS Pfaffians and of `asRuleQB · 0` -/

/-- **`Φ` of the coefficient vector of the `k`-th AS Pfaffian is that Pfaffian.** -/
theorem Phi_cPAS_eq {R : Type} [Field R] {E : WeierstrassCurve R} (a b g : R)
    (kappa : Fin 5 → Affine.FunctionField E) (k : Fin 5) :
    SdWfour.Phi kappa (Work.MotAS.cPAS a b g k)
      = Work.MotAS.kleinPAS (algebraMap R (Affine.FunctionField E) a)
          (algebraMap R (Affine.FunctionField E) b)
          (algebraMap R (Affine.FunctionField E) g) kappa k := by
  rw [← Work.MotAS.cPAS_sum (algebraMap R (Affine.FunctionField E) a)
        (algebraMap R (Affine.FunctionField E) b) (algebraMap R (Affine.FunctionField E) g)
        kappa k]
  change (∑ q : Fin 5 × Fin 3,
      Work.MotAS.cPAS a b g k q • (kappa (pfA q) * kappa (pfB q)))
    = ∑ q : Fin 5 × Fin 3,
        Work.MotAS.cPAS (algebraMap R (Affine.FunctionField E) a)
          (algebraMap R (Affine.FunctionField E) b) (algebraMap R (Affine.FunctionField E) g)
          k q * (kappa (pfA q) * kappa (pfB q))
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Work.MotAS.Cert.map_cPAS (algebraMap R (Affine.FunctionField E)) a b g k q,
    Algebra.smul_def]

/-- **`Φ` of the coefficient vector of `asRuleQB · 0` is `asRuleQB · 0`.** -/
theorem Phi_cB_eq {R : Type} [Field R] {E : WeierstrassCurve R} (a b g : R)
    (kappa : Fin 5 → Affine.FunctionField E) :
    SdWfour.Phi kappa (Work.MotAS.cB a b g)
      = Work.MotAS.asRuleQB (algebraMap R (Affine.FunctionField E) a)
          (algebraMap R (Affine.FunctionField E) b)
          (algebraMap R (Affine.FunctionField E) g) kappa 0 := by
  rw [← Work.MotAS.asW0_cB_sum (algebraMap R (Affine.FunctionField E) a)
        (algebraMap R (Affine.FunctionField E) b) (algebraMap R (Affine.FunctionField E) g)
        kappa]
  change (∑ q : Fin 5 × Fin 3,
      Work.MotAS.cB a b g q • (kappa (pfA q) * kappa (pfB q)))
    = ∑ q : Fin 5 × Fin 3,
        Work.MotAS.cB (algebraMap R (Affine.FunctionField E) a)
          (algebraMap R (Affine.FunctionField E) b) (algebraMap R (Affine.FunctionField E) g)
          q * (kappa (pfA q) * kappa (pfB q))
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [Work.MotAS.Cert.map_cB (algebraMap R (Affine.FunctionField E)) a b g q,
    Algebra.smul_def]

/-! ## §3 The core non-degeneracy: the multiplication map on the fifteen pairs -/

/-- **Core non-degeneracy.**  For a field `R`, a Weierstrass curve `E` over `R`, `a b g ∈ R` with
`a b ≠ 0`, `a² - ab - b² ≠ 0`, and `κ` in the function field whose span is that of `1, x, y, x², xy`
and on which the five AS Pfaffians vanish, the quadratic form
`asRuleQB (algebraMap a) (algebraMap b) (algebraMap g) κ 0` is nonzero.

The proof is the "kernel of the multiplication map" argument: `Φ κ` has range `L(10·O)` of dimension
`10`, hence a `5`-dimensional kernel, which is spanned by the five coefficient vectors `cPAS a b g k`
of the AS Pfaffians (they lie in the kernel by `Phi_cPAS_eq`, and are linearly independent).  The
certificate functional `psiAS a b` annihilates all five, but takes the value `-2a²b(a²-ab-b²) ≠ 0`
on the coefficient vector `cB a b g`, so `cB` is not in the kernel. -/
theorem cB_notMem_ker_Phi {R : Type} [Field R] {E : WeierstrassCurve R} (a b g : R)
    (h2 : (2 : R) ≠ 0) (hδ : a ^ 2 - a * b - b ^ 2 ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (h5 : (5 : R) = 0)
    (kappa : Fin 5 → Affine.FunctionField E)
    (hκmem : ∀ i : Fin 5, kappa i ∈ Submodule.span R (Set.range (sdBas E)))
    (hspans : ∀ m : Fin 5, sdBas E m ∈ Submodule.span R (Set.range kappa))
    (hκ : ∀ k : Fin 5, Work.MotAS.kleinPAS (algebraMap R (Affine.FunctionField E) a)
      (algebraMap R (Affine.FunctionField E) b)
      (algebraMap R (Affine.FunctionField E) g) kappa k = 0) :
    Work.MotAS.cB a b g ∉ (SdWfour.Phi kappa).ker := by
  have hker : (SdWfour.Phi kappa).ker = Submodule.span R (Set.range (Work.MotAS.cPAS a b g)) := by
    refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      refine LinearMap.mem_ker.mpr ?_
      rw [Phi_cPAS_eq, hκ k]
    · rw [finrank_span_eq_card (Work.MotAS.Cert.linearIndependent_cPAS a b g hδ h2),
        SdWfour.finrank_ker kappa hκmem hspans, Fintype.card_fin]
  intro hmem
  rw [hker] at hmem
  obtain ⟨mu, hmu⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hmem
  let ψ : (Fin 5 × Fin 3 → R) →ₗ[R] R :=
    { toFun := fun c => ∑ q, Work.MotAS.psiAS a b q * c q
      map_add' := by
        intro x y
        simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro r x
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
        refine Finset.sum_congr rfl (fun q _ => ?_)
        ring }
  have hψcB : ψ (Work.MotAS.cB a b g) = -2 * a ^ 2 * b * (a ^ 2 - a * b - b ^ 2) := by
    change (∑ q, Work.MotAS.psiAS a b q * Work.MotAS.cB a b g q) = _
    rw [Work.MotAS.psiAS_cB, h5, zero_mul, add_zero]
  have hψcPAS : ∀ k : Fin 5, ψ (Work.MotAS.cPAS a b g k) = 0 := by
    intro k
    change (∑ q, Work.MotAS.psiAS a b q * Work.MotAS.cPAS a b g k q) = 0
    rw [Work.MotAS.psiAS_cPAS, h5, zero_mul]
  have hkey : ψ (Work.MotAS.cB a b g) = ∑ k : Fin 5, mu k * ψ (Work.MotAS.cPAS a b g k) := by
    conv_lhs => rw [← hmu]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [map_smul, smul_eq_mul]
  rw [Finset.sum_eq_zero (fun k _ => by rw [hψcPAS k, mul_zero]), hψcB] at hkey
  have hprod : (2 : R) * a ^ 2 * b * (a ^ 2 - a * b - b ^ 2) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h2 (pow_ne_zero 2 ha)) hb) hδ
  have hzero : (2 : R) * a ^ 2 * b * (a ^ 2 - a * b - b ^ 2) = 0 := by
    have h := hkey
    rw [show (-2 : R) * a ^ 2 * b * (a ^ 2 - a * b - b ^ 2)
        = -((2 : R) * a ^ 2 * b * (a ^ 2 - a * b - b ^ 2)) from by ring] at h
    exact neg_eq_zero.mp h
  exact hprod hzero

/-- **Non-vanishing of the chart-`2` ruling form at the generic curve point `asTwY D g`** (in the
function field `Om D` over the algebraic closure of `RatFunc 𝕜`). -/
theorem asRuleQB_asTwY_ne_zero {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜) :
    Work.MotAS.asRuleQB (algebraMap 𝕜 (Work.MotV.Om D) D.a)
      (algebraMap 𝕜 (Work.MotV.Om D) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g)
      (Work.MotAS.asTwY D g) 0 ≠ 0 := by
  classical
  have h5R : (5 : Work.MotV.Kb 𝕜) = 0 := Work.MotAS.five_eq_zero_Kb 𝕜
  have h2R : (2 : Work.MotV.Kb 𝕜) ≠ 0 := by
    intro hh
    have h1 : (1 : Work.MotV.Kb 𝕜) = 0 := by
      have h52 : (5 : Work.MotV.Kb 𝕜) = 2 * 2 + 1 := by norm_num
      rw [h52, hh, mul_zero, zero_add] at h5R
      exact h5R
    exact one_ne_zero h1
  have hδ : (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a) ^ 2
      - (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a) * (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b)
      - (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b) ^ 2 ≠ 0 := by
    intro h
    exact hD.2.2.2 (RingHom.injective (algebraMap 𝕜 (Work.MotV.Kb 𝕜))
      (by simpa only [map_sub, map_mul, map_pow, map_zero] using h))
  have ha0 : D.a ≠ 0 := fun h => hD.1.ab_ne (by rw [h, zero_mul])
  have hb0 : D.b ≠ 0 := fun h => hD.1.ab_ne (by rw [h, mul_zero])
  have hAne : algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a ≠ 0 :=
    fun h => ha0 (RingHom.injective (algebraMap 𝕜 (Work.MotV.Kb 𝕜)) (by rw [h, map_zero]))
  have hBne : algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b ≠ 0 :=
    fun h => hb0 (RingHom.injective (algebraMap 𝕜 (Work.MotV.Kb 𝕜)) (by rw [h, map_zero]))
  have hκmem : ∀ i : Fin 5, Work.MotAS.asTwY D g i ∈ Submodule.span (Work.MotV.Kb 𝕜)
      (Set.range (Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotV.Kb 𝕜)))) :=
    fun i => Work.MotAS.ASChart3.asTwY_mem_span 𝕜 D g i
  have hspans : ∀ m : Fin 5, Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotV.Kb 𝕜)) m
      ∈ Submodule.span (Work.MotV.Kb 𝕜) (Set.range (Work.MotAS.asTwY D g)) := by
    obtain ⟨e, he⟩ := hD.1.spans
    intro m
    rw [show Work.MotK.TwRuling.sdBas (D.E.baseChange (Work.MotV.Kb 𝕜)) m
        = Work.MotV.kleinBas D (Work.MotV.Kb 𝕜) m from rfl, he (Work.MotV.Kb 𝕜) m]
    refine Submodule.sum_mem _ (fun i _ => ?_)
    rw [show Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i = Work.MotAS.asKap D i from rfl,
      ← Algebra.smul_def]
    refine Submodule.smul_mem _ _ ?_
    have h := congrFun (Work.MotAS.asMO_mulVec_asTwY D g) i
    rw [← h, Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ (fun j _ => ?_)
    rw [show Work.MotAS.asMO D g i j
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)
            (Work.MotAS.asM (Work.MotV5.asRoot g) i j) from rfl, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hκ : ∀ k : Fin 5, Work.MotAS.kleinPAS (algebraMap 𝕜 (Work.MotV.Om D) D.a)
      (algebraMap 𝕜 (Work.MotV.Om D) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g)
      (Work.MotAS.asTwY D g) k = 0 :=
    fun k => congrFun (Work.MotAS.asTwY_kleinPAS D hD g) k
  have hnot := cB_notMem_ker_Phi (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.a)
    (algebraMap 𝕜 (Work.MotV.Kb 𝕜) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g)
    h2R hδ hAne hBne h5R (Work.MotAS.asTwY D g) hκmem hspans hκ
  intro h0
  exact hnot (by
    rw [LinearMap.mem_ker, Phi_cB_eq]
    rw [← IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) D.a,
      ← IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) D.b,
      ← IsScalarTower.algebraMap_apply (RatFunc 𝕜) (Work.MotV.Kb 𝕜) (Work.MotV.Om D) g]
    exact h0)

/-! ## §4 Descent to the twist field -/

/-- **Non-vanishing of the chart-`2` ruling form at the generic point `asY0 D g` of the twisted
Klein curve** (in the twist field `↥(twistFieldAS D g)`).

Suppose `asRuleQB a b g (asY0 D g) 0 = 0`.  Mapping into `Om D` and using naturality of `asRuleQB`,
the point `asY0 D g` becomes `(asTwY D g 0)⁻¹ • asTwY D g`; homogeneity of degree `2` and
`asTwY D g 0 ≠ 0` then give `asRuleQB a b g (asTwY D g) 0 = 0`, contradicting
`asRuleQB_asTwY_ne_zero`. -/
theorem asRuleQB_asY0_ne_zero {𝕜 : Type} [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (g : RatFunc 𝕜) :
    Work.MotAS.asRuleQB (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.a)
      (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.b)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g) g)
      (Work.MotAS.asY0 D g) 0 ≠ 0 := by
  have hOm := asRuleQB_asTwY_ne_zero D hD g
  intro hB
  have towerA : algebraMap 𝕜 (Work.MotV.Om D) D.a
      = algebraMap ↥(Work.MotAS.twistFieldAS D g) (Work.MotV.Om D)
          (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.a) := by
    rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) D.a,
      IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g)
        (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.a),
      ← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g) D.a]
  have towerB : algebraMap 𝕜 (Work.MotV.Om D) D.b
      = algebraMap ↥(Work.MotAS.twistFieldAS D g) (Work.MotV.Om D)
          (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.b) := by
    rw [IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) (Work.MotV.Om D) D.b,
      IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g)
        (Work.MotV.Om D) (algebraMap 𝕜 (RatFunc 𝕜) D.b),
      ← IsScalarTower.algebraMap_apply 𝕜 (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g) D.b]
  have towerG : algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g
      = algebraMap ↥(Work.MotAS.twistFieldAS D g) (Work.MotV.Om D)
          (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g) g) :=
    IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g) (Work.MotV.Om D) g
  have hpt : (fun j => algebraMap ↥(Work.MotAS.twistFieldAS D g) (Work.MotV.Om D)
        (Work.MotAS.asY0 D g j))
      = (Work.MotAS.asTwY D g 0)⁻¹ • Work.MotAS.asTwY D g := by
    funext j
    show algebraMap ↥(Work.MotAS.twistFieldAS D g) (Work.MotV.Om D) (Work.MotAS.asY0 D g j)
      = (Work.MotAS.asTwY D g 0)⁻¹ * Work.MotAS.asTwY D g j
    rw [show algebraMap ↥(Work.MotAS.twistFieldAS D g) (Work.MotV.Om D) (Work.MotAS.asY0 D g j)
        = ((Work.MotAS.asY0 D g j : ↥(Work.MotAS.twistFieldAS D g)) : Work.MotV.Om D)
        from rfl,
      show ((Work.MotAS.asY0 D g j : ↥(Work.MotAS.twistFieldAS D g)) : Work.MotV.Om D)
        = Work.MotAS.asTwY D g j / Work.MotAS.asTwY D g 0 from rfl,
      div_eq_mul_inv, mul_comm]
  have key : Work.MotAS.asRuleQB (algebraMap 𝕜 (Work.MotV.Om D) D.a)
      (algebraMap 𝕜 (Work.MotV.Om D) D.b) (algebraMap (RatFunc 𝕜) (Work.MotV.Om D) g)
      (fun j => algebraMap ↥(Work.MotAS.twistFieldAS D g) (Work.MotV.Om D)
        (Work.MotAS.asY0 D g j)) 0 = 0 := by
    have h1 : algebraMap ↥(Work.MotAS.twistFieldAS D g) (Work.MotV.Om D)
        (Work.MotAS.asRuleQB (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.a)
          (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.b)
          (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g) g)
          (Work.MotAS.asY0 D g) 0) = 0 := by rw [hB, map_zero]
    rw [Work.MotAS.map_asRuleQB (algebraMap ↥(Work.MotAS.twistFieldAS D g) (Work.MotV.Om D))
      (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.a)
      (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D g) D.b)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D g) g)
      (Work.MotAS.asY0 D g) 0] at h1
    rw [← towerA, ← towerB, ← towerG] at h1
    exact h1
  rw [hpt, asRuleQB_smul_zero] at key
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h (pow_ne_zero 2 (inv_ne_zero (Work.MotAS.asTwY_zero_ne_zero D g hD.1)))
  · exact hOm h

/-! ## §5 The final assembly in `RatFunc ↥(twistFieldAS D g)` -/

/-- Chart-2 normalising coordinate: `W 0 ≠ 0`, where `W = asRuleQW a b g c X`, `c = algebraMap ∘ asY0 D g`.  This is the input `asPhi2` needs to be well posed; its chart-3 twin `Work.MotAS.ASChart3.asW3_four_ne_zero` is proved (`Submission/Work/MotAS/ASChart3/asW3_four_ne_zero.lean`) and is the template; see also the proved T-analogue `Work.MotK.TwRuling.sdW_four_ne_zero` and `Submission/Work/MotV5/ASLocal/GUIDE_chart2_holes.md`. -/
theorem asPhi2_denom (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) :
    Work.MotAS.asRuleQW (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.a)
      (algebraMap 𝕜 (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.b)
      (algebraMap (RatFunc 𝕜) (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) (Work.MotV.fAS 𝕜))
      (fun j => algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
        (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜) j))
      (RatFunc.X : RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) 0 ≠ 0 := by
  have hB : Work.MotAS.asRuleQB
      (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.a)
      (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.b)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) (Work.MotV.fAS 𝕜))
      (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜)) 0 ≠ 0 :=
    asRuleQB_asY0_ne_zero D hD (Work.MotV.fAS 𝕜)
  set_option synthInstance.maxHeartbeats 800000 in
  rw [IsScalarTower.algebraMap_apply 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
        (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.a,
    IsScalarTower.algebraMap_apply 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
        (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) D.b,
    IsScalarTower.algebraMap_apply (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
        (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) (Work.MotV.fAS 𝕜)]
  rw [show Work.MotAS.asRuleQW
        (algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
          (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
          (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.a))
        (algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
          (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
          (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.b))
        (algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
          (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
          (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) (Work.MotV.fAS 𝕜)))
        (fun j => algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
          (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜) j))
        (RatFunc.X : RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) 0
      = Work.MotAS.asRuleQA
          (algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
            (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
            (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.a))
          (algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
            (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
            (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.b))
          (algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
            (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
            (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) (Work.MotV.fAS 𝕜)))
          (fun j => algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
            (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜) j)) 0
        + (RatFunc.X : RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) * Work.MotAS.asRuleQB
          (algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
            (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
            (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.a))
          (algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
            (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
            (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.b))
          (algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
            (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)))
            (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) (Work.MotV.fAS 𝕜)))
          (fun j => algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
            (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))) (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜) j)) 0
      from rfl]
  rw [← Work.MotAS.map_asRuleQA
      (algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
        (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))))
      (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.a)
      (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.b)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) (Work.MotV.fAS 𝕜))
      (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜)) 0,
    ← Work.MotAS.map_asRuleQB
      (algebraMap ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))
        (RatFunc ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜))))
      (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.a)
      (algebraMap 𝕜 ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) D.b)
      (algebraMap (RatFunc 𝕜) ↥(Work.MotAS.twistFieldAS D (Work.MotV.fAS 𝕜)) (Work.MotV.fAS 𝕜))
      (Work.MotAS.asY0 D (Work.MotV.fAS 𝕜)) 0]
  exact ratFunc_algebraMap_add_X_mul_ne_zero hB

end Work.MotV5.ASLocal
