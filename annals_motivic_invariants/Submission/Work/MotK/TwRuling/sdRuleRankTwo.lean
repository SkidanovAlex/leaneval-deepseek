import Mathlib
import Submission.Work.MotK.TGen.SdualTBrick
import Submission.Work.MotK.TwRule
import Submission.Work.MotK.TGen.TwCoordGKleinTw
import Submission.Work.MotK.TwRule.KleinTwRuleEval
import Submission.Work.MotK.KleinTwData
import Submission.Work.MotK.TwRuling.KleinNondeg
import Submission.Work.MotK.TwRuling.sdW_four_ne_zero
import Submission.Work.MotK.TwRuling.sdY_curve
import Submission.Work.MotK.TwRuling.SdThetaSdualT
import Submission.Work.MotK.TwRuling.sdRankCert14
import Submission.Work.MotK.TwRuling.sum_kleinP_two_mul
import Submission.Work.MotK.TwRuling.sdRankQuad12
import Submission.Work.MotTDG.Setup
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option maxHeartbeats 4000000
set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.MotK.TwRuling

/-!
# `Work.MotK.TwRuling.sdRuleRankTwo`

The two ruling vectors `A = sdRuleA K D h`, `B = sdRuleB K D h` of the T-twisted Crauder–Katz
link are not proportional over the rational function field `sdA K D h`, in characteristic `≠ 2`.

## The argument

Write `F₁ = twistFieldTG K D h ⊆ K̄(E)` for the twist field, `y_i ∈ F₁` for the twisted Klein
coordinates (`sdRankY`), and let `p = a(b⁵-2a⁵)`, `q = b(3a⁵+b⁵)`.

1. `sdRuleA/B` are the images under `algebraMap ↥F₁ (sdA K D h)` of the `K`-rational elements
   `kleinTwRuleA a b h y`, so a `2×2` minor vanishes in `RatFunc ↥F₁` iff it vanishes in `F₁`
   (the algebra map of a field into its fraction field is injective).

2. **The certificate** (`sdRankCert14`): in `F₁`, using that the four twisted Pfaffians
   `kleinTwP0…3` vanish at `y` (`kleinTwP_sdRankY_eq_zero`), the `(1,4)`-minor is
   `A₁B₄ - A₄B₁ = 2b²(p·y₁² + q·y₂)`. It is nonzero whenever `(p,q) ≠ 0`: pushing to `K̄(E)`,
   `p·y₁² + q·y₂ = w⁻²κ₀⁻²(p·κ₁² + q·κ₀κ₂)`, a quadratic form on the Klein curve whose
   coefficient vector is supported on `{κ₀κ₂, κ₁²}`; no nonzero such vector lies in
   `span{p₀,…,p₄}` (`sdRankQuad12`, the `{2,5}`-support version of `KleinNondeg`).

3. **The remaining case** `p = q = 0` forces `5 = 0` and `b = 2a`, and then the identity
   `sum_kleinP_two_mul` degenerates to `2∑ₖ pₖ = a²(∑ᵢκᵢ)²`; the `pₖ` vanish at `κ`, so
   `∑ᵢκᵢ = 0` — a linear dependence of the Klein coordinates, contradicting `D.spans`
   (`kleinCoord_linearIndependent`).
-/

/-- The twisted Klein coordinates, as elements of the twist field `twistFieldTG K D h`. -/
noncomputable def sdRankY (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K) :
    Fin 5 → ↥(Work.MotK.twistFieldTG K D h) :=
  fun i => ⟨Work.MotK.twCoordG K D h i,
    IntermediateField.subset_adjoin K (Set.range (Work.MotK.twCoordG K D h))
      (Set.mem_range_self i)⟩

/-- The twisted Klein coordinates, seen in `K̄(E)`. -/
@[simp]
theorem sdRankY_apply (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K) (i : Fin 5) :
    ((sdRankY K D h i : ↥(Work.MotK.twistFieldTG K D h)) : Work.MotK.OmG K D)
      = Work.MotK.twCoordG K D h i := rfl

/-- The image of the twisted Klein coordinates under the `algebraMap` of the twist field. -/
@[simp]
theorem sdRankY_algebraMap (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K) (i : Fin 5) :
    algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.OmG K D) (sdRankY K D h i)
      = Work.MotK.twCoordG K D h i := rfl

/-! ## §1 The missing component formulas of the ruling vectors -/

/-- The first component of the first twisted ruling vector. -/
theorem kleinTwRuleA_one {R : Type*} [CommRing R] (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleA a b h c 1
      = -a * b ^ 2 * (a * h * (c 4) ^ 2 + 2 * b * (c 0) * (c 3)) := by
  unfold Work.MotK.kleinTwRuleA Work.MotK.kleinTwPolarP Work.MotK.kleinTwP Work.MotK.kleinTwTan
    Work.MotK.kleinTwBilin Work.MotK.kleinTwQ Work.MotK.kleinTwP0 Work.MotK.kleinTwP1
    Work.MotK.kleinTwP2 Work.MotK.kleinTwP3 Work.MotK.kleinTwP4 Work.MotK.kleinE
  simp only [Pi.single_apply, Fin.isValue]
  norm_num
  refl_ring1

/-- The first component of the second twisted ruling vector. -/
theorem kleinTwRuleB_one {R : Type*} [CommRing R] (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleB a b h c 1
      = a ^ 2 * (a ^ 2 * h * (c 3) * (c 4) - 4 * b ^ 2 * (c 0) * (c 2)) := by
  unfold Work.MotK.kleinTwRuleB Work.MotK.kleinTwPolarP Work.MotK.kleinTwP Work.MotK.kleinTwTan
    Work.MotK.kleinTwBilin Work.MotK.kleinTwQ Work.MotK.kleinTwP0 Work.MotK.kleinTwP1
    Work.MotK.kleinTwP2 Work.MotK.kleinTwP3 Work.MotK.kleinTwP4 Work.MotK.kleinE
  simp only [Pi.single_apply, Fin.isValue]
  norm_num
  refl_ring1

/-- The fourth component of the first ruling vector, in the factored form used by the
certificate `sdRankCert14`. -/
theorem kleinTwRuleA_four_fact {R : Type*} [CommRing R] (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleA a b h c 4
      = a ^ 2 * b * (2 * a * (c 0) ^ 2 - b * h * (c 1) * (c 4)) := by
  rw [kleinTwRuleA_four]
  refl_ring1

/-- The fourth component of the second ruling vector, in the factored form used by the
certificate `sdRankCert14`. -/
theorem kleinTwRuleB_four_fact {R : Type*} [CommRing R] (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleB a b h c 4
      = a * h * (a ^ 3 * (c 1) * (c 3) - 2 * b ^ 3 * (c 0) * (c 4)) := by
  rw [kleinTwRuleB_four]
  refl_ring1

/-- `(b - 2a)⁵ = b⁵ - 2a⁵ + 5·(…)`. -/
theorem sub_two_pow_five {R : Type*} [CommRing R] (b a : R) :
    (b - 2 * a) ^ 5
      = b ^ 5 - 2 * a ^ 5
        + 5 * (-2 * b ^ 4 * a + 8 * b ^ 3 * a ^ 2 - 16 * b ^ 2 * a ^ 3 + 16 * b * a ^ 4
          - 6 * a ^ 5) := by
  refl_ring1

/-- Naturality of the first component of the first ruling vector. -/
theorem kleinTwRuleA_map_one {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleA (φ a) (φ b) (φ h) (fun i => φ (c i)) 1
      = φ (Work.MotK.kleinTwRuleA a b h c 1) := by
  rw [kleinTwRuleA_one, kleinTwRuleA_one]
  simp only [map_mul, map_pow, map_add, map_neg, map_ofNat]

/-- Naturality of the first component of the second ruling vector. -/
theorem kleinTwRuleB_map_one {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleB (φ a) (φ b) (φ h) (fun i => φ (c i)) 1
      = φ (Work.MotK.kleinTwRuleB a b h c 1) := by
  rw [kleinTwRuleB_one, kleinTwRuleB_one]
  simp only [map_mul, map_pow, map_sub, map_ofNat]

/-- Naturality of the fourth component of the first ruling vector, in the factored form. -/
theorem kleinTwRuleA_map_four_fact {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleA (φ a) (φ b) (φ h) (fun i => φ (c i)) 4
      = φ (Work.MotK.kleinTwRuleA a b h c 4) := by
  rw [kleinTwRuleA_four_fact, kleinTwRuleA_four_fact]
  simp only [map_mul, map_pow, map_sub, map_ofNat]

/-- Naturality of the fourth component of the second ruling vector, in the factored form. -/
theorem kleinTwRuleB_map_four_fact {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (a b h : R) (c : Fin 5 → R) :
    Work.MotK.kleinTwRuleB (φ a) (φ b) (φ h) (fun i => φ (c i)) 4
      = φ (Work.MotK.kleinTwRuleB a b h c 4) := by
  rw [kleinTwRuleB_four_fact, kleinTwRuleB_four_fact]
  simp only [map_mul, map_pow, map_sub, map_ofNat]

/-! ## §2 The twisted Klein equations in the twist field -/

/-- The five twisted Pfaffians vanish on the twisted Klein coordinates, as elements of the
twist field `twistFieldTG K D h` (the `kleinTwP` form of `Work.MotK.TGen.TwCoordGKleinTw`). -/
theorem kleinTwP_sdRankY_eq_zero (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h : K) (hh : h ≠ 0) (k : Fin 5) :
    Work.MotK.kleinTwP (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h) k = 0 := by
  apply (algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.OmG K D)).injective
  rw [map_zero, ← map_kleinTwP]
  simp only [← IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
    (Work.MotK.OmG K D)]
  rw [← Work.MotK.TGen.kleinTw_eq_kleinTwP]
  exact Work.MotK.TGen.TwCoordGKleinTw D hD h hh k

/-! ## §3 Transporting a vanishing quadratic form from the twist field to `K̄(E)` -/

/-- If `p·y₁² + q·y₂ = 0` in the twist field, then `p·κ₁² + q·κ₀κ₂ = 0` in `K̄(E)`. -/
theorem quad_push (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good) (h : K)
    (hh : h ≠ 0) (p q : K)
    (h0 : algebraMap K ↥(Work.MotK.twistFieldTG K D h) p * (sdRankY K D h 1) ^ 2
      + algebraMap K ↥(Work.MotK.twistFieldTG K D h) q * sdRankY K D h 2 = 0) :
    algebraMap K (Work.MotK.OmG K D) p
        * (Work.MotV.kleinCoord D (Work.MotK.KbG K) 1
            * Work.MotV.kleinCoord D (Work.MotK.KbG K) 1)
      + algebraMap K (Work.MotK.OmG K D) q
        * (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0
            * Work.MotV.kleinCoord D (Work.MotK.KbG K) 2) = 0 := by
  have hw : algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h) ≠ 0 :=
    Work.MotK.TGen.wG_ne_zero D hh
  have hk0 : Work.MotV.kleinCoord D (Work.MotK.KbG K) 0 ≠ 0 :=
    hD.coord0_ne (Work.MotK.KbG K)
  have hpush : algebraMap K (Work.MotK.OmG K D) p * (Work.MotK.twCoordG K D h 1) ^ 2
      + algebraMap K (Work.MotK.OmG K D) q * Work.MotK.twCoordG K D h 2 = 0 := by
    have h1 := congrArg (algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.OmG K D)) h0
    simpa only [map_add, map_mul, map_pow, map_zero, sdRankY_algebraMap,
      IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.OmG K D)]
      using h1
  have hgoal : algebraMap K (Work.MotK.OmG K D) p
        * (Work.MotV.kleinCoord D (Work.MotK.KbG K) 1
            * Work.MotV.kleinCoord D (Work.MotK.KbG K) 1)
      + algebraMap K (Work.MotK.OmG K D) q
        * (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0
            * Work.MotV.kleinCoord D (Work.MotK.KbG K) 2)
      = (algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h)) ^ 2
        * (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) ^ 2
        * (algebraMap K (Work.MotK.OmG K D) p * (Work.MotK.twCoordG K D h 1) ^ 2
          + algebraMap K (Work.MotK.OmG K D) q * Work.MotK.twCoordG K D h 2) := by
    have hw1 : (algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h))
        * Work.MotK.twCoordG K D h 1
        = Work.MotV.kleinCoord D (Work.MotK.KbG K) 1
          / Work.MotV.kleinCoord D (Work.MotK.KbG K) 0 := by
      simpa using Work.MotK.TGen.pow_mul_twCoordG D h hh 1
    have hw2 : (algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h)) ^ 2
        * Work.MotK.twCoordG K D h 2
        = Work.MotV.kleinCoord D (Work.MotK.KbG K) 2
          / Work.MotV.kleinCoord D (Work.MotK.KbG K) 0 :=
      Work.MotK.TGen.pow_mul_twCoordG D h hh 2
    have hstep : (algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h)) ^ 2
          * (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) ^ 2
          * (algebraMap K (Work.MotK.OmG K D) p * (Work.MotK.twCoordG K D h 1) ^ 2
            + algebraMap K (Work.MotK.OmG K D) q * Work.MotK.twCoordG K D h 2)
        = (Work.MotV.kleinCoord D (Work.MotK.KbG K) 0) ^ 2
          * (algebraMap K (Work.MotK.OmG K D) p
              * ((algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h))
                  * Work.MotK.twCoordG K D h 1) ^ 2
            + algebraMap K (Work.MotK.OmG K D) q
                * ((algebraMap (Work.MotK.KbG K) (Work.MotK.OmG K D) (Work.MotK.root5G K h)) ^ 2
                    * Work.MotK.twCoordG K D h 2)) := by
      refl_ring1
    rw [hstep, hw1, hw2]
    first
      | (field_simp [hk0]; ring; done)
      | (field_simp [hk0]; done)
  rw [hgoal, hpush, mul_zero]

/-! ## §4 The main theorem -/

theorem sdRuleRankTwo (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    ∃ i j : Fin 5,
      Work.MotK.TGen.sdRuleA K D h i * Work.MotK.TGen.sdRuleB K D h j
        ≠ Work.MotK.TGen.sdRuleA K D h j * Work.MotK.TGen.sdRuleB K D h i := by
  classical
  -- the two ruling vectors as images of twist-field elements, in components `1` and `4`
  have hA1 : Work.MotK.TGen.sdRuleA K D h 1
      = algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h)
          (Work.MotK.kleinTwRuleA (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
            (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
            (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h) 1) := by
    rw [Work.MotK.TGen.sdRuleA]
    rw [show Work.MotK.TGen.sdY K D h
        = fun j => algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h)
            (sdRankY K D h j) from rfl]
    rw [IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h) D.a,
      IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h) D.b,
      IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h) h]
    exact kleinTwRuleA_map_one (algebraMap ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h))
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h)
  have hA4 : Work.MotK.TGen.sdRuleA K D h 4
      = algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h)
          (Work.MotK.kleinTwRuleA (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
            (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
            (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h) 4) := by
    rw [Work.MotK.TGen.sdRuleA]
    rw [show Work.MotK.TGen.sdY K D h
        = fun j => algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h)
            (sdRankY K D h j) from rfl]
    rw [IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h) D.a,
      IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h) D.b,
      IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h) h]
    exact kleinTwRuleA_map_four (algebraMap ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h))
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h)
  have hB1 : Work.MotK.TGen.sdRuleB K D h 1
      = algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h)
          (Work.MotK.kleinTwRuleB (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
            (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
            (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h) 1) := by
    rw [Work.MotK.TGen.sdRuleB]
    rw [show Work.MotK.TGen.sdY K D h
        = fun j => algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h)
            (sdRankY K D h j) from rfl]
    rw [IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h) D.a,
      IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h) D.b,
      IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h) h]
    exact kleinTwRuleB_map_one (algebraMap ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h))
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h)
  have hB4 : Work.MotK.TGen.sdRuleB K D h 4
      = algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h)
          (Work.MotK.kleinTwRuleB (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
            (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
            (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h) 4) := by
    rw [Work.MotK.TGen.sdRuleB]
    rw [show Work.MotK.TGen.sdY K D h
        = fun j => algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h)
            (sdRankY K D h j) from rfl]
    rw [IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h) D.a,
      IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h) D.b,
      IsScalarTower.algebraMap_apply K ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h) h]
    exact kleinTwRuleB_map_four (algebraMap ↥(Work.MotK.twistFieldTG K D h)
        (Work.MotK.TGen.sdA K D h))
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h)
  -- the twisted Pfaffians vanish at the twisted coordinates
  have hk0 : Work.MotK.kleinTwP0 (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h) = 0 :=
    kleinTwP_sdRankY_eq_zero K D hD h hh 0
  have hk1 : Work.MotK.kleinTwP1 (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h) = 0 :=
    kleinTwP_sdRankY_eq_zero K D hD h hh 1
  have hk2 : Work.MotK.kleinTwP2 (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h) = 0 :=
    kleinTwP_sdRankY_eq_zero K D hD h hh 2
  have hk3 : Work.MotK.kleinTwP3 (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
      (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h) = 0 :=
    kleinTwP_sdRankY_eq_zero K D hD h hh 3
  -- the certificate: the (1,4)-minor modulo the twisted Pfaffians
  have hcert := sdRankCert14 (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
    (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
    (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h)
  rw [← kleinTwRuleA_one, ← kleinTwRuleA_four_fact, ← kleinTwRuleB_one,
    ← kleinTwRuleB_four_fact] at hcert
  simp only [hk0, hk1, hk2, hk3, mul_zero, add_zero] at hcert
  -- the two coefficients
  have hpq : algebraMap K ↥(Work.MotK.twistFieldTG K D h) (D.a * (D.b ^ 5 - 2 * D.a ^ 5))
      = algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a
        * ((algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b) ^ 5
            - 2 * (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a) ^ 5) := by
    simp only [map_mul, map_pow, map_sub, map_ofNat]
  have hpq' : algebraMap K ↥(Work.MotK.twistFieldTG K D h) (D.b * (3 * D.a ^ 5 + D.b ^ 5))
      = algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b
        * (3 * (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a) ^ 5
            + (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b) ^ 5) := by
    simp only [map_mul, map_add, map_pow, map_ofNat]
  have ha0 : D.a ≠ 0 := fun h0 => hD.ab_ne (by rw [h0, zero_mul])
  have hb0 : D.b ≠ 0 := fun h0 => hD.ab_ne (by rw [h0, mul_zero])
  have hY0 : sdRankY K D h 0 = 1 := by
    apply Subtype.ext
    show Work.MotK.twCoordG K D h 0 = (1 : Work.MotK.OmG K D)
    rw [Work.MotK.twCoordG]
    simp only [Fin.val_zero, pow_zero, one_mul]
    exact div_self (hD.coord0_ne (Work.MotK.KbG K))
  rw [← hpq, ← hpq', hY0] at hcert
  by_cases hcase : D.a * (D.b ^ 5 - 2 * D.a ^ 5) ≠ 0
      ∨ D.b * (3 * D.a ^ 5 + D.b ^ 5) ≠ 0
  · -- Case 1: the `(1,4)`-minor is nonzero
    refine ⟨1, 4, ?_⟩
    intro hz
    have hzF : Work.MotK.kleinTwRuleA (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
          (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
          (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h) 1
        * Work.MotK.kleinTwRuleB (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
          (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
          (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h) 4
        - Work.MotK.kleinTwRuleA (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
          (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
          (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h) 4
        * Work.MotK.kleinTwRuleB (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a)
          (algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b)
          (algebraMap K ↥(Work.MotK.twistFieldTG K D h) h) (sdRankY K D h) 1 = 0 := by
      apply (algebraMap ↥(Work.MotK.twistFieldTG K D h) (Work.MotK.TGen.sdA K D h)).injective
      rw [map_sub, map_mul, map_mul, map_zero]
      rw [← hA1, ← hB4, ← hA4, ← hB1]
      rw [hz, sub_self]
    -- hence the quadratic form `p·y₁² + q·y₂` vanishes
    have hne1 : algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.a ≠ 0 := fun h0 =>
      ha0 (RingHom.injective (algebraMap K ↥(Work.MotK.twistFieldTG K D h)) (by rw [h0, map_zero]))
    have hne2 : algebraMap K ↥(Work.MotK.twistFieldTG K D h) D.b ≠ 0 := fun h0 =>
      hb0 (RingHom.injective (algebraMap K ↥(Work.MotK.twistFieldTG K D h)) (by rw [h0, map_zero]))
    have h2F : (2 : ↥(Work.MotK.twistFieldTG K D h)) ≠ 0 := by
      intro h0
      refine h2 (RingHom.injective (algebraMap K ↥(Work.MotK.twistFieldTG K D h)) ?_)
      rw [map_zero, ← h0]
      exact map_ofNat (algebraMap K ↥(Work.MotK.twistFieldTG K D h)) 2
    have hzq : algebraMap K ↥(Work.MotK.twistFieldTG K D h) (D.a * (D.b ^ 5 - 2 * D.a ^ 5))
          * (sdRankY K D h 1) ^ 2
        + algebraMap K ↥(Work.MotK.twistFieldTG K D h) (D.b * (3 * D.a ^ 5 + D.b ^ 5))
          * sdRankY K D h 2 = 0 := by
      have hthis := hcert
      rw [hzF, zero_sub, mul_neg, neg_eq_zero, mul_eq_zero] at hthis
      rcases hthis with h3 | h3
      · exact absurd h3 hne1
      · rcases mul_eq_zero.mp h3 with h4 | h4
        · refine absurd h4 ?_
          refine mul_ne_zero (mul_ne_zero h2F (pow_ne_zero 2 hne2)) ?_
          norm_num
        · simpa only [mul_one] using h4
    have hquad := sdRankQuad12 K D hD (D.a * (D.b ^ 5 - 2 * D.a ^ 5))
      (D.b * (3 * D.a ^ 5 + D.b ^ 5)) hcase
    exact hquad (by simpa only [pow_two] using quad_push K D hD h hh _ _ hzq)
  · -- Case 2: both coefficients vanish
    exfalso
    rw [not_or] at hcase
    obtain ⟨hp, hq⟩ := hcase
    have hp' : D.a * (D.b ^ 5 - 2 * D.a ^ 5) = 0 := not_not.mp hp
    have hq' : D.b * (3 * D.a ^ 5 + D.b ^ 5) = 0 := not_not.mp hq
    have ha : D.a ≠ 0 := fun h0 => hD.ab_ne (by rw [h0, zero_mul])
    have hb : D.b ≠ 0 := fun h0 => hD.ab_ne (by rw [h0, mul_zero])
    have hb5 : D.b ^ 5 = 2 * D.a ^ 5 := by
      rcases mul_eq_zero.mp hp' with h' | h'
      · exact absurd h' ha
      · exact sub_eq_zero.mp h'
    have hb5' : D.b ^ 5 = -(3 * D.a ^ 5) := by
      rcases mul_eq_zero.mp hq' with h' | h'
      · exact absurd h' hb
      · have h'' : D.b ^ 5 + 3 * D.a ^ 5 = 0 := by rw [add_comm]; exact h'
        exact add_eq_zero_iff_eq_neg.mp h''
    -- hence `5 = 0`
    have h5 : (5 : K) = 0 := by
      have h2eq : 2 * D.a ^ 5 = -(3 * D.a ^ 5) := by rw [← hb5, hb5']
      have ha5 : D.a ^ 5 ≠ 0 := pow_ne_zero 5 ha
      have hsum : 2 * D.a ^ 5 + 3 * D.a ^ 5 = 0 := by rw [h2eq]; ring
      have hsum' : 2 * D.a ^ 5 + 3 * D.a ^ 5 = (5 : K) * D.a ^ 5 := by ring
      rw [hsum'] at hsum
      exact (mul_eq_zero.mp hsum).resolve_right ha5
    -- hence `b = 2a`
    have hba : D.b = 2 * D.a := by
      have hp5 : (D.b - 2 * D.a) ^ 5 = 0 := by
        rw [sub_two_pow_five, h5, zero_mul, add_zero, hb5]
        refl_ring1
      exact sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (5 : ℕ) ≠ 0)).mp hp5)
    -- the Klein coordinates are linearly independent
    obtain ⟨e, he⟩ := hD.spans
    have hli : LinearIndependent (Work.MotK.KbG K) (Work.MotV.kleinCoord D (Work.MotK.KbG K)) :=
      Work.MotTDG.kleinCoord_linearIndependent D (Work.MotK.KbG K) e (he (Work.MotK.KbG K))
    -- their sum vanishes
    have hsum : (∑ i : Fin 5, Work.MotV.kleinCoord D (Work.MotK.KbG K) i) = 0 := by
      have hid := sum_kleinP_two_mul (R := Work.MotK.OmG K D)
        (a := algebraMap K (Work.MotK.OmG K D) D.a)
        (x := Work.MotV.kleinCoord D (Work.MotK.KbG K))
      have hz : ∀ k : Fin 5, Work.MotK.kleinP (algebraMap K (Work.MotK.OmG K D) D.a)
          (2 * algebraMap K (Work.MotK.OmG K D) D.a)
          (Work.MotV.kleinCoord D (Work.MotK.KbG K)) k = 0 := by
        intro k
        have h := hD.klein_eq (Work.MotK.KbG K) k
        have hb' : algebraMap K (Work.MotK.OmG K D) D.b
            = 2 * algebraMap K (Work.MotK.OmG K D) D.a := by
          rw [hba, map_mul, map_ofNat]
        rw [hb'] at h
        exact h
      have h5L : (5 : Work.MotK.OmG K D) = 0 := by
        have h1 : algebraMap K (Work.MotK.OmG K D) (5 : K) = (5 : Work.MotK.OmG K D) :=
          map_ofNat _ 5
        rw [← h1, h5, map_zero]
      have hsum0 : (∑ k : Fin 5, Work.MotK.kleinP (algebraMap K (Work.MotK.OmG K D) D.a)
          (2 * algebraMap K (Work.MotK.OmG K D) D.a)
          (Work.MotV.kleinCoord D (Work.MotK.KbG K)) k) = 0 :=
        Finset.sum_eq_zero fun k _ => hz k
      have haL : algebraMap K (Work.MotK.OmG K D) D.a ≠ 0 := fun h0 =>
        ha (RingHom.injective (algebraMap K (Work.MotK.OmG K D)) (by rw [h0, map_zero]))
      have h := hid
      rw [hsum0, mul_zero] at h
      rw [h5L] at h
      simp only [zero_mul, sub_zero] at h
      -- h : 0 = aL² · (∑κ)²
      have hsq : ((∑ i : Fin 5, Work.MotV.kleinCoord D (Work.MotK.KbG K) i)) ^ 2 = 0 :=
        (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero 2 haL)
      exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
    -- contradiction with linear independence
    rw [Fintype.linearIndependent_iff] at hli
    have hone : (1 : Work.MotK.KbG K) = 0 := hli (fun _ => 1) (by simpa using hsum) 0
    exact one_ne_zero hone

end Work.MotK.TwRuling
