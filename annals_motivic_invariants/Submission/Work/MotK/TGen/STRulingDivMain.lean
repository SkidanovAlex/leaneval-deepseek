import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotA.Defs
import Submission.Work.MotK.TwCensus.Defs
import Submission.Work.MotK.TwCensus.STClass
import Submission.Work.MotK.TwCensus.Amat_mulVec
import Submission.Work.MotK.TwCensus.K5Ruling
import Submission.Work.MotK.TwAmbh
import Submission.Work.MotK.KleinTwData.map_data
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.MotK.TGen.KleinTwFibre_eq_ker
import Submission.Work.MotK.TGen.STRulingAux
import Submission.Work.MotK.TGen.STRulingTheta
import Submission.Work.MotK.TGen.ThetaS
import Submission.Work.MotK.TGen.ThetaFwVec
import Submission.Work.MotK.TGen.ThetaST
import Submission.Work.MotK.TGen.ThetaRangeClosure
import Submission.Work.MotK.TGen.ZRingIsDomainAll
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type} [Field K]

/-! ## Helper identities on the chart data

The small missing ingredients of the assembly, kept here so that this file does not have to import
`Submission/Work/MotK/TGen/STRulingDiv.lean` (which still contains a `sorry`).
-/

/-- **Homogeneity of the twisted inverse map.** -/
theorem kleinTwRT_smul {R : Type*} [CommRing R] (a b h c : R) (y : Fin 5 → R) :
    Work.MotK.kleinTwR a b h (c • y) = c ^ 3 • Work.MotK.kleinTwR a b h y := by
  funext k
  fin_cases k
  · show Work.MotK.kleinTwR0 a b h (c • y) = c ^ 3 * Work.MotK.kleinTwR0 a b h y
    simp only [Work.MotK.kleinTwR0, Pi.smul_apply, smul_eq_mul]
    refl_ring1
  · show Work.MotK.kleinTwR1 a b h (c • y) = c ^ 3 * Work.MotK.kleinTwR1 a b h y
    simp only [Work.MotK.kleinTwR1, Pi.smul_apply, smul_eq_mul]
    refl_ring1
  · show Work.MotK.kleinTwR2 a b h (c • y) = c ^ 3 * Work.MotK.kleinTwR2 a b h y
    simp only [Work.MotK.kleinTwR2, Pi.smul_apply, smul_eq_mul]
    refl_ring1
  · show Work.MotK.kleinTwR3 a b h (c • y) = c ^ 3 * Work.MotK.kleinTwR3 a b h y
    simp only [Work.MotK.kleinTwR3, Pi.smul_apply, smul_eq_mul]
    refl_ring1
  · show Work.MotK.kleinTwR4 a b h (c • y) = c ^ 3 * Work.MotK.kleinTwR4 a b h y
    simp only [Work.MotK.kleinTwR4, Pi.smul_apply, smul_eq_mul]
    refl_ring1

section Naturality

variable {S : Type*} [CommRing S]

/-- **`sT` is natural.** -/
theorem map_sTT_ring (f : MvPolynomial (Fin 3) K →+* S) (a b h : K) :
    f (Work.MotK.TGen.sT a b h)
      = Work.MotK.kleinTwS (f (MvPolynomial.C a)) (f (MvPolynomial.C b))
          (f (MvPolynomial.C h))
          (Work.MotK.kleinTwStereo (f (MvPolynomial.C a)) (f (MvPolynomial.C b))
            (f (MvPolynomial.C h)) (fun i => f (Work.MotK.pRa a b h i))
            (fun i => f (Work.MotK.chart3 K i))) := by
  have hS : ∀ y : Fin 5 → MvPolynomial (Fin 3) K,
      f (Work.MotK.kleinTwS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) y)
        = Work.MotK.kleinTwS (f (MvPolynomial.C a)) (f (MvPolynomial.C b))
            (f (MvPolynomial.C h)) (fun i => f (y i)) :=
    fun y => (Work.MotK.KleinTwData.map_data f (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C h)).2.2.2.1 y
  have hSt : (fun i => f (Work.MotK.kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b)
        (MvPolynomial.C h) (Work.MotK.pRa a b h) (Work.MotK.chart3 K) i))
      = Work.MotK.kleinTwStereo (f (MvPolynomial.C a)) (f (MvPolynomial.C b))
        (f (MvPolynomial.C h)) (fun i => f (Work.MotK.pRa a b h i))
        (fun i => f (Work.MotK.chart3 K i)) :=
    funext fun i => (Work.MotK.KleinTwData.map_data f (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C h)).2.2.1 _ _ i
  rw [Work.MotK.TGen.sT, hS, hSt]

/-- **`fwVec` is natural.** -/
theorem map_fwVecT_ring (f : MvPolynomial (Fin 3) K →+* S) (a b h : K) :
    (fun i => f (Work.MotK.TGen.fwVec a b h i))
      = Work.MotK.kleinTwP (f (MvPolynomial.C a)) (f (MvPolynomial.C b))
          (f (MvPolynomial.C h))
          (Work.MotK.kleinTwStereo (f (MvPolynomial.C a)) (f (MvPolynomial.C b))
            (f (MvPolynomial.C h)) (fun i => f (Work.MotK.pRa a b h i))
            (fun i => f (Work.MotK.chart3 K i))) := by
  have hP : ∀ (y : Fin 5 → MvPolynomial (Fin 3) K) (k : Fin 5),
      f (Work.MotK.kleinTwP (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) y k)
        = Work.MotK.kleinTwP (f (MvPolynomial.C a)) (f (MvPolynomial.C b))
            (f (MvPolynomial.C h)) (fun i => f (y i)) k :=
    fun y k => (Work.MotK.KleinTwData.map_data f (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C h)).2.2.2.2.1 y k
  have hSt : (fun i => f (Work.MotK.kleinTwStereo (MvPolynomial.C a) (MvPolynomial.C b)
        (MvPolynomial.C h) (Work.MotK.pRa a b h) (Work.MotK.chart3 K) i))
      = Work.MotK.kleinTwStereo (f (MvPolynomial.C a)) (f (MvPolynomial.C b))
        (f (MvPolynomial.C h)) (fun i => f (Work.MotK.pRa a b h i))
        (fun i => f (Work.MotK.chart3 K i)) :=
    funext fun i => (Work.MotK.KleinTwData.map_data f (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C h)).2.2.1 _ _ i
  funext k
  rw [Work.MotK.TGen.fwVec, hP _ k, hSt]

/-- **The chart `chart3` under a `K`-algebra map.** -/
theorem eval_chart3T (f : MvPolynomial (Fin 3) K →+* S) :
    (fun i => f (Work.MotK.chart3 K i))
      = ![0, f (MvPolynomial.X 0), f (MvPolynomial.X 1), f (MvPolynomial.X 2), 1] := by
  rw [show (Work.MotK.chart3 K : Fin 5 → MvPolynomial (Fin 3) K)
    = ![0, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 1] from rfl]
  have h2 : (fun i => f (![0, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 1] i))
      = ![f 0, f (MvPolynomial.X 0), f (MvPolynomial.X 1), f (MvPolynomial.X 2), f 1] := by
    rw [show (fun i => f (![0, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 1] i))
        = (f : MvPolynomial (Fin 3) K → S) ∘ ![0, MvPolynomial.X 0, MvPolynomial.X 1,
            MvPolynomial.X 2, 1] from rfl]
    simp only [Matrix.vecCons, Fin.comp_cons, Matrix.empty_eq]
  rw [h2, map_zero, map_one]

/-- **Naturality of the ruling vectors `rv` under a change of scalars.** -/
theorem rv_map {S : Type*} [Field S] (φ : K →+* S) (a b h : K) (i : Fin 5) :
    MvPolynomial.map φ (Work.MotK.TwCensus.rv a b h i)
      = Work.MotK.TwCensus.rv (φ a) (φ b) (φ h) i := by
  fin_cases i <;>
    simp [Work.MotK.TwCensus.rv, map_mul, map_div₀, map_sub]

/-- **Naturality of the ruling vectors `rw` under a change of scalars.** -/
theorem rw_map {S : Type*} [Field S] (φ : K →+* S) (a b h : K) (i : Fin 5) :
    MvPolynomial.map φ (Work.MotK.TwCensus.rw a b h i)
      = Work.MotK.TwCensus.rw (φ a) (φ b) (φ h) i := by
  fin_cases i <;>
    simp [Work.MotK.TwCensus.rw, map_mul, map_div₀, map_sub]

end Naturality

/-- **`Sklein 4` is `-linT`.** -/
theorem Sklein_four (a b h : K) : Sklein a b h 4 = -Work.MotK.TGen.linT a b h := by
  simp [Sklein, Work.MotK.kleinTwStereo, Work.MotK.TGen.linT, Work.MotK.pRa,
    Work.MotK.kleinPointT, Work.MotK.chart3]

/-- **The chart identity for the stereographic point.** -/
theorem Sklein_chart (a b h : K) (j : Fin 3) :
    Sklein a b h (ch3' (K := K) j)
        - MvPolynomial.C (Work.MotK.kleinPointT a b h (ch3' (K := K) j)) * Sklein a b h 0
      = Sklein a b h 4 * MvPolynomial.X j := by
  fin_cases j <;>
    simp [Sklein, Work.MotK.kleinTwStereo, Work.MotK.pRa, Work.MotK.kleinPointT,
      Work.MotK.chart3, ch3'] <;>
    refl_ring1

/-! ## The main case -/

theorem STRulingDivMain_of_domain (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h : K) (hh : h ≠ 0) (x : Work.MotA.polySpec K 3) (hcoh : Order.coheight x = 1)
    (hx : Work.MotK.TGen.sT D.a D.b h ∈ x.asIdeal) (ha : D.a ≠ 0) (hb : D.b ≠ 0)
    (hlin : Work.MotK.TGen.linT D.a D.b h ∉ x.asIdeal)
    (hfw : Work.MotK.TGen.fwVec D.a D.b h 4 ∉ x.asIdeal)
    (hDZ : IsDomain (ZRing D.a D.b h)) :
    Nonempty (Work.MotV.resF K x ≃ₐ[K] FractionRing (Polynomial (ZRing D.a D.b h))) := by
  haveI : IsDomain (ZRing D.a D.b h) := hDZ
  haveI hxp : x.asIdeal.IsPrime := x.isPrime
  let q := MvPolynomial (Fin 3) K ⧸ x.asIdeal
  let k := Work.MotV.resF K x
  -- pin the instances of `k`, so that `MvPolynomial (Fin 3) k`, `Matrix` and `eval` all use the
  -- instances derived from the `Field` structure (instance diamond, see NOTE_STRulingDiv2.md)
  -- pin the instances of `k` to the ones coming from the `OreLocalization` structure of
  -- `FractionRing` (these are the ones used inside every imported lemma; see NOTE_STRulingDiv2.md)
  let loc : MvPolynomial (Fin 3) K →+* k := (algebraMap q k).comp (Ideal.Quotient.mk x.asIdeal)
  let f : MvPolynomial (Fin 3) K → k := ⇑loc
  have hf : ∀ p : MvPolynomial (Fin 3) K, f p = 0 ↔ p ∈ x.asIdeal := by
    intro p
    constructor
    · intro hp
      exact Ideal.Quotient.eq_zero_iff_mem.mp (IsFractionRing.injective q k (by
        show algebraMap q k (Ideal.Quotient.mk x.asIdeal p) = algebraMap q k 0
        rw [map_zero]; exact hp))
    · intro hp
      show algebraMap q k (Ideal.Quotient.mk x.asIdeal p) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  have hfC : ∀ c : K, f (MvPolynomial.C c) = algebraMap K k c := by
    intro c
    show algebraMap q k (Ideal.Quotient.mk x.asIdeal
      (algebraMap K (MvPolynomial (Fin 3) K) c)) = algebraMap K k c
    rw [Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply K q k]
  have hf0 : f 0 = 0 := map_zero loc
  have hf1 : f 1 = 1 := map_one loc
  have hfa : ∀ a b : MvPolynomial (Fin 3) K, f (a + b) = f a + f b := fun a b => map_add loc a b
  have hfm : ∀ a b : MvPolynomial (Fin 3) K, f (a * b) = f a * f b := fun a b => map_mul loc a b
  have hfneg : ∀ y : MvPolynomial (Fin 3) K, f (-y) = -f y := fun y => map_neg loc y
  have hfsub : ∀ a b : MvPolynomial (Fin 3) K, f (a - b) = f a - f b := by
    intro a b
    rw [sub_eq_add_neg, hfa, hfneg, sub_eq_add_neg]
  letI hCS : CommSemiring k := (inferInstance : Field k).toCommSemiring
  letI hCR : CommRing k := (inferInstance : Field k).toCommRing
  let fr : @RingHom (MvPolynomial (Fin 3) K) k _
      (@Semiring.toNonAssocSemiring k hCR.toCommSemiring.toSemiring) :=
    { toFun := ⇑loc
      map_one' := map_one loc
      map_mul' := fun a b => map_mul loc a b
      map_zero' := map_zero loc
      map_add' := fun a b => map_add loc a b }
  have hfr : ∀ p : MvPolynomial (Fin 3) K, fr p = f p := fun p => rfl
  have hfr' : ∀ p : MvPolynomial (Fin 3) K, f p = fr p := fun p => (hfr p).symm
  have hst := map_sTT_ring fr D.a D.b h
  have hfw4 := congrFun (map_fwVecT_ring fr D.a D.b h) 4
  have hsk : ∀ i : Fin 5, f (Sklein D.a D.b h i) =
      Work.MotK.kleinTwStereo (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) (fun i => f (Work.MotK.pRa D.a D.b h i))
        (fun i => f (Work.MotK.chart3 K i)) i :=
    fun i => congrFun (map_kleinTwStereo' fr (MvPolynomial.C D.a) (MvPolynomial.C D.b)
      (MvPolynomial.C h) (Work.MotK.pRa D.a D.b h) (Work.MotK.chart3 K)) i
  have hQ := (Work.MotK.KleinTwData.map_data fr (MvPolynomial.C D.a) (MvPolynomial.C D.b)
    (MvPolynomial.C h)).1 (Work.MotK.pRa D.a D.b h)
  have hlin_ev : f (Work.MotK.TGen.linT D.a D.b h) ≠ 0 := fun hh0 => hlin ((hf _).mp hh0)
  let vpt : Fin 3 → k := fun i => f (MvPolynomial.X i)
  let y : Fin 5 → k := Work.MotK.kleinTwStereo (f (MvPolynomial.C D.a))
      (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h))
      (fun i => f (Work.MotK.pRa D.a D.b h i)) (fun i => f (Work.MotK.chart3 K i))
  have hs : Work.MotK.kleinTwS (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) y = 0 := by
    rw [show y = Work.MotK.kleinTwStereo (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) (fun i => f (Work.MotK.pRa D.a D.b h i))
        (fun i => f (Work.MotK.chart3 K i)) from rfl]
    simp only [hfr']
    rw [← hst, hfr]
    exact (hf _).mpr hx
  let c' : Fin 5 → k := Work.MotK.kleinTwP (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) y
  have hc : Work.MotK.kleinTwR (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) c' = 0 := by
    funext j
    show Work.MotK.kleinTwR (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h))
      (Work.MotK.kleinTwP (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) y) j = 0
    rw [Work.MotK.KleinTwI1, hs, zero_mul]
  have hp0 : Work.MotK.kleinTwQ (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) (fun i => f (Work.MotK.pRa D.a D.b h i)) = 0 := by
    simp only [hfr']
    rw [← hQ, hfr]
    exact (hf _).mpr (by rw [Work.MotK.kleinTwQ_pRa D.a D.b h ha hh]; exact x.asIdeal.zero_mem)
  have hchartJ : ∀ j : Fin 3, y (ch3' (K := K) j)
      - algebraMap K k (Work.MotK.kleinPointT D.a D.b h (ch3' (K := K) j)) * y 0
      = y 4 * vpt j := by
    intro j
    have hcl := congrArg f (Sklein_chart (K := K) D.a D.b h j)
    have h1 : f (Sklein D.a D.b h (ch3' (K := K) j)
          - MvPolynomial.C (Work.MotK.kleinPointT D.a D.b h (ch3' (K := K) j))
            * Sklein D.a D.b h 0)
        = y (ch3' (K := K) j)
          - f (MvPolynomial.C (Work.MotK.kleinPointT D.a D.b h (ch3' (K := K) j))) * y 0 := by
      rw [hfsub, hfm, hsk (ch3' (K := K) j), hsk 0]
    have h2 : f (Sklein D.a D.b h 4 * MvPolynomial.X j) = y 4 * f (MvPolynomial.X j) := by
      rw [hfm, hsk 4]
    rw [h1, h2, hfC] at hcl
    exact hcl
  have hc0 : c' 0 = 0 := by
    show Work.MotK.kleinTwP (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) y 0 = 0
    show Work.MotK.kleinTwQ (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) y = 0
    rw [show y = Work.MotK.kleinTwStereo (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) (fun i => f (Work.MotK.pRa D.a D.b h i))
        (fun i => f (Work.MotK.chart3 K i)) from rfl,
      Work.MotK.KleinTwQ_stereo, hp0, mul_zero]
  have hc4 : c' 4 ≠ 0 := by
    intro h0
    have h1 : f (Work.MotK.TGen.fwVec D.a D.b h 4) = c' 4 := hfw4
    exact hfw ((hf _).mp (h1.trans h0))
  let u : k := c' 1 / c' 4
  let v : k := c' 2 / c' 4
  let w : k := c' 3 / c' 4
  have hc'_scal : c' = c' 4 • ![0, u, v, w, 1] := by
    funext j
    fin_cases j
    · show c' 0 = c' 4 * 0
      rw [hc0, mul_zero]
    · show c' 1 = c' 4 * (c' 1 / c' 4)
      exact (mul_div_cancel₀ (c' 1) hc4).symm
    · show c' 2 = c' 4 * (c' 2 / c' 4)
      exact (mul_div_cancel₀ (c' 2) hc4).symm
    · show c' 3 = c' 4 * (c' 3 / c' 4)
      exact (mul_div_cancel₀ (c' 3) hc4).symm
    · show c' 4 = c' 4 * 1
      rw [mul_one]
  have hxq : Work.MotK.kleinTwR (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) ![0, u, v, w, 1] = 0 := by
    have h1 : (c' 4) ^ 3 • Work.MotK.kleinTwR (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) ![0, u, v, w, 1] = 0 := by
      rw [← kleinTwRT_smul, ← hc'_scal]
      exact hc
    funext j
    have h2 : (c' 4) ^ 3 * Work.MotK.kleinTwR (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) ![0, u, v, w, 1] j = 0 := by
      simpa only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] using congrFun h1 j
    exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 3 hc4)
  have hSklein : ∀ i : Fin 5, y i = f (Sklein D.a D.b h i) := by
    intro i
    rw [show y = Work.MotK.kleinTwStereo (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) (fun i => f (Work.MotK.pRa D.a D.b h i))
        (fun i => f (Work.MotK.chart3 K i)) from rfl]
    exact (hsk i).symm
  have hy4 : y 4 ≠ 0 := by
    have h1 : y 4 = f (Sklein D.a D.b h 4) := hSklein 4
    rw [h1, Sklein_four, hfneg]
    exact neg_ne_zero.mpr hlin_ev
  have hy_ker : Matrix.mulVec (Work.MotK.TwCensus.AmatP (f (MvPolynomial.C D.a))
      (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) ![0, u, v, w, 1]) y = 0 := by
    have hM : Matrix.mulVec (Work.MotK.TwCensus.kleinTwM (f (MvPolynomial.C D.a))
        (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) y) c' = 0 := by
      rw [show c' = Work.MotK.kleinTwP (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) y from rfl]
      exact kleinTwM_mulVec_kleinTwP (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) y
    have hAP : Matrix.mulVec (Work.MotK.TwCensus.AmatP (f (MvPolynomial.C D.a))
        (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) c') y = 0 := by
      rw [AmatP_eq_Amat', Work.MotK.TwCensus.Amat_mulVec]
      exact hM
    have h2 : Matrix.mulVec (Work.MotK.TwCensus.AmatP (f (MvPolynomial.C D.a))
        (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h))
        (c' 4 • ![0, u, v, w, 1])) y = 0 := by
      rw [← hc'_scal]; exact hAP
    rw [AmatP_smul_right, Matrix.smul_mulVec] at h2
    exact (smul_eq_zero.mp h2).resolve_left hc4
  have hz3 : MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Zcub (f (MvPolynomial.C D.a))
      (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) 3) = 0 := by
    rw [Zcub_eval_eq']
    exact congrFun hxq 3
  have hz4 : MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Zcub (f (MvPolynomial.C D.a))
      (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) 4) = 0 := by
    rw [Zcub_eval_eq']
    exact congrFun hxq 4
  have ha_k : f (MvPolynomial.C D.a) ≠ 0 := by
    rw [hfC D.a]
    exact fun h0 => ha ((algebraMap K k).injective (by rw [h0, map_zero]))
  have hb_k : f (MvPolynomial.C D.b) ≠ 0 := by
    rw [hfC D.b]
    exact fun h0 => hb ((algebraMap K k).injective (by rw [h0, map_zero]))
  obtain ⟨c, d, hcd⟩ := (AmatP_ker_iff (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
    (f (MvPolynomial.C h)) u v w ha_k hb_k hz3 hz4 y).mp hy_ker
  let evrv : Fin 5 → k := fun i => MvPolynomial.eval ![u, v, w]
    (Work.MotK.TwCensus.rv (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) i)
  let evrw : Fin 5 → k := fun i => MvPolynomial.eval ![u, v, w]
    (Work.MotK.TwCensus.rw (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) i)
  have hcd' : y = c • evrv + d • evrw := hcd
  have hevrv3 : evrv 3 = 1 := by
    show MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv (f (MvPolynomial.C D.a))
      (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) 3) = 1
    simp [Work.MotK.TwCensus.rv]
  have hevrv4 : evrv 4 = 0 := by
    show MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv (f (MvPolynomial.C D.a))
      (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) 4) = 0
    simp [Work.MotK.TwCensus.rv]
  have hevrw3 : evrw 3 = 0 := by
    show MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rw (f (MvPolynomial.C D.a))
      (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) 3) = 0
    simp [Work.MotK.TwCensus.rw]
  have hevrw4 : evrw 4 = 1 := by
    show MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rw (f (MvPolynomial.C D.a))
      (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) 4) = 1
    simp [Work.MotK.TwCensus.rw]
  have hc_eq : c = y 3 := by
    have h3 := congrFun hcd' 3
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h3
    rw [hevrv3, hevrw3] at h3
    simpa using h3.symm
  have hd_eq : d = y 4 := by
    have h4 := congrFun hcd' 4
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h4
    rw [hevrv4, hevrw4] at h4
    simpa using h4.symm
  have hmem : ∀ i : Fin 5, y i = y 3 * evrv i + y 4 * evrw i := by
    intro i
    have hi := congrFun hcd' i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hi
    rw [hc_eq, hd_eq] at hi
    exact hi
  let ev : MvPolynomial (Fin 3) K →+* k :=
    MvPolynomial.eval₂Hom (algebraMap K k) (fun j => ![u, v, w] j)
  have hevX : ∀ j : Fin 3, ev (MvPolynomial.X j) = ![u, v, w] j :=
    fun j => MvPolynomial.eval₂Hom_X' _ _ j
  have hevC : ∀ c : K, ev (MvPolynomial.C c) = algebraMap K k c :=
    fun c => MvPolynomial.eval₂Hom_C _ _ c
  have hEvRv : ∀ i : Fin 5, ev (Work.MotK.TwCensus.rv D.a D.b h i) = evrv i := by
    intro i
    change MvPolynomial.eval₂ (algebraMap K k) (fun j => ![u, v, w] j)
        (Work.MotK.TwCensus.rv D.a D.b h i)
      = MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rv (f (MvPolynomial.C D.a))
          (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) i)
    rw [MvPolynomial.eval₂_eq_eval_map]
    have h1 : MvPolynomial.map (algebraMap K k) (Work.MotK.TwCensus.rv D.a D.b h i)
        = Work.MotK.TwCensus.rv (algebraMap K k D.a) (algebraMap K k D.b)
            (algebraMap K k h) i :=
      rv_map (algebraMap K k) D.a D.b h i
    rw [h1, hfC D.a, hfC D.b, hfC h]
  have hEvRw : ∀ i : Fin 5, ev (Work.MotK.TwCensus.rw D.a D.b h i) = evrw i := by
    intro i
    change MvPolynomial.eval₂ (algebraMap K k) (fun j => ![u, v, w] j)
        (Work.MotK.TwCensus.rw D.a D.b h i)
      = MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.rw (f (MvPolynomial.C D.a))
          (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) i)
    rw [MvPolynomial.eval₂_eq_eval_map]
    have h1 : MvPolynomial.map (algebraMap K k) (Work.MotK.TwCensus.rw D.a D.b h i)
        = Work.MotK.TwCensus.rw (algebraMap K k D.a) (algebraMap K k D.b)
            (algebraMap K k h) i :=
      rw_map (algebraMap K k) D.a D.b h i
    rw [h1, hfC D.a, hfC D.b, hfC h]
  have hRVS : ∀ i : Fin 5, ev (RVS D.a D.b h i)
      = evrv i - algebraMap K k (Work.MotK.kleinPointT D.a D.b h i) * evrv 0 := by
    intro i
    simp only [RVS]
    rw [map_sub, map_mul, hevC, hEvRv i, hEvRv 0]
  have hRWS : ∀ i : Fin 5, ev (RWS D.a D.b h i)
      = evrw i - algebraMap K k (Work.MotK.kleinPointT D.a D.b h i) * evrw 0 := by
    intro i
    simp only [RWS]
    rw [map_sub, map_mul, hevC, hEvRw i, hEvRw 0]
  let t : k := y 3 / y 4
  have ht : t * y 4 = y 3 := by
    show y 3 / y 4 * y 4 = y 3
    exact div_mul_cancel₀ _ hy4
  have hparam : ∀ j : Fin 3, vpt j
      = ev (RVS D.a D.b h (ch3' (K := K) j)) * t + ev (RWS D.a D.b h (ch3' (K := K) j)) := by
    intro j
    have h2 : y (ch3' (K := K) j)
        - algebraMap K k (Work.MotK.kleinPointT D.a D.b h (ch3' (K := K) j)) * y 0
        = y 4 * (ev (RVS D.a D.b h (ch3' (K := K) j)) * t
            + ev (RWS D.a D.b h (ch3' (K := K) j))) := by
      rw [hmem (ch3' (K := K) j), hmem 0, hRVS, hRWS]
      rw [show y 3 = t * y 4 from ht.symm]
      refl_ring1
    have h3 : y 4 * vpt j = y 4 * (ev (RVS D.a D.b h (ch3' (K := K) j)) * t
        + ev (RWS D.a D.b h (ch3' (K := K) j))) := by
      rw [← hchartJ j, h2]
    exact mul_left_cancel₀ hy4 h3
  have hZIker : Work.MotK.TwCensus.ZI D.a D.b h ≤ RingHom.ker ev := by
    rw [Work.MotK.TwCensus.ZI, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    change ev (Work.MotK.TwCensus.Zcub D.a D.b h j) = 0
    have h1 : ev (Work.MotK.TwCensus.Zcub D.a D.b h j)
        = Work.MotK.kleinTwR (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
            (f (MvPolynomial.C h)) ![0, u, v, w, 1] j := by
      rw [show Work.MotK.TwCensus.Zcub D.a D.b h j
          = Work.MotK.kleinTwR (MvPolynomial.C D.a) (MvPolynomial.C D.b) (MvPolynomial.C h)
              (Work.MotK.chart3 K) j from rfl]
      rw [(Work.MotK.KleinTwData.map_data ev (MvPolynomial.C D.a) (MvPolynomial.C D.b)
            (MvPolynomial.C h)).2.2.2.2.2 (Work.MotK.chart3 K) j]
      have hc : (fun i => ev (Work.MotK.chart3 K i)) = ![0, u, v, w, 1] := by
        rw [eval_chart3T ev]
        funext i
        fin_cases i <;> simp [hevX]
      rw [hevC D.a, hevC D.b, hevC h, hc]
      rw [← hfC D.a, ← hfC D.b, ← hfC h]
    rw [h1]
    exact congrFun hxq j
  have hradker : Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h) ≤ RingHom.ker ev := by
    intro p hp
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hp
    rw [RingHom.mem_ker]
    have h2 : ev p ^ n = 0 := by
      rw [← map_pow]
      exact RingHom.mem_ker.mp (hZIker hn)
    exact eq_zero_of_pow_eq_zero h2
  let psi : ZRing D.a D.b h →+* k :=
    Ideal.Quotient.lift (Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h)) ev hradker
  have hpsimk : ∀ p : MvPolynomial (Fin 3) K,
      psi (Ideal.Quotient.mk (Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h)) p) = ev p :=
    fun _ => Ideal.Quotient.lift_mk _ ev hradker
  let sig : Polynomial (ZRing D.a D.b h) →+* k := Polynomial.eval₂RingHom psi t
  let fr' : MvPolynomial (Fin 3) K →+* k := fr
  have hfr' : ∀ p : MvPolynomial (Fin 3) K, fr' p = f p := fun p => rfl
  have hsigt : ∀ p : MvPolynomial (Fin 3) K, sig (theta D.a D.b h p) = f p := by
    have hcomp : sig.comp (theta D.a D.b h) = fr' := by
      apply MvPolynomial.ringHom_ext
      · intro c
        have h1 : theta D.a D.b h (MvPolynomial.C c)
            = Polynomial.C (algebraMap K (ZRing D.a D.b h) c) := by
          rw [MvPolynomial.C_eq_algebraMap, AlgHom.commutes,
            IsScalarTower.algebraMap_apply K (ZRing D.a D.b h) (Polynomial (ZRing D.a D.b h)),
            Polynomial.algebraMap_eq]
        change sig (theta D.a D.b h (MvPolynomial.C c)) = fr' (MvPolynomial.C c)
        rw [h1]
        show Polynomial.eval₂RingHom psi t (Polynomial.C (algebraMap K (ZRing D.a D.b h) c))
            = f (MvPolynomial.C c)
        rw [show Polynomial.eval₂RingHom psi t (Polynomial.C (algebraMap K (ZRing D.a D.b h) c))
            = psi (algebraMap K (ZRing D.a D.b h) c) from
              Polynomial.eval₂_C (a := algebraMap K (ZRing D.a D.b h) c) psi t]
        rw [hfC]
        rw [show algebraMap K (ZRing D.a D.b h) c = Ideal.Quotient.mk
            (Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h)) (MvPolynomial.C c) from by
          rw [← Ideal.Quotient.mk_algebraMap, MvPolynomial.C_eq_algebraMap]]
        rw [hpsimk, hevC]
      · intro i
        change sig (theta D.a D.b h (MvPolynomial.X i)) = fr' (MvPolynomial.X i)
        rw [theta_X D.a D.b h i]
        show Polynomial.eval₂RingHom psi t (Polynomial.C (Ideal.Quotient.mk _
              (RVS D.a D.b h (ch3' (K := K) i))) * Polynomial.X
            + Polynomial.C (Ideal.Quotient.mk _ (RWS D.a D.b h (ch3' (K := K) i))))
          = f (MvPolynomial.X i)
        rw [map_add, map_mul,
          show Polynomial.eval₂RingHom psi t (Polynomial.C (Ideal.Quotient.mk _
              (RVS D.a D.b h (ch3' (K := K) i))))
            = psi (Ideal.Quotient.mk _ (RVS D.a D.b h (ch3' (K := K) i))) from
              Polynomial.eval₂_C (R := ZRing D.a D.b h) psi t,
          show Polynomial.eval₂RingHom psi t Polynomial.X = t from Polynomial.eval₂_X psi t,
          show Polynomial.eval₂RingHom psi t (Polynomial.C (Ideal.Quotient.mk _
              (RWS D.a D.b h (ch3' (K := K) i))))
            = psi (Ideal.Quotient.mk _ (RWS D.a D.b h (ch3' (K := K) i))) from
              Polynomial.eval₂_C (R := ZRing D.a D.b h) psi t,
          hpsimk, hpsimk]
        exact (hparam i).symm
    intro p
    exact (congrArg (fun g : MvPolynomial (Fin 3) K →+* k => g p) hcomp).trans (hfr' p)
  have hker_le : RingHom.ker (theta D.a D.b h) ≤ x.asIdeal := by
    intro p hp
    rw [RingHom.mem_ker] at hp
    exact (hf p).mp (by rw [← hsigt p, hp, map_zero])
  have hsT_mem : Work.MotK.TGen.sT D.a D.b h ∈ RingHom.ker (theta D.a D.b h) := by
    rw [RingHom.mem_ker]
    exact ThetaST K D.a D.b h
  have hheight : x.asIdeal.height = 1 :=
    (AlgebraicGeometry.idealHeight_eq_coheight (CommRingCat.of (MvPolynomial (Fin 3) K))
      x).trans hcoh
  have hker_theta : RingHom.ker (theta D.a D.b h) = x.asIdeal := by
    haveI : (RingHom.ker (theta D.a D.b h)).IsPrime := RingHom.ker_isPrime _
    have hsTne : Work.MotK.TGen.sT D.a D.b h ≠ 0 :=
      Work.MotK.TwCensus.sT_ne_zero D.a D.b h ha hb hh
    have hspan_le : Ideal.span {Work.MotK.TGen.sT D.a D.b h} ≤ RingHom.ker (theta D.a D.b h) :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hsT_mem)
    have hqne : RingHom.ker (theta D.a D.b h) ≠ ⊥ := by
      intro hbot
      have h4 : Work.MotK.TGen.sT D.a D.b h ∈ (⊥ : Ideal (MvPolynomial (Fin 3) K)) := by
        rw [← hbot]
        exact hspan_le (Ideal.subset_span (Set.mem_singleton_iff.mpr rfl))
      exact hsTne (Ideal.mem_bot.mp h4)
    have hqht : ((1 : ℕ) : ℕ∞) ≤ (RingHom.ker (theta D.a D.b h)).height := by
      have hb : (⊥ : Ideal (MvPolynomial (Fin 3) K)) < RingHom.ker (theta D.a D.b h) :=
        bot_lt_iff_ne_bot.mpr hqne
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hb
      rwa [Ideal.height_bot, zero_add] at h1
    by_contra hlt2
    have hlt : RingHom.ker (theta D.a D.b h) < x.asIdeal := lt_of_le_of_ne hker_le hlt2
    have h1 : (RingHom.ker (theta D.a D.b h)).height + 1 ≤ x.asIdeal.height :=
      Ideal.height_add_one_le_of_lt_of_isPrime hlt
    rw [hheight] at h1
    have h2 : ((1 : ℕ) : ℕ∞) + 1 ≤ ((1 : ℕ) : ℕ∞) :=
      le_trans (add_le_add hqht (le_refl ((1 : ℕ) : ℕ∞))) h1
    exact absurd h2 (by decide)
  have hs4 : theta D.a D.b h (Sklein D.a D.b h 4) ≠ 0 := by
    have hlinθ : theta D.a D.b h (linT D.a D.b h) ≠ 0 := by
      intro h0
      exact hlin_ev (by rw [← hsigt (linT D.a D.b h), h0, map_zero])
    rw [Sklein_four, map_neg]
    exact neg_ne_zero.mpr hlinθ
  have hf4 : theta D.a D.b h (fwVec D.a D.b h 4) ≠ 0 := by
    intro h0
    exact hfw ((hf _).mp (by rw [← hsigt (fwVec D.a D.b h 4), h0, map_zero]))
  obtain ⟨e1⟩ : Nonempty (Work.MotV.resF K x ≃ₐ[K] FractionRing (theta D.a D.b h).range) := by
    refine ⟨?_⟩
    show FractionRing (MvPolynomial (Fin 3) K ⧸ x.asIdeal) ≃ₐ[K]
      FractionRing (theta D.a D.b h).range
    rw [show x.asIdeal = RingHom.ker (theta D.a D.b h) from hker_theta.symm]
    refine IsFractionRing.algEquivOfAlgEquiv (R := K)
      (A := MvPolynomial (Fin 3) K ⧸ RingHom.ker (theta D.a D.b h))
      (B := ↥(theta D.a D.b h).range) ?_
    exact (AlgHom.ker_rangeRestrict (theta D.a D.b h)).symm ▸
      Ideal.quotientKerAlgEquivOfSurjective (AlgHom.rangeRestrict_surjective (theta D.a D.b h))
  obtain ⟨e2⟩ := ThetaRangeClosure K D.a D.b h ha hb hh hs4 hf4
  exact ⟨e1.trans e2⟩

/-- **Node K5: the source ruling divisor `sT` is ruled over the residual curve `V(ZI)`.** -/
theorem STRulingDivMain (K : Type) [Field K] (D : Work.MotV.KleinData K) (hD : D.Good)
    (h : K) (hh : h ≠ 0) (x : Work.MotA.polySpec K 3) (hcoh : Order.coheight x = 1)
    (hx : Work.MotK.TGen.sT D.a D.b h ∈ x.asIdeal) (ha : D.a ≠ 0) (hb : D.b ≠ 0)
    (hlin : Work.MotK.TGen.linT D.a D.b h ∉ x.asIdeal)
    (hfw : Work.MotK.TGen.fwVec D.a D.b h 4 ∉ x.asIdeal) :
    Nonempty (Work.MotV.resF K x ≃ₐ[K] FractionRing (Polynomial (MvPolynomial (Fin 3) K ⧸
      Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h)))) ∨ Work.MotV.JunkClass K x :=
  Or.inl (STRulingDivMain_of_domain K D hD h hh x hcoh hx ha hb hlin hfw
    (ZRingIsDomainAll K D hD h hh))

end Work.MotK.TGen
