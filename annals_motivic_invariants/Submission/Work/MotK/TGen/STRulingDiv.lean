import Mathlib
import Submission.Work.MotK.TGen.CensusFactors
import Submission.Work.MotK.TwCensus.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotA.Defs
import Submission.Work.MotK.TGen.JunkClassKleinTwBilinChart
import Submission.Work.MotK.CensusPrime.eq_span_of_height_one
import Submission.Work.MotK.TGen.KleinTwFibre_eq_ker
import Submission.Work.MotK.TwCensus.K5Ruling
import Submission.Work.MotK.CensusBridge.resF_span_eq_ratFunc
import Submission.Work.MotK.TwCensus.STRulingDefs
import Submission.Work.MotK.TGen.ChartMaps
import Submission.Work.MotK.KleinTwData.map_data
import Submission.Work.MotK.TGen.STRulingAux
-- NOTE (area owner): the junk conversions `Work.MotK.fwVec4JunkAll` / `cubTJunkAll` used
-- by this file moved to `TGen/JunkConversions.lean`; importing that module instead of
-- `LinkCertTGenInf.lean` breaks the import cycle that would otherwise forbid
-- `LinkCertTGenInf.lean` from stating the target theorem `Work.MotK.LinkCertTGenInf`.
import Submission.Work.MotK.TGen.JunkConversions
import Submission.Work.MotK.TGen.ThetaS
import Submission.Work.MotK.TGen.ThetaFwVec
import Submission.Work.MotK.TGen.ThetaST
import Submission.Work.MotK.TGen.ThetaRangeClosure
import Submission.Work.MotK.TGen.FwVec4ResF
import Submission.Work.MotK.TGen.STRulingDivMain
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotK.TGen.STRulingDiv` — the source ruling divisor `sT` is ruled over the curve `V(ZI)`

`Work.MotK.TGen.sT a b h` is the degree-`10` source ruling divisor of the T-twisted
Crauder--Katz link.  `Work.MotK.TwCensus.Zcub a b h j` are the five cubics of the inverse map in
the affine chart `chart3 = (0, X₀, X₁, X₂, 1)`, whose common zero locus is the base curve
`Z = V(ZI a b h)` of the ruling (the positive-dimensional fibre locus of the twisted quadro map,
`Work.MotK.TwCensus.STRulingDefs`).

The statement (`Work.MotK.TGen.STRulingDiv`) is: every codimension-one point `x` of `𝔸³` at which
`sT` vanishes has residue field `FractionRing (Polynomial (K[x] ⧸ radical ZI))` — the function field
of `Z × 𝔸¹` — or is *junk* (`Work.MotV.JunkClass`).

## The route

`linT a b h = a·b·X₁ + a²h·X₂` is the linear factor of `GambT`; by
`Work.MotK.TGen.JunkClassKleinTwBilinChart` every codimension-one point containing `linT` is junk.
So it remains to treat the codimension-one points `x ∋ sT` with `linT ∉ x`.

For such an `x`, put `k := resF K x`, and let `v j` be the images of `X j` in `k`.  Because
`linT(v) ≠ 0`, the stereographic point `y := kleinTwStereo a b h pRa (chart3(v))` is defined, and
`kleinTwS a b h y = sT(v) = 0`.  Hence `c' := kleinTwP a b h y` satisfies
`kleinTwR a b h c' = (kleinTwS a b h y) • y = 0` (`Work.MotK.KleinTwI1`), i.e. `c'` is a point of
the base curve `V(ZI)`: indeed `c' 0 = 0` (`Work.MotK.TGen.fwVec_zero`) and `kleinTwR` is
homogeneous of degree three, so `(Zcub a b h j)(c' 1 / c' 4, c' 2 / c' 4, c' 3 / c' 4) = 0`.

Two further facts about the ruling turn this into the required isomorphism:

* the ruling line over `c'` is `ker (AmatP a b h c')`, spanned by `rv`, `rw`
  (`AmatP_ker_eq_span`), and the Pfaffian identity `kleinTwM(y) · kleinTwP(y) = 0`
  (`Work.MotK.TGen.KleinTwM_mulVec_kleinTwP`) together with `Amat_mulVec`
  (`Work.MotK.TwCensus.Amat_mulVec`) shows `y` lies on it;
* `f̂₄ = fwVec a b h 4 = c' 4` does not vanish on the component: `fwVec 4` and `sT` have no
  common factor (`fwVec_four_notMem_of_sT`), so `c' 4 ≠ 0` and the affine coordinates above are
  defined.

Then `φ : A[X] → k` (`A = K[x] ⧸ radical (ZI a b h)`), sending the class of `X j` to the affine
coordinate of `c'` and `X` to the ruling parameter `t := y 3 / y 4`, is a `K`-algebra map whose
image's fraction field is `k` (the ruling parametrisation `σ^* : K[x] → A[X]` exhibits the `v j`
as the values of `φ`), whence `k ≅ FractionRing (A[X])` — the first disjunct of the statement.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option maxHeartbeats 40000000

namespace Work.MotK.TGen

open MvPolynomial

variable {K : Type*} [Field K]

/-! ## The delegated pieces -/

/-- **Homogeneity of the twisted inverse map.**  `kleinTwR` is a cubic map:
`kleinTwR a b h (c • y) = c^3 • kleinTwR a b h y`.  This is what turns a point `c'` of the base
curve into a point of the affine chart `{z₄ = 1}`. -/
theorem kleinTwR_smul {R : Type*} [CommRing R] (a b h c : R) (y : Fin 5 → R) :
    Work.MotK.kleinTwR a b h (c • y) = c ^ 3 • Work.MotK.kleinTwR a b h y := by
  funext k
  fin_cases k
  · show Work.MotK.kleinTwR0 a b h (c • y) = c ^ 3 * Work.MotK.kleinTwR0 a b h y
    simp only [Work.MotK.kleinTwR0, Pi.smul_apply, smul_eq_mul]
    first | refl_ring1 | ring
  · show Work.MotK.kleinTwR1 a b h (c • y) = c ^ 3 * Work.MotK.kleinTwR1 a b h y
    simp only [Work.MotK.kleinTwR1, Pi.smul_apply, smul_eq_mul]
    first | refl_ring1 | ring
  · show Work.MotK.kleinTwR2 a b h (c • y) = c ^ 3 * Work.MotK.kleinTwR2 a b h y
    simp only [Work.MotK.kleinTwR2, Pi.smul_apply, smul_eq_mul]
    first | refl_ring1 | ring
  · show Work.MotK.kleinTwR3 a b h (c • y) = c ^ 3 * Work.MotK.kleinTwR3 a b h y
    simp only [Work.MotK.kleinTwR3, Pi.smul_apply, smul_eq_mul]
    first | refl_ring1 | ring
  · show Work.MotK.kleinTwR4 a b h (c • y) = c ^ 3 * Work.MotK.kleinTwR4 a b h y
    simp only [Work.MotK.kleinTwR4, Pi.smul_apply, smul_eq_mul]
    first | refl_ring1 | ring

/-! ## Naturality of the chart data under a ring homomorphism -/

section Naturality

variable {S : Type*} [CommRing S]

/-- **`sT` is natural.** -/
theorem map_sT_ring (f : MvPolynomial (Fin 3) K →+* S) (a b h : K) :
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
theorem map_fwVec_ring (f : MvPolynomial (Fin 3) K →+* S) (a b h : K) :
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

/-- **`Zcub` is natural.** -/
theorem map_Zcub_ring (f : MvPolynomial (Fin 3) K →+* S) (a b h : K) :
    (fun j => f (Work.MotK.TwCensus.Zcub a b h j))
      = Work.MotK.kleinTwR (f (MvPolynomial.C a)) (f (MvPolynomial.C b)) (f (MvPolynomial.C h))
          (fun i => f (Work.MotK.chart3 K i)) := by
  have hR : ∀ (y : Fin 5 → MvPolynomial (Fin 3) K) (k : Fin 5),
      f (Work.MotK.kleinTwR (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C h) y k)
        = Work.MotK.kleinTwR (f (MvPolynomial.C a)) (f (MvPolynomial.C b))
            (f (MvPolynomial.C h)) (fun i => f (y i)) k :=
    fun y k => (Work.MotK.KleinTwData.map_data f (MvPolynomial.C a) (MvPolynomial.C b)
      (MvPolynomial.C h)).2.2.2.2.2 y k
  funext j
  rw [Work.MotK.TwCensus.Zcub, hR _ j]

/-- **The chart `chart3` under a `K`-algebra map.**  `(fun i => φ (chart3 K i))` is the
explicit vector `![0, φ (X 0), φ (X 1), φ (X 2), 1]`. -/
theorem eval_chart3 {S : Type*} [CommRing S]
    (φ : MvPolynomial (Fin 3) K →+* S) :
    (fun i => φ (Work.MotK.chart3 K i))
      = ![0, φ (MvPolynomial.X 0), φ (MvPolynomial.X 1), φ (MvPolynomial.X 2), 1] := by
  rw [show (Work.MotK.chart3 K : Fin 5 → MvPolynomial (Fin 3) K)
    = ![0, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 1] from rfl]
  have h2 : (fun i => φ (![0, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 1] i))
      = ![φ 0, φ (MvPolynomial.X 0), φ (MvPolynomial.X 1), φ (MvPolynomial.X 2), φ 1] := by
    rw [show (fun i => φ (![0, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 1] i))
        = (φ : MvPolynomial (Fin 3) K → S) ∘ ![0, MvPolynomial.X 0, MvPolynomial.X 1,
            MvPolynomial.X 2, 1] from rfl]
    simp only [Matrix.vecCons, Fin.comp_cons, Matrix.empty_eq]
  rw [h2, map_zero, map_one]

end Naturality


/-- **The `Zcub` evaluation.**  The five cubics of the inverse map, evaluated at the chart point
`(0,u,v,w,1)`, are the components of `kleinTwR a b h ![0,u,v,w,1]`.

(Proved by the direct computation of `kleinTwR_k`; the `map_Zcub_ring`-based proof is blocked by
an instance diamond on `k`, see the note in the class branch.) -/
theorem Zcub_eval_eq {K : Type*} [Field K] (a b h u v w : K) (j : Fin 5) :
    MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Zcub a b h j)
      = Work.MotK.kleinTwR a b h ![0, u, v, w, 1] j := by
  rw [Work.MotK.TwCensus.Zcub]
  fin_cases j
  · show MvPolynomial.eval ![u, v, w] (Work.MotK.kleinTwR0 (MvPolynomial.C a)
        (MvPolynomial.C b) (MvPolynomial.C h) (Work.MotK.chart3 K))
      = Work.MotK.kleinTwR0 a b h ![0, u, v, w, 1]
    simp only [Work.MotK.kleinTwR0, Work.MotK.kleinTwR1, Work.MotK.kleinTwR2,
      Work.MotK.kleinTwR3, Work.MotK.kleinTwR4, Work.MotK.chart3, map_add, map_sub,
      map_mul, map_pow, map_neg, map_zero, map_one, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four]
  · show MvPolynomial.eval ![u, v, w] (Work.MotK.kleinTwR1 (MvPolynomial.C a)
        (MvPolynomial.C b) (MvPolynomial.C h) (Work.MotK.chart3 K))
      = Work.MotK.kleinTwR1 a b h ![0, u, v, w, 1]
    simp only [Work.MotK.kleinTwR0, Work.MotK.kleinTwR1, Work.MotK.kleinTwR2,
      Work.MotK.kleinTwR3, Work.MotK.kleinTwR4, Work.MotK.chart3, map_add, map_sub,
      map_mul, map_pow, map_neg, map_zero, map_one, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four]
  · show MvPolynomial.eval ![u, v, w] (Work.MotK.kleinTwR2 (MvPolynomial.C a)
        (MvPolynomial.C b) (MvPolynomial.C h) (Work.MotK.chart3 K))
      = Work.MotK.kleinTwR2 a b h ![0, u, v, w, 1]
    simp only [Work.MotK.kleinTwR0, Work.MotK.kleinTwR1, Work.MotK.kleinTwR2,
      Work.MotK.kleinTwR3, Work.MotK.kleinTwR4, Work.MotK.chart3, map_add, map_sub,
      map_mul, map_pow, map_neg, map_zero, map_one, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four]
  · show MvPolynomial.eval ![u, v, w] (Work.MotK.kleinTwR3 (MvPolynomial.C a)
        (MvPolynomial.C b) (MvPolynomial.C h) (Work.MotK.chart3 K))
      = Work.MotK.kleinTwR3 a b h ![0, u, v, w, 1]
    simp only [Work.MotK.kleinTwR0, Work.MotK.kleinTwR1, Work.MotK.kleinTwR2,
      Work.MotK.kleinTwR3, Work.MotK.kleinTwR4, Work.MotK.chart3, map_add, map_sub,
      map_mul, map_pow, map_neg, map_zero, map_one, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four]
  · show MvPolynomial.eval ![u, v, w] (Work.MotK.kleinTwR4 (MvPolynomial.C a)
        (MvPolynomial.C b) (MvPolynomial.C h) (Work.MotK.chart3 K))
      = Work.MotK.kleinTwR4 a b h ![0, u, v, w, 1]
    simp only [Work.MotK.kleinTwR0, Work.MotK.kleinTwR1, Work.MotK.kleinTwR2,
      Work.MotK.kleinTwR3, Work.MotK.kleinTwR4, Work.MotK.chart3, map_add, map_sub,
      map_mul, map_pow, map_neg, map_zero, map_one, MvPolynomial.eval_C,
      MvPolynomial.eval_X, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_zero,
      Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_four]

/-! ## The main case: the residual curve is a domain -/

/-- `Sklein a b h 4 = -linT a b h`. -/
theorem Sklein_four_eq_neg_linT {K : Type} [Field K] (a b h : K) :
    Sklein a b h 4 = -linT a b h := by
  simp only [Sklein, linT, Work.MotK.kleinTwStereo, Work.MotK.kleinTwQ, Work.MotK.kleinTwBilin,
    Work.MotK.kleinTwP0, Work.MotK.pRa, Work.MotK.kleinPointT, Work.MotK.chart3,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons,
    map_zero, map_one, Pi.add_apply, Pi.sub_apply, mul_zero, sub_zero, mul_one]
  first | refl_ring1 | ring

theorem algMap_rv {K : Type} [Field K] {S : Type} [Field S] (g : K →+* S) (a b h : K)
    (i : Fin 5) :
    MvPolynomial.map g (Work.MotK.TwCensus.rv a b h i)
      = Work.MotK.TwCensus.rv (g a) (g b) (g h) i := by
  fin_cases i <;>
    simp [Work.MotK.TwCensus.rv, map_div₀]

theorem algMap_rw {K : Type} [Field K] {S : Type} [Field S] (g : K →+* S) (a b h : K)
    (i : Fin 5) :
    MvPolynomial.map g (Work.MotK.TwCensus.rw a b h i)
      = Work.MotK.TwCensus.rw (g a) (g b) (g h) i := by
  fin_cases i <;>
    simp [Work.MotK.TwCensus.rw, map_div₀]

theorem algMap_RVS {K : Type} [Field K] {S : Type} [Field S] (g : K →+* S) (a b h : K)
    (i : Fin 5) :
    MvPolynomial.map g (RVS a b h i) = RVS (g a) (g b) (g h) i := by
  have hkp : g (Work.MotK.kleinPointT a b h i)
      = Work.MotK.kleinPointT (g a) (g b) (g h) i := by
    fin_cases i <;> simp [Work.MotK.kleinPointT, map_div₀]
  rw [RVS, RVS]
  simp only [map_sub, map_mul, MvPolynomial.map_C, hkp, algMap_rv g a b h i,
    algMap_rv g a b h 0]

theorem algMap_RWS {K : Type} [Field K] {S : Type} [Field S] (g : K →+* S) (a b h : K)
    (i : Fin 5) :
    MvPolynomial.map g (RWS a b h i) = RWS (g a) (g b) (g h) i := by
  have hkp : g (Work.MotK.kleinPointT a b h i)
      = Work.MotK.kleinPointT (g a) (g b) (g h) i := by
    fin_cases i <;> simp [Work.MotK.kleinPointT, map_div₀]
  rw [RWS, RWS]
  simp only [map_sub, map_mul, MvPolynomial.map_C, hkp, algMap_rw g a b h i,
    algMap_rw g a b h 0]



/-! ### The argument over the abstract fraction field -/

theorem STRulingDiv_main_aux (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K)
    (hh : h ≠ 0) (x : Work.MotA.polySpec K 3) (hcoh : Order.coheight x = 1)
    (hx : Work.MotK.TGen.sT D.a D.b h ∈ x.asIdeal) (ha : D.a ≠ 0) (hb : D.b ≠ 0)
    (hlin : Work.MotK.TGen.linT D.a D.b h ∉ x.asIdeal)
    (hfw : Work.MotK.TGen.fwVec D.a D.b h 4 ∉ x.asIdeal)
    (k' : Type) [Field k'] [Algebra K k']
    [Algebra (MvPolynomial (Fin 3) K ⧸ x.asIdeal) k']
    [IsScalarTower K (MvPolynomial (Fin 3) K ⧸ x.asIdeal) k']
    [IsFractionRing (MvPolynomial (Fin 3) K ⧸ x.asIdeal) k']
    (hdom : IsDomain (Work.MotK.TGen.ZRing D.a D.b h)) :
    Nonempty (k' ≃ₐ[K] FractionRing (Polynomial (Work.MotK.TGen.ZRing D.a D.b h))) := by
  haveI hxp : x.asIdeal.IsPrime := x.isPrime
  let q := MvPolynomial (Fin 3) K ⧸ x.asIdeal
  let f : MvPolynomial (Fin 3) K →+* k' := (algebraMap q k').comp (Ideal.Quotient.mk x.asIdeal)
  have hfC : ∀ c : K, f (MvPolynomial.C c) = algebraMap K k' c := by
    intro c
    show algebraMap q k' (Ideal.Quotient.mk x.asIdeal
      (algebraMap K (MvPolynomial (Fin 3) K) c)) = algebraMap K k' c
    rw [Ideal.Quotient.mk_algebraMap, ← IsScalarTower.algebraMap_apply K q k']
  have h_ev_eq : ∀ p : MvPolynomial (Fin 3) K, f p = 0 ↔ p ∈ x.asIdeal := by
    intro p
    constructor
    · intro hp
      exact Ideal.Quotient.eq_zero_iff_mem.mp (IsFractionRing.injective q k' (by
        show algebraMap q k' (Ideal.Quotient.mk x.asIdeal p) = algebraMap q k' 0
        rw [map_zero]; exact hp))
    · intro hp
      show algebraMap q k' (Ideal.Quotient.mk x.asIdeal p) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]
  have halg : ∀ c : K, c ≠ 0 → f (MvPolynomial.C c) ≠ 0 := by
    intro c hc h0
    have h2 : MvPolynomial.C c ∈ x.asIdeal := (h_ev_eq _).mp h0
    have h3 : (1 : MvPolynomial (Fin 3) K) ∈ x.asIdeal := by
      have h4 := x.asIdeal.mul_mem_right (MvPolynomial.C c⁻¹) h2
      rw [← map_mul, mul_inv_cancel₀ hc, map_one] at h4
      exact h4
    exact hxp.ne_top (Ideal.eq_top_iff_one _ |>.mpr h3)
  have hlin_ev : f (Work.MotK.TGen.linT D.a D.b h) ≠ 0 := fun hh0 => hlin ((h_ev_eq _).mp hh0)
  let vpt : Fin 3 → k' := fun i => f (MvPolynomial.X i)
  let cpt : Fin 5 → k' := ![0, vpt 0, vpt 1, vpt 2, 1]
  have hcptf : cpt = (fun i => f (Work.MotK.chart3 K i)) := by
    rw [eval_chart3 f]
  let pK : Fin 5 → k' := fun i => f (Work.MotK.pRa D.a D.b h i)
  let y : Fin 5 → k' := Work.MotK.kleinTwStereo (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) pK cpt
  have hy_def : y = Work.MotK.kleinTwStereo (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) (fun i => f (Work.MotK.pRa D.a D.b h i))
      (fun i => f (Work.MotK.chart3 K i)) := by
    rw [show y = Work.MotK.kleinTwStereo (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) pK cpt from rfl, hcptf]
  have hs : Work.MotK.kleinTwS (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) y = 0 := by
    have h1 : f (Work.MotK.TGen.sT D.a D.b h) = 0 := (h_ev_eq _).mpr hx
    rw [hy_def]
    exact (map_sT_ring f D.a D.b h).symm.trans h1
  let c' : Fin 5 → k' := Work.MotK.kleinTwP (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) y
  have hc'def : c' = Work.MotK.kleinTwP (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) y := rfl
  have hc : Work.MotK.kleinTwR (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) c' = 0 := by
    funext j
    simp only [hc'def, Work.MotK.KleinTwI1, hs, zero_mul, Pi.zero_apply]
  have hp0 : Work.MotK.kleinTwQ (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) pK = 0 := by
    have hQ := (Work.MotK.KleinTwData.map_data f (MvPolynomial.C D.a) (MvPolynomial.C D.b)
      (MvPolynomial.C h)).1
    rw [← hQ (Work.MotK.pRa D.a D.b h), Work.MotK.kleinTwQ_pRa D.a D.b h ha hh, map_zero]
  have hc0 : c' 0 = 0 := by
    rw [hc'def]
    show Work.MotK.kleinTwQ (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) y = 0
    rw [show y = Work.MotK.kleinTwStereo (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) (fun i => f (Work.MotK.pRa D.a D.b h i))
        (fun i => f (Work.MotK.chart3 K i)) from hy_def,
      Work.MotK.KleinTwQ_stereo, hp0, mul_zero]
  have hc4 : c' 4 ≠ 0 := by
    intro h0
    have h1 : f (Work.MotK.TGen.fwVec D.a D.b h 4) = c' 4 := by
      rw [hc'def, hy_def]
      exact congrFun (map_fwVec_ring f D.a D.b h) 4
    exact hfw ((h_ev_eq _).mp (h1.trans h0))
  let u : k' := c' 1 / c' 4
  let v : k' := c' 2 / c' 4
  let w : k' := c' 3 / c' 4
  let bp : Fin 5 → k' := ![0, u, v, w, 1]
  have hc'_scal : c' = c' 4 • bp := by
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
      (f (MvPolynomial.C h)) bp = 0 := by
    have h1 : (c' 4) ^ 3 • Work.MotK.kleinTwR (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) bp = 0 := by
      rw [← kleinTwR_smul, ← hc'_scal]
      exact hc
    funext j
    have h2 : (c' 4) ^ 3 * Work.MotK.kleinTwR (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) bp j = 0 := by
      simpa only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] using congrFun h1 j
    exact (mul_eq_zero.mp h2).resolve_left (pow_ne_zero 3 hc4)
  -- **Step A**
  have hAker : Matrix.mulVec (Work.MotK.TwCensus.AmatP (f (MvPolynomial.C D.a))
      (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) bp) y = 0 := by
    have h1 : Matrix.mulVec (Work.MotK.TwCensus.Amat (f (MvPolynomial.C D.a))
        (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) c') y = 0 := by
      rw [Work.MotK.TwCensus.Amat_mulVec]
      have h2 := kleinTwM_mulVec_kleinTwP (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) y
      rwa [show Work.MotK.kleinTwP (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) y = c' from hc'def] at h2
    have h3 : Matrix.mulVec (Work.MotK.TwCensus.Amat (f (MvPolynomial.C D.a))
        (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) ((c' 4) • bp)) y
        = (c' 4) • Matrix.mulVec (Work.MotK.TwCensus.Amat (f (MvPolynomial.C D.a))
          (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) bp) y := by
      have hsm : Work.MotK.TwCensus.Amat (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
          (f (MvPolynomial.C h)) ((c' 4) • bp)
          = (c' 4) • Work.MotK.TwCensus.Amat (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
            (f (MvPolynomial.C h)) bp := by
        rw [← AmatP_eq_Amat', AmatP_smul_right, AmatP_eq_Amat']
      rw [hsm, Matrix.smul_mulVec]
    rw [hc'_scal, h3] at h1
    have h4 : Matrix.mulVec (Work.MotK.TwCensus.Amat (f (MvPolynomial.C D.a))
        (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) bp) y
        = 0 := (smul_eq_zero.mp h1).resolve_left hc4
    rwa [← AmatP_eq_Amat'] at h4
  -- **Step B**
  have h3zc : MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Zcub (f (MvPolynomial.C D.a))
      (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) 3) = 0 := by
    rw [Zcub_eval_eq' (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h))
      u v w 3]
    exact congrFun hxq 3
  have h4zc : MvPolynomial.eval ![u, v, w] (Work.MotK.TwCensus.Zcub (f (MvPolynomial.C D.a))
      (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) 4) = 0 := by
    rw [Zcub_eval_eq' (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h))
      u v w 4]
    exact congrFun hxq 4
  have hB := (AmatP_ker_iff (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
    (f (MvPolynomial.C h)) u v w (halg D.a ha) (halg D.b hb) h3zc h4zc) y
  obtain ⟨c₀, d₀, hycd⟩ := hB.mp hAker
  have hy3 : y 3 = c₀ := by
    have hh3 := congrFun hycd 3
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      eval_rv_three (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) u v w,
      eval_rw_three (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) u v w] at hh3
    simpa using hh3
  have hy4' : y 4 = d₀ := by
    have hh4 := congrFun hycd 4
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
      eval_rv_four (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) u v w,
      eval_rw_four (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) u v w] at hh4
    simpa using hh4
  -- **Step E**
  have hBval : Work.MotK.kleinTwBilin (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) pK cpt = f (Work.MotK.TGen.linT D.a D.b h) := by
    have hm := map_kleinTwBilin' (R := MvPolynomial (Fin 3) K) (S := k') f
      (MvPolynomial.C D.a) (MvPolynomial.C D.b) (MvPolynomial.C h)
      (Work.MotK.pRa D.a D.b h) (Work.MotK.chart3 K)
    have hL : Work.MotK.TGen.linT D.a D.b h
        = Work.MotK.kleinTwBilin (MvPolynomial.C D.a) (MvPolynomial.C D.b) (MvPolynomial.C h)
          (Work.MotK.pRa D.a D.b h) (Work.MotK.chart3 K) := rfl
    rw [hL, hm, hcptf]
  have hy4eqt : ∀ i : Fin 5, y i = Work.MotK.kleinTwQ (f (MvPolynomial.C D.a))
        (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) cpt * pK i
      - Work.MotK.kleinTwBilin (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
        (f (MvPolynomial.C h)) pK cpt * cpt i := by
    intro i
    have hst := Work.MotK.KleinTwStereo_pi_aux (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) pK cpt
    have hpi : Work.MotK.kleinTwPi pK cpt = cpt := by
      funext j'
      show cpt j' - cpt 0 * pK j' = cpt j'
      have h0 : cpt 0 = 0 := by simp [cpt]
      rw [h0, zero_mul, sub_zero]
    rw [hpi] at hst
    have hyi := congrFun hst i
    have hcpt0 : cpt 0 = 0 := by simp [cpt]
    rw [show y = Work.MotK.kleinTwStereo (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
      (f (MvPolynomial.C h)) pK cpt from rfl, hyi]
    have h2 : (2 : ℕ) ≠ 0 := by norm_num
    simp only [Pi.sub_apply, Pi.mul_apply, hcpt0, zero_pow h2, mul_zero, zero_mul,
      add_zero, sub_zero]
  have hy4val : y 4 = -f (Work.MotK.TGen.linT D.a D.b h) := by
    rw [hy4eqt 4, hBval]
    have hcpt4b : cpt 4 = 1 := by simp [cpt]
    have hpK4b : pK 4 = 0 := by
      show f (Work.MotK.pRa D.a D.b h 4) = 0
      simp [Work.MotK.pRa, Work.MotK.kleinPointT]
    rw [hcpt4b, hpK4b]
    first | refl_ring1 | ring
  have hy4ne : y 4 ≠ 0 := by rw [hy4val]; exact neg_ne_zero.mpr hlin_ev
  have hpKnat : ∀ i : Fin 5, pK i = Work.MotK.kleinPointT (f (MvPolynomial.C D.a))
      (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) i := by
    intro i
    show f (Work.MotK.pRa D.a D.b h i) = _
    rw [Work.MotK.pRa_apply, hfC]
    fin_cases i <;> simp [Work.MotK.kleinPointT, map_div₀, map_mul, hfC]
  -- **Step D**
  have hevRVS : ∀ i : Fin 5,
      MvPolynomial.eval ![u, v, w]
          (RVS (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) i)
        = MvPolynomial.eval ![u, v, w]
            (Work.MotK.TwCensus.rv (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
              (f (MvPolynomial.C h)) i)
          - pK i * MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rv (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
                (f (MvPolynomial.C h)) 0) := by
    intro i
    rw [RVS]
    simp only [map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_sub, MvPolynomial.eval_mul]
    rw [hpKnat i]
  have hevRWS : ∀ i : Fin 5,
      MvPolynomial.eval ![u, v, w]
          (RWS (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h)) i)
        = MvPolynomial.eval ![u, v, w]
            (Work.MotK.TwCensus.rw (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
              (f (MvPolynomial.C h)) i)
          - pK i * MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rw (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
                (f (MvPolynomial.C h)) 0) := by
    intro i
    rw [RWS]
    simp only [map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_sub, MvPolynomial.eval_mul]
    rw [hpKnat i]
  have hparam : ∀ j : Fin 3, vpt j = (y 3 / y 4) *
        MvPolynomial.eval ![u, v, w]
          (RVS (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h))
            (ch3' (K := k') j))
      + MvPolynomial.eval ![u, v, w]
          (RWS (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b)) (f (MvPolynomial.C h))
            (ch3' (K := k') j)) := by
    intro j
    have hcpti : ∀ i : Fin 5, cpt i = (y i - y 0 * pK i) / y 4 := by
      intro i
      have hyv : y 4 = -Work.MotK.kleinTwBilin (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
          (f (MvPolynomial.C h)) pK cpt := by
        have hpK4b : pK 4 = 0 := by
          show f (Work.MotK.pRa D.a D.b h 4) = 0
          simp [Work.MotK.pRa, Work.MotK.kleinPointT]
        have hcpt4b : cpt 4 = 1 := by simp [cpt]
        rw [hy4eqt 4, hpK4b, hcpt4b]
        first | refl_ring1 | ring
      have hkey : y i - y 0 * pK i = y 4 * cpt i := by
        have hpK0 : pK 0 = 1 := by
          show f (Work.MotK.pRa D.a D.b h 0) = 1
          simp [Work.MotK.pRa, Work.MotK.kleinPointT]
        have hc0' : cpt 0 = 0 := by simp [cpt]
        rw [hy4eqt i, hy4eqt 0, hyv, hpK0, hc0']
        first | refl_ring1 | ring
      rw [hkey]
      field_simp
    have hcptj : cpt (ch3' (K := k') j) = vpt j := by
      fin_cases j <;> rfl
    rw [← hcptj, hcpti]
    have hsplit : y (ch3' (K := k') j) - y 0 * pK (ch3' (K := k') j)
        = y 3 * (MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rv (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
                (f (MvPolynomial.C h)) (ch3' (K := k') j))
            - pK (ch3' (K := k') j) * MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rv (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
                (f (MvPolynomial.C h)) 0))
          + y 4 * (MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rw (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
                (f (MvPolynomial.C h)) (ch3' (K := k') j))
            - pK (ch3' (K := k') j) * MvPolynomial.eval ![u, v, w]
              (Work.MotK.TwCensus.rw (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
                (f (MvPolynomial.C h)) 0)) := by
      have h0 := congrFun hycd 0
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply] at h0
      have hi := congrFun hycd (ch3' (K := k') j)
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply] at hi
      rw [hy3, hy4', hi, h0]
      first | refl_ring1 | ring
    rw [hsplit, hevRVS (ch3' (K := k') j), hevRWS (ch3' (K := k') j)]
    field_simp

  -- ## Step F: the evaluation `σ` at the base point, and `σ ∘ θ = f`
  let ψ : MvPolynomial (Fin 3) K →+* k' := MvPolynomial.eval₂Hom (algebraMap K k') ![u, v, w]
  have hψC : ∀ c : K, ψ (MvPolynomial.C c) = algebraMap K k' c :=
    fun c => MvPolynomial.eval₂Hom_C (algebraMap K k') ![u, v, w] c
  have hψchart : (fun i => ψ (Work.MotK.chart3 K i)) = ![0, u, v, w, 1] := by
    rw [eval_chart3 ψ]
    funext i
    fin_cases i
    · rfl
    · exact MvPolynomial.eval₂Hom_X' (algebraMap K k') ![u, v, w] (0 : Fin 3)
    · exact MvPolynomial.eval₂Hom_X' (algebraMap K k') ![u, v, w] (1 : Fin 3)
    · exact MvPolynomial.eval₂Hom_X' (algebraMap K k') ![u, v, w] (2 : Fin 3)
    · rfl
  have hψZ : ∀ j : Fin 5, ψ (Work.MotK.TwCensus.Zcub D.a D.b h j) = 0 := by
    intro j
    have hz := congrFun (map_Zcub_ring ψ D.a D.b h) j
    rw [hz, hψchart, hψC D.a, hψC D.b, hψC h, ← hfC D.a, ← hfC D.b, ← hfC h]
    exact congrFun hxq j
  have hψRVS : ∀ i : Fin 5, ψ (RVS D.a D.b h i)
      = MvPolynomial.eval ![u, v, w] (RVS (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
          (f (MvPolynomial.C h)) i) := by
    intro i
    show MvPolynomial.eval₂ (algebraMap K k') ![u, v, w] (RVS D.a D.b h i) = _
    rw [MvPolynomial.eval₂_eq_eval_map, algMap_RVS (algebraMap K k') D.a D.b h i,
      ← hfC D.a, ← hfC D.b, ← hfC h]
  have hψRWS : ∀ i : Fin 5, ψ (RWS D.a D.b h i)
      = MvPolynomial.eval ![u, v, w] (RWS (f (MvPolynomial.C D.a)) (f (MvPolynomial.C D.b))
          (f (MvPolynomial.C h)) i) := by
    intro i
    show MvPolynomial.eval₂ (algebraMap K k') ![u, v, w] (RWS D.a D.b h i) = _
    rw [MvPolynomial.eval₂_eq_eval_map, algMap_RWS (algebraMap K k') D.a D.b h i,
      ← hfC D.a, ← hfC D.b, ← hfC h]
  have hZI : Work.MotK.TwCensus.ZI D.a D.b h ≤ RingHom.ker ψ := by
    rw [Work.MotK.TwCensus.ZI, Ideal.span_le]
    rintro x ⟨j, rfl⟩
    exact RingHom.mem_ker.mpr (hψZ j)
  have hrad : Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h) ≤ RingHom.ker ψ :=
    (RingHom.ker_isPrime ψ).radical_le_iff.mpr hZI
  let σA : Work.MotK.TGen.ZRing D.a D.b h →+* k' :=
    Ideal.Quotient.lift (Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h)) ψ hrad
  have hσAmk : ∀ r : MvPolynomial (Fin 3) K,
      σA (Ideal.Quotient.mk (Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h)) r) = ψ r :=
    fun r => Ideal.Quotient.lift_mk (Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h)) ψ hrad
  let σ : Polynomial (Work.MotK.TGen.ZRing D.a D.b h) →+* k' :=
    Polynomial.eval₂RingHom σA (y 3 / y 4)
  let θ : MvPolynomial (Fin 3) K →+* Polynomial (Work.MotK.TGen.ZRing D.a D.b h) :=
    (theta D.a D.b h).toRingHom
  have hσC : ∀ r : Work.MotK.TGen.ZRing D.a D.b h, σ (Polynomial.C r) = σA r :=
    fun r => RingHom.congr_fun (Polynomial.eval₂RingHom_comp_C σA (y 3 / y 4)) r
  have hσX : σ Polynomial.X = y 3 / y 4 := by
    show Polynomial.eval₂ σA (y 3 / y 4) Polynomial.X = y 3 / y 4
    rw [Polynomial.eval₂_X]
  have hcomp : σ.comp θ = f := by
    apply MvPolynomial.ringHom_ext
    · intro c
      show σ (θ (MvPolynomial.C c)) = f (MvPolynomial.C c)
      have hC : θ (MvPolynomial.C c)
          = Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h))
              (MvPolynomial.C c)) := by
        have h1 : (theta D.a D.b h) (MvPolynomial.C c)
            = algebraMap K (Polynomial (Work.MotK.TGen.ZRing D.a D.b h)) c := by
          rw [MvPolynomial.C_eq_algebraMap]
          exact (theta D.a D.b h).commutes c
        show (theta D.a D.b h) (MvPolynomial.C c) = _
        rw [h1, IsScalarTower.algebraMap_apply K (Work.MotK.TGen.ZRing D.a D.b h)
          (Polynomial (Work.MotK.TGen.ZRing D.a D.b h)), Polynomial.algebraMap_apply,
          Polynomial.C_inj, MvPolynomial.C_eq_algebraMap, Ideal.Quotient.mk_algebraMap]
        rw [Algebra.algebraMap_self_apply]
      rw [hC, hσC, hσAmk, hψC c, hfC c]
    · intro j
      show σ (θ (MvPolynomial.X j)) = f (MvPolynomial.X j)
      have hXj : θ (MvPolynomial.X j)
          = Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h))
                (RVS D.a D.b h (ch3' (K := K) j))) * Polynomial.X
            + Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h))
                (RWS D.a D.b h (ch3' (K := K) j))) := theta_X D.a D.b h j
      rw [hXj, map_add, map_mul, hσC, hσC, hσX, hσAmk, hσAmk, hψRVS, hψRWS]
      show _ = vpt j
      rw [hparam j]
      first
        | (congr 1; exact mul_comm _ _)
        | (simp only [mul_assoc, mul_comm, mul_left_comm])
        | ring
  have hker_le : RingHom.ker θ ≤ x.asIdeal := by
    intro p hp
    have hp0 : θ p = 0 := RingHom.mem_ker.mp hp
    refine (h_ev_eq p).mp ?_
    rw [← RingHom.congr_fun hcomp p, RingHom.comp_apply, hp0, map_zero]
  have hS4 : theta D.a D.b h (Sklein D.a D.b h 4) ≠ 0 := by
    intro h0
    have h1 : f (Sklein D.a D.b h 4) = 0 := by
      rw [← RingHom.congr_fun hcomp (Sklein D.a D.b h 4), RingHom.comp_apply,
        show θ (Sklein D.a D.b h 4) = 0 from h0, map_zero]
    rw [Sklein_four_eq_neg_linT, map_neg, neg_eq_zero] at h1
    exact hlin_ev h1
  have hffw4 : f (Work.MotK.TGen.fwVec D.a D.b h 4) = c' 4 := by
    rw [hc'def, hy_def]
    exact congrFun (map_fwVec_ring f D.a D.b h) 4
  have hF4 : theta D.a D.b h (Work.MotK.TGen.fwVec D.a D.b h 4) ≠ 0 := by
    intro h0
    have h1 : f (Work.MotK.TGen.fwVec D.a D.b h 4) = 0 := by
      rw [← RingHom.congr_fun hcomp (Work.MotK.TGen.fwVec D.a D.b h 4), RingHom.comp_apply,
        show θ (Work.MotK.TGen.fwVec D.a D.b h 4) = 0 from h0, map_zero]
    exact hc4 (hffw4 ▸ h1)
  -- ## Step G: `ker θ = x`
  have hst_mem : Work.MotK.TGen.sT D.a D.b h ∈ RingHom.ker θ :=
    RingHom.mem_ker.mpr (by
      show (theta D.a D.b h) (Work.MotK.TGen.sT D.a D.b h) = 0
      exact Work.MotK.TGen.ThetaST K D.a D.b h)
  have hker_ne_bot : RingHom.ker θ ≠ ⊥ := by
    intro h0
    have hsl : Work.MotK.TGen.sT D.a D.b h = 0 := by
      have h1 := hst_mem
      rw [h0] at h1
      simpa using h1
    exact Work.MotK.TwCensus.sT_ne_zero D.a D.b h ha hb hh hsl
  have hheight_x : x.asIdeal.height = 1 := by
    rw [AlgebraicGeometry.idealHeight_eq_coheight (CommRingCat.of (MvPolynomial (Fin 3) K)) x,
      hcoh]
  have hker_eq : RingHom.ker θ = x.asIdeal := by
    by_contra hne
    haveI hp' : (RingHom.ker θ).IsPrime := RingHom.ker_isPrime _
    have hlt : RingHom.ker θ < x.asIdeal := lt_of_le_of_ne hker_le hne
    have hx1 : x.asIdeal.height ≤ (1 : ℕ) := le_of_eq hheight_x
    have hq := (Ideal.height_le_iff.mp hx1) (RingHom.ker θ) hp' hlt
    haveI hbot' : (⊥ : Ideal (MvPolynomial (Fin 3) K)).IsPrime := Ideal.isPrime_bot
    have hbot_lt : (⊥ : Ideal (MvPolynomial (Fin 3) K)) < RingHom.ker θ :=
      lt_of_le_of_ne bot_le (Ne.symm hker_ne_bot)
    have h1le := Ideal.height_add_one_le_of_lt_of_isPrime
      (I := (⊥ : Ideal (MvPolynomial (Fin 3) K))) (J := RingHom.ker θ) hbot_lt
    rw [Ideal.height_bot, zero_add] at h1le
    exact absurd h1le (not_le_of_gt hq)
  -- ## Step H: assemble
  haveI : IsDomain (Work.MotK.TGen.ZRing D.a D.b h) := hdom
  have hker_eq' : RingHom.ker (theta D.a D.b h) = x.asIdeal := hker_eq
  have he1 := by
    letI : Semiring (MvPolynomial (Fin 3) K) := AddMonoidAlgebra.semiring
    letI : Semiring (Polynomial (Work.MotK.TGen.ZRing D.a D.b h)) := Polynomial.semiring
    exact fractionRing_quotient_ker_algEquiv (K := K) (R := MvPolynomial (Fin 3) K)
      (S := Polynomial (Work.MotK.TGen.ZRing D.a D.b h)) (theta D.a D.b h)
  obtain ⟨e1⟩ := he1
  rw [hker_eq'] at e1
  obtain ⟨e2⟩ := ThetaRangeClosure K D.a D.b h ha hb hh hS4 hF4
  have e3 : FractionRing (MvPolynomial (Fin 3) K ⧸ x.asIdeal) ≃ₐ[K] k' :=
    AlgEquiv.restrictScalars K (IsLocalization.algEquiv
      (nonZeroDivisors (MvPolynomial (Fin 3) K ⧸ x.asIdeal))
      (FractionRing (MvPolynomial (Fin 3) K ⧸ x.asIdeal)) k')
  exact ⟨e3.symm.trans (e1.trans e2)⟩

/-- **The main case, given that the residual curve is a domain.**

This is the "non-degenerate" case of `STRulingDiv`: the codimension-one points `x` with
`linT ∉ x` and `fwVec _ _ _ 4 ∉ x`.  It is proved over an abstract fraction field `k'` of
`K[x₀,x₁,x₂] ⧸ x` (see `STRulingDiv_main_aux`), which is where the whole argument lives; the
identification `k' = resF K x` is the uniqueness of the fraction ring. -/
theorem STRulingDiv_main_of_domain (K : Type) [Field K] (D : Work.MotV.KleinData K) (h : K)
    (hh : h ≠ 0) (x : Work.MotA.polySpec K 3) (hcoh : Order.coheight x = 1)
    (hx : Work.MotK.TGen.sT D.a D.b h ∈ x.asIdeal) (ha : D.a ≠ 0) (hb : D.b ≠ 0)
    (hlin : Work.MotK.TGen.linT D.a D.b h ∉ x.asIdeal)
    (hfw : Work.MotK.TGen.fwVec D.a D.b h 4 ∉ x.asIdeal)
    (hdom : IsDomain (Work.MotK.TGen.ZRing D.a D.b h)) :
    Nonempty (Work.MotV.resF K x ≃ₐ[K] FractionRing (Polynomial (MvPolynomial (Fin 3) K ⧸
      Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h)))) := by
  haveI hxp : x.asIdeal.IsPrime := x.isPrime
  exact STRulingDiv_main_aux K D h hh x hcoh hx ha hb hlin hfw (Work.MotV.resF K x) hdom

/-- **The main case of `STRulingDiv`**: `linT ∉ x` and `fwVec _ _ _ 4 ∉ x`.  The first disjunct is
proved, using the irreducibility of the residual curve (`ZRing_isDomain`). -/
theorem STRulingDiv_main (K : Type) [Field K] [Infinite K] (hk : ringChar K ≠ 5)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0)
    (x : Work.MotA.polySpec K 3) (hcoh : Order.coheight x = 1)
    (hx : Work.MotK.TGen.sT D.a D.b h ∈ x.asIdeal) (ha : D.a ≠ 0) (hb : D.b ≠ 0)
    (hlin : Work.MotK.TGen.linT D.a D.b h ∉ x.asIdeal)
    (hfw : Work.MotK.TGen.fwVec D.a D.b h 4 ∉ x.asIdeal) :
    Nonempty (Work.MotV.resF K x ≃ₐ[K] FractionRing (Polynomial (MvPolynomial (Fin 3) K ⧸
      Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h)))) ∨ Work.MotV.JunkClass K x :=
  -- `hk` is not needed by this route (the irreducibility of the residual curve is
  -- `Work.MotK.TGen.ZRingIsDomainAll`, valid in every characteristic).
  Work.MotK.TGen.STRulingDivMain K D hD h hh x hcoh hx ha hb hlin hfw

theorem STRulingDiv (K : Type) [Field K] [Infinite K] (hk : ringChar K ≠ 5)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K) (hh : h ≠ 0) :
    ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 →
      Work.MotK.TGen.sT D.a D.b h ∈ x.asIdeal →
      Nonempty (Work.MotV.resF K x ≃ₐ[K] FractionRing (Polynomial (MvPolynomial (Fin 3) K ⧸
        Ideal.radical (Work.MotK.TwCensus.ZI D.a D.b h)))) ∨ Work.MotV.JunkClass K x := by
  intro x hcoh hx
  have hab := hD.ab_ne
  have ha : D.a ≠ 0 := fun h0 => hab (by rw [h0, zero_mul])
  have hb : D.b ≠ 0 := fun h0 => hab (by rw [h0, mul_zero])
  by_cases hlin : Work.MotK.TGen.linT D.a D.b h ∈ x.asIdeal
  · exact Or.inr (Work.MotK.TGen.JunkClassKleinTwBilinChart D.a D.b h ha hb hh x hcoh hlin)
  by_cases hfw : Work.MotK.TGen.fwVec D.a D.b h 4 ∈ x.asIdeal
  · exact Or.inr (Work.MotK.fwVec4JunkAll D.a D.b h ha hb hh x hcoh hfw)
  · exact STRulingDiv_main K hk D hD h hh x hcoh hx ha hb hlin hfw

end Work.MotK.TGen
