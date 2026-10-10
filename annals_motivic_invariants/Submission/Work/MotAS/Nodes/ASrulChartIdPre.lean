import Mathlib
import Submission.Work.MotAS.Nodes.ASCertGen.P3Kernel
import Submission.Work.MotAS.Nodes.ASrulChartIdFibre
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotAS.ASRul.kleinMAS_fibre
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.ASChartGeo
import Submission.Work.MotAS.KleinTwScalarAS
import Submission.Work.MotAS.ASRulingMainAux
import Submission.Work.MotAS.ASRulV2.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end


set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
set_option autoImplicit false

namespace Work.MotAS.Nodes

open MvPolynomial

/-- The coordinate ring `A = K[X₀,X₁,X₂] ⧸ √(ZIAS a b g)` of the AS residual curve. -/
abbrev AQ (K : Type) [Field K] (a b g : K) : Type := Work.MotC5N3.ASrulA a b g

/-- `A[T]`. -/
abbrev PQ (K : Type) [Field K] (a b g : K) : Type := Polynomial (AQ K a b g)

/-- `S = A[T][1/ε]`, `ε = ASrulEpsA a b g`. -/
abbrev SQ (K : Type) [Field K] [CharP K 5] (a b g : K) : Type :=
  Localization.Away (Polynomial.C (Work.MotC5N3.ASrulEpsA a b g))

/-! ## §1  Generic identities for the AS link data -/

/-- The fifth AS Pfaffian is minus the twisted quadric. -/
theorem kleinPAS_four_gen {R : Type*} [CommRing R] (a b g : R) (y : Fin 5 → R) :
    Work.MotAS.kleinPAS a b g y 4 = -Work.MotAS.kleinQAS a b y := by
  simp only [Work.MotAS.kleinPAS, Work.MotAS.kleinPAS4, Work.MotAS.kleinQAS,
    Matrix.cons_val', Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons,
    Matrix.tail_cons, Fin.isValue, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one]
  first | refl_ring1 | ring

/-- The vector `e₀ = (1,0,0,0,0)`. -/
def e0v (R : Type*) [CommRing R] : Fin 5 → R := ![1, 0, 0, 0, 0]

@[simp] theorem e0v_zero (R : Type*) [CommRing R] : e0v R 0 = 1 := rfl
@[simp] theorem e0v_one (R : Type*) [CommRing R] : e0v R 1 = 0 := rfl
@[simp] theorem e0v_two (R : Type*) [CommRing R] : e0v R 2 = 0 := rfl
@[simp] theorem e0v_three (R : Type*) [CommRing R] : e0v R 3 = 0 := rfl
@[simp] theorem e0v_four (R : Type*) [CommRing R] : e0v R 4 = 0 := rfl

/-- `e₀` lies on the quadric. -/
theorem kleinQAS_e0v (R : Type*) [CommRing R] (a b : R) :
    Work.MotAS.kleinQAS a b (e0v R) = 0 := by
  simp only [Work.MotAS.kleinQAS, e0v_zero, e0v_one, e0v_two, e0v_three, e0v_four]
  first | refl_ring1 | ring

/-- Homogeneity of the AS Pfaffian vector, in the `•`-form. -/
theorem kleinPAS_smul' {R : Type*} [CommRing R] (a b g c : R) (v : Fin 5 → R) :
    Work.MotAS.kleinPAS a b g (c • v) = c ^ 2 • Work.MotAS.kleinPAS a b g v := by
  rw [show c • v = (fun i => c * v i) from by funext i; simp only [Pi.smul_apply, smul_eq_mul]]
  rw [Work.MotAS.kleinPAS_smul]
  funext i
  simp only [Pi.smul_apply, smul_eq_mul]

/-- The quadric identity for the projection `π_e x = x - x₀·e`:
`q(π_e x) + x₀·b(e, π_e x) = q(x) - x₀²·q(e)`. -/
theorem kleinQAS_kleinTwPi_add {R : Type*} [CommRing R] (a b : R) (e x : Fin 5 → R) :
    Work.MotAS.kleinQAS a b (Work.MotK.kleinTwPi e x)
        + x 0 * Work.MotAS.kleinBilinAS a b e (Work.MotK.kleinTwPi e x)
      = Work.MotAS.kleinQAS a b x - (x 0) ^ 2 * Work.MotAS.kleinQAS a b e := by
  simp only [Work.MotK.kleinTwPi, Work.MotAS.kleinQAS, Work.MotAS.kleinBilinAS, Pi.sub_apply,
    Pi.mul_apply, Pi.add_apply]
  first | refl_ring1 | ring

/-- **The inverse-stereographic identity at a quadric point**: if `e` and `x` lie on the quadric
then the stereographic parametrisation at `π_e x` is a multiple of `x`. -/
theorem kleinStereoAS_pi_eq {R : Type*} [CommRing R] (a b : R) (e x : Fin 5 → R)
    (he : Work.MotAS.kleinQAS a b e = 0) (hx : Work.MotAS.kleinQAS a b x = 0) :
    Work.MotAS.kleinStereoAS a b e (Work.MotK.kleinTwPi e x)
      = (-Work.MotAS.kleinBilinAS a b e (Work.MotK.kleinTwPi e x)) • x := by
  have hkey : Work.MotAS.kleinQAS a b (Work.MotK.kleinTwPi e x)
      = - (x 0) * Work.MotAS.kleinBilinAS a b e (Work.MotK.kleinTwPi e x) := by
    have h := kleinQAS_kleinTwPi_add a b e x
    rw [he, hx] at h
    linear_combination (norm := first | refl_ring1 | ring1) h
  funext i
  simp only [Work.MotAS.kleinStereoAS, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [hkey]
  simp only [Work.MotK.kleinTwPi, Pi.sub_apply]
  first | refl_ring1 | ring

/-- Naturality of the twisted quadric. -/
theorem map_kleinQAS' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (y : Fin 5 → R) :
    φ (Work.MotAS.kleinQAS a b y) = Work.MotAS.kleinQAS (φ a) (φ b) (fun i => φ (y i)) := by
  simp only [Work.MotAS.kleinQAS, map_add, map_sub, map_mul, map_pow, map_ofNat, map_neg]
  try ring

/-- Naturality of the polar form. -/
theorem map_kleinBilinAS' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (u v : Fin 5 → R) :
    φ (Work.MotAS.kleinBilinAS a b u v)
      = Work.MotAS.kleinBilinAS (φ a) (φ b) (fun i => φ (u i)) (fun i => φ (v i)) := by
  have h : (fun i => φ ((u + v) i)) = (fun i => φ (u i)) + (fun i => φ (v i)) := by
    funext i; simp only [Pi.add_apply, map_add]
  simp only [Work.MotAS.kleinBilinAS, map_sub]
  rw [map_kleinQAS' φ a b (u + v), h, map_kleinQAS' φ a b u, map_kleinQAS' φ a b v]

/-- Naturality of the stereographic parametrisation (vector form). -/
theorem map_kleinStereoAS_vec {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (p v : Fin 5 → R) :
    (fun i => φ (Work.MotAS.kleinStereoAS a b p v i))
      = Work.MotAS.kleinStereoAS (φ a) (φ b) (fun j => φ (p j)) (fun j => φ (v j)) := by
  funext i
  simp only [Work.MotAS.kleinStereoAS, Pi.sub_apply, Pi.mul_apply, map_sub, map_mul]
  rw [map_kleinQAS' φ a b v, map_kleinBilinAS' φ a b p v]

/-! ## §2  The ruling line, the base point and the source point in `A[T]` -/

/-- `5 = 0` in `A[T]`. -/
theorem five_eq_zero_PQ (K : Type) [Field K] [CharP K 5] (a b g : K) : (5 : PQ K a b g) = 0 := by
  have h5K : (5 : K) = 0 := CharP.cast_eq_zero K 5
  have h5X : (5 : MvPolynomial (Fin 3) K) = 0 := by
    rw [show (5 : MvPolynomial (Fin 3) K) = MvPolynomial.C (5 : K) from (map_ofNat _ 5).symm,
      h5K, map_zero]
  have h5A : (5 : AQ K a b g) = 0 := by
    rw [show (5 : AQ K a b g) = Ideal.Quotient.mk _ (5 : MvPolynomial (Fin 3) K)
        from (map_ofNat _ 5).symm, h5X, map_zero]
  rw [show (5 : PQ K a b g) = Polynomial.C (5 : AQ K a b g) from (map_ofNat _ 5).symm, h5A,
    map_zero]

/-- The source point `π_{e₀}(zvT)` of the ruling line in `A[T]`. -/
noncomputable def piV (K : Type) [Field K] (a b g : K) : Fin 5 → PQ K a b g :=
  Work.MotK.kleinTwPi (e0v (PQ K a b g)) (Work.MotAS.Nodes.ASGen.zvT a b g)

/-- The stereographic image `y = kleinStereoAS e₀ (π_{e₀}(zvT))` in `A[T]`. -/
noncomputable def yV (K : Type) [Field K] (a b g : K) : Fin 5 → PQ K a b g :=
  Work.MotAS.kleinStereoAS (algebraMap K (PQ K a b g) a) (algebraMap K (PQ K a b g) b)
    (e0v (PQ K a b g)) (piV K a b g)

/-- The image of the ruling line: `Q = kleinPAS zvT`. -/
noncomputable def QV (K : Type) [Field K] [CharP K 5] (a b g : K) : Fin 5 → PQ K a b g :=
  Work.MotAS.kleinPAS (algebraMap K (PQ K a b g) a) (algebraMap K (PQ K a b g) b)
    (algebraMap K (PQ K a b g) g) (Work.MotAS.Nodes.ASGen.zvT a b g)

/-- The image of the source point: `P = kleinPAS y`. -/
noncomputable def PV (K : Type) [Field K] [CharP K 5] (a b g : K) : Fin 5 → PQ K a b g :=
  Work.MotAS.kleinPAS (algebraMap K (PQ K a b g) a) (algebraMap K (PQ K a b g) b)
    (algebraMap K (PQ K a b g) g) (yV K a b g)

@[simp] theorem asCh3_zero : Work.MotAS.asCh3 (0 : Fin 3) = 1 := rfl
@[simp] theorem asCh3_one : Work.MotAS.asCh3 (1 : Fin 3) = 2 := rfl
@[simp] theorem asCh3_two : Work.MotAS.asCh3 (2 : Fin 3) = 3 := rfl

/-- The `(i+1)`-st coordinate of the generic base point is the class of `X i`. -/
theorem cvT_asCh3 (K : Type) [Field K] (a b g : K) (i : Fin 3) :
    Work.MotAS.Nodes.ASGen.cvT a b g (Work.MotAS.asCh3 i)
      = Polynomial.C (Ideal.Quotient.mk (Ideal.radical (Work.MotAS.ZIAS a b g))
          (MvPolynomial.X i)) := by
  rw [Work.MotAS.Nodes.ASGen.cvT, Work.MotAS.Nodes.ASGen.asMk, Work.MotAS.asBaseVec]
  fin_cases i <;> rfl

/-- The zeroth coordinate of the source point vanishes. -/
theorem piV_zero (K : Type) [Field K] (a b g : K) : piV K a b g 0 = 0 := by
  rw [piV, Work.MotK.kleinTwPi]
  simp

/-- The `(i+1)`-st coordinate of the source point is the `(i+1)`-st coordinate of the ruling
line. -/
theorem piV_asCh3 (K : Type) [Field K] (a b g : K) (i : Fin 3) :
    piV K a b g (Work.MotAS.asCh3 i) = Work.MotAS.Nodes.ASGen.zvT a b g (Work.MotAS.asCh3 i) := by
  rw [piV, Work.MotK.kleinTwPi]
  have h : e0v (PQ K a b g) (Work.MotAS.asCh3 i) = 0 := by
    fin_cases i <;> rfl
  rw [h, mul_zero, sub_zero]

/-- The ruling line lies on the AS quadric. -/
theorem QAS_zvT (K : Type) [Field K] [CharP K 5] (a b g : K)
    (hDZ : IsDomain (AQ K a b g)) :
    Work.MotAS.kleinQAS (algebraMap K (PQ K a b g) a) (algebraMap K (PQ K a b g) b)
      (Work.MotAS.Nodes.ASGen.zvT a b g) = 0 := by
  have hkerz : Matrix.mulVec (Work.MotAS.ASRul.kleinMAS (algebraMap K (PQ K a b g) a)
      (algebraMap K (PQ K a b g) b) (algebraMap K (PQ K a b g) g)
      (Work.MotAS.Nodes.ASGen.zvT a b g))
      (Work.MotAS.Nodes.ASGen.cvT a b g) = 0 := by
    rw [← Work.MotAS.AmatAS2_mulVec]
    exact Work.MotAS.Nodes.ASGen.AmatAS2_zvT_cvT a b g
  have hcv : Work.MotAS.Nodes.ASGen.cvT a b g ≠ 0 := by
    intro h0
    have h1 : Work.MotAS.Nodes.ASGen.cvT a b g 0 = 0 := congrFun h0 0
    rw [Work.MotAS.Nodes.ASGen.cvT_zero a b g] at h1
    exact one_ne_zero h1
  by_cases hQ : QV K a b g = 0
  · have h4 : Work.MotAS.kleinPAS (algebraMap K (PQ K a b g) a) (algebraMap K (PQ K a b g) b)
        (algebraMap K (PQ K a b g) g) (Work.MotAS.Nodes.ASGen.zvT a b g) 4 = 0 := by
      have hh := congrFun hQ 4
      rw [QV] at hh
      exact hh
    rw [kleinPAS_four_gen] at h4
    exact neg_eq_zero.mp h4
  · have hprop := kleinMAS_fibre_domain (five_eq_zero_PQ K a b g)
      (algebraMap K (PQ K a b g) a) (algebraMap K (PQ K a b g) b) (algebraMap K (PQ K a b g) g)
      (Work.MotAS.Nodes.ASGen.zvT a b g) (Work.MotAS.Nodes.ASGen.cvT a b g) hQ hcv hkerz
    have hzero : Work.MotAS.kleinPAS (algebraMap K (PQ K a b g) a) (algebraMap K (PQ K a b g) b)
        (algebraMap K (PQ K a b g) g) (Work.MotAS.Nodes.ASGen.zvT a b g) 4 = 0 := by
      have h4 := hprop 4
      rw [Work.MotAS.Nodes.ASGen.cvT_four, Work.MotAS.Nodes.ASGen.cvT_zero a b g, mul_one,
        mul_zero] at h4
      exact h4.symm
    have h4' : Work.MotAS.kleinQAS (algebraMap K (PQ K a b g) a) (algebraMap K (PQ K a b g) b)
        (Work.MotAS.Nodes.ASGen.zvT a b g)
        = - Work.MotAS.kleinPAS (algebraMap K (PQ K a b g) a) (algebraMap K (PQ K a b g) b)
            (algebraMap K (PQ K a b g) g) (Work.MotAS.Nodes.ASGen.zvT a b g) 4 := by
      rw [kleinPAS_four_gen, neg_neg]
    rw [h4', hzero, neg_zero]

/-- The source point of the ruling line is a multiple of the ruling line. -/
theorem yV_eq (K : Type) [Field K] [CharP K 5] (a b g : K) (hDZ : IsDomain (AQ K a b g)) :
    yV K a b g = (-Work.MotAS.kleinBilinAS (algebraMap K (PQ K a b g) a)
        (algebraMap K (PQ K a b g) b) (e0v (PQ K a b g)) (piV K a b g))
        • (Work.MotAS.Nodes.ASGen.zvT a b g) := by
  rw [yV]
  exact kleinStereoAS_pi_eq (algebraMap K (PQ K a b g) a) (algebraMap K (PQ K a b g) b)
    (e0v (PQ K a b g)) (Work.MotAS.Nodes.ASGen.zvT a b g)
    (kleinQAS_e0v (PQ K a b g) (algebraMap K (PQ K a b g) a) (algebraMap K (PQ K a b g) b))
    (QAS_zvT K a b g hDZ)


end Work.MotAS.Nodes
