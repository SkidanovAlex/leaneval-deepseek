import Mathlib
import Submission.Work.MotAS.ASData
import Submission.Work.MotK.TwAmbh
import Submission.Work.MotAS.ASTransport
import Submission.Work.MotAS.ASTransportR
import Submission.Work.MotAS.ASMatrix
import Submission.Work.MotAS.AsTransportSstage
import Submission.Work.MotAS.AsTransportSDstage
import Submission.Work.MotAS.KleinTwScalarASv
import Submission.Work.MotAS.KleinTwI3AS
import Submission.Work.MotAS.KleinTwScalarAS
import Submission.Work.MotK.KleinIdents
import Submission.Work.Reflect.PolyId

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotV5.ASChart.ASCore` — the AS link identities, free of the chart ring

This module collects the pieces of the AS (characteristic-5) Crauder–Katz link that are needed by
the *value lemmas* of the corrected affine chart (`Submission/Work/MotAS/CensusAS2.lean`), stated
over an arbitrary commutative ring of characteristic `5` and *without* the auxiliary
Artin–Schreier root `w` (the `w`-rooted forms are the transports of the split identities of
`Work.MotK`):

* `kleinStereoAS_pi_free` — the inverse-stereographic identity
  `y(π_p x) = q(x)·p − b(p,x)·x` for `q(p) = 0`;
* the homogeneity lemmas (`kleinTwPi_smul_free`, `kleinStereoAS_smul_free`, `kleinPAS_smul_free`,
  `kleinRAS_smul_free`, `kleinSecAS_smul_free`, `kleinSecDualAS_smul_free`, `kleinQAS_smul_free`,
  `kleinBilinAS_smul_right_free`);
* `kleinPAS_kleinRAS_free` — the link identity I2 `P^AS(R^AS z) = s'^AS(z)·z`, free of `w`;
* `kleinTwLinkComp2Free` — the composition `χ ∘ f` at the vector level,
  `π_p (R^AS (P^AS (y^AS(v)))) = −(b(p,v)·s^AS(y^AS(v))) • v` for `p` on the quadric, `p₀ = 1`,
  `v₀ = 0`;
* `kleinFwVecRingIdFree` — the composition `f ∘ χ` at the vector level,
  `P^AS(y^AS(π_p (R^AS w))) = b(p,R^AS w)² · s'^AS(w) • w` for `p` on the quadric and `w₄ = 0`
  (from I2 in the form of an explicit hypothesis, so that it can be used before/independently of
  the final statement of `kleinPAS_kleinRAS_free`).

The I1 and I3 identities are already available (`Work.MotAS.KleinTwScalarASv`,
`Work.MotAS.KleinTwI3AS`); I4 is `Work.MotAS.KleinTwI4ASb`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

open Polynomial

namespace Work.MotV5.ASChart

variable {R : Type*} [CommRing R]

/-! ## §0 Local copies of the two link data (so that this module does not depend on `ASLink`, which
carries the *proofs* of the both rooted and root-free link identities; the definitions below are
the definitions of `bilinAS` and `stereoAS` verbatim, so that
`rfl` identifies them in the chart modules.) -/

/-- The polar form of the AS quadric (definition of `bilinAS`). -/
def bilinAS (a b : R) (u v : Fin 5 → R) : R :=
  Work.MotAS.kleinQAS a b (u + v) - Work.MotAS.kleinQAS a b u - Work.MotAS.kleinQAS a b v

/-- Inverse stereographic projection from `p` (definition of `stereoAS`). -/
def stereoAS (a b : R) (p v : Fin 5 → R) : Fin 5 → R :=
  fun i => Work.MotAS.kleinQAS a b v * p i - bilinAS a b p v * v i

/-! ## §1 The inverse-stereographic identity and homogeneity -/

/-- The unconditional form of the inverse-stereographic identity (corrected by the `q(p)`-terms). -/
theorem kleinStereoAS_pi_aux_free (a b : R) (p x : Fin 5 → R) :
    stereoAS a b p (Work.MotK.kleinTwPi p x)
      = fun i => Work.MotAS.kleinQAS a b x * p i - bilinAS a b p x * x i
          - Work.MotAS.kleinQAS a b p * (x 0) ^ 2 * p i
          + 2 * Work.MotAS.kleinQAS a b p * x 0 * x i := by
  funext i
  simp only [stereoAS, bilinAS, Work.MotAS.kleinQAS,
    Work.MotK.kleinTwPi, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
  refl_ring1

/-- **The inverse-stereographic identity.**  For `p` on the AS quadric, the stereographic
parametrisation at the projection `x - x₀·p` of `x` is `q(x)·p - b(p,x)·x`. -/
theorem kleinStereoAS_pi_free (a b : R) (p x : Fin 5 → R)
    (hp : Work.MotAS.kleinQAS a b p = 0) :
    stereoAS a b p (Work.MotK.kleinTwPi p x)
      = fun i => Work.MotAS.kleinQAS a b x * p i - bilinAS a b p x * x i := by
  rw [kleinStereoAS_pi_aux_free a b p x, hp]
  funext i
  refl_ring1

/-- The AS quadric is homogeneous of degree two. -/
theorem kleinQAS_smul_free (a b c : R) (y : Fin 5 → R) :
    Work.MotAS.kleinQAS a b (fun i => c * y i) = c ^ 2 * Work.MotAS.kleinQAS a b y := by
  simp only [Work.MotAS.kleinQAS, Pi.mul_apply]
  refl_ring1

/-- The polar form is linear in its second argument. -/
theorem kleinBilinAS_smul_right_free (a b c : R) (u v : Fin 5 → R) :
    bilinAS a b u (fun i => c * v i) = c * bilinAS a b u v := by
  simp only [bilinAS, Work.MotAS.kleinQAS, Pi.add_apply, Pi.mul_apply]
  refl_ring1

/-- The stereographic parametrisation is homogeneous of degree two. -/
theorem kleinStereoAS_smul_free (a b c : R) (p v : Fin 5 → R) :
    stereoAS a b p (fun i => c * v i)
      = fun i => c ^ 2 * stereoAS a b p v i := by
  funext i
  simp only [stereoAS, Pi.mul_apply, kleinQAS_smul_free,
    kleinBilinAS_smul_right_free]
  refl_ring1

/-- The projection `kleinTwPi` is linear. -/
theorem kleinTwPi_smul_free (p x : Fin 5 → R) (c : R) :
    Work.MotK.kleinTwPi p (fun i => c * x i) = fun i => c * Work.MotK.kleinTwPi p x i := by
  funext i
  simp only [Work.MotK.kleinTwPi, Pi.mul_apply]
  refl_ring1

/-- The `0`-th AS Pfaffian is homogeneous of degree two. -/
theorem kleinPAS0_smul_free (a b g c : R) (y : Fin 5 → R) :
    Work.MotAS.kleinPAS0 a b g (fun i => c * y i) = c ^ 2 * Work.MotAS.kleinPAS0 a b g y := by
  simp only [Work.MotAS.kleinPAS0, Pi.mul_apply]
  refl_ring1

/-- The `1`-st AS Pfaffian is homogeneous of degree two. -/
theorem kleinPAS1_smul_free (a b g c : R) (y : Fin 5 → R) :
    Work.MotAS.kleinPAS1 a b g (fun i => c * y i) = c ^ 2 * Work.MotAS.kleinPAS1 a b g y := by
  simp only [Work.MotAS.kleinPAS1, Pi.mul_apply]
  refl_ring1

/-- The `2`-nd AS Pfaffian is homogeneous of degree two. -/
theorem kleinPAS2_smul_free (a b g c : R) (y : Fin 5 → R) :
    Work.MotAS.kleinPAS2 a b g (fun i => c * y i) = c ^ 2 * Work.MotAS.kleinPAS2 a b g y := by
  simp only [Work.MotAS.kleinPAS2, Pi.mul_apply]
  refl_ring1

/-- The `3`-rd AS Pfaffian is homogeneous of degree two. -/
theorem kleinPAS3_smul_free (a b g c : R) (y : Fin 5 → R) :
    Work.MotAS.kleinPAS3 a b g (fun i => c * y i) = c ^ 2 * Work.MotAS.kleinPAS3 a b g y := by
  simp only [Work.MotAS.kleinPAS3, Pi.mul_apply]
  refl_ring1

/-- The `4`-th AS Pfaffian is homogeneous of degree two. -/
theorem kleinPAS4_smul_free (a b g c : R) (y : Fin 5 → R) :
    Work.MotAS.kleinPAS4 a b g (fun i => c * y i) = c ^ 2 * Work.MotAS.kleinPAS4 a b g y := by
  simp only [Work.MotAS.kleinPAS4, Pi.mul_apply]
  refl_ring1

/-- The AS Pfaffians are homogeneous of degree two. -/
theorem kleinPAS_smul_free (a b g c : R) (y : Fin 5 → R) :
    Work.MotAS.kleinPAS a b g (fun i => c * y i)
      = fun i => c ^ 2 * Work.MotAS.kleinPAS a b g y i := by
  funext i
  fin_cases i
  · simpa [Work.MotAS.kleinPAS] using kleinPAS0_smul_free a b g c y
  · simpa [Work.MotAS.kleinPAS] using kleinPAS1_smul_free a b g c y
  · simpa [Work.MotAS.kleinPAS] using kleinPAS2_smul_free a b g c y
  · simpa [Work.MotAS.kleinPAS] using kleinPAS3_smul_free a b g c y
  · simpa [Work.MotAS.kleinPAS] using kleinPAS4_smul_free a b g c y

/-- The `0`-th component of the AS inverse map is homogeneous of degree three. -/
theorem kleinRAS0_smul_free (a b g c : R) (z : Fin 5 → R) :
    Work.MotAS.kleinRAS0 a b g (fun i => c * z i) = c ^ 3 * Work.MotAS.kleinRAS0 a b g z := by
  simp only [Work.MotAS.kleinRAS0, Pi.mul_apply]
  refl_ring1

/-- The `1`-st component of the AS inverse map is homogeneous of degree three. -/
theorem kleinRAS1_smul_free (a b g c : R) (z : Fin 5 → R) :
    Work.MotAS.kleinRAS1 a b g (fun i => c * z i) = c ^ 3 * Work.MotAS.kleinRAS1 a b g z := by
  simp only [Work.MotAS.kleinRAS1, Pi.mul_apply]
  refl_ring1

/-- The `2`-nd component of the AS inverse map is homogeneous of degree three. -/
theorem kleinRAS2_smul_free (a b g c : R) (z : Fin 5 → R) :
    Work.MotAS.kleinRAS2 a b g (fun i => c * z i) = c ^ 3 * Work.MotAS.kleinRAS2 a b g z := by
  simp only [Work.MotAS.kleinRAS2, Pi.mul_apply]
  refl_ring1

/-- The `3`-rd component of the AS inverse map is homogeneous of degree three. -/
theorem kleinRAS3_smul_free (a b g c : R) (z : Fin 5 → R) :
    Work.MotAS.kleinRAS3 a b g (fun i => c * z i) = c ^ 3 * Work.MotAS.kleinRAS3 a b g z := by
  simp only [Work.MotAS.kleinRAS3, Pi.mul_apply]
  refl_ring1

/-- The `4`-th component of the AS inverse map is homogeneous of degree three. -/
theorem kleinRAS4_smul_free (a b g c : R) (z : Fin 5 → R) :
    Work.MotAS.kleinRAS4 a b g (fun i => c * z i) = c ^ 3 * Work.MotAS.kleinRAS4 a b g z := by
  simp only [Work.MotAS.kleinRAS4, Pi.mul_apply]
  refl_ring1

/-- The AS inverse quadro-cubic map is homogeneous of degree three. -/
theorem kleinRAS_smul_free (a b g c : R) (z : Fin 5 → R) :
    Work.MotAS.kleinRAS a b g (fun i => c * z i)
      = fun i => c ^ 3 * Work.MotAS.kleinRAS a b g z i := by
  funext i
  fin_cases i
  · simpa [Work.MotAS.kleinRAS] using kleinRAS0_smul_free a b g c z
  · simpa [Work.MotAS.kleinRAS] using kleinRAS1_smul_free a b g c z
  · simpa [Work.MotAS.kleinRAS] using kleinRAS2_smul_free a b g c z
  · simpa [Work.MotAS.kleinRAS] using kleinRAS3_smul_free a b g c z
  · simpa [Work.MotAS.kleinRAS] using kleinRAS4_smul_free a b g c z

/-- The AS source secant quintic is homogeneous of degree five. -/
theorem kleinSecAS_smul_free (a b g c : R) (y : Fin 5 → R) :
    Work.MotAS.kleinSecAS a b g (fun i => c * y i) = c ^ 5 * Work.MotAS.kleinSecAS a b g y := by
  simp only [Work.MotAS.kleinSecAS, Pi.mul_apply]
  refl_ring1

/-- The AS dual secant quintic is homogeneous of degree five. -/
theorem kleinSecDualAS_smul_free (a b g c : R) (z : Fin 5 → R) :
    Work.MotAS.kleinSecDualAS a b g (fun i => c * z i)
      = c ^ 5 * Work.MotAS.kleinSecDualAS a b g z := by
  simp only [Work.MotAS.kleinSecDualAS, Pi.mul_apply]
  refl_ring1

/-! ## §2 Naturality of the chart data along a ring homomorphism -/

/-- Naturality of the AS quadric. -/
theorem map_kleinQAS_free {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (u : Fin 5 → R) :
    φ (Work.MotAS.kleinQAS a b u)
      = Work.MotAS.kleinQAS (φ a) (φ b) (fun i => φ (u i)) := by
  simp only [Work.MotAS.kleinQAS, map_add, map_sub, map_mul, map_pow, map_ofNat, map_natCast,
    map_one, map_zero, map_neg]

/-- Naturality of `bilinAS`. -/
theorem map_bilinAS_free {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (u v : Fin 5 → R) :
    φ (bilinAS a b u v) = bilinAS (φ a) (φ b) (fun i => φ (u i)) (fun i => φ (v i)) := by
  have h1 : (fun i => φ ((u + v) i)) = (fun i => φ (u i)) + (fun i => φ (v i)) := by
    funext i
    simp only [Pi.add_apply, map_add]
  simp only [bilinAS, map_sub, map_kleinQAS_free, h1]

/-- Naturality of `stereoAS`. -/
theorem map_stereoAS_free {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b : R)
    (p v : Fin 5 → R) :
    (fun i => φ (stereoAS a b p v i))
      = stereoAS (φ a) (φ b) (fun i => φ (p i)) (fun i => φ (v i)) := by
  funext i
  simp only [stereoAS, Pi.sub_apply, Pi.mul_apply, map_sub, map_mul, map_kleinQAS_free,
    map_bilinAS_free]

/-- Naturality of the projection `kleinTwPi`. -/
theorem map_kleinTwPi_free {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (p x : Fin 5 → R) :
    (fun i => φ (Work.MotK.kleinTwPi p x i))
      = Work.MotK.kleinTwPi (fun i => φ (p i)) (fun i => φ (x i)) := by
  funext i
  simp only [Work.MotK.kleinTwPi, map_sub, map_mul]

/-! ## §3 The link identity I2, free of the auxiliary root -/

/-- **I2^AS with an auxiliary root.**  In any commutative ring with `5 = 0` containing an element
`w` with `w ^ 5 = w + g`, the AS coordinates satisfy `P^AS (R^AS z) = s'^AS(z) • z`. -/
theorem kleinPAS_kleinRAS_vec (a b g w : R) (h5 : (5 : R) = 0)
    (hw : w ^ 5 = w + g) (z : Fin 5 → R) :
    Work.MotAS.kleinPAS a b g (Work.MotAS.kleinRAS a b g z)
      = fun i => Work.MotAS.kleinSecDualAS a b g z * z i := by
  apply Work.MotAS.asN_mulVec_injective h5 w
  rw [← Work.MotAS.asTransportP a b g w h5 hw (Work.MotAS.kleinRAS a b g z)]
  change Work.MotK.kleinP a b ((Work.MotAS.asM w).mulVec (Work.MotAS.kleinRAS a b g z))
    = (Work.MotAS.asN w).mulVec (fun i => Work.MotAS.kleinSecDualAS a b g z * z i)
  rw [← Work.MotAS.asTransportR a b g w h5 hw z]
  rw [show Work.MotK.kleinP a b
        (Work.MotK.kleinR a b (fun k => ∑ j, Work.MotAS.asN w k j * z j))
      = fun i => Work.MotK.kleinSecDual a b (fun k => ∑ j, Work.MotAS.asN w k j * z j)
          * (∑ j, Work.MotAS.asN w i j * z j) from
    funext fun i => Work.MotK.kleinP_kleinR a b _ i]
  rw [Work.MotAS.AsTransportSDstage a b g w h5 hw z]
  ext i
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **I2^AS, free of the auxiliary root**: `P^AS (R^AS z) = s'^AS(z) • z` in every commutative ring
with `5 = 0`. -/
theorem kleinPAS_kleinRAS_free (a b g : R) (z : Fin 5 → R) (h5 : (5 : R) = 0) :
    Work.MotAS.kleinPAS a b g (Work.MotAS.kleinRAS a b g z)
      = fun i => Work.MotAS.kleinSecDualAS a b g z * z i := by
  by_cases hone : (1 : R) = 0
  · haveI : Subsingleton R := ⟨fun x y => by
      have hx : x = 0 := by rw [← mul_one x, hone, mul_zero]
      have hy : y = 0 := by rw [← one_mul y, hone, zero_mul]
      rw [hx, hy]⟩
    exact Subsingleton.elim _ _
  · haveI : Nontrivial R := ⟨0, 1, fun h => hone h.symm⟩
    set p : Polynomial R := Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g with hpdef
    have hpmonic : p.Monic := by
      rw [hpdef, show (Polynomial.X ^ 5 - Polynomial.X - Polynomial.C g : Polynomial R)
        = Polynomial.X ^ 5 - (Polynomial.X + Polynomial.C g) by ring]
      refine Polynomial.monic_X_pow_sub ?_
      calc ((Polynomial.X + Polynomial.C g : Polynomial R).degree)
          ≤ max (Polynomial.X : Polynomial R).degree
              (Polynomial.C g : Polynomial R).degree := Polynomial.degree_add_le _ _
        _ ≤ max (1 : WithBot ℕ) 0 :=
            max_le_max Polynomial.degree_X_le Polynomial.degree_C_le
        _ = 1 := max_eq_left (WithBot.coe_le_coe.mpr (Nat.zero_le 1))
        _ < (5 : WithBot ℕ) := WithBot.coe_lt_coe.mpr (by norm_num)
    have hcoeff : p.coeff 5 = 1 := by
      rw [hpdef]
      simp [Polynomial.coeff_X_pow_self, Polynomial.coeff_X, Polynomial.coeff_C]
    have hdeg5 : (5 : WithBot ℕ) ≤ p.degree :=
      Polynomial.le_degree_of_ne_zero (by rw [hcoeff]; exact hone)
    have hw : (AdjoinRoot.root p) ^ 5
        = AdjoinRoot.root p + algebraMap R (AdjoinRoot p) g := by
      have h : (AdjoinRoot.root p) ^ 5 - AdjoinRoot.root p
          - algebraMap R (AdjoinRoot p) g = 0 := by
        have h := AdjoinRoot.eval₂_root p
        simpa only [hpdef, AdjoinRoot.algebraMap_eq, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
          Polynomial.eval₂_X, Polynomial.eval₂_C] using h
      have h4 : (AdjoinRoot.root p) ^ 5 - AdjoinRoot.root p = algebraMap R (AdjoinRoot p) g :=
        sub_eq_zero.mp h
      calc (AdjoinRoot.root p) ^ 5
          = ((AdjoinRoot.root p) ^ 5 - AdjoinRoot.root p) + AdjoinRoot.root p :=
            (sub_add_cancel _ _).symm
        _ = algebraMap R (AdjoinRoot p) g + AdjoinRoot.root p := by rw [h4]
        _ = AdjoinRoot.root p + algebraMap R (AdjoinRoot p) g := by rw [add_comm]
    have h5A : (5 : AdjoinRoot p) = 0 := by
      have h' : algebraMap R (AdjoinRoot p) (5 : R) = 0 := by rw [h5, map_zero]
      rw [← map_ofNat (algebraMap R (AdjoinRoot p)) 5]
      exact h'
    have hinj : Function.Injective (algebraMap R (AdjoinRoot p)) := by
      intro x y hxy
      by_contra hne
      have hCz : Polynomial.C (x - y) ≠ 0 :=
        Polynomial.C_ne_zero.mpr (sub_ne_zero.mpr hne)
      have hdeglt : (Polynomial.C (x - y)).degree < p.degree :=
        lt_of_le_of_lt (Polynomial.degree_C_le)
          (lt_of_lt_of_le (WithBot.coe_lt_coe.mpr (by norm_num : (0 : ℕ) < 5)) hdeg5)
      have hsub : algebraMap R (AdjoinRoot p) (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      have hmk : AdjoinRoot.mk p (Polynomial.C (x - y)) = 0 := by
        rw [AdjoinRoot.mk_C]
        exact hsub
      rw [AdjoinRoot.mk_eq_zero] at hmk
      exact (hpmonic.not_dvd_of_degree_lt hCz hdeglt) hmk
    have hmain := kleinPAS_kleinRAS_vec (algebraMap R (AdjoinRoot p) a)
      (algebraMap R (AdjoinRoot p) b) (algebraMap R (AdjoinRoot p) g) (AdjoinRoot.root p)
      h5A hw (fun j => algebraMap R (AdjoinRoot p) (z j))
    rw [Work.MotAS.KleinTwScalarAS_map_kleinRAS (algebraMap R (AdjoinRoot p)) a b g z]
      at hmain
    rw [Work.MotAS.KleinTwScalarAS_map_kleinPAS (algebraMap R (AdjoinRoot p)) a b g
      (Work.MotAS.kleinRAS a b g z)] at hmain
    rw [Work.MotAS.KleinTwI3AS_map_kleinSecDualAS (algebraMap R (AdjoinRoot p)) a b g z]
      at hmain
    funext i
    apply hinj
    simpa only [map_mul] using congrFun hmain i

/-! ## §3 The two composed ring identities on the chart vectors -/

/-- The fourth AS Pfaffian is minus the AS quadric (a polynomial identity in the coordinates; the
parameter `g` does not occur). -/
theorem kleinPAS_four_eq_neg_free (a b g : R) (y : Fin 5 → R) :
    Work.MotAS.kleinPAS a b g y 4 = -Work.MotAS.kleinQAS a b y := by
  simp only [Work.MotAS.kleinPAS, Work.MotAS.kleinPAS4, Work.MotAS.kleinQAS, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four]
  refl_ring1

/-- **`χ ∘ f` at the vector level.**  For `p` on the quadric with `p 0 = 1` and `v 0 = 0`, the
projection of `R^AS (P^AS (y^AS(v)))` is the scalar multiple
`-b(p,v)·s^AS(y^AS(v))` of `v`. -/
theorem kleinTwLinkComp2Free (a b g : R) (h5 : (5 : R) = 0) (p v : Fin 5 → R)
    (hp : Work.MotAS.kleinQAS a b p = 0) (hp0 : p 0 = 1) (hv0 : v 0 = 0) :
    Work.MotK.kleinTwPi p
        (Work.MotAS.kleinRAS a b g (Work.MotAS.kleinPAS a b g
          (stereoAS a b p v)))
      = fun i => -(bilinAS a b p v
            * Work.MotAS.kleinSecAS a b g (stereoAS a b p v)) * v i := by
  have h1 : Work.MotAS.kleinRAS a b g (Work.MotAS.kleinPAS a b g
        (stereoAS a b p v))
      = fun i => Work.MotAS.kleinSecAS a b g (stereoAS a b p v)
          * stereoAS a b p v i :=
    Work.MotAS.KleinTwScalarASv a b g (stereoAS a b p v) h5
  rw [h1, kleinTwPi_smul_free]
  have h2 : Work.MotK.kleinTwPi p (stereoAS a b p v)
      = fun i => -(bilinAS a b p v) * v i := by
    funext i
    simp only [Work.MotK.kleinTwPi]
    rw [show stereoAS a b p v i
        = Work.MotAS.kleinQAS a b v * p i - bilinAS a b p v * v i from rfl,
      show stereoAS a b p v 0 = Work.MotAS.kleinQAS a b v from by
        show Work.MotAS.kleinQAS a b v * p 0 - bilinAS a b p v * v 0
          = Work.MotAS.kleinQAS a b v
        rw [hp0, hv0, mul_one, mul_zero, sub_zero]]
    refl_ring1
  rw [h2]
  funext i
  first | refl_ring1 | ring

/-- **`f ∘ χ` at the vector level.**  For `p` on the quadric and `w` in the target hyperplane
`{w 4 = 0}` (so that `R^AS w` lies on the quadric), the forward map at the projection of `R^AS w`
is the scalar multiple `b(p, R^AS w)^2 · s'^AS(w)` of `w`. -/
theorem kleinFwVecRingIdFree (a b g : R) (p w : Fin 5 → R)
    (hp : Work.MotAS.kleinQAS a b p = 0) (hw : w 4 = 0)
    (hI2 : Work.MotAS.kleinPAS a b g (Work.MotAS.kleinRAS a b g w)
      = fun i => Work.MotAS.kleinSecDualAS a b g w * w i) :
    Work.MotAS.kleinPAS a b g (stereoAS a b p
        (Work.MotK.kleinTwPi p (Work.MotAS.kleinRAS a b g w)))
      = fun i => (bilinAS a b p (Work.MotAS.kleinRAS a b g w)) ^ 2
          * Work.MotAS.kleinSecDualAS a b g w * w i := by
  have h4 := congrFun hI2 4
  rw [kleinPAS_four_eq_neg_free, hw, mul_zero] at h4
  have hq : Work.MotAS.kleinQAS a b (Work.MotAS.kleinRAS a b g w) = 0 := neg_eq_zero.mp h4
  have hst : stereoAS a b p
        (Work.MotK.kleinTwPi p (Work.MotAS.kleinRAS a b g w))
      = fun i => -(bilinAS a b p (Work.MotAS.kleinRAS a b g w))
          * Work.MotAS.kleinRAS a b g w i := by
    rw [kleinStereoAS_pi_free a b p (Work.MotAS.kleinRAS a b g w) hp, hq]
    funext i
    refl_ring1
  rw [hst, kleinPAS_smul_free, hI2]
  funext i
  first | refl_ring1 | ring

end Work.MotV5.ASChart
