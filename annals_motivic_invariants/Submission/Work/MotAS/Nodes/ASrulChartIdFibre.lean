import Mathlib
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotAS.ASRul.kleinMAS_fibre
import Submission.Work.MotAS.KleinTwScalarAS
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option autoImplicit false

/-!
# `Work.MotAS.Nodes.ASrulChartIdFibre`

The fibre of the AS Klein matrix `kleinMAS` over an integral domain: two vectors of the kernel are
proportional over the fraction field.  This is the (forward) direction of
`Work.MotAS.ASRul.kleinMAS_fibre`, transportable from a domain to its fraction field.
-/

namespace Work.MotAS.Nodes

/-- `Matrix.mulVec` commutes with ring homomorphisms. -/
theorem mulVec_map' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (M : Matrix (Fin 5) (Fin 5) R) (y : Fin 5 → R) :
    Matrix.mulVec (Matrix.map M φ) (fun j => φ (y j)) = fun i => φ (Matrix.mulVec M y i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five, Matrix.map_apply, map_add, map_mul]

/-- Naturality of the AS Klein matrix. -/
theorem map_kleinMAS' {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (a b g : R)
    (y : Fin 5 → R) :
    Matrix.map (Work.MotAS.ASRul.kleinMAS a b g y) φ
      = Work.MotAS.ASRul.kleinMAS (φ a) (φ b) (φ g) (fun i => φ (y i)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.map_apply, Work.MotAS.ASRul.kleinMAS, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.head_cons, Matrix.tail_cons, Matrix.empty_eq, Matrix.of_apply, Matrix.cons_val',
      Fin.isValue, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, map_add, map_mul, map_sub,
      map_neg, map_ofNat, map_zero]

/-- **The fibre of the AS Klein matrix over an integral domain.**  If `c` lies in the kernel of
`kleinMAS a b g y` and `kleinPAS a b g y ≠ 0`, then `kleinPAS a b g y` and `c` are proportional
over the fraction field of `R`. -/
theorem kleinMAS_fibre_fraction' {R : Type} [CommRing R] [IsDomain R] (h5 : (5 : R) = 0)
    (a b g : R) (y c : Fin 5 → R)
    (hy : Work.MotAS.kleinPAS a b g y ≠ 0) (hc : c ≠ 0)
    (hker : Matrix.mulVec (Work.MotAS.ASRul.kleinMAS a b g y) c = 0) :
    ∃ μ : FractionRing R, μ ≠ 0 ∧ ∀ i : Fin 5,
      algebraMap R (FractionRing R) (Work.MotAS.kleinPAS a b g y i)
        = μ * algebraMap R (FractionRing R) (c i) := by
  let K := FractionRing R
  haveI : CharP R 5 := (CharP.charP_iff_prime_eq_zero (R := R) (by norm_num)).mpr h5
  haveI : CharP K 5 := CharP.of_ringHom_of_ne_zero (algebraMap R K) 5 (by norm_num)
  have hnat := Work.MotAS.KleinTwScalarAS_map_kleinPAS (algebraMap R K) a b g y
  have hmap := map_kleinMAS' (algebraMap R K) a b g y
  have hy' : Work.MotAS.kleinPAS (algebraMap R K a) (algebraMap R K b) (algebraMap R K g)
      (fun i => algebraMap R K (y i)) ≠ 0 := by
    intro h0
    apply hy
    funext i
    refine IsFractionRing.injective R K ?_
    have h1 : Work.MotAS.kleinPAS (algebraMap R K a) (algebraMap R K b) (algebraMap R K g)
        (fun i => algebraMap R K (y i)) i = 0 := by rw [h0]; rfl
    rw [← congrFun hnat i]
    simpa using h1
  have hc' : (fun i => algebraMap R K (c i)) ≠ 0 := by
    intro h0
    apply hc
    funext i
    refine IsFractionRing.injective R K ?_
    have h1 := congrFun h0 i
    simpa using h1
  have hker' : Matrix.mulVec (Work.MotAS.ASRul.kleinMAS (algebraMap R K a) (algebraMap R K b)
      (algebraMap R K g) (fun i => algebraMap R K (y i)))
      (fun i => algebraMap R K (c i)) = 0 := by
    rw [← hmap, mulVec_map']
    funext i
    have h := congrFun (congrArg (fun v : Fin 5 → R => fun i => algebraMap R K (v i)) hker) i
    simpa using h
  obtain ⟨μ, hμ, hμ'⟩ := (Work.MotAS.ASRul.kleinMAS_fibre K (algebraMap R K a) (algebraMap R K b)
    (algebraMap R K g) (fun i => algebraMap R K (y i)) (fun i => algebraMap R K (c i)) hy'
    hc').mp hker'
  exact ⟨μ, hμ, fun i => by
    rw [← congrFun hnat i]
    exact hμ' i⟩

/-- **The fibre of the AS Klein matrix over an integral domain, in the domain itself.**  If `c` lies
in the kernel of `kleinMAS a b g y` and `kleinPAS a b g y ≠ 0`, then `kleinPAS a b g y` and `c` are
proportional *in `R`* after clearing the zeroth coordinate. -/
theorem kleinMAS_fibre_domain {R : Type} [CommRing R] [IsDomain R] (h5 : (5 : R) = 0)
    (a b g : R) (y c : Fin 5 → R)
    (hy : Work.MotAS.kleinPAS a b g y ≠ 0) (hc : c ≠ 0)
    (hker : Matrix.mulVec (Work.MotAS.ASRul.kleinMAS a b g y) c = 0) (j : Fin 5) :
    Work.MotAS.kleinPAS a b g y 0 * c j = Work.MotAS.kleinPAS a b g y j * c 0 := by
  let K := FractionRing R
  obtain ⟨μ, hμ, hμ'⟩ := kleinMAS_fibre_fraction' h5 a b g y c hy hc hker
  refine IsFractionRing.injective R K ?_
  rw [map_mul, map_mul, hμ' 0, hμ' j]
  first | refl_ring1 | ring

end Work.MotAS.Nodes
