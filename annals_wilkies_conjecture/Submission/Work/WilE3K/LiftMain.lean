/-
  annals_wilkies_conjecture, AREA E3K: the lift of a `SepChainLocal` system into an `ETData`.

  Builds on `LiftSetup.lean` (the definitions) and proves:
  * `hasFDerivAt_liftPoint` — the derivative of the lift map `x ↦ liftPoint S E x`;
  * `jac_det_ne_zero` — nondegeneracy of the lifted points, from the entrywise identity
    `ev_d_eq` (proved in `LiftJac.lean`);
  * `liftPoint_injective`, `atomDeg_liftG_le` — the cardinality and degree bookkeeping.
-/
import Submission.Work.WilE3K.LiftSetup
import Submission.Work.WilE3K.ContAux
import Submission.Work.WilE3.Realify.SepChainLocal_fderiv_ev
import Submission.Work.WilE3.Realify.Defs
import Mathlib

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

variable {n r : ℕ}

/-! ## §1. The derivative of the affine forms -/

theorem ell_hasFDerivAt (S : Work.WilE3.SepChainLocal n r) (j : Fin r) (x : Fin n → ℝ) :
    HasFDerivAt (fun y => Lift.ell S j y)
      (∑ i, S.a j i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
  have h1 : HasFDerivAt (fun y : Fin n → ℝ => ∑ i, S.a j i * y i)
      (∑ i, S.a j i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) x := by
    have h := HasFDerivAt.sum (u := Finset.univ)
      (A := fun i (y : Fin n → ℝ) => S.a j i * y i)
      (A' := fun i => S.a j i • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ))
      (fun i _ => (hasFDerivAt_apply i x).const_mul (S.a j i))
    have key : (∑ i, (fun y : Fin n → ℝ => S.a j i * y i))
        = (fun y : Fin n → ℝ => ∑ i, S.a j i * y i) := by
      funext y; simp
    rw [key] at h
    exact h
  have h2 := h1.add_const (S.b j)
  have key : (fun y : Fin n → ℝ => (∑ i, S.a j i * y i) + S.b j) = (fun y => Lift.ell S j y) := by
    funext y; simp [Lift.ell]
  rwa [key] at h2

/-! ## §2. The derivative of the lift map -/

/-- The derivative of the lift map: `1 + t_p²` times the derivative of `ℓ_{j_p}` on the `tan`
coordinates, the coordinate projection on the free ones. -/
def liftLinComp (S : Work.WilE3.SepChainLocal n r)
    (E : ETData (Lift.rt S + n - 1) (Lift.rt S) n (Lift.re S)) (x : Fin n → ℝ)
    (c : Fin ((Lift.rt S + n - 1) + 1)) : (Fin n → ℝ) →L[ℝ] ℝ :=
  if h : (c : ℕ) < Lift.rt S then
    (1 + (Lift.liftT S x ⟨(c : ℕ), h⟩) ^ 2) •
      (∑ i, S.a (Lift.tanIdx S ⟨(c : ℕ), h⟩) i •
        (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ))
  else ContinuousLinearMap.proj (E.freeIndex c (not_lt.mp h))

/-- The derivative of the lift map, as a continuous linear map. -/
def liftLin (S : Work.WilE3.SepChainLocal n r)
    (E : ETData (Lift.rt S + n - 1) (Lift.rt S) n (Lift.re S)) (x : Fin n → ℝ) :
    (Fin n → ℝ) →L[ℝ] (Fin ((Lift.rt S + n - 1) + 1) → ℝ) :=
  ContinuousLinearMap.pi (liftLinComp S E x)

theorem liftLinComp_tan (S : Work.WilE3.SepChainLocal n r)
    (E : ETData (Lift.rt S + n - 1) (Lift.rt S) n (Lift.re S)) (x : Fin n → ℝ)
    (c : Fin ((Lift.rt S + n - 1) + 1)) (hc : (c : ℕ) < Lift.rt S) :
    liftLinComp S E x c =
      (1 + (Lift.liftT S x ⟨(c : ℕ), hc⟩) ^ 2) •
        (∑ i, S.a (Lift.tanIdx S ⟨(c : ℕ), hc⟩) i •
          (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) := by
  rw [liftLinComp, dif_pos hc]

theorem liftLinComp_free (S : Work.WilE3.SepChainLocal n r)
    (E : ETData (Lift.rt S + n - 1) (Lift.rt S) n (Lift.re S)) (x : Fin n → ℝ)
    (c : Fin ((Lift.rt S + n - 1) + 1)) (hc : ¬ (c : ℕ) < Lift.rt S) :
    liftLinComp S E x c = ContinuousLinearMap.proj (E.freeIndex c (not_lt.mp hc)) := by
  rw [liftLinComp, dif_neg hc]

theorem hasFDerivAt_liftPoint (S : Work.WilE3.SepChainLocal n r) (htype : Lift.IsET S)
    (E : ETData (Lift.rt S + n - 1) (Lift.rt S) n (Lift.re S)) (x₀ : Fin n → ℝ)
    (hx : ∀ j, Lift.ell S j x₀ ∈ S.dom j) :
    HasFDerivAt (fun x => Lift.liftPoint S E x) (liftLin S E x₀) x₀ := by
  rw [liftLin, hasFDerivAt_pi]
  intro c
  by_cases hc : (c : ℕ) < Lift.rt S
  · rw [liftLinComp_tan S _ x₀ c hc]
    have hpt : ∀ x, Lift.liftPoint S E x c
        = Lift.liftT S x ⟨(c : ℕ), hc⟩ :=
      fun x => Lift.liftPoint_tan S E x ⟨(c : ℕ), hc⟩
    have hmem : Lift.ell S (Lift.tanIdx S ⟨(c : ℕ), hc⟩) x₀
        ∈ S.dom (Lift.tanIdx S ⟨(c : ℕ), hc⟩) := hx _
    have hcomp := (S.hderiv _ _ hmem).comp_hasFDerivAt x₀ (ell_hasFDerivAt S _ x₀)
    change HasFDerivAt (fun y => S.phi (Lift.tanIdx S ⟨(c : ℕ), hc⟩)
        (Lift.ell S (Lift.tanIdx S ⟨(c : ℕ), hc⟩) y)) _ x₀ at hcomp
    have hfun : (fun y => S.phi (Lift.tanIdx S ⟨(c : ℕ), hc⟩)
          (Lift.ell S (Lift.tanIdx S ⟨(c : ℕ), hc⟩) y))
        = (fun y => Lift.liftT S y ⟨(c : ℕ), hc⟩) := by
      funext y
      rw [Lift.liftT, Lift.phi_tanIdx]
    have hval : ((S.R (Lift.tanIdx S ⟨(c : ℕ), hc⟩)).eval
          (fun _ => S.phi (Lift.tanIdx S ⟨(c : ℕ), hc⟩)
            (Lift.ell S (Lift.tanIdx S ⟨(c : ℕ), hc⟩) x₀)))
        = 1 + (Lift.liftT S x₀ ⟨(c : ℕ), hc⟩) ^ 2 := by
      rw [Lift.R_tanIdx S htype, Lift.phi_tanIdx S]
      simp [Lift.liftT, MvPolynomial.eval_X]
    rw [hfun, hval] at hcomp
    exact hcomp.congr_of_eventuallyEq (EventuallyEq.of_eq (funext hpt))
  · rw [liftLinComp_free S _ x₀ c hc]
    have hpt : ∀ x, Lift.liftPoint S E x c
        = x (E.freeIndex c (not_lt.mp hc)) := fun x =>
      calc Lift.liftPoint S E x c
          = Lift.liftPoint S E x (E.freeCoord (E.freeIndex c (not_lt.mp hc))) := by
            rw [ETData.freeCoord_freeIndex]
        _ = x (E.freeIndex c (not_lt.mp hc)) :=
            Lift.liftPoint_free S E x _
    exact (hasFDerivAt_apply _ x₀).congr_of_eventuallyEq (EventuallyEq.of_eq (funext hpt))

/-! ## §3. The cardinality and degree bookkeeping -/

theorem liftPoint_injective (S : Work.WilE3.SepChainLocal n r)
    (E : ETData (Lift.rt S + n - 1) (Lift.rt S) n (Lift.re S)) :
    Function.Injective (fun x => Lift.liftPoint S E x) := by
  intro x y h
  funext a
  have h1 := congrFun h (E.freeCoord a)
  simpa only [Lift.liftPoint_free] using h1

theorem atomDeg_liftG_le {N rt re n' r : ℕ} (hn : rt + n' = N + 1)
    (cls : Fin r → Fin rt ⊕ Fin re) (f : Fin n' → EAPoly n' r) (i : Fin n') :
    atomDeg (Lift.liftG hn cls f i) ≤ atomDeg (f i) := by
  have := MvPolynomial.totalDegree_rename_le (Lift.xi hn cls) (f i)
  simp only [Lift.liftG, atomDeg]
  omega

end Work.WilE3K
