import Mathlib
import Submission.Work.Serre.RangeEMVanDefs
import Submission.Work.Serre.Engine
import Submission.Work.Serre.hZeroOfPiZero
import Submission.Work.Serre.subsingleton_pi0_loopSpace_of_pi1
import Submission.Work.StemsB.homotopyGroup_loopSpace
import Submission.Work.StemsB.LoopShiftShifted
import Submission.Work.StemsB.fibrationLES_of_serre
import Submission.Work.StemsB.isSerreFibration_evalOne
import Submission.Work.StemsB.contractible_pathSpace
import Submission.Work.StemsB.bundlePullback_homotopyEquiv

/-!
# `RangeEMVanAll` from `RangeEMVanOne` and `SerreE3a`

The range form of the acyclicity of the Eilenberg–MacLane spaces for all degrees `a ≥ 0`, deduced
from the `1`-type case (`RangeEMVanOne`) by the loop-space induction:

for `W` connected with `π_i(W) = 0` for `1 ≤ i ≤ N`, `i ≠ a+1`, and `π_{a+1}(W)` a torsion group,
the rational homology `H_t(W;ℚ)` vanishes for `0 < t ≤ N - 1 - 2a`.

The step `a ↦ a+1` is the path–loop fibration `ΩW → PW → W`: the loop space `ΩW` has
`π_i(ΩW) = π_{i+1}(W)`, i.e. the same shape with `a ↦ a-1` and `N ↦ N-1`, so the induction
hypothesis applies to it; its rational acyclicity in the range is exactly the hypothesis of
`SerreE3a` for `evalOne : PW → W`, whose total space is contractible.  Since
`π_i(ΩW) = π_{i+1}(W)` via the currying isomorphism `Work.StemsB.stepMulEquivShifted`, and since
the homotopy fibre of `evalOne` is homotopy equivalent to `ΩW`
(`Work.StemsB.bundlePullback_homotopyEquiv` with the reversed reparametrisation contraction of the
path space), the two range losses per step are `2`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-! ## The elementary facts about `π₀`, connectedness and `H₀` -/

/-- A space whose `π₀` at some base point is a point is path connected. -/
theorem pathConnectedSpace_of_subsingleton_pi0 (X : Type) [TopologicalSpace X] (x₀ : X)
    (h : Subsingleton (HomotopyGroup (Fin 0) X x₀)) : PathConnectedSpace X := by
  refine pathConnectedSpace_iff_zerothHomotopy.mpr ⟨⟨ZerothHomotopy.mk x₀⟩, ⟨fun a b => ?_⟩⟩
  exact (HomotopyGroup.pi0EquivZerothHomotopy (x := x₀)).symm.injective (h.elim _ _)

/-- Conversely, a path connected space has `π₀` a point at every base point. -/
theorem subsingleton_pi0_of_pathConnectedSpace (X : Type) [TopologicalSpace X]
    [PathConnectedSpace X] (x : X) : Subsingleton (HomotopyGroup (Fin 0) X x) := by
  have h : Subsingleton (ZerothHomotopy X) :=
    (pathConnectedSpace_iff_zerothHomotopy.mp (inferInstance : PathConnectedSpace X)).2
  exact ⟨fun a b =>
    (HomotopyGroup.pi0EquivZerothHomotopy (x := x)).injective (Subsingleton.elim _ _)⟩

/-- `π₀` of a one-point space is a point. -/
theorem subsingleton_pi0_of_subsingleton (Y : Type) [TopologicalSpace Y] [Subsingleton Y] (y : Y) :
    Subsingleton (HomotopyGroup (Fin 0) Y y) := by
  have h : Subsingleton (ZerothHomotopy Y) :=
    inferInstanceAs (Subsingleton (Quotient (pathSetoid Y)))
  exact ⟨fun a b =>
    (HomotopyGroup.pi0EquivZerothHomotopy (x := y)).injective (Subsingleton.elim _ _)⟩

/-- **`H₀(X;ℚ) ≅ ℚ` when `π₀(X)` is a point.**  The degree-`0` case of K2
(`Work.Serre.hZeroOfPiZero`) in the form needed here: a space which is path connected has
`H₀(X;ℚ) ≅ H₀(*;ℚ)`. -/
theorem isIso_ratHomologyMap_toPoint_zero_of_subsingleton_pi0 (X : Type) [TopologicalSpace X]
    (x₀ : X) (h : Subsingleton (HomotopyGroup (Fin 0) X x₀)) :
    IsIso (ratHomologyMap (toPoint X) 0) := by
  haveI hpc : PathConnectedSpace X := pathConnectedSpace_of_subsingleton_pi0 X x₀ h
  refine hZeroOfPiZero (toPoint X) (fun x => ?_)
  haveI hx : Subsingleton (HomotopyGroup (Fin 0) X x) :=
    subsingleton_pi0_of_pathConnectedSpace X x
  haveI hy : Subsingleton (HomotopyGroup (Fin 0) PUnit (toPoint X x)) :=
    subsingleton_pi0_of_subsingleton PUnit (toPoint X x)
  exact ⟨fun a b _ => Subsingleton.elim a b,
    fun y => ⟨(HomotopyGroup.pi0EquivZerothHomotopy (x := x)).symm (ZerothHomotopy.mk x),
      Subsingleton.elim _ _⟩⟩

/-- **`RatAcyclicBelow` is a homotopy invariant.** -/
theorem ratAcyclicBelow_of_homotopyEquiv {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) {M : ℕ} (h : RatAcyclicBelow Y M) :
    RatAcyclicBelow X M := by
  have hcomp : (toPoint Y).comp e.toFun = toPoint X := ContinuousMap.ext fun x => rfl
  have hcomp' : ratHomologyMap (toPoint X) 0 =
      ratHomologyMap e.toFun 0 ≫ ratHomologyMap (toPoint Y) 0 := by
    rw [← ratHomologyMap_comp e.toFun (toPoint Y) 0, hcomp]
  refine ⟨fun t ht htM => ?_, ?_⟩
  · haveI : IsIso (ratHomologyMap e.toFun t) := IsRatHomologyIso.of_homotopyEquiv e t
    exact IsZero.of_iso (h.1 t ht htM) (asIso (ratHomologyMap e.toFun t))
  rw [hcomp']
  haveI : IsIso (ratHomologyMap e.toFun 0) := IsRatHomologyIso.of_homotopyEquiv e 0
  haveI : IsIso (ratHomologyMap (toPoint Y) 0) := h.2
  infer_instance

/-! ## The reversed reparametrisation contraction of the path space -/

/-- The reparametrisation of the path space, run backwards: `c (γ,t) = γ ((1-t)·-)`.  At `t = 0`
this is `γ`, at `t = 1` the constant path at `x₀`, and the constant path is fixed — a contraction
of `Work.StemsB.PathSpace X x₀` onto `constPath X x₀` in the orientation used by
`Work.StemsB.bundlePullback_homotopyEquiv`. -/
def pathReparamRev (X : Type) [TopologicalSpace X] (x₀ : X) :
    C(Work.StemsB.PathSpace X x₀ × unitInterval, Work.StemsB.PathSpace X x₀) where
  toFun q := (Work.StemsB.pathReparam X x₀) (q.1, unitInterval.symm q.2)
  continuous_toFun := (Work.StemsB.pathReparam X x₀).continuous.comp
    (Continuous.prodMk continuous_fst (unitInterval.continuous_symm.comp continuous_snd))

theorem pathReparamRev_apply (X : Type) [TopologicalSpace X] (x₀ : X)
    (γ : Work.StemsB.PathSpace X x₀) (t s : unitInterval) :
    (pathReparamRev X x₀ (γ, t)).1 s = γ.1 (unitInterval.symm t * s) :=
  Work.StemsB.pathReparam_apply X x₀ γ (unitInterval.symm t) s

theorem pathReparamRev_zero (X : Type) [TopologicalSpace X] (x₀ : X) (γ : Work.StemsB.PathSpace X x₀) :
    pathReparamRev X x₀ (γ, 0) = γ := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  rw [pathReparamRev_apply, unitInterval.symm_zero, one_mul]

theorem pathReparamRev_one (X : Type) [TopologicalSpace X] (x₀ : X) (γ : Work.StemsB.PathSpace X x₀) :
    pathReparamRev X x₀ (γ, 1) = Work.StemsB.constPath X x₀ := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  rw [pathReparamRev_apply, unitInterval.symm_one, zero_mul]
  simpa using γ.2

theorem pathReparamRev_const (X : Type) [TopologicalSpace X] (x₀ : X) (t : unitInterval) :
    pathReparamRev X x₀ (Work.StemsB.constPath X x₀, t) = Work.StemsB.constPath X x₀ := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro s
  rw [pathReparamRev_apply]
  rfl

/-- **The homotopy fibre of the path–loop fibration is the loop space.**  The homotopy fibre of
`evalOne : Work.StemsB.PathSpace X x₀ → X` over the constant path consists of the pairs `(γ, β)` of paths with
the same endpoint, and is homotopy equivalent to `Ω X = Path x₀ x₀` by
`Work.StemsB.bundlePullback_homotopyEquiv`, applied to the reversed reparametrisation contraction
`pathReparamRev` of the (contractible) path space. -/
theorem homotopyFibre_evalOne_homotopyEquiv (X : Type) [TopologicalSpace X] (x₀ : X) :
    Nonempty (ContinuousMap.HomotopyEquiv
      (Work.RatHurewicz.homotopyFibre (Work.StemsB.evalOne X x₀)
        (Work.StemsB.constPath X x₀)) (Path x₀ x₀)) :=
  Work.StemsB.bundlePullback_homotopyEquiv X x₀ (Work.StemsB.PathSpace X x₀) (Work.StemsB.evalOne X x₀)
    (Work.StemsB.constPath X x₀) (pathReparamRev X x₀) (pathReparamRev_zero X x₀)
    (pathReparamRev_one X x₀) (pathReparamRev_const X x₀)


/-- **`π₁` of a loop space is abelian.**  `π₁(ΩW) = π₂(W)` via the currying isomorphism
`Work.StemsB.stepMulEquivShifted`, and `π₂` of any space is abelian. -/
theorem mul_comm_pi1_loopSpace (X : Type) [TopologicalSpace X] (x₀ : X) :
    ∀ u v : HomotopyGroup (Fin 1) (Path x₀ x₀) (Path.refl x₀), u * v = v * u := by
  intro u v
  haveI : Nonempty (Fin 1) := ⟨⟨0, by omega⟩⟩
  haveI : Nonempty (Fin 2) := ⟨⟨0, by omega⟩⟩
  have h1 : u * v = (Work.StemsB.stepMulEquivShifted 1 (le_refl 1))
      ((Work.StemsB.stepMulEquivShifted 1 (le_refl 1)).symm u *
        (Work.StemsB.stepMulEquivShifted 1 (le_refl 1)).symm v) := by
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have h2 : v * u = (Work.StemsB.stepMulEquivShifted 1 (le_refl 1))
      ((Work.StemsB.stepMulEquivShifted 1 (le_refl 1)).symm v *
        (Work.StemsB.stepMulEquivShifted 1 (le_refl 1)).symm u) := by
    rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rw [h1, h2, mul_comm]

/-! ## The induction on the torsion degree

The `1`-type case (`a = 0`) is `RangeEMVanOne`; the step `a ↦ a+1` is the path–loop fibration. -/

/-- The base case `a = 0` of the induction is the `1`-type statement `RangeEMVanOne` itself: the
hypotheses `π_i(W) = 0` for `1 ≤ i ≤ N`, `i ≠ 1` split into the torsion of `π_1(W)` and the
vanishing of `π_i(W)` for `2 ≤ i ≤ N`. -/
theorem rangeEMVanAllAux_zero (hOne : RangeEMVanOne) : ∀ N, RangeEMVanAllAux 0 N := by
  intro N W _ w₀ h0 hcomm hzero htors t ht htN
  exact hOne N W w₀ h0 hcomm htors (fun i hi2 hiN => hzero i (by omega) hiN (by omega)) t ht
    (by omega)

/-- **The loop-space step.**  If the range form of the acyclicity of `K(A,a)` holds
(`RangeEMVanAllAux a`), then so does the range form for `K(A,a+1)` — for every range `N`.

Let `W` be connected with `π_i(W) = 0` for `1 ≤ i ≤ N`, `i ≠ a+2`, and `π_{a+2}(W)` torsion.  Its
loop space `ΩW = Path w₀ w₀` has `π_i(ΩW) = π_{i+1}(W)` (`Work.StemsB.stepMulEquivShifted`), i.e.
the shape required by `RangeEMVanAllAux a` with the range `N-1`, so it is rationally acyclic in
degrees `≤ N - 2 - 2a`.  Since the homotopy fibre of the path–loop fibration
`evalOne : PW → W` is homotopy equivalent to `ΩW` (`homotopyFibre_evalOne_homotopyEquiv`, a
homotopy invariant of rational homology and of the `H₀`-condition: `ΩW` is connected because
`π_1(W) = 0`), `SerreE3a` gives an isomorphism `H_t(PW;ℚ) ≅ H_t(W;ℚ)` in degrees
`t < N - 2 - 2a`; the total space `PW` is contractible, so `H_t(W;ℚ) = 0` for `0 < t ≤ N-3-2a`,
which is the claimed range `N - 1 - 2(a+1)`. -/
theorem rangeEMVanAllAux_succ (hE3a : SerreE3a) {a : ℕ} (ih : ∀ N, RangeEMVanAllAux a N) :
    ∀ N, RangeEMVanAllAux (a + 1) N := by
  intro N W _ w₀ h0 hcomm hzero htors t ht htN
  by_cases hvac : N - 1 - 2 * (a + 1) = 0
  · rw [hvac] at htN
    omega
  have hN : 2 * (a + 1) + 2 ≤ N := by omega
  have h1N : 1 ≤ N := by omega
  -- `π₁(W) = 0`, hence the loop space is connected
  have hpi1 : Subsingleton (HomotopyGroup (Fin 1) W w₀) := hzero 1 (le_refl 1) h1N (by omega)
  have hsub0Ω : Subsingleton (HomotopyGroup (Fin 0) (Path w₀ w₀) (Path.refl w₀)) :=
    subsingleton_pi0_loopSpace_of_pi1 w₀ hpi1
  -- the shape of the loop space
  have hzeroΩ : ∀ i : ℕ, 1 ≤ i → i ≤ N - 1 → i ≠ a + 1 →
      Subsingleton (HomotopyGroup (Fin i) (Path w₀ w₀) (Path.refl w₀)) := by
    intro i hi1 hiN hine
    haveI : Nonempty (Fin i) := ⟨⟨0, by omega⟩⟩
    haveI : Nonempty (Fin (i + 1)) := ⟨⟨0, by omega⟩⟩
    have hW : Subsingleton (HomotopyGroup (Fin (i + 1)) W w₀) :=
      hzero (i + 1) (by omega) (by omega) (by omega)
    let e : HomotopyGroup (Fin (i + 1)) W w₀ ≃*
        HomotopyGroup (Fin i) (Path w₀ w₀) (Path.refl w₀) :=
      Work.StemsB.stepMulEquivShifted i hi1
    exact ⟨fun u v => e.symm.injective (hW.elim (e.symm u) (e.symm v))⟩
  have htorsΩ : ∀ α : HomotopyGroup (Fin (a + 1)) (Path w₀ w₀) (Path.refl w₀),
      ∃ K : ℕ, 0 < K ∧ α ^ K = 1 := by
    intro α
    haveI : Nonempty (Fin (a + 1)) := ⟨⟨0, by omega⟩⟩
    haveI : Nonempty (Fin ((a + 1) + 1)) := ⟨⟨0, by omega⟩⟩
    obtain ⟨K, hK, hK1⟩ := htors ((Work.StemsB.stepMulEquivShifted (a + 1) (by omega)).symm α)
    refine ⟨K, hK, ?_⟩
    calc α ^ K = ((Work.StemsB.stepMulEquivShifted (a + 1) (by omega))
            ((Work.StemsB.stepMulEquivShifted (a + 1) (by omega)).symm α)) ^ K := by
          rw [MulEquiv.apply_symm_apply]
      _ = (Work.StemsB.stepMulEquivShifted (a + 1) (by omega))
            (((Work.StemsB.stepMulEquivShifted (a + 1) (by omega)).symm α) ^ K) :=
          (map_pow _ _ K).symm
      _ = 1 := by rw [hK1, map_one]
  -- the loop space is rationally acyclic in the range
  have hAcycΩ : RatAcyclicBelow (Path w₀ w₀) (N - 2 - 2 * a) :=
    ⟨fun s hs hsM => ih (N - 1) (Path w₀ w₀) (Path.refl w₀) hsub0Ω
        (mul_comm_pi1_loopSpace W w₀) hzeroΩ htorsΩ s hs (by omega),
      isIso_ratHomologyMap_toPoint_zero_of_subsingleton_pi0 (Path w₀ w₀) (Path.refl w₀) hsub0Ω⟩
  -- transport to the homotopy fibre of the path–loop fibration
  obtain ⟨e⟩ := homotopyFibre_evalOne_homotopyEquiv W w₀
  have hFib : RatAcyclicBelow (Work.RatHurewicz.homotopyFibre (Work.StemsB.evalOne W w₀)
      (Work.StemsB.constPath W w₀)) (N - 2 - 2 * a) :=
    ratAcyclicBelow_of_homotopyEquiv e hAcycΩ
  have hpc : PathConnectedSpace W := pathConnectedSpace_of_subsingleton_pi0 W w₀ h0
  -- `SerreE3a` on the path–loop fibration
  have hiso := hE3a (Work.StemsB.PathSpace W w₀) W (Work.StemsB.evalOne W w₀)
    (Work.StemsB.constPath W w₀) (N - 2 - 2 * a)
    (Work.StemsB.isSerreFibration_evalOne W w₀) hpc hFib
  haveI : IsIso (ratHomologyMap (Work.StemsB.evalOne W w₀) t) := hiso t (by omega)
  haveI hcontr : ContractibleSpace (Work.StemsB.PathSpace W w₀) :=
    Work.StemsB.contractible_pathSpace W w₀
  have hPS : IsZero (ratH (TopCat.of (Work.StemsB.PathSpace W w₀)) t) :=
    (ratAcyclic_of_contractible (Work.StemsB.PathSpace W w₀)).isZero_ratH ht
  exact IsZero.of_iso hPS (asIso (ratHomologyMap (Work.StemsB.evalOne W w₀) t)).symm

end

end Work.Serre

namespace Work.Serre

noncomputable section

theorem serreRangeEMVanAll (hE3a : Work.Serre.SerreE3a) (hOne : Work.Serre.RangeEMVanOne) :
    Work.Serre.RangeEMVanAll := by
  intro a
  induction a with
  | zero => exact rangeEMVanAllAux_zero hOne
  | succ a ih => exact rangeEMVanAllAux_succ hE3a ih

end

end Work.Serre
