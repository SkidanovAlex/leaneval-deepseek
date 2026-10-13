/-
  annals_wilkies_conjecture, AREA E3K (`Submission.Work.WilE3K`): the **base case** of the ET
  induction (`Work.WilE3K.ETB` at `rt = 0`).

  An `ETData N 0 n re` has no arctan equations at all, so its `Nondegen` condition is purely
  exp-affine: the `n = N + 1` equations `G i = 0` with the Jacobian determinant nonzero.  Up to the
  change of index `Fin n ≃ Fin (N+1)` (which exists because `E.h : 0 + n = N + 1`), it *is* an
  EA chain system in the sense of `WilkiesDesign.E`:

  * `ETData.baseEquiv E : Fin (N+1) ≃ Fin n` identifies the ambient coordinates with the free
    coordinates of `E` (`E.freeCoord` in one direction, `E.freeIndex` in the other);
  * `ETData.baseChain E : EAChain (N+1) re` has the chain coefficients `(j, i) ↦ E.dcoef i j`, so
    that the symbolic derivative `E.dPoly` of `ET.lean` is *definitionally* `eaD (baseChain E)`
    (`baseChain_dPoly`), and the exponential part `E.ellChain` is `EAChain.ell` (`baseChain_ell`);
  * `ETData.baseFun E i = E.G (E.freeIndex i _)` is the corresponding list of EA polynomials.

  Hence the ex-exp-affine Khovanskii bound `hq` applies verbatim, and `ETB q 0 N D = q.eval D` by
  definition, which is the statement of `ET_base`.
-/
import Mathlib
import Submission.Work.WilE3K.ET
import Submission.Work.WilE3K.Elim
import Submission.Work.Wilkies.E.Spec

noncomputable section
open Classical Topology Filter
namespace Work.WilE3K
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

namespace ETData

variable {N n re : ℕ}

/-! ## §1. The index change `Fin n ≃ Fin (N+1)` and the associated EA chain -/

/-- The ambient coordinates of an `ETData N 0 n re` are the free coordinates of `E`: the
map `freeIndex` is a bijection because `E.h : 0 + n = N + 1`. -/
def baseEquiv (E : ETData N 0 n re) : Fin (N + 1) ≃ Fin n where
  toFun i := E.freeIndex i (Nat.zero_le _)
  invFun j := E.freeCoord j
  left_inv i := E.freeCoord_freeIndex i _
  right_inv j := E.freeIndex_freeCoord j _

@[simp] theorem baseEquiv_apply (E : ETData N 0 n re) (i : Fin (N + 1)) :
    baseEquiv E i = E.freeIndex i (Nat.zero_le _) := rfl

/-- **The EA chain of a system with no arctan equation.**  Its coefficients are the symbolic
derivatives `E.dcoef` of `ET.lean`, which makes `eaD` definitionally equal to `E.dPoly`. -/
def baseChain (E : ETData N 0 n re) : EAChain (N + 1) re :=
  ⟨fun j i => E.dcoef i j, E.cb⟩

/-- The EA polynomials of the equations of `E`, indexed by the ambient coordinates. -/
def baseFun (E : ETData N 0 n re) : Fin (N + 1) → EAPoly (N + 1) re :=
  fun i => E.G (E.freeIndex i (Nat.zero_le _))

theorem baseFun_eq (E : ETData N 0 n re) (i : Fin (N + 1)) (h : 0 ≤ (i : ℕ)) :
    baseFun E i = E.G (E.freeIndex i h) := by
  simp only [baseFun]

theorem dcoef_eq (E : ETData N 0 n re) (i : Fin (N + 1)) (j : Fin re) :
    E.dcoef i j = E.ca j (baseEquiv E i) := by
  simp only [dcoef, baseEquiv, Equiv.coe_fn_mk, dite_eq_left (Nat.zero_le _)]

/-! ## §2. The chain of the lifted system is the chain of `E` -/

/-- The exponential part: `E.ellChain` is the affine form of the EA chain `baseChain E`. -/
theorem sum_ca_eq (E : ETData N 0 n re) (j : Fin re) (y : Fin (N + 1) → ℝ) :
    (∑ i : Fin (N + 1), E.dcoef i j * y i) = ∑ i : Fin n, E.ca j i * y (E.freeCoord i) := by
  refine Fintype.sum_equiv (baseEquiv E) (fun i : Fin (N + 1) => E.dcoef i j * y i)
    (fun i : Fin n => E.ca j i * y (E.freeCoord i)) (fun i => ?_)
  rw [dcoef_eq E i j, baseEquiv_apply E i, E.freeCoord_freeIndex]

theorem baseChain_ell (E : ETData N 0 n re) (j : Fin re) (x : Fin (N + 1) → ℝ) :
    E.ellChain j x = (baseChain E).ell j x := by
  simp only [ellChain, EAChain.ell, baseChain]
  congr 1
  exact (sum_ca_eq E j x).symm

/-- The symbolic derivative `E.dPoly` is `eaD` along the chain `baseChain E` -- definitionally. -/
theorem baseChain_dPoly (E : ETData N 0 n re) (i : Fin (N + 1)) (Q : EAPoly (N + 1) re) :
    E.dPoly i Q = eaD (baseChain E) i Q := by
  simp only [dPoly, eaD, baseChain]

/-- Evaluation of an EA polynomial is the same on both sides of the index change. -/
theorem baseChain_evalPoly (E : ETData N 0 n re) (Q : EAPoly (N + 1) re) (x : Fin (N + 1) → ℝ) :
    E.evalPoly Q x = eaEval (baseChain E) Q x := by
  simp only [evalPoly, eaEval]
  have h : (Sum.elim x fun j => Real.exp (E.ellChain j x)) =
      (Sum.elim x fun j => Real.exp ((baseChain E).ell j x)) := by
    funext k
    rcases k with a | b
    · rfl
    · simp only [Sum.elim_inr]
      rw [baseChain_ell]
  rw [h]

/-! ## §3. `Nondegen` is the nondegeneracy of the EA chain system -/

/-- The Jacobian of the lifted system (no arctan rows) is the Jacobian of the EA chain system. -/
theorem jac_eq (E : ETData N 0 n re) (z : Fin (N + 1) → ℝ) :
    E.jac z =
      Matrix.of fun i j => eaEval (baseChain E) (eaD (baseChain E) j (baseFun E i)) z := by
  ext i j
  rw [jac, Matrix.of_apply, Matrix.of_apply, dite_eq_right (show ¬ (i : ℕ) < 0 by omega)]
  rw [baseFun_eq E i (Nat.zero_le _), baseChain_evalPoly, baseChain_dPoly]

/-- **`E.Nondegen` is the `hq`-hypothesis of the EA chain system `baseChain E`.** -/
theorem base_nondeg (E : ETData N 0 n re) (z : Fin (N + 1) → ℝ) (hz : E.Nondegen z) :
    (∀ i : Fin (N + 1), eaEval (baseChain E) (baseFun E i) z = 0) ∧
    (Matrix.of fun i j => eaEval (baseChain E) (eaD (baseChain E) j (baseFun E i)) z).det ≠ 0 := by
  constructor
  · intro i
    rw [← baseChain_evalPoly]
    exact hz.1 (baseEquiv E i)
  · rw [← jac_eq E z]
    exact hz.2.2

end ETData

/-! ## §4. The base case of the ET induction -/

theorem ET_base (q : Polynomial ℕ) (M : ℕ)
    (hq : ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r) (f : Fin k → WilkiesDesign.E.EAPoly k r)
      (s : Finset (Fin k → ℝ)), k + r ≤ M →
      (∀ x ∈ s, (∀ i, WilkiesDesign.E.eaEval c (f i) x = 0) ∧
        (Matrix.of fun i j => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c j (f i)) x).det ≠ 0) →
      s.card ≤ q.eval (∑ i, WilkiesDesign.E.atomDeg (f i)))
    (N n re : ℕ) (E : Work.WilE3K.ETData N 0 n re) (s : Finset (Fin (N + 1) → ℝ))
    (hs : ∀ z ∈ s, E.Nondegen z) (hM : N + 1 + re ≤ M) :
    s.card ≤ Work.WilE3K.ETB q 0 N (∑ i, WilkiesDesign.E.atomDeg (E.G i) + 0) := by
  -- the degree sum is the same after the index change `Fin n ≃ Fin (N+1)`
  have hsum : (∑ i : Fin (N + 1), atomDeg (ETData.baseFun E i)) = ∑ i : Fin n, atomDeg (E.G i) := by
    refine Fintype.sum_equiv (ETData.baseEquiv E) (fun i => atomDeg (ETData.baseFun E i))
      (fun i => atomDeg (E.G i)) (fun i => ?_)
    rfl
  -- the frozen exp-affine Khovanskii bound applies to the associated EA chain system
  have hb := hq (N + 1) re (ETData.baseChain E) (ETData.baseFun E) s hM
    (fun z hz => ETData.base_nondeg E z (hs z hz))
  rw [hsum] at hb
  rw [show ETB q 0 N (∑ i, atomDeg (E.G i) + 0) = q.eval (∑ i, atomDeg (E.G i) + 0) from rfl]
  simpa using hb

end Work.WilE3K
