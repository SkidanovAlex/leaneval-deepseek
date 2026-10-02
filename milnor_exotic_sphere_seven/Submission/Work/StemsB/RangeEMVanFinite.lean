import Mathlib
import Submission.Work.Serre.serreRangeEMVanAll
import Submission.Work.Serre.serreE3a
import Submission.Work.RatHurewicz.rangeEMVanOneFinite
import Submission.Work.StemsB.RangeModelPlan
import Submission.Work.StemsB.rangeModel_ratH_iso
import Submission.Work.Serre.serreC0Range
import Submission.Work.StemsB.C3_of_rangeEMVanAll

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The range form of C3 with a **finite** coefficient group, and `C3FiniteTwo` without `SerreC3`

`Work.Serre.RangeEMVanAll` (`Submission/Work/Serre/serreRangeEMVanAll.lean`) is the *range* form of
C3: for `W` connected with `π_i(W) = 0` for `1 ≤ i ≤ N`, `i ≠ a+1`, and `π_{a+1}(W)` a **torsion**
group, one has `H_t(W;ℚ) = 0` for `0 < t ≤ N - 1 - 2a`.  It is proved there from
`Work.Serre.RangeEMVanOne` (the `1`-type case) and `Work.Serre.SerreE3a`.

This file is the same induction with the coefficient hypothesis weakened from *torsion* to
*finite* — which is all that `Work.StemsB.C3FiniteTwo` (finite `A`) needs, and which is supplied by
the transfer/lens-space theorem `Work.Serre.serreC3FiniteOne` (the `1`-type case for finite groups)
rather than by the much larger `Work.Serre.SerreC3` (arbitrary torsion, genuine models):

```
Work.RatHurewicz.RangeEMVanOneFinite                       (finite π₁)
  ⟹ Work.StemsB.RangeEMVanAllAuxFinite a N   (all a, all N)     [this file]
  ⟹ Work.StemsB.C3FiniteTwo
  ⟸ Work.StemsB.C3FiniteTwo_of_serreC3FiniteOne              [this file]
```

The induction step `a ↦ a+1` is *verbatim* the one of `Work.Serre.rangeEMVanAllAux_succ` (the
path–loop fibration `ΩW → PW → W` and `SerreE3a`, which is a **proved** theorem —
`Work.Serre.serreE3a`), the only change being the transport of `Finite (π_{a+2}W)` to
`Finite (π_{a+1}(ΩW))` along the currying equivalence `Work.StemsB.stepMulEquivShifted` in place of
the transport of the torsion predicate.  Consequently `SerreE3a` is not a hypothesis here either.

The bridge `RangeEMVanOneFinite → RangeEMVanOne` (the compactness argument turning *arbitrary
torsion* `π₁` into the finite case, `Submission/Work/RatHurewicz/rangeEMVanOne_of_finite.lean`) is
**not** used: the applications of `C3FiniteTwo` have finite coefficients throughout, and every
group met in the induction is the same group `π_{a+1}(W)`, so finiteness is preserved.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

/-- **The `a`-th level of the range form of C3 with a finite coefficient group.**  `W` connected,
`π_i(W) = 0` for `1 ≤ i ≤ N`, `i ≠ a+1`, and `π_{a+1}(W)` **finite**: then `H_t(W;ℚ) = 0` for
`0 < t ≤ N - 1 - 2a`.  This is `Work.Serre.RangeEMVanAllAux` with `Finite` in place of the torsion
predicate. -/
def RangeEMVanAllAuxFinite (a N : ℕ) : Prop :=
  ∀ (W : Type) [TopologicalSpace W] (w₀ : W),
    Subsingleton (HomotopyGroup (Fin 0) W w₀) →
    (∀ a b : HomotopyGroup (Fin 1) W w₀, a * b = b * a) →
    (∀ i : ℕ, 1 ≤ i → i ≤ N → i ≠ a + 1 → Subsingleton (HomotopyGroup (Fin i) W w₀)) →
    Finite (HomotopyGroup (Fin (a + 1)) W w₀) →
    ∀ t : ℕ, 0 < t → t ≤ N - 1 - 2 * a → IsZero (Work.Serre.ratH (TopCat.of W) t)

/-- The case `a = 0` is `RangeEMVanOneFinite` itself (the hypotheses `π_i(W) = 0` for
`2 ≤ i ≤ N` are the part `i ≠ 1` of the vanishing hypothesis). -/
theorem rangeEMVanAllAuxFinite_zero (hOne : Work.RatHurewicz.RangeEMVanOneFinite) :
    ∀ N, RangeEMVanAllAuxFinite 0 N := by
  intro N W _ w₀ h0 hcomm hzero hfin t ht htN
  exact hOne N W w₀ h0 hcomm hfin (fun i hi2 hiN => hzero i (by omega) hiN (by omega)) t ht
    (by omega)

/-- **The loop-space step, with finite coefficients.**  `Work.Serre.rangeEMVanAllAux_succ` with the
torsion predicate replaced by finiteness; `Work.Serre.serreE3a` (proved) supplies the mapping
theorem. -/
theorem rangeEMVanAllAuxFinite_succ {a : ℕ} (ih : ∀ N, RangeEMVanAllAuxFinite a N) :
    ∀ N, RangeEMVanAllAuxFinite (a + 1) N := by
  intro N W _ w₀ h0 hcomm hzero hfin t ht htN
  by_cases hvac : N - 1 - 2 * (a + 1) = 0
  · rw [hvac] at htN
    omega
  have hN : 2 * (a + 1) + 2 ≤ N := by omega
  have h1N : 1 ≤ N := by omega
  -- `π₁(W) = 0`, hence the loop space is connected
  have hpi1 : Subsingleton (HomotopyGroup (Fin 1) W w₀) := hzero 1 (le_refl 1) h1N (by omega)
  have hsub0Ω : Subsingleton (HomotopyGroup (Fin 0) (Path w₀ w₀) (Path.refl w₀)) :=
    Work.Serre.subsingleton_pi0_loopSpace_of_pi1 w₀ hpi1
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
  -- the coefficient group of the loop space is finite (the loop shift)
  have hfinΩ : Finite (HomotopyGroup (Fin (a + 1)) (Path w₀ w₀) (Path.refl w₀)) := by
    haveI : Nonempty (Fin (a + 1)) := ⟨⟨0, by omega⟩⟩
    haveI : Nonempty (Fin ((a + 1) + 1)) := ⟨⟨0, by omega⟩⟩
    haveI := hfin
    exact Finite.of_surjective (Work.StemsB.stepMulEquivShifted (a + 1) (by omega)).toFun
      (Work.StemsB.stepMulEquivShifted (a + 1) (by omega)).surjective
  -- the loop space is rationally acyclic in the range
  have hAcycΩ : Work.Serre.RatAcyclicBelow (Path w₀ w₀) (N - 2 - 2 * a) :=
    ⟨fun s hs hsM => ih (N - 1) (Path w₀ w₀) (Path.refl w₀) hsub0Ω
        (Work.Serre.mul_comm_pi1_loopSpace W w₀) hzeroΩ hfinΩ s hs (by omega),
      Work.Serre.isIso_ratHomologyMap_toPoint_zero_of_subsingleton_pi0 (Path w₀ w₀) (Path.refl w₀)
        hsub0Ω⟩
  -- transport to the homotopy fibre of the path–loop fibration
  obtain ⟨e⟩ := Work.Serre.homotopyFibre_evalOne_homotopyEquiv W w₀
  have hFib : Work.Serre.RatAcyclicBelow (Work.RatHurewicz.homotopyFibre
      (Work.StemsB.evalOne W w₀) (Work.StemsB.constPath W w₀)) (N - 2 - 2 * a) :=
    Work.Serre.ratAcyclicBelow_of_homotopyEquiv e hAcycΩ
  have hpc : PathConnectedSpace W := Work.Serre.pathConnectedSpace_of_subsingleton_pi0 W w₀ h0
  -- `SerreE3a` on the path–loop fibration (a proved theorem, not a hypothesis)
  have hiso := Work.Serre.serreE3a (Work.StemsB.PathSpace W w₀) W (Work.StemsB.evalOne W w₀)
    (Work.StemsB.constPath W w₀) (N - 2 - 2 * a)
    (Work.StemsB.isSerreFibration_evalOne W w₀) hpc hFib
  haveI : IsIso (Work.Serre.ratHomologyMap (Work.StemsB.evalOne W w₀) t) := hiso t (by omega)
  haveI hcontr : ContractibleSpace (Work.StemsB.PathSpace W w₀) :=
    Work.StemsB.contractible_pathSpace W w₀
  have hPS : IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.PathSpace W w₀)) t) :=
    (Work.Serre.ratAcyclic_of_contractible (Work.StemsB.PathSpace W w₀)).isZero_ratH ht
  exact IsZero.of_iso hPS (asIso (Work.Serre.ratHomologyMap (Work.StemsB.evalOne W w₀) t)).symm

/-- **The range form of C3 for finite coefficient groups, in all degrees** (by induction on `a`). -/
theorem rangeEMVanAllFinite (hOne : Work.RatHurewicz.RangeEMVanOneFinite) :
    ∀ a N, RangeEMVanAllAuxFinite a N := by
  intro a
  induction a with
  | zero => exact rangeEMVanAllAuxFinite_zero hOne
  | succ a ih => exact rangeEMVanAllAuxFinite_succ ih

/-! ## `C3FiniteTwo` from the finite range statement

The same argument as `Work.StemsB.C3FiniteTwo_of_rangeEMVanAll`, with the *finite* range statement
in place of `Work.Serre.RangeEMVanAll`. -/

/-- **`C3FiniteTwo` from the range form of C3 with finite coefficients.** -/
theorem C3FiniteTwo_of_rangeEMVanAllFinite (hOne : Work.RatHurewicz.RangeEMVanOneFinite) :
    C3FiniteTwo := by
  intro A _ hfA k hk N X _ pt hX i hi1 hiN
  have hidx : (k - 1) + 1 = k := by omega
  -- a range model of `K(A,k)` with the large top `N + 2k`
  obtain ⟨P, tP, p₀, hP⟩ := Work.Serre.serreC0Range A k (N + 2 * k) (by omega) (by omega)
  letI : TopologicalSpace P := tP
  -- the same hypothesis, read at the index `(k-1)+1`
  have hPa : Work.Serre.IsEMSpaceUpTo A ((k - 1) + 1) (by omega) (N + 2 * k) P p₀ := by
    convert hP using 1
  -- the coefficient group at `a = k-1` is finite (it is `A`, transported along the model)
  have hfinP : Finite (HomotopyGroup (Fin ((k - 1) + 1)) P p₀) := by
    obtain ⟨e⟩ := hPa.1
    haveI : Fintype A := Fintype.ofFinite A
    haveI : Finite (Multiplicative A) := inferInstance
    exact Finite.of_surjective e.symm.toFun e.symm.surjective
  -- the range statement at `a = k-1`, `N = N + 2k`
  have hvan : IsZero (Work.Serre.ratH (TopCat.of P) i) :=
    rangeEMVanAllFinite hOne (k - 1) (N + 2 * k) P p₀
      (hPa.2 0 (by omega) (Or.inl (by omega)))
      (by
        intro a b
        haveI : Subsingleton (HomotopyGroup (Fin 1) P p₀) :=
          hPa.2 1 (by omega) (Or.inl (by omega))
        exact Subsingleton.elim (a * b) (b * a))
      (fun j hj1 hjN hjne => hPa.2 j hjne (Or.inr hjN))
      hfinP i hi1 (by omega)
  -- the vanishing of the large model transfers to the given range model
  have hPQ : Work.Serre.IsEMSpaceUpTo A k (by omega) N P p₀ :=
    ⟨hP.1, fun j hj hc => hP.2 j hj (hc.imp id (fun h => by omega))⟩
  obtain ⟨e⟩ := rangeModel_ratH_iso A k N hk X pt hX P p₀ hPQ i hiN
  exact IsZero.of_iso hvan e

/-- **`C3FiniteTwo` from C3 at `n = 1` for finite coefficient groups** — the transfer/lens-space
statement `Work.Serre.serreC3FiniteOne`.  This is the sharpest form of the C3 input of the
contract: it needs neither the unbounded model-existence contract `SerreC0`, nor the arbitrary
torsion case `SerreC3`, nor the mapping theorem `SerreE3a` (all of which are either unprovable in
the tree or proved). -/
theorem C3FiniteTwo_of_serreC3FiniteOne
    (hC3One : ∀ (A : Type) [AddCommGroup A] [Fintype A] (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpace A 1 (by norm_num) X pt → Work.Serre.RatAcyclic X) :
    C3FiniteTwo :=
  C3FiniteTwo_of_rangeEMVanAllFinite
    (Work.RatHurewicz.rangeEMVanOneFinite_of_C3FiniteOne hC3One)

/-- **`C3FiniteTwo` from SERRE's `SerreC3`** (the mapping theorem `SerreE3a` is a proved theorem,
so it does not appear). -/
theorem C3FiniteTwo_of_SerreC3 (hC3 : Work.Serre.SerreC3) : C3FiniteTwo :=
  C3FiniteTwo_of_serre Work.Serre.serreE3a hC3

end

end Work.StemsB
