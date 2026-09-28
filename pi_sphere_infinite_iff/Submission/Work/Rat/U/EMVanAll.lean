import Mathlib
import Submission.Work.Serre.RangeEMVanFinDefs
import Submission.Work.Serre.serreRangeEMVanAll
import Submission.Work.Rat.U.EMVanOne
import Submission.Work.StemsB.homotopyGroup_loopSpace
import Submission.Work.StemsB.LoopShiftShifted

/-!
# `RangeEMVanAllFin` — the finite-coefficient range form of C3, in all degrees

`Work.Serre.RangeEMVanAllFin` (`RangeEMVanFinDefs.lean`) is the all-degrees range form of the
acyclicity of a `K(A,·)` model in a range, with the coefficient group `A = π_{a+1}(W)` assumed
**finite**.  The proof is the loop-space induction of `Work.Serre.serreRangeEMVanAll` with the
finiteness hypothesis in place of the torsion one: the path–loop fibration `ΩW → PW → W` has
`π_i(ΩW) = π_{i+1}(W)` through `Work.StemsB.stepMulEquivShifted`, so the *same* group
`π_{a+2}(W) ≅ π_{a+1}(ΩW)` carries the hypothesis at the next stage, and finiteness transports
along that isomorphism (`Fintype.ofEquiv`).

Together with `Work.Serre.serreRangeEMVanOneFin` this gives the range form of C3 for finite groups
**unconditionally**, from `SerreC0`, `SerreC3Finite` and `SerreE3a` (see
`serreRangeEMVanAllFin_unconditional`).
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology unitInterval

namespace Work.Serre

noncomputable section

/-- The base case `a = 0` of the finite-coefficient induction is `RangeEMVanOneFin` itself. -/
theorem rangeEMVanAllAuxFin_zero (hOne : RangeEMVanOneFin) : ∀ N, RangeEMVanAllAuxFin 0 N := by
  intro N W _ w₀ h0 hcomm hzero hfin t ht htN
  exact hOne N W w₀ h0 hcomm hfin (fun i hi2 hiN => hzero i (by omega) hiN (by omega)) t ht
    (by omega)

/-- **The loop-space step** (finite coefficients).  If the range form of the acyclicity of
`K(A,a)` holds with a finite `A` (`RangeEMVanAllAuxFin a`), then so does the form for `K(A,a+1)` —
the hypothesis `π_{a+2}(W)` finite transports to `π_{a+1}(ΩW)` along
`Work.StemsB.stepMulEquivShifted`. -/
theorem rangeEMVanAllAuxFin_succ (hE3a : SerreE3a) {a : ℕ}
    (ih : ∀ N, RangeEMVanAllAuxFin a N) : ∀ N, RangeEMVanAllAuxFin (a + 1) N := by
  intro N W _ w₀ h0 hcomm hzero hfin t ht htN
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
  -- the finiteness hypothesis transports to the loop space
  have hfinΩ : Nonempty (Fintype (HomotopyGroup (Fin (a + 1)) (Path w₀ w₀) (Path.refl w₀))) := by
    haveI : Nonempty (Fin (a + 1)) := ⟨⟨0, by omega⟩⟩
    haveI : Nonempty (Fin ((a + 1) + 1)) := ⟨⟨0, by omega⟩⟩
    haveI := hfin.some
    let e : HomotopyGroup (Fin ((a + 1) + 1)) W w₀ ≃*
        HomotopyGroup (Fin (a + 1)) (Path w₀ w₀) (Path.refl w₀) :=
      Work.StemsB.stepMulEquivShifted (a + 1) (by omega)
    exact ⟨Fintype.ofEquiv _ e.toEquiv⟩
  -- the loop space is rationally acyclic in the range
  have hAcycΩ : RatAcyclicBelow (Path w₀ w₀) (N - 2 - 2 * a) :=
    ⟨fun s hs hsM => ih (N - 1) (Path w₀ w₀) (Path.refl w₀) hsub0Ω
        (mul_comm_pi1_loopSpace W w₀) hzeroΩ hfinΩ s hs (by omega),
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

/-- **The finite-coefficient range form of C3, all degrees**, from the `1`-type case. -/
theorem serreRangeEMVanAllFin (hE3a : Work.Serre.SerreE3a) (hOne : Work.Serre.RangeEMVanOneFin) :
    Work.Serre.RangeEMVanAllFin := by
  intro a
  induction a with
  | zero => exact rangeEMVanAllAuxFin_zero hOne
  | succ a ih => exact rangeEMVanAllAuxFin_succ hE3a ih

/-- **C3 for finite groups, in range form, unconditionally**: from `SerreC0`, the proved
`SerreC3Finite` and `SerreE3a`.  (The general-torsion `RangeEMVanAll`/`SerreC3` additionally needs
the arbitrary-torsion case — see `README.md` §5.2.) -/
theorem serreRangeEMVanAllFin_unconditional (hC0 : Work.Serre.SerreC0)
    (hC3 : Work.Serre.SerreC3Finite) (hE3a : Work.Serre.SerreE3a) :
    Work.Serre.RangeEMVanAllFin :=
  serreRangeEMVanAllFin hE3a (serreRangeEMVanOneFin hC0 hC3)

end

end Work.Serre
