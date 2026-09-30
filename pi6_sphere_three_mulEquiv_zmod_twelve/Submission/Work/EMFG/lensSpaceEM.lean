import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.RatHurewicz.LensSpace.Basic
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.Serre.C1SphOne

/-!
# EMFG — the lens space `S^{2N+3}/μₙ` is a range model of `K(ZMod n, 1)`

`Work.EMFG.isEMSpaceUpTo_lensSpace`: `L = S^{2N+3}/μₙ` (`Work.RatHurewicz.lensSpace n N`) is a model
of `K(ZMod n,1)` through degree `2N`.

This is the range-model statement that the torsion case of `Work.EMFG.EMOne` needs.  It is proved
here (independently of `Submission/Work/RatHurewicz/LensSpace/EM.lean`, which is not reachable from
this area because of an unrelated failing module in its import closure) from:

* `Work.RatHurewicz.isCoveringMap_lensProj` — the quotient map `S^{2N+3} → L` is an `n`-sheeted
  covering;
* the long exact homotopy sequence of that covering (`Work.StemsB.FibrationLES`), which identifies
  `π₁(L)` with the deck group `ZMod n` (the total space is simply connected) and gives
  `π_i(L) = π_i(S^{2N+3}) = 0` for `2 ≤ i ≤ 2N`;
* `Work.RatHurewicz.lensSpacePathConnected` for `π₀`.
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.EMFG

noncomputable section

/-- **`π_{m+2}` of the base of a covering vanishes** if `π_{m+2}` of the total space and `π_{m+1}`
of the fibre do (exactness of the long exact homotopy sequence at `π_{m+2}` of the base). -/
theorem subsingleton_homotopyGroup_base_of_isCoveringMap {E X : Type} [TopologicalSpace E]
    [TopologicalSpace X] (p : C(E, X)) (hp : IsCoveringMap p) (e₀ : E) (m : ℕ)
    (hE : Subsingleton (HomotopyGroup (Fin (m + 2)) E e₀))
    (hF : Subsingleton (HomotopyGroup (Fin (m + 1)) (Work.StemsB.fibre p (p e₀))
      (Work.StemsB.fibrePoint p e₀))) :
    Subsingleton (HomotopyGroup (Fin (m + 2)) X (p e₀)) := by
  haveI := hE
  haveI := hF
  have hserre : Work.StemsB.IsSerreFibration p :=
    Work.StemsB.isSerreFibration_of_isCoveringMap p hp
  have hles : Work.StemsB.FibrationLES p e₀ :=
    Work.StemsB.fibrationLES_of_isSerreFibration p hserre e₀
  obtain ⟨d, -, hex, -⟩ := hles m
  have key : ∀ y : HomotopyGroup (Fin (m + 2)) X (p e₀), y = 1 := by
    intro y
    have hdy : d y = 1 := Subsingleton.elim _ _
    obtain ⟨z, hz⟩ := (hex y).mp hdy
    rw [← hz]
    exact (congrArg (Work.StemsB.πmap p (m + 1) e₀) (Subsingleton.elim z 1)).trans
      (map_one (Work.StemsB.πmap p (m + 1) e₀))
  exact ⟨fun a b => by rw [key a, key b]⟩

/-- **`π₁(L) ≅ ZMod n`** for the lens space, from the simply connected covering. -/
theorem pi_one_lensSpace (n N : ℕ) [NeZero n] (e₀ : Work.RatHurewicz.lensTotal N) :
    Nonempty (HomotopyGroup (Fin 1) (Work.RatHurewicz.lensSpace n N)
      (Work.RatHurewicz.lensProj n N e₀) ≃* Multiplicative (ZMod n)) :=
  ⟨(HomotopyGroup.pi1MulEquivFundamentalGroup.trans
    ((Work.RatHurewicz.isQuotientCoveringMap_lensProj n N).fundamentalGroupEquiv
      (x := Work.RatHurewicz.lensProj n N e₀) ⟨e₀, rfl⟩)).trans
    (Work.Serre.mulOppositeMulEquivComm (Multiplicative (ZMod n)))⟩

/-- **`π_i(L) = 0` for `2 ≤ i ≤ 2N`.** -/
theorem subsingleton_pi_lensSpace (n N : ℕ) [NeZero n] (e₀ : Work.RatHurewicz.lensTotal N) :
    ∀ i : ℕ, 2 ≤ i → i ≤ 2 * N →
      Subsingleton (HomotopyGroup (Fin i) (Work.RatHurewicz.lensSpace n N)
        (Work.RatHurewicz.lensProj n N e₀)) := by
  intro i hi hiN
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
  haveI hdisc : DiscreteTopology (Work.StemsB.fibre (Work.RatHurewicz.lensProj n N)
      (Work.RatHurewicz.lensProj n N e₀)) :=
    ((Work.RatHurewicz.isCoveringMap_lensProj n N)
      (Work.RatHurewicz.lensProj n N e₀)).discreteTopology_fiber
  refine subsingleton_homotopyGroup_base_of_isCoveringMap (Work.RatHurewicz.lensProj n N)
    (Work.RatHurewicz.isCoveringMap_lensProj n N) e₀ m ?_ ?_
  · exact Work.Stems.sphereConnectivity (2 * N + 3) (m + 2) (by omega) e₀
  · exact Work.Serre.subsingleton_homotopyGroup_of_discrete (m + 1) (by omega) _ _

/-- `π₀(L) = 0`, i.e. the lens space is path connected. -/
theorem subsingleton_pi_zero_lensSpace (n N : ℕ) [NeZero n]
    (l₀ : Work.RatHurewicz.lensSpace n N) :
    Subsingleton (HomotopyGroup (Fin 0) (Work.RatHurewicz.lensSpace n N) l₀) := by
  have hZ : Subsingleton (ZerothHomotopy (Work.RatHurewicz.lensSpace n N)) :=
    (pathConnectedSpace_iff_zerothHomotopy.mp (Work.RatHurewicz.lensSpacePathConnected n N)).2
  exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy
    (X := Work.RatHurewicz.lensSpace n N) (x := l₀)).injective (Subsingleton.elim _ _)⟩

/-- **The lens space is a model of `K(ZMod n, 1)` through degree `2N`.** -/
theorem isEMSpaceUpTo_lensSpace (n N : ℕ) [NeZero n] (e₀ : Work.RatHurewicz.lensTotal N) :
    Work.Serre.IsEMSpaceUpTo (ZMod n) 1 (by norm_num) (2 * N) (Work.RatHurewicz.lensSpace n N)
      (Work.RatHurewicz.lensProj n N e₀) := by
  constructor
  · exact pi_one_lensSpace n N e₀
  · intro i hi hc
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      exact subsingleton_pi_zero_lensSpace n N (Work.RatHurewicz.lensProj n N e₀)
    · rcases hc with hlt | hle
      · omega
      · exact subsingleton_pi_lensSpace n N e₀ i (by omega) hle

end

end Work.EMFG
