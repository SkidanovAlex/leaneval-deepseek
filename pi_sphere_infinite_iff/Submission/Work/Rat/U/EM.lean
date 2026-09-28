import Mathlib
import Submission.Work.RatHurewicz.LensSpace.Basic
import Submission.Work.Stems.sphereConnectivity
import Submission.Work.StemsB.SphLoopTools
import Submission.Work.Cohomology.sphereVanishing
import Submission.Work.RatHurewicz.coverRangeTransfer
import Submission.Work.RatHurewicz.ConnectivityBridge

/-!
# `L = S^{2N+3}/μₙ` is a range model of `K(ZMod n,1)` and is rationally acyclic in range

The covering `S^{2N+3} → L` has `n` sheets, so the transfer
(`Work.RatHurewicz.isZero_ratH_of_finite_covering_range`) proves that `H_t(L;ℚ) = 0` for
`0 < t ≤ 2N`, and the long exact homotopy sequence of the covering together with the connectivity
of the sphere proves that `L` is a model of `K(ZMod n,1)` in degrees `≤ 2N`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.RatHurewicz

noncomputable section

/-- The rational homology of `Sᵏ` vanishes away from the degrees `0` and `k`. -/
theorem isZero_ratH_sph_bottom {k j : ℕ} (hk : 1 ≤ k) (hj0 : j ≠ 0) (hjk : j ≠ k) :
    IsZero (Work.Serre.ratH (TopCat.of (Work.Serre.Sph k)) j) :=
  Work.StemsB.isZero_homology_rat_of_isZero_homology_int (TopCat.of (Work.Serre.Sph k)) j
    (Work.Cohomology.sphereVanishing k j hk hj0 hjk)

/-! ## The long exact homotopy sequence: `π_i` of the base of a covering -/

/-- **`π_{m+2}` of the base of a covering map is trivial** if `π_{m+2}` of the total space and
`π_{m+1}` of the fibre are trivial.  This is exactness of the long exact homotopy sequence of the
covering (a Serre fibration) at `π_{m+2}` of the base, the connecting map landing in the trivial
group `π_{m+1}` of the fibre. -/
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

/-! ## The homotopy groups of the lens space -/

/-- The canonical isomorphism `Gᵐᵒᵖ ≃* G` for a commutative group `G`. -/
def mulOppositeCommMulEquiv (G : Type*) [CommGroup G] : Gᵐᵒᵖ ≃* G where
  toFun x := MulOpposite.unop x
  invFun x := MulOpposite.op x
  left_inv x := rfl
  right_inv x := rfl
  map_mul' x y := by simp [MulOpposite.unop_mul, mul_comm]

/-- **`π₁(L) ≅ ZMod n`**: the total space of the covering is simply connected, so the fundamental
group of the base is the group of the covering, `ZMod n` (up to the opposite group, which is the
same in a commutative group). -/
theorem pi_one_lensSpace (n N : ℕ) [NeZero n] (e₀ : lensTotal N) :
    Nonempty (HomotopyGroup (Fin 1) (lensSpace n N) (lensProj n N e₀)
      ≃* Multiplicative (ZMod n)) :=
  ⟨(HomotopyGroup.pi1MulEquivFundamentalGroup.trans
    ((isQuotientCoveringMap_lensProj n N).fundamentalGroupEquiv
      (x := lensProj n N e₀) ⟨e₀, rfl⟩)).trans
    (mulOppositeCommMulEquiv (Multiplicative (ZMod n)))⟩

/-- **`π_i(L) = 0` for `2 ≤ i ≤ 2N`**: it is the `i`-th homotopy group of the simply connected
covering `S^{2N+3}`, and `π_i(S^{2N+3}) = 0` for `i ≤ 2N`. -/
theorem subsingleton_pi_lensSpace (n N : ℕ) [NeZero n] (e₀ : lensTotal N) :
    ∀ i : ℕ, 2 ≤ i → i ≤ 2 * N →
      Subsingleton (HomotopyGroup (Fin i) (lensSpace n N) (lensProj n N e₀)) := by
  intro i hi hiN
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 2 := ⟨i - 2, by omega⟩
  haveI hdisc : DiscreteTopology
      (Work.StemsB.fibre (lensProj n N) (lensProj n N e₀)) :=
    ((isCoveringMap_lensProj n N) (lensProj n N e₀)).discreteTopology_fiber
  refine subsingleton_homotopyGroup_base_of_isCoveringMap (lensProj n N)
    (isCoveringMap_lensProj n N) e₀ m ?_ ?_
  · exact Work.Stems.sphereConnectivity (2 * N + 3) (m + 2) (by omega) e₀
  · exact Work.Serre.subsingleton_homotopyGroup_of_discrete (m + 1) (by omega) _ _

/-- **`π₀(L) = 0`**, i.e. `L` is path connected. -/
theorem subsingleton_pi_zero_lensSpace (n N : ℕ) [NeZero n] (l₀ : lensSpace n N) :
    Subsingleton (HomotopyGroup (Fin 0) (lensSpace n N) l₀) := by
  have hZ : Subsingleton (ZerothHomotopy (lensSpace n N)) :=
    (pathConnectedSpace_iff_zerothHomotopy.mp (lensSpacePathConnected n N)).2
  exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy
    (X := lensSpace n N) (x := l₀)).injective (Subsingleton.elim _ _)⟩

/-- **`L` is a model of `K(ZMod n,1)` up to degree `2N`.** -/
theorem isEMSpaceUpTo_lensSpace (n N : ℕ) [NeZero n] (e₀ : lensTotal N) :
    Work.Serre.IsEMSpaceUpTo (ZMod n) 1 (by norm_num : 0 < 1) (2 * N) (lensSpace n N)
      (lensProj n N e₀) := by
  constructor
  · exact pi_one_lensSpace n N e₀
  · intro i hi hc
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      exact subsingleton_pi_zero_lensSpace n N (lensProj n N e₀)
    · rcases hc with hlt | hle
      · omega
      · exact subsingleton_pi_lensSpace n N e₀ i (by omega) hle

/-! ## Rational acyclicity in the range -/

/-- **`H_t(L;ℚ) = 0` for `0 < t ≤ 2N`**, by the transfer of the `n`-sheeted covering
`S^{2N+3} → L`: the total space has no rational homology below degree `2N+3`. -/
theorem isZero_ratH_lensSpace (n N : ℕ) [NeZero n] :
    ∀ t : ℕ, 0 < t → t ≤ 2 * N →
      IsZero (Work.Serre.ratH (TopCat.of (lensSpace n N)) t) := by
  refine isZero_ratH_of_finite_covering_range (lensProj n N) (isCoveringMap_lensProj n N)
    n (NeZero.pos n) (card_lensFibre n N) (2 * N) ?_
  intro t ht htN
  exact isZero_ratH_sph_bottom (k := 2 * N + 3) (j := t) (by omega) (by omega) (by omega)

end

end Work.RatHurewicz
