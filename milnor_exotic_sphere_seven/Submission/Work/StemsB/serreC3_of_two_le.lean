import Mathlib
import Submission.Work.RatHurewicz.rangeModelRatAcyclic
import Submission.Work.Serre.Models

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# C3 for finite `A` and `n ≥ 2`, from the torsion case of Serre's theorem

`Work.StemsB.serreC3_of_two_le`: the interface `C3Finite` of
`Submission/Work/StemsB/RangeModelPlan.lean` (`n ≥ 2`, finite abelian coefficients) follows from the
*contract* `Work.RatHurewicz.TorsionHomotopyVanishing`
(`Submission/Work/RatHurewicz/rangeModelRatAcyclic.lean`), i.e. from Serre's theorem in the torsion
case ("homotopy in 𝒞 ⟹ homology in 𝒞").

The mathematical content is a one-line observation: **a model `X` of `K(A,n)` with `A` finite has
*all* of its homotopy groups torsion.**  Indeed `π_i(X) = 0` for `i ≠ n` (in particular `π_0 = π_1
= 0`), while `π_n(X) ≃ A` is finite, hence torsion.  So the hypothesis of
`TorsionHomotopyVanishing` is available in *every* range `N`, giving `H_j(X;ℚ) = 0` for all `0 < j`;
in degree `0` the class is `H_0(X;ℚ) ≅ ℚ` because `X` is path connected.  That is exactly
`RatAcyclic X`.

The only non-trivial point of the formalisation is that `π_n(X) ≅ A` is an isomorphism of *types*
for the purposes of finiteness (`Finite` transports along the underlying equivalence), which avoids
having to compare the (proof-irrelevant) `Nonempty (Fin n)` instances that carry the group
structures on `HomotopyGroup (Fin n)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.StemsB

noncomputable section

/-- A finite group is a torsion group (`g ^ Nat.card G = 1`). -/
theorem serreC3Aux_isTorsionGroup_of_finite {G : Type*} [Group G] [Finite G] :
    Work.RatHurewicz.IsTorsionGroup G :=
  fun g => ⟨Nat.card G, Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩, pow_card_eq_one' (x := g)⟩

/-- A subsingleton group is a torsion group. -/
theorem serreC3Aux_isTorsionGroup_of_subsingleton {G : Type*} [Group G] (h : Subsingleton G) :
    Work.RatHurewicz.IsTorsionGroup G :=
  fun g => ⟨1, by norm_num, Subsingleton.elim _ _⟩

/-- In `ModuleCat ℚ`, a morphism between subsingleton modules is an isomorphism (both are then
nonempty subsingletons, so the map is bijective). -/
theorem serreC3Aux_isIso_of_subsingleton_module {M N : ModuleCat ℚ} (hM : Subsingleton (↥M))
    (hN : Subsingleton (↥N)) (f : M ⟶ N) : IsIso f := by
  haveI := hM
  haveI := hN
  refine IsIso.mk ⟨(0 : N ⟶ M), ?_, ?_⟩
  · apply ModuleCat.hom_ext
    ext x
    exact Subsingleton.elim _ _
  · apply ModuleCat.hom_ext
    ext y
    exact Subsingleton.elim _ _

/-- **C3 for finite `A` in degrees `n ≥ 2`.**  Every model of `K(A,n)`, `A` finite abelian,
`n ≥ 2`, is rationally acyclic, given the torsion case of Serre's theorem. -/
theorem serreC3_of_two_le (hTV : Work.RatHurewicz.TorsionHomotopyVanishing) :
    ∀ (A : Type) [AddCommGroup A] [Finite A] (n : ℕ) (hn : 2 ≤ n)
      (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpace A n (by omega) X pt → Work.Serre.RatAcyclic X := by
  intro A _ _ n hn X _ pt h
  -- the group structure on `HomotopyGroup (Fin n)` (used inside `IsEMSpace`)
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  -- `π_0` and `π_1` vanish (`n ≥ 2`)
  have h0 : Subsingleton (HomotopyGroup (Fin 0) X pt) := h.2 0 (by omega)
  have h1 : Subsingleton (HomotopyGroup (Fin 1) X pt) := h.2 1 (by omega)
  -- every `π_{j+2}` is torsion: either it is `π_n ≅ A` (finite), or it vanishes
  have htors : ∀ j : ℕ, Work.RatHurewicz.IsTorsionGroup (HomotopyGroup (Fin (j + 2)) X pt) := by
    intro j
    by_cases hj : j + 2 = n
    · have hfin : Finite (HomotopyGroup (Fin (j + 2)) X pt) := by
        rw [hj]
        exact Finite.of_equiv (Multiplicative A) h.1.some.toEquiv.symm
      exact serreC3Aux_isTorsionGroup_of_finite
    · exact serreC3Aux_isTorsionGroup_of_subsingleton (h.2 (j + 2) hj)
  -- `X` is path connected, hence `H₀(X;ℚ) ≅ ℚ`
  haveI hpc : PathConnectedSpace X := by
    rw [pathConnectedSpace_iff_zerothHomotopy]
    exact ⟨⟨ZerothHomotopy.mk pt⟩,
      (Equiv.subsingleton_congr (HomotopyGroup.pi0EquivZerothHomotopy (x := pt))).mp h0⟩
  have h0iso : IsIso (Work.Serre.ratHomologyMap (Work.Serre.toPoint X) 0) := by
    refine Work.Serre.hZeroOfPiZero (Work.Serre.toPoint X) (fun x => ?_)
    haveI hXx : Subsingleton (HomotopyGroup (Fin 0) X x) :=
      (Equiv.subsingleton_congr (HomotopyGroup.pi0EquivZerothHomotopy (x := x))).mpr inferInstance
    haveI hPx : Subsingleton (HomotopyGroup (Fin 0) PUnit (Work.Serre.toPoint X x)) :=
      (Equiv.subsingleton_congr
        (HomotopyGroup.pi0EquivZerothHomotopy (x := Work.Serre.toPoint X x))).mpr inferInstance
    exact ⟨fun a b _ => Subsingleton.elim a b, fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  -- in positive degrees, Serre's torsion theorem kills the rational homology
  intro m
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    exact h0iso
  · have hvan : Work.Serre.RatVanishingBelow X (m + 3) :=
      hTV m X pt h0 h1 (fun j _ => htors j)
    have hX : IsZero (Work.Serre.ratH (TopCat.of X) m) := hvan m hm (by omega)
    have hP : IsZero (Work.Serre.ratH (TopCat.of PUnit) m) :=
      Work.Cohomology.homologyContractible_ring ℚ (X := TopCat.of PUnit) m hm
    exact serreC3Aux_isIso_of_subsingleton_module (Work.Serre.subsingleton_of_isZero hX)
      (Work.Serre.subsingleton_of_isZero hP) _

end

end Work.StemsB
