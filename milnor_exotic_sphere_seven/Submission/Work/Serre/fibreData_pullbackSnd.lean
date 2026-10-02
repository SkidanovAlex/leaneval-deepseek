import Mathlib
import Submission.Work.Serre.Defs
import Submission.Work.StemsB.c2oddRangeTwo
import Submission.Work.StemsB.Fibrations

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Serre

noncomputable section

open CategoryTheory CategoryTheory.Limits

/-! ## Transfer of fibre data along a homeomorphism -/

/-- A homeomorphism induces an isomorphism of rational homology in every degree. -/
private theorem nonempty_ratH_iso_of_homeo' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) (h : Nonempty (ratH (TopCat.of Y) n ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (ratH (TopCat.of X) n ≅ ModuleCat.of ℚ ℚ) := by
  haveI : IsIso (ratHomologyMap (e : C(X, Y)) n) :=
    IsRatHomologyIso.of_homotopyEquiv e.toHomotopyEquiv n
  obtain ⟨e'⟩ := h
  exact ⟨asIso (ratHomologyMap (e : C(X, Y)) n) ≪≫ e'⟩

/-- Vanishing of rational homology transfers across a homeomorphism. -/
private theorem isZero_ratH_of_homeo' {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (n : ℕ) (h : IsZero (ratH (TopCat.of Y) n)) :
    IsZero (ratH (TopCat.of X) n) := by
  haveI : IsIso (ratHomologyMap (e : C(X, Y)) n) :=
    IsRatHomologyIso.of_homotopyEquiv e.toHomotopyEquiv n
  exact IsZero.of_iso h (asIso (ratHomologyMap (e : C(X, Y)) n))

/-- Path connectedness transfers backwards across a homeomorphism. -/
private theorem pathConnectedSpace_of_homeo' {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) [PathConnectedSpace Y] : PathConnectedSpace X :=
  e.symm.surjective.pathConnectedSpace e.symm.continuous

/-! ## The fibre of the second projection of a pullback -/

/-- The fibre of `Work.StemsB.pullbackSnd p g` over `γ₀` is homeomorphic to the fibre of `p`
over `g γ₀`: a point over `γ₀` is a pair `(e, γ₀)` with `p e = g γ₀`. -/
def fibrePullbackSndHomeo {E B Γ : Type} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace Γ] (p : C(E, B)) (g : C(Γ, B)) (γ₀ : Γ) :
    Work.StemsB.fibre (Work.StemsB.pullbackSnd p g) γ₀ ≃ₜ Work.StemsB.fibre p (g γ₀) where
  toFun y := ⟨y.1.1.1, by
    have h1 : p y.1.1.1 = g y.1.1.2 := y.1.2
    have h2 : y.1.1.2 = γ₀ := y.2
    rw [h2] at h1
    exact h1⟩
  invFun e := ⟨⟨(e.1, γ₀), e.2⟩, rfl⟩
  left_inv y := by
    refine Subtype.ext (Subtype.ext (Prod.ext rfl ?_))
    exact y.2.symm
  right_inv e := rfl
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.subtype_mk ?_ _
    fun_prop

/-- The fibre data of the pullback fibration `Work.StemsB.pullbackSnd p g` at a point `γ₀` with
`g γ₀ = b₀` agrees with the fibre data of `p` at `b₀`: path connectedness, vanishing of the rational
homology off degree `r` in the range `≤ N`, and `H_r ≅ ℚ`. -/
theorem fibreData_pullbackSnd {E B Γ : Type} [TopologicalSpace E] [TopologicalSpace B]
    [TopologicalSpace Γ] (p : C(E, B)) (g : C(Γ, B)) (γ₀ : Γ) {b₀ : B} (hgb : g γ₀ = b₀)
    (r N : ℕ)
    (hfib0 : PathConnectedSpace (Work.StemsB.fibre p b₀))
    (hvan : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) t))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre p b₀)) r ≅ ModuleCat.of ℚ ℚ)) :
    PathConnectedSpace (Work.StemsB.fibre (Work.StemsB.pullbackSnd p g) γ₀) ∧
    (∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero
        (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackSnd p g) γ₀)) t)) ∧
    Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre (Work.StemsB.pullbackSnd p g) γ₀)) r ≅
      ModuleCat.of ℚ ℚ) := by
  subst hgb
  exact ⟨pathConnectedSpace_of_homeo' (fibrePullbackSndHomeo p g γ₀),
    fun t ht htr htN => isZero_ratH_of_homeo' (fibrePullbackSndHomeo p g γ₀) t (hvan t ht htr htN),
    nonempty_ratH_iso_of_homeo' (fibrePullbackSndHomeo p g γ₀) r hgen⟩

end

end Work.Serre
