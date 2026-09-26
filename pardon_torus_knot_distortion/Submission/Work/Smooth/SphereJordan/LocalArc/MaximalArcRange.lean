import Mathlib
import Submission.Work.Smooth.SphereJordan.LocalArc.ArcRange
import Submission.Work.Smooth.SphereJordan.LocalArc.ArcRangeExtension
import Submission.Work.Smooth.SphereJordan.LocalArc.ArcEnds
import Submission.Work.Smooth.SphereJordan.LocalArc.Ends

/-!
# Arc ranges ordered by inclusion, and the maximal one

An **arc range** through `x₀` is the range of an injective continuous `γ : ℝ → X` with `γ 0 = x₀`
(`IsArcRange x₀ U`, `ArcRange.lean`).  These sets are ordered by inclusion; a *maximal* one is the
key object for the classification of compact connected locally-arc spaces:

* `ends_eq_of_isMaximal`: **a maximal arc range has equal ends.**  Indeed, if its two ends were
  distinct, `exists_arc_range_strictly_larger` would produce a strictly bigger arc range, violating
  maximality.
* `circle_param_of_isMaximal`: consequently a maximal arc range gives the `2π`-periodic injective
  parametrisation (`Ends.exists_circle_param_of_ends_eq`).
* `circle_param_of_exists_maximal`: the classification therefore follows from the mere *existence*
  of a maximal arc range.
* `exists_isMaximal_of_chain_bounds`: that existence follows from Zorn once every chain of arc
  ranges has an upper bound (the chain bound is the only remaining input).
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function Filter

open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]

/-- **Maximality of an arc range** through `x₀`: no larger arc range contains it. -/
def IsMaximalArcRange (x₀ : X) (U : Set X) : Prop :=
  IsArcRange x₀ U ∧ ∀ V : Set X, IsArcRange x₀ V → U ⊆ V → V ⊆ U

/-- The inclusion order on arc ranges through `x₀`. -/
instance instPartialOrderArcRange (x₀ : X) : PartialOrder {U : Set X // IsArcRange x₀ U} where
  le U V := U.1 ⊆ V.1
  le_refl U := subset_rfl
  le_trans _ _ _ h1 h2 := h1.trans h2
  le_antisymm _ _ h1 h2 := Subtype.ext (subset_antisymm h1 h2)

/-- **A maximal arc range has equal ends.**

More precisely, if `U = range α` is maximal then the two ends of `α` (which exist in a compact
space, `ArcEnds.exists_ends`) coincide; the witness `p` is that common end. -/
theorem ends_eq_of_isMaximal {x₀ : X} (H : Work.Smooth.SphereJordan.IsLocallyArc X) {U : Set X}
    (hU : IsArcRange x₀ U) (hmax : ∀ V : Set X, IsArcRange x₀ V → U ⊆ V → V ⊆ U) :
    ∃ (α : ℝ → X) (p : X), Continuous α ∧ Function.Injective α ∧ α 0 = x₀ ∧
      Set.range α = U ∧ p ∉ Set.range α ∧ Tendsto α atTop (𝓝 p) ∧ Tendsto α atBot (𝓝 p) := by
  obtain ⟨α, hc, hi, h0, hr⟩ := hU
  obtain ⟨pPos, pNeg, -, -, htop, hbot, hpPos, hpNeg⟩ := exists_ends H hc hi
  have hpq : pPos = pNeg := by
    by_contra hne
    obtain ⟨γ, hγc, hγi, hγ0, hsub⟩ :=
      exists_arc_range_strictly_larger H hc hi hpPos htop hbot hne ⟨0, h0⟩
    have hV : IsArcRange x₀ (Set.range γ) := ⟨γ, hγc, hγi, hγ0, rfl⟩
    have hle : Set.range γ ⊆ U := hmax (Set.range γ) hV (by rw [← hr]; exact hsub.1)
    exact hsub.2 (by rw [hr]; exact hle)
  exact ⟨α, pPos, hc, hi, h0, hr, hpPos, htop, hpq ▸ hbot⟩

/-- **A maximal arc range yields the circular parametrisation.** -/
theorem circle_param_of_isMaximal [PreconnectedSpace X] {x₀ : X}
    (H : Work.Smooth.SphereJordan.IsLocallyArc X) {U : Set X} (hU : IsArcRange x₀ U)
    (hmax : ∀ V : Set X, IsArcRange x₀ V → U ⊆ V → V ⊆ U) :
    ∃ γ : ℝ → X, Continuous γ ∧ Function.Periodic γ (2 * Real.pi) ∧
      Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) ∧ Set.range γ = Set.univ := by
  obtain ⟨α, p, hc, hi, -, -, hp, htop, hbot⟩ := ends_eq_of_isMaximal H hU hmax
  exact exists_circle_param_of_ends_eq H hc hi hp htop hbot

/-- **The classification follows from the existence of a maximal arc range.** -/
theorem circle_param_of_exists_maximal [PreconnectedSpace X] {x₀ : X}
    (H : Work.Smooth.SphereJordan.IsLocallyArc X)
    (h : ∃ U : Set X, IsArcRange x₀ U ∧ ∀ V : Set X, IsArcRange x₀ V → U ⊆ V → V ⊆ U) :
    ∃ γ : ℝ → X, Continuous γ ∧ Function.Periodic γ (2 * Real.pi) ∧
      Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) ∧ Set.range γ = Set.univ := by
  obtain ⟨U, hU, hmax⟩ := h
  exact circle_param_of_isMaximal H hU hmax

/-- **Existence of a maximal arc range from a chain bound (Zorn).**

If every chain of arc ranges through `x₀` has an upper bound which is again an arc range through
`x₀`, then a maximal one exists.  The chain bound is the only remaining input of the classification;
it is what `isArcRange_iUnion_of_monotone` (nested case) plus second countability is meant to
supply. -/
theorem exists_isMaximal_of_chain_bounds (x₀ : X)
    (hb : ∀ c : Set (Set X), (∀ U ∈ c, IsArcRange x₀ U) → IsChain (· ⊆ ·) c →
      ∃ ub : Set X, IsArcRange x₀ ub ∧ ∀ U ∈ c, U ⊆ ub) :
    ∃ U : Set X, IsArcRange x₀ U ∧ ∀ V : Set X, IsArcRange x₀ V → U ⊆ V → V ⊆ U := by
  obtain ⟨m, hmS, hmax⟩ := zorn_subset {U : Set X | IsArcRange x₀ U} (by
    intro c hc hchain
    exact hb c (fun U hU => hc hU) hchain)
  exact ⟨m, hmS, fun V hV hmV => hmax (y := V) hV hmV⟩

end

end Work.Smooth.SphereJordan.LocalArc
