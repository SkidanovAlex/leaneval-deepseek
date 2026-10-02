/-
Copyright: subproject `Submission/Work/FatouParabolic/` of `mandelbar_not_path_connected`.

# Lifting the strip coordinate through the coverings `F^[n]`

(Q4) of the design in `Submission/Work/NOTES_LEAD_mandelbar_gaps2.md` §2.1.

`Ψ₀` is the inverse Fatou coordinate on the horizontal tail strip `tailStrip C B`, satisfying the
Abel equation `F (Ψ₀ τ) = Ψ₀ (τ + 1)`.  Here we lift the map `τ ↦ Ψ₀ (τ + n)` through the covering
`F^[n] : Ω₀ → Ω₀` of the immediate basin `Ω₀ = immBasin F z₀ p₀`: on the deeper strip
`tailStrip (C - n) B` — convex, hence contractible, hence simply connected — there is a continuous
`X` with `F^[n] (X τ) = Ψ₀ (τ + n)`, and `X` agrees with `Ψ₀` on `tailStrip C B` (uniqueness of
lifts on the preconnected overlap).

The lift is `IsCoveringMap.existsUnique_continuousMap_lifts`, and the agreement clause is
`IsCoveringMap.eq_of_comp_eq`.
-/
import Mathlib
import Submission.Work.FatouParabolic.Core.ImmBasin.Defs
import Submission.Work.FatouParabolic.Core.isCoveringMap_iterate_immBasin

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Set Filter
open scoped Topology

namespace Work.FatouParabolic.Core

theorem exists_strip_lift {F : ℂ → ℂ} {z₀ p₀ : ℂ} {B C : ℝ} (hB : 0 < B)
    (hmap : Set.MapsTo F (Work.FatouParabolic.Core.immBasin F z₀ p₀)
      (Work.FatouParabolic.Core.immBasin F z₀ p₀))
    (hcover : ∀ n : ℕ, IsCoveringMap (Work.FatouParabolic.Core.immBasinIterate
      (Work.FatouParabolic.Core.immBasin F z₀ p₀) F hmap n))
    (Ψ₀ : ℂ → ℂ)
    (hΨ₀ : ∀ τ : ℂ, C < τ.re → |τ.im| < B →
      Ψ₀ τ ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀ ∧ F (Ψ₀ τ) = Ψ₀ (τ + 1) ∧
        DifferentiableAt ℂ Ψ₀ τ)
    (n : ℕ) :
    ∃ X : ℂ → ℂ, ContinuousOn X (Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B) ∧
      (∀ τ ∈ Work.FatouParabolic.Core.tailStrip (C - (n : ℝ)) B,
        X τ ∈ Work.FatouParabolic.Core.immBasin F z₀ p₀ ∧ (F^[n]) (X τ) = Ψ₀ (τ + n)) ∧
      (∀ τ ∈ Work.FatouParabolic.Core.tailStrip C B, X τ = Ψ₀ τ) := by
  classical
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  let Ω : Set ℂ := immBasin F z₀ p₀
  -- The Abel equation, iterated: `F^[k] (Ψ₀ τ) = Ψ₀ (τ + k)` on the tail strip.
  have hiter : ∀ (τ : ℂ), τ ∈ tailStrip C B → ∀ k : ℕ, (F^[k]) (Ψ₀ τ) = Ψ₀ (τ + k) := by
    intro τ hτ k
    have hτre : C < τ.re := hτ.1
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : C < (τ + (k : ℂ)).re ∧ |(τ + (k : ℂ)).im| < B := by
        have hre : (τ + (k : ℂ)).re = τ.re + (k : ℝ) := by simp
        have him : (τ + (k : ℂ)).im = τ.im := by simp
        exact ⟨by rw [hre]; linarith, by rw [him]; exact hτ.2⟩
      rw [Function.iterate_succ_apply', ih, (hΨ₀ (τ + (k : ℂ)) hk.1 hk.2).2.1]
      congr 1
      push_cast
      ring
  -- A base point of `tailStrip C B` (hence of the deeper strip as well).
  let τ₀ : ℂ := ((C + 1 : ℝ) : ℂ)
  have hτ₀re : τ₀.re = C + 1 := by simp [τ₀]
  have hτ₀im : τ₀.im = 0 := by simp [τ₀]
  have hτ₀S : τ₀ ∈ tailStrip C B := by
    refine ⟨?_, ?_⟩
    · rw [hτ₀re]; linarith
    · rw [hτ₀im]; simpa using hB
  have hτ₀A : τ₀ ∈ tailStrip (C - (n : ℝ)) B :=
    ⟨by rw [hτ₀re]; linarith, hτ₀S.2⟩
  -- `Ψ₀` is holomorphic (hence continuous) on the tail strip.
  have hΨdiff : DifferentiableOn ℂ Ψ₀ (tailStrip C B) :=
    fun τ hτ => ((hΨ₀ τ hτ.1 hτ.2).2.2).differentiableWithinAt
  have hΨcont : ContinuousOn Ψ₀ (tailStrip C B) := hΨdiff.continuousOn
  -- ... and so is `τ ↦ Ψ₀ (τ + n)` on the deeper strip.
  have hshift_maps : Set.MapsTo (fun z : ℂ => z + (n : ℂ))
      (tailStrip (C - (n : ℝ)) B) (tailStrip C B) := by
    intro z hz
    have hzre : C - (n : ℝ) < z.re := hz.1
    have hre : (z + (n : ℂ)).re = z.re + (n : ℝ) := by simp
    have him : (z + (n : ℂ)).im = z.im := by simp
    exact ⟨by rw [hre]; linarith, by rw [him]; exact hz.2⟩
  have hshift_cont : ContinuousOn (fun z : ℂ => Ψ₀ (z + (n : ℂ)))
      (tailStrip (C - (n : ℝ)) B) :=
    hΨcont.comp (continuous_id.add continuous_const).continuousOn hshift_maps
  -- The deeper strip is convex, hence contractible, hence simply connected; it is open, hence
  -- locally path connected.  The overlap `tailStrip C B` is convex, hence preconnected.
  haveI : LocallyPathConnectedSpace ↥(tailStrip (C - (n : ℝ)) B) :=
    (isOpen_tailStrip (C - (n : ℝ)) B).locallyPathConnectedSpace
  haveI : ContractibleSpace ↥(tailStrip (C - (n : ℝ)) B) :=
    (convex_tailStrip (C - (n : ℝ)) B).contractibleSpace ⟨τ₀, hτ₀A⟩
  haveI : SimplyConnectedSpace ↥(tailStrip (C - (n : ℝ)) B) :=
    SimplyConnectedSpace.ofContractible _
  haveI : PreconnectedSpace ↥(tailStrip C B) :=
    Subtype.preconnectedSpace (convex_tailStrip C B).isPreconnected
  -- The map we lift, and its value at the base point.
  let f : C(↥(tailStrip (C - (n : ℝ)) B), ↥Ω) :=
    ⟨fun σ => ⟨Ψ₀ (σ.1 + (n : ℂ)), (hΨ₀ _ (hshift_maps σ.2).1 (hshift_maps σ.2).2).1⟩,
      Continuous.subtype_mk (continuousOn_iff_continuous_domRestrict.mp hshift_cont) _⟩
  let e₀ : ↥Ω := ⟨Ψ₀ τ₀, (hΨ₀ τ₀ hτ₀S.1 hτ₀S.2).1⟩
  have hbase : immBasinIterate Ω F hmap n e₀ = f ⟨τ₀, hτ₀A⟩ := by
    refine Subtype.ext ?_
    rw [immBasinIterate_coe]
    change (F^[n]) (Ψ₀ τ₀) = Ψ₀ (τ₀ + (n : ℂ))
    rw [hiter τ₀ hτ₀S n]
  obtain ⟨Φ, ⟨hΦ0, hΦcomp⟩, -⟩ :=
    (hcover n).existsUnique_continuousMap_lifts f ⟨τ₀, hτ₀A⟩ e₀ hbase
  have hsub : tailStrip C B ⊆ tailStrip (C - (n : ℝ)) B :=
    tailStrip_subset (by linarith)
  refine ⟨fun τ => if h : τ ∈ tailStrip (C - (n : ℝ)) B then (Φ ⟨τ, h⟩).1 else Ψ₀ τ,
    ?_, ?_, ?_⟩
  · -- Continuity of the lift on the deeper strip.
    rw [continuousOn_iff_continuous_domRestrict]
    have hfun : (tailStrip (C - (n : ℝ)) B).domRestrict
        (fun τ => if h : τ ∈ tailStrip (C - (n : ℝ)) B then (Φ ⟨τ, h⟩).1 else Ψ₀ τ)
        = fun σ : ↥(tailStrip (C - (n : ℝ)) B) => (Φ σ).1 := by
      funext σ
      exact dite_eq_left σ.2
    rw [hfun]
    exact continuous_subtype_val.comp Φ.continuous
  · -- The defining property of the lift.
    intro τ hτ
    have hX : (if h : τ ∈ tailStrip (C - (n : ℝ)) B then (Φ ⟨τ, h⟩).1 else Ψ₀ τ) =
        (Φ ⟨τ, hτ⟩).1 := dite_eq_left hτ
    show (if h : τ ∈ tailStrip (C - (n : ℝ)) B then (Φ ⟨τ, h⟩).1 else Ψ₀ τ) ∈ Ω ∧
      (F^[n]) ((if h : τ ∈ tailStrip (C - (n : ℝ)) B then (Φ ⟨τ, h⟩).1 else Ψ₀ τ)) =
        Ψ₀ (τ + n)
    refine ⟨?_, ?_⟩
    · rw [hX]; exact (Φ ⟨τ, hτ⟩).2
    · rw [hX]
      have h2 := congrArg Subtype.val (congr_fun hΦcomp ⟨τ, hτ⟩)
      simp only [Function.comp_apply, immBasinIterate_coe] at h2
      exact h2
  · -- Agreement on the overlap, by uniqueness of lifts on the preconnected `tailStrip C B`.
    intro τ hτ
    have hXeq : (Φ ⟨τ, hsub hτ⟩).1 = Ψ₀ τ := by
      let u₁ : ↥(tailStrip C B) → ↥Ω := fun σ => Φ ⟨σ.1, hsub σ.2⟩
      let u₂ : ↥(tailStrip C B) → ↥Ω := fun σ => ⟨Ψ₀ σ.1, (hΨ₀ σ.1 σ.2.1 σ.2.2).1⟩
      have hcont₁ : Continuous u₁ :=
        Φ.continuous.comp (Continuous.subtype_mk continuous_subtype_val (fun σ => hsub σ.2))
      have hcont₂ : Continuous u₂ := by
        refine Continuous.subtype_mk ?_ _
        exact continuousOn_iff_continuous_domRestrict.mp hΨcont
      have heq : immBasinIterate Ω F hmap n ∘ u₁ = immBasinIterate Ω F hmap n ∘ u₂ := by
        funext σ
        apply Subtype.ext
        have h2 := congrArg Subtype.val (congr_fun hΦcomp ⟨σ.1, hsub σ.2⟩)
        simp only [Function.comp_apply, immBasinIterate_coe] at h2
        show (F^[n]) ((Φ ⟨σ.1, hsub σ.2⟩).1) = (F^[n]) (Ψ₀ σ.1)
        rw [hiter σ.1 σ.2 n]
        exact h2
      have hbase2 : u₁ ⟨τ₀, hτ₀S⟩ = u₂ ⟨τ₀, hτ₀S⟩ := by
        refine Subtype.ext ?_
        have h1 : (⟨τ₀, hsub hτ₀S⟩ : ↥(tailStrip (C - (n : ℝ)) B)) = ⟨τ₀, hτ₀A⟩ :=
          Subtype.ext rfl
        calc (Φ ⟨τ₀, hsub hτ₀S⟩).1 = (Φ ⟨τ₀, hτ₀A⟩).1 := by rw [h1]
          _ = (e₀ : ℂ) := by rw [hΦ0]
          _ = Ψ₀ τ₀ := rfl
      have hfin := (hcover n).eq_of_comp_eq hcont₁ hcont₂ heq ⟨τ₀, hτ₀S⟩ hbase2
      have hval := congrArg Subtype.val (congrFun hfin ⟨τ, hτ⟩)
      simpa using hval
    show (if h : τ ∈ tailStrip (C - (n : ℝ)) B then (Φ ⟨τ, h⟩).1 else Ψ₀ τ) = Ψ₀ τ
    rw [dite_eq_left (hsub hτ), hXeq]

end Work.FatouParabolic.Core
