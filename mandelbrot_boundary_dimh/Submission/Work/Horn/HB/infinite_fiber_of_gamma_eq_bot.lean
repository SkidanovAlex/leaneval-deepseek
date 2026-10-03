import Mathlib
import Submission.Work.BasinSC.CoverDisc.exists_homeomorph_pow_of_isCoveringMap
import Submission.Lib.Unif2.Commons.Topology.Covering.natCard_fiber_eq_of_preconnected

/-!
# Infinitude of the fibres of a covering of the punctured disc with trivial deck group

Let `q : Z → 𝔻*` be a covering map with `Z` path connected, and let
`Γ = Gamma hcov t₀ z₀ hz ≤ ℤ` be the stabiliser of the basepoint `z₀` under the `ℤ`-action on the
fibre over `u t₀` induced by the deck translations of the universal covering `u : U → 𝔻*`
(`Work.BasinSC.CoverDisc.Gamma`).  We prove

`infinite_fiber_of_gamma_eq_bot : Γ = ⊥ → ∀ w, (q ⁻¹' {w}).Infinite`.

Two ingredients:

* if `Γ = ⊥` then the action `n ↦ T hcov t₀ n ⟨z₀, hz⟩ : ℤ → q ⁻¹' {u t₀}` is *injective*, so the
  fibre over `u t₀` contains an injective image of the infinite group `ℤ` (`Set.Infinite`);
* the fibres of a covering map over a preconnected base have constant `Nat.card`
  (`Commons.Topology.Covering.natCard_fiber_eq_of_preconnected`), and every fibre is non-empty
  (the total space is path connected), so infinitude of one fibre propagates to all of them.
-/

namespace Work.Horn.HB

open Set Metric Filter Topology
open scoped Topology
open Work.BasinSC.CoverDisc

/-- A covering map with path connected total space is surjective, in the form needed below: every
fibre is non-empty.  (Path connectivity of `Z` is used through the lift `baseLift` of `u`.) -/
theorem fiber_nonempty_of_isCoveringMap {Z : Type*} [TopologicalSpace Z] [PathConnectedSpace Z]
    {q : Z → ↥Work.BasinSC.puncturedDisc} (hcov : IsCoveringMap q)
    {t₀ : ↥Work.BasinSC.CoverDisc.U} {z₀ : Z} (hz : q z₀ = Work.BasinSC.CoverDisc.u t₀)
    (w : ↥Work.BasinSC.puncturedDisc) : (q ⁻¹' {w}).Nonempty := by
  obtain ⟨s, hs⟩ := u_surjective w
  refine ⟨baseLift hcov t₀ z₀ hz s, ?_⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff, baseLift_mem hcov t₀ z₀ hz s, hs]

theorem infinite_fiber_of_gamma_eq_bot {Z : Type*} [TopologicalSpace Z] [PathConnectedSpace Z]
    {q : Z → ↥Work.BasinSC.puncturedDisc} (hcov : IsCoveringMap q)
    {t₀ : ↥Work.BasinSC.CoverDisc.U} {z₀ : Z} (hz : q z₀ = Work.BasinSC.CoverDisc.u t₀)
    (hΓ : Work.BasinSC.CoverDisc.Gamma hcov t₀ z₀ hz = ⊥)
    (w : ↥Work.BasinSC.puncturedDisc) : (q ⁻¹' {w}).Infinite := by
  -- The basepoint of the fibre over `u t₀`, as a point of the fibre.
  let x : ↥(q ⁻¹' {u t₀}) := ⟨z₀, hz⟩
  -- ### Step 1: `Γ = ⊥` makes the `ℤ`-action on the fibre over `u t₀` free, hence that fibre is
  -- infinite.
  have hstab : ∀ k : ℤ, T hcov t₀ k x = x ↔ k = 0 := by
    intro k
    have h1 := T_base_stabilizer hcov t₀ z₀ hz k
    constructor
    · intro hk
      have hk' : k ∈ Gamma hcov t₀ z₀ hz := h1.mp hk
      rw [hΓ, AddSubgroup.mem_bot] at hk'
      exact hk'
    · intro hk
      exact h1.mpr (by rw [hk]; intro t; rw [Ushift_zero])
  have hInf0 : (q ⁻¹' {u t₀}).Infinite := by
    have hinj : Function.Injective (fun k : ℤ => T hcov t₀ k x) := by
      intro m n hmn
      have hmn' : T hcov t₀ m x = T hcov t₀ n x := hmn
      have hfix : T hcov t₀ (m - n) x = x := by
        rw [sub_eq_add_neg, T_add' hcov t₀ m (-n), hmn', ← T_add hcov t₀ (-n) n,
          neg_add_cancel, T_zero]
      exact sub_eq_zero.mp ((hstab (m - n)).mp hfix)
    exact Set.infinite_coe_iff.mp
      (Infinite.of_injective (fun k : ℤ => T hcov t₀ k x) hinj)
  -- ### Step 2: all fibres of `q` have the same `Nat.card` and are non-empty, so the fibre over an
  -- arbitrary `w` is infinite too.  (`𝔻*` is preconnected: it is the continuous image of the
  -- preconnected right half plane `U` under the surjection `u`.)
  have hpreconn : IsPreconnected (Set.univ : Set ↥Work.BasinSC.puncturedDisc) := by
    have h : Set.range u = (Set.univ : Set ↥Work.BasinSC.puncturedDisc) :=
      Set.range_eq_univ.mpr u_surjective
    rw [← h]
    exact isPreconnected_range u_continuous
  have hcard := Commons.Topology.Covering.natCard_fiber_eq_of_preconnected (f := q)
    hcov.isCoveringMapOn hpreconn (Set.mem_univ (u t₀)) (Set.mem_univ w)
  have h0 : Nat.card ↥(q ⁻¹' {u t₀}) = 0 :=
    Nat.card_eq_zero.mpr (Or.inr hInf0.to_subtype)
  have hw0 : Nat.card ↥(q ⁻¹' {w}) = 0 := hcard.symm.trans h0
  rcases Nat.card_eq_zero.mp hw0 with hemp | hinf
  · obtain ⟨y, hy⟩ := fiber_nonempty_of_isCoveringMap hcov hz w
    exact (hemp.false ⟨y, hy⟩).elim
  · exact Set.infinite_coe_iff.mp hinf

end Work.Horn.HB
