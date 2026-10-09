import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.ProperStageDefs
import Submission.Work.SSGRoute.twistLayer
import Submission.Work.SSGRoute.local_transport
import Submission.Work.SSGRoute.step4_local_cyclic_bridge
import Submission.Work.SSGRoute.twist_cyclic_of_psi_trivial
import Submission.Work.CohomologicalShrinking.All
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The (A)–(F) assembly of Step 4 (items (5) and (6))

This module carries out the two case splits of the Step-4 assembly, on top of the `y`/`x` bundle
produced by the two arithmetic inputs (`SSGRoute.coker_obstruction` and
`SSGRoute.shafarevich_theorem13`).  It is the concrete form of the spec recorded in
`Submission/Work/SSGRoute/step4_local_cyclic_bridge.lean`:

* **item (5)** (`A ∉ T⁰`, the twist ramified over `K`, `φ|D_A = 1`) — three cases:
  `A` conjugate to an element of `S` (the bridge `step4_local_cyclic_of_eq_on`, with the local
  target `η` and pointwise agreement of `x` with `η` — supplied by the `coker_obstruction` side);
  `A` not conjugate to `S` but completely decomposed in the field `Λ` of `ψ` (`ψ|D_A = 1`), where
  `twist_cyclic_of_psi_trivial` with Theorem 13's cyclicity clause applies;
  finally `A` not conjugate to `S` and not completely decomposed in `Λ`, where both `ψ` and `x`
  are unramified on `I_A ∩ G_K`, so the twist is unramified and the clause is vacuous.
* **item (6)** — a case split on `φ|D_A`: if `φ|D_A = 1` then the cyclicity comes from item (5)
  (for `A ∉ T⁰`), from `x = 0` on `D_A` (for `A ∈ T⁰`), or from the bridge; the inertia statement
  is `inertia_map_eq_flowTwistEHom`.  If `φ|D_A ≠ 1` then the twist's local group is transferred
  from `ψ`'s: either `x` is a coboundary on `D_A` (the paper's `T²` prescription, "subtract the
  unramified part"), giving `isCyclic_map_flowTwistEHom_of_isCoboundaryOn` and
  `inertia_generates_flowTwistEHom_iff`, or the local target realises the twist by `η` (bridge). -/

namespace Work.SSGRoute

open SSGRoute
open Work.CohomologicalShrinking

set_option maxHeartbeats 2000000

/-- The closure of the image of a subgroup is its image subgroup. -/
theorem closure_image_eq_map {G H : Type*} [Group G] [Group H] (f : G →* H) (H' : Subgroup G) :
    Subgroup.closure (f '' (H' : Set G)) = H'.map f := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le (H'.map f)]
    rintro _ ⟨σ, hσ, rfl⟩
    exact Subgroup.mem_map_of_mem f hσ
  · rintro _ ⟨σ, hσ, rfl⟩
    exact Subgroup.subset_closure ⟨σ, hσ, rfl⟩

/-- If the level-`τ` solution is trivial on `D_A` then `D_A ≤ G_K`. -/
theorem decomp_le_fixingSubgroup_of_eq_one (p : ℕ) (K : IntermediateField ℚ SSGRoute.QBar)
    [Normal ℚ K] (n i j : ℕ) (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (hφquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n i j (φ σ) = Work.SSGRoute.restrict K σ)
    (A : ValuationSubring SSGRoute.QBar) (h : ∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) :
    ∀ σ ∈ SSGRoute.decomp ℚ A, σ ∈ K.fixingSubgroup := by
  intro σ hσ
  refine mem_fixingSubgroup_of_restrict_eq_one K ?_
  rw [← hφquot σ, h σ hσ, map_one]

/-- If `A` is completely decomposed in the field `Λ` of `ψ` then `ψ` is trivial on `D_A`. -/
theorem eq_one_of_isSplitIn (p : ℕ) (K Λ : IntermediateField ℚ SSGRoute.QBar) [Normal ℚ K]
    (n i j : ℕ) (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n
      (tauSucc i j).1 (tauSucc i j).2)
    (hΛker : ψ.ker = Λ.fixingSubgroup) (A : ValuationSubring SSGRoute.QBar)
    (h : SSGRoute.IsSplitIn ℚ Λ A) : ∀ σ ∈ SSGRoute.decomp ℚ A, ψ σ = 1 := by
  intro σ hσ
  rw [← MonoidHom.mem_ker, hΛker]
  exact h hσ

/-- **Item (5) of the assembly.**  The local cyclicity of the twist at the places of new
ramification outside `T⁰`, from the `y`/`x` bundle: the local-target bridge at the conjugates of
`S`, Theorem 13's cyclicity clause outside them, and vacuity where the twist is unramified. -/
theorem item5_of_bundle (p : ℕ) [Fact p.Prime] (K Λ : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (φ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n i j)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n
      (tauSucc i j).1 (tauSucc i j).2)
    (hφquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n i j (φ σ) = Work.SSGRoute.restrict K σ)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) =
      Work.SSGRoute.restrict K σ)
    (hΛker : ψ.ker = Λ.fixingSubgroup)
    (S : Finset (ValuationSubring SSGRoute.QBar))
    (hSram : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (SSGRoute.IsRamifiedIn ℚ Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace ℚ A B)
    (T0 : Finset (ValuationSubring SSGRoute.QBar))
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (Work.SSGRoute.restrict K σ) • x τ)
    (hxinertia : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) → ¬ SSGRoute.IsSplitIn ℚ Λ B →
      ∀ σ : SSGRoute.GalQ, SSGRoute.IsInertia ℚ B σ → x σ = 0)
    (hreal : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A → A ∉ T0 →
      (∃ A₀ ∈ S, SSGRoute.IsConjPlace ℚ A₀ A) →
      (∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) →
      ∃ η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
        (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
        (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
        IsCyclic (Subgroup.closure
          ((flowTwistE p K n i j η ψ) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
        (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
          flowTwistE p K n i j η ψ τ = flowTwistE p K n i j η ψ σ) ∧
        ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = η σ)
    (hcycOut : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ℚ A B) → SSGRoute.IsSplitIn ℚ Λ B →
      ∃ U : Subgroup SSGRoute.GalQ,
        (∃ V : Subgroup SSGRoute.GalQ, IsOpen (V : Set SSGRoute.GalQ) ∧
          U = V ⊓ SSGRoute.decomp ℚ B) ∧
        (∀ δ ∈ SSGRoute.decomp ℚ B, ∀ u ∈ U, δ * u * δ⁻¹ ∈ U) ∧
        (∃ g ∈ SSGRoute.decomp ℚ B, ∀ δ ∈ SSGRoute.decomp ℚ B, ∃ m : ℤ, δ⁻¹ * g ^ m ∈ U) ∧
        SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) U x) :
    ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A → A ∉ T0 →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      (∀ σ ∈ SSGRoute.decomp ℚ A, φ σ = 1) →
      IsCyclic ((SSGRoute.decomp ℚ A).map (flowTwistEHom p K n i j x ψ hψquot hxmul)) := by
  intro A hAfin hAT0 hram hφ1
  by_cases hS : ∃ A₀ ∈ S, SSGRoute.IsConjPlace ℚ A₀ A
  · -- the local target at `A` and the pointwise bridge
    obtain ⟨η, hηadd, hηloc, hη0, hηcyc, hηgen, heq⟩ := hreal A hAfin hAT0 hS hφ1
    have hb := step4_local_cyclic_of_eq_on p K n i j ψ x A
      ⟨η, hηadd, hηloc, hη0, hηcyc, hηgen, heq⟩
    rw [← closure_image_eq_map (flowTwistEHom p K n i j x ψ hψquot hxmul)
      (SSGRoute.decomp ℚ A)]
    exact hb.1
  · have hS' : ∀ A₀ ∈ S, ¬ SSGRoute.IsConjPlace ℚ A₀ A :=
      fun A₀ hA₀ hconj => hS ⟨A₀, hA₀, hconj⟩
    by_cases hΛ : SSGRoute.IsSplitIn ℚ Λ A
    · -- Theorem 13's cyclicity clause, at a place where `ψ` is trivial on `D_A`
      have hDK := decomp_le_fixingSubgroup_of_eq_one p K n i j φ hφquot A hφ1
      have hψA := eq_one_of_isSplitIn p K Λ n i j ψ hΛker A hΛ
      exact twist_cyclic_of_psi_trivial p K n i j x ψ hψquot hxmul A hDK hψA
        (hcycOut A hAfin hS' hΛ)
    · -- vacuity: both `ψ` and `x` are unramified on `I_A ∩ G_K`
      obtain ⟨σ, hI, hσK, hne⟩ := hram
      have hx0 : x σ = 0 := hxinertia A hAfin hS' hΛ σ hI
      have hnotram : ¬ SSGRoute.IsRamifiedIn ℚ Λ A :=
        fun hram' => hS (hSram A hAfin (Or.inl hram'))
      have hσΛ : σ ∈ Λ.fixingSubgroup := by
        by_contra hcon
        exact hnotram ⟨σ, hI, hcon⟩
      have hψ1 : ψ σ = 1 := by
        rw [← MonoidHom.mem_ker, hΛker]
        exact hσΛ
      rw [flowTwistEHom_apply, flowTwistE, flowTwist, hx0, hψ1] at hne
      simp at hne


/-- **Item (6) of the assembly.**  The transfer of the cyclic local structure from `ψ` to the twist,
from the `y`/`x` bundle.

The bundle input `hdich` is the paper's two local prescriptions at the places where the twist is
ramified: either `x` is a `1`-coboundary on `D_A` — so that on `D_A` the twist is the conjugate of
`ψ` (`Work.SSGRoute.flowTwistEHom_eq_conj_of_isCoboundaryOn`) and both properties transfer from the
hypothesis on `ψ` — or the local target realises the twist (`Work.SSGRoute.step4_local_target`),
when `pointwise agreement on `D_A`` gives both properties by the bridge
`Work.SSGRoute.step4_local_cyclic_of_eq_on`.  (This is the `T²` prescription "subtract the unramified
part" together with the `T³` local targets; at the places where `ψ` is trivial on `D_A` and `x`
ramifies the coboundary case is what Theorem 13's `hxnot`/`hxsplit` supplies.) -/
theorem item6_of_bundle (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (ψ : SSGRoute.GalQ →* flowGroup p (K ≃ₐ[ℚ] K) n
      (tauSucc i j).1 (tauSucc i j).2)
    (hψquot : ∀ σ, flowQuot p (K ≃ₐ[ℚ] K) n (tauSucc i j).1 (tauSucc i j).2 (ψ σ) =
      Work.SSGRoute.restrict K σ)
    (x : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j)
    (hxmul : ∀ σ τ : SSGRoute.GalQ, x (σ * τ) = x σ + (Work.SSGRoute.restrict K σ) • x τ)
    (hdich : ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      SSGRoute.IsCoboundaryOn (Work.SSGRoute.restrict K) (SSGRoute.decomp ℚ A) x ∨
        ∃ η : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
          (∀ σ ∈ SSGRoute.decomp ℚ A, ∀ τ ∈ SSGRoute.decomp ℚ A, η (σ * τ) = η σ + η τ) ∧
          SSGRoute.IsLocConstOn (SSGRoute.decomp ℚ A) η ∧
          (∀ σ, SSGRoute.IsInertia ℚ A σ → η σ = 0) ∧
          IsCyclic (Subgroup.closure
            ((flowTwistE p K n i j η ψ) '' (SSGRoute.decomp ℚ A : Set SSGRoute.GalQ))) ∧
          (∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
            flowTwistE p K n i j η ψ τ = flowTwistE p K n i j η ψ σ) ∧
          ∀ σ ∈ SSGRoute.decomp ℚ A, x σ = η σ) :
    ∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ ψ σ ≠ 1) →
      (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧
        (flowTwistEHom p K n i j x ψ hψquot hxmul) σ ≠ 1) →
      (IsCyclic ((SSGRoute.decomp ℚ A).map ψ) ∧
        ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧ ψ τ = ψ σ) →
      IsCyclic ((SSGRoute.decomp ℚ A).map (flowTwistEHom p K n i j x ψ hψquot hxmul)) ∧
        ∀ σ ∈ SSGRoute.decomp ℚ A, ∃ τ, SSGRoute.IsInertia ℚ A τ ∧
          (flowTwistEHom p K n i j x ψ hψquot hxmul) τ =
          (flowTwistEHom p K n i j x ψ hψquot hxmul) σ := by
  intro A hAfin hramψ hramtw hcycψ
  rcases hdich A hAfin hramtw with hcob | ⟨η, hηadd, hηloc, hη0, hηcyc, hηgen, heq⟩
  · -- the twist is the conjugate of `ψ` on `D_A`: everything transfers
    obtain ⟨M, hM⟩ := flowTwistEHom_eq_conj_of_isCoboundaryOn p K n i j x ψ hψquot hxmul
      (H := SSGRoute.decomp ℚ A) hcob
    refine ⟨isCyclic_map_flowTwistEHom_of_isCoboundaryOn p K n i j x ψ hψquot hxmul
      (H := SSGRoute.decomp ℚ A) hcob hcycψ.1, ?_⟩
    intro σ hσ
    obtain ⟨τ, hτ, hτeq⟩ := hcycψ.2 σ hσ
    exact ⟨τ, hτ, by rw [hM τ hτ.1, hM σ hσ, hτeq]⟩
  · -- the local target realises the twist: the bridge
    obtain ⟨hb1, hb2⟩ := step4_local_cyclic_of_eq_on p K n i j ψ x A
      ⟨η, hηadd, hηloc, hη0, hηcyc, hηgen, heq⟩
    refine ⟨?_, ?_⟩
    · rw [← closure_image_eq_map (flowTwistEHom p K n i j x ψ hψquot hxmul)
        (SSGRoute.decomp ℚ A)]
      exact hb1
    · intro σ hσ
      obtain ⟨τ, hτ, hτeq⟩ := hb2 σ hσ
      exact ⟨τ, hτ, by rw [flowTwistEHom_apply, flowTwistEHom_apply]; exact hτeq⟩

end Work.SSGRoute
