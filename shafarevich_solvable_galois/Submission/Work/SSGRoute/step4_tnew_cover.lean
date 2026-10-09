import Mathlib
import Submission.Work.SSGRoute.step4_y_aux
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.step4_transport_of_sha13
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking
open scoped Pointwise

/-! # The set `S` covers the places of new ramification

Two consequences of the stage-3 data of a coker-side datum `D = Step4CokerData p K n i j` that the
assembly of the datum `y` of the Fourth Step uses:

* `D.S` consists of finite places that are not over `p` (first conjunct): a place of `S` at which
  the pushed-down level-`n` map `D.psi` has a nontrivial inertia element inside `G_K` is a place of
  *new ramification* and hence, by `Work.SSGRoute.step4_psi_ramified_not_over_p`, never over `p`
  (the places over `p` are `T¹`-places, where the stage-3 data forces `psi` to be trivial on
  `D_A ∩ G_K`);

* every finite place `A` of new ramification that is `G_ℚ`-conjugate to an element of `S` is itself
  `G_ℚ`-conjugate to a place `P ∈ S` at which the same two conditions hold (second conjunct).  The
  only possible candidate is the given conjugate `A₀ ∈ S`, and the two conditions transfer:

  - `phi` trivial on `D_A` is `D_A ≤ ker phi`, and `ker phi` is normal, so it is conjugation
    invariant;
  - new ramification transfers because `step4_psi_ramified_isSplitIn` shows that `D_A ≤ G_K` at a
    place of new ramification; hence `D_{A₀} = s D_A s⁻¹ ≤ G_K` as well
    (`Work.SSGRoute.step4_isSplitIn_smul`), and the inertia transfers by conjugation. -/

theorem step4_tnew_cover {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ SSGRoute.QBar} [FiniteDimensional ℚ K] [Normal ℚ K] {n i j : ℕ} (D : Work.SSGRoute.Step4CokerData p K n i j) : (∀ A ∈ D.S, (∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1) → (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ D.psi σ ≠ 1) → SSGRoute.IsFinPlace ℚ A ∧ ¬ A.valuation (p : SSGRoute.QBar) < 1) ∧ (∀ A : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ A → A ∉ D.T0 → (∃ A₀ ∈ D.S, SSGRoute.IsConjPlace ℚ A₀ A) → (∀ σ ∈ SSGRoute.decomp ℚ A, D.phi σ = 1) → (∃ σ, SSGRoute.IsInertia ℚ A σ ∧ σ ∈ K.fixingSubgroup ∧ D.psi σ ≠ 1) → ∃ P ∈ D.S, SSGRoute.IsConjPlace ℚ P A ∧ (∀ σ ∈ SSGRoute.decomp ℚ P, D.phi σ = 1) ∧ (∃ σ, SSGRoute.IsInertia ℚ P σ ∧ σ ∈ K.fixingSubgroup ∧ D.psi σ ≠ 1)) := by
  refine ⟨?_, ?_⟩
  · -- First conjunct: a place of `S` of new ramification is finite and not over `p`.
    intro A hA _hφ hψ
    exact ⟨D.hSfin A hA, step4_psi_ramified_not_over_p D A (D.hSfin A hA) hψ⟩
  · -- Second conjunct: the new-ramification conditions transfer to the conjugate place of `S`.
    intro A hAfin _hAT0 hc hφ hψ
    obtain ⟨A₀, hA₀S, s, hs⟩ := hc
    -- `hs : s • A₀ = A`, so `A₀ = s⁻¹ • A`.
    have hs' : A₀ = s⁻¹ • A := by rw [← hs, inv_smul_smul]
    -- `A` is completely decomposed in `K`: `D_A ≤ G_K`.
    have hsplit : SSGRoute.IsSplitIn ℚ K A := step4_psi_ramified_isSplitIn D A hAfin hψ
    -- Conjugation invariance of "`phi` trivial on the decomposition group".
    have hφ₀ : ∀ σ ∈ SSGRoute.decomp ℚ A₀, D.phi σ = 1 := by
      intro σ hσ
      have hker : SSGRoute.decomp ℚ A₀ ≤ D.phi.ker := by
        rw [hs', decomp_conj, Subgroup.map_le_iff_le_comap,
          comap_conj_eq (MonoidHom.normal_ker D.phi) s⁻¹]
        exact fun τ hτ => MonoidHom.mem_ker.mpr (hφ τ hτ)
      exact MonoidHom.mem_ker.mp (hker hσ)
    -- `A₀` is completely decomposed in `K` as well.
    have hsplit₀ : SSGRoute.IsSplitIn ℚ K A₀ := by
      rw [hs']
      exact (step4_isSplitIn_smul K A s⁻¹).mpr hsplit
    obtain ⟨τ, hτI, _hτK, hτne⟩ := hψ
    -- The conjugate inertia element is an inertia element at `A₀`.
    have hI₀ : SSGRoute.IsInertia ℚ A₀ (s⁻¹ * τ * s) := by
      rw [hs']
      simpa using (isInertia_conj A s⁻¹ τ).mpr hτI
    refine ⟨A₀, hA₀S, ⟨s, hs⟩, hφ₀, s⁻¹ * τ * s, hI₀, hsplit₀ hI₀.1, ?_⟩
    -- `D.psi` of the conjugate inertia element is nontrivial.
    intro hconj
    have h1 : D.psi (s⁻¹ * τ * s) = (D.psi s)⁻¹ * D.psi τ * D.psi s := by
      rw [map_mul, map_mul, map_inv]
    have h1' : (D.psi s)⁻¹ * D.psi τ * D.psi s = 1 := by rw [← h1]; exact hconj
    have hτ1 : D.psi τ = 1 := by
      have h2 : D.psi τ = D.psi s * ((D.psi s)⁻¹ * D.psi τ * D.psi s) * (D.psi s)⁻¹ := by
        group
      rw [h2, h1']; group
    exact hτne hτ1

end Work.SSGRoute
