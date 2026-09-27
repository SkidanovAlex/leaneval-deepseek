import Mathlib
import Submission.Work.EKLC7.LeafwiseHoroDefs
import Submission.Work.EKLComp.locallyFree_compacta
import Submission.Work.EKLComp.free_ae

/-!
# `Work.EKLC7.AeFreeStab` — a.e. trivial `U`-stabilisers for a horospherical subgroup

For an `A`-invariant probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` and a horospherical subgroup
`U ≤ SL₃(ℝ)` (`Work.EKLContract.IsHoro`), the orbit map `u ↦ u • x` is injective for `μ`-a.e. `x`:

  `∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1`.

This is clause (U2) of the frozen leafwise-measure component `Work.EKLContract.P_Leafwise`
(Pisa 7.12 / EKL §2), in the form used by the `EKLComp` files.

The proof is the standard Poincaré-recurrence argument, and it is uniform in the subgroup `U`:
`IsHoro U` supplies a direction `t₀` in which every `u ∈ U` is contracted, i.e.
`α^{n t₀} u α^{-n t₀} → 1`.  Suppose `u ∈ U ∖ {1}` fixes `x`.  Then the conjugate
`α^{n t₀} u α^{-n t₀} ≠ 1` fixes `α^{n t₀} x` for every `n`, and the `A`-invariance of `μ` makes
`x ↦ α^{t₀} x` a conservative transformation, so a.e. `x` returns infinitely often to any
neighbourhood of itself — in particular to the *interior* of a compact set `K ∋ x` on which the
action is locally free.  For a large return time `n` the conjugate lies in the local-freeness
neighbourhood `V δ`, so local freeness forces `α^{n t₀} u α^{-n t₀} = 1`, hence `u = 1`:
contradiction.
-/

open MeasureTheory Filter Topology
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC7

open Work.EKLContract

/-- **A.e. free orbits for horospherical `U`** (Pisa 7.12, clause (U2) of `P_Leafwise`).

If `μ` is an `A`-invariant probability measure on `X₃` and `U` is horospherical, then for
`μ`-a.e. `x` no non-trivial element of `U` fixes `x`. -/
theorem ae_free_orbit_of_horo (μ : MeasureTheory.Measure X3) [MeasureTheory.IsProbabilityMeasure μ]
    (hμ : IsAInvariant μ) (U : Subgroup SL3) (hU : IsHoro U) :
    ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 := by
  -- a direction contracting every element of `U`
  obtain ⟨t₀, ht₀⟩ := hU.2.2
  -- Poincaré recurrence for the `μ`-preserving map `x ↦ α^{t₀} x`
  filter_upwards [Work.EKLRelCross.ae_frequently_visit μ t₀ (hμ t₀)] with x hx
  intro u hu hux
  by_contra hne
  -- a compact neighbourhood of `x` and the local freeness radius on it
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x
  obtain ⟨δ, hδ, hloc⟩ := Work.EKLComp.locallyFree_compacta K hKc
  have hV : V δ ∈ 𝓝 (1 : SL3) :=
    (Work.EKLContract.Lemmas.V_open_one δ hδ).1.mem_nhds
      (Work.EKLContract.Lemmas.V_open_one δ hδ).2
  -- the conjugates of `u` eventually lie in `V δ`
  have hev : ∀ᶠ n in atTop, aDiag t₀ ^ n * u * (aDiag t₀ ^ n)⁻¹ ∈ V δ :=
    (ht₀ u hu).eventually_mem hV
  -- the orbit of `x` returns infinitely often into `interior K`
  have hfreq : ∃ᶠ n in atTop,
      (fun y : X3 => aDiag t₀ • y)^[n] x ∈ interior K :=
    hx (interior K) (interior_mem_nhds.mpr hKn)
  obtain ⟨n, hnK, hnV⟩ := (hfreq.and_eventually hev).exists
  -- that conjugate fixes the returning point
  have hfix : (aDiag t₀ ^ n * u * (aDiag t₀ ^ n)⁻¹)
      • ((fun y : X3 => aDiag t₀ • y)^[n] x) = (fun y : X3 => aDiag t₀ • y)^[n] x := by
    rw [smul_iterate, mul_smul, mul_smul, inv_smul_smul, hux]
  -- local freeness on `K` forces it to be trivial
  have hconj : aDiag t₀ ^ n * u * (aDiag t₀ ^ n)⁻¹ = 1 :=
    hloc _ (interior_subset hnK) _ hnV hfix
  exact hne (by
    calc u = (aDiag t₀ ^ n)⁻¹ * (aDiag t₀ ^ n * u * (aDiag t₀ ^ n)⁻¹) * (aDiag t₀ ^ n) := by
          group
      _ = 1 := by rw [hconj]; group)

theorem AeFreeStab (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (hμ : Work.EKLContract.IsAInvariant μ)
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) :
    ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 :=
  ae_free_orbit_of_horo μ hμ U hU

end Work.EKLC7
