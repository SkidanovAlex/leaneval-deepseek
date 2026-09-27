import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.SL3Topology
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLComp.X3Background
import Submission.Work.EKLComp.locallyFree_compacta
import Submission.Work.EKLRelCross.LeafBasic

/-!
# Local freeness and a.e. free orbits

This module isolates the two elementary inputs of the leafwise-measure construction that are used
by several of its pieces (the existence `Work.EKLComp.leafwise_exists_of_free`, which is stated
with a.e. freeness as a hypothesis, and the derived clauses (U1), (U4)–(U9)):

* `Work.EKLComp.locallyFree_all` — the `U`-action on `X₃` is locally free for every subgroup
  `U ≤ SL₃(ℝ)` (Pisa §6.1), a specialisation of `Work.EKLComp.locallyFree_compacta`;
* `Work.EKLComp.ae_freeness` — (U2) / Pisa 7.12: if a probability `μ` is preserved by
  `α^{t₀}` and `α^{t₀}` contracts `U`, then `μ`-a.e. point has trivial `U`-stabiliser.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLComp

open Work.EKLContract

/-- **Local freeness of the `U`-action** (Pisa §6.1): `Work.EKLComp.locallyFree_compacta` gives
local freeness for the full `SL₃(ℝ)`-action on `X₃`; restricting the group element to a subgroup
gives `LocallyFree U` for every `U ≤ SL₃(ℝ)`. -/
theorem locallyFree_all (U : Subgroup SL3) : LocallyFree U := by
  intro K hK
  obtain ⟨δ, hδ, h⟩ := locallyFree_compacta K hK
  exact ⟨δ, hδ, fun x hx u _ huV hux => h x hx u huV hux⟩

/-- **(U2) a.e. free orbits** (Pisa 7.12 / EKL (2)).  If `μ` is a probability preserved by the
contracting element `α^{t₀}` and `U` is contracted by `α^{t₀}`, then `μ`-almost every point has
trivial `U`-stabiliser.  This is the hypothesis under which flowers are constructed, and it is
also clause (U2) of `P_Leafwise`. -/
theorem ae_freeness (U : Subgroup SL3) (hU : IsHoro U) (μ : Measure X3) [IsProbabilityMeasure μ]
    (t0 : Fin 3 → ℝ)
    (hmp : MeasurePreserving (fun x : X3 => aDiag t0 • x) μ μ)
    (hcontr : ContractU U t0) :
    ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 := by
  filter_upwards [Work.EKLRelCross.ae_frequently_visit μ t0 hmp] with x hx
  intro u hu hux
  by_contra hne
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x
  obtain ⟨δ, hδ, hloc⟩ := locallyFree_compacta K hKc
  have hV : V δ ∈ 𝓝 (1 : SL3) :=
    (Work.EKLContract.Lemmas.V_open_one δ hδ).1.mem_nhds
      (Work.EKLContract.Lemmas.V_open_one δ hδ).2
  have hev : ∀ᶠ n in atTop, aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹ ∈ V δ :=
    (hcontr u hu).eventually_mem hV
  have hfreq : ∃ᶠ n in atTop, (fun y : X3 => aDiag t0 • y)^[n] x ∈ interior K :=
    hx (interior K) (interior_mem_nhds.mpr hKn)
  obtain ⟨n, hnK, hnV⟩ := (hfreq.and_eventually hev).exists
  have hfix : (aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) • ((fun y : X3 => aDiag t0 • y)^[n] x)
      = (fun y : X3 => aDiag t0 • y)^[n] x := by
    rw [smul_iterate, mul_smul, mul_smul, inv_smul_smul, hux]
  have hconj : aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹ = 1 :=
    hloc _ (interior_subset hnK) _ hnV hfix
  exact hne (by
    calc u = (aDiag t0 ^ n)⁻¹ * (aDiag t0 ^ n * u * (aDiag t0 ^ n)⁻¹) * (aDiag t0 ^ n) := by
          group
      _ = 1 := by rw [hconj]; group)

end Work.EKLComp
