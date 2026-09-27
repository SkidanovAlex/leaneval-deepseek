import Mathlib
import Submission.Work.EKLComp.MaxLeafDefs
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLComp.locallyFree_compacta

/-!
# `Work.EKLComp.free_ae` — a.e. trivial `U_ij`-stabilisers

For an `A`-invariant probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` and a root group `U_ij`
(`i ≠ j`), the stabiliser of `μ`-almost every point in `U_ij` is trivial:

  `μ (Free i j hij)ᶜ = 0`,  `Free i j hij = {x | ∀ u ∈ U_ij, u • x = x → u = 1}`.

The proof is the Poincaré-recurrence argument (Pisa 7.12 / EKL §2):

* pick `t₀` with `t₀ i < t₀ j`, so that `α^{t₀} = aDiag t₀` contracts `U_ij`
  (`Work.EKLContract.Lemmas.horoUij_tendsto_conj`) and preserves `μ` (`IsAInvariant`);
* by Poincaré recurrence (`Work.EKLRelCross.ae_frequently_visit`) a.e. `x` returns
  infinitely often to every neighbourhood of itself;
* if `u = u_ij(s) ≠ 1` fixed `x`, then for every `n` the conjugate
  `α^{n t₀} u α^{-n t₀} = u_ij(e^{n(t₀ i - t₀ j)} s)` fixes `α^{n t₀} x`; for large `n` it lies in
  any prescribed `V δ`, and the orbit returns to a compact neighbourhood of `x`, where local
  freeness of the action (`locallyFree_compacta`, proved from the discreteness of `Γ₃`) forces
  the conjugate to be `1`, hence `u = 1`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLComp

/-- **Local freeness on compacta implies a.e. free orbits** for a root group `U_ij`, for any
`A`-invariant probability `μ`.

The only inputs are: the contraction of `U_ij` by `aDiag t₀` in a direction with `t₀ i < t₀ j`, the
`μ`-preservation of that map, Poincaré recurrence, and local freeness of the action on compacta. -/
theorem ae_free_of_locfree (i j : Fin 3) (hij : i ≠ j)
    (μ : MeasureTheory.Measure X3) [MeasureTheory.IsProbabilityMeasure μ]
    (hA : Work.EKLContract.IsAInvariant μ)
    (hlf : ∀ K : Set X3, IsCompact K → ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ K, ∀ g : SL3, g ∈ Work.EKLContract.V δ → g • x = x → g = 1) :
    ∀ᵐ x ∂μ, ∀ u ∈ Uij hij, u • x = x → u = 1 := by
  -- a direction contracting `U_ij`
  have ht : (fun k : Fin 3 => if k = j then (1 : ℝ) else 0) i
      < (fun k : Fin 3 => if k = j then (1 : ℝ) else 0) j := by
    show (if i = j then (1 : ℝ) else 0) < (if j = j then (1 : ℝ) else 0)
    rw [if_neg hij, if_pos rfl]; norm_num
  obtain ⟨t₀, ht₀⟩ : ∃ t : Fin 3 → ℝ, t i < t j :=
    ⟨fun k : Fin 3 => if k = j then (1 : ℝ) else 0, ht⟩
  -- Poincaré recurrence for the contracting element
  filter_upwards [Work.EKLRelCross.ae_frequently_visit μ t₀ (hA t₀)] with x hx
  intro u hu hux
  obtain ⟨s, rfl⟩ := (Work.EKLContract.Lemmas.mem_Uij_iff hij u).mp hu
  by_contra hne
  have hs : s ≠ 0 := by
    intro h0
    exact hne (by simp [h0, Work.EKLContract.Lemmas.horoUij_zero hij])
  -- a compact neighbourhood of `x` and the local freeness radius on it
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x
  obtain ⟨δ, hδ, hloc⟩ := hlf K hKc
  -- the orbit returns into `interior K`
  have hfreq : ∃ᶠ n in atTop,
      (fun y : X3 => aDiag t₀ • y)^[n] x ∈ interior K :=
    hx (interior K) (interior_mem_nhds.mpr hKn)
  -- the conjugates eventually lie in `V δ`
  have hconv : Tendsto (fun n : ℕ => aDiag t₀ ^ n * uij hij s * (aDiag t₀ ^ n)⁻¹)
      atTop (𝓝 1) :=
    Work.EKLContract.Lemmas.horoUij_tendsto_conj t₀ hij ht₀ s
  have hV : Work.EKLContract.V δ ∈ 𝓝 (1 : SL3) :=
    (Work.EKLContract.Lemmas.V_open_one δ hδ).1.mem_nhds
      (Work.EKLContract.Lemmas.V_open_one δ hδ).2
  have hev : ∀ᶠ n in atTop, aDiag t₀ ^ n * uij hij s * (aDiag t₀ ^ n)⁻¹ ∈ Work.EKLContract.V δ :=
    hconv.eventually_mem hV
  obtain ⟨n, hnK, hnV⟩ := (hfreq.and_eventually hev).exists
  have hfix : (aDiag t₀ ^ n * uij hij s * (aDiag t₀ ^ n)⁻¹)
      • ((fun y : X3 => aDiag t₀ • y)^[n] x) = (fun y : X3 => aDiag t₀ • y)^[n] x := by
    rw [smul_iterate, mul_smul, mul_smul, inv_smul_smul, hux]
  have hone : aDiag t₀ ^ n * uij hij s * (aDiag t₀ ^ n)⁻¹ = 1 :=
    hloc _ (interior_subset hnK) _ hnV hfix
  exact hne (by
    calc uij hij s = (aDiag t₀ ^ n)⁻¹ * (aDiag t₀ ^ n * uij hij s * (aDiag t₀ ^ n)⁻¹)
          * (aDiag t₀ ^ n) := by group
      _ = 1 := by rw [hone]; group)

theorem free_ae (i j : Fin 3) (hij : i ≠ j) (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ] (hA : Work.EKLContract.IsAInvariant μ) :
    μ (Work.EKLComp.Free i j hij)ᶜ = 0 := by
  have hae : ∀ᵐ x ∂μ, x ∈ Free i j hij := by
    filter_upwards [ae_free_of_locfree i j hij μ hA locallyFree_compacta] with x hx
    exact hx
  exact MeasureTheory.ae_iff.mp hae

end Work.EKLComp
