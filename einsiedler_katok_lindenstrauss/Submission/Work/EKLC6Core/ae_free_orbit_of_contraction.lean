import Mathlib
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLC6Core.uniform_injective_V_X3
import Submission.Work.EKLContract.Lemmas.V_open_one

/-!
# `Work.EKLC6Core.ae_free_orbit_of_contraction`

Item (U2) of the frozen contract `Work.EKLContract.P_Leafwise` (Pisa 7.12 / EKL p. 14):
for a probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` preserved by the diagonal element
`α^{t} = aDiag t`, and a closed subgroup `U ≤ SL₃(ℝ)` normalised by `A` and *contracted* by
`α^{t}` (every `u ∈ U` has `α^{nt} u α^{-nt} → 1`), the action of `U` is a.e. free:

  `∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1`.

The proof uses only uniform injectivity of the action on compact subsets of `X₃`
(`Work.EKLC6Core.uniform_injective_V_X3`, the fourth conjunct of `P_X3`, proved directly here from
discreteness of `Γ₃`); no leafwise measure theory is needed.

**Argument.**  Let `T = (· ↦ aDiag t • ·)`.

1. `T` preserves the probability measure `μ`, hence is conservative, so by the Poincaré
   recurrence theorem `MeasureTheory.Conservative.ae_frequently_mem_of_mem_nhds` almost every `x`
   returns infinitely often to **every** neighbourhood of `x` (`hrec`).
2. Fix such an `x` and suppose `u ∈ U`, `u ≠ 1`, fixes `x`.  Choose a compact neighbourhood `K`
   of `x` (from local compactness of the quotient `SL₃(ℝ)/SL₃(ℤ)`), and let `δ > 0` be the
   *uniform injectivity* radius on `K`: for `y ∈ K` and `g ∈ V δ`, `g • y = y` forces `g = 1`.
3. Since `α^{nt} x ∈ K` for infinitely many `n` (`hfreq`, recurrence to `interior K`) while the
   conjugates `uₙ = α^{nt} u α^{-nt} ∈ V δ` for all large `n` (`hev`, contraction), some `n`
   has both properties.  The conjugation identity
   `uₙ • (α^{nt} x) = α^{nt} • (u • x) = α^{nt} x` exhibits `uₙ ∈ V δ` as a witness of
   non-injectivity at the point `α^{nt} x ∈ K`, so uniform injectivity gives `uₙ = 1`, whence
   `u = α^{-nt} uₙ α^{nt} = 1`, contradiction.
-/

open MeasureTheory Filter Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

theorem ae_free_orbit_of_contraction {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (U : Subgroup Work.EKLContract.SL3)
    (hU : Work.EKLContract.IsHoro U) (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1)) :
    ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 := by
  -- Poincaré recurrence: a.e. point returns infinitely often to each of its neighbourhoods.
  have hrec : ∀ᵐ x ∂μ, ∀ s ∈ 𝓝 x, ∃ᶠ n in Filter.atTop,
      (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n] x ∈ s :=
    hmp.conservative.ae_frequently_mem_of_mem_nhds
  filter_upwards [hrec] with x hx
  intro u hu hux
  by_contra hne
  -- A compact neighbourhood `K` of `x`, and the uniform injectivity radius on `K`.
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x
  obtain ⟨δ, hδ, hinj⟩ := Work.EKLC6Core.uniform_injective_V_X3 K hKc
  have h1V : (1 : Work.EKLContract.SL3) ∈ Work.EKLContract.V δ :=
    (Work.EKLContract.Lemmas.V_open_one δ hδ).2
  have hV : Work.EKLContract.V δ ∈ 𝓝 (1 : Work.EKLContract.SL3) :=
    (Work.EKLContract.Lemmas.V_open_one δ hδ).1.mem_nhds h1V
  -- The conjugates `aDiag t ^ n * u * (aDiag t ^ n)⁻¹` eventually lie in `V δ`.
  have hev : ∀ᶠ n in Filter.atTop,
      Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹
        ∈ Work.EKLContract.V δ :=
    (hcontr u hu).eventually_mem hV
  -- Recurrence to the compact neighbourhood.
  have hfreq : ∃ᶠ n in Filter.atTop,
      (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n] x ∈ interior K :=
    hx (interior K) (interior_mem_nhds.mpr hKn)
  obtain ⟨n, hnK, hnV⟩ := (hfreq.and_eventually hev).exists
  -- The conjugate fixes the corresponding point of the orbit of `x`.
  have hfix : (Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
        • ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n] x)
      = (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n] x := by
    rw [smul_iterate, mul_smul, mul_smul, inv_smul_smul, hux]
  -- Uniform injectivity on the compact set `K` forces the conjugate to be trivial.
  have hconj : Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹ = 1 :=
    hinj _ (interior_subset hnK) _ hnV 1 h1V (by rw [one_smul]; exact hfix)
  refine hne ?_
  calc u = (Work.EKLContract.aDiag t ^ n)⁻¹
          * (Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
          * Work.EKLContract.aDiag t ^ n := by group
    _ = 1 := by rw [hconj]; group

end Work.EKLC6Core
