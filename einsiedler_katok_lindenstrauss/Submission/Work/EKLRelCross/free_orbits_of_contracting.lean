import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances

/-!
# `Work.EKLRelCross.free_orbits_of_contracting` — a.e. free orbits of a contracting horospherical
subgroup

This is item (U2) of the frozen contract `Work.EKLContract.P_Leafwise` (Pisa 7.12 / EKL p. 14):
for a probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)` preserved by the diagonal element
`α^{t₀} = aDiag t₀`, and a closed subgroup `U ≤ SL₃(ℝ)` normalised by `A` and *contracted* by
`α^{t₀}` (every `u ∈ U` has `α^{nt₀} u α^{-nt₀} → 1`), the action of `U` is a.e. free:

  `∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1`.

The proof uses only `P_X3` (`h2`); no leafwise measure theory is needed.

**Argument.**  Let `T = (· ↦ aDiag t₀ • ·)`.

1. `T` preserves the probability measure `μ`, hence is conservative, so by the Poincaré
   recurrence theorem `MeasureTheory.Conservative.ae_frequently_mem_of_mem_nhds` almost every `x`
   returns infinitely often to **every** neighbourhood of `x` (`hrec`).
2. Fix such an `x` and suppose `u ∈ U`, `u ≠ 1`, fixes `x`.  Choose a compact neighbourhood `K`
   of `x` (`WeaklyLocallyCompactSpace X₃`, supplied by the quotient instance
   `QuotientGroup.instLocallyCompactSpace` from `LocallyCompactSpace SL₃(ℝ)`), and let `δ > 0`
   be the *local freeness* radius of `P_X3` on `K`: for `y ∈ K` and `g ∈ V δ`, `g • y = y`
   forces `g = 1`.
3. Since `α^{nt₀} x ∈ K` for infinitely many `n` (`hfreq`, recurrence to `interior K`) while the
   conjugates `uₙ = α^{nt₀} u α^{-nt₀} ∈ V δ` for all large `n` (`hev`, contraction), some `n`
   has both properties.  The conjugation identity
   `uₙ • (α^{nt₀} x) = α^{nt₀} • (u • x) = α^{nt₀} x` exhibits `uₙ ∈ V δ` as a witness of
   non-freeness at the point `α^{nt₀} x ∈ K`, so local freeness gives `uₙ = 1`, whence
   `u = α^{-nt₀} uₙ α^{nt₀} = 1`, contradiction.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract
open Work.EKLContract.Lemmas

theorem free_orbits_of_contracting (h2 : Work.EKLContract.P_X3) {U : Subgroup Work.EKLContract.SL3}
    (hU : Work.EKLContract.IsHoro U) {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t0 : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => (Work.EKLContract.aDiag t0) ^ n * u * ((Work.EKLContract.aDiag t0) ^ n)⁻¹)
      Filter.atTop (nhds (1 : Work.EKLContract.SL3))) :
    ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1 := by
  -- Poincaré recurrence: a.e. point returns infinitely often to each of its neighbourhoods.
  have hrec : ∀ᵐ x ∂μ, ∀ s ∈ 𝓝 x, ∃ᶠ n in Filter.atTop,
      (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • y)^[n] x ∈ s :=
    hmp.conservative.ae_frequently_mem_of_mem_nhds
  filter_upwards [hrec] with x hx
  intro u hu hux
  by_contra hne
  -- A compact neighbourhood `K` of `x`, and the local freeness radius of `P_X3` on `K`.
  obtain ⟨K, hKc, hKn⟩ := exists_compact_mem_nhds x
  obtain ⟨δ, hδ, hinj⟩ := h2.2.2.2.1 K hKc
  have h1V : (1 : Work.EKLContract.SL3) ∈ Work.EKLContract.V δ := (V_open_one δ hδ).2
  have hV : Work.EKLContract.V δ ∈ 𝓝 (1 : Work.EKLContract.SL3) :=
    (V_open_one δ hδ).1.mem_nhds h1V
  -- The conjugates `α^{nt₀} u α^{-nt₀}` eventually lie in `V δ`.
  have hev : ∀ᶠ n in Filter.atTop,
      (Work.EKLContract.aDiag t0) ^ n * u * ((Work.EKLContract.aDiag t0) ^ n)⁻¹
        ∈ Work.EKLContract.V δ :=
    (hcontr u hu).eventually_mem hV
  -- Recurrence to the compact neighbourhood.
  have hfreq : ∃ᶠ n in Filter.atTop,
      (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • y)^[n] x ∈ interior K :=
    hx (interior K) (interior_mem_nhds.mpr hKn)
  obtain ⟨n, hnK, hnV⟩ := (hfreq.and_eventually hev).exists
  -- The conjugate fixes the corresponding point of the orbit of `x`.
  have hfix : ((Work.EKLContract.aDiag t0) ^ n * u * ((Work.EKLContract.aDiag t0) ^ n)⁻¹)
        • ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • y)^[n] x)
      = (fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • y)^[n] x := by
    rw [smul_iterate, mul_smul, mul_smul, inv_smul_smul, hux]
  -- Local freeness on the compact set `K` forces the conjugate to be trivial.
  have hconj : (Work.EKLContract.aDiag t0) ^ n * u * ((Work.EKLContract.aDiag t0) ^ n)⁻¹ = 1 :=
    hinj _ (interior_subset hnK) _ hnV 1 h1V (by rw [one_smul]; exact hfix)
  refine hne ?_
  calc u = ((Work.EKLContract.aDiag t0) ^ n)⁻¹
          * ((Work.EKLContract.aDiag t0) ^ n * u * ((Work.EKLContract.aDiag t0) ^ n)⁻¹)
          * (Work.EKLContract.aDiag t0) ^ n := by group
    _ = 1 := by rw [hconj]; group

end Work.EKLRelCross
