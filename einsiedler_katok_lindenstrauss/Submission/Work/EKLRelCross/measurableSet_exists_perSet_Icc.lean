import Mathlib
import Submission.Work.EKLRelCross.PeriodDefs
import Submission.Work.EKLRelCross.ciInf_rat_eq_zero_iff

/-!
# Measurability of `{x ∈ X' | PerSet(ν x) meets [a,b]}`

Let `ν` be a (weakly measurable) family of Radon measures on `SL₃(ℝ)`, all carried by the root
subgroup `U_ij = range (fun t => u_ij t)`, and suppose that the family `F : ℕ → C_c(SL₃, ℝ)`
*determines* such measures (`hF`).  Then for rationals `0 < a` and arbitrary `b` the set

`{x | x ∈ X' ∧ ∃ τ ∈ Icc a b, τ ∈ PerSet ν i j hij x}`

is measurable, where `PerSet ν i j hij x = {τ | (ν x).map (· * u_ij τ) = ν x}`.

The proof has three ingredients.

* `perSet_iff_psi`: using `hF`, for `x ∈ X'` membership in the period set is equivalent to the
  vanishing of the *countable* family of functions
  `ψ k τ x = ∫ g, F k (g * u_ij τ) ∂(ν x) - ∫ g, F k g ∂(ν x)`.
* For each `m`, the partial sum of squares `τ ↦ ∑_{k ≤ m} ψ k τ x ²` is continuous in `τ` and
  non-negative, so `ciInf_rat_eq_zero_iff` identifies `⨅_{q ∈ ℚ∩[a,b]} ∑_{k ≤ m} ψ k q x ² = 0`
  with the non-emptiness of the (closed, compact) level set `[a,b] ∩ {τ | ∀ k ≤ m, ψ k τ x = 0}`.
* The level sets are nested closed subsets of the compact interval `[a,b]`; by compactness they
  have a common point iff all of them are non-empty, and their intersection is exactly
  `[a,b] ∩ PerSet ν i j hij x`.
-/

namespace Work.EKLRelCross

open MeasureTheory Filter Topology
open Work.EKLContract

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-! ## The root range is preserved by right translation -/

/-- Right translation by `u_ij τ` preserves the complement of the root range, because the range
is a subgroup. -/
theorem preimage_compl_range_uij {i j : Fin 3} (hij : i ≠ j) (τ : ℝ) :
    (fun g : SL3 => g * uij hij τ) ⁻¹'
      (Set.range (fun t : ℝ => uij hij t))ᶜ
      = (Set.range (fun t : ℝ => uij hij t))ᶜ := by
  let H := Work.EKLContract.Lemmas.rangeUij hij
  have hcoe : (H : Set SL3) = Set.range (fun t : ℝ => uij hij t) :=
    Work.EKLContract.Lemmas.coe_rangeUij hij
  have hτ : uij hij τ ∈ H := by
    show uij hij τ ∈ (H : Set SL3); rw [hcoe]; exact Set.mem_range_self τ
  have keyH : ∀ g : SL3, g * uij hij τ ∈ (H : Set SL3) ↔ g ∈ (H : Set SL3) := by
    intro g
    constructor
    · intro h
      have hm := H.mul_mem h (H.inv_mem hτ)
      rwa [mul_inv_cancel_right] at hm
    · intro h
      exact H.mul_mem h hτ
  ext g
  simp only [Set.mem_preimage, Set.mem_compl_iff]
  rw [← hcoe]
  exact not_congr (keyH g)

/-- The pushforward of a measure carried by the root range is again carried by the root range. -/
theorem map_mulRight_uij_compl_range {i j : Fin 3} (hij : i ≠ j) (ν : Measure SL3)
    (hcar : ν (Set.range (fun t : ℝ => uij hij t))ᶜ = 0) (τ : ℝ) :
    (ν.map (fun g : SL3 => g * uij hij τ))
      (Set.range (fun t : ℝ => uij hij t))ᶜ = 0 := by
  have hφ : MeasurableEmbedding (fun g : SL3 => g * uij hij τ) := by
    simpa using (Homeomorph.mulRight (uij hij τ)).measurableEmbedding
  rw [hφ.map_apply ν ((Set.range (fun t : ℝ => uij hij t))ᶜ),
      preimage_compl_range_uij hij τ, hcar]

/-! ## The families `Φ` and `ψ` -/

/-- `Φ k τ x = ∫ g, (F k) (g * u_ij τ) ∂(ν x)`, the translate of the `k`-th test integral. -/
def Phi (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    {i j : Fin 3} (hij : i ≠ j) (k : ℕ) (τ : ℝ) (x : X3) : ℝ :=
  ∫ g, ((F k).comp (Homeomorph.mulRight (uij hij τ)).toCocompactMap) g ∂(ν x)

/-- `ψ k τ x = Φ k τ x - Φ k 0 x`: the change of the `k`-th test integral under translation. -/
def Psi (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    {i j : Fin 3} (hij : i ≠ j) (k : ℕ) (τ : ℝ) (x : X3) : ℝ :=
  Phi ν F hij k τ x - Phi ν F hij k 0 x

theorem Phi_apply (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    {i j : Fin 3} (hij : i ≠ j) (k : ℕ) (τ : ℝ) (x : X3) :
    Phi ν F hij k τ x = ∫ g, F k (g * uij hij τ) ∂(ν x) := rfl

theorem Phi_zero (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    {i j : Fin 3} (hij : i ≠ j) (k : ℕ) (x : X3) :
    Phi ν F hij k 0 x = ∫ g, F k g ∂(ν x) := by
  simp [Phi, Work.EKLC7.uij_zero]

theorem measurable_Phi (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    {i j : Fin 3} (hij : i ≠ j)
    (hmeas : ∀ f : CompactlySupportedContinuousMap SL3 ℝ, Measurable (fun x => ∫ g, f g ∂(ν x)))
    (k : ℕ) (τ : ℝ) : Measurable (fun x : X3 => Phi ν F hij k τ x) := by
  simpa [Phi] using hmeas ((F k).comp (Homeomorph.mulRight (uij hij τ)).toCocompactMap)

theorem measurable_Psi (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    {i j : Fin 3} (hij : i ≠ j)
    (hmeas : ∀ f : CompactlySupportedContinuousMap SL3 ℝ, Measurable (fun x => ∫ g, f g ∂(ν x)))
    (k : ℕ) (τ : ℝ) : Measurable (fun x : X3 => Psi ν F hij k τ x) := by
  have h1 := measurable_Phi ν F hij hmeas k τ
  have h0 := measurable_Phi ν F hij hmeas k 0
  have h : Measurable ((fun x : X3 => Phi ν F hij k τ x) - (fun x : X3 => Phi ν F hij k 0 x)) :=
    h1.sub h0
  rwa [show (fun x : X3 => Psi ν F hij k τ x)
      = (fun x : X3 => Phi ν F hij k τ x) - (fun x : X3 => Phi ν F hij k 0 x) from by
        funext x; rfl]

theorem continuous_Phi (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    {i j : Fin 3} (hij : i ≠ j) (k : ℕ) (x : X3)
    (hν : IsFiniteMeasureOnCompacts (ν x)) :
    Continuous (fun τ : ℝ => Phi ν F hij k τ x) := by
  haveI := hν
  simpa [Phi] using continuous_integral_translate_uij (ν x) (F k) hij

theorem continuous_Psi (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    {i j : Fin 3} (hij : i ≠ j) (k : ℕ) (x : X3)
    (hν : IsFiniteMeasureOnCompacts (ν x)) :
    Continuous (fun τ : ℝ => Psi ν F hij k τ x) := by
  have h1 := continuous_Phi ν F hij k x hν
  have h0 : Continuous (fun _ : ℝ => Phi ν F hij k 0 x) := continuous_const
  have h : Continuous ((fun τ : ℝ => Phi ν F hij k τ x) - (fun _ : ℝ => Phi ν F hij k 0 x)) :=
    h1.sub h0
  rwa [show (fun τ : ℝ => Psi ν F hij k τ x)
      = (fun τ : ℝ => Phi ν F hij k τ x) - (fun _ : ℝ => Phi ν F hij k 0 x) from by
        funext x; rfl]

/-! ## Period set = vanishing of the countable family `ψ` -/

/-- **Determination of a measure by the integrals against `F`, for measures carried by `U_ij`.**
Under the hypothesis `hF` of the main theorem, `τ` is a period of `ν x` iff all the translated
test integrals agree with the original ones. -/
theorem perSet_iff_forall_integral {i j : Fin 3} (hij : i ≠ j)
    (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    (hF : ∀ ν₁ ν₂ : Measure SL3,
        IsFiniteMeasureOnCompacts ν₁ → IsFiniteMeasureOnCompacts ν₂ →
        ν₁ (Set.range (fun t : ℝ => uij hij t))ᶜ = 0 →
        ν₂ (Set.range (fun t : ℝ => uij hij t))ᶜ = 0 →
        (∀ k, ∫ g, F k g ∂ν₁ = ∫ g, F k g ∂ν₂) → ν₁ = ν₂)
    {x : X3} (hradon : IsFiniteMeasureOnCompacts (ν x))
    (hcar : ν x (Set.range (fun t : ℝ => uij hij t))ᶜ = 0) (τ : ℝ) :
    τ ∈ PerSet ν i j hij x ↔
      ∀ k, ∫ g, F k (g * uij hij τ) ∂(ν x) = ∫ g, F k g ∂(ν x) := by
  constructor
  · intro hτ k
    have h := congrArg (fun (m : Measure SL3) => ∫ g, F k g ∂m) hτ
    have h1 : ∫ g, F k g ∂((ν x).map (fun g : SL3 => g * uij hij τ))
        = ∫ g, F k (g * uij hij τ) ∂(ν x) :=
      integral_map (μ := ν x) (Work.EKLC7.measurable_mulRight_uij hij τ).aemeasurable
        (F k).continuous.aestronglyMeasurable
    exact h1.symm.trans h
  · intro h
    haveI : IsFiniteMeasureOnCompacts (ν x) := hradon
    haveI : IsLocallyFiniteMeasure (ν x) := inferInstance
    haveI : (ν x).Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure (ν x)
    haveI : ((ν x).map (fun g : SL3 => g * uij hij τ)).Regular :=
      Measure.Regular.map (μ := ν x) (Homeomorph.mulRight (uij hij τ))
    have hμ : IsFiniteMeasureOnCompacts ((ν x).map (fun g : SL3 => g * uij hij τ)) :=
      inferInstance
    have hcarμ : ((ν x).map (fun g : SL3 => g * uij hij τ))
        (Set.range (fun t : ℝ => uij hij t))ᶜ = 0 :=
      map_mulRight_uij_compl_range hij (ν x) hcar τ
    have hint : ∀ k, ∫ g, F k g ∂(ν x)
        = ∫ g, F k g ∂((ν x).map (fun g : SL3 => g * uij hij τ)) := by
      intro k
      have h1 : ∫ g, F k g ∂((ν x).map (fun g : SL3 => g * uij hij τ))
          = ∫ g, F k (g * uij hij τ) ∂(ν x) :=
        integral_map (μ := ν x) (Work.EKLC7.measurable_mulRight_uij hij τ).aemeasurable
          (F k).continuous.aestronglyMeasurable
      exact (h1.trans (h k)).symm
    exact (hF (ν x) ((ν x).map (fun g : SL3 => g * uij hij τ))
      hradon hμ hcar hcarμ hint).symm

/-- The period-set condition reformulated via the vanishing of `ψ`. -/
theorem perSet_iff_psi {i j : Fin 3} (hij : i ≠ j)
    (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    (hF : ∀ ν₁ ν₂ : Measure SL3,
        IsFiniteMeasureOnCompacts ν₁ → IsFiniteMeasureOnCompacts ν₂ →
        ν₁ (Set.range (fun t : ℝ => uij hij t))ᶜ = 0 →
        ν₂ (Set.range (fun t : ℝ => uij hij t))ᶜ = 0 →
        (∀ k, ∫ g, F k g ∂ν₁ = ∫ g, F k g ∂ν₂) → ν₁ = ν₂)
    {x : X3} (hradon : IsFiniteMeasureOnCompacts (ν x))
    (hcar : ν x (Set.range (fun t : ℝ => uij hij t))ᶜ = 0) (τ : ℝ) :
    τ ∈ PerSet ν i j hij x ↔ ∀ k, Psi ν F hij k τ x = 0 := by
  rw [perSet_iff_forall_integral hij ν F hF hradon hcar τ]
  constructor
  · intro h k
    have hk := h k
    rw [Psi, Phi_apply, Phi_zero]
    exact sub_eq_zero.mpr hk
  · intro h k
    have hk := h k
    rw [Psi, Phi_apply, Phi_zero] at hk
    exact sub_eq_zero.mp hk

/-! ## Partial sums of squares -/

/-- The partial sum of squares `∑_{k ≤ m} ψ k τ x ²`. -/
def Ssq (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    {i j : Fin 3} (hij : i ≠ j) (m : ℕ) (τ : ℝ) (x : X3) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), (Psi ν F hij k τ x) ^ 2

theorem Ssq_nonneg (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    {i j : Fin 3} (hij : i ≠ j) (m : ℕ) (τ : ℝ) (x : X3) :
    0 ≤ Ssq ν F hij m τ x := by
  unfold Ssq
  exact Finset.sum_nonneg (fun k _ => sq_nonneg _)

theorem Ssq_eq_zero_iff (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    {i j : Fin 3} (hij : i ≠ j) (m : ℕ) (τ : ℝ) (x : X3) :
    Ssq ν F hij m τ x = 0 ↔ ∀ k ∈ Finset.range (m + 1), Psi ν F hij k τ x = 0 := by
  unfold Ssq
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg _)]
  constructor
  · intro h k hk
    have h2 : Psi ν F hij k τ x * Psi ν F hij k τ x = 0 := by
      simpa only [pow_two] using h k hk
    exact mul_self_eq_zero.mp h2
  · intro h k hk
    rw [h k hk]; ring

theorem measurable_Ssq (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    {i j : Fin 3} (hij : i ≠ j)
    (hmeas : ∀ f : CompactlySupportedContinuousMap SL3 ℝ, Measurable (fun x => ∫ g, f g ∂(ν x)))
    (m : ℕ) (τ : ℝ) : Measurable (fun x : X3 => Ssq ν F hij m τ x) := by
  unfold Ssq
  refine Finset.measurable_sum (Finset.range (m + 1)) fun k _ => ?_
  exact (measurable_Psi ν F hij hmeas k τ).pow_const 2

theorem continuous_Ssq (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    {i j : Fin 3} (hij : i ≠ j) (m : ℕ) (x : X3)
    (hν : IsFiniteMeasureOnCompacts (ν x)) :
    Continuous (fun τ : ℝ => Ssq ν F hij m τ x) := by
  unfold Ssq
  refine continuous_finset_sum (Finset.range (m + 1)) fun k _ => ?_
  exact (continuous_Psi ν F hij k x hν).pow 2

/-! ## The measurable `⨅` over rationals in `[a,b]` -/

/-- `Cfun ν F hij a b m x = ⨅_{q ∈ ℚ∩[a,b]} ∑_{k ≤ m} ψ k q x ²`. -/
def Cfun (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    {i j : Fin 3} (hij : i ≠ j) (a b : ℚ) (m : ℕ) (x : X3) : ℝ :=
  ⨅ (q : {q : ℚ // (a : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ (b : ℝ)}), Ssq ν F hij m (q : ℝ) x

theorem measurable_Cfun (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    {i j : Fin 3} (hij : i ≠ j)
    (hmeas : ∀ f : CompactlySupportedContinuousMap SL3 ℝ, Measurable (fun x => ∫ g, f g ∂(ν x)))
    (a b : ℚ) (m : ℕ) : Measurable (Cfun ν F hij a b m) := by
  unfold Cfun
  refine Measurable.iInf fun q => ?_
  exact measurable_Ssq ν F hij hmeas m (q : ℝ)

/-! ## The two directions of the main equivalence -/

/-- If `Cfun … m x = 0` for every `m` then the period set of `ν x` meets `[a,b]`. -/
theorem nonempty_of_forall_Cfun_eq_zero {i j : Fin 3} (hij : i ≠ j)
    (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    (hF : ∀ ν₁ ν₂ : Measure SL3,
        IsFiniteMeasureOnCompacts ν₁ → IsFiniteMeasureOnCompacts ν₂ →
        ν₁ (Set.range (fun t : ℝ => uij hij t))ᶜ = 0 →
        ν₂ (Set.range (fun t : ℝ => uij hij t))ᶜ = 0 →
        (∀ k, ∫ g, F k g ∂ν₁ = ∫ g, F k g ∂ν₂) → ν₁ = ν₂)
    {a b : ℚ} (hab : (a : ℝ) ≤ (b : ℝ)) {x : X3}
    (hradon : IsFiniteMeasureOnCompacts (ν x))
    (hcar : ν x (Set.range (fun t : ℝ => uij hij t))ᶜ = 0)
    (h : ∀ m, Cfun ν F hij a b m x = 0) :
    ∃ τ ∈ Set.Icc (a : ℝ) (b : ℝ), τ ∈ PerSet ν i j hij x := by
  have hnonempty : ∀ m, ∃ τ ∈ Set.Icc (a : ℝ) (b : ℝ),
      ∀ k, k ≤ m → Psi ν F hij k τ x = 0 := by
    intro m
    have hf : Continuous (fun τ : ℝ => Ssq ν F hij m τ x) := continuous_Ssq ν F hij m x hradon
    have h0 : ∀ τ, 0 ≤ Ssq ν F hij m τ x := fun τ => Ssq_nonneg ν F hij m τ x
    have hc0 : (⨅ (q : {q : ℚ // (a : ℝ) ≤ (q : ℝ) ∧ (q : ℝ) ≤ (b : ℝ)}),
        Ssq ν F hij m (q : ℝ) x) = 0 := h m
    obtain ⟨τ, hτ, hτ0⟩ :=
      (ciInf_rat_eq_zero_iff hab (fun τ => Ssq ν F hij m τ x) hf h0).mp hc0
    exact ⟨τ, hτ, fun k hk => (Ssq_eq_zero_iff ν F hij m τ x).mp hτ0 k
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))⟩
  have htd : ∀ m, {τ : ℝ | τ ∈ Set.Icc (a : ℝ) (b : ℝ) ∧ ∀ k, k ≤ m + 1 → Psi ν F hij k τ x = 0}
      ⊆ {τ : ℝ | τ ∈ Set.Icc (a : ℝ) (b : ℝ) ∧ ∀ k, k ≤ m → Psi ν F hij k τ x = 0} := by
    intro m τ hτ
    exact ⟨hτ.1, fun k hk => hτ.2 k (le_trans hk (Nat.le_succ m))⟩
  have hclosed : ∀ m, IsClosed
      {τ : ℝ | τ ∈ Set.Icc (a : ℝ) (b : ℝ) ∧ ∀ k, k ≤ m → Psi ν F hij k τ x = 0} := by
    intro m
    have heq : {τ : ℝ | τ ∈ Set.Icc (a : ℝ) (b : ℝ) ∧ ∀ k, k ≤ m → Psi ν F hij k τ x = 0}
        = Set.Icc (a : ℝ) (b : ℝ) ∩
          (⋂ (k : {k : ℕ // k ≤ m}), {τ : ℝ | Psi ν F hij k.1 τ x = 0}) := by
      ext τ
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun k => h2 k.1 k.2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, fun k hk => h2 ⟨k, hk⟩⟩
    rw [heq]
    exact isClosed_Icc.inter
      (isClosed_iInter fun k =>
        IsClosed.preimage (continuous_Psi ν F hij k.1 x hradon) isClosed_singleton)
  have hne : ∀ m, ({τ : ℝ | τ ∈ Set.Icc (a : ℝ) (b : ℝ) ∧
      ∀ k, k ≤ m → Psi ν F hij k τ x = 0} : Set ℝ).Nonempty := by
    intro m
    obtain ⟨τ, hτ, hτ2⟩ := hnonempty m
    exact ⟨τ, hτ, hτ2⟩
  have hcomp0 : IsCompact ({τ : ℝ | τ ∈ Set.Icc (a : ℝ) (b : ℝ) ∧
      ∀ k, k ≤ 0 → Psi ν F hij k τ x = 0} : Set ℝ) :=
    IsCompact.of_isClosed_subset isCompact_Icc (hclosed 0) (fun τ hτ => hτ.1)
  have hinter : (⋂ m, {τ : ℝ | τ ∈ Set.Icc (a : ℝ) (b : ℝ) ∧
      ∀ k, k ≤ m → Psi ν F hij k τ x = 0}).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun m => {τ : ℝ | τ ∈ Set.Icc (a : ℝ) (b : ℝ) ∧ ∀ k, k ≤ m → Psi ν F hij k τ x = 0})
      htd hne hcomp0 hclosed
  obtain ⟨τ, hτ⟩ := hinter
  have hτIcc : τ ∈ Set.Icc (a : ℝ) (b : ℝ) := (Set.mem_iInter.mp hτ 0).1
  have hτall : ∀ k, Psi ν F hij k τ x = 0 := fun k => (Set.mem_iInter.mp hτ k).2 k le_rfl
  exact ⟨τ, hτIcc, (perSet_iff_psi hij ν F hF hradon hcar τ).mpr hτall⟩

/-- Conversely, if the period set of `ν x` meets `[a,b]` then `Cfun … m x = 0` for every `m`. -/
theorem forall_Cfun_eq_zero_of_exists {i j : Fin 3} (hij : i ≠ j)
    (ν : X3 → Measure SL3) (F : ℕ → CompactlySupportedContinuousMap SL3 ℝ)
    (hF : ∀ ν₁ ν₂ : Measure SL3,
        IsFiniteMeasureOnCompacts ν₁ → IsFiniteMeasureOnCompacts ν₂ →
        ν₁ (Set.range (fun t : ℝ => uij hij t))ᶜ = 0 →
        ν₂ (Set.range (fun t : ℝ => uij hij t))ᶜ = 0 →
        (∀ k, ∫ g, F k g ∂ν₁ = ∫ g, F k g ∂ν₂) → ν₁ = ν₂)
    {a b : ℚ} (hab : (a : ℝ) ≤ (b : ℝ)) {x : X3}
    (hradon : IsFiniteMeasureOnCompacts (ν x))
    (hcar : ν x (Set.range (fun t : ℝ => uij hij t))ᶜ = 0)
    (h : ∃ τ ∈ Set.Icc (a : ℝ) (b : ℝ), τ ∈ PerSet ν i j hij x) :
    ∀ m, Cfun ν F hij a b m x = 0 := by
  obtain ⟨τ, hτ, hper⟩ := h
  have hall : ∀ k, Psi ν F hij k τ x = 0 :=
    (perSet_iff_psi hij ν F hF hradon hcar τ).mp hper
  intro m
  have hf : Continuous (fun τ : ℝ => Ssq ν F hij m τ x) := continuous_Ssq ν F hij m x hradon
  have h0 : ∀ τ, 0 ≤ Ssq ν F hij m τ x := fun τ => Ssq_nonneg ν F hij m τ x
  refine (ciInf_rat_eq_zero_iff hab (fun τ => Ssq ν F hij m τ x) hf h0).mpr ⟨τ, hτ, ?_⟩
  rw [Ssq_eq_zero_iff]
  intro k _
  exact hall k

/-! ## The main theorem -/

theorem measurableSet_exists_perSet_Icc
    {i j : Fin 3} (hij : i ≠ j) (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    (X' : Set Work.EKLContract.X3) (hX' : MeasurableSet X')
    (hradon : ∀ x ∈ X', MeasureTheory.IsFiniteMeasureOnCompacts (ν x))
    (hcar : ∀ x ∈ X', ν x (Set.range (fun t : ℝ => Work.EKLContract.uij hij t))ᶜ = 0)
    (hmeas : ∀ f : CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ,
      Measurable (fun x => ∫ g, f g ∂(ν x)))
    (F : ℕ → CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ)
    (hF : ∀ ν₁ ν₂ : MeasureTheory.Measure Work.EKLContract.SL3,
        MeasureTheory.IsFiniteMeasureOnCompacts ν₁ →
        MeasureTheory.IsFiniteMeasureOnCompacts ν₂ →
        ν₁ (Set.range (fun t : ℝ => Work.EKLContract.uij hij t))ᶜ = 0 →
        ν₂ (Set.range (fun t : ℝ => Work.EKLContract.uij hij t))ᶜ = 0 →
        (∀ k, ∫ g, F k g ∂ν₁ = ∫ g, F k g ∂ν₂) → ν₁ = ν₂)
    {a b : ℚ} (ha : 0 < a) :
    MeasurableSet {x | x ∈ X' ∧ ∃ τ ∈ Set.Icc (a : ℝ) (b : ℝ),
      τ ∈ Work.EKLRelCross.PerSet ν i j hij x} := by
  classical
  rcases le_or_gt (a : ℝ) (b : ℝ) with hab | hba
  · have hkey : ∀ x ∈ X', (∃ τ ∈ Set.Icc (a : ℝ) (b : ℝ), τ ∈ PerSet ν i j hij x) ↔
        ∀ m, Cfun ν F hij a b m x = 0 := fun x hx =>
      ⟨fun h => forall_Cfun_eq_zero_of_exists hij ν F hF hab (hradon x hx) (hcar x hx) h,
       fun h => nonempty_of_forall_Cfun_eq_zero hij ν F hF hab (hradon x hx) (hcar x hx) h⟩
    have hset : {x | x ∈ X' ∧ ∃ τ ∈ Set.Icc (a : ℝ) (b : ℝ),
          τ ∈ PerSet ν i j hij x}
        = X' ∩ ⋂ m, {x : X3 | Cfun ν F hij a b m x = 0} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨hx, h⟩; exact ⟨hx, fun m => (hkey x hx).mp h m⟩
      · rintro ⟨hx, h⟩; exact ⟨hx, (hkey x hx).mpr h⟩
    rw [hset]
    refine hX'.inter (MeasurableSet.iInter fun m => ?_)
    have hmeq : {x : X3 | Cfun ν F hij a b m x = 0} = (Cfun ν F hij a b m) ⁻¹' ({0} : Set ℝ) := by
      ext x; simp
    rw [hmeq]
    exact measurable_Cfun ν F hij hmeas a b m (measurableSet_singleton (0 : ℝ))
  · have hempty : Set.Icc (a : ℝ) (b : ℝ) = ∅ := Set.Icc_eq_empty_of_lt hba
    have hset : {x | x ∈ X' ∧ ∃ τ ∈ Set.Icc (a : ℝ) (b : ℝ),
          τ ∈ PerSet ν i j hij x} = ∅ := by
      ext x
      simp [hempty]
    rw [hset]
    exact MeasurableSet.empty

end

end Work.EKLRelCross
