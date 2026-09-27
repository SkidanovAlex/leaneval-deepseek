import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.Covariant
import Submission.Work.EKLC6Core.conjBox_nhds
import Submission.Work.EKLC6Core.box_iUnion_conjBox_neg
import Submission.Work.EKLC6Core.box_iInter_conjBox
import Submission.Work.EKLC6Core.box_conjBox_subset
import Submission.Work.EKLContract.Interfaces

/-!
# `EKLC6Core.box_facts` — the elementary geometry of the boxes `conjBox U (n t)`

Let `U ≤ SL₃(ℝ)` be a horospherical subgroup (`IsHoro U`: closed, normalised by the diagonal
flow, contracted by some `aDiag t₀`) and let `t : Fin 3 → ℝ` be an exponent vector that contracts
*all* of `U`:

`aDiag tⁿ · u · (aDiag tⁿ)⁻¹ → 1`   for every `u ∈ U`   (`hcontr`).

The conjugated boxes `conjBox U s = aDiag s · B₁^U · (aDiag s)⁻¹` then satisfy the four
elementary facts that the entropy computation of Pisa §7 takes for granted:

1. `conjBox U t ⊆ B₁^U` — the *contracted* box sits inside the normalising box;
2. `n ↦ conjBox U (-n t)` is monotone (the "big boxes" grow) and
3. `n ↦ conjBox U (n t)` is antitone (the "small boxes" shrink);
4. `⋃ₙ conjBox U (-n t) = U` and `⋂ₙ conjBox U (n t) = {1}`.

The mathematical content is the entry pattern forced by the contraction hypothesis: for
`u ∈ U` and `i ≠ j`,

`(aDiag tⁿ u aDiag(-n t))ᵢⱼ = e^{n (tᵢ - tⱼ)} uᵢⱼ → δᵢⱼ`,

so `uᵢⱼ = 0` whenever `tᵢ ≥ tⱼ` — the entries of `U` are supported on the directions contracted
by `t`. Feeding that back into the entry formula of conjugation by a single `aDiag t` gives both
inclusions of (1); (2) and (3) are then formal consequences of (1), and (4) is the two-sided
limit statement (`hcontr` says the small boxes shrink to the identity, hence the big boxes exhaust
`U`).

The individual pieces are proved in the sibling modules
`box_conjBox_subset`, `box_iUnion_conjBox_neg` and `box_iInter_conjBox`; this module proves the
entry pattern and assembles the five conjuncts.
-/

open Filter Topology
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## The entry pattern forced by the contraction hypothesis -/

/-- Entries of an element of `SL₃(ℝ)` are continuous functions of the element. -/
theorem box_facts_continuous_entry (i j : Fin 3) :
    Continuous fun g : SL3 => (g : Matrix (Fin 3) (Fin 3) ℝ) i j :=
  (continuous_apply j).comp (Matrix.SpecialLinearGroup.continuous_apply _ continuous_id i)

/-- The `(i,j)`-entry of the conjugates of `u` by the powers of `aDiag t` tends to the `(i,j)`
entry of the identity. -/
theorem box_facts_entry_tendsto {U : Subgroup SL3} {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (nhds 1))
    {u : SL3} (hu : u ∈ U) (i j : Fin 3) :
    Tendsto (fun n : ℕ => (aDiag t ^ n * u * (aDiag t ^ n)⁻¹) i j) atTop
      (nhds ((1 : SL3) i j)) :=
  ((box_facts_continuous_entry i j).tendsto 1).comp (hcontr u hu)

/-- **The entry pattern.**  If `t` contracts `U` (`hcontr`) then every `u ∈ U` has identity
entries in the directions that are *not* strictly contracted by `t`: `u i j = δ i j` whenever
`t j ≤ t i`. -/
theorem box_facts_entry_eq_one {U : Subgroup SL3} {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (nhds 1))
    {u : SL3} (hu : u ∈ U) {i j : Fin 3} (hij : t j ≤ t i) :
    u i j = (1 : SL3) i j := by
  have hseries : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (t i - t j)) * u i j) atTop
      (nhds ((1 : SL3) i j)) := by
    refine (box_facts_entry_tendsto hcontr hu i j).congr' ?_
    filter_upwards with n
    rw [boxi_conj_pow_apply]
  rcases eq_or_ne i j with rfl | hij'
  · -- diagonal entry: the sequence is constant, with limit `1`
    have hdiag : ((1 : SL3) i i) = 1 := Matrix.one_apply_eq i
    rw [hdiag] at hseries
    have hconst : Tendsto (fun _ : ℕ => u i i) atTop (nhds 1) := by
      refine hseries.congr' ?_
      filter_upwards with n
      rw [sub_self, mul_zero, Real.exp_zero, one_mul]
    rw [hdiag]
    exact tendsto_nhds_unique tendsto_const_nhds hconst
  · -- off-diagonal entry: the limit is `0` and the exponential factor is bounded below by `1`
    have hoff : ((1 : SL3) i j) = 0 := Matrix.one_apply_ne hij'
    have h0 : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (t i - t j)) * u i j) atTop (nhds 0) := by
      rw [hoff] at hseries
      exact hseries
    have hzero := boxi_eq_zero_of_tendsto_exp_mul (sub_nonneg.mpr hij) h0
    rw [hzero, hoff]

/-! ## Monotonicity of the two families of boxes -/

/-- Conjugation by `aDiag s` is monotone on sets. -/
theorem conjBy_mono (s : Fin 3 → ℝ) {A B : Set SL3} (h : A ⊆ B) : conjBy s A ⊆ conjBy s B :=
  Set.image_mono h

/-- **The big boxes grow.**  `n ↦ conjBox U (-n t)` is monotone. -/
theorem box_facts_monotone {U : Subgroup SL3} (hU : IsHoro U) {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (nhds 1)) :
    Monotone (fun n : ℕ => conjBox U (-(((n : ℝ)) • t))) := by
  have hstep : Box1 U ⊆ conjBox U (-t) := (box_conjBox_subset hU hcontr).2
  apply monotone_nat_of_le_succ
  intro n
  have hvec : -((((n + 1 : ℕ) : ℝ)) • t) = -((n : ℝ) • t) + (-t) := by
    ext i
    simp only [Pi.neg_apply, Pi.add_apply, Pi.smul_apply]
    push_cast
    ring
  calc conjBox U (-(((n : ℝ)) • t))
      = conjBy (-((n : ℝ) • t)) (Box1 U) := rfl
    _ ⊆ conjBy (-((n : ℝ) • t)) (conjBox U (-t)) := conjBy_mono _ hstep
    _ = conjBox U (-((n : ℝ) • t) + (-t)) :=
        (conjBox_add U (-((n : ℝ) • t)) (-t)).symm
    _ = conjBox U (-((((n + 1 : ℕ) : ℝ)) • t)) := by rw [hvec]

/-- **The small boxes shrink.**  `n ↦ conjBox U (n t)` is antitone. -/
theorem box_facts_antitone {U : Subgroup SL3} (hU : IsHoro U) {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Tendsto
      (fun n : ℕ => aDiag t ^ n * u * (aDiag t ^ n)⁻¹) atTop (nhds 1)) :
    Antitone (fun n : ℕ => conjBox U (((n : ℝ)) • t)) := by
  have hsub : conjBox U t ⊆ Box1 U := (box_conjBox_subset hU hcontr).1
  apply antitone_nat_of_succ_le
  intro n
  have hvec : ((((n + 1 : ℕ) : ℝ)) • t) = (n : ℝ) • t + t := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply]
    push_cast
    ring
  calc conjBox U ((((n + 1 : ℕ) : ℝ)) • t)
      = conjBy ((n : ℝ) • t) (conjBox U t) := by rw [hvec, conjBox_add]
    _ ⊆ conjBy ((n : ℝ) • t) (Box1 U) := conjBy_mono _ hsub
    _ = conjBox U (((n : ℝ)) • t) := rfl

/-! ## The five facts -/

theorem box_facts {U : Subgroup Work.EKLContract.SL3} (hU : Work.EKLContract.IsHoro U)
    {t : Fin 3 → ℝ}
    (hcontr : ∀ u ∈ U, Filter.Tendsto
      (fun n : ℕ => Work.EKLContract.aDiag t ^ n * u * (Work.EKLContract.aDiag t ^ n)⁻¹)
      Filter.atTop (nhds 1)) :
    (Work.EKLC6Core.conjBox U t ⊆ Work.EKLContract.Box1 U) ∧
    Monotone (fun n : ℕ => Work.EKLC6Core.conjBox U (-(((n : ℝ)) • t))) ∧
    Antitone (fun n : ℕ => Work.EKLC6Core.conjBox U (((n : ℝ)) • t)) ∧
    (⋃ n : ℕ, Work.EKLC6Core.conjBox U (-(((n : ℝ)) • t))) = U ∧
    (⋂ n : ℕ, Work.EKLC6Core.conjBox U (((n : ℝ)) • t)) = {1} :=
  ⟨(box_conjBox_subset hU hcontr).1,
   box_facts_monotone hU hcontr,
   box_facts_antitone hU hcontr,
   box_iUnion_conjBox_neg hU hcontr,
   box_iInter_conjBox hU hcontr⟩

end Work.EKLC6Core
