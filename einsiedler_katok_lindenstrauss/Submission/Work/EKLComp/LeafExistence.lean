import Mathlib
import Submission.Work.EKLC7.LeafwiseHoro
import Submission.Work.EKLC7.FlowerFamExists
import Submission.Work.EKLComp.plaque_propor

/-!
# Leafwise measures: the existence half under a.e. freeness

The frozen contract `Work.EKLContract.P_Leafwise` asks for the existence of a system of leafwise
measures for a probability measure `μ` under the hypothesis that **one** `α^{t₀}` preserves `μ`
and contracts `U` — not under full `A`-invariance.  The existing existence theorem
`Work.EKLC7.LeafwiseHoro` (Pisa Theorem 6.3) is stated for `A`-invariant `μ`.

This file removes that hypothesis: the whole construction of `Submission.Work.EKLC7.LeafNu*`
uses `A`-invariance only through the a.e. freeness of the `U`-orbits
(`Work.EKLC7.AeFreeStab`, Pisa 7.12), which the frozen hypotheses supply directly as
`∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1` (`Work.EKLComp.ae_freeness`).  Replacing that input, the
flower family and the conull "good set" are rebuilt here; the remaining seven fields, the
measurable leaf coordinate and the `equivariant` field are taken verbatim from `Work.EKLC7`.

Main result: `Work.EKLComp.leafwise_exists_of_free`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLComp

open Work.EKLContract Work.EKLC7

variable {U : Subgroup SL3} {μ : Measure X3}

/-! ## The flower family from a.e. freeness

The proof is the assembly of `Work.EKLC7.FlowerFam_of_localFlowerFam`, with the a.e.-freeness
input `ae_free_orbit_of_horo μ hA U hU` replaced by a hypothesis. -/

/-- **The flower family with unbounded radii exists, given a.e. freeness of the `U`-orbits.**
(Adapted from `Work.EKLC7.FlowerFam_of_localFlowerFam`; only the a.e.-freeness input changes.) -/
theorem FlowerFam_of_free (U : Subgroup SL3) (hU : IsHoro U)
    (μ : Measure X3) [IsProbabilityMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1) : Work.EKLC7.FlowerFamP U μ := by
  classical
  have hpos : ∀ᵐ x ∂μ, ∀ s : Set X3, IsOpen s → x ∈ s → 0 < μ s := ae_isOpen_pos (μ := μ)
  have hfam : ∀ k : ℕ, ∃ (E Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3),
      (∀ n, MeasurableSet (E n)) ∧ (∀ n, BigPlaqueOn U ((k : ℝ) + 1) (E n) (Z n) (m n)) ∧
      μ (⋃ n, E n)ᶜ = 0 := by
    intro k
    exact flowersAtRadius U (localFlowerFam_exists U hU) μ hfree hpos ((k : ℝ) + 1)
      (by positivity)
  choose E Z m hEmeas hbig hcov using hfam
  refine ⟨{ R := fun j => ((Nat.unpair j).1 : ℝ) + 1
            E := fun j => E (Nat.unpair j).1 (Nat.unpair j).2
            Z := fun j => Z (Nat.unpair j).1 (Nat.unpair j).2
            m := fun j => m (Nat.unpair j).1 (Nat.unpair j).2
            one_le := ?_
            measE := ?_
            big := ?_
            cover := ?_ }⟩
  · intro j
    have : (0 : ℝ) ≤ ((Nat.unpair j).1 : ℝ) := Nat.cast_nonneg _
    linarith
  · intro j
    exact hEmeas _ _
  · intro j
    exact hbig _ _
  · intro ρ hρ
    obtain ⟨k, hk⟩ := exists_nat_ge ρ
    have hk1 : ρ ≤ ((k : ℝ) + 1) := by linarith
    have h0 : ∀ᵐ x ∂μ, x ∈ ⋃ n, E k n := by
      rw [MeasureTheory.ae_iff]
      simpa [Set.compl_def] using hcov k
    filter_upwards [h0] with x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    refine ⟨Nat.pair k n, ?_, ?_⟩
    · show ρ ≤ ((Nat.unpair (Nat.pair k n)).1 : ℝ) + 1
      rw [Nat.unpair_pair]
      exact hk1
    · show x ∈ E (Nat.unpair (Nat.pair k n)).1 (Nat.unpair (Nat.pair k n)).2
      rw [Nat.unpair_pair]
      simpa using hn

/-! ## The conull good set from a.e. freeness

Adapted from `Work.EKLC7.FlowerFam.exists_good`: the five a.e. inputs are consumed exactly as
there, with `AeFreeStab μ hA U hU` replaced by the hypothesis. -/

/-- **The a.e. assembly**: the good set of a flower family is conull, given a.e. freeness.
(Adapted from `Work.EKLC7.FlowerFam.exists_good`.) -/
theorem exists_good_of_free (F : Work.EKLC7.FlowerFam U μ) [IsProbabilityMeasure μ]
    (hU : IsHoro U)
    (hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1)
    (hprop : Work.EKLC7.FlowerFam.ProporHyp U μ) : ∃ X', F.Good X' := by
  classical
  -- (1) the free-orbit condition
  have h1 : μ {x : X3 | ¬ (∀ u ∈ U, u • x = x → u = 1)} = 0 := by
    have h := hfree
    rwa [MeasureTheory.ae_iff] at h
  -- (2) the covering condition of the flowers
  have h2 : μ {x : X3 | ¬ (∀ n : ℕ, ∃ j, (n : ℝ) + 2 ≤ F.R j ∧ x ∈ F.E j)} = 0 := by
    have hstep : ∀ n : ℕ, μ {x : X3 | ¬ (∃ j, (n : ℝ) + 2 ≤ F.R j ∧ x ∈ F.E j)} = 0 := by
      intro n
      have h := F.cover ((n : ℝ) + 2) (by positivity)
      rwa [MeasureTheory.ae_iff] at h
    have hset : {x : X3 | ¬ (∀ n : ℕ, ∃ j, (n : ℝ) + 2 ≤ F.R j ∧ x ∈ F.E j)}
        = ⋃ (n : ℕ), {x : X3 | ¬ (∃ j, (n : ℝ) + 2 ≤ F.R j ∧ x ∈ F.E j)} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
      exact not_forall
    rw [hset]
    exact MeasureTheory.measure_iUnion_null hstep
  -- (3) the conditional measures are probability measures on their atoms
  have h3 : μ (⋃ j : ℕ, {x : X3 | x ∈ F.Z j ∧ F.kappa j x (atom (F.m j) x) ≠ 1}) = 0 := by
    refine MeasureTheory.measure_iUnion_null fun j => ?_
    have h : ∀ᵐ x ∂(μ.restrict (F.Z j)), F.kappa j x (atom (F.m j) x) = 1 :=
      Work.EKLComp.condExpKernel_atom ⟨F.m j⟩ (F.big j).1.1 (F.big j).1.2.1 (μ.restrict (F.Z j))
    have h' : ∀ᵐ x ∂μ, x ∈ F.Z j → F.kappa j x (atom (F.m j) x) = 1 :=
      (MeasureTheory.ae_restrict_iff' (F.zmeas j)).mp h
    have h'' : μ {x : X3 | ¬ (x ∈ F.Z j → F.kappa j x (atom (F.m j) x) = 1)} = 0 :=
      MeasureTheory.ae_iff.mp h'
    refine measure_mono_null ?_ h''
    intro x hx h
    exact hx.2 (h hx.1)
  -- (4) positivity of the normalising constants
  have h4 : μ (⋃ j : ℕ, ⋃ q : ℚ, {x : X3 | x ∈ F.Z j ∧
      ¬ (0 < F.kappa j x ((fun g : SL3 => g • x) '' (Uball U (q : ℝ)))) ∧ 0 < (q : ℝ)}) = 0 := by
    refine MeasureTheory.measure_iUnion_null fun j => ?_
    refine MeasureTheory.measure_iUnion_null fun q => ?_
    by_cases hq : 0 < (q : ℝ)
    · have h := Work.EKLComp.condExpKernel_pos U hU.1 (F.Z j) ⟨F.m j⟩ (F.big j).1 μ
        (UballOpen (q : ℝ)) (isOpen_UballOpen _) (one_mem_UballOpen hq)
      have hset : UballOpen (q : ℝ) ∩ (U : Set SL3) = Uball U (q : ℝ) := by
        rw [Set.inter_comm, ← Uball_eq_inter]
      rw [hset] at h
      have h' : ∀ᵐ x ∂μ, x ∈ F.Z j →
          0 < F.kappa j x ((fun g : SL3 => g • x) '' Uball U (q : ℝ)) :=
        (MeasureTheory.ae_restrict_iff' (F.zmeas j)).mp h
      have h'' : μ {x : X3 | ¬ (x ∈ F.Z j →
          0 < F.kappa j x ((fun g : SL3 => g • x) '' Uball U (q : ℝ)))} = 0 :=
        MeasureTheory.ae_iff.mp h'
      refine measure_mono_null ?_ h''
      intro x hx h
      refine hx.2.1 (h hx.1)
    · refine measure_mono_null ?_ (MeasureTheory.measure_empty (μ := μ))
      intro x hx
      exact absurd hx.2.2 hq
  -- (5) proportionality of the conditional measures of two flowers
  have h5 : μ (⋃ j : ℕ, ⋃ j' : ℕ, {x : X3 | x ∈ F.Z j ∩ F.Z j' ∧
      ¬ ProporOn (F.kappa j x) (F.kappa j' x)
        (atom (F.m j) x ∩ atom (F.m j') x)}) = 0 := by
    refine MeasureTheory.measure_iUnion_null fun j => ?_
    refine MeasureTheory.measure_iUnion_null fun j' => ?_
    have hp : ∀ᵐ x ∂μ, x ∈ F.Z j ∩ F.Z j' →
        ProporOn (F.kappa j x) (F.kappa j' x) (atom (F.m j) x ∩ atom (F.m j') x) := by
      simpa only [Work.EKLC7.FlowerFam.kappa] using hprop (F.Z j) (F.Z j') ⟨F.m j⟩ ⟨F.m j'⟩
        (F.big j).1 (F.big j').1
    have hp' : μ {x : X3 | ¬ (x ∈ F.Z j ∩ F.Z j' →
        ProporOn (F.kappa j x) (F.kappa j' x) (atom (F.m j) x ∩ atom (F.m j') x))} = 0 :=
      MeasureTheory.ae_iff.mp hp
    refine measure_mono_null ?_ hp'
    intro x hx h
    exact hx.2 (h hx.1)
  -- combine
  set bad : Set X3 := ({x : X3 | ¬ (∀ u ∈ U, u • x = x → u = 1)} ∪
      {x : X3 | ¬ (∀ n : ℕ, ∃ j, (n : ℝ) + 2 ≤ F.R j ∧ x ∈ F.E j)} ∪
      (⋃ j : ℕ, {x : X3 | x ∈ F.Z j ∧ F.kappa j x (atom (F.m j) x) ≠ 1}) ∪
      (⋃ j : ℕ, ⋃ q : ℚ, {x : X3 | x ∈ F.Z j ∧
        ¬ (0 < F.kappa j x ((fun g : SL3 => g • x) '' (Uball U (q : ℝ)))) ∧ 0 < (q : ℝ)})) ∪
      (⋃ j : ℕ, ⋃ j' : ℕ, {x : X3 | x ∈ F.Z j ∩ F.Z j' ∧
        ¬ ProporOn (F.kappa j x) (F.kappa j' x)
          (atom (F.m j) x ∩ atom (F.m j') x)}) with hbad_def
  have hbad : μ bad = 0 := by
    rw [hbad_def]
    exact MeasureTheory.measure_union_null
      (MeasureTheory.measure_union_null (MeasureTheory.measure_union_null
        (MeasureTheory.measure_union_null h1 h2) h3) h4) h5
  obtain ⟨t, hsub, htmeas, htnull⟩ := MeasureTheory.exists_measurable_superset_of_null hbad
  refine ⟨tᶜ, htmeas.compl, by simpa using htnull, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx u hu hux
    by_contra hne
    refine hx (hsub ?_)
    rw [hbad_def]
    exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_left _ (fun h => hne (h u hu hux)))))
  · intro n x hx
    by_contra hcon
    refine hx (hsub ?_)
    rw [hbad_def]
    exact Set.mem_union_left _ (Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_right _ (fun h => hcon (h n)))))
  · intro j x hx hxZ
    by_contra hcon
    refine hx (hsub ?_)
    rw [hbad_def]
    exact Set.mem_union_left _ (Set.mem_union_left _
      (Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨j, ⟨hxZ, hcon⟩⟩)))
  · intro j x hx hxZ q hq
    by_contra hcon
    obtain ⟨q', hq'pos, hq'lt⟩ := exists_rat_btwn hq
    refine hx (hsub ?_)
    rw [hbad_def]
    refine Set.mem_union_left _ (Set.mem_union_right _
      (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨q', ⟨hxZ, ?_, hq'pos⟩⟩⟩))
    intro hpos
    exact hcon (lt_of_lt_of_le hpos (measure_mono (Set.image_mono (Uball_mono (le_of_lt hq'lt)))))
  · intro j j' x hx hxZ
    by_contra hcon
    refine hx (hsub ?_)
    rw [hbad_def]
    exact Set.mem_union_right _
      (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨j', ⟨hxZ, hcon⟩⟩⟩)

/-! ## Existence of a leafwise system -/

/-- **Pisa Theorem 6.3 (existence of leafwise measures), under a.e. freeness.**  For a probability
measure `μ` on `X₃` whose `U`-orbits are a.e. free and a horospherical `U` there is a system `ν`
of leafwise measures on a conull set `X'`: `Work.EKLContract.IsLeafwise μ U ν X'`.

The frozen `P_Leafwise` hypotheses (`α^{t₀}` preserves `μ` and contracts `U`) produce the a.e.
freeness by `Work.EKLComp.ae_freeness`, so this is the existence clause of the contract. -/
theorem leafwise_exists_of_free (U : Subgroup SL3) (hU : IsHoro U)
    (μ : Measure X3) [IsProbabilityMeasure μ]
    (hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1) :
    ∃ (ν : X3 → Measure SL3) (X' : Set X3), IsLeafwise μ U ν X' := by
  obtain ⟨F⟩ := FlowerFam_of_free U hU μ hfree
  have hprop : Work.EKLC7.FlowerFam.ProporHyp U μ :=
    fun Z₁ Z₂ 𝔪₁ 𝔪₂ h₁ h₂ => Work.EKLComp.plaque_propor U μ Z₁ Z₂ 𝔪₁ 𝔪₂ h₁ h₂
  obtain ⟨X', hX'⟩ := exists_good_of_free F hU hfree hprop
  obtain ⟨coord, hcoordm, hcsub⟩ := Work.EKLC7.OrbitCoord U hU.1
  refine ⟨F.nu coord X', X', Work.EKLC7.isLeafwise_nu F hU hprop coord hcoordm hcsub hX' ?_⟩
  intro x hx u hu hux
  exact Work.EKLC7.nu_equivariant F hU coord hcoordm hcsub hX' x hx u hu hux

end Work.EKLComp
