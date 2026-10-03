/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Submission.Work.FatouCoord.Main
import Submission.Work.FatouCoord.Petal.reflected_inverse_germ

/-!
# The repelling petal

For a parabolic germ `f z = z + z ^ 2 h z` (`h 0 = 1`) the repelling petal is the mirror
`PetalRep r M = - (Petal r M)` of the attracting petal, and the dynamics on it is that of the
*inverse* germ: the local inverse `finv` of `f` maps `PetalRep r M` into itself and its orbits
converge to `0`.  Hence the repelling Fatou coordinate of `f` is the attracting Fatou
coordinate of `finv`, or equivalently (up to the reflection `z ↦ -z`) the attracting Fatou
coordinate of the reflected inverse germ `u ↦ -finv(-u)`
(`Petal/reflected_inverse_germ`).

Main exports: `isRepellingPetal_petalRep` (the identification with the attracting petal of the
inverse) and `exists_repelling_petal` (existence of the repelling petal and its coordinate).
-/

open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace Work.FatouCoord

noncomputable section

variable {f finv F h ψ : ℂ → ℂ} {a : ℂ} {r A A' M : ℝ} {z : ℂ}

/-- **The repelling petal is the attracting petal of the inverse.**  If the reflected inverse
germ `F u = -finv(-u)` maps `Petal r' M` into itself with orbits converging to `0` (so that
`Petal r' M` is an attracting petal for `F`, which is what `exists_petal_fatouCoord` supplies),
then `PetalRep r' M = -Petal r' M` is a repelling petal for `f` with local inverse `finv`. -/
theorem isRepellingPetal_petalRep {f finv F : ℂ → ℂ} {r' M : ℝ} (hr' : 0 < r')
    (hF : ∀ u ∈ ball 0 r', F u = -finv (-u))
    (hmapF : MapsTo F (Petal r' M) (Petal r' M))
    (hf_finv : ∀ z ∈ ball 0 r', f (finv z) = z)
    (hconv : ∀ u ∈ Petal r' M, Tendsto (fun n : ℕ => F^[n] u) atTop (nhds 0)) :
    IsRepellingPetal f finv (PetalRep r' M) := by
  have hball : ∀ z ∈ PetalRep r' M, -z ∈ ball 0 r' := by
    intro z hz
    rw [mem_ball_zero_iff, norm_neg]
    exact (mem_PetalRep.mp hz).1
  have hpetal : ∀ z ∈ PetalRep r' M, -z ∈ Petal r' M := fun z hz =>
    (neg_mem_Petal_iff (r := r') (M := M)).mpr hz
  have hball' : ∀ z ∈ PetalRep r' M, z ∈ ball 0 r' := fun z hz => by
    rw [mem_ball_zero_iff]
    exact (mem_PetalRep.mp hz).1
  have hpetal' : ∀ u ∈ Petal r' M, -u ∈ PetalRep r' M := fun u hu =>
    (neg_mem_Petal_iff (r := r') (M := M) (z := -u)).mp (by simpa only [neg_neg] using hu)
  have hfinv_eq : ∀ z ∈ PetalRep r' M, finv z = -F (-z) := by
    intro z hz
    have h := hF (-z) (hball z hz)
    rw [h]
    simp
  have hfinv_mapsTo : MapsTo finv (PetalRep r' M) (PetalRep r' M) := fun z hz => by
    rw [hfinv_eq z hz]
    exact hpetal' _ (hmapF (hpetal z hz))
  have hiter : ∀ (z : ℂ) (hz : z ∈ PetalRep r' M) (n : ℕ),
      finv^[n] z = -F^[n] (-z) := by
    intro z hz n
    induction n with
    | zero => simp
    | succ k ih =>
      have hmem : finv^[k] z ∈ PetalRep r' M := mapsTo_iterate_of_mapsTo hfinv_mapsTo k hz
      have hmem' : -F^[k] (-z) ∈ PetalRep r' M := by rw [← ih]; exact hmem
      rw [Function.iterate_succ_apply', ih, hfinv_eq (-F^[k] (-z)) hmem', neg_neg,
        Function.iterate_succ_apply']
  refine ⟨isOpen_PetalRep, PetalRep_subset_compl_zero, hfinv_mapsTo, ?_, ?_⟩
  · intro z hz
    exact hf_finv z (hball' z hz)
  · intro z hz
    have h := (hconv (-z) (hpetal z hz)).neg
    have heq : (fun n : ℕ => finv^[n] z) = fun n : ℕ => -F^[n] (-z) := by
      funext n
      exact hiter z hz n
    rw [heq]
    simpa using h

/-- **Leau–Fatou, repelling version.**  There is a repelling petal `PetalRep r' M` for `f`
carrying a Fatou coordinate `ψ` of the inverse dynamics (`ψ ∘ finv = ψ + 1`), injective, whose
image contains the tail of every horizontal strip.  Equivalently, `-ψ` is a repelling Fatou
coordinate for `f` itself. -/
theorem exists_repelling_petal (hb : ParabolicBounds f h a r A A') :
    ∃ (finv : ℂ → ℂ) (r' M : ℝ) (ψ : ℂ → ℂ), 0 < r' ∧ 0 < M ∧
      IsRepellingPetal f finv (PetalRep r' M) ∧
      IsFatouCoordinateOn finv ψ (PetalRep r' M) ∧ Set.InjOn ψ (PetalRep r' M) ∧
      (∀ B : ℝ, ∃ C : ℝ, ∀ τ : ℂ, C < τ.re → |τ.im| ≤ B →
        ∃ z ∈ PetalRep r' M, ψ z = τ) := by
  obtain ⟨finv, F, hF, r', A'', A''', hbF, hfinv, hf_finv, hFdef⟩ :=
    Petal.reflected_inverse_germ hb
  obtain ⟨M, hM, hmapF, hconvF, hfatouF, hinjF, himgF⟩ := exists_petal_fatouCoord hbF
  refine ⟨finv, r', M, (fun z => fatouCoord F (1 - (2 - a)) (-z)), hbF.hr, hM, ?_, ?_, ?_, ?_⟩
  · exact isRepellingPetal_petalRep hbF.hr hFdef hmapF hf_finv hconvF
  · refine ⟨?_, ?_⟩
    · have hmaps : MapsTo (fun z : ℂ => -z) (PetalRep r' M) (Petal r' M) := fun z hz =>
        (neg_mem_Petal_iff (r := r') (M := M)).mpr hz
      have hneg : DifferentiableOn ℂ (fun z : ℂ => -z) (PetalRep r' M) :=
        differentiableOn_id.neg
      exact hfatouF.1.comp hneg hmaps
    · intro z hz
      have hz' : -z ∈ Petal r' M := (neg_mem_Petal_iff (r := r') (M := M)).mpr hz
      have habel : fatouCoord F (1 - (2 - a)) (F (-z)) =
          fatouCoord F (1 - (2 - a)) (-z) + 1 := hfatouF.2 _ hz'
      have hloc : finv z = -F (-z) := by
        have h := hFdef (-z) (by
          rw [mem_ball_zero_iff, norm_neg]
          exact (mem_PetalRep.mp hz).1)
        rw [h]
        simp
      show fatouCoord F (1 - (2 - a)) (-(finv z)) =
        fatouCoord F (1 - (2 - a)) (-z) + 1
      rw [hloc, neg_neg, habel]
  · intro z hz z' hz' heq
    have h1 : -z ∈ Petal r' M := (neg_mem_Petal_iff (r := r') (M := M)).mpr hz
    have h2 : -z' ∈ Petal r' M := (neg_mem_Petal_iff (r := r') (M := M)).mpr hz'
    have h3 : -z = -z' := hinjF h1 h2 heq
    simpa using h3
  · intro B
    obtain ⟨C, hC⟩ := himgF B
    refine ⟨C, ?_⟩
    intro τ hτ hτB
    obtain ⟨u, hu, hψ⟩ := hC τ hτ hτB
    refine ⟨-u, (neg_mem_Petal_iff (r := r') (M := M) (z := -u)).mp (by
      simpa only [neg_neg] using hu), ?_⟩
    simpa using hψ

end

end Work.FatouCoord
