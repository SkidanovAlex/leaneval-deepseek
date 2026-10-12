import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Submission.Work.BoseKinLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseKinLoc.Volume.volume_coverU`

FS's localisation cover: `coverU ℓ L` is the set of translation parameters `u`
whose moving box `Λ(u) = ℓu + acube ℓ` meets the one-particle box `Ω = [0,L]³`.
Its volume is `((L+ℓ)/ℓ)³ = (L+ℓ)³/ℓ³` (the audit's `((L+ℓ)/ℓ)³`).

Coordinate form (`mem_coverU_iff`): for `ℓ > 0` and `L ≥ 0`,
`u ∈ coverU ℓ L` iff `u k ∈ [−1/2, L/ℓ + 1/2]` for every coordinate `k`; that
is, `coverU ℓ L` is exactly the cube `[−1/2, L/ℓ + 1/2]³`.

* forward: the witness `x ∈ [0,L]³` gives `−ℓ/2 ≤ x_k − ℓ u_k ≤ ℓ/2` with
  `0 ≤ x_k ≤ L`, hence `−1/2 ≤ u_k ≤ L/ℓ + 1/2`;
* backward: for `u_k ∈ [−1/2, L/ℓ+1/2]` the clamped coordinate
  `x_k = max 0 (min L (ℓ u_k))` lies in `[0,L]` and satisfies
  `|x_k − ℓ u_k| ≤ ℓ/2` because `ℓ u_k ∈ [−ℓ/2, L + ℓ/2]`.

The volume is then obtained by identifying `ℝ³ = WithLp 2 (Fin 3 → ℝ)` with the
coordinate space in a measure preserving way (`PiLp.volume_preserving_ofLp`)
and applying `Real.volume_Icc_pi`.
-/

noncomputable section

open MeasureTheory Set

namespace Work.BoseKinLoc.Volume

/-- Coordinate description of the localisation cover `coverU ℓ L`. -/
private lemma mem_coverU_iff {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L) (u : ℝ³) :
    u ∈ Work.BoseKinLoc.coverU ℓ L ↔
      WithLp.ofLp u ∈ Set.univ.pi (fun _ : Fin 3 => Set.Icc (-(1 / 2 : ℝ)) (L / ℓ + 1 / 2)) := by
  rw [Set.mem_univ_pi]
  simp only [Work.BoseKinLoc.coverU, Work.BoseKinLoc.ombox, Submission.BoseGases.acube,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, hx, hxu⟩ k
    have hxk : 0 ≤ x k ∧ x k ≤ L := Set.mem_Icc.mp (hx k)
    have hk : -ℓ / 2 ≤ (x - ℓ • u) k ∧ (x - ℓ • u) k ≤ ℓ / 2 := Set.mem_Icc.mp (hxu k)
    rw [show (x - ℓ • u) k = x k - ℓ * u k by simp] at hk
    refine ⟨?_, ?_⟩
    · have h1 : ℓ * (-(1 / 2)) ≤ ℓ * u k := by linarith [hk.2, hxk.1]
      exact le_of_mul_le_mul_left h1 hℓ
    · have h1 : ℓ * u k ≤ ℓ * (L / ℓ + 1 / 2) := by
        have he : ℓ * (L / ℓ + 1 / 2) = L + ℓ / 2 := by field_simp
        linarith [hk.1, hxk.2, he]
      exact le_of_mul_le_mul_left h1 hℓ
  · intro hu
    refine ⟨WithLp.toLp 2 (fun k : Fin 3 => max 0 (min L (ℓ * u k))), ?_, ?_⟩
    · intro k
      exact ⟨le_max_left _ _, max_le hL (min_le_left _ _)⟩
    · intro k
      have huk : -(1 / 2) ≤ u k ∧ u k ≤ L / ℓ + 1 / 2 := hu k
      have htlo : -(ℓ / 2) ≤ ℓ * u k := by
        have := mul_le_mul_of_nonneg_left huk.1 hℓ.le
        linarith
      have hthi : ℓ * u k ≤ L + ℓ / 2 := by
        have h := mul_le_mul_of_nonneg_left huk.2 hℓ.le
        have he : ℓ * (L / ℓ + 1 / 2) = L + ℓ / 2 := by field_simp
        linarith [h, he]
      rw [Set.mem_Icc]
      rw [show (WithLp.toLp 2 (fun k : Fin 3 => max 0 (min L (ℓ * u k))) - ℓ • u) k
            = max 0 (min L (ℓ * u k)) - ℓ * u k by simp]
      by_cases h0 : ℓ * u k < 0
      · have hmin : min L (ℓ * u k) = ℓ * u k := min_eq_right (by linarith)
        have hmax : max 0 (ℓ * u k) = 0 := max_eq_left h0.le
        rw [hmin, hmax]
        constructor <;> linarith
      · by_cases hL' : L < ℓ * u k
        · have hmin : min L (ℓ * u k) = L := min_eq_left hL'.le
          have hmax : max 0 L = L := max_eq_right hL
          rw [hmin, hmax]
          constructor <;> linarith
        · have h0' : 0 ≤ ℓ * u k := le_of_not_gt h0
          have hL'' : ℓ * u k ≤ L := le_of_not_gt hL'
          have hmin : min L (ℓ * u k) = ℓ * u k := min_eq_right hL''
          have hmax : max 0 (ℓ * u k) = ℓ * u k := max_eq_right h0'
          rw [hmin, hmax]
          constructor <;> linarith

theorem volume_coverU {ℓ L : ℝ} (hℓ : 0 < ℓ) (hL : 0 ≤ L) :
    MeasureTheory.volume (Work.BoseKinLoc.coverU ℓ L) =
      ENNReal.ofReal ((L + ℓ) ^ 3 / ℓ ^ 3) := by
  have hset : Work.BoseKinLoc.coverU ℓ L =
      WithLp.ofLp ⁻¹' (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-(1 / 2 : ℝ)) (L / ℓ + 1 / 2))) :=
    Set.ext fun u => mem_coverU_iff hℓ hL u
  rw [hset]
  have hmeas : MeasurableSet (Set.univ.pi (fun _ : Fin 3 => Set.Icc (-(1 / 2 : ℝ)) (L / ℓ + 1 / 2))) :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
  rw [MeasureTheory.MeasurePreserving.measure_preimage (PiLp.volume_preserving_ofLp (Fin 3))
    hmeas.nullMeasurableSet]
  rw [MeasureTheory.volume_pi_pi]
  simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_pow (by
    have h1 : 0 ≤ L / ℓ := div_nonneg hL hℓ.le
    linarith : (0 : ℝ) ≤ L / ℓ + 1 / 2 - -(1 / 2))]
  congr 1
  field_simp
  ring

end Work.BoseKinLoc.Volume
