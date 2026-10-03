/-
# The narrow (Farey) part of the modulated bump-difference family at the bottom height

At the bottom continuous height `k₁ = 0` the guard `core ρ 0 0 0 0 0` of
`Work.KMTAreas.A7.lacunaryBumpFareyDiffPartBound` is *automatic* on the narrow scales: the Farey
condition `0 - Log ⌊a n⌋ ≤ ⌊-Cρc⌋` with `Cρc ≥ 3` forces `Log ⌊a n⌋ ≥ 3`, hence `⌊a n⌋ ≥ 8`, and
at the bottom height every other conjunct of the guard (`inIndexSet 0 0 0 0`, `splitCut ρ 0 = 4`,
`mainRegime ρ 0 0`) is implied by `⌊a n⌋ ≥ 8`.  Consequently the `Farey`-clipped difference family
is bounded by the `core ∧ Farey`-clipped one, and the estimate of
`lacunaryBumpFareyDiffPartBound` transfers.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacunaryBumpFareyDiffPartBound

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.KMTAreas.A7LoLin

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7
open Work.Analysis.EndVar

noncomputable section

/-- Clipping a symbol by two equivalent propositions gives the same `Tle` family. -/
theorem Tle_clip_congr {ρ : ℝ} {l : ℕ} {c c' : Prop} [Decidable c] [Decidable c']
    (h : c ↔ c') {φ : ℝ → ℂ} {f : ℤ → ℂ} :
    Tle ρ l (fun ξ : ℝ => if c then φ ξ else 0) f
      = Tle ρ l (fun ξ : ℝ => if c' then φ ξ else 0) f := by
  have hfun : (fun ξ : ℝ => if c then φ ξ else 0)
      = fun ξ : ℝ => if c' then φ ξ else 0 := by
    funext ξ
    by_cases hc : c
    · rw [if_pos hc, if_pos (h.mp hc)]
    · rw [if_neg hc, if_neg (fun hc' => hc (h.mpr hc'))]
  rw [hfun]

/-- **At the bottom height the Farey condition implies the `core` guard** (for `Cρc ≥ 3`). -/
theorem core_bottom_of_farey {ρ Cρc : ℝ} (hCρc : 3 ≤ Cρc) {a : ℕ → NNReal} {n : ℕ}
    (h : Farey Cρc ρ 0 0 a n) : core ρ 0 0 0 0 0 a n := by
  set N : ℕ := Nat.floor (a n) with hN
  have hF : (0 : ℤ) - logN N ≤ fareyK Cρc ρ 0 := h
  have hfarey : fareyK Cρc ρ 0 = ⌊(-Cρc : ℝ)⌋ := by
    simp only [fareyK]
    norm_num
  rw [hfarey, zero_sub] at hF
  have hfloor : ⌊(-Cρc : ℝ)⌋ ≤ -3 := by
    rw [Int.floor_le_iff]
    push_cast
    linarith
  have hlog : (3 : ℤ) ≤ logN N := by omega
  have hN8 : 8 ≤ N := by
    have h3 : 3 ≤ (logN N).toNat := by omega
    have hpow : 2 ^ ((logN N).toNat) ≤ max N 2 := by
      have h := Nat.pow_log_le_self 2 (by omega : max N 2 ≠ 0)
      simpa [logN] using h
    have : (8 : ℕ) ≤ max N 2 := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ ((logN N).toNat) := Nat.pow_le_pow_right (by norm_num) h3
        _ ≤ max N 2 := hpow
    omega
  refine ⟨?_, ?_, ?_⟩
  · simp [inIndexSet, heightScale]
  · have h4 : splitCut ρ (max (max 0 0) (max 0 0)) = 4 := by
      simp [splitCut, scaleCount]
    rw [h4]
    omega
  · simp only [mainRegime, uScale, Nat.zero_add, max_self]
    have hsc : scaleCount 1 ρ 0 = 1 := by
      simp [scaleCount]
    rw [hsc]
    have : (2 : ℕ) ≤ (logN N).toNat := by omega
    exact ⟨this, this⟩

/-- **The narrow part of the modulated bump-difference family at the bottom height**, from
`Work.KMTAreas.A7.lacunaryBumpFareyDiffPartBound` (its `core ∧ Farey` guard is equivalent to `Farey`
here). -/
theorem fareyModDiffK (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p)
    (hptop : p < ⊤) (r : NNReal) (hr : 2 < r) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ Cρc : ℝ, 3 ≤ Cρc ∧ ∃ K : ℝ, 0 < K ∧
      ∀ (t : ℝ) (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1)
        (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
        (f : ℤ → ℂ),
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0 (fun ξ : ℝ =>
            if Work.KMTAreas.A7.Farey Cρc ρ 0 0 a n
            then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
              - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ else 0) f x))
          p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal K * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨Cρc, h3, K, hKpos, hbound⟩ :=
    lacunaryBumpFareyDiffPartBound 0 r hr ρ hρ hρ1 Λ hΛ p hp hptop
  refine ⟨Cρc, h3, K, hKpos, ?_⟩
  intro t ht a ha ha1 f
  have hpt : ∀ x : ℤ,
      PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (fun ξ : ℝ => if Work.KMTAreas.A7.Farey Cρc ρ 0 0 a n
            then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
              - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ else 0) f x)
        = PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (fun ξ : ℝ => if core ρ 0 0 0 0 0 a n ∧ Work.KMTAreas.A7.Farey Cρc ρ 0 0 a n
            then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
              - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ else 0) f x) := by
    intro x
    congr 1
    funext n
    exact congrFun (Tle_clip_congr (ρ := ρ) (l := 0)
      (c := Work.KMTAreas.A7.Farey Cρc ρ 0 0 a n)
      (c' := core ρ 0 0 0 0 0 a n ∧ Work.KMTAreas.A7.Farey Cρc ρ 0 0 a n)
      ⟨fun hF => ⟨core_bottom_of_farey h3 hF, hF⟩, fun hc => hc.2⟩
      (φ := fun ξ : ℝ => Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
        - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ) (f := f)) x
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
            (fun ξ : ℝ => if Work.KMTAreas.A7.Farey Cρc ρ 0 0 a n
              then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ else 0) f x))
          p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
            (fun ξ : ℝ => if core ρ 0 0 0 0 0 a n ∧ Work.KMTAreas.A7.Farey Cρc ρ 0 0 a n
              then Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ else 0) f x))
          p MeasureTheory.Measure.count := by
        congr 1
        funext x
        exact hpt x
    _ ≤ ENNReal.ofReal K * MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
        have h := hbound 0 0 0 0 le_rfl t ht a ha ha1 f
        simpa using h

end

end Work.KMTAreas.A7LoLin
