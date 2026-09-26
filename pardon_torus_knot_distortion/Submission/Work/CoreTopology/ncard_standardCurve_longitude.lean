import Mathlib
import Submission.Work.CoreTopology.Disk

/-!
# The standard `(p,q)` curve meets a longitude circle in exactly `q` points

The standard `(p,q)`-torus curve is the image of the straight line `t ↦ (p t, q t)`
in the parameter torus; a longitude circle `{φ = const}` is the level set of the
*second* parameter.  Hence `standardCurve p q t` lies on the longitude circle at
parameter `φ` exactly when `q t ≡ φ (mod 2π)`.  As `t` runs over a half-open period
`[0, 2π)` this congruence has exactly `q` solutions (they are the numbers
`(φ + 2π k)/q` for the `q` consecutive integers `k` with `φ + 2π k ∈ [0, 2π q)`).

No coprimality of `p` and `q` is needed.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.CoreTopology

/-- Membership of the standard `(p,q)`-curve in a longitude circle is equivalent to
the congruence `q t ≡ φ (mod 2π)`; the first (`p`-twisted) parameter is irrelevant. -/
private theorem standardCurve_mem_longitude_iff (p q : ℕ) (φ t : ℝ) :
    (standardCurve p q t ∈ Set.range (longitudeCurve standard φ)) ↔
      (∃ k : ℤ, (q : ℝ) * t = φ + (k : ℝ) * (2 * Real.pi)) := by
  constructor
  · rintro ⟨θ, hθ⟩
    have h : Work.Core.torusMap ((p : ℝ) * t) ((q : ℝ) * t) =
        Work.Core.torusMap θ φ := hθ.symm
    exact ((Work.Core.torusMap_eq_iff _ _ _ _).mp h).2
  · rintro ⟨k, hk⟩
    refine ⟨(p : ℝ) * t, ?_⟩
    show Work.Core.torusMap ((p : ℝ) * t) φ = Work.Core.torusMap ((p : ℝ) * t) ((q : ℝ) * t)
    have hc : ((-k : ℤ) : ℝ) * (2 * Real.pi) = -(k : ℝ) * (2 * Real.pi) := by
      push_cast; ring
    have key2 : φ = (q : ℝ) * t + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hc]; linarith
    exact (Work.Core.torusMap_eq_iff _ _ _ _).mpr ⟨⟨0, by simp⟩, ⟨-k, key2⟩⟩

/-- For a positive integer `q`, the solutions in a half-open period of the congruence
`q t ≡ φ (mod 2π)` are exactly `q` in number. -/
private theorem ncard_longitude_solutions (q : ℕ) (hq : 0 < q) (φ : ℝ) :
    (Set.Ico (0 : ℝ) (2 * Real.pi) ∩
      {t : ℝ | ∃ k : ℤ, (q : ℝ) * t = φ + (k : ℝ) * (2 * Real.pi)}).ncard = q := by
  let m : ℤ := ⌈-(φ) / (2 * Real.pi)⌉
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpne : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hpi
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
  have hm_low : -(φ) / (2 * Real.pi) ≤ (m : ℝ) := Int.le_ceil _
  have hm_up : (m : ℝ) < -(φ) / (2 * Real.pi) + 1 := Int.ceil_lt_add_one _
  have hm_low' : -φ ≤ (m : ℝ) * (2 * Real.pi) := by
    have h := mul_le_mul_of_nonneg_right hm_low (le_of_lt hpi)
    rwa [div_mul_cancel₀ _ hpne] at h
  have hm_up' : (m : ℝ) * (2 * Real.pi) < 2 * Real.pi - φ := by
    have h := mul_lt_mul_of_pos_right hm_up hpi
    rw [add_mul, div_mul_cancel₀ _ hpne, one_mul] at h
    linarith
  refine Set.ncard_eq_of_bijective
    (fun i _ => (φ + ((m + i : ℤ) : ℝ) * (2 * Real.pi)) / (q : ℝ)) ?_ ?_ ?_
  · intro a ha
    rw [Set.mem_inter_iff] at ha
    obtain ⟨ha1, ⟨k, hk⟩⟩ := ha
    rw [Set.mem_Ico] at ha1
    obtain ⟨ha0, ha2pi⟩ := ha1
    have hkg : -(φ) / (2 * Real.pi) ≤ (k : ℝ) := by
      rw [div_le_iff₀ hpi]
      have : (0 : ℝ) ≤ (q : ℝ) * a := mul_nonneg (le_of_lt hqpos) ha0
      linarith
    have hm_le_k : m ≤ k := Int.ceil_le.mpr hkg
    have hklt : (k : ℝ) < ((q : ℝ) * (2 * Real.pi) - φ) / (2 * Real.pi) := by
      rw [lt_div_iff₀ hpi]
      have h : (q : ℝ) * a < (q : ℝ) * (2 * Real.pi) := mul_lt_mul_of_pos_left ha2pi hqpos
      linarith
    have hle : ((q : ℝ) * (2 * Real.pi) - φ) / (2 * Real.pi) ≤ (q : ℝ) + (m : ℝ) := by
      rw [div_le_iff₀ hpi]
      linarith
    have hku : (k : ℝ) < (q : ℝ) + (m : ℝ) := lt_of_lt_of_le hklt hle
    have hkq : k ≤ m + (q : ℤ) - 1 := by
      have h1 : (k : ℝ) < ((m + (q : ℤ) : ℤ) : ℝ) := by push_cast; linarith
      have h2 : k < m + (q : ℤ) := by exact_mod_cast h1
      omega
    refine ⟨(k - m).toNat, ?_, ?_⟩
    · have hcast : (((k - m).toNat : ℕ) : ℤ) = k - m := Int.toNat_of_nonneg (by omega)
      omega
    · have hcast : (((k - m).toNat : ℕ) : ℤ) = k - m := Int.toNat_of_nonneg (by omega)
      have hmik : m + ((k - m).toNat : ℤ) = k := by omega
      show (φ + ((m + (k - m).toNat : ℤ) : ℝ) * (2 * Real.pi)) / (q : ℝ) = a
      rw [show ((m + (k - m).toNat : ℤ) : ℝ) = (k : ℝ) by rw [hmik]]
      rw [show φ + (k : ℝ) * (2 * Real.pi) = (q : ℝ) * a from hk.symm]
      exact mul_div_cancel_left₀ a hqne
  · intro i hi
    rw [Set.mem_inter_iff]
    have hmi_ge : (m : ℝ) ≤ ((m + i : ℤ) : ℝ) := by
      push_cast; exact le_add_of_nonneg_right (Nat.cast_nonneg i)
    have hnum : 0 ≤ φ + ((m + i : ℤ) : ℝ) * (2 * Real.pi) := by
      nlinarith [hm_low', hmi_ge, hpi]
    constructor
    · rw [Set.mem_Ico]
      refine ⟨div_nonneg hnum (le_of_lt hqpos), ?_⟩
      have hcast : ((m + i : ℤ) : ℝ) * (2 * Real.pi) =
          (m : ℝ) * (2 * Real.pi) + (i : ℝ) * (2 * Real.pi) := by
        push_cast; ring
      have hi_le : (i : ℝ) ≤ (q : ℝ) - 1 := by
        have : (i : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast (show i + 1 ≤ q by omega)
        linarith
      have hi2 : (i : ℝ) * (2 * Real.pi) ≤ ((q : ℝ) - 1) * (2 * Real.pi) :=
        mul_le_mul_of_nonneg_right hi_le (le_of_lt hpi)
      rw [div_lt_iff₀ hqpos]
      nlinarith [hm_up', hcast, hi2, hpi]
    · exact ⟨(m + i : ℤ), mul_div_cancel₀ _ hqne⟩
  · intro i j hi hj hij
    have hXY : φ + ((m + i : ℤ) : ℝ) * (2 * Real.pi) =
        φ + ((m + j : ℤ) : ℝ) * (2 * Real.pi) := by
      have h := congrArg (fun x : ℝ => x * (q : ℝ)) hij
      rwa [div_mul_cancel₀ _ hqne, div_mul_cancel₀ _ hqne] at h
    have h2 : ((m + i : ℤ) : ℝ) * (2 * Real.pi) = ((m + j : ℤ) : ℝ) * (2 * Real.pi) := by
      linarith
    have h3 : ((m + i : ℤ) : ℝ) = ((m + j : ℤ) : ℝ) := mul_right_cancel₀ hpne h2
    have h4 : (m + i : ℤ) = (m + j : ℤ) := by exact_mod_cast h3
    omega

/-- For positive `q`, the standard `(p,q)`-curve on the torus of revolution meets the longitude circle `{φ = const}` in exactly `q` points of a fundamental period: the set of parameters `t ∈ [0, 2π)` for which `standardCurve p q t` lies on the longitude circle at parameter `φ` has cardinality `q`. No coprimality is needed: writing the curve as `t ↦ torusMap (p t) (q t)`, the condition is `q t ≡ φ (mod 2π)`, which has exactly `q` solutions in a half-open period. -/
theorem ncard_standardCurve_longitude (p q : ℕ) (hq : 0 < q) (φ : ℝ) :
    (Set.Ico (0 : ℝ) (2 * Real.pi) ∩
      {t : ℝ | standardCurve p q t ∈ Set.range (longitudeCurve standard φ)}).ncard = q := by
  have hset : (Set.Ico (0 : ℝ) (2 * Real.pi) ∩
        {t : ℝ | standardCurve p q t ∈ Set.range (longitudeCurve standard φ)})
      = (Set.Ico (0 : ℝ) (2 * Real.pi) ∩
        {t : ℝ | ∃ k : ℤ, (q : ℝ) * t = φ + (k : ℝ) * (2 * Real.pi)}) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (standardCurve_mem_longitude_iff p q φ t).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (standardCurve_mem_longitude_iff p q φ t).mpr h2⟩
  rw [hset]
  exact ncard_longitude_solutions q hq φ

end Work.CoreTopology
