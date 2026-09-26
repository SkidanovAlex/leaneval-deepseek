import Mathlib
import Submission.Work.CoreTopology.Disk

namespace Work.CoreTopology

open Set

/-- Counting lemma for an arithmetic progression intersected with a half-open
interval: for `c > 0` and a natural number `p`, the points `a + k c` (`k ∈ ℤ`)
lying in `[0, p · c)` are exactly `p` in number.

Indeed, writing `X = -a/c`, membership of `a + k c = (k - X) c` in `[0, p c)`
is equivalent to `X ≤ k < X + p`, and the integers in the half-open interval
`[X, X + p)` are `⌈X⌉, ⌈X⌉ + 1, …, ⌈X⌉ + p - 1`. -/
theorem ncard_Ico_add_int_mul (a c : ℝ) (hc : 0 < c) (p : ℕ) (_hp : 0 < p) :
    (Set.Ico (0 : ℝ) ((p : ℝ) * c) ∩
      {t : ℝ | ∃ k : ℤ, t = a + (k : ℝ) * c}).ncard = p := by
  have hcne : c ≠ 0 := ne_of_gt hc
  set X : ℝ := -a / c with hX
  have hmul : ∀ k : ℤ, a + (k : ℝ) * c = ((k : ℝ) - X) * c := by
    intro k
    rw [hX]
    field_simp
    ring
  set m : ℤ := ⌈X⌉ with hm
  have hm_ge : X ≤ (m : ℝ) := by rw [hm]; exact Int.le_ceil X
  have hm_lt : (m : ℝ) < X + 1 := by rw [hm]; exact Int.ceil_lt_add_one X
  refine Set.ncard_eq_of_bijective (fun i _ => a + ((m + (i : ℤ) : ℤ) : ℝ) * c) ?_ ?_ ?_
  · rintro t ⟨htI, k, rfl⟩
    rw [Set.mem_Ico, hmul k, mul_nonneg_iff_of_pos_right hc, sub_nonneg] at htI
    obtain ⟨ht1, ht2⟩ := htI
    rw [mul_lt_mul_iff_of_pos_right hc] at ht2
    have hmk : m ≤ k := by rw [hm]; exact Int.ceil_le.mpr ht1
    have hsub : 0 ≤ k - m := by omega
    have hklp : ((k - m : ℤ) : ℝ) < (p : ℝ) := by
      have hkp : (k : ℝ) < (p : ℝ) + X := by linarith
      push_cast
      linarith
    refine ⟨(k - m).toNat, ?_, ?_⟩
    · rw [Int.toNat_lt hsub]
      exact_mod_cast hklp
    · have hcast : ((m + (((k - m).toNat : ℤ)) : ℤ) : ℝ) = (k : ℝ) := by
        have htn : (((k - m).toNat : ℤ)) = k - m := Int.toNat_of_nonneg hsub
        rw [htn]; push_cast; ring
      rw [hcast]
  · intro i hi
    have hcast : ((m + (i : ℤ) : ℤ) : ℝ) = (m : ℝ) + (i : ℝ) := by push_cast; ring
    have hi1 : (i : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hi)
    have h0i : (0 : ℝ) ≤ (i : ℝ) := by positivity
    refine ⟨?_, ⟨m + (i : ℤ), rfl⟩⟩
    · rw [Set.mem_Ico, hmul (m + (i : ℤ)), hcast, mul_nonneg_iff_of_pos_right hc, sub_nonneg,
        mul_lt_mul_iff_of_pos_right hc]
      constructor <;> linarith
  · intro i j _hi _hj heq
    have hcast : ((m + (i : ℤ) : ℤ) : ℝ) * c = ((m + (j : ℤ) : ℤ) : ℝ) * c := by linarith
    have h2 : ((m + (i : ℤ) : ℤ) : ℝ) = ((m + (j : ℤ) : ℤ) : ℝ) :=
      mul_right_cancel₀ hcne hcast
    have h3 : (m + (i : ℤ) : ℤ) = (m + (j : ℤ) : ℤ) := by exact_mod_cast h2
    omega

/-- For positive `p`, the standard `(p,q)`-curve on the torus of revolution meets the meridian circle `{θ = const}` in exactly `p` points of a fundamental period: the set of parameters `t ∈ [0, 2π)` for which `standardCurve p q t` lies on the meridian circle at parameter `θ` has cardinality `p`. No coprimality is needed: writing the curve as `t ↦ torusMap (p t) (q t)`, the condition is `p t ≡ θ (mod 2π)`, which has exactly `p` solutions in a half-open period. -/
theorem ncard_standardCurve_meridian (p q : ℕ) (hp : 0 < p) (θ : ℝ) :
    (Set.Ico (0 : ℝ) (2 * Real.pi) ∩
      {t : ℝ | standardCurve p q t ∈ Set.range (meridianCurve standard θ)}).ncard = p := by
  have hpne : (p : ℝ) ≠ 0 := by positivity
  have hc : 0 < 2 * Real.pi / (p : ℝ) := by positivity
  have h2pi : (2 : ℝ) * Real.pi = (p : ℝ) * (2 * Real.pi / (p : ℝ)) := by field_simp
  have hI : Set.Ico (0 : ℝ) (2 * Real.pi)
      = Set.Ico (0 : ℝ) ((p : ℝ) * (2 * Real.pi / (p : ℝ))) :=
    congrArg (fun x : ℝ => Set.Ico (0 : ℝ) x) h2pi
  -- The curve `t ↦ torusMap (p t) (q t)` meets the meridian circle `{θ = const}`
  -- exactly when `p t ≡ θ (mod 2π)`.
  have hset : {t : ℝ | standardCurve p q t ∈ Set.range (meridianCurve standard θ)}
      = {t : ℝ | ∃ k : ℤ, t = θ / (p : ℝ) + (k : ℝ) * (2 * Real.pi / (p : ℝ))} := by
    ext t
    simp only [Set.mem_ofPred_eq]
    constructor
    · intro h
      rw [Set.mem_range] at h
      obtain ⟨φ, hφ⟩ := h
      have hφ' : Work.Core.torusMap θ φ = Work.Core.torusMap ((p : ℝ) * t) ((q : ℝ) * t) := hφ
      obtain ⟨⟨k, hk⟩, -⟩ :=
        (Work.Core.torusMap_eq_iff θ φ ((p : ℝ) * t) ((q : ℝ) * t)).mp hφ'
      refine ⟨-k, ?_⟩
      refine mul_left_cancel₀ hpne ?_
      have h1 : (p : ℝ) * (θ / (p : ℝ) + ((-k : ℤ) : ℝ) * (2 * Real.pi / (p : ℝ)))
          = θ + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
        field_simp
      rw [h1]
      push_cast at hk ⊢
      linarith
    · rintro ⟨k, rfl⟩
      refine ⟨(q : ℝ) * (θ / (p : ℝ) + (k : ℝ) * (2 * Real.pi / (p : ℝ))), ?_⟩
      change Work.Core.torusMap θ ((q : ℝ) * (θ / (p : ℝ) + (k : ℝ) * (2 * Real.pi / (p : ℝ))))
        = Work.Core.torusMap ((p : ℝ) * (θ / (p : ℝ) + (k : ℝ) * (2 * Real.pi / (p : ℝ))))
            ((q : ℝ) * (θ / (p : ℝ) + (k : ℝ) * (2 * Real.pi / (p : ℝ))))
      have hpt : (p : ℝ) * (θ / (p : ℝ) + (k : ℝ) * (2 * Real.pi / (p : ℝ)))
          = θ + (k : ℝ) * (2 * Real.pi) := by
        field_simp
      rw [hpt]
      exact (Work.Core.torusMap_eq_iff θ
        ((q : ℝ) * (θ / (p : ℝ) + (k : ℝ) * (2 * Real.pi / (p : ℝ))))
        (θ + (k : ℝ) * (2 * Real.pi))
        ((q : ℝ) * (θ / (p : ℝ) + (k : ℝ) * (2 * Real.pi / (p : ℝ))))).mpr
        ⟨⟨-k, by push_cast; ring⟩, ⟨0, by ring⟩⟩
  rw [hset, hI]
  exact ncard_Ico_add_int_mul (θ / (p : ℝ)) (2 * Real.pi / (p : ℝ)) hc p hp

end Work.CoreTopology
