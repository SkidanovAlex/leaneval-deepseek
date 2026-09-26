import Mathlib
import Submission.Work.CoreTopology.ncard_standardCurve_meridian
import Submission.Work.StandardCurve.injOn_coprime

open LeanEval.KnotTheory.PardonDistortion

namespace Work.CoreTopology

/-- A `2π`-periodic function on `ℝ` takes each of its values already on the
fundamental period `[0, 2π)`: for every `t` there is `t' ∈ [0, 2π)` with
`f t' = f t`, namely `t` reduced modulo `2π` (i.e. `t - ⌊t / 2π⌋ · 2π`). -/
theorem exists_mem_Ico_period {f : ℝ → R3} (hper : Function.Periodic f (2 * Real.pi))
    (t : ℝ) : ∃ t' ∈ Set.Ico (0 : ℝ) (2 * Real.pi), f t' = f t := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨t - (⌊t / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi), ?_, ?_⟩
  · rw [Set.mem_Ico]
    constructor
    · have h1 : ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) ≤ t / (2 * Real.pi) := Int.floor_le _
      have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt hpi)
      rw [div_mul_cancel₀ t (ne_of_gt hpi)] at h2
      linarith
    · have h1 : t / (2 * Real.pi) < ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) + 1 :=
        Int.lt_floor_add_one _
      have h2 := mul_lt_mul_of_pos_right h1 hpi
      rw [add_mul, div_mul_cancel₀ t (ne_of_gt hpi), one_mul] at h2
      linarith
  · exact hper.sub_int_mul_eq ⌊t / (2 * Real.pi)⌋

/-- For coprime positive `p, q`, the standard `(p,q)`-curve `β` and the meridian circle `{θ = const}` of the standard torus meet in exactly `p` points: `encard (range β ∩ range (meridian circle)) = p`. This is the point-set form of `ncard_standardCurve_meridian`, obtained by restricting `β` to the fundamental period `[0, 2π)`, on which `β` is injective (`Work.StandardCurve.injOn_coprime`). -/
theorem encard_meridian_inter_standardCurve (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (θ : ℝ) :
    Set.encard (Set.range (standardCurve p q) ∩ Set.range (meridianCurve standard θ)) =
      (p : ℕ∞) := by
  -- The set of parameters in a fundamental period at which `β` meets the meridian circle.
  let T : Set ℝ := Set.Ico (0 : ℝ) (2 * Real.pi) ∩
      {t : ℝ | standardCurve p q t ∈ Set.range (meridianCurve standard θ)}
  have hper : Function.Periodic (fun t : ℝ => standardCurve p q t) (2 * Real.pi) :=
    (standardCurve p q).periodic
  -- `β` is `2π`-periodic, so its range is already the image of the fundamental period.
  have hrange : Set.range (standardCurve p q) =
      (fun t : ℝ => standardCurve p q t) '' Set.Ico (0 : ℝ) (2 * Real.pi) := by
    apply Set.Subset.antisymm
    · rintro x ⟨t, rfl⟩
      obtain ⟨t', ht', ht'eq⟩ := exists_mem_Ico_period hper t
      exact ⟨t', ht', ht'eq⟩
    · rintro x ⟨t, _ht, rfl⟩
      exact ⟨t, rfl⟩
  -- The counting lemma: exactly `p` parameters in the fundamental period.
  have hT : T.ncard = p := ncard_standardCurve_meridian p q hp θ
  have hfin : T.Finite := by
    by_contra h
    rw [Set.not_finite] at h
    rw [h.ncard] at hT
    omega
  -- `β` is injective on the fundamental period when `p` and `q` are coprime.
  have hinj : Set.InjOn (fun t : ℝ => standardCurve p q t) T := by
    have hinj0 : Set.InjOn (standardTorusCurve p q) (Set.Ico (0 : ℝ) (2 * Real.pi)) :=
      Work.StandardCurve.injOn_coprime p q hp hq hc
    intro s hs t ht hst
    have h : standardTorusCurve p q s = standardTorusCurve p q t := by
      calc standardTorusCurve p q s = standardCurve p q s := (standardCurve_apply p q s).symm
        _ = standardCurve p q t := hst
        _ = standardTorusCurve p q t := standardCurve_apply p q t
    exact hinj0 hs.1 ht.1 h
  -- Intersection with the meridian circle is the image of `T` under `β`.
  have hS : Set.range (standardCurve p q) ∩ Set.range (meridianCurve standard θ) =
      (fun t : ℝ => standardCurve p q t) '' T := by
    rw [hrange]
    exact (Set.image_inter_preimage _ _ _).symm
  rw [hS, hinj.encard_image, ← hfin.cast_ncard_eq, hT]

end Work.CoreTopology
