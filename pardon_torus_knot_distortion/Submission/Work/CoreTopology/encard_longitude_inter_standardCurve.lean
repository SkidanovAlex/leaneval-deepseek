import Mathlib
import Submission.Work.CoreTopology.ncard_standardCurve_longitude
import Submission.Work.StandardCurve.injOn_coprime

namespace Work.CoreTopology

/-- Every point of a `2π`-periodic curve is attained at some parameter in the
half-open fundamental period `[0, 2π)`: given `t`, the number `t - ⌊t/2π⌋ · 2π`
lies in `[0, 2π)` and has the same image. -/
private theorem exists_mem_Ico_of_periodic {α : Type*} {f : ℝ → α}
    (hf : Function.Periodic f (2 * Real.pi)) (t : ℝ) :
    ∃ s ∈ Set.Ico (0 : ℝ) (2 * Real.pi), f s = f t := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hpi' : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt hpi
  refine ⟨t - (⌊t / (2 * Real.pi)⌋ : ℤ) * (2 * Real.pi), ?_, hf.sub_int_mul_eq _⟩
  rw [Set.mem_Ico]
  have hlo := Int.floor_le (t / (2 * Real.pi))
  have hup := Int.lt_floor_add_one (t / (2 * Real.pi))
  have h1 : ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) ≤ t := by
    have h := mul_le_mul_of_nonneg_right hlo (le_of_lt hpi)
    rwa [div_mul_cancel₀ _ hpi'] at h
  have h2 : t < ((⌊t / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) + (2 * Real.pi) := by
    have h := mul_lt_mul_of_pos_right hup hpi
    rw [add_mul, one_mul, div_mul_cancel₀ _ hpi'] at h
    linarith
  exact ⟨by linarith, by linarith⟩

/-- For coprime positive `p, q`, the standard `(p,q)`-curve `β` and the longitude circle `{φ = const}` of the standard torus meet in exactly `q` points: `encard (range β ∩ range (longitude circle)) = q`. This is the point-set form of `ncard_standardCurve_longitude`, obtained by restricting `β` to the fundamental period `[0, 2π)`, on which `β` is injective (`Work.StandardCurve.injOn_coprime`). -/
theorem encard_longitude_inter_standardCurve (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (φ : ℝ) :
    Set.encard (Set.range (standardCurve p q) ∩ Set.range (longitudeCurve standard φ)) =
      (q : ℕ∞) := by
  have hper : Function.Periodic (standardCurve p q) (2 * Real.pi) :=
    fun t => (standardCurve p q).periodic t
  -- The image of the curve is already the image of one fundamental period.
  have hrange : Set.range (standardCurve p q) =
      standardCurve p q '' Set.Ico (0:ℝ) (2 * Real.pi) := by
    ext y
    constructor
    · rintro ⟨t, rfl⟩
      obtain ⟨s, hs, hfs⟩ := exists_mem_Ico_of_periodic hper t
      exact ⟨s, hs, hfs⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, rfl⟩
  -- Hence the intersection with the longitude circle is the image of the
  -- parameters in `[0, 2π)` at which the curve lies on the longitude circle.
  set S : Set ℝ := Set.Ico (0:ℝ) (2 * Real.pi) ∩
      {t : ℝ | (standardCurve p q).γ t ∈ Set.range (longitudeCurve standard φ).γ} with hS
  have hkey : Set.range (standardCurve p q) ∩ Set.range (longitudeCurve standard φ) =
      standardCurve p q '' S := by
    rw [hS, hrange, ← Set.image_inter_preimage]
    congr 1
  rw [hkey]
  have hScard : S.ncard = q := by
    rw [hS]; exact ncard_standardCurve_longitude p q hq φ
  -- The curve is injective on the fundamental period when `p` and `q` are coprime.
  have hinj : Set.InjOn (standardCurve p q) S := by
    rw [hS]
    exact (Work.StandardCurve.injOn_coprime p q hp hq hc).mono Set.inter_subset_left
  rw [hinj.encard_image]
  -- `S` is finite (its `ncard` is `q ≠ 0`), so `encard S = ncard S`.
  have hfin : S.Finite := by
    rw [← Set.encard_ne_top_iff]
    intro htop
    rw [Set.ncard_def, htop, ENat.toNat_top] at hScard
    omega
  rw [← hfin.cast_ncard_eq, hScard]

end Work.CoreTopology
