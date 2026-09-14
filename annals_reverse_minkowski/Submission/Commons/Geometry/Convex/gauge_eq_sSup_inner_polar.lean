import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Submission.Commons.Geometry.Convex.smul_mem_iff_le_inv_gauge

namespace Commons.Geometry.Convex

open Set
open scoped Pointwise

/-- Separation/bipolar form: if `x` lies outside a compact convex set `K` with `0` in its
interior, there is a vector `z` which is `≤ 1` on `K` (i.e. lies in the polar of `K`) but whose
inner product with `x` is `> 1`. -/
theorem exists_inner_gt_one_of_notMem {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {K : Set E} (hKcvx : Convex ℝ K) (hKcpt : IsCompact K)
    (hK0 : (0 : E) ∈ interior K) {x : E} (hxK : x ∉ K) :
    ∃ z : E, (∀ y ∈ K, inner ℝ z y ≤ 1) ∧ 1 < inner ℝ z x := by
  obtain ⟨f, u, hfK, hux⟩ :=
    geometric_hahn_banach_closed_point hKcvx hKcpt.isClosed hxK
  set z₀ : E := (InnerProductSpace.toDual ℝ E).symm f with hz₀
  have hz₀a : ∀ a : E, inner ℝ z₀ a = f a := fun a => by
    rw [hz₀]; exact InnerProductSpace.toDual_symm_apply
  have hu_pos : 0 < u := by
    have h := hfK 0 (interior_subset hK0)
    simp only [map_zero] at h
    linarith
  refine ⟨u⁻¹ • z₀, ?_, ?_⟩
  · intro y hy
    rw [real_inner_smul_left, hz₀a y]
    have h2 : u⁻¹ * f y < u⁻¹ * u := mul_lt_mul_of_pos_left (hfK y hy) (inv_pos.mpr hu_pos)
    rw [inv_mul_cancel₀ hu_pos.ne'] at h2
    linarith
  · rw [real_inner_smul_left, hz₀a x]
    have h2 : u⁻¹ * u < u⁻¹ * f x := mul_lt_mul_of_pos_left hux (inv_pos.mpr hu_pos)
    rw [inv_mul_cancel₀ hu_pos.ne'] at h2
    exact h2

/-- Bipolar form: a point all of whose inner products against the polar
`{z | ∀ y ∈ K, ⟪z, y⟫ ≤ 1}` are `≤ 1` lies in `K`. -/
theorem mem_of_forall_inner_le_one {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {K : Set E} (hKcvx : Convex ℝ K) (hKcpt : IsCompact K)
    (hK0 : (0 : E) ∈ interior K) {x : E}
    (h : ∀ z : E, (∀ y ∈ K, inner ℝ z y ≤ 1) → inner ℝ z x ≤ 1) : x ∈ K := by
  by_contra hxK
  obtain ⟨z, hz, hzx⟩ := exists_inner_gt_one_of_notMem hKcvx hKcpt hK0 hxK
  exact absurd (h z hz) (not_le.mpr hzx)

theorem gauge_eq_sSup_inner_polar {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (K : Set E) (hKcvx : Convex ℝ K) (hKcpt : IsCompact K) (hK0 : (0 : E) ∈ interior K) (v : E) : gauge K v = sSup ((fun z : E => inner ℝ z v) '' {z : E | ∀ y ∈ K, inner ℝ z y ≤ 1}) := by
  let P : Set E := {z : E | ∀ y ∈ K, inner ℝ z y ≤ 1}
  let S : Set ℝ := (fun z : E => inner ℝ z v) '' P
  change gauge K v = sSup S
  have h0P : (0 : E) ∈ P := by
    simp only [P]
    intro y hy
    simp
  have hmem0S : (0 : ℝ) ∈ S := ⟨(0 : E), h0P, by simp⟩
  have hSne : S.Nonempty := ⟨(0 : ℝ), hmem0S⟩
  have hA : ∀ c ∈ S, c ≤ gauge K v := by
    rintro c ⟨z, hz, rfl⟩
    have hz' : ∀ y ∈ K, inner ℝ z y ≤ 1 := hz
    show inner ℝ z v ≤ gauge K v
    apply le_of_forall_pos_le_add
    intro eps heps
    have ht : 0 < gauge K v + eps := by
      have := gauge_nonneg (s := K) v
      linarith
    have hvt : v ∈ (gauge K v + eps) • K :=
      (gauge_le_iff_of_pos hKcpt hKcvx hK0 ht).mp (by linarith)
    obtain ⟨y, hy, hyv⟩ := Set.mem_smul_set.mp hvt
    conv_lhs => rw [← hyv, real_inner_smul_right]
    have h1 : (gauge K v + eps) * inner ℝ z y ≤ (gauge K v + eps) * 1 :=
      mul_le_mul_of_nonneg_left (hz' y hy) (by linarith [gauge_nonneg (s := K) v])
    linarith
  have hupper : sSup S ≤ gauge K v := csSup_le hSne hA
  have hbdd : BddAbove S := ⟨gauge K v, hA⟩
  have hSnonneg : 0 ≤ sSup S := le_csSup hbdd hmem0S
  have hB : gauge K v ≤ sSup S := by
    apply le_of_forall_pos_le_add
    intro eps heps
    have ht : 0 < sSup S + eps := by linarith
    rw [gauge_le_iff_of_pos hKcpt hKcvx hK0 ht]
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ ht.ne' K v]
    apply mem_of_forall_inner_le_one hKcvx hKcpt hK0
    intro z hz
    have hzv : inner ℝ z v ≤ sSup S := le_csSup hbdd ⟨z, hz, rfl⟩
    rw [real_inner_smul_right]
    have h1 : (sSup S + eps)⁻¹ * inner ℝ z v ≤ (sSup S + eps)⁻¹ * (sSup S + eps) :=
      mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.mpr ht.le)
    rwa [inv_mul_cancel₀ ht.ne'] at h1
  exact le_antisymm hB hupper

end Commons.Geometry.Convex