import Mathlib
import Submission.Work.PL.Defs

namespace Work.Engulf.E4Aux

open Set Finset

/-- For an affine map `A : E N →ᵃ[ℝ] E n`, a weighted sum of images whose weights total `0` is the
linear part of the weighted sum of the points: `A x = A.linear x + A 0`, the constant term
carries the total weight `0`. -/
lemma sum_smul_affine_eq_linear {N n : ℕ} (A : PL.E N →ᵃ[ℝ] PL.E n) {ι : Type*}
    (t : Finset ι) (w : ι → ℝ) (z : ι → PL.E N) (hw : ∑ i ∈ t, w i = 0) :
    ∑ i ∈ t, w i • A (z i) = A.linear (∑ i ∈ t, w i • z i) := by
  have hAx : ∀ x : PL.E N, A x = A.linear x + A 0 := by
    intro x
    have h := AffineMap.map_vadd A (0 : PL.E N) x
    simpa using h
  calc ∑ i ∈ t, w i • A (z i)
      = ∑ i ∈ t, (w i • A.linear (z i) + w i • A 0) := by
        exact Finset.sum_congr rfl fun i _ => by rw [hAx (z i), smul_add]
    _ = ∑ i ∈ t, w i • A.linear (z i) + ∑ i ∈ t, w i • A 0 := Finset.sum_add_distrib
    _ = A.linear (∑ i ∈ t, w i • z i) := by
        have hzero : ∑ i ∈ t, w i • A 0 = 0 := by
          rw [← Finset.sum_smul, hw, zero_smul]
        rw [hzero, add_zero, map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul]

/-- **`hnd` for `GPaForm` (`E4a`)**.  An affine map injective on the simplex `simp s` preserves affine independence of the vertex set `s`: the images `A v`, `v ∈ s`, are affinely independent.  (Write `A x = A 0 + L x` with `L` linear; `∑ λ_v = 0` and `∑ λ_v • A v = 0` give `L (∑ λ_v • v) = 0`, and `∑ λ_v • v` lies in the direction of `aff s`; injectivity on `simp s` forces `L` to be injective on that direction, so `∑ λ_v • v = 0`, and `AffineIndependent` of `s` gives `λ = 0`.) -/
theorem affineIndependent_image_of_injOn {N n : ℕ} {s : Finset (PL.E N)}
    (hind : AffineIndependent ℝ (fun v : ↥s => (v : PL.E N)))
    {A : PL.E N →ᵃ[ℝ] PL.E n} (hinj : Set.InjOn A (PL.simp s)) :
    AffineIndependent ℝ (fun v : ↥s => A v) := by
  classical
  rw [affineIndependent_iff]
  intro t w hw hsum
  set z : ↥s → PL.E N := fun i => (i : PL.E N) with hz
  have hsum' : ∑ i ∈ t, w i • A (z i) = 0 := by simpa only [hz] using hsum
  have hlin : A.linear (∑ i ∈ t, w i • z i) = 0 := by
    rw [← sum_smul_affine_eq_linear A t w z hw]
    exact hsum'
  set wP : ↥s → ℝ := fun i => max (w i) 0 with hwP
  set wM : ↥s → ℝ := fun i => max (-w i) 0 with hwM
  set t₀ : ℝ := ∑ i ∈ t, wP i with ht₀def
  have hMsum : ∑ i ∈ t, wM i = t₀ := by
    have hkey : ∑ i ∈ t, (wP i - wM i) = ∑ i ∈ t, w i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hwP, hwM, max_zero_sub_max_neg_zero_eq_self]
    have h0 : ∑ i ∈ t, wP i - ∑ i ∈ t, wM i = 0 := by
      rw [Finset.sum_sub_distrib] at hkey
      rw [hkey, hw]
    rw [ht₀def]
    linarith
  by_cases ht : t₀ = 0
  · -- all weights vanish
    have hle_all : ∀ j ∈ t, w j ≤ 0 := by
      intro j hj
      have h1 : wP j ≤ t₀ := by
        rw [ht₀def]
        exact Finset.single_le_sum (fun i _ => le_max_right (w i) 0) hj
      have h2 : max (w j) 0 ≤ 0 := by rw [ht] at h1; simpa only [hwP] using h1
      exact le_trans (le_max_left _ _) h2
    intro i hi
    have h3 : -w i ≤ ∑ j ∈ t, -w j := by
      refine Finset.single_le_sum (f := fun j => -w j) (fun j hj => ?_) hi
      linarith [hle_all j hj]
    rw [Finset.sum_neg_distrib, hw, neg_zero] at h3
    have h4 := hle_all i hi
    linarith
  · -- one of the weights is positive: split into positive and negative parts
    have htpos : 0 < t₀ := by
      have hnn : 0 ≤ ∑ i ∈ t, wP i := Finset.sum_nonneg fun i _ => le_max_right _ _
      have hne : ∑ i ∈ t, wP i ≠ 0 := by rw [← ht₀def]; exact ht
      rw [ht₀def]
      exact lt_of_le_of_ne hnn (Ne.symm hne)
    have hp_mem : t.centerMass wP z ∈ PL.simp s := by
      rw [PL.simp]
      refine Finset.centerMass_mem_convexHull t (fun i _ => le_max_right (w i) 0) ?_ (fun i _ => i.2)
      rw [← ht₀def]
      exact htpos
    have hq_mem : t.centerMass wM z ∈ PL.simp s := by
      rw [PL.simp]
      refine Finset.centerMass_mem_convexHull t (fun i _ => le_max_right (-w i) 0) ?_ (fun i _ => i.2)
      rw [hMsum]
      exact htpos
    have hsub : t₀ • (t.centerMass wP z - t.centerMass wM z) = ∑ i ∈ t, w i • z i := by
      have hp' : t₀ • t.centerMass wP z = ∑ i ∈ t, wP i • z i := by
        rw [Finset.centerMass, ← ht₀def, smul_smul, mul_inv_cancel₀ (ne_of_gt htpos), one_smul]
      have hq' : t₀ • t.centerMass wM z = ∑ i ∈ t, wM i • z i := by
        rw [Finset.centerMass, hMsum, smul_smul, mul_inv_cancel₀ (ne_of_gt htpos), one_smul]
      rw [smul_sub, hp', hq', ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [← sub_smul, hwP, hwM, max_zero_sub_max_neg_zero_eq_self]
    have hpq : t.centerMass wP z = t.centerMass wM z := by
      refine hinj hp_mem hq_mem ?_
      have h0 : A.linear (t.centerMass wP z - t.centerMass wM z) = 0 := by
        have h1 : A.linear (t₀ • (t.centerMass wP z - t.centerMass wM z)) = 0 := by
          rw [hsub]
          exact hlin
        rw [map_smul] at h1
        exact (smul_eq_zero.mp h1).resolve_left (ne_of_gt htpos)
      have h2 : A (t.centerMass wP z) - A (t.centerMass wM z) = 0 := by
        rw [← vsub_eq_sub, ← AffineMap.linearMap_vsub A (t.centerMass wP z) (t.centerMass wM z),
          vsub_eq_sub]
        exact h0
      exact sub_eq_zero.mp h2
    have hX : ∑ i ∈ t, w i • z i = 0 := by
      rw [← hsub, hpq, sub_self, smul_zero]
    intro i hi
    exact hind.eq_zero_of_sum_eq_zero hw (by simpa only [hz] using hX) i hi

end Work.Engulf.E4Aux
