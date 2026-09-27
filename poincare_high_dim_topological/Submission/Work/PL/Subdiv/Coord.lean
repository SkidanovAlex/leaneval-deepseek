import Submission.Work.PL.Subdiv.Defs

/-!
# Coordinates of points of a simplex, and barycenter bookkeeping

This file is the linear-algebraic engine of the barycentric subdivision
(`Submission.Work.PL.Subdiv.SdBasic`).

* `sum_smul_bary_eq_sum_smul`: a sum `∑ c ρ • bary ρ` over a family of faces contained in a
  face `τ` is a linear combination of the vertices of `τ`.
* `sum_coeff_filter`: the coefficient sums agree.
* `exists_sum_smul_of_mem_simp`: a point of `simp B` is a convex combination of the vertices of `B`.
* `coords_eq_zero_of_mem_simp_subset`: if the point also lies in `simp B'` for a sub-face
  `B' ⊆ B`, then the coordinates outside `B'` vanish.
-/

open Set Metric
open scoped BigOperators
open PL

namespace Work.PL.Subdiv

noncomputable section

variable {N : ℕ}

/-- `c • bary ρ` as a sum over the vertices of `ρ`. -/
lemma smul_bary_eq_sum (ρ : Finset (E N)) (c : ℝ) :
    c • bary ρ = ∑ v ∈ ρ, (c / (ρ.card : ℝ)) • v := by
  rw [bary_eq_smul_sum, smul_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [div_eq_mul_inv]

/-- A sum of barycenters of faces contained in `τ`, expressed in the vertices of `τ`. -/
lemma sum_smul_bary_eq_sum_smul (C : Finset (Finset (E N))) (τ : Finset (E N))
    (h : ∀ ρ ∈ C, ρ ⊆ τ) (c : Finset (E N) → ℝ) :
    (∑ ρ ∈ C, c ρ • bary ρ)
      = ∑ v ∈ τ, (∑ ρ ∈ C.filter (fun ρ => v ∈ ρ), c ρ / (ρ.card : ℝ)) • v := by
  have hregroup := Finset.sum_comm'
    (s := C) (t := fun ρ : Finset (E N) => ρ) (t' := τ)
    (s' := fun v : E N => C.filter (fun ρ => v ∈ ρ))
    (f := fun ρ v => (c ρ / (ρ.card : ℝ)) • v)
    (fun ρ v => ⟨fun ⟨hρ, hv⟩ =>
        ⟨Finset.mem_filter.mpr ⟨hρ, hv⟩, h ρ hρ hv⟩,
      fun ⟨hv, _⟩ => ⟨(Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩⟩)
  rw [Finset.sum_congr rfl fun ρ _ => smul_bary_eq_sum ρ (c ρ), hregroup]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_smul]

/-- The coefficient sums of `sum_smul_bary_eq_sum_smul` agree. -/
lemma sum_coeff_filter (C : Finset (Finset (E N))) (τ : Finset (E N))
    (h : ∀ ρ ∈ C, ρ ⊆ τ) (hne : ∀ ρ ∈ C, ρ.Nonempty) (c : Finset (E N) → ℝ) :
    (∑ v ∈ τ, ∑ ρ ∈ C.filter (fun ρ => v ∈ ρ), c ρ / (ρ.card : ℝ)) = ∑ ρ ∈ C, c ρ := by
  have hregroup := (Finset.sum_comm'
    (s := C) (t := fun ρ : Finset (E N) => ρ) (t' := τ)
    (s' := fun v : E N => C.filter (fun ρ => v ∈ ρ))
    (f := fun ρ v => c ρ / (ρ.card : ℝ))
    (fun ρ v => ⟨fun ⟨hρ, hv⟩ =>
        ⟨Finset.mem_filter.mpr ⟨hρ, hv⟩, h ρ hρ hv⟩,
      fun ⟨hv, _⟩ => ⟨(Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩⟩)).symm
  rw [hregroup]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  have hcard : (ρ.card : ℝ) ≠ 0 := by
    simp only [Nat.cast_ne_zero]
    exact Finset.card_ne_zero.mpr (hne ρ hρ)
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [div_eq_mul_inv, mul_comm (↑ρ.card : ℝ), mul_assoc, inv_mul_cancel₀ hcard, mul_one]

/-- A point of the simplex on `B` is a convex combination of the vertices of `B`. -/
lemma exists_sum_smul_of_mem_simp {B : Finset (E N)} {x : E N} (hx : x ∈ simp B) :
    ∃ a : E N → ℝ, (∀ v ∈ B, 0 ≤ a v) ∧ (∑ v ∈ B, a v) = 1 ∧ (∑ v ∈ B, a v • v) = x ∧
      ∀ v, v ∉ B → a v = 0 := by
  obtain ⟨ι, hι, w, z, hw0, hw1, hz, hzx⟩ := mem_convexHull_iff_exists_fintype.mp hx
  classical
  letI := hι
  refine ⟨fun v => ∑ i ∈ (Finset.univ.filter (fun i => z i = v)), w i, ?_, ?_, ?_, ?_⟩
  · intro v _
    exact Finset.sum_nonneg fun i _ => hw0 i
  · have hfib := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset ι)) (t := B)
      (g := z) (fun i _ => Finset.mem_coe.mp (hz i)) w
    rw [hfib]
    exact hw1
  · have hfib := Finset.sum_fiberwise_of_maps_to (s := (Finset.univ : Finset ι)) (t := B)
      (g := z) (fun i _ => Finset.mem_coe.mp (hz i)) (fun i => w i • z i)
    rw [← hzx, ← hfib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun i hi => by rw [(Finset.mem_filter.mp hi).2]
  · intro v hv
    change (∑ i ∈ Finset.univ.filter (fun i => z i = v), w i) = 0
    rw [show Finset.univ.filter (fun i => z i = v) = ∅ from Finset.filter_eq_empty_iff.mpr
      (fun i _ hiz => hv (hiz ▸ Finset.mem_coe.mp (hz i)))]
    exact Finset.sum_empty

/-- Uniqueness of the coordinates of a point on an affinely independent vertex set. -/
lemma coords_unique_of_affineIndependent {B : Finset (E N)}
    (hB : AffineIndependent ℝ ((↑) : B → E N)) {a a' : E N → ℝ}
    (h1 : (∑ v ∈ B, a v) = ∑ v ∈ B, a' v)
    (h2 : (∑ v ∈ B, a v • v) = ∑ v ∈ B, a' v • v) : ∀ v ∈ B, a v = a' v :=
  AffineIndependent.eq_of_sum_eq_sum_subtype hB h1 h2

/-- If a point of `simp B` lies in `simp B'` for a sub-face `B' ⊆ B` (`B` affinely independent),
then its coordinates outside `B'` vanish. -/
lemma coords_eq_zero_of_mem_simp_subset {B B' : Finset (E N)} (hB' : B' ⊆ B)
    (hB : AffineIndependent ℝ ((↑) : B → E N)) {x : E N} {a : E N → ℝ}
    (_ha0 : ∀ v ∈ B, 0 ≤ a v) (hasum : (∑ v ∈ B, a v) = 1) (hax : (∑ v ∈ B, a v • v) = x)
    (hx : x ∈ simp B') : ∀ v ∈ B, v ∉ B' → a v = 0 := by
  obtain ⟨a', ha'0, ha'sum, ha'x, ha'out⟩ := exists_sum_smul_of_mem_simp hx
  have hsum' : (∑ v ∈ B, a' v) = 1 := by
    rw [← Finset.sum_subset hB' (fun v _ hv => ha'out v hv)]
    exact ha'sum
  have hpt' : (∑ v ∈ B, a' v • v) = x := by
    rw [← Finset.sum_subset hB' (fun v _ hv => by rw [ha'out v hv, zero_smul])]
    exact ha'x
  intro v hv hvB'
  have hvv : a v = a' v := by
    refine coords_unique_of_affineIndependent hB ?_ ?_ v hv
    · calc (∑ v ∈ B, a v) = 1 := hasum
        _ = ∑ v ∈ B, a' v := hsum'.symm
    · calc (∑ v ∈ B, a v • v) = x := hax
        _ = ∑ v ∈ B, a' v • v := hpt'.symm
  rw [hvv]
  exact ha'out v hvB'

end

end Work.PL.Subdiv
