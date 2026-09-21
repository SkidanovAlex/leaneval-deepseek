import Mathlib

namespace Work.Odd

open Set

/-- For a set `K` in an additive commutative group and a point `p`, the translate
`{x - p | x ∈ K}` agrees with its reflection through the origin
`{-(x - p) | x ∈ K}` if and only if `K` is symmetric about `p`, that is,
`x ∈ K ↔ 2 • p - x ∈ K` for every `x`. -/
lemma image2_sub_singleton_eq_neg_iff_nsmul {G : Type*} [AddCommGroup G]
    {K : Set G} {p : G} :
    Set.image2 (fun x y : G => x - y) K ({p} : Set G) =
      (fun x : G => -x) '' Set.image2 (fun x y : G => x - y) K ({p} : Set G) ↔
      ∀ x : G, (x ∈ K ↔ (2 : ℕ) • p - x ∈ K) := by
  have hmem : ∀ z : G, z ∈ Set.image2 (fun x y : G => x - y) K ({p} : Set G) ↔
      ∃ x ∈ K, x - p = z := by
    intro z
    rw [Set.mem_image2]
    constructor
    · rintro ⟨a, ha, b, hb, hab⟩
      rw [Set.mem_singleton_iff] at hb
      exact ⟨a, ha, by simpa [hb] using hab⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a, ha, p, rfl, rfl⟩
  constructor
  · intro h x
    have himp : ∀ z : G, z ∈ K → (2 : ℕ) • p - z ∈ K := by
      intro z hz
      have h1 : -(z - p) ∈ (fun x : G => -x) ''
          Set.image2 (fun x y : G => x - y) K ({p} : Set G) :=
        ⟨z - p, (hmem _).mpr ⟨z, hz, rfl⟩, rfl⟩
      rw [← h] at h1
      rcases (hmem _).mp h1 with ⟨y, hy, hyy⟩
      have hyy' : y = -(z - p) + p := (sub_eq_iff_eq_add).mp hyy
      have hy2 : y = (2 : ℕ) • p - z := by rw [hyy']; abel
      rwa [hy2] at hy
    exact ⟨himp x, fun hx => by
      have h2 := himp ((2 : ℕ) • p - x) hx
      rwa [show (2 : ℕ) • p - ((2 : ℕ) • p - x) = x by abel] at h2⟩
  · intro H
    apply Set.Subset.antisymm
    · intro z hz
      rcases (hmem _).mp hz with ⟨x, hx, rfl⟩
      exact ⟨p - x,
        (hmem _).mpr ⟨(2 : ℕ) • p - x, (H x).mp hx, by abel⟩, by abel⟩
    · intro z hz
      rw [Set.mem_image] at hz
      rcases hz with ⟨w, hw, hwz⟩
      rcases (hmem _).mp hw with ⟨x, hx, rfl⟩
      rw [← hwz]
      exact (hmem _).mpr ⟨(2 : ℕ) • p - x, (H x).mp hx, by abel⟩

lemma sub_singleton_eq_neg_iff {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))}
    {p : EuclideanSpace ℝ (Fin d)} :
    Set.image2 (fun x y : EuclideanSpace ℝ (Fin d) => x - y) K ({p} : Set (EuclideanSpace ℝ (Fin d))) =
      (fun x : EuclideanSpace ℝ (Fin d) => -x) ''
        Set.image2 (fun x y : EuclideanSpace ℝ (Fin d) => x - y) K
          ({p} : Set (EuclideanSpace ℝ (Fin d))) ↔
      ∀ x : EuclideanSpace ℝ (Fin d), (x ∈ K ↔ (2 : ℝ) • p - x ∈ K) := by
  rw [show (2 : ℝ) • p = (2 : ℕ) • p by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num]
        exact Nat.cast_smul_eq_nsmul ℝ (M := EuclideanSpace ℝ (Fin d)) 2 p]
  exact image2_sub_singleton_eq_neg_iff_nsmul (K := K) (p := p)

end Work.Odd
