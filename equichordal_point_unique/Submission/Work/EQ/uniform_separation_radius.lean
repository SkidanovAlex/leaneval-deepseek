import Mathlib

namespace Work.EQ

/-- **Uniform separation radius from finitely many pointwise ones.** If for every `k`-th root of
unity `ω ≠ 1` there is a radius `δ_ω > 0` with `δ_ω ≤ ρ` such that `P ω t` holds for every
`0 < ‖t‖ < δ_ω`, then there is a single `δ > 0`, `δ ≤ ρ` working for all `ω` simultaneously.
The set of `k`-th roots of unity is finite as `k > 0`. -/
lemma uniform_separation_radius {k : ℕ} (hk : 0 < k) {ρ : ℝ} (hρ : 0 < ρ) {P : ℂ → ℂ → Prop}
    (h : ∀ ω : ℂ, ω ^ k = 1 → ω ≠ 1 → ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < δ → P ω t) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ ω : ℂ, ω ^ k = 1 → ω ≠ 1 →
      ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < δ → P ω t := by
  classical
  -- The finite set of `k`-th roots of unity different from `1`.
  let A : Finset ℂ := (Polynomial.nthRoots k (1 : ℂ)).toFinset.filter (fun ω => ω ≠ 1)
  have hA_root : ∀ ω ∈ A, ω ^ k = 1 := by
    intro ω hω
    have hω' : ω ∈ (Polynomial.nthRoots k (1 : ℂ)).toFinset.filter (fun ω => ω ≠ 1) := hω
    exact (Polynomial.mem_nthRoots hk).mp
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hω').1)
  have hA_ne : ∀ ω ∈ A, ω ≠ 1 := by
    intro ω hω
    have hω' : ω ∈ (Polynomial.nthRoots k (1 : ℂ)).toFinset.filter (fun ω => ω ≠ 1) := hω
    exact (Finset.mem_filter.mp hω').2
  -- A chosen radius for each complex number (default `ρ`).
  let d : ℂ → ℝ := fun ω =>
    if hω : ω ^ k = 1 ∧ ω ≠ 1 then Classical.choose (h ω hω.1 hω.2) else ρ
  have hd : ∀ ω : ℂ, ω ^ k = 1 → ω ≠ 1 →
      0 < d ω ∧ d ω ≤ ρ ∧ ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < d ω → P ω t := by
    intro ω h1 hne
    have hdω : d ω = Classical.choose (h ω h1 hne) := by
      simp only [d]
      exact dite_eq_left ⟨h1, hne⟩
    rw [hdω]
    exact Classical.choose_spec (h ω h1 hne)
  -- The finite set of radii, including the global bound `ρ`.
  let vals : Finset ℝ := insert ρ (A.image d)
  have hne' : vals.Nonempty := Finset.insert_nonempty _ _
  refine ⟨vals.min' hne', ?_, ?_, ?_⟩
  · rw [Finset.lt_min'_iff]
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb''
    · exact hρ
    · rcases Finset.mem_image.mp hb'' with ⟨ω, hω, hωd⟩
      rw [← hωd]
      exact (hd ω (hA_root ω hω) (hA_ne ω hω)).1
  · have hρmem : ρ ∈ vals := Finset.mem_insert_self ρ (A.image d)
    exact Finset.min'_le vals ρ hρmem
  · intro ω h1 hne'' t ht0 htlt
    have hmemA : ω ∈ A := by
      have h1' : ω ∈ (Polynomial.nthRoots k (1 : ℂ)).toFinset :=
        Multiset.mem_toFinset.mpr ((Polynomial.mem_nthRoots hk).mpr h1)
      exact Finset.mem_filter.mpr ⟨h1', hne''⟩
    have hdmem : d ω ∈ A.image d := Finset.mem_image.mpr ⟨ω, hmemA, rfl⟩
    have hle : vals.min' hne' ≤ d ω :=
      Finset.min'_le vals (d ω) (Finset.mem_insert_of_mem hdmem)
    exact (hd ω h1 hne'').2.2 t ht0 (lt_of_lt_of_le htlt hle)

end Work.EQ
