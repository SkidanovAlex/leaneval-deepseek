import Mathlib

namespace Work.A3.Weil

/-- Membership in the `piFinset` for a tuple obtained by appending one entry with `Fin.snoc`:
appending `h` to `l` lands in the `piFinset` over `Fin (n+1)` exactly when `l` lands in the
`piFinset` over `Fin n` and `h ∈ s`. -/
lemma mem_piFinset_snoc {n : ℕ} {s : Finset ℤ} {l : Fin n → ℤ} {h : ℤ} :
    Fin.snoc l h ∈ Fintype.piFinset (fun _ : Fin (n + 1) => s) ↔
      l ∈ Fintype.piFinset (fun _ : Fin n => s) ∧ h ∈ s := by
  simp only [Fintype.mem_piFinset]
  constructor
  · intro H
    exact ⟨fun i => by simpa using H i.castSucc, by simpa using H (Fin.last n)⟩
  · rintro ⟨Hl, Hh⟩ i
    cases i using Fin.lastCases with
    | last => simpa using Hh
    | cast j => simpa using Hl j

theorem sum_piFinset_snoc (n : ℕ) (s : Finset ℤ) (g : (Fin (n + 1) → ℤ) → ℝ) :
    ∑ l ∈ Fintype.piFinset (fun _ : Fin n => s), ∑ h ∈ s, g (Fin.snoc (α := fun _ => ℤ) l h)
      = ∑ l ∈ Fintype.piFinset (fun _ : Fin (n + 1) => s), g l := by
  classical
  rw [← Finset.sum_product']
  refine Finset.sum_nbij'
    (fun p : (Fin n → ℤ) × ℤ => Fin.snoc (α := fun _ => ℤ) p.1 p.2)
    (fun m : Fin (n + 1) → ℤ => (fun i : Fin n => m i.castSucc, m (Fin.last n)))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨l, h⟩ hp
    exact mem_piFinset_snoc.2 ⟨(Finset.mem_product.1 hp).1, (Finset.mem_product.1 hp).2⟩
  · intro m hm
    have hm' : ∀ a : Fin (n + 1), m a ∈ s := Fintype.mem_piFinset.1 hm
    exact Finset.mem_product.2 ⟨Fintype.mem_piFinset.2 (fun i : Fin n => hm' i.castSucc),
      hm' (Fin.last n)⟩
  · rintro ⟨l, h⟩ hp
    simp
  · intro m hm
    exact Fin.snoc_init_self m
  · rintro ⟨l, h⟩ hp
    rfl

end Work.A3.Weil
