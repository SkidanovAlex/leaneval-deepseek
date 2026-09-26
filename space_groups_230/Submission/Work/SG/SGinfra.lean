import Submission.Work.SG.SGprelude

/-! Closure bookkeeping for `sgClose` (the `ℚ`-side breadth-first closure of `Defs`).
Nothing here is computational: `List.mem_dedup` turns `dedup` into set operations. -/

namespace Work.SG

/-- One closure round on the `ℚ`-side affine pairs. -/
def sgF (gens acc : List (List ℤ × List ℚ)) : List (List ℤ × List ℚ) :=
  (acc ++ acc.flatMap fun a => gens.map fun g => sgMulPair a g).dedup

theorem sgClose_eq_iterate (gens acc : List (List ℤ × List ℚ)) (k : ℕ) :
    sgClose gens k acc = (sgF gens)^[k] acc := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
      rw [show sgClose gens (k + 1) acc = sgClose gens k (sgF gens acc) from rfl]
      rw [ih (sgF gens acc)]
      exact (Function.iterate_succ_apply (f := sgF gens) (n := k) (x := acc)).symm

theorem sgClose_succ (gens acc : List (List ℤ × List ℚ)) (k : ℕ) :
    sgClose gens (k + 1) acc = sgF gens (sgClose gens k acc) := by
  rw [sgClose_eq_iterate, sgClose_eq_iterate, Function.iterate_succ_apply']

theorem mem_sgF {gens acc : List (List ℤ × List ℚ)} {p : List ℤ × List ℚ} :
    p ∈ sgF gens acc ↔ p ∈ acc ∨ ∃ a ∈ acc, ∃ g ∈ gens, sgMulPair a g = p := by
  simp only [sgF, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_map]

theorem mem_sgClose_succ {gens acc : List (List ℤ × List ℚ)} {p : List ℤ × List ℚ} {k : ℕ} :
    p ∈ sgClose gens (k + 1) acc ↔ p ∈ sgF gens (sgClose gens k acc) := by
  rw [sgClose_succ]

theorem sgClose_mono_acc {gens acc acc' : List (List ℤ × List ℚ)}
    (h : ∀ x, x ∈ acc → x ∈ acc') :
    ∀ (k : ℕ) {x : List ℤ × List ℚ}, x ∈ sgClose gens k acc → x ∈ sgClose gens k acc' := by
  intro k
  induction k with
  | zero => intro x hx; exact h x hx
  | succ k ih =>
      intro x hx
      rw [mem_sgClose_succ, mem_sgF] at hx ⊢
      rcases hx with hx | ⟨a, ha, g, hg, h⟩
      · exact Or.inl (ih hx)
      · exact Or.inr ⟨a, ih ha, g, hg, h⟩

theorem mem_sgClose_self {gens acc : List (List ℤ × List ℚ)} :
    ∀ (k : ℕ) {x : List ℤ × List ℚ}, x ∈ acc → x ∈ sgClose gens k acc := by
  intro k
  induction k with
  | zero => intro x hx; exact hx
  | succ k ih =>
      intro x hx
      rw [mem_sgClose_succ, mem_sgF]
      exact Or.inl (ih hx)

theorem sgClose_le_succ {gens acc : List (List ℤ × List ℚ)} :
    ∀ (k : ℕ) {x : List ℤ × List ℚ}, x ∈ sgClose gens k acc → x ∈ sgClose gens (k + 1) acc := by
  intro k
  induction k with
  | zero =>
      intro x hx
      rw [mem_sgClose_succ, mem_sgF]
      exact Or.inl hx
  | succ k ih =>
      intro x hx
      rw [mem_sgClose_succ, mem_sgF] at hx ⊢
      rcases hx with hx | ⟨a, ha, g, hg, h⟩
      · exact Or.inl (ih hx)
      · exact Or.inr ⟨a, ih ha, g, hg, h⟩

theorem sgClose_mono_fuel {gens acc : List (List ℤ × List ℚ)} {k k' : ℕ} (h : k ≤ k')
    {x : List ℤ × List ℚ} : x ∈ sgClose gens k acc → x ∈ sgClose gens k' acc := by
  induction h with
  | refl => exact id
  | step _ ih => exact fun hx => sgClose_le_succ _ (ih hx)

theorem sgClose_subset_of_closed {gens acc : List (List ℤ × List ℚ)} {S : Set (List ℤ × List ℚ)}
    (hacc : ∀ x, x ∈ acc → x ∈ S) (hcl : ∀ a, a ∈ S → ∀ g, g ∈ gens → sgMulPair a g ∈ S) :
    ∀ (k : ℕ) {x : List ℤ × List ℚ}, x ∈ sgClose gens k acc → x ∈ S := by
  intro k
  induction k with
  | zero => intro x hx; exact hacc x hx
  | succ k ih =>
      intro x hx
      rw [mem_sgClose_succ, mem_sgF] at hx
      rcases hx with hx | ⟨a, ha, g, hg, h⟩
      · exact ih hx
      · exact h ▸ hcl a (ih ha) g hg

theorem sgOne_mem_sgClose (gens : List (List ℤ × List ℚ)) (k : ℕ) :
    sgOne ∈ sgClose gens k [sgOne] := mem_sgClose_self k (List.mem_singleton_self sgOne)

/-! ### The integer-side mirror -/

theorem zClose_eq_iterate (gens : List (List ℤ × List ℤ)) (d : ℕ)
    (acc : List (List ℤ × List ℤ)) (k : ℕ) :
    zClose gens d k acc = (zF gens d)^[k] acc := by
  induction k generalizing acc with
  | zero => rfl
  | succ k ih =>
      rw [show zClose gens d (k + 1) acc = zClose gens d k (zF gens d acc) from rfl]
      rw [ih (zF gens d acc)]
      exact (Function.iterate_succ_apply (f := zF gens d) (n := k) (x := acc)).symm

theorem zClose_succ (gens : List (List ℤ × List ℤ)) (d : ℕ)
    (acc : List (List ℤ × List ℤ)) (k : ℕ) :
    zClose gens d (k + 1) acc = zF gens d (zClose gens d k acc) := by
  rw [zClose_eq_iterate, zClose_eq_iterate, Function.iterate_succ_apply']

theorem mem_zF {gens acc : List (List ℤ × List ℤ)} {d : ℕ} {p : List ℤ × List ℤ} :
    p ∈ zF gens d acc ↔ p ∈ acc ∨ ∃ a ∈ acc, ∃ g ∈ gens, zMul d a g = p := by
  simp only [zF, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_map]

theorem mem_zClose_succ {gens acc : List (List ℤ × List ℤ)} {d : ℕ} {p : List ℤ × List ℤ}
    {k : ℕ} : p ∈ zClose gens d (k + 1) acc ↔ p ∈ zF gens d (zClose gens d k acc) := by
  rw [zClose_succ]

theorem mem_zClose_self {gens acc : List (List ℤ × List ℤ)} {d : ℕ} :
    ∀ (k : ℕ) {x : List ℤ × List ℤ}, x ∈ acc → x ∈ zClose gens d k acc := by
  intro k
  induction k with
  | zero => intro x hx; exact hx
  | succ k ih =>
      intro x hx
      rw [mem_zClose_succ, mem_zF]
      exact Or.inl (ih hx)

theorem zClose_mono_fuel {gens acc : List (List ℤ × List ℤ)} {d : ℕ} {k k' : ℕ} (h : k ≤ k')
    {x : List ℤ × List ℤ} : x ∈ zClose gens d k acc → x ∈ zClose gens d k' acc := by
  have hle : ∀ (j : ℕ) {y : List ℤ × List ℤ}, y ∈ zClose gens d j acc →
      y ∈ zClose gens d (j + 1) acc := by
    intro j y hy
    rw [mem_zClose_succ, mem_zF]
    exact Or.inl hy
  induction h with
  | refl => exact id
  | step _ ih => exact fun hx => hle _ (ih hx)

theorem zClose_subset_of_closed {gens acc : List (List ℤ × List ℤ)} {d : ℕ}
    {S : Set (List ℤ × List ℤ)}
    (hacc : ∀ x, x ∈ acc → x ∈ S) (hcl : ∀ a, a ∈ S → ∀ g, g ∈ gens → zMul d a g ∈ S) :
    ∀ (k : ℕ) {x : List ℤ × List ℤ}, x ∈ zClose gens d k acc → x ∈ S := by
  intro k
  induction k with
  | zero => intro x hx; exact hacc x hx
  | succ k ih =>
      intro x hx
      rw [mem_zClose_succ, mem_zF] at hx
      rcases hx with hx | ⟨a, ha, g, hg, h⟩
      · exact ih hx
      · exact h ▸ hcl a (ih ha) g hg

end Work.SG
