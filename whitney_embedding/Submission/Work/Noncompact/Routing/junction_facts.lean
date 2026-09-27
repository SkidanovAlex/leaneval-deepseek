import Mathlib
import Submission.Work.Noncompact.Routing.seed_shell

/-!
# The level facts about the spine's seeds (the junctions of the line construction)

The junctions of the line construction inside a canal are the spine's seeds `q b m`.  For the
construction one needs, at every level `m > lev b`:

* `q b m ∈ D b m` (the seed lies in the region of its own level) and
  `q b m ∉ closure (D b (m+2))` — this is `nc_seed_junction`;
* `q b m ∉ closure (D b (m+1))` — so that an *offset-1* chart ball at the seed exists
  (`nc_shell_chartBall`): `q b m ∈ interior (K (m+1))` while `D b (m+1) ⊆ (K (m+1))ᶜ`;
* `q b m ∉ D b (m+1)` (the seed is *outside* the next region: with the offset-1 access ball the
  access part of a piece never meets the next region, which is what makes the trace of a piece in
  the next region exactly its terminal straight germ).
-/

namespace Work.Noncompact.Routing

open Set Topology
open Work.Noncompact.CompressionTube

variable {M : Type*} [TopologicalSpace M]

/-- **A point of `interior K` is not in the closure of a set contained in `Kᶜ`.** -/
theorem notMem_closure_of_mem_interior_of_subset_compl {K S : Set M} {x : M}
    (hx : x ∈ interior K) (hS : S ⊆ Kᶜ) : x ∉ closure S := by
  intro hcl
  obtain ⟨y, hyK, hyS⟩ := mem_closure_iff.mp hcl (interior K) isOpen_interior hx
  exact hS hyS (interior_subset hyK)

/-- **The level facts about the spine's seeds.**  For `m > lev b` the seed `q b m` lies in the
region `D b m`, outside the *next* region `D b (m+1)`, and outside the closures of both
`D b (m+1)` and `D b (m+2)`. -/
theorem nc_seed_shell_facts {K : ℕ → Set M} (hKmono : Monotone K) {B : Set M} {lev : B → ℕ}
    {q : B → ℕ → M} {γ : B → ℕ → ℝ → M} (h : SpineData K B lev q γ)
    {D : B → ℕ → Set M} (hDK : ∀ (b : B) i, D b i ⊆ (K i)ᶜ)
    (htail : ∀ (b : B) (i : ℕ), lev b ≤ i →
      (⋃ j : {j : ℕ // i ≤ j}, γ b (j : ℕ) '' Set.Icc (0:ℝ) 1) ⊆ D b i)
    {b : B} {m : ℕ} (hm : lev b + 1 ≤ m) :
    q b m ∈ D b m ∧ q b m ∉ closure (D b (m + 1)) ∧
      q b m ∉ closure (D b (m + 2)) ∧ q b m ∉ D b (m + 1) := by
  have hlevlt : lev b < m := by omega
  obtain ⟨hqD, hqcl2⟩ := nc_seed_junction (M := M) hKmono h hDK htail hm
  have hqint : q b m ∈ interior (K (m + 1)) := (h.q_shell b m hlevlt).1
  refine ⟨hqD, ?_, hqcl2, ?_⟩
  · exact notMem_closure_of_mem_interior_of_subset_compl hqint (hDK b (m + 1))
  · intro hmem
    exact (hDK b (m + 1) hmem) (interior_subset hqint)

end Work.Noncompact.Routing
