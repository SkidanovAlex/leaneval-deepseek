import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.lr_mixing
import Submission.Work.LT.lr_slice_bound
import Submission.Work.LT.hammingNorm_triple
import Submission.Work.LT.nonzero_view_rows

/-! Guidance from the project lead (the requester):

FULL ROUTE: read Submission/Work/LT/DESIGN.md first (the orchestrator's design; your lemma is one node of its DAG). Shared definitions: Submission/Work/LT/Defs.lean (namespace Work.LT) — do NOT edit it; if you need a new shared definition, put it in your own file. Siblings are being proved in parallel; import them when they land.

# lr_distance — guidance

DELLM Lem 4.4 in the quadripartite complex (only the right walk of `B` is used).

1. If `δ0 < μ` or `δ0 ≤ 0` the bound is `≤ 0`: done. Assume `0 ≤ μ ≤ δ0`.
2. `f ≠ 0` ⇒ some `x₀` with `f x₀ ≠ 0`; the 00-view at `x₀.1` is a nonzero element of `CA ⊗ CB`,
   so some column is a nonzero `CA`-word, so at least `δ0 Δ` rows `i` of that view are nonzero.
3. For such `i`, set `F_i : G × Fin Δ → 𝔽₂`, `F_i (g, j) = f (g, i, j)` — "edge `g — g * B j`" of
   the bipartite graph (left copy = type-00 vertices, right copy = type-01 vertices).
   Row `i` of the 00-view at `g` is `j ↦ F_i (g, j)`; row `i` of the 01-view at `h` is
   `j ↦ F_i (h * (B j)⁻¹, j)` (`lrSq` with `β = 1`). Both lie in `CB`.
   Let `S` = left vertices touching `supp F_i`, `T` = right vertices touching it. Each vertex of
   `S` (resp. `T`) carries `≥ δ0 Δ` support edges ⇒ `|supp| ≥ δ0 Δ max(|S|,|T|) ≥ δ0 Δ √(|S||T|)`.
4. **Bipartite expander mixing** from `rightExpander B μ`: `e(S,T) = Σ_g 1_S g Σ_j 1_T (g * B j)
   ≤ Δ |S||T|/|G| + μ Δ √(|S||T|)` (split `1_T` into mean + mean-zero part, Cauchy–Schwarz).
   With `s = √(|S||T|)/|G|`: `δ0 s ≤ s² + μ s` ⇒ `s ≥ δ0 - μ` ⇒ `|supp F_i| ≥ δ0 (δ0-μ) |G| Δ`.
   (Work with `|S||T|` squared forms to avoid `Real.sqrt` if convenient.)
5. Sum over the `≥ δ0 Δ` good `i` (the slices are disjoint pieces of `supp f`).

Expected size: 300–500 lines.
-/

/-! Implementation notes (prover of `lr_distance`).

The proof is assembled from three parallel pieces, all of them in namespace `Work.LT`:

* `nonzero_view_rows` (step 2): a nonzero codeword has a type-00 view with `≥ δ0 Δ` nonzero rows;
* `hammingNorm_triple`: the weight of a word on `G × Fin Δ × Fin Δ` is the sum of the weights of
  its middle-index slices;
* `lr_slice_bound` (steps 3–4, DELLM Lemma 4.4 for one slice, which itself uses the bipartite
  expander mixing `lr_mixing`): a slice whose rows *and* anti-rows are words of `CB` has support
  `≥ δ0 (δ0 - μ) |G| Δ` once it is nonzero.

Locally we only need the two "view membership" facts `row_mem_CB` and `row01_mem_CB` (row `i` of
the type-00 view at `g`, resp. of the type-01 view at `h`, lies in `CB`), the sign case
`¬ (μ ≤ δ0)` (where the claimed bound is `≤ 0`), and the arithmetic of the final summation. -/

namespace Work.LT

/-- Row `i` of the local view at the type-00 vertex `g` is `j ↦ f (g, i, j)`, and lies in `CB`
(the rows of `tensorCode CA CB` are the `CB`-words). -/
lemma row_mem_CB {G : Type} [Group G] {Δ : ℕ} (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) {f : G × Fin Δ × Fin Δ → ZMod 2}
    (hf : f ∈ lrCode A B CA CB) (g : G) (i : Fin Δ) :
    (fun j : Fin Δ => f (g, i, j)) ∈ CB := by
  have hmem := hf
  rw [lrCode] at hmem
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hmem
  have h1 := hmem 0 0 g
  rw [tensorCode] at h1
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at h1
  have h2 := h1.1 i
  convert h2 using 2
  simp [lrView, lrSq]

/-- Row `i` of the local view at the type-01 vertex `h` is `j ↦ f (h * (B j)⁻¹, i, j)` (the
square `lrSq A B 0 1 h i j` has type-01 vertex `h`), and lies in `CB`. -/
lemma row01_mem_CB {G : Type} [Group G] {Δ : ℕ} (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) {f : G × Fin Δ × Fin Δ → ZMod 2}
    (hf : f ∈ lrCode A B CA CB) (h : G) (i : Fin Δ) :
    (fun j : Fin Δ => f (h * (B j)⁻¹, i, j)) ∈ CB := by
  have hmem := hf
  rw [lrCode] at hmem
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hmem
  have h1 := hmem 0 1 h
  rw [tensorCode] at h1
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at h1
  have h2 := h1.1 i
  convert h2 using 2
  simp [lrView, lrSq]

/-- **Distance** (DELLM Lem 4.4, bipartite form). Every nonzero codeword has weight
`≥ δ0² (δ0 - μ) |G| Δ²`: a nonzero local view has `≥ δ0 Δ` nonzero rows `i`; for each such `i`
the slice `(g, j) ↦ f (g, i, j)` is a nonzero Tanner codeword (local code `CB`) on the bipartite
graph `g — g * B j`, which has `≥ δ0 (δ0 - μ) |G| Δ` nonzero edges by expander mixing. -/
theorem lr_distance {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (δ0 μ : ℝ) (hμ : 0 ≤ μ)
    (hB : rightExpander B μ)
    (hdA : ∀ x ∈ CA, x ≠ 0 → δ0 * Δ ≤ hammingNorm x)
    (hdB : ∀ x ∈ CB, x ≠ 0 → δ0 * Δ ≤ hammingNorm x) :
    ∀ f ∈ lrCode A B CA CB, f ≠ 0 →
      δ0 ^ 2 * (δ0 - μ) * (Fintype.card G * Δ * Δ) ≤ hammingNorm f := by
  intro f hf hfne
  -- `Δ = 0`: the code lives on an empty set of squares, the bound is `0 ≤ weight`.
  by_cases hΔ0 : Δ = 0
  · subst hΔ0
    simp
  · by_cases hcase : μ ≤ δ0
    · -- Main case `0 ≤ μ ≤ δ0`.  Pick a nonzero local view with `≥ δ0 Δ` nonzero rows.
      obtain ⟨g₀, hg₀⟩ := nonzero_view_rows A B CA CB δ0 hdA f hf hfne
      set I : Finset (Fin Δ) :=
        Finset.univ.filter (fun i : Fin Δ => (fun j : Fin Δ => f (g₀, i, j)) ≠ 0) with hI
      have hIc : δ0 * (Δ : ℝ) ≤ (I.card : ℝ) := hg₀
      have hc_nonneg : 0 ≤ δ0 * (δ0 - μ) * ((Fintype.card G : ℝ) * (Δ : ℝ)) :=
        mul_nonneg (mul_nonneg (le_trans hμ hcase) (sub_nonneg.mpr hcase))
          (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      -- Each good row `i` gives a nonzero slice whose rows and anti-rows lie in `CB`.
      have hslice : ∀ i ∈ I, δ0 * (δ0 - μ) * ((Fintype.card G : ℝ) * (Δ : ℝ)) ≤
          (hammingNorm (fun p : G × Fin Δ => f (p.1, i, p.2)) : ℝ) := by
        intro i hi
        have hne : (fun j : Fin Δ => f (g₀, i, j)) ≠ 0 := by
          rw [hI, Finset.mem_filter] at hi
          exact hi.2
        have hw : (fun p : G × Fin Δ => f (p.1, i, p.2)) ≠ 0 := by
          intro hcon
          obtain ⟨j, hj⟩ := Function.ne_iff.mp hne
          exact hj (by simpa using congrFun hcon (g₀, j))
        exact lr_slice_bound B CB δ0 μ hμ hcase hB hdB _
          (fun g => row_mem_CB A B CA CB hf g i)
          (fun h => row01_mem_CB A B CA CB hf h i) hw (Nat.pos_of_ne_zero hΔ0)
      -- Sum the per-slice bounds over the `≥ δ0 Δ` good rows.
      calc δ0 ^ 2 * (δ0 - μ) * (Fintype.card G * Δ * Δ)
          = (δ0 * (Δ : ℝ)) * (δ0 * (δ0 - μ) * ((Fintype.card G : ℝ) * (Δ : ℝ))) := by ring
        _ ≤ (I.card : ℝ) * (δ0 * (δ0 - μ) * ((Fintype.card G : ℝ) * (Δ : ℝ))) :=
              mul_le_mul_of_nonneg_right hIc hc_nonneg
        _ = ∑ i ∈ I, δ0 * (δ0 - μ) * ((Fintype.card G : ℝ) * (Δ : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ i ∈ I, (hammingNorm (fun p : G × Fin Δ => f (p.1, i, p.2)) : ℝ) :=
              Finset.sum_le_sum hslice
        _ ≤ ∑ i : Fin Δ, (hammingNorm (fun p : G × Fin Δ => f (p.1, i, p.2)) : ℝ) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ I)
                (fun i _ _ => Nat.cast_nonneg _)
        _ = (hammingNorm f : ℝ) := (hammingNorm_triple f).symm
    · -- Case `δ0 < μ`: the claimed bound is `≤ 0 ≤ weight`.
      have hμδ0 : δ0 < μ := lt_of_not_ge hcase
      have h1 : δ0 ^ 2 * (δ0 - μ) ≤ 0 := by nlinarith [sq_nonneg δ0]
      have h2 : (0 : ℝ) ≤ (hammingNorm f : ℝ) := Nat.cast_nonneg _
      have h3 : (0 : ℝ) ≤ (Fintype.card G : ℝ) * (Δ : ℝ) * (Δ : ℝ) := by positivity
      nlinarith [mul_nonneg (neg_nonneg.mpr h1) h3]

end Work.LT
