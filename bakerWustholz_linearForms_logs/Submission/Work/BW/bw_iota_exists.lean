import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.derVec_span_finrank_ge
import Submission.Work.BW.derVec_span_finrank_le
import Submission.Work.BW.exists_iota_of_finrank

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

/-- **BW §10: existence of the `r - 1` independent operators `∂*_j`.**
Under the standing hypotheses of BW §11 and the basic hypothesis `BH` at rank `r ≥ 2`, there are
`r - 1` indices `ι m ≠ k` whose coefficient vectors `derVec b k L (ι m)` (i.e. the operators
`∂*_j = b k ∂/∂z_j - b j ∂/∂z_k` of BW §10, evaluated on the `L i`) are `ℚ`-linearly independent.

The linear algebra: the `ℚ`-vectors `w j i = (b k · L i j - b j · L i k)` (`j : Fin n`, `i : Fin r`)
are the columns of `N = (b k) • M - m_k ⊗ b`, where `M = (L i j)`. Since `b` lies in the row space
of `M` and `b k ≠ 0`, the span of the `w j` is exactly the hyperplane `∑ i, t i · x i = 0` picked
out by a coefficient vector `t` with `Mᵀ t = b`; hence it has dimension `r - 1`. Faithfulness of the
two bounds, and the extraction of an independent subfamily of size `r - 1` out of a spanning set of
dimension `r - 1`, are the lemmas `derVec_span_finrank_ge`, `derVec_span_finrank_le` and
`exists_iota_of_finrank`. -/
theorem bw_iota_exists {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (c : ℝ) (hst : Standing φ α b k c)
    (hr : 2 ≤ r) (v : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K) (σ : Fin r → ℝ)
    (hBH : BH φ α b v c r L α' σ) :
    ∃ ι : Fin (r - 1) → Fin n, IotaOK b k L ι := by
  classical
  -- The two linear-algebra inputs carried by the hypotheses.
  obtain ⟨hL, hspan, -⟩ := hBH
  obtain ⟨-, -, -, -, hbk, -⟩ := hst
  -- The `∂*`-vectors `w j i = b k · L i j - b j · L i k`.
  let w : Fin n → (Fin r → ℚ) := fun j => fun i => (derVec b k L j i : ℚ)
  have hge : r - 1 ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range w)) :=
    derVec_span_finrank_ge L b k hL hbk
  have hle : Module.finrank ℚ (Submodule.span ℚ (Set.range w)) ≤ r - 1 :=
    derVec_span_finrank_le L b k hspan hbk
  have hdim : Module.finrank ℚ (Submodule.span ℚ (Set.range w)) = r - 1 :=
    le_antisymm hle hge
  -- The same family, indexed by the `j ≠ k` (the `j = k` vector is `0`).
  let w' : {j : Fin n // j ≠ k} → (Fin r → ℚ) := fun j => w j.val
  have hwk : w k = 0 := by
    funext i
    simp [w, derVec]
  have hspan_eq : Submodule.span ℚ (Set.range w') = Submodule.span ℚ (Set.range w) := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro x ⟨j, rfl⟩
      exact Submodule.subset_span ⟨j.val, rfl⟩
    · rw [Submodule.span_le]
      rintro x ⟨j, rfl⟩
      by_cases hj : j = k
      · rw [hj, hwk]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
  have hdim' : Module.finrank ℚ (Submodule.span ℚ (Set.range w')) = r - 1 := by
    rw [hspan_eq, hdim]
  -- Extract `r - 1` independent members and reindex them by `Fin (r - 1)`.
  obtain ⟨ι, -, hιLI⟩ := exists_iota_of_finrank (k := k) w' hdim'
  refine ⟨fun m => (ι m).val, ?_, ?_⟩
  · intro m
    exact (ι m).2
  · simpa only [Function.comp_def, w', w] using hιLI

end Work.BW
