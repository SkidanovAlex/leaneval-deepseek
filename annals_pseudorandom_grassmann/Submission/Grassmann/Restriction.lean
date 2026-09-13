import Submission.Grassmann.BilinearDegree

/-!
# Restrictions and shifts on `L(V,W)`

The paper arXiv:2209.04243 (Section 3.4-3.5) restricts a function `f` on `L(V,W)` to the
affine subspace of maps agreeing with a fixed `T` on a subspace `V₁ ≤ V` and whose dual
agrees with `T*` on `W₁°` (for `W₁ ≤ W`).  Concretely, choosing a quotient map
`Q : V ↠ V/V₁` and an inclusion `ι : W₁ ↪ W`, such a restricted map is the composite
`ι ∘ A ∘ Q` for `A ∈ L(V/V₁, W₁)`.

Here we formalize this **without** any submodule hypothesis, at the level of matrices:

* `restr Q ι f` is the function `A ↦ f (ι * A * Q)` on `L(𝔽₂^{n'}, 𝔽₂^{m'})`;
* `restr_mchar`: `restr Q ι (mchar X) = mchar (Q * X * ι)` -- restriction maps the character
  indexed by `X` to the character indexed by the "restricted dual" `Q * X * ι`;
* since `rank (Q * X * ι) ≤ rank X`, restrictions **do not increase degree**:
  `degLe_restr`;
* the shift operator `shift T f = fun A => f (A + T)` multiplies each character by a scalar
  (`shift_mchar`) and hence also does not increase degree (`degLe_shift`).
-/

open Matrix Finset BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission.Grassmann

noncomputable section

/-! ## The character sum formula and the trace form -/

/-- `ZMod.stdAddChar` turns sums into products. -/
lemma stdAddChar_sum {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    ZMod.stdAddChar (∑ i ∈ s, f i) = ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/-- The matrix character is the additive character of the trace: `mchar X A = ω^{Tr (X A)}`. -/
lemma mchar_eq_trace {m n : ℕ} (X : Matrix (Fin n) (Fin m) (ZMod 2))
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) :
    mchar X A = ZMod.stdAddChar (Matrix.trace (X * A)) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [mchar, Finset.prod_comm, stdAddChar_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← stdAddChar_sum]

/-! ## Restrictions -/

/-- The **restriction operator**: given a "quotient" matrix `Q : Matrix (Fin n') (Fin n)`
and an "inclusion" matrix `ι : Matrix (Fin m) (Fin m')`, the restriction of `f` is the
function `A ↦ f (ι * A * Q)` on `L(𝔽₂^{n'}, 𝔽₂^{m'})`. -/
def restr {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (ι : Matrix (Fin m) (Fin m') (ZMod 2))
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) : Matrix (Fin m') (Fin n') (ZMod 2) → ℂ :=
  fun A => f (ι * A * Q)

lemma restr_add {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (ι : Matrix (Fin m) (Fin m') (ZMod 2)) (f g : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    restr Q ι (f + g) = restr Q ι f + restr Q ι g := by
  funext A; rfl

lemma restr_zero {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (ι : Matrix (Fin m) (Fin m') (ZMod 2)) :
    restr Q ι (0 : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) =
      (0 : Matrix (Fin m') (Fin n') (ZMod 2) → ℂ) := by
  funext A; rfl

lemma restr_smul {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (ι : Matrix (Fin m) (Fin m') (ZMod 2)) (c : ℂ)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    restr Q ι (c • f) = c • restr Q ι f := by
  funext A; rfl

/-- **Restriction of a character**: `restr Q ι (mchar X) = mchar (Q * X * ι)`. -/
lemma restr_mchar {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (ι : Matrix (Fin m) (Fin m') (ZMod 2)) (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    restr Q ι (mchar X) = (mchar (Q * X * ι) : Matrix (Fin m') (Fin n') (ZMod 2) → ℂ) := by
  funext A
  rw [restr, mchar_eq_trace, mchar_eq_trace]
  congr 1
  rw [show X * (ι * A * Q) = X * ι * (A * Q) from by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_cycle X ι (A * Q),
    show (A * Q) * X * ι = A * (Q * X * ι) from by simp only [Matrix.mul_assoc],
    Matrix.trace_mul_comm A (Q * X * ι)]

/-- Restricting does not increase the rank of the dual matrix. -/
lemma restr_rank_le {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (ι : Matrix (Fin m) (Fin m') (ZMod 2)) (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    (Q * X * ι).rank ≤ X.rank := by
  rw [Matrix.mul_assoc]
  exact le_trans (Matrix.rank_mul_le_right Q (X * ι)) (Matrix.rank_mul_le_left X ι)

/-- **Restrictions do not increase degree.** -/
lemma degLe_restr {m n m' n' d : ℕ} (Q : Matrix (Fin n') (Fin n) (ZMod 2))
    (ι : Matrix (Fin m) (Fin m') (ZMod 2)) {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ}
    (hf : DegLe d f) : DegLe d (restr Q ι f) := by
  rw [degLe_iff_mem_charLe] at hf ⊢
  have hchar : ∀ (X : Matrix (Fin n) (Fin m) (ZMod 2)), X.rank ≤ d →
      (mchar (Q * X * ι) : Matrix (Fin m') (Fin n') (ZMod 2) → ℂ) ∈
        charLe (m := m') (n := n') d :=
    fun X hX => mchar_mem_charLe (le_trans (restr_rank_le Q ι X) hX)
  refine Submodule.span_induction (p := fun f _ => restr Q ι f ∈ charLe (m := m') (n := n') d)
    ?_ ?_ ?_ ?_ hf
  · rintro f ⟨X, hX, rfl⟩
    rw [restr_mchar]; exact hchar X hX
  · rw [restr_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [restr_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [restr_smul]; exact Submodule.smul_mem _ c ha

/-! ## Shifts -/

/-- The **shift operator** `Δ_T f = fun A => f (A + T)`. -/
def shift {m n : ℕ} (T : Matrix (Fin m) (Fin n) (ZMod 2))
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ :=
  fun A => f (A + T)

lemma shift_add {m n : ℕ} (T : Matrix (Fin m) (Fin n) (ZMod 2))
    (f g : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) :
    shift T (f + g) = shift T f + shift T g := by
  funext A; rfl

lemma shift_zero {m n : ℕ} (T : Matrix (Fin m) (Fin n) (ZMod 2)) :
    shift T (0 : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) =
      (0 : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) := by
  funext A; rfl

lemma shift_smul {m n : ℕ} (T : Matrix (Fin m) (Fin n) (ZMod 2)) (c : ℂ)
    (f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) : shift T (c • f) = c • shift T f := by
  funext A; rfl

/-- A shift multiplies each character by the scalar `mchar X T`. -/
lemma shift_mchar {m n : ℕ} (T : Matrix (Fin m) (Fin n) (ZMod 2))
    (X : Matrix (Fin n) (Fin m) (ZMod 2)) :
    shift T (mchar X) = mchar X T • (mchar X : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ) := by
  funext A
  rw [shift, Pi.smul_apply, smul_eq_mul, mchar_add_right X A T, mul_comm]

/-- **Shifts do not increase degree.** -/
lemma degLe_shift {m n d : ℕ} (T : Matrix (Fin m) (Fin n) (ZMod 2))
    {f : Matrix (Fin m) (Fin n) (ZMod 2) → ℂ} (hf : DegLe d f) : DegLe d (shift T f) := by
  rw [degLe_iff_mem_charLe] at hf ⊢
  refine Submodule.span_induction (p := fun f _ => shift T f ∈ charLe (m := m) (n := n) d)
    ?_ ?_ ?_ ?_ hf
  · rintro f ⟨X, hX, rfl⟩
    rw [shift_mchar]
    exact Submodule.smul_mem _ _ (mchar_mem_charLe hX)
  · rw [shift_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    rw [shift_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    rw [shift_smul]; exact Submodule.smul_mem _ c ha

end

end Submission.Grassmann
