import Submission.Grassmann.F1Helper

/-!
# The degree-reduction lemma (`lem:hyp inductive step` of arXiv:2209.04243, §4.3)

For a function `f` of degree at most `d` on `L(V,W)` the paper proves

  `(1/162)‖f‖₄⁴ ≤ q^{3d²}‖f‖₂⁴ + Σ_{(i,j)≠(0,0)} Σ_{V₁ ∈ 𝒱ᵢ, W₁ ∈ 𝒲ⱼ} q^{7d(i+j)}‖L_{V₁}∘L_{W₁}f‖₄⁴`.

The proof starts from the Parseval identity `‖f‖₄⁴ = Σ_X |\widehat{f²}(X)|²`, expands
`\widehat{f²}(X) = Σ_{Y+Z=X} f̂(Y)f̂(Z)`, and splits the pairs `(Y,Z)` with `Y+Z=X` into the two
classes `𝓕₁(X)` and `𝓕₂(X)` of `lem:F1` (`Submission.Grassmann.IsF1D_or_IsF2`):

* the `𝓕₁`-part is bounded by `lem:F1helper` (`Submission.Grassmann.F1Bound_of`);
* the `𝓕₂`-part is exactly `∑_X ‖F2Sum X f‖²`, bounded by `lem:F2`
  (`Submission.Grassmann.F2_sq_sum_le`).

This file contains the assembly.

## Main results

* `fcoeff_mul` — the normalised convolution formula `\widehat{fg}(X) = Σ_Y f̂(Y)ĝ(X+Y)`;
* `l4q_eq_sum_convSelf` — `‖f‖₄⁴ = Σ_X ‖Σ_Y f̂(Y)f̂(X+Y)‖²`;
* `norm_convSelf_le` — the pointwise bound
  `‖Σ_Y f̂(Y)f̂(X+Y)‖ ≤ F1Sum d X f + ‖F2Sum X f‖` for `f` of degree `≤ d`;
* `hyp_inductive_step` — the degree-reduction lemma.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-- The convolution of the normalised Fourier coefficients of `f` with itself:
`Σ_Y f̂(Y) f̂(X + Y)` — the value of `\widehat{f²}` at `X`. -/
def convSelf (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (X : Matrix (Fin n) (Fin m) 𝔽₂) : ℂ :=
  ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂, fcoeff f Y * fcoeff f (X + Y)

/-- **The normalised convolution formula**: `\widehat{fg}(X) = Σ_Y f̂(Y) ĝ(X+Y)` in the
normalisation of the paper. -/
lemma fcoeff_mul {m n : ℕ} (f g : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    fcoeff (fun A => f A * g A) X = ∑ Y, fcoeff f Y * fcoeff g (X + Y) := by
  simp only [fcoeff, fhat_mul_fun]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  ring

/-- **Parseval in the convolution form**: `‖f‖₄⁴ = Σ_X ‖Σ_Y f̂(Y) f̂(X+Y)‖²`. -/
theorem l4q_eq_sum_convSelf {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    l4q f = ∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ‖convSelf f X‖ ^ 2 := by
  rw [← l2sq_mul_self f, ← sum_normSq_fcoeff (fun A => f A * f A)]
  refine Finset.sum_congr rfl (fun X _ => ?_)
  rw [fcoeff_mul]
  rfl


/-! ## Splitting the convolution into its `𝓕₁` and `𝓕₂` parts -/

/-- `IsF2` (the paper's `𝓕₂`) and `IsF2BS` (the predicate used in `F2Sum`) agree on the pairs
occurring in the convolution: the pair `(Y, X+Y)`. -/
lemma isF2_iff_isF2BS {m n : ℕ} (X Y : Matrix (Fin n) (Fin m) 𝔽₂) :
    IsF2 X Y (X + Y) ↔ IsF2BS X Y (X + Y) := by
  have hsum : Y + (X + Y) = X := by
    calc Y + (X + Y) = X + (Y + Y) := by abel
      _ = X := by rw [mtx_add_self, add_zero]
  have hV : (LinearMap.range Y.mulVecLin ⊓ LinearMap.range (X + Y).mulVecLin ⊓
        LinearMap.range X.mulVecLin) =
      (LinearMap.range X.mulVecLin ⊓ LinearMap.range Y.mulVecLin ⊓
        LinearMap.range (X + Y).mulVecLin) := by ac_rfl
  have hW : (LinearMap.ker Y.mulVecLin ⊔ LinearMap.ker (X + Y).mulVecLin ⊔
        LinearMap.ker X.mulVecLin) =
      (LinearMap.ker X.mulVecLin ⊔ LinearMap.ker Y.mulVecLin ⊔
        LinearMap.ker (X + Y).mulVecLin) := by ac_rfl
  unfold IsF2 IsF2BS Vint Wsum
  rw [hsum, hV, hW]
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨rfl, h⟩

/-- The `𝓕₁`-part of the convolution at `X`: the sum over the pairs outside `𝓕₂(X)`. -/
def nonF2Sum {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) : ℂ :=
  ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
    if IsF2BS X Y (X + Y) then 0 else fcoeff f Y * fcoeff f (X + Y)

/-- The convolution splits into its `𝓕₁` and `𝓕₂` parts. -/
lemma convSelf_eq_add {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    convSelf f X = nonF2Sum X f + F2Sum X f := by
  unfold convSelf nonF2Sum F2Sum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun Y _ => ?_)
  by_cases h : IsF2BS X Y (X + Y) <;> simp [h]

/-- The inner sum of `F1Sum` at a fixed `Y ∈ B(d)`. -/
def innerZ {m n : ℕ} (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (Y : Bd m n d) : ℝ :=
  ∑ Z : Bd m n d, if IsF1D X Y.1 Z.1 then ‖fcoeff f Y.1‖ * ‖fcoeff f Z.1‖ else 0

lemma F1Sum_eq_sum_innerZ {m n : ℕ} (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    F1Sum d X f = ∑ Y : Bd m n d, innerZ d X f Y := rfl

lemma innerZ_term_nonneg {m n : ℕ} (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (Y Z : Bd m n d) :
    0 ≤ (if IsF1D X Y.1 Z.1 then ‖fcoeff f Y.1‖ * ‖fcoeff f Z.1‖ else 0) := by
  by_cases h : IsF1D X Y.1 Z.1
  · rw [if_pos h]; positivity
  · rw [if_neg h]

lemma innerZ_nonneg {m n : ℕ} (d : ℕ) (X : Matrix (Fin n) (Fin m) 𝔽₂)
    (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) (Y : Bd m n d) : 0 ≤ innerZ d X f Y :=
  Finset.sum_nonneg (fun Z _ => innerZ_term_nonneg d X f Y Z)

/-- For `f` of degree `≤ d`, the term of the `𝓕₁`-part of the convolution at `Y ∈ B(d)` is
bounded by the inner sum of `F1Sum`. -/
lemma le_innerZ {m n : ℕ} {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f)
    (X : Matrix (Fin n) (Fin m) 𝔽₂) (Y : Bd m n d) :
    (if IsF2BS X Y.1 (X + Y.1) then 0 else
        ‖fcoeff f Y.1‖ * ‖fcoeff f (X + Y.1)‖) ≤ innerZ d X f Y := by
  classical
  by_cases hF2 : IsF2BS X Y.1 (X + Y.1)
  · rw [if_pos hF2]
    exact innerZ_nonneg d X f Y
  rw [if_neg hF2]
  by_cases hrank : (X + Y.1).rank ≤ d
  · set Z₀ : Bd m n d := ⟨X + Y.1, hrank⟩ with hZ₀
    have h1 : IsF1D X Y.1 Z₀.1 := by
      rcases IsF1D_or_IsF2 X Y.1 (X + Y.1) (by
        calc Y.1 + (X + Y.1) = X + (Y.1 + Y.1) := by abel
          _ = X := by rw [mtx_add_self, add_zero]) with h | h
      · exact h
      · exact absurd ((isF2_iff_isF2BS X Y.1).mp h) hF2
    calc ‖fcoeff f Y.1‖ * ‖fcoeff f (X + Y.1)‖
        = (if IsF1D X Y.1 Z₀.1 then ‖fcoeff f Y.1‖ * ‖fcoeff f Z₀.1‖ else 0) := by
          rw [if_pos h1]
      _ ≤ innerZ d X f Y :=
          Finset.single_le_sum (fun Z _ => innerZ_term_nonneg d X f Y Z) (Finset.mem_univ Z₀)
  · have hz : fcoeff f (X + Y.1) = 0 := by
      rw [fcoeff_eq, hf (X + Y.1) (by omega), mul_zero]
    rw [hz, norm_zero, mul_zero]
    exact innerZ_nonneg d X f Y

/-! ## The pointwise bound -/

/-- `∑_{a : α} f a = ∑_{a : {a // p a}} f a` when `f` vanishes off `p`. -/
lemma sum_eq_sum_subtype {α : Type*} [Fintype α] {p : α → Prop} [DecidablePred p]
    (f : α → ℝ) (h : ∀ a, ¬ p a → f a = 0) :
    (∑ a, f a) = ∑ a : {a // p a}, f a.1 := by
  have h0 : (∑ i : {i // ¬ p i}, f ↑i) = 0 :=
    Finset.sum_eq_zero (fun i _ => h i.1 i.2)
  have key := Fintype.sum_subtype_add_sum_subtype (M := ℝ) (ι := α) p f
  rw [h0, add_zero] at key
  exact key.symm

/-- **The `𝓕₁`-part of the convolution is bounded by `F1Sum`**: for `f` of degree `≤ d`,
`‖Σ_{Y ∉ 𝓕₂(X)} f̂(Y)f̂(X+Y)‖ ≤ F1Sum d X f`. -/
lemma norm_nonF2Sum_le_F1Sum {m n : ℕ} {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    ‖nonF2Sum X f‖ ≤ F1Sum d X f := by
  classical
  have h1 : ‖nonF2Sum X f‖ ≤ ∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
      (if IsF2BS X Y (X + Y) then 0 else ‖fcoeff f Y‖ * ‖fcoeff f (X + Y)‖) := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun Y _ => ?_))
    by_cases h : IsF2BS X Y (X + Y)
    · rw [if_pos h, norm_zero, if_pos h]
    · rw [if_neg h, if_neg h, norm_mul]
  refine le_trans h1 ?_
  have h2 : (∑ Y : Matrix (Fin n) (Fin m) 𝔽₂,
        (if IsF2BS X Y (X + Y) then 0 else ‖fcoeff f Y‖ * ‖fcoeff f (X + Y)‖))
      = ∑ Y : Bd m n d,
        (if IsF2BS X Y.1 (X + Y.1) then 0 else ‖fcoeff f Y.1‖ * ‖fcoeff f (X + Y.1)‖) := by
    refine sum_eq_sum_subtype (p := fun Y : Matrix (Fin n) (Fin m) 𝔽₂ => Y.rank ≤ d)
      (fun Y => if IsF2BS X Y (X + Y) then 0 else ‖fcoeff f Y‖ * ‖fcoeff f (X + Y)‖)
      (fun Y hY => ?_)
    by_cases h : IsF2BS X Y (X + Y)
    · rw [if_pos h]
    · rw [if_neg h, fcoeff_eq, hf Y (by omega), mul_zero, norm_zero, zero_mul]
  rw [h2]
  refine le_trans (Finset.sum_le_sum (fun Y _ => le_innerZ hf X Y)) ?_
  rw [F1Sum_eq_sum_innerZ]

/-- **The pointwise decomposition bound**: `‖\widehat{f²}(X)‖ ≤ F1Sum d X f + ‖F2Sum X f‖`. -/
lemma norm_convSelf_le {m n : ℕ} {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe d f) (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    ‖convSelf f X‖ ≤ F1Sum d X f + ‖F2Sum X f‖ := by
  rw [convSelf_eq_add]
  exact le_trans (norm_add_le _ _) (add_le_add_left (norm_nonF2Sum_le_F1Sum hf X) _)

/-! ## The degree-reduction lemma -/

/-- **The degree-reduction lemma of arXiv:2209.04243 (`lem:hyp inductive step`)**: for a function
`f` on `L(V,W)` of degree at most `d`,

`‖f‖₄⁴ ≤ 162 q^{6d²}‖f‖₂⁴ + 2 Σ_{(i,j)≠(0,0)} Σ_{V₁ ∈ 𝒱ᵢ, W₁ ∈ 𝒲ⱼ} q^{7d(i+j)}‖L_{V₁}∘L_{W₁}f‖₄⁴`.

(The paper's constants are `1/162` and `q^{3d²}`; our `𝓕₁`-bound `lem:F1helper` is stated with
the harmless loss `81 q^{6d²}`, which only affects the constant `C` in `HypHyper`.)

The proof: `‖f‖₄⁴ = Σ_X ‖Σ_{Y+Z=X} f̂(Y)f̂(Z)‖²` (`l4q_eq_sum_convSelf`), each pair `Y+Z=X`
lies in `𝓕₁(X) ∪ 𝓕₂(X)` (`IsF1D_or_IsF2`), and the two parts are bounded by `lem:F1helper`
(`F1Bound_of`) and `lem:F2` (`F2_sq_sum_le`) respectively, assembled with `‖a+b‖² ≤ 2a²+2b²`. -/
theorem hyp_inductive_step {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ)
    (hf : DegLe d f) :
    l4q f ≤ 162 * (2 : ℝ) ^ (6 * d ^ 2) * (l2sq f) ^ 2 +
      2 * ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (m + 1),
        (if i = 0 ∧ j = 0 then 0 else (2 : ℝ) ^ (7 * d * (i + j))) *
          (∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            (if Module.finrank 𝔽₂ V₁ = i ∧ Module.finrank 𝔽₂ W₁ = m - j
              then l4q (Lup V₁ (Ldown W₁ f)) else 0)) := by
  rw [l4q_eq_sum_convSelf f]
  have hmain : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ‖convSelf f X‖ ^ 2)
      ≤ 2 * (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, (F1Sum d X f) ^ 2) +
        2 * (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ‖F2Sum X f‖ ^ 2) := by
    have hp : ∀ X : Matrix (Fin n) (Fin m) 𝔽₂,
        ‖convSelf f X‖ ^ 2 ≤ 2 * (F1Sum d X f) ^ 2 + 2 * ‖F2Sum X f‖ ^ 2 := by
      intro X
      have h := norm_convSelf_le hf X
      have h1 : ‖convSelf f X‖ ^ 2 ≤ (F1Sum d X f + ‖F2Sum X f‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h 2
      nlinarith [h1, sq_nonneg (F1Sum d X f - ‖F2Sum X f‖)]
    calc (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ‖convSelf f X‖ ^ 2)
        ≤ ∑ X : Matrix (Fin n) (Fin m) 𝔽₂,
            (2 * (F1Sum d X f) ^ 2 + 2 * ‖F2Sum X f‖ ^ 2) :=
          Finset.sum_le_sum (fun X _ => hp X)
      _ = 2 * (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, (F1Sum d X f) ^ 2) +
            2 * (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, ‖F2Sum X f‖ ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  refine hmain.trans (le_trans (add_le_add
    (mul_le_mul_of_nonneg_left (F1Bound_of d f hf) (by norm_num))
    (mul_le_mul_of_nonneg_left (F2_sq_sum_le d f hf) (by norm_num))) ?_)
  rw [show (2 : ℝ) * (81 * (2 : ℝ) ^ (6 * d ^ 2) * (l2sq f) ^ 2) =
      162 * (2 : ℝ) ^ (6 * d ^ 2) * (l2sq f) ^ 2 from by ring]

/-! ## Lemma 5.9 of arXiv:2209.04243 ("linear-algebraic-2") -/

/-- **Lemma "linear-algebraic-2"** (arXiv:2209.04243): if `X ≤ Y` in the rank poset of
`L(W,V)` then the induced map `Y|_{\\ker X} : \\ker X → V/\\operatorname{Im} X` has rank
`rank Y - rank X`.

Here the quotient `V/\\operatorname{Im} X` is encoded by `Q` (with `ker Q = Im X`) and the
inclusion `\\ker X ↪ W` by `ι` (with `range ι = ker X`, `ker ι = 0`). -/
lemma rank_mul_mul_eq_of_rank_le {m n m' n' : ℕ} (Q : Matrix (Fin n') (Fin n) 𝔽₂)
    (ι : Matrix (Fin m) (Fin m') 𝔽₂) (X Y : Matrix (Fin n) (Fin m) 𝔽₂)
    (hQ : LinearMap.ker Q.mulVecLin = LinearMap.range X.mulVecLin)
    (hιker : LinearMap.ker ι.mulVecLin = ⊥)
    (hι : LinearMap.range ι.mulVecLin = LinearMap.ker X.mulVecLin)
    (h1 : LinearMap.range X.mulVecLin ≤ LinearMap.range Y.mulVecLin)
    (h2 : ∀ w, Y.mulVec w ∈ LinearMap.range X.mulVecLin → Y.mulVec w = X.mulVec w) :
    (Q * Y * ι).rank = Y.rank - X.rank := by
  have hXY : X.rank ≤ Y.rank := Submodule.finrank_mono h1
  have hYle : Y.rank ≤ m := by
    have hrn := LinearMap.finrank_range_add_finrank_ker Y.mulVecLin
    rw [Module.finrank_fin_fun (R := 𝔽₂)] at hrn
    have : Y.rank = Module.finrank 𝔽₂ (LinearMap.range Y.mulVecLin) := rfl
    omega
  have hXYle : X.rank ≤ m := le_trans hXY hYle
  have hkerY : LinearMap.ker Y.mulVecLin ≤ LinearMap.ker X.mulVecLin := by
    intro w hw
    have hw' : Y.mulVec w = 0 := by simpa using hw
    have hmem : Y.mulVec w ∈ LinearMap.range X.mulVecLin := by
      rw [hw']; exact Submodule.zero_mem _
    have h := h2 w hmem
    have : X.mulVec w = 0 := by rw [← h, hw']
    simpa using this
  have hmemQ : ∀ w, (Q.mulVecLin.comp Y.mulVecLin) w = 0 ↔
      Y.mulVec w ∈ LinearMap.range X.mulVecLin := by
    intro w
    constructor
    · intro h
      rw [← hQ]
      simpa [LinearMap.mem_ker, LinearMap.comp_apply, Matrix.mulVecLin_apply] using h
    · intro h
      have hQw : Y.mulVec w ∈ LinearMap.ker Q.mulVecLin := by rw [hQ]; exact h
      simpa [LinearMap.comp_apply, Matrix.mulVecLin_apply] using (LinearMap.mem_ker.mp hQw)
  have hker : LinearMap.ker (Q.mulVecLin.comp Y.mulVecLin) ⊓ LinearMap.range ι.mulVecLin =
      LinearMap.ker Y.mulVecLin := by
    refine le_antisymm ?_ ?_
    · intro w hw
      obtain ⟨hw1, hw2⟩ := hw
      have hYW : Y.mulVec w ∈ LinearMap.range X.mulVecLin := (hmemQ w).mp hw1
      have h2w := h2 w hYW
      have hXw : X.mulVec w = 0 := by
        rw [hι] at hw2
        simpa using hw2
      have : Y.mulVec w = 0 := by rw [h2w, hXw]
      simpa using this
    · intro w hw
      refine ⟨(hmemQ w).mpr ?_, by show w ∈ LinearMap.range ι.mulVecLin; rw [hι]; exact hkerY hw⟩
      have hY0 : Y.mulVec w = 0 := by simpa using hw
      rw [hY0]; exact Submodule.zero_mem _
  have hfin : Module.finrank 𝔽₂ ↥(LinearMap.ker (Q.mulVecLin.comp Y.mulVecLin) ⊓
      LinearMap.range ι.mulVecLin) = m - Y.rank := by
    rw [hker]
    have hrn := LinearMap.finrank_range_add_finrank_ker Y.mulVecLin
    rw [Module.finrank_fin_fun (R := 𝔽₂)] at hrn
    have : Y.rank = Module.finrank 𝔽₂ (LinearMap.range Y.mulVecLin) := rfl
    omega
  have hm' : m' = m - X.rank := by
    have hrn := LinearMap.finrank_range_add_finrank_ker ι.mulVecLin
    rw [Module.finrank_fin_fun (R := 𝔽₂)] at hrn
    have hk : Module.finrank 𝔽₂ ↥(LinearMap.ker ι.mulVecLin) = 0 := by
      rw [hιker]; exact finrank_bot 𝔽₂ (Fin m' → 𝔽₂)
    have hr : Module.finrank 𝔽₂ (LinearMap.range ι.mulVecLin) = m' := by omega
    have hrk : Module.finrank 𝔽₂ ↥(LinearMap.ker X.mulVecLin) = m' := by rw [← hι]; exact hr
    have hrn2 := LinearMap.finrank_range_add_finrank_ker X.mulVecLin
    rw [Module.finrank_fin_fun (R := 𝔽₂)] at hrn2
    have hXr : X.rank = Module.finrank 𝔽₂ (LinearMap.range X.mulVecLin) := rfl
    omega
  have hT : (Q * Y * ι).mulVecLin = (Q.mulVecLin.comp Y.mulVecLin).comp ι.mulVecLin := by
    rw [Matrix.mulVecLin_mul, Matrix.mulVecLin_mul, LinearMap.comp_assoc]
  have hkerT : Module.finrank 𝔽₂ ↥(LinearMap.ker (Q * Y * ι).mulVecLin) = m - Y.rank := by
    rw [hT, Commons.LinearAlgebra.finrank_ker_comp ι.mulVecLin (Q.mulVecLin.comp Y.mulVecLin)]
    have hzero : Module.finrank 𝔽₂ ↥(LinearMap.ker ι.mulVecLin) = 0 := by
      rw [hιker]; exact finrank_bot 𝔽₂ (Fin m' → 𝔽₂)
    rw [hzero, zero_add, hfin]
  have hrank : (Q * Y * ι).rank = Module.finrank 𝔽₂ (LinearMap.range (Q * Y * ι).mulVecLin) := rfl
  rw [hrank]
  have hrn := LinearMap.finrank_range_add_finrank_ker (Q * Y * ι).mulVecLin
  rw [Module.finrank_fin_fun (R := 𝔽₂), hkerT] at hrn
  omega


end

end Submission.Grassmann
