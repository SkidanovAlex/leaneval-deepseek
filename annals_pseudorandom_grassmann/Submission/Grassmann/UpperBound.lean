import Submission.Grassmann.AfterRestricting
import Submission.Grassmann.DopXReform
import Submission.Grassmann.SwitchingRoles
import Submission.Grassmann.D4Rewrite
import Submission.Grassmann.Prop56Main
import Submission.Grassmann.HypHyperUC
import Submission.Commons.LinearAlgebra.Matrix.rank_eq_zero_iff

/-!
# The strong induction hypothesis of §8 (arXiv:2209.04243) and the base case

`HypHyperUC` (Theorem 1.5) is proved by strong induction on the degree `d`.  The induction
hypothesis at level `D` is the *same* inequality restricted to functions of degree `≤ D`:

```
IHyp C D := ∀ m n d f, d ≤ D → DegLe d f →
  l4q f ≤ 2^{C d²} Σ_{V₁,W₁ : |(V₁,W₁)| ≤ d} D4 V₁ W₁ (Lsub V₁ W₁ f).
```

This file sets `IHyp` up, shows that `HypHyperUC` is equivalent to `∃ C > 0, ∀ D, IHyp C D`,
reduces the latter to the base case plus the inductive step `IHyp C (d-1) → IHyp C d`, and
proves the base case `IHyp C 0` together with the two auxiliary facts used to absorb the
"constant" term of `lem:after restricting` into the main sum:

* `D4_bot_top` : `D4 ⊥ ⊤ (Lsub ⊥ ⊤ f) = (l2sq f)²`;
* `l2sq_sq_le_sum_D4` : `(l2sq f)² ≤ Σ_{V,W} [|(V,W)| ≤ d] D4 V W (Lsub V W f)`.
-/

open Finset BigOperators Matrix
open Classical

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-- A nonnegative function is dominated by its sum (over a finite type). -/
private lemma le_sum_of_nonneg {ι : Type*} [Fintype ι] (g : ι → ℝ) (a : ι)
    (hg : ∀ i, 0 ≤ g i) : g a ≤ ∑ i, g i :=
  Finset.single_le_sum (fun i _ => hg i) (Finset.mem_univ a)

/-! ## The hybrid predicate at `(⊥, ⊤)` -/

lemma hybridPredSub_bot_top {m n : ℕ} (X : Matrix (Fin n) (Fin m) 𝔽₂) :
    hybridPredSub (⊥ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (⊤ : Submodule 𝔽₂ (Fin m → 𝔽₂)) X :=
  ⟨bot_le, fun _ _ => Submodule.mem_top⟩

/-- `L_{⊥,⊤}` is the identity. -/
lemma Lsub_bot_top {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    Lsub (⊥ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (⊤ : Submodule 𝔽₂ (Fin m → 𝔽₂)) f = f := by
  refine eq_of_fcoeff_eq fun X => ?_
  rw [Lsub, fcoeff_lapMulN, if_pos (hybridPredSub_bot_top X), one_mul]

/-! ## `D4` is nonnegative and at `(⊥,⊤)` it is `(l2sq f)²` -/

lemma D4_nonneg {m n : ℕ} (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂))
    (W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂)) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    0 ≤ D4 V₁ W₁ f := by
  unfold D4
  refine mul_nonneg (by positivity) (Finset.sum_nonneg fun T _ => ?_)
  exact sq_nonneg _

/-- **`D4 ⊥ ⊤ (Lsub ⊥ ⊤ f) = (l2sq f)²`**: the pair `(⊥,⊤)` of order `0` contributes exactly
the squared `L²`-norm. -/
theorem D4_bot_top {m n : ℕ} (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    D4 (⊥ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (⊤ : Submodule 𝔽₂ (Fin m → 𝔽₂))
      (Lsub (⊥ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (⊤ : Submodule 𝔽₂ (Fin m → 𝔽₂)) f) =
      (l2sq f) ^ 2 := by
  rw [D4_Lsub_eq_sum_l2sq]
  have hpt : ∀ T : Matrix (Fin m) (Fin n) 𝔽₂,
      l2sq (Dop0S (⊥ : Submodule 𝔽₂ (Fin n → 𝔽₂)) (⊤ : Submodule 𝔽₂ (Fin m → 𝔽₂)) T f)
        = l2sq f := by
    intro T
    rw [Dop0S, Lsub_bot_top]
    exact l2sq_restr_shift_eq_of_order_zero (Qp ⊥) (Ip ⊤) (ker_Qp ⊥) (range_Ip ⊤) T f
  rw [Finset.sum_congr rfl (fun T _ => by rw [hpt T])]
  rw [Finset.sum_const, Finset.card_univ, fintype_card_matrix_zmod_two, nsmul_eq_mul]
  have h : (((2 ^ (m * n) : ℕ) : ℝ)) = (2 : ℝ) ^ (m * n) := by push_cast; ring
  rw [h, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), one_mul]

/-- **The constant term of `lem:after restricting` is dominated by the main sum**: the pair
`(⊥,⊤)` already contributes `(l2sq f)²`. -/
theorem l2sq_sq_le_sum_D4 {m n : ℕ} (d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ) :
    (l2sq f) ^ 2 ≤
      ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
          then D4 V₁ W₁ (Lsub V₁ W₁ f) else 0 := by
  have hWnn : ∀ (V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂)),
      0 ≤ ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
          then D4 V₁ W₁ (Lsub V₁ W₁ f) else 0 := fun V₁ =>
    Finset.sum_nonneg fun W₁ _ => by
      split
      · exact D4_nonneg _ _ _
      · exact le_refl 0
  have hinner : ∀ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂),
      (if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ (⊤ : Submodule 𝔽₂ (Fin m → 𝔽₂))) ≤ d
        then D4 V₁ ⊤ (Lsub V₁ ⊤ f) else 0) ≤
      ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
          then D4 V₁ W₁ (Lsub V₁ W₁ f) else 0 := by
    intro V₁
    by_cases h : Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ (⊤ : Submodule 𝔽₂ (Fin m → 𝔽₂))) ≤ d
    · rw [if_pos h]
      have hle := le_sum_of_nonneg
        (fun W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂) =>
          if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
            then D4 V₁ W₁ (Lsub V₁ W₁ f) else 0)
        ⊤ (fun W₁ => by
          split
          · exact D4_nonneg _ _ _
          · exact le_refl 0)
      rw [if_pos h] at hle
      exact hle
    · rw [if_neg h]
      exact hWnn V₁
  have hbot : Module.finrank 𝔽₂ (⊥ : Submodule 𝔽₂ (Fin n → 𝔽₂)) +
      (m - Module.finrank 𝔽₂ (⊤ : Submodule 𝔽₂ (Fin m → 𝔽₂))) = 0 := by
    have h1 : Module.finrank 𝔽₂ (⊥ : Submodule 𝔽₂ (Fin n → 𝔽₂)) = 0 := finrank_bot 𝔽₂ _
    have h2 : Module.finrank 𝔽₂ (⊤ : Submodule 𝔽₂ (Fin m → 𝔽₂)) = m := by
      rw [finrank_top, Module.finrank_fin_fun]
    rw [h1, h2, Nat.sub_self, add_zero]
  have hmain : (if Module.finrank 𝔽₂ (⊥ : Submodule 𝔽₂ (Fin n → 𝔽₂)) +
        (m - Module.finrank 𝔽₂ (⊤ : Submodule 𝔽₂ (Fin m → 𝔽₂))) ≤ d
        then D4 ⊥ ⊤ (Lsub ⊥ ⊤ f) else 0) = D4 ⊥ ⊤ (Lsub ⊥ ⊤ f) := by
    rw [if_pos (by rw [hbot]; exact Nat.zero_le d)]
  calc (l2sq f) ^ 2 = D4 ⊥ ⊤ (Lsub ⊥ ⊤ f) := (D4_bot_top f).symm
    _ = (if Module.finrank 𝔽₂ (⊥ : Submodule 𝔽₂ (Fin n → 𝔽₂)) +
          (m - Module.finrank 𝔽₂ (⊤ : Submodule 𝔽₂ (Fin m → 𝔽₂))) ≤ d
          then D4 ⊥ ⊤ (Lsub ⊥ ⊤ f) else 0) := hmain.symm
    _ ≤ (∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            if Module.finrank 𝔽₂ (⊥ : Submodule 𝔽₂ (Fin n → 𝔽₂)) +
              (m - Module.finrank 𝔽₂ W₁) ≤ d
              then D4 ⊥ W₁ (Lsub ⊥ W₁ f) else 0) := hinner ⊥
    _ ≤ ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂),
          ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
            if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
              then D4 V₁ W₁ (Lsub V₁ W₁ f) else 0 :=
        le_sum_of_nonneg _ ⊥ hWnn

/-! ## Functions of degree `0` are constant -/

/-- `mchar 0 A = 1`. -/
lemma mchar_zero_left {m n : ℕ} (A : Matrix (Fin m) (Fin n) 𝔽₂) :
    mchar (0 : Matrix (Fin n) (Fin m) 𝔽₂) A = 1 := by
  simp [mchar]

/-- A function of degree `0` is constant. -/
lemma exists_const_of_degLe_zero {m n : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe 0 f) : ∃ c : ℂ, f = fun _ => c := by
  classical
  refine ⟨((2 : ℂ) ^ (m * n))⁻¹ * fhat f 0, funext fun A => ?_⟩
  have hsum : (∑ X : Matrix (Fin n) (Fin m) 𝔽₂, fhat f X * mchar X A) = fhat f 0 := by
    rw [Finset.sum_eq_single (0 : Matrix (Fin n) (Fin m) 𝔽₂)]
    · rw [mchar_zero_left, mul_one]
    · intro X _ hX
      have hpos : 0 < X.rank := by
        by_contra hcon
        exact hX ((Commons.LinearAlgebra.Matrix.rank_eq_zero_iff X).mp (by omega))
      rw [hf X hpos, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ (0 : Matrix (Fin n) (Fin m) 𝔽₂)) h
  have hinv := fhat_inversion f A
  rw [hsum] at hinv
  rw [hinv]
  field_simp

/-- The squared `L²`-norm of a constant function. -/
lemma l2sq_const {m n : ℕ} (c : ℂ) :
    l2sq (fun _ : Matrix (Fin m) (Fin n) 𝔽₂ => c) = ‖c‖ ^ 2 := by
  rw [l2sq, Finset.sum_const, Finset.card_univ, fintype_card_matrix_zmod_two, nsmul_eq_mul]
  have h : (((2 ^ (m * n) : ℕ) : ℝ)) = (2 : ℝ) ^ (m * n) := by push_cast; ring
  rw [h, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), one_mul]

/-- The fourth moment of a constant function. -/
lemma l4q_const {m n : ℕ} (c : ℂ) :
    l4q (fun _ : Matrix (Fin m) (Fin n) 𝔽₂ => c) = ‖c‖ ^ 4 := by
  rw [l4q, Finset.sum_const, Finset.card_univ, fintype_card_matrix_zmod_two, nsmul_eq_mul]
  have h : (((2 ^ (m * n) : ℕ) : ℝ)) = (2 : ℝ) ^ (m * n) := by push_cast; ring
  rw [h, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)), one_mul]

/-- For a function of degree `0`, `‖f‖₄⁴ = (‖f‖₂²)²`. -/
lemma l4q_eq_sq_l2sq_of_degLe_zero {m n : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ}
    (hf : DegLe 0 f) : l4q f = (l2sq f) ^ 2 := by
  obtain ⟨c, rfl⟩ := exists_const_of_degLe_zero hf
  rw [l4q_const, l2sq_const]
  ring

/-! ## The strong induction hypothesis -/

/-- **The induction hypothesis of arXiv:2209.04243 §8 at level `D`** (equation `eq:ind-hyp`,
with the constant `100` replaced by an arbitrary `C`): every function of degree `≤ D`
satisfies the hypercontractive inequality with the *same* constant at its own degree. -/
def IHyp (C D : ℕ) : Prop :=
  ∀ (m n d : ℕ) (f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ), d ≤ D → DegLe d f →
    l4q f ≤ (2 : ℝ) ^ (C * d ^ 2) *
      ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ d
          then D4 V₁ W₁ (Lsub V₁ W₁ f) else 0

/-- Monotonicity of `IHyp` in the level. -/
theorem IHyp_mono {C D D' : ℕ} (h : IHyp C D) (hle : D' ≤ D) : IHyp C D' :=
  fun m n d f hd hf => h m n d f (le_trans hd hle) hf

/-- `IHyp` at every level gives Theorem 1.5. -/
theorem HypHyperUC_of_IHyp (C : ℕ) (hC : 0 < C) (h : ∀ D, IHyp C D) : HypHyperUC :=
  ⟨C, hC, fun m n d f hf => h d m n d f le_rfl hf⟩

/-- Conversely Theorem 1.5 gives `IHyp` at every level, with the same constant. -/
theorem IHyp_of_HypHyperUC (H : HypHyperUC) : ∃ C : ℕ, 0 < C ∧ ∀ D, IHyp C D := by
  obtain ⟨C, hC, h⟩ := H
  exact ⟨C, hC, fun D m n d f _ hf => h m n d f hf⟩

/-- **The base case**: every function of degree `0` satisfies the inequality with the trivial
constant. -/
theorem IHyp_zero (C : ℕ) : IHyp C 0 := by
  intro m n d f hd hf
  have hd0 : d = 0 := by omega
  subst hd0
  have h1 : l4q f = (l2sq f) ^ 2 := l4q_eq_sq_l2sq_of_degLe_zero hf
  have h2 : (l2sq f) ^ 2 ≤
      ∑ V₁ : Submodule 𝔽₂ (Fin n → 𝔽₂), ∑ W₁ : Submodule 𝔽₂ (Fin m → 𝔽₂),
        if Module.finrank 𝔽₂ V₁ + (m - Module.finrank 𝔽₂ W₁) ≤ 0
          then D4 V₁ W₁ (Lsub V₁ W₁ f) else 0 := l2sq_sq_le_sum_D4 0 f
  have h3 : (2 : ℝ) ^ (C * 0 ^ 2) = 1 := by norm_num
  rw [h1, h3, one_mul]
  exact h2

/-- **The strong induction carried out**: the base case plus the inductive step give `IHyp C D`
for every `D`. -/
theorem forall_IHyp_of_step (C : ℕ)
    (hstep : ∀ d : ℕ, 0 < d → IHyp C (d - 1) → IHyp C d) :
    IHyp C 0 → ∀ D, IHyp C D := by
  intro h0 D
  induction D with
  | zero => exact h0
  | succ D ih =>
      have := hstep (D + 1) (Nat.succ_pos D) (by simpa using ih)
      simpa using this

end

end Submission.Grassmann

namespace Submission.Grassmann

noncomputable section

local notation "𝔽₂" => ZMod 2

variable {m n : ℕ}

/-! ## `lem:after restricting` with the shifts averaged out

Combining `lem:after restricting` with `sum_l4q_DopX` (averaging over the shift `T`) replaces the
per-`T` sums of the `X`-derivatives by the fourth moments of a single Laplacian of the *big*
space.  This is the form in which the induction hypothesis is applied. -/

/-- The Fourier-multiplier predicate of the `X`-derivative of a triple `t = (V₂,W₂,X)`. -/
abbrev XtPred {m n : ℕ} (t : Triple m n) : Matrix (Fin n) (Fin m) 𝔽₂ → Prop :=
  fun Y => plLE (XtOf t.1 t.2.1 t.2.2) (charMat t.1 t.2.1 Y)

theorem trV₁_ge (t : Triple m n) : t.1 ≤ trV₁ t := by
  intro x hx
  rw [trV₁, Submodule.mem_comap]
  have h0 : Submodule.mkQ t.1 x = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hx
  rw [h0]
  exact Submodule.zero_mem _

theorem trW₁_le (t : Triple m n) : trW₁ t ≤ t.2.1 := Submodule.map_subtype_le _ _

/-- **`lem:after restricting`, shift-averaged form.** -/
theorem after_restricting' {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f) :
    l4q f ≤ 162 * 2 ^ (6 * d ^ 2) * (l2sq f) ^ 2 +
      2 * ∑ t : Triple m n,
        (if totOrder t = 0 then 0
         else 2 ^ (26 * d * totOrder t) *
           l4q (lapMulN (XtPred t) (Lsub t.1 t.2.1 f))) := by
  refine (after_restricting hf).trans ?_
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun t _ => le_of_eq ?_)
  by_cases ht0 : totOrder t = 0
  · rw [if_pos ht0, if_pos ht0, mul_zero]
  · rw [if_neg ht0, if_neg ht0]
    rw [sum_l4q_DopX (trV₁ t) (trW₁ t) t.1 t.2.1 t.2.2 f (trV₁_ge t) (trW₁_le t)]
    set c : ℝ := (2 : ℝ) ^ (26 * d * totOrder t) with hc
    set g : ℝ := l4q (lapMulN (XtPred t) (Lsub t.1 t.2.1 f)) with hg
    set Q : ℝ := (2 : ℝ) ^ (m * n) with hQ
    have hQ0 : Q ≠ 0 := by rw [hQ]; exact pow_ne_zero _ (by norm_num)
    have hkey : Q⁻¹ * (Q * g) = g := by
      rw [← mul_assoc, inv_mul_cancel₀ hQ0, one_mul]
    calc Q⁻¹ * (c * (Q * g)) = c * (Q⁻¹ * (Q * g)) := by ring
      _ = c * g := by rw [hkey]

/-- The order of a triple bounds the rank of every character kept by `XtPred t ∧ hp`. -/
theorem totOrder_le_rank_of_XtPred {t : Triple m n} {Y : Matrix (Fin n) (Fin m) 𝔽₂}
    (h1 : hybridPredSub t.1 t.2.1 Y) (h2 : XtPred t Y) : totOrder t ≤ Y.rank := by
  have hXrank : (XtOf t.1 t.2.1 t.2.2).rank = Module.finrank 𝔽₂ (LinearMap.range t.2.2) :=
    rank_XtOf t.1 t.2.1 t.2.2
  have hcrank : (charMat t.1 t.2.1 Y).rank =
      Module.finrank 𝔽₂ (LinearMap.range (YlinOf t.1 t.2.1 Y)) := by
    rw [charMat_eq_XtOf, rank_XtOf]
  have hle : (XtOf t.1 t.2.1 t.2.2).rank ≤ (charMat t.1 t.2.1 Y).rank := plLE_rank_le h2
  rw [hXrank, hcrank, finrank_range_YlinOf h1] at hle
  have hord := hybridPredSub_order_le_rank t.1 t.2.1 Y h1
  simp only [totOrder]
  omega

/-- The multiplier `L_{XtPred t} (Lsub t.1 t.2.1 f)` has degree at most `d` whenever `f` does
(and its non-vanishing Fourier coefficients have rank at least `totOrder t`). -/
theorem degLe_XtPred_Lsub {d : ℕ} {f : Matrix (Fin m) (Fin n) 𝔽₂ → ℂ} (hf : DegLe d f)
    (t : Triple m n) : DegLe d (lapMulN (XtPred t) (Lsub t.1 t.2.1 f)) :=
  degLe_lapMulN (P := XtPred t) (degLe_lapMulN (P := hybridPredSub t.1 t.2.1) hf)

end

end Submission.Grassmann
