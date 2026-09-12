import Mathlib
import Submission.Szemeredi.Removal.H4

/-!
# The constants of the generalized counting lemma

This file defines, by recursion on the order `D` and the number `m` of edges, the
constants `Theta D m` (the relative error) and `X D m` (the `ρ`-coefficient) of Tao's
generalized counting lemma (arXiv:math/0503572, §4).

The recursion is
* `Theta D m = Theta (D-1) m + Σ_{j ≤ m} etaB D j`
* `X D m = X (D-1) m + Σ_{j ≤ m} (CB D j + 1)`
where `etaB D j` is the `b`-term constant at order `D` with `j` edges (which feeds on the
constants `Theta (D-1)` and `X (D-1)` of the lower order).
-/

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

/-- The `ρ = 1/F(M_0)` of the counting lemma. -/
noncomputable def rhoC (F M : ℕ → ℕ) : ℝ := 1 / (F (M 0) : ℝ)

/-- An upper bound for `log Rg` (valid for every edge of the hypergraph). -/
noncomputable def LupC (F M : ℕ → ℕ) : ℝ := Real.log (F (M 0)) + 2

/-- `log (F (M D))`: the lower bound for `log Rg` on edges of order `D`. -/
noncomputable def LamC (F M : ℕ → ℕ) (D : ℕ) : ℝ := Real.log (F (M D))

/-- `(F (M D))^{-1/2}`: the factor by which the `b`-term is damped at order `D`. -/
noncomputable def PsiC (F M : ℕ → ℕ) (D : ℕ) : ℝ := (Real.sqrt (F (M D) : ℝ))⁻¹

/-- The `b`-term constant at order `D` for a bundle with `j` edges. -/
noncomputable def etaBC (F M : ℕ → ℕ) (D j : ℕ) (th X : ℕ → ℝ) : ℝ :=
  2 * PsiC F M D *
    (Real.sqrt (1 + th j) * Real.sqrt (1 + th (2 * j)) * (LamC F M D) ^ j
      + Real.sqrt (rhoC F M) *
          (Real.sqrt (1 + th j) * Real.sqrt (X (2 * j))
            + Real.sqrt (1 + th (2 * j)) * Real.sqrt (X j)) * (LupC F M) ^ j)

/-- The `ρ`-coefficient produced by the `b`-term at order `D` for `j` edges. -/
noncomputable def CBc (F M : ℕ → ℕ) (D j : ℕ) (X : ℕ → ℝ) : ℝ :=
  2 * PsiC F M D * Real.sqrt (X j * X (2 * j))

mutual
  /-- The relative error of the generalized counting lemma at order `D` with `m` edges. -/
  noncomputable def ThetaC (F M : ℕ → ℕ) : ℕ → ℕ → ℝ
    | 0, _ => 0
    | (D + 1), m => ThetaC F M D m
        + ∑ j ∈ Finset.range m, etaBC F M (D + 1) (j + 1) (ThetaC F M D) (XC F M D)

  /-- The `ρ`-coefficient of the generalized counting lemma at order `D` with `m` edges. -/
  noncomputable def XC (F M : ℕ → ℕ) : ℕ → ℕ → ℝ
    | 0, _ => 1
    | (D + 1), m => XC F M D m
        + ∑ j ∈ Finset.range m, (CBc F M (D + 1) (j + 1) (XC F M D) + 1)
end

@[simp] theorem ThetaC_zero (F M : ℕ → ℕ) (m : ℕ) : ThetaC F M 0 m = 0 := rfl

@[simp] theorem XC_zero (F M : ℕ → ℕ) (m : ℕ) : XC F M 0 m = 1 := rfl

theorem ThetaC_succ (F M : ℕ → ℕ) (D m : ℕ) :
    ThetaC F M (D + 1) m = ThetaC F M D m
      + ∑ j ∈ Finset.range m, etaBC F M (D + 1) (j + 1) (ThetaC F M D) (XC F M D) := rfl

theorem XC_succ (F M : ℕ → ℕ) (D m : ℕ) :
    XC F M (D + 1) m = XC F M D m
      + ∑ j ∈ Finset.range m, (CBc F M (D + 1) (j + 1) (XC F M D) + 1) := rfl


/-! ## Elementary positivity and monotonicity -/

variable {F M : ℕ → ℕ}

theorem LamC_nonneg (hF : ∀ n, 1 ≤ F n) (D : ℕ) : 0 ≤ LamC F M D :=
  Real.log_nonneg (by exact_mod_cast hF (M D))

theorem LupC_ge_two (hF : ∀ n, 1 ≤ F n) : 2 ≤ LupC F M := by
  have := LamC_nonneg (M := M) hF 0
  unfold LupC LamC at *
  linarith

theorem LupC_pos (hF : ∀ n, 1 ≤ F n) : 0 < LupC F M := lt_of_lt_of_le (by norm_num) (LupC_ge_two hF)

theorem rhoC_nonneg (hF : ∀ n, 1 ≤ F n) : 0 ≤ rhoC F M := by
  unfold rhoC
  have : (0 : ℝ) < (F (M 0) : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (hF (M 0))
  positivity

theorem PsiC_nonneg (D : ℕ) : 0 ≤ PsiC F M D := by
  unfold PsiC; positivity

theorem PsiC_pos (hF : ∀ n, 1 ≤ F n) (D : ℕ) : 0 < PsiC F M D := by
  rw [PsiC]
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by
    have := hF (M D); exact_mod_cast (by omega : 0 < F (M D))))

theorem etaBC_nonneg (hF : ∀ n, 1 ≤ F n) (D j : ℕ) (th X : ℕ → ℝ) :
    0 ≤ etaBC F M D j th X := by
  unfold etaBC
  have h1 : (0 : ℝ) ≤ (LamC F M D) ^ j := pow_nonneg (LamC_nonneg hF D) j
  have h2 : (0 : ℝ) ≤ (LupC F M) ^ j := pow_nonneg (le_trans (by norm_num) (LupC_ge_two hF)) j
  have h3 : (0 : ℝ) ≤ Real.sqrt (1 + th j) * Real.sqrt (1 + th (2 * j)) * (LamC F M D) ^ j :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) h1
  have h4 : (0 : ℝ) ≤ Real.sqrt (rhoC F M) *
      (Real.sqrt (1 + th j) * Real.sqrt (X (2 * j))
        + Real.sqrt (1 + th (2 * j)) * Real.sqrt (X j)) * (LupC F M) ^ j :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _)
      (add_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))) h2
  exact mul_nonneg (mul_nonneg (by norm_num) (PsiC_nonneg (F := F) (M := M) D)) (add_nonneg h3 h4)

theorem CBc_nonneg (D j : ℕ) (X : ℕ → ℝ) : 0 ≤ CBc F M D j X := by
  unfold CBc
  have := PsiC_nonneg (F := F) (M := M) D
  positivity

theorem ThetaC_nonneg (hF : ∀ n, 1 ≤ F n) (D m : ℕ) : 0 ≤ ThetaC F M D m := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [ThetaC_succ]
    have : (0 : ℝ) ≤ ∑ j ∈ Finset.range m,
        etaBC F M (D + 1) (j + 1) (ThetaC F M D) (XC F M D) :=
      Finset.sum_nonneg (fun j _ => etaBC_nonneg hF (D + 1) (j + 1) _ _)
    linarith

theorem XC_one_le (D m : ℕ) : 1 ≤ XC F M D m := by
  induction D with
  | zero => simp
  | succ D ih =>
    rw [XC_succ]
    have : (0 : ℝ) ≤ ∑ j ∈ Finset.range m,
        (CBc F M (D + 1) (j + 1) (XC F M D) + 1) :=
      Finset.sum_nonneg (fun j _ => by have := CBc_nonneg (F := F) (M := M) (D + 1) (j + 1) (XC F M D); linarith)
    linarith

theorem XC_nonneg (D m : ℕ) : 0 ≤ XC F M D m := le_trans (by norm_num) (XC_one_le (F := F) (M := M) D m)

theorem ThetaC_mono_m (hF : ∀ n, 1 ≤ F n) {D : ℕ} : Monotone (ThetaC F M D) := by
  induction D with
  | zero => intro a b _; simp
  | succ D ih =>
    intro m m' hmm'
    rw [ThetaC_succ, ThetaC_succ]
    have h1 : ThetaC F M D m ≤ ThetaC F M D m' := ih hmm'
    have h2 : ∑ j ∈ Finset.range m, etaBC F M (D + 1) (j + 1) (ThetaC F M D) (XC F M D)
        ≤ ∑ j ∈ Finset.range m', etaBC F M (D + 1) (j + 1) (ThetaC F M D) (XC F M D) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hmm'))
        (fun x _ _ => etaBC_nonneg hF (D + 1) (x + 1) _ _)
    linarith

theorem XC_mono_m {D : ℕ} : Monotone (XC F M D) := by
  induction D with
  | zero => intro a b _; simp
  | succ D ih =>
    intro m m' hmm'
    rw [XC_succ, XC_succ]
    have h1 : XC F M D m ≤ XC F M D m' := ih hmm'
    have h2 : ∑ j ∈ Finset.range m, (CBc F M (D + 1) (j + 1) (XC F M D) + 1)
        ≤ ∑ j ∈ Finset.range m', (CBc F M (D + 1) (j + 1) (XC F M D) + 1) :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (fun x hx => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hmm'))
        (fun x _ _ => by have := CBc_nonneg (F := F) (M := M) (D + 1) (x + 1) (XC F M D); linarith)
    linarith

theorem ThetaC_succ_ge (hF : ∀ n, 1 ≤ F n) (D m : ℕ) :
    ThetaC F M D m ≤ ThetaC F M (D + 1) m := by
  rw [ThetaC_succ]
  have : (0 : ℝ) ≤ ∑ j ∈ Finset.range m,
      etaBC F M (D + 1) (j + 1) (ThetaC F M D) (XC F M D) :=
    Finset.sum_nonneg (fun j _ => etaBC_nonneg hF (D + 1) (j + 1) _ _)
  linarith

theorem XC_succ_ge (D m : ℕ) : XC F M D m ≤ XC F M (D + 1) m := by
  rw [XC_succ]
  have : (0 : ℝ) ≤ ∑ j ∈ Finset.range m,
      (CBc F M (D + 1) (j + 1) (XC F M D) + 1) :=
    Finset.sum_nonneg (fun j _ => by
      have := CBc_nonneg (F := F) (M := M) (D + 1) (j + 1) (XC F M D); linarith)
  linarith

theorem ThetaC_mono_D (hF : ∀ n, 1 ≤ F n) {D D' : ℕ} (m : ℕ) (h : D ≤ D') :
    ThetaC F M D m ≤ ThetaC F M D' m := by
  induction h with
  | refl => exact le_rfl
  | step hle ih => exact le_trans ih (ThetaC_succ_ge hF _ m)

theorem XC_mono_D {D D' : ℕ} (m : ℕ) (h : D ≤ D') :
    XC F M D m ≤ XC F M D' m := by
  induction h with
  | refl => exact le_rfl
  | step hle ih => exact le_trans ih (XC_succ_ge (F := F) (M := M) _ m)

/-- The one-step increase of `Theta` at order `D+1` in the number of edges. -/
theorem ThetaC_step (hF : ∀ n, 1 ≤ F n) (D m : ℕ) :
    ThetaC F M (D + 1) m + etaBC F M (D + 1) (m + 1) (ThetaC F M D) (XC F M D)
      ≤ ThetaC F M (D + 1) (m + 1) := by
  rw [ThetaC_succ F M D (m + 1), ThetaC_succ F M D m, Finset.sum_range_succ]
  have h1 : ThetaC F M D m ≤ ThetaC F M D (m + 1) :=
    ThetaC_mono_m hF (Nat.le_succ m)
  have h2 : (0 : ℝ) ≤ ∑ j ∈ Finset.range m,
      etaBC F M (D + 1) (j + 1) (ThetaC F M D) (XC F M D) :=
    Finset.sum_nonneg (fun j _ => etaBC_nonneg hF (D + 1) (j + 1) _ _)
  linarith

/-- The one-step increase of `X` at order `D+1` in the number of edges. -/
theorem XC_step (D m : ℕ) :
    XC F M (D + 1) m + CBc F M (D + 1) (m + 1) (XC F M D) + 1
      ≤ XC F M (D + 1) (m + 1) := by
  rw [XC_succ F M D (m + 1), XC_succ F M D m, Finset.sum_range_succ]
  have h1 : XC F M D m ≤ XC F M D (m + 1) := XC_mono_m (Nat.le_succ m)
  have h2 : (0 : ℝ) ≤ ∑ j ∈ Finset.range m,
      (CBc F M (D + 1) (j + 1) (XC F M D) + 1) :=
    Finset.sum_nonneg (fun j _ => by have := CBc_nonneg (F := F) (M := M) (D + 1) (j + 1) (XC F M D); linarith)
  linarith


/-- The one-step increase of `Theta`, in the form used at a top edge of order `D.succ`
with `m` edges. -/
theorem ThetaC_step' (hF : ∀ n, 1 ≤ F n) (D : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    ThetaC F M D.succ (m - 1) + etaBC F M D.succ m (ThetaC F M D) (XC F M D)
      ≤ ThetaC F M D.succ m := by
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  simpa only [hm'] using ThetaC_step hF D (m - 1)

/-- The one-step increase of `X`, in the form used at a top edge of order `D.succ`. -/
theorem XC_step' (D : ℕ) {m : ℕ} (hm : 1 ≤ m) :
    XC F M D.succ (m - 1) + CBc F M D.succ m (XC F M D) + 1 ≤ XC F M D.succ m := by
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  simpa only [hm'] using XC_step (F := F) (M := M) D (m - 1)

/-- The algebraic identity behind the `b`-term key: multiplying `etaBC` by `√(Rg)/2`
leaves the "square-rooted" bracket. -/
theorem etaBC_half (hF : ∀ n, 1 ≤ F n) (D m : ℕ) (th X : ℕ → ℝ) :
    etaBC F M D m th X / 2 * Real.sqrt ((F (M D) : ℕ) : ℝ)
      = Real.sqrt (1 + th m) * Real.sqrt (1 + th (2 * m)) * (LamC F M D) ^ m
        + Real.sqrt (rhoC F M) * (Real.sqrt (1 + th m) * Real.sqrt (X (2 * m))
          + Real.sqrt (1 + th (2 * m)) * Real.sqrt (X m)) * (LupC F M) ^ m := by
  have hs : Real.sqrt ((F (M D) : ℕ) : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    have := hF (M D); exact_mod_cast (by omega : 0 < F (M D))
  unfold etaBC PsiC
  field_simp

/-- The algebraic identity behind the `b`-term key for the `ρ`-coefficient. -/
theorem CBc_half (hF : ∀ n, 1 ≤ F n) (D m : ℕ) (X : ℕ → ℝ) :
    CBc F M D m X / 2 * Real.sqrt ((F (M D) : ℕ) : ℝ) = Real.sqrt (X m * X (2 * m)) := by
  have hs : Real.sqrt ((F (M D) : ℕ) : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.mpr
    have := hF (M D); exact_mod_cast (by omega : 0 < F (M D))
  unfold CBc PsiC
  field_simp

end Szemeredi.Removal
