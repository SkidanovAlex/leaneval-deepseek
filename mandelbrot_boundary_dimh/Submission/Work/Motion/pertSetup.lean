import Mathlib
import Submission.Work.Motion.Basic

/-!
# Perturbed inverse branches: setup

Definitions and elementary facts about the iterate polynomials
`(c,x) ↦ (Tc c)^[n] x` and their `x`-derivatives, used by `Work.Motion.exists_pertData`.
-/

namespace Work.Motion
namespace Pert

open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter Function

noncomputable section

/-- `TcIter n (c,x) = (Tc c)^[n] x`, viewed as a function on `ℂ × ℂ`. -/
def TcIter (n : ℕ) : ℂ × ℂ → ℂ :=
  Nat.rec (fun q => q.2) (fun _ f => fun q => Tc q.1 (f q)) n

@[simp] theorem TcIter_zero : TcIter 0 = fun q : ℂ × ℂ => q.2 := rfl
theorem TcIter_succ (n : ℕ) : TcIter (n + 1) = fun q : ℂ × ℂ => Tc q.1 (TcIter n q) := rfl
@[simp] theorem TcIter_succ_apply (n : ℕ) (q : ℂ × ℂ) :
    TcIter (n + 1) q = Tc q.1 (TcIter n q) := rfl

/-- `dTc n (c,x) = deriv (fun y => (Tc c)^[n] y) x = ∏_{j<n} 2 * (Tc c)^[j] x`. -/
def dTc (n : ℕ) : ℂ × ℂ → ℂ :=
  Nat.rec (fun _ => 1) (fun k g => fun q => 2 * TcIter k q * g q) n

@[simp] theorem dTc_zero : dTc 0 = fun _ : ℂ × ℂ => 1 := rfl
theorem dTc_succ (n : ℕ) : dTc (n + 1) = fun q : ℂ × ℂ => 2 * TcIter n q * dTc n q := rfl
@[simp] theorem dTc_succ_apply (n : ℕ) (q : ℂ × ℂ) :
    dTc (n + 1) q = 2 * TcIter n q * dTc n q := rfl

theorem TcIter_eq (n : ℕ) (c x : ℂ) : TcIter n (c, x) = (Tc c)^[n] x := by
  induction n with
  | zero => simp
  | succ n ih => rw [TcIter_succ_apply, ih, Function.iterate_succ_apply']

/-- `Tc c` is complex differentiable everywhere. -/
theorem differentiable_Tc (c : ℂ) : Differentiable ℂ (Tc c) := by
  have h : Tc c = fun z : ℂ => z ^ 2 + c := rfl
  rw [h]
  exact (differentiable_id.pow 2).add_const c

/-- The derivative of `Tc c`. -/
theorem deriv_Tc (c y : ℂ) : deriv (Tc c) y = 2 * y := by
  have hd : HasDerivAt (fun z : ℂ => z ^ 2 + c) (2 * y) y := by
    have h := (hasDerivAt_pow 2 y).add_const c
    simpa using h
  exact hd.deriv

/-- The `x`-derivative of the `n`-th iterate of `Tc c` is the polynomial `dTc n`. -/
theorem deriv_TcIter (n : ℕ) (c x : ℂ) :
    deriv (fun y => (Tc c)^[n] y) x = dTc n (c, x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (fun y : ℂ => (Tc c)^[n.succ] y) = (Tc c) ∘ (Tc c)^[n] := by
      funext y; rw [Function.iterate_succ_apply']; rfl
    have hA : DifferentiableAt ℂ (Tc c) ((Tc c)^[n] x) := (differentiable_Tc c).differentiableAt
    have hB : DifferentiableAt ℂ ((Tc c)^[n]) x := ((differentiable_Tc c).iterate n).differentiableAt
    have hcomp : HasDerivAt ((Tc c) ∘ (Tc c)^[n])
        (2 * (Tc c)^[n] x * dTc n (c,x)) x := by
      have hh := hA.hasDerivAt.comp x hB.hasDerivAt
      rwa [deriv_Tc, ih] at hh
    rw [h1, hcomp.deriv, dTc_succ_apply, TcIter_eq]

/-- `TcIter n` is complex differentiable. -/
theorem differentiable_TcIter (n : ℕ) : Differentiable ℂ (TcIter n) := by
  induction n with
  | zero => simpa using (differentiable_snd :
      Differentiable ℂ (fun q : ℂ × ℂ => q.2))
  | succ n ih =>
    have h : TcIter (n + 1) = (fun p : ℂ × ℂ => Tc p.1 p.2) ∘
        (fun q : ℂ × ℂ => (q.1, TcIter n q)) := by
      funext q; simp
    rw [h]
    refine Differentiable.comp ?_ (Differentiable.prodMk differentiable_fst ih)
    have h2 : (fun p : ℂ × ℂ => Tc p.1 p.2) = fun p : ℂ × ℂ => p.2 ^ 2 + p.1 := rfl
    rw [h2]
    exact (differentiable_snd.pow 2).add differentiable_fst

/-- `dTc n` is complex differentiable. -/
theorem differentiable_dTc (n : ℕ) : Differentiable ℂ (dTc n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : dTc (n + 1) = fun q : ℂ × ℂ => 2 * TcIter n q * dTc n q := rfl
    rw [h]
    exact ((differentiable_const (2 : ℂ)).mul (differentiable_TcIter n)).mul ih

/-- `TcIter n` is `C^1` over `ℝ`. -/
theorem contDiff_TcIter (n : ℕ) : ContDiff ℝ 1 (TcIter n) := by
  induction n with
  | zero => simpa using (contDiff_snd :
      ContDiff ℝ (1 : WithTop ℕ∞) (fun q : ℂ × ℂ => q.2))
  | succ n ih =>
    have h : TcIter (n + 1) = (fun p : ℂ × ℂ => Tc p.1 p.2) ∘
        (fun q : ℂ × ℂ => (q.1, TcIter n q)) := by
      funext q; simp
    rw [h]
    refine ContDiff.comp ?_ (ContDiff.prodMk contDiff_fst ih)
    have h2 : (fun p : ℂ × ℂ => Tc p.1 p.2) = fun p : ℂ × ℂ => p.2 ^ 2 + p.1 := rfl
    rw [h2]
    exact (contDiff_snd.pow 2).add contDiff_fst

/-- `dTc n` is `C^1` over `ℝ`. -/
theorem contDiff_dTc (n : ℕ) : ContDiff ℝ 1 (dTc n) := by
  induction n with
  | zero => simpa using (contDiff_const : ContDiff ℝ (1 : WithTop ℕ∞) (fun _ : ℂ × ℂ => (1:ℂ)))
  | succ n ih =>
    have h : dTc (n + 1) = fun q : ℂ × ℂ => 2 * TcIter n q * dTc n q := rfl
    rw [h]
    exact (contDiff_const.mul (contDiff_TcIter n)).mul ih

/-- The inner radius used for the perturbed inverse branches: `r / 2 < rInner r < r`. -/
def rInner (r : ℝ) : ℝ := 7 * r / 8

open scoped NNReal

/-- `Amap τ m q = (Tc q.1)^[m] (τ q.2) - q.2`: the defect of the unperturbed branch. -/
def Amap (τ : ℂ → ℂ) (m : ℕ) : ℂ × ℂ → ℂ := fun q => TcIter m (q.1, τ q.2) - q.2

/-- `Bmap τ m q = d/dx (Tc q.1)^[m] x` at `x = τ q.2`. -/
def Bmap (τ : ℂ → ℂ) (m : ℕ) : ℂ × ℂ → ℂ := fun q => dTc m (q.1, τ q.2)

/-- `Fmap τ m q w = (Tc q.1)^[m] (τ q.2 + w) - (Tc q.1)^[m] (τ q.2)`. -/
def Fmap (τ : ℂ → ℂ) (m : ℕ) : ℂ × ℂ → ℂ → ℂ :=
  fun q w => TcIter m (q.1, τ q.2 + w) - TcIter m (q.1, τ q.2)

/-- The Newton map for the moving inverse branch. -/
def Psimap (τ : ℂ → ℂ) (m : ℕ) : ℂ × ℂ → ℂ → ℂ :=
  fun q w => w - (TcIter m (q.1, τ q.2 + w) - q.2) / Bmap τ m q

@[simp] theorem Amap_apply (τ : ℂ → ℂ) (m : ℕ) (q : ℂ × ℂ) :
    Amap τ m q = TcIter m (q.1, τ q.2) - q.2 := rfl

@[simp] theorem Bmap_apply (τ : ℂ → ℂ) (m : ℕ) (q : ℂ × ℂ) :
    Bmap τ m q = dTc m (q.1, τ q.2) := rfl

@[simp] theorem Fmap_apply (τ : ℂ → ℂ) (m : ℕ) (q : ℂ × ℂ) (w : ℂ) :
    Fmap τ m q w = TcIter m (q.1, τ q.2 + w) - TcIter m (q.1, τ q.2) := rfl

@[simp] theorem Psimap_apply (τ : ℂ → ℂ) (m : ℕ) (q : ℂ × ℂ) (w : ℂ) :
    Psimap τ m q w = w - (TcIter m (q.1, τ q.2 + w) - q.2) / Bmap τ m q := rfl

theorem Fmap_zero (τ : ℂ → ℂ) (m : ℕ) (q : ℂ × ℂ) : Fmap τ m q 0 = 0 := by
  simp [Fmap_apply]

/-- The equation `Fmap τ m q w = -Amap τ m q` is the fixed point equation for the branch. -/
theorem Fmap_neg_Amap_iff (τ : ℂ → ℂ) (m : ℕ) (q : ℂ × ℂ) (w : ℂ) :
    Fmap τ m q w = -Amap τ m q ↔ TcIter m (q.1, τ q.2 + w) = q.2 := by
  simp only [Fmap_apply, Amap_apply]
  constructor <;> intro h <;> linear_combination h

end

end Pert
end Work.Motion
