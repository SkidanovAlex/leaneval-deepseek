/-
# Expansions with size and error data

`CuspExp K T f P n M q N` bundles a *size* bound for `f` (exponent `n`, weight `M`) with an
*error* bound for `f - P` (exponent `q`, weight `N`), both in the gauge `cuspG` of
`Submission/Work/Asymptotics/CuspExp/Basic.lean`.  The atoms of the CKMRV kernel are expanded
in this form, and it is closed under multiplication and under multiplication by functions of
`τ` bounded on `K`.
-/
import Mathlib
import Submission.Work.Asymptotics.CuspExp.Basic

namespace Work.Asymptotics

open UpperHalfPlane

noncomputable section

/-- A size bound for `f` together with an error bound for the model `P`. -/
def CuspExp (K : Set ℍ) (T : ℝ) (f P : ℍ → ℍ → ℂ) (n : ℤ) (M : ℝ) (q : ℤ) (N : ℝ) : Prop :=
  CuspBdd K T f n M ∧ CuspBdd K T (fun τ z => f τ z - P τ z) q N

namespace CuspExp

variable {K : Set ℍ} {T : ℝ} {f P g Q : ℍ → ℍ → ℂ}
variable {n₁ : ℤ} {M₁ : ℝ} {q₁ : ℤ} {N₁ : ℝ} {n₂ : ℤ} {M₂ : ℝ} {q₂ : ℤ} {N₂ : ℝ}

lemma size {n : ℤ} {M : ℝ} {q : ℤ} {N : ℝ} (h : CuspExp K T f P n M q N) :
    CuspBdd K T f n M := h.1

lemma err {n : ℤ} {M : ℝ} {q : ℤ} {N : ℝ} (h : CuspExp K T f P n M q N) :
    CuspBdd K T (fun τ z => f τ z - P τ z) q N := h.2

/-- The model inherits a bound from the size and the error. -/
lemma model {n : ℤ} {M : ℝ} {q : ℤ} {N : ℝ} (h : CuspExp K T f P n M q N) (hT : 0 ≤ T) :
    CuspBdd K T P (min n q) (max M N) := by
  have h1 : CuspBdd K T f (min n q) (max M N) := h.1.mono hT (min_le_left _ _) (le_max_left _ _)
  have h2 : CuspBdd K T (fun τ z => f τ z - P τ z) (min n q) (max M N) :=
    h.2.mono hT (min_le_right _ _) (le_max_right _ _)
  refine (h1.sub h2).congr (fun τ z => ?_)
  ring

/-- Monotonicity of the data. -/
lemma mono {n : ℤ} {M : ℝ} {q : ℤ} {N : ℝ} (hT : 0 ≤ T) {n' : ℤ} {M' : ℝ} {q' : ℤ} {N' : ℝ}
    (hn : n' ≤ n) (hM : M ≤ M') (hq : q' ≤ q) (hN : N ≤ N')
    (h : CuspExp K T f P n M q N) : CuspExp K T f P n' M' q' N' :=
  ⟨h.1.mono hT hn hM, h.2.mono hT hq hN⟩

/-- Multiplication by a bounded function of `τ`. -/
lemma mul_const (c : ℍ → ℂ) (B : ℝ) (hB : 0 < B) (hc : ∀ τ ∈ K, ‖c τ‖ ≤ B)
    {n : ℤ} {M : ℝ} {q : ℤ} {N : ℝ} (h : CuspExp K T f P n M q N) :
    CuspExp K T (fun τ z => c τ * f τ z) (fun τ z => c τ * P τ z) n M q N :=
  ⟨h.1.mul_const c B hB hc, by
    refine (h.2.mul_const c B hB hc).congr (fun τ z => ?_)
    ring⟩

/-- Product of two expansions: the size exponents add, the error exponent is
`min (q₁ + n₂) (min n₁ q₁ + q₂)`. -/
lemma mul (hT : 0 ≤ T) (h₁ : CuspExp K T f P n₁ M₁ q₁ N₁) (h₂ : CuspExp K T g Q n₂ M₂ q₂ N₂) :
    CuspExp K T (fun τ z => f τ z * g τ z) (fun τ z => P τ z * Q τ z)
      (n₁ + n₂) (M₁ + M₂) (min (q₁ + n₂) (min n₁ q₁ + q₂))
      (max (N₁ + M₂) (max M₁ N₁ + N₂)) := by
  refine ⟨h₁.1.mul h₂.1, ?_⟩
  have hsplit : (fun τ z => f τ z * g τ z - P τ z * Q τ z) =
      fun τ z => (f τ z - P τ z) * g τ z + P τ z * (g τ z - Q τ z) := by
    funext τ z; ring
  rw [hsplit]
  -- both summands are bounded with the stated data
  have e1 : CuspBdd K T (fun τ z => (f τ z - P τ z) * g τ z) (q₁ + n₂) (N₁ + M₂) :=
    h₁.2.mul h₂.1
  have hP : CuspBdd K T P (min n₁ q₁) (max M₁ N₁) := h₁.model hT
  have e2 : CuspBdd K T (fun τ z => P τ z * (g τ z - Q τ z)) (min n₁ q₁ + q₂) (max M₁ N₁ + N₂) :=
    hP.mul h₂.2
  have h1' : CuspBdd K T (fun τ z => (f τ z - P τ z) * g τ z)
      (min (q₁ + n₂) (min n₁ q₁ + q₂)) (max (N₁ + M₂) (max M₁ N₁ + N₂)) :=
    e1.mono hT (min_le_left _ _) (le_max_left _ _)
  have h2' : CuspBdd K T (fun τ z => P τ z * (g τ z - Q τ z))
      (min (q₁ + n₂) (min n₁ q₁ + q₂)) (max (N₁ + M₂) (max M₁ N₁ + N₂)) :=
    e2.mono hT (min_le_right _ _) (le_max_right _ _)
  exact h1'.add h2'

/-- Composition with the identity `P = P'`: change the model. -/
lemma congr {P' : ℍ → ℍ → ℂ} (hPP' : ∀ τ z, P τ z = P' τ z)
    {n : ℤ} {M : ℝ} {q : ℤ} {N : ℝ} (h : CuspExp K T f P n M q N) :
    CuspExp K T f P' n M q N := by
  refine ⟨h.1, (h.2.congr (fun τ z => ?_))⟩
  rw [hPP' τ z]

end CuspExp

end

end Work.Asymptotics
