import Mathlib
import Submission.Work.Peluse.LadderP.p3HeartDefs

/-! LEAD-FROZEN (curric-46, 2026-10-03): vocabulary of the regime-swap + dense-concatenation route for ∀ t ≥ 1, lemma51P t. Design: Submission/Work/Peluse/P2P3_LEAD.md. Do not edit. Node theorems are separate requests. -/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderP.Swap

noncomputable section
open Work.Peluse

/-! ## 0. Vocabulary -/

/-- Element `q₁·(m₁+1) − q₂·(m₂+1)` of the multiset slot `q₁[M] − q₂[M]`
(a *raw* slot `q₁[M]` when `q₂ = 0`). -/
def pdir (q₁ q₂ : ℤ) {M : ℕ} (m : Fin M × Fin M) : ℤ :=
  q₁ * (((m.1 : ℕ) : ℤ) + 1) - q₂ * (((m.2 : ℕ) : ℤ) + 1)

/-- Box sum along the multiset slots `q₁ k·[M] − q₂ k·[M]`, `k < d`, Peluse normalisation `1/|S|`. -/
def pboxSum (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) : ℂ :=
  ((S.card : ℂ))⁻¹ * (((M : ℂ) ^ 4)⁻¹) ^ d *
    ∑ h : Fin d → Fin M × Fin M, ∑ h' : Fin d → Fin M × Fin M,
      ∑' x : ℤ, ∏ ω : Fin d → Bool, (star^[weight ω])
        (f (x + cornerShift (fun k => pdir (q₁ k) (q₂ k) (h k))
                            (fun k => pdir (q₁ k) (q₂ k) (h' k)) ω))

/-- The `2^d`-th power of the multiset box norm. -/
def pbox (d : ℕ) (q₁ q₂ : Fin d → ℤ) (M : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) : ℝ :=
  ‖pboxSum d q₁ q₂ M S f‖

/-- Uniform average over a nonempty finite type. -/
def avg {I : Type} [Fintype I] (F : I → ℝ) : ℝ := ((Fintype.card I : ℝ))⁻¹ * ∑ i, F i

/-- The *dense* average produced by the regime swap: slopes `ω·(h−h')`, `h,h' ∈ [H]^t`
(small), windows `[M]` (large).  It is `Concat.boxAvg t H 1 (omegaOf t) M N f` with an
arbitrary normalisation set `S`. -/
def denseAvg (t H M : ℕ) (S : Finset ℤ) (f : ℤ → ℂ) : ℝ :=
  ((H : ℝ))⁻¹ ^ (2 * t) *
    ∑ h : Fin t → Fin H, ∑ h' : Fin t → Fin H,
      boxNormPow (2 ^ t - 1)
        (fun i => arithIcc (Concat.dotZ (Holds.omegaOf t i) (Concat.tupSub h h')) M) S f

/-! ## 1. Slot set of the iterated concatenation (KKL Prop. 6.2), 0-based -/

/-- Triples `(j, ε, ε')`: `ε, ε'` agree before the pivot `s-1-j`, `ε = 1`, `ε' = 0` at the pivot. -/
def slotSet (s : ℕ) : Finset (Fin s × (Fin s → Bool) × (Fin s → Bool)) :=
  Finset.univ.filter (fun p =>
    (∀ r : Fin s, r.val + p.1.val + 1 < s → p.2.1 r = p.2.2 r) ∧
    (∀ r : Fin s, r.val + p.1.val + 1 = s → p.2.1 r = true ∧ p.2.2 r = false))

def slotCard (s : ℕ) : ℕ := (slotSet s).card

def slotAt (s : ℕ) (k : Fin (slotCard s)) : Fin s × (Fin s → Bool) × (Fin s → Bool) :=
  ((slotSet s).equivFin.symm k).1


/-- A coefficient pair is *generic* at scale `H` with parameter `η`. -/
def genPair (H : ℕ) (η : ℝ) (q₁ q₂ : ℤ) : Prop :=
  η * (H : ℝ) ≤ ((|q₁| : ℤ) : ℝ) ∧ η * (H : ℝ) ≤ ((|q₂| : ℤ) : ℝ) ∧
    ((Int.gcd q₁ q₂ : ℕ) : ℝ) ≤ 1 / η

end
end Work.Peluse.LadderP.Swap
