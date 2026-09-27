import Mathlib
import Submission.Work.EKLComp.Entropy

set_option maxHeartbeats 1000000

namespace Work.EKLComp

open MeasureTheory
open Work.EKLContract

variable {X : Type*} [mX : MeasurableSpace X]

/-! ## Iterates of mutually inverse maps -/

/-- If `S` is a left inverse of `T`, then `S^[k]` sends the `m`-th iterate of `T` back
`k` steps, as long as `k ≤ m`. -/
theorem ek_iterate_leftInverse {T S : X → X} (hl : Function.LeftInverse S T) (m k : ℕ)
    (hk : k ≤ m) (x : X) : S^[k] (T^[m] x) = T^[m - k] x := by
  have h1 : T^[m] x = T^[k] (T^[m - k] x) := by
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le hk]
  rw [h1]
  exact (hl.iterate k) (T^[m - k] x)

/-- The reversal of `Fin (m+1)` in value form. -/
theorem ek_val_rev_eq (m : ℕ) (k : Fin (m+1)) : (Fin.rev k).val = m - k.val := by
  rw [Fin.val_rev]
  omega

/-- Reversing the coordinates of a word `Fin N → Fin n` is a permutation. -/
def ekRevWordEquiv (N n : ℕ) : (Fin N → Fin n) ≃ (Fin N → Fin n) where
  toFun w := fun k => w (Fin.rev k)
  invFun w := fun k => w (Fin.rev k)
  left_inv w := by funext k; simp [Fin.rev_rev]
  right_inv w := by funext k; simp [Fin.rev_rev]

@[simp] theorem ekRevWordEquiv_apply (N n : ℕ) (w : Fin N → Fin n) :
    ekRevWordEquiv N n w = fun k => w (Fin.rev k) := rfl

/-! ## The key preimage identity -/

/-- Pulling back the `(m+1)`-fold join along `S = T⁻¹` by `T^[m]` gives the `(m+1)`-fold
join along `T` with the word reversed. -/
theorem ek_preimage_iterate_joinSets {T S : X → X} (hl : Function.LeftInverse S T)
    (P : FinPart X) (m : ℕ) (w : Fin (m+1) → Fin P.n) :
    T^[m] ⁻¹' joinSets S P (m+1) (fun k => w (Fin.rev k)) = joinSets T P (m+1) w := by
  ext x
  simp only [joinSets, Set.mem_preimage, Set.mem_iInter]
  constructor
  · intro h j
    have hk : (Fin.rev j).val ≤ m := by have := (Fin.rev j).isLt; omega
    have hmem := h (Fin.rev j)
    rw [ek_iterate_leftInverse hl m (Fin.rev j).val hk,
        ← ek_val_rev_eq m (Fin.rev j), Fin.rev_rev] at hmem
    exact hmem
  · intro h k
    have hk : k.val ≤ m := by have := k.isLt; omega
    rw [ek_iterate_leftInverse hl m k.val hk, ← ek_val_rev_eq m k]
    exact h (Fin.rev k)

/-! ## Equality of the Shannon entropies of the joins -/

/-- The `(m+1)`-fold joins along `T` and along a left inverse `S` have the same
Shannon entropy: the atoms correspond under `T^[m]`, which preserves measure. -/
theorem ek_Hfam_joinSets_inv (μ : Measure X) [IsProbabilityMeasure μ] {T S : X → X}
    (hmp : MeasurePreserving T μ μ) (hS : Measurable S) (hl : Function.LeftInverse S T)
    (P : FinPart X) (m : ℕ) :
    Hfam μ (joinSets T P (m+1)) = Hfam μ (joinSets S P (m+1)) := by
  have hstep : ∀ w : Fin (m+1) → Fin P.n,
      μ (joinSets T P (m+1) w)
        = μ (joinSets S P (m+1) (ekRevWordEquiv (m+1) P.n w)) := by
    intro w
    have hset := ek_preimage_iterate_joinSets hl P m w
    have hmeas : NullMeasurableSet
        (joinSets S P (m+1) (ekRevWordEquiv (m+1) P.n w)) μ :=
      (Work.EKLComp.Core.joinSets_measurable hS P (m+1)
        (ekRevWordEquiv (m+1) P.n w)).nullMeasurableSet
    rw [← hset]
    exact (hmp.iterate m).measure_preimage hmeas
  calc Hfam μ (joinSets T P (m+1))
      = Hfam μ (fun w : Fin (m+1) → Fin P.n =>
          joinSets S P (m+1) (ekRevWordEquiv (m+1) P.n w)) := by
        simp only [Hfam]
        exact Finset.sum_congr rfl fun w _ => by rw [hstep w]
    _ = Hfam μ (joinSets S P (m+1)) :=
        Work.EKLComp.Core.Hfam_equiv μ (ekRevWordEquiv (m+1) P.n) (joinSets S P (m+1))

/-! ## The Fekete infimum and the main theorem -/

/-- `hPart` is an invariant of left inverses of measure-preserving maps. -/
theorem hPart_eq_of_leftInverse {X : Type*} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] {T S : X → X} (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (hS : Measurable S) (hl : Function.LeftInverse S T) (P : Work.EKLContract.FinPart X) :
    @Work.EKLContract.hPart X mX μ S P = @Work.EKLContract.hPart X mX μ T P := by
  have hfun : (fun N : ℕ => Hfam μ (joinSets S P (N + 1)) / ((N : ℝ) + 1))
      = (fun N : ℕ => Hfam μ (joinSets T P (N + 1)) / ((N : ℝ) + 1)) :=
    funext fun N => by rw [(ek_Hfam_joinSets_inv μ hmp hS hl P N).symm]
  show (⨅ N : ℕ, Hfam μ (joinSets S P (N + 1)) / ((N : ℝ) + 1))
      = (⨅ N : ℕ, Hfam μ (joinSets T P (N + 1)) / ((N : ℝ) + 1))
  rw [hfun]

end Work.EKLComp
