import Mathlib
import Submission.Work.EKLComp.Entropy

/-!
# C3 — `ent μ S = ent μ T` for a measure-preserving `T` with two-sided inverse `S`

The Kolmogorov–Sinai entropy `ent μ T` of a measure-preserving transformation is a
conjugation invariant; in particular it does not change when `T` is replaced by its
inverse.  Here `T : X → X` is measure preserving and `S` is a two-sided inverse
(`S ∘ T = id` and `T ∘ S = id`, so `T` is a bijection with inverse `S`).

The proof compares the `N`-fold join partitions
`joinSets T P N w = ⋂_{k<N} T^[k] ⁻¹' P_{w k}` and `joinSets S P N w` atom by atom.
Since `S = T⁻¹`, applying `T^[m]` (with `N = m+1`) to the `(m+1)`-fold join along
`S` produces the `(m+1)`-fold join along `T` with the word reversed:

`T^[m] ⁻¹' joinSets S P (m+1) (w ∘ Fin.rev) = joinSets T P (m+1) w`.

As `T` is measure preserving and `Fin.rev` is an involution, the Shannon entropies of
the two joins coincide; taking the Fekete infimum over `N` gives `hPart μ S P = hPart μ T P`
for every finite partition `P`, and hence `ent μ S = ent μ T`.
-/

open MeasureTheory
open Work.EKLContract

noncomputable section

namespace Work.EKLComp

variable {X : Type} [mX : MeasurableSpace X]

/-! ## Iterates of mutually inverse maps -/

/-- If `S` is a left inverse of `T`, then `S^[k]` sends the `m`-th iterate of `T` back
`k` steps, as long as `k ≤ m`. -/
theorem iterate_leftInverse {T S : X → X} (hl : Function.LeftInverse S T) (m k : ℕ)
    (hk : k ≤ m) (x : X) : S^[k] (T^[m] x) = T^[m - k] x := by
  have h1 : T^[m] x = T^[k] (T^[m - k] x) := by
    rw [← Function.iterate_add_apply, Nat.add_sub_of_le hk]
  rw [h1]
  exact (hl.iterate k) (T^[m - k] x)

/-- The reversal of `Fin (m+1)` in value form. -/
theorem val_rev_eq (m : ℕ) (k : Fin (m+1)) : (Fin.rev k).val = m - k.val := by
  rw [Fin.val_rev]
  omega

/-- Reversing the coordinates of a word `Fin N → Fin n` is a permutation. -/
def revWordEquiv (N n : ℕ) : (Fin N → Fin n) ≃ (Fin N → Fin n) where
  toFun w := fun k => w (Fin.rev k)
  invFun w := fun k => w (Fin.rev k)
  left_inv w := by funext k; simp [Fin.rev_rev]
  right_inv w := by funext k; simp [Fin.rev_rev]

@[simp] theorem revWordEquiv_apply (N n : ℕ) (w : Fin N → Fin n) :
    revWordEquiv N n w = fun k => w (Fin.rev k) := rfl

/-! ## The key preimage identity -/

/-- Pulling back the `(m+1)`-fold join along `S = T⁻¹` by `T^[m]` gives the `(m+1)`-fold
join along `T` with the word reversed. -/
theorem preimage_iterate_joinSets {T S : X → X} (hl : Function.LeftInverse S T)
    (P : FinPart X) (m : ℕ) (w : Fin (m+1) → Fin P.n) :
    T^[m] ⁻¹' joinSets S P (m+1) (fun k => w (Fin.rev k)) = joinSets T P (m+1) w := by
  ext x
  simp only [joinSets, Set.mem_preimage, Set.mem_iInter]
  constructor
  · intro h j
    have hk : (Fin.rev j).val ≤ m := by have := (Fin.rev j).isLt; omega
    have hmem := h (Fin.rev j)
    rw [iterate_leftInverse hl m (Fin.rev j).val hk,
        ← val_rev_eq m (Fin.rev j), Fin.rev_rev] at hmem
    exact hmem
  · intro h k
    have hk : k.val ≤ m := by have := k.isLt; omega
    rw [iterate_leftInverse hl m k.val hk, ← val_rev_eq m k]
    exact h (Fin.rev k)

/-! ## Equality of the Shannon entropies of the joins -/

/-- The `(m+1)`-fold joins along `T` and along a two-sided inverse `S` have the same
Shannon entropy: the atoms correspond under `T^[m]`, which preserves measure. -/
theorem Hfam_joinSets_inv (μ : Measure X) [IsProbabilityMeasure μ] {T S : X → X}
    (hmp : MeasurePreserving T μ μ) (hS : Measurable S) (hl : Function.LeftInverse S T)
    (P : FinPart X) (m : ℕ) :
    Hfam μ (joinSets T P (m+1)) = Hfam μ (joinSets S P (m+1)) := by
  have hstep : ∀ w : Fin (m+1) → Fin P.n,
      μ (joinSets T P (m+1) w)
        = μ (joinSets S P (m+1) (revWordEquiv (m+1) P.n w)) := by
    intro w
    have hset := preimage_iterate_joinSets hl P m w
    have hmeas : NullMeasurableSet
        (joinSets S P (m+1) (revWordEquiv (m+1) P.n w)) μ :=
      (Work.EKLComp.Core.joinSets_measurable hS P (m+1)
        (revWordEquiv (m+1) P.n w)).nullMeasurableSet
    rw [← hset]
    exact (hmp.iterate m).measure_preimage hmeas
  calc Hfam μ (joinSets T P (m+1))
      = Hfam μ (fun w : Fin (m+1) → Fin P.n =>
          joinSets S P (m+1) (revWordEquiv (m+1) P.n w)) := by
        simp only [Hfam]
        exact Finset.sum_congr rfl fun w _ => by rw [hstep w]
    _ = Hfam μ (joinSets S P (m+1)) :=
        Work.EKLComp.Core.Hfam_equiv μ (revWordEquiv (m+1) P.n) (joinSets S P (m+1))

/-! ## The Fekete infimum and the main theorem -/

/-- `hPart` is an invariant of two-sided inverses of measure-preserving maps. -/
theorem hPart_inv (μ : Measure X) [IsProbabilityMeasure μ] {T S : X → X}
    (hmp : MeasurePreserving T μ μ) (hS : Measurable S) (hl : Function.LeftInverse S T)
    (P : FinPart X) : hPart μ S P = hPart μ T P := by
  have hfun : (fun N : ℕ => Hfam μ (joinSets S P (N + 1)) / ((N : ℝ) + 1))
      = (fun N : ℕ => Hfam μ (joinSets T P (N + 1)) / ((N : ℝ) + 1)) :=
    funext fun N => by rw [(Hfam_joinSets_inv μ hmp hS hl P N).symm]
  show (⨅ N : ℕ, Hfam μ (joinSets S P (N + 1)) / ((N : ℝ) + 1))
      = (⨅ N : ℕ, Hfam μ (joinSets T P (N + 1)) / ((N : ℝ) + 1))
  rw [hfun]

theorem ent_inverse {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure μ]
    (T S : X → X) (hT : Measurable T) (hS : Measurable S) (hmp : MeasureTheory.MeasurePreserving T μ μ)
    (hl : Function.LeftInverse S T) (hr : Function.RightInverse S T) :
    Work.EKLContract.ent μ S = Work.EKLContract.ent μ T := by
  have hpart : ∀ P : FinPart X, hPart μ S P = hPart μ T P :=
    fun P => hPart_inv μ hmp hS hl P
  show (⨆ P : FinPart X, ENNReal.ofReal (hPart μ S P))
      = (⨆ P : FinPart X, ENNReal.ofReal (hPart μ T P))
  exact iSup_congr fun P => by rw [hpart P]

end Work.EKLComp
