import Mathlib
import Submission.Work.Peluse.ExpA.Defs
import Submission.Work.Peluse.Concat.Defs

/-!
# The box average of the expansion is the pair sum over the corner data

`Work.Peluse.Concat.boxAvg s M₁ c ωOf D N f` is the normalised average over `h, h' ∈ [1,M₁]^s` of
the `(2^s-1)`-fold box-norm power of `f` at the direction family
`fun i → arithIcc (c · (ωOf i · (h - h'))) D` (see `Work.Peluse.Concat.Defs`).

The statement proved here is the change of variables `h ↦ h + 1`: writing the double average over
the corner data `k, k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁}` instead of the zero-based
tuples `Fin s → Fin M₁`, the direction set of the `i`-th slot becomes
`arithIcc (c · dotU (ωOfA s i) (fun j => k j - k' j)) D`.  The two averaging factors
`(M₁⁻¹)^(2s)` and `((M₁^s)^2)⁻¹` agree; the reindexing itself is the bijection
`Fin M₁ ≃ {n : ℕ // n ∈ Finset.Icc 1 M₁}`, `h ↦ h + 1`, applied level-wise.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.ExpA

noncomputable section

/-- The bijection `Fin M ≃ {n : ℕ // n ∈ Finset.Icc 1 M}`, `a ↦ a + 1`. -/
def finIccEquiv (M : ℕ) : Fin M ≃ {n : ℕ // n ∈ Finset.Icc 1 M} where
  toFun a := ⟨a.1 + 1, by rw [Finset.mem_Icc]; omega⟩
  invFun n := ⟨n.1 - 1, by have h := n.2; rw [Finset.mem_Icc] at h; omega⟩
  left_inv a := by ext; simp
  right_inv n := by
    have h := n.2; rw [Finset.mem_Icc] at h
    ext
    simp
    omega

/-- The induced bijection on `s`-tuples: `h ↦ fun i => h i + 1`. -/
def tupEquiv (s M : ℕ) : (Fin s → Fin M) ≃ ((i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M}) :=
  Equiv.piCongrRight (fun _ : Fin s => finIccEquiv M)

lemma tupEquiv_apply {s M : ℕ} (h : Fin s → Fin M) (i : Fin s) :
    ((tupEquiv s M h) i).1 = (h i).1 + 1 := rfl

/-- The change of variables in the direction sets: the difference tuple `tupSub h h'` of the
zero-based tuples `h, h' : Fin s → Fin M₁` is the difference of the corresponding corner data. -/
lemma dotZ_tupSub_eq_dotU {s M₁ : ℕ} (ω : Fin s → Bool) (h h' : Fin s → Fin M₁) :
    Work.Peluse.Concat.dotZ ω (Work.Peluse.Concat.tupSub h h') =
      dotU ω (fun j => (((tupEquiv s M₁ h) j).1 : ℤ) - (((tupEquiv s M₁ h') j).1 : ℤ)) := by
  simp only [Work.Peluse.Concat.dotZ, dotU]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hω : ω j <;>
    simp [hω, Work.Peluse.Concat.tupSub, tupEquiv, finIccEquiv]

theorem boxAvgEqPairSum {s : ℕ} (M₁ : ℕ) (hM₁ : 1 ≤ M₁) (c : ℤ) (D N : ℕ)
    (f : ℤ → ℂ) :
    Work.Peluse.Concat.boxAvg s M₁ c (Work.Peluse.ExpA.ωOfA s) D N f = ((((M₁ : ℝ) ^ s) ^ 2))⁻¹ *
      ∑ k : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
        ∑ k' : (i : Fin s) → {n : ℕ // n ∈ Finset.Icc 1 M₁},
          Work.Peluse.boxNormPow (2 ^ s - 1)
            (fun i : Fin (2 ^ s - 1) => Work.Peluse.arithIcc
              (c * Work.Peluse.ExpA.dotU (Work.Peluse.ExpA.ωOfA s i)
                (fun j => ((k j).1 : ℤ) - ((k' j).1 : ℤ))) D)
            (Work.Peluse.symIcc N) f := by
  have _ := hM₁
  rw [Work.Peluse.Concat.boxAvg]
  have hcoef : ((M₁ : ℝ))⁻¹ ^ (2 * s) = ((((M₁ : ℝ) ^ s) ^ 2))⁻¹ := by
    rw [inv_pow, mul_comm, pow_mul]
  rw [hcoef]
  congr 1
  -- the summands agree under the change of variables `h ↦ h + 1`
  have key : ∀ (h h' : Fin s → Fin M₁),
      Work.Peluse.boxNormPow (2 ^ s - 1)
        (fun i : Fin (2 ^ s - 1) => Work.Peluse.arithIcc
          (c * Work.Peluse.Concat.dotZ (Work.Peluse.ExpA.ωOfA s i)
            (Work.Peluse.Concat.tupSub h h')) D)
        (Work.Peluse.symIcc N) f =
      Work.Peluse.boxNormPow (2 ^ s - 1)
        (fun i : Fin (2 ^ s - 1) => Work.Peluse.arithIcc
          (c * Work.Peluse.ExpA.dotU (Work.Peluse.ExpA.ωOfA s i)
            (fun j => (((tupEquiv s M₁ h) j).1 : ℤ) - (((tupEquiv s M₁ h') j).1 : ℤ))) D)
        (Work.Peluse.symIcc N) f := by
    intro h h'
    exact congrArg (fun Q : Fin (2 ^ s - 1) → Finset ℤ =>
      Work.Peluse.boxNormPow (2 ^ s - 1) Q (Work.Peluse.symIcc N) f) (by
        funext i
        have hz := dotZ_tupSub_eq_dotU (Work.Peluse.ExpA.ωOfA s i) h h'
        exact congrArg (fun z : ℤ => Work.Peluse.arithIcc z D) (by rw [hz]))
  -- both averages are sums over the same index type
  refine Fintype.sum_equiv (M := ℝ) (tupEquiv s M₁) ?_ ?_ ?_
  · intro h
    refine Fintype.sum_equiv (M := ℝ) (tupEquiv s M₁) ?_ ?_ ?_
    · intro h'
      exact key h h'

end

end Work.Peluse.ExpA
