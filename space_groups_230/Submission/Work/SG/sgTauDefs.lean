import Mathlib
import Submission.Work.SG.SGprelude
import Submission.Work.SG.SGinfra
import Submission.Work.SG.imatOfList_inj

/-!
# Definitions and bookkeeping for `sgTau_eq_data`

`sgClose` (`Submission.Work.SG.Defs`) computes the table of a space-group representative over
`List ℚ` translations (`Int.fract`-reduced); the kernel cannot evaluate `ℚ` arithmetic, so the
computation side of this development is the integer mirror `zClose` of `SGprelude` (same
iteration, `zMul d` in place of `sgMulPair`), interpreted through `toPair d`.

This file collects, in the namespace `Work.SG.Tau` (to stay clear of the shared names), the
elementary list bookkeeping about `zClose`, and the two word-fold definitions `wfold`
(`ℚ`-side, right multiplication by the selected generators) and `wprodL` (its flat matrix
shadow, left-nested) used to exhibit entries of the table `sgTable k`.
-/

namespace Work.SG
namespace Tau

/-- The flat identity matrix. -/
def one9 : List ℤ := [1, 0, 0, 0, 1, 0, 0, 0, 1]

/-- Right fold of a word of generator indices through the affine multiplication. -/
def wfold (gens : List (List ℤ × List ℚ)) (w : List ℕ) : List ℤ × List ℚ :=
  w.foldl (fun a i => sgMulPair a (gens.getD i sgOne)) sgOne

/-- Fold of a word of generator indices through the flat matrix multiplication. -/
def wflatM (gs : List (List ℤ)) (w : List ℕ) : List ℤ :=
  w.foldl (fun a j => m9mul a (gs.getD j one9)) one9

/-- The first component of `wfold` is the flat matrix fold. -/
theorem wfold_fst (gens : List (List ℤ × List ℚ)) (w : List ℕ) :
    (wfold gens w).1 = w.foldl (fun a j => m9mul a (gens.getD j sgOne).1) one9 := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w a ih =>
      simp only [wfold] at ih ⊢
      rw [List.foldl_concat, List.foldl_concat]
      show m9mul (List.foldl (fun a i => sgMulPair a (gens.getD i sgOne)) sgOne w).1
            (gens.getD a sgOne).1
          = m9mul (List.foldl (fun a j => m9mul a (gens.getD j sgOne).1) one9 w)
            (gens.getD a sgOne).1
      rw [ih]

/-- The flat identity matrix is a unit for `m9mul` on the left. -/
theorem m9mul_one9_left {A : List ℤ} (hA : A.length = 9) : m9mul one9 A = A := by
  have hone : imatOfList (one9 : List ℤ) = (1 : IMat) := imatOfList_one
  refine imatOfList_inj (by rw [length_m9mul]) hA ?_
  rw [imatOfList_mul, hone, one_mul]

theorem zClose_zero (gens : List (List ℤ × List ℤ)) (d : ℕ)
    (acc : List (List ℤ × List ℤ)) : zClose gens d 0 acc = acc := rfl

theorem zClose_succ (gens : List (List ℤ × List ℤ)) (d : ℕ) (k : ℕ)
    (acc : List (List ℤ × List ℤ)) :
    zClose gens d (k + 1) acc = zClose gens d k (zF gens d acc) := rfl

theorem mem_zF {gens acc : List (List ℤ × List ℤ)} {d : ℕ} {p : List ℤ × List ℤ} :
    p ∈ zF gens d acc ↔ p ∈ acc ∨ ∃ a ∈ acc, ∃ g ∈ gens, zMul d a g = p := by
  simp only [zF, List.mem_dedup, List.mem_append, List.mem_flatMap, List.mem_map]

/-- The accumulator is contained in every closure built on it. -/
theorem zClose_subset_self (gens : List (List ℤ × List ℤ)) (d : ℕ) :
    ∀ (k : ℕ) (acc : List (List ℤ × List ℤ)), ∀ p ∈ acc, p ∈ zClose gens d k acc := by
  intro k
  induction k with
  | zero => intro acc p hp; rw [zClose_zero]; exact hp
  | succ k ih =>
      intro acc p hp
      rw [zClose_succ]
      exact ih _ p (List.mem_dedup.mpr (List.mem_append_left _ hp))

/-- `zClose` is monotone in the starting list. -/
theorem zClose_mono_acc (gens : List (List ℤ × List ℤ)) (d : ℕ) :
    ∀ (k : ℕ) {acc acc' : List (List ℤ × List ℤ)}, (∀ p ∈ acc, p ∈ acc') →
      ∀ p ∈ zClose gens d k acc, p ∈ zClose gens d k acc' := by
  intro k
  induction k with
  | zero =>
      intro acc acc' h p hp
      rw [zClose_zero] at hp ⊢
      exact h p hp
  | succ k ih =>
      intro acc acc' h p hp
      rw [zClose_succ] at hp ⊢
      refine ih ?_ p hp
      intro q hq
      rw [mem_zF] at hq ⊢
      rcases hq with hq | ⟨a, ha, g, hg, hq⟩
      · exact Or.inl (h q hq)
      · exact Or.inr ⟨a, h a ha, g, hg, hq⟩

/-- One more step only enlarges the closure. -/
theorem zClose_le_succ (gens : List (List ℤ × List ℤ)) (d : ℕ) (k : ℕ)
    (acc : List (List ℤ × List ℤ)) {p : List ℤ × List ℤ}
    (hp : p ∈ zClose gens d k acc) : p ∈ zClose gens d (k + 1) acc := by
  rw [zClose_succ]
  refine zClose_mono_acc gens d k ?_ p hp
  intro q hq
  exact List.mem_dedup.mpr (List.mem_append_left _ hq)

/-- Monotonicity of `zClose` in the number of steps. -/
theorem zClose_le (gens : List (List ℤ × List ℤ)) (d : ℕ) :
    ∀ {k k' : ℕ}, k ≤ k' → ∀ (acc : List (List ℤ × List ℤ)) {p : List ℤ × List ℤ},
      p ∈ zClose gens d k acc → p ∈ zClose gens d k' acc := by
  intro k k' h
  induction h with
  | refl => intro acc p hp; exact hp
  | step _ ih => intro acc p hp; exact zClose_le_succ gens d _ acc (ih acc hp)

/-- Induction principle for `zClose` relative to a set closed under right multiplication by
the generators. -/
theorem zClose_subset_of_closed (gens : List (List ℤ × List ℤ)) (d : ℕ)
    {S : Set (List ℤ × List ℤ)}
    (hcl : ∀ a, a ∈ S → ∀ g, g ∈ gens → zMul d a g ∈ S) :
    ∀ (k : ℕ) (acc : List (List ℤ × List ℤ)), (∀ x ∈ acc, x ∈ S) →
      ∀ p ∈ zClose gens d k acc, p ∈ S := by
  intro k
  induction k with
  | zero => intro acc h p hp; rw [zClose_zero] at hp; exact h p hp
  | succ k ih =>
      intro acc h p hp
      rw [zClose_succ] at hp
      refine ih _ ?_ p hp
      intro q hq
      rw [mem_zF] at hq
      rcases hq with hq | ⟨a, ha, g, hg, hq⟩
      · exact h q hq
      · exact hq ▸ hcl a (h a ha) g hg

end Tau
end Work.SG
