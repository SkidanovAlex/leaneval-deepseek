import Mathlib
import Submission.Commons.Combinatorics.Transference.card_image_join_inter_le

namespace Commons.Combinatorics.Transference

/-- Number of distinct level sets associated to the map
`x ↦ {y | ∀ j < K, ⌊(g j y - α j)/ε⌋ = ⌊(g j x - α j)/ε⌋}` is at most
`(2 * (⌈M/ε⌉ + 2) + 1) ^ K`.  This is the `P = univ` specialization of
`card_image_join_inter_le`, keeping track that the trivial partition has a single
part. -/
theorem card_image_kpart_le {X : Type*} [Fintype X] [DecidableEq X] {K : ℕ}
    (g : ℕ → X → ℝ) (α : ℕ → ℝ) {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M)
    (hg : ∀ j < K, ∀ x : X, |g j x| ≤ M) (hα0 : ∀ j, 0 ≤ α j) (hαε : ∀ j, α j < ε) :
    (Finset.univ.image (fun x => Finset.univ.filter (fun y => ∀ j : ℕ, j < K →
      ⌊(g j y - α j) / ε⌋ = ⌊(g j x - α j) / ε⌋))).card
      ≤ (2 * (⌈M / ε⌉ + 2) + 1).toNat ^ K := by
  classical
  -- Specialize the "join with a partition" lemma to the trivial partition `univ`,
  -- reindexing the `ℕ`-indexed data by `Fin K`.
  have hmain := card_image_join_inter_le (X := X) (K := K)
      (fun _ : X => (Finset.univ : Finset X))
      (fun x => Finset.mem_univ x)
      (fun _ _ _ => rfl)
      (fun j : Fin K => g j.val) hε (fun j : Fin K => α j.val)
      (fun j => hα0 j.val) (fun j => hαε j.val) hM
      (fun j x => hg j.val j.isLt x)
  -- The two image sets coincide.
  have himg : Finset.univ.image (fun x => Finset.univ.filter (fun y => ∀ j : ℕ, j < K →
        ⌊(g j y - α j) / ε⌋ = ⌊(g j x - α j) / ε⌋))
      = Finset.univ.image (fun x => (Finset.univ : Finset X) ∩ Finset.univ.filter
        (fun y => ∀ j : Fin K, ⌊(g j.val y - α j.val) / ε⌋
            = ⌊(g j.val x - α j.val) / ε⌋)) := by
    apply Finset.image_congr
    intro x _
    dsimp only
    rw [Finset.univ_inter]
    apply Finset.filter_congr
    intro y _
    constructor
    · intro h j; exact h j.val j.isLt
    · intro h j hj; exact h ⟨j, hj⟩
  -- The trivial partition has at most one part.
  have hcardP : (Finset.univ.image (fun _ : X => (Finset.univ : Finset X))).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [Finset.mem_image] at ha hb
    obtain ⟨x, _, rfl⟩ := ha
    obtain ⟨y, _, rfl⟩ := hb
    rfl
  rw [himg]
  calc (Finset.univ.image (fun x => (Finset.univ : Finset X) ∩ Finset.univ.filter
          (fun y => ∀ j : Fin K, ⌊(g j.val y - α j.val) / ε⌋
              = ⌊(g j.val x - α j.val) / ε⌋))).card
      ≤ (Finset.univ.image (fun _ : X => (Finset.univ : Finset X))).card
          * (2 * (⌈M / ε⌉ + 2) + 1).toNat ^ K := hmain
    _ ≤ 1 * (2 * (⌈M / ε⌉ + 2) + 1).toNat ^ K :=
          Nat.mul_le_mul_right _ hcardP
    _ = (2 * (⌈M / ε⌉ + 2) + 1).toNat ^ K := by rw [one_mul]

end Commons.Combinatorics.Transference
