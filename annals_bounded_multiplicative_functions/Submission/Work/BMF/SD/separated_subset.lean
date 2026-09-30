import Mathlib
import Submission.Work.BMF.SD.sd3_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- **A separated sub-family of prescribed size.**

If a finite set `A ⊆ ℕ` has at least `m * K` elements, it contains a subset `B` of
exactly `m` elements whose pairwise differences are all at least `K`.

The proof is the residue-class pigeonhole: as `a` runs over `A`, the residues
`a % K` take at most `K` values, so one residue class `j₀` carries a fiber of size
at least `A.card / K ≥ m`.  A fiber of the residue map is automatically
`K`-separated, since two distinct elements of the same residue class differ by a
positive multiple of `K`. -/
theorem separated_subset (A : Finset ℕ) (K m : ℕ) (hK : 0 < K) (hcard : m * K ≤ A.card) :
    ∃ B : Finset ℕ, B ⊆ A ∧ B.card = m ∧ ∀ a ∈ B, ∀ b ∈ B, a < b → K ≤ b - a := by
  classical
  -- The residues `a % K` partition `A` into the fibers `A.filter (· % K = j)`, `j < K`.
  have hfiber_sum : A.card = ∑ j ∈ Finset.range K, (A.filter (fun a => a % K = j)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro a _
    exact Finset.mem_range.mpr (Nat.mod_lt a hK)
  -- A fiber of maximal size.
  have hne : (Finset.range K).Nonempty := ⟨0, Finset.mem_range.mpr hK⟩
  obtain ⟨j₀, _, hj₀max⟩ :=
    Finset.exists_max_image (Finset.range K) (fun j => (A.filter (fun a => a % K = j)).card) hne
  -- The maximal fiber carries at least `A.card / K ≥ m` elements.
  have hsum_le : A.card ≤ K * (A.filter (fun a => a % K = j₀)).card := by
    rw [hfiber_sum]
    calc ∑ j ∈ Finset.range K, (A.filter (fun a => a % K = j)).card
        ≤ ∑ _j ∈ Finset.range K, (A.filter (fun a => a % K = j₀)).card :=
          Finset.sum_le_sum (fun j hj => hj₀max j hj)
      _ = K * (A.filter (fun a => a % K = j₀)).card := by
          simp [Finset.sum_const, Finset.card_range]
  have hmle : m ≤ (A.filter (fun a => a % K = j₀)).card := by
    have hmul : m * K ≤ (A.filter (fun a => a % K = j₀)).card * K := by
      calc m * K ≤ A.card := hcard
        _ ≤ K * (A.filter (fun a => a % K = j₀)).card := hsum_le
        _ = (A.filter (fun a => a % K = j₀)).card * K := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_right hmul hK
  -- Choose `m` of those elements.
  obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hmle
  refine ⟨B, ?_, hBcard, ?_⟩
  · exact hBsub.trans (Finset.filter_subset _ A)
  · intro a ha b hb hab
    have haF := Finset.mem_filter.mp (hBsub ha)
    have hbF := Finset.mem_filter.mp (hBsub hb)
    -- Same residue class: `K ∣ b - a`, and `b - a > 0`, hence `K ≤ b - a`.
    have hmodEq : a ≡ b [MOD K] := by show a % K = b % K; rw [haF.2, hbF.2]
    have hdvd : K ∣ b - a := (Nat.modEq_iff_dvd' (le_of_lt hab)).mp hmodEq
    exact Nat.le_of_dvd (Nat.sub_pos_of_lt hab) hdvd

end Work.BMF.SD
