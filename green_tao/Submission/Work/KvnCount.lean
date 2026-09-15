import Submission.Work.KvnPart

set_option linter.unusedSectionVars false

/-!
# Counting the atoms of the join of level-set σ-algebras (Green–Tao §7)

The join `levelJoin d F ε α` of the level-set σ-algebras of the anti-uniform functions
`davg d (F j)` at resolution `ε` has at most `(2⌈M/ε⌉+5)^K` atoms whenever `|davg d (F j)| ≤ M`
and `0 ≤ α j < ε`.  This is the counting step of Green–Tao §7 (it controls the exceptional set
`Ω`: `∑_Ω(ν+1) ≤ η·#atoms`), cf. `Commons.Combinatorics.Transference.bohr_sigma_Omega`.
-/

open Finset
open scoped BigOperators

namespace GTTrans

open Commons.Combinatorics.Transference
open FinSigma

/-- The level index `⌊(g x - α)/ε⌋` lies in `[-(⌈M/ε⌉+2), ⌈M/ε⌉+2]` whenever `|g x| ≤ M`,
`0 ≤ α < ε` and `0 < ε`. -/
lemma floor_levIdx_mem_Icc {X : Type*} (g : X → ℝ) {ε : ℝ} (hε : 0 < ε) {α : ℝ}
    (hα0 : 0 ≤ α) (hαε : α < ε) {M : ℝ} (hM : 0 ≤ M) {x : X} (hx : |g x| ≤ M) :
    ⌊(g x - α) / ε⌋ ∈ Finset.Icc (-(⌈M / ε⌉ + 2)) (⌈M / ε⌉ + 2) := by
  rw [Finset.mem_Icc]
  set c : ℤ := ⌈M / ε⌉ with hc
  have hceil : M / ε ≤ (c : ℝ) := by rw [hc]; exact Int.le_ceil _
  have hceil' : -(c : ℝ) ≤ -(M / ε) := neg_le_neg hceil
  rw [abs_le] at hx
  have hcastL : (((-(c + 2) : ℤ)) : ℝ) = -(c : ℝ) - 2 := by push_cast; ring
  have hcastR : (((c + 2 : ℤ)) : ℝ) = (c : ℝ) + 2 := by push_cast; ring
  constructor
  · rw [Int.le_floor, hcastL]
    have h1 : -(M / ε) - 1 < (g x - α) / ε := by
      have h2 : (-M - ε) / ε = -(M / ε) - 1 := by field_simp
      rw [← h2]
      apply div_lt_div_of_pos_right _ hε
      linarith [hx.1, hαε]
    linarith [hceil', h1]
  · rw [Int.floor_le_iff, hcastR]
    have h1 : (g x - α) / ε ≤ M / ε := by
      apply div_le_div_of_nonneg_right _ hε.le
      linarith [hx.2, hα0]
    linarith [h1, hceil]

/-- The image of `x ↦ ⌊(g x - α)/ε⌋` has at most `2⌈M/ε⌉+5` elements when `|g| ≤ M`,
`0 ≤ α < ε`, `0 < ε`. -/
lemma card_image_floor_le {X : Type*} [Fintype X] [DecidableEq X] (g : X → ℝ) {ε : ℝ}
    (hε : 0 < ε) {α : ℝ} (hα0 : 0 ≤ α) (hαε : α < ε) {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ x, |g x| ≤ M) :
    (Finset.univ.image (fun x => ⌊(g x - α) / ε⌋)).card
      ≤ (2 * (⌈M / ε⌉ + 2) + 1).toNat := by
  classical
  have hsub : Finset.univ.image (fun x => ⌊(g x - α) / ε⌋)
      ⊆ Finset.Icc (-(⌈M / ε⌉ + 2)) (⌈M / ε⌉ + 2) := by
    intro v hv
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hv
    exact floor_levIdx_mem_Icc g hε hα0 hαε hM (hg x)
  calc (Finset.univ.image (fun x => ⌊(g x - α) / ε⌋)).card
      ≤ (Finset.Icc (-(⌈M / ε⌉ + 2)) (⌈M / ε⌉ + 2)).card := Finset.card_le_card hsub
    _ = (2 * (⌈M / ε⌉ + 2) + 1).toNat := by
        rw [Int.card_Icc]
        congr 1
        ring

/-- **Counting the atoms of the join of level sets** (Green–Tao §7).  If `|davg d (F j)| ≤ M`
and `0 ≤ α j < ε` for all `j`, then the join of the level-set σ-algebras has at most
`(2⌈M/ε⌉+5)^K` atoms. -/
lemma card_image_levelJoin_le {p : ℕ} [Fact p.Prime] (d : ℕ) {K : ℕ}
    (F : Fin K → ZMod p → ℝ) {ε : ℝ} (hε : 0 < ε) (α : Fin K → ℝ)
    (hα0 : ∀ j, 0 ≤ α j) (hαε : ∀ j, α j < ε) {M : ℝ} (hM : 0 ≤ M)
    (hF : ∀ (j : Fin K) (x : ZMod p), |davg d (F j) x| ≤ M) :
    ((Finset.univ.image (levelJoin d F ε α)).card : ℝ)
      ≤ (((2 * (⌈M / ε⌉ + 2) + 1 : ℤ)) : ℝ) ^ K := by
  classical
  set B : ℤ := ⌈M / ε⌉ + 2 with hB
  set Φ : ZMod p → (Fin K → ℤ) := fun x j => ⌊(davg d (F j) x - α j) / ε⌋ with hΦ
  set Ψ : (Fin K → ℤ) → Finset (ZMod p) :=
    fun v => Finset.univ.filter (fun y => ∀ j : Fin K,
      ⌊(davg d (F j) y - α j) / ε⌋ = v j) with hΨ
  have hfac : ∀ x, levelJoin d F ε α x = Ψ (Φ x) := by
    intro x; rw [levelJoin, hΨ, hΦ]
  have himg : Finset.univ.image (levelJoin d F ε α) = (Finset.univ.image Φ).image Ψ := by
    rw [Finset.image_image]
    exact Finset.image_congr (fun x _ => hfac x)
  have hcard : (Finset.univ.image Φ).card
      ≤ (Fintype.piFinset (fun _ : Fin K => Finset.Icc (-B) B)).card := by
    apply Finset.card_le_card
    intro v hv
    rw [Fintype.mem_piFinset]
    intro j
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hv
    exact floor_levIdx_mem_Icc (davg d (F j)) hε (hα0 j) (hαε j) hM (hF j x)
  have hcardIcc : (Finset.Icc (-B) B).card = (2 * B + 1).toNat := by
    rw [Int.card_Icc]; congr 1; ring
  have hmain : (Finset.univ.image (levelJoin d F ε α)).card ≤ (2 * B + 1).toNat ^ K := by
    rw [himg]
    refine le_trans (le_trans Finset.card_image_le hcard) ?_
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hcardIcc]
  have hBpos : 0 ≤ 2 * B + 1 := by
    have hc0 : (0 : ℤ) ≤ ⌈M / ε⌉ := Int.ceil_nonneg (div_nonneg hM hε.le)
    rw [hB]; omega
  have hcast1 : (((2 * B + 1).toNat ^ K : ℕ) : ℝ) = (((2 * B + 1 : ℤ)) : ℝ) ^ K := by
    rw [Nat.cast_pow]
    congr 1
    rw [← Int.cast_natCast]
    exact_mod_cast Int.toNat_of_nonneg hBpos
  calc ((Finset.univ.image (levelJoin d F ε α)).card : ℝ)
      ≤ (((2 * B + 1).toNat ^ K : ℕ) : ℝ) := Nat.cast_le.mpr hmain
    _ = (((2 * B + 1 : ℤ)) : ℝ) ^ K := hcast1
    _ = (((2 * (⌈M / ε⌉ + 2) + 1 : ℤ)) : ℝ) ^ K := by rw [hB]

end GTTrans
