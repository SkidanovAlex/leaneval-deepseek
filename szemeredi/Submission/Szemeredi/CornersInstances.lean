import Mathlib
import Submission.Szemeredi.CornersToAP

/-!
# Proven instances of the corners theorem in low dimension

* `cornersFiniteD_one` – dimension one is elementary;
* `cornersFiniteD_two` – dimension two is mathlib's `corners_theorem` (re-derived
  here in the `Fin 2`-coordinate formulation used by `CornersFiniteD`).

As a consequence, through `finiteSzemeredi_of_cornersD` the lengths `k = 2` and
`k = 3` of the finite Szemerédi theorem are re-derived from the corner machinery,
cross-checking the main reduction of `CornersToAP.lean`.  The open core is
dimension `d ≥ 3` (`CornersFiniteD d ε`), which is the multidimensional corners
theorem — equivalent in difficulty to Szemerédi's theorem itself.
-/

open scoped BigOperators
open Finset

namespace Szemeredi

section Fin1

/-- Dimension one: a set of density `ε` in `ZMod M` (`M` large) contains two
distinct points, which form the one-dimensional corner `{x, x + t·e₀}`. -/
theorem cornersFiniteD_one (ε : ℝ) (hε : 0 < ε) : CornersFiniteD 1 ε := by
  classical
  refine ⟨⌈2 / ε⌉₊, ?_⟩
  intro M hM hM₀ B hB
  haveI : NeZero M := ⟨by omega⟩
  have hMposR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hεM : (2 : ℝ) ≤ ε * (M : ℝ) := by
    have hceil : (2 / ε : ℝ) ≤ (⌈2 / ε⌉₊ : ℝ) := by
      exact_mod_cast (Nat.le_ceil (2 / ε : ℝ))
    have hMle : (⌈2 / ε⌉₊ : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM₀
    have hmid : (2 : ℝ) ≤ (⌈2 / ε⌉₊ : ℝ) * ε := by
      calc
        (2 : ℝ) = (2 / ε) * ε := by field_simp [ne_of_gt hε]
        _ ≤ (⌈2 / ε⌉₊ : ℝ) * ε := by exact mul_le_mul_of_nonneg_right hceil (le_of_lt hε)
    calc
      (2 : ℝ) ≤ (⌈2 / ε⌉₊ : ℝ) * ε := hmid
      _ ≤ (M : ℝ) * ε := by exact mul_le_mul_of_nonneg_right hMle (le_of_lt hε)
      _ = ε * (M : ℝ) := by ring
  have hB2 : (2 : ℝ) ≤ (B.card : ℝ) := by
    calc
      (2 : ℝ) ≤ ε * (M : ℝ) := hεM
      _ = ε * (M : ℝ) ^ 1 := by ring
      _ ≤ (B.card : ℝ) := by simpa using hB
  have hB2' : 2 ≤ B.card := by exact_mod_cast hB2
  obtain ⟨u, hu, v, hv, huv⟩ := (Finset.one_lt_card).mp (by omega : 1 < B.card)
  let t : ZMod M := v 0 - u 0
  have ht : t ≠ 0 := by
    intro ht0
    apply huv
    ext i
    fin_cases i
    exact (sub_eq_zero.mp ht0).symm
  refine ⟨u, t, ht, hu, ?_⟩
  intro i
  have hpoint : (fun j : Fin 1 => u j + if j = i then t else 0) = v := by
    ext j
    fin_cases i
    fin_cases j
    change u 0 + (v 0 - u 0) = v 0
    abel
  simpa [hpoint] using hv
end Fin1
section FinTwo

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A vector with two coordinates, as an ordered pair. -/
def pairOfVector (v : Fin 2 → G) : G × G := (v 0, v 1)

/-- An ordered pair, as a vector with two coordinates. -/
def vectorOfPair (p : G × G) : Fin 2 → G := fun i => if i = 0 then p.1 else p.2

lemma pairOfVector_vectorOfPair (p : G × G) : pairOfVector (vectorOfPair p) = p := by
  ext <;> simp [pairOfVector, vectorOfPair]

lemma vectorOfPair_pairOfVector (v : Fin 2 → G) : vectorOfPair (pairOfVector v) = v := by
  ext i
  fin_cases i <;> simp [pairOfVector, vectorOfPair]

lemma pairOfVector_injective : Function.Injective (pairOfVector : (Fin 2 → G) → G × G) :=
  Function.LeftInverse.injective vectorOfPair_pairOfVector

/-- A corner of `B` (my formulation) is a corner of its image (mathlib formulation). -/
lemma isCorner_of_isCornerD {B : Finset (Fin 2 → G)} {x : Fin 2 → G} {t : G}
    (h : IsCornerD (B : Set (Fin 2 → G)) x t) :
    IsCorner ((B.image pairOfVector : Finset (G × G)) : Set (G × G))
      (x 0) (x 1) (x 0 + t) (x 1 + t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (x0, x1) = pairOf x ∈ image
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, by simpa using h.2.1, ?_⟩)
    simp [pairOfVector]
  · -- (x0, x1 + t) = pairOf (x + t·e₁)
    let ax1 := cornerAxis x ⟨1, by omega⟩ t
    have hax1 : ax1 ∈ B := h.2.2 ⟨1, by omega⟩
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ax1, hax1, ?_⟩)
    ext <;> simp [pairOfVector, ax1, cornerAxis]
  · -- (x0 + t, x1) = pairOf (x + t·e₀)
    let ax0 := cornerAxis x ⟨0, by omega⟩ t
    have hax0 : ax0 ∈ B := h.2.2 ⟨0, by omega⟩
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨ax0, hax0, ?_⟩)
    ext <;> simp [pairOfVector, ax0, cornerAxis]
  · abel

/-- A (nontrivial) mathlib corner in the image pulls back to a corner of `B`. -/
lemma exists_cornerD_of_isCorner {B : Finset (Fin 2 → G)} {x₁ y₁ x₂ y₂ : G}
    (hxy : IsCorner ((B.image pairOfVector : Finset (G × G)) : Set (G × G)) x₁ y₁ x₂ y₂)
    (hne : x₁ ≠ x₂) : ∃ x t, IsCornerD (B : Set (Fin 2 → G)) x t := by
  classical
  let x : Fin 2 → G := vectorOfPair (x₁, y₁)
  let t : G := x₂ - x₁
  have ht_ne : t ≠ 0 := by
    intro ht0
    apply hne
    exact (sub_eq_zero.mp (by simpa [t] using ht0)).symm
  -- pull-back lemma: every point of the image is the image of a point of `B`
  have pullback : ∀ p : G × G, p ∈ (B.image pairOfVector : Set (G × G)) → vectorOfPair p ∈ B := by
    intro p hp
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hp) with ⟨b, hb, hpb⟩
    have hvec : vectorOfPair p = b := by
      calc vectorOfPair p = vectorOfPair (pairOfVector b) := by rw [hpb]
        _ = b := vectorOfPair_pairOfVector b
    simpa [hvec]
  have hx2 : x₂ = x₁ + t := by
    simp [t]
  have hy2 : y₂ = y₁ + t := by
    have hadd : x₁ + y₂ = x₂ + y₁ := hxy.add_eq_add
    calc
      y₂ = (x₂ + y₁) - x₁ := by rw [← hadd]; abel
      _ = y₁ + (x₂ - x₁) := by abel
  have hx_mem : x ∈ B := by
    simpa [x] using pullback (x₁, y₁) hxy.fst_fst_mem
  refine ⟨x, t, ht_ne, hx_mem, ?_⟩
  intro i
  fin_cases i
  · -- axis 0: point = vector (x₂, y₁)
    have hpt : (fun j : Fin 2 => x j + if j = 0 then t else 0) = vectorOfPair (x₂, y₁) := by
      ext j
      fin_cases j
      · simp [x, vectorOfPair, hx2]
      · simp [x, vectorOfPair]
    have hb' : vectorOfPair (x₂, y₁) ∈ B := pullback (x₂, y₁) hxy.snd_fst_mem
    simpa [hpt]
  · -- axis 1: point = vector (x₁, y₂)
    have hpt : (fun j : Fin 2 => x j + if j = 1 then t else 0) = vectorOfPair (x₁, y₂) := by
      ext j
      fin_cases j
      · simp [x, vectorOfPair]
      · simp [x, vectorOfPair, hy2]
    have hb' : vectorOfPair (x₁, y₂) ∈ B := pullback (x₁, y₂) hxy.fst_snd_mem
    simpa [hpt]

end FinTwo


section Instances

/-- **Corners theorem, dimension two** (this is mathlib's `corners_theorem`,
rephrased over `Fin 2 → ZMod M` in the formulation used by `CornersFiniteD`). -/
theorem cornersFiniteD_two (ε : ℝ) (hε : 0 < ε) : CornersFiniteD 2 ε := by
  classical
  refine ⟨cornersTheoremBound ε, ?_⟩
  intro M hM hM₀ B hB
  haveI : NeZero M := ⟨by omega⟩
  have hcardM : Fintype.card (ZMod M) = M := ZMod.card M
  let B' : Finset ((ZMod M) × (ZMod M)) := B.image pairOfVector
  have hB'card : B'.card = B.card := by
    dsimp [B']
    exact Finset.card_image_of_injOn (s := B) (f := pairOfVector) (pairOfVector_injective.injOn)
  have hdens : ε * (Fintype.card (ZMod M) : ℝ) ^ 2 ≤ (B'.card : ℝ) := by
    rw [hB'card, hcardM]
    exact hB
  have hG : cornersTheoremBound ε ≤ Fintype.card (ZMod M) := by
    rw [hcardM]
    exact hM₀
  have hnc := corners_theorem (G := ZMod M) ε hε hG B' hdens
  -- hnc : ¬ IsCornerFree (B' : Set (ZMod M × ZMod M))
  rw [show ¬ IsCornerFree (B' : Set (ZMod M × ZMod M)) ↔
      ∃ x₁ y₁ x₂ y₂ : ZMod M, IsCorner (B' : Set (ZMod M × ZMod M)) x₁ y₁ x₂ y₂ ∧ x₁ ≠ x₂ by
        simp [IsCornerFree]] at hnc
  rcases hnc with ⟨x₁, y₁, x₂, y₂, hxy, hne⟩
  exact exists_cornerD_of_isCorner (B := B) hxy hne

/-- Sanity check, length two: the finite Szemerédi theorem for `k = 2` re-derived
through the corner machinery (`CornersFiniteD` in dimension one). -/
theorem finiteSzemeredi_two_via_corners (δ : ℝ) (hδ : 0 < δ) : FiniteSzemeredi 2 δ := by
  exact finiteSzemeredi_of_cornersD (n := 0) hδ (cornersFiniteD_one (δ / 4) (by positivity))

/-- Sanity check, length three: Roth's theorem re-derived through the corner machinery
(`CornersFiniteD` in dimension two, from mathlib's `corners_theorem`). -/
theorem finiteSzemeredi_three_via_corners (δ : ℝ) (hδ : 0 < δ) : FiniteSzemeredi 3 δ := by
  exact finiteSzemeredi_of_cornersD (n := 1) hδ (cornersFiniteD_two (δ / 4) (by positivity))

end Instances

end Szemeredi
