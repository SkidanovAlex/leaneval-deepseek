import Mathlib
import Submission.Work.Drive.planeChain

namespace Work.Drive

open scoped Manifold ContDiff
open Manifold

noncomputable section

/-- `foldFun` is even. -/
lemma foldFun_neg (x : ℝ) : foldFun (-x) = foldFun x := by
  simp [foldFun, Real.cos_neg]

/-- `foldFun` has period `2`. -/
lemma foldFun_add_two (x : ℝ) : foldFun (x + 2) = foldFun x := by
  have h : Real.cos (Real.pi * (x + 2)) = Real.cos (Real.pi * x) := by
    have : Real.pi * (x + 2) = Real.pi * x + 2 * Real.pi := by ring
    rw [this, Real.cos_add_two_pi]
  simp only [foldFun, h]

/-- `foldFun` has period `2 * m` for every integer `m`. -/
lemma foldFun_add_two_mul (x : ℝ) (m : ℤ) : foldFun (x + 2 * (m : ℝ)) = foldFun x := by
  induction m using Int.induction_on with
  | zero => simp
  | succ n ih =>
      have h : x + 2 * (((n : ℤ) + 1 : ℤ) : ℝ) = (x + 2 * (n : ℝ)) + 2 := by push_cast; ring
      rw [h, foldFun_add_two]
      simpa using ih
  | pred n ih =>
      have h : x + 2 * (((-(n : ℤ) - 1 : ℤ)) : ℝ) = (x + 2 * (-(n : ℝ))) - 2 := by push_cast; ring
      rw [h]
      have h2 : foldFun ((x + 2 * (-(n : ℝ))) - 2) = foldFun (x + 2 * (-(n : ℝ))) := by
        have hh := foldFun_add_two ((x + 2 * (-(n : ℝ))) - 2)
        rw [show (x + 2 * (-(n : ℝ))) - 2 + 2 = x + 2 * (-(n : ℝ)) by ring] at hh
        exact hh.symm
      rw [h2]
      simpa using ih

/-- **The affine representative of a real number inside `[0,1]`**: a translation by an even integer
and an optional reflection. -/
lemma exists_foldRep (x : ℝ) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ m : ℤ, ε * x + 2 * (m : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  set m₀ : ℤ := ⌊x / 2⌋ with hm₀
  have hm : (m₀ : ℝ) ≤ x / 2 ∧ x / 2 < (m₀ : ℝ) + 1 :=
    ⟨Int.floor_le (x / 2), Int.lt_floor_add_one (x / 2)⟩
  set u : ℝ := x - 2 * (m₀ : ℝ) with hu_def
  have hu : 0 ≤ u ∧ u < 2 := by
    constructor <;> [skip; skip] <;> · rw [hu_def]; linarith [hm.1, hm.2]
  by_cases h : u ≤ 1
  · refine ⟨1, Or.inl rfl, -m₀, ?_⟩
    have hcoe : (1 : ℝ) * x + 2 * ((-m₀ : ℤ) : ℝ) = u := by
      push_cast [hu_def]; ring
    rw [hcoe]
    exact ⟨hu.1, h⟩
  · push Not at h
    refine ⟨-1, Or.inr rfl, m₀ + 1, ?_⟩
    have hcoe : (-1 : ℝ) * x + 2 * (((m₀ + 1 : ℤ)) : ℝ) = 2 - u := by
      push_cast [hu_def]; ring
    rw [hcoe]
    exact ⟨by linarith, by linarith⟩

/-- The representative really preserves `foldFun`. -/
lemma foldFun_foldRep {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (x : ℝ) (m : ℤ) :
    foldFun (ε * x + 2 * (m : ℝ)) = foldFun x := by
  rcases hε with rfl | rfl
  · rw [one_mul]
    exact foldFun_add_two_mul x m
  · rw [neg_one_mul]
    rw [foldFun_add_two_mul (-x) m, foldFun_neg]

/-- The reordered form of `exists_foldRep`, convenient for `choose`. -/
lemma exists_foldRep' (x : ℝ) :
    ∃ (ε : ℝ) (m : ℤ), (ε = 1 ∨ ε = -1) ∧ ε * x + 2 * (m : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨ε, hε, m, hm⟩ := exists_foldRep x
  exact ⟨ε, m, hε, hm⟩

/-- **Transfer of the charted class regularity along an affine symmetry of the plane parameter.**  If
`G ∘ φ = G`, `φ` is affine at `y` with bijective linear part `D` and `G` is differentiable at `φ y`,
then `fderiv ℝ G` has the same range, and the same injectivity, at `y` and at `φ y`. -/
theorem fderiv_transfer_of_comp_eq {G : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    {φ : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    {D : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)}
    {y : EuclideanSpace ℝ (Fin 2)}
    (hcomp : ∀ x, G (φ x) = G x) (hφ : HasFDerivAt φ D y)
    (hD : Function.Injective D) (hD' : Function.Surjective D)
    (hG : DifferentiableAt ℝ G (φ y)) :
    (Function.Injective (fderiv ℝ G (φ y)) ↔ Function.Injective (fderiv ℝ G y)) ∧
      (fderiv ℝ G y).range = (fderiv ℝ G (φ y)).range := by
  have hG' : HasFDerivAt G (fderiv ℝ G (φ y)) (φ y) := hG.hasFDerivAt
  have hchain : HasFDerivAt (fun x => G (φ x)) ((fderiv ℝ G (φ y)).comp D) y :=
    hG'.comp (f := φ) (x := y) hφ
  have hfun : (fun x => G (φ x)) = G := funext hcomp
  have hkey : fderiv ℝ G y = (fderiv ℝ G (φ y)).comp D := by
    have h1 : fderiv ℝ (fun x => G (φ x)) y = (fderiv ℝ G (φ y)).comp D := hchain.fderiv
    rw [hfun] at h1
    exact h1
  have hrange : ((fderiv ℝ G (φ y)).comp D).range = (fderiv ℝ G (φ y)).range := by
    refine le_antisymm ?_ ?_
    · rintro w ⟨v, rfl⟩
      exact ⟨D v, rfl⟩
    · rintro w ⟨v, rfl⟩
      obtain ⟨u, rfl⟩ := hD' v
      exact ⟨u, rfl⟩
  constructor
  · rw [hkey]
    constructor
    · intro h a b hab
      exact hD (h (by simpa [ContinuousLinearMap.comp_apply] using hab))
    · intro h a b hab
      obtain ⟨u, rfl⟩ := hD' a
      obtain ⟨v, rfl⟩ := hD' b
      have huv : (fderiv ℝ G (φ y) ∘SL D) u = (fderiv ℝ G (φ y) ∘SL D) v := by
        simpa [ContinuousLinearMap.comp_apply] using hab
      rw [h huv]
  · rw [hkey, hrange]


end

end Work.Drive
