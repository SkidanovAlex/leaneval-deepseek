import Mathlib
import Submission.Work.Peluse.SwapC.weightSplit

/-!
# The cube sum splits along the two halves

`mCubeSum (2 * s)` over a direction map that is built out of two halves `βL`, `βR` and a corner
family `F` that only depends on the two halves of the sign pattern, factorises into the four-fold
sum over the two halves of the shift tuple, with the products over the `2s` sign patterns replaced
by the double products over the two half sign patterns.

The proof is a reindexing: split `Fin (2 * s) → X` along the equivalence
`splitEquiv : ((Fin s → X) × (Fin s → X)) ≃ (Fin (2 * s) → X)` (`sum_split_double`), and evaluate
the product over the sign patterns of the `2s` cube pointwise (`tsum_cube_split`), using that both
`weight` and `cornerShift` split along the two halves (`weightSplit`, `corner_shift_split`).
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

noncomputable section

open Work.Peluse

/-! ## 1. Splitting the index type `Fin (2 * s)` -/

/-- The forward map of `splitEquiv`: a pair of half-families read as a `2s`-family, the first `s`
coordinates from the first factor and the last `s` coordinates from the second. -/
def splitFun (s : ℕ) (X : Type) (p : (Fin s → X) × (Fin s → X)) : Fin (2 * s) → X :=
  fun j => if h : j.val < s then p.1 ⟨j.val, h⟩ else p.2 ⟨j.val - s, by omega⟩

/-- The inverse map of `splitEquiv`: the two halves of a `2s`-family. -/
def unsplitFun (s : ℕ) (X : Type) (h : Fin (2 * s) → X) : (Fin s → X) × (Fin s → X) :=
  (fun j => h ⟨j.val, by omega⟩, fun j => h ⟨s + j.val, by omega⟩)

/-- `(Fin s → X) × (Fin s → X)` is `Fin (2 * s) → X`: concatenate the two half-families. -/
def splitEquiv (s : ℕ) (X : Type) : ((Fin s → X) × (Fin s → X)) ≃ (Fin (2 * s) → X) where
  toFun := splitFun s X
  invFun := unsplitFun s X
  left_inv := by
    intro p
    refine Prod.ext ?_ ?_ <;> funext j <;> dsimp only [unsplitFun, splitFun]
    · rw [dif_pos j.isLt]
    · rw [dif_neg (show ¬ ((s + (j:ℕ)) < s) by omega)]
      rw [show (⟨s + (j:ℕ) - s, by omega⟩ : Fin s) = j from Fin.ext (by simp only [Fin.val_mk]; omega)]
  right_inv := by
    intro h
    funext j
    dsimp only [unsplitFun, splitFun]
    by_cases hj : (j : ℕ) < s
    · rw [dif_pos hj]
    · rw [dif_neg hj]
      rw [show (⟨s + ((j:ℕ) - s), by omega⟩ : Fin (2 * s)) = j from Fin.ext (by simp only [Fin.val_mk]; omega)]

/-- The two halves of `splitEquiv s X p`. -/
lemma splitEquiv_apply_left (s : ℕ) (X : Type) (p : (Fin s → X) × (Fin s → X)) (j : Fin s) :
    splitEquiv s X p ⟨j.val, by omega⟩ = p.1 j := by
  simp only [splitEquiv, Equiv.coe_fn_mk, splitFun]
  rw [dif_pos j.isLt]

/-- The two halves of `splitEquiv s X p` (second half). -/
lemma splitEquiv_apply_right (s : ℕ) (X : Type) (p : (Fin s → X) × (Fin s → X)) (j : Fin s) :
    splitEquiv s X p ⟨s + j.val, by omega⟩ = p.2 j := by
  simp only [splitEquiv, Equiv.coe_fn_mk, splitFun]
  rw [dif_neg (show ¬ (s + (j:ℕ) < s) by omega)]
  rw [show (⟨s + (j:ℕ) - s, by omega⟩ : Fin s) = j from Fin.ext (by simp only [Fin.val_mk]; omega)]

/-- `(splitEquiv s X).symm` is `unsplitFun`. -/
lemma splitEquiv_symm_apply (s : ℕ) (X : Type) (h : Fin (2 * s) → X) :
    (splitEquiv s X).symm h
      = (fun j => h ⟨j.val, by omega⟩, fun j => h ⟨s + j.val, by omega⟩) := rfl

/-- On sign patterns, `splitEquiv` inverts the two halves. -/
lemma splitEquiv_cL_cR (s : ℕ) (ω : Fin (2 * s) → Bool) :
    splitEquiv s Bool (cL s ω, cR s ω) = ω :=
  (splitEquiv s Bool).apply_symm_apply ω

/-- The first half of a concatenated sign pattern. -/
lemma cL_splitEquiv (s : ℕ) (p : (Fin s → Bool) × (Fin s → Bool)) :
    cL s (splitEquiv s Bool p) = p.1 := by
  funext j
  exact splitEquiv_apply_left s Bool p j

/-- The second half of a concatenated sign pattern. -/
lemma cR_splitEquiv (s : ℕ) (p : (Fin s → Bool) × (Fin s → Bool)) :
    cR s (splitEquiv s Bool p) = p.2 := by
  funext j
  exact splitEquiv_apply_right s Bool p j

/-- A direction map built out of the two halves, evaluated at a concatenated index. -/
lemma splitEquiv_dir_apply (s : ℕ) (X : Type) (βL βR : Fin s → X → ℤ)
    (p : (Fin s → X) × (Fin s → X)) (j : Fin (2 * s)) :
    (if h : j.val < s then βL ⟨j.val, h⟩ else βR ⟨j.val - s, by omega⟩) (splitEquiv s X p j)
      = (if h : j.val < s then (fun i => βL i (p.1 i)) ⟨j.val, h⟩
          else (fun i => βR i (p.2 i)) ⟨j.val - s, by omega⟩) := by
  simp only [splitEquiv, Equiv.coe_fn_mk, splitFun]
  by_cases hj : (j : ℕ) < s
  · rw [dif_pos hj, dif_pos hj, dif_pos hj]
  · rw [dif_neg hj, dif_neg hj, dif_neg hj]

/-! ## 1bis. Splitting a sum over `Fin (2 * s)` and `cornerShift` -/

/-- A sum over `Fin (2 * s)` splits into the sums over the first `s` and the last `s` indices. -/
lemma sum_fin_two_mul_split {M : Type*} [AddCommMonoid M] (s : ℕ) (g : Fin (2 * s) → M) :
    (∑ j : Fin (2 * s), g j)
      = (∑ i : Fin s, g ⟨i.val, by omega⟩) + (∑ i : Fin s, g ⟨s + i.val, by omega⟩) := by
  have h : s + s = 2 * s := by ring
  rw [← Equiv.sum_comp (finCongr h) g]
  rw [Fin.sum_univ_add]
  congr 1

/-- `cornerShift` splits along the two halves of a `2s`-family built out of two `s`-families. -/
lemma corner_shift_split (s : ℕ) (aL aL' aR aR' : Fin s → ℤ) (ω : Fin (2 * s) → Bool) :
    cornerShift
        (fun j : Fin (2 * s) => if h : j.val < s then aL ⟨j.val, h⟩ else aR ⟨j.val - s, by omega⟩)
        (fun j : Fin (2 * s) => if h : j.val < s then aL' ⟨j.val, h⟩ else aR' ⟨j.val - s, by omega⟩)
        ω
      = cornerShift aL aL' (cL s ω) + cornerShift aR aR' (cR s ω) := by
  simp only [cornerShift, cL, cR]
  rw [sum_fin_two_mul_split]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [dif_pos i.isLt, Fin.eta]
    rfl
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp only [dif_neg (show ¬ (s + i.val < s) by omega)]
    congr 1
    · congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega
    · congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega

/-! ## 2. The four-fold reindexing of the outer sums -/

/-- The outer `∑_h ∑_{h'}` of a `2s`-fold cube sum, reindexed along `splitEquiv` to the four-fold
sum over the two halves of `h` and of `h'`. -/
lemma sum_split_double (s : ℕ) (X : Type) [Fintype X] {M : Type*} [AddCommMonoid M]
    (G : (Fin (2*s) → X) → (Fin (2*s) → X) → M) :
    (∑ h : Fin (2*s) → X, ∑ h' : Fin (2*s) → X, G h h')
      = ∑ k₀ : Fin s → X, ∑ k₀' : Fin s → X, ∑ k₁ : Fin s → X, ∑ k₁' : Fin s → X,
          G (splitEquiv s X (k₀, k₁)) (splitEquiv s X (k₀', k₁')) := by
  have h1 : (∑ h : Fin (2*s) → X, ∑ h' : Fin (2*s) → X, G h h')
      = ∑ p : (Fin (2*s) → X) × (Fin (2*s) → X), G p.1 p.2 :=
    (Fintype.sum_prod_type (fun p : (Fin (2*s) → X) × (Fin (2*s) → X) => G p.1 p.2)).symm
  have h2 : (∑ p : (Fin (2*s) → X) × (Fin (2*s) → X), G p.1 p.2)
      = ∑ q : ((Fin s → X) × (Fin s → X)) × ((Fin s → X) × (Fin s → X)),
          G (splitEquiv s X q.1) (splitEquiv s X q.2) := by
    refine Fintype.sum_equiv ((splitEquiv s X).symm.prodCongr (splitEquiv s X).symm)
      (fun p => G p.1 p.2) (fun q => G (splitEquiv s X q.1) (splitEquiv s X q.2)) ?_
    intro p
    simp only [Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, Equiv.apply_symm_apply]
  have h3 : (∑ q : ((Fin s → X) × (Fin s → X)) × ((Fin s → X) × (Fin s → X)),
          G (splitEquiv s X q.1) (splitEquiv s X q.2))
      = ∑ k₀ : Fin s → X, ∑ k₁ : Fin s → X, ∑ k₀' : Fin s → X, ∑ k₁' : Fin s → X,
          G (splitEquiv s X (k₀, k₁)) (splitEquiv s X (k₀', k₁')) := by
    simp only [Fintype.sum_prod_type]
  have h4 : (∑ k₀ : Fin s → X, ∑ k₁ : Fin s → X, ∑ k₀' : Fin s → X, ∑ k₁' : Fin s → X,
          G (splitEquiv s X (k₀, k₁)) (splitEquiv s X (k₀', k₁')))
      = ∑ k₀ : Fin s → X, ∑ k₀' : Fin s → X, ∑ k₁ : Fin s → X, ∑ k₁' : Fin s → X,
          G (splitEquiv s X (k₀, k₁)) (splitEquiv s X (k₀', k₁')) := by
    refine Finset.sum_congr rfl (fun k₀ _ => ?_)
    exact Finset.sum_comm
  rw [h1, h2, h3, h4]

/-! ## 3. The pointwise splitting of the cube product -/

/-- The `2s`-fold product of the cube term splits into the double product over the two halves.
This is the pointwise core of `mCubeSum_split`. -/
lemma tsum_cube_split (s : ℕ) (X : Type) (βL βR : Fin s → X → ℤ)
    (F : (Fin s → Bool) → (Fin s → Bool) → ℤ → ℂ)
    (p p' : (Fin s → X) × (Fin s → X)) :
    (∑' x : ℤ, ∏ ω : Fin (2 * s) → Bool, (star^[weight ω])
        (F (cL s ω) (cR s ω) (x + cornerShift
          (fun j : Fin (2 * s) =>
            (if h : j.val < s then βL ⟨j.val, h⟩ else βR ⟨j.val - s, by omega⟩) (splitEquiv s X p j))
          (fun j : Fin (2 * s) =>
            (if h : j.val < s then βL ⟨j.val, h⟩ else βR ⟨j.val - s, by omega⟩) (splitEquiv s X p' j))
          ω)))
      = (∑' y : ℤ, ∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool, (star^[weight ε + weight ε'])
          (F ε ε' (y + cornerShift (fun j => βL j (p.1 j)) (fun j => βL j (p'.1 j)) ε
                     + cornerShift (fun j => βR j (p.2 j)) (fun j => βR j (p'.2 j)) ε'))) := by
  refine tsum_congr fun x => ?_
  have hcorner : ∀ ω : Fin (2 * s) → Bool, cornerShift
          (fun j : Fin (2 * s) =>
            (if h : j.val < s then βL ⟨j.val, h⟩ else βR ⟨j.val - s, by omega⟩) (splitEquiv s X p j))
          (fun j : Fin (2 * s) =>
            (if h : j.val < s then βL ⟨j.val, h⟩ else βR ⟨j.val - s, by omega⟩) (splitEquiv s X p' j))
          ω
        = cornerShift (fun j => βL j (p.1 j)) (fun j => βL j (p'.1 j)) (cL s ω)
          + cornerShift (fun j => βR j (p.2 j)) (fun j => βR j (p'.2 j)) (cR s ω) := by
    intro ω
    rw [show (fun j : Fin (2 * s) =>
            (if h : j.val < s then βL ⟨j.val, h⟩ else βR ⟨j.val - s, by omega⟩) (splitEquiv s X p j))
        = (fun j : Fin (2 * s) => if h : j.val < s then (fun i => βL i (p.1 i)) ⟨j.val, h⟩
            else (fun i => βR i (p.2 i)) ⟨j.val - s, by omega⟩) from
        funext fun j => splitEquiv_dir_apply s X βL βR p j]
    rw [show (fun j : Fin (2 * s) =>
            (if h : j.val < s then βL ⟨j.val, h⟩ else βR ⟨j.val - s, by omega⟩) (splitEquiv s X p' j))
        = (fun j : Fin (2 * s) => if h : j.val < s then (fun i => βL i (p'.1 i)) ⟨j.val, h⟩
            else (fun i => βR i (p'.2 i)) ⟨j.val - s, by omega⟩) from
        funext fun j => splitEquiv_dir_apply s X βL βR p' j]
    rw [corner_shift_split s (fun i => βL i (p.1 i)) (fun i => βL i (p'.1 i))
          (fun i => βR i (p.2 i)) (fun i => βR i (p'.2 i)) ω]
  trans (∏ q : (Fin s → Bool) × (Fin s → Bool),
      (star^[weight q.1 + weight q.2])
        (F q.1 q.2 (x + cornerShift (fun j => βL j (p.1 j)) (fun j => βL j (p'.1 j)) q.1
                  + cornerShift (fun j => βR j (p.2 j)) (fun j => βR j (p'.2 j)) q.2)))
  · refine Fintype.prod_equiv (splitEquiv s Bool).symm _ _ ?_
    intro ω
    rw [weightSplit s ω, hcorner ω, add_assoc]
    rfl
  · exact Fintype.prod_prod_type _

/-! ## 4. The target -/

/-- **The cube sum splits along the two halves.** -/
theorem mCubeSum_split (s : ℕ) (X : Type) [Fintype X] (βL βR : Fin s → X → ℤ)
    (S : Finset ℤ) (F : (Fin s → Bool) → (Fin s → Bool) → ℤ → ℂ) :
    Work.Peluse.SwapC.mCubeSum (2 * s) X
        (fun j => if h : j.val < s then βL ⟨j.val, h⟩ else βR ⟨j.val - s, by omega⟩)
        S (fun ω => F (cL s ω) (cR s ω))
      = ((S.card : ℂ))⁻¹ * (((Fintype.card X : ℂ))⁻¹) ^ (2 * (2 * s)) *
        ∑ k₀ : Fin s → X, ∑ k₀' : Fin s → X, ∑ k₁ : Fin s → X, ∑ k₁' : Fin s → X,
          ∑' y : ℤ, ∏ ε : Fin s → Bool, ∏ ε' : Fin s → Bool,
            (star^[weight ε + weight ε'])
              (F ε ε' (y + cornerShift (fun j => βL j (k₀ j)) (fun j => βL j (k₀' j)) ε
                            + cornerShift (fun j => βR j (k₁ j)) (fun j => βR j (k₁' j)) ε')) := by
  simp only [mCubeSum]
  congr 1
  rw [sum_split_double (s := s) (X := X)]
  simp only [tsum_cube_split]

end

end Work.Peluse.SwapC
