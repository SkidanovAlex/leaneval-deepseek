/-
# The image of an open subset of the Klein ball under a fold chart is open

The chart map of the fold class `i : Fin 98` and the sign index `r` is

  `foldTheta i r = coordPerm i ∘ mobiusKlein (N_F · D_r)`

(`FoldPiece.lean`).  This file proves the *openness* of its image: for every open `S ⊆ E4`
contained in the Klein ball, `foldTheta i r '' S` is open.  Together with the continuity of
`foldTheta` on the ball this is exactly the statement that the fold chart is a homeomorphism onto
an *open* subset of the chart model.

The two factors are treated separately.

* `coordPerm i` reindexes the model coordinates by the bijective permutation `foldTau i`.  Its
  inverse `coordPermInv i` is the reindexing by `foldTau i` itself, so `coordPerm i` is a
  continuous bijection of `E4` with continuous inverse; consequently `coordPerm i '' T` is open
  whenever `T` is.

* For a Lorentz matrix `M` preserving the upper sheet, the Klein action `mobiusKlein M` maps the
  open unit ball *onto* the upper half space (`mobiusKlein_image_ball`).  The inverse map is

    `g q = kleinOfHyp (M⁻¹ · hypOfUHS q)`,

  continuous on the open set `upperHalfSpace = {q : 0 < q 3}` (the Möbius factor `hypOfUHS` is
  smooth there and `kleinOfHyp` is smooth wherever `P 4 ≠ 0`).  Hence for `S` open inside the ball,
  `mobiusKlein M '' S = upperHalfSpace ∩ g ⁻¹' S` is open.
-/
import Mathlib
import Submission.Work.FoldInst.Voronoi
import Submission.Work.FoldInst.foldTheta_injOn

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Matrix

namespace Work.FoldInst

open Work.HypModel

/-! ### The inverse of a Lorentz matrix

`IsLorentzMat A` is `Aᵀ J A = J` together with `0 < A 4 4`; from `Aᵀ J A = J` alone the inverse of
`A` is `J · Aᵀ · J`, and `(det A)² = 1` upgrades this to the two-sided inverse.  These are public
copies of the private facts used in `mobiusKlein_image_ball`. -/

private theorem lorentzJ_transpose' : Jᵀ = J := by
  have : J = Matrix.diagonal (fun i : Fin 5 => if i = 4 then (-1 : ℝ) else 1) := rfl
  rw [this]
  ext i j
  rw [Matrix.transpose_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

private theorem lorentzJ_mul_self' : J * J = 1 := by
  have h1 : J = Matrix.diagonal (fun i : Fin 5 => if i = 4 then (-1 : ℝ) else 1) := rfl
  rw [h1, Matrix.diagonal_mul_diagonal]
  have h : (fun i : Fin 5 =>
      (if i = 4 then (-1 : ℝ) else 1) * (if i = 4 then (-1 : ℝ) else 1)) = fun _ => 1 := by
    funext i; by_cases h4 : i = 4 <;> simp [h4]
  rw [h, Matrix.diagonal_one]

private theorem det_lorentzJ' : J.det = (-1 : ℝ) := by
  have h1 : J = Matrix.diagonal (fun i : Fin 5 => if i = 4 then (-1 : ℝ) else 1) := rfl
  rw [h1, Matrix.det_diagonal, Fin.prod_univ_five]
  norm_num [Fin.isValue]

private theorem isLorentzMat_det_sq' {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) :
    A.det ^ 2 = 1 := by
  have h := congrArg Matrix.det hA.1
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_lorentzJ'] at h
  rw [pow_two]
  linarith

private theorem isLorentzMat_inv_eq' {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) :
    A⁻¹ = J * Aᵀ * J := by
  apply Matrix.inv_eq_left_inv
  calc J * Aᵀ * J * A = J * (Aᵀ * J * A) := by noncomm_ring
    _ = J * J := by rw [hA.1]
    _ = 1 := lorentzJ_mul_self'

private theorem isLorentzMat_mul_inv' {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) :
    A * A⁻¹ = 1 := by
  have h := isLorentzMat_det_sq' hA
  rw [pow_two] at h
  exact Matrix.mul_nonsing_inv A (IsUnit.of_mul_eq_one A.det h)

private theorem isLorentzMat_inv_mul' {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) :
    A⁻¹ * A = 1 := by
  rw [isLorentzMat_inv_eq' hA]
  calc J * Aᵀ * J * A = J * (Aᵀ * J * A) := by noncomm_ring
    _ = J * J := by rw [hA.1]
    _ = 1 := lorentzJ_mul_self'

/-- **The inverse of a Lorentz matrix is a Lorentz matrix.** -/
theorem isLorentzMat_inv {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A) :
    IsLorentzMat A⁻¹ := by
  have hC : A * A⁻¹ = 1 := isLorentzMat_mul_inv' hA
  have hCt : (A⁻¹)ᵀ * Aᵀ = 1 := by
    have h : (A * A⁻¹)ᵀ = (1 : Matrix (Fin 5) (Fin 5) ℝ)ᵀ := by rw [hC]
    rwa [Matrix.transpose_mul, Matrix.transpose_one] at h
  refine ⟨?_, ?_⟩
  · calc (A⁻¹)ᵀ * J * A⁻¹ = (A⁻¹)ᵀ * (Aᵀ * J * A) * A⁻¹ := by rw [hA.1]
      _ = ((A⁻¹)ᵀ * Aᵀ) * J * (A * A⁻¹) := by noncomm_ring
      _ = J := by rw [hCt, hC]; simp
  · have h44 : (A⁻¹) 4 4 = A 4 4 := by
      rw [isLorentzMat_inv_eq' hA]
      rw [show J = Matrix.diagonal (fun i : Fin 5 => if i = 4 then (-1 : ℝ) else 1) from rfl]
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply]
    rw [h44]; exact hA.2

/-! ### Continuity of `kleinOfHyp` off the hyperplane `P 4 = 0` -/

/-- **`kleinOfHyp` is smooth wherever `P 4 ≠ 0`.**  Each coordinate is `(P 4)⁻¹ · P i`. -/
theorem contDiffOn_kleinOfHyp : ContDiffOn ℝ ⊤ kleinOfHyp {P : V5 | P 4 ≠ 0} := by
  have hsub : ContDiffOn ℝ ⊤ (fun P : V5 => P 4) {P : V5 | P 4 ≠ 0} :=
    (ContinuousLinearMap.proj (4 : Fin 5) : V5 →L[ℝ] ℝ).contDiff.contDiffOn
  have h1 : ContDiffOn ℝ ⊤ (fun P : V5 => (P 4)⁻¹) {P : V5 | P 4 ≠ 0} :=
    hsub.inv (fun P hP => hP)
  rw [contDiffOn_piLp (p := 2) (E := fun _ : Fin 4 => ℝ)]
  intro i
  fin_cases i
  · change ContDiffOn ℝ ⊤ (fun P : V5 => (P 4)⁻¹ * P 0) {P : V5 | P 4 ≠ 0}
    exact h1.mul ((ContinuousLinearMap.proj (0 : Fin 5) : V5 →L[ℝ] ℝ).contDiff.contDiffOn)
  · change ContDiffOn ℝ ⊤ (fun P : V5 => (P 4)⁻¹ * P 1) {P : V5 | P 4 ≠ 0}
    exact h1.mul ((ContinuousLinearMap.proj (1 : Fin 5) : V5 →L[ℝ] ℝ).contDiff.contDiffOn)
  · change ContDiffOn ℝ ⊤ (fun P : V5 => (P 4)⁻¹ * P 2) {P : V5 | P 4 ≠ 0}
    exact h1.mul ((ContinuousLinearMap.proj (2 : Fin 5) : V5 →L[ℝ] ℝ).contDiff.contDiffOn)
  · change ContDiffOn ℝ ⊤ (fun P : V5 => (P 4)⁻¹ * P 3) {P : V5 | P 4 ≠ 0}
    exact h1.mul ((ContinuousLinearMap.proj (3 : Fin 5) : V5 →L[ℝ] ℝ).contDiff.contDiffOn)

/-- The upper half space `{q : 0 < q 3}` is open. -/
theorem isOpen_upperHalfSpace : IsOpen upperHalfSpace := by
  rw [upperHalfSpace]
  exact isOpen_lt continuous_const (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 3)

/-! ### The Klein action of a Lorentz matrix takes open subsets of the ball to open sets -/

/-- **The Klein action of a Lorentz matrix maps the open unit ball onto the upper half space by an
open embedding.**  For `S` open and contained in the ball, `mobiusKlein M '' S` is open.

The inverse of `mobiusKlein M` is `g q = kleinOfHyp (M⁻¹ · hypOfUHS q)`, continuous on the open
upper half space; hence `mobiusKlein M '' S = upperHalfSpace ∩ g ⁻¹' S` is open. -/
theorem isOpen_mobiusKlein_image {M : Matrix (Fin 5) (Fin 5) ℝ} (hM : IsLorentzMat M)
    {S : Set E4} (hS : IsOpen S) (hsub : S ⊆ ball) :
    IsOpen (mobiusKlein M '' S) := by
  have hMinv : IsLorentzMat M⁻¹ := isLorentzMat_inv hM
  have hmul1 : M * M⁻¹ = 1 := isLorentzMat_mul_inv' hM
  have hmul2 : M⁻¹ * M = 1 := isLorentzMat_inv_mul' hM
  have hB : Continuous (fun P : V5 => M⁻¹ *ᵥ P) := (contDiff_mulVec M⁻¹).continuous
  have hcont : ContinuousOn (fun q : E4 => kleinOfHyp (M⁻¹ *ᵥ hypOfUHS q)) upperHalfSpace := by
    have hA : ContinuousOn hypOfUHS upperHalfSpace := contDiffOn_hypOfUHS.continuousOn
    have hC : ContinuousOn kleinOfHyp {P : V5 | P 4 ≠ 0} := contDiffOn_kleinOfHyp.continuousOn
    have hmap : Set.MapsTo (fun q : E4 => M⁻¹ *ᵥ hypOfUHS q) upperHalfSpace
        {P : V5 | P 4 ≠ 0} := by
      intro q hq
      have hP : hypOfUHS q ∈ upperSheet :=
        ⟨lorentz_hypOfUHS_self (ne_of_gt hq), hypOfUHS_four_pos hq⟩
      exact ne_of_gt (isLorentzMat_mem_upperSheet hMinv hP).2
    exact hC.comp (hB.comp_continuousOn hA) hmap
  have hset : mobiusKlein M '' S
      = upperHalfSpace ∩ (fun q : E4 => kleinOfHyp (M⁻¹ *ᵥ hypOfUHS q)) ⁻¹' S := by
    ext q
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨mobiusKlein_mem hM (hsub hy), ?_⟩
      have hyb : y ∈ ball := hsub hy
      have h1 : hypOfUHS (mobiusKlein M y) = M *ᵥ hypOfKlein y := by
        rw [mobiusKlein]
        exact hypOfUHS_uhsOfHyp (isLorentzMat_mem_upperSheet hM (hypOfKlein_mem_upperSheet hyb))
      show kleinOfHyp (M⁻¹ *ᵥ hypOfUHS (mobiusKlein M y)) ∈ S
      rw [h1, Matrix.mulVec_mulVec, hmul2, Matrix.one_mulVec, kleinOfHyp_hypOfKlein hyb]
      exact hy
    · rintro ⟨hq, hqS⟩
      have hP : hypOfUHS q ∈ upperSheet :=
        ⟨lorentz_hypOfUHS_self (ne_of_gt hq), hypOfUHS_four_pos hq⟩
      have hQ : M⁻¹ *ᵥ hypOfUHS q ∈ upperSheet := isLorentzMat_mem_upperSheet hMinv hP
      refine ⟨kleinOfHyp (M⁻¹ *ᵥ hypOfUHS q), hqS, ?_⟩
      rw [mobiusKlein, hypOfKlein_kleinOfHyp hQ, Matrix.mulVec_mulVec, hmul1, Matrix.one_mulVec,
        uhsOfHyp_hypOfUHS (ne_of_gt hq)]
  rw [hset]
  exact hcont.isOpen_inter_preimage isOpen_upperHalfSpace hS

/-! ### The coordinate permutation is an open map

`coordPerm i y = fun j => y (foldTau i)⁻¹ j` reindexes the coordinates of `E4` by the bijection
`foldTau i`.  Reindexing by the inverse permutation `coordPermInv i y = fun j => y (foldTau i j)`
gives the two-sided inverse, and a reindexing is continuous. -/

/-- The inverse reindexing of `coordPerm i`: the coordinates of `y` permuted by `foldTau i`. -/
def coordPermInv (i : Fin 98) (y : E4) : E4 :=
  WithLp.toLp 2 (fun j : Fin 4 => y.ofLp (foldTau i j))

theorem coordPermInv_apply (i : Fin 98) (y : E4) (j : Fin 4) :
    coordPermInv i y j = y.ofLp (foldTau i j) := rfl

theorem coordPermInv_ofLp (i : Fin 98) (y : E4) (j : Fin 4) :
    (coordPermInv i y).ofLp j = y.ofLp (foldTau i j) := rfl

/-- `coordPerm i` is a left inverse of `coordPermInv i`. -/
theorem coordPerm_comp_coordPermInv (i : Fin 98) (y : E4) :
    coordPerm i (coordPermInv i y) = y := by
  ext j
  rw [coordPerm_apply, coordPermInv_ofLp,
    Function.rightInverse_invFun (foldTau_bijective i).2 j]

/-- `coordPerm i` is a right inverse of `coordPermInv i`. -/
theorem coordPermInv_comp_coordPerm (i : Fin 98) (y : E4) :
    coordPermInv i (coordPerm i y) = y := by
  ext j
  rw [coordPermInv_apply, coordPerm_apply,
    Function.leftInverse_invFun (foldTau_bijective i).1 j]

/-- A reindexing of the coordinates is continuous. -/
theorem continuous_coordPermInv (i : Fin 98) : Continuous (coordPermInv i) := by
  have h1 : Continuous (fun y : E4 => (fun j : Fin 4 => y.ofLp (foldTau i j))) :=
    continuous_pi (fun j => PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) (foldTau i j))
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)).comp h1

/-- Since `coordPerm i` is inverted by the reindexing `coordPermInv i`, its image is the preimage
of the inverse. -/
theorem image_coordPerm_eq_preimage (i : Fin 98) (T : Set E4) :
    coordPerm i '' T = coordPermInv i ⁻¹' T := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    show coordPermInv i (coordPerm i x) ∈ T
    rw [coordPermInv_comp_coordPerm]
    exact hx
  · intro hq
    exact ⟨coordPermInv i q, hq, coordPerm_comp_coordPermInv i q⟩

/-- **The coordinate permutation is an open map.** -/
theorem isOpenMap_coordPerm (i : Fin 98) : IsOpenMap (coordPerm i) := by
  intro T hT
  rw [image_coordPerm_eq_preimage]
  exact hT.preimage (continuous_coordPermInv i)

/-- The image form of `isOpenMap_coordPerm`. -/
theorem isOpen_coordPerm_image (i : Fin 98) {T : Set E4} (hT : IsOpen T) :
    IsOpen (coordPerm i '' T) :=
  isOpenMap_coordPerm i T hT

/-! ### The target -/

/-- **The image of an open subset of the Klein ball under a fold chart is open.**  The chart map is
`coordPerm i ∘ mobiusKlein (N_F · D_r)`; the second factor is the Klein action of the Lorentz matrix
`N_F · D_r` (`foldInst_foldNr_mul_foldDrR_isLorentz`) and is an open map on the ball
(`isOpen_mobiusKlein_image`), and the first factor is the coordinate permutation, also an open map
(`isOpenMap_coordPerm`). -/
theorem isOpen_foldTheta_image (i : Fin 98) (r : Fin (foldCodim i) → Bool) {S : Set E4}
    (hS : IsOpen S) (hsub : S ⊆ HypModel.ball) : IsOpen (foldTheta i r '' S) := by
  have hM : HypModel.IsLorentzMat (foldNr i * foldDrR i r) :=
    foldInst_foldNr_mul_foldDrR_isLorentz i r
  have h1 : IsOpen (HypModel.mobiusKlein (foldNr i * foldDrR i r) '' S) :=
    isOpen_mobiusKlein_image hM hS hsub
  rw [show foldTheta i r
        = coordPerm i ∘ HypModel.mobiusKlein (foldNr i * foldDrR i r) from rfl, Set.image_comp]
  exact isOpen_coordPerm_image i h1

end Work.FoldInst
