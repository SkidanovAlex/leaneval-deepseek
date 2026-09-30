/-
# The image of an open set of positive height under a cube chart is open
(`Work.RTOwed.chartKlein_image_open`)

The chart of the cube `a : Fin 48` is the Möbius chart

  `chartKlein a q = kleinOfHyp (chartMat a *ᵥ hypOfUHS q)`

(`cuspChart.lean`, where `CuspE4` are the coordinates of the upper half space model and `q 3 > 0`
is the height).  This file proves that it is an *open map* on the region of positive height: for
every open `S` with `0 < q 3` for all `q ∈ S`, the image `chartKlein a '' S` is open.

## How the chart sits in the hyperbolic models

Write `φ = hypOfUHS : {q : 0 < q 3} → upperSheet` and `ψ = kleinOfHyp : upperSheet → ball`, and put

  `χ = ψ ∘ φ : upper half space → Klein ball` (the model change),

so that `chartKlein a = ψ ∘ (chartMat a ·) ∘ φ`.  Two facts make this the *same kind* of map as the
Klein action `mobiusKlein` already treated in `Work.FoldInst.isOpen_mobiusKlein_image`:

* `chartMat a` is a positive multiple of a Lorentz matrix.  Concretely `chartMat a` is already in
  the Lorentz group for `16 ≤ a` (`chartMat_gramZ`) and is twice one for `a < 16`; hence the matrix

    `chartK a = (chartScale a)⁻¹ • chartMat a`,   `chartScale a ∈ {1, 2}`,

  is a Lorentz matrix with positive `(4,4)` entry (`chartK_isLorentz`).  As `kleinOfHyp` is
  homogeneous (`kleinOfHyp_smul`), the chart may be written with `chartK a` in place of `chartMat a`.

* The model change `χ` is a homeomorphism from the open upper half space onto the open ball
  (`isOpen_uhsToKlein_image`, with inverse `kleinToUhs = mobiusKlein 1`), hence it maps the open
  subsets of the upper half space to open subsets of `E4`.

Since `hypOfKlein (χ q) = hypOfUHS q` on the upper sheet and `hypOfUHS (uhsOfHyp P) = P`, the chart
factors as `chartKlein a = χ ∘ mobiusKlein (chartK a) ∘ χ`, and the result follows from the
openness of `mobiusKlein` on the ball (`isOpen_mobiusKlein_image`) applied twice.
-/
import Mathlib
import Submission.Work.RTOwed.cuspChart
import Submission.Work.FoldInst.isOpen_foldTheta_image
import Submission.Work.FoldInst.foldPsi_continuousOn
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.Lorentz
import Submission.Work.HypModel.lorentz_dHypOfUHS
import Submission.Work.HypModel.hypOfUHS_four_pos
import Submission.Work.HypModel.lorentz_hypOfUHS_self
import Submission.Work.HypModel.four_pos_of_lorentz_pair_neg
import Submission.Work.HypModel.hasFDerivAt_hypOfUHS
import Submission.Work.HypModel.hasFDerivAt_uhsOfHyp
import Submission.Work.HypModel.hypOfKlein_mem_upperSheet
import Submission.Work.HypModel.hypOfKlein_injOn
import Submission.Work.HypModel.hypOfKlein_kleinOfHyp
import Submission.Work.HypModel.hypOfKlein_diagonal
import Submission.Work.HypModel.hypOfKlein_segment_pos_combo
import Submission.Work.HypModel.hypOfUHS_injOn
import Submission.Work.HypModel.hypOfUHS_uhsOfHyp
import Submission.Work.HypModel.uhsOfHyp_three_pos
import Submission.Work.HypModel.isLorentzMat_uhsTranslation
import Submission.Work.HypModel.kleinOfHyp_hypOfKlein
import Submission.Work.HypModel.kleinOfHyp_mem_ball
import Submission.Work.HypModel.mobiusKlein_isometry
import Submission.Work.HypModel.mobiusKlein_mem
import Submission.Work.HypModel.mobiusKlein_mul
import Submission.Work.HypModel.mobius_contDiffOn
import Submission.Work.HypModel.uhsOfHyp_hypOfUHS
import Submission.Work.HypModel.mobius_isometry
import Submission.Work.HypModel.mobius_mul
import Submission.Work.HypModel.mobius_one
import Submission.Work.HypModel.mobius_uhsTranslation
import Submission.Work.HypModel.polarToUHS_isometry
import Submission.Work.HypModel.tangent_hypOfUHS

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Matrix
open Set Topology Function

namespace Work.RTOwed

/-! ## The chart matrix is a positive multiple of a Lorentz matrix

`chartMat a` is an integer matrix; the finite computations of this section (all decidable, proved
by `decide`) identify the multiple: `chartMat a` lies in the Lorentz group for `16 ≤ a`, and is
`2 ·` a Lorentz matrix for `a < 16`. -/

/-- The Gram matrix of the Lorentz form, over `ℤ`. -/
def Jz : Matrix (Fin 5) (Fin 5) ℤ := Matrix.diagonal (fun i => if i = 4 then (-1 : ℤ) else 1)

/-- The scaling factor of the chart matrix: `chartMat a = chartScale a · (Lorentz matrix)`. -/
def chartScaleZ : Fin 48 → ℤ := fun a => if (a : ℕ) < 16 then 2 else 1

/-- The scaling factor of the chart matrix, as a real number. -/
def chartScale (a : Fin 48) : ℝ := ((chartScaleZ a : ℤ) : ℝ)

/-- The chart matrix of the cube `a`, with real entries. -/
def chartMatR (a : Fin 48) : Matrix (Fin 5) (Fin 5) ℝ := (chartMat a).map (Int.castRingHom ℝ)

/-- **The normalised chart matrix**: the multiple of `chartMat a` which lies in the Lorentz group. -/
def chartK (a : Fin 48) : Matrix (Fin 5) (Fin 5) ℝ := (chartScale a)⁻¹ • chartMatR a

theorem chartScale_pos (a : Fin 48) : 0 < chartScale a := by
  unfold chartScale chartScaleZ; split <;> norm_num

/-- **The Gram identity of the chart matrix**: `chartMat a` scales the Lorentz form by
`chartScale a²`. -/
theorem chartMat_gramZ (a : Fin 48) :
    (chartMat a)ᵀ * Jz * (chartMat a) = (chartScaleZ a) ^ 2 • Jz := by
  decide +revert

/-- The `(4,4)` entry of the chart matrix is positive (it is `≥ 2`). -/
theorem chartMat_four_four_pos (a : Fin 48) : 0 < chartMat a 4 4 := by
  decide +revert

/-- `Jz` with real entries is the Lorentz Gram matrix `J`. -/
theorem hypModel_J_eq : Work.HypModel.J = Jz.map (Int.castRingHom ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jz, Work.HypModel.J]

/-- Changing the entries of a matrix by a ring hom commutes with the Gram construction. -/
theorem map_gram (M : Matrix (Fin 5) (Fin 5) ℤ) :
    ((M.map (Int.castRingHom ℝ))ᵀ * Work.HypModel.J * (M.map (Int.castRingHom ℝ)))
      = ((Mᵀ * Jz * M).map (Int.castRingHom ℝ)) := by
  rw [hypModel_J_eq, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]

/-- The scalar action of `ℤ` commutes with the entrywise change of ring. -/
theorem map_smul_int (n : ℤ) (A : Matrix (Fin 5) (Fin 5) ℤ) :
    (n • A).map (Int.castRingHom ℝ) = (n : ℝ) • A.map (Int.castRingHom ℝ) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Int.coe_castRingHom, Int.cast_mul]

/-- **The Gram identity of the chart matrix, over `ℝ`.** -/
theorem chartMatR_gram (a : Fin 48) :
    (chartMatR a)ᵀ * Work.HypModel.J * (chartMatR a)
      = (chartScale a) ^ 2 • Work.HypModel.J := by
  rw [chartMatR, map_gram, chartMat_gramZ, map_smul_int, ← hypModel_J_eq]
  congr 1
  rw [chartScale]
  push_cast
  ring

/-- **The normalised chart matrix `chartK a` is a Lorentz matrix** (with `0 < chartK a 4 4`). -/
theorem chartK_isLorentz (a : Fin 48) : Work.HypModel.IsLorentzMat (chartK a) := by
  have hc : chartScale a ≠ 0 := ne_of_gt (chartScale_pos a)
  have hR := chartMatR_gram a
  refine ⟨?_, ?_⟩
  · calc ((chartScale a)⁻¹ • chartMatR a)ᵀ * Work.HypModel.J * ((chartScale a)⁻¹ • chartMatR a)
        = ((chartScale a)⁻¹ • ((chartMatR a)ᵀ * Work.HypModel.J))
            * ((chartScale a)⁻¹ • chartMatR a) := by
          rw [Matrix.transpose_smul, Matrix.smul_mul]
      _ = (chartScale a)⁻¹
            • (((chartMatR a)ᵀ * Work.HypModel.J) * ((chartScale a)⁻¹ • chartMatR a)) := by
          rw [Matrix.smul_mul]
      _ = (chartScale a)⁻¹
            • ((chartScale a)⁻¹ • (((chartMatR a)ᵀ * Work.HypModel.J) * chartMatR a)) := by
          rw [Matrix.mul_smul]
      _ = ((chartScale a)⁻¹ * (chartScale a)⁻¹)
            • ((chartMatR a)ᵀ * Work.HypModel.J * chartMatR a) := by
          rw [smul_smul]
      _ = ((chartScale a)⁻¹ * (chartScale a)⁻¹) • ((chartScale a) ^ 2 • Work.HypModel.J) := by
          rw [hR]
      _ = Work.HypModel.J := by
          rw [smul_smul, show (chartScale a)⁻¹ * (chartScale a)⁻¹ * chartScale a ^ 2 = 1 by
            field_simp, one_smul]
  · rw [chartK, Matrix.smul_apply, smul_eq_mul]
    refine mul_pos (inv_pos.mpr (chartScale_pos a)) ?_
    rw [chartMatR, Matrix.map_apply]
    show (0 : ℝ) < ((chartMat a 4 4 : ℤ) : ℝ)
    exact_mod_cast chartMat_four_four_pos a

/-! ## The chart in terms of the Lorentz matrix `chartK a` -/

theorem proj4_smul (c : ℝ) (P : Work.HypModel.V5) :
    Work.HypModel.proj4 (c • P) = c • Work.HypModel.proj4 P := by
  ext i; fin_cases i <;> simp [Work.HypModel.proj4]

/-- **`kleinOfHyp` is homogeneous of degree `0`.** -/
theorem kleinOfHyp_smul {c : ℝ} (hc : c ≠ 0) (P : Work.HypModel.V5) :
    Work.HypModel.kleinOfHyp (c • P) = Work.HypModel.kleinOfHyp P := by
  rw [Work.HypModel.kleinOfHyp, Work.HypModel.kleinOfHyp, proj4_smul, Pi.smul_apply, smul_smul]
  congr 1
  by_cases h4 : P 4 = 0
  · simp [h4]
  · field_simp
    simp [smul_eq_mul]

/-- `chartMatR a = chartScale a · chartK a`: the chart is the Lorentz matrix `chartK a` up to a
positive scalar, which `kleinOfHyp` does not see. -/
theorem chartMatR_eq_smul_chartK (a : Fin 48) : chartMatR a = chartScale a • chartK a := by
  have hc : chartScale a ≠ 0 := ne_of_gt (chartScale_pos a)
  rw [chartK, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- **The chart of the cube `a` is the Lorentz-matrix chart of `chartK a`.** -/
theorem chartKlein_eq (a : Fin 48) (q : CuspE4) :
    chartKlein a q = Work.HypModel.kleinOfHyp (chartK a *ᵥ Work.HypModel.hypOfUHS q) := by
  have hc : chartScale a ≠ 0 := ne_of_gt (chartScale_pos a)
  show Work.HypModel.kleinOfHyp (chartMatR a *ᵥ Work.HypModel.hypOfUHS q)
      = Work.HypModel.kleinOfHyp (chartK a *ᵥ Work.HypModel.hypOfUHS q)
  rw [chartMatR_eq_smul_chartK, Matrix.smul_mulVec, kleinOfHyp_smul hc]

/-! ## The model change upper half space → Klein ball is an open map

`uhsToKlein q = kleinOfHyp (hypOfUHS q)` carries the upper half space onto the Klein ball, and it is
inverted by `kleinToUhs = mobiusKlein 1`, which is continuous on the ball
(`Work.FoldInst.continuousOn_mobiusKlein`). -/

/-- The model change from the upper half space to the Klein ball. -/
def uhsToKlein : CuspE4 → CuspE4 := fun q => Work.HypModel.kleinOfHyp (Work.HypModel.hypOfUHS q)

/-- The inverse model change, from the Klein ball to the upper half space: the Klein action of the
identity Lorentz matrix. -/
def kleinToUhs : CuspE4 → CuspE4 := Work.HypModel.mobiusKlein 1

/-- `hypOfUHS` maps the upper half space into the upper sheet. -/
theorem hypOfUHS_mem_upperSheet {q : CuspE4} (hq : q ∈ Work.HypModel.upperHalfSpace) :
    Work.HypModel.hypOfUHS q ∈ Work.HypModel.upperSheet :=
  ⟨Work.HypModel.lorentz_hypOfUHS_self (ne_of_gt hq), Work.HypModel.hypOfUHS_four_pos hq⟩

/-- The open unit ball is open in `E4`. -/
theorem isOpen_ball_hyp : IsOpen Work.HypModel.ball := by
  change IsOpen {y : CuspE4 | ‖y‖ < 1}
  exact isOpen_lt continuous_norm continuous_const

theorem kleinToUhs_apply (y : CuspE4) :
    kleinToUhs y = Work.HypModel.uhsOfHyp (Work.HypModel.hypOfKlein y) := by
  simp [kleinToUhs, Work.HypModel.mobiusKlein]

/-- `kleinToUhs` is a left inverse of `uhsToKlein` on the upper half space. -/
theorem kleinToUhs_uhsToKlein {q : CuspE4} (hq : q ∈ Work.HypModel.upperHalfSpace) :
    kleinToUhs (uhsToKlein q) = q := by
  rw [kleinToUhs_apply, uhsToKlein,
    Work.HypModel.hypOfKlein_kleinOfHyp (hypOfUHS_mem_upperSheet hq),
    Work.HypModel.uhsOfHyp_hypOfUHS (ne_of_gt hq)]

/-- `kleinToUhs` is a right inverse of `uhsToKlein` on the ball. -/
theorem uhsToKlein_kleinToUhs {y : CuspE4} (hy : y ∈ Work.HypModel.ball) :
    uhsToKlein (kleinToUhs y) = y := by
  rw [kleinToUhs_apply, uhsToKlein,
    Work.HypModel.hypOfUHS_uhsOfHyp (Work.HypModel.hypOfKlein_mem_upperSheet hy),
    Work.HypModel.kleinOfHyp_hypOfKlein hy]

/-- **The model change takes open subsets of the upper half space to open subsets of `E4`.**

`uhsToKlein '' S = ball ∩ kleinToUhs ⁻¹' S` — the two round trips `kleinToUhs ∘ uhsToKlein = id` on
the upper half space and `uhsToKlein ∘ kleinToUhs = id` on the ball — and `kleinToUhs` is continuous
on the open ball. -/
theorem isOpen_uhsToKlein_image {S : Set CuspE4} (hS : IsOpen S)
    (hSU : S ⊆ Work.HypModel.upperHalfSpace) : IsOpen (uhsToKlein '' S) := by
  have hset : uhsToKlein '' S = Work.HypModel.ball ∩ kleinToUhs ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨Work.HypModel.kleinOfHyp_mem_ball (hypOfUHS_mem_upperSheet (hSU hq)), ?_⟩
      show kleinToUhs (uhsToKlein q) ∈ S
      rw [kleinToUhs_uhsToKlein (hSU hq)]
      exact hq
    · rintro ⟨hyb, hyS⟩
      exact ⟨kleinToUhs y, hyS, uhsToKlein_kleinToUhs hyb⟩
  rw [hset]
  exact (Work.FoldInst.continuousOn_mobiusKlein Work.HypModel.IsLorentzMat_one).isOpen_inter_preimage
    isOpen_ball_hyp hS

/-! ## The chart is the conjugate of a Klein Möbius action -/

/-- **The chart of the cube is `χ ∘ mobiusKlein (chartK a) ∘ χ`.**  For `q` of positive height,
`hypOfKlein (χ q) = hypOfUHS q` (`hypOfKlein_kleinOfHyp`) and `hypOfUHS (uhsOfHyp P) = P` on the
upper sheet, so the two model changes cancel against the Klein lift (`hypOfUHS_uhsOfHyp`). -/
theorem chartK_eq_conj (a : Fin 48) (hK : Work.HypModel.IsLorentzMat (chartK a)) {q : CuspE4}
    (hq : q ∈ Work.HypModel.upperHalfSpace) :
    Work.HypModel.kleinOfHyp (chartK a *ᵥ Work.HypModel.hypOfUHS q)
      = uhsToKlein (Work.HypModel.mobiusKlein (chartK a) (uhsToKlein q)) := by
  have hP : Work.HypModel.hypOfUHS q ∈ Work.HypModel.upperSheet := hypOfUHS_mem_upperSheet hq
  have hQ : chartK a *ᵥ Work.HypModel.hypOfUHS q ∈ Work.HypModel.upperSheet :=
    Work.HypModel.isLorentzMat_mem_upperSheet hK hP
  rw [uhsToKlein, uhsToKlein, Work.HypModel.mobiusKlein, Work.HypModel.hypOfKlein_kleinOfHyp hP,
    Work.HypModel.hypOfUHS_uhsOfHyp hQ]

/-! ## The target -/

/-- **The image of an open set of positive height under a cube chart is open.**  The chart is
`χ ∘ mobiusKlein (chartK a) ∘ χ` (`chartK_eq_conj`, `chartKlein_eq`): both model changes are open
maps on the open upper half space (`isOpen_uhsToKlein_image`, with `χ` mapping onto the open ball)
and the Klein action of the Lorentz matrix `chartK a` is an open map on the ball
(`Work.FoldInst.isOpen_mobiusKlein_image`). -/
theorem chartKlein_image_open (a : Fin 48) {S : Set CuspE4} (hS : IsOpen S)
    (hpos : ∀ q ∈ S, 0 < q 3) : IsOpen (chartKlein a '' S) := by
  have hK : Work.HypModel.IsLorentzMat (chartK a) := chartK_isLorentz a
  have hSU : S ⊆ Work.HypModel.upperHalfSpace := fun q hq => hpos q hq
  rw [show chartKlein a '' S
      = (fun q : CuspE4 => Work.HypModel.kleinOfHyp (chartK a *ᵥ Work.HypModel.hypOfUHS q))
          '' S from by
    exact Set.image_congr (fun q _ => chartKlein_eq a q)]
  have hTopen : IsOpen (uhsToKlein '' S) := isOpen_uhsToKlein_image hS hSU
  have hTball : uhsToKlein '' S ⊆ Work.HypModel.ball := by
    rintro y ⟨q, hq, rfl⟩
    exact Work.HypModel.kleinOfHyp_mem_ball (hypOfUHS_mem_upperSheet (hSU hq))
  have hmid : IsOpen (Work.HypModel.mobiusKlein (chartK a) '' (uhsToKlein '' S)) :=
    Work.FoldInst.isOpen_mobiusKlein_image hK hTopen hTball
  have hmiduhs : Work.HypModel.mobiusKlein (chartK a) '' (uhsToKlein '' S)
      ⊆ Work.HypModel.upperHalfSpace := by
    rintro y ⟨z, hz, rfl⟩
    rw [Work.HypModel.mobiusKlein]
    change 0 < Work.HypModel.uhsOfHyp (chartK a *ᵥ Work.HypModel.hypOfKlein z) 3
    rw [Work.HypModel.uhsOfHyp_apply_three]
    exact inv_pos.mpr (Work.HypModel.upperSheet_four_sub_three_pos
      (Work.HypModel.isLorentzMat_mem_upperSheet hK
        (Work.HypModel.hypOfKlein_mem_upperSheet (hTball hz))))
  rw [show (fun q : CuspE4 => Work.HypModel.kleinOfHyp (chartK a *ᵥ Work.HypModel.hypOfUHS q))
        '' S
      = uhsToKlein '' (Work.HypModel.mobiusKlein (chartK a) '' (uhsToKlein '' S)) from by
    rw [← Set.image_comp, ← Set.image_comp]
    exact Set.image_congr (fun q hq => chartK_eq_conj a hK (hSU hq))]
  exact isOpen_uhsToKlein_image hmid hmiduhs

end Work.RTOwed
