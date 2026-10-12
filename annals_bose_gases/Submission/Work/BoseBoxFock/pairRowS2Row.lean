import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.pairG_supports
import Submission.Work.BoseBoxFock.pairRowS2Inst
import Submission.Work.BoseBoxFock.pinQBl_eq_periodisation
import Submission.Work.BoseBoxFock.pinQDl_eq_const
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowS2Row` — step (S2) of the FS `Q₂` row at the **row level**

The kernel form `Work.BoseBoxFock.potPairRows_kernelExpanded` of the `Q₂` row is a sum of five
triple-integral shapes, three of which (`block I`, `block II.1`, `block II.2`) carry the truncated
pair kernel `K1exp`.  Step (S2) of `FINDING_PotPairRows_exists.md` replaces `K1exp` by its limit
`K1lim` in those three blocks; the two `block III` shapes are *not* substituted (their weight is the
constant sequence `fun _ => 1`, whose `χχ`-row is a Dirichlet kernel with no function limit — that
is the (S2b)/(R3) part of the reduction).

This module

* fixes the three per-pair shapes `rowShape13`, `rowShape21`, `rowShape23` and their `pairSet n`
  sums `rowSum13`, `rowSum21`, `rowSum23`, and the block-`I/II` part `rowPairSubC` of the row;
* proves the row-level substitution bound `rowPairSub_Ksub_of_shapes`, which sums the per-pair
  bounds over `p ∈ pairSet n` (the per-pair bounds themselves are supplied by the state-level
  block lemmas `block13_Ksub_state` / `blockTwo3_Ksub_state` / `blockII1_Ksub_state`, applied in
  `pairRowS2RowKsub`);
* records the mirror form `pinQCl_eq_periodisation` of `pinQBl_eq_periodisation` (needed for the
  position form of `K1lim` in step (S3)).

Everything here is `sorry`-free.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-! ## 1. The mirror `χ̂`-row: `pinQCl` from `pinQBl`

`pinQCl ℓ W y = Σ'_n Ŵ(k_n)χ̂(ℓk_n)e^{−i⟪k_n,y⟫}` is `pinQBl ℓ W` at `w = −y`; hence the closed form
of `pinQBl_eq_periodisation` transfers verbatim. -/

theorem pinQCl_eq_periodisation {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℝ}
    (hWm : MeasureTheory.AEStronglyMeasurable W MeasureTheory.volume)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : HasCompactSupport W)
    (hWev : ∀ z, W (-z) = W z) (y : E3) :
    pinQCl ℓ W y
      = ∑' m : Fin 3 → ℤ, ∫ x : E3,
          ((W x : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ
            (ℓ • latVec m - y - x) : ℝ) : ℂ) := by
  have hmain := pinQBl_eq_periodisation (ℓ := ℓ) hℓ (W := W) hWm hWb hWs hWev (-y)
  have h1 : pinQCl ℓ W y = pinQBl ℓ W (-y) := by
    refine tsum_congr (fun n : Fin 3 → ℤ => ?_)
    show ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
        * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))
      = ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ)
        * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) (-y) : ℝ) : ℂ))
    rw [inner_neg_right, Complex.ofReal_neg]
    congr 1
    ring
  rw [h1, hmain]
  refine tsum_congr (fun m : Fin 3 → ℤ => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall (fun x : E3 => ?_))
  show ((W x : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ (-y + ℓ • latVec m - x) : ℝ) : ℂ)
      = ((W x : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ (ℓ • latVec m - y - x) : ℝ) : ℂ)
  rw [show -y + ℓ • latVec m - x = ℓ • latVec m - y - x by abel]

/-! ## 2. The three per-pair shapes and their row sums -/

/-- **Block I / III.1 shape**: the kernel sits at the configuration slot `p.2` and at the free
variable `y` (which is substituted into slot `p.1`); `A` is the slot-`p.1` state factor, `B` the
free factor of the `u`-integral. -/
noncomputable def rowShape13 {n : ℕ} (Θ : Xn n → ℂ) (A B : E3 → ℂ) (K : E3 → E3 → ℂ)
    (p : Fin n × Fin n) : ℂ :=
  ∫ x : Xn n, ∫ y : E3, ∫ u : E3,
    star (Θ x) * A (x p.1) * K (x p.2) y * star (B u)
      * Θ (Function.update (Function.update x p.1 y) p.2 u)

/-- **Block II.1 shape**: both kernel arguments are free variables. -/
noncomputable def rowShape21 {n : ℕ} (Θ : Xn n → ℂ) (A : E3 → ℂ) (K : E3 → E3 → ℂ)
    (p : Fin n × Fin n) : ℂ :=
  ∫ x : Xn n, ∫ y : E3, ∫ u : E3,
    star (Θ x) * A (x p.1) * A (x p.2) * K u y
      * Θ (Function.update (Function.update x p.1 y) p.2 u)

/-- **Block II.2 shape**: the kernel sits at the two configuration slots `p.1`, `p.2`. -/
noncomputable def rowShape23 {n : ℕ} (Θ : Xn n → ℂ) (A B : E3 → ℂ) (K : E3 → E3 → ℂ)
    (p : Fin n × Fin n) : ℂ :=
  ∫ x : Xn n, ∫ y : E3, ∫ u : E3,
    star (Θ x) * K (x p.1) (x p.2) * star (A y) * star (B u)
      * Θ (Function.update (Function.update x p.1 y) p.2 u)

/-- The `pairSet n`-sum of the block-I shape. -/
noncomputable def rowSum13 {n : ℕ} (Θ : Xn n → ℂ) (A B : E3 → ℂ) (K : E3 → E3 → ℂ) : ℂ :=
  ∑ p ∈ Submission.BoseGases.pairSet n, rowShape13 Θ A B K p

/-- **The `χχ`-images kernel** `χ(w)χ(y)·Σ'_{m≠0}W(w−y+ℓ•latVec m)`.

By the PROVED `Work.BoseBoxFock.chiChi_latPer3_eq_wLoc_add` it is (with `W = wScaled ℓ h`) the
difference between the `χχ` term of `K1lim ℓ (wScaled ℓ h)` and its `m = 0` part
`wLoc ℓ h 0 w y = χ(w)·wScaled ℓ h (w−y)·χ(y)`; the PROVED
`Work.BoseBoxFock.chiChiImages_pairing` bounds its box pairing by `C(R/ℓ)^K·CW`.  It is the (S3)
entry point: stripping it off `K1lim` turns the `χχ` term of the pair kernel into the honest
localised kernel `wLoc`. -/
noncomputable def chiChiImages (ℓ : ℝ) (W : E3 → ℂ) (w y : E3) : ℂ :=
  ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
    * (∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℂ) else W (w - y + ℓ • latVec m))


/-- The `pairSet n`-sum of the block-II.1 shape. -/
noncomputable def rowSum21 {n : ℕ} (Θ : Xn n → ℂ) (A : E3 → ℂ) (K : E3 → E3 → ℂ) : ℂ :=
  ∑ p ∈ Submission.BoseGases.pairSet n, rowShape21 Θ A K p

/-- The `pairSet n`-sum of the block-II.2 shape. -/
noncomputable def rowSum23 {n : ℕ} (Θ : Xn n → ℂ) (A B : E3 → ℂ) (K : E3 → E3 → ℂ) : ℂ :=
  ∑ p ∈ Submission.BoseGases.pairSet n, rowShape23 Θ A B K p

/-- **The block-`I/II` part of the `Q₂` row** at the kernels `KI` (block I) and `KII`
(blocks II.1, II.2), at the common state factor `A`, with the row's normalisation scalar `a`
(`a = ℓ⁻³` at the box side `ℓ`) and the `½` of the Bogoliubov block.  Taking `a` as the bare scalar
makes the identification with `potPairRows_kernelExpanded` definitional. -/
noncomputable def rowPairSubC {n : ℕ} (a : ℝ) (Θ : Xn n → ℂ) (A : E3 → ℂ)
    (KI KII : E3 → E3 → ℂ) : ℂ :=
  a • rowSum13 Θ A A KI
    + ((1 / 2 : ℝ) * a) • (rowSum21 Θ A KII + rowSum23 Θ A A KII)

/-- Membership in `pairSet n` is exactly the off-diagonal condition. -/
theorem mem_pairSet_iff {n : ℕ} {p : Fin n × Fin n} :
    p ∈ Submission.BoseGases.pairSet n ↔ p.1 ≠ p.2 := by
  rw [Submission.BoseGases.pairSet]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-! ## 3. The row-level substitution bound

The three blocks are summed separately, each per-pair bound being the corresponding state-level
block lemma; the `pairSet n` cardinality is kept symbolic (it is `n(n−1)`). -/

/-- **Step (S2) of the `Q₂` row at the row level.**  If each of the three shapes has its per-pair
substitution bound at a common constant `ε√C`, then the whole block-`I/II` part of the row moves by
at most `2·ℓ⁻³·#(pairSet n)·ε√C`. -/
theorem rowPairSubC_Ksub_of_shapes {n : ℕ} {a ε C : ℝ} {Θ : Xn n → ℂ} {A : E3 → ℂ}
    {KI KI' KII KII' : E3 → E3 → ℂ}
    (h13 : ∀ p ∈ Submission.BoseGases.pairSet n,
      ‖rowShape13 Θ A A KI p - rowShape13 Θ A A KI' p‖ ≤ ε * Real.sqrt C)
    (h21 : ∀ p ∈ Submission.BoseGases.pairSet n,
      ‖rowShape21 Θ A KII p - rowShape21 Θ A KII' p‖ ≤ ε * Real.sqrt C)
    (h23 : ∀ p ∈ Submission.BoseGases.pairSet n,
      ‖rowShape23 Θ A A KII p - rowShape23 Θ A A KII' p‖ ≤ ε * Real.sqrt C) :
    ‖rowPairSubC a Θ A KI KII - rowPairSubC a Θ A KI' KII'‖
      ≤ 2 * |a| * ((Submission.BoseGases.pairSet n).card : ℝ) * (ε * Real.sqrt C) := by
  classical
  have h13s : ‖rowSum13 Θ A A KI - rowSum13 Θ A A KI'‖
      ≤ ((Submission.BoseGases.pairSet n).card : ℝ) * (ε * Real.sqrt C) := by
    rw [rowSum13, rowSum13, ← Finset.sum_sub_distrib]
    calc ‖∑ p ∈ Submission.BoseGases.pairSet n,
            (rowShape13 Θ A A KI p - rowShape13 Θ A A KI' p)‖
        ≤ ∑ p ∈ Submission.BoseGases.pairSet n,
            ‖rowShape13 Θ A A KI p - rowShape13 Θ A A KI' p‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _p ∈ Submission.BoseGases.pairSet n, (ε * Real.sqrt C) := Finset.sum_le_sum h13
      _ = ((Submission.BoseGases.pairSet n).card : ℝ) * (ε * Real.sqrt C) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h21s : ‖rowSum21 Θ A KII - rowSum21 Θ A KII'‖
      ≤ ((Submission.BoseGases.pairSet n).card : ℝ) * (ε * Real.sqrt C) := by
    rw [rowSum21, rowSum21, ← Finset.sum_sub_distrib]
    calc ‖∑ p ∈ Submission.BoseGases.pairSet n,
            (rowShape21 Θ A KII p - rowShape21 Θ A KII' p)‖
        ≤ ∑ p ∈ Submission.BoseGases.pairSet n,
            ‖rowShape21 Θ A KII p - rowShape21 Θ A KII' p‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _p ∈ Submission.BoseGases.pairSet n, (ε * Real.sqrt C) := Finset.sum_le_sum h21
      _ = ((Submission.BoseGases.pairSet n).card : ℝ) * (ε * Real.sqrt C) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have h23s : ‖rowSum23 Θ A A KII - rowSum23 Θ A A KII'‖
      ≤ ((Submission.BoseGases.pairSet n).card : ℝ) * (ε * Real.sqrt C) := by
    rw [rowSum23, rowSum23, ← Finset.sum_sub_distrib]
    calc ‖∑ p ∈ Submission.BoseGases.pairSet n,
            (rowShape23 Θ A A KII p - rowShape23 Θ A A KII' p)‖
        ≤ ∑ p ∈ Submission.BoseGases.pairSet n,
            ‖rowShape23 Θ A A KII p - rowShape23 Θ A A KII' p‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _p ∈ Submission.BoseGases.pairSet n, (ε * Real.sqrt C) := Finset.sum_le_sum h23
      _ = ((Submission.BoseGases.pairSet n).card : ℝ) * (ε * Real.sqrt C) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hYZ : ‖(rowSum21 Θ A KII - rowSum21 Θ A KII')
      + (rowSum23 Θ A A KII - rowSum23 Θ A A KII')‖
      ≤ 2 * (((Submission.BoseGases.pairSet n).card : ℝ) * (ε * Real.sqrt C)) := by
    have h1 : ‖(rowSum21 Θ A KII - rowSum21 Θ A KII')
        + (rowSum23 Θ A A KII - rowSum23 Θ A A KII')‖
        ≤ ‖rowSum21 Θ A KII - rowSum21 Θ A KII'‖
          + ‖rowSum23 Θ A A KII - rowSum23 Θ A A KII'‖ :=
      norm_add_le _ _
    linarith [h21s, h23s]
  have hdec : rowPairSubC a Θ A KI KII - rowPairSubC a Θ A KI' KII'
      = a • (rowSum13 Θ A A KI - rowSum13 Θ A A KI')
        + ((1 / 2 : ℝ) * a)
            • ((rowSum21 Θ A KII - rowSum21 Θ A KII')
                + (rowSum23 Θ A A KII - rowSum23 Θ A A KII')) := by
    simp only [rowPairSubC, smul_add, smul_sub]
    abel
  rw [hdec]
  have ha : ‖a • (rowSum13 Θ A A KI - rowSum13 Θ A A KI')‖
      = |a| * ‖rowSum13 Θ A A KI - rowSum13 Θ A A KI'‖ := by
    rw [norm_smul, Real.norm_eq_abs]
  have hb : ‖((1 / 2 : ℝ) * a)
      • ((rowSum21 Θ A KII - rowSum21 Θ A KII')
          + (rowSum23 Θ A A KII - rowSum23 Θ A A KII'))‖
      = (1 / 2) * |a| * ‖(rowSum21 Θ A KII - rowSum21 Θ A KII')
          + (rowSum23 Θ A A KII - rowSum23 Θ A A KII')‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  calc ‖a • (rowSum13 Θ A A KI - rowSum13 Θ A A KI')
        + ((1 / 2 : ℝ) * a)
            • ((rowSum21 Θ A KII - rowSum21 Θ A KII')
                + (rowSum23 Θ A A KII - rowSum23 Θ A A KII'))‖
      ≤ ‖a • (rowSum13 Θ A A KI - rowSum13 Θ A A KI')‖
        + ‖((1 / 2 : ℝ) * a)
            • ((rowSum21 Θ A KII - rowSum21 Θ A KII')
                + (rowSum23 Θ A A KII - rowSum23 Θ A A KII'))‖ := norm_add_le _ _
    _ = |a| * ‖rowSum13 Θ A A KI - rowSum13 Θ A A KI'‖
        + (1 / 2) * |a| * ‖(rowSum21 Θ A KII - rowSum21 Θ A KII')
            + (rowSum23 Θ A A KII - rowSum23 Θ A A KII')‖ := by rw [ha, hb]
    _ ≤ |a| * (((Submission.BoseGases.pairSet n).card : ℝ) * (ε * Real.sqrt C))
        + (1 / 2) * |a|
          * (2 * (((Submission.BoseGases.pairSet n).card : ℝ) * (ε * Real.sqrt C))) := by
        refine add_le_add (mul_le_mul_of_nonneg_left h13s (abs_nonneg _)) ?_
        refine mul_le_mul_of_nonneg_left hYZ ?_
        positivity
    _ = 2 * |a| * ((Submission.BoseGases.pairSet n).card : ℝ) * (ε * Real.sqrt C) := by ring

end Work.BoseBoxFock
