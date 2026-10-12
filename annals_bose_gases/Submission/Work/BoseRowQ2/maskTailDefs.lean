import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowQ2.corpusBox_hatChi_sq_tsum_le
import Submission.Work.BoseRowQ2.rowGchiMaskRow_honest
import Submission.Work.BoseRowsFS.omega_lattice_honest_decay
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.maskTailDefs` — the lattice vocabulary of the *sharp* mask row

The sharp mask row of FS l.3253 needs one analytic input: the *Schwartz tail* of the corpus
`χ̂`.  In the `Lab N`-indexed form used below this is the pair of facts

* `Mc = ChatᵀChat + Tail`  (the lattice Parseval over `ℤ³`, cut at the cube `cube N`), and
* `ChatᵀChat ⪯ sup χ²`,

for the matrices `Chat k i = χ̂(vec (K k − K i))`, `Mc i j = χ̂²(vec (K i − K j))`
(`K = labVec`).

This module is the *interface*: the corpus kernels `chiHat`/`chiHatSq`, the constant `chiTailC`
of the `χ̂²`-tail bound, and the re-exported lattice bookkeeping of
`Work.BoseRowsFS.omega_lattice_honest_decay` (`boxN`, `mem_boxN_iff`, `labVec_mk`,
`labVec_injective'`, `card_boxN`).
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseRowQ2

open Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-! ## 1. The corpus kernels -/

/-- The corpus `χ̂` (`= ∫χ(x)cos⟪p,x⟫`). -/
noncomputable def chiHat (p : E3) : ℝ := Work.BoseK15.corpusBox.hatChi p

/-- The corpus `χ̂²` (`= ∫χ²(x)cos⟪p,x⟫`). -/
noncomputable def chiHatSq (p : E3) : ℝ := Work.BoseK15.corpusBox.hatChiSq p

@[simp] theorem chiHatSq_zero : chiHatSq 0 = 1 :=
  Work.BoseB4.BoxData.hatChiSq_zero Work.BoseK15.corpusBox

theorem chiHat_abs_le_one (p : E3) : |chiHat p| ≤ 1 :=
  Work.BoseK15.hatChi_le_one.1 p

theorem chiHatSq_abs_le_one (p : E3) : |chiHatSq p| ≤ 1 :=
  Work.BoseK15.hatChi_le_one.2 p

/-- `χ̂²` is even (the transform of an even function). -/
theorem chiHatSq_neg (p : E3) : chiHatSq (-p) = chiHatSq p := by
  simp only [chiHatSq, Work.BoseB4.BoxData.hatChiSq, inner_neg_left, Real.cos_neg]

/-- `χ̂` is even. -/
theorem chiHat_neg (p : E3) : chiHat (-p) = chiHat p := by
  simp only [chiHat, Work.BoseB4.BoxData.hatChi, inner_neg_left, Real.cos_neg]

/-- **The constant of the `χ̂²`-tail bound.**  `∑'_{‖vec n‖ ≥ R} χ̂(vec n)² ≤ chiTailC/R^101`. -/
noncomputable def chiTailC : ℝ := Classical.choose corpusBox_hatChi_sq_tsum_le

theorem chiTailC_nonneg : 0 ≤ chiTailC :=
  (Classical.choose_spec corpusBox_hatChi_sq_tsum_le).1

theorem chiTailC_le (R : ℝ) (hR : 1 ≤ R) :
    (∑' n : {n : Fin 3 → ℤ // R ≤ ‖Work.BoseB4.vec n‖}, chiHat (Work.BoseB4.vec n.val) ^ 2)
      ≤ chiTailC / R ^ 101 :=
  (Classical.choose_spec corpusBox_hatChi_sq_tsum_le).2 R hR

/-! ## 2. The lattice cube, and the re-exported bookkeeping -/

/-- The box `[-N,N]³ ∩ ℤ³` of lattice indices. -/
noncomputable def cube (N : ℕ) : Finset (Fin 3 → ℤ) := Work.BoseRowsFS.boxN N

theorem mem_cube {N : ℕ} {m : Fin 3 → ℤ} :
    m ∈ cube N ↔ ∀ i, -(N : ℤ) ≤ m i ∧ m i ≤ (N : ℤ) :=
  Work.BoseRowsFS.mem_boxN_iff

theorem labVec_mem_cube (N : ℕ) (n : Lab N) : labVec N n ∈ cube N :=
  Work.BoseRowsFS.labVec_mem_boxN N n

theorem labVec_surj (N : ℕ) {m : Fin 3 → ℤ} (hm : ∀ i, -(N : ℤ) ≤ m i ∧ m i ≤ (N : ℤ)) :
    labVec N (fun i => (m i : ZMod (2 * N + 1))) = m :=
  Work.BoseRowsFS.labVec_mk N hm

theorem labVec_inj' (N : ℕ) : Function.Injective (labVec N) :=
  Work.BoseRowsFS.labVec_injective' N

theorem card_cube (N : ℕ) : (cube N).card = (2 * N + 1) ^ 3 :=
  Work.BoseRowsFS.card_boxN N

theorem card_lab (N : ℕ) : Fintype.card (Lab N) = (2 * N + 1) ^ 3 := by
  simp [Lab, ZMod.card]

/-- **The image of `labVec N` is the cube.** -/
theorem image_labVec_eq_cube (N : ℕ) :
    (Finset.univ.image (labVec N)) = cube N := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro m hm
    obtain ⟨n, -, rfl⟩ := Finset.mem_image.mp hm
    exact labVec_mem_cube N n
  · rw [Finset.card_image_of_injective _ (labVec_inj' N), Finset.card_univ, card_lab,
      card_cube]

/-! ## 3. The `sup χ²` constant

`χ_base` is a `Classical.choice` bump, so the only provable bound is
`π/48 ≤ chiNormSq`, hence `sup χ² ≤ 48/π` (see
`Work.BoseRowQ2.RowGchiMaskSharpAux.chi_sq_le_48_div_pi`); it is re-proved here so that this
module can be imported by the row itself. -/

/-- `sup χ² ≤ 48/π`. -/
theorem chi_sq_le_48_div_pi' (x : E3) : (Submission.BoseGases.chi x) ^ 2 ≤ 48 / Real.pi := by
  have hbase_le : Submission.BoseGases.chiBase x ≤ 1 := Submission.BoseGases.chiBase_le_one x
  have hbase_nn : 0 ≤ Submission.BoseGases.chiBase x := Submission.BoseGases.chiBase_nonneg x
  have hnorm : Real.pi / 48 ≤ Submission.BoseGases.chiNormSq :=
    Work.SmallBoxOneBody.chiNormSq_ge_pi_div_48
  have hpos : 0 < Submission.BoseGases.chiNormSq := Submission.BoseGases.chiNormSq_pos
  rw [Submission.BoseGases.chi, div_pow, Real.sq_sqrt hpos.le, div_le_iff₀ hpos]
  have h1 : (Submission.BoseGases.chiBase x) ^ 2 ≤ 1 := by nlinarith
  have h2 : (48 / Real.pi) * (Real.pi / 48) = 1 := by field_simp
  calc (Submission.BoseGases.chiBase x) ^ 2 ≤ 1 := h1
    _ = (48 / Real.pi) * (Real.pi / 48) := h2.symm
    _ ≤ (48 / Real.pi) * Submission.BoseGases.chiNormSq :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)

/-! ## 4. The two lattice matrices of the mask row -/

/-- `Chat k i = χ̂(vec (K k − K i))`: the Gram entry `⟨g i, f k⟩` (FS's `χ̂`). -/
noncomputable def Chat (N : ℕ) (k i : Lab N) : ℝ :=
  chiHat (Work.BoseB4.vec (labVec N k - labVec N i))

/-- `Mc i j = χ̂²(vec (K i − K j))`: the kernel of `Σ_j Q_{L,j}χ²Q_{L,j}` (FS's `χ̂²`). -/
noncomputable def Mc (N : ℕ) (i j : Lab N) : ℝ :=
  chiHatSq (Work.BoseB4.vec (labVec N i - labVec N j))

/-- **The Schwartz tail matrix**: `Tail = Mc − ChatᵀChat`, whose entries are the lattice-tail
sums `Σ_{l ∉ cube} χ̂(vec (l − K i)) χ̂(vec (l − K j))` (`Work.BoseRowQ2.tail_eq_tsum`). -/
noncomputable def Tail (N : ℕ) (i j : Lab N) : ℝ :=
  Mc N i j - ∑ k : Lab N, Chat N k i * Chat N k j

theorem Mc_symm (N : ℕ) (i j : Lab N) : Mc N i j = Mc N j i := by
  have h : Work.BoseB4.vec (labVec N i - labVec N j)
      = -Work.BoseB4.vec (labVec N j - labVec N i) := by
    rw [← Work.BoseBoxFock.vec_neg (labVec N j - labVec N i)]
    congr 1
    abel
  rw [Mc, Mc, h, chiHatSq_neg]

end Work.BoseRowQ2
