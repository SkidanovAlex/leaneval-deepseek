import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.pairRowDirDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowKsubDir` — the Dirichlet (`BoxSmooth`) form of the (S2) glue

`Work.BoseBoxFock.pairRowKsub.int_pairing_sub_le` turns a *pairing* bound
`‖∫_{box²}(K−K')𝓖‖ ≤ ε√(∫∫‖𝓖‖²)` into `‖∫∫K𝓖 − ∫∫K'𝓖‖ ≤ ε√C` via an `L²` bound for the fibre
`𝓖`.  At the honest weights the available pairing estimate is *not* an `L²` statement but the
**Dirichlet** one (`Work.BoseBoxFock.K1exp_sub_K1lim_pairing_dir`, fed by the `χχ`-row `T6` and the
images row `T7`):

    ‖∫_{box²}(K−K')·G‖ ≤ ε·√(pairEnergy ℓ G)      for every `BoxSmooth ℓ G` .

`int_pairing_sub_le_dir` is the matching glue: `BoxSmooth` lets us replace the fibre `𝓖` by the
smooth representative `G'` (the pairing and `pairEnergy` only see the box squared), and then the
Dirichlet bound transfers verbatim.

`rowPairSubC_Ksub_of_shapes_pair` is the *per-pair* variant of
`Work.BoseBoxFock.rowPairSubC_Ksub_of_shapes`: with a two-term/per-fibre right-hand side the row-level
bound is a sum over pairs (not `#(pairSet n)` times one constant), which is what the consumer needs in
order to Cauchy–Schwarz the sum of the per-pair Dirichlet norms.

`sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-! ## 1. The Dirichlet glue -/

/-- **The Dirichlet form of the kernel-substitution bound.**  If the pairing of the kernel
difference against every `BoxSmooth` test function is `≤ ε√(pairEnergy ℓ ·)` (and the kernel
difference is supported in the box squared), then the two kernel forms of the fibre `𝓖` differ by at
most `ε√(pairEnergy ℓ 𝓖)`. -/
theorem int_pairing_sub_le_dir {ℓ ε : ℝ} {𝓖 K K' : E3 → E3 → ℂ} (hℓ : 0 < ℓ) (hε : 0 ≤ ε)
    (hGsupp : Function.support (Function.uncurry 𝓖) ⊆
      Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ))
    (hPair : ∀ G : E3 → E3 → ℂ, BoxSmooth ℓ G →
      ‖∫ w in Work.BoseK15.corpusBox.boxL ℓ,
         ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (K w y - K' w y) * G w y‖
        ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ G)
            + Real.sqrt (massBox ℓ G)))
    (hbs : BoxSmooth ℓ 𝓖)
    (hIntK : MeasureTheory.Integrable (Function.uncurry (fun w y : E3 => K w y * 𝓖 w y))
      (volume : Measure (E3 × E3)))
    (hIntK' : MeasureTheory.Integrable (Function.uncurry (fun w y : E3 => K' w y * 𝓖 w y))
      (volume : Measure (E3 × E3))) :
    ‖(∫ w : E3, ∫ y : E3, K w y * 𝓖 w y) - (∫ w : E3, ∫ y : E3, K' w y * 𝓖 w y)‖
      ≤ ε * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy ℓ 𝓖) + Real.sqrt (massBox ℓ 𝓖)) := by
  classical
  obtain ⟨G', hG'sm, hG'eq⟩ := hbs
  have HK : MeasureTheory.Integrable (fun z : E3 × E3 => K z.1 z.2 * 𝓖 z.1 z.2)
      (volume : Measure (E3 × E3)) := hIntK
  have HK' : MeasureTheory.Integrable (fun z : E3 × E3 => K' z.1 z.2 * 𝓖 z.1 z.2)
      (volume : Measure (E3 × E3)) := hIntK'
  have hsuppD : Function.support (Function.uncurry (fun w y : E3 => (K w y - K' w y) * 𝓖 w y))
      ⊆ Set.prod (Work.BoseK15.corpusBox.boxL ℓ) (Work.BoseK15.corpusBox.boxL ℓ) := by
    intro z hz
    have h1 : Function.uncurry 𝓖 z ≠ 0 := by
      intro h
      exact hz (by
        show (K z.1 z.2 - K' z.1 z.2) * 𝓖 z.1 z.2 = 0
        rw [show 𝓖 z.1 z.2 = 0 from h, mul_zero])
    exact hGsupp (Function.mem_support.mpr h1)
  have HD : MeasureTheory.Integrable
      (Function.uncurry (fun w y : E3 => (K w y - K' w y) * 𝓖 w y))
      (volume : Measure (E3 × E3)) := by
    have h := HK.sub HK'
    refine h.congr ?_
    refine Filter.Eventually.of_forall fun z => ?_
    simp only [Pi.sub_apply, Function.uncurry]
    ring
  have hsub : (∫ z : E3 × E3, K z.1 z.2 * 𝓖 z.1 z.2)
      - (∫ z : E3 × E3, K' z.1 z.2 * 𝓖 z.1 z.2)
      = ∫ z : E3 × E3, (K z.1 z.2 - K' z.1 z.2) * 𝓖 z.1 z.2 := by
    refine (MeasureTheory.integral_sub HK HK').symm.trans ?_
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.sub_apply]
    ring
  have hbox : (∫ z : E3 × E3, (K z.1 z.2 - K' z.1 z.2) * 𝓖 z.1 z.2)
      = ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (K w y - K' w y) * 𝓖 w y :=
    (MeasureTheory.integral_integral HD).symm.trans
      (integral_integral_eq_iterated_boxL (f := fun w y : E3 => (K w y - K' w y) * 𝓖 w y)
        hsuppD)
  have htrans : (∫ w in Work.BoseK15.corpusBox.boxL ℓ,
        ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (K w y - K' w y) * G' w y)
      = ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (K w y - K' w y) * 𝓖 w y :=
    setIntegral_pairing_congr_box (K := fun w y => K w y - K' w y) (G := 𝓖) (G' := G')
      (fun w y hw hy => hG'eq w y hw hy)
  have hpe : Work.BoseBoxFock.L1Tails.pairEnergy ℓ G'
      = Work.BoseBoxFock.L1Tails.pairEnergy ℓ 𝓖 :=
    pairEnergy_congr_box hℓ hG'eq
  have hmass : massBox ℓ G' = massBox ℓ 𝓖 := massBox_congr_box hG'eq
  have hmain : (∫ w : E3, ∫ y : E3, K w y * 𝓖 w y) - (∫ w : E3, ∫ y : E3, K' w y * 𝓖 w y)
      = ∫ w in Work.BoseK15.corpusBox.boxL ℓ,
          ∫ y in Work.BoseK15.corpusBox.boxL ℓ, (K w y - K' w y) * G' w y := by
    rw [MeasureTheory.integral_integral hIntK, MeasureTheory.integral_integral hIntK']
    exact hsub.trans (hbox.trans htrans.symm)
  rw [hmain, ← hpe, ← hmass]
  exact hPair G' ⟨G', hG'sm, fun w y _ _ => rfl⟩

/-! ## 2. The per-pair row-level assembly -/

/-- **Per-pair form of the row-level (S2) bound.**  If each of the three shapes has its per-pair
substitution bound `≤ ε·(r13 p)`, `≤ ε·(r21 p)`, `≤ ε·(r23 p)`, then the whole block-`I/II` part of
the row moves by at most `2|a|·ε·Σ_{p ∈ pairSet n} (r13 p + r21 p + r23 p)`. -/
theorem rowPairSubC_Ksub_of_shapes_pair {n : ℕ} {a ε : ℝ} {Θ : Xn n → ℂ} {A : E3 → ℂ}
    {KI KI' KII KII' : E3 → E3 → ℂ}
    (hε : 0 ≤ ε)
    (r13 r21 r23 : Fin n × Fin n → ℝ)
    (hr13 : ∀ p, 0 ≤ r13 p) (hr21 : ∀ p, 0 ≤ r21 p) (hr23 : ∀ p, 0 ≤ r23 p)
    (h13 : ∀ p ∈ Submission.BoseGases.pairSet n,
      ‖rowShape13 Θ A A KI p - rowShape13 Θ A A KI' p‖ ≤ ε * r13 p)
    (h21 : ∀ p ∈ Submission.BoseGases.pairSet n,
      ‖rowShape21 Θ A KII p - rowShape21 Θ A KII' p‖ ≤ ε * r21 p)
    (h23 : ∀ p ∈ Submission.BoseGases.pairSet n,
      ‖rowShape23 Θ A A KII p - rowShape23 Θ A A KII' p‖ ≤ ε * r23 p) :
    ‖rowPairSubC a Θ A KI KII - rowPairSubC a Θ A KI' KII'‖
      ≤ 2 * |a| * ε * ∑ p ∈ Submission.BoseGases.pairSet n, (r13 p + r21 p + r23 p) := by
  classical
  have h13s : ‖rowSum13 Θ A A KI - rowSum13 Θ A A KI'‖
      ≤ ε * ∑ p ∈ Submission.BoseGases.pairSet n, r13 p := by
    rw [rowSum13, rowSum13, ← Finset.sum_sub_distrib]
    calc ‖∑ p ∈ Submission.BoseGases.pairSet n,
            (rowShape13 Θ A A KI p - rowShape13 Θ A A KI' p)‖
        ≤ ∑ p ∈ Submission.BoseGases.pairSet n,
            ‖rowShape13 Θ A A KI p - rowShape13 Θ A A KI' p‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ Submission.BoseGases.pairSet n, ε * r13 p := Finset.sum_le_sum h13
      _ = ε * ∑ p ∈ Submission.BoseGases.pairSet n, r13 p := by
          rw [Finset.mul_sum]
  have h21s : ‖rowSum21 Θ A KII - rowSum21 Θ A KII'‖
      ≤ ε * ∑ p ∈ Submission.BoseGases.pairSet n, r21 p := by
    rw [rowSum21, rowSum21, ← Finset.sum_sub_distrib]
    calc ‖∑ p ∈ Submission.BoseGases.pairSet n,
            (rowShape21 Θ A KII p - rowShape21 Θ A KII' p)‖
        ≤ ∑ p ∈ Submission.BoseGases.pairSet n,
            ‖rowShape21 Θ A KII p - rowShape21 Θ A KII' p‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ Submission.BoseGases.pairSet n, ε * r21 p := Finset.sum_le_sum h21
      _ = ε * ∑ p ∈ Submission.BoseGases.pairSet n, r21 p := by
          rw [Finset.mul_sum]
  have h23s : ‖rowSum23 Θ A A KII - rowSum23 Θ A A KII'‖
      ≤ ε * ∑ p ∈ Submission.BoseGases.pairSet n, r23 p := by
    rw [rowSum23, rowSum23, ← Finset.sum_sub_distrib]
    calc ‖∑ p ∈ Submission.BoseGases.pairSet n,
            (rowShape23 Θ A A KII p - rowShape23 Θ A A KII' p)‖
        ≤ ∑ p ∈ Submission.BoseGases.pairSet n,
            ‖rowShape23 Θ A A KII p - rowShape23 Θ A A KII' p‖ := norm_sum_le _ _
      _ ≤ ∑ p ∈ Submission.BoseGases.pairSet n, ε * r23 p := Finset.sum_le_sum h23
      _ = ε * ∑ p ∈ Submission.BoseGases.pairSet n, r23 p := by
          rw [Finset.mul_sum]
  have hYZ : ‖(rowSum21 Θ A KII - rowSum21 Θ A KII')
      + (rowSum23 Θ A A KII - rowSum23 Θ A A KII')‖
      ≤ ε * (∑ p ∈ Submission.BoseGases.pairSet n, (r21 p + r23 p)) := by
    calc ‖(rowSum21 Θ A KII - rowSum21 Θ A KII')
          + (rowSum23 Θ A A KII - rowSum23 Θ A A KII')‖
        ≤ ‖rowSum21 Θ A KII - rowSum21 Θ A KII'‖
          + ‖rowSum23 Θ A A KII - rowSum23 Θ A A KII'‖ := norm_add_le _ _
      _ ≤ ε * (∑ p ∈ Submission.BoseGases.pairSet n, r21 p)
          + ε * (∑ p ∈ Submission.BoseGases.pairSet n, r23 p) := add_le_add h21s h23s
      _ = ε * (∑ p ∈ Submission.BoseGases.pairSet n, (r21 p + r23 p)) := by
          rw [Finset.sum_add_distrib]; ring
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
  have hA : 0 ≤ ∑ p ∈ Submission.BoseGases.pairSet n, r13 p :=
    Finset.sum_nonneg fun p _ => hr13 p
  have hB : 0 ≤ ∑ p ∈ Submission.BoseGases.pairSet n, (r21 p + r23 p) :=
    Finset.sum_nonneg fun p _ => add_nonneg (hr21 p) (hr23 p)
  have hsplit : (∑ p ∈ Submission.BoseGases.pairSet n, (r13 p + r21 p + r23 p))
      = (∑ p ∈ Submission.BoseGases.pairSet n, r13 p)
        + ∑ p ∈ Submission.BoseGases.pairSet n, (r21 p + r23 p) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => by ring
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
    _ ≤ |a| * (ε * ∑ p ∈ Submission.BoseGases.pairSet n, r13 p)
        + (1 / 2) * |a| * (ε * ∑ p ∈ Submission.BoseGases.pairSet n, (r21 p + r23 p)) := by
        refine add_le_add (mul_le_mul_of_nonneg_left h13s (abs_nonneg _)) ?_
        exact mul_le_mul_of_nonneg_left hYZ (by positivity)
    _ ≤ 2 * |a| * ε * ((∑ p ∈ Submission.BoseGases.pairSet n, r13 p)
          + ∑ p ∈ Submission.BoseGases.pairSet n, (r21 p + r23 p)) := by
        have h1 : |a| * (ε * ∑ p ∈ Submission.BoseGases.pairSet n, r13 p)
              + (1 / 2) * |a| * (ε * ∑ p ∈ Submission.BoseGases.pairSet n, (r21 p + r23 p))
            = |a| * ε * ((∑ p ∈ Submission.BoseGases.pairSet n, r13 p)
                + (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n, (r21 p + r23 p)) := by ring
        have h2 : (∑ p ∈ Submission.BoseGases.pairSet n, r13 p)
              + (1 / 2) * ∑ p ∈ Submission.BoseGases.pairSet n, (r21 p + r23 p)
            ≤ 2 * ((∑ p ∈ Submission.BoseGases.pairSet n, r13 p)
                + ∑ p ∈ Submission.BoseGases.pairSet n, (r21 p + r23 p)) := by
          linarith [hA, hB]
        have h3 : 2 * |a| * ε * ((∑ p ∈ Submission.BoseGases.pairSet n, r13 p)
              + ∑ p ∈ Submission.BoseGases.pairSet n, (r21 p + r23 p))
            = |a| * ε * (2 * ((∑ p ∈ Submission.BoseGases.pairSet n, r13 p)
                + ∑ p ∈ Submission.BoseGases.pairSet n, (r21 p + r23 p))) := by ring
        rw [h1, h3]
        exact mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg a) hε)
    _ = 2 * |a| * ε * ∑ p ∈ Submission.BoseGases.pairSet n, (r13 p + r21 p + r23 p) := by
        rw [hsplit]

end Work.BoseBoxFock
