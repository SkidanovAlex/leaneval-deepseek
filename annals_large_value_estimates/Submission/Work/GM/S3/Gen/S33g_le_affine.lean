import Mathlib
import Submission.Work.GM.S3.gen_defs
import Submission.Work.GM.S3.prop101_S33_le_affine
import Submission.Work.GM.S3.S34_le_affine
import Submission.Work.GM.S3.integral_comp_inv

namespace Work.GM.S3.Gen

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (Rfun affineSum)

noncomputable section

/-!
# GM 10.1 with three independent dyadic scales: `S₃,₃ ≤ 16 ∫ (affineSum 2 M₃ M₂ M₁ f)²`

This file proves `S33g_le_affine`, the verbatim generalisation of
`Work.GM.S3.prop101_S33_le_affine` to the case where the three summation indices of
`Asumg` carry *independent* dyadic scales `M₁, M₂, M₃`:

`S33g = ∫_{1/2}^2 (Σ_{m₁∈idx1 M₁} Σ_{m₂∈idxM M₂} Σ_{m₃∈idxM M₃} R̃(a₁(m,v))²)² dv`,

with `a₁(m,v) = (m₁v + m₃)/(m₂v)`.  The chain of inequalities is exactly the one of
`prop101_S33_le_affine`:

* `Asumg v = AsumInvg (1/v)` (the substitution `u = 1/v` sends `a₁` to `(m₃u+m₁)/m₂`);
* `AsumInvg = 2 · AsumInvgPos` (the reflection `(m₁,m₂,m₃) ↦ (-m₁,-m₂,-m₃)`);
* `1/u² ≤ 4` on `[1/2,2]`;
* `AsumInvgPos ≤ affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ')` pointwise (interchange the
  roles of `m₁` and `m₃`).

The only difference to the single-scale case is that the outer index set of the dominating
`affineSum` has scale `M₃` (matching the `m₃`-range of `Asumg`) while its innermost summation
range is the larger `Icc (-⌊2M₁⌋) ⌊2M₁⌋ ⊇ idx1 M₁`.
-/

/-! ## The reflection `(m₁,m₂,m₃) ↦ (-m₁,-m₂,-m₃)` with independent scales `M₂, M₃`

`Work.GM.S3.sum_triple_reflect` only covers the case where the two `idxM`-slots carry the *same*
scale.  Here the two large slots have independent scales `M₂` (the `m₂`-slot) and `M₃` (the
`m₃`-slot), and the hypothesis `1 ≤ M` is weakened to `0 < M₂`. -/

/-- Splitting the `m₂`-sum of `Σ_{m₁ ∈ idx1 M₁} Σ_{m₂ ∈ idxM M₂} Σ_{m₃ ∈ idxM M₃}` into its
positive (`idxMpos M₂`) and negative (`m₂ < 0`) parts (`0 < M₂`, so `m₂ ≠ 0`). -/
theorem sum_triple_split_gen (M₁ M₂ M₃ : ℝ) (F : ℤ → ℤ → ℤ → ℝ) (hM : 0 < M₂) :
    (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M₂, ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃)
      = (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M₂, ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃)
      + (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M₂).filter (fun m => m < 0),
          ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃) := by
  have hM0 : 0 ≤ M₂ := le_of_lt hM
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m₁ _
  rw [← Finset.sum_filter_add_sum_filter_not (idxM M₂) (fun m : ℤ => 0 < m)
        (fun m₂ => ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃)]
  rw [filter_pos_idxM_eq_idxMpos hM0, ← filter_lt_zero_eq_filter_not_pos hM]

/-- The `m₂ < 0` half of a triple sum with a reflection-invariant summand equals its `m₂ > 0`
half; the two `idxM`-slots carry independent scales (`Work.GM.S3.sum_triple_neg_eq_pos` with
`M₂ = M₃` and `0 < M₂` in place of `1 ≤ M₂`). -/
theorem sum_triple_neg_eq_pos_gen (M₁ M₂ M₃ : ℝ) (F : ℤ → ℤ → ℤ → ℝ)
    (hF : ∀ m₁ m₂ m₃ : ℤ, F (-m₁) (-m₂) (-m₃) = F m₁ m₂ m₃) (hM : 0 < M₂) :
    (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M₂).filter (fun m => m < 0), ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃)
      = (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M₂, ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃) := by
  have hM0 : 0 ≤ M₂ := le_of_lt hM
  -- reflect `m₃`
  have h1 : (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M₂).filter (fun m => m < 0),
        ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃)
      = (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M₂).filter (fun m => m < 0),
          ∑ m₃ ∈ idxM M₃, F m₁ m₂ (-m₃)) := by
    apply Finset.sum_congr rfl
    intro m₁ _
    apply Finset.sum_congr rfl
    intro m₂ _
    exact (sum_neg_idxM M₃ (fun m₃ => F m₁ m₂ m₃)).symm
  -- reflect `m₁`
  have h2 : (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M₂).filter (fun m => m < 0),
        ∑ m₃ ∈ idxM M₃, F m₁ m₂ (-m₃))
      = (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M₂).filter (fun m => m < 0),
          ∑ m₃ ∈ idxM M₃, F (-m₁) m₂ (-m₃)) :=
    (sum_neg_idx1 M₁ (fun m₁ =>
      ∑ m₂ ∈ (idxM M₂).filter (fun m => m < 0), ∑ m₃ ∈ idxM M₃, F m₁ m₂ (-m₃))).symm
  -- reflect `m₂`: the negative part of `idxM M₂` is the reflection of `idxMpos M₂`
  have h3 : (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M₂).filter (fun m => m < 0),
        ∑ m₃ ∈ idxM M₃, F (-m₁) m₂ (-m₃))
      = (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M₂, ∑ m₃ ∈ idxM M₃, F (-m₁) (-m₂) (-m₃)) := by
    apply Finset.sum_congr rfl
    intro m₁ _
    simpa using sum_neg_idxMneg hM0 (fun m₂ => ∑ m₃ ∈ idxM M₃, F (-m₁) (-m₂) (-m₃))
  have h4 : (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M₂, ∑ m₃ ∈ idxM M₃, F (-m₁) (-m₂) (-m₃))
      = (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M₂, ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃) := by
    apply Finset.sum_congr rfl
    intro m₁ _
    apply Finset.sum_congr rfl
    intro m₂ _
    apply Finset.sum_congr rfl
    intro m₃ _
    exact hF m₁ m₂ m₃
  exact h1.trans (h2.trans (h3.trans h4))

/-- For a summand invariant under `(m₁,m₂,m₃) ↦ (-m₁,-m₂,-m₃)`, the triple sum over
`idx1 M₁ × idxM M₂ × idxM M₃` is twice the sum over `idx1 M₁ × idxMpos M₂ × idxM M₃`. -/
theorem sum_triple_reflect_gen (M₁ M₂ M₃ : ℝ) (F : ℤ → ℤ → ℤ → ℝ)
    (hF : ∀ m₁ m₂ m₃ : ℤ, F (-m₁) (-m₂) (-m₃) = F m₁ m₂ m₃) (hM : 0 < M₂) :
    (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M₂, ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃)
      = 2 * (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M₂, ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃) := by
  have hs := sum_triple_split_gen M₁ M₂ M₃ F hM
  have hn := sum_triple_neg_eq_pos_gen M₁ M₂ M₃ F hF hM
  rw [hs, hn]
  ring

/-! ## The `u = 1/v` form and the reflection for `Asumg` -/

/-- `Asumg v = AsumInvg (1/v)` for `v ≠ 0`: the substitution `u = 1/v` turns `arg1 m₁ m₂ m₃ v =
(m₁v + m₃)/(m₂v)` into `(m₃u + m₁)/m₂`. -/
theorem asumg_eq_asuminvg (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hM₂ : 0 < M₂) {v : ℝ} (hv : v ≠ 0) :
    Asumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v = AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ (1 / v) := by
  simp only [Asumg, AsumInvg, arg1]
  apply Finset.sum_congr rfl; intro m₁ _
  apply Finset.sum_congr rfl; intro m₂ hm₂
  apply Finset.sum_congr rfl; intro m₃ _
  congr 1
  have hm2ne : ((m₂ : ℤ) : ℝ) ≠ 0 := by
    have h := ne_zero_of_mem_idxM hm₂ hM₂
    exact_mod_cast h
  field_simp
  ring_nf

/-- `AsumInvg = 2 · AsumInvgPos`: the reflection `(m₁,m₂,m₃) ↦ (-m₁,-m₂,-m₃)` preserves the
argument `(m₃u + m₁)/m₂` and exchanges the two halves of the `m₂`-sum.  Requires only `0 < M₂`
(the reflection argument needs `1 ≤ M` in `Work.GM.S3.sum_triple_reflect`, which is stronger than
needed). -/
theorem asuminvg_eq_two_mul (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hM₂ : 0 < M₂) (u : ℝ) :
    AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u = 2 * AsumInvgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ u := by
  have hF : ∀ m₁ m₂ m₃ : ℤ,
      Rtilde W N B ψ₁ ψ₂ ((((-m₃ : ℤ) : ℝ) * u + ((-m₁ : ℤ) : ℝ)) / ((-m₂ : ℤ) : ℝ)) ^ 2
        = Rtilde W N B ψ₁ ψ₂ (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) ^ 2 := by
    intro m₁ m₂ m₃
    have ha : ((((-m₃ : ℤ) : ℝ) * u + ((-m₁ : ℤ) : ℝ)) / ((-m₂ : ℤ) : ℝ))
        = (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) := by
      simp only [Int.cast_neg]; ring_nf
    rw [ha]
  simpa only [AsumInvg, AsumInvgPos] using
    sum_triple_reflect_gen M₁ M₂ M₃
      (fun m₁ m₂ m₃ : ℤ => Rtilde W N B ψ₁ ψ₂ (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) ^ 2)
      hF hM₂

/-- `0 ≤ AsumInvgPos u` (a finite sum of squares). -/
theorem asuminvgPos_nonneg (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ) (u : ℝ) :
    0 ≤ AsumInvgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ u := by
  simp only [AsumInvgPos]
  exact Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

/-! ## Pointwise domination by `affineSum` -/

/-- Pointwise domination `AsumInvgPos u ≤ affineSum 2 M₃ M₂ M₁ f u` with `f = testfun`, by
interchanging the roles of `m₁` and `m₃` in the index sets (the `m₃`-range `idxM M₃` becomes the
`idx1`-slot of scale `M₃`, the `m₁`-range `idx1 M₁` becomes the innermost `Icc (-⌊2M₁⌋) ⌊2M₁⌋`)
and using `R̃² ≤ f` pointwise. -/
theorem asuminvgPos_le_affineSum (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ)
    (ψ₁ ψ₂ ψ' : ℝ → ℝ) (hB : 0 ≤ (N : ℝ) * B)
    (hψ₁ : IsBumpAtZero ψ₁ 16) (hψ₂ : IsBumpAtOne ψ₂ 16) (hψ' : IsBumpAtOne ψ' 16)
    (hψ'one : ∀ x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8), ψ' x = 1)
    (hRsupp : ∀ x, RtildeSq W N B ψ₁ ψ₂ x ≠ 0 → x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)) (u : ℝ) :
    AsumInvgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ u ≤
      affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ') u := by
  have hRnn : ∀ x, 0 ≤ RtildeSq W N B ψ₁ ψ₂ x := fun x =>
    integral_nonneg fun u' =>
      mul_nonneg (mul_nonneg (mul_nonneg hB (hψ₁.2.1 _)) (hψ₂.2.1 u')) (sq_nonneg _)
  have hpt : ∀ x, Rtilde W N B ψ₁ ψ₂ x ^ 2 = testfun N W B ψ₁ ψ₂ ψ' x := by
    intro x
    rw [Rtilde_sq W N B ψ₁ ψ₂ x (hRnn x)]
    simp only [testfun]
    by_cases hx : RtildeSq W N B ψ₁ ψ₂ x = 0
    · simp [hx]
    · simp [hψ'one x (hRsupp x hx)]
  have htestfun_nn : ∀ x, 0 ≤ testfun N W B ψ₁ ψ₂ ψ' x :=
    fun x => mul_nonneg (hψ'.2.1 x) (hRnn x)
  have hL1 : AsumInvgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ u =
      ∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M₂, ∑ m₃ ∈ idxM M₃,
        testfun N W B ψ₁ ψ₂ ψ' (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) := by
    simp only [AsumInvgPos]
    apply Finset.sum_congr rfl; intro m₁ _
    apply Finset.sum_congr rfl; intro m₂ _
    apply Finset.sum_congr rfl; intro m₃ _
    exact hpt _
  have hL2 : (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M₂, ∑ m₃ ∈ idxM M₃,
        testfun N W B ψ₁ ψ₂ ψ' (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)))
      = ∑ m₃ ∈ idxM M₃, ∑ m₂ ∈ idxMpos M₂, ∑ m₁ ∈ idx1 M₁,
        testfun N W B ψ₁ ψ₂ ψ' (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) := by
    conv_lhs => enter [2, x]; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => enter [2, x]; rw [Finset.sum_comm]
  have hL := hL1.trans hL2
  have hR : affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ') u =
      ∑ m₃ ∈ idxM M₃, ∑ m₂ ∈ idxMpos M₂, ∑ m₁ ∈ Finset.Icc (-⌊2 * M₁⌋) ⌊2 * M₁⌋,
        testfun N W B ψ₁ ψ₂ ψ' (((m₃ : ℝ) * u + (m₁ : ℝ)) / (m₂ : ℝ)) := by
    simp only [affineSum, idxM, idxMpos]
  rw [hL, hR]
  refine Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun b _ => ?_))
  rw [idx1]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun a _ _ => htestfun_nn _)

/-! ## Continuity -/

/-- Continuity of `u ↦ AsumInvgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ u`. -/
theorem continuous_asuminvgPos (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hψ₁ : IsBumpAtZero ψ₁ 16) (hψ₂ : IsBumpAtOne ψ₂ 16) :
    Continuous (fun u => AsumInvgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ u) := by
  have hRt : Continuous (fun x => Rtilde W N B ψ₁ ψ₂ x) :=
    Real.continuous_sqrt.comp (RtildeSq_continuous W N B 16 ψ₁ ψ₂ hψ₁ hψ₂)
  simp only [AsumInvgPos]
  refine continuous_finset_sum _ (fun a _ => ?_)
  refine continuous_finset_sum _ (fun b hb => ?_)
  refine continuous_finset_sum _ (fun c _ => ?_)
  have hb1 : (1 : ℤ) ≤ b := (mem_Icc.mp (mem_filter.mp hb).1).1
  have hbne : ((b : ℤ) : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb1
    linarith
  have harg : Continuous (fun u : ℝ => (((c : ℝ) * u + (a : ℝ)) / (b : ℝ))) := by
    rw [show (fun u : ℝ => (((c : ℝ) * u + (a : ℝ)) / (b : ℝ)))
        = fun u => (((c : ℝ) * u + (a : ℝ)) * ((b : ℝ))⁻¹) from by
      funext u; rw [div_eq_mul_inv]]
    fun_prop
  exact (hRt.comp harg).pow 2

/-- Continuity of `u ↦ AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u` (the `m₂`-range is `idxM M₂`, and
`0 < M₂` ensures `m₂ ≠ 0`). -/
theorem continuous_asuminvg (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hψ₁ : IsBumpAtZero ψ₁ 16) (hψ₂ : IsBumpAtOne ψ₂ 16) (hM₂ : 0 < M₂) :
    Continuous (fun u => AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u) := by
  have hRt : Continuous (fun x => Rtilde W N B ψ₁ ψ₂ x) :=
    Real.continuous_sqrt.comp (RtildeSq_continuous W N B 16 ψ₁ ψ₂ hψ₁ hψ₂)
  simp only [AsumInvg]
  refine continuous_finset_sum _ (fun a _ => ?_)
  refine continuous_finset_sum _ (fun b hb => ?_)
  refine continuous_finset_sum _ (fun c _ => ?_)
  have hbne : ((b : ℤ) : ℝ) ≠ 0 := by
    have h := ne_zero_of_mem_idxM hb hM₂
    exact_mod_cast h
  have harg : Continuous (fun u : ℝ => (((c : ℝ) * u + (a : ℝ)) / (b : ℝ))) := by
    rw [show (fun u : ℝ => (((c : ℝ) * u + (a : ℝ)) / (b : ℝ)))
        = fun u => (((c : ℝ) * u + (a : ℝ)) * ((b : ℝ))⁻¹) from by
      funext u; rw [div_eq_mul_inv]]
    fun_prop
  exact (hRt.comp harg).pow 2

/-! ## Compact support of the dominating affine sum -/

/-- Compact support of `u ↦ affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ') u`: any nonzero summand
forces `|m₁ u| ≤ (33/8)·(2M₂) + 2M₁` where `|m₁| ≥ 1` (since `m₁ ∈ idx1 M₃` and `M₃ > 0`),
whence `|u| ≤ 33M₂/4 + 2M₁`. -/
theorem affineSum_testfun_hasCompactSupport_gen (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ)
    (ψ₁ ψ₂ ψ' : ℝ → ℝ) (hM₃ : 0 < M₃)
    (hRsupp : ∀ x, RtildeSq W N B ψ₁ ψ₂ x ≠ 0 → x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)) :
    HasCompactSupport (fun u => affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ') u) := by
  refine HasCompactSupport.intro
    (K := Set.Icc (-(33 / 4 * M₂ + 2 * M₁)) (33 / 4 * M₂ + 2 * M₁)) isCompact_Icc
    (fun u hu => ?_)
  simp only [affineSum]
  refine Finset.sum_eq_zero (fun m₁ hm₁ => ?_)
  refine Finset.sum_eq_zero (fun m₂ hm₂ => ?_)
  refine Finset.sum_eq_zero (fun m₃ hm₃ => ?_)
  refine testfun_eq_zero_of_notMem_support N W B ψ₁ ψ₂ ψ' hRsupp (fun hx => hu ?_)
  have hm1abs : (1 : ℝ) ≤ |(m₁ : ℝ)| := by
    have h := (mem_filter.mp hm₁).2
    have hpos : (0 : ℝ) < |(m₁ : ℝ)| := lt_trans hM₃ h
    have hne : m₁ ≠ 0 := by rintro rfl; simp at hpos
    have hone : (1 : ℤ) ≤ |m₁| := Int.one_le_abs hne
    exact_mod_cast hone
  have hm2mem : (1 : ℤ) ≤ m₂ := (mem_Icc.mp (mem_filter.mp hm₂).1).1
  have hm2pos : (0 : ℝ) < (m₂ : ℝ) := by
    have : (1 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm2mem
    linarith
  have hm2le : (m₂ : ℝ) ≤ 2 * M₂ := by
    have h := (mem_Icc.mp (mem_filter.mp hm₂).1).2
    calc (m₂ : ℝ) ≤ (⌊2 * M₂⌋ : ℝ) := by exact_mod_cast h
      _ ≤ 2 * M₂ := Int.floor_le _
  have hm3le : |(m₃ : ℝ)| ≤ 2 * M₁ := by
    have h := mem_Icc.mp hm₃
    have h1' : (-(⌊2 * M₁⌋ : ℝ)) ≤ (m₃ : ℝ) := by exact_mod_cast h.1
    have h2' : (m₃ : ℝ) ≤ (⌊2 * M₁⌋ : ℝ) := by exact_mod_cast h.2
    have hf : (⌊2 * M₁⌋ : ℝ) ≤ 2 * M₁ := Int.floor_le _
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hxabs : |(((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ))| ≤ 33 / 8 := by
    rw [abs_le]; exact ⟨by linarith [hx.1], hx.2⟩
  have hmain : |(m₁ : ℝ) * u| ≤ 33 / 4 * M₂ + 2 * M₁ := by
    have hane : (m₂ : ℝ) ≠ 0 := ne_of_gt hm2pos
    have hb : (m₁ : ℝ) * u =
        (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) * (m₂ : ℝ) - (m₃ : ℝ) := by
      rw [div_mul_cancel₀ _ hane]; ring
    rw [hb]
    calc |(((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) * (m₂ : ℝ) - (m₃ : ℝ)|
        ≤ |(((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) * (m₂ : ℝ)| + |(m₃ : ℝ)| := abs_sub _ _
      _ = |(((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ))| * |(m₂ : ℝ)| + |(m₃ : ℝ)| := by rw [abs_mul]
      _ ≤ (33 / 8) * (2 * M₂) + 2 * M₁ := by
          have h4 : |(((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ))| * |(m₂ : ℝ)|
              ≤ (33 / 8) * (2 * M₂) := by
            rw [abs_of_pos hm2pos]
            exact mul_le_mul hxabs hm2le (le_of_lt hm2pos) (by norm_num)
          linarith
      _ ≤ 33 / 4 * M₂ + 2 * M₁ := by linarith
  have habs : |u| ≤ 33 / 4 * M₂ + 2 * M₁ := by
    have h1 : |(m₁ : ℝ) * u| = |(m₁ : ℝ)| * |u| := abs_mul _ _
    have h2 : |u| ≤ |(m₁ : ℝ)| * |u| := by
      have h3 : (0 : ℝ) ≤ |u| := abs_nonneg u
      nlinarith [hm1abs, h3]
    linarith [h1 ▸ hmain]
  exact abs_le.mp habs

/-! ## The main statement -/

/-- **GM 10.1, recognition of `S₃,₃` as an `affineSum` integral, with three independent dyadic
scales.**  `S₃,₃ = ∫_{1/2}^{2}(Σ_m R̃(a₁(m,v))²)² dv` with `a₁ = (m₁v+m₃)/(m₂v)`: the reflection
`(m₁,m₂,m₃) ↦ (-m₁,-m₂,-m₃)` doubles the `m₂>0` part, the substitution `u = 1/v` turns `a₁`
into `(m₃u+m₁)/m₂` and costs `1/u² ≤ 4`, and after interchanging the `m₁`- and `m₃`-sums,
`R̃² = RtildeSq ≤ testfun` pointwise dominates the `u`-coefficient `m₃ ∈ idxM M₃` by the
`idx1 M₃`-slot of `affineSum 2 M₃ M₂ M₁`, whence
`S₃,₃ ≤ 16 ∫_ℝ (affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ'))²`. -/
theorem S33g_le_affine (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ ψ' : ℝ → ℝ)
    (hB : 0 ≤ (N : ℝ) * B) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    (hψ₁ : Work.GM.S3.IsBumpAtZero ψ₁ 16) (hψ₂ : Work.GM.S3.IsBumpAtOne ψ₂ 16)
    (hψ' : Work.GM.S3.IsBumpAtOne ψ' 16)
    (hψ'one : ∀ x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8), ψ' x = 1)
    (hRsupp : ∀ x, Work.GM.S3.RtildeSq W N B ψ₁ ψ₂ x ≠ 0 →
      x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)) :
    Work.GM.S3.Gen.S33g N W B M₁ M₂ M₃ ψ₁ ψ₂ ≤
      16 * ∫ u, (Submission.GM.affineSum 2 M₃ M₂ M₁
        (Work.GM.S3.testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by
  have hAInv_cont : Continuous (fun u => AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u) :=
    continuous_asuminvg N W B M₁ M₂ M₃ ψ₁ ψ₂ hψ₁ hψ₂ hM₂
  have hAInvPos_cont : Continuous (fun u => AsumInvgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ u) :=
    continuous_asuminvgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ hψ₁ hψ₂
  have htest_cont : Continuous (fun u => testfun N W B ψ₁ ψ₂ ψ' u) := by
    simp only [testfun]
    exact hψ'.1.continuous.mul (RtildeSq_continuous W N B 16 ψ₁ ψ₂ hψ₁ hψ₂)
  have hG_cont : Continuous (fun u => affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ') u) :=
    prop101_continuous_affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ') htest_cont
  have hG_cs : HasCompactSupport (fun u => affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ') u) :=
    affineSum_testfun_hasCompactSupport_gen N W B M₁ M₂ M₃ ψ₁ ψ₂ ψ' hM₃ hRsupp
  have hG_cs2 : HasCompactSupport
      (fun u => (affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hG_cs ⊢
    filter_upwards [hG_cs] with u hu
    simp [hu]
  have hG_int : Integrable
      (fun u => (affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2) volume :=
    (hG_cont.pow 2).integrable_of_hasCompactSupport hG_cs2
  -- (i) `Asumg v = AsumInvg (1/v)`
  have hstep1 : S33g N W B M₁ M₂ M₃ ψ₁ ψ₂ =
      ∫ v in (1 / 2 : ℝ)..2, (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ (1 / v)) ^ 2 := by
    rw [S33g]
    apply intervalIntegral.integral_congr
    intro v hv
    have hv' : v ∈ Set.Icc (1 / 2 : ℝ) 2 := by
      rwa [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hv
    have hv0 : v ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hv'.1)
    dsimp only
    rw [asumg_eq_asuminvg N W B M₁ M₂ M₃ ψ₁ ψ₂ hM₂ hv0]
  -- (ii) the substitution `u = 1/v` on `[1/2,2]`
  have hstep2 : (∫ v in (1 / 2 : ℝ)..2, (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ (1 / v)) ^ 2) =
      ∫ u in (1 / 2 : ℝ)..2, (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2 / u ^ 2 :=
    integral_comp_inv (K := fun u => (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2)
      (hAInv_cont.pow 2).continuousOn
  -- (iii) `1/u² ≤ 4` on `[1/2,2]`
  have hstep3 : (∫ u in (1 / 2 : ℝ)..2, (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2 / u ^ 2) ≤
      4 * ∫ u in (1 / 2 : ℝ)..2, (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2 := by
    have hmono : (∫ u in (1 / 2 : ℝ)..2, (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2 / u ^ 2) ≤
        ∫ u in (1 / 2 : ℝ)..2, 4 * (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2 := by
      refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ (fun u hu => ?_)
      · refine (((hAInv_cont.pow 2).continuousOn).div (continuousOn_id.pow 2) ?_).intervalIntegrable
        intro u hu
        have hu' : u ∈ Set.Icc (1 / 2 : ℝ) 2 := by
          rwa [Set.uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hu
        have : (0 : ℝ) < u := lt_of_lt_of_le (by norm_num) hu'.1
        exact pow_ne_zero 2 (ne_of_gt this)
      · exact ((hAInv_cont.pow 2).const_mul 4).intervalIntegrable _ _
      · rw [div_eq_mul_inv]
        have hquarter : (1 : ℝ) / 4 ≤ u ^ 2 := by nlinarith [hu.1]
        have hinv : (u ^ 2)⁻¹ ≤ 4 := by
          simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 4) hquarter
        calc (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2 * (u ^ 2)⁻¹
            ≤ (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2 * 4 :=
              mul_le_mul_of_nonneg_left hinv (sq_nonneg _)
          _ = 4 * (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2 := by ring
    rwa [intervalIntegral.integral_const_mul] at hmono
  -- (iv) `AsumInvg = 2 · AsumInvgPos`
  have hstep4 : (∫ u in (1 / 2 : ℝ)..2, (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2) =
      4 * ∫ u in (1 / 2 : ℝ)..2, (AsumInvgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2 := by
    have heq : (fun u => (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2)
        = fun u => 4 * (AsumInvgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2 := by
      funext u
      rw [asuminvg_eq_two_mul N W B M₁ M₂ M₃ ψ₁ ψ₂ hM₂ u]; ring
    rw [heq, intervalIntegral.integral_const_mul]
  -- (v) `AsumInvgPos ≤ affineSum`
  have hstep5 : (∫ u in (1 / 2 : ℝ)..2, (AsumInvgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2) ≤
      ∫ u in (1 / 2 : ℝ)..2, (affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by
    refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ (fun u _ => ?_)
    · exact (hAInvPos_cont.pow 2).intervalIntegrable _ _
    · exact (hG_cont.pow 2).intervalIntegrable _ _
    · exact pow_le_pow_left₀ (asuminvgPos_nonneg N W B M₁ M₂ M₃ ψ₁ ψ₂ u)
        (asuminvgPos_le_affineSum N W B M₁ M₂ M₃ ψ₁ ψ₂ ψ' hB hψ₁ hψ₂ hψ' hψ'one hRsupp u) 2
  -- (vi) extend `[1/2,2]` to `ℝ`
  have hstep6 : (∫ u in (1 / 2 : ℝ)..2,
        (affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2) ≤
      ∫ u, (affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by
    rw [intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)]
    exact setIntegral_le_integral hG_int (Filter.Eventually.of_forall (fun u => sq_nonneg _))
  calc S33g N W B M₁ M₂ M₃ ψ₁ ψ₂
      = ∫ v in (1 / 2 : ℝ)..2, (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ (1 / v)) ^ 2 := hstep1
    _ = ∫ u in (1 / 2 : ℝ)..2, (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2 / u ^ 2 := hstep2
    _ ≤ 4 * ∫ u in (1 / 2 : ℝ)..2, (AsumInvg N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2 := hstep3
    _ = 4 * (4 * ∫ u in (1 / 2 : ℝ)..2, (AsumInvgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2) := by
          rw [hstep4]
    _ = 16 * ∫ u in (1 / 2 : ℝ)..2, (AsumInvgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ u) ^ 2 := by ring
    _ ≤ 16 * ∫ u in (1 / 2 : ℝ)..2,
          (affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by linarith [hstep5]
    _ ≤ 16 * ∫ u, (affineSum 2 M₃ M₂ M₁ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by
          linarith [hstep6]

end

end Work.GM.S3.Gen
