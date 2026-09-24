import Mathlib
import Submission.Work.GM.S3.gen_defs
import Submission.Work.GM.S3.S34_le_affine
import Submission.Work.GM.S3.bsum_reflect
import Submission.Work.GM.S3.bsumPos_le_affineSum

namespace Work.GM.S3.Gen

open Complex Finset MeasureTheory
open scoped BigOperators
open Submission.GM (affineSum)

/-!
# GM Prop 10.1, `S₃,₄` recognition with three independent dyadic scales

The verbatim generalisation of `Work.GM.S3.S34_le_affine` to the objects `S34g`, `Bsumg`,
`BsumgPos` of `gen_defs.lean`, where the two large slots carry *independent* dyadic scales
`M₂`, `M₃` (instead of a single `M`).  The only ingredients that genuinely change are the
combinatorial reflection (`Bsumg = 2 · BsumgPos`, now reflecting the three slots against
`idx1 M₁`, `idxM M₂`, `idxM M₃` separately) and the compact-support estimate for the affine sum
(the support radius becomes `≍ M₂ + M₃` instead of `≍ M`).
-/

section Combinatorics

/-- Splitting a triple sum `Σ_{m₁∈idx1 M₁} Σ_{m₂∈idxM M₂} Σ_{m₃∈idxM M₃}` into its `m₂ > 0`
part (`idxMpos M₂`) and its `m₂ < 0` part.  Generalises `Work.GM.S3.sum_triple_split`, in which
the two large index sets coincide. -/
lemma sum_triple_split_g (M₁ M₂ M₃ : ℝ) (F : ℤ → ℤ → ℤ → ℝ) (hM₂ : 0 < M₂) :
    (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M₂, ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃)
      = (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M₂, ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃)
      + (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M₂).filter (fun m => m < 0),
          ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃) := by
  have hM0 : 0 ≤ M₂ := le_of_lt hM₂
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m₁ _
  rw [← Finset.sum_filter_add_sum_filter_not (idxM M₂) (fun m : ℤ => 0 < m)
        (fun m₂ => ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃)]
  rw [filter_pos_idxM_eq_idxMpos hM0, ← filter_lt_zero_eq_filter_not_pos hM₂]

/-- The `m₂ < 0` half of a triple sum with a reflection-invariant summand equals its `m₂ > 0`
half: the reflection `(m₁,m₂,m₃) ↦ (-m₁,-m₂,-m₃)` maps
`idx1 M₁ × (idxM M₂ ∩ {m₂ < 0}) × idxM M₃` bijectively onto
`idx1 M₁ × idxMpos M₂ × idxM M₃`.  Generalises `Work.GM.S3.sum_triple_neg_eq_pos`. -/
lemma sum_triple_neg_eq_pos_g (M₁ M₂ M₃ : ℝ) (F : ℤ → ℤ → ℤ → ℝ)
    (hF : ∀ m₁ m₂ m₃ : ℤ, F (-m₁) (-m₂) (-m₃) = F m₁ m₂ m₃) (hM₂ : 0 < M₂) :
    (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ (idxM M₂).filter (fun m => m < 0), ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃)
      = (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M₂, ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃) := by
  have hM0 : 0 ≤ M₂ := le_of_lt hM₂
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
`idx1 M₁ × idxM M₂ × idxM M₃` is twice the sum over `idx1 M₁ × idxMpos M₂ × idxM M₃`.
Generalises `Work.GM.S3.sum_triple_reflect`. -/
lemma sum_triple_reflect_g (M₁ M₂ M₃ : ℝ) (F : ℤ → ℤ → ℤ → ℝ)
    (hF : ∀ m₁ m₂ m₃ : ℤ, F (-m₁) (-m₂) (-m₃) = F m₁ m₂ m₃) (hM₂ : 0 < M₂) :
    (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxM M₂, ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃)
      = 2 * (∑ m₁ ∈ idx1 M₁, ∑ m₂ ∈ idxMpos M₂, ∑ m₃ ∈ idxM M₃, F m₁ m₂ m₃) := by
  have hs := sum_triple_split_g M₁ M₂ M₃ F hM₂
  have hn := sum_triple_neg_eq_pos_g M₁ M₂ M₃ F hF hM₂
  rw [hs, hn]
  ring

end Combinatorics

/-- The `m₂ < 0` half of `Bsumg` equals its `m₂ > 0` half (`BsumgPos`), because the reflection
`(m₁,m₂,m₃) ↦ (-m₁,-m₂,-m₃)` preserves `arg2`, while `idx1 M₁`, `idxM M₂`, `idxM M₃` are each
symmetric under `m ↦ -m`.  Generalises `Work.GM.S3.bsum_reflect`. -/
theorem bsumg_reflect (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hM₂ : 0 < M₂) (v : ℝ) :
    Bsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v = 2 * BsumgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ v := by
  have hF : ∀ m₁ m₂ m₃ : ℤ,
      Rtilde W N B ψ₁ ψ₂ (arg2 (-m₁) (-m₂) (-m₃) v) ^ 2
        = Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v) ^ 2 := by
    intro m₁ m₂ m₃
    rw [arg2_neg m₁ m₂ m₃ v]
  simpa only [Bsumg, BsumgPos] using
    sum_triple_reflect_g M₁ M₂ M₃
      (fun m₁ m₂ m₃ : ℤ => Rtilde W N B ψ₁ ψ₂ (arg2 m₁ m₂ m₃ v) ^ 2) hF hM₂

/-- Pointwise domination of the `m₂ > 0` part of `Bsumg` by `affineSum 2 M₁ M₂ M₃`; the
verbatim generalisation of `Work.GM.S3.bsumPos_le_affineSum` to independent scales in the two
large slots. -/
theorem bsumgPos_le_affineSum (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ ψ' : ℝ → ℝ)
    (hB : 0 ≤ (N : ℝ) * B)
    (hψ₁ : IsBumpAtZero ψ₁ 16) (hψ₂ : IsBumpAtOne ψ₂ 16)
    (hψ' : IsBumpAtOne ψ' 16)
    (hψ'one : ∀ x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8), ψ' x = 1)
    (hRsupp : ∀ x, RtildeSq W N B ψ₁ ψ₂ x ≠ 0 → x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8))
    (v : ℝ) :
    BsumgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ v ≤
      affineSum 2 M₁ M₂ M₃ (testfun N W B ψ₁ ψ₂ ψ') v := by
  have hRnn : ∀ x, 0 ≤ RtildeSq W N B ψ₁ ψ₂ x := fun x =>
    MeasureTheory.integral_nonneg fun u' =>
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
  simp only [BsumgPos, affineSum, idx1, idxMpos, idxM, arg2, hpt]
  refine Finset.sum_le_sum fun m₁ _ => Finset.sum_le_sum fun m₂ _ => ?_
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun m₃ _ _ => htestfun_nn _)

/-- Continuity of `v ↦ BsumgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ v` (a finite sum of squares of `Rtilde`
composed with the affine maps `arg2 m₁ m₂ m₃`).  Generalises `Work.GM.S3.continuous_BsumPos`. -/
theorem continuous_BsumgPos (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ : ℝ → ℝ)
    (hψ₁ : IsBumpAtZero ψ₁ 16) (hψ₂ : IsBumpAtOne ψ₂ 16) :
    Continuous (fun v => BsumgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ v) := by
  have hRt : Continuous (fun x => RtildeSq W N B ψ₁ ψ₂ x) :=
    RtildeSq_continuous W N B 16 ψ₁ ψ₂ hψ₁ hψ₂
  have hRcont : Continuous (fun x => Rtilde W N B ψ₁ ψ₂ x) := by
    have h : (fun x => Rtilde W N B ψ₁ ψ₂ x)
        = fun x => Real.sqrt (RtildeSq W N B ψ₁ ψ₂ x) := rfl
    rw [h]; exact Real.continuous_sqrt.comp hRt
  simp only [BsumgPos]
  refine continuous_finset_sum _ (fun m₁ _ => ?_)
  refine continuous_finset_sum _ (fun m₂ hm₂ => ?_)
  refine continuous_finset_sum _ (fun m₃ _ => ?_)
  have hm2 : (1 : ℤ) ≤ m₂ := (mem_Icc.mp (mem_filter.mp hm₂).1).1
  have hm2ne : ((m₂ : ℤ) : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm2
    linarith
  have harg : Continuous (fun v : ℝ => arg2 m₁ m₂ m₃ v) := by
    simp only [arg2]
    rw [show (fun v : ℝ => ((m₁ : ℝ) * v + (m₃ : ℝ)) / ((m₂ : ℝ)))
        = fun v => ((m₁ : ℝ) * v + (m₃ : ℝ)) * ((m₂ : ℝ))⁻¹ from by
      funext v; rw [div_eq_mul_inv]]
    fun_prop
  exact (hRcont.comp harg).pow 2

/-- Continuity of `u ↦ affineSum 2 M₁ M₂ M₃ (testfun N W B ψ₁ ψ₂ ψ') u`.  Generalises
`Work.GM.S3.continuous_affineSum_testfun`. -/
theorem continuous_affineSumg_testfun (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ)
    (ψ₁ ψ₂ ψ' : ℝ → ℝ)
    (hψ₁ : IsBumpAtZero ψ₁ 16) (hψ₂ : IsBumpAtOne ψ₂ 16) (hψ' : IsBumpAtOne ψ' 16) :
    Continuous (fun u => affineSum 2 M₁ M₂ M₃ (testfun N W B ψ₁ ψ₂ ψ') u) := by
  have hRt : Continuous (fun x => RtildeSq W N B ψ₁ ψ₂ x) :=
    RtildeSq_continuous W N B 16 ψ₁ ψ₂ hψ₁ hψ₂
  have htest : Continuous (fun u => testfun N W B ψ₁ ψ₂ ψ' u) := by
    simp only [testfun]
    exact hψ'.1.continuous.mul hRt
  simp only [affineSum]
  refine continuous_finset_sum _ (fun m₁ _ => ?_)
  refine continuous_finset_sum _ (fun m₂ hm₂ => ?_)
  refine continuous_finset_sum _ (fun m₃ _ => ?_)
  have hm2 : (1 : ℤ) ≤ m₂ := (mem_Icc.mp (mem_filter.mp hm₂).1).1
  have hm2ne : ((m₂ : ℤ) : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm2
    linarith
  have harg : Continuous (fun u : ℝ => (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ))) := by
    rw [show (fun u : ℝ => (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)))
        = fun u => (((m₁ : ℝ) * u + (m₃ : ℝ)) * ((m₂ : ℝ))⁻¹) from by
      funext u; rw [div_eq_mul_inv]]
    fun_prop
  exact htest.comp harg

/-- Compact support of `u ↦ affineSum 2 M₁ M₂ M₃ (testfun N W B ψ₁ ψ₂ ψ') u`: the support is
contained in `[-(11 (M₂ + M₃)), 11 (M₂ + M₃)]`.  Namely `1 ≤ |m₁|`, `1 ≤ m₂ ≤ 2 M₂`,
`|m₃| ≤ 2 M₃` and `(m₁u+m₃)/m₂ ∈ [1/8, 33/8]` on the support, whence
`|m₁u| ≤ (33/8)·2M₂ + 2M₃ ≤ 11(M₂+M₃)` and `|u| ≤ |m₁u|`.  Generalises
`Work.GM.S3.affineSum_testfun_hasCompactSupport`. -/
theorem affineSumg_testfun_hasCompactSupport (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ)
    (ψ₁ ψ₂ ψ' : ℝ → ℝ) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    (hRsupp : ∀ x, RtildeSq W N B ψ₁ ψ₂ x ≠ 0 → x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)) :
    HasCompactSupport (fun u => affineSum 2 M₁ M₂ M₃ (testfun N W B ψ₁ ψ₂ ψ') u) := by
  refine HasCompactSupport.intro
    (K := Set.Icc (-(11 * (M₂ + M₃))) (11 * (M₂ + M₃))) isCompact_Icc (fun u hu => ?_)
  simp only [affineSum]
  refine Finset.sum_eq_zero (fun m₁ hm₁ => ?_)
  refine Finset.sum_eq_zero (fun m₂ hm₂ => ?_)
  refine Finset.sum_eq_zero (fun m₃ hm₃ => ?_)
  refine testfun_eq_zero_of_notMem_support N W B ψ₁ ψ₂ ψ' hRsupp (fun hx => ?_)
  have hm1abs : (1 : ℝ) ≤ |(m₁ : ℝ)| := by
    have h1 : M₁ < |(m₁ : ℝ)| := (mem_filter.mp hm₁).2
    have hne : m₁ ≠ 0 := by
      intro h0
      rw [h0] at h1
      simp at h1
      linarith
    have h2 : (1 : ℤ) ≤ |m₁| := by
      have hpos : (0 : ℤ) < |m₁| := abs_pos.mpr hne
      omega
    have h3 : (1 : ℝ) ≤ ((|m₁| : ℤ) : ℝ) := by exact_mod_cast h2
    rwa [Int.cast_abs] at h3
  have hm2mem : (1 : ℤ) ≤ m₂ := (mem_Icc.mp (mem_filter.mp hm₂).1).1
  have hm2pos : (0 : ℝ) < (m₂ : ℝ) := by
    have : (1 : ℝ) ≤ (m₂ : ℝ) := by exact_mod_cast hm2mem
    linarith
  have hm2le : (m₂ : ℝ) ≤ 2 * M₂ := by
    have h := (mem_Icc.mp (mem_filter.mp hm₂).1).2
    calc (m₂ : ℝ) ≤ (⌊2 * M₂⌋ : ℝ) := by exact_mod_cast h
      _ ≤ 2 * M₂ := Int.floor_le _
  have hm3le : |(m₃ : ℝ)| ≤ 2 * M₃ := by
    have h := mem_Icc.mp hm₃
    have h1' : (-(⌊2 * M₃⌋ : ℝ)) ≤ (m₃ : ℝ) := by exact_mod_cast h.1
    have h2' : (m₃ : ℝ) ≤ (⌊2 * M₃⌋ : ℝ) := by exact_mod_cast h.2
    have hf : (⌊2 * M₃⌋ : ℝ) ≤ 2 * M₃ := Int.floor_le _
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hmain : |(m₁ : ℝ) * u| ≤ 11 * (M₂ + M₃) := by
    have hane : (m₂ : ℝ) ≠ 0 := ne_of_gt hm2pos
    have hxa : ((m₁ : ℝ) * u + (m₃ : ℝ)) =
        (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) * (m₂ : ℝ) :=
      (div_mul_cancel₀ _ hane).symm
    have hb : (m₁ : ℝ) * u =
        (((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) * (m₂ : ℝ) - (m₃ : ℝ) := by
      rw [← hxa]; ring
    rw [hb]
    have hxabs : |(((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ))| ≤ 33 / 8 := by
      rw [abs_le]; exact ⟨by linarith [hx.1], hx.2⟩
    have h2abs : |(m₂ : ℝ)| = (m₂ : ℝ) := abs_of_pos hm2pos
    calc |(((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) * (m₂ : ℝ) - (m₃ : ℝ)|
        ≤ |(((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ)) * (m₂ : ℝ)| + |(m₃ : ℝ)| := abs_sub _ _
      _ = |(((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ))| * |(m₂ : ℝ)| + |(m₃ : ℝ)| := by
          rw [abs_mul]
      _ ≤ (33 / 8) * (2 * M₂) + 2 * M₃ := by
          have h4 : |(((m₁ : ℝ) * u + (m₃ : ℝ)) / (m₂ : ℝ))| * |(m₂ : ℝ)| ≤
              (33 / 8) * (2 * M₂) := by
            rw [h2abs]
            exact mul_le_mul hxabs hm2le (le_of_lt hm2pos) (by norm_num)
          linarith
      _ ≤ 11 * (M₂ + M₃) := by nlinarith [hM₂, hM₃]
  have hu' : u ∈ Set.Icc (-(11 * (M₂ + M₃))) (11 * (M₂ + M₃)) := by
    have habs : |u| ≤ 11 * (M₂ + M₃) := by
      have h1 : |(m₁ : ℝ) * u| = |(m₁ : ℝ)| * |u| := abs_mul _ _
      have h2 : |u| ≤ |(m₁ : ℝ)| * |u| := by
        have h3 : (0 : ℝ) ≤ |u| := abs_nonneg u
        nlinarith [hm1abs, h3]
      linarith [h1 ▸ hmain]
    rw [abs_le] at habs
    exact habs
  exact hu hu'

/-- **GM 10.1, reduction of `S₃,₄` to an affine sum, with two independent large scales.**
With `f = testfun N W B ψ₁ ψ₂ ψ'` (i.e. `f u = ψ' u · R̃²(u)`), and `Rtilde² = RtildeSq`,

`S₃,₄ = ∫_{1/2}^2 (Σ_m R̃(a₂(m,v))²)² dv ≤ 4 ∫_ℝ (affineSum 2 M₁ M₂ M₃ f)²`,

the verbatim generalisation of `Work.GM.S3.S34_le_affine`. -/
theorem S34g_le_affine (N : ℕ) (W : Finset ℝ) (B M₁ M₂ M₃ : ℝ) (ψ₁ ψ₂ ψ' : ℝ → ℝ)
    (hB : 0 ≤ (N : ℝ) * B) (hM₁ : 0 < M₁) (hM₂ : 0 < M₂) (hM₃ : 0 < M₃)
    (hψ₁ : Work.GM.S3.IsBumpAtZero ψ₁ 16) (hψ₂ : Work.GM.S3.IsBumpAtOne ψ₂ 16)
    (hψ' : Work.GM.S3.IsBumpAtOne ψ' 16)
    (hψ'one : ∀ x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8), ψ' x = 1)
    (hRsupp : ∀ x, Work.GM.S3.RtildeSq W N B ψ₁ ψ₂ x ≠ 0 →
      x ∈ Set.Icc (1 / 8 : ℝ) (33 / 8)) :
    Work.GM.S3.Gen.S34g N W B M₁ M₂ M₃ ψ₁ ψ₂ ≤
      4 * ∫ u, (Submission.GM.affineSum 2 M₁ M₂ M₃
        (Work.GM.S3.testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by
  have hReflect : ∀ v, Bsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v =
      2 * BsumgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ v :=
    fun v => bsumg_reflect N W B M₁ M₂ M₃ ψ₁ ψ₂ hM₂ v
  have hPoint : ∀ v, BsumgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ v ≤
      affineSum 2 M₁ M₂ M₃ (testfun N W B ψ₁ ψ₂ ψ') v :=
    fun v => bsumgPos_le_affineSum N W B M₁ M₂ M₃ ψ₁ ψ₂ ψ' hB hψ₁ hψ₂ hψ' hψ'one hRsupp v
  have hPcont : Continuous (fun v => BsumgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ v) :=
    continuous_BsumgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ hψ₁ hψ₂
  have hGcont : Continuous (fun u => affineSum 2 M₁ M₂ M₃ (testfun N W B ψ₁ ψ₂ ψ') u) :=
    continuous_affineSumg_testfun N W B M₁ M₂ M₃ ψ₁ ψ₂ ψ' hψ₁ hψ₂ hψ'
  have hGcs : HasCompactSupport (fun u =>
      affineSum 2 M₁ M₂ M₃ (testfun N W B ψ₁ ψ₂ ψ') u) :=
    affineSumg_testfun_hasCompactSupport N W B M₁ M₂ M₃ ψ₁ ψ₂ ψ' hM₁ hM₂ hM₃ hRsupp
  have hGcs2 : HasCompactSupport (fun u =>
      (affineSum 2 M₁ M₂ M₃ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hGcs ⊢
    filter_upwards [hGcs] with u hu
    simp [hu]
  have hGint : Integrable (fun u =>
      (affineSum 2 M₁ M₂ M₃ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2) volume :=
    (hGcont.pow 2).integrable_of_hasCompactSupport hGcs2
  have hPnneg : ∀ v, 0 ≤ BsumgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ v := by
    intro v
    simp only [BsumgPos]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
      Finset.sum_nonneg (fun k _ => sq_nonneg _)))
  -- Step 1: `S₃,₄ = 4 ∫_{1/2}^2 (BsumgPos v)² dv`
  have h1 : S34g N W B M₁ M₂ M₃ ψ₁ ψ₂ =
      4 * ∫ v in (1 / 2 : ℝ)..2, (BsumgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ v) ^ 2 := by
    rw [S34g]
    have heq : (fun v => (Bsumg N W B M₁ M₂ M₃ ψ₁ ψ₂ v) ^ 2)
        = fun v => 4 * (BsumgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ v) ^ 2 := by
      funext v; rw [hReflect v]; ring
    rw [heq, intervalIntegral.integral_const_mul]
  -- Step 2: `∫_{1/2}^2 (BsumgPos)² ≤ ∫_ℝ (affineSum f)²`
  have h2 : ∫ v in (1 / 2 : ℝ)..2, (BsumgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ v) ^ 2 ≤
      ∫ u, (affineSum 2 M₁ M₂ M₃ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by
    have hmono : ∫ v in (1 / 2 : ℝ)..2, (BsumgPos N W B M₁ M₂ M₃ ψ₁ ψ₂ v) ^ 2 ≤
        ∫ v in (1 / 2 : ℝ)..2,
          (affineSum 2 M₁ M₂ M₃ (testfun N W B ψ₁ ψ₂ ψ') v) ^ 2 := by
      refine intervalIntegral.integral_mono_on (by norm_num) ?_ ?_ (fun v _ => ?_)
      · exact (hPcont.pow 2).intervalIntegrable _ _
      · exact (hGcont.pow 2).intervalIntegrable _ _
      · exact pow_le_pow_left₀ (hPnneg v) (hPoint v) 2
    have hle : ∫ v in (1 / 2 : ℝ)..2,
          (affineSum 2 M₁ M₂ M₃ (testfun N W B ψ₁ ψ₂ ψ') v) ^ 2 ≤
        ∫ u, (affineSum 2 M₁ M₂ M₃ (testfun N W B ψ₁ ψ₂ ψ') u) ^ 2 := by
      rw [intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)]
      exact setIntegral_le_integral hGint
        (Filter.Eventually.of_forall (fun u => sq_nonneg _))
    linarith
  rw [h1]
  linarith

end Work.GM.S3.Gen
