import Mathlib
import Submission.Work.KMTAreas.A7.adm_of_bump
import Submission.Work.KMTAreas.A7.variationalNorm_intervalIntegral_eLpNorm_le
import Submission.Work.KMTPlan.A6.LowSmallAux
import Submission.Work.KMTPlan.A6.Tm_randSymb_eq
import Submission.Work.KMTAreas.A7.varphitildeNt_support_all
import Submission.Work.KMTPlan.A6.Tm_bdd_of_l2
import Submission.Work.KMTPlan.A6.Tm_l2_bdd
import Submission.Work.KMTPlan.A6.exists_bound_BtwistEx_crude
import Submission.Work.KMTPlan.A6.lacunaryScaleBound
import Submission.Work.KMTPlan.A6.lowSmall_crude_bound
import Submission.Work.KMTPlan.A6.variationalNorm_le_VrFull
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-!
# The ingredient lemmas of the assembly of `Work.KMTPlan.A6.lowSmallModelVar`, in importable form

Verbatim copies (with the declarations renamed by an `A` suffix and the import of the target file
replaced by `LowSmallAux`) of the lemmas
`lowModelSlice_crude`, `TmSide_lowSymbF`, `TmSide_lowSymbG`, `Tm_lowSymbF_bdd`,
`slice_le_of_VrBound`, `lowModelVar_boundedL`, which are proved but live in modules that import
the target file - hence cannot be used *inside* it.  The target theorem of this run cannot be
written without them, so they are gathered here.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7

/-! ## The crude `ℓ¹` bound for the `t`-slices of the small-scale model tuple

The slice `lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n` of the small-scale model tuple is either
`0` (off the admissible set `lowSmallSet`) or the single-scale expression

`B^{l₁,l₂,m_Ẑ}_{m_*}(T^{l₁}_{φ_{N,t}}f, T^{l₂}_{φ̃_{N,t}}g)`, `N = ⌊a n⌋`, `m_* = η_{≤-2u}⊗η_{≤-2du}`.

Uniformly over a *bounded* range of quadruples (`lcL l₁ l₂ k₁ k₂ ≤ B`) and over all `a, n, t`, the
`ℓ¹` norm of that expression is at most `C(B,ρ,P) ‖f‖₂‖g‖₂`, with a constant that does not use any
gain:

* on `lowSmallSet` one has `N ≤ splitCut ρ B` (`splitCut_mono_local`), so the two symbols
  `φ_{N,k₁,t}`, `φ̃_{N,k₂,t}` range over the *finite* rectangle `N ≤ splitCut ρ B`, `k ≤ B`; the
  `ℓ¹` masses of the kernels of `T^{l_i}` are bounded there by a single constant `Ctm`
  (`tmKer_mass_bound`), whence the `ℓ²` bounds `‖T^{l_i}_{φ}f‖₂ ≤ Ctm ‖f‖₂`;
* the twisted bilinear multiplier is bounded crudely in `ℓ² × ℓ² → ℓ¹` by a constant depending only
  on `ρ, P, l₁, l₂` (`exists_bound_BtwistEx_crude`); taking the maximum over the finitely many
  pairs `(l₁,l₂)` with `l₁,l₂ ≤ B` makes it uniform in the quadruple. -/

/-- **The `(2,2,1)`-bookkeeping identity** for the constant: the product of the three `ofReal`
factors can be reassembled into one. -/
private lemma ofReal_three_mul {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (X Y : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * X) * (ENNReal.ofReal c * Y)
      = ENNReal.ofReal (a * b * c) * (X * Y) := by
  have h1 : ENNReal.ofReal (a * b * c)
      = ENNReal.ofReal a * ENNReal.ofReal b * ENNReal.ofReal c := by
    rw [show a * b * c = (a * b) * c from rfl, ENNReal.ofReal_mul (mul_nonneg ha hb),
      ENNReal.ofReal_mul ha]
  rw [h1]
  ring

theorem lowModelSlice_crudeA (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) (t : ℝ) (f g : ℤ → ℂ),
      Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (Work.KMTPlan.A6.lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n)
        1 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  -- the uniform `ℓ¹`-mass bound for the kernels of the exact-height multipliers on the rectangle
  obtain ⟨Ctm, hCtmpos, hCtm⟩ :=
    tmKer_mass_bound P ρ hρ hρ1 B (Work.KMTAreas.A7.splitCut ρ B)
  -- the uniform crude constant of the twisted bilinear multiplier over the rectangle of pairs
  set Rect : Finset (ℕ × ℕ) := (Finset.range (B + 1)).product (Finset.range (B + 1)) with hRect
  have hRectne : Rect.Nonempty := by
    rw [hRect]
    exact ⟨(0, 0), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩⟩
  set Cb : ℕ × ℕ → ℝ :=
    fun p => Classical.choose (exists_bound_BtwistEx_crude ρ P p.1 p.2) with hCbdef
  set CB : ℝ := Rect.sup' hRectne Cb with hCBdef
  have hCBmem : ∀ p ∈ Rect, Cb p ≤ CB := by
    intro p hp
    have h := Finset.le_sup' (s := Rect) (f := Cb) hp
    rwa [hCBdef]
  have hRect00 : ((0 : ℕ), (0 : ℕ)) ∈ Rect := by
    rw [hRect]
    exact Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  have hCB0 : 0 ≤ CB :=
    le_trans (Classical.choose_spec (exists_bound_BtwistEx_crude ρ P 0 0)).1
      (hCBmem (0, 0) hRect00)
  have hCbspec : ∀ p : ℕ × ℕ, ∀ (u : ℕ) (h k : ℤ → ℂ),
      eLpNorm (fun x : ℤ => BtwistEx ρ P p.1 p.2 (mStarF u) (mStargF P.natDegree u) h k x)
        1 Measure.count
        ≤ ENNReal.ofReal (Cb p) * eLpNorm h 2 Measure.count
            * eLpNorm k 2 Measure.count :=
    fun p => (Classical.choose_spec (exists_bound_BtwistEx_crude ρ P p.1 p.2)).2
  refine ⟨CB * Ctm * Ctm + 1, by positivity, ?_⟩
  intro a l₁ l₂ k₁ k₂ n t f g hlc ht hf hg
  -- the four height bounds
  have hl₁ : l₁ ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlc
  have hl₂ : l₂ ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlc
  have hk₁ : k₁ ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hlc
  have hk₂ : k₂ ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hlc
  have hpair : (l₁, l₂) ∈ Rect := by
    rw [hRect]
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩
  by_cases hset : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n
  · -- on the admissible set the slice is the single-scale model expression
    have hNK : Nat.floor (a n) ≤ Work.KMTAreas.A7.splitCut ρ B :=
      le_trans hset.2 (splitCut_mono_local ρ hρ.le hlc)
    -- the `ℓ²` bound for the two exact-height multipliers
    have hTm1 : eLpNorm (Tm ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f) 2 Measure.count
        ≤ ENNReal.ofReal Ctm * eLpNorm f 2 Measure.count := by
      obtain ⟨hsum1, hle1⟩ := hCtm.1 l₁ k₁ (Nat.floor (a n)) t hl₁ hk₁ hNK ht
      rw [Tm_eq_convOp]
      have hstep := Work.Analysis.Hilbert.eLpNorm_conv_count_le (p := 2) (by norm_num)
        (tmKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t)) f
      rw [ENNReal.ofReal_ofNat] at hstep
      refine hstep.trans ?_
      have hof : (∑' z : ℤ,
            ENNReal.ofReal ‖tmKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) z‖)
          = ENNReal.ofReal (∑' z : ℤ,
              ‖tmKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) z‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun z => norm_nonneg _) hsum1).symm
      rw [hof]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hle1) le_rfl
    have hTm2 : eLpNorm (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) 2
        Measure.count ≤ ENNReal.ofReal Ctm * eLpNorm g 2 Measure.count := by
      obtain ⟨hsum2, hle2⟩ := hCtm.2 l₂ k₂ (Nat.floor (a n)) t hl₂ hk₂ hNK ht
      rw [Tm_eq_convOp]
      have hstep := Work.Analysis.Hilbert.eLpNorm_conv_count_le (p := 2) (by norm_num)
        (tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)) g
      rw [ENNReal.ofReal_ofNat] at hstep
      refine hstep.trans ?_
      have hof : (∑' z : ℤ, ENNReal.ofReal
            ‖tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) z‖)
          = ENNReal.ofReal (∑' z : ℤ,
              ‖tmKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) z‖) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun z => norm_nonneg _) hsum2).symm
      rw [hof]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal hle2) le_rfl
    -- the slice is the single-scale model expression
    have hslice : lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n
        = fun x : ℤ => BtwistEx ρ P l₁ l₂
            (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))
            (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂)))
            (Tm ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f)
            (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g) x := by
      funext x
      simp only [lowModelSlice, hset, if_true]
    rw [hslice]
    refine (hCbspec (l₁, l₂) (uScale ρ (lcL l₁ l₂ k₁ k₂))
      (Tm ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t) f)
      (Tm ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t) g)).trans ?_
    refine (mul_le_mul' (mul_le_mul' (ENNReal.ofReal_le_ofReal (hCBmem (l₁, l₂) hpair)) hTm1)
      hTm2).trans ?_
    calc ENNReal.ofReal CB
          * (ENNReal.ofReal Ctm * eLpNorm f 2 Measure.count)
          * (ENNReal.ofReal Ctm * eLpNorm g 2 Measure.count)
        = ENNReal.ofReal (CB * Ctm * Ctm)
            * (eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count) :=
          ofReal_three_mul hCB0 hCtmpos.le hCtmpos.le _ _
      _ ≤ ENNReal.ofReal (CB * Ctm * Ctm + 1)
            * (eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count) :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
      _ = ENNReal.ofReal (CB * Ctm * Ctm + 1) * eLpNorm f 2 Measure.count
            * eLpNorm g 2 Measure.count := (mul_assoc _ _ _).symm
  · -- off the admissible set the slice vanishes
    have hzpt : ∀ x : ℤ, lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x = 0 := by
      intro x
      simp only [lowModelSlice, hset, if_false]
    have hz : lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n = 0 := funext hzpt
    rw [hz, eLpNorm_zero]
    exact bot_le

end

end Work.KMTPlan.A6


namespace Work.KMTPlan.A6

open scoped BigOperators

/-! ## `TmSide` for the `f`-side bump family `lowSymbF`

The bookkeeping predicate `TmSide ρ l K Φ` of `lowSmallModelVar` is exactly the `ℓ²`-form
admissibility `Adm2 (diffFreqs ρ l) (Φ k)` (`Tm_randSymb_eq.lean`), required for the members
`Φ k`, `k ∈ {0,…,K}`, of the symbol family.  Here `Φ = lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t`, whose `k`-th
member is either `0` (for `k = 0`, or off the small-scale index set `lowSmallSet`) or the modulated
KMT bump `varphiNt (⌊a k⌋) k₁ t`.

The bump facts are the analytic content: every `varphiNt N k t` is `C²` with compact support
(`contDiff_varphiNt`, `hasCompactSupport_varphiNt`), hence admissible in the `ℓ¹` sense
(`adm_of_bump`); the `ℓ²` form needed by `TmSide` follows because the squares of a summable
nonnegative family are summable. -/

/-- A nonnegative summable family of norms has summable squares (the terms are eventually `≤ 1`,
and in any case dominated by `(∑ ‖κ j‖ + 1) ‖κ j‖`). -/
lemma summable_sq_of_summable_norm {ι : Type*} {κ : ι → ℂ}
    (h : Summable fun j => ‖κ j‖) : Summable fun j => ‖κ j‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_)
    (h.mul_left ((∑' j, ‖κ j‖) + 1))
  calc ‖κ j‖ ^ 2 = ‖κ j‖ * ‖κ j‖ := sq _
    _ ≤ ((∑' j, ‖κ j‖) + 1) * ‖κ j‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        exact (h.le_tsum j (fun i _ => norm_nonneg _)).trans (le_add_of_nonneg_right zero_le_one)

/-- **`ℓ²`-admissibility of the modulated KMT bump** at the exact-height frequency set. -/
lemma adm2_varphiNt (ρ : ℝ) (l N k : ℕ) (t : ℝ) :
    Adm2 (Work.KMTAreas.A7.diffFreqs ρ l) (Work.KMTAreas.A7.varphiNt N k t) := by
  obtain ⟨h1, h2, h3⟩ := Work.KMTAreas.A7.adm_of_bump
    (A := Work.KMTAreas.A7.diffFreqs ρ l) (F := Work.KMTAreas.A7.varphiNt N k t)
    (Work.KMTAreas.A7.contDiff_varphiNt N k t)
    (Work.KMTAreas.A7.hasCompactSupport_varphiNt N k t)
  exact ⟨h1, h2, summable_sq_of_summable_norm h3⟩

/-- The zero symbol is `ℓ²`-admissible as soon as any symbol is. -/
lemma adm2_zero {A : Finset Work.Analysis.IonescuWainger.Circle} {φ : ℝ → ℂ}
    (h : Adm2 A φ) : Adm2 A (0 : ℝ → ℂ) := by
  have h0 := h.const_mul (0 : ℂ)
  have hfun : (fun ξ => (0 : ℂ) * φ ξ) = (0 : ℝ → ℂ) := by funext ξ; simp
  rwa [hfun] at h0

/-- **Every member of the `f`-side bump family `lowSymbF` is `ℓ²`-admissible** at the
exact-height frequency set of the first scale. -/
lemma adm2_lowSymbF (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (k : ℕ) :
    Adm2 (Work.KMTAreas.A7.diffFreqs ρ l₁) (lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k) := by
  by_cases hk : k = 0
  · have h0 : lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k = 0 := by
      rw [hk]; exact lowSymbF_zero ρ C₀ a l₁ l₂ k₁ k₂ t
    rw [h0]
    exact adm2_zero (adm2_varphiNt ρ l₁ 0 k₁ t)
  · by_cases h : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k
    · have h1 : lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k
          = Work.KMTAreas.A7.varphiNt (Nat.floor (a k)) k₁ t := by
        funext ξ; simp [lowSymbF, hk, h]
      rw [h1]
      exact adm2_varphiNt ρ l₁ (Nat.floor (a k)) k₁ t
    · have h1 : lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k = 0 := by
        funext ξ; simp [lowSymbF, hk, h]
      rw [h1]
      exact adm2_zero (adm2_varphiNt ρ l₁ 0 k₁ t)

theorem TmSide_lowSymbFA (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) :
    Work.KMTPlan.A6.TmSide ρ l₁ K (Work.KMTPlan.A6.lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) := by
  refine ⟨fun k _ x => (adm2_lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k).1 x,
    fun k _ => (adm2_lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k).2.1,
    fun k _ => (adm2_lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k).2.2⟩

end Work.KMTPlan.A6


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-! ## Local facts about the modulated `d`-fold bump `φ̃_{N,t}`

The small-scale model tuple of `lowSmallModelVar` uses the second KMT bump
`φ̃_{N,t} = varphitildeN d N k t` (with `d = P.natDegree`) as the `g`-side symbol.  The side
conditions of `TmSide` (periodised-translate summability, integrability of the
Ionescu--Wainger symbol of the periodisation, and quadratic decay of its kernel) are the same
ones used for `φ_{N,t}` in `Work.KMTAreas.A7.varphiNt_IW_facts`; we record the few elementary
facts about `φ̃_{N,t}` that are needed here, proved directly from the definitions, so that this
module depends only on its declared imports. -/

/-- The `d`-fold bump `φ̃_N` is pointwise bounded by `2` (it is a difference of two rescalings
of the cutoff `η`, each of modulus at most `1`). -/
theorem norm_varphitildeN_le_two_local (d N k : ℕ) (x : ℝ) :
    ‖Work.KMTAreas.A7.varphitildeN d N k x‖ ≤ 2 := by
  rw [Work.KMTAreas.A7.varphitildeN]
  split_ifs with hk
  · exact le_trans (Work.KMTContract.norm_kmtEta_le _) (by norm_num)
  · calc ‖Work.KMTContract.kmtEta _ - Work.KMTContract.kmtEta _‖
        ≤ ‖Work.KMTContract.kmtEta _‖ + ‖Work.KMTContract.kmtEta _‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (Work.KMTContract.norm_kmtEta_le _)
          (Work.KMTContract.norm_kmtEta_le _)
      _ = 2 := by norm_num

/-- The `d`-fold bump `φ̃_N` is `C²`. -/
theorem contDiff_varphitildeN_local (d N k : ℕ) :
    ContDiff ℝ 2 (Work.KMTAreas.A7.varphitildeN d N k) := by
  rw [Work.KMTAreas.A7.varphitildeN]
  split_ifs with hk
  · exact (Work.KMTAreas.A7.contDiff_kmtEta 2).comp (contDiff_const.mul contDiff_id)
  · exact ((Work.KMTAreas.A7.contDiff_kmtEta 2).comp (contDiff_const.mul contDiff_id)).sub
      ((Work.KMTAreas.A7.contDiff_kmtEta 2).comp (contDiff_const.mul contDiff_id))

/-- The modulated `d`-fold bump `φ̃_{N,t}` is pointwise bounded by `2`. -/
theorem norm_varphitildeNt_le_two_local (P : Polynomial ℤ) (d N k : ℕ) (t ξ : ℝ) :
    ‖Work.KMTAreas.A7.varphitildeNt P d N k t ξ‖ ≤ 2 := by
  rw [Work.KMTAreas.A7.varphitildeNt, norm_mul, Work.KMTAreas.A7.norm_ee, mul_one]
  exact norm_varphitildeN_le_two_local d N k ξ

/-- The modulated `d`-fold bump `φ̃_{N,t}` is `C²` (the modulation is a smooth nowhere vanishing
factor). -/
theorem contDiff_varphitildeNt_local (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    ContDiff ℝ 2 (Work.KMTAreas.A7.varphitildeNt P d N k t) := by
  rw [show Work.KMTAreas.A7.varphitildeNt P d N k t
      = fun ξ : ℝ => Work.KMTAreas.A7.varphitildeN d N k ξ *
          Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (contDiff_varphitildeN_local d N k).mul
    (Work.KMTAreas.A7.contDiff_ee_const_mul 2 (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)))

/-- The modulated `d`-fold bump `φ̃_{N,t}` has compact support (the modulation is nowhere
vanishing, so the support is that of `φ̃_N`, which is contained in a fixed interval). -/
theorem hasCompactSupport_varphitildeNt_local (P : Polynomial ℤ) (d N k : ℕ) (t : ℝ) :
    HasCompactSupport (Work.KMTAreas.A7.varphitildeNt P d N k t) := by
  refine HasCompactSupport.of_support_subset_isCompact (K :=
    Set.Icc (-((2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))))
      ((2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))))) isCompact_Icc ?_
  intro x hx
  exact abs_le.mp (Work.KMTAreas.A7.varphitildeNt_support_all P d N k t x hx)

/-! ## The side conditions for a single bump -/

/-- A function vanishing off `[-R, R]` has summable integer translates at every point: only the
finitely many integers in `[-⌈|x| + R⌉, ⌈|x| + R⌉]` can contribute. -/
theorem summable_shift_of_support_le {F : ℝ → ℂ} {R : ℝ}
    (hF0 : ∀ x : ℝ, R < |x| → F x = 0) (x : ℝ) :
    Summable fun j : ℤ => F (x + (j : ℝ)) := by
  set K : ℕ := Nat.ceil (|x| + R) with hKdef
  refine summable_of_ne_finset_zero (s := Finset.Icc (-(K : ℤ)) (K : ℤ)) (fun j hj => ?_)
  by_contra hne
  have hmem : |x + (j : ℝ)| ≤ R := by
    by_contra h
    exact hne (hF0 _ (lt_of_not_ge h))
  have hKle : |x| + R ≤ (K : ℝ) := by
    rw [hKdef]; exact Nat.le_ceil _
  have hj' : |(j : ℝ)| ≤ (K : ℝ) := by
    calc |(j : ℝ)| = |(x + (j : ℝ)) + (-x)| := by ring_nf
      _ ≤ |x + (j : ℝ)| + |-x| := abs_add_le _ _
      _ = |x + (j : ℝ)| + |x| := by rw [abs_neg]
      _ ≤ R + |x| := by linarith
      _ = |x| + R := by ring
      _ ≤ (K : ℝ) := hKle
  have habs : (|j| : ℤ) ≤ (K : ℤ) := by
    rw [← Int.cast_le (R := ℝ), Int.cast_abs]
    exact_mod_cast hj'
  exact absurd (abs_le.mp habs) (by simpa [Finset.mem_Icc] using hj)

/-- **The three `TmSide` conditions for a single bump.**  A measurable function `F`, vanishing
off `[-R, R]` and bounded by `C`, which is `C²` with compact support, satisfies: its translates
are summable, the Ionescu--Wainger symbol of its periodisation (over the exact-height frequencies
`diffFreqs ρ l`) is integrable on the circle, and the kernel of that symbol is square summable. -/
theorem tmSide_of_bump (ρ : ℝ) (l : ℕ) (F : ℝ → ℂ) (R C : ℝ) (hR : 0 ≤ R) (hmeas : Measurable F)
    (hF0 : ∀ x : ℝ, R < |x| → F x = 0) (hFC : ∀ x : ℝ, ‖F x‖ ≤ C)
    (hcd : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) :
    (∀ x : ℝ, Summable fun j : ℤ => F (x + (j : ℝ))) ∧
    MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet
      (Work.KMTAreas.A7.diffFreqs ρ l) (Work.Analysis.IonescuWainger.periodize F))
      Work.Analysis.IonescuWainger.circleMeasure ∧
    Summable fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize F)) j‖ ^ 2 := by
  refine ⟨fun x => summable_shift_of_support_le hF0 x, ?_, ?_⟩
  · exact (Work.Analysis.IWMultiplier.memLp_iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
      (Work.Analysis.IonescuWainger.memLp_periodize (R := R) (C := C) hmeas hR hF0
        hFC)).integrable le_top
  · set S : ℝ := max (∫ y, ‖F y‖) (∫ y, ‖iteratedDeriv 2 F y‖) with hSdef
    have hSnn : 0 ≤ S := le_trans (integral_nonneg (fun y => norm_nonneg _)) (le_max_left _ _)
    have hS1 : (∫ y, ‖F y‖) ≤ S := by rw [hSdef]; exact le_max_left _ _
    have hS2 : (∫ y, ‖iteratedDeriv 2 F y‖) ≤ S := by rw [hSdef]; exact le_max_right _ _
    have hdec : ∀ j : ℤ, ‖Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize F)) j‖
        ≤ (4 * (((Work.KMTAreas.A7.diffFreqs ρ l).card : ℝ) * S) + 1)
            * ‖Work.KMTAreas.A7.kmtKernWeight j‖ :=
      fun j => Work.KMTAreas.A7.iwKernel_decay_of_bump (Work.KMTAreas.A7.diffFreqs ρ l)
        hcd hcs (S := S) hSnn hS1 hS2 j
    have hW : Summable fun j : ℤ => ‖Work.KMTAreas.A7.kmtKernWeight j‖ ^ 2 := by
      refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_)
        Work.KMTAreas.A7.summable_kmtKernWeight
      have h1 : ‖Work.KMTAreas.A7.kmtKernWeight j‖ ≤ 1 := by
        rw [Work.KMTAreas.A7.norm_kmtKernWeight, div_le_one (by positivity)]
        nlinarith [abs_nonneg (j : ℝ)]
      calc ‖Work.KMTAreas.A7.kmtKernWeight j‖ ^ 2
          = ‖Work.KMTAreas.A7.kmtKernWeight j‖ * ‖Work.KMTAreas.A7.kmtKernWeight j‖ := by ring
        _ ≤ ‖Work.KMTAreas.A7.kmtKernWeight j‖ * 1 :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = ‖Work.KMTAreas.A7.kmtKernWeight j‖ := by ring
    refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_)
      (hW.mul_left ((4 * (((Work.KMTAreas.A7.diffFreqs ρ l).card : ℝ) * S) + 1) ^ 2))
    calc ‖Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize F)) j‖ ^ 2
        ≤ ((4 * (((Work.KMTAreas.A7.diffFreqs ρ l).card : ℝ) * S) + 1)
            * ‖Work.KMTAreas.A7.kmtKernWeight j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hdec j) 2
      _ = (4 * (((Work.KMTAreas.A7.diffFreqs ρ l).card : ℝ) * S) + 1) ^ 2
            * ‖Work.KMTAreas.A7.kmtKernWeight j‖ ^ 2 := by ring

/-! ## The target -/

/-- **The side conditions for the `g`-side bump family of the small-scale model tuple.**  The
family `n ↦ lowSymbG … n` is supported on the small-scale indices and equals the modulated
`d`-fold bump `φ̃_{⌊a n⌋,t}` there; each of its members satisfies the three Ionescu--Wainger
side conditions of `TmSide` (the zero members trivially, via `tmSide_of_bump` at the zero
function). -/
theorem TmSide_lowSymbGA (P : Polynomial ℤ) (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ)
    (t : ℝ) :
    Work.KMTPlan.A6.TmSide ρ l₂ K (Work.KMTPlan.A6.lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) := by
  let Rn : ℕ → ℝ := fun n => (2 : ℝ) ^ ((P.natDegree : ℝ) *
    ((k₂ : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ)))
  have hRn_def : ∀ n : ℕ, Rn n = (2 : ℝ) ^ ((P.natDegree : ℝ) *
      ((k₂ : ℝ) - (Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℝ))) := fun n => rfl
  have key : ∀ k ∈ Finset.range (K + 1),
      (∀ x : ℝ, Summable fun j : ℤ =>
        Work.KMTPlan.A6.lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k (x + (j : ℝ))) ∧
      MeasureTheory.Integrable (Work.Analysis.IonescuWainger.iwSymbolSet
        (Work.KMTAreas.A7.diffFreqs ρ l₂)
        (Work.Analysis.IonescuWainger.periodize
          (Work.KMTPlan.A6.lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k)))
        Work.Analysis.IonescuWainger.circleMeasure ∧
      Summable fun j : ℤ => ‖Work.Analysis.IWMultiplier.iwKernel
        (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l₂)
          (Work.Analysis.IonescuWainger.periodize
            (Work.KMTPlan.A6.lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k))) j‖ ^ 2 := by
    intro k _
    by_cases hk0 : k = 0
    · have hF : Work.KMTPlan.A6.lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k
          = fun _ : ℝ => (0 : ℂ) := by
        funext ξ
        simp only [Work.KMTPlan.A6.lowSymbG, hk0, if_true]
      rw [hF]
      exact tmSide_of_bump ρ l₂ (fun _ : ℝ => (0 : ℂ)) 0 0 le_rfl measurable_const
        (fun x _ => rfl) (fun x => by simp) contDiff_const HasCompactSupport.zero
    · by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k
      · have hF : Work.KMTPlan.A6.lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k
            = Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a k)) k₂ t := by
          funext ξ
          simp only [Work.KMTPlan.A6.lowSymbG, hk0, if_false, hls, if_true]
        rw [hF]
        refine tmSide_of_bump ρ l₂
          (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a k)) k₂ t)
          (Rn k) 2 ?_ ?_ ?_ ?_ ?_ ?_
        · rw [hRn_def k]; positivity
        · exact (contDiff_varphitildeNt_local P P.natDegree (Nat.floor (a k)) k₂ t)
            |>.continuous.measurable
        · intro x hx
          by_contra hne
          have hsupp := Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree
            (Nat.floor (a k)) k₂ t x hne
          rw [← hRn_def k] at hsupp
          exact absurd hx (not_lt.mpr hsupp)
        · intro x
          exact norm_varphitildeNt_le_two_local P P.natDegree (Nat.floor (a k)) k₂ t x
        · exact contDiff_varphitildeNt_local P P.natDegree (Nat.floor (a k)) k₂ t
        · exact hasCompactSupport_varphitildeNt_local P P.natDegree (Nat.floor (a k)) k₂ t
      · have hF : Work.KMTPlan.A6.lowSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k
            = fun _ : ℝ => (0 : ℂ) := by
          funext ξ
          simp only [Work.KMTPlan.A6.lowSymbG, hk0, if_false, hls, if_false]
        rw [hF]
        exact tmSide_of_bump ρ l₂ (fun _ : ℝ => (0 : ℂ)) 0 0 le_rfl measurable_const
          (fun x _ => rfl) (fun x => by simp) contDiff_const HasCompactSupport.zero
  refine ⟨fun k hk => (key k hk).1, fun k hk => (key k hk).2.1, fun k hk => (key k hk).2.2⟩

end

end Work.KMTPlan.A6


namespace Work.KMTPlan.A6

open MeasureTheory

/-- **The modulated bump `φ_{N,t}` is a legitimate `ℓ²`-to-`ℓ^∞` symbol for an *arbitrary* real
`t`.**  This is the unrestricted-`t` version of `Work.KMTAreas.A7.varphiNt_bounds`, whose
constants are uniform only on `t ∈ [1/2,1]`: here the bound `S` on the `L¹` norms of `φ_{N,t}` and
of `(φ_{N,t})''` is allowed to depend on `t`, which is all the pointwise bound on `Tm` needs.
Smoothness and compact support hold for every `t`
(`Work.KMTAreas.A7.contDiff_varphiNt`, `Work.KMTAreas.A7.hasCompactSupport_varphiNt`), and the
two integrals are finite real numbers. -/
theorem exists_varphiNt_bound (N k : ℕ) (t : ℝ) :
    ∃ S : ℝ, 0 ≤ S ∧
      ContDiff ℝ 2 (Work.KMTAreas.A7.varphiNt N k t) ∧
      HasCompactSupport (Work.KMTAreas.A7.varphiNt N k t) ∧
      (∫ y : ℝ, ‖Work.KMTAreas.A7.varphiNt N k t y‖) ≤ S ∧
      (∫ y : ℝ, ‖iteratedDeriv 2 (Work.KMTAreas.A7.varphiNt N k t) y‖) ≤ S := by
  refine ⟨(∫ y : ℝ, ‖Work.KMTAreas.A7.varphiNt N k t y‖)
      + (∫ y : ℝ, ‖iteratedDeriv 2 (Work.KMTAreas.A7.varphiNt N k t) y‖) + 1,
    ?_, Work.KMTAreas.A7.contDiff_varphiNt N k t,
    Work.KMTAreas.A7.hasCompactSupport_varphiNt N k t, ?_, ?_⟩
  · have h1 : 0 ≤ ∫ y : ℝ, ‖Work.KMTAreas.A7.varphiNt N k t y‖ :=
      integral_nonneg fun y => norm_nonneg _
    have h2 : 0 ≤ ∫ y : ℝ, ‖iteratedDeriv 2 (Work.KMTAreas.A7.varphiNt N k t) y‖ :=
      integral_nonneg fun y => norm_nonneg _
    linarith
  · have h2 : 0 ≤ ∫ y : ℝ, ‖iteratedDeriv 2 (Work.KMTAreas.A7.varphiNt N k t) y‖ :=
      integral_nonneg fun y => norm_nonneg _
    linarith
  · have h1 : 0 ≤ ∫ y : ℝ, ‖Work.KMTAreas.A7.varphiNt N k t y‖ :=
      integral_nonneg fun y => norm_nonneg _
    linarith

/-- **Pointwise boundedness of `Tm` at the small-scale slices of the low case.**

For each index `k` the `f`-side symbol `lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k` is either
`0` (at `k = 0`, and off the admissible set `lowSmallSet`) or the modulated bump
`φ_{⌊a k⌋,t}` of the paper's §6.  In both cases `Tm ρ l₁ · f` is a bounded function of `y`:

* in the degenerate case the symbol vanishes, so the multiplier vanishes
  (`Work.KMTPlan.A6.Tm_zero`);
* otherwise `Tm_l2_bdd`/`Tm_bdd_of_l2` bounds `Tm ρ l₁ φ f` pointwise by
  `C · ‖f‖_{ℓ²}`, since `φ = φ_{⌊a k⌋,t}` is a `C²` compactly supported symbol with finite
  `L¹` norms of itself and of its second derivative (`exists_varphiNt_bound`). -/
theorem Tm_lowSymbF_bddA (P : Polynomial ℤ) (ρ : ℝ) (l₁ : ℕ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count) :
    ∀ k : ℕ, ∃ D : ℝ, ∀ y : ℤ,
      ‖Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTPlan.A6.lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k) f y‖ ≤ D := by
  intro k
  obtain ⟨S, hSnn, hcd, hcs, hA, hB⟩ := exists_varphiNt_bound (Nat.floor (a k)) k₁ t
  by_cases hk0 : k = 0
  · -- the symbol vanishes at the anchor `k = 0`
    have hs : lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k = 0 := by
      funext ξ; simp [lowSymbF, hk0]
    refine ⟨0, fun y => ?_⟩
    rw [hs, Tm_zero ρ l₁ f hf]
    simp
  · by_cases hls : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ k
    · -- the symbol is the modulated bump `φ_{⌊a k⌋,t}`
      have hs : lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k
          = Work.KMTAreas.A7.varphiNt (Nat.floor (a k)) k₁ t := by
        funext ξ; simp [lowSymbF, hk0, hls]
      obtain ⟨C, _hCnn, hC⟩ := Tm_bdd_of_l2 ρ l₁ S hSnn
      refine ⟨C * Real.sqrt (∑' j : ℤ, ‖f j‖ ^ 2), fun y => ?_⟩
      rw [hs]
      exact hC (Work.KMTAreas.A7.varphiNt (Nat.floor (a k)) k₁ t) hcd hcs hA hB f hf y
    · -- the symbol vanishes off the admissible set
      have hs : lowSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k = 0 := by
        funext ξ; simp [lowSymbF, hk0, hls]
      refine ⟨0, fun y => ?_⟩
      rw [hs, Tm_zero ρ l₁ f hf]
      simp

end Work.KMTPlan.A6


namespace Work.KMTPlan.A6

/-!
# Slicing the low-case model variational estimate

This file contains the (purely measure-theoretic) step that converts a *pointwise* bound of the
variational norm of a single slice `n ↦ lowModelSlice ... t n x` by the `VrFull 2 K`-norm of the
family of single-scale pieces `k ↦ lowSliceA ... t k x` plus twice the `n = 0` value, into an
`ℒ¹(ℤ)` bound.

The only content is the triangle inequality (Minkowski) for `eLpNorm`, applied to
`ℝ≥0∞`-valued functions on `(ℤ, counting measure)`, where every function is measurable.
-/

open MeasureTheory

open scoped ENNReal NNReal

/-- Pointwise monotonicity of `eLpNorm` for `ℝ≥0∞`-valued functions on `(ℤ, count)`.  Stated with
both function types fixed, so that the (otherwise stuck) `ContinuousENorm` instance of the general
Mathlib lemma is determined. -/
private lemma eLpNorm_le_of_le_int (A B : ℤ → ℝ≥0∞) (h : ∀ x, A x ≤ B x) :
    eLpNorm A 1 MeasureTheory.Measure.count ≤ eLpNorm B 1 MeasureTheory.Measure.count := by
  have hae : ∀ᵐ x ∂MeasureTheory.Measure.count, ‖A x‖ₑ ≤ (1 : ℝ≥0) * ‖B x‖ₑ := by
    filter_upwards with x
    simpa using h x
  have h' := MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm)
    (μ := MeasureTheory.Measure.count) (f := A) (g := B) (c := 1) hae 1
  simpa [ENNReal.smul_def, smul_eq_mul] using h'

/-- Minkowski's inequality for `ℝ≥0∞`-valued functions on `(ℤ, count)`. -/
private lemma eLpNorm_add_le_int (A B : ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => A x + B x) 1 MeasureTheory.Measure.count
      ≤ eLpNorm A 1 MeasureTheory.Measure.count + eLpNorm B 1 MeasureTheory.Measure.count :=
  MeasureTheory.eLpNorm_add_le le_rfl

/-- Homogeneity of `eLpNorm` for `ℝ≥0∞`-valued functions on `(ℤ, count)` and the constant `2`. -/
private lemma eLpNorm_two_mul_le_int (B : ℤ → ℝ≥0∞) :
    eLpNorm (fun x : ℤ => (2 : ℝ≥0∞) * B x) 1 MeasureTheory.Measure.count
      ≤ 2 * eLpNorm B 1 MeasureTheory.Measure.count := by
  have hae : ∀ᵐ x ∂MeasureTheory.Measure.count,
      ‖(2 : ℝ≥0∞) * B x‖ₑ ≤ (2 : ℝ≥0) * ‖B x‖ₑ := by
    filter_upwards with x
    simp
  have h := MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm)
    (μ := MeasureTheory.Measure.count) (f := fun x : ℤ => (2 : ℝ≥0∞) * B x) (g := B)
    (c := 2) hae 1
  simpa [ENNReal.smul_def, smul_eq_mul] using h

/-- The variational norm of the slice family is bounded, in `ℒ¹(ℤ)`, by the `VrFull`-norm of the
single-scale family plus twice the initial slice.  This is the measure-theoretic (Minkowski) step
of the low case of area A6. -/
theorem slice_le_of_VrBoundA (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (r : NNReal) (K : ℕ) (C1 C2 : ENNReal)
    (hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => Work.KMTPlan.A6.lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)
      ≤ Work.Analysis.Variation.VrFull 2 K
          (fun k : ℕ => Work.KMTPlan.A6.lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t k x)
        + 2 * ENNReal.ofReal ‖Work.KMTPlan.A6.lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖)
    (hVr : MeasureTheory.eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 K
        (fun k : ℕ => Work.KMTPlan.A6.lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t k x))
        1 MeasureTheory.Measure.count ≤ C1)
    (hspike : MeasureTheory.eLpNorm (fun x : ℤ =>
        ENNReal.ofReal ‖Work.KMTPlan.A6.lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖)
        1 MeasureTheory.Measure.count ≤ C2) :
    Work.KMTPlan.A6.LowSliceVarNorm ρ P C₀ a f g l₁ l₂ k₁ k₂ t r ≤ C1 + 2 * C2 := by
  rw [LowSliceVarNorm]
  have hslice : ∀ x : ℤ,
      ‖PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)‖ₑ
      ≤ ‖Work.Analysis.Variation.VrFull 2 K
            (fun k : ℕ => lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t k x)
          + 2 * ENNReal.ofReal ‖lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖‖ₑ := by
    intro x
    simpa using hpt x
  have h1 : eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x))
        1 MeasureTheory.Measure.count
      ≤ eLpNorm (fun x : ℤ =>
          Work.Analysis.Variation.VrFull 2 K
              (fun k : ℕ => lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t k x)
            + 2 * ENNReal.ofReal
                ‖lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖)
        1 MeasureTheory.Measure.count :=
    eLpNorm_le_of_le_int _ _ hslice
  have h2 : eLpNorm (fun x : ℤ =>
          Work.Analysis.Variation.VrFull 2 K
              (fun k : ℕ => lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t k x)
            + 2 * ENNReal.ofReal
                ‖lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖)
        1 MeasureTheory.Measure.count
      ≤ eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 K
            (fun k : ℕ => lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t k x))
          1 MeasureTheory.Measure.count
        + eLpNorm (fun x : ℤ => (2 : ℝ≥0∞) * ENNReal.ofReal
            ‖lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖)
          1 MeasureTheory.Measure.count :=
    eLpNorm_add_le_int _ _
  have h3 : eLpNorm (fun x : ℤ => (2 : ℝ≥0∞) * ENNReal.ofReal
        ‖lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖)
        1 MeasureTheory.Measure.count
      ≤ 2 * eLpNorm (fun x : ℤ =>
          ENNReal.ofReal ‖lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖)
          1 MeasureTheory.Measure.count :=
    eLpNorm_two_mul_le_int _
  calc eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x))
        1 MeasureTheory.Measure.count
      ≤ eLpNorm (fun x : ℤ =>
          Work.Analysis.Variation.VrFull 2 K
              (fun k : ℕ => lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t k x)
            + 2 * ENNReal.ofReal
                ‖lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖)
        1 MeasureTheory.Measure.count := h1
    _ ≤ eLpNorm (fun x : ℤ => Work.Analysis.Variation.VrFull 2 K
            (fun k : ℕ => lowSliceA ρ P C₀ a f g l₁ l₂ k₁ k₂ t k x))
          1 MeasureTheory.Measure.count
        + eLpNorm (fun x : ℤ => (2 : ℝ≥0∞) * ENNReal.ofReal
            ‖lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖)
          1 MeasureTheory.Measure.count := h2
    _ ≤ C1 + 2 * eLpNorm (fun x : ℤ =>
          ENNReal.ofReal ‖lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t 0 x‖)
          1 MeasureTheory.Measure.count := add_le_add hVr h3
    _ ≤ C1 + 2 * C2 := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hspike (by norm_num : (0 : ℝ≥0∞) ≤ 2))

end Work.KMTPlan.A6


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

/-!
# The bounded-height case of the small-scale model tuple

`Work.KMTPlan.A6.lowModelVar_boundedLA` is the *crude* form of the small-scale (`§7`) model
estimate `Work.KMTPlan.A6.lowSmallModelVar`, restricted to the finitely many quadruples
`(l₁,l₂,k₁,k₂)` with `lcL l₁ l₂ k₁ k₂ ≤ B`: for a bounded range of heights no gain is needed and
the `ℓ¹(ℤ; V^r)`-norm of the model tuple is bounded by `C(Λ) ‖f‖₂ ‖g‖₂`.

The proof has three elementary ingredients (compare `A6/lowSmallBoundedL.lean`, which is the same
statement for the concrete columns `colSmall`):

* **Finiteness of the scale set.**  On the admissible set `lowSmallSet` one has
  `⌊a n⌋ ≤ splitCut ρ (lcL …) ≤ splitCut ρ B`, and a `Λ`-lacunary sequence with `a n ≥ 1` exceeds
  that threshold after `lowIdxBA ρ B Λ` indices; hence every `t`-slice family is supported in
  `Finset.range (lowIdxBA ρ B Λ)`, a set of cardinality depending only on `Λ` (and `ρ`, `B`).
* **The single-scale crude bound.**  `Work.KMTPlan.A6.lowModelSlice_crudeA` bounds each member of
  each slice family by `Ccr ‖f‖₂ ‖g‖₂`, uniformly in the quadruple, the scale `n`, the time `t`
  and the functions.
* **The bookkeeping.**  `(varsum)` in its finitely supported form
  (`eLpNorm_variationalNorm_le_sum`) bounds the `ℓ¹`-norm of the variational norm of a slice
  family by the sum of the `ℓ¹`-norms of its members; the time integral is then handled by
  `Work.KMTAreas.A7.variationalNorm_intervalIntegral_eLpNorm_le`, and the loss is absorbed into
  the constant `C(Λ)` (the weight `lcWeight c …` is bounded below by `2^{-|c|B}` on the finite
  range of heights).
-/

/-- **Monotonicity of the scale split.**  `splitCut ρ L = 2^{2^{⌊2^{2ρL}⌋}}` is monotone in the
height `L` for `ρ ≥ 0`. -/
theorem lowModelVar_splitCut_monoA (ρ : ℝ) (hρ : 0 ≤ ρ) :
    Monotone (Work.KMTAreas.A7.splitCut ρ) := by
  intro L M hLM
  have h1 : Work.Analysis.EndVar.scaleCount 1 ρ L ≤ Work.Analysis.EndVar.scaleCount 1 ρ M :=
    Work.KMTAreas.A7.ExcSupport.scaleCount_mono 1 hρ hLM
  exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) h1)

/-- **The index bound of a lacunary sequence.**  After `lowIdxBA ρ B Λ` indices a `Λ`-lacunary
sequence `a` with `a n ≥ 1` certainly exceeds the threshold `splitCut ρ B`; this is the elementary
part of `lacunaryScaleBound` with the threshold fixed once and for all. -/
noncomputable def lowIdxBA (ρ : ℝ) (B : ℕ) (Λ : NNReal) : ℕ :=
  Nat.ceil (((Work.KMTAreas.A7.splitCut ρ B : ℝ) + 1) / Real.logb 2 ((Λ : NNReal) : ℝ)) + 1

/-- The weight `2^{-c·L}` is the `rpow` of the height `lcL`. -/
lemma lcWeight_eq_rpow_lcLA (c : ℝ) (l₁ l₂ k₁ k₂ : ℕ) :
    lcWeight c l₁ l₂ k₁ k₂ = (2 : ℝ) ^ (-(c * (lcL l₁ l₂ k₁ k₂ : ℝ))) := by
  rw [lcWeight, ← lcL_eq, Int.cast_natCast]

/-- **The weight is bounded below on a bounded range of heights.**  If
`lcL l₁ l₂ k₁ k₂ ≤ B` then `2^{-|c|B} ≤ lcWeight c l₁ l₂ k₁ k₂`. -/
lemma pow_neg_abs_le_lcWeightA (c : ℝ) {B : ℕ} {l₁ l₂ k₁ k₂ : ℕ}
    (h : lcL l₁ l₂ k₁ k₂ ≤ B) :
    (2 : ℝ) ^ (-(|c| * (B : ℝ))) ≤ lcWeight c l₁ l₂ k₁ k₂ := by
  rw [lcWeight_eq_rpow_lcLA]
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  have hL0 : (0 : ℝ) ≤ (lcL l₁ l₂ k₁ k₂ : ℝ) := Nat.cast_nonneg _
  have hLB : (lcL l₁ l₂ k₁ k₂ : ℝ) ≤ (B : ℝ) := by exact_mod_cast h
  have h1 : c * (lcL l₁ l₂ k₁ k₂ : ℝ) ≤ |c| * (lcL l₁ l₂ k₁ k₂ : ℝ) :=
    mul_le_mul_of_nonneg_right (le_abs_self c) hL0
  have h2 : |c| * (lcL l₁ l₂ k₁ k₂ : ℝ) ≤ |c| * (B : ℝ) :=
    mul_le_mul_of_nonneg_left hLB (abs_nonneg c)
  linarith

theorem lowModelVar_boundedLA (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (B : ℕ) (c : ℝ) :
    ∃ C : NNReal → NNReal, ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      (∀ n : ℕ, AEMeasurable (fun p : ℝ × ℤ =>
          Work.KMTPlan.A6.lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ p.1 n p.2)
        (MeasureTheory.Measure.prod MeasureTheory.volume MeasureTheory.Measure.count)) →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTPlan.A6.lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
        1 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * ENNReal.ofReal (Work.KMTPlan.A6.lcWeight c l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  -- the crude single-scale bound for the `t`-slices
  obtain ⟨Ccr, hCcrpos, hCcr⟩ := lowModelSlice_crudeA P hd ρ hρ hρ1 C₀ hC₀ B
  -- the minimal weight on the bounded range of heights
  set wmin : ℝ := (2 : ℝ) ^ (-(|c| * (B : ℝ))) with hwmindef
  have hwminpos : 0 < wmin := Real.rpow_pos_of_pos (by norm_num) _
  -- the constant
  let Cc : NNReal → NNReal := fun Λ =>
    ⟨max (((lowIdxBA ρ B Λ : ℝ) * 4 * Ccr) / wmin) 1,
      le_trans zero_le_one (le_max_right _ _)⟩
  have hCcval : ∀ Λ : NNReal, (Cc Λ : ℝ) = max (((lowIdxBA ρ B Λ : ℝ) * 4 * Ccr) / wmin) 1 :=
    fun Λ => rfl
  refine ⟨Cc, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hlc hf hg hX
  have hρ0 : 0 ≤ ρ := le_of_lt hρ
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_of_le_of_lt (by norm_num) hr)
  have hwle : wmin ≤ lcWeight c l₁ l₂ k₁ k₂ := by
    rw [hwmindef]
    exact pow_neg_abs_le_lcWeightA c hlc
  -- the family is supported in the first `lowIdxBA ρ B Λ` scales
  have hsupp : ∀ t : ℝ, ∀ n : ℕ, n ∉ Finset.range (lowIdxBA ρ B Λ) →
      (fun x : ℤ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x) = 0 := by
    intro t n hn
    have hn' : lowIdxBA ρ B Λ ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    have hnot : ¬ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n := by
      intro hsm
      have h1 : Nat.floor (a n) ≤ Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) := hsm.2
      have h2 : Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) ≤ Work.KMTAreas.A7.splitCut ρ B :=
        lowModelVar_splitCut_monoA ρ hρ0 hlc
      have hgt : Work.KMTAreas.A7.splitCut ρ B < Nat.floor (a n) :=
        lacunaryScaleBound Λ hΛ a ha ha1 (Work.KMTAreas.A7.splitCut ρ B) n hn'
      exact absurd (le_trans h1 h2) (not_le.mpr hgt)
    funext x
    simp only [lowModelSlice, hnot, if_false, Pi.zero_apply]
  -- the bound on the constant of the bookkeeping
  set Csum : ENNReal := (lowIdxBA ρ B Λ : ENNReal) *
      (4 * (ENNReal.ofReal Ccr *
        (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count))) with hCsumdef
  -- the per-`t` bound
  have hbound : ∀ t ∈ Set.Icc ((1 : ℝ) / 2) 1, MeasureTheory.eLpNorm (fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x))
      1 MeasureTheory.Measure.count ≤ Csum := by
    intro t ht
    refine (Submission.PointwiseErgodicTheorems.eLpNorm_variationalNorm_le_sum (r := r) (p := 1)
      hr1 le_rfl (u := fun n : ℕ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n)
      (s := Finset.range (lowIdxBA ρ B Λ)) (hsupp t)
      (fun n _ => (measurable_of_countable
        (fun x : ℤ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)).aestronglyMeasurable)).trans ?_
    have h1 : ∑ n ∈ Finset.range (lowIdxBA ρ B Λ),
          4 * MeasureTheory.eLpNorm
            (fun x : ℤ => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)
            1 MeasureTheory.Measure.count
        ≤ ∑ _n ∈ Finset.range (lowIdxBA ρ B Λ),
          4 * (ENNReal.ofReal Ccr * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) :=
      Finset.sum_le_sum fun n _ =>
        mul_le_mul' le_rfl (hCcr a l₁ l₂ k₁ k₂ n t f g hlc ht hf hg)
    refine h1.trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hCsumdef]
    ring
  -- the `t`-integral
  have hfinal : MeasureTheory.eLpNorm (fun x : ℤ =>
      PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∫ t in ((1 : ℝ) / 2)..1,
          lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x))
      1 MeasureTheory.Measure.count ≤ Csum :=
    Work.KMTAreas.A7.variationalNorm_intervalIntegral_eLpNorm_le r hr1 1 le_rfl
      (fun t n x => lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x) Csum (fun n => hX n) hbound
  have heq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∫ t in ((1 : ℝ) / 2)..1,
          lowModelSlice ρ P C₀ a f g l₁ l₂ k₁ k₂ t n x)) := by
    funext x
    congr 1
    funext n
    exact lowModel_eq_integral_slice ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
  rw [heq]
  refine hfinal.trans ?_
  -- the constant comparison
  have hkey : (lowIdxBA ρ B Λ : ENNReal) * 4 * ENNReal.ofReal Ccr
      ≤ (Cc Λ : ENNReal) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂) := by
    have hxc : (0 : ℝ) ≤ ((lowIdxBA ρ B Λ : ℝ) * 4 * Ccr) / wmin :=
      div_nonneg (by positivity) hwminpos.le
    have hmax : ((lowIdxBA ρ B Λ : ℝ) * 4 * Ccr) / wmin ≤ (Cc Λ : ℝ) := by
      rw [hCcval Λ]; exact le_max_left _ _
    have hstep1 : ENNReal.ofReal (((lowIdxBA ρ B Λ : ℝ) * 4 * Ccr) / wmin)
        ≤ (Cc Λ : ENNReal) := by
      rw [← ENNReal.ofReal_coe_nnreal]
      exact ENNReal.ofReal_le_ofReal hmax
    have hstep2 : ENNReal.ofReal wmin ≤ ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂) :=
      ENNReal.ofReal_le_ofReal hwle
    have hstep3 := mul_le_mul' hstep1 hstep2
    have heq1 : ENNReal.ofReal (((lowIdxBA ρ B Λ : ℝ) * 4 * Ccr) / wmin)
          * ENNReal.ofReal wmin
        = ENNReal.ofReal ((lowIdxBA ρ B Λ : ℝ) * 4 * Ccr) := by
      rw [← ENNReal.ofReal_mul hxc,
        div_mul_cancel₀ _ (ne_of_gt hwminpos)]
    have heq2 : ENNReal.ofReal ((lowIdxBA ρ B Λ : ℝ) * 4 * Ccr)
        = (lowIdxBA ρ B Λ : ENNReal) * 4 * ENNReal.ofReal Ccr := by
      rw [show (lowIdxBA ρ B Λ : ℝ) * 4 * Ccr = ((lowIdxBA ρ B Λ : ℝ) * 4) * Ccr from rfl,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
    rw [← heq2, ← heq1]
    exact hstep3
  calc Csum
      = ((lowIdxBA ρ B Λ : ENNReal) * 4 * ENNReal.ofReal Ccr)
          * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := by
        rw [hCsumdef]; ring
    _ ≤ ((Cc Λ : ENNReal) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂))
          * (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) :=
        mul_le_mul' hkey le_rfl
    _ = (Cc Λ : ENNReal) * ENNReal.ofReal (lcWeight c l₁ l₂ k₁ k₂)
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
        (mul_assoc _ _ _).symm

end

end Work.KMTPlan.A6

