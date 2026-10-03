/-
# The small scales of the low case of area A6 are bounded on a bounded range of indices

`Work.KMTPlan.A6.colSmall` is the small-scale part of the §5 columns of the low case
(`k₁ = 0 ∨ k₂ = 0`) of Krause--Mirek--Tao's Theorem `varp`, i.e. the clamped columns

  `n ↦ 1_{N(a n) ∈ I^{max(l₁,l₂),k₁,k₂}} 1_{N(a n) ≤ splitCut ρ L} Ã_{N(a n)}(F^{0,l₁,k₁}f, G^{0,l₂,k₂}g)`

(where `N(a n) = ⌊a n⌋`, `L = max(max l₁ l₂)(max k₁ k₂)`).

**This module proves `lowSmallBoundedL`**: for *fixed* quadruples (`lcL l₁ l₂ k₁ k₂ ≤ B`,
so that only `(B+1)^4` quadruples occur) the `ℓ¹(ℤ; V^r)` norm of the small-scale family is
bounded by `C(Λ) ‖f‖₂ ‖g‖₂` — no gain, but a constant uniform in the quadruple, in the lacunary
sequence `a` and in the functions.

The proof has three ingredients.

* **Finiteness of the scale set.**  `splitCut ρ L ≤ splitCut ρ B = K`, and a `Λ`-lacunary
  sequence with `a n ≥ 1` exceeds `K` after `⌈(K+1)/log₂ Λ⌉ + 1` indices; so the family
  `n ↦ colSmall … n` is supported in `Finset.range (lowIndexBound Λ K)`, a set of cardinality
  depending only on `Λ` (and `ρ`, `B`).  This is `lacunaryScaleBound`.
* **The single scale bound.**  On the support, each column is a single halved average
  `Ã_N(F,G)` of the §5 pieces, so `(anf)` at `q = 1`, `q₁ = q₂ = 2`
  (`Work.KMTPlan.A6.eLpNorm_varpCol_le`) gives `‖column‖_{ℓ¹} ≤ ‖F‖₂ ‖G‖₂`; the `ℓ²` norms of
  the pieces are bounded by `pieceL2BoundRect`, uniformly over the finite rectangle of heights
  `l ≤ B₀`, `κ ∈ [-KB,KB]` determined by `N ≤ K`.
* **The bookkeeping.**  `(varsum)` in its finitely supported form
  (`eLpNorm_variationalNorm_le_sum`) reduces the `ℓ¹(ℤ;V^r)` norm of the family to the sum of the
  `ℓ¹` norms of its members, and the arithmetic lemma `tsum_const_le_mul` turns the sum of
  `lowIndexBound Λ K` identical terms into the constant `C(Λ)`.

Nothing here uses the number theory of areas A1/A4: the two hypothesis `hA1`, `hI` are kept
because the caller of `lowSmallBoundedL` has them at hand.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowSmallDefs
import Submission.Work.KMTPlan.A6.pieceL2BoundRect
import Submission.Work.KMTPlan.A6.lacunaryScaleBound
import Submission.Work.KMTAreas.A7.ExceptionalSupport

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.KMTContract

/-! ## The number of scales below a threshold -/

/-- The number of indices after which a `Λ`-lacunary sequence with `a n ≥ 1` certainly exceeds
the threshold `K`: `⌈(K+1)/log₂ Λ⌉ + 1` (see `lacunaryScaleBound`). -/
noncomputable def lowIndexBound (Λ : NNReal) (K : ℕ) : ℕ :=
  Nat.ceil (((K : ℝ) + 1) / Real.logb 2 (Λ : ℝ)) + 1

/-! ## Two elementary bookkeeping lemmas -/

/-- The small-scale threshold `splitCut ρ L = 2^{2^{⌊2^{2ρL}⌋}}` is monotone in the height `L`
(for `ρ ≥ 0`). -/
private theorem splitCut_mono (ρ : ℝ) (hρ : 0 ≤ ρ) : Monotone (Work.KMTAreas.A7.splitCut ρ) := by
  intro L M hLM
  have h1 : scaleCount 1 ρ L ≤ scaleCount 1 ρ M :=
    Work.KMTAreas.A7.ExcSupport.scaleCount_mono 1 hρ hLM
  exact Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) h1)

/-- A constant family of `nB` terms of size `4 · M · X` is bounded by `Kc · X`, provided
`nB · 4M ≤ Kc`.  This is the arithmetic of the finitely supported `(varsum)` bound. -/
theorem tsum_const_le_mul {Kc : NNReal} (nB : ℕ) (M : ℝ) (X : ENNReal)
    (hK : (nB : ℝ) * (4 * M) ≤ (Kc : ℝ)) :
    (nB : ENNReal) * (4 * (ENNReal.ofReal M * X)) ≤ (Kc : ENNReal) * X := by
  have h4 : ENNReal.ofReal (4 * M) = 4 * ENNReal.ofReal M := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 4), ENNReal.ofReal_ofNat]
  calc (nB : ENNReal) * (4 * (ENNReal.ofReal M * X))
      = ENNReal.ofReal (nB : ℝ) * (ENNReal.ofReal (4 * M) * X) := by
        rw [← ENNReal.ofReal_natCast (nB), h4]; ring
    _ = (ENNReal.ofReal (nB : ℝ) * ENNReal.ofReal (4 * M)) * X := by ring
    _ = ENNReal.ofReal ((nB : ℝ) * (4 * M)) * X := by
        rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (nB : ℝ))]
    _ ≤ ENNReal.ofReal ((Kc : ℝ)) * X := mul_le_mul' (ENNReal.ofReal_le_ofReal hK) le_rfl
    _ = (Kc : ENNReal) * X := by rw [ENNReal.ofReal_coe_nnreal]

/-! ## The main theorem -/

/-- **The small-scale family of the low case is bounded on a bounded range of quadruples.**

For every `B` there is `C : ℝ≥0 → ℝ≥0` such that for every `Λ`-lacunary sequence `a` with
`a n ≥ 1` and every low-case quadruple with `lcL l₁ l₂ k₁ k₂ ≤ B`, the `ℓ¹(ℤ;V^r)` norm of the
small-scale columns is at most `C Λ ‖f‖₂ ‖g‖₂`. -/
theorem lowSmallBoundedL (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (B : ℕ) :
    ∃ C : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → (k₁ = 0 ∨ k₂ = 0) →
      MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ B →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTPlan.A6.colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
        1 MeasureTheory.Measure.count
        ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_of_le_of_lt (by norm_num) hr)
  have hρ0 : 0 ≤ ρ := le_of_lt hρ
  -- the common scale threshold, and the rectangle of heights allowed by it
  set K : ℕ := Work.KMTAreas.A7.splitCut ρ B with hKdef
  set B₀ : ℕ := heightScale C₀ K + (logN K).toNat with hB₀def
  set KB : ℕ := (P.natDegree + 1) * (B₀ + 2) + 2 with hKBdef
  -- the uniform `ℓ²` bound for the continuous frequency pieces
  obtain ⟨Cρ, hCρpos, hCρ⟩ := pieceL2BoundRect ρ B₀ KB
  set Cq : NNReal := Cρ * Cρ with hCqdef
  -- the constant of the estimate
  set Kc : NNReal → NNReal := fun Λ => ⟨max ((lowIndexBound Λ K : ℝ) * (4 * (Cq : ℝ))) 1,
    le_trans zero_le_one (le_max_right _ 1)⟩ with hKcdef
  refine ⟨Kc, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 _hQ hf hg hlcLB
  have hsplit_mono : Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) ≤ K := by
    rw [hKdef]
    exact splitCut_mono ρ hρ0 hlcLB
  have hKcval : (lowIndexBound Λ K : ℝ) * (4 * (Cq : ℝ)) ≤ (Kc Λ : ℝ) := by
    rw [hKcdef]
    exact le_max_left _ 1
  have hB₀KB : B₀ + 1 ≤ KB := by rw [hKBdef]; nlinarith
  -- the family is supported in the first `lowIndexBound Λ K` scales
  have hsupp : ∀ n : ℕ, n ∉ Finset.range (lowIndexBound Λ K) →
      (fun x : ℤ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
    intro n hn
    have hn' : lowIndexBound Λ K ≤ n := by simpa only [Finset.mem_range, not_lt] using hn
    have hgt : K < Nat.floor (a n) := by
      simp only [lowIndexBound] at hn'
      exact lacunaryScaleBound Λ hΛ a ha ha1 K n hn'
    funext x
    show colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0
    rw [colSmall_apply, if_neg (not_le.mpr (lt_of_le_of_lt hsplit_mono hgt))]
  -- the two frequencies of the `F`-piece lie in the rectangle
  have hfreqF : ∀ (N k : ℕ), logN N ≤ (B₀ : ℤ) → k ≤ B₀ →
      (-(logN N) + (k : ℤ)) ∈ Finset.Icc (-(KB : ℤ)) (KB : ℤ) ∧
        (-(logN N) + ((k : ℤ) - 1)) ∈ Finset.Icc (-(KB : ℤ)) (KB : ℤ) := by
    intro N k hlog hk
    have h0 : 0 ≤ logN N := logN_nonneg N
    have h1 : (B₀ : ℤ) ≤ (KB : ℤ) := by exact_mod_cast (by omega : B₀ ≤ KB)
    simp only [Finset.mem_Icc]
    constructor <;> omega
  -- the two frequencies of the `G`-piece lie in the rectangle
  have hfreqG : ∀ (N k : ℕ), logN N ≤ (B₀ : ℤ) → k ≤ B₀ →
      ((P.natDegree : ℤ) * (-(logN N) + (k : ℤ))) ∈ Finset.Icc (-(KB : ℤ)) (KB : ℤ) ∧
        ((P.natDegree : ℤ) * (-(logN N) + ((k : ℤ) - 1))) ∈ Finset.Icc (-(KB : ℤ)) (KB : ℤ) := by
    intro N k hlog hk
    have h0 : 0 ≤ logN N := logN_nonneg N
    have hd : 0 ≤ (P.natDegree : ℤ) := Int.natCast_nonneg _
    have hkR : (k : ℤ) ≤ (B₀ : ℤ) := by exact_mod_cast hk
    have hdB : (P.natDegree : ℤ) * (B₀ : ℤ) ≤ (KB : ℤ) := by
      have : P.natDegree * B₀ ≤ KB := by rw [hKBdef]; nlinarith
      exact_mod_cast this
    have hdB' : (P.natDegree : ℤ) * ((B₀ : ℤ) + 1) ≤ (KB : ℤ) := by
      have : P.natDegree * (B₀ + 1) ≤ KB := by rw [hKBdef]; nlinarith
      exact_mod_cast this
    simp only [Finset.mem_Icc]
    constructor
    · constructor
      · nlinarith [mul_le_mul_of_nonneg_left (show -(logN N) ≥ -(B₀ : ℤ) by omega) hd,
          mul_le_mul_of_nonneg_left hkR hd, hdB, hdB']
      · nlinarith [mul_le_mul_of_nonneg_left hkR hd, mul_le_mul_of_nonneg_left h0 hd, hdB,
          mul_le_mul_of_nonneg_left (show (0:ℤ) ≤ (k:ℤ) by omega) hd]
    · constructor
      · nlinarith [mul_le_mul_of_nonneg_left (show -(logN N) ≥ -(B₀ : ℤ) by omega) hd,
          mul_le_mul_of_nonneg_left (show (0:ℤ) ≤ (k:ℤ) by omega) hd, hdB, hdB']
      · nlinarith [mul_le_mul_of_nonneg_left hkR hd, hdB]
  -- the single scale bound for the columns on the support
  have hterm : ∀ n ∈ Finset.range (lowIndexBound Λ K),
      eLpNorm (fun x : ℤ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count
        ≤ (Cq : ENNReal) * (eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count) := by
    intro n hn
    by_cases hclamp : Nat.floor (a n) ≤ Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂)
    · by_cases hidx : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
      · have hNB : Nat.floor (a n) ≤ K := le_trans hclamp hsplit_mono
        obtain ⟨hl₁, hl₂, hk₁, hk₂⟩ :=
          (inIndexSet_iff_le (C₀ := C₀) (l₁ := l₁) (l₂ := l₂) (k₁ := k₁) (k₂ := k₂)
            (N := Nat.floor (a n))).mp hidx
        have hle₀ : heightScale C₀ (Nat.floor (a n)) ≤ B₀ := by
          rw [hB₀def]; exact le_trans (heightScale_mono C₀ hNB) (Nat.le_add_right _ _)
        have hl₁B : l₁ ≤ B₀ := le_trans hl₁ hle₀
        have hl₂B : l₂ ≤ B₀ := le_trans hl₂ hle₀
        have hk₁B : k₁ ≤ B₀ := le_trans hk₁ hle₀
        have hk₂B : k₂ ≤ B₀ := le_trans hk₂ hle₀
        have hlog : logN (Nat.floor (a n)) ≤ (B₀ : ℤ) := by
          have h1 : logN (Nat.floor (a n)) ≤ logN K := logN_mono hNB
          have h2 : logN K ≤ (B₀ : ℤ) := by
            rw [hB₀def]
            push_cast
            have h3 : logN K ≤ ((logN K).toNat : ℤ) := Int.self_le_toNat _
            have h4 : (0:ℤ) ≤ (heightScale C₀ K : ℤ) := by positivity
            omega
          linarith
        have hFb : eLpNorm (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f) 2 Measure.count
            ≤ (Cρ : ENNReal) * eLpNorm f 2 Measure.count := by
          have h := hCρ l₁ (fun s : ℤ => -(logN (Nat.floor (a n))) + s) 0 (k₁ : ℤ) f hl₁B
            (hfreqF _ _ hlog hk₁B).1 (hfreqF _ _ hlog hk₁B).2
          simpa only [Fpiece_eq, Nat.cast_zero, neg_zero] using h
        have hGb : eLpNorm (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ)
              (Nat.floor (a n)) g) 2 Measure.count
            ≤ (Cρ : ENNReal) * eLpNorm g 2 Measure.count := by
          have h := hCρ l₂ (fun s : ℤ => (P.natDegree : ℤ) * (-(logN (Nat.floor (a n))) + s))
            0 (k₂ : ℤ) g hl₂B (hfreqG _ _ hlog hk₂B).1 (hfreqG _ _ hlog hk₂B).2
          simpa only [Gpiece_eq, Nat.cast_zero, neg_zero] using h
        have hFmem : MemLp (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f) 2 Measure.count :=
          MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hFb (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.eLpNorm_lt_top))
        have hGmem : MemLp (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ)
              (Nat.floor (a n)) g) 2 Measure.count :=
          MeasureTheory.memLp_iff.mpr (lt_of_le_of_lt hGb (ENNReal.mul_lt_top ENNReal.coe_lt_top hg.eLpNorm_lt_top))
        have heq : (fun x : ℤ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
            = (fun x : ℤ => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x) := by
          funext x
          rw [colSmall_apply, if_pos hclamp]
        rw [heq]
        refine ((eLpNorm_varpCol_le (ρ := ρ) (P := P) (C₀ := C₀) (a := a) (f := f) (g := g)
          (l₁ := l₁) (l₂ := l₂) (k₁ := k₁) (k₂ := k₂) (n := n) hidx hFmem hGmem).trans
          (mul_le_mul' hFb hGb)).trans ?_
        have hval : (Cρ : ENNReal) * eLpNorm f 2 Measure.count
              * ((Cρ : ENNReal) * eLpNorm g 2 Measure.count)
            = (Cq : ENNReal) * (eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count) := by
          rw [hCqdef, ENNReal.coe_mul]
          ring
        exact le_of_eq hval
      · have hz : (fun x : ℤ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
          funext x
          show colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0
          rw [colSmall_apply, if_pos hclamp, varpCol_apply, if_neg hidx]
        rw [hz, eLpNorm_zero]
        exact bot_le
    · have hz : (fun x : ℤ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
        funext x
        show colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0
        rw [colSmall_apply, if_neg hclamp]
      rw [hz, eLpNorm_zero]
      exact bot_le
  have hmeas : ∀ n ∈ Finset.range (lowIndexBound Λ K),
      AEStronglyMeasurable (fun x : ℤ => colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) Measure.count :=
    fun n _ => (measurable_of_countable _).aestronglyMeasurable
  -- the sum of the single scale bounds
  have hsum_eq : ∑ _n ∈ Finset.range (lowIndexBound Λ K),
        4 * ((Cq : ENNReal) * (eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count))
      = (lowIndexBound Λ K : ENNReal) *
          (4 * (ENNReal.ofReal (Cq : ℝ)
            * (eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count))) := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_coe_nnreal]
  refine (eLpNorm_variationalNorm_le_sum (r := r) (p := 1) hr1 le_rfl hsupp hmeas).trans ?_
  refine (Finset.sum_le_sum (fun n hn => mul_le_mul' le_rfl (hterm n hn))).trans ?_
  rw [hsum_eq]
  refine (tsum_const_le_mul (Kc := Kc Λ) (nB := lowIndexBound Λ K) (M := (Cq : ℝ))
    (X := eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count) hKcval).trans ?_
  exact le_of_eq (mul_assoc _ _ _).symm

end

end Work.KMTPlan.A6
