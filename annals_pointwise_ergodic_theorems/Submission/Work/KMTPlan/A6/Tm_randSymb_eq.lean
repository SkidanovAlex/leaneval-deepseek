/-
# The randomised telescoping identity for the exact-height IW family `Tm` (ℓ² form)

The identity proved here is the *symbolic* content of the two-dimensional
Rademacher--Menshov reduction: for the exact-height Ionescu--Wainger family
`Tm ρ l φ u = iwConv (diffFreqs ρ l) (periodize φ) u` of `KMTAreas/A7/ModelOps.lean`, the
randomised telescoping sum `∑_{k<K} ε k • (T^{l}_{Φ(k+1)} f - T^{l}_{Φ k} f)` collapses to the
single multiplier `T^{l}_{randSymb Φ ε K}` with the randomised symbol
`randSymb Φ ε K = ∑_{k<K} ε k (Φ(k+1) - Φ k)`.

The sibling lemma `Work.KMTAreas.A7.Tm_randSymb_eq_rangeSum` proves the same identity under
`ℓ¹`-kernels and *bounded* data.  Here the hypotheses are the `ℓ²` ones: the input is `f ∈ ℓ²(ℤ)`
and the convolution kernel of each piece is only requested to be square-summable.  The additivity
of the *unconditional* `tsum` defining `Tm` then follows from `ℓ² * ℓ² ⊆ ℓ¹`, which is
`Work.KMTPlan.A6.Tm_add_of_memLp.summable_smul_of_summable_normSq`.

The bookkeeping predicate is `Adm2 A φ`; it is the `ℓ²` analogue of `Adm` of
`KMTAreas/A7/Tm_randSymb_Adm.lean`, and the arguments below mirror that file's closure lemmas.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallModelDefs
import Submission.Work.KMTAreas.A7.FpieceEqTm
import Submission.Work.KMTPlan.A6.Tm_finset_sum

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IWMultiplier (iwKernel iwConv iwConv_apply)
open Work.Analysis.IonescuWainger (periodize iwSymbolSet circleMeasure iwSymbolSet_add
  iwSymbolSet_const_mul)
open Work.KMTAreas.A7 (Tm diffFreqs randSymb randSymb_zero Tm_const_mul periodize_add
  iwKernel_iwSymbolSet_add iwKernel_iwSymbolSet_sub iwKernel_iwSymbolSet_const_mul)

/-- **`ℓ²`-admissibility of a symbol `φ` at the frequency set `A`**: the translates of `φ` are
summable at every point, the IW symbol `iwSymbolSet A (periodize φ)` is integrable on the circle,
and its Fourier-coefficient (convolution) kernel is in `ℓ²`.  These are exactly the hypotheses
under which `Tm` is additive in the symbol for `ℓ²` input (`Tm_add_of_adm2`). -/
def Adm2 (A : Finset Work.Analysis.IonescuWainger.Circle) (φ : ℝ → ℂ) : Prop :=
  (∀ x : ℝ, Summable fun j : ℤ => φ (x + (j : ℝ))) ∧
    Integrable (iwSymbolSet A (periodize φ)) circleMeasure ∧
    Summable fun j : ℤ => ‖iwKernel (iwSymbolSet A (periodize φ)) j‖ ^ 2

/-- The exact-height multiplier of the zero symbol is the zero operator. -/
theorem Tm_zero_of_sym (ρ : ℝ) (l : ℕ) (f : ℤ → ℂ) : Tm ρ l (0 : ℝ → ℂ) f = 0 := by
  funext y
  simp only [Tm, iwConv_apply, Pi.zero_apply]
  simp [iwKernel, fourierCoeff, periodize]

/-- Pointwise scalar multiples of an `ℓ²`-admissible symbol are `ℓ²`-admissible. -/
theorem Adm2.const_mul {A : Finset Work.Analysis.IonescuWainger.Circle} {φ : ℝ → ℂ}
    (h : Adm2 A φ) (c : ℂ) : Adm2 A (fun ξ => c * φ ξ) := by
  have hper : periodize (fun ξ => c * φ ξ) = fun ξ => c * periodize φ ξ := by
    funext ξ
    simp only [periodize]
    exact tsum_mul_left
  have hsym : iwSymbolSet A (fun ξ => c * periodize φ ξ)
      = fun ξ => c * iwSymbolSet A (periodize φ) ξ := iwSymbolSet_const_mul A c (periodize φ)
  refine ⟨fun x => (h.1 x).mul_left c, ?_, ?_⟩
  · rw [hper, hsym]
    exact h.2.1.const_mul c
  · have hker : ∀ j : ℤ,
        iwKernel (iwSymbolSet A (fun ξ => c * periodize φ ξ)) j
          = c * iwKernel (iwSymbolSet A (periodize φ)) j :=
      fun j => iwKernel_iwSymbolSet_const_mul A c j
    simp only [hper]
    simpa only [hker, norm_mul, mul_pow] using h.2.2.mul_left (‖c‖ ^ 2)

/-- Sums of `ℓ²`-admissible symbols are `ℓ²`-admissible. -/
theorem Adm2.add {A : Finset Work.Analysis.IonescuWainger.Circle} {φ ψ : ℝ → ℂ}
    (h : Adm2 A φ) (h' : Adm2 A ψ) : Adm2 A (φ + ψ) := by
  have hper : periodize (φ + ψ) = periodize φ + periodize ψ := periodize_add h.1 h'.1
  refine ⟨fun x => (h.1 x).add (h'.1 x), ?_, ?_⟩
  · rw [hper, iwSymbolSet_add]
    exact h.2.1.add h'.2.1
  · have hker : ∀ j : ℤ,
        iwKernel (iwSymbolSet A (periodize φ + periodize ψ)) j
          = iwKernel (iwSymbolSet A (periodize φ)) j
            + iwKernel (iwSymbolSet A (periodize ψ)) j :=
      fun j => iwKernel_iwSymbolSet_add h.2.1 h'.2.1 j
    simp only [hper]
    refine Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => ?_)
      ((h.2.2.add h'.2.2).mul_left 2)
    rw [hker j]
    have h1 : ‖iwKernel (iwSymbolSet A (periodize φ)) j
          + iwKernel (iwSymbolSet A (periodize ψ)) j‖
        ≤ ‖iwKernel (iwSymbolSet A (periodize φ)) j‖
          + ‖iwKernel (iwSymbolSet A (periodize ψ)) j‖ := norm_add_le _ _
    have h2 : ‖iwKernel (iwSymbolSet A (periodize φ)) j
          + iwKernel (iwSymbolSet A (periodize ψ)) j‖ ^ 2
        ≤ (‖iwKernel (iwSymbolSet A (periodize φ)) j‖
          + ‖iwKernel (iwSymbolSet A (periodize ψ)) j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [h2, sq_nonneg (‖iwKernel (iwSymbolSet A (periodize φ)) j‖
      - ‖iwKernel (iwSymbolSet A (periodize ψ)) j‖)]

/-- Negatives of `ℓ²`-admissible symbols are `ℓ²`-admissible. -/
theorem Adm2.neg {A : Finset Work.Analysis.IonescuWainger.Circle} {φ : ℝ → ℂ}
    (h : Adm2 A φ) : Adm2 A (-φ) := by
  have hneg : Adm2 A (fun ξ => (-1 : ℂ) * φ ξ) := h.const_mul (-1)
  have hfun : (fun ξ => (-1 : ℂ) * φ ξ) = -φ := by funext ξ; simp
  rwa [hfun] at hneg

/-- Differences of `ℓ²`-admissible symbols are `ℓ²`-admissible. -/
theorem Adm2.sub {A : Finset Work.Analysis.IonescuWainger.Circle} {φ ψ : ℝ → ℂ}
    (h : Adm2 A φ) (h' : Adm2 A ψ) : Adm2 A (φ - ψ) := by
  have hfun : φ - ψ = φ + -ψ := by
    funext ξ; simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]
  rw [hfun]
  exact h.add h'.neg

/-- **Additivity of `Tm` in its symbol, in `ℓ²` form**: for `f ∈ ℓ²` and `ℓ²`-admissible symbols
`φ`, `ψ`, the multiplier of the sum is the sum of the multipliers. -/
theorem Tm_add_of_adm2 (ρ : ℝ) (l : ℕ) {φ ψ : ℝ → ℂ} {f : ℤ → ℂ}
    (hf : MemLp f 2 Measure.count) (h : Adm2 (diffFreqs ρ l) φ)
    (h' : Adm2 (diffFreqs ρ l) ψ) :
    Tm ρ l (φ + ψ) f = Tm ρ l φ f + Tm ρ l ψ f :=
  Tm_add_of_memLp ρ l hf h.1 h'.1 h.2.1 h'.2.1 h.2.2 h'.2.2

/-- **Subtractivity of `Tm` in its symbol, in `ℓ²` form**. -/
theorem Tm_sub_of_adm2 (ρ : ℝ) (l : ℕ) {φ ψ : ℝ → ℂ} {f : ℤ → ℂ}
    (hf : MemLp f 2 Measure.count) (h : Adm2 (diffFreqs ρ l) φ)
    (h' : Adm2 (diffFreqs ρ l) ψ) :
    Tm ρ l (φ - ψ) f = Tm ρ l φ f - Tm ρ l ψ f := by
  have hneg : Adm2 (diffFreqs ρ l) (fun ξ => (-1 : ℂ) * ψ ξ) := h'.const_mul (-1)
  have hsum := Tm_add_of_adm2 ρ l hf h hneg
  have hcm := Tm_const_mul (ρ := ρ) l (-1 : ℂ) (φ := ψ) (f := f)
  have hfun : φ + (fun ξ => (-1 : ℂ) * ψ ξ) = φ - ψ := by
    funext ξ; simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [hfun] at hsum
  rw [hsum, hcm]
  funext n
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- **The randomised telescoping identity**, with the `ℓ²`-admissibility of the partial symbol
`randSymb Φ ε K` carried along the induction on `K`. -/
theorem Tm_randSymb_eq_aux (ρ : ℝ) (l : ℕ) (Φ : ℕ → ℝ → ℂ) (ε : ℕ → ℂ) (f : ℤ → ℂ)
    (hf : MemLp f 2 Measure.count) :
    ∀ K : ℕ, (∀ m ≤ K, Adm2 (diffFreqs ρ l) (Φ m)) →
      Adm2 (diffFreqs ρ l) (randSymb Φ ε K) ∧
        Tm ρ l (randSymb Φ ε K) f
          = ∑ k ∈ Finset.range K, ε k • (Tm ρ l (Φ (k + 1)) f - Tm ρ l (Φ k) f) := by
  intro K
  induction K with
  | zero =>
      intro hΦ
      have h0 : Adm2 (diffFreqs ρ l) (0 : ℝ → ℂ) := by
        have h := (hΦ 0 le_rfl).const_mul (0 : ℂ)
        have hfun : (fun ξ => (0 : ℂ) * Φ 0 ξ) = (0 : ℝ → ℂ) := by funext ξ; simp
        rwa [hfun] at h
      refine ⟨?_, ?_⟩
      · rwa [randSymb_zero]
      · rw [randSymb_zero, Tm_zero_of_sym]
        simp
  | succ K ih =>
      intro hΦ
      have ihK := ih (fun m hm => hΦ m (Nat.le_trans hm (Nat.le_succ K)))
      have hpiece : Adm2 (diffFreqs ρ l) (fun ξ => ε K * ((Φ (K + 1) - Φ K) ξ)) :=
        ((hΦ (K + 1) le_rfl).sub (hΦ K (Nat.le_succ K))).const_mul (ε K)
      have hsucc : randSymb Φ ε (K + 1)
          = randSymb Φ ε K + (fun ξ => ε K * ((Φ (K + 1) - Φ K) ξ)) := by
        funext ξ
        simp only [randSymb, Pi.add_apply, Pi.sub_apply, Finset.sum_range_succ]
      refine ⟨?_, ?_⟩
      · rw [hsucc]
        exact ihK.1.add hpiece
      · rw [hsucc, Tm_add_of_adm2 ρ l hf ihK.1 hpiece, ihK.2,
          Tm_const_mul (ρ := ρ) l (ε K) (φ := Φ (K + 1) - Φ K) (f := f),
          Tm_sub_of_adm2 ρ l hf (hΦ (K + 1) le_rfl) (hΦ K (Nat.le_succ K))]
        funext y
        simp only [Finset.sum_apply, Finset.sum_range_succ, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, Pi.sub_apply]

theorem Tm_randSymb_eq (ρ : ℝ) (l K : ℕ) (Φ : ℕ → ℝ → ℂ) (ε : ℕ → ℂ) (f : ℤ → ℂ)
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hper : ∀ k ∈ Finset.range (K + 1), ∀ x : ℝ, Summable fun j : ℤ => Φ k (x + (j : ℝ)))
    (hI : ∀ k ∈ Finset.range (K + 1), MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize (Φ k)))
      Work.Analysis.IonescuWainger.circleMeasure)
    (hκ : ∀ k ∈ Finset.range (K + 1), Summable fun j : ℤ =>
      ‖Work.Analysis.IWMultiplier.iwKernel (Work.Analysis.IonescuWainger.iwSymbolSet
        (Work.KMTAreas.A7.diffFreqs ρ l)
        (Work.Analysis.IonescuWainger.periodize (Φ k))) j‖ ^ 2) :
    Work.KMTAreas.A7.Tm ρ l (Work.KMTAreas.A7.randSymb Φ ε K) f
      = ∑ k ∈ Finset.range K, ε k • (Work.KMTAreas.A7.Tm ρ l (Φ (k + 1)) f
          - Work.KMTAreas.A7.Tm ρ l (Φ k) f) := by
  refine (Tm_randSymb_eq_aux ρ l Φ ε f hf K ?_).2
  intro m hm
  exact ⟨hper m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)),
    hI m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm)),
    hκ m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))⟩

end Work.KMTPlan.A6
