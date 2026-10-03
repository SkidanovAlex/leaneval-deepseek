/-
The **small-scale half** of the Ionescu–Wainger multiplier theorem for the concrete frequency sets
`iwArithFreqs ρ l = (ℚ/ℤ)_{≤l}`.

The deep Ionescu–Wainger / Mirek–Stein–Zorin-Kranich multiplier theorem is *not* uniform in the
exponent `q = 2r` for fixed arcs: its numerator/denominator orthogonality needs the arithmetic gap
of `2r`-fold products of denominators to dominate `2r·2^k`, a smallness condition which fails for
large `r` when the scale `l` (hence the arc size) is fixed.  The scales `l ≤ L` are therefore
handled separately, and this is the content of the present lemma: for *finitely many* scales the
bound is elementary, because the IW arcs `α + ℝ_{≤k}`, `α ∈ (ℚ/ℤ)_{≤l}`, are pairwise separated
(`2^k · 2 ≤ 1`), each single arc `{α}` is a Magyar–Stein–Wainger multiplier (a modulation of the
`Q = 1` case of the sampling principle), and the frequency set is finite, of cardinality
`≲_ρ 2^{2^{ρl}}`.

The chain of the proof is

1. `two_pow_mul_two_le_one_of_goodMajorArcs` — good major arcs with `C_ρ ≥ 2` give `2^k · 2 ≤ 1`;
2. `MSW_single_torsion` at `Q = 1` — the scalar `ℓ^q(ℤ;ℂ)` bound for the single arc `{0}` with the
   constant `C₁ · M`, where `M` bounds the continuous multiplier `T_φ` on `L^q(ℝ)`;
3. the quantitative Khintchine/MZ passage `IWLqBound_of_scalar_mul` — the scalar bound implies the
   `H`-valued one with a constant *multiplied by* `K₁` (uniform in the finite dimensional Hilbert
   space `H`);
4. `IWLqBound_shift_singleton` — the same constant for every single arc `{α}` (the frequency set
   of a singleton only modulates the symbol, an isometry of every `ℓ^q`);
5. `IWLqBound_of_singleton_bounds` — summing over the finitely many arcs, with the loss
   `#(ℚ/ℤ)_{≤l}`;
6. taking the supremum of the resulting constants over the finitely many scales `l ≤ L`.

Note that steps 2–4 give a constant *linear* in `M`; this is where the quantitative form (3) of the
Khintchine passage is needed, and it is also why the constant may be taken independent of `M`.
-/
import Mathlib
import Submission.Work.KMTAreas.MSW_single_torsion
import Submission.Work.KMTAreas.iw_small_scale
import Submission.Work.KMTAreas.IWLqBound_of_scalar_mul
import Submission.Work.KMTAreas.integrable_iwSymbolSet_periodize

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTAreas

open scoped BigOperators ENNReal NNReal
open MeasureTheory

open Work.Analysis.IWMultiplier
open Work.Analysis.IonescuWainger

/-- Good major arcs with `C_ρ ≥ 2` put the frequency arc `ℝ_{≤k}` inside an interval of length
`< 1`: `2^k · 2 ≤ 1`.  In particular the single torsion point `{0}` satisfies the separation
hypothesis of the Magyar–Stein–Wainger sampling principle with `Q = 1`. -/
theorem two_pow_mul_two_le_one_of_goodMajorArcs {ρ Cρ : ℝ} {l : ℕ} {k : ℤ}
    (hgood : GoodMajorArcs ρ Cρ l k) (hCρ : 2 ≤ Cρ) (hρ : 0 < ρ) :
    (2 : ℝ) ^ k * 2 ≤ 1 := by
  have h := two_pow_succ_lt_one_of_goodMajorArcs hgood hCρ hρ
  rw [zpow_add_one₀ (by norm_num : (2 : ℝ) ≠ 0)] at h
  linarith

/-- **The small-scale half of the Ionescu–Wainger multiplier theorem.**  For `0 < ρ ≤ 1`,
`r ≥ 2`, `C_ρ ≥ 2` and a fixed finite range of scales `l ≤ L` there is a constant `C > 0`,
depending only on `ρ, r, C_ρ, L`, such that whenever `(l,k)` has good major arcs, `φ` is a
Schwartz symbol supported in `ℝ_{≤k}` and `M` bounds the continuous multiplier `T_φ` on
`L^{2r}(ℝ)`, the IW projection `T^{≤l}_φ` is bounded on `ℓ^{2r}(ℤ;H)` for every finite
dimensional Hilbert space `H` with constant `C · M`:

`IWLqBound (iwArithFreqs ρ l) (periodize φ) (2r) (C · M)`.

The only places where the hypotheses `l ≤ L` (finitely many scales) and the elementary
single-arc bound are used is the finiteness of the constant; the exponent `2r` is fixed
throughout, so the constant may depend on it. -/
theorem iwArithFreqs_small_scale (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : ℕ) (hr : 2 ≤ r)
    {Cρ : ℝ} (hCρ : 2 ≤ Cρ) (L : ℕ) :
    ∃ C : NNReal, 0 < C ∧ ∀ l : ℕ, l ≤ L → ∀ (k : ℤ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k →
      ∀ (φ : SchwartzMap ℝ ℂ),
        (∀ x, φ x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k) →
      ∀ (M : NNReal),
        Work.Analysis.IWMultiplier.IsLqMultiplierBound ((2 * r : ℕ) : ENNReal) (φ : ℝ → ℂ) M →
        Work.Analysis.IWMultiplier.IWLqBound (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize (φ : ℝ → ℂ)) ((2 * r : ℕ) : ENNReal) (C * M) := by
  classical
  set q : ENNReal := ((2 * r : ℕ) : ENNReal) with hqdef
  have hq1 : 1 ≤ q := by
    rw [hqdef]
    exact_mod_cast (show 1 ≤ 2 * r by omega)
  have hq2 : q < ⊤ := by
    rw [hqdef]
    exact ENNReal.natCast_lt_top (2 * r)
  -- the single-arc (Magyar–Stein–Wainger) constant `C₁`, and the Khintchine constant `K₁`
  obtain ⟨C₁, hC₁pos, hC₁⟩ := MSW_single_torsion (Q := 1) le_rfl (p := q) hq1 hq2
  obtain ⟨K₁, hK₁pos, hK₁⟩ := IWLqBound_of_scalar_mul (q := q) hq1 hq2
  have hC₁K₁pos : 0 < C₁ * K₁ := mul_pos hC₁pos hK₁pos
  -- the constant: the supremum of the per-scale bounds `(C₁ K₁) · #(ℚ/ℤ)_{≤l}`, `l ≤ L`
  refine ⟨(Finset.range (L + 1)).sup
      (fun l : ℕ => (C₁ * K₁) * (((iwArithFreqs ρ l).card : ℕ) : NNReal)) + 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_add_left le_rfl)
  · intro l hl k hgood φ hφ M hM
    have hk2 : (2 : ℝ) ^ k * 2 ≤ 1 := two_pow_mul_two_le_one_of_goodMajorArcs hgood hCρ hρ
    -- (i) the bound for a single arc `{α}`, with the constant `(C₁ K₁) · M`
    have hsingle : ∀ α : Work.Analysis.IonescuWainger.Circle,
        IWLqBound ({α} : Finset Work.Analysis.IonescuWainger.Circle) (periodize (φ : ℝ → ℂ)) q ((C₁ * K₁) * M) := by
      intro α
      have hk2' : (2 : ℝ) ^ k * (2 * ((1 : ℕ) : ℝ)) ≤ 1 := by simpa using hk2
      have hsc : IWLqBoundScalar (iwDenomFreqs {1}) (periodize (φ : ℝ → ℂ)) q (C₁ * M) :=
        hC₁ (k := k) hk2' hφ hM
      rw [iwDenomFreqs_one] at hsc
      have hb0 : IWLqBound ({0} : Finset Work.Analysis.IonescuWainger.Circle) (periodize (φ : ℝ → ℂ)) q ((C₁ * M) * K₁) :=
        hK₁ hsc
      have hbα : IWLqBound ({α} : Finset Work.Analysis.IonescuWainger.Circle) (periodize (φ : ℝ → ℂ)) q ((C₁ * M) * K₁) :=
        IWLqBound_shift_singleton hb0
      rwa [show (C₁ * M) * K₁ = (C₁ * K₁) * M from by ring] at hbα
    -- (ii) the sum over the finitely many arcs
    have hint : ∀ α ∈ iwArithFreqs ρ l,
        Integrable (iwSymbolSet ({α} : Finset Work.Analysis.IonescuWainger.Circle) (periodize (φ : ℝ → ℂ))) circleMeasure :=
      fun α _ => integrable_iwSymbolSet_periodize {α} φ
    have hbound : IWLqBound (iwArithFreqs ρ l) (periodize (φ : ℝ → ℂ)) q
        (((C₁ * K₁) * M) * (((iwArithFreqs ρ l).card : ℕ) : NNReal)) :=
      IWLqBound_of_singleton_bounds hint hq1 (fun α _ => hsingle α)
    -- (iii) the constant of the scale `l` is dominated by the supremum
    refine hbound.mono ?_
    have hlmem : l ∈ Finset.range (L + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hl)
    have hsup := Finset.le_sup
      (f := fun l : ℕ => (C₁ * K₁) * (((iwArithFreqs ρ l).card : ℕ) : NNReal)) hlmem
    calc ((C₁ * K₁) * M) * (((iwArithFreqs ρ l).card : ℕ) : NNReal)
        = ((C₁ * K₁) * (((iwArithFreqs ρ l).card : ℕ) : NNReal)) * M := by ring
      _ ≤ ((Finset.range (L + 1)).sup
            (fun l : ℕ => (C₁ * K₁) * (((iwArithFreqs ρ l).card : ℕ) : NNReal))) * M :=
          mul_le_mul_of_nonneg_right hsup (zero_le : (0 : NNReal) ≤ M)
      _ ≤ ((Finset.range (L + 1)).sup
            (fun l : ℕ => (C₁ * K₁) * (((iwArithFreqs ρ l).card : ℕ) : NNReal)) + 1) * M :=
          mul_le_mul_of_nonneg_right (le_add_right le_rfl) (zero_le : (0 : NNReal) ≤ M)

end Work.KMTAreas
