/-
# The high–high case of area A6: the core estimate

This module proves `Work.KMTPlan.A6.highHighCase_of_children`: the high–high case
(`CaseHH`, i.e. `k₁,k₂ ≥ 1`) of Krause--Mirek--Tao's Theorem `varp` at `(p₁,p₂,p) = (2,2,1)`
with the exponential gain `2^{-c·max(max l₁ l₂)(max k₁ k₂)}`.

The proof follows the paper's Proposition `high-high-l2`:

* the variational norm of the columns is dominated by the sum of the `ℓ¹` norms
  (`eLpNorm_variationalNorm_one_le_tsum`, `(varsum)`);
* on the index set and in the *good-scale regime* `hhGood R ρ M N` the single-scale `improv`
  (Theorem `improv`, hypothesis `hI`) may be applied at the height `L ≤ M` with `M ≤ L+2`
  produced by `exists_height_cases`: the arithmetic-frequency vanishing of the pieces
  (`hhVanishingF`/`hhVanishingG`) supplies the minor-arc hypothesis, the logarithmic error term
  is dominated by the gain (`LogGain`), and the result is `≲ 2^{-(cI/2)M}‖F_N‖₂‖G_N‖₂`;
* the exceptional quadruple `(0,0,1,1)` (where no such height exists) is treated by `(anf)`,
  the constant `2^{cI/2}` being absorbed by the weight `2^{-cI/2}`;
* the bad scales (outside the good-scale regime) are handled by the crude `ℓ²` bounds and the
  lacunarity of the scale sequence (`lacunaryCard`), so that only `≲ log N / log Λ` of them
  contribute;
* the good part is summed by Cauchy–Schwarz and the Bessel-type inequalities `BesselF`/`BesselG`
  (`tsum_mul_le_of_finset_sq_le`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.HHAux
import Submission.Work.KMTPlan.A6.hhVanishingG
import Submission.Work.KMTPlan.A6.lacunaryCard

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
open Work.Analysis.IonescuWainger
open Work.KMTContract

/-! ## Degenerate data -/

/-- With the counting measure on `ℤ`, a function of vanishing `ℓ²` norm is identically zero. -/
theorem eq_zero_of_eLpNorm_two_eq_zero {h : ℤ → ℂ}
    (hh : eLpNorm h 2 (Measure.count : Measure ℤ) = 0) : h = 0 := by
  funext x
  have hae : h =ᵐ[(Measure.count : Measure ℤ)] 0 :=
    (eLpNorm_eq_zero_iff (by norm_num)).mp hh
  exact Measure.ae_count_iff.mp hae x

/-! ## The gain coefficient -/

/-- The coefficient of the good-scale estimate: the `improv` constant `(4^{cI}+1)·CI` together
with the constant `2^{cI/2}` needed at the exceptional quadruple `(0,0,1,1)`. -/
def hhGainCoeff (cI : ℝ) (CI : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal ((4 : ℝ) ^ cI + 1) * (CI : ℝ≥0∞) + ENNReal.ofReal ((2 : ℝ) ^ (cI / 2))

/-- The weight comparison of the `improv` estimate with the gain `2^{-(cI/2)M}`. -/
theorem improv_weight_le {ρ cI R : ℝ} (hρ : 0 < ρ) (hcI : 0 < cI) (hR : 1 ≤ R)
    (hlog : Sub.LogGain ρ cI R) {CI : ℝ≥0} {l₁ l₂ k₁ k₂ L N : ℕ}
    (hL : kmtM l₁ l₂ k₁ k₂ ≤ L + 2) (hgood : hhGood R ρ (kmtM l₁ l₂ k₁ k₂) N) :
    (CI : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(cI * (L : ℝ)))
        + ((logN N : ℤ) : ℝ) ^ (-(cI / ρ)))
      ≤ (hhGainCoeff cI CI : ℝ≥0∞) * ENNReal.ofReal (hhWeight (cI / 2) l₁ l₂ k₁ k₂) := by
  have hX : (1 : ℝ) ≤ ((logN N : ℤ) : ℝ) := by
    have h := logN_pos N
    exact_mod_cast h
  have hlog' := hlog (kmtM l₁ l₂ k₁ k₂) ((logN N : ℤ) : ℝ) hX hgood
  have hgain := rpow_gain_le cI (le_of_lt hcI) L (kmtM l₁ l₂ k₁ k₂) hL
  have hsum : (2 : ℝ) ^ (-(cI * (L : ℝ))) + ((logN N : ℤ) : ℝ) ^ (-(cI / ρ))
      ≤ (((4 : ℝ) ^ cI + 1)) * hhWeight (cI / 2) l₁ l₂ k₁ k₂ := by
    have h4 : (2 : ℝ) ^ (2 * cI) = (4 : ℝ) ^ cI := by
      have h2 : (4 : ℝ) = 2 * 2 := by norm_num
      rw [h2, Real.mul_rpow (by norm_num) (by norm_num),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have hW : hhWeight (cI / 2) l₁ l₂ k₁ k₂
        = (2 : ℝ) ^ (-(cI / 2 * ((kmtM l₁ l₂ k₁ k₂ : ℕ) : ℝ))) := rfl
    have h1 : (2 : ℝ) ^ (-(cI * (L : ℝ)))
        ≤ (2 : ℝ) ^ (2 * cI) * hhWeight (cI / 2) l₁ l₂ k₁ k₂ := by
      rw [hW]
      exact hgain
    rw [h4] at h1
    have h2 : ((logN N : ℤ) : ℝ) ^ (-(cI / ρ)) ≤ hhWeight (cI / 2) l₁ l₂ k₁ k₂ := by
      rw [hW]; exact hlog'
    have h3 : ((4 : ℝ) ^ cI + 1) * hhWeight (cI / 2) l₁ l₂ k₁ k₂
        = (4 : ℝ) ^ cI * hhWeight (cI / 2) l₁ l₂ k₁ k₂ + hhWeight (cI / 2) l₁ l₂ k₁ k₂ := by
      ring
    rw [h3]
    linarith
  have hWpos : (0 : ℝ) ≤ hhWeight (cI / 2) l₁ l₂ k₁ k₂ := hhWeight_nonneg _ _ _ _ _
  calc (CI : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(cI * (L : ℝ)))
        + ((logN N : ℤ) : ℝ) ^ (-(cI / ρ)))
      = (CI : ℝ≥0∞) * (ENNReal.ofReal ((2 : ℝ) ^ (-(cI * (L : ℝ))))
          + ENNReal.ofReal (((logN N : ℤ) : ℝ) ^ (-(cI / ρ)))) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ (CI : ℝ≥0∞) * (ENNReal.ofReal ((4 : ℝ) ^ cI + 1)
          * ENNReal.ofReal (hhWeight (cI / 2) l₁ l₂ k₁ k₂)) := by
        refine mul_le_mul' le_rfl ?_
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact (ENNReal.ofReal_le_ofReal hsum).trans (le_of_eq (by
          rw [ENNReal.ofReal_mul (by positivity)]))
    _ = (ENNReal.ofReal ((4 : ℝ) ^ cI + 1) * (CI : ℝ≥0∞))
          * ENNReal.ofReal (hhWeight (cI / 2) l₁ l₂ k₁ k₂) := by
        ac_rfl
    _ ≤ (hhGainCoeff cI CI)
          * ENNReal.ofReal (hhWeight (cI / 2) l₁ l₂ k₁ k₂) := by
        refine mul_le_mul_of_nonneg_right ?_ zero_le
        exact le_add_of_nonneg_right zero_le

/-! ## The index sets of the good- and bad-scale parts -/

/-- The indices at which the good-scale estimate applies: the scale is in the index set and in
the good-scale regime. -/
def hhPm (R ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) : Prop :=
  inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) ∧
    hhGood R ρ (kmtM l₁ l₂ k₁ k₂) (Nat.floor (a n))

/-- The indices which are in the index set but outside the good-scale regime: these are the
"bad scales", of which there are only `O(log N / log Λ)` because of the lacunarity of `a`. -/
def hhBad (R ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) : Prop :=
  ¬ hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n ∧
    inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))

theorem hhBad.not_hhPm {R ρ : ℝ} {C₀ : ℕ} {a : ℕ → ℝ≥0} {l₁ l₂ k₁ k₂ n : ℕ}
    (h : hhBad R ρ C₀ a l₁ l₂ k₁ k₂ n) : ¬ hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n := h.1

theorem hhBad.indexSet {R ρ : ℝ} {C₀ : ℕ} {a : ℕ → ℝ≥0} {l₁ l₂ k₁ k₂ n : ℕ}
    (h : hhBad R ρ C₀ a l₁ l₂ k₁ k₂ n) :
    inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) := h.2

/-- **The single-scale good-scale estimate.**  If the vanishing hypothesis of `improv` holds for
the pieces and the height `L` satisfies `M ≤ L+2`, then the column obeys the estimate with the
gain `2^{-(cI/2)M}`. -/
theorem singleScaleGain
    {P : ℤ[X]} {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {cI : ℝ} (hcI : 0 < cI) {CI : ℝ≥0} {R : ℝ} (hR1 : 1 ≤ R)
    (hlog : Sub.LogGain ρ cI R)
    (hI : ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N → MemLp f 2 Measure.count → MemLp g 2 Measure.count →
        (kmtProj ρ l (-(logN N) + l) f = 0 ∨
          kmtProj ρ l ((P.natDegree : ℤ) * (-(logN N) + l)) g = 0) →
        eLpNorm (AhalfR TZ (N : ℝ≥0) X P f g) 1 Measure.count ≤
          (CI : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(cI * (l : ℝ)))
            + ((logN N : ℤ) : ℝ) ^ (-(cI / ρ))) * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count)
    {C₀ : ℕ} {a : ℕ → ℝ≥0} {f g : ℤ → ℂ} {l₁ l₂ k₁ k₂ L n : ℕ}
    (ha1 : 1 ≤ a n) (hL : kmtM l₁ l₂ k₁ k₂ ≤ L + 2)
    (hgood : hhGood R ρ (kmtM l₁ l₂ k₁ k₂) (Nat.floor (a n)))
    (hindex : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)))
    (hFmem : MemLp (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f) 2 Measure.count)
    (hGmem : MemLp (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g) 2 Measure.count)
    (hvan : kmtProj ρ L (-(logN (Nat.floor (a n))) + (L : ℤ))
              (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f) = 0 ∨
            kmtProj ρ L ((P.natDegree : ℤ) * (-(logN (Nat.floor (a n))) + (L : ℤ)))
              (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g) = 0) :
    eLpNorm (fun x : ℤ => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count
      ≤ (hhGainCoeff cI CI) * ENNReal.ofReal (hhWeight (cI / 2) l₁ l₂ k₁ k₂)
          * eLpNorm (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f) 2 Measure.count
          * eLpNorm (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g) 2 Measure.count := by
  have hN1 : 1 ≤ Nat.floor (a n) := Nat.le_floor (by exact_mod_cast ha1)
  have hmain := hI (Nat.floor (a n)) L
    (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f)
    (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g)
    hN1 hFmem hGmem hvan
  have hW := improv_weight_le (ρ := ρ) (cI := cI) (R := R) (CI := CI) hρ hcI hR1 hlog
    (l₁ := l₁) (l₂ := l₂) (k₁ := k₁) (k₂ := k₂) (N := Nat.floor (a n)) hL hgood
  have hcol : varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n
      = AhalfR TZ (a n) X P
          (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f)
          (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g) :=
    varpCol_eq_AhalfR (P := P) hindex
  rw [hcol, AhalfR_floor]
  calc eLpNorm (AhalfR TZ ((Nat.floor (a n) : ℕ) : ℝ≥0) X P
        (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f)
        (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g)) 1 Measure.count
      ≤ (CI : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(cI * (L : ℝ)))
            + ((logN (Nat.floor (a n)) : ℤ) : ℝ) ^ (-(cI / ρ)))
          * eLpNorm (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f) 2 Measure.count
          * eLpNorm (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g) 2 Measure.count := hmain
    _ = ((CI : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(cI * (L : ℝ)))
            + ((logN (Nat.floor (a n)) : ℤ) : ℝ) ^ (-(cI / ρ))))
          * (eLpNorm (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f) 2 Measure.count
            * eLpNorm (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g) 2 Measure.count) := by
        ac_rfl
    _ ≤ ((hhGainCoeff cI CI) * ENNReal.ofReal (hhWeight (cI / 2) l₁ l₂ k₁ k₂))
          * (eLpNorm (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f) 2 Measure.count
            * eLpNorm (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g) 2 Measure.count) :=
        mul_le_mul_of_nonneg_right hW zero_le
    _ = (hhGainCoeff cI CI) * ENNReal.ofReal (hhWeight (cI / 2) l₁ l₂ k₁ k₂)
          * eLpNorm (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f) 2 Measure.count
          * eLpNorm (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g) 2 Measure.count := by
        ac_rfl

/-- The constant of the high–high estimate, as a function of the lacunarity `Λ`. -/
noncomputable def hhConst (cI : ℝ) (CI : ℝ≥0) (BF BG : ℝ≥0 → ℝ≥0) (Nth : ℕ) (CFc CGc : ℝ≥0)
    (B₀ : ℕ) (Λ : ℝ≥0) : ℝ≥0 :=
  (3 * ((hhGainCoeff cI CI) * (BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞)
      + ((CFc * CGc : ℝ≥0) : ℝ≥0∞)
        * ((Nat.ceil (Real.log (Nth : ℝ) / Real.log (Λ : ℝ) + 1) : ℕ) : ℝ≥0∞)
        * ENNReal.ofReal ((2 : ℝ) ^ (cI / 2 * (B₀ : ℝ))) + 1)).toNNReal

/-- **The high–high case of Theorem `varp` at `(2,2,1)`, from the six child lemmas.** -/
theorem hh_main
    (hmem_ax : ∀ (ρ : ℝ) (l : ℕ) (k : ℤ) (f : ℤ → ℂ),
        MemLp f 2 Measure.count → MemLp (kmtProj ρ l k f) 2 Measure.count)
    (hbound_ax : ∀ (ρ : ℝ) (S : Finset (ℕ × ℤ)), ∃ C : ℝ≥0, 0 < C ∧
        ∀ p ∈ S, ∀ f : ℤ → ℂ, eLpNorm (kmtProj ρ p.1 p.2 f) 2 Measure.count
          ≤ (C : ℝ≥0∞) * eLpNorm f 2 Measure.count)
    (hCS_ax : ∀ (φ ψ : ℕ → ℝ≥0∞) (Pm : ℕ → Prop) [DecidablePred Pm] (Bφ Bψ u v : ℝ≥0∞),
        (∀ s : Finset ℕ, (∀ n ∈ s, Pm n) → (∑ n ∈ s, (φ n) ^ 2) ≤ Bφ ^ 2 * u ^ 2) →
        (∀ s : Finset ℕ, (∀ n ∈ s, Pm n) → (∑ n ∈ s, (ψ n) ^ 2) ≤ Bψ ^ 2 * v ^ 2) →
        (∑' n : ℕ, if Pm n then φ n * ψ n else 0) ≤ Bφ * Bψ * u * v)
    (hvanF_ax : ∀ (ρ R C : ℝ), 0 < ρ → ρ ≤ 1 → 1 ≤ R → C ≤ R →
        (∀ (l₁ L : ℕ) (K : ℤ), (K : ℝ) + C * (2 : ℝ) ^ (ρ * (max l₁ L : ℝ)) < 0 →
          NonAliasing K (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ L)) →
        Sub.VanishingF → ∀ (l₁ k₁ L N M : ℕ) (f : ℤ → ℂ), 1 ≤ k₁ → (L < l₁ ∨ L + 2 ≤ k₁) →
        L ≤ M → k₁ ≤ M → l₁ ≤ M → hhGood R ρ M N → MemLp f 2 Measure.count →
        kmtProj ρ L (-(logN N) + (L : ℤ)) (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) N f) = 0)
    (hvanG_ax : ∀ (ρ R C : ℝ), 0 < ρ → ρ ≤ 1 → 1 ≤ R → C ≤ R →
        (∀ (l₂ L : ℕ) (K : ℤ), (K : ℝ) + C * (2 : ℝ) ^ (ρ * (max l₂ L : ℝ)) < 0 →
          NonAliasing K (iwArithFreqs ρ l₂ ∪ iwArithFreqs ρ L)) →
        Sub.VanishingG → ∀ (P : ℤ[X]), 2 ≤ P.natDegree →
        ∀ (l₂ k₂ L N M : ℕ) (g : ℤ → ℂ), 1 ≤ k₂ → (L < l₂ ∨ L + 2 ≤ k₂) →
        L ≤ M → k₂ ≤ M → l₂ ≤ M → hhGood R ρ M N → MemLp g 2 Measure.count →
        kmtProj ρ L ((P.natDegree : ℤ) * (-(logN N) + (L : ℤ)))
          (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) N g) = 0)
    (P : ℤ[X]) (hd : 2 ≤ P.natDegree) (r : ℝ≥0) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (cI : ℝ) (hcI : 0 < cI) (CI : ℝ≥0)
    (hI : ∀ (N l : ℕ) (f g : ℤ → ℂ), 1 ≤ N → MemLp f 2 Measure.count → MemLp g 2 Measure.count →
        (kmtProj ρ l (-(logN N) + l) f = 0 ∨
          kmtProj ρ l ((P.natDegree : ℤ) * (-(logN N) + l)) g = 0) →
        eLpNorm (AhalfR TZ (N : ℝ≥0) X P f g) 1 Measure.count ≤
          (CI : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (-(cI * (l : ℝ)))
            + ((logN N : ℤ) : ℝ) ^ (-(cI / ρ))) * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count)
    (hvanF : Sub.VanishingF) (hvanG : Sub.VanishingG)
    (hbesF : Sub.BesselF ρ) (hbesG : Sub.BesselG ρ P) (hNA : Sub.NonAliasingSize ρ)
    (hlog : ∀ c : ℝ, 0 < c → ∀ R : ℝ, 1 ≤ R → Sub.LogGain ρ c R)
    (hgoodρ : ∀ R : ℝ, 1 ≤ R → Sub.GoodScaleArith C₀ ρ R) :
    PieceBoundOn ρ P C₀ 2 2 1 r
      (fun l₁ l₂ k₁ k₂ => (2 : ℝ) ^ (-(cI / 2 * (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ)))) CaseHH := by
  classical
  obtain ⟨CNA, hCNApos, hNA'⟩ := hNA
  obtain ⟨BF, CF, hCFpos, hbesF'⟩ := hbesF
  obtain ⟨BG, CG, hCGpos, hbesG'⟩ := hbesG
  set R : ℝ := max CNA (max CF CG) + 1 with hRdef
  have hR1 : 1 ≤ R := by
    rw [hRdef]
    have h1 : 0 ≤ max CNA (max CF CG) := le_trans hCNApos.le (le_max_left _ _)
    linarith
  have hR0 : 0 ≤ R := le_trans zero_le_one hR1
  have hRCNA : CNA ≤ R := by
    rw [hRdef]; have := le_max_left CNA (max CF CG); linarith
  have hRCF : CF ≤ R := by
    rw [hRdef]; have h1 := le_max_left CF CG; have h2 := le_max_right CNA (max CF CG); linarith
  have hRCG : CG ≤ R := by
    rw [hRdef]; have h1 := le_max_right CF CG; have h2 := le_max_right CNA (max CF CG); linarith
  obtain ⟨B₀, hB₀⟩ := hgoodρ R hR1
  set Lg : ℝ := (B₀ : ℝ) + R * (2 : ℝ) ^ (ρ * (B₀ : ℝ)) + 2 with hLgdef
  set KgN : ℕ := Nat.ceil Lg + 1 with hKgNdef
  have hKgN : Lg ≤ (KgN : ℝ) := by
    rw [hKgNdef]; have := Nat.le_ceil Lg; push_cast; linarith
  obtain ⟨CFc, hCFcpos, hCFc⟩ := crude_Fpiece_of hbound_ax ρ B₀ (KgN + 1)
  obtain ⟨CGc, hCGcpos, hCGc⟩ := crude_Gpiece_of hbound_ax ρ (P.natDegree : ℤ)
    (by exact_mod_cast Nat.zero_le P.natDegree) (P.natDegree * B₀) (P.natDegree * (KgN + 1))
  set Nth : ℕ := 2 ^ (KgN + 1) with hNthdef
  have hNth1 : (1 : ℝ) ≤ (Nth : ℝ) := by
    rw [hNthdef]; push_cast
    exact one_le_pow₀ (by norm_num)
  refine ⟨hhConst cI CI BF BG Nth CFc CGc B₀, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hHH
  set CL : ℝ≥0∞ := 3 * ((hhGainCoeff cI CI) * (BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞)
      + ((CFc * CGc : ℝ≥0) : ℝ≥0∞)
        * ((Nat.ceil (Real.log (Nth : ℝ) / Real.log (Λ : ℝ) + 1) : ℕ) : ℝ≥0∞)
        * ENNReal.ofReal ((2 : ℝ) ^ (cI / 2 * (B₀ : ℝ))) + 1) with hCLdef
  have hB_ne : ((CFc * CGc : ℝ≥0) : ℝ≥0∞)
      * ((Nat.ceil (Real.log (Nth : ℝ) / Real.log (Λ : ℝ) + 1) : ℕ) : ℝ≥0∞)
      * ENNReal.ofReal ((2 : ℝ) ^ (cI / 2 * (B₀ : ℝ))) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
      ENNReal.ofReal_ne_top
  have hGc_ne : (hhGainCoeff cI CI : ℝ≥0∞) ≠ ⊤ := by
    rw [hhGainCoeff]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.coe_ne_top,
      ENNReal.ofReal_ne_top⟩
  have hCLtop : CL ≠ ⊤ := by
    rw [hCLdef]
    refine ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.mpr ⟨?_, by norm_num⟩)
    refine ENNReal.add_ne_top.mpr ⟨?_, ?_⟩
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hGc_ne ENNReal.coe_ne_top)
        ENNReal.coe_ne_top
    · exact hB_ne
  have hCeq : ((hhConst cI CI BF BG Nth CFc CGc B₀ Λ : ℝ≥0) : ℝ≥0∞) = CL := by
    rw [hCLdef]
    exact ENNReal.coe_toNNReal hCLtop
  have hCL1 : (1 : ℝ≥0∞) ≤ CL := by
    rw [hCLdef]
    refine le_trans (by norm_num : (1 : ℝ≥0∞) ≤ 3) ?_
    exact le_mul_of_one_le_right zero_le le_add_self
  have hWpos : (0 : ℝ) ≤ hhWeight (cI / 2) l₁ l₂ k₁ k₂ := hhWeight_nonneg _ _ _ _ _
  have hWne : ENNReal.ofReal (hhWeight (cI / 2) l₁ l₂ k₁ k₂) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.rpow_pos_of_pos (by norm_num) _)
  -- the bad indices are bounded in scale
  have hbad_lt : ∀ n : ℕ, hhBad R ρ C₀ a l₁ l₂ k₁ k₂ n → (a n : ℝ) < (Nth : ℝ) := by
    intro n hn
    obtain ⟨hnp, hni⟩ := hn
    have hnot : ¬ hhGood R ρ (kmtM l₁ l₂ k₁ k₂) (Nat.floor (a n)) := fun hg => hnp ⟨hni, hg⟩
    have hMB : kmtM l₁ l₂ k₁ k₂ < B₀ := by
      by_contra hcon
      exact hnot (hB₀ (kmtM l₁ l₂ k₁ k₂) (Nat.floor (a n)) (not_lt.mp hcon)
        (kmtM_le_heightScale hni))
    have hlt : ((logN (Nat.floor (a n)) : ℤ) : ℝ) < Lg := by
      have h1 : ¬ ((kmtM l₁ l₂ k₁ k₂ : ℝ) + R * (2 : ℝ) ^ (ρ * (kmtM l₁ l₂ k₁ k₂ : ℝ)) + 2
          ≤ ((logN (Nat.floor (a n)) : ℤ) : ℝ)) := hnot
      push_neg at h1
      rw [hLgdef]
      have hMle : (kmtM l₁ l₂ k₁ k₂ : ℝ) ≤ (B₀ : ℝ) := by exact_mod_cast le_of_lt hMB
      have hexp : (2 : ℝ) ^ (ρ * (kmtM l₁ l₂ k₁ k₂ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (B₀ : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hρ.le, hMle])
      have := mul_le_mul_of_nonneg_left hexp hR0
      linarith
    have hKgle : logN (Nat.floor (a n)) ≤ (KgN : ℤ) := by
      have h3 : ((logN (Nat.floor (a n)) : ℤ) : ℝ) < (KgN : ℝ) := by linarith
      exact_mod_cast le_of_lt h3
    have h4 : Nat.log 2 (max (Nat.floor (a n)) 2) ≤ KgN := by
      have hK := hKgle
      simp only [logN] at hK
      exact_mod_cast hK
    have h5 : max (Nat.floor (a n)) 2 < 2 ^ (KgN + 1) := by
      calc max (Nat.floor (a n)) 2
          < 2 ^ (Nat.log 2 (max (Nat.floor (a n)) 2) + 1) :=
            Nat.lt_pow_succ_log_self (by norm_num) _
        _ ≤ 2 ^ (KgN + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h6 : Nat.floor (a n) < Nth := by
      rw [hNthdef]; exact lt_of_le_of_lt (le_max_left _ _) h5
    have h7 : a n < ((Nth : ℕ) : ℝ≥0) := by
      have := Nat.lt_floor_add_one (a n)
      have h8 : (Nat.floor (a n) + 1 : ℕ) ≤ Nth := h6
      calc a n < (Nat.floor (a n) : ℝ≥0) + 1 := this
        _ ≤ (Nth : ℝ≥0) := by exact_mod_cast h8
    exact_mod_cast h7
  have hcard_le : ∀ s : Finset ℕ, (∀ n ∈ s, hhBad R ρ C₀ a l₁ l₂ k₁ k₂ n) →
      (s.card : ℝ) ≤ Real.log (Nth : ℝ) / Real.log (Λ : ℝ) + 1 := by
    intro s hs
    exact lacunaryCard Λ hΛ a ha ha1 s (Nth : ℝ) hNth1 (fun n hn => hbad_lt n (hs n hn))
  have hbadsum : (∑' n : ℕ, if hhBad R ρ C₀ a l₁ l₂ k₁ k₂ n then (1 : ℝ≥0∞) else 0)
      ≤ ((Nat.ceil (Real.log (Nth : ℝ) / Real.log (Λ : ℝ) + 1) : ℕ) : ℝ≥0∞) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    refine iSup_le (fun s => ?_)
    have h1 : ∑ n ∈ s, (if hhBad R ρ C₀ a l₁ l₂ k₁ k₂ n then (1 : ℝ≥0∞) else 0)
        = (((s.filter (hhBad R ρ C₀ a l₁ l₂ k₁ k₂)).card : ℕ) : ℝ≥0∞) := by
      rw [← Finset.sum_filter]
      simp
    rw [h1]
    have h2 : (s.filter (hhBad R ρ C₀ a l₁ l₂ k₁ k₂)).card
        ≤ Nat.ceil (Real.log (Nth : ℝ) / Real.log (Λ : ℝ) + 1) := by
      have h3 := hcard_le (s.filter (hhBad R ρ C₀ a l₁ l₂ k₁ k₂))
        (fun n hn => (Finset.mem_filter.mp hn).2)
      have h4 := Nat.le_ceil (Real.log (Nth : ℝ) / Real.log (Λ : ℝ) + 1)
      exact_mod_cast le_trans h3 h4
    exact_mod_cast h2
  have hr1 : 1 ≤ r := le_of_lt (lt_of_le_of_lt (by norm_num) hr)
  -- the degenerate cases
  rcases eq_or_ne (eLpNorm f 2 Measure.count) 0 with hf0 | hf0
  · have hfz : f = 0 := eq_zero_of_eLpNorm_two_eq_zero hf0
    have hcol : (fun n : ℕ => eLpNorm (fun x : ℤ =>
        varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count) = 0 := by
      funext n
      have h1 : (fun x : ℤ => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
        funext x
        rw [hfz]
        exact congrFun (congrFun
          (varpCol_kmt_zero_left ρ P P.natDegree C₀ a l₁ l₂ k₁ k₂ g) n) x
      rw [h1]
      simp
    have hb := eLpNorm_variationalNorm_one_le_tsum (r := r) hr1
      (fun n x => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)
    have hsum0 : (∑' n : ℕ, eLpNorm (fun x : ℤ =>
        varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count) = 0 :=
      ENNReal.tsum_eq_zero.mpr (fun n => by
        have := congrFun hcol n
        simpa using this)
    rw [hsum0, mul_zero] at hb
    exact hb.trans (zero_le)
  rcases eq_or_ne (eLpNorm g 2 Measure.count) 0 with hg0 | hg0
  · have hgz : g = 0 := eq_zero_of_eLpNorm_two_eq_zero hg0
    have hcol : (fun n : ℕ => eLpNorm (fun x : ℤ =>
        varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count) = 0 := by
      funext n
      have h1 : (fun x : ℤ => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
        funext x
        rw [hgz]
        exact congrFun (congrFun
          (varpCol_kmt_zero_right ρ P P.natDegree C₀ a l₁ l₂ k₁ k₂ f) n) x
      rw [h1]
      simp
    have hb := eLpNorm_variationalNorm_one_le_tsum (r := r) hr1
      (fun n x => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)
    have hsum0 : (∑' n : ℕ, eLpNorm (fun x : ℤ =>
        varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count) = 0 :=
      ENNReal.tsum_eq_zero.mpr (fun n => by
        have := congrFun hcol n
        simpa using this)
    rw [hsum0, mul_zero] at hb
    exact hb.trans (zero_le)
  rcases eq_or_ne (eLpNorm f 2 Measure.count) ⊤ with hftop | hftop
  · have hne : CL * ENNReal.ofReal (hhWeight (cI / 2) l₁ l₂ k₁ k₂) ≠ 0 :=
      mul_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hCL1)) hWne
    have hRHS : ((hhConst cI CI BF BG Nth CFc CGc B₀ Λ : ℝ≥0) : ℝ≥0∞)
        * ENNReal.ofReal ((fun l₁ l₂ k₁ k₂ =>
            (2 : ℝ) ^ (-(cI / 2 * (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ)))) l₁ l₂ k₁ k₂)
        * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count = ⊤ := by
      rw [show (fun l₁ l₂ k₁ k₂ =>
            (2 : ℝ) ^ (-(cI / 2 * (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ)))) l₁ l₂ k₁ k₂
          = hhWeight (cI / 2) l₁ l₂ k₁ k₂ from (hhWeight_eq (cI / 2) l₁ l₂ k₁ k₂).symm]
      rw [hCeq, hftop, ENNReal.mul_top hne, ENNReal.top_mul hg0]
    rw [hRHS]
    exact le_top
  rcases eq_or_ne (eLpNorm g 2 Measure.count) ⊤ with hgtop | hgtop
  · have hne : CL * ENNReal.ofReal (hhWeight (cI / 2) l₁ l₂ k₁ k₂) ≠ 0 :=
      mul_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hCL1)) hWne
    have hRHS : ((hhConst cI CI BF BG Nth CFc CGc B₀ Λ : ℝ≥0) : ℝ≥0∞)
        * ENNReal.ofReal ((fun l₁ l₂ k₁ k₂ =>
            (2 : ℝ) ^ (-(cI / 2 * (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ)))) l₁ l₂ k₁ k₂)
        * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count = ⊤ := by
      rw [show (fun l₁ l₂ k₁ k₂ =>
            (2 : ℝ) ^ (-(cI / 2 * (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ)))) l₁ l₂ k₁ k₂
          = hhWeight (cI / 2) l₁ l₂ k₁ k₂ from (hhWeight_eq (cI / 2) l₁ l₂ k₁ k₂).symm]
      rw [hCeq, hgtop, ENNReal.mul_top (mul_ne_zero hne hf0)]
    rw [hRHS]
    exact le_top
  -- the main case
  have hfmem : MemLp f 2 Measure.count :=
    MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hftop)
  have hgmem : MemLp g 2 Measure.count :=
    MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hgtop)
  -- the main case
  have hfmem : MemLp f 2 Measure.count :=
    MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hftop)
  have hgmem : MemLp g 2 Measure.count :=
    MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hgtop)
  have hHK : 1 ≤ k₁ ∧ 1 ≤ k₂ := hHH
  set W : ℝ≥0∞ := ENNReal.ofReal (hhWeight (cI / 2) l₁ l₂ k₁ k₂) with hWdef
  set Kg : ℝ≥0∞ := hhGainCoeff cI CI with hKgdef
  set Kc : ℝ≥0∞ := ((CFc * CGc : ℝ≥0) : ℝ≥0∞) with hKcdef
  set KbU : ℕ := Nat.ceil (Real.log (Nth : ℝ) / Real.log (Λ : ℝ) + 1) with hKbUdef
  set F : ℝ≥0∞ := eLpNorm f 2 Measure.count with hFdef
  set G : ℝ≥0∞ := eLpNorm g 2 Measure.count with hGdef
  set φ : ℕ → ℝ≥0∞ := fun n => eLpNorm
    (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f) 2 Measure.count with hφdef
  set ψ : ℕ → ℝ≥0∞ := fun n => eLpNorm
    (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g) 2 Measure.count with hψdef
  -- the two computations used by the bad-scale part
  have hMB_of : ∀ n : ℕ, inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) →
      ¬ hhGood R ρ (kmtM l₁ l₂ k₁ k₂) (Nat.floor (a n)) → kmtM l₁ l₂ k₁ k₂ < B₀ := by
    intro n hni hnot
    by_contra hcon
    exact hnot (hB₀ (kmtM l₁ l₂ k₁ k₂) (Nat.floor (a n)) (not_lt.mp hcon)
      (kmtM_le_heightScale hni))
  have hloglt_of : ∀ n : ℕ, kmtM l₁ l₂ k₁ k₂ < B₀ →
      ¬ hhGood R ρ (kmtM l₁ l₂ k₁ k₂) (Nat.floor (a n)) →
      ((logN (Nat.floor (a n)) : ℤ) : ℝ) < Lg := by
    intro n hMB hnot
    have h1 : ¬ ((kmtM l₁ l₂ k₁ k₂ : ℝ) + R * (2 : ℝ) ^ (ρ * (kmtM l₁ l₂ k₁ k₂ : ℝ)) + 2
        ≤ ((logN (Nat.floor (a n)) : ℤ) : ℝ)) := hnot
    push_neg at h1
    rw [hLgdef]
    have hMle : (kmtM l₁ l₂ k₁ k₂ : ℝ) ≤ (B₀ : ℝ) := by exact_mod_cast le_of_lt hMB
    have hexp : (2 : ℝ) ^ (ρ * (kmtM l₁ l₂ k₁ k₂ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (B₀ : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [hρ.le, hMle])
    have := mul_le_mul_of_nonneg_left hexp hR0
    linarith
  -- the per-index estimate
  have hterm : ∀ n : ℕ, eLpNorm (fun x : ℤ =>
      varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count
      ≤ (if hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n then Kg * W * φ n * ψ n
          else if inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
            then Kc * F * G else 0) := by
    intro n
    by_cases hP : hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n
    · rw [if_pos hP]
      obtain ⟨hind, hgd⟩ := hP
      have hFm := memLp_Fpiece_of hmem_ax ρ l₁ k₁ (Nat.floor (a n)) hfmem
      have hGm := memLp_Gpiece_of hmem_ax ρ (P.natDegree : ℤ) l₂ k₂ (Nat.floor (a n)) hgmem
      by_cases hexc : l₁ = 0 ∧ l₂ = 0 ∧ k₁ = 1 ∧ k₂ = 1
      · obtain ⟨h1, h2, h3, h4⟩ := hexc
        have hanf := eLpNorm_varpCol_le (P := P) (C₀ := C₀) (a := a)
          (f := f) (g := g) (l₁ := l₁) (l₂ := l₂) (k₁ := k₁) (k₂ := k₂) (n := n)
          hind hFm hGm
        have hone : (1 : ℝ≥0∞) ≤ Kg * W := by
          have hw : (2 : ℝ) ^ (cI / 2) * hhWeight (cI / 2) l₁ l₂ k₁ k₂ = 1 := by
            rw [h1, h2, h3, h4]
            exact rpow_exc_eq cI
          have h2' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 : ℝ) ^ (cI / 2)) * W := by
            rw [hWdef, ← ENNReal.ofReal_mul (by positivity), hw, ENNReal.ofReal_one]
          refine le_trans h2' ?_
          rw [hKgdef, hhGainCoeff, hWdef]
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le) zero_le
        calc eLpNorm (fun x : ℤ => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)
              1 Measure.count ≤ φ n * ψ n := by
              rw [hφdef, hψdef]; exact hanf
          _ = 1 * (φ n * ψ n) := (one_mul _).symm
          _ ≤ (Kg * W) * (φ n * ψ n) := mul_le_mul_of_nonneg_right hone zero_le
          _ = Kg * W * φ n * ψ n := by ac_rfl
      · have hval : 1 ≤ l₁ ∨ 2 ≤ k₁ ∨ 1 ≤ l₂ ∨ 2 ≤ k₂ := by
          by_contra hcon
          push_neg at hcon
          exact hexc ⟨by omega, by omega, by omega, by omega⟩
        obtain ⟨L, hLM, hML, hside⟩ := exists_height_cases l₁ l₂ k₁ k₂ hval
        have hvan : (kmtProj ρ L (-(logN (Nat.floor (a n))) + (L : ℤ))
              (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f) = 0) ∨
            (kmtProj ρ L ((P.natDegree : ℤ) * (-(logN (Nat.floor (a n))) + (L : ℤ)))
              (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g) = 0) := by
          rcases hside with hF | hG
          · exact Or.inl (hvanF_ax ρ R CNA hρ hρ1 hR1 hRCNA hNA' hvanF l₁ k₁ L
              (Nat.floor (a n)) (kmtM l₁ l₂ k₁ k₂) f hHK.1 hF hLM
              (kmtM_ge_k₁ l₁ l₂ k₁ k₂) (kmtM_ge_l₁ l₁ l₂ k₁ k₂) hgd hfmem)
          · exact Or.inr (hvanG_ax ρ R CNA hρ hρ1 hR1 hRCNA hNA' hvanG P hd l₂ k₂ L
              (Nat.floor (a n)) (kmtM l₁ l₂ k₁ k₂) g hHK.2 hG hLM
              (kmtM_ge_k₂ l₁ l₂ k₁ k₂) (kmtM_ge_l₂ l₁ l₂ k₁ k₂) hgd hgmem)
        have hsg := singleScaleGain (P := P) hρ hρ1 hcI hR1 (hlog cI hcI R hR1) hI
          (ha1 n) hML hgd hind hFm hGm hvan
        rw [hKgdef, hWdef, hφdef, hψdef]
        exact hsg
    · rw [if_neg hP]
      by_cases hind : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
      · rw [if_pos hind]
        have hnotgd : ¬ hhGood R ρ (kmtM l₁ l₂ k₁ k₂) (Nat.floor (a n)) :=
          fun hg => hP ⟨hind, hg⟩
        have hMB := hMB_of n hind hnotgd
        have hloglt := hloglt_of n hMB hnotgd
        have hKgle : logN (Nat.floor (a n)) ≤ (KgN : ℤ) := by
          have h3 : ((logN (Nat.floor (a n)) : ℤ) : ℝ) < (KgN : ℝ) := by linarith
          exact_mod_cast le_of_lt h3
        have hFm := memLp_Fpiece_of hmem_ax ρ l₁ k₁ (Nat.floor (a n)) hfmem
        have hGm := memLp_Gpiece_of hmem_ax ρ (P.natDegree : ℤ) l₂ k₂ (Nat.floor (a n)) hgmem
        have hanf := eLpNorm_varpCol_le (P := P) (C₀ := C₀) (a := a)
          (f := f) (g := g) (l₁ := l₁) (l₂ := l₂) (k₁ := k₁) (k₂ := k₂) (n := n)
          hind hFm hGm
        have hl1B : l₁ ≤ B₀ := le_trans (kmtM_ge_l₁ l₁ l₂ k₁ k₂) (le_of_lt hMB)
        have hl2B : l₂ ≤ B₀ := le_trans (kmtM_ge_l₂ l₁ l₂ k₁ k₂) (le_of_lt hMB)
        have hk1B : k₁ ≤ B₀ := le_trans (kmtM_ge_k₁ l₁ l₂ k₁ k₂) (le_of_lt hMB)
        have hk2B : k₂ ≤ B₀ := le_trans (kmtM_ge_k₂ l₁ l₂ k₁ k₂) (le_of_lt hMB)
        have hflog : (0 : ℤ) ≤ logN (Nat.floor (a n)) := logN_nonneg _
        have hφle : φ n ≤ (CFc : ℝ≥0∞) * F := by
          rw [hφdef, hFdef]
          refine hCFc l₁ k₁ (Nat.floor (a n)) f hl1B ?_ ?_
          · have := hKgle
            omega
          · omega
        have hψle : ψ n ≤ (CGc : ℝ≥0∞) * G := by
          rw [hψdef, hGdef]
          refine hCGc l₂ k₂ (Nat.floor (a n)) g ?_ ?_ ?_
          · exact le_trans hl2B (Nat.le_mul_of_pos_left B₀ (by omega))
          · have hd0 : (0 : ℤ) ≤ (P.natDegree : ℤ) := by
              exact_mod_cast Nat.zero_le P.natDegree
            have hK2 : (0 : ℤ) ≤ (k₂ : ℤ) := by exact_mod_cast Nat.zero_le k₂
            have hL1 : (1 : ℤ) ≤ (P.natDegree : ℤ) := by
              have := hd; omega
            have := hKgle
            push_cast
            nlinarith
          · have hd0 : (0 : ℤ) ≤ (P.natDegree : ℤ) := by
              exact_mod_cast Nat.zero_le P.natDegree
            have hK2 : (0 : ℤ) ≤ (k₂ : ℤ) := by exact_mod_cast Nat.zero_le k₂
            have := hk2B
            have := hflog
            push_cast
            nlinarith
        calc eLpNorm (fun x : ℤ => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)
              1 Measure.count ≤ φ n * ψ n := by
              rw [hφdef, hψdef]; exact hanf
          _ ≤ ((CFc : ℝ≥0∞) * F) * ((CGc : ℝ≥0∞) * G) := mul_le_mul' hφle hψle
          _ = Kc * F * G := by
              rw [hKcdef, ENNReal.coe_mul]; ac_rfl
      · rw [if_neg hind]
        have h1 : (fun x : ℤ => varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x) = 0 := by
          funext x
          rw [varpCol_apply, if_neg hind]
          rfl
        rw [h1]
        simp
  -- the sum over the scales
  have hsum : (∑' n : ℕ, eLpNorm (fun x : ℤ =>
        varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count)
      ≤ Kg * W * (∑' n : ℕ, if hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n then φ n * ψ n else 0)
        + (Kc * F * G) * (∑' n : ℕ, if hhBad R ρ C₀ a l₁ l₂ k₁ k₂ n then (1 : ℝ≥0∞) else 0) := by
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    have hpt : ∀ n : ℕ,
        (if hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n then Kg * W * φ n * ψ n
          else if inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
            then Kc * F * G else 0)
        = (if hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n then Kg * W * φ n * ψ n else 0)
          + (if hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n then 0
             else if inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
               then Kc * F * G else 0) := by
      intro n
      by_cases h : hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n <;> simp [h]
    rw [tsum_congr hpt, ENNReal.tsum_add]
    refine add_le_add ?_ ?_
    · rw [← ENNReal.tsum_mul_left]
      refine ENNReal.tsum_le_tsum (fun n => ?_)
      by_cases h : hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n
      · rw [if_pos h, if_pos h]
        exact le_of_eq (by ac_rfl)
      · rw [if_neg h, if_neg h]
        simp
    · rw [← ENNReal.tsum_mul_left]
      refine le_of_eq (tsum_congr (fun n => ?_))
      by_cases h : hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n
      · rw [if_pos h]
        have hb : ¬ hhBad R ρ C₀ a l₁ l₂ k₁ k₂ n := fun hb => hb.1 h
        rw [if_neg hb, mul_zero]
      · rw [if_neg h]
        by_cases hind : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
        · rw [if_pos hind]
          have hb : hhBad R ρ C₀ a l₁ l₂ k₁ k₂ n := ⟨h, hind⟩
          rw [if_pos hb, mul_one]
        · rw [if_neg hind]
          have hb : ¬ hhBad R ρ C₀ a l₁ l₂ k₁ k₂ n := fun hb => hind hb.2
          rw [if_neg hb, mul_zero]
  -- the Cauchy--Schwarz / Bessel step
  have hCS : (∑' n : ℕ, if hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n then φ n * ψ n else 0)
      ≤ (BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞) * F * G := by
    refine hCS_ax φ ψ (hhPm R ρ C₀ a l₁ l₂ k₁ k₂) (BF Λ : ℝ≥0∞) (BG Λ : ℝ≥0∞) F G ?_ ?_
    · intro s hs
      have hb := hbesF' l₁ k₁ hHK.1 a Λ hΛ ha ha1 s f hfmem (fun n hn => ?_)
      · rw [hFdef]
        exact hb
      · have hgd' : (kmtM l₁ l₂ k₁ k₂ : ℝ)
            + R * (2 : ℝ) ^ (ρ * (kmtM l₁ l₂ k₁ k₂ : ℝ)) + 2
            ≤ ((logN (Nat.floor (a n)) : ℤ) : ℝ) := (hs n hn).2
        have h1 : ((max l₁ k₁ : ℕ) : ℝ) ≤ (kmtM l₁ l₂ k₁ k₂ : ℝ) := by
          exact_mod_cast max_le (kmtM_ge_l₁ l₁ l₂ k₁ k₂) (kmtM_ge_k₁ l₁ l₂ k₁ k₂)
        have h2 : CF * (2 : ℝ) ^ (ρ * (l₁ : ℝ))
            ≤ R * (2 : ℝ) ^ (ρ * (kmtM l₁ l₂ k₁ k₂ : ℝ)) := by
          refine mul_le_mul hRCF ?_ (by positivity) hR0
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have h3 : (l₁ : ℝ) ≤ (kmtM l₁ l₂ k₁ k₂ : ℝ) := by
            exact_mod_cast le_trans (le_max_left l₁ l₂) (le_max_left _ _)
          nlinarith [hρ.le]
        linarith [hgd']
    · intro s hs
      have hb := hbesG' l₂ k₂ hHK.2 a Λ hΛ ha ha1 s g hgmem (fun n hn => ?_)
      · rw [hGdef]
        exact hb
      · have hgd' : (kmtM l₁ l₂ k₁ k₂ : ℝ)
            + R * (2 : ℝ) ^ (ρ * (kmtM l₁ l₂ k₁ k₂ : ℝ)) + 2
            ≤ ((logN (Nat.floor (a n)) : ℤ) : ℝ) := (hs n hn).2
        have h1 : ((max l₂ k₂ : ℕ) : ℝ) ≤ (kmtM l₁ l₂ k₁ k₂ : ℝ) := by
          exact_mod_cast max_le (kmtM_ge_l₂ l₁ l₂ k₁ k₂) (kmtM_ge_k₂ l₁ l₂ k₁ k₂)
        have h2 : CG * (2 : ℝ) ^ (ρ * (l₂ : ℝ))
            ≤ R * (2 : ℝ) ^ (ρ * (kmtM l₁ l₂ k₁ k₂ : ℝ)) := by
          refine mul_le_mul hRCG ?_ (by positivity) hR0
          refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
          have h3 : (l₂ : ℝ) ≤ (kmtM l₁ l₂ k₁ k₂ : ℝ) := by
            exact_mod_cast le_trans (le_max_right l₁ l₂) (le_max_left _ _)
          nlinarith [hρ.le]
        linarith [hgd']
  have hbadsumK : (∑' n : ℕ, if hhBad R ρ C₀ a l₁ l₂ k₁ k₂ n then (1 : ℝ≥0∞) else 0)
      ≤ (KbU : ℝ≥0∞) := by
    rw [hKbUdef]
    exact hbadsum
  -- the final arithmetic
  by_cases hMB₀ : kmtM l₁ l₂ k₁ k₂ ≤ B₀
  · have hZW : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((2 : ℝ) ^ (cI / 2 * (B₀ : ℝ))) * W := by
      rw [hWdef, hhWeight, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      refine Real.one_le_rpow (by norm_num) ?_
      have hMle : ((kmtM l₁ l₂ k₁ k₂ : ℕ) : ℝ) ≤ (B₀ : ℝ) := by exact_mod_cast hMB₀
      nlinarith [le_of_lt hcI]
    -- the two arithmetic comparisons
    have hle1 : Kg * W * ((BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞) * F * G)
        = (Kg * (BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞)) * (W * F * G) := by ac_rfl
    have hle2 : (Kc * F * G) * (KbU : ℝ≥0∞)
        ≤ (Kc * (KbU : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (cI / 2 * (B₀ : ℝ))))
            * (W * F * G) := by
      calc (Kc * F * G) * (KbU : ℝ≥0∞)
          = (Kc * (KbU : ℝ≥0∞)) * (F * G) := by ac_rfl
        _ ≤ (Kc * (KbU : ℝ≥0∞))
              * ((ENNReal.ofReal ((2 : ℝ) ^ (cI / 2 * (B₀ : ℝ))) * W) * (F * G)) :=
            mul_le_mul_of_nonneg_left (le_mul_of_one_le_left zero_le hZW) zero_le
        _ = (Kc * (KbU : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (cI / 2 * (B₀ : ℝ)))
              * (W * F * G)) := by ac_rfl
    have hsumK : (∑' n : ℕ, eLpNorm (fun x : ℤ =>
          varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count)
        ≤ Kg * W * (∑' n : ℕ, if hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n then φ n * ψ n else 0)
          + (Kc * F * G) * (KbU : ℝ≥0∞) :=
      hsum.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hbadsumK zero_le))
    have hfinal0 : Kg * W * ((BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞) * F * G)
          + (Kc * F * G) * (KbU : ℝ≥0∞)
        ≤ (Kg * (BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞)
            + Kc * (KbU : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (cI / 2 * (B₀ : ℝ))) + 1)
          * (W * F * G) := by
      rw [hle1]
      refine le_trans (add_le_add le_rfl hle2) ?_
      rw [add_mul, add_mul, one_mul]
      exact le_add_of_nonneg_right zero_le
    calc eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
            varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
        ≤ 3 * (Kg * W * (∑' n : ℕ, if hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n then φ n * ψ n else 0)
            + (Kc * F * G) * (KbU : ℝ≥0∞)) := by
          refine (eLpNorm_variationalNorm_one_le_tsum (r := r) hr1 _).trans ?_
          exact mul_le_mul_of_nonneg_left hsumK zero_le
      _ ≤ 3 * (Kg * W * ((BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞) * F * G)
            + (Kc * F * G) * (KbU : ℝ≥0∞)) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          exact add_le_add (mul_le_mul_of_nonneg_left hCS zero_le) le_rfl
      _ ≤ 3 * ((Kg * (BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞)
            + Kc * (KbU : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (cI / 2 * (B₀ : ℝ))) + 1)
            * (W * F * G)) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          exact hfinal0
      _ = CL * W * F * G := by
          rw [hCLdef]
          ac_rfl
      _ = ((hhConst cI CI BF BG Nth CFc CGc B₀ Λ : ℝ≥0) : ℝ≥0∞)
            * ENNReal.ofReal ((fun l₁ l₂ k₁ k₂ =>
                (2 : ℝ) ^ (-(cI / 2 * (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ)))) l₁ l₂ k₁ k₂)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
          rw [hCeq, hWdef, hFdef, hGdef, hhWeight_eq]
  · -- the bad part is empty
    have hMlt : B₀ < kmtM l₁ l₂ k₁ k₂ := not_le.mp hMB₀
    have hbadzero : (∑' n : ℕ, if hhBad R ρ C₀ a l₁ l₂ k₁ k₂ n then (1 : ℝ≥0∞) else 0) = 0 := by
      refine ENNReal.tsum_eq_zero.mpr (fun n => ?_)
      by_cases h : hhBad R ρ C₀ a l₁ l₂ k₁ k₂ n
      · exfalso
        exact h.1 ⟨h.2, hB₀ (kmtM l₁ l₂ k₁ k₂) (Nat.floor (a n)) (le_of_lt hMlt)
          (kmtM_le_heightScale h.2)⟩
      · simp [h]
    have hCLlow : Kg * (BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞) ≤ CL := by
      rw [hCLdef]
      refine le_trans ?_ (le_mul_of_one_le_left zero_le (by norm_num))
      exact le_trans (le_add_of_nonneg_right zero_le) (le_add_of_nonneg_right zero_le)
    have hKgBF : Kg * W * ((BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞) * F * G)
        = (Kg * (BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞)) * (W * F * G) := by ac_rfl
    have hsumK : (∑' n : ℕ, eLpNorm (fun x : ℤ =>
          varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x) 1 Measure.count)
        ≤ Kg * W * (∑' n : ℕ, if hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n then φ n * ψ n else 0) :=
      hsum.trans (by rw [hbadzero, mul_zero, add_zero])
    calc eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
            varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x)) 1 Measure.count
        ≤ 3 * (Kg * W * (∑' n : ℕ, if hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n then φ n * ψ n else 0)) := by
          refine (eLpNorm_variationalNorm_one_le_tsum (r := r) hr1 _).trans ?_
          exact mul_le_mul_of_nonneg_left hsumK zero_le
      _ ≤ 3 * ((Kg * (BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞)) * (W * F * G)) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          calc Kg * W * (∑' n : ℕ, if hhPm R ρ C₀ a l₁ l₂ k₁ k₂ n then φ n * ψ n else 0)
              ≤ Kg * W * ((BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞) * F * G) :=
                mul_le_mul_of_nonneg_left hCS zero_le
            _ = (Kg * (BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞)) * (W * F * G) := by ac_rfl
      _ ≤ 3 * ((Kg * (BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞) + 1) * (W * F * G)) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le) zero_le
      _ ≤ 3 * ((Kg * (BF Λ : ℝ≥0∞) * (BG Λ : ℝ≥0∞)
            + Kc * (KbU : ℝ≥0∞) * ENNReal.ofReal ((2 : ℝ) ^ (cI / 2 * (B₀ : ℝ))) + 1)
            * (W * F * G)) := by
          refine mul_le_mul_of_nonneg_left ?_ zero_le
          refine mul_le_mul_of_nonneg_right ?_ zero_le
          exact add_le_add (le_add_of_nonneg_right zero_le) le_rfl
      _ = CL * W * F * G := by
          rw [hCLdef]
          ac_rfl
      _ = ((hhConst cI CI BF BG Nth CFc CGc B₀ Λ : ℝ≥0) : ℝ≥0∞)
            * ENNReal.ofReal ((fun l₁ l₂ k₁ k₂ =>
                (2 : ℝ) ^ (-(cI / 2 * (lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) : ℝ)))) l₁ l₂ k₁ k₂)
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
          rw [hCeq, hWdef, hFdef, hGdef, hhWeight_eq]

end

end Work.KMTPlan.A6
