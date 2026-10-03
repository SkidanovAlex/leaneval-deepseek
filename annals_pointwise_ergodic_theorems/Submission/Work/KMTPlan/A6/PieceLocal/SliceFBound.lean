/-
# `Work.KMTPlan.A6.PieceBoundedH.sliceFBound` — the bounded-height packet estimate for the
`f`-side carrier

This file proves the `f`-side bounded-height packet estimate `SliceFBound r C₀ ρ B` of
`Submission/Work/KMTPlan/A6/PieceBoundedH/Defs.lean`: uniformly in the `Λ`-lacunary family `a`, in
the quadruple with `lcL l₁ l₂ k₁ k₂ ≤ B`, in `t ∈ [1/2,1]` and in `f`,

  `‖ Vʳ (n ↦ 1_{core n} · T^{≤l₁}_{φ_{N_n,t}}(Π_{l₁,≤-u}f)) ‖_{ℓ²(ℤ)} ≤ K(Λ) ‖f‖_{ℓ²(ℤ)}`,

where the constant `K` may depend on `Λ`, `ρ`, `B` and `r`.

## The decomposition

Everything rests on the two *proved* halves of the paper's linear lacunary estimate at bounded
height, and on the *proved* vanishing-case machine:

* **`k₁ ≥ 1`.**  There the modified bump `φ_{N_n,t} = φ_{N_n}e(N_n t·)` is *narrow* and its signed
  sums are uniformly bounded by `MdlLinVarphiNtjSupBound Λ hΛ` (a constant depending on `Λ` only);
  the `ℓ²`-variational estimate is then `mdlVanishingCaseUnif`
  (`MdlSliceLinF.lean`, proved and axiom-clean).

* **`k₁ = 0`.**  Here `φ_{N,t} = φ_N + (φ_{N,t} - φ_N)` and, for *bounded* input (which is what
  occurs: `mdlF ρ u l₁ f ∈ ℓ²` hence bounded), `Tle` is additive in the symbol
  (`A7LoLin.Tle_add_of_bounded`).  So the variational norm splits into
  * the **unmodulated low-pass family** `n ↦ kmtProj ρ l₁ (-(Log N_n)) g`, i.e. the low-pass walk
      `m ↦ lpf ρ l₁ m₀ m g` at the levels `Log N_n` — bounded here by `walkVarBound` below, which
      is the `#(iwArithFreqs ρ l₁)`-lossy route (`chainPart` by the proved
      `eLpNorm_chainPart_le_uniform`, values-supremum by the telescoping
      `supPart ≤ ‖T_0‖ + chainPart 3` of `A7G.maximalLowpass`, `‖T_0‖` by the trivial
      single-scale symbol bound of `mdlF_two_le.lean`).  At bounded height the loss
      `#(iwArithFreqs ρ B)` is a constant, and — crucially — this route works for *every*
      `ρ ∈ (0,1]`, with no good-major-arcs hypothesis;
  * the **difference family** `n ↦ Tle ρ l₁ (φ_{N_n,t} - φ_{N_n}) g`, bounded by the proved
      `mdlDiffFamilyAll` (`PieceBoundedH/diffFamilyAll.lean`, the global-height form of
      `MdlSliceLinF`'s `mdlDiffFamily_local`; the difference vanishes at the origin, so its signed
      sums are bounded by `varphiNtDiffSupBound`).

The `Λ`-lacunary sequence is compared with the *full* level walk (all `m ∈ ℕ`, which is
`2`-lacunary by construction) by monotone reindexing (`A7.variationalNorm_comp_mono_le`), and the
clipping at the core condition (a suffix of `ℕ`, `mdlCore_of_le`) by
`Work.KMTPlan.A6.variationalNorm_prefix_zero_le`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.PieceBoundedH.Defs
import Submission.Work.KMTPlan.A6.PieceBoundedH.diffFamilyAll
import Submission.Work.KMTPlan.A6.variationalNorm_prefix_zero_le
import Submission.Work.KMTPlan.A6.PieceLocal.StaleA7GAliases
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6.PieceLocal

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar Work.Analysis.IonescuWainger
open Work.KMTPlan.A6.PieceBoundedH

/-! ## Preliminary: `MemLp` on the counting measure gives a summable `ℓ²`-series -/

/-- `MemLp g 2 count` implies `Summable (fun n => ‖g n‖ ^ (2 : ℝ))`. -/
theorem summable_of_memLp_two {g : ℤ → ℂ} (hg : MemLp g 2 Measure.count) :
    Summable (fun n : ℤ => ‖g n‖ ^ (2 : ℝ)) := by
  have hmem := Work.KMTPlan.A6.memlpOfMemLpCount (by norm_num : (2 : ENNReal) ≠ 0)
    (by norm_num : (2 : ENNReal) ≠ ⊤) hg
  have h := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)).mp hmem
  simpa using h

/-! ## The `#(iwArithFreqs ρ l₁)`-uniform chain-part bound for the low-pass walk -/

/-- **The chain part of the low-pass walk is bounded on `ℓ²`, uniformly in `l₁ ≤ B` and in the
base level `m₀`.**  This is `Work.KMTAreas.A7Hi.eLpNorm_chainPart_le_uniform` at `p = 2` with the
constant made explicit: `(1 + #(iwArithFreqs ρ B)) C'`, `C'` from `A7Hi.DilVarClean`. -/
theorem walkChainPartBound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ : ℕ), l₁ ≤ B → ∀ (m₀ : ℕ) (g : ℤ → ℂ),
      Summable (fun n : ℤ => ‖g n‖ ^ (2 : ℝ)) →
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m g x)) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  obtain ⟨C', hC'pos, hC'⟩ := Work.KMTAreas.A7Hi.DilVarClean (2 : ℝ) (by norm_num) r hr
    Work.KMTAreas.A7Hi.kmtPhiSch
  refine ⟨(1 + ((iwArithFreqs ρ B).card : ℝ)) * C', by positivity, ?_⟩
  intro l₁ hl₁ m₀ g hg
  have hpt := Work.KMTAreas.A7Hi2.chainPart_le_sum_variationalNorm ρ l₁ m₀ r hr
    (2 : ENNReal) (by norm_num) (by norm_num) g (by simpa using hg)
  have h1 : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m g x)) 2 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
          ∑ α ∈ iwArithFreqs ρ l₁,
            variationalNorm r (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam
              Work.KMTAreas.A7Hi.kmtPhiSch (Work.KMTAreas.A7Hi.lpfScale m₀)
              (Work.KMTAreas.A7Hi.charMul α g) m x))
        2 MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by simpa only [enorm_eq_self] using hpt x)
  have h2 : MeasureTheory.eLpNorm (fun x : ℤ =>
          ∑ α ∈ iwArithFreqs ρ l₁,
            variationalNorm r (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam
              Work.KMTAreas.A7Hi.kmtPhiSch (Work.KMTAreas.A7Hi.lpfScale m₀)
              (Work.KMTAreas.A7Hi.charMul α g) m x))
        2 MeasureTheory.Measure.count
      ≤ ∑ α ∈ iwArithFreqs ρ l₁,
          MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
            (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
              (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.charMul α g) m x))
            2 MeasureTheory.Measure.count :=
    Commons.MeasureTheory.Lp.eLpNorm_finset_sum_le_ennreal (by norm_num)
      (fun α _ => (measurable_of_countable _).aemeasurable)
  have h3 : ∀ α ∈ iwArithFreqs ρ l₁,
      MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r
          (fun m : ℕ => Work.KMTAreas.A7Hi.dilFam Work.KMTAreas.A7Hi.kmtPhiSch
            (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.charMul α g) m x))
        2 MeasureTheory.Measure.count
      ≤ ENNReal.ofReal C' * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    intro α _
    have hD := hC' (Work.KMTAreas.A7Hi.lpfScale m₀) (Work.KMTAreas.A7Hi.lpfScale_pos m₀)
      (Work.KMTAreas.A7Hi.lpfScale_lacunary m₀) (Work.KMTAreas.A7Hi.charMul α g)
    rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) from by norm_num]
    refine hD.trans (le_of_eq ?_)
    congr 1
    refine MeasureTheory.eLpNorm_congr_norm_ae (hf := by pw_aesm) (hg := by pw_aesm) (Filter.Eventually.of_forall fun y => ?_)
    exact Work.KMTAreas.A7Hi.norm_charMul α g y
  have hsum : (∑ _α ∈ iwArithFreqs ρ l₁,
        ENNReal.ofReal C' * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count)
      = ENNReal.ofReal (((iwArithFreqs ρ l₁).card : ℝ) * C')
        * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  refine (h1.trans (h2.trans (Finset.sum_le_sum h3))).trans ?_
  rw [hsum]
  have hcard : ((iwArithFreqs ρ l₁).card : ℝ) ≤ ((iwArithFreqs ρ B).card : ℝ) := by
    exact_mod_cast Finset.card_le_card (iwArithFreqs_mono hρ hρ1 hl₁)
  have hle : ((iwArithFreqs ρ l₁).card : ℝ) * C'
      ≤ (1 + ((iwArithFreqs ρ B).card : ℝ)) * C' := by
    have hC'nn : (0 : ℝ) ≤ C' := hC'pos.le
    nlinarith [hcard, hC'nn]
  exact mul_le_mul (ENNReal.ofReal_le_ofReal hle) le_rfl bot_le bot_le

/-! ## The single-scale bound for the low-pass projections at bounded height -/

/-- **The `ℓ²` bound for a single low-pass projection at any level `-(m₀)`**, with a constant
`2 Q²` uniform in `m₀` (the trivial symbol bound `#(iwArithFreqs ρ l') · sup|η_{≤-(m₀)}|`). -/
theorem kmtProj_l2_le (ρ : ℝ) (l' : ℕ) (Q : ℕ) (hQ : ∀ q ∈ iwP ρ l', q ≤ Q)
    (m₀ : ℕ) {g : ℤ → ℂ} (hg : MemLp g 2 Measure.count) :
    MeasureTheory.eLpNorm (Work.KMTContract.kmtProj ρ l' (-(m₀ : ℤ)) g) 2
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (((Q * Q : ℕ) : ℝ) * 2)
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  refine Work.KMTPlan.A6.eLpNorm_kmtProj_le_of_symbol (K := ((Q * Q : ℕ) : ℝ) * 2) ?_
    (by positivity) hg
  intro θ
  have h := Work.KMTPlan.A6.norm_iwSymbolSet_etaCut_le_of_card (k := -(m₀ : ℤ)) (C := 2)
    (by norm_num)
    (Work.KMTPlan.A6.norm_periodize_etaCut_le_two (-(m₀ : ℤ)) (by omega)) ρ l' Q hQ θ
  simpa using h

/-! ## The variational bound for the low-pass walk -/

/-- **The low-pass walk `m ↦ lpf ρ l₁ m₀ m g = Π_{≤l₁,≤-(m₀+m)} g` is bounded on `ℓ²`, uniformly in
`l₁ ≤ B` and in the base level `m₀`.** -/
theorem walkVarBound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r) (B : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (l₁ : ℕ), l₁ ≤ B → ∀ (m₀ : ℕ) (g : ℤ → ℂ),
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m g x))
        2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  obtain ⟨Cc3, hCc3pos, hCc3⟩ := walkChainPartBound ρ hρ hρ1 3 (by norm_num) B
  obtain ⟨Ccr, hCcrpos, hCcr⟩ := walkChainPartBound ρ hρ hρ1 r hr B
  obtain ⟨Qc, hQcpos, hQcelem⟩ := iwP_element_le hρ
  set Qbig : ℕ := Nat.ceil ((2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (B : ℝ)))) with hQbigdef
  have hQbig : ∀ (l : ℕ), l ≤ B → ∀ q ∈ iwP ρ l, q ≤ Qbig := by
    intro l hl q hq
    have h1 : (q : ℝ) ≤ (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l : ℝ))) := hQcelem l q hq
    have h2 : (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l : ℝ)))
        ≤ (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (B : ℝ))) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      refine mul_le_mul_of_nonneg_left ?_ hQcpos.le
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hl) hρ.le)
    have h3 : (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (B : ℝ))) ≤ (Qbig : ℝ) := by
      rw [hQbigdef]; exact Nat.le_ceil _
    exact_mod_cast le_trans h1 (le_trans h2 h3)
  refine ⟨((Qbig * Qbig : ℕ) : ℝ) * 2 + (Cc3 + Ccr), by positivity, ?_⟩
  intro l₁ hl₁ m₀ g hg
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  -- the pointwise bound: sup part + chain part
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m g x)
      ≤ ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 g x‖ₑ
        + (Work.KMTAreas.A7Hi.chainPart 3 (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m g x)
          + Work.KMTAreas.A7Hi.chainPart r (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m g x)) := by
    intro x
    rw [Work.KMTAreas.A7Hi.variationalNorm_eq_parts, ← add_assoc]
    refine add_le_add ?_ le_rfl
    exact (Work.KMTAreas.A7G.supPart_le_first_add_partMaxD ρ l₁ m₀ g x r).trans
      (add_le_add le_rfl (Work.KMTAreas.A7G.partMaxD_le_chainPart ρ l₁ m₀ g x))
  have hstep1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m g x)) 2 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 g x‖ₑ)
          2 MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ =>
            Work.KMTAreas.A7Hi.chainPart 3 (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m g x)
            + Work.KMTAreas.A7Hi.chainPart r
                (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m g x))
          2 MeasureTheory.Measure.count :=
    (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hpt).trans
      (MeasureTheory.eLpNorm_add_le (by norm_num))
  have hstep2 : MeasureTheory.eLpNorm (fun x : ℤ =>
        Work.KMTAreas.A7Hi.chainPart 3 (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m g x)
        + Work.KMTAreas.A7Hi.chainPart r
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m g x))
      2 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ =>
          Work.KMTAreas.A7Hi.chainPart 3 (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m g x))
          2 MeasureTheory.Measure.count
        + MeasureTheory.eLpNorm (fun x : ℤ =>
          Work.KMTAreas.A7Hi.chainPart r (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m g x))
          2 MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_add_le (by norm_num)
  have hstep3 : MeasureTheory.eLpNorm (fun x : ℤ => ‖Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 g x‖ₑ)
        2 MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 g) 2 MeasureTheory.Measure.count :=
    Work.KMTAreas.A7G.eLpNorm_enorm_eq (by norm_num) (by norm_num)
  have hsingle : MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 g) 2
        MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (((Qbig * Qbig : ℕ) : ℝ) * 2)
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    have hproj : Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ 0 g
        = Work.KMTContract.kmtProj ρ l₁ (-(m₀ : ℤ)) g := by
      unfold Work.KMTAreas.A7Hi.lpf
      norm_num
    rw [hproj]
    exact kmtProj_l2_le ρ l₁ Qbig (hQbig l₁ hl₁) m₀ hg
  have hchain3 := hCc3 l₁ hl₁ m₀ g (summable_of_memLp_two hg)
  have hchainr := hCcr l₁ hl₁ m₀ g (summable_of_memLp_two hg)
  refine hstep1.trans ((add_le_add ((hstep3.le.trans hsingle))
    (hstep2.trans (add_le_add hchain3 hchainr))).trans ?_)
  refine le_of_eq ?_
  rw [← add_mul, ← add_mul]
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-! ## The masked unmodulated low-pass family -/

/-- **The clipped low-pass walk of the `k₁ = 0` slice is bounded on `ℓ²`.**  The core condition
`mdlCore ρ C₀ a l₁ l₂ 0 k₂` is a *suffix* of `ℕ` (`mdlCore_of_le`); on that suffix the level is
`Log N_n`, so the family is a monotone reindexing of the full walk `m ↦ lpf ρ l₁ m₀ m g` with
`m₀ = Log N_{n₀}`, padded with zeros (`variationalNorm_prefix_zero_le`). -/
theorem lowpassMaskedBound (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (B : ℕ) (C₀ : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₂ : ℕ) (g : ℤ → ℂ),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) → l₁ ≤ B →
      MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
              Work.KMTContract.kmtProj ρ l₁ (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) g x
            else 0)) 2 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  obtain ⟨Cw, hCwpos, hCw⟩ := walkVarBound ρ hρ hρ1 r hr B
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  refine ⟨2 * Cw, by positivity, ?_⟩
  intro a Λ l₁ l₂ k₂ g hΛ ha ha1 hl₁ hg
  by_cases hcore : ∃ n, mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
  · set n₀ : ℕ := Nat.find hcore with hn₀def
    have hn₀core : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n₀ := Nat.find_spec hcore
    have hmin : ∀ m, mdlCore ρ C₀ a l₁ l₂ 0 k₂ m → n₀ ≤ m := fun m hm => Nat.find_min' hcore hm
    have hfloor : Monotone fun n => Nat.floor (a n) := monotone_floor_lacunary hΛ ha ha1
    have hsuffix : ∀ n, n₀ ≤ n → mdlCore ρ C₀ a l₁ l₂ 0 k₂ n :=
      fun n hn => mdlCore_of_le hfloor hn hn₀core
    set lev : ℕ → ℕ := fun n => (Work.Analysis.EndVar.logN (Nat.floor (a n))).toNat with hlevdef
    have hlevmono : Monotone lev :=
      fun i j hij => Int.toNat_le_toNat (Work.Analysis.EndVar.logN_mono (hfloor hij))
    set m₀ : ℕ := lev n₀ with hm₀def
    have hm₀le : ∀ n, n₀ ≤ n → m₀ ≤ lev n := fun n hn => hlevmono hn
    set sub : ℕ → ℤ → ℂ :=
      fun k => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ (lev (n₀ + k) - m₀) g with hsubdef
    -- identification of the masked family with the prefix-zero padded `sub`
    have hfam : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
              Work.KMTContract.kmtProj ρ l₁
                (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) g x
            else 0))
        = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if n < n₀ then 0 else sub (n - n₀) x)) := by
      funext x
      congr 1
      funext n
      by_cases hn : n < n₀
      · have hnc : ¬ mdlCore ρ C₀ a l₁ l₂ 0 k₂ n := fun h => absurd (hmin n h) (not_le.mpr hn)
        simp only [hn, if_true, if_neg hnc]
      · have hnle : n₀ ≤ n := not_lt.mp hn
        have hc : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n := hsuffix n hnle
        have hnat : n₀ + (n - n₀) = n := Nat.add_sub_cancel' hnle
        have hval : sub (n - n₀) x
            = Work.KMTContract.kmtProj ρ l₁
                (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) g x := by
          have h1 : ((m₀ : ℤ) + ((lev (n₀ + (n - n₀)) - m₀ : ℕ) : ℤ)) = (lev n : ℤ) := by
            rw [hnat]
            have hle := hm₀le n hnle
            omega
          have h2 : (lev n : ℤ) = Work.Analysis.EndVar.logN (Nat.floor (a n)) :=
            Int.toNat_of_nonneg (Work.Analysis.EndVar.logN_nonneg _)
          simp only [hsubdef, Work.KMTAreas.A7Hi.lpf]
          rw [h1, h2]
        simp only [if_neg hn, if_pos hc, hval]
    rw [hfam]
    have hsubwalk : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
          (fun k : ℕ => sub k x)
        ≤ PointwiseErgodicTheorems.variationalNorm r
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m g x) := by
      intro x
      have hφ : Monotone (fun k : ℕ => lev (n₀ + k) - m₀) :=
        fun i j hij => Nat.sub_le_sub_right (hlevmono (Nat.add_le_add_left hij n₀)) m₀
      have h := Work.KMTAreas.A7.variationalNorm_comp_mono_le (r := r)
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m g x)
        (φ := fun k : ℕ => lev (n₀ + k) - m₀) hφ
      simpa only [hsubdef] using h
    have hwalk := hCw l₁ hl₁ m₀ g hg
    calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if n < n₀ then 0 else sub (n - n₀) x)) 2 MeasureTheory.Measure.count
        ≤ MeasureTheory.eLpNorm (fun x : ℤ => (2 : ENNReal)
            * PointwiseErgodicTheorems.variationalNorm r (fun k : ℕ => sub k x))
            2 MeasureTheory.Measure.count :=
          MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm)
            (fun x => variationalNorm_prefix_zero_le r hr1
              (fun k : ℕ => sub k x) n₀)
      _ = (2 : ENNReal) * MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm r (fun k : ℕ => sub k x))
            2 MeasureTheory.Measure.count :=
          Commons.MeasureTheory.Lp.eLpNorm_const_mul_ennreal (by norm_num) (by norm_num)
            (by norm_num)
      _ ≤ (2 : ENNReal) * (ENNReal.ofReal Cw * MeasureTheory.eLpNorm g 2
            MeasureTheory.Measure.count) := by
          refine mul_le_mul' le_rfl ?_
          exact (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hsubwalk).trans hwalk
      _ = ENNReal.ofReal (2 * Cw) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
          rw [show (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) from by norm_num, ← mul_assoc,
            ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  · have h0 : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
              Work.KMTContract.kmtProj ρ l₁
                (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) g x
            else 0)) = fun _ : ℤ => 0 := by
      funext x
      have hz : (fun n : ℕ => if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
              Work.KMTContract.kmtProj ρ l₁
                (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) g x
            else 0) = (0 : ℕ → ℂ) := by
        funext n
        rw [if_neg (fun h => hcore ⟨n, h⟩)]
        rfl
      rw [hz]
      have h := Submission.PointwiseErgodicTheorems.variationalNorm_smul (r := r) hr1
        (0 : ℂ) (0 : ℕ → ℂ)
      simpa using h
    rw [h0]
    simp

/-- `Work.KMTAreas.A7.lossWeight` is monotone in the four height parameters. -/
theorem lossWeight_le_of_le {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) {l₁ l₂ k₁ k₂ B : ℕ}
    (h1 : l₁ ≤ B) (h2 : l₂ ≤ B) (h3 : k₁ ≤ B) (h4 : k₂ ≤ B) :
    Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂ ≤ Work.KMTAreas.A7.lossWeight c ρ B B B B := by
  rw [Work.KMTAreas.A7.lossWeight, Work.KMTAreas.A7.lossWeight]
  have hLz : Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ)
      ≤ Work.Analysis.EndVar.lmax B B (B : ℤ) (B : ℤ) := by
    rw [Work.Analysis.EndVar.lmax, Work.Analysis.EndVar.lmax]
    exact max_le_max
      (max_le_max (show (l₁ : ℤ) ≤ (B : ℤ) from by exact_mod_cast h1)
        (show (l₂ : ℤ) ≤ (B : ℤ) from by exact_mod_cast h2))
      (max_le_max (show (k₁ : ℤ) ≤ (B : ℤ) from by exact_mod_cast h3)
        (show (k₂ : ℤ) ≤ (B : ℤ) from by exact_mod_cast h4))
  have hL : Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ ≤ Work.KMTAreas.A7.lmaxR B B B B := by
    rw [Work.KMTAreas.A7.lmaxR, Work.KMTAreas.A7.lmaxR]
    exact_mod_cast hLz
  have hL0 : 0 ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lmaxR]
    exact_mod_cast (show (0 : ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) from by
      rw [Work.Analysis.EndVar.lmax]
      exact le_trans (Int.natCast_nonneg l₁)
        (le_trans (le_max_left _ _) (le_max_left _ _)))
  refine mul_le_mul (Real.rpow_le_rpow (by linarith) (by linarith) hc)
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left hL (mul_nonneg hc hρ)))
    (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by linarith) _)

theorem sliceFBound (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (B : ℕ) : Work.KMTPlan.A6.PieceBoundedH.SliceFBound r C₀ ρ B := by
  obtain ⟨Clp, hClppos, hClp⟩ := lowpassMaskedBound ρ hρ hρ1 r hr B C₀
  obtain ⟨Kd, hKd⟩ := Work.KMTPlan.A6.mdlDiffFamilyAll C₀ hC₀ r hr ρ hρ hρ1
  obtain ⟨Qc, hQcpos, hQcelem⟩ := Work.Analysis.IonescuWainger.iwP_element_le hρ
  set Qbig : ℕ := Nat.ceil ((2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (B : ℝ)))) with hQbigdef
  have hQbig : ∀ (l : ℕ), l ≤ B → ∀ q ∈ iwP ρ l, q ≤ Qbig := by
    intro l hl q hq
    have h1 : (q : ℝ) ≤ (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l : ℝ))) := hQcelem l q hq
    have h2 : (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (l : ℝ)))
        ≤ (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (B : ℝ))) := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      refine mul_le_mul_of_nonneg_left ?_ hQcpos.le
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hl) hρ.le)
    have h3 : (2 : ℝ) ^ (Qc * (2 : ℝ) ^ (ρ * (B : ℝ))) ≤ (Qbig : ℝ) := by
      rw [hQbigdef]; exact Nat.le_ceil _
    exact_mod_cast le_trans h1 (le_trans h2 h3)
  set CmdlF : ℝ := 2 * (1 + 2 * (Qbig : ℝ) ^ 2) with hCmdlFdef
  have hCmdlFpos : 0 < CmdlF := by rw [hCmdlFdef]; positivity
  set lossB : ℝ := Work.KMTAreas.A7.lossWeight 2 ρ B B B B with hlossBdef
  have hlossB0 : 0 ≤ lossB := by
    rw [hlossBdef]; exact Work.KMTAreas.A7.lossWeight_nonneg 2 ρ B B B B
  set Mof : NNReal → ℝ := fun Λ => if h : 1 < Λ then
      max 1 (Classical.choose (MdlLinVarphiNtjSupBound Λ h)) else 1 with hMofdef
  have hMof1 : ∀ Λ : NNReal, 1 ≤ Mof Λ := by
    intro Λ
    rw [hMofdef]
    dsimp only
    split_ifs with h
    · exact le_max_left _ _
    · exact le_rfl
  set Kv : NNReal → ℝ := fun Λ => if h : 1 < Λ then
      Classical.choose (mdlVanishingCaseUnif ρ hρ hρ1 C₀ r hr 0 (Mof Λ) (hMof1 Λ)) else 1
    with hKvdef
  set Kfun : NNReal → NNReal := fun Λ =>
      ⟨max 1 (max (Clp * CmdlF + (Kd Λ : ℝ) * lossB) (Kv Λ)),
        le_trans zero_le_one (le_max_left _ _)⟩ with hKfundef
  have hKfunval : ∀ Λ : NNReal, (Kfun Λ : ℝ)
      = max 1 (max (Clp * CmdlF + (Kd Λ : ℝ) * lossB) (Kv Λ)) := by
    intro Λ; rw [hKfundef]; rfl
  refine ⟨Kfun, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 ht hLB
  have hKΛ : (Kfun Λ : ENNReal)
      = ENNReal.ofReal (max 1 (max (Clp * CmdlF + (Kd Λ : ℝ) * lossB) (Kv Λ))) := by
    rw [ENNReal.coe_nnreal_eq, hKfunval]
  have hKΛ1 : (1 : ℝ) ≤ (Kfun Λ : ℝ) := by rw [hKfunval]; exact le_max_left _ _
  have hKΛne : (Kfun Λ : ENNReal) ≠ 0 := by
    rw [ne_eq, ENNReal.coe_eq_zero]
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hKΛ1)
  by_cases hftop : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = ⊤
  · rw [hftop, ENNReal.mul_top hKΛne]
    exact le_top
  · have hfmem : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count :=
      MeasureTheory.memLp_iff.mpr (lt_top_iff_ne_top.mpr hftop)
    have hl₁B : l₁ ≤ B :=
      le_trans (le_trans (le_max_left l₁ l₂) (le_max_left (max l₁ l₂) (max k₁ k₂))) hLB
    have hl₂B : l₂ ≤ B :=
      le_trans (le_trans (le_max_right l₁ l₂) (le_max_left (max l₁ l₂) (max k₁ k₂))) hLB
    have hk₁B : k₁ ≤ B :=
      le_trans (le_trans (le_max_left k₁ k₂) (le_max_right (max l₁ l₂) (max k₁ k₂))) hLB
    have hk₂B : k₂ ≤ B :=
      le_trans (le_trans (le_max_right k₁ k₂) (le_max_right (max l₁ l₂) (max k₁ k₂))) hLB
    by_cases hk₁ : k₁ = 0
    · subst hk₁
      set G : ℤ → ℂ := Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ 0 k₂))
        l₁ f with hG
      have hGmem : MeasureTheory.MemLp G 2 MeasureTheory.Measure.count := by
        rw [hG]; exact Work.KMTPlan.A6.memLp_mdlF ρ _ l₁ hfmem
      obtain ⟨Bg, hBg⟩ := Work.KMTAreas.A7.eLpNorm_finite_bounded 2 (by norm_num) G hGmem.eLpNorm_lt_top
      have hGbd : ∀ m : ℤ, ‖G m‖ ≤ Bg := hBg
      have hGn : MeasureTheory.eLpNorm G 2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal CmdlF * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        rw [hG]
        refine (Work.KMTPlan.A6.mdlF_two_le ρ (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ 0 k₂))
          l₁ Qbig (hQbig l₁ hl₁B) (hQbig (l₁ - 1) (by omega)) f).trans ?_
        refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
        rw [hCmdlFdef]
        have hz : (2 : ℝ) ^ (-((Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ 0 k₂) : ℤ))) ≤ 1 := by
          rw [zpow_neg]
          exact inv_le_one_of_one_le₀ (one_le_zpow₀ (a := (2 : ℝ)) (by norm_num) (by positivity))
        have hz0 : 0 ≤ (2 : ℝ) ^ (-((Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ 0 k₂) : ℤ))) :=
          zpow_nonneg (by norm_num) _
        have hQ2 : (0 : ℝ) ≤ (Qbig : ℝ) ^ 2 := sq_nonneg _
        nlinarith [hz, hz0, hQ2]
      set UF : ℤ → ENNReal := fun x => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
            Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) G x
          else 0) with hUF
      set DF : ℤ → ENNReal := fun x => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
            Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                  - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ) G x
          else 0) with hDF
      have hsplit : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => sliceF ρ C₀ a l₁ l₂ 0 k₂ t f n x) ≤ UF x + DF x := by
        intro x
        have hfam : (fun n : ℕ => sliceF ρ C₀ a l₁ l₂ 0 k₂ t f n x)
            = (fun n : ℕ => (if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                  Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) G x
                else 0)
              + (if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                  Work.KMTAreas.A7.Tle ρ l₁ (fun ξ : ℝ =>
                      Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                        - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ) G x
                else 0)) := by
          funext n
          by_cases hc : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
          · simp only [sliceF, hc, if_true, ← hG]
            have hsym : (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0
                  + fun ξ : ℝ => Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                      - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ)
                = Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t := by
              funext ξ; simp only [Pi.add_apply]; ring
            have hAdmφ : Work.KMTAreas.A7.Adm (iwArithFreqs ρ l₁)
                (Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0) := by
              have hφ : Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 0
                  = Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 := by
                funext ξ; simp [Work.KMTAreas.A7.varphiNt, Work.KMTAreas.A7.ee]
              simpa only [hφ] using (Work.KMTAreas.A7.adm_of_bump
                (Work.KMTAreas.A7.contDiff_varphiNt (Nat.floor (a n)) 0 0)
                (Work.KMTAreas.A7.hasCompactSupport_varphiNt (Nat.floor (a n)) 0 0))
            have hAdmψ : Work.KMTAreas.A7.Adm (iwArithFreqs ρ l₁) (fun ξ : ℝ =>
                Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t ξ
                  - Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0 ξ) :=
              (Work.KMTAreas.A7.adm_of_bump
                (Work.KMTAreas.A7.contDiff_varphiNt (Nat.floor (a n)) 0 t)
                (Work.KMTAreas.A7.hasCompactSupport_varphiNt (Nat.floor (a n)) 0 t)).sub hAdmφ
            conv_lhs => rw [← hsym]
            rw [Work.KMTAreas.A7LoLin.Tle_add_of_bounded hAdmφ hAdmψ hGbd]
            rfl
          · simp only [sliceF, hc, if_false, Pi.zero_apply, add_zero]
        rw [hfam]
        exact Submission.PointwiseErgodicTheorems.variationalNorm_add_le
          (le_of_lt (lt_trans (by norm_num) hr)) _ _
      have hUeq : UF = fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
              Work.KMTContract.kmtProj ρ l₁
                (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) G x
            else 0) := by
        rw [hUF]
        funext x
        congr 1
        funext n
        by_cases hc : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
        · simp only [hc, if_true]
          have hφ : Work.KMTAreas.A7.varphiN (Nat.floor (a n)) 0
              = Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
                  (-(Work.Analysis.EndVar.logN (Nat.floor (a n)))) := by
            funext ξ
            simp only [Work.KMTAreas.A7.varphiN, if_true,
              Work.Analysis.IonescuWainger.etaCut]
            congr 1
            rw [div_eq_mul_inv, ← zpow_neg, neg_neg, ← Real.rpow_intCast]
            ring
          rw [hφ, Work.KMTAreas.A7.Tle_etaCut]
        · simp only [hc, if_false]
      have hD' : MeasureTheory.eLpNorm DF 2 MeasureTheory.Measure.count
          ≤ (Kd Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        rw [hDF]; exact hKd a Λ l₁ l₂ k₂ t f hΛ ha ha1 ht
      have hUF : MeasureTheory.eLpNorm UF 2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (Clp * CmdlF) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        have hU' : MeasureTheory.eLpNorm UF 2 MeasureTheory.Measure.count
            ≤ ENNReal.ofReal Clp * MeasureTheory.eLpNorm G 2 MeasureTheory.Measure.count := by
          rw [hUeq]
          exact hClp a Λ l₁ l₂ k₂ G hΛ ha ha1 hl₁B hGmem
        calc MeasureTheory.eLpNorm UF 2 MeasureTheory.Measure.count
            ≤ ENNReal.ofReal Clp * MeasureTheory.eLpNorm G 2 MeasureTheory.Measure.count := hU'
          _ ≤ ENNReal.ofReal Clp * (ENNReal.ofReal CmdlF
                * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) :=
              mul_le_mul' le_rfl hGn
          _ = ENNReal.ofReal (Clp * CmdlF) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul hClppos.le]
      have hDF : MeasureTheory.eLpNorm DF 2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal ((Kd Λ : ℝ) * lossB)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        have hloss : Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂ ≤ lossB := by
          rw [hlossBdef]
          exact lossWeight_le_of_le (by norm_num) hρ.le hl₁B hl₂B (Nat.zero_le _) hk₂B
        have h1 : (Kd Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ 0 k₂)
            ≤ ENNReal.ofReal ((Kd Λ : ℝ) * lossB) := by
          rw [ENNReal.coe_nnreal_eq, ← ENNReal.ofReal_mul (Kd Λ).coe_nonneg]
          exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left hloss (Kd Λ).coe_nonneg)
        exact hD'.trans (mul_le_mul' h1 le_rfl)
      have hmain : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => sliceF ρ C₀ a l₁ l₂ 0 k₂ t f n x)) 2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (Clp * CmdlF + (Kd Λ : ℝ) * lossB)
              * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        have h1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => sliceF ρ C₀ a l₁ l₂ 0 k₂ t f n x)) 2 MeasureTheory.Measure.count
            ≤ MeasureTheory.eLpNorm UF 2 MeasureTheory.Measure.count
              + MeasureTheory.eLpNorm DF 2 MeasureTheory.Measure.count :=
          (MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) hsplit).trans
            (MeasureTheory.eLpNorm_add_le (by norm_num))
        refine h1.trans ((add_le_add hUF hDF).trans ?_)
        rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg hClppos.le hCmdlFpos.le)
          (mul_nonneg (Kd Λ).coe_nonneg hlossB0)]
      refine hmain.trans ?_
      rw [hKΛ]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      exact le_trans (le_max_left _ _) (le_max_right _ _)
    · have hk₁pos : 1 ≤ k₁ := Nat.one_le_iff_ne_zero.mpr hk₁
      have hspec := Classical.choose_spec (MdlLinVarphiNtjSupBound Λ hΛ)
      have hsup : ∀ (U : Finset ℕ) (ω : ℕ → Bool) (ξ : ℝ),
          ‖∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
            Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ 0 t ξ‖ ≤ Mof Λ := by
        intro U ω ξ
        have h := hspec.2.1 k₁ hk₁pos 0 (by decide) t ht a ha ha1 U ω ξ
        have hMofval : Mof Λ = max 1 (Classical.choose (MdlLinVarphiNtjSupBound Λ hΛ)) := by
          rw [hMofdef]
          simp only [dif_pos hΛ]
        rw [hMofval]
        exact le_trans h (le_max_right _ _)
      have hKvval : Kv Λ
          = Classical.choose (mdlVanishingCaseUnif ρ hρ hρ1 C₀ r hr 0 (Mof Λ) (hMof1 Λ)) := by
        rw [hKvdef]
        simp only [dif_pos hΛ]
      have hgoal : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => sliceF ρ C₀ a l₁ l₂ k₁ k₂ t f n x)) 2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (Kv Λ) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
        rw [hKvval]
        have hmain := (Classical.choose_spec (mdlVanishingCaseUnif ρ hρ hρ1 C₀ r hr 0 (Mof Λ)
          (hMof1 Λ))).2 a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 hsup
        have heq : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => sliceF ρ C₀ a l₁ l₂ k₁ k₂ t f n x))
            = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
                  Work.KMTAreas.A7.Tle ρ l₁
                    (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ 0 t)
                    (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                      (max (max l₁ l₂) (max k₁ k₂))) l₁ f) x
                else 0)) := by
          funext x
          congr 1
          funext n
          by_cases hc : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
          · simp only [sliceF, hc, if_true, Work.KMTPlan.A6.varphiNtj_zero, lcL]
          · simp only [sliceF, hc, if_false, Pi.zero_apply]
        rw [heq]
        exact hmain
      refine hgoal.trans ?_
      rw [hKΛ]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      exact le_trans (le_max_right _ _) (le_max_right _ _)

end

end Work.KMTPlan.A6.PieceLocal
