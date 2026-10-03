import Mathlib
import Submission.Work.KMTPlan.A6.MdlPktLinFDefs
import Submission.Work.KMTPlan.A6.TleMdlF_eq_TmLocal
import Submission.Work.KMTPlan.A6.MdlPktNarrowness
import Submission.Work.KMTAreas.A7.mixedGFibreLargeScalesCrux
import Submission.Work.KMTAreas.A7Hi.lowpassNarrowVarRep
import Submission.Work.KMTPlan.A6.LowModApproxBoundedH.liftAux
import Submission.Work.KMTPlan.A6.eLpNorm_piExact_le
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 32000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7

noncomputable section

/-! ## Local bricks -/

/-- `‖z‖ₑ = ofReal ‖z‖` for a complex number. -/
private theorem enorm_eq_ofReal_norm_local (z : ℂ) : ‖z‖ₑ = ENNReal.ofReal ‖z‖ := by
  rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]
  rfl

/-- Modulating a sequence by a character does not change its `ℓᵖ`-norm (counting measure). -/
private theorem eLpNorm_fourier_mul_local (α : Work.Analysis.IonescuWainger.Circle) (F : ℤ → ℂ)
    (p : ENNReal) :
    MeasureTheory.eLpNorm (fun y : ℤ => fourier (T := 1) y α * F y) p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm F p MeasureTheory.Measure.count := by
  have h1 : ∀ y : ℤ, ‖fourier (T := 1) y α‖ₑ = 1 := fun y => by
    rw [enorm_eq_ofReal_norm_local, Work.KMTAreas.A7Hi.norm_fourier_int α y, ENNReal.ofReal_one]
  refine le_antisymm ?_ ?_
  · refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun y => ?_)
    rw [enorm_mul, h1 y, one_mul]
  · refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun y => ?_)
    rw [enorm_mul, h1 y, one_mul]

/-- **The lift from the height-`0` estimate to the height-`l` estimate.** -/
private theorem eLpNorm_variationalNorm_Tle_le_sum_local (ρ : ℝ) (l : ℕ) {ψ : ℕ → ℝ → ℂ}
    (hψ : ∀ n, MeasureTheory.Integrable (ψ n))
    (hψcw : ∀ n, Summable fun j : ℤ => ‖cw (ψ n) j‖)
    (c : ℕ → Prop) [DecidablePred c] (r : NNReal) (hr : 1 ≤ r)
    (p : ENNReal) (hp : 1 ≤ p) (hpt : p ≠ ⊤) {K : ENNReal}
    (h0 : ∀ F : ℤ → ℂ, MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if c n then Tle ρ 0 (ψ n) F x else 0))
        p MeasureTheory.Measure.count
      ≤ K * MeasureTheory.eLpNorm F p MeasureTheory.Measure.count)
    (F : ℤ → ℂ) {CF : ℝ} (hbdd : ∀ y : ℤ, ‖F y‖ ≤ CF) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => if c n then Tle ρ l (ψ n) F x else 0))
      p MeasureTheory.Measure.count
    ≤ (∑ _α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l, K)
        * MeasureTheory.eLpNorm F p MeasureTheory.Measure.count := by
  classical
  have hp0 : p ≠ 0 := by
    intro h
    rw [h] at hp
    exact absurd hp (by norm_num)
  have hpt_bound : ∀ x : ℤ,
      PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if c n then Tle ρ l (ψ n) F x else 0)
      ≤ ∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if c n then
              Tle ρ 0 (ψ n) (fun y : ℤ => fourier (T := 1) y α * F y) x
              else 0) :=
    fun x => Work.KMTPlan.A6.LowModApproxBoundedH.Lift.variationalNorm_Tle_le_sum ρ l hψ hψcw F CF
      hbdd c r hr x
  have hstep1 := Work.KMTAreas.A7.eLpNorm_mono_ennreal (μ := MeasureTheory.Measure.count)
    hpt_bound hp0 hpt
  have hstep2 := Work.KMTAreas.A7.eLpNorm_finset_sum_le_ennreal
    (μ := MeasureTheory.Measure.count)
    (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
    (fun α x => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => if c n then Tle ρ 0 (ψ n)
        (fun y : ℤ => fourier (T := 1) y α * F y) x else 0)) hp hpt
  have hstep3 : (∑ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if c n then Tle ρ 0 (ψ n)
            (fun y : ℤ => fourier (T := 1) y α * F y) x else 0))
        p MeasureTheory.Measure.count)
      ≤ ∑ _α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
          K * MeasureTheory.eLpNorm F p MeasureTheory.Measure.count :=
    Finset.sum_le_sum (fun α _hα =>
      (h0 (fun y : ℤ => fourier (T := 1) y α * F y)).trans
        (le_of_eq (by rw [eLpNorm_fourier_mul_local])))
  exact hstep1.trans (hstep2.trans (hstep3.trans (Finset.sum_mul _ _ _).symm.le))

/-- **Narrowness of the packet bump on the A6 core, at an arbitrary height `l₁`.** -/
theorem supportedInArc_varphiNt_zero_of_core_gen (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ k₂ n : ℕ) (t : ℝ) (h : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n) :
    Work.Analysis.IonescuWainger.SupportedInArc
      (-((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂)) : ℕ) : ℤ) - 1)
      (Work.Analysis.IonescuWainger.periodize (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) 0 t)) := by
  obtain ⟨_, hcut, _⟩ := h
  set u : ℕ := Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂)) with hudef
  have hn : (2 : ℕ) ^ (2 ^ u) < Nat.floor (a n) := hcut
  have hlog_nat : 2 ^ u ≤ Nat.log 2 (max (Nat.floor (a n)) 2) :=
    Nat.le_log_of_pow_le (by norm_num) (le_trans hn.le (le_max_left _ _))
  have hlog : ((2 : ℕ) ^ u : ℤ) ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := by
    rw [Work.Analysis.EndVar.logN]
    exact_mod_cast hlog_nat
  have hup : ((u : ℤ)) + 1 ≤ ((2 : ℕ) ^ u : ℤ) := by
    have hone : ((u : ℤ)) + 1 = ((u + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [hone]
    exact_mod_cast Nat.succ_le_of_lt (show u < 2 ^ u from Nat.lt_two_pow_self)
  have hle : -(Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ -((u : ℤ)) - 1 := by
    have : ((u : ℤ)) + 1 ≤ Work.Analysis.EndVar.logN (Nat.floor (a n)) := le_trans hup hlog
    omega
  exact Work.KMTPlan.A6.pkt_supportedInArc_mono_level hle
    (Work.KMTPlan.A6.supportedInArc_varphiNt_zero (Nat.floor (a n)) t)

/-- **A `Λ`-lacunary sequence with `1 ≤ a n` is monotone.** -/
theorem monotone_of_lacunary' {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h2 : Λ < a (n + 1) / a n := ha n
  have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
  have h3 : a n ≤ Λ * a n := by
    simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
  exact le_trans h3 h1.le

/-- **Failure of the good-major-arc threshold bounds the scale.** -/
theorem uScale_lt_imp_bound (ρ : ℝ) (hρ : 0 < ρ) (Cρ : ℝ) (hCρ : 0 < Cρ) :
    ∃ B : ℕ, ∀ (l₁ L : ℕ), l₁ ≤ L →
      ((Work.KMTAreas.A7.uScale ρ L : ℕ) : ℝ) < Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) → L ≤ B := by
  refine ⟨Nat.ceil ((1 + Real.logb 2 Cρ) / ρ), ?_⟩
  intro l₁ L hl hlt
  have hρ0 : (0 : ℝ) ≤ ρ := hρ.le
  have h1 : (2 : ℝ) ^ (2 * ρ * (L : ℝ)) ≤ 2 * ((Work.KMTAreas.A7.uScale ρ L : ℕ) : ℝ) :=
    Work.KMTPlan.A6.rpow_le_two_mul_uScale ρ hρ0 L
  have hl₁L : (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤ (2 : ℝ) ^ (ρ * (L : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
      have : (l₁ : ℝ) ≤ (L : ℝ) := by exact_mod_cast hl
      nlinarith [hρ0])
  have h2 : 2 * ((Work.KMTAreas.A7.uScale ρ L : ℕ) : ℝ)
      < 2 * (Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ))) := by linarith
  have h3 : (2 : ℝ) ^ (2 * ρ * (L : ℝ)) < 2 * Cρ * (2 : ℝ) ^ (ρ * (L : ℝ)) := by
    have h5 : (0 : ℝ) ≤ 2 * Cρ := by linarith
    have h4 : 2 * (Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))
        ≤ 2 * Cρ * (2 : ℝ) ^ (ρ * (L : ℝ)) := by
      calc 2 * (Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)))
          = (2 * Cρ) * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := by ring
        _ ≤ (2 * Cρ) * (2 : ℝ) ^ (ρ * (L : ℝ)) := mul_le_mul_of_nonneg_left hl₁L h5
    linarith
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (ρ * (L : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have heq : (2 : ℝ) ^ (2 * ρ * (L : ℝ))
      = (2 : ℝ) ^ (ρ * (L : ℝ)) * (2 : ℝ) ^ (ρ * (L : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have h6 : (2 : ℝ) ^ (ρ * (L : ℝ)) < 2 * Cρ := by
    have h7 : (2 : ℝ) ^ (ρ * (L : ℝ)) * (2 : ℝ) ^ (ρ * (L : ℝ))
        < (2 * Cρ) * (2 : ℝ) ^ (ρ * (L : ℝ)) := by
      rw [← heq]; exact h3
    nlinarith [hpos, h7]
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h7 : ρ * (L : ℝ) < 1 + Real.logb 2 Cρ := by
    have hlog : Real.log ((2 : ℝ) ^ (ρ * (L : ℝ))) < Real.log (2 * Cρ) :=
      Real.log_lt_log (Real.rpow_pos_of_pos (by norm_num) _) h6
    rw [Real.log_rpow (by norm_num)] at hlog
    rw [Real.log_mul (by norm_num) (ne_of_gt hCρ)] at hlog
    have h8 : (ρ * (L : ℝ) - 1) * Real.log 2 < Real.log Cρ := by nlinarith [hlog]
    have h9 : (ρ * (L : ℝ) - 1) < Real.log Cρ / Real.log 2 :=
      (lt_div_iff₀ hlog2pos).mpr h8
    rw [Real.logb]
    linarith
  have h10 : (L : ℝ) < (1 + Real.logb 2 Cρ) / ρ := by
    refine (lt_div_iff₀ hρ).mpr ?_
    rw [mul_comm]
    exact h7
  have h11 : (L : ℝ) ≤ ((Nat.ceil ((1 + Real.logb 2 Cρ) / ρ) : ℕ) : ℝ) :=
    le_trans h10.le (Nat.le_ceil _)
  exact_mod_cast h11

/-- The exact-height frequencies at `l` are `≤ l` arithmetic frequencies. -/
theorem diffFreqs_subset_local (ρ : ℝ) (l : ℕ) :
    Work.KMTAreas.A7.diffFreqs ρ l ⊆ Work.Analysis.IonescuWainger.iwArithFreqs ρ l := by
  rw [Work.KMTAreas.A7.diffFreqs]
  by_cases h : l = 0
  · rw [if_pos h, h]
  · rw [if_neg h]
    exact Finset.sdiff_subset

/-- **The `ℓ²` bound for the exact-height shell `mdlF` at bounded height.** -/
theorem eLpNorm_mdlF_le_of_card (ρ : ℝ) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1) (u l B : ℕ) (hl : l ≤ B)
    (f : ℤ → ℂ) :
    MeasureTheory.eLpNorm (mdlF ρ u l f) 2 MeasureTheory.Measure.count
      ≤ ((4 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : NNReal) : NNReal) : ENNReal) *
          MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  have h1 := Work.KMTPlan.A6.eLpNorm_piExact_le_of_height_le_one ρ hρ hρ₁ l (-(u : ℤ))
    (by omega : (-(u : ℤ)) ≤ 1) f
  have hcard : ((4 * (Work.KMTAreas.A7.diffFreqs ρ l).card : ℕ) : ENNReal)
      ≤ ((4 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : NNReal) : NNReal)
          : ENNReal) := by
    have h2 : (Work.KMTAreas.A7.diffFreqs ρ l).card
        ≤ (Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card :=
      (Finset.card_le_card (diffFreqs_subset_local ρ l)).trans
        (Finset.card_le_card (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ₁ hl))
    have h3 : (4 * (Work.KMTAreas.A7.diffFreqs ρ l).card : ℕ)
        ≤ (4 * (Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : ℕ) :=
      Nat.mul_le_mul_left 4 h2
    calc ((4 * (Work.KMTAreas.A7.diffFreqs ρ l).card : ℕ) : ENNReal)
        ≤ ((4 * (Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : ℕ) : ENNReal) := by
          exact_mod_cast h3
      _ = ((4 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : NNReal) : NNReal)
            : ENNReal) := by
          push_cast
          ring
  exact h1.trans (mul_le_mul' hcard le_rfl)

/-- `1 ≤ lossWeight c ρ l₁ l₂ k₁ k₂` for `c ≥ 0`. -/
theorem one_le_lossWeight {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) (l₁ l₂ k₁ k₂ : ℕ) :
    1 ≤ Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂ := by
  have hL : (0 : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lmaxR]
    have h : (0 : ℤ) ≤ Work.Analysis.EndVar.lmax l₁ l₂ (k₁ : ℤ) (k₂ : ℤ) := by
      rw [Work.Analysis.EndVar.lmax]
      omega
    exact_mod_cast h
  rw [Work.KMTAreas.A7.lossWeight]
  have h1 : (1 : ℝ) ≤ (1 + Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) ^ c :=
    Real.one_le_rpow (by linarith) hc
  have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (c * ρ * Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ _ := mul_le_mul h1 h2 (by norm_num) (by positivity)

/-- **The A6 core predicate is the A7 core predicate.** -/
theorem mdlCore_iff_core_local (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) :
    mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n ↔
      Work.KMTAreas.A7.core ρ C₀ l₁ l₂ k₁ k₂ a n := by
  simp only [mdlCore, Work.KMTAreas.A7.core]

/-- **The positive-height instance `1 ≤ l₁` of `MdlPktZeroZero` from the A7 `Hcl` estimate at
`p = 2`, `k₁ = 0`.**

This is the A6 glue of the road `CruxAll → HclEstimate2 → MdlPktZeroZeroPos` recorded in
`NOTES_MdlPktLinF_SESSION2.md`: it identifies the target's carrier
`Tle ρ l₁ (varphiNtj (⌊a n⌋) 0 0 t) (mdlF ρ (uScale ρ L) l₁ f)` (clipped at `mdlCore`) with the A7
`Hcl` carrier `Tex ρ l₁ (varphiNt (⌊a n⌋) 0 t) f` and hence gets the estimate from `HclEstimate2`.

## Roadmap (read before starting)

Write `L = max (max l₁ l₂) (max 0 k₂)`, `u = uScale ρ L`, `N = ⌊a n⌋`.

* `mdlCore ρ C₀ a l₁ l₂ 0 k₂ n` and `Work.KMTAreas.A7.core ρ C₀ l₁ l₂ 0 k₂ a n` are the *same*
  predicate (definitionally; `MdlDefs.mdlCore_iff`), and `varphiNtj N 0 0 t = varphiNt N 0 t`
  (`MdlDefs.varphiNtj_zero`).
* **Narrowness** (`splitCut ρ L = 2^{2^u} < N`, `mainRegime`): the bump is supported in
  `realArc (-u - 1)`, `Work.KMTPlan.A6.supportedInArc_varphiNt_zero_of_core`.
* **`⊤`-case**: if `eLpNorm f 2 MeasureTheory.Measure.count = ⊤` then the RHS of
  `MdlPktZeroZeroPos` is `⊤` (choose `K Λ ≥ 1`); so assume `MemLp f 2 count`
  (`measurable_of_countable f`).
* **The non-aliased case.**  If `GoodMajorArcs ρ Cρ l₁ (-(u : ℤ))` holds for the non-aliasing
  constant `Cρ` of `Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing`
  (`∀ l k, GoodMajorArcs ρ Cρ l k → NonAliasing k (iwArithFreqs ρ l)`), then
  `Work.KMTPlan.A6.Tle_mdlF_eq_Tm_local` gives
  `Tle ρ l₁ (varphiNt N 0 t) (mdlF ρ u l₁ f) = Tm ρ l₁ (varphiNt N 0 t) f`, and for `l₁ ≠ 0`
  `Work.KMTAreas.A7.Tm_eq_Tex_crux` (in `A7/mixedGFibreLargeScalesCrux.lean`) turns this into
  `Tex ρ l₁ (varphiNt N 0 t) f`, i.e. (with `1 ≤ l₁`) exactly the `Hcl` carrier; transport the
  bound of `h` across the `if` with `by_cases` (do NOT use `rw [if_pos …]` with a `core`-flavoured
  term, see the header of `MdlPktZeroZeroAtZero.lean`).
* **The two "bad" cases** (`u = 1`, or `2^{ρ l₁} < T₀(Cρ)`): here `u < Cρ · 2^{ρ l₁}` with
  `u ≥ 2^{2ρL} - 1` and `L ≥ l₁`, so `L` is bounded by a function of `ρ` alone, hence so is `l₁`.
  In that regime the cardinality `#(iwArithFreqs ρ l₁)` is a function of `ρ` alone, so it may be
  absorbed into `K Λ` (which is chosen *after* `ρ`): decompose
  `Tle ρ l₁ ψ g = Σ_{α ∈ iwArithFreqs ρ l₁} iwConv {α} (periodize ψ) g`
  (`Work.Analysis.IWMultiplier.iwConv_eq_sum_singleton`), bound the variational norm of the sum by
  the sum of the variational norms (the finite sum is over a `ρ`-bounded index set), and bound each
  channel family `n ↦ iwConv {α} (periodize (varphiNt ⌊a n⌋ 0 t)) g` (a *lacunary dilation family*
  of the fixed function `g = mdlF ρ u l₁ f`, with kernel `j ↦ e (j α) · cw (periodize (varphiNt …)) j`)
  by `C(ρ) ‖g‖₂` using the clean lacunary dilation machinery `Work.KMTAreas.A7Hi.DilVar` (or
  `Work.KMTAreas.A7Hi.lowpassNarrowVarRep`) applied to `charMul α g`.  Finally `‖g‖₂ ≤ C(ρ)‖f‖₂`
  (the single-scale `piExact` bound).
* The estimate for the *clipped* family is then `3 ×` the unclipped one
  (`Work.KMTAreas.A7.eLpNorm_variationalNorm_clip_le`, `core` is upward closed in `n`). -/
theorem MdlPktZeroZeroPos_of_hclEstimate2 (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R)
    (h : Work.KMTPlan.A6.HclEstimate2 C₀ R) : Work.KMTPlan.A6.MdlPktZeroZeroPos C₀ R := by
  classical
  obtain ⟨A, hA0, ρ₀, hρ0, H⟩ := h
  have hr1 : (1 : NNReal) ≤ R := le_trans (by norm_num) (le_of_lt hR)
  refine ⟨A, hA0, min ρ₀ 1, lt_min hρ0 one_pos, ?_⟩
  intro ρ hρ hρρ
  have hρ1 : ρ ≤ 1 := le_trans hρρ (min_le_right _ _)
  have hρρ₀ : ρ ≤ ρ₀ := le_trans hρρ (min_le_left _ _)
  obtain ⟨Kh, hKh⟩ := H ρ hρ hρρ₀
  obtain ⟨Cρ, hCρpos, hCρna⟩ := Work.Analysis.IonescuWainger.exists_goodMajorArcs_nonAliasing hρ
  obtain ⟨B, hB⟩ := uScale_lt_imp_bound ρ hρ Cρ hCρpos
  have hLoLinExists : ∀ Λ : NNReal, 1 < Λ → ∃ CL : NNReal, ∀ (a : ℕ → NNReal)
      (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n : ℕ, 1 ≤ a n) (t : ℝ)
      (ht : t ∈ Set.Icc (1 / 2 : ℝ) 1) (F : ℤ → ℂ),
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
          (fun n : ℕ => Tle ρ 0 (varphiNt (Nat.floor (a n)) 0 t) F x))
        2 MeasureTheory.Measure.count
        ≤ (CL : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count := by
    intro Λ hΛ
    obtain ⟨C, hC⟩ := LoLinVar ρ hρ hρ1 2 (by norm_num) (by norm_num) R hR Λ hΛ
    refine ⟨C, fun a ha ha1 t ht F => ?_⟩
    have hkN : ∀ n : ℕ, 2 ^ 0 ≤ Nat.floor (a n) := by
      intro n
      have h1 : (1 : NNReal) ≤ a n := ha1 n
      have h2 : 0 < Nat.floor (a n) := Nat.floor_pos.mpr h1
      omega
    have h := hC a ha ha1 0 hkN t ht F
    rwa [show ((1 : ℝ) + ((0 : ℕ) : ℝ)) ^ 2 = 1 by norm_num, ENNReal.ofReal_one,
      mul_one] at h
  set Kab : NNReal → NNReal := (fun Λ => if hh : 1 < Λ then
      max 1 ((3 : NNReal) * Classical.choose (hLoLinExists Λ hh)
        * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : NNReal)
        * (4 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : NNReal)))
      else 1) with hKabdef
  refine ⟨fun Λ => max (max (Kh Λ) (Kab Λ)) 1, ?_⟩
  intro a Λ l₁ l₂ k₂ t f hΛ ha ha1 ht hl₁
  by_cases hftop : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = ⊤
  · rw [hftop]
    have hne : ((max (max (Kh Λ) (Kab Λ)) 1 : NNReal) : ENNReal)
        * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂) ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · simp
      · rw [ENNReal.ofReal_ne_zero_iff]
        exact lt_of_lt_of_le one_pos (one_le_lossWeight hA0 hρ.le l₁ l₂ 0 k₂)
    rw [ENNReal.mul_top hne]
    exact le_top
  · have hfflt : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count < ⊤ :=
      lt_top_iff_ne_top.mpr hftop
    have hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count :=
      MeasureTheory.memLp_iff.mpr (hfflt)
    by_cases hgood : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁
        (-((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂)) : ℕ) : ℤ))
    · -- ## the non-aliased case: the composite identity
      have hnA : Work.Analysis.IonescuWainger.NonAliasing
          (-((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂)) : ℕ) : ℤ))
          (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁) := hCρna l₁ _ hgood
      have hident : ∀ n : ℕ, mdlCore ρ C₀ a l₁ l₂ 0 k₂ n →
          Tle ρ l₁ (varphiNtj (Nat.floor (a n)) 0 0 t)
              (mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ f)
            = Tex ρ l₁ (varphiNt (Nat.floor (a n)) 0 t) f := by
        intro n hn
        rw [varphiNtj_zero]
        rw [Work.KMTPlan.A6.Tle_mdlF_eq_Tm_local ρ hρ hρ1
          (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ (Nat.floor (a n)) 0
          (Work.KMTAreas.A7.uScale_pos hρ.le _) t hf hnA
          (supportedInArc_varphiNt_zero_of_core_gen ρ C₀ a l₁ l₂ k₂ n t hn)]
        exact Work.KMTAreas.A7.Tm_eq_Tex_crux ρ l₁ (by omega) _ f
      have hfam : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ =>
              if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Tle ρ l₁ (varphiNtj (Nat.floor (a n)) 0 0 t)
                  (mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ f) x
              else 0))
          = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ => Work.KMTAreas.A7.Hcl ρ C₀ a l₁ l₂ 0 k₂ t f n x)) := by
        funext x
        congr 1
        funext n
        by_cases hc : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
        · have hcore : Work.KMTAreas.A7.core ρ C₀ l₁ l₂ 0 k₂ a n :=
            (mdlCore_iff_core_local ρ C₀ a l₁ l₂ 0 k₂ n).mp hc
          simp only [if_pos hc, hident n hc, Work.KMTAreas.A7.Hcl, if_pos hcore]
        · have hcore : ¬ Work.KMTAreas.A7.core ρ C₀ l₁ l₂ 0 k₂ a n :=
            fun hcon => hc ((mdlCore_iff_core_local ρ C₀ a l₁ l₂ 0 k₂ n).mpr hcon)
          simp only [if_neg hc, Work.KMTAreas.A7.Hcl, if_neg hcore]
          rfl
      rw [hfam]
      have hb := hKh a Λ l₁ l₂ k₂ t f hΛ ha ha1 ht
      refine hb.trans ?_
      refine mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
      exact ENNReal.coe_le_coe.mpr (le_trans (le_max_left (Kh Λ) (Kab Λ))
        (le_max_left (max (Kh Λ) (Kab Λ)) 1))
    · -- ## the aliased case: `L` is bounded and everything is a height-`0` walk
      have hbad : ((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂)) : ℕ) : ℝ)
          < Cρ * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) := by
        by_contra hcon
        push_neg at hcon
        have h2 : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁
            (-((Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂)) : ℕ) : ℤ)) := by
          unfold Work.Analysis.IonescuWainger.GoodMajorArcs
          push_cast
          linarith
        exact hgood h2
      have hl₁L : l₁ ≤ max (max l₁ l₂) (max 0 k₂) :=
        le_trans (le_max_left l₁ l₂) (le_max_left _ _)
      have hLB : max (max l₁ l₂) (max 0 k₂) ≤ B := hB l₁ _ hl₁L hbad
      have hl₁B : l₁ ≤ B := le_trans hl₁L hLB
      set psi : ℕ → ℝ → ℂ := (fun n => varphiNtj (Nat.floor (a n)) 0 0 t) with hpsidef
      have hpsieq : ∀ n : ℕ, psi n = varphiNt (Nat.floor (a n)) 0 t := by
        intro n
        simp only [hpsidef, varphiNtj_zero]
      have hmon : Monotone a := monotone_of_lacunary' hΛ ha ha1
      set CLc : NNReal := Classical.choose (hLoLinExists Λ hΛ) with hCLcdef
      have hCLspec : ∀ (F : ℤ → ℂ), MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ => Tle ρ 0 (varphiNt (Nat.floor (a n)) 0 t) F x))
            2 MeasureTheory.Measure.count
          ≤ (CLc : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count := by
        intro F
        simpa only [← hCLcdef] using
          Classical.choose_spec (hLoLinExists Λ hΛ) a ha ha1 t ht F
      set K0 : ENNReal := (((3 : NNReal) * CLc : NNReal) : ENNReal) with hK0def
      have h0 : ∀ F : ℤ → ℂ, MeasureTheory.eLpNorm (fun x : ℤ =>
            PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ => if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then Tle ρ 0 (psi n) F x else 0))
            2 MeasureTheory.Measure.count
          ≤ K0 * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count := by
        intro F
        have huncl : MeasureTheory.eLpNorm (fun x : ℤ =>
              PointwiseErgodicTheorems.variationalNorm R
                (fun n : ℕ => Tle ρ 0 (psi n) F x))
              2 MeasureTheory.Measure.count
            ≤ (CLc : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count := by
          have hfam : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
                (fun n : ℕ => Tle ρ 0 (psi n) F x))
              = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
                  (fun n : ℕ => Tle ρ 0 (varphiNt (Nat.floor (a n)) 0 t) F x)) := by
            simp only [hpsieq]
          rw [hfam]
          exact hCLspec F
        by_cases hex : ∃ n : ℕ, mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
        · refine (Work.KMTAreas.A7.eLpNorm_variationalNorm_clip_le (r := R) hr1 2
              (Nat.find hex)
              (fun n : ℕ => fun x : ℤ => Tle ρ 0 (psi n) F x)
              (fun n : ℕ => fun x : ℤ => if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Tle ρ 0 (psi n) F x else 0) ?_ ?_).trans ?_
          · intro n hn
            funext x
            have hnc : ¬ mdlCore ρ C₀ a l₁ l₂ 0 k₂ n := Nat.find_min hex hn
            simp only [if_neg hnc]
            rfl
          · intro n hn
            funext x
            have hc : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n :=
              (mdlCore_iff_core_local ρ C₀ a l₁ l₂ 0 k₂ n).mpr
                (Work.KMTAreas.A7.core_mono hmon hn
                  ((mdlCore_iff_core_local ρ C₀ a l₁ l₂ 0 k₂ _).mp (Nat.find_spec hex)))
            simp only [if_pos hc]
          · have h3 : (3 : ENNReal) * (CLc : ENNReal) = K0 := by
              rw [hK0def]
              show ((3 : NNReal) : ENNReal) * (CLc : ENNReal)
                = (((3 : NNReal) * CLc : NNReal) : ENNReal)
              rw [ENNReal.coe_mul]
            exact (mul_le_mul' (le_refl (3 : ENNReal)) huncl).trans
              (le_of_eq (by rw [← mul_assoc, h3]))
        · have hfam0 : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
              (fun n : ℕ => if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then Tle ρ 0 (psi n) F x else 0))
              = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
                  (fun _ : ℕ => (0 : ℂ))) := by
            funext x
            have hfam : (fun n : ℕ => (if mdlCore ρ C₀ a l₁ l₂ 0 k₂ n then
                Tle ρ 0 (psi n) F x else 0)) = fun _ : ℕ => (0 : ℂ) := by
              funext n
              by_cases hc : mdlCore ρ C₀ a l₁ l₂ 0 k₂ n
              · exact (hex ⟨n, hc⟩).elim
              · simp [hc]
            rw [hfam]
          rw [hfam0, Work.KMTAreas.A7.eLpNorm_variationalNorm_zero hr1 2]
          exact zero_le
      have hψint : ∀ n : ℕ, MeasureTheory.Integrable (psi n) := fun n => by
        rw [hpsieq n]
        exact Work.KMTAreas.A7.integrable_varphiNt _ _ _
      have hψcw : ∀ n : ℕ, Summable fun j : ℤ => ‖cw (psi n) j‖ := fun n => by
        rw [hpsieq n]
        exact Work.KMTAreas.A7.cw_varphiNt_summable _ _ _
      have hFmem : MeasureTheory.eLpNorm
          (mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ f)
          2 MeasureTheory.Measure.count < ⊤ :=
        lt_of_le_of_lt (eLpNorm_mdlF_le_of_card ρ hρ hρ1
          (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ B hl₁B f)
          (ENNReal.mul_lt_top ENNReal.coe_lt_top hfflt)
      obtain ⟨CF, hCF⟩ := Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top
        (p := 2) (by norm_num) hFmem
      have hmain := eLpNorm_variationalNorm_Tle_le_sum_local (K := K0) ρ l₁ hψint hψcw
        (fun n => mdlCore ρ C₀ a l₁ l₂ 0 k₂ n) R hr1 2 (by norm_num) (by norm_num) h0
        (mdlF ρ (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ f) hCF
      have hsum_le : (∑ _α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁, K0)
          ≤ (((Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : NNReal) : ENNReal) * K0 := by
        rw [Finset.sum_const, nsmul_eq_mul]
        refine mul_le_mul' ?_ le_rfl
        exact_mod_cast Finset.card_le_card
          (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 hl₁B)
      have hKbad_le :
          (((Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : NNReal) : ENNReal) * K0
            * ((4 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : NNReal) : NNReal)
                : ENNReal)
          ≤ (Kab Λ : ENNReal) := by
        have hKabΛ : Kab Λ = max 1 ((3 : NNReal) * CLc
            * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : NNReal)
            * (4 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : NNReal))) := by
          rw [hKabdef]
          dsimp only
          rw [dif_pos hΛ, ← hCLcdef]
        rw [hKabΛ]
        refine le_trans (le_of_eq ?_) (ENNReal.coe_le_coe.mpr (le_max_right 1 _))
        rw [hK0def]
        push_cast
        ring
      have hKab_le_K : (Kab Λ : ENNReal) ≤ ((max (max (Kh Λ) (Kab Λ)) 1 : NNReal) : ENNReal) :=
        ENNReal.coe_le_coe.mpr (le_trans (le_max_right (Kh Λ) (Kab Λ))
          (le_max_left (max (Kh Λ) (Kab Λ)) 1))
      have hlw : (1 : ENNReal) ≤
          ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂) := by
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal (one_le_lossWeight hA0 hρ.le l₁ l₂ 0 k₂)
      refine hmain.trans ?_
      calc (∑ _α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁, K0)
            * MeasureTheory.eLpNorm (mdlF ρ
                (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ f)
              2 MeasureTheory.Measure.count
          ≤ ((((Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : NNReal) : ENNReal) * K0)
              * MeasureTheory.eLpNorm (mdlF ρ
                  (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ f)
                2 MeasureTheory.Measure.count :=
              mul_le_mul' hsum_le le_rfl
        _ ≤ ((((Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : NNReal) : ENNReal) * K0)
              * (((4 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : NNReal) : NNReal)
                    : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count) :=
              mul_le_mul' le_rfl (eLpNorm_mdlF_le_of_card ρ hρ hρ1
                (Work.KMTAreas.A7.uScale ρ (max (max l₁ l₂) (max 0 k₂))) l₁ B hl₁B f)
        _ = ((((Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : NNReal) : ENNReal) * K0
              * ((4 * ((Work.Analysis.IonescuWainger.iwArithFreqs ρ B).card : NNReal) : NNReal)
                  : ENNReal)) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
              ring
        _ ≤ (Kab Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count :=
              mul_le_mul' hKbad_le le_rfl
        _ ≤ (((max (max (Kh Λ) (Kab Λ)) 1 : NNReal) : ENNReal)
              * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂))
            * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
              refine mul_le_mul' ?_ le_rfl
              calc (Kab Λ : ENNReal) = (Kab Λ : ENNReal) * 1 := by ring
                _ ≤ ((max (max (Kh Λ) (Kab Λ)) 1 : NNReal) : ENNReal)
                    * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight A ρ l₁ l₂ 0 k₂) :=
                    mul_le_mul' hKab_le_K hlw

end

end Work.KMTPlan.A6
