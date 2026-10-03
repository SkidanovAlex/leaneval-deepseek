import Mathlib
import Submission.Work.KMTAreas.A7.LoLinVar
import Submission.Work.KMTAreas.A7.variationalNorm_clip_le
import Submission.Port.Aesm

namespace Work.KMTPlan.A6.LowModApproxBoundedH

open MeasureTheory
open scoped ENNReal NNReal BigOperators

set_option maxHeartbeats 1000000

/-! ## Elementary helpers -/

/-- A `Λ`-lacunary sequence with all terms `≥ 1` is monotone. -/
theorem monotone_of_lacunary {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h2 : Λ < a (n + 1) / a n := ha n
  have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
  have h3 : a n ≤ Λ * a n := by
    simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
  exact le_trans h3 h1.le

/-- At arithmetic height `0` the Ionescu--Wainger operator `Tle ρ 0` does not depend on `ρ`:
`iwArithFreqs ρ 0 = {0}` for every `ρ`, so both are the convolution with the periodisation of
`φ`. -/
theorem Tle_zero_rho_indep (ρ ρ' : ℝ) {φ : ℝ → ℂ} {f : ℤ → ℂ} :
    Work.KMTAreas.A7.Tle ρ 0 φ f = Work.KMTAreas.A7.Tle ρ' 0 φ f := by
  unfold Work.KMTAreas.A7.Tle
  rw [Work.KMTAreas.A7.iwArithFreqs_zero, Work.KMTAreas.A7.iwArithFreqs_zero]

/-! ## The auxiliary estimate for a fixed `Λ` -/

/-- The `f`-side level-`0` clipped lacunary variational estimate at `p = 2` for a fixed lacunarity
constant `Λ > 1`.  The proof applies the proved linear estimate `Work.KMTAreas.A7.LoLinVar`
(at `ρ = 1`, transported to the given `ρ` along `Tle ρ 0 = Tle 1 0`) to the lacunary *tail*
`n ↦ a (n + m)` of the lacunary sequence, where `m` is the first index of the `core` set: the
`core` set is a tail (it is upward closed in `n`) and the main-regime condition `2^{k₁} ≤ ⌊a n⌋`
holds on it, so the clipping costs only the factor `2` of `variationalNorm_clip_le`.  Note that
the resulting constant is *uniform* in `l₂, k₂`: the clip depends on them only through the tail
start `m`, and clipping at any tail costs at most a factor `2`. -/
theorem plainVarF_lev0_aux (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (ρ : ℝ) (hρ : 0 < ρ) (B : ℕ) (Λ : NNReal) (hΛ : 1 < Λ) :
    ∃ C : NNReal, ∀ (a : ℕ → NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (F : ℤ → ℂ),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        k₁ ≤ B → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ 0 l₂ k₁ k₂ a n then
              Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
              else 0)) 2 MeasureTheory.Measure.count
          ≤ (C : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count := by
  obtain ⟨Cl, hCl⟩ := Work.KMTAreas.A7.LoLinVar 1 one_pos le_rfl (2 : ENNReal)
    ENNReal.one_lt_two (ENNReal.ofNat_lt_top (n := 2)) r hr Λ hΛ
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  refine ⟨2 * Cl * ((1 + B : ℕ) : NNReal) ^ 2, ?_⟩
  intro a l₂ k₁ k₂ t F ha ha1 hk ht
  have hamono : Monotone a := monotone_of_lacunary hΛ ha ha1
  by_cases hex : ∃ n, Work.KMTAreas.A7.core ρ C₀ 0 l₂ k₁ k₂ a n
  · -- the `core` set is the tail `{n | m ≤ n}`
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ n : ℕ, Work.KMTAreas.A7.core ρ C₀ 0 l₂ k₁ k₂ a n ↔ m ≤ n := by
      refine ⟨Nat.find hex, fun n => ⟨fun h => ?_, fun h => ?_⟩⟩
      · by_contra hcon
        rw [not_le] at hcon
        exact Nat.find_min hex hcon h
      · exact Work.KMTAreas.A7.core_mono hamono h (Nat.find_spec hex)
    -- clipping at a tail costs at most a factor `2`
    have hclipx : ∀ x : ℤ,
        PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ 0 l₂ k₁ k₂ a n
            then Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
            else 0)
        ≤ 2 * PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x) := by
      intro x
      have hfun : (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ 0 l₂ k₁ k₂ a n
            then Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
            else 0)
          = (fun n : ℕ => if m ≤ n then Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x else 0) := by
        funext n
        by_cases h : Work.KMTAreas.A7.core ρ C₀ 0 l₂ k₁ k₂ a n
        · rw [if_pos h, if_pos ((hm n).mp h)]
        · rw [if_neg h, if_neg (fun hc => h ((hm n).mpr hc))]
      rw [hfun]
      refine (Work.KMTAreas.A7.variationalNorm_clip_le r hr1
        (fun n : ℕ => Work.KMTAreas.A7.Tle ρ 0
          (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x) m).trans (le_of_eq ?_)
      exact (two_mul _).symm
    have hstep : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ 0 l₂ k₁ k₂ a n
            then Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
            else 0)) 2 MeasureTheory.Measure.count
        ≤ 2 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x))
            2 MeasureTheory.Measure.count :=
      MeasureTheory.eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' (hf := by pw_aesm) (c := 2)
        (Filter.Eventually.of_forall (fun x => by
          rw [enorm_eq_self, enorm_eq_self]
          exact hclipx x)) 2
    -- the linear estimate on the lacunary tail `n ↦ a (n + m)`
    have hshift : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x))
            2 MeasureTheory.Measure.count
        ≤ (Cl : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count := by
      have hfun2 : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x))
          = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Work.KMTAreas.A7.Tle 1 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x)) := by
        funext x
        have hfam : (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x)
            = (fun j : ℕ => Work.KMTAreas.A7.Tle 1 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x) := by
          funext j
          rw [Tle_zero_rho_indep ρ 1]
        rw [hfam]
      rw [hfun2]
      refine hCl (fun j : ℕ => a (j + m)) ?_ (fun j => ha1 (j + m)) k₁ ?_ t ht F
      · intro j
        have h := ha (j + m)
        have hidx : j + 1 + m = (j + m) + 1 := by omega
        show Λ < a (j + 1 + m) / a (j + m)
        rw [hidx]; exact h
      · intro j
        exact Work.KMTAreas.A7.two_pow_le_floor_of_core
          ((hm (j + m)).mpr (Nat.le_add_left m j))
    have h2coe : ((2 : NNReal) : ENNReal) = (2 : ENNReal) := rfl
    have hcoef : (2 : ENNReal) * ((Cl : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2))
        ≤ (((2 * Cl * ((1 + B : ℕ) : NNReal) ^ 2 : NNReal)) : ENNReal) := by
      have hcast : (1 + (k₁ : ℝ)) = ((1 + k₁ : ℕ) : ℝ) := by push_cast; ring
      have hof : ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2) = ↑(((1 + k₁ : ℕ) : NNReal) ^ 2) := by
        rw [hcast, ENNReal.ofReal_pow (Nat.cast_nonneg (1 + k₁)), ENNReal.ofReal_natCast]
        rfl
      have hm2 : (((1 + k₁ : ℕ) : NNReal) ^ 2) ≤ (((1 + B : ℕ) : NNReal) ^ 2) := by
        have hle : ((1 + k₁ : ℕ) : NNReal) ≤ ((1 + B : ℕ) : NNReal) :=
          by exact_mod_cast Nat.add_le_add_left hk 1
        rw [sq, sq]; exact mul_le_mul' hle hle
      have hmid : (Cl : ENNReal) * ↑(((1 + k₁ : ℕ) : NNReal) ^ 2)
          ≤ (Cl : ENNReal) * ↑(((1 + B : ℕ) : NNReal) ^ 2) :=
        mul_le_mul' le_rfl (ENNReal.coe_le_coe.mpr hm2)
      have hmain : (2 : ENNReal) * ((Cl : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2))
          ≤ (2 : ENNReal) * ((Cl : ENNReal) * ↑(((1 + B : ℕ) : NNReal) ^ 2)) := by
        rw [hof]
        exact mul_le_mul' le_rfl hmid
      refine hmain.trans (le_of_eq ?_)
      rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_pow, h2coe]
      ring
    calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ 0 l₂ k₁ k₂ a n
              then Work.KMTAreas.A7.Tle ρ 0
                (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
              else 0)) 2 MeasureTheory.Measure.count
        ≤ 2 * MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun j : ℕ => Work.KMTAreas.A7.Tle ρ 0
              (Work.KMTAreas.A7.varphiNt (Nat.floor (a (j + m))) k₁ t) F x))
            2 MeasureTheory.Measure.count := hstep
      _ ≤ 2 * ((Cl : ENNReal) * ENNReal.ofReal ((1 + (k₁ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count) :=
            mul_le_mul' le_rfl hshift
      _ ≤ (((2 * Cl * ((1 + B : ℕ) : NNReal) ^ 2 : NNReal)) : ENNReal) *
              MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count := by
            rw [← mul_assoc]
            exact mul_le_mul' hcoef le_rfl
  · -- the `core` set is empty: the family vanishes identically
    have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ 0 l₂ k₁ k₂ a n
            then Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
            else 0))
        = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r (fun _ : ℕ => (0 : ℂ))) := by
      funext x
      have hfam : (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ 0 l₂ k₁ k₂ a n
            then Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
            else 0) = (fun _ : ℕ => (0 : ℂ)) := by
        funext n
        rw [if_neg (fun hc => hex ⟨n, hc⟩)]
      rw [hfam]
    rw [hzero, Work.KMTAreas.A7.eLpNorm_variationalNorm_zero hr1 2]
    exact zero_le

/-- **The `f`-side *level-0* (arithmetic-free) lacunary variational estimate at `p = 2`,
clipped to the core index set, for arbitrary `ρ > 0`.**  For every `B` there is `C : ℝ≥0 → ℝ≥0` such
that for every `Λ`-lacunary family `a` with `a n ≥ 1`, every `k₁ ≤ B` and every `t ∈ [1/2,1]`, the
`ℓ²(ℤ)` norm of the `r`-variation of `n ↦ 1_{core} Tle ρ 0 (varphiNt ⌊a n⌋ k₁ t) F` is at most
`C Λ ‖F‖₂`.

How to prove it (all ingredients are proved and axiom-clean; no `ρ ≤ 1` is needed):

* `Tle ρ 0 φ = iwConv (iwArithFreqs ρ 0) (periodize φ)` and `iwArithFreqs ρ 0 = {0}` for *every*
  `ρ` (`iwP ρ 0 = Icc 1 (2^0) = {1}`), so `Tle ρ 0` does not depend on `ρ`; transport the proved
  `Work.KMTAreas.A7.LoFLinVarClipped` (or `Work.KMTAreas.A7.LoLinVar`) from `ρ = 1` to the given `ρ`
  along that equality;
* `LoFLinVarClipped` is stated with the clip `core 1 …`; the clip of the statement is `core ρ …`.
  Both are *tails* in `n` (because `a` is monotone), and since only `k₁ ≤ B` is unbounded-free, the
  two clips differ only on a finite set of indices whose cardinality is bounded in terms of
  `ρ, C₀, B, Λ`; on that finite set each term is bounded pointwise by `‖cw φ‖_{ℓ²} ‖F‖₂ ≤ ‖F‖₂`
  (`Tle ρ 0 φ F x = ∑'_j (cw φ j) F (x - j)` and `‖cw φ‖_{ℓ²} = ‖periodize φ‖_{L²} ≤ 1`), so
  `V^r` of the difference family is bounded by `2 · ♯(finite set) · ‖F‖₂`.  Hence the constant of
  the estimate may absorb the change of clip;
* `LoFLinVarClipped` bounds by `ofReal (C * lossWeight 4 1 l₁ l₂ k₁ k₂)`, and with `lcL ≤ B`
  (equivalently the boundedness of `l₁, l₂, k₁, k₂`) the weight is bounded by a constant in
  `ρ, C₀, B`. -/
theorem plainVarF_lev0 (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (hC₀ : 1 ≤ C₀)
    (ρ : ℝ) (hρ : 0 < ρ) (B : ℕ) :
    ∃ C : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (t : ℝ) (F : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        k₁ ≤ B → t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTAreas.A7.core ρ C₀ 0 l₂ k₁ k₂ a n then
              Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t) F x
              else 0)) 2 MeasureTheory.Measure.count
          ≤ (C Λ : ENNReal) * MeasureTheory.eLpNorm F 2 MeasureTheory.Measure.count := by
  classical
  refine ⟨fun Λ => if h : 1 < Λ then
      Classical.choose (plainVarF_lev0_aux r hr C₀ hC₀ ρ hρ B Λ h) else 0, ?_⟩
  intro a Λ l₂ k₁ k₂ t F hΛ ha ha1 hk ht
  simp only [dif_pos hΛ]
  exact Classical.choose_spec (plainVarF_lev0_aux r hr C₀ hC₀ ρ hρ B Λ hΛ)
    a l₂ k₁ k₂ t F ha ha1 hk ht

end Work.KMTPlan.A6.LowModApproxBoundedH
