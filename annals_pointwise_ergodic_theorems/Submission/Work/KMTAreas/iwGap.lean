/-
# Area A1: the Ionescu–Wainger multiplier theorem for even exponents

Assembly of `Work.KMTAreas.IWEvenMultiplierGap` (MSZ3 Theorem 2.1 / Tao's `main` for the
workspace's concrete Ionescu–Wainger frequency sets `iwArithFreqs ρ l`) from the signed-strata
form of Tao's `main` (`Work.KMTAreas.main_signed_strata_uniform`), the arithmetic identification
`iwArithFreqs ρ l = P.biUnion sigmaStrataFinset` of the selected strata
(`Work.KMTAreas.strata_biUnion_eq_iwArithFreqs`), the elementary small-scale half
(`Work.KMTAreas.iwArithFreqs_small_scale`), the numeric core for large scales
(`Work.KMTAreas.iwSLmax_smallness_large`), the multiplier-norm transfer
(`Work.KMTAreas.IWMult_periodize`), the `tsum`-to-`eLpNorm` root extraction
(`Work.KMTAreas.eLpNorm_count_le_of_tsum_le`) and the quantitative scalar-to-vector lift
(`Work.KMTAreas.IWLqBound_of_scalar_mul`).

## The split at a threshold `l₀(r,ρ)`

With the *sharp* element bound `iwSLmax ρ l = max Q_0^{(l)} (2^{l D_ρ})` of Tao's denominator set
`S_l`, the arithmetic core `2r ε (iwSLmax)^{2r(D_ρ+1)} < 1/2` fails for no large scale
(`Work.KMTAreas.iwSLmax_smallness_large`), because `log₂ (iwSLmax ρ l) = O(2^{ρl/2} l)` grows
slower than `log₂ ε = k ≤ -2·2^{ρl}` decays.  Below the threshold the scale is finite and the
bound is elementary.  The threshold depends on `r` but not on `l`, matching the quantifier order
`∃C_ρ, ∀q, ∃C_q, ∀l,k` of Theorem `thm:iw`.
-/
import Mathlib
import Submission.Work.KMTAreas.strata_biUnion_eq_iwArithFreqs
import Submission.Work.KMTAreas.IWMult_periodize
import Submission.Work.KMTAreas.iwSLmax_smallness_large
import Submission.Work.KMTAreas.iwArithFreqs_small_scale
import Submission.Work.KMTAreas.eLpNorm_count_le_of_tsum_le
import Submission.Work.KMTAreas.main_signed_strata
import Submission.Work.KMTAreas.opArc_biUnion_strata
import Submission.Work.KMTAreas.opArc_eq_iwConv
import Submission.Work.KMTAreas.IsLqMultiplierBound_supNorm
import Submission.Work.BourgainPlan.IonescuWainger.petal_smallness_of_good
import Submission.Work.BourgainPlan.Maximal.exists_flat_bump_uniform

set_option autoImplicit false
set_option maxHeartbeats 4000000

open MeasureTheory ENNReal
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas

open Work.Analysis.IonescuWainger
open Work.BourgainPlan.IonescuWainger (sigmaStrataFinset QA opArc memℓp_finsupp HasNonce)
open Work.Analysis.IWMultiplier (IWLqBound IWLqBoundScalar iwConv angleBracket IsLqMultiplierBound
  one_le_angleBracket)

/-- The elementary numeric consequence of the "core" inequality: if `2r ε q^{2r(D+1)} < 1/2` then
`c ε q^a < 1` for every `1 ≤ c ≤ 2r` and `a ≤ 2r(D+1)` (with `q ≥ 1`, `ε ≥ 0`). -/
private lemma core_mul_lt {ε q : ℝ} (hq1 : 1 ≤ q) (hε : 0 ≤ ε) {r D : ℕ} (hr : 1 ≤ r)
    {c : ℝ} (hc1 : 1 ≤ c) (hc2 : c ≤ 2 * (r : ℝ)) {a : ℕ} (ha : a ≤ 2 * r * (D + 1))
    (hcore : 2 * (r : ℝ) * ε * q ^ (2 * r * (D + 1)) < 1 / 2) : c * ε * q ^ a < 1 := by
  have hq0 : (0 : ℝ) ≤ q := le_trans zero_le_one hq1
  have hqa : q ^ a ≤ q ^ (2 * r * (D + 1)) := pow_le_pow_right₀ hq1 ha
  have h1 : c * q ^ a ≤ 2 * (r : ℝ) * q ^ (2 * r * (D + 1)) := by
    calc c * q ^ a ≤ (2 * (r : ℝ)) * q ^ a :=
          mul_le_mul_of_nonneg_right hc2 (pow_nonneg hq0 a)
      _ ≤ (2 * (r : ℝ)) * q ^ (2 * r * (D + 1)) :=
          mul_le_mul_of_nonneg_left hqa (by positivity)
  calc c * ε * q ^ a = ε * (c * q ^ a) := by ring
    _ ≤ ε * (2 * (r : ℝ) * q ^ (2 * r * (D + 1))) := mul_le_mul_of_nonneg_left h1 hε
    _ = 2 * (r : ℝ) * ε * q ^ (2 * r * (D + 1)) := by ring
    _ < 1 / 2 := hcore
    _ < 1 := by norm_num

/-- The smallness hypothesis of Tao's `main` from the "core" inequality. -/
private lemma eps_lt_div_of_core {ε q : ℝ} (hq1 : 1 ≤ q) (hε0 : 0 < ε) {r D : ℕ} (hr : 1 ≤ r)
    (hcore : 2 * (r : ℝ) * ε * q ^ (2 * r * (D + 1)) < 1 / 2) :
    ε < (1 / 2) / (2 * (r : ℝ) * q ^ (2 * r * (D + 1))) := by
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le zero_lt_one hq1
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hden : (0 : ℝ) < 2 * (r : ℝ) * q ^ (2 * r * (D + 1)) := by positivity
  rw [lt_div_iff₀ hden]
  have heq : ε * (2 * (r : ℝ) * q ^ (2 * r * (D + 1)))
      = 2 * (r : ℝ) * ε * q ^ (2 * r * (D + 1)) := by ring
  rw [heq]
  exact hcore

/-- An indicator-weighted sum over a finset is the sum over the filtered finset. -/
private lemma sum_indicator_mul {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    (F : ι → ℂ) : ∑ A ∈ s, (if p A then (1 : ℂ) else 0) * F A = ∑ A ∈ s.filter p, F A := by
  have hterm : ∀ A : ι, (if p A then (1 : ℂ) else 0) * F A = if p A then F A else 0 := by
    intro A
    by_cases h : p A <;> simp [h]
  simp_rw [hterm]
  rw [← Finset.sum_filter]

/-- **Area A1's multiplier gap** (MSZ3 Theorem 2.1 / Tao's `main` for the concrete frequency sets
`iwArithFreqs ρ l` of Appendix A of Krause–Mirek–Tao). -/
theorem iwEvenMultiplierGap_proof : IWEvenMultiplierGap := by
  intro ρ hρ hρ1
  refine ⟨2, by norm_num, ?_⟩
  intro r hr
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  obtain ⟨l₀, hl₀⟩ := iwSLmax_smallness_large ρ hρ hρ1 r hr (Cρ := 2) (by norm_num)
  obtain ⟨Cs, hCspos, hsmall⟩ :=
    iwArithFreqs_small_scale ρ hρ hρ1 r hr (Cρ := 2) (le_refl 2) (max (iwC0 ρ + 1) l₀)
  obtain ⟨Cφ, hCφpos, hbump⟩ := Work.BourgainPlan.Maximal.exists_flat_bump_uniform
  have hD1 : 1 ≤ iwD ρ + 1 := Nat.le_add_left 1 _
  obtain ⟨K, hKpos, hmain⟩ := main_signed_strata_uniform (k := iwD ρ + 1) (r := r) hr hD1
    (Cφ := Cφ) (Mφ := 1) hCφpos.le (by norm_num)
  have hq1 : (1 : ENNReal) ≤ ((2 * r : ℕ) : ENNReal) := by
    exact_mod_cast (show 1 ≤ 2 * r by omega)
  have hq2 : ((2 * r : ℕ) : ENNReal) < ⊤ := ENNReal.natCast_lt_top (2 * r)
  obtain ⟨κ, hκpos, hκ⟩ := IWLqBound_of_scalar_mul (q := ((2 * r : ℕ) : ENNReal)) hq1 hq2
  set C₁ : NNReal := Real.toNNReal (K ^ (1 / (2 * (r : ℝ)))) with hC₁def
  set Cd : NNReal := C₁ * κ with hCddef
  refine ⟨max Cs (max 1 Cd), lt_of_lt_of_le hCspos (le_max_left _ _), ?_⟩
  intro l k hgood φ hφ M hM
  by_cases hl : l ≤ max (iwC0 ρ + 1) l₀
  · -- ## the small scales
    refine IWLqBound.mono (hsmall l hl k hgood φ hφ M hM) ?_
    calc Cs * M ≤ max Cs (max 1 Cd) * M :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max Cs (max 1 Cd) * (angleBracket l * M) :=
          mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_left (by positivity) (one_le_angleBracket l)) (by positivity)
      _ = max Cs (max 1 Cd) * angleBracket l * M := by ring
  · -- ## the deep route
    rw [not_le] at hl
    have hlC0 : iwC0 ρ < l := by omega
    have hll₀ : l₀ ≤ l := by omega
    have hpair := iwSL_pairwise ρ hρ l
    have h2S : ∀ q ∈ iwSL ρ l, 2 ≤ q := hpair.1
    have hS : ∀ p ∈ iwSL ρ l, ∀ q ∈ iwSL ρ l, p ≠ q → Nat.Coprime p q := hpair.2
    have hqmax1 : 1 ≤ iwSLmax ρ l :=
      le_trans (le_trans (by norm_num : (1 : ℕ) ≤ 2) (two_le_iwQ0 ρ hρ l))
        (le_max_left (iwQ0 ρ l) (2 ^ (l * iwD ρ)))
    have hmax : ∀ q ∈ iwSL ρ l, q ≤ iwSLmax ρ l := iwSLmax_element_le ρ l
    have hqmaxpos : (0 : ℝ) < ((iwSLmax ρ l : ℕ) : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hqmax1 : (0 : ℕ) < iwSLmax ρ l)
    have hqmax1R : (1 : ℝ) ≤ ((iwSLmax ρ l : ℕ) : ℝ) := by exact_mod_cast hqmax1
    have hcore : 2 * (r : ℝ) * (2 : ℝ) ^ k *
        ((iwSLmax ρ l : ℕ) : ℝ) ^ (2 * r * (iwD ρ + 1)) < 1 / 2 := hl₀ l hll₀ k hgood
    have hle : (k : ℝ) ≤ -2 := by
      have h2ρ : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) :=
        Real.one_le_rpow (by norm_num) (by positivity)
      have h := hgood
      rw [GoodMajorArcs] at h
      nlinarith
    have hle1Z : k ≤ (-1 : ℤ) := by
      exact_mod_cast (show (k : ℝ) ≤ -1 by linarith)
    have hle2Z : k ≤ (-2 : ℤ) := by exact_mod_cast hle
    have hk_half : (2 : ℝ) ^ k ≤ 1 / 2 := by
      have h1 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (-1 : ℤ) :=
        zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hle1Z
      have h2 : (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 := by rw [zpow_neg_one]; norm_num
      exact le_trans h1 h2.le
    have hk4 : (2 : ℝ) ^ k ≤ 1 / 4 := by
      have h1 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (-2 : ℤ) :=
        zpow_le_zpow_right₀ (a := (2 : ℝ)) (by norm_num) hle2Z
      have h2 : (2 : ℝ) ^ (-2 : ℤ) = 1 / 4 := by
        rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, zpow_neg, zpow_ofNat]
        norm_num
      exact le_trans h1 h2.le
    have hkpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    have hqpow_pos : (0 : ℝ) < ((iwSLmax ρ l : ℕ) : ℝ) ^ (2 * (iwD ρ + 1)) :=
      pow_pos hqmaxpos _
    have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    have hr2R : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have h2r3 : (3 : ℝ) ≤ 2 * (r : ℝ) := by linarith
    have key3 : 3 * (2 : ℝ) ^ k * ((iwSLmax ρ l : ℕ) : ℝ) ^ (2 * (iwD ρ + 1)) < 1 :=
      core_mul_lt hqmax1R hkpos.le hr1 (c := 3) (by norm_num) h2r3
        (Nat.mul_le_mul_right (iwD ρ + 1) (by omega : 2 ≤ 2 * r)) hcore
    have key4 : 4 * (2 : ℝ) ^ k * ((iwSLmax ρ l : ℕ) : ℝ) ^ (2 * (iwD ρ + 1)) < 1 :=
      core_mul_lt hqmax1R hkpos.le hr1 (c := 4) (by norm_num) (by linarith [hr2R])
        (Nat.mul_le_mul_right (iwD ρ + 1) (by omega : 2 ≤ 2 * r)) hcore
    have key1 : 1 * (2 : ℝ) ^ k * ((iwSLmax ρ l : ℕ) : ℝ) ^ (iwD ρ + 1) < 1 :=
      core_mul_lt hqmax1R hkpos.le hr1 (c := 1) le_rfl (by linarith [hr1R])
        (Nat.le_mul_of_pos_left _ (by omega : 0 < 2 * r)) hcore
    have key2 : 2 * (2 : ℝ) ^ k * ((iwSLmax ρ l : ℕ) : ℝ) ^ (iwD ρ + 1) < 1 :=
      core_mul_lt hqmax1R hkpos.le hr1 (c := 2) (by norm_num) (by linarith [hr1R])
        (Nat.le_mul_of_pos_left _ (by omega : 0 < 2 * r)) hcore
    have hεη : (2 : ℝ) ^ k + 2 * (2 : ℝ) ^ k
        < 1 / ((iwSLmax ρ l : ℕ) : ℝ) ^ (2 * (iwD ρ + 1)) := by
      rw [lt_div_iff₀ hqpow_pos]
      have he : ((2 : ℝ) ^ k + 2 * (2 : ℝ) ^ k) * ((iwSLmax ρ l : ℕ) : ℝ) ^ (2 * (iwD ρ + 1))
          = 3 * (2 : ℝ) ^ k * ((iwSLmax ρ l : ℕ) : ℝ) ^ (2 * (iwD ρ + 1)) := by ring
      rw [he]
      exact key3
    have hη2 : 2 * (2 * (2 : ℝ) ^ k)
        < 1 / ((iwSLmax ρ l : ℕ) : ℝ) ^ (2 * (iwD ρ + 1)) := by
      rw [lt_div_iff₀ hqpow_pos]
      have he : (2 * (2 * (2 : ℝ) ^ k)) * ((iwSLmax ρ l : ℕ) : ℝ) ^ (2 * (iwD ρ + 1))
          = 4 * (2 : ℝ) ^ k * ((iwSLmax ρ l : ℕ) : ℝ) ^ (2 * (iwD ρ + 1)) := by ring
      rw [he]
      exact key4
    have hεq : (2 : ℝ) ^ k * ((iwSLmax ρ l : ℕ) : ℝ) ^ (iwD ρ + 1) ≤ 1 := by
      simpa using key1.le
    have hεq2 : (2 : ℝ) ^ k * ((iwSLmax ρ l : ℕ) : ℝ) ^ (iwD ρ + 1) < 1 / 2 := by
      rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      have he : (2 : ℝ) ^ k * ((iwSLmax ρ l : ℕ) : ℝ) ^ (iwD ρ + 1) * 2
          = 2 * (2 : ℝ) ^ k * ((iwSLmax ρ l : ℕ) : ℝ) ^ (iwD ρ + 1) := by ring
      rw [he]
      exact key2
    have hgood' : (2 : ℝ) ^ k < (1 / 2) /
        (2 * (r : ℝ) * ((iwSLmax ρ l : ℕ) : ℝ) ^ (2 * r * (iwD ρ + 1))) :=
      eps_lt_div_of_core hqmax1R hkpos hr1 hcore
    have hsmallN : ∀ A : Fin r ⊕ Fin r → Finset ℕ,
        (∀ j, A j ⊆ iwSL ρ l ∧ (A j).card ≤ iwD ρ + 1) → HasNonce A →
        2 * (r : ℝ) * (2 : ℝ) ^ k < 1 / ((∏ j, QA (A j) : ℕ) : ℝ) := by
      intro A hA _
      exact Work.BourgainPlan.IonescuWainger.nonce_smallness_of_good (c := (1 / 2)) h2S
        hqmax1 hmax (by norm_num) (by norm_num) hgood' (fun j => (hA j).1) (fun j => (hA j).2)
    have hsmallP : ∀ A₀ ∈ (iwSL ρ l).powerset.filter (fun A => A.card ≤ iwD ρ + 1),
        ∀ A : (i : Fin r) → ↥(((iwSL ρ l) \ A₀).powerset.filter
            (fun B => B.card ≤ iwD ρ + 1 - A₀.card)),
          (∀ i j : Fin r, i ≠ j → Disjoint ((A i).1) ((A j).1)) →
          2 * (r : ℝ) * (2 : ℝ) ^ k * ((QA A₀ * (∏ i, QA ((A i).1)) : ℕ) : ℝ) < 1 := by
      intro A₀ hA₀ A _
      exact Work.BourgainPlan.IonescuWainger.petal_smallness_of_good (c := (1 / 2)) h2S
        hqmax1 hmax (by norm_num) (by norm_num) hgood'
        (Finset.mem_powerset.mp (Finset.mem_filter.mp hA₀).1) ((Finset.mem_filter.mp hA₀).2)
        (fun i => Finset.mem_powerset.mp (Finset.mem_filter.mp (A i).2).1)
        (fun i => (Finset.mem_filter.mp (A i).2).2)
    have hφsup : ∀ x : ℝ, ‖(φ : ℝ → ℂ) x‖ ≤ (M : ℝ) :=
      IsLqMultiplierBound_supNorm (p := ((2 * r : ℕ) : ENNReal)) hq1 hq2 φ.continuous hM
    have hφ0 : ∀ x : ℝ, (2 : ℝ) ^ k < |x| → (φ : ℝ → ℂ) x = 0 := by
      intro x hx
      by_contra hne
      have hmem := hφ x hne
      rw [realArc, Set.mem_Icc] at hmem
      have : |x| ≤ (2 : ℝ) ^ k := abs_le.mpr hmem
      linarith
    have hψmem : MemLp (periodize (φ : ℝ → ℂ)) ⊤ (AddCircle.haarAddCircle (T := 1)) :=
      memLp_periodize φ.continuous.measurable (R := (2 : ℝ) ^ k) (C := (M : ℝ))
        hkpos.le hφ0 hφsup
    have hψsupp : ∀ ξ : Work.BourgainPlan.IonescuWainger.Circle,
        (2 : ℝ) ^ k < ‖ξ‖ → periodize (φ : ℝ → ℂ) ξ = 0 := by
      intro ξ hξ
      by_contra hne
      obtain ⟨θ, hθ, hθξ⟩ := supportedInArc_periodize (φ := (φ : ℝ → ℂ)) hφ
        (fun x => (schwartz_shift_summable φ x).of_norm) ξ hne
      rw [realArc, Set.mem_Icc] at hθ
      have hθle : |θ| ≤ (2 : ℝ) ^ k := abs_le.mpr hθ
      have hnorm : ‖(θ : Work.BourgainPlan.IonescuWainger.Circle)‖ = |θ| :=
        (AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero (x := θ)).mpr
          (by simpa using (le_trans hθle hk_half : |θ| ≤ 1 / 2))
      rw [← hθξ, hnorm] at hξ
      linarith
    obtain ⟨φ', hφ'mem, hφ'bd, hφ'supp, hφ'one, hφ'decay⟩ :=
      hbump ((2 : ℝ) ^ k) (2 * (2 : ℝ) ^ k) hkpos (le_refl _) (by linarith)
    set Kφ : ℤ → ℂ := fun m => ∫ ξ, φ' ξ * star (fourier m ξ)
      ∂(AddCircle.haarAddCircle (T := 1)) with hKφdef
    have hKφ : ∀ m : ℤ, ∫ ξ, φ' ξ * star (fourier m ξ)
        ∂(AddCircle.haarAddCircle (T := 1)) = Kφ m := fun m => rfl
    have hdecayφ : ∀ m : ℤ, ‖Kφ m‖ ≤ Cφ * (2 * (2 : ℝ) ^ k) /
        (1 + ((2 * (2 : ℝ) ^ k) * (m : ℝ)) ^ 2) ^ ((3 : ℝ) / 2) := fun m => hφ'decay m
    have hMult : Work.BourgainPlan.Maximal.IWMult r (periodize (φ : ℝ → ℂ)) M :=
      IWMult_periodize hr hk_half hφ hM
    -- ### the selected strata
    set SS : Finset (Finset ℕ) := (iwSL ρ l).powerset.filter (fun A => A.card ≤ iwD ρ + 1)
      with hSSdef
    set PP : Finset (Finset ℕ) := SS.filter (fun A => iwQ0 ρ l ∈ A ∨ A.card ≤ iwD ρ)
      with hPPdef
    have hPPU : PP.biUnion sigmaStrataFinset = iwArithFreqs ρ l := by
      rw [hPPdef, hSSdef]
      exact strata_biUnion_eq_iwArithFreqs ρ hρ hρ1 hlC0
    have hdisj : ∀ A ∈ PP, ∀ B ∈ PP, A ≠ B →
        Disjoint (sigmaStrataFinset A) (sigmaStrataFinset B) := by
      intro A hA B hB hAB
      rw [hPPdef, hSSdef, Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset] at hA hB
      exact Work.BourgainPlan.IonescuWainger.disjoint_sigmaStrataFinset h2S hS
        hA.1.1 hB.1.1 hAB
    have hεs : ∀ A : Finset ℕ,
        ‖(if iwQ0 ρ l ∈ A ∨ A.card ≤ iwD ρ then (1 : ℂ) else 0)‖ ≤ 1 := by
      intro A
      by_cases h : iwQ0 ρ l ∈ A ∨ A.card ≤ iwD ρ <;> simp [h]
    -- ### the scalar `ℓ^{2r}` bound
    have hscal : IWLqBoundScalar (iwArithFreqs ρ l) (periodize (φ : ℝ → ℂ))
        ((2 * r : ℕ) : ENNReal) (C₁ * M) := by
      intro g hg
      obtain ⟨f, hf⟩ : ∃ f : ℤ →₀ ℂ, (⇑f : ℤ → ℂ) = g :=
        ⟨Finsupp.ofSupportFinite g hg, Finsupp.ofSupportFinite_coe⟩
      have hbound := hmain hqmax1 h2S hS hmax hkpos (by linarith [hkpos]) hεη hη2 hεq hεq2
        (periodize (φ : ℝ → ℂ)) hψmem hψsupp M M.coe_nonneg hMult
        φ' hφ'mem hφ'bd hφ'supp hφ'one hKφ hdecayφ hsmallN hsmallP
        (fun A : Finset ℕ => if iwQ0 ρ l ∈ A ∨ A.card ≤ iwD ρ then (1 : ℂ) else 0) hεs f
      have hSumFun : (fun n : ℤ => ∑ A ∈ SS,
            (if iwQ0 ρ l ∈ A ∨ A.card ≤ iwD ρ then (1 : ℂ) else 0) *
              opArc (periodize (φ : ℝ → ℂ)) hψmem (sigmaStrataFinset A) (⇑f)
                (memℓp_finsupp f) n)
          = (fun n : ℤ => ∑ A ∈ PP, opArc (periodize (φ : ℝ → ℂ)) hψmem
              (sigmaStrataFinset A) (⇑f) (memℓp_finsupp f) n) := by
        funext n
        rw [sum_indicator_mul, ← hPPdef]
      have hSumFun2 : (fun n : ℤ => ∑ A ∈ PP, opArc (periodize (φ : ℝ → ℂ)) hψmem
              (sigmaStrataFinset A) (⇑f) (memℓp_finsupp f) n)
          = opArc (periodize (φ : ℝ → ℂ)) hψmem (iwArithFreqs ρ l) (⇑f)
              (memℓp_finsupp f) := by
        have h1 : (fun n : ℤ => ∑ A ∈ PP, opArc (periodize (φ : ℝ → ℂ)) hψmem
              (sigmaStrataFinset A) (⇑f) (memℓp_finsupp f) n)
            = (fun n : ℤ => (∑ A ∈ PP, opArc (periodize (φ : ℝ → ℂ)) hψmem
                (sigmaStrataFinset A) (⇑f) (memℓp_finsupp f)) n) := by
          funext n
          rw [Finset.sum_apply]
        rw [h1, ← opArc_biUnion_strata (periodize (φ : ℝ → ℂ)) hψmem PP hdisj (⇑f)
          (memℓp_finsupp f), hPPU]
      have hL : (∑' n : ℤ, ENNReal.ofReal (‖opArc (periodize (φ : ℝ → ℂ)) hψmem
            (iwArithFreqs ρ l) (⇑f) (memℓp_finsupp f) n‖ ^ (2 * r)))
          = ∑' n : ℤ, ENNReal.ofReal (‖∑ A ∈ SS,
              (if iwQ0 ρ l ∈ A ∨ A.card ≤ iwD ρ then (1 : ℂ) else 0) *
                opArc (periodize (φ : ℝ → ℂ)) hψmem (sigmaStrataFinset A) (⇑f)
                  (memℓp_finsupp f) n‖ ^ (2 * r)) := by
        refine tsum_congr fun n => congrArg (fun z : ℂ => ENNReal.ofReal (‖z‖ ^ (2 * r))) ?_
        exact (congrFun (hSumFun.trans hSumFun2) n).symm
      have htsum : ∑' n : ℤ, ENNReal.ofReal (‖opArc (periodize (φ : ℝ → ℂ)) hψmem
            (iwArithFreqs ρ l) (⇑f) (memℓp_finsupp f) n‖ ^ (2 * r))
          ≤ ENNReal.ofReal (K * (M : ℝ) ^ (2 * r)) *
            ∑' n : ℤ, ENNReal.ofReal (‖(⇑f : ℤ → ℂ) n‖ ^ (2 * r)) := by
        rw [hL]
        exact hbound
      have hroot := eLpNorm_count_le_of_tsum_le (r := r) hr1
        (X := fun n => opArc (periodize (φ : ℝ → ℂ)) hψmem (iwArithFreqs ρ l) (⇑f)
          (memℓp_finsupp f) n)
        (Y := (⇑f : ℤ → ℂ)) (C := K * (M : ℝ) ^ (2 * r)) (by positivity) htsum
      have hXeq : (fun n => opArc (periodize (φ : ℝ → ℂ)) hψmem (iwArithFreqs ρ l) (⇑f)
            (memℓp_finsupp f) n)
          = fun n => iwConv (iwArithFreqs ρ l) (periodize (φ : ℝ → ℂ)) g n := by
        funext n
        rw [← hf]
        exact opArc_eq_iwConv (periodize (φ : ℝ → ℂ)) hψmem (iwArithFreqs ρ l) (⇑f)
          (memℓp_finsupp f) n
      have hconst : ENNReal.ofReal ((K * (M : ℝ) ^ (2 * r)) ^ (1 / (2 * (r : ℝ))))
          = ENNReal.ofReal (((C₁ * M : NNReal)) : ℝ) := by
        congr 1
        have hMnn : (0 : ℝ) ≤ (M : ℝ) := M.coe_nonneg
        have hval : (((C₁ * M : NNReal)) : ℝ) = K ^ (1 / (2 * (r : ℝ))) * (M : ℝ) := by
          rw [hC₁def, NNReal.coe_mul, Real.coe_toNNReal _ (Real.rpow_nonneg hKpos.le _)]
        rw [hval]
        rw [show (M : ℝ) ^ (2 * r) = (M : ℝ) ^ (2 * (r : ℝ)) by
          rw [show (2 * (r : ℝ)) = ((2 * r : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]]
        rw [Real.mul_rpow hKpos.le (Real.rpow_nonneg hMnn _)]
        rw [← Real.rpow_mul hMnn (2 * (r : ℝ)) (1 / (2 * (r : ℝ)))]
        rw [show 2 * (r : ℝ) * (1 / (2 * (r : ℝ))) = 1 by field_simp]
        rw [Real.rpow_one]
      rw [hXeq, hconst] at hroot
      simpa [hf] using hroot
    -- ### the vector-valued bound and the constant
    have hvec : IWLqBound (iwArithFreqs ρ l) (periodize (φ : ℝ → ℂ))
        ((2 * r : ℕ) : ENNReal) ((C₁ * M) * κ) := hκ hscal
    refine IWLqBound.mono hvec ?_
    calc (C₁ * M) * κ = Cd * M := by rw [hCddef]; ring
      _ ≤ max Cs (max 1 Cd) * M :=
          mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_right _ _)) (by positivity)
      _ ≤ max Cs (max 1 Cd) * (angleBracket l * M) :=
          mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_left (by positivity) (one_le_angleBracket l)) (by positivity)
      _ = max Cs (max 1 Cd) * angleBracket l * M := by ring

end Work.KMTAreas
