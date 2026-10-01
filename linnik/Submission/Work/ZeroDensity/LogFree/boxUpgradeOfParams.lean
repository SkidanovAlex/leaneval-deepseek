import Mathlib
import Submission.Work.ZeroDensity.LogFree.RouteDefs
import Submission.Work.ZeroDensity.Jutila.jutilaNonPrincipal
import Submission.Work.ZeroDensity.LogFree.boxMassGeneral
import Submission.Work.ZeroDensity.LogFree.excZeroReal
import Submission.Work.ZeroDensity.LogFree.excCharUnique
import Submission.Work.ZeroDensity.LogFree.cardSystemLeM

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity.LogFree

open Work.ZeroDensity.Jutila

/-! ## Helpers -/

/-- A non-trivial zero (`zeroMult ≠ 0`) of a non-principal character has real part `< 1`. -/
lemma zeroMult_re_lt_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {ρ : ℂ}
    (hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0) : ρ.re < 1 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hΛ : DirichletCharacter.completedLFunction χ.primitiveCharacter ρ = 0 := by
    have h' := apply_eq_zero_of_analyticOrderNatAt_ne_zero hzm
    simpa [Work.LinnikContract.zeroMult] using h'
  have hstrip := Commons.NumberTheory.DirichletCharacter.zerosInStrip χ.primitiveCharacter
    (Work.A7.primitiveCharacter_ne_one hχ)
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) ρ hΛ
  exact hstrip.2

/-- The box `k` at scale `Δ` is the half-open interval `[kΔ, (k+1)Δ)` of imaginary parts. -/
lemma boxIdx_bounds {Δ : ℝ} (hΔ : 0 < Δ) {k : ℤ} {ρ : ℂ} (h : boxIdx Δ ρ = k) :
    (k : ℝ) * Δ ≤ ρ.im ∧ ρ.im < ((k : ℝ) + 1) * Δ := by
  have hfl : ((k : ℝ)) ≤ ρ.im / Δ ∧ ρ.im / Δ < (k : ℝ) + 1 := Int.floor_eq_iff.mp h
  exact ⟨(le_div_iff₀ hΔ).mp hfl.1, (div_lt_iff₀ hΔ).mp hfl.2⟩

/-- If `2 ∣ (a-b)` and `a ≠ b` then `|a-b| ≥ 2`. -/
lemma two_le_abs_sub_of_dvd {a b : ℤ} (h2 : (2 : ℤ) ∣ (a - b)) (hne : a ≠ b) :
    (2 : ℤ) ≤ |a - b| := by
  obtain ⟨c, hc⟩ := h2
  have hc0 : c ≠ 0 := by
    intro h0
    apply hne
    have : a - b = 0 := by rw [hc, h0]; ring
    linarith
  have h1 : (1 : ℤ) ≤ |c| := by
    have := abs_pos.mpr hc0
    omega
  calc (2 : ℤ) = 2 * 1 := by ring
    _ ≤ 2 * |c| := by linarith [h1]
    _ = |a - b| := by rw [hc, abs_mul]; norm_num

lemma even_two_dvd {a b : ℤ} (ha : Even a) (hb : Even b) : (2 : ℤ) ∣ (a - b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  exact ⟨x - y, by rw [hx, hy]; ring⟩

lemma odd_two_dvd {a b : ℤ} (ha : Odd a) (hb : Odd b) : (2 : ℤ) ∣ (a - b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  exact ⟨x - y, by rw [hx, hy]; ring⟩

/-- The **even occupied boxes** of a finite zero set `S` at scale `Δ`. -/
def boxEven (S : Finset ℂ) (Δ : ℝ) : Finset ℤ :=
  (S.image (boxIdx Δ)).filter (fun k => Even k)

/-- The **odd occupied boxes** of a finite zero set `S` at scale `Δ`. -/
def boxOdd (S : Finset ℂ) (Δ : ℝ) : Finset ℤ :=
  (S.image (boxIdx Δ)).filter (fun k => ¬ Even k)

/-- The **larger parity class** of occupied boxes: the parity split of Jutila §3. -/
def boxPar (S : Finset ℂ) (Δ : ℝ) : Finset ℤ :=
  if (boxEven S Δ).card ≤ (boxOdd S Δ).card then boxOdd S Δ else boxEven S Δ

lemma boxPar_card (S : Finset ℂ) (Δ : ℝ) :
    (boxPar S Δ).card = max (boxEven S Δ).card (boxOdd S Δ).card := by
  rw [boxPar]
  by_cases h : (boxEven S Δ).card ≤ (boxOdd S Δ).card
  · rw [if_pos h, max_eq_right h]
  · rw [if_neg h, max_eq_left (le_of_lt (not_le.mp h))]

lemma boxPar_sub (S : Finset ℂ) (Δ : ℝ) : boxPar S Δ ⊆ S.image (boxIdx Δ) := by
  intro k hk
  rw [boxPar] at hk
  by_cases h : (boxEven S Δ).card ≤ (boxOdd S Δ).card
  · rw [if_pos h, boxOdd] at hk
    exact (Finset.mem_filter.mp hk).1
  · rw [if_neg h, boxEven] at hk
    exact (Finset.mem_filter.mp hk).1

lemma boxPar_two_le_abs_sub (S : Finset ℂ) (Δ : ℝ) {k k' : ℤ}
    (hk : k ∈ boxPar S Δ) (hk' : k' ∈ boxPar S Δ) (hne : k ≠ k') :
    (2 : ℤ) ≤ |k - k'| := by
  rw [boxPar] at hk hk'
  by_cases h : (boxEven S Δ).card ≤ (boxOdd S Δ).card
  · rw [if_pos h, boxOdd] at hk hk'
    rw [Finset.mem_filter] at hk hk'
    have hkO : Odd k := by
      rcases Int.even_or_odd k with hE | hO
      · exact absurd hE hk.2
      · exact hO
    have hkO' : Odd k' := by
      rcases Int.even_or_odd k' with hE | hO
      · exact absurd hE hk'.2
      · exact hO
    exact two_le_abs_sub_of_dvd (odd_two_dvd hkO hkO') hne
  · rw [if_neg h, boxEven] at hk hk'
    rw [Finset.mem_filter] at hk hk'
    exact two_le_abs_sub_of_dvd (even_two_dvd hk.2 hk'.2) hne

/-- Two zeros lying in boxes of the same parity class are `Δ`-separated. -/
lemma abs_im_sub_ge_of_boxes {Δ : ℝ} (hΔ : 0 < Δ) {ρ ρ' : ℂ} {k k' : ℤ}
    (h : boxIdx Δ ρ = k) (h' : boxIdx Δ ρ' = k') (h2 : (2 : ℤ) ≤ |k - k'|) :
    Δ ≤ |ρ.im - ρ'.im| := by
  obtain ⟨hb1, hb2⟩ := boxIdx_bounds hΔ h
  obtain ⟨hb1', hb2'⟩ := boxIdx_bounds hΔ h'
  have hne : k ≠ k' := by
    intro hh
    rw [hh, sub_self, abs_zero] at h2
    omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hrel : (2 : ℤ) ≤ k' - k := by
      have : |k - k'| = k' - k := by rw [abs_of_neg (by omega : k - k' < 0)]; ring
      rw [← this]; exact h2
    have hk2 : (k : ℝ) + 2 ≤ (k' : ℝ) := by exact_mod_cast (by omega : k + 2 ≤ k')
    have hstep : Δ < ρ'.im - ρ.im := by
      have h1 : ((k : ℝ) + 2) * Δ ≤ (k' : ℝ) * Δ := mul_le_mul_of_nonneg_right hk2 hΔ.le
      have h2' : (k : ℝ) * Δ + 2 * Δ ≤ ρ'.im := by
        calc (k : ℝ) * Δ + 2 * Δ = ((k : ℝ) + 2) * Δ := by ring
          _ ≤ (k' : ℝ) * Δ := h1
          _ ≤ ρ'.im := hb1'
      have h3 : ρ.im < (k : ℝ) * Δ + Δ := by nlinarith [hb2]
      nlinarith [h2', h3]
    rw [abs_sub_comm, abs_of_pos (by linarith : 0 < ρ'.im - ρ.im)]
    linarith
  · have hrel : (2 : ℤ) ≤ k - k' := by
      have : |k - k'| = k - k' := by rw [abs_of_pos (by omega : 0 < k - k')]
      rw [← this]; exact h2
    have hk2 : (k' : ℝ) + 2 ≤ (k : ℝ) := by exact_mod_cast (by omega : k' + 2 ≤ k)
    have hstep : Δ < ρ.im - ρ'.im := by
      have h1 : ((k' : ℝ) + 2) * Δ ≤ (k : ℝ) * Δ := mul_le_mul_of_nonneg_right hk2 hΔ.le
      have h2' : (k' : ℝ) * Δ + 2 * Δ ≤ ρ.im := by
        calc (k' : ℝ) * Δ + 2 * Δ = ((k' : ℝ) + 2) * Δ := by ring
          _ ≤ (k : ℝ) * Δ := h1
          _ ≤ ρ.im := hb1
      have h3 : ρ'.im < (k' : ℝ) * Δ + Δ := by nlinarith [hb2']
      nlinarith [h2', h3]
    rw [abs_of_pos (by linarith : 0 < ρ.im - ρ'.im)]
    linarith

lemma boxPar_sep (S : Finset ℂ) (Δ : ℝ) (hΔ : 0 < Δ) {ρ ρ' : ℂ} {k k' : ℤ}
    (hk : k ∈ boxPar S Δ) (hk' : k' ∈ boxPar S Δ) (hρ : boxIdx Δ ρ = k)
    (hρ' : boxIdx Δ ρ' = k') (hne : k ≠ k') : Δ ≤ |ρ.im - ρ'.im| :=
  abs_im_sub_ge_of_boxes hΔ hρ hρ' (boxPar_two_le_abs_sub S Δ hk hk' hne)

/-- **L6 of `JUTILA_UNIFIED_LEAD.md` §3: the box upgrade with a general exponent** — the box/parity
upgrade turning a bound `M` for every `c₀`-non-exceptional `1/L`-separated system into a bound for
the whole non-principal zero count. -/
theorem boxUpgradeOfParams (p : Work.ZeroDensity.LogFree.Params) :
    Work.ZeroDensity.LogFree.BoxUpgrade p := by
  obtain ⟨Cbox, hCboxpos, hCbox⟩ := boxMassGeneral
  obtain ⟨cB, hcBpos, hcB⟩ := excZeroReal
  obtain ⟨cE, hcEpos, qE, hcE⟩ := excCharUnique
  set c₀ : ℝ := min cB cE with hc₀def
  have hc₀pos : 0 < c₀ := by rw [hc₀def]; exact lt_min hcBpos hcEpos
  have hc₀B : c₀ ≤ cB := by rw [hc₀def]; exact min_le_left _ _
  have hc₀E : c₀ ≤ cE := by rw [hc₀def]; exact min_le_right _ _
  set Kob : ℕ := max qE 1 with hKobdef
  refine ⟨12 * Cbox * ((Kob : ℝ) + 1), by positivity, c₀, hc₀pos, 1, by norm_num, ?_⟩
  intro q hq _inst T σ hT _hD hσ0 hσ1 M hM hhyp
  -- ## elementary bounds on the scale
  have hσpos : 0 < σ := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) (le_trans (le_of_lt p.hσ₀) hσ0)
  have hL1 : 1 ≤ Lscale q T := by
    rw [Lscale, scale]
    have h6 : (6 : ℝ) ≤ (q : ℝ) * (T + 2) := by
      have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
      have h3 : (3 : ℝ) ≤ T + 2 := by linarith
      nlinarith
    have hlog6 : (1 : ℝ) ≤ Real.log 6 := by
      have h1 : Real.exp 1 ≤ (6 : ℝ) := by have he := Real.exp_one_lt_three; linarith
      have h2 : Real.log (Real.exp 1) ≤ Real.log 6 := Real.log_le_log (Real.exp_pos 1) h1
      have h3 : Real.log (Real.exp 1) = 1 := Real.log_exp 1
      linarith
    exact le_trans hlog6 (Real.log_le_log (by norm_num) h6)
  have hLpos : 0 < Lscale q T := lt_of_lt_of_le one_pos hL1
  set Δ : ℝ := 1 / Lscale q T with hΔdef
  have hΔpos : 0 < Δ := by rw [hΔdef]; exact one_div_pos.mpr hLpos
  have hΔle1 : Δ ≤ 1 := by rw [hΔdef]; exact (div_le_one hLpos).mpr hL1
  set σL : ℝ := min σ (1 - Δ) with hσLdef
  have hσL0 : 0 ≤ σL := by rw [hσLdef]; apply le_min <;> linarith
  have hσLσ : σL ≤ σ := by rw [hσLdef]; exact min_le_left _ _
  have hΔleσL : Δ ≤ 1 - σL := by
    have h := min_le_right σ (1 - Δ); rw [← hσLdef] at h; linarith
  -- ## the logarithmic factor
  have hlog_le : Real.log ((q : ℝ) * (T + 1)) ≤ Lscale q T := by
    rw [Lscale, scale]
    apply Real.log_le_log (by positivity)
    nlinarith
  have hinner : (1 - σL) * Real.log ((q : ℝ) * (T + 1)) + 1
      ≤ 6 * ((1 - σ) * Lscale q T + 1) := by
    have honeσL : 1 - σL = max (1 - σ) Δ := by
      have key : ∀ a b : ℝ, 1 - min a b = max (1 - a) (1 - b) := by
        intro a b
        rcases le_total a b with hab | hab
        · rw [min_eq_left hab, max_eq_left (by linarith : 1 - b ≤ 1 - a)]
        · rw [min_eq_right hab, max_eq_right (by linarith : 1 - a ≤ 1 - b)]
      rw [hσLdef, key, show (1 : ℝ) - (1 - Δ) = Δ from by ring]
    have hle1 : (1 - σ) * Real.log ((q : ℝ) * (T + 1)) ≤ (1 - σ) * Lscale q T :=
      mul_le_mul_of_nonneg_left hlog_le (by linarith)
    have hle2 : Δ * Real.log ((q : ℝ) * (T + 1)) ≤ 1 := by
      have h' : Δ * Real.log ((q : ℝ) * (T + 1)) ≤ Δ * Lscale q T :=
        mul_le_mul_of_nonneg_left hlog_le hΔpos.le
      have h'' : Δ * Lscale q T = 1 := by rw [hΔdef]; field_simp
      linarith
    have hmax : (1 - σL) * Real.log ((q : ℝ) * (T + 1)) ≤ max ((1 - σ) * Lscale q T) 1 := by
      rw [honeσL]
      by_cases h : (1 - σ) ≤ Δ
      · rw [max_eq_right h]; exact le_trans hle2 (le_max_right _ _)
      · push Not at h; rw [max_eq_left h.le]; exact le_trans hle1 (le_max_left _ _)
    have hfin : max ((1 - σ) * Lscale q T) 1 + 1 ≤ 6 * ((1 - σ) * Lscale q T + 1) := by
      have h0 : 0 ≤ (1 - σ) * Lscale q T := mul_nonneg (by linarith) hLpos.le
      have : max ((1 - σ) * Lscale q T) 1 ≤ (1 - σ) * Lscale q T + 1 :=
        max_le (by linarith) (by linarith)
      linarith
    linarith
  set B : ℝ := 6 * Cbox * ((1 - σ) * Lscale q T + 1) with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]
    have h0 : (0 : ℝ) ≤ (1 - σ) * Lscale q T + 1 := by
      have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - σ) hLpos.le; linarith
    have h1 := hCboxpos.le; nlinarith
  -- ## the box decomposition
  set S : DirichletCharacter ℂ q → Finset ℂ :=
    fun χ => Set.Finite.toFinset (zeroSupport_finite χ σ T) with hSdef
  have hS : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ∀ ρ : ℂ,
      (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
        then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) ≠ 0 → ρ ∈ S χ := by
    intro χ _ ρ hρ
    rw [hSdef]
    exact (Set.Finite.mem_toFinset (hs := zeroSupport_finite χ σ T)).mpr
      (Function.mem_support.mpr hρ)
  have hSmem : ∀ (χ : DirichletCharacter ℂ q) (ρ : ℂ), ρ ∈ S χ →
      σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T ∧ Work.LinnikContract.zeroMult χ ρ ≠ 0 := by
    intro χ ρ h
    simp only [hSdef] at h
    rw [Set.Finite.mem_toFinset (zeroSupport_finite χ σ T)] at h
    rw [Function.mem_support] at h
    by_cases hc : σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
    · rw [if_pos hc] at h
      exact ⟨hc.1, hc.2.1, hc.2.2, fun h0 => h (by rw [h0]; norm_num)⟩
    · rw [if_neg hc] at h
      exact absurd rfl h
  have hbox : ∀ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ∀ k : ℤ,
      ∑ ρ ∈ (S χ).filter (fun ρ => boxIdx Δ ρ = k),
        (if σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T
          then (Work.LinnikContract.zeroMult χ ρ : ℝ) else 0) ≤ B := by
    intro χ hχ k
    have hχ1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    refine le_trans (sum_filter_boxIdx_le_boxMass χ σ T Δ (S χ) (hS χ hχ) k) ?_
    refine le_trans (hCbox q hq χ hχ1 σL σ T Δ hσL0 hσLσ hσ1 hT hΔpos hΔleσL k) ?_
    rw [hBdef]; nlinarith [hCboxpos, hinner]
  have hsplit := erase_zeroCountIn_le_two_mul_paritySplit σ T Δ B hB0 S hS hbox
  -- ## one zero per box of the larger parity class
  set Gp : Finset (DirichletCharacter ℂ q × ℤ) :=
    (Finset.univ.erase (1 : DirichletCharacter ℂ q)).biUnion
      (fun χ => (boxPar (S χ) Δ).image (fun k => (χ, k))) with hGpdef
  have hdisj : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)) :
        Set (DirichletCharacter ℂ q)).PairwiseDisjoint
      (fun χ => (boxPar (S χ) Δ).image (fun k => (χ, k))) := by
    intro χ _ χ' _ hne
    change Disjoint ((boxPar (S χ) Δ).image (fun k => (χ, k)))
      ((boxPar (S χ') Δ).image (fun k => (χ', k)))
    rw [Finset.disjoint_left]
    intro p hp hp'
    rw [Finset.mem_image] at hp hp'
    obtain ⟨k, _, hk⟩ := hp
    obtain ⟨k', _, hk'⟩ := hp'
    have h : (χ, k) = (χ', k') := by rw [hk, hk']
    exact hne (congrArg Prod.fst h)
  have hGp_mem : ∀ p ∈ Gp, p.1 ≠ 1 ∧ p.2 ∈ boxPar (S p.1) Δ := by
    intro p hp
    rw [hGpdef, Finset.mem_biUnion] at hp
    obtain ⟨χ, hχ, hp⟩ := hp
    rw [Finset.mem_image] at hp
    obtain ⟨k, hk, hpk⟩ := hp
    have h1 : p.1 = χ := by rw [← hpk]
    have h2 : p.2 = k := by rw [← hpk]
    exact ⟨by rw [h1]; exact (Finset.mem_erase.mp hχ).1, by rw [h1, h2]; exact hk⟩
  set selZero : DirichletCharacter ℂ q → ℤ → ℂ := fun χ k =>
    if h : ∃ ρ, ρ ∈ S χ ∧ boxIdx Δ ρ = k then Classical.choose h else 0 with hseldef
  have hsel_mem : ∀ χ k, (∃ ρ, ρ ∈ S χ ∧ boxIdx Δ ρ = k) → selZero χ k ∈ S χ := by
    intro χ k h; rw [hseldef]; dsimp only; rw [dif_pos h]; exact (Classical.choose_spec h).1
  have hsel_idx : ∀ χ k, (∃ ρ, ρ ∈ S χ ∧ boxIdx Δ ρ = k) → boxIdx Δ (selZero χ k) = k := by
    intro χ k h; rw [hseldef]; dsimp only; rw [dif_pos h]; exact (Classical.choose_spec h).2
  have hsel_exists : ∀ χ k, k ∈ boxPar (S χ) Δ → ∃ ρ, ρ ∈ S χ ∧ boxIdx Δ ρ = k := by
    intro χ k hk
    have hk' := boxPar_sub (S χ) Δ hk
    rw [Finset.mem_image] at hk'
    obtain ⟨ρ, hρ, hρk⟩ := hk'
    exact ⟨ρ, hρ, hρk⟩
  set Sel : Finset (DirichletCharacter ℂ q × ℂ) :=
    Gp.image (fun p => (p.1, selZero p.1 p.2)) with hSeldef
  have hf_inj : Set.InjOn (fun p : DirichletCharacter ℂ q × ℤ => (p.1, selZero p.1 p.2)) ↑Gp := by
    intro p hp p' hp' heq
    have hGp1 := hGp_mem p hp
    have hGp2 := hGp_mem p' hp'
    have h1 : p.1 = p'.1 := by simpa using congrArg Prod.fst heq
    have h2 : selZero p.1 p.2 = selZero p'.1 p'.2 := by simpa using congrArg Prod.snd heq
    have e1 := hsel_idx p.1 p.2 (hsel_exists p.1 p.2 hGp1.2)
    have e2 := hsel_idx p'.1 p'.2 (hsel_exists p'.1 p'.2 hGp2.2)
    have h3 : p.2 = p'.2 := by rw [← e1, ← e2, h2]
    exact Prod.ext h1 h3
  have hSel_spec : ∀ p ∈ Sel, ∃ χ : DirichletCharacter ℂ q, ∃ k : ℤ,
      χ ≠ 1 ∧ k ∈ boxPar (S χ) Δ ∧ p = (χ, selZero χ k) := by
    intro p hp
    rw [hSeldef, Finset.mem_image] at hp
    obtain ⟨p₀, hp₀, hp⟩ := hp
    rw [hGpdef, Finset.mem_biUnion] at hp₀
    obtain ⟨χ, hχ, hp₀⟩ := hp₀
    rw [Finset.mem_image] at hp₀
    obtain ⟨k, hk, hpk⟩ := hp₀
    refine ⟨χ, k, (Finset.mem_erase.mp hχ).1, hk, ?_⟩
    rw [← hp, ← hpk]
  have hSel_extract : ∀ p ∈ Sel, ∃ χ : DirichletCharacter ℂ q, ∃ k : ℤ,
      χ ≠ 1 ∧ p = (χ, selZero χ k) ∧ k ∈ boxPar (S χ) Δ ∧
      selZero χ k ∈ S χ ∧ boxIdx Δ (selZero χ k) = k := by
    intro p hp
    obtain ⟨χ, k, hχ, hk, hp⟩ := hSel_spec p hp
    exact ⟨χ, k, hχ, hp, hk, hsel_mem χ k (hsel_exists χ k hk),
      hsel_idx χ k (hsel_exists χ k hk)⟩
  have hSel_cond : ∀ p ∈ Sel, p.1 ≠ 1 ∧ σ ≤ p.2.re ∧ p.2.re ≤ 1 ∧ |p.2.im| ≤ T ∧
      Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 := by
    intro p hp
    obtain ⟨χ, k, hχ, hp, hk, hmem, -⟩ := hSel_extract p hp
    obtain ⟨h1, h2, h3, h4⟩ := hSmem χ (selZero χ k) hmem
    exact ⟨by rw [hp]; exact hχ, by rw [hp]; exact h1, by rw [hp]; exact h2,
      by rw [hp]; exact h3, by rw [hp]; exact h4⟩
  have hSel_re1 : ∀ p ∈ Sel, p.2.re < 1 := by
    intro p hp
    obtain ⟨h1, -, -, -, h5⟩ := hSel_cond p hp
    exact zeroMult_re_lt_one h1 h5
  have hSel_sep : ∀ p ∈ Sel, ∀ p' ∈ Sel, p ≠ p' → p.1 = p'.1 →
      1 / Lscale q T ≤ |p.2.im - p'.2.im| := by
    intro p hp p' hp' hne heq
    obtain ⟨χ, k, hχ, hp, hk, -, hidx⟩ := hSel_extract p hp
    obtain ⟨χ', k', hχ', hp', hk', -, hidx'⟩ := hSel_extract p' hp'
    have hχχ' : χ = χ' := by rw [hp] at heq; rw [hp'] at heq; exact heq
    rw [← hχχ'] at hk' hidx' hp'
    have hkne : k ≠ k' := by
      intro hkk; exact hne (by rw [hp, hp', hkk])
    rw [hp, hp', ← hΔdef]
    exact boxPar_sep (S χ) Δ hΔpos hk hk' hidx hidx' hkne
  -- ## `J ≤ M + Kob`
  set SelN : Finset (DirichletCharacter ℂ q × ℂ) :=
    Sel.filter (fun p => c₀ ≤ (1 - p.2.re) * Lscale q T) with hSelNdef
  set SelE : Finset (DirichletCharacter ℂ q × ℂ) :=
    Sel.filter (fun p => ¬ (c₀ ≤ (1 - p.2.re) * Lscale q T)) with hSelEdef
  have hSelN_le : (SelN.card : ℝ) ≤ M := by
    refine cardSystemLeM (L := Lscale q T) (S := SelN) hhyp ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro p hp; exact (hSel_cond p (Finset.mem_filter.mp hp).1).1
    · intro p hp; exact (hSel_cond p (Finset.mem_filter.mp hp).1).2.2.2.2
    · intro p hp; exact (hSel_cond p (Finset.mem_filter.mp hp).1).2.1
    · intro p hp; exact hSel_re1 p (Finset.mem_filter.mp hp).1
    · intro p hp; exact (hSel_cond p (Finset.mem_filter.mp hp).1).2.2.2.1
    · intro p hp; exact (Finset.mem_filter.mp hp).2
    · intro p hp p' hp' hne heq
      exact hSel_sep p (Finset.mem_filter.mp hp).1 p' (Finset.mem_filter.mp hp').1 hne heq
  have hSelE_le : (SelE.card : ℝ) ≤ (Kob : ℝ) := by
    have hk0 : ∀ p ∈ SelE, ∃ χ : DirichletCharacter ℂ q, ∃ k : ℤ,
        p = (χ, selZero χ k) ∧ k = 0 := by
      intro p hp
      have hpSel : p ∈ Sel := (Finset.mem_filter.mp hp).1
      have hlt : (1 - p.2.re) * Lscale q T < c₀ := not_le.mp (Finset.mem_filter.mp hp).2
      obtain ⟨χ, k, hχ, hp, hk, hmem, hidx⟩ := hSel_extract p hpSel
      obtain ⟨-, -, -, h4, h5⟩ := hSel_cond p hpSel
      have hlt' : (1 - (selZero χ k).re) * Lscale q T < cB := by
        rw [hp] at hlt; linarith [hlt, hc₀B]
      have h5' : Work.LinnikContract.zeroMult χ (selZero χ k) ≠ 0 := by
        rw [hp] at h5; exact h5
      have him0 : (selZero χ k).im = 0 :=
        (hcB q hq χ hχ (selZero χ k) T hT (by rw [hp] at h4; exact h4) h5' hlt').1
      have hbox0 : boxIdx Δ (selZero χ k) = 0 := by
        show ⌊(selZero χ k).im / Δ⌋ = 0
        rw [him0, zero_div]; simp
      exact ⟨χ, k, hp, by rw [← hidx]; exact hbox0⟩
    have hinj : Set.InjOn (fun p : DirichletCharacter ℂ q × ℂ => p.1) ↑SelE := by
      intro p hp p' hp' heq
      obtain ⟨χ, k, hp, hk⟩ := hk0 p hp
      obtain ⟨χ', k', hp', hk'⟩ := hk0 p' hp'
      have h1 : χ = χ' := by rw [hp, hp'] at heq; exact heq
      rw [hp, hp', h1, hk, hk']
    have himg : SelE.image Prod.fst ⊆
        (Finset.univ.erase (1 : DirichletCharacter ℂ q)).filter
          (fun χ => ∃ ρ : ℂ, Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ T ∧
            (1 - ρ.re) * Lscale q T < c₀) := by
      intro χ hχ
      rw [Finset.mem_image] at hχ
      obtain ⟨p, hp, rfl⟩ := hχ
      obtain ⟨h1, -, -, h4, h5⟩ := hSel_cond p (Finset.mem_filter.mp hp).1
      have hlt : (1 - p.2.re) * Lscale q T < c₀ := not_le.mp (Finset.mem_filter.mp hp).2
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_erase.mpr ⟨h1, Finset.mem_univ _⟩, p.2, h5, h4, hlt⟩
    have hmono : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).filter
          (fun χ => ∃ ρ : ℂ, Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ T ∧
            (1 - ρ.re) * Lscale q T < c₀)).card
        ≤ ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).filter
          (fun χ => ∃ ρ : ℂ, Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ T ∧
            (1 - ρ.re) * Lscale q T < cE)).card :=
      Finset.card_le_card (fun χ hχ => by
        rw [Finset.mem_filter] at hχ ⊢
        exact ⟨hχ.1, hχ.2.imp (fun ρ hρ => ⟨hρ.1, hρ.2.1, lt_of_lt_of_le hρ.2.2 hc₀E⟩)⟩)
    have hcard2 : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).filter
          (fun χ => ∃ ρ : ℂ, Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ T ∧
            (1 - ρ.re) * Lscale q T < c₀)).card ≤ Kob := by
      by_cases hq9 : qE ≤ q
      · have hc1 : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).filter
            (fun χ => ∃ ρ : ℂ, Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ T ∧
              (1 - ρ.re) * Lscale q T < cE)).card ≤ 1 :=
          Finset.card_le_one.mpr (by
            intro a ha b hb
            rw [Finset.mem_filter] at ha hb
            by_contra hab
            exact (hcE q hq9 T hT a b (Finset.mem_erase.mp ha.1).1
              (Finset.mem_erase.mp hb.1).1 hab ⟨ha.2, hb.2⟩).elim)
        have hK1 : 1 ≤ Kob := by rw [hKobdef]; exact le_max_right _ _
        omega
      · have hc1 : ((Finset.univ.erase (1 : DirichletCharacter ℂ q)).filter
            (fun χ => ∃ ρ : ℂ, Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ T ∧
              (1 - ρ.re) * Lscale q T < c₀)).card
            ≤ (Finset.univ : Finset (DirichletCharacter ℂ q)).card :=
          le_trans (Finset.card_le_card (Finset.filter_subset _ _))
            (Finset.card_le_card (Finset.erase_subset _ _))
        have hcardu : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
          rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
          exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
        have h3 : q.totient ≤ q := Nat.totient_le q
        have h4 : q < qE := not_le.mp hq9
        have h5 : qE ≤ Kob := by rw [hKobdef]; exact le_max_left _ _
        omega
    calc (SelE.card : ℝ) = ((SelE.image Prod.fst).card : ℝ) := by
          rw [Finset.card_image_iff.mpr hinj]
      _ ≤ (((Finset.univ.erase (1 : DirichletCharacter ℂ q)).filter
            (fun χ => ∃ ρ : ℂ, Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ |ρ.im| ≤ T ∧
              (1 - ρ.re) * Lscale q T < c₀)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card himg
      _ ≤ (Kob : ℝ) := by exact_mod_cast hcard2
  have hcard_split : Sel.card = SelN.card + SelE.card :=
    (Finset.card_filter_add_card_filter_not (s := Sel)
      (p := fun p => c₀ ≤ (1 - p.2.re) * Lscale q T)).symm
  have hcardSel : (Sel.card : ℝ) = ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
      ((max (boxEven (S χ) Δ).card (boxOdd (S χ) Δ).card : ℕ) : ℝ) := by
    rw [hSeldef, Finset.card_image_iff.mpr hf_inj, hGpdef, Finset.card_biUnion hdisj,
      Nat.cast_sum]
    refine Finset.sum_congr rfl (fun χ _ => ?_)
    rw [Finset.card_image_of_injective _ (fun a b hab => congrArg Prod.snd hab), boxPar_card]
  have hJbound : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
        ((max (boxEven (S χ) Δ).card (boxOdd (S χ) Δ).card : ℕ) : ℝ)) ≤ M + (Kob : ℝ) := by
    rw [← hcardSel]
    have hcs : (Sel.card : ℝ) = (SelN.card : ℝ) + (SelE.card : ℝ) := by
      rw [hcard_split]; push_cast; ring
    rw [hcs]
    linarith [hSelN_le, hSelE_le]
  -- ## assembly
  calc famCountNP q σ T
      = ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          Work.LinnikAreas.zeroCountIn χ σ T := by
          simp only [famCountNP, Work.ZeroDensity.zCount]
    _ ≤ 2 * B * ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          ((max (boxEven (S χ) Δ).card (boxOdd (S χ) Δ).card : ℕ) : ℝ) := by
          simpa only [boxEven, boxOdd] using hsplit
    _ ≤ 2 * B * (M + (Kob : ℝ)) := mul_le_mul_of_nonneg_left hJbound (by linarith [hB0])
    _ ≤ 12 * Cbox * ((Kob : ℝ) + 1) * ((1 + (1 - σ) * Lscale q T) * (M + 1) + 1) := by
          rw [hBdef]
          have hKob0 : (0 : ℝ) ≤ (Kob : ℝ) := Nat.cast_nonneg _
          have h4 : (0 : ℝ) ≤ (1 - σ) * Lscale q T + 1 := by
            have := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - σ) hLpos.le; linarith
          have h2 : M + (Kob : ℝ) ≤ ((Kob : ℝ) + 1) * (M + 1) := by nlinarith [hM, hKob0]
          have h3 : (0 : ℝ) ≤ 2 * (6 * Cbox * ((1 - σ) * Lscale q T + 1)) := by
            rw [← hBdef]; linarith [hB0]
          calc 2 * (6 * Cbox * ((1 - σ) * Lscale q T + 1)) * (M + (Kob : ℝ))
              ≤ 2 * (6 * Cbox * ((1 - σ) * Lscale q T + 1)) * (((Kob : ℝ) + 1) * (M + 1)) :=
                mul_le_mul_of_nonneg_left h2 h3
            _ = 12 * Cbox * ((Kob : ℝ) + 1) * (((1 - σ) * Lscale q T + 1) * (M + 1)) := by ring
            _ ≤ 12 * Cbox * ((Kob : ℝ) + 1) * ((1 + (1 - σ) * Lscale q T) * (M + 1) + 1) := by
                have h5 : (0 : ℝ) ≤ 12 * Cbox * ((Kob : ℝ) + 1) := by
                  apply mul_nonneg
                  · exact mul_nonneg (by norm_num) hCboxpos.le
                  · positivity
                have h6 : ((1 - σ) * Lscale q T + 1) * (M + 1)
                    ≤ (1 + (1 - σ) * Lscale q T) * (M + 1) + 1 := by nlinarith
                exact mul_le_mul_of_nonneg_left h6 h5

end Work.ZeroDensity.LogFree
