/-
# ZeroFreeTables/OffAxis/exists_stripFree_height_of_logFreeNP

**OA4 with the unified log-free non-principal density input.**  The sibling file
`OffAxis/exists_stripFree_height.lean` derives the strip-free scale from Jutila's *family* estimate
`FamDensityEpsRange (4/5) 1 2` (all characters, including the principal one).  Here the input is the
*non-principal* unified estimate `Work.ZeroDensity.LogFree.logFreeNP σ₀ c` of
`ZeroDensity/JUTILA_UNIFIED_LEAD.md` §3, and the only two changes are:

* the family count `famCount` is replaced by its non-principal variant `famCountNP` — which is
  legitimate because every zero produced by the `IsZAt`-witnesses is *non-principal* (`IsZAt`
  carries the conjunct `χ ≠ 1`);
* the exponent is the general `c (1-σ)` in place of `(2+ε)(1-σ)`: at the single point
  `σ = 1 - 2/log q` the density bound is `(qT)^{2c/log q} ≤ e^{7c/3}` (rather than `e^7`) once
  `6 log T ≤ log q`, so the number of windows is `M = ⌈C e^{7c/3}⌉`.

Since `σ` is pinned to `1 - 2/log q` (which tends to `1`), the hypothesis `σ₀ < 1` of `logFreeNP`
suffices: it only forces the threshold `log q ≥ 2/(1-σ₀)`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroDensity.LogFree.Defs
import Submission.Work.ZeroFreeTables.OffAxis.exists_stripFree_height
import Submission.Work.ZeroFreeTables.OffAxis.card_le_famCount
import Submission.Work.ZeroFreeTables.OffAxis.rpow_height_bound

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

/-! ## 1. The height bound with a general exponent -/

/-- Height bound used in the zero-free region argument, with a general exponent `c > 0`: if the
logarithm of the modulus `q` dominates `6 log T`, then `(q*T)^{2c/log q} ≤ exp (7c/3)`.

This is `rpow_height_bound` (`c = 3`) with the `6`-power replaced by `2c`: writing
`a = 2c / log q`, the exponent in `(q*T)^a = exp(a · log(q*T))` splits as
`a·log q + a·log T = 2c + 2c·log T/log q ≤ 2c + c/3 = 7c/3`. -/
theorem rpow_height_bound_gen {q : ℕ} {T c : ℝ} (hq : 1 < q) (hT : 1 ≤ T) (hc : 0 < c)
    (hlog : 6 * Real.log T ≤ Real.log (q : ℝ)) :
    ((q : ℝ) * T) ^ (2 * c / Real.log (q : ℝ)) ≤ Real.exp (7 * c / 3) := by
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < (q : ℝ) := lt_trans zero_lt_one hq1
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hTpos : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hbase_pos : 0 < (q : ℝ) * T := mul_pos hqpos hTpos
  have hkey : (Real.log (q : ℝ) + Real.log T) * (2 * c / Real.log (q : ℝ)) ≤ 7 * c / 3 := by
    rw [← mul_div_assoc, div_le_iff₀ hlogq_pos]
    have hprod : 0 ≤ (c / 3) * (Real.log (q : ℝ) - 6 * Real.log T) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith [hprod]
  rw [Real.rpow_def_of_pos hbase_pos, Real.log_mul (ne_of_gt hqpos) (ne_of_gt hTpos)]
  exact Real.exp_le_exp.mpr hkey

/-! ## 2. The non-principal card bound -/

/-- `card_le_famCount` with the family sum restricted to the *non-principal* characters: a finite
set of zeros whose witnesses `χ` are all non-principal is counted by
`Σ'_{χ ≠ 1} N(σ,T,χ) = famCountNP q σ T`.

The proof is that of `card_le_famCount`, with each occurrence of `Finset.univ` replaced by
`Finset.univ.erase 1`; the extra hypothesis `χ ≠ 1` places the witness inside the erased set. -/
theorem card_le_famCountNP {q : ℕ} [NeZero q] (σ T : ℝ) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, ∃ χ : DirichletCharacter ℂ q,
      χ ≠ 1 ∧ Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T) :
    (S.card : ℝ) ≤ Work.ZeroDensity.LogFree.famCountNP q σ T := by
  classical
  let g : DirichletCharacter ℂ q → ℂ → ℝ :=
    fun χ u => if σ ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ T
      then (Work.LinnikContract.zeroMult χ u : ℝ) else 0
  have hg_nonneg : ∀ χ u, 0 ≤ g χ u := by
    intro χ u
    simp only [g]
    split_ifs <;> simp
  have hg_supp : ∀ χ, Function.HasFiniteSupport (g χ) := by
    intro χ
    refine (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ σ T).subset ?_
    intro u hu
    simp only [Function.mem_support, g] at hu
    have hc : σ ≤ u.re ∧ u.re ≤ 1 ∧ |u.im| ≤ T := by
      by_contra hcon
      exact hu (if_neg hcon)
    have hzm : Work.LinnikContract.zeroMult χ u ≠ 0 := by
      have hz : (Work.LinnikContract.zeroMult χ u : ℝ) ≠ 0 := by
        rwa [if_pos hc] at hu
      exact_mod_cast hz
    exact ⟨hzm, hc.1, hc.2.1, hc.2.2⟩
  have hP1 : ∀ χ : DirichletCharacter ℂ q, ∑ u ∈ S, g χ u ≤ ∑ᶠ u, g χ u :=
    fun χ => finset_sum_le_finsum_of_nonneg (hg_nonneg χ) (hg_supp χ) S
  have hP2 : ∀ u ∈ S,
      (1 : ℝ) ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), g χ u := by
    intro u hu
    obtain ⟨χ, hχ1, hzm, hσ, hre, him⟩ := hS u hu
    have hval : g χ u = (Work.LinnikContract.zeroMult χ u : ℝ) := by
      simp only [g]
      rw [if_pos ⟨hσ, hre, him⟩]
    have hge1 : (1 : ℝ) ≤ g χ u := by
      rw [hval]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr hzm
    have hmem : χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q) :=
      Finset.mem_erase.mpr ⟨hχ1, Finset.mem_univ χ⟩
    exact hge1.trans (Finset.single_le_sum (fun i _ => hg_nonneg i u) hmem)
  have hmain : (S.card : ℝ) ≤
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ∑ᶠ u, g χ u := by
    calc (S.card : ℝ) = ∑ u ∈ S, (1 : ℝ) := by simp
      _ ≤ ∑ u ∈ S, ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), g χ u :=
          Finset.sum_le_sum hP2
      _ = ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ∑ u ∈ S, g χ u :=
          Finset.sum_comm
      _ ≤ ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), ∑ᶠ u, g χ u :=
          Finset.sum_le_sum (fun χ _ => hP1 χ)
  simpa only [g, Work.ZeroDensity.LogFree.famCountNP, Work.ZeroDensity.zCount,
    Work.LinnikAreas.zeroCountIn] using hmain

/-! ## 3. The strip-free height from the non-principal log-free estimate -/

theorem exists_stripFree_height_of_logFreeNP {σ₀ c : ℝ} (hσ0 : σ₀ < 1) (hc : 0 < c)
    (h : Work.ZeroDensity.LogFree.logFreeNP σ₀ c) :
    ∃ M : ℕ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q], ∃ k : ℕ, k ≤ M ∧
      ∀ (χ : DirichletCharacter ℂ q) (u : ℂ),
        Work.ZeroFreeTables.IsZAt (10 * ((50 : ℝ) * 10 ^ k)) χ u →
        (50 : ℝ) * 10 ^ k < |u.im| → 2 < Work.LinnikContract.lamOf q u := by
  classical
  obtain ⟨C, hCpos, hC⟩ := h
  have hden : 0 < 1 - σ₀ := by linarith
  -- the number of windows and the total height
  set M : ℕ := ⌈C * Real.exp (7 * c / 3)⌉₊ with hMdef
  have hMge : C * Real.exp (7 * c / 3) ≤ (M : ℝ) := Nat.le_ceil _
  set T : ℝ := 500 * (10 : ℝ) ^ M with hTdef
  have hT1 : 1 ≤ T := by
    rw [hTdef]
    have h := one_le_pow₀ (show (1 : ℝ) ≤ 10 by norm_num) (n := M)
    nlinarith
  -- the threshold on `log q`: `log q ≥ 10`, `log q ≥ 2/(1-σ₀)`, `6 log T ≤ log q`
  refine ⟨M, max 2 (⌈Real.exp (max 10 (max (2 / (1 - σ₀)) (6 * Real.log T + 100)))⌉₊ + 1), ?_⟩
  intro q hq hqne
  have hq2 : 2 ≤ q := le_trans (le_max_left _ _) hq
  have hq1n : 1 < q := by omega
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq1n
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  set B : ℝ := max 10 (max (2 / (1 - σ₀)) (6 * Real.log T + 100)) with hBdef
  have hthr : Real.exp B < (q : ℝ) := by
    have h1 : ⌈Real.exp B⌉₊ + 1 ≤ q := le_trans (le_max_right _ _) hq
    have h2 : Real.exp B < ((⌈Real.exp B⌉₊ : ℕ) : ℝ) + 1 := by
      have := Nat.le_ceil (Real.exp B)
      linarith
    have h3 : (((⌈Real.exp B⌉₊ : ℕ) : ℝ) + 1) ≤ (q : ℝ) := by
      exact_mod_cast h1
    linarith
  have hlogthr : B < Real.log (q : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos B) hthr
    rwa [Real.log_exp] at h
  have hlogT : 6 * Real.log T ≤ Real.log (q : ℝ) := by
    have h1 : 6 * Real.log T + 100 ≤ B :=
      (le_max_right (2 / (1 - σ₀)) (6 * Real.log T + 100)).trans (le_max_right 10 _)
    linarith
  have hlogσ : 2 / (1 - σ₀) ≤ Real.log (q : ℝ) := by
    have h1 : 2 / (1 - σ₀) ≤ B :=
      (le_max_left (2 / (1 - σ₀)) (6 * Real.log T + 100)).trans (le_max_right 10 _)
    linarith
  set σ : ℝ := 1 - 2 / Real.log (q : ℝ) with hσdef
  have hσle1 : σ ≤ 1 := by
    rw [hσdef]
    have h2 : 0 ≤ 2 / Real.log (q : ℝ) := by positivity
    linarith
  have hσge : σ₀ ≤ σ := by
    rw [hσdef]
    have h2 : 2 ≤ Real.log (q : ℝ) * (1 - σ₀) := (div_le_iff₀ hden).mp hlogσ
    have h3 : 2 / Real.log (q : ℝ) ≤ 1 - σ₀ := by
      rw [div_le_iff₀ hlogq]
      linarith
    linarith
  by_contra hcon
  push Not at hcon
  have hcon' : ∀ k : ℕ, ∃ p : DirichletCharacter ℂ q × ℂ,
      k ≤ M → IsZAt (10 * ((50 : ℝ) * 10 ^ k)) p.1 p.2 ∧
        (50 : ℝ) * 10 ^ k < |p.2.im| ∧ Work.LinnikContract.lamOf q p.2 ≤ 2 := by
    intro k
    by_cases hk : k ≤ M
    · obtain ⟨χ, u, h1, h2, h3⟩ := hcon k hk
      exact ⟨(χ, u), fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨(1, 0), fun hk' => absurd hk' hk⟩
  let pt : ℕ → DirichletCharacter ℂ q × ℂ := fun k => Classical.choose (hcon' k)
  have hpt : ∀ k : ℕ, k ≤ M →
      IsZAt (10 * ((50 : ℝ) * 10 ^ k)) (pt k).1 (pt k).2 ∧
        (50 : ℝ) * 10 ^ k < |(pt k).2.im| ∧ Work.LinnikContract.lamOf q (pt k).2 ≤ 2 :=
    fun k hk => Classical.choose_spec (hcon' k) hk
  let χf : ℕ → DirichletCharacter ℂ q := fun k => (pt k).1
  let uf : ℕ → ℂ := fun k => (pt k).2
  have hbad : ∀ k : ℕ, k ≤ M →
      IsZAt (10 * ((50 : ℝ) * 10 ^ k)) (χf k) (uf k) ∧
        (50 : ℝ) * 10 ^ k < |(uf k).im| ∧ Work.LinnikContract.lamOf q (uf k) ≤ 2 :=
    fun k hk => hpt k hk
  -- the window witness zeros are pairwise distinct
  have hSinj : Set.InjOn uf ((Finset.range (M + 1) : Finset ℕ) : Set ℕ) := by
    intro k hk j hj hkj
    simp only [Finset.mem_coe, Finset.mem_range] at hk hj
    rcases lt_trichotomy k j with hlt | heq | hgt
    · exfalso
      have hkM : k ≤ M := by omega
      have hjM : j ≤ M := by omega
      have himk : |(uf k).im| ≤ (500 : ℝ) * 10 ^ k := by
        have h := (hbad k hkM).1.2.2
        have h' : 10 * ((50 : ℝ) * 10 ^ k) = (500 : ℝ) * 10 ^ k := by ring
        linarith
      have himj : (50 : ℝ) * 10 ^ j < |(uf j).im| := (hbad j hjM).2.1
      have hle : (500 : ℝ) * 10 ^ k ≤ (50 : ℝ) * 10 ^ j := pow_strip_le hlt
      have him : |(uf j).im| = |(uf k).im| := by rw [← hkj]
      linarith
    · exact heq
    · exfalso
      have hkM : k ≤ M := by omega
      have hjM : j ≤ M := by omega
      have himj : |(uf j).im| ≤ (500 : ℝ) * 10 ^ j := by
        have h := (hbad j hjM).1.2.2
        have h' : 10 * ((50 : ℝ) * 10 ^ j) = (500 : ℝ) * 10 ^ j := by ring
        linarith
      have himk : (50 : ℝ) * 10 ^ k < |(uf k).im| := (hbad k hkM).2.1
      have hle : (500 : ℝ) * 10 ^ j ≤ (50 : ℝ) * 10 ^ k := pow_strip_le hgt
      have him : |(uf j).im| = |(uf k).im| := by rw [← hkj]
      linarith
  set S : Finset ℂ := (Finset.range (M + 1)).image uf with hSdef
  have hScard : S.card = M + 1 := by
    rw [hSdef, Finset.card_image_of_injOn hSinj, Finset.card_range]
  -- every witness is counted by the non-principal zero count at `(σ, T)`
  have hSgood : ∀ ρ ∈ S, ∃ χ : DirichletCharacter ℂ q,
      χ ≠ 1 ∧ Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T := by
    intro ρ hρ
    rw [hSdef, Finset.mem_image] at hρ
    obtain ⟨k, hk, hkρ⟩ := hρ
    subst hkρ
    simp only [Finset.mem_range] at hk
    have hkM : k ≤ M := by omega
    obtain ⟨hZ, him, hlam⟩ := hbad k hkM
    refine ⟨χf k, hZ.1, hZ.2.1, ?_,
      le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one (χf k) hZ.2.1), ?_⟩
    · rw [hσdef]
      have h1 : (1 - (uf k).re) * Real.log (q : ℝ) ≤ 2 := by
        simpa [Work.LinnikContract.lamOf] using hlam
      have h2 : 1 - (uf k).re ≤ 2 / Real.log (q : ℝ) := (le_div_iff₀ hlogq).mpr h1
      linarith
    · rw [hTdef]
      have h1 : |(uf k).im| ≤ 10 * ((50 : ℝ) * 10 ^ k) := hZ.2.2
      have h2 : 10 * ((50 : ℝ) * 10 ^ k) = (500 : ℝ) * 10 ^ k := by ring
      have h3 : (10 : ℝ) ^ k ≤ (10 : ℝ) ^ M := pow_le_pow_right₀ (by norm_num) hkM
      have h4 : (500 : ℝ) * 10 ^ k ≤ 500 * (10 : ℝ) ^ M :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)
      linarith
  have hcount := card_le_famCountNP σ T S hSgood
  -- the density estimate at `σ = 1 - 2/log q`, height `T`
  have hfam := hC q hq2 σ T hσge hσle1 hT1
  have h1σ : 1 - σ = 2 / Real.log (q : ℝ) := by rw [hσdef]; ring
  have hexp : c * (1 - σ) = 2 * c / Real.log (q : ℝ) := by rw [h1σ]; ring
  have hrpow : ((q : ℝ) * T) ^ (c * (1 - σ)) ≤ Real.exp (7 * c / 3) := by
    rw [hexp]
    exact rpow_height_bound_gen hq1n hT1 hc hlogT
  have hbound : Work.ZeroDensity.LogFree.famCountNP q σ T ≤ C * Real.exp (7 * c / 3) :=
    le_trans hfam (mul_le_mul_of_nonneg_left hrpow hCpos.le)
  have h1 : (S.card : ℝ) ≤ C * Real.exp (7 * c / 3) := le_trans hcount hbound
  rw [hScard] at h1
  push_cast at h1
  linarith

end Work.ZeroFreeTables.OffAxis
