import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.ZeroDensity.Defs
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Work.ZeroFreeTables.OffAxis.rpow_height_bound
import Submission.Work.ZeroFreeTables.OffAxis.card_le_famCount

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables.OffAxis

/-- The windows `(50·10^k, 500·10^k]` are increasing: for `k < j` the `k`-th window lies
strictly below the `j`-th one. -/
lemma pow_strip_le {k j : ℕ} (h : k < j) :
    (500 : ℝ) * 10 ^ k ≤ (50 : ℝ) * 10 ^ j := by
  have h1 : (10 : ℝ) ^ (k + 1) ≤ (10 : ℝ) ^ j :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 : (500 : ℝ) * 10 ^ k = (50 : ℝ) * (10 : ℝ) ^ (k + 1) := by
    rw [pow_succ]; ring
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 (by norm_num)

theorem exists_stripFree_height (hJ : Work.ZeroDensity.FamDensityEpsRange (4/5) 1 2) :
    ∃ M : ℕ, ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ [NeZero q], ∃ k : ℕ, k ≤ M ∧
      ∀ (χ : DirichletCharacter ℂ q) (u : ℂ),
        Work.ZeroFreeTables.IsZAt (10 * ((50 : ℝ) * 10 ^ k)) χ u →
        (50 : ℝ) * 10 ^ k < |u.im| → 2 < Work.LinnikContract.lamOf q u := by
  classical
  obtain ⟨C, hCpos, hC⟩ := hJ 1 (by norm_num)
  -- the number of windows and the total height
  set M : ℕ := ⌈C * Real.exp 7⌉₊ with hMdef
  have hMge : C * Real.exp 7 ≤ (M : ℝ) := Nat.le_ceil _
  set T : ℝ := 500 * (10 : ℝ) ^ M with hTdef
  have hT1 : 1 ≤ T := by
    rw [hTdef]
    have h := one_le_pow₀ (show (1 : ℝ) ≤ 10 by norm_num) (n := M)
    nlinarith
  -- the threshold on `log q`
  refine ⟨M, max 2 (⌈Real.exp (max 10 (6 * Real.log T + 100))⌉₊ + 1), ?_⟩
  intro q hq hqne
  have hq2 : 2 ≤ q := le_trans (le_max_left _ _) hq
  have hq1n : 1 < q := by omega
  have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast hq1n
  have hlogq : 0 < Real.log (q : ℝ) := Real.log_pos hq1
  have hthr : Real.exp (max 10 (6 * Real.log T + 100)) < (q : ℝ) := by
    have h1 : ⌈Real.exp (max 10 (6 * Real.log T + 100))⌉₊ + 1 ≤ q :=
      le_trans (le_max_right _ _) hq
    have h2 : Real.exp (max 10 (6 * Real.log T + 100)) <
        ((⌈Real.exp (max 10 (6 * Real.log T + 100))⌉₊ : ℕ) : ℝ) + 1 := by
      have := Nat.le_ceil (Real.exp (max 10 (6 * Real.log T + 100)))
      linarith
    have h3 : (((⌈Real.exp (max 10 (6 * Real.log T + 100))⌉₊ : ℕ) : ℝ) + 1) ≤ (q : ℝ) := by
      exact_mod_cast h1
    linarith
  have hlogthr : max 10 (6 * Real.log T + 100) < Real.log (q : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos (max 10 (6 * Real.log T + 100))) hthr
    rwa [Real.log_exp] at h
  have hlogT : 6 * Real.log T ≤ Real.log (q : ℝ) :=
    le_of_lt (lt_of_le_of_lt (by linarith [le_max_right (10 : ℝ) (6 * Real.log T + 100)]) hlogthr)
  have hlog10 : 10 ≤ Real.log (q : ℝ) :=
    le_of_lt (lt_of_le_of_lt (le_max_left (10 : ℝ) (6 * Real.log T + 100)) hlogthr)
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
  set σ : ℝ := 1 - 2 / Real.log (q : ℝ) with hσdef
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
  -- every witness is counted by the family zero count at `(σ, T)`
  have hSgood : ∀ ρ ∈ S, ∃ χ : DirichletCharacter ℂ q,
      Work.LinnikContract.zeroMult χ ρ ≠ 0 ∧ σ ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ T := by
    intro ρ hρ
    rw [hSdef, Finset.mem_image] at hρ
    obtain ⟨k, hk, hkρ⟩ := hρ
    subst hkρ
    simp only [Finset.mem_range] at hk
    have hkM : k ≤ M := by omega
    obtain ⟨hZ, him, hlam⟩ := hbad k hkM
    refine ⟨χf k, hZ.2.1, ?_, le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one (χf k) hZ.2.1), ?_⟩
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
  have hcount := card_le_famCount σ T S hSgood
  -- the density estimate at `σ = 1 - 2/log q`, height `T`
  have hσlo : (4 : ℝ) / 5 ≤ σ := by
    rw [hσdef]
    have h2 : 2 / Real.log (q : ℝ) ≤ 1 / 5 := by
      rw [div_le_iff₀ hlogq]
      linarith
    linarith
  have hσhi : σ ≤ 1 := by
    rw [hσdef]
    have h2 : 0 ≤ 2 / Real.log (q : ℝ) := by positivity
    linarith
  have hfam := hC q hq2 σ T hσlo hσhi hT1
  have h1σ : 1 - σ = 2 / Real.log (q : ℝ) := by rw [hσdef]; ring
  have hexp : (2 + 1) * (1 - σ) = 6 / Real.log (q : ℝ) := by rw [h1σ]; ring
  have hrpow : ((q : ℝ) * T) ^ ((2 + 1) * (1 - σ)) ≤ Real.exp 7 := by
    rw [hexp]
    exact rpow_height_bound hq1n hT1 hlogT
  have hbound : Work.ZeroDensity.famCount q σ T ≤ C * Real.exp 7 :=
    le_trans hfam (mul_le_mul_of_nonneg_left hrpow hCpos.le)
  have h1 : (S.card : ℝ) ≤ C * Real.exp 7 := le_trans hcount hbound
  rw [hScard] at h1
  push_cast at h1
  linarith

end Work.ZeroFreeTables.OffAxis
