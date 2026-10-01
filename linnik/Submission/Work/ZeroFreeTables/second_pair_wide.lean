import Mathlib
import Submission.Work.LinnikContract.Defs
import Submission.Work.ZeroFreeTables.Defs
import Submission.Work.ZeroFreeTables.HBTable7_defs2
import Submission.Work.ZeroFreeTables.exists_min_other_wide

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- Arithmetic helper: for any `Q₀ K : ℕ` there is `Q ≥ Q₀`, `Q ≥ 2` with
`2 ^ (K+1) - 1 ≤ 10 * log Q` (log is unbounded). -/
theorem exists_Q_log_ge (Q₀ K : ℕ) :
    ∃ Q : ℕ, Q₀ ≤ Q ∧ 2 ≤ Q ∧ (2 : ℝ) ^ (K + 1) - 1 ≤ 10 * Real.log (Q : ℝ) := by
  set r : ℝ := ((2 : ℝ) ^ (K + 1) - 1) / 10 with hr
  obtain ⟨n, hn⟩ := exists_nat_gt (Real.exp r)
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_trans (Real.exp_pos r) hn
  have hlog : r ≤ Real.log (n : ℝ) := by
    have h := Real.log_lt_log (Real.exp_pos r) hn
    rw [Real.log_exp] at h
    linarith
  refine ⟨max Q₀ (max 2 n), le_max_left _ _, ?_, ?_⟩
  · exact le_trans (le_max_left 2 n) (le_max_right Q₀ (max 2 n))
  · have hQn : (n : ℝ) ≤ ((max Q₀ (max 2 n) : ℕ) : ℝ) := by
      have h : n ≤ max Q₀ (max 2 n) := le_trans (le_max_right 2 n) (le_max_right Q₀ _)
      exact_mod_cast h
    have hlogQ : Real.log (n : ℝ) ≤ Real.log ((max Q₀ (max 2 n) : ℕ) : ℝ) :=
      Real.log_le_log hnpos hQn
    have hfin : r ≤ Real.log (((max Q₀ (max 2 n) : ℕ) : ℝ)) := le_trans hlog hlogQ
    have hr10 : 10 * r = (2 : ℝ) ^ (K + 1) - 1 := by rw [hr]; ring
    calc (2 : ℝ) ^ (K + 1) - 1 = 10 * r := hr10.symm
      _ ≤ 10 * Real.log (((max Q₀ (max 2 n) : ℕ) : ℝ)) := by linarith

/-- If `S` is a finite set of pairs `(χ, ρ)` with `χ ∉ {1, χ₁, χ₁⁻¹}`, `ρ` a zero of `χ`,
`|ρ.im| ≤ H` and `λ(ρ) ≤ Λ`, then `S.card ≤ otherLamCount χ₁ Λ H`. -/
theorem otherLamCount_ge_card {q : ℕ} [NeZero q] (χ₁ : DirichletCharacter ℂ q) (Λ H : ℝ)
    (S : Finset (DirichletCharacter ℂ q × ℂ))
    (hS : ∀ p ∈ S, p.1 ≠ 1 ∧ p.1 ≠ χ₁ ∧ p.1 ≠ χ₁⁻¹ ∧
      Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧ |p.2.im| ≤ H ∧
      Work.LinnikContract.lamOf q p.2 ≤ Λ) :
    (S.card : ℝ) ≤ Work.ZeroFreeTables.otherLamCount χ₁ Λ H := by
  classical
  let F : DirichletCharacter ℂ q × ℂ → ℝ := fun p =>
    if p.1 ≠ 1 ∧ p.1 ≠ χ₁ ∧ p.1 ≠ χ₁⁻¹ ∧ Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧
        |p.2.im| ≤ H ∧ Work.LinnikContract.lamOf q p.2 ≤ Λ
    then (Work.LinnikContract.zeroMult p.1 p.2 : ℝ) else 0
  have hOther : Work.ZeroFreeTables.otherLamCount χ₁ Λ H = ∑ᶠ p, F p := rfl
  let T : Finset (DirichletCharacter ℂ q × ℂ) :=
    Finset.univ.biUnion (fun χ : DirichletCharacter ℂ q =>
      ((Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box χ (1 - Λ / Real.log (q:ℝ)) H).toFinset).image
        (fun z : ℂ => (χ, z)))
  have hsup : Function.support F ⊆ ↑T := by
    intro p hp
    rw [Function.mem_support] at hp
    have hcond : p.1 ≠ 1 ∧ p.1 ≠ χ₁ ∧ p.1 ≠ χ₁⁻¹ ∧ Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧
        |p.2.im| ≤ H ∧ Work.LinnikContract.lamOf q p.2 ≤ Λ := by
      by_contra hcon
      exact hp (by simp only [F]; rw [if_neg hcon])
    obtain ⟨hχ1, hχχ₁, hχχ₁', hzm, him, hlam⟩ := hcond
    have hqne : q ≠ 1 := by
      rintro rfl
      exact hχ1 (Subsingleton.elim p.1 1)
    have hlogpos : 0 < Real.log (q:ℝ) := by
      have h0 : q ≠ 0 := NeZero.ne q
      refine Real.log_pos ?_
      exact_mod_cast (show 1 < q by omega)
    have haz : 1 - Λ / Real.log (q:ℝ) ≤ p.2.re := by
      have hst : (1 - p.2.re) * Real.log (q:ℝ) ≤ Λ := by
        simpa [Work.LinnikContract.lamOf] using hlam
      have hdiv : 1 - p.2.re ≤ Λ / Real.log (q:ℝ) := by
        rw [le_div_iff₀ hlogpos]; exact hst
      linarith
    have hzbox : p.2 ∈ (Work.LinnikAreas.boxMaxZeroAux.finite_zeroMult_box p.1 (1 - Λ / Real.log (q:ℝ)) H).toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact ⟨hzm, haz, le_of_lt (Work.LinnikAreas.boxMaxZeroAux.zeroMult_re_lt_one p.1 hzm), him⟩
    rw [Finset.mem_coe]
    exact Finset.mem_biUnion.mpr ⟨p.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨p.2, hzbox, rfl⟩⟩
  rw [hOther, finsum_eq_finsetSum_of_support_subset F hsup]
  have hsub : S ⊆ T := by
    intro p hp
    have hp' : p ∈ Function.support F := by
      rw [Function.mem_support]
      obtain ⟨h1,h2,h3,hzm,him,hlam⟩ := hS p hp
      have hFeq : F p = (Work.LinnikContract.zeroMult p.1 p.2 : ℝ) := by
        simp only [F]; rw [if_pos ⟨h1,h2,h3,hzm,him,hlam⟩]
      rw [hFeq]; exact_mod_cast hzm
    have hmem : p ∈ (↑T : Set _) := hsup hp'
    simpa using hmem
  have hge : (S.card : ℝ) ≤ ∑ p ∈ S, F p := by
    have hcard : (S.card : ℝ) = ∑ p ∈ S, (1:ℝ) := by simp
    rw [hcard]
    apply Finset.sum_le_sum
    intro p hp
    obtain ⟨h1,h2,h3,hzm,him,hlam⟩ := hS p hp
    have hFeq : F p = (Work.LinnikContract.zeroMult p.1 p.2 : ℝ) := by
      simp only [F]; rw [if_pos ⟨h1,h2,h3,hzm,him,hlam⟩]
    rw [hFeq]
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hzm)
  have hle : ∑ p ∈ S, F p ≤ ∑ p ∈ T, F p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by
      simp only [F]; split_ifs <;> positivity)
  linarith

theorem second_pair_wide
    (hcount : ∃ C : ℝ, 0 < C ∧ ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → ∀ [NeZero q]
      (χ₁ : DirichletCharacter ℂ q) (Λ H : ℝ),
      Λ ≤ 3 → H ≤ 10 * Real.log (q : ℝ) → Work.ZeroFreeTables.otherLamCount χ₁ Λ H ≤ C) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → ∀ [NeZero q] (χ₁ : DirichletCharacter ℂ q) (ρ₁ : ℂ)
      (χ : DirichletCharacter ℂ q) (ρ : ℂ) (Λ : ℝ),
      Work.ZeroFreeTables.IsMin1WideAt 10 χ₁ ρ₁ → χ₁ ^ 2 = 1 → ρ₁.im = 0 →
      Work.LinnikContract.lamOf q ρ₁ < 696 / 1000 →
      Work.LinnikContract.IsZ χ ρ → χ ≠ χ₁ → χ ≠ χ₁⁻¹ →
      Work.LinnikContract.lamOf q ρ < Λ → Λ ≤ 3 →
      ∃ (χ₂ : DirichletCharacter ℂ q) (ρ₂ : ℂ),
        χ₂ ≠ 1 ∧ χ₂ ≠ χ₁ ∧ χ₂ ≠ χ₁⁻¹ ∧ Work.LinnikContract.zeroMult χ₂ ρ₂ ≠ 0 ∧
        Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q ρ ∧
        2 * |ρ₂.im| + 1 ≤ 10 * Real.log (q : ℝ) ∧
        ∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → ψ ≠ χ₁ → ψ ≠ χ₁⁻¹ →
          Work.LinnikContract.zeroMult ψ u ≠ 0 →
          |u.im| ≤ 2 * |ρ₂.im| + 1 → Work.LinnikContract.lamOf q ρ₂ ≤ Work.LinnikContract.lamOf q u := by
  obtain ⟨C, hCpos, Q₀, hQ₀⟩ := hcount
  set K : ℕ := Nat.ceil C with hK
  obtain ⟨Q, hQge₀, hQge2, hQlog⟩ := exists_Q_log_ge Q₀ K
  refine ⟨Q, ?_⟩
  intro q hqQ _inst χ₁ ρ₁ χ ρ Λ hmin1 hchi1sq hρ₁im hlam1 hIsZ hχχ₁ hχχ₁inv hlamρΛ hΛ3
  have hχ1 : χ ≠ 1 := hIsZ.1
  have hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0 := hIsZ.2.1
  have him1 : |ρ.im| ≤ 1 := hIsZ.2.2
  have hlamρ3 : Work.LinnikContract.lamOf q ρ ≤ 3 := le_of_lt (lt_of_lt_of_le hlamρΛ hΛ3)
  have hHle : (2:ℝ)^(K+1) - 1 ≤ 10 * Real.log (q:ℝ) := by
    have hQq : (Q:ℝ) ≤ (q:ℝ) := by exact_mod_cast hqQ
    have hQpos : (0:ℝ) < (Q:ℝ) := by exact_mod_cast (show 0 < Q by omega)
    have hlogmono : Real.log (Q:ℝ) ≤ Real.log (q:ℝ) := Real.log_le_log hQpos hQq
    linarith [hQlog, hlogmono]
  let Pmin : ℝ → (DirichletCharacter ℂ q × ℂ) → Prop := fun H p =>
    p.1 ≠ 1 ∧ p.1 ≠ χ₁ ∧ p.1 ≠ χ₁⁻¹ ∧ Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧
    |p.2.im| ≤ H ∧ Work.LinnikContract.lamOf q p.2 ≤ Work.LinnikContract.lamOf q ρ ∧
    (∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 → Work.LinnikContract.zeroMult ψ u ≠ 0 →
      |u.im| ≤ H → ψ ≠ χ₁ → ψ ≠ χ₁⁻¹ → Work.LinnikContract.lamOf q p.2 ≤ Work.LinnikContract.lamOf q u)
  have mz : ∀ H : ℝ, 1 ≤ H → ∃ p : DirichletCharacter ℂ q × ℂ, Pmin H p := by
    intro H hH
    obtain ⟨χ₂, ρ₂, h1, h2, h3, h4, h5, h6, h7⟩ :=
      exists_min_other_wide H (le_trans zero_le_one hH) χ₁ χ ρ hχ1 hχχ₁ hχχ₁inv hzm (le_trans him1 hH)
    exact ⟨(χ₂, ρ₂), h1, h2, h3, h4, h5, h6, h7⟩
  let minp : (H : ℝ) → 1 ≤ H → DirichletCharacter ℂ q × ℂ := fun H hH => Classical.choose (mz H hH)
  have minp_spec : ∀ H hH, Pmin H (minp H hH) := fun H hH => Classical.choose_spec (mz H hH)
  have hle_abs : ∀ s : ℝ × (DirichletCharacter ℂ q × ℂ), (1:ℝ) ≤ 2 * |s.2.2.im| + 1 := by
    intro s
    have h : (0:ℝ) ≤ |s.2.2.im| := abs_nonneg _
    linarith
  let f : ℝ × (DirichletCharacter ℂ q × ℂ) → ℝ × (DirichletCharacter ℂ q × ℂ) := fun s =>
    if 2 * |s.2.2.im| + 1 ≤ s.1 then s
    else (2 * |s.2.2.im| + 1, minp (2 * |s.2.2.im| + 1) (hle_abs s))
  let σ : ℕ → ℝ × (DirichletCharacter ℂ q × ℂ) := Nat.rec (1, minp 1 le_rfl) (fun _ s => f s)
  have hstep : ∀ k, σ (Nat.succ k) = f (σ k) := fun k => rfl
  have Inv : ∀ k, 1 ≤ (σ k).1 ∧ Pmin (σ k).1 (σ k).2 := by
    intro k
    induction k with
    | zero => exact ⟨le_rfl, minp_spec 1 le_rfl⟩
    | succ k ih =>
      rw [hstep k]
      simp only [f]
      split_ifs with hcond
      · exact ih
      · exact ⟨hle_abs (σ k), minp_spec (2 * |(σ k).2.2.im| + 1) (hle_abs (σ k))⟩
  have hH1 : ∀ k, 1 ≤ (σ k).1 := fun k => (Inv k).1
  have hP : ∀ k, Pmin (σ k).1 (σ k).2 := fun k => (Inv k).2
  have hPim : ∀ k, |(σ k).2.2.im| ≤ (σ k).1 := fun k => (hP k).2.2.2.2.1
  have hPmin : ∀ k, (∀ (ψ : DirichletCharacter ℂ q) (u : ℂ), ψ ≠ 1 →
      Work.LinnikContract.zeroMult ψ u ≠ 0 → |u.im| ≤ (σ k).1 → ψ ≠ χ₁ → ψ ≠ χ₁⁻¹ →
      Work.LinnikContract.lamOf q (σ k).2.2 ≤ Work.LinnikContract.lamOf q u) :=
    fun k => (hP k).2.2.2.2.2.2
  have hHnext : ∀ k, ¬(2 * |(σ k).2.2.im| + 1 ≤ (σ k).1) →
      (σ (Nat.succ k)).1 = 2 * |(σ k).2.2.im| + 1 := by
    intro k hk
    rw [hstep k]; simp only [f]; rw [if_neg hk]
  have hstep_le : ∀ k, (σ (Nat.succ k)).1 ≤ 2 * (σ k).1 + 1 := by
    intro k
    by_cases hk : 2 * |(σ k).2.2.im| + 1 ≤ (σ k).1
    · rw [hstep k]; simp only [f]; rw [if_pos hk]
      have := hH1 k; linarith
    · rw [hHnext k hk]
      have h := hPim k
      linarith
  have hbdd : ∀ k, (σ k).1 ≤ (2:ℝ)^(k+1) - 1 := by
    intro k
    induction k with
    | zero =>
      have h0 : (σ 0).1 = 1 := rfl
      rw [h0]; norm_num
    | succ k ih =>
      have hs := hstep_le k
      have hpow : (2:ℝ)^(k+1+1) = (2:ℝ)^(k+1) * 2 := by
        rw [show k+1+1 = (k+1)+1 from rfl, pow_succ]
      show (σ (Nat.succ k)).1 ≤ (2:ℝ)^(Nat.succ k + 1) - 1
      rw [show Nat.succ k = k+1 from rfl, hpow]
      linarith [hs, ih]
  have hpowle : ∀ k ≤ K, (2:ℝ)^(k+1) - 1 ≤ (2:ℝ)^(K+1) - 1 := by
    intro k hk
    have hm : (2:ℝ)^(k+1) ≤ (2:ℝ)^(K+1) := by
      apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
      omega
    linarith
  have hex : ∃ k, k ≤ K ∧ 2 * |(σ k).2.2.im| + 1 ≤ (σ k).1 := by
    by_contra hno
    have hno' : ∀ k, k ≤ K → ¬(2 * |(σ k).2.2.im| + 1 ≤ (σ k).1) := by
      intro k hk hle
      exact hno ⟨k, hk, hle⟩
    let P : ℕ → DirichletCharacter ℂ q × ℂ := fun k => (σ k).2
    have himinc : ∀ k < K, |(P k).2.im| < |(P (k+1)).2.im| := by
      intro k hk
      have hkK : k ≤ K := by omega
      have hkp1K : k+1 ≤ K := by omega
      have h1 : (σ (k+1)).1 = 2 * |(σ k).2.2.im| + 1 := hHnext k (hno' k hkK)
      have h2 : (σ ((k+1)+1)).1 = 2 * |(σ (k+1)).2.2.im| + 1 := hHnext (k+1) (hno' (k+1) hkp1K)
      have hlt : (σ (k+1)).1 < (σ ((k+1)+1)).1 := by
        rw [h2]; exact not_le.mp (hno' (k+1) hkp1K)
      have hfin : |(σ k).2.2.im| < |(σ (k+1)).2.2.im| := by
        rw [h1] at hlt
        rw [h2] at hlt
        linarith
      simpa only [P] using hfin
    have hinj : Set.InjOn P ↑(Finset.range (K+1)) := by
      intro i hi j hj hij
      rw [Finset.mem_coe, Finset.mem_range] at hi hj
      have hjK : j ≤ K := by omega
      have hiK : i ≤ K := by omega
      have key : ∀ j ≤ K, ∀ i, i < j → |(P i).2.im| < |(P j).2.im| := by
        intro j
        induction j with
        | zero => intro _ i hi; omega
        | succ j ih =>
          intro hj i hi
          have hjK' : j ≤ K := by omega
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
          · exact lt_trans (ih hjK' i hlt) (himinc j (by omega))
          · rw [heq]; exact himinc j (by omega)
      rcases le_total i j with hle | hle
      · rcases lt_or_eq_of_le hle with hlt | heq
        · have hlt' := key j hjK i hlt
          have hg : |(P i).2.im| = |(P j).2.im| := by rw [hij]
          rw [hg] at hlt'; exact absurd hlt' (lt_irrefl _)
        · exact heq
      · rcases lt_or_eq_of_le hle with hlt | heq
        · have hlt' := key i hiK j hlt
          have hg : |(P i).2.im| = |(P j).2.im| := by rw [hij]
          rw [← hg] at hlt'; exact absurd hlt' (lt_irrefl _)
        · exact heq.symm
    let S : Finset (DirichletCharacter ℂ q × ℂ) := (Finset.range (K+1)).image P
    have hScard : S.card = K+1 := by
      show ((Finset.range (K+1)).image P).card = K + 1
      rw [Finset.card_image_of_injOn hinj]
      simp
    have hScond : ∀ p ∈ S, p.1 ≠ 1 ∧ p.1 ≠ χ₁ ∧ p.1 ≠ χ₁⁻¹ ∧
        Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧ |p.2.im| ≤ (2:ℝ)^(K+1) - 1 ∧
        Work.LinnikContract.lamOf q p.2 ≤ Work.LinnikContract.lamOf q ρ := by
      intro p hp
      rw [show S = (Finset.range (K+1)).image P from rfl, Finset.mem_image] at hp
      obtain ⟨k, hk, rfl⟩ := hp
      rw [Finset.mem_range] at hk
      have hkK : k ≤ K := by omega
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP k
      refine ⟨h1, h2, h3, h4, ?_, h6⟩
      calc |(P k).2.im| ≤ (σ k).1 := h5
        _ ≤ (2:ℝ)^(k+1) - 1 := hbdd k
        _ ≤ (2:ℝ)^(K+1) - 1 := hpowle k hkK
    have hcount_ge : ((K+1 : ℕ) : ℝ) ≤
        otherLamCount χ₁ (Work.LinnikContract.lamOf q ρ) ((2:ℝ)^(K+1) - 1) := by
      have hh := otherLamCount_ge_card χ₁ (Work.LinnikContract.lamOf q ρ) ((2:ℝ)^(K+1) - 1) S hScond
      rwa [hScard] at hh
    have hcount_le : otherLamCount χ₁ (Work.LinnikContract.lamOf q ρ) ((2:ℝ)^(K+1) - 1) ≤ C :=
      hQ₀ q (le_trans hQge₀ hqQ) χ₁ (Work.LinnikContract.lamOf q ρ) ((2:ℝ)^(K+1) - 1) hlamρ3 hHle
    have hKge : C ≤ (K:ℝ) := by
      rw [hK]; exact Nat.le_ceil C
    rw [Nat.cast_add, Nat.cast_one] at hcount_ge
    linarith [hKge, hcount_ge, hcount_le]
  obtain ⟨k, hkK, hgood⟩ := hex
  refine ⟨(σ k).2.1, (σ k).2.2, (hP k).1, (hP k).2.1, (hP k).2.2.1, (hP k).2.2.2.1,
    (hP k).2.2.2.2.2.1, ?_, ?_⟩
  · calc 2 * |(σ k).2.2.im| + 1 ≤ (σ k).1 := hgood
      _ ≤ (2:ℝ)^(k+1) - 1 := hbdd k
      _ ≤ (2:ℝ)^(K+1) - 1 := hpowle k hkK
      _ ≤ 10 * Real.log (q:ℝ) := hHle
  · intro ψ u hψ1 hψχ₁ hψχ₁inv hzm' him'
    exact hPmin k ψ u hψ1 hzm' (le_trans him' hgood) hψχ₁ hψχ₁inv

end Work.ZeroFreeTables
