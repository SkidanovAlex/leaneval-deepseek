import Mathlib
import Submission.Work.ZeroFreeTables.HB88Defs
import Submission.Work.ZeroFreeTables.second_pair_wide

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroFreeTables

/-- **The second pair with the count lifted to a fixed level `K`** (`Work.ZeroFreeTables.PairParam`):
given the parametric count `Work.ZeroFreeTables.OtherLamCountLeK K`, this is
`Work.ZeroFreeTables.second_pair_wide` with its count hypothesis `Λ ≤ 3` replaced by `Λ ≤ K`, so
that the `λ`-bound of the target zero may be any fixed constant.

Route: copy the proof of `second_pair_wide` verbatim; the count is used only in the pigeonhole
`⌈C⌉` iteration (`Work.ZeroFreeTables.exists_min_other_wide`, `otherLamCount_ge_card`,
`exists_Q_log_ge`) at the level `Λ := K`, with `hlamρK : lamOf q ρ ≤ K` in place of `hlamρ3`, and
in the doubling bound `H_{k+1} = 2|ρ_k.im| + 1`. -/
theorem PairParam_of_count (K : ℝ) (hK : 0 < K)
    (hcount : Work.ZeroFreeTables.OtherLamCountLeK K) : Work.ZeroFreeTables.PairParam K := by
  obtain ⟨C, hCpos, Q₀, hQ₀⟩ := hcount
  set Nc : ℕ := Nat.ceil C with hNc
  obtain ⟨Q, hQge₀, hQge2, hQlog⟩ := exists_Q_log_ge Q₀ Nc
  refine ⟨Q, ?_⟩
  intro q hqQ _inst χ₁ ρ₁ χ ρ hmin1 hchi1sq hρ₁im hlam1 hIsZ hχχ₁ hχχ₁inv hlamρK
  have hχ1 : χ ≠ 1 := hIsZ.1
  have hzm : Work.LinnikContract.zeroMult χ ρ ≠ 0 := hIsZ.2.1
  have him1 : |ρ.im| ≤ 1 := hIsZ.2.2
  have hlamρKle : Work.LinnikContract.lamOf q ρ ≤ K := le_of_lt hlamρK
  have hHle : (2:ℝ)^(Nc+1) - 1 ≤ 10 * Real.log (q:ℝ) := by
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
  have hpowle : ∀ k ≤ Nc, (2:ℝ)^(k+1) - 1 ≤ (2:ℝ)^(Nc+1) - 1 := by
    intro k hk
    have hm : (2:ℝ)^(k+1) ≤ (2:ℝ)^(Nc+1) := by
      apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
      omega
    linarith
  have hex : ∃ k, k ≤ Nc ∧ 2 * |(σ k).2.2.im| + 1 ≤ (σ k).1 := by
    by_contra hno
    have hno' : ∀ k, k ≤ Nc → ¬(2 * |(σ k).2.2.im| + 1 ≤ (σ k).1) := by
      intro k hk hle
      exact hno ⟨k, hk, hle⟩
    let P : ℕ → DirichletCharacter ℂ q × ℂ := fun k => (σ k).2
    have himinc : ∀ k < Nc, |(P k).2.im| < |(P (k+1)).2.im| := by
      intro k hk
      have hkK : k ≤ Nc := by omega
      have hkp1K : k+1 ≤ Nc := by omega
      have h1 : (σ (k+1)).1 = 2 * |(σ k).2.2.im| + 1 := hHnext k (hno' k hkK)
      have h2 : (σ ((k+1)+1)).1 = 2 * |(σ (k+1)).2.2.im| + 1 := hHnext (k+1) (hno' (k+1) hkp1K)
      have hlt : (σ (k+1)).1 < (σ ((k+1)+1)).1 := by
        rw [h2]; exact not_le.mp (hno' (k+1) hkp1K)
      have hfin : |(σ k).2.2.im| < |(σ (k+1)).2.2.im| := by
        rw [h1] at hlt
        rw [h2] at hlt
        linarith
      simpa only [P] using hfin
    have hinj : Set.InjOn P ↑(Finset.range (Nc+1)) := by
      intro i hi j hj hij
      rw [Finset.mem_coe, Finset.mem_range] at hi hj
      have hjK : j ≤ Nc := by omega
      have hiK : i ≤ Nc := by omega
      have key : ∀ j ≤ Nc, ∀ i, i < j → |(P i).2.im| < |(P j).2.im| := by
        intro j
        induction j with
        | zero => intro _ i hi; omega
        | succ j ih =>
          intro hj i hi
          have hjK' : j ≤ Nc := by omega
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
    let S : Finset (DirichletCharacter ℂ q × ℂ) := (Finset.range (Nc+1)).image P
    have hScard : S.card = Nc+1 := by
      show ((Finset.range (Nc+1)).image P).card = Nc + 1
      rw [Finset.card_image_of_injOn hinj]
      simp
    have hScond : ∀ p ∈ S, p.1 ≠ 1 ∧ p.1 ≠ χ₁ ∧ p.1 ≠ χ₁⁻¹ ∧
        Work.LinnikContract.zeroMult p.1 p.2 ≠ 0 ∧ |p.2.im| ≤ (2:ℝ)^(Nc+1) - 1 ∧
        Work.LinnikContract.lamOf q p.2 ≤ Work.LinnikContract.lamOf q ρ := by
      intro p hp
      rw [show S = (Finset.range (Nc+1)).image P from rfl, Finset.mem_image] at hp
      obtain ⟨k, hk, rfl⟩ := hp
      rw [Finset.mem_range] at hk
      have hkK : k ≤ Nc := by omega
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP k
      refine ⟨h1, h2, h3, h4, ?_, h6⟩
      calc |(P k).2.im| ≤ (σ k).1 := h5
        _ ≤ (2:ℝ)^(k+1) - 1 := hbdd k
        _ ≤ (2:ℝ)^(Nc+1) - 1 := hpowle k hkK
    have hcount_ge : ((Nc+1 : ℕ) : ℝ) ≤
        otherLamCount χ₁ (Work.LinnikContract.lamOf q ρ) ((2:ℝ)^(Nc+1) - 1) := by
      have hh := otherLamCount_ge_card χ₁ (Work.LinnikContract.lamOf q ρ) ((2:ℝ)^(Nc+1) - 1) S hScond
      rwa [hScard] at hh
    have hcount_le : otherLamCount χ₁ (Work.LinnikContract.lamOf q ρ) ((2:ℝ)^(Nc+1) - 1) ≤ C :=
      hQ₀ q (le_trans hQge₀ hqQ) χ₁ (Work.LinnikContract.lamOf q ρ) ((2:ℝ)^(Nc+1) - 1) hlamρKle hHle
    have hKge : C ≤ (Nc:ℝ) := by
      rw [hNc]; exact Nat.le_ceil C
    rw [Nat.cast_add, Nat.cast_one] at hcount_ge
    linarith [hKge, hcount_ge, hcount_le]
  obtain ⟨k, hkK, hgood⟩ := hex
  refine ⟨(σ k).2.1, (σ k).2.2, (hP k).1, (hP k).2.1, (hP k).2.2.1, (hP k).2.2.2.1,
    (hP k).2.2.2.2.2.1, ?_, ?_⟩
  · calc 2 * |(σ k).2.2.im| + 1 ≤ (σ k).1 := hgood
      _ ≤ (2:ℝ)^(k+1) - 1 := hbdd k
      _ ≤ (2:ℝ)^(Nc+1) - 1 := hpowle k hkK
      _ ≤ 10 * Real.log (q:ℝ) := hHle
  · intro ψ u hψ1 hψχ₁ hψχ₁inv hzm' him'
    exact hPmin k ψ u hψ1 hzm' (le_trans him' hgood) hψχ₁ hψχ₁inv

end Work.ZeroFreeTables
