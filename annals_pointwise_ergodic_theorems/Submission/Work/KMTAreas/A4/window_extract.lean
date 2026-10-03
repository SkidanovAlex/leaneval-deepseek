import Mathlib
import Submission.Work.KMTAreas.A4.winBase

namespace Work.KMTAreas.A4

open scoped BigOperators
open Work.Analysis.InverseTheory

/-- The sum of `u` over the length-`L` block of integers starting at `k`:
`∑_{n ∈ [k, k+L-1]} u n`. -/
noncomputable def winBlockSum (u : ℤ → ℂ) (L : ℕ) (k : ℤ) : ℂ :=
  ∑ n ∈ Finset.Icc k (k + (L : ℤ) - 1), u n

/-- Reindex a sum over the block `[n-(L-1), n]` by the distance from its right endpoint. -/
lemma winBlock_Icc_eq_sum_range (L : ℕ) (hL : 1 ≤ L) (n : ℤ) (g : ℤ → ℝ) :
    ∑ k ∈ Finset.Icc (n - ((L : ℤ) - 1)) n, g k
      = ∑ t ∈ Finset.range L, g (n - (t : ℤ)) := by
  refine Finset.sum_bij (fun k hk => (n - k).toNat) ?_ ?_ ?_ ?_
  · intro k hk
    rw [Finset.mem_range]
    have hk' : n - ((L : ℤ) - 1) ≤ k ∧ k ≤ n := Finset.mem_Icc.mp hk
    have hnk : 0 ≤ n - k := by omega
    have hcast : (((n - k).toNat : ℤ)) = n - k := Int.toNat_of_nonneg hnk
    have : (((n - k).toNat : ℤ)) < (L : ℤ) := by omega
    exact_mod_cast this
  · intro k1 hk1 k2 hk2 h
    have h1 : 0 ≤ n - k1 := by have := Finset.mem_Icc.mp hk1; omega
    have h2 : 0 ≤ n - k2 := by have := Finset.mem_Icc.mp hk2; omega
    have e1 : (((n - k1).toNat : ℤ)) = n - k1 := Int.toNat_of_nonneg h1
    have e2 : (((n - k2).toNat : ℤ)) = n - k2 := Int.toNat_of_nonneg h2
    have : ((n - k1).toNat : ℤ) = ((n - k2).toNat : ℤ) := by exact_mod_cast h
    omega
  · intro t ht
    refine ⟨n - (t : ℤ), ?_, ?_⟩
    · rw [Finset.mem_Icc]
      have htL : t < L := Finset.mem_range.mp ht
      constructor <;> omega
    · have hsub : n - (n - (t : ℤ)) = (t : ℤ) := by ring
      rw [hsub]
      simp
  · intro k hk
    have hk' : n - ((L : ℤ) - 1) ≤ k ∧ k ≤ n := Finset.mem_Icc.mp hk
    have hnk : 0 ≤ n - k := by omega
    have hcast : (((n - k).toNat : ℤ)) = n - k := Int.toNat_of_nonneg hnk
    congr 1
    omega

/-- The `ℓ¹` norm of the block-indicator weights at a fixed `n` is bounded by the sum of the
absolute values of a single length-`L` window of `ρ`. -/
lemma winBlock_tsum_norm_le (ρ u : ℤ → ℂ) (L : ℕ) (hL : 1 ≤ L) (s : ℤ)
    (hu : ∀ n : ℤ, ‖u n‖ ≤ 1) (n : ℤ) :
    (∑' k : ℤ, ‖(ρ (k - s) *
        (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0)) * u n‖)
      ≤ ∑ t ∈ Finset.range L, ‖ρ (n - (t : ℤ) - s)‖ := by
  calc
    (∑' k : ℤ, ‖(ρ (k - s) *
        (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0)) * u n‖)
      = ∑ k ∈ Finset.Icc (n - ((L : ℤ) - 1)) n, ‖ρ (k - s) * u n‖ := by
          rw [tsum_eq_sum (s := Finset.Icc (n - ((L : ℤ) - 1)) n)]
          · apply Finset.sum_congr rfl
            intro k hk
            have hcond : k ≤ n ∧ n ≤ k + (L : ℤ) - 1 := by
              have hk' : n - ((L : ℤ) - 1) ≤ k ∧ k ≤ n := Finset.mem_Icc.mp hk
              omega
            rw [if_pos hcond]
            simp
          · intro k hk
            have hnot : ¬ (k ≤ n ∧ n ≤ k + (L : ℤ) - 1) := by
              intro h
              exact hk (Finset.mem_Icc.mpr (by omega))
            rw [if_neg hnot]
            simp
    _ ≤ ∑ k ∈ Finset.Icc (n - ((L : ℤ) - 1)) n, ‖ρ (k - s)‖ := by
          apply Finset.sum_le_sum
          intro k hk
          rw [norm_mul]
          have h := mul_le_mul_of_nonneg_left (hu n) (norm_nonneg (ρ (k - s)))
          simpa using h
    _ = ∑ t ∈ Finset.range L, ‖ρ (n - (t : ℤ) - s)‖ := by
          simpa using winBlock_Icc_eq_sum_range L hL n (fun k => ‖ρ (k - s)‖)

/-- The double family `(n,k) ↦ ρ(k-s) 1_{k ≤ n ≤ k+L-1} u n` is summable. -/
lemma winBlock_summable_double (ρ u : ℤ → ℂ) (L : ℕ) (hL : 1 ≤ L) (s : ℤ)
    (hρ : Summable ρ) (hu : ∀ n : ℤ, ‖u n‖ ≤ 1) :
    Summable (fun p : ℤ × ℤ =>
      (ρ (p.2 - s) *
        (if p.2 ≤ p.1 ∧ p.1 ≤ p.2 + (L : ℤ) - 1 then (1 : ℂ) else 0)) * u p.1) := by
  let g : ℤ × ℤ → ℂ := fun p =>
      (ρ (p.2 - s) *
        (if p.2 ≤ p.1 ∧ p.1 ≤ p.2 + (L : ℤ) - 1 then (1 : ℂ) else 0)) * u p.1
  have hnorm : Summable (fun p : ℤ × ℤ => ‖g p‖) := by
    refine (summable_prod_of_nonneg (f := fun p : ℤ × ℤ => ‖g p‖)
      (by intro p; exact norm_nonneg _)).mpr ?_
    constructor
    · intro n
      refine summable_of_ne_finset_zero (s := Finset.Icc (n - ((L : ℤ) - 1)) n) ?_
      intro k hk
      have hnot : ¬ (k ≤ n ∧ n ≤ k + (L : ℤ) - 1) := by
        intro h
        exact hk (Finset.mem_Icc.mpr (by omega))
      simp only [g]
      rw [if_neg hnot]
      simp
    · have hG : Summable (fun n : ℤ => ∑ t ∈ Finset.range L, ‖ρ (n - (t : ℤ) - s)‖) := by
        refine summable_finset_sum (Finset.range L) ?_
        intro t ht
        have hinj : Function.Injective (fun n : ℤ => n - (t : ℤ) - s) := by
          intro a b h
          change a - (t : ℤ) - s = b - (t : ℤ) - s at h
          omega
        exact (summable_norm_iff.mpr hρ).comp_injective hinj
      refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun k => norm_nonneg _) ?_ hG
      intro n
      exact winBlock_tsum_norm_le ρ u L hL s hu n
  exact Summable.of_norm hnorm

/-- For fixed `k`, the `n`-sum of the block indicator times `u` factors as `ρ(k-s)` times the
block sum of `u`. -/
lemma winBlock_tsum_factor (ρ u : ℤ → ℂ) (L : ℕ) (s k : ℤ) :
    (∑' n : ℤ, (ρ (k - s) *
        (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0)) * u n)
      = ρ (k - s) * winBlockSum u L k := by
  rw [winBlockSum]
  calc
    (∑' n : ℤ, (ρ (k - s) *
        (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0)) * u n)
      = ∑' n : ℤ, ρ (k - s) *
          ((if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0) * u n) := by
          apply tsum_congr
          intro n
          ring
    _ = ρ (k - s) * ∑' n : ℤ,
          (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0) * u n := by
          rw [tsum_mul_left]
    _ = ρ (k - s) * ∑ n ∈ Finset.Icc k (k + (L : ℤ) - 1), u n := by
          congr 1
          rw [tsum_eq_sum (s := Finset.Icc k (k + (L : ℤ) - 1))]
          · apply Finset.sum_congr rfl
            intro n hn
            have hcond : k ≤ n ∧ n ≤ k + (L : ℤ) - 1 := Finset.mem_Icc.mp hn
            rw [if_pos hcond]
            simp
          · intro n hn
            have hnot : ¬ (k ≤ n ∧ n ≤ k + (L : ℤ) - 1) := by
              intro h
              exact hn (Finset.mem_Icc.mpr h)
            rw [if_neg hnot]
            simp

/-- Fubini: a windowed sum whose window is a sliding length-`L` block average of `ρ` equals the
corresponding `ρ`-weighted sum of block sums of `u`. -/
lemma winTsum_eq_blockTsum (ρ u : ℤ → ℂ) (L : ℕ) (hL : 1 ≤ L) (s : ℤ) (w : ℤ → ℂ)
    (hρ : Summable ρ) (hu : ∀ n : ℤ, ‖u n‖ ≤ 1)
    (hdecomp : ∀ n : ℤ, w n = ∑' k : ℤ, ρ (k - s) *
          (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0)) :
    ∑' n : ℤ, w n * u n = ∑' k : ℤ, ρ (k - s) * winBlockSum u L k := by
  let f : ℤ → ℤ → ℂ := fun n k =>
      (ρ (k - s) * (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0)) * u n
  have hf : Summable (Function.uncurry f) := by
    change Summable (fun p : ℤ × ℤ => f p.1 p.2)
    exact winBlock_summable_double ρ u L hL s hρ hu
  calc
    ∑' n : ℤ, w n * u n = ∑' n : ℤ, ∑' k : ℤ, f n k := by
          apply tsum_congr
          intro n
          rw [hdecomp n]
          rw [← tsum_mul_right]
    _ = ∑' k : ℤ, ∑' n : ℤ, f n k := (Summable.tsum_comm hf).symm
    _ = ∑' k : ℤ, ρ (k - s) * winBlockSum u L k := by
          apply tsum_congr
          intro k
          exact winBlock_tsum_factor ρ u L s k

/-- Extraction of one block from a large windowed sum: if the window is a sliding block average of
`ρ` with `ℓ¹` mass at most `A/L`, then some length-`L` block has norm at least
`ε L / (K A)`. -/
lemma winExtract_block (K : ℝ) (hK : 1 < K) (w : ℤ → ℂ) (L : ℕ) (hL : 1 ≤ L) (s : ℤ)
    (ρ u : ℤ → ℂ) (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε)
    (hu : ∀ n : ℤ, ‖u n‖ ≤ 1) (hρ : Summable ρ)
    (hρb : (∑' k : ℤ, ‖ρ k‖) ≤ A / (L : ℝ))
    (hdecomp : ∀ n : ℤ, w n = ∑' k : ℤ, ρ (k - s) *
          (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0))
    (hwin : ε ≤ ‖∑' n : ℤ, w n * u n‖) :
    ∃ a b : ℤ, a ≤ b ∧ (((b - a : ℤ) : ℝ) + 1) ≤ (L : ℝ) ∧
        ε * L / (K * A) ≤ ‖∑ n ∈ Finset.Icc a b, u n‖ := by
  by_contra hno
  have hBs : ∀ k : ℤ, ‖winBlockSum u L k‖ < ε * (L : ℝ) / (K * A) := by
    intro k
    apply lt_of_not_ge
    intro hc
    apply hno
    refine ⟨k, k + (L : ℤ) - 1, ?_, ?_, ?_⟩
    · have hLZ : (0 : ℤ) ≤ (L : ℤ) - 1 := by omega
      omega
    · have hlen : ((k + (L : ℤ) - 1 - k : ℤ) : ℝ) + 1 = (L : ℝ) := by
        have hz : k + (L : ℤ) - 1 - k = (L : ℤ) - 1 := by ring
        rw [hz]
        push_cast
        ring
      rw [hlen]
    · simpa [winBlockSum] using hc
  have hid := winTsum_eq_blockTsum ρ u L hL s w hρ hu hdecomp
  have hwin' : ε ≤ ‖∑' k : ℤ, ρ (k - s) * winBlockSum u L k‖ := by
    rwa [hid] at hwin
  set c : ℝ := ε * (L : ℝ) / (K * A) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    positivity
  have hshift : (∑' k : ℤ, ‖ρ (k - s)‖) = ∑' k : ℤ, ‖ρ k‖ := by
    simpa using (Equiv.subRight s).tsum_eq (fun k : ℤ => ‖ρ k‖)
  have hρb_shift : (∑' k : ℤ, ‖ρ (k - s)‖) ≤ A / (L : ℝ) := by
    rw [hshift]; exact hρb
  have hnormshift : Summable (fun k : ℤ => ‖ρ (k - s)‖) := by
    have hinj : Function.Injective (fun k : ℤ => k - s) := by
      intro a b h
      change a - s = b - s at h
      omega
    exact (summable_norm_iff.mpr hρ).comp_injective hinj
  have hg : Summable (fun k : ℤ => ‖ρ (k - s)‖ * c) := hnormshift.mul_right c
  have hsum_norm_block : Summable (fun k : ℤ => ‖ρ (k - s) * winBlockSum u L k‖) := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) ?_ hg
    intro k
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (le_of_lt (hBs k)) (norm_nonneg _)
  have hle : ‖∑' k : ℤ, ρ (k - s) * winBlockSum u L k‖ ≤ c * (A / (L : ℝ)) := by
    calc
      ‖∑' k : ℤ, ρ (k - s) * winBlockSum u L k‖
          ≤ ∑' k : ℤ, ‖ρ (k - s) * winBlockSum u L k‖ :=
              norm_tsum_le_tsum_norm hsum_norm_block
      _ ≤ ∑' k : ℤ, ‖ρ (k - s)‖ * c := by
              refine Summable.tsum_le_tsum (fun k => ?_) hsum_norm_block hg
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (le_of_lt (hBs k)) (norm_nonneg _)
      _ = c * (∑' k : ℤ, ‖ρ (k - s)‖) := by rw [tsum_mul_right, mul_comm]
      _ ≤ c * (A / (L : ℝ)) := mul_le_mul_of_nonneg_left hρb_shift hcpos.le
  have hcalc : c * (A / (L : ℝ)) = ε / K := by
    rw [hcdef]
    have hLne : (L : ℝ) ≠ 0 := by positivity
    field_simp [hA.ne', hK.ne', hLne]
  have hle_eps : ε ≤ ε / K := by
    calc ε ≤ ‖∑' k : ℤ, ρ (k - s) * winBlockSum u L k‖ := hwin'
      _ ≤ c * (A / (L : ℝ)) := hle
      _ = ε / K := hcalc
  have hKpos : 0 < K := by linarith
  have hlt_eps : ε / K < ε := by
    rw [div_lt_iff₀ hKpos]
    nlinarith
  exact not_lt_of_ge hle_eps hlt_eps

theorem window_extract :
    ∃ K : ℝ, 0 < K ∧ ∀ (M : ℝ) (L : ℕ) (s : ℤ) (ρ u : ℤ → ℂ) (A ε : ℝ),
      1 ≤ M → 1 ≤ L → 0 < A → 0 < ε →
      (∀ n : ℤ, ‖u n‖ ≤ 1) → Summable ρ → (∑' k : ℤ, ‖ρ k‖) ≤ A / L →
      (∀ n : ℤ, (∑' k : ℤ, ρ (k - s) *
          (if k ≤ n ∧ n ≤ k + (L : ℤ) - 1 then (1 : ℂ) else 0))
            = Work.KMTAreas.A4.win M (0 : Work.Analysis.InverseTheory.FreqCircle) (n - s)) →
      ε ≤ ‖∑' n : ℤ, Work.KMTAreas.A4.win M (0 : Work.Analysis.InverseTheory.FreqCircle) (n - s) * u n‖ →
      ∃ a b : ℤ, a ≤ b ∧ (((b - a : ℤ) : ℝ) + 1) ≤ (L : ℝ) ∧
        ε * L / (K * A) ≤ ‖∑ n ∈ Finset.Icc a b, u n‖ := by
  refine ⟨2, by norm_num, ?_⟩
  intro M L s ρ u A ε hM hL hA hε hu hρ hρb hdecomp hwin
  refine winExtract_block (K := 2) (by norm_num) (w := fun n : ℤ => win M (0 : FreqCircle) (n - s))
    (L := L) (hL := hL) (s := s) (ρ := ρ) (u := u) (A := A) (ε := ε)
    hA hε hu hρ ?_ ?_ ?_
  · simpa using hρb
  · intro n
    exact (hdecomp n).symm
  · exact hwin

end Work.KMTAreas.A4
