import Mathlib
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs
import Submission.Work.ZeroDensity.Jutila.LzAux.KappaConvIdentity
import Submission.Work.ZeroDensity.Jutila.uniAQBound
import Submission.Commons.NumberTheory.Moebius.log_weighted_moebius_recip_bound
import Submission.Work.LinnikAreas.Density4.sum_Icc_filter_dvd_reindex


/-! Re-homing of `KMSsumOneDecay` into `Work.ZeroDensity.Jutila.LzDiffAux`, so that its import
closure avoids `LinnikAreas.JutilaPieces.MobiusKappaAux` (whose `Density4.KappaDefs` dependency
clashes with `Density4.BzBilinDefs`).  The elementary `1/(d√d)`-sum lemmas that the original
obtained from `MobiusKappaAux` are inlined below. -/

namespace Work.ZeroDensity.Jutila.LzDiffAux

open Finset
open Work.ZeroDensity.Jutila

noncomputable section
lemma sqrt_inv_step (n : ℕ) (hn : 2 ≤ n) :
    (1:ℝ)/((n:ℝ) * Real.sqrt (n:ℝ))
      ≤ 2 * ((1:ℝ)/Real.sqrt (((n-1:ℕ):ℝ)) - (1:ℝ)/Real.sqrt (n:ℝ)) := by
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn1R : ((n-1:ℕ):ℝ) = (n:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]; norm_num
  have hn1pos : (0:ℝ) < ((n-1:ℕ):ℝ) := by rw [hn1R]; linarith
  set a : ℝ := Real.sqrt (((n-1:ℕ):ℝ)) with ha
  set b : ℝ := Real.sqrt (n:ℝ) with hb
  have hapos : 0 < a := Real.sqrt_pos.mpr hn1pos
  have hbpos : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have ha2 : a^2 = ((n-1:ℕ):ℝ) := Real.sq_sqrt hn1pos.le
  have hb2 : b^2 = (n:ℝ) := Real.sq_sqrt (by positivity)
  have hsum : 0 < a + b := by linarith
  have hab : a*b ≤ (n:ℝ) + 1 := by
    have hsq : (a*b)^2 ≤ ((n:ℝ)+1)^2 := by
      rw [mul_pow, ha2, hb2, hn1R]
      nlinarith
    nlinarith [hsq, mul_nonneg hapos.le hbpos.le, hnR]
  have hkey : a*(a+b) ≤ 2*b^2 := by
    nlinarith [ha2, hb2, hn1R, hab]
  have hba : b - a = 1/(a+b) := by
    rw [eq_div_iff (ne_of_gt hsum)]
    nlinarith [ha2, hb2, hn1R]
  have hL : (1:ℝ)/((n:ℝ) * b) = 1/b^3 := by rw [← hb2]; field_simp
  rw [hL]
  have h1 : (1:ℝ)/a - (1:ℝ)/b = (b-a)/(a*b) := by field_simp
  rw [h1, hba]
  rw [show (2:ℝ) * (1/(a+b)/(a*b)) = 2/((a+b)*(a*b)) by field_simp]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < b^3)]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < (a+b)*(a*b))]
  nlinarith [hkey]

lemma telescope_inv_sqrt (N M : ℕ) (hN : 1 ≤ N) (hNM : N ≤ M) :
    (∑ n ∈ Finset.Icc (N+1) M,
        ((1:ℝ)/Real.sqrt (((n-1:ℕ):ℝ)) - (1:ℝ)/Real.sqrt (n:ℝ)))
      = (1:ℝ)/Real.sqrt (N:ℝ) - (1:ℝ)/Real.sqrt (M:ℝ) := by
  induction M, hNM using Nat.le_induction with
  | base =>
      rw [Finset.Icc_eq_empty (by omega : ¬ N + 1 ≤ N), Finset.sum_empty]
      ring
  | succ M hNM ih =>
      rw [Finset.sum_Icc_succ_top (by omega : N + 1 ≤ M + 1), ih]
      have hcast : ((M + 1 - 1 : ℕ) : ℝ) = (M:ℝ) := by
        rw [Nat.add_sub_cancel]
      rw [hcast]
      ring

lemma sum_inv_sqrt_mul_tail (N M : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc (N+1) M, (1:ℝ)/((n:ℝ) * Real.sqrt (n:ℝ)))
      ≤ 2 / Real.sqrt (N:ℝ) := by
  by_cases hMN : M ≤ N
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · have hNM : N ≤ M := by omega
    calc (∑ n ∈ Finset.Icc (N+1) M, (1:ℝ)/((n:ℝ) * Real.sqrt (n:ℝ)))
        ≤ ∑ n ∈ Finset.Icc (N+1) M,
            2 * ((1:ℝ)/Real.sqrt (((n-1:ℕ):ℝ)) - (1:ℝ)/Real.sqrt (n:ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          rw [Finset.mem_Icc] at hn
          exact sqrt_inv_step n (by omega)
      _ = 2 * ((1:ℝ)/Real.sqrt (N:ℝ) - (1:ℝ)/Real.sqrt (M:ℝ)) := by
          rw [← Finset.mul_sum, telescope_inv_sqrt N M hN hNM]
      _ ≤ 2 / Real.sqrt (N:ℝ) := by
          have h1 : 0 ≤ 2 * ((1:ℝ)/Real.sqrt (M:ℝ)) := by positivity
          have h2 : 2 / Real.sqrt (N:ℝ) = 2 * (1/Real.sqrt (N:ℝ)) := by
            rw [div_eq_mul_one_div]
          rw [mul_sub, h2]
          linarith

lemma sum_inv_sqrt_mul_le (M : ℕ) :
    (∑ d ∈ Finset.Icc 1 M, (1:ℝ)/((d:ℝ) * Real.sqrt (d:ℝ))) ≤ 3 := by
  have h1 : (∑ d ∈ Finset.Icc 2 M, (1:ℝ)/((d:ℝ) * Real.sqrt (d:ℝ)))
      ≤ 2 / Real.sqrt (1:ℝ) := by
    simpa using sum_inv_sqrt_mul_tail 1 M le_rfl
  rw [Real.sqrt_one, div_one] at h1
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM; simp
  · have hsplit : Finset.Icc 1 M = insert 1 (Finset.Icc 2 M) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    rw [hsplit, Finset.sum_insert (by simp)]
    have hval : (1:ℝ)/(((1:ℕ):ℝ) * Real.sqrt (((1:ℕ):ℝ))) = 1 := by norm_num
    rw [hval]
    linarith


/-!
# Decay of `Σ_{r ≤ x} μ(r)/κ(r)`

The main theorem `KMSsumOneDecay` shows that `Ssum x 1 = Σ_{r ≤ x, (r,1)=1} μ(r)/κ(r)` is
bounded by `K·Dc c x = K·exp(-(c·√(log x)))` for suitable absolute `K, c > 0`.

The proof rests on three ingredients, all available in the workspace:

* the Dirichlet-convolution identity `μ/κ = d₀ ∗ (μ/id)` with `d₀(d) = 1/(d·κ(d))`
  (`LzAux.KappaConvIdentity`), which reindexes the sum as
  `Ssum x 1 = Σ_{d ≤ x} (1/(d·κ(d)))·M(⌊x/d⌋)`, `M(y) = Σ_{k ≤ y} μ(k)/k`;
* the de la Vallée Poussin decay `|M(y)| ≤ C·exp(-c√(log y))` (`Commons…moebius_recip_sum_exp_decay`);
* the two bounds for the weight `gam d = 1/(d·kap d)` (`kap d = ∏_{p|d}(p+1) = κ(d)` on squarefree
  `d`): the partial sums `Σ_{d ≤ N} gam d ≤ K` (from `uniAQBound`, via `kap d ≥ rad d`) and the tail
  bound `Σ_{M < d ≤ N} gam d ≤ 6/√M` (from the squarefree decomposition `d = a·b²` of `uniAQBound`).
-/

/-! ## Part 1: the weight and its bounds -/

/-- `gam d = 1/(d·kap d)`, the weight of the convolution identity. -/
def gam (d : ℕ) : ℝ := ((d : ℝ) * kap d)⁻¹

lemma gam_nonneg (d : ℕ) : 0 ≤ gam d :=
  inv_nonneg.mpr (mul_nonneg (Nat.cast_nonneg d) (le_of_lt (kap_pos d)))

lemma gam_pos {d : ℕ} (hd : 1 ≤ d) : 0 < gam d :=
  inv_pos.mpr (mul_pos (by exact_mod_cast hd) (kap_pos d))

/-- `kap d ≥ rad d`, hence `gam d ≤ 1/(d·rad d)`. -/
lemma kap_ge_rad (d : ℕ) : (rad d : ℝ) ≤ kap d := by
  rw [rad, kap, Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun p _ => by positivity) (fun p _ => by linarith)

lemma gam_le_inv_rad {d : ℕ} (hd : 1 ≤ d) : gam d ≤ 1 / ((d : ℝ) * (rad d : ℝ)) := by
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hr : (0 : ℝ) < (rad d : ℝ) := by
    rw [rad]
    exact_mod_cast Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
  have h := one_div_le_one_div_of_le (mul_pos hd0 hr)
    (mul_le_mul_of_nonneg_left (kap_ge_rad d) hd0.le)
  simpa [gam, one_div] using h

/-- Partial sums of the weight are bounded, by `uniAQBound`. -/
lemma gam_partial : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
    (∑ d ∈ Finset.Icc 1 N, gam d) ≤ C := by
  obtain ⟨K, hK, hKb⟩ := uniAQBound
  refine ⟨K, hK, fun N => ?_⟩
  calc (∑ d ∈ Finset.Icc 1 N, gam d)
      ≤ ∑ d ∈ Finset.Icc 1 N, 1 / ((d : ℝ) * (rad d : ℝ)) :=
        Finset.sum_le_sum (fun d hd => gam_le_inv_rad (Finset.mem_Icc.mp hd).1)
    _ ≤ K := hKb N

/-- `Σ_{b ∈ Icc K L} 1/b² ≤ 2/K` for `K ≥ 1`. -/
lemma sum_inv_sq_Icc_le (K L : ℕ) (hK : 1 ≤ K) :
    (∑ b ∈ Finset.Icc K L, 1 / (b : ℝ) ^ 2) ≤ 2 / (K : ℝ) := by
  rcases eq_or_lt_of_le hK with h | h
  · subst h
    calc (∑ b ∈ Finset.Icc 1 L, 1 / (b : ℝ) ^ 2) ≤ 2 := uniAQInvSqSum L
      _ = 2 / ((1 : ℕ) : ℝ) := by norm_num
  · have hK2 : 2 ≤ K := h
    by_cases hKL : K ≤ L
    · have hterm : ∀ b ∈ Finset.Icc K L, 1 / (b : ℝ) ^ 2 ≤ 1 / ((b : ℝ) * ((b : ℝ) - 1)) := by
        intro b hb
        have hb2 : 2 ≤ b := le_trans hK2 (Finset.mem_Icc.mp hb).1
        have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
        have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
          have : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
          linarith
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      have htel : (∑ b ∈ Finset.Icc K L, 1 / ((b : ℝ) * ((b : ℝ) - 1)))
          = 1 / ((K : ℝ) - 1) - 1 / (L : ℝ) := by
        have hsub := Finset.sum_Icc_sub (m := K) (n := L) hKL
          (f := fun i : ℕ => -(1 / ((i : ℝ) - 1)))
        have hcongr : (∑ b ∈ Finset.Icc K L, 1 / ((b : ℝ) * ((b : ℝ) - 1)))
            = ∑ b ∈ Finset.Icc K L,
                (-(1 / ((((b + 1 : ℕ)) : ℝ) - 1)) - -(1 / ((b : ℝ) - 1))) := by
          apply Finset.sum_congr rfl
          intro b hb
          have hb2 : 2 ≤ b := le_trans hK2 (Finset.mem_Icc.mp hb).1
          have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 0 < b)
          have hb1 : (0 : ℝ) < (b : ℝ) - 1 := by
            have : (1 : ℝ) < (b : ℝ) := by exact_mod_cast (by omega : 1 < b)
            linarith
          have hcast : (((b + 1 : ℕ)) : ℝ) - 1 = (b : ℝ) := by push_cast; ring
          rw [hcast]
          field_simp
          ring
        rw [hcongr, hsub]
        have hcastL : (((L + 1 : ℕ)) : ℝ) - 1 = (L : ℝ) := by push_cast; ring
        rw [hcastL]
        ring
      calc (∑ b ∈ Finset.Icc K L, 1 / (b : ℝ) ^ 2)
          ≤ ∑ b ∈ Finset.Icc K L, 1 / ((b : ℝ) * ((b : ℝ) - 1)) := Finset.sum_le_sum hterm
        _ = 1 / ((K : ℝ) - 1) - 1 / (L : ℝ) := htel
        _ ≤ 1 / ((K : ℝ) - 1) := by
            have : (0 : ℝ) ≤ 1 / (L : ℝ) := by positivity
            linarith
        _ ≤ 2 / (K : ℝ) := by
            have hK1' : (0 : ℝ) < (K : ℝ) - 1 := by
              have : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hK2
              linarith
            have hK0' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
            rw [div_le_div_iff₀ hK1' hK0']
            have hK2' : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK2
            linarith
    · have hemp : Finset.Icc K L = ∅ := Finset.Icc_eq_empty_iff.mpr (by omega)
      rw [hemp, Finset.sum_empty]
      positivity

/-- **Tail bound for the weight `gam`**: `Σ_{M < d ≤ N} 1/(d·kap d) ≤ 6/√M` for `M ≥ 1`. -/
theorem gam_tail : ∀ M N : ℕ, 1 ≤ M →
    (∑ d ∈ Finset.Icc (M + 1) N, gam d) ≤ 6 / Real.sqrt (M : ℝ) := by
  intro M N hM
  have hstep1 : (∑ d ∈ Finset.Icc (M + 1) N, gam d)
      ≤ ∑ d ∈ Finset.Icc (M + 1) N, 1 / ((d : ℝ) * (rad d : ℝ)) :=
    Finset.sum_le_sum (fun d hd =>
      gam_le_inv_rad (le_trans (by omega : 1 ≤ M + 1) (Finset.mem_Icc.mp hd).1))
  set φ : ℕ → ℕ × ℕ := fun d => (sqfreePart d, sqRoot d) with hφ
  set F : ℕ × ℕ → ℝ := fun p => 1 / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2) with hF
  have hterm : ∀ d ∈ Finset.Icc (M + 1) N, 1 / ((d : ℝ) * (rad d : ℝ)) ≤ F (φ d) := by
    intro d hd
    have hd0 : d ≠ 0 := by
      have := (Finset.mem_Icc.mp hd).1
      omega
    have h := invMulRad_le_inv_sq_mul_sq (a := sqfreePart d) (b := sqRoot d)
      (one_le_sqfreePart hd0) (one_le_sqRoot hd0) (sqRoot_sq_mul_sqfreePart d)
      (sqfreePart_dvd_rad d hd0)
    simpa only [hF, hφ] using h
  have hinj : Set.InjOn φ ↑(Finset.Icc (M + 1) N) := by
    intro d _ d' _ heq
    have h1 : sqfreePart d = sqfreePart d' := congrArg Prod.fst heq
    have h2 : sqRoot d = sqRoot d' := congrArg Prod.snd heq
    calc d = sqRoot d ^ 2 * sqfreePart d := (sqRoot_sq_mul_sqfreePart d).symm
      _ = sqRoot d' ^ 2 * sqfreePart d' := by rw [h1, h2]
      _ = d' := sqRoot_sq_mul_sqfreePart d'
  have hsub : (Finset.Icc (M + 1) N).image φ ⊆
      ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter (fun p => M < p.1 * p.2 ^ 2) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    have hdlo : M + 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hdN : d ≤ N := (Finset.mem_Icc.mp hd).2
    have hd0 : d ≠ 0 := by omega
    have ha1 := one_le_sqfreePart hd0
    have hb1 := one_le_sqRoot hd0
    have hspec := sqRoot_sq_mul_sqfreePart d
    have hbpos : 0 < sqRoot d := by omega
    have hapos : 0 < sqfreePart d := by omega
    have ha_le : sqfreePart d ≤ d := by
      have h : sqfreePart d ≤ sqRoot d ^ 2 * sqfreePart d :=
        Nat.le_mul_of_pos_left _ (pow_pos hbpos 2)
      rwa [hspec] at h
    have hb_le : sqRoot d ≤ d := by
      have h1 : sqRoot d ≤ sqRoot d * sqRoot d := Nat.le_mul_of_pos_left _ hbpos
      have h2 : sqRoot d * sqRoot d ≤ sqRoot d * sqRoot d * sqfreePart d :=
        Nat.le_mul_of_pos_right _ hapos
      have h3 : sqRoot d * sqRoot d * sqfreePart d = sqRoot d ^ 2 * sqfreePart d := by ring
      rw [h3] at h2
      exact (h1.trans h2).trans_eq hspec
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [(by rfl : φ d = (sqfreePart d, sqRoot d)), Finset.mem_product]
      exact ⟨Finset.mem_Icc.mpr ⟨ha1, ha_le.trans hdN⟩,
        Finset.mem_Icc.mpr ⟨hb1, hb_le.trans hdN⟩⟩
    · show M < sqfreePart d * sqRoot d ^ 2
      have hspec' : sqfreePart d * sqRoot d ^ 2 = d := by
        rw [mul_comm, sqRoot_sq_mul_sqfreePart d]
      rw [hspec']
      omega
  have hbound : (∑ x ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
        (fun p => M < p.1 * p.2 ^ 2), F x) ≤ 6 / Real.sqrt (M : ℝ) := by
    rw [Finset.sum_filter, Finset.sum_product]
    have hinner : ∀ a ∈ Finset.Icc 1 N,
        (∑ b ∈ Finset.Icc 1 N, (if M < a * b ^ 2 then F (a, b) else 0))
          ≤ (2 / Real.sqrt (M : ℝ)) * (1 / ((a : ℝ) * Real.sqrt (a : ℝ))) := by
      intro a ha
      have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
      have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
      have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
      set Y : ℝ := Real.sqrt (M : ℝ) / Real.sqrt (a : ℝ) with hY
      have hYpos : 0 < Y := div_pos (Real.sqrt_pos.mpr hM0) (Real.sqrt_pos.mpr ha0)
      set K : ℕ := ⌊Y⌋₊ + 1 with hKdef
      have hK1 : 1 ≤ K := Nat.le_add_left 1 _
      have hcont : (Finset.Icc 1 N).filter (fun b => M < a * b ^ 2) ⊆ Finset.Icc K N := by
        intro b hb
        rw [Finset.mem_filter, Finset.mem_Icc] at hb
        obtain ⟨⟨hb1, hbN⟩, hcond⟩ := hb
        have hb0 : (0 : ℝ) < (b : ℝ) := by exact_mod_cast hb1
        have hYb : Y < (b : ℝ) := by
          have h2 : (M : ℝ) < (a : ℝ) * (b : ℝ) ^ 2 := by exact_mod_cast hcond
          have h3 : Real.sqrt (M : ℝ) < Real.sqrt ((a : ℝ) * (b : ℝ) ^ 2) :=
            Real.sqrt_lt_sqrt (by positivity) h2
          rw [Real.sqrt_mul (le_of_lt ha0), Real.sqrt_sq (le_of_lt hb0)] at h3
          rw [hY, div_lt_iff₀ (Real.sqrt_pos.mpr ha0)]
          linarith [h3]
        have hKb : K ≤ b := by
          rw [hKdef]
          by_contra hcon
          push Not at hcon
          have h1 : ((b : ℕ) : ℝ) ≤ (⌊Y⌋₊ : ℝ) := by
            exact_mod_cast (by omega : b ≤ ⌊Y⌋₊)
          have h2 : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (le_of_lt hYpos)
          linarith
        exact Finset.mem_Icc.mpr ⟨hKb, hbN⟩
      have hbsum : (∑ b ∈ (Finset.Icc 1 N).filter (fun b => M < a * b ^ 2),
            1 / (b : ℝ) ^ 2) ≤ 2 / Y := by
        calc (∑ b ∈ (Finset.Icc 1 N).filter (fun b => M < a * b ^ 2), 1 / (b : ℝ) ^ 2)
            ≤ ∑ b ∈ Finset.Icc K N, 1 / (b : ℝ) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hcont (fun x _ _ => by positivity)
          _ ≤ 2 / (K : ℝ) := sum_inv_sq_Icc_le K N hK1
          _ ≤ 2 / Y := by
              have hYK : Y ≤ (K : ℝ) := by
                rw [hKdef]
                have h1 : Y < (⌊Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Y
                push_cast
                linarith
              exact div_le_div_of_nonneg_left (by norm_num) hYpos hYK
      have hfac : ∀ b : ℕ, F (a, b) = (1 / (a : ℝ) ^ 2) * (1 / (b : ℝ) ^ 2) := by
        intro b
        simp only [hF, one_div]
        rw [mul_inv_rev]
        ring
      calc (∑ b ∈ Finset.Icc 1 N, (if M < a * b ^ 2 then F (a, b) else 0))
          = ∑ b ∈ (Finset.Icc 1 N).filter (fun b => M < a * b ^ 2), F (a, b) := by
            rw [Finset.sum_filter]
        _ = (1 / (a : ℝ) ^ 2) * ∑ b ∈ (Finset.Icc 1 N).filter (fun b => M < a * b ^ 2),
              1 / (b : ℝ) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b _
            rw [hfac b]
        _ ≤ (1 / (a : ℝ) ^ 2) * (2 / Y) :=
            mul_le_mul_of_nonneg_left hbsum (by positivity)
        _ = (2 / Real.sqrt (M : ℝ)) * (1 / ((a : ℝ) * Real.sqrt (a : ℝ))) := by
            have hkey : Real.sqrt (a : ℝ) / (a : ℝ) ^ 2
                = 1 / ((a : ℝ) * Real.sqrt (a : ℝ)) := by
              rw [div_eq_div_iff (by positivity) (by positivity), one_mul]
              have hsq := Real.sq_sqrt ha0.le
              nlinarith [hsq]
            rw [hY]
            have hstep : 2 / (Real.sqrt (M : ℝ) / Real.sqrt (a : ℝ))
                = 2 * Real.sqrt (a : ℝ) / Real.sqrt (M : ℝ) := by
              rw [div_div_eq_mul_div]
            rw [hstep]
            rw [show (1 / (a : ℝ) ^ 2) * (2 * Real.sqrt (a : ℝ) / Real.sqrt (M : ℝ))
                = (2 / Real.sqrt (M : ℝ)) * (Real.sqrt (a : ℝ) / (a : ℝ) ^ 2) by ring]
            rw [hkey]
    calc (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 N,
            (if M < a * b ^ 2 then F (a, b) else 0))
        ≤ ∑ a ∈ Finset.Icc 1 N,
            (2 / Real.sqrt (M : ℝ)) * (1 / ((a : ℝ) * Real.sqrt (a : ℝ))) :=
          Finset.sum_le_sum hinner
      _ = (2 / Real.sqrt (M : ℝ))
            * ∑ a ∈ Finset.Icc 1 N, 1 / ((a : ℝ) * Real.sqrt (a : ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ (2 / Real.sqrt (M : ℝ)) * 3 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact sum_inv_sqrt_mul_le N
      _ = 6 / Real.sqrt (M : ℝ) := by ring
  calc (∑ d ∈ Finset.Icc (M + 1) N, gam d)
      ≤ ∑ d ∈ Finset.Icc (M + 1) N, 1 / ((d : ℝ) * (rad d : ℝ)) := hstep1
    _ ≤ ∑ d ∈ Finset.Icc (M + 1) N, F (φ d) := Finset.sum_le_sum hterm
    _ = ∑ x ∈ (Finset.Icc (M + 1) N).image φ, F x := (Finset.sum_image hinj).symm
    _ ≤ ∑ x ∈ ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter
          (fun p => M < p.1 * p.2 ^ 2), F x :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => by rw [hF]; positivity)
    _ ≤ 6 / Real.sqrt (M : ℝ) := hbound

/-! ## Part 2: the convolution identity and the reindexing -/

/-- Abbreviation for the partial sums of `μ(n)/n`. -/
abbrev MuSum (n : ℕ) : ℝ := Commons.NumberTheory.Moebius.muRecipSum n

/-- The convolution identity `μ/κ = d₀ ∗ (μ/id)` (`d₀(d) = 1/(d·κ(d))`), in the `kappa`
normalisation. -/
lemma mu_kappa_conv (n : ℕ) (hn : 1 ≤ n) :
    (ArithmeticFunction.moebius n : ℝ) / kappa n
      = ∑ d ∈ n.divisors,
          gam d * ((ArithmeticFunction.moebius (n / d) : ℝ) / ((n / d : ℕ) : ℝ)) := by
  rw [mu_div_kappa_eq_mu_div_kap n, ← LzAux.KappaConvIdentity n hn]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have h : gam d = 1 / ((d : ℝ) * kap d) := by rw [gam, one_div]
  rw [h]

/-- **Reindexed form of `Ssum x 1`**: `Σ_{r ≤ x} μ(r)/κ(r) = Σ_{d ≤ x} (1/(d·κ(d)))·M(⌊x/d⌋)`. -/
theorem Ssum_conv (x : ℕ) :
    Ssum x 1 = ∑ d ∈ Finset.Icc 1 x, gam d * MuSum (x / d) := by
  have hfilt : (Finset.Icc 1 x).filter (fun r => Nat.Coprime r 1) = Finset.Icc 1 x := by
    apply Finset.filter_true_of_mem
    intro r _
    exact Nat.coprime_one_right r
  have hdiv : ∀ r ∈ Finset.Icc 1 x,
      r.divisors = (Finset.Icc 1 x).filter (fun d => d ∣ r) := by
    intro r hr
    obtain ⟨hr1, hrx⟩ := Finset.mem_Icc.mp hr
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hdvd, -⟩
      have hd0 : d ≠ 0 := fun h => by
        rw [h] at hdvd
        exact (by omega : r ≠ 0) (Nat.eq_zero_of_zero_dvd hdvd)
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hd0, (Nat.le_of_dvd (by omega) hdvd).trans hrx⟩, hdvd⟩
    · rintro ⟨⟨hd1, -⟩, hdvd⟩
      exact ⟨hdvd, by omega⟩
  unfold Ssum
  rw [hfilt]
  have hpt : ∀ r ∈ Finset.Icc 1 x,
      (ArithmeticFunction.moebius r : ℝ) / kappa r
        = ∑ d ∈ r.divisors,
            gam d * ((ArithmeticFunction.moebius (r / d) : ℝ) / ((r / d : ℕ) : ℝ)) :=
    fun r hr => mu_kappa_conv r (Finset.mem_Icc.mp hr).1
  rw [Finset.sum_congr rfl hpt]
  have hswap : (∑ r ∈ Finset.Icc 1 x, ∑ d ∈ r.divisors,
        gam d * ((ArithmeticFunction.moebius (r / d) : ℝ) / ((r / d : ℕ) : ℝ)))
      = ∑ d ∈ Finset.Icc 1 x, ∑ r ∈ (Finset.Icc 1 x).filter (fun r => d ∣ r),
        gam d * ((ArithmeticFunction.moebius (r / d) : ℝ) / ((r / d : ℕ) : ℝ)) := by
    rw [Finset.sum_congr rfl (fun r hr => by rw [hdiv r hr])]
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  rw [Work.LinnikAreas.Density4.sum_Icc_filter_dvd_reindex x d hd1
      (fun m => gam d * ((ArithmeticFunction.moebius (m / d) : ℝ) / ((m / d : ℕ) : ℝ)))]
  have hd0 : d ≠ 0 := by omega
  have hMu : MuSum (x / d) = ∑ k ∈ Finset.Icc 1 (x / d),
      (ArithmeticFunction.moebius k : ℝ) / (k : ℝ) := rfl
  rw [hMu, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Nat.mul_div_cancel_left k (by omega : 0 < d)]

/-! ## Part 3: auxiliary estimates for the main theorem -/

/-- For `d ≤ √x` and `x ≥ 16`, the logarithmic factor at `⌊x/d⌋` is at least half of that
at `x`. -/
lemma head_sqrt_log_compare (x d : ℕ) (hx : 16 ≤ x) (hd1 : 1 ≤ d) (hd : d ≤ Nat.sqrt x) :
    (1 / 2) * Real.sqrt (Real.log (x : ℝ))
      ≤ Real.sqrt (Real.log (((x / d : ℕ) : ℝ))) := by
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hsq4 : 4 ≤ Real.sqrt (x : ℝ) := by
    have h16 : (16 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg (x : ℝ)]
  have hDle : ((Nat.sqrt x : ℕ) : ℝ) ≤ Real.sqrt (x : ℝ) := by
    have h1 : (((Nat.sqrt x : ℕ) : ℝ)) ^ 2 ≤ (x : ℝ) := by
      exact_mod_cast Nat.sqrt_le' x
    have h2 : (0 : ℝ) ≤ ((Nat.sqrt x : ℕ) : ℝ) := by positivity
    nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg (x : ℝ),
      sq_nonneg (Real.sqrt (x : ℝ) - ((Nat.sqrt x : ℕ) : ℝ))]
  have hdle : (d : ℝ) ≤ Real.sqrt (x : ℝ) := le_trans (by exact_mod_cast hd) hDle
  have hxd : Real.sqrt (x : ℝ) ≤ (x : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hd0]
    calc Real.sqrt (x : ℝ) * (d : ℝ) ≤ Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) :=
          mul_le_mul_of_nonneg_left hdle (Real.sqrt_nonneg _)
      _ = (x : ℝ) := Real.mul_self_sqrt hx0.le
  have hfloor : (x : ℝ) / (d : ℝ) - 1 ≤ ((x / d : ℕ) : ℝ) := by
    have hcast : ((x / d : ℕ) : ℝ) = ⌊(x : ℝ) / (d : ℝ)⌋₊ := by
      rw [Nat.floor_div_natCast (x : ℝ) d, Nat.floor_natCast]
    rw [hcast]
    have := Nat.lt_floor_add_one ((x : ℝ) / (d : ℝ))
    linarith
  have hroot : Real.sqrt (x : ℝ) / 2 ≤ ((x / d : ℕ) : ℝ) := by linarith
  have hlog : Real.log (Real.sqrt (x : ℝ) / 2) ≤ Real.log (((x / d : ℕ) : ℝ)) := by
    apply Real.log_le_log
    · positivity
    · linarith
  rw [Real.log_div (by positivity) (by norm_num), Real.log_sqrt hx0.le] at hlog
  have hlogx : 4 * Real.log 2 ≤ Real.log (x : ℝ) := by
    have h16 : Real.log 16 ≤ Real.log (x : ℝ) :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hx)
    rwa [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow] at h16
  have hquarter : (1 / 4) * Real.log (x : ℝ) ≤ Real.log (((x / d : ℕ) : ℝ)) := by linarith
  have hnn : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ x))
  have hthis := Real.sqrt_le_sqrt hquarter
  have hkey : Real.sqrt ((1 / 4) * Real.log (x : ℝ))
      = (1 / 2) * Real.sqrt (Real.log (x : ℝ)) := by
    have hsq : (1 / 4) * Real.log (x : ℝ)
        = (Real.sqrt (Real.log (x : ℝ)) / 2) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hnn]
      ring
    rw [hsq, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ Real.sqrt (Real.log (x : ℝ)) / 2)]
    ring
  rwa [hkey] at hthis

/-- The factor `1/√(√x)` is dominated by the exponential envelope `exp(-(log x)/4)`. -/
lemma tail_factor (x : ℕ) (hx : 16 ≤ x) :
    1 / Real.sqrt ((Nat.sqrt x : ℕ) : ℝ)
      ≤ 2 * Real.exp (-(Real.log (x : ℝ) / 4)) := by
  have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hD : Real.sqrt (x : ℝ) / 2 ≤ ((Nat.sqrt x : ℕ) : ℝ) := by
    have hlt : Real.sqrt (x : ℝ) < ((Nat.sqrt x : ℕ) : ℝ) + 1 := by
      rw [Real.sqrt_lt' (by positivity : (0 : ℝ) < ((Nat.sqrt x : ℕ) : ℝ) + 1)]
      have hnat : x < (Nat.sqrt x + 1) ^ 2 := Nat.lt_succ_sqrt' x
      exact_mod_cast hnat
    have hsx2 : 2 ≤ Real.sqrt (x : ℝ) := by
      have h4 : (4 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 4 ≤ x)
      nlinarith [Real.sq_sqrt hx0.le, Real.sqrt_nonneg (x : ℝ)]
    linarith
  have h2 : Real.sqrt (Real.sqrt (x : ℝ)) ≤ 2 * Real.sqrt ((Nat.sqrt x : ℕ) : ℝ) := by
    have h1 : Real.sqrt (Real.sqrt (x : ℝ)) ≤ Real.sqrt (2 * ((Nat.sqrt x : ℕ) : ℝ)) := by
      apply Real.sqrt_le_sqrt
      linarith
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at h1
    refine h1.trans ?_
    have h3 : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have h4 : (0 : ℝ) ≤ Real.sqrt ((Nat.sqrt x : ℕ) : ℝ) := Real.sqrt_nonneg _
    nlinarith
  have h3 : Real.exp (-(Real.log (x : ℝ) / 4)) = 1 / Real.sqrt (Real.sqrt (x : ℝ)) := by
    have h4 : Real.log (Real.sqrt (Real.sqrt (x : ℝ))) = Real.log (x : ℝ) / 4 := by
      rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt hx0.le]
      ring
    have h5 : Real.exp (Real.log (x : ℝ) / 4) = Real.sqrt (Real.sqrt (x : ℝ)) := by
      rw [← h4, Real.exp_log (by positivity)]
    rw [Real.exp_neg, h5, one_div]
  have hposS : (0 : ℝ) < Real.sqrt (Real.sqrt (x : ℝ)) :=
    Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hx0)
  have hgoal : (1 : ℝ) / Real.sqrt ((Nat.sqrt x : ℕ) : ℝ)
      = 2 / (2 * Real.sqrt ((Nat.sqrt x : ℕ) : ℝ)) := by ring
  rw [h3, mul_one_div, hgoal]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt ((Nat.sqrt x : ℕ) : ℝ)),
    div_mul_eq_mul_div, le_div_iff₀ hposS]
  linarith [h2]

/-! ## Part 3: the main theorem -/

theorem KMSsumOneDecay : ∃ K c : ℝ, 0 < K ∧ 0 < c ∧ ∀ x : ℕ, |Ssum x 1| ≤ K * Dc c x := by
  obtain ⟨c₁, C₁, hc₁, hC₁, hdec⟩ := Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay
  set M₀ : ℝ := max C₁ 1 with hM₀def
  have hM₀pos : 0 < M₀ := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hdecay : ∀ n : ℕ, 1 ≤ n →
      |MuSum n| ≤ M₀ * Real.exp (-(c₁ * Real.sqrt (Real.log (n : ℝ)))) := by
    intro n hn
    have h := Commons.NumberTheory.Moebius.muRecipSum_decay hc₁ hC₁ hdec n hn
    simpa only [hM₀def, MuSum] using h
  obtain ⟨Cps, hCps, hps⟩ := gam_partial
  refine ⟨Cps * M₀ + 12 * M₀ * Real.exp (c₁ ^ 2 / 16)
      + 15 * Real.exp (c₁ / 4 * Real.sqrt (Real.log 16)) + 1, c₁ / 4, ?_, by positivity, ?_⟩
  · have h1 : (0 : ℝ) ≤ Cps * M₀ := by positivity
    have h2 : (0 : ℝ) ≤ 12 * M₀ * Real.exp (c₁ ^ 2 / 16) := by positivity
    have h3 : (0 : ℝ) ≤ 15 * Real.exp (c₁ / 4 * Real.sqrt (Real.log 16)) := by positivity
    linarith
  · intro x
    rcases Nat.lt_or_ge x 16 with hx | hx
    · -- small case
      have hx15 : x ≤ 15 := by omega
      have hle : |Ssum x 1| ≤ 15 := by
        have h1 : |Ssum x 1| ≤ (x : ℝ) := by
          have hfilt : (Finset.Icc 1 x).filter (fun r => Nat.Coprime r 1) = Finset.Icc 1 x := by
            apply Finset.filter_true_of_mem
            intro r _
            exact Nat.coprime_one_right r
          unfold Ssum
          rw [hfilt]
          calc |∑ r ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius r : ℝ) / kappa r|
              ≤ ∑ r ∈ Finset.Icc 1 x, |(ArithmeticFunction.moebius r : ℝ) / kappa r| :=
                Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ r ∈ Finset.Icc 1 x, (1 : ℝ) := by
                apply Finset.sum_le_sum
                intro r hr
                have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
                have hk1 : 1 ≤ kappa r := by
                  have hr0 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
                  have hprod : 1 ≤ ∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ)) := by
                    apply Finset.one_le_prod₀
                    intro p hp
                    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
                      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
                    have : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
                    linarith
                  rw [kappa]
                  calc (1 : ℝ) = 1 * 1 := (mul_one 1).symm
                    _ ≤ (r : ℝ) * ∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ)) :=
                        mul_le_mul hr0 hprod zero_le_one (by linarith)
                have hmu := Commons.NumberTheory.Moebius.moebius_abs_le_one r
                have hkpos : (0 : ℝ) < kappa r := lt_of_lt_of_le zero_lt_one hk1
                rw [abs_div, abs_of_pos hkpos, div_le_one hkpos]
                linarith
            _ = ((Finset.Icc 1 x).card : ℝ) := by simp
            _ = (x : ℝ) := by
                have hcard : (Finset.Icc 1 x).card = x := by
                  rw [Nat.card_Icc]
                  omega
                rw [hcard]
        exact h1.trans (by exact_mod_cast hx15)
      have hK : 15 * Real.exp (c₁ / 4 * Real.sqrt (Real.log 16))
          ≤ Cps * M₀ + 12 * M₀ * Real.exp (c₁ ^ 2 / 16)
            + 15 * Real.exp (c₁ / 4 * Real.sqrt (Real.log 16)) + 1 := by
        have h1 : (0 : ℝ) ≤ Cps * M₀ := by positivity
        have h2 : (0 : ℝ) ≤ 12 * M₀ * Real.exp (c₁ ^ 2 / 16) := by positivity
        have h3 : (0 : ℝ) ≤ 1 := by norm_num
        linarith
      have hexp : Real.exp (-(c₁ / 4 * Real.sqrt (Real.log 16)))
          ≤ Real.exp (-(c₁ / 4 * Real.sqrt (Real.log (x : ℝ)))) := by
        apply Real.exp_le_exp.mpr
        have hlog : Real.log (x : ℝ) ≤ Real.log 16 := by
          rcases Nat.eq_zero_or_pos x with h0 | hpos
          · rw [h0]
            simp only [Nat.cast_zero, Real.log_zero]
            exact Real.log_nonneg (by norm_num)
          · apply Real.log_le_log (by exact_mod_cast hpos)
            have h2 : (x : ℝ) ≤ 15 := by exact_mod_cast hx15
            linarith
        have hs := Real.sqrt_le_sqrt hlog
        have h1 : 0 ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_nonneg _
        have h2 : 0 ≤ Real.sqrt (Real.log 16) := Real.sqrt_nonneg _
        nlinarith [hc₁]
      have hKpos : (0 : ℝ) ≤ Cps * M₀ + 12 * M₀ * Real.exp (c₁ ^ 2 / 16)
          + 15 * Real.exp (c₁ / 4 * Real.sqrt (Real.log 16)) + 1 := by
        have h1 : (0 : ℝ) ≤ Cps * M₀ := by positivity
        have h2 : (0 : ℝ) ≤ 12 * M₀ * Real.exp (c₁ ^ 2 / 16) := by positivity
        have h3 : (0 : ℝ) ≤ 15 * Real.exp (c₁ / 4 * Real.sqrt (Real.log 16)) := by positivity
        linarith
      calc |Ssum x 1| ≤ 15 := hle
        _ = 15 * Real.exp (c₁ / 4 * Real.sqrt (Real.log 16))
              * Real.exp (-(c₁ / 4 * Real.sqrt (Real.log 16))) := by
              rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
        _ ≤ (Cps * M₀ + 12 * M₀ * Real.exp (c₁ ^ 2 / 16)
              + 15 * Real.exp (c₁ / 4 * Real.sqrt (Real.log 16)) + 1)
              * Real.exp (-(c₁ / 4 * Real.sqrt (Real.log (x : ℝ)))) :=
              mul_le_mul hK hexp (Real.exp_nonneg _) hKpos
        _ = (Cps * M₀ + 12 * M₀ * Real.exp (c₁ ^ 2 / 16)
              + 15 * Real.exp (c₁ / 4 * Real.sqrt (Real.log 16)) + 1) * Dc (c₁ / 4) x := rfl
    · -- main case
      have hx16 : 16 ≤ x := hx
      have hx0 : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
      have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
      set L : ℝ := Real.sqrt (Real.log (x : ℝ)) with hLdef
      have hlogxnn : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg hx1
      have hL2 : L ^ 2 = Real.log (x : ℝ) := Real.sq_sqrt hlogxnn
      have hLnn : 0 ≤ L := Real.sqrt_nonneg _
      set D : ℕ := Nat.sqrt x with hDdef
      have hD1 : 1 ≤ D := Nat.le_sqrt.mpr (by omega)
      have hDx : D ≤ x := Nat.sqrt_le_self x
      rw [Ssum_conv x]
      have hsplit : ∀ f : ℕ → ℝ, (∑ d ∈ Finset.Icc 1 x, f d)
          = (∑ d ∈ Finset.Icc 1 D, f d) + ∑ d ∈ Finset.Icc (D + 1) x, f d := by
        intro f
        have hset : Finset.Icc 1 x = Finset.Icc 1 D ∪ Finset.Icc (D + 1) x := by
          ext k
          simp only [Finset.mem_Icc, Finset.mem_union]
          omega
        rw [hset, Finset.sum_union]
        exact Finset.disjoint_left.mpr (fun a ha hb => by
          simp only [Finset.mem_Icc] at ha hb
          omega)
      have hb1 : ∀ d ∈ Finset.Icc 1 D, |MuSum (x / d)| ≤ M₀ * Real.exp (-(c₁ / 2 * L)) := by
        intro d hd
        obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
        have hdx : d ≤ x := hdD.trans hDx
        have hcase : 1 ≤ x / d := Nat.div_pos hdx (by omega)
        have hcmp := head_sqrt_log_compare x d hx16 hd1 hdD
        have hdec_d := hdecay (x / d) hcase
        have hthis : Real.exp (-(c₁ * Real.sqrt (Real.log ((x / d : ℕ) : ℝ))))
            ≤ Real.exp (-(c₁ / 2 * L)) := by
          apply Real.exp_le_exp.mpr
          have h2 := mul_le_mul_of_nonneg_left hcmp hc₁.le
          rw [hLdef]
          linarith
        exact hdec_d.trans (mul_le_mul_of_nonneg_left hthis hM₀pos.le)
      have hpart1 : (∑ d ∈ Finset.Icc 1 D, gam d * |MuSum (x / d)|)
          ≤ Cps * M₀ * Real.exp (-(c₁ / 2 * L)) := by
        calc (∑ d ∈ Finset.Icc 1 D, gam d * |MuSum (x / d)|)
            ≤ ∑ d ∈ Finset.Icc 1 D, gam d * (M₀ * Real.exp (-(c₁ / 2 * L))) := by
              apply Finset.sum_le_sum
              intro d hd
              exact mul_le_mul_of_nonneg_left (hb1 d hd) (gam_nonneg d)
          _ = (∑ d ∈ Finset.Icc 1 D, gam d) * (M₀ * Real.exp (-(c₁ / 2 * L))) := by
              rw [Finset.sum_mul]
          _ ≤ Cps * (M₀ * Real.exp (-(c₁ / 2 * L))) :=
              mul_le_mul_of_nonneg_right (hps D) (by positivity)
          _ = Cps * M₀ * Real.exp (-(c₁ / 2 * L)) := by ring
      have hb2 : ∀ d ∈ Finset.Icc (D + 1) x, |MuSum (x / d)| ≤ M₀ := by
        intro d hd
        obtain ⟨hdlo, hdx⟩ := Finset.mem_Icc.mp hd
        have hcase : 1 ≤ x / d := Nat.div_pos hdx (by omega)
        have hdec_d := hdecay (x / d) hcase
        have hexp1 : Real.exp (-(c₁ * Real.sqrt (Real.log ((x / d : ℕ) : ℝ)))) ≤ 1 := by
          rw [Real.exp_le_one_iff]
          exact neg_nonpos.mpr (mul_nonneg hc₁.le (Real.sqrt_nonneg _))
        calc |MuSum (x / d)|
            ≤ M₀ * Real.exp (-(c₁ * Real.sqrt (Real.log ((x / d : ℕ) : ℝ)))) := hdec_d
          _ ≤ M₀ * 1 := mul_le_mul_of_nonneg_left hexp1 hM₀pos.le
          _ = M₀ := mul_one _
      have hpart2 : (∑ d ∈ Finset.Icc (D + 1) x, gam d * |MuSum (x / d)|)
          ≤ 12 * M₀ * Real.exp (-(L ^ 2 / 4)) := by
        have htail : (∑ d ∈ Finset.Icc (D + 1) x, gam d) ≤ 6 / Real.sqrt (D : ℝ) := by
          have h := gam_tail D x hD1
          simpa only [hDdef] using h
        calc (∑ d ∈ Finset.Icc (D + 1) x, gam d * |MuSum (x / d)|)
            ≤ ∑ d ∈ Finset.Icc (D + 1) x, gam d * M₀ := by
              apply Finset.sum_le_sum
              intro d hd
              exact mul_le_mul_of_nonneg_left (hb2 d hd) (gam_nonneg d)
          _ = (∑ d ∈ Finset.Icc (D + 1) x, gam d) * M₀ := by rw [Finset.sum_mul]
          _ ≤ (6 / Real.sqrt (D : ℝ)) * M₀ := mul_le_mul_of_nonneg_right htail hM₀pos.le
          _ ≤ (12 * Real.exp (-(L ^ 2 / 4))) * M₀ := by
              apply mul_le_mul_of_nonneg_right _ hM₀pos.le
              have hf : 1 / Real.sqrt ((Nat.sqrt x : ℕ) : ℝ)
                  ≤ 2 * Real.exp (-(Real.log (x : ℝ) / 4)) := tail_factor x hx16
              have h6 : 6 / Real.sqrt (D : ℝ) = 6 * (1 / Real.sqrt ((Nat.sqrt x : ℕ) : ℝ)) := by
                rw [hDdef]
                ring
              have h7 : 6 * (2 * Real.exp (-(Real.log (x : ℝ) / 4)))
                  = 12 * Real.exp (-(L ^ 2 / 4)) := by
                rw [hL2]
                ring
              calc 6 / Real.sqrt (D : ℝ) = 6 * (1 / Real.sqrt ((Nat.sqrt x : ℕ) : ℝ)) := h6
                _ ≤ 6 * (2 * Real.exp (-(Real.log (x : ℝ) / 4))) :=
                    mul_le_mul_of_nonneg_left hf (by norm_num)
                _ = 12 * Real.exp (-(L ^ 2 / 4)) := h7
          _ = 12 * M₀ * Real.exp (-(L ^ 2 / 4)) := by ring
      have hAbs : |∑ d ∈ Finset.Icc 1 x, gam d * MuSum (x / d)|
          ≤ ∑ d ∈ Finset.Icc 1 x, gam d * |MuSum (x / d)| := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        apply Finset.sum_congr rfl
        intro d _
        rw [abs_mul, abs_of_nonneg (gam_nonneg d)]
      have hmain : |∑ d ∈ Finset.Icc 1 x, gam d * MuSum (x / d)|
          ≤ (Cps * M₀ + 12 * M₀ * Real.exp (c₁ ^ 2 / 16)) * Real.exp (-(c₁ / 4 * L)) := by
        rw [hsplit (fun d => gam d * |MuSum (x / d)|)] at hAbs
        have e1 : Cps * M₀ * Real.exp (-(c₁ / 2 * L))
            ≤ Cps * M₀ * Real.exp (-(c₁ / 4 * L)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Real.exp_le_exp.mpr
          nlinarith [hc₁, hLnn]
        have e2 : 12 * M₀ * Real.exp (-(L ^ 2 / 4))
            ≤ 12 * M₀ * Real.exp (c₁ ^ 2 / 16) * Real.exp (-(c₁ / 4 * L)) := by
          have hkey : -(L ^ 2 / 4) ≤ c₁ ^ 2 / 16 - (c₁ / 4) * L := by
            nlinarith [sq_nonneg (L / 2 - c₁ / 4)]
          calc 12 * M₀ * Real.exp (-(L ^ 2 / 4))
              ≤ 12 * M₀ * Real.exp (c₁ ^ 2 / 16 - (c₁ / 4) * L) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact Real.exp_le_exp.mpr hkey
            _ = 12 * M₀ * Real.exp (c₁ ^ 2 / 16) * Real.exp (-(c₁ / 4 * L)) := by
                rw [Real.exp_sub]
                have hneg : Real.exp (-(c₁ / 4 * L)) = (Real.exp (c₁ / 4 * L))⁻¹ :=
                  Real.exp_neg _
                rw [hneg]
                ring
        calc |∑ d ∈ Finset.Icc 1 x, gam d * MuSum (x / d)|
            ≤ (∑ d ∈ Finset.Icc 1 D, gam d * |MuSum (x / d)|)
              + ∑ d ∈ Finset.Icc (D + 1) x, gam d * |MuSum (x / d)| := hAbs
          _ ≤ Cps * M₀ * Real.exp (-(c₁ / 2 * L)) + 12 * M₀ * Real.exp (-(L ^ 2 / 4)) :=
              add_le_add hpart1 hpart2
          _ ≤ (Cps * M₀ + 12 * M₀ * Real.exp (c₁ ^ 2 / 16)) * Real.exp (-(c₁ / 4 * L)) := by
              rw [add_mul]
              exact add_le_add e1 e2
      have hDc : Dc (c₁ / 4) x = Real.exp (-(c₁ / 4 * L)) := by rw [Dc, hLdef]
      rw [hDc]
      refine hmain.trans ?_
      apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
      have h3 : (0 : ℝ) ≤ 15 * Real.exp (c₁ / 4 * Real.sqrt (Real.log 16)) := by positivity
      have h4 : (0 : ℝ) ≤ 1 := by norm_num
      linarith

end

end Work.ZeroDensity.Jutila.LzDiffAux
