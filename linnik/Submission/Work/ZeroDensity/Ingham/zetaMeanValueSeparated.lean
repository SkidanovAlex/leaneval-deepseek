import Mathlib
import Submission.Work.ZeroDensity.Montgomery.mvtDefs
import Submission.Work.ZeroDensity.Montgomery.mvtSpread
import Submission.Work.ZeroDensity.Montgomery.gallagherSeparated
import Submission.Work.ZeroDensity.Montgomery.cpow_neg_sigma_add_it
import Submission.Work.ZeroDensity.Montgomery.sumIcc_byParts
import Submission.Work.ZeroDensity.Montgomery.countCongLe
import Submission.Work.ZeroDensity.Ingham.dirPolySeparatedMVT
import Submission.Work.ZeroDensity.Ingham.dirPolySigmaReduction
import Submission.Work.ZeroDensity.Ingham.arithWeightSum

namespace Work.ZeroDensity.Ingham

open scoped Classical BigOperators
open MeasureTheory

/-- The tail Dirichlet polynomial `t ↦ ∑_{2 ≤ n ≤ k} b n · n^{-it}`. -/
private noncomputable def tailPoly (b : ℕ → ℂ) (k : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 2 k, b n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))

/-- The tail `∑_{2 ≤ n ≤ k}` written as a `∑_{1 ≤ n ≤ k}` with the `n = 1` coefficient killed. -/
private lemma tailPoly_eq_trunc (b : ℕ → ℂ) (k : ℕ) (hk : 1 ≤ k) (t : ℝ) :
    tailPoly b k t
      = ∑ n ∈ Finset.Icc 1 k, (if n = 1 then 0 else b n) * (n : ℂ) ^ (-((t : ℂ) * Complex.I)) := by
  rw [tailPoly]
  have hset : Finset.Icc 1 k = insert 1 (Finset.Icc 2 k) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
  rw [hset, Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  have hzero : (if (1 : ℕ) = 1 then (0 : ℂ) else b 1) * ((1 : ℕ) : ℂ) ^ (-((t : ℂ) * Complex.I)) = 0 := by
    simp
  rw [hzero, zero_add]
  apply Finset.sum_congr rfl
  intro x hx
  have hx1 : x ≠ 1 := by have := (Finset.mem_Icc.mp hx).1; omega
  rw [if_neg hx1]

/-- **Mean value bound for Dirichlet polynomials at separated points with arbitrary real parts**
(Montgomery–Vaughan (26.26), the case `q = 1`).  There is an absolute `C > 0` such that for
`T ≥ 2`, `δ > 0`, `N ≥ 1`, arbitrary coefficients `b : ℕ → ℂ` and a `δ`-separated set of points
`(σ_r, t_r)` with `σ_r ≥ 0`, `|t_r| ≤ T`,

`Σ_r ‖Σ_{n≤N} b_n n^{-(σ_r + i t_r)}‖²
   ≤ C (log 2N + 1/δ)(T + N) Σ_{n≤N} ‖b_n‖² (1 + log 2N / log 2n)`.

The real parts `σ_r` are arbitrary non-negative reals: this is the form used in the large-values
counts of the zero-density estimates. -/
theorem zetaMeanValueSeparated :
    ∃ C : ℝ, 0 < C ∧ ∀ (T δ : ℝ), 2 ≤ T → 0 < δ → ∀ (N : ℕ), 1 ≤ N →
      ∀ (b : ℕ → ℂ) (s : Finset (ℝ × ℝ)),
        (∀ p ∈ s, 0 ≤ p.1) → (∀ p ∈ s, -T ≤ p.2 ∧ p.2 ≤ T) →
        (∀ p ∈ s, ∀ p' ∈ s, p ≠ p' → δ ≤ |p.2 - p'.2|) →
        (∑ p ∈ s, ‖∑ n ∈ Finset.Icc 1 N,
              b n * (n : ℂ) ^ (-((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))‖ ^ 2)
          ≤ C * (Real.log (2 * (N : ℝ)) + 1 / δ) * (T + (N : ℝ)) *
              ∑ n ∈ Finset.Icc 1 N,
                ‖b n‖ ^ 2 * (1 + Real.log (2 * (N : ℝ)) / Real.log (2 * (n : ℝ))) := by
  obtain ⟨C₁, hC₁pos, hMVT⟩ := dirPolySeparatedMVT
  obtain ⟨C₂, hC₂pos, hRed⟩ := dirPolySigmaReduction
  obtain ⟨C₃, hC₃pos, hArith⟩ := arithWeightSum
  have hC₁nn : 0 ≤ C₁ := le_of_lt hC₁pos
  have hC₂nn : 0 ≤ C₂ := le_of_lt hC₂pos
  have hC₃nn : 0 ≤ C₃ := le_of_lt hC₃pos
  refine ⟨C₁ + C₂ * C₁ * (2 + C₃) + 2, by positivity, ?_⟩
  intro T δ hT hδ N hN b s hσ hTn hsep
  have h1dpos : (0 : ℝ) < 1 / δ := by positivity
  have hTnn : (0 : ℝ) ≤ T := by linarith
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlN : (0 : ℝ) ≤ Real.log (2 * (N : ℝ)) := Real.log_nonneg (by linarith)
  have hcol : (0 : ℝ) ≤ 1 / δ + Real.log (2 * (N : ℝ)) := by linarith
  -- the set of imaginary parts
  set S' : Finset ℝ := s.image (fun p : ℝ × ℝ => p.2) with hS'def
  have hinj : Set.InjOn (fun p : ℝ × ℝ => p.2) ↑s := by
    intro p hp p' hp' heq
    by_contra hne
    have h := hsep p hp p' hp' hne
    change p.2 = p'.2 at heq
    rw [heq, sub_self, abs_zero] at h
    linarith
  have hS'T : ∀ t ∈ S', -T ≤ t ∧ t ≤ T := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    exact hTn p hp
  have hS'sep : ∀ t ∈ S', ∀ t' ∈ S', t ≠ t' → δ ≤ |t - t'| := by
    intro t ht t' ht' hne
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨p', hp', rfl⟩ := Finset.mem_image.mp ht'
    exact hsep p hp p' hp' (fun h => hne (by rw [h]))
  have hreindex : ∀ F : ℝ → ℝ, (∑ t ∈ S', F t) = ∑ p ∈ s, F p.2 := by
    intro F
    have h := Finset.sum_image (f := F) hinj
    simpa [hS'def] using h
  rcases eq_or_lt_of_le hN with hN1 | hN2
  · -- N = 1
    subst hN1
    have hb1nn : (0 : ℝ) ≤ ‖b 1‖ ^ 2 := by positivity
    have hlog2N : Real.log (2 * ((1 : ℕ) : ℝ)) = Real.log 2 := by norm_num
    have hK : C₁ ≤ C₁ + C₂ * C₁ * (2 + C₃) + 2 := by
      have h0 : (0 : ℝ) ≤ C₂ * C₁ * (2 + C₃) := by
        apply mul_nonneg; apply mul_nonneg hC₂nn hC₁nn; linarith
      linarith
    have hKnn : (0 : ℝ) ≤ C₁ + C₂ * C₁ * (2 + C₃) + 2 := by positivity
    have hAnn : (0 : ℝ) ≤ 1 / δ + Real.log (2 * ((1 : ℕ) : ℝ)) := by
      have h1 : (0 : ℝ) ≤ Real.log (2 * ((1 : ℕ) : ℝ)) := by
        rw [hlog2N]; exact Real.log_nonneg (by norm_num)
      linarith
    have hBnn : (0 : ℝ) ≤ T + ((1 : ℕ) : ℝ) := by norm_num; linarith
    have hL : (∑ p ∈ s, ‖∑ n ∈ Finset.Icc 1 1, b n * (n : ℂ) ^ (-((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))‖ ^ 2)
        = ∑ t ∈ S', ‖b 1‖ ^ 2 := by
      rw [hreindex (fun (_ : ℝ) => ‖b 1‖ ^ 2)]
      apply Finset.sum_congr rfl; intro p hp
      simp [Finset.Icc_self]
    rw [hL]
    have hMt := hMVT T δ hT hδ 1 le_rfl (fun (_ : ℕ) => b 1) S' hS'T hS'sep
    have hb1 : (∑ n ∈ Finset.Icc 1 1, ‖(fun (_ : ℕ) => b 1) n‖ ^ 2) = ‖b 1‖ ^ 2 := by
      simp [Finset.Icc_self]
    rw [hb1] at hMt
    have hbridge : (∑ t ∈ S', ‖b 1‖ ^ 2)
        = ∑ t ∈ S', ‖∑ n ∈ Finset.Icc 1 1, (fun (_ : ℕ) => b 1) n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2 := by
      apply Finset.sum_congr rfl; intro t ht
      simp [Finset.Icc_self]
    rw [hbridge]
    refine hMt.trans ?_
    have hsum1 : ‖b 1‖ ^ 2
        ≤ ∑ n ∈ Finset.Icc 1 1, ‖b n‖ ^ 2 * (1 + Real.log (2 * ((1 : ℕ) : ℝ)) / Real.log (2 * (n : ℝ))) := by
      have hmem : (1 : ℕ) ∈ Finset.Icc 1 1 := Finset.mem_Icc.mpr ⟨le_rfl, le_rfl⟩
      have hnn : ∀ n ∈ Finset.Icc 1 1,
          (0 : ℝ) ≤ ‖b n‖ ^ 2 * (1 + Real.log (2 * ((1 : ℕ) : ℝ)) / Real.log (2 * (n : ℝ))) := by
        intro n hn
        have hn1 : n = 1 := by have := Finset.mem_Icc.mp hn; omega
        subst hn1
        have hlog : 0 < Real.log (2 * ((1 : ℕ) : ℝ)) := by rw [hlog2N]; exact Real.log_pos (by norm_num)
        have hw : 0 ≤ 1 + Real.log (2 * ((1 : ℕ) : ℝ)) / Real.log (2 * ((1 : ℕ) : ℝ)) := by
          have := div_nonneg hlog.le hlog.le; linarith
        exact mul_nonneg (by positivity) hw
      have hle := Finset.single_le_sum hnn hmem
      refine le_trans ?_ hle
      have hge1 : (1 : ℝ) ≤ 1 + Real.log (2 * ((1 : ℕ) : ℝ)) / Real.log (2 * ((1 : ℕ) : ℝ)) := by
        have hlog : 0 ≤ Real.log (2 * ((1 : ℕ) : ℝ)) := by rw [hlog2N]; exact Real.log_nonneg (by norm_num)
        have := div_nonneg hlog hlog; linarith
      calc ‖b 1‖ ^ 2 = ‖b 1‖ ^ 2 * 1 := by ring
        _ ≤ ‖b 1‖ ^ 2 * (1 + Real.log (2 * ((1 : ℕ) : ℝ)) / Real.log (2 * ((1 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hge1 (by positivity)
    calc C₁ * (1 / δ + Real.log (2 * ((1 : ℕ) : ℝ))) * (T + ((1 : ℕ) : ℝ)) * ‖b 1‖ ^ 2
        ≤ (C₁ + C₂ * C₁ * (2 + C₃) + 2) * (1 / δ + Real.log (2 * ((1 : ℕ) : ℝ))) *
            (T + ((1 : ℕ) : ℝ)) * ‖b 1‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right _ hb1nn
          apply mul_le_mul_of_nonneg_right _ hBnn
          exact mul_le_mul_of_nonneg_right hK hAnn
      _ ≤ (C₁ + C₂ * C₁ * (2 + C₃) + 2) * (1 / δ + Real.log (2 * ((1 : ℕ) : ℝ))) *
            (T + ((1 : ℕ) : ℝ)) *
            (∑ n ∈ Finset.Icc 1 1, ‖b n‖ ^ 2 * (1 + Real.log (2 * ((1 : ℕ) : ℝ)) / Real.log (2 * (n : ℝ)))) :=
          mul_le_mul_of_nonneg_left hsum1 (mul_nonneg (mul_nonneg hKnn hAnn) hBnn)
      _ = (C₁ + C₂ * C₁ * (2 + C₃) + 2) * (Real.log (2 * ((1 : ℕ) : ℝ)) + 1 / δ) *
            (T + ((1 : ℕ) : ℝ)) *
            (∑ n ∈ Finset.Icc 1 1, ‖b n‖ ^ 2 * (1 + Real.log (2 * ((1 : ℕ) : ℝ)) / Real.log (2 * (n : ℝ)))) := by
          ring
  · -- main case: 2 ≤ N
    have hN2' : 2 ≤ N := by omega
    have hb1nn : (0 : ℝ) ≤ ‖b 1‖ ^ 2 := by positivity
    set V : ℝ := ∑ n ∈ Finset.Icc 1 N,
        ‖b n‖ ^ 2 * (1 + Real.log (2 * (N : ℝ)) / Real.log (2 * (n : ℝ))) with hVdef
    have hlognn : ∀ n ∈ Finset.Icc 1 N, (0 : ℝ) ≤ Real.log (2 * (n : ℝ)) := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      exact Real.log_nonneg (by
        have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
        linarith)
    have hVnn : 0 ≤ V := by
      rw [hVdef]
      apply Finset.sum_nonneg; intro n hn
      have hw : (0 : ℝ) ≤ 1 + Real.log (2 * (N : ℝ)) / Real.log (2 * (n : ℝ)) := by
        have := div_nonneg hlN (hlognn n hn); linarith
      exact mul_nonneg (by positivity) hw
    have hV1 : ‖b 1‖ ^ 2 ≤ V := by
      have hmem : 1 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN⟩
      have hnn : ∀ n ∈ Finset.Icc 1 N,
          (0 : ℝ) ≤ ‖b n‖ ^ 2 * (1 + Real.log (2 * (N : ℝ)) / Real.log (2 * (n : ℝ))) := by
        intro n hn
        have hw : (0 : ℝ) ≤ 1 + Real.log (2 * (N : ℝ)) / Real.log (2 * (n : ℝ)) := by
          have := div_nonneg hlN (hlognn n hn); linarith
        exact mul_nonneg (by positivity) hw
      have hle := Finset.single_le_sum hnn hmem
      rw [hVdef]
      refine le_trans ?_ hle
      have hge1 : (1 : ℝ) ≤ 1 + Real.log (2 * (N : ℝ)) / Real.log (2 * ((1 : ℕ) : ℝ)) := by
        have hlog2 : (0 : ℝ) ≤ Real.log (2 * ((1 : ℕ) : ℝ)) := Real.log_nonneg (by norm_num)
        have := div_nonneg hlN hlog2; linarith
      calc ‖b 1‖ ^ 2 = ‖b 1‖ ^ 2 * 1 := by ring
        _ ≤ ‖b 1‖ ^ 2 * (1 + Real.log (2 * (N : ℝ)) / Real.log (2 * ((1 : ℕ) : ℝ))) :=
            mul_le_mul_of_nonneg_left hge1 (by positivity)
    have hVN : (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) ≤ V := by
      rw [hVdef]
      apply Finset.sum_le_sum; intro n hn
      have hw : (1 : ℝ) ≤ 1 + Real.log (2 * (N : ℝ)) / Real.log (2 * (n : ℝ)) := by
        have := div_nonneg hlN (hlognn n hn); linarith
      calc ‖b n‖ ^ 2 = ‖b n‖ ^ 2 * 1 := by ring
        _ ≤ ‖b n‖ ^ 2 * (1 + Real.log (2 * (N : ℝ)) / Real.log (2 * (n : ℝ))) :=
            mul_le_mul_of_nonneg_left hw (by positivity)
    -- the tail bound for `1 ≤ k ≤ N`
    have hMTk : ∀ k, 1 ≤ k → k ≤ N →
        (∑ t ∈ S', ‖tailPoly b k t‖ ^ 2)
          ≤ C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * (∑ n ∈ Finset.Icc 1 k, ‖b n‖ ^ 2) := by
      intro k hk1 hkN
      have hMt := hMVT T δ hT hδ k hk1 (fun n => if n = 1 then 0 else b n) S' hS'T hS'sep
      have hbridge : (∑ t ∈ S', ‖tailPoly b k t‖ ^ 2)
          = ∑ t ∈ S', ‖∑ n ∈ Finset.Icc 1 k,
              (fun n => if n = 1 then 0 else b n) n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2 := by
        apply Finset.sum_congr rfl; intro t ht
        rw [tailPoly_eq_trunc b k hk1 t]
      rw [hbridge]
      refine hMt.trans ?_
      have hWk : (∑ n ∈ Finset.Icc 1 k, ‖(fun n => if n = 1 then 0 else b n) n‖ ^ 2)
          ≤ ∑ n ∈ Finset.Icc 1 k, ‖b n‖ ^ 2 := by
        apply Finset.sum_le_sum; intro n hn
        by_cases hn1 : n = 1
        · simp [hn1]
        · simp [hn1]
      have hkNR : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
      have hlogk : Real.log (2 * (k : ℝ)) ≤ Real.log (2 * (N : ℝ)) :=
        Real.log_le_log (by positivity) (by linarith)
      have hc1 : (1 / δ + Real.log (2 * (k : ℝ))) ≤ (1 / δ + Real.log (2 * (N : ℝ))) := by linarith
      have hc2 : (T + (k : ℝ)) ≤ (T + (N : ℝ)) := by linarith
      have hn1 : (0 : ℝ) ≤ T + (k : ℝ) := by
        have : (0 : ℝ) ≤ (k : ℝ) := by positivity
        linarith
      have hn3 : (0 : ℝ) ≤ T + (N : ℝ) := by linarith
      have hA1 := mul_le_mul hc1 hc2 hn1 hcol
      have hA2 := mul_le_mul hA1 hWk (by positivity) (mul_nonneg hcol hn3)
      calc C₁ * (1 / δ + Real.log (2 * (k : ℝ))) * (T + (k : ℝ)) *
            (∑ n ∈ Finset.Icc 1 k, ‖(fun n => if n = 1 then 0 else b n) n‖ ^ 2)
          = C₁ * ((1 / δ + Real.log (2 * (k : ℝ))) * (T + (k : ℝ)) *
              (∑ n ∈ Finset.Icc 1 k, ‖(fun n => if n = 1 then 0 else b n) n‖ ^ 2)) := by ring
        _ ≤ C₁ * ((1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) *
              (∑ n ∈ Finset.Icc 1 k, ‖b n‖ ^ 2)) := mul_le_mul_of_nonneg_left hA2 hC₁nn
        _ = C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * (∑ n ∈ Finset.Icc 1 k, ‖b n‖ ^ 2) := by ring
    have hA : (∑ p ∈ s, ‖b 1‖ ^ 2) ≤ C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * V := by
      rw [(hreindex (fun (_ : ℝ) => ‖b 1‖ ^ 2)).symm]
      have hMt := hMVT T δ hT hδ 1 le_rfl (fun (_ : ℕ) => b 1) S' hS'T hS'sep
      have hb1 : (∑ n ∈ Finset.Icc 1 1, ‖(fun (_ : ℕ) => b 1) n‖ ^ 2) = ‖b 1‖ ^ 2 := by
        simp [Finset.Icc_self]
      rw [hb1] at hMt
      have hbridge : (∑ t ∈ S', ‖b 1‖ ^ 2)
          = ∑ t ∈ S', ‖∑ n ∈ Finset.Icc 1 1, (fun (_ : ℕ) => b 1) n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2 := by
        apply Finset.sum_congr rfl; intro t ht
        simp [Finset.Icc_self]
      rw [hbridge]
      have hlog2 : Real.log (2 * ((1 : ℕ) : ℝ)) ≤ Real.log (2 * (N : ℝ)) := by
        apply Real.log_le_log (by norm_num)
        have h1N : ((1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
        linarith
      have hcoef : C₁ * (1 / δ + Real.log (2 * ((1 : ℕ) : ℝ))) * (T + ((1 : ℕ) : ℝ))
          ≤ C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) := by
        have h1 : (1 / δ + Real.log (2 * ((1 : ℕ) : ℝ))) ≤ (1 / δ + Real.log (2 * (N : ℝ))) :=
          add_le_add_right hlog2 (1 / δ)
        have h2 : (T + ((1 : ℕ) : ℝ)) ≤ (T + (N : ℝ)) :=
          add_le_add_right (by exact_mod_cast hN : ((1 : ℕ) : ℝ) ≤ (N : ℝ)) T
        have hn1 : (0 : ℝ) ≤ T + ((1 : ℕ) : ℝ) := by norm_num; linarith
        exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC₁nn) h2 hn1 (mul_nonneg hC₁nn hcol)
      have hcoefnn : (0 : ℝ) ≤ C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) :=
        mul_nonneg (mul_nonneg hC₁nn hcol) (by linarith [hTnn, hNR])
      calc (∑ t ∈ S', ‖∑ n ∈ Finset.Icc 1 1, (fun (_ : ℕ) => b 1) n * (n : ℂ) ^ (-((t : ℂ) * Complex.I))‖ ^ 2)
          ≤ C₁ * (1 / δ + Real.log (2 * ((1 : ℕ) : ℝ))) * (T + ((1 : ℕ) : ℝ)) * ‖b 1‖ ^ 2 := hMt
        _ ≤ C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * V :=
            mul_le_mul hcoef hV1 hb1nn hcoefnn
    have hB : (∑ p ∈ s, ‖tailPoly b N p.2‖ ^ 2) ≤ C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * V := by
      rw [(hreindex (fun t => ‖tailPoly b N t‖ ^ 2)).symm]
      exact (hMTk N hN le_rfl).trans
        (mul_le_mul_of_nonneg_left hVN (mul_nonneg (mul_nonneg hC₁nn hcol) (by linarith [hTnn, hNR])))
    have hC : (∑ p ∈ s, ∑ k ∈ Finset.Icc 2 (N - 1), ‖tailPoly b k p.2‖ ^ 2 / ((k : ℝ) * Real.log (k : ℝ)))
        ≤ C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * (C₃ * V) := by
      rw [Finset.sum_comm]
      have hperk : ∀ k ∈ Finset.Icc 2 (N - 1),
          (∑ p ∈ s, ‖tailPoly b k p.2‖ ^ 2 / ((k : ℝ) * Real.log (k : ℝ)))
          ≤ (C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) *
              (∑ n ∈ Finset.Icc 1 k, ‖b n‖ ^ 2)) / ((k : ℝ) * Real.log (k : ℝ)) := by
        intro k hk
        obtain ⟨hk2, hkN1⟩ := Finset.mem_Icc.mp hk
        have hkN : k ≤ N := by omega
        have hk1 : 1 ≤ k := by omega
        have hkw : (0 : ℝ) < (k : ℝ) * Real.log (k : ℝ) := by
          have hk2R : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
          have : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
          positivity
        have htail := hMTk k hk1 hkN
        rw [← Finset.sum_div, (hreindex (fun t => ‖tailPoly b k t‖ ^ 2)).symm]
        exact div_le_div_of_nonneg_right htail hkw.le
      calc (∑ k ∈ Finset.Icc 2 (N - 1), ∑ p ∈ s, ‖tailPoly b k p.2‖ ^ 2 / ((k : ℝ) * Real.log (k : ℝ)))
          ≤ ∑ k ∈ Finset.Icc 2 (N - 1),
              (C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) *
                (∑ n ∈ Finset.Icc 1 k, ‖b n‖ ^ 2)) / ((k : ℝ) * Real.log (k : ℝ)) :=
            Finset.sum_le_sum hperk
        _ = C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) *
              (∑ k ∈ Finset.Icc 2 (N - 1), (∑ n ∈ Finset.Icc 1 k, ‖b n‖ ^ 2) / ((k : ℝ) * Real.log (k : ℝ))) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro k hk
            rw [mul_div_assoc]
        _ ≤ C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * (C₃ * V) := by
            have hAr := hArith N hN2' b
            rw [hVdef]
            exact mul_le_mul_of_nonneg_left hAr (mul_nonneg (mul_nonneg hC₁nn hcol) (by linarith [hTnn, hNR]))
    -- pointwise reduction
    have hpt : ∀ p ∈ s, ‖∑ n ∈ Finset.Icc 1 N, b n * (n : ℂ) ^ (-((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))‖ ^ 2
        ≤ C₂ * (‖b 1‖ ^ 2 + ‖tailPoly b N p.2‖ ^ 2
            + ∑ k ∈ Finset.Icc 2 (N - 1), ‖tailPoly b k p.2‖ ^ 2 / ((k : ℝ) * Real.log (k : ℝ))) := by
      intro p hp
      have h := hRed N hN2' b p.1 p.2 (hσ p hp)
      simpa only [tailPoly] using h
    have hsum := Finset.sum_le_sum hpt
    have hsumeq : (∑ p ∈ s, C₂ * (‖b 1‖ ^ 2 + ‖tailPoly b N p.2‖ ^ 2
            + ∑ k ∈ Finset.Icc 2 (N - 1), ‖tailPoly b k p.2‖ ^ 2 / ((k : ℝ) * Real.log (k : ℝ))))
        = C₂ * ((∑ p ∈ s, ‖b 1‖ ^ 2) + (∑ p ∈ s, ‖tailPoly b N p.2‖ ^ 2)
            + (∑ p ∈ s, ∑ k ∈ Finset.Icc 2 (N - 1), ‖tailPoly b k p.2‖ ^ 2 / ((k : ℝ) * Real.log (k : ℝ)))) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have hlast : C₂ * ((∑ p ∈ s, ‖b 1‖ ^ 2) + (∑ p ∈ s, ‖tailPoly b N p.2‖ ^ 2)
          + (∑ p ∈ s, ∑ k ∈ Finset.Icc 2 (N - 1), ‖tailPoly b k p.2‖ ^ 2 / ((k : ℝ) * Real.log (k : ℝ))))
        ≤ C₂ * (C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * V
            + C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * V
            + C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * (C₃ * V)) := by
      apply mul_le_mul_of_nonneg_left _ hC₂nn
      linarith [hA, hB, hC]
    have hfin : C₂ * (C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * V
            + C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * V
            + C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * (C₃ * V))
        ≤ (C₁ + C₂ * C₁ * (2 + C₃) + 2) * (Real.log (2 * (N : ℝ)) + 1 / δ) * (T + (N : ℝ)) * V := by
      have hkey : C₂ * (C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * V
            + C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * V
            + C₁ * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * (C₃ * V))
          = (C₂ * C₁ * (2 + C₃)) * ((1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * V) := by ring
      rw [hkey]
      have hbase_nn : (0 : ℝ) ≤ (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * V :=
        mul_nonneg (mul_nonneg hcol (by linarith [hTnn, hNR])) hVnn
      have hK : C₂ * C₁ * (2 + C₃) ≤ C₁ + C₂ * C₁ * (2 + C₃) + 2 := by linarith [hC₁nn]
      have hcomm : (Real.log (2 * (N : ℝ)) + 1 / δ) = (1 / δ + Real.log (2 * (N : ℝ))) := by ring
      rw [hcomm]
      calc (C₂ * C₁ * (2 + C₃)) * ((1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * V)
          ≤ (C₁ + C₂ * C₁ * (2 + C₃) + 2) * ((1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * V) :=
            mul_le_mul_of_nonneg_right hK hbase_nn
        _ = (C₁ + C₂ * C₁ * (2 + C₃) + 2) * (1 / δ + Real.log (2 * (N : ℝ))) * (T + (N : ℝ)) * V := by ring
    rw [hVdef]
    calc (∑ p ∈ s, ‖∑ n ∈ Finset.Icc 1 N, b n * (n : ℂ) ^ (-((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))‖ ^ 2)
        ≤ ∑ p ∈ s, C₂ * (‖b 1‖ ^ 2 + ‖tailPoly b N p.2‖ ^ 2
            + ∑ k ∈ Finset.Icc 2 (N - 1), ‖tailPoly b k p.2‖ ^ 2 / ((k : ℝ) * Real.log (k : ℝ))) := hsum
      _ = C₂ * ((∑ p ∈ s, ‖b 1‖ ^ 2) + (∑ p ∈ s, ‖tailPoly b N p.2‖ ^ 2)
            + (∑ p ∈ s, ∑ k ∈ Finset.Icc 2 (N - 1), ‖tailPoly b k p.2‖ ^ 2 / ((k : ℝ) * Real.log (k : ℝ)))) := hsumeq
      _ ≤ (C₁ + C₂ * C₁ * (2 + C₃) + 2) * (Real.log (2 * (N : ℝ)) + 1 / δ) * (T + (N : ℝ)) *
              ∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2 * (1 + Real.log (2 * (N : ℝ)) / Real.log (2 * (n : ℝ))) := by
            linarith [hlast, hfin]

end Work.ZeroDensity.Ingham
