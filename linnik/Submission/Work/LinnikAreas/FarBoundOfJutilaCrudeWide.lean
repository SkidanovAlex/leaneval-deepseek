import Mathlib
import Submission.Work.LinnikAreas.FarBoundOfJutilaMontgomery
import Submission.Work.LinnikAreas.JMAuxSh.ShAux
import Submission.Work.LinnikAreas.FarBoundJM
import Submission.Work.LinnikAreas.CrudeWideDefs
import Submission.Work.LinnikAreas.CellMultLeBoundJMcw
import Submission.Work.LinnikAreas.MsumBoundJMcw

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

set_option maxHeartbeats 2000000

namespace Work.LinnikAreas

open Work.LinnikContract

/-- **The far-zero mass bound** from the wide-range crude log-free family estimate.  This is
`Work.LinnikAreas.finset_boundJMsh` with the Montgomery middle-branch term deleted and the
branch-1 constant inflated (the branch-1 `R`-power is now `-9/10` instead of `-3/2`, because the
crude exponent `(24/5+1/1000)·(1021/5000) = 0.98036` only fits `CellLayerKsum`'s hypothesis
`θ ≤ 11/10`). -/
lemma finset_boundJMcw (q : ℕ) [NeZero q] (hq : 2 ≤ q) (R : ℕ) (hR : 1 ≤ R)
    (CJ c0 : ℝ) (hCJ : 0 < CJ) (hc0 : 0 < c0)
    (hfamJ : ∀ σ T : ℝ, (1:ℝ) - 1021/5000 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ σ T
        ≤ CJ * ((q:ℝ) * T) ^ (((24:ℝ)/5 + 1/1000) * (1 - σ)))
    (hball : ∀ {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N), χ ≠ 1 → χ.IsPrimitive →
      ∀ (a : ℂ) (ρ : ℝ), 1 ≤ ρ →
      (∑ᶠ u : ℂ, (((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
          (Metric.closedBall a ρ)) u : ℤ) : ℝ))
        ≤ c0 * (ρ + 1) * (Real.log (‖a‖ + ρ + 2) + Real.log (N:ℝ) + 2))
    (hL : 30000000 ≤ Real.log (q:ℝ))
    (S : Finset (DirichletCharacter ℂ q × ℂ)) :
    farMassSum R (Real.log (q:ℝ)) S
      ≤ 640000 * CJ / ((R:ℝ)^(9/10:ℝ)) + 1920000 * c0 * Real.log (q:ℝ)
          / (q:ℝ)^(29/50000:ℝ) := by
  classical
  set L : ℝ := Real.log (q:ℝ) with hLdef
  have hLpos : 0 < L := by
    rw [hLdef]
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < q))
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  have hL1 : (1:ℝ) ≤ L := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ z ∈ S, z.1 ≠ 1 → ¬ InBox q (R:ℝ) z.2 → zeroMult z.1 z.2 ≠ 0 →
      max (farM L z : ℝ) (farY L z) + 1 ≤ (2:ℝ)^K := by
    refine ⟨S.sup (fun z => Nat.ceil (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))), ?_⟩
    intro z hz _ _ _
    have h1 : Nat.ceil (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))
        ≤ S.sup (fun z => Nat.ceil (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))) :=
      Finset.le_sup (f := fun z => Nat.ceil
        (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))) hz
    have h2 : Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1)
        ≤ ((S.sup (fun z => Nat.ceil
          (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))) : ℕ) : ℝ) :=
      le_trans (Nat.le_ceil _) (by exact_mod_cast h1)
    have h3 := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) h2
    have h4 : (2:ℝ) ^ (Real.logb 2 (max (farM L z : ℝ) (farY L z) + 1))
        = (max (farM L z : ℝ) (farY L z) + 1 : ℝ) :=
      Real.rpow_logb (by norm_num) (by norm_num) (by positivity)
    rw [h4, Real.rpow_natCast] at h3
    exact h3
  have h1 := farMass_le_doubleSum (q := q) R hR hLpos (le_of_eq hLdef.symm) K S hK
  have hcell0 : ∀ m k : ℕ, 0 ≤ (1/4:ℝ)^k * cellLayer R m k := by
    intro m k
    have : (0:ℝ) ≤ cellLayer R m k := by rw [cellLayer]; split <;> norm_num
    positivity
  have h2 : (∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k * cellLayer R m k
            * cellMult L (farPairs R S) m k)
      ≤ (∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k * cellLayer R m k
            * cellBoundJMcw q CJ c0 L m k) := by
    refine Finset.sum_le_sum (fun m _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
    refine Finset.sum_le_sum (fun k _ => ?_)
    refine mul_le_mul_of_nonneg_left ?_ (hcell0 m k)
    refine CellMultLeBoundJMcw hq hLpos hL1 hCJ hc0 hfamJ hball ?_ m k
    intro z hz
    rw [farPairs, Finset.mem_filter, Finset.mem_filter] at hz
    exact ⟨hz.1.2.1, hz.2⟩
  have h3 := MsumBoundJMcw hq hLpos hLdef hL1 R hR hCJ hc0 (Nat.ceil L + 1) (K+1)
  have h23 : (∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k * cellLayer R m k
            * cellMult L (farPairs R S) m k)
      ≤ 20000 * CJ / (R:ℝ)^(9/10:ℝ) + 60000 * c0 * L / (q:ℝ)^(29/50000:ℝ) := le_trans h2 h3
  refine le_trans h1 ?_
  have hmul : 32 * ((∑ m ∈ Finset.range (Nat.ceil L + 1), Real.exp (-(49/10) * (m:ℝ))
        * ∑ k ∈ Finset.range (K+1), (1/4:ℝ)^k * cellLayer R m k
            * cellMult L (farPairs R S) m k))
      ≤ 32 * (20000 * CJ / (R:ℝ)^(9/10:ℝ) + 60000 * c0 * L / (q:ℝ)^(29/50000:ℝ)) :=
    mul_le_mul_of_nonneg_left h23 (by norm_num)
  refine le_trans hmul (le_of_eq ?_)
  ring

/-- **Heath-Brown's Lemma 13.2 (the far-zero bound) from the *single* wide crude log-free input.**

Assuming only `Work.LinnikAreas.FamilyZeroDensityJutilaCrudeWide` — the crude log-free
non-principal family estimate `Σ_{χ ≠ 1} N(σ,T,χ) ≤ C·(qT)^{(24/5+ε)(1-σ)}` on the constant range
`σ ≥ 1 - 1021/5000` — the far-zero mass is bounded by `ε` for `q ≥ q₀(ε)` with the box radius
`R = R(ε)` fixed.  This is the single-input form of
`Work.LinnikAreas.FarBoundHyp_of_jutila_and_mesh`; it makes `Work.LinnikAreas.area2` depend on one
target instead of two. -/
theorem FarBoundOfJutilaCrudeWide (h : Work.LinnikAreas.FamilyZeroDensityJutilaCrudeWide) :
    Work.LinnikAreas.FarBoundHyp := by
  obtain ⟨CJ, hCJpos, hJ⟩ := h (1/1000) (by norm_num)
  obtain ⟨c0, hc0pos, hball⟩ :=
    Commons.NumberTheory.DirichletCharacter.completedL_ballZeroCount_uniform
  intro ε hε
  have hε4 : 0 < ε/4 := by linarith
  set A₁ : ℝ := (1280000 * CJ / ε) ^ ((10:ℝ)/9) with hA₁def
  have hA₁pos : 0 < A₁ := by rw [hA₁def]; exact Real.rpow_pos_of_pos (by positivity) _
  set R : ℕ := Nat.floor A₁ + 2 with hRdef
  have hR1 : 1 ≤ R := by rw [hRdef]; omega
  have hRpos : (0:ℝ) < (R:ℝ) := by exact_mod_cast (by omega : 0 < R)
  have hRleA₁ : A₁ ≤ (R:ℝ) := by
    have h2 : A₁ < ((Nat.floor A₁ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : ((Nat.floor A₁ : ℕ) : ℝ) + 1 ≤ (R:ℝ) := by
      rw [hRdef]; push_cast; linarith
    linarith
  have hA₁pow : A₁ ^ ((9:ℝ)/10) = 1280000 * CJ / ε := by
    rw [hA₁def, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 1280000 * CJ / ε)]
    norm_num
  have hfirst : 640000 * CJ / (R:ℝ)^(9/10:ℝ) ≤ ε/2 := by
    have hge : 1280000 * CJ / ε ≤ (R:ℝ) ^ ((9:ℝ)/10) := by
      have h := Real.rpow_le_rpow hA₁pos.le hRleA₁ (by norm_num : (0:ℝ) ≤ 9/10)
      rwa [hA₁pow] at h
    have hquot : 640000 * CJ / (R:ℝ)^(9/10:ℝ) ≤ 640000 * CJ / (1280000 * CJ / ε) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hge
    have hval : 640000 * CJ / (1280000 * CJ / ε) = ε/2 := by
      field_simp
      ring
    linarith
  set B : ℝ := max 1 (7680000 * c0 / ε) with hBdef
  have hB1 : (1:ℝ) ≤ B := le_max_left _ _
  have hBge : 7680000 * c0 / ε ≤ B := le_max_right _ _
  set q₀ : ℕ := max (max (max (Nat.ceil (Real.exp 30000000))
    (Nat.ceil (4 * (1920000:ℝ) * c0 / ε))) (Nat.ceil (B ^ 3449))) 2 with hq₀def
  have hq₀2 : 2 ≤ q₀ := by rw [hq₀def]; exact le_max_right _ _
  have hq₀exp : Nat.ceil (Real.exp 30000000) ≤ q₀ := by
    rw [hq₀def]
    exact le_trans (le_max_left _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hq₀c : Nat.ceil (4 * (1920000:ℝ) * c0 / ε) ≤ q₀ := by
    rw [hq₀def]
    exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hq₀B : Nat.ceil (B ^ 3449) ≤ q₀ := by
    rw [hq₀def]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨(R:ℝ), hRpos, q₀, ?_⟩
  intro q hq hqN
  have hq2 : 2 ≤ q := le_trans hq₀2 hq
  have hqRpos : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqR1 : (1:ℝ) ≤ (q:ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hexpq : Real.exp 30000000 ≤ (q:ℝ) := by
    have h1 : Real.exp 30000000 ≤ ((Nat.ceil (Real.exp 30000000) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (Real.exp 30000000) : ℕ) : ℝ) ≤ (q:ℝ) :=
      Nat.cast_le.mpr (le_trans hq₀exp hq)
    linarith
  have hL : 30000000 ≤ Real.log (q:ℝ) := by
    rw [← Real.log_exp 30000000]
    exact Real.log_le_log (Real.exp_pos 30000000) hexpq
  have hqbig : 4 * (1920000:ℝ) * c0 / ε ≤ (q:ℝ) := by
    have h1 : 4 * (1920000:ℝ) * c0 / ε
        ≤ ((Nat.ceil (4 * (1920000:ℝ) * c0 / ε) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (4 * (1920000:ℝ) * c0 / ε) : ℕ) : ℝ) ≤ (q:ℝ) :=
      Nat.cast_le.mpr (le_trans hq₀c hq)
    linarith
  let P : ℝ := Real.exp ((29/100000) * Real.log (q:ℝ))
  have hPval : P = Real.exp ((29/100000) * Real.log (q:ℝ)) := rfl
  have hPpos : (0:ℝ) < P := by rw [hPval]; exact Real.exp_pos _
  have hqP : (q:ℝ)^((29:ℝ)/100000) = P := by
    rw [hPval, Real.rpow_def_of_pos hqRpos]
    congr 1
    ring
  have hqB : B ^ 3449 ≤ (q:ℝ) := by
    have h1 : B ^ 3449 ≤ ((Nat.ceil (B ^ 3449) : ℕ) : ℝ) := Nat.le_ceil _
    have h2 : ((Nat.ceil (B ^ 3449) : ℕ) : ℝ) ≤ (q:ℝ) := Nat.cast_le.mpr (le_trans hq₀B hq)
    linarith
  have hBpos : (0:ℝ) < B := lt_of_lt_of_le zero_lt_one hB1
  have hBq : B ≤ P := by
    rw [← hqP]
    have h2 : (B ^ (3449:ℕ) : ℝ) ^ ((29:ℝ)/100000) ≤ (q:ℝ)^((29:ℝ)/100000) :=
      Real.rpow_le_rpow (by positivity) hqB (by norm_num)
    have h3 : (B ^ (3449:ℕ) : ℝ) ^ ((29:ℝ)/100000)
        = B ^ (((29:ℝ)/100000) * 3449) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hBpos)]
      congr 1
      ring
    have h1 : (1:ℝ) ≤ ((29:ℝ)/100000) * 3449 := by norm_num
    have h9 : B ≤ B ^ (((29:ℝ)/100000)*3449) := by
      have h10 := Real.rpow_le_rpow_of_exponent_le hB1 h1
      rwa [Real.rpow_one] at h10
    linarith [h2, h3, h9]
  have hAg : 7680000 * c0 ≤ ε * P := by
    have h2 : 7680000 * c0 / ε ≤ P := le_trans hBge hBq
    rw [div_le_iff₀ hε] at h2
    linarith [h2]
  have hLle : Real.log (q:ℝ) ≤ P := by
    rw [hPval]
    have hx : (0:ℝ) ≤ (29/100000) * Real.log (q:ℝ) := by
      have h1 : (0:ℝ) ≤ Real.log (q:ℝ) := by linarith [hL]
      positivity
    have h2 := Real.pow_div_factorial_le_exp ((29/100000) * Real.log (q:ℝ)) hx 2
    have hbig : Real.log (q:ℝ) ≤ ((29/100000) * Real.log (q:ℝ))^2/2 := by
      have h3 : ((29:ℝ)/100000) = 0.00029 := by norm_num
      nlinarith [hL]
    linarith [h2, hbig]
  have hthird : 1920000 * c0 * Real.log (q:ℝ) / (q:ℝ)^(29/50000:ℝ) ≤ ε/4 := by
    have hsplit : (q:ℝ)^(29/50000:ℝ) = P * P := by
      have hPQ : (q:ℝ)^((29:ℝ)/100000) = P := hqP
      rw [← hPQ, ← Real.rpow_add hqRpos]
      congr 1
      norm_num
    rw [hsplit, div_le_iff₀ (mul_pos hPpos hPpos)]
    have hc0 : (0:ℝ) ≤ c0 := le_of_lt hc0pos
    nlinarith [hLle, hAg, hc0, hPpos, hε]
  have hfamJ : ∀ σ T : ℝ, (1:ℝ) - 1021/5000 ≤ σ → σ ≤ 1 → 1 ≤ T →
      ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ σ T
        ≤ CJ * ((q:ℝ) * T) ^ (((24:ℝ)/5 + 1/1000) * (1 - σ)) :=
    fun σ T hσ hσ1 hT => hJ q hq2 σ T hσ hσ1 hT
  -- the total far mass
  have hfin : ∀ u : Finset (DirichletCharacter ℂ q × ℂ), farMassSum R (Real.log (q:ℝ)) u ≤ ε := by
    intro u
    have hb := finset_boundJMcw q hq2 R hR1 CJ c0 hCJpos hc0pos hfamJ hball hL u
    linarith [hb, hfirst, hthird]
  let F : DirichletCharacter ℂ q × ℂ → ℝ := fun z =>
    if z.1 = 1 then 0 else if InBox q (R:ℝ) z.2 then 0
      else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * Real.log (q:ℝ))‖
  have hFbound : ∀ u : Finset (DirichletCharacter ℂ q × ℂ), ∑ z ∈ u, F z ≤ ε := fun u => hfin u
  have hFnn : 0 ≤ F := fun z => by
    show 0 ≤ (if z.1 = 1 then 0 else if InBox q (R:ℝ) z.2 then 0
      else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * Real.log (q:ℝ))‖)
    split_ifs with h1 h2
    · exact le_refl 0
    · exact le_refl 0
    · exact mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  have hsumm : Summable F := summable_of_sum_le hFnn hFbound
  have htsum : ∑' z : DirichletCharacter ℂ q × ℂ, F z ≤ ε :=
    Real.tsum_le_of_sum_le hFnn hFbound
  rw [Summable.tsum_prod hsumm] at htsum
  rw [tsum_fintype] at htsum
  have hstep : (∑ χ : DirichletCharacter ℂ q, ∑' ρ : ℂ, F (χ, ρ))
      = ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          farSum q (11/2) (3/10) (R:ℝ) χ := by
    have h1z : (∑' ρ : ℂ, F ((1 : DirichletCharacter ℂ q), ρ)) = 0 := by
      rw [tsum_congr (fun ρ => ?_), tsum_zero]
      have hp : ((1 : DirichletCharacter ℂ q), ρ).1 = 1 := rfl
      show (if ((1 : DirichletCharacter ℂ q), ρ).1 = 1 then (0:ℝ) else _) = 0
      rw [if_pos hp]
    rw [← Finset.sum_erase_add _ (fun χ => ∑' ρ : ℂ, F (χ, ρ))
        (Finset.mem_univ (1 : DirichletCharacter ℂ q)), h1z, add_zero]
    refine Finset.sum_congr rfl (fun χ hχ => ?_)
    have hχ1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    rw [farSum]
    refine tsum_congr (fun ρ => ?_)
    have hpt : (χ, ρ).1 ≠ 1 := by simpa using hχ1
    simp only [F]
    rw [if_neg hpt]
  rw [hstep] at htsum
  exact htsum

end Work.LinnikAreas
