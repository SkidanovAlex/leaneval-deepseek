/-
# `Submission.Work.FIChain.s3InnerInt_eq_dsum` — the `λ⁺`-inner sum as a divisor sum of
congruence-block integrals (**real endpoints**)

`s3InnerInt a N ℓ Cm z sz = Σ_{c ∈ S} a(ℓc)·∫_1^{c/Cm}ρ(c;u)du/u` (`S` = the chain's `c`-range
`z < c ≤ sz`, `ℓ c ≤ N`).  Expanding `ρ(c;u) = Σ_{d | c, d ≤ u} μ(d)` and swapping the `c`- and
`d`-sums gives `∫_1^{sz/Cm}(du/u)Σ_{d ≤ u}μ(d)A_d(u)`, where `A_d(u)` is the sum of `a(ℓc)` over
the range with `d | c` and `Cm u < c`; with `n = ℓc` that is the congruence sum
`Ad a (ℓd)(min (ℓ sz) N) − Ad a (ℓd)(max (ℓ z) (ℓ Cm u))` (`Ad_block_eq_real`).

The `u`-integral is cut at `U = min (sz/Cm) (N/(ℓ Cm))`: for `Cm u > N/ℓ` no `c ≤ N/ℓ` satisfies
`Cm u < c`, so the `u`-integrand vanishes; and on `[1,U]` the hypotheses `ℓ z ≤ N`,
`u ≤ N/(ℓ Cm)` make the block a genuine `Ad`-difference.

**Real endpoints are essential** for the downstream `(2.4)`-application: they give the `b`-window
conditions `n ≤ ℓ sz`, `n > ℓ z`, `n > ℓ Cm u` (no floors), hence (with `t = ℓ Cm u`) the
modulus-count condition `ζ = ℓd ≤ t/Cm` **uniform in `(e,b,d)`** — exactly the shape of
`Work.FIChain.main_ebd_sum_le`.  Corollaries (all proved here):
`rhoTrunc_eq_sum_filter`, `innerC_u_eq`, `s3InnerInt_eq_dsum`. -/
import Mathlib
import Submission.Work.FIChain.S3plusC_route_defs
import Submission.Work.FIChain.Ad_block_eq_real
import Submission.Work.FIChain.s3InnerInt_eq_integral_swap

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIChain

open Finset
open scoped BigOperators Interval

attribute [local instance] Classical.propDecidable

noncomputable section

namespace Work.FIChain
open scoped BigOperators
noncomputable section

/-- `rhoTrunc c u` as a sum over `d ∈ Icc 1 ⌊u⌋₊` with `d ∣ c` (for `1 ≤ c`). -/
lemma rhoTrunc_eq_sum_filter (c : ℕ) (u : ℝ) (hc : 1 ≤ c) :
    Submission.ASP.rhoTrunc c u
      = ∑ d ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun d => d ∣ c), (ArithmeticFunction.moebius d : ℝ) := by
  rw [Submission.ASP.rhoTrunc]
  refine Finset.sum_congr ?_ (fun d _ => rfl)
  ext d
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdvd, -⟩, hle⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega), Nat.le_floor hle⟩, hdvd⟩
  · rintro ⟨⟨hd1, hle⟩, hdvd⟩
    refine ⟨⟨hdvd, by omega⟩, ?_⟩
    by_cases hu : 0 ≤ u
    · exact le_trans (Nat.cast_le.mpr hle) (Nat.floor_le hu)
    · rw [Nat.floor_eq_zero.mpr (by linarith [not_le.mp hu])] at hle
      omega

/-- **The pointwise identity at a real `u`** (real endpoints). -/
lemma innerC_u_eq (a : ℕ → ℝ) (N ℓ Cm : ℕ) (z sz u : ℝ) (hℓ : 1 ≤ ℓ) (hCm : 1 ≤ Cm)
    (hz0 : 0 ≤ z) (hA : max z ((Cm:ℝ)*u) ≤ sz) (hB : (ℓ:ℝ) * max z ((Cm:ℝ)*u) ≤ (N:ℝ)) :
    (∑ c ∈ (Finset.Icc 1 N).filter (fun c : ℕ => z < (c:ℝ) ∧ (c:ℝ) ≤ sz ∧ ℓ*c ≤ N),
        (if (Cm:ℝ)*u < (c:ℝ) then a (ℓ*c) * Submission.ASP.rhoTrunc c u else 0))
      = ∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
          (Submission.ASP.Ad a (ℓ*d) (min ((ℓ:ℝ) * sz) (N:ℝ))
            - Submission.ASP.Ad a (ℓ*d) (max ((ℓ:ℝ) * z) ((ℓ:ℝ) * (Cm:ℝ) * u))) := by
  classical
  have hA0 : 0 ≤ max z ((Cm:ℝ)*u) := le_trans hz0 (le_max_left _ _)
  have hℓmul : (ℓ:ℝ) * max z ((Cm:ℝ)*u) = max ((ℓ:ℝ)*z) ((ℓ:ℝ)*((Cm:ℝ)*u)) :=
    mul_max_of_nonneg _ _ (by positivity)
  have hTeq : ∀ d : ℕ,
      (((Finset.Icc 1 N).filter (fun c : ℕ => z < (c:ℝ) ∧ (c:ℝ) ≤ sz ∧ ℓ*c ≤ N)).filter
          (fun c : ℕ => (Cm:ℝ)*u < (c:ℝ))).filter (fun c : ℕ => d ∣ c)
      = (Finset.Icc 1 N).filter
          (fun c : ℕ => max z ((Cm:ℝ)*u) < (c:ℝ) ∧ (c:ℝ) ≤ sz ∧ ℓ*c ≤ N ∧ d ∣ c) := by
    intro d
    rw [Finset.filter_filter, Finset.filter_filter]
    refine Finset.filter_congr ?_
    intro c hc
    constructor
    · rintro ⟨⟨hz, hs, hl⟩, hcu, hd⟩
      exact ⟨max_lt hz hcu, hs, hl, hd⟩
    · rintro ⟨hm, hs, hl, hd⟩
      exact ⟨⟨lt_of_le_of_lt (le_max_left _ _) hm, hs, hl⟩,
        lt_of_le_of_lt (le_max_right _ _) hm, hd⟩
  rw [← Finset.sum_filter]
  trans ∑ c ∈ ((Finset.Icc 1 N).filter (fun c : ℕ => z < (c:ℝ) ∧ (c:ℝ) ≤ sz ∧ ℓ*c ≤ N)).filter
        (fun c : ℕ => (Cm:ℝ)*u < (c:ℝ)),
      a (ℓ*c) * ∑ d ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun d : ℕ => d ∣ c), (ArithmeticFunction.moebius d : ℝ)
  · refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hc
    rw [rhoTrunc_eq_sum_filter c u (by omega)]
  trans ∑ c ∈ ((Finset.Icc 1 N).filter (fun c : ℕ => z < (c:ℝ) ∧ (c:ℝ) ≤ sz ∧ ℓ*c ≤ N)).filter
        (fun c : ℕ => (Cm:ℝ)*u < (c:ℝ)),
      ∑ d ∈ Finset.Icc 1 ⌊u⌋₊,
        (if d ∣ c then a (ℓ*c) * (ArithmeticFunction.moebius d : ℝ) else 0)
  · refine Finset.sum_congr rfl (fun c hc => ?_)
    rw [Finset.mul_sum, Finset.sum_filter]
  trans ∑ d ∈ Finset.Icc 1 ⌊u⌋₊, ∑ c ∈ ((Finset.Icc 1 N).filter
        (fun c : ℕ => z < (c:ℝ) ∧ (c:ℝ) ≤ sz ∧ ℓ*c ≤ N)).filter
        (fun c : ℕ => (Cm:ℝ)*u < (c:ℝ)),
        (if d ∣ c then a (ℓ*c) * (ArithmeticFunction.moebius d : ℝ) else 0)
  · exact Finset.sum_comm
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have h1 : (∑ c ∈ (((Finset.Icc 1 N).filter
        (fun c : ℕ => z < (c:ℝ) ∧ (c:ℝ) ≤ sz ∧ ℓ*c ≤ N)).filter
        (fun c : ℕ => (Cm:ℝ)*u < (c:ℝ))),
        (if d ∣ c then a (ℓ*c) * (ArithmeticFunction.moebius d : ℝ) else 0))
      = (ArithmeticFunction.moebius d : ℝ) * ∑ c ∈ (Finset.Icc 1 N).filter
        (fun c : ℕ => max z ((Cm:ℝ)*u) < (c:ℝ) ∧ (c:ℝ) ≤ sz ∧ ℓ*c ≤ N ∧ d ∣ c), a (ℓ*c) := by
    rw [(Finset.sum_filter (fun c : ℕ => d ∣ c)
        (fun c => a (ℓ*c) * (ArithmeticFunction.moebius d : ℝ))).symm, hTeq d, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun c _ => by ring)
  rw [h1, Ad_block_eq_real a N ℓ d (max z ((Cm:ℝ)*u)) sz hℓ hA0 hA hB]
  rw [hℓmul]
  ring_nf


theorem s3InnerInt_eq_dsum (a : ℕ → ℝ) (N ℓ Cm : ℕ) (z sz : ℝ)
    (hℓ : 1 ≤ ℓ) (hCm : 1 ≤ Cm) (hsz1 : 1 ≤ sz) (hzsz : z ≤ sz)
    (hzN : (ℓ : ℝ) * z ≤ (N : ℝ)) (hCmz : (Cm : ℝ) ≤ z) (hT : 1 ≤ sz / (Cm : ℝ)) :
    s3InnerInt a N ℓ Cm z sz
      = ∫ u in (1 : ℝ)..(min (sz / (Cm : ℝ)) ((N : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)))),
          (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
            (Submission.ASP.Ad a (ℓ * d) (min ((ℓ:ℝ) * sz) (N : ℝ))
              - Submission.ASP.Ad a (ℓ * d) (max ((ℓ:ℝ) * z) ((ℓ:ℝ) * (Cm:ℝ) * u)))) / u := by
  classical
  set U : ℝ := min (sz / (Cm : ℝ)) ((N : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) with hUdef
  have hCmpos : (0 : ℝ) < (Cm : ℝ) := by exact_mod_cast (by omega : 0 < Cm)
  have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by exact_mod_cast (by omega : 0 < ℓ)
  have hUl : U ≤ sz / (Cm : ℝ) := min_le_left _ _
  have hUr : U ≤ (N : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) := min_le_right _ _
  have hU1 : 1 ≤ U := by
    refine le_min hT ?_
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hCmz hℓpos.le, hzN]
  have hszpos : 0 < sz := lt_of_lt_of_le zero_lt_one hsz1
  have hz0 : 0 ≤ z := le_trans (by positivity : (0:ℝ) ≤ (Cm:ℝ)) hCmz
  set F : ℝ → ℝ := fun u => ∑ c ∈ (Finset.Icc 1 N).filter
      (fun c : ℕ => z < (c:ℝ) ∧ (c:ℝ) ≤ sz ∧ ℓ*c ≤ N),
      (if (Cm:ℝ)*u < (c:ℝ) then a (ℓ*c) * Submission.ASP.rhoTrunc c u else 0) with hFdef
  have hmain := s3InnerInt_eq_integral_swap a N ℓ Cm z sz hCm hCmz hszpos hT
  rw [hmain]
  have hfun : (fun u : ℝ => ∑ c ∈ (Finset.Icc 1 N).filter
      (fun c : ℕ => z < (c:ℝ) ∧ (c:ℝ) ≤ sz ∧ ℓ*c ≤ N),
      (if (Cm:ℝ)*u < (c:ℝ) then a (ℓ*c) * Submission.ASP.rhoTrunc c u else 0) / u)
      = fun u : ℝ => F u / u := by
    funext u; rw [hFdef, Finset.sum_div]
  rw [hfun]
  have hFzero : ∀ u : ℝ, U < u → F u = 0 := by
    intro u hu
    rw [hFdef]
    refine Finset.sum_eq_zero (fun c hc => ?_)
    rw [Finset.mem_filter, Finset.mem_Icc] at hc
    obtain ⟨⟨hc1, hcN⟩, hcz, hcsz, hcl⟩ := hc
    rw [if_neg]
    intro hcon
    have h1 : u < sz / (Cm : ℝ) := by
      rw [lt_div_iff₀ hCmpos]
      nlinarith [hcon, hcsz]
    have h2 : U < sz / (Cm : ℝ) := lt_trans hu h1
    have hUeq : U = (N : ℝ) / ((ℓ : ℝ) * (Cm : ℝ)) := by
      rw [hUdef]
      rcases min_cases (sz / (Cm : ℝ)) ((N : ℝ) / ((ℓ : ℝ) * (Cm : ℝ))) with ⟨he, -⟩ | ⟨he, -⟩
      · rw [← he, hUdef] at h2; exact absurd h2 (lt_irrefl _)
      · exact he
    have h3 : (N : ℝ) < u * ((ℓ : ℝ) * (Cm : ℝ)) := by
      have h4 : U < u := hu
      rw [hUeq, div_lt_iff₀ (by positivity)] at h4
      linarith
    have h4 : (ℓ : ℝ) * ((Cm : ℝ) * u) < (ℓ : ℝ) * (c : ℝ) :=
      mul_lt_mul_of_pos_left (show (Cm:ℝ) * u < (c:ℝ) from hcon) (show (0:ℝ) < (ℓ:ℝ) from hℓpos)
    have h5 : (ℓ : ℝ) * (c : ℝ) ≤ (N : ℝ) := by
      have h6 : (((ℓ * c : ℕ)) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcl
      push_cast at h6
      exact h6
    nlinarith [h3, h4, h5]
  have hcut : (∫ u in (1 : ℝ)..(sz / (Cm : ℝ)), F u / u) = ∫ u in (1 : ℝ)..U, F u / u := by
    rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hU1]
    have hpt : ∀ u ∈ Set.Ioc (1 : ℝ) (sz / (Cm : ℝ)),
        (Set.Ioc (1 : ℝ) U).indicator (fun u => F u / u) u = F u / u := by
      intro u hu
      rw [Set.mem_Ioc] at hu
      by_cases h : u ≤ U
      · exact Set.indicator_of_mem (show u ∈ Set.Ioc (1:ℝ) U from Set.mem_Ioc.mpr ⟨hu.1, h⟩) _
      · rw [Set.indicator_of_notMem (fun hh => h (Set.mem_Ioc.mp hh).2),
          hFzero u (not_le.mp h), zero_div]
    rw [← MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hpt,
      MeasureTheory.setIntegral_indicator measurableSet_Ioc]
    rw [show Set.Ioc (1:ℝ) (sz / (Cm:ℝ)) ∩ Set.Ioc (1:ℝ) U = Set.Ioc (1:ℝ) U from
      Set.inter_eq_right.mpr (fun u hu => Set.mem_Ioc.mpr
        ⟨(Set.mem_Ioc.mp hu).1, le_trans (Set.mem_Ioc.mp hu).2 hUl⟩)]
  rw [hcut]
  have hpt2 : ∀ u ∈ Set.uIcc (1 : ℝ) U, F u / u
      = (∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
            (Submission.ASP.Ad a (ℓ * d) (min ((ℓ:ℝ) * sz) (N : ℝ))
              - Submission.ASP.Ad a (ℓ * d) (max ((ℓ:ℝ) * z) ((ℓ:ℝ) * (Cm:ℝ) * u)))) / u := by
    intro u hu
    rw [Set.uIcc_of_le hU1] at hu
    obtain ⟨hu1, huU⟩ := hu
    have hA : max z ((Cm:ℝ)*u) ≤ sz := by
      refine max_le hzsz ?_
      calc (Cm:ℝ) * u ≤ (Cm:ℝ) * U := mul_le_mul_of_nonneg_left huU hCmpos.le
        _ ≤ (Cm:ℝ) * (sz / (Cm:ℝ)) := mul_le_mul_of_nonneg_left hUl hCmpos.le
        _ = sz := by field_simp
    have hB : (ℓ:ℝ) * max z ((Cm:ℝ)*u) ≤ (N:ℝ) := by
      rw [mul_max_of_nonneg _ _ hℓpos.le]
      refine max_le hzN ?_
      have h8 : (ℓ:ℝ) * (Cm:ℝ) * U ≤ (N:ℝ) := by
        have h8' := hUr
        rw [le_div_iff₀ (by positivity : (0:ℝ) < (ℓ:ℝ) * (Cm:ℝ))] at h8'
        calc (ℓ:ℝ) * (Cm:ℝ) * U = U * ((ℓ:ℝ) * (Cm:ℝ)) := by ring
          _ ≤ (N:ℝ) := h8'
      calc (ℓ:ℝ) * ((Cm:ℝ) * u) = (ℓ:ℝ) * (Cm:ℝ) * u := by ring
        _ ≤ (ℓ:ℝ) * (Cm:ℝ) * U := mul_le_mul_of_nonneg_left huU (by positivity)
        _ ≤ (N:ℝ) := h8
    rw [show F u = ∑ d ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.moebius d : ℝ) *
          (Submission.ASP.Ad a (ℓ*d) (min ((ℓ:ℝ) * sz) (N:ℝ))
            - Submission.ASP.Ad a (ℓ*d) (max ((ℓ:ℝ) * z) ((ℓ:ℝ) * (Cm:ℝ) * u)))
        from innerC_u_eq a N ℓ Cm z sz u hℓ hCm hz0 hA hB]
  rw [intervalIntegral.integral_congr hpt2, hUdef]



end

end Work.FIChain
