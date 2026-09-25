import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_block_core_defs

namespace Work.BourgainPlan.Maximal

open Finset
open Commons.Analysis.ExponentialSums

set_option autoImplicit false

/-! ## Elementary helpers for count-of-indicators arguments -/

/-- A finite sum of `0/1`-indicators is the indicator of "some point is active". -/
lemma sum_ite_one_eq_indicator {α : Type*} (S : Finset α) (Q : α → Prop) [DecidablePred Q]
    (huniq : ∀ x ∈ S, ∀ y ∈ S, Q x → Q y → x = y) :
    (∑ x ∈ S, (if Q x then (1:ℂ) else 0)) = if (∃ x ∈ S, Q x) then 1 else 0 := by
  by_cases h : ∃ x ∈ S, Q x
  · obtain ⟨x0, hx0S, hx0⟩ := h
    have hmain : (∑ x ∈ S, (if Q x then (1:ℂ) else 0)) = 1 := by
      rw [Finset.sum_eq_single x0]
      · rw [if_pos hx0]
      · intro y hyS hyne
        rw [if_neg]
        exact fun hy => hyne (huniq y hyS x0 hx0S hy hx0)
      · intro hx0not
        exact absurd hx0S hx0not
    rw [hmain, if_pos ⟨x0, hx0S, hx0⟩]
  · rw [if_neg h]
    refine Finset.sum_eq_zero (fun x hx => ?_)
    rw [if_neg]
    exact fun hxQ => h ⟨x, hx, hxQ⟩

/-- If two natural numbers below `K` differ by a multiple of `K`, they are equal. -/
lemma nat_eq_of_sub_eq_mul {K : ℕ} (hK : 1 ≤ K) {s s' : ℕ} {m : ℤ}
    (hs : s < K) (hs' : s' < K) (h : (s:ℤ) - (s':ℤ) = m * (K:ℤ)) : s = s' := by
  have hKpos : (0:ℤ) < (K:ℤ) := by exact_mod_cast hK
  have habs : |(s:ℤ) - (s':ℤ)| < (K:ℤ) := by
    rw [abs_lt]
    refine ⟨?_, ?_⟩
    · have h1 : (s':ℤ) < (K:ℤ) := by exact_mod_cast hs'
      have h2 : (0:ℤ) ≤ (s:ℤ) := Int.natCast_nonneg s
      omega
    · have h1 : (s:ℤ) < (K:ℤ) := by exact_mod_cast hs
      have h2 : (0:ℤ) ≤ (s':ℤ) := Int.natCast_nonneg s'
      omega
  have hlt : |m| * (K:ℤ) < (K:ℤ) := by
    have h' := habs
    rw [h, abs_mul, abs_of_nonneg (Int.natCast_nonneg K)] at h'
    exact h'
  have hm0 : m = 0 := by
    by_contra hm
    have h1 : (1:ℤ) ≤ |m| := Int.one_le_abs hm
    have h3 : (K:ℤ) ≤ |m| * (K:ℤ) := by
      calc (K:ℤ) = 1 * (K:ℤ) := by ring
        _ ≤ |m| * (K:ℤ) := mul_le_mul_of_nonneg_right h1 (Int.natCast_nonneg K)
    linarith
  have hzero : (s:ℤ) - (s':ℤ) = 0 := by rw [h, hm0, zero_mul]
  have : (s:ℤ) = (s':ℤ) := sub_eq_zero.mp hzero
  exact_mod_cast this

/-- An integer within `ρ < 1/2` of `u - c₀`, where `u ∈ (0,K)` and `c₀ ∈ [0,1)`, lies in the
window `[-1,K]`. -/
lemma int_mem_Icc_of_close_scaled {K : ℕ} (hK : 1 ≤ K) {c₀ u ρ : ℝ}
    (hc0 : 0 ≤ c₀) (hc1 : c₀ < 1) (hu0 : 0 < u) (hu1 : u < (K:ℝ)) (hr : ρ < 1/2)
    {l : ℤ} (hl : |u - c₀ - (l:ℝ)| ≤ ρ) :
    l ∈ Finset.Icc (-1:ℤ) (K:ℤ) := by
  obtain ⟨hle1, hle2⟩ := abs_le.mp hl
  have hgt : (-1:ℝ) < u - c₀ := by linarith
  have hlt : u - c₀ < (K:ℝ) := by linarith
  rw [Finset.mem_Icc]
  constructor
  · have h3 : (-3/2 : ℝ) < (l:ℝ) := by linarith
    by_contra hcon
    rw [not_le] at hcon
    have h4 : l ≤ -2 := by omega
    have h5 : (l:ℝ) ≤ -2 := by exact_mod_cast h4
    linarith
  · have h3 : (l:ℝ) < (K:ℝ) + 1/2 := by linarith
    by_contra hcon
    rw [not_le] at hcon
    have h4 : (K:ℤ) + 1 ≤ l := by omega
    have h5 : ((K:ℤ):ℝ) + 1 ≤ (l:ℝ) := by exact_mod_cast h4
    push_cast at h5
    linarith

open Classical in
/-- **Collapse of the `l`-window to the periodised sum (scaled form).**

For `K ≥ 1`, `c₀ ∈ [0,1)`, `u ∈ (0,K)` and `ρ ∈ (0,1/2)`, the sum over the window `l ∈ [-1,K]` of
the sharp indicators `1_{|u - c₀ - l| ≤ ρ}` equals the sum over the residues `s ∈ [0,K)` of the
periodised indicators `1_{∃m, |u + mK - (c₀+s)| ≤ ρ}`. -/
lemma sharpCore_sum_eq_periodic_scaled (K : ℕ) (hK : 1 ≤ K) (c₀ u ρ : ℝ)
    (hc0 : 0 ≤ c₀) (hc1 : c₀ < 1) (hu0 : 0 < u) (hu1 : u < (K:ℝ))
    (hr0 : 0 < ρ) (hr : ρ < 1/2) :
    (∑ l ∈ Finset.Icc (-1 : ℤ) (K:ℤ), (if |u - c₀ - (l:ℝ)| ≤ ρ then (1:ℂ) else 0))
      = (∑ s ∈ Finset.range K,
          (if ∃ m : ℤ, |u + (m:ℝ)*(K:ℝ) - (c₀ + (s:ℝ))| ≤ ρ then (1:ℂ) else 0)) := by
  have hIntUniq : ∀ l l' : ℤ, |u - c₀ - (l:ℝ)| ≤ ρ → |u - c₀ - (l':ℝ)| ≤ ρ → l = l' := by
    intro l l' hl hl'
    by_contra hne
    have h2 : (1:ℝ) ≤ |(l:ℝ) - (l':ℝ)| := by
      have hcast : ((l - l' : ℤ):ℝ) = (l:ℝ) - (l':ℝ) := by push_cast; ring
      rw [← hcast, ← Int.cast_abs]
      exact_mod_cast (Int.one_le_abs (sub_ne_zero.mpr hne))
    have h1 : |(l:ℝ) - (l':ℝ)| ≤ 2*ρ := by
      calc |(l:ℝ) - (l':ℝ)| = |(u - c₀ - (l':ℝ)) - (u - c₀ - (l:ℝ))| := by ring_nf
        _ ≤ |u - c₀ - (l':ℝ)| + |u - c₀ - (l:ℝ)| := abs_sub _ _
        _ ≤ ρ + ρ := add_le_add hl' hl
        _ = 2*ρ := by ring
    linarith
  have hLuniq : ∀ l ∈ Finset.Icc (-1:ℤ) (K:ℤ), ∀ l' ∈ Finset.Icc (-1:ℤ) (K:ℤ),
      |u - c₀ - (l:ℝ)| ≤ ρ → |u - c₀ - (l':ℝ)| ≤ ρ → l = l' :=
    fun l _ l' _ hl hl' => hIntUniq l l' hl hl'
  have hkey : ∀ (t : ℕ) (n : ℤ), |u + (n:ℝ)*(K:ℝ) - (c₀ + (t:ℝ))| ≤ ρ →
      |u - c₀ - (((t:ℤ) - n*(K:ℤ) : ℤ):ℝ)| ≤ ρ := by
    intro t n hn
    have hcast : (((t:ℤ) - n*(K:ℤ) : ℤ):ℝ) = (t:ℝ) - (n:ℝ)*(K:ℝ) := by push_cast; ring
    rw [hcast]
    have : u - c₀ - ((t:ℝ) - (n:ℝ)*(K:ℝ)) = u + (n:ℝ)*(K:ℝ) - (c₀ + (t:ℝ)) := by ring
    rw [this]; exact hn
  have hRuniq : ∀ s ∈ Finset.range K, ∀ s' ∈ Finset.range K,
      (∃ m : ℤ, |u + (m:ℝ)*(K:ℝ) - (c₀ + (s:ℝ))| ≤ ρ) →
      (∃ m : ℤ, |u + (m:ℝ)*(K:ℝ) - (c₀ + (s':ℝ))| ≤ ρ) → s = s' := by
    intro s hs s' hs' hm hm'
    obtain ⟨m, hm⟩ := hm
    obtain ⟨m', hm'⟩ := hm'
    have hslt : s < K := Finset.mem_range.mp hs
    have hs'lt : s' < K := Finset.mem_range.mp hs'
    have hl := hkey s m hm
    have hl' := hkey s' m' hm'
    have heq := hIntUniq _ _ hl hl'
    have hsub : (s:ℤ) - (s':ℤ) = (m - m') * (K:ℤ) := by linear_combination heq
    exact nat_eq_of_sub_eq_mul hK hslt hs'lt hsub
  have hEx : (∃ l ∈ Finset.Icc (-1:ℤ) (K:ℤ), |u - c₀ - (l:ℝ)| ≤ ρ)
      ↔ (∃ s ∈ Finset.range K, ∃ m : ℤ, |u + (m:ℝ)*(K:ℝ) - (c₀ + (s:ℝ))| ≤ ρ) := by
    constructor
    · rintro ⟨l, hl, hla⟩
      have hKZ : (K:ℤ) ≠ 0 := by
        have : (0:ℤ) < (K:ℤ) := by exact_mod_cast hK
        omega
      have hs_mem : (l % (K:ℤ)).toNat ∈ Finset.range K := by
        rw [Finset.mem_range]
        exact (Int.toNat_lt (Int.emod_nonneg l hKZ)).mpr
          (Int.emod_lt_of_pos l (by exact_mod_cast hK))
      refine ⟨(l % (K:ℤ)).toNat, hs_mem, -(l / (K:ℤ)), ?_⟩
      have hem : (((l % (K:ℤ)).toNat : ℕ) : ℝ) = ((l % (K:ℤ) : ℤ) : ℝ) := by
        have h := Int.toNat_of_nonneg (Int.emod_nonneg l hKZ)
        exact_mod_cast h
      have hde : ((l % (K:ℤ) : ℤ) : ℝ) + (K:ℝ) * ((l / (K:ℤ) : ℤ):ℝ) = (l:ℝ) := by
        have h := Int.emod_add_mul_ediv l (K:ℤ)
        exact_mod_cast h
      have heq2 : u + ((-(l / (K:ℤ)) : ℤ):ℝ)*(K:ℝ)
            - (c₀ + (((l % (K:ℤ)).toNat : ℕ):ℝ)) = u - c₀ - (l:ℝ) := by
        rw [hem, ← hde]
        push_cast
        ring
      rw [heq2]
      exact hla
    · rintro ⟨s, hs, m, hm⟩
      have hslt : s < K := Finset.mem_range.mp hs
      have hl : |u - c₀ - (((s:ℤ) - m*(K:ℤ) : ℤ):ℝ)| ≤ ρ := hkey s m hm
      exact ⟨(s:ℤ) - m*(K:ℤ),
        int_mem_Icc_of_close_scaled hK hc0 hc1 hu0 hu1 hr hl, hl⟩
  rw [sum_ite_one_eq_indicator (Finset.Icc (-1:ℤ) (K:ℤ))
        (fun l : ℤ => |u - c₀ - (l:ℝ)| ≤ ρ) hLuniq,
      sum_ite_one_eq_indicator (Finset.range K)
        (fun s : ℕ => ∃ m : ℤ, |u + (m:ℝ)*(K:ℝ) - (c₀ + (s:ℝ))| ≤ ρ) hRuniq]
  by_cases h : (∃ l ∈ Finset.Icc (-1:ℤ) (K:ℤ), |u - c₀ - (l:ℝ)| ≤ ρ)
  · rw [if_pos h, if_pos (hEx.mp h)]
  · rw [if_neg h, if_neg (fun hh => h (hEx.mpr hh))]

/-! ## The two pointwise identifications for the general polynomial -/

/-- The sharp-window condition of a single `l`-term, rescaled by the leading coefficient. -/
lemma sharp_iff_scaled (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (q a : ℕ) (hq : 1 ≤ q)
    {k : ℕ} (θ : ℝ) (l : ℤ) :
    (|polyDil P k * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1)
      ↔ (|(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)|
            ≤ (P.leadingCoeff:ℝ)*(polyDil P k)⁻¹) := by
  have hc0 : (0:ℝ) < (P.leadingCoeff:ℝ) := by exact_mod_cast hc
  have hpos : 0 < polyDil P k := polyDil_pos P k
  have hY : (P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)
      = (P.leadingCoeff:ℝ) * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))) := by
    field_simp
    ring
  rw [hY]
  constructor
  · intro h
    have h1 : polyDil P k * |θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))| ≤ 1 := by
      rwa [abs_mul, abs_of_pos hpos] at h
    have hX : |θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))| ≤ (polyDil P k)⁻¹ := by
      have h2 : polyDil P k * |θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))|
          ≤ polyDil P k * (polyDil P k)⁻¹ := by
        rw [mul_inv_cancel₀ (ne_of_gt hpos)]
        exact h1
      exact le_of_mul_le_mul_left h2 hpos
    calc |(P.leadingCoeff:ℝ) * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))|
        = (P.leadingCoeff:ℝ) * |θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))| := by
          rw [abs_mul, abs_of_pos hc0]
      _ ≤ (P.leadingCoeff:ℝ) * (polyDil P k)⁻¹ := mul_le_mul_of_nonneg_left hX (le_of_lt hc0)
  · intro h
    have hcX : (P.leadingCoeff:ℝ) * |θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))|
        ≤ (P.leadingCoeff:ℝ) * (polyDil P k)⁻¹ := by
      rwa [abs_mul, abs_of_pos hc0] at h
    have hX : |θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))| ≤ (polyDil P k)⁻¹ :=
      (mul_le_mul_iff_of_pos_left hc0).mp hcX
    have h1 : polyDil P k * |θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ))| ≤ 1 := by
      have h2 := mul_le_mul_of_nonneg_left hX (le_of_lt hpos)
      rwa [mul_inv_cancel₀ (ne_of_gt hpos)] at h2
    rwa [abs_mul, abs_of_pos hpos]

open Classical in
/-- The periodised-neighbourhood indicator at a reduced frequency `(a+sq)/(qc)`, rescaled by `c`. -/
lemma perNbhd_eq_scaled (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff) (q a s : ℕ) (hq : 1 ≤ q)
    (θ r : ℝ) :
    Commons.Analysis.ExponentialSums.perNbhd
        (((a:ℝ) + (s:ℝ)*(q:ℝ)) / ((q:ℝ)*(P.leadingCoeff:ℝ))) r θ
      = (if ∃ m : ℤ, |(P.leadingCoeff:ℝ)*θ + (m:ℝ)*(P.leadingCoeff:ℝ)
            - ((a:ℝ)/(q:ℝ) + (s:ℝ))| ≤ (P.leadingCoeff:ℝ)*r then (1:ℂ) else 0) := by
  have hc0 : (0:ℝ) < (P.leadingCoeff:ℝ) := by exact_mod_cast hc
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hqne : (q:ℝ) ≠ 0 := ne_of_gt hq0
  have hcne : (P.leadingCoeff:ℝ) ≠ 0 := ne_of_gt hc0
  have hcl : (P.leadingCoeff:ℝ) * (((a:ℝ) + (s:ℝ)*(q:ℝ)) / ((q:ℝ)*(P.leadingCoeff:ℝ)))
      = (a:ℝ)/(q:ℝ) + (s:ℝ) := by
    field_simp
  rw [Commons.Analysis.ExponentialSums.perNbhd]
  have hiff : (∃ l : ℤ, |θ + (l:ℝ) - (((a:ℝ) + (s:ℝ)*(q:ℝ)) / ((q:ℝ)*(P.leadingCoeff:ℝ)))| ≤ r)
      ↔ (∃ m : ℤ, |(P.leadingCoeff:ℝ)*θ + (m:ℝ)*(P.leadingCoeff:ℝ)
            - ((a:ℝ)/(q:ℝ) + (s:ℝ))| ≤ (P.leadingCoeff:ℝ)*r) := by
    apply exists_congr
    intro m
    have hkey : (P.leadingCoeff:ℝ)*θ + (m:ℝ)*(P.leadingCoeff:ℝ) - ((a:ℝ)/(q:ℝ) + (s:ℝ))
        = (P.leadingCoeff:ℝ) * (θ + (m:ℝ)
            - (((a:ℝ) + (s:ℝ)*(q:ℝ)) / ((q:ℝ)*(P.leadingCoeff:ℝ)))) := by
      rw [mul_sub, hcl]
      ring
    rw [hkey]
    constructor
    · intro hm
      have h2 : (P.leadingCoeff:ℝ) * |θ + (m:ℝ)
            - (((a:ℝ) + (s:ℝ)*(q:ℝ)) / ((q:ℝ)*(P.leadingCoeff:ℝ)))|
          ≤ (P.leadingCoeff:ℝ)*r := mul_le_mul_of_nonneg_left hm (le_of_lt hc0)
      rwa [abs_mul, abs_of_pos hc0]
    · intro hm
      have hm' : (P.leadingCoeff:ℝ) * |θ + (m:ℝ)
            - (((a:ℝ) + (s:ℝ)*(q:ℝ)) / ((q:ℝ)*(P.leadingCoeff:ℝ)))|
          ≤ (P.leadingCoeff:ℝ)*r := by
        rwa [abs_mul, abs_of_pos hc0] at hm
      exact (mul_le_mul_iff_of_pos_left hc0).mp hm'
  rw [hiff]

/-- **The `l`-window of a block collapses to a periodised-neighbourhood sum.**  Let `c = P.leadingCoeff > 0`, `1 ≤ q`, `a < q`, and let `r = (polyDil P k)⁻¹ = (2^k)^{-d}` be the sharp window radius, assumed `< 1/(2c)`.  Then for `θ ∈ (0,1)` the sum over the window `l ∈ [-1,c]` of the sharp indicators at the `c`-scaled frequencies `(a/q + l)/c` equals the sum over `s ∈ [0,c)` of the periodised neighbourhood indicators at the reduced frequencies `(a + s q)/(q c)` and the same radius.

Both sides are `0`-or-`1`-valued: rewrite the window condition `|polyDil P k * (θ - (a/q+l)/c)| ≤ 1` as `|θ - (a/q+l)/c| ≤ (polyDil P k)⁻¹`, note that the frequencies `(a/q+l)/c`, `l ∈ ℤ`, are spaced `1/c > 2r`, so at most one `l` is active, and that an active `l` satisfies `l ∈ [-1,c]` because `cθ ∈ (0,c)` and `a/q ∈ [0,1)` while `cr < 1/2`; then use the bijection `l ↦ l mod c` between the possible active `l ∈ [-1,c]` and the residues `s ∈ [0,c)`, and `perNbhd_eq_one`/`perNbhd_ne_zero` from `Commons.Analysis.ExponentialSums`. -/
theorem poly_sharp_core_periodic (P : Polynomial ℤ) (hc : 0 < P.leadingCoeff)
    (hd : 2 ≤ P.natDegree) {q a : ℕ} (hq : 1 ≤ q) (ha : a < q) {k : ℕ}
    (hsmall : (polyDil P k)⁻¹ < 1 / (2 * (P.leadingCoeff : ℝ))) (θ : ℝ) (hθ0 : 0 < θ)
    (hθ1 : θ < 1) :
    (∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
        (if |polyDil P k * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1
          then (1:ℂ) else 0))
      = ∑ s ∈ Finset.range (P.leadingCoeff.toNat),
          Commons.Analysis.ExponentialSums.perNbhd
            (((a:ℝ) + (s:ℝ) * (q:ℝ)) / ((q:ℝ) * (P.leadingCoeff:ℝ)))
            ((polyDil P k)⁻¹) θ := by
  classical
  have hc0 : (0:ℝ) < (P.leadingCoeff:ℝ) := by exact_mod_cast hc
  have hq0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hCZ : ((P.leadingCoeff.toNat : ℕ) : ℤ) = P.leadingCoeff := Int.toNat_of_nonneg (le_of_lt hc)
  have hCR : ((P.leadingCoeff.toNat : ℕ) : ℝ) = (P.leadingCoeff:ℝ) := by exact_mod_cast hCZ
  have hK : 1 ≤ P.leadingCoeff.toNat := by
    have h1 : (1:ℤ) ≤ ((P.leadingCoeff.toNat : ℕ) : ℤ) := by rw [hCZ]; omega
    exact_mod_cast h1
  have hrpos : 0 < (polyDil P k)⁻¹ := inv_pos.mpr (polyDil_pos P k)
  have hρlt : (P.leadingCoeff:ℝ) * (polyDil P k)⁻¹ < 1/2 := by
    have h1 : (polyDil P k)⁻¹ * (P.leadingCoeff:ℝ)
        < (1/(2*(P.leadingCoeff:ℝ))) * (P.leadingCoeff:ℝ) :=
      mul_lt_mul_of_pos_right hsmall hc0
    have h2 : (1/(2*(P.leadingCoeff:ℝ))) * (P.leadingCoeff:ℝ) = 1/2 := by
      field_simp
    rw [h2] at h1
    rw [mul_comm (P.leadingCoeff:ℝ) (polyDil P k)⁻¹]
    exact h1
  have hgen := sharpCore_sum_eq_periodic_scaled (P.leadingCoeff.toNat) hK
      ((a:ℝ)/(q:ℝ)) ((P.leadingCoeff:ℝ)*θ) ((P.leadingCoeff:ℝ)*(polyDil P k)⁻¹)
      (div_nonneg (Nat.cast_nonneg a) (le_of_lt hq0))
      ((div_lt_one hq0).mpr (by exact_mod_cast ha))
      (mul_pos hc0 hθ0)
      (by rw [hCR]; exact mul_lt_of_lt_one_right hc0 hθ1)
      (mul_pos hc0 hrpos) hρlt
  rw [hCR] at hgen
  have hL : (∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
        (if |polyDil P k * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1
          then (1:ℂ) else 0))
      = (∑ l ∈ Finset.Icc (-1 : ℤ) P.leadingCoeff,
        (if |(P.leadingCoeff:ℝ)*θ - (a:ℝ)/(q:ℝ) - (l:ℝ)|
            ≤ (P.leadingCoeff:ℝ)*(polyDil P k)⁻¹ then (1:ℂ) else 0)) :=
    Finset.sum_congr rfl (fun l _ => by
      by_cases h : |polyDil P k * (θ - (((a:ℝ)/(q:ℝ) + (l:ℝ)) / (P.leadingCoeff:ℝ)))| ≤ 1
      · rw [if_pos h, if_pos ((sharp_iff_scaled P hc q a hq θ l).mp h)]
      · rw [if_neg h,
          if_neg (fun hh => h ((sharp_iff_scaled P hc q a hq θ l).mpr hh))])
  have hset : Finset.Icc (-1 : ℤ) P.leadingCoeff
      = Finset.Icc (-1 : ℤ) ((P.leadingCoeff.toNat : ℕ) : ℤ) := by rw [hCZ]
  have hR : (∑ s ∈ Finset.range (P.leadingCoeff.toNat),
          Commons.Analysis.ExponentialSums.perNbhd
            (((a:ℝ) + (s:ℝ) * (q:ℝ)) / ((q:ℝ) * (P.leadingCoeff:ℝ)))
            ((polyDil P k)⁻¹) θ)
      = (∑ s ∈ Finset.range (P.leadingCoeff.toNat),
          (if ∃ m : ℤ, |(P.leadingCoeff:ℝ)*θ + (m:ℝ)*(P.leadingCoeff:ℝ)
            - ((a:ℝ)/(q:ℝ) + (s:ℝ))| ≤ (P.leadingCoeff:ℝ)*((polyDil P k)⁻¹)
            then (1:ℂ) else 0)) :=
    Finset.sum_congr rfl
      (fun s _ => perNbhd_eq_scaled P hc q a s hq θ ((polyDil P k)⁻¹))
  rw [hL, hset, hgen, ← hR]

end Work.BourgainPlan.Maximal
