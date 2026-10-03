import Mathlib

namespace Work.A3

/-- For `0 ≤ r ≤ 3/4`, the partial geometric sums of `r` are bounded by `4`
(the full sum being `1/(1-r) ≤ 4`). -/
private lemma geom_sum_range_le_four {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 3/4) (N : ℕ) :
    ∑ a ∈ Finset.range N, r ^ a ≤ 4 := by
  have hr1 : r < 1 := by linarith
  have hAS := hasSum_geometric_of_lt_one h0 hr1
  have hle : ∑ a ∈ Finset.range N, r ^ a ≤ (1 - r)⁻¹ := by
    have h := hAS.summable.sum_le_tsum (Finset.range N) (fun i _ => pow_nonneg h0 i)
    rwa [hAS.tsum_eq] at h
  have hpos : 0 < 1 - r := by linarith
  have h4 : (1 - r)⁻¹ ≤ 4 := by
    rw [inv_le_iff_one_le_mul₀ hpos]
    linarith
  linarith

/-- Among the nonzero multiples of `p` below `p^ν` whose `p`-adic valuation is exactly `a`
(`a < ν`), there are at most `p^(ν-a)`: the map `h ↦ h / p^a` is injective into `{0,…,p^(ν-a)-1}`. -/
private lemma fiber_card_le (p ν a : ℕ) (hp : p.Prime) (ha : a < ν) :
    (((Finset.range (p ^ ν)).filter (fun h => h ≠ 0)).filter
        (fun h => h.factorization p = a)).card ≤ p ^ (ν - a) := by
  classical
  have hpa : 0 < p ^ a := pow_pos hp.pos a
  have hle : a ≤ ν := le_of_lt ha
  have hff : Set.MapsTo (fun h => h / p ^ a)
        ↑(((Finset.range (p ^ ν)).filter (fun h => h ≠ 0)).filter
        (fun h => h.factorization p = a)) ↑(Finset.range (p ^ (ν - a))) := by
    intro h hh
    rw [Finset.mem_coe, Finset.mem_range] at *
    obtain ⟨hh1, hfac⟩ := Finset.mem_filter.mp hh
    obtain ⟨hh2, hne⟩ := Finset.mem_filter.mp hh1
    have hlt : h < p ^ ν := Finset.mem_range.mp hh2
    have hdvd : p ^ a ∣ h := (hp.pow_dvd_iff_le_factorization hne).mpr (le_of_eq hfac.symm)
    have hmul : p ^ a * (h / p ^ a) = h := Nat.mul_div_cancel' hdvd
    have : p ^ a * (h / p ^ a) < p ^ a * p ^ (ν - a) := by
      rw [hmul, ← pow_add, Nat.add_sub_cancel' hle]
      exact hlt
    exact (Nat.mul_lt_mul_left hpa).mp this
  have hinj : Set.InjOn (fun h => h / p ^ a)
        ↑(((Finset.range (p ^ ν)).filter (fun h => h ≠ 0)).filter
        (fun h => h.factorization p = a)) := by
    intro h1 hh1 h2 hh2 heq
    rw [Finset.mem_coe] at hh1 hh2
    obtain ⟨hh1a, hf1⟩ := Finset.mem_filter.mp hh1
    obtain ⟨hh2a, hf2⟩ := Finset.mem_filter.mp hh2
    have hne1 : h1 ≠ 0 := (Finset.mem_filter.mp hh1a).2
    have hne2 : h2 ≠ 0 := (Finset.mem_filter.mp hh2a).2
    have hd1 : p ^ a ∣ h1 := (hp.pow_dvd_iff_le_factorization hne1).mpr (le_of_eq hf1.symm)
    have hd2 : p ^ a ∣ h2 := (hp.pow_dvd_iff_le_factorization hne2).mpr (le_of_eq hf2.symm)
    have heq' : h1 / p ^ a = h2 / p ^ a := heq
    rw [← Nat.mul_div_cancel' hd1, ← Nat.mul_div_cancel' hd2, heq']
  simpa using Finset.card_le_card_of_injOn (fun h => h / p ^ a) hff hinj

/-- Grouping the sum `∑_{1 ≤ h < p^ν} p^{-(ν - v_p(h))η}` by `a = v_p(h)` and bounding each
level set by `p^{ν-a}`, the sum is dominated by the geometric series
`∑_{a<ν} p^{ν-a} p^{-(ν-a)η}`, whose ratio is `p^{-(1-η)} ≤ 3/4` (here `η ≤ 1/2`, `p ≥ 2`),
whence the factor `4`. -/
lemma sum_factorization_rpow_le (p ν : ℕ) (hp : p.Prime) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1/2) :
    ∑ h ∈ (Finset.range (p ^ ν)).filter (fun h => h ≠ 0),
        (p : ℝ) ^ (-(((ν - h.factorization p : ℕ) : ℝ) * η))
      ≤ 4 * (p : ℝ) ^ ((ν : ℝ) * (1 - η)) := by
  classical
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hpnn : (0:ℝ) ≤ p := hp0.le
  -- `p^{1-η} ≥ 4/3`
  have hp43 : (4/3 : ℝ) ≤ (p:ℝ) ^ (1 - η) := by
    have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    have h43 : (4/3 : ℝ) ≤ (2:ℝ) ^ ((1:ℝ)/2) := by
      have h1 : (4/3:ℝ) ≤ Real.sqrt 2 := by
        rw [Real.le_sqrt (by norm_num) (by norm_num)]
        norm_num
      rwa [Real.sqrt_eq_rpow] at h1
    have h2' : (2:ℝ) ^ ((1:ℝ)/2) ≤ (2:ℝ) ^ (1 - η) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith
    have h3 : (2:ℝ) ^ (1 - η) ≤ (p:ℝ) ^ (1 - η) :=
      Real.rpow_le_rpow (by norm_num) h2 (by linarith)
    linarith
  -- the geometric ratio `r = p^{-(1-η)}`
  set r : ℝ := (p:ℝ) ^ (-(1 - η)) with hr
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.rpow_nonneg hpnn _
  have hr34 : r ≤ 3/4 := by
    rw [hr, Real.rpow_neg hpnn]
    have hpos : 0 < (p:ℝ)^(1-η) := Real.rpow_pos_of_pos hp0 _
    have h1 : ((p:ℝ)^(1-η))⁻¹ ≤ ((4/3:ℝ))⁻¹ := (inv_le_inv₀ hpos (by norm_num)).mpr hp43
    rwa [show ((4/3:ℝ))⁻¹ = 3/4 by norm_num] at h1
  set S := (Finset.range (p ^ ν)).filter (fun h => h ≠ 0) with hS
  -- the valuation of every element of `S` is `< ν`
  have hmaps : ∀ h ∈ S, h.factorization p ∈ Finset.range ν := by
    intro h hh
    rw [Finset.mem_range]
    by_contra hcon
    push Not at hcon
    have hh' : h ∈ (Finset.range (p ^ ν)).filter (fun h => h ≠ 0) := hS ▸ hh
    obtain ⟨hh2, hne⟩ := Finset.mem_filter.mp hh'
    have hlt : h < p ^ ν := Finset.mem_range.mp hh2
    have hdvd : p ^ ν ∣ h := (hp.pow_dvd_iff_le_factorization hne).mpr hcon
    have hle : p ^ ν ≤ h := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hdvd
    exact absurd hlt (not_lt.mpr hle)
  -- split the sum into the level sets of the valuation
  have hsplit : ∑ h ∈ S, (p:ℝ)^(-(((ν - h.factorization p : ℕ) : ℝ) * η))
      = ∑ a ∈ Finset.range ν, ∑ h ∈ S.filter (fun h => h.factorization p = a),
          (p:ℝ)^(-(((ν - h.factorization p : ℕ) : ℝ) * η)) :=
    (Finset.sum_fiberwise_of_maps_to hmaps _).symm
  rw [hsplit]
  calc ∑ a ∈ Finset.range ν, ∑ h ∈ S.filter (fun h => h.factorization p = a),
          (p:ℝ)^(-(((ν - h.factorization p : ℕ) : ℝ) * η))
      ≤ ∑ a ∈ Finset.range ν, (p:ℝ)^(ν-a) * (p:ℝ)^(-(((ν - a : ℕ) : ℝ) * η)) := by
        apply Finset.sum_le_sum
        intro a ha
        have haν : a < ν := Finset.mem_range.mp ha
        -- on a level set the summand is constant
        have hconst : ∀ h ∈ S.filter (fun h => h.factorization p = a),
            (p:ℝ)^(-(((ν - h.factorization p : ℕ) : ℝ) * η))
              = (p:ℝ)^(-(((ν - a : ℕ) : ℝ) * η)) := by
          intro h hh
          rw [(Finset.mem_filter.mp hh).2]
        have hsum1 : ∑ h ∈ S.filter (fun h => h.factorization p = a),
            (p:ℝ)^(-(((ν - h.factorization p : ℕ) : ℝ) * η))
            = ((S.filter (fun h => h.factorization p = a)).card : ℝ)
                * (p:ℝ)^(-(((ν - a : ℕ) : ℝ) * η)) := by
          rw [Finset.sum_congr rfl hconst, Finset.sum_const, nsmul_eq_mul]
        rw [hsum1]
        -- the level set has at most `p^(ν-a)` elements
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hpnn _)
        have hc := fiber_card_le p ν a hp haν
        rw [hS]
        exact_mod_cast hc
    _ = (p:ℝ)^((ν:ℝ)*(1-η)) * ∑ a ∈ Finset.range ν, r^a := by
        rw [Finset.sum_congr rfl (fun a ha => ?_), Finset.mul_sum]
        have haν : a ≤ ν := le_of_lt (Finset.mem_range.mp ha)
        -- each term is `p^{ν(1-η)} r^a`
        calc (p:ℝ)^(ν-a) * (p:ℝ)^(-(((ν - a : ℕ) : ℝ) * η))
            = (p:ℝ)^((((ν - a : ℕ) : ℝ))) * (p:ℝ)^(-(((ν - a : ℕ) : ℝ) * η)) := by
              rw [← Real.rpow_natCast (p:ℝ) (ν-a)]
          _ = (p:ℝ)^((((ν - a : ℕ) : ℝ)) + (-(((ν - a : ℕ) : ℝ) * η))) := by
              rw [← Real.rpow_add hp0]
          _ = (p:ℝ)^((((ν - a : ℕ) : ℝ)) * (1 - η)) := by
                rw [show (((ν - a : ℕ) : ℝ)) + (-(((ν - a : ℕ) : ℝ) * η))
                      = (((ν - a : ℕ) : ℝ)) * (1 - η) by ring]
          _ = (p:ℝ)^(((ν:ℝ) - (a:ℝ)) * (1-η)) := by rw [Nat.cast_sub haν]
          _ = (p:ℝ)^(((ν:ℝ)*(1-η)) + (-(1-η)*(a:ℝ))) := by
                rw [show ((ν:ℝ)-(a:ℝ))*(1-η) = (ν:ℝ)*(1-η) + (-(1-η)*(a:ℝ)) by ring]
          _ = (p:ℝ)^((ν:ℝ)*(1-η)) * (p:ℝ)^(-(1-η)*(a:ℝ)) := by rw [Real.rpow_add hp0]
          _ = (p:ℝ)^((ν:ℝ)*(1-η)) * r^a := by
                rw [hr, ← Real.rpow_natCast ((p:ℝ)^(-(1-η))) a, ← Real.rpow_mul hpnn]
    _ ≤ (p:ℝ)^((ν:ℝ)*(1-η)) * 4 :=
        mul_le_mul_of_nonneg_left (geom_sum_range_le_four hr0 hr34 ν) (Real.rpow_nonneg hpnn _)
    _ = 4 * (p:ℝ)^((ν:ℝ)*(1-η)) := by ring

end Work.A3
