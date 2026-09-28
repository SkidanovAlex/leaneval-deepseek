import Mathlib

open Finset

namespace Work.HP

lemma dyIdx_exists (u : ℝ) : ∃ i : ℕ, u ≤ (2:ℝ)^i := by
  refine ⟨⌈u⌉₊, ?_⟩
  have h1 : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
  have h2 : (⌈u⌉₊ : ℝ) ≤ (2:ℝ)^⌈u⌉₊ := by
    have h := @Nat.lt_two_pow_self ⌈u⌉₊
    have h3 : ((⌈u⌉₊ : ℕ) : ℝ) < ((2:ℝ)^⌈u⌉₊) := by exact_mod_cast h
    linarith
  linarith

noncomputable def dyIdx (u : ℝ) : ℕ := Nat.find (dyIdx_exists u)

lemma le_pow_dyIdx (u : ℝ) : u ≤ (2:ℝ)^(dyIdx u) := by
  unfold dyIdx; exact Nat.find_spec (dyIdx_exists u)

lemma dyIdx_le_iff {u : ℝ} {i : ℕ} (h : u ≤ (2:ℝ)^i) : dyIdx u ≤ i := by
  unfold dyIdx; exact Nat.find_min' (dyIdx_exists u) h

lemma dyIdx_mono {u v : ℝ} (h : u ≤ v) : dyIdx u ≤ dyIdx v :=
  dyIdx_le_iff (le_trans h (le_pow_dyIdx v))

lemma pow_dyIdx_le {u : ℝ} (hu : 1 ≤ u) : (2:ℝ)^(dyIdx u) ≤ 2*u := by
  unfold dyIdx
  set m := Nat.find (dyIdx_exists u) with hm
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · rw [h0]; norm_num; linarith
  · have hmin : ¬ (u ≤ (2:ℝ)^(m - 1)) := Nat.find_min (dyIdx_exists u) (by omega)
    have hlt : (2:ℝ)^(m - 1) < u := not_le.mp hmin
    have hpow : (2:ℝ)^m = (2:ℝ)^(m - 1) * 2 := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hpos]
      rw [pow_succ, Nat.pred_eq_sub_one]
    rw [hpow]; linarith

theorem sum_comp_image_eq {ι κ : Type*} [DecidableEq κ] (s : Finset ι) (g : ι → κ) (G : κ → ℝ) :
    ∑ p ∈ s, G (g p) = ∑ c ∈ s.image g, ((s.filter (fun p => g p = c)).card : ℝ) * G c := by
  have h1 : (∑ p ∈ s, G (g p)) = ∑ p ∈ s with g p ∈ s.image g, G (g p) := by
    rw [Finset.filter_true_of_mem]
    intro p hp; exact Finset.mem_image_of_mem g hp
  rw [h1, ← Finset.sum_fiberwise_eq_sum_filter' s (s.image g) g G]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  rw [Finset.sum_const, nsmul_eq_mul]

lemma rpow_div_le {r : ℝ} (hr : 0 ≤ r) {u : ℝ} {m : ℕ} (hu : (2:ℝ)^m ≤ 2*u) :
    (2:ℝ)^(r*(m:ℝ)) / u^r ≤ (2:ℝ)^r := by
  have hu0 : 0 < u := by
    have h1 : (1:ℝ) ≤ (2:ℝ)^m := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    linarith
  rcases eq_or_lt_of_le hr with h0 | hpos
  · rw [← h0]; simp
  · rw [div_le_iff₀ (Real.rpow_pos_of_pos hu0 r)]
    rw [← Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hu0.le]
    have hL : (2:ℝ)^(r*(m:ℝ)) = ((2:ℝ)^m)^r := by
      rw [show r*(m:ℝ) = (m:ℝ)*r by ring,
          Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (m:ℝ) r, Real.rpow_natCast]
    rw [hL, Real.rpow_le_rpow_iff (by positivity) (by positivity) hpos]
    exact hu

theorem term_le_rpow {t s : ℝ} (ht : 0 < t) (hs : 0 ≤ s) {D x y : ℝ} {i j k : ℕ}
    (hD : (2:ℝ)^k ≤ 2*D) (hx : (2:ℝ)^i ≤ 2*x) (hy : (2:ℝ)^j ≤ 2*y) :
    1 / (D^t * x^s * y^s)
      ≤ (2:ℝ)^(t + 2*s) * (2:ℝ)^(-(t*(k:ℝ) + s*(i:ℝ) + s*(j:ℝ))) := by
  have hD0 : 0 < D := by
    have h1 : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    linarith
  have hx0 : 0 < x := by
    have h1 : (1:ℝ) ≤ (2:ℝ)^i := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    linarith
  have hy0 : 0 < y := by
    have h1 : (1:ℝ) ≤ (2:ℝ)^j := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
    linarith
  have hDp : 0 < D^t := Real.rpow_pos_of_pos hD0 t
  have hxp : 0 < x^s := Real.rpow_pos_of_pos hx0 s
  have hyp : 0 < y^s := Real.rpow_pos_of_pos hy0 s
  have hA : (2:ℝ)^(t*(k:ℝ) + s*(i:ℝ) + s*(j:ℝ))
      = (2:ℝ)^(t*(k:ℝ)) * (2:ℝ)^(s*(i:ℝ)) * (2:ℝ)^(s*(j:ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  have hprod : (2:ℝ)^(t*(k:ℝ) + s*(i:ℝ) + s*(j:ℝ)) / (D^t * x^s * y^s)
      = ((2:ℝ)^(t*(k:ℝ))/D^t) * ((2:ℝ)^(s*(i:ℝ))/x^s) * ((2:ℝ)^(s*(j:ℝ))/y^s) := by
    rw [hA]; field_simp
  have hgen : (2:ℝ)^(t*(k:ℝ) + s*(i:ℝ) + s*(j:ℝ)) / (D^t * x^s * y^s) ≤ (2:ℝ)^(t + 2*s) := by
    rw [hprod]
    have e1 := rpow_div_le ht.le hD
    have e2 := rpow_div_le hs hx
    have e3 := rpow_div_le hs hy
    calc ((2:ℝ)^(t*(k:ℝ))/D^t) * ((2:ℝ)^(s*(i:ℝ))/x^s) * ((2:ℝ)^(s*(j:ℝ))/y^s)
        ≤ (2:ℝ)^t * (2:ℝ)^s * (2:ℝ)^s := by
          apply mul_le_mul (mul_le_mul e1 e2 (by positivity) (by positivity)) e3 (by positivity) (by positivity)
      _ = (2:ℝ)^(t+2*s) := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          congr 1; ring
  have hpos2 : 0 < (2:ℝ)^(-(t*(k:ℝ) + s*(i:ℝ) + s*(j:ℝ))) := Real.rpow_pos_of_pos (by norm_num) _
  have hfin : (2:ℝ)^(-(t*(k:ℝ) + s*(i:ℝ) + s*(j:ℝ))) * ((2:ℝ)^(t*(k:ℝ) + s*(i:ℝ) + s*(j:ℝ)) / (D^t*x^s*y^s))
      ≤ (2:ℝ)^(-(t*(k:ℝ) + s*(i:ℝ) + s*(j:ℝ))) * (2:ℝ)^(t+2*s) :=
    mul_le_mul_of_nonneg_left hgen hpos2.le
  have hL : (2:ℝ)^(-(t*(k:ℝ) + s*(i:ℝ) + s*(j:ℝ))) * ((2:ℝ)^(t*(k:ℝ) + s*(i:ℝ) + s*(j:ℝ)) / (D^t*x^s*y^s))
      = 1 / (D^t*x^s*y^s) := by
    rw [← mul_div_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2), neg_add_cancel, Real.rpow_zero]
  rw [hL] at hfin
  calc 1/(D^t*x^s*y^s) ≤ (2:ℝ)^(-(t*(k:ℝ)+s*(i:ℝ)+s*(j:ℝ))) * (2:ℝ)^(t+2*s) := hfin
    _ = (2:ℝ)^(t+2*s) * (2:ℝ)^(-(t*(k:ℝ)+s*(i:ℝ)+s*(j:ℝ))) := by ring

lemma geom_le_pow {r : ℝ} (hr : 2 ≤ r) (n : ℕ) : ∑ i ∈ Finset.range n, r^i ≤ r^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h0 : (0:ℝ) ≤ r^n := by positivity
    nlinarith [ih, h0, hr]

theorem geom_fiber_sum_bound (β Q : ℝ) (hβ : 0 < β) (hQ : 1 ≤ Q) (K : Finset ℕ)
    (h : ∀ k ∈ K, (2:ℝ)^k ≤ Q) :
    ∑ k ∈ K, (2:ℝ)^(β * (k:ℝ)) ≤ ((2:ℝ)^β / ((2:ℝ)^β - 1)) * Q^β := by
  have hr : (1:ℝ) < (2:ℝ)^β := Real.one_lt_rpow (by norm_num : (1:ℝ) < 2) hβ
  have hpos : 0 < ((2:ℝ)^β / ((2:ℝ)^β - 1)) * Q^β := by
    apply mul_pos (div_pos (Real.rpow_pos_of_pos (by norm_num) β) (by linarith))
    exact Real.rpow_pos_of_pos (by linarith) β
  rcases Finset.eq_empty_or_nonempty K with hK | hK
  · rw [hK, Finset.sum_empty]; exact le_of_lt hpos
  · set M := K.max' hK with hM
    have hMmem : M ∈ K := Finset.max'_mem K hK
    have hMle : ∀ k ∈ K, k ≤ M := fun k hk => Finset.le_max' K k hk
    have hQM : (2:ℝ)^M ≤ Q := h M hMmem
    have hsub : K ⊆ Finset.range (M+1) := fun k hk => Finset.mem_range.mpr (Nat.lt_succ_of_le (hMle k hk))
    have hstep1 : ∑ k ∈ K, (2:ℝ)^(β*(k:ℝ)) ≤ ∑ k ∈ Finset.range (M+1), (2:ℝ)^(β*(k:ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro k hk _
      positivity
    refine le_trans hstep1 ?_
    have hstep2 : (∑ k ∈ Finset.range (M+1), (2:ℝ)^(β*(k:ℝ))) = ∑ k ∈ Finset.range (M+1), ((2:ℝ)^β)^k := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) β (k:ℝ), Real.rpow_natCast]
    rw [hstep2, geom_sum_eq (ne_of_gt hr) (M+1)]
    have hden : (0:ℝ) < (2:ℝ)^β - 1 := by linarith
    have hnum : ((2:ℝ)^β)^(M+1) - 1 ≤ ((2:ℝ)^β)^M * (2:ℝ)^β := by
      rw [pow_succ]; linarith
    have hQM' : ((2:ℝ)^β)^M ≤ Q^β := by
      rw [← Real.rpow_natCast ((2:ℝ)^β) M,
          ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) β (M:ℝ)]
      rw [show β*(↑M:ℝ) = (↑M:ℝ)*β by ring,
          Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (M:ℝ) β, Real.rpow_natCast]
      exact Real.rpow_le_rpow (by positivity) hQM hβ.le
    calc (((2:ℝ)^β)^(M+1) - 1) / ((2:ℝ)^β - 1)
        ≤ (((2:ℝ)^β)^M * (2:ℝ)^β) / ((2:ℝ)^β - 1) := div_le_div_of_nonneg_right hnum hden.le
      _ ≤ ((2:ℝ)^β * Q^β) / ((2:ℝ)^β - 1) := by
          apply div_le_div_of_nonneg_right _ hden.le
          calc ((2:ℝ)^β)^M * (2:ℝ)^β ≤ Q^β * (2:ℝ)^β := mul_le_mul_of_nonneg_right hQM' (by positivity)
            _ = (2:ℝ)^β * Q^β := by ring
      _ = ((2:ℝ)^β / ((2:ℝ)^β - 1)) * Q^β := by ring

lemma inner_sum_bound {β : ℝ} (hβ : 0 < β) {V : ℝ} (hV : 1 ≤ V) (i j N : ℕ) :
    ∑ k ∈ (Finset.range N).filter (fun k => (2:ℝ)^k * V ≤ (2:ℝ)^(i+j+1)),
      (2:ℝ)^(β*(k:ℝ))
    ≤ ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^(i+j+1)/V)^β := by
  set K := (Finset.range N).filter (fun k => (2:ℝ)^k * V ≤ (2:ℝ)^(i+j+1)) with hK
  rcases Finset.eq_empty_or_nonempty K with h | h
  · rw [h, Finset.sum_empty]
    apply le_of_lt
    apply mul_pos (div_pos (Real.rpow_pos_of_pos (by norm_num) β) (by linarith [Real.one_lt_rpow (by norm_num : (1:ℝ) < 2) hβ]))
    exact Real.rpow_pos_of_pos (div_pos (by positivity) (by linarith)) β
  · have hV0 : (0:ℝ) < V := by linarith
    have hQ1 : (1:ℝ) ≤ (2:ℝ)^(i+j+1)/V := by
      obtain ⟨k, hk⟩ := h
      rw [hK, Finset.mem_filter, Finset.mem_range] at hk
      have h2k : (1:ℝ) ≤ (2:ℝ)^k := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)
      have hle : V ≤ (2:ℝ)^(i+j+1) := by
        calc V = 1*V := by ring
          _ ≤ (2:ℝ)^k * V := mul_le_mul_of_nonneg_right h2k (by linarith)
          _ ≤ (2:ℝ)^(i+j+1) := hk.2
      rw [le_div_iff₀ hV0]; simpa using hle
    have hbound : ∀ k ∈ K, (2:ℝ)^k ≤ (2:ℝ)^(i+j+1)/V := by
      intro k hk
      rw [hK, Finset.mem_filter] at hk
      rw [le_div_iff₀ hV0]
      exact hk.2
    exact geom_fiber_sum_bound β ((2:ℝ)^(i+j+1)/V) hβ hQ1 K hbound

theorem box_dyadic_sum {α β γ : ℝ} (hγ : γ = α + β) (hβ : 0 < β) (hγ1 : 1 ≤ γ)
    {V : ℝ} (hV : 1 ≤ V) (L : ℕ) :
    ∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (L+1),
      ∑ k ∈ (Finset.range (2*L+2)).filter (fun k => (2:ℝ)^k * V ≤ (2:ℝ)^(i+j+1)),
        (2:ℝ)^(α*(i:ℝ)) * (2:ℝ)^(α*(j:ℝ)) * (2:ℝ)^(β*(k:ℝ))
    ≤ ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β) * ((2:ℝ)^(γ*((L:ℝ)+1)))^2 := by
  have hV0 : (0:ℝ) < V := by linarith
  have hγpos : (0:ℝ) < γ := by linarith
  have hcpos : (0:ℝ) < (2:ℝ)^β / ((2:ℝ)^β - 1) :=
    div_pos (Real.rpow_pos_of_pos (by norm_num) β)
      (by linarith [Real.one_lt_rpow (by norm_num : (1:ℝ) < 2) hβ])
  have hXnn : (0:ℝ) ≤ ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β) :=
    le_of_lt (mul_pos hcpos (div_pos (Real.rpow_pos_of_pos (by norm_num) β) (Real.rpow_pos_of_pos hV0 β)))
  have h2r : (2:ℝ) ≤ (2:ℝ)^γ := by
    calc (2:ℝ) = (2:ℝ)^(1:ℝ) := (Real.rpow_one 2).symm
      _ ≤ (2:ℝ)^γ := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hγ1
  have geomL : (∑ i ∈ Finset.range (L+1), (2:ℝ)^(γ*(i:ℝ))) ≤ (2:ℝ)^(γ*((L:ℝ)+1)) := by
    have hgc : (∑ i ∈ Finset.range (L+1), (2:ℝ)^(γ*(i:ℝ)))
        = ∑ i ∈ Finset.range (L+1), ((2:ℝ)^γ)^i := by
      apply Finset.sum_congr rfl; intro i hi
      rw [Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) γ (i:ℝ), Real.rpow_natCast]
    rw [hgc]
    refine le_trans (geom_le_pow h2r (L+1)) ?_
    refine le_of_eq ?_
    rw [← Real.rpow_natCast ((2:ℝ)^γ) (L+1),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) γ (((L+1 : ℕ) : ℝ))]
    congr 1
    simp only [Nat.cast_add, Nat.cast_one]
  have hpair : ∀ i j : ℕ,
      (∑ k ∈ (Finset.range (2*L+2)).filter (fun k => (2:ℝ)^k * V ≤ (2:ℝ)^(i+j+1)),
        (2:ℝ)^(α*(i:ℝ)) * (2:ℝ)^(α*(j:ℝ)) * (2:ℝ)^(β*(k:ℝ)))
      ≤ ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β)
        * ((2:ℝ)^(γ*(i:ℝ)) * (2:ℝ)^(γ*(j:ℝ))) := by
    intro i j
    have h1 : (∑ k ∈ (Finset.range (2*L+2)).filter (fun k => (2:ℝ)^k * V ≤ (2:ℝ)^(i+j+1)),
        (2:ℝ)^(α*(i:ℝ)) * (2:ℝ)^(α*(j:ℝ)) * (2:ℝ)^(β*(k:ℝ)))
        = (2:ℝ)^(α*(i:ℝ)) * (2:ℝ)^(α*(j:ℝ)) *
          (∑ k ∈ (Finset.range (2*L+2)).filter (fun k => (2:ℝ)^k * V ≤ (2:ℝ)^(i+j+1)),
            (2:ℝ)^(β*(k:ℝ))) := by
      rw [Finset.mul_sum]
    rw [h1]
    refine le_trans (mul_le_mul_of_nonneg_left (inner_sum_bound hβ hV i j (2*L+2)) (by positivity)) ?_
    have halg : (2:ℝ)^(α*(i:ℝ)) * (2:ℝ)^(α*(j:ℝ)) *
          (((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^(i+j+1)/V)^β)
        = ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β)
          * ((2:ℝ)^(γ*(i:ℝ)) * (2:ℝ)^(γ*(j:ℝ))) := by
      calc (2:ℝ)^(α*(i:ℝ)) * (2:ℝ)^(α*(j:ℝ)) * (((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^(i+j+1)/V)^β)
          = ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^(α*(i:ℝ)) * (2:ℝ)^(α*(j:ℝ)) * ((2:ℝ)^(i+j+1))^β) / V^β := by
            rw [Real.div_rpow (by positivity) hV0.le]; ring
        _ = ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^(α*(i:ℝ)) * (2:ℝ)^(α*(j:ℝ)) * (2:ℝ)^(((i:ℝ)+(j:ℝ)+1)*β)) / V^β := by
            rw [← Real.rpow_natCast (2:ℝ) (i+j+1),
                show (((i+j+1:ℕ):ℝ)) = (i:ℝ)+(j:ℝ)+1 by simp only [Nat.cast_add, Nat.cast_one],
                ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
        _ = ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β * (2:ℝ)^(γ*(i:ℝ)) * (2:ℝ)^(γ*(j:ℝ))) / V^β := by
            rw [show (2:ℝ)^(α*(i:ℝ)) * (2:ℝ)^(α*(j:ℝ)) * (2:ℝ)^(((i:ℝ)+(j:ℝ)+1)*β)
                = (2:ℝ)^β * (2:ℝ)^(γ*(i:ℝ)) * (2:ℝ)^(γ*(j:ℝ)) by
              rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
                  ← Real.rpow_add (by norm_num : (0:ℝ) < 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
              congr 1
              rw [hγ]; ring]
        _ = ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β) * ((2:ℝ)^(γ*(i:ℝ)) * (2:ℝ)^(γ*(j:ℝ))) := by ring
    rw [halg]
  have hsum : (∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (L+1),
        ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β) * ((2:ℝ)^(γ*(i:ℝ)) * (2:ℝ)^(γ*(j:ℝ))))
      = ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β)
        * ((∑ i ∈ Finset.range (L+1), (2:ℝ)^(γ*(i:ℝ))) * (∑ j ∈ Finset.range (L+1), (2:ℝ)^(γ*(j:ℝ)))) := by
    calc (∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (L+1),
          ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β) * ((2:ℝ)^(γ*(i:ℝ)) * (2:ℝ)^(γ*(j:ℝ))))
        = ∑ i ∈ Finset.range (L+1), (((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β) * (2:ℝ)^(γ*(i:ℝ)))
            * (∑ j ∈ Finset.range (L+1), (2:ℝ)^(γ*(j:ℝ))) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl; intro j hj; ring
      _ = (∑ i ∈ Finset.range (L+1), ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β) * (2:ℝ)^(γ*(i:ℝ)))
            * (∑ j ∈ Finset.range (L+1), (2:ℝ)^(γ*(j:ℝ))) := by
          rw [← Finset.sum_mul]
      _ = ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β)
            * ((∑ i ∈ Finset.range (L+1), (2:ℝ)^(γ*(i:ℝ))) * (∑ j ∈ Finset.range (L+1), (2:ℝ)^(γ*(j:ℝ)))) := by
          rw [← Finset.mul_sum]; ring
  calc ∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (L+1),
        ∑ k ∈ (Finset.range (2*L+2)).filter (fun k => (2:ℝ)^k * V ≤ (2:ℝ)^(i+j+1)),
          (2:ℝ)^(α*(i:ℝ)) * (2:ℝ)^(α*(j:ℝ)) * (2:ℝ)^(β*(k:ℝ))
      ≤ ∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (L+1),
          ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β) * ((2:ℝ)^(γ*(i:ℝ)) * (2:ℝ)^(γ*(j:ℝ))) := by
        apply Finset.sum_le_sum; intro i hi
        apply Finset.sum_le_sum; intro j hj
        exact hpair i j
    _ = ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β)
          * ((∑ i ∈ Finset.range (L+1), (2:ℝ)^(γ*(i:ℝ))) * (∑ j ∈ Finset.range (L+1), (2:ℝ)^(γ*(j:ℝ)))) := hsum
    _ ≤ ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β)
          * ((2:ℝ)^(γ*((L:ℝ)+1)) * (2:ℝ)^(γ*((L:ℝ)+1))) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul geomL geomL (by positivity) (by positivity)
        · exact hXnn
    _ = ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β) * ((2:ℝ)^(γ*((L:ℝ)+1)))^2 := by ring

theorem box_reduce_dyadic {α β : ℝ} {V : ℝ} (hV : 1 ≤ V) (L : ℕ) (T : Finset (ℕ × ℕ × ℕ))
    (h1 : ∀ c ∈ T, c.1 ≤ L) (h2 : ∀ c ∈ T, c.2.1 ≤ L)
    (h3 : ∀ c ∈ T, (2:ℝ)^(c.2.2) * V ≤ (2:ℝ)^(c.1 + c.2.1 + 1)) :
    ∑ c ∈ T, (2:ℝ)^(α*(c.1:ℝ)) * (2:ℝ)^(α*(c.2.1:ℝ)) * (2:ℝ)^(β*(c.2.2:ℝ))
    ≤ ∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (L+1),
        ∑ k ∈ (Finset.range (2*L+2)).filter (fun k => (2:ℝ)^k * V ≤ (2:ℝ)^(i+j+1)),
          (2:ℝ)^(α*(i:ℝ)) * (2:ℝ)^(α*(j:ℝ)) * (2:ℝ)^(β*(k:ℝ)) := by
  have hsub : T ⊆ ((Finset.range (L+1)).product ((Finset.range (L+1)).product (Finset.range (2*L+2)))).filter
      (fun c => (2:ℝ)^(c.2.2) * V ≤ (2:ℝ)^(c.1 + c.2.1 + 1)) := by
    intro c hc
    have hmem1 : c.1 ∈ Finset.range (L+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (h1 c hc))
    have hmem2 : c.2.1 ∈ Finset.range (L+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (h2 c hc))
    have hmem3 : c.2.2 ∈ Finset.range (2*L+2) := by
      have hc1 : c.1 ≤ L := h1 c hc
      have hc2 : c.2.1 ≤ L := h2 c hc
      rw [Finset.mem_range]
      have hk2 : (2:ℝ)^(c.2.2) ≤ (2:ℝ)^(c.1 + c.2.1 + 1) := by
        calc (2:ℝ)^(c.2.2) = (2:ℝ)^(c.2.2) * 1 := by ring
          _ ≤ (2:ℝ)^(c.2.2) * V := mul_le_mul_of_nonneg_left hV (by positivity)
          _ ≤ (2:ℝ)^(c.1 + c.2.1 + 1) := h3 c hc
      have hup : (2:ℝ)^(c.1 + c.2.1 + 1) ≤ (2:ℝ)^(2*L+1) := by
        apply pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2)
        omega
      have hk3 : c.2.2 ≤ 2*L+1 := by
        by_contra hcon
        simp only [not_le] at hcon
        have := pow_lt_pow_right₀ (by norm_num : (1:ℝ) < 2) (show 2*L+1 < c.2.2 by omega)
        linarith
      omega
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hmem1, Finset.mem_product.mpr ⟨hmem2, hmem3⟩⟩, h3 c hc⟩
  have hconv : ∑ c ∈ ((Finset.range (L+1)).product ((Finset.range (L+1)).product (Finset.range (2*L+2)))).filter
        (fun c => (2:ℝ)^(c.2.2) * V ≤ (2:ℝ)^(c.1 + c.2.1 + 1)),
        (2:ℝ)^(α*(c.1:ℝ)) * (2:ℝ)^(α*(c.2.1:ℝ)) * (2:ℝ)^(β*(c.2.2:ℝ))
      = ∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (L+1),
          ∑ k ∈ (Finset.range (2*L+2)).filter (fun k => (2:ℝ)^k * V ≤ (2:ℝ)^(i+j+1)),
            (2:ℝ)^(α*(i:ℝ)) * (2:ℝ)^(α*(j:ℝ)) * (2:ℝ)^(β*(k:ℝ)) := by
    rw [Finset.sum_filter]
    calc ∑ c ∈ (Finset.range (L+1)).product ((Finset.range (L+1)).product (Finset.range (2*L+2))),
            (if (2:ℝ)^(c.2.2) * V ≤ (2:ℝ)^(c.1 + c.2.1 + 1)
              then (2:ℝ)^(α*(c.1:ℝ)) * (2:ℝ)^(α*(c.2.1:ℝ)) * (2:ℝ)^(β*(c.2.2:ℝ)) else 0)
        = ∑ i ∈ Finset.range (L+1), ∑ y ∈ (Finset.range (L+1)).product (Finset.range (2*L+2)),
            (if (2:ℝ)^(y.2) * V ≤ (2:ℝ)^(i + y.1 + 1)
              then (2:ℝ)^(α*(i:ℝ)) * (2:ℝ)^(α*(y.1:ℝ)) * (2:ℝ)^(β*(y.2:ℝ)) else 0) :=
          Finset.sum_product _ _ _
      _ = ∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (L+1), ∑ k ∈ Finset.range (2*L+2),
            (if (2:ℝ)^k * V ≤ (2:ℝ)^(i + j + 1)
              then (2:ℝ)^(α*(i:ℝ)) * (2:ℝ)^(α*(j:ℝ)) * (2:ℝ)^(β*(k:ℝ)) else 0) := by
          apply Finset.sum_congr rfl; intro i hi
          exact Finset.sum_product _ _ _
      _ = ∑ i ∈ Finset.range (L+1), ∑ j ∈ Finset.range (L+1),
          ∑ k ∈ (Finset.range (2*L+2)).filter (fun k => (2:ℝ)^k * V ≤ (2:ℝ)^(i+j+1)),
            (2:ℝ)^(α*(i:ℝ)) * (2:ℝ)^(α*(j:ℝ)) * (2:ℝ)^(β*(k:ℝ)) := by
          apply Finset.sum_congr rfl; intro i hi
          apply Finset.sum_congr rfl; intro j hj
          rw [← Finset.sum_filter]
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun c hc _ => by positivity)) ?_
  rw [hconv]

/-- The reciprocal weight of a dyadic cell. -/
noncomputable def Dterm (s t : ℝ) (c : ℕ × ℕ × ℕ) : ℝ :=
  (2:ℝ)^(-(t*(c.2.2:ℝ) + s*(c.1:ℝ) + s*(c.2.1:ℝ)))

/-- The dyadic weight of a cell. -/
noncomputable def Dweight (α β : ℝ) (c : ℕ × ℕ × ℕ) : ℝ :=
  (2:ℝ)^(α*(c.1:ℝ)) * (2:ℝ)^(α*(c.2.1:ℝ)) * (2:ℝ)^(β*(c.2.2:ℝ))

/-- The product of the cardinality bound and the reciprocal weight of a cell collapses to the
dyadic weight, provided `α = 2 - s` and `β = n - 1 - t`. -/
lemma cardterm_eq {n : ℕ} {s t α β : ℝ} (hn : 1 ≤ n) (hα : α = 2 - s) (hβ : β = (n:ℝ) - 1 - t)
    (c : ℕ × ℕ × ℕ) :
    ((2:ℝ)^(c.1))^2 * ((2:ℝ)^(c.2.1))^2 * ((2:ℝ)^(c.2.2))^(n-1) * Dterm s t c
      = Dweight α β c := by
  rw [Dterm, Dweight, hα, hβ]
  rw [← pow_mul, ← pow_mul, ← pow_mul]
  rw [← Real.rpow_natCast (2:ℝ) (c.1*2), ← Real.rpow_natCast (2:ℝ) (c.2.1*2),
      ← Real.rpow_natCast (2:ℝ) (c.2.2*(n-1))]
  rw [show ((c.1*2:ℕ):ℝ) = 2*(c.1:ℝ) by push_cast; ring,
      show ((c.2.1*2:ℕ):ℝ) = 2*(c.2.1:ℝ) by push_cast; ring,
      show ((c.2.2*(n-1):ℕ):ℝ) = (c.2.2:ℝ)*((n:ℝ)-1) by
        rw [Nat.cast_mul, Nat.cast_sub hn, Nat.cast_one]]
  rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2), ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
  congr 1
  ring

theorem dyadic_summation {γ : Type*} (n : ℕ) (hn : 3 ≤ n) (s t : ℝ) (hs : 0 ≤ s) (ht : 0 < t)
    (htn : t < (n : ℝ) - 1) (hst : s + t ≤ (n : ℝ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset γ) (x y D : γ → ℝ) (K V X : ℝ), 0 < K → 1 ≤ V → 1 ≤ X →
      (∀ p ∈ S, 1 ≤ x p ∧ 1 ≤ y p ∧ 1 ≤ D p ∧ D p * V ≤ x p * y p ∧ x p ≤ X ∧ y p ≤ X) →
      (∀ A B Δ : ℝ, 1 ≤ A → 1 ≤ B → 0 < Δ →
        ((S.filter (fun p => x p ≤ A ∧ y p ≤ B ∧ D p ≤ Δ)).card : ℝ)
          ≤ K * A ^ 2 * B ^ 2 * Δ ^ (n - 1)) →
      (∑ p ∈ S, 1 / (D p ^ t * x p ^ s * y p ^ s))
        ≤ C * K * X ^ (2 * ((n : ℝ) + 1 - s - t)) / V ^ ((n : ℝ) - 1 - t) := by
  set α : ℝ := 2 - s with hαdef
  set β : ℝ := (n : ℝ) - 1 - t with hβdef
  set g : ℝ := (n : ℝ) + 1 - s - t with hgdef
  have hβpos : 0 < β := by rw [hβdef]; linarith
  have hg1 : 1 ≤ g := by rw [hgdef]; linarith
  have hgsum : g = α + β := by rw [hαdef, hβdef, hgdef]; ring
  have hβden : 0 < (2:ℝ)^β - 1 := by
    have h := Real.one_lt_rpow (by norm_num : (1:ℝ) < 2) hβpos; linarith
  have hcpos : 0 < (2:ℝ)^β / ((2:ℝ)^β - 1) :=
    div_pos (Real.rpow_pos_of_pos (by norm_num) β) hβden
  refine ⟨(2:ℝ)^(t+2*s) * ((2:ℝ)^β / ((2:ℝ)^β - 1)) * (2:ℝ)^β * (2:ℝ)^(4*g), ?_, ?_⟩
  · exact mul_pos (mul_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) (t+2*s)) hcpos)
      (Real.rpow_pos_of_pos (by norm_num) β)) (Real.rpow_pos_of_pos (by norm_num) (4*g))
  · intro S x y D K V X hK hV hX hbd hcnt
    let L : ℕ := dyIdx X
    let idx : γ → ℕ × ℕ × ℕ := fun p => (dyIdx (x p), dyIdx (y p), dyIdx (D p))
    have hABpos : 0 < ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β) :=
      mul_pos hcpos (div_pos (Real.rpow_pos_of_pos (by norm_num) β)
        (Real.rpow_pos_of_pos (by linarith) β))
    -- (i) pointwise bound
    have hpt : ∀ p ∈ S, 1 / (D p ^ t * x p ^ s * y p ^ s) ≤ (2:ℝ)^(t + 2*s) * Dterm s t (idx p) := by
      intro p hp
      obtain ⟨h1x, h1y, h1D, hDV, hxX, hyX⟩ := hbd p hp
      have eD : (2:ℝ)^((idx p).2.2) ≤ 2 * D p := pow_dyIdx_le h1D
      have ex : (2:ℝ)^((idx p).1) ≤ 2 * x p := pow_dyIdx_le h1x
      have ey : (2:ℝ)^((idx p).2.1) ≤ 2 * y p := pow_dyIdx_le h1y
      exact term_le_rpow ht hs eD ex ey
    -- (ii) sum over S
    have hsum1 : ∑ p ∈ S, 1/(D p^t * x p^s * y p^s) ≤
        (2:ℝ)^(t+2*s) * ∑ p ∈ S, Dterm s t (idx p) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpt
    -- (iii) reindex by cell
    have hfib : ∑ p ∈ S, Dterm s t (idx p) =
        ∑ c ∈ S.image idx, ((S.filter (fun p => idx p = c)).card : ℝ) * Dterm s t c :=
      sum_comp_image_eq S idx (Dterm s t)
    -- (iv) cardinality bound per cell
    have hcard : ∀ c ∈ S.image idx, ((S.filter (fun p => idx p = c)).card : ℝ)
        ≤ K * ((2:ℝ)^(c.1))^2 * ((2:ℝ)^(c.2.1))^2 * ((2:ℝ)^(c.2.2))^(n-1) := by
      intro c hc
      have hsub : S.filter (fun p => idx p = c) ⊆
          S.filter (fun q => x q ≤ (2:ℝ)^(c.1) ∧ y q ≤ (2:ℝ)^(c.2.1) ∧ D q ≤ (2:ℝ)^(c.2.2)) := by
        intro q hq
        rw [Finset.mem_filter] at hq ⊢
        obtain ⟨hqS, hqe⟩ := hq
        refine ⟨hqS, ?_, ?_, ?_⟩
        · have h : x q ≤ (2:ℝ)^((idx q).1) := le_pow_dyIdx (x q); rwa [hqe] at h
        · have h : y q ≤ (2:ℝ)^((idx q).2.1) := le_pow_dyIdx (y q); rwa [hqe] at h
        · have h : D q ≤ (2:ℝ)^((idx q).2.2) := le_pow_dyIdx (D q); rwa [hqe] at h
      have hc2 := hcnt ((2:ℝ)^(c.1)) ((2:ℝ)^(c.2.1)) ((2:ℝ)^(c.2.2))
        (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) (by positivity)
      calc ((S.filter (fun p => idx p = c)).card : ℝ)
          ≤ ((S.filter (fun q => x q ≤ (2:ℝ)^(c.1) ∧ y q ≤ (2:ℝ)^(c.2.1) ∧ D q ≤ (2:ℝ)^(c.2.2))).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ K * ((2:ℝ)^(c.1))^2 * ((2:ℝ)^(c.2.1))^2 * ((2:ℝ)^(c.2.2))^(n-1) := hc2
    -- (v) per-cell product collapses
    have hper : ∀ c ∈ S.image idx,
        ((S.filter (fun p => idx p = c)).card : ℝ) * Dterm s t c ≤ K * Dweight α β c := by
      intro c hc
      have h1 := hcard c hc
      have h2 : (0:ℝ) ≤ Dterm s t c := by rw [Dterm]; positivity
      calc ((S.filter (fun p => idx p = c)).card : ℝ) * Dterm s t c
          ≤ (K * ((2:ℝ)^(c.1))^2 * ((2:ℝ)^(c.2.1))^2 * ((2:ℝ)^(c.2.2))^(n-1)) * Dterm s t c :=
            mul_le_mul_of_nonneg_right h1 h2
        _ = K * Dweight α β c := by
            rw [← cardterm_eq (n := n) (s := s) (t := t) (by omega) hαdef hβdef c]; ring
    -- (vi) box reduction and dyadic box sum
    have hL1 : ∀ c ∈ S.image idx, c.1 ≤ L := by
      intro c hc
      obtain ⟨p, hp, hpc⟩ := Finset.mem_image.mp hc
      obtain ⟨h1x, h1y, h1D, hDV, hxX, hyX⟩ := hbd p hp
      rw [← hpc]
      exact dyIdx_mono hxX
    have hL2 : ∀ c ∈ S.image idx, c.2.1 ≤ L := by
      intro c hc
      obtain ⟨p, hp, hpc⟩ := Finset.mem_image.mp hc
      obtain ⟨h1x, h1y, h1D, hDV, hxX, hyX⟩ := hbd p hp
      rw [← hpc]
      exact dyIdx_mono hyX
    have hL3 : ∀ c ∈ S.image idx, (2:ℝ)^(c.2.2) * V ≤ (2:ℝ)^(c.1 + c.2.1 + 1) := by
      intro c hc
      obtain ⟨p, hp, hpc⟩ := Finset.mem_image.mp hc
      obtain ⟨h1x, h1y, h1D, hDV, hxX, hyX⟩ := hbd p hp
      rw [← hpc]
      have hV0 : 0 < V := by linarith
      have eD : (2:ℝ)^((idx p).2.2) ≤ 2 * D p := pow_dyIdx_le h1D
      have ex : x p ≤ (2:ℝ)^((idx p).1) := le_pow_dyIdx (x p)
      have ey : y p ≤ (2:ℝ)^((idx p).2.1) := le_pow_dyIdx (y p)
      calc (2:ℝ)^((idx p).2.2) * V ≤ (2 * D p) * V := mul_le_mul_of_nonneg_right eD hV0.le
        _ = 2 * (D p * V) := by ring
        _ ≤ 2 * (x p * y p) := mul_le_mul_of_nonneg_left hDV (by norm_num)
        _ ≤ 2 * ((2:ℝ)^((idx p).1) * (2:ℝ)^((idx p).2.1)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul ex ey (le_trans zero_le_one h1y) (by positivity)) (by norm_num)
        _ = (2:ℝ)^((idx p).1 + (idx p).2.1 + 1) := by rw [pow_add, pow_add]; ring
    have hbox := box_reduce_dyadic (α := α) (β := β) hV L (S.image idx) hL1 hL2 hL3
    have hboxsum := box_dyadic_sum (α := α) (β := β) (γ := g) hgsum hβpos hg1 hV L
    have hTW : ∑ c ∈ S.image idx, Dweight α β c ≤
        ((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β) * ((2:ℝ)^(g*((L:ℝ)+1)))^2 :=
      le_trans hbox hboxsum
    -- (vii) relate L to X
    have hXrel : ((2:ℝ)^(g*((L:ℝ)+1)))^2 ≤ (2:ℝ)^(4*g) * X^(2*g) := by
      have hX0 : (0:ℝ) < X := by linarith
      have hXL : (2:ℝ)^L ≤ 2 * X := pow_dyIdx_le hX
      have hpowL : ((2:ℝ)^L)^g = (2:ℝ)^(g*(L:ℝ)) := by
        rw [← Real.rpow_natCast (2:ℝ) L, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (L:ℝ) g]
        congr 1; ring
      have step1 : (2:ℝ)^(g*((L:ℝ)+1)) = ((2:ℝ)^L)^g * (2:ℝ)^g := by
        rw [show g*((L:ℝ)+1) = g*(L:ℝ) + g by ring, Real.rpow_add (by norm_num : (0:ℝ) < 2),
            ← hpowL]
      have step2 : (2:ℝ)^(g*((L:ℝ)+1)) ≤ (2:ℝ)^(2*g) * X^g := by
        rw [step1]
        have h1 : ((2:ℝ)^L)^g ≤ (2*X)^g := Real.rpow_le_rpow (by positivity) hXL (le_of_lt (by linarith : 0 < g))
        have h2 : (2*X)^g = (2:ℝ)^g * X^g := Real.mul_rpow (by norm_num) (le_of_lt hX0)
        rw [h2] at h1
        have hg2 : (2:ℝ)^g * (2:ℝ)^g = (2:ℝ)^(2*g) := by
          rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; congr 1; ring
        calc ((2:ℝ)^L)^g * (2:ℝ)^g ≤ ((2:ℝ)^g * X^g) * (2:ℝ)^g :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = (2:ℝ)^(2*g) * X^g := by rw [← hg2]; ring
      calc ((2:ℝ)^(g*((L:ℝ)+1)))^2 ≤ ((2:ℝ)^(2*g) * X^g)^2 :=
            pow_le_pow_left₀ (by positivity) step2 2
        _ = (2:ℝ)^(4*g) * X^(2*g) := by
            rw [mul_pow]
            have e1 : ((2:ℝ)^(2*g))^2 = (2:ℝ)^(4*g) := by
              rw [← Real.rpow_natCast ((2:ℝ)^(2*g)) 2,
                  ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) (2*g) ((2:ℕ):ℝ)]
              congr 1; push_cast; ring
            have e2 : (X^g)^2 = X^(2*g) := by
              rw [← Real.rpow_natCast (X^g) 2,
                  ← Real.rpow_mul (le_of_lt hX0) g ((2:ℕ):ℝ)]
              congr 1; push_cast; ring
            rw [e1, e2]
    -- (viii) assemble
    calc ∑ p ∈ S, 1/(D p^t * x p^s * y p^s)
        ≤ (2:ℝ)^(t+2*s) * ∑ p ∈ S, Dterm s t (idx p) := hsum1
      _ = (2:ℝ)^(t+2*s) * ∑ c ∈ S.image idx, ((S.filter (fun p => idx p = c)).card : ℝ) * Dterm s t c := by
            rw [hfib]
      _ ≤ (2:ℝ)^(t+2*s) * ∑ c ∈ S.image idx, K * Dweight α β c := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Finset.sum_le_sum hper
      _ = (2:ℝ)^(t+2*s) * K * ∑ c ∈ S.image idx, Dweight α β c := by
            conv_lhs => rw [Finset.mul_sum]
            conv_rhs => rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro c hc; ring
      _ ≤ (2:ℝ)^(t+2*s) * K *
            (((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β) * ((2:ℝ)^(g*((L:ℝ)+1)))^2) :=
            mul_le_mul_of_nonneg_left hTW (by positivity)
      _ ≤ (2:ℝ)^(t+2*s) * K *
            (((2:ℝ)^β / ((2:ℝ)^β - 1)) * ((2:ℝ)^β / V^β) * ((2:ℝ)^(4*g) * X^(2*g))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hXrel hABpos.le) (by positivity)
      _ = (2:ℝ)^(t+2*s) * ((2:ℝ)^β / ((2:ℝ)^β - 1)) * (2:ℝ)^β * (2:ℝ)^(4*g)
            * K * X^(2*((n:ℝ)+1-s-t)) / V^((n:ℝ)-1-t) := by
            ring

end Work.HP
