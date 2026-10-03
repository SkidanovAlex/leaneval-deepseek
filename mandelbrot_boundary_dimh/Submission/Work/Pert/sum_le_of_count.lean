import Mathlib
import Submission.Work.Pert.LCH.layer_cake_pointwise
import Submission.Work.Pert.LCH.harmonic_le_log

namespace Work.Pert

open Finset

/-! A layer-cake bound for a finite family whose "small levels" are counted.
`K` elements `d i ≥ 0`, a counting bound `#{i < K : d i ≤ t} ≤ A (B t + 1)` for all `t > 0`,
and `H > 0` with `A (B H + 1) ≤ K` (i.e. `H` is at most the saturation level
`t* = (K - A)/(A B)` of the counting bound) give
`∑_{i<K} 1/max(H, d i) ≤ A (B (2 + log(2+K)) + 1/H) + A B`.

Proof route.  `LCH.layer_cake_pointwise` (public, `Submission/Work/Pert/LCH/layer_cake_pointwise.lean`)
gives, for every `N : ℕ` and `0 ≤ d`, `0 < H`,
`1/max(H,d) ≤ ∑_{l<N} (1/((l+1)H) - 1/((l+2)H))·[d ≤ (l+2)H] + 1/((N+1)H)`.
Sum over `i < K` and insert `hcount` at the levels `t = (l+2)H > 0`:
`∑_i 1/max(H,d i) ≤ ∑_{l<N} A·(B(l+2)H + 1)/((l+1)(l+2)H) + K/((N+1)H)`
(using `(1/((l+1)H) - 1/((l+2)H)) = 1/((l+1)(l+2)H)`).  Now
`(B(l+2)H + 1)/((l+1)(l+2)H) = B/(l+1) + 1/((l+1)(l+2)H)`, so the sum equals
`A·[B·∑_{l<N}1/(l+1) + (1/H)(1 - 1/(N+1))]`, and combining the two `1/(N+1)` terms
(`-A/((N+1)H) + K/((N+1)H) = (K-A)/((N+1)H)`) the bound becomes
`A·[B·∑_{l<N}1/(l+1) + 1/H] + (K-A)/((N+1)H)`.
Take `N = ⌊t*/H⌋` (well defined and `≥ 1` by `hsat`, so `(N+1)H > t*` and
`(K-A)/((N+1)H) < (K-A)/t* = A·B`), and use `LCH.harmonic_le_log` for
`∑_{l<N}1/(l+1) ≤ 1 + log N ≤ 1 + log(2+K)`; the last step needs `N ≤ 2 + K`, which follows from
`N ≤ t*/H = (K-A)/(A B H) ≤ (K-A)/3 ≤ K` (`hA`, `hBH`). -/

/-- Telescoping: `∑_{l<N} 1/((l+1)(l+2)) = 1 - 1/(N+1)`. -/
private lemma telescope_inv_prod (N : ℕ) :
    (∑ l ∈ Finset.range N, (1:ℝ) / (((l:ℝ)+1) * ((l:ℝ)+2))) = 1 - 1/((N:ℝ)+1) := by
  have hterm : ∀ l : ℕ, (1:ℝ) / (((l:ℝ)+1) * ((l:ℝ)+2))
      = 1/((l:ℝ)+1) - 1/((l:ℝ)+2) := by
    intro l
    have h1 : ((l:ℝ)+1) ≠ 0 := by positivity
    have h2 : ((l:ℝ)+2) ≠ 0 := by positivity
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.range N) => hterm l)]
  have h := Finset.sum_range_sub' (fun l : ℕ => (1:ℝ)/((l:ℝ)+1)) N
  have hcast : ∀ i : ℕ, ((1:ℝ)/(((i+1:ℕ):ℝ)+1)) = 1/((i:ℝ)+2) := by
    intro i; push_cast; ring_nf
  rw [show (∑ l ∈ Finset.range N, ((1:ℝ)/((l:ℝ)+1) - 1/((l:ℝ)+2)))
        = ∑ l ∈ Finset.range N, ((1:ℝ)/((l:ℝ)+1) - (1:ℝ)/(((l+1:ℕ):ℝ)+1)) from
      Finset.sum_congr rfl (fun l _ => by rw [hcast l])] at *
  rw [h]
  norm_num

/-- The weighted layer-cake sum rewrites into the harmonic sum plus the telescoping tail. -/
private lemma layer_sum_id (A B H : ℝ) (hH : H ≠ 0) (N : ℕ) :
    (∑ l ∈ Finset.range N,
        ((1:ℝ) / (((l:ℝ)+1)*H) - 1/(((l:ℝ)+2)*H)) * (A * (B * (((l:ℝ)+2)*H) + 1)))
      = A*B * (∑ l ∈ Finset.range N, 1/((l:ℝ)+1))
        + (A/H) * (1 - 1/((N:ℝ)+1)) := by
  have hterm : ∀ l : ℕ,
      ((1:ℝ)/(((l:ℝ)+1)*H) - 1/(((l:ℝ)+2)*H)) * (A*(B*(((l:ℝ)+2)*H)+1))
        = A*B*(1/((l:ℝ)+1)) + (A/H)*(1/(((l:ℝ)+1)*((l:ℝ)+2))) := by
    intro l
    have h1 : ((l:ℝ)+1) ≠ 0 := by positivity
    have h2 : ((l:ℝ)+2) ≠ 0 := by positivity
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.range N) => hterm l)]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.mul_sum]
  · rw [← Finset.mul_sum, telescope_inv_prod]

/-- **Summed layer-cake bound.**  Summing the pointwise layer-cake estimate over the `K`
elements and using the counting hypothesis at every level `(l+2)H > 0` bounds the reciprocal
sum by the weighted level sum plus the tail `K/((N+1)H)`. -/
private lemma sum_pointwise_le {K N : ℕ} {d : ℕ → ℝ} {A B H : ℝ}
    (hH : 0 < H)
    (hd : ∀ i < K, 0 ≤ d i)
    (hcount : ∀ t : ℝ, 0 < t →
      (((Finset.range K).filter (fun i => d i ≤ t)).card : ℝ) ≤ A * (B * t + 1)) :
    (∑ i ∈ Finset.range K, 1 / max H (d i))
      ≤ (∑ l ∈ Finset.range N,
          (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) * (A * (B * (((l:ℝ)+2) * H) + 1)))
        + (K : ℝ) / (((N:ℝ)+1) * H) := by
  have hpt : ∀ i ∈ Finset.range K,
      1 / max H (d i) ≤
        (∑ l ∈ Finset.range N,
          (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) *
            (if d i ≤ ((l:ℝ)+2) * H then (1:ℝ) else 0))
        + 1 / (((N:ℝ)+1) * H) := by
    intro i hi
    have hiK : i < K := Finset.mem_range.mp hi
    have hdi : 0 ≤ d i := hd i hiK
    have h := Work.Pert.LCH.layer_cake_pointwise hdi hH N
    rwa [max_comm] at h
  calc (∑ i ∈ Finset.range K, 1 / max H (d i))
      ≤ ∑ i ∈ Finset.range K,
          ((∑ l ∈ Finset.range N,
            (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) *
              (if d i ≤ ((l:ℝ)+2) * H then (1:ℝ) else 0))
          + 1 / (((N:ℝ)+1) * H)) := Finset.sum_le_sum hpt
    _ = (∑ i ∈ Finset.range K, ∑ l ∈ Finset.range N,
            (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) *
              (if d i ≤ ((l:ℝ)+2) * H then (1:ℝ) else 0))
          + ∑ i ∈ Finset.range K, 1 / (((N:ℝ)+1) * H) := by
        rw [Finset.sum_add_distrib]
    _ = (∑ l ∈ Finset.range N, ∑ i ∈ Finset.range K,
            (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) *
              (if d i ≤ ((l:ℝ)+2) * H then (1:ℝ) else 0))
          + ∑ i ∈ Finset.range K, 1 / (((N:ℝ)+1) * H) := by
        rw [Finset.sum_comm]
    _ = (∑ l ∈ Finset.range N,
            (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) *
              (((Finset.range K).filter (fun i => d i ≤ ((l:ℝ)+2) * H)).card : ℝ))
          + ∑ i ∈ Finset.range K, 1 / (((N:ℝ)+1) * H) := by
        congr 1
        apply Finset.sum_congr rfl
        intro l _
        rw [← Finset.mul_sum, Finset.sum_boole]
    _ = (∑ l ∈ Finset.range N,
            (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) *
              (((Finset.range K).filter (fun i => d i ≤ ((l:ℝ)+2) * H)).card : ℝ))
          + (K : ℝ) / (((N:ℝ)+1) * H) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one_div]
    _ ≤ (∑ l ∈ Finset.range N,
          (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) * (A * (B * (((l:ℝ)+2) * H) + 1)))
        + (K : ℝ) / (((N:ℝ)+1) * H) := by
        apply add_le_add
        · apply Finset.sum_le_sum
          intro l _
          have hw : 0 ≤ 1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H) := by
            have h1 : 0 < ((l:ℝ)+1) * H := by positivity
            have hle : ((l:ℝ)+1) * H ≤ ((l:ℝ)+2) * H := by nlinarith [hH]
            have := one_div_le_one_div_of_le h1 hle
            linarith
          have ht : 0 < ((l:ℝ)+2) * H := by positivity
          have hc := hcount (((l:ℝ)+2) * H) ht
          exact mul_le_mul_of_nonneg_left hc hw
        · exact le_rfl

theorem sum_le_of_count {K : ℕ} {d : ℕ → ℝ} {A B H : ℝ}
    (hA : 1 ≤ A) (hB : 0 < B) (hH : 0 < H) (hBH : 3 ≤ B * H)
    (hd : ∀ i < K, 0 ≤ d i)
    (hcount : ∀ t : ℝ, 0 < t →
      (((Finset.range K).filter (fun i => d i ≤ t)).card : ℝ) ≤ A * (B * t + 1))
    (hsat : A * (B * H + 1) ≤ (K : ℝ)) :
    (∑ i ∈ Finset.range K, 1 / max H (d i))
      ≤ A * (B * (2 + Real.log (2 + (K : ℝ))) + 1 / H) + A * B := by
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA
  have hAB : 0 < A * B := mul_pos hApos hB
  have hABne : A * B ≠ 0 := ne_of_gt hAB
  -- `A ≤ K`, so that `t*` below is nonnegative.
  have hKA : A ≤ (K : ℝ) := by
    have h1 : (1:ℝ) ≤ B * H + 1 := by linarith
    have h2 : A * 1 ≤ A * (B * H + 1) := mul_le_mul_of_nonneg_left h1 (le_of_lt hApos)
    linarith
  set tstar : ℝ := ((K:ℝ) - A) / (A * B) with htstar
  have htstar_nn : 0 ≤ tstar := by
    rw [htstar]; exact div_nonneg (by linarith) (le_of_lt hAB)
  set x : ℝ := tstar / H with hx
  have hx_nn : 0 ≤ x := by rw [hx]; exact div_nonneg htstar_nn (le_of_lt hH)
  set N : ℕ := (⌊x⌋).toNat with hN
  have hNcast : (N : ℝ) = (⌊x⌋ : ℝ) := by
    rw [hN]
    exact_mod_cast Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx_nn)
  have hN_le_x : (N:ℝ) ≤ x := by rw [hNcast]; exact Int.floor_le x
  have hx_lt_N : x < (N:ℝ) + 1 := by rw [hNcast]; exact Int.lt_floor_add_one x
  -- `t* < (N+1) H`.
  have hxH : tstar < ((N:ℝ) + 1) * H := by
    have h := hx_lt_N
    rw [hx] at h
    have hh := mul_lt_mul_of_pos_right h hH
    rwa [div_mul_cancel₀ tstar (ne_of_gt hH)] at hh
  -- `N ≤ 2 + K`.
  have hx_le : x ≤ ((K:ℝ) - A)/3 := by
    rw [hx, htstar, div_div]
    have h3 : (3:ℝ) ≤ (A*B)*H := by
      have h := mul_le_mul hA hBH (by norm_num : (0:ℝ) ≤ 3) (le_of_lt hApos)
      nlinarith [h]
    exact div_le_div_of_nonneg_left (by linarith) (by norm_num) h3
  have hN_le_K : (N:ℝ) ≤ 2 + (K:ℝ) := by
    have hk : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
    calc (N:ℝ) ≤ x := hN_le_x
      _ ≤ ((K:ℝ) - A)/3 := hx_le
      _ ≤ 2 + (K:ℝ) := by nlinarith [hKA, hk]
  -- The summed layer-cake bound and its telescoped form.
  have hsum := sum_pointwise_le (K := K) (N := N) (d := d) (A := A) (B := B) (H := H)
      hH hd hcount
  have hid := layer_sum_id A B H (ne_of_gt hH) N
  rw [hid] at hsum
  have hstep2 :
      A*B * (∑ l ∈ Finset.range N, 1/((l:ℝ)+1)) + (A/H)*(1 - 1/((N:ℝ)+1)) + (K:ℝ)/(((N:ℝ)+1)*H)
        = A*B * (∑ l ∈ Finset.range N, 1/((l:ℝ)+1)) + A/H + ((K:ℝ) - A)/(((N:ℝ)+1)*H) := by
    field_simp
    ring
  have hharm : (∑ l ∈ Finset.range N, (1:ℝ)/((l:ℝ)+1)) ≤ 1 + Real.log (2 + (K:ℝ)) := by
    have h1 := Work.Pert.LCH.harmonic_le_log N
    have h2 : Real.log (N:ℝ) ≤ Real.log (2 + (K:ℝ)) := by
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · rw [hN0]
        simp only [Nat.cast_zero, Real.log_zero]
        apply Real.log_nonneg
        have hk : (0:ℝ) ≤ (K:ℝ) := Nat.cast_nonneg K
        linarith
      · exact Real.log_le_log (by exact_mod_cast hNpos) hN_le_K
    linarith
  have hslack : ((K:ℝ) - A)/(((N:ℝ)+1)*H) ≤ A*B := by
    have h1 : (A*B) * tstar < (A*B) * (((N:ℝ)+1)*H) := mul_lt_mul_of_pos_left hxH hAB
    have h2 : (A*B) * tstar = (K:ℝ) - A := by
      rw [htstar]; exact mul_div_cancel₀ _ hABne
    rw [h2] at h1
    rw [div_le_iff₀ (by positivity)]
    linarith
  calc (∑ i ∈ Finset.range K, 1 / max H (d i))
      ≤ A*B * (∑ l ∈ Finset.range N, 1/((l:ℝ)+1)) + A/H + ((K:ℝ) - A)/(((N:ℝ)+1)*H) := by
        rw [← hstep2]; exact hsum
    _ ≤ A*B * (1 + Real.log (2 + (K:ℝ))) + A/H + A*B := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_left hharm (le_of_lt hAB)
          · exact le_rfl
        · exact hslack
    _ ≤ A * (B * (2 + Real.log (2 + (K : ℝ))) + 1 / H) + A * B := by
        have hL : A*B * (1 + Real.log (2 + (K:ℝ)))
            ≤ A*B * (2 + Real.log (2 + (K:ℝ))) :=
          mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hAB)
        have heq : A * (B * (2 + Real.log (2 + (K : ℝ))) + 1 / H) + A * B
            = A*B * (2 + Real.log (2 + (K:ℝ))) + A/H + A*B := by ring
        rw [heq]
        linarith

end Work.Pert
