import Mathlib
import Submission.Work.Pert.LCH.layer_cake_pointwise
import Submission.Work.Pert.LCH.harmonic_le_log

namespace Work.Pert

open Finset

/-! ## A layer-cake bound for `∑ 1 / max H (d i)` over an arbitrary finite set

Given a finite `B : Finset ℕ`, a nonnegative family `d : ℕ → ℝ`, a counting hypothesis
`#{i ∈ B : d i ≤ t} ≤ A (C t + 1)` valid for every `t > 0`, and a level `H > 0` with
`A (C H + 1) ≤ |B|` (so that `H` does not exceed the saturation level
`t* = (|B| - A)/(A C)` of the counting bound), we bound

`∑_{i ∈ B} 1 / max H (d i) ≤ A C (1 + log (1 + |B|/(A C H))) + A/H + A C`.

The argument is the layer-cake argument (carried out in
`Work.PertMiddle.sum_inv_max_le_count_log` for `B = Finset.range K`), here for an arbitrary
`Finset`:

* the public pointwise layer-cake estimate `Work.Pert.LCH.layer_cake_pointwise` gives, for
  `0 ≤ d`, `H > 0` and every `N : ℕ`,
  `1/max H d ≤ ∑_{l<N} (1/((l+1)H) - 1/((l+2)H))·[d ≤ (l+2)H] + 1/((N+1)H)`;
* summing over `i ∈ B` and inserting the counting hypothesis at the levels `(l+2)H > 0`,
  `∑_{i∈B} 1/max H (d i) ≤ ∑_{l<N} A·(C(l+2)H + 1)/((l+1)(l+2)H) + |B|/((N+1)H)`;
* the algebraic identity `(C(l+2)H + 1)/((l+1)(l+2)H) = C/(l+1) + 1/((l+1)(l+2)H)` and the
  telescoping `∑_{l<N} 1/((l+1)(l+2)) = 1 - 1/(N+1)` turn this into
  `A C·(∑_{l<N} 1/(l+1)) + A/H + (|B| - A)/((N+1)H)`;
* with `N = ⌊t*/H⌋` the tail is `≤ A C`, while the harmonic sum is
  `≤ 1 + log N ≤ 1 + log(1 + |B|/(A C H))`, since `N ≤ |B|/(A C H)`. -/

/-- Telescoping: `∑_{l<N} 1/((l+1)(l+2)) = 1 - 1/(N+1)`. -/
private lemma sum_inv_max_telescope (N : ℕ) :
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
private lemma sum_inv_max_layer_id (A C H : ℝ) (hH : H ≠ 0) (N : ℕ) :
    (∑ l ∈ Finset.range N,
        ((1:ℝ) / (((l:ℝ)+1)*H) - 1/(((l:ℝ)+2)*H)) * (A * (C * (((l:ℝ)+2)*H) + 1)))
      = A*C * (∑ l ∈ Finset.range N, 1/((l:ℝ)+1))
        + (A/H) * (1 - 1/((N:ℝ)+1)) := by
  have hterm : ∀ l : ℕ,
      ((1:ℝ)/(((l:ℝ)+1)*H) - 1/(((l:ℝ)+2)*H)) * (A*(C*(((l:ℝ)+2)*H)+1))
        = A*C*(1/((l:ℝ)+1)) + (A/H)*(1/(((l:ℝ)+1)*((l:ℝ)+2))) := by
    intro l
    have h1 : ((l:ℝ)+1) ≠ 0 := by positivity
    have h2 : ((l:ℝ)+2) ≠ 0 := by positivity
    field_simp
    ring
  rw [Finset.sum_congr rfl (fun l (_ : l ∈ Finset.range N) => hterm l)]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.mul_sum]
  · rw [← Finset.mul_sum, sum_inv_max_telescope]

/-- **Summed layer-cake bound.**  Summing the pointwise layer-cake estimate over the elements
of `B` and using the counting hypothesis at every level `(l+2)H > 0` bounds the reciprocal
sum by the weighted level sum plus the tail `|B|/((N+1)H)`. -/
private lemma sum_inv_max_pointwise {B : Finset ℕ} {N : ℕ} {d : ℕ → ℝ} {A C H : ℝ}
    (hH : 0 < H)
    (hd : ∀ i ∈ B, 0 ≤ d i)
    (hcount : ∀ t : ℝ, 0 < t →
      ((B.filter (fun i => d i ≤ t)).card : ℝ) ≤ A * (C * t + 1)) :
    (∑ i ∈ B, 1 / max H (d i))
      ≤ (∑ l ∈ Finset.range N,
          (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) * (A * (C * (((l:ℝ)+2) * H) + 1)))
        + (B.card : ℝ) / (((N:ℝ)+1) * H) := by
  have hpt : ∀ i ∈ B,
      1 / max H (d i) ≤
        (∑ l ∈ Finset.range N,
          (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) *
            (if d i ≤ ((l:ℝ)+2) * H then (1:ℝ) else 0))
        + 1 / (((N:ℝ)+1) * H) := by
    intro i hi
    have hdi : 0 ≤ d i := hd i hi
    have h := Work.Pert.LCH.layer_cake_pointwise hdi hH N
    rwa [max_comm] at h
  calc (∑ i ∈ B, 1 / max H (d i))
      ≤ ∑ i ∈ B,
          ((∑ l ∈ Finset.range N,
            (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) *
              (if d i ≤ ((l:ℝ)+2) * H then (1:ℝ) else 0))
          + 1 / (((N:ℝ)+1) * H)) := Finset.sum_le_sum hpt
    _ = (∑ i ∈ B, ∑ l ∈ Finset.range N,
            (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) *
              (if d i ≤ ((l:ℝ)+2) * H then (1:ℝ) else 0))
          + ∑ i ∈ B, 1 / (((N:ℝ)+1) * H) := by
        rw [Finset.sum_add_distrib]
    _ = (∑ l ∈ Finset.range N, ∑ i ∈ B,
            (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) *
              (if d i ≤ ((l:ℝ)+2) * H then (1:ℝ) else 0))
          + ∑ i ∈ B, 1 / (((N:ℝ)+1) * H) := by
        rw [Finset.sum_comm]
    _ = (∑ l ∈ Finset.range N,
            (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) *
              (((B.filter (fun i => d i ≤ ((l:ℝ)+2) * H)).card : ℝ)))
          + ∑ i ∈ B, 1 / (((N:ℝ)+1) * H) := by
        congr 1
        apply Finset.sum_congr rfl
        intro l _
        rw [← Finset.mul_sum, Finset.sum_boole]
    _ = (∑ l ∈ Finset.range N,
            (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) *
              (((B.filter (fun i => d i ≤ ((l:ℝ)+2) * H)).card : ℝ)))
          + (B.card : ℝ) / (((N:ℝ)+1) * H) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ (∑ l ∈ Finset.range N,
          (1 / (((l:ℝ)+1) * H) - 1 / (((l:ℝ)+2) * H)) * (A * (C * (((l:ℝ)+2) * H) + 1)))
        + (B.card : ℝ) / (((N:ℝ)+1) * H) := by
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

theorem sum_inv_max_le_count_finset {B : Finset ℕ} {d : ℕ → ℝ} {A C H : ℝ}
    (hA : 1 ≤ A) (hC : 0 < C) (hH : 0 < H)
    (hd : ∀ i ∈ B, 0 ≤ d i)
    (hcount : ∀ t : ℝ, 0 < t → ((B.filter (fun i => d i ≤ t)).card : ℝ) ≤ A * (C * t + 1))
    (hsat : A * (C * H + 1) ≤ (B.card : ℝ)) :
    ∑ i ∈ B, 1 / max H (d i)
      ≤ A * C * (1 + Real.log (1 + (B.card : ℝ) / (A * C * H))) + A / H + A * C := by
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA
  have hAC : 0 < A * C := mul_pos hApos hC
  have hACne : A * C ≠ 0 := ne_of_gt hAC
  have hACH : 0 < A * C * H := mul_pos hAC hH
  -- `A ≤ |B|`, so that the saturation level `t*` below is nonnegative.
  have hKA : A ≤ (B.card : ℝ) := by
    have hCHnn : 0 ≤ C * H := mul_nonneg (le_of_lt hC) (le_of_lt hH)
    have h1 : (1:ℝ) ≤ C * H + 1 := by linarith
    have h2 : A * 1 ≤ A * (C * H + 1) := mul_le_mul_of_nonneg_left h1 (le_of_lt hApos)
    linarith
  have hKpos : (0:ℝ) < (B.card : ℝ) := by linarith
  set tstar : ℝ := ((B.card:ℝ) - A) / (A * C) with htstar
  have htstar_nn : 0 ≤ tstar := by rw [htstar]; exact div_nonneg (by linarith) (le_of_lt hAC)
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
  -- The summed layer-cake bound and its telescoped form.
  have hsum := sum_inv_max_pointwise (B := B) (N := N) (d := d) (A := A) (C := C) (H := H)
      hH hd hcount
  have hid := sum_inv_max_layer_id A C H (ne_of_gt hH) N
  rw [hid] at hsum
  have hstep2 :
      A*C * (∑ l ∈ Finset.range N, 1/((l:ℝ)+1)) + (A/H)*(1 - 1/((N:ℝ)+1))
          + (B.card:ℝ)/(((N:ℝ)+1)*H)
        = A*C * (∑ l ∈ Finset.range N, 1/((l:ℝ)+1)) + A/H + ((B.card:ℝ) - A)/(((N:ℝ)+1)*H) := by
    field_simp
    ring
  -- `N ≤ |B|/(A C H)`, hence the harmonic sum is at most `1 + log(1 + |B|/(A C H))`.
  have hN_le_rho : (N:ℝ) ≤ (B.card : ℝ) / (A * C * H) := by
    calc (N:ℝ) ≤ x := hN_le_x
      _ = tstar / H := hx
      _ = ((B.card:ℝ) - A) / (A * C * H) := by rw [htstar, div_div]
      _ ≤ (B.card : ℝ) / (A * C * H) :=
            div_le_div_of_nonneg_right (by linarith) (le_of_lt hACH)
  have hharm : (∑ l ∈ Finset.range N, (1:ℝ)/((l:ℝ)+1))
      ≤ 1 + Real.log (1 + (B.card : ℝ) / (A * C * H)) := by
    rcases Nat.eq_zero_or_pos N with hN0 | hNpos
    · rw [hN0]
      simp only [Finset.range_zero, Finset.sum_empty]
      have h1 : (1:ℝ) ≤ 1 + (B.card : ℝ) / (A * C * H) := by
        have : 0 ≤ (B.card : ℝ) / (A * C * H) := le_of_lt (div_pos hKpos hACH)
        linarith
      have h2 := Real.log_nonneg h1
      linarith
    · have h1 := Work.Pert.LCH.harmonic_le_log N
      have h2 : Real.log (N:ℝ) ≤ Real.log (1 + (B.card : ℝ) / (A * C * H)) := by
        apply Real.log_le_log
        · exact_mod_cast hNpos
        · linarith [hN_le_rho]
      linarith
  -- The tail term is at most `A C`.
  have hslack : ((B.card:ℝ) - A)/(((N:ℝ)+1)*H) ≤ A*C := by
    have h1 : (A*C) * tstar < (A*C) * (((N:ℝ)+1)*H) := mul_lt_mul_of_pos_left hxH hAC
    have h2 : (A*C) * tstar = (B.card:ℝ) - A := by
      rw [htstar]; exact mul_div_cancel₀ _ hACne
    rw [h2] at h1
    rw [div_le_iff₀ (by positivity)]
    linarith
  calc (∑ i ∈ B, 1 / max H (d i))
      ≤ A*C * (∑ l ∈ Finset.range N, 1/((l:ℝ)+1)) + A/H + ((B.card:ℝ) - A)/(((N:ℝ)+1)*H) := by
        rw [← hstep2]; exact hsum
    _ ≤ A*C * (1 + Real.log (1 + (B.card : ℝ) / (A * C * H))) + A/H + A*C := by
        apply add_le_add
        · apply add_le_add
          · exact mul_le_mul_of_nonneg_left hharm (le_of_lt hAC)
          · exact le_rfl
        · exact hslack

end Work.Pert
