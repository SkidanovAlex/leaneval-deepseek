import Mathlib.Algebra.Order.Ring.Star
import Submission.Commons.Analysis.Real.exp_sub_one_sub_le
import Submission.Commons.Analysis.Real.mul_exp_sub_one_sub_le
import Submission.Commons.Probability.Chernoff.chernoff_two_sided_finite_weighted

namespace Commons.Combinatorics.BalancedColouring

open Finset

/-- **Sum over all `t`-colourings of a product over a finite set.**

For a finite set `S ⊆ ι` and `g : ι → Fin t → ℝ`,
`∑_{i : ι → Fin t} ∏_{e ∈ S} g e (i e) = t ^ (card ι - card S) * ∏_{e ∈ S} ∑_{a} g e a`. -/
theorem sum_prod_pi_fin {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) (t : ℕ)
    (g : ι → Fin t → ℝ) :
    (∑ i : ι → Fin t, ∏ e ∈ S, g e (i e))
      = (t : ℝ) ^ (Fintype.card ι - S.card) * ∏ e ∈ S, ∑ a : Fin t, g e a := by
  classical
  have h1 : (∑ i : ι → Fin t, ∏ e ∈ S, g e (i e))
      = ∑ i : ι → Fin t, ∏ e : ι, (if e ∈ S then g e (i e) else 1) := by
    apply Finset.sum_congr rfl
    intro i _
    exact (Fintype.prod_extend_by_one S (fun e => g e (i e))).symm
  have h2 : (∑ i : ι → Fin t, ∏ e : ι, (if e ∈ S then g e (i e) else 1))
      = ∏ e : ι, (if e ∈ S then (∑ a : Fin t, g e a) else (t : ℝ)) := by
    have h := Finset.sum_prod_piFinset (s := (Finset.univ : Finset (Fin t)))
      (g := fun e a => if e ∈ S then g e a else (1 : ℝ))
    simpa using h
  have h3 : (∏ e : ι, (if e ∈ S then (∑ a : Fin t, g e a) else (t : ℝ)))
      = (∏ e ∈ S, (∑ a : Fin t, g e a)) * (t : ℝ) ^ (Fintype.card ι - S.card) := by
    have hmul : (∏ e : ι, (if e ∈ S then (∑ a : Fin t, g e a) else (t : ℝ)))
        = (∏ e : ι, (if e ∈ S then (∑ a : Fin t, g e a) else 1))
          * (∏ e : ι, (if e ∈ S then (1 : ℝ) else (t : ℝ))) := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro e _
      by_cases h : e ∈ S <;> simp [h]
    rw [hmul, Fintype.prod_extend_by_one]
    have hScompl : ∀ e : ι, (if e ∈ S then (1 : ℝ) else (t : ℝ)) = (if e ∈ Sᶜ then (t : ℝ) else 1) := by
      intro e
      by_cases h : e ∈ S <;> simp [h, Finset.mem_compl]
    rw [Finset.prod_congr rfl (fun e _ => hScompl e), Fintype.prod_extend_by_one,
      Finset.prod_const, Finset.card_compl]
  rw [h1, h2, h3, mul_comm]

/-- The sum over `Fin t` of `if a = j then E else 1`. -/
theorem sum_ite_fin {t : ℕ} (ht : 1 ≤ t) (j : Fin t) (E : ℝ) :
    (∑ a : Fin t, (if a = j then E else 1)) = (t : ℝ) - 1 + E := by
  have h1 : (∑ a : Fin t, (if a = j then E else 1))
      = E + ∑ a ∈ (Finset.univ : Finset (Fin t)).erase j, (if a = j then E else 1) := by
    rw [← Finset.insert_erase (Finset.mem_univ j),
      Finset.sum_insert (Finset.notMem_erase j _)]
    simp
  have h2 : (∑ a ∈ (Finset.univ : Finset (Fin t)).erase j, (if a = j then E else 1))
      = ∑ _a ∈ (Finset.univ : Finset (Fin t)).erase j, (1 : ℝ) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [if_neg (Finset.mem_erase.mp ha).1]
  rw [h1, h2, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub ht]
  ring

/-- **Weighted Chernoff bound for `Fin t`-colourings.**  Let `S` be a finite set of weighted
elements, `w e ∈ [0,C]`, `j` a fixed colour, `t ≥ 2`.  The number of colourings
`i : ι → Fin t` for which the total weight of the elements of `S` coloured `j` exceeds
`a + τ` is at most `t ^ card ι * exp (-(τ^2) / (2 C (a + τ/3)))`, provided
`(∑_{e ∈ S} w e) / t ≤ a`. -/
private theorem card_bad_le_aux {ι : Type*} [Fintype ι] [DecidableEq ι] (t : ℕ) (ht : 2 ≤ t)
    (S : Finset ι) (j : Fin t) (w : ι → ℝ) (hw0 : ∀ e, 0 ≤ w e)
    {C a τ : ℝ} (hC : 0 < C) (hwC : ∀ e ∈ S, w e ≤ C) (ha : 0 ≤ a) (hτ : 0 ≤ τ)
    (hμa : (∑ e ∈ S, w e) / (t : ℝ) ≤ a) :
    ((Finset.univ.filter (fun i : ι → Fin t =>
        a + τ < (S.filter (fun e => i e = j)).sum w)).card : ℝ)
      ≤ (t : ℝ) ^ (Fintype.card ι) * Real.exp (-(τ ^ 2) / (2 * C * (a + τ / 3))) := by
  classical
  have ht1 : (1 : ℕ) ≤ t := le_trans (by norm_num) ht
  have htR : (0 : ℝ) < (t : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) ht)
  have hsum_nonneg : 0 ≤ ∑ e ∈ S, w e := Finset.sum_nonneg (fun e _ => hw0 e)
  by_cases hsum0 : (∑ e ∈ S, w e) = 0
  · have hwz : ∀ e ∈ S, w e = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => hw0 e)).mp hsum0
    have hbad_empty : (Finset.univ.filter (fun i : ι → Fin t =>
        a + τ < (S.filter (fun e => i e = j)).sum w)) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro i _
      have : (S.filter (fun e => i e = j)).sum w = 0 :=
        Finset.sum_eq_zero (fun e he => hwz e (Finset.mem_of_mem_filter e he))
      rw [this]
      linarith
    rw [hbad_empty, Finset.card_empty]
    simp only [Nat.cast_zero]
    positivity
  · have hsum_pos : 0 < ∑ e ∈ S, w e := lt_of_le_of_ne hsum_nonneg (Ne.symm hsum0)
    set μ : ℝ := (∑ e ∈ S, w e) / (t : ℝ) with hμdef
    have hμpos : 0 < μ := by rw [hμdef]; exact div_pos hsum_pos htR
    have hμnn : 0 ≤ μ := le_of_lt hμpos
    set B : ℝ := a + τ / 3 with hBdef
    have hBpos : 0 < B := by rw [hBdef]; linarith
    set u : ℝ := τ / B with hudef
    have hBu : B * u = τ := by rw [hudef]; field_simp
    have hkey : μ * (Real.exp u - 1 - u) ≤ u * τ / 2 := by
      have hle : μ ≤ B - τ / 3 := by rw [hBdef]; linarith [hμa]
      have h := Commons.Analysis.Real.mul_exp_sub_one_sub_le hBpos hτ hμnn hle
      simpa only [← hudef] using h
    set k : ℝ := u / C with hkdef
    have hknn : 0 ≤ k := by rw [hkdef]; positivity
    have hkC : k * C = u := by rw [hkdef]; field_simp
    have hX : ∀ i : ι → Fin t, (S.filter (fun e => i e = j)).sum w
        = ∑ e ∈ S, (if i e = j then w e else 0) :=
      fun i => Finset.sum_filter (s := S) (p := fun e => i e = j) (f := w)
    have hstep1 : ((Finset.univ.filter (fun i : ι → Fin t =>
          a + τ < (S.filter (fun e => i e = j)).sum w)).card : ℝ)
        ≤ ∑ i : ι → Fin t,
            Real.exp (k * ((S.filter (fun e => i e = j)).sum w - (μ + τ))) := by
      have hcard : ((Finset.univ.filter (fun i : ι → Fin t =>
            a + τ < (S.filter (fun e => i e = j)).sum w)).card : ℝ)
          = ∑ i ∈ Finset.univ.filter (fun i : ι → Fin t =>
              a + τ < (S.filter (fun e => i e = j)).sum w), (1 : ℝ) := by
        rw [Finset.card_eq_sum_ones]
        simp
      rw [hcard]
      refine le_trans (Finset.sum_le_sum ?_)
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => Real.exp_nonneg _))
      intro i hi
      have hlt : a + τ < (S.filter (fun e => i e = j)).sum w := (Finset.mem_filter.mp hi).2
      have hnonneg : 0 ≤ k * ((S.filter (fun e => i e = j)).sum w - (μ + τ)) := by
        apply mul_nonneg hknn
        linarith [hlt, hμa]
      calc (1 : ℝ) = Real.exp 0 := by simp
        _ ≤ Real.exp (k * ((S.filter (fun e => i e = j)).sum w - (μ + τ))) :=
            Real.exp_le_exp.mpr hnonneg
    have hstep2 : (∑ i : ι → Fin t,
          Real.exp (k * ((S.filter (fun e => i e = j)).sum w - (μ + τ))))
        = Real.exp (-(k * (μ + τ)))
          * ∑ i : ι → Fin t, Real.exp (k * (S.filter (fun e => i e = j)).sum w) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← Real.exp_add]
      congr 1
      ring
    have hstep3 : (∑ i : ι → Fin t, Real.exp (k * (S.filter (fun e => i e = j)).sum w))
        = (t : ℝ) ^ (Fintype.card ι - S.card)
          * ∏ e ∈ S, ((t : ℝ) - 1 + Real.exp (k * w e)) := by
      have hprod : ∀ i : ι → Fin t, Real.exp (k * (S.filter (fun e => i e = j)).sum w)
          = ∏ e ∈ S, (if i e = j then Real.exp (k * w e) else 1) := by
        intro i
        rw [hX i, Finset.mul_sum, Real.exp_sum]
        apply Finset.prod_congr rfl
        intro e _
        by_cases h : i e = j <;> simp [h]
      rw [Finset.sum_congr rfl (fun i _ => hprod i)]
      rw [sum_prod_pi_fin S t (fun e a => if a = j then Real.exp (k * w e) else 1)]
      congr 1
      apply Finset.prod_congr rfl
      intro e _
      exact sum_ite_fin ht1 j (Real.exp (k * w e))
    have hstep4 : (∏ e ∈ S, ((t : ℝ) - 1 + Real.exp (k * w e)))
        ≤ (t : ℝ) ^ (S.card) * Real.exp ((μ / C) * (Real.exp u - 1)) := by
      have hper : ∀ e ∈ S, ((t : ℝ) - 1 + Real.exp (k * w e))
          ≤ (t : ℝ) * Real.exp ((Real.exp (k * w e) - 1) / (t : ℝ)) := by
        intro e _
        have h := Commons.Probability.Chernoff.per_coord_exp_le (1 / (t : ℝ)) (w e) k
        rw [show (1 / (t : ℝ)) * (Real.exp (k * w e) - 1)
            = (Real.exp (k * w e) - 1) / (t : ℝ) by ring] at h
        have h2 := mul_le_mul_of_nonneg_left h (le_of_lt htR)
        have h3 : (t : ℝ) * (1 - 1 / (t : ℝ) + 1 / (t : ℝ) * Real.exp (k * w e))
            = (t : ℝ) - 1 + Real.exp (k * w e) := by field_simp
        rw [h3] at h2
        exact h2
      have hterm_nn : ∀ e ∈ S, 0 ≤ (t : ℝ) - 1 + Real.exp (k * w e) := by
        intro e _
        have htR1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht1
        have := Real.exp_pos (k * w e)
        linarith
      calc (∏ e ∈ S, ((t : ℝ) - 1 + Real.exp (k * w e)))
          ≤ ∏ e ∈ S, ((t : ℝ) * Real.exp ((Real.exp (k * w e) - 1) / (t : ℝ))) :=
            Finset.prod_le_prod₀ hterm_nn hper
        _ = (t : ℝ) ^ (S.card)
              * ∏ e ∈ S, Real.exp ((Real.exp (k * w e) - 1) / (t : ℝ)) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
        _ = (t : ℝ) ^ (S.card)
              * Real.exp (∑ e ∈ S, (Real.exp (k * w e) - 1) / (t : ℝ)) := by
            rw [Real.exp_sum]
        _ ≤ (t : ℝ) ^ (S.card) * Real.exp ((μ / C) * (Real.exp u - 1)) := by
            apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by positivity) _)
            apply Real.exp_le_exp.mpr
            have hchord : ∀ e ∈ S, Real.exp (k * w e) - 1 ≤ (w e / C) * (Real.exp u - 1) := by
              intro e he
              have h := Commons.Probability.Chernoff.chord_scaled (T := k) hC (hw0 e) (hwC e he)
              rwa [hkC] at h
            calc ∑ e ∈ S, (Real.exp (k * w e) - 1) / (t : ℝ)
                ≤ ∑ e ∈ S, ((w e / C) * (Real.exp u - 1)) / (t : ℝ) := by
                  apply Finset.sum_le_sum
                  intro e he
                  exact div_le_div_of_nonneg_right (hchord e he) (le_of_lt htR)
              _ = ((∑ e ∈ S, w e / C) * (Real.exp u - 1)) / (t : ℝ) := by
                  rw [Finset.sum_mul, ← Finset.sum_div]
              _ = ((∑ e ∈ S, w e) / C * (Real.exp u - 1)) / (t : ℝ) := by
                  rw [Finset.sum_div]
              _ = (μ / C) * (Real.exp u - 1) := by
                  rw [hμdef]; field_simp
    have hexp : -(k * (μ + τ)) + (μ / C) * (Real.exp u - 1) ≤ -(τ ^ 2) / (2 * C * B) := by
      have hrewrite : -(k * (μ + τ)) + (μ / C) * (Real.exp u - 1)
          = -k * τ + (μ / C) * (Real.exp u - 1 - u) := by
        have hA : (μ / C) * u = μ * k := by rw [← hkC]; field_simp
        rw [show (μ / C) * (Real.exp u - 1) = (μ / C) * (Real.exp u - 1 - u) + (μ / C) * u
          by ring, hA]
        ring
      rw [hrewrite]
      have hCne : C ≠ 0 := ne_of_gt hC
      have hgoalC : C * (-k * τ + (μ / C) * (Real.exp u - 1 - u)) ≤ C * (-(τ ^ 2) / (2 * C * B)) := by
        have hr : C * (-(τ ^ 2) / (2 * C * B)) = -(τ ^ 2) / (2 * B) := by field_simp
        rw [hr]
        have hl : C * (-k * τ + (μ / C) * (Real.exp u - 1 - u))
            = -u * τ + μ * (Real.exp u - 1 - u) := by
          have h1 : C * (μ / C) = μ := by field_simp
          have h2 : C * k = u := by rw [mul_comm]; exact hkC
          calc C * (-k * τ + (μ / C) * (Real.exp u - 1 - u))
              = -(C * k) * τ + (C * (μ / C)) * (Real.exp u - 1 - u) := by ring
            _ = -u * τ + μ * (Real.exp u - 1 - u) := by rw [h1, h2]
        rw [hl]
        have hr2 : τ ^ 2 / (2 * B) = u * τ / 2 := by rw [← hBu]; field_simp
        rw [neg_div, hr2]
        linarith [hkey]
      exact le_of_mul_le_mul_left hgoalC hC
    have hfinal : ((Finset.univ.filter (fun i : ι → Fin t =>
          a + τ < (S.filter (fun e => i e = j)).sum w)).card : ℝ)
        ≤ (t : ℝ) ^ (Fintype.card ι) * Real.exp (-(τ ^ 2) / (2 * C * B)) := by
      calc ((Finset.univ.filter (fun i : ι → Fin t =>
            a + τ < (S.filter (fun e => i e = j)).sum w)).card : ℝ)
          ≤ ∑ i : ι → Fin t,
              Real.exp (k * ((S.filter (fun e => i e = j)).sum w - (μ + τ))) := hstep1
        _ = Real.exp (-(k * (μ + τ)))
              * ∑ i : ι → Fin t, Real.exp (k * (S.filter (fun e => i e = j)).sum w) := hstep2
        _ ≤ Real.exp (-(k * (μ + τ))) * ((t : ℝ) ^ (Fintype.card ι - S.card)
              * ∏ e ∈ S, ((t : ℝ) - 1 + Real.exp (k * w e))) := by
            rw [← hstep3]
        _ ≤ Real.exp (-(k * (μ + τ))) * ((t : ℝ) ^ (Fintype.card ι - S.card)
              * ((t : ℝ) ^ (S.card) * Real.exp ((μ / C) * (Real.exp u - 1)))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hstep4 (pow_nonneg (by positivity) _)) (Real.exp_nonneg _)
        _ = (t : ℝ) ^ (Fintype.card ι)
              * Real.exp (-(k * (μ + τ)) + (μ / C) * (Real.exp u - 1)) := by
            have hpow : (t : ℝ) ^ (Fintype.card ι - S.card) * (t : ℝ) ^ (S.card)
                = (t : ℝ) ^ (Fintype.card ι) := by
              rw [← pow_add, Nat.sub_add_cancel (Finset.card_le_univ S)]
            rw [show Real.exp (-(k * (μ + τ)))
                  * ((t : ℝ) ^ (Fintype.card ι - S.card)
                    * ((t : ℝ) ^ (S.card) * Real.exp ((μ / C) * (Real.exp u - 1))))
                = (Real.exp (-(k * (μ + τ))) * Real.exp ((μ / C) * (Real.exp u - 1)))
                  * ((t : ℝ) ^ (Fintype.card ι - S.card) * (t : ℝ) ^ (S.card)) by ring,
              hpow, ← Real.exp_add]
            ring
        _ ≤ (t : ℝ) ^ (Fintype.card ι) * Real.exp (-(τ ^ 2) / (2 * C * B)) :=
            mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (pow_nonneg (by positivity) _)
    simpa only [hBdef] using hfinal

/-- **Balanced random `t`-colouring (probabilistic method).**

Let `ι` be a finite set of "edges" with weights `w e ≥ 0`, bounded by `C`, `Γ` a
finite set of "colours", `t ≥ 2` a number of parts, and `χ e j` the colour that
edge `e` receives when it is put in part `j`.  Assume that the part determines
the colour, in the sense that `χ e j = c` forces `j = jof c`, and that for every
colour `c` the total weight of the edges that *would* receive colour `c` (when
put in its prescribed part `jof c`) is at most `W`.

Then, provided the union bound
`|Γ| * 2 * exp (-τ² / (2 * (C * (W / t + τ / 3)))) < 1`
holds, there is a single assignment `i : ι → Fin t` of every edge to a part such
that the total weight of the edges receiving any fixed colour `c` is at most
`W / t + τ`.

This is the "randomly spread the colour classes over `t` sub-colourings"
argument (each edge independently choosing one of the `t` parts, Chernoff +
union bound). -/
theorem exists_colouring_bounded_load {ι Γ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype Γ] [DecidableEq Γ] (t : ℕ) (ht : 2 ≤ t) (jof : Γ → Fin t)
    (χ : ι → Fin t → Γ) (hχ : ∀ e j c, χ e j = c → j = jof c)
    (w : ι → ℝ) (hw0 : ∀ e, 0 ≤ w e) {C W τ : ℝ} (hC0 : 0 ≤ C) (hwle : ∀ e, w e ≤ C)
    (hW0 : 0 ≤ W) (hτ0 : 0 ≤ τ)
    (hW : ∀ c : Γ, (Finset.univ.filter (fun e => χ e (jof c) = c)).sum w ≤ W)
    (hcard : (Fintype.card Γ : ℝ) *
      (2 * Real.exp (-(τ ^ 2) / (2 * (C * (W / t + τ / 3))))) < 1) :
    ∃ i : ι → Fin t, ∀ c : Γ,
      (Finset.univ.filter (fun e => χ e (i e) = c)).sum w ≤ W / t + τ := by
  classical
  by_cases hCz : C = 0
  · -- if `C = 0` all weights vanish and the bound is trivial
    refine ⟨fun _ => ⟨0, by omega⟩, fun c => ?_⟩
    have hw : ∀ e, w e = 0 := fun e => le_antisymm (by simpa [hCz] using hwle e) (hw0 e)
    simp only [hw, Finset.sum_const_zero]
    positivity
  · have hCpos : 0 < C := lt_of_le_of_ne hC0 (Ne.symm hCz)
    have ht1 : (1 : ℕ) ≤ t := le_trans (by norm_num) ht
    -- per colour bound
    have hper : ∀ c : Γ,
        ((Finset.univ.filter (fun i : ι → Fin t =>
          W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w)).card : ℝ)
        ≤ (t : ℝ) ^ (Fintype.card ι)
            * Real.exp (-(τ ^ 2) / (2 * (C * (W / t + τ / 3)))) := by
      intro c
      set S : Finset ι := Finset.univ.filter (fun e => χ e (jof c) = c) with hSdef
      have hsub : Finset.univ.filter (fun i : ι → Fin t =>
            W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w)
          ⊆ Finset.univ.filter (fun i : ι → Fin t =>
            W / t + τ < (S.filter (fun e => i e = jof c)).sum w) := by
        intro i hi
        rw [Finset.mem_filter] at hi ⊢
        refine ⟨Finset.mem_univ _, ?_⟩
        have hsub2 : Finset.univ.filter (fun e => χ e (i e) = c)
            ⊆ S.filter (fun e => i e = jof c) := by
          intro e he
          rw [Finset.mem_filter] at he ⊢
          obtain ⟨-, hec⟩ := he
          have hje : i e = jof c := hχ e (i e) c hec
          refine ⟨?_, hje⟩
          rw [hSdef, Finset.mem_filter]
          exact ⟨Finset.mem_univ e, by rw [← hje]; exact hec⟩
        have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun e _ _ => hw0 e)
        linarith [hi.2]
      have hcard_le : ((Finset.univ.filter (fun i : ι → Fin t =>
            W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w)).card : ℝ)
          ≤ ((Finset.univ.filter (fun i : ι → Fin t =>
            W / t + τ < (S.filter (fun e => i e = jof c)).sum w)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      have haux := card_bad_le_aux t ht S (jof c) w hw0 hCpos (fun e _ => hwle e)
        (by positivity) hτ0 (div_le_div_of_nonneg_right (hW c) (by positivity))
      calc ((Finset.univ.filter (fun i : ι → Fin t =>
              W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w)).card : ℝ)
          ≤ _ := hcard_le
        _ ≤ (t : ℝ) ^ (Fintype.card ι)
              * Real.exp (-(τ ^ 2) / (2 * C * (W / t + τ / 3))) := haux
        _ = (t : ℝ) ^ (Fintype.card ι)
              * Real.exp (-(τ ^ 2) / (2 * (C * (W / t + τ / 3)))) := by
            congr 1
            rw [mul_assoc]
    -- union bound over the colours
    have hunion : ((Finset.univ.filter (fun i : ι → Fin t => ∃ c : Γ,
        W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w)).card : ℝ)
        < (t : ℝ) ^ (Fintype.card ι) := by
      have hsub : Finset.univ.filter (fun i : ι → Fin t => ∃ c : Γ,
            W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w)
          ⊆ Finset.univ.biUnion (fun c : Γ => Finset.univ.filter (fun i : ι → Fin t =>
            W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w)) := by
        intro i hi
        rw [Finset.mem_filter] at hi
        obtain ⟨-, c, hc⟩ := hi
        rw [Finset.mem_biUnion]
        exact ⟨c, Finset.mem_univ c, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hc⟩⟩
      have h1 : ((Finset.univ.filter (fun i : ι → Fin t => ∃ c : Γ,
            W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w)).card : ℝ)
          ≤ ∑ c : Γ, ((Finset.univ.filter (fun i : ι → Fin t =>
            W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w)).card : ℝ) := by
        calc ((Finset.univ.filter (fun i : ι → Fin t => ∃ c : Γ,
              W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w)).card : ℝ)
            ≤ ((Finset.univ.biUnion (fun c : Γ => Finset.univ.filter (fun i : ι → Fin t =>
              W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w))).card : ℝ) :=
              by exact_mod_cast Finset.card_le_card hsub
          _ ≤ ((∑ c ∈ Finset.univ, (Finset.univ.filter (fun i : ι → Fin t =>
              W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w)).card) : ℝ) :=
              by exact_mod_cast Finset.card_biUnion_le
          _ = ∑ c : Γ, ((Finset.univ.filter (fun i : ι → Fin t =>
              W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w)).card : ℝ) := by
              rfl
      have h2 : ∑ c : Γ, ((Finset.univ.filter (fun i : ι → Fin t =>
            W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w)).card : ℝ)
          ≤ ∑ _c : Γ, (t : ℝ) ^ (Fintype.card ι)
              * Real.exp (-(τ ^ 2) / (2 * (C * (W / t + τ / 3)))) :=
        Finset.sum_le_sum (fun c _ => hper c)
      have h3 : ∑ _c : Γ, (t : ℝ) ^ (Fintype.card ι)
            * Real.exp (-(τ ^ 2) / (2 * (C * (W / t + τ / 3))))
          = (Fintype.card Γ : ℝ) * ((t : ℝ) ^ (Fintype.card ι)
              * Real.exp (-(τ ^ 2) / (2 * (C * (W / t + τ / 3))))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have h4 : (Fintype.card Γ : ℝ) * ((t : ℝ) ^ (Fintype.card ι)
            * Real.exp (-(τ ^ 2) / (2 * (C * (W / t + τ / 3)))))
          < (t : ℝ) ^ (Fintype.card ι) := by
        have hepos : 0 < Real.exp (-(τ ^ 2) / (2 * (C * (W / t + τ / 3)))) := Real.exp_pos _
        have hΓe : (Fintype.card Γ : ℝ) * Real.exp (-(τ ^ 2) / (2 * (C * (W / t + τ / 3)))) < 1 := by
          have h1 : (Fintype.card Γ : ℝ) * Real.exp (-(τ ^ 2) / (2 * (C * (W / t + τ / 3))))
              ≤ (Fintype.card Γ : ℝ)
                * (2 * Real.exp (-(τ ^ 2) / (2 * (C * (W / t + τ / 3))))) :=
            mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg _)
          have h2 : (Fintype.card Γ : ℝ)
                * (2 * Real.exp (-(τ ^ 2) / (2 * (C * (W / t + τ / 3))))) < 1 := hcard
          linarith
        have htpow : 0 < (t : ℝ) ^ (Fintype.card ι) := by positivity
        calc (Fintype.card Γ : ℝ) * ((t : ℝ) ^ (Fintype.card ι)
              * Real.exp (-(τ ^ 2) / (2 * (C * (W / t + τ / 3)))))
            = ((Fintype.card Γ : ℝ) * Real.exp (-(τ ^ 2) / (2 * (C * (W / t + τ / 3)))))
              * (t : ℝ) ^ (Fintype.card ι) := by ring
          _ < 1 * (t : ℝ) ^ (Fintype.card ι) := mul_lt_mul_of_pos_right hΓe htpow
          _ = (t : ℝ) ^ (Fintype.card ι) := by ring
      linarith [h1, h2, h3, h4]
    -- extract an assignment outside the union of the bad sets
    have hne : Finset.univ.filter (fun i : ι → Fin t => ∃ c : Γ,
        W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w) ≠ Finset.univ := by
      intro huniv
      have hcarduniv : ((Finset.univ.filter (fun i : ι → Fin t => ∃ c : Γ,
            W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w)).card : ℝ)
          = (t : ℝ) ^ (Fintype.card ι) := by
        rw [huniv, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
        push_cast
        ring
      linarith [hunion, hcarduniv]
    have hssub : Finset.univ.filter (fun i : ι → Fin t => ∃ c : Γ,
        W / t + τ < (Finset.univ.filter (fun e => χ e (i e) = c)).sum w) ⊂ Finset.univ := by
      rw [Finset.ssubset_iff_subset_ne]
      exact ⟨Finset.filter_subset _ _, hne⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_of_ssubset hssub
    refine ⟨i, fun c => ?_⟩
    by_contra hlt
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, c, not_le.mp hlt⟩)

end Commons.Combinatorics.BalancedColouring