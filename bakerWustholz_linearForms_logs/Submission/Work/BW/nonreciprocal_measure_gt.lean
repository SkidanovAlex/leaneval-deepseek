import Mathlib
import Submission.Work.BW.roots_facts
import Submission.Work.BW.pow_sum_roots_int
import Submission.Work.BW.inv_pow_sum_roots_int
import Submission.Work.BW.multiset_eq_of_powSum_eq
import Submission.Work.BW.roots_map_conj_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Polynomial

/-! ## Auxiliary lemmas about multisets of real / complex numbers -/

private theorem nrm_sum_sub {α β : Type*} [AddCommGroup β] (s : Multiset α) (f g : α → β) :
    (s.map (fun a => f a - g a)).sum = (s.map f).sum - (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons,
        Multiset.map_cons, Multiset.sum_cons, ih]
      abel

private theorem nrm_norm_sum_le {α : Type*} (s : Multiset α) (f : α → ℂ) :
    ‖(s.map f).sum‖ ≤ (s.map (fun a => ‖f a‖)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
      exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

private theorem nrm_sum_le_sum {α : Type*} (s : Multiset α) (f g : α → ℝ)
    (h : ∀ a ∈ s, f a ≤ g a) : (s.map f).sum ≤ (s.map g).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons]
      exact add_le_add (h a (Multiset.mem_cons_self a s))
        (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

private theorem nrm_prod_nonneg {α : Type*} (s : Multiset α) (f : α → ℝ)
    (h : ∀ a ∈ s, 0 ≤ f a) : 0 ≤ (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact mul_nonneg (h a (Multiset.mem_cons_self a s))
        (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

private theorem nrm_prod_pos {α : Type*} (s : Multiset α) (f : α → ℝ)
    (h : ∀ a ∈ s, 0 < f a) : 0 < (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons]
      exact mul_pos (h a (Multiset.mem_cons_self a s))
        (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

private theorem nrm_prod_le_prod {α : Type*} (s : Multiset α) (f g : α → ℝ)
    (hf : ∀ a ∈ s, 0 ≤ f a) (h : ∀ a ∈ s, f a ≤ g a) :
    (s.map f).prod ≤ (s.map g).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have hfa : 0 ≤ f a := hf a (Multiset.mem_cons_self a s)
      have hga : 0 ≤ g a := le_trans hfa (h a (Multiset.mem_cons_self a s))
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
      exact mul_le_mul (h a (Multiset.mem_cons_self a s))
        (ih (fun b hb => hf b (Multiset.mem_cons_of_mem hb))
          (fun b hb => h b (Multiset.mem_cons_of_mem hb)))
        (nrm_prod_nonneg s f fun b hb => hf b (Multiset.mem_cons_of_mem hb)) hga

private theorem nrm_log_prod {α : Type*} (s : Multiset α) (f : α → ℝ)
    (h : ∀ a ∈ s, 0 < f a) :
    Real.log ((s.map f).prod) = (s.map (fun a => Real.log (f a))).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      have ha : 0 < f a := h a (Multiset.mem_cons_self a s)
      have hs : 0 < (s.map f).prod := nrm_prod_pos s f fun b hb => h b (Multiset.mem_cons_of_mem hb)
      rw [Multiset.map_cons, Multiset.prod_cons, Real.log_mul (ne_of_gt ha) (ne_of_gt hs),
        Multiset.map_cons, Multiset.sum_cons, ih fun b hb => h b (Multiset.mem_cons_of_mem hb)]

/-- For a monic integer polynomial the Mahler measure of its image in `ℂ[X]` is the product of
`max 1 ‖z‖` over its complex roots. -/
private theorem nrm_mahler_map (P : Polynomial ℤ) (hP : P.Monic) :
    (P.map (Int.castRingHom ℂ)).mahlerMeasure
      = ((P.map (Int.castRingHom ℂ)).roots.map (fun z => max 1 ‖z‖)).prod := by
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    leadingCoeff_map_of_injective (Int.castRingHom ℂ).injective_int, hP.leadingCoeff, map_one,
    norm_one, one_mul]

private theorem nrm_norm_prod {α : Type*} (s : Multiset α) (f : α → ℂ) :
    ‖(s.map f).prod‖ = (s.map (fun a => ‖f a‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul, Multiset.map_cons, Multiset.prod_cons,
        ih]

/-! ## Elementary real analysis lemmas -/

private theorem nrm_log_max_one (x : ℝ) (hx : 0 < x) :
    Real.log (max 1 x) = max 0 (Real.log x) := by
  by_cases h : 1 ≤ x
  · rw [max_eq_right h]
    exact (max_eq_right (Real.log_nonneg h)).symm
  · have h' : x ≤ 1 := le_of_lt (not_le.mp h)
    rw [max_eq_left h', Real.log_one]
    exact (max_eq_left (Real.log_nonpos (le_of_lt hx) h')).symm

private theorem nrm_abs_one_sub_exp_neg (t : ℝ) :
    |1 - Real.exp (-t)| ≤ |t| * Real.exp |t| := by
  by_cases ht : 0 ≤ t
  · have h1 : 1 - Real.exp (-t) ≤ t := by
      have := Real.add_one_le_exp (-t); linarith
    have h2 : 0 ≤ 1 - Real.exp (-t) := by
      have h : Real.exp (-t) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
      rw [Real.exp_zero] at h
      linarith
    rw [abs_of_nonneg h2, abs_of_nonneg ht]
    calc 1 - Real.exp (-t) ≤ t := h1
      _ = 1 * t := by ring
      _ ≤ Real.exp t * t := mul_le_mul_of_nonneg_right (Real.one_le_exp ht) ht
      _ = t * Real.exp t := by ring
  · have ht' : t < 0 := not_le.mp ht
    have h1 : Real.exp (-t) - 1 ≤ (-t) * Real.exp (-t) := by
      have hle : 1 + t ≤ Real.exp t := by have := Real.add_one_le_exp t; linarith
      have hmul : (1 + t) * Real.exp (-t) ≤ 1 := by
        calc (1 + t) * Real.exp (-t) ≤ Real.exp t * Real.exp (-t) :=
              mul_le_mul_of_nonneg_right hle (Real.exp_nonneg _)
          _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have hexp : (1 + t) * Real.exp (-t) = Real.exp (-t) + t * Real.exp (-t) := by ring
      linarith [hmul, hexp]
    have h2 : 1 - Real.exp (-t) ≤ 0 := by
      have hpos : 1 ≤ Real.exp (-t) := Real.one_le_exp (by linarith)
      linarith
    rw [abs_of_nonpos h2, abs_of_neg ht']
    linarith [h1]

private theorem nrm_exp_sq_inv_pow (x : ℝ) (hx : 0 < x) (m : ℕ) :
    ((x ^ 2)⁻¹) ^ m = Real.exp (-(2 * (m : ℝ) * Real.log x)) := by
  have h2 : x ^ 2 = Real.exp (2 * Real.log x) := by
    have h : Real.exp (2 * Real.log x) = x ^ 2 := by
      rw [show (2 : ℝ) * Real.log x = ((2 : ℕ) : ℝ) * Real.log x by norm_num, Real.exp_nat_mul,
        Real.exp_log hx]
    exact h.symm
  rw [h2, ← Real.exp_neg, ← Real.exp_nat_mul]
  congr 1
  ring

/-! ## The analytic estimate -/

/-- If `S` is a conjugation-invariant multiset of nonzero complex numbers, all of whose elements
have `|log ‖z‖|` summing to at most `2 * δ`, then the `m`-th power sum of `S` differs from the
`m`-th power sum of the multiset of inverses by at most `4 m δ exp (6 m δ)`. -/
private theorem nrm_pow_sum_sub_inv_bound (S : Multiset ℂ) (δ : ℝ) (m : ℕ)
    (hne : ∀ z ∈ S, z ≠ 0)
    (hconj : S.map (starRingEnd ℂ) = S)
    (hlog : (S.map (fun z => |Real.log ‖z‖|)).sum ≤ 2 * δ) :
    ‖(S.map (fun z => z ^ m)).sum - (S.map (fun z => (z⁻¹) ^ m)).sum‖
      ≤ 4 * (m : ℝ) * δ * Real.exp (6 * (m : ℝ) * δ) := by
  have hsingle : ∀ z ∈ S, |Real.log ‖z‖| ≤ 2 * δ := by
    have hnonneg : ∀ x ∈ S.map (fun z => |Real.log ‖z‖|), 0 ≤ x := by
      intro x hx
      obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.mp hx
      exact abs_nonneg _
    intro z hz
    have hmem : |Real.log ‖z‖| ∈ S.map (fun z => |Real.log ‖z‖|) :=
      Multiset.mem_map.mpr ⟨z, hz, rfl⟩
    exact le_trans (Multiset.single_le_sum hnonneg _ hmem) hlog
  -- rewrite the sum of inverses as a "conjugate-swapped" sum
  have hmap1 : S.map (fun z => (z⁻¹) ^ m)
      = S.map (fun z => (starRingEnd ℂ z) ^ m * ((((‖z‖ ^ 2)⁻¹ : ℝ)) : ℂ) ^ m) := by
    refine Multiset.map_congr rfl ?_
    intro z _
    rw [Complex.inv_def, mul_pow]
    congr 2
    rw [Complex.normSq_eq_norm_sq]
  have hmap2 : S.map (fun z => (starRingEnd ℂ z) ^ m * ((((‖z‖ ^ 2)⁻¹ : ℝ)) : ℂ) ^ m)
      = S.map (fun z => z ^ m * ((((‖z‖ ^ 2)⁻¹ : ℝ)) : ℂ) ^ m) := by
    conv_lhs => rw [← hconj]
    simp only [Multiset.map_map, Function.comp_apply]
    refine Multiset.map_congr rfl ?_
    intro z _
    have h1 : (starRingEnd ℂ) ((starRingEnd ℂ) z) = z := by simp
    simp only [h1, Complex.norm_conj]
  have hsum_inv : (S.map (fun z => (z⁻¹) ^ m)).sum
      = (S.map (fun z => z ^ m * ((((‖z‖ ^ 2)⁻¹ : ℝ)) : ℂ) ^ m)).sum := by
    rw [hmap1, hmap2]
  have hdiff : (S.map (fun z => z ^ m)).sum - (S.map (fun z => (z⁻¹) ^ m)).sum
      = (S.map (fun z => z ^ m * (1 - ((((‖z‖ ^ 2)⁻¹ : ℝ)) : ℂ) ^ m))).sum := by
    rw [hsum_inv, ← nrm_sum_sub]
    refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
    intro z _
    ring
  -- pointwise estimate
  have hpoint : ∀ z ∈ S, ‖z ^ m * (1 - ((((‖z‖ ^ 2)⁻¹ : ℝ)) : ℂ) ^ m)‖
      ≤ (2 * (m : ℝ) * Real.exp (6 * (m : ℝ) * δ)) * |Real.log ‖z‖| := by
    intro z hz
    have hz0 : z ≠ 0 := hne z hz
    have hρ : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    have hlamle : |Real.log ‖z‖| ≤ 2 * δ := hsingle z hz
    have hρexp : Real.exp (Real.log ‖z‖) = ‖z‖ := Real.exp_log hρ
    have hc : ((((‖z‖ ^ 2)⁻¹ : ℝ)) : ℂ) ^ m
        = ((Real.exp (-(2 * (m : ℝ) * Real.log ‖z‖)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, nrm_exp_sq_inv_pow ‖z‖ hρ m]
    have hnorm_z : ‖z ^ m‖ = Real.exp ((m : ℝ) * Real.log ‖z‖) := by
      rw [norm_pow]
      conv_lhs => rw [← hρexp]
      rw [← Real.exp_nat_mul]
    have hnorm1 : ‖(1 : ℂ) - ((Real.exp (-(2 * (m : ℝ) * Real.log ‖z‖)) : ℝ) : ℂ)‖
        = |1 - Real.exp (-(2 * (m : ℝ) * Real.log ‖z‖))| := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_def, Complex.normSq_ofReal,
        ← pow_two, Real.sqrt_sq_eq_abs]
    have hb1 : ‖(1 : ℂ) - ((((‖z‖ ^ 2)⁻¹ : ℝ)) : ℂ) ^ m‖
        ≤ 2 * (m : ℝ) * |Real.log ‖z‖| * Real.exp (2 * (m : ℝ) * |Real.log ‖z‖|) := by
      rw [hc, hnorm1]
      have h := nrm_abs_one_sub_exp_neg (2 * (m : ℝ) * Real.log ‖z‖)
      have ht : |2 * (m : ℝ) * Real.log ‖z‖| = 2 * (m : ℝ) * |Real.log ‖z‖| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_nonneg (Nat.cast_nonneg m)]
      rwa [ht] at h
    have hstep : Real.exp ((m : ℝ) * Real.log ‖z‖)
          * (2 * (m : ℝ) * |Real.log ‖z‖| * Real.exp (2 * (m : ℝ) * |Real.log ‖z‖|))
        ≤ 2 * (m : ℝ) * |Real.log ‖z‖| * Real.exp (3 * (m : ℝ) * |Real.log ‖z‖|) := by
      have hexplt : Real.exp ((m : ℝ) * Real.log ‖z‖)
          ≤ Real.exp ((m : ℝ) * |Real.log ‖z‖|) := by
        refine Real.exp_le_exp.mpr ?_
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        nlinarith [le_abs_self (Real.log ‖z‖)]
      have hstep1 : Real.exp ((m : ℝ) * Real.log ‖z‖)
            * (2 * (m : ℝ) * |Real.log ‖z‖| * Real.exp (2 * (m : ℝ) * |Real.log ‖z‖|))
          = 2 * (m : ℝ) * |Real.log ‖z‖|
            * (Real.exp ((m : ℝ) * Real.log ‖z‖) * Real.exp (2 * (m : ℝ) * |Real.log ‖z‖|)) := by
        ring
      have hstep2 : Real.exp ((m : ℝ) * |Real.log ‖z‖|)
            * Real.exp (2 * (m : ℝ) * |Real.log ‖z‖|)
          = Real.exp (3 * (m : ℝ) * |Real.log ‖z‖|) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hstep1]
      calc 2 * (m : ℝ) * |Real.log ‖z‖|
              * (Real.exp ((m : ℝ) * Real.log ‖z‖) * Real.exp (2 * (m : ℝ) * |Real.log ‖z‖|))
          ≤ 2 * (m : ℝ) * |Real.log ‖z‖|
              * (Real.exp ((m : ℝ) * |Real.log ‖z‖|) * Real.exp (2 * (m : ℝ) * |Real.log ‖z‖|)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexplt (Real.exp_nonneg _))
              (by positivity)
        _ = 2 * (m : ℝ) * |Real.log ‖z‖| * Real.exp (3 * (m : ℝ) * |Real.log ‖z‖|) := by
            rw [hstep2]
    calc ‖z ^ m * (1 - ((((‖z‖ ^ 2)⁻¹ : ℝ)) : ℂ) ^ m)‖
        = ‖z ^ m‖ * ‖(1 : ℂ) - ((((‖z‖ ^ 2)⁻¹ : ℝ)) : ℂ) ^ m‖ := norm_mul _ _
      _ ≤ Real.exp ((m : ℝ) * Real.log ‖z‖)
            * (2 * (m : ℝ) * |Real.log ‖z‖| * Real.exp (2 * (m : ℝ) * |Real.log ‖z‖|)) := by
          rw [hnorm_z]
          exact mul_le_mul_of_nonneg_left hb1 (Real.exp_nonneg _)
      _ ≤ 2 * (m : ℝ) * |Real.log ‖z‖| * Real.exp (3 * (m : ℝ) * |Real.log ‖z‖|) := hstep
      _ ≤ 2 * (m : ℝ) * |Real.log ‖z‖| * Real.exp (6 * (m : ℝ) * δ) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          nlinarith [hlamle, hm0]
      _ = (2 * (m : ℝ) * Real.exp (6 * (m : ℝ) * δ)) * |Real.log ‖z‖| := by ring
  calc ‖(S.map (fun z => z ^ m)).sum - (S.map (fun z => (z⁻¹) ^ m)).sum‖
      = ‖(S.map (fun z => z ^ m * (1 - ((((‖z‖ ^ 2)⁻¹ : ℝ)) : ℂ) ^ m))).sum‖ := by rw [hdiff]
    _ ≤ (S.map (fun z => ‖z ^ m * (1 - ((((‖z‖ ^ 2)⁻¹ : ℝ)) : ℂ) ^ m)‖)).sum :=
        nrm_norm_sum_le _ _
    _ ≤ (S.map (fun z => (2 * (m : ℝ) * Real.exp (6 * (m : ℝ) * δ)) * |Real.log ‖z‖|)).sum :=
        nrm_sum_le_sum _ _ _ hpoint
    _ = (2 * (m : ℝ) * Real.exp (6 * (m : ℝ) * δ))
          * (S.map (fun z => |Real.log ‖z‖|)).sum := Multiset.sum_map_mul_left
    _ ≤ (2 * (m : ℝ) * Real.exp (6 * (m : ℝ) * δ)) * (2 * δ) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 4 * (m : ℝ) * δ * Real.exp (6 * (m : ℝ) * δ) := by ring

/-- **Cassels–Smyth–Breusch, explicit form.** A monic *irreducible* integer polynomial of degree
`n ≥ 2` whose multiset of complex roots is *not* closed under `z ↦ z⁻¹` (equivalently: is not a
reciprocal polynomial, hence also not cyclotomic) has Mahler measure bounded away from `1`,
namely `M(P) > 1 + 1/(52 n log 6n)`.

(Note that irreducibility and `degree > 1` give `P.coeff 0 ≠ 0`, so that `z ↦ z⁻¹` is defined on
every root — cf. `Work.BW.root_ne_zero_of_natDegree_gt_one` — which is why the hypothesis
`hnrec` is the right formulation of "not inversion-closed".  Without it, `P = X ^ 2` would be a
counterexample.)

The proof is the classical elementary argument.  Assuming `M(P) ≤ 1 + δ` with
`δ = 1/(52 n log 6n)`, the Mahler-measure bound forces every root `z` to satisfy
`|log ‖z‖| ≤ 2 δ`, with `∑_z |log ‖z‖| ≤ 2 δ`.  Then
`∑_z z^m - ∑_z z^{-m} = ∑_z z^m (1 - ‖z‖^{-2m})` (using that the multiset of roots is invariant
under complex conjugation) is a rational integer of absolute value at most
`4 m δ exp (6 m δ) < 1` for `1 ≤ m ≤ n`, hence vanishes.  Since the power sums `∑_z z^m`,
`m ≤ n`, determine the multiset of roots, the involution `z ↦ z⁻¹` permutes the roots, which
contradicts `hnrec`. -/
theorem nonreciprocal_measure_gt (P : Polynomial ℤ) (hP : P.Monic) (hirr : Irreducible P)
    (hdeg : 1 < P.natDegree)
    (hnrec : ∀ z ∈ (P.map (Int.castRingHom ℂ)).roots,
      ∀ w ∈ (P.map (Int.castRingHom ℂ)).roots, z * w ≠ 1) :
    1 + 1 / (52 * (P.natDegree : ℝ) * Real.log (6 * (P.natDegree : ℝ)))
      < (P.map (Int.castRingHom ℂ)).mahlerMeasure := by
  obtain ⟨hroot_ne, hprod_roots, -, hcoeff0_ne⟩ := roots_facts P hP hirr hdeg
  set n : ℕ := P.natDegree with hn
  set Q : Polynomial ℂ := P.map (Int.castRingHom ℂ) with hQ
  set δ : ℝ := 1 / (52 * (n : ℝ) * Real.log (6 * (n : ℝ))) with hδ
  have hn2 : 2 ≤ n := hdeg
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  have hQmonic : Q.Monic := by rw [hQ]; exact hP.map _
  have hQne : Q ≠ 0 := hQmonic.ne_zero
  have hndeg : Q.natDegree = n := by
    rw [hQ, hn]
    exact Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℂ)) P
  have hcard : Q.roots.card = n := by
    rw [← hndeg]
    exact (Polynomial.splits_iff_card_roots).mp (IsAlgClosed.splits Q)
  have hroots_ne : Q.roots ≠ 0 := by
    intro h
    have hz : Q.roots.card = 0 := by rw [h]; rfl
    omega
  have hlog12 : (2 : ℝ) ≤ Real.log 12 := by
    rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 12)]
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      simpa using Real.exp_nat_mul 1 2
    rw [h2]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hlog6n : (2 : ℝ) ≤ Real.log (6 * (n : ℝ)) := by
    have h6n : 12 ≤ 6 * (n : ℝ) := by
      have h : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    exact le_trans hlog12 (Real.log_le_log (by norm_num) h6n)
  have hlog2 : (3 : ℝ) / 52 ≤ Real.log 2 := by
    have h : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith
  have hδpos : 0 < δ := by
    rw [hδ]
    positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
    have h : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    linarith
  have hmain : 1 + δ < Q.mahlerMeasure := by
    by_contra hcon
    rw [not_lt] at hcon
    have hmahler : Q.mahlerMeasure = (Q.roots.map (fun z => max 1 ‖z‖)).prod := by
      rw [hQ]
      exact nrm_mahler_map P hP
    have hprod_le : (Q.roots.map (fun z => ‖z‖)).prod ≤ Q.mahlerMeasure := by
      rw [hmahler]
      exact nrm_prod_le_prod Q.roots _ _ (fun z _ => norm_nonneg z)
        (fun z _ => le_max_right 1 ‖z‖)
    have hprod_prod : Q.roots.prod = (-1 : ℂ) ^ n * ((P.coeff 0 : ℤ) : ℂ) := hprod_roots
    have hbound_coeff : ‖(((P.coeff 0 : ℤ)) : ℂ)‖ ≤ 1 + δ := by
      have h1 : ‖(-1 : ℂ) ^ n * ((P.coeff 0 : ℤ) : ℂ)‖ = ‖(((P.coeff 0 : ℤ)) : ℂ)‖ := by
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      rw [← h1]
      calc ‖(-1 : ℂ) ^ n * ((P.coeff 0 : ℤ) : ℂ)‖ = (Q.roots.map (fun z => ‖z‖)).prod := by
            rw [← hprod_prod]
            simpa using nrm_norm_prod Q.roots (fun z => z)
        _ ≤ Q.mahlerMeasure := hprod_le
        _ ≤ 1 + δ := hcon
    have hkZ : (|P.coeff 0| : ℤ) = 1 := by
      have h3 : (1 : ℝ) ≤ ‖(((P.coeff 0 : ℤ)) : ℂ)‖ := by
        rw [Complex.norm_intCast, ← Int.cast_abs]
        have h0 : (0 : ℤ) < |P.coeff 0| := abs_pos.mpr hcoeff0_ne
        have h1 : (1 : ℤ) ≤ |P.coeff 0| := by omega
        exact_mod_cast h1
      have h4 : ‖(((P.coeff 0 : ℤ)) : ℂ)‖ < 2 := by
        have hδlt1 : δ < 1 := by
          have h104 : (104 : ℝ) ≤ 52 * (n : ℝ) * Real.log (6 * (n : ℝ)) := by
            have h1 : (104 : ℝ) ≤ 52 * Real.log (6 * (n : ℝ)) := by linarith [hlog6n]
            calc (104 : ℝ) = 1 * 104 := by ring
              _ ≤ (n : ℝ) * (52 * Real.log (6 * (n : ℝ))) :=
                  mul_le_mul hn1 h1 (by norm_num) (by linarith)
              _ = 52 * (n : ℝ) * Real.log (6 * (n : ℝ)) := by ring
          rw [hδ, div_lt_one (by positivity)]
          linarith
        linarith
      rw [Complex.norm_intCast] at h3 h4
      have h5 : ((|P.coeff 0| : ℤ) : ℝ) < 2 := by
        rw [Int.cast_abs]; exact h4
      have h6 : (1 : ℝ) ≤ ((|P.coeff 0| : ℤ) : ℝ) := by
        rw [Int.cast_abs]; exact h3
      have h7 : (1 : ℤ) ≤ |P.coeff 0| := by exact_mod_cast h6
      have h8 : (|P.coeff 0| : ℤ) < 2 := by exact_mod_cast h5
      omega
    have h0 : P.coeff 0 = 1 ∨ P.coeff 0 = -1 :=
      (abs_eq (by norm_num : (0 : ℤ) ≤ 1)).mp hkZ
    have hnorm_coeff : ‖(((P.coeff 0 : ℤ)) : ℂ)‖ = 1 := by
      rw [Complex.norm_intCast, ← Int.cast_abs, hkZ, Int.cast_one]
    have hprod_norm : (Q.roots.map (fun z => ‖z‖)).prod = 1 := by
      have h1 : ‖Q.roots.prod‖ = (Q.roots.map (fun z => ‖z‖)).prod := by
        simpa using nrm_norm_prod Q.roots (fun z => z)
      rw [hprod_prod, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at h1
      rw [← h1, hnorm_coeff]
    have hlog_zero : (Q.roots.map (fun z => Real.log ‖z‖)).sum = 0 := by
      rw [← nrm_log_prod Q.roots (fun z => ‖z‖) (fun z hz => norm_pos_iff.mpr (hroot_ne z hz)),
        hprod_norm, Real.log_one]
    have hlog_max : (Q.roots.map (fun z => max 0 (Real.log ‖z‖))).sum ≤ δ := by
      have h1 : (Q.roots.map (fun z => max 0 (Real.log ‖z‖))).sum
          = Real.log ((Q.roots.map (fun z => max 1 ‖z‖)).prod) := by
        rw [nrm_log_prod Q.roots (fun z => max 1 ‖z‖)
          (fun z _ => lt_of_lt_of_le one_pos (le_max_left _ _))]
        refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
        intro z hz
        exact (nrm_log_max_one ‖z‖ (norm_pos_iff.mpr (hroot_ne z hz))).symm
      rw [h1, ← hmahler]
      calc Real.log Q.mahlerMeasure ≤ Q.mahlerMeasure - 1 :=
            Real.log_le_sub_one_of_pos (mahlerMeasure_pos_of_ne_zero hQne)
        _ ≤ δ := by linarith
    have hlog_sum : (Q.roots.map (fun z => |Real.log ‖z‖|)).sum ≤ 2 * δ := by
      have h1 : (Q.roots.map (fun z => |Real.log ‖z‖|)).sum
          = (Q.roots.map (fun z => 2 * max 0 (Real.log ‖z‖) - Real.log ‖z‖)).sum := by
        refine congrArg Multiset.sum (Multiset.map_congr rfl ?_)
        intro z _
        by_cases h : 0 ≤ Real.log ‖z‖
        · rw [abs_of_nonneg h, max_eq_right h]; ring
        · have h' : Real.log ‖z‖ < 0 := not_le.mp h
          rw [abs_of_neg h', max_eq_left (le_of_lt h')]; ring
      rw [h1, nrm_sum_sub]
      have h2 : (Q.roots.map (fun z => 2 * max 0 (Real.log ‖z‖))).sum
          = 2 * (Q.roots.map (fun z => max 0 (Real.log ‖z‖))).sum :=
        Multiset.sum_map_mul_left
      rw [h2, hlog_zero]
      linarith
    have hsingle : ∀ z ∈ Q.roots, |Real.log ‖z‖| ≤ 2 * δ := by
      have hnonneg : ∀ x ∈ Q.roots.map (fun z => |Real.log ‖z‖|), 0 ≤ x := by
        intro x hx
        obtain ⟨z', hz', rfl⟩ := Multiset.mem_map.mp hx
        exact abs_nonneg _
      intro z hz
      have hmem : |Real.log ‖z‖| ∈ Q.roots.map (fun z => |Real.log ‖z‖|) :=
        Multiset.mem_map.mpr ⟨z, hz, rfl⟩
      exact le_trans (Multiset.single_le_sum hnonneg _ hmem) hlog_sum
    have hconj : Q.roots.map (starRingEnd ℂ) = Q.roots := by
      rw [hQ]
      exact roots_map_conj_eq P
    have hnum : ∀ m : ℕ, 1 ≤ m → m ≤ n →
        4 * (m : ℝ) * δ * Real.exp (6 * (m : ℝ) * δ) < 1 := by
      intro m hm1 hmn
      have hmle : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
      have hA : (104 : ℝ) * (n : ℝ) ≤ 52 * (n : ℝ) * Real.log (6 * (n : ℝ)) := by
        have h1 : (104 : ℝ) ≤ 52 * Real.log (6 * (n : ℝ)) := by linarith [hlog6n]
        calc (104 : ℝ) * (n : ℝ) = (n : ℝ) * 104 := by ring
          _ ≤ (n : ℝ) * (52 * Real.log (6 * (n : ℝ))) :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
          _ = 52 * (n : ℝ) * Real.log (6 * (n : ℝ)) := by ring
      have hδle : δ ≤ 1 / (104 * (n : ℝ)) := by
        rw [hδ, one_div_le_one_div (by positivity) (by positivity)]
        exact hA
      have hmδ : (m : ℝ) * δ ≤ 1 / 104 := by
        have hmul : (m : ℝ) * δ ≤ (n : ℝ) * (1 / (104 * (n : ℝ))) :=
          mul_le_mul hmle hδle (le_of_lt hδpos) (by positivity)
        have hnf : (n : ℝ) * (1 / (104 * (n : ℝ))) = 1 / 104 := by field_simp
        linarith [hmul, hnf]
      have hexp : Real.exp (6 * (m : ℝ) * δ) ≤ 2 := by
        have h6 : 6 * (m : ℝ) * δ ≤ Real.log 2 := by
          have h61 : 6 * (m : ℝ) * δ ≤ 6 * (1 / 104) := by linarith
          linarith [h61, hlog2]
        calc Real.exp (6 * (m : ℝ) * δ) ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr h6
          _ = 2 := Real.exp_log (by norm_num)
      have h4 : 4 * (m : ℝ) * δ ≤ 1 / 26 := by linarith
      calc 4 * (m : ℝ) * δ * Real.exp (6 * (m : ℝ) * δ) ≤ (1 / 26) * 2 :=
            mul_le_mul h4 hexp (Real.exp_nonneg _) (by norm_num)
        _ = 1 / 13 := by norm_num
        _ < 1 := by norm_num
    have hpq : ∀ m : ℕ, 1 ≤ m → m ≤ Q.roots.card →
        (Q.roots.map (fun z => z ^ m)).sum = (Q.roots.map (fun z => (z⁻¹) ^ m)).sum := by
      intro m hm1 hmc
      have hmn : m ≤ n := by rw [← hcard]; exact hmc
      obtain ⟨c1, hc1⟩ := pow_sum_roots_int P hP m
      obtain ⟨c2, hc2⟩ := inv_pow_sum_roots_int P hP h0 m
      rw [← hQ] at hc1 hc2
      have hb := nrm_pow_sum_sub_inv_bound Q.roots δ m (fun z hz => hroot_ne z hz) hconj hlog_sum
      have hlt := hnum m hm1 hmn
      have hceq : (c1 : ℂ) = (c2 : ℂ) := by
        by_contra hne
        have hneZ : c1 ≠ c2 := fun h => hne (by rw [h])
        have heq : (Q.roots.map (fun z => z ^ m)).sum - (Q.roots.map (fun z => (z⁻¹) ^ m)).sum
            = (c1 : ℂ) - (c2 : ℂ) := by rw [hc1, hc2]
        have hge1 : (1 : ℝ) ≤ ‖(c1 : ℂ) - (c2 : ℂ)‖ := by
          have hsub : (c1 : ℂ) - (c2 : ℂ) = ((c1 - c2 : ℤ) : ℂ) := (Int.cast_sub c1 c2).symm
          rw [hsub, Complex.norm_intCast, ← Int.cast_abs]
          have h0' : (0 : ℤ) < |c1 - c2| := abs_pos.mpr (sub_ne_zero.mpr hneZ)
          have h1' : (1 : ℤ) ≤ |c1 - c2| := by omega
          exact_mod_cast h1'
        rw [heq] at hb
        linarith
      rw [hc1, hc2, hceq]
    have hS : Q.roots = Q.roots.map (fun z => z⁻¹) := by
      refine multiset_eq_of_powSum_eq (by simp) ?_
      intro m hm1 hmc
      rw [Multiset.map_map]
      simp only [Function.comp_apply]
      exact hpq m hm1 hmc
    obtain ⟨z, hz⟩ := Multiset.exists_mem_of_ne_zero hroots_ne
    have hzn : z ≠ 0 := hroot_ne z hz
    have hzmem : z⁻¹ ∈ Q.roots := by
      have h : z⁻¹ ∈ Q.roots.map (fun z => z⁻¹) := Multiset.mem_map_of_mem _ hz
      rwa [← hS] at h
    exact hnrec z hz z⁻¹ hzmem (mul_inv_cancel₀ hzn)
  rw [hδ, hn, hQ] at hmain
  exact hmain

end Work.BW
