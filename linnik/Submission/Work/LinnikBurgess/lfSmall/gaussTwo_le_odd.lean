import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.gaussTwoLocal_defs
import Submission.Work.LinnikBurgess.peel_gauss
import Submission.Work.LinnikBurgess.vcap_two_gamma
import Submission.Work.LinnikBurgess.dvd_natCast_val_iff
import Submission.Work.LinnikBurgess.lfSmall.gaussQuad_odd

/-!
# Lemma A (U2) for odd `p`: the two-term stationary phase

`Work.LinnikBurgess.lfSmall.gaussTwo_le_odd` bounds the cubic character correlation at a prime
power `p^e` (`p` an odd prime) by `p^(e/2) · gaussTwoRHS p e m a b`, for every `m` with
`e ≤ 3m` and `2m ≤ e`.

The proof: split `x = y + p^m·w` (`zmod_sum_range`/digit decomposition); for `y` that is not a unit
at `p` every summand vanishes; for a unit `y` the `w`-dependence peels off (`peel_gauss`) into the
constant `χ(∏(y+a_l))·conj χ(∏(y+b_l))` times a quadratic Gauss sum
`gaussQuad p (e-m) θ α γ` with `α = defect1 p e a b y`, `γ = -(1/2)p^m·defect2 p e a b y`, which is
of size `p^((e-m+g)/2)` with `g = m + vcap p (e-2m) (defect2 p e a b y).val` and vanishes unless
`p^g ∣ defect1 p e a b y` (`gaussQuad_bound_odd`); that is exactly the weight of `gaussTwoRHS`.
-/

open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.LinnikBurgess.lfSmall

/-- `vcap p K x ≤ K` (local copy, to avoid depending on another module's naming). -/
private lemma vcap_le_odd (p K x : ℕ) : vcap p K x ≤ K := by
  unfold vcap
  split
  · exact le_rfl
  · exact Nat.min_le_right _ _

/-- The standard reindexing of a sum over `ZMod N` as a sum over `Finset.range N`. -/
private lemma zmod_sum_range_aux (N : ℕ) [NeZero N] (g : ZMod N → ℂ) :
    (∑ x : ZMod N, g x) = ∑ i ∈ Finset.range N, g ((i : ℕ) : ZMod N) := by
  refine Finset.sum_bij (fun (x : ZMod N) _ => x.val) ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_range.mpr (ZMod.val_lt a)
  · intro a _ b _ h; exact ZMod.val_injective N h
  · intro b hb
    refine ⟨((b : ℕ) : ZMod N), Finset.mem_univ _, ?_⟩
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hb)]
  · intro a _
    rw [ZMod.natCast_zmod_val]

/-- Reindexing `x = y + p^m·w`: the correlation sum over `ZMod (p^e)` splits into the low digit
`y < p^m` and the high digits `w : ZMod (p^(e-m))`. -/
private theorem sum_reindex_odd_self {p e m : ℕ} [Fact p.Prime] (hm : 1 ≤ m) (h2 : 2 * m ≤ e)
    (F : ZMod (p ^ e) → ℂ) :
    (∑ x : ZMod (p ^ e), F x)
      = ∑ y ∈ Finset.range (p ^ m), ∑ w : ZMod (p ^ (e - m)),
          F (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e))
              * ((w.val : ℕ) : ZMod (p ^ e))) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : NeZero (p ^ e) := ⟨pow_ne_zero e hp0⟩
  haveI : NeZero (p ^ m) := ⟨pow_ne_zero m hp0⟩
  haveI : NeZero (p ^ (e - m)) := ⟨pow_ne_zero (e - m) hp0⟩
  have hsum : m + (e - m) = e := by omega
  rw [zmod_sum_range_aux (p ^ e) F]
  have hrange : Finset.range (p ^ e) = Finset.range (p ^ m * p ^ (e - m)) := by
    congr 1
    rw [← pow_add, hsum]
  rw [hrange]
  rw [Commons.Algebra.BigOperators.sum_range_mul_eq (fun i => F ((i : ℕ) : ZMod (p ^ e)))
    (p ^ m) (p ^ (e - m))]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  rw [zmod_sum_range_aux (p ^ (e - m)) (fun w : ZMod (p ^ (e - m)) =>
    F (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e))))]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp ht)]
  congr 1
  push_cast
  ring

/-- Off the unit locus the summand of the correlation vanishes: a factor divisible by `p` makes the
whole product a non-unit, and `χ` of a non-unit is `0`. -/
private theorem odd_innerSum_vanishing_self {p e m : ℕ} [Fact p.Prime] (hm : 1 ≤ m)
    (h2 : 2 * m ≤ e) (χ : DirichletCharacter ℂ (p ^ e)) (a b : Fin 3 → ℕ) (y : ℕ)
    (hy : ¬ UnitAt p y a b) (w : ZMod (p ^ (e - m))) :
    χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e))
          + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e)) + (a l : ZMod (p ^ e))))
      * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e))
          + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e))
          + (b l : ZMod (p ^ e))))) = 0 := by
  classical
  have he : 0 < e := by omega
  have hwit : ∃ l : Fin 3, p ∣ y + a l ∨ p ∣ y + b l := by
    by_contra hc
    push_neg at hc
    exact hy hc
  rcases hwit with ⟨l, hl | hl⟩
  · have hdvd : p ∣ y + p ^ m * w.val + a l := by
      have h := dvd_add hl (dvd_mul_of_dvd_left (dvd_pow_self p (by omega : m ≠ 0)) w.val)
      rwa [add_right_comm] at h
    have hfac : ¬ IsUnit (((y + p ^ m * w.val + a l : ℕ)) : ZMod (p ^ e)) := by
      rw [ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) he]
      exact fun hh => hh hdvd
    have hprod : ¬ IsUnit (∏ l' : Fin 3, (((y + p ^ m * w.val + a l' : ℕ)) : ZMod (p ^ e))) := by
      intro hcon
      have hsplit := Finset.prod_erase_mul (Finset.univ : Finset (Fin 3))
        (fun l' : Fin 3 => (((y + p ^ m * w.val + a l' : ℕ)) : ZMod (p ^ e)))
        (Finset.mem_univ l)
      rw [← hsplit] at hcon
      exact hfac (IsUnit.mul_iff.mp hcon).2
    rw [show (∏ l' : Fin 3, (((y : ℕ) : ZMod (p ^ e))
            + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e))
            + (a l' : ZMod (p ^ e))))
          = ∏ l' : Fin 3, (((y + p ^ m * w.val + a l' : ℕ)) : ZMod (p ^ e)) from
        Finset.prod_congr rfl (fun l' _ => by push_cast; ring),
      MulChar.map_nonunit χ hprod, zero_mul]
  · have hdvd : p ∣ y + p ^ m * w.val + b l := by
      have h := dvd_add hl (dvd_mul_of_dvd_left (dvd_pow_self p (by omega : m ≠ 0)) w.val)
      rwa [add_right_comm] at h
    have hfac : ¬ IsUnit (((y + p ^ m * w.val + b l : ℕ)) : ZMod (p ^ e)) := by
      rw [ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) he]
      exact fun hh => hh hdvd
    have hprod : ¬ IsUnit (∏ l' : Fin 3, (((y + p ^ m * w.val + b l' : ℕ)) : ZMod (p ^ e))) := by
      intro hcon
      have hsplit := Finset.prod_erase_mul (Finset.univ : Finset (Fin 3))
        (fun l' : Fin 3 => (((y + p ^ m * w.val + b l' : ℕ)) : ZMod (p ^ e)))
        (Finset.mem_univ l)
      rw [← hsplit] at hcon
      exact hfac (IsUnit.mul_iff.mp hcon).2
    rw [show (∏ l' : Fin 3, (((y : ℕ) : ZMod (p ^ e))
            + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e))
            + (b l' : ZMod (p ^ e))))
          = ∏ l' : Fin 3, (((y + p ^ m * w.val + b l' : ℕ)) : ZMod (p ^ e)) from
        Finset.prod_congr rfl (fun l' _ => by push_cast; ring),
      MulChar.map_nonunit χ hprod, map_zero, mul_zero]

/-- The per-`y` bound, positive case: on a unit `y` satisfying the criticality condition the inner
sum is bounded by `p^(e/2) · p^(b_y/2)`, `b_y = vcap p (e-2m) (defect2 p e a b y).val`. -/
private theorem inner_bound_odd_pos {p e m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h3 : e ≤ 3 * m) (h2 : 2 * m ≤ e) (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (a b : Fin 3 → ℕ) (y : ℕ) (hU : UnitAt p y a b)
    (hdiv : p ^ (m + vcap p (e - 2 * m) (defect2 p e a b y).val) ∣ (defect1 p e a b y).val) :
    ‖∑ w : ZMod (p ^ (e - m)),
      χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e))
          + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e)) + (a l : ZMod (p ^ e))))
      * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e))
          + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e))
          + (b l : ZMod (p ^ e)))))‖
      ≤ (p : ℝ) ^ ((e : ℝ) / 2)
          * (p : ℝ) ^ ((vcap p (e - 2 * m) (defect2 p e a b y).val : ℝ) / 2) := by
  classical
  have hme : m ≤ e := by omega
  have hK1 : 1 ≤ e - m := by omega
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hvb : vcap p (e - 2 * m) (defect2 p e a b y).val ≤ e - 2 * m := vcap_le_odd p (e - 2 * m) _
  set α : ZMod (p ^ (e - m)) := (((defect1 p e a b y).val : ℕ) : ZMod (p ^ (e - m))) with hαdef
  set γ : ZMod (p ^ (e - m)) :=
    -((2 : ZMod (p ^ (e - m)))⁻¹) * ((p ^ m : ℕ) : ZMod (p ^ (e - m)))
      * (((defect2 p e a b y).val : ℕ) : ZMod (p ^ (e - m))) with hγdef
  set θ : ℂ := psiFun p e m χ 1 with hθdef
  have hprim : IsPrimitiveRoot θ (p ^ (e - m)) := by
    rw [hθdef]
    exact psiFun_one_isPrimitiveRoot hp2 hm h3 h2 χ hχ
  have hpeel := peel_gauss (p := p) (e := e) (m := m) hp2 hm h3 h2 χ a b y hU
  have hgq := gaussQuad_bound_odd (p := p) (K := e - m) hp2 hK1 hprim α γ
  have hvc := vcap_two_gamma (p := p) (e := e) (m := m) hp2 hm h2
    (defect2 p e a b y).val (ZMod.val_lt _)
  have hvc' : vcap p (e - m) (2 * γ).val = m + vcap p (e - 2 * m) (defect2 p e a b y).val := by
    rw [hγdef]; exact hvc
  have hcond : p ^ (vcap p (e - m) (2 * γ).val) ∣ α.val := by
    rw [hvc', hαdef]
    exact (dvd_natCast_val_iff (p := p) (K := e - m)
      (g := m + vcap p (e - 2 * m) (defect2 p e a b y).val)
      (d := (defect1 p e a b y).val) (by omega)).mpr hdiv
  have harith : (p : ℝ) ^ ((((e - m : ℕ) : ℝ)
        + ((vcap p (e - m) (2 * γ).val : ℕ) : ℝ)) / 2)
      = (p : ℝ) ^ ((e : ℝ) / 2)
        * (p : ℝ) ^ ((vcap p (e - 2 * m) (defect2 p e a b y).val : ℝ) / 2) := by
    have hexp : ((((e - m : ℕ) : ℝ) + ((vcap p (e - m) (2 * γ).val : ℕ) : ℝ)) / 2)
        = (e : ℝ) / 2 + ((vcap p (e - 2 * m) (defect2 p e a b y).val : ℕ) : ℝ) / 2 := by
      rw [hvc']
      simp only [Nat.cast_sub hme, Nat.cast_add]
      ring
    rw [hexp, Real.rpow_add hp_pos]
  have hC : ‖χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + (a l : ZMod (p ^ e))))
      * (starRingEnd ℂ) (χ (∏ l : Fin 3,
          (((y : ℕ) : ZMod (p ^ e)) + (b l : ZMod (p ^ e)))))‖ ≤ 1 := by
    have h1 := DirichletCharacter.norm_le_one χ
      (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + (a l : ZMod (p ^ e))))
    have h2' := DirichletCharacter.norm_le_one χ
      (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + (b l : ZMod (p ^ e))))
    have h1' := norm_nonneg (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + (a l : ZMod (p ^ e)))))
    have h2'' := norm_nonneg (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + (b l : ZMod (p ^ e)))))
    rw [starRingEnd_apply, norm_mul, norm_star]
    nlinarith [h1, h2', h1', h2'']
  rw [hpeel, norm_mul, ← hθdef, ← hαdef, ← hγdef]
  refine (mul_le_mul hC hgq (norm_nonneg _) (by norm_num)).trans (le_of_eq ?_)
  rw [one_mul, if_pos hcond, harith]

/-- The per-`y` bound, vanishing case: if some shift of `y` is not a unit at `p`, or the
criticality condition fails, the inner sum is `0`. -/
private theorem inner_bound_odd_zero {p e m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h3 : e ≤ 3 * m) (h2 : 2 * m ≤ e) (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (a b : Fin 3 → ℕ) (y : ℕ)
    (h : ¬ (UnitAt p y a b
        ∧ p ^ (m + vcap p (e - 2 * m) (defect2 p e a b y).val) ∣ (defect1 p e a b y).val)) :
    (∑ w : ZMod (p ^ (e - m)),
      χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e))
          + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e)) + (a l : ZMod (p ^ e))))
      * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e))
          + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e))
          + (b l : ZMod (p ^ e)))))) = 0 := by
  classical
  have hK1 : 1 ≤ e - m := by omega
  by_cases hU : UnitAt p y a b
  · have hdiv : ¬ (p ^ (m + vcap p (e - 2 * m) (defect2 p e a b y).val)
        ∣ (defect1 p e a b y).val) := fun hh => h ⟨hU, hh⟩
    have hvb : vcap p (e - 2 * m) (defect2 p e a b y).val ≤ e - 2 * m := vcap_le_odd p (e - 2 * m) _
    set α : ZMod (p ^ (e - m)) := (((defect1 p e a b y).val : ℕ) : ZMod (p ^ (e - m))) with hαdef
    set γ : ZMod (p ^ (e - m)) :=
      -((2 : ZMod (p ^ (e - m)))⁻¹) * ((p ^ m : ℕ) : ZMod (p ^ (e - m)))
        * (((defect2 p e a b y).val : ℕ) : ZMod (p ^ (e - m))) with hγdef
    set θ : ℂ := psiFun p e m χ 1 with hθdef
    have hprim : IsPrimitiveRoot θ (p ^ (e - m)) := by
      rw [hθdef]
      exact psiFun_one_isPrimitiveRoot hp2 hm h3 h2 χ hχ
    have hpeel := peel_gauss (p := p) (e := e) (m := m) hp2 hm h3 h2 χ a b y hU
    have hgq := gaussQuad_bound_odd (p := p) (K := e - m) hp2 hK1 hprim α γ
    have hvc := vcap_two_gamma (p := p) (e := e) (m := m) hp2 hm h2
      (defect2 p e a b y).val (ZMod.val_lt _)
    have hvc' : vcap p (e - m) (2 * γ).val = m + vcap p (e - 2 * m) (defect2 p e a b y).val := by
      rw [hγdef]; exact hvc
    have hcond' : ¬ (p ^ (vcap p (e - m) (2 * γ).val) ∣ α.val) := by
      intro hh
      rw [hvc', hαdef] at hh
      exact hdiv ((dvd_natCast_val_iff (p := p) (K := e - m)
        (g := m + vcap p (e - 2 * m) (defect2 p e a b y).val)
        (d := (defect1 p e a b y).val) (by omega)).mp hh)
    have hG : ‖gaussQuad p (e - m) θ α γ‖ = 0 := by
      refine le_antisymm (hgq.trans (le_of_eq ?_)) (norm_nonneg _)
      rw [if_neg hcond']
    have hG0 : gaussQuad p (e - m) θ α γ = 0 := norm_eq_zero.mp hG
    rw [hpeel, ← hθdef, ← hαdef, ← hγdef, hG0, mul_zero]
  · refine Finset.sum_eq_zero (fun w _ => ?_)
    exact odd_innerSum_vanishing_self hm h2 χ a b y hU w

theorem gaussTwo_le_odd {p e m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h3 : e ≤ 3 * m) (h2 : 2 * m ≤ e) (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (a b : Fin 3 → ℕ) :
    ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
      ≤ (p : ℝ) ^ ((e : ℝ) / 2) * gaussTwoRHS p e m a b := by
  classical
  have hre := sum_reindex_odd_self (p := p) (e := e) (m := m) hm h2
    (fun x : ZMod (p ^ e) => χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e))))))
  rw [hre]
  calc ‖∑ y ∈ Finset.range (p ^ m), ∑ w : ZMod (p ^ (e - m)),
        χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e))
            + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e)) + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e))
            + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e))
            + (b l : ZMod (p ^ e)))))‖
      ≤ ∑ y ∈ Finset.range (p ^ m), ‖∑ w : ZMod (p ^ (e - m)),
          χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e))
              + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e))
              + (a l : ZMod (p ^ e))))
          * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e))
              + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e))
              + (b l : ZMod (p ^ e)))))‖ := norm_sum_le _ _
    _ ≤ ∑ y ∈ Finset.range (p ^ m),
          ((p : ℝ) ^ ((e : ℝ) / 2)
            * (if UnitAt p y a b
                  ∧ p ^ (m + vcap p (e - 2 * m) (defect2 p e a b y).val)
                      ∣ (defect1 p e a b y).val
               then (p : ℝ) ^ ((vcap p (e - 2 * m) (defect2 p e a b y).val : ℝ) / 2)
               else 0)) := by
        refine Finset.sum_le_sum (fun y hy => ?_)
        by_cases hc : UnitAt p y a b
            ∧ p ^ (m + vcap p (e - 2 * m) (defect2 p e a b y).val) ∣ (defect1 p e a b y).val
        · rw [if_pos hc]
          exact inner_bound_odd_pos hp2 hm h3 h2 χ hχ a b y hc.1 hc.2
        · rw [if_neg hc, inner_bound_odd_zero hp2 hm h3 h2 χ hχ a b y hc, norm_zero, mul_zero]
    _ = (p : ℝ) ^ ((e : ℝ) / 2) * gaussTwoRHS p e m a b := by
        rw [gaussTwoRHS, Finset.mul_sum]

end Work.LinnikBurgess.lfSmall
