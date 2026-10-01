import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs
import Submission.Work.LinnikBurgess.peel_gauss_bound
import Submission.Work.LinnikBurgess.corr6_primePow_gaussTwo_le

/-!
# Lemma A (odd `p`), on a `sorryAx`-free basis

This file proves `Work.LinnikBurgess.corr6_primePow_gaussTwo_bound`: the summation step that turns
the per-lift bound `peel_gauss_bound` into a bound of the complete cubic correlation over
`ZMod (p^e)` by `p^(e/2) · gaussTwoRHS p e m a b`.

It has the same statement as `Work.LinnikBurgess.corr6_primePow_gaussTwo_le` (a drop-in for its
callers), but it is built on `peel_gauss_bound`, whose Gauss-sum input is
`Work.LinnikBurgess.gaussQuad_mul_conj` / `gaussQuad_norm_bound` (proved in
`Submission/Work/LinnikBurgess/peel_gauss_bound.lean`), so it does *not* depend on the `sorry` in
`Submission/Work/LinnikBurgess/gaussQuad_mul_star.lean`; `#print axioms` confirms this.

From the imported module only two `sorryAx`-free bookkeeping lemmas are used:
`zmod_sum_range_aux` (reindexing a `ZMod`-sum as a range sum) and `vanish_nonunit` (the summand
vanishes at non-units).
-/

open Classical

open scoped BigOperators

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.LinnikBurgess

/-- The cubic correlation summand at `x : ZMod (p^e)`. -/
noncomputable def peelCorrG (p e : ℕ) (χ : DirichletCharacter ℂ (p ^ e)) (a b : Fin 3 → ℕ)
    (x : ZMod (p ^ e)) : ℂ :=
  χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
    * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))

/-- **Lemma A for odd `p`, summation step.**  Let `p` be an odd prime, `m ≥ 1` with `e ≤ 3m` and
`2m ≤ e`, and `χ` a primitive character mod `p^e`.  Then the complete cubic correlation is bounded
by `p^(e/2)` times `gaussTwoRHS p e m a b`, the sum over the low digit `y < p^m` of the Gauss-sum
weight `p^(b_y/2)`, present exactly when `y` is a unit at `p` and `p^(m+b_y) ∣ defect1(y)`, where
`b_y = vcap p (e-2m) (defect2(y))`. -/
theorem corr6_primePow_gaussTwo_bound {p e m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hm : 1 ≤ m)
    (h3 : e ≤ 3 * m) (h2 : 2 * m ≤ e) (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (a b : Fin 3 → ℕ) :
    ‖∑ x : ZMod (p ^ e), χ (∏ l : Fin 3, (x + (a l : ZMod (p ^ e))))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (x + (b l : ZMod (p ^ e)))))‖
      ≤ (p : ℝ) ^ ((e : ℝ) / 2) * gaussTwoRHS p e m a b := by
  have hp : p.Prime := Fact.out
  have hppos : 0 < p := hp.pos
  have hmle : m ≤ e := by omega
  have hKme : p ^ e = p ^ m * p ^ (e - m) := by rw [← pow_add, Nat.add_sub_of_le hmle]
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
  set bnd : ℕ → ℝ := fun y =>
      (if UnitAt p y a b
            ∧ p ^ (m + vcap p (e - 2 * m) (defect2 p e a b y).val) ∣ (defect1 p e a b y).val
        then (p : ℝ) ^ (((vcap p (e - 2 * m) (defect2 p e a b y).val : ℕ) : ℝ) / 2) else 0)
    with hbnddef
  -- ### Step 1: reindex `ZMod (p^e)` by the two digits `y < p^m`, `w mod p^(e-m)`
  have hrange : (∑ x : ZMod (p ^ e), peelCorrG p e χ a b x)
      = ∑ j ∈ Finset.range (p ^ e), peelCorrG p e χ a b (((j : ℕ) : ZMod (p ^ e))) :=
    zmod_sum_range_aux (p ^ e) (peelCorrG p e χ a b)
  have hbij1 : (∑ j ∈ Finset.range (p ^ e), peelCorrG p e χ a b (((j : ℕ) : ZMod (p ^ e))))
      = ∑ yw ∈ Finset.range (p ^ m) ×ˢ Finset.range (p ^ (e - m)),
          peelCorrG p e χ a b (((yw.1 + p ^ m * yw.2 : ℕ) : ZMod (p ^ e))) := by
    refine Finset.sum_bij (fun j _ => (j % p ^ m, j / p ^ m)) ?_ ?_ ?_ ?_
    · intro j hj
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range]
      refine ⟨Nat.mod_lt _ (pow_pos hppos m), ?_⟩
      rw [Nat.div_lt_iff_lt_mul (pow_pos hppos m)]
      calc j < p ^ e := Finset.mem_range.mp hj
        _ = p ^ m * p ^ (e - m) := hKme
        _ = p ^ (e - m) * p ^ m := by ring
    · intro j1 _ j2 _ heq
      rw [Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      calc j1 = p ^ m * (j1 / p ^ m) + j1 % p ^ m := (Nat.div_add_mod j1 (p ^ m)).symm
        _ = p ^ m * (j2 / p ^ m) + j2 % p ^ m := by rw [h1, h2]
        _ = j2 := Nat.div_add_mod j2 (p ^ m)
    · intro yw hyw
      rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hyw
      obtain ⟨hy, hw⟩ := hyw
      refine ⟨yw.1 + p ^ m * yw.2, ?_, ?_⟩
      · rw [Finset.mem_range]
        calc yw.1 + p ^ m * yw.2 < p ^ m + p ^ m * yw.2 := by omega
          _ = p ^ m * (yw.2 + 1) := by ring
          _ ≤ p ^ m * p ^ (e - m) := Nat.mul_le_mul_left _ (by omega)
          _ = p ^ e := hKme.symm
      · rw [Prod.mk.injEq]
        exact ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hy],
          by rw [Nat.add_mul_div_left _ _ (pow_pos hppos m), Nat.div_eq_of_lt hy,
                Nat.zero_add]⟩
    · intro j _
      congr 1
      have hjj : j % p ^ m + p ^ m * (j / p ^ m) = j := by
        rw [Nat.add_comm, Nat.div_add_mod]
      rw [hjj]
  have hbij2 : (∑ yw ∈ Finset.range (p ^ m) ×ˢ Finset.range (p ^ (e - m)),
          peelCorrG p e χ a b (((yw.1 + p ^ m * yw.2 : ℕ) : ZMod (p ^ e))))
      = ∑ y ∈ Finset.range (p ^ m), ∑ w ∈ Finset.range (p ^ (e - m)),
          peelCorrG p e χ a b (((y + p ^ m * w : ℕ) : ZMod (p ^ e))) :=
    Finset.sum_product _ _ _
  have hbij := hbij1.trans hbij2
  -- ### Step 2: the per-`y` bound
  have hbnd : ∀ y ∈ Finset.range (p ^ m),
      ‖∑ w ∈ Finset.range (p ^ (e - m)),
          peelCorrG p e χ a b (((y + p ^ m * w : ℕ) : ZMod (p ^ e)))‖
        ≤ (p : ℝ) ^ ((e : ℝ) / 2) * bnd y := by
    intro y hy
    by_cases hunit : UnitAt p y a b
    · have hconv : (∑ w : ZMod (p ^ (e - m)),
            peelCorrG p e χ a b (((y + p ^ m * w.val : ℕ) : ZMod (p ^ e))))
          = ∑ w ∈ Finset.range (p ^ (e - m)),
            peelCorrG p e χ a b (((y + p ^ m * w : ℕ) : ZMod (p ^ e))) := by
        rw [zmod_sum_range_aux (p ^ (e - m))
          (fun w : ZMod (p ^ (e - m)) =>
            peelCorrG p e χ a b (((y + p ^ m * w.val : ℕ) : ZMod (p ^ e))))]
        refine Finset.sum_congr rfl (fun w hw => ?_)
        congr 1
        rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hw)]
      have hsummand : ∀ w : ZMod (p ^ (e - m)),
          peelCorrG p e χ a b (((y + p ^ m * w.val : ℕ) : ZMod (p ^ e)))
            = χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e))
                  * ((w.val : ℕ) : ZMod (p ^ e)) + ((a l : ℕ) : ZMod (p ^ e))))
              * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e))
                  + ((p ^ m : ℕ) : ZMod (p ^ e)) * ((w.val : ℕ) : ZMod (p ^ e))
                  + ((b l : ℕ) : ZMod (p ^ e))))) := by
        intro w
        have ha : (∏ l : Fin 3, ((((y + p ^ m * w.val : ℕ) : ZMod (p ^ e))
              + (a l : ZMod (p ^ e)))))
            = ∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e))
                * ((w.val : ℕ) : ZMod (p ^ e)) + ((a l : ℕ) : ZMod (p ^ e))) := by
          refine Finset.prod_congr rfl (fun l _ => ?_)
          push_cast
          ring
        have hb : (∏ l : Fin 3, ((((y + p ^ m * w.val : ℕ) : ZMod (p ^ e))
              + (b l : ZMod (p ^ e)))))
            = ∏ l : Fin 3, (((y : ℕ) : ZMod (p ^ e)) + ((p ^ m : ℕ) : ZMod (p ^ e))
                * ((w.val : ℕ) : ZMod (p ^ e)) + ((b l : ℕ) : ZMod (p ^ e))) := by
          refine Finset.prod_congr rfl (fun l _ => ?_)
          push_cast
          ring
        simp only [peelCorrG]
        rw [ha, hb]
      have hbndy : bnd y = (if p ^ (m + vcap p (e - 2 * m) (defect2 p e a b y).val)
            ∣ (defect1 p e a b y).val
          then (p : ℝ) ^ (((vcap p (e - 2 * m) (defect2 p e a b y).val : ℕ) : ℝ) / 2)
          else 0) := by
        rw [hbnddef]
        simp only [hunit, true_and]
      rw [hbndy, hconv.symm, Finset.sum_congr rfl (fun w _ => hsummand w)]
      exact peel_gauss_bound (p := p) (e := e) (m := m) hp2 hm h3 h2 χ hχ a b y hunit
    · have hzero : (∑ w ∈ Finset.range (p ^ (e - m)),
            peelCorrG p e χ a b (((y + p ^ m * w : ℕ) : ZMod (p ^ e)))) = 0 := by
        refine Finset.sum_eq_zero (fun w _ => ?_)
        exact vanish_nonunit hm h2 χ a b y hunit w
      have hbnd0 : bnd y = 0 := by
        rw [hbnddef]
        simp only [hunit, false_and, if_false]
      rw [hzero, norm_zero, hbnd0, mul_zero]
  -- ### Step 3: sum over the low digit
  have hfin : ‖∑ y ∈ Finset.range (p ^ m), ∑ w ∈ Finset.range (p ^ (e - m)),
        peelCorrG p e χ a b (((y + p ^ m * w : ℕ) : ZMod (p ^ e)))‖
      ≤ (p : ℝ) ^ ((e : ℝ) / 2) * gaussTwoRHS p e m a b := by
    calc ‖∑ y ∈ Finset.range (p ^ m), ∑ w ∈ Finset.range (p ^ (e - m)),
            peelCorrG p e χ a b (((y + p ^ m * w : ℕ) : ZMod (p ^ e)))‖
        ≤ ∑ y ∈ Finset.range (p ^ m), ‖∑ w ∈ Finset.range (p ^ (e - m)),
            peelCorrG p e χ a b (((y + p ^ m * w : ℕ) : ZMod (p ^ e)))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ y ∈ Finset.range (p ^ m), (p : ℝ) ^ ((e : ℝ) / 2) * bnd y :=
          Finset.sum_le_sum hbnd
      _ = (p : ℝ) ^ ((e : ℝ) / 2) * ∑ y ∈ Finset.range (p ^ m), bnd y := by
          rw [Finset.mul_sum]
      _ = (p : ℝ) ^ ((e : ℝ) / 2) * gaussTwoRHS p e m a b := by
          congr 1
  change ‖∑ x : ZMod (p ^ e), peelCorrG p e χ a b x‖
      ≤ (p : ℝ) ^ ((e : ℝ) / 2) * gaussTwoRHS p e m a b
  rw [hrange, hbij]
  exact hfin

end Work.LinnikBurgess
