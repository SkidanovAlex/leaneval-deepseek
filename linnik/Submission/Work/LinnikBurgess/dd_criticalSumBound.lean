import Mathlib
import Submission.Work.LinnikBurgess.singleton_defs
import Submission.Work.LinnikBurgess.api
import Submission.Commons.NumberTheory.DirichletCharacter.charCorrelation6_levelSum_nondegenerate
import Submission.Commons.NumberTheory.GaussSum.quadratic_phase_prime_pow
import Submission.Work.LinnikBurgess.ddDefs
import Submission.Work.LinnikBurgess.dd_cubicUnit
import Submission.Work.LinnikBurgess.cubic_phase_prime_pow
import Submission.Work.LinnikBurgess.dd_levelSum_eq_cubicSum

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.LinnikBurgess

open scoped BigOperators
open Polynomial

/-!
# The critical (doubly degenerate) level-sum bound

We prove that the level sum at a *doubly degenerate* critical class `r` of a primitive character
`χ` modulo `p ^ e` (`e ≥ 4`, `p ≠ 2`) is at most `8 p ^ (2e/3 - 1)`, under the extra hypothesis
that the pair `(a,b)` carries a *cubic* doubly degenerate class somewhere.

## Structure of the proof

* `target_sum_eq3` (commons) rewrites the target sum as
  `(∏_l χ (r + a_l)) * (∏_l conj (χ (r + b_l))) * levelSum3 p e 1 (e-2) χ A C`
  with `A l = gammaU p e r (a l) = ((r+a_l)⁻¹)` and `C l = gammaU p e r (b l)`; the constant factor
  has modulus `1`.  Hence it suffices to bound `levelSum3 p e 1 (e-2) χ A C`.

* `IsDD p e a b r` translates, for `A`, `C`, into
  (D1) `p^2 ∣ (∑ A - ∑ C).val`,
  (D2) `p ∣ (∑ A^2 - ∑ C^2).val`,
  and `hcub` (together with `hdd`) yields
  (D3) `¬ p ∣ (∑ A^3 - ∑ C^3).val`     -- this is `dd_cubicUnit`;
  `hcub` also forces `p ≥ 5` (for `p = 3` we have `x³ = x` on `ZMod 3`, so `IsDD` implies that the
  cubic defect vanishes modulo `3`, contradicting `IsDDCubic`).

* `dd_levelSum_eq_cubicSum` (the analytic/structural core): given (D1), (D2), (D3) there is an
  integer polynomial `H = β·X + γ·X^2 + δ·X^3 + p·R` with `p ∤ δ` (a *genuine cubic* phase modulo
  `p`) such that `‖levelSum3 p e 1 (e-2) χ A C‖ = p * ‖Tsum (p^(e-3)) H‖`.
  The factor `p` and the reduction from `e-2` to `e-3` digits come from (D1) + (D2): the phase
  `u(w) = (prodCoord3 p e 1 A C w - 1)/p` is divisible by `p^2`, so the summand is constant along
  the top digit, and its expansion `u(w) = ∑ c_k w^k` has `v(c_1) ≥ 2`, `v(c_2) ≥ 2` and
  `c_3 = p^2 δ/3 + …`, so the normalized phase `u/p^2` is a genuine cubic with unit cubic
  coefficient (D3).

* `cubic_phase_prime_pow`: the cubic `p`-adic Weyl bound `‖Tsum (p^K) H‖ ≤ 8 p^(2K/3)` for genuine
  cubic phases and `p ≥ 5`, by the stationary-phase/peel induction (the cubic analogue of
  `Commons.NumberTheory.GaussSum.quadratic_phase_prime_pow`).
-/

/-- `gammaU` is the inverse of the lift of the shifted residue. -/
lemma gammaU_eq (p e : ℕ) [Fact p.Prime] (r : ZMod p) (u : ℕ) :
    Commons.NumberTheory.DirichletCharacter.gammaU p e r u
      = ((((r.val : ℕ) : ZMod (p ^ e)) + (u : ℕ)))⁻¹ := by
  rw [Commons.NumberTheory.DirichletCharacter.gammaU]
  congr 1
  push_cast
  ring

/-- The reduction of `gammaU` modulo `p`. -/
lemma gammaU_castHom (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e) (r : ZMod p) (u : ℕ)
    (hu : (r + (u : ZMod p)) ≠ 0) :
    ZMod.castHom (by simpa using pow_dvd_pow p he : p ∣ p ^ e) (ZMod p)
        (Commons.NumberTheory.DirichletCharacter.gammaU p e r u)
      = (r + (u : ZMod p))⁻¹ := by
  have h0 : ((r.val + u : ℕ) : ZMod p) = r + (u : ZMod p) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
  have h1 : ((((r.val + u : ℕ)) : ZMod (p ^ e)))
      * Commons.NumberTheory.DirichletCharacter.gammaU p e r u = 1 :=
    Commons.NumberTheory.DirichletCharacter.gammaU_mul p e r u hu he
  have h2 := congrArg (ZMod.castHom (by simpa using pow_dvd_pow p he : p ∣ p ^ e) (ZMod p)) h1
  rw [map_mul, map_one, map_natCast] at h2
  have h2' : (r + (u : ZMod p)) * ZMod.castHom (by simpa using pow_dvd_pow p he : p ∣ p ^ e)
      (ZMod p) (Commons.NumberTheory.DirichletCharacter.gammaU p e r u) = 1 := by
    rw [← h0]
    exact h2
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h2')

theorem dd_criticalSumBound {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 4 ≤ e)
    (χ : DirichletCharacter ℂ (p ^ e)) (hχ : χ.IsPrimitive)
    (a b : Fin 3 → ℕ) (r : ZMod p)
    (hcub : ∃ r' : ZMod p, Work.LinnikBurgess.IsDDCubic p e a b r')
    (hdd : Work.LinnikBurgess.IsDD p e a b r) :
    ‖∑ z : ZMod (p ^ (e - 2)),
        χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
              + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
              + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))‖
      ≤ 8 * (p : ℝ) ^ ((2 * (e : ℝ)) / 3 - 1) := by
  have he3 : 3 ≤ e := by omega
  have he1 : 1 ≤ e := by omega
  obtain ⟨hunit, hcrit, hsq, hdef⟩ := hdd
  obtain ⟨hp5, h3raw⟩ := dd_cubicUnit hp2 he1 a b r hcub ⟨hunit, hcrit, hsq, hdef⟩
  set A : Fin 3 → ZMod (p ^ e) :=
    fun l => Commons.NumberTheory.DirichletCharacter.gammaU p e r (a l) with hA
  set C : Fin 3 → ZMod (p ^ e) :=
    fun l => Commons.NumberTheory.DirichletCharacter.gammaU p e r (b l) with hC
  -- norm of the constant factor
  have hunitA : ∀ l : Fin 3, ‖χ (((r.val + a l : ℕ)) : ZMod (p ^ e))‖ = 1 := by
    intro l
    have hu : IsUnit ((((r.val + a l : ℕ)) : ZMod (p ^ e))) := by
      rw [ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) he1]
      intro hd
      refine (hunit l).1 ?_
      have h2 : ((r.val + a l : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hd
      rw [Nat.cast_add, ZMod.natCast_zmod_val] at h2
      simpa using h2
    rw [← IsUnit.unit_spec hu]
    exact Commons.NumberTheory.DirichletCharacter.norm_apply_unit χ hu.unit
  have hunitB : ∀ l : Fin 3, ‖(starRingEnd ℂ) (χ (((r.val + b l : ℕ)) : ZMod (p ^ e)))‖ = 1 := by
    intro l
    rw [Complex.norm_conj]
    have hu : IsUnit ((((r.val + b l : ℕ)) : ZMod (p ^ e))) := by
      rw [ZMod.isUnit_natCast_iff_not_dvd_pow (Fact.out : p.Prime) he1]
      intro hd
      refine (hunit l).2 ?_
      have h2 : ((r.val + b l : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hd
      rw [Nat.cast_add, ZMod.natCast_zmod_val] at h2
      simpa using h2
    rw [← IsUnit.unit_spec hu]
    exact Commons.NumberTheory.DirichletCharacter.norm_apply_unit χ hu.unit
  have hconst1 : (∏ l : Fin 3, ‖χ (((r.val + a l : ℕ)) : ZMod (p ^ e))‖) = 1 := by
    rw [Finset.prod_congr rfl (fun l _ => hunitA l), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    norm_num
  have hconst2 : (∏ l : Fin 3, ‖(starRingEnd ℂ) (χ (((r.val + b l : ℕ)) : ZMod (p ^ e)))‖) = 1 := by
    rw [Finset.prod_congr rfl (fun l _ => hunitB l), Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
    norm_num
  -- the defect conditions
  have hAeq : ∀ l : Fin 3, A l = Commons.NumberTheory.DirichletCharacter.gammaU p e r (a l) :=
    fun l => rfl
  have hCeq : ∀ l : Fin 3, C l = Commons.NumberTheory.DirichletCharacter.gammaU p e r (b l) :=
    fun l => rfl
  have hdsum1 : ddDsum p e 1 A C = ddDefect p e a b r := by
    simp only [ddDsum, ddDefect, pow_one]
    congr 1
    · exact Finset.sum_congr rfl (fun l _ => by rw [hAeq l, gammaU_eq])
    · exact Finset.sum_congr rfl (fun l _ => by rw [hCeq l, gammaU_eq])
  have hD1 : (p : ℕ) ^ 2 ∣ (ddDsum p e 1 A C).val := by rw [hdsum1]; exact hdef
  have hD3 : ¬ (p : ℕ) ∣ (ddDsum p e 3 A C).val := by
    intro hcon
    apply h3raw
    have hEq : ddDsum p e 3 A C = ddDefectK p e a b r 3 := by
      simp only [ddDsum, ddDefectK]
      congr 1
      · exact Finset.sum_congr rfl (fun l _ => by rw [hAeq l, gammaU_eq])
      · exact Finset.sum_congr rfl (fun l _ => by rw [hCeq l, gammaU_eq])
    rw [hEq] at hcon
    exact hcon
  have hdiv1 : p ∣ p ^ e := by simpa using pow_dvd_pow p he1
  have hD2 : (p : ℕ) ∣ (ddDsum p e 2 A C).val := by
    rw [← Commons.NumberTheory.DirichletCharacter.castHom_eq_zero_iff_dvd_val_one hdiv1]
    have hc : ∀ l : Fin 3, ZMod.castHom hdiv1 (ZMod p) (A l) = (r + (a l : ZMod p))⁻¹ :=
      fun l => gammaU_castHom p e he1 r (a l) (hunit l).1
    have hd : ∀ l : Fin 3, ZMod.castHom hdiv1 (ZMod p) (C l) = (r + (b l : ZMod p))⁻¹ :=
      fun l => gammaU_castHom p e he1 r (b l) (hunit l).2
    have hsumA : (∑ l : Fin 3, (ZMod.castHom hdiv1 (ZMod p) (A l)) ^ 2)
        = ∑ l : Fin 3, ((r + (a l : ZMod p))⁻¹) ^ 2 :=
      Finset.sum_congr rfl (fun l _ => by rw [hc l])
    have hsumC : (∑ l : Fin 3, (ZMod.castHom hdiv1 (ZMod p) (C l)) ^ 2)
        = ∑ l : Fin 3, ((r + (b l : ZMod p))⁻¹) ^ 2 :=
      Finset.sum_congr rfl (fun l _ => by rw [hd l])
    have hred : ZMod.castHom hdiv1 (ZMod p) (ddDsum p e 2 A C)
        = (∑ l : Fin 3, (ZMod.castHom hdiv1 (ZMod p) (A l)) ^ 2)
          - (∑ l : Fin 3, (ZMod.castHom hdiv1 (ZMod p) (C l)) ^ 2) := by
      simp only [ddDsum, map_sub, map_sum, map_pow]
    rw [hred, hsumA, hsumC, hsq, sub_self]
  -- the reconstruction
  obtain ⟨H, hH, hnorm⟩ := dd_levelSum_eq_cubicSum hp2 he χ hχ A C hD1 hD2 hD3
  have hgoal : ‖∑ z : ZMod (p ^ (e - 2)),
        χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
              + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (a l : ℕ)))
        * (starRingEnd ℂ) (χ (∏ l : Fin 3, (((r.val : ℕ) : ZMod (p ^ e))
              + (p : ZMod (p ^ e)) * ((z.val : ℕ) : ZMod (p ^ e)) + (b l : ℕ))))‖
      = (p : ℝ) * ‖Commons.NumberTheory.GaussSum.Tsum (p ^ (e - 3)) H‖ := by
    rw [Commons.NumberTheory.DirichletCharacter.target_sum_eq3 p e he3 χ a b r hunit]
    simp only [norm_mul, norm_prod, hconst1, hconst2, one_mul]
    rw [hnorm]
  rw [hgoal]
  have hbound := cubic_phase_prime_pow p (e - 3) hp5 H hH
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  calc (p : ℝ) * ‖Commons.NumberTheory.GaussSum.Tsum (p ^ (e - 3)) H‖
      ≤ (p : ℝ) * (8 * (p : ℝ) ^ ((2 * (((e - 3 : ℕ)) : ℝ)) / 3)) :=
        mul_le_mul_of_nonneg_left hbound hp0.le
    _ = 8 * (p : ℝ) ^ ((2 * (e : ℝ)) / 3 - 1) := by
        have hcast : (((e - 3 : ℕ)) : ℝ) = (e : ℝ) - 3 := by
          rw [Nat.cast_sub (by omega : 3 ≤ e)]; norm_num
        have hexp : (2 * ((e : ℝ) - 3)) / 3 + 1 = (2 * (e : ℝ)) / 3 - 1 := by ring
        have hpow : (p : ℝ) ^ ((2 * ((e : ℝ) - 3)) / 3) * (p : ℝ)
            = (p : ℝ) ^ ((2 * ((e : ℝ) - 3)) / 3 + 1) := by
          rw [Real.rpow_add hp0, Real.rpow_one]
        rw [hcast,
          show (p : ℝ) * (8 * (p : ℝ) ^ ((2 * ((e : ℝ) - 3)) / 3))
            = 8 * ((p : ℝ) ^ ((2 * ((e : ℝ) - 3)) / 3) * (p : ℝ)) by ring,
          hpow, hexp]

end Work.LinnikBurgess
