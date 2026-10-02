/-
Copyright: subproject `Submission/Work/PARIMPL/ParSplit/` of `mandelbar_not_path_connected`.
NOTE (area owner, PARIMPL): the polynomial `(F c (m + .) - (m + .))` of `ParSplit.phase_of_split`
is named `Gshift`, not `Gpoly`: `ParWall`'s `Gpoly` is a *different*, unary polynomial, and the two
modules must be importable together.  The occurrences of the old name in this file are updated.


# `Work.PARIMPL.ParSplit.wall_factorization` — the wall factorization of the discriminant

For `c` in a parameter ball, the two fixed points of `Work.EL.F c` inside the dynamical disc
`ball d.z₁ R` are the roots `m c ± δ` of the quadratic `(X - m c)² - G c`.  Writing

  `wallG c = (F c (m c + t) - (m c + t))`  (a polynomial in `t`),

the quadratic `X² - C (G c)` divides `wallG c` wherever the two roots are simple, and the quotient
`wallR c = wallG c /ₘ (X² - C (G c))` has a *continuous* family of coefficients (because it is
given by the explicit telescoping formula `Rₖ = Σⱼ gʲ (wallG).coeff (k+2+2j)`).  The product of
the two values of `wallR c` at the two roots is the "wall normalizer"

  `wallZ c = (the even part of `wallR c t * wallR c (-t)` evaluated at `G c`)`,

the symmetric function of the two roots which the multiplier relations of `phase_of_split`
(`deriv_F_of_gtc_fix`, `deriv_F_of_gtc_swap`) show to be real after multiplication by `G c`:

  `G c * wallZ c = -(1/4) (F'(m c + δ) - 1) (F'(m c - δ) - 1)`.

Then `A c = (G c * wallZ c).re` is real, vanishes exactly where `G` does, and
`h c = (wallZ c)⁻¹` is continuous and non-vanishing with `G = A * h`; this is the factorization
(H2) which `ParSplit.Sqrt.exists_continuousOn_sq_eq_mul_of_real` turns into a continuous square
root of `G`.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.PARIMPL.ParSplit.Split
import Submission.Work.PARIMPL.ParSplit.Sqrt
import Submission.Work.PARIMPL.ParSplit.BuildSplit
import Submission.Work.PARIMPL.ParSplit.g_mem_of_split
import Submission.Work.PARIMPL.ParSplit.deriv_conj_of_swap
import Submission.Work.PARIMPL.ParSplit.deriv_star_self_of_fix
import Submission.Work.PARIMPL.ParSplit.phase_of_split
import Submission.Work.PARIMPL.ParSplit.continuousAt_coeff_Gpoly
import Submission.Work.PARIMPL.ParSplit.deriv_prod_real_of_char
import Submission.Work.PARIMPL.ParSplit.divByMonic_X_sq_sub_C

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 0

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL.ParSplit

open Polynomial

/-! ## The wall data -/

/-- A fixed degree bound for the shifted second-return polynomial. -/
def wallB : ℕ := 2048

/-- The shifted second-return polynomial `G(t) = F c (m c + t) - (m c + t)`. -/
noncomputable def wallG (m : ℂ → ℂ) (c : ℂ) : Polynomial ℂ := Gshift c (m c)

/-- The quotient of `wallG m c` by `X² - C (G c)`. -/
noncomputable def wallR (m G : ℂ → ℂ) (c : ℂ) : Polynomial ℂ :=
  wallG m c /ₘ (Polynomial.X ^ 2 - Polynomial.C (G c))

/-- **The wall normalizer**: the even part of `wallR (t) * wallR (-t)`, evaluated at `G c`. -/
noncomputable def wallZ (m G : ℂ → ℂ) (c : ℂ) : ℂ :=
  ∑ n ∈ Finset.range (wallB + 1),
    (wallR m G c * (wallR m G c).comp (-Polynomial.X)).coeff (2 * n) * (G c) ^ n

/-! ## Degree bounds -/

lemma tsqP_natDegree_le (c : ℂ) :
    ((Polynomial.X ^ 2 + Polynomial.C (star c)) ^ 2 + Polynomial.C c).natDegree ≤ 4 := by
  have h1 : (Polynomial.X ^ 2 + Polynomial.C (star c) : Polynomial ℂ).natDegree ≤ 2 := by
    calc (Polynomial.X ^ 2 + Polynomial.C (star c) : Polynomial ℂ).natDegree
        ≤ max (Polynomial.X ^ 2).natDegree (Polynomial.C (star c)).natDegree :=
          Polynomial.natDegree_add_le _ _
      _ = max 2 0 := by rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
      _ = 2 := by norm_num
  calc (((Polynomial.X ^ 2 + Polynomial.C (star c)) ^ 2 + Polynomial.C c)).natDegree
      ≤ max (((Polynomial.X ^ 2 + Polynomial.C (star c)) ^ 2)).natDegree
          (Polynomial.C c).natDegree := Polynomial.natDegree_add_le _ _
    _ ≤ max 4 0 := by
        refine max_le_max ?_ ?_
        · calc (((Polynomial.X ^ 2 + Polynomial.C (star c)) ^ 2)).natDegree
              ≤ 2 * (Polynomial.X ^ 2 + Polynomial.C (star c)).natDegree :=
                Polynomial.natDegree_pow_le
            _ ≤ 2 * 2 := Nat.mul_le_mul_left 2 h1
            _ = 4 := by norm_num
        · rw [Polynomial.natDegree_C]
    _ = 4 := by norm_num

lemma natDegree_compIter_le (q : Polynomial ℂ) (n : ℕ) (hq : q.natDegree ≤ 4) :
    (compIter q n).natDegree ≤ 4 ^ n := by
  induction n with
  | zero => simp [compIter]
  | succ n ih =>
      rw [compIter]
      calc ((compIter q n).comp q).natDegree ≤ (compIter q n).natDegree * q.natDegree :=
            Polynomial.natDegree_comp_le
        _ ≤ 4 ^ n * 4 := Nat.mul_le_mul ih hq
        _ = 4 ^ (n + 1) := by ring

lemma natDegree_polyF_le (c : ℂ) : (polyF c).natDegree ≤ 1024 := by
  have := natDegree_compIter_le
    ((Polynomial.X ^ 2 + Polynomial.C (star c)) ^ 2 + Polynomial.C c) 5 (tsqP_natDegree_le c)
  simpa [polyF, show (4:ℕ)^5 = 1024 from by norm_num] using this

lemma natDegree_X_add_C_le (u : ℂ) : (Polynomial.X + Polynomial.C u).natDegree ≤ 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  simp only [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]
  rw [ite_eq_right (by omega : ¬ (1 = N)), ite_eq_right (by omega : ¬ (N = 0))]
  ring

lemma natDegree_wallG_le (m : ℂ → ℂ) (c : ℂ) : (wallG m c).natDegree ≤ 1024 := by
  have h1 : wallG m c = (polyF c).comp (Polynomial.X + Polynomial.C (m c))
      - (Polynomial.X + Polynomial.C (m c)) := rfl
  rw [h1]
  calc ((polyF c).comp (Polynomial.X + Polynomial.C (m c))
        - (Polynomial.X + Polynomial.C (m c))).natDegree
      ≤ max ((polyF c).comp (Polynomial.X + Polynomial.C (m c))).natDegree
            (Polynomial.X + Polynomial.C (m c)).natDegree := Polynomial.natDegree_sub_le _ _
    _ ≤ max 1024 1 := by
        refine max_le_max ?_ (natDegree_X_add_C_le _)
        calc ((polyF c).comp (Polynomial.X + Polynomial.C (m c))).natDegree
            ≤ (polyF c).natDegree * (Polynomial.X + Polynomial.C (m c)).natDegree :=
              Polynomial.natDegree_comp_le
          _ ≤ 1024 * 1 := Nat.mul_le_mul (natDegree_polyF_le c) (natDegree_X_add_C_le _)
          _ = 1024 := by norm_num
    _ = 1024 := by norm_num

lemma wallB_ge (k : ℕ) (hk : k ≤ 1024) : k ≤ wallB := by
  rw [show wallB = 2048 from rfl]; omega

/-! ## Evaluation and derivative of `wallG` -/

lemma wallG_eval (m : ℂ → ℂ) (c t : ℂ) :
    (wallG m c).eval t = Work.EL.F c (m c + t) - (m c + t) := Gshift_eval c (m c) t

lemma wallG_deriv_eval (m : ℂ → ℂ) (c t : ℂ) :
    (wallG m c).derivative.eval t = deriv (Work.EL.F c) (m c + t) - 1 := by
  have := deriv_Fm c (m c) t
  rw [show wallG m c = Gshift c (m c) from rfl, this]
  ring

/-! ## The explicit coefficient formula for the quotient -/

lemma coeff_finsetSum {ι : Type*} (s : Finset ι) (p : ι → Polynomial ℂ) (n : ℕ) :
    (∑ i ∈ s, p i).coeff n = ∑ i ∈ s, (p i).coeff n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Polynomial.coeff_add, ih]

lemma sum_range_eq_of_vanishing {f : ℕ → ℂ} {N M : ℕ} (hNM : N ≤ M)
    (hf : ∀ j, N < j → f j = 0) :
    ∑ j ∈ Finset.range (N + 1), f j = ∑ j ∈ Finset.range (M + 1), f j := by
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro x hxt hxs
    simp only [Finset.mem_range] at hxt hxs
    exact hf x (by omega)

/-- **The explicit telescoping formula** for the quotient of `wallG m c` by `X² - C (G c)`. -/
lemma wallR_coeff (m G : ℂ → ℂ) (c : ℂ) (k : ℕ) :
    (wallR m G c).coeff k
      = ∑ j ∈ Finset.range (wallB + 1), (G c) ^ j * (wallG m c).coeff (k + 2 + 2 * j) := by
  have hB : (wallG m c).natDegree ≤ wallB := wallB_ge _ (natDegree_wallG_le m c)
  rw [wallR, divByMonic_X_sq_sub_C, coeff_finsetSum]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  by_cases hk : k ≤ (wallG m c).natDegree
  · rw [ite_eq_left (by simp only [Finset.mem_range]; omega :
        k ∈ Finset.range ((wallG m c).natDegree + 1))]
    exact sum_range_eq_of_vanishing hB (fun j hj => by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), mul_zero])
  · rw [ite_eq_right (by simp only [Finset.mem_range]; omega :
        k ∉ Finset.range ((wallG m c).natDegree + 1))]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp only [Finset.mem_range] at hj; omega),
      mul_zero]

/-! ## Continuity of the wall data -/

lemma continuousAt_finsetSum {ι X : Type*} [TopologicalSpace X] {s : Finset ι}
    {f : ι → X → ℂ} {x : X}
    (h : ∀ i ∈ s, ContinuousAt (f i) x) : ContinuousAt (fun y => ∑ i ∈ s, f i y) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuousAt_const
  | insert a s ha ih =>
      have hsplit : (fun y => ∑ i ∈ insert a s, f i y) = fun y => f a y + ∑ i ∈ s, f i y := by
        funext y; rw [Finset.sum_insert ha]
      rw [hsplit]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

lemma continuousAt_wallG_coeff {m : ℂ → ℂ} {c : ℂ} (hm : ContinuousAt m c) (k : ℕ) :
    ContinuousAt (fun c' : ℂ => (wallG m c').coeff k) c :=
  continuousAt_coeff_Gpoly hm k

lemma continuousAt_wallR_coeff {m G : ℂ → ℂ} {c : ℂ} (hm : ContinuousAt m c)
    (hG : ContinuousAt G c) (k : ℕ) :
    ContinuousAt (fun c' : ℂ => (wallR m G c').coeff k) c := by
  have h : (fun c' : ℂ => (wallR m G c').coeff k)
      = fun c' => ∑ j ∈ Finset.range (wallB + 1),
          (G c') ^ j * (wallG m c').coeff (k + 2 + 2 * j) := by
    funext c'
    exact wallR_coeff m G c' k
  rw [h]
  exact continuousAt_finsetSum (fun j _ => (hG.pow j).mul (continuousAt_wallG_coeff hm _))

lemma coeff_comp_neg_X (p : Polynomial ℂ) (k : ℕ) :
    (p.comp (-Polynomial.X)).coeff k = (-1) ^ k * p.coeff k := by
  have hp : p.comp (-Polynomial.X)
      = ∑ i ∈ Finset.range (p.natDegree + 1),
          Polynomial.C (p.coeff i) * (-Polynomial.X) ^ i := by
    rw [Polynomial.comp, Polynomial.eval₂_eq_sum_range]
  rw [hp, coeff_finsetSum]
  have hterm : ∀ i : ℕ, (Polynomial.C (p.coeff i) * (-Polynomial.X) ^ i).coeff k
      = if k = i then (-1) ^ i * p.coeff i else 0 := by
    intro i
    have hpow : (-Polynomial.X) ^ i = Polynomial.C ((-1 : ℂ) ^ i) * Polynomial.X ^ i := by
      have h1 : (-Polynomial.X : Polynomial ℂ) = Polynomial.C (-1) * Polynomial.X := by
        rw [Polynomial.C_neg, Polynomial.C_1]; ring
      rw [h1, mul_pow, ← map_pow]
    rw [hpow, ← mul_assoc, ← Polynomial.C_mul, Polynomial.coeff_C_mul_X_pow]
    by_cases hk : k = i <;> simp [hk, mul_comm]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [Finset.sum_ite_eq]
  by_cases hk : k ≤ p.natDegree
  · rw [ite_eq_left (by simp only [Finset.mem_range]; omega :
        k ∈ Finset.range (p.natDegree + 1))]
  · rw [ite_eq_right (by simp only [Finset.mem_range]; omega :
        k ∉ Finset.range (p.natDegree + 1)),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    ring

lemma continuousAt_wallZ {m G : ℂ → ℂ} {c : ℂ} (hm : ContinuousAt m c)
    (hG : ContinuousAt G c) :
    ContinuousAt (fun c' : ℂ => wallZ m G c') c := by
  have h : (fun c' : ℂ => wallZ m G c') = fun c' => ∑ n ∈ Finset.range (wallB + 1),
      ((wallR m G c' * (wallR m G c').comp (-Polynomial.X)).coeff (2 * n)) * (G c') ^ n := rfl
  rw [h]
  refine continuousAt_finsetSum (fun n _ => ?_)
  have hpt : ∀ c' : ℂ, (wallR m G c' * (wallR m G c').comp (-Polynomial.X)).coeff (2 * n)
      = ∑ i ∈ Finset.HasAntidiagonal.antidiagonal (2 * n),
          (wallR m G c').coeff i.1 * ((-1) ^ i.2 * (wallR m G c').coeff i.2) := by
    intro c'
    rw [Polynomial.coeff_mul]
    exact Finset.sum_congr rfl (fun i _ => by rw [coeff_comp_neg_X])
  have hfun : (fun c' : ℂ =>
        (wallR m G c' * (wallR m G c').comp (-Polynomial.X)).coeff (2 * n) * (G c') ^ n)
      = fun c' => (∑ i ∈ Finset.HasAntidiagonal.antidiagonal (2 * n),
          (wallR m G c').coeff i.1 * ((-1) ^ i.2 * (wallR m G c').coeff i.2)) * (G c') ^ n := by
    funext c'; rw [hpt c']
  rw [hfun]
  exact (continuousAt_finsetSum (fun i _ =>
    (continuousAt_wallR_coeff hm hG i.1).mul
      (continuousAt_const.mul (continuousAt_wallR_coeff hm hG i.2)))).mul (hG.pow n)


/-! ## The even part identity for `wallZ` -/

lemma comp_neg_X_comp_neg_X (p : Polynomial ℂ) :
    (p.comp (-Polynomial.X)).comp (-Polynomial.X) = p := by
  rw [Polynomial.comp_assoc]
  have h : (-Polynomial.X : Polynomial ℂ).comp (-Polynomial.X) = Polynomial.X := by
    rw [Polynomial.neg_comp, Polynomial.X_comp, neg_neg]
  rw [h, Polynomial.comp_X]

lemma eval_comp_neg_X (p : Polynomial ℂ) (z : ℂ) :
    (p.comp (-Polynomial.X)).eval z = p.eval (-z) := by
  rw [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]

lemma coeff_eq_zero_of_odd {p : Polynomial ℂ} (heven : p.comp (-Polynomial.X) = p) {k : ℕ}
    (hk : k % 2 = 1) : p.coeff k = 0 := by
  have h := coeff_comp_neg_X p k
  rw [heven] at h
  have hneg : ((-1 : ℂ)) ^ k = -1 := (Nat.odd_iff.mpr hk).neg_one_pow
  rw [hneg] at h
  have h3 : (2 : ℂ) * p.coeff k = 0 := by linear_combination h
  exact (mul_eq_zero.mp h3).resolve_left (by norm_num)

lemma eq_sum_even_monomials {p : Polynomial ℂ} (heven : p.comp (-Polynomial.X) = p) :
    p = ∑ n ∈ Finset.range (p.natDegree + 1),
        Polynomial.C (p.coeff (2 * n)) * Polynomial.X ^ (2 * n) := by
  refine Polynomial.ext (fun k => ?_)
  rw [coeff_finsetSum]
  rw [Finset.sum_congr rfl (fun n _ => by rw [Polynomial.coeff_C_mul_X_pow])]
  by_cases hk : k % 2 = 1
  · rw [coeff_eq_zero_of_odd heven hk, Finset.sum_eq_zero (fun n hn => by
      rw [ite_eq_right (by intro h; omega : ¬ (k = 2 * n))])]
  · have hk2 : k = 2 * (k / 2) := by omega
    rw [hk2]
    rw [Finset.sum_eq_single (k / 2)]
    · rw [ite_eq_left (by ring)]
    · intro n hn hn2
      rw [ite_eq_right (by omega : ¬ (2 * (k / 2) = 2 * n))]
    · intro hmem
      simp only [Finset.mem_range] at hmem
      rw [ite_eq_left (by ring), Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

lemma natDegree_wallR_le (m G : ℂ → ℂ) (c : ℂ) : (wallR m G c).natDegree ≤ 1024 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [wallR_coeff]
  exact Finset.sum_eq_zero (fun j _ => by
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by have := natDegree_wallG_le m c; omega),
      mul_zero])

/-- **The even part identity**: the wall normalizer is the product of the two values of the
quotient at the two roots of `X² - C (G c)`. -/
lemma wallZ_eval_mul {m G : ℂ → ℂ} {c δ : ℂ} (hδ : δ ^ 2 = G c) :
    wallZ m G c = (wallR m G c).eval δ * (wallR m G c).eval (-δ) := by
  set R : Polynomial ℂ := wallR m G c
  set Ψ : Polynomial ℂ := R * R.comp (-Polynomial.X)
  have hΨeven : Ψ.comp (-Polynomial.X) = Ψ := by
    rw [show Ψ = R * R.comp (-Polynomial.X) from rfl, Polynomial.mul_comp,
      comp_neg_X_comp_neg_X]
    ring
  have hdecomp := eq_sum_even_monomials hΨeven
  have hdeg : Ψ.natDegree ≤ wallB := by
    have hcomp : (R.comp (-Polynomial.X)).natDegree ≤ R.natDegree := by
      calc (R.comp (-Polynomial.X)).natDegree ≤ R.natDegree * (-Polynomial.X).natDegree :=
            Polynomial.natDegree_comp_le
        _ = R.natDegree * 1 := by rw [Polynomial.natDegree_neg, Polynomial.natDegree_X]
        _ = R.natDegree := by ring
    calc Ψ.natDegree = (R * R.comp (-Polynomial.X)).natDegree := rfl
      _ ≤ R.natDegree + (R.comp (-Polynomial.X)).natDegree := Polynomial.natDegree_mul_le
      _ ≤ 1024 + 1024 := Nat.add_le_add (natDegree_wallR_le m G c)
          (le_trans hcomp (natDegree_wallR_le m G c))
      _ = wallB := by rw [show wallB = 2048 from rfl]
  have hf : ∀ j, Ψ.natDegree < j → Ψ.coeff (2 * j) * (G c) ^ j = 0 := by
    intro j hj
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]
  have hmain : wallZ m G c = ∑ n ∈ Finset.range (Ψ.natDegree + 1), Ψ.coeff (2 * n) * (G c) ^ n := by
    rw [show wallZ m G c = ∑ n ∈ Finset.range (wallB + 1), Ψ.coeff (2 * n) * (G c) ^ n from rfl]
    exact (sum_range_eq_of_vanishing hdeg hf).symm
  rw [hmain]
  have heval : Ψ.eval δ
      = ∑ n ∈ Finset.range (Ψ.natDegree + 1), Ψ.coeff (2 * n) * δ ^ (2 * n) := by
    conv_lhs => rw [hdecomp]
    rw [Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl (fun n _ => by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X])
  have hsum : ∑ n ∈ Finset.range (Ψ.natDegree + 1), Ψ.coeff (2 * n) * (G c) ^ n
      = ∑ n ∈ Finset.range (Ψ.natDegree + 1), Ψ.coeff (2 * n) * δ ^ (2 * n) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [show δ ^ (2 * n) = (G c) ^ n by rw [pow_mul, hδ]]
  rw [hsum, ← heval]
  rw [show Ψ = R * R.comp (-Polynomial.X) from rfl, Polynomial.eval_mul, eval_comp_neg_X]



/-! ## Divisibility of `wallG` by the quadratic at simple roots -/

lemma wallG_eq_mul_wallR {m G : ℂ → ℂ} {c δ : ℂ} (hδ : δ ^ 2 = G c) (hδ0 : δ ≠ 0)
    (h1 : (wallG m c).eval δ = 0) (h2 : (wallG m c).eval (-δ) = 0) :
    wallG m c = (Polynomial.X ^ 2 - Polynomial.C (G c)) * wallR m G c := by
  obtain ⟨R, hR⟩ := Polynomial.dvd_iff_isRoot.mpr (Polynomial.IsRoot.def.mpr h1)
  have hReval : Polynomial.IsRoot R (-δ) := by
    have h := congrArg (fun p : Polynomial ℂ => p.eval (-δ)) hR
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.IsRoot.def] at h ⊢
    rw [h2] at h
    have hne : -δ - δ ≠ 0 := by intro hh; exact hδ0 (by linear_combination (-1/2 : ℂ) * hh)
    exact (mul_eq_zero.mp h.symm).resolve_left hne
  obtain ⟨S, hS⟩ := Polynomial.dvd_iff_isRoot.mpr hReval
  have hX : (Polynomial.X - Polynomial.C δ) * (Polynomial.X + Polynomial.C δ)
      = Polynomial.X ^ 2 - Polynomial.C (G c) := by
    rw [← hδ]
    simp only [map_pow]
    ring
  have hfac : wallG m c = (Polynomial.X ^ 2 - Polynomial.C (G c)) * S := by
    rw [hR, hS, Polynomial.C_neg, sub_neg_eq_add, ← mul_assoc, hX]
  have hQmonic : (Polynomial.X ^ 2 - Polynomial.C (G c) : Polynomial ℂ).Monic :=
    Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hdeg : (0 : Polynomial ℂ).degree < (Polynomial.X ^ 2 - Polynomial.C (G c)).degree := by
    rw [Polynomial.degree_X_pow_sub_C (by norm_num), Polynomial.degree_zero]
    exact WithBot.bot_lt_coe 2
  have hquot := (Polynomial.div_modByMonic_unique S (0 : Polynomial ℂ) hQmonic
    ⟨by rw [zero_add], hdeg⟩).1
  have hquot' : wallG m c /ₘ (Polynomial.X ^ 2 - Polynomial.C (G c)) = S :=
    hfac ▸ hquot
  rw [wallR, hquot', ← hfac]

/-! ## The two explicit facts about `Complex.sqrt` -/

lemma sqrt_sq_C (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  rw [Complex.sqrt]
  exact Complex.cpow_nat_inv_pow z (n := 2) (by norm_num)

lemma norm_sqrt_C (z : ℂ) : ‖Complex.sqrt z‖ = Real.sqrt ‖z‖ := by
  have h2 : ‖Complex.sqrt z‖ ^ 2 = ‖z‖ := by rw [← norm_pow, sqrt_sq_C]
  calc ‖Complex.sqrt z‖ = Real.sqrt (‖Complex.sqrt z‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt ‖z‖ := by rw [h2]

lemma eval_zero_coeff (p : Polynomial ℂ) : p.eval 0 = p.coeff 0 := by
  rw [Polynomial.eval_eq_sum_range]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b hb hb0
    rw [zero_pow hb0, mul_zero]
  · intro h
    simp at h



attribute [local irreducible] Work.EL.F LeanEval.ComplexAnalysis.Tantibar Work.Landing.Tsq

lemma wallZ_mul_real {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) {R : ℝ} (hR : 0 < R)
    {m G : ℂ → ℂ} {c : ℂ} {εg η : ℝ}
    (hεgb : Metric.ball (c₀, d.z₁) εg ⊆
      (fun p : ℂ × ℂ => Work.PARIMPL.gtc p.1 p.2) ⁻¹' Metric.ball d.z₁ R)
    (hηR : η ≤ R) (hηg : η ≤ εg) (hcεg : dist c c₀ < εg)
    (hsmall : dist (m c) d.z₁ + Real.sqrt ‖G c‖ < η)
    (hchar : ∀ z ∈ Metric.ball d.z₁ R, (Work.EL.F c z = z ↔ (z - m c) ^ 2 = G c)) :
    G c * wallZ m G c = (((G c * wallZ m G c).re : ℝ) : ℂ) := by
  by_cases hG0 : G c = 0
  · rw [hG0, zero_mul]
    simp
  · set δ : ℂ := Complex.sqrt (G c) with hδdef
    have hδsq : δ ^ 2 = G c := by rw [hδdef]; exact sqrt_sq_C (G c)
    have hδ0 : δ ≠ 0 := by
      intro h
      exact hG0 (by rw [← hδsq, h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
    have hδnorm : ‖δ‖ = Real.sqrt ‖G c‖ := by rw [hδdef]; exact norm_sqrt_C (G c)
    have hφ' := hsmall
    have hrootd : dist (m c + δ) d.z₁ < η ∧ dist (m c - δ) d.z₁ < η := by
      constructor
      · rw [dist_eq_norm]
        calc ‖m c + δ - d.z₁‖ ≤ ‖m c - d.z₁‖ + ‖δ‖ := by
              rw [show m c + δ - d.z₁ = (m c - d.z₁) + δ by ring]
              exact norm_add_le _ _
          _ = dist (m c) d.z₁ + Real.sqrt ‖G c‖ := by rw [dist_eq_norm, hδnorm]
          _ < η := hφ'
      · rw [dist_eq_norm]
        calc ‖m c - δ - d.z₁‖ ≤ ‖(m c - d.z₁) - δ‖ := by
              rw [show m c - δ - d.z₁ = (m c - d.z₁) - δ by ring]
          _ ≤ ‖m c - d.z₁‖ + ‖δ‖ := norm_sub_le _ _
          _ = dist (m c) d.z₁ + Real.sqrt ‖G c‖ := by rw [dist_eq_norm, hδnorm]
          _ < η := hφ'
    have hplus : m c + δ ∈ Metric.ball d.z₁ R := by
      rw [mem_ball]; exact lt_of_lt_of_le hrootd.1 hηR
    have hminus : m c - δ ∈ Metric.ball d.z₁ R := by
      rw [mem_ball]; exact lt_of_lt_of_le hrootd.2 hηR
    have hp_mem : ((c, m c + δ) : ℂ × ℂ) ∈ Metric.ball (c₀, d.z₁) εg := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt hcεg (lt_of_lt_of_le hrootd.1 hηg)
    have hm_mem : ((c, m c - δ) : ℂ × ℂ) ∈ Metric.ball (c₀, d.z₁) εg := by
      rw [Metric.mem_ball, Prod.dist_eq]
      exact max_lt hcεg (lt_of_lt_of_le hrootd.2 hηg)
    have hgplus : Work.PARIMPL.gtc c (m c + δ) ∈ Metric.ball d.z₁ R := hεgb hp_mem
    have hgminus : Work.PARIMPL.gtc c (m c - δ) ∈ Metric.ball d.z₁ R := hεgb hm_mem
    have hfixp : Work.EL.F c (m c + δ) = m c + δ :=
      (hchar _ hplus).mpr (by rw [add_sub_cancel_left, hδsq])
    have hfixm : Work.EL.F c (m c - δ) = m c - δ :=
      (hchar _ hminus).mpr (by rw [sub_sub_cancel_left, neg_sq, hδsq])
    obtain ⟨t, ht⟩ := deriv_prod_real_of_char d hR hchar hδsq
      hplus hminus hgplus hgminus
    have hquot : wallG m c = (Polynomial.X ^ 2 - Polynomial.C (G c)) * wallR m G c := by
      refine wallG_eq_mul_wallR hδsq hδ0 ?_ ?_
      · rw [wallG_eval, hfixp]; ring
      · rw [wallG_eval, show m c + -δ = m c - δ by ring, hfixm]; ring
    have hQeval : (Polynomial.X ^ 2 - Polynomial.C (G c) : Polynomial ℂ).eval δ = 0 := by
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        hδsq, sub_self]
    have hQeval' : (Polynomial.X ^ 2 - Polynomial.C (G c) : Polynomial ℂ).eval (-δ) = 0 := by
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        neg_sq, hδsq, sub_self]
    have hderQ : (Polynomial.X ^ 2 - Polynomial.C (G c) : Polynomial ℂ).derivative
        = Polynomial.C (2 : ℂ) * Polynomial.X := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_X_pow, Polynomial.derivative_C,
        sub_zero]
      norm_num
    have hQd : (Polynomial.X ^ 2 - Polynomial.C (G c) : Polynomial ℂ).derivative.eval δ
        = 2 * δ := by
      rw [hderQ, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    have hQd' : (Polynomial.X ^ 2 - Polynomial.C (G c) : Polynomial ℂ).derivative.eval (-δ)
        = -(2 * δ) := by
      rw [hderQ, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring
    have hd1 : (wallG m c).derivative.eval δ = 2 * δ * (wallR m G c).eval δ := by
      rw [hquot, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_mul, hQeval, hQd]
      ring
    have hd2 : (wallG m c).derivative.eval (-δ) = -(2 * δ) * (wallR m G c).eval (-δ) := by
      rw [hquot, Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_mul, hQeval', hQd']
      ring
    have h1 := wallG_deriv_eval m c δ
    have h2 := wallG_deriv_eval m c (-δ)
    have hkey : G c * wallZ m G c
        = -((deriv (Work.EL.F c) (m c + δ) - 1)
            * (deriv (Work.EL.F c) (m c - δ) - 1)) / 4 := by
      rw [show m c - δ = m c + (-δ) by ring]
      rw [wallZ_eval_mul hδsq, ← h1, ← h2, hd1, hd2, ← hδsq]
      ring
    rw [hkey, ht, show (-(t : ℂ)) / 4 = ((-(t / 4) : ℝ) : ℂ) by push_cast; ring,
      Complex.ofReal_re]

/-- **The wall factorization** `G = A · h` with `A` real-valued (H2 of the ParSplit design). -/
theorem wall_factorization {c₀ : ℂ} (d : Work.EL.RootParabolic c₀)
    {ρ R : ℝ} (hρ : 0 < ρ) (hR : 0 < R) {m G : ℂ → ℂ}
    (hm : ContinuousOn m (Metric.ball c₀ ρ)) (hG : ContinuousOn G (Metric.ball c₀ ρ))
    (hm₀ : m c₀ = d.z₁) (hG₀ : G c₀ = 0)
    (hchar : ∀ c ∈ Metric.ball c₀ ρ, ∀ z ∈ Metric.ball d.z₁ R,
      (Work.EL.F c z = z ↔ (z - m c) ^ 2 = G c)) :
    ∃ ρ' > 0, ρ' ≤ ρ ∧ ∃ A : ℂ → ℝ, ContinuousOn A (Metric.ball c₀ ρ') ∧
      (∀ c ∈ Metric.ball c₀ ρ', A c = 0 ↔ G c = 0) ∧
      ∃ h : ℂ → ℂ, ContinuousOn h (Metric.ball c₀ ρ') ∧
        (∀ c ∈ Metric.ball c₀ ρ', h c ≠ 0) ∧
        (∀ c ∈ Metric.ball c₀ ρ', G c = (A c : ℂ) * h c) := by
  have hc₀ρ : c₀ ∈ Metric.ball c₀ ρ := mem_ball_self hρ
  have hmc : ContinuousAt m c₀ := hm.continuousAt (isOpen_ball.mem_nhds hc₀ρ)
  have hGc : ContinuousAt G c₀ := hG.continuousAt (isOpen_ball.mem_nhds hc₀ρ)
  -- `g c = (T_c)^5` maps a small neighbourhood of `(c₀, z₁)` into the dynamical disc
  have hgcont : ContinuousAt (fun p : ℂ × ℂ => Work.PARIMPL.gtc p.1 p.2) (c₀, d.z₁) :=
    continuous_gtc_prod.continuousAt
  have hgbase : Work.PARIMPL.gtc c₀ d.z₁ = d.z₁ := d.per_half
  obtain ⟨εg, hεg, hεgb⟩ := Metric.mem_nhds_iff.mp (hgcont.preimage_mem_nhds
    (isOpen_ball.mem_nhds (by rw [hgbase]; exact mem_ball_self hR)))
  set η : ℝ := min R εg with hηdef
  have hη : 0 < η := lt_min hR hεg
  have hηR : η ≤ R := min_le_left _ _
  have hηg : η ≤ εg := min_le_right _ _
  -- shrink the parameter ball so that both roots are close to `z₁`
  have hφc : ContinuousAt (fun c : ℂ => dist (m c) d.z₁ + Real.sqrt ‖G c‖) c₀ :=
    (hmc.dist continuousAt_const).add (Real.continuous_sqrt.continuousAt.comp hGc.norm)
  have hφ0 : dist (m c₀) d.z₁ + Real.sqrt ‖G c₀‖ < η := by
    rw [hm₀, hG₀, dist_self, norm_zero, Real.sqrt_zero, add_zero]; exact hη
  obtain ⟨εφ, hεφ, hεφb⟩ := Metric.mem_nhds_iff.mp (hφc.preimage_mem_nhds
    ((isOpen_lt continuous_id continuous_const).mem_nhds hφ0))
  set ρ₀ : ℝ := min (min εφ ρ) εg with hρ₀def
  have hρ₀ : 0 < ρ₀ := lt_min (lt_min hεφ hρ) hεg
  have hρ₀ρ : ρ₀ ≤ ρ := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρ₀εg : ρ₀ ≤ εg := min_le_right _ _
  have hρ₀εφ : ρ₀ ≤ εφ := le_trans (min_le_left _ _) (min_le_left _ _)
  have hsmall : ∀ c ∈ Metric.ball c₀ ρ₀, dist (m c) d.z₁ + Real.sqrt ‖G c‖ < η :=
    fun c hc => hεφb (lt_of_lt_of_le hc hρ₀εφ)
  -- **reality** of `G c * wallZ c` on `ball c₀ ρ₀`
  have hreal : ∀ c ∈ Metric.ball c₀ ρ₀,
      G c * wallZ m G c = (((G c * wallZ m G c).re : ℝ) : ℂ) := by
    intro c hc
    exact wallZ_mul_real d hR hεgb hηR hηg (lt_of_lt_of_le (mem_ball.mp hc) hρ₀εg)
      (hsmall c hc) (fun z hz => hchar c (ball_subset_ball hρ₀ρ hc) z hz)
  -- `wallZ c₀ ≠ 0`
  have hZf0 : wallZ m G c₀ ≠ 0 := by
    have h1 : wallZ m G c₀ = (wallR m G c₀).eval 0 * (wallR m G c₀).eval 0 := by
      have h := wallZ_eval_mul (m := m) (G := G) (c := c₀) (δ := 0) (by rw [hG₀]; ring)
      simpa using h
    have h2 : (wallR m G c₀).eval 0 = (wallG m c₀).coeff 2 := by
      rw [eval_zero_coeff, wallR_coeff]
      rw [hG₀]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j hj hj0
        rw [zero_pow hj0, zero_mul]
      · intro h; simp at h
    have h3 : (wallG m c₀).coeff 2 = iteratedDeriv 2 (Work.EL.F c₀) d.z₁ / 2 := by
      rw [show wallG m c₀ = Gshift c₀ (m c₀) from rfl, hm₀]
      exact Gshift_coeff_two c₀ d.z₁
    rw [h1, h2, h3]
    exact mul_ne_zero (div_ne_zero d.simple (by norm_num))
      (div_ne_zero d.simple (by norm_num))
  -- the final ball
  have hZfcont : ContinuousAt (fun c : ℂ => wallZ m G c) c₀ := continuousAt_wallZ hmc hGc
  have hneigh : {c : ℂ | wallZ m G c ≠ 0} ∈ 𝓝 c₀ :=
    hZfcont.preimage_mem_nhds (isOpen_ne.mem_nhds hZf0)
  obtain ⟨εz, hεz, hεzb⟩ := Metric.mem_nhds_iff.mp hneigh
  set ρ' : ℝ := min ρ₀ εz with hρ'def
  have hρ' : 0 < ρ' := lt_min hρ₀ hεz
  have hρ'ρ₀ : ρ' ≤ ρ₀ := min_le_left _ _
  have hρ'z : ρ' ≤ εz := min_le_right _ _
  have hsub : Metric.ball c₀ ρ' ⊆ Metric.ball c₀ ρ₀ := ball_subset_ball hρ'ρ₀
  have hZfne : ∀ c ∈ Metric.ball c₀ ρ', wallZ m G c ≠ 0 := fun c hc =>
    hεzb (lt_of_lt_of_le hc hρ'z)
  have hrealle : ∀ c ∈ Metric.ball c₀ ρ', G c * wallZ m G c
      = (((G c * wallZ m G c).re : ℝ) : ℂ) := fun c hc => hreal c (hsub hc)
  refine ⟨ρ', hρ', le_trans hρ'ρ₀ hρ₀ρ, fun c => (G c * wallZ m G c).re, ?_, ?_,
    fun c => (wallZ m G c)⁻¹, ?_, ?_, ?_⟩
  · -- continuity of `A`
    intro x hx
    rw [continuousWithinAt_iff_continuousAt (isOpen_ball.mem_nhds hx)]
    have hxρ : x ∈ Metric.ball c₀ ρ := ball_subset_ball (le_trans hρ'ρ₀ hρ₀ρ) hx
    exact Complex.continuous_re.continuousAt.comp
      ((hG.continuousAt (isOpen_ball.mem_nhds hxρ)).mul
        (continuousAt_wallZ (hm.continuousAt (isOpen_ball.mem_nhds hxρ))
          (hG.continuousAt (isOpen_ball.mem_nhds hxρ))))
  · -- the zero set of `A`
    intro c hc
    constructor
    · intro hA0
      have h1 : G c * wallZ m G c = 0 := by
        rw [hrealle c hc]
        show (((G c * wallZ m G c).re : ℝ) : ℂ) = 0
        have hA0' : (G c * wallZ m G c).re = 0 := hA0
        rw [hA0']
        simp
      exact (mul_eq_zero.mp h1).resolve_right (hZfne c hc)
    · intro hG0
      show (G c * wallZ m G c).re = 0
      rw [hG0, zero_mul, Complex.zero_re]
  · -- continuity of `h`
    intro x hx
    rw [continuousWithinAt_iff_continuousAt (isOpen_ball.mem_nhds hx)]
    have hxρ : x ∈ Metric.ball c₀ ρ := ball_subset_ball (le_trans hρ'ρ₀ hρ₀ρ) hx
    exact (continuousAt_wallZ (hm.continuousAt (isOpen_ball.mem_nhds hxρ))
      (hG.continuousAt (isOpen_ball.mem_nhds hxρ))).inv₀ (hZfne x hx)
  · intro c hc
    exact inv_ne_zero (hZfne c hc)
  · intro c hc
    rw [← hrealle c hc, mul_inv_cancel_right₀ (hZfne c hc)]

end Work.PARIMPL.ParSplit
