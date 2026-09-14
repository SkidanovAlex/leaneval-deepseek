import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.ZMod.Defs

namespace Commons.Algebra.MvPolynomial

open _root_.MvPolynomial
open scoped BigOperators

section Helpers

variable {K : Type*} [CommSemiring K] {m : ℕ}

/-- The blockwise dehomogenisation map: in each block `h` it substitutes the chart coordinate
`X (h, c h)` by `1` and the other coordinate `X (h, 1 - c h)` by `X h`. -/
noncomputable abbrev dehom (c : Fin m → Fin 2) :
    MvPolynomial (Fin m × Fin 2) K →ₐ[K] MvPolynomial (Fin m) K :=
  MvPolynomial.aeval (fun hi : Fin m × Fin 2 =>
    if hi.2 = c hi.1 then (1 : MvPolynomial (Fin m) K) else MvPolynomial.X hi.1)

/-- The value at `a` of a finsupp written as a sum of single-supported finsupps. -/
lemma finset_sum_single_apply {ι M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (s : Finset ι) (f : ι → M) (a : ι) :
    (∑ i ∈ s, Finsupp.single i (f i)) a = if a ∈ s then f a else 0 := by
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

/-- In `Fin 2` every element is either the given one or "one minus it". -/
lemma fin2_eq_or_sub (c j : Fin 2) : j = c ∨ j = (1 : Fin 2) - c := by
  fin_cases c <;> fin_cases j <;> decide

/-- The two elements `c h` and `1 - c h` of `Fin 2` enumerate the block `h`, so the two
exponents add up to the same total. -/
lemma block_perm (u : (Fin m × Fin 2) →₀ ℕ) (c : Fin m → Fin 2) (h : Fin m) :
    u (h, c h) + u (h, (1 : Fin 2) - c h) = u (h, 0) + u (h, 1) := by
  generalize hh : c h = ch
  fin_cases ch <;> simp_all [Nat.add_comm]

/-- The dehomogenisation of a monomial. -/
lemma dehom_monomial (c : Fin m → Fin 2) (u : (Fin m × Fin 2) →₀ ℕ) (a : K) :
    dehom c (MvPolynomial.monomial u a)
      = MvPolynomial.monomial (∑ h : Fin m, Finsupp.single h (u (h, (1 : Fin 2) - c h))) a := by
  rw [dehom, MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  have hprod : u.prod (fun i k =>
        (if i.2 = c i.1 then (1 : MvPolynomial (Fin m) K) else MvPolynomial.X i.1) ^ k)
      = MvPolynomial.monomial (∑ h : Fin m, Finsupp.single h (u (h, (1 : Fin 2) - c h))) 1 := by
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    rw [Fintype.prod_prod_type]
    have hblock : ∀ h : Fin m,
        (∏ j : Fin 2, (if j = c h then (1 : MvPolynomial (Fin m) K) else MvPolynomial.X h)
            ^ u (h,j))
        = MvPolynomial.X h ^ (u (h, (1 : Fin 2) - c h)) := by
      intro h
      rw [Fin.prod_univ_two]
      have hc : c h = 0 ∨ c h = 1 := by
        generalize hh : c h = ch
        fin_cases ch <;> simp_all
      rcases hc with hc | hc
      · rw [hc]
        have h1 : (1 : Fin 2) - 0 = 1 := by decide
        simp [h1]
      · rw [hc]
        have h2 : (1 : Fin 2) - 1 = 0 := by decide
        simp
    calc (∏ h : Fin m, ∏ j : Fin 2,
            (if j = c h then (1 : MvPolynomial (Fin m) K) else MvPolynomial.X h) ^ u (h,j))
        = ∏ h : Fin m, MvPolynomial.X h ^ (u (h, (1 : Fin 2) - c h)) :=
          Finset.prod_congr rfl (fun h _ => hblock h)
      _ = MvPolynomial.monomial
            (Finsupp.indicator Finset.univ (fun i _ => u (i, (1 : Fin 2) - c i))) 1 :=
          MvPolynomial.prod_X_pow _ _
      _ = MvPolynomial.monomial (∑ h : Fin m, Finsupp.single h (u (h, (1 : Fin 2) - c h))) 1 := by
          congr 1
          rw [Finsupp.indicator_eq_sum_single]
  rw [hprod, MvPolynomial.C_mul_monomial, mul_one]

end Helpers

variable {K : Type*} [Field K] {m : ℕ}

/-- **Coefficients of the blockwise dehomogenisation** (two variables per block).

Let `K` be a field, `c : Fin m → Fin 2` a choice of chart coordinate in each block, and
`G ∈ K[X (h,0), X (h,1)]` a polynomial which is homogeneous of degree `d h` in block `h`
(expressed as: every exponent vector in the support has `(h,0)`-exponent plus `(h,1)`-exponent
equal to `d h`).  Then the dehomogenisation
`dehom G := aeval (fun hi => if hi.2 = c hi.1 then 1 else X hi.1) G`, which substitutes
`X (h, c h) ↦ 1` and `X (h, 1 - c h) ↦ X h`, has `t`-th coefficient equal to the coefficient of
`G` at the unique exponent vector with `(h, 1 - c h)`-exponent `t h` and `(h, c h)`-exponent
`d h - t h`.

Proof: `dehom (monomial u a) = a • ∏ h, X h ^ (u (h, 1 - c h))` (a product over the support may
be extended to the full type because the exponent is `0` off the support); hence the coefficient
of `Y ^ t` is the sum of the coefficients `a` of those `u` with `u (h, 1 - c h) = t h` for all
`h`; by the homogeneity hypothesis such a `u` is unique (its other coordinates are
`d h - t h`), and it is exactly the exponent vector displayed. -/
theorem coeff_aeval_dehomog_two_vars {K : Type*} [Field K] {m : ℕ} (c : Fin m → Fin 2)
    (d : Fin m → ℕ) (G : MvPolynomial (Fin m × Fin 2) K)
    (hhom : ∀ u ∈ G.support, ∀ h : Fin m, u (h, 0) + u (h, 1) = d h) (t : Fin m →₀ ℕ) :
    (MvPolynomial.aeval (fun hi : Fin m × Fin 2 =>
        if hi.2 = c hi.1 then (1 : MvPolynomial (Fin m) K)
        else MvPolynomial.X hi.1) G).coeff t =
      G.coeff (∑ h : Fin m, (Finsupp.single (h, (1 : Fin 2) - c h) (t h) +
        Finsupp.single (h, c h) (d h - t h))) := by
  change (dehom (K := K) c G).coeff t = _
  set uStar : (Fin m × Fin 2) →₀ ℕ :=
    ∑ h : Fin m, (Finsupp.single (h, (1 : Fin 2) - c h) (t h) +
      Finsupp.single (h, c h) (d h - t h)) with huStar
  -- The values of `uStar` on the two coordinates of each block.
  have huStar_apply : ∀ (h : Fin m) (j : Fin 2),
      uStar (h,j) = (if (1:Fin 2) - c h = j then t h else 0)
        + (if c h = j then d h - t h else 0) := by
    intro h j
    rw [huStar]
    rw [Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single h]
    · simp only [Finsupp.add_apply, Finsupp.single_apply, Prod.mk.injEq, true_and]
    · intro h' _ hne
      simp [Finsupp.add_apply, Prod.mk.injEq, hne]
    · intro hnot
      simp at hnot
  have hne_sub : ∀ h : Fin m, c h ≠ (1 : Fin 2) - c h := by
    intro h
    generalize hh : c h = ch
    fin_cases ch <;> decide
  have huStar_other : ∀ h : Fin m, uStar (h, (1 : Fin 2) - c h) = t h := by
    intro h
    rw [huStar_apply]
    simp [hne_sub h]
  have huStar_c : ∀ h : Fin m, uStar (h, c h) = d h - t h := by
    intro h
    rw [huStar_apply]
    simp [Ne.symm (hne_sub h)]
  -- Uniqueness: an exponent in the support satisfying `u (h, 1 - c h) = t h` must be `uStar`.
  have key : ∀ u ∈ G.support,
      ((∑ h : Fin m, Finsupp.single h (u (h, (1 : Fin 2) - c h))) = t ↔ u = uStar) := by
    intro u hu
    constructor
    · intro hKu
      have hval : ∀ h : Fin m, u (h, (1 : Fin 2) - c h) = t h := by
        intro h
        have hh := congrArg (fun (f : Fin m →₀ ℕ) => f h) hKu
        rw [finset_sum_single_apply] at hh
        simpa using hh
      have hval_c : ∀ h : Fin m, u (h, c h) = d h - t h := by
        intro h
        have hperm : u (h, c h) + u (h, (1 : Fin 2) - c h) = d h := by
          rw [block_perm, hhom u hu h]
        rw [hval h] at hperm
        omega
      ext a
      rcases a with ⟨h, j⟩
      rcases fin2_eq_or_sub (c h) j with hj | hj
      · rw [hj, hval_c h, huStar_c h]
      · rw [hj, hval h, huStar_other h]
    · intro hu_eq
      subst hu_eq
      ext h
      rw [finset_sum_single_apply]
      simp [huStar_other h]
  -- Expand `G` into monomials and take the `t`-th coefficient.
  have hmap : dehom c G = ∑ u ∈ G.support,
      MvPolynomial.monomial (∑ h : Fin m, Finsupp.single h (u (h, (1 : Fin 2) - c h)))
        (G.coeff u) := by
    conv_lhs => rw [MvPolynomial.as_sum G]
    rw [map_sum]
    exact Finset.sum_congr rfl (fun u _ => dehom_monomial c u (G.coeff u))
  rw [hmap, MvPolynomial.coeff_sum]
  have hstep : ∑ u ∈ G.support, MvPolynomial.coeff t
        (MvPolynomial.monomial (∑ h : Fin m, Finsupp.single h (u (h, (1 : Fin 2) - c h)))
          (G.coeff u))
      = ∑ u ∈ G.support, (if u = uStar then G.coeff u else 0) := by
    apply Finset.sum_congr rfl
    intro u hu
    rw [MvPolynomial.coeff_monomial]
    by_cases h : (∑ h : Fin m, Finsupp.single h (u (h, (1:Fin 2) - c h))) = t
    · rw [if_pos h, if_pos ((key u hu).mp h)]
    · rw [if_neg h, if_neg (fun hh => h ((key u hu).mpr hh))]
  rw [hstep, Finset.sum_ite_eq']
  by_cases h : uStar ∈ G.support
  · simp [h]
  · rw [if_neg h]
    have hzero : G.coeff uStar = 0 := by
      rw [MvPolynomial.mem_support_iff] at h
      exact not_not.mp h
    simp [hzero]

end Commons.Algebra.MvPolynomial