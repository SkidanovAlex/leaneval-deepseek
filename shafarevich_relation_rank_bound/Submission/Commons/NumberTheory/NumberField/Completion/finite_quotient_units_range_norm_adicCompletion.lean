import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.RingTheory.Henselian.valuation_completion_liesOver
import Submission.Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one
import Submission.Commons.RingTheory.Henselian.adicCompletionIntegers_henselianLocalRing
import Submission.Commons.NumberTheory.NumberField.Completion.val_norm_adicCompletion_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.norm_range_of_ramificationIdx_eq_one
import Submission.Commons.NumberTheory.NumberField.Completion.norm_adicCompletionIntegers_mem
import Submission.Commons.NumberTheory.NumberField.Completion.adicCompletionMap_injective
import Submission.Commons.NumberTheory.NumberField.Completion.exists_trace_eq_one_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.exists_norm_uniformizer_mul_unit_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.exists_units_mul_uniformizer_zpow_adicCompletion
import Submission.Commons.NumberTheory.NumberField.Completion.finiteIndex_principalUnits_adicCompletionIntegers

/-!
# Finiteness of the quotient of the local units by the local norm group

Let `L / K` be a finite Galois extension of number fields, `Q` a height one prime of `𝓞 K` and `q`
a height one prime of `𝓞 L` lying over `Q`.  Then the extension of local fields `L_q / K_Q` is
Galois, and the target statement of this file is that the quotient of the units of `K_Q` by the
group of norms from `L_q` is *finite*.

This is the easy half of the norm index theorem of local class field theory (the full theorem,
`#(K_Qˣ ⧸ N L_qˣ) = #Gal(L_q/K_Q)ᵃᵇ`, is local Artin reciprocity): the norm group has finite
index in the units.  The proof given here is the classical one, and is *elementary* in the sense
that it avoids local class field theory altogether:

* the trace `Tr = Tr_{L_q/K_Q}` is surjective, and there is a fixed element `u₀` with `Tr u₀ = 1`
  and bounded valuation; hence for every small `t` one can find `y` with `Tr y = t` and
  `v y ≤ (v t)/2 + O(1)`.
* Consequently the second order expansion `N (1 + y) = 1 + Tr y + O(y²)` of the norm map shows
  that `N` maps the principal units of `L_q` *onto* the principal units `1 + 𝔪^M` of `K_Q` of a
  sufficiently high level `M` (a Newton iteration, the "norm is an open map" argument).
* Since `1 + 𝔪^M` has finite index in the units of the ring of integers of `K_Q`, the norm group
  contains a finite index subgroup of the units.  Together with the fact that the valuation of a
  norm is a multiple of the inertia degree `f`, this gives finiteness of the quotient.
-/

open scoped NumberField WithZero
open IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Commons.NumberTheory.NumberField.Completion

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

theorem val_norm_one_add_sub_one_sub_trace_le_aux
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ y : q.adicCompletion L,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y ≤
          (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) →
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            (Algebra.norm (Q.adicCompletion K) (1 + y) - 1 -
              Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) y)) ≤
        (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y) *
          (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    isGalois_adicCompletion Q q hq
  intro y hy
  have hval : ∀ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (σ y) =
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y :=
    fun σ => val_algEquiv_adicCompletion Q q hq σ y
  have key : algebraMap (Q.adicCompletion K) (q.adicCompletion L)
      (Algebra.norm (Q.adicCompletion K) (1 + y) - 1 -
        Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) y) =
      (∏ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, (1 + σ y)) - 1 -
        ∑ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, σ y := by
    have h1 := Algebra.norm_eq_prod_automorphisms (Q.adicCompletion K) (1 + y)
    have h2 := trace_eq_sum_automorphisms (K := Q.adicCompletion K)
      (L := q.adicCompletion L) (x := y)
    have h3 : (∏ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, σ (1 + y)) =
        ∏ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L, (1 + σ y) :=
      Finset.prod_congr rfl fun σ _ => by rw [map_add, map_one]
    rw [map_sub, map_sub, map_one, h1, h2, h3]
  rw [key]
  have hδ1 : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y ≤ 1 :=
    le_trans hy (by rw [← WithZero.exp_zero]; exact WithZero.exp_le_exp.mpr (by norm_num))
  have ha : ∀ σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (σ y) ≤
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y :=
    fun σ => le_of_eq (hval σ)
  exact prod_one_add_sub_one_sub_sum_le _ Finset.univ _ _ hδ1 (fun σ _ => ha σ)

lemma val_algebraMap_eq_one_of_close_aux
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (k : ℕ) (hk1 : 1 ≤ k) (z w : Q.adicCompletion K) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) z) = 1 →
    Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (z - w)) ≤
      (WithZero.exp (-(k : ℤ)) : WithZero (Multiplicative ℤ)) →
    Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) w) = 1 := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro hz hclose
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    isGalois_adicCompletion Q q hq
  have hexp_lt_one :
      (WithZero.exp (-(k : ℤ)) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hmap_sub : algebraMap (Q.adicCompletion K) (q.adicCompletion L) (z - w) =
      algebraMap (Q.adicCompletion K) (q.adicCompletion L) z -
        algebraMap (Q.adicCompletion K) (q.adicCompletion L) w := map_sub _ _ _
  have hlt : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (z - w)) <
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) z) := by
    rw [hz]
    exact lt_of_le_of_lt hclose hexp_lt_one
  rcases lt_trichotomy (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L) z))
    (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L) w)) with h | h | h
  · have hh := Valuation.map_sub_eq_of_lt_right
      (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)))
      (x := algebraMap (Q.adicCompletion K) (q.adicCompletion L) z)
      (y := algebraMap (Q.adicCompletion K) (q.adicCompletion L) w) h
    rw [hmap_sub, hh] at hlt
    exact absurd (h.trans hlt) (lt_irrefl _)
  · exact h.symm.trans hz
  · have hh := Valuation.map_sub_eq_of_lt_left
      (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)))
      (x := algebraMap (Q.adicCompletion K) (q.adicCompletion L) z)
      (y := algebraMap (Q.adicCompletion K) (q.adicCompletion L) w) h
    rw [hmap_sub, hh] at hlt
    exact absurd hlt (lt_irrefl _)

/-- One Newton step for the norm map: given an integral approximation `u` with
`v (z - N u) ≤ exp (-k)`, one can multiply `u` by an integral element `a` so that the
error drops to `exp (-(k+1))`. -/
lemma norm_step_aux
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (D : ℕ) (u₀ : q.adicCompletion L) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) u₀ = 1 →
    Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) u₀ ≤
      (WithZero.exp (D : ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ (k : ℕ) (z : Q.adicCompletion K) (u : q.adicCompletionIntegers L),
      2 * D + 1 ≤ k →
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L) z) = 1 →
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
          (z - Algebra.norm (Q.adicCompletion K) (u : q.adicCompletion L))) ≤
        (WithZero.exp (-(k : ℤ)) : WithZero (Multiplicative ℤ)) →
      ∃ a : q.adicCompletionIntegers L,
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            (z - Algebra.norm (Q.adicCompletion K)
              ((u * a : q.adicCompletionIntegers L) : q.adicCompletion L))) ≤
          (WithZero.exp (-((k + 1 : ℕ) : ℤ)) : WithZero (Multiplicative ℤ)) ∧
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (((u * a : q.adicCompletionIntegers L) : q.adicCompletion L) -
            (u : q.adicCompletion L)) ≤
          (WithZero.exp (((D : ℤ) - (k : ℤ))) : WithZero (Multiplicative ℤ)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro hu₀ hu₀D k z u hk hz hderr
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    isGalois_adicCompletion Q q hq
  have hexp_lt_one :
      (WithZero.exp (-(k : ℤ)) : WithZero (Multiplicative ℤ)) < 1 := by
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  -- The value of `Nu := N u`
  set Nu : Q.adicCompletion K := Algebra.norm (Q.adicCompletion K) (u : q.adicCompletion L)
    with hNudef
  have hNu1 : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L) Nu) = 1 :=
    val_algebraMap_eq_one_of_close_aux Q q hq k (by omega) z Nu hz hderr
  have hNu_ne : Nu ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hNu1
    exact zero_ne_one (by rw [← hNu1, map_zero])
  -- the correction `t = z / Nu - 1`
  set t : Q.adicCompletion K := z / Nu - 1 with htdef
  have htval : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L) t) ≤
      (WithZero.exp (-(k : ℤ)) : WithZero (Multiplicative ℤ)) := by
    have ht_eq : t = (z - Nu) / Nu := by rw [htdef]; field_simp
    rw [ht_eq, map_div₀, Valuation.map_div, hNu1, div_one]
    exact hderr
  -- the correction element `y = t • u₀`
  set y : q.adicCompletion L := algebraMap (Q.adicCompletion K) (q.adicCompletion L) t * u₀
    with hydef
  have hyval : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y ≤
      (WithZero.exp (((D : ℤ) - (k : ℤ))) : WithZero (Multiplicative ℤ)) := by
    rw [hydef, map_mul]
    calc Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (algebraMap (Q.adicCompletion K) (q.adicCompletion L) t) *
          Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) u₀
        ≤ (WithZero.exp (-(k : ℤ)) : WithZero (Multiplicative ℤ)) *
            (WithZero.exp (D : ℤ) : WithZero (Multiplicative ℤ)) := mul_le_mul' htval hu₀D
      _ = (WithZero.exp (((D : ℤ) - (k : ℤ))) : WithZero (Multiplicative ℤ)) := by
          rw [← WithZero.exp_add]
          congr 1
          ring
  have hy_lt_one : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y < 1 := by
    refine lt_of_le_of_lt hyval ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have h1y_val : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (1 + y) ≤ 1 :=
    Valuation.map_add_le _ (le_of_eq (Valuation.map_one _)) (le_of_lt hy_lt_one)
  set a : q.adicCompletionIntegers L :=
    ⟨1 + y, (mem_adicCompletionIntegers (R := 𝓞 L) L q).mpr h1y_val⟩ with hadef
  have ha_coe : ((a : q.adicCompletionIntegers L) : q.adicCompletion L) = 1 + y := rfl
  -- trace of the correction
  have hTry : Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) y = t := by
    have hsmul : y = t • u₀ := by rw [hydef, Algebra.smul_def]
    rw [hsmul, map_smul, smul_eq_mul, hu₀, mul_one]
  -- the second order error
  set err : Q.adicCompletion K := Algebra.norm (Q.adicCompletion K) (1 + y) - 1 -
    Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) y with herrdef
  have herr_val : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L) err) ≤
      (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y) *
        (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y) :=
    val_norm_one_add_sub_one_sub_trace_le_aux Q q hq y
      (Commons.RingTheory.Henselian.lt_one_le_exp_neg_one hy_lt_one)
  have herr_bound : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L) err) ≤
      (WithZero.exp (2 * ((D : ℤ) - (k : ℤ))) : WithZero (Multiplicative ℤ)) := by
    calc Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L) err)
        ≤ (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y) *
            (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y) := herr_val
      _ ≤ (WithZero.exp ((D : ℤ) - (k : ℤ)) : WithZero (Multiplicative ℤ)) *
            (WithZero.exp ((D : ℤ) - (k : ℤ)) : WithZero (Multiplicative ℤ)) :=
          mul_le_mul' hyval hyval
      _ = (WithZero.exp (2 * ((D : ℤ) - (k : ℤ))) : WithZero (Multiplicative ℤ)) := by
          rw [← WithZero.exp_add]
          congr 1
          ring
  -- the algebra
  have hN1y_eq : Algebra.norm (Q.adicCompletion K) (1 + y) = err + 1 + t := by
    rw [herrdef, hTry]
    ring
  have ht_mul : Nu * t = z - Nu := by
    rw [htdef]
    field_simp
  have hkey : z - Nu * Algebra.norm (Q.adicCompletion K) (1 + y) = -(Nu * err) := by
    rw [hN1y_eq, mul_add, mul_add, mul_one, ht_mul]
    ring
  have hcoe : ((u * a : q.adicCompletionIntegers L) : q.adicCompletion L) =
      (u : q.adicCompletion L) * (a : q.adicCompletion L) := by push_cast; ring
  have hnorm_eq : Algebra.norm (Q.adicCompletion K)
      ((u * a : q.adicCompletionIntegers L) : q.adicCompletion L)
      = Nu * Algebra.norm (Q.adicCompletion K) (1 + y) := by
    rw [hcoe, map_mul, ← hNudef, ha_coe]
  refine ⟨a, ?_, ?_⟩
  · rw [hnorm_eq, hkey, map_neg, Valuation.map_neg, map_mul, Valuation.map_mul, hNu1, one_mul]
    exact herr_bound.trans (WithZero.exp_le_exp.mpr (by omega))
  · rw [hcoe]
    rw [show (u : q.adicCompletion L) * (a : q.adicCompletion L) - (u : q.adicCompletion L)
        = (u : q.adicCompletion L) * ((a : q.adicCompletion L) - 1) from by ring]
    rw [ha_coe]
    rw [show (1 + y : q.adicCompletion L) - 1 = y from by ring]
    rw [map_mul]
    calc Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
            (u : q.adicCompletion L) *
          Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) y
        ≤ 1 * (WithZero.exp ((D : ℤ) - (k : ℤ)) : WithZero (Multiplicative ℤ)) :=
          mul_le_mul' u.2 hyval
      _ = (WithZero.exp ((D : ℤ) - (k : ℤ)) : WithZero (Multiplicative ℤ)) := one_mul _

theorem exists_norm_eq_of_val_sub_one_le_aux
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal)
    (D : ℕ) (u₀ : q.adicCompletion L) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Algebra.trace (Q.adicCompletion K) (q.adicCompletion L) u₀ = 1 →
    Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) u₀ ≤
      (WithZero.exp (D : ℤ) : WithZero (Multiplicative ℤ)) →
    ∀ z : Q.adicCompletion K,
      Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (z - 1) ≤
        (WithZero.exp (-((2 * D + 2 : ℕ) : ℤ)) : WithZero (Multiplicative ℤ)) →
      ∃ x : q.adicCompletion L, Algebra.norm (Q.adicCompletion K) x = z := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro hu₀ hu₀D z hz
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    isGalois_adicCompletion Q q hq
  set M : ℕ := 2 * D + 2 with hMdef
  -- ### basic facts about `z`
  have hz1lt : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
      (z - 1) < 1 := by
    refine lt_of_le_of_lt hz ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hzK : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) z = 1 := by
    have h := Valuation.map_add_eq_of_lt_left
      (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)))
      (x := (1 : Q.adicCompletion K)) (y := z - 1) (by rw [map_one]; exact hz1lt)
    rw [map_one, show (1 : Q.adicCompletion K) + (z - 1) = z by ring] at h
    exact h
  have hzL : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L) z) = 1 := by
    rw [RingHom.algebraMap_toAlgebra, val_adicCompletionMap_eq_pow Q q hq z, hzK, one_pow]
  have hz1L : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L) (z - 1)) ≤
      (WithZero.exp (-(M : ℤ)) : WithZero (Multiplicative ℤ)) := by
    have he : 1 ≤ q.asIdeal.ramificationIdx (𝓞 K) :=
      Ideal.ramificationIdx_pos q.asIdeal (𝓞 K)
    rw [RingHom.algebraMap_toAlgebra, val_adicCompletionMap_eq_pow Q q hq (z - 1), hMdef]
    calc (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ)) (z - 1)) ^
          (q.asIdeal.ramificationIdx (𝓞 K))
        ≤ ((WithZero.exp (-((2 * D + 2 : ℕ) : ℤ)) : WithZero (Multiplicative ℤ))) ^
            (q.asIdeal.ramificationIdx (𝓞 K)) := pow_le_pow_left' hz _
      _ = (WithZero.exp (-(((2 * D + 2 : ℕ) : ℤ)) *
            (q.asIdeal.ramificationIdx (𝓞 K) : ℤ)) : WithZero (Multiplicative ℤ)) := by
          rw [← WithZero.exp_nsmul]
          congr 1
          push_cast
          ring
      _ ≤ (WithZero.exp (-(((2 * D + 2 : ℕ) : ℤ))) : WithZero (Multiplicative ℤ)) := by
          apply WithZero.exp_le_exp.mpr
          have hle : (((2 * D + 2 : ℕ) : ℤ)) ≤
              (((2 * D + 2 : ℕ) : ℤ)) * (q.asIdeal.ramificationIdx (𝓞 K) : ℤ) :=
            le_mul_of_one_le_right (by positivity) (by exact_mod_cast he)
          linarith
  -- ### the recursive construction
  let P : ℕ → q.adicCompletionIntegers L × q.adicCompletionIntegers L → Prop := fun n p =>
    Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
          (z - Algebra.norm (Q.adicCompletion K) (p.1 : q.adicCompletion L))) ≤
        (WithZero.exp (-((M + n : ℕ) : ℤ)) : WithZero (Multiplicative ℤ)) ∧
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        ((p.1 : q.adicCompletion L) - (p.2 : q.adicCompletion L)) ≤
        (WithZero.exp (((D : ℤ) - (M : ℤ) - (n : ℤ) + 1)) : WithZero (Multiplicative ℤ))
  have hbase : P 0 ((1, 1) : q.adicCompletionIntegers L × q.adicCompletionIntegers L) := by
    constructor
    · have h1 : Algebra.norm (Q.adicCompletion K)
          (((1 : q.adicCompletionIntegers L) : q.adicCompletion L)) = 1 := by
        rw [show ((1 : q.adicCompletionIntegers L) : q.adicCompletion L) = 1 by rfl, map_one]
      rw [h1]
      simpa using hz1L
    · have h0 : (((1, 1) : q.adicCompletionIntegers L × q.adicCompletionIntegers L).1 :
            q.adicCompletion L) -
          (((1, 1) : q.adicCompletionIntegers L × q.adicCompletionIntegers L).2 :
            q.adicCompletion L) = 0 := by simp
      rw [h0, Valuation.map_zero]
      exact zero_le
  have hstep : ∀ (n : ℕ) (p : q.adicCompletionIntegers L × q.adicCompletionIntegers L),
      P n p → ∃ p' : q.adicCompletionIntegers L × q.adicCompletionIntegers L,
        p'.2 = p.1 ∧ P (n + 1) p' := by
    intro n p hp
    obtain ⟨hp1, hp2⟩ := hp
    have hk : 2 * D + 1 ≤ M + n := by omega
    obtain ⟨a, haerr, hadiff⟩ :=
      norm_step_aux Q q hq D u₀ hu₀ hu₀D (M + n) z p.1 hk hzL hp1
    refine ⟨(p.1 * a, p.1), rfl, ?_, ?_⟩
    · refine haerr.trans (WithZero.exp_le_exp.mpr ?_)
      push_cast
      omega
    · refine hadiff.trans (WithZero.exp_le_exp.mpr ?_)
      push_cast
      omega
  let motive : ℕ → Type _ := fun n =>
    {p : q.adicCompletionIntegers L × q.adicCompletionIntegers L // P n p}
  let stepF : (n : ℕ) → motive n → motive (n + 1) := fun n p =>
    ⟨Classical.choose (hstep n p.1 p.2), (Classical.choose_spec (hstep n p.1 p.2)).2⟩
  let g : (n : ℕ) → motive n := Nat.rec ⟨(1, 1), hbase⟩ stepF
  let u : ℕ → q.adicCompletionIntegers L := fun n => (g n).1.1
  have hu_norm : ∀ n : ℕ,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
          (z - Algebra.norm (Q.adicCompletion K) ((u n) : q.adicCompletion L))) ≤
        (WithZero.exp (-((M + n : ℕ) : ℤ)) : WithZero (Multiplicative ℤ)) :=
    fun n => (g n).2.1
  have hg_prev : ∀ n : ℕ, (g (n + 1)).1.2 = u n :=
    fun n => (Classical.choose_spec (hstep n (g n).1 (g n).2)).1
  have hu_diff : ∀ n : ℕ,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (((u (n + 1)) : q.adicCompletion L) - ((u n) : q.adicCompletion L)) ≤
        (WithZero.exp (((D : ℤ) - (M : ℤ) - (n : ℤ))) : WithZero (Multiplicative ℤ)) := by
    intro n
    have h := (g (n + 1)).2.2
    rw [hg_prev n] at h
    refine h.trans (WithZero.exp_le_exp.mpr ?_)
    push_cast
    omega
  have hDleM : (D : ℤ) ≤ (M : ℤ) := by
    rw [hMdef]; push_cast; omega
  have hu_cauchy : ∀ n m : ℕ, m ≤ n →
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (((u n) : q.adicCompletion L) - ((u m) : q.adicCompletion L)) ≤
        (WithZero.exp (-(m : ℤ)) : WithZero (Multiplicative ℤ)) := by
    intro n
    induction n with
    | zero =>
      intro m hm
      obtain rfl : m = 0 := Nat.le_zero.mp hm
      simp
    | succ n ih =>
      intro m hm
      rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · simp
      · have hmn : m ≤ n := Nat.lt_succ_iff.mp hlt
        have h1 := ih m hmn
        have h2 := hu_diff n
        rw [show ((u (n + 1)) : q.adicCompletion L) - ((u m) : q.adicCompletion L)
            = (((u (n + 1)) : q.adicCompletion L) - ((u n) : q.adicCompletion L)) +
              (((u n) : q.adicCompletion L) - ((u m) : q.adicCompletion L)) from by ring]
        refine Valuation.map_add_le _ (le_trans h2 ?_) h1
        apply WithZero.exp_le_exp.mpr
        omega
  -- ### the limit
  have hmem_iff : ∀ (x : q.adicCompletionIntegers L) (m : ℕ),
      x ∈ (IsLocalRing.maximalIdeal (q.adicCompletionIntegers L)) ^ m ↔
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (x : q.adicCompletion L) ≤ (WithZero.exp (-(m : ℤ)) : WithZero (Multiplicative ℤ)) := by
    intro x m
    have hcoe : ∀ y : q.adicCompletionIntegers L,
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap (q.adicCompletionIntegers L) (q.adicCompletion L) y) =
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (y : q.adicCompletion L) := fun y => rfl
    rw [Commons.RingTheory.Henselian.mem_pow_maximalIdeal_iff, hcoe, hcoe,
      Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one q]
    have hexp : ((WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ))) ^ m =
        (WithZero.exp (-(m : ℤ)) : WithZero (Multiplicative ℤ)) := by
      rw [← WithZero.exp_nsmul]
      congr 1
      simp
    rw [hexp]
  obtain ⟨ell, hL⟩ := (Commons.RingTheory.Henselian.isPrecomplete_adicCompletionIntegers
    (R := 𝓞 L) (K := L) q).prec' (fun n => u n) (by
      intro m n hmn
      rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, hmem_iff]
      rw [show (((u m - u n : q.adicCompletionIntegers L)) : q.adicCompletion L) =
          -(((u n) : q.adicCompletion L) - ((u m) : q.adicCompletion L)) from by push_cast; ring,
        Valuation.map_neg]
      exact hu_cauchy n m hmn)
  have hLdiff : ∀ n : ℕ,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (((u n) : q.adicCompletion L) - (ell : q.adicCompletion L)) ≤
        (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
    intro n
    have h := hL n
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, hmem_iff] at h
    rw [show (((u n - ell : q.adicCompletionIntegers L)) : q.adicCompletion L) =
        ((u n) : q.adicCompletion L) - (ell : q.adicCompletion L) from by push_cast; ring] at h
    exact h
  -- ### the values of the approximations are `1`
  have hu1 : ∀ n : ℕ, Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      ((u n) : q.adicCompletion L) = 1 := by
    intro n
    have hN1 : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
          (Algebra.norm (Q.adicCompletion K) ((u n) : q.adicCompletion L))) = 1 :=
      val_algebraMap_eq_one_of_close_aux Q q hq (M + n) (by omega) z _ hzL (hu_norm n)
    have hpow := val_norm_adicCompletion_eq_pow Q q hq ((u n) : q.adicCompletion L)
    rw [RingHom.algebraMap_toAlgebra] at hpow
    have hpow1 : (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
        ((u n) : q.adicCompletion L)) ^
        Module.finrank (Q.adicCompletion K) (q.adicCompletion L) = 1 := by
      rw [← hpow]
      exact hN1
    rcases lt_trichotomy (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      ((u n) : q.adicCompletion L)) 1 with h | h | h
    · exfalso
      have hlt : (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          ((u n) : q.adicCompletion L)) ^
          Module.finrank (Q.adicCompletion K) (q.adicCompletion L) < 1 :=
        pow_lt_one₀ zero_le h (Module.finrank_pos (R := Q.adicCompletion K)
          (M := q.adicCompletion L)).ne'
      rw [hpow1] at hlt
      exact lt_irrefl 1 hlt
    · exact h
    · exact absurd h (not_lt_of_ge (u n).2)
  -- ### the final estimate
  refine ⟨(ell : q.adicCompletion L), ?_⟩
  have key : ∀ n : ℕ, Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
      (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
        (z - Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L))) ≤
      (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst hn0
      have hN1' : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            (Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L))) ≤ 1 := by
        have hmem : Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L) ∈
            Q.adicCompletionIntegers K := norm_adicCompletionIntegers_mem Q q hq ell
        have hvK : Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
            (Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L)) ≤ 1 :=
          (mem_adicCompletionIntegers (R := 𝓞 K) K Q).mp hmem
        calc Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
              (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
                (Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L)))
            = (Valued.v (R := Q.adicCompletion K) (Γ₀ := WithZero (Multiplicative ℤ))
                (Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L))) ^
                  (q.asIdeal.ramificationIdx (𝓞 K)) := by
              rw [RingHom.algebraMap_toAlgebra, val_adicCompletionMap_eq_pow Q q hq]
          _ ≤ 1 ^ (q.asIdeal.ramificationIdx (𝓞 K)) := pow_le_pow_left' hvK _
          _ = 1 := one_pow _
      rw [map_sub]
      simpa using Valuation.map_sub_le
        (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)))
        (le_of_eq hzL) hN1'
    · -- `n ≥ 1`
      have hun1 : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          ((u n) : q.adicCompletion L) = 1 := hu1 n
      have hδbound : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (((ell : q.adicCompletion L) - ((u n) : q.adicCompletion L)) /
            ((u n) : q.adicCompletion L)) ≤
          (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
        rw [Valuation.map_div, hun1, div_one]
        rw [Valuation.map_sub_swap]
        exact hLdiff n
      have hδmem : (((ell : q.adicCompletion L) - ((u n) : q.adicCompletion L)) /
            ((u n) : q.adicCompletion L)) ∈ (q.adicCompletionIntegers L : Set (q.adicCompletion L)) := by
        apply (mem_adicCompletionIntegers (R := 𝓞 L) L q).mpr
        exact le_trans hδbound (WithZero.exp_le_exp.mpr (by omega))
      set δu : q.adicCompletionIntegers L :=
        ⟨((ell : q.adicCompletion L) - ((u n) : q.adicCompletion L)) /
            ((u n) : q.adicCompletion L), hδmem⟩ with hδudef
      have hδu_coe : ((δu : q.adicCompletionIntegers L) : q.adicCompletion L) =
          ((ell : q.adicCompletion L) - ((u n) : q.adicCompletion L)) /
            ((u n) : q.adicCompletion L) := rfl
      have hδu_bound : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          ((δu : q.adicCompletionIntegers L) : q.adicCompletion L) ≤
          (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
        rw [hδu_coe]
        exact hδbound
      have hun0 : ((u n : q.adicCompletionIntegers L) : q.adicCompletion L) ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hun1
        exact zero_ne_one hun1
      have hLun : (ell : q.adicCompletion L) =
          ((u n : q.adicCompletionIntegers L) : q.adicCompletion L) *
            ((1 + δu : q.adicCompletionIntegers L) : q.adicCompletion L) := by
        rw [show ((1 + δu : q.adicCompletionIntegers L) : q.adicCompletion L) =
            1 + ((δu : q.adicCompletionIntegers L) : q.adicCompletion L) from by push_cast; ring]
        rw [hδu_coe]
        field_simp
        ring
      have hδu_lt : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          ((δu : q.adicCompletionIntegers L) : q.adicCompletion L) ≤
          (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) :=
        le_trans hδu_bound (WithZero.exp_le_exp.mpr (by omega))
      have htr : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            (Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
              ((δu : q.adicCompletionIntegers L) : q.adicCompletion L))) ≤
          (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
        rw [trace_eq_sum_automorphisms (K := Q.adicCompletion K)
          (x := ((δu : q.adicCompletionIntegers L) : q.adicCompletion L))]
        refine Valuation.map_sum_le _ (fun σ _ => ?_)
        rw [val_algEquiv_adicCompletion Q q hq σ]
        exact hδu_bound
      have herr : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            (Algebra.norm (Q.adicCompletion K)
                (1 + ((δu : q.adicCompletionIntegers L) : q.adicCompletion L)) - 1 -
              Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
                ((δu : q.adicCompletionIntegers L) : q.adicCompletion L))) ≤
          (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
        calc Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
              (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
                (Algebra.norm (Q.adicCompletion K)
                    (1 + ((δu : q.adicCompletionIntegers L) : q.adicCompletion L)) - 1 -
                  Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
                    ((δu : q.adicCompletionIntegers L) : q.adicCompletion L)))
            ≤ (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
                ((δu : q.adicCompletionIntegers L) : q.adicCompletion L)) *
                (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
                  ((δu : q.adicCompletionIntegers L) : q.adicCompletion L)) :=
              val_norm_one_add_sub_one_sub_trace_le_aux Q q hq _ hδu_lt
          _ ≤ (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) *
                (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) :=
              mul_le_mul' hδu_bound hδu_bound
          _ = (WithZero.exp (-((2 * n : ℕ) : ℤ)) : WithZero (Multiplicative ℤ)) := by
              rw [← WithZero.exp_add]
              congr 1
              push_cast
              ring
          _ ≤ (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) :=
              WithZero.exp_le_exp.mpr (by push_cast; omega)
      have hsmall : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            (Algebra.norm (Q.adicCompletion K)
              ((1 + δu : q.adicCompletionIntegers L) : q.adicCompletion L) - 1)) ≤
          (WithZero.exp (-(n : ℤ)) : WithZero (Multiplicative ℤ)) := by
        rw [show ((1 + δu : q.adicCompletionIntegers L) : q.adicCompletion L) =
            1 + ((δu : q.adicCompletionIntegers L) : q.adicCompletion L) from by push_cast; ring]
        rw [show Algebra.norm (Q.adicCompletion K)
              (1 + ((δu : q.adicCompletionIntegers L) : q.adicCompletion L)) - 1 =
            (Algebra.norm (Q.adicCompletion K)
                (1 + ((δu : q.adicCompletionIntegers L) : q.adicCompletion L)) - 1 -
              Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
                ((δu : q.adicCompletionIntegers L) : q.adicCompletion L)) +
              Algebra.trace (Q.adicCompletion K) (q.adicCompletion L)
                ((δu : q.adicCompletionIntegers L) : q.adicCompletion L) from by ring]
        rw [RingHom.map_add]
        exact Valuation.map_add_le _ herr htr
      have hNu1n : Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            (Algebra.norm (Q.adicCompletion K)
              ((u n : q.adicCompletionIntegers L) : q.adicCompletion L))) = 1 := by
        rw [val_norm_adicCompletion_eq_pow Q q hq, hun1, one_pow]
      have hNL : Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L) =
          Algebra.norm (Q.adicCompletion K) ((u n : q.adicCompletionIntegers L) : q.adicCompletion L) *
            Algebra.norm (Q.adicCompletion K)
              ((1 + δu : q.adicCompletionIntegers L) : q.adicCompletion L) := by
        rw [hLun, map_mul]
      rw [hNL, RingHom.map_sub, RingHom.map_mul]
      rw [show (algebraMap (Q.adicCompletion K) (q.adicCompletion L) z -
            algebraMap (Q.adicCompletion K) (q.adicCompletion L)
                (Algebra.norm (Q.adicCompletion K)
                  ((u n : q.adicCompletionIntegers L) : q.adicCompletion L)) *
              algebraMap (Q.adicCompletion K) (q.adicCompletion L)
                (Algebra.norm (Q.adicCompletion K)
                  ((1 + δu : q.adicCompletionIntegers L) : q.adicCompletion L))) =
          algebraMap (Q.adicCompletion K) (q.adicCompletion L)
              (z - Algebra.norm (Q.adicCompletion K)
                ((u n : q.adicCompletionIntegers L) : q.adicCompletion L)) +
            algebraMap (Q.adicCompletion K) (q.adicCompletion L)
              (Algebra.norm (Q.adicCompletion K)
                ((u n : q.adicCompletionIntegers L) : q.adicCompletion L)) *
              (1 - algebraMap (Q.adicCompletion K) (q.adicCompletion L)
                (Algebra.norm (Q.adicCompletion K)
                  ((1 + δu : q.adicCompletionIntegers L) : q.adicCompletion L))) from by
        rw [show algebraMap (Q.adicCompletion K) (q.adicCompletion L)
              (z - Algebra.norm (Q.adicCompletion K)
                ((u n : q.adicCompletionIntegers L) : q.adicCompletion L)) =
            algebraMap (Q.adicCompletion K) (q.adicCompletion L) z -
              algebraMap (Q.adicCompletion K) (q.adicCompletion L)
                (Algebra.norm (Q.adicCompletion K)
                  ((u n : q.adicCompletionIntegers L) : q.adicCompletion L)) from
          RingHom.map_sub _ _ _]
        ring]
      refine Valuation.map_add_le _ ?_ ?_
      · exact (hu_norm n).trans (WithZero.exp_le_exp.mpr (by omega))
      · rw [Valuation.map_mul, hNu1n, one_mul]
        rw [show (1 : q.adicCompletion L) - algebraMap (Q.adicCompletion K) (q.adicCompletion L)
              (Algebra.norm (Q.adicCompletion K)
                ((1 + δu : q.adicCompletionIntegers L) : q.adicCompletion L)) =
            -(algebraMap (Q.adicCompletion K) (q.adicCompletion L)
              (Algebra.norm (Q.adicCompletion K)
                ((1 + δu : q.adicCompletionIntegers L) : q.adicCompletion L) - 1)) from by
          rw [map_sub, map_one]
          ring]
        rw [Valuation.map_neg]
        exact hsmall
  have hz1 : algebraMap (Q.adicCompletion K) (q.adicCompletion L)
      (z - Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L)) = 0 :=
    eq_zero_of_forall_val_le_exp_neg _ key
  have hsub : z - Algebra.norm (Q.adicCompletion K) (ell : q.adicCompletion L) = 0 := by
    apply adicCompletionMap_injective Q q hq
    simpa [RingHom.algebraMap_toAlgebra] using hz1
  exact (sub_eq_zero.mp hsub).symm

lemma finiteIndex_units_inf_range_norm_aux
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) (C : ℕ) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    (∀ z : Q.adicCompletion K,
      Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) (z - 1) ≤
        (WithZero.exp (-(C : ℤ)) : Zstar0) →
      ∃ x : q.adicCompletion L, Algebra.norm (Q.adicCompletion K) x = z) →
    (((Units.map ((algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) :
        (Q.adicCompletionIntegers K) →* (Q.adicCompletion K)))).range ⊓
      MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
        q.adicCompletion L →* Q.adicCompletion K))).subgroupOf
      (Units.map ((algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) :
        (Q.adicCompletionIntegers K) →* (Q.adicCompletion K)))).range).FiniteIndex := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  intro hopen
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) := hfd
  let f : (Q.adicCompletionIntegers K)ˣ →* (Q.adicCompletion K)ˣ :=
    Units.map ((algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) :
      (Q.adicCompletionIntegers K) →* (Q.adicCompletion K)))
  let H : Subgroup (Q.adicCompletion K)ˣ :=
    MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
      q.adicCompletion L →* Q.adicCompletion K))
  obtain ⟨U, hU, hUfi⟩ := finiteIndex_principalUnits_adicCompletionIntegers Q C
  have hUle : U ≤ ((f.range ⊓ H).subgroupOf f.range).comap
      (f.codRestrict f.range (fun x => ⟨x, rfl⟩)) := by
    intro u hu
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    constructor
    · exact ⟨u, rfl⟩
    · -- `f u` is a norm
      have hmem : ((u : Q.adicCompletionIntegers K) - 1) ∈
          (IsLocalRing.maximalIdeal (Q.adicCompletionIntegers K)) ^ C := (hU u).mp hu
      have hcoe : ∀ y : Q.adicCompletionIntegers K,
          Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
            (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) y) =
          Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0) (y : Q.adicCompletion K) :=
        fun y => rfl
      have hval : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
          (((u : Q.adicCompletionIntegers K) : Q.adicCompletion K) - 1) ≤
          (WithZero.exp (-(C : ℤ)) : Zstar0) := by
        rw [Commons.RingTheory.Henselian.mem_pow_maximalIdeal_iff, hcoe, hcoe,
          Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one Q] at hmem
        have hC : (WithZero.exp (-1 : ℤ) : Zstar0) ^ C =
            (WithZero.exp (-(C : ℤ)) : Zstar0) := by
          rw [show (-(C : ℤ)) = C • (-1 : ℤ) by simp, ← WithZero.exp_nsmul]
        rw [hC] at hmem
        exact hmem
      obtain ⟨y, hyu⟩ := hopen ((u : Q.adicCompletionIntegers K) : Q.adicCompletion K) hval
      have hyne : y ≠ 0 := by
        intro h0
        rw [h0, Algebra.norm_zero] at hyu
        exact Units.ne_zero u (Subtype.coe_injective hyu.symm)
      have hmap : Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K) (Units.mk0 y hyne) = f u := by
        apply Units.ext
        rw [Units.coe_map, Units.val_mk0]
        exact hyu
      exact ⟨Units.mk0 y hyne, hmap⟩
  have hf'surj : Function.Surjective (f.codRestrict f.range (fun x => ⟨x, rfl⟩)) := by
    rintro ⟨p, hp⟩
    obtain ⟨x, rfl⟩ := hp
    exact ⟨x, rfl⟩
  rw [Subgroup.finiteIndex_iff]
  rw [← Subgroup.index_comap_of_surjective (H := (f.range ⊓ H).subgroupOf f.range)
    (f := f.codRestrict f.range (fun x => ⟨x, rfl⟩)) hf'surj]
  exact ne_zero_of_dvd_ne_zero hUfi.index_ne_zero (Subgroup.index_dvd_of_le hUle)

private lemma inv_mul_comm_mul_mul_self {G : Type*} [CommGroup G] (x a b : G) :
    x⁻¹ * (a * (b * x)) = a * b := by
  rw [mul_comm x⁻¹ (a * (b * x)), mul_assoc, mul_assoc, mul_inv_cancel, mul_one]

/-- Finiteness of the index of `H` in a commutative group, given generators `P` and `w` such
that `w ^ f ∈ P ⊔ H` and `P ∩ H` has finite index in `P`. -/
theorem finiteIndex_of_zpow_generators_aux {G : Type*} [CommGroup G] (H P : Subgroup G) (w : G)
    (f : ℕ) (hf : 0 < f)
    (hgen : ∀ g : G, ∃ p ∈ P, ∃ m : ℤ, g = p * w ^ m)
    (hw : w ^ f ∈ P ⊔ H)
    (hfin : ((P ⊓ H).subgroupOf P).FiniteIndex) : H.FiniteIndex := by
  have hFpos : (0 : ℤ) < (f : ℤ) := by exact_mod_cast hf
  have hwz : w ^ (f : ℤ) ∈ P ⊔ H := by rwa [zpow_natCast]
  let W : Subgroup G := P ⊔ H
  have hWW : P ⊔ H = W := rfl
  have hWfin : W.FiniteIndex := by
    have hsurj : Function.Surjective
        (fun r : Fin f => QuotientGroup.mk (w ^ ((r : ℕ) : ℤ)) : Fin f → G ⧸ W) := by
      intro x
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨p, hp, m, hm⟩ := hgen g
      have hrmem : (0 : ℤ) ≤ m % (f : ℤ) := Int.emod_nonneg m hFpos.ne'
      have hrlt : m % (f : ℤ) < (f : ℤ) := Int.emod_lt_of_pos m hFpos
      refine ⟨⟨(m % (f : ℤ)).toNat, by omega⟩, ?_⟩
      rw [QuotientGroup.eq, hm, Int.toNat_of_nonneg hrmem]
      have hsplit : w ^ m = (w ^ (f : ℤ)) ^ (m / (f : ℤ)) * w ^ (m % (f : ℤ)) := by
        rw [← zpow_mul, ← zpow_add]
        congr 1
        have := Int.mul_ediv_add_emod m (f : ℤ)
        linarith
      rw [hsplit, inv_mul_comm_mul_mul_self]
      exact Subgroup.mul_mem _ (le_sup_left (a := P) (b := H) hp)
        (Subgroup.zpow_mem _ hwz _)
    haveI : Finite (G ⧸ W) := Finite.of_surjective _ hsurj
    exact Subgroup.finiteIndex_of_finite_quotient
  have hHW : (H.subgroupOf W).FiniteIndex := by
    have hker : (P ⊓ H).subgroupOf P ≤ ((QuotientGroup.mk' (H.subgroupOf W)).comp
        (Subgroup.inclusion (le_sup_left : P ≤ W))).ker := by
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
      exact hx.2
    let φ : (↥P ⧸ ((P ⊓ H).subgroupOf P)) →* (↥W ⧸ (H.subgroupOf W)) :=
      QuotientGroup.lift ((P ⊓ H).subgroupOf P)
        ((QuotientGroup.mk' (H.subgroupOf W)).comp (Subgroup.inclusion (le_sup_left : P ≤ W))) hker
    have hφsurj : Function.Surjective φ := by
      intro y
      obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨p, hp, h, hh, hph⟩ := Subgroup.mem_sup.mp (show (w' : G) ∈ P ⊔ H from w'.2)
      refine ⟨QuotientGroup.mk (⟨p, hp⟩ : ↥P), ?_⟩
      show QuotientGroup.mk' (H.subgroupOf W)
          (Subgroup.inclusion (le_sup_left : P ≤ W) (⟨p, hp⟩ : ↥P)) =
        QuotientGroup.mk' (H.subgroupOf W) w'
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      push_cast
      rw [Subgroup.coe_inclusion]
      rw [show (w' : G) = p * h from hph.symm]
      rw [show p⁻¹ * (p * h) = h from by group]
      exact hh
    haveI : Finite (↥W ⧸ (H.subgroupOf W)) := Finite.of_surjective _ hφsurj
    exact Subgroup.finiteIndex_of_finite_quotient
  rw [Subgroup.finiteIndex_iff]
  have hrel : H.relIndex W ≠ 0 := Subgroup.finiteIndex_iff.mp hHW
  rw [← Subgroup.relIndex_mul_index (le_sup_right : H ≤ W)]
  exact mul_ne_zero hrel hWfin.index_ne_zero

theorem finite_quotient_units_range_norm_adicCompletion {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    Finite ((Q.adicCompletion K)ˣ ⧸
      MonoidHom.range (Units.map (Algebra.norm (Q.adicCompletion K) :
        q.adicCompletion L →* Q.adicCompletion K))) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfd : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) := hfd
  -- the norm is surjective on a principal unit group
  obtain ⟨D, u₀, hu₀, hu₀D⟩ := exists_trace_eq_one_adicCompletion Q q hq
  have hopen := exists_norm_eq_of_val_sub_one_le_aux Q q hq D u₀ hu₀ hu₀D
  have hfin := finiteIndex_units_inf_range_norm_aux Q q hq (2 * D + 2) hopen
  -- the inertia degree of `q`
  have hf : 0 < q.asIdeal.inertiaDeg (𝓞 K) := Ideal.inertiaDeg_pos q.asIdeal (𝓞 K)
  set H : Subgroup (Q.adicCompletion K)ˣ := MonoidHom.range (Units.map
    (Algebra.norm (Q.adicCompletion K) : q.adicCompletion L →* Q.adicCompletion K)) with hHdef
  set P : Subgroup (Q.adicCompletion K)ˣ := (Units.map
    (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) :
      (Q.adicCompletionIntegers K) →* (Q.adicCompletion K))).range with hPdef
  set ϖ : Q.adicCompletionIntegers K :=
    Commons.RingTheory.Henselian.uniformizer (R := 𝓞 K) (K := K) Q with hϖdef
  have hϖval : Valued.v (R := Q.adicCompletion K) (Γ₀ := Zstar0)
      (ϖ : Q.adicCompletion K) = WithZero.exp (-1 : ℤ) :=
    Commons.RingTheory.Henselian.uniformizer_valuation_eq_exp_neg_one Q
  have hϖne : (ϖ : Q.adicCompletion K) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hϖval
    exact WithZero.exp_ne_zero hϖval.symm
  set w : (Q.adicCompletion K)ˣ := Units.mk0 (ϖ : Q.adicCompletion K) hϖne with hwdef
  -- a unit `u₁` of the integers and an element `x₁` with `N x₁ = u₁ * ϖ ^ f`
  obtain ⟨u₁, x₁, hux₁⟩ := exists_norm_uniformizer_mul_unit_adicCompletion Q q hq
  have hu₁ne : ((u₁ : Q.adicCompletionIntegers K) : Q.adicCompletion K) ≠ 0 :=
    fun hh => Units.ne_zero u₁ (Subtype.coe_injective hh)
  have hx₁ne : x₁ ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero] at hux₁
    exact mul_ne_zero hu₁ne (pow_ne_zero _ hϖne) hux₁.symm
  have hgen : ∀ g : (Q.adicCompletion K)ˣ, ∃ p ∈ P, ∃ m : ℤ, g = p * w ^ m := by
    intro g
    obtain ⟨u, m, hm⟩ := exists_units_mul_uniformizer_zpow_adicCompletion Q g
    refine ⟨Units.map (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) :
      (Q.adicCompletionIntegers K) →* (Q.adicCompletion K)) u, ⟨u, rfl⟩, m, ?_⟩
    apply Units.ext
    rw [Units.val_mul, Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    change (g : Q.adicCompletion K) =
      ((u : Q.adicCompletionIntegers K) : Q.adicCompletion K) * (ϖ : Q.adicCompletion K) ^ m
    exact hm
  have hw : w ^ (q.asIdeal.inertiaDeg (𝓞 K)) ∈ P ⊔ H := by
    have hwu : w ^ (q.asIdeal.inertiaDeg (𝓞 K)) =
        (Units.map (algebraMap (Q.adicCompletionIntegers K) (Q.adicCompletion K) :
          (Q.adicCompletionIntegers K) →* (Q.adicCompletion K)) u₁)⁻¹ *
        Units.map (Algebra.norm (Q.adicCompletion K) :
          q.adicCompletion L →* Q.adicCompletion K) (Units.mk0 x₁ hx₁ne) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.coe_map, Units.coe_map,
        Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_mk0, hux₁]
      change (ϖ : Q.adicCompletion K) ^ (q.asIdeal.inertiaDeg (𝓞 K)) =
        (((u₁ : Q.adicCompletionIntegers K) : Q.adicCompletion K))⁻¹ *
          (((u₁ : Q.adicCompletionIntegers K) : Q.adicCompletion K) *
            (ϖ : Q.adicCompletion K) ^ (q.asIdeal.inertiaDeg (𝓞 K)))
      rw [inv_mul_cancel_left₀ hu₁ne]
    rw [hwu]
    refine Subgroup.mul_mem _ (le_sup_left (a := P) (b := H) ?_)
      (le_sup_right (a := P) (b := H) ?_)
    · exact ⟨u₁⁻¹, map_inv _ _⟩
    · exact ⟨Units.mk0 x₁ hx₁ne, rfl⟩
  have hIdx : H.FiniteIndex :=
    finiteIndex_of_zpow_generators_aux H P w (q.asIdeal.inertiaDeg (𝓞 K)) hf hgen hw hfin
  exact Subgroup.finite_quotient_of_finiteIndex


end

end Commons.NumberTheory.NumberField.Completion
