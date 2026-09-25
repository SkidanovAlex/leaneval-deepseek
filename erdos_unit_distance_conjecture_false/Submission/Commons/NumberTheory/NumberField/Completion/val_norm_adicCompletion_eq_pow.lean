import Mathlib
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.exists_inertiaSubgroup_adicCompletion_isNormal_card_quotient
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
import Submission.Commons.RingTheory.Henselian.valuation_completion_liesOver

open scoped NumberField WithZero
open IsDedekindDomain.HeightOneSpectrum

/-- In the value group `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`, the `z`-th power of `exp m` is
`exp (m * z)`. -/
private lemma withZero_exp_zpow (m z : ℤ) :
    (WithZero.exp m : WithZero (Multiplicative ℤ)) ^ z = WithZero.exp (m * z) := by
  rw [show WithZero.exp m = (WithZero.exp (1 : ℤ)) ^ m by
    rw [← WithZero.exp_zsmul]; norm_num]
  rw [← zpow_mul, ← WithZero.exp_zsmul]
  norm_num

/-- Two surjective valuations with values in `ℤᵐ⁰` which are equivalent (i.e. have the same
valuation subring) are equal.  Both hypotheses are used: surjectivity pins down the value group
as `ℤᵐ⁰`, so that the order isomorphism of value groups induced by the equivalence is an
automorphism of the chain `ℤᵐ⁰` which is compatible with the group structure, hence the
identity. -/
private theorem valuation_eq_of_isEquiv_of_surjective
    {F : Type*} [Field F] {v w : Valuation F (WithZero (Multiplicative ℤ))}
    (hv : Function.Surjective v) (hw : Function.Surjective w) (h : v.IsEquiv w) : v = w := by
  -- an element whose `v`-value is `exp 1`
  obtain ⟨u, hu⟩ := hv (WithZero.exp (1 : ℤ))
  have hu0 : u ≠ 0 := fun h0 => WithZero.exp_ne_zero (by rw [← hu, h0, map_zero])
  have hvu0 : v u ≠ 0 := by rw [hu]; exact WithZero.exp_ne_zero
  -- `w u = exp m`
  set m : ℤ := (w u).log with hm
  have hwune : w u ≠ 0 := fun h0 => hvu0 ((h.eq_zero).mpr h0)
  have hwu : w u = WithZero.exp m := (WithZero.exp_log hwune).symm
  have hmpos : 0 < m := by
    rw [← WithZero.exp_lt_exp (a := (0 : ℤ)) (b := m), WithZero.exp_zero, ← hwu]
    have h1 : v 1 < v u := by
      rw [map_one, hu]; exact WithZero.exp_lt_exp.mpr (by norm_num)
    simpa using (h.lt_iff_lt).mp h1
  have hpow : ∀ z : ℤ, w (u ^ z) = WithZero.exp (m * z) := by
    intro z
    rw [map_zpow₀, hwu, withZero_exp_zpow]
  apply Valuation.ext; intro x
  by_cases hx : x = 0
  · rw [hx, map_zero, map_zero]
  · have hvx0 : v x ≠ 0 := (Valuation.ne_zero_iff v).mpr hx
    set k : ℤ := (v x).log with hk
    have hvx : v x = WithZero.exp k := (WithZero.exp_log hvx0).symm
    -- the `v`-normalized unit `x * u ^ (-k)`
    have hvc : v (x * u ^ (-k)) = 1 := by
      rw [map_mul, hvx, map_zpow₀, hu, ← WithZero.exp_zsmul, ← WithZero.exp_add]
      simp
    have hwc : w (x * u ^ (-k)) = 1 := (h.eq_one_iff_eq_one).mp hvc
    have hwx : w x = WithZero.exp (m * k) := by
      have hsplit : w x = w (x * u ^ (-k)) * w (u ^ k) := by
        rw [← map_mul]
        congr 1
        rw [mul_assoc, ← zpow_add₀ hu0]
        simp
      rw [hsplit, hwc, one_mul, hpow]
    -- `m = 1` forced by the surjectivity of `w`
    have hm1 : m = 1 := by
      obtain ⟨y, hy⟩ := hw (WithZero.exp (1 : ℤ))
      have hy0 : y ≠ 0 := fun h0 => WithZero.exp_ne_zero (by rw [← hy, h0, map_zero])
      have hvy0 : v y ≠ 0 := (Valuation.ne_zero_iff v).mpr hy0
      set j : ℤ := (v y).log with hj
      have hvy : v y = WithZero.exp j := (WithZero.exp_log hvy0).symm
      have hvc2 : v (y * u ^ (-j)) = 1 := by
        rw [map_mul, hvy, map_zpow₀, hu, ← WithZero.exp_zsmul, ← WithZero.exp_add]; simp
      have hwc2 : w (y * u ^ (-j)) = 1 := (h.eq_one_iff_eq_one).mp hvc2
      have hwy : w y = WithZero.exp (m * j) := by
        have hsplit : w y = w (y * u ^ (-j)) * w (u ^ j) := by
          rw [← map_mul]
          congr 1
          rw [mul_assoc, ← zpow_add₀ hu0]
          simp
        rw [hsplit, hwc2, one_mul, hpow]
      have hmul : m * j = 1 := by
        rw [hwy, WithZero.exp_inj] at hy
        exact hy
      rcases (Int.mul_eq_one_iff_eq_one_or_neg_one.mp hmul) with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact h1
      · omega
    rw [hwx, hm1, one_mul, ← hvx]

namespace Commons.NumberTheory.NumberField.Completion

open Commons.RingTheory.Henselian

/-- Every `Q.adicCompletion K`-algebra automorphism of `q.adicCompletion L` preserves the
`q`-adic valuation.  Indeed it preserves the valuation ring
(`algEquiv_mem_adicCompletionIntegers_iff_adicCompletion`), and since the value group is `ℤᵐ⁰`
and the valuation is surjective, `Valuation.eq_of_isEquiv_of_surjective` upgrades this to an
isometry. -/
theorem val_algEquiv_adicCompletion {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (adicCompletionMap Q q hq)
    ∀ (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L)
      (x : q.adicCompletion L),
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) (σ x) =
        Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) x := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (adicCompletionMap Q q hq)
  intro σ x
  let w : Valuation (q.adicCompletion L) (WithZero (Multiplicative ℤ)) :=
    (Valued.v : Valuation (q.adicCompletion L) (WithZero (Multiplicative ℤ))).comap
      (σ : q.adicCompletion L →+* q.adicCompletion L)
  have hsurjv : Function.Surjective
      (Valued.v : q.adicCompletion L → WithZero (Multiplicative ℤ)) :=
    adicCompletion_valued_surjective q
  have hsurjw : Function.Surjective w := by
    intro z
    obtain ⟨y, hy⟩ := hsurjv z
    refine ⟨σ.symm y, ?_⟩
    show Valued.v (σ (σ.symm y)) = z
    rw [AlgEquiv.apply_symm_apply]; exact hy
  have hequiv : (Valued.v : Valuation (q.adicCompletion L)
      (WithZero (Multiplicative ℤ))).IsEquiv w := by
    apply Valuation.isEquiv_of_val_le_one
    intro y
    show Valued.v y ≤ 1 ↔ Valued.v (σ y) ≤ 1
    rw [← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
          (R := 𝓞 L) (K := L) (v := q),
        ← IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
          (R := 𝓞 L) (K := L) (v := q)]
    exact (algEquiv_mem_adicCompletionIntegers_iff_adicCompletion Q q hq σ y).symm
  have hEq : w = (Valued.v : Valuation (q.adicCompletion L)
      (WithZero (Multiplicative ℤ))) :=
    valuation_eq_of_isEquiv_of_surjective hsurjw hsurjv hequiv.symm
  have : w x = Valued.v x := by rw [hEq]
  simpa [w, Valuation.comap_apply] using this

theorem val_norm_adicCompletion_eq_pow {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
    ∀ x : q.adicCompletion L,
      Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ))
          (algebraMap (Q.adicCompletion K) (q.adicCompletion L)
            (Algebra.norm (Q.adicCompletion K) x)) =
        (Valued.v (R := q.adicCompletion L) (Γ₀ := WithZero (Multiplicative ℤ)) x) ^
          (Module.finrank (Q.adicCompletion K) (q.adicCompletion L)) := by
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  haveI hfin : Module.Finite (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    isGalois_adicCompletion Q q hq
  intro x
  rw [Algebra.norm_eq_prod_automorphisms (Q.adicCompletion K) x]
  rw [map_prod]
  simp_rw [val_algEquiv_adicCompletion Q q hq]
  rw [Finset.prod_const, Finset.card_univ]
  congr 1
  rw [← Nat.card_eq_fintype_card]
  exact IsGalois.card_aut_eq_finrank (Q.adicCompletion K) (q.adicCompletion L)

end Commons.NumberTheory.NumberField.Completion
