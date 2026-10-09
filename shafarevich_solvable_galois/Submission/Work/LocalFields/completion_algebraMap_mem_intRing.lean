import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.CompletionLocalField
import Submission.Work.LocalFields.LocalFieldAPI
import Submission.Work.LocalFields.exists_pow_eq_of_one_sub_lt_one
import Submission.Work.LocalFields.exists_algebra_completion
import Submission.Work.LocalFields.valuation_smul_of_mem_stabilizer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero

/-- **The structure map `K_v →+* L_w` of a `K_v`-algebra structure on `L_w` compatible with
`K ⊆ L` maps the valuation ring `𝒪_{K_v}` into `𝒪_{L_w}`.**

Equivalently, `σ := φ.algebraMap` is bounded on the unit ball, hence (being additive) uniformly
continuous.  This is the technical heart of `Work.LocalFields.completion_algebra_range_eq`.

Proof route: `R := σ⁻¹(𝒪_{L_w}) = {x | v_{L_w}(σ x) ≤ 1}` is a valuation subring of `K_v`
(its `valuationSubring` is that of `Valued.v.comap σ`), it contains `𝒪_{K_v} ∩ K` (because
`σ|_K = ρ|_K` and the `v`- and `w`-adic valuations agree on `K`), and it is a *proper* subring
(take `λ ∈ K` of `v`-adic valuation `> 1`; then `σ λ = ρ λ` has `w`-adic valuation `> 1`).
Since `𝒪_{K_v}` is a discrete valuation ring (Krull dimension one), `R = 𝒪_{K_v}` -- this is the
step that needs the uniqueness of the extension of the (complete) `p`-adic valuation of `ℚ_p` to
the finite extension `K_v/ℚ_p`: any valuation subring `S ⊆ K_v` with `S ∩ ℚ_p = 𝒪_{ℚ_p}` equals
`𝒪_{K_v}`, and `σ x ∈ 𝒪_{L_w}` for `x ∈ 𝒪_{K_v} ∩ K` shows `R ∩ ℚ_p = 𝒪_{ℚ_p}`.
Finally `σ(𝒪_{K_v}) ⊆ 𝒪_{L_w}` is the claim with `R = σ⁻¹(𝒪_{L_w}) = 𝒪_{K_v}`.

The argument formalised here is different and avoids the general uniqueness theory of extensions
of valuations.  Choose `π ∈ 𝓞 K` with `v(π) < 1` and let `e` be the (additive) valuation of the
image of `π` in `L_w`; let `c` be the residue characteristic of `K_v` and put `n = 1 + c * e`.
Then `n` is coprime to `c` while `e < n`.  An element `x` with `Valued.v x ≤ 1` satisfies
`1 + π xⁿ ≡ 1 (mod 𝔪_{K_v})`, hence is an `n`-th power in `K_v` (Hensel); applying `σ` (which
fixes `K`) we obtain that `1 + π (σ x)ⁿ` is an `n`-th power in `L_w`.  If `Valued.v (σ x) > 1`
then the non-archimedean inequality forces `v_{L_w}(1 + π (σ x)ⁿ) = v(π)·v(σ x)ⁿ`, so that
`v(π)` is an `n`-th power in the value group `ℤᵐ⁰`, i.e. `n ∣ e` -- contradicting `e < n`. -/
theorem completion_algebraMap_mem_intRing {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (v : Work.LocalFields.FinitePrime K) (w : Work.LocalFields.FinitePrime L)
    [hw : w.asIdeal.LiesOver v.asIdeal]
    [φ : Algebra (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
    [IsScalarTower K (Work.LocalFields.Completion K v) (Work.LocalFields.Completion L w)]
    (x : Work.LocalFields.Completion K v) (hx : Valued.v x ≤ 1) :
    Valued.v (φ.algebraMap x) ≤ 1 := by
  classical
  -- ## A small nonzero element of `K`
  obtain ⟨π, hπmem, hπ0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (IsDedekindDomain.HeightOneSpectrum.ne_bot v)
  have hπK : (v.valuation K) ((π : 𝓞 K) : K) < 1 := by
    rw [NumberField.RingOfIntegers.coe_eq_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
    exact hπmem
  have hπKne : ((π : 𝓞 K) : K) ≠ 0 := fun h =>
    hπ0 (NumberField.RingOfIntegers.coe_injective h)
  -- ## Its images in the two completions
  set tK : Completion K v := algebraMap K (Completion K v) ((π : 𝓞 K) : K) with htK
  set tL : Completion L w := algebraMap K (Completion L w) ((π : 𝓞 K) : K) with htL
  have htK_lt : Valued.v tK < 1 := by
    rw [htK]
    have h2 : (algebraMap K (Completion K v) ((π : 𝓞 K) : K)) =
        (((π : 𝓞 K) : K) : Completion K v) := rfl
    rw [h2, IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe K v]
    exact hπK
  have htL_lt : Valued.v tL < 1 := by
    have hiso := valuation_isEquiv_of_liesOver v w
    have h1 : (w.valuation L) (algebraMap K L ((π : 𝓞 K) : K)) < 1 :=
      (Valuation.isEquiv_iff_val_lt_one.mp hiso).mp hπK
    rw [htL]
    have h2 : (algebraMap K (Completion L w) ((π : 𝓞 K) : K)) =
        ((algebraMap K L ((π : 𝓞 K) : K)) : Completion L w) := rfl
    rw [h2, IsDedekindDomain.HeightOneSpectrum.adicCompletion.valued_coe L w]
    exact h1
  -- ## The exponent `e` of `π` in the value group of `L_w`, and the auxiliary integer `n`
  obtain ⟨e, he⟩ : ∃ e : ℕ, Valued.v tL = WithZero.exp (-(e : ℤ)) := by
    refine exists_exp_neg_of_ne_zero_of_le_one ?_ (le_of_lt htL_lt)
    have : tL ≠ 0 := by
      rw [htL]
      intro h
      exact hπKne (RingHom.injective (algebraMap K (Completion L w)) (by rw [h, map_zero]))
    exact (Valuation.zero_iff (Valued.v)).not.mpr this
  have he1 : 0 < e := by
    have h : WithZero.exp (-(e : ℤ)) < WithZero.exp (0 : ℤ) := by
      rw [← he, WithZero.exp_zero]; exact htL_lt
    have := WithZero.exp_lt_exp.mp h
    omega
  set c : ℕ := ringChar (𝓀[Work.LocalFields.Completion K v]) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact @CharP.ringChar_ne_zero_of_finite _ _ (completion_finite_residue v)
  have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc0
  set n : ℕ := 1 + c * e with hn
  have hn0 : n ≠ 0 := by rw [hn]; omega
  have hcop : n.Coprime c := by
    rw [hn, Nat.coprime_add_mul_left_left]
    exact Nat.coprime_one_left c
  have hen : e < n := by
    have h : e ≤ c * e := Nat.le_mul_of_pos_left e (by omega)
    rw [hn]; omega
  -- ## Hensel: `1 + π xⁿ` is an `n`-th power in `K_v`
  obtain ⟨y, hy⟩ : ∃ y : Completion K v, y ^ n = 1 + tK * x ^ n := by
    refine exists_pow_eq_of_one_sub_lt_one (k := Completion K v) ?_ ?_
    · show Nat.Coprime n (ringChar (𝓀[Work.LocalFields.Completion K v]))
      exact hcop
    · show Valued.v ((1 + tK * x ^ n) - 1) < 1
      rw [add_sub_cancel_left, Valuation.map_mul, Valuation.map_pow]
      calc Valued.v tK * Valued.v x ^ n ≤ Valued.v tK * 1 :=
            mul_le_mul_right (pow_le_one' hx n) _
        _ = Valued.v tK := mul_one _
        _ < 1 := htK_lt
  -- ## The scalar tower identifies the two copies of `π`
  have hσt : φ.algebraMap tK = tL := by
    rw [htK, htL]
    exact (IsScalarTower.algebraMap_apply K (Completion K v) (Completion L w) ((π : 𝓞 K) : K)).symm
  have hpow_l : (φ.algebraMap y) ^ n = 1 + tL * (φ.algebraMap x) ^ n := by
    rw [← map_pow, hy]
    simp only [map_add, map_one, map_mul, map_pow]
    rw [hσt]
  -- ## Contradiction if `σ x` is not integral
  by_contra hcon
  have hv1 : 1 < Valued.v (φ.algebraMap x) := lt_of_not_ge hcon
  set Y : Completion L w := φ.algebraMap x with hY
  have hY0 : Y ≠ 0 := by
    intro h
    rw [h, map_zero] at hv1
    exact absurd hv1 (not_lt.mpr (zero_le_one : (0 : ℤᵐ⁰) ≤ 1))
  set m : ℤ := (Valued.v Y).log with hm
  have hYv : Valued.v Y = WithZero.exp m :=
    (WithZero.exp_log ((Valuation.zero_iff (Valued.v)).not.mpr hY0)).symm
  have hmpos : 0 < m := by
    have h : WithZero.exp (0 : ℤ) < WithZero.exp m := by
      rw [WithZero.exp_zero, ← hYv]; exact hv1
    exact WithZero.exp_lt_exp.mp h
  have hm1 : (1 : ℤ) ≤ m := hmpos
  have hne : (e : ℤ) < (n : ℤ) := by exact_mod_cast hen
  -- the value of `tL * Yⁿ`
  have hval : Valued.v (tL * Y ^ n) = WithZero.exp (-(e : ℤ) + (n : ℤ) * m) := by
    rw [Valuation.map_mul, Valuation.map_pow, he, hYv, ← WithZero.exp_nsmul, ← WithZero.exp_add]
    congr 1
  -- `v (tL * Yⁿ) > 1`
  have hgt : Valued.v (1 : Completion L w) < Valued.v (tL * Y ^ n) := by
    rw [map_one, hval, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    nlinarith
  have hkey : Valued.v ((φ.algebraMap y) ^ n) = WithZero.exp (-(e : ℤ) + (n : ℤ) * m) := by
    rw [hpow_l, Valuation.map_add_eq_of_lt_right (Valued.v) hgt, hval]
  have hYne : Valued.v (φ.algebraMap y) ≠ 0 := by
    intro h0
    have h1 : Valued.v ((φ.algebraMap y) ^ n) = 0 := by
      rw [Valuation.map_pow, h0, zero_pow hn0]
    rw [hkey] at h1
    exact WithZero.exp_ne_zero h1
  set a : ℤ := (Valued.v (φ.algebraMap y)).log with ha
  have hav : Valued.v (φ.algebraMap y) = WithZero.exp a := (WithZero.exp_log hYne).symm
  have hlog : (n : ℤ) * a = -(e : ℤ) + (n : ℤ) * m := by
    have h2 : Valued.v ((φ.algebraMap y) ^ n) = WithZero.exp ((n : ℤ) * a) := by
      rw [Valuation.map_pow, hav, ← WithZero.exp_nsmul]
      congr 1
    rw [h2] at hkey
    exact WithZero.exp_injective hkey
  have hdvd : n ∣ e := by
    have h4 : (e : ℤ) = (n : ℤ) * (m - a) := by linarith
    exact Int.natCast_dvd_natCast.mp ⟨m - a, h4⟩
  exact absurd (Nat.le_of_dvd he1 hdvd) (not_le.mpr hen)

end Work.LocalFields
