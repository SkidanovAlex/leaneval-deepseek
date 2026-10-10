import Mathlib.Computability.Reduce
import Mathlib.RingTheory.Henselian
import Mathlib.Data.Int.Star
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Commons.NumberTheory.NumberField.Completion.map_maximalIdeal_eq_maximalIdeal_pow
import Submission.NK.UchidaKummer.Approximation.pow_eq_of_val_le_exp_neg
import Submission.NK.UchidaKummer.Approximation.pow_eq_of_val_sub_one_lt_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open IsDedekindDomain

namespace NK.UchidaKummer.Approximation

/-! ## The closed balls of the `v`-adic topology are open

The value group of `v.adicCompletion K` is the discrete group `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`,
so a ball `{z | v z ≤ exp (-m)}` is a translate of a basic neighbourhood of `0` — and is in fact
*open*, by the general lemma `Valued.isOpen_closedBall` of Mathlib. -/

theorem isOpen_val_le_exp_neg {K : Type*} [Field K] [NumberField K]
    (v : NK.Chebotarev.PrimeIdeal K) (m : ℕ) :
    IsOpen {z : v.adicCompletion K |
      Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0) z ≤ WithZero.exp (-(m : ℤ))} := by
  obtain ⟨π, hπ, -⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_uniformizer_adicCompletionIntegers v
  set r : MonoidWithZeroHom.ValueGroup₀
    ((Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0)) : v.adicCompletion K →*₀ Zstar0) :=
    (Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0)).restrict ((π : v.adicCompletion K) ^ m)
  have hemb : MonoidWithZeroHom.ValueGroup₀.embedding r = WithZero.exp (-(m : ℤ)) := by
    rw [Valuation.embedding_restrict, map_pow, hπ, ← WithZero.exp_nsmul]
    congr 1
    simp
  have hball : IsOpen {x : v.adicCompletion K |
      (Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0)).restrict x ≤ r} :=
    Valued.isOpen_closedBall (R := v.adicCompletion K) (r := r) (by
      intro h
      have h' := congrArg MonoidWithZeroHom.ValueGroup₀.embedding h
      rw [hemb, map_zero] at h'
      exact WithZero.exp_ne_zero h')
  have : {z : v.adicCompletion K |
        Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0) z ≤ WithZero.exp (-(m : ℤ))}
      = {x : v.adicCompletion K |
        (Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0)).restrict x ≤ r} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    rw [Valuation.restrict_le_iff_le_embedding, hemb]
  rw [this]
  exact hball

/-! ## The valuation of a prime is `exp (-e)` once it is `< 1`

This is the exponent `e` of the `ℓ`-adic logarithm computation: it is the ramification index of
the prime below `𝔮` in the completion. -/

theorem exists_exp_form_of_val_lt_one {K : Type*} [Field K] [NumberField K]
    (v : NK.Chebotarev.PrimeIdeal K) (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hlt : Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0) ((ℓ : ℕ) : v.adicCompletion K) < 1) :
    ∃ e : ℕ, 1 ≤ e ∧ Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0) ((ℓ : ℕ) : v.adicCompletion K)
      = WithZero.exp (-(e : ℤ)) := by
  set t : Zstar0 := Valued.v (R := v.adicCompletion K) (Γ₀ := Zstar0) ((ℓ : ℕ) : v.adicCompletion K)
    with ht
  have hne : ((ℓ : ℕ) : v.adicCompletion K) ≠ 0 := by
    have hinj := (algebraMap K (v.adicCompletion K)).injective
    have h : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr hℓ.ne_zero
    intro hk
    exact h (hinj (by rw [map_natCast, hk, map_zero]))
  have htne : t ≠ 0 := by
    rw [ht]
    exact (Valuation.ne_zero_iff _).mpr hne
  have hlog : WithZero.log t < 0 := by
    have h1 : WithZero.exp (WithZero.log t) < WithZero.exp 0 := by
      rw [WithZero.exp_log htne, WithZero.exp_zero]
      exact hlt
    exact WithZero.exp_lt_exp.mp h1
  refine ⟨(-(WithZero.log t)).toNat, ?_, ?_⟩
  · have h2 : (1 : ℤ) ≤ -(WithZero.log t) := by omega
    have h3 : ((-(WithZero.log t)).toNat : ℤ) = -(WithZero.log t) :=
      Int.toNat_of_nonneg (by omega)
    omega
  · have h3 : ((-(WithZero.log t)).toNat : ℤ) = -(WithZero.log t) :=
      Int.toNat_of_nonneg (by omega)
    rw [h3, neg_neg]
    exact (WithZero.exp_log htne).symm

/-! ## The `ℓ`-th power subgroup of the units of a `p`-adic completion is open

The subgroup `(kˣ)^ℓ` of `ℓ`-th powers contains the ball of radius `exp (-m)` around `1` (for a
suitable `m`), which is open; being a subgroup, it is then a union of translates of this ball and
hence open. -/

theorem isOpenEllPowSubgroup (K : Type*) [Field K] [NumberField K] (ℓ : ℕ) (hℓ : ℓ.Prime) :
    NK.UchidaKummer.IsOpenEllPowSubgroup K ℓ := by
  intro v
  let k := v.adicCompletion K
  change IsOpen ((NK.UchidaKummer.ellPowSubgroup k ℓ : Subgroup kˣ) : Set kˣ)
  have hmain : IsOpen {x : k | ∃ y : kˣ, (y : k) ^ ℓ = x} := by
    have key : ∃ m : ℕ, 1 ≤ m ∧ ∀ x : k,
        Valued.v (R := k) (Γ₀ := Zstar0) (x - 1) ≤ WithZero.exp (-(m : ℤ)) →
          ∃ y : kˣ, (y : k) ^ ℓ = x := by
      by_cases hunit : IsUnit ((ℓ : ℕ) : v.adicCompletionIntegers K)
      · -- `ℓ` is a unit of the ring of integers: Hensel's lemma applies to `X ^ ℓ - x`.
        refine ⟨1, le_refl 1, fun x hx => ?_⟩
        refine pow_eq_of_val_sub_one_lt_one K v ℓ hℓ hunit x ?_
        refine lt_of_le_of_lt hx ?_
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
        norm_num
      · -- `ℓ` is not a unit, so `v ℓ = exp (-e)` for some `e ≥ 1`: the `ℓ`-adic logarithm gives
        -- the `ℓ`-th powers on a deeper ball.
        have hle : Valued.v (R := k) (Γ₀ := Zstar0) ((ℓ : ℕ) : k) ≤ 1 :=
          Commons.Analysis.Nonarchimedean.val_natCast_le_one
            (Valued.v (R := k) (Γ₀ := Zstar0)) ℓ
        have hne1 : Valued.v (R := k) (Γ₀ := Zstar0) ((ℓ : ℕ) : k) ≠ 1 := by
          intro h
          exact hunit (HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mpr h)
        have hlt : Valued.v (R := k) (Γ₀ := Zstar0) ((ℓ : ℕ) : k) < 1 :=
          lt_of_le_of_ne hle hne1
        obtain ⟨e, -, hval⟩ := exists_exp_form_of_val_lt_one v ℓ hℓ hlt
        obtain ⟨N, hN1, hN⟩ := pow_eq_of_val_le_exp_neg K v ℓ hℓ e hval
        exact ⟨N, hN1, hN⟩
    obtain ⟨m, _, hm⟩ := key
    set B : Set k := {x : k | Valued.v (R := k) (Γ₀ := Zstar0) (x - 1) ≤ WithZero.exp (-(m : ℤ))}
      with hBdef
    have hBopen : IsOpen B := by
      have hiff : B = (fun x : k => x - 1) ⁻¹'
          {z : k | Valued.v (R := k) (Γ₀ := Zstar0) z ≤ WithZero.exp (-(m : ℤ))} := by
        ext x
        simp only [hBdef, Set.mem_ofPred_eq, Set.mem_preimage]
      rw [hiff]
      exact (isOpen_val_le_exp_neg v m).preimage (continuous_id.sub continuous_const)
    have hBS : B ⊆ {x : k | ∃ y : kˣ, (y : k) ^ ℓ = x} := fun x hx => hm x hx
    have h1B : (1 : k) ∈ B := by
      simp only [hBdef, Set.mem_ofPred_eq, sub_self, map_zero]
      exact bot_le
    -- the set of `ℓ`-th powers of units is closed under multiplication
    have hmul : ∀ x ∈ {x : k | ∃ y : kˣ, (y : k) ^ ℓ = x}, ∀ b ∈ B,
        x * b ∈ {x : k | ∃ y : kˣ, (y : k) ^ ℓ = x} := by
      rintro x ⟨y, rfl⟩ b hb
      obtain ⟨z, hz⟩ := hBS hb
      exact ⟨y * z, by rw [Units.val_mul, mul_pow, hz]⟩
    -- hence it is a union of translates of the open ball `B`
    rw [isOpen_iff_mem_nhds]
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      obtain ⟨y, hy⟩ := hx
      exact pow_ne_zero ℓ (Units.ne_zero y) hy
    have hxB : (Homeomorph.mulLeft₀ x hx0) '' B ∈ nhds x := by
      have hh : IsOpen ((Homeomorph.mulLeft₀ x hx0) '' B) :=
        (Homeomorph.mulLeft₀ x hx0).isOpenMap B hBopen
      exact hh.mem_nhds ⟨1, h1B, by simp⟩
    refine Filter.mem_of_superset hxB ?_
    rintro y ⟨b, hb, rfl⟩
    exact hmul x hx b hb
  -- transport back to the units: `Units.val` is continuous and injective
  have hpre : (Units.val ⁻¹' {x : k | ∃ y : kˣ, (y : k) ^ ℓ = x})
      = (NK.UchidaKummer.ellPowSubgroup k ℓ : Set kˣ) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, NK.UchidaKummer.ellPowSubgroup,
      MonoidHom.coe_range, Set.mem_range, powMonoidHom_apply]
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, Units.ext (by rw [← hy, Units.val_pow_eq_pow_val])⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, by rw [← hy, Units.val_pow_eq_pow_val]⟩
  rw [← hpre]
  exact Units.continuous_val.isOpen_preimage _ hmain

end NK.UchidaKummer.Approximation
