import Submission.ZagierHoffmanProof.OmegaD

/-!
# The Anderson–Thakur period function with its normalising constant

Let `K` be a complete `ℤᵐ⁰`-valued field of characteristic `p`, `q` a `p`-power, `θ ∈ K` with
`v θ = exp d` (`1 ≤ d`) and `μ ∈ K` a "period constant" with `μ^{q-1}·θ^q = -1` (equivalently
`μ^{q-1} = -θ^{-q}`, so `v μ = -q·d/(q-1)`, which is why `d ≥ 2` is forced whenever `μ ∈ K`).

Then the *true* Anderson–Thakur period function over `K` is

  `Ω := C μ · atOmega q θ`   (the pure product `∏_{i≥1}(1 - t/θ^{q^i})` times `μ`),

and it satisfies, in the positive-twist (Frobenius) form,

  ★ `(t - θ^q)·Ω^{(1)} = Ω`

(equivalently `Ω^{(-1)} = (t - θ)Ω`), together with `IsSmall Ω` when `v μ ≤ exp (-1)`.

The concrete model is `K = F((y)) = LaurentSeries F` with `θ = -y^{-(q-1)}` (`d = q - 1`) and
`μ = y^q`, for which `μ^{q-1}·θ^q = -1` is proved in `KummerField.lean`
(`kummerMu_pow_mul_theta_pow`); that instantiation is a matter of providing the `CharP`/`ExpChar`
instances for the Laurent series field.

## Main results

* `atOmega_twistD'` — `(t - θ^q)·Ω̃^{(1)} = -θ^q·Ω̃` for the pure product `Ω̃ = atOmega q θ`.
* ★ `periodDatum_twist` — `(t - θ^q)·Ω^{(1)} = Ω` for `Ω = C μ · Ω̃`.
* ★ `isSmall_periodDatum` — `IsSmall Ω`.
* `periodDatum_entire`, `periodDatum_bounded`.
-/

set_option autoImplicit false
open Filter Polynomial RatFunc
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰] [CompleteSpace K] [NonarchimedeanAddGroup K]
variable (q : ℕ) [FrobPow K q] (θ : K)

/-- **The sharp shape of the period functional equation**: `(t - θ^q)·Ω̃^{(1)} = -θ^q·Ω̃` for the
pure product `Ω̃ = atOmega q θ`, in a general normalisation `v θ = exp d`. -/
theorem atOmega_twistD' (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d) (hq : 2 ≤ q) :
    (PowerSeries.X - PowerSeries.C (θ ^ q)) * frobTwist (R := K) (p := q) 1 (atOmega q θ)
      = -PowerSeries.C (θ ^ q) * atOmega q θ := by
  have hθ0 : θ ≠ 0 := by
    intro h; rw [h, map_zero] at hθ
    exact absurd hθ.symm (WithZero.exp_ne_zero)
  have h1 : (PowerSeries.X - PowerSeries.C (θ ^ q) : PowerSeries K)
      = -PowerSeries.C (θ ^ q) * (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X) := by
    have hx : θ ^ (q ^ 1) * omX q θ 1 = 1 := by
      rw [omX]
      exact mul_inv_cancel₀ (pow_ne_zero _ hθ0)
    have h2 : (PowerSeries.C (θ ^ q) : PowerSeries K) * PowerSeries.C (omX q θ 1) = 1 := by
      rw [← map_mul]
      have h3 : θ ^ q * omX q θ 1 = 1 := by
        simpa only [pow_one] using hx
      rw [h3, map_one]
    calc (PowerSeries.X - PowerSeries.C (θ ^ q) : PowerSeries K)
        = -PowerSeries.C (θ ^ q)
            + (PowerSeries.C (θ ^ q) * PowerSeries.C (omX q θ 1)) * PowerSeries.X := by
          rw [h2]; ring
      _ = -PowerSeries.C (θ ^ q)
            * (1 - PowerSeries.C (omX q θ 1) * PowerSeries.X) := by ring
  rw [h1, mul_assoc, atOmega_twist_d q θ d hd hθ hq]

/-- **The period functional equation with the normalising constant**: if `μ^{q-1}·θ^q = -1` then
`Ω := C μ · atOmega q θ` satisfies `(t - θ^q)·Ω^{(1)} = Ω`. -/
theorem periodDatum_twist {μ : K} (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) (hμ : μ ^ (q - 1) * θ ^ q = -1) :
    (PowerSeries.X - PowerSeries.C (θ ^ q))
        * frobTwist (R := K) (p := q) 1 (PowerSeries.C μ * atOmega q θ)
      = PowerSeries.C μ * atOmega q θ := by
  have hq1 : 1 ≤ q := by omega
  have hpow : μ ^ q * θ ^ q = -μ := by
    have h : μ ^ q = μ ^ (q - 1) * μ := by
      conv_lhs => rw [← Nat.sub_add_cancel hq1]
      rw [pow_add, pow_one]
    rw [h]
    calc μ ^ (q - 1) * μ * θ ^ q = μ ^ (q - 1) * θ ^ q * μ := by ring
      _ = -1 * μ := by rw [hμ]
      _ = -μ := by ring
  have hC : (PowerSeries.C (μ ^ q) : PowerSeries K) * PowerSeries.C (θ ^ q)
      = -PowerSeries.C μ := by
    rw [← map_mul, hpow, map_neg]
  calc (PowerSeries.X - PowerSeries.C (θ ^ q))
        * frobTwist (R := K) (p := q) 1 (PowerSeries.C μ * atOmega q θ)
      = (PowerSeries.X - PowerSeries.C (θ ^ q))
          * (PowerSeries.C (μ ^ q) * frobTwist (R := K) (p := q) 1 (atOmega q θ)) := by
        rw [frobTwist_mul, frobTwist_C, pow_one]
    _ = PowerSeries.C (μ ^ q)
          * ((PowerSeries.X - PowerSeries.C (θ ^ q))
            * frobTwist (R := K) (p := q) 1 (atOmega q θ)) := by ring
    _ = PowerSeries.C (μ ^ q) * (-PowerSeries.C (θ ^ q) * atOmega q θ) := by
        rw [atOmega_twistD' q θ d hd hθ hq]
    _ = -((PowerSeries.C (μ ^ q) : PowerSeries K) * PowerSeries.C (θ ^ q)) * atOmega q θ := by ring
    _ = PowerSeries.C μ * atOmega q θ := by rw [hC]; ring

/-- The period function with its normalising constant is small. -/
theorem isSmall_periodDatum {μ : K} (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) (hμ : Valued.v μ ≤ WithZero.exp (-1)) :
    IsSmall (PowerSeries.C μ * atOmega q θ) :=
  isSmall_C_mul_atOmega_d q θ d hd hθ hq hμ

/-- The period function with its normalising constant is entire (a Tate series). -/
theorem periodDatum_bounded {μ : K} (d : ℤ) (hd : 1 ≤ d) (hθ : Valued.v θ = WithZero.exp d)
    (hq : 2 ≤ q) : SeriesBounded (PowerSeries.C μ * atOmega q θ) :=
  (atOmega_bounded_d q θ d hd hθ hq).C_mul μ

end ZagierHoffmanPositiveChar
