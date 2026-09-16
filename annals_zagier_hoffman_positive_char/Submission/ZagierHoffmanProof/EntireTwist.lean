import Mathlib.RingTheory.PowerSeries.Basic
import Submission.ZagierHoffmanProof.CompletionInstances
import Submission.ZagierHoffmanProof.FrobPow
import Submission.ZagierHoffmanProof.Entire

/-!
# The Frobenius twist of a power series and of entire series

For a commutative ring `R` of characteristic `p`, the `n`-fold *Frobenius twist* of a power
series `f = ∑ aₖ zᵏ` is

  `frobTwist p n f = ∑ aₖ ^ (p ^ n) zᵏ`,

i.e. the Frobenius endomorphism `x ↦ x ^ (p ^ n)` applied coefficientwise (this is the
`(-n)`-twist `f^{(-n)}` of the `t`-motives literature).  It is a ring endomorphism of
`R⟦z⟧`, and it preserves the Tate boundedness condition and the entire (Tate) condition of
`Entire.lean`.

## Main definitions

* `frobTwist p n f` — the twisted series; `frobTwistHom p n` — the same, as a `RingHom`.
* `expmul` — `exp k ^ m = exp (k * m)` in the value group `ℤᵐ⁰`.

## Main results

* `frobTwistHom` is a ring endomorphism (`frobTwist_add`, `frobTwist_mul`, …).
* `frobTwist_comp` — twisting twice is twisting by the sum of the exponents.
* `SeriesBounded.frobTwist` and `Entire.frobTwist`.
-/

set_option autoImplicit false

open Filter
open scoped WithZero Topology

namespace ZagierHoffmanPositiveChar

/-- `exp` turns multiplication of exponents into powers in the value group. -/
lemma expmul (k : ℤ) (m : ℕ) : (WithZero.exp k) ^ m = (WithZero.exp (k * m) : ℤᵐ⁰) := by
  induction m with
  | zero => simp
  | succ j ih => rw [pow_succ, ih, ← WithZero.exp_add]; congr 1; push_cast; ring

/-- `exp` of a natural multiple: `exp (k * n) = exp k ^ n`. -/
lemma exp_mul_natCast (k : ℤ) (n : ℕ) :
    (WithZero.exp ((n : ℤ) * k) : ℤᵐ⁰) = (WithZero.exp k) ^ n := by
  rw [mul_comm, expmul]

section twist

variable {R : Type*} [CommRing R] {p : ℕ} [FrobPow R p]

/-- The `n`-fold Frobenius twist of a power series: the coefficient at `k` is the
`p ^ n`-th power of the coefficient of the original series. -/
noncomputable def frobTwist (n : ℕ) (f : PowerSeries R) : PowerSeries R :=
  PowerSeries.mk fun k => (PowerSeries.coeff k f) ^ (p ^ n)

lemma frobTwist_apply (n : ℕ) (f : PowerSeries R) :
    frobTwist (R := R) (p := p) n f
      = PowerSeries.mk (fun k => (PowerSeries.coeff k f) ^ (p ^ n)) := rfl

@[simp] lemma frobTwist_coeff (n : ℕ) (f : PowerSeries R) (k : ℕ) :
    PowerSeries.coeff k (frobTwist (R := R) (p := p) n f)
      = (PowerSeries.coeff k f) ^ (p ^ n) := by
  rw [frobTwist_apply, PowerSeries.coeff_mk]

lemma sum_pow_frob {ι : Type*} (s : Finset ι) (f : ι → R) (n : ℕ) :
    (∑ i ∈ s, f i) ^ (p ^ n) = ∑ i ∈ s, (f i) ^ (p ^ n) := by
  exact FrobPow.sum_pow s f n

/-- The Frobenius twist as a ring endomorphism of `R⟦z⟧`. -/
noncomputable def frobTwistHom (n : ℕ) : PowerSeries R →+* PowerSeries R where
  toFun := frobTwist (R := R) (p := p) n
  map_zero' := by
    ext k
    rw [frobTwist_coeff]
    simp [zero_pow (pow_ne_zero n (FrobPow.ne_zero R (q := p)))]
  map_one' := by
    ext k
    rw [frobTwist_coeff, PowerSeries.coeff_one]
    by_cases h : k = 0
    · simp [h]
    · simp [h, zero_pow (pow_ne_zero n (FrobPow.ne_zero R (q := p)))]
  map_add' := by
    haveI := FrobPow.pow (R := R) (q := p) n
    intro f g
    ext k
    simp only [frobTwist_coeff, map_add, FrobPow.add_pow]
  map_mul' := by
    intro f g
    ext k
    simp only [frobTwist_coeff, PowerSeries.coeff_mul, map_sum, map_mul, sum_pow_frob, mul_pow]

@[simp] lemma frobTwist_zero (n : ℕ) : frobTwist (R := R) (p := p) n 0 = 0 :=
  (frobTwistHom (R := R) (p := p) n).map_zero

@[simp] lemma frobTwist_one (n : ℕ) : frobTwist (R := R) (p := p) n 1 = 1 :=
  (frobTwistHom (R := R) (p := p) n).map_one

lemma frobTwist_add (n : ℕ) (f g : PowerSeries R) :
    frobTwist (R := R) (p := p) n (f + g)
      = frobTwist (R := R) (p := p) n f + frobTwist (R := R) (p := p) n g :=
  (frobTwistHom (R := R) (p := p) n).map_add f g

lemma frobTwist_mul (n : ℕ) (f g : PowerSeries R) :
    frobTwist (R := R) (p := p) n (f * g)
      = frobTwist (R := R) (p := p) n f * frobTwist (R := R) (p := p) n g :=
  (frobTwistHom (R := R) (p := p) n).map_mul f g

lemma frobTwist_neg (n : ℕ) (f : PowerSeries R) :
    frobTwist (R := R) (p := p) n (-f) = -frobTwist (R := R) (p := p) n f :=
  (frobTwistHom (R := R) (p := p) n).map_neg f

lemma frobTwist_sub (n : ℕ) (f g : PowerSeries R) :
    frobTwist (R := R) (p := p) n (f - g)
      = frobTwist (R := R) (p := p) n f - frobTwist (R := R) (p := p) n g :=
  (frobTwistHom (R := R) (p := p) n).map_sub f g

lemma frobTwist_C (n : ℕ) (c : R) :
    frobTwist (R := R) (p := p) n (PowerSeries.C c)
      = PowerSeries.C (c ^ (p ^ n)) := by
  ext k
  rw [frobTwist_coeff, PowerSeries.coeff_C, PowerSeries.coeff_C]
  by_cases h : k = 0
  · simp [h]
  · simp [h, zero_pow (pow_ne_zero n (FrobPow.ne_zero R (q := p)))]

lemma frobTwist_pow (n : ℕ) (f : PowerSeries R) (m : ℕ) :
    frobTwist (R := R) (p := p) n (f ^ m) = (frobTwist (R := R) (p := p) n f) ^ m :=
  (frobTwistHom (R := R) (p := p) n).map_pow f m

lemma frobTwist_comp (m n : ℕ) (f : PowerSeries R) :
    frobTwist (R := R) (p := p) m (frobTwist (R := R) (p := p) n f)
      = frobTwist (R := R) (p := p) (m + n) f := by
  ext k
  rw [frobTwist_coeff, frobTwist_coeff, frobTwist_coeff, ← pow_mul, ← pow_add, Nat.add_comm m n]

lemma frobTwist_iterate (n : ℕ) (f : PowerSeries R) :
    (frobTwist (R := R) (p := p) 1)^[n] f = frobTwist (R := R) (p := p) n f := by
  induction n with
  | zero =>
      rw [Function.iterate_zero_apply, frobTwist_apply]
      ext k
      simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih, frobTwist_comp, Nat.one_add]

end twist

section entire

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰] {p : ℕ} [FrobPow K p]

lemma SeriesBounded.frobTwist {f : PowerSeries K} (hf : SeriesBounded f) (n : ℕ) :
    SeriesBounded (frobTwist (R := K) (p := p) n f) := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨M * ((p ^ n : ℕ) : ℤ), fun k => ?_⟩
  rw [frobTwist_coeff, map_pow, ← expmul M (p ^ n)]
  exact pow_le_pow_left' (hM k) _

lemma Entire.frobTwist {f : PowerSeries K} (hf : Entire f) (n : ℕ) :
    Entire (frobTwist (R := K) (p := p) n f) := by
  intro N
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hf (max (N + 1) 1))
  refine Filter.eventually_atTop.mpr ⟨N₀, fun k hk => ?_⟩
  rw [frobTwist_coeff, map_pow]
  have hP : (1 : ℤ) ≤ ((p ^ n : ℕ) : ℤ) := by
    have := pow_pos (Nat.pos_of_ne_zero (FrobPow.ne_zero K (q := p))) n
    omega
  have hT : (0 : ℤ) ≤ max (N + 1) 1 := le_trans zero_le_one (le_max_right _ _)
  have h1 : (Valued.v (PowerSeries.coeff k f)) ^ (p ^ n)
      ≤ WithZero.exp (-(max (N + 1) 1) * ((p ^ n : ℕ) : ℤ)) := by
    rw [← expmul (-(max (N + 1) 1)) (p ^ n)]
    exact pow_le_pow_left' (le_of_lt (hN₀ k hk)) _
  calc (Valued.v (PowerSeries.coeff k f)) ^ (p ^ n)
      ≤ WithZero.exp (-(max (N + 1) 1) * ((p ^ n : ℕ) : ℤ)) := h1
    _ ≤ WithZero.exp (-(max (N + 1) 1)) :=
        WithZero.exp_le_exp.mpr (by nlinarith [hT, hP])
    _ < WithZero.exp (-N) :=
        WithZero.exp_lt_exp.mpr (by
          have h : N < max (N + 1) 1 := lt_of_lt_of_le (show N < N + 1 by omega) (le_max_left _ _)
          omega)

/-- The Frobenius twist preserves the ring of entire series. -/
lemma frobTwist_mem_entireSubring {p : ℕ} [FrobPow K p] (n : ℕ) {f : PowerSeries K}
    (hf : f ∈ entireSubring K) : frobTwist (p := p) n f ∈ entireSubring K :=
  hf.frobTwist n

/-- The Frobenius twist preserves the Tate algebra. -/
lemma frobTwist_mem_tateSubring {p : ℕ} [FrobPow K p] (n : ℕ) {f : PowerSeries K}
    (hf : f ∈ tateSubring K) : frobTwist (p := p) n f ∈ tateSubring K :=
  hf.frobTwist n

end entire

end ZagierHoffmanPositiveChar
