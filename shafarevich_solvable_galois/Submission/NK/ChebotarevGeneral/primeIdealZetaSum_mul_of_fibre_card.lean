import Mathlib
import Submission.NK.ChebotarevGeneral.DensityAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ChebotarevGeneral

open NumberField IsDedekindDomain

/-! ## Scaling a Dirichlet series by a constant fibre count

The transfer step of the reduction of Čebotarev's theorem to its abelian (cyclic) case compares the
partial Dirichlet series over the set `A` of primes of `M` with a given Frobenius, with the partial
series over the set `B` of primes of `K` whose Frobenius class contains `σ`.  The link between the
two sets is that the number of primes of `A` above a prime `𝔭` of `K`, multiplied by the order
`m = ord(σ)`, is `n = |C_G(σ)|` or `0` according to whether `𝔭 ∈ B`; that is exactly the hypothesis
`hfib` of `primeIdealZetaSum_mul_of_fibre_card`.

The arithmetic content is isolated in the following lemma, which is completely general:  if a
family `k : P → ℕ` of multiplicities is related to the indicator of `B` by
`k 𝔭 * m = B.indicator (fun _ => n) 𝔭`, then the `m`-fold multiple of the series over the fibre
counts is `n` times the series over `B`. -/

/-- **A constant fibre count scales a series by a constant.**  Let `k : P → ℕ` be a family of
natural numbers and `B : Set P`; if `k 𝔭 * m = B.indicator (fun _ => n) 𝔭` for all `𝔭`, then
`(∑' 𝔭, k 𝔭 * g 𝔭) * m = n * ∑' 𝔭 ∈ B, g 𝔭`. -/
lemma tsum_mul_of_indicator_fibre_eq {P : Type*} {k : P → ℕ} {g : P → ℝ} {B : Set P} {m n : ℕ}
    (h : ∀ 𝔭, k 𝔭 * m = B.indicator (fun _ => n) 𝔭) :
    (∑' 𝔭, (k 𝔭 : ℝ) * g 𝔭) * (m : ℝ) = (n : ℝ) * ∑' 𝔭 : B, g 𝔭 := by
  -- a pointwise computation, first moving the multiplication inside and then replacing the
  -- multiplicity `k 𝔭` by the indicator of `B`
  have hpt : ∀ 𝔭, ((k 𝔭 : ℝ) * g 𝔭) * (m : ℝ) = B.indicator (fun 𝔮 => (n : ℝ) * g 𝔮) 𝔭 := by
    intro 𝔭
    -- the coerced indicator of `B` is the indicator of the coerced function
    have hind : ((B.indicator (fun _ => n) 𝔭 : ℕ) : ℝ) = B.indicator (fun _ => (n : ℝ)) 𝔭 := by
      by_cases hb : 𝔭 ∈ B
      · rw [Set.indicator_of_mem hb, Set.indicator_of_mem hb]
      · rw [Set.indicator_of_notMem hb, Set.indicator_of_notMem hb]
        simp
    have hcast : ((k 𝔭 * m : ℕ) : ℝ) = ((B.indicator (fun _ => n) 𝔭 : ℕ) : ℝ) := by rw [h 𝔭]
    rw [Nat.cast_mul] at hcast
    rw [mul_assoc (↑(k 𝔭)) (g 𝔭) (↑m), mul_comm (g 𝔭) (↑m), ← mul_assoc (↑(k 𝔭)) (↑m) (g 𝔭)]
    rw [hcast, hind]
    by_cases hb : 𝔭 ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hb]
  rw [← tsum_mul_right]
  rw [tsum_congr hpt]
  rw [← tsum_subtype]
  exact tsum_mul_left

theorem primeIdealZetaSum_mul_of_fibre_card {K M : Type*} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M]
    {A : Set (NK.Chebotarev.PrimeIdeal M)} {B : Set (NK.Chebotarev.PrimeIdeal K)} (m n : ℕ)
    (hA : ∀ 𝒬 ∈ A,
      (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal = 1)
    (hfib : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K,
      Nat.card {𝒬 : NK.Chebotarev.PrimeIdeal M // 𝒬 ∈ A ∧ 𝒬.asIdeal.LiesOver 𝔭.asIdeal} * m
        = B.indicator (fun _ => n) 𝔭)
    {s : ℝ} (hs : 1 < s) :
    NumberField.Set.primeIdealZetaSum A s * (m : ℝ)
      = (n : ℝ) * NumberField.Set.primeIdealZetaSum B s := by
  classical
  -- group the series over `A` by the prime of `K` below
  have hZA := primeIdealZetaSum_eq_tsum_fibre (K := K) (M := M) (S := A) hA hs
  -- the two descriptions of the fibre of `A` over `𝔭` agree
  have hcard : ∀ 𝔭 : NK.Chebotarev.PrimeIdeal K,
      (Nat.card {𝒬 : A // (𝒬 : NK.Chebotarev.PrimeIdeal M).asIdeal.LiesOver 𝔭.asIdeal} : ℝ)
        = (Nat.card {𝒬 : NK.Chebotarev.PrimeIdeal M //
            𝒬 ∈ A ∧ 𝒬.asIdeal.LiesOver 𝔭.asIdeal} : ℝ) := by
    intro 𝔭
    exact_mod_cast Nat.card_congr
      ({ toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
         invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
         left_inv := fun x => rfl
         right_inv := fun x => rfl } :
        {𝒬 : A // (𝒬 : NK.Chebotarev.PrimeIdeal M).asIdeal.LiesOver 𝔭.asIdeal} ≃
        {𝒬 : NK.Chebotarev.PrimeIdeal M // 𝒬 ∈ A ∧ 𝒬.asIdeal.LiesOver 𝔭.asIdeal})
  have hZA' : NumberField.Set.primeIdealZetaSum A s
      = ∑' 𝔭 : NK.Chebotarev.PrimeIdeal K,
          (Nat.card {𝒬 : NK.Chebotarev.PrimeIdeal M //
              𝒬 ∈ A ∧ 𝒬.asIdeal.LiesOver 𝔭.asIdeal} : ℝ)
            * (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) := by
    rw [hZA]
    exact tsum_congr fun 𝔭 => by rw [hcard 𝔭]
  -- unfold the series over `B` as a sum over the elements of `B`
  rw [hZA', NumberField.Set.primeIdealZetaSum_def]
  exact tsum_mul_of_indicator_fibre_eq (P := NK.Chebotarev.PrimeIdeal K)
    (k := fun 𝔭 => Nat.card {𝒬 : NK.Chebotarev.PrimeIdeal M //
      𝒬 ∈ A ∧ 𝒬.asIdeal.LiesOver 𝔭.asIdeal})
    (g := fun 𝔭 => (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s)) (B := B) (m := m) (n := n) hfib

end NK.ChebotarevGeneral
