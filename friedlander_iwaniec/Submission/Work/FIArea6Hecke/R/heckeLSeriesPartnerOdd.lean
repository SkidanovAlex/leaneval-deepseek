/-
# `Work.FIArea6Hecke.R.heckeLSeriesPartnerOdd`

The Euler-product comparison between the Hecke `L`-series of a strict character `χ` mod `4d` and
its conductor partner `χ₀`, with the correction confined to the **odd** rational primes dividing
`4d`:

  `L(s,ψ_χ) = L(s,ψ_{χ₀})·∏_{p ∣ 4d, p ≠ 2}((1 - c₁(p)p^{-s})(1 - c₂(p)p^{-s}))`,  `re s > 1`.

The point is that the local Euler factor at `p = 2` is `1` on **both** sides, so no correction is
needed there: primary Gaussian integers have odd norm (`heckeLam_even`), hence
`λ(2^e) = 0` for every `e ≥ 1` and `λ(1) = χ(1) = 1` for each of `χ`, `χ₀`.  At the remaining
primes the argument is the local comparison of `heckeLSeriesPartnerLE`:

* `p ∣ 4d`, `p ≠ 2`: `λ_χ(p^e) = 0` for `e ≥ 1` (vanishing at the conductor,
  `heckeLamPrimePowZeroBad`), so the local factor of `L(s,ψ_χ)` is `1`, while the local factor of
  `L(s,ψ_{χ₀})` times `(1 - c₁(p)u)(1 - c₂(p)u)` is `1` by the two-term local recursion
  (`localFactor_at_bad`);
* `p ∤ 4d`: `λ_χ(p^e) = λ_{χ₀}(p^e)` for all `e` (`heckeLamPrimePowEqGood`), so the local factors
  agree.

The two `HasProd` statements are combined with the `HasProd` of the finite correction family
(`hasProdCorrFamily`) and `HasProd.unique`.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.StrictConductorDefs
import Submission.Work.FIArea5.S16Hecke.heckeLSeries_eulerProduct_hasProd
import Submission.Work.FIArea5.S16Hecke.heckeLam_localRec
import Submission.Work.FIArea6Hecke.R.heckeLamPrimePowZeroBad
import Submission.Work.FIArea6Hecke.R.heckeLamPrimePowEqGood
import Submission.Work.FIArea6Hecke.R.hasProdCorrFamily
import Submission.Work.FIArea6Hecke.R.LocalPrimeMine
import Submission.Work.FIArea6Hecke.R.heckeLSeriesPartnerLE

set_option autoImplicit false

namespace Work.FIArea6Hecke.R

open scoped BigOperators
open Work.FIArea5.S16Hecke

noncomputable section

/-- **The local Euler factor at `2` is `1`.**  For any coefficient family `χ` with `χ 1 = 1`, the
local factor `Σ_e λ(2^e)2^{-es}` of the Dirichlet series equals `1`: every primary Gaussian
integer has odd norm (`heckeLam_even`), so `λ(2^e) = 0` for `e ≥ 1`, and `λ(1) = χ 1 = 1`. -/
theorem localFactorTwo_eq_one (chi : GaussianInt → ℂ) (m : ℤ) (h1 : chi 1 = 1) {s : ℂ}
    (hs : 1 < s.re) :
    (∑' e : ℕ, heckeLam chi m (2 ^ e) / (((2 : ℕ) : ℂ) ^ ((e : ℂ) * s))) = 1 := by
  have hterm : ∀ e : ℕ, heckeLam chi m (2 ^ e) / (((2 : ℕ) : ℂ) ^ ((e : ℂ) * s))
      = heckeLam chi m (2 ^ e) * ((((2 : ℕ) : ℂ)) ^ (-s)) ^ e := by
    intro e
    rw [div_eq_mul_inv, cpow_inv_mul_eq 2 e s (by norm_num)]
  rw [tsum_congr hterm]
  rw [tsum_eq_single 0 (fun b hb => by
    have hev : Even (2 ^ b) :=
      ⟨2 ^ (b - 1), by rw [← two_mul, ← pow_succ']; congr 1; omega⟩
    rw [heckeLam_even chi m hev, zero_mul])]
  simp [heckeLam_one, h1]

/-- **Euler factors of conductor partners, correction at odd primes only.**  For a strict character
`χ` mod `4d` and a conductor partner `χ₀` (`IsConductorPartner`), the Hecke `L`-series differ by
the finite Euler-factor correction at the odd rational primes dividing `4d`. -/
theorem heckeLSeriesPartnerOdd (d : ℕ) (hd : 1 ≤ d) (chi : GaussianInt → ℂ) (M : GaussianInt)
    (chi₀ : GaussianInt → ℂ) (m : ℤ)
    (hchi : Work.FIArea5.S16Hecke.IsCharMod4dStrict d chi)
    (hpart : Work.FIArea6Hecke.R.IsConductorPartner d chi M chi₀) :
    ∃ (S : Finset ℕ) (c₁ c₂ : ℕ → ℂ),
      (∀ p ∈ S, Nat.Prime p ∧ p ∣ 4 * d ∧ p ≠ 2 ∧ ‖c₁ p‖ ≤ 1 ∧ ‖c₂ p‖ ≤ 1) ∧
      (∀ s : ℂ, 1 < s.re →
        Work.FIArea5.S16Hecke.heckeLSeries chi m s =
          Work.FIArea5.S16Hecke.heckeLSeries chi₀ m s *
            ∏ p ∈ S, ((1 - c₁ p * ((p : ℂ) ^ (-s))) * (1 - c₂ p * ((p : ℂ) ^ (-s))))) := by
  classical
  -- at each prime, the local roots delivered by `localPrimeExistsMine`
  let c₁ : ℕ → ℂ := fun p =>
    if hp : p.Prime then (localPrimeExistsMine d hd chi M chi₀ m hchi hpart p hp).choose else 0
  let c₂ : ℕ → ℂ := fun p =>
    if hp : p.Prime then
      ((localPrimeExistsMine d hd chi M chi₀ m hchi hpart p hp).choose_spec).choose else 0
  have hc₁ : ∀ p (hp : p.Prime),
      c₁ p = (localPrimeExistsMine d hd chi M chi₀ m hchi hpart p hp).choose := by
    intro p hp
    dsimp only [c₁]
    rw [dif_pos hp]
  have hc₂ : ∀ p (hp : p.Prime),
      c₂ p = ((localPrimeExistsMine d hd chi M chi₀ m hchi hpart p hp).choose_spec).choose := by
    intro p hp
    dsimp only [c₂]
    rw [dif_pos hp]
  have hspec : ∀ p (hp : p.Prime), ‖c₁ p‖ ≤ 1 ∧ ‖c₂ p‖ ≤ 1 ∧ ∀ e : ℕ,
      heckeLam chi m (p ^ e) =
        ∑ j ∈ Finset.range (e + 1), betaC (c₁ p) (c₂ p) j * heckeLam chi₀ m (p ^ (e - j)) := by
    intro p hp
    have h := (localPrimeExistsMine d hd chi M chi₀ m hchi hpart p hp).choose_spec.choose_spec
    rw [hc₁ p hp, hc₂ p hp]
    exact h
  -- the finite set of odd primes dividing `4d`
  let S : Finset ℕ := (4 * d).primeFactors.filter (fun p => p ≠ 2)
  have hSdef : S = (4 * d).primeFactors.filter (fun p => p ≠ 2) := rfl
  have hSprime : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    rw [hSdef] at hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hS4 : ∀ p ∈ S, p ∣ 4 * d := by
    intro p hp
    rw [hSdef] at hp
    exact Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have hS2 : ∀ p ∈ S, p ≠ 2 := by
    intro p hp
    rw [hSdef] at hp
    exact (Finset.mem_filter.mp hp).2
  refine ⟨S, c₁, c₂, ?_, ?_⟩
  · intro p hp
    exact ⟨hSprime p hp, hS4 p hp, hS2 p hp, (hspec p (hSprime p hp)).1,
      (hspec p (hSprime p hp)).2.1⟩
  · intro s hs
    have hA := heckeLSeries_eulerProduct_hasProd chi m hchi.1.1 hchi.1.2.1 hchi.1.2.2.1 hs
    have hB := heckeLSeries_eulerProduct_hasProd chi₀ m hpart.2.2.1 hpart.2.2.2.1
      hpart.2.2.2.2.1 hs
    have hC : HasProd (fun p : Nat.Primes => if (p : ℕ) ∈ S then
        corrFacP c₁ c₂ s (p : ℕ) else 1)
        (∏ p ∈ S, corrFacP c₁ c₂ s p) := by
      simpa only [corrFacP] using
        hasProdCorrFamily S (fun p hp => hSprime p hp) c₁ c₂ s
    -- the local factor of `χ` is `1` at the primes dividing `4d`
    have hAone : ∀ p : Nat.Primes, (p : ℕ) ∈ S →
        (∑' e : ℕ, heckeLam chi m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s))) = 1 := by
      intro p hpS
      have hpp : (p : ℕ).Prime := hSprime _ hpS
      have hp4 : (p : ℕ) ∣ 4 * d := hS4 _ hpS
      have hrew : (∑' e : ℕ, heckeLam chi m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
          = ∑' e : ℕ, heckeLam chi m ((p : ℕ) ^ e) * ((((p : ℕ) : ℂ) ^ (-s)) ^ e) := by
        refine tsum_congr fun e => ?_
        rw [div_eq_mul_inv, cpow_inv_mul_eq (p : ℕ) e s hpp.ne_zero]
      rw [hrew, tsum_eq_single 0 (fun b hb => by
        rw [heckeLamPrimePowZeroBad d hd chi m hchi (p : ℕ) hpp hp4 b (Nat.pos_of_ne_zero hb),
          zero_mul])]
      simp [heckeLam_one, hchi.1.1]
    -- and the local factor of `χ₀` times the correction is `1` there
    have hBone : ∀ p : Nat.Primes, (p : ℕ) ∈ S →
        (∑' e : ℕ, heckeLam chi₀ m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
          * corrFacP c₁ c₂ s (p : ℕ) = 1 := by
      intro p hpS
      have hpp : (p : ℕ).Prime := hSprime _ hpS
      have hp4 : (p : ℕ) ∣ 4 * d := hS4 _ hpS
      have hl : ∀ e : ℕ, heckeLam chi m ((p : ℕ) ^ e) =
          ∑ j ∈ Finset.range (e + 1), betaC (c₁ (p : ℕ)) (c₂ (p : ℕ)) j
            * heckeLam chi₀ m ((p : ℕ) ^ (e - j)) := (hspec (p : ℕ) hpp).2.2
      have hz : ∀ e : ℕ, 1 ≤ e → heckeLam chi m ((p : ℕ) ^ e) = 0 :=
        fun e he => heckeLamPrimePowZeroBad d hd chi m hchi (p : ℕ) hpp hp4 e he
      have key := localFactor_at_bad hpp hs hpart.2.2.2.2.1 hchi.1.1 hpart.2.2.1 hl hz
      simpa only [corrFacP] using key
    -- the pointwise comparison of the local factors
    have hpt : ∀ p : Nat.Primes,
        (∑' e : ℕ, heckeLam chi m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
          = (∑' e : ℕ, heckeLam chi₀ m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
            * (if (p : ℕ) ∈ S then corrFacP c₁ c₂ s (p : ℕ) else 1) := by
      intro p
      by_cases hmem : (p : ℕ) ∈ S
      · rw [if_pos hmem, hAone p hmem, hBone p hmem]
      · rw [if_neg hmem, mul_one]
        by_cases hp2 : (p : ℕ) = 2
        · rw [hp2, localFactorTwo_eq_one chi m hchi.1.1 hs,
            localFactorTwo_eq_one chi₀ m hpart.2.2.1 hs]
        · have hp4 : ¬ (p : ℕ) ∣ 4 * d := fun hdiv => hmem (by
            rw [hSdef]
            exact Finset.mem_filter.mpr
              ⟨Nat.mem_primeFactors.mpr ⟨p.2, hdiv, by omega⟩, hp2⟩)
          refine tsum_congr fun e => ?_
          rw [heckeLamPrimePowEqGood d hd chi M chi₀ m hchi hpart (p : ℕ) p.2 hp4 e]
    have hBC := hB.mul hC
    have hA' : HasProd (fun p : Nat.Primes =>
        ∑' e : ℕ, heckeLam chi m ((p : ℕ) ^ e) / (((p : ℕ) : ℂ) ^ ((e : ℂ) * s)))
        (heckeLSeries chi₀ m s * ∏ p ∈ S, corrFacP c₁ c₂ s p) :=
      hBC.congr_fun fun p => hpt p
    simpa only [corrFacP] using HasProd.unique hA hA'

end

end Work.FIArea6Hecke.R
