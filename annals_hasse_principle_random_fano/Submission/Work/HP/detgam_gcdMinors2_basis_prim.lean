import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.NA.VeroAux
import Submission.Work.HP.NA.exists_lam_gcdMinors2

namespace Work.HP

/-- The gcd of a finite set of integers is nonnegative. -/
lemma int_finset_gcd_nonneg' {β : Type*} (s : Finset β) (f : β → ℤ) : 0 ≤ s.gcd f := by
  have h : |s.gcd f| = s.gcd f := by rw [Int.abs_eq_normalize, Finset.normalize_gcd]
  exact h ▸ abs_nonneg _

/-- Every coordinate of a basis vector of a saturated rank-two sublattice `K ⊆ ℤ^ι` is "primitive
at every prime": no prime divides all coordinates of `b i`.

Indeed, if `p` divided all coordinates of `b i`, the vector `w = b i / p` would satisfy
`p • w = b i ∈ K`, so `w ∈ K` by saturation; applying the linear isomorphism `b.repr` to
`p • w = b i` and evaluating at the coordinate `i` yields `p * (b.repr w) i = 1`, which is
impossible for a prime `p`. -/
lemma basis_coord_prim {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Submodule ℤ (ι → ℤ)) (hK : IsPrimLat K) (b : Module.Basis (Fin 2) ℤ K)
    (i : Fin 2) (p : ℕ) (hp : Nat.Prime p) :
    ∃ j, ¬ (p : ℤ) ∣ (b i : ι → ℤ) j := by
  classical
  by_contra h
  push Not at h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpnz : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨w, hwvec⟩ : ∃ w : ι → ℤ, (p : ℤ) • w = (b i : ι → ℤ) := by
    refine ⟨fun j => (b i : ι → ℤ) j / (p : ℤ), ?_⟩
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    exact Int.mul_ediv_cancel' (h j)
  have hmem : (p : ℤ) • w ∈ K := by rw [hwvec]; exact (b i).2
  have hwKmem : w ∈ K := hK w (p : ℤ) hpnz hmem
  have heq : (p : ℤ) • (⟨w, hwKmem⟩ : K) = b i := by
    apply Subtype.ext
    simp only [Submodule.coe_smul]
    exact hwvec
  have hrepr := congrArg b.repr heq
  simp only [map_smul, Module.Basis.repr_self] at hrepr
  have h1 := congrArg (fun f : Fin 2 →₀ ℤ => f i) hrepr
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul] at h1
  exact hpz.not_dvd_one ⟨(b.repr ⟨w, hwKmem⟩) i, h1.symm⟩

/-- The gcd of the `2 × 2` minors of a `ℤ`-basis of a saturated rank-`2` sublattice `K ⊆ ℤ^ι`
is `1`.

HINT.  `gcdMinors2 u v = Finset.univ.gcd (fun ij : ι × ι => u ij.1 * v ij.2 - u ij.2 * v ij.1)`,
so it suffices to show no prime `p` divides all minors (use
`Int.prime_iff_natAbs_prime`/`Int.prime_def_lt` and `Nat.exists_prime_and_dvd`, or `Int.associated`).
First note that each `b i` is primitive (if `γ • w = b i` with `w : ι → ℤ` and `γ ≠ 0` then
`w ∈ K` by saturation, so `w = t₀ • b 0 + t₁ • b 1`, giving `γ * tᵢ = δᵢ`).  Suppose a prime `p`
divides every minor of `b 0, b 1`.  Since `b 1` is primitive there is `i₀` with `¬ p ∣ b 1 i₀`,
and then every minor with index `i₀` gives `b 0 ≡ λ • b 1 (mod p)` with
`λ = b 0 i₀ * (b 1 i₀)⁻¹` (there is `μ` with `μ * b 1 i₀ ≡ 1 [ZMOD p]` by
`Int.isCoprime_iff_exists_mul_modEq_one`), i.e. `b 0 - λ • b 1 = p • w` for some `w : ι → ℤ`.
Now `b 0 - λ • b 1 ∈ K`, so `w ∈ K` by saturation, so `w = t₀ • b 0 + t₁ • b 1`; substituting
gives `(p * t₀ - 1) • b 0 + (p * t₁ + λ) • b 1 = 0`, and `ℤ`-independence of `b 0, b 1`
(they are a basis) yields `p * t₀ = 1`, impossible. -/
theorem detgam_gcdMinors2_basis_prim {ι : Type*} [Fintype ι] [DecidableEq ι]
    (K : Submodule ℤ (ι → ℤ)) (hK : IsPrimLat K) (b : Module.Basis (Fin 2) ℤ K) :
    gcdMinors2 (b 0 : ι → ℤ) (b 1 : ι → ℤ) = 1 := by
  classical
  have hpos : 0 ≤ gcdMinors2 (b 0 : ι → ℤ) (b 1 : ι → ℤ) := by
    rw [gcdMinors2]
    exact int_finset_gcd_nonneg' _ _
  have hno : ∀ p : ℕ, Nat.Prime p →
      ¬ (p : ℤ) ∣ gcdMinors2 (b 0 : ι → ℤ) (b 1 : ι → ℤ) := by
    intro p hp hpdiv
    have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hpnz : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    obtain ⟨i₀, hi₀⟩ := basis_coord_prim K hK b 0 p hp
    obtain ⟨c, hc⟩ := NA.exists_lam_gcdMinors2 (e := 1) hp (b 0 : ι → ℤ) (b 1 : ι → ℤ)
      ⟨i₀, hi₀⟩ (by simpa using hpdiv)
    have hc' : ∀ j, (p : ℤ) ∣ ((b 1 : ι → ℤ) j - c * (b 0 : ι → ℤ) j) :=
      fun j => by simpa using hc j
    obtain ⟨w, hwvec⟩ : ∃ w : ι → ℤ,
        (p : ℤ) • w = (b 1 : ι → ℤ) - c • (b 0 : ι → ℤ) := by
      refine ⟨fun j => ((b 1 : ι → ℤ) j - c * (b 0 : ι → ℤ) j) / (p : ℤ), ?_⟩
      funext j
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      exact Int.mul_ediv_cancel' (hc' j)
    have hmem : (p : ℤ) • w ∈ K := by
      rw [hwvec]
      exact K.sub_mem (b 1).2 (K.smul_mem c (b 0).2)
    have hwKmem : w ∈ K := hK w (p : ℤ) hpnz hmem
    have heq : (p : ℤ) • (⟨w, hwKmem⟩ : K) = b 1 - c • b 0 := by
      apply Subtype.ext
      simp only [Submodule.coe_smul, Submodule.coe_sub]
      exact hwvec
    have hrepr := congrArg b.repr heq
    simp only [map_smul, map_sub, Module.Basis.repr_self] at hrepr
    have h1 := congrArg (fun f : Fin 2 →₀ ℤ => f 1) hrepr
    simp only [Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (show (1 : Fin 2) ≠ 0 from by decide), smul_eq_mul,
      mul_zero, sub_zero] at h1
    exact hpz.not_dvd_one ⟨(b.repr ⟨w, hwKmem⟩) 1, h1.symm⟩
  by_contra hne
  have hna : (gcdMinors2 (b 0 : ι → ℤ) (b 1 : ι → ℤ)).natAbs ≠ 1 := by
    intro h
    apply hne
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [Nat.cast_one] at hcast
    rw [Int.natAbs_of_nonneg hpos] at hcast
    exact hcast
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hna
  refine hno p hp ?_
  have h1 : (p : ℤ).natAbs ∣ (gcdMinors2 (b 0 : ι → ℤ) (b 1 : ι → ℤ)).natAbs := by
    simpa [Int.natAbs_natCast] using hpdvd
  exact (Int.natAbs_dvd_natAbs).mp h1

end Work.HP
