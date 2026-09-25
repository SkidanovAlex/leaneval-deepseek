import Mathlib
import Submission.NK.Reconstruct.GammaDual
import Submission.NK.GlobalCFT.Place
import Submission.NK.Reconstruct.card_dvd_of_isPGroup_quotient_adicUnits
import Submission.NK.RankTheoryDeep.nsmul_pow_factorization_toZModPow

namespace NK.RankTheoryDeep

/-- **Separation engine for `ℤ_ℓ`-valued characters.**

Let `G` be a commutative (topological, but the topology plays no role) group and `χ : G →+ ℤ_ℓ` an
additive homomorphism.  If there is a single exponent `v` such that for *every* level `m` the
`m`-th reduction `PadicInt.toZModPow m ∘ χ` is killed by `ℓ^v`, then `χ = 0`.

Indeed the family of reductions `PadicInt.toZModPow m` is jointly injective on `ℤ_ℓ`
(`PadicInt.ext_of_toZModPow`), so `ℓ^v • χ a = 0` for every `a`, whence `χ a = 0` because `ℤ_ℓ` is
a domain and `ℓ^v ≠ 0`. -/
theorem eq_zero_of_toZModPow_nsmul_eq_zero {ℓ : ℕ} [Fact ℓ.Prime] {G : Type*} [CommGroup G]
    {χ : Additive G →+ PadicInt ℓ} {v : ℕ}
    (h : ∀ (m : ℕ) (a : Additive G), (ℓ ^ v) • (PadicInt.toZModPow m) (χ a) = 0) : χ = 0 := by
  refine AddMonoidHom.ext fun a => ?_
  have hmain : ((ℓ ^ v : ℕ) : ℤ_[ℓ]) * χ a = 0 := by
    rw [← PadicInt.ext_of_toZModPow]
    intro m
    rw [map_mul, map_natCast, map_zero, ← nsmul_eq_mul]
    exact h m a
  have hne : ((ℓ ^ v : ℕ) : ℤ_[ℓ]) ≠ 0 := by
    rw [Nat.cast_pow]
    exact pow_ne_zero v (Nat.cast_ne_zero.mpr (Fact.out : ℓ.Prime).ne_zero)
  exact (mul_eq_zero.mp hmain).resolve_left hne

/-- **Every continuous character of a local unit group away from `ℓ` is trivial.**

Let `K` be a number field, `Q` a finite place of `K` whose residue field `𝓞_K ⧸ Q` has
characteristic `p ≠ ℓ`, and `𝒪_Qˣ = NK.GlobalCFT.Place.localUnits K (Place.ofFinite Q)` the group of
local units (`= (Q.adicCompletionIntegers K)ˣ`, `Place.localUnits_ofFinite`), with its subspace
topology.  Then

  `NK.Reconstruct.Dual 𝒪_Qˣ ℓ = {f : Additive 𝒪_Qˣ →+ ℤ_ℓ // Continuous f}`

is **trivial**: every continuous homomorphism `𝒪_Qˣ → ℤ_ℓ` is zero.

Proof.  Let `χ : 𝒪_Qˣ → ℤ_ℓ` be continuous and `n ≥ 1`.  The composite
`χ_n := PadicInt.toZModPow n ∘ χ : 𝒪_Qˣ → ℤ/ℓ^n` is continuous with image `P` a finite subgroup of
`ℤ/ℓ^n`, hence a finite `ℓ`-group; by the on-disk
`NK.Reconstruct.card_dvd_of_isPGroup_quotient_adicUnits` (every finite `ℓ`-group quotient of
`𝒪_Qˣ` has order dividing `q - 1`, where `q = #(𝓞_K ⧸ Q)` — proved via Hensel, that `1 + 𝔪` is
`ℓ`-divisible when `p ≠ ℓ`) we get `#P ∣ q - 1`; since `P` is an `ℓ`-group, `#P ∣ ℓ^v` with
`v = v_ℓ(q-1)`.  Hence the image of `χ_n` lies in the subgroup `{y : ℓ^v y = 0}` of `ℤ/ℓ^n`, i.e.
`χ(x) ∈ ℓ^{n-v}ℤ_ℓ` for every `x` and every `n > v`.  Therefore `χ(x) ∈ ⋂_n ℓ^{n-v}ℤ_ℓ = 0` (a
nonzero `ℤ_ℓ`-element has finite `ℓ`-adic valuation), so `χ = 0`.

This is the "`v ∤ ℓ` contributes nothing to the `ℓ`-adic rank" half of item (1) of the request: it
is what makes `Hom_cts(C_K, ℤ_ℓ) ⊆ ⨁_{v | ℓ} Hom_cts(𝒪_vˣ, ℤ_ℓ)`, hence the finiteness of the
`ℤ_ℓ`-rank of `r_ℓ(K) = rank Hom_cts(C_K, ℤ_ℓ)` (CoNF (10.3.20)) and the corrected residual
`NK.RankTheoryDeep.HausQuotRankFinite` — in stark contrast to the naive torsion-free quotient of
`C_K^{pro-ℓ}`, which has rank `ℵ₀` because *finite* groups of unbounded order still admit
non-torsion "diagonal" elements (`RankTheoryDeep/ProductRank.lean`).

The hypotheses are satisfiable (`K = ℚ`, `Q = (3)`, `ℓ = 2`, `p = 3`), and the conclusion is not
automatic: it fails precisely when `p = ℓ` (then `𝒪_Qˣ ⊇ 1 + 𝔪 ≅ ℤ_ℓ` contributes `ℤ_ℓ`; e.g.
`K = ℚ`, `Q = (2)`, `ℓ = 2`).  Since the topology on `𝒪_Qˣ` is the adic one and not discrete,
continuity is a genuine hypothesis. -/
theorem dual_localUnits_eq_zero_of_residueChar_ne {K : Type*} [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
    (hres : CharP (NumberField.RingOfIntegers K ⧸ Q.asIdeal) p) (hne : p ≠ ℓ)
    (χ : NK.Reconstruct.Dual
      (↥(NK.GlobalCFT.Place.localUnits K (NK.GlobalCFT.Place.ofFinite Q))) ℓ) : χ = 0 := by
  classical
  -- Transport `χ` along the canonical isomorphism `𝒪_Qˣ ≅ (𝒪_{K_Q})ˣ` to the units of the
  -- `Q`-adic integers.
  let e := Submonoid.unitsEquivUnitsType (Q.adicCompletionIntegers K).toSubmonoid
  let χ' : Additive (Q.adicCompletionIntegers K)ˣ →+ PadicInt ℓ :=
    χ.1.comp (MonoidHom.toAdditive e.symm.toMonoidHom)
  -- At every level `m` the ℓ-th power of the exponent `v = v_ℓ(q - 1)` kills the reduction of `χ`.
  have hχ' : χ' = 0 := by
    refine eq_zero_of_toZModPow_nsmul_eq_zero
      (v := (Nat.card (NumberField.RingOfIntegers K ⧸ Q.asIdeal) - 1).factorization ℓ) ?_
    intro m a
    exact nsmul_pow_factorization_toZModPow Q hres hne m
      ((PadicInt.toZModPow m).toAddMonoidHom.comp χ') a
  -- Deduce `χ = 0`, using that `e` is an isomorphism (hence surjective).
  apply Subtype.ext
  refine AddMonoidHom.ext fun a => ?_
  have key : χ' (MonoidHom.toAdditive e.toMonoidHom a) = χ.1 a := by
    show χ.1 (MonoidHom.toAdditive e.symm.toMonoidHom (MonoidHom.toAdditive e.toMonoidHom a))
      = χ.1 a
    congr 1
  have h2 : χ' (MonoidHom.toAdditive e.toMonoidHom a) = 0 := by
    rw [hχ']; rfl
  rwa [key] at h2

end NK.RankTheoryDeep
