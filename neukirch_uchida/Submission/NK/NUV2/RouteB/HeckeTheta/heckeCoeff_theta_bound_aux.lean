/-
# The Hecke partial-sum bound for a non-trivial ray class character

This is the analytic heart of the Hecke-theta route to `NK.NUV2.RouteB.heckeCoeff_theta_bound`:
for an *open* subgroup `U ≤ 𝕀 K` with finite ray class group, a finite set `S` of primes and a
ray class character `χ ≠ 1`, the partial sums of the coefficients `heckeCoeff K U S χ` of the Hecke
`L`-series of `χ` are `O(N^θ)` for some `θ < 1`.

The proof is the classical equidistribution argument, assembled from the following pieces.

* `NK.NUV2.RouteB.RayModulus.exists_modulus_le`: an open `U` contains a congruence subgroup
  `U(𝔪)`; enlarging the modulus by the primes of `S` (so that its support contains `S`) keeps this
  inclusion (`enlargeMod` below).
* `NK.NUV2.RouteB.HeckeTheta.sharpSub_of_dictionary` (this repository): the *sharp* ray-class
  count for a congruence subgroup — the dictionary identity
  `NK.NUV2.RouteB.HeckeTheta.rayClassCnt_eq_coset_sum` together with the sharp lattice-coset
  count `NK.NUV2.RouteB.HeckeTheta.cosetConeCnt_sharp` — gives
  `|A_{c₁}(X) - A_{c₂}(X)| ≤ C X^{1-1/[K:ℚ]}` for ideals coprime to the support of `𝔪`.
  The main terms cancel because `N𝔡 · covol(𝔪𝔡⁻¹)` does not depend on `𝔡`.
* `NK.NUV2.RouteB.SharpCount.of_le` (proved): a power-saving bound for a *finer* subgroup
  transfers to any coarser subgroup, since the class counts are sums over the fibres of a surjection
  of finite groups, whose fibres all have the same cardinality.
* `NK.NUV2.RouteB.uniform_of_sharp_aux` (proved): the passage from the sharp bound for a set `S'`
  containing `S` to a power saving for an arbitrary finite set `S` (the Euler factors supported on
  `S'∖S` cost at most `N^ε`, absorbed by lowering the exponent).
* `NK.NUV2.RouteB.heckePartialSum_of_uniformCount` (proved): the equidistribution of ideals in the
  ray classes of `U` implies the partial-sum bound, by grouping the coefficients by ray class and
  using `∑_c χ(c) = 0` for `χ ≠ 1`.

The hypotheses `𝔪`, `hcong` and `hprime` of the statement are not needed by this route (the
existence of a modulus for `U` and the non-triviality of `χ` suffice); they are kept so that the
statement can be used exactly as requested.
-/
import Mathlib
import Submission.NK.HeckeL.Basic
import Submission.NK.NUV2.RouteB.HeckeTheta.Defs
import Submission.NK.NUV2.RouteB.HeckeTheta.DictTools
import Submission.NK.NUV2.RouteB.HeckeTheta.sharpSub_of_dictionary
import Submission.NK.NUV2.RouteB.HeckeTheta.rayClassCnt_eq_coset_sum
import Submission.NK.NUV2.RouteB.RayModulus.exists_modulus_le
import Submission.NK.NUV2.HeckeAnalytic.Transfer
import Submission.NK.NUV2.HeckeAnalytic.finite_congSubgroup_rayClassGroup
import Submission.NK.NUV2.RouteB.uniform_of_sharp_rayClassCount
import Submission.NK.NUV2.RouteB.heckePartialSum_uniform
import Submission.NK.NUV2.RouteB.CongCount.CongRayAux

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open NumberField IsDedekindDomain
open scoped Classical BigOperators

namespace NK.NUV2.RouteB.HeckeTheta

/-- Enlargement of a modulus by the primes of `S`: the exponents are raised to at least one at the
primes of `S` (so that the support contains `S`), the archimedean conditions are untouched. -/
noncomputable def enlargeMod (K : Type) [Field K] [NumberField K]
    (𝔪 : NK.NUV2.RouteB.Modulus K) (S : Finset (NK.HeckeL.PrimeIdeal K)) :
    NK.NUV2.RouteB.Modulus K where
  exps q := if q ∈ S then max (𝔪.exps q) 1 else 𝔪.exps q
  finite_support := by
    rw [NK.NUV2.RouteB.HasFiniteSupport]
    have h2 : ∀ᶠ q in Filter.cofinite, q ∉ S := by
      rw [Filter.eventually_cofinite]
      simpa using S.finite_toSet
    filter_upwards [𝔪.finite_support, h2] with q hq hqS
    rw [if_neg hqS, hq]
  pos := 𝔪.pos

theorem enlargeMod_exps (K : Type) [Field K] [NumberField K]
    (𝔪 : NK.NUV2.RouteB.Modulus K) (S : Finset (NK.HeckeL.PrimeIdeal K))
    (q : NK.HeckeL.PrimeIdeal K) :
    (enlargeMod K 𝔪 S).exps q = if q ∈ S then max (𝔪.exps q) 1 else 𝔪.exps q := rfl

theorem enlargeMod_pos (K : Type) [Field K] [NumberField K]
    (𝔪 : NK.NUV2.RouteB.Modulus K) (S : Finset (NK.HeckeL.PrimeIdeal K)) :
    (enlargeMod K 𝔪 S).pos = 𝔪.pos := rfl

theorem heckeCoeff_theta_bound_aux (K : Type) [Field K] [NumberField K]
    (U : Subgroup (NK.GlobalCFT.Idele K)) (hU : IsOpen (U : Set (NK.GlobalCFT.Idele K)))
    (hfin : Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U))
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ 0)
    (hcong : ∀ γ : NumberField.RingOfIntegers K, γ - 1 ∈ 𝔪 →
      NK.NUV2.RouteB.HeckeTheta.IsTotallyPositive γ →
      NK.HeckeL.classOfIdeal K U (Ideal.span {γ}) = 1)
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (χ : NK.HeckeL.RayChar K U) (hχ : χ ≠ 1)
    (hprime : ∃ 𝔮 : NK.HeckeL.PrimeIdeal K, ¬ 𝔮.asIdeal ∣ 𝔪 ∧
      χ (NK.HeckeL.classOfIdeal K U 𝔮.asIdeal) ≠ 1) :
    ∃ C θ : ℝ, 0 < C ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ N : ℕ, 1 ≤ N →
      ‖∑ k ∈ Finset.Icc 1 N, NK.HeckeL.heckeCoeff K U S χ k‖ ≤ C * (N : ℝ) ^ θ := by
  classical
  letI : Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U) := hfin
  -- the sharp ray-class count for congruence subgroups
  have hCrux : ∀ (𝔫 : NK.NUV2.RouteB.Modulus K),
      NK.NUV2.RouteB.SharpSub K (NK.NUV2.RouteB.CongSubgroup K 𝔫) 𝔫.supportFinset
        (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) := fun 𝔫 =>
    NK.NUV2.RouteB.HeckeTheta.sharpSub_of_dictionary K 𝔫
      (fun 𝔡 h𝔡 hcop X =>
        NK.NUV2.RouteB.HeckeTheta.rayClassCnt_eq_coset_sum K 𝔫 𝔡 h𝔡 hcop X)
  -- a modulus for `U` whose support contains `S`
  obtain ⟨𝔪₀, h𝔪₀⟩ := NK.NUV2.RouteB.RayModulus.exists_modulus_le K U hU
  set 𝔫 : NK.NUV2.RouteB.Modulus K := enlargeMod K 𝔪₀ S with h𝔫def
  have hle : NK.NUV2.RouteB.CongSubgroup K 𝔫 ≤ U := by
    refine le_trans (NK.NUV2.RouteB.CongCount.congSubgroup_le_of_exps_le (fun q => ?_)
      (enlargeMod_pos K 𝔪₀ S)) h𝔪₀
    rw [enlargeMod_exps]
    split_ifs with hq
    · exact le_max_left _ _
    · exact le_rfl
  have hSsub : S ⊆ 𝔫.supportFinset := by
    intro q hq
    refine 𝔫.mem_supportFinset ?_
    rw [h𝔫def, enlargeMod_exps]
    simp [hq]
  haveI hfinC : Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K
      (NK.NUV2.RouteB.CongSubgroup K 𝔫)) :=
    NK.NUV2.HeckeAnalytic.finite_congSubgroup_rayClassGroup K 𝔫
  have hθ0 : (0 : ℝ) ≤ 1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ) := by
    have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
      exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
    have h1 : (1 : ℝ) / (Module.finrank ℚ K : ℝ) ≤ 1 := by
      rw [div_le_one hn]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Module.finrank_pos (R := ℚ) (M := K)).ne')
    linarith
  -- transfer the sharp bound from `U(𝔫)` to `U`
  have hsharpU : NK.NUV2.RouteB.SharpSub K U 𝔫.supportFinset
      (1 - (1 : ℝ) / (Module.finrank ℚ K : ℝ)) :=
    NK.NUV2.RouteB.SharpCount.to_natCard
      (NK.NUV2.RouteB.SharpCount.of_le (V := NK.NUV2.RouteB.CongSubgroup K 𝔫) (W := U)
        hle (NK.NUV2.RouteB.SharpCount.of_natCard (hCrux 𝔫))) hθ0
  -- absorb the primes of `S`
  obtain ⟨C, θc, hCpos, hθclt, hbd⟩ :=
    NK.NUV2.RouteB.uniform_of_sharp_aux (K := K) U S 𝔫.supportFinset hSsub hsharpU
      (fun ε hε => NK.NUV2.RouteB.Unif.card_supported_le K (𝔫.supportFinset \ S) ε hε)
  -- assemble the equidistribution input of Hecke's partial-sum bound
  have hC' : ∃ (C θ : ℝ), 0 < C ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ X : ℝ, 1 ≤ X →
      ∀ c₁ c₂ : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U,
        |((Nat.card {𝔞 : Ideal (NumberField.RingOfIntegers K) //
              𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
              NK.HeckeL.classOfIdeal K U 𝔞 = c₁ ∧ Ideal.absNorm 𝔞 ≤ X} : ℝ)
        - (Nat.card {𝔞 : Ideal (NumberField.RingOfIntegers K) //
              𝔞 ≠ 0 ∧ (∀ 𝔭 ∈ S, ¬ 𝔭.asIdeal ∣ 𝔞) ∧
              NK.HeckeL.classOfIdeal K U 𝔞 = c₂ ∧ Ideal.absNorm 𝔞 ≤ X} : ℝ))|
      ≤ C * X ^ θ :=
    ⟨C, max θc 0, hCpos, le_max_right _ _, max_lt hθclt one_pos, fun X hX c₁ c₂ =>
      (hbd X hX c₁ c₂).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX (le_max_left θc 0)) hCpos.le)⟩
  exact NK.NUV2.RouteB.heckePartialSum_of_uniformCount K U S χ hχ hC'

end NK.NUV2.RouteB.HeckeTheta
