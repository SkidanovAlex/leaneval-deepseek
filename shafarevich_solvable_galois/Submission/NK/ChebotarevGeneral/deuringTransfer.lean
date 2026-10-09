/-
Work of the Neukirch–Uchida team: the general Čebotarev density theorem.

# The density form of the transfer step (Deuring)

The main theorem of this file is `NK.ChebotarevGeneral.deuringTransfer`, the analytic transfer
step of Deuring's proof of Čebotarev's density theorem: the cyclic (abelian) case of Čebotarev
implies the general case.

The proof is the classical one.  Let `N/K` be a finite Galois extension of number fields,
`σ : Gal(N/K)`, `H = ⟨σ⟩` and `M = N^H`.  Write

* `SM` for the set of primes of `M` at which `σ` is a Frobenius element of `N/M` (whose Dirichlet
  density `1/|H|` is the hypothesis),
* `Su ⊆ SM` for the subset of those primes of residue degree one over the prime of `K` below, lying
  over a prime of `K` unramified in `N`,
* `T` for the set of primes of `K` at which `σ` is a Frobenius element of `N/K`, and
  `Tu = T ∩ {unramified}`.

Then

* each `𝔭 ∈ Tu` has exactly `|C_G(σ)|/ord(σ)` primes of `Su` above it
  (`card_fibre_frobSetSub_mul_orderOf`), and no prime outside `Tu` has one
  (`card_fibre_frobSetSub_eq_zero_of_not`), so `Z(Su) * ord(σ) = |C_G(σ)| * Z(Tu)` for the partial
  Dirichlet series (`primeIdealZetaSum_mul_of_fibre_card`);
* `SM ∖ Su` contributes a bounded amount, being contained in the primes of residue degree at least
  two together with the primes above the finitely many ramified primes
  (`exists_bound_primeIdealZetaSum_of_inertiaDeg_or_mem_finite`);
* hence the series `Z(Su)/log (1/(s-1))` still tends to `1/|H|`, and therefore
  `Z(Tu)/log (1/(s-1)) → 1/|C_G(σ)|`; this is the Dirichlet density of `Tu`
  (`hasDirichletDensity_of_tendsto_primeIdealZetaSum_div_log`);
* finally `Tu` differs from `T` by the finitely many primes ramified in `N`, so `T` has the same
  density (`NK.Chebotarev.HasDirichletDensitySensitivity`).
-/
import Mathlib
import Submission.NK.ChebotarevGeneral.Defs
import Submission.NK.ChebotarevGeneral.DensityAux
import Submission.NK.ChebotarevGeneral.card_fibre_eq_frobCount
import Submission.NK.ChebotarevGeneral.card_isFrobAt_liesOver_mul_orderOf
import Submission.NK.ChebotarevGeneral.exists_isFrobAt_liesOver_of_isFrobAtPrime_under
import Submission.NK.ChebotarevGeneral.isFrobAtPrime_under_of_isFrobAt
import Submission.NK.ChebotarevGeneral.summable_zetaWeight_of_inertiaDeg_ge_two
import Submission.NK.ChebotarevGeneral.Infinity
import Submission.NK.ChebotarevGeneral.primeIdealZetaSum_mul_of_fibre_card
import Submission.NK.ChebotarevGeneral.exists_bound_primeIdealZetaSum_of_inertiaDeg_or_mem_finite
import Submission.NK.ChebotarevGeneral.hasDirichletDensity_of_tendsto_primeIdealZetaSum_div_log
import Submission.NK.ChebotarevGeneral.card_fibre_frobSetSub_eq_zero_of_not
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ChebotarevGeneral

noncomputable section

open Filter IsDedekindDomain
open NK.Chebotarev
open scoped Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-! ## Two elementary analytic lemmas -/

/-- If `f` is bounded above by a constant `C` and nonnegative near `1⁺`, and `g → +∞` there, then
`f / g → 0`. -/
theorem tendsto_div_atTop_of_eventually_le_const {C : ℝ} {f g : ℝ → ℝ}
    (hg : Tendsto g (𝓝[>] (1 : ℝ)) atTop)
    (hf0 : ∀ᶠ s in 𝓝[>] (1 : ℝ), 0 ≤ f s)
    (hfC : ∀ᶠ s in 𝓝[>] (1 : ℝ), f s ≤ C) :
    Tendsto (fun s => f s / g s) (𝓝[>] (1 : ℝ)) (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ ((tendsto_const_nhds (x := C)).div_atTop hg)
  · filter_upwards [hf0, hg.eventually (eventually_ge_atTop 0)] with s h0 hg0
    exact div_nonneg h0 hg0
  · filter_upwards [hfC, hg.eventually (eventually_ge_atTop 0)] with s hC hg0
    exact div_le_div_of_nonneg_right hC hg0

/-- `log (1/(s-1)) → +∞` as `s → 1⁺`. -/
theorem tendsto_log_one_div_sub_one_nhdsGT :
    Tendsto (fun s : ℝ => Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) atTop := by
  have h1a : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝 ((1 : ℝ) - 1)) :=
    ((continuous_id.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds).sub_const 1
  have h1b : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℝ)) := by simpa using h1a
  have h1 : Tendsto (fun s : ℝ => s - 1) (𝓝[>] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h1b, by
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp only [Set.mem_Ioi] at hs ⊢
      linarith⟩
  have h2 : Tendsto (fun s : ℝ => (s - 1)⁻¹) (𝓝[>] (1 : ℝ)) atTop :=
    tendsto_inv_nhdsGT_zero.comp h1
  refine (Real.tendsto_log_atTop.comp h2).congr' ?_
  filter_upwards with s
  simp only [Function.comp_apply, one_div]



/-! ## The fibre count of the transfer -/

section FibreCount

variable {K N : Type} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
  [FiniteDimensional K N] [IsGalois K N]


/-- **The fibre count at an unramified prime.**  Let `N/K` be a finite Galois extension of number
fields, `σ : Gal(N/K)`, `M` an intermediate field with `M.fixingSubgroup = ⟨σ⟩`, and `𝔭` a prime of
`K` unramified in `N` at which `σ` is a Frobenius element.  Then the number of primes of `𝓞 M`
above `𝔭` of residue degree one over `𝔭` at which the image of `σ` in `Gal(N/M)` is a Frobenius
element, multiplied by `ord(σ)`, is `|C_G(σ)|`.

This is the combination of `card_fibre_eq_frobCount` (the fibres of `N` and of `M` over `𝔭` have
the same size) with `card_isFrobAt_liesOver_mul_orderOf` (the number of Frobenius primes of `N`
above `𝔭` times `ord σ` is `|C_G(σ)|`). -/
theorem deuring_fibre_card_mul_orderOf (M : IntermediateField K N) {σ : Gal(N/K)}
    (hσ : σ ∈ M.fixingSubgroup) (hfix : M.fixingSubgroup = Subgroup.zpowers σ)
    {𝔭 : PrimeIdeal K} (hunr : IsUnramifiedAt (K := K) (N := N) 𝔭)
    (hfrob : IsFrobAtPrime (K := K) (L := N) 𝔭 σ) :
    Nat.card {𝒬 : PrimeIdeal ↥M //
        IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩) ∧
        (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal = 1 ∧
        IsUnramifiedAt (K := K) (N := N)
          (HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬) ∧
        𝒬.asIdeal.LiesOver 𝔭.asIdeal} * orderOf σ
      = Nat.card (Subgroup.centralizer ({σ} : Set (Gal(N/K)))) := by
  classical
  -- the four conjuncts cut out the same set as the three conjuncts of `card_fibre_eq_frobCount`,
  -- because `𝔭` is unramified
  have hcard : Nat.card {𝒬 : PrimeIdeal ↥M //
        IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩) ∧
        (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal = 1 ∧
        IsUnramifiedAt (K := K) (N := N)
          (HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬) ∧
        𝒬.asIdeal.LiesOver 𝔭.asIdeal}
      = Nat.card {𝒬 : PrimeIdeal ↥M // 𝒬.asIdeal.LiesOver 𝔭.asIdeal ∧
        IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩) ∧
        𝔭.asIdeal.inertiaDeg' 𝒬.asIdeal = 1} := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun 𝒬 => ?_)
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h4, h1, ?_⟩
      rw [h4.over]
      exact h2
    · rintro ⟨h4, h1, h2⟩
      have hunder : HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬 = 𝔭 :=
        HeightOneSpectrum.ext (by
          rw [HeightOneSpectrum.under_asIdeal]
          exact h4.over.symm)
      refine ⟨h1, ?_, ?_, h4⟩
      · rw [← h4.over]
        exact h2
      · rw [hunder]
        exact hunr
  rw [hcard, card_fibre_eq_frobCount M hσ hfix hunr]
  exact card_isFrobAt_liesOver_mul_orderOf hunr hfrob

end FibreCount

/-! ## The transfer step -/

/-- **The density form of the transfer step (Deuring).**

Written out, `NK.ChebotarevGeneral.DeuringTransfer` says:  for number fields `K N` with `N/K`
finite Galois and `σ : Gal(N/K)`, putting `H = ⟨σ⟩` and `M = N^H`, if the set of primes of `M` at
which `σ` is a Frobenius element of the extension `N/M` has Dirichlet density `1/ord(σ)`, then the
set of primes of `K` at which `σ` is a Frobenius element of `N/K` has Dirichlet density
`1/|C_G(σ)| = |cl(σ)|/|G|`.

Suggested route, with all the pieces available in this directory (and re-exported by the modules
listed in `depends_on`).

Let `SM := frobSetSub M σ _` (the set of primes of `M` at which `σ` is a Frobenius element of
`N/M`, whose density `1/|H|` is the hypothesis), `Sf ⊆ SM` the subset of primes of residue degree
one over the prime of `K` below, and `Su ⊆ Sf` the subset of those lying over a prime of `K`
unramified in `N`.  Let `T` be the Frobenius set of `σ` in `K` and `Tu := T ∩ {unramified}`.

1. `NK.ChebotarevGeneral.card_fibre_eq_frobCount` gives, for `𝔭` unramified, that the primes of
   `Su` above `𝔭` are in bijection with the primes of `N` above `𝔭` at which `σ` is a Frobenius
   element.
2. `NK.ChebotarevGeneral.card_isFrobAt_liesOver_mul_orderOf` gives that the latter number times
   `ord(σ)` is `|C_G(σ)|`, so each unramified `𝔭 ∈ T` contributes the constant
   `|C_G(σ)|/ord(σ)`.
3. `NK.ChebotarevGeneral.primeIdealZetaSum_eq_tsum_fibre'` (in `DensityAux`) turns the fibre
   counts into the identity `Z(Su) = (|C_G(σ)|/ord σ) * Z(Tu)` of partial Dirichlet series, where
   `Z(S)` is `NumberField.Set.primeIdealZetaSum S`.
4. The complement `SM ∖ Su` contributes a bounded amount:  `SM ∖ Sf` consists of primes of residue
   degree at least two, whose Dirichlet series is summable by
   `NK.ChebotarevGeneral.summable_zetaWeight_of_inertiaDeg_ge_two`, while `Sf ∖ Su` consists of
   primes of `M` above the finitely many primes of `K` ramified in `N`
   (`NK.ChebotarevGeneral.finite_setOf_not_isUnramified` and the finiteness of the primes above a
   fixed prime).
5. The limit algebra:  `Z(SM)/Z_M → 1/|H|` and `Z_M → ∞` give
   `Z(Su)/Z_M → 1/|H|`; `Z(Su)/Real.log (1/(s-1)) → 1/|H|` follows from
   `Z_M/Real.log (1/(s-1)) → 1`, and hence `Z(Tu)/Real.log (1/(s-1)) → 1/|C_G(σ)|`; finally
   `Z(Tu)/Z_K → 1/|C_G(σ)|` using `Z_K/Real.log (1/(s-1)) → 1`
   (`Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_div_log` together with
   `NK.ChebotarevGeneral.hasDirichletDensity_univ`).  Since `Tu` differs from `T` by the finitely
   many ramified primes, `NK.Chebotarev.HasDirichletDensitySensitivity` gives the conclusion with
   the density `frobDensity σ = 1/|C_G(σ)|`.

The final density is `NK.ChebotarevGeneral.frobDensity σ`, and
`NK.ChebotarevGeneral.chebotarevDensity_of_abelian` (`Basic.lean`) consumes this lemma. -/
theorem deuringTransfer : DeuringTransfer := by
  intro K N _ _ _ _ _ _ _ σ hdM
  classical
  -- ## Setup
  set M : IntermediateField K N := IntermediateField.fixedField (Subgroup.zpowers σ) with hMdef
  have hfix : M.fixingSubgroup = Subgroup.zpowers σ := by
    rw [hMdef]; exact IntermediateField.fixingSubgroup_fixedField _
  have hσ : σ ∈ M.fixingSubgroup := by rw [hfix]; exact Subgroup.mem_zpowers σ
  -- the hypothesis, re-expressed with our proof of `σ ∈ M.fixingSubgroup`
  have hdM' : NumberField.Set.HasDirichletDensity (frobSetSub M σ hσ)
      (1 / (Nat.card (Subgroup.zpowers σ) : ℝ)) := by
    convert hdM using 2
  -- the sets occurring in the statement
  set SM : Set (PrimeIdeal ↥M) := frobSetSub M σ hσ with hSMdef
  set Su : Set (PrimeIdeal ↥M) :=
    {𝒬 | IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩) ∧
      (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal = 1 ∧
      IsUnramifiedAt (K := K) (N := N)
        (HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬)} with hSudef
  set Tu : Set (PrimeIdeal K) :=
    {𝔭 | IsFrobAtPrime (K := K) (L := N) 𝔭 σ ∧ IsUnramifiedAt (K := K) (N := N) 𝔭}
    with hTudef
  set T : Set (PrimeIdeal K) := frobSet (K := K) (N := N) σ with hTdef
  set Bad : Set (PrimeIdeal K) := {𝔭 | ¬ IsUnramifiedAt (K := K) (N := N) 𝔭} with hBaddef
  have hSMmem : ∀ 𝒬 : PrimeIdeal ↥M, 𝒬 ∈ SM ↔
      IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩) := by
    intro 𝒬; rw [hSMdef]; exact mem_frobSetSub hσ
  have hSumem : ∀ 𝒬 : PrimeIdeal ↥M, 𝒬 ∈ Su ↔
      IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩) ∧
      (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal = 1 ∧
      IsUnramifiedAt (K := K) (N := N)
        (HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬) := by
    intro 𝒬; rw [hSudef]; exact Iff.rfl
  have hTumem : ∀ 𝔭 : PrimeIdeal K, 𝔭 ∈ Tu ↔
      IsFrobAtPrime (K := K) (L := N) 𝔭 σ ∧ IsUnramifiedAt (K := K) (N := N) 𝔭 := by
    intro 𝔭; rw [hTudef]; exact Iff.rfl
  have hTmem : ∀ 𝔭 : PrimeIdeal K, 𝔭 ∈ T ↔ IsFrobAtPrime (K := K) (L := N) 𝔭 σ := by
    intro 𝔭; rw [hTdef]; exact mem_frobSet
  have hBadmem : ∀ 𝔭 : PrimeIdeal K, 𝔭 ∈ Bad ↔ ¬ IsUnramifiedAt (K := K) (N := N) 𝔭 := by
    intro 𝔭; rw [hBaddef]; exact Iff.rfl
  have hBadfin : Bad.Finite := by
    rw [hBaddef]; exact finite_setOf_not_isUnramified

  -- ## The complement of `Su` in `SM` contributes a bounded amount
  obtain ⟨C₀, hC₀⟩ :=
    exists_bound_primeIdealZetaSum_of_inertiaDeg_or_mem_finite (K := K) (M := ↥M) SM Bad hBadfin
  have hcomp_le : ∀ s : ℝ, 1 < s →
      NumberField.Set.primeIdealZetaSum (SM \ Su) s ≤ max C₀ 0 := by
    intro s hs
    refine le_trans (Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_mono ?_ hs)
      (le_trans (hC₀ s hs) (le_max_left _ _))
    rintro 𝒬 ⟨h𝒬SM, h𝒬Su⟩
    refine ⟨h𝒬SM, ?_⟩
    by_cases hd : (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal = 1
    · right
      intro hunr
      exact h𝒬Su ((hSumem 𝒬).mpr ⟨(hSMmem 𝒬).mp h𝒬SM, hd, hunr⟩)
    · left
      have h1 := one_le_inertiaDeg'_under (K := K) 𝒬
      omega

  -- ## The split of the partial series over `SM`
  have hSuSub : Su ⊆ SM := by
    intro 𝒬 h𝒬
    exact (hSMmem 𝒬).mpr ((hSumem 𝒬).mp h𝒬).1
  have hsplit : ∀ s : ℝ, 1 < s →
      NumberField.Set.primeIdealZetaSum SM s =
        NumberField.Set.primeIdealZetaSum Su s +
          NumberField.Set.primeIdealZetaSum (SM \ Su) s := by
    intro s hs
    have hsumm : Summable fun 𝔭 : PrimeIdeal ↥M =>
        (Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) :=
      Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := ↥M) hs
    calc NumberField.Set.primeIdealZetaSum SM s
        = NumberField.Set.primeIdealZetaSum (Su ∪ (SM \ Su)) s := by
          rw [Set.union_sdiff_cancel hSuSub]
      _ = NumberField.Set.primeIdealZetaSum Su s +
            NumberField.Set.primeIdealZetaSum (SM \ Su) s :=
          Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_union_of_disjoint
            (S := Su) (T := SM \ Su) (Set.disjoint_left.mpr fun x hx hx' => hx'.2 hx) s
            (hsumm.subtype Su) (hsumm.subtype (SM \ Su))

  -- ## The limit of the series over `Su`, divided by `log (1/(s-1))`
  have hSMlog : Tendsto (fun s : ℝ => NumberField.Set.primeIdealZetaSum SM s /
      Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ))
        (𝓝 (1 / (Nat.card (Subgroup.zpowers σ) : ℝ))) :=
    Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_div_log hdM'
  have hcomplog : Tendsto (fun s : ℝ => NumberField.Set.primeIdealZetaSum (SM \ Su) s /
      Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ)) (𝓝 0) :=
    tendsto_div_atTop_of_eventually_le_const (g := fun s : ℝ => Real.log (1 / (s - 1)))
      tendsto_log_one_div_sub_one_nhdsGT
      (Filter.Eventually.of_forall fun s => NumberField.Set.primeIdealZetaSum_nonneg _ s)
      ((show ∀ᶠ s in 𝓝[>] (1 : ℝ), (1 : ℝ) < s from self_mem_nhdsWithin).mono
        fun s hs => hcomp_le s hs)
  have hSulog : Tendsto (fun s : ℝ => NumberField.Set.primeIdealZetaSum Su s /
      Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ))
        (𝓝 (1 / (Nat.card (Subgroup.zpowers σ) : ℝ))) := by
    have h1 : Tendsto (fun s : ℝ => NumberField.Set.primeIdealZetaSum SM s /
          Real.log (1 / (s - 1)) - NumberField.Set.primeIdealZetaSum (SM \ Su) s /
          Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ))
          (𝓝 (1 / (Nat.card (Subgroup.zpowers σ) : ℝ))) := by
      have h := hSMlog.sub hcomplog
      rwa [sub_zero] at h
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hsplit s hs]
    ring

  -- ## The fibre count: `Z(Su) * ord σ = |C_G(σ)| * Z(Tu)`
  have hZmul : ∀ s : ℝ, 1 < s →
      NumberField.Set.primeIdealZetaSum Su s * (orderOf σ : ℝ) =
        (Nat.card (Subgroup.centralizer ({σ} : Set (Gal(N/K)))) : ℝ) *
          NumberField.Set.primeIdealZetaSum Tu s := by
    intro s hs
    refine primeIdealZetaSum_mul_of_fibre_card (K := K) (M := ↥M) (A := Su) (B := Tu)
      (m := orderOf σ) (n := Nat.card (Subgroup.centralizer ({σ} : Set (Gal(N/K))))) ?_ ?_ hs
    · intro 𝒬 h𝒬
      exact ((hSumem 𝒬).mp h𝒬).2.1
    · intro 𝔭
      by_cases h𝔭 : 𝔭 ∈ Tu
      · rw [Set.indicator_of_mem h𝔭]
        have hcard : Nat.card {𝒬 : PrimeIdeal ↥M // 𝒬 ∈ Su ∧ 𝒬.asIdeal.LiesOver 𝔭.asIdeal} =
            Nat.card {𝒬 : PrimeIdeal ↥M //
              IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩) ∧
              (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal = 1 ∧
              IsUnramifiedAt (K := K) (N := N)
                (HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬) ∧
              𝒬.asIdeal.LiesOver 𝔭.asIdeal} :=
          Nat.card_congr (Equiv.subtypeEquivRight fun 𝒬 => by
            rw [hSumem 𝒬]; tauto)
        rw [hcard]
        exact deuring_fibre_card_mul_orderOf M hσ hfix
          ((hTumem 𝔭).mp h𝔭).2 ((hTumem 𝔭).mp h𝔭).1
      · rw [Set.indicator_of_notMem h𝔭]
        have hcard : Nat.card {𝒬 : PrimeIdeal ↥M // 𝒬 ∈ Su ∧ 𝒬.asIdeal.LiesOver 𝔭.asIdeal} =
            Nat.card {𝒬 : PrimeIdeal ↥M //
              IsFrobAtPrime (K := ↥M) (L := N) 𝒬 (M.fixingSubgroupEquiv ⟨σ, hσ⟩) ∧
              (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal = 1 ∧
              IsUnramifiedAt (K := K) (N := N)
                (HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬) ∧
              𝒬.asIdeal.LiesOver 𝔭.asIdeal} :=
          Nat.card_congr (Equiv.subtypeEquivRight fun 𝒬 => by
            rw [hSumem 𝒬]; tauto)
        rw [hcard, card_fibre_frobSetSub_eq_zero_of_not (K := K) (N := N) M hσ
          ((hTumem 𝔭).not.mp h𝔭)]
        ring

  -- ## The limit of the series over `Tu`, divided by `log (1/(s-1))`
  have hTulog : Tendsto (fun s : ℝ => NumberField.Set.primeIdealZetaSum Tu s /
      Real.log (1 / (s - 1))) (𝓝[>] (1 : ℝ))
        (𝓝 (1 / (Nat.card (Subgroup.centralizer ({σ} : Set (Gal(N/K)))) : ℝ))) := by
    have hn : (Nat.card (Subgroup.centralizer ({σ} : Set (Gal(N/K)))) : ℝ) ≠ 0 := by
      have hpos : 0 < Nat.card (Subgroup.centralizer ({σ} : Set (Gal(N/K)))) := Nat.card_pos
      exact_mod_cast hpos.ne'
    have ho : (orderOf σ : ℝ) ≠ 0 := by
      have hpos : 0 < orderOf σ := by
        rw [← Nat.card_zpowers σ]; exact Nat.card_pos
      exact_mod_cast hpos.ne'
    have hlim : ((orderOf σ : ℝ) /
          (Nat.card (Subgroup.centralizer ({σ} : Set (Gal(N/K)))) : ℝ)) *
          (1 / (Nat.card (Subgroup.zpowers σ) : ℝ)) =
        1 / (Nat.card (Subgroup.centralizer ({σ} : Set (Gal(N/K)))) : ℝ) := by
      rw [Nat.card_zpowers σ]
      field_simp
    have h1 : Tendsto (fun s : ℝ => ((orderOf σ : ℝ) /
          (Nat.card (Subgroup.centralizer ({σ} : Set (Gal(N/K)))) : ℝ)) *
          (NumberField.Set.primeIdealZetaSum Su s / Real.log (1 / (s - 1))))
        (𝓝[>] (1 : ℝ))
        (𝓝 (1 / (Nat.card (Subgroup.centralizer ({σ} : Set (Gal(N/K)))) : ℝ))) := by
      have h := hSulog.const_mul ((orderOf σ : ℝ) /
        (Nat.card (Subgroup.centralizer ({σ} : Set (Gal(N/K)))) : ℝ))
      rwa [hlim] at h
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hz := hZmul s hs
    have hstep : NumberField.Set.primeIdealZetaSum Tu s =
        ((orderOf σ : ℝ) /
          (Nat.card (Subgroup.centralizer ({σ} : Set (Gal(N/K)))) : ℝ)) *
          NumberField.Set.primeIdealZetaSum Su s := by
      rw [div_mul_eq_mul_div, eq_div_iff hn]
      rw [mul_comm (NumberField.Set.primeIdealZetaSum Tu s), ← hz, mul_comm]
    rw [hstep]; ring

  -- ## The density of `Tu`
  have hTudens : NumberField.Set.HasDirichletDensity Tu (frobDensity (K := K) (N := N) σ) :=
    hasDirichletDensity_of_tendsto_primeIdealZetaSum_div_log hTulog

  -- ## `Tu` differs from `T` only at the finitely many ramified primes
  have hsymm : (Tu \ T ∪ T \ Tu).Finite := by
    have h1 : Tu \ T = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro 𝔭 ⟨h𝔭Tu, h𝔭T⟩
      exact h𝔭T ((hTmem 𝔭).mpr ((hTumem 𝔭).mp h𝔭Tu).1)
    have h2 : T \ Tu ⊆ Bad := by
      rintro 𝔭 ⟨h𝔭T, h𝔭Tu⟩
      rw [hBadmem]
      intro hunr
      exact h𝔭Tu ((hTumem 𝔭).mpr ⟨(hTmem 𝔭).mp h𝔭T, hunr⟩)
    rw [h1, Set.empty_union]
    exact hBadfin.subset h2
  exact NK.Chebotarev.HasDirichletDensitySensitivity hsymm hTudens

end

end NK.ChebotarevGeneral
