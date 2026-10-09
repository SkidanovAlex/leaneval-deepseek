/-
Work of the Neukirch–Uchida team: the general Čebotarev density theorem.

# The existence form of Čebotarev's theorem

This file proves the existence form `ChebotarevInfinite` of Čebotarev's theorem from its abelian
case `AbelianChebotarevDensity` and the *ascent* half of the transfer step
(`NK.ChebotarevGeneral.exists_isFrobAt_of_isFrobAtPrime_under`) together with the analytic
fact that the primes of a number field of residue degree at least two contribute a bounded
amount to the Dirichlet series (`NK.ChebotarevGeneral.summable_zetaWeight_of_inertiaDeg_ge_two`).

The argument is Deuring's transfer, but only in the *existence* form, which avoids the exact
fibre count of the transfer:  let `N/K` be finite Galois, `σ : Gal(N/K)`, `H = ⟨σ⟩` and
`M = N^H`.  The abelian case applied to the cyclic extension `N/M` gives a set `S` of primes of
`M` of Dirichlet density `1/|H| > 0`, namely those at which `σ` is a Frobenius element of `N/M`;
in particular the partial Dirichlet series over `S` tends to `+∞`.  If the Frobenius set of `σ`
in `K` (the set `T` of primes of `K` at which `σ` is a Frobenius element of `N/K`) were finite,
then every prime of `M` above a prime outside `T` would have residue degree at least two over `K`
(by the ascent lemma), so the primes of `M` above primes outside `T` would contribute a bounded
amount; the finitely many primes of `M` above primes in `T` also contribute a bounded amount.
That would make the partial Dirichlet series over `S` bounded, a contradiction.
-/
import Mathlib
import Submission.NK.ChebotarevGeneral.Basic
import Submission.NK.ChebotarevGeneral.RatLevel
import Submission.NK.ChebotarevGeneral.exists_isFrobAt_of_isFrobAtPrime_under
import Submission.NK.ChebotarevGeneral.summable_zetaWeight_of_inertiaDeg_ge_two
import Submission.Commons.NumberTheory.NumberField.finite_primesOver
import Submission.Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_union_of_disjoint
import Submission.Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_univ_nhdsGT
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace NK.ChebotarevGeneral

noncomputable section

open NK.Chebotarev Filter
open scoped Topology

/-! ## A positive-density set has a divergent partial Dirichlet series -/

/-- **A set of positive Dirichlet density has a partial Dirichlet series tending to `+∞`.** -/
theorem tendsto_primeIdealZetaSum_of_hasDirichletDensity {K : Type*} [Field K] [NumberField K]
    {S : Set (NK.Chebotarev.PrimeIdeal K)} {δ : ℝ}
    (h : NumberField.Set.HasDirichletDensity S δ) (hδ : 0 < δ) :
    Tendsto (fun s : ℝ => NumberField.Set.primeIdealZetaSum S s) (𝓝[>] (1 : ℝ)) atTop := by
  have huniv : Tendsto (fun s : ℝ => NumberField.Set.primeIdealZetaSum
      (Set.univ : Set (NK.Chebotarev.PrimeIdeal K)) s) (𝓝[>] (1 : ℝ)) atTop :=
    Commons.NumberTheory.NumberField.Set.tendsto_primeIdealZetaSum_univ_nhdsGT K
  rw [NumberField.Set.HasDirichletDensity] at h
  -- eventually the ratio exceeds `δ / 2`
  have hev : ∀ᶠ s in 𝓝[>] (1 : ℝ), δ / 2 ≤ NumberField.Set.primeIdealZetaSum S s /
      NumberField.Set.primeIdealZetaSum (Set.univ : Set (NK.Chebotarev.PrimeIdeal K)) s :=
    ((tendsto_order.1 h).1 (δ / 2) (by linarith)).mono fun s hs => le_of_lt hs
  refine tendsto_atTop_mono' _ ?_ (Tendsto.const_mul_atTop (by linarith : (0:ℝ) < δ / 2) huniv)
  filter_upwards [hev, huniv.eventually_gt_atTop 0] with s hs hpos
  have hzero : NumberField.Set.primeIdealZetaSum
      (Set.univ : Set (NK.Chebotarev.PrimeIdeal K)) s ≠ 0 := ne_of_gt hpos
  have hS : NumberField.Set.primeIdealZetaSum S s =
      (NumberField.Set.primeIdealZetaSum S s / NumberField.Set.primeIdealZetaSum
        (Set.univ : Set (NK.Chebotarev.PrimeIdeal K)) s) *
        NumberField.Set.primeIdealZetaSum (Set.univ : Set (NK.Chebotarev.PrimeIdeal K)) s := by
    field_simp
  rw [hS]
  exact mul_le_mul_of_nonneg_right hs (le_of_lt hpos)

/-! ## The ascent half of the transfer -/

section Ascent

variable {K N : Type} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
  [FiniteDimensional K N] [IsGalois K N]

/-- **A prime of an intermediate field with residue degree one over `𝔭` at which the image of `σ` is
a Frobenius element forces `𝔭` to be in the Frobenius set of `σ`.** -/
theorem two_le_inertiaDeg'_of_not_isFrobAtPrime {M : IntermediateField K N} {σ : Gal(N/K)}
    (hσ : σ ∈ M.fixingSubgroup) {𝔭 : NK.Chebotarev.PrimeIdeal K}
    {𝒬 : NK.Chebotarev.PrimeIdeal ↥M} (hQ : 𝒬.asIdeal.LiesOver 𝔭.asIdeal)
    (hnot : ¬ NK.Chebotarev.IsFrobAtPrime (K := K) (L := N) 𝔭 σ)
    (hfrob : NK.Chebotarev.IsFrobAtPrime (K := ↥M) (L := N) 𝒬
      (M.fixingSubgroupEquiv ⟨σ, hσ⟩)) :
    2 ≤ 𝔭.asIdeal.inertiaDeg' 𝒬.asIdeal := by
  by_contra h
  haveI := hQ
  have hpos : 0 < 𝔭.asIdeal.inertiaDeg' 𝒬.asIdeal :=
    Ideal.inertiaDeg'_pos 𝔭.asIdeal 𝒬.asIdeal
  have h1 : 𝔭.asIdeal.inertiaDeg' 𝒬.asIdeal = 1 := by omega
  exact hnot (exists_isFrobAt_of_isFrobAtPrime_under M hQ h1 hσ hfrob)

end Ascent

/-! ## The existence form of Čebotarev's theorem -/

section Main

variable {K N : Type} [Field K] [NumberField K] [Field N] [NumberField N] [Algebra K N]
  [FiniteDimensional K N] [IsGalois K N]

/-- **The cyclic case implies the general case, in existence form.** -/
theorem infinite_frobSet_of_abelian (h_ab : AbelianChebotarevDensity) : ChebotarevInfinite := by
  classical
  intro K N _ _ _ _ _ _ _ σ
  -- the cyclic level `M = N^⟨σ⟩`
  set H : Subgroup Gal(N/K) := Subgroup.zpowers σ with hH
  set M : IntermediateField K N := IntermediateField.fixedField H with hM
  have hfix : M.fixingSubgroup = H := by
    rw [hM, hH]
    exact IntermediateField.fixingSubgroup_fixedField H
  have hσ : σ ∈ M.fixingSubgroup := by rw [hfix]; exact Subgroup.mem_zpowers σ
  set S : Set (NK.Chebotarev.PrimeIdeal ↥M) := frobSetSub (K := K) (N := N) M σ hσ with hS
  -- the abelian case gives density `1/|H|` for the primes of `M` at which `σ` is a Frobenius
  have hd : NumberField.Set.HasDirichletDensity S
      (1 / (Nat.card (Subgroup.zpowers σ) : ℝ)) := by
    rw [hS]
    exact hasDirichletDensity_frobSetSub_of_abelian (K := K) (N := N) h_ab σ
  have hδ : 0 < 1 / (Nat.card (Subgroup.zpowers σ) : ℝ) := by
    have h1 : 0 < Nat.card ↥(Subgroup.zpowers σ) := Nat.card_pos
    positivity
  have htend : Tendsto (fun s : ℝ => NumberField.Set.primeIdealZetaSum S s) (𝓝[>] (1 : ℝ)) atTop :=
    tendsto_primeIdealZetaSum_of_hasDirichletDensity hd hδ
  -- suppose that `σ` is a Frobenius element at only finitely many primes of `K`
  by_contra hfin
  -- the finitely many primes of `M` above the primes of `K` at which `σ` is a Frobenius
  set A : Set (NK.Chebotarev.PrimeIdeal ↥M) :=
    {𝒬 | ∃ 𝔭 ∈ frobSet (K := K) (N := N) σ, 𝒬.asIdeal.LiesOver 𝔭.asIdeal} with hA
  have hAfin : A.Finite := by
    rw [hA]
    refine (Set.Finite.biUnion (Set.not_infinite.mp hfin)
      (fun 𝔭 _ => finite_setOf_liesOver 𝔭)).subset ?_
    rintro 𝒬 ⟨𝔭, h𝔭, hlies⟩
    exact Set.mem_biUnion h𝔭 hlies
  -- the remaining primes of `S`
  set T : Set (NK.Chebotarev.PrimeIdeal ↥M) := S \ A with hT
  -- the primes of residue degree at least two contribute a bounded amount
  set C : ℝ := ∑' 𝒬 : NK.Chebotarev.PrimeIdeal ↥M,
    (if 2 ≤ (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal
      then ((Ideal.absNorm 𝒬.asIdeal : ℝ) ^ (-(3 / 4 : ℝ))) else 0) with hC
  have hsumm : Summable (fun 𝒬 : NK.Chebotarev.PrimeIdeal ↥M =>
      if 2 ≤ (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal
        then ((Ideal.absNorm 𝒬.asIdeal : ℝ) ^ (-(3 / 4 : ℝ))) else 0) :=
    summable_zetaWeight_of_inertiaDeg_ge_two (K := K) (M := ↥M) (by norm_num)
  -- every prime of `T` has residue degree at least two
  have hdeg : ∀ 𝒬 ∈ T,
      2 ≤ (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal).inertiaDeg' 𝒬.asIdeal := by
    intro 𝒬 h𝒬
    rw [hT] at h𝒬
    have hmemS : 𝒬 ∈ S := h𝒬.1
    have hnotA : 𝒬 ∉ A := h𝒬.2
    have hfrob : NK.Chebotarev.IsFrobAtPrime (K := ↥M) (L := N) 𝒬
        (M.fixingSubgroupEquiv ⟨σ, hσ⟩) := hmemS
    have hlies : 𝒬.asIdeal.LiesOver (Ideal.under (NumberField.RingOfIntegers K) 𝒬.asIdeal) :=
      (Ideal.liesOver_iff _ _).mpr rfl
    have hnot : ¬ NK.Chebotarev.IsFrobAtPrime (K := K) (L := N)
        (IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬) σ := by
      intro hcon
      refine hnotA ?_
      rw [hA]
      refine ⟨IsDedekindDomain.HeightOneSpectrum.under (NumberField.RingOfIntegers K) 𝒬,
        hcon, ?_⟩
      rwa [IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
    have hres := two_le_inertiaDeg'_of_not_isFrobAtPrime (M := M) hσ hlies hnot hfrob
    rwa [IsDedekindDomain.HeightOneSpectrum.under_asIdeal] at hres
  -- the primes of `T` contribute at most `C`
  have h2C : ∀ s : ℝ, 1 < s → NumberField.Set.primeIdealZetaSum T s ≤ C := by
    intro s hs
    have hsumM : Summable (fun 𝒬 : NK.Chebotarev.PrimeIdeal ↥M =>
        (Ideal.absNorm 𝒬.asIdeal : ℝ) ^ (-s)) :=
      Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum hs
    have hsumA : Summable (fun b : T => (Ideal.absNorm b.1.asIdeal : ℝ) ^ (-s)) :=
      hsumM.subtype _
    have hsumB : Summable (fun b : T =>
        if 2 ≤ (Ideal.under (NumberField.RingOfIntegers K) b.1.asIdeal).inertiaDeg' b.1.asIdeal
          then ((Ideal.absNorm b.1.asIdeal : ℝ) ^ (-(3 / 4 : ℝ))) else 0) := hsumm.subtype _
    rw [NumberField.Set.primeIdealZetaSum_def, hC]
    refine le_trans (Summable.tsum_le_tsum (fun b => ?_) hsumA hsumB) ?_
    · rw [if_pos (hdeg b.1 b.2)]
      refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr fun h0 =>
        b.1.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))
    · refine Summable.tsum_subtype_le _ _ (fun a => ?_) hsumm
      by_cases hc : 2 ≤ (Ideal.under (NumberField.RingOfIntegers K) a.asIdeal).inertiaDeg' a.asIdeal
      · simp only [hc, ↓reduceIte]
        exact Real.rpow_nonneg (by positivity) _
      · simp only [hc, ↓reduceIte]
        exact le_refl 0
  -- hence the partial Dirichlet series over `S` is bounded
  have hupper : ∀ s : ℝ, 1 < s → NumberField.Set.primeIdealZetaSum S s ≤
      (S ∩ A).ncard + C := by
    intro s hs
    have hsumM : Summable (fun 𝒬 : NK.Chebotarev.PrimeIdeal ↥M =>
        (Ideal.absNorm 𝒬.asIdeal : ℝ) ^ (-s)) :=
      Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum hs
    have hsplit := Commons.NumberTheory.NumberField.Set.primeIdealZetaSum_union_of_disjoint
      (S := S ∩ A) (T := T) (Set.disjoint_left.mpr fun x hx hx' => by
        rw [hT] at hx'; exact hx'.2 hx.2) s
      (hsumM.subtype _) (hsumM.subtype _)
    have hunion : (S ∩ A) ∪ T = S := by
      rw [hT]
      exact Set.inter_union_sdiff S A
    rw [hunion] at hsplit
    rw [hsplit]
    have h1 : NumberField.Set.primeIdealZetaSum (S ∩ A) s ≤ ((S ∩ A).ncard : ℝ) :=
      NumberField.Set.primeIdealZetaSum_le_card_of_finite (hAfin.subset Set.inter_subset_right)
        (by linarith)
    have h2 := h2C s hs
    linarith
  -- contradiction: the series tends to `+∞` but is bounded
  obtain ⟨s, hsbig, hs1⟩ := ((htend.eventually_ge_atTop ((S ∩ A).ncard + C + 1)).and
    (self_mem_nhdsWithin : Set.Ioi (1 : ℝ) ∈ 𝓝[>] (1 : ℝ))).exists
  have hs1' : 1 < s := hs1
  have := hupper s hs1'
  linarith

end Main

end

end NK.ChebotarevGeneral
