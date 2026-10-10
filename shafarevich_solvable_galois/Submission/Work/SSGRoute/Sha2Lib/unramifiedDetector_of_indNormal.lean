import Mathlib.RepresentationTheory.Induced
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Submission.NK.TameStructureDeep.Tame.InertiaFieldAux
import Submission.Work.SSGRoute.InertiaDefs
import Submission.Work.SSGRoute.LTDDefs.Basic
import Submission.Work.Sha2Lib.isUnramifiedDetector_of_ind
import Submission.Work.Sha2Lib.normalClosure_inertia_acts_trivially
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

/-! ## Inertia elements fix the `p`-th roots of unity

The lemma `aux_isInertiaAt_apply_pow_eq_one` below is the arithmetic input of the assembly: an
inertia element at a finite place `q` with `p ∉ q` fixes every `p`-th root of unity lying in `K`.
It is the `ζ`-hypothesis `hNζ` required by the dispatched node `unramifiedDetector_indNormal` (for
the normal closure of the inertia group).

The proof is the standard reduction-modulo-`q` argument, phrased entirely inside `𝓞 K` so that the
ideal membership of the inertia condition can be handed to the elementary Lemma
`aux_eq_of_pow_eq_one_of_sub_mem` (`x ^ p = y ^ p = 1` and `x - y ∈ Q` with `(p : R) ∉ Q` force
`x = y` in a domain). -/

set_option backward.isDefEq.respectTransparency false in
/-- **A root of unity congruent to `1` modulo an ideal away from `p` is `1`.**

In a domain `R`, if `y ^ p = 1` and `y - 1 ∈ Q` for an ideal `Q` with `(p : R) ∉ Q`, then `y = 1`:
`y ≠ 1` gives `∑_{i<p} y ^ i = 0` by the geometric sum (here `R` is a domain) while `y ≡ 1 (mod Q)`
gives `∑_{i<p} y ^ i ≡ p (mod Q)`, so `p ∈ Q`, a contradiction. -/
private lemma aux_eq_one_of_pow_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsDomain R] {p : ℕ}
    (Q : Ideal R) (hpQ : (p : R) ∉ Q) {y : R} (hy : y ^ p = 1) (hy1 : y - 1 ∈ Q) : y = 1 := by
  by_contra hne
  have hneq : y - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hsum : (∑ i ∈ Finset.range p, y ^ i) = 0 := by
    have h := mul_geom_sum y p
    rw [hy, sub_self] at h
    rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hneq
    · exact h'
  have hmem : (∑ i ∈ Finset.range p, y ^ i) - (p : R) ∈ Q := by
    have h1 : (∑ i ∈ Finset.range p, (y ^ i - 1)) ∈ Q :=
      Ideal.sum_mem _ fun i _ => by
        have heq : y ^ i - 1 = (∑ j ∈ Finset.range i, y ^ j) * (y - 1) := by
          rw [mul_comm]
          exact (mul_geom_sum y i).symm
        rw [heq]
        exact Ideal.mul_mem_left Q _ hy1
    have h2 : (∑ i ∈ Finset.range p, (y ^ i - 1)) =
        (∑ i ∈ Finset.range p, y ^ i) - (∑ _i ∈ Finset.range p, (1 : R)) :=
      Finset.sum_sub_distrib (fun i => y ^ i) (fun _ => (1 : R))
    have hone : (∑ _i ∈ Finset.range p, (1 : R)) = (p : R) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [h2, hone] at h1
    exact h1
  rw [hsum, zero_sub] at hmem
  exact hpQ (by simpa using Q.neg_mem hmem)

set_option backward.isDefEq.respectTransparency false in
/-- **Two congruent `p`-th roots of unity in a domain are equal.**

If `u ^ p = v ^ p = 1` and `u - v ∈ Q` with `(p : R) ∉ Q`, then `u = v`.  Indeed
`y := u * v ^ (p - 1)` satisfies `y ^ p = 1` and `y - 1 = v ^ (p - 1) * (u - v) ∈ Q` (using `p > 0`
so that `v ^ (p - 1) * v = v ^ p = 1`), so `y = 1` by `aux_eq_one_of_pow_eq_one_of_sub_mem`; then
`u = y * v = v`. -/
private lemma aux_eq_of_pow_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsDomain R] {p : ℕ}
    (hp0 : p ≠ 0) (Q : Ideal R) (hpQ : (p : R) ∉ Q) {u v : R} (hu : u ^ p = 1) (hv : v ^ p = 1)
    (hmem : u - v ∈ Q) : u = v := by
  have hp1 : 1 ≤ p := Nat.one_le_iff_ne_zero.mpr hp0
  have hsplit : v ^ (p - 1) * v = v ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel hp1]
  have hy : (u * v ^ (p - 1)) ^ p = 1 := by
    rw [mul_pow, hu, one_mul, ← pow_mul, Nat.mul_comm, pow_mul, hv, one_pow]
  have hy1 : u * v ^ (p - 1) - 1 ∈ Q := by
    have heq : u * v ^ (p - 1) - 1 = v ^ (p - 1) * (u - v) := by
      rw [← hv, ← hsplit]
      ring
    rw [heq]
    exact Ideal.mul_mem_left Q _ hmem
  have hone : u * v ^ (p - 1) = 1 := aux_eq_one_of_pow_eq_one_of_sub_mem Q hpQ hy hy1
  have hfin : u * v ^ (p - 1) * v = v := by rw [hone, one_mul]
  rwa [mul_assoc, hsplit, hv, mul_one] at hfin

set_option backward.isDefEq.respectTransparency false in
/-- **The inertia at `q` fixes the `p`-th roots of unity, when `p` is a unit at `q`.**

Let `k ⊆ K` be a finite Galois extension of number fields, `q` a finite place of `K` with
`p ∉ q`, and `σ` acting trivially on the residue field of `q`. Then `σ ξ = ξ` for every
`ξ ∈ K` with `ξ ^ p = 1`.

Indeed `ξ` is a root of the monic `X ^ p - 1`, hence a unit of `𝓞 K` (and `σ ξ` lies in `𝓞 K`), and
`σ ξ ≡ ξ (mod q)`, so Lemma `aux_eq_of_pow_eq_one_of_sub_mem` applied to the two `p`-th roots of
unity `σ ξ` and `ξ` of `𝓞 K` gives `σ ξ = ξ`. -/
private lemma aux_isInertiaAt_apply_pow_eq_one {p : ℕ} (hp0 : p ≠ 0) {k K : Type} [Field k]
    [Field K] [NumberField K] [Algebra k K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (σ : K ≃ₐ[k] K) (hσ : SSGRoute.PTExt.IsInertiaAt q σ) {ξ : K} (hξ : ξ ^ p = 1) :
    σ ξ = ξ := by
  have hξint : IsIntegral ℤ ξ :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hp0) (by rw [hξ]; exact isIntegral_one)
  have hσξ : (σ ξ) ^ p = 1 := by rw [← map_pow, hξ, map_one]
  have hσξint : IsIntegral ℤ (σ ξ) :=
    IsIntegral.of_pow (Nat.pos_of_ne_zero hp0) (by rw [hσξ]; exact isIntegral_one)
  -- `σ ξ ≡ ξ (mod q)`, from the inertia hypothesis applied to `ξ ∈ 𝓞 K`
  have hmem : (⟨σ ξ, hσξint⟩ : NumberField.RingOfIntegers K) -
      (⟨ξ, hξint⟩ : NumberField.RingOfIntegers K) ∈ q.asIdeal := by
    refine (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := K) q _).mp ?_
    have hcalc : (IsDedekindDomain.HeightOneSpectrum.valuation K q) (σ ξ - ξ) < 1 := by
      simpa using hσ (⟨ξ, hξint⟩ : NumberField.RingOfIntegers K)
    exact hcalc
  have hηRp : (⟨σ ξ, hσξint⟩ : NumberField.RingOfIntegers K) ^ p = 1 := by
    apply Subtype.ext
    simpa using hσξ
  have hξRp : (⟨ξ, hξint⟩ : NumberField.RingOfIntegers K) ^ p = 1 := by
    apply Subtype.ext
    simpa using hξ
  exact Subtype.ext_iff.mp (aux_eq_of_pow_eq_one_of_sub_mem hp0 q.asIdeal hpq hηRp hξRp hmem)

set_option backward.isDefEq.respectTransparency false in
/-- **The normal closure of the inertia at `q` fixes a primitive `p`-th root of unity `ζ ∈ K`.**

The set `H = {σ | ∀ ξ, ξ ^ p = 1 → σ ξ = ξ}` of automorphisms acting trivially on all `p`-th roots
of unity is a *normal* subgroup of `Gal(K/k)` (it is closed under conjugation because
`(τ σ τ⁻¹) ξ = τ (σ (τ⁻¹ ξ))` and `τ⁻¹ ξ` is again a `p`-th root of unity), and it contains every
inertia element at `q` by `aux_isInertiaAt_apply_pow_eq_one`. Hence the normal closure of the
inertia set is contained in `H`, which is the claim for `ζ` (`ζ ^ p = 1`). -/
private lemma aux_normalClosure_inertia_fixes_zeta (p : ℕ) [Fact p.Prime] {k K : Type}
    [Field k] [Field K] [NumberField K] [Algebra k K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (ζ : K) (hζ : IsPrimitiveRoot ζ p) :
    ∀ σ ∈ Subgroup.normalClosure {σ : K ≃ₐ[k] K | SSGRoute.PTExt.IsInertiaAt q σ}, σ ζ = ζ := by
  have hp0 : p ≠ 0 := (Fact.out (p := p.Prime)).ne_zero
  let H : Subgroup (K ≃ₐ[k] K) :=
    { carrier := {σ | ∀ ξ : K, ξ ^ p = 1 → σ ξ = ξ}
      mul_mem' := by
        intro a b ha hb ξ hξ
        have ha' : ∀ ξ : K, ξ ^ p = 1 → a ξ = ξ := ha
        have hb' : ∀ ξ : K, ξ ^ p = 1 → b ξ = ξ := hb
        rw [AlgEquiv.mul_apply, hb' ξ hξ, ha' ξ hξ]
      one_mem' := by
        intro ξ hξ
        simp
      inv_mem' := by
        intro a ha ξ hξ
        have ha' : ∀ ξ : K, ξ ^ p = 1 → a ξ = ξ := ha
        have h2 : (a.symm ξ) ^ p = 1 := by rw [← map_pow, hξ, map_one]
        have h3 : a (a.symm ξ) = a.symm ξ := ha' (a.symm ξ) h2
        rw [AlgEquiv.apply_symm_apply] at h3
        exact h3.symm }
  have hHnorm : H.Normal := by
    refine ⟨fun n hn g ξ hξ => ?_⟩
    have hn' : ∀ ξ : K, ξ ^ p = 1 → n ξ = ξ := hn
    have h2 : (g.symm ξ) ^ p = 1 := by rw [← map_pow, hξ, map_one]
    calc (g * n * g⁻¹) ξ = g (n (g⁻¹ ξ)) := by rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
      _ = g (g⁻¹ ξ) := by rw [hn' (g⁻¹ ξ) h2]
      _ = ξ := by simp
  have hSH : {σ : K ≃ₐ[k] K | SSGRoute.PTExt.IsInertiaAt q σ} ⊆ H :=
    fun σ hσ ξ hξ => aux_isInertiaAt_apply_pow_eq_one hp0 q hpq σ hσ hξ
  haveI := hHnorm
  have hle := Subgroup.normalClosure_le_normal hSH
  intro σ hσ
  exact hle hσ ζ hζ.pow_eq_one

/-- **The leaf `C6` from the induced-normal node, in the `μ_p ⊆ K` case** (step 4 of
`_lead_design/ssg_pt_design_1002/DESIGN.md` §2 A1).

`ζ ∈ K` is a primitive `p`-th root of unity — the hypothesis this route needs (see
`PING_indNormal_needs_mu_p_in_K.md`); every consumer of the E9 input carries it as
`E9Input_of_core.lean`'s `hroot : ∃ ζ' : K, IsPrimitiveRoot ζ' p`.  So the statement below gives the
leaf `Work.Sha2Lib.unramifiedDetector` at `M` in the `μ_p ⊆ K` case (the ζ-free case needs the leaf
and its ζ-free consumers restated).

`hind` is node `unramifiedDetector_indNormal`: the detector for `Ind_N^Γ W`, for every normal
`N ⊴ Gal(K/k)` containing the inertia at `q`, fixing `ζ`, and every finite trivial `p`-torsion
`N`-module `W`.  Conclusion: the detector for an arbitrary finite `p`-torsion `M` on which the
inertia at `q` acts trivially.

Route (all pieces are already proved, on disk): take `N` = the normal closure of
`{σ | IsInertiaAt q σ}` (`normalClosure_inertia_acts_trivially` gives that it acts trivially on `M`
from `hI`; `PT.inertia_fixes_zeta` plus `(τστ⁻¹)ζ = τ(σ(τ⁻¹ζ)) = τ(τ⁻¹ζ) = ζ` gives `hNζ`); put
`W := Rep.res N.subtype M`; `hind` gives the detector for `Ind_N^Γ W`, whose counit to `M` is
surjective (`indRes_counit_surjective`), and a nonzero `φ` stays nonzero after pullback along it
(`ext_comp_mk0_ne_zero_of_surjective`), so `Sha2Lib.detectsAt_of_coeff_surjection` transports
detection to `M`. -/
theorem unramifiedDetector_of_indNormal (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (hpq : ((p : NumberField.RingOfIntegers K) ∉ q.asIdeal))
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (hI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (hind : ∀ (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
      (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
      (hNζ : ∀ σ ∈ N, σ ζ = ζ)
      (W : Rep.{0} SSGRoute.PTExt.Coeff N) [Finite W] (hWp : ∀ x : W, p • x = 0)
      (hWtriv : ∀ (n : N) (x : W), W.ρ n x = x),
      Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq (Rep.ind N.subtype W)) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq M := by
  classical
  -- `N` = the normal closure of the inertia at `q`, and `W = res_N M`
  let N : Subgroup (K ≃ₐ[k] K) :=
    Subgroup.normalClosure {σ : K ≃ₐ[k] K | SSGRoute.PTExt.IsInertiaAt q σ}
  haveI hNnormal : N.Normal := Subgroup.normalClosure_normal
  have hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N :=
    fun σ hσ => Subgroup.subset_normalClosure hσ
  have hNζ : ∀ σ ∈ N, σ ζ = ζ := aux_normalClosure_inertia_fixes_zeta p q hpq ζ hζ
  -- the dispatched node, applied to `N` and to the trivial `p`-torsion `N`-module `res_N M`
  have hindet : Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq
      (Rep.ind N.subtype (Rep.res N.subtype M)) :=
    hind N hNI hNζ (Rep.res N.subtype M) (fun x => hM x)
      (fun n x => Work.Sha2Lib.normalClosure_inertia_acts_trivially p k K M q hI
        (n : K ≃ₐ[k] K) n.2 x)
  haveI : N.FiniteIndex := inferInstance
  -- detection transfers from `Ind_N^Γ (res_N M)` to `M` along the (surjective) counit
  exact Work.Sha2Lib.isUnramifiedDetector_of_ind p k K Ω w q hwq N M hM hindet

end Work.SSGRoute.Sha2Lib
