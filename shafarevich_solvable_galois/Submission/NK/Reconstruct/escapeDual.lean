import Mathlib
import Submission.NK.Reconstruct.gammaHaus
import Submission.NK.Reconstruct.frobElementAt
import Submission.NK.Reconstruct.prop4f3_measureStep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The escape lemma of Proposition 4f.3

Shimizu's Proposition 4f.3 (arXiv:2009.10431, §4) needs the following avoidance statement:

*if `ψ_i : Γ_L → ℤ_ℓ` (`i = 1, …, k`) are non-zero continuous homomorphisms, then there is a prime
`𝔭` of `L` whose Frobenius element `γ = galToGamma σ` at `𝔭` satisfies `ψ_i(γ) ≠ 1` for all `i`.*

The proof is the Baire-category argument: `ker ψ_i` is a closed subgroup of the compact Hausdorff
group `Γ_L`; it is **not** open, because an open kernel would make the range finite, and a finite
subgroup of the torsion-free group `ℤ_ℓ` is trivial.  A finite union of closed non-open subgroups
cannot exhaust `Γ_L` (`NK.Reconstruct.exists_notMem_iUnion_closedSubgroup`), and the Frobenius
elements are dense in `Γ_L` (`NK.Reconstruct.dense_image_galToGamma_isFrobElementAt`, i.e.
Čebotarev, hypothesis (c) of the reconstruction) — so one of them lies outside the union.

The same statement with the target `Γ_L^{tf}` (rather than `ℤ_ℓ`) follows, since `Γ_L^{tf}` embeds
in a product of copies of `ℤ_ℓ`: a non-zero homomorphism into it is detected by a continuous linear
functional.

## References

S. Shimizu, *On the Neukirch–Uchida theorem for small sets of primes*, arXiv:2009.10431, §4;
J.-P. Serre, *Abelian ℓ-adic Representations and Elliptic Curves*, Ch. I §2.2.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace NK.Reconstruct

variable {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K'] [Algebra K K']
  [IsSepClosure K K']

/-- **A finite subgroup of a torsion-free group is trivial.** -/
theorem finite_range_eq_bot_of_torsionFree {G N : Type*} [Group G] [Group N] (ψ : G →* N)
    (htf : ∀ (y : N) (n : ℕ), n ≠ 0 → y ^ n = 1 → y = 1) (hfin : Finite ψ.range) :
    ψ.range = ⊥ := by
  haveI := hfin
  rw [Subgroup.eq_bot_iff_forall]
  intro y hy
  have hcard : Nat.card (ψ.range) ≠ 0 :=
    Nat.card_ne_zero.mpr ⟨⟨⟨y, hy⟩⟩, inferInstance⟩
  exact htf y (Nat.card ψ.range) hcard
    (orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard ψ.range hy))

/-- **A non-zero homomorphism into a torsion-free group has infinite range.** -/
theorem not_finite_range_of_ne_one {G N : Type*} [Group G] [Group N] (ψ : G →* N)
    (htf : ∀ (y : N) (n : ℕ), n ≠ 0 → y ^ n = 1 → y = 1) (hne : ψ ≠ 1) :
    ¬ Finite ψ.range := by
  intro hfin
  apply hne
  refine MonoidHom.ext fun x => ?_
  have hx : ψ x ∈ ψ.range := Set.mem_range_self x
  rw [finite_range_eq_bot_of_torsionFree ψ htf hfin] at hx
  simpa using hx

/-- The torsion-freeness of `Multiplicative ℤ_ℓ`, in the form needed below. -/
theorem torsionFree_multiplicative_padicInt (ℓ : ℕ) [Fact ℓ.Prime]
    (y : Multiplicative (PadicInt ℓ)) (n : ℕ) (hn : n ≠ 0) (h : y ^ n = 1) : y = 1 :=
  multiplicative_padicInt_pow_eq_one hn h

/-- **The escape lemma of Proposition 4f.3.**  For finitely many non-zero continuous homomorphisms
`ψ_i : Γ_K → ℤ_ℓ` there is a prime `p` of `K` and a Frobenius element `σ` at `p` such that
`ψ_i (galToGamma σ) ≠ 1` for all `i`.

The only arithmetic input is Čebotarev, in the form of hypothesis (c) of the reconstruction
(`NK.Reconstruct.ChebotarevInput`), through the density of the Frobenius elements in `Γ_K`. -/
theorem exists_isFrobElementAt_notMem_iUnion_ker_padicInt (hc : ChebotarevInput K K') (ℓ : ℕ)
    [Fact ℓ.Prime] {ι : Type*} [Finite ι]
    (ψ : ι → Gamma K K' ℓ →* Multiplicative (PadicInt ℓ))
    (hcont : ∀ i, Continuous (ψ i)) (hne : ∀ i, ψ i ≠ 1) :
    ∃ (p : NK.Chebotarev.PrimeIdeal K) (σ : Gal(K'/K)),
      IsFrobElementAt p σ ∧ ∀ i, ψ i (galToGamma (K := K) (K' := K') ℓ σ) ≠ 1 :=
  exists_isFrobElementAt_notMem_iUnion_ker_of_infinite_range (K := K) (K' := K') hc ℓ ψ hcont
    (fun i => not_finite_range_of_ne_one (ψ i) (torsionFree_multiplicative_padicInt ℓ) (hne i))

/-- **The escape lemma with target `Γ_M^{tf}`.**  If the homomorphisms `φ_i : Γ_K → Γ_M^{tf}` are
non-zero and continuous, then some Frobenius element escapes all their kernels: `Γ_M^{tf}` is a
subgroup of a product of copies of `ℤ_ℓ`, so that for each `i` there is a continuous functional
`g_i` with `g_i ∘ φ_i ≠ 1`, and the previous lemma applied to the `g_i ∘ φ_i` gives the result.

This is the form in which Proposition 4f.3 consumes the measure step. -/
theorem exists_isFrobElementAt_notMem_ker_gammaHaus' {M : Type*} [Field M] [NumberField M]
    {M' : Type*} [Field M'] [Algebra M M'] [IsSepClosure M M'] (hc : ChebotarevInput K K')
    (ℓ : ℕ) [Fact ℓ.Prime] {ι : Type*} [Finite ι]
    (φ : ι → Gamma K K' ℓ →* GammaHaus M M' ℓ)
    (hcont : ∀ i, Continuous (φ i)) (hne : ∀ i, φ i ≠ 1) :
    ∃ (p : NK.Chebotarev.PrimeIdeal K) (σ : Gal(K'/K)),
      IsFrobElementAt p σ ∧ ∀ i, φ i (galToGamma (K := K) (K' := K') ℓ σ) ≠ 1 := by
  classical
  -- `Γ_M^{tf}` is a subgroup of a product of copies of `ℤ_ℓ`: a non-zero element of it has a
  -- non-zero component, so each `φ i` is detected by some continuous functional
  have hchoice : ∀ i, ∃ (g : Dual (Gamma M M' ℓ) ℓ) (x : Gamma K K' ℓ), (φ i x).1 g ≠ 1 := by
    intro i
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp (hne i)
    by_contra hcon
    apply hx
    refine Subtype.ext (funext fun g => ?_)
    have hg1 : (φ i x).1 g = 1 := by
      by_contra hgt
      exact hcon ⟨g, x, hgt⟩
    simpa using hg1
  choose g x0 hg using hchoice
  let ψ : ι → Gamma K K' ℓ →* Multiplicative (PadicInt ℓ) := fun i =>
    { toFun := fun x => (φ i x).1 (g i)
      map_one' := by
        show (φ i 1).1 (g i) = 1
        rw [map_one]
        rfl
      map_mul' := by
        intro x y
        show (φ i (x * y)).1 (g i) = (φ i x).1 (g i) * (φ i y).1 (g i)
        rw [map_mul]
        rfl }
  have hψne : ∀ i, ψ i ≠ 1 := by
    intro i h
    exact hg i (by
      have h1 : ψ i (x0 i) = 1 := by rw [h]; rfl
      simpa [ψ] using h1)
  have hψcont : ∀ i, Continuous (ψ i) := by
    intro i
    exact ((continuous_apply (g i)).comp continuous_subtype_val).comp (hcont i)
  obtain ⟨p, σ, hp, hσ⟩ :=
    exists_isFrobElementAt_notMem_iUnion_ker_padicInt (K := K) (K' := K') hc ℓ ψ hψcont hψne
  refine ⟨p, σ, hp, fun i => ?_⟩
  intro h0
  have h1 : ψ i (galToGamma (K := K) (K' := K') ℓ σ) = 1 := by
    show (φ i (galToGamma (K := K) (K' := K') ℓ σ)).1 (g i) = 1
    rw [h0]
    rfl
  exact hσ i h1

end NK.Reconstruct
