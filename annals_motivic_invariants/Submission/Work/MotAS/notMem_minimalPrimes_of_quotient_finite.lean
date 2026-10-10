import Mathlib
import Submission.Work.CKLink6.exists_maximalIdeal_height_eq_of_ne_zero

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotAS

/-- Over a field `𝕜`, every maximal ideal of `𝕜[X₁,…,Xₙ]` has height `n`.

This is the universe-polymorphic form of `Work.CKLink6.height_eq_of_isMaximal` (whose field
argument lives in `Type`); the target statement of this file is universe-polymorphic in `K`, so
the helper has to be re-proved here.  The proof is the one of the `CKLink6` original: induction on
`n`, using `Polynomial.height_eq_height_add_one` (additivity of height in a polynomial extension)
together with the fact that `𝕜[X₁,…,Xₙ]` is Jacobson, so that the contraction of a maximal ideal
of `𝕜[X₁,…,Xₙ₊₁]` to `𝕜[X₁,…,Xₙ]` is again maximal
(`Polynomial.isMaximal_comap_C_of_isJacobsonRing`). -/
theorem height_eq_of_isMaximal_univ (𝕜 : Type*) [Field 𝕜] :
    ∀ (n : ℕ) (𝔪 : Ideal (MvPolynomial (Fin n) 𝕜)), 𝔪.IsMaximal → 𝔪.height = (n : ℕ∞) := by
  intro n
  induction n with
  | zero =>
    intro 𝔪 h𝔪
    have hdim : ringKrullDim (MvPolynomial (Fin 0) 𝕜) = 0 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite]
      simp
    have hle := Ideal.height_le_ringKrullDim_of_ne_top h𝔪.ne_top
    rw [hdim] at hle
    have hle' : 𝔪.height ≤ (0 : ℕ∞) := by simpa using hle
    exact le_antisymm hle' (by simp)
  | succ n ih =>
    intro 𝔪 h𝔪
    let e := MvPolynomial.finSuccEquiv 𝕜 n
    set M : Ideal (Polynomial (MvPolynomial (Fin n) 𝕜)) := Ideal.map e.toRingEquiv 𝔪 with hMdef
    have hM : M.IsMaximal := Ideal.map_isMaximal_of_equiv e.toRingEquiv
    have hLO : M.LiesOver (M.comap Polynomial.C) :=
      ⟨by rw [Ideal.under, Polynomial.algebraMap_eq]⟩
    have hp : (M.comap Polynomial.C).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing M
    have hp' : (M.comap Polynomial.C).height = (n : ℕ∞) := ih _ hp
    have hPM : M.height = (M.comap Polynomial.C).height + 1 := by
      rw [Polynomial.height_eq_height_add_one (M.comap Polynomial.C) M]
    rw [← RingEquiv.height_map e.toRingEquiv 𝔪]
    change M.height = ((n + 1 : ℕ) : ℕ∞)
    rw [hPM, hp']
    norm_num

/-- **A curve in `K[X₀,X₁,X₂]`.**  Let `I ⊴ R = K[X₀,X₁,X₂]` be an ideal all of whose minimal
primes are curves (height `2`).  If adding a single element `x` makes `R ⧸ (I ⊔ (x))` finite
dimensional over `K` (so that `I ⊔ (x)` cuts out the empty subscheme in the `K`-finite sense),
then `x` cannot vanish on any irreducible component of `V(I)`: for a minimal prime `𝔭` of `I`
the hypothesis `x ∈ 𝔭` would make `𝔭` a minimal prime of `I ⊔ (x)` inside the zero-dimensional
ring `R ⧸ (I ⊔ (x))`, hence maximal; but a maximal ideal of `K[X₀,X₁,X₂]` has height `3`
(`Work.MotAS.height_eq_of_isMaximal_univ`), contradicting `height 𝔭 = 2`. -/
theorem notMem_minimalPrimes_of_quotient_finite {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin 3) K)) (x : MvPolynomial (Fin 3) K)
    (hfin : Module.Finite K (MvPolynomial (Fin 3) K ⧸ (I ⊔ Ideal.span {x})))
    (hht : ∀ 𝔭 ∈ I.minimalPrimes, Ideal.height 𝔭 = 2) :
    ∀ 𝔭 ∈ I.minimalPrimes, x ∉ 𝔭 := by
  intro 𝔭 h𝔭 hx
  -- `𝔭` is a prime containing `I` (minimality), and `J := I ⊔ (x) ≤ 𝔭` since `x ∈ 𝔭`.
  haveI hp𝔭 : 𝔭.IsPrime := Ideal.IsMinimalPrime.isPrime h𝔭
  have hJ𝔭 : I ⊔ Ideal.span {x} ≤ 𝔭 := by
    refine sup_le (Ideal.IsMinimalPrime.le h𝔭) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hx
  haveI hfinI : Module.Finite K (MvPolynomial (Fin 3) K ⧸ (I ⊔ Ideal.span {x})) := hfin
  -- Hence `R ⧸ 𝔭` is a quotient of the `K`-finite ring `R ⧸ (I ⊔ (x))`, so it is `K`-finite.
  have hfin' : Module.Finite K (MvPolynomial (Fin 3) K ⧸ 𝔭) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ K hJ𝔭).toLinearMap (by
      intro y
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Ideal.Quotient.mk _ a, by rw [← ha]; simp⟩)
  -- A `K`-finite domain is a field, so `𝔭` is maximal.
  haveI hdom : IsDomain (MvPolynomial (Fin 3) K ⧸ 𝔭) := Ideal.Quotient.isDomain 𝔭
  haveI hfield : IsField (MvPolynomial (Fin 3) K ⧸ 𝔭) := IsField.of_isDomain_of_finite K _
  have hmax : 𝔭.IsMaximal := Ideal.Quotient.maximal_of_isField 𝔭 hfield
  -- But every maximal ideal of `K[X₀,X₁,X₂]` has height `3`, contradicting `height 𝔭 = 2`.
  have h3 : Ideal.height 𝔭 = 3 := height_eq_of_isMaximal_univ K 3 𝔭 hmax
  have h2 : Ideal.height 𝔭 = 2 := hht 𝔭 h𝔭
  rw [h2] at h3
  norm_num at h3

end Work.MotAS
