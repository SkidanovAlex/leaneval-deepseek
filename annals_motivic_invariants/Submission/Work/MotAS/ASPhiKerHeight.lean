import Mathlib
import Submission.Work.MotAS.ASZPhiDefs
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.AK
import Submission.Work.MotAS.transcendental_twistFieldAS_gen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.MotAS.ASPhiKerHeight` — the kernel of `asPhi` has height at most two

`asPhi D : K[X₀,X₁,X₂] →ₐ[K] ↥(twistFieldAS D (3 • fAS 𝕜))` (`K = RatFunc 𝕜`) is the chart of the
linear projection `F = phiAS a b` restricted to the AS-twisted Klein curve, and
`Z = ZIAS (aK D) (bK D) (fAS 𝕜)` is the residual ideal
(`Submission/Work/MotAS/ASResidual.lean`).  Node `asPhi_ker` asks for
`RingHom.ker (asPhi D) = √Z`; the *easy half* `Z ≤ ker (asPhi D)` is
`Work.MotAS.zias_le_ker_asPhi`, and the *hard half* can be replaced by a height count
(`Submission/Work/MotAS/asPhi_ker.lean`): with `√Z` prime of height two and
`(ker (asPhi D)).height ≤ 2`, the inclusion `√Z ≤ ker (asPhi D)` is an equality.

This module provides the height bound.  Its content is the observation that the *only* way
`ker φ` can have height three in the three-dimensional ring `K[X₀,X₁,X₂]` is for it to be
**maximal**; and `ker φ` cannot be maximal **as soon as the image of `φ` generates a field with a
transcendental element**.  Indeed, if `ker φ` were maximal then `K[X]/ker φ` would be a field
finitely generated as a `K`-algebra, hence *finite* over `K` by Zariski's lemma
(`finite_of_finite_type_of_isJacobsonRing`), hence algebraic over `K`; the image of `φ` consists
of algebraic elements, so the subfield `Subfield.closure (K ∪ range φ)` (which is `⊤` by
hypothesis) would be algebraic over `K`, contradicting the existence of a transcendental element
(`Work.MotAS.transcendental_twistFieldAS_gen` for `g = 3 • fAS 𝕜`).

The hypothesis "the closure of the image is `⊤`" is exactly node `asPhi_gen`
(`Submission/Work/MotAS/asPhi_gen.lean`, `Work.MotAS.asPhiGenFinal`).  Together with the height
computation of the residual (`Work.MotAS.asPhiKerResidual`: `√Z` prime with `height = 2`) this
yields `Work.MotAS.asPhi_ker` without the explicit inverse map `ρ` of the projection.

## Main results

* `not_isMaximal_ker_of_transcendental`
* `height_ker_le_two_of_transcendental`
* `height_ker_asPhi_le_two` — the `asPhi` instance, conditional on `asPhi_gen`
* `ker_asPhi_eq_radical_of_height` — the assembled kernel statement, conditional on
  `asPhi_gen`, the easy half `Z ≤ ker (asPhi D)`, and `IsPrime √Z` with `2 ≤ height √Z`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

namespace Work.MotAS

open MvPolynomial

/-! ## §1 The abstract height argument -/

/-- **The algebraic elements of a field extension form a subfield.** -/
private def algSubfield {K F : Type} [Field K] [Field F] [Algebra K F] : Subfield F where
  carrier := {x | IsAlgebraic K x}
  mul_mem' := fun ha hb => IsAlgebraic.mul ha hb
  one_mem' := isAlgebraic_one
  add_mem' := fun ha hb => IsAlgebraic.add ha hb
  zero_mem' := isAlgebraic_zero
  neg_mem' := fun ha => IsAlgebraic.neg ha
  inv_mem' := fun x hx => IsAlgebraic.inv hx

/-- **The closure of `K` together with algebraic elements is not everything**, in the presence of a
transcendental element. -/
private lemma closure_ne_top_of_algebraic {K F : Type} [Field K] [Field F] [Algebra K F]
    {S : Set F} (hS : ∀ x ∈ S, IsAlgebraic K x)
    (htr : ∃ x : F, Transcendental K x) :
    Subfield.closure (Set.range (algebraMap K F) ∪ S) ≠ ⊤ := by
  intro htop
  have hle : Subfield.closure (Set.range (algebraMap K F) ∪ S)
      ≤ algSubfield (K := K) (F := F) := by
    rw [Subfield.closure_le]
    rintro x (hx | hx)
    · obtain ⟨k, rfl⟩ := hx
      exact isAlgebraic_algebraMap k
    · exact hS x hx
  have htop' : (⊤ : Subfield F) ≤ algSubfield (K := K) (F := F) := by rw [← htop]; exact hle
  obtain ⟨x, hx⟩ := htr
  exact hx (htop' (Subfield.mem_top x))

/-- **`ker φ` is not maximal if the image of `φ` generates a field with a transcendental element.**

Zariski's lemma makes the residue field of a maximal kernel finite, hence algebraic, over `K`; the
generated subfield would then be algebraic, contradicting the transcendental element. -/
theorem not_isMaximal_ker_of_transcendental {K F : Type} [Field K] [Field F] [Algebra K F]
    (φ : MvPolynomial (Fin 3) K →ₐ[K] F)
    (hgen : Subfield.closure (Set.range (algebraMap K F) ∪ Set.range φ) = ⊤)
    (htr : ∃ x : F, Transcendental K x) :
    ¬ (RingHom.ker φ).IsMaximal := by
  intro hmax
  haveI : (RingHom.ker φ).IsMaximal := hmax
  letI : Field (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ) := Ideal.Quotient.field _
  haveI : Algebra.FiniteType K (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ) :=
    Algebra.FiniteType.quotient K (RingHom.ker φ)
  haveI : Module.Finite K (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ) :=
    finite_of_finite_type_of_isJacobsonRing K _
  haveI : Algebra.IsAlgebraic K (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ) :=
    Algebra.IsAlgebraic.of_finite K _
  refine closure_ne_top_of_algebraic (K := K) (F := F) (S := Set.range φ) ?_ htr hgen
  rintro x ⟨p, rfl⟩
  have h1 : IsAlgebraic K (Ideal.kerLiftAlg φ (Ideal.Quotient.mk (RingHom.ker φ) p)) :=
    IsAlgebraic.algHom (Ideal.kerLiftAlg φ) (Algebra.IsAlgebraic.isAlgebraic _)
  rwa [Ideal.kerLiftAlg_mk] at h1

/-- In `ℕ∞ = WithTop ℕ` the interval `(2, 3]` is the single point `3`. -/
private lemma le_two_of_le_three_of_ne {a : ℕ∞} (h1 : a ≤ 3) (h2 : a ≠ 3) : a ≤ 2 := by
  match a with
  | ⊤ => exact absurd h1 (not_le.mpr (WithTop.coe_lt_top 3))
  | (n : ℕ) =>
      have h1' : n ≤ 3 := by exact_mod_cast h1
      have h2' : n ≠ 3 := by rintro rfl; exact h2 (by norm_num)
      have : n ≤ 2 := by omega
      exact_mod_cast this

/-- **The height bound.**  If `φ : K[X₀,X₁,X₂] → F` has image generating a field with a
transcendental element, then `(ker φ).height ≤ 2` — the kernel is not a maximal ideal of the
three-dimensional ring `K[X₀,X₁,X₂]`. -/
theorem height_ker_le_two_of_transcendental {K F : Type} [Field K] [Field F] [Algebra K F]
    (φ : MvPolynomial (Fin 3) K →ₐ[K] F)
    (hgen : Subfield.closure (Set.range (algebraMap K F) ∪ Set.range φ) = ⊤)
    (htr : ∃ x : F, Transcendental K x) :
    (RingHom.ker φ).height ≤ 2 := by
  have hnotmax := not_isMaximal_ker_of_transcendental φ hgen htr
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hdim : ringKrullDim (MvPolynomial (Fin 3) K) = (3 : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field K,
      zero_add]
    norm_num
  have hle3 : (RingHom.ker φ).height ≤ (3 : ℕ∞) := by
    have h := Ideal.height_le_ringKrullDim_of_isPrime (I := RingHom.ker φ)
    rw [hdim] at h
    exact WithBot.coe_le_coe.mp h
  refine le_two_of_le_three_of_ne hle3 ?_
  -- the height is not three: a height-three prime of `K[X₀,X₁,X₂]` is maximal
  intro h3
  by_cases hT : RingHom.ker φ = ⊤
  · -- the zero map: the image is algebraic, contradicting the transcendental element
    refine closure_ne_top_of_algebraic (K := K) (F := F) (S := Set.range φ) ?_ htr hgen
    rintro x ⟨p, rfl⟩
    have hp : φ p = 0 := RingHom.mem_ker.mp (by rw [hT]; exact Submodule.mem_top)
    rw [hp]
    exact isAlgebraic_zero
  · obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (RingHom.ker φ) hT
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact hnotmax (heq ▸ hm)
    · have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [h3] at h1
      haveI : m.IsPrime := hm.isPrime
      have h2 : m.height ≤ (3 : ℕ∞) := by
        have h := Ideal.height_le_ringKrullDim_of_isPrime (I := m)
        rw [hdim] at h
        exact WithBot.coe_le_coe.mp h
      exact absurd ((ENat.add_one_le_iff (ne_of_lt (WithTop.coe_lt_top 3))).mp
        (le_trans h1 h2)) (lt_irrefl (3 : ℕ∞))

/-- **The height bound from a single transcendental value of `φ`.**  If some value `φ p` is
transcendental over `K`, then `ker φ` is not maximal, hence has height at most two. -/
theorem height_ker_le_two_of_transcendental_value {K F : Type} [Field K] [Field F] [Algebra K F]
    (φ : MvPolynomial (Fin 3) K →ₐ[K] F)
    (htr : ∃ p : MvPolynomial (Fin 3) K, ¬ IsAlgebraic K (φ p)) :
    (RingHom.ker φ).height ≤ 2 := by
  have hnotmax : ¬ (RingHom.ker φ).IsMaximal := by
    intro hmax
    haveI : (RingHom.ker φ).IsMaximal := hmax
    letI : Field (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ) := Ideal.Quotient.field _
    haveI : Algebra.FiniteType K (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ) :=
      Algebra.FiniteType.quotient K (RingHom.ker φ)
    haveI : Module.Finite K (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ) :=
      finite_of_finite_type_of_isJacobsonRing K _
    haveI : Algebra.IsAlgebraic K (MvPolynomial (Fin 3) K ⧸ RingHom.ker φ) :=
      Algebra.IsAlgebraic.of_finite K _
    obtain ⟨p, hp⟩ := htr
    refine hp ?_
    have h1 : IsAlgebraic K (Ideal.kerLiftAlg φ (Ideal.Quotient.mk (RingHom.ker φ) p)) :=
      IsAlgebraic.algHom (Ideal.kerLiftAlg φ) (Algebra.IsAlgebraic.isAlgebraic _)
    rwa [Ideal.kerLiftAlg_mk] at h1
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hdim : ringKrullDim (MvPolynomial (Fin 3) K) = (3 : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field K,
      zero_add]
    norm_num
  have hle3 : (RingHom.ker φ).height ≤ (3 : ℕ∞) := by
    have h := Ideal.height_le_ringKrullDim_of_isPrime (I := RingHom.ker φ)
    rw [hdim] at h
    exact WithBot.coe_le_coe.mp h
  refine le_two_of_le_three_of_ne hle3 ?_
  intro h3
  by_cases hT : RingHom.ker φ = ⊤
  · -- the zero map: every value is zero, hence algebraic, contradicting the hypothesis
    obtain ⟨p, hp⟩ := htr
    refine hp ?_
    have hp0 : φ p = 0 := RingHom.mem_ker.mp (by rw [hT]; exact Submodule.mem_top)
    rw [hp0]
    exact isAlgebraic_zero
  · obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (RingHom.ker φ) hT
    rcases eq_or_lt_of_le hle with heq | hlt
    · exact hnotmax (heq ▸ hm)
    · have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      rw [h3] at h1
      haveI : m.IsPrime := hm.isPrime
      have h2 : m.height ≤ (3 : ℕ∞) := by
        have h := Ideal.height_le_ringKrullDim_of_isPrime (I := m)
        rw [hdim] at h
        exact WithBot.coe_le_coe.mp h
      exact absurd ((ENat.add_one_le_iff (ne_of_lt (WithTop.coe_lt_top 3))).mp
        (le_trans h1 h2)) (lt_irrefl (3 : ℕ∞))

/-! ## §2 The `asPhi` instance -/

/-- **The kernel of the chart map of the AS linear projection has height at most two**, given that
its image generates the AS twist field of class `3 • fAS 𝕜` (`Work.MotAS.asPhi_gen`). -/
theorem height_ker_asPhi_le_two (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (hgen : Subfield.closure (Set.range (algebraMap (RatFunc 𝕜)
        ↥(twistFieldAS D (3 • Work.MotV.fAS 𝕜))) ∪ Set.range (asPhi D)) = ⊤) :
    (RingHom.ker (asPhi D)).height ≤ 2 :=
  height_ker_le_two_of_transcendental (asPhi D) hgen
    (transcendental_twistFieldAS_gen 𝕜 D hD (3 • Work.MotV.fAS 𝕜))

/-- **The same height bound from a single transcendental coordinate**
(`Work.MotAS.asPhiX1_transcendental`); this route does *not* need `Work.MotAS.asPhi_gen`. -/
theorem height_ker_asPhi_le_two_of_transcendental (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (h : ¬ IsAlgebraic (RatFunc 𝕜) (asPhi D (MvPolynomial.X 1))) :
    (RingHom.ker (asPhi D)).height ≤ 2 :=
  height_ker_le_two_of_transcendental_value (asPhi D) ⟨MvPolynomial.X 1, h⟩

/-! ## §3 The assembled kernel statement -/

/-- **`ker (asPhi D) = √(ZIAS (aK D) (bK D) (fAS 𝕜))`** from a height bound on the kernel and the
primeness/height of `√ZIAS`.

The proof: `√Z ≤ ker φ` since `ker φ` is prime and contains `Z`.  `√Z` is prime of height two while
`ker φ` has height at most two; a strict inclusion of prime ideals raises the height by at least one,
so no strict inclusion is possible. -/
theorem ker_asPhi_eq_radical_of_height_le (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (hZ : ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ≤ RingHom.ker (asPhi D))
    (hprime : (Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜))).IsPrime)
    (hht : (2 : ℕ∞) ≤ (Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜))).height)
    (hker2 : (RingHom.ker (asPhi D)).height ≤ 2) :
    RingHom.ker (asPhi D) = Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜)) := by
  haveI hker : (RingHom.ker (asPhi D)).IsPrime := RingHom.ker_isPrime (asPhi D)
  have hle : Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜)) ≤ RingHom.ker (asPhi D) :=
    hker.radical_le_iff.mpr hZ
  refine le_antisymm ?_ hle
  by_contra hcon
  have hne : Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜)) ≠ RingHom.ker (asPhi D) :=
    fun h => hcon (le_of_eq h.symm)
  have hlt : Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜)) < RingHom.ker (asPhi D) :=
    lt_of_le_of_ne hle hne
  haveI : (Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜))).IsPrime := hprime
  have h2 : (Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜))).height + 1
      ≤ (RingHom.ker (asPhi D)).height :=
    Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h3 : (Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜))).height + 1 ≤ (2 : ℕ∞) :=
    le_trans h2 hker2
  have h4 : (Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜))).height < (2 : ℕ∞) :=
    (ENat.add_one_le_iff' (ne_of_lt (WithTop.coe_lt_top 2))).mp h3
  exact (not_lt.mpr hht) h4

/-- **`ker (asPhi D) = √(ZIAS (aK D) (bK D) (fAS 𝕜))`**, from

* `hZ` — the easy half `ZIAS ≤ ker (asPhi D)` (`Work.MotAS.zias_le_ker_asPhi`),
* `hgen` — node `asPhi_gen`,
* `hprime`/`hht` — `√(ZIAS)` is prime of height two (`Work.MotAS.asPhiKerResidual`). -/
theorem ker_asPhi_eq_radical_of_height (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (D : Work.MotV.KleinData 𝕜) (hD : Work.MotV5.KleinData.ASGood D)
    (hgen : Subfield.closure (Set.range (algebraMap (RatFunc 𝕜)
        ↥(twistFieldAS D (3 • Work.MotV.fAS 𝕜))) ∪ Set.range (asPhi D)) = ⊤)
    (hZ : ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜) ≤ RingHom.ker (asPhi D))
    (hprime : (Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜))).IsPrime)
    (hht : (2 : ℕ∞) ≤ (Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜))).height) :
    RingHom.ker (asPhi D) = Ideal.radical (ZIAS (aK D) (bK D) (Work.MotV.fAS 𝕜)) :=
  ker_asPhi_eq_radical_of_height_le 𝕜 D hD hZ hprime hht
    (height_ker_asPhi_le_two 𝕜 D hD hgen)

end Work.MotAS
