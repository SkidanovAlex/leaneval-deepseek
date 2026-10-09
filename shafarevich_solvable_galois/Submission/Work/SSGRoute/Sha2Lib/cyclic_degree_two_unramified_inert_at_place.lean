import Mathlib
import Submission.Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum
import Submission.Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.exists_unramified_extension_of_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_le_finrank
import Submission.Commons.FieldTheory.Polynomial.exists_monic_irreducible_of_natDegree
import Submission.Commons.RingTheory.Polynomial.exists_monic_lift_of_surjective
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.NK.NUV2.LC.adjoinSq_normal_finrank_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField IntermediateField
open Polynomial
open IsDedekindDomain.HeightOneSpectrum

namespace Work.SSGRoute.Sha2Lib

/-- A finite-dimensional extension of a field of characteristic zero of dimension at most two is
Galois: it is separable (characteristic zero) and normal because every minimal polynomial has
degree at most two and a polynomial of degree at most two with a root splits. -/
theorem isGalois_of_finrank_le_two {K E : Type*} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] [CharZero K] (h : Module.finrank K E ≤ 2) : IsGalois K E :=
  isGalois_iff.mpr ⟨Algebra.IsSeparable.of_integral K E, NK.NUV2.LC.normal_of_finrank_le_two h⟩

/-- **The local computation: a degree-`2` polynomial with irreducible reduction at `Q` gives
`e(w|Q) = 1`, `f(w|Q) = 2` for every prime `w` of `𝓞 M` above `Q`.**

Let `M ⊆ Ω` be a finite extension of the number field `k` with `[M : k] ≤ 2` (`hfr`), let
`f ∈ (𝓞 k)[X]` be monic of degree `2` whose reduction `g` modulo `Q` is irreducible, and let
`θ ∈ 𝓞 M` be a root of `f`.  Then for every prime `w` of `𝓞 M` lying over `Q`,

* `f(w|Q) ≥ deg g = 2`, because the reduction of `θ` modulo `w` is a root of the irreducible `g`,
  so that `deg g ≤ f(w|Q)` (`natDegree_le_inertiaDeg_of_aeval_eq_zero`);
* `e(w|Q) · f(w|Q) = [M_w : k_Q] ≤ [M : k] ≤ 2` (`finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg`
  and `finrank_adicCompletion_le_finrank`).

Hence `f(w|Q) = 2` and `e(w|Q) = 1`. -/
theorem ramificationIdx_eq_one_inertiaDeg_eq_two_of_quadratic_reduction (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (M : IntermediateField k Ω) [NumberField ↥M] [FiniteDimensional k ↥M]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (f : Polynomial (NumberField.RingOfIntegers k)) (hfmonic : f.Monic) (hfdeg : f.natDegree = 2)
    (g : Polynomial (NumberField.RingOfIntegers k ⧸ Q.asIdeal))
    (hgirr : Irreducible g) (hmap : Polynomial.map (Ideal.Quotient.mk Q.asIdeal) f = g)
    (θ : NumberField.RingOfIntegers ↥M) (hθ : Polynomial.aeval θ f = 0)
    (hfr : Module.finrank k ↥M ≤ 2) :
    ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M),
      w.asIdeal.LiesOver Q.asIdeal →
        w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 ∧
        w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = 2 := by
  intro w hw
  classical
  haveI : w.asIdeal.LiesOver Q.asIdeal := hw
  haveI hmaxQ : Q.asIdeal.IsMaximal := Q.isMaximal
  haveI hmaxw : w.asIdeal.IsMaximal := w.isMaximal
  haveI hfinS : Finite (NumberField.RingOfIntegers ↥M ⧸ w.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum w
  -- `g` is monic of degree two
  have hgmonic : g.Monic := by rw [← hmap]; exact hfmonic.map _
  have hgcd : (Ideal.Quotient.mk Q.asIdeal) f.leadingCoeff ≠ 0 := by
    rw [hfmonic.leadingCoeff, map_one]; exact one_ne_zero
  have hgdeg : g.natDegree = 2 := by
    rw [← hmap, Polynomial.natDegree_map_of_leadingCoeff_ne_zero (Ideal.Quotient.mk Q.asIdeal) hgcd]
    exact hfdeg
  -- the inertia degree is at least the degree of `g`
  have hres : 2 ≤ w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    have h := Commons.NumberTheory.NumberField.Completion.natDegree_le_inertiaDeg_of_aeval_eq_zero
      (R := NumberField.RingOfIntegers k) (S := NumberField.RingOfIntegers ↥M)
      Q.asIdeal w.asIdeal f g hgmonic hgirr hmap θ hθ
    omega
  -- `e · f` is the local degree, which is at most `[M : k]`
  letI : Algebra (Q.adicCompletion k) (w.adicCompletion ↥M) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q w hw)
  have hmul :=
    Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := k) (L := ↥M) Q w hw
  have hle :=
    Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_le_finrank
      (K := k) (L := ↥M) Q w hw
  have hepos : 0 < w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) :=
    Ideal.ramificationIdx_pos (NumberField.RingOfIntegers k) w.asIdeal
  have h1 : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
      w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) ≤ 2 := by
    rw [hmul]; exact hle.trans hfr
  have hf2 : w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = 2 := by
    have h2 : w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) ≤
        w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
          w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) :=
      Nat.le_mul_of_pos_left _ hepos
    omega
  refine ⟨?_, hf2⟩
  have hge : 2 ≤ w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
      w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := by
    calc 2 ≤ w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) := hres
      _ ≤ w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
            w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) :=
          Nat.le_mul_of_pos_left _ hepos
  have hprod : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) *
      w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = 2 := le_antisymm h1 hge
  have h2 : w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) * 2 = 2 := by
    have hh := hprod
    rw [hf2] at hh
    exact hh
  exact Nat.mul_right_cancel (by norm_num : 0 < 2) (by rw [one_mul]; exact h2)

/-- **The integrality step.**  If `θ ∈ Ω` lies in the intermediate field `M` and is a root of a
*monic* polynomial `f ∈ (𝓞 k)[X]` (mapped into `Ω`), then `θ` is an algebraic integer of `M`: it is
the image of an element `θ'` of the ring of integers `𝓞 ↥M` which is a root of `f` over `𝓞 k`.

Indeed `θ` is integral over `𝓞 k` (root of the monic `f`), hence over `ℤ` (`ℤ ⊆ 𝓞 k ⊆ k` is a tower
of finite extensions), hence lies in `𝓞 ↥M = IsIntegralClosure ℤ ↥M`; the evaluation is compatible
with the algebra maps `𝓞 k → 𝓞 ↥M → ↥M`. -/
theorem exists_ringOfIntegers_aeval_eq_zero_root (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] (M : IntermediateField k Ω) [FiniteDimensional k ↥M]
    (f : Polynomial (NumberField.RingOfIntegers k)) (hfmonic : f.Monic)
    (θ : Ω) (hmem : θ ∈ M)
    (hθ : (Polynomial.map (algebraMap (NumberField.RingOfIntegers k) Ω) f).IsRoot θ) :
    ∃ θ' : NumberField.RingOfIntegers ↥M,
      (θ' : ↥M) = ⟨θ, hmem⟩ ∧ Polynomial.aeval θ' f = 0 := by
  classical
  let R := NumberField.RingOfIntegers k
  -- ## `θ` is a root of `f` over `R`, hence integral over `R`
  have hθR : Polynomial.aeval θ f = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
    exact hθ
  have hintR : IsIntegral R θ := ⟨f, hfmonic, hθR⟩
  -- ## `θ` is integral over `ℤ`
  haveI hIR : Algebra.IsIntegral ℤ R := inferInstance
  have hintZ : IsIntegral ℤ θ := isIntegral_trans (R := ℤ) (A := R) θ hintR
  -- ## `θ`, viewed in `M`, is integral over `ℤ`
  have hintM : IsIntegral ℤ (⟨θ, hmem⟩ : ↥M) :=
    IsIntegral.tower_bot (R := ℤ) (A := ↥M) (B := Ω) (algebraMap ↥M Ω).injective (by
      rw [show (algebraMap ↥M Ω) ⟨θ, hmem⟩ = θ from rfl]
      exact hintZ)
  -- ## hence `θ` is an element of `𝓞 ↥M`
  obtain ⟨θ', hθ'map⟩ :=
    (IsIntegralClosure.isIntegral_iff (A := NumberField.RingOfIntegers ↥M)
      (R := ℤ) (B := ↥M)).mp hintM
  refine ⟨θ', hθ'map, ?_⟩
  -- ## `f` vanishes at `θ'`
  have hA : Polynomial.aeval (⟨θ, hmem⟩ : ↥M) (f.map (algebraMap R k)) = 0 := by
    have h1 := Polynomial.map_aeval_eq_aeval_map (R := k) (S := ↥M) (T := Ω) (U := Ω)
      (φ := algebraMap k Ω) (ψ := algebraMap ↥M Ω) (by ext x; rfl)
      (f.map (algebraMap R k)) ⟨θ, hmem⟩
    have h2 : (algebraMap ↥M Ω)
        (Polynomial.aeval (⟨θ, hmem⟩ : ↥M) (f.map (algebraMap R k))) = 0 := by
      rw [h1]
      have h3 : (f.map (algebraMap R k)).map (algebraMap k Ω) =
          f.map (algebraMap R Ω) := by
        rw [Polynomial.map_map]; congr 1
      rw [h3]
      exact hθ
    exact (algebraMap ↥M Ω).injective (by rw [h2, map_zero])
  apply NumberField.RingOfIntegers.coe_injective (K := ↥M)
  rw [map_zero]
  have h5 := Polynomial.map_aeval_eq_aeval_map
    (R := R) (S := NumberField.RingOfIntegers ↥M) (T := ↥M) (U := ↥M)
    (φ := algebraMap R ↥M)
    (ψ := algebraMap (NumberField.RingOfIntegers ↥M) ↥M) (by ext x; rfl) f θ'
  rw [h5, hθ'map]
  have h6 : f.map (algebraMap R ↥M) =
      (f.map (algebraMap R k)).map (algebraMap k ↥M) := by
    rw [Polynomial.map_map]; congr 1
  rw [h6, ← Polynomial.aeval_eq_aeval_map (R := k) (S := ↥M) (T := ↥M)
    (φ := algebraMap k ↥M) (by ext x; rfl) (f.map (algebraMap R k)) ⟨θ, hmem⟩]
  exact hA

/-- **A quadratic level over `k` which is unramified at a prescribed finite place and in which that place is inert.**

`Q` is a finite place of the number field `k`, `Ω` is algebraically closed with `k → Ω`.  We produce a
level `M : IntermediateField k Ω` which is a number field, Galois and cyclic over `k` of degree `2`,
such that *every* prime `w` of `𝓞 M` above `Q` satisfies `e(w|Q) = 1` (unramified) and `f(w|Q) = 2`
(inert; equivalently the decomposition group of `w` in `Gal(M/k) ≅ ℤ/2` is everything).

Route (the naive "non-square residue class" does NOT work when the residue characteristic is `2`,
e.g. `k = ℚ`, `Q = (2)`, where `κ(Q) = 𝔽₂` has no non-square unit, yet `M = ℚ(√5)` is the desired
answer).  Instead we use the *unramified* extension of the local field `k_Q` directly, in the global
form given by `Commons.NumberTheory.NumberField.Completion.exists_unramified_extension_of_inertiaDeg`:
there is a monic `f ∈ (𝓞 k)[X]` of degree `2` whose reduction modulo `Q` is irreducible (a lift of an
irreducible quadratic over the finite field `κ(Q)`); a root `θ` of `f` in `Ω` then generates a
level `M = k⟮θ⟯` with `[M : k] ≤ 2`, and the reduction of `θ` modulo any prime above `Q` is a root
of the irreducible `g`, forcing `f(w|Q) ≥ 2` while `e(w|Q)·f(w|Q) = [M_w : k_Q] ≤ [M : k] ≤ 2`.
Hence `e(w|Q) = 1` and `f(w|Q) = 2` for *every* `w | Q`, and in particular `[M : k] = 2`, so that
`M/k` is Galois with cyclic Galois group of order `2`. -/
theorem cyclic_degree_two_unramified_inert_at_place (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [IsAlgClosed Ω] [Algebra k Ω]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)) :
    ∃ (M : IntermediateField k Ω) (_ : NumberField ↥M) (_ : FiniteDimensional k ↥M)
      (_ : IsGalois k ↥M),
      IsCyclic (↥M ≃ₐ[k] ↥M) ∧ Nat.card (↥M ≃ₐ[k] ↥M) = 2 ∧
      ∀ w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥M),
        w.asIdeal.LiesOver Q.asIdeal →
          w.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 ∧
          w.asIdeal.inertiaDeg (NumberField.RingOfIntegers k) = 2 := by
  classical
  let R := NumberField.RingOfIntegers k
  haveI hfinQ : Finite (R ⧸ Q.asIdeal) :=
    Commons.NumberTheory.NumberField.finite_quotient_heightOneSpectrum Q
  letI : Field (R ⧸ Q.asIdeal) := Ideal.Quotient.field Q.asIdeal
  haveI : Fintype (R ⧸ Q.asIdeal) := Fintype.ofFinite _
  -- ## an irreducible quadratic `g` over the residue field, and a monic lift `f` to `𝓞 k`
  obtain ⟨g, hgmonic, hgirr, hgdeg⟩ :=
    Commons.FieldTheory.Polynomial.exists_monic_irreducible_of_natDegree
      (F := R ⧸ Q.asIdeal) 2 (by norm_num)
  obtain ⟨f, hfmonic, hfdeg, hfmap⟩ :=
    Commons.RingTheory.Polynomial.exists_monic_lift_of_surjective
      (Ideal.Quotient.mk Q.asIdeal) Ideal.Quotient.mk_surjective g hgmonic
  have hfndeg : f.natDegree = 2 := hfdeg.trans hgdeg
  let p : Polynomial k := f.map (algebraMap R k)
  have hpmonic : p.Monic := hfmonic.map _
  have hpdeg : p.natDegree = 2 := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero (algebraMap R k) (by
      rw [hfmonic.leadingCoeff, map_one]; exact one_ne_zero)]
    exact hfndeg
  let F : Polynomial Ω := f.map (algebraMap R Ω)
  have hFmonic : F.Monic := hfmonic.map _
  have hFdeg : F.natDegree = 2 := by
    rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero (algebraMap R Ω) (by
      rw [hfmonic.leadingCoeff, map_one]; exact one_ne_zero)]
    exact hfndeg
  have hFdegnz : F.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hFmonic.ne_zero, hFdeg]; norm_num
  -- ## a root `θ` of `f` in `Ω`, and the level `M = k⟮θ⟯`
  obtain ⟨θ, hθ⟩ := IsAlgClosed.exists_root F hFdegnz
  let M : IntermediateField k Ω := k⟮θ⟯
  have hmem : θ ∈ M := IntermediateField.mem_adjoin_simple_self k θ
  have key : Polynomial.map (algebraMap k Ω) p = F := by
    show Polynomial.map (algebraMap k Ω) (Polynomial.map (algebraMap R k) f)
      = Polynomial.map (algebraMap R Ω) f
    rw [Polynomial.map_map]; congr 1
  have hroot : Polynomial.aeval θ p = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, key]
    exact hθ
  have hint : IsIntegral k θ := ⟨p, hpmonic, hroot⟩
  haveI hfd : FiniteDimensional k ↥M := IntermediateField.adjoin.finiteDimensional hint
  haveI hnf : NumberField ↥M := NumberField.of_module_finite k ↥M
  have hfinrank_le : Module.finrank k ↥M ≤ 2 := by
    rw [IntermediateField.adjoin.finrank hint]
    calc (minpoly k θ).natDegree ≤ p.natDegree :=
          Polynomial.natDegree_le_of_dvd (minpoly.dvd k θ hroot) hpmonic.ne_zero
      _ = 2 := hpdeg
  haveI hgal : IsGalois k ↥M := isGalois_of_finrank_le_two hfinrank_le
  -- ## the local computation
  obtain ⟨θ', -, hθ'⟩ := exists_ringOfIntegers_aeval_eq_zero_root k Ω M f hfmonic θ hmem hθ
  have hchain := ramificationIdx_eq_one_inertiaDeg_eq_two_of_quadratic_reduction k Ω M Q f
    hfmonic hfndeg g hgirr hfmap θ' hθ' hfinrank_le
  -- ## `[M : k] = 2`
  obtain ⟨w₀, hw₀⟩ :=
    Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver (K := k) (L := ↥M) Q
  have hA := hchain w₀ hw₀
  have hfinrank : Module.finrank k ↥M = 2 := by
    have hle := Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_le_finrank
      (K := k) (L := ↥M) Q w₀ hw₀
    letI : Algebra (Q.adicCompletion k) (w₀.adicCompletion ↥M) :=
      RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q w₀ hw₀)
    rw [← Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      (K := k) (L := ↥M) Q w₀ hw₀, hA.1, one_mul, hA.2] at hle
    omega
  refine ⟨M, inferInstance, inferInstance, inferInstance, ?_, ?_, hchain⟩
  · refine isCyclic_of_prime_card (p := 2) ?_
    rw [IsGalois.card_aut_eq_finrank, hfinrank]
  · rw [IsGalois.card_aut_eq_finrank, hfinrank]

end Work.SSGRoute.Sha2Lib
