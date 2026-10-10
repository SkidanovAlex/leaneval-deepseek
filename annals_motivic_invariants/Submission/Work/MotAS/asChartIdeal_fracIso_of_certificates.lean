import Mathlib
import Submission.Work.MotAS.ASZTwistDefs
import Submission.Work.MotAS.ASResidual

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotAS

set_option backward.isDefEq.respectTransparency false

/-- **The certificate form of a fraction-field identification.**

Let `S` be a commutative `𝕜`-algebra, `T` a field with a `𝕜`-algebra structure, `Φ : S →ₐ[𝕜] T` a
`𝕜`-algebra map whose kernel is exactly an ideal `I ⊆ S`, and suppose that `T` is generated, as a
*field* over `𝕜`, by the image of `Φ` together with `𝕜` itself.  Then the fraction ring of the
quotient `S ⧸ I` is `𝕜`-algebra isomorphic to `T`.

Proof: `Φ` factors through an *injective* `𝕜`-algebra map `Ψ : S ⧸ I →ₐ[𝕜] T`, hence `S ⧸ I` is a
domain and the universal property of the fraction ring extends `Ψ` to `φ : FractionRing (S ⧸ I) →ₐ[𝕜] T`.
The image of `φ` is a subfield of `T` containing the image of `Ψ` (hence of `Φ`) and, since `φ` is a
`𝕜`-algebra map, the image of `𝕜`; the generation hypothesis then forces it to be all of `T`, i.e. `φ`
is surjective.  A ring map out of a field is injective, so `φ` is an isomorphism. -/
theorem fractionRing_quotient_algEquiv_of_ker {𝕜 S T : Type*} [Field 𝕜] [CommRing S] [Algebra 𝕜 S]
    [Field T] [Algebra 𝕜 T] (I : Ideal S) (Φ : S →ₐ[𝕜] T) (hker : RingHom.ker Φ = I)
    (hgen : Subfield.closure (Set.range (algebraMap 𝕜 T) ∪ Set.range Φ) = ⊤) :
    Nonempty (FractionRing (S ⧸ I) ≃ₐ[𝕜] T) := by
  have H : ∀ x ∈ I, Φ x = 0 := by
    intro x hx
    have hx' : x ∈ RingHom.ker Φ := by rw [hker]; exact hx
    simpa [RingHom.mem_ker] using hx'
  let Ψ : S ⧸ I →ₐ[𝕜] T := Ideal.Quotient.liftₐ I Φ H
  have hmk : ∀ x : S, Ψ (Ideal.Quotient.mk I x) = Φ x := by
    intro x
    dsimp only [Ψ]
    rw [Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    rfl
  have hΨinj : Function.Injective Ψ := by
    intro x y hxy
    obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hmk, hmk] at hxy
    have hmem : x' - y' ∈ I := by
      rw [← hker, RingHom.mem_ker, map_sub, hxy, sub_self]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem x' y').mpr hmem
  haveI : IsDomain (S ⧸ I) := hΨinj.isDomain Ψ
  let ψ : FractionRing (S ⧸ I) →+* T := IsFractionRing.lift hΨinj
  have hrange : Set.range Ψ = Set.range Φ := by
    ext y; constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨x', (hmk x').symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨Ideal.Quotient.mk I x, hmk x⟩
  have hle : Subfield.closure (Set.range (algebraMap 𝕜 T) ∪ Set.range Φ) ≤ ψ.fieldRange := by
    rw [Subfield.closure_le]
    rintro y (hy | hy)
    · obtain ⟨k, rfl⟩ := hy
      refine RingHom.mem_fieldRange.mpr ⟨algebraMap 𝕜 (FractionRing (S ⧸ I)) k, ?_⟩
      exact (IsFractionRing.liftAlgHom hΨinj).commutes k
    · rw [← hrange] at hy
      obtain ⟨x, rfl⟩ := hy
      refine RingHom.mem_fieldRange.mpr ⟨algebraMap (S ⧸ I) (FractionRing (S ⧸ I)) x, ?_⟩
      exact IsFractionRing.lift_algebraMap hΨinj x
  have htop : ψ.fieldRange = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact hle
  refine ⟨AlgEquiv.ofBijective (IsFractionRing.liftAlgHom hΨinj) ⟨?_, ?_⟩⟩
  · exact RingHom.injective ψ
  · intro y
    have : y ∈ ψ.fieldRange := by rw [htop]; exact Subfield.mem_top y
    exact RingHom.mem_fieldRange.mp this

theorem asChartIdeal_fracIso_of_certificates (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5]
    (a b g : RatFunc 𝕜)
    (hdom : IsDomain (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸
      Ideal.radical (Work.MotAS.ZIAS a b g)))
    (Φ : MvPolynomial (Fin 5) (RatFunc 𝕜) →ₐ[RatFunc 𝕜]
      FractionRing (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ Ideal.radical (Work.MotAS.ZIAS a b g)))
    (hker : RingHom.ker Φ = Work.MotAS.asChartIdeal a b (2 • g))
    (hgen : Subfield.closure (Set.range (algebraMap (RatFunc 𝕜)
        (FractionRing (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸ Ideal.radical (Work.MotAS.ZIAS a b g))))
        ∪ Set.range Φ) = ⊤) :
    Nonempty (FractionRing (MvPolynomial (Fin 5) (RatFunc 𝕜) ⧸
        Work.MotAS.asChartIdeal a b (2 • g)) ≃ₐ[RatFunc 𝕜]
      FractionRing (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸
        Ideal.radical (Work.MotAS.ZIAS a b g))) := by
  haveI : IsDomain (MvPolynomial (Fin 3) (RatFunc 𝕜) ⧸
      Ideal.radical (Work.MotAS.ZIAS a b g)) := hdom
  exact fractionRing_quotient_algEquiv_of_ker (Work.MotAS.asChartIdeal a b (2 • g)) Φ hker hgen

end Work.MotAS
