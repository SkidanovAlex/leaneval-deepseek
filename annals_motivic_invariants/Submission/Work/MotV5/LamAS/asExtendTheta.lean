import Mathlib
import Submission.Work.MotV5.LamAS.asPsi
import Submission.Work.MotT.extend_algEquiv_of_linearDisjoint

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.LamAS

set_option linter.unusedVariables false

open WeierstrassCurve WeierstrassCurve.Affine

/-- **Identification of a `comap` with its image.**  If `f : L →ₐ[K] L'` is injective and the
intermediate field `E ⊆ L'` is contained in the range of `f`, then `E.comap f` is canonically
`K`-isomorphic to `E`, the isomorphism being the restriction of `f`. -/
theorem comap_algEquiv_of_le_fieldRange {K L L' : Type*} [Field K] [Field L] [Field L']
    [Algebra K L] [Algebra K L']
    (f : L →ₐ[K] L') (hf : Function.Injective f) (E : IntermediateField K L')
    (hE : E ≤ f.fieldRange) :
    ∃ e : E.comap f ≃ₐ[K] E, ∀ x : E.comap f, (e x : L') = f (x : L) := by
  let φ : E.comap f →ₐ[K] E :=
    { toFun := fun x => ⟨f (x : L), x.2⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' := fun a b => Subtype.ext (map_mul f (a : L) (b : L))
      map_zero' := Subtype.ext (map_zero f)
      map_add' := fun a b => Subtype.ext (map_add f (a : L) (b : L))
      commutes' := fun k => Subtype.ext (AlgHom.commutes f k) }
  have hφ : ∀ x : E.comap f, ((φ x : E) : L') = f (x : L) := fun x => rfl
  have hinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    exact hf (congrArg (fun z : E => (z : L')) hab)
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.mp (hE y.2)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · show f x ∈ E
      rw [hx]; exact y.2
    · apply Subtype.ext
      show f x = (y : L')
      exact hx
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩, fun x => hφ x⟩

/-- An isomorphism of the two twist fields (pulled back to `M = L(E)`) extends to an `L`-algebra automorphism of `M`. -/
theorem asExtendTheta (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] (D : Work.MotV.KleinData 𝕜)
    (hD : Work.MotV5.KleinData.ASGood D) (f₁ f₂ : RatFunc 𝕜)
    (τ₁ τ₂ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D)
    (hF1 : Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS ≤
      (Work.MotV5.LamAS.asIota D f₁ f₂).fieldRange)
    (hF2 : Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS ≤
      (Work.MotV5.LamAS.asIota D f₁ f₂).fieldRange)
    (hLI1 : (Work.MotV5.LamAS.asF D f₁ f₂ f₁ τ₁ σS).LinearDisjoint
      ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂))
    (hLI2 : (Work.MotV5.LamAS.asF D f₁ f₂ f₂ τ₂ σS).LinearDisjoint
      ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂))
    (hsup1 : Work.MotV5.LamAS.asF D f₁ f₂ f₁ τ₁ σS ⊔
      Work.MotV5.LamAS.asLImageM D f₁ f₂ = ⊤)
    (hsup2 : Work.MotV5.LamAS.asF D f₁ f₂ f₂ τ₂ σS ⊔
      Work.MotV5.LamAS.asLImageM D f₁ f₂ = ⊤)
    (θ : ↥(Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS) ≃ₐ[RatFunc 𝕜]
      ↥(Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS)) :
    ∃ Θ : Work.MotV5.LamAS.asML D f₁ f₂ ≃ₐ[↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂)]
        Work.MotV5.LamAS.asML D f₁ f₂,
      ∀ (x : ↥(Work.MotV5.LamAS.asF D f₁ f₂ f₁ τ₁ σS))
        (hx : Work.MotV5.LamAS.asIota D f₁ f₂ (x : Work.MotV5.LamAS.asML D f₁ f₂) ∈
          Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS),
        Work.MotV5.LamAS.asIota D f₁ f₂ (Θ x) =
          θ ⟨Work.MotV5.LamAS.asIota D f₁ f₂ x, hx⟩ := by
  classical
  -- The two twist fields, pulled back to `M`, are `comap`s of the twist fields along `asIota`.
  -- Since both twist fields lie in the range of `asIota` (`hF1`, `hF2`), the base-change map
  -- restricts to `K`-isomorphisms `asF i ≃ₐ ↥(asTwistFieldTrue … i)`, and transporting `θ`
  -- across these restrictions gives a `K`-isomorphism of the two `asF`'s.
  have key₁ := comap_algEquiv_of_le_fieldRange (asIota D f₁ f₂) (asIota_injective D f₁ f₂)
      (Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS) hF1
  have key₂ := comap_algEquiv_of_le_fieldRange (asIota D f₁ f₂) (asIota_injective D f₁ f₂)
      (Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS) hF2
  let e₁ : (Work.MotV5.LamAS.asF D f₁ f₂ f₁ τ₁ σS) ≃ₐ[RatFunc 𝕜]
      ↥(Work.MotV5.asTwistFieldTrue D f₁ τ₁ σS) := key₁.choose
  have he₁ : ∀ x : (Work.MotV5.LamAS.asF D f₁ f₂ f₁ τ₁ σS),
      (e₁ x : Work.MotV.Om D) =
        (Work.MotV5.LamAS.asIota D f₁ f₂) (x : Work.MotV5.LamAS.asML D f₁ f₂) :=
    fun x => key₁.choose_spec x
  let e₂ : (Work.MotV5.LamAS.asF D f₁ f₂ f₂ τ₂ σS) ≃ₐ[RatFunc 𝕜]
      ↥(Work.MotV5.asTwistFieldTrue D f₂ τ₂ σS) := key₂.choose
  have he₂ : ∀ x : (Work.MotV5.LamAS.asF D f₁ f₂ f₂ τ₂ σS),
      (e₂ x : Work.MotV.Om D) =
        (Work.MotV5.LamAS.asIota D f₁ f₂) (x : Work.MotV5.LamAS.asML D f₁ f₂) :=
    fun x => key₂.choose_spec x
  let θ' : (Work.MotV5.LamAS.asF D f₁ f₂ f₁ τ₁ σS) ≃ₐ[RatFunc 𝕜]
      (Work.MotV5.LamAS.asF D f₁ f₂ f₂ τ₂ σS) := e₁.trans (θ.trans e₂.symm)
  -- Linear disjointness and the sup conditions are exactly the hypotheses of the general
  -- extension result, which produces an `L`-algebra automorphism of `M` extending `θ'`.
  obtain ⟨Θ, hΘ⟩ := Work.MotT.extend_algEquiv_of_linearDisjoint
    (F₁ := Work.MotV5.LamAS.asF D f₁ f₂ f₁ τ₁ σS)
    (F₂ := Work.MotV5.LamAS.asF D f₁ f₂ f₂ τ₂ σS)
    (K := RatFunc 𝕜) (L := ↥(Work.MotV5.LamAS.asL2 (𝕜 := 𝕜) f₁ f₂))
    (Ω := Work.MotV5.LamAS.asML D f₁ f₂) hLI1 hLI2 hsup1 hsup2 θ'
  refine ⟨Θ, ?_⟩
  intro x hx
  rw [hΘ x]
  -- `asIota (θ' x) = e₂ (θ' x)`, and `θ' = e₁ ≫ θ ≫ e₂⁻¹`, so `e₂ (θ' x) = θ (e₁ x)`;
  -- finally `e₁ x = ⟨asIota x, hx⟩` by definition of the restriction.
  rw [← he₂ (θ' x)]
  have h1 : e₂ (θ' x) = θ (e₁ x) := by
    simp only [θ']
    rw [AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.apply_symm_apply]
  have h2 : e₁ x = ⟨asIota D f₁ f₂ (x : asML D f₁ f₂), hx⟩ := by
    apply Subtype.ext
    exact he₁ x
  rw [h1, h2]

end Work.MotV5.LamAS
