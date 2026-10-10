import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.SSGRoute.E1aClean.completion_quotient_uniqueDivisible
import Submission.Work.SSGRoute.ExtChain.ext_push_engine
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E1aClean

/-- **Unique `n`-divisibility of a quotient of units, abstractly.**

Let `f : E →* L` be a homomorphism of groups with `L` commutative.  Suppose that

* (`hdiv`) every `z : L` can be written `z = f u * w ^ n` with `w : L` and `u : E`, for every
  `n > 0`;
* (`hpur`) if `z ^ n = f u` with `n > 0`, then already `z = f u'` for some `u' : E`.

Then for every `p > 0` multiplication by `p` is a bijection of the quotient of the additive
group `Additive L` by the (additive subgroup attached to the) image of `f`; in multiplicative
terms, the quotient `L / f(E)` is uniquely `p`-divisible.

Surjectivity of `p • ·` is `hdiv` at `n = p`; injectivity is `hpur` at `n = p` applied to
`z = a⁻¹ * b` once `(a ^ p)⁻¹ * b ^ p = (a⁻¹ * b) ^ p = f u` is known. -/
theorem nsmul_bijective_quotient_of_uniqueDivisible {E L : Type*} [Group E] [CommGroup L]
    (f : E →* L) (p : ℕ) (hp : 0 < p)
    (hdiv : ∀ n : ℕ, 0 < n → ∀ z : L, ∃ (w : L) (u : E), z = f u * w ^ n)
    (hpur : ∀ n : ℕ, 0 < n → ∀ (z : L) (u : E), z ^ n = f u → ∃ u' : E, z = f u') :
    Function.Bijective (fun z : Additive L ⧸ (MonoidHom.range f).toAddSubgroup => p • z) := by
  -- `mk` of `ofMul a` and of `ofMul b` agree exactly when `a⁻¹ * b` lies in the range of `f`.
  have aux1 : ∀ a b : L, (QuotientAddGroup.mk (Additive.ofMul a) :
        Additive L ⧸ (MonoidHom.range f).toAddSubgroup)
      = QuotientAddGroup.mk (Additive.ofMul b) ↔ a⁻¹ * b ∈ MonoidHom.range f := by
    intro a b
    rw [QuotientAddGroup.eq, Additive.mem_toAddSubgroup]
    constructor <;> intro h <;> simpa using h
  -- `p •` on the quotient is the `p`-th power upstairs; this is `rfl` for `Additive`.
  have aux2 : ∀ (n : ℕ) (A : Additive L),
      n • (QuotientAddGroup.mk A : Additive L ⧸ (MonoidHom.range f).toAddSubgroup)
        = QuotientAddGroup.mk (Additive.ofMul (A.toMul ^ n)) := by
    intro n A
    rw [← QuotientAddGroup.mk_nsmul]
    rfl
  refine ⟨?_, ?_⟩
  · -- injectivity
    intro x
    refine QuotientAddGroup.induction_on x ?_
    intro A y
    refine QuotientAddGroup.induction_on y ?_
    intro B h
    simp only [] at h
    rw [aux2 p A, aux2 p B] at h
    have hmem : (A.toMul ^ p)⁻¹ * B.toMul ^ p ∈ MonoidHom.range f :=
      (aux1 (A.toMul ^ p) (B.toMul ^ p)).mp h
    obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hmem
    have hkey : (A.toMul⁻¹ * B.toMul) ^ p = f u := by
      rw [mul_pow, inv_pow, ← hu]
    obtain ⟨u', hu'⟩ := hpur p hp (A.toMul⁻¹ * B.toMul) u hkey
    exact (aux1 A.toMul B.toMul).mpr (by rw [hu']; exact MonoidHom.mem_range.mpr ⟨u', rfl⟩)
  · -- surjectivity
    intro z
    refine QuotientAddGroup.induction_on z ?_
    intro A
    obtain ⟨w, u, hw⟩ := hdiv p hp A.toMul
    refine ⟨QuotientAddGroup.mk (Additive.ofMul w), ?_⟩
    show p • QuotientAddGroup.mk (Additive.ofMul w) = QuotientAddGroup.mk A
    rw [aux2 p (Additive.ofMul w)]
    simp only [toMul_ofMul]
    have key : (w ^ p)⁻¹ * A.toMul = f u := by
      rw [hw, mul_comm (f u) (w ^ p), inv_mul_cancel_left]
    exact (aux1 (w ^ p) A.toMul).mpr (by rw [key]; exact MonoidHom.mem_range.mpr ⟨u, rfl⟩)

/-- **The arithmetic half of `(PUSH)`**: for the henselisation `K^h = Ω^{D_A ⊓ Gal(Ω/K)}` of `K`
at a finite place `A` of `Ω` and an injective field map `φ : K^h →+* K_q` whose image is relatively
algebraically closed in the completion `K_q = localField K (ofFinite q)` (both supplied by
`E1aClean.decompField_embeds_completion`), multiplication by `p` is a bijection on the quotient of
the additive group `K_qˣ` by the image of `(K^h)ˣ`.

This is exactly the hypothesis `hQ` of the `(PUSH)` engine
`Work.SSGRoute.ExtChain.postcomp_mk₀_bijective_of_ptorsion_uniqueDivisible`
(`ExtChain/ext_push_engine.lean`): surjectivity is the divisibility clause and injectivity the
purity clause of `E1aClean.completion_quotient_uniqueDivisible`, both with `n = p` (valid since
`0 < p`). -/
theorem unitsQuotient_pow_bijective_fixed (k Ω : Type) [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (φ : ↥(IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)) →+*
      (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q)))
    (hφ : Function.Injective φ)
    (halg : ∀ z : NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite q),
      (∃ r : Polynomial ↥(IntermediateField.fixedField
            (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)),
          r ≠ 0 ∧ Polynomial.eval₂ φ z r = 0) →
        ∃ x : ↥(IntermediateField.fixedField (SSGRoute.decomp k A ⊓ (SSGRoute.res k K).ker)),
          φ x = z)
    (p : ℕ) [Fact p.Prime] :
    Function.Bijective (fun z : Additive (NK.GlobalCFT.Place.localField K
        (NK.GlobalCFT.Place.ofFinite q))ˣ ⧸
        (MonoidHom.range (Units.map φ.toMonoidHom)).toAddSubgroup => p • z) := by
  have hUD := completion_quotient_uniqueDivisible k Ω K A hA q φ hφ halg
  exact nsmul_bijective_quotient_of_uniqueDivisible (Units.map φ.toMonoidHom) p
    (Fact.out : p.Prime).pos hUD.1 hUD.2

end Work.SSGRoute.E1aClean
