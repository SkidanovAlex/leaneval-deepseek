import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.pt_char_pTorsion
import Submission.Work.SSGRoute.exists_galois_level_p_dvd
import Submission.Work.SSGRoute.e6_util
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `χ` interface and the `p`-torsion of the Poitou--Tate pairing values

Two small, self-contained inputs of the assembly of the atom
`Work.SSGRoute.tatePoitouEmbedding` (`= G5` of `Submission/Work/SSGRoute/DESIGN_FIX2.md`):

* `char_pTorsion_level_of` — the `χ` interface: at any finite Galois level `K₀ ⊇ K` of `Ω` with
  `p ∣ [K₀:k]`, the `p`-torsion of `H²(Gal(K₀/k), C_{K₀})` is `𝔽_p` (a re-indexing of the proved
  `Work.SSGRoute.pt_char_pTorsion`).  The *existence* of such a level is the proved
  `Work.SSGRoute.exists_galois_level_p_dvd`, so `G5` can always find the level `K₀` at which the
  pairing values are read off.
* `nsmul_pairK` — the pairing values `pairK x h = ⟨x,h⟩ ∈ H²(Gal(K/k), C_K)` are `p`-torsion as
  soon as the coefficients `M` are (the item recorded in `DESIGN_FIX2.md` §5).

Everything here is `sorry`-free and rests only on `propext`, `Classical.choice`, `Quot.sound`.
-/

open CategoryTheory

namespace Work.SSGRoute.PTdualControl

open SSGRoute.PTExt

/-- **The `χ` interface of `G5`.**  For a finite Galois intermediate field `K₀ ⊆ Ω` with
`p ∣ [K₀ : k]`, the `p`-torsion of `H²(Gal(K₀/k), C_{K₀}) = extH (classesK k K₀) 2` is a
subgroup `P`, and there is an additive bijection `χ : P ≃+ 𝔽_p`.  This is
`Work.SSGRoute.pt_char_pTorsion` with the level `K₀` presented as an `IntermediateField k Ω`
(the auxiliary level `K` of that statement is instantiated at `k`). -/
theorem char_pTorsion_level_of (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K₀ : IntermediateField k Ω)
    [FiniteDimensional k K₀] [IsGalois k K₀] (hp : p ∣ Module.finrank k K₀) :
    ∃ (P : AddSubgroup (SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k ↥K₀) 2))
      (χ : P →+ ZMod p),
      (∀ v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k ↥K₀) 2, v ∈ P ↔ p • v = 0) ∧
      Function.Bijective χ :=
  pt_char_pTorsion p k k ↥K₀ hp

set_option linter.unusedVariables false in
/-- **The pairing values are `p`-torsion.**  If the coefficients `M` are killed by `p`, then so is
the Yoneda product `pairK x h = h.comp x` of `x ∈ Ext¹_G(M,C_K)` with `h ∈ H¹(G,M)`.

Proof: `p • x = 0` because `M` is `p`-torsion (`Work.SSGRoute.E6Util.ext_nsmul_p_torsion_left`),
the map `x ↦ h.comp x` is additive, and additivity transfers `nsmul`. -/
theorem nsmul_pairK (p : ℕ) (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} (hM : ∀ m : M, p • m = 0)
    (x : CategoryTheory.Abelian.Ext.{0} M (SSGRoute.PTExt.classesK k K) 1)
    (h : SSGRoute.PTExt.extH M 1) :
    p • SSGRoute.PTExt.pairK (k := k) (K := K) x h = 0 := by
  have hx : p • x = 0 := SSGRoute.E6Util.ext_nsmul_p_torsion_left p hM x
  have key : ∀ m : ℕ, m • (h.comp x rfl) = h.comp (m • x) rfl := by
    intro m
    induction m with
    | zero => rw [zero_nsmul, zero_nsmul, Abelian.Ext.comp_zero]
    | succ m ih => rw [succ_nsmul, ih, succ_nsmul, Abelian.Ext.comp_add]
  show p • (h.comp x rfl) = 0
  rw [key p, hx, Abelian.Ext.comp_zero]

end Work.SSGRoute.PTdualControl
