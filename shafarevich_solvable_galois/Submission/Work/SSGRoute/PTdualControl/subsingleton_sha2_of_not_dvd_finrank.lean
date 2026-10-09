import Mathlib
import Submission.Work.SSGRoute.ShaCocycles
import Submission.Work.SSGRoute.sha2_restrict_vanish
import Submission.Work.SSGRoute.coboundary2_top_of_coboundary2_on_coprime_index
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ш²(k,E)` vanishes when `p ∤ [K:k]`

`Work.SSGRoute.sha2_restrict_vanish` shows that a locally trivial `2`-cocycle of `Z2loc p k Ω K E`
is a `2`-coboundary on the open normal subgroup `K.fixingSubgroup ≤ Ω ≃ₐ[k] Ω`, of index `[K:k]`,
with a locally constant primitive.  When `p ∤ [K:k]` the coefficient prime is invertible mod the
index, so the cochain-level transfer of
`Work.SSGRoute.coboundary2_top_of_coboundary2_on_coprime_index`
(`cor ∘ res = index`, hence `res`-injectivity on `p`-primary classes) promotes the local triviality
to a *global* `2`-coboundary: `Sha2 p k Ω K E` is a subsingleton.

This is the `p ∤ [K:k]` half of the case split used by the assembly of the atom
`Work.SSGRoute.tatePoitouEmbedding`: by `Work.SSGRoute.PTdualControl.nsmul_pairK` the Poitou–Tate
pairing values at level `K` are `p`-torsion in `H²(Gal(K/k),C_K) ≅ ℤ/[K:k]`, so they *vanish* when
`p ∤ [K:k]`, and the control statement is then witnessed by `l = 0`
(`Work.SSGRoute.PTdualControl.sha2_dual_control_alt_of_sha2_vanish`).  No duality is needed in that
case.
-/

namespace Work.SSGRoute.PTdualControl

/-- **`Ш²(k,E)` vanishes when `p ∤ [K:k]`**: every locally trivial continuous `2`-cocycle
`G_k × G_k → E` is a global `2`-coboundary, `E` being a finite `p`-torsion
`Gal(K/k)`-module and `[K:k]` coprime to `p`. -/
theorem subsingleton_sha2_of_not_dvd_finrank (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (hp : ¬ p ∣ Module.finrank k K) :
    Subsingleton (Work.SSGRoute.Sha2 p k Ω K E) := by
  haveI hp' : p.Prime := Fact.out
  -- `K.fixingSubgroup` is the kernel of the (surjective) restriction map
  have hker : (SSGRoute.res k K).ker = K.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker K
  have hnorm : K.fixingSubgroup.Normal := by
    rw [← hker]; exact MonoidHom.normal_ker _
  have hopen : IsOpen (K.fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :=
    IntermediateField.fixingSubgroup_isOpen K
  have hclosed : IsClosed (K.fixingSubgroup : Set (Ω ≃ₐ[k] Ω)) :=
    (K.fixingSubgroup.isClosed_of_isOpen hopen)
  -- its index is the degree `[K:k]`
  have hsurj : Function.Surjective (SSGRoute.res k K) :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) (E := Ω)
  have hindex : K.fixingSubgroup.index = Module.finrank k K := by
    rw [← hker, Subgroup.index_ker (SSGRoute.res k K), MonoidHom.range_eq_top.mpr hsurj,
      Subgroup.card_top]
    exact IsGalois.card_aut_eq_finrank k K
  have hfin : K.fixingSubgroup.FiniteIndex :=
    ⟨by rw [hindex]; exact (Module.finrank_pos (R := k) (M := K)).ne'⟩
  have hcop : Nat.Coprime K.fixingSubgroup.index p := by
    rw [hindex]; exact (hp'.coprime_iff_not_dvd.mpr hp).symm
  -- every locally trivial `2`-cocycle is a global `2`-coboundary
  have hle : Work.SSGRoute.Z2loc p k Ω K E ≤ Work.SSGRoute.B2top p k Ω K E := by
    intro c hc
    exact Work.SSGRoute.coboundary2_top_of_coboundary2_on_coprime_index p
      (SSGRoute.res k K) K.fixingSubgroup hnorm hclosed hfin hcop c hc.1 hc.2.1
      (Work.SSGRoute.sha2_restrict_vanish p k Ω K ζ hζ hζK E c hc)
  have hq : (Work.SSGRoute.B2top p k Ω K E).comap
      (Work.SSGRoute.Z2loc p k Ω K E).subtype = ⊤ := by
    rw [Submodule.eq_top_iff']
    rintro ⟨c, hc⟩
    exact hle hc
  exact Submodule.Quotient.subsingleton_iff.mpr hq

end Work.SSGRoute.PTdualControl
