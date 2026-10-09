import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The exactness of the class formation at `Ext^{r+1}_G(M, Kˣ)`

`Work.SSGRoute.Sha2Lib.pt_core_assembly` records the exactness at `Ext^r_G(M, C_K)`
(`exists_extToClasses_iff_extDelta_eq_zero`).  Its *partner* on the other end of the long exact
sequence of `0 → Kˣ → 𝕀_K → C_K → 0` is proved here:

  `extToIdeles y = 0  →  ∃ x : Ext^r_G(M, C_K), extDelta x = y`   for `y : Ext^{r+1}_G(M, Kˣ)`,

i.e. `ker(Ext^{r+1}_G(M, Kˣ) → Ext^{r+1}_G(M, 𝕀_K)) ⊆ im(extDelta)`.  (The reverse inclusion is the
formal consequence `extDelta ≫ extToIdeles = 0` of `ShortComplex.ShortExact.extClass_comp`; the
present direction is the load-bearing one.)

This is the input that the assembly of the atom `Work.SSGRoute.tatePoitouEmbedding` (node `G5`)
needs in order to *produce* the class `x_b ∈ Ext¹_G(E', C_K)` attached to a `Ш²`-class `b`: by the
node `E1a` (`ext_sha2_bridge`) the class `β b ∈ Ext²_G(E', Kˣ)` satisfies exactly
`extToIdeles (β b) = 0`, and the pairing `pairK x_b (β_{E1b} h) ∈ H²(Gal(K/k), C_K)` — the value fed
into the `p`-torsion character `χ` — is built from such an `x_b`.
-/

open CategoryTheory

namespace Work.SSGRoute.PTdualControl

open SSGRoute.PTExt

/-- **Exactness of the class formation at `Ext^{r+1}_G(M, Kˣ)`** (the `im(extDelta)` half).  A class
of `Ext^{r+1}_{Gal(K/k)}(M, Kˣ)` that dies under postcomposition with `Kˣ → 𝕀_K` is the connecting
image of a class of `Ext^r_{Gal(K/k)}(M, C_K)`. -/
theorem exists_extDelta_eq_of_extToIdeles_eq_zero
    (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    {M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)} {r : ℕ}
    (y : Abelian.Ext.{0} M (SSGRoute.PTExt.unitsK k K) (r + 1))
    (hy : SSGRoute.PTExt.extToIdeles (k := k) (K := K) y = 0) :
    ∃ x : Abelian.Ext.{0} M (SSGRoute.PTExt.classesK k K) r,
      SSGRoute.PTExt.extDelta (k := k) (K := K) x = y := by
  obtain ⟨x, hx⟩ := Abelian.Ext.covariant_sequence_exact₁ (X := M)
    (S := SSGRoute.PTExt.sesK k K) (NK.HassePrinciple.ideleShortComplex_shortExact k K) y
    (n₁ := r + 1) hy (n₀ := r) (hn₀ := rfl)
  exact ⟨x, hx⟩

end Work.SSGRoute.PTdualControl
