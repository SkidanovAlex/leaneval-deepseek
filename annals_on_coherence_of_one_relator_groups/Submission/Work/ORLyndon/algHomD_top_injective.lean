/-
# Injectivity of `K[G] → ↥(D ⊤)`

The algebra homomorphism `MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop` sends `single g k` to
`k • genTop g`, i.e. it is the `K`-algebra map `K[G] → D(G)` determined by the image of `G` in
the division closure `D ⊤` of `K[G]` in the ambient ring `U`.  We show it is injective, i.e.
`K[G] ⊆ D(G)`.

As in `Work.ORAssembly.Ring.toS_injective`, the argument is Linnell independence
(`TorsionData.independence`, input (I1)) at the trivial subgroup `⊥`: the composite
`K[G] → D ⊤ → U` sends a finitely supported family to a `D(⊥)`-linear combination of the
`gen g` with pairwise distinct group parts (they lie in pairwise distinct cosets of `⊥`), and
such a combination vanishes only if every coefficient does.  The coefficients lie in
`D(⊥) ⊇ K` (all subalgebras contain the scalars), and the structure map `K → U` is injective
because `U` is nontrivial and `K` is a field.

Injectivity is *not* formal: for a general `K`-algebra the images of a group under a monoid
homomorphism need not be `K`-linearly independent; this is exactly what (I1) provides.
-/
import Mathlib
import Submission.Work.ORTorsion.Main

namespace Work.ORTorsion

namespace TorsionData

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]

/-- The group part `G → U` of a torsion datum, through the units. -/
noncomputable def genU (L : TorsionData K G U) : G →* U :=
  (Units.coeHom U).comp L.gen

@[simp] theorem genU_apply (L : TorsionData K G U) (g : G) :
    genU L g = (L.gen g : U) := rfl

/-- The `K`-algebra map `K[G] → U` attached to a torsion datum (`single g k ↦ k • gen g`). -/
noncomputable def toU (L : TorsionData K G U) : MonoidAlgebra K G →ₐ[K] U :=
  MonoidAlgebra.lift K U G (genU L)

@[simp] theorem toU_single (L : TorsionData K G U) (g : G) (k : K) :
    toU L (MonoidAlgebra.single g k) = k • (L.gen g : U) :=
  MonoidAlgebra.lift_single (genU L) g k

/-- The composite `K[G] → ↥(D ⊤) → U` is `toU`. -/
theorem coe_lift_eq_toU (L : TorsionData K G U) (x : MonoidAlgebra K G) :
    ((MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop x : ↥(L.D ⊤)) : U) = toU L x := by
  have hAlg : (Subalgebra.val (L.D ⊤)).comp
      (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop) = toU L := by
    apply MonoidAlgebra.algHom_ext
    · intro g
      rw [AlgHom.comp_apply, toU, MonoidAlgebra.lift_single, MonoidAlgebra.lift_single,
        one_smul, one_smul]
      rfl
    · ext
  exact congrArg (fun f : MonoidAlgebra K G →ₐ[K] U => f x) hAlg

/-- The explicit form of `toU` on `K[G]`, as a sum over `supp x`: this is the
`D(⊥)`-linear combination appearing in Linnell independence. -/
theorem toU_apply (L : TorsionData K G U) (x : MonoidAlgebra K G) :
    toU L x = ∑ i : ↑x.coeff.support, algebraMap K U (x.coeff ↑i) * (L.gen (↑i : G) : U) := by
  rw [toU, MonoidAlgebra.lift_apply', Finsupp.sum]
  rw [← Finset.sum_coe_sort x.coeff.support (fun a => algebraMap K U (x.coeff a) * genU L a)]
  rfl

/-- Linnell independence `(I1)` of a torsion datum for an arbitrary finite indexing type: if
the group parts `g i` lie in pairwise distinct right cosets of `H` (i.e.
`(g i) * (g j)⁻¹ ∈ H → i = j`) and the coefficients `a i` all lie in the division closure `D H`,
then a vanishing sum `∑ i, a i * gen (g i)` forces every coefficient to vanish.  The statement is
reduced to the `Fin n` version in `TorsionData.independence` by transporting along
`Fintype.equivFin ι`. -/
theorem independence_fintype (L : TorsionData K G U) {H : Subgroup G} {ι : Type*} [Fintype ι]
    (g : ι → G) (hinj : ∀ i j, (g i) * (g j)⁻¹ ∈ H → i = j) (a : ι → U)
    (ha : ∀ i, a i ∈ L.D H) (hsum : ∑ i, a i * (L.gen (g i) : U) = 0) : ∀ i, a i = 0 := by
  classical
  let e := Fintype.equivFin ι
  have hid : ∀ i j : Fin (Fintype.card ι), (g (e.symm i)) * (g (e.symm j))⁻¹ ∈ H → i = j := by
    intro i j hij
    have h1 : e.symm i = e.symm j := hinj _ _ hij
    exact e.symm.injective h1
  have hsum' : ∑ k : Fin (Fintype.card ι), a (e.symm k) * (L.gen (g (e.symm k)) : U) = 0 := by
    rw [Equiv.sum_comp e.symm (fun i => a i * (L.gen (g i) : U))]
    exact hsum
  have h := L.independence H (Fintype.card ι) (fun k => g (e.symm k)) hid
    (fun k => a (e.symm k)) (fun k => ha _) hsum'
  intro i
  simpa using h (e i)

end TorsionData

end Work.ORTorsion

namespace Work.ORLyndon

open Work.ORTorsion

/-- **The map `K[G] → ↥(D ⊤)` is injective**, i.e. `K[G] ⊆ D(G)`.  This is Linnell independence
(I1) of `TorsionData` at the trivial subgroup. -/
theorem algHomD_top_injective {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U]
    [Nontrivial U] [Algebra K U] (L : Work.ORTorsion.TorsionData K G U) :
    Function.Injective (MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop) := by
  -- It suffices to show that an element of `K[G]` with vanishing image vanishes.
  have key : ∀ x : MonoidAlgebra K G,
      MonoidAlgebra.lift K ↥(L.D ⊤) G L.genTop x = 0 → x = 0 := by
    intro x hx
    classical
    -- Pushing the composite `K[G] → D ⊤ → U` along `TorsionData.toU`, the hypothesis becomes
    -- the vanishing of `∑_{g ∈ supp x} algebraMap K U (x g) * gen g` in `U`.
    have hsum : ∑ i : ↑x.coeff.support,
        algebraMap K U (x.coeff ↑i) * (L.gen (↑i : G) : U) = 0 := by
      rw [← TorsionData.toU_apply L x, ← TorsionData.coe_lift_eq_toU L x, hx]
      simp
    -- The group parts are the elements of `supp x`, all in distinct right cosets of `⊥`, and the
    -- coefficients lie in `D ⊥` (which contains the scalars).
    have hind := TorsionData.independence_fintype L (H := ⊥)
      (g := fun i : ↑x.coeff.support => (↑i : G))
      (hinj := fun i j hij => Subtype.ext (mul_inv_eq_one.mp (Subgroup.mem_bot.mp hij)))
      (a := fun i : ↑x.coeff.support => algebraMap K U (x.coeff ↑i))
      (ha := fun i => Subalgebra.algebraMap_mem (L.D ⊥) _)
      (hsum := hsum)
    -- Hence every coefficient of `x` vanishes.
    apply MonoidAlgebra.ext
    ext g
    by_cases hg : g ∈ x.coeff.support
    · have h3 : algebraMap K U (x.coeff g) = 0 := hind ⟨g, hg⟩
      by_contra hne
      have h4 : (x.coeff g) • (1 : U) = 0 := by
        rwa [Algebra.algebraMap_eq_smul_one] at h3
      have h5 : (1 : U) = 0 := by
        have h6 := congrArg (fun u : U => (x.coeff g)⁻¹ • u) h4
        simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul, smul_zero] using h6
      exact one_ne_zero h5
    · exact Finsupp.notMem_support_iff.mp hg
  intro x y hxy
  have h2 : x - y = 0 := key _ (by rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp h2

end Work.ORLyndon
