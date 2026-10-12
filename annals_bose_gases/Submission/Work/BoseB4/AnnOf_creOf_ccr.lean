import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.Ann_cre_ccr
import Submission.Work.BoseB4.ModeFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.AnnOf_creOf_ccr` — the mode-system CCR

`Work.BoseB4.Ann_cre_ccr` proves the *one-mode* canonical commutation relation
`[a_l, a_{l'}^†] = δ_{ll'}` on the real bosonic Fock space `RealFock m`.  Here we
lift it to arbitrary **superpositions** of modes: for coordinate vectors
`f g : Fin m → ℝ`,

  `[annOf m f, creOf m g] = gram f g · 1`,

i.e. FS `eq:Commutator_general` in its coordinate form.  This is the `ccr` field
of node B7's `FockData` interface (`Work.BoseB4.B7Instance`).

The mathematical content is pure multilinearity: if the endomorphisms `A i` and
`C j` of a module satisfy `[A i, C j] = δ_{ij}`, then

  `[Σ_i f_i • A_i, Σ_j g_j • C_j] = (Σ_{j} g_j · f_j) • 1`.

The proof is the reduction `ccr_sum` below, with the (trivial but pervasive)
finite-sum bookkeeping isolated in `comp_sum_smul_expand` and the Kronecker
contraction `sum_ite_mul_eq`.

Everything is stated for an arbitrary commutative ring `R`, an `R`-module `M` and
a finite index type `ι`, so that the same reduction is available in any other
mode model; the Fock statement is the instance `R = ℝ`, `M = RealFock m`,
`ι = Fin m`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB4

set_option autoImplicit false

/-! ## 1. Bilinear expansion of a composition of finite sums -/

/-- The composition of two finite sums of endomorphisms expands bilinearly:
`(Σ_i f_i • A_i).comp (Σ_j g_j • C_j) = Σ_i Σ_j (f_i * g_j) • (A_i.comp C_j)`. -/
lemma comp_sum_smul_expand {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] (A C : ι → Module.End R M) (f g : ι → R) :
    (∑ i, f i • A i).comp (∑ j, g j • C j)
      = ∑ i, ∑ j, (f i * g j) • ((A i).comp (C j)) := by
  ext x
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_smul]

/-! ## 2. The Kronecker contraction `Σ_i Σ_j δ_{ij} c_{ij} = Σ_i c_{ii}` -/

/-- `Σ_i f_i • 1` collects into a single scalar multiple of the identity. -/
lemma sum_ite_mul_smul_one {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] [DecidableEq ι] (f g : ι → R) :
    (∑ i, ∑ j, (if i = j then (f i * g j) else 0) • (1 : Module.End R M))
      = (∑ i, f i * g i) • 1 := by
  have hdiag : ∀ i, (∑ j, (if i = j then (f i * g j) else 0) • (1 : Module.End R M))
      = (f i * g i) • (1 : Module.End R M) := by
    intro i
    rw [← Finset.sum_smul, Finset.sum_ite_eq]
    simp
  rw [Finset.sum_congr rfl fun i _ => hdiag i, ← Finset.sum_smul]

/-! ## 3. The commutator of two mode superpositions -/

/-- **The mode-system CCR.**  If the endomorphisms `A i, C j` satisfy
`[A i, C j] = δ_{ij} • 1` for all `i j`, then the superpositions
`Σ_i f_i • A_i` and `Σ_j g_j • C_j` satisfy
`[Σ_i f_i • A_i, Σ_j g_j • C_j] = (Σ_i f_i * g_i) • 1`. -/
lemma ccr_sum {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι]
    [DecidableEq ι] (A C : ι → Module.End R M)
    (h : ∀ i j, (A i).comp (C j) = (C j).comp (A i) + (if i = j then (1 : R) else 0) • 1)
    (f g : ι → R) :
    (∑ i, f i • A i).comp (∑ j, g j • C j)
      = (∑ j, g j • C j).comp (∑ i, f i • A i) + (∑ i, f i * g i) • 1 := by
  rw [comp_sum_smul_expand A C f g, comp_sum_smul_expand C A g f]
  have hsplit : (∑ i, ∑ j, (f i * g j) • ((A i).comp (C j)))
      = (∑ i, ∑ j, (f i * g j) • ((C j).comp (A i)))
        + ∑ i, ∑ j, (if i = j then (f i * g j) else 0) • (1 : Module.End R M) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h i j, smul_add, smul_smul, mul_ite, mul_one, mul_zero]
  rw [hsplit, Finset.sum_comm]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  · exact sum_ite_mul_smul_one f g

/-! ## 4. The Fock-space statement -/

/-- FS `eq:Commutator_general` for the mode superpositions
`annOf m f = Σ_l f_l ∂_l` and `creOf m g = Σ_l g_l · x_l` on the real bosonic
Fock space over `m` modes: their commutator is the Gram product `gram f g` of the
one-particle coordinate vectors. -/
theorem AnnOf_creOf_ccr {m : ℕ} (f g : Fin m → ℝ) :
    (Work.BoseB4.annOf m f).comp (Work.BoseB4.creOf m g)
      = (Work.BoseB4.creOf m g).comp (Work.BoseB4.annOf m f)
        + (Work.BoseB4.gram f g) • (1 : Work.BoseB4.RealFock m →ₗ[ℝ] Work.BoseB4.RealFock m) := by
  exact ccr_sum (ann m) (cre m) (fun l l' => Ann_cre_ccr l l') f g

end Work.BoseB4
