import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.IsAdjoinRoot
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.style.haveILetI false

namespace Commons.FieldTheory

open Polynomial IntermediateField
open scoped IntermediateField

universe u

/-- If `f` is a separable polynomial over a field `F`, then `F[X]/(f)` (which is a field
as soon as `f` is irreducible) is a separable extension of `F`.  This is the generic
"adjoining a root of a separable polynomial yields a separable extension" statement,
proved via the primitive-element description of `AdjoinRoot f` and
`IntermediateField.isSeparable_adjoin_simple_iff_isSeparable`. -/
theorem isSeparable_adjoinRoot {F : Type u} [Field F] {f : F[X]} [Fact (Irreducible f)]
    (hf : f.Separable) : Algebra.IsSeparable F (AdjoinRoot f) := by
  have hfroot : aeval (AdjoinRoot.root f) f = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  -- the adjoined root is separable over `F`
  have hsep_root : IsSeparable F (AdjoinRoot.root f) :=
    hf.of_dvd (minpoly.dvd F (AdjoinRoot.root f) hfroot)
  -- hence the simple extension it generates is separable
  have hsep : Algebra.IsSeparable F F⟮AdjoinRoot.root f⟯ :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable F (AdjoinRoot f)).2 hsep_root
  -- and this simple extension is the whole of `F[X]/(f)`
  have htop : F⟮AdjoinRoot.root f⟯ = ⊤ := by
    rw [← AdjoinRoot.isAdjoinRoot_root_eq_root]
    exact IsAdjoinRoot.primitive_element_root (AdjoinRoot.isAdjoinRoot f)
  rw [htop] at hsep
  haveI := hsep
  exact AlgEquiv.Algebra.isSeparable (IntermediateField.topEquiv (F := F) (E := AdjoinRoot f))

/-- A field `F` is separably closed as soon as it has no finite separable extension of
degree `> 1`.  Indeed, a separable irreducible polynomial `p` over `F` of positive degree
gives rise to the finite separable extension `F[X]/(p)` of degree `deg p`, so the hypothesis
forces `deg p ≤ 1`; a linear polynomial has a root in `F`. -/
theorem isSepClosed_of_no_finite_separable_extension {F : Type u} [Field F]
    (h : ∀ (F' : Type u) [Field F'] [Algebra F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'],
      Module.finrank F F' ≤ 1) : IsSepClosed F := by
  refine IsSepClosed.of_exists_root F ?_
  intro p hpmon hpirr hpsep
  haveI : Fact (Irreducible p) := ⟨hpirr⟩
  have hp0 : p ≠ 0 := hpmon.ne_zero
  -- `F[X]/(p)` is a finite-dimensional separable extension of `F`
  haveI : FiniteDimensional F (AdjoinRoot p) := hpmon.finite_adjoinRoot
  haveI : Algebra.IsSeparable F (AdjoinRoot p) := isSeparable_adjoinRoot hpsep
  have hle : Module.finrank F (AdjoinRoot p) ≤ 1 := h (AdjoinRoot p)
  -- its degree is the degree of `p`
  have hrank : Module.finrank F (AdjoinRoot p) = p.natDegree :=
    (PowerBasis.finrank (AdjoinRoot.powerBasis hp0)).trans (AdjoinRoot.powerBasis_dim hp0)
  have hnd : p.natDegree ≤ 1 := by rw [← hrank]; exact hle
  -- a monic irreducible polynomial is not constant
  have hnd_ne_zero : p.natDegree ≠ 0 := by
    intro hz
    have hC : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero hz
    have hcoeff : p.coeff 0 = 1 := by
      rw [← hz]; exact hpmon.coeff_natDegree
    rw [hC, hcoeff, C_1] at hpirr
    exact hpirr.not_isUnit isUnit_one
  have hnd1 : p.natDegree = 1 :=
    le_antisymm hnd (Nat.one_le_iff_ne_zero.mpr hnd_ne_zero)
  -- a monic polynomial of degree one is `X + c`, whose root is `-c`
  refine ⟨-(p.coeff 0), ?_⟩
  rw [hpmon.eq_X_add_C hnd1]
  simp

end Commons.FieldTheory