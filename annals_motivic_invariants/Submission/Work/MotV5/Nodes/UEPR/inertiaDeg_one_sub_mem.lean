import Mathlib

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.MotV5.Nodes.UEPR

/-- **A field extension of degree `1` is trivial.**  If `L` is an `K`-algebra and a field, and the
`K`-dimension of `L` is `1`, then `algebraMap K L` is surjective: since `L` is nontrivial its
span (as a `K`-submodule) is nonzero, and a nonzero submodule of a one-dimensional space is
everything. -/
theorem surjective_algebraMap_of_finrank_eq_one {K L : Type*} [Field K] [Field L] [Algebra K L]
    (h : Module.finrank K L = 1) : Function.Surjective (algebraMap K L) := by
  haveI : Module.Free K L := Module.Free.of_divisionRing K L
  exact ((Algebra.finrank_eq_one_iff_bijective_algebraMap (F := K) (E := L)).mp h).2

/-- **Trivial inertia degree forces a trivial residue extension.**  For an integral extension
`R → S`, a prime `P` of `S` lying over a maximal ideal `p` of `R`, if the inertia degree
`P.inertiaDeg R` equals `1` then the residue ring map `R ⧸ p → S ⧸ P` is surjective; equivalently,
every element of `S` is congruent modulo `P` to an element of the image of `R`.

Since `R ⧸ p` and `S ⧸ P` are fields (`P` is maximal because it is prime and integral over the
maximal ideal `p`) and `P.inertiaDeg R = Module.finrank (R ⧸ p) (S ⧸ P)`, the hypothesis says
that `S ⧸ P` is a one-dimensional `R ⧸ p`-vector space, so the structure map is onto. -/
theorem inertiaDeg_one_sub_mem {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (P : Ideal S) [P.IsPrime] (p : Ideal R) [p.IsMaximal]
    [P.LiesOver p] (hf : P.inertiaDeg R = 1) :
    ∀ b : S, ∃ x : R, b - algebraMap R S x ∈ P := by
  -- `P` is maximal: it is prime and integral over the maximal ideal `p`.
  haveI : P.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal P p
  -- Both residue rings are fields, so the residue extension has a dimension over a field.
  letI : Field (R ⧸ p) := Ideal.Quotient.field p
  letI : Field (S ⧸ P) := Ideal.Quotient.field P
  -- The inertia degree is the dimension of the residue field extension.
  have hfr : Module.finrank (R ⧸ p) (S ⧸ P) = 1 := by
    rw [← Ideal.inertiaDeg_eq_of_isMaximal p P, hf]
  -- A one-dimensional extension of fields has surjective structure map.
  have hsurj : Function.Surjective (algebraMap (R ⧸ p) (S ⧸ P)) :=
    surjective_algebraMap_of_finrank_eq_one hfr
  intro b
  obtain ⟨c, hc⟩ := hsurj (Ideal.Quotient.mk P b)
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨x, ?_⟩
  -- The class of `algebraMap R S x` in `S ⧸ P` is the class of `b`.
  have h2 : Ideal.Quotient.mk P (algebraMap R S x) = Ideal.Quotient.mk P b := by
    rw [← Ideal.Quotient.algebraMap_mk_of_liesOver P p x, hx, hc]
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h3 : Ideal.Quotient.mk P (b - algebraMap R S x)
      = Ideal.Quotient.mk P b - Ideal.Quotient.mk P (algebraMap R S x) := map_sub _ _ _
  rw [h3, h2, sub_self]

end Work.MotV5.Nodes.UEPR
