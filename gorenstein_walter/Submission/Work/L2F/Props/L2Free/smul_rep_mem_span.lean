import Mathlib

namespace Work.L2F.Props.L2Free

/-- If `A ∈ SL(2,F)` fixes a point `p` of `ℙ¹(F)`, then it maps the representative vector
`p.rep` into the line it spans, i.e. `p.rep` is an eigenvector of `A`. -/
theorem smul_rep_mem_span {F : Type*} [Field F]
    (A : Matrix.SpecialLinearGroup (Fin 2) F) (p : Projectivization F (Fin 2 → F))
    (h : A • p = p) :
    A • Projectivization.rep p ∈ Submodule.span F {Projectivization.rep p} := by
  -- `A • rep p` is again nonzero, and it represents the same projective point as `rep p`.
  have hne : A • Projectivization.rep p ≠ 0 :=
    (smul_ne_zero_iff_ne A).mpr (Projectivization.rep_nonzero p)
  have h1 : Projectivization.mk F (A • Projectivization.rep p) hne =
      Projectivization.mk F (Projectivization.rep p) (Projectivization.rep_nonzero p) := by
    rw [← Projectivization.mk_rep p] at h
    rw [Projectivization.smul_mk] at h
    exact h
  -- Two nonzero vectors give the same projective point iff one is a scalar multiple of the other.
  obtain ⟨a, ha⟩ :=
    (Projectivization.mk_eq_mk_iff' F (A • Projectivization.rep p) (Projectivization.rep p)
      hne (Projectivization.rep_nonzero p)).mp h1
  rw [Submodule.mem_span_singleton]
  exact ⟨a, ha⟩

end Work.L2F.Props.L2Free
