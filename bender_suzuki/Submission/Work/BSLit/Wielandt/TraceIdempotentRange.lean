import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.Wielandt

open LinearMap

/-- An idempotent endomorphism of a module fixes each element of its range. -/
theorem map_eq_self_of_mem_range {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    (P : M →ₗ[R] M) (hP : P * P = P) {x : M} (hx : x ∈ LinearMap.range P) : P x = x := by
  obtain ⟨y, rfl⟩ := hx
  have := congrArg (fun (f : M →ₗ[R] M) => f y) hP
  simpa using this

/-- For an idempotent endomorphism `P` of a free finite module `M` over a commutative ring `R`
whose range is again free and finite, the trace of `P` is (the image of) the natural-number rank
of its range: `tr P = finrank R (range P)`.

Route: `P = (range P).subtype ∘ π` where `π : M →ₗ[R] range P` is the corestriction of `P`;
`LinearMap.trace_comp_comm'` moves the trace to `π ∘ (range P).subtype = id` (since `P` is a
projection, `P x = x` for `x ∈ range P`), and `trace_id` gives `finrank`. -/
theorem TraceIdempotentRange {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] (P : M →ₗ[R] M) (hP : P * P = P)
    [Module.Free R (LinearMap.range P)] [Module.Finite R (LinearMap.range P)] :
    LinearMap.trace R M P = (Module.finrank R (LinearMap.range P) : R) := by
  -- The corestriction of `P` onto its own range.
  let P' : M →ₗ[R] LinearMap.range P :=
    P.codRestrict (LinearMap.range P) fun x => LinearMap.mem_range_self P x
  -- The inclusion of the range back into `M`.
  let ι : LinearMap.range P →ₗ[R] M := (LinearMap.range P).subtype
  have h1 : ι ∘ₗ P' = P := by
    ext x
    simp only [LinearMap.comp_apply, P', ι, LinearMap.codRestrict_apply, Submodule.subtype_apply]
  have h2 : P' ∘ₗ ι = 1 := by
    ext x
    change P (x : M) = (x : M)
    exact map_eq_self_of_mem_range P hP x.2
  calc LinearMap.trace R M P
      = LinearMap.trace R M (ι ∘ₗ P') := by rw [h1]
    _ = LinearMap.trace R (LinearMap.range P) (P' ∘ₗ ι) := LinearMap.trace_comp_comm' P' ι
    _ = LinearMap.trace R (LinearMap.range P) 1 := by rw [h2]
    _ = (Module.finrank R (LinearMap.range P) : R) := LinearMap.trace_one R (LinearMap.range P)

end Work.BSLit.Wielandt
