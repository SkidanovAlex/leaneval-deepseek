import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotA.not_gen_of_awayAlgEquiv
import Submission.Work.MotA.coheight_eq_one_iff
import Submission.Work.MotA.resEquiv_iff_fractionRing

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero
open MotivicInvariants (GenByPseudoRegularizable)

/-- Node CERT: a `𝕜`-level certificate refutes the pseudo-regular generation of `Cr 𝕜 n`.

Route.  Apply `Work.MotA.not_gen_of_awayAlgEquiv 𝕜 n c.F c.G c.hF c.hG c.Φ c.z` (the base point
`z` is `c.z : Work.MotA.polySpec 𝕜 n`, where `polySpec 𝕜 n` carries the `Over (Spec 𝕜)`
instance `Work.MotA.instOverPolySpec`).  It remains to see
`divCount 𝕜 n c.F c.z ≠ divCount 𝕜 n c.G c.z`:
* `divCount 𝕜 n G z = Set.ncard {x | coheight x = 1 ∧ G ∈ x.asIdeal ∧ ResEquiv 𝕜 x z}`.  This set
  is contained in `{z}` — if `x` is in it then `ResEquiv 𝕜 x z`, so `x = z` by the contrapositive
  of `c.G_other x` — and contains `z` because `c.z_ht` and `c.z_mem` hold and `ResEquiv 𝕜 z z` is
  reflexive.  Hence the set is finite and `ncard = 1`.
* `divCount 𝕜 n F z = 0` because every element of the corresponding set has `ResEquiv 𝕜 x z`,
  contradicting `c.F_none x`.  Hence `ncard = 0`.
Consistency check (no contradiction): `c.F_none` at `x = z` forces `F ∉ z.asIdeal`. -/
theorem not_gen_of_certN {𝕜 : Type} [Field 𝕜] {n : ℕ} (c : CertN 𝕜 n) :
    ¬ GenByPseudoRegularizable 𝕜 n := by
  refine Work.MotA.not_gen_of_awayAlgEquiv 𝕜 n c.F c.G c.hF c.hG c.Φ
    (Z := Work.MotA.polySpec 𝕜 n) c.z ?_
  -- On the `F` side the relevant set of codimension-one points is empty.
  have hFset : {x : Work.MotA.polySpec 𝕜 n |
      Order.coheight x = 1 ∧ c.F ∈ x.asIdeal ∧ ResEquiv 𝕜 x c.z} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hx1, hxmem, hxres⟩
    exact c.F_none x hx1 hxmem hxres
  -- On the `G` side it is exactly the singleton `{c.z}`.
  have hGset : {x : Work.MotA.polySpec 𝕜 n |
      Order.coheight x = 1 ∧ c.G ∈ x.asIdeal ∧ ResEquiv 𝕜 x c.z} = {c.z} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx1, hxmem, hxres⟩
      by_contra hne
      exact c.G_other x hx1 hxmem hne hxres
    · rintro rfl
      exact ⟨c.z_ht, c.z_mem, ⟨RingEquiv.refl _, by simp⟩⟩
  simp only [Work.MotA.divCount]
  rw [hFset, hGset]
  simp

end Work.MotV
