import Mathlib
import Submission.Work.ShafarevichKoch.CohomologyAction

/-!
# `Work.ShafarevichKoch.conjKer_mem_cocycles1` -- conjugation preserves `1`-cocycles

For `π : G →* Q` with `N = ker π`, the group `G` acts on `N` by conjugation and hence on the
cohomology of `N` with coefficients in a `G`-module `A`.  The action of `g : G` on a `1`-cocycle
`f : N → A` is `n ↦ g · f (g⁻¹ n g)`.  This file shows that this is again a `1`-cocycle, which
is the group-theoretic heart of the conjugation action on `H¹(N, A)`, one of the two inputs of the
Hochschild--Serre five-term exact sequence used in the Shafarevich--Koch relation count.
-/

set_option linter.style.haveILetI false

namespace Work.ShafarevichKoch

theorem conjKer_mem_cocycles1 {k G Q : Type} [CommRing k] [Group G] [Group Q]
    (π : G →* Q) (A : Rep k G) (g : G)
    (f : ↥(groupCohomology.cocycles₁ (Rep.res (MonoidHom.ker π).subtype A))) :
    (fun n : MonoidHom.ker π => A.ρ g (f (Work.ShafarevichKoch.conjKer π g⁻¹ n)))
      ∈ groupCohomology.cocycles₁ (Rep.res (MonoidHom.ker π).subtype A) := by
  rw [groupCohomology.mem_cocycles₁_iff]
  intro n m
  -- the cocycle identity for `f` on the normal subgroup `ker π`
  have hf := (groupCohomology.mem_cocycles₁_iff (f : MonoidHom.ker π → A)).1 f.2
  -- `g⁻¹ (n m) g = (g⁻¹ n g) (g⁻¹ m g)`, so `f` satisfies its cocycle identity there
  have h1 : f (conjKer π g⁻¹ (n * m)) =
      A.ρ ((conjKer π g⁻¹ n : MonoidHom.ker π) : G) (f (conjKer π g⁻¹ m))
        + f (conjKer π g⁻¹ n) := by
    rw [conjKer_mul]
    exact hf _ _
  -- the group identity `g (g⁻¹ n g) = n g` making the two actions match
  have hg : g * ((conjKer π g⁻¹ n : MonoidHom.ker π) : G) = (n : G) * g := by
    simp [conjKer_coe]
    group
  rw [h1, map_add]
  congr 1
  calc A.ρ g (A.ρ ((conjKer π g⁻¹ n : MonoidHom.ker π) : G) (f (conjKer π g⁻¹ m)))
      = A.ρ (g * ((conjKer π g⁻¹ n : MonoidHom.ker π) : G))
          (f (conjKer π g⁻¹ m)) := by
        rw [map_mul, Module.End.mul_apply]
    _ = A.ρ ((n : G) * g) (f (conjKer π g⁻¹ m)) := by rw [hg]
    _ = A.ρ (n : G) (A.ρ g (f (conjKer π g⁻¹ m))) := by
        rw [map_mul, Module.End.mul_apply]

end Work.ShafarevichKoch
