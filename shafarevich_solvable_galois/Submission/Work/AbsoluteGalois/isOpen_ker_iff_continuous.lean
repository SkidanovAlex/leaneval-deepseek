/-
# Open kernel vs. continuity for homomorphisms out of `G_ℚ`

A group homomorphism out of a topological group into a **discrete** group is continuous exactly
when its kernel is open (a coset of an open subgroup is open, and conversely `ker ψ` is the
preimage of the open singleton `{1}`).

The intended use is `G = Field.absoluteGaloisGroup ℚ`, which Mathlib equips with the Krull
topology (`Field.instIsTopologicalGroupAbsoluteGaloisGroup`), so that an open subgroup of `G_ℚ`
is precisely the kernel of a continuous homomorphism onto a finite discrete group.

## Main results

* `Work.AbsoluteGalois.isOpen_ker_iff_continuous_of_discrete` — the general statement for a
  topological group source and a discrete target;
* `Work.AbsoluteGalois.isOpen_ker_iff_continuous` — the specialisation to `G_ℚ`.
-/
import Mathlib
import Submission.Work.AbsoluteGalois.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteGalois

open Filter

/-- **A homomorphism from a topological group to a discrete group is continuous if and only if
its kernel is open.**

The forward direction is `ker ψ = ψ ⁻¹' {1}` with `{1}` open, and the converse follows from
continuity at `1`: a homomorphism out of a topological group is continuous as soon as it is
continuous at `1`, and `{1} ⊆ G` open means that `ψ ⁻¹' {1} = ker ψ ∈ 𝓝 1`. -/
theorem isOpen_ker_iff_continuous_of_discrete {G H : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [DiscreteTopology H] (ψ : G →* H) :
    IsOpen (ψ.ker : Set G) ↔ Continuous ψ := by
  constructor
  · intro hf
    apply continuous_of_continuousAt_one ψ
    rw [ContinuousAt, nhds_discrete H, map_one, Filter.tendsto_pure]
    exact hf.mem_nhds (map_one ψ)
  · intro h
    have h1 : (ψ.ker : Set G) = ψ ⁻¹' ({1} : Set H) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe, MonoidHom.mem_ker]
    rw [h1]
    exact h.isOpen_preimage {1} (isOpen_discrete {1})

/-- **Open kernel vs. continuity for the absolute Galois group of `ℚ`.**

`Field.absoluteGaloisGroup ℚ` carries the Krull topology, for which it is a topological group;
hence a homomorphism to a discrete group `G` is continuous if and only if its kernel is open. -/
theorem isOpen_ker_iff_continuous {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    (ψ : Field.absoluteGaloisGroup ℚ →* G) :
    IsOpen (ψ.ker : Set (Field.absoluteGaloisGroup ℚ)) ↔ Continuous ψ :=
  isOpen_ker_iff_continuous_of_discrete ψ

end Work.AbsoluteGalois
