/-
Copyright (c) 2025. All rights reserved.

# Functoriality of `H¹` and `H²` (identity and composition)

`Submission/Work/AbsoluteKummer/Basic.lean` constructs `mapH1` and `mapH2` (the maps induced on
continuous cohomology by an equivariant additive map of discrete modules) and proves
`mapH1_H1π`, `mapH2_H2π`, `mapH1_id_H1π`, `mapH1_comp_H1π`.  This file adds the corresponding
statements for `H²`:

* `Work.AbsoluteKummer.mapH2_id_H2π` — the identity map of coefficients induces the identity;
* `Work.AbsoluteKummer.mapH2_comp_H2π` — `mapH2` is compatible with composition.
-/
import Submission.Work.AbsoluteKummer.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w

namespace Work.AbsoluteKummer

open scoped Classical Topology
open Filter

noncomputable section

variable {G : Type u} {M : Type v} [TopologicalSpace G] [Group G] [AddCommGroup M]
variable [DistribMulAction G M]

theorem mapH2_id_H2π (c : Z2 G M) :
    mapH2 (G := G) (M := M) (N := M) (AddMonoidHom.id M)
      (Work.GroupCohomology.isEquivariant_id (G := G) (A := M)) (H2π G M c) = H2π G M c := by
  rw [mapH2_H2π]
  exact congrArg (H2π G M) (Subtype.ext rfl)

variable {N : Type w} [AddCommGroup N] [DistribMulAction G N]

theorem mapH2_comp_H2π {P : Type u} [AddCommGroup P] [DistribMulAction G P]
    (φ : M →+ N) (ψ : N →+ P) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hψ : Work.GroupCohomology.IsEquivariant G ψ) (c : Z2 G M) :
    mapH2 (ψ.comp φ) (hψ.comp hφ) (H2π G M c) =
      mapH2 ψ hψ (mapH2 φ hφ (H2π G M c)) := by
  rw [mapH2_H2π, mapH2_H2π, mapH2_H2π]
  exact congrArg (H2π G P) (Subtype.ext rfl)

end

end Work.AbsoluteKummer
