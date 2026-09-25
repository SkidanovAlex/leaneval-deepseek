/-
Copyright: the martinet_totally_real_towers team.

# The transgression cocycle is independent of the section, up to a `2`-coboundary

Fix a group extension `1 → N → G → Q → 1` (`GroupExt G Q N`) with an injective structural map
`i : N →* G` whose range is the kernel of `q : G →* Q`, a discrete `Q`-module `M` whose `N`-action
is trivial and whose `Q`-action is the `G`-action transported along a section `s` of `q`
(`hcompQ : y • m = s y • m`), and a `G`-invariant `1`-cocycle `φ : N → M`, i.e.
`φ (conj g n) = g • φ n`.

For a section `s` of `q` the raw transgression is

  `tgFun E s hs φ (x, y) = φ (s x · s y · s (xy)⁻¹)`   (`x, y : Q`),

see `isCocycle2_tgFun`, where it is shown to be a `2`-cocycle.  Two sections differ by an
`N`-valued "defect"

  `a y = sectDefect E s s' hs hs' y`,   characterised by `i (a y) = s' y · s y⁻¹`,

i.e. `s' y = i (a y) · s y`.  Substituting this into the factor system of `s'` and using that
`conj (s y) (i (a z)) = i (s y · a z · s y⁻¹)` inside `G` gives the group identity

  `u_{s'} (y, z) = a y · conj (s y) (a z) · u_s (y, z) · (a (y z))⁻¹`   in `N`,

where `u_s = tgArg E s hs`.  Applying the additive `φ` (using `hinv` and `hcompQ` to move
`conj (s y)` and the action across) yields

  `tgFun E s' hs' φ (y, z) = tgFun E s hs φ (y, z) + d¹ (φ ∘ a) (y, z)`,

so that

  `tgFun E s hs φ - tgFun E s' hs' φ = d¹ (-(φ ∘ a))`   on `Q × Q`.

This is the well-definedness of the transgression `H¹(N,M)^G → H²(Q,M)` on the level of cocycles:
changing the section changes the transgression by a `2`-coboundary.
-/

import Mathlib
import Submission.Work.ConCohomology.Extension
import Submission.Work.ConCohomology.isCocycle2_tgFun

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

section SectDefect

variable {G Q N : Type*} [Group G] [Group Q] [Group N]

/-- The defect of a second section `s'` relative to a fixed section `s`, at a point `y : Q`: the
element `s' y · s y⁻¹` of `N = ker q`.  It satisfies `i (sectDefect E s s' hs hs' y) = s' y · s y⁻¹`,
i.e. `s' y = i (sectDefect E s s' hs hs' y) · s y`, so that `s'` is obtained from `s` by translating
by an `N`-valued function on `Q`. -/
noncomputable def sectDefect (E : GroupExt G Q N) (s s' : Q → G)
    (hs : ∀ y : Q, E.q (s y) = y) (hs' : ∀ y : Q, E.q (s' y) = y) (y : Q) : N :=
  E.kerLift (s' y * (s y)⁻¹) (by rw [map_mul, map_inv, hs', hs]; simp)

/-- The defining property of `sectDefect`: its image in `G` is the ratio of the two sections. -/
lemma i_sectDefect (E : GroupExt G Q N) (s s' : Q → G)
    (hs : ∀ y : Q, E.q (s y) = y) (hs' : ∀ y : Q, E.q (s' y) = y) (y : Q) :
    E.i (sectDefect E s s' hs hs' y) = s' y * (s y)⁻¹ := E.i_kerLift _ _

end SectDefect

/-- **Independence of the transgression cocycle of the choice of section.**  With the notation of
`isCocycle2_tgFun` (`N` acting trivially on `M`, the `Q`-action compatible with the `G`-action along
the section `s`, `φ` a `1`-cocycle for the trivial `N`-action and `G`-equivariant), the difference of
the transgression cocycles attached to two sections `s` and `s'` of `q` is a `2`-coboundary on `Q`:
there is `w : Q → M` with `tgFun E s hs φ - tgFun E s' hs' φ = d1Fun w`. -/
theorem tgFun_section_independence {G Q N : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [Group N]
    [TopologicalSpace N] [IsTopologicalGroup N] {M : Type*} [AddCommGroup M]
    [DistribMulAction G M] [DistribMulAction N M] [DistribMulAction Q M] (E : GroupExt G Q N)
    (hcompN : ∀ (n : N) (m : M), n • m = m) (s s' : Q → G)
    (hs : ∀ y : Q, E.q (s y) = y) (hs' : ∀ y : Q, E.q (s' y) = y)
    (hcompQ : ∀ (y : Q) (m : M), y • m = s y • m) (φ : N → M) (hφ : IsCocycle1 φ)
    (hinv : ∀ (g : G) (n : N), φ (E.conj g n) = g • φ n) :
    ∃ w : Q → M, tgFun E s hs φ - tgFun E s' hs' φ = d1Fun (G := Q) w := by
  -- Under the trivial `N`-action, the `1`-cocycle `φ` is an additive map `N → M`.
  have hφadd : ∀ a b : N, φ (a * b) = φ a + φ b := fun a b => by
    rw [hφ a b, hcompN a (φ b)]
  have hφ1 : φ 1 = 0 := by
    have h := hφadd 1 1
    rw [mul_one] at h
    exact (add_left_cancel (show φ 1 + 0 = φ 1 + φ 1 by rw [add_zero]; exact h)).symm
  have hφinv : ∀ a : N, φ a⁻¹ = -φ a := by
    intro a
    have h : φ a + φ a⁻¹ = 0 := by rw [← hφadd a a⁻¹, mul_inv_cancel, hφ1]
    exact eq_neg_of_add_eq_zero_right h
  have hφadd4 : ∀ a b c d : N, φ (a * b * c * d) = φ a + φ b + φ c + φ d := by
    intro a b c d
    rw [hφadd (a * b * c) d, hφadd (a * b) c, hφadd a b]
  -- The defect of `s'` relative to `s`, and the function whose coboundary we will exhibit.
  set A : Q → N := fun y => sectDefect E s s' hs hs' y with hA
  have hAi : ∀ y : Q, E.i (A y) = s' y * (s y)⁻¹ := fun y => i_sectDefect E s s' hs hs' y
  set W : Q → M := fun y => φ (A y) with hW
  -- The factor systems of the two sections differ by the expected product in `N`.
  have hkey : ∀ y z : Q, tgArg E s' hs' y z
      = A y * E.conj (s y) (A z) * tgArg E s hs y z * (A (y * z))⁻¹ := by
    intro y z
    apply E.injective_i
    simp only [i_tgArg, map_mul, map_inv, E.i_conj, hAi]
    group
  -- Consequently the two transgression cocycles differ by the coboundary of `W = φ ∘ A`.
  have htgArg : ∀ x y : Q, φ (tgArg E s hs x y) = tgFun E s hs φ (x, y) :=
    fun x y => (tgFun_eq_tgArg E s hs φ x y).symm
  have htg : ∀ y z : Q, tgFun E s' hs' φ (y, z)
      = tgFun E s hs φ (y, z) + d1Fun (G := Q) W (y, z) := by
    intro y z
    rw [tgFun_eq_tgArg, hkey y z, hφadd4, hφinv, hinv (s y) (A z), ← hcompQ y (φ (A z)),
      htgArg y z, d1Fun_apply]
    abel
  refine ⟨-W, ?_⟩
  funext p
  obtain ⟨y, z⟩ := p
  show tgFun E s hs φ (y, z) - tgFun E s' hs' φ (y, z)
      = d1Fun (G := Q) (-W) (y, z)
  rw [htg y z, d1Fun_neg]
  simp only [Pi.neg_apply]
  simp only [d1Fun_apply]
  abel

end Work.ConCohomology
