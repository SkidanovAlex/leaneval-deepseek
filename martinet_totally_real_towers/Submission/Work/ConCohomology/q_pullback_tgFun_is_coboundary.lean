/-
Copyright: the martinet_totally_real_towers team.

# The pullback of the transgression along `q : G → Q` is a coboundary

Fix a group extension `1 → N → G → Q → 1` (`GroupExt G Q N`), a section `s : Q → G` of `q`, and a
function `φ : N → M`.  The raw transgression is

  `tgFun E s hs φ (x, y) = φ (s x · s y · s (xy)⁻¹)`   (`x, y : Q`),

see `isCocycle2_tgFun`, where it is shown to be a factor system on `Q` when `N` acts trivially on
`M`, `φ` is additive and `φ` is `G`-equivariant.

When the factor system is pulled back along `q : G → Q`, i.e. evaluated at `(q x, q y)` for
`x y : G`, it becomes a *coboundary*: the reason is that on `G` the section `s` can be corrected by
the "defect"

  `u x = x · s (q x)⁻¹ ∈ ker q = N`   (`liftArg`),

which satisfies `s (q x) = i (u x)⁻¹ · x`.  Substituting `s (q x) = i (u x)⁻¹ x` into the factor
system gives, inside `G`,

  `s (q x) s (q y) s (q x · q y)⁻¹ = i (u x⁻¹ · (conj x (u y))⁻¹ · u (x y))`,

and applying the additive `φ` (using `hinv` to move `conj x` across `φ`) yields exactly
`d¹ β (x, y)` for `β x = - φ (u x)`.

Equivalently: `tg ∘ (q × q) = d¹ (φ ∘ u)`, which is the statement that the transgression vanishes
on the image of `H¹(Q, M) → H²(Q,M)` restricted along `q`, `ker(inf₂) = im(tg)`.
-/

import Mathlib
import Submission.Work.ConCohomology.Extension
import Submission.Work.ConCohomology.isCocycle2_tgFun

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function Classical

section LiftArg

variable {G Q N : Type*} [Group G] [Group Q] [Group N]

/-- The defect of a section `s` of `q` at a point `x : G`: the element `x · s (q x)⁻¹` of
`N = ker q`.  It measures by how much `s (q x)` fails to be `x`, and satisfies
`s (q x) = i (liftArg E s hs x)⁻¹ · x`. -/
noncomputable def liftArg (E : GroupExt G Q N) (s : Q → G) (hs : ∀ y : Q, E.q (s y) = y)
    (x : G) : N :=
  E.kerLift (x * (s (E.q x))⁻¹) (by rw [map_mul, map_inv, hs]; simp)

/-- The defining property of `liftArg`: `i (liftArg E s hs x) = x * s (q x)⁻¹`. -/
lemma i_liftArg (E : GroupExt G Q N) (s : Q → G) (hs : ∀ y : Q, E.q (s y) = y) (x : G) :
    E.i (liftArg E s hs x) = x * (s (E.q x))⁻¹ := E.i_kerLift _ _

end LiftArg

/-- **The pullback of the raw transgression along `q` is a coboundary.**  With the notation of
`isCocycle2_tgFun` (`N` acting trivially on `M`, `φ` additive, `φ` `G`-equivariant), the function
`p ↦ tgFun E s hs φ (q p.1, q p.2)` on `G × G` is the coboundary of `β = - φ ∘ liftArg`. -/
theorem q_pullback_tgFun_is_coboundary {G Q N : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group Q] [TopologicalSpace Q] [Group N] [TopologicalSpace N]
    [IsTopologicalGroup N] {M : Type*} [AddCommGroup M] [DistribMulAction G M]
    [DistribMulAction N M] (E : GroupExt G Q N) (hcompN : ∀ (n : N) (m : M), n • m = m)
    (s : Q → G) (hs : ∀ y : Q, E.q (s y) = y) (φ : N → M) (hφ : IsCocycle1 φ)
    (hinv : ∀ (g : G) (n : N), φ (E.conj g n) = g • φ n) :
    ∃ β : G → M,
      (fun p : G × G => tgFun E s hs φ (E.q p.1, E.q p.2)) = d1Fun (G := G) β := by
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
  have hφadd3 : ∀ a b c : N, φ (a * b * c) = φ a + φ b + φ c := by
    intro a b c
    rw [hφadd (a * b) c, hφadd a b]
  -- The factor system of `s`, expressed through the defect `liftArg`.
  have hkey : ∀ x y : G, tgArg E s hs (E.q x) (E.q y)
      = (liftArg E s hs x)⁻¹ * (E.conj x (liftArg E s hs y))⁻¹ * liftArg E s hs (x * y) := by
    intro x y
    apply E.injective_i
    simp only [i_tgArg, map_mul, map_inv, E.i_conj, i_liftArg]
    group
  refine ⟨fun x => -φ (liftArg E s hs x), ?_⟩
  funext p
  obtain ⟨x, y⟩ := p
  show tgFun E s hs φ (E.q x, E.q y)
      = x • (-φ (liftArg E s hs y)) - (-φ (liftArg E s hs (x * y))) + (-φ (liftArg E s hs x))
  rw [tgFun_eq_tgArg, hkey x y, hφadd3, hφinv, hφinv, hinv x (liftArg E s hs y)]
  simp only [smul_neg]
  abel

end Work.ConCohomology
