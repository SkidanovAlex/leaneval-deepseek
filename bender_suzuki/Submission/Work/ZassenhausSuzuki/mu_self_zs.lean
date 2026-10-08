import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsDefs
import Submission.Work.ZassenhausSuzuki.hG_tilde_eq
import Submission.Work.ZassenhausSuzuki.mu_conj_mul_inv_zs
import Submission.Work.ZassenhausSuzuki.f_tilde_zs
import Submission.Work.ZassenhausSuzuki.hG_conj_gG_eq_tilde

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.mu_self_zs` — BG 3.1 (k)

`μ_x(x) = (∼(x⁻¹))⁻¹` for `x ∈ Q#`, where `μ_x(y) = g(h(x)·y·h(x)⁻¹)` (`muPt`,
the point action of the Moufang involution `t·h(x)`) and `∼` is the Suzuki reflection
`∼x = g((g x)⁻¹)` (`tildeOf`).

The whole identity is a consequence of the canonical relations H1 (`(g x)⁻¹ = f x⁻¹`),
H2 (`f(f x) = x`) and the `g∘f` formula `canon_gf` (`g(f y) = h(y)⁻¹·g(y)⁻¹·h(y)`)
applied at `y = x` and at `y = ∼x`, together with `f(∼x) = h(x)·x·h(x)⁻¹`
(`f_tilde_zs`), `g(∼x) = (g x)⁻¹` (`g_g`), `h(∼x) = h(x)` (`hG_tilde_eq`) and
`∼(x⁻¹) = g(f x)` (H1 at `x⁻¹`).  Concretely

`μ_x(x) = g(f(∼x)) = h(∼x)⁻¹·g(∼x)⁻¹·h(∼x) = (h x)⁻¹·(g x)·(h x)`

and

`(∼(x⁻¹))⁻¹ = (g(f x))⁻¹ = ((h x)⁻¹·(g x)⁻¹·(h x))⁻¹ = (h x)⁻¹·(g x)·(h x)`. ∎
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

theorem mu_self_zs {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {x : Q} (hx : (x : G) ≠ 1) :
    Work.ZassenhausSuzuki.TitsDesign.muPt hsplit C x x
      = (Work.ZassenhausSuzuki.tildeOf C x⁻¹)⁻¹ := by
  classical
  -- non-triviality of the various coordinates
  have hgx : ((C.g x : Q) : G) ≠ 1 := canon_g_ne_one hsplit hzass h2 C hx
  have hgxi : ((((C.g x)⁻¹ : Q)) : G) ≠ 1 := canon_inv_ne_one hgx
  have hxinv : ((x⁻¹ : Q) : G) ≠ 1 := canon_inv_ne_one hx
  -- `∼x = g ((g x)⁻¹)`
  have htildex : (tildeOf C x : Q) = C.g ((C.g x)⁻¹) := by
    rw [tildeOf]
    simp only [hx, ↓reduceIte]
  have htilde_ne : ((tildeOf C x : Q) : G) ≠ 1 := by
    rw [htildex]
    exact canon_g_ne_one hsplit hzass h2 C hgxi
  -- `f(∼x) = h(x) · x · h(x)⁻¹`, i.e. `f(∼x) = conjH x x`
  have hftil : C.f (tildeOf C x) = TitsDesign.conjH hsplit C x x := by
    apply Subtype.ext
    rw [f_tilde_zs hsplit hzass h2 C hx]
    rfl
  -- `g(∼x) = (g x)⁻¹` and `h(∼x) = h(x)` (as elements of `G`)
  have hgtil : ((C.g (tildeOf C x) : Q) : G) = (((C.g x)⁻¹ : Q) : G) := by
    have hq : C.g (tildeOf C x) = (C.g x)⁻¹ := by
      rw [htildex]
      exact canon_g_g hsplit hzass h2 C hgxi
    exact congrArg (fun z : Q => (z : G)) hq
  have hhtil : ((C.h (tildeOf C x) : twoPoint H t) : G)
      = ((C.h x : twoPoint H t) : G) := hG_tilde_eq hsplit hzass h2 C hx
  -- the value of `μ_x(x) = g(f(∼x))`
  have hL : ((C.g (C.f (tildeOf C x)) : Q) : G)
      = ((C.h x : twoPoint H t) : G)⁻¹ * ((C.g x : Q) : G)
        * ((C.h x : twoPoint H t) : G) := by
    rw [canon_gf hsplit C (tildeOf C x) htilde_ne]
    rw [hhtil, hgtil]
    simp only [Subgroup.coe_inv]
    group
  -- `∼(x⁻¹) = g(f x)` (H1 at `x⁻¹`)
  have htildexi : (tildeOf C x⁻¹ : Q) = C.g (C.f x) := by
    rw [tildeOf]
    simp only [hxinv, ↓reduceIte]
    congr 1
    simpa using canon_H1 hsplit C x⁻¹ hxinv
  -- the value of `(∼(x⁻¹))⁻¹`
  have hR : (((tildeOf C x⁻¹)⁻¹ : Q) : G)
      = ((C.h x : twoPoint H t) : G)⁻¹ * ((C.g x : Q) : G)
        * ((C.h x : twoPoint H t) : G) := by
    rw [htildexi]
    simp only [Subgroup.coe_inv]
    rw [canon_gf hsplit C x hx]
    group
  change C.g (TitsDesign.conjH hsplit C x x) = (tildeOf C x⁻¹)⁻¹
  rw [← hftil]
  exact Subtype.ext (hL.trans hR.symm)

end Work.ZassenhausSuzuki
