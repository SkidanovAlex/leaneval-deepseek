/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Work.MotK
-/
import Submission.Work.MotK.KleinTwData
import Submission.Work.MotK.LinkData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The T-twist (and S-twist) link data of the quadro-cubic transformation

This is the interface used to build the affine certificate `Work.MotV.LinkCert`
(`MOTIVIC_S45_LEAD.md` §6, `GUIDE_LINK.md` §B).

In the *split* model (`LinkData.lean`) the link uses the shift-invariant quadric
`q = Σ_k p_k` and the hyperplane `H = {Σ_k z_k = 0}`: the map `f = P ∘ y` lands in `H` because
`Σ_k p_k(y(v)) = q(y(v)) = q(v)²q(p) = 0` when `q(p) = 0`.

For the **T-twist** the roles are the T-invariant ones: the quadric is `q = p_0` and the
hyperplane is `H = {z_0 = 0}` (both are fixed by the diagonal `μ₅`-action `z_k ↦ ζ^k z_k`).
Then `p_0(y(v)) = q(y(v)) = q(v)²q(p) = 0`, so `f` maps into `H`, and everything else is the same
construction with `p_0` in place of `Σ_k p_k`:

* `kleinTwQ a b h y = kleinTwP0 a b h y` — the T-invariant quadric in Kummer coordinates;
* `kleinTwBilin a b h u v` — its polar form `q(u+v) - q(u) - q(v)`;
* `kleinTwStereo a b h p v` — inverse stereographic projection `q(v)·p - b(p,v)·v`;
* `kleinTwFhom a b h p v = b(p,v)·kleinTwS(y(v))` (the source equation);
* `kleinTwGhom a b h p w = b(p,kleinTwR w)·kleinTwSDual(w)` (the target equation).

The two identities that make `f^*` an isomorphism of localisations are
`G_hom(f(v)) = -kleinTwS(y(v))²·b(p,v)·F_hom(v)` (`KleinTwLinkUnit`, the analogue of the proved
`KleinLinkUnit`) and the symmetric one involving the projection `π_p` and `y∘π_p = id` on `Q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace Work.MotK

variable {R : Type*} [CommRing R]

/-- The T-invariant quadric `q = p_0` in Kummer coordinates. -/
def kleinTwQ (a b h : R) (y : Fin 5 → R) : R := kleinTwP0 a b h y

/-- The polar form of the T-invariant quadric. -/
def kleinTwBilin (a b h : R) (u v : Fin 5 → R) : R :=
  kleinTwQ a b h (u + v) - kleinTwQ a b h u - kleinTwQ a b h v

/-- Inverse stereographic projection from `p ∈ {q = 0}` for the T-twisted quadric. -/
def kleinTwStereo (a b h : R) (p v : Fin 5 → R) : Fin 5 → R :=
  fun i => kleinTwQ a b h v * p i - kleinTwBilin a b h p v * v i

/-- The source equation of the T-twist link: `F_hom(v) = b(p,v)·s(y(v))`. -/
def kleinTwFhom (a b h : R) (p v : Fin 5 → R) : R :=
  kleinTwBilin a b h p v * kleinTwS a b h (kleinTwStereo a b h p v)

/-- The target equation of the T-twist link: `G_hom(w) = b(p,R w)·s'(w)`. -/
def kleinTwGhom (a b h : R) (p w : Fin 5 → R) : R :=
  kleinTwBilin a b h p (kleinTwR a b h w) * kleinTwSDual a b h w

end Work.MotK
