/-
Copyright: the martinet_totally_real_towers team.

# Short exact sequences of coefficient modules

This module packages a short exact sequence `0 → A → B → C → 0` of `G`-modules (`CoeffSES`),
together with the auxiliary choices needed to write down the connecting homomorphisms of the
long exact sequence: a set-theoretic inverse `invFun` of `f` on the image of `f`, a set-theoretic
section `sect` of `g`, and the two *raw* connecting cochains `delta0Fun` (degree `0 → 1`) and
`delta1Fun` (degree `1 → 2`).

The results proved about these objects live in other modules of the chapter; here we only fix the
conventions.
-/

import Submission.Work.ConCohomology.Basic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.ConCohomology

open Function
open Classical

/-- A short exact sequence `0 → A → B → C → 0` of `G`-modules, all maps being `G`-equivariant. -/
structure CoeffSES (G : Type*) [Group G] (A : Type*) (B : Type*) (C : Type*) [AddCommGroup A]
    [AddCommGroup B] [AddCommGroup C] [DistribMulAction G A] [DistribMulAction G B]
    [DistribMulAction G C] where
  /-- The inclusion `A → B`. -/
  f : EqHom G A B
  /-- The projection `B → C`. -/
  g : EqHom G B C
  injective_f : Injective f
  surjective_g : Surjective g
  exact : ∀ b : B, g b = 0 ↔ ∃ a : A, f a = b

namespace CoeffSES

variable {G : Type*} [Group G]
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]

/-- A total function `B → A` which is a set-theoretic inverse of `f` on the image of `f`
(and `0` elsewhere). -/
noncomputable def invFun (S : CoeffSES G A B C) (b : B) : A :=
  if h : ∃ a : A, S.f a = b then Classical.choose h else 0

/-- A set-theoretic section of the projection `g`. -/
noncomputable def sect (S : CoeffSES G A B C) (c : C) : B :=
  Classical.choose (S.surjective_g c)

lemma g_sect (S : CoeffSES G A B C) (c : C) : S.g (S.sect c) = c :=
  Classical.choose_spec (S.surjective_g c)

/-- The raw degree `0 → 1` connecting cochain attached to an invariant element of `C`. -/
noncomputable def delta0Fun (S : CoeffSES G A B C) (c : C) : G → A :=
  fun σ => S.invFun (σ • S.sect c - S.sect c)

/-- The raw degree `1 → 2` connecting cochain attached to a cochain `c : G → C`. -/
noncomputable def delta1Fun (S : CoeffSES G A B C) (c : G → C) : G × G → A :=
  fun p => S.invFun (p.1 • S.sect (c p.2) - S.sect (c (p.1 * p.2)) + S.sect (c p.1))

variable (S : CoeffSES G A B C)

@[simp] lemma invFun_eq (b : B) :
    S.invFun b = if h : ∃ a : A, S.f a = b then Classical.choose h else 0 := rfl

@[simp] lemma delta0Fun_apply (c : C) (σ : G) :
    S.delta0Fun c σ = S.invFun (σ • S.sect c - S.sect c) := rfl

@[simp] lemma delta1Fun_apply (c : G → C) (σ τ : G) :
    S.delta1Fun c (σ, τ) =
      S.invFun (σ • S.sect (c τ) - S.sect (c (σ * τ)) + S.sect (c σ)) := rfl

end CoeffSES

end Work.ConCohomology
