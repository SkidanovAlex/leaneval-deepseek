import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Chain17
import Submission.Work.ThmF.ChV12.Lemma5Defs
import Submission.Work.ThmF.ChV3.Prove.W_le_centralizer_X5
import Submission.Work.ThmF.ChV3.Prove.V_conj_X5
import Submission.Work.ThmF.ChV3.Prove.V_conj_Cst

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.W_V_on_L` — Peterfalvi II Ch. V §3, step (15b)

`W` centralises `X = ⟨Q₀, K, t⟩`, and `V = C_D(t)` normalises `L = X ∩ C_G(st)`.

* **First conjunct.**  `X5 H t = ⟨Q₀ ∪ Kset H t ∪ {t}⟩`, and `W = C_V(K)` centralises each
  generator: `Kset H t` by definition of `W`, `t` because `W ≤ centD H t ≤ C_G(t)`, and
  `Q₀ = Inv(H) ∪ {1}` because `W ≤ C_G(Q₀sub H)` — which is exactly Ch. II §4 Prop. 4
  (`hC4`), the only place a hypothesis beyond the definitions is used.  Packaged as
  `W_le_centralizer_X5`, this gives `W ≤ C_G(X5 H t)`.

* **Second conjunct.**  `Lsub H s t = X5 H t ⊓ Cst s t` is an intersection, and conjugation by
  `v ∈ V` preserves both factors:

  - `V_conj_X5`: `v` preserves `Q₀` (conjugation by an element of `H` permutes the involutions of
    `H`), preserves `Kset H t` (for `k ∈ D` with `t k t⁻¹ = k⁻¹` one has `t (v k v⁻¹) t⁻¹ =
    (v k v⁻¹)⁻¹`, using `t v = v t`), and fixes `t` — hence preserves
    `X5 H t = ⟨Q₀ ∪ Kset ∪ {t}⟩`;
  - `V_conj_Cst`: `V ≤ C_G(s)` (Peterfalvi II Ch. V §2 Lemma 3 a), *i.e.* the uniqueness clause
    of the structure identity `ChV12.structureIdentity`: conjugating `t s t = r⁻¹ t r` by
    `v ∈ V` gives a second solution `(v s v⁻¹, v r v⁻¹)`, so `v s v⁻¹ = s`) and `V ≤ C_G(t)` by
    definition, hence `V ≤ C_G(st) = Cst s t` and conjugation by `v` preserves `Cst s t`.

  Since conjugation by `v` is injective, `Subgroup.map_inf` distributes it over the
  intersection, and the two factor-wise statements assemble to
  `cj v (Lsub H s t) = Lsub H s t`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThmF.ChV3.Prove

open Work.ThmF

theorem W_V_on_L {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hC4 : Submission.Blueprint.ChIIFourProp) (c : Work.ThmF.ChV3.CtxF H Q t s r P) :
    (∀ w ∈ Work.ThmF.W H t, ∀ x ∈ Work.ThmF.Lemma5.X5 H t, w * x = x * w) ∧
      (∀ v ∈ Submission.Blueprint.centD H t,
        Work.ThmF.ChV3.cj v (Work.ThmF.ChV3.Lsub H s t) = Work.ThmF.ChV3.Lsub H s t) := by
  constructor
  · -- `W ≤ C_G(X5 H t)`: Ch. II §4 Prop. 4 `W = C_V(K) = D ⊓ C_G(Inv H)` plus the definitions.
    intro w hw x hx
    exact (Subgroup.mem_centralizer_iff.mp
      (W_le_centralizer_X5 hC4 c.sit c.split hw) x hx).symm
  · -- `V` normalises both factors `X5 H t` and `Cst s t = C_G(st)` of `L = X5 ∩ C_G(st)`.
    intro v hv
    have hX5 : Work.ThmF.ChV3.cj v (Work.ThmF.Lemma5.X5 H t) = Work.ThmF.Lemma5.X5 H t :=
      V_conj_X5 c.split v hv
    have hCst : Work.ThmF.ChV3.cj v (Work.ThmF.ChV3.Cst s t) = Work.ThmF.ChV3.Cst s t :=
      V_conj_Cst c.split c.s_mem c.s_inv c.r_mem c.sid v hv
    change Work.ThmF.ChV3.cj v (Work.ThmF.Lemma5.X5 H t ⊓ Work.ThmF.ChV3.Cst s t) =
      (Work.ThmF.Lemma5.X5 H t ⊓ Work.ThmF.ChV3.Cst s t)
    have hmap : Work.ThmF.ChV3.cj v (Work.ThmF.Lemma5.X5 H t ⊓ Work.ThmF.ChV3.Cst s t) =
        Work.ThmF.ChV3.cj v (Work.ThmF.Lemma5.X5 H t) ⊓
          Work.ThmF.ChV3.cj v (Work.ThmF.ChV3.Cst s t) :=
      Subgroup.map_inf _ _ _ (MulAut.conj v).injective
    rw [hmap, hX5, hCst]

end Work.ThmF.ChV3.Prove
