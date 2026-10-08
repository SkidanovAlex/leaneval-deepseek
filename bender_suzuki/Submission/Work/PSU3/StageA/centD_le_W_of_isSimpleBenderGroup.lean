import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.modelDataBorel
import Submission.Work.Hall.SchurZassenhaus.hall_schurZassenhaus_conj
import Submission.Work.Models.Abstract.twoPoint_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.centD_le_W_of_isSimpleBenderGroup`

The requested statement:

  `IsSimpleBenderGroup G → PSU3Hyp H Q t → centD H t ≤ W H t`.

With `D = twoPoint H t = H ⊓ H^t`, `V = centD H t = C_D(t)`, `K = Kset H t = J(D,t)` and
`W = C_V(K)`, this is the rank-one theorem `V = W` of Peterfalvi II Ch. V–VII.  Under the
hypothesis `IsSimpleBenderGroup G` (i.e. `G` is one of the three families
`PSL(2,2ⁿ)`, `Sz(2^{2n+1})`, `PSU(3,2ⁿ)`) the statement has an elementary proof, which is what
this file records:

* `Work.PSU3.StageA.modelDataBorel` attaches to the strongly embedded subgroup `H` a
  `Work.Models.ModelData P` with `P.B = H`.  `ModelData` carries the one structural fact that
  matters here, `P.hTab` : **the torus `T` is abelian**, and `ModelData.B` is a `BenderPair`
  (Borel subgroup of a Bender group).
* For such a pair and `t ∉ P.B`, the Bruhat decomposition `G = B ∪ BwB` shows that the
  two-point stabiliser `D = B ⊓ B^t` is a `B`-conjugate of the torus (`twoPoint_eq`,
  `inf_conj_w`): `D = conj b T` with `b ∈ B`.  Hence **`D` is abelian**
  (`mul_comm_of_mem_twoPoint`).
* Finally `V ≤ D` and `K = J(D,t) ⊆ D`, so `V` and `K` lie in the abelian group `D` and
  therefore commute: `V ≤ C_G(K)`, i.e. `V ≤ V ⊓ C_G(K) = W`.

Nothing else is used: in particular neither `ChIIFourProp`, nor `FeitThompsonProp`, nor the
Kantor–Seitz black box, nor simplicity or `V ≠ 1`, enters this route (the latter two only serve
to locate the case in the source).  The essential input is the abelianness of the torus, which
is a *model* fact (`ModelData.hTab`), unavailable from `PSU3Hyp` alone — this is exactly why the
sibling node `centD_le_W_of_PSU3Hyp` (whose hypothesis list does not mention
`IsSimpleBenderGroup`) is the deep node of the area, while the present statement, with the
classification hypothesis in hand, is elementary.
-/

set_option autoImplicit false

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- **Conjugates of abelian subgroups are abelian.**  If `T` is abelian and `b : G`, then
`conj b T = b T b⁻¹` is abelian: `x, y ∈ b T b⁻¹` means `b⁻¹ x b, b⁻¹ y b ∈ T`, which commute. -/
theorem mul_comm_of_mem_conj {G : Type} [Group G] {T : Subgroup G} {b : G}
    (hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) {x y : G}
    (hx : x ∈ Submission.Blueprint.conj b T) (hy : y ∈ Submission.Blueprint.conj b T) :
    x * y = y * x := by
  have hx' : b⁻¹ * x * b ∈ T := Work.Models.mem_conj_iff.mp hx
  have hy' : b⁻¹ * y * b ∈ T := Work.Models.mem_conj_iff.mp hy
  have h := hTab _ hx' _ hy'
  calc x * y = b * ((b⁻¹ * x * b) * (b⁻¹ * y * b)) * b⁻¹ := by group
    _ = b * ((b⁻¹ * y * b) * (b⁻¹ * x * b)) * b⁻¹ := by rw [h]
    _ = y * x := by group

/-- **The two-point stabiliser `D = B ⊓ B^t` of a Bender pair is abelian**, for `t ∉ B`.

By the Bruhat decomposition (`Work.Models.Abstract.twoPoint_eq`) `D` is a `B`-conjugate of the
torus `T`, and the torus is abelian (`P.hTab`). -/
theorem mul_comm_of_mem_twoPoint {G : Type} [Group G] [Finite G] (P : Work.Models.ModelData G)
    {t : G} (ht : t ∉ P.B) {x y : G} (hx : x ∈ Submission.Blueprint.twoPoint P.B t)
    (hy : y ∈ Submission.Blueprint.twoPoint P.B t) : x * y = y * x := by
  obtain ⟨b, _hb, _c, _hc, _hbc, hD⟩ := Work.Models.Abstract.twoPoint_eq P.toBenderPair ht
  rw [hD] at hx hy
  exact mul_comm_of_mem_conj P.hTab hx hy

theorem centD_le_W_of_isSimpleBenderGroup {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (hY : LeanEval.GroupTheory.Defs.IsSimpleBenderGroup G)
    (hS : Work.PSU3.PSU3Hyp H Q t) :
    Submission.Blueprint.centD H t ≤ Work.ThmF.W H t := by
  -- Attach model data to the strongly embedded subgroup `H`: `P.B = H` and the torus is abelian.
  obtain ⟨P, hPB⟩ := modelDataBorel hY hS.split.stronglyEmbedded
  have htB : t ∉ P.B := by rw [hPB]; exact hS.split.not_mem
  intro v hv
  rw [Work.ThmF.le_W_iff]
  refine ⟨hv, ?_⟩
  intro k hk
  -- `V ≤ D` and `K = J(D,t) ⊆ D`.
  have hvD : v ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hv).1
  have hkD : k ∈ Submission.Blueprint.twoPoint H t := Work.ThmF.Kset_subset H t hk
  -- Both lie in the abelian group `D = twoPoint P.B t`.
  have hv' : v ∈ Submission.Blueprint.twoPoint P.B t := by rw [hPB]; exact hvD
  have hk' : k ∈ Submission.Blueprint.twoPoint P.B t := by rw [hPB]; exact hkD
  exact mul_comm_of_mem_twoPoint P htB hk' hv'

end Work.PSU3.StageA
