import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.centD_ne_bot

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.PSU3.StageA.centD_le_W_of_PSU3Hyp` — status of the node `V ≤ W`

Peterfalvi II, Ch. II §4 / Ch. V §2 use `V = C_D(t)` and `W = C_V(J(D,t)) = C_V(K)` (pp. 236, 242);
`W ≤ V` is definitional, so `centD H t ≤ W H t` is *exactly* `V = W`, i.e. "`D = K·V` is abelian"
(`K = J(D,t) = Kset H t`).

## What is established here, hole-free

* `centD_le_W_of_normal` — **`V ⊴ D` implies `V ≤ W`.**  This is the reduction used by both
  `Work.PSU3.StageA.not_caseB` (`false_of_centD_normal`) and
  `Work.PSU3.StageA.chVI_caseWbot` (`false_of_centD_le_W`): with `D = twoPoint H t ≤ N_G(V)`,
  every `k ∈ Kset H t` normalises `V`, and the `t`-calculus (`t k t = k⁻¹`, `t v t = v`,
  `|D|` odd) gives `k v = v k` for `v ∈ V`; `centD H t ⊆ W H t` follows by definition of `W`.
* `centD_eq_W_of_le` — with `W ≤ V` definitional, `V ≤ W` forces `V = W`.
* `centD_le_W_of_PSU3Hyp_of_normal` — under `PSU3Hyp` the sibling node
  `twoPoint H t ≤ N_G(centD H t)` (`Work.PSU3.StageA.centD_normal_of_PSU3Hyp`, still a `hole` in
  `not_caseB.lean`) gives the requested statement.

## Why the requested statement is not a delegable structural fact

`V ≤ W` is equivalent to `D ≤ N_G(V)` (the sibling node), and it is *not* a consequence of
`ChIIFourProp` — which is true for every group in the situation `(B0)–(B2)`, simple or not.
Concretely, Ch. VI §1 Prop. (Peterfalvi II p. 259) is a statement about that same situation and its
**case b)** has `W = 1` while (B3) gives `V ≠ 1`; so with `IsSimpleGroup G` dropped the conclusion
of this file's target fails.  Its truth for *simple* `G` is exactly Suzuki's Lemma 60 as corrected
by Kantor–Seitz (§§14–15) and reproved by Peterfalvi in Ch. VII §4 (`V ≠ W ⟹ O^{2'}(G) ≠ G`),
whose formalisation is the missing content of
`Submission.Work.PSU3.StageB.exists_omega_of_not_fpf` (pp. 278–280), *together with* the
elimination of Ch. VI §1 cases a), b) by simplicity
(`Work.PSU3.StageA.not_caseA` / `not_caseB`, Ch. VI §2 (1)–(7) and §3).

Moreover the statement is **stronger than what its two users need**, so no proof of it is on their
critical path.  `chVI_caseWbot` and `not_caseB` invoke it only under `W H t = ⊥`, where it says
`V ≤ ⊥` — i.e. exactly "`W = ⊥` is impossible"; the generality `V = W` in the remaining case is the
part that needs §4.  The source's own exclusion of cases a), b) (Ch. VI §2 (1)–(7), §3) uses
`K = J(D,t) ⊴ D` (Ch. V §1 Prop. 2, via App. X/Feit–Thompson, or
`Work.PSU3.StageA.Ksub_eq_Kset_of_W_ne_bot` when `W ≠ ⊥`) together with the case data — not
`V ≤ W`.  Likewise the case-a) argument uses `V ≤ N_G(K)`, which is automatic from `K ⊴ D`, and
`V ≤ N_G(Q₀)`, `V ≤ C_G(t)`; it does not need `V ⊴ D`.

Positive evidence that the *conclusion* is right for the groups the area is about: in the
PSU(3,2ⁿ) model the torus `T̄ = twoPoint B̄ w̄` is the image of the abelian (indeed cyclic) group
`(GF(2^{2n}))ˣ` — it consists of the diagonal matrices `diag(a, a^{q-1}, a^{-q})` — so
`centD B̄ w̄ ≤ W B̄ w̄` there (`centD_le_W_psu3Model` proved in the sibling file
`Submission/Work/PSU3/StageA/centD_le_W_psu3Model.lean` (kept in its own module because the model
files are heavy).  For a *general* simple Bender group the same abelianness of the torus is
available as the `hTab` field of `Work.Models.ModelData` (via `Work.Models.modelDataBorel`), which
is the tool with which the `W ≠ ⊥` case of `V ≤ W` becomes accessible — the missing pieces there
being that `V` itself is abelian (`V ≤ C_G(W)`, which needs the Ch. VI case analysis) and the
transport of the model's torus to `F ⊓ D` for `F = O^{2'}(C_G(W))` (`ChIIFourProp` P3 with `X = W`).
-/

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- **`V ⊴ D` forces `V ≤ W`.**  If `D = twoPoint H t` normalises `V = centD H t` (equivalently
`V` is normal in `D`), then every `k ∈ Kset H t` centralises `V`; hence
`centD H t ≤ W H t = V ⊓ C_G(Kset H t)`.

Only group theory is used: `t` is an involution, `|D|` is odd, an element of `Kset H t` lies in
`D` and is inverted by `t`, and `V` centralises `t`. -/
theorem centD_le_W_of_normal {G : Type} [Group G] {H : Subgroup G} {t : G} (ht2 : t * t = 1)
    (hDodd : Odd (Nat.card (twoPoint H t)))
    (hN : twoPoint H t ≤ Subgroup.normalizer (centD H t : Set G)) :
    centD H t ≤ Work.ThmF.W H t := by
  intro v hv
  rw [Work.ThmF.W, Subgroup.mem_inf]
  refine ⟨hv, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hkD : k ∈ twoPoint H t := Work.ThmF.Kset_subset H t hk
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hkt : t * k * t = k⁻¹ := by
    have h := (Work.ThmF.mem_Kset_iff.mp hk).2
    rwa [hti] at h
  -- `k v k⁻¹` again lies in `V`, hence centralises `t`
  have hkvk : k * v * k⁻¹ ∈ centD H t :=
    (Subgroup.mem_normalizer_iff.mp (hN hkD) v).mp hv
  have hct : k * v * k⁻¹ ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hkvk).2
  have hvt : v ∈ Subgroup.centralizer ({t} : Set G) := (Subgroup.mem_inf.mp hv).2
  have h1 : t * (k * v * k⁻¹) = (k * v * k⁻¹) * t :=
    Subgroup.mem_centralizer_iff.mp hct t (Set.mem_singleton t)
  have h2 : t * (k * v * k⁻¹) * t = k * v * k⁻¹ := by rw [h1, mul_assoc, ht2, mul_one]
  have h3 : t * v = v * t := Subgroup.mem_centralizer_iff.mp hvt t (Set.mem_singleton t)
  have h4 : t * v * t = v := by rw [h3, mul_assoc, ht2, mul_one]
  -- conjugation by `t` intertwines inversion on `k` with the identity on `v`
  have hφ1 : (MulAut.conj t) k = k⁻¹ := by rw [MulAut.conj_apply, hti]; exact hkt
  have hφ2 : (MulAut.conj t) k⁻¹ = k := by rw [map_inv, hφ1, inv_inv]
  have hφ3 : (MulAut.conj t) v = v := by rw [MulAut.conj_apply, hti]; exact h4
  have hφ4 : (MulAut.conj t) (k * v * k⁻¹) = k * v * k⁻¹ := by
    rw [MulAut.conj_apply, hti]; exact h2
  have hkey : k⁻¹ * v * k = k * v * k⁻¹ := by
    rw [← hφ4, map_mul, map_mul, hφ1, hφ3, hφ2]
  have hsquares : v * k ^ 2 = k ^ 2 * v := by
    have h9 : v * k = k ^ 2 * v * k⁻¹ := by
      calc v * k = k * (k⁻¹ * v * k) := by group
        _ = k * (k * v * k⁻¹) := by rw [hkey]
        _ = k ^ 2 * v * k⁻¹ := by rw [pow_two]; group
    calc v * k ^ 2 = v * k * k := by rw [pow_two, mul_assoc]
      _ = (k ^ 2 * v * k⁻¹) * k := by rw [h9]
      _ = k ^ 2 * v := by group
  -- `k` has odd order, hence is a power of `k ^ 2`
  have hkodd : Odd (orderOf k) :=
    Odd.of_dvd_nat hDodd (Subgroup.orderOf_dvd_natCard (twoPoint H t) hkD)
  obtain ⟨m, hm⟩ := hkodd
  have hkpow : k = (k ^ 2) ^ (m + 1) := by
    have h10 : k ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one k
    have h11 : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
    have h12 : k ^ (2 * (m + 1)) = k := by rw [h11, pow_add, h10, one_mul, pow_one]
    exact h12.symm.trans (pow_mul k 2 (m + 1))
  have hcomm2 : ∀ n : ℕ, (k ^ 2) ^ n * v = v * (k ^ 2) ^ n :=
    fun n => (Commute.pow_right hsquares n).symm
  rw [hkpow]
  exact hcomm2 (m + 1)

/-- `W ≤ V` is definitional (`W H t = centD H t ⊓ C_G(Kset H t)`), so `V ≤ W` means `V = W`. -/
theorem centD_eq_W_of_le {G : Type} [Group G] {H : Subgroup G} {t : G}
    (h : centD H t ≤ Work.ThmF.W H t) :
    centD H t = Work.ThmF.W H t :=
  le_antisymm h (Work.ThmF.W_le_centD H t)

/-- **The requested statement follows from its sibling node** `D ≤ N_G(V)`: this is the formalised
content of `Work.PSU3.StageA.not_caseB`'s `false_of_centD_normal` /
`Work.PSU3.StageA.chVI_caseWbot`'s `false_of_centD_le_W`, i.e. the two nodes
`centD_le_W_of_PSU3Hyp` and `centD_normal_of_PSU3Hyp` are the same statement. -/
theorem centD_le_W_of_PSU3Hyp_of_normal {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (_hC4 : Submission.Blueprint.ChIIFourProp)
    (hN : twoPoint H t ≤ Subgroup.normalizer (centD H t : Set G)) :
    centD H t ≤ Work.ThmF.W H t :=
  centD_le_W_of_normal (Work.RankOneUniqueness.mul_self_eq_one hS.split)
    (hS.split.stronglyEmbedded.2.2 t hS.split.not_mem) hN

-- Superseded (2026): the hole-carrying `centD_le_W_of_PSU3Hyp` was removed by the hole sweep;
-- its proved replacement is `Work.PSU3.StageA.centD_le_W_of_PSU3Hyp_closed` (in
-- `StageA/centD_le_W_of_PSU3Hyp_closed.lean`), which adds `HigmanProp` and `FeitThompsonProp`.

end Work.PSU3.StageA
