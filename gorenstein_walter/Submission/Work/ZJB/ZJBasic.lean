import Submission.Work.ZJB.Defs

/-!
# ZJB — the `Z(J(P))` API needed for control of strong fusion

Glauberman's `(C_p)` (1968, p. 1116) is stated for the *characteristic functor*
`K(P) = Z(J(P))`; the properties of `K` that the argument uses are:

* `K(P) ≤ P` and `P ≤ N_G(K(P))` (characteristic in `P`), so that `S` is a Sylow `p`-subgroup of
  `N_G(K(S))` — `le_normalizer_ZJ`, `normalizer_le_normalizer_ZJ`;
* `K(P^g) = K(P)^g`, so that `K` may be transported along conjugacy — `ZJ_map_conj`;
* `K(P) ≠ 1` for `P ≠ 1` — `ZJ_ne_bot`.

The first two are proved here from GLUE's `Work.GW2.thompsonJ_map_conj` (covariance of `J(P)`)
and the library lemma `Subgroup.map_centralizer_inf_of_disjoint_ker`.
-/

namespace Work.ZJB

open Work.GW2
open Subgroup

variable {G : Type*} [Group G]

/-- Conjugation covariance of `Z(J(P))`: `Z(J(P^g)) = (Z(J(P)))^g`. -/
theorem ZJ_map_conj (P : Subgroup G) (g : G) :
    ZJ (P.map (MulAut.conj g : G →* G)) = (ZJ P).map (MulAut.conj g : G →* G) := by
  have hJ : Subgroup.thompsonJAbelian (P.map (MulAut.conj g : G →* G))
      = (Subgroup.thompsonJAbelian P).map (MulAut.conj g : G →* G) := by
    rw [← thompsonJ_eq_thompsonJAbelian, ← thompsonJ_eq_thompsonJAbelian]
    simpa using thompsonJ_map_conj P g
  have hker : Disjoint (Subgroup.thompsonJAbelian P) (MulAut.conj g : G →* G).ker := by
    rw [MonoidHom.ker_eq_bot _ (MulAut.conj g).injective]
    exact disjoint_bot_right
  have hinf := Subgroup.map_centralizer_inf_of_disjoint_ker
    (f := (MulAut.conj g : G →* G)) (J := Subgroup.thompsonJAbelian P) hker
  rw [ZJ_eq_thompsonJAbelian, ZJ_eq_thompsonJAbelian, hJ]
  exact hinf.symm

/-- `N_G(P) ≤ N_G(Z(J(P)))`. -/
theorem normalizer_le_normalizer_ZJ (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer (ZJ P : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hx ⊢
  calc (ZJ P).map (MulAut.conj x : G →* G)
      = ZJ (P.map (MulAut.conj x : G →* G)) := (ZJ_map_conj P x).symm
    _ = ZJ P := by rw [hx]

/-- `P ≤ N_G(Z(J(P)))`: `Z(J(P))` is characteristic in `P`. -/
theorem le_normalizer_ZJ (P : Subgroup G) :
    P ≤ normalizer (ZJ P : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_le_normalizer_ZJ P)

end Work.ZJB
