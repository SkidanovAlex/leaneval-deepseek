import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Case2CountSetup

namespace Work.CORE4

open Subgroup

/-- **`M = E(M)·C_M(t)` when `E(M)` has one class of involutions** (Bender 1981, §4, p. 224).

Let `E = E(M) = layerIn M` be the layer of `M` (the join of the normal quasisimple subgroups of
`M`, transported to `G`), let `t ∈ E` be an involution with one class of `E`-conjugates among the
involutions of `E`.  Then every `g ∈ M` satisfies `g ∈ E · C_M(t)`.

* `E ⊴ M`: `layerIn M` is the image of `layer M = sSup {E ≤ M | E.Normal ∧ IsQuasisimple E}`
  under `M.subtype`, and a `sSup` of normal subgroups is normal (`layerIn_le`,
  `layerIn_le_normalizer`, both already proved in `Submission.Work.CORE4.CountSetup`).
* Hence for `g ∈ M` the conjugate `g t g⁻¹` lies in `E`, and it is an involution
  (`orderOf` is conjugation invariant).
* The one-class hypothesis produces `d ∈ E` with `d t d⁻¹ = g t g⁻¹`.  Then `d g` centralizes `t`,
  i.e. `d g ∈ M ⊓ C_G(t) = M ⊓ B.H`, and `g = d⁻¹ · (d g)` with `d⁻¹ ∈ E`.

The reverse inclusion is `E ≤ M`. -/
theorem M_eq_layerIn_sup_of_oneInvClass {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (M : Subgroup G)
    (hone : Work.GW2.OneInvClassIn (Work.GW2.layerIn M)) (ht : B.t ∈ Work.GW2.layerIn M) :
    M = Work.GW2.layerIn M ⊔ (M ⊓ B.H) := by
  set E : Subgroup G := Work.GW2.layerIn M with hE
  -- `E ≤ M` and `M` normalizes `E`
  have hEM : E ≤ M := by rw [hE]; exact layerIn_le M
  have hnorm : M ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE]; exact layerIn_le_normalizer M
  have htE : B.t ∈ E := by rw [hE]; exact ht
  refine le_antisymm ?_ (sup_le hEM inf_le_left)
  intro g hg
  -- the `M`-conjugate of `t` still lies in `E`
  have hconj : g * B.t * g⁻¹ ∈ E :=
    Subgroup.le_normalizer_iff.mp hnorm g hg B.t htE
  -- and it is an involution
  have horder : orderOf (g * B.t * g⁻¹) = 2 := by
    have hconj_eq : g * B.t * g⁻¹ = (MulAut.conj g) B.t := by simp [MulAut.conj_apply]
    rw [hconj_eq, ← B.t_order, orderOf_eq_orderOf_iff]
    intro n
    rw [← map_pow]
    exact (MulAut.conj g).map_eq_one_iff
  -- one class of involutions in `E` conjugates it back to `t`
  obtain ⟨d, hd, hconjd⟩ := hone (g * B.t * g⁻¹) ⟨hconj, horder⟩ B.t ⟨htE, B.t_order⟩
  have hdM : d ∈ M := hEM hd
  -- `d * g` centralizes `t`
  have hcen : d * g ∈ B.H := by
    show d * g ∈ Subgroup.centralizer ({B.t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hX : (d * g) * B.t * (d * g)⁻¹ = B.t := by
      rw [show (d * g) * B.t * (d * g)⁻¹ = d * (g * B.t * g⁻¹) * d⁻¹ by group]
      exact hconjd
    calc (d * g) * B.t = ((d * g) * B.t * (d * g)⁻¹) * (d * g) := by group
      _ = B.t * (d * g) := by rw [hX]
  have hmem : d * g ∈ M ⊓ B.H := ⟨M.mul_mem hdM hg, hcen⟩
  have hgoal : g = d⁻¹ * (d * g) := by group
  rw [hgoal]
  exact Subgroup.mul_mem_sup (E.inv_mem hd) hmem

end Work.CORE4
