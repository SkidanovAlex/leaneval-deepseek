import Mathlib
import Submission.Work.BSHallW.Defs
import Submission.Work.Grun.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSHallW.WeakClosure` — weakly closed subgroups of a Sylow subgroup

Throughout, `S` is a subgroup of a group `G`, `A ≤ S`, and `A` is *weakly closed in `S` with
respect to `G`* in the sense of `Work.ThmF.HallWielandtProp` (and of the corrected
`Work.BSHallW.HallWielandtOddProp`):

`hwc : ∀ g : G, A^g ≤ S → A^g = A`,   where `A^g = A.map (MulAut.conj g).toMonoidHom = g A g⁻¹`.

This file collects the three elementary consequences that the Hall–Wielandt argument uses:

* `conj_mem_of_weaklyClosed` — for `g ∈ S` and `a ∈ A`, the conjugate `g a g⁻¹` lies in `A`
  (take `g ∈ S`: then `A^g ≤ S` because `g, a, g⁻¹ ∈ S`);
* `le_normalizer_of_weaklyClosed` — `S ≤ N_G(A)` (the same fact, in normalizer form);
* `subgroupOf_normal_of_weaklyClosed` — `A` is normal in `S` (as a subgroup of `↥S`);
* `commutator_mem_of_weaklyClosed` — for `u ∈ S`, `z ∈ A` one has `⁅u, z⁆ ∈ A`.

This last one is what makes Hall's condition 2) of Theorem 14.4.2 available: since `A` is abelian,
`⁅u, z⁆ ∈ A` and `z ∈ A` commute, so `e_p(u,z) = e_{p-1}(⁅u,z⁆,z) = 1` for `p ≥ 3`
(`Work.BSHallW.IterComm`).
-/

set_option autoImplicit false

open scoped commutatorElement

namespace Work.BSHallW

variable {G : Type*} [Group G]

/-- **Weak closure, elementwise form.**  If `A ≤ S` is weakly closed in `S` and `g ∈ S`, then
conjugation by `g` preserves `A` pointwise. -/
theorem conj_mem_of_weaklyClosed {S A : Subgroup G} (hAS : A ≤ S)
    (hwc : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ S →
      A.map (MulAut.conj g).toMonoidHom = A)
    {g : G} (hg : g ∈ S) {a : G} (ha : a ∈ A) : g * a * g⁻¹ ∈ A := by
  have hle : A.map (MulAut.conj g).toMonoidHom ≤ S := by
    rintro x ⟨a', ha', rfl⟩
    exact S.mul_mem (S.mul_mem hg (hAS ha')) (S.inv_mem hg)
  have heq := hwc g hle
  have hmem : g * a * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
  rwa [heq] at hmem

/-- **Weak closure gives `S ≤ N_G(A)`.**  The normalizer of `A` contains the whole Sylow subgroup
that `A` is weakly closed in. -/
theorem le_normalizer_of_weaklyClosed {S A : Subgroup G} (hAS : A ≤ S)
    (hwc : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ S →
      A.map (MulAut.conj g).toMonoidHom = A) :
    S ≤ Subgroup.normalizer (A : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact conj_mem_of_weaklyClosed hAS hwc hg hh
  · intro hh
    have h1 : g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ ∈ A :=
      conj_mem_of_weaklyClosed hAS hwc (S.inv_mem hg) hh
    have h2 : g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ = h := by group
    rwa [h2] at h1

/-- **`A` is normal in `S`.**  Weak closure of `A` in `S` (with respect to `G`) implies that the
subgroup `A.subgroupOf S` of `↥S` is normal. -/
theorem subgroupOf_normal_of_weaklyClosed {S A : Subgroup G} (hAS : A ≤ S)
    (hwc : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ S →
      A.map (MulAut.conj g).toMonoidHom = A) :
    (A.subgroupOf S).Normal := by
  refine Subgroup.Normal.mk fun n hn g => ?_
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simpa using conj_mem_of_weaklyClosed hAS hwc g.2 hn

/-- **The commutator of `S` with `A` lands in `A`.** -/
theorem commutator_mem_of_weaklyClosed {S A : Subgroup G} (hAS : A ≤ S)
    (hwc : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ S →
      A.map (MulAut.conj g).toMonoidHom = A)
    {u : G} (hu : u ∈ S) {z : G} (hz : z ∈ A) : ⁅u, z⁆ ∈ A := by
  have h1 : u * z * u⁻¹ ∈ A := conj_mem_of_weaklyClosed hAS hwc hu hz
  rw [commutatorElement_def]
  exact A.mul_mem h1 (A.inv_mem hz)

/-- **Weak closure in a `p`-group is normality.**  (Recorded for callers who have `S ≤ N_G(A)` from
`le_normalizer_of_weaklyClosed` and want the `Subgroup.Normal` instance.) -/
theorem normal_of_weaklyClosed {S A : Subgroup G} (hAS : A ≤ S)
    (hwc : ∀ g : G, A.map (MulAut.conj g).toMonoidHom ≤ S →
      A.map (MulAut.conj g).toMonoidHom = A) :
    ∀ g ∈ S, ∀ a ∈ A, g * a * g⁻¹ ∈ A :=
  fun _ hg _ ha => conj_mem_of_weaklyClosed hAS hwc hg ha

end Work.BSHallW
