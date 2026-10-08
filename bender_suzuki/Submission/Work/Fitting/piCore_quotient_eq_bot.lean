import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.piCore_quotient_eq_bot`

The `π`-core of `G / O_π(G)` is trivial:  `O_π(G/O_π(G)) = 1`.

Indeed, let `K = O_π(G)` and let `M` be a normal subgroup of `G/K` with `π`-order.  Its
preimage `A = M.comap (mk' K)` is a normal subgroup of `G` containing `K`, of order
`|A| = |K| * |M|` (a `π`-number, since `K ≤ G` has `π`-order).  Hence `A ≤ O_π(G) = K`,
and applying `mk' K` gives `M = f(A) ≤ f(K) = 1`.  Thus `M = ⊥` for every normal
`π`-subgroup of `G/K`, so the supremum `O_π(G/K)` is `⊥`.

The only group-theoretic input is the order formula `|f⁻¹(M)| = |ker f| * |M|` for a
surjective homomorphism `f`, which we prove above.
-/

noncomputable section

open Classical

namespace Work.Fitting

variable {G : Type*} [Group G]

/-- For a surjective homomorphism `f : G →* H` and a subgroup `M ≤ H`, the preimage of `M`
under `f` has order `|ker f| * |M|`:  the restricted map `f⁻¹(M) → M` is surjective with
kernel `ker f`, and `Nat.card ↥(ker f) * (ker f).index = Nat.card ↥(f⁻¹ M)` by Lagrange. -/
theorem card_comap_eq_card_ker_mul {H : Type*} [Group H] (f : G →* H)
    (hf : Function.Surjective f) (M : Subgroup H) :
    Nat.card ↥(Subgroup.comap f M) = Nat.card ↥f.ker * Nat.card ↥M := by
  have hK : f.ker ≤ Subgroup.comap f M := by
    intro x hx
    rw [Subgroup.mem_comap]
    rw [MonoidHom.mem_ker] at hx
    rw [hx]
    exact M.one_mem
  have hcardker : Nat.card ↥(f.ker.subgroupOf (Subgroup.comap f M)) = Nat.card ↥f.ker :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK).toEquiv
  have hidx : (f.ker.subgroupOf (Subgroup.comap f M)).index = Nat.card ↥M := by
    rw [show (f.ker.subgroupOf (Subgroup.comap f M)).index =
        f.ker.relIndex (Subgroup.comap f M) from rfl]
    rw [Subgroup.relIndex_ker,
      Subgroup.map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hf]; exact le_top)]
  calc Nat.card ↥(Subgroup.comap f M)
      = Nat.card ↥(f.ker.subgroupOf (Subgroup.comap f M)) *
        (f.ker.subgroupOf (Subgroup.comap f M)).index := (Subgroup.card_mul_index _).symm
    _ = Nat.card ↥f.ker * Nat.card ↥M := by rw [hcardker, hidx]

theorem piCore_quotient_eq_bot (π : ℕ → Prop) (G : Type*) [Group G] [Finite G] :
    Work.Fitting.piCore π (G ⧸ Work.Fitting.piCore π G) = ⊥ := by
  set K : Subgroup G := piCore π G with hKdef
  change piCore π (G ⧸ K) = ⊥
  haveI hKnorm : K.Normal := inferInstance
  set f : G →* G ⧸ K := QuotientGroup.mk' K with hfdef
  have hsurj : Function.Surjective f := QuotientGroup.mk'_surjective K
  have hker : f.ker = K := QuotientGroup.ker_mk' K
  have hkinj : IsPiNat π (Nat.card ↥K) := piCore_isPiNat G π
  refine le_antisymm ?_ bot_le
  rw [piCore]
  refine sSup_le fun M hM => ?_
  rw [mem_piCoreSet] at hM
  obtain ⟨hMnormal, hMpi⟩ := hM
  haveI : M.Normal := hMnormal
  have hrange : M ≤ f.range := by
    rw [MonoidHom.range_eq_top.mpr hsurj]; exact le_top
  have hcomap_norm : (M.comap f).Normal := Subgroup.normal_comap f
  have hcard : Nat.card ↥(M.comap f) = Nat.card ↥K * Nat.card ↥M := by
    have h := card_comap_eq_card_ker_mul f hsurj M
    rw [hker] at h
    exact h
  have hcomapπ : IsPiNat π (Nat.card ↥(M.comap f)) := by
    rw [hcard]
    exact IsPiNat.mul hkinj hMpi
  have hle : M.comap f ≤ K := le_piCore hcomap_norm hcomapπ
  have hmap : Subgroup.map f (M.comap f) = M := Subgroup.map_comap_eq_self hrange
  have hmapK : Subgroup.map f K = ⊥ :=
    (Subgroup.map_eq_bot_iff K).mpr (le_of_eq hker.symm)
  calc M = Subgroup.map f (M.comap f) := hmap.symm
    _ ≤ Subgroup.map f K := Subgroup.map_mono hle
    _ = ⊥ := hmapK

end Work.Fitting
