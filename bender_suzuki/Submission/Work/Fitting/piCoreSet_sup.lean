import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.piCoreSet_sup`

The set `piCoreSet π G` of normal `π`-subgroups of `G` is closed under joins: if `|N|` and
`|M|` are `π`-numbers, then so is `|N ⊔ M|`.

The mathematical content is the cardinal identity

`|N ⊔ M| * |N ⊓ M| = |N| * |M|`  for `N` normal,

which is a form of the second isomorphism theorem (`N ⊔ M` is the union of the cosets of
`N` representing `M/(N ⊓ M)`).  Consequently `|N ⊔ M|` divides `|N| * |M|`, so every prime
divisor of `|N ⊔ M|` divides `|N|` or `|M|`, hence lies in `π`.

No finiteness hypothesis on `G` is needed: the identity above holds with Mathlib's convention
`Nat.card _ = 0` on infinite types (both sides vanish as soon as one of the subgroups is
infinite), and in that degenerate case `IsPiNat π 0` says that *every* prime lies in `π`,
which is exactly what is needed.
-/

noncomputable section

set_option linter.style.haveILetI false

open Classical

namespace Work.Fitting

variable {G : Type*} [Group G]

/-- Cardinal identity for the join of two subgroups, the first being normal:
`|N ⊔ M| * |N ⊓ M| = |N| * |M|`.

The second isomorphism theorem gives `|N ⊔ M| = |M| * [M : M ⊓ N]` and Lagrange's theorem
gives `|M| = [M : M ⊓ N] * |M ⊓ N|`; the claim follows.  The statement is unconditional:
for infinite subgroups both sides are `0`. -/
private lemma card_sup_mul_card_inf (N M : Subgroup G) [N.Normal] :
    Nat.card ↥(N ⊔ M) * Nat.card ↥(N ⊓ M) = Nat.card ↥N * Nat.card ↥M := by
  have hcard : ∀ {H K : Subgroup G}, Nat.card ↥(H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
    intro H K
    rw [← Subgroup.inf_subgroupOf_right H K]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := H ⊓ K) (K := K) inf_le_right).toEquiv
  -- `|N ⊔ M| = |N| * [M : M ⊓ N]`, via Lagrange in `N ⊔ M`.
  have h1 : Nat.card ↥(N ⊔ M) = Nat.card ↥N * N.relIndex M := by
    rw [← Subgroup.index_mul_card (N.subgroupOf (N ⊔ M)),
      show (N.subgroupOf (N ⊔ M)).index = N.relIndex (N ⊔ M) from rfl,
      Subgroup.relIndex_sup_left M N,
      hcard (H := N) (K := N ⊔ M), inf_of_le_left le_sup_left]
    ring
  -- `|M| = [M : M ⊓ N] * |N ⊓ M|`, via Lagrange in `M`.
  have h2 : Nat.card ↥M = N.relIndex M * Nat.card ↥(N ⊓ M) := by
    rw [← Subgroup.index_mul_card (N.subgroupOf M),
      show (N.subgroupOf M).index = N.relIndex M from rfl,
      hcard (H := N) (K := M), inf_comm]
  rw [h1, h2]; ring

/-- The order of `N ⊔ M` divides `|N| * |M|` when `N` is normal.  (Unconditional: for infinite
subgroups both sides are `0`.) -/
private lemma card_sup_dvd_mul_card (N M : Subgroup G) [N.Normal] :
    Nat.card ↥(N ⊔ M) ∣ Nat.card ↥N * Nat.card ↥M :=
  ⟨Nat.card ↥(N ⊓ M), (card_sup_mul_card_inf N M).symm⟩

/-- The join of two normal `π`-subgroups is again a normal `π`-subgroup. -/
theorem sup_mem_piCoreSet_of_isPiNat {π : ℕ → Prop} {N M : Subgroup G}
    (hN : N.Normal) (hM : M.Normal)
    (hNπ : IsPiNat π (Nat.card ↥N)) (hMπ : IsPiNat π (Nat.card ↥M)) :
    N ⊔ M ∈ piCoreSet π G := by
  haveI := hN
  haveI := hM
  exact ⟨inferInstance, isPiNat_of_dvd (card_sup_dvd_mul_card N M) (IsPiNat.mul hNπ hMπ)⟩

theorem piCoreSet_sup {G : Type*} [Group G] {π : ℕ → Prop} {N M : Subgroup G}
    (hN : N ∈ Work.Fitting.piCoreSet π G) (hM : M ∈ Work.Fitting.piCoreSet π G) :
    N ⊔ M ∈ Work.Fitting.piCoreSet π G := by
  rw [mem_piCoreSet] at hN hM
  exact sup_mem_piCoreSet_of_isPiNat hN.1 hM.1 hN.2 hM.2

end Work.Fitting
