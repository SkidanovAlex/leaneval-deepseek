import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB2.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Sector.jointProj_resolution` — the resolution of the identity by the
joint sector projections

FS §6 grades a box state `Ψ` by the joint spectrum of the slot operators `Qᵢ = 1 − Pᵢ`
whose set of eigenvalues is `{0,1}` at every slot, so that

    Σ_{S ⊆ {0,…,n−1}} E_S = 1,     E_S = ∏_{i∈S} Qᵢ ∏_{j∉S} Pⱼ,

i.e. `E_S` is the spectral projection of the excitation-number operator `n₊ = Σᵢ Qᵢ`.
The statement below is that identity in the concrete vocabulary of
`Submission.Work.BoseFixB2.Defs` (`jointProj ℓ S Φ = blockOp ℓ S n Φ`, the slots `0,…,n−1`
carrying `Q` on `S` and `P` off `S`, applied in increasing order of the slot).

## The proof

Nothing analytic is needed: the whole content is the pointwise identity
`Pᵢ φ + Qᵢ φ = φ` (`aQ` is *defined* as `1 − aP`) — in particular **no continuity
hypothesis on `Φ`**.  Concretely, writing `ψ_S = blockOp ℓ S k Φ` for the composition of the
slot operators at the subsets of `{0,…,k−1}`, we prove by induction on `k` that

    Σ_{S ⊆ {0,…,k−1}} ψ_S = Φ,

using the decomposition `powerset (insert k (range k)) = powerset (range k) ∪
(powerset (range k)).image (insert k)` of the powerset of the slot index set: the new slot
contributes `aP` to the terms `S ⊆ range k` and `aQ` to the terms `insert k S`, and at each
point `x` the pair sums to `ψ_S x`.  Note that the operators are never moved past the sum:
the induction is a sum of *pointwise* rewrites, so neither additivity of the integral
defining `aP` nor commutation/idempotence of the slot operators enters.

The only recursion facts used are `blockOp_succ` (the one-step unfolding), a variant
`blockOp_congr_set_lt` of `blockOp_congr_set` with the agreement hypothesis restricted to the
slots below the recursion length `k` (which is what makes
`blockOp ℓ (insert k S) k Φ = blockOp ℓ S k Φ` available), and the definition of `aQ`.
-/

namespace Work.BoseFixB2.Sector

open Work.BoseFixB2
open Submission.BoseGases

set_option linter.unusedVariables false

/-- `blockOp` depends on `S` only through its intersection with `{0,…,k−1}`: the agreement
of `S` and `T` is needed only *below the recursion length* `k` (the variant of
`blockOp_congr_set`, whose hypothesis runs over all `j < n`, that the induction below
needs in order to compare `blockOp ℓ (insert k S) k` with `blockOp ℓ S k`). -/
lemma blockOp_congr_set_lt {ℓ : ℝ} {n : ℕ} {S T : Finset ℕ} :
    ∀ {k : ℕ}, k ≤ n → (∀ j < k, (j ∈ S ↔ j ∈ T)) → ∀ Φ : X n → ℝ,
      blockOp ℓ S k Φ = blockOp ℓ T k Φ := by
  intro k
  induction k with
  | zero => intro _ _ Φ; rfl
  | succ k ih =>
      intro hk h Φ
      have hkn : k < n := Nat.lt_of_succ_le hk
      rw [blockOp_succ S hkn Φ, blockOp_succ T hkn Φ,
          ih (Nat.le_of_lt hkn) (fun j hj => h j (Nat.lt_trans hj (Nat.lt_succ_self k))) Φ]
      by_cases hmem : k ∈ S
      · rw [if_pos hmem, if_pos ((h k (Nat.lt_succ_self k)).mp hmem)]
      · rw [if_neg hmem, if_neg (fun hc => hmem ((h k (Nat.lt_succ_self k)).mpr hc))]

/-- **The one-slot splitting step.**  For a slot set `S` of the slots `0,…,m−1` (so
`m ∉ S`), the two branches of the slot `m` — `Pₘ` for `S`, `Qₘ` for `insert m S` — applied
after the slots `< m` add up to the composition at `S`:

    `blockOp S (m+1) + blockOp (insert m S) (m+1) = blockOp S m`.

This is `Pₘ φ + Qₘ φ = φ` at `φ = blockOp S m Φ` (`aQ` is defined as `1 − aP`), together
with the fact that the slots `< m` cannot see whether the slot `m` was inserted. -/
lemma blockOp_step {ℓ : ℝ} {n m : ℕ} (hmn : m < n) {S : Finset ℕ} (hS : m ∉ S) (Φ : X n → ℝ) :
    blockOp ℓ S (m+1) Φ + blockOp ℓ (insert m S) (m+1) Φ = blockOp ℓ S m Φ := by
  have h3 : blockOp ℓ (insert m S) m Φ = blockOp ℓ S m Φ :=
    blockOp_congr_set_lt (Nat.le_of_lt hmn) (fun j hj => by
      rw [Finset.mem_insert]
      exact ⟨fun h => h.elim (fun he => absurd (he ▸ hj) (by omega)) id, Or.inr⟩) Φ
  have h1 : blockOp ℓ S (m+1) Φ = aP ℓ ⟨m,hmn⟩ (blockOp ℓ S m Φ) := by
    rw [blockOp_succ S hmn Φ, if_neg hS]
  have h2 : blockOp ℓ (insert m S) (m+1) Φ = aQ ℓ ⟨m,hmn⟩ (blockOp ℓ S m Φ) := by
    rw [blockOp_succ (insert m S) hmn Φ, if_pos (Finset.mem_insert_self m S), h3]
  rw [h1, h2]
  funext x
  show aP ℓ ⟨m,hmn⟩ (blockOp ℓ S m Φ) x + aQ ℓ ⟨m,hmn⟩ (blockOp ℓ S m Φ) x = blockOp ℓ S m Φ x
  unfold aQ
  ring

/-- **The partial resolution of the identity**: the sum of the joint sector projections of
the slots `0,…,m−1` over all their subsets is the identity, for every state `Φ` (no
regularity is needed). -/
lemma blockOp_sum_powerset (ℓ : ℝ) {n : ℕ} (Φ : X n → ℝ) :
    ∀ m, m ≤ n → (∑ S ∈ (Finset.range m).powerset, blockOp ℓ S m Φ) = Φ := by
  intro m
  induction m with
  | zero =>
      intro _
      simp
  | succ m ih =>
      intro hm
      have hmn : m < n := Nat.lt_of_succ_le hm
      have hdisj : Disjoint (Finset.range m).powerset
          ((Finset.range m).powerset.image (fun s : Finset ℕ => insert m s)) := by
        rw [Finset.disjoint_left]
        intro a ha hb
        rw [Finset.mem_image] at hb
        obtain ⟨T, hT, rfl⟩ := hb
        exact Finset.notMem_range_self ((Finset.mem_powerset.mp ha) (Finset.mem_insert_self m T))
      have hinj : Set.InjOn (fun s : Finset ℕ => insert m s) ↑((Finset.range m).powerset) := by
        intro x hx y hy hxy
        have hx' : m ∉ x := fun h => Finset.notMem_range_self ((Finset.mem_powerset.mp hx) h)
        have hy' : m ∉ y := fun h => Finset.notMem_range_self ((Finset.mem_powerset.mp hy) h)
        calc x = (insert m x).erase m := (Finset.erase_insert hx').symm
          _ = (insert m y).erase m := by rw [show insert m x = insert m y from hxy]
          _ = y := Finset.erase_insert hy'
      rw [Finset.range_add_one, Finset.powerset_insert, Finset.sum_union hdisj,
          Finset.sum_image hinj, ← Finset.sum_add_distrib]
      rw [Finset.sum_congr rfl (fun S hS =>
        blockOp_step hmn (fun hmem => Finset.notMem_range_self ((Finset.mem_powerset.mp hS) hmem)) Φ)]
      exact ih (Nat.le_of_lt hmn)

theorem jointProj_resolution {ℓ : ℝ} {n : ℕ} (hℓ : 0 < ℓ) (Φ : Submission.BoseGases.X n → ℝ) (hΦ : Continuous Φ) : (∑ S ∈ (Finset.range n).powerset, Work.BoseFixB2.jointProj ℓ S Φ) = Φ := by
  simpa only [jointProj] using blockOp_sum_powerset ℓ Φ n le_rfl

end Work.BoseFixB2.Sector
