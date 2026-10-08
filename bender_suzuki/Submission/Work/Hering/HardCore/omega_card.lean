/-
# The cardinality of the levels `Ω_m(C)` of an abelian group with `Ω_1(C)` of order `8`

This file proves `Work.Hering.HardCore.omega_card`:

if `C` is an abelian subgroup of a finite group `G` whose subgroup of involutions
`Ω_1(C)` is a subgroup `V` of order `8`, and if in addition every element of `V` is a
`2^(m-1)`-th power of an element of `C`, then the level-`m` subgroup
`Ω_m(C) = {x ∈ C : x ^ 2^m = 1}` has cardinality `8 ^ m`.

The proof is elementary and avoids the classification of finite abelian groups.  For
`2 ≤ j ≤ m` the map
`φ_j : Ω_j(C) → Ω_1(C)`, `x ↦ x ^ 2^(j-1)`,
is a surjective homomorphism with kernel `Ω_(j-1)(C)` (surjectivity: a `2^(m-1)`-th
root `c` of `v ∈ V` satisfies `c ^ 2^m = 1`, so `c ^ 2^(m-j)` lies in `Ω_j(C)` and maps to
`v`).  Hence `Nat.card Ω_j = Nat.card Ω_(j-1) * 8`, and induction on `j` gives the claim.

The statement being proved is exactly the one requested; no definitions from the source
are changed.
-/

import Mathlib
import Submission.Work.Hering.HardCore.abelian_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.HardCore

variable {G : Type*} [Group G]

/-- The levels `Ω_n(C)` are increasing in `n`. -/
lemma Omega_mono (C : Subgroup G) (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x) (n : ℕ) :
    Omega C hCab n ≤ Omega C hCab (n + 1) := by
  intro x hx
  rw [mem_Omega] at hx ⊢
  refine ⟨hx.1, ?_⟩
  rw [pow_succ, pow_mul, hx.2, one_pow]

/-- For subgroups `H ≤ K`, the type `↥(H.subgroupOf K)` has the same cardinality as `↥H`. -/
lemma natCard_subgroupOf_of_le {H K : Subgroup G} (h : H ≤ K) :
    Nat.card ↥(H.subgroupOf K) = Nat.card ↥H := by
  apply Nat.card_congr
  exact
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun y => ⟨⟨y.1, h y.2⟩, y.2⟩
      left_inv := fun x => by rfl
      right_inv := fun y => by rfl }

/-- The key step: for `n + 1 ≤ m`, the level-`(n+1)` subgroup has cardinality
`|Ω_n(C)| * |Ω_1(C)|`.  The homomorphism `x ↦ x ^ 2^n` from `Ω_(n+1)(C)` onto `Ω_1(C)`
has kernel `Ω_n(C)`; the hypothesis `hsurj` makes it surjective. -/
lemma card_Omega_succ (C V : Subgroup G)
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hOmega1 : Omega C hCab 1 = V) {m n : ℕ} (hnm : n + 1 ≤ m)
    (hsurj : ∀ v ∈ V, ∃ c ∈ C, c ^ 2 ^ (m - 1) = v) :
    Nat.card ↥(Omega C hCab (n + 1)) =
      Nat.card ↥(Omega C hCab n) * Nat.card ↥(Omega C hCab 1) := by
  have hm1 : 1 ≤ m := by omega
  have e1 : (2 : ℕ) ^ m = 2 ^ (m - 1) * 2 := by
    conv_lhs => rw [← Nat.sub_add_cancel hm1]
    exact pow_succ 2 (m - 1)
  have e2 : m - n - 1 + (n + 1) = m := by omega
  have e3 : m - n - 1 + n = m - 1 := by omega
  let f : ↥(Omega C hCab (n + 1)) →* ↥(Omega C hCab 1) :=
    { toFun := fun x => ⟨x.1 ^ (2 ^ n), by
        rw [mem_Omega]
        refine ⟨C.pow_mem (Omega_le C hCab (n + 1) x.2) _, ?_⟩
        rw [show (2 : ℕ) ^ 1 = 2 from rfl, ← pow_mul, (pow_succ 2 n).symm]
        exact (mem_Omega.mp x.2).2⟩
      map_one' := by
        apply Subtype.ext
        show (1 : G) ^ (2 ^ n) = 1
        rw [one_pow]
      map_mul' := fun x y => by
        ext
        simp only [Subgroup.coe_mul]
        rw [Commute.mul_pow]
        exact (commute_iff_eq _ _).mpr
          (hCab x.1 (Omega_le C hCab (n + 1) x.2) y.1 (Omega_le C hCab (n + 1) y.2)) }
  have hsurjf : Function.Surjective f := by
    intro y
    have hy : y.1 ∈ V := hOmega1 ▸ y.2
    obtain ⟨c, hcC, hc⟩ := hsurj y.1 hy
    have hcc : c ^ (2 ^ m) = 1 := by
      rw [e1, pow_mul, hc]
      exact (mem_Omega.mp y.2).2
    refine ⟨⟨c ^ (2 ^ (m - n - 1)), ?_⟩, ?_⟩
    · rw [mem_Omega]
      refine ⟨C.pow_mem hcC _, ?_⟩
      rw [← pow_mul, ← pow_add, e2]
      exact hcc
    · apply Subtype.ext
      show (c ^ (2 ^ (m - n - 1))) ^ (2 ^ n) = (y : G)
      rw [← pow_mul, ← pow_add, e3, hc]
  have hker : f.ker = (Omega C hCab n).subgroupOf (Omega C hCab (n + 1)) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_Omega, Subtype.ext_iff]
    constructor
    · intro h; exact ⟨Omega_le C hCab (n + 1) x.2, h⟩
    · rintro ⟨-, h2⟩; exact h2
  have hmem : Nat.card ↥f.ker = Nat.card ↥(Omega C hCab n) := by
    rw [hker]
    exact natCard_subgroupOf_of_le (Omega_mono C hCab n)
  have hrange : f.range = ⊤ := MonoidHom.range_eq_top.mpr hsurjf
  calc Nat.card ↥(Omega C hCab (n + 1))
      = Nat.card ↥f.ker * Nat.card ↥f.range := by
        rw [← Subgroup.card_mul_index f.ker, Subgroup.index_ker f]
    _ = Nat.card ↥(Omega C hCab n) * Nat.card ↥(Omega C hCab 1) := by
        rw [hmem, hrange]
        exact congrArg (fun t => Nat.card ↥(Omega C hCab n) * t)
          (Nat.card_congr Subgroup.topEquiv.toEquiv)

theorem omega_card {G : Type*} [Group G] [Finite G] (V C : Subgroup G)
    (hCab : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x)
    (hcard : Nat.card V = 8) (hOmega1 : Omega C hCab 1 = V) {m : ℕ} (hm : 1 ≤ m)
    (hsurj : ∀ v ∈ V, ∃ c ∈ C, c ^ 2 ^ (m - 1) = v) :
    Nat.card ↥(Omega C hCab m) = 8 ^ m := by
  have hOmega1card : Nat.card ↥(Omega C hCab 1) = 8 := by
    rw [hOmega1]; exact hcard
  have hstep : ∀ k, 1 ≤ k →
      (k ≤ m → Nat.card ↥(Omega C hCab k) = 8 ^ k) →
      (k + 1 ≤ m → Nat.card ↥(Omega C hCab (k + 1)) = 8 ^ (k + 1)) := by
    intro k _ hP hk1
    have hkm : k ≤ m := by omega
    rw [card_Omega_succ C V hCab hOmega1 hk1 hsurj, hP hkm, hOmega1card, pow_succ]
  have hbase : (1 ≤ m → Nat.card ↥(Omega C hCab 1) = 8 ^ 1) := by
    intro _
    simpa using hOmega1card
  have hkey : ∀ k, 1 ≤ k → k ≤ m → Nat.card ↥(Omega C hCab k) = 8 ^ k :=
    Nat.le_induction hbase hstep
  exact hkey m hm (le_refl m)

end Work.Hering.HardCore
