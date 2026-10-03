import Mathlib
import Submission.Work.OROneRel.tlWindowHalvesDefs
import Submission.Work.OROneRel.hnnConjSplit

/-!
# The descent argument for the two-letter band: the gate bookkeeping

This file develops the *descent argument* of
`Submission/Work/OROneRel/NOTES_twoLetter_hnnConjMap_routes.md`, §10, which proves

  `Function.Injective (hnnConjMap (tlH p q Wt) (tlLowTau p q))`

(the two-letter band splitting at the level of `F₂`), from the single Mayer--Vietoris input
`Work.OROneRel.tlHalves_inter` (**INT**).

## The gate bookkeeping

The reduced normal form of an element of `HNN(↥H, hnnEdgeA H τ, hnnEdgeB H τ, hnnConjEquiv H τ)`
(Mathlib's `HNNExtension.NormalWord`) carries the "chain" condition

  `g_i ∈ toSubgroup A B u_i → u_i = u_{i+1}`,

which, transported to `F₂` along `hnnConjMap`, says: for consecutive exponents `u_i, u_{i+1}`,

* `u_i = +1`, `u_{i+1} = -1` (a *peak* of the level walk at `S_i`):  `k_i ∉ tlAk (S_i - 1)`;
* `u_i = -1`, `u_{i+1} = +1` (a *valley*):                        `k_i ∉ tlAk S_i`,

where `S_i = u_1 + … + u_i` and `k_i = τ ^ (S_i) · g_i · τ ^ (-S_i)`.  This file proves exactly
those two translations (`mem_tlAk_sub_one_iff` and `mem_tlAk_iff`).
-/
namespace Work.OROneRel

universe u

/-- The coercion of a conjugation automorphism, in a form that rewrites. -/
theorem toMonoidHom_conj_apply {G : Type*} [Group G] (g x : G) :
    MulEquiv.toMonoidHom (MulAut.conj g) x = g * x * g⁻¹ :=
  MulAut.conj_apply g x

/-- Membership in a conjugated subgroup `a H a⁻¹`. -/
theorem mem_map_conj_iff {G : Type*} [Group G] (H : Subgroup G) (a g : G) :
    g ∈ H.map (MulAut.conj a) ↔ a⁻¹ * g * a ∈ H := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, hhg⟩
    have h2 : (MulAut.conj a) h = g := hhg
    rw [MulAut.conj_apply] at h2
    rw [← h2]
    rw [show a⁻¹ * (a * h * a⁻¹) * a = h from by group]
    exact hh
  · intro hg
    refine ⟨a⁻¹ * g * a, hg, ?_⟩
    show (MulAut.conj a) (a⁻¹ * g * a) = g
    rw [MulAut.conj_apply]
    group

/-- Membership in a translated vertex `tlHk k = τ ^ k · tlH · τ ^ (-k)`. -/
theorem mem_tlHk_iff_desc (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (k : ℤ) (x : FreeGroup (Fin 2)) :
    x ∈ tlHk p q hp hq hcop Wt k ↔
      (tlLowTau p q hp hq hcop ^ k)⁻¹ * x * (tlLowTau p q hp hq hcop ^ k) ∈ tlH p q Wt :=
  mem_map_conj_iff _ _ _

/-- **The peak translation**: the conjugate `τ^S · g · τ^(-S)` lies in the gate `tlAk (S-1)`
(`= tlHk (S-1) ⊓ tlHk S`) exactly when `g ∈ hnnEdgeA (tlH) τ = tlH ⊓ τ⁻¹ tlH τ`. -/
theorem mem_tlAk_sub_one_iff (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (S : ℤ) (g : FreeGroup (Fin 2)) :
    (tlLowTau p q hp hq hcop ^ S) * g * (tlLowTau p q hp hq hcop ^ S)⁻¹ ∈ tlAk p q hp hq hcop Wt (S - 1) ↔
      g ∈ hnnEdgeA (tlH p q Wt) (tlLowTau p q hp hq hcop) := by
  rw [tlAk, Subgroup.mem_inf, mem_tlHk_iff_desc, mem_tlHk_iff_desc, hnnEdgeA, Subgroup.mem_inf,
    mem_map_conj_iff]
  have hS : S - 1 + 1 = S := by ring
  simp only [hS, tlH, inv_inv]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · rw [show g = (tlLowTau p q hp hq hcop ^ S)⁻¹ * ((tlLowTau p q hp hq hcop ^ S) * g * (tlLowTau p q hp hq hcop ^ S)⁻¹) * (tlLowTau p q hp hq hcop ^ S) from by group]
      exact h2
    · rw [show (tlLowTau p q hp hq hcop) * g * (tlLowTau p q hp hq hcop)⁻¹ = (tlLowTau p q hp hq hcop ^ (S - 1))⁻¹
          * ((tlLowTau p q hp hq hcop ^ S) * g * (tlLowTau p q hp hq hcop ^ S)⁻¹) * (tlLowTau p q hp hq hcop ^ (S - 1)) from by group]
      exact h1
  · rintro ⟨h2, h1⟩
    refine ⟨?_, ?_⟩
    · rw [show (tlLowTau p q hp hq hcop ^ (S - 1))⁻¹ * ((tlLowTau p q hp hq hcop ^ S) * g * (tlLowTau p q hp hq hcop ^ S)⁻¹) * (tlLowTau p q hp hq hcop ^ (S - 1))
          = (tlLowTau p q hp hq hcop) * g * (tlLowTau p q hp hq hcop)⁻¹ from by group]
      exact h1
    · rw [show (tlLowTau p q hp hq hcop ^ S)⁻¹ * ((tlLowTau p q hp hq hcop ^ S) * g * (tlLowTau p q hp hq hcop ^ S)⁻¹) * (tlLowTau p q hp hq hcop ^ S) = g from by group]
      exact h2

/-- **The valley translation**: the conjugate `τ^S · g · τ^(-S)` lies in the gate `tlAk S`
(`= tlHk S ⊓ tlHk (S+1)`) exactly when `g ∈ hnnEdgeB (tlH) τ = τ (hnnEdgeA) τ⁻¹
(= tlH ⊓ τ tlH τ⁻¹)`. -/
theorem mem_tlAk_iff (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2)) (S : ℤ) (g : FreeGroup (Fin 2)) :
    (tlLowTau p q hp hq hcop ^ S) * g * (tlLowTau p q hp hq hcop ^ S)⁻¹ ∈ tlAk p q hp hq hcop Wt S ↔
      g ∈ hnnEdgeB (tlH p q Wt) (tlLowTau p q hp hq hcop) := by
  rw [tlAk, Subgroup.mem_inf, mem_tlHk_iff_desc, mem_tlHk_iff_desc, hnnEdgeB, hnnEdgeA,
    mem_map_conj_iff, Subgroup.mem_inf, mem_map_conj_iff]
  simp only [tlH, inv_inv]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · rw [show (tlLowTau p q hp hq hcop)⁻¹ * g * (tlLowTau p q hp hq hcop) = (tlLowTau p q hp hq hcop ^ (S + 1))⁻¹
          * ((tlLowTau p q hp hq hcop ^ S) * g * (tlLowTau p q hp hq hcop ^ S)⁻¹) * (tlLowTau p q hp hq hcop ^ (S + 1)) from by group]
      exact h2
    · rw [show (tlLowTau p q hp hq hcop) * ((tlLowTau p q hp hq hcop)⁻¹ * g * (tlLowTau p q hp hq hcop)) * (tlLowTau p q hp hq hcop)⁻¹ = (tlLowTau p q hp hq hcop ^ S)⁻¹
          * ((tlLowTau p q hp hq hcop ^ S) * g * (tlLowTau p q hp hq hcop ^ S)⁻¹) * (tlLowTau p q hp hq hcop ^ S) from by group]
      exact h1
  · rintro ⟨h2, h1⟩
    refine ⟨?_, ?_⟩
    · rw [show (tlLowTau p q hp hq hcop ^ S)⁻¹ * ((tlLowTau p q hp hq hcop ^ S) * g * (tlLowTau p q hp hq hcop ^ S)⁻¹) * (tlLowTau p q hp hq hcop ^ S)
          = (tlLowTau p q hp hq hcop) * ((tlLowTau p q hp hq hcop)⁻¹ * g * (tlLowTau p q hp hq hcop)) * (tlLowTau p q hp hq hcop)⁻¹ from by group]
      exact h1
    · rw [show (tlLowTau p q hp hq hcop ^ (S + 1))⁻¹ * ((tlLowTau p q hp hq hcop ^ S) * g * (tlLowTau p q hp hq hcop ^ S)⁻¹) * (tlLowTau p q hp hq hcop ^ (S + 1))
          = (tlLowTau p q hp hq hcop)⁻¹ * g * (tlLowTau p q hp hq hcop) from by group]
      exact h2


/-! ## The two block lemmas (the heart of the descent)

These are stated here (and are the remaining work); the proofs are the induction on the number `n`
of letters described in `Submission/Work/OROneRel/NOTES_twoLetter_hnnConjMap_routes.md`, §10.3.

An **up-block** is a sequence of letters `y : Fin n → F₂` at levels `t : Fin n → ℤ` with
`t 0 = t (n-1) = b`, all levels `≥ b`, consecutive levels differing by `1`, `y i ∈ tlHk (t i)`, and
the *peak* condition: whenever the level just before `i` equals the level just after `i` (with the
two boundary levels read as `b-1`), `y i ∉ tlAk (t i - 1)`.  Conclusion: the product is not in
`tlPle (b-1)`.

The **down-block** is the mirror image (levels `≤ b`, external levels `b+1`, valley condition
`y i ∉ tlAk (t i)`), with conclusion "the product is not in `tlPge (b+1)`". -/

/-- The predecessor index of `i : Fin n` stays in range. -/
theorem fin_sub_one_lt {n : ℕ} (hn : 1 ≤ n) (i : Fin n) : i.1 - 1 < n := by
  rcases Nat.eq_zero_or_pos i.1 with h | h
  · rw [h]; omega
  · exact lt_of_le_of_lt (Nat.sub_le _ _) i.isLt

/-- The level *before* the `i`-th letter of a block based at level `b` (the level of the letter
preceding the block if `i` is the first letter). -/
noncomputable def blkPrev (b : ℤ) {n : ℕ} (hn : 1 ≤ n) (t : Fin n → ℤ) (i : Fin n) : ℤ :=
  if i = ⟨0, hn⟩ then b - 1 else t ⟨i.1 - 1, fin_sub_one_lt hn i⟩

/-- The level *after* the `i`-th letter of a block based at level `b`. -/
noncomputable def blkNext (b : ℤ) {n : ℕ} (t : Fin n → ℤ) (i : Fin n) : ℤ :=
  if h : i.1 + 1 < n then t ⟨i.1 + 1, h⟩ else b - 1

/-- Variant of `blkNext` with the external level `e` (used for down-blocks, where the external level
is `b + 1`). -/
noncomputable def blkNextE (e : ℤ) {n : ℕ} (t : Fin n → ℤ) (i : Fin n) : ℤ :=
  if h : i.1 + 1 < n then t ⟨i.1 + 1, h⟩ else e

/-- Variant of `blkPrev` with the external level `e`. -/
noncomputable def blkPrevE (e : ℤ) {n : ℕ} (hn : 1 ≤ n) (t : Fin n → ℤ) (i : Fin n) : ℤ :=
  if i = ⟨0, hn⟩ then e else t ⟨i.1 - 1, fin_sub_one_lt hn i⟩

@[simp] theorem blkPrev_zero (b : ℤ) {n : ℕ} (hn : 1 ≤ n) (t : Fin n → ℤ) :
    blkPrev b hn t ⟨0, hn⟩ = b - 1 := by
  rw [blkPrev]; simp

@[simp] theorem blkNextE_last (e : ℤ) {n : ℕ} (hn : 1 ≤ n) (t : Fin n → ℤ) :
    blkNextE e t ⟨n - 1, by omega⟩ = e := by
  rw [blkNextE]
  have : ¬ ((⟨n - 1, by omega⟩ : Fin n).1 + 1 < n) := by simp; omega
  simp [this]

@[simp] theorem blkPrevE_zero (e : ℤ) {n : ℕ} (hn : 1 ≤ n) (t : Fin n → ℤ) :
    blkPrevE e hn t ⟨0, hn⟩ = e := by
  rw [blkPrevE]; simp

/-- **The base case of the up-block descent**: a single letter at level `b` which is not in the gate
`tlAk (b-1)` is not in `tlPle (b-1)` either (because it is automatically in `tlPge b`). -/
theorem single_letter_not_mem_tlPle (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2))
    (hINT : ∀ c : ℤ, tlPle p q hp hq hcop Wt c ⊓ tlPge p q hp hq hcop Wt (c + 1)
      = tlAk p q hp hq hcop Wt c)
    (b : ℤ) (y : FreeGroup (Fin 2)) (hy : y ∈ tlHk p q hp hq hcop Wt b)
    (hpeak : y ∉ tlAk p q hp hq hcop Wt (b - 1)) :
    y ∉ tlPle p q hp hq hcop Wt (b - 1) := by
  intro h
  have h2 : y ∈ tlPge p q hp hq hcop Wt (b - 1 + 1) := by
    rw [show b - 1 + 1 = b from by ring]
    exact tlHk_le_tlPge p q hp hq hcop Wt le_rfl hy
  have h3 : y ∈ tlAk p q hp hq hcop Wt (b - 1) := by
    rw [← hINT (b - 1)]
    exact ⟨h, h2⟩
  exact hpeak h3

/-- **The base case of the down-block descent** (mirror image). -/
theorem single_letter_not_mem_tlPge (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hcop : Nat.Coprime p q)
    (Wt : ℤ → FreeGroup (Fin 2))
    (hINT : ∀ c : ℤ, tlPle p q hp hq hcop Wt c ⊓ tlPge p q hp hq hcop Wt (c + 1)
      = tlAk p q hp hq hcop Wt c)
    (b : ℤ) (y : FreeGroup (Fin 2)) (hy : y ∈ tlHk p q hp hq hcop Wt b)
    (hvalley : y ∉ tlAk p q hp hq hcop Wt b) :
    y ∉ tlPge p q hp hq hcop Wt (b + 1) := by
  intro h
  have h2 : y ∈ tlPle p q hp hq hcop Wt b := tlHk_le_tlPle p q hp hq hcop Wt le_rfl hy
  have h3 : y ∈ tlAk p q hp hq hcop Wt b := by
    rw [← hINT b]
    exact ⟨h2, h⟩
  exact hvalley h3

end Work.OROneRel
