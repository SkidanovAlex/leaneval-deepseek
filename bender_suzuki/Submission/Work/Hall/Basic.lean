import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Hall`: Hall subgroups of finite groups

This is the base module of area A1 of the Feit–Thompson (odd order theorem) drive: the theory of
Hall `π`-subgroups of finite solvable groups (P. Hall's theorems `E_π`, `C_π`, `D_π` in the
notation of Feit–Thompson 1963, Chapter I §2).

## Conventions

* `π : ℕ → Prop` is a *set of primes* (the predicate is only ever asked about primes).
* `IsPiNat π n` : `n` is a `π`-number, i.e. every prime divisor of `n` lies in `π`.
* `IsPiSubgroup π H` : `H` is a `π`-subgroup, i.e. `|H|` is a `π`-number.
* `IsHall π H` : `H` is a Hall `π`-subgroup of `G`: `|H|` is a `π`-number and
  `[G : H]` is a `π'`-number (an `S_π`-subgroup in the terminology of Feit–Thompson).
* `piPart π n` : the largest `π`-number dividing `n` (FT's `n_π`).
* Conjugation of subgroups is Mathlib's pointwise action `MulAut.conj g • H`.
* `IsMinimalNormal N` : `N` is a nontrivial normal subgroup of `G` minimal with that property.
* `IsElementaryAbelian p A` : `A` is abelian and has exponent dividing `p`.

Everything is stated for a general group `G`; finiteness hypotheses appear as `[Finite G]`.

## Main results (in `Work.Hall.Main`)

* `Work.Hall.exists_isHall` — `E_π` : a finite solvable group has a Hall `π`-subgroup.
* `Work.Hall.isHall_conj` — `C_π` : any two Hall `π`-subgroups are conjugate.
* `Work.Hall.le_conj_of_isPiNat` — `D_π` : every `π`-subgroup lies in a conjugate of a given
  Hall `π`-subgroup.
* `Work.Hall.schurZassenhaus_conj` — conjugacy of complements of a normal Hall subgroup.
-/

universe u

open scoped Pointwise

namespace Work.Hall

open Classical

variable {G : Type*} [Group G]

/-- `n` is a `π`-number: every prime divisor of `n` lies in `π`. -/
def IsPiNat (π : ℕ → Prop) (n : ℕ) : Prop := ∀ p, p.Prime → p ∣ n → π p

/-- `H` is a `π`-subgroup of `G`: `|H|` is a `π`-number. -/
def IsPiSubgroup (π : ℕ → Prop) (H : Subgroup G) : Prop := IsPiNat π (Nat.card H)

/-- `H` is a Hall `π`-subgroup of `G` (an `S_π`-subgroup in Feit–Thompson's terminology):
`|H|` is a `π`-number and `[G : H]` is a `π'`-number. -/
def IsHall (π : ℕ → Prop) (H : Subgroup G) : Prop :=
  IsPiNat π (Nat.card H) ∧ IsPiNat (fun p => ¬ π p) H.index

/-- The `π`-part of a natural number: the largest `π`-number dividing `n`
(Feit–Thompson's `n_π`). -/
noncomputable def piPart (π : ℕ → Prop) (n : ℕ) : ℕ :=
  ∏ p ∈ (n.primeFactors.filter π), p ^ n.factorization p

/-- `N` is a minimal normal subgroup of `G`: nontrivial, normal, and containing no smaller
nontrivial normal subgroup of `G`. -/
def IsMinimalNormal (N : Subgroup G) : Prop :=
  N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup G, M.Normal → M ≤ N → M ≠ ⊥ → N ≤ M

/-- `A` is elementary abelian of exponent `p`: abelian, with every element of order dividing `p`. -/
def IsElementaryAbelian (p : ℕ) (A : Subgroup G) : Prop :=
  IsMulCommutative A ∧ ∀ a : A, a ^ p = 1


section PiNatAPI

variable {π π' : ℕ → Prop} {m n k : ℕ}

theorem IsPiNat.one : IsPiNat π 1 := fun p hp hd => (hp.ne_one (Nat.dvd_one.mp hd)).elim

theorem IsPiNat.mono (h : ∀ p, π p → π' p) (hn : IsPiNat π n) : IsPiNat π' n :=
  fun p hp hd => h p (hn p hp hd)

theorem IsPiNat.of_dvd (hd : k ∣ n) (hn : IsPiNat π n) : IsPiNat π k :=
  fun p hp hpk => hn p hp (hpk.trans hd)

theorem IsPiNat.of_eq (h : m = n) (hn : IsPiNat π n) : IsPiNat π m := h ▸ hn

theorem IsPiNat.mul (hm : IsPiNat π m) (hn : IsPiNat π n) : IsPiNat π (m * n) := by
  intro p hp hd
  rcases hp.dvd_mul.mp hd with h | h
  · exact hm p hp h
  · exact hn p hp h

theorem IsPiNat.pow (hn : IsPiNat π n) (k : ℕ) : IsPiNat π (n ^ k) :=
  fun p hp hd => hn p hp (hp.dvd_of_dvd_pow hd)

/-- If every prime divisor of `n` is `p` and `p ∈ π`, then `n` is a `π`-number. -/
theorem IsPiNat.of_eq_prime {p : ℕ} (h : IsPiNat (fun q => q = p) n) (hpπ : π p) :
    IsPiNat π n := by
  intro q hq hd
  rw [show q = p from h q hq hd]
  exact hpπ

/-- If every prime divisor of `n` is `p` and `p ∉ π`, then `n` is a `π'`-number. -/
theorem IsPiNat.of_eq_prime_compl {p : ℕ} (h : IsPiNat (fun q => q = p) n) (hpπ : ¬ π p) :
    IsPiNat (fun q => ¬ π q) n := by
  intro q hq hd
  rw [show q = p from h q hq hd]
  exact hpπ

end PiNatAPI

section IsHallAPI

variable {G : Type*} [Group G] {π : ℕ → Prop} {H : Subgroup G}

/-- Conjugation preserves the property of being a Hall `π`-subgroup. -/
theorem IsHall.map_mulAut (e : MulAut G) (h : IsHall π H) : IsHall π (H.map e.toMonoidHom) :=
  ⟨h.1.of_dvd (Subgroup.card_map_dvd H e.toMonoidHom),
    h.2.of_eq (Subgroup.index_map_of_bijective e.bijective H)⟩

theorem IsHall.conj_iff (g : G) : IsHall π (MulAut.conj g • H) ↔ IsHall π H :=
  ⟨fun h =>
      ⟨h.1.of_eq (Subgroup.card_map_of_injective (K := H) (MulAut.conj g).injective).symm,
        h.2.of_eq (Subgroup.index_map_of_bijective (MulAut.conj g).bijective H).symm⟩,
    fun h => h.map_mulAut (MulAut.conj g)⟩

/-- The image of a Hall `π`-subgroup under a surjective homomorphism is a Hall `π`-subgroup. -/
theorem isHall_map_of_surjective {G G' : Type*} [Group G] [Group G'] {π : ℕ → Prop}
    (f : G →* G') (hf : Function.Surjective f) {H : Subgroup G} (h : IsHall π H) :
    IsHall π (H.map f) :=
  ⟨h.1.of_dvd (Subgroup.card_map_dvd H f), h.2.of_dvd (Subgroup.index_map_dvd H hf)⟩

end IsHallAPI

end Work.Hall
