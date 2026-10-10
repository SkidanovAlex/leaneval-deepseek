import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Algebra.Group.Pi.Units
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.GroupTheory

open scoped Nat

/-- A sequence of pairwise distinct primes: `primeSeq n hn k` is a prime congruent to `1`
modulo `n k`, and the sequence is strictly increasing (hence the primes are distinct).  The
bound used when choosing the `(k+1)`-st prime is the value at `k`, which guarantees strict
growth. -/
noncomputable def primeSeq (n : ℕ → ℕ) (hn : ∀ i, n i ≠ 0) : ℕ → ℕ
  | 0 => Classical.choose (Nat.exists_prime_gt_modEq_one 0 (hn 0))
  | (i + 1) => Classical.choose (Nat.exists_prime_gt_modEq_one (primeSeq n hn i) (hn (i + 1)))

theorem primeSeq_prime (n : ℕ → ℕ) (hn : ∀ i, n i ≠ 0) (m : ℕ) :
    Nat.Prime (primeSeq n hn m) := by
  cases m with
  | zero => exact (Classical.choose_spec (Nat.exists_prime_gt_modEq_one 0 (hn 0))).1
  | succ m =>
    exact (Classical.choose_spec
      (Nat.exists_prime_gt_modEq_one (primeSeq n hn m) (hn (m + 1)))).1

theorem primeSeq_modEq (n : ℕ → ℕ) (hn : ∀ i, n i ≠ 0) (m : ℕ) :
    primeSeq n hn m ≡ 1 [MOD n m] := by
  cases m with
  | zero => exact (Classical.choose_spec (Nat.exists_prime_gt_modEq_one 0 (hn 0))).2.2
  | succ m =>
    exact (Classical.choose_spec
      (Nat.exists_prime_gt_modEq_one (primeSeq n hn m) (hn (m + 1)))).2.2

theorem primeSeq_lt_succ (n : ℕ → ℕ) (hn : ∀ i, n i ≠ 0) (m : ℕ) :
    primeSeq n hn m < primeSeq n hn (m + 1) :=
  (Classical.choose_spec (Nat.exists_prime_gt_modEq_one (primeSeq n hn m) (hn (m + 1)))).2.1

theorem primeSeq_strictMono (n : ℕ → ℕ) (hn : ∀ i, n i ≠ 0) :
    StrictMono (primeSeq n hn) :=
  strictMono_nat_of_lt_succ (primeSeq_lt_succ n hn)

/-- Every finite abelian group is a quotient of `(ZMod N)ˣ` for some `N ≠ 0`.

Hints: `CommGroup.equiv_prod_multiplicative_zmod_of_finite` writes
`G ≃* ∏ i, Multiplicative (ZMod (n i))` with `1 < n i`. Choose distinct primes `p i ≡ 1 [MOD n i]`
(Dirichlet: `Nat.exists_prime_gt_modEq_one`) and set `N = ∏ i, p i`. Then `ZMod.prodEquivPi`,
`Units.mapEquiv`, `MulEquiv.piUnits` give `(ZMod N)ˣ ≃* ∏ i, (ZMod (p i))ˣ`;
`ZMod.isCyclic_units_prime` and `zmodCyclicMulEquiv` identify `(ZMod (p i))ˣ` with
`Multiplicative (ZMod (p i - 1))`, and `ZMod.castHom (n i ∣ p i - 1)` gives a surjection
`Multiplicative (ZMod (p i - 1)) →* Multiplicative (ZMod (n i))` (`ZMod.castHom_surjective`).
Finally use that a product of surjections is surjective. -/
theorem exists_surjective_units_zmod (G : Type*) [CommGroup G] [Finite G] :
    ∃ (N : ℕ) (_ : N ≠ 0), ∃ f : (ZMod N)ˣ →* G, Function.Surjective f := by
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite G
  letI : Fintype ι := hι
  let k := Fintype.card ι
  let eι : ι ≃ Fin k := Fintype.equivFin ι
  -- Extend the family `n` to all of `ℕ` by the value `1` outside `Fin k`.
  let n' : ℕ → ℕ := fun m => if h : m < k then n (eι.symm ⟨m, h⟩) else 1
  have hn' : ∀ m, n' m ≠ 0 := by
    intro m
    dsimp only [n']
    split_ifs with h
    · have : 0 < n (eι.symm ⟨m, h⟩) := lt_trans Nat.zero_lt_one (hn _)
      exact this.ne'
    · exact one_ne_zero
  -- Distinct primes `p i ≡ 1 [MOD n i]`.
  let p : ι → ℕ := fun i => primeSeq n' hn' (eι i).val
  have hp_prime : ∀ i, Nat.Prime (p i) := fun i => primeSeq_prime n' hn' (eι i).val
  have hp_inj : Function.Injective p := by
    intro i j hij
    have h3 : (eι i).val = (eι j).val :=
      (primeSeq_strictMono n' hn').injective hij
    exact eι.injective (Fin.ext h3)
  have hne' : ∀ i, n' (eι i).val = n i := by
    intro i
    show (if h : (eι i).val < k then n (eι.symm ⟨(eι i).val, h⟩) else 1) = n i
    rw [dif_pos (eι i).isLt]
    congr 1
    exact Equiv.symm_apply_apply eι i
  have hp_congr : ∀ i, p i ≡ 1 [MOD n i] := by
    intro i
    have h := primeSeq_modEq n' hn' (eι i).val
    rwa [hne' i] at h
  have hcop : Pairwise (Function.onFun Nat.Coprime p) := fun i j hij =>
    (Nat.coprime_primes (hp_prime i) (hp_prime j)).mpr (fun h => hij (hp_inj h))
  -- The modulus `N = ∏ i, p i` is nonzero.
  let N : ℕ := ∏ i, p i
  have hN : N ≠ 0 := by
    show (∏ i, p i) ≠ 0
    exact Finset.prod_ne_zero_iff.mpr (fun a _ => (hp_prime a).ne_zero)
  -- Chinese remainder theorem: `(ZMod N)ˣ ≃* ∏ i, (ZMod (p i))ˣ`.
  let crt : ZMod N ≃+* ((i : ι) → ZMod (p i)) := ZMod.prodEquivPi p hcop
  let iso1 : (ZMod N)ˣ ≃* ((i : ι) → (ZMod (p i))ˣ) :=
    (Units.mapEquiv crt.toMulEquiv).trans MulEquiv.piUnits
  have hdiv : ∀ i, n i ∣ p i - 1 := fun i =>
    (Nat.modEq_iff_dvd' (le_of_lt (hp_prime i).one_lt)).mp (hp_congr i).symm
  -- For each `i`, a surjection `(ZMod (p i))ˣ →* Multiplicative (ZMod (n i))`.
  have hsurj : ∀ i, ∃ g : (ZMod (p i))ˣ →* Multiplicative (ZMod (n i)),
      Function.Surjective g := by
    intro i
    haveI : Fact (Nat.Prime (p i)) := ⟨hp_prime i⟩
    have hcyc : IsCyclic (ZMod (p i))ˣ := ZMod.isCyclic_units_prime (hp_prime i)
    have hcard : Nat.card (ZMod (p i))ˣ = p i - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units]
    let θ : Multiplicative (ZMod (p i - 1)) ≃* (ZMod (p i))ˣ := hcard ▸ zmodCyclicMulEquiv hcyc
    let c : ZMod (p i - 1) →+ ZMod (n i) := (ZMod.castHom (hdiv i) (ZMod (n i))).toAddMonoidHom
    let χ : Multiplicative (ZMod (p i - 1)) →* Multiplicative (ZMod (n i)) :=
      AddMonoidHom.toMultiplicative c
    refine ⟨χ.comp θ.symm.toMonoidHom, ?_⟩
    have hc_surj : Function.Surjective c := ZMod.castHom_surjective (hdiv i)
    have hχ : Function.Surjective χ := by
      intro y
      obtain ⟨a, ha⟩ := hc_surj (Multiplicative.toAdd y)
      refine ⟨Multiplicative.ofAdd a, ?_⟩
      rw [show χ (Multiplicative.ofAdd a) = Multiplicative.ofAdd (c a) from rfl, ha,
        ofAdd_toAdd]
    exact hχ.comp θ.symm.surjective
  choose f_i hf_i using hsurj
  -- Componentwise surjection on the product.
  let F : ((i : ι) → (ZMod (p i))ˣ) →* ((i : ι) → Multiplicative (ZMod (n i))) :=
    MonoidHom.piMap f_i
  have hF : Function.Surjective F :=
    Function.Surjective.piMap (fun i => hf_i i)
  let f : (ZMod N)ˣ →* G := e.symm.toMonoidHom.comp (F.comp iso1.toMonoidHom)
  refine ⟨N, hN, f, ?_⟩
  intro y
  obtain ⟨a, ha⟩ := e.symm.surjective y
  obtain ⟨b, hb⟩ := hF a
  obtain ⟨c, hc⟩ := iso1.surjective b
  refine ⟨c, ?_⟩
  show e.symm (F (iso1 c)) = y
  rw [hc, hb, ha]

end Work.GroupTheory
