import Mathlib
import Submission.Work.ATOM.Defs

/-!
# AREA ATOM / `ℤ[S]`: the level structure of a light profinite set

Let `S : LightProfinite`.  Mathlib gives `S` as the limit of the finite sets
`S.component n := S.diagram.obj ⟨n⟩` along the transition maps
`S.transitionMap n : S.component (n+1) ⟶ S.component n`, with projections
`S.proj n : S ⟶ S.component n`.

This file defines:
* `sect S n` — a chosen section of `S.transitionMap n`;
* `itTr S n m h` — the iterated transition `S.component n → S.component m` (`m ≤ n`);
* `itSe S n m h` — the iterated section `S.component n → S.component m` (`n ≤ m`);
* `leg S n m` — the pairing of the two, i.e. the `m`-th leg of the cone of `σ_n`;
* `coneOf S n`, `sig S n := S.asLimit.lift (coneOf S n)` — the map `σ_n : S.component n ⟶ S`
  whose `m`-th coordinate is `leg S n m`;
* `e S n := sig S n ≫ S.proj n` — the endomorphism `e_n : S ⟶ S`.

The main results are `sig_proj : sig S n ≫ S.proj n = 𝟙 _` and the element-level
computations `proj_sig_apply` and `e_apply`.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed

noncomputable section

namespace Work.ATOM

variable (S : LightProfinite.{0})

/-- The finite components of a light profinite set carry the discrete topology (the corresponding
Mathlib instance is only local). -/
instance instDiscreteComponent (n : ℕ) : DiscreteTopology (S.component n) := ⟨rfl⟩

/-- A chosen section of the `n`-th transition map `S.component (n+1) ⟶ S.component n`. -/
noncomputable def sect (n : ℕ) : S.component n ⟶ S.component (n+1) :=
  ConcreteCategory.ofHom ⟨Function.surjInv (S.surjective_transitionMap n),
    continuous_of_discreteTopology⟩

lemma sect_transitionMap (n : ℕ) : sect S n ≫ S.transitionMap n = 𝟙 (S.component n) := by
  ext x
  exact Function.surjInv_eq _ _

/-- The iterated section: the map `S.component n ⟶ S.component m` (`n ≤ m`) obtained by
composing the chosen sections. -/
noncomputable def itSe (n m : ℕ) (h : n ≤ m) : S.component n ⟶ S.component m :=
  Nat.leRecOn (C := fun k => S.component n ⟶ S.component k) h (fun {k} ih => ih ≫ sect S k) (𝟙 _)

lemma itSe_succ (n m : ℕ) (h : n ≤ m) :
    itSe S n (m+1) (Nat.le_succ_of_le h) = itSe S n m h ≫ sect S m := by
  unfold itSe
  rw [Nat.leRecOn_succ]

lemma itSe_self (n : ℕ) : itSe S n n (le_refl n) = 𝟙 (S.component n) := by
  unfold itSe
  rw [Nat.leRecOn_self]

/-- The iterated transition: the projection `S.component n ⟶ S.component m` (`m ≤ n`). -/
noncomputable def itTr (n m : ℕ) (h : m ≤ n) : S.component n ⟶ S.component m :=
  S.diagram.map (homOfLE h).op

lemma itTr_self (n : ℕ) : itTr S n n (le_refl n) = 𝟙 (S.component n) := by
  unfold itTr
  rw [Subsingleton.elim (homOfLE (le_refl n)).op (𝟙 (Opposite.op n))]
  exact S.diagram.map_id _

lemma itTr_comp_transition (n m : ℕ) (h : m+1 ≤ n) :
    itTr S n (m+1) h ≫ S.transitionMap m = itTr S n m (le_trans (Nat.le_succ m) h) := by
  unfold itTr LightProfinite.transitionMap
  rw [← S.diagram.map_comp]
  congr 1

/-- The full set of legs: `leg S n m : S.component n ⟶ S.component m`. -/
noncomputable def leg (n m : ℕ) : S.component n ⟶ S.component m :=
  if h : m ≤ n then itTr S n m h else itSe S n m (le_of_lt (Nat.not_le.mp h))

lemma leg_of_le (n m : ℕ) (h : m ≤ n) : leg S n m = itTr S n m h := by
  rw [leg]
  exact dif_pos h

lemma leg_of_ge (n m : ℕ) (h : n ≤ m) : leg S n m = itSe S n m h := by
  rw [leg]
  split_ifs with h'
  · have hnm : n = m := le_antisymm h h'
    subst hnm
    rw [Subsingleton.elim h' (le_refl n), Subsingleton.elim h (le_refl n), itTr_self, itSe_self]
  · rfl

/-- The cone condition for the legs, in successor form. -/
lemma leg_succ (n m : ℕ) : leg S n (m+1) ≫ S.transitionMap m = leg S n m := by
  by_cases h : m + 1 ≤ n
  · rw [leg_of_le S n (m+1) h, leg_of_le S n m (le_trans (Nat.le_succ m) h), itTr_comp_transition]
  · have h2 : n ≤ m := by omega
    rw [leg_of_ge S n m h2, leg_of_ge S n (m+1) (by omega), itSe_succ, Category.assoc,
      sect_transitionMap S m, Category.comp_id]

/-- The cone over `S.diagram` with cone point `S.component n` whose `m`-th leg is `leg S n m`. -/
noncomputable def coneOf (n : ℕ) : Cone S.diagram where
  pt := S.component n
  π := NatTrans.ofOpSequence (fun m => leg S n m) (fun m => (leg_succ S n m).symm)

/-- `σ_n : S.component n ⟶ S`. -/
noncomputable def sig (n : ℕ) : S.component n ⟶ S :=
  S.asLimit.lift (coneOf S n)

/-- Element-level description of the projections of `σ_n`. -/
lemma proj_sig_apply (n m : ℕ) (t : S.component n) : S.proj m (sig S n t) = leg S n m t := by
  rw [← ConcreteCategory.comp_apply (f := sig S n) (g := S.proj m) (x := t)]
  exact congrArg (fun (f : S.component n ⟶ S.component m) => (ConcreteCategory.hom f) t)
    (S.asLimit.fac (coneOf S n) ⟨m⟩)

lemma sig_proj_apply (n : ℕ) (t : S.component n) : S.proj n (sig S n t) = t := by
  rw [proj_sig_apply S n n t, leg_of_le S n n le_rfl, itTr_self]
  rfl

lemma sig_proj (n : ℕ) : sig S n ≫ S.proj n = 𝟙 (S.component n) := by
  apply ConcreteCategory.hom_ext
  intro t
  rw [ConcreteCategory.comp_apply, proj_sig_apply, leg_of_le S n n le_rfl, itTr_self]

/-- `e_n : S ⟶ S`, the idempotent `σ_n ∘ π_n` (i.e. `π_n` followed by `σ_n`). -/
noncomputable def e (n : ℕ) : S ⟶ S := S.proj n ≫ sig S n

lemma e_apply (n : ℕ) (x : S) : e S n x = sig S n (S.proj n x) := by
  rw [e, ConcreteCategory.comp_apply]

/-- `A n := e_n '' univ`, the image of the `n`-th idempotent. -/
def A (n : ℕ) : Set S := Set.range (e S n)

/-- `B 0 := A 0` and `B n := A n \ A (n-1)` for `n ≥ 1`: the "new points at level `n`". -/
def B (n : ℕ) : Set S := if n = 0 then A S 0 else A S n \ A S (n-1)

end Work.ATOM
