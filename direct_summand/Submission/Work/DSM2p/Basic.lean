import Submission.Work.DSMap.Mix

/-!
# DSM2p — André's flatness lemma in the Česnavičius–Scholze form: foundations

This module is the entry point of the subproject `Submission/Work/DSM2p/`, which owns the
mixed-characteristic node `DSMap.Mix.area_M2'` of the direct-summand project.

The mathematics is Česnavičius–Scholze, *Purity for flat cohomology* (arXiv:1912.10932), §1.3
(`approx-lem`, `nilp-lem`, `Andre-lem`) and §"Perfectoid rings" (`perfectoid-def`, `p-int-cl`,
`p-oid-rec`), together with André's original flatness lemma (arXiv:1609.00345, arXiv:1608.08882).

## Vocabulary introduced here

* `IsRootSystem p r` : `r : ℕ → B` is a *compatible system of `p`-power roots*, `r (k+1) ^ p = r k`.
* `HasCompatPRoots p x` : `x` admits such a system (i.e. `x` lies in the image of the tilting
  map `x ↦ x^♯` when `B` is perfectoid).
* `IsPIntegrallyClosedIn p R` : `R ≤ S` is *p-integrally closed* in `S`, meaning
  `x ^ p ∈ R → x ∈ R` for `x : S` (CS §p-int-cl).
* `pIntTower p R` / `pIntClosure p R` : the tower `R₀ = R`, `R_{n+1} = R_n[z : z ^ p ∈ R_n]`
  of CS §p-int-cl and its union, the *p-integral closure*: the smallest p-integrally closed
  subring of `S` containing `R`.
* `IsFrobIsoMod p ϖ` : the Frobenius `x ↦ x ^ p` induces an isomorphism `B/ϖ → B/ϖ^p`
  (this is the pair of conditions `frobSurj`/`frobInj` of `DSMap.PerfectoidData`, with the
  element `ϖ` explicit); by CS §perfectoid-def this is the practical recognition criterion for
  perfectoid rings.

## The road to `area_M2'`

See `DESIGN.md` in this directory for the dependency graph.  The headline lemmas are
`frobInj_of_pIntClosed` (CS `p-int-cl-lem`, injective direction) and its companions in
`pIntegral.lean`, and the construction of the cover in `Construction.lean`.
-/

open scoped Classical

namespace Work.DSM2p

universe u v

/-! ## Compatible systems of `p`-power roots -/

/-- `r` is a compatible system of `p`-power roots: `r (k+1) ^ p = r k` for all `k`. -/
def IsRootSystem {B : Type u} [CommRing B] (p : ℕ) (r : ℕ → B) : Prop :=
  ∀ k : ℕ, r (k + 1) ^ p = r k

/-- `x` admits a compatible system of `p`-power roots. -/
def HasCompatPRoots {B : Type u} [CommRing B] (p : ℕ) (x : B) : Prop :=
  ∃ r : ℕ → B, r 0 = x ∧ IsRootSystem p r

namespace HasCompatPRoots

variable {B : Type u} [CommRing B] {p : ℕ}

theorem one : HasCompatPRoots p (1 : B) :=
  ⟨fun _ => 1, rfl, by intro k; simp⟩

theorem zero (hp : 0 < p) : HasCompatPRoots p (0 : B) :=
  ⟨fun _ => 0, rfl, fun k => by rw [zero_pow hp.ne']⟩

theorem mul {x y : B} (hx : HasCompatPRoots p x) (hy : HasCompatPRoots p y) :
    HasCompatPRoots p (x * y) := by
  obtain ⟨r, rfl, hr⟩ := hx
  obtain ⟨s, rfl, hs⟩ := hy
  exact ⟨fun k => r k * s k, rfl, fun k => by rw [mul_pow, hr k, hs k]⟩

/-- The `k`-th member of a root system again has a root system. -/
theorem of_rootSystem {r : ℕ → B} (hr : IsRootSystem p r) (k : ℕ) :
    HasCompatPRoots p (r k) :=
  ⟨fun n => r (n + k), by simp, fun n => by
    have := hr (n + k)
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this⟩

end HasCompatPRoots

/-! ## p-integral closedness (CS §p-int-cl) -/

/-- `R ≤ S` is p-integrally closed in `S`: every `x : S` with `x ^ p ∈ R` lies in `R`. -/
def IsPIntegrallyClosedIn {S : Type u} [CommRing S] (p : ℕ) (R : Subring S) : Prop :=
  ∀ x : S, x ^ p ∈ R → x ∈ R

variable {S : Type u} [CommRing S]

/-- The p-integral closure tower: `R₀ = R`, `R_{n+1}` is generated over `R_n` by the elements
`z` of `S` with `z ^ p ∈ R_n`. -/
def pIntTower (p : ℕ) (R : Subring S) : ℕ → Subring S
  | 0 => R
  | n + 1 => pIntTower p R n ⊔ Subring.closure {x : S | x ^ p ∈ pIntTower p R n}

theorem pIntTower_succ (p : ℕ) (R : Subring S) (n : ℕ) :
    pIntTower p R (n + 1) =
      pIntTower p R n ⊔ Subring.closure {x : S | x ^ p ∈ pIntTower p R n} := rfl

theorem le_pIntTower (p : ℕ) (R : Subring S) (n : ℕ) : R ≤ pIntTower p R n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact ih.trans le_sup_left

theorem pIntTower_mono (p : ℕ) (R : Subring S) : Monotone (pIntTower p R) := by
  intro m n hmn
  induction hmn with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans le_sup_left

/-- The p-integral closure of `R` in `S`: the union of the tower; the smallest p-integrally
closed subring of `S` containing `R` (CS §p-int-cl). -/
def pIntClosure (p : ℕ) (R : Subring S) : Subring S where
  carrier := {x : S | ∃ n : ℕ, x ∈ pIntTower p R n}
  mul_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨max m n, mul_mem (pIntTower_mono p R (le_max_left m n) hm)
      (pIntTower_mono p R (le_max_right m n) hn)⟩
  one_mem' := ⟨0, R.one_mem⟩
  add_mem' := by
    rintro x y ⟨m, hm⟩ ⟨n, hn⟩
    exact ⟨max m n, add_mem (pIntTower_mono p R (le_max_left m n) hm)
      (pIntTower_mono p R (le_max_right m n) hn)⟩
  zero_mem' := ⟨0, R.zero_mem⟩
  neg_mem' := by
    rintro x ⟨n, hn⟩
    exact ⟨n, neg_mem hn⟩

theorem pIntTower_le_pIntClosure (p : ℕ) (R : Subring S) (n : ℕ) :
    pIntTower p R n ≤ pIntClosure p R := fun _ hx => ⟨n, hx⟩

theorem le_pIntClosure (p : ℕ) (R : Subring S) : R ≤ pIntClosure p R :=
  (le_pIntTower p R 0).trans (pIntTower_le_pIntClosure p R 0)

theorem mem_pIntClosure_iff (p : ℕ) (R : Subring S) (x : S) :
    x ∈ pIntClosure p R ↔ ∃ n : ℕ, x ∈ pIntTower p R n := Iff.rfl

/-- The p-integral closure is p-integrally closed. -/
theorem pIntClosure_isPIntegrallyClosed (p : ℕ) (R : Subring S) :
    IsPIntegrallyClosedIn p (pIntClosure p R) := by
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have h : Subring.closure {x : S | x ^ p ∈ pIntTower p R n} ≤
      pIntTower p R n ⊔ Subring.closure {x : S | x ^ p ∈ pIntTower p R n} := le_sup_right
  exact ⟨n + 1, h (Subring.subset_closure (by simpa using hn))⟩

/-- The p-integral closure is the *smallest* p-integrally closed subring containing `R`. -/
theorem pIntClosure_le {p : ℕ} {R C : Subring S} (hRC : R ≤ C)
    (hC : IsPIntegrallyClosedIn p C) : pIntClosure p R ≤ C := by
  have key : ∀ n : ℕ, pIntTower p R n ≤ C := by
    intro n
    induction n with
    | zero => exact hRC
    | succ n ih =>
      rw [pIntTower_succ]
      refine sup_le ih (Subring.closure_le.mpr ?_)
      intro y hy
      exact hC y (ih hy)
  rintro x ⟨n, hn⟩
  exact key n hn

/-! ## The Frobenius recognition criterion (CS §perfectoid-def, `p-oid-mod-pi`) -/

/-- **CS `p-oid-mod-pi`.**  The Frobenius `x ↦ x ^ p` induces an isomorphism `B/ϖ → B/ϖ^p`:
every element is a `p`-th power modulo `ϖ ^ p`, and `x ^ p ∈ (ϖ ^ p)` forces `x ∈ (ϖ)`.
For `ϖ` a nonzerodivisor with `ϖ ^ p ∈ B ^× · p` and `B` `ϖ`-adically complete, this is
equivalent to `B` being perfectoid (CS §perfectoid-def, final paragraph). -/
structure IsFrobIsoMod (p : ℕ) (B : Type u) [CommRing B] (ϖ : B) : Prop where
  /-- every element is a `p`-th power modulo `ϖ ^ p`. -/
  surj : ∀ x : B, ∃ y : B, x - y ^ p ∈ Ideal.span {ϖ ^ p}
  /-- `x ^ p ∈ (ϖ ^ p)` implies `x ∈ (ϖ)`. -/
  inj : ∀ x : B, x ^ p ∈ Ideal.span {ϖ ^ p} → x ∈ Ideal.span {ϖ}

end Work.DSM2p
