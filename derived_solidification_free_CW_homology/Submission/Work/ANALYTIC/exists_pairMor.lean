import Mathlib
import Submission.Work.ATOM.ZS.Topo.Defs
import Submission.Work.ATOM.Defs

namespace Work.ANALYTIC

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid

noncomputable section

/-!
# The truncation map `(ℕ∪{∞})² ⟶ ℕ∪{∞}`

We construct the continuous map (equivalently a morphism of light profinite sets)
`(k,j) ↦ j` if `k ≤ j` (both finite), `↦ ∞` otherwise; so both `∞`-axes are sent to `∞`.
This is the topological input for the primed family `F' : P ⊗ P ⟶ P` of `REFS/03` §2.

We first do the work on the underlying product type `↥(ℕ∪{∞}) × ↥(ℕ∪{∞})`, where all the
set-theoretic manipulations are syntactically well typed, and then transfer to the tensor product
`(ℕ∪{∞}) ⊗ (ℕ∪{∞})` (whose underlying type is that product type by definition).
-/

/-- The underlying function of the truncation map, on the product type. -/
def pairFunP (p : ↥(ℕ∪{∞}) × ↥(ℕ∪{∞})) : ℕ∪{∞} :=
  p.1.elim (∞ : ℕ∪{∞}) (fun k => p.2.elim (∞ : ℕ∪{∞})
    (fun j => if k ≤ j then (j : ℕ∪{∞}) else ∞))

@[simp] theorem pairFunP_finite (k j : ℕ) :
    pairFunP ((k : ℕ∪{∞}), (j : ℕ∪{∞})) = if k ≤ j then (j : ℕ∪{∞}) else ∞ := rfl

@[simp] theorem pairFunP_infty_fst (j : ℕ∪{∞}) : pairFunP ((∞ : ℕ∪{∞}), j) = ∞ := by
  cases j with
  | none => rfl
  | some j => rfl

@[simp] theorem pairFunP_infty_snd (k : ℕ∪{∞}) : pairFunP (k, (∞ : ℕ∪{∞})) = ∞ := by
  cases k with
  | none => rfl
  | some k => rfl

/-- The fibre of `pairFunP` over a finite value `n`: exactly the points `(k,n)` with `k ≤ n`. -/
theorem pairFunP_eq_some_iff (n : ℕ) (p : ↥(ℕ∪{∞}) × ↥(ℕ∪{∞})) :
    pairFunP p = (n : ℕ∪{∞}) ↔
      ∃ k : ℕ, k ≤ n ∧ p = ((k : ℕ∪{∞}), (n : ℕ∪{∞})) := by
  have key : ∀ k m : ℕ,
      pairFunP ((k : ℕ∪{∞}), (m : ℕ∪{∞})) = (n : ℕ∪{∞}) ↔
        ∃ k' : ℕ, k' ≤ n ∧
          ((k : ℕ∪{∞}), (m : ℕ∪{∞})) = ((k' : ℕ∪{∞}), (n : ℕ∪{∞})) := by
    intro k m
    rw [pairFunP_finite]
    by_cases h : k ≤ m
    · rw [if_pos h]
      constructor
      · intro hj
        have hmn : m = n := by simpa using hj
        exact ⟨k, hmn ▸ h, Prod.ext rfl hj⟩
      · rintro ⟨k', _hk', he⟩
        simpa using congrArg Prod.snd he
    · rw [if_neg h]
      constructor
      · intro hc
        exact absurd hc (OnePoint.infty_ne_coe n)
      · rintro ⟨k', hk', he⟩
        have hkk : k = k' := by simpa using congrArg Prod.fst he
        have hmn : m = n := by simpa using congrArg Prod.snd he
        exact absurd (hkk ▸ hmn ▸ hk') h
  by_cases h1 : p.1 = (∞ : ℕ∪{∞})
  · have hp : p = ((∞ : ℕ∪{∞}), p.2) := Prod.ext h1 rfl
    rw [hp, pairFunP_infty_fst]
    refine ⟨fun hc => absurd hc (OnePoint.infty_ne_coe n), ?_⟩
    rintro ⟨x, -, hx⟩
    exact absurd (congrArg Prod.fst hx) (OnePoint.infty_ne_coe x)
  · obtain ⟨k, hk⟩ := OnePoint.ne_infty_iff_exists.mp h1
    have hp : p = ((k : ℕ∪{∞}), p.2) := Prod.ext hk.symm rfl
    rw [hp]
    by_cases h2 : p.2 = (∞ : ℕ∪{∞})
    · rw [h2, pairFunP_infty_snd]
      refine ⟨fun hc => absurd hc (OnePoint.infty_ne_coe n), ?_⟩
      rintro ⟨x, -, hx⟩
      have h : (∞ : ℕ∪{∞}) = (n : ℕ∪{∞}) := by
        simpa using congrArg Prod.snd hx
      exact absurd h (OnePoint.infty_ne_coe n)
    · obtain ⟨m, hm⟩ := OnePoint.ne_infty_iff_exists.mp h2
      rw [← hm]
      exact key k m

/-- Continuity of the truncation map on the product type, by the criterion
`Work.ATOM.continuous_onePoint_iff_isClopen`: the fibre over a finite point `n` is the clopen set
`{k | k ≤ n} × {n}`, a finite union of products of clopen singletons. -/
theorem pairFunP_continuous : Continuous pairFunP := by
  rw [Work.ATOM.continuous_onePoint_iff_isClopen]
  intro n
  have hset : pairFunP ⁻¹' {(n : ℕ∪{∞})} =
      ⋃ k ∈ Set.Iic n,
        (({(k : ℕ∪{∞})} : Set ↥(ℕ∪{∞})) ×ˢ ({(n : ℕ∪{∞})} : Set ↥(ℕ∪{∞}))) := by
    ext p
    rw [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion₂]
    simp only [Set.mem_Iic, Set.mem_prod, Set.mem_singleton_iff, exists_prop]
    constructor
    · intro hp
      obtain ⟨k, hk, hpe⟩ := (pairFunP_eq_some_iff n p).mp hp
      exact ⟨k, hk, congrArg Prod.fst hpe, congrArg Prod.snd hpe⟩
    · rintro ⟨k, hk, h1, h2⟩
      exact (pairFunP_eq_some_iff n p).mpr ⟨k, hk, Prod.ext h1 h2⟩
  rw [hset]
  exact Set.Finite.isClopen_biUnion (Set.finite_Iic n) fun k _ =>
    (Work.ATOM.isClopen_singleton_some k).prod (Work.ATOM.isClopen_singleton_some n)

/-- The underlying function of the truncation map `(ℕ∪∞)² ⟶ ℕ∪∞`, on the light profinite set
`(ℕ∪{∞}) ⊗ (ℕ∪{∞})`. -/
def pairFun (p : ↥(Work.ATOM.NS2)) : ℕ∪{∞} := pairFunP (p.1, p.2)

@[simp] theorem pairFun_finite (k j : ℕ) :
    pairFun ⟨(k : ℕ∪{∞}), (j : ℕ∪{∞})⟩ = if k ≤ j then (j : ℕ∪{∞}) else ∞ :=
  pairFunP_finite k j

@[simp] theorem pairFun_infty_fst (j : ℕ∪{∞}) : pairFun ⟨(∞ : ℕ∪{∞}), j⟩ = ∞ :=
  pairFunP_infty_fst j

@[simp] theorem pairFun_infty_snd (k : ℕ∪{∞}) : pairFun ⟨k, (∞ : ℕ∪{∞})⟩ = ∞ :=
  pairFunP_infty_snd k

/-- Continuity of the truncation map, transferred from the product type. -/
theorem pairFun_continuous : Continuous pairFun :=
  pairFunP_continuous.comp continuous_id

/-- The map `(ℕ∪∞)² ⟶ ℕ∪∞` of light profinite sets induced by `pairFun`. -/
def pairMor : Work.ATOM.NS2 ⟶ ℕ∪{∞} :=
  ConcreteCategory.ofHom ⟨pairFun, pairFun_continuous⟩

@[simp] theorem pairMor_apply (p : ↥(Work.ATOM.NS2)) : pairMor p = pairFun p := rfl

/-- **The "truncation in the second variable" map `(ℕ∪∞)² ⟶ ℕ∪∞`.**  The continuous map
sending a pair of finite integers `(k,j)` with `k ≤ j` to `j` and every other point to `∞`
(so both `∞`-axes are mapped to `∞`).  It is the topological input for the primed family
`F' : P ⊗ P ⟶ P`, `(k,e_j) ↦ e_j` if `k ≤ j`, of REFS/03 §2.  Continuity follows from the
criterion `Work.ATOM.continuous_onePoint_iff_isClopen`: the fibres over finite points are the
finite sets `{(k,n) : k ≤ n}`, which are clopen (each `{(k,n)} = {k} × {n}` is a product of
clopen singletons; cf. the scratch file `Submission/Work/ANALYTIC/_cbe_pair.lean`, whose
`pairFun`/`pairMor` are meant to be this map, but whose set-theoretic proof steps are incomplete). -/
theorem exists_pairMor :
    ∃ g : (ℕ∪{∞}) ⊗ (ℕ∪{∞}) ⟶ ℕ∪{∞},
      (∀ k j : ℕ, g ⟨(k : ℕ∪{∞}), (j : ℕ∪{∞})⟩ = if k ≤ j then (j : ℕ∪{∞}) else ∞) ∧
      (∀ j : ℕ∪{∞}, g ⟨(∞ : ℕ∪{∞}), j⟩ = ∞) ∧
      (∀ k : ℕ∪{∞}, g ⟨k, (∞ : ℕ∪{∞})⟩ = ∞) := by
  refine ⟨pairMor, ?_, ?_, ?_⟩
  · intro k j
    exact pairFun_finite k j
  · intro j
    exact pairFun_infty_fst j
  · intro k
    exact pairFun_infty_snd k

end

end Work.ANALYTIC
