import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.theta_window` — the excited window has an explicit inhabitant

FS §8's model Hamiltonian is the second quantisation of the honest box datum on the
Fock space `RealFock m` (`(Fin m →₀ ℕ) →₀ ℝ`, monomial-coefficient model) with the
condensate mode `0 : Fin m` singled out (`Submission/Work/BoseBoxFock/Defs.lean`).
The `§9`–`§10` gate `RB67FS` — and the intermediate `box_to_model` / `model_kafz`
statements — quantifies over vectors `Ψ ≠ 0` lying in the **window**

`ExcWindow M n Ψ` := `Ψ` is a finite sum of `n₊`-eigenvectors with eigenvalues `≤ 𝓜`,
and has at most `n` particles,

where `n₊ = nExc = totNumOp m − n₀` is the **excited** number operator (all particles
outside the condensate).  A statement quantified over an empty window would be
vacuous, so one owes an explicit witness.

The natural witness is the Fock state with `n₀` particles **all in the condensate**,

`Ψ = Finsupp.single (Finsupp.single (0 : Fin m) n₀) 1`,

i.e. the basis vector at the multi-index `α₀ = n₀·e₀`.  It satisfies `n₊Ψ = 0` (it is a
`0`-eigenvector, because `totNumOp` and `n₀` both act on it by the scalar `n₀`), and its
particle number is `α₀.sum (fun _ k => k) = n₀ ≤ n`.  Hence `Ψ ∈ ExcWindow M n` for
*every* threshold `M` and every `n ≥ n₀`: the threshold plays no role, since
`0 ∈ Finset.range (⌊M⌋₊ + 1)` always, so the `j = 0` term of the decomposition absorbs
the whole vector (`M` may even be negative).

Main contents:

* `ann_single_theta` — annihilation on a basis vector (`Work.BoseB4.cre_single` is the
  creation counterpart), and the index identity `sub_e_add_e_theta`
  `(α − e_l) + e_l = α`, valid when `α l ≠ 0`;
* `modeNumOp_single` — `n_l Ψ = (α l) • Ψ` for the basis vector at `α`;
* `n0_single`, `totNumOp_single` — the same for the two number operators appearing in
  `nExc`;
* `theta_window` — the window membership.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false

/-! ## 1. The ladder operators on a basis vector

The monomial-coefficient model acts on the basis vectors `Finsupp.single α b` by
`a_l Ψ = (α l) · Ψ_{α − e_l}` and `a_l† Ψ_α = Ψ_{α + e_l}`; the technical point is
that the multi-index subtraction is truncated, so `(α − e_l) + e_l = α` only when
`α l ≠ 0` — but in the other case the scalar factor `(α l) = 0` kills the term anyway. -/

/-- Annihilation on a basis vector: it lowers the `l`-th occupation and multiplies by it. -/
private lemma ann_single_theta {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) (b : ℝ) :
    ann m l (Finsupp.single α b) = Finsupp.single (α - e m l) ((α l : ℝ) * b) := by
  simp only [ann, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply, Finsupp.smul_single,
    smul_eq_mul, one_mul, mul_comm]

/-- `(α − e_l) + e_l = α` whenever `α l ≠ 0` (the truncated subtraction is undone by the
addition as soon as the `l`-th occupation is nonzero). -/
private lemma sub_e_add_e_theta {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) (h : α l ≠ 0) :
    (α - e m l) + e m l = α := by
  ext i
  by_cases hi : i = l
  · subst hi
    simp [Finsupp.add_apply, e]
    omega
  · simp [Finsupp.add_apply, e, hi]

/-- **The mode number operator on a basis vector.**  `n_l = a_l†a_l = modeNumOp m l`
acts on the basis vector at the multi-index `α` by the scalar `α l`, the `l`-th
occupation number. -/
theorem modeNumOp_single {m : ℕ} (l : Fin m) (α : Fin m →₀ ℕ) :
    modeNumOp m l (Finsupp.single α (1 : ℝ)) = (α l : ℝ) • Finsupp.single α (1 : ℝ) := by
  rw [modeNumOp, LinearMap.comp_apply, ann_single_theta, Work.BoseB4.cre_single]
  by_cases h : α l = 0
  · rw [h]; simp
  · rw [sub_e_add_e_theta l α h]
    simp

/-! ## 2. The two number operators of `nExc` on the condensate state -/

/-- **The condensate number operator `n₀ = a₀†a₀` on a basis vector.** -/
theorem n0_single {m : ℕ} [NeZero m] (α : Fin m →₀ ℕ) :
    n0 (m := m) (Finsupp.single α (1 : ℝ)) = (α 0 : ℝ) • Finsupp.single α (1 : ℝ) := by
  rw [show n0 (m := m) = Work.BoseB4.modeNumOp m (0 : Fin m) from rfl]
  exact modeNumOp_single 0 α

/-- **The total number operator `N = ∑_l a_l†a_l` on a basis vector.**  It multiplies by
the total occupation `∑_l α l`. -/
theorem totNumOp_single {m : ℕ} (α : Fin m →₀ ℕ) :
    totNumOp m (Finsupp.single α (1 : ℝ))
      = (∑ i : Fin m, ((α i : ℕ) : ℝ)) • Finsupp.single α (1 : ℝ) := by
  rw [totNumOp]
  simp only [LinearMap.sum_apply]
  rw [Finset.sum_congr rfl (fun i _ => modeNumOp_single i α), ← Finset.sum_smul]

/-! ## 3. The window membership -/

/-- **The excited window is inhabited at every threshold.**  For every `M : ℝ` and every
`n₀ ≤ n`, the Fock state with `n₀` particles in the condensate mode `0` and none outside
lies in `ExcWindow M n`: it is a `0`-eigenvector of the excited number operator
`n₊ = N − n₀` (so the decomposition of the window may be taken to be
`φ 0 = Ψ`, `φ j = 0` for `j ≠ 0`), and its particle number is `n₀ ≤ n`. -/
theorem theta_window {m : ℕ} [NeZero m] (M : ℝ) {n n₀ : ℕ} (hn : n₀ ≤ n) : Work.BoseBoxFock.ExcWindow M n (Finsupp.single (Finsupp.single (0 : Fin m) n₀) (1 : ℝ)) := by
  -- (the statement is verbatim the one requested; `Work.BoseBoxFock.ExcWindow` is
  --  `ExcWindow` of this namespace and is left fully qualified on purpose)
  -- the multi-index `α₀ = n₀·e₀` and the basis vector `Ψ` on it
  set α₀ : Fin m →₀ ℕ := Finsupp.single (0 : Fin m) n₀ with hα₀
  set Ψ : RealFock m := Finsupp.single α₀ (1 : ℝ) with hΨ
  have hα₀zero : α₀ 0 = n₀ := Finsupp.single_eq_same
  have hsum : (∑ i : Fin m, ((α₀ i : ℕ) : ℝ)) = (n₀ : ℝ) := by
    rw [hα₀, Finset.sum_eq_single 0]
    · simp
    · intro b _ hb
      rw [Finsupp.single_eq_of_ne hb]; simp
    · intro h
      exact absurd (Finset.mem_univ (0 : Fin m)) h
  -- both `n₀` and `N` act on `Ψ` by the scalar `n₀`, hence `n₊Ψ = 0`
  have hn0 : n0 (m := m) Ψ = (n₀ : ℝ) • Ψ := by
    rw [hΨ, n0_single, hα₀zero]
  have htot : totNumOp m Ψ = (n₀ : ℝ) • Ψ := by
    rw [hΨ, totNumOp_single, hsum]
  have heig : nExc (m := m) Ψ = 0 := by
    rw [nExc, LinearMap.sub_apply, hn0, htot, sub_self]
  refine ⟨⟨fun j => if j = 0 then Ψ else 0, ?_, ?_⟩, ?_⟩
  · -- the decomposition `Ψ = φ 0 + 0 + …`: `φ 0 = Ψ` is a `0`-eigenvector, `φ j = 0` else
    intro j
    by_cases hj : j = 0
    · subst hj; simp [heig]
    · simp [hj]
  · -- the sum over `j ∈ range (⌊M⌋₊ + 1)` keeps only its `j = 0` term, which is `Ψ`
    have h1 : (∑ j ∈ Finset.range (⌊M⌋₊ + 1), (if j = 0 then Ψ else 0)) = Ψ := by
      rw [Finset.sum_eq_single_of_mem 0
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _)))]
      · simp
      · intro b _ hb; simp [hb]
    exact h1.symm
  · -- the particle-number condition: the support of `Ψ` is the singleton `{α₀}`
    intro α hα
    have hαmem : α ∈ ({(α₀)} : Finset (Fin m →₀ ℕ)) := by
      rw [hΨ] at hα
      rwa [Finsupp.support_single α₀ (by norm_num : (1 : ℝ) ≠ 0)] at hα
    have hαeq : α = α₀ := Finset.mem_singleton.mp hαmem
    rw [hαeq, hα₀]
    rw [Finsupp.sum_single_index (by simp : (fun _ (k : ℕ) => k) (0 : Fin m) 0 = 0)]
    exact hn

end Work.BoseBoxFock
