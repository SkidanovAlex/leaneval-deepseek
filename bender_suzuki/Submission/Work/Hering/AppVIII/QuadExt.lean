/-
# The quadratic extension `L = K[α]`, `α² = εα + 1`

Appendix VIII of Peterfalvi I (Prop. 3, p. 226) studies `Aut(B(n,1,ε))`.  The group
`B(n,1,ε)` is the central extension of `K = GF(2ⁿ)` by `K × K` with quadratic map
`q(a,b) = a² + εab + b²`, and the computation of `Aut` is done after identifying `K × K`
with the quadratic field extension `L = K[α]`, where `α² = εα + 1`.  Under this
identification `q` becomes the norm `x ↦ x·x̄` of `L/K`, whose value is the `|K|`-th power
`x ^ |K|` of `x`.

This file sets up that field extension (as `AdjoinRoot (X² + εX + 1)`) and its basic API:

* `Anisotropic ε` — the hypothesis of App. VIII Prop. 3: `a² + εab + b² = 0 → a = b = 0`;
* `QuadExt K ε` — the extension, a field when `ε` is anisotropic;
* `qalpha` — the adjoined root `α`, with `qalpha_sq : α * α = ε * α + 1`;
* `qbasis` — the `K`-basis `(1, α)`, and `exists_repr`: every element is `a + b·α`;
* `quadExt_natCard : Nat.card (QuadExt K ε) = Nat.card K ^ 2`.
-/
import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Polynomial Module

namespace Work.Hering.AppVIII

variable (K : Type*) [Field K] [CharP K 2]

/-- **Anisotropy** of `ε` (the hypothesis of App. VIII Prop. 3): the quadratic form
`(a,b) ↦ a² + εab + b²` vanishes only at `0`. -/
def Anisotropic (ε : K) : Prop :=
  ∀ a b : K, a * a + ε * (a * b) + b * b = 0 → a = 0 ∧ b = 0

/-- The polynomial `X ^ 2 + ε * X + 1` whose root generates the quadratic extension. -/
def quadPoly (ε : K) : K[X] := X ^ 2 + C ε * X + 1

/-- The quadratic extension `L = K[α]` of `K` with `α² = εα + 1`. -/
abbrev QuadExt (ε : K) : Type _ := AdjoinRoot (quadPoly K ε)

lemma quadPoly_ne_zero (ε : K) : quadPoly K ε ≠ 0 := by
  intro h
  have h2 : (quadPoly K ε).natDegree = 2 := by rw [quadPoly]; compute_degree!
  rw [h] at h2
  simp at h2

lemma quadPoly_natDegree (ε : K) : (quadPoly K ε).natDegree = 2 := by
  rw [quadPoly]; compute_degree!

lemma eps_ne_zero {ε : K} (h : Anisotropic K ε) : ε ≠ 0 := by
  intro h0
  have h1 := h 1 1 (by
    rw [h0]
    simp only [mul_one, zero_mul, add_zero, one_mul]
    exact CharTwo.add_self_eq_zero 1)
  exact one_ne_zero h1.2

lemma quadPoly_not_isRoot {ε : K} (h : Anisotropic K ε) (x : K) :
    ¬ (quadPoly K ε).IsRoot x := by
  rw [Polynomial.IsRoot, quadPoly]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_one]
  rw [pow_two]
  intro hx
  have h2 := h x 1 (by simpa using hx)
  exact one_ne_zero h2.2

/-- The anisotropy hypothesis makes `X² + εX + 1` irreducible, so `QuadExt K ε` is a field. -/
theorem quadPoly_irreducible {ε : K} (h : Anisotropic K ε) :
    Irreducible (quadPoly K ε) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ (quadPoly_not_isRoot K h)
  rw [Finset.mem_Icc, quadPoly_natDegree]
  norm_num

/-- Cardinality of `AdjoinRoot f` over a finite field: `|K[X]/(f)| = |K| ^ deg f`. -/
theorem natCard_adjoinRoot [Finite K] {f : K[X]} (hf : f ≠ 0) :
    Nat.card (AdjoinRoot f) = Nat.card K ^ f.natDegree := by
  haveI : Module.Finite K (AdjoinRoot f) :=
    @Finite.of_basis K (AdjoinRoot f) (Fin (AdjoinRoot.powerBasis hf).dim) _ _ _ _
      (AdjoinRoot.powerBasis hf).basis
  rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot f)]
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis hf), AdjoinRoot.powerBasis_dim hf]

/-- The quadratic extension has `|K|²` elements. -/
theorem quadExt_natCard [Finite K] (ε : K) :
    Nat.card (QuadExt K ε) = Nat.card K ^ 2 := by
  rw [natCard_adjoinRoot K (quadPoly_ne_zero K ε), quadPoly_natDegree]

/-- The adjoined root `α`, satisfying `α² = εα + 1`. -/
noncomputable def qalpha (ε : K) : QuadExt K ε := AdjoinRoot.root (quadPoly K ε)

/-- The `K`-basis `(1, α)` of the quadratic extension. -/
noncomputable def qbasis (ε : K) : Basis (Fin 2) K (QuadExt K ε) :=
  (AdjoinRoot.powerBasis (quadPoly_ne_zero K ε)).basis.reindex
    (finCongr (by
      rw [AdjoinRoot.powerBasis_dim (quadPoly_ne_zero K ε), quadPoly_natDegree]))

lemma qbasis_zero (ε : K) : qbasis K ε 0 = 1 := by
  rw [qbasis]
  simp only [Basis.reindex_apply, PowerBasis.basis_eq_pow]
  simp

lemma qbasis_one (ε : K) : qbasis K ε 1 = qalpha K ε := by
  rw [qbasis]
  simp only [Basis.reindex_apply, PowerBasis.basis_eq_pow]
  simp [qalpha]

/-- Every element of `L = K[α]` is `a + b·α` with `a b : K`. -/
theorem exists_repr (ε : K) (x : QuadExt K ε) :
    ∃ p : K × K,
      x = algebraMap K (QuadExt K ε) p.1 + algebraMap K (QuadExt K ε) p.2 * qalpha K ε := by
  refine ⟨((qbasis K ε).repr x 0, (qbasis K ε).repr x 1), ?_⟩
  have h := Basis.sum_repr (qbasis K ε) x
  rw [Fin.sum_univ_two, qbasis_zero, qbasis_one] at h
  calc x = ((qbasis K ε).repr x) 0 • (1 : QuadExt K ε)
        + ((qbasis K ε).repr x) 1 • qalpha K ε := h.symm
    _ = algebraMap K (QuadExt K ε) ((qbasis K ε).repr x 0)
        + algebraMap K (QuadExt K ε) ((qbasis K ε).repr x 1) * qalpha K ε := by
        simp only [Algebra.smul_def, mul_one]

/-- The defining relation of `α`: `α² = εα + 1`. -/
theorem qalpha_sq (ε : K) :
    qalpha K ε * qalpha K ε = algebraMap K (QuadExt K ε) ε * qalpha K ε + 1 := by
  have h0 : (AdjoinRoot.mk (quadPoly K ε)) (X ^ 2 + C ε * X + 1) = 0 := by
    have h := AdjoinRoot.mk_self (f := quadPoly K ε)
    rwa [quadPoly] at h
  simp only [map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_one] at h0
  rw [pow_two] at h0
  have hkey : qalpha K ε * qalpha K ε + algebraMap K (QuadExt K ε) ε * qalpha K ε + 1 = 0 := h0
  have h2 : qalpha K ε * qalpha K ε + (algebraMap K (QuadExt K ε) ε * qalpha K ε + 1) = 0 := by
    rwa [add_assoc] at hkey
  have h3 : algebraMap K (QuadExt K ε) ε * qalpha K ε + 1
      + (algebraMap K (QuadExt K ε) ε * qalpha K ε + 1) = 0 := by
    have h : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
    calc (algebraMap K (QuadExt K ε)) ε * qalpha K ε + 1
          + ((algebraMap K (QuadExt K ε)) ε * qalpha K ε + 1)
        = (1 : K) • ((algebraMap K (QuadExt K ε)) ε * qalpha K ε + 1)
          + (1 : K) • ((algebraMap K (QuadExt K ε)) ε * qalpha K ε + 1) := by simp
      _ = ((1 : K) + 1) • ((algebraMap K (QuadExt K ε)) ε * qalpha K ε + 1) :=
            (add_smul 1 1 _).symm
      _ = 0 := by rw [h, zero_smul]
  exact add_right_cancel (h2.trans h3.symm)

/-- `L` has characteristic two: every element is its own negative. -/
lemma quadExt_add_self (ε : K) (x : QuadExt K ε) : x + x = 0 := by
  have h : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  calc x + x = (1 : K) • x + (1 : K) • x := by simp
    _ = ((1 : K) + 1) • x := (add_smul 1 1 x).symm
    _ = 0 := by rw [h, zero_smul]

end Work.Hering.AppVIII
