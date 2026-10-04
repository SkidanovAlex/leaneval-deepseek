import Mathlib
import Submission.Work.Diff.Alg.Pinch.Q2Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The index identity `E2 = S2`

`Work.Diff.Alg.Pinch.Q2Defs` expands the two sides of

`Phi (Q2 R) X (bar X) = (Tmat R X * Rm R).trace`

into explicit sums `S1, S2` (left-hand side) and `E1, E2, E3, E4` (right-hand side).
The present file proves `E2 R X = S2 R X` for an algebraic curvature tensor `R`.

In components (`R i j k l = ⟪R(eᵢ,eⱼ)eₗ, eₖ⟫`),

* `E2 R X = ∑ i j k l a d, R i j k l · R k d a j · conj (X (i,a)) · X (d,l)`;
* `S2 R X = ∑ i j k l p q, R i p l q · R j p k q · X (i,j) · conj (X (k,l))`.

Unlike the companion identities `E1 = S1`, `E4 = S1`, this one is *not* a single
relabelling of the six summation indices: the two sums share a common middle term

* `M  R X = ∑ i j k l a d, R l k i j · R d k a j · X (d,l) · conj (X (i,a))`,
* `M' R X = ∑ i j k l a d, R l k i j · R d k a j · X (l,d) · conj (X (a,i))`,

namely

* `E2 = M`  pointwise, using `R i j k l = - R l k i j` and `R k d a j = - R d k a j`
  (antisymmetry in the first pair together with pair symmetry) and commutativity in `ℂ`;
* `S2 = M'` by the coordinate relabelling `(i,j,k,l,p,q) ↦ (l,d,a,i,k,j)`;
* `M' = M`  by the involution `(i,a,d,l) ↦ (a,i,l,d)`, which exchanges the two `R`
  factors and turns `X (l,d) · conj (X (a,i))` into `X (d,l) · conj (X (i,a))`.

Everything is realised as a permutation of the six coordinates of
`(Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n)`, so the reindexings are
`Equiv.sum_comp`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The index type of the flattened sums: three pairs. -/
private abbrev P (n : ℕ) := (Fin n × Fin n) × (Fin n × Fin n) × (Fin n × Fin n)

/-- `E2` flattened to a sum over three pairs `(i,j)`, `(k,l)`, `(a,d)`. -/
private def e2F {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) : P n → ℂ :=
  fun x => (R x.1.1 x.1.2 x.2.1.1 x.2.1.2 : ℂ) * (R x.2.1.1 x.2.2.2 x.2.2.1 x.1.2 : ℂ)
    * bar X (x.1.1, x.2.2.1) * X (x.2.2.2, x.2.1.2)

/-- The common middle term `M` flattened. -/
private def mF {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) : P n → ℂ :=
  fun x => (R x.2.1.2 x.2.1.1 x.1.1 x.1.2 : ℂ) * (R x.2.2.2 x.2.1.1 x.2.2.1 x.1.2 : ℂ)
    * X (x.2.2.2, x.2.1.2) * bar X (x.1.1, x.2.2.1)

/-- The relabelled middle term `M'` flattened. -/
private def mF' {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) : P n → ℂ :=
  fun x => (R x.2.1.2 x.2.1.1 x.1.1 x.1.2 : ℂ) * (R x.2.2.2 x.2.1.1 x.2.2.1 x.1.2 : ℂ)
    * X (x.2.1.2, x.2.2.2) * bar X (x.2.2.1, x.1.1)

/-- `S2` flattened to a sum over three pairs `(i,j)`, `(k,l)`, `(p,q)`. -/
private def s2F {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) : P n → ℂ :=
  fun x => (R x.1.1 x.2.2.1 x.2.1.2 x.2.2.2 : ℂ) * (R x.1.2 x.2.2.1 x.2.1.1 x.2.2.2 : ℂ)
    * X (x.1.1, x.1.2) * bar X (x.2.1.1, x.2.1.2)

/-- The coordinate permutation realising `S2 = M'`, as an involution:
with `x = ((i,j),(k,l),(p,q))` it sends `(p,q)` to `(l,i)` etc.  Concretely the
permutation of the six slots is `(1 4)(2 6)(3 5)`. -/
private def sig {n : ℕ} : P n → P n :=
  fun x => ((x.2.1.2, x.2.2.2), (x.2.2.1, x.1.1), (x.2.1.1, x.1.2))

/-- `sig` packaged as an equivalence (it is an involution). -/
private def sigEquiv {n : ℕ} : P n ≃ P n :=
  ⟨sig, sig, by rintro ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩⟩; rfl,
    by rintro ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩⟩; rfl⟩

/-- The coordinate permutation realising `M' = M`, as an involution: it swaps
`i ↔ a` and `d ↔ l`, i.e. the permutation of the six slots `(1 5)(4 6)`. -/
private def tau {n : ℕ} : P n → P n :=
  fun x => ((x.2.2.1, x.1.2), (x.2.1.1, x.2.2.2), (x.1.1, x.2.1.2))

/-- `tau` packaged as an equivalence (it is an involution). -/
private def tauEquiv {n : ℕ} : P n ≃ P n :=
  ⟨tau, tau, by rintro ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩⟩; rfl,
    by rintro ⟨⟨a, b⟩, ⟨c, d⟩, ⟨e, f⟩⟩; rfl⟩

/-- `E2` as a sum over three pairs of indices. -/
private lemma E2_flat {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) :
    E2 R X = ∑ x, e2F R X x := by
  simp only [E2, e2F, Fintype.sum_prod_type]

/-- `S2` as a sum over three pairs of indices. -/
private lemma S2_flat {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) :
    S2 R X = ∑ x, s2F R X x := by
  simp only [S2, s2F, Fintype.sum_prod_type]

/-- The pointwise identity `e2F = mF`, using the two curvature symmetries. -/
private lemma e2F_eq_mF {n : ℕ} (R : Curv4 n) (hR : IsAlgCurv R) (X : Fin n × Fin n → ℂ)
    (x : P n) : e2F R X x = mF R X x := by
  have h1 : (R x.1.1 x.1.2 x.2.1.1 x.2.1.2 : ℂ)
      = - (R x.2.1.2 x.2.1.1 x.1.1 x.1.2 : ℂ) := by
    have hreal : R x.1.1 x.1.2 x.2.1.1 x.2.1.2 = - R x.2.1.2 x.2.1.1 x.1.1 x.1.2 := by
      rw [← hR.2.1 x.1.1 x.1.2 x.2.1.1 x.2.1.2, hR.1 x.2.1.2 x.2.1.1 x.1.1 x.1.2]
    exact_mod_cast hreal
  have h2 : (R x.2.1.1 x.2.2.2 x.2.2.1 x.1.2 : ℂ)
      = - (R x.2.2.2 x.2.1.1 x.2.2.1 x.1.2 : ℂ) := by
    have hreal : R x.2.1.1 x.2.2.2 x.2.2.1 x.1.2 = - R x.2.2.2 x.2.1.1 x.2.2.1 x.1.2 :=
      hR.1 x.2.2.2 x.2.1.1 x.2.2.1 x.1.2
    exact_mod_cast hreal
  simp only [e2F, mF]
  rw [h1, h2]
  ring

/-- The pointwise identity `s2F = mF' ∘ sig`, by definition of `sig`. -/
private lemma s2F_eq_sig {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) (x : P n) :
    s2F R X x = mF' R X (sig x) := by
  simp only [s2F, mF', sig]

/-- The pointwise identity `mF' = mF ∘ tau`, by commutativity in `ℂ`. -/
private lemma mF'_eq_tau {n : ℕ} (R : Curv4 n) (X : Fin n × Fin n → ℂ) (x : P n) :
    mF' R X x = mF R X (tau x) := by
  simp only [mF', mF, tau]
  ring

theorem E2_eq_S2 (n : ℕ) (R : Submission.Diff.Alg.Curv4 n) (hR : Submission.Diff.Alg.IsAlgCurv R)
    (X : Fin n × Fin n → ℂ) :
    Work.Diff.Alg.Pinch.E2 R X = Work.Diff.Alg.Pinch.S2 R X := by
  rw [E2_flat R X, S2_flat R X]
  have hE : (∑ x, e2F R X x) = ∑ x, mF R X x :=
    Finset.sum_congr rfl (fun x _ => e2F_eq_mF R hR X x)
  have hS : (∑ x, s2F R X x) = ∑ x, mF R X x := by
    calc (∑ x, s2F R X x)
        = ∑ x, mF' R X (sigEquiv x) := Finset.sum_congr rfl (fun x _ => s2F_eq_sig R X x)
      _ = ∑ y, mF' R X y := Equiv.sum_comp (sigEquiv (n := n)) (mF' R X)
      _ = ∑ y, mF R X (tauEquiv y) := Finset.sum_congr rfl (fun y _ => mF'_eq_tau R X y)
      _ = ∑ y, mF R X y := Equiv.sum_comp (tauEquiv (n := n)) (mF R X)
  rw [hE, hS]

end Work.Diff.Alg.Pinch
