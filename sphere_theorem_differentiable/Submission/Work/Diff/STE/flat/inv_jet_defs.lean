import Mathlib
import Submission.Work.Diff.STE.FlatPDE

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the inverse-matrix jet bounds (`Work.Diff.STE.flat.inv_jet_bound`)

The flat (torus) short-time-existence argument needs bounds for the derivatives of the entries of
the *inverse* of the metric matrix `reMat (seriesFunM c x)`, uniformly in the Galerkin truncation
`N` and in the coefficient family `c`, under the two hypotheses

* the level-`s` energy bound `ENormSqFull s (seriesFunM c) ≤ Bs ^ 2`, and
* uniform ellipticity of `reMat (seriesFunM c x)` with constant `lam > 0`.

The two structures that make this an instance of the Moser/composition estimate
(`CSq_comp_vecarg_le_local`) are recorded here:

* the "entry vector" map `z ↦ reMatZ z`, sending a complex vector indexed by
  `Fin (card (Fin n × Fin n))` (the Fourier-side stand-in for the `n²` entries of the matrix
  `seriesFunM c x`) to the real `n × n` matrix of its real parts;
* the open set `invNonsing n = {z | (reMatZ z).det ≠ 0}` on which the entry
  `z ↦ ((reMatZ z)⁻¹) c' d'` (`invPhi`) is smooth, and the compact set `invElliptic n lam ρ` of
  "elliptic" vectors, which is contained in `invNonsing n` as soon as `lam > 0`.
-/

open Matrix BigOperators

namespace Work.Diff.STE.flat

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- The identification of the `n²` matrix positions with `Fin (card (Fin n × Fin n))`, used to
feed the matrix entries into the vector-valued Moser estimate (which is stated for
`(Fin m → ℂ)`-valued arguments). -/
def invEv (n : ℕ) : Fin n × Fin n ≃ Fin (Fintype.card (Fin n × Fin n)) :=
  Fintype.equivFin _

/-- The real matrix built from a complex "entry vector" by taking real parts. -/
def reMatZ {n : ℕ} (z : Fin (Fintype.card (Fin n × Fin n)) → ℂ) : Fin n → Fin n → ℝ :=
  fun i j => (z (invEv n (i, j))).re

@[simp] lemma reMatZ_apply {n : ℕ} (z : Fin (Fintype.card (Fin n × Fin n)) → ℂ) (i j : Fin n) :
    reMatZ z i j = (z (invEv n (i, j))).re := rfl

/-- The open set of non-singular entry vectors: the domain of smoothness of the inverse. -/
def invNonsing (n : ℕ) : Set (Fin (Fintype.card (Fin n × Fin n)) → ℂ) :=
  {z | Matrix.det (Matrix.of (reMatZ z)) ≠ 0}

/-- The compact set of "elliptic" entry vectors: bounded in every coordinate, and with the
quadratic form of the real part bounded below by `lam * ‖v‖²`. -/
def invElliptic (n : ℕ) (lam ρ : ℝ) : Set (Fin (Fintype.card (Fin n × Fin n)) → ℂ) :=
  {z | (∀ i, ‖z i‖ ≤ ρ) ∧
    (∀ v : Fin n → ℝ,
      lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j, reMatZ z i j * v i * v j)}

/-- The `(c', d')`-entry of the inverse of the real matrix underlying a (Pi-typed) real matrix.
The argument is fed through `Matrix.of` so that the *matrix* inverse is used unambiguously. -/
def matInvEntry {n : ℕ} (A : Fin n → Fin n → ℝ) (c' d' : Fin n) : ℝ :=
  ((Matrix.of A)⁻¹ : Matrix (Fin n) (Fin n) ℝ) c' d'

/-- The `(c', d')`-entry of the inverse of the real part of the entry vector, as a function on the
entry-vector space.  This is the function whose composition with the series of a coefficient
family is controlled by the Moser estimate. -/
def invPhi (n : ℕ) (c' d' : Fin n) :
    (Fin (Fintype.card (Fin n × Fin n)) → ℂ) → ℂ :=
  fun z => ((matInvEntry (reMatZ z) c' d' : ℝ) : ℂ)

@[simp] lemma matInvEntry_apply {n : ℕ} (A : Fin n → Fin n → ℝ) (c' d' : Fin n) :
    matInvEntry A c' d' = ((Matrix.of A)⁻¹ : Matrix (Fin n) (Fin n) ℝ) c' d' := rfl

@[simp] lemma invPhi_apply {n : ℕ} (c' d' : Fin n)
    (z : Fin (Fintype.card (Fin n × Fin n)) → ℂ) :
    invPhi n c' d' z = ((matInvEntry (reMatZ z) c' d' : ℝ) : ℂ) := rfl

/-- The entry vector attached to a matrix-valued coefficient family: the `n²` complex-valued
coefficient families of its entries, re-indexed along `invEv`.  This is the vector of arguments to
which the Moser estimate (`CSq_comp_vecarg_le_local`) is applied. -/
def invCvec (n : ℕ) (c : (Fin n → ℤ) → Fin n → Fin n → ℂ) :
    (Fin n → ℤ) → (Fin (Fintype.card (Fin n × Fin n)) → ℂ) :=
  fun k i => c k (((invEv n).symm i).1) (((invEv n).symm i).2)

@[simp] lemma invCvec_apply {n : ℕ} (c : (Fin n → ℤ) → Fin n → Fin n → ℂ) (k : Fin n → ℤ)
    (i : Fin (Fintype.card (Fin n × Fin n))) :
    invCvec n c k i = c k (((invEv n).symm i).1) (((invEv n).symm i).2) := rfl

/-- The entry function of the matrix series of a coefficient family, at the index corresponding to
`i`, is the series of the corresponding entry family. -/
@[simp] lemma seriesFun_invCvec {n : ℕ} (c : (Fin n → ℤ) → Fin n → Fin n → ℂ) (k : Fin n → ℤ)
    (i : Fin (Fintype.card (Fin n × Fin n))) (x : Fin n → ℝ) :
    Work.Diff.STE.seriesFun (fun k => invCvec n c k i) x
      = Work.Diff.STE.Flat.seriesFunM c x ((invEv n).symm i).1 ((invEv n).symm i).2 := rfl

/-- Building the real matrix out of the entry vector of `seriesFunM c` recovers `reMat`. -/
lemma reMatZ_invCvec {n : ℕ} (c : (Fin n → ℤ) → Fin n → Fin n → ℂ) (x : Fin n → ℝ) :
    reMatZ (fun i => Work.Diff.STE.seriesFun (fun k => invCvec n c k i) x)
      = Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) := by
  funext i j
  simp only [reMatZ, Work.Diff.STE.Flat.reMat, Work.Diff.STE.Flat.seriesFunM_apply,
    invCvec_apply, Equiv.symm_apply_apply]

/-- Building the real matrix out of the entry vector of `seriesFunM c` recovers `reMat`
(statement at the `Matrix` type, so that the `Inv` instance of matrices is used on both sides). -/
lemma reMatZ_invCvec_mat {n : ℕ} (c : (Fin n → ℤ) → Fin n → Fin n → ℂ) (x : Fin n → ℝ) :
    Matrix.of (reMatZ (fun i => Work.Diff.STE.seriesFun (fun k => invCvec n c k i) x))
      = Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) := by
  apply Matrix.ext
  intro i j
  simp only [Matrix.of_apply, reMatZ, Work.Diff.STE.Flat.reMat,
    Work.Diff.STE.Flat.seriesFunM_apply, invCvec_apply, Equiv.symm_apply_apply]

/-- The Moser estimate applied to the entry vector of `seriesFunM c` controls precisely the
`(c', d')`-entry of the inverse of `reMat (seriesFunM c x)`. -/
lemma invPhi_invCvec {n : ℕ} (c : (Fin n → ℤ) → Fin n → Fin n → ℂ) (c' d' : Fin n)
    (x : Fin n → ℝ) :
    invPhi n c' d' (fun i => Work.Diff.STE.seriesFun (fun k => invCvec n c k i) x)
      = (((Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x))⁻¹) c' d' : ℂ) := by
  rw [invPhi_apply]
  exact congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => ((M⁻¹) c' d' : ℂ)) (reMatZ_invCvec_mat c x)

/-- The entry vector of the matrix series of a coefficient family, at a point of the torus. -/
def entryVec (n : ℕ) (c : (Fin n → ℤ) → Fin n → Fin n → ℂ) (x : Fin n → ℝ) :
    Fin (Fintype.card (Fin n × Fin n)) → ℂ :=
  fun i => Work.Diff.STE.seriesFun (fun k => invCvec n c k i) x

@[simp] lemma entryVec_apply (n : ℕ) (c : (Fin n → ℤ) → Fin n → Fin n → ℂ) (x : Fin n → ℝ)
    (i : Fin (Fintype.card (Fin n × Fin n))) :
    entryVec n c x i = Work.Diff.STE.seriesFun (fun k => invCvec n c k i) x := rfl

/-- The `(c', d')`-entry of the inverse of the real part of the matrix series. -/
def invEntryFun (n : ℕ) (c : (Fin n → ℤ) → Fin n → Fin n → ℂ) (c' d' : Fin n) :
    (Fin n → ℝ) → ℂ :=
  fun x => invPhi n c' d' (entryVec n c x)

@[simp] lemma invEntryFun_apply (n : ℕ) (c : (Fin n → ℤ) → Fin n → Fin n → ℂ) (c' d' : Fin n)
    (x : Fin n → ℝ) : invEntryFun n c c' d' x = invPhi n c' d' (entryVec n c x) := rfl

/-- The entry vector of the matrix series reconstructs `reMat (seriesFunM c x)`. -/
lemma reMatZ_entryVec (n : ℕ) (c : (Fin n → ℤ) → Fin n → Fin n → ℂ) (x : Fin n → ℝ) :
    reMatZ (entryVec n c x) = Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) :=
  reMatZ_invCvec c x

/-- The inverse-entry function is the `(c', d')`-entry of the inverse of `reMat (seriesFunM c ·)`. -/
lemma invEntryFun_eq (n : ℕ) (c : (Fin n → ℤ) → Fin n → Fin n → ℂ) (c' d' : Fin n) :
    invEntryFun n c c' d'
      = fun y => (((Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c y))⁻¹) c' d' : ℂ) := by
  funext y
  simp only [invEntryFun_apply, entryVec_apply]
  exact invPhi_invCvec c c' d' y

end

end Work.Diff.STE.flat
