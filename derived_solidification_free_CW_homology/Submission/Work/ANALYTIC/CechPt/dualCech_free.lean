import Mathlib
import Submission.Work.ANALYTIC.CechPt.DualCechSetup
import Submission.Work.ANALYTIC.HaarBasisMain

/-!
# The terms of the dual Čech complex are free

The terms of the dual Čech complex of the Cantor cover are the abelian groups
`DualC p = C(cechTerm p, ℤ)` of locally constant `ℤ`-valued functions on the `p`-th Čech term
(`Submission/Work/ANALYTIC/CechPt/DualCechSetup.lean`).  Here we prove that each of them is a
free `ℤ`-module.

The route is the Haar/Schauder basis of `C(T, ℤ)` for an infinite light profinite set `T`
(`Submission/Work/ANALYTIC/HaarBasisMain.lean`):

`Work.ANALYTIC.Haar.haarLinearEquiv T : LocallyConstant ↥T ℤ ≃ₗ[ℤ] (Haar.JIdx →₀ ℤ)`,

which transports the standard basis of `Haar.JIdx →₀ ℤ` to `C(T,ℤ)`.  The only input we have to
supply is the infinitude of `cechTerm p`: the diagonal of the Cantor set sits inside it, and the
Cantor set is infinite because it has points with arbitrarily prescribed digits
(`exists_coord_eq`).  Concretely, for each `n` we take the point of `C` with a `1` in position `n`
and `0` elsewhere; the constant `(p+1)`-tuples over these points are pairwise distinct points of
`cechTerm p` (they all have the same binary expansion, being constant tuples).
-/

open CategoryTheory Limits LightProfinite LightCondensed

noncomputable section

namespace Work.ANALYTIC.CechPt

/-! ## Infinitude of the Čech terms -/

/-- A point of the Cantor set whose digit sequence is `1` exactly in position `n` and `0`
elsewhere. -/
noncomputable def unitDigitPoint (n : ℕ) : ↥cantor :=
  Classical.choose (exists_coord_eq (fun k : ℕ => (if k = n then 1 else 0 : Fin 2)))

/-- The defining property of `unitDigitPoint`. -/
theorem digitsOf_unitDigitPoint (n k : ℕ) :
    digitsOf (unitDigitPoint n) k = (if k = n then 1 else 0 : Fin 2) :=
  Classical.choose_spec (exists_coord_eq (fun k : ℕ => (if k = n then 1 else 0 : Fin 2))) k

/-- The points `unitDigitPoint n` are pairwise distinct. -/
theorem unitDigitPoint_injective : Function.Injective unitDigitPoint := by
  intro n m h
  by_contra hnm
  have h1 : digitsOf (unitDigitPoint n) n = (1 : Fin 2) := by
    rw [digitsOf_unitDigitPoint]; simp
  have h2 : digitsOf (unitDigitPoint n) n = (0 : Fin 2) := by
    rw [h, digitsOf_unitDigitPoint]; simp [hnm]
  rw [h2] at h1
  exact absurd h1 (by decide)

/-- **The `p`-th Čech term is infinite.**  The constant `(p+1)`-tuples over the points
`unitDigitPoint n` of the Cantor set give an injection `ℕ ↪ ↥(cechTerm p)`: they lie in
`cechCover p` because all their coordinates have the same binary expansion. -/
theorem infinite_cechTerm (p : ℕ) : Infinite ↥(cechTerm p) := by
  have hinj : Function.Injective
      (fun n : ℕ => (⟨fun _ : Fin (p + 1) => unitDigitPoint n,
        mem_cechCover.mpr (fun i j => rfl)⟩ : ↥(cechTerm p))) := by
    intro n m h
    have h' : (fun _ : Fin (p + 1) => unitDigitPoint n)
        = (fun _ : Fin (p + 1) => unitDigitPoint m) := congrArg Subtype.val h
    exact unitDigitPoint_injective (congrFun h' ⟨0, Nat.succ_pos p⟩)
  exact Infinite.of_injective _ hinj

attribute [instance 100] infinite_cechTerm

/-! ## Freeness -/

/-- Every term `C(cechTerm p, ℤ)` of the dual Čech complex is a free `ℤ`-module.

Suggested route (cheap): `Work.ANALYTIC.Haar.haarLinearEquiv (cechTerm p) :
LocallyConstant ↥(cechTerm p) ℤ ≃ₗ[ℤ] (Haar.JIdx →₀ ℤ)` (needs `[Infinite ↥(cechTerm p).toTop]`,
easy for `cechTerm p`), then transport the standard basis of `JIdx →₀ ℤ` along it and apply
`Module.Free.of_basis`. -/
theorem dualCech_free (p : ℕ) : Module.Free ℤ (Work.ANALYTIC.CechPt.DualC p) :=
  Module.Free.of_equiv (Work.ANALYTIC.Haar.haarLinearEquiv (cechTerm p)).symm

end Work.ANALYTIC.CechPt
