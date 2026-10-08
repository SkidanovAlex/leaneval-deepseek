import Mathlib
import Submission.Work.L2F.Props.oddsub.eigenline_setup
import Submission.Work.L2F.Props.oddsub.charpoly_separable_of_semisimple
import Submission.Work.L2F.Props.oddsub.mk_eq_mk_of_eigen

/-!
# The eigenpoint set of a semisimple element of `SL(2,E)` over an algebraically closed field

Let `E` be an algebraically closed field and `m : Matrix (Fin 2) (Fin 2) E` a matrix with
`m.det = 1` whose characteristic polynomial `X² - tr(m)·X + det(m)` is separable
(`Work.L2F.Props.SemisimpleSL m`).  Then `m` has two distinct eigenvalues in `E`, hence exactly
two eigenlines, i.e. the set of eigenpoints of `m` on the projective line `ℙ¹(E)` has cardinality
`2`:

`(eigenPointSet m).ncard = 2`.

The proof is the standard one:

* the characteristic polynomial splits (the field is algebraically closed), has degree `2`, and
  is separable, so its root set has exactly two elements
  (`Polynomial.card_rootSet_eq_natDegree`);
* each root `λ` admits a nonzero eigenvector, since `λ` is an eigenvalue of the endomorphism
  `Matrix.toLin' m` (`Module.End.hasEigenvalue_iff_isRoot_charpoly`,
  `Module.End.HasEigenvalue.exists_hasEigenvector`);
* two nonzero eigenvectors of the non-scalar matrix `m` for the same eigenvalue are proportional,
  so they define the same eigenpoint — this is `mk_eq_mk_of_eigen`;
* conversely, the eigenvalue attached to an eigenpoint is a root of the characteristic
  polynomial.

These ingredients give a bijection between `eigenPointSet m` and the (two-element) root set of
`m.charpoly`.
-/

open Polynomial Matrix
open scoped MatrixGroups

namespace Work.L2F.Props.oddsub

noncomputable section

/-- Scalars acting on a nonzero vector are determined by the result. -/
private theorem smul_eq_smul_of_ne_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {v : V} (hv : v ≠ 0) {a b : K} (h : a • v = b • v) : a = b := by
  have h' : (a - b) • v = 0 := by rw [sub_smul, h, sub_self]
  rcases (smul_eq_zero.mp h') with h1 | h2
  · exact sub_eq_zero.mp h1
  · exact absurd h2 hv

/-- Membership in `rootSet` is being an `IsRoot`, for a nonzero polynomial. -/
private theorem mem_rootSet_iff_isRoot {E : Type*} [Field E] {p : E[X]} (hp : p ≠ 0) {c : E} :
    c ∈ p.rootSet E ↔ p.IsRoot c := by
  rw [Polynomial.IsRoot.def, Polynomial.mem_rootSet]
  simp [hp, Polynomial.aeval_def]

/-- `IsRoot` gives the corresponding element of `rootSet`. -/
private theorem mem_rootSet_of_isRoot {E : Type*} [Field E] {p : E[X]} (hp : p ≠ 0) {c : E}
    (h : p.IsRoot c) : c ∈ p.rootSet E :=
  (mem_rootSet_iff_isRoot hp).mpr h

/-- An element of `rootSet` is an `IsRoot`. -/
private theorem isRoot_of_mem_rootSet {E : Type*} [Field E] {p : E[X]} (hp : p ≠ 0) {c : E}
    (h : c ∈ p.rootSet E) : p.IsRoot c :=
  (mem_rootSet_iff_isRoot hp).mp h

/-- If `v ≠ 0` and `m *ᵥ v = c • v`, then `c` is a root of the characteristic polynomial. -/
private theorem isRoot_charpoly_of_mulVec_eq_smul {E : Type*} [Field E]
    (m : Matrix (Fin 2) (Fin 2) E) {v : Fin 2 → E}
    (hv : v ≠ 0) {c : E} (h : Matrix.mulVec m v = c • v) : m.charpoly.IsRoot c := by
  have hev : Module.End.HasEigenvector (Matrix.toLin' m) c v := by
    refine ⟨?_, hv⟩
    exact (Module.End.mem_eigenspace_iff (f := Matrix.toLin' m) (μ := c) (x := v)).mpr (by
      rw [Matrix.toLin'_apply]; exact h)
  have hE := Module.End.hasEigenvalue_of_hasEigenvector hev
  have hE' : (LinearMap.charpoly (Matrix.toLin' m)).IsRoot c :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly (Matrix.toLin' m) c).mp hE
  rwa [Matrix.charpoly_toLin'] at hE'

/-- A root of the characteristic polynomial has a nonzero eigenvector. -/
private theorem exists_mulVec_eq_smul_of_isRoot_charpoly {E : Type*} [Field E]
    (m : Matrix (Fin 2) (Fin 2) E) {c : E}
    (h : m.charpoly.IsRoot c) : ∃ v : Fin 2 → E, v ≠ 0 ∧ Matrix.mulVec m v = c • v := by
  have hE : Module.End.HasEigenvalue (Matrix.toLin' m) c :=
    (Module.End.hasEigenvalue_iff_isRoot_charpoly (Matrix.toLin' m) c).mpr
      (by rwa [Matrix.charpoly_toLin'])
  obtain ⟨v, hv⟩ := Module.End.HasEigenvalue.exists_hasEigenvector hE
  exact ⟨v, hv.2, by
    rw [← Matrix.toLin'_apply]
    exact (Module.End.mem_eigenspace_iff (f := Matrix.toLin' m) (μ := c) (x := v)).mp hv.1⟩

theorem ncard_eigenPointSet_of_semisimple (E : Type*) [Field E] [IsAlgClosed E]
    (m : Matrix (Fin 2) (Fin 2) E) (hdet : m.det = 1)
    (h : Work.L2F.Props.SemisimpleSL m) :
    (Work.L2F.Props.oddsub.eigenPointSet m).ncard = 2 := by
  classical
  have hm : ∀ c : E, m ≠ c • (1 : Matrix (Fin 2) (Fin 2) E) := h.1
  have hsep : m.charpoly.Separable := charpoly_separable_of_semisimple E m h
  have hnd : m.charpoly.natDegree = 2 := by
    rw [Matrix.charpoly_natDegree_eq_dim]; simp
  -- the root set of the characteristic polynomial has exactly two elements
  have hcard : Fintype.card ↥(m.charpoly.rootSet E) = 2 := by
    have hs : (m.charpoly.map (algebraMap E E)).Splits := by
      rw [show m.charpoly.map (algebraMap E E) = m.charpoly from by simp]
      exact IsAlgClosed.splits m.charpoly
    rw [Polynomial.card_rootSet_eq_natDegree hsep hs, hnd]
  -- the eigenvector attached to a root of the characteristic polynomial
  let vecOf : ↥(m.charpoly.rootSet E) → (Fin 2 → E) := fun lam =>
    Classical.choose (exists_mulVec_eq_smul_of_isRoot_charpoly m
      (isRoot_of_mem_rootSet m.charpoly_monic.ne_zero lam.2))
  have hvecOf : ∀ lam : ↥(m.charpoly.rootSet E),
      vecOf lam ≠ 0 ∧ Matrix.mulVec m (vecOf lam) = (lam : E) • vecOf lam := fun lam =>
    Classical.choose_spec
      (exists_mulVec_eq_smul_of_isRoot_charpoly m
        (isRoot_of_mem_rootSet m.charpoly_monic.ne_zero lam.2))
  -- the map sending a root to the corresponding eigenpoint
  let Φ : ↥(m.charpoly.rootSet E) → Projectivization E (Fin 2 → E) := fun lam =>
    Projectivization.mk E (vecOf lam) (hvecOf lam).1
  have hinj : Function.Injective Φ := by
    intro lam mu hlm
    have hv : Projectivization.mk E (vecOf mu) (hvecOf mu).1
        = Projectivization.mk E (vecOf lam) (hvecOf lam).1 := hlm.symm
    rw [Projectivization.mk_eq_mk_iff'] at hv
    obtain ⟨a, ha⟩ := hv
    have key : (mu : E) • vecOf mu = (lam : E) • vecOf mu := by
      calc (mu : E) • vecOf mu = Matrix.mulVec m (vecOf mu) := (hvecOf mu).2.symm
        _ = Matrix.mulVec m (a • vecOf lam) := by rw [ha]
        _ = a • Matrix.mulVec m (vecOf lam) := by rw [Matrix.mulVec_smul]
        _ = a • ((lam : E) • vecOf lam) := by rw [(hvecOf lam).2]
        _ = (a * (lam : E)) • vecOf lam := by rw [smul_smul]
        _ = ((lam : E) * a) • vecOf lam := by rw [mul_comm]
        _ = (lam : E) • (a • vecOf lam) := by rw [smul_smul]
        _ = (lam : E) • vecOf mu := by rw [ha]
    exact Subtype.ext (smul_eq_smul_of_ne_zero (hvecOf mu).1 key).symm
  have himage : Set.range Φ = eigenPointSet m := by
    ext p
    constructor
    · rintro ⟨lam, hlam⟩
      rw [← hlam]
      obtain ⟨a, ha⟩ : ∃ a : E, a • vecOf lam = (Φ lam).rep := by
        have hEq : Projectivization.mk E ((Φ lam).rep) (Projectivization.rep_nonzero (Φ lam))
            = Projectivization.mk E (vecOf lam) (hvecOf lam).1 := by
          rw [Projectivization.mk_rep]
        exact (Projectivization.mk_eq_mk_iff' E ((Φ lam).rep) (vecOf lam)
          (Projectivization.rep_nonzero (Φ lam)) (hvecOf lam).1).mp hEq
      refine ⟨(lam : E), ?_⟩
      rw [← ha, Matrix.mulVec_smul, (hvecOf lam).2, smul_smul, smul_smul, mul_comm]
    · intro hp
      obtain ⟨c, hc⟩ := hp
      have hroot : c ∈ m.charpoly.rootSet E :=
        mem_rootSet_of_isRoot m.charpoly_monic.ne_zero
          (isRoot_charpoly_of_mulVec_eq_smul m (Projectivization.rep_nonzero p) hc)
      refine ⟨⟨c, hroot⟩, ?_⟩
      rw [← Projectivization.mk_rep p]
      exact mk_eq_mk_of_eigen E m hm (hvecOf ⟨c, hroot⟩).1
        (Projectivization.rep_nonzero p) (hvecOf ⟨c, hroot⟩).2 hc
  have hmain : (eigenPointSet m).ncard = Fintype.card ↥(m.charpoly.rootSet E) := by
    rw [← himage, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card]
  rw [hmain, hcard]

end

end Work.L2F.Props.oddsub
