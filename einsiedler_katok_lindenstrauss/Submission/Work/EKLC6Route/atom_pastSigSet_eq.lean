import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.countableGenEntropy
import Submission.Work.EKLC6Core.atom_iSup_comap_iterate_eq
import Submission.Work.EKLC6Core.atom_generateFrom_range_eq

namespace Work.EKLC6Route

/-- The atom of the past σ-algebra `pastSigSet t S = ⨆ n, (Tm t)^[n] ⁻¹' σ(range S)` at `x` is the
set of points `y` whose whole `Tm t`-orbit shadows that of `x` across the partition `S`: for every
`n`, `(Tm t)^[n] x` and `(Tm t)^[n] y` lie in the same member `S m`.  This is
`Work.EKLC6Core.atom_iSup_comap_iterate_eq` composed with
`Work.EKLC6Core.atom_generateFrom_range_eq`, using that `S` is a (measurability-free) partition of
`X₃` (disjoint and covering). -/
theorem atom_pastSigSet_eq {t : Fin 3 → ℝ} (S : ℕ → Set Work.EKLContract.X3)
    (x : Work.EKLContract.X3)
    (hdisj : ∀ m n, m ≠ n → Disjoint (S m) (S n))
    (hcover : (⋃ n, S n) = Set.univ) :
    Work.EKLContract.atom (Work.EKLC6Core.pastSigSet t S) x =
      {y | ∀ n, ∀ m, (Work.EKLC6Route.Tm t)^[n] x ∈ S m →
        (Work.EKLC6Route.Tm t)^[n] y ∈ S m} := by
  -- Unfold the past σ-algebra and identify the atom of a supremum of pullbacks with the
  -- "shadowing on the atoms of the factors" set.
  rw [Work.EKLC6Core.pastSigSet, Work.EKLC6Core.atom_iSup_comap_iterate_eq]
  ext y
  -- The atom of `σ(range S)` is the set of points with the same `S`-pattern, so the two sides
  -- differ only by the direction in which the pattern is read.
  simp only [Work.EKLC6Core.atom_generateFrom_range_eq, Set.mem_ofPred_eq]
  constructor
  · intro h n m hx
    exact (h n m).mpr hx
  · intro h n m
    refine ⟨fun hy => ?_, fun hx => h n m hx⟩
    -- `(Tm t)^[n] x` lies in some part `S m₀`; then `(Tm t)^[n] y` lies in `S m₀` too, and since
    -- the parts are pairwise disjoint and `(Tm t)^[n] y ∈ S m`, necessarily `m = m₀`.
    obtain ⟨m₀, hm₀⟩ : ∃ m₀, (Work.EKLC6Route.Tm t)^[n] x ∈ S m₀ := by
      have hxU : (Work.EKLC6Route.Tm t)^[n] x ∈ (⋃ i, S i) := by
        rw [hcover]; exact Set.mem_univ _
      exact Set.mem_iUnion.mp hxU
    have hy₀ : (Work.EKLC6Route.Tm t)^[n] y ∈ S m₀ := h n m₀ hm₀
    have hmm : m = m₀ := by
      by_contra hne
      exact Set.disjoint_left.mp (hdisj m m₀ hne) hy hy₀
    rw [hmm]
    exact hm₀

end Work.EKLC6Route
