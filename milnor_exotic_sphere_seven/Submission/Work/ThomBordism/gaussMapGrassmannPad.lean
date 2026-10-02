import Mathlib
import Submission.Work.ThomBordism.gaussMapGrassmann
import Submission.Work.ThomBordism.PontryaginThom.Pad
import Submission.Work.ThomBordism.Grassmann.inclusionBundleIso

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000

namespace Work.ThomBordism

noncomputable section

/-- **The iterated ambient inclusion.**  For `a ≤ b` there is a continuous map
`ψ : G̃r_k(ℝ^{k+a}) → G̃r_k(ℝ^{k+b})` (the composite of the inclusions adding one last zero
coordinate) whose pullback of the tautological bundle is isomorphic to the tautological bundle of
the smaller Grassmannian (because the transition functions are the same: the frames agree). -/
theorem inclusionBundleIso_iter (k : ℕ) {a b : ℕ} (hab : a ≤ b) :
    ∃ ψ : C(Work.ThomBordism.Grassmann.OG k a, Work.ThomBordism.Grassmann.OG k b),
      Nonempty (Work.Thom.BundleIso
        (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k b) ψ)
        (Work.ThomBordism.Grassmann.tautologicalBundle k a)) := by
  induction b, hab using Nat.le_induction with
  | base =>
      refine ⟨ContinuousMap.id _, ⟨Work.Thom.BundleIso.ofEq ?_⟩⟩
      exact Work.Thom.bundleComap_id (Work.ThomBordism.Grassmann.tautologicalBundle k a)
  | succ n _han ih =>
      obtain ⟨ψ, ⟨e⟩⟩ := ih
      obtain ⟨φ, ⟨e'⟩⟩ := Work.ThomBordism.Grassmann.inclusionBundleIso k n
      refine ⟨φ.comp ψ, ?_⟩
      have hcomp : Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k (n + 1))
            (φ.comp ψ)
          = Work.Thom.bundleComap
              (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k (n + 1)) φ)
              ψ :=
        (Work.Thom.bundleComap_comp (Work.ThomBordism.Grassmann.tautologicalBundle k (n + 1))
          φ ψ).symm
      obtain ⟨e''⟩ := Work.Thom.BundleIso_comap_exists
        (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k (n + 1)) φ)
        (Work.ThomBordism.Grassmann.tautologicalBundle k n) e' ψ
      exact ⟨(Work.Thom.BundleIso.ofEq hcomp).trans (e''.trans e)⟩

theorem gaussMapGrassmannPad {V : Work.ThomBordism.Man8} {k m : ℕ}
    (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k)) (hk : 1 ≤ k) (hm : 8 ≤ m) :
    ∃ (ι : Type) (ν : Work.TangentClasses.RealBundle V.pt (Work.ThomBordism.Grassmann.Amb k) ι)
      (φ : ν.TotalSpace ≃ₜ Work.Tubular.NormalTotal E)
      (gauss : C(V.pt, Work.ThomBordism.Grassmann.OG k m)),
      Work.Thom.IsEuclidean ν ∧
      (∀ p, Work.Thom.fibreNorm ν p = Work.Tubular.normalNorm E (φ p)) ∧
      Nonempty (Work.Thom.BundleIso
        (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k m) gauss) ν) := by
  obtain ⟨ι, ν, φ, gauss₈, hEuc, hNorm, hIso₈⟩ := gaussMapGrassmann E hk
  obtain ⟨ψ, ⟨eψ⟩⟩ := inclusionBundleIso_iter k hm
  refine ⟨ι, ν, φ, ψ.comp gauss₈, hEuc, hNorm, ?_⟩
  obtain ⟨e₂⟩ := Work.Thom.BundleIso_comap_exists
    (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k m) ψ)
    (Work.ThomBordism.Grassmann.tautologicalBundle k 8) eψ gauss₈
  have hcomp : Work.Thom.bundleComap
        (Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k m) ψ) gauss₈
      = Work.Thom.bundleComap (Work.ThomBordism.Grassmann.tautologicalBundle k m)
          (ψ.comp gauss₈) :=
    Work.Thom.bundleComap_comp (Work.ThomBordism.Grassmann.tautologicalBundle k m) ψ gauss₈
  obtain ⟨e₈⟩ := hIso₈
  exact ⟨(Work.Thom.BundleIso.ofEq hcomp.symm).trans (e₂.trans e₈)⟩

end

end Work.ThomBordism
