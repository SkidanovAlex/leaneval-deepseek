import Mathlib
import Submission.Work.ThomBordism.Transversality.BoxFamily.Point

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `boxSet` is open, and contains a box around `(y₀, 0)`

* `boxSet_isOpen`: the set of pairs `(y, s)` on which the normal-form construction is valid is open.
  Its three defining conditions are open: `y ∈ domChart.source`, `Φ y + s ∈ codChart.source`, and
  `boxCoord hF y s ∈ (domChart.extend 𝓡n).target`; the last of these uses that `boxCoord` is
  continuous at the points where the first two hold (junk values of the charts outside their
  sources do not occur there).
* `exists_boxSet_nhds`: consequently a whole box `W × {‖s‖ ≤ δ}` around `(y₀, 0)` is contained in
  `boxSet hF`.
-/

open scoped Manifold ContDiff
open Function Set Topology Manifold Filter

set_option autoImplicit false

namespace Work.ThomBordism.Transversality.BoxFamily

noncomputable section

open Work.ThomBordism.Transversality (CoreTarget)

variable {n k : ℕ} {X : CoreTarget n k} {y₀ : X.E} {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem boxSet_isOpen
    (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) :
    IsOpen (boxSet hF) := by
  let T : X.E × EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin k) := fun q => X.Φ q.1 + q.2
  have hTcont : Continuous T :=
    (X.contMDiff_Φ.continuous.comp continuous_fst).add continuous_snd
  have hTopen : IsOpen (hF.domChart.extend (𝓡 n)).target := by
    rw [extend_domChart_target hF]; exact hF.domChart.open_target
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hp1 : p.1 ∈ hF.domChart.source := hp.1
  have hp2 : T p ∈ hF.codChart.source := hp.2.1
  have hp3 : boxCoord hF p.1 p.2 ∈ (hF.domChart.extend (𝓡 n)).target := hp.2.2
  have hA : {q : X.E × EuclideanSpace ℝ (Fin k) | q.1 ∈ hF.domChart.source} ∈ 𝓝 p :=
    (hF.domChart.open_source.preimage continuous_fst).mem_nhds hp1
  have hB : {q : X.E × EuclideanSpace ℝ (Fin k) | T q ∈ hF.codChart.source} ∈ 𝓝 p :=
    (hF.codChart.open_source.preimage hTcont).mem_nhds hp2
  have hCod : ContinuousAt (fun q : X.E × EuclideanSpace ℝ (Fin k) => hF.codChart (T q)) p :=
    ContinuousAt.comp' (f := T) (x := p)
      (contMDiffAt_of_mem_maximalAtlas hF.codChart_mem_maximalAtlas hp2).continuousAt
      hTcont.continuousAt
  have hDom : ContinuousAt (fun q : X.E × EuclideanSpace ℝ (Fin k) => hF.domChart q.1) p :=
    ContinuousAt.comp' (f := Prod.fst) (x := p)
      (contMDiffAt_of_mem_maximalAtlas hF.domChart_mem_maximalAtlas hp1).continuousAt
      continuous_fst.continuousAt
  have hEquiv : ContinuousAt (fun q : X.E × EuclideanSpace ℝ (Fin k) =>
      hF.equiv (hF.domChart q.1)) p :=
    ContinuousAt.comp' (f := fun q : X.E × EuclideanSpace ℝ (Fin k) => hF.domChart q.1) (x := p)
      hF.equiv.continuous.continuousAt hDom
  have hEquiv2 : ContinuousAt (fun q : X.E × EuclideanSpace ℝ (Fin k) =>
      (hF.equiv (hF.domChart q.1)).2) p :=
    ContinuousAt.comp' (x := p)
      (f := fun q : X.E × EuclideanSpace ℝ (Fin k) => hF.equiv (hF.domChart q.1))
      continuous_snd.continuousAt hEquiv
  have hpair : ContinuousAt (fun q : X.E × EuclideanSpace ℝ (Fin k) =>
      (hF.codChart (T q), (hF.equiv (hF.domChart q.1)).2)) p :=
    Filter.Tendsto.prodMk_nhds hCod hEquiv2
  have hBox : ContinuousAt (fun q : X.E × EuclideanSpace ℝ (Fin k) => boxCoord hF q.1 q.2) p :=
    ContinuousAt.comp' (x := p) (f := fun q : X.E × EuclideanSpace ℝ (Fin k) =>
      (hF.codChart (T q), (hF.equiv (hF.domChart q.1)).2))
      hF.equiv.symm.continuous.continuousAt hpair
  have hC : {q : X.E × EuclideanSpace ℝ (Fin k) |
      boxCoord hF q.1 q.2 ∈ (hF.domChart.extend (𝓡 n)).target} ∈ 𝓝 p :=
    hBox.preimage_mem_nhds (hTopen.mem_nhds hp3)
  refine Filter.mem_of_superset (Filter.inter_mem (Filter.inter_mem hA hB) hC) ?_
  intro q hq
  exact ⟨hq.1.1, hq.1.2, hq.2⟩

theorem exists_boxSet_nhds
    (hF : IsSubmersionAtOfComplement F (𝓡 n) (𝓡 k) ((⊤ : ℕ∞) : WithTop ℕ∞) X.Φ y₀) :
    ∃ (W : Set X.E) (δ : ℝ), IsOpen W ∧ y₀ ∈ W ∧ 0 < δ ∧
      ∀ y ∈ W, ∀ s : EuclideanSpace ℝ (Fin k), ‖s‖ ≤ δ → (y, s) ∈ boxSet hF := by
  have hmem : boxSet hF ∈ 𝓝 ((y₀, (0 : EuclideanSpace ℝ (Fin k)))) :=
    (boxSet_isOpen hF).mem_nhds (boxSet_self hF)
  rw [nhds_prod_eq] at hmem
  obtain ⟨V, hV, A, hA, hVA⟩ := Filter.mem_prod_iff.mp hmem
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hA
  refine ⟨interior V, r / 2, isOpen_interior, mem_interior_iff_mem_nhds.mpr hV, by linarith, ?_⟩
  intro y hy s hs
  have hyV : y ∈ V := interior_subset hy
  have hsA : s ∈ A := hball (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; linarith)
  exact hVA (Set.mk_mem_prod hyV hsA)

end

end Work.ThomBordism.Transversality.BoxFamily
