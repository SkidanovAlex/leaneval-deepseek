import Submission.Work.PTGeometric.AmbientPerturbation
import Submission.Work.PTGeometric.LastMile

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Function Set Topology Manifold Filter

namespace Work.PTGeometric

noncomputable section

open Work.ThomBordism

/-- **The pre-data of the last mile**: everything the ambient perturbation theorem of
`AmbientPerturbation.lean` needs, plus the *boundary* data of the collapse end, but without any
transversality away from the boundary. -/
structure AmbientPreData (n k : ℕ) (ι : Type) [Fintype ι] (Fam : ι → Man8) where
  M : Type
  [topologicalSpace : TopologicalSpace M]
  [chartedSpace : ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
  [isManifold : IsManifold (𝓡∂ ((8 + k) + 1)) ∞ M]
  [compactSpace : CompactSpace M]
  [t2Space : T2Space M]
  [nonempty : Nonempty M]
  P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)
  hP : ContMDiff (𝓡∂ ((8 + k) + 1))
    (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) ∞ P
  isProj : ∀ x, P x ∈ Gr n k
  v : M → EuclideanSpace ℝ (Fin n)
  hv : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ v
  mem : ∀ x, P x (v x) = v x
  m : ℕ
  C : AmbCharts n k M P m
  χ : Fin m → M → ℝ
  hχsm : ∀ l, ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, ℝ)) ∞ (χ l)
  hχrange : ∀ l x, 0 ≤ χ l x ∧ χ l x ≤ 1
  hχU : ∀ l y, χ l y ≠ 0 → y ∈ C.U l
  hχint : ∀ l y, χ l y ≠ 0 → (𝓡∂ ((8 + k) + 1)).IsInteriorPoint y
  hχbd : ∃ V : Set M, IsOpen V ∧ (𝓡∂ ((8 + k) + 1)).boundary M ⊆ V ∧
    ∀ l y, y ∈ V → χ l y = 0
  hcov : ∀ x, (∀ l, χ l x = 0) → AmbGood C v x
  S : Set M
  isClosed_S : IsClosed S
  S_subset_bdry : S ⊆ (𝓡∂ ((8 + k) + 1)).boundary M
  endHomeo : ↥(S ∩ {x : M | v x = 0}) ≃ₜ (Σ i : ι, (Fam i).pt)
  avoid : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary M, x ∉ S → v x ≠ 0
  bndTr : ∀ (x : M) (hx : x ∈ (𝓡∂ ((8 + k) + 1)).boundary M), v x = 0 →
    ∃ l : Fin m, x ∈ C.U l ∧
      IsSubmersionAt (𝓡∂ ((8 + k) + 1)) (𝓡 k) ∞ (fun y => C.ell l (v y)) x ∧
      IsSubmersionAt (𝓡 (8 + k)) (𝓡 k) ∞
        (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary M) => C.ell l (v y)) ⟨x, hx⟩

attribute [instance] AmbientPreData.topologicalSpace AmbientPreData.chartedSpace
  AmbientPreData.isManifold AmbientPreData.compactSpace AmbientPreData.t2Space
  AmbientPreData.nonempty

namespace AmbientPreData

variable {n k : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Man8}

/-- **The last mile, assembled.**  From the pre-data (chart family with adapted frames, cut-offs
covering the bad set, and the boundary collapse-end data) one obtains the ambient collapse-end data:
apply the ambient perturbation theorem to the interior and keep the boundary data, which is untouched
because the cut-offs vanish near the boundary. -/
def ambientCollapseEnd (D : AmbientPreData n k ι Fam) :
    AmbientCollapseEnd n k ι Fam := by
  classical
  let V : Set D.M := Classical.choose D.hχbd
  have hVopen : IsOpen V := (Classical.choose_spec D.hχbd).1
  have hVbd : (𝓡∂ ((8 + k) + 1)).boundary D.M ⊆ V := (Classical.choose_spec D.hχbd).2.1
  have hV0 : ∀ l y, y ∈ V → D.χ l y = 0 := (Classical.choose_spec D.hχbd).2.2
  let w : D.M → EuclideanSpace ℝ (Fin n) :=
    Classical.choose (exists_ambient_perturbation D.C D.v D.hv D.mem D.χ D.hχsm D.hχrange D.hχU
      D.hχint D.hχbd D.hcov)
  have hwspec := Classical.choose_spec
    (exists_ambient_perturbation D.C D.v D.hv D.mem D.χ D.hχsm D.hχrange D.hχU
      D.hχint D.hχbd D.hcov)
  have hwsm : ContMDiff (𝓡∂ ((8 + k) + 1)) (𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ w := hwspec.1
  have hwmem : ∀ y, D.P y (w y) = w y := hwspec.2.1
  have hwv : ∀ x, (∀ l, D.χ l x = 0) → w x = D.v x := hwspec.2.2.1
  have hwgood : ∀ x, AmbGood D.C w x := hwspec.2.2.2
  -- near the boundary the perturbation is the identity
  have hwV : ∀ y ∈ V, w y = D.v y := by
    intro y hy
    exact hwv y (fun l => hV0 l y hy)
  have hev_bd : ∀ x ∈ (𝓡∂ ((8 + k) + 1)).boundary D.M, w =ᶠ[𝓝 x] D.v := by
    intro x hx
    filter_upwards [hVopen.mem_nhds (hVbd hx)] with y hy
    exact hwV y hy
  have hset : D.S ∩ {x : D.M | w x = 0} = D.S ∩ {x : D.M | D.v x = 0} := by
    ext x
    constructor
    · rintro ⟨hxS, hxw⟩
      have h := hwV x (hVbd (D.S_subset_bdry hxS))
      refine ⟨hxS, ?_⟩
      show D.v x = 0
      rw [← h]
      exact hxw
    · rintro ⟨hxS, hxv⟩
      have h := hwV x (hVbd (D.S_subset_bdry hxS))
      refine ⟨hxS, ?_⟩
      show w x = 0
      rw [h]
      exact hxv
  refine ({ M := D.M, P := D.P, v := w, continuous_P := D.hP.continuous, continuous_v := hwsm.continuous, contMDiff_v := hwsm, isProj := D.isProj, mem := hwmem, S := D.S, isClosed_S := D.isClosed_S, S_subset_bdry := D.S_subset_bdry, smooth_near_S := ⟨V, D.S_subset_bdry.trans hVbd, hVopen, D.hP.contMDiffOn, hwsm.contMDiffOn⟩, endHomeo := (Homeomorph.setCongr hset).trans D.endHomeo, avoid := ?_, transverse := ?_, bndTransverse := ?_ } : AmbientCollapseEnd n k ι Fam)
  · intro x hx hxS hwx
    have hw_eq := hwV x (hVbd hx)
    rw [hw_eq] at hwx
    exact D.avoid x hx hxS hwx
  · intro x hwx
    by_cases hxint : (𝓡∂ ((8 + k) + 1)).IsInteriorPoint x
    · rcases hwgood x with hne | ⟨l, hxU, hsub⟩
      · exact absurd hwx hne
      · exact ⟨D.C.ell l, D.C.U l, D.C.isOpen_U l, hxU, D.C.ell_inj l, hsub⟩
    · -- at a boundary zero the chart is the one supplied by the boundary transversality
      have hxbd : x ∈ (𝓡∂ ((8 + k) + 1)).boundary D.M := by
        by_contra h
        exact hxint (((𝓡∂ ((8 + k) + 1)).isInteriorPoint_iff_not_isBoundaryPoint x).mpr h)
      have hev : w =ᶠ[𝓝 x] D.v := hev_bd x hxbd
      have hvx : D.v x = 0 := by rw [← hev.eq_of_nhds]; exact hwx
      obtain ⟨l, hxU, hsub, -⟩ := D.bndTr x hxbd hvx
      have hev2 : (fun y => D.C.ell l (D.v y)) =ᶠ[𝓝 x] (fun y => D.C.ell l (w y)) := by
        filter_upwards [hev] with y hy
        show D.C.ell l (D.v y) = D.C.ell l (w y)
        rw [← hy]
      exact ⟨D.C.ell l, D.C.U l, D.C.isOpen_U l, hxU, D.C.ell_inj l,
        (IsSubmersionAt.congr_iff hev2).mp hsub⟩
  · intro x hx hwx
    have hev : w =ᶠ[𝓝 x] D.v := hev_bd x hx
    have hvx : D.v x = 0 := by rw [← hev.eq_of_nhds]; exact hwx
    obtain ⟨l, hxU, hsub, hbsub⟩ := D.bndTr x hx hvx
    have hev2 : (fun y => D.C.ell l (D.v y)) =ᶠ[𝓝 x] (fun y => D.C.ell l (w y)) := by
      filter_upwards [hev] with y hy
      show D.C.ell l (D.v y) = D.C.ell l (w y)
      rw [← hy]
    have hev3 : (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary D.M) => D.C.ell l (D.v y))
        =ᶠ[𝓝 ⟨x, hx⟩] (fun y : ↥((𝓡∂ ((8 + k) + 1)).boundary D.M) => D.C.ell l (w y)) := by
      have hop : (Subtype.val ⁻¹' V) ∈ 𝓝 (⟨x, hx⟩ : ↥((𝓡∂ ((8 + k) + 1)).boundary D.M)) :=
        (continuous_subtype_val (p := fun z : D.M => z ∈ (𝓡∂ ((8 + k) + 1)).boundary D.M)).continuousAt.preimage_mem_nhds
          (hVopen.mem_nhds (hVbd hx))
      filter_upwards [hop] with y hy
      have hy' : (y : D.M) ∈ V := hy
      show D.C.ell l (D.v ↑y) = D.C.ell l (w ↑y)
      rw [← hwV (y : D.M) hy']
    exact ⟨D.C.ell l, D.C.U l, D.C.isOpen_U l, hxU, D.C.ell_inj l,
      (IsSubmersionAt.congr_iff hev2).mp hsub, (IsSubmersionAt.congr_iff hev3).mp hbsub⟩

end AmbientPreData

end

end Work.PTGeometric
