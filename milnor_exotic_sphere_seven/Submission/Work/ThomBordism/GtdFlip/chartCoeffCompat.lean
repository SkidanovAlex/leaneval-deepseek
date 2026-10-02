import Mathlib
import Submission.Work.Thom.ChartOrientation
import Submission.Work.Thom.isOrientedOver_of_det_pos
import Submission.Work.Thom.chartCoeffAux
import Submission.Work.ThomBordism.Grassmann.localThomMapChartInjective

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

namespace Work.ThomBordism.GtdFlip

open Work.TangentClasses

noncomputable section

/-! ## A cast bookkeeping lemma

The coefficient equations of the chart pieces are stated in degree `n`, while the local Thom map
produces degree `0 + n` classes.  The following elementary lemma removes the degree cast
`Nat.zero_add n`: two degree-`(0+n)` classes which become equal after transporting along
`Nat.zero_add n` are equal. -/

theorem eqRec_zero_add_inj {M : ℕ → Type} (n : ℕ) {A B : M (0 + n)}
    (h : (Nat.zero_add n) ▸ A = (Nat.zero_add n) ▸ B) : A = B := by
  have h2 := congrArg (fun z => (Nat.zero_add n).symm ▸ z) h
  simpa only [eqRec_eq_cast, cast_cast, cast_eq] using h2

/-- **Compatibility of the chart coefficients of a Thom class on an overlap.**

Let `Z → B` be a real bundle of rank `n`, `T` a Thom class of `Z`, and let `dS`, `dT` be the
coefficients expressing the restriction of `T` over the chart pieces `baseSet i`, `baseSet j` in
terms of the explicit chart classes `chartCoh`.  If the transition map `coordChange i j` is
orientation preserving on the overlap, then `ptEv` of `dS` and of `dT` agree at every point of the
overlap.

The proof restricts both coefficient equations to the fibre over a point `b` of the overlap, using
the fact that over a single point every orientation preserving gauge fixes the model class, so
that the two chart classes over `{b}` coincide; injectivity of the local Thom map in degree `0`
then identifies the two restricted coefficients, and `ptEv` is read off by pulling back. -/
theorem chartCoeffCompat {B : Type} [TopologicalSpace B] {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type} [FiniteDimensional ℝ F] (Z : Work.TangentClasses.RealBundle B F ι)
    {n : ℕ} (hrank : Z.rank = n) (hn : 1 ≤ n) (T : Work.Thom.ThomClass Z n)
    (e : F ≃L[ℝ] EuclideanSpace ℝ (Fin n)) (i j : ι)
    (dS : Work.Thom.Coh ℤ 0 ↥(Z.baseSet i)) (dT : Work.Thom.Coh ℤ 0 ↥(Z.baseSet j))
    (hdS : (Work.Thom.PieceRes Z (Z.baseSet i) n).hom T.τ
      = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n (Z.baseSet i)
          (Work.Thom.chartCoh Z n e i (Z.baseSet i) subset_rfl) 0 dS))
    (hdT : (Work.Thom.PieceRes Z (Z.baseSet j) n).hom T.τ
      = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n (Z.baseSet j)
          (Work.Thom.chartCoh Z n e j (Z.baseSet j) subset_rfl) 0 dT))
    (hori : ∀ x : ↥(Z.baseSet i ∩ Z.baseSet j),
      0 < LinearMap.det ((Z.coordChange i j (x : B)).toLinearMap)) :
    ∀ x : ↥(Z.baseSet i ∩ Z.baseSet j),
      Work.Thom.ptEv ⟨x.1, x.2.1⟩ dS = Work.Thom.ptEv ⟨x.1, x.2.2⟩ dT := by
  intro x
  -- the two singleton pieces at the point `x.1`
  have hsubi : ({x.1} : Set B) ⊆ Z.baseSet i := Work.Thom.singleton_subset_of_mem x.2.1
  have hsubj : ({x.1} : Set B) ⊆ Z.baseSet j := Work.Thom.singleton_subset_of_mem x.2.2
  have hsubij : ({x.1} : Set B) ⊆ Z.baseSet i ∩ Z.baseSet j :=
    fun y hy => ⟨hsubi hy, hsubj hy⟩
  -- the two coefficient equations over the singleton piece
  have h1 := Work.Thom.PieceRes_singleton_eq Z n T i (U := Z.baseSet i) (fun _ hx => hx) e dS
    hdS x.1 x.2.1 hsubi
  have h2 := Work.Thom.PieceRes_singleton_eq Z n T j (U := Z.baseSet j) (fun _ hx => hx) e dT
    hdT x.1 x.2.2 hsubj
  -- over a single point an orientation preserving transition fixes the chart class
  have hdet : ∀ y : ↥({x.1} : Set B),
      0 < LinearMap.det ((Z.coordChange i j (y : B)).toLinearMap) := by
    intro y
    have hy : (y : B) = x.1 := Set.mem_singleton_iff.mp y.2
    rw [hy]
    exact hori x
  have hτ : Work.Thom.chartCoh Z n e j ({x.1} : Set B) hsubj
      = Work.Thom.chartCoh Z n e i ({x.1} : Set B) hsubi :=
    Work.Thom.localThomOfChart_eq_of_det_pos Z n hn e i j ({x.1} : Set B)
      hsubi hsubj hsubij hdet
  -- rewrite the second equation with the common chart class
  have h2' : (Work.Thom.PieceRes Z ({x.1} : Set B) n).hom T.τ
      = (Nat.zero_add n) ▸ (Work.Thom.localThomMap Z n ({x.1} : Set B)
          (Work.Thom.chartCoh Z n e i ({x.1} : Set B) hsubi) 0
          ((Work.Thom.CohMap (Work.Thom.ptIncl (Z.baseSet j) x.1 x.2.2) ℤ 0).hom dT)) := by
    rw [h2, hτ]
  -- injectivity of the local Thom map in degree `0` identifies the two coefficients
  have hLM : Work.Thom.localThomMap Z n ({x.1} : Set B)
        (Work.Thom.chartCoh Z n e i ({x.1} : Set B) hsubi) 0
        ((Work.Thom.CohMap (Work.Thom.ptIncl (Z.baseSet i) x.1 x.2.1) ℤ 0).hom dS)
      = Work.Thom.localThomMap Z n ({x.1} : Set B)
        (Work.Thom.chartCoh Z n e i ({x.1} : Set B) hsubi) 0
        ((Work.Thom.CohMap (Work.Thom.ptIncl (Z.baseSet j) x.1 x.2.2) ℤ 0).hom dT) :=
    eqRec_zero_add_inj (M := fun k => Work.Thom.PieceCoh Z ({x.1} : Set B) k) n
      (h1.symm.trans h2')
  have hd : (Work.Thom.CohMap (Work.Thom.ptIncl (Z.baseSet i) x.1 x.2.1) ℤ 0).hom dS
      = (Work.Thom.CohMap (Work.Thom.ptIncl (Z.baseSet j) x.1 x.2.2) ℤ 0).hom dT :=
    ((Work.Thom.localThomOfChart Z n e i ({x.1} : Set B) hsubi).isThom 0).1 hLM
  -- read off the values at the point
  have hA : Work.Thom.ptEv (⟨x.1, x.2.1⟩ : ↥(Z.baseSet i)) dS
      = Work.Thom.ptEv (⟨x.1, rfl⟩ : ↥({x.1} : Set B))
          ((Work.Thom.CohMap (Work.Thom.ptIncl (Z.baseSet i) x.1 x.2.1) ℤ 0).hom dS) := by
    rw [Work.Thom.ptEv_pullback (Work.Thom.ptIncl (Z.baseSet i) x.1 x.2.1)
      (⟨x.1, rfl⟩ : ↥({x.1} : Set B)) dS]
    congr 1
  have hB : Work.Thom.ptEv (⟨x.1, x.2.2⟩ : ↥(Z.baseSet j)) dT
      = Work.Thom.ptEv (⟨x.1, rfl⟩ : ↥({x.1} : Set B))
          ((Work.Thom.CohMap (Work.Thom.ptIncl (Z.baseSet j) x.1 x.2.2) ℤ 0).hom dT) := by
    rw [Work.Thom.ptEv_pullback (Work.Thom.ptIncl (Z.baseSet j) x.1 x.2.2)
      (⟨x.1, rfl⟩ : ↥({x.1} : Set B)) dT]
    congr 1
  rw [hA, hB, hd]

end

end Work.ThomBordism.GtdFlip
