import Mathlib
import Submission.Work.WilE7.CoreStep.GermDefs
import Submission.Work.CoreStep.hcof_of_pairCovers

namespace Work.CoreStep

open Classical Filter Topology

/-- **The failure of the local branch-covering produces a *second*, distinct point over the same
base point, which is an accumulation point of the "bad" points.**

Proof.  Write `A := absSet T`, `x₀ := absPtInv u`, `b := π x₀`, and put

  * `D := C \ π '' (A ∩ V)` — the base points of `C` that are *not* covered by the branch `A ∩ V`;
  * `B := {z ∈ A : π z ∈ D}` — the "bad" points of the piece.

`hfail` says exactly that every neighbourhood `U` of `b` meets `D` (otherwise `C ∩ U` would be
covered by `π '' (A ∩ V)`), so `b ∈ closure D`.  Since `C ⊆ π '' A`, every point of `D` has a lift
in `B`, so `b ∈ closure (π '' B)`, and as `π` is continuous, `closure (π '' B) ⊆ π '' closure B`;
together with compactness of `closure B` (everything sits in the cube `[-1,1]^N`) this produces
`z★ ∈ closure B` with `π z★ = b`.  Then `z★ ∈ closure A` and `π z★ = b ∈ C`, so `hclosed` puts
`z★ ∈ A`; and `z★ ≠ x₀` because `B ⊆ Vᶜ` (`z ∈ B ∩ V` would force `π z ∈ π '' (A ∩ V)`, against
`π z ∈ D`) while `x₀ ∈ V`.  Finally `z★ ∈ closure B` is literally the last clause: every
neighbourhood of `z★` contains a point of `B`. -/
theorem fail_data {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1)))
    (C : Set (Fin n → ℝ))
    (hCsub : C ⊆ WilkiesDesign.E.projFirst n (m + 1) '' (Work.WilE7.MainDesign.absSet T))
    (hclosed : ∀ z ∈ closure (Work.WilE7.MainDesign.absSet T),
      WilkiesDesign.E.projFirst n (m + 1) z ∈ C → z ∈ Work.WilE7.MainDesign.absSet T)
    (u : Fin (Work.WilE7.CoreStep.pDim n m) → ℝ)
    (hpC : WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) ∈ C)
    (V : Set (Fin (n + (m + 1)) → ℝ)) (hV : V ∈ nhds (Work.WilE7.CoreStep.absPtInv u))
    (hfail : ¬ ∃ U ∈ nhds (WilkiesDesign.E.projFirst n (m + 1)
        (Work.WilE7.CoreStep.absPtInv u)),
      C ∩ U ⊆ WilkiesDesign.E.projFirst n (m + 1) ''
        (Work.WilE7.MainDesign.absSet T ∩ V)) :
    ∃ zstar ∈ Work.WilE7.MainDesign.absSet T,
      WilkiesDesign.E.projFirst n (m + 1) zstar =
        WilkiesDesign.E.projFirst n (m + 1) (Work.WilE7.CoreStep.absPtInv u) ∧
      zstar ≠ Work.WilE7.CoreStep.absPtInv u ∧
      ∀ O ∈ nhds zstar, ∃ z ∈ O, z ∈ Work.WilE7.MainDesign.absSet T ∧
        WilkiesDesign.E.projFirst n (m + 1) z ∈ C ∧
        WilkiesDesign.E.projFirst n (m + 1) z ∉ WilkiesDesign.E.projFirst n (m + 1) ''
          (Work.WilE7.MainDesign.absSet T ∩ V) := by
  let x0 : Fin (n + (m + 1)) → ℝ := Work.WilE7.CoreStep.absPtInv u
  let b : Fin n → ℝ := WilkiesDesign.E.projFirst n (m + 1) x0
  let A : Set (Fin (n + (m + 1)) → ℝ) := Work.WilE7.MainDesign.absSet T
  let D : Set (Fin n → ℝ) :=
    {x | x ∈ C ∧ x ∉ WilkiesDesign.E.projFirst n (m + 1) '' (A ∩ V)}
  let B : Set (Fin (n + (m + 1)) → ℝ) :=
    {z | z ∈ A ∧ WilkiesDesign.E.projFirst n (m + 1) z ∈ D}
  have hbC : b ∈ C := hpC
  have hAcube : A ⊆ WilkiesDesign.E.cubeC (n + (m + 1)) := absSet_subset_cubeC T
  -- `hfail` says every neighbourhood of `b` meets `D`
  have hbD : b ∈ closure D := by
    rw [mem_closure_iff_nhds]
    intro U hU
    have hno : ¬ (C ∩ U ⊆ WilkiesDesign.E.projFirst n (m + 1) '' (A ∩ V)) :=
      fun hsub => hfail ⟨U, hU, hsub⟩
    rw [Set.not_subset] at hno
    obtain ⟨x, hxCU, hxnot⟩ := hno
    exact ⟨x, hxCU.2, hxCU.1, hxnot⟩
  -- every point of `D` lifts into `B`
  have hDsub : D ⊆ WilkiesDesign.E.projFirst n (m + 1) '' B := by
    intro x hx
    obtain ⟨w, hwA, hwπ⟩ := hCsub hx.1
    exact ⟨w, ⟨hwA, by rw [hwπ]; exact hx⟩, hwπ⟩
  have hb_cl : b ∈ closure (WilkiesDesign.E.projFirst n (m + 1) '' B) :=
    closure_mono hDsub hbD
  have hBsubA : B ⊆ A := fun z hz => hz.1
  have hBcube : B ⊆ WilkiesDesign.E.cubeC (n + (m + 1)) := fun z hz => hAcube (hBsubA hz)
  have hclBcube : closure B ⊆ WilkiesDesign.E.cubeC (n + (m + 1)) :=
    closure_minimal hBcube (cubeC_isCompact' (n + (m + 1))).isClosed
  have hclBcompact : IsCompact (closure B) :=
    (cubeC_isCompact' (n + (m + 1))).of_isClosed_subset isClosed_closure hclBcube
  have himgclosed : IsClosed (WilkiesDesign.E.projFirst n (m + 1) '' closure B) :=
    (hclBcompact.image (continuous_projFirst' n (m + 1))).isClosed
  have hbimg := closure_minimal (Set.image_mono subset_closure) himgclosed hb_cl
  obtain ⟨zstar, hzstar_clB, hzstar_b⟩ := hbimg
  have hzstar_clA : zstar ∈ closure A := closure_mono hBsubA hzstar_clB
  have hzstar_A : zstar ∈ A := hclosed zstar hzstar_clA (by rw [hzstar_b]; exact hbC)
  -- `B` avoids the neighbourhood `V` of `x₀`, whence `z★ ≠ x₀`
  have hzstar_ne : zstar ≠ x0 := by
    intro heq
    have hx0clB : x0 ∈ closure B := heq ▸ hzstar_clB
    obtain ⟨z, hzV, hzB⟩ := mem_closure_iff_nhds.mp hx0clB V hV
    exact hzB.2.2 ⟨z, ⟨hzB.1, hzV⟩, rfl⟩
  refine ⟨zstar, hzstar_A, hzstar_b, hzstar_ne, ?_⟩
  intro O hO
  obtain ⟨z, hzO, hzB⟩ := mem_closure_iff_nhds.mp hzstar_clB O hO
  exact ⟨z, hzO, hzB.1, hzB.2.1, hzB.2.2⟩

end Work.CoreStep
