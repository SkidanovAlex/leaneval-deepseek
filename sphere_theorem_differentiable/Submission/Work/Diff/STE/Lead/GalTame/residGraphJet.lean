import Mathlib
import Submission.Work.Diff.STE.Lead.GalTame.residGn.BoxDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

open scoped Topology

/-!
# `Work.Diff.STE.Lead.GalTame.residGraphJet`

Uniform jet bounds for the graph function of the sharp residual: for the outer function
`boxPhi` of `ResidGn.BoxDefs` (which is `tmsPhiFun` with the *compactly supported* separator
`boxZeta = ζ · boxEta`, `boxEta` a bump of radii `2σ_j < 3σ_j`), the `k`-th iterated derivative in
the state `w = (z, V, W)` is bounded on the set `{|V| ≤ B, |W| ≤ B}` by a sequence `D'`
*independent of the flat coordinate `z`*.

Proof.
* `boxPhi = tmsPhiFun D j cl ch hcl hch (boxZeta D j ζ)`, and `boxZeta D j ζ` is globally `C^∞`
  with `tsupport (boxZeta D j ζ) ⊆ tsupport ζ ⊆ tmsGood D j`, so `tmsPhi_smooth` gives that
  `boxPhi` is globally `C^∞`; its scalar components are `ContDiff` and hence have continuous
  iterated derivatives.
* On the **compact box** `tmsBox (3σ_j) B B` the compact jet bound `tms_compact_jet_bound`
  supplies the sequence `D'`.
* Off that box, i.e. for `‖z‖ > 3σ_j`, the flat coordinate is outside
  `tsupport (boxZeta D j ζ) ⊆ closedBall 0 (3σ_j)`; since the complement of the topological
  support is open, the graph function vanishes on a whole neighbourhood of the state, so its
  `k`-th iterated derivative is `0 ≤ D' m` (`Filter.EventuallyEq.iteratedFDeriv`).
-/
theorem residGraphJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (cl ch : ℝ) (hcl : 0 < cl) (hch : cl < ch)
    (ζ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (hζ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) ζ)
    (hζsupp : tsupport ζ ⊆ Work.Diff.STE.B3.tmsGood (I := I) (M := M) D j)
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ D' : ℕ → ℝ, (∀ m : ℕ, 0 ≤ D' m) ∧
      ∀ (m k : ℕ), k ≤ m →
      ∀ (z : Fin (Module.finrank ℝ E) → ℝ)
        (V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)
        (W : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          Fin (Module.finrank ℝ E) → ℝ)
        (a' b' : Fin (Module.finrank ℝ E)),
        (∀ p q, |V p q| ≤ B) → (∀ p q r, |W p q r| ≤ B) →
        ‖iteratedFDeriv ℝ k
          (fun w : (Fin (Module.finrank ℝ E) → ℝ) ×
              (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ×
              (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
                Fin (Module.finrank ℝ E) → ℝ) =>
            Work.Diff.STE.Lead.GalTame.ResidGn.boxPhi (I := I) (M := M) D j cl ch hcl hch ζ
              w a' b')
          (z, V, W)‖ ≤ D' m := by
  classical
  -- `boxPhi` is `tmsPhiFun` with the compactly supported separator `boxZeta`.
  have hZeta : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (ResidGn.boxZeta (I := I) (M := M) D j ζ) :=
    ResidGn.boxZeta_contDiff (I := I) (M := M) D j hζ
  -- the topological support of `boxZeta` still lies in the good set of flat coordinates.
  have hsupp : tsupport (ResidGn.boxZeta (I := I) (M := M) D j ζ)
      ⊆ Work.Diff.STE.B3.tmsGood (I := I) (M := M) D j :=
    subset_trans
      (tsupport_mul_subset_left (f := ζ) (g := ResidGn.boxEta (I := I) (M := M) D j)) hζsupp
  -- hence `boxPhi` is globally `C^∞`.
  have hcont : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
      (ResidGn.boxPhi (I := I) (M := M) D j cl ch hcl hch ζ) :=
    Work.Diff.STE.B3.tmsPhi_smooth (I := I) (M := M) D j cl ch hcl hch
      (ResidGn.boxZeta (I := I) (M := M) D j ζ) hZeta hsupp
      (fun a' b' =>
        Work.Diff.STE.B3.tmPsi_state_contDiffOn (I := I) (M := M) D j cl ch hcl hch a' b')
  -- the compact box of states of the target.
  obtain ⟨D', hD'0, hD'⟩ :=
    Work.Diff.STE.B3.tms_compact_jet_bound
      (Φ := ResidGn.boxPhi (I := I) (M := M) D j cl ch hcl hch ζ) hcont
      (Work.Diff.STE.B3.tmsBox (E := E) (3 * D.σ j) B B)
      (Work.Diff.STE.B3.tmsBox_isCompact (E := E) (3 * D.σ j) B B)
  refine ⟨D', hD'0, ?_⟩
  intro m k hkm z V W a' b' hV hW
  by_cases hz : ‖z‖ ≤ 3 * D.σ j
  · -- inside the box: the compact jet bound applies.
    exact hD' m k hkm (z, V, W) a' b'
      (Work.Diff.STE.B3.tmsBox_mem (E := E) hB hB hz hV hW)
  · -- outside the box: `boxPhi` vanishes on a whole neighbourhood of the state.
    have hzc : z ∉ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (3 * D.σ j) := by
      intro hcon
      rw [Metric.mem_closedBall, dist_zero_right] at hcon
      exact hz hcon
    have hzt : z ∉ tsupport (ResidGn.boxZeta (I := I) (M := M) D j ζ) :=
      fun hcon => hzc (ResidGn.boxZeta_tsupport_subset (I := I) (M := M) D j ζ hcon)
    have hnb : (tsupport (ResidGn.boxZeta (I := I) (M := M) D j ζ))ᶜ ∈ 𝓝 z :=
      (isClosed_tsupport _).isOpen_compl.mem_nhds hzt
    have hev : (fun w => ResidGn.boxPhi (I := I) (M := M) D j cl ch hcl hch ζ w a' b')
        =ᶠ[𝓝 (z, V, W)] (fun _ => (0 : ℝ)) := by
      filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds hnb] with w hw
      simp only [ResidGn.boxPhi_apply, Work.Diff.STE.B3.tmsPhiFun,
        image_eq_zero_of_notMem_tsupport hw, zero_mul]
    have hzero : iteratedFDeriv ℝ k
        (fun w => ResidGn.boxPhi (I := I) (M := M) D j cl ch hcl hch ζ w a' b')
          (z, V, W) = 0 := by
      have h1 := hev.iteratedFDeriv ℝ k
      rw [h1.eq_of_nhds]
      simp
    rw [hzero, norm_zero]
    exact hD'0 m

end Work.Diff.STE.Lead.GalTame
