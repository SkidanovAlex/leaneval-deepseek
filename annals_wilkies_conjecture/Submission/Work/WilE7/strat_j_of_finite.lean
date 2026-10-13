/-
  WilE7: from finite fibres to full fibre codimension.

  `Work.WilE7.strat_j_of_finite`: a `Good` stratum `S` (fibrewise Jacobian of `S.h` of rank `S.j`
  at every point of `S.X.set`) whose fibres over `ℝ^p` are finite must have `S.j = q`.

  The two halves of the argument are

  * `S.j ≤ q`: the fibrewise Jacobian is a `S.j × q` matrix, so its rank is at most the number of
    its columns (`Matrix.rank_le_width`);
  * `q ≤ S.j`: if `S.j < q`, then `q - S.j ≥ 1` and the implicit-function-theorem chart
    `Work.WilE7.fibre_analytic_chart` parametrises the fibre of `S` near a point `z ∈ S.X.set` by an
    analytic map `γ : ℝ^{q - S.j} → ℝ^q` with injective differential at `0` and `γ 0 = projSnd z`,
    whose image near `0` lies in the fibre.  If that fibre were finite, the image of a small ball
    under `γ` would be a *finite* set; but it is the continuous image of a ball, hence preconnected,
    so (`IsPreconnected.infinite_of_nontrivial`) it must be a single point, forcing `γ` to be
    eventually constant, hence `fderiv γ 0 = 0` — contradicting the injectivity of the differential
    and `q - S.j ≥ 1`.
-/
import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE7.fiber_finite_of_good_full_rank
import Submission.Work.WilE7.fibre_analytic_chart

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
namespace Work.WilE7
open WilkiesConjecture WilkiesDesign WilkiesDesign.E

theorem strat_j_of_finite {p q : ℕ} (S : WilkiesDesign.E.Stratum p q) (hGood : S.Good)
    (hne : S.X.set.Nonempty)
    (hfin : ∀ x : Fin p → ℝ, (WilkiesDesign.E.fiber S.X.set x).Finite) : S.j = q := by
  classical
  obtain ⟨z, hz⟩ := hne
  -- The fibrewise Jacobian at `z` is a `S.j × q` matrix whose rank is `S.j`, so `S.j ≤ q`.
  have hle : S.j ≤ q := by
    have h := Matrix.rank_le_width (Matrix.of fun (a : Fin S.j) (l : Fin q) =>
      eaEval S.X.c (eaD S.X.c (Fin.natAdd p l) (S.h a)) z)
    rw [(hGood z hz).2.1] at h
    exact h
  rcases lt_or_eq_of_le hle with hlt | heq
  · -- `S.j < q`: the fibre is infinite, contradicting `hfin`.
    exfalso
    -- The IFT chart of the fibre of `S` at `z`.
    obtain ⟨γ, hγ0, hγan, hγinj, hγmem⟩ := fibre_analytic_chart S hGood z hz
    obtain ⟨ε, hεpos, hε⟩ := Metric.eventually_nhds_iff.mp hγmem
    have hγcont : Continuous γ :=
      continuous_iff_continuousAt.mpr fun s => (hγan s).continuousAt
    -- The image of a small ball under `γ` lies in the fibre.
    have himg_sub : γ '' Metric.ball (0 : Fin (q - S.j) → ℝ) ε ⊆
        fiber S.X.set (projFirst p q z) := by
      rintro w ⟨s, hs, rfl⟩
      exact hε (Metric.mem_ball.mp hs)
    have himgfin : (γ '' Metric.ball (0 : Fin (q - S.j) → ℝ) ε).Finite :=
      (hfin (projFirst p q z)).subset himg_sub
    -- ... and that image is preconnected.
    have hpre : IsPreconnected (γ '' Metric.ball (0 : Fin (q - S.j) → ℝ) ε) :=
      Metric.isPreconnected_ball.image γ hγcont.continuousOn
    by_cases hnt : (γ '' Metric.ball (0 : Fin (q - S.j) → ℝ) ε).Nontrivial
    · -- A finite preconnected set is a subsingleton, so a nontrivial one is infinite.
      exact himgfin.not_infinite (hpre.infinite_of_nontrivial hnt)
    · -- Hence `γ` is eventually constant, so its differential at `0` vanishes.
      have hsub : (γ '' Metric.ball (0 : Fin (q - S.j) → ℝ) ε).Subsingleton :=
        Set.not_nontrivial_iff.mp hnt
      have hconst : ∀ s ∈ Metric.ball (0 : Fin (q - S.j) → ℝ) ε, γ s = γ 0 := fun s hs =>
        hsub ⟨s, hs, rfl⟩ ⟨0, Metric.mem_ball_self hεpos, rfl⟩
      have hev : γ =ᶠ[𝓝 (0 : Fin (q - S.j) → ℝ)]
          (fun _ : Fin (q - S.j) → ℝ => projSnd p q z) := by
        filter_upwards [Metric.ball_mem_nhds (0 : Fin (q - S.j) → ℝ) hεpos] with s hs
        rw [hconst s hs, hγ0]
      have hzero : fderiv ℝ γ (0 : Fin (q - S.j) → ℝ) = 0 := by
        rw [hev.fderiv_eq]
        exact fderiv_const_apply _
      -- But the differential at `0` is injective and the domain is nontrivial.
      have hpos : 0 < q - S.j := by omega
      let i : Fin (q - S.j) := ⟨0, hpos⟩
      have hu : (Pi.single i (1 : ℝ) : Fin (q - S.j) → ℝ) ≠ 0 := by
        intro h0
        have h1 := congrFun h0 i
        simp only [Pi.single_eq_same, Pi.zero_apply] at h1
        exact one_ne_zero h1
      refine hu (hγinj ?_)
      have hkey : (fun t : Fin (q - S.j) → ℝ => (fderiv ℝ γ (0 : Fin (q - S.j) → ℝ)) t)
          (Pi.single i (1 : ℝ)) = (fun t : Fin (q - S.j) → ℝ =>
            (fderiv ℝ γ (0 : Fin (q - S.j) → ℝ)) t) 0 := by
        simp [hzero]
      exact hkey
  · exact heq

end Work.WilE7
