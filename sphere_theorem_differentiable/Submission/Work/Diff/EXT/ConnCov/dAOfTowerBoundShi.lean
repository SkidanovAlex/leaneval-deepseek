import Mathlib
import Submission.Work.Diff.EXT.ConnCov.dAOfTowerBoundShiAux
import Submission.Work.Diff.EXT.ConnCov.aComp_jets_of_aOfTower
import Submission.Work.Diff.EXT.ConnCov.chartMat_jets_of_aComp_jets
import Submission.Work.Diff.EXT.ConnCov.dAOfTower_chart_bound
import Submission.Work.Diff.EXT.ConnCov.slotLin_bound
import Submission.Work.Diff.EXT.ConnCov.coeff_l1_le_of_hmet

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The reaction bound for the frozen tower of the connection difference (Shi input)

Target: `Work.Diff.EXT.ConnCov.dAOfTowerBoundShi`.

The auxiliary definitions and lemmas (`dAOfBase_apply`, `tower_dAOfBase_eq_deriv`,
`dAOf_tower_val_dep`, `aOf_tower_value_bound`, and the packed value functional `tvdVal` of the
reaction tower) live in the sibling module `Submission.Work.Diff.EXT.ConnCov.dAOfTowerBoundShiAux`,
so that the modules proving the inputs of the target (`aComp_jets_of_aOfTower`,
`chartMat_jets_of_aComp_jets`, `dAOfTower_chart_bound`) can import them without importing this
(open) module.

## Route of the proof

`∂_t` of the frozen tower of the connection difference is a fixed differential expression of order
`k + 3` in the metric family, so the bound is a *jet bound* for the metric family on the slab.  The
proof goes through charts:

1. `hA` (the fixed-connection tower of `aOf G t`, levels `≤ k`) gives, through the Koszul relation,
   bounded chart jets of the connection difference (`aComp_jets_of_aOfTower`);
2. together with the metric comparison `hmet` this recovers the chart jets of the metric matrix up
   to order `k + 1` (`chartMat_jets_of_aComp_jets`);
3. the chart recursion of the reaction gives the coordinate-frame components of the reaction tower
   (`dAOfTower_chart_bound`);
4. the reaction tower is a `(k + 3)`-fold *linear* functional of the values of its field arguments
   (`tvdVal_slotLin`), so its bound on the coordinate frame of a chart (`dAOfTower_chart_bound`)
   yields the metric-norm bound of the target, the coefficients of a vector in the coordinate frame
   being controlled by the uniform ellipticity of the chart matrix
   (`coeff_l1_le_of_hmet`); the uniformity in `x ∈ M` is obtained from a finite chart cover
   (`exists_chart_ball_cover_source`).
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov

open Work.Diff.EXT.ATower

theorem dAOfTowerBoundShi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (G : ℝ → Submission.Diff.SMet I M) (T C : ℝ) (hT : 0 < T) (hC : 0 ≤ C)
    (hflow : Submission.Diff.IsRicciFlow G T)
    (hbound : ∀ t ∈ Set.Ico 0 T, Submission.Diff.CurvBound (G t) C)
    (hmet : ∀ t ∈ Set.Ico 0 T, ∀ x : M, ∀ u : TangentSpace I x,
      (G t).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G 0).inner x u u ∧
      (G 0).inner x u u ≤ Real.exp (2 * ((Module.finrank ℝ E : ℝ) * C) * t) * (G t).inner x u u)
    (hShi : Work.Diff.EXT.ShiBounds (I := I) (M := M))
    (k : ℕ) (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j)
    (hA : ∀ j, j ≤ k → ∀ t ∈ Set.Ico (T / 2) T,
      Work.Diff.EXT.ATower.ValBound G t j
        (Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
          (fun _ => Work.Diff.EXT.aOf G t) j) (B j)) :
    ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ x : M,
      ∀ (v : Fin k → TangentSpace I x) (a b c : TangentSpace I x),
        |Work.Diff.EXT.ATower.tower (Submission.Diff.lcOf (G 0))
            (Work.Diff.EXT.ConnCov.dAOfBase G t) k
            (fun i => Submission.Diff.smoothExt x (v i))
            (Submission.Diff.smoothExt x a) (Submission.Diff.smoothExt x b)
            (Submission.Diff.smoothExt x c) x|
          ≤ Ck * (1 + Finset.sum (Finset.range (k + 1)) B)
              * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i))))
              * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
              * Real.sqrt ((G t).inner x c c) := by
  classical
  by_cases hMne : Nonempty M
  · letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) :=
      ⟨(G 0).toRiemannianMetric⟩
    haveI : IsContMDiffRiemannianBundle I (⊤ : ℕ∞) E (fun x : M ↦ TangentSpace I x) := inferInstance
    -- ## the finite cover by chart balls
    obtain ⟨ι₀, hFint, x₀, r, hrpos, hrsub, hcover⟩ :=
      Work.Diff.EXT.ConnCov.exists_chart_ball_cover_source (I := I) (M := M)
    let K' : ι₀ → Set E := fun i => Metric.closedBall ((extChartAt I (x₀ i)) (x₀ i)) (r i)
    have hK'c : ∀ i, IsCompact (K' i) := fun i => isCompact_closedBall _ _
    have hK't : ∀ i, K' i ⊆ (extChartAt I (x₀ i)).target := fun i => hrsub i
    have hK'ne : ∀ i, (K' i).Nonempty := fun i =>
      ⟨_, Metric.mem_closedBall_self (hrpos i).le⟩
    -- some chart of the cover (the cover is nonempty because `M` is)
    have hex : ∃ i : ι₀, True := by
      obtain ⟨x⟩ := hMne
      have hx : x ∈ ⋃ i, (chartAt H (x₀ i)).source ∩
          (extChartAt I (x₀ i)) ⁻¹' Metric.ball ((extChartAt I (x₀ i)) (x₀ i)) (r i) := by
        rw [hcover]; exact Set.mem_univ x
      rw [Set.mem_iUnion] at hx
      exact ⟨hx.choose, trivial⟩
    obtain ⟨i0, -⟩ := hex
    have hneF : (Finset.univ : Finset ι₀).Nonempty := ⟨i0, Finset.mem_univ i0⟩
    -- ## the coordinate-frame bound of the reaction tower, uniformly on each chart
    have hP4 : ∀ i : ι₀, ∃ Ck : ℝ, 0 ≤ Ck ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K' i,
        ∀ (v : Fin k → Fin (Module.finrank ℝ E)) (i₁ i₂ i₃ : Fin (Module.finrank ℝ E)),
          |tower (Submission.Diff.lcOf (G 0)) (dAOfBase G t) k
            (fun s => Work.Diff.GE.cFrame (I := I) (x₀ i) (v s))
            (Work.Diff.GE.cFrame (I := I) (x₀ i) i₁)
            (Work.Diff.GE.cFrame (I := I) (x₀ i) i₂)
            (Work.Diff.GE.cFrame (I := I) (x₀ i) i₃)
            (Work.Diff.EXT.pt (I := I) (x₀ i) y)| ≤ Ck := by
      intro i
      exact dAOfTower_chart_bound (I := I) (M := M) hLC G T C hT hC hflow hbound hmet hShi k
        (x₀ i) (K' i) (hK'c i) (hK't i)
        (aComp_jets_of_aOfTower (I := I) (M := M) hLC G T C hT hC hmet k B hB hA
          (x₀ i) (K' i) (hK'c i) (hK't i))
        (chartMat_jets_of_aComp_jets (I := I) (M := M) hLC G T C hT hC hmet
          (x₀ i) (K' i) (hK'c i) (hK't i) k
          (aComp_jets_of_aOfTower (I := I) (M := M) hLC G T C hT hC hmet k B hB hA
            (x₀ i) (K' i) (hK'c i) (hK't i)))
    choose Cc hCc0 hCc using hP4
    -- ## the uniform bound for the coefficients in the chart frame
    have hCB : ∀ i : ι₀, ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Set.Ico (T / 2) T, ∀ y ∈ K' i,
        ∀ v : TangentSpace I (Work.Diff.EXT.pt (I := I) (x₀ i) y),
          Finset.sum Finset.univ (fun p => |(Module.finBasis ℝ E).repr
              ((trivializationAt E (TangentSpace I) (x₀ i)).continuousLinearMapAt ℝ
                (Work.Diff.EXT.pt (I := I) (x₀ i) y) v) p|)
            ≤ K * Real.sqrt ((G t).inner (Work.Diff.EXT.pt (I := I) (x₀ i) y) v v) :=
      fun i => coeff_l1_le_of_hmet (I := I) (M := M) G T C hT hC hmet
        (x₀ i) (K' i) (hK'c i) (hK't i) (hK'ne i)
    choose KK hKKpos hKK using hCB
    -- ## the uniform constant
    set Cmax : ℝ := Finset.sup' Finset.univ hneF (fun i => Cc i * (KK i) ^ (k + 3)) with hCmax
    have hCmax : ∀ i : ι₀, Cc i * (KK i) ^ (k + 3) ≤ Cmax := fun i =>
      Finset.le_sup' (f := fun i => Cc i * (KK i) ^ (k + 3)) (Finset.mem_univ i)
    have hCmax0 : 0 ≤ Cmax :=
      le_trans (mul_nonneg (hCc0 i0) (pow_nonneg (hKKpos i0).le _)) (hCmax i0)
    have hSumB0 : 0 ≤ Finset.sum (Finset.range (k + 1)) B :=
      Finset.sum_nonneg (fun j _ => hB j)
    have hden : (1 + Finset.sum (Finset.range (k + 1)) B) ≠ 0 :=
      ne_of_gt (by linarith)
    refine ⟨Cmax / (1 + Finset.sum (Finset.range (k + 1)) B),
      div_nonneg hCmax0 (by linarith),
      fun t ht x v a b c => ?_⟩
    -- ## the chart containing `x`
    have hxmem : x ∈ ⋃ i, (chartAt H (x₀ i)).source ∩
        (extChartAt I (x₀ i)) ⁻¹' Metric.ball ((extChartAt I (x₀ i)) (x₀ i)) (r i) := by
      rw [hcover]; exact Set.mem_univ x
    rw [Set.mem_iUnion] at hxmem
    obtain ⟨i, hi1, hi2⟩ := hxmem
    have hxsrc : x ∈ (chartAt H (x₀ i)).source := hi1
    have hyK : extChartAt I (x₀ i) x ∈ K' i := Metric.ball_subset_closedBall hi2
    have hytarget : extChartAt I (x₀ i) x ∈ (extChartAt I (x₀ i)).target := hK't i hyK
    have hpt : Work.Diff.EXT.pt (I := I) (x₀ i) (extChartAt I (x₀ i) x) = x := by
      show (extChartAt I (x₀ i)).symm (extChartAt I (x₀ i) x) = x
      exact (extChartAt I (x₀ i)).left_inv (by rw [extChartAt_source]; exact hxsrc)
    have htIoo : t ∈ Set.Ioo 0 T := ⟨by linarith [ht.1, hT], ht.2⟩
    -- the value functional on the packed arguments is the target tower
    rw [← tvdVal_uOf (G := G) (t := t) (x := x) (v := v) (a := a) (b := b) (c := c)]
    -- ## slot linearity + expansion in the chart frame
    have hlin : ∀ (u : Fin (k + 3) → TangentSpace I x) (s : Fin (k + 3))
        (p q : TangentSpace I x) (α β : ℝ),
        tvdVal G t k x (Function.update u s (α • p + β • q))
          = α * tvdVal G t k x (Function.update u s p)
            + β * tvdVal G t k x (Function.update u s q) := fun u s p q α β =>
      tvdVal_slotLin (I := I) (M := M) hLC hflow htIoo k x u s p q α β
    -- the values of the tower on the pure tensors of the chart frame
    have hb : ∀ p : Fin (k + 3) → Fin (Module.finrank ℝ E),
        |tvdVal G t k x (fun s => Work.Diff.GE.cFrame (I := I) (x₀ i) (p s) x)| ≤ Cc i := by
      intro p
      have h1 : tvdVal G t k x (fun s => Work.Diff.GE.cFrame (I := I) (x₀ i) (p s) x)
          = tower (Submission.Diff.lcOf (G 0)) (dAOfBase G t) k
              (fun s => Submission.Diff.smoothExt x
                (Work.Diff.GE.cFrame (I := I) (x₀ i) (p (Fin.castAdd 3 s)) x))
              (Submission.Diff.smoothExt x
                (Work.Diff.GE.cFrame (I := I) (x₀ i) (p (Fin.natAdd k 0)) x))
              (Submission.Diff.smoothExt x
                (Work.Diff.GE.cFrame (I := I) (x₀ i) (p (Fin.natAdd k 1)) x))
              (Submission.Diff.smoothExt x
                (Work.Diff.GE.cFrame (I := I) (x₀ i) (p (Fin.natAdd k 2)) x)) x := rfl
      have hconv := cFrame_tower_eq_smoothExt (I := I) (M := M) hLC hflow htIoo k (x₀ i)
        (y := extChartAt I (x₀ i) x) hytarget
        (fun s => p (Fin.castAdd 3 s)) (p (Fin.natAdd k 0)) (p (Fin.natAdd k 1))
        (p (Fin.natAdd k 2))
      rw [hpt] at hconv
      rw [h1, ← hconv, ← hpt]
      exact hCc i t ht (extChartAt I (x₀ i) x) hyK _ _ _ _
    -- the coefficients of the arguments in the chart frame
    have hw : ∀ s, uOf v a b c s = Finset.sum Finset.univ
        (fun p => frameCoef (x₀ i) x (uOf v a b c s) p •
          Work.Diff.GE.cFrame (I := I) (x₀ i) p x) := fun s =>
      (sum_frameCoef_smul_cFrame (I := I) (M := M) (x₀ i) x hxsrc (uOf v a b c s)).symm
    have hslot := slotLin_bound (W := TangentSpace I x) (N := k + 3)
      (n := Module.finrank ℝ E) (Ψ := tvdVal G t k x) hlin
      (fun p => Work.Diff.GE.cFrame (I := I) (x₀ i) p x) (Cc i) (hCc0 i) hb
      (fun s p => frameCoef (x₀ i) x (uOf v a b c s) p) (uOf v a b c) hw
    -- ## the product of the coefficient norms
    have hone : ∀ s : Fin (k + 3), Finset.sum Finset.univ
        (fun p => |frameCoef (x₀ i) x (uOf v a b c s) p|)
        ≤ KK i * Real.sqrt ((G t).inner x (uOf v a b c s) (uOf v a b c s)) := by
      intro s
      have h := hKK i t ht (extChartAt I (x₀ i) x) hyK (uOf v a b c s)
      rw [hpt] at h
      simpa only [frameCoef] using h
    have hprod : Finset.univ.prod (fun s : Fin (k + 3) => Finset.sum Finset.univ
        (fun p => |frameCoef (x₀ i) x (uOf v a b c s) p|))
        ≤ (KK i) ^ (k + 3) * Finset.univ.prod
            (fun s : Fin (k + 3) => Real.sqrt ((G t).inner x (uOf v a b c s)
              (uOf v a b c s))) := by
      have h1 := Finset.prod_le_prod₀ (s := (Finset.univ : Finset (Fin (k + 3))))
        (f := fun s : Fin (k + 3) => Finset.sum Finset.univ
          (fun p => |frameCoef (x₀ i) x (uOf v a b c s) p|))
        (g := fun s : Fin (k + 3) => KK i * Real.sqrt ((G t).inner x (uOf v a b c s)
          (uOf v a b c s)))
        (fun s _ => Finset.sum_nonneg (fun p _ => abs_nonneg _)) (fun s _ => hone s)
      refine le_trans h1 (le_of_eq ?_)
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    -- ## the product splits into the direction and the three argument norms
    have hsplit : Finset.univ.prod (fun s : Fin (k + 3) => Real.sqrt ((G t).inner x
          (uOf v a b c s) (uOf v a b c s)))
        = (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i))))
          * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
          * Real.sqrt ((G t).inner x c c) := by
      have e1 := Fin.prod_univ_add (fun s : Fin (k + 3) => Real.sqrt ((G t).inner x
        (uOf v a b c s) (uOf v a b c s)))
      have e2 : Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x
            (uOf v a b c (Fin.castAdd 3 i)) (uOf v a b c (Fin.castAdd 3 i))))
          = Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i))) := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [uOf_castAdd]
      have e3 : Finset.univ.prod (fun i : Fin 3 => Real.sqrt ((G t).inner x
            (uOf v a b c (Fin.natAdd k i)) (uOf v a b c (Fin.natAdd k i))))
          = Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
            * Real.sqrt ((G t).inner x c c) := by
        rw [Fin.prod_univ_three]
        simp only [uOf_natAdd_zero, uOf_natAdd_one, uOf_natAdd_two]
      rw [e1, e2, e3]
      ring
    -- ## assembly
    have hPnn : 0 ≤ Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i))) :=
      Finset.prod_nonneg (fun i _ => Real.sqrt_nonneg _)
    have hQnn : 0 ≤ Finset.univ.prod (fun s : Fin (k + 3) =>
        Real.sqrt ((G t).inner x (uOf v a b c s) (uOf v a b c s))) :=
      Finset.prod_nonneg (fun s _ => Real.sqrt_nonneg _)
    calc |tvdVal G t k x (uOf v a b c)|
        ≤ Cc i * Finset.univ.prod (fun s : Fin (k + 3) => Finset.sum Finset.univ
            (fun p => |frameCoef (x₀ i) x (uOf v a b c s) p|)) := hslot
      _ ≤ Cc i * ((KK i) ^ (k + 3) * Finset.univ.prod (fun s : Fin (k + 3) =>
            Real.sqrt ((G t).inner x (uOf v a b c s) (uOf v a b c s)))) :=
          mul_le_mul_of_nonneg_left hprod (hCc0 i)
      _ = (Cc i * (KK i) ^ (k + 3)) * Finset.univ.prod (fun s : Fin (k + 3) =>
            Real.sqrt ((G t).inner x (uOf v a b c s) (uOf v a b c s))) := by ring
      _ ≤ Cmax * Finset.univ.prod (fun s : Fin (k + 3) =>
            Real.sqrt ((G t).inner x (uOf v a b c s) (uOf v a b c s))) :=
          mul_le_mul_of_nonneg_right (hCmax i) hQnn
      _ = Cmax * ((Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i))))
            * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
            * Real.sqrt ((G t).inner x c c)) := by rw [hsplit]
      _ = Cmax / (1 + Finset.sum (Finset.range (k + 1)) B)
            * (1 + Finset.sum (Finset.range (k + 1)) B)
            * (Finset.univ.prod (fun i : Fin k => Real.sqrt ((G t).inner x (v i) (v i))))
            * Real.sqrt ((G t).inner x a a) * Real.sqrt ((G t).inner x b b)
            * Real.sqrt ((G t).inner x c c) := by
          rw [div_mul_cancel₀ _ hden]; ring
  · refine ⟨0, le_refl 0, fun t ht x => ?_⟩
    exact (hMne ⟨x⟩).elim

end Work.Diff.EXT.ConnCov
