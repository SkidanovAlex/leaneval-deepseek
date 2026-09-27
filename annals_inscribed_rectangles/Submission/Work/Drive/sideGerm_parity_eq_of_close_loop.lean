import Mathlib
import Submission.Work.Drive.psgFamilyDefs
import Submission.Work.Drive.sideGerm_count_localconst
import Submission.Work.Drive.psg_famMeet_endpoints
import Submission.Work.Drive.psg_havoid
import Submission.Work.Drive.psg_fam_smoothness
import Submission.Work.Drive.psg_family_regular

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

variable {m : ℕ}

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-! ## The helper statements of the route

* `contMDiff_psgLoopFam` / `contMDiff_psgChainFam` — the two sides of the family are `C^∞` on the
  five-box (the `hL`/`hN` hypotheses of the parity engine);
* `contMDiff_psgLoopFam_joint` / `contMDiff_psgChainFam_joint` — the *joint* smoothness in the shift
  and the box coordinate (consumed by the parametric Sard of the regularity obligation);
* `psg_havoid` — the radial-face avoidance clause of the engine, transferred from the geometric
  statement `Work.Drive.germHavoid_loop`;
* `psg_family_regular` — **the regularity obligation**: the parametric Sard for this family, in the
  two *independent* chart perturbations `(τ₁, τ₂)`;
* `psg_crossing` — the crossing clause at the two slice faces `p 0 ∈ {0,1}`, from the constancy of the
  family in `p 0` near the ends;
* `psg_famMeet_zero_ncard` / `psg_famMeet_one_ncard` — the identification of the two end slices of the
  family with the two counts;
* `sideGerm_count_localconst` — the transfer: at a good configuration the `ZMod 2` count is locally
  constant in the perturbation parameter. -/

theorem contMDiff_psgLoopFam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (tA tB : ℝ) (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (psgLoopFam Ξ Q A B τ₁) :=
  (psg_fam_smoothness Ξ Q c hΞ hQ A B tA tB τ₁ τ₂).1

theorem contMDiff_psgChainFam (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q)
    (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tA tB : ℝ)
    (τ₁ τ₂ : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (psgChainFam Ξ Q c A B tA tB τ₂) :=
  (psg_fam_smoothness Ξ Q c hΞ hQ A B tA tB τ₁ τ₂).2.1

/-! ## The target theorem -/

theorem sideGerm_parity_eq_of_close_loop {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace)
    (c : ℝ) (hΞ : Work.Drive.ChartPert Q m Ξ) (hQ : Work.Drive.IsChartData Q) (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (w : UnitAddCircle)
    (hloop : Disjoint (Set.range (Work.Drive.coreLoop Q))
      (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q)) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w' : UnitAddCircle),
        ‖t‖ < ε → ‖t'‖ < ε → dist w' w < δ →
        Work.Drive.GoodAt Ξ Q c w t → Work.Drive.GoodAt Ξ Q c w' t' →
          Odd (Work.Drive.CntAt Ξ Q c w t) = Odd (Work.Drive.CntAt Ξ Q c w' t') := by
  classical
  obtain ⟨ε₀, δ₀, hε₀, hδ₀, hhav⟩ :=
    germHavoid_loop Ξ Q c hΞ hQ hc hcbot w hloop
  refine ⟨min (ε₀ / 4) (1 / 4), min δ₀ (1 / 4),
    lt_min (by linarith) (by norm_num), lt_min (by linarith) (by norm_num), ?_⟩
  intro t t' w' ht ht' hw' hgoodA hgoodB
  have hεle : min (ε₀ / 4) (1 / 4) ≤ ε₀ / 4 := min_le_left _ _
  have htE : ‖t‖ < ε₀ / 4 := lt_of_lt_of_le ht hεle
  have ht'E : ‖t'‖ < ε₀ / 4 := lt_of_lt_of_le ht' hεle
  have hδle : min δ₀ (1 / 4) ≤ 1 / 2 := by
    have h := min_le_right δ₀ (1 / 4); linarith
  obtain ⟨wt, hwt⟩ := QuotientAddGroup.mk_surjective w
  obtain ⟨tA, htA, hAdist⟩ := exists_lift_dist_eq (w := w) (w' := w) (wt := wt)
    (δ := min δ₀ (1 / 4)) hwt (by rw [dist_self]; exact lt_min hδ₀ (by norm_num)) hδle
  obtain ⟨tB, htB, hBdist⟩ := exists_lift_dist_eq (w := w) (w' := w') (wt := wt)
    (δ := min δ₀ (1 / 4)) hwt hw' hδle
  have hAmax : |tA - wt| = 0 := by rw [hAdist, dist_self]
  obtain ⟨ρA, hρA, hTA⟩ := sideGerm_count_localconst Ξ Q c hΞ hQ w t hgoodA
  obtain ⟨ρB, hρB, hTB⟩ := sideGerm_count_localconst Ξ Q c hΞ hQ w' t' hgoodB
  set εbr : ℝ := min (min ρA ρB) (ε₀ / 4) / 2 with hεbrdef
  have hεbrpos : 0 < εbr := by
    rw [hεbrdef]
    exact div_pos (lt_min (lt_min hρA hρB) (by linarith)) (by norm_num)
  have hεbrlt : εbr < min (min ρA ρB) (ε₀ / 4) := by
    rw [hεbrdef]
    exact half_lt_self (lt_min (lt_min hρA hρB) (by linarith))
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, htrans, hface0⟩ :=
    psg_family_regular Ξ Q c hΞ hQ t t' tA tB hεbrpos
  have hτ₁ρA : ‖τ₁‖ < ρA :=
    lt_of_lt_of_le hτ₁ (le_trans (le_of_lt hεbrlt) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hτ₂ρA : ‖τ₂‖ < ρA :=
    lt_of_lt_of_le hτ₂ (le_trans (le_of_lt hεbrlt) (le_trans (min_le_left _ _) (min_le_left _ _)))
  have hτ₁ρB : ‖τ₁‖ < ρB :=
    lt_of_lt_of_le hτ₁ (le_trans (le_of_lt hεbrlt) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hτ₂ρB : ‖τ₂‖ < ρB :=
    lt_of_lt_of_le hτ₂ (le_trans (le_of_lt hεbrlt) (le_trans (min_le_left _ _) (min_le_right _ _)))
  have hτ₁ε : ‖τ₁‖ < ε₀ / 4 :=
    lt_of_lt_of_le hτ₁ (le_trans (le_of_lt hεbrlt) (min_le_right _ _))
  have hτ₂ε : ‖τ₂‖ < ε₀ / 4 :=
    lt_of_lt_of_le hτ₂ (le_trans (le_of_lt hεbrlt) (min_le_right _ _))
  have hεhalf : ε₀ / 4 + ε₀ / 4 = ε₀ / 2 := by ring
  have hεlt : ε₀ / 2 < ε₀ := by linarith
  have havoid : ∀ p ∈ Submission.Drive.unitBox 4,
      famLoop (psgLoopFam Ξ Q t t' τ₁) p = famChain (psgChainFam Ξ Q c t t' tA tB τ₂) p →
      (p 4 = 0 ∨ p 4 = 1) → False :=
    psg_havoid Ξ Q c t t' w tA tB τ₁ τ₂ hhav
      (fun s => by
        have hL := norm_psgPathL_le t t' s
        have hR := norm_psgPathR_le t t' s
        rw [Prod.norm_def]
        refine max_lt ?_ ?_
        · calc ‖psgPathL t t' s + τ₁‖ ≤ ‖psgPathL t t' s‖ + ‖τ₁‖ := norm_add_le _ _
            _ ≤ max ‖t.1‖ ‖t'.1‖ + ε₀ / 4 :=
                le_of_lt (add_lt_add_of_le_of_lt hL hτ₁ε)
            _ ≤ ε₀ / 4 + ε₀ / 4 := by
                have h1 : ‖t.1‖ ≤ ‖t‖ := norm_fst_le t
                have h2 : ‖t'.1‖ ≤ ‖t'‖ := norm_fst_le t'
                have hmax : max ‖t.1‖ ‖t'.1‖ ≤ ε₀ / 4 :=
                  max_le (le_trans h1 (le_of_lt htE)) (le_trans h2 (le_of_lt ht'E))
                linarith
            _ = ε₀ / 2 := hεhalf
            _ < ε₀ := hεlt
        · calc ‖psgPathR t t' s + τ₂‖ ≤ ‖psgPathR t t' s‖ + ‖τ₂‖ := norm_add_le _ _
            _ ≤ max ‖t.2‖ ‖t'.2‖ + ε₀ / 4 := le_of_lt (add_lt_add_of_le_of_lt hR hτ₂ε)
            _ ≤ ε₀ / 4 + ε₀ / 4 := by
                have h1 : ‖t.2‖ ≤ ‖t‖ := norm_snd_le t
                have h2 : ‖t'.2‖ ≤ ‖t'‖ := norm_snd_le t'
                have hmax : max ‖t.2‖ ‖t'.2‖ ≤ ε₀ / 4 :=
                  max_le (le_trans h1 (le_of_lt htE)) (le_trans h2 (le_of_lt ht'E))
                linarith
            _ = ε₀ / 2 := hεhalf
            _ < ε₀ := hεlt)
      (fun s => by
        have h := dist_psgAngleClass_le (tA := tA) (tB := tB) (wt := wt) (s := s)
        rw [hAmax] at h
        have hmax : max 0 |tB - wt| = |tB - wt| := max_eq_right (abs_nonneg _)
        rw [hmax] at h
        rw [hwt] at h
        rw [hBdist] at h
        exact lt_of_le_of_lt h (lt_of_lt_of_le hw' (min_le_left _ _)))
  have hface := hface0
  have hloopfam : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      psgLoopFam Ξ Q t t' τ₁ (mk2 u 0) = psgLoopFam Ξ Q t t' τ₁ (mk2 u 1) := by
    intro u _
    simp only [psgLoopFam, chartLoopFam, mk2_apply_zero, mk2_apply_one]
    exact coreLoop_seam_closed (fun z hz => by
      show Ξ (psgPathL t t' u + τ₁) (Q (-z)) = Ξ (psgPathL t t' u + τ₁) (Q z)
      rw [hQ.2 z hz])
  have hseamfam : ∀ (u : ℝ) (x : EuclideanSpace ℝ (Fin 3)), onSeam x →
      psgChainFam Ξ Q c t t' tA tB τ₂ (famPt u (seamInv x))
        = psgChainFam Ξ Q c t t' tA tB τ₂ (famPt u x) := by
    intro u x hx
    rw [psgChainFam_famPt_apply, psgChainFam_famPt_apply]
    refine (clampedSweep_seamInv c (fun s => 1 - s) (psgPFam Ξ Q t t' tA tB τ₂ u)
      (fun y hy => ?_) x hx).symm
    show psgPFam Ξ Q t t' tA tB τ₂ u y = psgPFam Ξ Q t t' tA tB τ₂ u (seamInv2 y)
    refine (diskPlane_seamInv2 (Q := fun z => rotCapping (psgAngleClass tA tB u)
      (Ξ (psgPathR t t' u + τ₂) (Q z))) ?_ hy).symm
    intro z hz
    exact congrArg (fun w => rotCapping (psgAngleClass tA tB u)
      (Ξ (psgPathR t t' u + τ₂) w)) (hQ.2 z hz)
  have hiff := odd_ncard_famMeet_iff CappingSpace (psgLoopFam Ξ Q t t' τ₁)
    (psgChainFam Ξ Q c t t' tA tB τ₂)
    (contMDiff_psgLoopFam Ξ Q c hΞ hQ t t' tA tB τ₁ τ₂)
    (contMDiff_psgChainFam Ξ Q c hΞ hQ t t' tA tB τ₁ τ₂)
    hloopfam hseamfam havoid htrans hface
  have h01 := psg_famMeet_endpoints Ξ Q c t t' tA tB τ₁ τ₂ htA htB
  have h0 := h01.1
  have h1 := h01.2
  have hAeq : Odd (CntAt Ξ Q c w (t.1 + τ₁, t.2 + τ₂)) = Odd (CntAt Ξ Q c w t) :=
    hTA τ₁ τ₂ hτ₁ρA hτ₂ρA
  have hBeq : Odd (CntAt Ξ Q c w' (t'.1 + τ₁, t'.2 + τ₂)) = Odd (CntAt Ξ Q c w' t') :=
    hTB τ₁ τ₂ hτ₁ρB hτ₂ρB
  rw [← hAeq, ← hBeq, ← h0, ← h1]
  exact propext hiff

end

end Work.Drive
