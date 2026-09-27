import Mathlib
import Submission.Work.Drive.sideGermSepDefs
import Submission.Work.Drive.CntAt_locallyConstant
import Submission.Work.Drive.chartIsSmooth
import Submission.Work.Drive.germHavoidZc
import Submission.Work.Drive.designCountLocalityGen
import Submission.Work.Drive.sepFamRegularProof

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option maxHeartbeats 4000000

noncomputable section

/-! ## 5. The assembly: the parity locality from the locality of the count and the Sard data -/

/-- **The parity locality of the germ route, from its two analytic obligations.**

* `hLoc` is the *count locality* at a good configuration: the germ count is constant on a whole
  neighbourhood of any configuration at which the pair is a `GoodPair` (this is the implicit function
  theorem plus the compactness of the parameter box; the *interiority* and *transversality* of the
  base meets are exactly the clauses of `GoodAt`, and no genericity is needed).
* `hReg` is the *Sard* obligation: for every two configurations `A`, `B`, every pair of angle lifts
  and every `ε' > 0`, some shift `τ` of small norm has the family of the straight path from `A` to `B`
  regular in the sense of the parity engine.

The two are combined as in the module docstring of `Work.Drive.sideGerm_parity_eq_of_close`: the engine
gives the equality of the parities of the two shifted end counts, and `hLoc` moves each end back to the
configuration that was given. -/
theorem sideGerm_parity_eq_of_close_of_separation_of_data {γ : Circle → ℝ × ℝ} {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ)
    (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hQ : IsPlaneChart γ hγne Q) (hΞ : ChartPert Q m Ξ) (hc : 0 < c)
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p) (w : UnitAddCircle) (hw : w ∈ Zc γ)
    (hLoc : ∀ (w₀ : UnitAddCircle) (t₀ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)),
      GoodAt Ξ Q c w₀ t₀ → ∃ ρ : ℝ, 0 < ρ ∧
        ∀ (t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w' : UnitAddCircle),
          ‖t' - t₀‖ < ρ → dist w' w₀ < ρ → CntAt Ξ Q c w' t' = CntAt Ξ Q c w₀ t₀)
    (hReg : ∀ (A B : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (tR t'R : ℝ)
      (ε' : ℝ), 0 < ε' → ∃ τ₁ τ₂ : EuclideanSpace ℝ (Fin m), ‖τ₁‖ < ε' ∧ ‖τ₂‖ < ε' ∧
        SepRegular Ξ Q c tR t'R A B τ₁ τ₂) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w' : UnitAddCircle),
        ‖t‖ < ε → ‖t'‖ < ε → dist w' w < δ →
        GoodAt Ξ Q c w t → GoodAt Ξ Q c w' t' →
          Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w' t') := by
  obtain ⟨εh, δh, hεh, hδh, hav⟩ := germHavoid_of_Zc hγne hγinj hQ Ξ c hΞ hc hcbot hw
  refine ⟨εh / 8, δh / 2, by linarith, by linarith, ?_⟩
  intro t t' w' ht ht' hw' hg hg'
  obtain ⟨ρ₁, hρ₁, hloc₁⟩ := hLoc w t hg
  obtain ⟨ρ₂, hρ₂, hloc₂⟩ := hLoc w' t' hg'
  obtain ⟨tR, t'R, htR, ht'R, hlift⟩ := sep_exists_lift_pair w w'
  set εs : ℝ := min (εh / 16) (min (ρ₁ / 4) (ρ₂ / 4)) with hεsdef
  have hεspos : 0 < εs := by
    rw [hεsdef]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hεs16 : εs ≤ εh / 16 := by rw [hεsdef]; exact min_le_left _ _
  have hεs1 : εs ≤ ρ₁ / 4 := by
    rw [hεsdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεs2 : εs ≤ ρ₂ / 4 := by
    rw [hεsdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hreg⟩ := hReg t t' tR t'R εs hεspos
  have hτ₁16 : ‖τ₁‖ < εh / 16 := lt_of_lt_of_le hτ₁ hεs16
  have hτ₂16 : ‖τ₂‖ < εh / 16 := lt_of_lt_of_le hτ₂ hεs16
  have hτ₁ρ₁ : ‖τ₁‖ < ρ₁ / 4 := lt_of_lt_of_le hτ₁ hεs1
  have hτ₂ρ₁ : ‖τ₂‖ < ρ₁ / 4 := lt_of_lt_of_le hτ₂ hεs1
  have hτ₁ρ₂ : ‖τ₁‖ < ρ₂ / 4 := lt_of_lt_of_le hτ₁ hεs2
  have hτ₂ρ₂ : ‖τ₂‖ < ρ₂ / 4 := lt_of_lt_of_le hτ₂ hεs2
  -- the three geometric clauses of the engine
  have hπ : IsChartData Q := IsChartData_of_isPlaneChart hQ
  have hloop := sep_hloop Ξ Q hπ t t' τ₁
  have hseam := sep_hseam Ξ Q c tR t'R t t' τ₂ hπ
  have hsmall : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖(sepPathL t t' s + τ₁, sepPathR t t' s + τ₂)‖ < εh := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := Set.mem_Icc.mp hs
    have ht1 : ‖t.1‖ < εh / 8 := lt_of_le_of_lt (norm_fst_le t) ht
    have ht2 : ‖t'.1‖ < εh / 8 := lt_of_le_of_lt (norm_fst_le t') ht'
    have hu1 : ‖t.2‖ < εh / 8 := lt_of_le_of_lt (norm_snd_le t) ht
    have hu2 : ‖t'.2‖ < εh / 8 := lt_of_le_of_lt (norm_snd_le t') ht'
    have e1 : ‖sepPathL t t' s + τ₁‖ < εh := by
      have hnl : ‖sepPathL t t' s‖ ≤ (1 - s) * ‖t.1‖ + s * ‖t'.1‖ := by
        rw [sepPathL]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
          abs_of_nonneg hs0]
      have hb : (1 - s) * ‖t.1‖ + s * ‖t'.1‖ ≤ εh / 8 := by nlinarith
      have := norm_add_le (sepPathL t t' s) τ₁
      linarith [hτ₁16]
    have e2 : ‖sepPathR t t' s + τ₂‖ < εh := by
      have hnl : ‖sepPathR t t' s‖ ≤ (1 - s) * ‖t.2‖ + s * ‖t'.2‖ := by
        rw [sepPathR]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
          abs_of_nonneg hs0]
      have hb : (1 - s) * ‖t.2‖ + s * ‖t'.2‖ ≤ εh / 8 := by nlinarith
      have := norm_add_le (sepPathR t t' s) τ₂
      linarith [hτ₂16]
    rw [Prod.norm_def]
    exact max_lt e1 e2
  have hang : ∀ s ∈ Set.Icc (0 : ℝ) 1, dist (sepAngle tR t'R s) w < δh := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := (Set.mem_Icc.mp hs).1
    have hs1 : s ≤ 1 := (Set.mem_Icc.mp hs).2
    have hd : sepAngle tR t'R s = (((1 - s) * tR + s * t'R : ℝ) : UnitAddCircle) := rfl
    rw [hd, ← htR]
    have hstep1 : dist (((1 - s) * tR + s * t'R : ℝ) : UnitAddCircle) ((tR : ℝ) : UnitAddCircle)
        ≤ |(1 - s) * tR + s * t'R - tR| := sep_dist_coe_coe_le _ _
    have hstep2 : |(1 - s) * tR + s * t'R - tR| ≤ |tR - t'R| := by
      rw [show (1 - s) * tR + s * t'R - tR = s * (t'R - tR) from by ring, abs_mul,
        abs_of_nonneg hs0, abs_sub_comm tR t'R]
      nlinarith [abs_nonneg (t'R - tR), hs1]
    have habs : |tR - t'R| = dist w' w := by rw [abs_sub_comm]; exact hlift
    calc dist (((1 - s) * tR + s * t'R : ℝ) : UnitAddCircle) ((tR : ℝ) : UnitAddCircle)
        ≤ |(1 - s) * tR + s * t'R - tR| := hstep1
      _ ≤ |tR - t'R| := hstep2
      _ = dist w' w := habs
      _ < δh := by linarith
  have havoid := sep_havoid Ξ Q c tR t'R w t t' τ₁ τ₂ hav hsmall hang
  have hiff := odd_coreSideCount_iff_of_famRegular_gen (sepQfam Ξ Q t t' τ₁) c
    (sepPfam Ξ Q tR t'R t t' τ₂) hreg.hL hreg.hN hloop hseam havoid hreg.htrans hreg.hface
  rw [sepCoreSideCount_zero_eq_CntAt Ξ Q c tR t'R t t' τ₁ τ₂,
    sepCoreSideCount_one_eq_CntAt Ξ Q c tR t'R t t' τ₁ τ₂, htR, ht'R] at hiff
  have hc1 : CntAt Ξ Q c w (t.1 + τ₁, t.2 + τ₂) = CntAt Ξ Q c w t := by
    refine hloc₁ _ w ?_ ?_
    · have hsub : ((t.1 + τ₁, t.2 + τ₂) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) - t
          = (τ₁, τ₂) := by ext <;> simp
      rw [hsub, Prod.norm_def]
      exact max_lt (lt_trans hτ₁ρ₁ (by linarith)) (lt_trans hτ₂ρ₁ (by linarith))
    · rw [dist_self]; exact hρ₁
  have hc2 : CntAt Ξ Q c w' (t'.1 + τ₁, t'.2 + τ₂) = CntAt Ξ Q c w' t' := by
    refine hloc₂ _ w' ?_ ?_
    · have hsub : ((t'.1 + τ₁, t'.2 + τ₂) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) - t'
          = (τ₁, τ₂) := by ext <;> simp
      rw [hsub, Prod.norm_def]
      exact max_lt (lt_trans hτ₁ρ₂ (by linarith)) (lt_trans hτ₂ρ₂ (by linarith))
    · rw [dist_self]; exact hρ₂
  rw [hc1, hc2] at hiff
  exact propext hiff

/-! ## 6. The target statement -/

/-- **The germ route's parity locality with the `hdisj` slot discharged.**  This is the colleague's
`Work.Drive.sideGerm_parity_eq_of_close` — *same conclusion, same `Ξ`/`Q`/`c` data, same explicit
`(w : UnitAddCircle)` binder, everything copied character for character* — with its hypothesis

`hdisj : Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q)`

replaced by the data that is actually obtainable (and is supplied in the application by
`IsSmoothEmbedding` + the chart lane): `hγne : ∀ x, γ x ≠ 0`, `hγinj : Function.Injective γ`,
`hQ : IsPlaneChart γ hγne Q`, and `hw : w ∈ Zc γ`.

The proof is the assembly `Work.Drive.sideGerm_parity_eq_of_close_of_separation_of_data`, fed by its
two analytic obligations:
* `Work.Drive.CntAt_locallyConstant` — the count is locally constant at a good configuration;
* `Work.Drive.sep_fam_regular` — the Sard regularity of the straight path family between two
  configurations. -/
theorem sideGerm_parity_eq_of_close_of_separation {γ : Circle → ℝ × ℝ} {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace)
    (c : ℝ) (hγne : ∀ x : Circle, γ x ≠ 0) (hγinj : Function.Injective γ)
    (hQ : Work.Drive.IsPlaneChart γ hγne Q) (hΞ : Work.Drive.ChartPert Q m Ξ) (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (w : UnitAddCircle) (hw : w ∈ Work.Drive.Zc γ) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w' : UnitAddCircle),
        ‖t‖ < ε → ‖t'‖ < ε → dist w' w < δ →
        Work.Drive.GoodAt Ξ Q c w t → Work.Drive.GoodAt Ξ Q c w' t' →
          Odd (Work.Drive.CntAt Ξ Q c w t) = Odd (Work.Drive.CntAt Ξ Q c w' t') := by
  exact sideGerm_parity_eq_of_close_of_separation_of_data Ξ Q c hγne hγinj hQ hΞ hc hcbot w hw
    (fun w₀ t₀ ht => CntAt_locallyConstant Ξ Q c hΞ (IsSmoothChart_of_isPlaneChart hQ) hc w₀ t₀ ht)
    (fun A B tR t'R ε' hε' => sep_fam_regular_proof Ξ Q c hΞ (IsSmoothChart_of_isPlaneChart hQ) hc A B tR t'R ε' hε')

end

end Work.Drive
