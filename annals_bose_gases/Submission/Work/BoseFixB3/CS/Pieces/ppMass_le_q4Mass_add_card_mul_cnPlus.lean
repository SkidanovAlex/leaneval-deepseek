import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB3.CS.Pieces.integral_abox_pair_swap_kernel
import Submission.Work.BoseFixB3.CS.Pieces.ppMass_fibre_le
import Submission.Work.BoseFixB3.CS.Pieces.q4Mass_fibre_marginal
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB3.CS.Pieces

noncomputable section
open MeasureTheory

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

/-- Linearity of the double cube integral for jointly continuous integrands. -/
private lemma integral_acube2_add {F G : E3 → E3 → ℝ}
    (hF : Continuous (fun p : E3 × E3 => F p.1 p.2))
    (hG : Continuous (fun p : E3 × E3 => G p.1 p.2)) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ y in Submission.BoseGases.acube ℓ,
        ∫ z in Submission.BoseGases.acube ℓ, (F y z + G y z))
      = (∫ y in Submission.BoseGases.acube ℓ,
            ∫ z in Submission.BoseGases.acube ℓ, F y z)
        + (∫ y in Submission.BoseGases.acube ℓ,
            ∫ z in Submission.BoseGases.acube ℓ, G y z) := by
  classical
  have hFz : ∀ x : E3, MeasureTheory.Integrable (fun z : E3 => F x z)
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := fun x =>
    ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
      ((hF.comp (continuous_const.prodMk continuous_id)).continuousOn)
  have hGz : ∀ x : E3, MeasureTheory.Integrable (fun z : E3 => G x z)
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) := fun x =>
    ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
      ((hG.comp (continuous_const.prodMk continuous_id)).continuousOn)
  have hFy : MeasureTheory.Integrable
      (fun y : E3 => ∫ z in Submission.BoseGases.acube ℓ, F y z)
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
      ((continuous_parametric_integral_of_continuous
        (f := fun (y : E3) (z : E3) => F y z) hF (Submission.BoseGases.acube_compact hℓ)).continuousOn)
  have hGy : MeasureTheory.Integrable
      (fun y : E3 => ∫ z in Submission.BoseGases.acube ℓ, G y z)
      (MeasureTheory.volume.restrict (Submission.BoseGases.acube ℓ)) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.acube_compact hℓ)
      ((continuous_parametric_integral_of_continuous
        (f := fun (y : E3) (z : E3) => G y z) hG (Submission.BoseGases.acube_compact hℓ)).continuousOn)
  calc (∫ y in Submission.BoseGases.acube ℓ,
        ∫ z in Submission.BoseGases.acube ℓ, (F y z + G y z))
      = ∫ y in Submission.BoseGases.acube ℓ,
          ((∫ z in Submission.BoseGases.acube ℓ, F y z)
            + (∫ z in Submission.BoseGases.acube ℓ, G y z)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with y
        exact MeasureTheory.integral_add (hFz y) (hGz y)
    _ = (∫ y in Submission.BoseGases.acube ℓ,
            ∫ z in Submission.BoseGases.acube ℓ, F y z)
          + (∫ y in Submission.BoseGases.acube ℓ,
              ∫ z in Submission.BoseGases.acube ℓ, G y z) :=
        MeasureTheory.integral_add hFy hGy

/-- **Per-pair integrated CS bound.**  Integrating the fibre bound `ppMass_fibre_le_outer` over
the background configuration and using the two marginal identities
(`q4Mass_fibre_marginal` for the `4Q`-square and `integral_abox_pair_swap_kernel` for the two
slot fluctuations):

`2·ℓ⁻⁶·∫(P_iP_jΦ)² ≤ C₀·( 2·∫(q4B_{ij})²w + ℓ⁻²·∫(Q_iΦ)² + ℓ⁻²·∫(Q_jΦ)² )`. -/
private lemma pair_integrated_le {v : E3 → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    (R : ℝ) (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hav : 0 < BoseGases.a v)
    (h : ∃ w : E3 → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hfib : ∀ (ℓ : ℝ), 0 < ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ (n : ℕ) (i j : Fin n), i ≠ j → ∀ {Φ : Submission.BoseGases.X n → ℝ}, Continuous Φ →
      ∀ x : Submission.BoseGases.X n,
      2 * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) ^ 2
        ≤ C₀ * (2 * (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
                (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h))
                    Φ (i, j) (Function.update (Function.update x i y) j z)) ^ 2
                  * Submission.BoseGases.wLoc ℓ v 0 y z)
            + (ℓ ^ 2)⁻¹ * (∫ y in Submission.BoseGases.acube ℓ,
                ∫ z in Submission.BoseGases.acube ℓ,
                  (Submission.BoseGases.aQ ℓ i Φ
                      (Function.update (Function.update x i y) j z)) ^ 2
                + (Submission.BoseGases.aQ ℓ j Φ
                      (Function.update (Function.update x i y) j z)) ^ 2)))
    {m : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (i j : Fin (m + 2)) (hij : i ≠ j) {Φ : X (m + 2) → ℝ} (hΦc : Continuous Φ) :
    2 * ((ℓ ^ 3)⁻¹ * ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (m + 2) ℓ,
          (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) ^ 2))
      ≤ C₀ * (2 * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
              (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) x) ^ 2
                * Submission.BoseGases.wLoc ℓ v 0 (x i) (x j))
            + (ℓ ^ 2)⁻¹ * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
                (Submission.BoseGases.aQ ℓ i Φ x) ^ 2)
            + (ℓ ^ 2)⁻¹ * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
                (Submission.BoseGases.aQ ℓ j Φ x) ^ 2)) := by
  classical
  obtain ⟨j', hj'⟩ : ∃ j' : Fin (m + 1), i.succAbove j' = j :=
    Fin.exists_succAbove_eq (x := j) (y := i) hij.symm
  -- ## abbreviations
  set Q : ℝ := ∫ x in Submission.BoseGases.abox (m + 2) ℓ,
      (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) x) ^ 2
        * Submission.BoseGases.wLoc ℓ v 0 (x i) (x j) with hQ
  set Ki : ℝ := ∫ x in Submission.BoseGases.abox (m + 2) ℓ, (Submission.BoseGases.aQ ℓ i Φ x) ^ 2
    with hKi
  set Kj : ℝ := ∫ x in Submission.BoseGases.abox (m + 2) ℓ, (Submission.BoseGases.aQ ℓ j Φ x) ^ 2
    with hKj
  set J : ℝ := ∫ x in Submission.BoseGases.abox (m + 2) ℓ,
      (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) ^ 2 with hJ
  -- the measures and the measure preserving double insertion
  set ν2 : Measure (E3 × E3) :=
    ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
      ((volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) with hν2
  set νp : Measure (X m) :=
    (volume : Measure (X m)).restrict (Submission.BoseGases.abox m ℓ) with hνp
  set MAP : (E3 × E3) × X m → X (m + 2) :=
    fun q => Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2 with hMAP
  have hmp : MeasureTheory.MeasurePreserving MAP (ν2.prod νp)
      ((volume : Measure (X (m + 2))).restrict (Submission.BoseGases.abox (m + 2) ℓ)) := by
    rw [hν2, hνp, hMAP]
    exact Submission.BoseGases.ins2_flat_mp (p := m) hℓ i j'
  have hemb : MeasurableEmbedding MAP := by
    rw [hMAP]
    have hfun : (fun q : (E3 × E3) × X m => Submission.BoseGases.ins2 i j' q.1.1 q.1.2 q.2)
        = (⇑(Submission.BoseGases.kcInsN (m + 1) i)) ∘
            (Prod.map id (⇑(Submission.BoseGases.kcInsN m j'))) ∘ ⇑(MeasurableEquiv.prodAssoc) := by
      funext q
      rcases q with ⟨⟨y, z⟩, r⟩
      rfl
    rw [hfun]
    exact ((MeasurableEquiv.measurableEmbedding (Submission.BoseGases.kcInsN (m + 1) i)).comp
      ((MeasurableEmbedding.prodMap MeasurableEmbedding.id
          (MeasurableEquiv.measurableEmbedding (Submission.BoseGases.kcInsN m j'))).comp
        (MeasurableEquiv.measurableEmbedding MeasurableEquiv.prodAssoc)))
  haveI : IsFiniteMeasure ν2 := by rw [hν2]; infer_instance
  -- the slot values of an inserted configuration
  have hcfg : ∀ (q : (E3 × E3) × X m) (y z : E3),
      Function.update (Function.update (MAP q) i y) j z
        = Submission.BoseGases.ins2 i j' y z q.2 := by
    intro q y z
    rw [hMAP, ← hj', Submission.BoseGases.ins2_update_i, Submission.BoseGases.ins2_update_succ]
  have hMAPi : ∀ q : (E3 × E3) × X m, (MAP q) i = q.1.1 := by
    intro q
    rw [hMAP]
    exact Submission.BoseGases.ins2_apply_i i j' q.1.1 q.1.2 q.2
  have hMAPj : ∀ q : (E3 × E3) × X m, (MAP q) j = q.1.2 := by
    intro q
    rw [hMAP, ← hj']
    exact Submission.BoseGases.ins2_apply_succ i j' q.1.1 q.1.2 q.2
  -- ## integrability of the box integrand
  have hv_int : MeasureTheory.Integrable v := MeasureTheory.memLp_one_iff_integrable.mp hv1
  have hsuppv : ∀ z : E3, R ≤ ‖z‖ → v z = 0 := fun z hz =>
    Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp hz
  have hpmem : (i, j) ∈ Submission.BoseGases.pairSet (m + 2) := by
    rw [Submission.BoseGases.pairSet]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩
  obtain ⟨-, hqmeas, B, hB0, hqbnd⟩ :=
    ae_bounded_q4B_abox hv hvrad R hR hv_supp hav h hℓ (Φ := Φ) hΦc hpmem
  have hIntOn : MeasureTheory.IntegrableOn
      (fun x : X (m + 2) =>
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) x) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 (x i) (x j))
      (Submission.BoseGases.abox (m + 2) ℓ) MeasureTheory.volume :=
    integrableOn_sq_mul_wLoc (n := m + 2) (p := (i, j))
      hℓ hv_int hsuppv hRℓ hij hqmeas hB0 hqbnd
  -- ## the ambient functions
  set Afl : X (m + 2) → ℝ := fun x => ∫ y in Submission.BoseGases.acube ℓ,
      ∫ z in Submission.BoseGases.acube ℓ,
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j)
            (Function.update (Function.update x i y) j z)) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 y z with hAfl
  set Bfl : X (m + 2) → ℝ := fun x => ∫ y in Submission.BoseGases.acube ℓ,
      ∫ z in Submission.BoseGases.acube ℓ,
        (Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x i y) j z)) ^ 2 with hBfl
  set Bgl : X (m + 2) → ℝ := fun x => ∫ y in Submission.BoseGases.acube ℓ,
      ∫ z in Submission.BoseGases.acube ℓ,
        (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x i y) j z)) ^ 2 with hBgl
  set Bsl : X (m + 2) → ℝ := fun x => ∫ y in Submission.BoseGases.acube ℓ,
      ∫ z in Submission.BoseGases.acube ℓ,
        ((Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x i y) j z)) ^ 2
          + (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x i y) j z)) ^ 2)
    with hBsl
  set Rhl : X (m + 2) → ℝ := fun x => C₀ * (2 * Afl x + (ℓ ^ 2)⁻¹ * Bsl x) with hRhl
  -- the peeled functions
  set Aph : X m → ℝ := fun r2 => ∫ y in Submission.BoseGases.acube ℓ,
      ∫ z in Submission.BoseGases.acube ℓ,
        (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j)
            (Submission.BoseGases.ins2 i j' y z r2)) ^ 2
          * Submission.BoseGases.wLoc ℓ v 0 y z with hAph
  set Bph : X m → ℝ := fun r2 => ∫ y in Submission.BoseGases.acube ℓ,
      ∫ z in Submission.BoseGases.acube ℓ,
        (Submission.BoseGases.aQ ℓ i Φ (Submission.BoseGases.ins2 i j' y z r2)) ^ 2 with hBph
  set Bqh : X m → ℝ := fun r2 => ∫ y in Submission.BoseGases.acube ℓ,
      ∫ z in Submission.BoseGases.acube ℓ,
        (Submission.BoseGases.aQ ℓ j Φ (Submission.BoseGases.ins2 i j' y z r2)) ^ 2 with hBqh
  set Bsh : X m → ℝ := fun r2 => ∫ y in Submission.BoseGases.acube ℓ,
      ∫ z in Submission.BoseGases.acube ℓ,
        ((Submission.BoseGases.aQ ℓ i Φ (Submission.BoseGases.ins2 i j' y z r2)) ^ 2
          + (Submission.BoseGases.aQ ℓ j Φ (Submission.BoseGases.ins2 i j' y z r2)) ^ 2) with hBsh
  -- ## continuity of the update and insertion maps
  have hupdcont : ∀ x : X (m + 2), Continuous (fun q : E3 × E3 =>
      Function.update (Function.update x i q.1) j q.2) := fun x =>
    ((continuous_const (y := x) : Continuous (fun _ : E3 × E3 => x)).update i
      continuous_fst).update j continuous_snd
  have hins2c : ∀ r2 : X m, Continuous (fun q : E3 × E3 =>
      Submission.BoseGases.ins2 i j' q.1 q.2 r2) := by
    intro r2
    show Continuous (fun q : E3 × E3 =>
      Submission.BoseGases.kcInsN (m + 1) i (q.1, Submission.BoseGases.kcInsN m j' (q.2, r2)))
    exact (Submission.BoseGases.kcInsN_cont (n := m + 1) i).comp
      (continuous_fst.prodMk ((Submission.BoseGases.kcInsN_cont (n := m) j').comp
        (continuous_snd.prodMk continuous_const)))
  -- ## the linearity identities
  have hBsl_eq : Bsl = fun x => Bfl x + Bgl x := by
    funext x
    rw [hBsl, hBfl, hBgl]
    exact integral_acube2_add
      (((Submission.BoseGases.aQ_continuous hℓ i hΦc).comp (hupdcont x)).pow 2)
      (((Submission.BoseGases.aQ_continuous hℓ j hΦc).comp (hupdcont x)).pow 2) hℓ
  have hBsh_eq : Bsh = fun r2 => Bph r2 + Bqh r2 := by
    funext r2
    rw [hBsh, hBph, hBqh]
    exact integral_acube2_add
      (((Submission.BoseGases.aQ_continuous hℓ i hΦc).comp (hins2c r2)).pow 2)
      (((Submission.BoseGases.aQ_continuous hℓ j hΦc).comp (hins2c r2)).pow 2) hℓ
  -- ## the pointwise inequality
  have hpt : ∀ x : X (m + 2),
      2 * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) ^ 2 ≤ Rhl x := by
    intro x
    rw [hRhl, hAfl]
    exact hfib ℓ hℓ hRℓ (m + 2) i j hij hΦc x
  -- ## integrability in the peeled space
  set Ψ : (E3 × E3) × X m → ℝ := fun q =>
      (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) (MAP q)) ^ 2
        * Submission.BoseGases.wLoc ℓ v 0 q.1.1 q.1.2 with hΨ
  have hΨint : MeasureTheory.Integrable Ψ (ν2.prod νp) := by
    rw [hΨ]
    refine (hmp.integrable_comp_emb hemb (g := fun x : X (m + 2) =>
      (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) x) ^ 2
        * Submission.BoseGases.wLoc ℓ v 0 (x i) (x j))).mpr ?_ |>.congr ?_
    · exact hIntOn
    · filter_upwards with q
      simp only [Function.comp_apply]
      rw [hMAPi q, hMAPj q]
  have hAprod : MeasureTheory.Integrable
      (fun r2 : X m => ∫ q1 : E3 × E3, Ψ (q1, r2) ∂ν2) νp :=
    hΨint.integral_prod_right
  have hAph_int : MeasureTheory.Integrable Aph νp := by
    refine hAprod.congr ?_
    filter_upwards [hΨint.prod_left_ae] with r2 hr2
    rw [hAph]
    rw [MeasureTheory.integral_prod (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      (f := fun q1 : E3 × E3 => Ψ (q1, r2)) hr2]
  -- the two slot fluctuations in the peeled space
  have hPsi_i_int : MeasureTheory.Integrable
      (fun q : (E3 × E3) × X m => (Submission.BoseGases.aQ ℓ i Φ (MAP q)) ^ 2)
      (ν2.prod νp) :=
    (hmp.integrable_comp_emb hemb
      (g := fun x : X (m + 2) => (Submission.BoseGases.aQ ℓ i Φ x) ^ 2)).mpr
      (Submission.BoseGases.integrableOn_abox_of_continuous hℓ
        ((Submission.BoseGases.aQ_continuous hℓ i hΦc).pow 2))
  have hPsi_j_int : MeasureTheory.Integrable
      (fun q : (E3 × E3) × X m => (Submission.BoseGases.aQ ℓ j Φ (MAP q)) ^ 2)
      (ν2.prod νp) :=
    (hmp.integrable_comp_emb hemb
      (g := fun x : X (m + 2) => (Submission.BoseGases.aQ ℓ j Φ x) ^ 2)).mpr
      (Submission.BoseGases.integrableOn_abox_of_continuous hℓ
        ((Submission.BoseGases.aQ_continuous hℓ j hΦc).pow 2))
  have hBph_int : MeasureTheory.Integrable Bph νp := by
    refine (hPsi_i_int.integral_prod_right).congr ?_
    filter_upwards [hPsi_i_int.prod_left_ae] with r2 hr2
    rw [hBph]
    rw [MeasureTheory.integral_prod (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      (f := fun q1 : E3 × E3 => (Submission.BoseGases.aQ ℓ i Φ (MAP (q1, r2))) ^ 2) hr2]
  have hBqh_int : MeasureTheory.Integrable Bqh νp := by
    refine (hPsi_j_int.integral_prod_right).congr ?_
    filter_upwards [hPsi_j_int.prod_left_ae] with r2 hr2
    rw [hBqh]
    rw [MeasureTheory.integral_prod (μ := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      (ν := (volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      (f := fun q1 : E3 × E3 => (Submission.BoseGases.aQ ℓ j Φ (MAP (q1, r2))) ^ 2) hr2]
  have hBsh_int : MeasureTheory.Integrable Bsh νp := by
    rw [hBsh_eq]
    exact hBph_int.add hBqh_int
  -- ## continuity (hence box integrability) of the ambient slot-fluctuation functions
  have hupdcont3 : Continuous (fun p : (X (m + 2) × E3) × E3 =>
      Function.update (Function.update p.1.1 i p.1.2) j p.2) :=
    (continuous_fst.fst.update i continuous_fst.snd).update j continuous_snd
  have hBfl_cont : Continuous Bfl := by
    rw [hBfl]
    refine continuous_parametric_integral_of_continuous
      (f := fun (x : X (m + 2)) (y : E3) => ∫ z in Submission.BoseGases.acube ℓ,
        (Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x i y) j z)) ^ 2) ?_
      (Submission.BoseGases.acube_compact hℓ)
    refine continuous_parametric_integral_of_continuous
      (f := fun (p : X (m + 2) × E3) (z : E3) =>
        (Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update p.1 i p.2) j z)) ^ 2) ?_
      (Submission.BoseGases.acube_compact hℓ)
    exact (((Submission.BoseGases.aQ_continuous hℓ i hΦc).comp hupdcont3).pow 2)
  have hBgl_cont : Continuous Bgl := by
    rw [hBgl]
    refine continuous_parametric_integral_of_continuous
      (f := fun (x : X (m + 2)) (y : E3) => ∫ z in Submission.BoseGases.acube ℓ,
        (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x i y) j z)) ^ 2) ?_
      (Submission.BoseGases.acube_compact hℓ)
    refine continuous_parametric_integral_of_continuous
      (f := fun (p : X (m + 2) × E3) (z : E3) =>
        (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update p.1 i p.2) j z)) ^ 2) ?_
      (Submission.BoseGases.acube_compact hℓ)
    exact (((Submission.BoseGases.aQ_continuous hℓ j hΦc).comp hupdcont3).pow 2)
  have hBfl_int : MeasureTheory.Integrable Bfl
      ((volume : Measure (X (m + 2))).restrict (Submission.BoseGases.abox (m + 2) ℓ)) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact (m + 2) hℓ)
      hBfl_cont.continuousOn
  have hBgl_int : MeasureTheory.Integrable Bgl
      ((volume : Measure (X (m + 2))).restrict (Submission.BoseGases.abox (m + 2) ℓ)) :=
    ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact (m + 2) hℓ)
      hBgl_cont.continuousOn
  -- ## the identifications between the ambient and the peeled functions
  have hAfl_MAP : ∀ q : (E3 × E3) × X m, Afl (MAP q) = Aph q.2 := by
    intro q
    rw [hAfl, hAph]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    rw [hcfg q y z]
  have hBsl_MAP : ∀ q : (E3 × E3) × X m, Bsl (MAP q) = Bsh q.2 := by
    intro q
    rw [hBsl, hBsh]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    apply MeasureTheory.integral_congr_ae
    filter_upwards with z
    rw [hcfg q y z]
  -- ## integrability of the ambient right-hand side (transported from the peeled space)
  have hAq_int : MeasureTheory.Integrable (fun q : (E3 × E3) × X m => Aph q.2) (ν2.prod νp) :=
    hAph_int.comp_snd ν2
  have hBsq_int : MeasureTheory.Integrable (fun q : (E3 × E3) × X m => Bsh q.2) (ν2.prod νp) :=
    hBsh_int.comp_snd ν2
  have hRhl_int : MeasureTheory.Integrable Rhl
      ((volume : Measure (X (m + 2))).restrict (Submission.BoseGases.abox (m + 2) ℓ)) := by
    refine (hmp.integrable_comp_emb hemb (g := fun x : X (m + 2) =>
      C₀ * (2 * Afl x + (ℓ ^ 2)⁻¹ * Bsl x))).mp ?_
    refine (((hAq_int.const_mul 2).add (hBsq_int.const_mul ((ℓ ^ 2)⁻¹))).const_mul C₀).congr ?_
    filter_upwards with q
    show C₀ * (2 * Aph q.2 + (ℓ ^ 2)⁻¹ * Bsh q.2)
      = C₀ * (2 * Afl (MAP q) + (ℓ ^ 2)⁻¹ * Bsl (MAP q))
    rw [hAfl_MAP q, hBsl_MAP q]
  -- ## the values of the peeled integrals
  have hAph_val : (∫ q : (E3 × E3) × X m, Aph q.2 ∂(ν2.prod νp)) = ℓ ^ 6 * Q := by
    have h1 : (∫ x in Submission.BoseGases.abox (m + 2) ℓ, Afl x)
        = ∫ q : (E3 × E3) × X m, Aph q.2 ∂(ν2.prod νp) := by
      rw [← hmp.integral_comp hemb Afl]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with q
      exact hAfl_MAP q
    rw [← h1]
    show (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
        ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j)
              (Function.update (Function.update x i y) j z)) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 y z)
      = ℓ ^ 6 * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
          (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h)) Φ (i, j) x) ^ 2
            * Submission.BoseGases.wLoc ℓ v 0 (x i) (x j))
    exact q4Mass_fibre_marginal hv hvrad hv1 R hR hv_supp hav h hℓ hRℓ i j hij hΦc
  have hBsh_val : (∫ q : (E3 × E3) × X m, Bsh q.2 ∂(ν2.prod νp)) = ℓ ^ 6 * Ki + ℓ ^ 6 * Kj := by
    have h1 : (∫ x in Submission.BoseGases.abox (m + 2) ℓ, Bsl x)
        = ∫ q : (E3 × E3) × X m, Bsh q.2 ∂(ν2.prod νp) := by
      rw [← hmp.integral_comp hemb Bsl]
      apply MeasureTheory.integral_congr_ae
      filter_upwards with q
      exact hBsl_MAP q
    rw [← h1, hBsl_eq]
    rw [MeasureTheory.integral_add hBfl_int hBgl_int]
    have hKi_eq : (∫ x in Submission.BoseGases.abox (m + 2) ℓ, Bfl x) = ℓ ^ 6 * Ki := by
      rw [hKi]
      show (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
          ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
            (Submission.BoseGases.aQ ℓ i Φ (Function.update (Function.update x i y) j z)) ^ 2)
        = ℓ ^ 6 * ∫ x in Submission.BoseGases.abox (m + 2) ℓ,
            (Submission.BoseGases.aQ ℓ i Φ x) ^ 2
      exact integral_abox_pair_swap_kernel (n := m + 2) hℓ i j hij
        (K := fun x _ _ => (Submission.BoseGases.aQ ℓ i Φ x) ^ 2)
        (((Submission.BoseGases.aQ_continuous hℓ i hΦc).comp continuous_fst).pow 2)
    have hKj_eq : (∫ x in Submission.BoseGases.abox (m + 2) ℓ, Bgl x) = ℓ ^ 6 * Kj := by
      rw [hKj]
      show (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
          ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
            (Submission.BoseGases.aQ ℓ j Φ (Function.update (Function.update x i y) j z)) ^ 2)
        = ℓ ^ 6 * ∫ x in Submission.BoseGases.abox (m + 2) ℓ,
            (Submission.BoseGases.aQ ℓ j Φ x) ^ 2
      exact integral_abox_pair_swap_kernel (n := m + 2) hℓ i j hij
        (K := fun x _ _ => (Submission.BoseGases.aQ ℓ j Φ x) ^ 2)
        (((Submission.BoseGases.aQ_continuous hℓ j hΦc).comp continuous_fst).pow 2)
    rw [hKi_eq, hKj_eq]
  -- ## the value of the integrated right-hand side
  have hRval : (∫ x in Submission.BoseGases.abox (m + 2) ℓ, Rhl x)
      = C₀ * (2 * (ℓ ^ 6 * Q) + (ℓ ^ 2)⁻¹ * (ℓ ^ 6 * Ki + ℓ ^ 6 * Kj)) := by
    rw [← hmp.integral_comp hemb Rhl]
    have h2 : (fun q : (E3 × E3) × X m => Rhl (MAP q))
        = fun q : (E3 × E3) × X m => C₀ * (2 * Aph q.2 + (ℓ ^ 2)⁻¹ * Bsh q.2) := by
      funext q
      show C₀ * (2 * Afl (MAP q) + (ℓ ^ 2)⁻¹ * Bsl (MAP q))
        = C₀ * (2 * Aph q.2 + (ℓ ^ 2)⁻¹ * Bsh q.2)
      rw [hAfl_MAP q, hBsl_MAP q]
    rw [h2, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_add (hAq_int.const_mul 2) (hBsq_int.const_mul ((ℓ ^ 2)⁻¹)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      hAph_val, hBsh_val]
  -- ## the monotone integral
  have hmono : (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
        2 * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) ^ 2)
      ≤ ∫ x in Submission.BoseGases.abox (m + 2) ℓ, Rhl x :=
    MeasureTheory.integral_mono_of_nonneg
      (f := fun x : X (m + 2) =>
        2 * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) ^ 2)
      (g := Rhl)
      (Filter.Eventually.of_forall (fun x => by positivity))
      hRhl_int
      (Filter.Eventually.of_forall hpt)
  have hLval : (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
        2 * (Submission.BoseGases.aP ℓ i (Submission.BoseGases.aP ℓ j Φ) x) ^ 2) = 2 * J := by
    rw [hJ, MeasureTheory.integral_const_mul]
  rw [hLval, hRval] at hmono
  -- ## the ℓ⁶ arithmetic
  have hℓ6 : (ℓ ^ 6)⁻¹ * ℓ ^ 6 = 1 := inv_mul_cancel₀ (pow_ne_zero 6 (ne_of_gt hℓ))
  have hfin : 2 * ((ℓ ^ 3)⁻¹ * ((ℓ ^ 3)⁻¹ * J))
      ≤ C₀ * (2 * Q + (ℓ ^ 2)⁻¹ * Ki + (ℓ ^ 2)⁻¹ * Kj) := by
    have hm := mul_le_mul_of_nonneg_right hmono (by positivity : (0 : ℝ) ≤ (ℓ ^ 6)⁻¹)
    have e1 : (C₀ * (2 * (ℓ ^ 6 * Q) + (ℓ ^ 2)⁻¹ * (ℓ ^ 6 * Ki + ℓ ^ 6 * Kj))) * (ℓ ^ 6)⁻¹
        = C₀ * (2 * Q + (ℓ ^ 2)⁻¹ * Ki + (ℓ ^ 2)⁻¹ * Kj) := by
      have h6 : ℓ ^ 6 ≠ 0 := pow_ne_zero 6 (ne_of_gt hℓ)
      have h2 : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hℓ)
      field_simp
      ring
    have e2 : (2 * J) * (ℓ ^ 6)⁻¹ = 2 * ((ℓ ^ 3)⁻¹ * ((ℓ ^ 3)⁻¹ * J)) := by
      have h3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
      have h6 : ℓ ^ 6 ≠ 0 := pow_ne_zero 6 (ne_of_gt hℓ)
      field_simp
    rw [e1, e2] at hm
    exact hm
  exact hfin

/-- **The CS pair-mass inequality with the card factor** (`Design note §14.1`): for every `ℓ`
with `R ≤ ℓ·chiR0` and every `n`, the condensate pair mass is bounded by the `4Q`-square plus
`n·ℓ⁻²` times the excited mass. -/
theorem ppMass_le_q4Mass_add_card_mul_cnPlus {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v)
    (hvrad : BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1 MeasureTheory.volume)
    (R : ℝ) (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hav : 0 < BoseGases.a v)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ℓ : ℝ), 0 < ℓ → R ≤ ℓ * Submission.BoseGases.chiR0 →
      ∀ (n : ℕ) {Φ : Submission.BoseGases.X n → ℝ}, Continuous Φ →
      Work.BoseFixB3.CS.ppMass ℓ Φ
        ≤ C * (Work.BoseFixB3.CS.q4Mass ℓ (Submission.BoseGases.omC (Classical.choose h))
                (Submission.BoseGases.wLoc ℓ v 0) Φ
            + (n : ℝ) * ((ℓ ^ 2)⁻¹ * Submission.BoseGases.cnPlus ℓ Φ)) := by
  classical
  obtain ⟨C₀, hC₀0, hfib⟩ := ppMass_fibre_le_outer hv hvrad hv1 R hR hv_supp hav h
  refine ⟨C₀, hC₀0, ?_⟩
  intro ℓ hℓ hRℓ n Φ hΦc
  rcases n with _ | _ | m
  · -- ## `n = 0`
    have hp0 : Submission.BoseGases.pairSet 0 = (∅ : Finset (Fin 0 × Fin 0)) := by decide
    have hz : Work.BoseFixB3.CS.ppMass ℓ (Φ : X 0 → ℝ) = 0 := by
      rw [Work.BoseFixB3.CS.ppMass, hp0, Finset.sum_empty]
      ring
    rw [hz]
    refine mul_nonneg hC₀0 (add_nonneg ?_ ?_)
    · rw [Work.BoseFixB3.CS.q4Mass, hp0]
      simp
    · refine mul_nonneg (by norm_num) (mul_nonneg (by positivity) (Work.BoseFixB3.cnPlus_nonneg Φ))
  · -- ## `n = 1`
    have hp1 : Submission.BoseGases.pairSet 1 = (∅ : Finset (Fin 1 × Fin 1)) := by decide
    have hz : Work.BoseFixB3.CS.ppMass ℓ (Φ : X 1 → ℝ) = 0 := by
      rw [Work.BoseFixB3.CS.ppMass, hp1, Finset.sum_empty]
      ring
    rw [hz]
    refine mul_nonneg hC₀0 (add_nonneg ?_ ?_)
    · rw [Work.BoseFixB3.CS.q4Mass, hp1]
      simp
    · refine mul_nonneg (by norm_num) (mul_nonneg (by positivity) (Work.BoseFixB3.cnPlus_nonneg Φ))
  · -- ## `n = m + 2`
    set Q4 : ℝ := Work.BoseFixB3.CS.q4Mass ℓ (Submission.BoseGases.omC (Classical.choose h))
        (Submission.BoseGases.wLoc ℓ v 0) Φ with hQ4def
    set CN : ℝ := Submission.BoseGases.cnPlus ℓ Φ with hCNdef
    have hCNnn : 0 ≤ CN := by rw [hCNdef]; exact Work.BoseFixB3.cnPlus_nonneg Φ
    have hQ4nn : 0 ≤ Q4 := by
      rw [hQ4def, Work.BoseFixB3.CS.q4Mass]
      exact Finset.sum_nonneg (fun q hq => MeasureTheory.integral_nonneg_of_ae
        (Filter.Eventually.of_forall (fun x => mul_nonneg (sq_nonneg _)
          (Work.BoseFixR.wLoc_zero_nonneg hv ℓ (x q.1) (x q.2)))))
    have hpairle : ∀ p ∈ Submission.BoseGases.pairSet (m + 2),
        2 * ((ℓ ^ 3)⁻¹ * ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (m + 2) ℓ,
            (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2))
        ≤ C₀ * (2 * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
              (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h))
                  Φ (p.1, p.2) x) ^ 2
                * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
            + (ℓ ^ 2)⁻¹ * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
                (Submission.BoseGases.aQ ℓ p.1 Φ x) ^ 2)
            + (ℓ ^ 2)⁻¹ * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
                (Submission.BoseGases.aQ ℓ p.2 Φ x) ^ 2)) :=
      fun p hp => pair_integrated_le hv hvrad hv1 R hR hv_supp hav h hC₀0 hfib hℓ hRℓ p.1 p.2
        (Finset.mem_filter.mp hp).2 hΦc
    have hsum := Finset.sum_le_sum hpairle
    -- the value of the left-hand sum
    have hL : (∑ p ∈ Submission.BoseGases.pairSet (m + 2),
        2 * ((ℓ ^ 3)⁻¹ * ((ℓ ^ 3)⁻¹ * ∫ x in Submission.BoseGases.abox (m + 2) ℓ,
            (Submission.BoseGases.aP ℓ p.1 (Submission.BoseGases.aP ℓ p.2 Φ) x) ^ 2)))
        = 2 * Work.BoseFixB3.CS.ppMass ℓ Φ := by
      rw [Work.BoseFixB3.CS.ppMass, ← Finset.mul_sum]
      congr 1
      rw [← Finset.mul_sum, ← Finset.mul_sum]
      ring
    -- the value of the right-hand sum
    have hR : (∑ p ∈ Submission.BoseGases.pairSet (m + 2),
          C₀ * (2 * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
                (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h))
                    Φ (p.1, p.2) x) ^ 2
                  * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))
              + (ℓ ^ 2)⁻¹ * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
                  (Submission.BoseGases.aQ ℓ p.1 Φ x) ^ 2)
              + (ℓ ^ 2)⁻¹ * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
                  (Submission.BoseGases.aQ ℓ p.2 Φ x) ^ 2)))
        = C₀ * (2 * Q4 + 2 * (((m : ℝ) + 1) * ((ℓ ^ 2)⁻¹ * CN))) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have h3 : (∑ p ∈ Submission.BoseGases.pairSet (m + 2),
            2 * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
              (Submission.BoseGases.q4B ℓ (Submission.BoseGases.omC (Classical.choose h))
                  Φ (p.1, p.2) x) ^ 2
                * Submission.BoseGases.wLoc ℓ v 0 (x p.1) (x p.2))) = 2 * Q4 := by
        rw [← Finset.mul_sum, hQ4def, Work.BoseFixB3.CS.q4Mass]
      have h1 : (∑ p ∈ Submission.BoseGases.pairSet (m + 2),
            (ℓ ^ 2)⁻¹ * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
              (Submission.BoseGases.aQ ℓ p.1 Φ x) ^ 2))
          = (ℓ ^ 2)⁻¹ * (((m : ℝ) + 1) * CN) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [hCNdef, Submission.BoseGases.cnPlus]
        have hsf := Submission.BoseGases.sum_pairSet_first_eq (m + 2)
            (fun a : Fin (m + 2) => ∫ x in Submission.BoseGases.abox (m + 2) ℓ,
              (Submission.BoseGases.aQ ℓ a Φ x) ^ 2)
        rw [hsf]
        push_cast
        ring
      have h2 : (∑ p ∈ Submission.BoseGases.pairSet (m + 2),
            (ℓ ^ 2)⁻¹ * (∫ x in Submission.BoseGases.abox (m + 2) ℓ,
              (Submission.BoseGases.aQ ℓ p.2 Φ x) ^ 2))
          = (ℓ ^ 2)⁻¹ * (((m : ℝ) + 1) * CN) := by
        rw [← Finset.mul_sum]
        congr 1
        rw [hCNdef, Submission.BoseGases.cnPlus]
        have hss := Submission.BoseGases.sum_pairSet_second_eq (m + 2)
            (fun a : Fin (m + 2) => ∫ x in Submission.BoseGases.abox (m + 2) ℓ,
              (Submission.BoseGases.aQ ℓ a Φ x) ^ 2)
        rw [hss]
        push_cast
        ring
      rw [h3, h1, h2]
      ring
    rw [hL, hR] at hsum
    -- divide by `2` and compare the cardinality coefficients
    have hgoal : Work.BoseFixB3.CS.ppMass ℓ Φ ≤ C₀ * (Q4 + ((m : ℝ) + 1) * ((ℓ ^ 2)⁻¹ * CN)) := by
      have hX : C₀ * (2 * Q4 + 2 * (((m : ℝ) + 1) * ((ℓ ^ 2)⁻¹ * CN)))
          = 2 * (C₀ * (Q4 + ((m : ℝ) + 1) * ((ℓ ^ 2)⁻¹ * CN))) := by ring
      rw [hX] at hsum
      linarith [hsum]
    have hstep : C₀ * (Q4 + ((m : ℝ) + 1) * ((ℓ ^ 2)⁻¹ * CN))
        ≤ C₀ * (Q4 + ((m : ℝ) + 2) * ((ℓ ^ 2)⁻¹ * CN)) := by
      refine mul_le_mul_of_nonneg_left ?_ hC₀0
      refine add_le_add le_rfl ?_
      exact mul_le_mul_of_nonneg_right (by linarith)
        (mul_nonneg (by positivity) hCNnn)
    have hfin := le_trans hgoal hstep
    have hcast : (((m + 2 : ℕ)) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    exact hfin

end

end Work.BoseFixB3.CS.Pieces
