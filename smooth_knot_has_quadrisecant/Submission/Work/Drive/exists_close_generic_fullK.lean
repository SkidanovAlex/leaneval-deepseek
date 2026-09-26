import Mathlib
import Submission.Work.Drive.genericFullDense
import Submission.Work.Drive.qwDefs
import Submission.Work.Drive.qBad_interior_empty
import Submission.Work.Drive.quadrisecantIsolated_of_not_qBad_v2

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

/-! ## Closedness of the quadrisecant-isolation bad set (local copy, strict box)

The module `Submission.Work.Drive.qBad_isClosed` cannot currently be imported: it depends on
`Submission.Work.Drive.qBox_isCompact`, whose proof of closedness of `qBox` uses the *older, weaker*
total-length bound `qB τ - qA τ ≤ 2π`, whereas the definition in `qwDefs` carries the *strict* bound
`qB τ - qA τ ≤ 2π - 1/(k+1)`.  The statement of closedness is nevertheless available, and the proof
is the same compact-projection argument; we reproduce it here against `qBox_compact` (the version
matching the definition). -/

/-- The `i`-th partial of the four-point collinearity map, packaged in `WithLp 2 (Space × Space)`,
depends continuously on the coefficient/window pair. -/
private lemma continuous_qPartialW_K {r : ℝ → Space} (hr : IsSmoothKnot r) (i : Fin 4) :
    Continuous (fun p : Coeff × QP => qPartialW r p i) :=
  Continuous.comp (WithLp.prod_continuous_toLp 2 Space Space)
    (contDiff_qPartial_apply hr i).continuous

/-- Each entry of the Gram matrix of the partials is continuous. -/
private lemma continuous_gram_apply_K {r : ℝ → Space} (hr : IsSmoothKnot r) (i j : Fin 4) :
    Continuous (fun p : Coeff × QP => Matrix.gram ℝ (qPartialW r p) i j) := by
  simp only [Matrix.gram_apply]
  exact Continuous.inner (continuous_qPartialW_K hr i) (continuous_qPartialW_K hr j)

/-- The Gram matrix of the partials depends continuously on the coefficient/window pair. -/
private lemma continuous_gram_K {r : ℝ → Space} (hr : IsSmoothKnot r) :
    Continuous (fun p : Coeff × QP => Matrix.gram ℝ (qPartialW r p)) := by
  change Continuous (fun p : Coeff × QP => fun i j => Matrix.gram ℝ (qPartialW r p) i j)
  rw [continuous_pi_iff]
  intro i
  rw [continuous_pi_iff]
  intro j
  exact continuous_gram_apply_K hr i j

/-- **The Gram determinant `qGram` is continuous.** -/
private lemma continuous_qGram_K {r : ℝ → Space} (hr : IsSmoothKnot r) :
    Continuous (fun p : Coeff × QP => qGram r p) := by
  simpa only [qGram] using (continuous_gram_K hr).matrix_det

/-- **The data map `p ↦ (triplet r p, qGram r p)` is continuous**, so its zero set is closed. -/
private lemma continuous_triplet_gram_K {r : ℝ → Space} (hr : IsSmoothKnot r) :
    Continuous (fun p : Coeff × QP => (triplet r p, qGram r p)) :=
  (contDiff_triplet hr).continuous.prodMk (continuous_qGram_K hr)

/-- **The quadrisecant-isolation bad set is closed** (strict-box form). -/
private theorem qBad_isClosed' {r : ℝ → Space} (hr : IsSmoothKnot r) (ρ : ℝ) (k : ℕ) :
    IsClosed (qBad r ρ k) := by
  have hcont : Continuous (fun p : Coeff × QP => (triplet r p, qGram r p)) :=
    continuous_triplet_gram_K hr
  have hcomp : IsCompact
      ((Kv ρ ×ˢ qBox k) ∩ {p : Coeff × QP | (triplet r p, qGram r p) = 0}) :=
    ((isCompact_Kv ρ).prod (qBox_compact k)).inter_right (isClosed_singleton.preimage hcont)
  have himg : Prod.fst '' ((Kv ρ ×ˢ qBox k) ∩ {p : Coeff × QP | (triplet r p, qGram r p) = 0})
      = qBad r ρ k := by
    ext c
    constructor
    · rintro ⟨p, ⟨hp, hp0⟩, rfl⟩
      obtain ⟨hp1, hp2⟩ := hp
      obtain ⟨h1, h2⟩ := Prod.mk_eq_zero.mp hp0
      exact ⟨hp1, p.2, hp2, h1, h2⟩
    · rintro ⟨hc, τ, hτ, h1, h2⟩
      exact ⟨(c, τ), ⟨⟨hc, hτ⟩, by simp [h1, h2]⟩, rfl⟩
  rw [← himg]
  exact (hcomp.image continuous_fst).isClosed

/-- The combined bad family of the Baire assembly: the four families of
`Work.Drive.badFamFull` together with the quadrisecant-isolation bad sets `qBad`. -/
private def badFamFullK (r : ℝ → Space) (r₀ : ℝ) : BadIdxFull ⊕ ℕ → Set Coeff
  | Sum.inl i => badFamFull r r₀ i
  | Sum.inr k => qBad r r₀ k

end

open Work.Drive LeanEval.KnotTheory.Quadrisecant in
/-- **The Baire assembly with the quadrisecant-isolation bad family.**

A copy of the proof of `Work.Drive.exists_close_generic_full`
(`Submission/Work/Drive/genericFullDense.lean`) with one further countable family of bad sets added
to the intersection: the quadrisecant-isolation bad sets `k ↦ qBad r₁ r₀ k`, where `r₁` is the
first (inflection-free) approximant and `r₀` the coefficient radius of the construction.

The inputs are the closedness `Work.Drive.qBad_isClosed`, the empty interior
`Work.Drive.qBad_interior_empty` and the passage
`Work.Drive.quadrisecantIsolated_of_not_qBad_v2` converting "`c` avoids every `qBad r₁ r₀ k`" into
`QuadrisecantIsolated (pertV r₁ c)`.  Everything else (the triangle/parallel bad sets `badABC`,
`badPsi`, the five-collinear sets `bad5C` and the degenerate tangent-chord sets `tcBad`, the
constants `r₀`, `Kc`, the Baire step `Work.Drive.exists_coeff_avoiding`, and the closeness estimates)
is copied unchanged from `Work.Drive.exists_close_generic_full`. -/
theorem exists_close_generic_fullK {r : ℝ → Space} (hr : IsSmoothKnot r) (ε : ℝ) (hε : 0 < ε) :
    ∃ r' : ℝ → Space, IsSmoothKnot r' ∧ TorusGeneralPositionTransverse r' ∧
      (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) ∧ NoFiveCollinear r' ∧
      TangentChordGP r' ∧ QuadrisecantIsolated r' ∧
      ∀ t : ℝ, ‖r' t - r t‖ < ε ∧ ‖velocity r' t - velocity r t‖ < ε := by
  classical
  -- step 1: first remove the inflections
  obtain ⟨r₁, h₁, hnoinfl₁, hclose₁⟩ := exists_close_nonzero_curvature hr (ε/2) (by linarith)
  have hnoinfl₁' : ∀ t : ℝ, cross3 (velocity r₁ t) (deriv (velocity r₁) t) ≠ 0 :=
    fun t => (linearIndependent_pair_iff_cross3_ne_zero _ _).mp (hnoinfl₁ t)
  -- step 2: nonvanishing curvature is preserved on a ball
  obtain ⟨ρ, hρpos, hρ⟩ := exists_curvPreserve_bound h₁ hnoinfl₁'
  -- step 3: the smallness constants
  obtain ⟨ε₀, hε₀pos, hsm⟩ := smallCorrectionKnot h₁
  set Kc : ℝ := max ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ 1 with hKcdef
  have hKcpos : 0 < Kc := lt_of_lt_of_le one_pos (le_max_right _ _)
  set r₀ : ℝ := min (min (ρ/2) (ε₀/(100*Kc))) (ε/(100*Kc)) with hr₀def
  have hr₀pos : 0 < r₀ := lt_min (lt_min (by positivity) (by positivity)) (by positivity)
  have hr₀leρ : r₀ ≤ ρ := by
    have h2 : r₀ ≤ ρ/2 := le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have hr₀leε : r₀ ≤ ε/(100*Kc) := min_le_right _ _
  have hr₀leε₀ : r₀ ≤ ε₀/(100*Kc) := le_trans (min_le_left _ _) (min_le_right _ _)
  have hbound : ∀ c ∈ Kv r₀, ‖eCoeff c‖ ≤ Kc * r₀ := by
    intro c hc
    have hcn : ‖c‖ ≤ r₀ := by rw [Kv, Metric.mem_closedBall, dist_zero_right] at hc; exact hc
    have hop : ‖eCoeff c‖ ≤ ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ * ‖c‖ :=
      ContinuousLinearMap.le_opNorm (eCoeff : Coeff →L[ℝ] (Fin 9 → Space)) c
    have hkey : ‖(eCoeff : Coeff →L[ℝ] (Fin 9 → Space))‖ * ‖c‖ ≤ Kc * r₀ :=
      mul_le_mul (le_max_left _ _) hcn (norm_nonneg c)
        (le_trans (norm_nonneg _) (le_max_left _ _))
    linarith
  have hS : ∀ c ∈ Kv r₀, IsSmoothKnot (pertV r₁ c) := by
    intro c hc
    refine isSmoothKnot_pertV h₁ hε₀pos hsm ?_
    have h1 := hbound c hc
    have h2 : Kc * r₀ ≤ ε₀/100 := by
      have := mul_le_mul_of_nonneg_left hr₀leε₀ hKcpos.le
      rwa [show Kc * (ε₀/(100*Kc)) = ε₀/100 from by field_simp] at this
    linarith
  -- the curvature hypothesis for the tangent–chord bad set
  have hcurv : ∀ c ∈ Kv r₀, ∀ t : ℝ, cross3 (tcVel r₁ c t) (tcAcc r₁ c t) ≠ 0 := by
    intro c hc t
    rw [tcVel_eq_pertVelV, tcAcc_eq_deriv r₁ h₁.smooth c t]
    exact hρ c (mem_Kv_mono hr₀leρ hc) t
  -- step 4: the combined Baire step (the four bad families)
  have hclosed : ∀ i : BadIdxFull, IsClosed (badFamFull r₁ r₀ i) := by
    rintro (((j | j) | k) | k)
    · exact isClosed_badSet (isCompact_tripleSet j.1) (contDiff_stratABC h₁ j.2).continuous r₀
    · exact isClosed_badSet (isCompact_Kn j.1 (j.2 : ℝ)) (contDiff_stratPsi h₁).continuous r₀
    · exact bad5C_isClosed h₁ r₀ k
    · exact tcBad_isClosed h₁ r₀ k
  have hempty : ∀ i : BadIdxFull, interior (badFamFull r₁ r₀ i) = ∅ := by
    rintro (((j | j) | k) | k)
    · exact badABC_empty_interior h₁ hS jetSurj_holds j
    · exact badPsi_empty_interior h₁ hS jetSurj_holds j
    · exact bad5C_interior_empty h₁ hr₀pos hS k
    · exact tcBad_interior_empty h₁ hr₀pos hS hcurv k
  have hclosedK : ∀ i : BadIdxFull ⊕ ℕ, IsClosed (badFamFullK r₁ r₀ i) := by
    rintro (i | k)
    · exact hclosed i
    · exact qBad_isClosed' h₁ r₀ k
  have hemptyK : ∀ i : BadIdxFull ⊕ ℕ, interior (badFamFullK r₁ r₀ i) = ∅ := by
    rintro (i | k)
    · exact hempty i
    · exact qBad_interior_empty h₁ hr₀pos hS k
  obtain ⟨c, hcU, hgood⟩ := exists_coeff_avoiding hr₀pos (badFamFullK r₁ r₀) hclosedK hemptyK
  have hcKv : c ∈ Kv r₀ := interior_subset hcU
  have hgoodABC : ∀ (j : Fin 3) (k : ℕ) (w : ℝ × ℝ × ℝ),
      w ∈ tripleSet k → stratABC r₁ j (c, w) ≠ 0 := by
    intro j k w hw hzero
    exact hgood (Sum.inl (Sum.inl (Sum.inl (Sum.inl (k, j))))) ⟨hcKv, w, hw, hzero⟩
  have hgoodPsi : ∀ (k L : ℕ) (w : Cfg), w ∈ Kn k L → stratPsi r₁ (c, w) ≠ 0 := by
    intro k L w hw hzero
    exact hgood (Sum.inl (Sum.inl (Sum.inl (Sum.inr (k, L))))) ⟨hcKv, w, hw, hzero⟩
  have hgood5C : ∀ k : ℕ, c ∉ bad5C r₁ r₀ k := fun k => hgood (Sum.inl (Sum.inl (Sum.inr k)))
  have hgood5 : ∀ k : ℕ, c ∉ bad5 r₁ r₀ k :=
    fun k hk => hgood5C k (bad5_subset_bad5C hk)
  have hgoodTC : ∀ k : ℕ, c ∉ tcBad r₁ r₀ k := fun k => hgood (Sum.inl (Sum.inr k))
  have hgoodQ : ∀ k : ℕ, c ∉ qBad r₁ r₀ k := fun k => hgood (Sum.inr k)
  refine ⟨pertV r₁ c, hS c hcKv, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- torus transverse general position, from the pointwise condition
    refine torusGeneralPositionTransverse_of_pointwise ?_
    intro a b m ha hb hm hcol hdist
    have haI : a ∈ Set.Icc (0:ℝ) (2 * Real.pi) :=
      ⟨ha.1, le_of_lt (by simpa [period] using ha.2)⟩
    have hbI : b ∈ Set.Icc (0:ℝ) (2 * Real.pi) :=
      ⟨hb.1, le_of_lt (by simpa [period] using hb.2)⟩
    have hmI : m ∈ Set.Icc (0:ℝ) (2 * Real.pi) :=
      ⟨hm.1, le_of_lt (by simpa [period] using hm.2)⟩
    have ha2 : a < 2 * Real.pi := by simpa [period] using ha.2
    have hb2 : b < 2 * Real.pi := by simpa [period] using hb.2
    have hm2 : m < 2 * Real.pi := by simpa [period] using hm.2
    have hab : a ≠ b := fun h => hdist.1 (by rw [h, sub_self])
    have ham : a ≠ m := fun h => hdist.2.1 (by rw [h, sub_self])
    have hbm : b ≠ m := fun h => hdist.2.2 (by rw [h, sub_self])
    have hcsep1 : 0 < csep a b := by
      have hlt : |a - b| < 2 * Real.pi := by
        rw [abs_lt]; exact ⟨by linarith [haI.1, hb2], by linarith [ha2, hbI.1]⟩
      exact lt_min (abs_pos.mpr (sub_ne_zero.mpr hab)) (sub_pos.mpr hlt)
    have hcsep2 : 0 < csep a m := by
      have hlt : |a - m| < 2 * Real.pi := by
        rw [abs_lt]; exact ⟨by linarith [haI.1, hm2], by linarith [ha2, hmI.1]⟩
      exact lt_min (abs_pos.mpr (sub_ne_zero.mpr ham)) (sub_pos.mpr hlt)
    have hcsep3 : 0 < csep b m := by
      have hlt : |b - m| < 2 * Real.pi := by
        rw [abs_lt]; exact ⟨by linarith [hbI.1, hm2], by linarith [hb2, hmI.1]⟩
      exact lt_min (abs_pos.mpr (sub_ne_zero.mpr hbm)) (sub_pos.mpr hlt)
    obtain ⟨k, hk⟩ := exists_div_succ_le (lt_min (lt_min hcsep1 hcsep2) hcsep3)
    have hk1 : (1:ℝ)/(k+1) ≤ csep a b :=
      hk.trans (le_trans (min_le_left _ _) (min_le_left _ _))
    have hk2 : (1:ℝ)/(k+1) ≤ csep a m :=
      hk.trans (le_trans (min_le_left _ _) (min_le_right _ _))
    have hk3 : (1:ℝ)/(k+1) ≤ csep b m := hk.trans (min_le_right _ _)
    have hw : (a, b, m) ∈ tripleSet k := ⟨haI, hbI, hmI, hk1, hk2, hk3⟩
    have hA := hgoodABC 0 k (a, b, m) hw
    have hB := hgoodABC 1 k (a, b, m) hw
    have hM := hgoodABC 2 k (a, b, m) hw
    -- the three tangent–chord vectors are nonzero
    have hyA : cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      intro hzero
      have hz : stratA r₁ (c, (a, b, m)) = 0 := by rw [stratA_apply, hcol, hzero]; rfl
      exact hA hz
    have hyB : cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      intro hzero
      have hz : stratB r₁ (c, (a, b, m)) = 0 := by rw [stratB_apply, hcol, hzero]; rfl
      exact hB hz
    have hyM : cross3 (pertVelV r₁ c m) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      intro hzero
      have hz : stratM r₁ (c, (a, b, m)) = 0 := by rw [stratM_apply, hcol, hzero]; rfl
      exact hM hz
    have hya : cross3 (velocity (pertV r₁ c) a) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      rwa [← velocity_pertV h₁.smooth c a] at hyA
    have hyb : cross3 (velocity (pertV r₁ c) b) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      rwa [← velocity_pertV h₁.smooth c b] at hyB
    have hym : cross3 (velocity (pertV r₁ c) m) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
      rwa [← velocity_pertV h₁.smooth c m] at hyM
    -- the tangent–chord vectors are not all parallel
    have hnoPar : ¬ ∃ la mu : ℝ,
        cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b) =
          la • cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b) ∧
        cross3 (pertVelV r₁ c m) (pertV r₁ c a - pertV r₁ c b) =
          mu • cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b) := by
      rintro ⟨la, mu, hla, hmu⟩
      obtain ⟨j, hj⟩ := exists_nat_ge (max |la| |mu|)
      have hmem : mkCfg la mu a b m ∈ Kn k j :=
        mem_Kn_mkCfg (le_trans (le_max_left _ _) hj) (le_trans (le_max_right _ _) hj)
          haI hbI hmI hk1 hk2 hk3
      have hzero : stratPsi r₁ (c, mkCfg la mu a b m) = 0 := by
        rw [stratPsi_apply, cfgA_mkCfg, cfgB_mkCfg, cfgM_mkCfg, cfgLam_mkCfg, cfgMu_mkCfg,
          hcol, hla, hmu]
        simp
      exact hgoodPsi k j _ hmem hzero
    have hmb : pertV r₁ c m - pertV r₁ c b ≠ 0 := hdist.2.2
    refine ⟨?_, ?_⟩
    · -- rank two
      have hcp0 : collParam a b m (0 : Fin 3) = a := rfl
      have hcp1 : collParam a b m (1 : Fin 3) = b := rfl
      have hcp2 : collParam a b m (2 : Fin 3) = m := rfl
      have hpar : (¬ ∃ la : ℝ, cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b) =
          la • cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b)) ∨
          (¬ ∃ mu : ℝ, cross3 (pertVelV r₁ c m) (pertV r₁ c a - pertV r₁ c b) =
          mu • cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b)) := by
        by_contra hcon
        push_neg at hcon
        exact hnoPar ⟨hcon.1.choose, hcon.2.choose, hcon.1.choose_spec, hcon.2.choose_spec⟩
      rcases hpar with hpar | hpar
      · have hc : cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
          intro hzero
          exact hpar ⟨0, by rw [hzero, zero_smul]⟩
        refine (rank_two_criterion_at_collinearity_zero (r := pertV r₁ c) (a := a) (b := b)
          (m := m) hdist.1 hdist.2.1 hmb hcol).mpr ⟨0, 1, by norm_num, ?_⟩
        rw [hcp0, hcp1, velocity_pertV h₁.smooth c a, velocity_pertV h₁.smooth c b]
        refine (linearIndependent_pair_iff_cross3_ne_zero _ _).mpr ?_
        intro hzero
        have hzero' : cross3 (cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b))
            (cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b)) = 0 := by
          rw [cross3_anticomm, hzero, neg_zero]
        rcases (cross3_eq_zero_iff_smul_local
          (u := cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b))
          (v := cross3 (pertVelV r₁ c a) (pertV r₁ c a - pertV r₁ c b))).mp hzero' with h | h
        · exact hyB h
        · exact hpar ⟨h.choose, h.choose_spec⟩
      · have hc : cross3 (pertVelV r₁ c m) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := by
          intro hzero
          exact hpar ⟨0, by rw [hzero, zero_smul]⟩
        refine (rank_two_criterion_at_collinearity_zero (r := pertV r₁ c) (a := a) (b := b)
          (m := m) hdist.1 hdist.2.1 hmb hcol).mpr ⟨1, 2, by decide, ?_⟩
        rw [hcp1, hcp2, velocity_pertV h₁.smooth c b, velocity_pertV h₁.smooth c m]
        refine (linearIndependent_pair_iff_cross3_ne_zero _ _).mpr ?_
        intro hzero
        rcases (cross3_eq_zero_iff_smul_local
          (u := cross3 (pertVelV r₁ c b) (pertV r₁ c a - pertV r₁ c b))
          (v := cross3 (pertVelV r₁ c m) (pertV r₁ c a - pertV r₁ c b))).mp hzero with h | h
        · exact hyB h
        · exact hpar ⟨h.choose, h.choose_spec⟩
    · -- endpoint tangents off the chord
      obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ,
          pertV r₁ c a - pertV r₁ c m = ρ • (pertV r₁ c a - pertV r₁ c b) := by
        have hcol' : cross3 (pertV r₁ c a - pertV r₁ c b) (pertV r₁ c a - pertV r₁ c m) = 0 := by
          rwa [collinearityValue_eq] at hcol
        rcases (cross3_eq_zero_iff_smul_local (u := pertV r₁ c a - pertV r₁ c b)
          (v := pertV r₁ c a - pertV r₁ c m)).mp hcol' with h | h
        · exact absurd h hdist.1
        · exact h
      have hρ0 : ρ ≠ 0 := by
        intro h0
        rw [h0, zero_smul] at hρ
        exact hdist.2.1 hρ
      have hρ1 : ρ ≠ 1 := by
        intro h1
        have h2 : pertV r₁ c a - pertV r₁ c m = pertV r₁ c a - pertV r₁ c b := by
          rw [hρ, h1, one_smul]
        have h5 := congrArg (fun x : Space => pertV r₁ c a - x) h2
        rw [sub_sub_cancel, sub_sub_cancel] at h5
        exact hdist.2.2 (by rw [h5, sub_self])
      have hρm : pertV r₁ c b - pertV r₁ c m = (ρ - 1) • (pertV r₁ c a - pertV r₁ c b) := by
        have h1 : pertV r₁ c b - pertV r₁ c m
            = -(pertV r₁ c a - pertV r₁ c b) + (pertV r₁ c a - pertV r₁ c m) := by abel
        rw [h1, hρ, sub_smul, one_smul]
        abel
      have hρm0 : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
      have hya' : cross3 (velocity (pertV r₁ c) a) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := hya
      have hyb' : cross3 (velocity (pertV r₁ c) b) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := hyb
      have hym' : cross3 (velocity (pertV r₁ c) m) (pertV r₁ c a - pertV r₁ c b) ≠ 0 := hym
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [cross3_anticomm]; exact neg_ne_zero.mpr hya'
      · rw [cross3_anticomm]; exact neg_ne_zero.mpr hyb'
      · rw [hρ, cross3_smul_left]
        exact smul_ne_zero hρ0 (by rw [cross3_anticomm]; exact neg_ne_zero.mpr hya')
      · rw [hρ, cross3_smul_left]
        exact smul_ne_zero hρ0 (by rw [cross3_anticomm]; exact neg_ne_zero.mpr hym')
      · rw [hρm, cross3_smul_left]
        exact smul_ne_zero hρm0 (by rw [cross3_anticomm]; exact neg_ne_zero.mpr hyb')
      · rw [hρm, cross3_smul_left]
        exact smul_ne_zero hρm0 (by rw [cross3_anticomm]; exact neg_ne_zero.mpr hym')
  · -- the curvature is preserved
    intro t
    have hcn : ‖c‖ ≤ r₀ := by
      have hc' := hcKv
      rw [Kv, Metric.mem_closedBall, dist_zero_right] at hc'
      exact hc'
    have hρc : c ∈ Kv ρ := by
      rw [Kv, Metric.mem_closedBall, dist_zero_right]
      linarith
    have h := hρ c hρc t
    have hvel : (fun s : ℝ => pertVelV r₁ c s) = velocity (pertV r₁ c) :=
      funext fun s => (velocity_pertV h₁.smooth c s).symm
    have h' : cross3 (velocity (pertV r₁ c) t) (deriv (velocity (pertV r₁ c)) t) ≠ 0 := by
      rw [← hvel]
      exact h
    exact (linearIndependent_pair_iff_cross3_ne_zero _ _).mpr h'
  · -- no five collinear points
    exact noFiveCollinear_of_not_bad5 hcKv hgood5
  · -- tangent-chord general position
    exact tangentChordGP_of_no_tcBad h₁ (hS c hcKv) hcKv hgoodTC
  · -- quadrisecant isolation
    exact quadrisecantIsolated_of_not_qBad_v2 h₁ hcKv (hS c hcKv) hgoodQ
  · -- closeness
    intro t
    have hb1 : ‖eCoeff c‖ ≤ Kc * r₀ := hbound c hcKv
    have hb2 : Kc * r₀ ≤ ε/100 := by
      have := mul_le_mul_of_nonneg_left hr₀leε hKcpos.le
      rwa [show Kc * (ε/(100*Kc)) = ε/100 from by field_simp] at this
    constructor
    · have hdiff : pertV r₁ c t - r t = perturbCorr (eCoeff c) t + (r₁ t - r t) := by
        simp [pertV, perturb]
        abel
      rw [hdiff]
      have h2 : ‖perturbCorr (eCoeff c) t‖ ≤ 9 * ‖eCoeff c‖ := norm_perturbCorr_le _ _
      have h5 : ‖r₁ t - r t‖ < ε/2 := (hclose₁ t).1
      calc ‖perturbCorr (eCoeff c) t + (r₁ t - r t)‖
          ≤ ‖perturbCorr (eCoeff c) t‖ + ‖r₁ t - r t‖ := norm_add_le _ _
        _ < ε := by linarith
    · have hdiff : velocity (pertV r₁ c) t - velocity r t
          = perturbVelCorr (eCoeff c) t + (velocity r₁ t - velocity r t) := by
        rw [velocity_pertV h₁.smooth c t]
        simp [pertVelV, perturbVel]
        abel
      rw [hdiff]
      have h2 : ‖perturbVelCorr (eCoeff c) t‖ ≤ 36 * ‖eCoeff c‖ := norm_perturbVelCorr_le _ _
      have h5 : ‖velocity r₁ t - velocity r t‖ < ε/2 := (hclose₁ t).2
      calc ‖perturbVelCorr (eCoeff c) t + (velocity r₁ t - velocity r t)‖
          ≤ ‖perturbVelCorr (eCoeff c) t‖ + ‖velocity r₁ t - velocity r t‖ := norm_add_le _ _
        _ < ε := by linarith

end Work.Drive
