import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.ZPLatticeAux
import Submission.Work.BoseFixR.LatGreen.FoldDefs
import Submission.Work.BoseRowsFS.W1_pair_integrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.ZPW1Facts` — the kinematic facts about `W₁ = W(1−ω)` at the box scale

This is the package of properties of the honest one-body kernel
`W₁ = W₁At v h μ = W1fun v h (ell v μ) = wScaled ℓ (g₀ v h)` (`ℓ = ℓ(μ) = sideAt μ (a v)`)
that the zero-point/mass rows of the Bogoliubov chapter consume: evenness, support in `ball 0 R`,
`L¹`, a.e. nonnegativity, Bochner-integrability of the Coulomb pair kernel `W₁⊗W₁/‖x−y‖`, the
large-box condition `4R ≤ ℓ(μ)`, and the two-sided mass bound
`8π·a v ≤ ∫W₁ ≤ 16π·a v`.

All the analytic content is already on the shelf; the point of this lemma is that a *single*
diluteness threshold `ε₀` makes all of it hold simultaneously on the whole admissible set
`Work.BoseBoxFix.Adm v ε₀`:

* `existsAdmRegime` (from `Submission/Work/BoseBogFS/existsAdmRegime.lean`) gives the régime
  `R ≤ ℓ·chiR0`, `R/ℓ ≤ r₁`, `C·(R/ℓ)² ≤ 1/2` from one threshold, where `C, r₁` are the Taylor
  data of `χ⋆χ` at `0` (`Submission.BoseGases.conv3chi_second_order_bound`,
  `Submission/ConvChiBound.lean`);
* `exists_adm_ell_ge` (same module) gives `4R ≤ ℓ(μ)` from another threshold; the two are merged
  by taking `min`;
* the five structural/dynamical conjuncts are `Work.BoseFixR.isEven_W1fun`,
  `Work.BoseFixR.tsupport_W1fun_subset`, `Submission.BoseGases.wScaled_g0_integrable`,
  `Submission.BoseGases.wScaled_g0_nonneg_ae` and `Work.BoseRowsFS.W1_pair_integrable`;
* the mass bound is `W1_mass_bounds` (same namespace as this lemma), whose upper half
  `8πa(1 + 2C(R/ℓ)²)` is rounded to `16πa` with the régime inequality `C(R/ℓ)² ≤ 1/2`.
-/

namespace Work.BoseBogFS

open MeasureTheory

theorem ZPW1Facts :
    ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ},
      0 < R → (∀ x, 0 ≤ v x) → _root_.BoseGases.IsRadial v → tsupport v ⊆ Metric.ball 0 R →
      0 < _root_.BoseGases.a v →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        (∀ x : EuclideanSpace ℝ (Fin 3),
            Work.BoseBogFS.W1At v h μ (-x) = Work.BoseBogFS.W1At v h μ x) ∧
        tsupport (Work.BoseBogFS.W1At v h μ)
          ⊆ Metric.ball 0 R ∧
        MeasureTheory.Integrable (Work.BoseBogFS.W1At v h μ) ∧
        (∀ᵐ x, 0 ≤ Work.BoseBogFS.W1At v h μ x) ∧
        MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Work.BoseBogFS.W1At v h μ p.1 * Work.BoseBogFS.W1At v h μ p.2 / ‖p.1 - p.2‖) ∧
        4 * R ≤ Work.BoseFixR.ell v μ ∧
        8 * Real.pi * _root_.BoseGases.a v
            ≤ ∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseBogFS.W1At v h μ x ∧
        (∫ x : EuclideanSpace ℝ (Fin 3), Work.BoseBogFS.W1At v h μ x)
            ≤ 16 * Real.pi * _root_.BoseGases.a v := by
  intro v h R hR hv hvrad hv_supp hav
  -- ## the Taylor data of `χ ⋆ χ` at `0`
  obtain ⟨C, hC0, r₁, hr₁, hT⟩ := Submission.BoseGases.conv3chi_second_order_bound
  -- ## the two diluteness thresholds
  obtain ⟨ε₁, hε₁, hreg⟩ :=
    existsAdmRegime (v := v) (R := R) (C := C) (r₁ := r₁) hR hav hC0 hr₁
  obtain ⟨ε₂, hε₂, hell⟩ :=
    exists_adm_ell_ge (v := v) hav (M := 4 * R) (by linarith)
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_⟩
  intro μ hμ
  -- unpack `Adm` at the two thresholds
  have hμ1 : Work.BoseBoxFix.Adm v ε₁ μ :=
    ⟨hμ.1, le_trans hμ.2.1 (min_le_left _ _), hμ.2.2⟩
  have hμ2 : Work.BoseBoxFix.Adm v ε₂ μ :=
    ⟨hμ.1, le_trans hμ.2.1 (min_le_right _ _), hμ.2.2⟩
  obtain ⟨hRℓ, hreg', hcond⟩ := hreg μ hμ1
  have h4R : 4 * R ≤ Work.BoseFixR.ell v μ := hell μ hμ2
  have hℓ : 0 < Work.BoseFixR.ell v μ := by linarith
  -- ## the mass bounds
  obtain ⟨hlo, hhi⟩ :=
    W1_mass_bounds (v := v) (h := h) (R := R) (ℓ := Work.BoseFixR.ell v μ)
      (r₁ := r₁) (C := C) hR hv hvrad hv_supp hC0 hr₁ hℓ hT hreg' hcond
  -- ## the upper mass bound rounded to `16πa`
  have ha0 : 0 < _root_.BoseGases.a v := hav
  have hfac : 1 + 2 * C * (R / Work.BoseFixR.ell v μ) ^ 2 ≤ 2 := by linarith
  have hπ : 0 < Real.pi := Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, h4R, ?_, ?_⟩
  · -- evenness
    intro x
    exact Work.BoseFixR.isEven_W1fun h hvrad (Work.BoseFixR.ell v μ) x
  · -- support
    exact Work.BoseFixR.tsupport_W1fun_subset h hv_supp (Work.BoseFixR.ell v μ)
  · -- `L¹`
    exact Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  · -- a.e. nonnegativity
    exact Submission.BoseGases.wScaled_g0_nonneg_ae hR hv hvrad hv_supp h
  · -- Coulomb pair integrability
    exact Work.BoseRowsFS.W1_pair_integrable h hR hℓ hv hvrad hv_supp hRℓ
  · -- lower mass bound
    exact hlo
  · -- upper mass bound
    have hmono : 8 * Real.pi * _root_.BoseGases.a v
          * (1 + 2 * C * (R / Work.BoseFixR.ell v μ) ^ 2)
        ≤ 16 * Real.pi * _root_.BoseGases.a v := by
      have h8 : 0 ≤ 8 * Real.pi * _root_.BoseGases.a v := by positivity
      nlinarith [hfac, h8]
    exact le_trans hhi hmono

end Work.BoseBogFS
