import ChallengeDeps
import Submission.Work.BoseBogFS.highMode_arith
import Submission.Work.BoseBogFS.scaleRow_of_fsParams
import Submission.Work.BoseBoxFock.AllDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.hZP_highMode` — the high-momentum mode domination

The target is the `ζ_k < 1` branch of the pointwise cut comparison of
`Work.BoseBogFS.hZP_of_lattice` (see
`Submission/Work/BoseBogFS/FINDING_hZP_of_lattice_plan.md` §0/§1): every mode whose UV cut
factor is strictly below one satisfies `2·|ρ·Ŵ₁(F.kmom k)| ≤ E.tau k`.

The proof is assembled from three proved pieces plus the view's pins:

* the cut factor `uvCut fu' Λ p < 1` gives `p > Λ` (`LowCut.one`), hence — with the view
  cut data `4·(K_L√(μa)) ≤ Λ` — the momentum `p` sits strictly above the first kink
  `(sℓ)⁻¹` of the smoothed symbol by at least `(4K_L − 1)·√(μa)`;
* `Work.BoseBogFS.scaleRow_of_fsParams` (delegated, proved) supplies the three scale rows
  `(sℓ)⁻¹ ≤ √(μa)`, `1024 ≤ K_L`, `ε_T ≤ 1/2` from the `FSParamsView` pins alone;
* `Work.BoseBogFS.tauSm_ge_kink` turns the kink position into `E.tau k ≥
  (1−ε_T)·(max 0 (p − (sℓ)⁻¹))²`, and `Work.BoseBogFS.highMode_arith` (delegated, proved)
  closes the bookkeeping against `|ρ| ≤ 2μ` (`rho_pos_of_close`/`rho_le_two_of_close`) and
  `|Ŵ₁| ≤ 16π·(a v)` (`Work.BoseB7AK.W1rows.W1hat_abs_le`).

The main theorem is the honest-family instance of the two-line lemma `hZP_highMode_aux`,
which is stated for an arbitrary `KzDatum` carrying the `All` view.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox
open Work.BoseBoxFix Work.BoseFixR Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The high-momentum domination at an abstract `KzDatum` with the `All` view.**  This is
`Work.BoseBogFS.hZP_highMode` with the honest box family replaced by an arbitrary
`KzDatum`; all the pins are read off `RViewFSAll` (conjuncts 1, 2, 3, 4, 7, 8, 9 and 12). -/
theorem hZP_highMode_aux {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ε μ ρ : ℝ} (D : Work.BoseFixR.KzDatum)
    (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hε : ε ≤ (1 / 2) ^ 1000) (hAdm : Work.BoseBoxFix.Adm v ε μ)
    (hview : D.viewFSAll v h μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hclose : Work.BoseBoxFock.CloseCondFS v μ ρ)
    {fu' : Work.BoseBoxFix.LowCut} {Λ : ℝ}
    (hΛ : 4 * (D.E.KL * Real.sqrt (D.E.mu * D.E.aScat)) ≤ Λ)
    (k : D.Mode)
    (hζ : Work.BoseBoxFock.uvCut fu' Λ (D.F.kmom k) < 1) :
    2 * |ρ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
        (D.F.kmom k)| ≤ D.E.tau k := by
  -- (a) the view's pins
  unfold Work.BoseFixR.KzDatum.viewFSAll at hview
  unfold Work.BoseBoxFock.RViewFSAll at hview
  obtain ⟨hFSP, hmu, hac, hell, -, -, hdP, hsP, heTP, -, -, htau, -⟩ := hview
  have hvE : Work.BoseB7.FSParamsView D.E := Classical.choice hFSP
  -- (b) diluteness data
  have hμpos : 0 < μ := hAdm.1
  have hav' : 0 < _root_.BoseGases.a v := hav
  have hε₁ : ε ≤ 1 :=
    le_trans hε (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 ≤ 1))
  have htpos : 0 < hvE.t := hvE.t_pos
  have ht_eq : hvE.t = μ * (_root_.BoseGases.a v) ^ 3 := by
    rw [← hvE.mu_eq, hmu, hac]
  have htε : hvE.t ≤ (1 / 2) ^ 1000 := by
    rw [ht_eq]
    exact le_trans hAdm.2.1 hε
  have htε' : D.E.mu * D.E.aScat ^ 3 ≤ (1 / 2) ^ 1000 := by
    rw [hmu, hac]
    exact le_trans hAdm.2.1 hε
  -- (c) the scale row at the view's `FSParamsView`
  obtain ⟨hsl_le, hKL1024, heTq⟩ := scaleRow_of_fsParams (E := D.E) hvE htε'
  have heT1 : D.E.eT ≤ 1 := le_trans heTq (by norm_num)
  have heT0 : 0 ≤ D.E.eT := by
    rw [hvE.eT_eq, Work.BoseBox.fsXp]
    exact Real.rpow_nonneg htpos.le _
  have hs_pos : 0 < D.E.s := by rw [hvE.s_eq]; exact Work.BoseBox.fsXp_pos htpos
  have hd_pos : 0 < D.E.d := by rw [hvE.d_eq]; exact Work.BoseBox.fsXp_pos htpos
  have hEℓpos : 0 < D.E.ell := Work.BoseB7.ell_pos D.E hvE
  have hℓpos : 0 < Work.BoseFixR.ell v μ := by rw [← hell]; exact hEℓpos
  -- (d) the `τ`-pin in the `E`-vocabulary, and the kink row
  have htau' : D.E.tau
      = fun k => Work.BoseBoxFock.tauSm D.E.eT D.E.s D.E.d D.E.ell (D.F.kmom k) := by
    rw [htau, ← heTP, ← hsP, ← hdP, ← hell]
  have htautk : D.E.tau k
      = Work.BoseBoxFock.tauSm D.E.eT D.E.s D.E.d D.E.ell (D.F.kmom k) := congrFun htau' k
  have hτkink : (1 - D.E.eT) * (max 0 (‖D.F.kmom k‖ - (D.E.s * D.E.ell)⁻¹)) ^ 2
      ≤ D.E.tau k := by
    have hrow := tauSm_ge_kink (eT := D.E.eT) (s := D.E.s) (d := D.E.d) (ℓ := D.E.ell)
      heT0 heT1 hs_pos hd_pos hEℓpos (D.F.kmom k)
    rw [htautk]
    exact hrow
  -- (e) the cut factor below one forces `Λ < ‖kmom k‖`
  have hζ' : fu'.f (‖D.F.kmom k‖ / Λ) < 1 := hζ
  have hgt1 : 1 < ‖D.F.kmom k‖ / Λ := by
    by_contra hcon
    push Not at hcon
    have h1 : fu'.f (‖D.F.kmom k‖ / Λ) = 1 := Work.BoseBoxFix.LowCut.one fu' _ hcon
    rw [h1] at hζ'
    exact lt_irrefl 1 hζ'
  have hΛpos : 0 < Λ := by
    by_contra hcon
    push Not at hcon
    have hle : ‖D.F.kmom k‖ / Λ ≤ 1 := by
      have h0 : ‖D.F.kmom k‖ / Λ ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (norm_nonneg _) hcon
      linarith
    linarith [hgt1, hle]
  have hΛp : Λ < ‖D.F.kmom k‖ := (one_lt_div hΛpos).mp hgt1
  -- (f) the mass bounds of `ρ` and `Ŵ₁`
  have hρ0 : 0 < ρ := rho_pos_of_close v hε₁ hav hAdm hclose
  have hρ2 : ρ ≤ 2 * μ := rho_le_two_of_close v hε₁ hav hAdm hclose
  have hρabs : |ρ| ≤ 2 * D.E.mu := by
    rw [hmu, abs_of_pos hρ0]
    exact hρ2
  have hμE : 0 < D.E.mu := by rw [hmu]; exact hμpos
  have haE : 0 < D.E.aScat := by rw [hac]; exact hav'
  have hw' : |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
      (D.F.kmom k)| ≤ 16 * Real.pi * D.E.aScat := by
    rw [hac]
    exact Work.BoseB7AK.W1rows.W1hat_abs_le hR hℓpos hv hvrad hv_supp h hRℓ (D.F.kmom k)
  -- (g) the pure arithmetic
  exact highMode_arith (KL := D.E.KL) (Λ := Λ) (sℓ := (D.E.s * D.E.ell)⁻¹) (μ := D.E.mu)
    (av := D.E.aScat) (ρ := ρ)
    (w := Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) (D.F.kmom k))
    (p := ‖D.F.kmom k‖) (τ := D.E.tau k) (eT := D.E.eT)
    hμE haE hρabs hw' hKL1024 hΛ hΛp hsl_le heTq hτkink

/-- **The high-momentum mode domination at the honest box family**
(needed for the holder `Work.BoseBogFS.hZP_of_lattice`; the full recipe is in
`Submission/Work/BoseBogFS/FINDING_hZP_of_lattice_plan.md` §1).

At the honest family `E = (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E`, given FS's
diluteness `Adm v ε μ` with `ε ≤ (1/2)^1000`, the `All` view of the family, the regime row
`R ≤ ell v μ · chiR0`, `CloseCondFS v μ ρ`, and the view's own UV-cut data `(fu', Λ)`
(`4·(E.KL·√(E.mu·E.aScat)) ≤ Λ`), every mode `k` whose cut factor is **strictly below one**
satisfies

    2·|ρ·Ŵ₁(F.kmom k)| ≤ E.tau k ,      Ŵ₁(p) = chat (W1fun v h (ell v μ)) p .

**Content.**  The cut factor `uvCut fu' Λ (F.kmom k) < 1` forces `‖F.kmom k‖ > Λ ≥
4·K_L·√(μa)`, hence (kink domination `Work.BoseBogFS.tauSm_ge_kink`,
`(sℓ)⁻¹ = t^{1/646}√(μa) ≤ √(μa)`, `K_L ≥ 1024` from `ε ≤ 2^{-1000}`,
`ε_T ≤ 1/2` from `rpow_23_le_half`)

    E.tau k ≥ (1/2)·(4095)²·μ·(a v) ≥ 8·10⁶·μ·(a v) ,

while `|ρ| ≤ 2μ` (`Work.BoseBogFS.rho_pos_of_close`, `rho_le_two_of_close`, in
`Submission/Work/BoseBogFS/hKAP_of_rows.lean`) and `|Ŵ₁| ≤ 16π·(a v)`
(`Work.BoseB7AK.W1rows.W1hat_abs_le`, from `R ≤ ℓ·chiR0` and `ScatSol v`)
give `2|ρŴ₁| ≤ 64π·μ·(a v) ≤ 201·μ·(a v)`.  The two constants are far apart, so this is a
comfortable statement; all the work is bookkeeping through the view's pins. -/
theorem hZP_highMode {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ}
    {R ε μ ρ : ℝ} (hR : 0 < R) (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v)
    (hε : ε ≤ (1 / 2) ^ 1000) (hAdm : Work.BoseBoxFix.Adm v ε μ)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0)
    (hclose : Work.BoseBoxFock.CloseCondFS v μ ρ)
    {fu' : Work.BoseBoxFix.LowCut} {Λ : ℝ}
    (hΛ : 4 * ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.KL
        * Real.sqrt ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.mu
            * (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.aScat)) ≤ Λ)
    (k : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).Mode)
    (hζ : Work.BoseBoxFock.uvCut fu' Λ
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k) < 1) :
    2 * |ρ * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ))
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F.kmom k)|
      ≤ (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.tau k := by
  exact hZP_highMode_aux (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ) hR hv hvrad hv_supp
    hav hε hAdm hview hRℓ hclose hΛ k hζ

end Work.BoseBogFS
