/-
# Row 26 of the §8 table in the open-quadrant (primed) vocabulary

`Work.FTS.Nonlinear.Open.Row26`: the `ℋ⁴`-honesty and the norm bound of the piece

  `N₅^{ss}(z,θ) = -sin²θ · FK(F_*)(z) · F_*(z,θ)`

(`Work.FTS.Nonlin.N5ss`), uniformly for `0 < α ≤ min(α₂,1)` and with the rate `α²`.

## Route

`FK(F_*) = α·2z/(1+z)² = 2α·hKer(z)` (`FstarPkg.FK_Fstar`) and
`F_* = α(Γ/c)·2·hKer` (`Construction.Fstar`, `FM.Fstar = 2·hKer`), so on the open quadrant

  `N₅^{ss} = a(θ)·r(z)`,   `a θ = sin²θ·Γ(θ)`,   `r z = -(4α²/c(α))·hKer(z)²`,

a product of an *angular* profile and a *radial* function (the constant is carried by the radial
factor, which keeps the angular bounds constant-free).  Two facts about the angular profile are
needed, both with the **sharp** angular majorant `G θ = Γ(θ)·(α + sin 2θ)`:

* `|sin²θ·Γ(θ)| ≤ 1`, and
* `|D_θ^i (sin²θ·Γ)| ≤ B·Γ·(α + sin 2θ)` for `1 ≤ i ≤ 4` (`Row26Ang` below, an immediate
  consequence of the `Lop`-iterate bound `RNP26.psiB_Lop_bound` on the open interval, the two
  endpoints being trivial because both sides vanish there);

the crude bound `|D_θ^i(sin²θΓ)| ≤ B·sin(2θ)^{α/5}` (`RNP.dthSinSqGam_le`) would only give the
rate `α^{3/2}`.  Then

* the `ℋ⁴`-honesty is `AuxAngRad.HkMem_ang_rad` with `G` as above (its integrability against the
  heavy weight `sin(2θ)^{-γ}` is `gamWeightInt`), and
* the norm bound is `Pieces.RNP.Xn_ang_rad_le_gen` with `M1 = M` of `gamWeightInt` and
  `Xn α (fun z _ => hKer z²) ≤ Cr` of `hkerSq_radial_alt`, giving
  `Xn α (N₅^{ss}) ≤ √(10⁴ + 4B²M)·(40·Cr)·α²`.

The hypotheses `g`, `Φs`, `Φg` (and hence the interfaces `N4Norm'`/`N4Extra'`) are irrelevant for
this row: the piece involves only the fundamental model `F_*`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row26
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Open.Row25
import Submission.Work.FTS.NonlinRows.AuxAngRad.HkMem_ang_rad
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row23
import Submission.Work.FTS.Nonlinear.Pieces.RNP.hkerSqAux
import Submission.Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.Nonlinear.Pieces.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-! ## The sharp `D_θ`-iterate bound for the angular factor `sin²θ·Γ(θ)` -/

/-- **The `D_θ`-iterates of `sin²θ·Γ(θ)` are bounded by `B·Γ(θ)·(α + sin 2θ)`.**

This is the `Iθ`-version (the closed angular interval) of the sharp iterate bound
`RNP26.psiB_Lop_bound`, which is stated on the open interval with the majorant
`Γ·(sin²(2θ) + α)`; since `0 ≤ sin 2θ ≤ 1` on `Iθ`, that majorant is dominated by
`Γ·(α + sin 2θ)`.  At the two endpoints both sides vanish: `Γ(0) = Γ(π/2) = 0`
(`Gam_zero_left`/`Gam_zero_right`) and `D_θ^i f = sin(2θ)·∂_θ(D_θ^{i-1}f) = 0` for `i ≥ 1`. -/
theorem Row26Ang :
    ∃ B : ℝ, 0 < B ∧ ∀ α : ℝ, 0 < α → α ≤ 1 → ∀ i : ℕ, 1 ≤ i → i ≤ 4 →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 θ|
          ≤ B * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by
  obtain ⟨D, hDpos, hD⟩ := Work.FTS.Nonlinear.Pieces.RNP26.psiB_Lop_bound
  refine ⟨D, hDpos, ?_⟩
  intro α hα hα1 i hi1 hi4 θ hθ
  have hΓnn : 0 ≤ Work.Spaces.Gam α θ := (Work.Spaces.Gam_bounds α θ hα hθ).1
  -- split the two endpoints off
  rcases eq_or_lt_of_le hθ.1 with h0 | h0pos
  · -- `θ = 0`
    have hθ0 : θ = 0 := h0.symm
    subst hθ0
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi1)
    have hz : Work.Spaces.DthIter (j + 1)
        (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 0 = 0 := by
      rw [Work.Spaces.DthIter_succ]
      simp [Work.Spaces.Dth]
    rw [hz, abs_zero, Work.Spaces.Gam_zero_left α (ne_of_gt hα)]
    simp
  · rcases eq_or_lt_of_le hθ.2 with hpi | hpilt
    · -- `θ = π/2`
      subst hpi
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hi1)
      have hz : Work.Spaces.DthIter (j + 1)
          (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 (Real.pi / 2) = 0 := by
        rw [Work.Spaces.DthIter_succ]
        simp only [Work.Spaces.Dth]
        rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, zero_mul]
      rw [hz, abs_zero, Work.Spaces.Gam_zero_right α (ne_of_gt hα),
        show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      simp
    · -- interior: the `Lop`-iterate bound of `psiB_Lop_bound`
      have hioo : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨h0pos, hpilt⟩
      have hL : Work.Spaces.DthIter i
          (fun _ (θ' : ℝ) => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') 0 θ
          = Work.Spaces.Lop^[i] (fun θ' : ℝ => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') θ := by
        rw [Work.Spaces.DthIter_eq_iterate_Lop]
      rw [hL]
      have h := hD α hα hα1 i hi1 hi4 θ hioo
      have hs2 : Real.sin (2 * θ) ^ 2 ≤ Real.sin (2 * θ) := by
        have hs0 : 0 ≤ Real.sin (2 * θ) :=
          (Real.sin_pos_of_pos_of_lt_pi (by linarith [h0pos])
            (by linarith [hpilt, Real.pi_pos])).le
        nlinarith [Real.sin_le_one (2 * θ)]
      calc |Work.Spaces.Lop^[i] (fun θ' : ℝ => Real.sin θ' ^ 2 * Work.Spaces.Gam α θ') θ|
          ≤ D * Work.Spaces.Gam α θ * (Real.sin (2 * θ) ^ 2 + α) := h
        _ ≤ D * Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) := by
            refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = D * (Work.Spaces.Gam α θ * (α + Real.sin (2 * θ))) := by ring

/-! ## The row -/

theorem Row26 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N5ss α) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N5ss α) ≤ K * (α ^ 2) := by
  obtain ⟨Csh, hCshpos, hCsh⟩ := Row26Ang
  obtain ⟨Cr, hCrpos, hCr⟩ := Work.FTS.Nonlinear.Pieces.RNP.hkerSq_radial_alt
  obtain ⟨M, hMpos, hM⟩ := Work.FTS.Nonlinear.Pieces.RNP.gamWeightInt
  refine ⟨Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * Cr) + 1, ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * Cr) := by
      positivity
    linarith
  · intro α g Φs Φg hα hα1 hαα₂ hgal hstar hell
    have hcge : (1 : ℝ) / 10 ≤ Work.Spaces.c α := (Work.Spaces.c_bounds α hα hα1).1
    have hcpos : 0 < Work.Spaces.c α := by linarith
    -- the angular profile, the radial factor and the angular majorant
    set psi : ℝ → ℝ := fun θ => Real.sin θ ^ 2 * Work.Spaces.Gam α θ with hpsi
    set r : ℝ → ℝ := fun z => (-(4 * α ^ 2 / Work.Spaces.c α)) * Work.Spaces.hKer z ^ 2 with hr
    set G : ℝ → ℝ := fun θ => Work.Spaces.Gam α θ * (α + Real.sin (2 * θ)) with hG
    -- ### the factorisation of the piece
    have hfac : Work.FTS.Nonlin.N5ss α = fun z θ => psi θ * r z := by
      funext z θ
      rw [hpsi, hr]
      simp only [Work.FTS.Nonlin.N5ss]
      rw [Work.FTS.Nonlin.FK_Fstar hα hα1]
      simp only [Work.Construction.Fstar, Work.FM.Fstar, Work.Spaces.hKer_apply]
      ring
    -- ### smoothness of the two factors
    have hSOsin2 : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => Real.sin θ ^ 2) := by
      have h1 := Work.FTS.NonlinRows.smoothOpen_const_mul (-1)
        Work.FTS.Nonlinear.Open.row25_smoothOpen_neg_sinSq
      rw [show (fun _ (θ : ℝ) => (-1 : ℝ) * (-(Real.sin θ ^ 2)))
          = fun _ (θ : ℝ) => Real.sin θ ^ 2 from by
        funext z θ; ring] at h1
      exact h1
    have hSOpsi : Work.FTS.EllipticEst.SmoothOpen (fun _ (θ : ℝ) => psi θ) := by
      rw [hpsi]
      exact Work.FTS.Nonlinear.Open.row25_smoothOpen_ang_mul hSOsin2
        (Work.FTS.Nonlinear.Open.row25_smoothOpen_Gam α)
    have hrSO : Work.FTS.EllipticEst.SmoothOpen (fun z (_ : ℝ) => r z) := by
      rw [hr]
      refine Work.FTS.NonlinRows.smoothOpen_const_mul (-(4 * α ^ 2 / Work.Spaces.c α)) ?_
      refine Work.FTS.NonlinRows.smoothOpen_radial fun n => ?_
      have h := Work.FTS.Nonlinear.Open.row25_contDiffOn_hKer n
      simpa only [pow_two] using h.mul h
    -- ### the two angular bounds
    have ha0 : ∀ θ ∈ Work.Spaces.Iθ, |psi θ| ≤ 1 := by
      intro θ hθ
      simpa only [hpsi, Work.FTS.Nonlinear.Pieces.RNP.psiB] using
        Work.FTS.Nonlinear.Pieces.RNP.psiB_abs_le_one (α := α) hα hθ
    have ha1 : ∀ i : ℕ, 1 ≤ i → i ≤ 4 → ∀ θ ∈ Work.Spaces.Iθ,
        |Work.Spaces.DthIter i (fun _ (θ' : ℝ) => psi θ') 0 θ| ≤ Csh * G θ := by
      intro i hi1 hi4 θ hθ
      have h := hCsh α hα hα1 i hi1 hi4 θ hθ
      simpa only [hpsi, hG] using h
    -- ### the angular majorant
    have hGnn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ G θ := by
      intro θ hθ
      have hGam := Work.Spaces.Gam_bounds α θ hα hθ
      have hs := Work.FTS.Nonlinear.RadialProd.sin_two_nonneg_of_mem_Iθ hθ
      rw [hG]
      exact mul_nonneg hGam.1 (by linarith)
    have hGint : MeasureTheory.IntegrableOn
        (fun θ : ℝ => G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ) Work.Spaces.Iθ := by
      have h := (hM α hα hα1).1
      rw [hG]
      simpa only [mul_pow, mul_assoc] using h
    have hm1 : ∫ θ in Work.Spaces.Iθ,
        G θ ^ 2 * Work.FTS.Nonlinear.RadialProd.smG α θ ≤ M := by
      have h := (hM α hα hα1).2
      rw [hG]
      simpa only [mul_pow, mul_assoc] using h
    -- ### the radial factor
    have hrmem : Work.Spaces.HkMem α 4 (fun z (_ : ℝ) => r z) := by
      rw [hr]
      exact Work.FTS.LocData.HkMem_const_mul α 4 (-(4 * α ^ 2 / Work.Spaces.c α))
        (hCr α hα hα1).1
    have hcoefabs : |-(4 * α ^ 2 / Work.Spaces.c α)| ≤ 40 * α ^ 2 := by
      rw [abs_neg, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * α ^ 2 / Work.Spaces.c α),
        div_le_iff₀ hcpos]
      nlinarith [hcge, sq_nonneg α, hα.le]
    have hXnr : Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z) ≤ 40 * α ^ 2 * Cr := by
      have h0 : Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => Work.Spaces.hKer z ^ 2) ≤ Cr :=
        (hCr α hα hα1).2
      have hrew : Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z)
          = |-(4 * α ^ 2 / Work.Spaces.c α)|
            * Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => Work.Spaces.hKer z ^ 2) := by
        rw [hr]
        exact Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul α (-(4 * α ^ 2 / Work.Spaces.c α))
          (fun z (_ : ℝ) => Work.Spaces.hKer z ^ 2)
      rw [hrew]
      exact mul_le_mul hcoefabs h0 (Work.Spaces.HkNorm_nonneg α 4 _) (by positivity)
    -- ### the honesty and the norm
    have hHk : Work.Spaces.HkMem α 4 (fun z θ => psi θ * r z) :=
      Work.FTS.NonlinRows.AuxAngRad.HkMem_ang_rad (α := α) (a := psi) (r := r) (G := G)
        (B0 := 1) (B1 := Csh) hSOpsi hrSO hGnn hGint ha0 ha1 hrmem
    have hXn := Work.FTS.Nonlinear.Pieces.RNP.Xn_ang_rad_le_gen α hα psi r G
      (B0 := 1) (B1 := Csh) (M1 := M) (by norm_num) hCshpos.le hMpos.le hGnn ha0 ha1
      hGint hm1 hrmem
    rw [hfac]
    refine ⟨hHk, ?_⟩
    calc Work.FTS.Nonlin.Xn α (fun z θ => psi θ * r z)
        ≤ Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M)
            * Work.FTS.Nonlin.Xn α (fun z (_ : ℝ) => r z) := hXn
      _ ≤ Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * α ^ 2 * Cr) :=
          mul_le_mul_of_nonneg_left hXnr (Real.sqrt_nonneg _)
      _ = (Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * Cr)) * α ^ 2 := by ring
      _ ≤ (Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * Cr) + 1) * α ^ 2 := by
          have h1 : (0 : ℝ) ≤ Real.sqrt (1 ^ 2 * 10000 + 4 * Csh ^ 2 * M) * (40 * Cr) := by
            positivity
          nlinarith [h1, sq_nonneg α]

end Work.FTS.Nonlinear.Open
