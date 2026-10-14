import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.StrongPersist.SP6.WlInf6OfFlatW
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.RXR5.Fstar_C1Jet
import Submission.Work.FTS_RegExport.RXT.Sys.slice_contDiffOn_four
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_alt_majorant
import Submission.Work.FTS_StreamBdry.SB4.l12_zero_plainE
import Submission.Work.Spaces.factor_bound
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.Ftau_C1Jet =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR5L

theorem Ftau_C1Jet {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S)
    (hSt1 : Work.FTS.RegPkgGal.St1Class α S
      (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)))
    (hO1 : ∃ N₂ N₃ : ℝ, 0 ≤ N₂ ∧ 0 ≤ N₃ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₂
        (fun z θ τ => Work.Spaces.Dz (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ) ∧
      Work.FTS.RegPkgGal.C1Jet α S N₃
        (fun z θ τ => Work.Spaces.Dth (fun z θ => Work.FTS_RegExport.RXR5.SG α g z θ τ) z θ)) :
    ∃ N₄ : ℝ, 0 ≤ N₄ ∧
      Work.FTS.RegPkgGal.C1Jet α S N₄
        (fun z θ τ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ z θ) := by
  obtain ⟨N₁, _hN₁0, hN₁⟩ := SG_C1Jet (S := S) hα hα13 hOK hS hSt1
  have hF : Work.FTS.RegPkgGal.C1Jet α S (100 + 20 * Work.FTS.Regularity.pExp α)
      (fun z θ (_ : ℝ) => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) :=
    Work.FTS.RegPkgGal.Der.C1JetFstar (S := S) hα hα13
  have hsum : Work.FTS.RegPkgGal.C1Jet α S
      ((100 + 20 * Work.FTS.Regularity.pExp α) + N₁)
      (fun z θ τ =>
        Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ
          + Work.FTS_RegExport.RXR5.SG α g z θ τ) :=
    Work.FTS.RegPkgGal.C1Jet.add hF hN₁
  exact ⟨100 + 20 * Work.FTS.Regularity.pExp α + N₁,
    by have hp := Work.FTS.Regularity.pExp_pos hα; linarith, hsum⟩

end Work.FTS_RegExport.RXR5L
end
-- ===== merged: Submission.Work.FTS_StreamBdry.Inputs.ftau_cont =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.Inputs.ftau_cont` — continuity of `F(τ) = F_* + g(·,·,τ)`

The first of the three `SrcOK`-shaped inputs of the slice adapter (`NOTES_slice_inputs_route.md`,
§ (1)): for `τ ≥ 0` the full profile `F(τ) = Ftau (pExp a) g τ = F_* + slice g τ` is jointly
continuous on the half-strip `Ioi 0 ×ˢ Iθ`.

The argument uses *only* the regularity package `hreg` (the fields `hOK` and `ha13` are not
needed):

* the transport identity `Ftau_eq_profFull` of `SliceTr.lean` identifies `F(τ)` with the full
  profile `profFull a (extG G) · · τ = F_* + extG G · · τ` on the closed strip;
* `F_*` is visibly continuous there (`2z/(1+z)²` is only singular at `z = -1`);
* the perturbation slice `(z,θ) ↦ extG G z θ τ` is `a`-Hölder (hence continuous) at the horizon
  `S = τ + 1` by the two moduli `RegPkg'.zmod` (uniform in `θ`) and `RegPkg'.thmod` (uniform in
  `z`) of the package — their combination dominates the product metric `dist (z,θ) (z',θ')`.

The two reusable pieces are factored out as `continuousOn_Fstar_ftau` and
`continuousOn_extG_slice` below, so that the sibling leaf `ftau_Dz_cont` can use them.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.Inputs

set_option autoImplicit false

/-- **Continuity of the star profile `F_*` on the half-strip** `Ioi 0 ×ˢ Iθ`.
(`F_* = α·(Γ(θ)/c)·2z/(1+z)²`; the radial factor is singular only at `z = -1`, which the strip
excludes, and `Γ` is `rpow` of a continuous function with positive exponent.) -/
theorem continuousOn_Fstar_ftau {a : ℝ} (ha : 0 < a) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Construction.Fstar (Work.FTS.Regularity.pExp a) p.1 p.2)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  have hpa : 0 < Work.FTS.Regularity.pExp a := Work.FTS.Regularity.pExp_pos ha
  have hGam : Continuous (fun θ : ℝ => Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ) := by
    simp only [Work.Spaces.Gam]
    exact (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).rpow_const
      (fun _ => Or.inr (le_of_lt (by linarith [hpa] : (0 : ℝ) < Work.FTS.Regularity.pExp a / 3)))
  have hFstarOn : ContinuousOn (fun z : ℝ => Work.FM.Fstar z) (Set.Ioi 0) := by
    simp only [Work.FM.Fstar]
    refine ContinuousOn.div ?_ ?_ ?_
    · exact (continuous_const.mul continuous_id).continuousOn
    · exact ((continuous_const.add continuous_id).pow 2).continuousOn
    · intro z hz
      have hz' : (0 : ℝ) < z := hz
      have hz1 : (0 : ℝ) < 1 + z := by linarith
      exact ne_of_gt (by positivity)
  have hFz : ContinuousOn (fun p : ℝ × ℝ => Work.FM.Fstar p.1) (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    hFstarOn.comp continuous_fst.continuousOn (fun p hp => hp.1)
  have hth : ContinuousOn
      (fun p : ℝ × ℝ => Work.FTS.Regularity.pExp a *
        (Work.Spaces.Gam (Work.FTS.Regularity.pExp a) p.2 / Work.Spaces.c (Work.FTS.Regularity.pExp a)))
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) :=
    (continuous_const.mul ((hGam.comp continuous_snd).div_const _)).continuousOn
  refine ContinuousOn.congr (hth.mul hFz) (fun p _ => ?_)
  simp only [Work.Construction.Fstar, Pi.mul_apply]

/-- **Continuity of the (extended) perturbation slice** `(z,θ) ↦ extG G z θ τ` on the half-strip,
for `τ ≥ 0`, from the package `RegPkg' a S A B (extG G)` at the horizon `S = τ + 1`.

The two Hölder moduli of the package are uniform in the other variable, so their sum is an
`a`-Hölder modulus for the product metric. -/
theorem continuousOn_extG_slice {a τ : ℝ} {G : ℝ → ℝ → ℝ → ℝ} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hτ : 0 ≤ τ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.FTS.RegPkgGal.extG G p.1 p.2 τ)
      (Set.Ioi 0 ×ˢ Work.Spaces.Iθ) := by
  have hmem : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  have hpkg : Work.FTS.RegPkgGal.RegPkg' a (τ + 1) A B (Work.FTS.RegPkgGal.extG G) :=
    hreg (τ + 1) (by linarith)
  obtain ⟨Lg, hLg0, hLg⟩ := hpkg.zmod hmem
  obtain ⟨Lθ, hLθ0, hLθ⟩ := hpkg.thmod hmem
  have ha0 : 0 < a := hpkg.alpha_pos
  rw [Metric.continuousOn_iff]
  intro b hb ε hε
  obtain ⟨hbz, hbθ⟩ := hb
  have hCpos : 0 < Lg + Lθ + 1 := by linarith
  refine ⟨(ε / (Lg + Lθ + 1)) ^ (1 / a), Real.rpow_pos_of_pos (by positivity) _, ?_⟩
  intro x hx hdist
  obtain ⟨hxz, hxθ⟩ := hx
  have hdx : |x.1 - b.1| ≤ dist x b := by
    rw [Prod.dist_eq, Real.dist_eq]; exact le_max_left _ _
  have hdy : |x.2 - b.2| ≤ dist x b := by
    rw [Prod.dist_eq, Real.dist_eq]; exact le_max_right _ _
  have hdxa : |x.1 - b.1| ^ a ≤ dist x b ^ a :=
    Real.rpow_le_rpow (abs_nonneg _) hdx (le_of_lt ha0)
  have hdya : |x.2 - b.2| ^ a ≤ dist x b ^ a :=
    Real.rpow_le_rpow (abs_nonneg _) hdy (le_of_lt ha0)
  have h1 := hLθ x.1 x.2 b.2 (le_of_lt hxz) hxθ hbθ
  have h2 := hLg x.1 b.1 b.2 (le_of_lt hxz) (le_of_lt hbz) hbθ
  have hmul1 : Lg * |x.1 - b.1| ^ a ≤ Lg * dist x b ^ a := mul_le_mul_of_nonneg_left hdxa hLg0
  have hmul2 : Lθ * |x.2 - b.2| ^ a ≤ Lθ * dist x b ^ a := mul_le_mul_of_nonneg_left hdya hLθ0
  have htri : |Work.FTS.RegPkgGal.extG G x.1 x.2 τ - Work.FTS.RegPkgGal.extG G b.1 b.2 τ|
      ≤ Lg * dist x b ^ a + Lθ * dist x b ^ a := by
    have hsplit : Work.FTS.RegPkgGal.extG G x.1 x.2 τ - Work.FTS.RegPkgGal.extG G b.1 b.2 τ
        = (Work.FTS.RegPkgGal.extG G x.1 x.2 τ - Work.FTS.RegPkgGal.extG G x.1 b.2 τ)
          + (Work.FTS.RegPkgGal.extG G x.1 b.2 τ - Work.FTS.RegPkgGal.extG G b.1 b.2 τ) := by
      ring
    rw [hsplit]
    calc |(Work.FTS.RegPkgGal.extG G x.1 x.2 τ - Work.FTS.RegPkgGal.extG G x.1 b.2 τ)
            + (Work.FTS.RegPkgGal.extG G x.1 b.2 τ - Work.FTS.RegPkgGal.extG G b.1 b.2 τ)|
        ≤ |Work.FTS.RegPkgGal.extG G x.1 x.2 τ - Work.FTS.RegPkgGal.extG G x.1 b.2 τ|
            + |Work.FTS.RegPkgGal.extG G x.1 b.2 τ - Work.FTS.RegPkgGal.extG G b.1 b.2 τ| :=
          abs_add_le _ _
      _ ≤ Lθ * |x.2 - b.2| ^ a + Lg * |x.1 - b.1| ^ a := add_le_add h1 h2
      _ ≤ Lθ * dist x b ^ a + Lg * dist x b ^ a := add_le_add hmul2 hmul1
      _ = Lg * dist x b ^ a + Lθ * dist x b ^ a := by ring
  rw [Real.dist_eq]
  have hδeq : ((ε / (Lg + Lθ + 1)) ^ (1 / a)) ^ a = ε / (Lg + Lθ + 1) := by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ ε / (Lg + Lθ + 1)), one_div,
      inv_mul_cancel₀ (ne_of_gt ha0), Real.rpow_one]
  have hdlt : dist x b ^ a < ε / (Lg + Lθ + 1) := by
    rw [← hδeq]
    exact Real.rpow_lt_rpow (dist_nonneg) hdist ha0
  calc |Work.FTS.RegPkgGal.extG G x.1 x.2 τ - Work.FTS.RegPkgGal.extG G b.1 b.2 τ|
      ≤ Lg * dist x b ^ a + Lθ * dist x b ^ a := htri
    _ = (Lg + Lθ) * dist x b ^ a := by ring
    _ ≤ (Lg + Lθ) * (ε / (Lg + Lθ + 1)) := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hdlt) (by linarith)
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ hCpos]
        nlinarith [hε, hLg0, hLθ0]


end Work.FTS_StreamBdry.Inputs
end
end
