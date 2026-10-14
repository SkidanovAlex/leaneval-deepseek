import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.Filter.Defs
import Mathlib.Tactic.MinImports
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.NonlinRows.NRow14T2
import Submission.Work.FTS.NonlinRows.pure_slot_mul_pth_le
import Submission.Work.FTS.Nonlinear.Pieces.rl1Pieces.Pgs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroSliceInt
import Submission.Work.FTS.StrongEps.EpsE4Thr.GainDefs
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartArith
import Submission.Work.FTS.StrongEps.SmoothOpen_Jeps
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.mixed_Jeps_kernel_partial
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.R1G.vecResid_eq_scalar_smul
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow10T2 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option linter.unusedVariables false

/-!
# Row 10 of the §8 table, `T2` vocabulary: the star field is present

This is the row-10 statement in the *upgraded* vocabulary `Work.FTS.VocabO2.Ctx2`, whose star
package `StarPkgo2` carries (as its field `RW`) exactly the information diagnosed as missing in
`NRow10.lean`: the `𝒲^{4,∞}`-membership and the `≤ Cs·α` bound of the star coefficient
`H = ((z+1)/z)·ℛ(Φ̃_*) = StarH α Φs`.

With that field available the row is the product rule `N4Norm'.wprod` applied to `H` and to the
bounded radial factor `φ(z) = z/(1+z)`: the proof is verbatim the body of `NRow10_of_WlInfStar`
(same directory), with its hypothesis `hstar` instantiated by `Ctx2`'s `RW` field instead of being
assumed as a global clause. -/

/-- The `StarPkgo2` field `RW`, read in the `StarH`-form used by the product rule. -/
theorem starH_mem_of_StarPkgo2 {α Cs : ℝ} {Φs : Fn}
    (hs : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    Work.Spaces.WlInfMem α 4 (StarH α Φs) ∧
      Work.Spaces.WlInf α 4 (StarH α Φs) ≤ Cs * α :=
  hs.RW


end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.NonlinRows.NRow14 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.NonlinRows

end Work.FTS.NonlinRows
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.jet_LGammaT =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter MeasureTheory

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The pointwise expansion of `𝓛_Γ^T` -/

/-- The operator `𝓛_Γ^T = 𝓛_Γ - 𝕡∘Transport` written out in its five elementary pieces:
the two `𝓛`-terms, the `L₁₂`-term with the coefficient `2zΓ(θ)/(c(α)(1+z)²)`, the angular
transport term `3D_θf/(1+z)`, and the projection correction with the coefficient
`(Γ(θ)/c(α))·2z²/(1+z)³`. -/
theorem LGammaT_eq_expansion (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Coercivity.LGammaT α f z θ
      = f z θ + Work.Spaces.Dz f z θ - (2 / (1 + z)) * f z θ
        - (2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
            * Work.Coercivity.L12f f z
        - (3 / (1 + z)) * Work.Spaces.Dth f z θ
        + (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)
            * Work.Coercivity.L12f (Work.Coercivity.Transport f) 0 := by
  simp only [Work.Coercivity.LGammaT, Work.Coercivity.LGamma, Work.Coercivity.Proj,
    Work.Coercivity.Transport, Work.Coercivity.L]
  ring

/-! ## 2. The `Jet` of `𝓛_Γ^T(g(τ))` -/

theorem jet_LGammaT {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {N₁ N₂ N₃ N₄ N₅ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hg : Work.FTS.Regularity.Jet α S N₁ g)
    (hDzg : Work.FTS.Regularity.Jet α S N₂ (fun z θ τ => Work.Spaces.Dz (fun z θ => g z θ τ) z θ))
    (hDthg : Work.FTS.Regularity.Jet α S N₃ (fun z θ τ => Work.Spaces.Dth (fun z θ => g z θ τ) z θ))
    (hL12 : Work.FTS.Regularity.Jet α S N₄
      (fun z θ τ => Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z))
    (hL12T : Work.FTS.Regularity.Jet α S N₅
      (fun z θ τ => Work.Coercivity.L12f
        (fun z θ' => 3 * Work.Spaces.Dth (fun z θ => g z θ τ) z θ' / (1 + z)) 0)) :
    ∃ Nc : ℝ, Work.FTS.Regularity.Jet α S Nc
      (fun z θ τ => Work.Coercivity.LGammaT (Work.FTS.Regularity.pExp α)
        (Work.FTS.Regularity.gSlice g τ) z θ) := by
  -- the given `Jet`s, in the `gSlice`-form in which the expansion of `𝓛_Γ^T` is written
  have hg' : Work.FTS.Regularity.Jet α S N₁
      (fun z θ τ => Work.FTS.Regularity.gSlice g τ z θ) := hg
  have hDz' : Work.FTS.Regularity.Jet α S N₂
      (fun z θ τ => Work.Spaces.Dz (Work.FTS.Regularity.gSlice g τ) z θ) := hDzg
  have hDth' : Work.FTS.Regularity.Jet α S N₃
      (fun z θ τ => Work.Spaces.Dth (Work.FTS.Regularity.gSlice g τ) z θ) := hDthg
  have hL12' : Work.FTS.Regularity.Jet α S N₄
      (fun z θ τ => Work.Coercivity.L12f (Work.FTS.Regularity.gSlice g τ) z) := hL12
  have hL12T' : Work.FTS.Regularity.Jet α S N₅
      (fun z θ τ => Work.Coercivity.L12f
        (Work.Coercivity.Transport (Work.FTS.Regularity.gSlice g τ)) 0) := hL12T
  -- the coefficient estimates (the `jet_coeff_all` aggregation)
  obtain ⟨_, h2, h3, _, hcoef, hAK0⟩ := jet_coeff_all (S := S) hα hα13
  have hAK' : Work.FTS.Regularity.Jet α S 100
      (fun z θ _ => (Work.Spaces.Gam (Work.FTS.Regularity.pExp α) θ
          / Work.Spaces.c (Work.FTS.Regularity.pExp α)) * (2 * z ^ 2 / (1 + z) ^ 3)) :=
    rhsJet_congr (fun z θ τ => rfl) hAK0
  -- the five pieces of the expansion, as `Jet`s of the family `(z,θ,τ) ↦ ·(z,θ)`
  have Pg := Work.FTS.Regularity.Jet.mul (Work.FTS.Regularity.Jet.neg h2) hg'
  have P12 := Work.FTS.Regularity.Jet.mul hcoef hL12'
  have Pth := Work.FTS.Regularity.Jet.mul (Work.FTS.Regularity.Jet.neg h3) hDth'
  have PAK := Work.FTS.Regularity.Jet.mul hAK' hL12T'
  -- the sum, in the order of the expansion
  have hE := Work.FTS.Regularity.Jet.add
    (Work.FTS.Regularity.Jet.add
      (Work.FTS.Regularity.Jet.add
        (Work.FTS.Regularity.Jet.add
          (Work.FTS.Regularity.Jet.add hg' hDz')
          Pg)
        (Work.FTS.Regularity.Jet.neg P12))
      Pth)
    PAK
  refine ⟨_, rhsJet_congr (fun z θ τ => ?_) hE⟩
  rw [LGammaT_eq_expansion]
  field_simp
  ring

end Work.FTS.RegPkgGal.Der
end
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.jet_N =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-- **Scalar multiplication of a `Jet`**: if `h` is a `Jet` of constant `N` then so is
`x ↦ c · h x`, with constant `|c| · N`. -/
theorem jetN_const_mul {α S N c : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.Regularity.Jet α S N h) :
    Work.FTS.Regularity.Jet α S (|c| * N) (fun z θ τ => c * h z θ τ) := by
  refine ⟨mul_nonneg (abs_nonneg _) H.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (H.2.1 z θ τ hz hθ hτ) (abs_nonneg c)
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := H.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    rw [show c * h z θ τ - c * h z' θ' τ' = c * (h z θ τ - h z' θ' τ') by ring, abs_mul]
    calc |c| * |h z θ τ - h z' θ' τ'| ≤ |c| * (N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
      _ = |c| * N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by ring

/-- A bounded Lipschitz function of `θ` alone gives a `Jet` (with constant `2N`): the `θ`-analogue
of `Work.FTS.Regularity.Jet.of_z_lipschitz`.  Needed for the angular factor `sin²θ` of `N`. -/
theorem jetN_of_th_lipschitz {α S N : ℝ} {ψ : ℝ → ℝ} (hN : 0 ≤ N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hb : ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ N)
    (hl : ∀ θ θ' : ℝ, θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ → |ψ θ - ψ θ'| ≤ N * |θ - θ'|) :
    Work.FTS.Regularity.Jet α S (2 * N) (fun _ θ _ => ψ θ) := by
  refine ⟨by linarith, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    linarith [hb θ hθ]
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have hd0 : (0 : ℝ) ≤ |z - z'| + |θ - θ'| + |τ - τ'| := by positivity
    rcases le_total |θ - θ'| 1 with hcase | hcase
    · have hle1 : |θ - θ'| ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by
        have h := Work.FTS.Regularity.le_rpow_add hα0 hα1 (abs_nonneg (θ - θ')) hcase
          (by positivity : (0 : ℝ) ≤ |z - z'| + |τ - τ'|)
        rw [show |θ - θ'| + (|z - z'| + |τ - τ'|) = |z - z'| + |θ - θ'| + |τ - τ'| by ring] at h
        exact h
      calc |ψ θ - ψ θ'| ≤ N * |θ - θ'| := hl θ θ' hθ hθ'
        _ ≤ N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := mul_le_mul_of_nonneg_left hle1 hN
        _ ≤ 2 * N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by
            have := Real.rpow_nonneg hd0 α
            nlinarith [hN]
    · have hle1 : 1 ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by
        refine Real.one_le_rpow ?_ hα0
        have h1 : 0 ≤ |z - z'| := abs_nonneg _
        have h2 : 0 ≤ |τ - τ'| := abs_nonneg _
        linarith
      have h2N : |ψ θ - ψ θ'| ≤ 2 * N := by
        have h1 : |ψ θ| ≤ N := hb θ hθ
        have h2 : |ψ θ'| ≤ N := hb θ' hθ'
        calc |ψ θ - ψ θ'| = |ψ θ + (-ψ θ')| := by ring_nf
          _ ≤ |ψ θ| + |-ψ θ'| := abs_add_le _ _
          _ = |ψ θ| + |ψ θ'| := by rw [abs_neg]
          _ ≤ 2 * N := by linarith
      calc |ψ θ - ψ θ'| ≤ 2 * N := h2N
        _ = 2 * N * 1 := by ring
        _ ≤ 2 * N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
            mul_le_mul_of_nonneg_left hle1 (by linarith)

/-- The angular factor `θ ↦ sin²θ` is a `Jet` (constant `4`). -/
theorem jetN_sin_sq {α S : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.Regularity.Jet α S 4 (fun _ θ _ => Real.sin θ ^ 2) := by
  have h2 := jetN_of_th_lipschitz (α := α) (S := S) (N := 2) (ψ := fun θ => Real.sin θ ^ 2)
    (by norm_num) hα.le hα1 ?_ ?_
  · simpa [show ((2:ℝ) * 2) = 4 by norm_num] using h2
  · intro θ hθ
    have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (Real.sin θ - 1), sq_nonneg (Real.sin θ + 1), abs_le.mp h1]
  · intro θ θ' hθ hθ'
    have hs : |Real.sin θ - Real.sin θ'| ≤ |θ - θ'| := by
      have h := Real.lipschitzWith_sin.dist_le_mul θ θ'
      simpa [Real.dist_eq] using h
    have hp : |Real.sin θ + Real.sin θ'| ≤ 2 := by
      have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
      have h2 : |Real.sin θ'| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ', Real.sin_le_one θ'⟩
      calc |Real.sin θ + Real.sin θ'| ≤ |Real.sin θ| + |Real.sin θ'| := abs_add_le _ _
        _ ≤ 1 + 1 := add_le_add h1 h2
        _ = 2 := by norm_num
    rw [show Real.sin θ ^ 2 - Real.sin θ' ^ 2
        = (Real.sin θ - Real.sin θ') * (Real.sin θ + Real.sin θ') by ring, abs_mul]
    calc |Real.sin θ - Real.sin θ'| * |Real.sin θ + Real.sin θ'| ≤ |θ - θ'| * 2 :=
          mul_le_mul hs hp (abs_nonneg _) (abs_nonneg _)
      _ = 2 * |θ - θ'| := by ring


end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.jet_N0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.jet_N0`

The quadratic term `N₀` of the fake-time equation (tex `\eqref{N0}`),

  `N₀(α, F, g) = (3/(2α)) sin(2θ) L₁₂(F_*)(z) ∂_θF_*(z,θ)
      - c₂(θ) L₁₂(F_*)(z) D_zF_*(z,θ)
      + (1/α) L₁₂(g)(z) g(z,θ)
      + (3/(2α)) sin(2θ) L₁₂(g)(z) ∂_θF(z,θ)
      - c₂(θ) L₁₂(g)(z) D_zF(z,θ)
      - c₂(θ) L₁₂(F_*)(z) D_zg(z,θ)`

evaluated on the fake-time family `F(τ) = F_* + g(τ)`, `g(τ)` (i.e. on
`Construction.Ftau (pExp α) g τ` and `Regularity.gSlice g τ`), is again a `Jet` (bounded and
jointly `α`-Hölder on the strip `z ≥ 0, θ ∈ Iθ, τ ∈ [0,S]`).

The proof is the `Jet`-calculus of `Submission.Work.FTS.Regularity.regPkg_inhabited`
(`Jet.add`, `Jet.neg`, `Jet.mul`, `Jet.congr`) together with

* the elementary `Jet` of the angular coefficient `c₂(θ) = cos 2θ - sin²θ` (`jN0_c2m`: bounded by
  `2` and `4`-Lipschitz, hence an `α`-Hölder `Jet` with constant `4`);
* the `Jet` of the explicit profile `F_* = Construction.Fstar (pExp α)` (`hFstJ`, constant `100`),
  from the packaged moduli `Regularity.fstar_abs_le_gamma` and
  `Regularity.fstar_joint_modulus` — this is what turns the hypothesis `hF` on
  `F(τ) = F_* + g(τ)` into the `Jet` of the perturbation `g` itself;
* the substitution `sin(2θ)∂_θ = D_θ` (`Spaces.Dth`), which is what makes the two `∂_θ`-slots
  consumable from the hypotheses `hDthF`, `hDthFstar` (the *weighted* angular derivative is the
  only one that is a `Jet` for the genuine profile — see `NOTES_RegPkgGal` §6);
* `Coercivity.L12f = Construction.L12` (definitional), so the hypotheses `hL12g`, `hL12Fstar`
  supply the two `L₁₂`-slots.

This is the leaf `Der.jet_N0` of the `R5Slot` tree (NOTES_RegPkgGal §14), consumed by
`Der.rhs_jet_of_parts`.
-/

namespace Work.FTS.RegPkgGal.Der

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Two elementary `Jet`-closure helpers -/


/-- The angular coefficient `c₂(θ) = cos 2θ - sin²θ` (`Construction.c2m`) is bounded by `2`. -/
theorem jN0_c2m_abs (θ : ℝ) : |Work.Construction.c2m θ| ≤ 2 := by
  rw [Work.Construction.c2m_eq]
  have h1 : |Real.cos (2 * θ)| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have h2 : |Real.sin θ ^ 2| ≤ 1 := by
    rw [abs_sq]
    nlinarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]
  calc |Real.cos (2 * θ) - Real.sin θ ^ 2|
      = |Real.cos (2 * θ) + -(Real.sin θ ^ 2)| := by rw [sub_eq_add_neg]
    _ ≤ |Real.cos (2 * θ)| + |-(Real.sin θ ^ 2)| := abs_add_le _ _
    _ = |Real.cos (2 * θ)| + |Real.sin θ ^ 2| := by rw [abs_neg]
    _ ≤ 1 + 1 := add_le_add h1 h2
    _ = 2 := by norm_num

/-- `θ ↦ c₂(θ) = cos 2θ - sin²θ` is `4`-Lipschitz. -/
theorem jN0_c2m_lip (θ θ' : ℝ) :
    |Work.Construction.c2m θ - Work.Construction.c2m θ'| ≤ 4 * |θ - θ'| := by
  rw [Work.Construction.c2m_eq θ, Work.Construction.c2m_eq θ']
  have hcos : |Real.cos (2 * θ) - Real.cos (2 * θ')| ≤ 2 * |θ - θ'| := by
    have h : |Real.cos (2 * θ) - Real.cos (2 * θ')| ≤ |2 * θ - 2 * θ'| := by
      have hh := Real.lipschitzWith_cos.dist_le_mul (2 * θ) (2 * θ')
      simpa [Real.dist_eq] using hh
    have h2 : |2 * θ - 2 * θ'| = 2 * |θ - θ'| := by
      rw [show 2 * θ - 2 * θ' = 2 * (θ - θ') by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    rw [h2] at h
    exact h
  have hsin : |Real.sin θ ^ 2 - Real.sin θ' ^ 2| ≤ 2 * |θ - θ'| := by
    have hs : |Real.sin θ - Real.sin θ'| ≤ |θ - θ'| := by
      have h := Real.lipschitzWith_sin.dist_le_mul θ θ'
      simpa [Real.dist_eq] using h
    have hsum : |Real.sin θ + Real.sin θ'| ≤ 2 := by
      calc |Real.sin θ + Real.sin θ'| ≤ |Real.sin θ| + |Real.sin θ'| := abs_add_le _ _
        _ ≤ 1 + 1 := add_le_add (abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩)
              (abs_le.mpr ⟨Real.neg_one_le_sin θ', Real.sin_le_one θ'⟩)
        _ = 2 := by norm_num
    rw [show Real.sin θ ^ 2 - Real.sin θ' ^ 2
        = (Real.sin θ - Real.sin θ') * (Real.sin θ + Real.sin θ') by ring, abs_mul]
    calc |Real.sin θ - Real.sin θ'| * |Real.sin θ + Real.sin θ'| ≤ |θ - θ'| * 2 :=
          mul_le_mul hs hsum (abs_nonneg _) (abs_nonneg _)
      _ = 2 * |θ - θ'| := by ring
  calc |(Real.cos (2 * θ) - Real.sin θ ^ 2) - (Real.cos (2 * θ') - Real.sin θ' ^ 2)|
      = |(Real.cos (2 * θ) - Real.cos (2 * θ')) + -(Real.sin θ ^ 2 - Real.sin θ' ^ 2)| := by
        congr 1; ring
    _ ≤ |Real.cos (2 * θ) - Real.cos (2 * θ')| + |-(Real.sin θ ^ 2 - Real.sin θ' ^ 2)| :=
        abs_add_le _ _
    _ = |Real.cos (2 * θ) - Real.cos (2 * θ')| + |Real.sin θ ^ 2 - Real.sin θ' ^ 2| := by
        rw [abs_neg]
    _ ≤ 2 * |θ - θ'| + 2 * |θ - θ'| := add_le_add hcos hsin
    _ = 4 * |θ - θ'| := by ring

/-- **The angular coefficient `c₂` is a `Jet`** with constant `4`: it is bounded by `2` and
`4`-Lipschitz, and a bounded Lipschitz function is `α`-Hölder for `0 < α ≤ 1`. -/
theorem jN0_c2m {α S : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.Regularity.Jet α S 4 (fun _ θ _ => Work.Construction.c2m θ) := by
  refine ⟨by norm_num, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    exact le_trans (jN0_c2m_abs θ) (by norm_num)
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    set d := |z - z'| + |θ - θ'| + |τ - τ'| with hd
    have hd0 : 0 ≤ d := by rw [hd]; positivity
    have h2 : |Work.Construction.c2m θ - Work.Construction.c2m θ'| ≤ 4 := by
      rw [sub_eq_add_neg]
      calc |Work.Construction.c2m θ + -Work.Construction.c2m θ'|
          ≤ |Work.Construction.c2m θ| + |-Work.Construction.c2m θ'| := abs_add_le _ _
        _ = |Work.Construction.c2m θ| + |Work.Construction.c2m θ'| := by rw [abs_neg]
        _ ≤ 2 + 2 := add_le_add (jN0_c2m_abs θ) (jN0_c2m_abs θ')
        _ = 4 := by norm_num
    rcases le_or_gt d 1 with hdle | hdgt
    · have hself : d ≤ d ^ α := Work.FTS.Regularity.self_le_rpow_of_le_one hα hα1 hd0 hdle
      have hθd : |θ - θ'| ≤ d := by rw [hd]; linarith [abs_nonneg (z - z'), abs_nonneg (τ - τ')]
      have h1 := jN0_c2m_lip θ θ'
      have h3 : (4:ℝ) * |θ - θ'| ≤ 4 * d := by linarith [abs_nonneg (θ - θ')]
      have h4 : (4:ℝ) * d ≤ 4 * d ^ α := by linarith [hself]
      linarith
    · have hone : (1:ℝ) ≤ d ^ α := Real.one_le_rpow hdgt.le hα.le
      linarith


end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.RegPkgGal.Der.jet_Nstar =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.RegPkgGal.Der.jet_Nstar`

The modulation term `N_*` of the fake-time equation,

  `N_*(μ,λ,g) = -μ·g - (μ + λ + μλ)·D_z g`   (`Work.Construction.Nstar`),

evaluated on the clock functions `μ(τ)`, `λ(τ)` and on the perturbation family
`(z,θ,τ) ↦ g z θ τ`.  The statement is the `Jet`-regularity of that family:

if `g` and `D_z g(·,·,τ)` are bounded and jointly `α`-Hölder on the strip
`z ≥ 0, θ ∈ Iθ, τ ∈ [0,S]` with constant `N` (`Jet`), and if `μ`, `λ` are bounded by `Nmu` and
`α`-Hölder with constant `Nmu` on `[0,S]`, then `N_*` is again a `Jet` on the strip.

The proof is purely algebraic: `μ`, `λ`, `μλ` and `μ + λ + μλ` are `Jet`s depending on `τ` only
(`Jet.of_time` below), and the `Jet`-calculus of `Submission.Work.FTS.Regularity.regPkg_inhabited`
(`Jet.add`, `Jet.neg`, `Jet.mul`, `Jet.congr`) closes the term under products and sums, with the
constants adding: a product of a `Jet` of constant `N₁` with one of constant `N₂` has constant
`2·N₁·N₂`.

This is exactly the `hNs` hypothesis of `Work.FTS.RegPkgGal.Der.rhs_jet_of_parts`.
-/

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-- A function of `τ` alone which is bounded by `M` on `[0,S]` and `α`-Hölder there with
constant `M` is a `Jet` (constant in `z` and `θ`). -/
theorem Jet.of_time {α S M : ℝ} {m : ℝ → ℝ} (hα0 : 0 ≤ α) (hM : 0 ≤ M)
    (hb : ∀ τ ∈ Set.Icc 0 S, |m τ| ≤ M)
    (hh : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |m τ - m τ'| ≤ M * |τ - τ'| ^ α) :
    Work.FTS.Regularity.Jet α S M (fun _ _ τ => m τ) := by
  refine ⟨hM, fun _ _ τ _ _ hτ => hb τ hτ, ?_⟩
  intro z z' θ θ' τ τ' _ _ _ _ hτ hτ'
  refine le_trans (hh τ hτ τ' hτ') (mul_le_mul_of_nonneg_left ?_ hM)
  refine Real.rpow_le_rpow (abs_nonneg _) ?_ hα0
  have h1 : 0 ≤ |z - z'| := abs_nonneg _
  have h2 : 0 ≤ |θ - θ'| := abs_nonneg _
  have h3 : 0 ≤ |τ - τ'| := abs_nonneg _
  linarith

theorem jet_Nstar {α S : ℝ} {g : ℝ → ℝ → ℝ → ℝ} {mu lam : ℝ → ℝ} {N Nmu : ℝ}
    (hα : 0 < α) (hS : 0 < S)
    (hg : Work.FTS.Regularity.Jet α S N g)
    (hDg : Work.FTS.Regularity.Jet α S N (fun z θ τ => Work.Spaces.Dz (fun z θ => g z θ τ) z θ))
    (hmu : 0 ≤ Nmu ∧ ∀ τ ∈ Set.Icc 0 S, |mu τ| ≤ Nmu ∧ ∀ τ' ∈ Set.Icc 0 S,
      |mu τ - mu τ'| ≤ Nmu * |τ - τ'| ^ α)
    (hlam : ∀ τ ∈ Set.Icc 0 S, |lam τ| ≤ Nmu ∧ ∀ τ' ∈ Set.Icc 0 S,
      |lam τ - lam τ'| ≤ Nmu * |τ - τ'| ^ α) :
    ∃ Nc : ℝ, Work.FTS.Regularity.Jet α S Nc
      (fun z θ τ => Work.Construction.Nstar (mu τ) (lam τ) (fun z θ => g z θ τ) z θ) := by
  obtain ⟨hNmu0, hmu⟩ := hmu
  have hMuh : ∀ τ ∈ Set.Icc 0 S, |mu τ| ≤ Nmu := fun τ hτ => (hmu τ hτ).1
  have hMud : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |mu τ - mu τ'| ≤ Nmu * |τ - τ'| ^ α :=
    fun τ hτ τ' hτ' => (hmu τ hτ).2 τ' hτ'
  have hLamh : ∀ τ ∈ Set.Icc 0 S, |lam τ| ≤ Nmu := fun τ hτ => (hlam τ hτ).1
  have hLamd : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, |lam τ - lam τ'| ≤ Nmu * |τ - τ'| ^ α :=
    fun τ hτ τ' hτ' => (hlam τ hτ).2 τ' hτ'
  have hMuJ : Work.FTS.Regularity.Jet α S Nmu (fun _ _ τ => mu τ) :=
    Jet.of_time hα.le hNmu0 hMuh hMud
  have hLamJ : Work.FTS.Regularity.Jet α S Nmu (fun _ _ τ => lam τ) :=
    Jet.of_time hα.le hNmu0 hLamh hLamd
  have hMuLamJ : Work.FTS.Regularity.Jet α S (2 * Nmu * Nmu) (fun _ _ τ => mu τ * lam τ) :=
    Work.FTS.Regularity.Jet.mul hMuJ hLamJ
  have hCJ : Work.FTS.Regularity.Jet α S ((Nmu + Nmu) + 2 * Nmu * Nmu)
      (fun _ _ τ => mu τ + lam τ + mu τ * lam τ) :=
    Work.FTS.Regularity.Jet.add (Work.FTS.Regularity.Jet.add hMuJ hLamJ) hMuLamJ
  have hMuGJ : Work.FTS.Regularity.Jet α S (2 * Nmu * N) (fun z θ τ => mu τ * g z θ τ) :=
    Work.FTS.Regularity.Jet.mul hMuJ hg
  have hCDgJ : Work.FTS.Regularity.Jet α S (2 * ((Nmu + Nmu) + 2 * Nmu * Nmu) * N)
      (fun z θ τ => (mu τ + lam τ + mu τ * lam τ)
        * Work.Spaces.Dz (fun z θ => g z θ τ) z θ) :=
    Work.FTS.Regularity.Jet.mul hCJ hDg
  refine ⟨2 * Nmu * N + 2 * ((Nmu + Nmu) + 2 * Nmu * Nmu) * N, ?_⟩
  refine Work.FTS.Regularity.Jet.congr
    (Work.FTS.Regularity.Jet.add (Work.FTS.Regularity.Jet.neg hMuGJ)
      (Work.FTS.Regularity.Jet.neg hCDgJ)) ?_
  intro z θ τ hz hθ hτ
  simp only [Work.Construction.Nstar, Work.Spaces.Dz]
  ring

end Work.FTS.RegPkgGal.Der
end
-- ===== merged: Submission.Work.FTS.StrongEps.thetaTraces_Jeps_proof =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace TJ

/-- A real function which is eventually nonnegative and eventually `≤ ε` for every `ε > 0` tends
to `0`. -/
theorem tendsto_zero_of_eventually_le {l : Filter ℝ} {F : ℝ → ℝ}
    (hnn : ∀ᶠ x in l, 0 ≤ F x) (h : ∀ ε' > 0, ∀ᶠ x in l, F x ≤ ε') :
    Tendsto F l (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [hnn] with x hx using lt_of_lt_of_le ha hx
  · have h2 : 0 < b / 2 := by linarith
    filter_upwards [h (b / 2) h2] with x hx using lt_of_le_of_lt hx (by linarith)

/-- **The routed representation of `D_z^s (J_ε f)`**: all `s` radial derivatives are moved onto
the (smooth, compactly supported) kernel by `s` integrations by parts in the shift parameter
`p₁`, so that the integrand carries the *values* of `f` only. -/
theorem mixed_zero_Jeps_routed {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : Fn} (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (s : ℕ) :
    Work.Spaces.mixed s 0 (Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p * f (zShift z p.1) (thShift θ p.2) := by
  rw [mixed_Jeps_kernel_partial ρ hρ hε hsm hz hθ s 0 0 0 (Nat.zero_le s) (le_refl 0)]
  simp only [Nat.sub_zero, pow_zero, one_mul]
  congr 1
  funext p
  simp only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero, EpsE4Thr.KdK, Kd_eq,
    iteratedDeriv_zero]

/-- **The routed kernel vanishes off the ball of radius `ε`** (a point where it does not vanish
satisfies `|p.1| + |p.2| ≤ 2ε`, and here the sharp form holds: the kernel `Kdr ρ a b` of `ρ` is
supported in the unit ball). -/
theorem KdK_eq_zero_of_not_mem {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (a b : ℕ) {p : ℝ × ℝ} (hp : ¬ (max |p.1| |p.2| ≤ ε)) : EpsE4Thr.KdK ρ ε a b p = 0 := by
  have hstep : ∀ u : ℝ, (ε⁻¹ * u) ^ 2 ≤ 1 → |u| ≤ ε := by
    intro u hu
    have h3 : |ε⁻¹ * u| ≤ 1 := (sq_le_one_iff_abs_le_one (ε⁻¹ * u)).mp hu
    rw [abs_mul, abs_of_pos (inv_pos.mpr hε)] at h3
    have h4 : ε⁻¹ * |u| * ε ≤ 1 * ε := mul_le_mul_of_nonneg_right h3 hε.le
    have h5 : ε⁻¹ * |u| * ε = |u| := by field_simp
    linarith
  rw [EpsE4Thr.Kd_Jker_scale hρ ε a b p]
  have hq : EpsE4Thr.Kdr ρ a b (ε⁻¹ • p) = 0 := by
    by_contra hne
    have hsupp := EpsE4Thr.Kdr_support hρ a b (ε⁻¹ • p) hne
    rw [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_eq_mul] at hsupp
    exact hp (max_le (hstep p.1 (by nlinarith [sq_nonneg (ε⁻¹ * p.2)]))
      (hstep p.2 (by nlinarith [sq_nonneg (ε⁻¹ * p.1)])))
  simp only [Jker, hq, mul_zero]

/-- **The routed integral is bounded by the mass of the routed kernel times the sup of `f` on the
window**: the shifted profile is continuous on the compact ball of radius `ε` (the shift maps it
into the open quadrant), and off that ball the routed kernel vanishes. -/
theorem abs_routed_Jeps_le {ρ : ℝ × ℝ → ℝ} (hρ : IsSmoothKernel ρ) {ε : ℝ} (hε : 0 < ε)
    (a b : ℕ) {f : Fn} (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    {z θ M : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hM : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
      |f (zShift z p.1) (thShift θ p.2)| ≤ M) :
    |∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε a b p * f (zShift z p.1) (thShift θ p.2)|
      ≤ (∫ p : ℝ × ℝ, |EpsE4Thr.KdK ρ ε a b p|) * M := by
  have hGz : ∀ p : ℝ × ℝ, ¬ (max |p.1| |p.2| ≤ ε) → EpsE4Thr.KdK ρ ε a b p = 0 :=
    fun p hp => KdK_eq_zero_of_not_mem hρ hε a b hp
  have hGc : ContinuousOn (EpsE4Thr.KdK ρ ε a b) (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    (EpsE4Thr.KdK_continuous hρ ε a b).continuousOn
  have hAc : ContinuousOn (fun p : ℝ × ℝ => f (zShift z p.1) (thShift θ p.2))
      (Metric.closedBall (0 : ℝ × ℝ) ε) :=
    ((hsm 0).continuousOn).comp (continuous_shift_pair z θ).continuousOn
      (fun _ _ => ⟨zShift_pos hz, thShift_mem hθ⟩)
  have hz0 : ∀ p : ℝ × ℝ, p ∉ Metric.closedBall (0 : ℝ × ℝ) ε →
      EpsE4Thr.KdK ρ ε a b p = 0 := fun p hp =>
    hGz p (by rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hp; exact hp)
  have hon1 : IntegrableOn (fun p : ℝ × ℝ => |EpsE4Thr.KdK ρ ε a b p| * M)
      (Metric.closedBall (0 : ℝ × ℝ) ε) volume :=
    ((hGc.abs).mul continuousOn_const).integrableOn_compact (isCompact_closedBall _ _)
  have hInt1 : Integrable (fun p : ℝ × ℝ => |EpsE4Thr.KdK ρ ε a b p| * M) :=
    hon1.integrable_of_forall_notMem_eq_zero (fun p hp => by rw [hz0 p hp, abs_zero, zero_mul])
  have hon2 : IntegrableOn (fun p : ℝ × ℝ => EpsE4Thr.KdK ρ ε a b p
      * f (zShift z p.1) (thShift θ p.2)) (Metric.closedBall (0 : ℝ × ℝ) ε) volume :=
    (hGc.mul hAc).integrableOn_compact (isCompact_closedBall _ _)
  have hInt2 : Integrable (fun p : ℝ × ℝ => EpsE4Thr.KdK ρ ε a b p
      * f (zShift z p.1) (thShift θ p.2)) :=
    hon2.integrable_of_forall_notMem_eq_zero (fun p hp => by rw [hz0 p hp, zero_mul])
  calc |∫ p, EpsE4Thr.KdK ρ ε a b p * f (zShift z p.1) (thShift θ p.2)|
      ≤ ∫ p, |EpsE4Thr.KdK ρ ε a b p * f (zShift z p.1) (thShift θ p.2)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ p, |EpsE4Thr.KdK ρ ε a b p| * M :=
        integral_mono hInt2.abs hInt1 (fun p => by
          by_cases hpm : p ∈ Metric.closedBall (0 : ℝ × ℝ) ε
          · rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at hpm
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left
              (hM p (le_trans (le_max_left _ _) hpm) (le_trans (le_max_right _ _) hpm))
              (abs_nonneg _)
          · rw [hz0 p hpm, zero_mul, abs_zero, zero_mul])
    _ = (∫ p, |EpsE4Thr.KdK ρ ε a b p|) * M := integral_mul_const M _

end TJ

theorem thetaTraces_Jeps_proof {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    {α : ℝ} (hα : α ∈ Set.Ioc 0 1) {ε : ℝ} (hε : 0 < ε) {f : Work.FTS.Galerkin.Fn}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad)
    (ht0 : ∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ →
      ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε')
    (ht1 : ∀ a b : ℕ, a + b ≤ 7 → ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < π / 2 → π / 2 - δ < θ →
      ∀ z : ℝ, 0 < z →
        Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a f z θ) ^ 2 ≤ ε') :
    Work.FTS.PhiStar.ThetaTraces α 10 (Work.FTS.StrongEps.Jeps ρ ε f) := by
  have _hα := hα
  intro s _hs z hz
  -- the routed representation, on the open quadrant
  have hcm : ∀ θ ∈ Set.Ioo 0 (π / 2), Work.Spaces.mixed s 0 (Jeps ρ ε f) z θ
      = ∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p * f (zShift z p.1) (thShift θ p.2) :=
    fun θ hθ => TJ.mixed_zero_Jeps_routed hρ hε hsm hz hθ s
  have hIθ : Set.Ioo 0 (π / 2) ∈ 𝓝[>] (0 : ℝ) :=
    Ioo_mem_nhdsGT (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)
  have hIθ' : Set.Ioo 0 (π / 2) ∈ 𝓝[<] (π / 2) :=
    Ioo_mem_nhdsLT (by linarith [Real.pi_pos] : (0 : ℝ) < π / 2)
  refine ⟨?_, ?_⟩
  · -- ### `θ → 0⁺`
    have hlim : Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p
            * f (zShift z p.1) (thShift θ p.2)) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine TJ.tendsto_zero_of_eventually_le ?_ ?_
      · filter_upwards [hIθ] with θ hθ using
          mul_nonneg (Real.rpow_nonneg (sin_two_nonneg ⟨hθ.1.le, by linarith [hθ.2]⟩) _)
            (sq_nonneg _)
      · intro ε'' hε''
        set K : ℝ := Real.exp (ε * |1 - Work.Spaces.gam α|) with hKdef
        have hKpos : 0 < K := Real.exp_pos _
        set C : ℝ := ∫ p : ℝ × ℝ, |EpsE4Thr.KdK ρ ε s 0 p| with hCdef
        have hC0 : 0 ≤ C := by
          rw [hCdef]; exact integral_nonneg fun p => abs_nonneg _
        obtain ⟨δ, hδpos, hδ⟩ :=
          ht0 0 0 (by norm_num) (ε'' / (C ^ 2 + 1) / K) (by positivity)
        simp only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero] at hδ
        have hθs : ∀ᶠ θ in 𝓝[>] (0 : ℝ), ∀ p : ℝ, |p| ≤ ε → thShift θ p < δ :=
          Traces.eventually_thShift_lt ε δ hδpos
        filter_upwards [hIθ, hθs] with θ hθ hθs
        have hsinpos : 0 < Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_pos_of_pos (sin_two_pos hθ) _
        set M : ℝ := Real.sqrt ((ε'' / (C ^ 2 + 1))
          / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) with hMdef
        have hMn : 0 ≤ M := Real.sqrt_nonneg _
        have hMsq : M ^ 2 = (ε'' / (C ^ 2 + 1))
            / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.sq_sqrt (div_nonneg (by positivity) hsinpos.le)
        have hMb : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
            |f (zShift z p.1) (thShift θ p.2)| ≤ M := by
          intro p hp1 hp2
          have hz1 : 0 < zShift z p.1 := zShift_pos hz
          have hth : thShift θ p.2 ∈ Set.Ioo 0 (π / 2) := thShift_mem hθ
          have hhyp := hδ (thShift θ p.2) hth.1 (hθs p.2 hp2) (zShift z p.1) hz1
          have hcmp := Traces.sin_rpow_thShift_le θ p.2 ε (1 - Work.Spaces.gam α)
            hθ hε.le hp2
          have hsq : (f (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ M ^ 2 := by
            rw [hMsq, le_div_iff₀ hsinpos]
            calc (f (zShift z p.1) (thShift θ p.2)) ^ 2
                  * Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                ≤ (f (zShift z p.1) (thShift θ p.2)) ^ 2
                    * (K * Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)) :=
                  mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)
              _ = K * (Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)
                    * (f (zShift z p.1) (thShift θ p.2)) ^ 2) := by ring
              _ ≤ K * (ε'' / (C ^ 2 + 1) / K) := mul_le_mul_of_nonneg_left hhyp hKpos.le
              _ = ε'' / (C ^ 2 + 1) := by rw [mul_div_cancel₀ _ hKpos.ne']
          have hsq' : |f (zShift z p.1) (thShift θ p.2)| ≤ |M| := sq_le_sq.mp hsq
          rwa [abs_of_nonneg hMn] at hsq'
        have hJep := TJ.abs_routed_Jeps_le hρ hε s 0 hsm hz hθ hMb
        have hjsq : (∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p
            * f (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ (C * M) ^ 2 := by
          rw [← sq_abs, hCdef]
          exact pow_le_pow_left₀ (abs_nonneg _) hJep 2
        calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p
                  * f (zShift z p.1) (thShift θ p.2)) ^ 2
            ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (C * M) ^ 2 :=
              mul_le_mul_of_nonneg_left hjsq hsinpos.le
          _ = C ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * M ^ 2) := by ring
          _ = C ^ 2 * (ε'' / (C ^ 2 + 1)) := by rw [hMsq, mul_div_cancel₀ _ hsinpos.ne']
          _ ≤ ε'' := by
              rw [mul_div_assoc', div_le_iff₀ (by positivity : (0 : ℝ) < C ^ 2 + 1)]
              nlinarith [hε''.le, sq_nonneg C]
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hIθ] with θ hθ
    rw [hcm θ hθ]
  · -- ### `θ → (π/2)⁻`
    have hlim : Tendsto (fun θ : ℝ => Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
        * (∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p
            * f (zShift z p.1) (thShift θ p.2)) ^ 2) (𝓝[<] (π / 2)) (𝓝 0) := by
      refine TJ.tendsto_zero_of_eventually_le ?_ ?_
      · filter_upwards [hIθ'] with θ hθ using
          mul_nonneg (Real.rpow_nonneg (sin_two_nonneg ⟨hθ.1.le, by linarith [hθ.2]⟩) _)
            (sq_nonneg _)
      · intro ε'' hε''
        set K : ℝ := Real.exp (ε * |1 - Work.Spaces.gam α|) with hKdef
        have hKpos : 0 < K := Real.exp_pos _
        set C : ℝ := ∫ p : ℝ × ℝ, |EpsE4Thr.KdK ρ ε s 0 p| with hCdef
        have hC0 : 0 ≤ C := by
          rw [hCdef]; exact integral_nonneg fun p => abs_nonneg _
        obtain ⟨δ, hδpos, hδ⟩ :=
          ht1 0 0 (by norm_num) (ε'' / (C ^ 2 + 1) / K) (by positivity)
        simp only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero] at hδ
        have hθs : ∀ᶠ θ in 𝓝[<] (π / 2), ∀ p : ℝ, |p| ≤ ε → π / 2 - δ < thShift θ p :=
          Traces.eventually_thShift_gt ε δ hδpos
        filter_upwards [hIθ', hθs] with θ hθ hθs
        have hsinpos : 0 < Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.rpow_pos_of_pos (sin_two_pos hθ) _
        set M : ℝ := Real.sqrt ((ε'' / (C ^ 2 + 1))
          / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)) with hMdef
        have hMn : 0 ≤ M := Real.sqrt_nonneg _
        have hMsq : M ^ 2 = (ε'' / (C ^ 2 + 1))
            / Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) :=
          Real.sq_sqrt (div_nonneg (by positivity) hsinpos.le)
        have hMb : ∀ p : ℝ × ℝ, |p.1| ≤ ε → |p.2| ≤ ε →
            |f (zShift z p.1) (thShift θ p.2)| ≤ M := by
          intro p hp1 hp2
          have hz1 : 0 < zShift z p.1 := zShift_pos hz
          have hth : thShift θ p.2 ∈ Set.Ioo 0 (π / 2) := thShift_mem hθ
          have hhyp := hδ (thShift θ p.2) hth.2 (hθs p.2 hp2) (zShift z p.1) hz1
          have hcmp := Traces.sin_rpow_thShift_le θ p.2 ε (1 - Work.Spaces.gam α)
            hθ hε.le hp2
          have hsq : (f (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ M ^ 2 := by
            rw [hMsq, le_div_iff₀ hsinpos]
            calc (f (zShift z p.1) (thShift θ p.2)) ^ 2
                  * Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
                ≤ (f (zShift z p.1) (thShift θ p.2)) ^ 2
                    * (K * Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)) :=
                  mul_le_mul_of_nonneg_left hcmp (sq_nonneg _)
              _ = K * (Real.sin (2 * thShift θ p.2) ^ (1 - Work.Spaces.gam α)
                    * (f (zShift z p.1) (thShift θ p.2)) ^ 2) := by ring
              _ ≤ K * (ε'' / (C ^ 2 + 1) / K) := mul_le_mul_of_nonneg_left hhyp hKpos.le
              _ = ε'' / (C ^ 2 + 1) := by rw [mul_div_cancel₀ _ hKpos.ne']
          have hsq' : |f (zShift z p.1) (thShift θ p.2)| ≤ |M| := sq_le_sq.mp hsq
          rwa [abs_of_nonneg hMn] at hsq'
        have hJep := TJ.abs_routed_Jeps_le hρ hε s 0 hsm hz hθ hMb
        have hjsq : (∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p
            * f (zShift z p.1) (thShift θ p.2)) ^ 2 ≤ (C * M) ^ 2 := by
          rw [← sq_abs, hCdef]
          exact pow_le_pow_left₀ (abs_nonneg _) hJep 2
        calc Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α)
              * (∫ p : ℝ × ℝ, EpsE4Thr.KdK ρ ε s 0 p
                  * f (zShift z p.1) (thShift θ p.2)) ^ 2
            ≤ Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (C * M) ^ 2 :=
              mul_le_mul_of_nonneg_left hjsq hsinpos.le
          _ = C ^ 2 * (Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * M ^ 2) := by ring
          _ = C ^ 2 * (ε'' / (C ^ 2 + 1)) := by rw [hMsq, mul_div_cancel₀ _ hsinpos.ne']
          _ ≤ ε'' := by
              rw [mul_div_assoc', div_le_iff₀ (by positivity : (0 : ℝ) < C ^ 2 + 1)]
              nlinarith [hε''.le, sq_nonneg C]
    refine Tendsto.congr' ?_ hlim
    filter_upwards [hIθ'] with θ hθ
    rw [hcm θ hθ]

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS_MuLamOK.Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_MuLamOK

open Work.FTS.Galerkin (Fn Fam slice muDyn lamDyn)

set_option autoImplicit false

/-! ## The constant family and the three definitional identifications -/

/-- The family which is constant in the fake time `τ`, attached to a single profile `f`:
this is the family at which the `τ = 0` clause of `MuLamOK` is evaluated (the `fun z θ _ => f z θ`
of `EpsLimit.lean`). -/
def constFam (f : Fn) : Fam := fun z θ _ => f z θ

@[simp] theorem constFam_apply (f : Fn) (z θ τ : ℝ) : constFam f z θ τ = f z θ := rfl

@[simp] theorem slice_constFam (f : Fn) (τ : ℝ) : slice (constFam f) τ = f := rfl




/-- The same identification in the literal form in which `MuLamOK` is stated. -/
theorem muDyn_lambda_zero (α : ℝ) (Φs : Fn) (E : Fn → Fn) (f : Fn) :
    muDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ)) (fun z θ _ => f z θ) 0
      = Work.Construction.mufunS α
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f)
          (Work.Construction.N α (Work.Construction.Ftot α f)
            (fun z θ => Φs z θ + E f z θ)) f := rfl

/-- `lamDyn` is `lamfun` of `muDyn`, at the constant family. -/
theorem lamDyn_lambda_zero (α : ℝ) (Φs : Fn) (E : Fn → Fn) (f : Fn) :
    lamDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ)) (fun z θ _ => f z θ) 0
      = Work.Construction.lamfun
          (muDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ))
            (fun z θ _ => f z θ) 0) := rfl

/-! ## The second modulation constant `λ` -/

/-- **`|λ| ≤ 1` when `|μ| ≤ 1/3`.**  `lamfun μ = -2μ/(1+μ)` and `|1+μ| ≥ 1 - |μ| ≥ 2/3`, so
`|λ| ≤ 2·(1/3)/(2/3) = 1`. -/
theorem abs_lamfun_le_one {μ : ℝ} (hμ : |μ| ≤ 1 / 3) : |Work.Construction.lamfun μ| ≤ 1 := by
  have h1 : 1 - |μ| ≤ |1 + μ| := by
    have h := abs_sub_abs_le_abs_sub (1 : ℝ) (-μ)
    simpa [abs_neg, sub_neg_eq_add] using h
  have hpos : (0 : ℝ) < |1 + μ| := by linarith [abs_nonneg μ]
  have key : 2 * |μ| ≤ |1 + μ| := by linarith [hμ, h1, abs_nonneg μ]
  rw [Work.Construction.lamfun, abs_div, abs_mul, abs_neg]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2, div_le_iff₀ hpos]
  linarith [key]

/-! ## The three zero-mode estimates as an interface -/

/-- **`Z₀`**: the zero mode of `N₀` on `ClassC` profiles of `ℋ⁴`-size `≤ C₀α²`:
`|L₁₂(N₀ α (F_*+f) f)(0)| ≤ K α²`. -/
def ZeroMode0 (α C₀ K : ℝ) : Prop :=
  ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
    |Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0|
      ≤ K * α ^ 2

/-- **`Z₁`**: the zero mode of `N` on `ClassC` profiles of `ℋ⁴`-size `≤ C₀α²`, evaluated with
the canonical stream function `Φs + E f`: `|L₁₂(N α (F_*+f) (Φs+Ef))(0)| ≤ K α²`. -/
def ZeroMode1 (α C₀ K : ℝ) (Φs : Fn) (E : Fn → Fn) : Prop :=
  ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
    |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + E f z θ)) 0| ≤ K * α ^ 2

/-- **`Z₂`**: the zero mode of the transport term `3 D_θf/(1+z)` on `ClassC` profiles of
`ℋ⁴`-size `≤ C₀α²`: `|L₁₂(3D_θf/(1+z))(0)| ≤ K α²`. -/
def ZeroMode2 (α C₀ K : ℝ) : Prop :=
  ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
    |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0| ≤ K * α ^ 2

/-! ## The μ-bound from the three zero modes -/

/-- **The modulation is `≤ 3Kα/2`.**  `2α μ` is the sum of the three `L₁₂`-zero-modes, each of
size `≤ K α²`, so `|μ| ≤ (1/(2α))·3Kα² = 3Kα/2`. -/
theorem abs_muDyn_le_three_halves {α C₀ K : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hα : 0 < α) (h0 : ZeroMode0 α C₀ K) (h1 : ZeroMode1 α C₀ K Φs E)
    (h2 : ZeroMode2 α C₀ K) :
    ∀ f : Fn, Work.FTS.ClassC.ClassC α f → Work.FTS.Nonlin.Xn α f ≤ C₀ * α ^ 2 →
      |muDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ))
        (fun z θ _ => f z θ) 0| ≤ 3 * K * α / 2 := by
  intro f hf hX
  have hA0 := h0 f hf hX
  have hA1 := h1 f hf hX
  have hA2 := h2 f hf hX
  rw [muDyn_lambda_zero]
  have hfac : Work.Construction.mufunS α
        (Work.Construction.N0 α (Work.Construction.Ftot α f) f)
        (Work.Construction.N α (Work.Construction.Ftot α f) (fun z θ => Φs z θ + E f z θ)) f
      = (1 / (2 * α)) * (Work.Construction.L12
            (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0
          + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
              (fun z θ => Φs z θ + E f z θ)) 0)
        + (1 / (2 * α)) * Work.Construction.L12
            (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0 := rfl
  rw [hfac]
  have hval : (1 / (2 * α)) * (3 * (K * α ^ 2)) = 3 * K * α / 2 := by
    field_simp
  have hmain : |(1 / (2 * α)) * (Work.Construction.L12
          (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0
        + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
            (fun z θ => Φs z θ + E f z θ)) 0)
      + (1 / (2 * α)) * Work.Construction.L12
          (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0|
      ≤ (1 / (2 * α)) * (3 * (K * α ^ 2)) := by
    have hre : (1 / (2 * α)) * (Work.Construction.L12
            (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0
          + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
              (fun z θ => Φs z θ + E f z θ)) 0)
        + (1 / (2 * α)) * Work.Construction.L12
            (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0
        = (1 / (2 * α))
          * ((Work.Construction.L12 (Work.Construction.N0 α (Work.Construction.Ftot α f) f) 0
              + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
                  (fun z θ => Φs z θ + E f z θ)) 0)
            + Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0) := by
      ring
    rw [hre, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * α))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    linarith [abs_add_le (Work.Construction.L12 (Work.Construction.N0 α
            (Work.Construction.Ftot α f) f) 0)
          (Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
              (fun z θ => Φs z θ + E f z θ)) 0),
      abs_add_le (Work.Construction.L12 (Work.Construction.N0 α
            (Work.Construction.Ftot α f) f) 0
          + Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
              (fun z θ => Φs z θ + E f z θ)) 0)
          (Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth f z θ / (1 + z)) 0),
      hA0, hA1, hA2]
  rw [hval] at hmain
  exact hmain

/-! ## The reduction -/

/-- **The μ/λ clause from the three zero-mode estimates.**  For `9Kα ≤ 2` one has
`|μ| ≤ 3Kα/2 ≤ 1/3`, hence `|λ| ≤ 1`, which is exactly the conjunction of
`Work.FTS.StrongEps.MuLamOK` (`|μ| ≤ 1/2` and `|λ| ≤ 1`). -/
theorem MuLamOK_of_zeroModes {α C₀ K : ℝ} {Φs : Fn} {E : Fn → Fn}
    (hα : 0 < α) (h0 : ZeroMode0 α C₀ K) (h1 : ZeroMode1 α C₀ K Φs E)
    (h2 : ZeroMode2 α C₀ K) (hsmall : 9 * K * α ≤ 2) :
    Work.FTS.StrongEps.MuLamOK α C₀ Φs E := by
  intro f hf hX
  have hmu := abs_muDyn_le_three_halves hα h0 h1 h2 f hf hX
  have hthird : |muDyn α (Work.FTS.Nonlin.PsiCan Φs E (fun z θ _ => f z θ))
      (fun z θ _ => f z θ) 0| ≤ 1 / 3 := by
    linarith
  exact ⟨by linarith, by rw [lamDyn_lambda_zero]; exact abs_lamfun_le_one hthird⟩

end Work.FTS_MuLamOK
end
end
