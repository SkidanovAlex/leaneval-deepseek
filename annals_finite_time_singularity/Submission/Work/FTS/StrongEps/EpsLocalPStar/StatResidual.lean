import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.LinearCombination
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.StrongEps.E5Extract
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs
import Submission.Work.FTS.StrongEps.EpsSqTools.LinAux.LinPartAux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Stability.MainLHSSubN
-- ===== merged: Submission.Work.FTS.StrongEps.E5Clauses =====
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

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The two boundary clauses -/

/-- **`init`.**  The clamp attains the datum at `τ = 0`, because the *approximants* do: at
`τ = 0` every `slice (G k) 0` is the datum (`IsEpsSolP.init`), so the limit `F 0` agrees with
`g₀` on the open quadrant, and the clamp agrees with the datum off it. -/
theorem E5_init {α B T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {ε : ℕ → ℝ} {G : ℕ → Fam} {φ : ℕ → ℕ} {F : ℝ → Fn}
    (hsol : ∀ k : ℕ, IsEpsSolP α ρ (ε k) T Φs E g₀ (G k))
    (hconv0 : ConvLocUnifH6 α B (fun n => slice (G (φ n)) 0) (F 0)) :
    ∀ z θ, clampQ F g₀ z θ 0 = g₀ z θ := by
  refine clampQ_init ?_
  intro z θ hz hθ
  have hK : ({(z, θ)} : Set (ℝ × ℝ)) ⊆ Work.FTS.EllipticEst.Q0 := by
    intro p hp
    rw [Set.mem_singleton_iff] at hp
    subst hp
    exact Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hpt : Filter.Tendsto (fun n : ℕ => slice (G (φ n)) 0 z θ) Filter.atTop
      (𝓝 (F 0 z θ)) := by
    have h1 := (hconv0.conv {(z, θ)} isCompact_singleton hK 0 0 (by norm_num)).tendsto_at
      (Set.mem_singleton _)
    simpa only [Work.Spaces.mixed_zero_right, Work.Spaces.DzIter_zero,
      Work.FTS.Galerkin.slice_apply] using h1
  have hconst : (fun n : ℕ => slice (G (φ n)) 0 z θ) = fun _ : ℕ => g₀ z θ := by
    funext n
    exact (hsol (φ n)).1 z θ
  rw [hconst] at hpt
  exact tendsto_nhds_unique hpt tendsto_const_nhds

/-- **`vanish`.**  The clamp vanishes on the two angular boundary lines for `z ≥ 0` as soon as
the datum does — which is the first conjunct of `EpsUniformMem` (and a *necessary* condition,
`EpsLimNecessary.ExistsLimH.datum_vanish`). -/
theorem E5_vanish {F : ℝ → Fn} {g₀ : Fn}
    (hvan : ∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) :
    ∀ τ z, 0 ≤ z → clampQ F g₀ z 0 τ = 0 ∧ clampQ F g₀ z (π / 2) τ = 0 :=
  clampQ_vanish hvan

/-! ## The space-regularity clause -/

/-- **`c4`.**  The clamped limit family is `C⁴` in space at every `τ ∈ Icc 0 T`. -/
theorem E5_c4 {α B T : ℝ} {g₀ : Fn} {G : ℕ → Fam} {φ : ℕ → ℕ} {F : ℝ → Fn}
    (hconv : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ConvLocUnifH6 α B (fun n => slice (G (φ n)) τ) (F τ)) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ContDiffOn ℝ 4 (Function.uncurry (slice (clampQ F g₀) τ))
        Work.FTS.EllipticEst.Q0 :=
  fun τ hτ => clampQ_contDiffOn (hconv τ hτ).contDiffOn

/-! ## The two norm clauses -/

/-- **`bd6`.**  The uniform `ℋ⁶`-bound of the limit is the one carried by the extraction; nothing
is re-derived on the limit slice. -/
theorem E5_bd6 {α B T : ℝ} {g₀ : Fn} {G : ℕ → Fam} {φ : ℕ → ℕ} {F : ℝ → Fn}
    (hconvL : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ConvLev0H6 α B (fun n => slice (G (φ n)) τ) (F τ)) :
    ∃ B' : ℝ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α (slice (clampQ F g₀) τ) ≤ B' := by
  refine ⟨B, fun τ hτ => ?_⟩
  have h := clampQ_hkNorm α 6 F g₀ τ
  show Work.Spaces.HkNorm α 6 (slice (clampQ F g₀) τ) ≤ B
  rw [h]
  exact (hconvL τ hτ).hkNorm_le

/-- **`bd4`.**  The uniform `ℋ⁴`-bound of the limit, by lower semicontinuity of the `ℋ⁴`-energy
along the slotwise local uniform convergence (`Xn_le_of_convLocUnif`).  The input is the uniform
`ℋ⁴`-bound and membership of the **converging** sequence — this is the clause that the `P₀`
projection perturbs (see `NOTES_session13.md` §2). -/
theorem E5_bd4 {α B C₀ T : ℝ} {g₀ : Fn} {G : ℕ → Fam} {φ : ℕ → ℕ} {F : ℝ → Fn}
    (hconv : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ConvLocUnifH6 α B (fun n => slice (G (φ n)) τ) (F τ))
    (hmem : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ n : ℕ,
      Work.Spaces.HkMem α 4 (slice (G (φ n)) τ))
    (hb : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ n : ℕ,
      Work.FTS.Nonlin.Xn α (slice (G (φ n)) τ) ≤ C₀ * α ^ 2) :
    ∀ τ ∈ Set.Icc (0 : ℝ) T, Work.FTS.Nonlin.Xn α (slice (clampQ F g₀) τ) ≤ C₀ * α ^ 2 := by
  intro τ hτ
  have h := clampQ_hkNorm α 4 F g₀ τ
  show Work.Spaces.HkNorm α 4 (slice (clampQ F g₀) τ) ≤ C₀ * α ^ 2
  rw [h]
  exact EpsLimBd4 (hconv τ hτ) (hmem τ hτ) (hb τ hτ)

/-- **`mem4`.**  The honest `ℋ⁴`-membership of the limit slice, from the proved `EpsLimMem4`
(whose per-`z` bound is *not* removable — `HkMem` is a per-`z` condition while Fatou gives it only
a.e. in `z`). -/
theorem E5_mem4 {α B : ℝ} (g₀ : Fn) {G : ℕ → Fn} {F : ℝ → Fn} {τ : ℝ}
    (hconv : ConvLocUnifH6 α B G (F τ))
    (hsm : ∀ n : ℕ, ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry (G n)) Work.FTS.EllipticEst.Q0)
    (hmem : ∀ n : ℕ, Work.Spaces.HkMem α 6 (G n))
    (hb : ∀ n : ℕ, Work.Spaces.HkNorm α 6 (G n) ≤ B)
    (hz : ∀ z ∈ Work.Spaces.Iz, ∃ Bz : ℝ, ∀ n : ℕ,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 (G n) z θ) ≤ Bz) :
    Work.Spaces.HkMem α 4 (slice (clampQ F g₀) τ) ∧
      Work.Spaces.HkNorm α 4 (slice (clampQ F g₀) τ) ≤ B := by
  obtain ⟨hm, hb'⟩ := EpsLimMem4 hconv hsm hmem hb hz
  have h := clampQ_hkNorm α 4 F g₀ τ
  refine ⟨clampQ_hkMem α 4 hm, ?_⟩
  show Work.Spaces.HkNorm α 4 (slice (clampQ F g₀) τ) ≤ B
  rw [h]; exact hb'

/-! ## The fake-time continuity of the limit family -/

/-- **`cont`.**  Continuity in the fake time, at every point of the open quadrant: the
τ-Lipschitz property of the approximants passes to the limit (`EpsLimCont`), and the clamp is
constant off the open angular interval. -/
theorem E5_cont {α B T : ℝ} {g₀ : Fn} {G : ℕ → Fam} {F : ℝ → Fn}
    (hconvL : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ConvLev0H6 α B (fun n => slice (G n) τ) (F τ))
    (hlip : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ τ ∈ Set.Icc (0 : ℝ) T,
        ∀ τ' ∈ Set.Icc (0 : ℝ) T,
          |slice (G n) τ p.1 p.2 - slice (G n) τ' p.1 p.2| ≤ C * |τ - τ'|) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      ContinuousOn (fun τ => clampQ F g₀ z θ τ) (Set.Icc (0 : ℝ) T) := by
  intro z θ hzθ
  exact clampQ_continuousOn hzθ.1 ⟨hzθ.2.1, hzθ.2.2⟩ (EpsLimCont hconvL hlip z θ hzθ)

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5ExtractHbdd =====
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

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The extraction, from the value bound of `epsRHSP`.**  Same conclusion as `E5Extract`, with
`hequi` produced by `EpsProfileLip` instead of `E5Equi`. -/
theorem E5Extract_of_hbdd {α B T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {ε : ℕ → ℝ} {G : ℕ → Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ)
    (hε : ∀ k : ℕ, ε k ∈ Set.Ioc 0 1)
    (hsol : ∀ k : ℕ, IsEpsSolP α ρ (ε k) T Φs E g₀ (G k))
    (hsm : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.EllipticEst.SmoothOpen (slice (G k) τ))
    (hmem6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.Spaces.HkMem α 6 (slice (G k) τ))
    (hb6 : ∀ k : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T,
      Work.FTS.StrongGlobal.Xn6 α (slice (G k) τ) ≤ B)
    (hcont : ∀ k : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => epsRHSP α ρ (ε k) Φs E (G k) s p.1 p.2) (Set.Icc 0 T))
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p ∈ K,
        |epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C) :
    ∃ (φ : ℕ → ℕ) (F : ℝ → Fn), StrictMono φ ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) T,
        ConvLocUnifH6 α B (fun n => slice (G (φ n)) τ) (F τ) := by
  -- the raw `ContDiffOn` form of the smoothness clause, as `EpsConvRat` asks for it
  have hsm' : ∀ n : ℕ, ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ k : ℕ,
      ContDiffOn ℝ k (Function.uncurry (slice (G n) τ))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    fun n τ hτ k => (hsm n τ hτ).forall k
  -- **Step 1.** the diagonal extraction over the rational times
  obtain ⟨φ, F, hφ, hconvR⟩ := EpsConvRat (α := α) (B := B) (T := T) hα.1
    (G := G) hsm' hmem6 hb6
  -- the level-`0` Lipschitz property of the profiles, from the *value* bound only
  have hequi := EpsProfileLip (α := α) (T := T) (ρ := ρ) (Φs := Φs) (E := E) (g₀ := g₀)
    (ε := ε) (G := G) hsol hcont hbdd
  -- **Step 2.** the limit at the given `τ` (a fresh extraction, coherent via Cauchy)
  have hAll : ∀ τ ∈ Set.Icc (0 : ℝ) T,
      ∃ f : Fn, ConvLocUnifH6 α B (fun n => slice (G (φ n)) τ) f :=
    fun τ hτ => EpsConvAllTau (α := α) (B := B) (T := T) hα.1 (G := G) (F := F) (φ := φ) hφ
      hsm' hmem6 hb6 (fun σ hσ => (hconvR σ hσ).toLev0) hequi τ hτ
  -- **Step 3.** the two pieces, as a total function of `τ`
  have htot : ∀ τ : ℝ, ∃ f : Fn,
      τ ∈ Set.Icc (0 : ℝ) T → ConvLocUnifH6 α B (fun n => slice (G (φ n)) τ) f := by
    intro τ
    by_cases hT : τ ∈ Set.Icc (0 : ℝ) T
    · by_cases hq : τ ∈ Set.range (fun q : ℚ => (q : ℝ))
      · exact ⟨F τ, fun _ => hconvR τ ⟨hT, hq⟩⟩
      · obtain ⟨f, hf⟩ := hAll τ hT
        exact ⟨f, fun _ => hf⟩
    · exact ⟨F τ, fun h => absurd h hT⟩
  refine ⟨φ, fun τ => Classical.choose (htot τ), hφ, fun τ hτ => ?_⟩
  exact Classical.choose_spec (htot τ) hτ

end Work.FTS.StrongEps
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.StatResidual =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open Work.FTS.Galerkin (Fn Fam slice famOf)

set_option autoImplicit false
set_option maxHeartbeats 1600000


end Work.FTS.StrongEps.EpsLocalPStar
end
