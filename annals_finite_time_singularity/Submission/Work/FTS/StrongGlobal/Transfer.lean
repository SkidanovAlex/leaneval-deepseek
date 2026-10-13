/-
# `Work.FTS.StrongGlobal.Transfer` — from the pieces to the global strong solution

This module contains the *last* step of S5: given a family `g` which agrees, near every fake time
`τ ≥ 0`, with the single accumulated piece `G (pIdx δ τ)` (and which is the first piece `G 0` at
negative fake time) — and given that every `G n` is an accumulated piece (`PieceData`, i.e. a
strong solution on `[0, stepEnd δ n]` with the a-priori `ℋ⁴`-bound `C₀α²` and the `ℋ⁶`-bound
`Kα²`) — the family `g` **is** a global strong solution:

* `IsDynGSolWith (IsBslSolPos α) α (PsiCan Φs EllSol g) g`;
* the datum identity `g (·,·,0) = g₀`;
* the *regularity package* `RegPkgMin α g`, i.e. the interface consumed by `Work.FTS.RegPkgGal`:
  joint `C¹` on the open slab, `C⁴` in space at every time (through the Sobolev input S3
  `SobolevC4`), continuity in fake time, `ℋ⁴`-membership, a uniform `ℋ³`-bound on `∂_τg` (through
  S6 `DbDStrong`) and the vanishing on the angular boundaries;
* the uniform a-priori bound `Xn α (slice g τ) ≤ C₀α²` for all `τ ≥ 0`.

The transfer is *pointwise in the fake time*: every field of `StrongSolOn`/`RegPkgMin` is read at a
time `τ ≥ 0` from the piece `G (pIdx δ τ)`, using the agreement on the interval
`((n)δ - δ, nδ + δ)`, which is a *neighbourhood* of `τ` — one unit of slack on each side plus the
nesting of the pieces (`Work.FTS.StrongGlobal.Gglob_eq_piece_near`).  The two right-hand sides
`dynLin`, `dynRHS` and the canonical stream function `PsiCan Φs EllSol` depend on the family only
through its slice (`dynLin_congr`, `dynRHS_congr`, `slice_PsiCan_congr`, `Ftau_congr`), so all the
congruences are immediate once the slices agree at `τ`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongGlobal.Global

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongGlobal

open Work.FTS.Nonlin
open Work.FTS.Apriori
open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS gdot IsDynEqOn IsDynGSolWith)

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {α : ℝ} {Φs : Fn} {EllSol : Fn → Fn}

/-- The decomposition of `(z,θ) ∈ Qd`. -/
theorem mem_Qd_parts {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 := by
  rw [Work.Construction.Qd, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- The index of a negative fake time is `0`. -/
theorem pIdx_of_neg {δ τ : ℝ} (hδ : 0 < δ) (h : τ < 0) : pIdx δ τ = 0 := by
  rw [pIdx, Nat.floor_of_nonpos]
  exact div_nonpos_of_nonpos_of_nonneg h.le hδ.le

/-- **The regularity transfer.**  A family which agrees near every fake time with a single
accumulated piece is a global strong solution with `RegPkgMin`. -/
theorem global_of_agree {IP : ℝ → Fn → Fn → ℝ} {δ C₀ K Cd : ℝ} {g₀ : Fn} {G : ℕ → Fam}
    {g : Fam} (hδ : 0 < δ)
    (hpiece : ∀ n, PieceData α Φs EllSol g₀ δ C₀ K n (G n))
    (hagree : ∀ {n : ℕ} {τ : ℝ}, 0 ≤ τ → pIdx δ τ = n → ∀ z θ τ',
      τ' ∈ Set.Ioo ((n : ℝ) * δ - δ) ((n : ℝ) * δ + δ) → g z θ τ' = G n z θ τ')
    (hagree0 : ∀ z θ τ', τ' < 0 → g z θ τ' = G 0 z θ τ')
    (hSob : SobolevC4 α) (hDbd : DbDStrong α Φs EllSol C₀ Cd) :
    IsDynGSolWith (IsBslSolPos α) α (PsiCan Φs EllSol g) g ∧
      (∀ z θ, g z θ 0 = g₀ z θ) ∧ RegPkgMin α g ∧
      (∀ τ, 0 ≤ τ → Xn α (slice g τ) ≤ C₀ * α ^ 2) := by
  -- `τ ≤ stepEnd δ (pIdx δ τ)` and `τ` lies in the open interval of its piece
  have hsub : ∀ {n : ℕ} {τ : ℝ}, pIdx δ τ = n → τ ≤ stepEnd δ n := by
    intro n τ hn
    have h1 := lt_pIdx_succ (δ := δ) (τ := τ) hδ
    rw [hn] at h1
    rw [stepEnd]
    exact h1.le
  have hmem_interval : ∀ {n : ℕ} {τ : ℝ}, 0 ≤ τ → pIdx δ τ = n →
      τ ∈ Set.Ioo ((n : ℝ) * δ - δ) ((n : ℝ) * δ + δ) := by
    intro n τ hτ hn
    refine ⟨?_, ?_⟩
    · have h1 := mul_pIdx_le hδ hτ
      rw [hn] at h1
      linarith
    · have h1 := lt_pIdx_succ (δ := δ) (τ := τ) hδ
      rw [hn] at h1
      have h2 : (((n : ℝ)) + 1) * δ = (n : ℝ) * δ + δ := by ring
      rw [h2] at h1
      exact h1
  -- locality of `g`
  have hlocs : ∀ p : P3, uncurry3 g =ᶠ[𝓝 p] uncurry3 (G (pIdx δ p.2.2)) := by
    intro p
    by_cases hneg : p.2.2 < 0
    · have hneigh : {q : P3 | q.2.2 < 0} ∈ 𝓝 p :=
        (isOpen_lt (continuous_snd.comp continuous_snd) continuous_const).mem_nhds hneg
      have hp0 : pIdx δ p.2.2 = 0 := pIdx_of_neg hδ hneg
      filter_upwards [hneigh] with q hq
      rw [hp0]
      change g q.1 q.2.1 q.2.2 = G 0 q.1 q.2.1 q.2.2
      exact hagree0 q.1 q.2.1 q.2.2 hq
    · have hpnn : 0 ≤ p.2.2 := le_of_not_gt hneg
      have hmemc : {q : P3 | q.2.2 ∈ Set.Ioo (((pIdx δ p.2.2 : ℕ) : ℝ) * δ - δ)
          (((pIdx δ p.2.2 : ℕ) : ℝ) * δ + δ)} ∈ 𝓝 p :=
        (isOpen_Ioo.preimage (continuous_snd.comp continuous_snd)).mem_nhds
          (hmem_interval hpnn rfl)
      filter_upwards [hmemc] with q hq
      exact hagree hpnn rfl q.1 q.2.1 q.2.2 hq
  -- the slice identity at a covered time
  have hslice : ∀ {n : ℕ} {τ : ℝ}, 0 ≤ τ → pIdx δ τ = n → slice g τ = slice (G n) τ := by
    intro n τ hτ hn
    funext z θ
    exact hagree hτ hn z θ τ (hmem_interval hτ hn)
  -- differentiability of the fake-time slice of `g`
  have hslice_diff : ∀ {z θ τ : ℝ} (hτ : 0 ≤ τ)
      (hq : 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2), DifferentiableAt ℝ (fun s => g z θ s) τ := by
    intro z θ τ hτ hq
    obtain ⟨hz, hθ, hθ'⟩ := hq
    have hmem := hmem_interval hτ rfl
    have hU : Set.Ioo (((pIdx δ τ : ℕ) : ℝ) * δ - δ) (((pIdx δ τ : ℕ) : ℝ) * δ + δ) ∈ 𝓝 τ :=
      (isOpen_Ioo).mem_nhds hmem
    have hev : (fun s => g z θ s) =ᶠ[𝓝 τ] (fun s => G (pIdx δ τ) z θ s) := by
      filter_upwards [hU] with s hs
      exact hagree hτ rfl z θ s hs
    have hmemc1 : (z, θ, τ) ∈ slab (0 - 1) (stepEnd δ (pIdx δ τ) + 1) := by
      refine mem_slab.mpr ⟨hz, hθ, hθ', by linarith, ?_⟩
      have h1 := hsub (n := pIdx δ τ) (τ := τ) rfl
      linarith
    have hcat : ContDiffAt ℝ 1 (uncurry3 (G (pIdx δ τ))) (z, θ, τ) :=
      ((hpiece (pIdx δ τ)).sol.c1.contDiffWithinAt hmemc1).contDiffAt
        ((isOpen_slab _ _).mem_nhds hmemc1)
    exact hev.differentiableAt_iff.mpr (differentiableAt_slice_of_contDiffAt hcat)
  -- the value of the derivative of the fake-time slice
  have hslice_deriv : ∀ {z θ τ : ℝ} (hτ : 0 ≤ τ) (hq : 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2),
      deriv (fun s => g z θ s) τ
        = dynLin α (G (pIdx δ τ)) τ z θ
          + dynRHS α (PsiCan Φs EllSol (G (pIdx δ τ))) (G (pIdx δ τ)) τ z θ := by
    intro z θ τ hτ hq
    obtain ⟨hz, hθ, hθ'⟩ := hq
    have hmem := hmem_interval hτ rfl
    have hU : Set.Ioo (((pIdx δ τ : ℕ) : ℝ) * δ - δ) (((pIdx δ τ : ℕ) : ℝ) * δ + δ) ∈ 𝓝 τ :=
      (isOpen_Ioo).mem_nhds hmem
    have hev : (fun s => g z θ s) =ᶠ[𝓝 τ] (fun s => G (pIdx δ τ) z θ s) := by
      filter_upwards [hU] with s hs
      exact hagree hτ rfl z θ s hs
    rw [hev.deriv_eq]
    refine deriv_eq_of_hasDerivWithinAt_Icc (stepEnd_pos hδ _) ⟨hτ, hsub rfl⟩ ?_ ?_
    · exact (hpiece (pIdx δ τ)).sol.eq z θ τ ⟨hτ, hsub rfl⟩ ⟨hz, hθ, hθ'⟩
    · have hmemc1 : (z, θ, τ) ∈ slab (0 - 1) (stepEnd δ (pIdx δ τ) + 1) := by
        refine mem_slab.mpr ⟨hz, hθ, hθ', by linarith, ?_⟩
        have h1 := hsub (n := pIdx δ τ) (τ := τ) rfl
        linarith
      have hcat : ContDiffAt ℝ 1 (uncurry3 (G (pIdx δ τ))) (z, θ, τ) :=
        ((hpiece (pIdx δ τ)).sol.c1.contDiffWithinAt hmemc1).contDiffAt
          ((isOpen_slab _ _).mem_nhds hmemc1)
      exact differentiableAt_slice_of_contDiffAt hcat
  -- the two-sided fake-time derivative, and the equation
  have hderiv_at : ∀ {z θ τ : ℝ}, 0 ≤ τ → (z, θ) ∈ Work.Construction.Qd →
      HasDerivAt (fun s => g z θ s)
        (dynLin α g τ z θ + dynRHS α (PsiCan Φs EllSol g) g τ z θ) τ := by
    intro z θ τ hτ hz
    obtain ⟨hz1, hz2, hz3⟩ := mem_Qd_parts hz
    have hsl := hslice hτ rfl
    have hder := hslice_deriv hτ ⟨hz1, hz2, hz3⟩
    have hdiff := hslice_diff hτ ⟨hz1, hz2, hz3⟩
    have hval : dynLin α (G (pIdx δ τ)) τ z θ
        + dynRHS α (PsiCan Φs EllSol (G (pIdx δ τ))) (G (pIdx δ τ)) τ z θ
        = dynLin α g τ z θ + dynRHS α (PsiCan Φs EllSol g) g τ z θ := by
      rw [← dynLin_congr hsl, ← dynRHS_congr hsl]
    have h := hdiff.hasDerivAt
    rw [hder, hval] at h
    exact h
  have heq : IsDynEqOn α (PsiCan Φs EllSol g) g :=
    fun z θ τ hτ hz => (hderiv_at hτ hz).hasDerivWithinAt
  -- the elliptic law
  have hlaw : ∀ τ, 0 ≤ τ → IsBslSolPos α (Work.Construction.Ftau α g τ)
      (slice (PsiCan Φs EllSol g) τ) := by
    intro τ hτ
    have hsl := hslice hτ rfl
    have hp := (hpiece (pIdx δ τ)).sol.law τ ⟨hτ, hsub rfl⟩
    exact hp.congr (Ftau_congr hsl.symm) (slice_PsiCan_congr hsl.symm)
  -- the strong-solution fields at every finite horizon
  have hglob : ∀ n : ℕ, StrongSolOn α Φs EllSol 0 (stepEnd δ n) g := by
    intro n
    refine ⟨stepEnd_nonneg hδ n, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z θ τ hτ hz
      exact (hderiv_at hτ.1 hz).hasDerivWithinAt
    · exact fun τ hτ => hlaw τ hτ.1
    · intro τ hτ
      rw [hslice hτ.1 rfl]
      exact (hpiece (pIdx δ τ)).sol.gal τ ⟨hτ.1, hsub rfl⟩
    · intro p hp
      obtain ⟨hz, hθ, hθ', hp4, -⟩ := mem_slab.mp hp
      have hmemc1 : p ∈ slab (0 - 1) (stepEnd δ (pIdx δ p.2.2) + 1) := by
        refine mem_slab.mpr ⟨hz, hθ, hθ', hp4, ?_⟩
        by_cases hneg : p.2.2 < 0
        · rw [pIdx_of_neg hδ hneg, stepEnd]
          push_cast
          linarith
        · have h1 := hsub (n := pIdx δ p.2.2) (τ := p.2.2) rfl
          linarith
      have hcj : ContDiffAt ℝ 1 (uncurry3 (G (pIdx δ p.2.2))) p :=
        ((hpiece (pIdx δ p.2.2)).sol.c1.contDiffWithinAt hmemc1).contDiffAt
          ((isOpen_slab _ _).mem_nhds hmemc1)
      exact (hcj.congr_of_eventuallyEq (hlocs p)).contDiffWithinAt
    · intro τ hτ
      rw [dynLin_congr (hslice hτ.1 rfl)]
      exact (hpiece (pIdx δ τ)).sol.regLin τ ⟨hτ.1, hsub rfl⟩
    · intro τ hτ
      rw [dynRHS_congr (hslice hτ.1 rfl)]
      exact (hpiece (pIdx δ τ)).sol.regRHS τ ⟨hτ.1, hsub rfl⟩
  refine ⟨⟨hlaw, heq⟩, ?_, ?_, ?_⟩
  · -- the datum
    intro z θ
    have h0 : pIdx δ 0 = 0 :=
      (pIdx_eq_iff (τ := 0) hδ (le_refl 0)).mpr ⟨by norm_num, by simpa using hδ⟩
    have hsl := hslice (le_refl 0) h0
    have h1 : g z θ 0 = G 0 z θ 0 := congrFun (congrFun hsl z) θ
    rw [h1]
    exact (hpiece 0).data z θ
  · -- the regularity package
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp
      obtain ⟨hz, hθ, hθ', hτ⟩ := mem_quadSlab.mp hp
      have hmemc1 : p ∈ slab (0 - 1) (stepEnd δ (pIdx δ p.2.2) + 1) := by
        refine mem_slab.mpr ⟨hz, hθ, hθ', by linarith, ?_⟩
        have h1 := hsub (n := pIdx δ p.2.2) (τ := p.2.2) rfl
        linarith
      have hcj : ContDiffAt ℝ 1 (uncurry3 (G (pIdx δ p.2.2))) p :=
        ((hpiece (pIdx δ p.2.2)).sol.c1.contDiffWithinAt hmemc1).contDiffAt
          ((isOpen_slab _ _).mem_nhds hmemc1)
      exact (hcj.congr_of_eventuallyEq (hlocs p)).contDiffWithinAt
    · intro τ hτ
      refine hSob (slice g τ) ?_
      rw [hslice hτ rfl]
      exact (hpiece (pIdx δ τ)).sol.hmem6 τ ⟨hτ, hsub rfl⟩
    · intro z θ hz
      intro τ hτ
      exact (hslice_diff hτ (mem_Qd_parts hz)).continuousAt.continuousWithinAt
    · intro τ hτ
      rw [hslice hτ rfl]
      exact (hpiece (pIdx δ τ)).sol.hmem4 τ ⟨hτ, hsub rfl⟩
    · refine DbdLoc.of_uniform ⟨Cd, fun τ hτ => ?_⟩
      have hbnd : ∀ τ' ∈ Set.Icc 0 (stepEnd δ (pIdx δ τ)), Xn α (slice g τ') ≤ C₀ * α ^ 2 := by
        intro τ' hτ'
        rw [hslice hτ'.1 rfl]
        exact (hpiece (pIdx δ τ')).bnd4 τ' ⟨hτ'.1, hsub rfl⟩
      exact hDbd g (stepEnd δ (pIdx δ τ)) (stepEnd_nonneg hδ _) (hglob (pIdx δ τ))
        hbnd τ ⟨hτ.le, hsub rfl⟩
    · intro τ hτ z hz
      have hsl := hslice hτ rfl
      have hv := (hpiece (pIdx δ τ)).sol.gal τ ⟨hτ, hsub rfl⟩
      constructor
      · have h1 : g z 0 τ = G (pIdx δ τ) z 0 τ := congrFun (congrFun hsl z) 0
        rw [h1]
        exact hv.vanish.1 z
      · have h1 : g z (Real.pi / 2) τ = G (pIdx δ τ) z (Real.pi / 2) τ :=
          congrFun (congrFun hsl z) (Real.pi / 2)
        rw [h1]
        exact hv.vanish.2 z
  · -- the a-priori bound
    intro τ hτ
    rw [hslice hτ rfl]
    exact (hpiece (pIdx δ τ)).bnd4 τ ⟨hτ, hsub rfl⟩

end Work.FTS.StrongGlobal
