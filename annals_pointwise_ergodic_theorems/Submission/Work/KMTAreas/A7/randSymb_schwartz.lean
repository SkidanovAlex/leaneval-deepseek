/-
# The randomised small-scale symbol is a Schwartz function

This module proves `Work.KMTAreas.A7.randSymb_schwartz`: the randomised symbol of the
small-scale tuple,

  `randSymb (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K`

is a Schwartz function on `ℝ`.

**Why this is true.**  `randSymb φ ε K = ∑_{n < K} ε n • (φ (n+1) - φ n)` is a *finite* linear
combination of the translates of the family `φ = smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t`, and the
`m`-th member of that family is either `0` or the modulated Ionescu--Wainger bump
`φ_{N,t} = φ_N · e(N t ·)` at the lacunary scale `N = ⌊a m⌋` (`smallSymbF_apply`).  Each
`φ_{N,t}` is smooth (a `C^∞` rescaled cutoff times a unimodular exponential) and compactly
supported (in the frequency window `|ξ| ≤ 2^{k₁ - Log N}`), hence a Schwartz function.  The
Schwartz space is a complex vector space, so the finite combination is again Schwartz.

The construction of the Schwartz function is explicit: `varphiNtSch N k t` is the Schwartz
realisation of `φ_{N,t}`, `smallSymbFSch … m t` is the `m`-th member of the family as a Schwartz
map (the `if randAct … then … else 0` of `randSymbDefs`), and the witnessing Schwartz function is
`∑_{n < K} ε n • (smallSymbFSch … (n+1) t - smallSymbFSch … n t)`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.randSymbDefs
import Submission.Work.KMTAreas.A7.varphiNt_bounds

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Finset
open scoped BigOperators

/-! ## Smoothness of the bumps at all orders -/

/-- The fixed cutoff `η = kmtEta` is smooth to all orders (it is the complexification of the
`ContDiffBump` `kmtBump`). -/
lemma contDiff_kmtEta_all : ContDiff ℝ (⊤ : ℕ∞) Work.KMTContract.kmtEta :=
  (ContinuousLinearMap.contDiff (n := (⊤ : ℕ∞)) (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)).comp
    (ContDiffBump.contDiff Work.KMTContract.kmtBump (n := ⊤))

/-- The modulated exponential `ξ ↦ e(c ξ)` is smooth to all orders. -/
lemma contDiff_ee_all (c : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => ee (c * ξ)) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => (ξ : ℂ)) :=
    ContinuousLinearMap.contDiff (n := (⊤ : ℕ∞)) (Complex.ofRealCLM : ℝ →L[ℝ] ℂ)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun ξ : ℝ => (2 * ↑Real.pi * Complex.I * ↑c) * (ξ : ℂ)) :=
    contDiff_const.mul h1
  have h3 : ContDiff ℝ (⊤ : ℕ∞)
      (fun ξ : ℝ => Complex.exp ((2 * ↑Real.pi * Complex.I * ↑c) * (ξ : ℂ))) :=
    ContDiff.cexp h2
  have heq : (fun ξ : ℝ => Complex.exp ((2 * ↑Real.pi * Complex.I * ↑c) * (ξ : ℂ)))
      = (fun ξ : ℝ => ee (c * ξ)) := by
    funext ξ
    simp only [ee]
    congr 1
    push_cast
    ring
  rw [heq] at h3
  exact h3

/-- The KMT bump `φ_N` is smooth to all orders. -/
lemma contDiff_varphiN_all (N k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (varphiN N k) := by
  unfold varphiN
  split
  · exact contDiff_kmtEta_all.comp (contDiff_const.mul contDiff_id)
  · exact (contDiff_kmtEta_all.comp (contDiff_const.mul contDiff_id)).sub
      (contDiff_kmtEta_all.comp (contDiff_const.mul contDiff_id))

/-- The modulated bump `φ_{N,t}` is smooth to all orders. -/
lemma contDiff_varphiNt_all (N k : ℕ) (t : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (varphiNt N k t) := by
  unfold varphiNt
  exact (contDiff_varphiN_all N k).mul (contDiff_ee_all ((N : ℝ) * t))

/-! ## The modulated bump as a Schwartz function -/

/-- The modulated bump `φ_{N,t}` as a Schwartz function. -/
noncomputable def varphiNtSch (N k : ℕ) (t : ℝ) : SchwartzMap ℝ ℂ :=
  (hasCompactSupport_varphiNt N k t).toSchwartzMap (contDiff_varphiNt_all N k t)

@[simp] lemma varphiNtSch_apply (N k : ℕ) (t : ℝ) (ξ : ℝ) :
    varphiNtSch N k t ξ = varphiNt N k t ξ :=
  HasCompactSupport.toSchwartzMap_toFun (hasCompactSupport_varphiNt N k t)
    (contDiff_varphiNt_all N k t) ξ

@[simp] lemma varphiNtSch_coe (N k : ℕ) (t : ℝ) :
    (varphiNtSch N k t : ℝ → ℂ) = varphiNt N k t :=
  funext (varphiNtSch_apply N k t)

/-! ## The member family of the randomised symbol as Schwartz maps -/

/-- The `m`-th member of the bump family `smallSymbF`, as a Schwartz function: it is the bump
`φ_{⌊a m⌋,t}` where the small-scale condition `randAct` holds, and `0` otherwise. -/
noncomputable def smallSymbFSch (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (m : ℕ) (t : ℝ) : SchwartzMap ℝ ℂ :=
  if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then varphiNtSch (Nat.floor (a m)) k₁ t else 0

/-- The Schwartz realisation of the family member agrees with `smallSymbF`. -/
lemma smallSymbFSch_coe (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ m : ℕ) (t : ℝ) :
    (smallSymbFSch ρ C₀ a l₁ l₂ k₁ k₂ m t : ℝ → ℂ) = smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t m := by
  unfold smallSymbFSch
  rw [smallSymbF_apply]
  by_cases h : randAct ρ C₀ a l₁ l₂ k₁ k₂ m
  · rw [if_pos h, if_pos h]
    exact varphiNtSch_coe (Nat.floor (a m)) k₁ t
  · rw [if_neg h, if_neg h]
    funext ξ
    simp

@[simp] lemma smallSymbFSch_apply (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ m : ℕ)
    (t : ℝ) (ξ : ℝ) :
    smallSymbFSch ρ C₀ a l₁ l₂ k₁ k₂ m t ξ = smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t m ξ :=
  congrFun (smallSymbFSch_coe ρ C₀ a l₁ l₂ k₁ k₂ m t) ξ

/-! ## The main statement -/

theorem randSymb_schwartz (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ)
    (ε : ℕ → ℂ) (K : ℕ) :
    ∃ Φ : SchwartzMap ℝ ℂ,
      (⇑Φ : ℝ → ℂ) = Work.KMTAreas.A7.randSymb
        (Work.KMTAreas.A7.smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K := by
  refine ⟨∑ n ∈ Finset.range K, ε n • (smallSymbFSch ρ C₀ a l₁ l₂ k₁ k₂ (n + 1) t
      - smallSymbFSch ρ C₀ a l₁ l₂ k₁ k₂ n t), ?_⟩
  funext ξ
  simp [randSymb, smallSymbFSch_apply]

end

end Work.KMTAreas.A7
