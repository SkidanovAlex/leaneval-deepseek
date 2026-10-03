import Mathlib
import Submission.Work.KMTAreas.A7.Tle_varphitildeNt_bounded
import Submission.Work.KMTAreas.A7.randSymbGCoefDefs
import Submission.Work.KMTAreas.A7.adm_of_bump

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## Instances of `Adm` for the two bump families

Both families are built from the modulated bumps `varphiNt N k₁ t` and `varphitildeNt P d N k₂ t`,
which are `C²` with compact support; `adm_of_bump` then gives the three properties of `Adm`. -/

/-- The `f`-side modulated bump is admissible at the exact-height frequency set. -/
theorem Adm_varphiNt' (ρ : ℝ) (l N k₁ : ℕ) (t : ℝ) :
    Adm (diffFreqs ρ l) (varphiNt N k₁ t) :=
  adm_of_bump (contDiff_varphiNt N k₁ t) (hasCompactSupport_varphiNt N k₁ t)

/-- The modulated `g`-side bump `φ̃_{N,t}` is `C²` with compact support. -/
private lemma contDiff_varphitildeNt' (P : Polynomial ℤ) (d N k₂ : ℕ) (t : ℝ) :
    ContDiff ℝ 2 (varphitildeNt P d N k₂ t) := by
  rw [show varphitildeNt P d N k₂ t
      = fun ξ : ℝ => varphitildeN d N k₂ ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (contDiff_varphitildeN d N k₂).mul (contDiff_ee_const_mul 2 _)

private lemma hasCompactSupport_varphitildeNt' (P : Polynomial ℤ) (d N k₂ : ℕ) (t : ℝ) :
    HasCompactSupport (varphitildeNt P d N k₂ t) := by
  rw [show varphitildeNt P d N k₂ t
      = fun ξ : ℝ => varphitildeN d N k₂ ξ * ee (PevalR P ((N : ℝ) * t) * ξ) from rfl]
  exact (hasCompactSupport_varphitildeN d N k₂).mul_right

/-- The modulated `g`-side bump is admissible at the exact-height frequency set. -/
theorem Adm_varphitildeNt' (ρ : ℝ) (P : Polynomial ℤ) (l d N k₂ : ℕ) (t : ℝ) :
    Adm (diffFreqs ρ l) (varphitildeNt P d N k₂ t) :=
  adm_of_bump (contDiff_varphitildeNt' P d N k₂ t) (hasCompactSupport_varphitildeNt' P d N k₂ t)

/-- Every member of the `f`-side bump family `smallSymbF` is admissible (it is either `0` or a
modulated bump, and `Adm` is closed under scalar multiples). -/
theorem Adm_smallSymbF (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (l : ℕ) (m : ℕ) :
    Adm (diffFreqs ρ l) (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t m) := by
  have h2 := (Adm_varphiNt' ρ l (Nat.floor (a m)) k₁ t).const_mul
    (if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then (1 : ℂ) else 0)
  have hfun : (fun ξ => (if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then (1 : ℂ) else 0)
      * varphiNt (Nat.floor (a m)) k₁ t ξ) = smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t m := by
    funext ξ
    rw [smallSymbF_apply]
    by_cases hc : randAct ρ C₀ a l₁ l₂ k₁ k₂ m <;> simp [hc]
  rwa [hfun] at h2

/-- Every member of the `g`-side bump family `smallSymbG` is admissible. -/
theorem Adm_smallSymbG (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ)
    (t : ℝ) (l : ℕ) (m : ℕ) :
    Adm (diffFreqs ρ l) (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t m) := by
  have h2 := (Adm_varphitildeNt' ρ P l P.natDegree (Nat.floor (a m)) k₂ t).const_mul
    (if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then (1 : ℂ) else 0)
  have hfun : (fun ξ => (if randAct ρ C₀ a l₁ l₂ k₁ k₂ m then (1 : ℂ) else 0)
      * varphitildeNt P P.natDegree (Nat.floor (a m)) k₂ t ξ)
      = smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t m := by
    funext ξ
    rw [smallSymbG_apply]
    by_cases hc : randAct ρ C₀ a l₁ l₂ k₁ k₂ m <;> simp [hc]
  rwa [hfun] at h2

/-! ## The randomised telescoping identity

The linearity of `Tm` in the symbol (`Tm_add_of_bounded`, in `Adm` form) turns the *telescoping*
finite sum `∑_{k<K} ε k (Tm φ (k+1) - Tm φ k)` into a single `Tm` of the randomised symbol
`randSymb φ ε K`, for a family `φ` whose members are admissible.  The proof is an induction on `K`,
carrying the admissibility of the partial symbol `randSymb φ ε K` along. -/

theorem Tm_randSymb_eq_rangeSum (ρ : ℝ) (l : ℕ) (φ : ℕ → ℝ → ℂ) (ε : ℕ → ℂ) (f : ℤ → ℂ) {B : ℝ}
    (hB : ∀ m : ℤ, ‖f m‖ ≤ B) (hφ : ∀ m : ℕ, Adm (diffFreqs ρ l) (φ m)) :
    ∀ K : ℕ, Adm (diffFreqs ρ l) (randSymb φ ε K) ∧
      Tm ρ l (randSymb φ ε K) f
        = fun y : ℤ => ∑ k ∈ Finset.range K, ε k *
            (Tm ρ l (φ (k+1)) f y - Tm ρ l (φ k) f y) := by
  intro K
  induction K with
  | zero =>
      have hz : Adm (diffFreqs ρ l) (0 : ℝ → ℂ) := by
        have h := (hφ 0).const_mul (0 : ℂ)
        have hfun : (fun ξ => (0 : ℂ) * φ 0 ξ) = (0 : ℝ → ℂ) := by funext ξ; simp
        rwa [hfun] at h
      refine ⟨?_, ?_⟩
      · rw [randSymb_zero]; exact hz
      · rw [randSymb_zero, Tm_zero']
        funext y
        simp
  | succ K ih =>
      have hpiece : Adm (diffFreqs ρ l) (fun ξ => ε K * ((φ (K+1) - φ K) ξ)) :=
        ((hφ (K+1)).sub (hφ K)).const_mul (ε K)
      have hsucc : randSymb φ ε (K + 1)
          = randSymb φ ε K + (fun ξ => ε K * ((φ (K+1) - φ K) ξ)) := by
        funext ξ
        simp only [randSymb, Pi.add_apply, Pi.sub_apply, Finset.sum_range_succ]
      refine ⟨?_, ?_⟩
      · rw [hsucc]
        exact ih.1.add hpiece
      · rw [hsucc, Tm_add_of_adm hB ih.1 hpiece]
        rw [ih.2, Tm_const_mul, Tm_sub_of_adm hB (hφ (K+1)) (hφ K)]
        funext y
        simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_range_succ]

theorem Tm_randSymb_smallSymb (P : Polynomial ℤ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ K : ℕ) (t : ℝ) (ε : ℕ → ℂ) (f g : ℤ → ℂ) {Cf Cg : ℝ}
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) (l : ℕ) :
    (fun y : ℤ => ∑ k ∈ Finset.range K, ε k *
        (Work.KMTAreas.A7.Tm ρ l (Work.KMTAreas.A7.smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t (k+1)) f y
          - Work.KMTAreas.A7.Tm ρ l (Work.KMTAreas.A7.smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k) f y))
      = Work.KMTAreas.A7.Tm ρ l (Work.KMTAreas.A7.randSymb
          (Work.KMTAreas.A7.smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε K) f ∧
    (fun y : ℤ => ∑ k ∈ Finset.range K, ε k *
        (Work.KMTAreas.A7.Tm ρ l (Work.KMTAreas.A7.smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t (k+1)) g y
          - Work.KMTAreas.A7.Tm ρ l (Work.KMTAreas.A7.smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k) g y))
      = Work.KMTAreas.A7.Tm ρ l (Work.KMTAreas.A7.randSymb
          (Work.KMTAreas.A7.smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε K) g := by
  constructor
  · exact (Tm_randSymb_eq_rangeSum ρ l (smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t) ε f hf
      (fun m => Adm_smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t l m) K).2.symm
  · exact (Tm_randSymb_eq_rangeSum ρ l (smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t) ε g hg
      (fun m => Adm_smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t l m) K).2.symm

end

end Work.KMTAreas.A7
