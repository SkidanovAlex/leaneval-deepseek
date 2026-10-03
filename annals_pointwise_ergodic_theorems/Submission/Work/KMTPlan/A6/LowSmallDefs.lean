/-
# The small-scale model operators of the low case of area A6

This module fixes the vocabulary of the small-scale (paper §7) analysis of the
**low case** `k₁ = 0 ∨ k₂ = 0` of area A6, i.e. of the estimate `Work.KMTPlan.A6.LcSmall`.

The columns of the contract are `varpCol (kmtPj ρ) P d C₀ a f g l₁ l₂ k₁ k₂`, i.e. the halved
average `Ã_N(F^{0,l₁,k₁}_N f, G^{0,l₂,k₂}_N g)` clamped to the index set; the small-scale family
`colSmall` further clamps the scales by `N ≤ splitCut ρ L`, `L = max (max l₁ l₂) (max k₁ k₂)`.

The paper's §6 replaces the concrete column by the *twisted bilinear multiplier*
`B^{l₁,l₂,m_Ẑ}_{m_*}` applied to the modulated Littlewood--Paley pieces
`T^{l₁}_{φ_{N,t}}F`, `T^{l₂}_{φ̃_{N,t}}G` (`F = Π_{l₁,≤0}f`, `G = Π_{l₂,≤0}g`), integrated in
`t ∈ [1/2,1]`; this is the *model tuple* `lowModel` below.

**The window `m_*`.**  The symbol of §6 is the *narrow* window
`m_* = η_{≤-2u} ⊗ η_{≤-2du}`, `u = uScale ρ L = ⌊2^{2ρL}⌋`, `L = lcL l₁ l₂ k₁ k₂`
(`mStarF u`, `mStargF d u`), exactly as in `Work.KMTAreas.A7.modelTuple`.  Two conditions make
this the correct choice:

* *the window contains the bumps*: `φ_{N,t}` is supported at frequency scale `2^{k}/N`, and
  `2^{k} ≤ 2^{-2u}N`, i.e. `k + 2u ≤ Log N`, is `mainRegime ρ k₁ k₂ N`; hence `m_* ≡ 1` on the
  support of the bumps and `bn-ident` identifies `lowModel` with the paper's §6 model
  `B^{l₁,l₂,m_Ẑ}_{(φ_N⊗φ̃_N)m̃_{N,ℝ}}`;
* *the window is finer than the spacing of the arithmetic frequencies*:
  `L ≤ 2u`, i.e. the window `η_{≤-2u}` is supported at scale `2^{-2u} ≪ 2^{-l}`
  (`l = max(l₁,l₂)`), which is what makes the arithmetic-frequency smearing
  `Σ_α m_Ẑ(α) Φ(α-ν)` collapse to the single term `m_Ẑ(ν)`.  **This is why `mStarF 0`
  (the wide window `η`) is wrong**: with `Φ = periodize η` one has `Φ(α-ν) ≍ 1` even for the
  off-diagonal pairs, so the model's arithmetic symbol differs from the concrete one's by an
  `O(1)` amount; see `NOTES_lowSmallModelApprox.md`, Finding 2.

Both conditions are automatic on `lowSmallSet` once `lcL` is large enough, the first because
`inIndexSet` gives `L ≤ heightScale C₀ N = C₀·LogLog N`, hence `Log N ≥ 2^{L/C₀} ≫ 2^{2ρL} ≥ u`
(taking `2ρC₀ ≤ 1/8`); this is `lowSmallWindowConds`.  For the finitely many small quadruples the
crude bound `lowSmallBoundedL` is used instead, so nothing is lost.

Because the contract's pieces are the *exact arithmetic height* pieces (`piExact`), the arithmetic
symbol of the model must be the one with the exact-height frequency sets `(ℚ/ℤ)_l`
(`Work.KMTAreas.A7.diffFreqs`), not the height-`≤ l` sets; this is the only difference between
`arithKernelEx`/`BtwistEx` here and `Work.KMTAreas.A7.arithKernel`/`Btwist`.

Everything in this module is definitional.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowDefs
import Submission.Work.KMTAreas.A7.ModelOps
import Submission.Work.KMTAreas.A7.ModelApproxAux

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.KMTContract
open Work.Analysis.EndVar
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

/-- **The admissible small scales of the low case**: the index set `I^{max(l₁,l₂),k₁,k₂}` cut at
the small-scale threshold `splitCut ρ L`, `L = lcL l₁ l₂ k₁ k₂`. -/
def lowSmallSet (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) : Prop :=
  inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) ∧
    Nat.floor (a n) ≤ Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂)

instance (ρ : ℝ) (C₀ : ℕ) (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ n : ℕ) :
    Decidable (lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n) := by
  unfold lowSmallSet; infer_instance

theorem lowSmallSet_iff {ρ : ℝ} {C₀ : ℕ} {a : ℕ → ℝ≥0} {l₁ l₂ k₁ k₂ n : ℕ} :
    lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n ↔
      inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) ∧
        Nat.floor (a n) ≤ Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂) := Iff.rfl

/-- **The arithmetic symbol of the twisted bilinear multiplier at exact arithmetic heights.**

`∑_{α₁ ∈ (ℚ/ℤ)_{l₁}} ∑_{α₂ ∈ (ℚ/ℤ)_{l₂}} m_Ẑ(α₁,α₂) e(-j₁α₁) e(-j₂α₂)` is the double Fourier
coefficient of the arithmetic symbol `m_{l₁,l₂,Ẑ} = (1_{(ℚ/ℤ)_{l₁}} ⊗ 1_{(ℚ/ℤ)_{l₂}}) m_Ẑ`
of §6, evaluated at the integers `(j₁,j₂)`. -/
noncomputable def arithKernelEx (ρ : ℝ) (P : ℤ[X]) (q : ℕ) (l₁ l₂ : ℕ)
    (j₁ j₂ : ℤ) : ℂ :=
  ∑ α₁ ∈ Work.KMTAreas.A7.diffFreqs ρ l₁, ∑ α₂ ∈ Work.KMTAreas.A7.diffFreqs ρ l₂,
    Work.KMTAreas.A7.mZ P q α₁ α₂
      * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂

/-- **The twisted bilinear multiplier `B^{l₁,l₂,m_Ẑ}_{m₁⊗m₂}`** of §6 at exact arithmetic
heights, in kernel form: the bilinear convolution operator with kernel
`(j₁,j₂) ↦ arithKernelEx … j₁ j₂ · (𝓕⁻m₁)(j₁) · (𝓕⁻m₂)(j₂)`. -/
noncomputable def BtwistEx (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) : ℤ → ℂ :=
  fun x => ∑' j₁ : ℤ, ∑' j₂ : ℤ,
    arithKernelEx ρ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂
      * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂ * h (x - j₁) * k (x - j₂)

/-- **The model tuple of the small-scale low case** (paper §6--§7).

On the small-scale index set it is
`n ↦ ∫_{1/2}^1 B^{l₁,l₂,m_Ẑ}_{m_*}(T^{l₁}_{φ_{N,t}}f, T^{l₂}_{φ̃_{N,t}}g) dt`,
`N = ⌊a n⌋`, with the modulated bumps `φ_{N,t}`, `φ̃_{N,t}` of §6 and `m_* = η_{≤0} ⊗ η_{≤0}` (the
bottom scale `u = 0` of the contract), and it vanishes off the small-scale index set.

The multipliers `T^{l}_{φ}` are the *exact arithmetic height* IW multipliers
(`Work.KMTAreas.A7.Tm`, built from `diffFreqs`), matching the exact-height pieces `Fpiece`,
`Gpiece` of the concrete columns.  The bumps are applied to `f`, `g` themselves, not to a
projection: the paper's `F = Π_{l₁,≤-u}f` is *not* a bounded projection at the contract's bottom
scale `u = 0` (its symbol is `∑_{β ∈ (ℚ/ℤ)_{≤l}} η`, which is `≥ 1` pointwise, so its norm is at
least `2^l`), while the functional calculus `T^{l}_{φ}(Π_{l,≤-u}f) = T^{l}_{φ·η_{≤-u}}f` together
with the support condition `φ·η_{≤-u} = φ` shows that the two descriptions agree.  Since `Tm` is
linear in its symbol and `piExact (kmtPj ρ) l κ = Tm ρ l (etaCut kmtEta κ)` (for finitely
supported, hence all `ℓ²`, inputs), the definition above is the `f`-base form of the model
operator of §6 (Proposition `mod-approx` composed with the functional calculus `bn-ident`). -/
noncomputable def lowModel (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n then
      ∫ t in (1/2 : ℝ)..1,
        BtwistEx ρ P l₁ l₂
          (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
          (Work.KMTAreas.A7.mStargF P.natDegree
            (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
          (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t)
            f)
          (Work.KMTAreas.A7.Tm ρ l₂
            (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)
            g) x
    else 0

theorem lowModel_apply (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ) :
    lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x =
      (if lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n then
        ∫ t in (1/2 : ℝ)..1,
          BtwistEx ρ P l₁ l₂
            (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
            (Work.KMTAreas.A7.mStargF P.natDegree
              (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
            (Work.KMTAreas.A7.Tm ρ l₁ (Work.KMTAreas.A7.varphiNt (Nat.floor (a n)) k₁ t)
              f)
            (Work.KMTAreas.A7.Tm ρ l₂
              (Work.KMTAreas.A7.varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)
              g) x
      else 0) := rfl

/-- Off the admissible set the model tuple vanishes. -/
theorem lowModel_eq_zero_of_not (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ)
    (h : ¬ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n) :
    lowModel ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
  rw [lowModel_apply, if_neg h]

/-- **The clamped concrete column of the small-scale regime is `varpCol` on the admissible
set**: `colSmall` is `varpCol` cut at `splitCut`, and `varpCol` itself is cut at the index
set, so on `lowSmallSet` the two agree. -/
theorem colSmall_eq_varpCol_on (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ)
    (h : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n) :
    colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      = varpCol (kmtPj ρ) P P.natDegree C₀ a f g l₁ l₂ k₁ k₂ n x := by
  rw [colSmall_apply, if_pos h.2, varpCol_apply, if_pos h.1]

/-- Off the admissible set the clamped concrete column vanishes. -/
theorem colSmall_eq_zero_of_not (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ)
    (h : ¬ lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n) :
    colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x = 0 := by
  by_cases hclamp : Nat.floor (a n) ≤ Work.KMTAreas.A7.splitCut ρ (lcL l₁ l₂ k₁ k₂)
  · rw [colSmall_apply, if_pos hclamp, varpCol_apply,
      if_neg (fun hidx => h ⟨hidx, hclamp⟩)]
  · rw [colSmall_apply, if_neg hclamp]

end

end Work.KMTPlan.A6
