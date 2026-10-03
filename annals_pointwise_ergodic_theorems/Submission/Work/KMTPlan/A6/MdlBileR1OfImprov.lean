/-
# Theorem `bile` at `r = 1` in the finite cyclic model (paper: Proposition `bile-2`)

Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals 195 (2022), Proposition `bile-2` (`Theorem bile holds when r = 1`), in the
finite cyclic model `ℤ/Qℤ` in which the model operator estimates of §8 are stated:

  if `f` or `g` on `ℤ/Qℤ` satisfies the Ionescu--Wainger minor-arc condition `MdlIwMinorArc ρ l Q`
  (its discrete Fourier transform vanishes on the frequencies of arithmetic height `≤ l`), then

    `‖A_{ℤ/Qℤ}(f,g)‖_{L¹(ℤ/Qℤ)} ≲_{C₃} 2^{-c·l} ‖f‖_{L²} ‖g‖_{L²}`,

with a constant that is *uniform in* `Q` and `l`.  This uniformity is the whole content of the
theorem: `ℤ/Qℤ` is a probability space, so without the gain the estimate would follow from
Cauchy--Schwarz with a constant depending on nothing at all — but a *gain* `2^{-c·l}` with `c`
independent of `Q` and `l` is a genuine arithmetic statement.

## The proof (the paper's limiting argument)

The paper derives the finite statement from the `ℤ`-statement, which is a degenerate case of
`improv`: lift `f, g` to `ℤ` by

  `f_R(n) = R^{-1/2} ψ(n/R) f(n mod Q)`     (`ψ ∈ 𝒮(ℝ)` even, `‖ψ‖_{L²} = 1`, `𝓕ψ ⊆ [-1,1]`),

for a large `N` and an extremely large `R ≫ N`.  Then

1. the lift has no Fourier support on the arcs `ℳ_{≤l,≤-Log N+l}` — because `𝓕ψ ⊆ [-1,1]` and the
   minor-arc condition separates the frequencies (`BileLiftKmtProjZero`) — so `improv` applies:
   `‖A_{N,ℤ}(f_R,g_R)‖_{L¹(ℤ)} ≲ (2^{-cl} + ⟨Log N⟩^{-c/ρ}) ‖f_R‖₂ ‖g_R‖₂`;
2. the `ℓ²`-norms of the lifts converge to the `L²(ℤ/Qℤ)`-norms of `f, g` (Riemann sums against
   the smooth window; `BileWindowLimits`);
3. `A_{N,ℤ}(f_R,g_R)(n) = R^{-1}|ψ(n/R)|² A_{ℤ/Qℤ}(f,g)(n mod Q) + O(R^{-2}⟨n/R⟩^{-10})`, so
   `‖A_{N,ℤ}(f_R,g_R)‖_{L¹(ℤ)} → ½‖A_{ℤ/Qℤ}(f,g)‖_{L¹(ℤ/Qℤ)}` as `R → ∞` at fixed `N`
   (`BileLiftAhalfLimit`), and `½‖A_{ℤ/Qℤ}(f,g)‖` is the `N → ∞` limit of `‖bileHalvedAvg‖`
   (`BileHalvedAvgLimit`; the factor `½` is the length of the halved window `(N/2,N]` normalised
   by `N`);
4. the `ε`-bookkeeping is assembled in `BileAssembly` (Items 1, 2, 3 and the fixed-scale step
   `bileHalvedAvg_le_of_improv`), and the final `η → 0` limit is `bile_eta_absorption`.

The rate `c` is that of `ImprovKMT` (independent of `ρ`), and the constant is `2 C_ρ`.

## What this is used for

`MdlBileR1OfImprov` is the arithmetic-gain input of the `(2,2,1)` case of the model estimate
`model-est-2` (`Work.KMTPlan.A6.MdlSliceCoreGain`): the model's inputs carry the *exact* arithmetic
height `l` (the `mdlF` shells), hence are minor arc at that height, and the gain `2^{-c·l}` is what
makes the variational sum over the scales converge.  The interpolation of this `r = 1` estimate
with the trivial `L²×L² → L^q` bound gives Theorem `bile` for all `r ≥ 1` (the `L^q` endpoint needs
no arithmetic input at all, since `ℤ/Qℤ` is a probability space), which is the form needed for the
`V^r`-norms of `MdlSliceCoreGain` when `r > 2`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.BileAssembly
import Submission.Work.KMTPlan.A6.BileWindowLimits
import Submission.Work.KMTPlan.A6.BileHalvedAvgLimit
import Submission.Work.KMTPlan.A6.BileLiftAhalfLimit
import Submission.Work.KMTPlan.A6.BileLargeN

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.Concentration

/-- **Theorem `bile` at `r = 1` (paper: Proposition `bile-2`).**  In the finite cyclic model, the
arithmetic bilinear average of a minor-arc function against an arbitrary one gains `2^{-c·l}`, with
a constant uniform in the modulus `Q` and the height `l`. -/
theorem MdlBileR1OfImprov (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hI : Work.KMTContract.ImprovKMT P) :
    ∃ c : ℝ, 0 < c ∧ ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ C : ℝ, 0 < C ∧
        ∀ (Q : ℕ) [NeZero Q] (l : ℕ) (f g : ZMod Q → ℂ),
        (Work.KMTPlan.A6.MdlIwMinorArc ρ l Q f ∨ Work.KMTPlan.A6.MdlIwMinorArc ρ l Q g) →
        Work.Analysis.Concentration.LpNormZMod Q 1
            (Work.Analysis.Concentration.polyBilinearAverageZMod Polynomial.X P Q f g)
          ≤ C * (2 : ℝ) ^ (-(c * (l : ℝ))) *
              Work.Analysis.Concentration.LpNormZMod Q 2 f *
              Work.Analysis.Concentration.LpNormZMod Q 2 g := by
  obtain ⟨c, hc, hIall⟩ := hI
  refine ⟨c, hc, fun ρ hρ hρ1 => ?_⟩
  obtain ⟨C₀, hIρ⟩ := hIall ρ hρ hρ1
  obtain ⟨ψ, hψsupp, hψL2, hwin2, hwin1⟩ := BileWindowLimits
  refine ⟨max 1 (2 * (C₀ : ℝ)), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro Q hNZ l f g hm
  have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne Q)
  set A : ZMod Q → ℂ := polyBilinearAverageZMod Polynomial.X P Q f g with hA
  set G : ℝ := (2 : ℝ) ^ (-(c * (l : ℝ))) with hGdef
  have hGnn : (0 : ℝ) ≤ G := by rw [hGdef]; positivity
  -- **Step 1**: the `η`-form of the estimate, at a scale `N` which is large enough both for
  -- `BileLargeN` and for the `N → ∞` limit of the halved average.  The budget `η` of the two
  -- limits is `η/2`, leaving `η/2` for the `+η` of `bileHalvedAvg_le_of_improv` and one `η`
  -- for the two-sided comparison at `(N, R)`.
  have key : ∀ η : ℝ, 0 < η →
      (1 / 2) * LpNormZMod Q 1 A ≤
        (C₀ : ℝ) * (G + η) * ((1 + η) * LpNormZMod Q 2 f) *
          ((1 + η) * LpNormZMod Q 2 g) + η := by
    intro η hη
    have hη2 : 0 < η / 2 := by linarith
    obtain ⟨N₀, hN₀⟩ := BileLargeN P (by omega) ρ hρ l c hc (Q := Q) (η / 2) hη2
    obtain ⟨N₁, hN₁⟩ := bileHalvedAvg_ge_of_tendsto (BileHalvedAvgLimit P f g) (η / 2) hη2
    set N : ℕ := max N₀ N₁ with hNdef
    have hN0 : N₀ ≤ N := le_max_left _ _
    have hN1 : N₁ ≤ N := le_max_right _ _
    obtain ⟨hQN, hkf, hkg, hδ⟩ := hN₀ N hN0
    have hN1le : 1 ≤ N := le_trans hQ1 hQN
    obtain ⟨R₀, hR₀⟩ := bileHalvedAvg_le_of_improv ψ hρ hρ1 hQ1 hc hIρ hψsupp (hwin2 hQ1)
      (fun N' u v hN' => BileLiftAhalfLimit P ψ hψL2 hQ1 hN' u v) hN1le hQN hη2 hkf hkg hδ hm
    have hge := hN₁ N hN1
    have hfun : (fun z : ZMod Q => (1 / 2 : ℂ) * A z)
        = fun z : ZMod Q => (((1 / 2 : ℝ)) : ℂ) * A z := by
      funext z
      norm_num
    have hhom : LpNormZMod Q 1 (fun z : ZMod Q => (1 / 2 : ℂ) * A z)
        = (1 / 2) * LpNormZMod Q 1 A := by
      rw [hfun, LpNormZMod_const_mul Q (s := 1) (c := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num) A]
    rw [hhom] at hge
    have hR := hR₀ R₀ le_rfl
    rw [← hGdef] at hR
    -- `η/2` may be replaced by `η` in the right-hand side
    have hmono : (C₀ : ℝ) * (G + η / 2) * ((1 + η / 2) * LpNormZMod Q 2 f) *
        ((1 + η / 2) * LpNormZMod Q 2 g)
        ≤ (C₀ : ℝ) * (G + η) * ((1 + η) * LpNormZMod Q 2 f) *
          ((1 + η) * LpNormZMod Q 2 g) := by
      have hf : (0 : ℝ) ≤ LpNormZMod Q 2 f := LpNormZMod_nonneg Q 2 f
      have hg : (0 : ℝ) ≤ LpNormZMod Q 2 g := LpNormZMod_nonneg Q 2 g
      have h1 : G + η / 2 ≤ G + η := by linarith
      have h2 : (1 + η / 2) ≤ (1 + η) := by linarith
      have h3 : (0 : ℝ) ≤ 1 + η / 2 := by linarith
      have h4 : (0 : ℝ) ≤ 1 + η := by linarith
      have h5 : (0 : ℝ) ≤ G + η := by linarith
      calc (C₀ : ℝ) * (G + η / 2) * ((1 + η / 2) * LpNormZMod Q 2 f) *
              ((1 + η / 2) * LpNormZMod Q 2 g)
          = (C₀ : ℝ) * ((G + η / 2) * (1 + η / 2) * (1 + η / 2)) *
              (LpNormZMod Q 2 f * LpNormZMod Q 2 g) := by ring
        _ ≤ (C₀ : ℝ) * ((G + η) * (1 + η) * (1 + η)) *
              (LpNormZMod Q 2 f * LpNormZMod Q 2 g) := by
            apply mul_le_mul_of_nonneg_right _ (mul_nonneg hf hg)
            apply mul_le_mul_of_nonneg_left _ (NNReal.coe_nonneg C₀)
            exact mul_le_mul (mul_le_mul h1 h2 h3 h5) h2 h3 (mul_nonneg h5 h4)
        _ = (C₀ : ℝ) * (G + η) * ((1 + η) * LpNormZMod Q 2 f) *
              ((1 + η) * LpNormZMod Q 2 g) := by ring
    linarith
  -- **Step 2**: absorb the `η`'s (`bile_eta_absorption`).
  have key2 : ∀ ε : ℝ, 0 < ε →
      (1 / 2) * LpNormZMod Q 1 A ≤
        (C₀ : ℝ) * G * LpNormZMod Q 2 f * LpNormZMod Q 2 g + ε := by
    intro ε hε
    obtain ⟨η, hη, habs⟩ := bile_eta_absorption (C := (C₀ : ℝ)) (G := G)
      (A := LpNormZMod Q 2 f) (B := LpNormZMod Q 2 g) (ε := ε)
      (NNReal.coe_nonneg C₀) hGnn (LpNormZMod_nonneg Q 2 f) (LpNormZMod_nonneg Q 2 g) hε
    exact (key η hη).trans habs
  have key3 : (1 / 2) * LpNormZMod Q 1 A ≤
      (C₀ : ℝ) * G * LpNormZMod Q 2 f * LpNormZMod Q 2 g := by
    by_contra hcon
    have hlt := not_le.mp hcon
    have hε : 0 < ((1 / 2) * LpNormZMod Q 1 A
        - (C₀ : ℝ) * G * LpNormZMod Q 2 f * LpNormZMod Q 2 g) / 2 := by linarith
    have h := key2 _ hε
    linarith
  -- **Step 3**: remove the factor `1/2` and replace `C₀` by `max 1 (2 C₀)`.
  have hfinal : LpNormZMod Q 1 A ≤
      max 1 (2 * (C₀ : ℝ)) * G * LpNormZMod Q 2 f * LpNormZMod Q 2 g := by
    have h2 : LpNormZMod Q 1 A ≤
        2 * ((C₀ : ℝ) * G * LpNormZMod Q 2 f * LpNormZMod Q 2 g) := by linarith
    calc LpNormZMod Q 1 A
        ≤ 2 * ((C₀ : ℝ) * G * LpNormZMod Q 2 f * LpNormZMod Q 2 g) := h2
      _ = (2 * (C₀ : ℝ)) * G * LpNormZMod Q 2 f * LpNormZMod Q 2 g := by ring
      _ ≤ max 1 (2 * (C₀ : ℝ)) * G * LpNormZMod Q 2 f * LpNormZMod Q 2 g :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hGnn)
            (LpNormZMod_nonneg Q 2 f)) (LpNormZMod_nonneg Q 2 g)
  rw [hA, hGdef] at hfinal
  exact hfinal

end

end Work.KMTPlan.A6
