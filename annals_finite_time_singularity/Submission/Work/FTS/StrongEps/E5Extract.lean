/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/E5Extract.lean` — the extraction half of `E5`

`E5` (`exists_limH`, `EpsLimit.lean`) must, for every horizon `T > 0`, extract from the uniform
family of `ε`-solutions a single subsequence `φ` and a limit curve `τ ↦ F τ` carrying the
convergence package `ConvLocUnifH6 α B (slice (G (φ n)) τ) (F τ)` at **every** `τ ∈ [0,T]`.

The extraction itself is already proved, in three bricks:

* `EpsConvRat` — the diagonal extraction over the rational times: a strictly increasing `φ` and
  limits `F τ` at the *rational* `τ ∈ [0,T]`, carrying `ConvLocUnifH6` (hence `ConvLev0H6`) along
  the *fixed* subsequence `φ`.  It consumes the all-order smoothness of the slices, the `ℋ⁶`
  honesty and the uniform `ℋ⁶`-bound;
* `EpsConvAllTau` — the upgrade to *every* `τ ∈ [0,T]`: the profiles at `τ` are uniformly Cauchy
  on compacts (`hequi`, the level-`0` Lipschitz property of the families), a fresh
  `EpsConvSubseq` at each `τ` produces a candidate limit, and the sub-subsequence principle gives
  the slot convergence of the *full* `φ`-sequence;
* `EpsProfileLip_of_epsWP_corr` — `hequi` itself, from the uniform slot bounds of the *projected*
  right-hand side `epsRHSP` (which come from `EpsRHSP_slotSup_corr_fam`, i.e. from the sup bounds
  on `epsWP` plus the bound `hcorr` on the `L₁₂`-zero-mode of the mollified right-hand side).

This module assembles the three.  `E5Equi` isolates `hequi`'s four inputs (`hcont`, `hwin`,
`hcorr`, `hreg`) as explicit hypotheses, so that the final proof of `exists_limH` only has to
supply them once; `E5Extract` is the extraction proper.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsConvRat
import Submission.Work.FTS.StrongEps.EpsConvAllTau
import Submission.Work.FTS.StrongEps.EpsProfileLip_of_epsWP_corr

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

/-! ## `hequi` from the inputs of `EpsProfileLip_of_epsWP_corr` -/

/-- **The τ-Lipschitz property of the profiles** (the hypothesis `hequi` of `EpsConvAllTau`),
assembled from the four inputs of `EpsProfileLip_of_epsWP_corr`:

* `hcont` — the right-hand side `epsRHSP … s p` is continuous in the fake time at every point of
  the open quadrant;
* `hwin` — the *window* property of the mollifier: for every compact `K ⊆ Q0` there is a compact
  `K' ⊆ Q0` containing the whole mollification window of `K` whose slots of `epsWP` are uniformly
  bounded;
* `hcorr` — the uniform bound on `|L₁₂ (J_ε (epsWP s)) 0|`, the coefficient of the `P₀`-correction;
* `hreg` — all-order smoothness of `epsWP` on the open quadrant. -/
theorem E5Equi {α T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {ε : ℕ → ℝ} {G : ℕ → Fam}
    (hα : α ∈ Set.Ioc 0 1) (hρ : IsSmoothKernel ρ) (hε : ∀ k : ℕ, ε k ∈ Set.Ioc 0 1)
    (hsol : ∀ k : ℕ, IsEpsSolP α ρ (ε k) T Φs E g₀ (G k))
    (hcont : ∀ k : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => epsRHSP α ρ (ε k) Φs E (G k) s p.1 p.2) (Set.Icc 0 T))
    (hwin : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ K ⊆ K' ∧
        (∀ n : ℕ, ∀ p ∈ K, ∀ q : ℝ × ℝ, |q.1| ≤ ε n → |q.2| ≤ ε n →
          (zShift p.1 q.1, thShift p.2 q.2) ∈ K') ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.Icc 0 T,
          ∀ p ∈ K', |Work.Spaces.mixed j i (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2| ≤ C)
    (hcorr : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      |Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0| ≤ C)
    (hreg : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ (ε n) Φs E (G n) s)) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ τ ∈ Set.Icc (0 : ℝ) T,
        ∀ τ' ∈ Set.Icc (0 : ℝ) T,
          |slice (G n) τ p.1 p.2 - slice (G n) τ' p.1 p.2| ≤ C * |τ - τ'| := by
  intro K hK hKQ
  exact EpsProfileLip_of_epsWP_corr hα hρ hε hsol hcont hK hKQ (hwin K hK hKQ) hcorr hreg

/-! ## The extraction at every fake time -/

/-- **The extraction half of `E5`.**  From a sequence of `ε`-solutions of the projected scheme
with all-order smooth slices, honest `ℋ⁶`-membership and a uniform `ℋ⁶`-bound, a positive
sequence `ε → 0` bounded by `1`, and the four `hequi`-inputs of `E5Equi`, there is a strictly
increasing `φ` and a limit curve `F` such that at **every** `τ ∈ Icc 0 T` the profiles
`slice (G (φ n)) τ` converge to `F τ` locally uniformly on the open quadrant *together with every
slot of order `≤ 4`*, `F τ` is `C⁴` there and `Xn6 α (F τ) ≤ B`.

The limit curve is assembled from two pieces: at the rational fake times it is the curve of
`EpsConvRat`, and at the other times it is the per-`τ` limit produced by `EpsConvAllTau`; the two
agree on the open quadrant (uniqueness of limits), but no agreement is needed — the conclusion is
stated separately at each `τ`. -/
theorem E5Extract {α B T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
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
    (hwin : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ K' : Set (ℝ × ℝ), IsCompact K' ∧ K' ⊆ Work.FTS.EllipticEst.Q0 ∧ K ⊆ K' ∧
        (∀ n : ℕ, ∀ p ∈ K, ∀ q : ℝ × ℝ, |q.1| ≤ ε n → |q.2| ≤ ε n →
          (zShift p.1 q.1, thShift p.2 q.2) ∈ K') ∧
        ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ (j i : ℕ), j + i ≤ 4 → ∀ s ∈ Set.Icc 0 T,
          ∀ p ∈ K', |Work.Spaces.mixed j i (epsWP α ρ (ε n) Φs E (G n) s) p.1 p.2| ≤ C)
    (hcorr : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      |Work.Construction.L12 (Jeps ρ (ε n) (epsWP α ρ (ε n) Φs E (G n) s)) 0| ≤ C)
    (hreg : ∀ n : ℕ, ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (epsWP α ρ (ε n) Φs E (G n) s)) :
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
  -- the level-`0` Lipschitz property of the profiles
  have hequi := E5Equi hα hρ hε hsol hcont hwin hcorr hreg
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

/-! ## The sequence producer with `ε ≤ 1` -/

/-- **`EpsUniformMem` produces a sequence with `ε k ∈ Ioc 0 1`**, which is what the extraction
bricks (`EpsConvRat`, `EpsConvAllTau`, `EpsProfileLip_of_epsWP_corr`) require — the sequence of
`EpsUniformMem.exists_seq` has `ε k = ε₁/(k+1)`, which need not be `≤ 1`.  The proof is that of
`exists_seq` with `ε k := min ε₁ 1 / (k+1)`. -/
theorem EpsUniformMem.exists_seq_one {α C₀ K : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {g₀ : Fn} (hU : EpsUniformMem α ρ Φs E g₀ C₀ K) {T : ℝ} (hT : 0 < T) :
    (∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) ∧ Work.Construction.L12 g₀ 0 = 0 ∧
    ∃ K' : ℝ, K ≤ K' ∧ ∃ ε : ℕ → ℝ, (∀ k : ℕ, ε k ∈ Set.Ioc 0 1) ∧
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      ∃ Maj : ℝ → ℝ, MeasureTheory.IntegrableOn (fun z => Maj z / z) (Set.Ioi 0) ∧
      ∃ g : ℕ → Fam, ∀ k : ℕ, IsEpsSolP α ρ (ε k) T Φs E g₀ (g k) ∧
        ∀ τ ∈ Set.Icc (0 : ℝ) T,
          Work.FTS.EllipticEst.SmoothOpen (slice (g k) τ) ∧
            Work.Spaces.HkMem α 4 (slice (JfamP ρ (ε k) (g k)) τ) ∧
            Work.Spaces.HkMem α 6 (slice (g k) τ) ∧
            Work.FTS.Nonlin.Xn α (slice (JfamP ρ (ε k) (g k)) τ) ≤ C₀ * α ^ 2 ∧
            Work.FTS.StrongGlobal.Xn6 α (slice (g k) τ) ≤ K' ∧
            Work.FTS.ClassC.ClassC α (slice (JfamP ρ (ε k) (g k)) τ) ∧
            ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g k p.1 p.2.1 p.2.2)
              (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T) ∧
            EpsDecay α ρ Φs E (ε k) τ (g k) Maj := by
  obtain ⟨K', hKK', ε₁, hε₁pos, Maj, hMajint, hε₁⟩ := hU.2.2 T hT
  set e : ℝ := min ε₁ 1 with he
  have hepos : 0 < e := lt_min hε₁pos one_pos
  have hele : e ≤ ε₁ := min_le_left _ _
  have hpos : ∀ k : ℕ, 0 < e / (k + 1 : ℝ) := fun k => div_pos hepos (by positivity)
  have hle : ∀ k : ℕ, e / (k + 1 : ℝ) ≤ ε₁ := by
    intro k
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
    calc e = e * 1 := (mul_one e).symm
      _ ≤ e * ((k : ℝ) + 1) := by
          refine mul_le_mul_of_nonneg_left ?_ hepos.le
          exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      _ ≤ ε₁ * ((k : ℝ) + 1) := by
          refine mul_le_mul_of_nonneg_right hele (by positivity)
  have htend : Filter.Tendsto (fun k : ℕ => e / (k + 1 : ℝ)) Filter.atTop (nhds 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul e
    simpa [div_eq_mul_inv] using h
  have hex : ∀ k : ℕ, ∃ g : Fam,
      IsEpsSolP α ρ (e / (k + 1 : ℝ)) T Φs E g₀ g ∧
        ∀ τ ∈ Set.Icc (0 : ℝ) T,
          Work.FTS.EllipticEst.SmoothOpen (slice g τ) ∧
            Work.Spaces.HkMem α 4 (slice (JfamP ρ (e / (k + 1 : ℝ)) g) τ) ∧
            Work.Spaces.HkMem α 6 (slice g τ) ∧
            Work.FTS.Nonlin.Xn α (slice (JfamP ρ (e / (k + 1 : ℝ)) g) τ) ≤ C₀ * α ^ 2 ∧
            Work.FTS.StrongGlobal.Xn6 α (slice g τ) ≤ K' ∧
            Work.FTS.ClassC.ClassC α (slice (JfamP ρ (e / (k + 1 : ℝ)) g) τ) ∧
            ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
              (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Icc 0 T) ∧
            EpsDecay α ρ Φs E (e / (k + 1 : ℝ)) τ g Maj :=
    fun k => hε₁ _ ⟨hpos k, hle k⟩
  choose g hg using hex
  refine ⟨hU.1, hU.2.1, K', hKK', fun k => e / (k + 1 : ℝ), fun k => ⟨hpos k, ?_⟩, htend,
    Maj, hMajint, g, hg⟩
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
  calc e = e * 1 := (mul_one e).symm
    _ ≤ e * ((k : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_left ?_ hepos.le
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    _ ≤ 1 * ((k : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)

end Work.FTS.StrongEps
