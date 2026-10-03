/-
# The shared definitions of the KMT contract (`ROUTE_LEAD.md` §3.0, step A0)

This module fixes the vocabulary in which the eight *areas* of
`Submission/Work/KMTContract/Areas.lean` and their composition
(`Submission/Work/KMTContract/Composition.lean`) are stated: the concrete Ionescu--Wainger
projections of the paper, the "paraproduct columns" of §5, and the truncation `truncZ` used to
pass from finitely supported to `ℓ^p` inputs.

## Main definitions

* `kmtBump`, `kmtEta` — the paper's cutoff `η`: a smooth even function with `0 ≤ η ≤ 1`, equal to
  `1` on `[-1/2, 1/2]` and supported in `[-1, 1]` (realised by Mathlib's `ContDiffBump 0` with
  `rIn = 1/2`, `rOut = 1`);
* `kmtProj ρ l k f` — the Ionescu--Wainger projection `Π_{≤l,≤k} f` of §5 on an *arbitrary*
  function `f : ℤ → ℂ`, realised as the convolution with the Fourier coefficients of the IW symbol
  `iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))` (this is
  `Work.Analysis.IWMultiplier.iwConv`; for `f ∈ ℓ²` it agrees with the `L²` multiplier `iwProj`,
  see `Work.Analysis.IWMultiplier.iwConv_eq_iwOpSet`);
* `kmtPj ρ` — the same family bundled as the projection interface
  `Work.Analysis.Paraproduct.IWProjections` consumed by the `EndVar` chapter;
* `VarpStatementΛWith`, `PieceBound` — Theorem `varp` with a lacunarity-dependent constant,
  stated for exactly the columns `varpCol` (bottom scale `u = 0`, `s₁, s₂ ∈ ℕ`) that the §5
  assembly consumes, with a *general* weight `w l₁ l₂ s₁ s₂`; `PieceBound ρ P C₀ p₁ p₂ p r w` is
  the same statement for the concrete projections `kmtPj ρ` and `d = P.natDegree`;
* `truncZ K f` — the truncation `x ↦ if |x| ≤ K then f x else 0` used to test the areas on
  finitely supported functions.

## Conventions

* `ρ ∈ (0,1]` is the Ionescu--Wainger parameter of `(ℚ/ℤ)_{≤l}` (the paper's `ρ = 1/C₁`);
* `C₀` is the constant of the height scale `l_{(N)} = C₀ · LogLog N`
  (`Work.Analysis.EndVar.heightScale`);
* `PieceBound` and the areas are stated for arbitrary `f g : ℤ → ℂ`; the right-hand side is `⊤`
  when the norms are infinite, and the left-hand side is `0` when the data vanish (this is the
  convention under which the `EndVar` assembly consumes them, cf. `varEstZ_of_varEstHalf`).
-/
import Submission.Work.Analysis.EndVar.VarpTools
import Submission.Work.Analysis.InverseTheory.MajorArcs
import Submission.Work.Analysis.IWMultiplier.Gap

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTContract

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems

open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier
open Work.Analysis.EndVar
open Work.Analysis.Paraproduct (IWProjections)

/-! ## The cutoff `η` -/

/-- The paper's cutoff `η`: a smooth even function with values in `[0,1]`, equal to `1` on
`[-1/2, 1/2]` and supported in `[-1, 1]`, realised as a Mathlib `ContDiffBump` with `rIn = 1/2`
and `rOut = 1`. -/
noncomputable def kmtBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The complex-valued cutoff `η = kmtBump`. -/
noncomputable def kmtEta : ℝ → ℂ := fun x => ((kmtBump : ℝ → ℝ) x : ℂ)

/-- `η = 1` on `[-1/2, 1/2]`. -/
theorem kmtEta_one {x : ℝ} (hx : |x| ≤ 1 / 2) : kmtEta x = 1 := by
  have h : x ∈ Metric.closedBall (0 : ℝ) (kmtBump.rIn) := by
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, kmtBump]
    exact hx
  simp only [kmtEta]
  rw [ContDiffBump.one_of_mem_closedBall kmtBump h]
  norm_num

/-- `η = 0` off `[-1, 1]`. -/
theorem kmtEta_zero {x : ℝ} (hx : 1 ≤ |x|) : kmtEta x = 0 := by
  have h : (kmtBump).rOut ≤ dist x (0 : ℝ) := by
    rw [dist_zero_right, Real.norm_eq_abs, kmtBump]; exact hx
  simp only [kmtEta]
  rw [ContDiffBump.zero_of_le_dist kmtBump h]
  norm_num

/-- `η` is even. -/
theorem kmtEta_neg (x : ℝ) : kmtEta (-x) = kmtEta x := by
  simp only [kmtEta]
  rw [ContDiffBump.neg]

/-- `0 ≤ η ≤ 1`. -/
theorem kmtEta_nonneg (x : ℝ) : 0 ≤ kmtBump x := ContDiffBump.nonneg kmtBump
theorem kmtEta_le_one (x : ℝ) : kmtBump x ≤ 1 := ContDiffBump.le_one kmtBump

/-- `‖η x‖ ≤ 1`. -/
theorem norm_kmtEta_le (x : ℝ) : ‖kmtEta x‖ ≤ 1 := by
  simp only [kmtEta, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (kmtEta_nonneg x)]
  exact kmtEta_le_one x

/-! ## The Ionescu--Wainger projections -/

/-- **The Ionescu--Wainger projection `Π_{≤ l, ≤ k}` of §5 on an arbitrary function.**

`kmtProj ρ l k f` is the convolution of `f` with the Fourier coefficients of the IW symbol
`ξ ↦ ∑_{α ∈ (ℚ/ℤ)_{≤l}} η((ξ - α)/2^k)`, i.e. the paper's operator
`T^{≤l}_{η_{≤k}} = Π_{≤l,≤k}` written in the form used by `Work.Analysis.IWMultiplier.iwConv`
(so that it makes sense for every `f : ℤ → ℂ`, without an `ℓ²` hypothesis). -/
noncomputable def kmtProj (ρ : ℝ) (l : ℕ) (k : ℤ) (f : ℤ → ℂ) : ℤ → ℂ :=
  iwConv (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) f

theorem kmtProj_apply (ρ : ℝ) (l : ℕ) (k : ℤ) (f : ℤ → ℂ) (n : ℤ) :
    kmtProj ρ l k f n
      = ∑' j : ℤ,
          iwKernel (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) j * f (n - j) :=
  rfl

/-- The concrete Ionescu--Wainger projections, bundled as the projection interface of the `EndVar`
chapter. -/
noncomputable def kmtPj (ρ : ℝ) : IWProjections := ⟨kmtProj ρ⟩

@[simp] theorem kmtPj_proj (ρ : ℝ) (l : ℕ) (k : ℤ) (f : ℤ → ℂ) :
    (kmtPj ρ).proj l k f = kmtProj ρ l k f := rfl

/-! ## The projections and the §5 columns on the zero function -/

@[simp] theorem kmtProj_zero (ρ : ℝ) (l : ℕ) (k : ℤ) :
    kmtProj ρ l k (0 : ℤ → ℂ) = 0 := by
  funext n
  simp [kmtProj_apply]

@[simp] theorem piExact_kmt_zero (ρ : ℝ) (l : ℕ) (k : ℤ) :
    piExact (kmtPj ρ) l k (0 : ℤ → ℂ) = 0 := by
  rw [piExact]
  split <;> simp

@[simp] theorem piece_kmt_zero (ρ : ℝ) (l : ℕ) (κ : ℤ → ℤ) (a s : ℤ) :
    piece (kmtPj ρ) l κ a s (0 : ℤ → ℂ) = 0 := by
  rw [piece]
  split <;> simp

@[simp] theorem Fpiece_kmt_zero (ρ : ℝ) (u l : ℕ) (s : ℤ) (N : ℕ) :
    Fpiece (kmtPj ρ) u l s N (0 : ℤ → ℂ) = 0 :=
  piece_kmt_zero ρ l _ _ s

@[simp] theorem Gpiece_kmt_zero (ρ : ℝ) (d : ℤ) (u l : ℕ) (s : ℤ) (N : ℕ) :
    Gpiece (kmtPj ρ) d u l s N (0 : ℤ → ℂ) = 0 :=
  piece_kmt_zero ρ l _ _ s

/-- The §5 column vanishes when the second function does. -/
@[simp] theorem varpPiece_kmt_zero_right (ρ : ℝ) (P : ℤ[X]) (d : ℕ) (N : ℝ≥0) (f : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) :
    varpPiece (kmtPj ρ) P d N f 0 l₁ l₂ k₁ k₂ = 0 := by
  simp [varpPiece, AhalfR_zero_right]

/-- The §5 column vanishes when the first function does. -/
@[simp] theorem varpPiece_kmt_zero_left (ρ : ℝ) (P : ℤ[X]) (d : ℕ) (N : ℝ≥0) (g : ℤ → ℂ)
    (l₁ l₂ k₁ k₂ : ℕ) :
    varpPiece (kmtPj ρ) P d N 0 g l₁ l₂ k₁ k₂ = 0 := by
  simp [varpPiece, AhalfR_zero_left]

/-- The clamped §5 column vanishes when the second function does. -/
theorem varpCol_kmt_zero_right (ρ : ℝ) (P : ℤ[X]) (d C₀ : ℕ) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ : ℕ) (f : ℤ → ℂ) :
    varpCol (kmtPj ρ) P d C₀ a f 0 l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  rw [varpCol_apply]
  split
  · simp
  · rfl

/-- The clamped §5 column vanishes when the first function does. -/
theorem varpCol_kmt_zero_left (ρ : ℝ) (P : ℤ[X]) (d C₀ : ℕ) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ : ℕ) (g : ℤ → ℂ) :
    varpCol (kmtPj ρ) P d C₀ a 0 g l₁ l₂ k₁ k₂ = 0 := by
  funext n x
  rw [varpCol_apply]
  split
  · simp
  · rfl

/-! ## Theorem `varp` with a general weight, and its concrete instance -/

/-- **Theorem `varp` with a lacunarity-dependent constant and a general weight.**

There is a constant `C : ℝ≥0 → ℝ≥0` such that for every `Λ > 1`, every `Λ`-lacunary sequence `a`
with `a n ≥ 1`, every `l₁ l₂ s₁ s₂ : ℕ` and all `f g : ℤ → ℂ`, the §5 columns `varpCol` obey

`‖ (varpCol …)_n ‖_{ℓ^p(ℤ;V^r)} ≤ C Λ · w l₁ l₂ s₁ s₂ · ‖f‖_{ℓ^{p₁}} ‖g‖_{ℓ^{p₂}}`.

This is the hypothesis list of Theorem `varp` (Krause--Mirek--Tao §4) with the specific gain
`w` left free: the areas A6 (`VarpL2KMT`) and A7 (`VarpLossKMT`) of `ROUTE_LEAD.md` §3.1 supply
it with `w = 2^{-c·max(l₁,l₂,s₁,s₂)}` and `w = 2^{Aρ·max(l₁,l₂,s₁,s₂)}` respectively, and the
composition interpolates the two (with `VarBilinInterp`, A8) into the canonical gain
`2^{-c'·max(l₁,l₂,s₁,s₂)}` of `VarpStatementΛ`. -/
def VarpStatementΛWith (Pj : IWProjections) (P : ℤ[X]) (d C₀ : ℕ)
    (p₁ p₂ p : ℝ≥0∞) (r : ℝ≥0) (w : ℕ → ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∃ C : ℝ≥0 → ℝ≥0,
    ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
      1 < Λ → Lacunary Λ a → (∀ n, 1 ≤ a n) →
      eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ =>
          varpCol Pj P d C₀ a f g l₁ l₂ k₁ k₂ n x))
        p Measure.count
      ≤ (C Λ : ℝ≥0∞) * ENNReal.ofReal (w l₁ l₂ k₁ k₂) *
          eLpNorm f p₁ Measure.count * eLpNorm g p₂ Measure.count

/-- **Theorem `varp` for the concrete Ionescu--Wainger projections**, with `d = P.natDegree` and
a general weight `w`.  This is the shape in which the areas A6/A7 are stated. -/
def PieceBound (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (p₁ p₂ p : ℝ≥0∞) (r : ℝ≥0)
    (w : ℕ → ℕ → ℕ → ℕ → ℝ) : Prop :=
  VarpStatementΛWith (kmtPj ρ) P P.natDegree C₀ p₁ p₂ p r w

theorem pieceBound_iff (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (p₁ p₂ p : ℝ≥0∞) (r : ℝ≥0)
    (w : ℕ → ℕ → ℕ → ℕ → ℝ) :
    PieceBound ρ P C₀ p₁ p₂ p r w ↔
      VarpStatementΛWith (kmtPj ρ) P P.natDegree C₀ p₁ p₂ p r w := Iff.rfl

/-! ## The truncation `truncZ` -/

/-- The truncation `truncZ K f = f · 1_{[-K,K]}`: the finitely supported approximation used to
test the `ℓ^p` estimates of the areas on finitely supported data. -/
def truncZ (K : ℕ) (f : ℤ → ℂ) : ℤ → ℂ := fun x => if |x| ≤ (K : ℤ) then f x else 0

theorem truncZ_apply (K : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    truncZ K f x = if |x| ≤ (K : ℤ) then f x else 0 := rfl

theorem truncZ_of_le {K : ℕ} {f : ℤ → ℂ} {x : ℤ} (h : |x| ≤ (K : ℤ)) : truncZ K f x = f x := by
  rw [truncZ_apply, if_pos h]

theorem truncZ_of_gt {K : ℕ} {f : ℤ → ℂ} {x : ℤ} (h : (K : ℤ) < |x|) : truncZ K f x = 0 := by
  rw [truncZ_apply, if_neg (not_le.mpr h)]

theorem truncZ_add (K : ℕ) (f g : ℤ → ℂ) : truncZ K (f + g) = truncZ K f + truncZ K g := by
  funext x
  rw [Pi.add_apply, truncZ_apply, truncZ_apply, truncZ_apply]
  split <;> simp

theorem truncZ_smul (K : ℕ) (c : ℂ) (f : ℤ → ℂ) : truncZ K (c • f) = c • truncZ K f := by
  funext x
  rw [Pi.smul_apply, truncZ_apply, truncZ_apply]
  split <;> simp

theorem truncZ_zero (K : ℕ) : truncZ K (0 : ℤ → ℂ) = 0 := by
  funext x; rw [truncZ_apply]; split <;> simp

theorem supportIn_truncZ (K : ℕ) (f : ℤ → ℂ) :
    Work.Analysis.InverseTheory.SupportIn (truncZ K f) K := by
  intro x hx
  refine truncZ_of_gt ?_
  have hx' : (K : ℤ) < (x.natAbs : ℤ) := by exact_mod_cast hx
  rwa [Int.natCast_natAbs] at hx'

theorem finsupp_truncZ (K : ℕ) (f : ℤ → ℂ) :
    Work.Analysis.InverseTheory.FinSupp (truncZ K f) := by
  refine ⟨Finset.Icc (-(K : ℤ)) (K : ℤ), fun x hx => ?_⟩
  refine truncZ_of_gt ?_
  by_contra hc
  rw [not_lt] at hc
  rw [Finset.mem_Icc] at hx
  exact hx (abs_le.mp hc)

/-- `truncZ K` is monotone in `K`. -/
theorem truncZ_mono {K K' : ℕ} (h : K ≤ K') (f : ℤ → ℂ) (x : ℤ) :
    ‖truncZ K f x‖ ≤ ‖truncZ K' f x‖ := by
  rw [truncZ_apply, truncZ_apply]
  split
  · rename_i hx
    rw [if_pos (by omega)]
  · simp

/-- The truncations of `f` converge to `f` pointwise. -/
theorem tendsto_truncZ (f : ℤ → ℂ) (x : ℤ) :
    Tendsto (fun K : ℕ => truncZ K f x) atTop (𝓝 (f x)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop x.natAbs] with K hK
  symm
  refine truncZ_of_le ?_
  have h1 : |x| ≤ (x.natAbs : ℤ) := by rw [Int.natCast_natAbs]
  exact le_trans h1 (by exact_mod_cast hK)

end

end Work.KMTContract
