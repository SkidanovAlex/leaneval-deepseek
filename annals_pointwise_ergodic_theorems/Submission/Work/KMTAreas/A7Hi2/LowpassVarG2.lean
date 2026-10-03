/-
# The `g`-side low-pass lacunary variational estimate, from its three dyadic pieces

This module reduces the `g`-side low-pass estimate of the target
`Work.KMTAreas.A7Hi.LinVarG` (paper `(lin-2)`, low-frequency case `k₂ = 0`, for the *unmodulated*
bump `φ̃_N = varphitildeN d N 0`) to the **dyadic** estimate for the Ionescu--Wainger projections
`m ↦ kmtProj ρ l₁ (-(m₀+m))`.

The reduction is the same one as in `Work.KMTAreas.A7.lacunaryIWProjLowpassVar` (which does it on
the `f`-side for `varphiN`):

* `varphitildeN d N 0 = etaCut kmtEta (-(d * logN N))`, whence
  `Tle ρ l₂ (varphitildeN d N 0) = kmtProj ρ l₂ (-(d * logN N))` (`Tle_etaCut`);
* for a `Λ`-lacunary family `a` the map `n ↦ d * logN ⌊a n⌋` is monotone, and reindexing a family
  by a monotone map does not increase its variational norm
  (`Work.KMTAreas.A7.variationalNorm_comp_mono_le`);
* `GoodMajorArcs ρ Cρ l₂ k` forces `k ≤ 0` and `k ≥ -(d * logN ⌊a n⌋)` is the narrowness
  hypothesis, so with `m₀ := (-k).toNat` the dyadic family `m ↦ kmtProj ρ l₂ (-(m₀+m))` covers
  the reindexed lacunary family.

The dyadic estimate itself is assembled (exactly as in `Work.KMTAreas.A7Hi.LowpassVar`) from its
three definitional pieces, which are hypotheses here so that the module is independent of their
proofs:

* `SupPiece` — the values-supremum (maximal) bound;
* `ChainPiece` — the chain term of the variational norm, controlled by the supremum and by the
  band-pass square function of the increments;
* `SqPiece` — the band-pass square-function bound for the increments.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.lacDilTriVar
import Submission.Work.KMTAreas.A7Hi.LowpassDefs
import Submission.Work.KMTAreas.A7.LoHelpers
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7Hi2

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems

noncomputable section

/-! ## The three dyadic pieces -/

/-- The values-supremum piece: the Ionescu--Wainger maximal bound for the family
`m ↦ lpf ρ l₁ m₀ m f = kmtProj ρ l₁ (-(m₀+m)) f` on the good major arcs, with the polynomial
loss `(1+l₁)²` and constant independent of `m₀`. -/
def SupPiece : Prop :=
  ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤)
    (r : NNReal),
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count

/-- The chain piece: the chain term of the variational norm of the family is controlled by its
values supremum and by the band-pass square function of its increments, with a real-variable
constant `B` independent of `l₁` and `m₀`. -/
def ChainPiece : Prop :=
  ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Cρ₀ : ℝ),
    ∃ B : ℝ, 0 < B ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ₀ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ =>
          Work.KMTAreas.A7Hi.chainPart r (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal B *
          (MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
              (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
              p MeasureTheory.Measure.count
           + MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
              p MeasureTheory.Measure.count)

/-- The square-function piece: the band-pass square function of the increments of the family is
bounded on `ℓᵖ` by `C(1+l₁)²‖f‖`, uniformly in the base level `m₀` and the arithmetic height `l₁`. -/
def SqPiece : Prop :=
  ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤),
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f) p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count

/-! ## The dyadic assembly -/

/-- **The dyadic low-pass variational estimate**, assembled from the three pieces: for
`0 < ρ ≤ 1`, `2 < r`, `1 < p < ∞` there are `Cρ > 0`, `C > 0` such that on the good major arcs
`GoodMajorArcs ρ Cρ l₁ (-(m₀))` the `r`-variation of the family `m ↦ kmtProj ρ l₁ (-(m₀+m)) f` is
bounded on `ℓᵖ(ℤ)` by `C(1+l₁)²‖f‖`, uniformly in `m₀` and `l₁`. -/
theorem dyadicLowpass (hSup : SupPiece) (hChain : ChainPiece) (hSq : SqPiece)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧ ∀ (l₁ m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₁ (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l₁ : ℝ)) ^ 2) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  obtain ⟨CρA, hCρAp, A, hAp, hA⟩ := hSup ρ hρ hρ1 p hp hptop r
  obtain ⟨CρC, hCρCp, C, hCp, hC⟩ := hSq ρ hρ hρ1 p hp hptop
  obtain ⟨B, hBp, hB⟩ := hChain ρ hρ hρ1 r hr p hp hptop (max CρA CρC)
  refine ⟨max CρA CρC, lt_max_of_lt_left hCρAp, A + B * (A + C), by positivity, ?_⟩
  intro l₁ m₀ hgood f
  have hgoodA : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρA l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (C₁ := CρA) (C₂ := max CρA CρC)
      (le_max_left _ _) hgood
  have hgoodC : Work.Analysis.IonescuWainger.GoodMajorArcs ρ CρC l₁ (-(m₀ : ℤ)) :=
    Work.KMTAreas.A7Hi.goodMajorArcs_mono (C₁ := CρC) (C₂ := max CρA CρC)
      (le_max_right _ _) hgood
  have hsplit : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
      = (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        + (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x)) := by
    funext x; exact Work.KMTAreas.A7Hi.variationalNorm_eq_parts r _
  rw [hsplit]
  have hp1 : (1 : ℝ≥0∞) ≤ p := le_of_lt hp
  have hsub := Work.KMTAreas.A7.eLpNorm_add_le_ennreal
    (u := fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
      (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
    (v := fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
      (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
    hp1 (ne_of_lt hptop) (μ := MeasureTheory.Measure.count)
  have hAs := hA l₁ m₀ hgoodA f
  have hBs := hB l₁ m₀ hgood f
  have hCs := hC l₁ m₀ hgoodC f
  refine hsub.trans ?_
  have hXY : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
      + MeasureTheory.eLpNorm (Work.KMTAreas.A7Hi.sqFun ρ l₁ m₀ f)
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal ((A + C) * (1 + (l₁ : ℝ)) ^ 2) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    refine (add_le_add hAs hCs).trans (le_of_eq ?_)
    have hsum : (A + C) * (1 + (l₁ : ℝ)) ^ 2
        = A * (1 + (l₁ : ℝ)) ^ 2 + C * (1 + (l₁ : ℝ)) ^ 2 := by ring
    rw [hsum]
    exact Work.KMTAreas.A7Hi.ofReal_mul_add_eq (by positivity) (by positivity) _
  have hchainE : MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₁ m₀ m f x))
        p MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (B * ((A + C) * (1 + (l₁ : ℝ)) ^ 2)) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
    refine (hBs.trans (mul_le_mul_right hXY _)).trans (le_of_eq ?_)
    exact Work.KMTAreas.A7Hi.ofReal_mul_mul_eq (by positivity) (by positivity) _
  refine (add_le_add hAs hchainE).trans (le_of_eq ?_)
  have hsum : (A + B * (A + C)) * (1 + (l₁ : ℝ)) ^ 2
      = A * (1 + (l₁ : ℝ)) ^ 2 + B * ((A + C) * (1 + (l₁ : ℝ)) ^ 2) := by ring
  rw [hsum]
  exact Work.KMTAreas.A7Hi.ofReal_mul_add_eq (by positivity) (by positivity) _

/-! ## The two elementary identities for the `g`-side bump -/

/-- `varphitildeN d N 0 = etaCut kmtEta (-(d * logN N))`: the unmodulated `g`-side bump at scale
`N` is the continuous cutoff at the level `-(d * logN N)`. -/
theorem varphitildeN_zero_eq_etaCut (d N : ℕ) :
    Work.KMTAreas.A7.varphitildeN d N 0
      = Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta
          (-((d : ℤ) * Work.Analysis.EndVar.logN N)) := by
  funext ξ
  simp only [Work.KMTAreas.A7.varphitildeN, if_true,
    Work.Analysis.IonescuWainger.etaCut]
  congr 1
  have h2 : ((2 : ℝ) ^ (-((d : ℤ) * Work.Analysis.EndVar.logN N)))⁻¹
      = (2 : ℝ) ^ ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) := by
    rw [zpow_neg, inv_inv, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  rw [div_eq_mul_inv, h2]
  ac_rfl

/-- `Tle ρ l (varphitildeN d N 0) = kmtProj ρ l (-(d * logN N))`. -/
@[simp] theorem Tle_varphitildeN_zero (ρ : ℝ) (l d N : ℕ) :
    Work.KMTAreas.A7.Tle ρ l (Work.KMTAreas.A7.varphitildeN d N 0)
      = Work.KMTContract.kmtProj ρ l (-((d : ℤ) * Work.Analysis.EndVar.logN N)) := by
  rw [varphitildeN_zero_eq_etaCut]
  exact Work.KMTAreas.A7.Tle_etaCut ρ l _

/-- A `Λ`-lacunary sequence with `Λ > 1` and `a n ≥ 1` is monotone. -/
theorem monotone_of_lacunary {Λ : NNReal} (hΛ : 1 < Λ) {a : ℕ → NNReal}
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) : Monotone a := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  have hpos : (0 : NNReal) < a n := lt_of_lt_of_le zero_lt_one (ha1 n)
  have h2 : Λ < a (n + 1) / a n := ha n
  have h1 : Λ * a n < a (n + 1) := by rwa [lt_div_iff₀ hpos] at h2
  have h3 : a n ≤ Λ * a n := by
    simpa using mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt hpos)
  exact le_trans h3 h1.le

/-- `logN` is monotone in the scale. -/
theorem logN_mono' {N M : ℕ} (h : N ≤ M) :
    Work.Analysis.EndVar.logN N ≤ Work.Analysis.EndVar.logN M := by
  unfold Work.Analysis.EndVar.logN
  exact Int.ofNat_le.mpr (Nat.log_mono_right (max_le_max h le_rfl))

/-! ## The `g`-side reduction -/

/-- **The `g`-side low-pass lacunary variational estimate**, from the three dyadic pieces: for a
`Λ`-lacunary family of scales `N_n = ⌊a n⌋`, `1 < p < ∞`, `2 < r`, in the narrow regime
`GoodMajorArcs ρ Cρ l₂ k` with `k ≥ -(d * logN ⌊a n⌋)`, the `r`-variation over `n` of the
Ionescu--Wainger projections of the unmodulated `g`-side bumps `varphitildeN d N 0` is bounded on
`ℓᵖ(ℤ)` by `C (1+l₂)² ‖f‖`, uniformly in the family `a`, the height `l₂` and the level `k`. -/
theorem lowpassVarG_of_pieces (hSup : SupPiece) (hChain : ChainPiece) (hSq : SqPiece)
    (d : ℕ) (hd : 1 ≤ d) :
    ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
      (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Λ : NNReal) (hΛ : 1 < Λ),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (k : ℤ) (l₂ : ℕ) (a : ℕ → NNReal)
          (ha : PointwiseErgodicTheorems.Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
          Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₂ k →
          (∀ n : ℕ, -((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₂
                (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) f x))
            p MeasureTheory.Measure.count
            ≤ ENNReal.ofReal (C * (1 + (l₂ : ℝ)) ^ 2) *
                MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  intro ρ hρ hρ1 r hr p hp hptop Λ hΛ
  obtain ⟨Cρ, hCρ, C, hC, hCb⟩ := dyadicLowpass hSup hChain hSq ρ hρ hρ1 r hr p hp hptop
  refine ⟨Cρ, hCρ, C, hC, ?_⟩
  intro k l₂ a ha ha1 f hgood hk
  have hk0 : k ≤ 0 := by
    have hpos : (0 : ℝ) < Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) := by
      have h2 := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) (ρ * (l₂ : ℝ))
      positivity
    have h3 : (k : ℝ) ≤ 0 := by
      have h4 : (k : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * (l₂ : ℝ)) := hgood
      linarith
    exact_mod_cast h3
  have hamono : Monotone a := monotone_of_lacunary hΛ ha ha1
  set m₀ : ℕ := (-k).toNat with hm₀def
  have hm₀ : ((m₀ : ℕ) : ℤ) = -k := by
    rw [hm₀def]
    exact Int.toNat_of_nonneg (by omega)
  have hgood' : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₂ (-(m₀ : ℤ)) := by
    rw [hm₀, neg_neg]
    exact hgood
  set σ : ℕ → ℕ := fun n => (((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n))) + k).toNat
    with hσdef
  have hσmono : Monotone σ := by
    intro n m hnm
    have h1 : Nat.floor (a n) ≤ Nat.floor (a m) := Nat.floor_mono (hamono hnm)
    have h2 : Work.Analysis.EndVar.logN (Nat.floor (a n))
        ≤ Work.Analysis.EndVar.logN (Nat.floor (a m)) := logN_mono' h1
    have h2' : (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n))
        ≤ (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a m)) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have h3 : (0 : ℤ) ≤ (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n)) + k := by
      have h := hk n; omega
    have h4 : (0 : ℤ) ≤ (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a m)) + k := by
      have h := hk m; omega
    show (((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n))) + k).toNat
        ≤ (((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a m))) + k).toNat
    have hx : (((((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n))) + k).toNat : ℕ) : ℤ)
        = (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n)) + k := Int.toNat_of_nonneg h3
    have hy : (((((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a m))) + k).toNat : ℕ) : ℤ)
        = (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a m)) + k := Int.toNat_of_nonneg h4
    have h5 : (((((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n))) + k).toNat : ℕ) : ℤ)
        ≤ (((((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a m))) + k).toNat : ℕ) : ℤ) := by
      rw [hx, hy]; omega
    exact_mod_cast h5
  have hσcoe : ∀ n : ℕ, ((σ n : ℕ) : ℤ)
      = (d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n)) + k := by
    intro n
    rw [hσdef]
    exact Int.toNat_of_nonneg (by have h := hk n; omega)
  have hreindex : ∀ x : ℤ,
      (fun n : ℕ => Work.KMTContract.kmtProj ρ l₂
          (-((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n)))) f x)
        = fun n : ℕ =>
            (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₂ m₀ m f x) (σ n) := by
    intro x
    funext n
    have h1 : (-((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n))) : ℤ)
        = -((m₀ : ℤ) + ((σ n : ℕ) : ℤ)) := by
      rw [hm₀, hσcoe n]
      ring
    show Work.KMTContract.kmtProj ρ l₂ _ f x = Work.KMTContract.kmtProj ρ l₂ _ f x
    rw [h1]
  calc MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₂
            (Work.KMTAreas.A7.varphitildeN d (Nat.floor (a n)) 0) f x))
        p MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Work.KMTContract.kmtProj ρ l₂
            (-((d : ℤ) * Work.Analysis.EndVar.logN (Nat.floor (a n)))) f x))
        p MeasureTheory.Measure.count := by
        congr 1
        funext x
        simp only [Tle_varphitildeN_zero]
    _ ≤ MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₂ m₀ m f x))
        p MeasureTheory.Measure.count := by
        refine MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => ?_)
        rw [hreindex x]
        exact Work.KMTAreas.A7.variationalNorm_comp_mono_le
          (fun m : ℕ => Work.KMTAreas.A7Hi.lpf ρ l₂ m₀ m f x) hσmono
    _ ≤ ENNReal.ofReal (C * (1 + (l₂ : ℝ)) ^ 2) *
          MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := hCb l₂ m₀ hgood' f

end

end Work.KMTAreas.A7Hi2
