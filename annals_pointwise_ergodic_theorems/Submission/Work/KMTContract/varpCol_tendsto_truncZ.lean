import Mathlib
import Submission.Work.KMTContract.Defs

/-!
# Pointwise convergence of the truncated §5 columns

This module proves `Work.KMTContract.varpCol_tendsto_truncZ`, the third hypothesis of the
interpolation lemma `VarBilinInterp` at the columns `varpCol` of the §5 assembly.

The convergence of the individual Ionescu--Wainger projections `kmtProj ρ l k` along the
truncations `truncZ K f → f` is taken as a hypothesis `hconv`; everything else is the algebra of
`Filter.Tendsto`, because `varpCol`, `varpPiece`, `Fpiece`/`Gpiece`, `piece`, `piExact`,
`AhalfR` and `Ablock` are finite combinations of projections of `f` and `g` evaluated at fixed
shifts of the point.

The proof is layered:

* `piExact_tendsto_truncZ`, `piece_tendsto_truncZ`, `Fpiece_tendsto_truncZ`,
  `Gpiece_tendsto_truncZ` transport the convergence through the §5 dyadic pieces;
* `Ablock_tendsto`, `AhalfR_tendsto` transport it through the halved average at a fixed scale;
* `varpPiece_tendsto_truncZ` combines the two, and the main theorem handles the clamping
  indicator (which does not depend on `K`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open Polynomial
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.Analysis.Paraproduct (IWProjections)

namespace Work.KMTContract

noncomputable section

/-! ## The projections -/

/-- The convergence hypothesis `hconv`, unpacked into the form used by the following lemmas. -/
private lemma kmtProj_truncZ_tendsto (ρ : ℝ)
    (hconv : ∀ (l : ℕ) (k : ℤ) {p : ENNReal}, 1 < p → ∀ {f : ℤ → ℂ},
      MeasureTheory.MemLp f p MeasureTheory.Measure.count → ∀ n : ℤ,
        Filter.Tendsto (fun K : ℕ => kmtProj ρ l k (truncZ K f) n)
          Filter.atTop (nhds (kmtProj ρ l k f n)))
    {p : ENNReal} (h1 : 1 < p) {f : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f p MeasureTheory.Measure.count) :
    ∀ (l : ℕ) (k : ℤ) (m : ℤ),
      Filter.Tendsto (fun K : ℕ => kmtProj ρ l k (truncZ K f) m) Filter.atTop
        (nhds (kmtProj ρ l k f m)) :=
  fun l k m => hconv l k h1 hf m

/-! ## The §5 dyadic pieces -/

/-- Convergence through the exact-height projection `Π_{l,≤k} = Π_{≤l,≤k} - Π_{≤l-1,≤k}`. -/
private lemma piExact_tendsto_truncZ {Pj : IWProjections} {f : ℤ → ℂ}
    (h : ∀ (l : ℕ) (k : ℤ) (m : ℤ),
      Filter.Tendsto (fun K : ℕ => Pj.proj l k (truncZ K f) m) Filter.atTop
        (nhds (Pj.proj l k f m))) :
    ∀ (l : ℕ) (k : ℤ) (m : ℤ),
      Filter.Tendsto (fun K : ℕ => piExact Pj l k (truncZ K f) m) Filter.atTop
        (nhds (piExact Pj l k f m)) := by
  intro l k m
  by_cases h0 : l = 0
  · subst h0
    simpa only [piExact, if_true] using h 0 k m
  · have h1 : Filter.Tendsto (fun K : ℕ => Pj.proj l k (truncZ K f) m) Filter.atTop
        (nhds (Pj.proj l k f m)) := h l k m
    have h2 : Filter.Tendsto (fun K : ℕ => Pj.proj (l - 1) k (truncZ K f) m) Filter.atTop
        (nhds (Pj.proj (l - 1) k f m)) := h (l - 1) k m
    have h3 := h1.sub h2
    simpa only [piExact, if_neg h0, Pi.sub_apply] using h3

/-- Convergence through the generic continuous frequency piece `piece`. -/
private lemma piece_tendsto_truncZ {Pj : IWProjections} {f : ℤ → ℂ}
    (h : ∀ (l : ℕ) (k : ℤ) (m : ℤ),
      Filter.Tendsto (fun K : ℕ => Pj.proj l k (truncZ K f) m) Filter.atTop
        (nhds (Pj.proj l k f m))) :
    ∀ (l : ℕ) (κ : ℤ → ℤ) (a s : ℤ) (m : ℤ),
      Filter.Tendsto (fun K : ℕ => piece Pj l κ a s (truncZ K f) m) Filter.atTop
        (nhds (piece Pj l κ a s f m)) := by
  intro l κ a s m
  have hp := piExact_tendsto_truncZ h
  by_cases hsa : s = a
  · have h1 : Filter.Tendsto (fun K : ℕ => piExact Pj l (κ s) (truncZ K f) m) Filter.atTop
        (nhds (piExact Pj l (κ s) f m)) := hp l (κ s) m
    simpa only [piece, if_pos hsa] using h1
  · have h1 : Filter.Tendsto
        (fun K : ℕ => piExact Pj l (κ s) (truncZ K f) m
          - piExact Pj l (κ (s - 1)) (truncZ K f) m)
        Filter.atTop (nhds (piExact Pj l (κ s) f m - piExact Pj l (κ (s - 1)) f m)) :=
      (hp l (κ s) m).sub (hp l (κ (s - 1)) m)
    simpa only [piece, if_neg hsa, Pi.sub_apply] using h1

/-- Convergence through the `f`-piece `F^{u,l,s}_N f` at a fixed scale `N`. -/
private lemma Fpiece_tendsto_truncZ {Pj : IWProjections} {f : ℤ → ℂ}
    (h : ∀ (l : ℕ) (k : ℤ) (m : ℤ),
      Filter.Tendsto (fun K : ℕ => Pj.proj l k (truncZ K f) m) Filter.atTop
        (nhds (Pj.proj l k f m))) :
    ∀ (u l : ℕ) (s : ℤ) (N : ℕ) (m : ℤ),
      Filter.Tendsto (fun K : ℕ => Fpiece Pj u l s N (truncZ K f) m) Filter.atTop
        (nhds (Fpiece Pj u l s N f m)) := by
  intro u l s N m
  have hp := piece_tendsto_truncZ h
  simpa only [Fpiece_eq] using hp l (fun s => -(logN N) + s) (-(u : ℤ)) s m

/-- Convergence through the `g`-piece `G^{u,l,s}_N g` at a fixed scale `N`. -/
private lemma Gpiece_tendsto_truncZ {Pj : IWProjections} {g : ℤ → ℂ}
    (h : ∀ (l : ℕ) (k : ℤ) (m : ℤ),
      Filter.Tendsto (fun K : ℕ => Pj.proj l k (truncZ K g) m) Filter.atTop
        (nhds (Pj.proj l k g m))) :
    ∀ (d : ℤ) (u l : ℕ) (s : ℤ) (N : ℕ) (m : ℤ),
      Filter.Tendsto (fun K : ℕ => Gpiece Pj d u l s N (truncZ K g) m) Filter.atTop
        (nhds (Gpiece Pj d u l s N g m)) := by
  intro d u l s N m
  have hp := piece_tendsto_truncZ h
  simpa only [Gpiece_eq] using hp l (fun s => d * (-(logN N) + s)) (-(u : ℤ)) s m

/-! ## The halved average at a fixed scale -/

/-- Convergence through the (un-normalised) halved block sum `Ablock TZ`. -/
private lemma Ablock_tendsto {F G : ℕ → ℤ → ℂ} {F₀ G₀ : ℤ → ℂ}
    (hF : ∀ y : ℤ, Filter.Tendsto (fun K : ℕ => F K y) Filter.atTop (nhds (F₀ y)))
    (hG : ∀ y : ℤ, Filter.Tendsto (fun K : ℕ => G K y) Filter.atTop (nhds (G₀ y)))
    (m : ℕ) (P₁ P₂ : Polynomial ℤ) (x : ℤ) :
    Filter.Tendsto (fun K : ℕ => Ablock TZ m P₁ P₂ (F K) (G K) x) Filter.atTop
      (nhds (Ablock TZ m P₁ P₂ F₀ G₀ x)) := by
  simp only [Ablock]
  exact tendsto_finsetSum _ (fun n _ => (hF _).mul (hG _))

/-- Convergence through the halved average `Ã_N` at a fixed real scale `N`. -/
private lemma AhalfR_tendsto {F G : ℕ → ℤ → ℂ} {F₀ G₀ : ℤ → ℂ}
    (hF : ∀ y : ℤ, Filter.Tendsto (fun K : ℕ => F K y) Filter.atTop (nhds (F₀ y)))
    (hG : ∀ y : ℤ, Filter.Tendsto (fun K : ℕ => G K y) Filter.atTop (nhds (G₀ y)))
    (N : ℝ≥0) (P₁ P₂ : Polynomial ℤ) (x : ℤ) :
    Filter.Tendsto (fun K : ℕ => AhalfR TZ N P₁ P₂ (F K) (G K) x) Filter.atTop
      (nhds (AhalfR TZ N P₁ P₂ F₀ G₀ x)) := by
  simp only [AhalfR, Ahalf]
  exact (Ablock_tendsto hF hG (Nat.floor N) P₁ P₂ x).const_mul _

/-! ## The §5 column, unclamped -/

/-- Convergence through the unclamped §5 summand `varpPiece` at a fixed scale `a n`. -/
private lemma varpPiece_tendsto_truncZ (ρ : ℝ) (P : Polynomial ℤ) (d : ℕ)
    (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ n : ℕ)
    (hconv : ∀ (l : ℕ) (k : ℤ) {p : ENNReal}, 1 < p → ∀ {f : ℤ → ℂ},
      MeasureTheory.MemLp f p MeasureTheory.Measure.count → ∀ m : ℤ,
        Filter.Tendsto (fun K : ℕ => kmtProj ρ l k (truncZ K f) m) Filter.atTop
          (nhds (kmtProj ρ l k f m)))
    {p₁ p₂ : ENNReal} (h1 : 1 < p₁) (h2 : 1 < p₂) {f g : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f p₁ MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g p₂ MeasureTheory.Measure.count) (x : ℤ) :
    Filter.Tendsto
      (fun K : ℕ => varpPiece (kmtPj ρ) P d (a n) (truncZ K f) (truncZ K g)
        l₁ l₂ k₁ k₂ x)
      Filter.atTop
      (nhds (varpPiece (kmtPj ρ) P d (a n) f g l₁ l₂ k₁ k₂ x)) := by
  have hpf : ∀ (l : ℕ) (k : ℤ) (m : ℤ),
      Filter.Tendsto (fun K : ℕ => (kmtPj ρ).proj l k (truncZ K f) m) Filter.atTop
        (nhds ((kmtPj ρ).proj l k f m)) := fun l k m => hconv l k h1 hf m
  have hpg : ∀ (l : ℕ) (k : ℤ) (m : ℤ),
      Filter.Tendsto (fun K : ℕ => (kmtPj ρ).proj l k (truncZ K g) m) Filter.atTop
        (nhds ((kmtPj ρ).proj l k g m)) := fun l k m => hconv l k h2 hg m
  have hF : ∀ y : ℤ, Filter.Tendsto
      (fun K : ℕ => Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) (truncZ K f) y)
      Filter.atTop (nhds (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f y)) :=
    Fpiece_tendsto_truncZ hpf 0 l₁ (k₁ : ℤ) (Nat.floor (a n))
  have hG : ∀ y : ℤ, Filter.Tendsto
      (fun K : ℕ => Gpiece (kmtPj ρ) (d : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) (truncZ K g) y)
      Filter.atTop (nhds (Gpiece (kmtPj ρ) (d : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g y)) :=
    Gpiece_tendsto_truncZ hpg (d : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n))
  simpa only [varpPiece] using AhalfR_tendsto hF hG (a n) X P x

/-! ## The main theorem -/

/-- **Pointwise convergence of the truncated §5 columns.**  This is the third hypothesis of the
interpolation lemma `VarBilinInterp` (area A8) at the operator
`T = varpCol (kmtPj ρ) P P.natDegree C₀ a · · l₁ l₂ s₁ s₂`: it says that feeding the truncations
`truncZ K f`, `truncZ K g` into the columns and letting `K → ∞` converges pointwise to the value
at `f`, `g`.

The convergence of `kmtProj` along truncations (target `kmtProj_tendsto_truncZ`, which needs the
`j^{-2}` kernel decay) is taken here as a hypothesis `hconv`, so that this bracket of the contract
can be proved independently of the kernel-decay target.  The rest is bookkeeping: `varpCol`,
`varpPiece`, `Fpiece`/`Gpiece`, `piece`, `piExact` and `AhalfR` are finite linear combinations of
projections of `f` and `g` evaluated at the shifted points `x - n`, `x - P(n)`, and
`truncZ K f → f` pointwise for every argument, so the limits are computed by the algebra of
`Filter.Tendsto` (`Tendsto.add/sub/mul/const_mul`, `tendsto_const_nhds`). -/
theorem varpCol_tendsto_truncZ (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ s₁ s₂ : ℕ)
    (hconv : ∀ (l : ℕ) (k : ℤ) {p : ENNReal}, 1 < p → ∀ {f : ℤ → ℂ},
      MeasureTheory.MemLp f p MeasureTheory.Measure.count → ∀ n : ℤ,
        Filter.Tendsto
          (fun K : ℕ => Work.KMTContract.kmtProj ρ l k (Work.KMTContract.truncZ K f) n)
          Filter.atTop (nhds (Work.KMTContract.kmtProj ρ l k f n)))
    {p₁ p₂ : ENNReal} (h1 : 1 < p₁) (h2 : 1 < p₂) {f g : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f p₁ MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g p₂ MeasureTheory.Measure.count) (n : ℕ) (x : ℤ) :
    Filter.Tendsto
      (fun K : ℕ => Work.Analysis.EndVar.varpCol (Work.KMTContract.kmtPj ρ) P P.natDegree C₀ a
        (Work.KMTContract.truncZ K f) (Work.KMTContract.truncZ K g) l₁ l₂ s₁ s₂ n x)
      Filter.atTop
      (nhds (Work.Analysis.EndVar.varpCol (Work.KMTContract.kmtPj ρ) P P.natDegree C₀ a
        f g l₁ l₂ s₁ s₂ n x)) := by
  by_cases hC : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (s₁ : ℤ) (s₂ : ℤ)
      (Nat.floor (a n))
  · simp only [Work.Analysis.EndVar.varpCol_apply, if_pos hC]
    exact varpPiece_tendsto_truncZ ρ P P.natDegree a l₁ l₂ s₁ s₂ n hconv h1 h2 hf hg x
  · simp only [Work.Analysis.EndVar.varpCol_apply, if_neg hC]
    exact tendsto_const_nhds

end

end Work.KMTContract
