import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Submission.SingleScale
import Submission.Work.Analysis.Paraproduct.Varp
import Submission.Work.Analysis.SingleScale.lacunary_logb_rpow_summable

/-!
# The §5 objects of Krause--Mirek--Tao

This module fixes the notation of §5 of

* B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages*, Annals of Math. 195 (3) 2022 (arXiv:2008.00857),

the section that reduces the main variational estimate `end-var` to the major-arc paraproduct
estimates `varp` (Theorem `varp`, §4 of the paper) together with the single-scale minor arc
estimate `improv` (Theorem `improv`, §5 of the paper).  Concretely we define

* the logarithmic scale `Log N = log₂ max(N,2)` (`logN`, integer-valued) and the real scale
  `logScaleR` matching `Work.Analysis.Concentration.logScale`;
* the iterated logarithm `LogLog N` (`logLogN`) and the maximum height scale
  `l_{(N)} = C₀ LogLog N` (`heightScale`), \eqref{kl-def} of the paper;
* the two good-major-arc pairs `(l_{(N)}, -Log N + l_{(N)})` and
  `(l_{(N)}, -d Log N + d l_{(N)})` (`goodMajorArcPair₁`, `goodMajorArcPair₂`);
* the exact-height Ionescu--Wainger projection `Π_{l,≤k} = Π_{≤l,≤k} - Π_{≤l-1,≤k}` (`piExact`);
* the continuous dyadic pieces `F^{u,l₁,s₁}_N` and `G^{u,l₂,s₂}_N` of \eqref{FN-def}, \eqref{GN-def}
  (`Fpiece`, `Gpiece`, from the generic `piece`);
* the index set `I^{l,s₁,s₂} = {N : l, s₁, s₂ ≤ l_{(N)}}` of \eqref{index-def} (`inIndexSet`);
* the major arc part `R_N(f,g) = Ã_N(Π_{≤l_{(N)},≤-Log N+l_{(N)}} f,
  Π_{≤l_{(N)},≤-dLog N+dl_{(N)}} g)` of the halved average (`majorArcPart`).

The two structural identities of §5 are proved here:

* `piLe_eq_sum_piExact` : `Π_{≤l,≤m} = ∑_{0 ≤ l' ≤ l} Π_{l',≤m}`;
* `sum_Fpiece` / `sum_Gpiece` : `Π_{l,≤m} f = ∑_{-u ≤ s ≤ M} F^{u,l,s}_N f` (and the `G` analogue).

Everything in this file is sorry-free and depends only on the trusted statement layer and on the
projection interface `Work.Analysis.Paraproduct.IWProjections` (a record of the properties of
Lemma `iw-prop`; the concrete projections are `Work.Analysis.IonescuWainger.iwProj`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.Analysis.EndVar

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems
open Work.Analysis.Paraproduct (IWProjections)

/-! ## The logarithmic scales -/

/-- The paper's logarithmic scale `Log N = log₂ max(N,2)`, as an integer.  (The paper uses this
scale as a frequency threshold `2^{-Log N}`; the integer part is what the projection
`Π_{≤ l, ≤ k}` sees.) -/
def logN (N : ℕ) : ℤ := (Nat.log 2 (max N 2) : ℤ)

/-- The real logarithmic scale `Log N`, matching `Work.Analysis.Concentration.logScale`. -/
def logScaleR (N : ℕ) : ℝ := (logN N : ℝ)

/-- The paper's iterated logarithm `LogLog N`, as a natural number. -/
def logLogN (N : ℕ) : ℕ := Nat.log 2 (Nat.log 2 (max N 2) + 2)

/-- The maximum height scale `l_{(N)} = C₀ LogLog N` of \eqref{kl-def}. -/
def heightScale (C₀ N : ℕ) : ℕ := C₀ * logLogN N

lemma logN_nonneg (N : ℕ) : 0 ≤ logN N := by
  simp only [logN]; positivity

lemma logLogN_pos (N : ℕ) : 0 < logLogN N := by
  rw [logLogN, Nat.log_pos_iff]
  exact ⟨by omega, by norm_num⟩

lemma heightScale_pos {C₀ : ℕ} (h : 0 < C₀) (N : ℕ) : 0 < heightScale C₀ N :=
  Nat.mul_pos h (logLogN_pos N)

lemma logN_mono : Monotone logN := by
  intro m n h
  simp only [logN]
  exact_mod_cast Nat.log_mono_right (max_le_max_right 2 h)

lemma logLogN_mono : Monotone logLogN := by
  intro m n h
  simp only [logLogN]
  exact Nat.log_mono_right (Nat.add_le_add_right (Nat.log_mono_right (max_le_max_right 2 h)) 2)

lemma heightScale_mono (C₀ : ℕ) : Monotone (heightScale C₀) :=
  fun _ _ h => Nat.mul_le_mul_left C₀ (logLogN_mono h)

/-! ## The good major arc pairs of §5 -/

/-- The good major arc pair `(l_{(N)}, -Log N + l_{(N)})` for the first function `f`. -/
def goodMajorArcPair₁ (C₀ N : ℕ) : ℕ × ℤ :=
  (heightScale C₀ N, -(logN N) + (heightScale C₀ N : ℤ))

/-- The good major arc pair `(l_{(N)}, -d Log N + d l_{(N)})` for the second function `g`. -/
def goodMajorArcPair₂ (C₀ d N : ℕ) : ℕ × ℤ :=
  (heightScale C₀ N, -((d : ℤ) * logN N) + (d : ℤ) * (heightScale C₀ N : ℤ))

/-! ## The exact-height Ionescu--Wainger projections -/

/-- The exact-height Ionescu--Wainger projection
`Π_{l,≤k} := Π_{≤l,≤k} - Π_{≤l-1,≤k}` of \eqref{iw-2}, with the convention
`Π_{≤-1,≤k} = 0` (so that `Π_{0,≤k} = Π_{≤0,≤k}`). -/
def piExact (Pj : IWProjections) (l : ℕ) (k : ℤ) (f : ℤ → ℂ) : ℤ → ℂ :=
  if l = 0 then Pj.proj 0 k f else Pj.proj l k f - Pj.proj (l - 1) k f

/-- The arithmetic dyadic decomposition of §5: `Π_{≤l,≤m} = ∑_{0 ≤ l' ≤ l} Π_{l',≤m}`. -/
theorem piLe_eq_sum_piExact (Pj : IWProjections) (l : ℕ) (k : ℤ) (f : ℤ → ℂ) :
    Pj.proj l k f = ∑ l' ∈ Finset.range (l + 1), piExact Pj l' k f := by
  induction l with
  | zero => simp [piExact]
  | succ l ih =>
      rw [Finset.sum_range_succ, ← ih]
      have h : piExact Pj (l + 1) k f = Pj.proj (l + 1) k f - Pj.proj l k f := by
        have hsub : (l + 1) - 1 = l := by omega
        rw [piExact, if_neg (Nat.succ_ne_zero l), hsub]
      rw [h]
      abel

/-! ## The continuous dyadic pieces `F^{u,l,s}_N` and `G^{u,l,s}_N` -/

/-- The generic continuous frequency piece at the bottom scale `a`: for a frequency scale function
`κ : ℤ → ℤ`, `piece Pj l κ a s f = Π_{l,≤κ a} f` when `s = a`, and
`Π_{l,≤κ s} f - Π_{l,≤κ (s-1)} f` when `s ≠ a`.  Summing over `s ∈ [a, M]` telescopes to
`Π_{l,≤κ M} f` (`sum_piece_Icc`). -/
def piece (Pj : IWProjections) (l : ℕ) (κ : ℤ → ℤ) (a : ℤ) (s : ℤ) (f : ℤ → ℂ) : ℤ → ℂ :=
  if s = a then piExact Pj l (κ s) f
  else piExact Pj l (κ s) f - piExact Pj l (κ (s - 1)) f

/-- Unfolding of `piece` away from the bottom scale. -/
lemma piece_of_ne {Pj : IWProjections} {l : ℕ} {κ : ℤ → ℤ} {a s : ℤ} {f : ℤ → ℂ}
    (h : s ≠ a) :
    piece Pj l κ a s f = piExact Pj l (κ s) f - piExact Pj l (κ (s - 1)) f := by
  simp only [piece, if_neg h]

/-- Unfolding of `piece` at the bottom scale. -/
lemma piece_self (Pj : IWProjections) (l : ℕ) (κ : ℤ → ℤ) (a : ℤ) (f : ℤ → ℂ) :
    piece Pj l κ a a f = piExact Pj l (κ a) f := by
  simp [piece]

/-- `F^{u,l,s}_N f` of \eqref{FN-def}: the continuous frequency piece of `Π_{l,≤·} f` at scale
`-Log N + s`, the pieces for `s > -u` being Littlewood--Paley differences and the bottom piece
`s = -u` being the single projection `Π_{l,≤-Log N-u} f`. -/
def Fpiece (Pj : IWProjections) (u l : ℕ) (s : ℤ) (N : ℕ) (f : ℤ → ℂ) : ℤ → ℂ :=
  piece Pj l (fun s => -(logN N) + s) (-(u : ℤ)) s f

/-- `G^{u,l,s}_N g` of \eqref{GN-def}: the continuous frequency piece of `Π_{l,≤·} g` at the
rescaled scales `d(-Log N + s)` (the shifts of `g` are of size `N^d`, `d = deg P`). -/
def Gpiece (Pj : IWProjections) (d : ℤ) (u l : ℕ) (s : ℤ) (N : ℕ) (g : ℤ → ℂ) : ℤ → ℂ :=
  piece Pj l (fun s => d * (-(logN N) + s)) (-(u : ℤ)) s g

lemma Fpiece_eq (Pj : IWProjections) (u l : ℕ) (s : ℤ) (N : ℕ) (f : ℤ → ℂ) :
    Fpiece Pj u l s N f
      = piece Pj l (fun s => -(logN N) + s) (-(u : ℤ)) s f := rfl

lemma Gpiece_eq (Pj : IWProjections) (d : ℤ) (u l : ℕ) (s : ℤ) (N : ℕ) (g : ℤ → ℂ) :
    Gpiece Pj d u l s N g
      = piece Pj l (fun s => d * (-(logN N) + s)) (-(u : ℤ)) s g := rfl

private lemma Icc_succ_right_int {a M : ℤ} (h : a ≤ M) :
    Finset.Icc a (M + 1) = insert (M + 1) (Finset.Icc a M) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

/-- **The telescoping of the continuous dyadic pieces.**  For `a ≤ M`,
`∑_{a ≤ s ≤ M} piece Pj l κ a s f = Π_{l,≤κ M} f`. -/
theorem sum_piece_Icc (Pj : IWProjections) (l : ℕ) (κ : ℤ → ℤ) (a M : ℤ) (f : ℤ → ℂ)
    (h : a ≤ M) :
    ∑ s ∈ Finset.Icc a M, piece Pj l κ a s f = piExact Pj l (κ M) f := by
  induction M, h using Int.le_induction with
  | base => rw [Finset.Icc_self, Finset.sum_singleton, piece_self]
  | succ M hM ih =>
      have hins : (M + 1) ∉ Finset.Icc a M := by simp only [Finset.mem_Icc]; omega
      rw [Icc_succ_right_int hM, Finset.sum_insert hins, ih,
        piece_of_ne (Pj := Pj) (κ := κ) (a := a) (f := f) (by omega : ¬ (M + 1 = a))]
      rw [show M + 1 - 1 = M from by ring]
      abel

/-- **The decomposition \eqref{FN-def}: `Π_{l₁,≤m} f = ∑_{-u ≤ s₁ ≤ M} F^{u,l₁,s₁}_N f`** at
`m = -Log N + M`. -/
theorem sum_Fpiece (Pj : IWProjections) (u l : ℕ) (N : ℕ) (f : ℤ → ℂ) (M : ℤ)
    (h : -(u : ℤ) ≤ M) :
    ∑ s ∈ Finset.Icc (-(u : ℤ)) M, Fpiece Pj u l s N f
      = piExact Pj l (-(logN N) + M) f :=
  sum_piece_Icc Pj l (fun s => -(logN N) + s) (-(u : ℤ)) M f h

/-- **The decomposition \eqref{GN-def}: `Π_{l₂,≤m} g = ∑_{-u ≤ s₂ ≤ M} G^{u,l₂,s₂}_N g`** at
`m = d(-Log N + M)`. -/
theorem sum_Gpiece (Pj : IWProjections) (d : ℤ) (u l : ℕ) (N : ℕ) (g : ℤ → ℂ) (M : ℤ)
    (h : -(u : ℤ) ≤ M) :
    ∑ s ∈ Finset.Icc (-(u : ℤ)) M, Gpiece Pj d u l s N g
      = piExact Pj l (d * (-(logN N) + M)) g :=
  sum_piece_Icc Pj l (fun s => d * (-(logN N) + s)) (-(u : ℤ)) M g h

/-- The decomposition of §5, specialised to the height scale: summing the `F`-pieces up to
`l_{(N)}` recovers `Π_{l₁,≤-Log N + l_{(N)}}`. -/
theorem sum_Fpiece_heightScale (Pj : IWProjections) (u l : ℕ) (C₀ N : ℕ) (f : ℤ → ℂ)
    (h : -(u : ℤ) ≤ (heightScale C₀ N : ℤ)) :
    ∑ s ∈ Finset.Icc (-(u : ℤ)) (heightScale C₀ N : ℤ), Fpiece Pj u l s N f
      = piExact Pj l (-(logN N) + (heightScale C₀ N : ℤ)) f :=
  sum_Fpiece Pj u l N f _ h

/-- The decomposition of §5, specialised to the height scale (the `G` analogue). -/
theorem sum_Gpiece_heightScale (Pj : IWProjections) (d : ℤ) (u l : ℕ) (C₀ N : ℕ) (g : ℤ → ℂ)
    (h : -(u : ℤ) ≤ (heightScale C₀ N : ℤ)) :
    ∑ s ∈ Finset.Icc (-(u : ℤ)) (heightScale C₀ N : ℤ), Gpiece Pj d u l s N g
      = piExact Pj l (d * (-(logN N) + (heightScale C₀ N : ℤ))) g :=
  sum_Gpiece Pj d u l N g _ h

/-! ## The index set `I^{l,s₁,s₂}` and the major arc part -/

/-- The index set `I^{l,s₁,s₂} = {N ∈ D : l, s₁, s₂ ≤ l_{(N)}}` of \eqref{index-def}. -/
def inIndexSet (C₀ : ℕ) (l s₁ s₂ : ℤ) (N : ℕ) : Prop :=
  l ≤ (heightScale C₀ N : ℤ) ∧ s₁ ≤ (heightScale C₀ N : ℤ) ∧ s₂ ≤ (heightScale C₀ N : ℤ)

/-- The index set `I^{l,s₁,s₂}` is decidable. -/
instance decidableInIndexSet (C₀ : ℕ) (l s₁ s₂ : ℤ) (N : ℕ) :
    Decidable (inIndexSet C₀ l s₁ s₂ N) := by
  unfold inIndexSet; infer_instance

/-- The index set `I^{l,s₁,s₂}` factors as the conjunction of its four defining inequalities, so
that `I^{max(l₁,l₂),s₁,s₂} = I^{l₁,s₁,s₂} ∩ I^{l₂,s₁,s₂}`; this is what lets the §5 assembly
separate the arithmetic dyadic decomposition in `l₁` and `l₂`. -/
lemma inIndexSet_max_iff (C₀ : ℕ) (l₁ l₂ : ℤ) (s₁ s₂ : ℤ) (N : ℕ) :
    inIndexSet C₀ (max l₁ l₂) s₁ s₂ N ↔
      l₁ ≤ (heightScale C₀ N : ℤ) ∧ l₂ ≤ (heightScale C₀ N : ℤ) ∧
      s₁ ≤ (heightScale C₀ N : ℤ) ∧ s₂ ≤ (heightScale C₀ N : ℤ) := by
  simp only [inIndexSet, max_le_iff, and_assoc]

/-- The number of available scales `u = ⌊C₂ 2^{2ρl}⌋` of \eqref{u-def}. -/
def scaleCount (C₂ : ℕ) (ρ : ℝ) (l : ℕ) : ℕ := ⌊(C₂ : ℝ) * (2 : ℝ) ^ (2 * ρ * (l : ℝ))⌋.toNat

/-- **The major arc part of the halved average**, §5:
`R_N(f,g) = Ã_N(Π_{≤l_{(N)},≤-Log N+l_{(N)}} f, Π_{≤l_{(N)},≤-dLog N+dl_{(N)}} g)`. -/
def majorArcPart (Pj : IWProjections) (P : ℤ[X]) (d : ℕ) (C₀ : ℕ) (N : ℕ)
    (f g : ℤ → ℂ) : ℤ → ℂ :=
  AhalfR TZ N X P
    (Pj.proj (heightScale C₀ N) (-(logN N) + (heightScale C₀ N : ℤ)) f)
    (Pj.proj (heightScale C₀ N)
      (-((d : ℤ) * logN N) + (d : ℤ) * (heightScale C₀ N : ℤ)) g)

end

end Work.Analysis.EndVar
