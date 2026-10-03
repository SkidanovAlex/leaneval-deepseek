/-
# Vocabulary for the exact-height §6 model approximation of Area A7 (`ModelApproxHi`)

This module fixes the kernels occurring in the single-scale model approximation of §6 of

* B. Krause, M. Mirek, T. Tao, *Pointwise ergodic theorems for non-conventional bilinear
  polynomial averages*, Annals of Math. 195 (3) 2022,

in the exact-height formulation of `Work.KMTAreas.A7.mainPartTuple` / `modelTuple`
(`A7/Large/Defs.lean`):

* `hiKconc` — the kernel of the concrete halved average `Ã_N(F^{l₁}_{k₁}f, G^{l₂}_{k₂}g)`;
* `hiKmod` — the kernel of the §6 model operator
  `∫_{1/2}^1 B^{l₁,l₂,m_Ẑ}_{m_*}(T^{l₁}_{φ_{N,t}}f, T^{l₂}_{φ̃_{N,t}}g)dt`;
* `hiKer` — the kernel of the exact-height IW multiplier `Tex ρ l φ` (valid for `l ≥ 1`);
* `hiTwKernel` — the arithmetic/`m_*` kernel of the twisted bilinear multiplier.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxDefs
import Submission.Work.KMTAreas.A7.BilinOpKhalf
import Submission.Work.KMTAreas.A7.BilinOpLp
import Submission.Work.A7.ModelApproxCore_Fpiece_convOp
import Submission.Work.A7.ModelApproxCore_Gpiece_convOp
import Submission.Work.A7.ModelApproxCore_kernelComp
import Submission.Work.KMTPlan.A6.IwKernelArithChar

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.EndVar Work.Analysis.IWMultiplier

/-! ## The exact-height IW kernel -/

/-- The kernel of the exact-height Ionescu--Wainger multiplier `Tex ρ l φ`: the Fourier
coefficients of the symbol `∑_{α ∈ (ℚ/ℤ)_l} (periodize φ)(· - α)`. -/
noncomputable def hiKer (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) : ℤ → ℂ :=
  iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize φ))

/-- For `l ≥ 1` the exact-height arithmetic frequency set of `Tex` is `diffFreqs`. -/
theorem iwArithFreqsNew_eq_diffFreqs (ρ : ℝ) {l : ℕ} (hl : 1 ≤ l) :
    Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l = diffFreqs ρ l := by
  simp only [Work.Analysis.IonescuWainger.iwArithFreqsNew, diffFreqs, if_neg (by omega : ¬ l = 0)]

/-- **`Tex ρ l φ` is the convolution with `hiKer ρ l φ`** (for `l ≥ 1`). -/
theorem Tex_eq_convOp_hiKer (ρ : ℝ) {l : ℕ} (hl : 1 ≤ l) (φ : ℝ → ℂ) (f : ℤ → ℂ) :
    Tex ρ l φ f = convOp (hiKer ρ l φ) f := by
  funext n
  rw [Tex, iwConv_apply, convOp]
  refine tsum_congr (fun j => ?_)
  rw [iwArithFreqsNew_eq_diffFreqs ρ hl, smul_eq_mul]
  rfl

/-- **Fibre form of the exact-height kernel**: it is the arithmetic character sum over the
exact-height frequency set times the continuous Fourier transform of the bump. -/
theorem hiKer_fourier (ρ : ℝ) (l : ℕ) {φ : ℝ → ℂ} (hφ : Integrable φ) (j : ℤ) :
    hiKer ρ l φ j = (∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α) * cw φ j :=
  Work.KMTPlan.A6.IwKernelArithChar (diffFreqs ρ l) hφ j

/-! ## The twisted bilinear kernel of the §6 model -/

/-- The arithmetic/`m_*` kernel of the twisted bilinear multiplier `B^{l₁,l₂,m_Ẑ}_{m₁⊗m₂}` at
exact arithmetic heights. -/
noncomputable def hiTwKernel (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ) : ℤ → ℤ → ℂ :=
  fun j₁ j₂ => arithKernelExact ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂

/-- **`BtwistExact` is the bilinear convolution with `hiTwKernel`** (definitional). -/
theorem BtwistExact_eq_bilinOp_hiTw (ρ : ℝ) (P : ℤ[X]) (l₁ l₂ : ℕ) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) :
    BtwistExact ρ P l₁ l₂ m₁ m₂ h k = bilinOp (hiTwKernel ρ P l₁ l₂ m₁ m₂) h k := rfl

/-! ## Summability of the piece kernels -/

/-- The exact-height kernel `exactKer ρ l k` is absolutely summable. -/
theorem summable_exactKer_norm (ρ : ℝ) (l : ℕ) (k : ℤ) :
    Summable (fun j : ℤ => ‖exactKer ρ l k j‖) := by
  rcases eq_or_ne l 0 with hl | hl
  · subst hl
    rw [exactKer, if_pos rfl]
    exact Work.KMTAreas.A5.summable_kmtKern_norm ρ 0 k
  · rw [exactKer, if_neg hl]
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      ((Work.KMTAreas.A5.summable_kmtKern_norm ρ l k).add
        (Work.KMTAreas.A5.summable_kmtKern_norm ρ (l - 1) k))
    simp only [Pi.sub_apply]
    exact norm_sub_le _ _

/-- The §5 piece kernel `pieceKer ρ l κs a s` is absolutely summable. -/
theorem summable_pieceKer_norm (ρ : ℝ) (l : ℕ) (κs : ℤ → ℤ) (a s : ℤ) :
    Summable (fun j : ℤ => ‖pieceKer ρ l κs a s j‖) := by
  by_cases h : s = a
  · rw [pieceKer, if_pos h]
    exact summable_exactKer_norm ρ l (κs s)
  · rw [pieceKer, if_neg h]
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      ((summable_exactKer_norm ρ l (κs s)).add (summable_exactKer_norm ρ l (κs (s - 1))))
    simp only [Pi.sub_apply]
    exact norm_sub_le _ _

/-- The kernel `khalf m P` of the halved average is finitely supported, hence summable. -/
theorem summable_khalf_norm (m : ℕ) (P : Polynomial ℤ) :
    Summable (fun p : ℤ × ℤ => ‖khalf m P p.1 p.2‖) := by
  refine summable_of_ne_finset_zero
    (s := (Finset.Icc ((m : ℤ) / 2 + 1) (m : ℤ)).image (fun a => (a, P.eval a))) ?_
  rintro ⟨a, b⟩ hp
  rw [khalf]
  by_cases hc : (m / 2 : ℤ) < a ∧ a ≤ (m : ℤ) ∧ b = P.eval a
  · rw [if_pos hc]
    exfalso
    apply hp
    obtain ⟨h1, h2, h3⟩ := hc
    refine Finset.mem_image.mpr ⟨a, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      refine ⟨?_, h2⟩
      have h2' : ((m / 2 : ℕ) : ℤ) = (m : ℤ) / 2 := Int.natCast_div m 2
      omega
    · rw [h3]
  · rw [if_neg hc]
    simp

/-! ## The kernel of the concrete column -/

/-- **The kernel of the concrete column** `mainPartTuple`: the §5 halved average of the two
exact-height pieces is the bilinear convolution with `hiKconc`. -/
noncomputable def hiKconc (ρ : ℝ) (P : ℤ[X]) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) :
    ℤ → ℤ → ℂ :=
  kernComp (khalf (Nat.floor (a n)) P)
    (pieceKer ρ l₁ (fun s : ℤ => -(logN (Nat.floor (a n))) + s) 0 (k₁ : ℤ))
    (pieceKer ρ l₂
      (fun s : ℤ => (P.natDegree : ℤ) * (-(logN (Nat.floor (a n))) + s)) 0 (k₂ : ℤ))

/-- The kernel `hiKconc` is absolutely summable. -/
theorem summable_hiKconc (ρ : ℝ) (P : ℤ[X]) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) :
    Summable (fun p : ℤ × ℤ => ‖hiKconc ρ P a l₁ l₂ k₁ k₂ n p.1 p.2‖) := by
  have h := Work.A7.ModelApproxCore_aux.summable_kernComp
    (K := khalf (Nat.floor (a n)) P)
    (κ := pieceKer ρ l₁ (fun s : ℤ => -(logN (Nat.floor (a n))) + s) 0 (k₁ : ℤ))
    (κ' := pieceKer ρ l₂
      (fun s : ℤ => (P.natDegree : ℤ) * (-(logN (Nat.floor (a n))) + s)) 0 (k₂ : ℤ))
    (summable_khalf_norm (Nat.floor (a n)) P)
    (summable_pieceKer_norm ρ l₁ _ 0 (k₁ : ℤ))
    (summable_pieceKer_norm ρ l₂ _ 0 (k₂ : ℤ))
  simpa only [hiKconc] using h

/-- **The concrete column is the bilinear convolution with `hiKconc`.** -/
theorem varpPiece_eq_bilinOp_hiKconc (ρ : ℝ) (P : ℤ[X]) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ n : ℕ) {f g : ℤ → ℂ}
    (hf : Work.KMTAreas.A5.BoundedZ f) (hg : Work.KMTAreas.A5.BoundedZ g) (x : ℤ) :
    varpPiece (Work.KMTContract.kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂ x
      = bilinOp (hiKconc ρ P a l₁ l₂ k₁ k₂ n) f g x := by
  rw [varpPiece, BilinOpKhalf (a n) P _ _,
    Work.A7.ModelApproxCore_Fpiece_convOp ρ l₁ k₁ (Nat.floor (a n)) hf,
    Work.A7.ModelApproxCore_Gpiece_convOp ρ P.natDegree l₂ k₂ (Nat.floor (a n)) hg,
    ← Work.A7.ModelApproxCore_kernelComp
      (K := khalf (Nat.floor (a n)) P)
      (κ := pieceKer ρ l₁ (fun s : ℤ => -(logN (Nat.floor (a n))) + s) 0 (k₁ : ℤ))
      (κ' := pieceKer ρ l₂
        (fun s : ℤ => (P.natDegree : ℤ) * (-(logN (Nat.floor (a n))) + s)) 0 (k₂ : ℤ))
      (u := f) (v := g) (Cu := hf.choose) (Cv := hg.choose)
      (summable_khalf_norm (Nat.floor (a n)) P)
      (summable_pieceKer_norm ρ l₁ _ 0 (k₁ : ℤ))
      (summable_pieceKer_norm ρ l₂ _ 0 (k₂ : ℤ))
      hf.choose_spec hg.choose_spec x]
  rfl

/-! ## The kernel of the §6 model -/

/-- **The kernel of the §6 model operator** (as used by `modelTuple`):
the `t`-integral of the composition of the twisted kernel with the two exact-height kernels of the
modulated bumps. -/
noncomputable def hiKmod (ρ : ℝ) (P : ℤ[X]) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) :
    ℤ → ℤ → ℂ :=
  fun j₁ j₂ => ∫ t in (1/2 : ℝ)..1,
    kernComp (hiTwKernel ρ P l₁ l₂
        (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
        (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))))
      (hiKer ρ l₁ (varphiNt (Nat.floor (a n)) k₁ t))
      (hiKer ρ l₂ (varphitildeNt P P.natDegree (Nat.floor (a n)) k₂ t)) j₁ j₂

/-! ## The fixture conditions -/

/-- **The `hi` core condition**: the guard of `mainPartTuple`/`modelTuple` together with the two
hypotheses `1 ≤ l₁`, `1 ≤ l₂` under which the exact-height objects of `Large/Defs.lean` are the
paper's §6 objects. -/
def hiCore (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (n : ℕ) : Prop :=
  inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) ∧
    splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n) ∧
    mainRegime ρ k₁ k₂ (Nat.floor (a n))

theorem hiCore_iff (ρ : ℝ) (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) :
    hiCore ρ P C₀ a l₁ l₂ k₁ k₂ n ↔
      inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) ∧
        splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n) ∧
        mainRegime ρ k₁ k₂ (Nat.floor (a n)) := Iff.rfl

end
end Work.KMTAreas.A7
