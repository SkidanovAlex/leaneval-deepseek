import Mathlib
import Submission.Work.KMTContract.kmtProj_finsupp_linear

/-!
# Bilinearity of the §5 columns `varpCol` on finitely supported inputs

This module proves `Work.KMTContract.varpCol_finsupp_bilinear`, the bilinearity hypothesis that
the interpolation lemma `VarBilinInterp` (area A8) demands of the operator
`T = varpCol (kmtPj ρ) P P.natDegree C₀ a · · l₁ l₂ s₁ s₂`.

The whole column is a finite linear combination of the Ionescu--Wainger projections
`kmtProj ρ l k` applied to `f` (resp. `g`):

* `piExact … l k f = Π_{l,≤k} f - Π_{l-1,≤k} f` is linear in `f` because `kmtProj ρ l k` is
  (`Work.KMTContract.kmtProj_finsupp_linear`, plus the scalar version proved below);
* `piece`, `Fpiece`, `Gpiece` are case distinctions on a *fixed* frequency scale, hence linear;
* the clamping indicator `if inIndexSet … then _ else 0` does not depend on `f` or `g`, and the
  halved average `Ã = AhalfR` is bilinear (`AhalfR_add_left'`, `AhalfR_add_right'` of
  `Work.Analysis.EndVar.VarpTools`, plus the `smul` versions proved here).

All the auxiliary lemmas are `private`; the only public declaration is the target theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTContract

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal PNat BigOperators
open Submission.PointwiseErgodicTheorems
open Work.Analysis.EndVar
open Work.Analysis.Paraproduct (IWProjections)

noncomputable section

/-! ## Scalar multiplication and addition for the Ionescu--Wainger projections -/

/-- `kmtProj ρ l k` is homogeneous: it is the convolution with a fixed kernel. -/
private lemma kmtProj_smul (ρ : ℝ) (l : ℕ) (k : ℤ) (c : ℂ) (f : ℤ → ℂ) :
    kmtProj ρ l k (c • f) = c • kmtProj ρ l k f := by
  funext n
  have hK : ∀ g : ℤ → ℂ, kmtProj ρ l k g n
      = ∑' j : ℤ, Work.Analysis.IWMultiplier.iwKernel
          (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut kmtEta k))) j * g (n - j) :=
    fun g => kmtProj_apply ρ l k g n
  rw [Pi.smul_apply, hK (c • f), hK f]
  rw [smul_eq_mul, ← tsum_mul_left]
  exact tsum_congr fun j => by rw [Pi.smul_apply, smul_eq_mul]; ring

/-- **Linearity of `kmtProj ρ l k` on finitely supported inputs**, in the form needed here. -/
private lemma kmtProj_linear (ρ : ℝ) (l : ℕ) (k : ℤ) (f f' : ℤ → ℂ) (c : ℂ)
    (hf : Work.Analysis.InverseTheory.FinSupp f)
    (hf' : Work.Analysis.InverseTheory.FinSupp f') :
    kmtProj ρ l k (f + c • f') = kmtProj ρ l k f + c • kmtProj ρ l k f' := by
  have h := kmtProj_finsupp_linear ρ l k f f' c hf hf'
  rw [show (f + c • f') = fun x => f x + c * f' x from
    funext fun x => by simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]]
  rw [h]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-! ## Linearity of the projections, pieces and continuous pieces -/

/-- Linearity of the exact-height projection `piExact`. -/
private lemma piExact_linear (ρ : ℝ) (l : ℕ) (k : ℤ) (f f' : ℤ → ℂ) (c : ℂ)
    (hf : Work.Analysis.InverseTheory.FinSupp f)
    (hf' : Work.Analysis.InverseTheory.FinSupp f') :
    piExact (kmtPj ρ) l k (f + c • f') = piExact (kmtPj ρ) l k f + c • piExact (kmtPj ρ) l k f' := by
  rw [piExact, piExact, piExact]
  split_ifs with h
  · subst h
    simpa only [kmtPj_proj] using kmtProj_linear ρ 0 k f f' c hf hf'
  · simp only [kmtPj_proj]
    rw [kmtProj_linear ρ l k f f' c hf hf', kmtProj_linear ρ (l - 1) k f f' c hf hf']
    funext x
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Linearity of the continuous frequency piece `piece`. -/
private lemma piece_linear (ρ : ℝ) (l : ℕ) (κ : ℤ → ℤ) (a s : ℤ) (f f' : ℤ → ℂ) (c : ℂ)
    (hf : Work.Analysis.InverseTheory.FinSupp f)
    (hf' : Work.Analysis.InverseTheory.FinSupp f') :
    piece (kmtPj ρ) l κ a s (f + c • f') = piece (kmtPj ρ) l κ a s f + c • piece (kmtPj ρ) l κ a s f' := by
  simp only [piece]
  split_ifs with h
  · exact piExact_linear ρ l (κ s) f f' c hf hf'
  · rw [piExact_linear ρ l (κ s) f f' c hf hf',
      piExact_linear ρ l (κ (s - 1)) f f' c hf hf']
    funext x
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- Linearity of `F^{u,l,s}_N`. -/
private lemma Fpiece_linear (ρ : ℝ) (u l : ℕ) (s : ℤ) (N : ℕ) (f f' : ℤ → ℂ) (c : ℂ)
    (hf : Work.Analysis.InverseTheory.FinSupp f)
    (hf' : Work.Analysis.InverseTheory.FinSupp f') :
    Fpiece (kmtPj ρ) u l s N (f + c • f') = Fpiece (kmtPj ρ) u l s N f + c • Fpiece (kmtPj ρ) u l s N f' := by
  simp only [Fpiece]
  exact piece_linear ρ l _ (-(u : ℤ)) s f f' c hf hf'

/-- Linearity of `G^{u,l,s}_N`. -/
private lemma Gpiece_linear (ρ : ℝ) (d : ℤ) (u l : ℕ) (s : ℤ) (N : ℕ) (f f' : ℤ → ℂ) (c : ℂ)
    (hf : Work.Analysis.InverseTheory.FinSupp f)
    (hf' : Work.Analysis.InverseTheory.FinSupp f') :
    Gpiece (kmtPj ρ) d u l s N (f + c • f') = Gpiece (kmtPj ρ) d u l s N f + c • Gpiece (kmtPj ρ) d u l s N f' := by
  simp only [Gpiece]
  exact piece_linear ρ l _ (-(u : ℤ)) s f f' c hf hf'

/-! ## Homogeneity of the halved average -/

private lemma Ablock_smul_left (m : ℕ) (P₁ P₂ : ℤ[X]) (c : ℂ) (f g : ℤ → ℂ) :
    Ablock TZ m P₁ P₂ (c • f) g = c • Ablock TZ m P₁ P₂ f g := by
  funext x
  simp only [Ablock, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

private lemma Ablock_smul_right (m : ℕ) (P₁ P₂ : ℤ[X]) (c : ℂ) (f g : ℤ → ℂ) :
    Ablock TZ m P₁ P₂ f (c • g) = c • Ablock TZ m P₁ P₂ f g := by
  funext x
  simp only [Ablock, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- Homogeneity of the halved average in the first argument. -/
private lemma AhalfR_smul_left (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (c : ℂ) (f g : ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ (c • f) g = c • AhalfR TZ N P₁ P₂ f g := by
  funext x
  rw [AhalfR_eq, Pi.smul_apply, AhalfR_eq, Ablock_smul_left]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- Homogeneity of the halved average in the second argument. -/
private lemma AhalfR_smul_right (N : ℝ≥0) (P₁ P₂ : ℤ[X]) (c : ℂ) (f g : ℤ → ℂ) :
    AhalfR TZ N P₁ P₂ f (c • g) = c • AhalfR TZ N P₁ P₂ f g := by
  funext x
  rw [AhalfR_eq, Pi.smul_apply, AhalfR_eq, Ablock_smul_right]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-! ## Bilinearity of the §5 summands -/

/-- Bilinearity of the unclamped summand `varpPiece` in its first argument. -/
private lemma varpPiece_linear_left (ρ : ℝ) (P : ℤ[X]) (d : ℕ) (N : ℝ≥0)
    (f f' g : ℤ → ℂ) (c : ℂ) (hf : Work.Analysis.InverseTheory.FinSupp f)
    (hf' : Work.Analysis.InverseTheory.FinSupp f') (l₁ l₂ k₁ k₂ : ℕ) :
    varpPiece (kmtPj ρ) P d N (f + c • f') g l₁ l₂ k₁ k₂
      = varpPiece (kmtPj ρ) P d N f g l₁ l₂ k₁ k₂
        + c • varpPiece (kmtPj ρ) P d N f' g l₁ l₂ k₁ k₂ := by
  simp only [varpPiece]
  rw [Fpiece_linear ρ 0 l₁ (k₁ : ℤ) (Nat.floor N) f f' c hf hf',
    AhalfR_add_left', AhalfR_smul_left]

/-- Bilinearity of the unclamped summand `varpPiece` in its second argument. -/
private lemma varpPiece_linear_right (ρ : ℝ) (P : ℤ[X]) (d : ℕ) (N : ℝ≥0)
    (f g g' : ℤ → ℂ) (c : ℂ) (hg : Work.Analysis.InverseTheory.FinSupp g)
    (hg' : Work.Analysis.InverseTheory.FinSupp g') (l₁ l₂ k₁ k₂ : ℕ) :
    varpPiece (kmtPj ρ) P d N f (g + c • g') l₁ l₂ k₁ k₂
      = varpPiece (kmtPj ρ) P d N f g l₁ l₂ k₁ k₂
        + c • varpPiece (kmtPj ρ) P d N f g' l₁ l₂ k₁ k₂ := by
  simp only [varpPiece]
  rw [Gpiece_linear ρ (d : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor N) g g' c hg hg',
    AhalfR_add_right', AhalfR_smul_right]

/-- Bilinearity of the clamped §5 column `varpCol` in its first argument.  The clamping
indicator does not depend on `f`. -/
private lemma varpCol_linear_left (ρ : ℝ) (P : ℤ[X]) (d C₀ : ℕ) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ : ℕ) (f f' g : ℤ → ℂ) (c : ℂ)
    (hf : Work.Analysis.InverseTheory.FinSupp f)
    (hf' : Work.Analysis.InverseTheory.FinSupp f') :
    varpCol (kmtPj ρ) P d C₀ a (f + c • f') g l₁ l₂ k₁ k₂
      = varpCol (kmtPj ρ) P d C₀ a f g l₁ l₂ k₁ k₂
        + c • varpCol (kmtPj ρ) P d C₀ a f' g l₁ l₂ k₁ k₂ := by
  funext n x
  simp only [varpCol_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
  · rw [if_pos h, if_pos h, if_pos h]
    rw [varpPiece_linear_left ρ P d (a n) f f' g c hf hf' l₁ l₂ k₁ k₂]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · rw [if_neg h, if_neg h, if_neg h]
    simp

/-- Bilinearity of the clamped §5 column `varpCol` in its second argument. -/
private lemma varpCol_linear_right (ρ : ℝ) (P : ℤ[X]) (d C₀ : ℕ) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ : ℕ) (f g g' : ℤ → ℂ) (c : ℂ)
    (hg : Work.Analysis.InverseTheory.FinSupp g)
    (hg' : Work.Analysis.InverseTheory.FinSupp g') :
    varpCol (kmtPj ρ) P d C₀ a f (g + c • g') l₁ l₂ k₁ k₂
      = varpCol (kmtPj ρ) P d C₀ a f g l₁ l₂ k₁ k₂
        + c • varpCol (kmtPj ρ) P d C₀ a f g' l₁ l₂ k₁ k₂ := by
  funext n x
  simp only [varpCol_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
  · rw [if_pos h, if_pos h, if_pos h]
    rw [varpPiece_linear_right ρ P d (a n) f g g' c hg hg' l₁ l₂ k₁ k₂]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · rw [if_neg h, if_neg h, if_neg h]
    simp

/-! ## The target -/

/-- **Bilinearity of the §5 columns `varpCol` on finitely supported inputs** (both arguments).
This is the bilinearity hypothesis that the interpolation lemma `VarBilinInterp` (area A8)
demands of the operator `T = varpCol (kmtPj ρ) P P.natDegree C₀ a · · l₁ l₂ s₁ s₂` in the
composition `exists_varEstHalfFin_Cv_of_areas`.

Proof route: unfold `varpCol`, `varpPiece`, `Fpiece`/`Gpiece`, `piece`, `piExact` — each is a
finite linear combination of the projections `kmtProj ρ l k` applied to `f` (resp. `g`), and the
clamping indicator `if inIndexSet … then _ else 0` does not depend on `f` or `g`; use
`Work.KMTContract.kmtProj_finsupp_linear` (already proved) for the projections and the bilinearity
lemmas `AhalfR_add_left'`, `AhalfR_add_right'` of `Work.Analysis.EndVar.VarpTools` for the halved
average (plus the corresponding `smul` lemmas, which may be proved in the same file). -/
theorem varpCol_finsupp_bilinear (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → NNReal)
    (l₁ l₂ s₁ s₂ : ℕ) :
    (∀ (f f' g : ℤ → ℂ) (c : ℂ),
      Work.Analysis.InverseTheory.FinSupp f → Work.Analysis.InverseTheory.FinSupp f' →
      (fun n x => Work.Analysis.EndVar.varpCol (Work.KMTContract.kmtPj ρ) P P.natDegree C₀ a
          (f + c • f') g l₁ l₂ s₁ s₂ n x)
        = fun n x => Work.Analysis.EndVar.varpCol (Work.KMTContract.kmtPj ρ) P P.natDegree C₀ a
              f g l₁ l₂ s₁ s₂ n x
            + c * Work.Analysis.EndVar.varpCol (Work.KMTContract.kmtPj ρ) P P.natDegree C₀ a
              f' g l₁ l₂ s₁ s₂ n x) ∧
    (∀ (f g g' : ℤ → ℂ) (c : ℂ),
      Work.Analysis.InverseTheory.FinSupp g → Work.Analysis.InverseTheory.FinSupp g' →
      (fun n x => Work.Analysis.EndVar.varpCol (Work.KMTContract.kmtPj ρ) P P.natDegree C₀ a
          f (g + c • g') l₁ l₂ s₁ s₂ n x)
        = fun n x => Work.Analysis.EndVar.varpCol (Work.KMTContract.kmtPj ρ) P P.natDegree C₀ a
              f g l₁ l₂ s₁ s₂ n x
            + c * Work.Analysis.EndVar.varpCol (Work.KMTContract.kmtPj ρ) P P.natDegree C₀ a
              f g' l₁ l₂ s₁ s₂ n x) := by
  constructor
  · intro f f' g c hf hf'
    rw [varpCol_linear_left ρ P P.natDegree C₀ a l₁ l₂ s₁ s₂ f f' g c hf hf']
    funext n x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  · intro f g g' c hg hg'
    rw [varpCol_linear_right ρ P P.natDegree C₀ a l₁ l₂ s₁ s₂ f g g' c hg hg']
    funext n x
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

end

end Work.KMTContract
