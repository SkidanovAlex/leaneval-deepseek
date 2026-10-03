/-
# The kernels of the §6 model approximation (Area A7, `ModelApproxHi`)

Continuation of `ModelApproxHiDefs`: the identification of the two kernels with the concrete
column and with the §6 model operator, and the auxiliary computations feeding the `crude-mult`
estimate.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxHiDefs
import Submission.Work.KMTAreas.A7.FpieceEqTmLq

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.EndVar Work.Analysis.IWMultiplier
open Work.KMTContract

/-! ## The `delta` function and the extraction of a kernel from its operator -/

/-- The Kronecker delta at `0` on `ℤ`. -/
noncomputable def deltaZ : ℤ → ℂ := fun z => if z = 0 then 1 else 0

theorem boundedZ_deltaZ : Work.KMTAreas.A5.BoundedZ deltaZ :=
  ⟨1, by intro z; simp only [deltaZ]; split_ifs <;> simp⟩

/-- **The kernel is recovered from its convolution operator.** -/
theorem convOp_deltaZ (κ : ℤ → ℂ) : convOp κ deltaZ = κ := by
  funext x
  rw [convOp, tsum_eq_single x]
  · simp [deltaZ]
  · intro j hj
    simp only [deltaZ]
    rw [if_neg]
    · ring
    · rintro h
      exact hj (by omega)

/-! ## The two kernels are the exact-height kernels of the bumps -/

/-- `iwConv (diffFreqs ρ l) (periodize φ)` is the convolution with `hiKer ρ l φ`. -/
theorem iwConv_diffFreqs_eq_convOp_hiKer (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (f : ℤ → ℂ) :
    iwConv (diffFreqs ρ l) (periodize φ) f = convOp (hiKer ρ l φ) f := by
  funext n
  rw [iwConv_apply, convOp]
  refine tsum_congr (fun j => ?_)
  rw [smul_eq_mul]
  rfl

/-- `Tm ρ l φ` is the convolution with `hiKer ρ l φ`. -/
theorem Tm_eq_convOp_hiKer (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (f : ℤ → ℂ) :
    Tm ρ l φ f = convOp (hiKer ρ l φ) f :=
  iwConv_diffFreqs_eq_convOp_hiKer ρ l φ f

/-- The §5 window `pieceSymF k N` is the §6 bump `varphiN N k`. -/
theorem pieceSymF_eq_varphiN (k N : ℕ) : pieceSymF k N = varphiN N k := by
  funext ξ
  have key2 : ∀ a : ℤ, ((2:ℝ) ^ a)⁻¹ = (2:ℝ) ^ ((↑(-a) : ℝ)) := by
    intro a
    rw [Real.rpow_intCast, zpow_neg]
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    rw [pieceSymF, varphiN, if_pos rfl, if_pos rfl]
    simp only [etaCut, div_eq_mul_inv]
    rw [key2 (-(logN N))]
    congr 1
    push_cast
    ring
  · have hk' : ¬ (k = 0) := hk
    rw [pieceSymF, varphiN, if_neg hk', if_neg hk']
    simp only [etaCut, div_eq_mul_inv]
    rw [key2 (-(logN N) + (k:ℤ)), key2 (-(logN N) + (k:ℤ) - 1)]
    congr 1
    · push_cast; ring
    · push_cast; ring

/-- **The exact-height kernel of the window bump `varphiN N k`** is the `pieceKer` of the §5
piece. -/
theorem pieceKer_eq_hiKer (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l k N : ℕ) :
    pieceKer ρ l (fun s : ℤ => -(logN N) + s) 0 (k : ℤ) = hiKer ρ l (varphiN N k) := by
  have h : convOp (pieceKer ρ l (fun s : ℤ => -(logN N) + s) 0 (k : ℤ)) deltaZ
      = convOp (hiKer ρ l (varphiN N k)) deltaZ := by
    rw [← Work.A7.ModelApproxCore_Fpiece_convOp ρ l k N boundedZ_deltaZ,
      FpieceEqTm_of_bounded hρ hρ1 l k N deltaZ boundedZ_deltaZ.choose_spec,
      Tm_eq_convOp_hiKer, pieceSymF_eq_varphiN]
  rwa [convOp_deltaZ, convOp_deltaZ] at h


/-- The §5 window `pieceSymG d k N` is the §6 bump `varphitildeN d N k`. -/
theorem pieceSymG_eq_varphitildeN (d k N : ℕ) : pieceSymG (d : ℤ) k N = varphitildeN d N k := by
  funext ξ
  have key2 : ∀ a : ℤ, ((2:ℝ) ^ a)⁻¹ = (2:ℝ) ^ ((↑(-a) : ℝ)) := by
    intro a
    rw [Real.rpow_intCast, zpow_neg]
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    rw [pieceSymG, varphitildeN, if_pos rfl, if_pos rfl]
    simp only [etaCut, div_eq_mul_inv]
    rw [key2 (-((d:ℤ) * logN N))]
    congr 1
    push_cast
    ring
  · rw [pieceSymG, varphitildeN, if_neg hk, if_neg hk]
    simp only [etaCut, div_eq_mul_inv]
    rw [key2 ((d:ℤ) * (-(logN N) + (k:ℤ))), key2 ((d:ℤ) * (-(logN N) + (k:ℤ) - 1))]
    congr 1
    · push_cast; ring
    · push_cast; ring

/-- **The exact-height kernel of the window bump `varphitildeN d N k`** is the `pieceKer` of the
§5 `G` piece. -/
theorem pieceKerG_eq_hiKer (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (d l k N : ℕ) :
    pieceKer ρ l (fun s : ℤ => (d:ℤ) * (-(logN N) + s)) 0 (k : ℤ)
      = hiKer ρ l (varphitildeN d N k) := by
  have h : convOp (pieceKer ρ l (fun s : ℤ => (d:ℤ) * (-(logN N) + s)) 0 (k : ℤ)) deltaZ
      = convOp (hiKer ρ l (varphitildeN d N k)) deltaZ := by
    rw [← Work.A7.ModelApproxCore_Gpiece_convOp ρ d l k N boundedZ_deltaZ,
      GpieceEqTm_of_bounded hρ hρ1 (d:ℤ) l k N deltaZ boundedZ_deltaZ.choose_spec,
      Tm_eq_convOp_hiKer, pieceSymG_eq_varphitildeN]
  rwa [convOp_deltaZ, convOp_deltaZ] at h

/-! ## The scale-parameterised kernels

The two kernels of `ModelApproxHiDefs` only depend on the scale `N = ⌊a n⌋`; these versions make
that explicit, so that the fibre identities can be stated for an arbitrary `N : ℕ`. -/

/-- The concrete kernel at the integer scale `N`, in the exact-height form. -/
noncomputable def hiKconcN (ρ : ℝ) (P : ℤ[X]) (N : ℕ) (l₁ l₂ k₁ k₂ : ℕ) : ℤ → ℤ → ℂ :=
  kernComp (khalf N P) (hiKer ρ l₁ (varphiN N k₁)) (hiKer ρ l₂ (varphitildeN P.natDegree N k₂))

/-- The concrete kernel of `hiKconcDefs` at `N = ⌊a n⌋`. -/
theorem hiKconc_eq (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : ℤ[X]) (a : ℕ → NNReal)
    (l₁ l₂ k₁ k₂ n : ℕ) :
    hiKconc ρ P a l₁ l₂ k₁ k₂ n = hiKconcN ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂ := by
  unfold hiKconc hiKconcN
  rw [pieceKer_eq_hiKer ρ hρ hρ1 l₁ k₁ (Nat.floor (a n)),
    pieceKerG_eq_hiKer ρ hρ hρ1 P.natDegree l₂ k₂ (Nat.floor (a n))]

/-- The model kernel at the integer scale `N`. -/
noncomputable def hiKmodN (ρ : ℝ) (P : ℤ[X]) (N : ℕ) (l₁ l₂ k₁ k₂ : ℕ) : ℤ → ℤ → ℂ :=
  fun j₁ j₂ => ∫ t in (1/2 : ℝ)..1,
    kernComp (hiTwKernel ρ P l₁ l₂
        (mStarF (uScale ρ (max (max l₁ l₂) (max k₁ k₂))))
        (mStargF P.natDegree (uScale ρ (max (max l₁ l₂) (max k₁ k₂)))))
      (hiKer ρ l₁ (varphiNt N k₁ t))
      (hiKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) j₁ j₂

/-- The model kernel of `ModelApproxHiDefs` at `N = ⌊a n⌋`. -/
theorem hiKmod_eq (ρ : ℝ) (P : ℤ[X]) (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ n : ℕ) :
    hiKmod ρ P a l₁ l₂ k₁ k₂ n = hiKmodN ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂ := rfl

end
end Work.KMTAreas.A7
