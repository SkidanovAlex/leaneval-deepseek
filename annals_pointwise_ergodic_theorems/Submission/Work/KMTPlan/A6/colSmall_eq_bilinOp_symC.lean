/-
# The clamped small-scale column is the bilinear operator with the symbol `symC`

This module proves `Work.KMTPlan.A6.colSmall_eq_bilinOp_symC`: on the admissible small-scale set
`lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n`, the clamped concrete column
`colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n` of the low case of area A6 is the bilinear convolution
operator (`Work.KMTAreas.A7.bilinOp`) whose kernel is the coefficient kernel
`coeff2 (symC ρ P ⌊a n⌋ l₁ l₂ k₁ k₂)` of the symbol
`Work.KMTPlan.A6.symC` — the product of the discrete symbol `halfSym ⌊a n⌋ P` of the halved
average `Ã_N` with the symbols of the two exact-height Ionescu--Wainger multipliers
`T^{l₁}_{φ_N}`, `T^{l₂}_{φ̃_N}` (`tmKer ρ l (varphiN N k₁)`,
`tmKer ρ l₂ (varphitildeN d N k₂)`).

## The proof

Everything is bookkeeping on explicit convolution kernels:

1. `colSmall = varpCol = varpPiece` on `lowSmallSet`
   (`colSmall_eq_varpCol_on`, `varpCol_eq_piece`), and `varpPiece` is by definition the halved
   average `Ã_N = AhalfR TZ (a n) X P` of the two §5 pieces (`Fpiece`, `Gpiece`) — hence
   `bilinOp (khalf ⌊a n⌋ P) (Fpiece …) (Gpiece …)` by `BilinOpKhalf`;
2. `Fpiece (kmtPj ρ) 0 l₁ k₁ N f = Tm ρ l₁ (pieceSymF k₁ N) f` and
   `Gpiece (kmtPj ρ) d 0 l₂ k₂ N g = Tm ρ l₂ (pieceSymG d k₂ N) g` for bounded `f`, `g`
   (`FpieceEqTm_of_bounded`, `GpieceEqTm_of_bounded`, `A7/FpieceEqTm.lean`,
   `A7/FpieceEqTmLq.lean`) — boundedness is exactly the hypothesis `BoundedZ f`, `BoundedZ g`
   available here;
3. `pieceSymF k N = varphiN N k` (`Work.KMTPlan.A6.varphiN_eq_pieceSymF`, a delegated lemma) and
   `pieceSymG d k N = varphitildeN d N k` (`cesb_varphitildeN_eq_pieceSymG` below), and
   `Tm ρ l φ u = convOp (tmKer ρ l φ) u` definitionally;
4. the composition of the bilinear convolution `bilinOp (khalf ⌊a n⌋ P)` with the two linear
   convolutions `convOp (tmKer …)` is the bilinear convolution with the composed kernel
   (`Work.A7.ModelApproxCore_kernelComp`, which needs the three kernels in `ℓ¹`:
   `cesb_summable_khalf`, and `cesb_summable_tmKer_varphiN` / `cesb_summable_tmKer_varphitildeN`,
   obtained from the decomposition of the bumps into differences of `etaCut`s and
   `summable_iwKernel_diffFreqs`);
5. `SymConc_coeff` identifies that composed kernel with `coeff2 (symC …)` — `symC` is *defined*
   as the corresponding product of the three sequence symbols.

The only symbolic ingredient is `cesb_tmKer_etaCut` (`tmKer ρ l (etaCut η c) = exactKer ρ l c`,
i.e. `Π_{l,≤c}` is the exact-height multiplier with symbol `η_{≤c}`), which is the additivity of
`iwKernel ∘ iwSymbolSet` in the *frequency set* (`iwKernel_iwSymbolSet_sdiff`,
`iwArithFreqs_mono`), plus the linearity `cesb_tmKer_sub_etaCut` in the symbol.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.SymConc_coeff
import Submission.Work.KMTPlan.A6.varphiN_eq_pieceSymF
import Submission.Work.KMTAreas.A7.BilinOpLp
import Submission.Work.KMTAreas.A7.FpieceEqTmLq
import Submission.Work.A7.ModelApproxCore_Fpiece_convOp
import Submission.Work.A7.ModelApproxCore_Gpiece_convOp
import Submission.Work.A7.ModelApproxCore_kernelComp

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract
open Work.KMTAreas.A7
open Work.Analysis.EndVar

/-! ## 1. Summability of the kernels of the concrete column -/

/-- The exact-height kernel `exactKer ρ l k` is absolutely summable (it is a finite difference of
`kmtKern`s, each of which decays like `j^{-2}`). -/
theorem cesb_summable_exactKer (ρ : ℝ) (l : ℕ) (k : ℤ) :
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
theorem cesb_summable_pieceKer (ρ : ℝ) (l : ℕ) (κs : ℤ → ℤ) (a s : ℤ) :
    Summable (fun j : ℤ => ‖pieceKer ρ l κs a s j‖) := by
  by_cases h : s = a
  · rw [pieceKer, if_pos h]
    exact cesb_summable_exactKer ρ l (κs s)
  · rw [pieceKer, if_neg h]
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      ((cesb_summable_exactKer ρ l (κs s)).add (cesb_summable_exactKer ρ l (κs (s - 1))))
    simp only [Pi.sub_apply]
    exact norm_sub_le _ _

/-- The kernel `khalf m P` of the halved average is finitely supported (on the integers
`m / 2 < a ≤ m`, with the second coordinate forced to be `P.eval a`), hence absolutely
summable. -/
theorem cesb_summable_khalf (m : ℕ) (P : ℤ[X]) :
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
      exact ⟨by omega, h2⟩
    · rw [h3]
  · rw [if_neg hc]
    simp

/-! ## 2. The exact-height multiplier with the cutoff symbol -/

/-- **The kernel of the exact-height Ionescu--Wainger multiplier with the cutoff symbol.**  The
multiplier `Tm ρ l (etaCut η c)` — whose symbol is `∑_{γ ∈ (ℚ/ℤ)_l} (periodize η_{≤c})(· - γ)` —
has the kernel `exactKer ρ l c` of the contract's exact-height projection
`Π_{l,≤c} = Π_{≤l,≤c} - Π_{≤l-1,≤c}`.  This is the additivity of `iwKernel ∘ iwSymbolSet` in
the frequency set (`iwSymbolSet_sdiff`) together with `diffFreqs ρ l = (ℚ/ℤ)_l`. -/
theorem cesb_tmKer_etaCut (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) (c : ℤ) :
    tmKer ρ l (etaCut kmtEta c) = exactKer ρ l c := by
  funext j
  rcases eq_or_ne l 0 with hl | hl
  · subst hl
    have hE : exactKer ρ 0 c = Work.KMTAreas.A5.kmtKern ρ 0 c := by rw [exactKer, if_pos rfl]
    have hD : diffFreqs ρ 0 = iwArithFreqs ρ 0 := by rw [diffFreqs, if_pos rfl]
    rw [hE]
    simp only [tmKer, hD]
  · have hne : l ≠ 0 := hl
    have hE : exactKer ρ l c
        = Work.KMTAreas.A5.kmtKern ρ l c - Work.KMTAreas.A5.kmtKern ρ (l - 1) c := by
      rw [exactKer, if_neg hne]
    have hD : diffFreqs ρ l = iwArithFreqs ρ l \ iwArithFreqs ρ (l - 1) := by
      rw [diffFreqs, if_neg hne]
    have hsub : iwArithFreqs ρ (l - 1) ⊆ iwArithFreqs ρ l :=
      iwArithFreqs_mono hρ hρ1 (Nat.pred_le l)
    have hA : Integrable (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta c)))
        circleMeasure :=
      (memLp_iwSymbolSet _ (Work.KMTAreas.A7.memLp_periodize_etaCut c)).integrable le_top
    have hB : Integrable (iwSymbolSet (iwArithFreqs ρ (l - 1)) (periodize (etaCut kmtEta c)))
        circleMeasure :=
      (memLp_iwSymbolSet _ (Work.KMTAreas.A7.memLp_periodize_etaCut c)).integrable le_top
    rw [hE]
    simp only [tmKer, hD]
    exact Work.KMTAreas.A7.iwKernel_iwSymbolSet_sdiff hsub hA hB j

/-- Linearity of `tmKer ρ l` in the symbol, over a difference of two rescaled cutoffs `etaCut`s
(`iwSymbolSet` is additive in the symbol and `periodize` is additive on differences of
`etaCut`s). -/
theorem cesb_tmKer_sub_etaCut (ρ : ℝ) (l : ℕ) (a b : ℤ) :
    tmKer ρ l (fun θ => etaCut kmtEta a θ - etaCut kmtEta b θ)
      = tmKer ρ l (etaCut kmtEta a) - tmKer ρ l (etaCut kmtEta b) := by
  funext j
  have hA : Integrable (iwSymbolSet (diffFreqs ρ l) (periodize (etaCut kmtEta a))) circleMeasure :=
    (memLp_iwSymbolSet _ (Work.KMTAreas.A7.memLp_periodize_etaCut a)).integrable le_top
  have hB : Integrable (iwSymbolSet (diffFreqs ρ l) (periodize (etaCut kmtEta b))) circleMeasure :=
    (memLp_iwSymbolSet _ (Work.KMTAreas.A7.memLp_periodize_etaCut b)).integrable le_top
  show iwKernel (iwSymbolSet (diffFreqs ρ l)
        (periodize (fun θ => etaCut kmtEta a θ - etaCut kmtEta b θ))) j
      = iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize (etaCut kmtEta a))) j
        - iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize (etaCut kmtEta b))) j
  rw [Work.KMTAreas.A7.periodize_sub_etaCut a b]
  exact Work.KMTAreas.A7.iwKernel_iwSymbolSet_sub hA hB j

/-! ## 3. The bumps as differences of `etaCut`s -/

/-- The bottom piece symbol at `s = 0`: the single cutoff at scale `-Log N`. -/
theorem cesb_pieceSymF_zero (N : ℕ) :
    pieceSymF 0 N = etaCut kmtEta (-(logN N)) := by
  funext ξ
  simp only [pieceSymF, if_true]

/-- The piece symbol away from the bottom scale: a difference of consecutive cutoffs. -/
theorem cesb_pieceSymF_ne (N k : ℕ) (hk : k ≠ 0) :
    pieceSymF k N = fun θ => etaCut kmtEta (-(logN N) + (k : ℤ)) θ
      - etaCut kmtEta (-(logN N) + (k : ℤ) - 1) θ := by
  funext θ
  simp only [pieceSymF, if_neg hk]

/-- The bottom `G`-piece symbol at `s = 0`. -/
theorem cesb_pieceSymG_zero (d : ℤ) (N : ℕ) :
    pieceSymG d 0 N = etaCut kmtEta (-(d * logN N)) := by
  funext ξ
  simp only [pieceSymG, if_true]

/-- The `G`-piece symbol away from the bottom scale. -/
theorem cesb_pieceSymG_ne (d : ℤ) (N k : ℕ) (hk : k ≠ 0) :
    pieceSymG d k N = fun θ => etaCut kmtEta (d * (-(logN N) + (k : ℤ))) θ
      - etaCut kmtEta (d * (-(logN N) + (k : ℤ) - 1)) θ := by
  funext θ
  simp only [pieceSymG, if_neg hk]

/-- `etaCut η m` is `η` precomposed with the scaling by the reciprocal integer power:
`etaCut η m ξ = η (2^{-m} ξ)`. -/
private lemma cesb_etaCut_eq_mul (η : ℝ → ℂ) (m : ℤ) (ξ : ℝ) :
    etaCut η m ξ = η ((2 : ℝ) ^ (-m) * ξ) := by
  have h : ξ / (2:ℝ) ^ m = (2:ℝ) ^ (-m) * ξ := by
    rw [div_eq_mul_inv, ← zpow_neg, mul_comm]
  simpa only [etaCut] using congrArg η h

/-- **The §6 bump `φ̃_N` is the §7 piece symbol `pieceSymG`** (the `G`-analogue of the delegated
`varphiN_eq_pieceSymF`): the paper's rescaled bump `η(2^{d(Log N-k)}·) - η(2^{d(Log N-k+1)}·)` is
the same function as the difference `etaCut η (d(-Log N + k)) - etaCut η (d(-Log N + k - 1))` of
cutoffs of the `G`-piece. -/
theorem cesb_varphitildeN_eq_pieceSymG (d N k : ℕ) :
    varphitildeN d N k = pieceSymG (d : ℤ) k N := by
  funext ξ
  by_cases hk : k = 0
  · simp only [varphitildeN, pieceSymG, if_pos hk]
    rw [cesb_etaCut_eq_mul, neg_neg]
    have hcast : (d:ℝ) * (logN N : ℝ) = (((d:ℤ) * logN N : ℤ) : ℝ) := by
      push_cast; ring
    rw [hcast, Real.rpow_intCast]
  · simp only [varphitildeN, pieceSymG, if_neg hk]
    have hp1 : (2:ℝ) ^ ((d:ℝ) * ((logN N : ℝ) - (k:ℝ)))
        = (2:ℝ) ^ (-((d:ℤ) * (-(logN N) + (k:ℤ)))) := by
      rw [← Real.rpow_intCast]
      congr 1
      push_cast
      ring
    have hp2 : (2:ℝ) ^ ((d:ℝ) * ((logN N : ℝ) - (k:ℝ) + 1))
        = (2:ℝ) ^ (-((d:ℤ) * (-(logN N) + (k:ℤ) - 1))) := by
      rw [← Real.rpow_intCast]
      congr 1
      push_cast
      ring
    simp only [cesb_etaCut_eq_mul, hp1, hp2]

/-! ## 4. Summability of the two Ionescu--Wainger factor kernels -/

/-- The kernel of `Tm ρ l (varphiN N k)` is absolutely summable: on the small scales it is a
finite difference of `ℓ¹` Ionescu--Wainger kernels. -/
theorem cesb_summable_tmKer_varphiN (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l N k : ℕ) :
    Summable (fun j : ℤ => ‖tmKer ρ l (varphiN N k) j‖) := by
  rw [varphiN_eq_pieceSymF N k]
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    rw [cesb_pieceSymF_zero N]
    simpa only [tmKer] using
      Work.KMTAreas.A7.summable_iwKernel_diffFreqs ρ hρ hρ1 l (-(logN N))
  · rw [cesb_pieceSymF_ne N k hk, cesb_tmKer_sub_etaCut]
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      ((Work.KMTAreas.A7.summable_iwKernel_diffFreqs ρ hρ hρ1 l (-(logN N) + (k:ℤ))).add
        (Work.KMTAreas.A7.summable_iwKernel_diffFreqs ρ hρ hρ1 l (-(logN N) + (k:ℤ) - 1)))
    simp only [Pi.sub_apply]
    exact norm_sub_le _ _

/-- The kernel of `Tm ρ l (varphitildeN d N k)` is absolutely summable. -/
theorem cesb_summable_tmKer_varphitildeN (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l d N k : ℕ) :
    Summable (fun j : ℤ => ‖tmKer ρ l (varphitildeN d N k) j‖) := by
  rw [cesb_varphitildeN_eq_pieceSymG d N k]
  rcases eq_or_ne k 0 with hk | hk
  · subst hk
    rw [cesb_pieceSymG_zero (d:ℤ) N]
    simpa only [tmKer] using
      Work.KMTAreas.A7.summable_iwKernel_diffFreqs ρ hρ hρ1 l (-((d:ℤ) * logN N))
  · rw [cesb_pieceSymG_ne (d:ℤ) N k hk, cesb_tmKer_sub_etaCut]
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      ((Work.KMTAreas.A7.summable_iwKernel_diffFreqs ρ hρ hρ1 l ((d:ℤ) * (-(logN N) + (k:ℤ)))).add
        (Work.KMTAreas.A7.summable_iwKernel_diffFreqs ρ hρ hρ1 l
          ((d:ℤ) * (-(logN N) + (k:ℤ) - 1))))
    simp only [Pi.sub_apply]
    exact norm_sub_le _ _

/-! ## 5. The clamped column as a bilinear convolution -/

/-- On the admissible small-scale set, the clamped concrete column is the bilinear convolution
with the composed kernel of the halved average and the two Ionescu--Wainger factor kernels
`tmKer ρ l₁ (varphiN ⌊a n⌋ k₁)`, `tmKer ρ l₂ (varphitildeN P.natDegree ⌊a n⌋ k₂)`. -/
theorem cesb_colSmall_eq_bilinOp_kernComp (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (P : ℤ[X]) (C₀ : ℕ) (a : ℕ → ℝ≥0) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ)
    (hf : Work.KMTAreas.A5.BoundedZ f) (hg : Work.KMTAreas.A5.BoundedZ g)
    (h : lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n) :
    colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      = bilinOp (kernComp (khalf (Nat.floor (a n)) P)
          (tmKer ρ l₁ (varphiN (Nat.floor (a n)) k₁))
          (tmKer ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) k₂))) f g x := by
  rw [colSmall_eq_varpCol_on ρ P C₀ a f g l₁ l₂ k₁ k₂ n x h,
    Work.Analysis.EndVar.varpCol_eq_piece (Pj := kmtPj ρ) (P := P) (d := P.natDegree)
      (C₀ := C₀) (a := a) (f := f) (g := g) (l₁ := l₁) (l₂ := l₂) (k₁ := k₁) (k₂ := k₂)
      (n := n) (x := x) (Work.Analysis.EndVar.inIndexSet_iff_le.mp h.1)]
  rw [show varpPiece (kmtPj ρ) P P.natDegree (a n) f g l₁ l₂ k₁ k₂ x
      = AhalfR TZ (a n) X P (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) (Nat.floor (a n)) f)
          (Gpiece (kmtPj ρ) (P.natDegree : ℤ) 0 l₂ (k₂ : ℤ) (Nat.floor (a n)) g) x from rfl,
    BilinOpKhalf (a n) P]
  rw [Work.KMTAreas.A7.FpieceEqTm_of_bounded (ρ := ρ) hρ hρ1 l₁ k₁ (Nat.floor (a n)) f
      hf.choose_spec,
    Work.KMTAreas.A7.GpieceEqTm_of_bounded (ρ := ρ) hρ hρ1 (P.natDegree : ℤ) l₂ k₂
      (Nat.floor (a n)) g hg.choose_spec,
    ← varphiN_eq_pieceSymF (Nat.floor (a n)) k₁,
    ← cesb_varphitildeN_eq_pieceSymG P.natDegree (Nat.floor (a n)) k₂]
  rw [Tm_eq_convOp, Tm_eq_convOp]
  exact (Work.A7.ModelApproxCore_kernelComp (K := khalf (Nat.floor (a n)) P)
      (κ := tmKer ρ l₁ (varphiN (Nat.floor (a n)) k₁))
      (κ' := tmKer ρ l₂ (varphitildeN P.natDegree (Nat.floor (a n)) k₂))
      (cesb_summable_khalf _ _) (cesb_summable_tmKer_varphiN ρ hρ hρ1 l₁ _ k₁)
      (cesb_summable_tmKer_varphitildeN ρ hρ hρ1 l₂ P.natDegree (Nat.floor (a n)) k₂)
      hf.choose_spec hg.choose_spec x).symm

/-! ## 6. The coefficient kernel of `symC` -/

/-- The composed kernel is the coefficient kernel of `symC`: this is `SymConc_coeff`, the product
form of the symbol dictionary, with the two factor kernels `tmKer` of `symC`. -/
theorem cesb_kernComp_eq_coeff2_symC (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : ℤ[X])
    (l₁ l₂ k₁ k₂ N : ℕ) :
    kernComp (khalf N P) (tmKer ρ l₁ (varphiN N k₁)) (tmKer ρ l₂ (varphitildeN P.natDegree N k₂))
      = coeff2 (symC ρ P N l₁ l₂ k₁ k₂) := by
  funext i j
  rw [SymConc_coeff (tmKer ρ l₁ (varphiN N k₁)) (tmKer ρ l₂ (varphitildeN P.natDegree N k₂))
      (cesb_summable_tmKer_varphiN ρ hρ hρ1 l₁ N k₁).of_norm
      (cesb_summable_tmKer_varphitildeN ρ hρ hρ1 l₂ P.natDegree N k₂).of_norm N P i j]
  rfl

/-! ## 7. The target -/

theorem colSmall_eq_bilinOp_symC (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (C₀ : ℕ)
    (a : ℕ → NNReal) (f g : ℤ → ℂ) (l₁ l₂ k₁ k₂ n : ℕ) (x : ℤ)
    (hf : Work.KMTAreas.A5.BoundedZ f) (hg : Work.KMTAreas.A5.BoundedZ g)
    (h : Work.KMTPlan.A6.lowSmallSet ρ C₀ a l₁ l₂ k₁ k₂ n) :
    Work.KMTPlan.A6.colSmall ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      = Work.KMTAreas.A7.bilinOp
          (fun u v => Work.KMTPlan.A6.coeff2
            (Work.KMTPlan.A6.symC ρ P (Nat.floor (a n)) l₁ l₂ k₁ k₂) u v) f g x := by
  rw [cesb_colSmall_eq_bilinOp_kernComp ρ hρ hρ1 P C₀ a f g l₁ l₂ k₁ k₂ n x hf hg h,
    cesb_kernComp_eq_coeff2_symC ρ hρ hρ1 P l₁ l₂ k₁ k₂ (Nat.floor (a n))]

end

end Work.KMTPlan.A6
