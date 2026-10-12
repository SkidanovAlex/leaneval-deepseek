import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.L1Tails.chiChiCoulAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowDirDefs` — the Dirichlet interface of step (S2) of the `Q₂` row

Step (S2) of `FINDING_PotPairRows_exists.md` replaces the truncated pair kernel `K1exp` by its
limit `K1lim` (and then strips the lattice images `chiChiImages`, resp. compares with the word
kernels `wLoc`).  The pairing estimate available for that substitution is **not** of
`L²`/`L^∞`-kernel type at the honest weights (`W₁ = W1fun` is only `L¹`, cf. §9.2/§9.13 of the
FINDING): both proved tails,

* the `χχ`-row (`Work.BoseBoxFock.L1Tails.kernelTail`, T6), and
* the images row (`Work.BoseBoxFock.L1Tails.chiChiImages_pairing_coul`, T7),

are stated for a **smooth, box²-supported test function** `H` and bound the pairing by the
*Dirichlet energy*

    pairEnergy ℓ H = ∫_{box}∫_{box} (Σ_j ‖∂_{w_j}(χ_ℓ w · H w y)‖² + ℓ⁻²‖χ_ℓ w · H w y‖²)

(see `Work.BoseBoxFock.L1Tails.pairEnergy`).

The test functions that actually occur in (S2) are the *fibres* of the row
(`Work.BoseBoxFock.pairG13/pairG23/pairG21`), and these are **not** smooth at the honest state:
the state factor is `boxRestrictC ℓ Φ = Φ·1_{abox}` and the condensate pin is
`pinCond v μ c = c·1_{boxL}`, so the fibre carries the sharp box indicators of the state.

The repair — and the reason this module exists — is that the pairings only see the fibre **on the
box squared** (`K1exp`/`K1lim` are supported in `boxL ℓ × boxL ℓ`, each of their four terms carrying
a `χ_ℓ`- or `θ_Λ`-factor in each variable), and on the box the indicators of the state are `1`:
`closedBall 0 (ℓ/2) ⊆ acube ℓ = boxL ℓ`.  Hence it suffices to ask that the fibre *agrees on the box
squared with a smooth function*, which is exactly the predicate

    BoxSmooth ℓ G  :=  ∃ G', ContDiff ℝ ⊤ (uncurry G') ∧ ∀ w y, w ∈ boxL ℓ → y ∈ boxL ℓ → G' w y = G w y

(for the honest fibre `G'` is the *box-restricted* parameter integral, smooth by differentiation
under the integral over the fixed compact box).  This module fixes that vocabulary and proves the
transport lemmas that make it usable:

* `pairEnergy_congr_box` — `BoxSmooth`-style equality on the box squared preserves the Dirichlet
  energy (the `χ`-weight kills everything outside the box, and `χ` vanishes off the box);
* `setIntegral_pairing_congr_box` — the box-squared pairing is unchanged.

`sorry`-free.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-! ## 1. The window vanishes off the box -/

/-- The closed ball of radius `ℓ/2` sits in the centred cube: `‖w‖ < ℓ/2 → w ∈ boxL ℓ`. -/
theorem mem_boxL_of_norm_lt {ℓ : ℝ} (hℓ : 0 < ℓ) {w : E3} (hw : ‖w‖ < ℓ / 2) :
    w ∈ Work.BoseK15.corpusBox.boxL ℓ := by
  rw [Work.BoseBoxFock.corpusBox_boxL_eq_acube hℓ, Submission.BoseGases.mem_acube_iff]
  intro i
  rw [Set.mem_Icc]
  have h1 : ‖w i‖ ≤ ‖w‖ := PiLp.norm_apply_le w i
  rw [Real.norm_eq_abs] at h1
  have h2 := abs_le.mp h1
  constructor <;> linarith [h2.1, h2.2]

/-- `chiScale ℓ` is supported in the centred cube `boxL ℓ = acube ℓ`. -/
theorem chiScale_eq_zero_of_notMem_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) {w : E3}
    (hw : w ∉ Work.BoseK15.corpusBox.boxL ℓ) : Submission.BoseGases.chiScale ℓ w = 0 := by
  by_contra hne
  exact hw (mem_boxL_of_norm_lt hℓ ((Work.BoseFixB1.chiScale_ne_zero_iff hℓ w).1 hne))

/-! ## 2. The test-function classes -/

/-- **The test-function class of the (S2) pairing**: `G` agrees on the box squared with a smooth
function.  `K1exp − K1lim` is supported in the box squared, and all the pairings are integrals over
the box squared, so only the restriction of `G` to `boxL ℓ × boxL ℓ` matters. -/
def BoxSmooth (ℓ : ℝ) (G : E3 → E3 → ℂ) : Prop :=
  ∃ G' : E3 → E3 → ℂ, ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G') ∧
    ∀ w y, w ∈ Work.BoseK15.corpusBox.boxL ℓ → y ∈ Work.BoseK15.corpusBox.boxL ℓ →
      G' w y = G w y

/-- **The `n`-body "smooth cut by the box indicator"** form of the state pin: `f` is a `C^∞`
function times the indicator of `abox n ℓ`.  (`boxRestrictC ℓ Φ` is of this shape.) -/
def CutSmooth {n : ℕ} (ℓ : ℝ) (f : Xn n → ℂ) : Prop :=
  ∃ f₀ : Xn n → ℂ, ContDiff ℝ (⊤ : ℕ∞) f₀ ∧
    ∀ x, f x = Set.indicator (Submission.BoseGases.abox n ℓ) f₀ x

/-- **The one-particle "smooth cut by the box indicator"**: `pinCond v μ c = c·thetaFun ℓ` is of
this shape. -/
def CutSmooth1 (ℓ : ℝ) (f : E3 → ℂ) : Prop :=
  ∃ f₀ : E3 → ℂ, ContDiff ℝ (⊤ : ℕ∞) f₀ ∧
    ∀ x, f x = Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) f₀ x

/-- The pinned condensate `pinCond v μ c = c·thetaFun (ellH v μ)` is a `CutSmooth1`. -/
theorem cutSmooth1_pinCond (v : E3 → ℝ) (μ : ℝ) (c : ℂ) :
    CutSmooth1 (ellH v μ) (pinCond v μ c) := by
  refine ⟨fun _ => c, contDiff_const, fun x => ?_⟩
  simp only [pinCond, Work.BoseB4.BoxData.thetaFun_apply]
  by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
  · rw [if_pos hx, Set.indicator_of_mem hx, mul_one]
  · rw [if_neg hx, Set.indicator_of_notMem hx, mul_zero]

/-! ## 3. Transport lemmas -/

/-- **The Dirichlet energy only depends on the restriction to the box squared.**  If `G'` and `G`
agree on `boxL ℓ × boxL ℓ` then `pairEnergy ℓ G' = pairEnergy ℓ G`: inside the box the two
integrands agree pointwise (the `χ_ℓ`-weighted functions are literally equal, since `χ_ℓ` vanishes
off the box), and both set integrals are over the box. -/
theorem pairEnergy_congr_box {ℓ : ℝ} (hℓ : 0 < ℓ) {G G' : E3 → E3 → ℂ}
    (h : ∀ w y, w ∈ Work.BoseK15.corpusBox.boxL ℓ → y ∈ Work.BoseK15.corpusBox.boxL ℓ →
      G' w y = G w y) :
    Work.BoseBoxFock.L1Tails.pairEnergy ℓ G' = Work.BoseBoxFock.L1Tails.pairEnergy ℓ G := by
  unfold Work.BoseBoxFock.L1Tails.pairEnergy
  refine MeasureTheory.setIntegral_congr_fun
    (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun w hw => ?_)
  refine MeasureTheory.setIntegral_congr_fun
    (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun y hy => ?_)
  have hfun : (fun w' : E3 => ((Submission.BoseGases.chiScale ℓ w' : ℝ) : ℂ) * G' w' y)
      = (fun w' : E3 => ((Submission.BoseGases.chiScale ℓ w' : ℝ) : ℂ) * G w' y) := by
    funext w'
    by_cases hw' : w' ∈ Work.BoseK15.corpusBox.boxL ℓ
    · rw [h w' y hw' hy]
    · rw [chiScale_eq_zero_of_notMem_boxL hℓ hw']
      simp
  have hmass : ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) * G' w y
      = ((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ) * G w y := by
    by_cases hw' : w ∈ Work.BoseK15.corpusBox.boxL ℓ
    · rw [h w y hw' hy]
    · rw [chiScale_eq_zero_of_notMem_boxL hℓ hw']
      simp
  rw [hfun, hmass]

/-- **The box-squared pairing only depends on the restriction to the box squared.** -/
theorem setIntegral_pairing_congr_box {ℓ : ℝ} {K G G' : E3 → E3 → ℂ}
    (h : ∀ w y, w ∈ Work.BoseK15.corpusBox.boxL ℓ → y ∈ Work.BoseK15.corpusBox.boxL ℓ →
      G' w y = G w y) :
    (∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
        K w y * G' w y)
      = ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ,
          K w y * G w y := by
  refine MeasureTheory.setIntegral_congr_fun
    (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun w hw => ?_)
  refine MeasureTheory.setIntegral_congr_fun
    (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun y hy => ?_)
  rw [h w y hw hy]

/-- **The box-squared mass** of a test function: the second term of the (S2) pairing estimate.  It is
needed because the `θ_Λθ_Λ`-row of `K1exp − K1lim` is the *constant* `(ℓ³)⁻¹(pinQD(c) − pinQDl)`
multiplied by the sharp box indicators: on the box *corners* (`‖w‖ > ℓ/2`, where `χ_ℓ` vanishes
everywhere in a neighbourhood but `θ_Λ = 1`) the kernel difference does not vanish although
`pairEnergy` is blind to it, so the Dirichlet term alone cannot control that row (refuted by the
prover of `K1exp_sub_K1lim_pairing_dir`, session 10).  The `χθ`/`θχ` rows and the `χχ`/images rows are
controlled by `pairEnergy` alone. -/
noncomputable def massBox (ℓ : ℝ) (G : E3 → E3 → ℂ) : ℝ :=
  ∫ w in Work.BoseK15.corpusBox.boxL ℓ, ∫ y in Work.BoseK15.corpusBox.boxL ℓ, ‖G w y‖ ^ 2

/-- **The box-squared mass only depends on the restriction to the box squared.** -/
theorem massBox_congr_box {ℓ : ℝ} {G G' : E3 → E3 → ℂ}
    (h : ∀ w y, w ∈ Work.BoseK15.corpusBox.boxL ℓ → y ∈ Work.BoseK15.corpusBox.boxL ℓ →
      G' w y = G w y) :
    massBox ℓ G' = massBox ℓ G := by
  unfold massBox
  refine MeasureTheory.setIntegral_congr_fun
    (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun w hw => ?_)
  refine MeasureTheory.setIntegral_congr_fun
    (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ) (fun y hy => ?_)
  rw [h w y hw hy]

/-- The direction vector of the *slot*-`i`, coordinate-`j` derivative on `Xn n`. -/
noncomputable def slotDirVec {n : ℕ} (i : Fin n) (j : Fin 3) : Xn n :=
  Function.update (0 : Xn n) i (EuclideanSpace.single j (1 : ℝ))

/-- **The `L²` content of a state pin on the box** `∫_{abox n ℓ}‖Θ‖²` (the value of `normB` for the
honest pin `Θ = boxRestrictC ℓ Φ`). -/
noncomputable def pinL2 {n : ℕ} (ℓ : ℝ) (Θ : Xn n → ℂ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ, ‖Θ x‖ ^ 2

/-- **The one-slot Dirichlet content of a state pin** `Σ_{i,j}∫_{abox n ℓ}‖∂_{i,j}Θ‖²`: the
quantity that bounds the *derivative* of the row's fibres, and that `IsLowB` controls through
`kinFormB ≤ 12πaμ²ℓ³‖Φ‖²`.  (This is the state-dependent factor of the corrected `D2` of
`FINDING_PotPairRows_exists.md` §10; note the fibre's Dirichlet involves the *product*
`pinL2 · (pinDir + pinL2)`, i.e. the two state factors are separated by Cauchy–Schwarz, so no
`∂Θ·Θ` — and no sup norm of the state — appears.) -/
noncomputable def pinDir {n : ℕ} (ℓ : ℝ) (Θ : Xn n → ℂ) : ℝ :=
  ∫ x in Submission.BoseGases.abox n ℓ, ∑ i : Fin n, ∑ j : Fin 3,
    ‖fderiv ℝ Θ x (slotDirVec i j)‖ ^ 2

/-- The box-squared mass is nonnegative. -/
theorem massBox_nonneg (ℓ : ℝ) (G : E3 → E3 → ℂ) : 0 ≤ massBox ℓ G := by
  unfold massBox
  exact integral_nonneg fun w => integral_nonneg fun y => by positivity

end Work.BoseBoxFock
