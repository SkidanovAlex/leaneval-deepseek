import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.LC_setup
import Submission.Work.A14D.LC_A_defs
import Submission.Work.A14D.jumpI_defs
import Submission.Work.A14D.om1_geometry
import Submission.Work.A14D.primSeg_hasDerivAt

/-!
# `Work.A14D.jump_I_ident` — the jump identity for the three integral slots

The `SU`-branch `BUi a b c HU HL i` of the `i`-th integral slot is the primitive, based at `cSU`,
of the integrand `jIntU = y'·y^{−i}·((HU + HL∘wC) − jets)`; the jump `JFI D i` is the primitive,
based at the same point, of `jIntJ = y'·y^{−i}·(D − D∘wC)`.  Because the deck involution
`wC z = z/(z−1)` leaves the half-plane intersection `SU ∩ SL` invariant, the difference

  `PhiI = (BUi − BUi∘wC) − JFI`

has *zero derivative* on `SU ∩ SL`: the chain rule together with `yC∘wC = yC` turns the
`wC`-pullback of the `BUi`-derivative into `y'·y^{−i}·((HU∘wC + HL) − jets)`, and on the wedge
`D = HU − HL` by hypothesis, so everything cancels.  As `SU ∩ SL` is convex (hence preconnected)
and `PhiI` vanishes at the interior point `cWedge = 3 + i/10` by definition of `JFIc`, the identity

  `JFIc a b c HU HL D i z = BUi a b c HU HL i z − BUi a b c HU HL i (wC z)`

holds on all of `SU ∩ SL`.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology BigOperators

noncomputable section

/-! ## 1. Elementary geometry of the deck involution on `SU`, `SL`, `SU ∩ SL` -/

private lemma wC_inv_local {z : ℂ} (hz : z ≠ 1) : wC (wC z) = z := by
  simp only [wC]
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  ring

private lemma wC_sub_one_local {z : ℂ} (hz : z ≠ 1) : wC z - 1 = (z - 1)⁻¹ := by
  simp only [wC]
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  field_simp
  ring

private lemma yC_wC_local {z : ℂ} (hz : z ≠ 1) : yC (wC z) = yC z := by
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have hw1 : z / (z - 1) - 1 ≠ 0 := by
    have h : wC z - 1 ≠ 0 := by
      rw [wC_sub_one_local hz]
      exact inv_ne_zero hz1
    simpa only [wC] using h
  simp only [yC, wC]
  field_simp
  ring

private lemma one_notMem_SU_local : (1 : ℂ) ∉ SU := by
  rw [mem_SU_iff]
  norm_num

private lemma zero_notMem_SU_local : (0 : ℂ) ∉ SU := by
  rw [mem_SU_iff]
  norm_num

private lemma z_ne_one_of_mem_SU_local {z : ℂ} (hz : z ∈ SU) : z ≠ 1 := by
  intro h
  rw [h] at hz
  exact one_notMem_SU_local hz

/-- The real and imaginary parts of `wC z = 1 + (z−1)⁻¹`. -/
private lemma wC_re_im_local {z : ℂ} (hz : z ≠ 1) :
    (wC z).re = 1 + (z.re - 1) / Complex.normSq (z - 1) ∧
      (wC z).im = -(z.im) / Complex.normSq (z - 1) := by
  have hw : wC z = 1 + (z - 1)⁻¹ := by
    have h := wC_sub_one_local hz
    rw [← h]
    ring
  constructor
  · rw [hw]
    simp only [Complex.add_re, Complex.one_re, Complex.inv_re, Complex.sub_re]
    try ring
  · rw [hw]
    simp only [Complex.add_im, Complex.one_im, Complex.inv_im, Complex.sub_im]
    try ring

/-- `wC` maps the half plane `SU` into `SL`. -/
private lemma wC_mem_SL_of_mem_SU_local {z : ℂ} (hz : z ∈ SU) : wC z ∈ SL := by
  have hz1 : z ≠ 1 := z_ne_one_of_mem_SU_local hz
  have hz' : 1 < 8 * z.im + z.re := mem_SU_iff.mp hz
  have hN : 0 < Complex.normSq (z - 1) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hz1)
  have hNne : Complex.normSq (z - 1) ≠ 0 := ne_of_gt hN
  obtain ⟨hr, hi⟩ := wC_re_im_local hz1
  rw [mem_SL_iff, ← sub_pos]
  have hkey : (wC z).re - (8 * (wC z).im + 1)
      = (8 * z.im + z.re - 1) / Complex.normSq (z - 1) := by
    rw [hr, hi]
    field_simp
    ring
  rw [hkey, div_pos_iff_of_pos_right hN]
  linarith

/-- `wC` maps the wedge `SU ∩ SL` into itself. -/
private lemma wC_mem_wedge_local {z : ℂ} (hz : z ∈ SU ∩ SL) : wC z ∈ SU ∩ SL := by
  have hz1 : z ≠ 1 := z_ne_one_of_mem_SU_local hz.1
  have hzU : 1 < 8 * z.im + z.re := mem_SU_iff.mp hz.1
  have hzL : 8 * z.im + 1 < z.re := mem_SL_iff.mp hz.2
  have hN : 0 < Complex.normSq (z - 1) := Complex.normSq_pos.mpr (sub_ne_zero.mpr hz1)
  have hNne : Complex.normSq (z - 1) ≠ 0 := ne_of_gt hN
  obtain ⟨hr, hi⟩ := wC_re_im_local hz1
  constructor
  · rw [mem_SU_iff, ← sub_pos]
    have hkey : 8 * (wC z).im + (wC z).re - 1
        = (z.re - 1 - 8 * z.im) / Complex.normSq (z - 1) := by
      rw [hr, hi]
      field_simp
      ring
    rw [hkey, div_pos_iff_of_pos_right hN]
    linarith
  · rw [mem_SL_iff, ← sub_pos]
    have hkey : (wC z).re - (8 * (wC z).im + 1)
        = (z.re - 1 + 8 * z.im) / Complex.normSq (z - 1) := by
      rw [hr, hi]
      field_simp
      ring
    rw [hkey, div_pos_iff_of_pos_right hN]
    linarith

private lemma cSU_mem_SU_local : cSU ∈ SU := by
  rw [mem_SU_iff]
  norm_num [cSU]

private lemma cWedge_mem_wedge_local : cWedge ∈ SU ∩ SL := by
  constructor
  · rw [mem_SU_iff]
    norm_num [cWedge]
  · rw [mem_SL_iff]
    norm_num [cWedge]

/-- `GjetA` is a polynomial in `yC`, hence invariant under `wC`. -/
private lemma GjetA_wC_local (a b c : ℤ) (i : ℕ) {z : ℂ} (hz : z ≠ 1) :
    GjetA a b c i (wC z) = GjetA a b c i z := by
  unfold GjetA
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [yC_wC_local hz]

/-! ## 2. The derivative of `wC` and the chain rule identity `dyC(wC z)·wC'(z) = dyC z` -/

private lemma hasDerivAt_wC_local (z : ℂ) (hz : z ≠ 1) :
    HasDerivAt wC (-(1 / (z - 1) ^ 2)) z := by
  have h' : HasDerivAt (fun x : ℂ => x / (x - 1))
      ((1 * (z - 1) - z * 1) / (z - 1) ^ 2) z :=
    (hasDerivAt_id z).div ((hasDerivAt_id z).sub_const 1) (sub_ne_zero.mpr hz)
  have hder : (1 * (z - 1) - z * 1) / (z - 1) ^ 2 = -(1 / (z - 1) ^ 2) := by ring
  rw [hder] at h'
  exact h'

private lemma dyC_wC_mul_local {z : ℂ} (hz : z ≠ 1) :
    dyC (wC z) * (-(1 / (z - 1) ^ 2)) = dyC z := by
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr hz
  have h1 : z / (z - 1) - 1 ≠ 0 := by
    have h : wC z - 1 ≠ 0 := by
      rw [wC_sub_one_local hz]
      exact inv_ne_zero hz1
    simpa only [wC] using h
  unfold dyC wC
  field_simp
  ring

/-! ## 3. Holomorphy of the two integrands on `SU` -/

private lemma yC_diffOn_SU_local : DifferentiableOn ℂ yC SU := by
  unfold yC
  exact (differentiableOn_id.pow 2).div (differentiableOn_id.sub (differentiableOn_const 1))
    (fun z hz => sub_ne_zero.mpr (fun h => one_notMem_SU_local (by rwa [h] at hz)))

private lemma dyC_diffOn_SU_local : DifferentiableOn ℂ dyC SU := by
  unfold dyC
  exact ((differentiableOn_id.pow 2).sub ((differentiableOn_const 2).mul differentiableOn_id)).div
    ((differentiableOn_id.sub (differentiableOn_const 1)).pow 2)
    (fun z hz => pow_ne_zero 2 (sub_ne_zero.mpr (fun h => one_notMem_SU_local (by rwa [h] at hz))))

private lemma yC_ne_zero_SU_local {z : ℂ} (hz : z ∈ SU) : yC z ≠ 0 := by
  intro h
  have hz1 : z - 1 ≠ 0 := sub_ne_zero.mpr (z_ne_one_of_mem_SU_local hz)
  have h2 : z ^ 2 = 0 := by
    have hh := h
    unfold yC at hh
    field_simp at hh
    simpa using hh
  have hz0 : z = 0 := sq_eq_zero_iff.mp h2
  rw [hz0] at hz
  exact zero_notMem_SU_local hz

private lemma HLwC_diffOn_SU_local {HL : ℂ → ℂ} (hHL : DifferentiableOn ℂ HL SL) :
    DifferentiableOn ℂ (fun z => HL (wC z)) SU := by
  have hw : DifferentiableOn ℂ wC SU := by
    unfold wC
    exact differentiableOn_id.div (differentiableOn_id.sub (differentiableOn_const 1))
      (fun z hz => sub_ne_zero.mpr (fun h => one_notMem_SU_local (by rwa [h] at hz)))
  exact hHL.comp hw (fun z hz => wC_mem_SL_of_mem_SU_local hz)

private lemma GjetA_diffOn_SU_local (a b c : ℤ) (i : ℕ) :
    DifferentiableOn ℂ (GjetA a b c i) SU := by
  induction i with
  | zero =>
    have h0 : GjetA a b c 0 = fun _ => (0 : ℂ) := by
      funext z
      simp [GjetA]
    rw [h0]
    exact differentiableOn_const _
  | succ i ih =>
    have h1 : GjetA a b c (i + 1) = fun z => GjetA a b c i z +
        ((PowerSeries.coeff i (Submission.CDTPlan.GZ a b c) : ℚ) : ℂ) * (yC z) ^ i := by
      funext z
      simp only [GjetA, Finset.sum_range_succ]
    rw [h1]
    exact ih.add ((differentiableOn_const _).mul (yC_diffOn_SU_local.pow i))

private lemma jIntU_diffOn_local (a b c : ℤ) {HU HL : ℂ → ℂ}
    (hHU : DifferentiableOn ℂ HU SU) (hHL : DifferentiableOn ℂ HL SL) (i : ℕ) :
    DifferentiableOn ℂ (jIntU a b c HU HL i) SU := by
  have hyinv : DifferentiableOn ℂ (fun z => (yC z)⁻¹ ^ i) SU :=
    (yC_diffOn_SU_local.inv (fun z hz => yC_ne_zero_SU_local hz)).pow i
  have hinner : DifferentiableOn ℂ (fun z => (HU z + HL (wC z)) - GjetA a b c i z) SU :=
    (hHU.add (HLwC_diffOn_SU_local hHL)).sub (GjetA_diffOn_SU_local a b c i)
  exact (dyC_diffOn_SU_local.mul hyinv).mul hinner

private lemma jumpH_diffOn_SU_local {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) :
    DifferentiableOn ℂ (jumpH D) SU := by
  have hw : DifferentiableOn ℂ wC SU := by
    unfold wC
    exact differentiableOn_id.div (differentiableOn_id.sub (differentiableOn_const 1))
      (fun z hz => sub_ne_zero.mpr (fun h => one_notMem_SU_local (by rwa [h] at hz)))
  have hcomp : DifferentiableOn ℂ (fun z => D (wC z)) SU :=
    hD.comp hw (fun z hz => SL_subset_Om1 (wC_mem_SL_of_mem_SU_local hz))
  exact (hD.mono SU_subset_Om1).sub hcomp

private lemma jIntJ_diffOn_local {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (i : ℕ) :
    DifferentiableOn ℂ (jIntJ D i) SU :=
  (dyC_diffOn_SU_local.mul
    ((yC_diffOn_SU_local.inv (fun z hz => yC_ne_zero_SU_local hz)).pow i)).mul
    (jumpH_diffOn_SU_local hD)

/-! ## 4. The primitives `BUi`, `JFI` and their `wC`-pullback -/

private lemma hasDerivAt_BUi (a b c : ℤ) {HU HL : ℂ → ℂ}
    (hHU : DifferentiableOn ℂ HU SU) (hHL : DifferentiableOn ℂ HL SL) (i : Fin 3) :
    ∀ z ∈ SU, HasDerivAt (BUi a b c HU HL i) (jIntU a b c HU HL (i : ℕ) z) z := by
  have hf : DifferentiableOn ℂ (jIntU a b c HU HL (i : ℕ)) SU :=
    jIntU_diffOn_local a b c hHU hHL (i : ℕ)
  have h := primSeg_hasDerivAt convex_SU isOpen_SU_H_cont cSU_mem_SU_local hf
  intro z hz
  have h2 := (h z hz).const_add (∑' k : ℕ,
      ((PowerSeries.coeff k (Submission.CDTPlan.fourteen a b c (iIdxA i)) : ℚ) : ℂ)
        * (yC cSU) ^ k)
  rw [BUi_eq_const_add_primSeg]
  exact h2

private lemma hasDerivAt_JFI {D : ℂ → ℂ} (hD : DifferentiableOn ℂ D Om1) (i : Fin 3) :
    ∀ z ∈ SU, HasDerivAt (JFI D i) (jIntJ D (i : ℕ) z) z := by
  have hf : DifferentiableOn ℂ (jIntJ D (i : ℕ)) SU := jIntJ_diffOn_local hD (i : ℕ)
  have h := primSeg_hasDerivAt convex_SU isOpen_SU_H_cont cSU_mem_SU_local hf
  intro z hz
  rw [JFI_eq_primSeg]
  exact h z hz

/-- Chain rule for the `wC`-pullback of `BUi` on the wedge. -/
private lemma hasDerivAt_BUi_comp_wC (a b c : ℤ) {HU HL : ℂ → ℂ}
    (hHU : DifferentiableOn ℂ HU SU) (hHL : DifferentiableOn ℂ HL SL) (i : Fin 3)
    {z : ℂ} (hz : z ∈ SU ∩ SL) :
    HasDerivAt (fun u => BUi a b c HU HL i (wC u))
      (dyC z * (yC z)⁻¹ ^ (i : ℕ) * (HU (wC z) + HL z - GjetA a b c (i : ℕ) z)) z := by
  have hz1 : z ≠ 1 := z_ne_one_of_mem_SU_local hz.1
  have hwz : wC z ∈ SU ∩ SL := wC_mem_wedge_local hz
  have hBU : HasDerivAt (BUi a b c HU HL i) (jIntU a b c HU HL (i : ℕ) (wC z)) (wC z) :=
    hasDerivAt_BUi a b c hHU hHL i (wC z) hwz.1
  refine (hBU.comp (x := z) (hasDerivAt_wC_local z hz1)).congr_deriv ?_
  calc jIntU a b c HU HL (i : ℕ) (wC z) * (-(1 / (z - 1) ^ 2))
      = (dyC (wC z) * (-(1 / (z - 1) ^ 2)))
          * ((yC z)⁻¹ ^ (i : ℕ) * (HU (wC z) + HL z - GjetA a b c (i : ℕ) z)) := by
        simp only [jIntU]
        rw [wC_inv_local hz1, yC_wC_local hz1, GjetA_wC_local a b c (i : ℕ) hz1]
        ring
    _ = dyC z * (yC z)⁻¹ ^ (i : ℕ) * (HU (wC z) + HL z - GjetA a b c (i : ℕ) z) := by
        rw [dyC_wC_mul_local hz1]
        ring

/-! ## 5. The difference `PhiI` has zero derivative on the wedge -/

private lemma hasDerivAt_PhiI (a b c : ℤ) {HU HL D : ℂ → ℂ}
    (hHU : DifferentiableOn ℂ HU SU) (hHL : DifferentiableOn ℂ HL SL)
    (hD : DifferentiableOn ℂ D Om1)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z) (i : Fin 3) :
    ∀ z ∈ SU ∩ SL, HasDerivAt (PhiI a b c HU HL D i) 0 z := by
  intro z hz
  have hwz : wC z ∈ SU ∩ SL := wC_mem_wedge_local hz
  have h1 : HasDerivAt (BUi a b c HU HL i) (jIntU a b c HU HL (i : ℕ) z) z :=
    hasDerivAt_BUi a b c hHU hHL i z hz.1
  have h2 : HasDerivAt (fun u => BUi a b c HU HL i (wC u))
      (dyC z * (yC z)⁻¹ ^ (i : ℕ) * (HU (wC z) + HL z - GjetA a b c (i : ℕ) z)) z :=
    hasDerivAt_BUi_comp_wC a b c hHU hHL i hz
  have h3 : HasDerivAt (JFI D i) (jIntJ D (i : ℕ) z) z := hasDerivAt_JFI hD i z hz.1
  have hmain := (h1.sub h2).sub h3
  have hzero : jIntU a b c HU HL (i : ℕ) z
      - dyC z * (yC z)⁻¹ ^ (i : ℕ) * (HU (wC z) + HL z - GjetA a b c (i : ℕ) z)
      - jIntJ D (i : ℕ) z = 0 := by
    simp only [jIntU, jIntJ, jumpH]
    rw [hDj z hz, hDj (wC z) hwz]
    ring
  rw [hzero] at hmain
  exact hmain

/-- `PhiI` vanishes at the wedge point `cWedge`. -/
private lemma PhiI_cWedge (a b c : ℤ) (HU HL D : ℂ → ℂ) (i : Fin 3) :
    PhiI a b c HU HL D i cWedge
      = (BUi a b c HU HL i cWedge - BUi a b c HU HL i (wC cWedge)) - JFI D i cWedge := rfl

theorem jump_I_ident (a b c : ℤ) (HU HL D : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU) (hHL : DifferentiableOn ℂ HL SL)
    (hD : DifferentiableOn ℂ D Om1)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z) (i : Fin 3) :
    ∀ z ∈ SU ∩ SL, JFIc a b c HU HL D i z
      = BUi a b c HU HL i z - BUi a b c HU HL i (wC z) := by
  have hKconv : Convex ℝ (SU ∩ SL) := convex_SU.inter convex_SL
  have hKpre : IsPreconnected (SU ∩ SL) := hKconv.isPreconnected
  have hKopen : IsOpen (SU ∩ SL) := isOpen_SU_H_cont.inter isOpen_SL_H_cont
  have hdiff : DifferentiableOn ℂ (PhiI a b c HU HL D i) (SU ∩ SL) :=
    fun z hz =>
      (hasDerivAt_PhiI a b c hHU hHL hD hDj i z hz).differentiableAt.differentiableWithinAt
  have hder : (SU ∩ SL).EqOn (deriv (PhiI a b c HU HL D i)) 0 :=
    fun z hz => (hasDerivAt_PhiI a b c hHU hHL hD hDj i z hz).deriv
  intro z hz
  have hconst := IsOpen.is_const_of_deriv_eq_zero hKopen hKpre hdiff hder
    cWedge_mem_wedge_local hz
  simp only [PhiI_def] at hconst
  simp only [JFIc]
  rw [hconst]
  ring

end

end Work.A14D
