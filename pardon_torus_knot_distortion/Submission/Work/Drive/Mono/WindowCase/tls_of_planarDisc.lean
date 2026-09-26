import Mathlib
import Submission.Work.Drive.Mono.FiberModel.Defs
import Submission.Work.Drive.Mono.FiberModel.planarImage
import Submission.Work.Drive.Mono.FiberModel.planar_basic
import Submission.Work.Drive.Mono.FiberModel.pair_facts
import Submission.Work.Drive.Mono.FiberModel.height_basic
import Submission.Work.Drive.Mono.WindowCase.tls_fibre_model
import Submission.Work.Drive.Mono.WindowCase.tls_planar_facts
import Submission.Work.Drive.Mono.WindowCase.frontier_hypograph_eq
import Submission.Work.Drive.Mono.WindowCase.CupDefs
import Submission.Work.Drive.Mono.isEmbeddedSphere_of_twoDiscs
import Submission.Work.Drive.Mono.WindowCase.tls_hypograph_sphere
import Submission.Work.Drive.Mono.WindowCase.frontierStrictOverEq
import Submission.Work.Drive.Mono.WindowCase.solidOverDiscSphere
import Submission.Work.InnermostDisk.isEmbeddedSphere_image_homeomorph

namespace Work.Drive.Mono.WindowCase

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

variable {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {u h lam : ℝ} {v : R3}
  {ℓ : R3 →L[ℝ] ℝ}

/-! ## Elementary facts about the box -/

/-- The centre of the box is in the box. -/
theorem PBox_center_mem (hs : 0 < s) : c ∈ Submission.PBox s c σ := by
  rw [Submission.mem_PBox]
  intro i
  rw [sub_self, abs_zero]
  exact mul_pos (Submission.boxSide_pos i) hs

/-- Every point of the closed box satisfies the box inequalities with `≤`. -/
theorem ClBox_coord (hs : 0 < s) {y : R3} (hy : y ∈ Work.Drive.Mono.FiberModel.ClBox s c σ)
    (i : Fin 3) : |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s := by
  have hcont : Continuous fun z : R3 => |z (σ i) - c (σ i)| := by fun_prop
  have hsub : Submission.PBox s c σ ⊆
      {z : R3 | |z (σ i) - c (σ i)| < Submission.boxSide i * s} := by
    intro z hz
    exact (Submission.mem_PBox.mp hz) i
  have hy' : y ∈ closure (Submission.PBox s c σ) := by
    simpa only [Work.Drive.Mono.FiberModel.ClBox] using hy
  have h1 : y ∈ closure {z : R3 | |z (σ i) - c (σ i)| < Submission.boxSide i * s} :=
    closure_mono hsub hy'
  exact closure_lt_subset_le hcont continuous_const h1

/-- The interior of the closed box is the open box. -/
theorem interior_ClBox (hs : 0 < s) :
    interior (Work.Drive.Mono.FiberModel.ClBox s c σ) = Submission.PBox s c σ := by
  have hCl : Work.Drive.Mono.FiberModel.ClBox s c σ = closure (Submission.PBox s c σ) := rfl
  have hne : (interior (Submission.PBox s c σ)).Nonempty :=
    ⟨c, by rw [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq]; exact PBox_center_mem hs⟩
  rw [hCl]
  rw [Convex.interior_closure_eq_interior_of_nonempty_interior
    (Work.Topology.SphereSlicing.convex_PBox s c σ) hne]
  rw [(Work.Topology.SphereSlicing.isOpen_PBox s c σ).interior_eq]

/-! ## The fibre coordinate -/

/-- `(levPair, ζ)` separates points when `ζ` is transverse to the fibres of `levPair`. -/
theorem levPair_zeta_inj {ζ : R3 →L[ℝ] ℝ} (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ)
    {y y' : R3} (h1 : Work.Drive.Mono.FiberModel.levPair v ℓ y
        = Work.Drive.Mono.FiberModel.levPair v ℓ y')
    (h2 : ζ y = ζ y') : y = y' := by
  have h1a : (Work.Drive.Mono.FiberModel.levPair v ℓ y).1
      = (Work.Drive.Mono.FiberModel.levPair v ℓ y').1 := congrArg Prod.fst h1
  have h1b : (Work.Drive.Mono.FiberModel.levPair v ℓ y).2
      = (Work.Drive.Mono.FiberModel.levPair v ℓ y').2 := congrArg Prod.snd h1
  simp only [Work.Drive.Mono.FiberModel.levPair] at h1a h1b
  have h3 : inner ℝ v (y - y') = 0 := by rw [inner_sub_right, h1a, sub_self]
  have h4 : ℓ (y - y') = 0 := by rw [map_sub, h1b, sub_self]
  have h5 : ζ (y - y') = 0 := by rw [map_sub, h2, sub_self]
  exact sub_eq_zero.mp (hζ (y - y') h3 h4 h5)

/-! ## The fibre of the closed box in the `ζ`-coordinate -/

/-- The fibre direction is not annihilated by a functional transverse to the fibres. -/
theorem zeta_fibreDir_ne_zero {ζ : R3 →L[ℝ] ℝ} (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ) :
    ζ (Work.Drive.Final.Trough.fibreDir v ℓ) ≠ 0 := by
  intro h0
  have hker := Work.Drive.Final.Trough.pair_fibreDir (v := v) (ℓ := ℓ) hv hℓv hℓne
  refine Work.Drive.Final.Trough.fibreDir_ne_zero (v := v) (ℓ := ℓ) hv hℓv hℓne (hζ _ ?_ ?_ h0)
  · have h := congrArg Prod.fst hker
    simpa [Work.Drive.Final.Trough.pair_apply] using h
  · have h := congrArg Prod.snd hker
    simpa [Work.Drive.Final.Trough.pair_apply] using h

/-- The closed box is convex. -/
theorem convex_ClBox : Convex ℝ (Work.Drive.Mono.FiberModel.ClBox s c σ) :=
  Work.Topology.SphereSlicing.convex_PBox s c σ |>.closure

/-- The `ζ`-values of the fibre of the closed box over `X ∈ boxShadow` are precisely the points of
the interval `[fMin X, fMax X]`: the fibre is described by `ζ` alone. -/
theorem mem_ClBox_iff_zeta (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {ζ : R3 →L[ℝ] ℝ} (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ)
    (hfib : ∀ X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ,
      ζ '' Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X
        = Set.Icc (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X)
            (Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X))
    {X : ℝ × ℝ} (hX : X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) {y : R3}
    (hy : Work.Drive.Mono.FiberModel.levPair v ℓ y = X) :
    y ∈ Work.Drive.Mono.FiberModel.ClBox s c σ ↔
      ζ y ∈ Set.Icc (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X)
        (Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X) := by
  constructor
  · intro hyC
    have hmem : ζ y ∈ ζ '' Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X :=
      ⟨y, ⟨hyC, hy⟩, rfl⟩
    rwa [hfib X hX] at hmem
  · intro hz
    have hmem : ζ y ∈ ζ '' Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X := by rwa [hfib X hX]
    obtain ⟨y', hy', hzy'⟩ := hmem
    have hy'X : Work.Drive.Mono.FiberModel.levPair v ℓ y' = X := hy'.2
    have : y' = y := levPair_zeta_inj hζ (by rw [hy'X, hy]) hzy'
    rw [← this]
    exact hy'.1

/-- A point of the closed box over `X` whose `ζ`-value is strictly interior in the fibre interval
has a neighbourhood along the fibre direction contained in the closed box. -/
theorem exists_smul_mem_ClBox (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {ζ : R3 →L[ℝ] ℝ} (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ)
    (hfib : ∀ X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ,
      ζ '' Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X
        = Set.Icc (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X)
            (Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X))
    {X : ℝ × ℝ} (hX : X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) {y : R3}
    (hyC : y ∈ Work.Drive.Mono.FiberModel.ClBox s c σ)
    (hyX : Work.Drive.Mono.FiberModel.levPair v ℓ y = X)
    (hlo : Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X < ζ y)
    (hhi : ζ y < Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X) :
    ∃ δ > 0, ∀ t : ℝ, |t| < δ →
      y + t • Work.Drive.Final.Trough.fibreDir v ℓ ∈ Work.Drive.Mono.FiberModel.ClBox s c σ := by
  classical
  set k := Work.Drive.Final.Trough.fibreDir v ℓ with hk
  have hζk : ζ k ≠ 0 := zeta_fibreDir_ne_zero hv hℓv hℓne hζ
  -- two comparison points of the fibre, on either side of `y` in the `ζ`-coordinate
  obtain ⟨yP, hyPfib, hyPζ⟩ : ∃ y' ∈ Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X,
      ζ y' = (ζ y + Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X) / 2 := by
    have hmem : (ζ y + Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X) / 2 ∈
        ζ '' Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X := by
      rw [hfib X hX]
      exact ⟨by linarith, by linarith⟩
    exact hmem
  obtain ⟨yM, hyMfib, hyMζ⟩ : ∃ y' ∈ Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X,
      ζ y' = (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X + ζ y) / 2 := by
    have hmem : (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X + ζ y) / 2 ∈
        ζ '' Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X := by
      rw [hfib X hX]
      exact ⟨by linarith, by linarith⟩
    exact hmem
  -- fibre coordinates
  have hpy : Work.Drive.Final.Trough.pair v ℓ y = X := by
    simpa [Work.Drive.Mono.FiberModel.levPair, Work.Drive.Final.Trough.pair_apply] using hyX
  have hpyP : Work.Drive.Final.Trough.pair v ℓ yP = X := by
    simpa [Work.Drive.Mono.FiberModel.levPair, Work.Drive.Final.Trough.pair_apply] using hyPfib.2
  have hpyM : Work.Drive.Final.Trough.pair v ℓ yM = X := by
    simpa [Work.Drive.Mono.FiberModel.levPair, Work.Drive.Final.Trough.pair_apply] using hyMfib.2
  obtain ⟨tp, htp⟩ := Work.Drive.Final.Trough.exists_fibre_coord (v := v) (ℓ := ℓ) hv hℓv hℓne yP
  obtain ⟨tm, htm⟩ := Work.Drive.Final.Trough.exists_fibre_coord (v := v) (ℓ := ℓ) hv hℓv hℓne yM
  obtain ⟨ty, hty⟩ := Work.Drive.Final.Trough.exists_fibre_coord (v := v) (ℓ := ℓ) hv hℓv hℓne y
  have htP : yP = Work.Drive.Final.Trough.sectionL v ℓ X + tp • k := by rw [htp, hpyP]
  have htM : yM = Work.Drive.Final.Trough.sectionL v ℓ X + tm • k := by rw [htm, hpyM]
  have htY : y = Work.Drive.Final.Trough.sectionL v ℓ X + ty • k := by rw [hty, hpy]
  have hζP : ζ yP = ζ (Work.Drive.Final.Trough.sectionL v ℓ X) + tp * ζ k := by
    rw [htP, map_add, map_smul, smul_eq_mul]
  have hζM : ζ yM = ζ (Work.Drive.Final.Trough.sectionL v ℓ X) + tm * ζ k := by
    rw [htM, map_add, map_smul, smul_eq_mul]
  have hζY : ζ y = ζ (Work.Drive.Final.Trough.sectionL v ℓ X) + ty * ζ k := by
    rw [htY, map_add, map_smul, smul_eq_mul]
  have hPpos : 0 < (tp - ty) * ζ k := by
    have h1 : ζ yP - ζ y = (Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X - ζ y) / 2 := by
      rw [hyPζ]; ring
    have h2 : ζ yP - ζ y = (tp - ty) * ζ k := by rw [hζP, hζY]; ring
    rw [h2] at h1
    linarith
  have hMneg : (tm - ty) * ζ k < 0 := by
    have h1 : ζ yM - ζ y = (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X - ζ y) / 2 := by
      rw [hyMζ]; ring
    have h2 : ζ yM - ζ y = (tm - ty) * ζ k := by rw [hζM, hζY]; ring
    rw [h2] at h1
    linarith
  -- `ty` lies strictly between `tp` and `tm`
  have hbetween : (tp - ty) * (tm - ty) < 0 := by
    rcases lt_or_gt_of_ne hζk with hkneg | hkpos
    · have h1 : tp - ty < 0 := by
        by_contra hcon
        have h1' : 0 ≤ tp - ty := not_lt.mp hcon
        nlinarith [mul_nonpos_of_nonneg_of_nonpos h1' hkneg.le]
      have h2 : 0 < tm - ty := by
        by_contra hcon
        have h2' : tm - ty ≤ 0 := le_of_not_gt hcon
        nlinarith [mul_nonneg_of_nonpos_of_nonpos h2' hkneg.le]
      nlinarith
    · have h1 : 0 < tp - ty := pos_of_mul_pos_left hPpos hkpos.le
      have h2 : tm - ty < 0 := neg_of_mul_neg_left hMneg hkpos.le
      nlinarith
  have hsep1 : tp - ty ≠ 0 := by
    intro h0
    simp [h0] at hbetween
  have hsep2 : tm - ty ≠ 0 := by
    intro h0
    simp [h0] at hbetween
  have hδpos : 0 < min |tp - ty| |tm - ty| / 2 := by
    have h1 : 0 < |tp - ty| := abs_pos.mpr hsep1
    have h2 : 0 < |tm - ty| := abs_pos.mpr hsep2
    have h3 := lt_min h1 h2
    linarith
  refine ⟨min |tp - ty| |tm - ty| / 2, hδpos, fun τ hτlt => ?_⟩
  have hs1 : |τ| < |tp - ty| := by
    have h := min_le_left |tp - ty| |tm - ty|; linarith
  have hs2 : |τ| < |tm - ty| := by
    have h := min_le_right |tp - ty| |tm - ty|; linarith
  have hbet' : (tp - (ty + τ)) * (tm - (ty + τ)) < 0 := by
    have h1 : tp - (ty + τ) = (tp - ty) - τ := by ring
    have h2 : tm - (ty + τ) = (tm - ty) - τ := by ring
    rw [h1, h2]
    rcases mul_neg_iff.mp hbetween with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have h3 : 0 < (tp - ty) - τ := by
        have h4 := le_abs_self τ; rw [abs_of_pos ha] at hs1; linarith
      have h4 : (tm - ty) - τ < 0 := by
        have h5 := neg_abs_le τ; rw [abs_of_neg hb] at hs2; linarith
      exact mul_neg_of_pos_of_neg h3 h4
    · have h3 : (tp - ty) - τ < 0 := by
        have h4 := neg_abs_le τ; rw [abs_of_neg ha] at hs1; linarith
      have h4 : 0 < (tm - ty) - τ := by
        have h5 := le_abs_self τ; rw [abs_of_pos hb] at hs2; linarith
      exact mul_neg_of_neg_of_pos h3 h4
  -- the convex combination
  set u : ℝ := (ty + τ - tp) / (tm - tp) with hu
  have htmp : tm - tp ≠ 0 := by
    intro h0
    have htp' : tm = tp := by linarith
    rw [htp'] at hbetween
    have h2 := mul_self_nonneg (tp - ty)
    linarith
  have hu_pos : 0 < u := by
    rcases mul_neg_iff.mp hbet' with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hnum : ty + τ - tp < 0 := by linarith
      have hden : tm - tp < 0 := by linarith
      rw [hu]; exact div_pos_of_neg_of_neg hnum hden
    · have hnum : 0 < ty + τ - tp := by linarith
      have hden : 0 < tm - tp := by linarith
      rw [hu]; exact div_pos hnum hden
  have hu_lt : u < 1 := by
    rcases mul_neg_iff.mp hbet' with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have hden : tm - tp < 0 := by linarith
      rw [hu, div_lt_one_of_neg hden]; linarith
    · have hden : 0 < tm - tp := by linarith
      rw [hu, div_lt_one hden]; linarith
  have hcoef : (1 - u) * tp + u * tm = ty + τ := by
    rw [hu]
    field_simp
    ring
  have hcombo : (1 - u) • yP + u • yM = y + τ • k := by
    rw [htP, htM, htY]
    have hmod : (1 - u) • (Work.Drive.Final.Trough.sectionL v ℓ X + tp • k)
        + u • (Work.Drive.Final.Trough.sectionL v ℓ X + tm • k)
        = Work.Drive.Final.Trough.sectionL v ℓ X + ((1 - u) * tp + u * tm) • k := by
      module
    rw [hmod, hcoef]
    module
  have hsum : (1 - u) + u = 1 := by ring
  have hu0 : 0 ≤ 1 - u := by linarith
  have hmem : (1 - u) • yP + u • yM ∈ Work.Drive.Mono.FiberModel.ClBox s c σ :=
    convex_ClBox (a := 1 - u) (b := u) hyPfib.1 hyMfib.1 hu0 hu_pos.le hsum
  rw [← hcombo]
  exact hmem

/-- The fibre direction is tangent to the box fibres. -/
theorem levPair_fibreDir (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0) :
    Work.Drive.Mono.FiberModel.levPairCLM v ℓ (Work.Drive.Final.Trough.fibreDir v ℓ) = 0 := by
  have h := Work.Drive.Final.Trough.pair_fibreDir (v := v) (ℓ := ℓ) hv hℓv hℓne
  rw [Work.Drive.Final.Trough.pair_apply] at h
  rw [Work.Drive.Mono.FiberModel.levPairCLM_apply]
  exact h

/-- A point of the open box can be shifted a little in both fibre directions and stay in the box. -/
theorem exists_smul_mem_PBox {y : R3} (hyP : y ∈ Submission.PBox s c σ) :
    ∃ τ : ℝ, 0 < τ ∧
      y + τ • Work.Drive.Final.Trough.fibreDir v ℓ ∈ Submission.PBox s c σ ∧
      y + (-τ) • Work.Drive.Final.Trough.fibreDir v ℓ ∈ Submission.PBox s c σ := by
  obtain ⟨ε, hεpos, hεball⟩ :=
    Metric.isOpen_iff.mp (Work.Topology.SphereSlicing.isOpen_PBox s c σ) y hyP
  set τ : ℝ := ε / (2 * (‖Work.Drive.Final.Trough.fibreDir v ℓ‖ + 1)) with hτ
  have hτpos : 0 < τ := by rw [hτ]; positivity
  have hτsmall : τ * ‖Work.Drive.Final.Trough.fibreDir v ℓ‖ < ε := by
    rw [hτ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg (Work.Drive.Final.Trough.fibreDir v ℓ)]
  have hmem : ∀ a : ℝ, |a| = τ →
      y + a • Work.Drive.Final.Trough.fibreDir v ℓ ∈ Submission.PBox s c σ := by
    intro a ha
    refine hεball ?_
    rw [Metric.mem_ball, dist_eq_norm]
    have h1 : y + a • Work.Drive.Final.Trough.fibreDir v ℓ - y
        = a • Work.Drive.Final.Trough.fibreDir v ℓ := by abel
    rw [h1, norm_smul, Real.norm_eq_abs, ha]
    exact hτsmall
  exact ⟨τ, hτpos, hmem τ (abs_of_pos hτpos), hmem (-τ) (by rw [abs_neg, abs_of_pos hτpos])⟩

/-- **The open box in the fibre coordinates.**  A point of `ℝ³` lies in the open box exactly when
its `(levPair, ζ)`-coordinates lie over the interior of the shadow, with `ζ`-value strictly between
the two heights. -/
theorem mem_PBox_iff_zeta (hs : 0 < s) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {ζ : R3 →L[ℝ] ℝ} (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ)
    (hfib : ∀ X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ,
      ζ '' Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X
        = Set.Icc (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X)
            (Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X))
    (hstrict : ∀ X ∈ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ),
      Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X
        < Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X)
    (y : R3) :
    y ∈ Submission.PBox s c σ ↔
      Work.Drive.Mono.FiberModel.levPair v ℓ y
          ∈ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) ∧
        Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ
            (Work.Drive.Mono.FiberModel.levPair v ℓ y) < ζ y ∧
          ζ y < Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ
            (Work.Drive.Mono.FiberModel.levPair v ℓ y) := by
  classical
  set X := Work.Drive.Mono.FiberModel.levPair v ℓ y with hXdef
  have hk0 := levPair_fibreDir (v := v) (ℓ := ℓ) hv hℓv hℓne
  have hζk : ζ (Work.Drive.Final.Trough.fibreDir v ℓ) ≠ 0 :=
    zeta_fibreDir_ne_zero hv hℓv hℓne hζ
  have hCl : ∀ {z : R3}, z ∈ Submission.PBox s c σ →
      z ∈ Work.Drive.Mono.FiberModel.ClBox s c σ := by
    intro z hz
    have h : z ∈ closure (Submission.PBox s c σ) := subset_closure hz
    simpa only [Work.Drive.Mono.FiberModel.ClBox] using h
  have hlev : ∀ a : ℝ, Work.Drive.Mono.FiberModel.levPair v ℓ
      (y + a • Work.Drive.Final.Trough.fibreDir v ℓ) = X := by
    intro a
    rw [Work.Drive.Mono.FiberModel.levPair_eq_levPairCLM, map_add, map_smul, hk0,
      smul_zero, add_zero]
    exact hXdef.symm
  constructor
  · intro hyP
    have hyW : X ∈ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) := by
      rw [← Work.Drive.Mono.FiberModel.image_PBox_eq_interior_boxShadow (s := s) c σ hv hℓv hℓne]
      exact ⟨y, hyP, rfl⟩
    have hXW : X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ := interior_subset hyW
    have hle := (mem_ClBox_iff_zeta (s := s) (c := c) (σ := σ) hv hℓv hℓne hζ hfib
      hXW hXdef.symm).mp (hCl hyP)
    obtain ⟨τ, hτpos, hτP, hτM⟩ := exists_smul_mem_PBox (s := s) (c := c) (σ := σ)
      (v := v) (ℓ := ℓ) hyP
    have hp := (mem_ClBox_iff_zeta (s := s) (c := c) (σ := σ) hv hℓv hℓne hζ hfib
      hXW (hlev τ)).mp (hCl hτP)
    have hm := (mem_ClBox_iff_zeta (s := s) (c := c) (σ := σ) hv hℓv hℓne hζ hfib
      hXW (hlev (-τ))).mp (hCl hτM)
    have hzvP : ζ (y + τ • Work.Drive.Final.Trough.fibreDir v ℓ)
        = ζ y + τ * ζ (Work.Drive.Final.Trough.fibreDir v ℓ) := by
      rw [map_add, map_smul, smul_eq_mul]
    have hzvM : ζ (y + (-τ) • Work.Drive.Final.Trough.fibreDir v ℓ)
        = ζ y - τ * ζ (Work.Drive.Final.Trough.fibreDir v ℓ) := by
      rw [map_add, map_smul, smul_eq_mul]; ring
    refine ⟨hyW, ?_, ?_⟩
    · by_contra hcon
      have hEq : ζ y = Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X :=
        le_antisymm (not_lt.mp hcon) hle.1
      rw [hEq] at hzvP hzvM
      have h1 : 0 ≤ ζ (Work.Drive.Final.Trough.fibreDir v ℓ) := by nlinarith [hp.1, hzvP]
      have h2 : ζ (Work.Drive.Final.Trough.fibreDir v ℓ) ≤ 0 := by nlinarith [hm.1, hzvM]
      exact hζk (le_antisymm h2 h1)
    · by_contra hcon
      have hEq : ζ y = Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X :=
        le_antisymm hle.2 (not_lt.mp hcon)
      rw [hEq] at hzvP hzvM
      have h1 : 0 ≤ ζ (Work.Drive.Final.Trough.fibreDir v ℓ) := by nlinarith [hm.2, hzvM]
      have h2 : ζ (Work.Drive.Final.Trough.fibreDir v ℓ) ≤ 0 := by nlinarith [hp.2, hzvP]
      exact hζk (le_antisymm h2 h1)
  · rintro ⟨hyW, hlo, hhi⟩
    have hXW : X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ := interior_subset hyW
    have hIcc : ζ y ∈ Set.Icc (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X)
        (Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X) := ⟨hlo.le, hhi.le⟩
    have hyC : y ∈ Work.Drive.Mono.FiberModel.ClBox s c σ :=
      (mem_ClBox_iff_zeta (s := s) (c := c) (σ := σ) hv hℓv hℓne hζ hfib hXW hXdef.symm).mpr hIcc
    by_contra hcon
    have hcoord : ∃ i : Fin 3, |y (σ i) - c (σ i)| = Submission.boxSide i * s := by
      by_contra hcon'
      push_neg at hcon'
      refine hcon (Submission.mem_PBox.mpr (fun i => ?_))
      exact lt_of_le_of_ne (ClBox_coord hs hyC i) (hcon' i)
    obtain ⟨i, hi⟩ := hcoord
    have hbs : 0 < Submission.boxSide i * s := mul_pos (Submission.boxSide_pos i) hs
    obtain ⟨δ, hδpos, hδ⟩ := exists_smul_mem_ClBox (s := s) (c := c) (σ := σ)
      hv hℓv hℓne hζ hfib hXW hyC hXdef.symm hlo hhi
    set a : ℝ := δ / 2 with ha
    have hapos : 0 < a := by rw [ha]; linarith
    have haδ : |a| < δ := by rw [abs_of_pos hapos, ha]; linarith
    have h1 := ClBox_coord hs (hδ a haδ) i
    have h2 := ClBox_coord hs (hδ (-a) (by rw [abs_neg]; exact haδ)) i
    have h1' : (y + a • Work.Drive.Final.Trough.fibreDir v ℓ) (σ i)
        = y (σ i) + a * Work.Drive.Final.Trough.fibreDir v ℓ (σ i) := by
      simp [smul_eq_mul]
    rw [h1'] at h1
    have h2' : (y + (-a) • Work.Drive.Final.Trough.fibreDir v ℓ) (σ i)
        = y (σ i) - a * Work.Drive.Final.Trough.fibreDir v ℓ (σ i) := by
      simp [smul_eq_mul, sub_eq_add_neg, mul_neg]
    rw [h2'] at h2
    have hki : Work.Drive.Final.Trough.fibreDir v ℓ (σ i) = 0 := by
      rcases (abs_eq hbs.le).mp hi with heq | heq
      · have hterm : y (σ i) + a * Work.Drive.Final.Trough.fibreDir v ℓ (σ i) - c (σ i)
            = Submission.boxSide i * s + a * Work.Drive.Final.Trough.fibreDir v ℓ (σ i) := by
          linarith
        rw [hterm] at h1
        have hup := le_abs_self (Submission.boxSide i * s
          + a * Work.Drive.Final.Trough.fibreDir v ℓ (σ i))
        have hterm2 : y (σ i) - a * Work.Drive.Final.Trough.fibreDir v ℓ (σ i) - c (σ i)
            = Submission.boxSide i * s - a * Work.Drive.Final.Trough.fibreDir v ℓ (σ i) := by
          linarith
        rw [hterm2] at h2
        have hdn := le_abs_self (Submission.boxSide i * s
          - a * Work.Drive.Final.Trough.fibreDir v ℓ (σ i))
        nlinarith
      · have hterm : y (σ i) + a * Work.Drive.Final.Trough.fibreDir v ℓ (σ i) - c (σ i)
            = -(Submission.boxSide i * s) + a * Work.Drive.Final.Trough.fibreDir v ℓ (σ i) := by
          linarith
        rw [hterm] at h1
        have hlow := neg_le_of_abs_le h1
        have hterm2 : y (σ i) - a * Work.Drive.Final.Trough.fibreDir v ℓ (σ i) - c (σ i)
            = -(Submission.boxSide i * s) - a * Work.Drive.Final.Trough.fibreDir v ℓ (σ i) := by
          linarith
        rw [hterm2] at h2
        have hlow2 := neg_le_of_abs_le h2
        nlinarith
    obtain ⟨z, hzP, hzX⟩ : ∃ z, z ∈ Submission.PBox s c σ ∧
        Work.Drive.Mono.FiberModel.levPair v ℓ z = X := by
      rw [← Work.Drive.Mono.FiberModel.image_PBox_eq_interior_boxShadow (s := s) c σ hv hℓv hℓne]
        at hyW
      exact hyW
    obtain ⟨ty, hty⟩ := Work.Drive.Final.Trough.exists_fibre_coord (v := v) (ℓ := ℓ) hv hℓv hℓne y
    obtain ⟨tz, htz⟩ := Work.Drive.Final.Trough.exists_fibre_coord (v := v) (ℓ := ℓ) hv hℓv hℓne z
    have hpy : Work.Drive.Final.Trough.pair v ℓ y = X := by
      simpa [Work.Drive.Mono.FiberModel.levPair, Work.Drive.Final.Trough.pair_apply] using hXdef.symm
    have hpz : Work.Drive.Final.Trough.pair v ℓ z = X := by
      simpa [Work.Drive.Mono.FiberModel.levPair, Work.Drive.Final.Trough.pair_apply] using hzX
    have hty' : y = Work.Drive.Final.Trough.sectionL v ℓ X
        + ty • Work.Drive.Final.Trough.fibreDir v ℓ := by rw [hty, hpy]
    have htz' : z = Work.Drive.Final.Trough.sectionL v ℓ X
        + tz • Work.Drive.Final.Trough.fibreDir v ℓ := by rw [htz, hpz]
    have hdiff : z (σ i) = y (σ i) := by
      have h3 : z - y = (tz - ty) • Work.Drive.Final.Trough.fibreDir v ℓ := by
        rw [htz', hty']; module
      have h4 : (z - y) (σ i) = (tz - ty) * Work.Drive.Final.Trough.fibreDir v ℓ (σ i) := by
        rw [h3]
        simp [smul_eq_mul]
      rw [hki, mul_zero] at h4
      have h5 : (z - y) (σ i) = z (σ i) - y (σ i) := by simp
      linarith [h4, h5]
    have hzlt := (Submission.mem_PBox.mp hzP) i
    rw [hdiff, hi] at hzlt
    exact lt_irrefl _ hzlt

/-- **The removed level in the fibre coordinates.** -/
theorem tiltedLevelRemoved_eq_fibre (hs : 0 < s) (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {ζ : R3 →L[ℝ] ℝ} (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ)
    (hfib : ∀ X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ,
      ζ '' Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X
        = Set.Icc (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X)
            (Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X))
    (hstrict : ∀ X ∈ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ),
      Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X
        < Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X) :
    Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam =
      {y : R3 | Work.Drive.Mono.FiberModel.levPair v ℓ y ∈
            Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam ∧
          Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ
              (Work.Drive.Mono.FiberModel.levPair v ℓ y) < ζ y ∧
            ζ y < Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ
              (Work.Drive.Mono.FiberModel.levPair v ℓ y)} := by
  ext y
  rw [Work.Drive.Mono.FiberModel.tiltedLevelRemoved_eq s c σ u v h lam ℓ,
    Work.Drive.Mono.FiberModel.planarImage_eq s c σ u v h lam ℓ hv hℓv hℓne,
    Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hyP, hyc⟩
    have h := (mem_PBox_iff_zeta (s := s) (c := c) (σ := σ) hs hv hℓv hℓne hζ hfib hstrict y).mp hyP
    exact ⟨⟨h.1, hyc⟩, h.2.1, h.2.2⟩
  · rintro ⟨⟨hyW, hyc⟩, hlo, hhi⟩
    exact ⟨(mem_PBox_iff_zeta (s := s) (c := c) (σ := σ) hs hv hℓv hℓne hζ hfib hstrict y).mpr
      ⟨hyW, hlo, hhi⟩, hyc⟩

/-! ## The fibre coordinate change as a homeomorphism of `ℝ³` -/

/-- The coordinate identification `ℝ × ℝ ≃ ℝ²`. -/
noncomputable def xyL : (ℝ × ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (LinearEquiv.piFinTwo ℝ (fun _ : Fin 2 => ℝ)).symm.trans
    (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).symm

/-- The coordinate identification `ℝ × ℝ ≃ ℝ²` as a continuous linear equivalence. -/
noncomputable def xyLC : (ℝ × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (xyL : (ℝ × ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 2)).toContinuousLinearEquiv

/-- The coordinate homeomorphism `ℝ × ℝ ≃ ℝ²`. -/
noncomputable def xyLHomeo : (ℝ × ℝ) ≃ₜ EuclideanSpace ℝ (Fin 2) := xyLC.toHomeomorph

theorem xyLHomeo_apply (X : ℝ × ℝ) : xyLHomeo X = xyL X := rfl

theorem xyL_image_interior (s : Set (ℝ × ℝ)) : xyL '' interior s = interior (xyL '' s) :=
  Homeomorph.image_interior xyLHomeo s

theorem xyL_image_closure (s : Set (ℝ × ℝ)) : xyL '' closure s = closure (xyL '' s) :=
  Homeomorph.image_closure xyLHomeo s

theorem xyL_image_frontier (s : Set (ℝ × ℝ)) : xyL '' frontier s = frontier (xyL '' s) :=
  Homeomorph.image_frontier xyLHomeo s

/-- The map `xyL` is continuous. -/
theorem continuous_xyL : Continuous (fun X : ℝ × ℝ => xyL X) :=
  LinearMap.continuous_of_finiteDimensional (xyL : (ℝ × ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))

/-- The map `xyL.symm` is continuous. -/
theorem continuous_xyL_symm : Continuous (fun X : EuclideanSpace ℝ (Fin 2) => xyL.symm X) :=
  LinearMap.continuous_of_finiteDimensional
    (xyL.symm : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ × ℝ)

/-- The identification `ℝ² × ℝ ≃ ℝ³`. -/
noncomputable def mkLin : (EuclideanSpace ℝ (Fin 2) × ℝ) ≃ₗ[ℝ] R3 where
  toFun := fun P => Work.Drive.Mono.cmk P.1 P.2
  invFun := fun p => (Work.Drive.Mono.cproj p, Work.Drive.Mono.clast p)
  left_inv := by
    intro P
    simp [Work.Drive.Mono.cproj_cmk, Work.Drive.Mono.clast_cmk]
  right_inv := by
    intro p
    simp [Work.Drive.Mono.cmk_cproj_clast]
  map_add' := by
    intro P Q
    exact (Work.Drive.Mono.cmk_add P.1 Q.1 P.2 Q.2).symm
  map_smul' := by
    intro c P
    exact (Work.Drive.Mono.cmk_smul c P.1 P.2).symm

theorem mkLin_apply (P : EuclideanSpace ℝ (Fin 2) × ℝ) :
    mkLin P = Work.Drive.Mono.cmk P.1 P.2 := rfl

theorem cproj_mkLin (P : EuclideanSpace ℝ (Fin 2) × ℝ) :
    Work.Drive.Mono.cproj (mkLin P) = P.1 := by
  simp [mkLin_apply, Work.Drive.Mono.cproj_cmk]

theorem clast_mkLin (P : EuclideanSpace ℝ (Fin 2) × ℝ) :
    Work.Drive.Mono.clast (mkLin P) = P.2 := by
  simp [mkLin_apply, Work.Drive.Mono.clast_cmk]

/-- The linear coordinate change `y ↦ (xyL (⟪v,y⟫, ℓ y), ζ y)` of the fibre model. -/
noncomputable def fibLin (v : R3) (ℓ ζ : R3 →L[ℝ] ℝ) : R3 →ₗ[ℝ] R3 where
  toFun := fun y => Work.Drive.Mono.cmk (xyL (Work.Drive.Mono.FiberModel.levPair v ℓ y)) (ζ y)
  map_add' := by
    intro y y'
    have h1 : Work.Drive.Mono.FiberModel.levPair v ℓ (y + y')
        = Work.Drive.Mono.FiberModel.levPair v ℓ y
          + Work.Drive.Mono.FiberModel.levPair v ℓ y' := by
      rw [Work.Drive.Mono.FiberModel.levPair_eq_levPairCLM]
      rw [map_add (Work.Drive.Mono.FiberModel.levPairCLM v ℓ) y y']
    have h2 : ζ (y + y') = ζ y + ζ y' := map_add ζ y y'
    rw [h1, h2, map_add xyL (Work.Drive.Mono.FiberModel.levPair v ℓ y)
      (Work.Drive.Mono.FiberModel.levPair v ℓ y')]
    exact (Work.Drive.Mono.cmk_add _ _ _ _).symm
  map_smul' := by
    intro c y
    have h1 : Work.Drive.Mono.FiberModel.levPair v ℓ (c • y)
        = c • Work.Drive.Mono.FiberModel.levPair v ℓ y := by
      rw [Work.Drive.Mono.FiberModel.levPair_eq_levPairCLM]
      rw [map_smul (Work.Drive.Mono.FiberModel.levPairCLM v ℓ) c y]
    have h2 : ζ (c • y) = c • ζ y := map_smul ζ c y
    rw [h1, h2, map_smul xyL c (Work.Drive.Mono.FiberModel.levPair v ℓ y)]
    exact (Work.Drive.Mono.cmk_smul c _ _).symm

theorem fibLin_apply (v : R3) (ℓ ζ : R3 →L[ℝ] ℝ) (y : R3) :
    fibLin v ℓ ζ y = Work.Drive.Mono.cmk (xyL (Work.Drive.Mono.FiberModel.levPair v ℓ y))
      (ζ y) := rfl

theorem cproj_fibLin (v : R3) (ℓ ζ : R3 →L[ℝ] ℝ) (y : R3) :
    Work.Drive.Mono.cproj (fibLin v ℓ ζ y)
      = xyL (Work.Drive.Mono.FiberModel.levPair v ℓ y) := by
  simp [fibLin, Work.Drive.Mono.cproj_cmk]

theorem clast_fibLin (v : R3) (ℓ ζ : R3 →L[ℝ] ℝ) (y : R3) :
    Work.Drive.Mono.clast (fibLin v ℓ ζ y) = ζ y := by
  simp [fibLin, Work.Drive.Mono.clast_cmk]

/-- Surjectivity of the coordinate change. -/
theorem fibLin_surjective (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {ζ : R3 →L[ℝ] ℝ} (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ) :
    Function.Surjective (fibLin v ℓ ζ) := by
  intro p
  obtain ⟨y₀, hy₀⟩ := Work.Drive.Mono.FiberModel.levPairCLM_surjective hv hℓv hℓne
    (xyL.symm (Work.Drive.Mono.cproj p))
  have hk0 := levPair_fibreDir (v := v) (ℓ := ℓ) hv hℓv hℓne
  have hζk : ζ (Work.Drive.Final.Trough.fibreDir v ℓ) ≠ 0 :=
    zeta_fibreDir_ne_zero hv hℓv hℓne hζ
  refine ⟨y₀ + ((Work.Drive.Mono.clast p - ζ y₀)
      / ζ (Work.Drive.Final.Trough.fibreDir v ℓ)) •
      Work.Drive.Final.Trough.fibreDir v ℓ, ?_⟩
  rw [fibLin_apply]
  have hpair : Work.Drive.Mono.FiberModel.levPair v ℓ
      (y₀ + ((Work.Drive.Mono.clast p - ζ y₀)
        / ζ (Work.Drive.Final.Trough.fibreDir v ℓ)) •
        Work.Drive.Final.Trough.fibreDir v ℓ) = xyL.symm (Work.Drive.Mono.cproj p) := by
    rw [Work.Drive.Mono.FiberModel.levPair_eq_levPairCLM, map_add, map_smul, hk0,
      smul_zero, add_zero, ← hy₀]
  have hcl : ζ (y₀ + ((Work.Drive.Mono.clast p - ζ y₀)
        / ζ (Work.Drive.Final.Trough.fibreDir v ℓ)) •
        Work.Drive.Final.Trough.fibreDir v ℓ) = Work.Drive.Mono.clast p := by
    rw [map_add, map_smul, smul_eq_mul]
    field_simp
    ring
  rw [hpair, hcl, xyL.apply_symm_apply, Work.Drive.Mono.cmk_cproj_clast]

/-- **The fibre coordinate change**: `y ↦ mk (xyL (⟪v,y⟫, ℓ y)) (ζ y)` is a homeomorphism of `ℝ³`
when `ζ` is transverse to the fibres of `(⟪v,·⟫, ℓ)`. -/
noncomputable def fibreHomeo (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {ζ : R3 →L[ℝ] ℝ} (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ) : R3 ≃ₜ R3 :=
  (LinearEquiv.ofBijective (fibLin v ℓ ζ) (by
    constructor
    · intro y y' hyy'
      have h1 : Work.Drive.Mono.FiberModel.levPair v ℓ y
          = Work.Drive.Mono.FiberModel.levPair v ℓ y' := by
        have h := congrArg Work.Drive.Mono.cproj hyy'
        simp only [cproj_fibLin] at h
        exact xyL.injective h
      have h2 : ζ y = ζ y' := by
        have h := congrArg Work.Drive.Mono.clast hyy'
        simp only [clast_fibLin] at h
        exact h
      exact levPair_zeta_inj hζ h1 h2
    · exact fibLin_surjective hv hℓv hℓne hζ)).toContinuousLinearEquiv.toHomeomorph

theorem fibreHomeo_apply (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {ζ : R3 →L[ℝ] ℝ} (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ) (y : R3) :
    fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ y
      = Work.Drive.Mono.cmk (xyL (Work.Drive.Mono.FiberModel.levPair v ℓ y)) (ζ y) := by
  show fibLin v ℓ ζ y = _
  exact fibLin_apply v ℓ ζ y

theorem cproj_fibreHomeo (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {ζ : R3 →L[ℝ] ℝ} (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ) (y : R3) :
    Work.Drive.Mono.cproj (fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ y)
      = xyL (Work.Drive.Mono.FiberModel.levPair v ℓ y) := by
  rw [fibreHomeo_apply, Work.Drive.Mono.cproj_cmk]

theorem clast_fibreHomeo (hv : v ≠ 0) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    {ζ : R3 →L[ℝ] ℝ} (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ) (y : R3) :
    Work.Drive.Mono.clast (fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ y) = ζ y := by
  rw [fibreHomeo_apply, Work.Drive.Mono.clast_cmk]

/-! ## The image of the level under the fibre coordinate change -/

/-- The fibre coordinate change carries the removed level onto the strict region over the planar
image, in the plane of the shadow. -/
theorem image_fibreHomeo_tiltedLevelRemoved (hs : 0 < s) (hv : v ≠ 0) (hℓv : ℓ v = 0)
    (hℓne : ℓ ≠ 0) {ζ : R3 →L[ℝ] ℝ}
    (hζ : Work.Drive.Mono.FiberModel.HasTrivKernel v ℓ ζ)
    (hfib : ∀ X ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ,
      ζ '' Work.Drive.Mono.FiberModel.fibre v ℓ s c σ X
        = Set.Icc (Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X)
            (Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X))
    (hstrict : ∀ X ∈ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ),
      Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ X
        < Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ X) :
    fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ
        '' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam
      = {p : R3 |
          Work.Drive.Mono.cproj p ∈ xyL ''
              Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam ∧
          Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (xyL.symm (Work.Drive.Mono.cproj p))
              < Work.Drive.Mono.clast p ∧
          Work.Drive.Mono.clast p
            < Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ (xyL.symm (Work.Drive.Mono.cproj p))} := by
  rw [tiltedLevelRemoved_eq_fibre (s := s) (c := c) (σ := σ) (u := u) (h := h) (lam := lam)
    hs hv hℓv hℓne hζ hfib hstrict]
  ext p
  constructor
  · rintro ⟨y, ⟨hyZ, hlo, hhi⟩, rfl⟩
    refine ⟨⟨Work.Drive.Mono.FiberModel.levPair v ℓ y, hyZ,
      (cproj_fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ y).symm⟩, ?_, ?_⟩
    · rw [clast_fibreHomeo, cproj_fibreHomeo, xyL.symm_apply_apply]
      exact hlo
    · rw [clast_fibreHomeo, cproj_fibreHomeo, xyL.symm_apply_apply]
      exact hhi
  · rintro ⟨⟨X, hXZ, hXeq⟩, hlo, hhi⟩
    have hlev' : Work.Drive.Mono.FiberModel.levPair v ℓ
        ((fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ).symm p)
        = xyL.symm (Work.Drive.Mono.cproj p) := by
      refine xyL.injective ?_
      rw [xyL.apply_symm_apply, ← cproj_fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ
        ((fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ).symm p),
        (fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ).apply_symm_apply]
    have hlast' : ζ ((fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ).symm p)
        = Work.Drive.Mono.clast p := by
      rw [← clast_fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ
        ((fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ).symm p),
        (fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ).apply_symm_apply]
    have hXmem : Work.Drive.Mono.FiberModel.levPair v ℓ
        ((fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ).symm p)
        ∈ Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam := by
      rw [hlev', ← hXeq, xyL.symm_apply_apply]
      exact hXZ
    exact ⟨(fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ).symm p,
      ⟨hXmem, by rw [hlev', hlast']; exact hlo, by rw [hlev', hlast']; exact hhi⟩,
      (fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζ).apply_symm_apply p⟩

/-- **The one-sphere window from a planar disc.**  If the closure of the planar image of the level
is a disc and the box pokes out of the slab on both sides above the wall, then the frontier of the
level is a single embedded sphere. -/
theorem tls_of_planarDisc
    (s : ℝ) (hs : 0 < s) (c : EuclideanSpace ℝ (Fin 3)) (σ : Equiv.Perm (Fin 3)) (u h lam : ℝ)
    (v : EuclideanSpace ℝ (Fin 3))
    (ℓ : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ) (hh : 0 < h) (hℓv : ℓ v = 0) (hℓne : ℓ ≠ 0)
    (hv : v ≠ 0)
    (hwinP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y)
    (hwinM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h)
    (hwallP : ∃ y ∈ Submission.PBox s c σ, inner ℝ v c + u + h < inner ℝ v y ∧ lam < ℓ y)
    (hwallM : ∃ y ∈ Submission.PBox s c σ, inner ℝ v y < inner ℝ v c + u - h ∧ lam < ℓ y)
    (hZdisc : ∃ e : C(Metric.closedBall (0 : ℂ) 1, ℝ × ℝ), Function.Injective e ∧
      Set.range e = closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam) ∧
      Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) =
        frontier (closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam))) :
    Work.InnermostDisk.IsEmbeddedSphere
      (frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) := by
  classical
  -- the fibre model and the planar facts
  obtain ⟨ζ, hζker, hfib, hstrict, hcontMax, hcontMin, hconcMax, hconvMin⟩ :=
    tls_fibre_model s hs c σ h v ℓ hh hℓv hℓne hv
  obtain ⟨hintZ, hclZ⟩ :=
    tls_planar_facts s hs c σ u h lam v ℓ hh hℓv hℓne hv hwinP hwinM hwallP hwallM
  obtain ⟨e, he_inj, he_range, he_bdry⟩ := hZdisc
  set Z : Set (ℝ × ℝ) := Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam with hZdef
  set K : Set (ℝ × ℝ) := closure Z with hKdef
  have hKZ : K = closure (Work.Drive.Mono.FiberModel.planarImage s c σ u v h ℓ lam) := by
    rw [hKdef, hZdef]
  have he_rangeK : Set.range e = K := by rw [hKZ]; exact he_range
  have he_bdryK : Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier K := by
    rw [hKZ]; exact he_bdry
  have hZc : Z = interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) ∩
      Work.Drive.Mono.FiberModel.chamber (Work.Drive.Mono.FiberModel.slabA u c v) h lam := by
    rw [hZdef]
    exact Work.Drive.Mono.FiberModel.planarImage_eq s c σ u v h lam ℓ hv hℓv hℓne
  have hintZ_Z : interior (closure Z)
      = interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) ∩
        {X : ℝ × ℝ | h < |X.1 - Work.Drive.Mono.FiberModel.slabA u c v| ∨ lam < X.2} := by
    rw [hZdef]
    exact hintZ
  have hclZ_Z : closure Z = Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ ∩
      ({X : ℝ × ℝ | Work.Drive.Mono.FiberModel.slabA u c v + h ≤ X.1} ∪
       {X : ℝ × ℝ | X.1 ≤ Work.Drive.Mono.FiberModel.slabA u c v - h} ∪
       {X : ℝ × ℝ | lam ≤ X.2}) := by
    rw [hZdef]
    exact hclZ
  have hboxsub : K ⊆ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ := by
    rw [hKdef, hclZ_Z]; exact fun x hx => hx.1
  have hintsub : interior K ⊆ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ := by
    rw [hKdef, hintZ_Z]; exact fun x hx => interior_subset hx.1
  have hintKsubW : interior K ⊆ interior (Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ) := by
    rw [hKdef, hintZ_Z]; exact fun x hx => hx.1
  have hintZ' : interior K ⊆ Z := by
    intro X hX
    rw [hKdef] at hX
    rw [hintZ_Z] at hX
    rw [hZc]
    refine ⟨hX.1, ?_⟩
    rcases hX.2 with hh1 | hh1
    · exact Or.inl hh1
    · exact Or.inr (le_of_lt hh1)
  -- the disc structure of `K` in the plane of the shadow
  have hKdisc' : ∃ e' : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e' ∧ Set.range e' = xyL '' K ∧
      Set.range (fun θ : ℝ => e' (Work.CoreTopology.circlePoint θ)) = frontier (xyL '' K) := by
    have hcont : Continuous fun z : Metric.closedBall (0 : ℂ) 1 => xyL (e z) :=
      continuous_xyL.comp e.continuous
    refine ⟨⟨fun z => xyL (e z), hcont⟩, ?_, ?_, ?_⟩
    · exact fun z z' hz => he_inj (xyL.injective hz)
    · show Set.range (fun z : Metric.closedBall (0 : ℂ) 1 => xyL (e z)) = xyL '' K
      have h1 : Set.range (fun z : Metric.closedBall (0 : ℂ) 1 => xyL (e z))
          = xyL '' Set.range e := by
        simpa [Function.comp_def] using Set.range_comp (fun X : ℝ × ℝ => xyL X) e
      rw [h1, he_rangeK]
    · show Set.range (fun θ : ℝ => xyL (e (Work.CoreTopology.circlePoint θ)))
          = frontier (xyL '' K)
      have h1 : Set.range (fun θ : ℝ => xyL (e (Work.CoreTopology.circlePoint θ)))
          = xyL '' Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) := by
        simpa [Function.comp_def] using Set.range_comp (fun X : ℝ × ℝ => xyL X)
          (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ))
      rw [h1, he_bdryK]
      exact xyL_image_frontier K
  obtain ⟨e', he'_inj, he'_range, he'_bdry⟩ := hKdisc'
  have hKdisc'' : ∃ e' : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)),
      Function.Injective e' ∧ Set.range e' = xyL '' K ∧
      Set.range (fun θ : ℝ => e' (Work.CoreTopology.circlePoint θ)) = frontier (xyL '' K) :=
    ⟨e', he'_inj, he'_range, he'_bdry⟩
  have hKcl : closure (interior K) = K := by
    have h1 := tls_closure_interior_eq_of_discParam he'_inj he'_range he'_bdry
    rw [← xyL_image_interior K] at h1
    rw [← xyL_image_closure (interior K)] at h1
    exact (Set.image_injective.mpr xyL.injective) h1
  -- the planar facts transported to the plane of the shadow
  have hZclosure' : closure (xyL '' Z) = xyL '' K := by
    rw [hKdef]
    exact (xyL_image_closure Z).symm
  have hintZ'' : interior (xyL '' K) ⊆ xyL '' Z := by
    rw [← xyL_image_interior K]
    exact Set.image_mono hintZ'
  have hKcl' : closure (interior (xyL '' K)) = xyL '' K := by
    rw [← xyL_image_interior K, ← xyL_image_closure (interior K), hKcl]
  -- the two heights in the plane of the shadow
  have hα' : ContinuousOn (fun X : EuclideanSpace ℝ (Fin 2) =>
      Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (xyL.symm X)) (xyL '' K) := by
    refine ContinuousOn.comp (t := Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)
      (f := fun X : EuclideanSpace ℝ (Fin 2) => (xyL.symm : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ) X)
      hcontMin (xyLC.symm.continuous.continuousOn) ?_
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := hX
    simpa using hboxsub hY
  have hβ' : ContinuousOn (fun X : EuclideanSpace ℝ (Fin 2) =>
      Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ (xyL.symm X)) (xyL '' K) := by
    refine ContinuousOn.comp (t := Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ)
      (f := fun X : EuclideanSpace ℝ (Fin 2) => (xyL.symm : EuclideanSpace ℝ (Fin 2) → ℝ × ℝ) X)
      hcontMax (xyLC.symm.continuous.continuousOn) ?_
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := hX
    simpa using hboxsub hY
  have hαβ' : ∀ X ∈ xyL '' K, (fun X : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (xyL.symm X)) X
      ≤ (fun X : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ (xyL.symm X)) X := by
    rintro X ⟨Y, hY, rfl⟩
    have hY' : Y ∈ Work.Drive.Mono.FiberModel.boxShadow s c σ v ℓ := hboxsub hY
    have h2 : Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ Y ∈
        ζ '' Work.Drive.Mono.FiberModel.fibre v ℓ s c σ Y :=
      Work.Drive.Mono.FiberModel.fMin_mem hY'
    rw [hfib Y hY'] at h2
    exact h2.2
  have hlt' : ∀ X ∈ interior (xyL '' K), (fun X : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (xyL.symm X)) X
      < (fun X : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ (xyL.symm X)) X := by
    intro X hX
    rw [← xyL_image_interior K] at hX
    obtain ⟨Y, hY, rfl⟩ := hX
    exact hstrict Y (hintKsubW hY)
  -- the strict region and the solid
  set A : Set R3 := {p : R3 | Work.Drive.Mono.cproj p ∈ xyL '' Z ∧
      Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (xyL.symm (Work.Drive.Mono.cproj p))
        < Work.Drive.Mono.clast p ∧
      Work.Drive.Mono.clast p
        < Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ (xyL.symm (Work.Drive.Mono.cproj p))}
    with hAdef
  set B : Set R3 := {p : R3 | Work.Drive.Mono.cproj p ∈ xyL '' K ∧
      Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (xyL.symm (Work.Drive.Mono.cproj p))
        ≤ Work.Drive.Mono.clast p ∧
      Work.Drive.Mono.clast p
        ≤ Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ (xyL.symm (Work.Drive.Mono.cproj p))}
    with hBdef
  have hAB : frontier A = frontier B := by
    rw [hAdef, hBdef]
    exact frontierStrictOverEq (Z := xyL '' Z) (K := xyL '' K)
      (α := fun X : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (xyL.symm X))
      (β := fun X : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ (xyL.symm X))
      hZclosure' hintZ'' hKcl' hα' hβ' hαβ' hlt'
  have hBsphere : Work.InnermostDisk.IsEmbeddedSphere (frontier B) := by
    rw [hBdef]
    exact solidOverDiscSphere (K := xyL '' K)
      (α := fun X : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.Mono.FiberModel.fMin ζ v ℓ s c σ (xyL.symm X))
      (β := fun X : EuclideanSpace ℝ (Fin 2) =>
        Work.Drive.Mono.FiberModel.fMax ζ v ℓ s c σ (xyL.symm X))
      hKdisc'' hα' hβ' hαβ' hlt'
  have hIm : fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζker ''
      Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam = A := by
    rw [hAdef, hZdef]
    exact image_fibreHomeo_tiltedLevelRemoved (s := s) (c := c) (σ := σ) (u := u)
      (h := h) (lam := lam) hs hv hℓv hℓne hζker hfib hstrict
  have hAsphere : Work.InnermostDisk.IsEmbeddedSphere (frontier A) := by
    rw [hAB]
    exact hBsphere
  have h1 : fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζker ''
      frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) = frontier A := by
    rw [Homeomorph.image_frontier, hIm]
  have hsymm : (fibreHomeo (v := v) (ℓ := ℓ) hv hℓv hℓne hζker).symm '' frontier A
      = frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) := by
    rw [← h1, Set.image_image]
    simp
  rw [← hsymm]
  exact Work.InnermostDisk.isEmbeddedSphere_image_homeomorph _ hAsphere

end

end Work.Drive.Mono.WindowCase


