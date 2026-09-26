import Mathlib
import Submission.Work.InnermostDisk.Defs
import Submission.Work.TorusCover.Main
import Submission.Work.InnermostDisk.not_isEssential_iff_homotopic_const
import Submission.Work.InnermostDisk.polarCoord_surjective
import Submission.Work.InnermostDisk.exp_eq_exp_mul_I_exists_int
import Submission.Work.InnermostDisk.descend_continuousMap

/-!
# Inessential loops of a torus bound discs in the surface

Pardon's topological core needs the fact that a closed curve `α` on the surface `F = P.carrier`
of a parametrised torus that is *inessential* (winding vector zero) bounds a disc **in `F`**:
`Work.InnermostDisk.BoundsDiscInSurface P α`.

The mathematics is the covering-space description of `F = ℝ²/2πℤ²`: a curve with vanishing
winding vector lifts to a `2π`-periodic map `Λ : ℝ → ℝ²` into the parameter plane, and then the
"cone" over that lift, namely

`(r, θ) ↦ P.psi (r * Θ θ) (r * Φ θ)`,

is a continuous map of the closed unit disc `𝔻` into `F` whose boundary (`r = 1`) is
`θ ↦ P.psi (Θ θ) (Φ θ) = α.γ θ`.

The technical point is that the formula above lives on the polar-coordinate rectangle
`[0,1] × [0,2π]` and must be descended to `𝔻` through the (surjective, continuous, hence
quotient) map `(r,θ) ↦ r exp (iθ)`; the descent is legitimate exactly because the lift `Λ` is
`2π`-periodic.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.CoreTopology

namespace Work.InnermostDisk

noncomputable section


/-! ## The polar-coordinate rectangle and the map `(r,θ) ↦ r exp (iθ)` -/

/-- The rectangle `[0,1] × [0,2π]` of polar coordinates of the closed unit disc. -/
abbrev polarBox : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)

private lemma isCompact_polarBox : IsCompact polarBox :=
  isCompact_Icc.prod isCompact_Icc

/-- Polar coordinates `(r, θ) ↦ r · exp (iθ)`. -/
private def polarMapFun (p : ℝ × ℝ) : ℂ := (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)

private lemma continuous_polarMapFun : Continuous polarMapFun := by
  show Continuous fun p : ℝ × ℝ => (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)
  fun_prop

private lemma norm_polarMapFun {p : ℝ × ℝ} (h : 0 ≤ p.1) : ‖polarMapFun p‖ = p.1 := by
  rw [polarMapFun, norm_mul, Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self h,
    Complex.norm_exp_ofReal_mul_I, mul_one]

private lemma polarMapFun_mem {p : ℝ × ℝ} (hp : p ∈ polarBox) :
    polarMapFun p ∈ Metric.closedBall (0 : ℂ) 1 := by
  rw [polarBox, Set.mem_prod, Set.mem_Icc] at hp
  rw [Metric.mem_closedBall, dist_zero_right, norm_polarMapFun hp.1.1]
  exact hp.1.2

/-- `(r,θ) ↦ r exp (iθ)` as a map of the polar rectangle onto the closed unit disc. -/
private def boxToDisc : polarBox → Metric.closedBall (0 : ℂ) 1 :=
  fun p => ⟨polarMapFun p.1, polarMapFun_mem p.2⟩

private lemma continuous_boxToDisc : Continuous boxToDisc :=
  Continuous.subtype_mk (continuous_polarMapFun.comp continuous_subtype_val)
    (fun p => polarMapFun_mem p.2)

private lemma boxToDisc_surjective : Function.Surjective boxToDisc := by
  intro z
  have hz : ‖(z : ℂ)‖ ≤ 1 := by
    have h := Metric.mem_closedBall.mp z.2
    rwa [dist_zero_right] at h
  obtain ⟨r, θ, hr0, hr1, hθ0, hθ1, hval⟩ := polarCoord_surjective (z : ℂ) hz
  refine ⟨⟨(r, θ), ?_⟩, ?_⟩
  · exact ⟨⟨hr0, hr1⟩, ⟨hθ0, hθ1⟩⟩
  · apply Subtype.ext
    show polarMapFun (r, θ) = (z : ℂ)
    rw [polarMapFun]
    exact hval

/-! ## The cone over a periodic lift, on the polar rectangle -/

/-- The "cone" over a lift `Λ` of a closed curve, on the polar rectangle: at radius `r` and
angle `θ` it is the point of `F` with parameters `r • Λ θ`.  For `r = 1` this is the curve
itself, so the boundary of the disc is the curve `α`. -/
private def rectMap (P : ParamTorus) (Λ : ℝ → ℝ × ℝ) (k : polarBox) : R3 :=
  P.psi (k.1.1 * (Λ k.1.2).1) (k.1.1 * (Λ k.1.2).2)

private lemma continuous_rectMap (P : ParamTorus) {Λ : ℝ → ℝ × ℝ} (hcont : Continuous Λ) :
    Continuous (rectMap P Λ) := by
  have h1 : Continuous fun k : polarBox => k.1.1 := continuous_fst.comp continuous_subtype_val
  have h2 : Continuous fun k : polarBox => k.1.2 := continuous_snd.comp continuous_subtype_val
  have hΘ : Continuous fun k : polarBox => (Λ k.1.2).1 := hcont.fst.comp h2
  have hΦ : Continuous fun k : polarBox => (Λ k.1.2).2 := hcont.snd.comp h2
  have harg : Continuous fun k : polarBox =>
      ((k.1.1 * (Λ k.1.2).1, k.1.1 * (Λ k.1.2).2) : ℝ × ℝ) :=
    Continuous.prodMk (h1.mul hΘ) (h1.mul hΦ)
  exact (P.cont.comp harg).congr (fun k => rfl)

/-- Two points of the polar rectangle that represent the same point of the disc give the same
point of `F`: this is where `2π`-periodicity of the lift `Λ` is used. -/
private lemma rectMap_fiber (P : ParamTorus) {Λ : ℝ → ℝ × ℝ}
    (hper : ∀ t : ℝ, Λ (t + 2 * Real.pi) = Λ t) {x y : polarBox}
    (h : boxToDisc x = boxToDisc y) : rectMap P Λ x = rectMap P Λ y := by
  have hval : polarMapFun x.1 = polarMapFun y.1 := congrArg Subtype.val h
  have hx1 : 0 ≤ x.1.1 := x.2.1.1
  have hy1 : 0 ≤ y.1.1 := y.2.1.1
  have hrs : x.1.1 = y.1.1 := by
    have hnorm := congrArg norm hval
    rwa [norm_polarMapFun hx1, norm_polarMapFun hy1] at hnorm
  rcases eq_or_ne x.1.1 0 with h0 | h0
  · have hy0 : y.1.1 = 0 := by rw [← hrs]; exact h0
    rw [rectMap, rectMap, h0, hy0]
    simp
  · have hc : (x.1.1 : ℂ) ≠ 0 := by
      intro hczero
      exact h0 (Complex.ofReal_inj.mp (hczero.trans Complex.ofReal_zero.symm))
    have hexp : Complex.exp ((x.1.2 : ℂ) * Complex.I)
        = Complex.exp ((y.1.2 : ℂ) * Complex.I) := by
      have hh := hval
      simp only [polarMapFun] at hh
      rw [← hrs] at hh
      exact mul_left_cancel₀ hc hh
    obtain ⟨n, hn⟩ := exp_eq_exp_mul_I_exists_int hexp
    have hΛ : Λ x.1.2 = Λ y.1.2 := by
      have hp := (show Function.Periodic Λ (2 * Real.pi) from hper).int_mul n y.1.2
      rw [← hn] at hp
      exact hp
    rw [rectMap, rectMap, hrs, congrArg Prod.fst hΛ, congrArg Prod.snd hΛ]

/-! ## Descending the cone to a disc in the surface -/

/-- **The cone over a `2π`-periodic lift of `α` is a disc in the surface bounded by `α`.**

If `Λ = (Θ, Φ)` is a continuous `2π`-periodic lift of the closed curve `α` (i.e.
`P.psi (Θ t) (Φ t) = α.γ t` for all `t`), then `α` bounds an embedded disc in `F`: the map
`(r, θ) ↦ P.psi (r Θ θ) (r Φ θ)` descends through the quotient map `(r,θ) ↦ r exp (iθ)` of the
polar rectangle onto the disc. -/
private lemma exists_bounding_map_of_periodic_lift (P : ParamTorus) (α : ClosedCurve P)
    (Λ : ℝ → ℝ × ℝ) (hcont : Continuous Λ)
    (hlift : ∀ t : ℝ, P.psi (Λ t).1 (Λ t).2 = α.γ t)
    (hper : ∀ t : ℝ, Λ (t + 2 * Real.pi) = Λ t) :
    ∃ e : C(Disc, P.carrier), ∀ θ : ℝ, (e (circlePoint θ) : R3) = α.γ θ := by
  have : CompactSpace polarBox := isCompact_iff_compactSpace.mp isCompact_polarBox
  obtain ⟨e₀, he₀cont, he₀⟩ :=
    descend_continuousMap continuous_boxToDisc boxToDisc_surjective
      (continuous_rectMap P hcont) (fun _ _ h => rectMap_fiber P hper h)
  have hmem : ∀ z : Disc, e₀ z ∈ P.carrier := by
    intro z
    obtain ⟨k, hk⟩ := boxToDisc_surjective z
    rw [← hk, he₀ k]
    exact P.psi_mem_carrier _ _
  refine ⟨⟨fun z => ⟨e₀ z, hmem z⟩, he₀cont.subtype_mk hmem⟩, ?_⟩
  intro θ
  change e₀ (circlePoint θ) = α.γ θ
  obtain ⟨k, hk1, hk2⟩ := Work.TorusCover.exists_int_sub_mem_Icc θ
  set θ₀ : ℝ := θ - (k : ℝ) * (2 * Real.pi) with hθ₀def
  have hmem' : ((1 : ℝ), θ₀) ∈ polarBox :=
    ⟨⟨zero_le_one, le_refl (1 : ℝ)⟩, ⟨hk1, hk2⟩⟩
  have hθeq : θ = θ₀ + (k : ℝ) * (2 * Real.pi) := by rw [hθ₀def]; ring
  have hα : α.γ θ₀ = α.γ θ := by
    have hp := (show Function.Periodic α.γ (2 * Real.pi) from α.periodic).int_mul k θ₀
    rw [← hθeq] at hp
    exact hp.symm
  have hbox : boxToDisc ⟨((1 : ℝ), θ₀), hmem'⟩ = circlePoint θ := by
    apply Subtype.ext
    show polarMapFun ((1 : ℝ), θ₀) = Complex.exp ((θ : ℂ) * Complex.I)
    rw [polarMapFun, Complex.ofReal_one, one_mul]
    rw [Complex.exp_eq_exp_iff_exists_int]
    refine ⟨-k, ?_⟩
    have hreal : θ₀ = θ + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by
      rw [hθ₀def]; push_cast; ring
    have hcast : (θ₀ : ℂ) = (θ : ℂ) + ((-k : ℤ) : ℂ) * (2 * (Real.pi : ℂ)) := by
      exact_mod_cast hreal
    rw [hcast]
    ring
  have hrect : rectMap P Λ ⟨((1 : ℝ), θ₀), hmem'⟩ = α.γ θ := by
    rw [rectMap, one_mul, one_mul, hlift θ₀, hα]
  rw [← hbox, he₀]
  exact hrect

/-! ## From a non-essential closed curve to a periodic lift -/

/-- **A closed curve of `F` with vanishing winding vector admits a `2π`-periodic lift** to the
parameter plane.  Such a curve exists because the parametrisation is a covering map
(`Work.TorusCover.ParamTorus_exists_liftOf`), and any lift has winding vector `0` because the
curve is inessential. -/
private lemma exists_periodic_lift_of_not_isEssential (P : ParamTorus) {α : ClosedCurve P}
    (h : ¬ IsEssential P α) :
    ∃ Λ : ℝ → ℝ × ℝ, Continuous Λ ∧ (∀ t : ℝ, P.psi (Λ t).1 (Λ t).2 = α.γ t) ∧
      ∀ t : ℝ, Λ (t + 2 * Real.pi) = Λ t := by
  obtain ⟨L⟩ := Work.TorusCover.ParamTorus_exists_liftOf P α
  have hwind : L.winding = (0, 0) := by
    by_contra hne
    exact h ⟨L, hne⟩
  refine ⟨fun t => (L.Θ t, L.Φ t), L.contΘ.prodMk L.contΦ, fun t => L.lifts t, ?_⟩
  intro t
  have hp := L.period_shift_winding t
  rw [hwind] at hp
  show (L.Θ (t + 2 * Real.pi), L.Φ (t + 2 * Real.pi)) = (L.Θ t, L.Φ t)
  exact Prod.ext (by simpa using hp.1) (by simpa using hp.2)

/-! ## The main statement -/

/-- **An inessential closed curve of a torus bounds a disc in the surface.**

If the closed curve `α` of `F = P.carrier` has zero winding vector, then its lift to the
parameter plane is `2π`-periodic, and the cone over that lift is a continuous map of the closed
disc into `F` whose boundary is `α`.  Hence `α` is inessential in Pardon's sense
(`Work.InnermostDisk.BoundsDiscInSurface`). -/
theorem boundsDiscInSurface_of_not_isEssential (P : Work.CoreTopology.ParamTorus)
    {α : Work.CoreTopology.ClosedCurve P} (h : ¬ Work.CoreTopology.IsEssential P α) :
    Work.InnermostDisk.BoundsDiscInSurface P α := by
  obtain ⟨Λ, hcont, hlift, hper⟩ := exists_periodic_lift_of_not_isEssential P h
  exact exists_bounding_map_of_periodic_lift P α Λ hcont hlift hper

end

end Work.InnermostDisk
