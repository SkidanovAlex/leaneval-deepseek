import Mathlib
import Submission.Work.Drive.Mono.CylRegionDefs
import Submission.Work.Drive.Mono.cylRegion_e_mem_interior
import Submission.Work.CoreTopology.Disk
import Submission.Work.Drive.Mono.WindowCase.CupDefs
import Submission.Work.Drive.Mono.WindowCase.cupE_injective
import Submission.Work.Drive.Mono.WindowCase.cupE_range

/-!
# The cup over a plane disc is parametrised by the disc

`Work.Drive.Mono.WindowCase.exists_cupParam`: if `K ⊆ ℝ²` is a plane disc, parametrised by an
injective continuous map `e` of the closed unit disc `𝔻 = Metric.closedBall 0 1` whose boundary
circle maps onto `frontier K`, and `g : K → ℝ` is continuous and nonnegative, then the **cup**

`{(x,0) | x ∈ K} ∪ {(x,y) | x ∈ frontier K, 0 ≤ y ≤ g x}`

is the image of an injective continuous map `E : 𝔻 → ℝ³`, and the boundary circle lands on the
top rim `(e (circlePoint θ), g (e (circlePoint θ)))`.

The parametrisation is the collapse-aware, **direction dependent** one of `CupDefs`:
`Work.Drive.Mono.WindowCase.cupE`, whose threshold `cupG e g z = 1/2 + 1/(2(1 + g (e (cupDir z))))`
equals `1` exactly where `g` vanishes at the boundary point in the direction of `z`.  The naive
collar aligned map collapses the whole fibre over such a boundary point onto the base and is not
injective; the direction dependent threshold avoids this.

## Contents

* `cupAux_continuous_cupE` (this file): `cupE e g` is continuous.  Both branches are continuous
  where they are used (the bottom branch `cupBottom` is continuous *everywhere*, including the
  origin, thanks to the clamping `max (cupG e g z) ‖z‖ ≥ 1/2`; the wall branch is continuous on
  the wall region), and they agree on the switch `‖z‖ = cupG e g z`, so the two closed regions
  `{‖z‖ ≤ cupG e g z}` and `{cupG e g z ≤ ‖z‖}` can be glued.  The algebraic identity
  `1 - cupG e g z = g / (2(1+g))` rewrites the wall height as `2(1+g)(‖z‖ - cupG e g z)` on the
  wall region, which is where continuity at the switch comes from.
* `cupE_circlePoint` (this file): on the boundary circle the parametrisation lands on the top rim.
* `Work.Drive.Mono.WindowCase.cupE_injective` and `...cupE_range` (separate files): injectivity and
  the range.
-/

namespace Work.Drive.Mono.WindowCase

open LeanEval.KnotTheory.PardonDistortion Set Filter Topology

noncomputable section

local notation "𝔻" => Metric.closedBall (0 : ℂ) 1

variable {K : Set (EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}



/-! ## 1. Elementary facts about the threshold -/

theorem cupAux_arg_nonneg (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hg0 : ∀ x ∈ K, 0 ≤ g x) (z : 𝔻) :
    0 ≤ g (e (cupDir z)) :=
  hg0 _ (by rw [← he_range]; exact Set.mem_range_self _)

theorem cupAux_half_lt (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hg0 : ∀ x ∈ K, 0 ≤ g x) (z : 𝔻) :
    (1 : ℝ) / 2 < cupG e g z :=
  cupG_half_lt (cupAux_arg_nonneg e he_range hg0 z)

theorem cupAux_pos (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hg0 : ∀ x ∈ K, 0 ≤ g x) (z : 𝔻) :
    0 < cupG e g z :=
  lt_trans (by norm_num) (cupAux_half_lt e he_range hg0 z)

theorem cupAux_norm_le_one (z : 𝔻) : ‖(z : ℂ)‖ ≤ 1 := by
  have h := z.2
  rwa [Metric.mem_closedBall, dist_zero_right] at h

/-! ## 2. Continuity of the threshold away from the origin -/

theorem cupAux_continuousAt_cupDir {z₀ : 𝔻} (hz₀ : (z₀ : ℂ) ≠ 0) :
    ContinuousAt (fun z : 𝔻 => cupDir z) z₀ := by
  have hnum : ContinuousAt (fun z : 𝔻 => (z : ℂ)) z₀ := continuous_subtype_val.continuousAt
  have hden : ContinuousAt (fun z : 𝔻 => ‖(z : ℂ)‖) z₀ :=
    (continuous_norm.comp continuous_subtype_val).continuousAt
  have hne : ‖(z₀ : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hz₀
  have hdenC : ContinuousAt (fun z : 𝔻 => ((‖(z : ℂ)‖ : ℝ) : ℂ)) z₀ :=
    Complex.continuous_ofReal.continuousAt.comp hden
  have hneC : ((‖(z₀ : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
    simpa [Complex.ofReal_eq_zero] using hne
  show Tendsto (fun z : 𝔻 => cupDir z) (𝓝 z₀) (𝓝 (cupDir z₀))
  rw [tendsto_subtype_rng]
  show Tendsto (fun z : 𝔻 => (z : ℂ) / ‖(z : ℂ)‖) (𝓝 z₀)
    (𝓝 ((z₀ : ℂ) / ‖(z₀ : ℂ)‖))
  exact hnum.div hdenC hneC

theorem cupAux_continuousAt_g (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hgc : ContinuousOn g K) {z₀ : 𝔻}
    (hz₀ : (z₀ : ℂ) ≠ 0) : ContinuousAt (fun z : 𝔻 => g (e (cupDir z))) z₀ := by
  let φ : 𝔻 → EuclideanSpace ℝ (Fin 2) := fun z => e (cupDir z)
  have hdir : ContinuousAt (fun z : 𝔻 => cupDir z) z₀ := cupAux_continuousAt_cupDir hz₀
  have hφ : ContinuousAt φ z₀ := e.continuous.continuousAt.comp hdir
  have h1 : ContinuousWithinAt g K (φ z₀) :=
    hgc.continuousWithinAt (by
      have hz : φ z₀ = e (cupDir z₀) := rfl
      rw [hz, ← he_range]; exact Set.mem_range_self _)
  have h2 : ContinuousWithinAt φ univ z₀ := hφ.continuousWithinAt
  have h3 : MapsTo φ univ K := fun z _ => by
    have hz : φ z = e (cupDir z) := rfl
    rw [hz, ← he_range]; exact Set.mem_range_self _
  exact (h1.comp h2 h3).continuousAt univ_mem

theorem cupAux_continuousAt_cupG (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x)
    {z₀ : 𝔻} (hz₀ : (z₀ : ℂ) ≠ 0) : ContinuousAt (cupG e g) z₀ := by
  have hx := cupAux_continuousAt_g e he_range hgc hz₀
  have hx0 : 0 ≤ g (e (cupDir z₀)) := cupAux_arg_nonneg e he_range hg0 z₀
  have hden : (2 : ℝ) * (1 + g (e (cupDir z₀))) ≠ 0 := by linarith
  have hinv : ContinuousAt (fun z : 𝔻 => 1 / (2 * (1 + g (e (cupDir z))))) z₀ :=
    (continuousAt_const : ContinuousAt (fun _ : 𝔻 => (1 : ℝ)) z₀).div
      ((hx.const_add 1).const_mul 2) hden
  show ContinuousAt (fun z : 𝔻 => (1 : ℝ) / 2 + 1 / (2 * (1 + g (e (cupDir z))))) z₀
  exact continuousAt_const.add hinv

/-! ## 3. Continuity of the underlying map `z ↦ z / max (G z) ‖z‖` -/

theorem cupAux_norm_div_le (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hg0 : ∀ x ∈ K, 0 ≤ g x) (z : 𝔻) :
    ‖(z : ℂ) / max (cupG e g z) ‖(z : ℂ)‖‖ ≤ 2 * ‖(z : ℂ)‖ := by
  have hr : (0 : ℝ) ≤ ‖(z : ℂ)‖ := norm_nonneg _
  have hG : (1 : ℝ) / 2 < cupG e g z := cupAux_half_lt e he_range hg0 z
  rw [norm_div, Complex.norm_of_nonneg (le_trans hr (le_max_right _ _))]
  by_cases h : ‖(z : ℂ)‖ ≤ cupG e g z
  · rw [max_eq_left h, div_le_iff₀ (lt_trans (by norm_num) hG)]
    nlinarith
  · rw [max_eq_right (le_of_lt (lt_of_not_ge h))]
    refine le_trans (div_self_le_one hr) ?_
    have h' : cupG e g z ≤ ‖(z : ℂ)‖ := le_of_lt (lt_of_not_ge h)
    have h'' : (1 : ℝ) / 2 < ‖(z : ℂ)‖ := lt_of_lt_of_le hG h'
    linarith

theorem cupAux_continuous_F (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x) :
    Continuous (fun z : 𝔻 => (z : ℂ) / max (cupG e g z) ‖(z : ℂ)‖) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  by_cases hz₀ : (z₀ : ℂ) = 0
  · have hz : z₀ = 0 := Subtype.ext hz₀
    rw [hz]
    have hF0 : (0 : ℂ) / max (cupG e g (0 : 𝔻)) ‖((0 : 𝔻) : ℂ)‖ = 0 := by simp
    show Tendsto (fun z : 𝔻 => (z : ℂ) / max (cupG e g z) ‖(z : ℂ)‖) (𝓝 0)
      (𝓝 ((0 : ℂ) / max (cupG e g (0 : 𝔻)) ‖((0 : 𝔻) : ℂ)‖))
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hf0 : ∀ z : 𝔻,
        ‖(z : ℂ) / max (cupG e g z) ‖(z : ℂ)‖ -
          (0 : ℂ) / max (cupG e g (0 : 𝔻)) ‖((0 : 𝔻) : ℂ)‖‖
          = ‖(z : ℂ) / max (cupG e g z) ‖(z : ℂ)‖‖ := by
      intro z; rw [hF0, sub_zero]
    have h2t : Tendsto (fun z : 𝔻 => (2 : ℝ) * ‖(z : ℂ)‖) (𝓝 0) (𝓝 0) := by
      have h2 : ContinuousAt (fun z : 𝔻 => (2 : ℝ) * ‖(z : ℂ)‖) 0 :=
        ((continuous_norm.comp continuous_subtype_val).continuousAt).const_mul 2
      have h20 : (2 : ℝ) * ‖((0 : 𝔻) : ℂ)‖ = 0 := by simp
      have ht := h2.tendsto
      rwa [h20] at ht
    exact squeeze_zero (fun z => norm_nonneg _)
      (fun z => by rw [hf0 z]; exact cupAux_norm_div_le e he_range hg0 z) h2t
  · have hG := cupAux_continuousAt_cupG e he_range hgc hg0 hz₀
    have hn : ContinuousAt (fun z : 𝔻 => ‖(z : ℂ)‖) z₀ :=
      (continuous_norm.comp continuous_subtype_val).continuousAt
    have hmax : ContinuousAt (fun z : 𝔻 => max (cupG e g z) ‖(z : ℂ)‖) z₀ := hG.sup hn
    have hne : max (cupG e g z₀) ‖(z₀ : ℂ)‖ ≠ 0 := by
      have h1 := cupAux_half_lt e he_range hg0 z₀
      have h2 := le_max_left (cupG e g z₀) ‖(z₀ : ℂ)‖
      linarith
    have hmaxC : ContinuousAt (fun z : 𝔻 => ((max (cupG e g z) ‖(z : ℂ)‖ : ℝ) : ℂ)) z₀ :=
      Complex.continuous_ofReal.continuousAt.comp hmax
    have hneC : ((max (cupG e g z₀) ‖(z₀ : ℂ)‖ : ℝ) : ℂ) ≠ 0 := by
      simpa [Complex.ofReal_eq_zero] using hne
    exact continuous_subtype_val.continuousAt.div hmaxC hneC

theorem cupAux_continuous_cupScaled (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x) :
    Continuous (cupScaled e g) :=
  (cupAux_continuous_F e he_range hgc hg0).subtype_coind (fun z => (cupScaled e g z).2)

theorem cupAux_continuous_cupBottom (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x) :
    Continuous (cupBottom e g) :=
  continuous_cmk.comp
    ((e.continuous.comp (cupAux_continuous_cupScaled e he_range hgc hg0)).prodMk
      continuous_const)

/-! ## 4. The wall branch: continuity via the simplified height -/

/-- The wall branch with the height `g · (r - G)/(1 - G)` simplified, using
`1 - G = g/(2(1+g))`.  It agrees with `cupWall` on the wall region and is continuous there. -/
def cupAuxWallS (e : C(𝔻, EuclideanSpace ℝ (Fin 2))) (g : EuclideanSpace ℝ (Fin 2) → ℝ)
    (z : 𝔻) : EuclideanSpace ℝ (Fin 3) :=
  cmk (e (cupDir z)) (2 * (1 + g (e (cupDir z))) * (‖(z : ℂ)‖ - cupG e g z))

theorem cupAux_continuousOn_cupAuxWallS (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x) :
    ContinuousOn (cupAuxWallS e g) {z : 𝔻 | (z : ℂ) ≠ 0} := by
  intro z hz
  have hdir : ContinuousAt (fun z : 𝔻 => cupDir z) z := cupAux_continuousAt_cupDir hz
  have hEc : ContinuousAt (fun z : 𝔻 => e (cupDir z)) z :=
    e.continuous.continuousAt.comp hdir
  have hgEc : ContinuousAt (fun z : 𝔻 => g (e (cupDir z))) z :=
    cupAux_continuousAt_g e he_range hgc hz
  have hG : ContinuousAt (cupG e g) z := cupAux_continuousAt_cupG e he_range hgc hg0 hz
  have hn : ContinuousAt (fun z : 𝔻 => ‖(z : ℂ)‖) z :=
    (continuous_norm.comp continuous_subtype_val).continuousAt
  have hheight :
      ContinuousAt (fun z : 𝔻 => 2 * (1 + g (e (cupDir z))) * (‖(z : ℂ)‖ - cupG e g z)) z :=
    (((hgEc.const_add 1).const_mul 2).mul (hn.sub hG))
  show ContinuousWithinAt (cupAuxWallS e g) {z : 𝔻 | (z : ℂ) ≠ 0} z
  exact (continuous_cmk.continuousAt.comp (hEc.prodMk hheight)).continuousWithinAt

theorem cupAux_cupWall_eq (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hg0 : ∀ x ∈ K, 0 ≤ g x) {z : 𝔻}
    (hz : cupG e g z ≤ ‖(z : ℂ)‖) : cupWall e g z = cupAuxWallS e g z := by
  have hm0 : 0 ≤ g (e (cupDir z)) := cupAux_arg_nonneg e he_range hg0 z
  have hrle : ‖(z : ℂ)‖ ≤ 1 := cupAux_norm_le_one z
  have hheight :
      g (e (cupDir z)) * ((‖(z : ℂ)‖ - cupG e g z) / (1 - cupG e g z))
        = 2 * (1 + g (e (cupDir z))) * (‖(z : ℂ)‖ - cupG e g z) := by
    by_cases hm : g (e (cupDir z)) = 0
    · have hG1 : cupG e g z = 1 := (cupG_eq_one_iff hm0).mpr hm
      have hr1 : ‖(z : ℂ)‖ = 1 := le_antisymm hrle (by rw [hG1] at hz; exact hz)
      rw [hm, hG1, hr1]
      norm_num
    · have hGlt : cupG e g z < 1 := by
        have h1 : 0 < g (e (cupDir z)) := lt_of_le_of_ne hm0 (Ne.symm hm)
        have := cupG_le_one hm0
        have h2 : cupG e g z ≠ 1 := fun h => hm ((cupG_eq_one_iff hm0).mp h)
        exact lt_of_le_of_ne this h2
      have h1G : (1 : ℝ) - cupG e g z
          = g (e (cupDir z)) / (2 * (1 + g (e (cupDir z)))) := by
        simp only [cupG]
        field_simp
        ring
      rw [h1G]
      field_simp
  rw [cupWall, cupAuxWallS, cmk_eq_cmk_iff]
  exact ⟨rfl, hheight⟩

/-! ## 5. Closedness of the two branches and the pasting -/

theorem cupAux_isOpen_cupG_lt (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x) :
    IsOpen {z : 𝔻 | cupG e g z < ‖(z : ℂ)‖} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hzval : cupG e g z < ‖(z : ℂ)‖ := hz
  have hz0 : (z : ℂ) ≠ 0 := by
    intro h0
    have h1 : cupG e g z < 0 := by simpa [h0] using hzval
    have h2 := cupAux_pos e he_range hg0 z
    linarith
  have hcont : ContinuousAt (fun z : 𝔻 => cupG e g z - ‖(z : ℂ)‖) z :=
    (cupAux_continuousAt_cupG e he_range hgc hg0 hz0).sub
      ((continuous_norm.comp continuous_subtype_val).continuousAt)
  have hlt : cupG e g z - ‖(z : ℂ)‖ < 0 := by linarith
  have hev : ∀ᶠ z' : 𝔻 in 𝓝 z, cupG e g z' - ‖(z' : ℂ)‖ < 0 :=
    hcont.tendsto.eventually (isOpen_Iio.mem_nhds hlt)
  filter_upwards [hev] with z' hz'
  show cupG e g z' < ‖(z' : ℂ)‖
  linarith

theorem cupAux_isClosed_le (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x) :
    IsClosed {z : 𝔻 | ‖(z : ℂ)‖ ≤ cupG e g z} := by
  have h := (cupAux_isOpen_cupG_lt e he_range hgc hg0).isClosed_compl
  rwa [show {z : 𝔻 | cupG e g z < ‖(z : ℂ)‖}ᶜ = {z : 𝔻 | ‖(z : ℂ)‖ ≤ cupG e g z} from by
    ext z; simp [not_lt]] at h

theorem cupAux_isOpen_norm_lt (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x) :
    IsOpen {z : 𝔻 | ‖(z : ℂ)‖ < cupG e g z} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  by_cases hz0 : (z : ℂ) = 0
  · have hz_eq : z = 0 := Subtype.ext hz0
    rw [hz_eq]
    refine Filter.mem_of_superset
      (Metric.ball_mem_nhds (0 : 𝔻) (by norm_num : (0 : ℝ) < 1 / 4)) ?_
    intro z' hz'
    have h1 : ‖(z' : ℂ)‖ < 1 / 4 := by
      simpa [Metric.mem_ball, Subtype.dist_eq, dist_zero_right] using hz'
    have h2 : (1 : ℝ) / 2 < cupG e g z' := cupAux_half_lt e he_range hg0 z'
    show ‖(z' : ℂ)‖ < cupG e g z'
    linarith
  · have hzval : ‖(z : ℂ)‖ < cupG e g z := hz
    have hcont : ContinuousAt (fun z : 𝔻 => ‖(z : ℂ)‖ - cupG e g z) z :=
      ((continuous_norm.comp continuous_subtype_val).continuousAt).sub
        (cupAux_continuousAt_cupG e he_range hgc hg0 hz0)
    have hlt : ‖(z : ℂ)‖ - cupG e g z < 0 := by linarith
    have hev : ∀ᶠ z' : 𝔻 in 𝓝 z, ‖(z' : ℂ)‖ - cupG e g z' < 0 :=
      hcont.tendsto.eventually (isOpen_Iio.mem_nhds hlt)
    filter_upwards [hev] with z' hz'
    show ‖(z' : ℂ)‖ < cupG e g z'
    linarith

theorem cupAux_isClosed_le_norm (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x) :
    IsClosed {z : 𝔻 | cupG e g z ≤ ‖(z : ℂ)‖} := by
  have h := (cupAux_isOpen_norm_lt e he_range hgc hg0).isClosed_compl
  rwa [show {z : 𝔻 | ‖(z : ℂ)‖ < cupG e g z}ᶜ = {z : 𝔻 | cupG e g z ≤ ‖(z : ℂ)‖} from by
    ext z; simp [not_lt]] at h

theorem cupAux_continuous_cupE (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x) :
    Continuous (cupE e g) := by
  have hS1 : ContinuousOn (cupE e g) {z : 𝔻 | ‖(z : ℂ)‖ ≤ cupG e g z} :=
    (cupAux_continuous_cupBottom e he_range hgc hg0).continuousOn.congr
      (fun z hz => cupE_of_le hz)
  have hS2 : ContinuousOn (cupE e g) {z : 𝔻 | cupG e g z ≤ ‖(z : ℂ)‖} := by
    have hsub : {z : 𝔻 | cupG e g z ≤ ‖(z : ℂ)‖} ⊆ {z : 𝔻 | (z : ℂ) ≠ 0} := by
      intro z hz h0
      have h1 : cupG e g z ≤ 0 := by simpa [h0] using hz
      have h2 := cupAux_pos e he_range hg0 z
      linarith
    have hwallS : ContinuousOn (cupWall e g) {z : 𝔻 | cupG e g z ≤ ‖(z : ℂ)‖} :=
      ((cupAux_continuousOn_cupAuxWallS e he_range hgc hg0).mono hsub).congr
        (fun z hz => cupAux_cupWall_eq e he_range hg0 hz)
    exact hwallS.congr (fun z hz => by
      by_cases h : ‖(z : ℂ)‖ ≤ cupG e g z
      · rw [cupE_of_le h, cupBottom_eq_cupWall_of_eq (le_antisymm h hz)]
      · rw [cupE_of_gt (lt_of_not_ge h)])
  have hcover : {z : 𝔻 | ‖(z : ℂ)‖ ≤ cupG e g z} ∪ {z : 𝔻 | cupG e g z ≤ ‖(z : ℂ)‖} = univ := by
    ext z
    simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]
    exact le_total ‖(z : ℂ)‖ (cupG e g z)
  have hcontOn : ContinuousOn (cupE e g) univ := by
    rw [← hcover]
    exact hS1.union_of_isClosed hS2 (cupAux_isClosed_le e he_range hgc hg0)
      (cupAux_isClosed_le_norm e he_range hgc hg0)
  rwa [continuousOn_univ] at hcontOn

/-! ## The boundary circle lands on the top rim -/

/-- On the boundary circle the parametrisation of the cup lands on the top rim. -/
theorem cupE_circlePoint
    {K : Set (EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (e : C(𝔻, EuclideanSpace ℝ (Fin 2)))
    (he_range : Set.range e = K) (hg0 : ∀ x ∈ K, 0 ≤ g x) (θ : ℝ) :
    cupE e g (Work.CoreTopology.circlePoint θ) =
      cmk (e (Work.CoreTopology.circlePoint θ)) (g (e (Work.CoreTopology.circlePoint θ))) := by
  set z := Work.CoreTopology.circlePoint θ with hz
  have hnorm : ‖(z : ℂ)‖ = 1 := by
    rw [hz, Work.CoreTopology.circlePoint_coe]
    exact Complex.norm_exp_ofReal_mul_I θ
  have hdir : cupDir z = z := cupDir_eq_self hnorm
  have hm : 0 ≤ g (e (cupDir z)) := by
    rw [hdir]
    exact hg0 _ (by rw [← he_range]; exact Set.mem_range_self z)
  have hGle : cupG e g z ≤ 1 := cupG_le_one hm
  by_cases h : ‖(z : ℂ)‖ ≤ cupG e g z
  · have hG1 : cupG e g z = 1 := le_antisymm hGle (by rw [← hnorm]; exact h)
    have hm0 : g (e (cupDir z)) = 0 := (cupG_eq_one_iff hm).mp hG1
    have hgz : g (e z) = 0 := by rw [hdir] at hm0; exact hm0
    have hmax : max (cupG e g z) ‖(z : ℂ)‖ = ‖(z : ℂ)‖ :=
      max_eq_right (by rw [hG1, hnorm])
    have hscaled : cupScaled e g z = z := by
      refine Subtype.ext ?_
      rw [cupScaled_coe, hmax, hnorm]
      simp
    rw [cupE_eq_cmk_bottom h, hscaled, hgz]
  · have hlt : cupG e g z < ‖(z : ℂ)‖ := lt_of_not_ge h
    have hGlt : cupG e g z < 1 := by rw [← hnorm]; exact hlt
    have hne : (1 : ℝ) - cupG e g z ≠ 0 := by linarith
    rw [cupE_eq_cmk_wall hlt, hdir, hnorm, div_self hne, mul_one]

/-! PROOF HINT (the reviewers' suggested collar-aligned map is NOT injective where `g` vanishes
on `frontier K`: the whole fibre `{θ} × [1/2,1]` collapses onto the base point and collides with
the inner disc. Use instead a *direction-dependent threshold*:

Let `G : Metric.closedBall (0 : ℂ) 1 → ℝ`, `G z = 1 - g (e (dir z)) / (2 * (1 + g (e (dir z))))`
where `dir z = z / ‖z‖` (a point of the disc, of norm `1`) — so `1/2 ≤ G z ≤ 1`, and `G z = 1`
exactly when `g (e (dir z)) = 0`.  Define

`E z = if ‖(z : ℂ)‖ ≤ G z then cmk (e (⟨(z : ℂ) / G z, _⟩)) 0`
`      else cmk (e (dir z)) (g (e (dir z)) * ((‖(z : ℂ)‖ - G z) / (1 - G z)))`.

On the "bottom" branch the base point `e (z / G z)` runs over all of `K` (the ratio `‖z‖ / G z`
ranges over `[0,1]`); on the "wall" branch the base is the boundary point `e (dir z)` and the
height runs over `[0, g (e (dir z))]`.  The two branches agree on the switch `‖z‖ = G z`
(both give `cmk (e (dir z)) 0`), giving continuity; injectivity uses that `z / G z` recovers the
direction and then the modulus; the boundary `‖z‖ = 1` lands on the top rim
(`cmk (e z) (g (e z))`), which is the third conjunct. -/
theorem exists_cupParam
    {K : Set (EuclideanSpace ℝ (Fin 2))} {g : EuclideanSpace ℝ (Fin 2) → ℝ}
    (e : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 2)))
    (he_inj : Function.Injective e) (he_range : Set.range e = K)
    (he_bdry : Set.range (fun θ : ℝ => e (Work.CoreTopology.circlePoint θ)) = frontier K)
    (hgc : ContinuousOn g K) (hg0 : ∀ x ∈ K, 0 ≤ g x) :
    ∃ E : C(Metric.closedBall (0 : ℂ) 1, EuclideanSpace ℝ (Fin 3)),
      Function.Injective E ∧
      Set.range E =
        {P : EuclideanSpace ℝ (Fin 3) | Work.Drive.Mono.cproj P ∈ K ∧ Work.Drive.Mono.clast P = 0} ∪
        {P : EuclideanSpace ℝ (Fin 3) | Work.Drive.Mono.cproj P ∈ frontier K ∧
          0 ≤ Work.Drive.Mono.clast P ∧ Work.Drive.Mono.clast P ≤ g (Work.Drive.Mono.cproj P)} ∧
      (∀ θ : ℝ, E (Work.CoreTopology.circlePoint θ) =
        Work.Drive.Mono.cmk (e (Work.CoreTopology.circlePoint θ))
          (g (e (Work.CoreTopology.circlePoint θ)))) := by
  refine ⟨⟨cupE e g, cupAux_continuous_cupE e he_range hgc hg0⟩, ?_, ?_, ?_⟩
  · exact cupE_injective e he_inj he_range he_bdry hgc hg0
  · exact cupE_range e he_inj he_range he_bdry hgc hg0
  · exact cupE_circlePoint e he_range hg0

end

end Work.Drive.Mono.WindowCase
