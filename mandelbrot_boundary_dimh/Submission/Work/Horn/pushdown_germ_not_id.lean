import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Horn.basic
import Submission.Work.Horn.gholo
import Submission.Work.Horn.inf_of_parts
import Submission.Work.Horn.pushdown_germ

/-!
# AREA HORN: the germ of the pushed-down horn map at `0` is not the identity

`Work.Horn.pushdown_germ` shows that near `0` the pushed-down horn map `g = pushdown d.E`
has the shape `g ζ = ζ · π (H ζ)` with `H` holomorphic at `0` and `H 0 = 0`.  The point of
the present lemma is that this germ is *not* the identity: the lifted horn map `Ẽ` is
infinite-to-one on `Bu` (`HornData.inf_u`, here an explicit hypothesis `hinf`), whereas the
identity germ would force `Ẽ = id` on the whole connected set `Bu`.

The argument is short.  Suppose `g =ᶠ[𝓝 0] id`.  Choose `r > 0` with `ball 0 r ⊆ {g = id}`.
Let `R` be the threshold of the upper-end normalisation `Ẽ w - w → 0` at level `1/2`, and let
`M ≥ max (R) (-log r/(2π)) η₀`.  For `Im w > M` the point `π w` lies in `ball 0 r`, so

`π (Ẽ w) = g (π w) = π w`,  hence `Ẽ w - w ∈ ℤ`,

while `‖Ẽ w - w‖ < 1/2`, so `Ẽ w = w`.  Thus `Ẽ = id` on the open half-plane `{Im w > M}`, which
meets the preconnected open set `BuOf d B` (`BuOf` contains `{Im > η₀}`).  Since `Ẽ - id` is
holomorphic on `BuOf` (which is a subset of the lifted domain `DE`), the identity theorem gives
`Ẽ = id` on `BuOf`.  But then every `Ẽ`-fibre in `BuOf` is a subsingleton, so its `π`-image is
finite, contradicting `hinf`.

(The equality `π (Ẽ w) = g (π w)` is `pushdown_piExp`; the lift `w ↦ log ζ/(2πi)` of a point of
`ball 0 r` has imaginary part `> -log r/(2π)`, which is what fixes the threshold `M`.)
-/

namespace Work.Horn

open scoped Topology
open Filter Topology Metric

noncomputable section

/-- `‖π w‖ = exp (-2π Im w)`. -/
theorem piExp_norm (w : ℂ) : ‖MandelDim.piExp w‖ = Real.exp (-(2 * Real.pi * w.im)) := by
  rw [MandelDim.piExp, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- **The germ of the pushed-down horn map `g = pushdown Ẽ_{f₀}` at `0` is not the identity.**
The hypothesis `hinf` is `HornData.inf_u`: the lifted horn map `Ẽ` is infinite-to-one on `Bu` in
the sense that every fibre has infinite `π`-image; this rules out `g` being the identity near `0`. -/
theorem pushdown_germ_not_id (hTopo : MandelDim.HornTopoStatement)
    (f₀ : ℂ → ℂ) (D₀ B : Set ℂ) (c : ℂ) (d : MandelDim.ParabData f₀ D₀)
    (hsetup : MandelDim.IsF0Setup f₀ D₀ B c)
    (hinf : ∀ y : ℂ,
      (MandelDim.piExp '' {w : ℂ | w ∈ MandelDim.BuOf d B ∧ d.E w = y}).Infinite) :
    ¬ (∀ᶠ ζ in nhds 0, MandelDim.pushdown d.E ζ = ζ) := by
  intro H
  obtain ⟨hBuO, hBlO, hBuT, hBlT, hup, hlow, hsub⟩ := hTopo f₀ D₀ B c d hsetup
  -- the germ equality holds on a ball of radius `r > 0`
  obtain ⟨r, hr, hballm⟩ := Metric.mem_nhds_iff.mp H
  -- the upper-end normalisation `Ẽ w - w → 0`, at level `1/2`
  obtain ⟨R, hR⟩ := Work.Horn.MandelDim.ParabData.E_upper_iff d (1/2) (by norm_num)
  -- the threshold above which both effects are in force
  set M : ℝ := max R (max (-(Real.log r) / (2*Real.pi)) d.η₀) with hMdef
  have hRle : R ≤ M := le_max_left _ _
  have htle : -(Real.log r) / (2*Real.pi) ≤ M :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hηle : d.η₀ ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  -- ## Step 1: `Ẽ w = w` on the half plane `{Im w > M}`
  have key : ∀ w : ℂ, M < w.im → d.E w = w := by
    intro w hw
    have hwR : R < w.im := lt_of_le_of_lt hRle hw
    have hwt : -(Real.log r) / (2*Real.pi) < w.im := lt_of_le_of_lt htle hw
    have hwη : d.η₀ < w.im := lt_of_le_of_lt hηle hw
    -- the lift lies in the `T`-equivariant region `{|Im| > η₀}`
    have hwD : w ∈ {w : ℂ | d.η₀ < |w.im|} := lt_abs.mpr (Or.inl hwη)
    have hpush := Work.Horn.MandelDim.pushdown_piExp (E := d.E)
      (D := {w : ℂ | d.η₀ < |w.im|}) (Work.Horn.isTInvariant_abs_im_gt d.η₀)
      (fun u hu _ => (Work.Horn.isTEquivariantOn_E_abs_im_gt d).2 u hu) hwD
    -- `π w` is close to `0`, hence a fixed point of `g`
    have hπlt : ‖MandelDim.piExp w‖ < r := by
      have h2pi : (0:ℝ) < 2*Real.pi := by positivity
      have ht_mul : 2*Real.pi * (-(Real.log r) / (2*Real.pi)) = -(Real.log r) := by
        field_simp
      have hgt : 2*Real.pi*(-(Real.log r)/(2*Real.pi)) < 2*Real.pi*w.im :=
        mul_lt_mul_of_pos_left hwt h2pi
      rw [ht_mul] at hgt
      rw [piExp_norm]
      have h2 : -(2*Real.pi*w.im) < Real.log r := by linarith
      calc Real.exp (-(2*Real.pi*w.im)) < Real.exp (Real.log r) := Real.exp_lt_exp.mpr h2
        _ = r := Real.exp_log hr
    have hmem : MandelDim.piExp w ∈ Metric.ball (0:ℂ) r := by
      rw [Metric.mem_ball, dist_zero_right]; exact hπlt
    have h1 : MandelDim.pushdown d.E (MandelDim.piExp w) = MandelDim.piExp w := hballm hmem
    have h2 : MandelDim.piExp (d.E w) = MandelDim.piExp w := by rw [← hpush, h1]
    obtain ⟨k, hk⟩ := (Work.Horn.MandelDim.piExp_eq_iff).mp h2
    have hkd : d.E w - w = (k : ℂ) := by rw [hk]; ring
    -- the shift is an integer of modulus `< 1/2`, hence `0`
    have h3 : ‖((k:ℤ):ℂ)‖ < 1/2 := by
      have := hR w hwR
      rwa [← hkd]
    have hk0 : k = 0 := by
      have hklt : |(k : ℝ)| < 1 := by
        rw [Complex.norm_intCast] at h3; linarith
      exact Int.abs_lt_one_iff.mp (by exact_mod_cast hklt)
    rw [hk0] at hk; simpa using hk
  -- ## Step 2: `Ẽ - id` is holomorphic on `BuOf d B`
  have hE_diff : DifferentiableOn ℂ d.E (MandelDim.BuOf d B) := by
    intro w hw
    have hwDE : w ∈ d.DE := hsub (Or.inl hw)
    have hφ : DifferentiableWithinAt ℂ d.φ (MandelDim.BuOf d B) w :=
      (d.φ_holo w hwDE.1).mono (fun x hx => (hsub (Or.inl hx)).1)
    have hΦ : DifferentiableWithinAt ℂ d.Φ (MandelDim.ParabolicBasin f₀ D₀) (d.φ w) :=
      d.Φ_holo (d.φ w) hwDE.2
    exact hΦ.comp w hφ (fun x hx => (hsub (Or.inl hx)).2)
  -- the open half plane `{Im > M}` meets `BuOf d B`
  set z₀ : ℂ := Complex.I * (M + 1) with hz₀def
  have hz₀im : z₀.im = M + 1 := by
    simp [hz₀def]
  have hz₀mem : z₀ ∈ MandelDim.BuOf d B := by
    apply hup
    show d.η₀ < z₀.im
    rw [hz₀im]; linarith
  have hpre : IsPreconnected (MandelDim.BuOf d B) := isPreconnected_connectedComponentIn
  have hevent : d.E =ᶠ[nhds z₀] id := by
    have hopen : {w : ℂ | M < w.im} ∈ nhds z₀ := by
      apply IsOpen.mem_nhds
      · exact isOpen_lt continuous_const Complex.continuous_im
      · show M < z₀.im
        rw [hz₀im]; linarith
    filter_upwards [hopen] with w hw
    exact key w hw
  -- ## Step 3: identity theorem: `Ẽ = id` on all of `BuOf d B`
  have heqon : Set.EqOn d.E id (MandelDim.BuOf d B) :=
    AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (hE_diff.analyticOnNhd hBuO) analyticOnNhd_id hpre hz₀mem hevent
  -- ## Step 4: the fibre of `Ẽ` over `z₀` inside `BuOf` is a subsingleton
  have hsubsing : ({w : ℂ | w ∈ MandelDim.BuOf d B ∧ d.E w = z₀}).Subsingleton := by
    intro a ha b hb
    have ha' : a = z₀ := by
      have hh := heqon ha.1
      rw [ha.2] at hh
      exact hh.symm
    have hb' : b = z₀ := by
      have hh := heqon hb.1
      rw [hb.2] at hh
      exact hh.symm
    rw [ha', hb']
  have hfin : (MandelDim.piExp '' {w : ℂ | w ∈ MandelDim.BuOf d B ∧ d.E w = z₀}).Finite :=
    Set.Subsingleton.finite (fun a ha b hb => by
      obtain ⟨x, hx, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hb
      rw [hsubsing hx hy])
  exact (hinf z₀).not_finite hfin

end

end Work.Horn
