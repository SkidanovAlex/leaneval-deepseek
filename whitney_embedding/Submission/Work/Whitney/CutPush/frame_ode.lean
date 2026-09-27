import Mathlib
import Submission.Work.ODE.LinearFamily

/-!
# The FRAME brick, via a linear ODE: the analytic half

`Work.Whitney.CutPush.plane_family_trivialisation` (the FRAME brick of
`Submission/Work/Whitney/CutPush/NOTES_linear_fibered_route.md`) asks: for a smooth family
`π : ℝ → (E →L[ℝ] E)` of *projections* (idempotent, constant outside `[0,1]`, rank `N/2`), there is
a smooth family of linear *equivalences* `M t` with `M t (range (π t)) ⊆ range (π 0)`.

## The construction (this file: the analytic half)

Write `End := E →L[ℝ] E`, `B t := deriv π t`, and consider the *saturated* field
`X (t, (z, w)) = (1, χ (z, w) • (B t * z , -(w * B t)))` on `ℝ × (End × End)`, where `χ` is the
radial cutoff `satCutoff R ‖·‖` of `Work.ODE.LinearFamily`.  Its global integral curve `γ` through
`(0, (1, 1))` has (i) first coordinate `t`, hence `γ t = (t, (z t, w t))` with

`z' = χ ‖(z,w)‖ • (B t * z)`,   `w' = χ ‖(z,w)‖ • (-(w * B t))`,

and (ii) the useful consequences

* **product rule**: `(w * z)' = w' * z + w * z' = χ • (-(w B) z + w (B z)) = 0`, so `w t * z t = 1`
  for every `t` (the *same* cutoff for both factors — this is why the two are solved together);
* **Gronwall**: `‖z t‖ ≤ exp (C t)` and `‖w t‖ ≤ exp (C t)` for `t ∈ [0,1]` where `C` bounds
  `‖B t‖`, so with `R ≥ exp C` the cutoff is `1` *on the interval*, i.e. both equations are the
  plain linear equations there;
* the plain equations hold in fact **for all** `t`, because `B t = 0` off `[0,1]` makes both sides
  vanish there.

What is left (see the `sorry` at the end, and `NOTES_linear_fibered_route.md` §8) is:
the *aligning* step (`z t` carries `range (π 0)` into `range (π t)`: the reflection identity
`(1 - π t) B t u = (deriv π t) u` for `u ∈ range (π t)`, obtained from `π u = u` and
`π (B u) = 0`, followed by a Gronwall for `Φ t := (1 - π t) (z t v)`), assembled with `w t z t = 1`
into `M t := w t`; smoothness of `z, w` by bootstrapping the linear equation; and the packaging
`End ≃L[ℝ] End`.

The two derived identities used by the aligning step, both from `hidem` and `hderiv`, are:

* `B t * π t + π t * B t = B t` — differentiate `s ↦ π s * π s`;
* `π t * B t * π t = 0` — multiply the previous identity by `π t` on the right.
-/

namespace Work.Whitney.CutPush

open scoped Topology ContDiff
open Function
open Work.ODE (satField satCutoff satCutoff_eq_one satCutoff_le_one satCutoff_nonneg
  exists_isIntegralCurve_satField fst_eq_of_isIntegralCurve_satField hasDerivAt_snd_satField)

/-- The endomorphism ring of `ℝ^N`. -/
abbrev FrameEnd (N : ℕ) := EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N)

variable {N : ℕ}

lemma frame_mul_eq_comp (f g : FrameEnd N) (x : EuclideanSpace ℝ (Fin N)) : (f * g) x = f (g x) :=
  mul_apply_eq_comp f g x

/-! ## The coefficient family `B` and the linear field attached to it -/

section Coeff

/-- The saturated ODE field of the FRAME brick, as an instance of the *linear family* field
`Work.ODE.satField`: `(t, (z,w)) ↦ (1, χ ‖(z,w)‖ • (B t * z, -(w * B t)))`. -/
noncomputable def frameLin (B : ℝ → FrameEnd N) (t : ℝ) :
    (FrameEnd N × FrameEnd N) →L[ℝ] (FrameEnd N × FrameEnd N) :=
  LinearMap.mkContinuous
    { toFun := fun Y : FrameEnd N × FrameEnd N => (B t * Y.1, -(Y.2 * B t))
      map_add' := by
        intro a b
        refine Prod.ext ?_ ?_ <;> simp only [Prod.fst_add, Prod.snd_add, Prod.mk_add_mk,
          map_add, mul_add, add_mul, neg_add]
      map_smul' := by
        intro c a
        refine Prod.ext ?_ ?_
        · apply ContinuousLinearMap.ext
          intro x
          simp only [Prod.smul_fst, smul_apply, frame_mul_eq_comp, map_smul, RingHom.id_apply]
        · apply ContinuousLinearMap.ext
          intro x
          simp only [Prod.smul_snd, smul_apply, frame_mul_eq_comp, map_smul,
            Pi.neg_apply, neg_apply, smul_neg, RingHom.id_apply] }
    ‖B t‖
    (by
      intro Y
      rw [Prod.norm_def, Prod.norm_def]
      refine max_le ?_ ?_
      · calc ‖B t * Y.1‖ ≤ ‖B t‖ * ‖Y.1‖ := norm_mul_le _ _
          _ ≤ ‖B t‖ * max ‖Y.1‖ ‖Y.2‖ :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
      · calc ‖-(Y.2 * B t)‖ = ‖Y.2 * B t‖ := norm_neg _
          _ ≤ ‖Y.2‖ * ‖B t‖ := norm_mul_le _ _
          _ = ‖B t‖ * ‖Y.2‖ := by ring
          _ ≤ ‖B t‖ * max ‖Y.1‖ ‖Y.2‖ :=
              mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _))

lemma frameLin_apply (B : ℝ → FrameEnd N) (t : ℝ) (Y : FrameEnd N × FrameEnd N) :
    frameLin B t Y = (B t * Y.1, -(Y.2 * B t)) := rfl

lemma frameLin_opNorm_le (B : ℝ → FrameEnd N) (t : ℝ) : ‖frameLin B t‖ ≤ ‖B t‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun Y => by
    rw [frameLin_apply, Prod.norm_def, Prod.norm_def]
    refine max_le ?_ ?_
    · calc ‖B t * Y.1‖ ≤ ‖B t‖ * ‖Y.1‖ := norm_mul_le _ _
        _ ≤ ‖B t‖ * max ‖Y.1‖ ‖Y.2‖ :=
            mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
    · calc ‖-(Y.2 * B t)‖ = ‖Y.2 * B t‖ := norm_neg _
        _ ≤ ‖Y.2‖ * ‖B t‖ := norm_mul_le _ _
        _ = ‖B t‖ * ‖Y.2‖ := by ring
        _ ≤ ‖B t‖ * max ‖Y.1‖ ‖Y.2‖ :=
            mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _))

lemma frameLin_sub_apply (B : ℝ → FrameEnd N) (t s : ℝ) (Y : FrameEnd N × FrameEnd N) :
    (frameLin B t - frameLin B s) Y = ((B t - B s) * Y.1, -(Y.2 * (B t - B s))) := by
  rw [ContinuousLinearMap.sub_apply, frameLin_apply, frameLin_apply]
  refine Prod.ext ?_ ?_
  · show B t * Y.1 - B s * Y.1 = (B t - B s) * Y.1
    rw [sub_mul]
  · show -(Y.2 * B t) - -(Y.2 * B s) = -(Y.2 * (B t - B s))
    rw [mul_sub, neg_sub]
    abel

lemma frameLin_sub_opNorm_le (B : ℝ → FrameEnd N) (t s : ℝ) :
    ‖frameLin B t - frameLin B s‖ ≤ ‖B t - B s‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun Y => ?_)
  rw [frameLin_sub_apply, Prod.norm_def, Prod.norm_def]
  refine max_le ?_ ?_
  · calc ‖(B t - B s) * Y.1‖ ≤ ‖B t - B s‖ * ‖Y.1‖ := norm_mul_le _ _
      _ ≤ ‖B t - B s‖ * max ‖Y.1‖ ‖Y.2‖ :=
          mul_le_mul_of_nonneg_left (le_max_left _ _) (norm_nonneg _)
  · calc ‖-(Y.2 * (B t - B s))‖ = ‖Y.2 * (B t - B s)‖ := norm_neg _
      _ ≤ ‖Y.2‖ * ‖B t - B s‖ := norm_mul_le _ _
      _ = ‖B t - B s‖ * ‖Y.2‖ := by ring
      _ ≤ ‖B t - B s‖ * max ‖Y.1‖ ‖Y.2‖ :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (norm_nonneg _)

end Coeff

/-! ## The two derivative identities -/

section Identities

variable (π π' : ℝ → FrameEnd N)

/-- Differentiating `s ↦ π s * π s = π s` at `t`: `B t π t + π t B t = B t`. -/
theorem deriv_idem (hidem : ∀ t y, π t (π t y) = π t y)
    (hderiv : ∀ t, HasDerivAt (fun s : ℝ => π s) (π' t) t) (t : ℝ) :
    π' t * π t + π t * π' t = π' t := by
  have h1 : HasDerivAt (fun s : ℝ => π s * π s) (π' t * π t + π t * π' t) t :=
    (hderiv t).mul (hderiv t)
  have h2 : HasDerivAt (fun s : ℝ => π s * π s) (π' t) t := by
    have heq : (fun s : ℝ => π s * π s) = fun s : ℝ => π s := by
      funext s
      exact ContinuousLinearMap.ext (fun y => by rw [frame_mul_eq_comp]; exact hidem s y)
    rw [heq]
    exact hderiv t
  exact h1.unique h2

/-- The second identity: `π t * B t * π t = 0`. -/
theorem idem_mul_deriv_mul (hidem : ∀ t y, π t (π t y) = π t y)
    (hderiv : ∀ t, HasDerivAt (fun s : ℝ => π s) (π' t) t) (t : ℝ) :
    π t * π' t * π t = 0 := by
  have h := deriv_idem π π' hidem hderiv t
  have h2 : π t * π' t = π' t - π' t * π t := by
    have hh : π t * π' t + π' t * π t = π' t := by rw [add_comm]; exact h
    exact eq_sub_of_add_eq hh
  have h3 : π t * π t = π t :=
    ContinuousLinearMap.ext (fun y => by rw [frame_mul_eq_comp]; exact hidem t y)
  calc π t * π' t * π t = (π' t - π' t * π t) * π t := by rw [h2]
    _ = π' t * π t - π' t * π t * π t := by rw [sub_mul]
    _ = π' t * π t - π' t * (π t * π t) := by rw [mul_assoc]
    _ = π' t * π t - π' t * π t := by rw [h3]
    _ = 0 := sub_self _

/-- **The aligning identity.**  For `u ∈ range (π t)`, `π t` acts as the identity on `π' t u`, i.e.
`(1 - π t) (π' t u) = π' t u`: this is the identity that makes the defect
`Φ t = (1 - π t) (z t v)` solve a *homogeneous* linear equation. -/
theorem one_sub_mul_deriv (hidem : ∀ t y, π t (π t y) = π t y)
    (hderiv : ∀ t, HasDerivAt (fun s : ℝ => π s) (π' t) t) (t : ℝ)
    {u : EuclideanSpace ℝ (Fin N)} (hu : π t u = u) :
    (1 - π t) (π' t u) = π' t u := by
  have h := congrArg (fun T : FrameEnd N => T u) (idem_mul_deriv_mul π π' hidem hderiv t)
  simp only [frame_mul_eq_comp, zero_apply] at h
  rw [hu] at h
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, h, sub_zero]

/-- **`π'` vanishes off `[0,1]`.**  Since `π` is constant on `(-∞,0]` and on `[1,∞)`, so is its
derivative: this is what makes the *linear* equations hold on all of `ℝ` (both sides vanish off
`[0,1]`) and what makes the compact-support arguments possible. -/
theorem deriv_eq_zero_of_lt_zero {π' : ℝ → FrameEnd N}
    (hleft : ∀ t, t ≤ 0 → π t = π 0)
    (hderiv : ∀ t, HasDerivAt (fun s : ℝ => π s) (π' t) t) {t : ℝ} (ht : t < 0) : π' t = 0 := by
  have hev : (fun s : ℝ => π s) =ᶠ[𝓝 t] (fun _ => π 0) := by
    filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
    exact hleft s (le_of_lt hs)
  have h1 : HasDerivAt (fun _ : ℝ => π 0) (π' t) t :=
    (Filter.EventuallyEq.hasDerivAt_iff hev).mp (hderiv t)
  exact h1.unique (hasDerivAt_const t (π 0))

/-- `π'` vanishes for `t > 1`. -/
theorem deriv_eq_zero_of_one_lt {π' : ℝ → FrameEnd N}
    (hright : ∀ t, 1 ≤ t → π t = π 1)
    (hderiv : ∀ t, HasDerivAt (fun s : ℝ => π s) (π' t) t) {t : ℝ} (ht : 1 < t) : π' t = 0 := by
  have hev : (fun s : ℝ => π s) =ᶠ[𝓝 t] (fun _ => π 1) := by
    filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
    exact hright s (le_of_lt hs)
  have h1 : HasDerivAt (fun _ : ℝ => π 1) (π' t) t :=
    (Filter.EventuallyEq.hasDerivAt_iff hev).mp (hderiv t)
  exact h1.unique (hasDerivAt_const t (π 1))

end Identities

/-! ## The global integral curve -/

section Curve

variable (π' : ℝ → FrameEnd N) (R C LA : ℝ)

set_option synthInstance.maxHeartbeats 200000 in
/-- **Existence of the global integral curve** of the saturated FRAME field, through `(0, (1,1))`:
the *linear family* theorem of `Work.ODE.LinearFamily` applied to `frameLin π'`. -/
theorem exists_frameCurve (hR : 0 < R) (hC : 0 ≤ C) (hLA : 0 ≤ LA)
    (hB : ∀ t, ‖π' t‖ ≤ C) (hBlip : ∀ t s, ‖π' t - π' s‖ ≤ LA * |t - s|) :
    ∃ γ : ℝ → ℝ × (FrameEnd N × FrameEnd N),
      γ 0 = (0, (1, 1)) ∧ IsIntegralCurve γ (fun _ z => satField (frameLin π') R z) :=
  exists_isIntegralCurve_satField (A := frameLin π') hR hC hLA
    (fun t => (frameLin_opNorm_le π' t).trans (hB t))
    (fun t s => (frameLin_sub_opNorm_le π' t s).trans (hBlip t s)) (0, (1, 1))

variable {π'}

/-- The first coordinate of the integral curve is the parameter. -/
theorem frameCurve_fst {R : ℝ} {γ : ℝ → ℝ × (FrameEnd N × FrameEnd N)}
    (hγ : IsIntegralCurve γ (fun _ z => satField (frameLin π') R z))
    (hγ0 : γ 0 = (0, (1, 1))) (s : ℝ) : (γ s).1 = s :=
  fst_eq_of_isIntegralCurve_satField hγ hγ0 rfl s

/-- The `z`-equation (`z = (γ ·).2.1`). -/
theorem frameCurve_z_deriv {R : ℝ} {γ : ℝ → ℝ × (FrameEnd N × FrameEnd N)}
    (hγ : IsIntegralCurve γ (fun _ z => satField (frameLin π') R z))
    (hγ0 : γ 0 = (0, (1, 1))) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (γ t).2.1)
      ((satCutoff R ‖(γ s).2‖) • (π' s * (γ s).2.1)) s := by
  have hval : ((satCutoff R ‖(γ s).2‖) • (frameLin π' s (γ s).2)).1
      = (satCutoff R ‖(γ s).2‖) • (π' s * (γ s).2.1) := by
    simp only [Prod.smul_fst, frameLin_apply]
  exact hval ▸ (hasDerivAt_snd_satField (A := frameLin π') hγ hγ0 rfl s).fst

/-- The `w`-equation (`w = (γ ·).2.2`). -/
theorem frameCurve_w_deriv {R : ℝ} {γ : ℝ → ℝ × (FrameEnd N × FrameEnd N)}
    (hγ : IsIntegralCurve γ (fun _ z => satField (frameLin π') R z))
    (hγ0 : γ 0 = (0, (1, 1))) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (γ t).2.2)
      ((satCutoff R ‖(γ s).2‖) • (-((γ s).2.2 * π' s))) s := by
  have hval : ((satCutoff R ‖(γ s).2‖) • (frameLin π' s (γ s).2)).2
      = (satCutoff R ‖(γ s).2‖) • (-((γ s).2.2 * π' s)) := by
    simp only [Prod.smul_snd, frameLin_apply]
  exact hval ▸ (hasDerivAt_snd_satField (A := frameLin π') hγ hγ0 rfl s).snd

end Curve

/-! ## Gronwall for the pair

`FrameEnd N` carries no inner product, so the elementary `(‖·‖²)' = 2⟪·,·'⟫` route is unavailable;
the estimate is instead Mathlib's Banach-space Gronwall
`norm_le_gronwallBound_of_norm_deriv_right_le` (`Mathlib/Analysis/ODE/Gronwall.lean`) with
`ε = 0`, whose solution is `gronwallBound_ε0`: `‖ζ t‖ ≤ ‖ζ 0‖ * exp (C * (t - a))`. -/

section Gronwall

/-- **Gronwall.**  A curve of pairs solving `ζ' = κ • (B t * ζ.1, -(ζ.2 * B t))` with
`0 ≤ κ ≤ 1` and `‖B t‖ ≤ C` grows at most like `exp (C t)` on `[0,1]`. -/
theorem pair_gronwall {B : ℝ → FrameEnd N} {κ : ℝ → ℝ}
    {ζ : ℝ → FrameEnd N × FrameEnd N} {C : ℝ}
    (hC : 0 ≤ C) (hB : ∀ t, ‖B t‖ ≤ C)
    (hκ0 : ∀ t, 0 ≤ κ t) (hκ1 : ∀ t, κ t ≤ 1)
    (hζ : ∀ t, HasDerivAt ζ (κ t • (frameLin B t (ζ t))) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖ζ t‖ ≤ Real.exp C * ‖ζ 0‖ := by
  have hcont : Continuous ζ :=
    continuous_iff_continuousAt.mpr (fun x => (hζ x).continuousAt)
  have hpt : ∀ x : ℝ, ‖frameLin B x (ζ x)‖ ≤ C * ‖ζ x‖ := by
    intro x
    rw [frameLin_apply, Prod.norm_def]
    refine max_le ?_ ?_
    · have h1 : ‖(ζ x).1‖ ≤ ‖ζ x‖ := by rw [Prod.norm_def]; exact le_max_left _ _
      refine (norm_mul_le _ _).trans ?_
      calc ‖B x‖ * ‖(ζ x).1‖ ≤ C * ‖(ζ x).1‖ :=
            mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)
        _ ≤ C * ‖ζ x‖ := mul_le_mul_of_nonneg_left h1 hC
    · have h1 : ‖(ζ x).2‖ ≤ ‖ζ x‖ := by rw [Prod.norm_def]; exact le_max_right _ _
      calc ‖-((ζ x).2 * B x)‖ = ‖(ζ x).2 * B x‖ := norm_neg _
        _ ≤ ‖(ζ x).2‖ * ‖B x‖ := norm_mul_le _ _
        _ ≤ ‖ζ x‖ * C := mul_le_mul h1 (hB x) (norm_nonneg _) (norm_nonneg _)
        _ = C * ‖ζ x‖ := by ring
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      ‖κ x • (frameLin B x (ζ x))‖ ≤ C * ‖ζ x‖ + 0 := by
    intro x _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hκ0 x)]
    calc κ x * ‖frameLin B x (ζ x)‖ ≤ 1 * (C * ‖ζ x‖) :=
          mul_le_mul (hκ1 x) (hpt x) (norm_nonneg _) (by linarith [hκ0 x])
      _ = C * ‖ζ x‖ + 0 := by ring
  have key := norm_le_gronwallBound_of_norm_deriv_right_le (f := ζ)
    (f' := fun x : ℝ => κ x • (frameLin B x (ζ x))) (δ := ‖ζ 0‖) (K := C) (ε := 0)
    (a := 0) (b := 1) hcont.continuousOn
    (fun x _ => (hζ x).hasDerivWithinAt) le_rfl hbound
  intro t ht
  have h1 := key t ht
  rw [sub_zero, gronwallBound_ε0] at h1
  calc ‖ζ t‖ ≤ ‖ζ 0‖ * Real.exp (C * t) := h1
    _ ≤ ‖ζ 0‖ * Real.exp C := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        exact Real.exp_le_exp.mpr (by nlinarith [ht.2])
    _ = Real.exp C * ‖ζ 0‖ := by ring

end Gronwall

/-! ## The inverse relation `w t * z t = 1`

The two components of the FRAME field are solved with the **same** scalar factor
`κ = satCutoff R ‖(z, w)‖`; that common factor is exactly what makes the product rule close. -/

section Inverse

/-- **The transport and its inverse compose to the identity.**  If `z` and `w` solve the
left- and right-multiplication equations with the *same* factor `κ`, then `w * z` is constant, and
`w t * z t = 1` for every `t`. -/
theorem mul_eq_one_of_hasDerivAt {B : ℝ → FrameEnd N} {κ : ℝ → ℝ} {z w : ℝ → FrameEnd N}
    (hz : ∀ t, HasDerivAt z (κ t • (B t * z t)) t)
    (hw : ∀ t, HasDerivAt w (κ t • (-(w t * B t))) t)
    (h0 : w 0 * z 0 = 1) : ∀ t, w t * z t = 1 := by
  have hderiv : ∀ t, HasDerivAt (fun s => w s * z s) 0 t := by
    intro t
    have h := (hw t).mul (hz t)
    have e1 : κ t • (-(w t * B t)) * z t = κ t • (-((w t * B t) * z t)) := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [frame_mul_eq_comp, smul_apply, neg_apply]
    have e2 : w t * (κ t • (B t * z t)) = κ t • (w t * (B t * z t)) := by
      apply ContinuousLinearMap.ext
      intro x
      simp only [frame_mul_eq_comp, smul_apply, map_smul]
    have hsum : κ t • (-((w t * B t) * z t)) + κ t • (w t * (B t * z t))
        = κ t • (-((w t * B t) * z t) + w t * (B t * z t)) :=
      (smul_add (κ t) _ _).symm
    have hval : κ t • (-(w t * B t)) * z t + w t * (κ t • (B t * z t)) = 0 := by
      rw [e1, e2, hsum, mul_assoc, neg_add_cancel, smul_zero]
    exact hval ▸ h
  have hdiff : Differentiable ℝ (fun s => w s * z s) := fun t => (hderiv t).differentiableAt
  have hzero : ∀ t, fderiv ℝ (fun s => w s * z s) t = 0 := by
    intro t
    have h := (hderiv t).hasFDerivAt.fderiv
    rw [h]
    apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_zero, zero_apply]
  intro t
  have h := is_const_of_fderiv_eq_zero hdiff hzero 0 t
  exact h.symm.trans h0

end Inverse


/-! ## The aligning step

The heart of the FRAME brick.  For `v ∈ range (π 0)` we show that the transported vector
`z t v = (γ t).2.1 v` stays in `range (π t)` for `t ∈ [0,1]`.  The defect
`Φ t := (1 - π t) (z t v)` satisfies the *homogeneous* linear equation

  `Φ' t = (-(π' t) + (1 - π t) * π' t) (Φ t)`,

because the non-`Φ` part `(1 - π t) (π' t (π t (z t v))) = π' t (π t (z t v))` cancels the
`-π' t` — the aligning identity `one_sub_mul_deriv`.  Since `Φ 0 = 0`, Mathlib's interval Grönwall
zero-lemma `eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right` (same file) gives `Φ ≡ 0`. -/

section Align

/-- `‖(1 : E →L[ℝ] E)‖ ≤ 1`. -/
lemma norm_one_frameEnd_le : ‖(1 : FrameEnd N)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  simp

/-- **The algebraic core of the aligning step.**  The functional
`A w := -(π' x w) + (1 - π x) (π' x w)` vanishes on `range (π x)` (the aligning identity) and is
therefore invariant under `1 - π x`. -/
lemma align_aux (π π' : ℝ → FrameEnd N) (hidem : ∀ t y, π t (π t y) = π t y)
    (hderiv : ∀ t, HasDerivAt (fun s : ℝ => π s) (π' t) t) (x : ℝ)
    (u : EuclideanSpace ℝ (Fin N)) :
    -(π' x u) + (1 - π x) (π' x u)
      = -(π' x ((1 - π x) u)) + (1 - π x) (π' x ((1 - π x) u)) := by
  have hA0 : ∀ w : EuclideanSpace ℝ (Fin N), π x w = w →
      -(π' x w) + (1 - π x) (π' x w) = 0 := by
    intro w hw
    rw [one_sub_mul_deriv π π' hidem hderiv x hw, neg_add_cancel]
  have key : ∀ a b : EuclideanSpace ℝ (Fin N),
      -(π' x (a + b)) + (1 - π x) (π' x (a + b))
        = (-(π' x a) + (1 - π x) (π' x a)) + (-(π' x b) + (1 - π x) (π' x b)) := by
    intro a b
    rw [map_add, map_add]
    abel
  have hdec : u = π x u + (1 - π x) u := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
    abel
  have step : -(π' x u) + (1 - π x) (π' x u)
      = (-(π' x (π x u)) + (1 - π x) (π' x (π x u)))
        + (-(π' x ((1 - π x) u)) + (1 - π x) (π' x ((1 - π x) u))) := by
    conv_lhs => rw [hdec]
    exact key (π x u) ((1 - π x) u)
  rw [step, hA0 (π x u) (hidem x u), zero_add]

/-- **The aligning step.**  If the cutoff is `1` on `[0,1]`, every `v ∈ range (π 0)` has
`z t v ∈ range (π t)` there. -/
theorem align_mem_range {R C M : ℝ} {π π' : ℝ → FrameEnd N}
    {γ : ℝ → ℝ × (FrameEnd N × FrameEnd N)}
    (hidem : ∀ t y, π t (π t y) = π t y)
    (hderiv : ∀ t, HasDerivAt (fun s : ℝ => π s) (π' t) t)
    (hC : 0 ≤ C) (hB : ∀ t, ‖π' t‖ ≤ C)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖π t‖ ≤ M)
    (hγ : IsIntegralCurve γ (fun _ z => satField (frameLin π') R z))
    (hγ0 : γ 0 = (0, (1, 1)))
    (hκ : ∀ t ∈ Set.Icc (0 : ℝ) 1, satCutoff R ‖(γ t).2‖ = 1) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ v, π 0 v = v → π t ((γ t).2.1 v) = (γ t).2.1 v := by
  intro t ht v hv
  have hcoeff : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      ‖-(π' x) + (1 - π x) * π' x‖ ≤ C + (1 + M) * C := by
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, le_of_lt hx.2⟩
    have h1 : ‖(1 : FrameEnd N) - π x‖ ≤ 1 + M := by
      calc ‖(1 : FrameEnd N) - π x‖ ≤ ‖(1 : FrameEnd N)‖ + ‖π x‖ := norm_sub_le _ _
        _ ≤ 1 + M := add_le_add norm_one_frameEnd_le (hM x hxI)
    calc ‖-(π' x) + (1 - π x) * π' x‖ ≤ ‖-(π' x)‖ + ‖(1 - π x) * π' x‖ := norm_add_le _ _
      _ ≤ ‖π' x‖ + ‖1 - π x‖ * ‖π' x‖ := by
          rw [norm_neg]
          exact add_le_add le_rfl (norm_mul_le _ _)
      _ ≤ C + (1 + M) * C := by
          refine add_le_add (hB x) (mul_le_mul h1 (hB x) (norm_nonneg _) ?_)
          linarith [hM x hxI, norm_nonneg (π x)]
  have hderiv_f : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => (1 - π s) ((γ s).2.1 v))
        ((-(π' x) + (1 - π x) * π' x) ((1 - π x) ((γ x).2.1 v))) x := by
    intro x hx
    have hxI : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx.1, le_of_lt hx.2⟩
    have hzx : HasDerivAt (fun s : ℝ => (γ s).2.1) (π' x * (γ x).2.1) x := by
      have h := frameCurve_z_deriv (π' := π') hγ hγ0 x
      rw [hκ x hxI] at h
      simpa using h
    have hS : HasDerivAt (fun s : ℝ => (1 : FrameEnd N) - π s) (-(π' x)) x := by
      have h := (hderiv x).const_sub (1 : FrameEnd N)
      simpa using h
    have hzv : HasDerivAt (fun s : ℝ => (γ s).2.1 v) ((π' x * (γ x).2.1) v) x := by
      have h := hzx.clm_apply (hasDerivAt_const x v)
      simpa using h
    have hmain := hS.clm_apply hzv
    have hval : (-(π' x)) ((γ x).2.1 v) + (1 - π x) ((π' x * (γ x).2.1) v)
        = (-(π' x) + (1 - π x) * π' x) ((1 - π x) ((γ x).2.1 v)) := by
      have h2 : (-(π' x) + (1 - π x) * π' x) ((1 - π x) ((γ x).2.1 v))
          = -(π' x ((1 - π x) ((γ x).2.1 v)))
            + (1 - π x) (π' x ((1 - π x) ((γ x).2.1 v))) := by
        rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.neg_apply, frame_mul_eq_comp]
      have h3 : (1 - π x) ((π' x * (γ x).2.1) v) = (1 - π x) (π' x ((γ x).2.1 v)) := by
        rw [frame_mul_eq_comp]
      rw [h2, h3, ContinuousLinearMap.neg_apply]
      exact align_aux π π' hidem hderiv x ((γ x).2.1 v)
    exact hval ▸ hmain
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) 1,
      ‖(-(π' x) + (1 - π x) * π' x) ((1 - π x) ((γ x).2.1 v))‖
        ≤ (C + (1 + M) * C) * ‖(1 - π x) ((γ x).2.1 v)‖ := by
    intro x hx
    calc ‖(-(π' x) + (1 - π x) * π' x) ((1 - π x) ((γ x).2.1 v))‖
        ≤ ‖-(π' x) + (1 - π x) * π' x‖ * ‖(1 - π x) ((γ x).2.1 v)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (C + (1 + M) * C) * ‖(1 - π x) ((γ x).2.1 v)‖ :=
          mul_le_mul_of_nonneg_right (hcoeff x hx) (norm_nonneg _)
  have hzcont : Continuous (fun s : ℝ => (γ s).2.1) :=
    continuous_iff_continuousAt.mpr
      (fun x => (frameCurve_z_deriv (π' := π') hγ hγ0 x).continuousAt)
  have hcont : ContinuousOn (fun s : ℝ => (1 - π s) ((γ s).2.1 v)) (Set.Icc 0 1) :=
    ((continuous_const.sub ((continuous_iff_continuousAt.mpr
        (fun x => (hderiv x).continuousAt)))).clm_apply (hzcont.clm_apply continuous_const)).continuousOn
  have hf0 : (1 - π 0) ((γ 0).2.1 v) = 0 := by
    have h1 : (γ 0).2.1 = (1 : FrameEnd N) := by rw [hγ0]
    have h2 : (1 : FrameEnd N) v = v := by simp
    rw [h1, h2, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, hv, sub_self]
  have hzero := eq_zero_of_abs_deriv_le_mul_abs_self_of_eq_zero_right
    (f := fun s : ℝ => (1 - π s) ((γ s).2.1 v))
    (f' := fun x : ℝ => (-(π' x) + (1 - π x) * π' x) ((1 - π x) ((γ x).2.1 v)))
    (K := C + (1 + M) * C) (a := 0) (b := 1)
    hcont (fun x hx => (hderiv_f x hx).hasDerivWithinAt) hf0 hbound
  have h := hzero t ht
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] at h
  exact (sub_eq_zero.mp h).symm

end Align


/-! ## Smoothness bootstrap

The last analytic input: a curve solving `z' = B t * z t` with `B` smooth is smooth, by a finite
induction on the order (if `z` is `C^k` then `z' = B * z` is `C^k`, so `z` is `C^{k+1}`). -/

section Smooth

/-- **Smoothness of the solution of a linear ODE with smooth (operator-valued) coefficient.** -/
theorem contDiff_of_hasDerivAt_mul {N : ℕ} {B z : ℝ → FrameEnd N}
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hz : ∀ t, HasDerivAt z (B t * z t) t) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z := by
  have hderiv : deriv z = fun t : ℝ => B t * z t := by
    funext t
    exact (hz t).deriv
  have hdiff : Differentiable ℝ z := fun t => (hz t).differentiableAt
  refine contDiff_infty.mpr (fun k => ?_)
  induction k with
  | zero => exact contDiff_zero.mpr hdiff.continuous
  | succ k ih =>
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨hdiff, fun h => absurd h (by simp), ?_⟩
      rw [hderiv]
      exact ((contDiff_infty.mp hB) k).mul ih

/-- The right-multiplication variant (used for the inverse family `w`). -/
theorem contDiff_of_hasDerivAt_mul' {N : ℕ} {B w : ℝ → FrameEnd N}
    (hB : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) B)
    (hw : ∀ t, HasDerivAt w (-(w t * B t)) t) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := by
  have hderiv : deriv w = fun t : ℝ => -(w t * B t) := by
    funext t
    exact (hw t).deriv
  have hdiff : Differentiable ℝ w := fun t => (hw t).differentiableAt
  refine contDiff_infty.mpr (fun k => ?_)
  induction k with
  | zero => exact contDiff_zero.mpr hdiff.continuous
  | succ k ih =>
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨hdiff, fun h => absurd h (by simp), ?_⟩
      rw [hderiv]
      exact (ih.mul ((contDiff_infty.mp hB) k)).neg

end Smooth


/-! ## Packaging into linear equivalences -/

section Package

/-- **Packaging.**  A smooth pair `(w, z)` of operator families with `w t * z t = 1` for all `t`
gives a smooth family of linear equivalences acting as `w`, with inverse family acting as `z`. -/
theorem exists_linearEquiv_family {N : ℕ} {z w : ℝ → FrameEnd N}
    (hzw : ∀ t, w t * z t = 1)
    (hz : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) z)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) :
    ∃ M : ℝ → (EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)),
      (∀ t y, M t y = w t y) ∧ (∀ t y, (M t).symm y = z t y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => M p.1 p.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => (M p.1).symm p.2) := by
  have hmul : ∀ t y, w t (z t y) = y := fun t y => by
    have h := congrArg (fun T : FrameEnd N => T y) (hzw t)
    simpa [frame_mul_eq_comp] using h
  have hsurj : ∀ t, Function.Surjective (w t) := fun t y => ⟨z t y, hmul t y⟩
  have hinj : ∀ t, Function.Injective (w t) := fun t =>
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mpr (hsurj t)
  have hleft : ∀ t y, z t (w t y) = y := fun t y => hinj t (by
    have h := congrArg (fun T : FrameEnd N => T (w t y)) (hzw t)
    simpa [frame_mul_eq_comp] using h)
  let M : ℝ → (EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)) := fun t =>
    (LinearEquiv.mk ((w t).toLinearMap) (z t) (hleft t) (hmul t)).toContinuousLinearEquiv
  have hcoe : ∀ t y, M t y = w t y := fun t y => rfl
  have hinv : ∀ t y, (M t).symm y = z t y := fun t y => rfl
  refine ⟨M, hcoe, hinv, ?_, ?_⟩
  · have h1 : (fun p : ℝ × EuclideanSpace ℝ (Fin N) => M p.1 p.2)
        = fun p : ℝ × EuclideanSpace ℝ (Fin N) => w p.1 p.2 := funext fun p => hcoe p.1 p.2
    rw [h1]
    exact (hw.comp contDiff_fst).clm_apply contDiff_snd
  · have h1 : (fun p : ℝ × EuclideanSpace ℝ (Fin N) => (M p.1).symm p.2)
        = fun p : ℝ × EuclideanSpace ℝ (Fin N) => z p.1 p.2 := funext fun p => hinv p.1 p.2
    rw [h1]
    exact (hz.comp contDiff_fst).clm_apply contDiff_snd

end Package

/-! ## The assembled brick (statement)

Once `pair_gronwall` is available, the rest of the argument is:

* `w t * z t = 1` for every `t`: `(w * z)' = w' * z + w * z' = κ • (-(w B) z + w (B z)) = 0` (the two
  factors share the cutoff `κ = satCutoff R ‖(z,w)‖`);
* the *aligning identity* `(1 - π t) (B t u) = B t u` for `u ∈ range (π t)`, from `π u = u` and
  `π t * B t * π t = 0` (`idem_mul_deriv_mul`), which makes `Φ t := (1 - π t) (z t v)` solve the
  *homogeneous* linear equation `Φ' = (-(B t) + (1 - π t) * B t) Φ`, so `Φ ≡ 0` by `pair_gronwall`
  (applied with `ζ 0 = 0`, whose right-hand side is `0`) — i.e. `z t (range (π 0)) ⊆ range (π t)`;
* hence `M t := w t` (a linear equivalence, since `w t * z t = 1`) carries `range (π t)` into
  `range (π 0)`, is bounded by `exp C`, and is smooth: `z` and `w` solve the *linear* equations
  `z' = B t * z`, `w' = -(w * B t)` for all `t` (the cutoff is `1` on `[0,1]` by `pair_gronwall`,
  and both sides vanish off `[0,1]` because `B t = 0` there), so smoothness follows by bootstrapping
  `ContDiff ℝ k` with `contDiff_succ_iff_deriv`.
-/

/-- **The FRAME brick.**  A smooth family of projections `π`, constant outside `[0,1]`, of constant
rank, is trivialised by a smooth family of linear equivalences carrying `range (π t)` into
`range (π 0)` — on `[0,1]`, which is the range on which the flattening consumes it.

`π'` is the derivative of the family (given as data: the caller has the plane family, hence its
derivative); `hleft`/`hright` say that `π` is constant off `(0,1)`; `hrank` is the (automatic, but
proved elsewhere) constancy of the rank of a continuous family of projections — it is what converts
`z t '' range (π 0) ⊆ range (π t)` into an equality and hence dualises to
`w t '' range (π t) ⊆ range (π 0)`. -/
theorem frame_family_trivialisation {N : ℕ}
    (π π' : ℝ → FrameEnd N)
    (hidem : ∀ t y, π t (π t y) = π t y)
    (hderiv : ∀ t, HasDerivAt (fun s : ℝ => π s) (π' t) t)
    (hleft : ∀ t, t ≤ 0 → π t = π 0)
    (hright : ∀ t, 1 ≤ t → π t = π 1)
    (hBpos : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, ‖π' t‖ ≤ C)
    (hBlip : ∃ LA : ℝ, 0 ≤ LA ∧ ∀ t s, ‖π' t - π' s‖ ≤ LA * |t - s|)
    (hrank : ∀ t, Module.finrank ℝ (LinearMap.range (π t).toLinearMap)
      = Module.finrank ℝ (LinearMap.range (π 0).toLinearMap))
    (hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) π') :
    ∃ M : ℝ → (EuclideanSpace ℝ (Fin N) ≃L[ℝ] EuclideanSpace ℝ (Fin N)),
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y, π 0 (M t (π t y)) = M t (π t y)) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y, ‖M t y‖ ≤ C * ‖y‖) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => M p.1 p.2) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × EuclideanSpace ℝ (Fin N) => (M p.1).symm p.2) := by
  obtain ⟨C, hC, hB⟩ := hBpos
  obtain ⟨LA, hLA, hBlip'⟩ := hBlip
  have hπcont : Continuous (fun t : ℝ => π t) :=
    continuous_iff_continuousAt.mpr (fun x => (hderiv x).continuousAt)
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) 1) hπcont.continuousOn
  set R : ℝ := Real.exp C + 2 with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  obtain ⟨γ, hγ0, hγ⟩ := exists_frameCurve (π' := π') R C LA hR hC hLA hB hBlip'
  have hgron : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖(γ t).2‖ ≤ Real.exp C * ‖(γ 0).2‖ := by
    intro t ht
    exact pair_gronwall hC hB (fun s => satCutoff_nonneg R _) (fun s => satCutoff_le_one R _)
      (fun s => hasDerivAt_snd_satField (A := frameLin π') hγ hγ0 rfl s) t ht
  have hγ02 : ‖(γ 0).2‖ ≤ 1 := by
    rw [hγ0]
    show max ‖(1 : FrameEnd N)‖ ‖(1 : FrameEnd N)‖ ≤ 1
    exact max_le norm_one_frameEnd_le norm_one_frameEnd_le
  have hκ : ∀ t ∈ Set.Icc (0 : ℝ) 1, satCutoff R ‖(γ t).2‖ = 1 := by
    intro t ht
    refine satCutoff_eq_one hR ?_
    calc ‖(γ t).2‖ ≤ Real.exp C * ‖(γ 0).2‖ := hgron t ht
      _ ≤ Real.exp C * 1 := mul_le_mul_of_nonneg_left hγ02 (Real.exp_pos C).le
      _ ≤ R := by rw [hRdef]; linarith [Real.exp_pos C]
  have halign := align_mem_range (R := R) (C := C) (M := M₀) hidem hderiv hC hB hM₀ hγ hγ0 hκ
  have hz : ∀ t, HasDerivAt (fun s : ℝ => (γ s).2.1)
      ((satCutoff R ‖(γ t).2‖) • (π' t * (γ t).2.1)) t :=
    fun t => frameCurve_z_deriv (π' := π') hγ hγ0 t
  have hw : ∀ t, HasDerivAt (fun s : ℝ => (γ s).2.2)
      ((satCutoff R ‖(γ t).2‖) • (-((γ t).2.2 * π' t))) t :=
    fun t => frameCurve_w_deriv (π' := π') hγ hγ0 t
  have hzw : ∀ t, (γ t).2.2 * (γ t).2.1 = 1 := by
    refine mul_eq_one_of_hasDerivAt hz hw ?_
    rw [hγ0]
    exact one_mul 1
  have hzero_off : ∀ t, t ∉ Set.Icc (0 : ℝ) 1 → π' t = 0 := by
    intro t ht
    have ht' : t < 0 ∨ 1 < t := by
      rw [Set.mem_Icc, not_and_or] at ht
      push_neg at ht
      exact ht
    rcases ht' with h | h
    · exact deriv_eq_zero_of_lt_zero (π := π) hleft hderiv h
    · exact deriv_eq_zero_of_one_lt (π := π) hright hderiv h
  have hlinz : ∀ t, HasDerivAt (fun s : ℝ => (γ s).2.1) (π' t * (γ t).2.1) t := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · have h := hz t
      rw [hκ t ht] at h
      simpa using h
    · have h0 := hzero_off t ht
      have hval : (satCutoff R ‖(γ t).2‖) • (π' t * (γ t).2.1) = π' t * (γ t).2.1 := by
        rw [h0]
        apply ContinuousLinearMap.ext
        intro x
        simp
      exact hval ▸ hz t
  have hlinw : ∀ t, HasDerivAt (fun s : ℝ => (γ s).2.2) (-((γ t).2.2 * π' t)) t := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) 1
    · have h := hw t
      rw [hκ t ht] at h
      simpa using h
    · have h0 := hzero_off t ht
      have hval : (satCutoff R ‖(γ t).2‖) • (-((γ t).2.2 * π' t)) = -((γ t).2.2 * π' t) := by
        rw [h0]
        apply ContinuousLinearMap.ext
        intro x
        simp
      exact hval ▸ hw t
  obtain ⟨M, hM, hMinv, hMs, hMis⟩ := exists_linearEquiv_family (z := fun s => (γ s).2.1)
    (w := fun s => (γ s).2.2) hzw (contDiff_of_hasDerivAt_mul hsmooth hlinz)
    (contDiff_of_hasDerivAt_mul' hsmooth hlinw)
  have hfun : ∀ t : ℝ, (((M t).symm :
      EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)))
      = ((γ t).2.1 : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) := by
    intro t
    refine LinearMap.ext (fun s => ?_)
    exact hMinv t s
  refine ⟨M, ?_, ?_, hMs, hMis⟩
  · intro t ht y
    set S : Submodule ℝ (EuclideanSpace ℝ (Fin N)) := LinearMap.range (π 0).toLinearMap with hS
    set T : Submodule ℝ (EuclideanSpace ℝ (Fin N)) := LinearMap.range (π t).toLinearMap with hT
    have hmaps : S.map (((γ t).2.1 :
        EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N))) ≤ T := by
      rintro z ⟨s, hs, rfl⟩
      have hvs : π 0 s = s := by
        obtain ⟨v, hv⟩ := hs
        rw [← hv]
        exact hidem 0 v
      have hz : π t ((γ t).2.1 s) = (γ t).2.1 s := halign t ht s hvs
      exact ⟨(γ t).2.1 s, hz⟩
    have hfr : Module.finrank ℝ (S.map (((γ t).2.1 :
        EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)))) = Module.finrank ℝ T := by
      have hcongr : S.map (((γ t).2.1 :
          EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)))
          = S.map (((M t).symm).toLinearEquiv : EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N)) := by
        congr 1
        exact (hfun t).symm
      rw [hcongr, LinearEquiv.finrank_map_eq ((M t).symm).toLinearEquiv S]
      have h2 : Module.finrank ℝ S = Module.finrank ℝ T := by
        rw [hT]
        exact (hrank t).symm
      exact h2
    have heq : S.map (((γ t).2.1 :
        EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N))) = T :=
      Submodule.eq_of_le_of_finrank_eq hmaps hfr
    have hy : (γ t).2.2 (π t y) ∈ S := by
      have hmem : π t y ∈ S.map (((γ t).2.1 :
          EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin N))) := by
        rw [heq]
        exact ⟨y, rfl⟩
      obtain ⟨s, hs, hsz⟩ := hmem
      have h1 : (γ t).2.2 ((γ t).2.1 s) = s := by
        have h := congrArg (fun T' : FrameEnd N => T' s) (hzw t)
        simpa [frame_mul_eq_comp] using h
      have h2 : (γ t).2.2 (π t y) = s := by
        rw [← hsz]
        exact h1
      rw [h2]
      exact hs
    have h3 : π 0 ((γ t).2.2 (π t y)) = (γ t).2.2 (π t y) := by
      obtain ⟨u, hu⟩ := hy
      rw [← hu]
      exact hidem 0 u
    rw [hM t (π t y)]
    exact h3
  · refine ⟨Real.exp C + 1, by positivity, ?_⟩
    intro t ht y
    rw [hM t y]
    calc ‖(γ t).2.2 y‖ ≤ ‖(γ t).2.2‖ * ‖y‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ Real.exp C * ‖y‖ := by
          refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg y)
          calc ‖(γ t).2.2‖ ≤ ‖(γ t).2‖ := by
                rw [Prod.norm_def]; exact le_max_right _ _
            _ ≤ Real.exp C * ‖(γ 0).2‖ := hgron t ht
            _ ≤ Real.exp C * 1 := mul_le_mul_of_nonneg_left hγ02 (Real.exp_pos C).le
            _ = Real.exp C := mul_one _
      _ ≤ (Real.exp C + 1) * ‖y‖ := by
          have h1 : (0:ℝ) ≤ ‖y‖ := norm_nonneg y
          have h2 : (0:ℝ) < Real.exp C := Real.exp_pos C
          nlinarith


end Work.Whitney.CutPush
