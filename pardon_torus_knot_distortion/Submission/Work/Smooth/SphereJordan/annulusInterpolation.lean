import Mathlib
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.InnermostDisk.descend_continuousMap
import Submission.Work.InnermostDisk.polarCoord_surjective

/-!
# Radial interpolation of a circle homeomorphism on the annulus

Given a continuous, strictly increasing `χ : ℝ → ℝ` with `χ (θ + 2π) = χ θ + 2π` (a lift of an
orientation preserving homeomorphism of the circle), we build a homeomorphism `Φ` of the closed
unit disc `𝔻 ⊆ ℂ` which

* fixes the boundary circle `∂𝔻` pointwise,
* carries the concentric circle of radius `1/2` onto itself, moving `(1/2) e^{iθ}` to
  `(1/2) e^{i χ θ}`,
* preserves the norm `‖Φ z‖ = ‖z‖`.

The construction is the obvious one in polar coordinates: writing `z = r e^{iθ}` we set
`Φ z = r e^{i Ψ(r,θ)}` where `Ψ(r,θ) = θ + t(r) (χ θ - θ)` interpolates between the identity on
`∂𝔻` (where the weight `t(r)` vanishes) and `χ` on the circle of radius `1/2` (where `t(r) = 1`).

The map is exhibited as a *descent* of a continuous map on the compact rectangle
`[0,2π] × [0,1]` along the polar coordinate map `(θ,r) ↦ r e^{iθ}`, so its continuity is
automatic (`Work.InnermostDisk.descend_continuousMap`).  It is then shown to be a bijection, hence
a homeomorphism since `𝔻` is compact Hausdorff.
-/

namespace Work.Smooth.SphereJordan

noncomputable section

open Set

/-! ## Clamping and the interpolation weight -/

/-- `clamp01 r` is `r` clamped to the interval `[0,1]`. -/
def clamp01 (r : ℝ) : ℝ := max 0 (min r 1)

theorem continuous_clamp01 : Continuous clamp01 := by
  unfold clamp01; fun_prop

theorem clamp01_nonneg (r : ℝ) : 0 ≤ clamp01 r := le_max_left _ _

theorem clamp01_le_one (r : ℝ) : clamp01 r ≤ 1 :=
  max_le (by norm_num) (min_le_right _ _)

theorem clamp01_of_mem {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : clamp01 r = r := by
  unfold clamp01
  rw [min_eq_left h1, max_eq_right h0]

/-- The norm of a nonnegative real, as a complex number. -/
theorem norm_coe_ofReal {r : ℝ} (hr : 0 ≤ r) : ‖((r : ℝ) : ℂ)‖ = r := by
  rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self hr]

/-- The interpolation weight: `1` on `[0,1/2]`, `0` on `[1,∞)`, and linear in between. -/
def interpT (r : ℝ) : ℝ := max 0 (min (2 * (1 - r)) 1)

theorem continuous_interpT : Continuous interpT := by
  unfold interpT; fun_prop

theorem interpT_nonneg (r : ℝ) : 0 ≤ interpT r := le_max_left _ _

theorem interpT_le_one (r : ℝ) : interpT r ≤ 1 :=
  max_le (by norm_num) (min_le_right _ _)

theorem interpT_one : interpT 1 = 0 := by unfold interpT; norm_num

theorem interpT_half : interpT (1 / 2) = 1 := by unfold interpT; norm_num

/-- The interpolated angle at radius `r`: `θ` for `r = 1`, `χ θ` for `r ≤ 1/2`. -/
def psi (χ : ℝ → ℝ) (r θ : ℝ) : ℝ := θ + interpT r * (χ θ - θ)

theorem psi_eq (χ : ℝ → ℝ) (r θ : ℝ) :
    psi χ r θ = (1 - interpT r) * θ + interpT r * χ θ := by
  rw [psi]; ring

theorem psi_one (χ : ℝ → ℝ) (θ : ℝ) : psi χ 1 θ = θ := by
  rw [psi, interpT_one]; ring

theorem psi_half (χ : ℝ → ℝ) (θ : ℝ) : psi χ (1 / 2) θ = χ θ := by
  rw [psi, interpT_half]; ring

theorem continuous_psi (χ : ℝ → ℝ) (hχ : Continuous χ) :
    Continuous (fun p : ℝ × ℝ => psi χ p.2 p.1) := by
  have h : (fun p : ℝ × ℝ => psi χ p.2 p.1)
      = fun p : ℝ × ℝ => p.1 + interpT p.2 * (χ p.1 - p.1) := rfl
  rw [h]
  exact continuous_fst.add
    ((continuous_interpT.comp continuous_snd).mul ((hχ.comp continuous_fst).sub continuous_fst))

/-! ## Periodicity -/

/-- `θ ↦ χ θ - θ` is `2π`-periodic. -/
theorem chi_sub_periodic (χ : ℝ → ℝ)
    (hshift : ∀ θ : ℝ, χ (θ + 2 * Real.pi) = χ θ + 2 * Real.pi) :
    Function.Periodic (fun θ => χ θ - θ) (2 * Real.pi) := by
  intro θ
  show χ (θ + 2 * Real.pi) - (θ + 2 * Real.pi) = χ θ - θ
  rw [hshift θ]; ring

/-- `χ` shifts by `2πk` under `θ ↦ θ + 2πk`, for every integer `k`. -/
theorem chi_shift_int (χ : ℝ → ℝ)
    (hshift : ∀ θ : ℝ, χ (θ + 2 * Real.pi) = χ θ + 2 * Real.pi)
    (k : ℤ) (θ : ℝ) :
    χ (θ + k * (2 * Real.pi)) = χ θ + k * (2 * Real.pi) := by
  have hper := (chi_sub_periodic χ hshift).int_mul k
  have h : χ (θ + k * (2 * Real.pi)) - (θ + k * (2 * Real.pi)) = χ θ - θ := hper θ
  linarith

/-- The same for the interpolated angle `ψ`. -/
theorem psi_shift_int (χ : ℝ → ℝ)
    (hshift : ∀ θ : ℝ, χ (θ + 2 * Real.pi) = χ θ + 2 * Real.pi)
    (r : ℝ) (k : ℤ) (θ : ℝ) :
    psi χ r (θ + k * (2 * Real.pi)) = psi χ r θ + k * (2 * Real.pi) := by
  have hχ := chi_shift_int χ hshift k θ
  rw [psi, psi, hχ]
  ring

/-- The exponential of `ψ + 2πk`. -/
theorem exp_add_int_two_pi (ψ : ℝ) (k : ℤ) :
    Complex.exp (((ψ + k * (2 * Real.pi) : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((ψ : ℂ) * Complex.I) := by
  have h : ((ψ + k * (2 * Real.pi) : ℝ) : ℂ) * Complex.I
      = (ψ : ℂ) * Complex.I + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ## Monotonicity and surjectivity of `ψ r ·` -/

theorem psi_strictMono (χ : ℝ → ℝ) (hmono : StrictMono χ) (r : ℝ) :
    StrictMono (fun θ : ℝ => psi χ r θ) := by
  intro θ θ' hθ
  change psi χ r θ < psi χ r θ'
  rw [psi_eq, psi_eq]
  have ht0 : 0 ≤ interpT r := interpT_nonneg r
  have ht1 : interpT r ≤ 1 := interpT_le_one r
  have ha : 0 < θ' - θ := sub_pos.mpr hθ
  have hb : 0 < χ θ' - χ θ := sub_pos.mpr (hmono hθ)
  have key : (1 - interpT r) * θ' + interpT r * χ θ' - ((1 - interpT r) * θ + interpT r * χ θ)
      = (1 - interpT r) * (θ' - θ) + interpT r * (χ θ' - χ θ) := by ring
  rw [← sub_pos, key]
  by_cases h : interpT r ≤ 1 / 2
  · have h1 : (1 : ℝ) / 2 ≤ 1 - interpT r := by linarith
    have hle : (1 : ℝ) / 2 * (θ' - θ) ≤ (1 - interpT r) * (θ' - θ) :=
      mul_le_mul_of_nonneg_right h1 ha.le
    have hpos : 0 < (1 : ℝ) / 2 * (θ' - θ) := mul_pos (by norm_num) ha
    have hb' : 0 ≤ interpT r * (χ θ' - χ θ) := mul_nonneg ht0 hb.le
    linarith
  · push_neg at h
    have h2 : (1 : ℝ) / 2 ≤ interpT r := le_of_lt h
    have hle : (1 : ℝ) / 2 * (χ θ' - χ θ) ≤ interpT r * (χ θ' - χ θ) :=
      mul_le_mul_of_nonneg_right h2 hb.le
    have hpos : 0 < (1 : ℝ) / 2 * (χ θ' - χ θ) := mul_pos (by norm_num) hb
    have ha' : 0 ≤ (1 - interpT r) * (θ' - θ) := mul_nonneg (by linarith) ha.le
    linarith

/-- A continuous function on `ℝ` which shifts by a positive constant `c` is surjective. -/
theorem shift_surjective {f : ℝ → ℝ} (hfcont : Continuous f) {c : ℝ} (hc : 0 < c)
    (hshift : ∀ θ : ℝ, f (θ + c) = f θ + c) : Function.Surjective f := by
  intro y
  have hnat : ∀ n : ℕ, f ((n : ℝ) * c) = f 0 + (n : ℝ) * c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep : ((n + 1 : ℕ) : ℝ) * c = (n : ℝ) * c + c := by push_cast; ring
      rw [hstep, hshift, ih]; push_cast; ring
  have hnat' : ∀ n : ℕ, f (-((n : ℝ) * c)) = f 0 - (n : ℝ) * c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep : -(((n + 1 : ℕ) : ℝ) * c) = -((n : ℝ) * c) - c := by push_cast; ring
      rw [hstep]
      have hback : f (-((n : ℝ) * c) - c) = f (-((n : ℝ) * c)) - c := by
        have hh := hshift (-((n : ℝ) * c) - c)
        have hcc : -((n : ℝ) * c) - c + c = -((n : ℝ) * c) := by ring
        rw [hcc] at hh
        linarith
      rw [hback, ih]; push_cast; ring
  obtain ⟨N, hN⟩ := exists_nat_gt ((y - f 0) / c)
  obtain ⟨M, hM⟩ := exists_nat_gt (-((y - f 0) / c))
  have htop : y ≤ f ((N : ℝ) * c) := by
    rw [hnat N]
    have hNc : y - f 0 ≤ (N : ℝ) * c := by
      have h2 : (y - f 0) / c * c < (N : ℝ) * c := mul_lt_mul_of_pos_right hN hc
      rw [div_mul_cancel₀ _ (ne_of_gt hc)] at h2
      exact h2.le
    linarith
  have hbot : f (-((M : ℝ) * c)) ≤ y := by
    rw [hnat' M]
    have hMc : -((M : ℝ) * c) ≤ y - f 0 := by
      have h2 : -((y - f 0) / c) * c < (M : ℝ) * c := mul_lt_mul_of_pos_right hM hc
      have h3 : -((y - f 0) / c) * c = -(y - f 0) := by
        rw [neg_mul, div_mul_cancel₀ _ (ne_of_gt hc)]
      rw [h3] at h2
      linarith
    linarith
  have hM0 : (0 : ℝ) ≤ (M : ℝ) * c := mul_nonneg (Nat.cast_nonneg M) hc.le
  have hN0 : (0 : ℝ) ≤ (N : ℝ) * c := mul_nonneg (Nat.cast_nonneg N) hc.le
  have hab : -((M : ℝ) * c) ≤ (N : ℝ) * c := by linarith
  have hy : y ∈ Set.Icc (f (-((M : ℝ) * c))) (f ((N : ℝ) * c)) := ⟨hbot, htop⟩
  obtain ⟨θ, _, hθ⟩ := intermediate_value_Icc hab hfcont.continuousOn hy
  exact ⟨θ, hθ⟩

/-- The interpolated angle is surjective at every radius. -/
theorem psi_surjective (χ : ℝ → ℝ) (hcont : Continuous χ)
    (hshift : ∀ θ : ℝ, χ (θ + 2 * Real.pi) = χ θ + 2 * Real.pi) (r : ℝ) :
    Function.Surjective (fun θ : ℝ => psi χ r θ) := by
  have hcont' : Continuous (fun θ : ℝ => psi χ r θ) := by
    have h : (fun θ : ℝ => psi χ r θ)
        = fun θ : ℝ => θ + interpT r * (χ θ - θ) := rfl
    rw [h]
    exact continuous_id.add (continuous_const.mul (hcont.sub continuous_id))
  have hc : (0 : ℝ) < 2 * Real.pi := by positivity
  refine shift_surjective (c := 2 * Real.pi) hcont' hc ?_
  intro θ
  have h := psi_shift_int χ hshift r 1 θ
  simpa using h

/-! ## The polar angle of a unit complex number -/

/-- Every unit complex number is `e^{iθ}` for some `θ ∈ [0, 2π]`. -/
theorem exists_angle_mem_Icc (u : ℂ) (hu : ‖u‖ = 1) :
    ∃ θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi), Complex.exp ((θ : ℂ) * Complex.I) = u := by
  obtain ⟨r, θ, hr0, hr1, hθ0, hθ1, heq⟩ :=
    Work.InnermostDisk.polarCoord_surjective u (le_of_eq hu)
  have hr1' : r = 1 := by
    have hnorm := congrArg (fun z : ℂ => ‖z‖) heq
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] at hnorm
    rw [norm_coe_ofReal hr0, hu] at hnorm
    exact hnorm
  exact ⟨θ, ⟨hθ0, hθ1⟩, by simpa [hr1'] using heq⟩

/-! ## The polar and twisted polar maps into the disc -/

/-- The polar coordinate map `(θ,r) ↦ r e^{iθ}`, as a map to `ℂ`. -/
def polC (p : ℝ × ℝ) : ℂ :=
  ((clamp01 p.2 : ℝ) : ℂ) * Complex.exp (((p.1 : ℝ) : ℂ) * Complex.I)

/-- The twisted polar coordinate map `(θ,r) ↦ r e^{i ψ(r,θ)}`, as a map to `ℂ`. -/
def twiC (χ : ℝ → ℝ) (p : ℝ × ℝ) : ℂ :=
  ((clamp01 p.2 : ℝ) : ℂ) * Complex.exp (((psi χ p.2 p.1 : ℝ) : ℂ) * Complex.I)

theorem polC_apply (θ r : ℝ) :
    polC (θ, r) = ((clamp01 r : ℝ) : ℂ) * Complex.exp (((θ : ℝ) : ℂ) * Complex.I) := rfl

theorem twiC_apply (χ : ℝ → ℝ) (θ r : ℝ) :
    twiC χ (θ, r) = ((clamp01 r : ℝ) : ℂ) * Complex.exp (((psi χ r θ : ℝ) : ℂ) * Complex.I) :=
  rfl

theorem norm_polC (p : ℝ × ℝ) : ‖polC p‖ = clamp01 p.2 := by
  rw [polC, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_coe_ofReal (clamp01_nonneg p.2)]

theorem norm_twiC (χ : ℝ → ℝ) (p : ℝ × ℝ) : ‖twiC χ p‖ = clamp01 p.2 := by
  rw [twiC, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, norm_coe_ofReal (clamp01_nonneg p.2)]

theorem continuous_polC : Continuous polC := by
  unfold polC
  exact (Complex.continuous_ofReal.comp (continuous_clamp01.comp continuous_snd)).mul
    (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp continuous_fst).mul
      continuous_const))

theorem continuous_twiC (χ : ℝ → ℝ) (hχ : Continuous χ) : Continuous (twiC χ) := by
  unfold twiC
  exact (Complex.continuous_ofReal.comp (continuous_clamp01.comp continuous_snd)).mul
    (Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_psi χ hχ)).mul continuous_const))

/-- The polar map into the model disc. -/
def polDisc (p : ℝ × ℝ) : Disc :=
  ⟨polC p, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_polC]
    exact clamp01_le_one p.2⟩

/-- The twisted polar map into the model disc. -/
def twiDisc (χ : ℝ → ℝ) (p : ℝ × ℝ) : Disc :=
  ⟨twiC χ p, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_twiC]
    exact clamp01_le_one p.2⟩

theorem polDisc_coe (p : ℝ × ℝ) : ((polDisc p : Disc) : ℂ) = polC p := rfl

theorem twiDisc_coe (χ : ℝ → ℝ) (p : ℝ × ℝ) :
    ((twiDisc χ p : Disc) : ℂ) = twiC χ p := rfl

theorem continuous_polDisc : Continuous polDisc :=
  Continuous.subtype_mk continuous_polC _

theorem continuous_twiDisc (χ : ℝ → ℝ) (hχ : Continuous χ) : Continuous (twiDisc χ) :=
  Continuous.subtype_mk (continuous_twiC χ hχ) _

theorem norm_coe_polDisc (p : ℝ × ℝ) : ‖((polDisc p : Disc) : ℂ)‖ = clamp01 p.2 := by
  rw [polDisc_coe, norm_polC]

theorem norm_coe_twiDisc (χ : ℝ → ℝ) (p : ℝ × ℝ) :
    ‖((twiDisc χ p : Disc) : ℂ)‖ = clamp01 p.2 := by
  rw [twiDisc_coe, norm_twiC]

/-! ## Descent along the polar coordinate map -/

/-- The compact rectangle `[0,2π] × [0,1]` of polar coordinates. -/
def polSet : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) 1

theorem isCompact_polSet : IsCompact polSet := isCompact_Icc.prod isCompact_Icc

theorem compactSpace_polSet : CompactSpace polSet := isCompact_iff_compactSpace.mp isCompact_polSet

/-- The polar coordinate map `(θ,r) ↦ r e^{iθ}` of the model disc. -/
def polMap : polSet → Disc := fun x => polDisc x.1

/-- The twisted polar coordinate map `(θ,r) ↦ r e^{i ψ(r,θ)}`. -/
def twiMap (χ : ℝ → ℝ) : polSet → Disc := fun x => twiDisc χ x.1

theorem continuous_polMap : Continuous polMap :=
  continuous_polDisc.comp continuous_subtype_val

theorem continuous_twiMap (χ : ℝ → ℝ) (hχ : Continuous χ) : Continuous (twiMap χ) :=
  (continuous_twiDisc χ hχ).comp continuous_subtype_val

theorem norm_coe_polMap (x : polSet) : ‖((polMap x : Disc) : ℂ)‖ = clamp01 x.1.2 :=
  norm_coe_polDisc x.1

theorem norm_coe_twiMap (χ : ℝ → ℝ) (x : polSet) :
    ‖((twiMap χ x : Disc) : ℂ)‖ = clamp01 x.1.2 :=
  norm_coe_twiDisc χ x.1

/-- The polar coordinate map is surjective onto the model disc. -/
theorem polMap_surjective : Function.Surjective polMap := by
  intro z
  have hz : ‖((z : Disc) : ℂ)‖ ≤ 1 := by
    have h := z.2
    rwa [Metric.mem_closedBall, dist_zero_right] at h
  obtain ⟨r, θ, hr0, hr1, hθ0, hθ1, heq⟩ :=
    Work.InnermostDisk.polarCoord_surjective ((z : Disc) : ℂ) hz
  refine ⟨⟨(θ, r), ⟨hθ0, hθ1⟩, ⟨hr0, hr1⟩⟩, ?_⟩
  apply Subtype.ext
  change polC (θ, r) = ((z : Disc) : ℂ)
  rw [polC_apply, clamp01_of_mem hr0 hr1]
  exact heq

/-! ## Injectivity of `θ ↦ e^{iθ}`-equalities -/

theorem ofReal_mul_I_inj {a b : ℝ} (h : (a : ℂ) * Complex.I = (b : ℂ) * Complex.I) : a = b := by
  have h2 : (((a - b : ℝ)) : ℂ) * Complex.I = 0 := by
    rw [Complex.ofReal_sub, sub_mul, h, sub_self]
  have h3 : (((a - b : ℝ)) : ℂ) = 0 :=
    (mul_eq_zero.mp h2).resolve_right Complex.I_ne_zero
  exact sub_eq_zero.mp (Complex.ofReal_inj.mp h3)

/-- `e^{iθ} = e^{iθ'}` forces `θ - θ'` to be an integer multiple of `2π`. -/
theorem expeq_iff_real {θ θ' : ℝ}
    (h : Complex.exp ((θ : ℂ) * Complex.I) = Complex.exp ((θ' : ℂ) * Complex.I)) :
    ∃ k : ℤ, θ = θ' + k * (2 * Real.pi) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  refine ⟨n, ?_⟩
  have hn' : (θ : ℂ) * Complex.I
      = ((θ' + (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
    rw [hn]; push_cast; ring
  exact ofReal_mul_I_inj hn'

/-! ## Well-definedness of the twisted map on the disc -/

theorem twiMap_fiber (χ : ℝ → ℝ)
    (hshift : ∀ θ : ℝ, χ (θ + 2 * Real.pi) = χ θ + 2 * Real.pi)
    {x y : polSet} (h : polMap x = polMap y) : twiMap χ x = twiMap χ y := by
  obtain ⟨⟨θ, r⟩, hxmem⟩ := x
  obtain ⟨hθmem, hrmem⟩ := hxmem
  obtain ⟨⟨θ', r'⟩, hymem⟩ := y
  obtain ⟨hθ'mem, hr'mem⟩ := hymem
  have hr0 : 0 ≤ r := hrmem.1
  have hr1 : r ≤ 1 := hrmem.2
  have hr0' : 0 ≤ r' := hr'mem.1
  have hr1' : r' ≤ 1 := hr'mem.2
  have hc : polC (θ, r) = polC (θ', r') := congrArg (fun w : Disc => (w : ℂ)) h
  have hnn : clamp01 r = clamp01 r' := by
    rw [← norm_polC (θ, r), ← norm_polC (θ', r'), hc]
  have hrr : r = r' := by
    rwa [clamp01_of_mem hr0 hr1, clamp01_of_mem hr0' hr1'] at hnn
  apply Subtype.ext
  change twiC χ (θ, r) = twiC χ (θ', r')
  rw [twiC_apply, twiC_apply, clamp01_of_mem hr0 hr1, clamp01_of_mem hr0' hr1', hrr.symm]
  by_cases hrz : r = 0
  · rw [hrz]; simp
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrz)
    have hmain : Complex.exp ((θ : ℂ) * Complex.I) = Complex.exp ((θ' : ℂ) * Complex.I) := by
      have hc2 : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)
          = (r : ℂ) * Complex.exp ((θ' : ℂ) * Complex.I) := by
        have hthis := hc
        rw [polC_apply, polC_apply, clamp01_of_mem hr0 hr1, clamp01_of_mem hr0' hr1',
          hrr.symm] at hthis
        exact hthis
      exact mul_left_cancel₀ (by exact_mod_cast (ne_of_gt hrpos)) hc2
    obtain ⟨k, hk⟩ := expeq_iff_real hmain
    have hpsi : psi χ r θ = psi χ r θ' + k * (2 * Real.pi) := by
      rw [hk, psi_shift_int χ hshift r k θ']
    rw [hpsi, exp_add_int_two_pi]

/-- The twisted map is continuous on the disc. -/
theorem exists_continuous_twist (χ : ℝ → ℝ) (hcont : Continuous χ)
    (hshift : ∀ θ : ℝ, χ (θ + 2 * Real.pi) = χ θ + 2 * Real.pi) :
    ∃ Φ : Disc → Disc, Continuous Φ ∧ ∀ p : polSet, Φ (polMap p) = twiMap χ p := by
  letI : CompactSpace polSet := compactSpace_polSet
  exact Work.InnermostDisk.descend_continuousMap continuous_polMap polMap_surjective
    (continuous_twiMap χ hcont) (fun x y h => twiMap_fiber χ hshift h)

/-! ## The twisted map is a homeomorphism -/

theorem twist_zero (χ : ℝ → ℝ) (Φ : Disc → Disc)
    (hΦ : ∀ p : polSet, Φ (polMap p) = twiMap χ p) : Φ 0 = 0 := by
  set x : polSet := ⟨(0, 0), ⟨⟨le_refl (0 : ℝ), by positivity⟩,
    ⟨le_refl (0 : ℝ), by norm_num⟩⟩⟩
  have hx : polMap x = 0 := by
    apply Subtype.ext
    change polC (0, 0) = ((0 : Disc) : ℂ)
    rw [polC_apply, clamp01_of_mem (le_refl (0 : ℝ)) (by norm_num)]
    simp
  conv_lhs => rw [← hx]
  rw [hΦ x]
  apply Subtype.ext
  change twiC χ (0, 0) = ((0 : Disc) : ℂ)
  rw [twiC_apply, clamp01_of_mem (le_refl (0 : ℝ)) (by norm_num)]
  simp

theorem twiMap_polMap_eq (χ : ℝ → ℝ) (hmono : StrictMono χ)
    (hshift : ∀ θ : ℝ, χ (θ + 2 * Real.pi) = χ θ + 2 * Real.pi) {x y : polSet}
    (h : twiMap χ x = twiMap χ y) : polMap x = polMap y := by
  obtain ⟨⟨θ, r⟩, hxmem⟩ := x
  obtain ⟨hθmem, hrmem⟩ := hxmem
  obtain ⟨⟨θ', r'⟩, hymem⟩ := y
  obtain ⟨hθ'mem, hr'mem⟩ := hymem
  have hr0 : 0 ≤ r := hrmem.1
  have hr1 : r ≤ 1 := hrmem.2
  have hr0' : 0 ≤ r' := hr'mem.1
  have hr1' : r' ≤ 1 := hr'mem.2
  have hc : twiC χ (θ, r) = twiC χ (θ', r') := congrArg (fun w : Disc => (w : ℂ)) h
  have hnn : clamp01 r = clamp01 r' := by
    rw [← norm_twiC χ (θ, r), ← norm_twiC χ (θ', r'), hc]
  have hrr : r = r' := by
    rwa [clamp01_of_mem hr0 hr1, clamp01_of_mem hr0' hr1'] at hnn
  by_cases hrz : r = 0
  · have hr'z : r' = 0 := by rw [← hrr]; exact hrz
    apply Subtype.ext
    change polC (θ, r) = polC (θ', r')
    rw [polC_apply, polC_apply, hrz, hr'z,
      clamp01_of_mem (le_refl (0 : ℝ)) (by norm_num)]
    simp
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrz)
    have hmain : (clamp01 r : ℂ) * Complex.exp (((psi χ r θ : ℝ) : ℂ) * Complex.I)
        = (clamp01 r' : ℂ) * Complex.exp (((psi χ r' θ' : ℝ) : ℂ) * Complex.I) := by
      have hthis := hc
      rw [twiC_apply, twiC_apply] at hthis
      exact hthis
    have hexp : Complex.exp (((psi χ r θ : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((psi χ r θ' : ℝ) : ℂ) * Complex.I) := by
      rw [clamp01_of_mem hr0 hr1, clamp01_of_mem hr0' hr1', hrr.symm] at hmain
      exact mul_left_cancel₀ (by exact_mod_cast (ne_of_gt hrpos)) hmain
    obtain ⟨k, hk⟩ := expeq_iff_real hexp
    have hEq : psi χ r (θ' + k * (2 * Real.pi)) = psi χ r θ := by
      rw [psi_shift_int χ hshift r k θ']
      exact hk.symm
    have hkθ : θ' + k * (2 * Real.pi) = θ := (psi_strictMono χ hmono r).injective hEq
    have hexpθ : Complex.exp ((θ : ℂ) * Complex.I) = Complex.exp ((θ' : ℂ) * Complex.I) := by
      have hθθ' : θ = θ' + k * (2 * Real.pi) := hkθ.symm
      rw [hθθ', exp_add_int_two_pi]
    apply Subtype.ext
    change polC (θ, r) = polC (θ', r')
    rw [polC_apply, polC_apply, clamp01_of_mem hr0 hr1, clamp01_of_mem hr0' hr1',
      hrr.symm, hexpθ]

theorem twist_injective (χ : ℝ → ℝ) (hmono : StrictMono χ)
    (hshift : ∀ θ : ℝ, χ (θ + 2 * Real.pi) = χ θ + 2 * Real.pi) (Φ : Disc → Disc)
    (hΦ : ∀ p : polSet, Φ (polMap p) = twiMap χ p) : Function.Injective Φ := by
  intro z z' hzz'
  obtain ⟨x, hx⟩ := polMap_surjective z
  obtain ⟨y, hy⟩ := polMap_surjective z'
  have htwi : twiMap χ x = twiMap χ y := by
    rw [← hΦ x, ← hΦ y, hx, hy, hzz']
  have hp : polMap x = polMap y := twiMap_polMap_eq χ hmono hshift htwi
  rw [← hx, ← hy, hp]

theorem twist_surjective (χ : ℝ → ℝ) (hcont : Continuous χ)
    (hshift : ∀ θ : ℝ, χ (θ + 2 * Real.pi) = χ θ + 2 * Real.pi) (Φ : Disc → Disc)
    (hΦ : ∀ p : polSet, Φ (polMap p) = twiMap χ p) : Function.Surjective Φ := by
  intro w
  obtain ⟨y, hy⟩ := polMap_surjective w
  obtain ⟨⟨θ₀, r⟩, hymem⟩ := y
  obtain ⟨hθ₀mem, hrmem⟩ := hymem
  have hr0 : 0 ≤ r := hrmem.1
  have hr1 : r ≤ 1 := hrmem.2
  by_cases hr : r = 0
  · have hw : w = 0 := by
      rw [← hy]
      apply Subtype.ext
      change polC (θ₀, r) = ((0 : Disc) : ℂ)
      rw [polC_apply, hr, clamp01_of_mem (le_refl (0 : ℝ)) (by norm_num)]
      simp
    refine ⟨0, ?_⟩
    rw [hw]
    exact twist_zero χ Φ hΦ
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    obtain ⟨η, hη⟩ := psi_surjective χ hcont hshift r θ₀
    have hη' : psi χ r η = θ₀ := hη
    obtain ⟨θ, hθmem, hθeq⟩ :=
      exists_angle_mem_Icc (Complex.exp ((η : ℂ) * Complex.I))
        (Complex.norm_exp_ofReal_mul_I η)
    obtain ⟨k, hk⟩ := expeq_iff_real hθeq
    have hpsi : psi χ r θ = psi χ r η + k * (2 * Real.pi) := by
      rw [hk, psi_shift_int χ hshift r k η]
    have hexp : Complex.exp (((psi χ r θ : ℝ) : ℂ) * Complex.I)
        = Complex.exp ((θ₀ : ℂ) * Complex.I) := by
      rw [hpsi, exp_add_int_two_pi, hη']
    refine ⟨polMap ⟨(θ, r), ⟨hθmem, ⟨hr0, hr1⟩⟩⟩, ?_⟩
    rw [hΦ]
    rw [← hy]
    apply Subtype.ext
    change twiC χ (θ, r) = polC (θ₀, r)
    rw [twiC_apply, polC_apply, clamp01_of_mem hr0 hr1, hexp]

theorem twist_circlePoint (χ : ℝ → ℝ)
    (_hshift : ∀ θ : ℝ, χ (θ + 2 * Real.pi) = χ θ + 2 * Real.pi) (Φ : Disc → Disc)
    (hΦ : ∀ p : polSet, Φ (polMap p) = twiMap χ p) :
    ∀ θ : ℝ, Φ (circlePoint θ) = circlePoint θ := by
  intro θ
  obtain ⟨θ₀, hθ₀mem, hθ₀eq⟩ :=
    exists_angle_mem_Icc (Complex.exp ((θ : ℂ) * Complex.I))
      (Complex.norm_exp_ofReal_mul_I θ)
  have hx : polMap ⟨(θ₀, 1), ⟨hθ₀mem, ⟨by norm_num, le_refl 1⟩⟩⟩ = circlePoint θ := by
    apply Subtype.ext
    change polC (θ₀, 1) = ((circlePoint θ : Disc) : ℂ)
    rw [polC_apply, clamp01_of_mem (by norm_num) (by norm_num), Complex.ofReal_one, one_mul,
      Work.Smooth.Jordan.circlePoint_coe, hθ₀eq]
  rw [← hx]
  rw [hΦ]
  rw [hx]
  apply Subtype.ext
  change twiC χ (θ₀, 1) = ((circlePoint θ : Disc) : ℂ)
  rw [twiC_apply, clamp01_of_mem (by norm_num) (by norm_num), Complex.ofReal_one, one_mul,
    psi_one, Work.Smooth.Jordan.circlePoint_coe, hθ₀eq]

theorem twist_halfCirclePoint (χ : ℝ → ℝ)
    (hshift : ∀ θ : ℝ, χ (θ + 2 * Real.pi) = χ θ + 2 * Real.pi) (Φ : Disc → Disc)
    (hΦ : ∀ p : polSet, Φ (polMap p) = twiMap χ p) :
    ∀ θ : ℝ, Φ (halfCirclePoint θ) = halfCirclePoint (χ θ) := by
  intro θ
  obtain ⟨θ₀, hθ₀mem, hθ₀eq⟩ :=
    exists_angle_mem_Icc (Complex.exp ((θ : ℂ) * Complex.I))
      (Complex.norm_exp_ofReal_mul_I θ)
  have hx : polMap ⟨(θ₀, 1 / 2), ⟨hθ₀mem, ⟨by norm_num, by norm_num⟩⟩⟩
      = halfCirclePoint θ := by
    apply Subtype.ext
    change polC (θ₀, 1 / 2) = ((halfCirclePoint θ : Disc) : ℂ)
    rw [polC_apply, clamp01_of_mem (by norm_num) (by norm_num), halfCirclePoint_coe,
      Work.Smooth.Jordan.circlePoint_coe, hθ₀eq]
    norm_num
  rw [← hx]
  rw [hΦ]
  apply Subtype.ext
  change twiC χ (θ₀, 1 / 2) = ((halfCirclePoint (χ θ) : Disc) : ℂ)
  rw [twiC_apply, clamp01_of_mem (by norm_num) (by norm_num), psi_half,
    halfCirclePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  obtain ⟨k, hk⟩ := expeq_iff_real hθ₀eq
  have hχ : χ θ₀ = χ θ + k * (2 * Real.pi) := by
    rw [hk, chi_shift_int χ hshift k θ]
  have hexp : Complex.exp ((χ θ₀ : ℂ) * Complex.I) = Complex.exp ((χ θ : ℂ) * Complex.I) := by
    rw [hχ, exp_add_int_two_pi]
  rw [hexp]
  norm_num

theorem twist_norm (χ : ℝ → ℝ) (Φ : Disc → Disc)
    (hΦ : ∀ p : polSet, Φ (polMap p) = twiMap χ p) :
    ∀ z : Disc, ‖((Φ z : Disc) : ℂ)‖ = ‖((z : Disc) : ℂ)‖ := by
  intro z
  obtain ⟨x, hx⟩ := polMap_surjective z
  rw [← hx, hΦ x]
  change ‖((twiDisc χ x.1 : Disc) : ℂ)‖ = ‖((polDisc x.1 : Disc) : ℂ)‖
  rw [norm_coe_twiDisc, norm_coe_polDisc]

/-! ## The main statement -/

theorem annulusInterpolation (χ : ℝ → ℝ) (hcont : Continuous χ) (hmono : StrictMono χ)
    (hshift : ∀ θ : ℝ, χ (θ + 2 * Real.pi) = χ θ + 2 * Real.pi) :
    ∃ Φ : Work.Smooth.SphereJordan.Disc ≃ₜ Work.Smooth.SphereJordan.Disc,
      (∀ θ : ℝ, Φ (Work.Smooth.SphereJordan.circlePoint θ)
        = Work.Smooth.SphereJordan.circlePoint θ) ∧
      (∀ θ : ℝ, Φ (Work.Smooth.SphereJordan.halfCirclePoint θ)
        = Work.Smooth.SphereJordan.halfCirclePoint (χ θ)) ∧
      (∀ z : Work.Smooth.SphereJordan.Disc,
        ‖((Φ z : Work.Smooth.SphereJordan.Disc) : ℂ)‖
          = ‖((z : Work.Smooth.SphereJordan.Disc) : ℂ)‖) := by
  obtain ⟨Φ, hΦcont, hΦ⟩ := exists_continuous_twist χ hcont hshift
  have hinj : Function.Injective Φ := twist_injective χ hmono hshift Φ hΦ
  have hsurj : Function.Surjective Φ := twist_surjective χ hcont hshift Φ hΦ
  have hfix := twist_circlePoint χ hshift Φ hΦ
  have hhalf := twist_halfCirclePoint χ hshift Φ hΦ
  have hnorm := twist_norm χ Φ hΦ
  let e : Disc ≃ Disc := Equiv.ofBijective Φ ⟨hinj, hsurj⟩
  have hec : Continuous (⇑e) := by
    change Continuous Φ
    exact hΦcont
  refine ⟨Continuous.homeoOfEquivCompactToT2 (f := e) hec, ?_, ?_, ?_⟩
  · intro θ; exact hfix θ
  · intro θ; exact hhalf θ
  · intro z; exact hnorm z

end

end Work.Smooth.SphereJordan
