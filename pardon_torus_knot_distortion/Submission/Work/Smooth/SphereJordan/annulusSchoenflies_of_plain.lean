import Mathlib
import Submission.Work.Smooth.SphereJordan.Pasting
import Submission.Work.Smooth.SphereJordan.Defs
import Submission.Work.Smooth.SphereJordan.lift_shift_eq_pm_one
import Submission.Work.Smooth.SphereJordan.annulusInterpolation
import Mathlib.Topology.Order.IntermediateValue

/-!
# From the plain annulus form of Schoenflies to the parametrised form

The **annulus form of the Schoenflies theorem** (`AnnulusSchoenflies`, `Pasting.lean`) asks that an
embedded disc `h : 𝔻 ↪ 𝔻`, whose boundary circle lies in the *open* disc, be straightened by a
homeomorphism `Θ` of the closed disc which fixes the boundary circle pointwise and which carries the
boundary circle of `h` onto the concentric circle of radius `1/2` **in the prescribed
parametrisation**, up to one of the two orientation signs `s = ±1`.

This file derives it from the *plain* (set-theoretic) form `PlainAnnulusSchoenflies`, which contains
no clause about the parametrisation of the inner boundary circle.  Given a homeomorphism `Θ₀` with
the plain properties, the map

  `θ ↦ Θ₀ (h (e^{iθ}))`

is a homeomorphism of the circle `∂𝔻` onto the circle of radius `1/2`; write it as
`halfCirclePoint ∘ Ψ`.  The orientation of `Ψ` is the orientation of the embedding `h` and cannot be
prescribed.  We lift `Ψ` to a continuous `Ψ̃ : ℝ → ℝ` along the covering map `Circle.exp : ℝ → Circle`
of the circle (Mathlib's `IsCoveringMap.existsUnique_continuousMap_lifts`, the domain `ℝ` being
simply connected), and determine its shift: `Ψ̃ (θ + 2π) = Ψ̃ θ + 2π d` for a constant `d : ℤ`, and
`d = ±1`.  Setting `s := d`, the map `χ θ := Ψ̃ (s * θ)` is a strictly increasing homeomorphism of
`ℝ` commuting with the shift by `2π`, so the circle map which it induces on the circle of radius
`1/2` (an orientation-preserving homeomorphism of that circle) extends to a homeomorphism of the
annulus `{1/2 ≤ ‖z‖ ≤ 1}` fixing the outer boundary pointwise — this is the elementary annular
interpolation `annulusInterpolation`.  Composing the inverse of that interpolated homeomorphism with
`Θ₀` gives a homeomorphism of `𝔻` with all the required properties.

Nothing outside `Submission/Work/Smooth/SphereJordan/` is modified.
-/

open Set

namespace Work.Smooth.SphereJordan

noncomputable section

/-! ## The parametrisation of the boundary circle -/

/-- Two parameters giving the same point of the boundary circle differ by an integer multiple of
`2π`. -/
theorem circlePoint_sub_mem_zmultiples {x y : ℝ} (h : circlePoint x = circlePoint y) :
    ∃ k : ℤ, x - y = (k : ℝ) * (2 * Real.pi) := by
  have h1 : Complex.exp ((x : ℂ) * Complex.I) = Complex.exp ((y : ℂ) * Complex.I) := by
    have := congrArg (fun z : Disc => (z : ℂ)) h
    rwa [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe] at this
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp h1
  have h2 : x = y + (n : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  exact ⟨n, by rw [h2]; ring⟩

/-- Shifting the parameter of the boundary circle by an integer multiple of `2π` does not change
the point. -/
theorem circlePoint_add_int_mul (θ : ℝ) (k : ℤ) :
    circlePoint (θ + (k : ℝ) * (2 * Real.pi)) = circlePoint θ := by
  apply Subtype.ext
  rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
  have hI : ((θ + (k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I
      = (θ : ℂ) * Complex.I + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [hI, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The parametrisation of the boundary circle is `2π`-periodic. -/
theorem circlePoint_add_two_pi (θ : ℝ) : circlePoint (θ + 2 * Real.pi) = circlePoint θ := by
  simpa using circlePoint_add_int_mul θ 1

/-- The boundary point `e^{iθ}` has norm one. -/
theorem norm_circlePoint_plain (θ : ℝ) : ‖((circlePoint θ : Disc) : ℂ)‖ = 1 := by
  rw [Work.Smooth.Jordan.circlePoint_coe, Complex.norm_exp_ofReal_mul_I]

/-- The parametrisation of the boundary circle is continuous. -/
theorem continuous_circlePoint : Continuous (circlePoint : ℝ → Disc) :=
  Continuous.subtype_mk (by fun_prop : Continuous fun θ : ℝ => Complex.exp (θ * Complex.I))
    (fun θ => by rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp_ofReal_mul_I])

/-! ## Monotonicity and shifts of a lift -/

/-- The integer-multiple form of the shift: if `Ψ (θ + 2π) = Ψ θ + c · 2π` for all `θ`, then
`Ψ (θ + k · 2π) = Ψ θ + k · c · 2π` for every integer `k`. -/
theorem shift_int (Ψ : ℝ → ℝ) (c : ℝ)
    (h : ∀ θ : ℝ, Ψ (θ + 2 * Real.pi) = Ψ θ + c * (2 * Real.pi)) :
    ∀ (θ : ℝ) (k : ℤ), Ψ (θ + (k : ℝ) * (2 * Real.pi)) = Ψ θ + (k : ℝ) * c * (2 * Real.pi) := by
  have hnat : ∀ (θ : ℝ) (n : ℕ),
      Ψ (θ + (n : ℝ) * (2 * Real.pi)) = Ψ θ + (n : ℝ) * c * (2 * Real.pi) := by
    intro θ n
    induction n with
    | zero => simp
    | succ n ih =>
        have h1 : θ + ((n : ℕ) + 1 : ℕ) * (2 * Real.pi)
            = (θ + (n : ℝ) * (2 * Real.pi)) + 2 * Real.pi := by push_cast; ring
        rw [h1, h, ih]; push_cast; ring
  have hneg : ∀ (θ : ℝ) (n : ℕ),
      Ψ (θ - (n : ℝ) * (2 * Real.pi)) = Ψ θ - (n : ℝ) * c * (2 * Real.pi) := by
    intro θ n
    induction n with
    | zero => simp
    | succ n ih =>
        have h1 : θ - ((n : ℕ) + 1 : ℕ) * (2 * Real.pi)
            = (θ - (n : ℝ) * (2 * Real.pi)) - 2 * Real.pi := by push_cast; ring
        have h2 : Ψ ((θ - (n : ℝ) * (2 * Real.pi)) - 2 * Real.pi)
            = Ψ (θ - (n : ℝ) * (2 * Real.pi)) - c * (2 * Real.pi) := by
          have h3 := h ((θ - (n : ℝ) * (2 * Real.pi)) - 2 * Real.pi)
          have h4 : (θ - (n : ℝ) * (2 * Real.pi) - 2 * Real.pi) + 2 * Real.pi
              = θ - (n : ℝ) * (2 * Real.pi) := by ring
          rw [h4] at h3
          linarith
        rw [h1, h2, ih]; push_cast; ring
  intro θ k
  rcases k with n | n
  · simpa using hnat θ n
  · have hk : ((Int.negSucc n : ℤ) : ℝ) = -((n : ℝ) + 1) := by
      rw [Int.negSucc_eq]; push_cast; ring
    rw [hk]
    have h1 : θ + (-((n : ℝ) + 1)) * (2 * Real.pi)
        = θ - ((n + 1 : ℕ) : ℝ) * (2 * Real.pi) := by push_cast; ring
    rw [h1, hneg θ (n + 1)]
    push_cast; ring

/-- A continuous injective `Ψ : ℝ → ℝ` which advances by `2π` over each period `2π` is strictly
increasing.  (For `0 < t ≤ 2π` the function `s ↦ Ψ (z + s)` starts at `Ψ z` and ends at `Ψ z + 2π`;
were `Ψ (z + t) ≤ Ψ z`, then — by the intermediate value theorem in the strict case, and immediately
in the equality case — two different parameters would have the same image.) -/
theorem strictMono_of_shift (Ψ : ℝ → ℝ) (hc : Continuous Ψ) (hinj : Function.Injective Ψ)
    (hshift : ∀ θ : ℝ, Ψ (θ + 2 * Real.pi) = Ψ θ + 2 * Real.pi) : StrictMono Ψ := by
  have key : ∀ z t : ℝ, 0 < t → t ≤ 2 * Real.pi → Ψ z < Ψ (z + t) := by
    intro z t ht0 ht2
    by_contra hcon
    rw [not_lt] at hcon
    have hcont' : Continuous fun s : ℝ => Ψ (z + s) :=
      hc.comp (continuous_const.add continuous_id)
    have hz2 : Ψ (z + 2 * Real.pi) = Ψ z + 2 * Real.pi := hshift z
    rcases lt_or_eq_of_le hcon with hlt | heq
    · have hsub := intermediate_value_Ioo ht2 hcont'.continuousOn
      obtain ⟨s, hs, hsv⟩ := hsub (show Ψ z ∈ Set.Ioo (Ψ (z + t)) (Ψ (z + 2 * Real.pi)) from
        ⟨hlt, by rw [hz2]; linarith⟩)
      have : z + s = z := hinj hsv
      linarith [hs.1]
    · have : z + t = z := hinj heq
      linarith
  intro x y hxy
  have hpos : 0 < (y - x) / (2 * Real.pi) := by positivity
  obtain ⟨n, hn⟩ := exists_nat_gt ((y - x) / (2 * Real.pi))
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
    linarith
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
  set t : ℝ := (y - x) / n with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht2 : t ≤ 2 * Real.pi := by
    rw [ht, div_le_iff₀ hnpos]
    have hlt : y - x < (n : ℝ) * (2 * Real.pi) := by
      have h1 := mul_lt_mul_of_pos_right hn (by positivity : (0 : ℝ) < 2 * Real.pi)
      rwa [div_mul_cancel₀ (y - x) (by positivity : (2 * Real.pi : ℝ) ≠ 0)] at h1
    linarith
  have hstep : ∀ k : ℕ, Ψ (x + (k : ℝ) * t) < Ψ (x + ((k : ℕ) + 1 : ℕ) * t) := by
    intro k
    have hk := key (x + (k : ℝ) * t) t ht0 ht2
    have heq : x + (k : ℝ) * t + t = x + (((k : ℕ) + 1 : ℕ) : ℝ) * t := by push_cast; ring
    rwa [heq] at hk
  have hchain : ∀ k : ℕ, k ≤ n → Ψ x ≤ Ψ (x + (k : ℝ) * t) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hk' : k ≤ n := le_trans (Nat.le_succ k) hk
        have h1 := ih hk'
        have h2 := hstep k
        linarith
  have hfin := hchain n le_rfl
  have hne : Ψ (x + (n : ℝ) * t) ≠ Ψ x := by
    intro hcon
    have h1 : x + (n : ℝ) * t = x := hinj hcon
    have h2 : (n : ℝ) * t = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact hn0 (by exact_mod_cast h)
    · exact absurd h (ne_of_gt ht0)
  have hnt : (n : ℝ) * t = y - x := by
    rw [ht]
    exact mul_div_cancel₀ (y - x) (ne_of_gt hnpos)
  have hxy' : x + (n : ℝ) * t = y := by rw [hnt]; ring
  rw [hxy'] at hfin hne
  exact lt_of_le_of_ne hfin (Ne.symm hne)

/-- A continuous injective `Ψ : ℝ → ℝ` which advances by `-2π` over each period `2π` is strictly
decreasing. -/
theorem strictAnti_of_shift (Ψ : ℝ → ℝ) (hc : Continuous Ψ) (hinj : Function.Injective Ψ)
    (hshift : ∀ θ : ℝ, Ψ (θ + 2 * Real.pi) = Ψ θ - 2 * Real.pi) : StrictAnti Ψ := by
  have hshift' : ∀ θ : ℝ, (fun θ => -Ψ θ) (θ + 2 * Real.pi) = (fun θ => -Ψ θ) θ + 2 * Real.pi := by
    intro θ
    have := hshift θ
    simp only
    linarith
  have hinj' : Function.Injective fun θ : ℝ => -Ψ θ := by
    intro a b h
    exact hinj (neg_injective h)
  have hmono : StrictMono fun θ : ℝ => -Ψ θ :=
    strictMono_of_shift (fun θ => -Ψ θ) hc.neg hinj' hshift'
  intro x y hxy
  have := hmono hxy
  simp only at this
  linarith

/-! ## The main theorem -/

theorem annulusSchoenflies_of_plain (h : Work.Smooth.SphereJordan.PlainAnnulusSchoenflies) :
    Work.Smooth.SphereJordan.AnnulusSchoenflies := by
  intro h₀ hinj hbd
  obtain ⟨Θ₀, hfix, hmem, hopen⟩ := h h₀ hinj hbd
  -- ## Step 1: the boundary circle of `h₀` is mapped onto the circle of radius `1/2`
  have hhalf : ∀ θ : ℝ, ‖((Θ₀ (h₀ (circlePoint θ)) : Disc) : ℂ)‖ = 1 / 2 := by
    intro θ
    refine le_antisymm ((hmem (h₀ (circlePoint θ))).mp ⟨circlePoint θ, rfl⟩) ?_
    have hnot : ¬ ‖((circlePoint θ : Disc) : ℂ)‖ < 1 := by
      rw [norm_circlePoint_plain]; norm_num
    by_contra hlt
    have hlt' : ‖((Θ₀ (h₀ (circlePoint θ)) : Disc) : ℂ)‖ < 1 / 2 := not_le.mp hlt
    exact hnot ((hopen (circlePoint θ)).mpr hlt')
  -- ## Step 2: the boundary circle as a loop in the unit circle
  have hnorm2 : ∀ θ : ℝ, ‖(2 : ℂ) * ((Θ₀ (h₀ (circlePoint θ)) : Disc) : ℂ)‖ = 1 := by
    intro θ
    rw [norm_mul, hhalf θ]
    norm_num
  have hcont2 : Continuous fun θ : ℝ => (Θ₀ (h₀ (circlePoint θ)) : Disc) :=
    Θ₀.continuous.comp (h₀.continuous.comp continuous_circlePoint)
  let f : C(ℝ, Circle) :=
    ⟨fun θ => ⟨2 * ((Θ₀ (h₀ (circlePoint θ)) : Disc) : ℂ), by
      show 2 * ((Θ₀ (h₀ (circlePoint θ)) : Disc) : ℂ) ∈ Metric.sphere (0 : ℂ) 1
      rw [mem_sphere_zero_iff_norm]
      exact hnorm2 θ⟩,
      Continuous.subtype_mk (continuous_const.mul (continuous_subtype_val.comp hcont2)) (fun θ => by
        show 2 * ((Θ₀ (h₀ (circlePoint θ)) : Disc) : ℂ) ∈ Metric.sphere (0 : ℂ) 1
        rw [mem_sphere_zero_iff_norm]
        exact hnorm2 θ)⟩
  have hfapply : ∀ θ : ℝ,
      ((f θ : Circle) : ℂ) = 2 * ((Θ₀ (h₀ (circlePoint θ)) : Disc) : ℂ) := fun θ => rfl
  have hfper : ∀ θ : ℝ, f (θ + 2 * Real.pi) = f θ := by
    intro θ
    apply Subtype.ext
    rw [hfapply, hfapply, circlePoint_add_two_pi]
  -- ## Step 3: lift the loop to `ℝ` along the universal cover of the circle
  obtain ⟨Ψ, ⟨hΨ0, hΨlift⟩, -⟩ :=
    Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts f 0
      (Complex.arg (((f 0 : Circle)) : ℂ)) (Circle.exp_arg (f 0))
  have hlift : ∀ θ : ℝ, Circle.exp (Ψ θ) = f θ := fun θ => congrFun hΨlift θ
  have hΨcont : Continuous Ψ := Ψ.continuous
  have hcirc : ∀ θ : ℝ,
      ((circlePoint (Ψ θ) : Disc) : ℂ) = 2 * ((Θ₀ (h₀ (circlePoint θ)) : Disc) : ℂ) := by
    intro θ
    have h1 := congrArg Subtype.val (hlift θ)
    simp only [Circle.coe_exp, hfapply] at h1
    rw [Work.Smooth.Jordan.circlePoint_coe]
    exact h1
  have hkey : ∀ θ : ℝ, Θ₀ (h₀ (circlePoint θ)) = halfCirclePoint (Ψ θ) := by
    intro θ
    apply Subtype.ext
    have h1 := hcirc θ
    rw [Work.Smooth.Jordan.circlePoint_coe] at h1
    rw [halfCirclePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
    linear_combination (-1 / 2) * h1
  -- ## Step 4: the shift of the lift
  have hstep : ∀ θ : ℝ, ∃ k : ℤ, Ψ (θ + 2 * Real.pi) - Ψ θ = (k : ℝ) * (2 * Real.pi) := by
    intro θ
    have h1 : Circle.exp (Ψ (θ + 2 * Real.pi)) = Circle.exp (Ψ θ) := by
      rw [hlift (θ + 2 * Real.pi), hlift θ, hfper θ]
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp h1
    exact ⟨k, by rw [hk]; ring⟩
  have hcontstep : Continuous fun θ : ℝ => Ψ (θ + 2 * Real.pi) - Ψ θ :=
    ((hΨcont.comp (continuous_id.add continuous_const)).sub hΨcont)
  obtain ⟨d, hd⟩ := Work.CoreTopology.LiftOf.continuous_int_multiple_const
    (fun θ : ℝ => Ψ (θ + 2 * Real.pi) - Ψ θ) hcontstep hstep
  have hd' : ∀ θ : ℝ, Ψ (θ + 2 * Real.pi) = Ψ θ + (d : ℝ) * (2 * Real.pi) := by
    intro θ
    have := hd θ
    linarith
  -- ## Step 5: the shift is `±1`
  have hmod : ∀ x y : ℝ, (∃ k : ℤ, Ψ x - Ψ y = (k : ℝ) * (2 * Real.pi)) →
      (∃ k : ℤ, x - y = (k : ℝ) * (2 * Real.pi)) := by
    intro x y ⟨k, hk⟩
    have hxy : circlePoint (Ψ x) = circlePoint (Ψ y) := by
      apply Subtype.ext
      rw [Work.Smooth.Jordan.circlePoint_coe, Work.Smooth.Jordan.circlePoint_coe]
      have h2 : (Ψ x : ℂ) = (Ψ y : ℂ) + (k : ℂ) * (2 * (Real.pi : ℂ)) := by
        have h0 : Ψ x = Ψ y + (k : ℝ) * (2 * Real.pi) := by linarith
        rw [h0]
        push_cast
        ring
      have h1 : (Ψ x : ℂ) * Complex.I
          = (Ψ y : ℂ) * Complex.I + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        rw [h2]; ring
      rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have h3 : ((circlePoint (Ψ x) : Disc) : ℂ) = ((circlePoint (Ψ y) : Disc) : ℂ) := by rw [hxy]
    rw [hcirc x, hcirc y] at h3
    have h4 : Θ₀ (h₀ (circlePoint x)) = Θ₀ (h₀ (circlePoint y)) := by
      apply Subtype.ext
      exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h3
    exact circlePoint_sub_mem_zmultiples (hinj (Θ₀.injective h4))
  have hdpm : d = 1 ∨ d = -1 := lift_shift_eq_pm_one Ψ hΨcont d hd' hmod
  have hdne : d ≠ 0 := by
    rcases hdpm with hd1 | hd1 <;> rw [hd1] <;> norm_num
  -- ## Step 6: injectivity and monotonicity of `Ψ`
  have hshiftInt : ∀ (θ : ℝ) (k : ℤ),
      Ψ (θ + (k : ℝ) * (2 * Real.pi)) = Ψ θ + (k : ℝ) * (d : ℝ) * (2 * Real.pi) :=
    shift_int Ψ (d : ℝ) hd'
  have hinjΨ : Function.Injective Ψ := by
    intro x y hxy
    obtain ⟨k, hk⟩ := hmod x y ⟨0, by rw [hxy]; ring⟩
    have hx : x = y + (k : ℝ) * (2 * Real.pi) := by linarith
    have h4 : (k : ℝ) * (d : ℝ) * (2 * Real.pi) = 0 := by
      have h5 : Ψ y + (k : ℝ) * (d : ℝ) * (2 * Real.pi) = Ψ y := by
        rw [← hshiftInt y k, ← hx]; exact hxy
      linarith
    have h5 : (k : ℝ) * (d : ℝ) = 0 := by
      rcases mul_eq_zero.mp h4 with h | h
      · exact h
      · exact absurd h (by positivity)
    rcases mul_eq_zero.mp h5 with h | h
    · have hk0 : k = 0 := by exact_mod_cast h
      rw [hk0] at hk
      push_cast at hk
      linarith
    · exact absurd (by exact_mod_cast h : d = 0) hdne
  have hmono1 : d = 1 → StrictMono Ψ := fun hd1 => strictMono_of_shift Ψ hΨcont hinjΨ (fun θ => by
    have h := hd' θ
    rw [hd1] at h
    push_cast at h
    linarith)
  have hmono2 : d = -1 → StrictAnti Ψ := fun hd1 => strictAnti_of_shift Ψ hΨcont hinjΨ (fun θ => by
    have h := hd' θ
    rw [hd1] at h
    push_cast at h
    linarith)
  -- ## Step 7: the reparametrisation `χ θ = Ψ (s * θ)` and the interpolated homeomorphism
  set s : ℝ := (d : ℝ) with hs
  have hs1 : s = 1 ∨ s = -1 := by
    rcases hdpm with hd1 | hd1
    · left; rw [hs, hd1]; norm_num
    · right; rw [hs, hd1]; norm_num
  have hss : s * s = 1 := by
    rcases hs1 with h | h <;> rw [h] <;> norm_num
  have hχcont : Continuous fun θ : ℝ => Ψ (s * θ) :=
    hΨcont.comp (continuous_const.mul continuous_id)
  have hχmono : StrictMono fun θ : ℝ => Ψ (s * θ) := by
    intro a b hab
    rcases hdpm with hd1 | hd1
    · have hs1' : s = 1 := by rw [hs, hd1]; norm_num
      have := hmono1 hd1
      show Ψ (s * a) < Ψ (s * b)
      rw [hs1']
      simpa using this hab
    · have hs1' : s = -1 := by rw [hs, hd1]; norm_num
      have := hmono2 hd1
      show Ψ (s * a) < Ψ (s * b)
      rw [hs1']
      exact this (by linarith)
  have hχshift : ∀ θ : ℝ, (fun θ => Ψ (s * θ)) (θ + 2 * Real.pi)
      = (fun θ => Ψ (s * θ)) θ + 2 * Real.pi := by
    intro θ
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, s * (2 * Real.pi) = (k : ℝ) * (2 * Real.pi) ∧ (k : ℝ) = s := by
      rcases hs1 with h | h
      · exact ⟨1, by rw [h]; ring, by rw [h]; norm_num⟩
      · exact ⟨-1, by rw [h]; ring, by rw [h]; norm_num⟩
    calc Ψ (s * (θ + 2 * Real.pi))
        = Ψ (s * θ + s * (2 * Real.pi)) := by rw [mul_add]
      _ = Ψ (s * θ + (k : ℝ) * (2 * Real.pi)) := by rw [hk1]
      _ = Ψ (s * θ) + (k : ℝ) * (d : ℝ) * (2 * Real.pi) := hshiftInt (s * θ) k
      _ = Ψ (s * θ) + 2 * Real.pi := by
            rw [hk2]
            have h1 : s * (d : ℝ) = 1 := by rw [← hs]; exact hss
            rw [h1]; ring
  obtain ⟨Φχ, hΦfix, hΦhalf, hΦnorm⟩ :=
    annulusInterpolation (fun θ => Ψ (s * θ)) hχcont hχmono hχshift
  have hΦnorm' : ∀ z : Disc, ‖((Φχ.symm z : Disc) : ℂ)‖ = ‖((z : Disc) : ℂ)‖ := by
    intro z
    have h1 := hΦnorm (Φχ.symm z)
    rw [Homeomorph.apply_symm_apply] at h1
    exact h1.symm
  have hΦfix' : ∀ θ : ℝ, Φχ.symm (circlePoint θ) = circlePoint θ := by
    intro θ
    nth_rewrite 1 [← hΦfix θ]
    rw [Homeomorph.symm_apply_apply]
  -- ## Step 8: assembly
  refine ⟨Θ₀.trans Φχ.symm, s, hs1, ?_, ?_, ?_, ?_⟩
  · intro θ
    show Φχ.symm (Θ₀ (circlePoint θ)) = circlePoint θ
    rw [hfix θ]
    exact hΦfix' θ
  · intro θ
    show Φχ.symm (Θ₀ (h₀ (circlePoint (s * θ)))) = halfCirclePoint θ
    rw [hkey (s * θ), ← hΦhalf θ, Homeomorph.symm_apply_apply]
  · intro x
    show (∃ z : Disc, h₀ z = x) ↔ ‖((Φχ.symm (Θ₀ x) : Disc) : ℂ)‖ ≤ 1 / 2
    rw [hΦnorm' (Θ₀ x)]
    exact hmem x
  · intro z
    show ‖((z : Disc) : ℂ)‖ < 1 ↔ ‖((Φχ.symm (Θ₀ (h₀ z)) : Disc) : ℂ)‖ < 1 / 2
    rw [hΦnorm' (Θ₀ (h₀ z))]
    exact hopen z

end

end Work.Smooth.SphereJordan
