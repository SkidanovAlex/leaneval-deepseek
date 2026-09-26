import Submission.Work.Smooth.JordanSeparation.BumpCylinder
import Submission.Work.Smooth.JordanSeparation.ChordWindow
import Submission.Work.Smooth.JordanSeparation.BumpStep

/-!
# The sharp legality criterion for a "cap cut" of a plane curve

`SCHOENFLIES.md` §6.3 asks, for the exhaustion proof of (E), for the *per-step legality* of a
**cap cut**: push the part of a closed curve `γ` that lies above a level `t` in a direction `ν`
down to that level, i.e. replace `γ` by

`capCutCurve γ ν t θ = γ θ - capProfile γ ν t θ • ν`,   `capProfile γ ν t θ = max 0 (⟪γ θ, ν⟫ - t)`.

The existing machinery (`BumpCylinder.lean`, `ChordWindow.lean`) proves *sufficient* conditions for
the push `(θ,s) ↦ γ θ - (s · capProfile γ ν t θ) • ν` to be injective
(`bumpCylinder_of_chord` under a chord condition, `bumpCylinder_of_window` under a
`C¹`-smoothness + window condition).  The purpose of this file is the **exact** criterion, which is
both simpler and sharper (and needs *no* smoothness — the curves produced by cuts have corners):

> the push is injective (modulo the period) **if and only if** no `ν`-parallel chord of `γ` is
> swallowed by the cap `{⟪·, ν⟫ ≥ t}`,
> i.e. **if and only if** every chord `γ θ - γ θ'` parallel to `ν` meets the open half-plane
> `{⟪·, ν⟫ < t}`.

In min-form: every `ν`-parallel chord satisfies `min (⟪γ θ, ν⟫) (⟪γ θ', ν⟫) < t`.

This is the exact condition used by any cutting-based exhaustion of the inside of `γ`
(Bing's exhaustion, `SCHOENFLIES.md` §6): a cap may be flattened to the level `t` exactly when no
parallel chord of the curve is swallowed whole by the cap.

## Main declarations

* `dotV z ν` — the `ν`-component `re (conj z * ν)` of a vector (the scalar product with `ν` when
  `‖ν‖ = 1`);
* `capProfile γ ν t`, `capCutCurve γ ν t`, `capPush γ ν t` — the profile, the cut curve and the
  push cylinder;
* `capPush_injective_iff` — **the criterion** (min-form);
* `capPush_injective_iff'` — the same in the geometric "no chord swallowed by the cap" form;
* `not_injective_of_swallowed_iff` — the constructive half: a swallowed chord yields an explicit
  collision;
* `capCutCurve_dotV` — after the cut, the `ν`-level of a point of the curve is `min ⟪γ θ,ν⟫ t`
  (the curve is *flattened* above the level `t`);
* `capCutCurve_isSimple` — for a simple closed `C⁰` curve, a legal cut produces a simple closed
  curve (`Set.InjOn` on a period), with the period bookkeeping the chain needs.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-! ## The `ν`-component of a vector -/

/-- The **`ν`-component** of `z : ℂ ≅ ℝ²`: `dotV z ν = re (conj z * ν)`.  For `‖ν‖ = 1` this is the
(real) scalar product `⟪z, ν⟫`. -/
def dotV (z ν : ℂ) : ℝ := ((starRingEnd ℂ) z * ν).re

theorem dotV_def (z ν : ℂ) : dotV z ν = ((starRingEnd ℂ) z * ν).re := rfl

/-- The `ν`-component in real coordinates. -/
theorem dotV_eq (z ν : ℂ) : dotV z ν = z.re * ν.re + z.im * ν.im := by
  rw [dotV, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem dotV_add (a b ν : ℂ) : dotV (a + b) ν = dotV a ν + dotV b ν := by
  rw [dotV_eq, dotV_eq, dotV_eq, Complex.add_re, Complex.add_im]; ring

theorem dotV_sub (a b ν : ℂ) : dotV (a - b) ν = dotV a ν - dotV b ν := by
  rw [dotV_eq, dotV_eq, dotV_eq, Complex.sub_re, Complex.sub_im]; ring

theorem dotV_smul (r : ℝ) (z ν : ℂ) : dotV ((r : ℂ) * z) ν = r * dotV z ν := by
  rw [dotV_eq, dotV_eq, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem dotV_neg (z ν : ℂ) : dotV (-z) ν = -dotV z ν := by
  rw [dotV_eq, dotV_eq, Complex.neg_re, Complex.neg_im]; ring

theorem dotV_neg_right (z ν : ℂ) : dotV z (-ν) = -dotV z ν := by
  rw [dotV_eq, dotV_eq, Complex.neg_re, Complex.neg_im]; ring

@[simp] theorem dotV_zero (ν : ℂ) : dotV 0 ν = 0 := by simp [dotV]

theorem dotV_self (ν : ℂ) : dotV ν ν = ν.re * ν.re + ν.im * ν.im := by
  rw [dotV_eq]

theorem dotV_self_eq_one {ν : ℂ} (hν : ‖ν‖ = 1) : dotV ν ν = 1 := by
  have h := Complex.sq_norm ν
  rw [hν] at h
  norm_num at h
  rw [Complex.normSq_apply] at h
  rw [dotV_self]
  linarith

/-- A vector whose determinant with `ν ≠ 0` vanishes is a real multiple of `ν`. -/
theorem exists_smul_of_detV_eq_zero {u ν : ℂ} (hν : ν ≠ 0) (h : detV u ν = 0) :
    ∃ c : ℝ, u = ((c : ℝ) : ℂ) * ν := by
  rcases (detV_eq_zero_iff u ν).mp h with ⟨r, hr | hr⟩
  · have hr0 : r ≠ 0 := fun h0 => hν (by rw [hr, h0, Complex.ofReal_zero, zero_mul])
    refine ⟨1 / r, ?_⟩
    have h1 : (((r:ℝ)⁻¹ : ℝ) : ℂ) * ((r:ℂ)) = 1 := by
      rw [← Complex.ofReal_mul, inv_mul_cancel₀ hr0, Complex.ofReal_one]
    calc u = (((r:ℝ)⁻¹ : ℝ) : ℂ) * ((r:ℂ)) * u := by rw [h1, one_mul]
      _ = (((r:ℝ)⁻¹ : ℝ) : ℂ) * ν := by rw [mul_assoc, hr]
      _ = ((1 / r : ℝ) : ℂ) * ν := by rw [one_div]
  · exact ⟨r, hr⟩

/-! ## The cap profile, the cut curve and the push -/

/-- The **cap profile** of `γ` in direction `ν` at level `t`: `max 0 (⟪γ θ, ν⟫ - t)`. -/
def capProfile (γ : ℝ → ℂ) (ν : ℂ) (t : ℝ) : ℝ → ℝ :=
  fun θ => if t < dotV (γ θ) ν then dotV (γ θ) ν - t else 0

theorem capProfile_apply (γ : ℝ → ℂ) (ν : ℂ) (t θ : ℝ) :
    capProfile γ ν t θ = if t < dotV (γ θ) ν then dotV (γ θ) ν - t else 0 := rfl

theorem capProfile_nonneg (γ : ℝ → ℂ) (ν : ℂ) (t θ : ℝ) : 0 ≤ capProfile γ ν t θ := by
  rw [capProfile_apply]; split_ifs <;> linarith

theorem capProfile_eq_zero_iff {γ : ℝ → ℂ} {ν : ℂ} {t θ : ℝ} :
    capProfile γ ν t θ = 0 ↔ dotV (γ θ) ν ≤ t := by
  rw [capProfile_apply]
  by_cases h : t < dotV (γ θ) ν
  · rw [if_pos h]
    exact ⟨fun h0 => absurd (le_of_eq (sub_eq_zero.mp h0)) (not_le_of_gt h),
      fun h0 => absurd h (not_lt.mpr h0)⟩
  · rw [if_neg h]
    exact ⟨fun _ => not_lt.mp h, fun _ => rfl⟩

theorem capProfile_pos_iff {γ : ℝ → ℂ} {ν : ℂ} {t θ : ℝ} :
    0 < capProfile γ ν t θ ↔ t < dotV (γ θ) ν := by
  rw [capProfile_apply]
  constructor
  · intro h
    by_contra hlt
    rw [if_neg hlt] at h
    exact lt_irrefl _ h
  · intro h
    rw [if_pos h]; linarith

theorem capProfile_eq_of_lt {γ : ℝ → ℂ} {ν : ℂ} {t θ : ℝ} (h : t < dotV (γ θ) ν) :
    capProfile γ ν t θ = dotV (γ θ) ν - t := by
  rw [capProfile_apply, if_pos h]

theorem capProfile_eq_zero_of_le {γ : ℝ → ℂ} {ν : ℂ} {t θ : ℝ} (h : dotV (γ θ) ν ≤ t) :
    capProfile γ ν t θ = 0 :=
  capProfile_eq_zero_iff.mpr h

/-- The profile is the `max`-form of the definition. -/
theorem capProfile_eq_max (γ : ℝ → ℂ) (ν : ℂ) (t θ : ℝ) :
    capProfile γ ν t θ = max 0 (dotV (γ θ) ν - t) := by
  rw [capProfile_apply]
  rcases le_or_gt (dotV (γ θ) ν) t with h | h
  · rw [if_neg (not_lt.mpr h), max_eq_left (by linarith)]
  · rw [if_pos h, max_eq_right (le_of_lt (by linarith : (0:ℝ) < dotV (γ θ) ν - t))]

theorem capProfile_fun_eq (γ : ℝ → ℂ) (ν : ℂ) (t : ℝ) :
    capProfile γ ν t = fun θ => max 0 (dotV (γ θ) ν - t) :=
  funext (capProfile_eq_max γ ν t)

theorem capProfile_periodic {γ : ℝ → ℂ} {ν : ℂ} {t : ℝ}
    (hγ : Function.Periodic γ (2 * Real.pi)) :
    Function.Periodic (capProfile γ ν t) (2 * Real.pi) := by
  intro θ
  rw [capProfile_apply, capProfile_apply, hγ θ]

theorem continuous_dotV_right (ν : ℂ) : Continuous (fun z : ℂ => dotV z ν) := by
  rw [show (fun z : ℂ => dotV z ν) = fun z => z.re * ν.re + z.im * ν.im from by
    funext z; rw [dotV_eq]]
  exact (Complex.continuous_re.mul continuous_const).add
    (Complex.continuous_im.mul continuous_const)

theorem continuous_capProfile {γ : ℝ → ℂ} {ν : ℂ} {t : ℝ} (hγ : Continuous γ) :
    Continuous (capProfile γ ν t) := by
  have h : Continuous fun θ : ℝ => dotV (γ θ) ν := (continuous_dotV_right ν).comp hγ
  have hmax : Continuous fun θ : ℝ => max (0:ℝ) (dotV (γ θ) ν - t) :=
    (continuous_const : Continuous fun _ : ℝ => (0:ℝ)).max (h.sub continuous_const)
  rw [capProfile_fun_eq]
  exact hmax

/-- The **cut curve**: `γ` with the part above level `t` pushed down to the level `t` in the
direction `-ν`. -/
def capCutCurve (γ : ℝ → ℂ) (ν : ℂ) (t : ℝ) : ℝ → ℂ :=
  fun θ => γ θ - ((capProfile γ ν t θ : ℝ) : ℂ) * ν

theorem capCutCurve_apply (γ : ℝ → ℂ) (ν : ℂ) (t θ : ℝ) :
    capCutCurve γ ν t θ = γ θ - ((capProfile γ ν t θ : ℝ) : ℂ) * ν := rfl

theorem capCutCurve_fun_eq (γ : ℝ → ℂ) (ν : ℂ) (t : ℝ) :
    capCutCurve γ ν t = fun θ => γ θ - ((capProfile γ ν t θ : ℝ) : ℂ) * ν :=
  funext (capCutCurve_apply γ ν t)

/-- The **push cylinder** of a cap cut: `(θ,s) ↦ γ θ - (s · capProfile γ ν t θ) • ν`. -/
def capPush (γ : ℝ → ℂ) (ν : ℂ) (t : ℝ) : ℝ × ℝ → ℂ :=
  fun p => γ p.1 - ((p.2 * capProfile γ ν t p.1 : ℝ) : ℂ) * ν

theorem capPush_apply (γ : ℝ → ℂ) (ν : ℂ) (t : ℝ) (p : ℝ × ℝ) :
    capPush γ ν t p = γ p.1 - ((p.2 * capProfile γ ν t p.1 : ℝ) : ℂ) * ν := rfl

theorem capPush_fun_eq (γ : ℝ → ℂ) (ν : ℂ) (t : ℝ) :
    capPush γ ν t = fun p : ℝ × ℝ => γ p.1 - ((p.2 * capProfile γ ν t p.1 : ℝ) : ℂ) * ν :=
  funext (capPush_apply γ ν t)

theorem capPush_one (γ : ℝ → ℂ) (ν : ℂ) (t θ : ℝ) : capPush γ ν t (θ, 1) = capCutCurve γ ν t θ := by
  rw [capPush_apply, capCutCurve_apply, one_mul]

theorem capPush_zero (γ : ℝ → ℂ) (ν : ℂ) (t θ : ℝ) : capPush γ ν t (θ, 0) = γ θ := by
  rw [capPush_apply, zero_mul, Complex.ofReal_zero, zero_mul, sub_zero]

/-- The cut curve is continuous when `γ` is. -/
theorem continuous_capCutCurve {γ : ℝ → ℂ} {ν : ℂ} {t : ℝ} (hγ : Continuous γ) :
    Continuous (capCutCurve γ ν t) := by
  have h : Continuous fun θ : ℝ => ((capProfile γ ν t θ : ℝ) : ℂ) * ν :=
    ((Complex.continuous_ofReal.comp (continuous_capProfile hγ))).mul continuous_const
  rw [capCutCurve_fun_eq]
  exact hγ.sub h

theorem capCutCurve_periodic {γ : ℝ → ℂ} {ν : ℂ} {t : ℝ}
    (hγ : Function.Periodic γ (2 * Real.pi)) :
    Function.Periodic (capCutCurve γ ν t) (2 * Real.pi) := by
  intro θ
  rw [capCutCurve_apply, capCutCurve_apply, hγ θ, capProfile_periodic hγ θ]

/-- The push cylinder is continuous when `γ` is. -/
theorem continuous_capPush {γ : ℝ → ℂ} {ν : ℂ} {t : ℝ} (hγ : Continuous γ) :
    Continuous (capPush γ ν t) := by
  have h1 : Continuous fun p : ℝ × ℝ => ((p.2 * capProfile γ ν t p.1 : ℝ) : ℂ) * ν :=
    (Complex.continuous_ofReal.comp
      (continuous_snd.mul ((continuous_capProfile hγ).comp continuous_fst))).mul continuous_const
  rw [capPush_fun_eq]
  exact (hγ.comp continuous_fst).sub h1

/-- The push cylinder is `2π`-periodic in the first variable when `γ` is. -/
theorem capPush_periodic {γ : ℝ → ℂ} {ν : ℂ} {t : ℝ}
    (hγ : Function.Periodic γ (2 * Real.pi)) :
    ∀ θ s : ℝ, capPush γ ν t (θ + 2 * Real.pi, s) = capPush γ ν t (θ, s) := by
  intro θ s
  rw [capPush_apply, capPush_apply, hγ θ, capProfile_periodic hγ θ]

/-- After the cut, the `ν`-level of a point of the curve is `⟪γ θ,ν⟫` clamped at the level `t`. -/
theorem capCutCurve_dotV {γ : ℝ → ℂ} {ν : ℂ} (hν : ‖ν‖ = 1) (t θ : ℝ) :
    dotV (capCutCurve γ ν t θ) ν = min (dotV (γ θ) ν) t := by
  rw [capCutCurve_apply, dotV_sub, dotV_smul, dotV_self_eq_one hν, mul_one]
  rcases le_or_gt (dotV (γ θ) ν) t with h | h
  · rw [capProfile_eq_zero_of_le h, min_eq_left h]
    ring
  · rw [capProfile_eq_of_lt h, min_eq_right (le_of_lt h)]
    ring

/-! ## The two halves of the criterion -/

/-- **A swallowed chord produces a collision.**  If some `ν`-parallel chord of `γ` has both
endpoints at level `≥ t`, then the cap push at level `t` is *not* injective (in the sense that it
identifies two distinct points of the cylinder). -/
theorem not_push_injective_of_swallowed {γ : ℝ → ℂ} {ν : ℂ} {t : ℝ} (hν : ‖ν‖ = 1)
    {θ θ' : ℝ} (hdet : detV (γ θ - γ θ') ν = 0) (hne : γ θ ≠ γ θ')
    (hswallow : t ≤ dotV (γ θ) ν ∧ t ≤ dotV (γ θ') ν) :
    ¬ (∀ θ s θ' s', s ∈ Set.Icc (0:ℝ) 1 → s' ∈ Set.Icc (0:ℝ) 1 →
      γ θ - ((s * capProfile γ ν t θ : ℝ) : ℂ) * ν
        = γ θ' - ((s' * capProfile γ ν t θ' : ℝ) : ℂ) * ν →
      s * capProfile γ ν t θ = s' * capProfile γ ν t θ' ∧ γ θ = γ θ') := by
  intro hpush
  have hν0 : ν ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hν; norm_num at hν
  obtain ⟨c, hc⟩ := exists_smul_of_detV_eq_zero hν0 hdet
  have hdot : dotV (γ θ) ν - dotV (γ θ') ν = c := by
    have h1 := congrArg (fun z => dotV z ν) hc
    rwa [dotV_smul, dotV_self_eq_one hν, mul_one, dotV_sub] at h1
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0, Complex.ofReal_zero, zero_mul, sub_eq_zero] at hc
    exact hne hc
  rcases lt_or_gt_of_ne hcne with hneg | hpos
  · -- `c < 0`: push `θ'` down by `-c`, leaving `θ` alone
    have hlt : dotV (γ θ) ν < dotV (γ θ') ν := by linarith
    have hψ : capProfile γ ν t θ' = dotV (γ θ') ν - t := capProfile_eq_of_lt (by linarith [hswallow.2])
    have hψpos : 0 < capProfile γ ν t θ' := by rw [hψ]; linarith [hswallow.2]
    have hcle : -c ≤ capProfile γ ν t θ' := by
      rw [hψ]; linarith [hswallow.1]
    have hcol : γ θ - ((0 * capProfile γ ν t θ : ℝ) : ℂ) * ν
        = γ θ' - (((-c) / capProfile γ ν t θ' * capProfile γ ν t θ' : ℝ) : ℂ) * ν := by
      have h1 : (-c) / capProfile γ ν t θ' * capProfile γ ν t θ' = -c :=
        div_mul_cancel₀ (-c) (ne_of_gt hψpos)
      have h2 : γ θ = γ θ' + ((c : ℝ) : ℂ) * ν := by linear_combination hc
      rw [h1, h2, zero_mul, Complex.ofReal_zero, zero_mul, sub_zero]
      push_cast
      ring
    have hres := (hpush θ 0 θ' ((-c) / capProfile γ ν t θ') (by norm_num) (by
      refine ⟨div_nonneg (by linarith) (le_of_lt hψpos), ?_⟩
      exact (div_le_one hψpos).mpr hcle) hcol).1
    rw [zero_mul, div_mul_cancel₀ (-c) (ne_of_gt hψpos)] at hres
    exact hcne (neg_eq_zero.mp hres.symm)
  · -- `c > 0`: push `θ` down by `c`, leaving `θ'` alone
    have hlt : dotV (γ θ') ν < dotV (γ θ) ν := by linarith
    have hψ : capProfile γ ν t θ = dotV (γ θ) ν - t := capProfile_eq_of_lt (by linarith [hswallow.1])
    have hψpos : 0 < capProfile γ ν t θ := by rw [hψ]; linarith [hswallow.1]
    have hcle : c ≤ capProfile γ ν t θ := by
      rw [hψ]; linarith [hswallow.2]
    have hcol : γ θ - ((c / capProfile γ ν t θ * capProfile γ ν t θ : ℝ) : ℂ) * ν
        = γ θ' - ((0 * capProfile γ ν t θ' : ℝ) : ℂ) * ν := by
      have h1 : c / capProfile γ ν t θ * capProfile γ ν t θ = c :=
        div_mul_cancel₀ c (ne_of_gt hψpos)
      have h2 : γ θ = γ θ' + ((c : ℝ) : ℂ) * ν := by linear_combination hc
      rw [h1, h2, zero_mul, Complex.ofReal_zero, zero_mul, sub_zero]
      ring
    have hres := (hpush θ (c / capProfile γ ν t θ) θ' 0 (by
      refine ⟨div_nonneg (le_of_lt hpos) (le_of_lt hψpos), ?_⟩
      exact (div_le_one hψpos).mpr hcle) (by norm_num) hcol).1
    rw [zero_mul, div_mul_cancel₀ c (ne_of_gt hψpos)] at hres
    exact hcne hres

/-- **A legal cut is injective.**  If no `ν`-parallel chord of `γ` is swallowed by the cap
`{⟪·,ν⟫ ≥ t}`, then the push at level `t` is injective modulo the period (two points of the
cylinder with the same image carry the same profile value and the same point of `γ`). -/
theorem capPush_injective_of_legal {γ : ℝ → ℂ} {ν : ℂ} {t : ℝ} (hν : ‖ν‖ = 1)
    (hcrit : ∀ θ θ', detV (γ θ - γ θ') ν = 0 → γ θ ≠ γ θ' →
      min (dotV (γ θ) ν) (dotV (γ θ') ν) < t) :
    ∀ θ s θ' s', s ∈ Set.Icc (0:ℝ) 1 → s' ∈ Set.Icc (0:ℝ) 1 →
      γ θ - ((s * capProfile γ ν t θ : ℝ) : ℂ) * ν
        = γ θ' - ((s' * capProfile γ ν t θ' : ℝ) : ℂ) * ν →
      s * capProfile γ ν t θ = s' * capProfile γ ν t θ' ∧ γ θ = γ θ' := by
  have hν0 : ν ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hν; norm_num at hν
  intro θ s θ' s' hs hs' heq
  set c : ℝ := s * capProfile γ ν t θ - s' * capProfile γ ν t θ' with hcdef
  have hpar : γ θ - γ θ' = ((c : ℝ) : ℂ) * ν := by
    have h3 : γ θ - ((s * capProfile γ ν t θ : ℝ) : ℂ) * ν
        = γ θ' - ((s' * capProfile γ ν t θ' : ℝ) : ℂ) * ν := heq
    have h2 : ((c : ℝ) : ℂ) * ν
        = ((s * capProfile γ ν t θ : ℝ) : ℂ) * ν
          - ((s' * capProfile γ ν t θ' : ℝ) : ℂ) * ν := by
      rw [hcdef]; push_cast; ring
    rw [h2]
    linear_combination h3
  have hdot : dotV (γ θ) ν - dotV (γ θ') ν = c := by
    have h1 := congrArg (fun z => dotV z ν) hpar
    rwa [dotV_smul, dotV_self_eq_one hν, mul_one, dotV_sub] at h1
  by_cases hc0 : c = 0
  · refine ⟨sub_eq_zero.mp hc0, ?_⟩
    have hz : γ θ - γ θ' = 0 := by rw [hpar, hc0, Complex.ofReal_zero, zero_mul]
    exact sub_eq_zero.mp hz
  · exfalso
    have hγ : γ θ ≠ γ θ' := by
      intro h
      rw [h, sub_self] at hpar
      rcases mul_eq_zero.mp hpar.symm with h' | h'
      · exact hc0 (Complex.ofReal_eq_zero.mp h')
      · exact hν0 h'
    have hmin := hcrit θ θ' (by rw [hpar, detV_smul_left, detV_self, mul_zero]) hγ
    have hψθ : 0 ≤ capProfile γ ν t θ := capProfile_nonneg _ _ _ _
    have hψθ' : 0 ≤ capProfile γ ν t θ' := capProfile_nonneg _ _ _ _
    have hψeq : s * capProfile γ ν t θ - s' * capProfile γ ν t θ' = c := hcdef.symm
    rcases lt_or_gt_of_ne hc0 with hneg | hpos
    · -- `c < 0`: the minimum is `⟪γ θ,ν⟫`, which is `< t`
      have hu : dotV (γ θ) ν < t := by
        have hmm : min (dotV (γ θ) ν) (dotV (γ θ') ν) = dotV (γ θ) ν :=
          min_eq_left (by linarith)
        rwa [hmm] at hmin
      have hle : -c ≤ capProfile γ ν t θ' := by
        have h2 : -c = s' * capProfile γ ν t θ' - s * capProfile γ ν t θ := by linarith [hψeq]
        rw [h2, capProfile_eq_zero_of_le (le_of_lt hu), mul_zero, sub_zero]
        calc s' * capProfile γ ν t θ' ≤ 1 * capProfile γ ν t θ' :=
              mul_le_mul_of_nonneg_right hs'.2 hψθ'
          _ = capProfile γ ν t θ' := one_mul _
      rcases le_or_gt (dotV (γ θ') ν) t with h2 | h2
      · rw [capProfile_eq_zero_of_le h2] at hle; linarith
      · rw [capProfile_eq_of_lt h2] at hle; linarith
    · -- `c > 0`: the minimum is `⟪γ θ',ν⟫`, which is `< t`
      have hu : dotV (γ θ') ν < t := by
        have hmm : min (dotV (γ θ) ν) (dotV (γ θ') ν) = dotV (γ θ') ν :=
          min_eq_right (by linarith)
        rwa [hmm] at hmin
      have hle : c ≤ capProfile γ ν t θ := by
        rw [← hψeq, capProfile_eq_zero_of_le (le_of_lt hu), mul_zero, sub_zero]
        calc s * capProfile γ ν t θ ≤ 1 * capProfile γ ν t θ :=
              mul_le_mul_of_nonneg_right hs.2 hψθ
          _ = capProfile γ ν t θ := one_mul _
      rcases le_or_gt (dotV (γ θ) ν) t with h2 | h2
      · rw [capProfile_eq_zero_of_le h2] at hle; linarith
      · rw [capProfile_eq_of_lt h2] at hle; linarith

/-! ## The criterion -/

/-- The predicate "the push cylinder of the cap cut at level `t` is injective modulo the period",
in the form in which the chain assembly consumes it. -/
def CapPushInjective (γ : ℝ → ℂ) (ν : ℂ) (t : ℝ) : Prop :=
  ∀ θ s θ' s', s ∈ Set.Icc (0:ℝ) 1 → s' ∈ Set.Icc (0:ℝ) 1 →
    γ θ - ((s * capProfile γ ν t θ : ℝ) : ℂ) * ν
      = γ θ' - ((s' * capProfile γ ν t θ' : ℝ) : ℂ) * ν →
    s * capProfile γ ν t θ = s' * capProfile γ ν t θ' ∧ γ θ = γ θ'

/-- **The sharp legality criterion for a cap cut** (min-form): the push at level `t` is injective
modulo the period **if and only if** every `ν`-parallel chord of `γ` dips below the level `t`. -/
theorem capPush_injective_iff {γ : ℝ → ℂ} {ν : ℂ} {t : ℝ} (hν : ‖ν‖ = 1) :
    CapPushInjective γ ν t ↔
      ∀ θ θ', detV (γ θ - γ θ') ν = 0 → γ θ ≠ γ θ' →
        min (dotV (γ θ) ν) (dotV (γ θ') ν) < t := by
  constructor
  · intro hpush θ θ' hdet hne
    by_contra hcon
    have hs2 : t ≤ min (dotV (γ θ) ν) (dotV (γ θ') ν) := not_lt.mp hcon
    exact not_push_injective_of_swallowed hν hdet hne
      ⟨le_trans hs2 (min_le_left _ _), le_trans hs2 (min_le_right _ _)⟩ hpush
  · exact capPush_injective_of_legal hν

/-- **The sharp legality criterion for a cap cut** (geometric form): the push at level `t` is
injective modulo the period **if and only if** no chord of `γ` parallel to `ν` is swallowed by the
cap `{⟪·,ν⟫ ≥ t}`. -/
theorem capPush_injective_iff' {γ : ℝ → ℂ} {ν : ℂ} {t : ℝ} (hν : ‖ν‖ = 1) :
    CapPushInjective γ ν t ↔
      ∀ θ θ', detV (γ θ - γ θ') ν = 0 → γ θ ≠ γ θ' →
        ¬(t ≤ dotV (γ θ) ν ∧ t ≤ dotV (γ θ') ν) := by
  rw [capPush_injective_iff hν]
  constructor
  · intro h θ θ' hdet hne hsw
    exact absurd (h θ θ' hdet hne) (not_lt.mpr (le_min hsw.1 hsw.2))
  · intro h θ θ' hdet hne
    by_contra hcon
    have h2 : t ≤ min (dotV (γ θ) ν) (dotV (γ θ') ν) := not_lt.mp hcon
    exact h θ θ' hdet hne ⟨le_trans h2 (min_le_left _ _), le_trans h2 (min_le_right _ _)⟩

/-! ## The criterion for an arbitrary profile (composability with the `C¹` theory)

The cap-cut criterion above is the special case `ψ = capProfile γ ν t` of a criterion that holds
for an **arbitrary nonnegative profile** `ψ`.  Recording the general form matters because the cuts
used in the exhaustion produce curves *with corners*, whereas the index/separation theory of the
sibling modules is stated for `C¹` curves: the general criterion shows that one may freely replace
the piecewise-linear cap profile by a *smooth* profile (of the same support and height) and still has
a legal cut — hence a `C¹` cut curve — with no change in the geometry. -/

/-- **The push criterion for an arbitrary nonnegative profile.**  The push
`(θ,s) ↦ γ θ - s·ψ θ • ν` is injective modulo the period **iff** for every chord `γ θ - γ θ' = c ν`
the profile at the endpoint *pointing along* the chord is less than the chord length:
`0 < c → ψ θ < c` and `c < 0 → ψ θ' < -c`. -/
theorem push_injective_iff_of_profile {γ : ℝ → ℂ} {ν : ℂ} {ψ : ℝ → ℝ} (hν : ‖ν‖ = 1)
    (hψ : ∀ θ, 0 ≤ ψ θ) :
    (∀ θ s θ' s', s ∈ Set.Icc (0:ℝ) 1 → s' ∈ Set.Icc (0:ℝ) 1 →
      γ θ - ((s * ψ θ : ℝ) : ℂ) * ν = γ θ' - ((s' * ψ θ' : ℝ) : ℂ) * ν →
      s * ψ θ = s' * ψ θ' ∧ γ θ = γ θ') ↔
    (∀ θ θ' c : ℝ, γ θ - γ θ' = ((c : ℝ) : ℂ) * ν → c ≠ 0 →
      (0 < c → ψ θ < c) ∧ (c < 0 → ψ θ' < -c)) := by
  have hν0 : ν ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hν; norm_num at hν
  constructor
  · -- a violated condition yields an explicit collision
    intro hpush
    by_contra hcon
    simp only [not_forall] at hcon
    obtain ⟨θ, hcon⟩ := hcon
    obtain ⟨θ', hcon⟩ := hcon
    obtain ⟨c, hcon⟩ := hcon
    obtain ⟨hc, hcne, hnot⟩ := hcon
    rw [not_and_or] at hnot
    have hψθ := hψ θ
    have hψθ' := hψ θ'
    rcases hnot with h1 | h1
    · rw [Classical.not_imp, not_lt] at h1
      obtain ⟨hpos, hle⟩ := h1
      have hψpos : 0 < ψ θ := lt_of_lt_of_le hpos hle
      have hs : c / ψ θ * ψ θ = c := div_mul_cancel₀ c (ne_of_gt hψpos)
      have hcol : γ θ - ((c / ψ θ * ψ θ : ℝ) : ℂ) * ν
          = γ θ' - ((0 * ψ θ' : ℝ) : ℂ) * ν := by
        rw [hs, show γ θ' - ((0 * ψ θ' : ℝ) : ℂ) * ν = γ θ' from by
              rw [zero_mul, Complex.ofReal_zero, zero_mul, sub_zero]]
        linear_combination hc
      have hres := (hpush θ (c / ψ θ) θ' 0 (by
        refine ⟨div_nonneg (le_of_lt hpos) (le_of_lt hψpos),
          (div_le_one hψpos).mpr hle⟩) (by norm_num) hcol).1
      rw [zero_mul, hs] at hres
      exact hcne hres
    · rw [Classical.not_imp, not_lt] at h1
      obtain ⟨hneg, hle⟩ := h1
      have hψpos : 0 < ψ θ' := lt_of_lt_of_le (by linarith) hle
      have hs : (-c) / ψ θ' * ψ θ' = -c := div_mul_cancel₀ (-c) (ne_of_gt hψpos)
      have hcol : γ θ - ((0 * ψ θ : ℝ) : ℂ) * ν
          = γ θ' - (((-c) / ψ θ' * ψ θ' : ℝ) : ℂ) * ν := by
        rw [hs, show γ θ - ((0 * ψ θ : ℝ) : ℂ) * ν = γ θ from by
              rw [zero_mul, Complex.ofReal_zero, zero_mul, sub_zero]]
        have h2 : γ θ = γ θ' + ((c : ℝ) : ℂ) * ν := by linear_combination hc
        rw [h2]; push_cast; ring
      have hres := (hpush θ 0 θ' ((-c) / ψ θ') (by norm_num) (by
        refine ⟨div_nonneg (by linarith) (le_of_lt hψpos),
          (div_le_one hψpos).mpr hle⟩) hcol).1
      rw [zero_mul, hs] at hres
      exact hcne (neg_eq_zero.mp hres.symm)
  · -- the condition rules out every collision
    intro hcrit θ s θ' s' hs hs' heq
    set c : ℝ := s * ψ θ - s' * ψ θ' with hcdef
    have hpar : γ θ - γ θ' = ((c : ℝ) : ℂ) * ν := by
      have h2 : ((c : ℝ) : ℂ) * ν = ((s * ψ θ : ℝ) : ℂ) * ν - ((s' * ψ θ' : ℝ) : ℂ) * ν := by
        rw [hcdef]; push_cast; ring
      rw [h2]
      linear_combination heq
    by_cases hc0 : c = 0
    · refine ⟨sub_eq_zero.mp hc0, ?_⟩
      have hz : γ θ - γ θ' = 0 := by rw [hpar, hc0, Complex.ofReal_zero, zero_mul]
      exact sub_eq_zero.mp hz
    · exfalso
      obtain ⟨hpos, hneg⟩ := hcrit θ θ' c hpar hc0
      have hψθ := hψ θ
      have hψθ' := hψ θ'
      have hceq : c = s * ψ θ - s' * ψ θ' := hcdef
      rcases lt_or_gt_of_ne hc0 with hlt | hgt
      · have h1 : s' * ψ θ' ≤ ψ θ' := by
          calc s' * ψ θ' ≤ 1 * ψ θ' := mul_le_mul_of_nonneg_right hs'.2 hψθ'
            _ = ψ θ' := one_mul _
        have h2 : -c ≤ ψ θ' := by
          have : -c = s' * ψ θ' - s * ψ θ := by linarith [hceq]
          rw [this]
          linarith [h1, mul_nonneg hs.1 hψθ]
        linarith [hneg hlt, h2]
      · have h1 : s * ψ θ ≤ ψ θ := by
          calc s * ψ θ ≤ 1 * ψ θ := mul_le_mul_of_nonneg_right hs.2 hψθ
            _ = ψ θ := one_mul _
        have h2 : c ≤ ψ θ := by linarith [hceq, h1, mul_nonneg hs'.1 hψθ']
        linarith [hpos hgt, h2]

/-! ## The convergence criterion of the exhaustion, and the existence of a legal level -/

theorem dotV_le_norm (z ν : ℂ) : dotV z ν ≤ ‖z‖ * ‖ν‖ := by
  rw [dotV]
  calc ((starRingEnd ℂ) z * ν).re ≤ ‖(starRingEnd ℂ) z * ν‖ := Complex.re_le_norm _
    _ = ‖z‖ * ‖ν‖ := by rw [norm_mul, starRingEnd_apply, norm_star]

/-- **The convergence criterion of the cutting exhaustion.**  If a nested family of sets all contains
`p` and each set, at level `k`, eventually lies below the level `⟪p,ν⟫ + ε` in every direction `ν`
(this is what a *cap cut* through `p` produces), then the intersection is `{p}`. -/
theorem sInter_eq_singleton_of_halfplane_eventually {C : ℕ → Set ℂ} {p : ℂ}
    (hpmem : ∀ k, p ∈ C k)
    (hsup : ∀ ν : ℂ, ‖ν‖ = 1 → ∀ ε > 0, ∀ᶠ k in Filter.atTop,
      ∀ x ∈ C k, dotV x ν < dotV p ν + ε) :
    (⋂ k, C k) = {p} := by
  refine Set.Subset.antisymm ?_ (Set.singleton_subset_iff.mpr (Set.mem_iInter.mpr hpmem))
  intro q hq
  rw [Set.mem_singleton_iff]
  have hqk : ∀ k, q ∈ C k := Set.mem_iInter.mp hq
  have key : ∀ ν : ℂ, ‖ν‖ = 1 → dotV q ν ≤ dotV p ν := by
    intro ν hν
    by_contra hlt
    push Not at hlt
    have hε : 0 < (dotV q ν - dotV p ν) / 2 := by linarith
    obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp (hsup ν hν _ hε)
    have := hk k le_rfl q (hqk k)
    linarith
  have h1 : dotV q 1 = dotV p 1 := by
    refine le_antisymm (key 1 (by norm_num)) ?_
    have h := key (-1) (by norm_num)
    rw [dotV_neg_right, dotV_neg_right] at h
    linarith
  have hI : dotV q Complex.I = dotV p Complex.I := by
    refine le_antisymm (key Complex.I (by simp)) ?_
    have h := key (-Complex.I) (by rw [norm_neg]; simp)
    rw [dotV_neg_right, dotV_neg_right] at h
    linarith
  have hre : q.re = p.re := by
    have := h1
    rw [dotV_eq, dotV_eq] at this
    simpa using this
  have him : q.im = p.im := by
    have := hI
    rw [dotV_eq, dotV_eq] at this
    simpa using this
  exact Complex.ext hre him

/-! ## Simplicity of the cut curve -/

/-- For a simple closed continuous curve, a legal cap cut produces a curve which is again
injective on a period. -/
theorem capCutCurve_isSimple {γ : ℝ → ℂ} (hper : Function.Periodic γ (2 * Real.pi))
    (hsimp : Set.InjOn γ (Set.Ico 0 (2 * Real.pi))) {ν : ℂ} {t : ℝ} (_hν : ‖ν‖ = 1)
    (h : CapPushInjective γ ν t) :
    Set.InjOn (capCutCurve γ ν t) (Set.Ico 0 (2 * Real.pi)) := by
  intro θ hθ θ' hθ' heq
  have h1 := h θ 1 θ' 1 (by norm_num) (by norm_num)
    (by simpa only [capCutCurve_apply, one_mul] using heq)
  obtain ⟨k, hk⟩ := eq_mod_period_of_eq hper hsimp h1.2
  have hk0 : k = 0 := eq_of_int_mul_two_pi hθ hθ' hk
  rw [hk0, Int.cast_zero, zero_mul, add_zero] at hk
  exact hk.symm

/-! ## There is always a legal level for a bounded curve -/

/-- For a bounded curve and a unit direction, every level above the `ν`-extent of the curve gives a
legal cap cut (the cap is empty). -/
theorem exists_capPushInjective_of_lt {γ : ℝ → ℂ} {ν : ℂ} (hν : ‖ν‖ = 1)
    (hbdd : Bornology.IsBounded (Set.range γ)) :
    ∃ m : ℝ, ∀ t : ℝ, m < t → CapPushInjective γ ν t := by
  rcases (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp hbdd with ⟨r, hr⟩
  refine ⟨r, fun t ht => (capPush_injective_iff' hν).mpr fun θ θ' _ _ hcon => ?_⟩
  have hmem : γ θ ∈ Metric.closedBall (0 : ℂ) r := hr ⟨θ, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hmem
  have hlt : dotV (γ θ) ν < t := by
    have h := dotV_le_norm (γ θ) ν
    rw [hν, mul_one] at h
    linarith
  exact absurd hcon.1 (not_le.mpr hlt)

end

end Work.Smooth.JordanSeparation
