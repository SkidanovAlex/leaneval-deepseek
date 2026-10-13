/-
  WilC4/InvFamDefs : the *value-inverted* family `InvY Y` and the *halved* breakpoint family
  `HalfB B₀`, together with the bookkeeping that relates them to `Y`, `B₀`.

  ## Why these are here

  `ratW_gt_of_window` needs a *lower* bound `|w| > 2/N` on the doubling ratio at a point `z` whose
  window `[z/N, N z']` misses `B₀`.  The available uniform input is the *upper* bound
  `deep_ratio_scale_bdd`: at a `β`-deep point (for `B₀`), `|f_c(2x)/f_c(x)| < β`.

  The lower bound for `Y` is the upper bound for the family whose fibre is `1/f_c`, since

      `RatW (InvY Y) c x u ↔ u ≠ 0 ∧ RatW Y c x u⁻¹`

  (see `ratW_invY_iff`): inverting the fibre value inverts the doubling ratio at the *same* point,
  so `IsDeepR` (which only sees `B₀`, `c`, `β`, `x`) is unchanged.  The one correction needed is in
  the *monotonicity* half of `ULPMStruct`: on a `B₀`-free interval the ratio `f(2t)/f(t)` of the
  inverse family can change sign when `2t` crosses a breakpoint, i.e. at `t = b/2`.  Enlarging the
  breakpoint family to `HalfB B₀ = B₀ ∪ B₀/2` restores constant sign and hence monotonicity
  (`invY_ulpmStruct`).

  `deep_ratio_scale_bdd` is applied to `InvY Y` at the breakpoint family `HalfB B₀`; the scale
  loss of a factor `2` (`HalfB` needs `2β`-deepness in `B₀`) is harmless because the target
  constant `2/N` has room: the argument produces the stronger `4/N < |w|`.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ULPMAsm
import Submission.Work.WilC4.ulpmTot_definable

set_option autoImplicit false
noncomputable section
open Classical FirstOrder FirstOrder.Language
namespace Work.WilC4

open WilkiesDesign WilkiesDesign.CG
open Work.WilC4.Route (Gr InD valY ratioY)

variable {k : ℕ}

/-! ## 1. The value-inverted family -/

/-- The *value-inverted* family: `v ∈ InvY Y` iff `v` encodes `(x, y, c)` with `y ≠ 0` and
`1/y` a value of the fibre of `Y` at `(c, x)`.  Equivalently the fibre of `InvY Y` at `(c, x)` is
`(f_c x)⁻¹` where `f_c` is defined and nonzero, and is empty otherwise.

The definition is written with the index embedding `UlpmEmb` so that it is a finite-existential
projection of a preimage of `Y` (`invY_definable`). -/
def InvY (Y : Set (Fin (k + 2) → ℝ)) : Set (Fin (k + 2) → ℝ) :=
  {v | ∃ u : Fin 1 → ℝ, u 0 ≠ 0 ∧ u 0 * v 1 = 1 ∧
    (Sum.elim v u) ∘ (UlpmEmb k) ∈ Y}

/-- Membership in `InvY Y` read on the free coordinates `(x, y, c)` of `v`. -/
theorem mem_invY_iff (Y : Set (Fin (k + 2) → ℝ)) (v : Fin (k + 2) → ℝ) :
    v ∈ InvY Y ↔ ∃ u : Fin 1 → ℝ, u 0 ≠ 0 ∧ u 0 * v 1 = 1 ∧
      Fin.cons (v 0) (Fin.cons (u 0) (fun i : Fin k => v i.succ.succ)) ∈ Y := by
  unfold InvY
  constructor
  · rintro ⟨u, h1, h2, h3⟩
    exact ⟨u, h1, h2, by rwa [ulpmEmb_comp] at h3⟩
  · rintro ⟨u, h1, h2, h3⟩
    exact ⟨u, h1, h2, by rwa [ulpmEmb_comp]⟩

/-- **The graph relation of the inverse family.**  `Gr (InvY Y) c x y` iff `y ≠ 0` and `y⁻¹` is a
value of the fibre of `Y` at `(c, x)`. -/
theorem gr_invY_iff (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x y : ℝ) :
    Gr (InvY Y) c x y ↔ y ≠ 0 ∧ Gr Y c x y⁻¹ := by
  show Fin.cons x (Fin.cons y c) ∈ InvY Y ↔ y ≠ 0 ∧ Fin.cons x (Fin.cons y⁻¹ c) ∈ Y
  rw [mem_invY_iff]
  have ht : (fun i : Fin k => (Fin.cons x (Fin.cons y c) : Fin (k+2) → ℝ) i.succ.succ) = c := by
    funext i; simp
  have hz : (Fin.cons x (Fin.cons y c) : Fin (k+2) → ℝ) 0 = x := rfl
  have ho : (Fin.cons x (Fin.cons y c) : Fin (k+2) → ℝ) 1 = y := by simp
  rw [ht, hz, ho]
  constructor
  · rintro ⟨u, hu0, huy, hY⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [mul_zero] at huy
      exact zero_ne_one huy
    have hu : u 0 = y⁻¹ := by
      refine mul_right_cancel₀ hy0 ?_
      rw [huy, inv_mul_cancel₀ hy0]
    exact ⟨hy0, by rw [hu] at hY; exact hY⟩
  · rintro ⟨hy0, hY⟩
    exact ⟨fun _ : Fin 1 => y⁻¹, by simpa using hy0, by rw [inv_mul_cancel₀ hy0],
      by simpa using hY⟩

/-- The inverse family is a family of graphs as soon as `Y` is. -/
theorem invY_functional {Y : Set (Fin (k + 2) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y') :
    ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr (InvY Y) c x y → Gr (InvY Y) c x y' → y = y' := by
  intro c x y y' hy hy'
  rw [gr_invY_iff] at hy hy'
  have h : y⁻¹ = y'⁻¹ := hfun c x _ _ hy.2 hy'.2
  rwa [inv_inj] at h

/-- **The doubling ratio of the inverse family is the inverse ratio:** inverting the fibre value
inverts the doubling ratio at the same point. -/
theorem ratW_invY_iff (Y : Set (Fin (k + 2) → ℝ)) (c : Fin k → ℝ) (x w : ℝ) :
    RatW (InvY Y) c x w ↔ w ≠ 0 ∧ RatW Y c x w⁻¹ := by
  constructor
  · rintro ⟨y, y', hy, hy', hy0, hwy⟩
    rw [gr_invY_iff] at hy hy'
    obtain ⟨hyne, hyY⟩ := hy
    obtain ⟨hy'ne, hy'Y⟩ := hy'
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [zero_mul] at hwy
      exact hy'ne hwy.symm
    have hw : w = y' * y⁻¹ := by
      apply mul_right_cancel₀ hyne
      rw [hwy, mul_assoc, inv_mul_cancel₀ hyne, mul_one]
    refine ⟨hw0, y⁻¹, y'⁻¹, hyY, hy'Y, inv_ne_zero hyne, ?_⟩
    rw [hw, mul_inv, inv_inv, mul_assoc, mul_inv_cancel₀ hyne, mul_one]
  · rintro ⟨hw0, y, y', hy, hy', hy0, hwy⟩
    have hy'0 : y' ≠ 0 := by
      rw [← hwy]
      exact mul_ne_zero (inv_ne_zero hw0) hy0
    refine ⟨y⁻¹, y'⁻¹,
      (gr_invY_iff Y c x y⁻¹).mpr ⟨inv_ne_zero hy0, by rwa [inv_inv]⟩,
      (gr_invY_iff Y c (2 * x) y'⁻¹).mpr ⟨inv_ne_zero hy'0, by rwa [inv_inv]⟩,
      inv_ne_zero hy0, ?_⟩
    have : y' = w⁻¹ * y := hwy.symm
    rw [this, mul_inv, inv_inv]

/-! ## 2. The halved breakpoint family -/

/-- The breakpoint family `B₀ ∪ B₀/2`: the breakpoints of `B₀` together with their halves (the
halving acts on the *argument* coordinate, `v 0`).  On a `HalfB B₀`-free interval the fibre `f`
is nonzero at `t` *and* at `2t`, which makes the ratio `f(2t)/f(t)` of constant sign. -/
def HalfB (B₀ : Set (Fin (k + 1) → ℝ)) : Set (Fin (k + 1) → ℝ) :=
  B₀ ∪ {v | Fin.cons (2 * v 0) (fun i : Fin k => v i.succ) ∈ B₀}

/-- Membership of a `HalfB`-point in the free coordinates. -/
theorem mem_halfB_iff (B₀ : Set (Fin (k + 1) → ℝ)) (b : ℝ) (c : Fin k → ℝ) :
    Fin.cons b c ∈ HalfB B₀ ↔ Fin.cons b c ∈ B₀ ∨ Fin.cons (2 * b) c ∈ B₀ := by
  unfold HalfB
  simp only [Set.mem_union, Set.mem_ofPred_eq, Fin.cons_zero, Fin.cons_succ]

/-- **Deepness for `HalfB` follows from deepness for `B₀` at twice the scale.**  The window
`[x/β, βx]` of a `β`-deep point of `B₀` misses `HalfB B₀` as soon as `[x/(2β), 2βx]` misses `B₀`:
the `B₀` part is contained in the latter, and a halved breakpoint `b/2` in the former would put
`b` in `[2x/β, 2βx] ⊆ [x/(2β), 2βx]`. -/
theorem isDeepR_halfB {B₀ : Set (Fin (k + 1) → ℝ)} {c : Fin k → ℝ} {β x : ℝ}
    (hβ : 0 < β) (hx : 0 < x) (h : IsDeepR B₀ c β x) : IsDeepR (HalfB B₀) c (β / 2) x := by
  have h2β : 2 * (β / 2) = β := by ring
  have hxβ : 0 < x / β := div_pos hx hβ
  intro b hb hcon
  rw [h2β] at hcon
  obtain ⟨hb1, hb2⟩ := hcon
  rw [mem_halfB_iff] at hb
  rcases hb with hbB | hbB
  · exact h b hbB ⟨le_trans (by rw [div_le_div_iff₀ (by positivity) hβ]; linarith) hb1,
      le_trans hb2 (by nlinarith [hβ, hx])⟩
  · refine h (2 * b) hbB ⟨?_, ?_⟩
    · have h2 : 2 * (x / β) ≤ 2 * b := by linarith
      have h1 : x / (2 * β) ≤ 2 * (x / β) := by
        rw [show x / (2 * β) = (x / β) / 2 by ring]
        nlinarith [hxβ]
      linarith
    · nlinarith [hb2, hβ, hx]

end Work.WilC4
