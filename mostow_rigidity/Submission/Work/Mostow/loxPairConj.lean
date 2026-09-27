import Mathlib
import Submission.Work.Mostow.mlDefs
import Submission.Work.Mostow.busemann_smul_cocycle

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-! `LoxPair` is conjugation invariant, with the pair acted on by `bd t⁻¹`.

Show `LoxPair (t⁻¹ * a * t) (bd t⁻¹ x) (bd t⁻¹ y)`:
* `bd t⁻¹ x, bd t⁻¹ y ∈ Sph n`, and they are distinct because `bd t` is inverse to `bd t⁻¹` on
  `Sph n`: `bd (t * t⁻¹) ξ = bd 1 ξ = ξ` (`POActionProp`).
* `bd (t⁻¹ * a * t) (bd t⁻¹ x) = bd t⁻¹ (bd a (bd t (bd t⁻¹ x))) = bd t⁻¹ (bd a x) = bd t⁻¹ x`.
* Nonzero translation: show `busemann (bd t⁻¹ x) ((t⁻¹ * a * t) • 0) = busemann x (a • 0)`.
  Since `(t⁻¹ * a * t) • 0 = t⁻¹ • (a • (t • 0))` (action law), the cocycle clause with `g := t⁻¹`,
  `ξ := x`, `u := a • (t • 0)` gives
  `busemann (bd t⁻¹ x) ((t⁻¹*a*t) • 0) = busemann x (a • (t • 0)) + busemann (bd t⁻¹ x) (t⁻¹ • 0)`;
  the cocycle clause with `g := a`, `ξ := x`, `u := t • 0` gives
  `busemann x (a • (t • 0)) = busemann x (t • 0) + busemann x (a • 0)` (using `bd a x = x`);
  and the cocycle clause with `g := t`, `ξ := bd t⁻¹ x`, `u := t⁻¹ • 0` gives
  `0 = busemann (bd t⁻¹ x) (t⁻¹ • 0) + busemann x (t • 0)` (its left side is
  `busemann x 0 = 0`, because `bd t (bd t⁻¹ x) = x`). -/
theorem loxPairConj (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) {a : LeanEval.Geometry.MostowRigidity.PO n 1}
    {x y : Submission.Mostow.E n} (h : Submission.Mostow.LoxPair a x y)
    (t : LeanEval.Geometry.MostowRigidity.PO n 1) :
    Submission.Mostow.LoxPair (t⁻¹ * a * t) (Submission.Mostow.bd t⁻¹ x)
      (Submission.Mostow.bd t⁻¹ y) := by
  obtain ⟨hxS, hyS, hxy, hax, hay, hbus⟩ := h
  -- boundary sphere membership
  have hbdxS : bd t⁻¹ x ∈ Sph n := hA.2.2.2.2.2.2.2.1 t⁻¹ x hxS
  have hbdyS : bd t⁻¹ y ∈ Sph n := hA.2.2.2.2.2.2.2.1 t⁻¹ y hyS
  -- `bd t` inverts `bd t⁻¹` on the boundary sphere
  have hcancel : ∀ ξ ∈ Sph n, bd t (bd t⁻¹ ξ) = ξ := by
    intro ξ hξ
    have h1 := hA.2.2.2.2.2.2.2.2.2.1 t t⁻¹ ξ hξ
    rw [mul_inv_cancel t, hA.2.2.2.2.2.2.2.2.1 ξ hξ] at h1
    exact h1.symm
  refine ⟨hbdxS, hbdyS, ?_, ?_, ?_, ?_⟩
  · -- distinctness: apply `bd t` to both sides
    intro heq
    have h2 := congrArg (bd t) heq
    rw [hcancel x hxS, hcancel y hyS] at h2
    exact hxy h2
  · -- `bd (t⁻¹*a*t) (bd t⁻¹ x) = bd t⁻¹ x`
    have h1 := hA.2.2.2.2.2.2.2.2.2.1 (t⁻¹ * a) t (bd t⁻¹ x) hbdxS
    rw [hcancel x hxS, hA.2.2.2.2.2.2.2.2.2.1 t⁻¹ a x hxS, hax] at h1
    exact h1
  · -- `bd (t⁻¹*a*t) (bd t⁻¹ y) = bd t⁻¹ y`
    have h1 := hA.2.2.2.2.2.2.2.2.2.1 (t⁻¹ * a) t (bd t⁻¹ y) hbdyS
    rw [hcancel y hyS, hA.2.2.2.2.2.2.2.2.2.1 t⁻¹ a y hyS, hay] at h1
    exact h1
  · -- nonzero translation
    -- action law: `(t⁻¹ * a * t) • 0 = t⁻¹ • (a • (t • 0))`
    have hact : (t⁻¹ * a * t) • (0 : E n) = t⁻¹ • (a • (t • 0)) := by
      rw [hA.2.2.2.2.1 (t⁻¹ * a) t 0, hA.2.2.2.2.1 t⁻¹ a (t • 0)]
    -- cocycle with `g := t⁻¹`
    have e1 : busemann (bd t⁻¹ x) ((t⁻¹ * a * t) • (0 : E n))
        = busemann x (a • (t • 0)) + busemann (bd t⁻¹ x) (t⁻¹ • 0) := by
      have h1 := busemann_smul_cocycle n hA t⁻¹ (bd t⁻¹ x) (a • (t • 0)) hbdxS
      rw [inv_inv, hcancel x hxS] at h1
      rw [hact]
      exact h1
    -- cocycle with `g := a`
    have e2 : busemann x (a • (t • 0)) = busemann x (t • 0) + busemann x (a • 0) := by
      have h2 := busemannCocycle n hA a x (t • 0) hxS
      rw [hax] at h2
      exact h2
    -- cocycle with `g := t`
    have e3 : busemann x (t • 0) + busemann (bd t⁻¹ x) (t⁻¹ • 0) = 0 := by
      have ht0 : t • (t⁻¹ • (0 : E n)) = 0 := by
        rw [← hA.2.2.2.2.1 t t⁻¹ 0, mul_inv_cancel t, hA.2.2.2.1 0]
      have h3 := busemannCocycle n hA t (bd t⁻¹ x) (t⁻¹ • 0) hbdxS
      rw [hcancel x hxS, ht0, busemann_zero x] at h3
      linarith [h3]
    -- combine
    have hsum : busemann (bd t⁻¹ x) ((t⁻¹ * a * t) • (0 : E n)) = busemann x (a • 0) := by
      linarith [e1, e2, e3]
    rw [hsum]
    exact hbus

end Work.Mostow
