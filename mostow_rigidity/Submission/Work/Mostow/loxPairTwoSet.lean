import Mathlib
import Submission.Work.Mostow.mlDefs
import Submission.Work.Mostow.busemannCocycle

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-! A loxodromic element permutes only one two-point set of the boundary: its own fixed pair.

Route: if `a` permutes `{z, w}` (hypothesis `hpres`) then `a * a` fixes both `z` and `w`
(`bd (a * a) z = bd a (bd a z) = z` in both cases of `hpres`). Moreover
`busemann x ((a * a) • 0) = 2 * busemann x (a • 0) ≠ 0`: apply the cocycle clause of `HypIsometryProp`
with `g := a`, `ξ := x`, `u := a • 0`, using `bd a x = x`, the action law `(a * a) • 0 = a • (a • 0)`
and `bd a x = x` again. Now apply `hPS x y` (from `h : LoxPair a x y` you get `x, y ∈ Sph n` and
`x ≠ y`) to the element `a * a`: its third clause says that any boundary fixed point `ζ ≠ x, y` of
`a * a` forces `busemann x ((a * a) • 0) = 0`, a contradiction. So `z ∈ {x, y}` and, likewise,
`w ∈ {x, y}`, and `hne : z ≠ w` splits the conclusion into the two cases. -/
theorem loxPairTwoSet (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (hPS : Submission.Mostow.PairStabProp n)
    {a : LeanEval.Geometry.MostowRigidity.PO n 1} {x y : Submission.Mostow.E n}
    (h : Submission.Mostow.LoxPair a x y)
    {z w : Submission.Mostow.E n} (hz : z ∈ Submission.Mostow.Sph n)
    (hw : w ∈ Submission.Mostow.Sph n) (hne : z ≠ w)
    (hpres : (Submission.Mostow.bd a z = z ∧ Submission.Mostow.bd a w = w) ∨
      (Submission.Mostow.bd a z = w ∧ Submission.Mostow.bd a w = z)) :
    (z = x ∧ w = y) ∨ (z = y ∧ w = x) := by
  obtain ⟨hxS, hyS, hxy, hax, hay, hbus⟩ := h
  -- `bd (a * a)` is `bd a` twice
  have hmul : ∀ ξ : E n, ξ ∈ Sph n → bd (a * a) ξ = bd a (bd a ξ) := fun ξ hξ =>
    hA.2.2.2.2.2.2.2.2.2.1 a a ξ hξ
  have haa_x : bd (a * a) x = x := by
    rw [hmul x hxS, hax, hax]
  have haa_y : bd (a * a) y = y := by
    rw [hmul y hyS, hay, hay]
  -- `a * a` fixes `z` and `w`
  have haa_z : bd (a * a) z = z := by
    rw [hmul z hz]
    rcases hpres with ⟨hz', _⟩ | ⟨hz', hw'⟩
    · rw [hz', hz']
    · rw [hz', hw']
  have haa_w : bd (a * a) w = w := by
    rw [hmul w hw]
    rcases hpres with ⟨_, hw'⟩ | ⟨hz', hw'⟩
    · rw [hw', hw']
    · rw [hw', hz']
  -- the Busemann value at `a * a` is twice the one at `a`
  have hbus2 : busemann x ((a * a) • (0 : E n)) = 2 * busemann x (a • 0) := by
    rw [hA.2.2.2.2.1 a a (0 : E n)]
    have h1 := busemannCocycle n hA a x (a • 0) hxS
    rw [hax] at h1
    linarith
  have hbus2ne : busemann x ((a * a) • (0 : E n)) ≠ 0 := by
    rw [hbus2]
    exact mul_ne_zero two_ne_zero hbus
  -- no third boundary fixed point of `a * a` can exist
  obtain ⟨p, hp⟩ := hPS x y hxS hyS hxy
  have hthird : ∀ ζ ∈ Sph n, ζ ≠ x → ζ ≠ y → bd (a * a) ζ = ζ → False := by
    intro ζ hζ hζx hζy hbdζ
    exact hbus2ne ((hp (a * a) haa_x haa_y).2 ζ hζ hζx hζy hbdζ)
  have hzmem : z = x ∨ z = y := by
    by_contra hc
    exact hthird z hz (fun h' => hc (Or.inl h')) (fun h' => hc (Or.inr h')) haa_z
  have hwmem : w = x ∨ w = y := by
    by_contra hc
    exact hthird w hw (fun h' => hc (Or.inl h')) (fun h' => hc (Or.inr h')) haa_w
  rcases hzmem with hzx | hzy
  · rcases hwmem with hwx | hwy
    · exact absurd (hzx.trans hwx.symm) hne
    · exact Or.inl ⟨hzx, hwy⟩
  · rcases hwmem with hwx | hwy
    · exact Or.inr ⟨hzy, hwx⟩
    · exact absurd (hzy.trans hwy.symm) hne

end Work.Mostow
