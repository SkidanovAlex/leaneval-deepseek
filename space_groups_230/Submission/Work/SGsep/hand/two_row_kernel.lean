import Mathlib
import Submission.Work.SGsep.hand.HandDefs2

namespace Work.SGsep.hand

open Work.SG Work.SG.Data Work.SGsep.Hand Work.SGsep.Hand.Data

/-! ## Componentwise tooling for `V3`

`V3` is the flat integer vector record `⟨x, y, z⟩ : ℤ³`.  It has no extensionality
theorem registered, so we provide one; the remaining lemmas are the blackboard
computation identities for the cross product written out in components. -/

/-- Extensionality for `V3` (no `[ext]` theorem is generated for the structure). -/
theorem V3.ext' {a b : V3} (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a; cases b; simp_all

/-- Bilinearity of the cross product in its first argument. -/
theorem V3.cross_smul_left (m : Int) (z c : V3) :
    V3.cross (V3.smul m z) c = V3.smul m (V3.cross z c) := by
  apply V3.ext' <;> simp [V3.cross, V3.smul] <;> ring

/-- Vector triple product, first form: `(a × b) × c = (a·c) b − (b·c) a`. -/
theorem V3.cross_cross_left (a b c : V3) :
    V3.cross (V3.cross a b) c =
      V3.sub (V3.smul (V3.dot a c) b) (V3.smul (V3.dot b c) a) := by
  apply V3.ext' <;> simp [V3.cross, V3.smul, V3.sub, V3.dot] <;> ring

/-- Vector triple product, second form: `a × (b × c) = (a·c) b − (a·b) c`. -/
theorem V3.cross_cross_right (a b c : V3) :
    V3.cross a (V3.cross b c) =
      V3.sub (V3.smul (V3.dot a c) b) (V3.smul (V3.dot a b) c) := by
  apply V3.ext' <;> simp [V3.cross, V3.smul, V3.sub, V3.dot] <;> ring

/-- The zero scalar kills any vector. -/
theorem V3.smul_zero' (v : V3) : V3.smul 0 v = V3.zero := by
  apply V3.ext' <;> simp [V3.smul, V3.zero]

/-- `v − v = 0`. -/
theorem V3.sub_self (v : V3) : V3.sub v v = V3.zero := by
  apply V3.ext' <;> simp [V3.sub, V3.zero]

/-- A nonzero scalar multiple of `w` can only vanish if `w` does. -/
theorem V3.smul_eq_zero {m : Int} (hm : m ≠ 0) {w : V3} (h : V3.smul m w = V3.zero) :
    w = V3.zero := by
  have hx : m * w.x = 0 := by
    have := congrArg V3.x h; simpa [V3.smul, V3.zero] using this
  have hy : m * w.y = 0 := by
    have := congrArg V3.y h; simpa [V3.smul, V3.zero] using this
  have hz : m * w.z = 0 := by
    have := congrArg V3.z h; simpa [V3.smul, V3.zero] using this
  apply V3.ext'
  · exact (mul_eq_zero.mp hx).resolve_left hm
  · exact (mul_eq_zero.mp hy).resolve_left hm
  · exact (mul_eq_zero.mp hz).resolve_left hm

/-- The self dot product of a nonzero integer vector is a nonzero integer. -/
theorem V3.dot_self_ne_zero {z : V3} (hz : z ≠ V3.zero) : V3.dot z z ≠ 0 := by
  intro h
  have hq : (V3.dot z z : ℚ) = (z.x:ℚ)^2 + (z.y:ℚ)^2 + (z.z:ℚ)^2 := by
    simp only [V3.dot]; push_cast; ring
  have hzq : (z.x:ℚ) ≠ 0 ∨ (z.y:ℚ) ≠ 0 ∨ (z.z:ℚ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨h1,h2,h3⟩ := hcon
    apply hz
    apply V3.ext'
    · simp only [V3.zero]; exact_mod_cast h1
    · simp only [V3.zero]; exact_mod_cast h2
    · simp only [V3.zero]; exact_mod_cast h3
  have hpos : (0:ℚ) < (z.x:ℚ)^2 + (z.y:ℚ)^2 + (z.z:ℚ)^2 := by
    rcases hzq with hx|hx|hx
    · have := sq_pos_of_ne_zero hx; nlinarith [sq_nonneg (z.y:ℚ), sq_nonneg (z.z:ℚ)]
    · have := sq_pos_of_ne_zero hx; nlinarith [sq_nonneg (z.x:ℚ), sq_nonneg (z.z:ℚ)]
    · have := sq_pos_of_ne_zero hx; nlinarith [sq_nonneg (z.x:ℚ), sq_nonneg (z.y:ℚ)]
  have h2 : (V3.dot z z : ℚ) = 0 := by exact_mod_cast h
  rw [hq] at h2
  linarith

/-- Two-row kernel lemma: a vector killed by two independent rows `r`, `s` (independence tested by
`cross r s = m • z`, `m ≠ 0`, `z ≠ 0`) is a rational multiple of the cross product direction `z`. -/
theorem two_row_kernel {r s z : V3} {m : Int} (hm : m ≠ 0) (hz : z ≠ V3.zero)
    (h : V3.cross r s = V3.smul m z) {c : V3} (hr : V3.dot r c = 0) (hs : V3.dot s c = 0) :
    ∃ q : ℚ, (c.x : ℚ) = q * (z.x : ℚ) ∧ (c.y : ℚ) = q * (z.y : ℚ) ∧ (c.z : ℚ) = q * (z.z : ℚ) := by
  -- Step 1: `c` is orthogonal to `r × s = m z`, hence `z × c = 0`.
  have h1 := V3.cross_cross_left r s c
  rw [hr, hs] at h1
  simp only [V3.smul_zero', V3.sub_self] at h1
  rw [h, V3.cross_smul_left] at h1
  have hcz : V3.cross z c = V3.zero := V3.smul_eq_zero hm h1
  -- Step 2: `z × c = 0` forces `(z·z) c = (z·c) z`, i.e. `c` is a rational multiple of `z`.
  have h2 := V3.cross_cross_right z z c
  rw [hcz] at h2
  have hcross0 : V3.cross z V3.zero = V3.zero := by
    apply V3.ext' <;> simp [V3.cross, V3.zero]
  rw [hcross0] at h2
  have ex : (V3.dot z c) * z.x = (V3.dot z z) * c.x := by
    have := congrArg V3.x h2
    simp [V3.sub, V3.smul, V3.zero] at this
    omega
  have ey : (V3.dot z c) * z.y = (V3.dot z z) * c.y := by
    have := congrArg V3.y h2
    simp [V3.sub, V3.smul, V3.zero] at this
    omega
  have ez : (V3.dot z c) * z.z = (V3.dot z z) * c.z := by
    have := congrArg V3.z h2
    simp [V3.sub, V3.smul, V3.zero] at this
    omega
  have hzq : (V3.dot z z : ℚ) ≠ 0 := by
    have := V3.dot_self_ne_zero hz
    exact_mod_cast this
  refine ⟨(V3.dot z c : ℚ) / (V3.dot z z : ℚ), ?_, ?_, ?_⟩
  · have hc : (V3.dot z c : ℚ) * (z.x : ℚ) = (V3.dot z z : ℚ) * (c.x : ℚ) := by
      have := congrArg (fun t : ℤ => (t : ℚ)) ex
      push_cast at this
      linarith
    field_simp
    linarith
  · have hc : (V3.dot z c : ℚ) * (z.y : ℚ) = (V3.dot z z : ℚ) * (c.y : ℚ) := by
      have := congrArg (fun t : ℤ => (t : ℚ)) ey
      push_cast at this
      linarith
    field_simp
    linarith
  · have hc : (V3.dot z c : ℚ) * (z.z : ℚ) = (V3.dot z z : ℚ) * (c.z : ℚ) := by
      have := congrArg (fun t : ℤ => (t : ℚ)) ez
      push_cast at this
      linarith
    field_simp
    linarith

end Work.SGsep.hand
