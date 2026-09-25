import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.relT_defs
import Submission.Work.LT.chi_basic
import Submission.Work.LT.relT_sl3E_basic
import Submission.Work.LT.relT_sl3E_conj

namespace Work.LT

/-! **The dual action of the `SL₂`-transvections on the character indices.**

Conjugation by `y = E_ab(k)` sends `u(s,t) = E_ac(s)E_bc(t)` to `u(s+kt, t)`
(`relT_sl3E_conj`), so `L_y` maps the `χ_z`-isotypic component of `f` to the `χ_{Mab(-k) z}`
component (and `y = E_ba(k)` gives `u(s,t) ↦ u(s,t+ks)`, i.e. `Mba(-k)`).

ROUTE. A direct computation from the definitions. For `y = sl3E p a b k`:
`(fhat_z (L_y f))(g) = (p²)⁻¹ ∑_{s,t} conj(chi p z (s,t)) f(y u(s,t) g)`; use
`sl3E p a b k * colU p a b c st = colU p a b c (st.1 + k*st.2, st.2) * sl3E p a b k`
(from `relT_sl3E_conj`: `y u y⁻¹ = u(s+kt,t)` and `y u = (y u y⁻¹) y`), then reindex the sum by
`(s,t) ↦ (s + k*t, t)` (`Fintype.sum_bijective` for the bijection `st ↦ (st.1 + k*st.2, st.2)`)
and rewrite the character with `chi p z (st.1 + k*st.2, st.2) = chi p (Mab p k z) st` (a `ring`
identity on the exponents; see `chi_basic`). Symmetrically for `E_ba(k)` with `Mba` and
`(s,t) ↦ (s, t + k*s)`. NB: the correct index shift is `Mab p (-k)`, not `Mab p k`. -/

/-- The shear `(s,t) ↦ (s + k·t, t)` of `(ℤ/p)²`, as a permutation; the reindexing used for the
dual action of `E_ab(k)`. -/
def relTFhatShearA (p : ℕ) (k : ZMod p) : ZMod p × ZMod p ≃ ZMod p × ZMod p where
  toFun st := (st.1 + k * st.2, st.2)
  invFun st := (st.1 - k * st.2, st.2)
  left_inv st := by ext <;> ring
  right_inv st := by ext <;> ring

/-- The shear `(s,t) ↦ (s, t + k·s)` of `(ℤ/p)²`, as a permutation; the reindexing used for the
dual action of `E_ba(k)`. -/
def relTFhatShearB (p : ℕ) (k : ZMod p) : ZMod p × ZMod p ≃ ZMod p × ZMod p where
  toFun st := (st.1, st.2 + k * st.1)
  invFun st := (st.1, st.2 - k * st.1)
  left_inv st := by ext <;> ring
  right_inv st := by ext <;> ring

/-- The character index change under the shear `(s,t) ↦ (s - k·t, t)`: it is the dual transvection
`Mab p (-k)`. -/
lemma relTFhatChiShiftA (p : ℕ) [NeZero p] (k : ZMod p) (uv st : ZMod p × ZMod p) :
    chi p uv (st.1 - k * st.2, st.2) = chi p (Mab p (-k) uv) st := by
  simp only [chi, Mab]; congr 1; ring

/-- The character index change under the shear `(s,t) ↦ (s, t - k·s)`: it is the dual transvection
`Mba p (-k)`. -/
lemma relTFhatChiShiftB (p : ℕ) [NeZero p] (k : ZMod p) (uv st : ZMod p × ZMod p) :
    chi p uv (st.1, st.2 - k * st.1) = chi p (Mba p (-k) uv) st := by
  simp only [chi, Mba]; congr 1; ring

/-- Conjugation by the transvection `y = E_ab(k)` of the column subgroup, in the form
`y · u(st) = u(st.1 + k·st.2, st.2) · y`. -/
lemma relTFhatConjKeyA (p : ℕ) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (k : ZMod p) (st : ZMod p × ZMod p) :
    sl3E p a b k * colU p a b c st
      = colU p a b c (st.1 + k * st.2, st.2) * sl3E p a b k := by
  have hconj : sl3E p a b k * colU p a b c st * sl3E p a b (-k)
      = colU p a b c (st.1 + k * st.2, st.2) := by
    simpa only [colU] using (relT_sl3E_conj.1 p hab hac hbc k st.1 st.2)
  have hy : sl3E p a b (-k) * sl3E p a b k = 1 := relT_sl3E_basic.2.2.1 p hab k
  calc sl3E p a b k * colU p a b c st
      = sl3E p a b k * colU p a b c st * (sl3E p a b (-k) * sl3E p a b k) := by rw [hy, mul_one]
    _ = (sl3E p a b k * colU p a b c st * sl3E p a b (-k)) * sl3E p a b k := by
          simp only [mul_assoc]
    _ = colU p a b c (st.1 + k * st.2, st.2) * sl3E p a b k := by rw [hconj]

/-- Conjugation by the transvection `y = E_ba(k)` of the column subgroup, in the form
`y · u(st) = u(st.1, st.2 + k·st.1) · y`. -/
lemma relTFhatConjKeyB (p : ℕ) {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (k : ZMod p) (st : ZMod p × ZMod p) :
    sl3E p b a k * colU p a b c st
      = colU p a b c (st.1, st.2 + k * st.1) * sl3E p b a k := by
  have hconj : sl3E p b a k * colU p a b c st * sl3E p b a (-k)
      = colU p a b c (st.1, st.2 + k * st.1) := by
    simpa only [colU] using (relT_sl3E_conj.2 p hab hac hbc k st.1 st.2)
  have hy : sl3E p b a (-k) * sl3E p b a k = 1 := relT_sl3E_basic.2.2.1 p (Ne.symm hab) k
  calc sl3E p b a k * colU p a b c st
      = sl3E p b a k * colU p a b c st * (sl3E p b a (-k) * sl3E p b a k) := by rw [hy, mul_one]
    _ = (sl3E p b a k * colU p a b c st * sl3E p b a (-k)) * sl3E p b a k := by
          simp only [mul_assoc]
    _ = colU p a b c (st.1, st.2 + k * st.1) * sl3E p b a k := by rw [hconj]

/-- **The dual action of `E_ab(k)` on the character indices.** Left translation by the transvection
`y = E_ab(k)` sends the `χ_z`-isotypic component of `f` to the `χ_{Mab p (-k) z}`-component. -/
theorem relTFhatConjLeft (p : ℕ) [NeZero p] {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (k : ZMod p) (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
    (z : ZMod p × ZMod p) :
    ∀ g, fhat p a b c z (fun x => f (sl3E p a b k * x)) g
          = fhat p a b c (Mab p (-k) z) f (sl3E p a b k * g) := by
  intro g
  have step1 : (∑ st : ZMod p × ZMod p, star (chi p z st) *
        f (sl3E p a b k * (colU p a b c st * g)))
      = ∑ st : ZMod p × ZMod p, star (chi p z st) *
          f (colU p a b c (st.1 + k * st.2, st.2) * (sl3E p a b k * g)) := by
    refine Finset.sum_congr rfl (fun st _ => ?_)
    have h : sl3E p a b k * (colU p a b c st * g)
        = colU p a b c (st.1 + k * st.2, st.2) * (sl3E p a b k * g) := by
      rw [← mul_assoc, relTFhatConjKeyA p hab hac hbc k st, mul_assoc]
    rw [h]
  have step2 : (∑ st : ZMod p × ZMod p, star (chi p z st) *
        f (colU p a b c (st.1 + k * st.2, st.2) * (sl3E p a b k * g)))
      = ∑ st : ZMod p × ZMod p, star (chi p z (st.1 - k * st.2, st.2)) *
          f (colU p a b c st * (sl3E p a b k * g)) := by
    rw [← Equiv.sum_comp (relTFhatShearA p k) (fun st : ZMod p × ZMod p =>
        star (chi p z (st.1 - k * st.2, st.2)) * f (colU p a b c st * (sl3E p a b k * g)))]
    refine Finset.sum_congr rfl (fun st _ => ?_)
    simp only [relTFhatShearA, Equiv.coe_fn_mk]
    have h : chi p z (st.1 + k * st.2 - k * st.2, st.2) = chi p z st := by
      rw [show st.1 + k * st.2 - k * st.2 = st.1 from by ring]
    rw [h]
  have step3 : (∑ st : ZMod p × ZMod p, star (chi p z (st.1 - k * st.2, st.2)) *
        f (colU p a b c st * (sl3E p a b k * g)))
      = ∑ st : ZMod p × ZMod p, star (chi p (Mab p (-k) z) st) *
          f (colU p a b c st * (sl3E p a b k * g)) := by
    refine Finset.sum_congr rfl (fun st _ => ?_)
    rw [congrArg star (relTFhatChiShiftA p k z st)]
  simp only [fhat]
  rw [step1, step2, step3]

/-- **The dual action of `E_ba(k)` on the character indices.** Left translation by the transvection
`y = E_ba(k)` sends the `χ_z`-isotypic component of `f` to the `χ_{Mba p (-k) z}`-component. -/
theorem relTFhatConjRight (p : ℕ) [NeZero p] {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (k : ZMod p) (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
    (z : ZMod p × ZMod p) :
    ∀ g, fhat p a b c z (fun x => f (sl3E p b a k * x)) g
          = fhat p a b c (Mba p (-k) z) f (sl3E p b a k * g) := by
  intro g
  have step1 : (∑ st : ZMod p × ZMod p, star (chi p z st) *
        f (sl3E p b a k * (colU p a b c st * g)))
      = ∑ st : ZMod p × ZMod p, star (chi p z st) *
          f (colU p a b c (st.1, st.2 + k * st.1) * (sl3E p b a k * g)) := by
    refine Finset.sum_congr rfl (fun st _ => ?_)
    have h : sl3E p b a k * (colU p a b c st * g)
        = colU p a b c (st.1, st.2 + k * st.1) * (sl3E p b a k * g) := by
      rw [← mul_assoc, relTFhatConjKeyB p hab hac hbc k st, mul_assoc]
    rw [h]
  have step2 : (∑ st : ZMod p × ZMod p, star (chi p z st) *
        f (colU p a b c (st.1, st.2 + k * st.1) * (sl3E p b a k * g)))
      = ∑ st : ZMod p × ZMod p, star (chi p z (st.1, st.2 - k * st.1)) *
          f (colU p a b c st * (sl3E p b a k * g)) := by
    rw [← Equiv.sum_comp (relTFhatShearB p k) (fun st : ZMod p × ZMod p =>
        star (chi p z (st.1, st.2 - k * st.1)) * f (colU p a b c st * (sl3E p b a k * g)))]
    refine Finset.sum_congr rfl (fun st _ => ?_)
    simp only [relTFhatShearB, Equiv.coe_fn_mk]
    have h : chi p z (st.1, st.2 + k * st.1 - k * st.1) = chi p z st := by
      rw [show st.2 + k * st.1 - k * st.1 = st.2 from by ring]
    rw [h]
  have step3 : (∑ st : ZMod p × ZMod p, star (chi p z (st.1, st.2 - k * st.1)) *
        f (colU p a b c st * (sl3E p b a k * g)))
      = ∑ st : ZMod p × ZMod p, star (chi p (Mba p (-k) z) st) *
          f (colU p a b c st * (sl3E p b a k * g)) := by
    refine Finset.sum_congr rfl (fun st _ => ?_)
    rw [congrArg star (relTFhatChiShiftB p k z st)]
  simp only [fhat]
  rw [step1, step2, step3]

theorem relT_fhat_conj :
    ∀ (p : ℕ) [NeZero p] {a b c : Fin 3}, a ≠ b → a ≠ c → b ≠ c →
      ∀ (k : ZMod p) (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
        (z : ZMod p × ZMod p),
        (∀ g, fhat p a b c z (fun x => f (sl3E p a b k * x)) g
                = fhat p a b c (Mab p (-k) z) f (sl3E p a b k * g))
      ∧ (∀ g, fhat p a b c z (fun x => f (sl3E p b a k * x)) g
                = fhat p a b c (Mba p (-k) z) f (sl3E p b a k * g)) := by
  intro p hp a b c hab hac hbc k f z
  exact ⟨relTFhatConjLeft p hab hac hbc k f z, relTFhatConjRight p hab hac hbc k f z⟩

/- The request stub placed this theorem inside a nested `namespace Work.LT`, so the same statement
is also available at `Work.LT.Work.LT.relT_fhat_conj`. -/
namespace Work.LT

theorem relT_fhat_conj :
    ∀ (p : ℕ) [NeZero p] {a b c : Fin 3}, a ≠ b → a ≠ c → b ≠ c →
      ∀ (k : ZMod p) (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
        (z : ZMod p × ZMod p),
        (∀ g, fhat p a b c z (fun x => f (sl3E p a b k * x)) g
                = fhat p a b c (Mab p (-k) z) f (sl3E p a b k * g))
      ∧ (∀ g, fhat p a b c z (fun x => f (sl3E p b a k * x)) g
                = fhat p a b c (Mba p (-k) z) f (sl3E p b a k * g)) :=
  _root_.Work.LT.relT_fhat_conj

end Work.LT

end Work.LT
