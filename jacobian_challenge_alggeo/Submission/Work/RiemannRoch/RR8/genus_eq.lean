import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.Linear
import Submission.Work.CurveBasics.Linear.finiteDimensional_L
import Submission.Work.CurveBasics.Divisor.deg_nonneg
import Submission.Work.CurveBasics.Divisor.deg_eq_zero_iff
import Submission.Work.RiemannRoch.RRLib
import Submission.Work.RiemannRoch.RR.ExistsIeqZero
import Submission.Work.RiemannRoch.Canonical
import Submission.Work.RiemannRoch.Canonical.Properties
import Submission.Work.RiemannRoch.Duality.Basic
import Submission.Work.CurveBasics.Curve.BCSquare.divMap_isEffective
import Submission.Work.CurveBasics.exists_separating_element

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option maxHeartbeats 1000000

namespace Work.RiemannRoch.RR8

open Work.CurveBasics

universe u

/-- **Base change preserves degrees, for effective divisors of positive degree.**  If the base
change of the Riemann–Roch dimension `l` agrees with `l` for all divisors, then for an
effective divisor `E` of positive degree the base change `S.divMap E` has the same degree.

Subtracting Riemann–Roch for the divisors `n • E` and `(n+1) • E` (which have degree at least
`N`, the vanishing threshold for the index of speciality) shows that on `C'`
`i ((n+1) • E') = i (n • E') - (deg E' - deg E)`; the left hand side is a natural number for
every `n`, which forces `deg E' ≤ deg E`.  Since `E` (hence `E'`) is effective, `i` is
antitone along `n ↦ n • E'`, which gives the reverse inequality.

This is a local copy of the corresponding lemma of the RR8 chapter, so that this file does
not have to depend on it. -/
private theorem deg_divMap_eq_of_effective_pos_loc {k : Type u} [Field k] {F : Type u}
    [Field F] [Algebra k F] {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C')
    (hl : ∀ D : C.Div, C'.l (S.divMap D) = C.l D)
    (N : ℤ) (hN : ∀ D : C.Div, N ≤ C.deg D → Work.RiemannRoch.Curve.i C D = 0)
    {E : C.Div} (hEeff : E.IsEffective) (hEdeg : 0 < C.deg E) :
    C'.deg (S.divMap E) = C.deg E := by
  set d : ℤ := C'.deg (S.divMap E) - C.deg E with hddef
  have hE1 : (1 : ℤ) ≤ C.deg E := hEdeg
  obtain ⟨n0, hn0⟩ := exists_nat_ge (max N 1)
  have hn0N : N ≤ (n0 : ℤ) := le_trans (le_max_left N 1) hn0
  have hdegN : ∀ n : ℕ, n0 ≤ n → N ≤ C.deg (n • E) := by
    intro n hn
    have h1 : N ≤ (n : ℤ) := le_trans hn0N (by exact_mod_cast hn)
    rw [Curve.deg_nsmul, nsmul_eq_mul]
    calc N ≤ (n : ℤ) := h1
      _ = (n : ℤ) * 1 := (mul_one _).symm
      _ ≤ (n : ℤ) * C.deg E := mul_le_mul_of_nonneg_left hE1 (by positivity)
  have step : ∀ m : ℕ, n0 ≤ m →
      (Work.RiemannRoch.Curve.i C' (S.divMap ((m + 1) • E)) : ℤ)
        = (Work.RiemannRoch.Curve.i C' (S.divMap (m • E)) : ℤ) - d := by
    intro m hm
    have hm1 : N ≤ C.deg (m • E) := hdegN m hm
    have hm2 : N ≤ C.deg ((m + 1) • E) := hdegN (m + 1) (le_trans hm (Nat.le_succ m))
    have hi1 : Work.RiemannRoch.Curve.i C (m • E) = 0 := hN _ hm1
    have hi2 : Work.RiemannRoch.Curve.i C ((m + 1) • E) = 0 := hN _ hm2
    have r1 := Work.RiemannRoch.Curve.riemannRoch C (m • E)
    have r2 := Work.RiemannRoch.Curve.riemannRoch C ((m + 1) • E)
    have r1' := Work.RiemannRoch.Curve.riemannRoch C' (S.divMap (m • E))
    have r2' := Work.RiemannRoch.Curve.riemannRoch C' (S.divMap ((m + 1) • E))
    have hs : C.deg ((m + 1) • E) = C.deg (m • E) + C.deg E := by
      rw [succ_nsmul E m, Curve.deg_add]
    have hC : (C.l ((m + 1) • E) : ℤ) - (C.l (m • E) : ℤ) = C.deg E := by
      simp only [hi1, hi2, hs, Nat.cast_zero, sub_zero] at r1 r2
      linarith
    have hs' : C'.deg (S.divMap ((m + 1) • E))
        = C'.deg (S.divMap (m • E)) + C'.deg (S.divMap E) := by
      rw [succ_nsmul E m, map_add, Curve.deg_add]
    have hC' : (C'.l (S.divMap ((m + 1) • E)) : ℤ) - (C'.l (S.divMap (m • E)) : ℤ)
        = C'.deg (S.divMap E)
          + ((Work.RiemannRoch.Curve.i C' (S.divMap ((m + 1) • E)) : ℤ)
             - (Work.RiemannRoch.Curve.i C' (S.divMap (m • E)) : ℤ)) := by
      rw [hs'] at r2'
      linarith
    have e1 : (C'.l (S.divMap ((m + 1) • E)) : ℤ) = (C.l ((m + 1) • E) : ℤ) := by
      rw [hl ((m + 1) • E)]
    have e2 : (C'.l (S.divMap (m • E)) : ℤ) = (C.l (m • E) : ℤ) := by
      rw [hl (m • E)]
    rw [hddef]
    linarith [hC, hC', e1, e2]
  -- the reverse inequality, from anti-monotonicity of `i` along `n ↦ n • E'`
  have hge : C.deg E ≤ C'.deg (S.divMap E) := by
    have hE'eff : (S.divMap E).IsEffective := Curve.BCSquare.divMap_isEffective S hEeff
    have hlediv : (n0 • (S.divMap E)) ≤ ((n0 + 1) • (S.divMap E)) := by
      intro Q
      have hx : (0 : ℤ) ≤ (S.divMap E) Q := hE'eff Q
      rw [Finsupp.nsmul_apply, Finsupp.nsmul_apply, nsmul_eq_mul, nsmul_eq_mul]
      push_cast
      exact mul_le_mul_of_nonneg_right (by omega : ((n0 : ℤ)) ≤ (n0 : ℤ) + 1) hx
    have hanti := Work.RiemannRoch.RR.i_anti C' hlediv
    have hst := step n0 (le_refl n0)
    simp only [map_nsmul] at hst
    have hcast : (Work.RiemannRoch.Curve.i C' ((n0 + 1) • (S.divMap E)) : ℤ)
        ≤ (Work.RiemannRoch.Curve.i C' (n0 • (S.divMap E)) : ℤ) := by
      exact_mod_cast hanti
    linarith [hst, hcast, hddef]
  have hle : C'.deg (S.divMap E) ≤ C.deg E := by
    by_contra hcon
    push_neg at hcon
    have hd1 : (1 : ℤ) ≤ d := by rw [hddef]; omega
    set I : ℤ := (Work.RiemannRoch.Curve.i C' (S.divMap (n0 • E)) : ℤ) with hI
    have hI0 : (0 : ℤ) ≤ I := by rw [hI]; exact Int.natCast_nonneg _
    set kk : ℕ := I.toNat + 1 with hkk
    have hkkI : (kk : ℤ) = I + 1 := by
      rw [hkk]; push_cast; rw [Int.toNat_of_nonneg hI0]
    have key : ∀ n : ℕ, n0 ≤ n →
        (Work.RiemannRoch.Curve.i C' (S.divMap (n • E)) : ℤ)
          = I - ((n : ℤ) - (n0 : ℤ)) * d := by
      intro n hn
      refine Nat.le_induction ?_ ?_ n hn
      · simp [hI]
      · intro q hq ih
        rw [step q hq, ih]
        push_cast
        ring
    have hkey := key (n0 + kk) (Nat.le_add_right n0 kk)
    have harith : (((n0 + kk : ℕ) : ℤ) - (n0 : ℤ)) = (kk : ℤ) := by push_cast; ring
    rw [harith] at hkey
    rw [hkkI] at hkey
    have hpos : (0 : ℤ) ≤ (Work.RiemannRoch.Curve.i C' (S.divMap ((n0 + kk) • E)) : ℤ) :=
      Int.natCast_nonneg _
    have hlt : I - (I + 1) * d < 0 := by
      have hle' : (I + 1) * 1 ≤ (I + 1) * d :=
        mul_le_mul_of_nonneg_left hd1 (by linarith)
      rw [mul_one] at hle'
      linarith
    linarith [hkey, hpos, hlt]
  linarith

/-- **Base change preserves degrees.**  For a base-change square `S : BCSquare C C'` along which
the Riemann–Roch dimension `l` is preserved (`C'.l (S.divMap D) = C.l D` for all `D`), the
pullback of divisors preserves degrees: `deg (S.divMap D) = deg D` for every divisor `D`.

Any divisor is a sum of multiples of place divisors, and the identity is additive in `D` and
known for the place divisors by `deg_divMap_eq_of_effective_pos_loc`.  This is a local copy of
the corresponding lemma of the RR8 chapter, so that this file does not have to depend on it. -/
private theorem deg_divMap_loc {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Work.CurveBasics.Curve k} {C' : Work.CurveBasics.Curve F}
    (S : Work.CurveBasics.Curve.BCSquare C C')
    (hl : ∀ D : C.Div, C'.l (S.divMap D) = C.l D) (D : C.Div) :
    C'.deg (S.divMap D) = C.deg D := by
  obtain ⟨N, hN⟩ := Work.RiemannRoch.Curve.exists_i_eq_zero C
  have hplace : ∀ Q : C.Place,
      C'.deg (S.divMap (Curve.Div.place Q)) = C.deg (Curve.Div.place Q) := by
    intro Q
    have heff : (Curve.Div.place Q).IsEffective := by
      intro R
      rw [Curve.Div.place]
      by_cases h : R = Q
      · subst h; rw [Finsupp.single_eq_same]; norm_num
      · rw [Finsupp.single_eq_of_ne h]
    have hdeg : 0 < C.deg (Curve.Div.place Q) := by
      rw [Curve.deg_place]
      exact_mod_cast Place.residueDegree_pos Q
    exact deg_divMap_eq_of_effective_pos_loc S hl N hN heff hdeg
  refine Finsupp.induction D ?_ ?_
  · simp
  · intro Q n f _ _ ih
    have hsingle : Finsupp.single Q n = n • Curve.Div.place Q := by
      rw [Curve.Div.place, Finsupp.smul_single, smul_eq_mul, mul_one]
    have hsingle2 : C'.deg (S.divMap (Finsupp.single Q n)) = C.deg (Finsupp.single Q n) := by
      rw [hsingle, map_zsmul, Curve.deg_zsmul, Curve.deg_zsmul, hplace Q]
    simp only [map_add, Curve.deg_add]
    rw [ih, hsingle2]

/-- **The genus is invariant under base change of curves.**

Riemann–Roch holds unconditionally on both curves (finiteness of the genus is a theorem,
`hasFiniteGenus`).  Together with the hypothesis `hl : l (S.divMap D) = l D` and the identity
`deg (S.divMap D) = deg D` (`deg_divMap_loc`), comparing the two Riemann–Roch equations for the
same divisor `D` of `C` yields, for every `D`,
`i C' (S.divMap D) = i C D + (genus C' - genus C)`.

Both indices of speciality vanish in large degree (`exists_i_eq_zero`).  Taking `D = n • [P]` for
a place `P` of positive degree and `n` so large that both `deg D` and `deg (S.divMap D) = deg D`
exceed the two vanishing thresholds, the relation gives `0 = 0 + (genus C' - genus C)`, hence
`genus C' = genus C`. -/
theorem genus_eq {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Work.CurveBasics.Curve k} {C' : Work.CurveBasics.Curve F}
    (S : Work.CurveBasics.Curve.BCSquare C C')
    (hl : ∀ D : C.Div, C'.l (S.divMap D) = C.l D) :
    Work.RiemannRoch.Curve.genus C' = Work.RiemannRoch.Curve.genus C := by
  -- Riemann–Roch on both curves, together with `hl` and degree preservation, gives for every
  -- divisor `D` of `C` the relation `i'(S.divMap D) = i(D) + (g' - g)`.
  have key : ∀ D : C.Div,
      (Work.RiemannRoch.Curve.i C' (S.divMap D) : ℤ)
        = (Work.RiemannRoch.Curve.i C D : ℤ)
          + ((Work.RiemannRoch.Curve.genus C' : ℤ) - (Work.RiemannRoch.Curve.genus C : ℤ)) := by
    intro D
    have hC := Work.RiemannRoch.Curve.riemannRoch C D
    have hC' := Work.RiemannRoch.Curve.riemannRoch C' (S.divMap D)
    rw [hl D, deg_divMap_loc S hl D] at hC'
    linarith
  -- Both `i` and `i'` vanish in large degree ...
  obtain ⟨N, hN⟩ := Work.RiemannRoch.Curve.exists_i_eq_zero C
  obtain ⟨N', hN'⟩ := Work.RiemannRoch.Curve.exists_i_eq_zero C'
  -- ... so evaluate the relation at a divisor `n • H` of degree exceeding both thresholds.
  obtain ⟨P⟩ := Work.CurveBasics.exists_place C
  set H : C.Div := Curve.Div.place P with hH
  have hHpos : (1 : ℤ) ≤ C.deg H := by
    rw [hH, Curve.deg_place]
    exact_mod_cast Place.residueDegree_pos P
  obtain ⟨n, hn⟩ := exists_nat_ge (max (max N N') 1)
  have hnN : N ≤ (n : ℤ) :=
    le_trans (le_trans (le_max_left N N') (le_max_left (max N N') 1)) hn
  have hnN' : N' ≤ (n : ℤ) :=
    le_trans (le_trans (le_max_right N N') (le_max_left (max N N') 1)) hn
  have hdeg_eq : C.deg (n • H) = (n : ℤ) * C.deg H := by
    rw [Curve.deg_nsmul, nsmul_eq_mul]
  have hmul_ge : ∀ {M : ℤ}, M ≤ (n : ℤ) → M ≤ (n : ℤ) * C.deg H := by
    intro M hM
    have h1 : (n : ℤ) * 1 ≤ (n : ℤ) * C.deg H :=
      mul_le_mul_of_nonneg_left hHpos (by positivity)
    rw [mul_one] at h1
    linarith
  have hi : Work.RiemannRoch.Curve.i C (n • H) = 0 := by
    apply hN
    rw [hdeg_eq]
    exact hmul_ge hnN
  have hi' : Work.RiemannRoch.Curve.i C' (S.divMap (n • H)) = 0 := by
    apply hN'
    rw [deg_divMap_loc S hl (n • H), hdeg_eq]
    exact hmul_ge hnN'
  have hk := key (n • H)
  rw [hi, hi'] at hk
  have hg : (Work.RiemannRoch.Curve.genus C' : ℤ)
      = (Work.RiemannRoch.Curve.genus C : ℤ) := by
    linarith
  exact_mod_cast hg

end Work.RiemannRoch.RR8
