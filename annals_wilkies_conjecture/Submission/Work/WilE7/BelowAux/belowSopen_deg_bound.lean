/-
  WilE7 (`Submission.Work.WilE7.BelowAux.belowSopen_deg_bound`): the *arithmetic* of the
  semi-Pfaffian presentation `belowSopen Z S` of the open below cell.

  `belowSopen Z S = belowS Z S ∩ {t > -1}` (`BelowAux.belowOpenDefs`), and `belowS` is built by
  chaining three operations on DNF presentations:

    `belowW1 = fiberProdZ Z S.X`            (`fibreProduct_semiPf`),
    `belowPadded = SemiPf.prod belowW1 cube` (`prodDeg`),
    `belowS = SemiPf.addConds belowPadded [] [belowPhigh]` (`BandAux.BandDefs`),

  followed by one more `addConds` cut with `belowOpenAtom` for `belowSopen`.  Each of these
  operations has a polynomial degree estimate in the degrees of the inputs (and, for the fibre
  product, the format bound `F`); chaining them gives

    `deg (belowSopen Z S) ≤ 18 * (1 + 2 (1 + F) (1 + 2 D)²)² + 8`

  whenever `Z.fmt, S.X.fmt ≤ F` and `Z.deg, S.X.deg ≤ D`.  The polynomial `Cb` exhibited below
  evaluates exactly to the right hand side; its coefficients depend only on `F`.

  The estimate is used by `Work.WilE7.belowBand_bd`, which needs a *uniform* (in `p`, `m`) degree
  bound for the single `*`-piece presenting the open below band.
-/
import Mathlib
import Submission.Work.WilE7.BelowAux.belowOpenDefs
import Submission.Work.WilE7.prodDeg

namespace Work.WilE7.BelowAux

theorem belowSopen_deg_bound (F : ℕ) : ∃ Cb : Polynomial ℕ,
    ∀ {p m : ℕ} (Z : WilkiesDesign.E.SemiPf (p + (m + 1)))
      (S : WilkiesDesign.E.Stratum p (m + 1)) (D : ℕ),
      WilkiesDesign.E.SemiPf.fmt Z ≤ F → WilkiesDesign.E.SemiPf.fmt S.X ≤ F →
      WilkiesDesign.E.SemiPf.deg Z ≤ D → WilkiesDesign.E.SemiPf.deg S.X ≤ D →
      WilkiesDesign.E.SemiPf.deg (Work.WilE7.BelowAux.belowSopen Z S) ≤ Cb.eval D := by
  refine ⟨Polynomial.C 18 *
      (1 + Polynomial.C (2 * (1 + F)) * (1 + Polynomial.C 2 * Polynomial.X) ^ 2) ^ 2 +
      Polynomial.C 8, ?_⟩
  intro p m Z S D hZF hSF hZD hSD
  -- the value of the exhibited polynomial at `D`
  have hCb : (Polynomial.C 18 *
        (1 + Polynomial.C (2 * (1 + F)) * (1 + Polynomial.C 2 * Polynomial.X) ^ 2) ^ 2 +
        Polynomial.C 8 : Polynomial ℕ).eval D
      = 18 * (1 + 2 * (1 + F) * (1 + 2 * D) ^ 2) ^ 2 + 8 := by simp
  rw [hCb]
  -- ### degree of the fibre product `belowW1 Z S = fiberProdZ Z S.X`
  have hW : (belowW1 Z S).deg ≤ 2 * (1 + F) * (1 + 2 * D) ^ 2 := by
    have h0 := Work.WilE7.fiberProdZ_deg (p := p) (q := m + 1) (F := F) Z S.X hZF
    have hsum : Z.deg + S.X.deg ≤ 2 * D := by omega
    have hsq : (1 + (Z.deg + S.X.deg)) ^ 2 ≤ (1 + 2 * D) ^ 2 :=
      Nat.pow_le_pow_left (Nat.add_le_add_left hsum 1) 2
    exact le_trans h0 (Nat.mul_le_mul_left (2 * (1 + F)) hsq)
  -- ### degree of the padded product `belowPadded Z S = prod (belowW1 Z S) bandCube1`
  -- (`bandCube1` has degree `0`, so the bound collapses)
  have hP0 : (belowPadded Z S).deg ≤ 2 * (1 + (belowW1 Z S).deg) ^ 2 :=
    Work.WilE7.prodDeg (belowW1 Z S) Work.WilE7.bandCube1
  have hP : (belowPadded Z S).deg ≤ 2 * (1 + 2 * (1 + F) * (1 + 2 * D) ^ 2) ^ 2 := by
    refine le_trans hP0 (Nat.mul_le_mul_left 2 ?_)
    exact Nat.pow_le_pow_left (Nat.add_le_add_left hW 1) 2
  -- ### the two strict atoms raise the degree by at most `2` each
  have hPhigh : WilkiesDesign.E.atomDeg (belowPhigh p m (belowPadded Z S).r) ≤ 2 :=
    atomDeg_belowPhigh
  have hOpen : WilkiesDesign.E.atomDeg (belowOpenAtom p m (belowS Z S).r) ≤ 2 := by
    have h := MvPolynomial.totalDegree_add
      (MvPolynomial.X (Sum.inl (belowTIdx p m)) :
        WilkiesDesign.E.EAPoly (belowDim p m) (belowS Z S).r)
      (MvPolynomial.C (1 : ℝ) : WilkiesDesign.E.EAPoly (belowDim p m) (belowS Z S).r)
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C] at h
    simp only [WilkiesDesign.E.atomDeg, belowOpenAtom]
    omega
  -- cutting with one inequality of degree `≤ 2`
  have hB : (belowS Z S).deg ≤ 3 * (belowPadded Z S).deg + 2 := by
    have h := Work.WilE7.SemiPf.addConds_deg_le (belowPadded Z S) []
      [belowPhigh p m (belowPadded Z S).r]
    simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, zero_add,
      add_zero] at h
    refine le_trans h ?_
    have hm : max 1 (belowPadded Z S).deg ≤ 1 + (belowPadded Z S).deg :=
      max_le (by omega) (by omega)
    have e : max 1 (belowPadded Z S).deg *
          WilkiesDesign.E.atomDeg (belowPhigh p m (belowPadded Z S).r)
        ≤ (1 + (belowPadded Z S).deg) * 2 :=
      le_trans (Nat.mul_le_mul_left _ hPhigh) (Nat.mul_le_mul_right 2 hm)
    calc (belowPadded Z S).deg + max 1 (belowPadded Z S).deg *
          WilkiesDesign.E.atomDeg (belowPhigh p m (belowPadded Z S).r)
        ≤ (belowPadded Z S).deg + (1 + (belowPadded Z S).deg) * 2 :=
          Nat.add_le_add_left e _
      _ = 3 * (belowPadded Z S).deg + 2 := by ring
  -- cutting `belowS` with the strict atom `t > -1`
  have hO : (belowSopen Z S).deg ≤ 3 * (belowS Z S).deg + 2 := by
    have h := Work.WilE7.SemiPf.addConds_deg_le (belowS Z S) []
      [belowOpenAtom p m (belowS Z S).r]
    simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons, zero_add,
      add_zero] at h
    refine le_trans h ?_
    have hm : max 1 (belowS Z S).deg ≤ 1 + (belowS Z S).deg :=
      max_le (by omega) (by omega)
    have e : max 1 (belowS Z S).deg * WilkiesDesign.E.atomDeg (belowOpenAtom p m (belowS Z S).r)
        ≤ (1 + (belowS Z S).deg) * 2 :=
      le_trans (Nat.mul_le_mul_left _ hOpen) (Nat.mul_le_mul_right 2 hm)
    calc (belowS Z S).deg + max 1 (belowS Z S).deg *
          WilkiesDesign.E.atomDeg (belowOpenAtom p m (belowS Z S).r)
        ≤ (belowS Z S).deg + (1 + (belowS Z S).deg) * 2 := Nat.add_le_add_left e _
      _ = 3 * (belowS Z S).deg + 2 := by ring
  -- ### assembly
  calc (belowSopen Z S).deg
      ≤ 3 * (belowS Z S).deg + 2 := hO
    _ ≤ 3 * (3 * (belowPadded Z S).deg + 2) + 2 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 3 hB) 2
    _ = 9 * (belowPadded Z S).deg + 8 := by ring
    _ ≤ 9 * (2 * (1 + 2 * (1 + F) * (1 + 2 * D) ^ 2) ^ 2) + 8 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left 9 hP) 8
    _ = 18 * (1 + 2 * (1 + F) * (1 + 2 * D) ^ 2) ^ 2 + 8 := by ring

end Work.WilE7.BelowAux
