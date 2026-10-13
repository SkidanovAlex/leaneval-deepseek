/-
  WilE7 (`Work.WilE7.BandAux.bandS3two_bd`): the format and degree bounds for the two-strata band
  presentation `bandS3two Z S₁ S₂`.

  The chain of estimates is the one described in `Work.WilE7.bdBound`:

    `bandW1  Z S = Z ×_{ℝ^p} S.X`            (`fiberProdZ`)
    `bandW2two    = (Z × S₁.X) × (Z × S₂.X)` (`fiberProdZ` of the two `bandW1`'s)
    `bandPaddedtwo = bandW2two × [-1,1]`     (`SemiPf.prod`)
    `bandS3two     = bandPaddedtwo ∩ {v₂ < t < v₂'}` (`SemiPf.addConds`)

  With `F` bounding the formats and `D` the degrees of `Z`, `S₁.X`, `S₂.X`, we obtain
  `deg(bandW1) ≤ 8(1+F)(1+D)²`, `deg(bandW2two) ≤ 2(1+2F)(17+16F)²(1+D)⁴`,
  `deg(bandPaddedtwo) ≤ 2(1+2(1+2F)(17+16F)²)²(1+D)⁸` and finally
  `deg(bandS3two) ≤ 5·deg(bandPaddedtwo) + 4 ≤ bdBound F · (1+D)⁸`.  The format bound is
  `2·(2F) + 1 = 4F + 1`.
-/
import Mathlib
import Submission.Work.WilE7.BandAux.bdBoundDef
import Submission.Work.WilE7.BandAux.BandDefsTwo
import Submission.Work.WilE7.BandAux.BandDefs
import Submission.Work.WilE7.fiberProduct_semiPf
import Submission.Work.WilE7.prodDeg
import Submission.Work.WilE7.prod_semiPf
import Submission.Work.Wilkies.E.Spec

set_option autoImplicit false
noncomputable section
open Classical
open Work.WilE7 WilkiesDesign WilkiesDesign.E

namespace Work.WilE7.BandAux

/-- Piling the two inequalities `f > 0`, `g > 0` (of degree `≤ 2` each) onto a semi-Pfaffian
set `X` multiplies the degree bound by at most `5` (plus `4`).  This is the last step of the
`bandS3two` estimate, isolated because it is pure list/arithmetic bookkeeping. -/
theorem addConds_two_deg_le {k : ℕ} (X : SemiPf k) (f g : EAPoly k X.r)
    (hf : atomDeg f ≤ 2) (hg : atomDeg g ≤ 2) :
    (SemiPf.addConds X [] [f, g]).deg ≤ 5 * X.deg + 4 := by
  have h := SemiPf.addConds_deg_le X [] [f, g]
  have h2 : (([f, g] : List (EAPoly k X.r)).map atomDeg).sum ≤ 4 := by
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  simp only [List.map_nil, List.sum_nil, Nat.zero_add] at h
  have hm : max 1 X.deg ≤ X.deg + 1 := by
    rcases lt_or_ge 1 X.deg with hh | hh
    · rw [max_eq_right (le_of_lt hh)]; omega
    · rw [max_eq_left hh]; omega
  calc (SemiPf.addConds X [] [f, g]).deg
      ≤ X.deg + max 1 X.deg * (([f, g] : List (EAPoly k X.r)).map atomDeg).sum := h
    _ ≤ X.deg + (X.deg + 1) * 4 := Nat.add_le_add_left (Nat.mul_le_mul hm h2) X.deg
    _ = 5 * X.deg + 4 := by ring

theorem bandS3two_bd {p m : ℕ} (Z : WilkiesDesign.E.SemiPf (p + (m + 1)))
    (S₁ S₂ : WilkiesDesign.E.Stratum p (m + 1)) (F D : ℕ)
    (hZf : Z.fmt ≤ F) (hS1f : S₁.X.fmt ≤ F) (hS2f : S₂.X.fmt ≤ F)
    (hZd : Z.deg ≤ D) (hS1d : S₁.X.deg ≤ D) (hS2d : S₂.X.deg ≤ D) :
    (Work.WilE7.bandS3two Z S₁ S₂).fmt ≤ 4 * F + 1 ∧
    (Work.WilE7.bandS3two Z S₁ S₂).deg ≤ Work.WilE7.bdBound F * (1 + D) ^ 8 := by
  -- §1. The formats.
  have hW1f : ∀ (S : Stratum p (m + 1)), S.X.fmt ≤ F → (bandW1 Z S).fmt ≤ 2 * F := fun S hS =>
    fiberProdZ_fmt (p := p) (q := m + 1) Z S.X hZf hS
  have hW2f : (bandW2two Z S₁ S₂).fmt ≤ 4 * F := by
    have h := fiberProdZ_fmt (p := p + (m + 1)) (q := p + (m + 1)) (F := 2 * F)
      (bandW1 Z S₁) (bandW1 Z S₂) (hW1f S₁ hS1f) (hW1f S₂ hS2f)
    have h4 : 2 * (2 * F) = 4 * F := by ring
    rw [h4] at h
    exact h
  have hPaddf : (bandPaddedtwo Z S₁ S₂).fmt ≤ 4 * F + 1 := by
    have hp : (SemiPf.prod (bandW2two Z S₁ S₂) bandCube1).fmt
        = (bandW2two Z S₁ S₂).fmt + bandCube1.fmt := by
      simp only [SemiPf.fmt, SemiPf.prod_r]; omega
    have hc : bandCube1.fmt = 1 := by
      simp [bandCube1, Work.WilE8.cubeSemiPf, SemiPf.fmt]
    show (SemiPf.prod (bandW2two Z S₁ S₂) bandCube1).fmt ≤ 4 * F + 1
    rw [hp, hc]; omega
  have hfmt : (bandS3two Z S₁ S₂).fmt ≤ 4 * F + 1 := by
    rw [bandS3two, SemiPf.addConds_fmt]
    exact hPaddf
  -- §2. Degree of the single fibre product `W₁`, uniform in the stratum.
  have hW1d : ∀ (S : Stratum p (m + 1)), S.X.deg ≤ D →
      (bandW1 Z S).deg ≤ 8 * (1 + F) * (1 + D) ^ 2 := by
    intro S hSd
    have h := fiberProdZ_deg (p := p) (q := m + 1) (F := F) Z S.X hZf
    have h2 : 1 + (Z.deg + S.X.deg) ≤ 2 * (1 + D) := by omega
    have h3 : (1 + (Z.deg + S.X.deg)) ^ 2 ≤ 4 * (1 + D) ^ 2 := by
      have hp := Nat.pow_le_pow_left h2 2
      calc (1 + (Z.deg + S.X.deg)) ^ 2 ≤ (2 * (1 + D)) ^ 2 := hp
        _ = 4 * (1 + D) ^ 2 := by ring
    calc (bandW1 Z S).deg
        ≤ 2 * (1 + F) * (1 + (Z.deg + S.X.deg)) ^ 2 := h
      _ ≤ 2 * (1 + F) * (4 * (1 + D) ^ 2) := Nat.mul_le_mul_left _ h3
      _ = 8 * (1 + F) * (1 + D) ^ 2 := by ring
  -- §3. Degree of the double fibre product.
  have hW2d : (bandW2two Z S₁ S₂).deg
      ≤ 2 * (1 + 2 * F) * (17 + 16 * F) ^ 2 * (1 + D) ^ 4 := by
    have h := fiberProdZ_deg (p := p + (m + 1)) (q := p + (m + 1)) (F := 2 * F)
      (bandW1 Z S₁) (bandW1 Z S₂) (hW1f S₁ hS1f)
    have hd1 := hW1d S₁ hS1d
    have hd2 := hW1d S₂ hS2d
    have hsum : (bandW1 Z S₁).deg + (bandW1 Z S₂).deg ≤ 16 * (1 + F) * (1 + D) ^ 2 := by
      have hadd := Nat.add_le_add hd1 hd2
      calc (bandW1 Z S₁).deg + (bandW1 Z S₂).deg
          ≤ 8 * (1 + F) * (1 + D) ^ 2 + 8 * (1 + F) * (1 + D) ^ 2 := hadd
        _ = 16 * (1 + F) * (1 + D) ^ 2 := by ring
    have hone : 1 ≤ (1 + D) ^ 2 := Nat.one_le_pow 2 (1 + D) (by omega)
    have h4 : 1 + ((bandW1 Z S₁).deg + (bandW1 Z S₂).deg)
        ≤ (17 + 16 * F) * (1 + D) ^ 2 := by
      calc 1 + ((bandW1 Z S₁).deg + (bandW1 Z S₂).deg)
          ≤ (1 + D) ^ 2 + 16 * (1 + F) * (1 + D) ^ 2 := Nat.add_le_add hone hsum
        _ = (17 + 16 * F) * (1 + D) ^ 2 := by ring
    have h5 := Nat.pow_le_pow_left h4 2
    calc (bandW2two Z S₁ S₂).deg
        ≤ 2 * (1 + 2 * F) * (1 + ((bandW1 Z S₁).deg + (bandW1 Z S₂).deg)) ^ 2 := h
      _ ≤ 2 * (1 + 2 * F) * ((17 + 16 * F) * (1 + D) ^ 2) ^ 2 := Nat.mul_le_mul_left _ h5
      _ = 2 * (1 + 2 * F) * (17 + 16 * F) ^ 2 * (1 + D) ^ 4 := by ring
  -- §4. Degree after adjoining the vertical coordinate.
  have hCd : bandCube1.deg = 0 := by
    simp [bandCube1, Work.WilE8.cubeSemiPf, SemiPf.deg, Basic.deg]
  have hPa2 : (bandPaddedtwo Z S₁ S₂).deg ≤ 2 * (1 + (bandW2two Z S₁ S₂).deg) ^ 2 := by
    have hPa := prodDeg (bandW2two Z S₁ S₂) bandCube1
    simp only [hCd, Nat.add_zero] at hPa
    exact hPa
  have hPaddd : (bandPaddedtwo Z S₁ S₂).deg
      ≤ 2 * (1 + 2 * (1 + 2 * F) * (17 + 16 * F) ^ 2) ^ 2 * (1 + D) ^ 8 := by
    have h4 : 1 ≤ (1 + D) ^ 4 := Nat.one_le_pow 4 (1 + D) (by omega)
    have h5 : 1 + (bandW2two Z S₁ S₂).deg
        ≤ (1 + 2 * (1 + 2 * F) * (17 + 16 * F) ^ 2) * (1 + D) ^ 4 := by
      calc 1 + (bandW2two Z S₁ S₂).deg
          ≤ 1 + 2 * (1 + 2 * F) * (17 + 16 * F) ^ 2 * (1 + D) ^ 4 :=
              Nat.add_le_add_left hW2d 1
        _ ≤ (1 + D) ^ 4 + 2 * (1 + 2 * F) * (17 + 16 * F) ^ 2 * (1 + D) ^ 4 :=
              Nat.add_le_add_right h4 _
        _ = (1 + 2 * (1 + 2 * F) * (17 + 16 * F) ^ 2) * (1 + D) ^ 4 := by ring
    have h6 := Nat.pow_le_pow_left h5 2
    calc (bandPaddedtwo Z S₁ S₂).deg ≤ 2 * (1 + (bandW2two Z S₁ S₂).deg) ^ 2 := hPa2
      _ ≤ 2 * ((1 + 2 * (1 + 2 * F) * (17 + 16 * F) ^ 2) * (1 + D) ^ 4) ^ 2 :=
            Nat.mul_le_mul_left 2 h6
      _ = 2 * (1 + 2 * (1 + 2 * F) * (17 + 16 * F) ^ 2) ^ 2 * (1 + D) ^ 8 := by ring
  -- §5. Degree after the two inequalities.
  have hS3d : (bandS3two Z S₁ S₂).deg
      ≤ 10 * (1 + 2 * (1 + 2 * F) * (17 + 16 * F) ^ 2) ^ 2 * (1 + D) ^ 8 + 4 := by
    have h := addConds_two_deg_le (bandPaddedtwo Z S₁ S₂)
      (bandPlow p m (bandPaddedtwo Z S₁ S₂).r) (bandPhigh p m (bandPaddedtwo Z S₁ S₂).r)
      atomDeg_bandPlow atomDeg_bandPhigh
    calc (bandS3two Z S₁ S₂).deg ≤ 5 * (bandPaddedtwo Z S₁ S₂).deg + 4 := h
      _ ≤ 5 * (2 * (1 + 2 * (1 + 2 * F) * (17 + 16 * F) ^ 2) ^ 2 * (1 + D) ^ 8) + 4 :=
            Nat.add_le_add_right (Nat.mul_le_mul_left 5 hPaddd) 4
      _ = 10 * (1 + 2 * (1 + 2 * F) * (17 + 16 * F) ^ 2) ^ 2 * (1 + D) ^ 8 + 4 := by ring
  -- §6. Absorbing the constants into `bdBound F`.
  have hae : 2 * (1 + 2 * F) * (17 + 16 * F) ^ 2
      ≤ 2 * (1 + 2 * F) * (1 + 36 * (1 + F)) ^ 2 := by
    have h : 17 + 16 * F ≤ 1 + 36 * (1 + F) := by ring_nf; omega
    exact Nat.mul_le_mul_left (2 * (1 + 2 * F)) (Nat.pow_le_pow_left h 2)
  refine ⟨hfmt, ?_⟩
  calc (bandS3two Z S₁ S₂).deg
      ≤ 10 * (1 + 2 * (1 + 2 * F) * (17 + 16 * F) ^ 2) ^ 2 * (1 + D) ^ 8 + 4 := hS3d
    _ ≤ 10 * (1 + 2 * (1 + 2 * F) * (1 + 36 * (1 + F)) ^ 2) ^ 2 * (1 + D) ^ 8 + 4 := by
        have h1 : (1 + 2 * (1 + 2 * F) * (17 + 16 * F) ^ 2) ^ 2
            ≤ (1 + 2 * (1 + 2 * F) * (1 + 36 * (1 + F)) ^ 2) ^ 2 :=
          Nat.pow_le_pow_left (Nat.add_le_add_left hae 1) 2
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_right ((1 + D) ^ 8) (Nat.mul_le_mul_left 10 h1)) 4
    _ ≤ (10 * (1 + 2 * (1 + 2 * F) * (1 + 36 * (1 + F)) ^ 2) ^ 2 + 4) * (1 + D) ^ 8 := by
        have h8 : 1 ≤ (1 + D) ^ 8 := Nat.one_le_pow 8 (1 + D) (by omega)
        have h4 : 4 ≤ 4 * (1 + D) ^ 8 := by
          have hh := Nat.mul_le_mul_left 4 h8
          simpa using hh
        calc 10 * (1 + 2 * (1 + 2 * F) * (1 + 36 * (1 + F)) ^ 2) ^ 2 * (1 + D) ^ 8 + 4
            ≤ 10 * (1 + 2 * (1 + 2 * F) * (1 + 36 * (1 + F)) ^ 2) ^ 2 * (1 + D) ^ 8
                + 4 * (1 + D) ^ 8 := Nat.add_le_add_left h4 _
          _ = (10 * (1 + 2 * (1 + 2 * F) * (1 + 36 * (1 + F)) ^ 2) ^ 2 + 4)
                * (1 + D) ^ 8 := by ring
    _ = bdBound F * (1 + D) ^ 8 := by rfl

end Work.WilE7.BandAux
