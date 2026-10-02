/-
Copyright: subproject `Submission/Work/SeedCertNum/` of `mandelbar_not_path_connected`.

# Locating the certified point in the ray area's boxes

The ray area `SeedCertRay` ships three boxes of *rational* endpoints (`Work.SeedCertRay.Xb`,
`Zb`, `Ab`, built in `Submission/Work/SeedCertRay/Q.lean` from mantissas at scale `2^40`), and its
`landsAt_alphas_data` asks for `Xb.mem c`, `Zb.mem z₁`, `Ab.mem A` for one *single* `(c, z₁, A)`.
This area's `cb`, `z1`, `Aquad` (see `NOTES.md` §13) are that point; this file states the three
memberships in the coordinates of those boxes, so the consumer only has to compare the rational
endpoints of `Xb`/`Zb`/`Ab` with the bounds below.

The boxes are:

* `Xb`: centre `(-1293728561597/2^40, 195856658686/2^40)`, half-width `2^-30`
  (`HWM = 1024 = 2^10`);
* `Zb`: centre `(-1293130773744/2^40, 195408601406/2^40)`, half-width `2^-20`;
* `Ab`: centre `( 415268074471237/2^40, 624540193106589/2^40)`, half-width `2^-20`.

## Main results

* `Abox_in_rayAb`, `Xz_in_rayZb`, `Xt_in_rayXb` — the dyadic endpoint comparisons of the boxes of
  this area (`Abox`, `krawData.Xz`, `krawData.Xt`) with the half-width boxes above;
* `Aquad_in_rayAbD`, `z1_in_rayZbD`, `cb_in_rayXbD` — the resulting statements for the certified
  `A`, `z₁`, `c_b`, with the bounds still written as `Dya.toReal`s;
* `Aquad_in_rayAb`, `z1_in_rayZb`, `cb_in_rayXb` — the same with plain `ℝ` numerals.
-/
import Mathlib
import Submission.Work.SeedCertNum.A1Export

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCert

noncomputable section

set_option maxRecDepth 10000

/-! ## The dyadic endpoint comparisons -/

/-- `Abox` (the enclosure of `A = F''(z₁)/2`) lies in the half-width-`2^-20` box about the ray
area's `Ab` centre. -/
theorem Abox_in_rayAb :
    Dya.le (Dya.sub (dy 415268074471237 40) (dy 1 20)) Abox.rlo = true ∧
    Dya.le Abox.rhi (Dya.add (dy 415268074471237 40) (dy 1 20)) = true ∧
    Dya.le (Dya.sub (dy 624540193106589 40) (dy 1 20)) Abox.ilo = true ∧
    Dya.le Abox.ihi (Dya.add (dy 624540193106589 40) (dy 1 20)) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `krawData.Xz` (the box of `z₁`) lies in the half-width-`2^-20` box about the ray area's `Zb`
centre. -/
theorem Xz_in_rayZb :
    Dya.le (Dya.sub (dy (-1293130773744) 40) (dy 1 20)) krawData.Xz.rlo = true ∧
    Dya.le krawData.Xz.rhi (Dya.add (dy (-1293130773744) 40) (dy 1 20)) = true ∧
    Dya.le (Dya.sub (dy 195408601406 40) (dy 1 20)) krawData.Xz.ilo = true ∧
    Dya.le krawData.Xz.ihi (Dya.add (dy 195408601406 40) (dy 1 20)) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- `krawData.Xt` (the interval of `Im c`) lies in the half-width-`2^-30` interval about the ray
area's `Xb` centre imaginary part. -/
theorem Xt_in_rayXb :
    Dya.le (Dya.sub (dy 195856658686 40) (dy 1 30)) krawData.Xt.lo = true ∧
    Dya.le krawData.Xt.hi (Dya.add (dy 195856658686 40) (dy 1 30)) = true :=
  ⟨by decide, by decide⟩

/-! ## The membership statements, with the bounds as `Dya.toReal`s -/

/-- **`Aquad` is in the ray area's `Ab`.** -/
theorem Aquad_in_rayAbD :
    ((dy 415268074471237 40).sub (dy 1 20)).toReal ≤ Aquad.re ∧
    Aquad.re ≤ ((dy 415268074471237 40).add (dy 1 20)).toReal ∧
    ((dy 624540193106589 40).sub (dy 1 20)).toReal ≤ Aquad.im ∧
    Aquad.im ≤ ((dy 624540193106589 40).add (dy 1 20)).toReal := by
  obtain ⟨h1, h2, h3, h4⟩ := Abox_in_rayAb
  obtain ⟨hm1, hm2, hm3, hm4⟩ := (CBox.mem_toSet.mp Aquad_mem)
  exact ⟨le_trans ((Dya.toReal_le_iff _ _).mp h1) hm1,
         le_trans hm2 ((Dya.toReal_le_iff _ _).mp h2),
         le_trans ((Dya.toReal_le_iff _ _).mp h3) hm3,
         le_trans hm4 ((Dya.toReal_le_iff _ _).mp h4)⟩

/-- **`z1` is in the ray area's `Zb`.** -/
theorem z1_in_rayZbD :
    ((dy (-1293130773744) 40).sub (dy 1 20)).toReal ≤ z1.re ∧
    z1.re ≤ ((dy (-1293130773744) 40).add (dy 1 20)).toReal ∧
    ((dy 195408601406 40).sub (dy 1 20)).toReal ≤ z1.im ∧
    z1.im ≤ ((dy 195408601406 40).add (dy 1 20)).toReal := by
  obtain ⟨h1, h2, h3, h4⟩ := Xz_in_rayZb
  obtain ⟨hm1, hm2, hm3, hm4⟩ := (CBox.mem_toSet.mp z1_mem)
  exact ⟨le_trans ((Dya.toReal_le_iff _ _).mp h1) hm1,
         le_trans hm2 ((Dya.toReal_le_iff _ _).mp h2),
         le_trans ((Dya.toReal_le_iff _ _).mp h3) hm3,
         le_trans hm4 ((Dya.toReal_le_iff _ _).mp h4)⟩

/-- The second coordinate of the Krawczyk point, `Im c_b`. -/
theorem krawU_im_in_rayXbD :
    ((dy 195856658686 40).sub (dy 1 30)).toReal ≤ krawU.2.2 ∧
    krawU.2.2 ≤ ((dy 195856658686 40).add (dy 1 30)).toReal := by
  obtain ⟨h1, h2⟩ := Xt_in_rayXb
  obtain ⟨hm1, hm2⟩ := (IV.mem_toSet.mp cb_im_mem)
  exact ⟨le_trans ((Dya.toReal_le_iff _ _).mp h1) hm1,
         le_trans hm2 ((Dya.toReal_le_iff _ _).mp h2)⟩

/-- **`cb` is in the ray area's `Xb`**: `Re c_b` is *exactly* the centre real part. -/
theorem cb_in_rayXbD :
    ((dy 195856658686 40).sub (dy 1 30)).toReal ≤ cb.im ∧
    cb.im ≤ ((dy 195856658686 40).add (dy 1 30)).toReal := by
  have hcbim : cb.im = krawU.2.2 := by simp [cb, cOf_apply]
  rw [hcbim]
  exact krawU_im_in_rayXbD

/-! ## The membership statements, with plain `ℝ` numerals -/

theorem dy_sub_val (n : ℤ) (e k : ℕ) :
    ((dy n e).sub (dy 1 k)).toReal = (n : ℝ) / 2 ^ e - 2 ^ (-(k : ℤ)) := by
  rw [Dya.toReal_sub, Dya.toReal, Dya.toReal]
  simp only [dy, Int.cast_one, one_div]
  rw [zpow_neg, zpow_natCast]

theorem dy_add_val (n : ℤ) (e k : ℕ) :
    ((dy n e).add (dy 1 k)).toReal = (n : ℝ) / 2 ^ e + 2 ^ (-(k : ℤ)) := by
  rw [Dya.toReal_add, Dya.toReal, Dya.toReal]
  simp only [dy, Int.cast_one, one_div]
  rw [zpow_neg, zpow_natCast]


/-- **`Aquad` is in the ray area's `Ab`**, in plain `ℝ` numerals. -/
theorem Aquad_in_rayAb :
    ((415268074471237 : ℝ) / 2 ^ 40) - 2 ^ (-(20 : ℤ)) ≤ Aquad.re ∧
    Aquad.re ≤ ((415268074471237 : ℝ) / 2 ^ 40) + 2 ^ (-(20 : ℤ)) ∧
    ((624540193106589 : ℝ) / 2 ^ 40) - 2 ^ (-(20 : ℤ)) ≤ Aquad.im ∧
    Aquad.im ≤ ((624540193106589 : ℝ) / 2 ^ 40) + 2 ^ (-(20 : ℤ)) := by
  obtain ⟨h1, h2, h3, h4⟩ := Aquad_in_rayAbD
  have e1 := dy_sub_val 415268074471237 40 20
  have e2 := dy_add_val 415268074471237 40 20
  have e3 := dy_sub_val 624540193106589 40 20
  have e4 := dy_add_val 624540193106589 40 20
  simp only [dy] at e1 e2 e3 e4 h1 h2 h3 h4
  exact ⟨by linarith [e1, h1], by linarith [e2, h2],
         by linarith [e3, h3], by linarith [e4, h4]⟩

/-- **`z1` is in the ray area's `Zb`**, in plain `ℝ` numerals. -/
theorem z1_in_rayZb :
    ((-1293130773744 : ℝ) / 2 ^ 40) - 2 ^ (-(20 : ℤ)) ≤ z1.re ∧
    z1.re ≤ ((-1293130773744 : ℝ) / 2 ^ 40) + 2 ^ (-(20 : ℤ)) ∧
    ((195408601406 : ℝ) / 2 ^ 40) - 2 ^ (-(20 : ℤ)) ≤ z1.im ∧
    z1.im ≤ ((195408601406 : ℝ) / 2 ^ 40) + 2 ^ (-(20 : ℤ)) := by
  obtain ⟨h1, h2, h3, h4⟩ := z1_in_rayZbD
  have e1 := dy_sub_val (-1293130773744) 40 20
  have e2 := dy_add_val (-1293130773744) 40 20
  have e3 := dy_sub_val 195408601406 40 20
  have e4 := dy_add_val 195408601406 40 20
  simp only [dy] at e1 e2 e3 e4 h1 h2 h3 h4
  exact ⟨by linarith [e1, h1], by linarith [e2, h2],
         by linarith [e3, h3], by linarith [e4, h4]⟩

/-- **`cb` is in the ray area's `Xb`**, in plain `ℝ` numerals: `Re c_b` is exactly the centre
real part. -/
theorem cb_in_rayXb :
    cb.re = (-1293728561597 : ℝ) / 2 ^ 40 ∧
    ((195856658686 : ℝ) / 2 ^ 40) - 2 ^ (-(30 : ℤ)) ≤ cb.im ∧
    cb.im ≤ ((195856658686 : ℝ) / 2 ^ 40) + 2 ^ (-(30 : ℤ)) := by
  obtain ⟨h1, h2⟩ := cb_in_rayXbD
  have e1 := dy_sub_val 195856658686 40 30
  have e2 := dy_add_val 195856658686 40 30
  simp only [dy] at e1 e2 h1 h2
  exact ⟨cb_re, by linarith [e1, h1], by linarith [e2, h2]⟩

/-- **`‖c_b‖ ≤ 2`** (the far-field hypothesis of the ray chain). -/
theorem cb_norm_le_two : ‖cb‖ ≤ 2 := by
  obtain ⟨hre, hlo, hhi⟩ := cb_in_rayXb
  have h1 : |cb.re| ≤ 1.18 := by rw [hre]; norm_num
  have h2 : |cb.im| ≤ 0.19 := by
    rw [abs_le]
    constructor
    · have : (0.1781 : ℝ) ≤ ((195856658686 : ℝ) / 2 ^ 40) - 2 ^ (-(30 : ℤ)) := by norm_num
      linarith
    · have : ((195856658686 : ℝ) / 2 ^ 40) + 2 ^ (-(30 : ℤ)) ≤ (0.1782 : ℝ) := by norm_num
      linarith
  calc ‖cb‖ ≤ |cb.re| + |cb.im| := Complex.norm_le_abs_re_add_abs_im cb
    _ ≤ 1.18 + 0.19 := add_le_add h1 h2
    _ ≤ 2 := by norm_num

end

end Work.SeedCert
