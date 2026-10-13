import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.PSeries
import Submission.Work.FTS.PhiStar.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Expansion
import Submission.Work.FTS.PhiStar.FlatWAux.QmLopBound
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.Spaces.DthIter_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.FlatWAux.Fam2Diff

/-!
# `SummBounds` : absolute summability of the two mode series of the `Fam2` difference

Both series are compared with the convergent majorant `K * ((m:ℝ)+1)^{-2}`:

* the first summand is bounded by
  `|b_m| · λ_m^{-J} · |R_m(z)| · ((2^{18}+100)(2m+1)^{18}+2)`, and the three inputs
  `|b_m| ≤ Cd/λ_m` (the `√(2m+1)` is dropped, it is `≥ 1`), `|R_m(z)| ≤ Cr/λ_m` (the `k = 0`
  instance of `hrbJ`, after removing the factor `z/(z+1) ≤ 1`) and
  `D ≤ (2^{18}+102)(2m+1)^{18}` give
  `≤ Cd Cr (2^{18}+102) · (2m+1)^{18}/λ_m^{10} ≤ Cd Cr (2^{18}+102)/(2m+1)^2`
  since `λ_m ≥ (2m+1)^2`;
* the second summand is bounded by `|b_m| ≤ Cd/λ_m`, `|D^i(∂_θ Q_m)| ≤ Ci (2m+1)^{2i+4}`
  (`QmLopBound`, `i ≤ 6`) and the same eigenvalue comparison, giving
  `≤ Cd Ci/(2m+1)^{2}`.

The `m = 0` summand vanishes in both cases because `b_0 = 0`.
-/

/-! ## Elementary facts about the eigenvalue `λ_m = 2m(2m+5) = 4m²+10m` -/

private lemma lam_pos_of_one_le {m : ℕ} (hm : 1 ≤ m) :
    0 < Gegenbauer.lam m := by
  have hx : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  show (0 : ℝ) < 2 * (m : ℝ) * (2 * (m : ℝ) + 5)
  positivity

/-- `λ_m ≥ 0` (it is `2m(2m+5)`). -/
private lemma lam_nonneg (m : ℕ) : 0 ≤ Gegenbauer.lam m := by
  show (0 : ℝ) ≤ 2 * (m : ℝ) * (2 * (m : ℝ) + 5)
  positivity

/-- `(2m+1)² ≤ λ_m` for `m ≥ 1` (`4m²+4m+1 ≤ 4m²+10m`). -/
private lemma lam_sq_le_of_one_le {m : ℕ} (hm : 1 ≤ m) :
    (2 * (m : ℝ) + 1) ^ 2 ≤ Gegenbauer.lam m := by
  have hx : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  show (2 * (m : ℝ) + 1) ^ 2 ≤ 2 * (m : ℝ) * (2 * (m : ℝ) + 5)
  nlinarith

/-- The `√(2m+1)` in the coefficient decay hypothesis is discarded (it is `≥ 1`). -/
private lemma bmode_le_div_lam {ψ : ℝ → ℝ} {Cd : ℝ} (hCd : 0 < Cd)
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Series.bmode m ψ|
        ≤ Cd / (Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1))) :
    ∀ m : ℕ, 1 ≤ m → |Series.bmode m ψ| ≤ Cd / Gegenbauer.lam m := by
  intro m hm
  have hx : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hLpos : 0 < Gegenbauer.lam m := lam_pos_of_one_le hm
  have hs1 : (1 : ℝ) ≤ Real.sqrt (2 * (m : ℝ) + 1) := by
    rw [Real.one_le_sqrt]; linarith
  have hle : Gegenbauer.lam m ≤ Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1) :=
    le_mul_of_one_le_right (le_of_lt hLpos) hs1
  exact le_trans (hdec m hm) (div_le_div_of_nonneg_left (le_of_lt hCd) hLpos hle)

/-- `Σ_m ((m+1)²)^{-1}` converges. -/
private lemma summable_inv_sq_shift :
    Summable (fun m : ℕ => (((m : ℝ) + 1) ^ 2)⁻¹) := by
  have h1 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
  have h2 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
    (summable_nat_add_iff 1).mpr h1
  simpa using h2

/-- Removing the factor `(z+1)/z` of a bound: for `z > 0`, `|f z| ≤ |(z+1)/z · f z|`. -/
private lemma div_self_bound {f : ℝ → ℝ} {z Cr2 : ℝ} (hz : 0 < z)
    (h : |(z + 1) / z * f z| ≤ Cr2) : |f z| ≤ Cr2 := by
  have hz1 : (0 : ℝ) < z + 1 := by linarith
  have hkey : f z = ((z + 1) / z * f z) * (z / (z + 1)) := by
    field_simp
  rw [hkey, abs_mul]
  have hle1 : |z / (z + 1)| ≤ 1 := by
    rw [abs_of_pos (div_pos hz hz1), div_le_one hz1]
    linarith
  calc |(z + 1) / z * f z| * |z / (z + 1)|
      ≤ |(z + 1) / z * f z| * 1 := mul_le_mul_of_nonneg_left hle1 (abs_nonneg _)
    _ = |(z + 1) / z * f z| := by ring
    _ ≤ Cr2 := h

/-- The `k = 0` instance of `hrbJ` bounds the radial Green function itself. -/
private lemma radGreen_lam_le {α : ℝ} {z : ℝ} {m : ℕ} {Cr : ℝ} (_hm : 1 ≤ m) (hz : 0 < z)
    (hrb : ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Radial.radGreen α m
              (Ajit α J (VocabO.phiA α)) z'') z'|
        ≤ Cr / Gegenbauer.lam m) :
    |Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z| ≤ Cr / Gegenbauer.lam m := by
  refine div_self_bound (f := fun z' => Radial.radGreen α m (Ajit α J (VocabO.phiA α)) z')
    hz ?_
  simpa only [pow_zero, one_mul, iteratedDeriv_zero] using hrb 0 (by norm_num) z hz

/-- A constant series stays summable when `2m+1` is replaced by `m+1`. -/
private lemma div_shift_le {K : ℝ} (hK : 0 ≤ K) {m : ℕ} (hm : 1 ≤ m) :
    K / (2 * (m : ℝ) + 1) ^ 2 ≤ K * (((m : ℝ) + 1) ^ 2)⁻¹ := by
  have hx : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h1 : ((m : ℝ) + 1) ^ 2 ≤ (2 * (m : ℝ) + 1) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    linarith
  have h2 : ((2 * (m : ℝ) + 1) ^ 2)⁻¹ ≤ (((m : ℝ) + 1) ^ 2)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr h1
  rw [div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left h2 hK

/-! ## The two arithmetic cores -/

/-- Bound of the first summand: from `|b| ≤ Cd/Λ`, `|R| ≤ Cr/Λ`, `Λ ≥ L² ≥ 1`. -/
private lemma arith1 {b R Lam L K Cd Cr : ℝ}
    (hLam : 0 < Lam) (hL : 1 ≤ L) (hL2 : L ^ 2 ≤ Lam)
    (hCd : 0 ≤ Cd) (hCr : 0 ≤ Cr)
    (hb : |b| ≤ Cd / Lam) (hR : |R| ≤ Cr / Lam)
    (hK : Cd * Cr * (2 ^ 18 + 102) ≤ K) :
    |b| * (Lam⁻¹) ^ 8 * |R| * ((2 ^ 18 + 100) * L ^ 18 + 2) ≤ K / L ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hL2pos : 0 < L ^ 2 := pow_pos hLpos 2
  have hL16pos : 0 < L ^ 16 := pow_pos hLpos 16
  have hL18 : (1 : ℝ) ≤ L ^ 18 := one_le_pow₀ hL
  have hDle : (2 ^ 18 + 100) * L ^ 18 + 2 ≤ (2 ^ 18 + 102) * L ^ 18 := by nlinarith [hL18]
  have hinv : Lam⁻¹ ≤ (L ^ 2)⁻¹ := (inv_le_inv₀ hLam hL2pos).mpr hL2
  have hp : (Lam⁻¹) ^ 8 ≤ (L ^ 16)⁻¹ := by
    have h := pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt hLam)) hinv 8
    simpa only [inv_pow, show (L ^ 2) ^ 8 = L ^ 16 by ring] using h
  have h1 : |b| * (Lam⁻¹) ^ 8 ≤ (Cd / Lam) * (L ^ 16)⁻¹ :=
    mul_le_mul hb hp (pow_nonneg (inv_nonneg.mpr (le_of_lt hLam)) 8)
      (div_nonneg hCd (le_of_lt hLam))
  have h2 : |b| * (Lam⁻¹) ^ 8 * |R| ≤ (Cd / Lam) * (L ^ 16)⁻¹ * (Cr / Lam) :=
    mul_le_mul h1 hR (abs_nonneg _)
      (mul_nonneg (div_nonneg hCd (le_of_lt hLam)) (inv_nonneg.mpr (le_of_lt hL16pos)))
  have h4 : (0 : ℝ) ≤ (Cd / Lam) * (L ^ 16)⁻¹ * (Cr / Lam) := by positivity
  have hstep : |b| * (Lam⁻¹) ^ 8 * |R| * ((2 ^ 18 + 100) * L ^ 18 + 2)
      ≤ (Cd / Lam) * (L ^ 16)⁻¹ * (Cr / Lam) * ((2 ^ 18 + 102) * L ^ 18) :=
    mul_le_mul h2 hDle (by positivity) h4
  have hval : (Cd / Lam) * (L ^ 16)⁻¹ * (Cr / Lam) * ((2 ^ 18 + 102) * L ^ 18)
      = Cd * Cr * (2 ^ 18 + 102) * (L ^ 2 / Lam ^ 2) := by
    field_simp
  have hle2 : L ^ 2 / Lam ^ 2 ≤ 1 / L ^ 2 := by
    rw [div_le_div_iff₀ (pow_pos hLam 2) hL2pos]
    nlinarith [hL2]
  have hKnn : (0 : ℝ) ≤ Cd * Cr * (2 ^ 18 + 102) := by positivity
  calc |b| * (Lam⁻¹) ^ 8 * |R| * ((2 ^ 18 + 100) * L ^ 18 + 2)
      ≤ (Cd / Lam) * (L ^ 16)⁻¹ * (Cr / Lam) * ((2 ^ 18 + 102) * L ^ 18) := hstep
    _ = Cd * Cr * (2 ^ 18 + 102) * (L ^ 2 / Lam ^ 2) := hval
    _ ≤ Cd * Cr * (2 ^ 18 + 102) * (1 / L ^ 2) := mul_le_mul_of_nonneg_left hle2 hKnn
    _ = Cd * Cr * (2 ^ 18 + 102) / L ^ 2 := by ring
    _ ≤ K / L ^ 2 := div_le_div_of_nonneg_right hK (by positivity)

/-- Bound of the second summand: from `|b| ≤ Cd/Λ`, `|W| ≤ Ci L^{2i+4}` (`i ≤ 6`). -/
private lemma arith2 {b W Lam L K Cd Ci : ℝ} {i : ℕ}
    (hLam : 0 < Lam) (hL : 1 ≤ L) (hL2 : L ^ 2 ≤ Lam) (hi : i ≤ 6)
    (hCd : 0 ≤ Cd) (hCi : 0 ≤ Ci)
    (hb : |b| ≤ Cd / Lam) (hW : |W| ≤ Ci * L ^ (2 * i + 4))
    (hK : Cd * Ci ≤ K) :
    |b| * (Lam⁻¹) ^ 8 * |W| / Lam ≤ K / L ^ 2 := by
  have hLpos : 0 < L := lt_of_lt_of_le one_pos hL
  have hL2pos : 0 < L ^ 2 := pow_pos hLpos 2
  have hL16pos : 0 < L ^ 16 := pow_pos hLpos 16
  have hinv : Lam⁻¹ ≤ (L ^ 2)⁻¹ := (inv_le_inv₀ hLam hL2pos).mpr hL2
  have hp : (Lam⁻¹) ^ 8 ≤ (L ^ 16)⁻¹ := by
    have h := pow_le_pow_left₀ (inv_nonneg.mpr (le_of_lt hLam)) hinv 8
    simpa only [inv_pow, show (L ^ 2) ^ 8 = L ^ 16 by ring] using h
  have h1 : |b| * (Lam⁻¹) ^ 8 ≤ (Cd / Lam) * (L ^ 16)⁻¹ :=
    mul_le_mul hb hp (pow_nonneg (inv_nonneg.mpr (le_of_lt hLam)) 8)
      (div_nonneg hCd (le_of_lt hLam))
  have h2 : |b| * (Lam⁻¹) ^ 8 * |W| ≤ (Cd / Lam) * (L ^ 16)⁻¹ * (Ci * L ^ (2 * i + 4)) :=
    mul_le_mul h1 hW (abs_nonneg _)
      (mul_nonneg (div_nonneg hCd (le_of_lt hLam)) (inv_nonneg.mpr (le_of_lt hL16pos)))
  have h3 : |b| * (Lam⁻¹) ^ 8 * |W| / Lam
      ≤ (Cd / Lam) * (L ^ 16)⁻¹ * (Ci * L ^ (2 * i + 4)) / Lam :=
    div_le_div_of_nonneg_right h2 (le_of_lt hLam)
  have hval2 : (Cd / Lam) * (L ^ 16)⁻¹ * (Ci * L ^ (2 * i + 4)) / Lam
      = Cd * Ci * (L ^ (2 * i + 4) / (Lam ^ 2 * L ^ 16)) := by
    field_simp
  have hi16 : 2 * i + 4 ≤ 16 := by omega
  have hpow : L ^ (2 * i + 4) ≤ L ^ 16 := pow_le_pow_right₀ hL hi16
  have hLam2 : L ^ 4 ≤ Lam ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ L ^ 2) hL2 2
    rwa [show (L ^ 2) ^ 2 = L ^ 4 by ring] at h
  have hL4pos : 0 < L ^ 4 := by positivity
  have key : L ^ (2 * i + 4) / (Lam ^ 2 * L ^ 16) ≤ 1 / L ^ 2 := by
    have hA : L ^ (2 * i + 4) / (Lam ^ 2 * L ^ 16) ≤ L ^ 16 / (Lam ^ 2 * L ^ 16) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    have hB : L ^ 16 / (Lam ^ 2 * L ^ 16) = 1 / Lam ^ 2 := by
      field_simp
    have hC : 1 / Lam ^ 2 ≤ 1 / L ^ 4 := one_div_le_one_div_of_le hL4pos hLam2
    have hD : 1 / L ^ 4 ≤ 1 / L ^ 2 := by
      apply one_div_le_one_div_of_le hL2pos
      calc L ^ 2 = L ^ 2 * 1 := by ring
        _ ≤ L ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_left (one_le_pow₀ hL) (by positivity)
        _ = L ^ 4 := by ring
    linarith
  have hKnn : (0 : ℝ) ≤ Cd * Ci := by positivity
  calc |b| * (Lam⁻¹) ^ 8 * |W| / Lam
      ≤ (Cd / Lam) * (L ^ 16)⁻¹ * (Ci * L ^ (2 * i + 4)) / Lam := h3
    _ = Cd * Ci * (L ^ (2 * i + 4) / (Lam ^ 2 * L ^ 16)) := hval2
    _ ≤ Cd * Ci * (1 / L ^ 2) := mul_le_mul_of_nonneg_left key hKnn
    _ = Cd * Ci / L ^ 2 := by ring
    _ ≤ K / L ^ 2 := div_le_div_of_nonneg_right hK (by positivity)

theorem SummBounds {α : ℝ} {ψ : ℝ → ℝ} {z θ : ℝ} {i : ℕ} (hi : i ≤ 6) (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hb0 : Work.FTS.PhiStar.Series.bmode 0 ψ = 0)
    (hdec : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ|
        ≤ C / (Work.FTS.PhiStar.Gegenbauer.lam m * Real.sqrt (2 * (m : ℝ) + 1)))
    (hrbJ : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ k : ℕ, k ≤ 7 → ∀ z' : ℝ, 0 < z' →
      |(z' + 1) ^ k * iteratedDeriv k (fun z'' => (z'' + 1) / z''
          * Work.FTS.PhiStar.Radial.radGreen α m
              (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                (Work.FTS.VocabO.phiA α)) z'') z'|
        ≤ C / Work.FTS.PhiStar.Gegenbauer.lam m) :
    (Summable fun m : ℕ => |Work.FTS.PhiStar.Series.bmode m ψ| *
        ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ Work.FTS.PhiStar.FlatWAux.J *
        |Work.FTS.PhiStar.Radial.radGreen α m
          (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
            (Work.FTS.VocabO.phiA α)) z| *
        ((2 ^ (2 * 8 + 2) + 100) * (2 * (m : ℝ) + 1) ^ 18 + 2)) ∧
    (Summable fun m : ℕ => |Work.FTS.PhiStar.Series.bmode m ψ| *
        ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹) ^ Work.FTS.PhiStar.FlatWAux.J *
        |(Work.Spaces.Lop^[i]) (deriv (Work.FTS.PhiStar.FlatWAux.Qm m)) θ| /
        Work.FTS.PhiStar.Gegenbauer.lam m) := by
  obtain ⟨Cd, hCdpos, hdec⟩ := hdec
  obtain ⟨Cr, hCrpos, hrbJ⟩ := hrbJ
  obtain ⟨Ci, hCinn, hCi⟩ := QmLopBound
  set K : ℝ := (Cd + 1) * (Cr + 1) * (Ci i + 1) * (2 ^ 18 + 200) with hKdef
  have hCd1 : (0 : ℝ) < Cd + 1 := by linarith
  have hCr1 : (0 : ℝ) < Cr + 1 := by linarith
  have hCi1 : (0 : ℝ) < Ci i + 1 := by linarith [hCinn i]
  have hP18 : (0 : ℝ) < 2 ^ 18 + 200 := by norm_num
  have hprod : (0 : ℝ) < (Cd + 1) * (Cr + 1) * (Ci i + 1) :=
    mul_pos (mul_pos hCd1 hCr1) hCi1
  have hKnn : (0 : ℝ) ≤ K := by
    rw [hKdef]
    exact le_of_lt (mul_pos hprod hP18)
  have hK1 : Cd * Cr * (2 ^ 18 + 102) ≤ K := by
    rw [hKdef]
    have h1 : Cd * Cr ≤ (Cd + 1) * (Cr + 1) * (Ci i + 1) := by
      nlinarith [hCdpos, hCrpos, hCinn i]
    have h3 : (2 : ℝ) ^ 18 + 102 ≤ 2 ^ 18 + 200 := by norm_num
    calc Cd * Cr * (2 ^ 18 + 102)
        ≤ ((Cd + 1) * (Cr + 1) * (Ci i + 1)) * (2 ^ 18 + 200) :=
          mul_le_mul h1 h3 (by norm_num) (le_of_lt hprod)
      _ = (Cd + 1) * (Cr + 1) * (Ci i + 1) * (2 ^ 18 + 200) := by ring
  have hK2 : Cd * Ci i ≤ K := by
    rw [hKdef]
    have h1 : Cd * Ci i ≤ (Cd + 1) * (Cr + 1) * (Ci i + 1) := by
      nlinarith [hCdpos, hCrpos, hCinn i]
    have h3 : (1 : ℝ) ≤ 2 ^ 18 + 200 := by norm_num
    calc Cd * Ci i ≤ ((Cd + 1) * (Cr + 1) * (Ci i + 1)) * 1 := by
          rw [mul_one]; exact h1
      _ ≤ ((Cd + 1) * (Cr + 1) * (Ci i + 1)) * (2 ^ 18 + 200) :=
          mul_le_mul_of_nonneg_left h3 (le_of_lt hprod)
      _ = (Cd + 1) * (Cr + 1) * (Ci i + 1) * (2 ^ 18 + 200) := by ring
  have hsumg : Summable (fun m : ℕ => K * (((m : ℝ) + 1) ^ 2)⁻¹) :=
    summable_inv_sq_shift.mul_left K
  refine ⟨?_, ?_⟩
  · refine Summable.of_nonneg_of_le (f := fun m : ℕ => K * (((m : ℝ) + 1) ^ 2)⁻¹) ?_ ?_ hsumg
    · intro m
      have hpow : (0 : ℝ) ≤ ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹)
          ^ Work.FTS.PhiStar.FlatWAux.J :=
        pow_nonneg (inv_nonneg.mpr (lam_nonneg m)) _
      have hD : (0 : ℝ) ≤ (2 ^ (2 * 8 + 2) + 100) * (2 * (m : ℝ) + 1) ^ 18 + 2 := by
        positivity
      exact mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hpow) (abs_nonneg _)) hD
    · intro m
      by_cases hm : m = 0
      · subst hm
        rw [hb0]
        simp only [abs_zero, zero_mul, mul_zero, Nat.cast_zero, zero_add, one_pow, inv_one,
          mul_one]
        exact hKnn
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
        have hLpos : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := lam_pos_of_one_le hm1
        have hL1 : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
          have hx : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
          linarith
        have hLsq : (2 * (m : ℝ) + 1) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m :=
          lam_sq_le_of_one_le hm1
        have hb : |Work.FTS.PhiStar.Series.bmode m ψ|
            ≤ Cd / Work.FTS.PhiStar.Gegenbauer.lam m :=
          bmode_le_div_lam hCdpos hdec m hm1
        have hR : |Work.FTS.PhiStar.Radial.radGreen α m
            (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
              (Work.FTS.VocabO.phiA α)) z| ≤ Cr / Work.FTS.PhiStar.Gegenbauer.lam m :=
          radGreen_lam_le hm1 hz (fun k hk z' hz' => hrbJ m hm1 k hk z' hz')
        have hmain := arith1 (b := Work.FTS.PhiStar.Series.bmode m ψ)
          (R := Work.FTS.PhiStar.Radial.radGreen α m
            (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
              (Work.FTS.VocabO.phiA α)) z)
          (Lam := Work.FTS.PhiStar.Gegenbauer.lam m) (L := 2 * (m : ℝ) + 1)
          (K := K) (Cd := Cd) (Cr := Cr) hLpos hL1 hLsq (le_of_lt hCdpos) (le_of_lt hCrpos)
          hb hR hK1
        exact le_trans hmain (div_shift_le hKnn hm1)
  · refine Summable.of_nonneg_of_le (f := fun m : ℕ => K * (((m : ℝ) + 1) ^ 2)⁻¹) ?_ ?_ hsumg
    · intro m
      have hpow : (0 : ℝ) ≤ ((Work.FTS.PhiStar.Gegenbauer.lam m)⁻¹)
          ^ Work.FTS.PhiStar.FlatWAux.J :=
        pow_nonneg (inv_nonneg.mpr (lam_nonneg m)) _
      exact div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) hpow) (abs_nonneg _))
        (lam_nonneg m)
    · intro m
      by_cases hm : m = 0
      · subst hm
        rw [hb0]
        simp only [abs_zero, zero_mul, zero_div, Nat.cast_zero, zero_add, one_pow,
          inv_one, mul_one]
        exact hKnn
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
        have hLpos : 0 < Work.FTS.PhiStar.Gegenbauer.lam m := lam_pos_of_one_le hm1
        have hL1 : (1 : ℝ) ≤ 2 * (m : ℝ) + 1 := by
          have hx : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
          linarith
        have hLsq : (2 * (m : ℝ) + 1) ^ 2 ≤ Work.FTS.PhiStar.Gegenbauer.lam m :=
          lam_sq_le_of_one_le hm1
        have hb : |Work.FTS.PhiStar.Series.bmode m ψ|
            ≤ Cd / Work.FTS.PhiStar.Gegenbauer.lam m :=
          bmode_le_div_lam hCdpos hdec m hm1
        have hW : |(Work.Spaces.Lop^[i]) (deriv (Work.FTS.PhiStar.FlatWAux.Qm m)) θ|
            ≤ Ci i * (2 * (m : ℝ) + 1) ^ (2 * i + 4) := hCi m hm1 i hi θ hθ
        have hmain := arith2 (b := Work.FTS.PhiStar.Series.bmode m ψ)
          (W := (Work.Spaces.Lop^[i]) (deriv (Work.FTS.PhiStar.FlatWAux.Qm m)) θ)
          (Lam := Work.FTS.PhiStar.Gegenbauer.lam m) (L := 2 * (m : ℝ) + 1)
          (K := K) (Cd := Cd) (Ci := Ci i) (i := i)
          hLpos hL1 hLsq hi (le_of_lt hCdpos) (hCinn i) hb hW hK2
        exact le_trans hmain (div_shift_le hKnn hm1)

end Work.FTS.PhiStar.FlatWAux.Fam2Diff
