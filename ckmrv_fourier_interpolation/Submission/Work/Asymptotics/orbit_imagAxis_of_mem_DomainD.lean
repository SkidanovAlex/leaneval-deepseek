import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Kernels.All

set_option maxHeartbeats 1600000

namespace Work.Asymptotics

open scoped MatrixGroups
open UpperHalfPlane

/-- For integers `b d e f` with `e*d - b*f = 1`, the products `b*e` and `d*f` have the
same sign.  Equivalently `(b*e)*(d*f) ≥ 0`. -/
private lemma sign_det {b d e f : ℤ} (h : e * d - b * f = 1) : 0 ≤ (b * e) * (d * f) := by
  have hid : (b * e) * (d * f) = (d * e) * (d * e - 1) := by
    linear_combination (-(d * e)) * h
  rw [hid]
  rcases le_or_gt (d * e) 0 with hle | hlt
  · nlinarith [sq_nonneg (d * e)]
  · nlinarith [sq_nonneg (d * e - 1)]

/-- Elementary integrality: two nonnegative integers summing to one are `(0,1)` or `(1,0)`. -/
private lemma int_two_cases {p q : ℤ} (hp : 0 ≤ p) (hq : 0 ≤ q) (h : p + q = 1) :
    (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 0) := by
  omega

private lemma eq_one_of_mul_eq_one_left {a b : ℤ} (ha : 0 ≤ a) (h : a * b = 1) : a = 1 := by
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact h1
  · omega

private lemma eq_one_of_mul_eq_one_right {a b : ℤ} (hb : 0 ≤ b) (h : a * b = 1) : b = 1 := by
  rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨_, h2⟩ | ⟨_, h2⟩
  · exact h2
  · omega

private lemma eq_zero_of_mul_eq_zero_left {a b : ℤ} (hb : b ≠ 0) (h : a * b = 0) : a = 0 := by
  rcases mul_eq_zero.mp h with h1 | h1
  · exact h1
  · exact absurd h1 hb

/-- The integrality heart of the argument.  `B, D, E = B + α, F = D + β` are nonnegative
integers, `w > 0`, the determinant condition `(B*β - D*α)^2 = 1` holds, and the two linear
inequalities `E*α + F*β*w > 0`, `B*E + D*F*w > 0` hold.  Then `B*α + D*β*w ≥ 0`. -/
private lemma key_combo (B D α β : ℤ) (w : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hE : 0 ≤ B + α) (hF : 0 ≤ D + β) (hw : 0 < w)
    (hdet : (B * β - D * α) ^ 2 = 1)
    (h1 : 0 < ((B + α : ℤ):ℝ) * (α:ℝ) + ((D + β : ℤ):ℝ) * (β:ℝ) * w)
    (h2 : 0 < (B:ℝ) * ((B + α : ℤ):ℝ) + (D:ℝ) * ((D + β : ℤ):ℝ) * w) :
    0 ≤ (B:ℝ) * (α:ℝ) + (D:ℝ) * (β:ℝ) * w := by
  have hBR : (0:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB
  have hDR : (0:ℝ) ≤ (D:ℝ) := by exact_mod_cast hD
  have hER : (0:ℝ) ≤ ((B + α : ℤ):ℝ) := by exact_mod_cast hE
  have hFR : (0:ℝ) ≤ ((D + β : ℤ):ℝ) := by exact_mod_cast hF
  have hdetZ : B * β - D * α = 1 ∨ B * β - D * α = -1 := by
    have h := hdet
    rw [sq] at h
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' h with ⟨h1', _⟩ | ⟨h1', _⟩
    · exact Or.inl h1'
    · exact Or.inr h1'
  rcases le_or_gt (0:ℤ) α with hα | hα
  · rcases le_or_gt (0:ℤ) β with hβ | hβ
    · -- α ≥ 0, β ≥ 0
      have hαR : (0:ℝ) ≤ (α:ℝ) := by exact_mod_cast hα
      have hβR : (0:ℝ) ≤ (β:ℝ) := by exact_mod_cast hβ
      linarith [mul_nonneg hBR hαR, mul_nonneg (mul_nonneg hDR hβR) hw.le]
    · -- α ≥ 0, β ≤ -1
      have hαR : (0:ℝ) ≤ (α:ℝ) := by exact_mod_cast hα
      have hβR : (β:ℝ) ≤ 0 := by exact_mod_cast (le_of_lt hβ)
      have hBβ : (B:ℝ) * (β:ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hBR hβR
      have hDα : (0:ℝ) ≤ (D:ℝ) * (α:ℝ) := mul_nonneg hDR hαR
      have hkey : (B:ℝ) * (β:ℝ) - (D:ℝ) * (α:ℝ) = -1 := by
        rcases hdetZ with hh | hh
        · exfalso
          have hhR : (B:ℝ) * (β:ℝ) - (D:ℝ) * (α:ℝ) = 1 := by exact_mod_cast hh
          linarith
        · exact_mod_cast hh
      have hsumZ : D * α + B * (-β) = 1 := by
        have h : (D:ℝ) * (α:ℝ) + (B:ℝ) * ((-β : ℤ) : ℝ) = 1 := by
          push_cast
          linarith
        exact_mod_cast h
      have hp : 0 ≤ D * α := mul_nonneg hD hα
      have hq : 0 ≤ B * (-β) := mul_nonneg hB (by omega)
      rcases int_two_cases hp hq hsumZ with ⟨hp0, hq1⟩ | ⟨hp1, hq0⟩
      · -- D*α = 0, B*(-β) = 1
        have hnb : -β = 1 := eq_one_of_mul_eq_one_right (by omega : (0:ℤ) ≤ -β) hq1
        have hβ1 : β = -1 := by omega
        have hα0 : α = 0 := by
          rcases mul_eq_zero.mp hp0 with h | h
          · exfalso; omega
          · exact h
        have hDmR : (0:ℝ) ≤ (D:ℝ) - 1 := by
          have hDmZ : (0:ℤ) ≤ D - 1 := by omega
          exact_mod_cast hDmZ
        have h1v : ((B + α : ℤ):ℝ) * (α:ℝ) + ((D + β : ℤ):ℝ) * (β:ℝ) * w
            = -((D:ℝ) - 1) * w := by
          rw [hα0, hβ1]; push_cast; ring
        rw [h1v] at h1
        nlinarith [hw, hDmR]
      · -- D*α = 1, B*(-β) = 0
        have hDv : D = 1 := eq_one_of_mul_eq_one_left hD hp1
        have hα1 : α = 1 := eq_one_of_mul_eq_one_right hα hp1
        have hnbne : (-β : ℤ) ≠ 0 := by omega
        have hB0 : B = 0 := eq_zero_of_mul_eq_zero_left hnbne hq0
        have hβ1 : β = -1 := by omega
        have h2v : (B:ℝ) * ((B + α : ℤ):ℝ) + (D:ℝ) * ((D + β : ℤ):ℝ) * w = 0 := by
          rw [hB0, hα1, hDv, hβ1]; push_cast; ring
        rw [h2v] at h2
        exact absurd h2 (lt_irrefl 0)
  · rcases le_or_gt (0:ℤ) β with hβ | hβ
    · -- α ≤ -1, β ≥ 0
      have hβR : (0:ℝ) ≤ (β:ℝ) := by exact_mod_cast hβ
      have hαR : (α:ℝ) ≤ 0 := by exact_mod_cast (le_of_lt hα)
      have hBβ : (0:ℝ) ≤ (B:ℝ) * (β:ℝ) := mul_nonneg hBR hβR
      have hDα : (D:ℝ) * (α:ℝ) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hDR hαR
      have hkey : (B:ℝ) * (β:ℝ) - (D:ℝ) * (α:ℝ) = 1 := by
        rcases hdetZ with hh | hh
        · exact_mod_cast hh
        · exfalso
          have hhR : (B:ℝ) * (β:ℝ) - (D:ℝ) * (α:ℝ) = -1 := by exact_mod_cast hh
          linarith
      have hsumZ : D * (-α) + B * β = 1 := by
        have h : (D:ℝ) * ((-α : ℤ) : ℝ) + (B:ℝ) * (β:ℝ) = 1 := by
          push_cast
          linarith
        exact_mod_cast h
      have hp : 0 ≤ D * (-α) := mul_nonneg hD (by omega)
      have hq : 0 ≤ B * β := mul_nonneg hB hβ
      rcases int_two_cases hp hq hsumZ with ⟨hp0, hq1⟩ | ⟨hp1, hq0⟩
      · -- D*(-α) = 0, B*β = 1
        have hB1 : B = 1 := eq_one_of_mul_eq_one_left hB hq1
        have hb1 : β = 1 := eq_one_of_mul_eq_one_right hβ hq1
        have hD0 : D = 0 := eq_zero_of_mul_eq_zero_left (by omega : (-α : ℤ) ≠ 0) hp0
        have h2v : (B:ℝ) * ((B + α : ℤ):ℝ) + (D:ℝ) * ((D + β : ℤ):ℝ) * w = 1 + (α:ℝ) := by
          rw [hB1, hD0, hb1]; push_cast; ring
        rw [h2v] at h2
        have hαl : (α:ℝ) ≤ -1 := by
          have h : α ≤ -1 := by omega
          exact_mod_cast h
        linarith
      · -- D*(-α) = 1, B*β = 0
        have hDv : D = 1 := eq_one_of_mul_eq_one_left hD hp1
        have hna1 : -α = 1 := eq_one_of_mul_eq_one_right (by omega : (0:ℤ) ≤ -α) hp1
        have hα1 : α = -1 := by omega
        rcases mul_eq_zero.mp hq0 with hB0 | hβ0
        · exfalso; omega
        · have h1v : ((B + α : ℤ):ℝ) * (α:ℝ) + ((D + β : ℤ):ℝ) * (β:ℝ) * w = 1 - (B:ℝ) := by
            rw [hβ0, hα1, hDv]; push_cast; ring
          rw [h1v] at h1
          have hBge : (1:ℝ) ≤ (B:ℝ) := by
            have h : (1:ℤ) ≤ B := by omega
            exact_mod_cast h
          linarith
    · -- α ≤ -1, β ≤ -1
      have hαR : (α:ℝ) ≤ 0 := by exact_mod_cast (le_of_lt hα)
      have hβR : (β:ℝ) ≤ 0 := by exact_mod_cast (le_of_lt hβ)
      have h1a : ((B + α : ℤ):ℝ) * (α:ℝ) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hER hαR
      have h1b : ((D + β : ℤ):ℝ) * (β:ℝ) * w ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hFR hβR) hw.le
      have hlt : ((B + α : ℤ):ℝ) * (α:ℝ) + ((D + β : ℤ):ℝ) * (β:ℝ) * w < 0 := by
        rcases lt_or_eq_of_le h1a with h | h
        · linarith
        · rcases lt_or_eq_of_le h1b with h' | h'
          · linarith
          · exfalso
            have hE0 : (B + α : ℤ) = 0 := by
              rcases mul_eq_zero.mp h with hh | hh
              · exact_mod_cast hh
              · have hh2 : α = 0 := by exact_mod_cast hh
                omega
            have hF0 : (D + β : ℤ) = 0 := by
              rcases mul_eq_zero.mp h' with hh | hh
              · rcases mul_eq_zero.mp hh with hh1 | hh1
                · exact_mod_cast hh1
                · have hh2 : β = 0 := by exact_mod_cast hh1
                  omega
              · exact absurd hh (ne_of_gt hw)
            have hBeq : B = -α := by omega
            have hDeq : D = -β := by omega
            have hz : B * β - D * α = 0 := by rw [hBeq, hDeq]; ring
            rcases hdetZ with hd | hd <;> omega
      linarith [h1, hlt]

/-- Restatement of `key_combo` with the endpoint parameters `E, F` (with `α = E - B`,
`β = F - D`) exposed. -/
private lemma key_combo' (B D E F : ℤ) (w : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hE : 0 ≤ E) (hF : 0 ≤ F) (hw : 0 < w)
    (hdet : (B * (F - D) - D * (E - B)) ^ 2 = 1)
    (h1 : 0 < (E:ℝ) * ((E:ℝ) - (B:ℝ)) + (F:ℝ) * ((F:ℝ) - (D:ℝ)) * w)
    (h2 : 0 < (B:ℝ) * (E:ℝ) + (D:ℝ) * (F:ℝ) * w) :
    0 ≤ (B:ℝ) * ((E:ℝ) - (B:ℝ)) + (D:ℝ) * ((F:ℝ) - (D:ℝ)) * w := by
  have h1a : B + (E - B) = E := by ring
  have h1b : D + (F - D) = F := by ring
  have hdet' : (B * (F - D) - D * (E - B)) ^ 2 = 1 := hdet
  have hkey := key_combo B D (E - B) (F - D) w hB hD
    (by rw [h1a]; exact hE) (by rw [h1b]; exact hF) hw hdet'
    (by rw [h1a, h1b]; push_cast; exact h1)
    (by
      push_cast
      have hh : (B:ℝ) * ((B:ℝ) + ((E:ℝ) - (B:ℝ))) + (D:ℝ) * ((D:ℝ) + ((F:ℝ) - (D:ℝ))) * w
          = (B:ℝ) * (E:ℝ) + (D:ℝ) * (F:ℝ) * w := by ring
      rw [hh]; exact h2)
  push_cast at hkey ⊢
  exact hkey

/-- **The core algebraic statement.**  If `a d - b c = 1`, `w > 0` and both `a^2 + c^2 w` and
`b^2 + d^2 w` exceed `|a b + c d w|`, then `a b + c d w = 0`. -/
private lemma core_le (a b c d : ℤ) (w : ℝ) (hw : 0 < w)
    (hdet : (a:ℝ)*(d:ℝ) - (b:ℝ)*(c:ℝ) = 1)
    (hA : (a:ℝ)^2 + (c:ℝ)^2*w > |(a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w|)
    (hB : (b:ℝ)^2 + (d:ℝ)^2*w > |(a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w|) :
    (a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w ≤ 0 := by
  have hdetZ : a*d - b*c = 1 := by exact_mod_cast hdet
  set e : ℤ := a - b with he
  set f : ℤ := c - d with hf
  have hdet' : e*d - b*f = 1 := by rw [he, hf]; linear_combination hdetZ
  have he' : (e:ℝ) = (a:ℝ) - (b:ℝ) := by rw [he]; push_cast; ring
  have hf' : (f:ℝ) = (c:ℝ) - (d:ℝ) := by rw [hf]; push_cast; ring
  have hsign : (0:ℝ) ≤ ((b:ℝ)*(e:ℝ)) * ((d:ℝ)*(f:ℝ)) := by
    have h := sign_det hdet'
    exact_mod_cast h
  have ht : (a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w
      = ((b:ℝ)^2 + (d:ℝ)^2*w) - (-((b:ℝ)*(e:ℝ) + (d:ℝ)*(f:ℝ)*w)) := by
    rw [he', hf']; ring
  have hAeq : ((a:ℝ)^2 + (c:ℝ)^2*w) - ((a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w)
      = ((e:ℝ)^2 + (f:ℝ)^2*w) - (-((b:ℝ)*(e:ℝ) + (d:ℝ)*(f:ℝ)*w)) := by
    rw [he', hf']; ring
  have hBpos : 0 < -((b:ℝ)*(e:ℝ) + (d:ℝ)*(f:ℝ)*w) := by
    have habs : (a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w ≤ |(a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w| :=
      le_abs_self _
    linarith [hB, ht, habs]
  have hAlt : -((b:ℝ)*(e:ℝ) + (d:ℝ)*(f:ℝ)*w) < (e:ℝ)^2 + (f:ℝ)^2*w := by
    have habs : (a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w ≤ |(a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w| :=
      le_abs_self _
    linarith [hA, hAeq, habs]
  have hbe : (b:ℝ)*(e:ℝ) ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    have hdfw : (d:ℝ)*(f:ℝ)*w < 0 := by linarith [hBpos, hcon]
    have hdfx : (d:ℝ)*(f:ℝ) < 0 := by
      by_contra h2
      rw [not_lt] at h2
      have h3 : 0 ≤ (d:ℝ)*(f:ℝ)*w := mul_nonneg h2 hw.le
      linarith
    have h4 : ((b:ℝ)*(e:ℝ)) * ((d:ℝ)*(f:ℝ)) < 0 := mul_neg_of_pos_of_neg hcon hdfx
    linarith [hsign]
  have hdf : (d:ℝ)*(f:ℝ) ≤ 0 := by
    by_contra hcon
    rw [not_le] at hcon
    have hdfwpos : 0 < (d:ℝ)*(f:ℝ)*w := mul_pos hcon hw
    have hbex : (b:ℝ)*(e:ℝ) < 0 := by linarith [hBpos, hdfwpos]
    have h4 : ((b:ℝ)*(e:ℝ)) * ((d:ℝ)*(f:ℝ)) < 0 := mul_neg_of_neg_of_pos hbex hcon
    linarith [hsign]
  have hb2 : (((|b|:ℤ):ℝ))^2 = (b:ℝ)^2 := by rw [Int.cast_abs, sq_abs]
  have hd2 : (((|d|:ℤ):ℝ))^2 = (d:ℝ)^2 := by rw [Int.cast_abs, sq_abs]
  have he2 : (((|e|:ℤ):ℝ))^2 = (e:ℝ)^2 := by rw [Int.cast_abs, sq_abs]
  have hf2 : (((|f|:ℤ):ℝ))^2 = (f:ℝ)^2 := by rw [Int.cast_abs, sq_abs]
  have hbe'' : ((|b|:ℤ):ℝ) * ((|e|:ℤ):ℝ) = -((b:ℝ)*(e:ℝ)) := by
    rw [Int.cast_abs, Int.cast_abs, ← abs_mul, abs_of_nonpos hbe]
  have hdf'' : ((|d|:ℤ):ℝ) * ((|f|:ℤ):ℝ) = -((d:ℝ)*(f:ℝ)) := by
    rw [Int.cast_abs, Int.cast_abs, ← abs_mul, abs_of_nonpos hdf]
  have hBF0 : (((|b|:ℤ)*(|f|:ℤ) - (|d|:ℤ)*(|e|:ℤ) : ℤ) : ℝ)^2 = 1 := by
    have hbe3 : |(b:ℝ)| * |(e:ℝ)| = -((b:ℝ)*(e:ℝ)) := by
      rw [← abs_mul, abs_of_nonpos hbe]
    have hdf3 : |(d:ℝ)| * |(f:ℝ)| = -((d:ℝ)*(f:ℝ)) := by
      rw [← abs_mul, abs_of_nonpos hdf]
    have hbs : |(b:ℝ)|^2 = (b:ℝ)^2 := sq_abs _
    have hds : |(d:ℝ)|^2 = (d:ℝ)^2 := sq_abs _
    have hes : |(e:ℝ)|^2 = (e:ℝ)^2 := sq_abs _
    have hfs : |(f:ℝ)|^2 = (f:ℝ)^2 := sq_abs _
    have hcross : (|(b:ℝ)| * |(f:ℝ)|) * (|(d:ℝ)| * |(e:ℝ)|) = (b:ℝ)*(d:ℝ)*(e:ℝ)*(f:ℝ) := by
      rw [show (|(b:ℝ)| * |(f:ℝ)|) * (|(d:ℝ)| * |(e:ℝ)|)
          = (|(b:ℝ)| * |(e:ℝ)|) * (|(d:ℝ)| * |(f:ℝ)|) from by ring, hbe3, hdf3]
      ring
    have h2 : (b:ℝ)*(f:ℝ) - (d:ℝ)*(e:ℝ) = -1 := by
      have h : b*f - d*e = -1 := by linear_combination (-1) * hdet'
      exact_mod_cast h
    push_cast
    calc (|(b:ℝ)| * |(f:ℝ)| - |(d:ℝ)| * |(e:ℝ)|)^2
        = (|(b:ℝ)| * |(f:ℝ)|)^2
            - 2 * ((|(b:ℝ)| * |(f:ℝ)|) * (|(d:ℝ)| * |(e:ℝ)|))
            + (|(d:ℝ)| * |(e:ℝ)|)^2 := by ring
      _ = |(b:ℝ)|^2 * |(f:ℝ)|^2
            - 2 * ((|(b:ℝ)| * |(f:ℝ)|) * (|(d:ℝ)| * |(e:ℝ)|))
            + |(d:ℝ)|^2 * |(e:ℝ)|^2 := by rw [mul_pow, mul_pow]
      _ = (b:ℝ)^2 * (f:ℝ)^2 - 2 * ((b:ℝ)*(d:ℝ)*(e:ℝ)*(f:ℝ)) + (d:ℝ)^2*(e:ℝ)^2 := by
        rw [hbs, hds, hes, hfs, hcross]
      _ = ((b:ℝ)*(f:ℝ) - (d:ℝ)*(e:ℝ))^2 := by ring
      _ = 1 := by rw [h2]; ring
  have hBFZ : ((|b|:ℤ) * ((|f|:ℤ) - (|d|:ℤ)) - (|d|:ℤ) * ((|e|:ℤ) - (|b|:ℤ)))^2 = 1 := by
    have h1 : (((|b|:ℤ) * ((|f|:ℤ) - (|d|:ℤ)) - (|d|:ℤ) * ((|e|:ℤ) - (|b|:ℤ)) : ℤ) : ℝ)^2 = 1 := by
      have heq : (((|b|:ℤ) * ((|f|:ℤ) - (|d|:ℤ)) - (|d|:ℤ) * ((|e|:ℤ) - (|b|:ℤ)) : ℤ) : ℝ)
          = (((|b|:ℤ)*(|f|:ℤ) - (|d|:ℤ)*(|e|:ℤ) : ℤ) : ℝ) := by push_cast; ring
      rw [heq]; exact hBF0
    exact_mod_cast h1
  have hhh : -((b:ℝ)*(e:ℝ) + (d:ℝ)*(f:ℝ)*w)
      = ((|b|:ℤ):ℝ) * ((|e|:ℤ):ℝ) + ((|d|:ℤ):ℝ) * ((|f|:ℤ):ℝ) * w := by
    rw [hbe'', hdf'']; ring
  have h1 : (0:ℝ) < ((|e|:ℤ):ℝ) * (((|e|:ℤ):ℝ) - ((|b|:ℤ):ℝ))
      + ((|f|:ℤ):ℝ) * (((|f|:ℤ):ℝ) - ((|d|:ℤ):ℝ)) * w := by
    have hid : ((|e|:ℤ):ℝ) * (((|e|:ℤ):ℝ) - ((|b|:ℤ):ℝ))
        + ((|f|:ℤ):ℝ) * (((|f|:ℤ):ℝ) - ((|d|:ℤ):ℝ)) * w
        = ((e:ℝ)^2 + (f:ℝ)^2*w) - (-((b:ℝ)*(e:ℝ) + (d:ℝ)*(f:ℝ)*w)) := by
      nlinarith [he2, hf2, hbe'', hdf'']
    linarith [hAlt, hid]
  have h2 : (0:ℝ) < ((|b|:ℤ):ℝ) * ((|e|:ℤ):ℝ) + ((|d|:ℤ):ℝ) * ((|f|:ℤ):ℝ) * w := by
    rw [← hhh]; exact hBpos
  have hkey := key_combo' (|b|:ℤ) (|d|:ℤ) (|e|:ℤ) (|f|:ℤ) w
      (abs_nonneg b) (abs_nonneg d) (abs_nonneg e) (abs_nonneg f) hw hBFZ h1 h2
  have ht2 : (a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w
      = -((((|b|:ℤ):ℝ)) * (((|e|:ℤ):ℝ) - ((|b|:ℤ):ℝ))
          + (((|d|:ℤ):ℝ)) * (((|f|:ℤ):ℝ) - ((|d|:ℤ):ℝ)) * w) := by
    rw [ht, hhh, hb2.symm, hd2.symm]
    ring
  rw [ht2]
  linarith [hkey]

/-- The symmetric companion of `core_le`, via the reflection `(b,c) ↦ (-b,-c)`. -/
private lemma core (a b c d : ℤ) (w : ℝ) (hw : 0 < w)
    (hdet : (a:ℝ)*(d:ℝ) - (b:ℝ)*(c:ℝ) = 1)
    (hA : (a:ℝ)^2 + (c:ℝ)^2*w > |(a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w|)
    (hB : (b:ℝ)^2 + (d:ℝ)^2*w > |(a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w|) :
    (a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w = 0 := by
  have hle : (a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w ≤ 0 := core_le a b c d w hw hdet hA hB
  have hge : 0 ≤ (a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w := by
    have hdet2 : (a:ℝ)*(d:ℝ) - ((-b : ℤ):ℝ) * ((-c : ℤ):ℝ) = 1 := by
      push_cast; linarith [hdet]
    have ht2 : (a:ℝ) * ((-b : ℤ):ℝ) + ((-c : ℤ):ℝ) * (d:ℝ)*w
        = -((a:ℝ)*(b:ℝ) + (c:ℝ)*(d:ℝ)*w) := by push_cast; ring
    have hA2 : (a:ℝ)^2 + ((-c : ℤ):ℝ)^2*w
        > |(a:ℝ) * ((-b : ℤ):ℝ) + ((-c : ℤ):ℝ) * (d:ℝ)*w| := by
      rw [ht2, abs_neg]
      simpa using hA
    have hB2 : ((-b : ℤ):ℝ)^2 + (d:ℝ)^2*w
        > |(a:ℝ) * ((-b : ℤ):ℝ) + ((-c : ℤ):ℝ) * (d:ℝ)*w| := by
      rw [ht2, abs_neg]
      simpa using hB
    have hle2 := core_le a (-b) (-c) d w hw hdet2 hA2 hB2
    push_cast at hle2
    linarith
  linarith

theorem orbit_imagAxis_of_mem_DomainD (τ : UpperHalfPlane) (hτ : τ ∈ Work.Asymptotics.DomainD)
    (γ : SL(2,ℤ)) (h : ((γ • τ : UpperHalfPlane) : ℂ).re = 0) : τ.re = 0 := by
  set w' : ℍ := γ • τ with hw'
  have hre : (w' : ℂ).re = 0 := by rw [hw']; exact h
  have hu : 0 < w'.im := w'.im_pos
  have hcoe : (w' : ℂ) = (w'.im : ℂ) * Complex.I := by
    have h1 := Complex.re_add_im (w' : ℂ)
    rw [hre, UpperHalfPlane.coe_im] at h1
    simp only [Complex.ofReal_zero, zero_add] at h1
    exact h1.symm
  have hcast : ∀ m : ℤ, ((algebraMap ℤ ℝ m : ℂ)) = (m : ℂ) := fun m => by simp
  have hsl : (w' : ℂ) = (((γ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℤ) : ℂ)) /
      (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) := by
    rw [hw', UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [hcast]
  have hcd : (![((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)] : Fin 2 → ℝ) ≠ 0 := by
    intro hh
    have h10 : γ 1 0 = 0 := by
      have h' : ((γ 1 0 : ℤ) : ℝ) = 0 := by simpa using congrFun hh 0
      exact_mod_cast h'
    have h11 : γ 1 1 = 0 := by
      have h' : ((γ 1 1 : ℤ) : ℝ) = 0 := by simpa using congrFun hh 1
      exact_mod_cast h'
    have hd := γ.2
    rw [Matrix.det_fin_two, h10, h11] at hd
    norm_num at hd
  have hden : (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ≠ 0 :=
    UpperHalfPlane.linear_ne_zero τ hcd
  have heq : (((γ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℤ) : ℂ))
      = ((w'.im : ℂ) * Complex.I) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) := by
    have h2 := hsl
    rw [hcoe] at h2
    exact (div_eq_iff hden).mp h2.symm
  have hz : (τ : ℂ) = (τ.re : ℂ) + (τ.im : ℂ) * Complex.I := by
    have h1 := Complex.re_add_im (τ : ℂ)
    rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h1
    exact h1.symm
  rw [hz] at heq
  have hre2 := congrArg Complex.re heq
  have him2 := congrArg Complex.im heq
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.intCast_re, Complex.intCast_im, Complex.I_re, Complex.I_im,
    mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero, zero_sub, neg_mul, neg_neg,
    mul_neg, Complex.zero_re, Complex.zero_im, Complex.ofReal_zero] at hre2 him2
  ring_nf at hre2 him2
  set A : ℝ := ((γ 0 0 : ℤ) : ℝ) with hAdef
  set B : ℝ := ((γ 0 1 : ℤ) : ℝ) with hBdef
  set C : ℝ := ((γ 1 0 : ℤ) : ℝ) with hCdef
  set Dd : ℝ := ((γ 1 1 : ℤ) : ℝ) with hDdef
  set u : ℝ := w'.im with hudef
  have hsys1 : A * τ.re + B = -(u * C * τ.im) := hre2
  have hsys2 : A * τ.im = τ.re * u * C + u * Dd := him2
  have hdetZ : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have hd := γ.2
    rw [Matrix.det_fin_two] at hd
    exact hd
  have hdetR : A * Dd - B * C = 1 := by
    rw [hAdef, hBdef, hCdef, hDdef]
    exact_mod_cast hdetZ
  have hdetZ' : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ)
      - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
    exact_mod_cast hdetZ
  set t : ℝ := A * B + C * Dd * u^2 with htdef
  set D : ℝ := A^2 + C^2 * u^2 with hDdef
  have hposden : 0 < D := by
    have hne : ((γ 0 0 : ℤ) : ℝ) ≠ 0 ∨ ((γ 1 0 : ℤ) : ℝ) ≠ 0 := by
      by_contra hcon
      simp only [not_or, not_not] at hcon
      obtain ⟨h0, h1⟩ := hcon
      have h0' : γ 0 0 = 0 := by exact_mod_cast h0
      have h1' : γ 1 0 = 0 := by exact_mod_cast h1
      rw [h0', h1'] at hdetZ
      norm_num at hdetZ
    rw [hDdef, hAdef, hCdef]
    rcases hne with h0 | h1
    · have h2 : 0 < (((γ 0 0 : ℤ) : ℝ))^2 := by rw [pow_two]; exact mul_self_pos.mpr h0
      nlinarith [sq_nonneg (((γ 1 0 : ℤ) : ℝ)), sq_nonneg w'.im]
    · have h2 : 0 < (((γ 1 0 : ℤ) : ℝ))^2 := by rw [pow_two]; exact mul_self_pos.mpr h1
      have h4 : 0 < (((γ 1 0 : ℤ) : ℝ))^2 * w'.im^2 := mul_pos h2 (pow_pos hu 2)
      nlinarith [sq_nonneg (((γ 0 0 : ℤ) : ℝ))]
  have hx1 : τ.re * D = -t := by
    rw [hDdef, htdef]
    have h1 := congrArg (fun z : ℝ => A * z) hsys1
    have h2 := congrArg (fun z : ℝ => u * C * z) hsys2
    linear_combination h1 - h2
  have hy1 : τ.im * D = u := by
    rw [hDdef]
    have h1 := congrArg (fun z : ℝ => u * C * z) hsys1
    have h2 := congrArg (fun z : ℝ => A * z) hsys2
    linear_combination h1 + h2 + u * hdetR
  have hA1 : |τ.re| < 1 := by
    have h1 := hτ.1
    have h2 := hτ.2.1
    rw [abs_lt]
    exact ⟨h1, h2⟩
  have hB1 : |τ.re| < τ.re^2 + τ.im^2 := by
    have hn1 := hτ.2.2.1
    have hn2 := hτ.2.2.2
    have e1 : ‖(τ:ℂ) - (1/2 : ℂ)‖^2 = (τ.re - 1/2)^2 + τ.im^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have h1 : ((τ:ℂ) - (1/2 : ℂ)).re = τ.re - 1/2 := by
        rw [Complex.sub_re, UpperHalfPlane.coe_re]; simp
      have h2 : ((τ:ℂ) - (1/2 : ℂ)).im = τ.im := by
        rw [Complex.sub_im, UpperHalfPlane.coe_im]; simp
      rw [h1, h2]; ring
    have e2 : ‖(τ:ℂ) + (1/2 : ℂ)‖^2 = (τ.re + 1/2)^2 + τ.im^2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have h1 : ((τ:ℂ) + (1/2 : ℂ)).re = τ.re + 1/2 := by
        rw [Complex.add_re, UpperHalfPlane.coe_re]; simp
      have h2 : ((τ:ℂ) + (1/2 : ℂ)).im = τ.im := by
        rw [Complex.add_im, UpperHalfPlane.coe_im]; simp
      rw [h1, h2]; ring
    have h1 : τ.re^2 + τ.im^2 > τ.re := by
      have h := hn1
      have h2 : (1/2:ℝ)^2 < ‖(τ:ℂ) - (1/2 : ℂ)‖^2 := by
        nlinarith [norm_nonneg ((τ:ℂ) - (1/2 : ℂ))]
      rw [e1] at h2
      nlinarith [h2]
    have h2 : τ.re^2 + τ.im^2 > -τ.re := by
      have h := hn2
      have h3 : (1/2:ℝ)^2 < ‖(τ:ℂ) + (1/2 : ℂ)‖^2 := by
        nlinarith [norm_nonneg ((τ:ℂ) + (1/2 : ℂ))]
      rw [e2] at h3
      nlinarith [h3]
    rcases le_or_gt (0:ℝ) τ.re with hs | hs
    · rwa [abs_of_nonneg hs]
    · rw [abs_of_neg hs]; exact h2
  have hAu : |t| < D := by
    have h2 : τ.re = -t / D := by
      rw [eq_div_iff (ne_of_gt hposden)]
      linarith [hx1]
    have h3 : |τ.re| = |t| / D := by
      rw [h2, abs_div, abs_of_pos hposden, abs_neg]
    rw [h3, div_lt_one hposden] at hA1
    exact hA1
  have hsq2 : (B^2 + Dd^2*u^2) * D = t^2 + u^2 := by
    rw [hDdef, htdef]
    calc (B^2 + Dd^2*u^2) * (A^2 + C^2*u^2)
        = (A*B + C*Dd*u^2)^2 + u^2 * (A*Dd - B*C)^2 := by ring
      _ = (A*B + C*Dd*u^2)^2 + u^2 := by rw [hdetR]; ring
  have hBu : |t| < B^2 + Dd^2*u^2 := by
    have h2 : τ.re = -t / D := by
      rw [eq_div_iff (ne_of_gt hposden)]
      linarith [hx1]
    have h3 : τ.im = u / D := by
      rw [eq_div_iff (ne_of_gt hposden)]
      linarith [hy1]
    have h4 : |t| * D < t^2 + u^2 := by
      have hh := hB1
      rw [h2, h3] at hh
      simp only [abs_neg, abs_div, abs_of_pos hposden, neg_sq, div_pow] at hh
      rw [← add_div] at hh
      rw [div_lt_div_iff₀ hposden (pow_pos hposden 2)] at hh
      rw [pow_two, ← mul_assoc] at hh
      exact lt_of_mul_lt_mul_right hh hposden.le
    rw [← hsq2] at h4
    exact lt_of_mul_lt_mul_right h4 hposden.le
  have ht0 : t = 0 := by
    have hcore := core (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) (u^2) (pow_pos hu 2) hdetR
      (by simpa only [← hAdef, ← hBdef, ← hCdef, ← hDdef, ← htdef] using hAu)
      (by simpa only [← hAdef, ← hBdef, ← hCdef, ← hDdef, ← htdef] using hBu)
    have hcore' : A * B + C * Dd * u^2 = 0 := by
      simpa only [← hAdef, ← hBdef, ← hCdef, ← hDdef] using hcore
    rw [← htdef] at hcore'
    exact hcore'
  rw [ht0, neg_zero] at hx1
  exact (mul_eq_zero.mp hx1).resolve_right (ne_of_gt hposden)

end Work.Asymptotics
