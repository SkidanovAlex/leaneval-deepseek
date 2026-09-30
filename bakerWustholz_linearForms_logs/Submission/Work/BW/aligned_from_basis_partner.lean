import Mathlib
import Submission.Work.BW.aligned_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Rounding to the nearest integer: every real number is within `1/2` of an integer. -/
lemma exists_int_abs_sub_le_half (x : ℝ) : ∃ b : ℤ, |x - (b : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊x + 1 / 2⌋, ?_⟩
  have h1 : ((⌊x + 1 / 2⌋ : ℤ) : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have h2 : x + 1 / 2 < ((⌊x + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Nearest-integer approximation of the rational number `mm / d` by an integer `b`:
`|mm - b * d| ≤ |d| / 2`. -/
lemma near_mul_real (d mm : ℤ) (hd : d ≠ 0) :
    ∃ b : ℤ, |(mm : ℝ) - (b : ℝ) * (d : ℝ)| ≤ |(d : ℝ)| / 2 := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  obtain ⟨b, hb⟩ : ∃ b : ℤ, |((mm : ℝ) / (d : ℝ)) - (b : ℝ)| ≤ 1 / 2 := by
    refine ⟨⌊(mm : ℝ) / (d : ℝ) + 1 / 2⌋, ?_⟩
    have h1 : ((⌊(mm : ℝ) / (d : ℝ) + 1 / 2⌋ : ℤ) : ℝ) ≤ (mm : ℝ) / (d : ℝ) + 1 / 2 :=
      Int.floor_le _
    have h2 : (mm : ℝ) / (d : ℝ) + 1 / 2 < ((⌊(mm : ℝ) / (d : ℝ) + 1 / 2⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  refine ⟨b, ?_⟩
  have hdecomp : (mm : ℝ) - (b : ℝ) * (d : ℝ) =
      (d : ℝ) * ((mm : ℝ) / (d : ℝ) - (b : ℝ)) := by
    field_simp
  rw [hdecomp, abs_mul]
  calc |(d : ℝ)| * |(mm : ℝ) / (d : ℝ) - (b : ℝ)| ≤ |(d : ℝ)| * (1 / 2) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = |(d : ℝ)| / 2 := by ring

theorem aligned_from_basis_partner {m : ℕ} (L : Submodule ℤ (Fin m → ℤ))
    (A r u : Fin m → ℤ) (hA : A ∈ L) (hr : r ∈ L)
    (hgenA : ∀ y : Fin m → ℤ, y ∈ L ↔ ∃ a b : ℤ, y = a • A + b • r)
    (hindA : ∀ a b : ℤ, a • A + b • r = 0 → a = 0 ∧ b = 0)
    (θ : (Fin m → ℤ) → ℂ)
    (hθ : ∀ (a b : ℤ) (y z : Fin m → ℤ), θ (a • y + b • z) = (a : ℂ) * θ y + (b : ℂ) * θ z)
    (hrker : θ r = 0)
    (c : Fin m → ℝ) (hc : ∀ i, 0 ≤ c i) (T : ℝ) (hT : 0 ≤ T)
    (huθ : θ u ≠ 0)
    (hdec : ∃ d mm : ℤ, d ≠ 0 ∧ u = d • A + mm • r)
    (hub : Work.BW.wn c u + Work.BW.wn c r ≤ T / 2) :
    ∃ e' : Fin 2 → Fin m → ℤ,
      (∀ y : Fin m → ℤ, y ∈ L ↔ ∃ a b : ℤ, y = a • e' 0 + b • e' 1) ∧
      (e' 0 ≠ 0 → (e' 1 = 0 ∨ ∀ a b : ℤ, a • e' 0 + b • e' 1 = 0 → a = 0 ∧ b = 0)) ∧
      (e' 1 = 0 → Work.BW.wn c (e' 0) ≤ T) ∧
      (e' 1 ≠ 0 → θ (e' 0) + θ (e' 1) = 0 ∧ Work.BW.wn c (e' 0) + Work.BW.wn c (e' 1) ≤ T) := by
  obtain ⟨d, mm, hd, hu⟩ := hdec
  obtain ⟨b₀, hb₀⟩ := near_mul_real d mm hd
  -- The aligned pair: `e' 0 = A + b₀ • r`, `e' 1 = -(A + (b₀ - 1) • r)`, so that
  -- `e' 0 + e' 1 = r` and `{e' 0, e' 1}` is a unimodular change of basis from `{A, r}`.
  let e' : Fin 2 → Fin m → ℤ :=
    fun i => if i = (0 : Fin 2) then A + b₀ • r else -(A + (b₀ - 1) • r)
  have he'0 : e' 0 = A + b₀ • r := by simp [e']
  have he'1 : e' 1 = -(A + (b₀ - 1) • r) := by simp [e']
  have hsum : e' 0 + e' 1 = r := by
    rw [he'0, he'1]
    ext i
    simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hth : θ (e' 0) + θ (e' 1) = 0 := by
    have h := hθ 1 1 (e' 0) (e' 1)
    simp only [one_smul] at h
    rw [hsum, hrker] at h
    simpa using h.symm
  have he'1_ne : e' 1 ≠ 0 := by
    intro h
    rw [he'1] at h
    have hz : A + (b₀ - 1) • r = 0 := neg_eq_zero.mp h
    have hcon := hindA 1 (b₀ - 1) (by simpa using hz)
    exact one_ne_zero hcon.1
  have hbnd : Work.BW.wn c (e' 0) + Work.BW.wn c (e' 1) ≤ T := by
    have hD : 0 < |(d : ℝ)| := abs_pos.mpr (by exact_mod_cast hd)
    have hDn : |(d : ℝ)| ≠ 0 := ne_of_gt hD
    have hD1 : 1 ≤ |(d : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |d| := Int.one_le_abs hd
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|d| : ℤ) : ℝ) := by exact_mod_cast h1
        _ = |(d : ℝ)| := Int.cast_abs
    have hUnn : 0 ≤ Work.BW.wn c u := wn_nonneg c hc u
    have hRnn : 0 ≤ Work.BW.wn c r := wn_nonneg c hc r
    have hmul : d • (A + b₀ • r) = u - (mm - b₀ * d) • r := by
      rw [hu]
      ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hDm : |(d : ℝ)| * Work.BW.wn c (A + b₀ • r) ≤
        Work.BW.wn c u + |((mm - b₀ * d : ℤ) : ℝ)| * Work.BW.wn c r := by
      calc |(d : ℝ)| * Work.BW.wn c (A + b₀ • r) = wn c (d • (A + b₀ • r)) := by
            rw [wn_smul]
        _ = wn c (u - (mm - b₀ * d) • r) := by rw [hmul]
        _ ≤ wn c u + wn c ((mm - b₀ * d) • r) := wn_sub_le c hc u _
        _ = wn c u + |((mm - b₀ * d : ℤ) : ℝ)| * wn c r := by rw [wn_smul]
    have hX : |((mm - b₀ * d : ℤ) : ℝ)| ≤ |(d : ℝ)| / 2 := by simpa using hb₀
    have hstep : |(d : ℝ)| * wn c (A + b₀ • r) ≤
        wn c u + (|(d : ℝ)| / 2) * wn c r := by
      have h := mul_le_mul_of_nonneg_right hX hRnn
      linarith [hDm, h]
    have hg1 : wn c (A + (b₀ - 1) • r) ≤ wn c (A + b₀ • r) + wn c r := by
      have hsub : A + (b₀ - 1) • r = (A + b₀ • r) - r := by
        ext i
        simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        ring
      calc wn c (A + (b₀ - 1) • r) = wn c ((A + b₀ • r) - r) := by rw [hsub]
        _ ≤ wn c (A + b₀ • r) + wn c r := wn_sub_le c hc _ _
    have he0 : wn c (e' 0) = wn c (A + b₀ • r) := by rw [he'0]
    have he1 : wn c (e' 1) = wn c (A + (b₀ - 1) • r) := by rw [he'1, wn_neg]
    have hg0 : wn c (A + b₀ • r) ≤ wn c u / |(d : ℝ)| + wn c r / 2 := by
      have hkey : wn c (A + b₀ • r) ≤
          (wn c u + (|(d : ℝ)| / 2) * wn c r) / |(d : ℝ)| := by
        rw [le_div_iff₀ hD]
        calc wn c (A + b₀ • r) * |(d : ℝ)| = |(d : ℝ)| * wn c (A + b₀ • r) := by ring
          _ ≤ wn c u + (|(d : ℝ)| / 2) * wn c r := hstep
      have hsplit : (wn c u + (|(d : ℝ)| / 2) * wn c r) / |(d : ℝ)| =
          wn c u / |(d : ℝ)| + wn c r / 2 := by
        field_simp
      rwa [hsplit] at hkey
    have hdiv : wn c u / |(d : ℝ)| ≤ wn c u := by
      rw [div_le_iff₀ hD]
      nlinarith [hD1, hUnn]
    have hT2 : 2 * wn c u + 2 * wn c r ≤ T := by linarith [hub]
    rw [he0, he1]
    linarith [hg1, hg0, hdiv, hT2]
  refine ⟨e', ?_, ?_, ?_, ?_⟩
  · intro y
    constructor
    · intro hy
      obtain ⟨a, b, h⟩ := (hgenA y).mp hy
      refine ⟨a * (1 - b₀) + b, b - a * b₀, ?_⟩
      rw [h, he'0, he'1]
      ext i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · rintro ⟨a, b, rfl⟩
      rw [hgenA]
      refine ⟨a - b, a * b₀ + b * (1 - b₀), ?_⟩
      rw [he'0, he'1]
      ext i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      ring
  · intro _
    right
    intro a b hab
    have h2 : (a - b) • A + (a * b₀ + b * (1 - b₀)) • r = 0 := by
      rw [← hab, he'0, he'1]
      ext i
      simp only [Pi.add_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨h1, h2'⟩ := hindA (a - b) (a * b₀ + b * (1 - b₀)) h2
    have hab' : a = b := by linarith
    have ha0 : a = 0 := by
      rw [← hab'] at h2'
      ring_nf at h2'
      exact h2'
    exact ⟨ha0, by rw [← hab', ha0]⟩
  · intro h
    exact absurd h he'1_ne
  · intro _
    exact ⟨hth, hbnd⟩

end Work.BW
