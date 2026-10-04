import Mathlib
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.Q2PR.scale_real
import Submission.Work.Diff.Alg.Q2PR.root_quad
import Submission.Work.Diff.Alg.Q2PR.orthonormal_basis

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.Alg.q2p_reduce`

Given two `ℂ`-linearly independent vectors `z w : Fin n → ℂ`, there is an invertible `ℂ`-linear
change of basis `(ζ, η) = (a z + b w, c z + d w)` for which the four real vectors
`Re ζ, Im ζ, Re η, Im η` are mutually orthogonal: equivalently the new pair satisfies
`cHerm ζ η = 0`, `cBil ζ η = 0` and `cBil ζ ζ`, `cBil η η` are real.

The proof picks an `cHerm`-orthonormal basis `e₁, e₂` of `span_ℂ {z, w}` and then looks for
`ζ = α e₁ + β e₂`, `η = -conj β e₁ + conj α e₂`.  The pair `(ζ, η)` is `cHerm`-orthogonal for
every `(α, β)`, and `cBil ζ η = -p α conj β + q (α conj α - β conj β) + r β conj α` with
`p = cBil e₁ e₁`, `q = cBil e₁ e₂`, `r = cBil e₂ e₂`; this complex quadratic form always has a
nontrivial zero (`root_quad`).  Finally `ζ` and `η` are scaled (`scale_real`) so that `cBil` is
real on each of them.
-/

namespace Work.Diff.Alg.Q2PRed

open Finset Submission.Diff.Alg Work.Diff.Alg.Q2P

variable {n : ℕ}

/-! ## The Euclidean pairing -/

theorem dot_self_nonneg (u : Fin n → ℝ) : 0 ≤ dot u u := by
  simp only [dot]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg (u i)

theorem dot_self_eq_zero {u : Fin n → ℝ} : dot u u = 0 ↔ u = 0 := by
  constructor
  · intro h
    funext i
    have h' := (Finset.sum_eq_zero_iff_of_nonneg (f := fun i => u i * u i)
      (fun i _ => mul_self_nonneg (u i))).mp (by simpa [dot] using h)
    exact mul_self_eq_zero.mp (h' i (Finset.mem_univ i))
  · rintro rfl; simp [dot]

/-! ## Bilinearity of the two pairings -/

theorem cHerm_add₁ (z z' w : Fin n → ℂ) : cHerm (z + z') w = cHerm z w + cHerm z' w := by
  simp only [cHerm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem cHerm_add₂ (z w w' : Fin n → ℂ) : cHerm z (w + w') = cHerm z w + cHerm z w' := by
  simp only [cHerm, Pi.add_apply, star_add, mul_add, Finset.sum_add_distrib]

theorem cHerm_smul₁ (a : ℂ) (z w : Fin n → ℂ) : cHerm (a • z) w = a * cHerm z w := by
  simp only [cHerm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cHerm_smul₂ (a : ℂ) (z w : Fin n → ℂ) : cHerm z (a • w) = star a * cHerm z w := by
  simp only [cHerm, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [star_mul]; ring

theorem cHerm_comm (z w : Fin n → ℂ) : cHerm z w = star (cHerm w z) := by
  simp only [cHerm, star_sum, star_mul, star_star]

theorem cBil_add₁ (z z' w : Fin n → ℂ) : cBil (z + z') w = cBil z w + cBil z' w := by
  simp only [cBil, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem cBil_add₂ (z w w' : Fin n → ℂ) : cBil z (w + w') = cBil z w + cBil z w' := by
  simp only [cBil, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem cBil_smul₁ (a : ℂ) (z w : Fin n → ℂ) : cBil (a • z) w = a * cBil z w := by
  simp only [cBil, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cBil_smul₂ (a : ℂ) (z w : Fin n → ℂ) : cBil z (a • w) = a * cBil z w := by
  simp only [cBil, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cBil_comm (z w : Fin n → ℂ) : cBil z w = cBil w z := by
  simp only [cBil]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## Positivity of `cHerm z z` -/

theorem cHerm_self_re (z : Fin n → ℂ) :
    (cHerm z z).re = dot (cRe z) (cRe z) + dot (cIm z) (cIm z) := cHerm_re z z

theorem cHerm_self_re_nonneg (z : Fin n → ℂ) : 0 ≤ (cHerm z z).re := by
  rw [cHerm_self_re]; exact add_nonneg (dot_self_nonneg _) (dot_self_nonneg _)

theorem cHerm_self_im (z : Fin n → ℂ) : (cHerm z z).im = 0 := by
  rw [cHerm_im, dot_comm' (cIm z) (cRe z)]; ring

theorem cHerm_self_re_pos {z : Fin n → ℂ} (hz : z ≠ 0) : 0 < (cHerm z z).re := by
  rw [cHerm_self_re]
  have h1 : 0 ≤ dot (cRe z) (cRe z) := dot_self_nonneg _
  have h2 : 0 ≤ dot (cIm z) (cIm z) := dot_self_nonneg _
  rcases eq_or_ne (cRe z) 0 with h | h
  · rcases eq_or_ne (cIm z) 0 with h' | h'
    · refine absurd ?_ hz
      funext i
      exact Complex.ext (by simpa [cRe] using congrFun h i) (by simpa [cIm] using congrFun h' i)
    · have hne : dot (cIm z) (cIm z) ≠ 0 := fun hh => h' (dot_self_eq_zero.mp hh)
      have : 0 < dot (cIm z) (cIm z) := lt_of_le_of_ne' h2 hne
      linarith
  · have hne : dot (cRe z) (cRe z) ≠ 0 := fun hh => h (dot_self_eq_zero.mp hh)
    have : 0 < dot (cRe z) (cRe z) := lt_of_le_of_ne' h1 hne
    linarith

theorem cHerm_self_ne_zero {z : Fin n → ℂ} : cHerm z z ≠ 0 ↔ z ≠ 0 := by
  constructor
  · intro h hz; exact h (by rw [hz]; simp [cHerm])
  · intro hz h; have := cHerm_self_re_pos hz; rw [h] at this; simp at this

/-! ## Expansion of the pairings on an orthonormal pair -/

theorem cHerm_pair (a b c d : ℂ) (z w : Fin n → ℂ)
    (h11 : cHerm z z = 1) (h22 : cHerm w w = 1) (h12 : cHerm z w = 0) (h21 : cHerm w z = 0) :
    cHerm (a • z + b • w) (c • z + d • w) = a * star c + b * star d := by
  simp only [cHerm_add₁, cHerm_add₂, cHerm_smul₁, cHerm_smul₂, h11, h22, h12, h21,
    mul_one, mul_zero, add_zero]
  ring

theorem cHerm_self_pair (a b : ℂ) (z w : Fin n → ℂ)
    (h11 : cHerm z z = 1) (h22 : cHerm w w = 1) (h12 : cHerm z w = 0) (h21 : cHerm w z = 0) :
    cHerm (a • z + b • w) (a • z + b • w) = a * star a + b * star b :=
  cHerm_pair a b a b z w h11 h22 h12 h21

theorem cBil_pair (a b c d : ℂ) (z w : Fin n → ℂ) :
    cBil (a • z + b • w) (c • z + d • w)
      = a * c * cBil z z + a * d * cBil z w + b * c * cBil w z + b * d * cBil w w := by
  simp only [cBil_add₁, cBil_add₂, cBil_smul₁, cBil_smul₂]; ring

theorem mul_star_re (a : ℂ) : (a * star a).re = Complex.normSq a := by
  simp [Complex.mul_re, Complex.normSq_apply]

theorem pair_ne_zero {a b : ℂ} (h : a ≠ 0 ∨ b ≠ 0) : a * star a + b * star b ≠ 0 := by
  intro hc
  have hre : (a * star a + b * star b).re = 0 := by rw [hc]; rfl
  rw [Complex.add_re, mul_star_re, mul_star_re] at hre
  have ha := Complex.normSq_nonneg a
  have hb := Complex.normSq_nonneg b
  have ha0 : Complex.normSq a = 0 := by linarith
  have hb0 : Complex.normSq b = 0 := by linarith
  rw [Complex.normSq_eq_zero] at ha0 hb0
  rcases h with h | h
  · exact h ha0
  · exact h hb0

end Work.Diff.Alg.Q2PRed

namespace Work.Diff.Alg

open Finset Submission.Diff.Alg Work.Diff.Alg.Q2P Work.Diff.Alg.Q2PRed

theorem q2p_reduce {n : ℕ} (z w : Fin n → ℂ)
    (hind : ∀ a b : ℂ, (∀ i, a * z i + b * w i = 0) → a = 0 ∧ b = 0) :
    ∃ (a b c d : ℂ), a * d - b * c ≠ 0 ∧
      Work.Diff.Alg.Q2P.cHerm (Work.Diff.Alg.Q2P.comb a b z w) (Work.Diff.Alg.Q2P.comb c d z w) = 0 ∧
      Work.Diff.Alg.Q2P.cBil (Work.Diff.Alg.Q2P.comb a b z w) (Work.Diff.Alg.Q2P.comb c d z w) = 0 ∧
      (Work.Diff.Alg.Q2P.cBil (Work.Diff.Alg.Q2P.comb a b z w)
        (Work.Diff.Alg.Q2P.comb a b z w)).im = 0 ∧
      (Work.Diff.Alg.Q2P.cBil (Work.Diff.Alg.Q2P.comb c d z w)
        (Work.Diff.Alg.Q2P.comb c d z w)).im = 0 := by
  obtain ⟨e1, e2, c1, c2, c3, hc1, hc2, h11, h22, h12, h21, hz, hw⟩ :=
    Work.Diff.Alg.Q2PR.orthonormal_basis z w hind
  obtain ⟨α, β, hαβ, hroot⟩ :=
    Work.Diff.Alg.Q2PR.root_quad (cBil e1 e1) (cBil e1 e2) (cBil e2 e2)
  set ζ : Fin n → ℂ := α • e1 + β • e2 with hζ
  set η : Fin n → ℂ := (-(star β)) • e1 + (star α) • e2 with hη
  have hζηH : cHerm ζ η = 0 := by
    rw [hζ, hη, cHerm_pair α β (-(star β)) (star α) e1 e2 h11 h22 h12 h21]
    simp only [star_neg, star_star]
    ring
  have hζηB : cBil ζ η = 0 := by
    rw [hζ, hη, cBil_pair α β (-(star β)) (star α) e1 e2, cBil_comm e2 e1]
    have key : -(cBil e1 e1) * α * star β + cBil e1 e2 * (α * star α - β * star β)
          + cBil e2 e2 * β * star α
        = α * (-(star β)) * cBil e1 e1 + α * star α * cBil e1 e2 + β * (-(star β)) * cBil e1 e2
          + β * star α * cBil e2 e2 := by
      ring_nf
    rw [← key]
    exact hroot
  have hζζ : cHerm ζ ζ = α * star α + β * star β := by
    rw [hζ, cHerm_self_pair α β e1 e2 h11 h22 h12 h21]
  have hηη : cHerm η η = α * star α + β * star β := by
    rw [hη, cHerm_self_pair (-(star β)) (star α) e1 e2 h11 h22 h12 h21]
    simp only [star_neg, star_star]
    ring
  have hS : α * star α + β * star β ≠ 0 := pair_ne_zero hαβ
  obtain ⟨l, hl0, hl⟩ := Work.Diff.Alg.Q2PR.scale_real (cBil ζ ζ)
  obtain ⟨m, hm0, hm⟩ := Work.Diff.Alg.Q2PR.scale_real (cBil η η)
  set ζ' : Fin n → ℂ := l • ζ with hζ'
  set η' : Fin n → ℂ := m • η with hη'
  have hls : l * star l ≠ 0 := mul_ne_zero hl0 (star_ne_zero.mpr hl0)
  have hms : m * star m ≠ 0 := mul_ne_zero hm0 (star_ne_zero.mpr hm0)
  have hζ'c : cHerm ζ' ζ' = l * star l * (α * star α + β * star β) := by
    rw [hζ', cHerm_smul₁, cHerm_smul₂, hζζ, mul_assoc]
  have hη'c : cHerm η' η' = m * star m * (α * star α + β * star β) := by
    rw [hη', cHerm_smul₁, cHerm_smul₂, hηη, mul_assoc]
  have hζ'ne : ζ' ≠ 0 := cHerm_self_ne_zero.mp (by rw [hζ'c]; exact mul_ne_zero hls hS)
  have hH' : cHerm ζ' η' = 0 := by
    rw [hζ', hη', cHerm_smul₁, cHerm_smul₂, hζηH]
    ring
  have hB' : cBil ζ' η' = 0 := by
    rw [hζ', hη', cBil_smul₁, cBil_smul₂, hζηB]
    ring
  have hBζ : (cBil ζ' ζ').im = 0 := by
    rw [hζ', cBil_smul₁, cBil_smul₂]; simpa [mul_assoc] using hl
  have hBη : (cBil η' η').im = 0 := by
    rw [hη', cBil_smul₁, cBil_smul₂]; simpa [mul_assoc] using hm
  set a : ℂ := l * (α * c1⁻¹ - β * (c2⁻¹ * c3 * c1⁻¹)) with ha
  set b : ℂ := l * (β * c2⁻¹) with hb
  set c : ℂ := m * ((-(star β)) * c1⁻¹ - (star α) * (c2⁻¹ * c3 * c1⁻¹)) with hc
  set d : ℂ := m * ((star α) * c2⁻¹) with hd
  have he1 : e1 = c1⁻¹ • z := by rw [hz, smul_smul, inv_mul_cancel₀ hc1, one_smul]
  have he2 : e2 = c2⁻¹ • w - (c2⁻¹ * c3 * c1⁻¹) • z := by
    have h : c2 • e2 = w - c3 • e1 := by rw [hw, add_sub_cancel_right]
    calc e2 = c2⁻¹ • (c2 • e2) := by rw [smul_smul, inv_mul_cancel₀ hc2, one_smul]
      _ = c2⁻¹ • (w - c3 • e1) := by rw [h]
      _ = c2⁻¹ • w - (c2⁻¹ * c3) • e1 := by rw [smul_sub, smul_smul]
      _ = c2⁻¹ • w - (c2⁻¹ * c3) • (c1⁻¹ • z) := by rw [he1]
      _ = c2⁻¹ • w - (c2⁻¹ * c3 * c1⁻¹) • z := by rw [smul_smul]
  have hζ'e : ζ' = comb a b z w := by
    rw [hζ', hζ, he1, he2]
    ext i
    simp only [comb, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [ha, hb]
    ring
  have hη'e : η' = comb c d z w := by
    rw [hη', hη, he1, he2]
    ext i
    simp only [comb, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [hc, hd]
    ring
  refine ⟨a, b, c, d, ?_, ?_, ?_, ?_, ?_⟩
  · intro hdet
    have hcombζ : comb a b z w ≠ 0 := fun h => hζ'ne (hζ'e.trans h)
    have hab : a ≠ 0 ∨ b ≠ 0 := by
      by_contra hh
      simp only [not_or, not_not] at hh
      exact hcombζ (by ext i; simp [comb, hh.1, hh.2])
    have hS' : cHerm ζ' ζ' ≠ 0 := by rw [hζ'c]; exact mul_ne_zero hls hS
    obtain ⟨t, ht1, ht2⟩ : ∃ t : ℂ, c = t * a ∧ d = t * b := by
      by_cases ha0 : a = 0
      · have hb0 : b ≠ 0 := by
          rcases hab with h | h
          · exact absurd ha0 h
          · exact h
        have hbc : b * c = 0 := by
          have h := hdet
          rw [ha0, zero_mul, zero_sub] at h
          simpa using h
        have hc0 : c = 0 := (mul_eq_zero.mp hbc).resolve_left hb0
        exact ⟨d * b⁻¹, by rw [hc0, ha0, mul_zero], by rw [mul_assoc, inv_mul_cancel₀ hb0, mul_one]⟩
      · have had : a * d = b * c := sub_eq_zero.mp hdet
        refine ⟨a⁻¹ * c, by rw [mul_assoc, mul_comm c a, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul], ?_⟩
        calc d = a⁻¹ * (a * d) := by rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
          _ = a⁻¹ * (b * c) := by rw [had]
          _ = a⁻¹ * c * b := by ring
    have hηt : η' = t • ζ' := by
      rw [hη'e, hζ'e]
      ext i
      simp only [comb, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [ht1, ht2]
      ring
    have htmp := hH'
    rw [hηt, cHerm_smul₂] at htmp
    have ht0 : t = 0 := by
      rcases mul_eq_zero.mp htmp with h | h
      · exact star_eq_zero.mp h
      · exact absurd h hS'
    have hzero : cHerm η' η' = 0 := by
      rw [hηt, ht0, zero_smul]; simp [cHerm]
    rw [hη'c] at hzero
    exact mul_ne_zero hms hS hzero
  · rw [← hζ'e, ← hη'e]; exact hH'
  · rw [← hζ'e, ← hη'e]; exact hB'
  · rw [← hζ'e]; exact hBζ
  · rw [← hη'e]; exact hBη

end Work.Diff.Alg
