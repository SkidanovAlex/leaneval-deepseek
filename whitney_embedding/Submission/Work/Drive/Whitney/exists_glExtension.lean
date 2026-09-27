import Mathlib
import Submission.Work.Drive.Whitney.frameExtensionBoundary

/-!
# Extension of a smooth family of invertible matrices onto `[a,b]`

This file proves `Work.Drive.Whitney.exists_glExtension`:

if `g : ℝ → Matrix (Fin k) (Fin k) ℝ` is entrywise `C^∞`, invertible at `a` and at `b` and
`0 < (g a).det * (g b).det` (the two determinants have the same sign), then for some `δ > 0` there is
an entrywise `C^∞` family `H` with `H = g` outside `(a + δ, b - δ)` and `(H t).det ≠ 0` for all
`t ∈ [a,b]`.

The construction is the "clamped bridge":

* choose `ρ > 0` (much smaller than `b - a`) so that
  * `g` is entrywise within the invertibility ball of `g a` on `[a, a + ρ]`, and within the
    invertibility ball of `g b` on `[b - ρ, b]` (continuity at `a` and at `b`, and openness of the
    invertible matrices — `exists_entrywise_ball_det`);
* put `c := a + ρ/4`, `d := b - ρ/4`, `τ := ρ/8` and
  * `γ : ℝ → Matrix (Fin k) (Fin k) ℝ` a smooth path of invertible matrices which equals `g a` on
    `(-∞, c + τ]` (so it is constant on the left transition) and `g b` on `[d - τ, ∞)`.  It exists by
    `Glue.of_detSign` applied to `glue_canon` (smooth paths in `GL_k(ℝ)` joining the canonical
    matrices of equal determinant sign) and `Glue.reparam`;
  * `χ` a smooth scalar bump with `χ = 0` off `(c,d)` and `χ = 1` on `[c + τ, d - τ]`;
  * `H := (1 - χ) • g + χ • γ`.

Then `H = g` off `(c,d)`, and `H` is invertible on `[a,b]`: on `[a, c + τ]` it is a convex
combination of two matrices within the entrywise invertibility ball of `g a`, on `[c + τ, d - τ]` it
equals `γ`, and on `[d - τ, b]` it is a convex combination of two matrices within the entrywise
invertibility ball of `g b`.
-/

open scoped Matrix.Norms.Elementwise

namespace Work.Drive.Whitney

/-- The `C^∞` level, as an element of `WithTop ℕ∞` (same as `Work.Drive.Whitney.Smooth`). -/
abbrev CInf : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- **Entrywise smoothness of a matrix-valued smooth map.**  If `f : ℝ → Matrix (Fin k) (Fin k) ℝ`
is `C^∞` (for the entrywise/sup structure), then so is each of its entries. -/
lemma contDiff_matrix_apply {k : ℕ} {f : ℝ → Matrix (Fin k) (Fin k) ℝ}
    (hf : ContDiff ℝ CInf f) (i j : Fin k) : ContDiff ℝ CInf (fun t => f t i j) := by
  change ContDiff ℝ CInf (fun t : ℝ => fun i : Fin k => fun j : Fin k => f t i j) at hf
  rw [contDiff_pi] at hf
  exact (contDiff_pi.mp (hf i)) j

/-- **The invertible matrices form an open set, in the entrywise form.**  If `M` is invertible then
there is `r > 0` such that every matrix all of whose entries differ from those of `M` by less than
`r` is invertible as well. -/
lemma exists_entrywise_ball_det {k : ℕ} (M : Fin k → Fin k → ℝ) (hM : Matrix.det M ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ A : Fin k → Fin k → ℝ,
      (∀ i j, |A i j - M i j| < r) → Matrix.det A ≠ 0 := by
  have hcont : ContinuousAt (fun A : Fin k → Fin k → ℝ => Matrix.det A) M := by fun_prop
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨r, hr, hr'⟩ := hcont |Matrix.det M| (abs_pos.mpr hM)
  refine ⟨r, hr, fun A hA => ?_⟩
  intro hd0
  have hdist : dist A M < r := by
    rw [dist_pi_lt_iff hr]; intro i
    rw [dist_pi_lt_iff hr]; intro j
    rw [Real.dist_eq]; exact hA i j
  have h := hr' hdist
  rw [Real.dist_eq, hd0] at h
  rw [zero_sub, abs_neg] at h
  exact lt_irrefl _ h

/-- **`Glue` for matrices whose determinants have the same sign.**  Two invertible matrices `A`, `B`
with `0 < A.det * B.det` are joined by a smooth path of invertible matrices which is equal to `A` on
`(-∞, 0]` and to `B` on `[1, ∞)`. -/
theorem Glue.of_detSign {k : ℕ} {A B : Matrix (Fin k) (Fin k) ℝ}
    (hA : A.det ≠ 0) (hB : B.det ≠ 0) (h : 0 < A.det * B.det) : Glue A B := by
  rcases mul_pos_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hs : (decide (0 < A.det)) = (decide (0 < B.det)) := by
      rw [decide_eq_true ha, decide_eq_true hb]
    have h2 := Glue.symm (glue_canon k B hB)
    rw [← hs] at h2
    exact Glue.trans (glue_canon k A hA) h2
  · have hs : (decide (0 < A.det)) = (decide (0 < B.det)) := by
      rw [decide_eq_false (not_lt.mpr (le_of_lt ha)), decide_eq_false (not_lt.mpr (le_of_lt hb))]
    have h2 := Glue.symm (glue_canon k B hB)
    rw [← hs] at h2
    exact Glue.trans (glue_canon k A hA) h2

/-- **Reparametrised `Glue` path.**  A `Glue` path from `A` to `B` can be made constant equal to
`A` to the left of an arbitrary `u` and constant equal to `B` to the right of an arbitrary `v > u`
(by composing with an affine reparametrisation of `ℝ`). -/
lemma Glue.reparam {k : ℕ} {A B : Matrix (Fin k) (Fin k) ℝ} (h : Glue A B)
    {u v : ℝ} (huv : u < v) :
    ∃ γ : ℝ → Matrix (Fin k) (Fin k) ℝ, ContDiff ℝ CInf γ ∧ (∀ t, t ≤ u → γ t = A) ∧
      (∀ t, v ≤ t → γ t = B) ∧ (∀ t, (γ t).det ≠ 0) := by
  obtain ⟨η, hη0, hη1, hηc, hηd⟩ := h
  refine ⟨fun t => η ((t - u) / (v - u)), ?_, ?_, ?_, ?_⟩
  · exact hηc.comp (by fun_prop)
  · intro t ht
    exact hη0 _ (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  · intro t ht
    have h1 : 1 ≤ (t - u) / (v - u) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < v - u)]
      linarith
    exact hη1 _ h1
  · intro t; exact hηd _

/-- **Extension of a smooth family of invertible matrices onto `[a,b]`.**

If `g : ℝ → Matrix (Fin k) (Fin k) ℝ` is smooth (entrywise), invertible at `a` and at `b` and
`0 < (g a).det * (g b).det`, then there is `δ > 0` and an entrywise-smooth `H` with `H = g` off the
open interval `(a + δ, b - δ)` and with `(H t).det ≠ 0` for all `t ∈ [a,b]`.

Route: `g` is invertible on neighbourhoods of `a` and `b`; clamp the parameter with a smooth `ψ`
(= identity near `a`, constant later) so that `g ∘ ψ` is invertible; similarly on the right; join
the two constant values by a path in `GL_k(ℝ)` from `Work.Drive.Whitney.FB.stabilizerPath` with
`k = 0` (smooth paths in `GL_n` between two operators whose determinants have the same sign); the
sign condition is supplied by `hsign` and by continuity of `det ∘ g` on the intervals where `g` is
invertible. -/
theorem exists_glExtension {k : ℕ} {a b : ℝ} (hab : a < b)
    (g : ℝ → Matrix (Fin k) (Fin k) ℝ)
    (hg : ∀ i j : Fin k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => g t i j))
    (ha : (g a).det ≠ 0) (hb : (g b).det ≠ 0)
    (hsign : 0 < (g a).det * (g b).det) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ H : ℝ → Matrix (Fin k) (Fin k) ℝ,
      (∀ i j : Fin k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => H t i j)) ∧
      (∀ t : ℝ, t ∉ Set.Ioo (a + δ) (b - δ) → H t = g t) ∧
      (∀ t ∈ Set.Icc a b, (H t).det ≠ 0) := by
  -- The matrix-valued family `g`, and its continuity.
  have hgC : ContDiff ℝ CInf (fun t : ℝ => fun i : Fin k => fun j : Fin k => g t i j) := by
    rw [contDiff_pi]
    exact fun i => contDiff_pi.mpr fun j => hg i j
  have hGcont : Continuous (fun t : ℝ => fun i : Fin k => fun j : Fin k => g t i j) :=
    hgC.continuous
  -- Invertibility margins at the two ends.
  obtain ⟨r, hr, hball⟩ := exists_entrywise_ball_det (fun i j => g a i j) ha
  obtain ⟨s, hs, hball'⟩ := exists_entrywise_ball_det (fun i j => g b i j) hb
  -- Radii on which `g` stays in the corresponding balls.
  obtain ⟨ρ₁, hρ₁, h₁⟩ := Metric.continuousAt_iff.mp (hGcont.continuousAt (x := a)) r hr
  obtain ⟨ρ₂, hρ₂, h₂⟩ := Metric.continuousAt_iff.mp (hGcont.continuousAt (x := b)) s hs
  set ρ : ℝ := min (min ρ₁ ρ₂) ((b - a) / 2) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]; exact lt_min (lt_min hρ₁ hρ₂) (by linarith)
  have hρ1 : ρ ≤ ρ₁ := by
    rw [hρdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hρ2 : ρ ≤ ρ₂ := by
    rw [hρdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hρab : ρ ≤ (b - a) / 2 := by rw [hρdef]; exact min_le_right _ _
  set c : ℝ := a + ρ / 4 with hcdef
  set d : ℝ := b - ρ / 4 with hddef
  set τ : ℝ := ρ / 8 with hτdef
  have hτpos : 0 < τ := by rw [hτdef]; linarith
  have hδpos : 0 < ρ / 4 := by linarith
  -- Closeness of `g` to its values at the endpoints.
  have hcloseA : ∀ t : ℝ, |t - a| < ρ → ∀ i j : Fin k, |g t i j - g a i j| < r := by
    intro t ht i j
    have hta : dist t a < ρ₁ := by rw [Real.dist_eq]; exact lt_of_lt_of_le ht hρ1
    have hd := h₁ hta
    have h1 := (dist_pi_lt_iff hr).mp hd
    have h2 := (dist_pi_lt_iff hr).mp (h1 i)
    simpa [Real.dist_eq] using h2 j
  have hcloseB : ∀ t : ℝ, |t - b| < ρ → ∀ i j : Fin k, |g t i j - g b i j| < s := by
    intro t ht i j
    have htb : dist t b < ρ₂ := by rw [Real.dist_eq]; exact lt_of_lt_of_le ht hρ2
    have hd := h₂ htb
    have h1 := (dist_pi_lt_iff hs).mp hd
    have h2 := (dist_pi_lt_iff hs).mp (h1 i)
    simpa [Real.dist_eq] using h2 j
  -- The path in `GL_k(ℝ)`.
  have hGlue : Glue (g a) (g b) := Glue.of_detSign ha hb hsign
  have huv : c + τ < d - τ := by
    rw [hcdef, hddef, hτdef]
    linarith [hρab, hab]
  obtain ⟨γ, hγc, hγ0, hγ1, hγd⟩ := hGlue.reparam (u := c + τ) (v := d - τ) huv
  -- The scalar bump.
  set χ : ℝ → ℝ := fun t => Real.smoothTransition ((t - c) / τ) *
    Real.smoothTransition ((d - t) / τ) with hχdef
  have hχc : ContDiff ℝ CInf χ := by
    rw [hχdef]
    exact (((Real.smoothTransition.contDiff (n := ⊤)).comp
          ((contDiff_id.sub contDiff_const).div_const τ)).mul
        ((Real.smoothTransition.contDiff (n := ⊤)).comp
          ((contDiff_const.sub contDiff_id).div_const τ)))
  have hχnn : ∀ t, 0 ≤ χ t := by
    intro t; rw [hχdef]
    exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  have hχle : ∀ t, χ t ≤ 1 := by
    intro t; rw [hχdef]
    exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)
  have hχ0 : ∀ t, t ≤ c → χ t = 0 := by
    intro t ht
    simp only [hχdef]
    have : Real.smoothTransition ((t - c) / τ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hτpos.le)
    rw [this, zero_mul]
  have hχ0' : ∀ t, d ≤ t → χ t = 0 := by
    intro t ht
    simp only [hχdef]
    have : Real.smoothTransition ((d - t) / τ) = 0 :=
      Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hτpos.le)
    rw [this, mul_zero]
  have hχ1 : ∀ t, c + τ ≤ t → t ≤ d - τ → χ t = 1 := by
    intro t ht₁ ht₂
    simp only [hχdef]
    have h1 : Real.smoothTransition ((t - c) / τ) = 1 := by
      refine Real.smoothTransition.one_of_one_le ?_
      rw [le_div_iff₀ hτpos]; linarith
    have h2 : Real.smoothTransition ((d - t) / τ) = 1 := by
      refine Real.smoothTransition.one_of_one_le ?_
      rw [le_div_iff₀ hτpos]; linarith
    rw [h1, h2, one_mul]
  refine ⟨ρ / 4, hδpos, fun t : ℝ => (1 - χ t) • g t + χ t • γ t, ?_, ?_, ?_⟩
  · -- smoothness of `H`, entrywise
    intro i j
    show ContDiff ℝ CInf (fun t : ℝ => ((1 - χ t) • g t + χ t • γ t) i j)
    have hγij : ContDiff ℝ CInf (fun t : ℝ => γ t i j) := contDiff_matrix_apply hγc i j
    have hgij : ContDiff ℝ CInf (fun t : ℝ => g t i j) := hg i j
    have h1 : ContDiff ℝ CInf (fun t : ℝ => (1 - χ t) * g t i j) :=
      ((contDiff_const : ContDiff ℝ CInf (fun _ : ℝ => (1 : ℝ))).sub hχc).mul hgij
    have h2 : ContDiff ℝ CInf (fun t : ℝ => χ t * γ t i j) := hχc.mul hγij
    have hfun : (fun t : ℝ => ((1 - χ t) • g t + χ t • γ t) i j)
        = fun t : ℝ => (1 - χ t) * g t i j + χ t * γ t i j := by
      funext t
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hfun]
    exact h1.add h2
  · -- `H = g` off the interval
    intro t ht
    change (1 - χ t) • g t + χ t • γ t = g t
    rw [Set.mem_Ioo, not_and_or] at ht
    rcases ht with h | h
    · have ht' : t ≤ c := by rw [hcdef]; linarith [not_lt.mp h]
      rw [hχ0 t ht']
      simp
    · have ht' : d ≤ t := by rw [hddef]; linarith [not_lt.mp h]
      rw [hχ0' t ht']
      simp
  · -- invertibility on `[a,b]`
    intro t ht
    change ((1 - χ t) • g t + χ t • γ t).det ≠ 0
    rcases le_total t (c + τ) with htc | htc
    · -- left transition (or before it): convex combination inside the ball of `g a`
      have hγt : γ t = g a := hγ0 t htc
      rw [hγt]
      refine hball ((1 - χ t) • g t + χ t • g a) ?_
      intro i j
      show |((1 - χ t) • g t + χ t • g a) i j - g a i j| < r
      have hta : |t - a| < ρ := by
        have h2 : t ≤ a + 3 * (ρ / 8) := by rw [hcdef, hτdef] at htc; linarith
        rw [abs_of_nonneg (by linarith [ht.1])]
        linarith
      have hgt : |g t i j - g a i j| < r := hcloseA t hta i j
      have hsplit : ((1 - χ t) • g t + χ t • g a) i j - g a i j
          = (1 - χ t) * (g t i j - g a i j) := by
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      rw [hsplit, abs_mul]
      have habs : |1 - χ t| ≤ 1 := by
        rw [abs_le]; exact ⟨by linarith [hχle t], by linarith [hχnn t]⟩
      calc |1 - χ t| * |g t i j - g a i j| ≤ 1 * |g t i j - g a i j| :=
            mul_le_mul_of_nonneg_right habs (abs_nonneg _)
        _ = |g t i j - g a i j| := one_mul _
        _ < r := hgt
    · rcases le_total t (d - τ) with htd | htd
      · -- middle: `H = γ`
        have hχt : χ t = 1 := hχ1 t htc htd
        have hHt : (1 - χ t) • g t + χ t • γ t = γ t := by
          rw [hχt]; simp
        rw [hHt]
        exact hγd t
      · -- right transition (or after it): convex combination inside the ball of `g b`
        have hγt : γ t = g b := hγ1 t htd
        rw [hγt]
        refine hball' ((1 - χ t) • g t + χ t • g b) ?_
        intro i j
        show |((1 - χ t) • g t + χ t • g b) i j - g b i j| < s
        have htb : |t - b| < ρ := by
          have h2 : b - 3 * (ρ / 8) ≤ t := by rw [hddef, hτdef] at htd; linarith
          rw [abs_of_nonpos (by linarith [ht.2])]
          linarith
        have hgt : |g t i j - g b i j| < s := hcloseB t htb i j
        have hsplit : ((1 - χ t) • g t + χ t • g b) i j - g b i j
            = (1 - χ t) * (g t i j - g b i j) := by
          simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
          ring
        rw [hsplit, abs_mul]
        have habs : |1 - χ t| ≤ 1 := by
          rw [abs_le]; exact ⟨by linarith [hχle t], by linarith [hχnn t]⟩
        calc |1 - χ t| * |g t i j - g b i j| ≤ 1 * |g t i j - g b i j| :=
              mul_le_mul_of_nonneg_right habs (abs_nonneg _)
          _ = |g t i j - g b i j| := one_mul _
          _ < s := hgt

end Work.Drive.Whitney
