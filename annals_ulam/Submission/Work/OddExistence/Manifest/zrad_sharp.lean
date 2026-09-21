import Mathlib
import Submission.Work.OddVolterra.KernelExt.Defs

/-!
# Sharp jet bounds for the radicand `Zrad` on the full square `[0,1]²`

Local copy of `Work.OddCurveB.Hard.Zrad_jet_bounds_sharp`, the only place in the workspace where
the jet bounds for `KernelExt.Zrad` are proved for *all* `a, σ ∈ [0,1]` (the versions in
`Work.OddVolterra.Window` and `Work.OddVolterra.Existence.aw_thetaM_tri_close` are restricted to
a proper sub-box).
-/

namespace Work.OddExistence.Manifest.ZS

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

open Work.OddVolterra Work.OddVolterra.KernelExt

section JetBounds

/-- The jets of an affine function `v ↦ t * v + h v`. -/
private lemma affine_jet_eq {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (t a : ℝ) (k : ℕ) :
    iteratedDeriv k (fun v : ℝ => t * v + h v) a
      = (if k = 0 then t * a else if k = 1 then t else 0) + iteratedDeriv k h a := by
  have h1 : ContDiffAt ℝ (k : ℕ) (fun v : ℝ => t * v) a := by fun_prop
  have h2 : ContDiffAt ℝ (k : ℕ) h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [show (fun v : ℝ => t * v + h v) = (fun v : ℝ => t * v) + h from rfl,
    iteratedDeriv_add h1 h2]
  congr 1
  rw [show (fun v : ℝ => t * v) = fun v => t * id v from rfl,
    iteratedDeriv_const_mul t (f := id) contDiffAt_id, iteratedDeriv_id]
  split_ifs <;> ring

/-- Jet bound for an affine function. -/
private lemma affine_jet_le {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) {δ a t : ℝ}
    (ha : |a| ≤ 1) {k : ℕ} (hk : |iteratedDeriv k h a| ≤ δ) :
    |iteratedDeriv k (fun v : ℝ => t * v + h v) a| ≤ |t| + δ := by
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg _) hk
  rw [affine_jet_eq hh t a k]
  have h1 : |(if k = 0 then t * a else if k = 1 then t else 0)| ≤ |t| := by
    split_ifs with h0 h1'
    · rw [abs_mul]; nlinarith [ha, abs_nonneg t]
    · rfl
    · simpa using abs_nonneg t
  linarith [abs_add_le ((if k = 0 then t * a else if k = 1 then t else 0))
    (iteratedDeriv k h a), abs_nonneg (iteratedDeriv k h a), abs_nonneg t]

/-- Leibniz jet bound for a product. -/
private lemma prod_jet_le {f g : ℝ → ℝ} {a A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {N : ℕ}
    (hf : ∀ k ≤ N, |iteratedDeriv k f a| ≤ A) (hg : ∀ k ≤ N, |iteratedDeriv k g a| ≤ B)
    (hf' : ContDiffAt ℝ N f a) (hg' : ContDiffAt ℝ N g a) {j : ℕ} (hj : j ≤ N) :
    |iteratedDeriv j (f * g) a| ≤ 2 ^ j * (A * B) := by
  rw [iteratedDeriv_mul (hf'.of_le (by exact_mod_cast hj)) (hg'.of_le (by exact_mod_cast hj))]
  calc |∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * iteratedDeriv i f a * iteratedDeriv (j - i) g a|
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (A * B) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
        intro i hi
        rw [Finset.mem_range] at hi
        have hi1 : |iteratedDeriv i f a| ≤ A := hf i (by omega)
        have hi2 : |iteratedDeriv (j - i) g a| ≤ B := hg (j - i) (by omega)
        have hCi : (0:ℝ) ≤ (j.choose i : ℝ) := by positivity
        rw [abs_mul, abs_mul, abs_of_nonneg hCi]
        calc (j.choose i : ℝ) * |iteratedDeriv i f a| * |iteratedDeriv (j - i) g a|
            ≤ (j.choose i : ℝ) * A * B :=
              mul_le_mul (mul_le_mul_of_nonneg_left hi1 hCi) hi2 (abs_nonneg _) (by positivity)
          _ = (j.choose i : ℝ) * (A * B) := by ring
    _ = 2 ^ j * (A * B) := by
        rw [← Finset.sum_mul]
        have h : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
          rw [← Nat.cast_sum, Nat.sum_range_choose]; push_cast; ring
        rw [h]

/-- **Sharp jet bounds for `Zrad`.**  There is a constant `C` (depending only on `n`) such that
for every function `h` that is `δ`-small in `C^{n+2}`, every slope `σ ∈ [0,1]`, every `|t| ≤ 2`
and every `a ∈ [0,1]`, the first `n+2` derivatives of `v ↦ Zrad h (v,σ,t)` at `a` are bounded by
`C`, and their deviation from the corresponding derivatives of the unperturbed radicand
`Zrad 0 (v,σ,t) = (tσ)² - (tv)²` is at most `C δ (|t| + δ)`. -/
theorem Zrad_jet_bounds_sharp (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ → ℝ) (δ : ℝ), ContDiff ℝ (⊤ : ℕ∞) h → 0 ≤ δ → δ ≤ 1 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ δ) →
      ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ t : ℝ, |t| ≤ 2 → ∀ a ∈ Set.Icc (0 : ℝ) 1,
        (∀ j : ℕ, j ≤ n + 2 →
          |iteratedDeriv j (fun v : ℝ => KernelExt.Zrad h (v, σ, t)) a| ≤ C) ∧
        (∀ j : ℕ, j ≤ n + 2 →
          |iteratedDeriv j (fun v : ℝ => KernelExt.Zrad h (v, σ, t)) a -
           iteratedDeriv j (fun v : ℝ => KernelExt.Zrad 0 (v, σ, t)) a| ≤
             C * δ * (|t| + δ)) := by
  refine ⟨2 ^ (n + 6) + 40, by positivity, ?_⟩
  intro h δ hh hδ0 hδ1 hjet σ hσ t ht a ha
  have haabs : |a| ≤ 1 := abs_le.mpr ⟨by linarith [ha.1], ha.2⟩
  have hσabs : |σ| ≤ 1 := abs_le.mpr ⟨by linarith [hσ.1], hσ.2⟩
  have htk : |t| ≤ 3 := by linarith only [ht]
  have hdk : δ ≤ 3 := by linarith only [hδ1]
  have hC4 : (4 : ℝ) ≤ 2 ^ (n + 6) + 40 := by
    have hp : (0:ℝ) ≤ 2 ^ (n + 6) := by positivity
    linarith
  have hC40 : (40 : ℝ) ≤ 2 ^ (n + 6) + 40 := by
    have hp : (0:ℝ) ≤ 2 ^ (n + 6) := by positivity
    linarith
  have h2n : (9 : ℝ) * 2 ^ (n + 2) ≤ 2 ^ (n + 6) + 40 := by
    have h5 : (0:ℝ) < 2 ^ (n + 2) := by positivity
    have h6 : (2:ℝ) ^ (n + 6) = 16 * 2 ^ (n + 2) := by ring
    nlinarith
  have h2n2 : (2 : ℝ) ^ (n + 3) ≤ 2 ^ (n + 6) + 40 := by
    have h5 : (0:ℝ) < 2 ^ (n + 2) := by positivity
    have h6 : (2:ℝ) ^ (n + 6) = 16 * 2 ^ (n + 2) := by ring
    have h7 : (2:ℝ) ^ (n + 3) = 2 * 2 ^ (n + 2) := by ring
    nlinarith
  have hcont : ∀ (k : ℕ) (c : ℝ), ContDiffAt ℝ k (fun v : ℝ => c * v + h v) a := fun k c =>
    (by fun_prop : ContDiffAt ℝ k (fun v : ℝ => c * v) a).add
      (hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top))
  have hFu : (fun v : ℝ => KernelExt.Zrad h (v, σ, t))
      = fun v => (t * σ + h σ) ^ 2 - (t * v + h v) ^ 2 := by
    funext v; simp only [KernelExt.Zrad, line]; ring
  have hF0 : (fun v : ℝ => KernelExt.Zrad 0 (v, σ, t)) = fun v => (t * σ) ^ 2 - (t * v) ^ 2 := by
    funext v; simp only [KernelExt.Zrad, line, Pi.zero_apply]; ring
  have hW : (fun v : ℝ => KernelExt.Zrad h (v, σ, t)) - (fun v : ℝ => KernelExt.Zrad 0 (v, σ, t))
      = fun v => ((t * σ + h σ) ^ 2 - (t * σ) ^ 2) - (h v * (2 * t * v + h v)) := by
    funext v; simp only [Pi.sub_apply, KernelExt.Zrad, line, Pi.zero_apply]; ring
  have hPl : ∀ k ≤ n + 2, |iteratedDeriv k (fun v : ℝ => t * v + h v) a| ≤ |t| + δ :=
    fun k _ => affine_jet_le hh (t := t) haabs (hjet k (by omega) a)
  have hQl : ∀ k ≤ n + 2, |iteratedDeriv k (fun v : ℝ => 2 * t * v + h v) a| ≤ 2 * |t| + δ := by
    intro k hk
    have h2t : |(2 : ℝ) * t| = 2 * |t| := by rw [abs_mul]; norm_num
    have h := affine_jet_le hh (t := 2 * t) (a := a) haabs (k := k) (hjet k (by omega) a)
    rw [h2t] at h
    exact h
  have hsq : ∀ k ≤ n + 2,
      |iteratedDeriv k (fun v : ℝ => (t * v + h v) ^ 2) a| ≤ 2 ^ k * ((|t| + δ) * (|t| + δ)) := by
    intro k hk
    have he : (fun v : ℝ => (t * v + h v) ^ 2)
        = (fun v : ℝ => t * v + h v) * (fun v : ℝ => t * v + h v) := by
      funext v; simp only [Pi.mul_apply]; ring
    rw [he]
    exact prod_jet_le (by positivity) (by positivity) hPl hPl (hcont (n+2) t) (hcont (n+2) t) hk
  constructor
  · -- the values
    intro j hj
    rw [hFu]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [iteratedDeriv_zero]
      have hA : |t * σ + h σ| ≤ 3 := by
        have h1 : |t * σ| ≤ 2 := by rw [abs_mul]; nlinarith [abs_nonneg t, hσabs, ht]
        have h2 : |h σ| ≤ 1 := le_trans (hjet 0 (by omega) σ) hδ1
        have h3 := abs_add_le (t * σ) (h σ); linarith
      have hB : |t * a + h a| ≤ 3 := by
        have h1 : |t * a| ≤ 2 := by rw [abs_mul]; nlinarith [abs_nonneg t, haabs, ht]
        have h2 : |h a| ≤ 1 := le_trans (hjet 0 (by omega) a) hδ1
        have h3 := abs_add_le (t * a) (h a); linarith
      have he : (t * σ + h σ) ^ 2 - (t * a + h a) ^ 2
          = ((t * σ + h σ) + (t * a + h a)) * ((t * σ + h σ) - (t * a + h a)) := by ring
      rw [he, abs_mul]
      have h1 : |(t * σ + h σ) + (t * a + h a)| ≤ 6 := by
        have h3 := abs_add_le (t * σ + h σ) (t * a + h a); linarith
      have h2 : |(t * σ + h σ) - (t * a + h a)| ≤ 6 := by
        have h3 := abs_add_le (t * σ + h σ) (-(t * a + h a))
        rw [abs_neg] at h3
        have he2 : (t * σ + h σ) + -(t * a + h a) = (t * σ + h σ) - (t * a + h a) := by ring
        rw [he2] at h3; linarith
      have h36 : |(t * σ + h σ) + (t * a + h a)| * |(t * σ + h σ) - (t * a + h a)| ≤ 36 := by
        nlinarith [h1, h2, abs_nonneg ((t * σ + h σ) + (t * a + h a)),
          abs_nonneg ((t * σ + h σ) - (t * a + h a))]
      linarith [h36, hC40]
    · have hc : ContDiffAt ℝ (j : ℕ) (fun v : ℝ => (t * v + h v) ^ 2) a := (hcont j t).pow 2
      rw [show (fun v : ℝ => (t * σ + h σ) ^ 2 - (t * v + h v) ^ 2)
        = (fun _ : ℝ => (t * σ + h σ) ^ 2) - (fun v : ℝ => (t * v + h v) ^ 2) from rfl,
        iteratedDeriv_sub contDiffAt_const hc, iteratedDeriv_const, if_neg hj0, zero_sub, abs_neg]
      have h1 : 2 ^ j * ((|t| + δ) * (|t| + δ)) ≤ 9 * 2 ^ (n + 2) := by
        have h2j : (2 : ℝ) ^ j ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
        have h3 : (|t| + δ) * (|t| + δ) ≤ 9 := by nlinarith [htk, hdk, abs_nonneg t, hδ0]
        have hp : (0 : ℝ) ≤ (|t| + δ) * (|t| + δ) := by positivity
        nlinarith [h2j, h3, hp, pow_pos (by norm_num : (0:ℝ) < 2) j]
      linarith [hsq j hj, h1, h2n]
  · -- the deviations
    intro j hj
    have hhAt : ContDiffAt ℝ (j : ℕ) h a := hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    have hc1 : ContDiffAt ℝ (j : ℕ) (fun v : ℝ => KernelExt.Zrad h (v, σ, t)) a := by
      rw [hFu]; exact contDiffAt_const.sub ((hcont j t).pow 2)
    have hc0 : ContDiffAt ℝ (j : ℕ) (fun v : ℝ => KernelExt.Zrad 0 (v, σ, t)) a := by
      rw [hF0]
      exact contDiffAt_const.sub ((by fun_prop : ContDiffAt ℝ (j:ℕ) (fun v : ℝ => t * v) a).pow 2)
    have hkey : iteratedDeriv j (fun v : ℝ => KernelExt.Zrad h (v, σ, t)) a
        - iteratedDeriv j (fun v : ℝ => KernelExt.Zrad 0 (v, σ, t)) a
        = iteratedDeriv j
            (fun v : ℝ => ((t * σ + h σ) ^ 2 - (t * σ) ^ 2) - h v * (2 * t * v + h v)) a := by
      rw [← iteratedDeriv_sub hc1 hc0, hW]
    rw [hkey]
    by_cases hj0 : j = 0
    · subst hj0
      simp only [iteratedDeriv_zero]
      have h2t : |(2 : ℝ) * t| = 2 * |t| := by rw [abs_mul]; norm_num
      have h1 : |(t * σ + h σ) ^ 2 - (t * σ) ^ 2| ≤ 2 * δ * (|t| + δ) := by
        have he : (t * σ + h σ) ^ 2 - (t * σ) ^ 2 = h σ * (2 * t * σ + h σ) := by ring
        rw [he, abs_mul]
        have h2 : |2 * t * σ + h σ| ≤ 2 * (|t| + δ) := by
          have h3 : |2 * t * σ| ≤ 2 * |t| := by rw [abs_mul, h2t]; nlinarith [abs_nonneg t, hσabs]
          have h4 : |h σ| ≤ δ := hjet 0 (by omega) σ
          have h5 := abs_add_le (2 * t * σ) (h σ); linarith
        calc |h σ| * |2 * t * σ + h σ| ≤ δ * (2 * (|t| + δ)) :=
              mul_le_mul (hjet 0 (by omega) σ) h2 (abs_nonneg _) hδ0
          _ = 2 * δ * (|t| + δ) := by ring
      have h3' : |h a * (2 * t * a + h a)| ≤ 2 * δ * (|t| + δ) := by
        rw [abs_mul]
        have h2 : |2 * t * a + h a| ≤ 2 * (|t| + δ) := by
          have h3 : |2 * t * a| ≤ 2 * |t| := by rw [abs_mul, h2t]; nlinarith [abs_nonneg t, haabs]
          have h4 : |h a| ≤ δ := hjet 0 (by omega) a
          have h5 := abs_add_le (2 * t * a) (h a); linarith
        calc |h a| * |2 * t * a + h a| ≤ δ * (2 * (|t| + δ)) :=
              mul_le_mul (hjet 0 (by omega) a) h2 (abs_nonneg _) hδ0
          _ = 2 * δ * (|t| + δ) := by ring
      have hsum : |((t * σ + h σ) ^ 2 - (t * σ) ^ 2) - h a * (2 * t * a + h a)| ≤
          4 * δ * (|t| + δ) := by
        have hA := abs_le.mp h1
        have hB := abs_le.mp h3'
        rw [abs_le]
        constructor <;> linarith [hA.1, hA.2, hB.1, hB.2]
      have hpos : (0:ℝ) ≤ δ * (|t| + δ) := by positivity
      nlinarith [hsum, hC4, hpos]
    · have hg : ContDiffAt ℝ (j : ℕ) (fun v : ℝ => h v * (2 * t * v + h v)) a :=
        hhAt.mul (hcont j (2*t))
      have hkey2 : iteratedDeriv j
          (fun v : ℝ => ((t * σ + h σ) ^ 2 - (t * σ) ^ 2) - h v * (2 * t * v + h v)) a
          = - iteratedDeriv j (fun v : ℝ => h v * (2 * t * v + h v)) a := by
        rw [show (fun v : ℝ => ((t * σ + h σ) ^ 2 - (t * σ) ^ 2) - h v * (2 * t * v + h v))
            = (fun _ : ℝ => ((t * σ + h σ) ^ 2 - (t * σ) ^ 2)) -
              (fun v : ℝ => h v * (2 * t * v + h v)) from rfl,
          iteratedDeriv_sub contDiffAt_const hg, iteratedDeriv_const, if_neg hj0, zero_sub]
      rw [hkey2, abs_neg]
      have hprod : |iteratedDeriv j (fun v : ℝ => h v * (2 * t * v + h v)) a| ≤
          2 ^ j * (δ * (2 * |t| + δ)) :=
        prod_jet_le hδ0 (by positivity) (fun k _ => hjet k (by omega) a) hQl
          (hh.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)) (hcont (n+2) (2*t)) hj
      have h1 : 2 ^ j * (δ * (2 * |t| + δ)) ≤ 2 ^ (n + 3) * δ * (|t| + δ) := by
        have h2j : (2 : ℝ) ^ j ≤ 2 ^ (n + 2) := pow_le_pow_right₀ (by norm_num) (by omega)
        have h2bis : δ * (2 * |t| + δ) ≤ 2 * δ * (|t| + δ) := by
          nlinarith [hδ0, abs_nonneg t, sq_nonneg δ]
        have hp : (0 : ℝ) ≤ δ * (2 * |t| + δ) := by positivity
        have h2n' : (0 : ℝ) ≤ 2 ^ (n + 2) := by positivity
        have step1 : 2 ^ j * (δ * (2 * |t| + δ)) ≤ 2 ^ (n + 2) * (2 * δ * (|t| + δ)) :=
          mul_le_mul h2j h2bis hp h2n'
        rw [show 2 ^ (n + 2) * (2 * δ * (|t| + δ)) = 2 ^ (n + 3) * δ * (|t| + δ) by ring] at step1
        exact step1
      have h2 : 2 ^ (n + 3) * δ * (|t| + δ) ≤ (2 ^ (n + 6) + 40) * δ * (|t| + δ) := by
        have hp : (0 : ℝ) ≤ δ * (|t| + δ) := by positivity
        have h := mul_le_mul_of_nonneg_right h2n2 hp
        calc 2 ^ (n + 3) * δ * (|t| + δ) = 2 ^ (n + 3) * (δ * (|t| + δ)) := by ring
          _ ≤ (2 ^ (n + 6) + 40) * (δ * (|t| + δ)) := h
          _ = (2 ^ (n + 6) + 40) * δ * (|t| + δ) := by ring
      linarith [hprod, h1, h2]

end JetBounds

end

end Work.OddExistence.Manifest.ZS
