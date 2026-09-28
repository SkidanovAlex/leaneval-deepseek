import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.tau_basic
import Submission.Work.HP.tau_ball_volume

/-!
# `Work.HP.tau_prop_scale`

Scaling and perturbation properties of the archimedean factor
`τ(a;γ) = γ · vol{u ∈ B_{n+1}(1) : a ∈ 𝒞_{ν(u)}^{(γ)}}` (paper (5.2)) and of the predicate
`IPt d n a` ("`f_a` has a real zero on the unit sphere").

Three facts are proved.

* `Cgam_perturb_mem` : if `‖y - a‖ ≤ 1` and `8γ ≤ ‖a‖` (and `γ ≥ 1/4`), then the cone
  `𝒞_{ν(u)}^{(2γ)}` at `y` is contained in the cone `𝒞_{ν(u)}^{(γ)}` at `a`; the point is that
  `‖y‖ ≤ ‖a‖ + 1 ≤ 2‖a‖ - 4γ`, so Cauchy--Schwarz gives
  `|⟨ν(u),a⟩| ≤ ‖ν(u)‖‖y‖/(4γ) + ‖ν(u)‖ ≤ ‖ν(u)‖‖a‖/(2γ)`.
* `Cgam_full_of_le_half` : for `γ ≤ 1/2` the cone `𝒞_v^{(γ)}` is all of space (Cauchy--Schwarz
  alone gives `|⟨v,t⟩| ≤ ‖v‖‖t‖ ≤ ‖v‖‖t‖/(2γ)`).
* `tau_prop_scale` itself, the target lemma: the first conjunct follows by splitting on
  `γ ≤ 1/2` (where the relevant measure is the one of the whole unit ball) versus `1/2 ≤ γ`
  (where the two relevant sets are nested, so `measure_mono` applies); the second and third
  conjuncts are the exact homogeneity of `τ` and of `IPt` in the form.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory MvPolynomial

namespace Work.HP

/-- Triangle inequality for `|·|` on `ℝ`. -/
lemma abs_add_le' {a b : ℝ} : |a + b| ≤ |a| + |b| :=
  abs_le.mpr ⟨by linarith [neg_abs_le a, neg_abs_le b],
    by linarith [le_abs_self a, le_abs_self b]⟩

/-- For `γ ≤ 1/2` the cone `𝒞_v^{(γ)}` is the whole space, by Cauchy--Schwarz. -/
lemma Cgam_full_of_le_half {d n : ℕ} (a : Mon d n → ℝ) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ ≤ 1 / 2)
    (u : Fin (n + 1) → ℝ) : a ∈ Cgam (veronese d n u) γ := by
  show |dotR (veronese d n u) a| ≤ rNorm (veronese d n u) * rNorm a / (2 * γ)
  have hP : 0 ≤ rNorm (veronese d n u) * rNorm a :=
    mul_nonneg (rNorm_nonneg _) (rNorm_nonneg a)
  have hc : (0 : ℝ) < 2 * γ := by linarith
  calc |dotR (veronese d n u) a| ≤ rNorm (veronese d n u) * rNorm a := abs_dotR_le _ _
    _ = rNorm (veronese d n u) * rNorm a * 1 := by ring
    _ ≤ rNorm (veronese d n u) * rNorm a * (1 / (2 * γ)) := by
        refine mul_le_mul_of_nonneg_left ?_ hP
        rw [one_le_div hc]
        linarith
    _ = rNorm (veronese d n u) * rNorm a / (2 * γ) := by ring

/-- Cone stability: if `y` is within distance `1` of `a` and `8γ ≤ ‖a‖`, then membership of the
cone at `y` with parameter `2γ` implies membership at `a` with parameter `γ`. -/
lemma Cgam_perturb_mem {d n : ℕ} (a y : Mon d n → ℝ) (γ : ℝ) (hγ : 0 < γ) (hγ4 : 1 / 4 ≤ γ)
    (h8 : 8 * γ ≤ rNorm a) (h1 : rNorm (y - a) ≤ 1) (u : Fin (n + 1) → ℝ)
    (hy : y ∈ Cgam (veronese d n u) (2 * γ)) : a ∈ Cgam (veronese d n u) γ := by
  have h2γ : (0 : ℝ) < 2 * γ := by linarith
  have h4γ : (0 : ℝ) < 4 * γ := by linarith
  have hν : 0 ≤ rNorm (veronese d n u) := rNorm_nonneg _
  -- Cauchy--Schwarz bounds, kept in multiplied form to avoid division
  have hCSy : |dotR (veronese d n u) y| * (4 * γ) ≤ rNorm (veronese d n u) * rNorm y := by
    refine (le_div_iff₀ h4γ).mp ?_
    have h : |dotR (veronese d n u) y| ≤ rNorm (veronese d n u) * rNorm y / (2 * (2 * γ)) := hy
    rwa [show 2 * (2 * γ) = 4 * γ by ring] at h
  have hCSa : |dotR (veronese d n u) (a - y)| ≤ rNorm (veronese d n u) := by
    have h2' : rNorm (a - y) ≤ 1 := by rw [rNorm_sub_comm]; exact h1
    calc |dotR (veronese d n u) (a - y)| ≤ rNorm (veronese d n u) * rNorm (a - y) :=
          abs_dotR_le _ _
      _ ≤ rNorm (veronese d n u) * 1 := mul_le_mul_of_nonneg_left h2' hν
      _ = rNorm (veronese d n u) := mul_one _
  have hsplit : dotR (veronese d n u) a
      = dotR (veronese d n u) y + dotR (veronese d n u) (a - y) := by
    rw [← dotR_add_right, show y + (a - y) = a by ext i; simp]
  have htri : |dotR (veronese d n u) a|
      ≤ |dotR (veronese d n u) y| + |dotR (veronese d n u) (a - y)| := by
    rw [hsplit]; exact abs_add_le'
  have hrmy : rNorm y ≤ rNorm a + rNorm (y - a) := rNorm_le_add_sub y a
  have hmain : rNorm y + 4 * γ ≤ 2 * rNorm a := by
    have h4γ1 : (1 : ℝ) + 4 * γ ≤ rNorm a := by linarith
    linarith
  -- conclude after multiplying by `2γ`
  show |dotR (veronese d n u) a| ≤ rNorm (veronese d n u) * rNorm a / (2 * γ)
  rw [le_div_iff₀ h2γ]
  have hA : |dotR (veronese d n u) a| * (2 * γ)
      ≤ (|dotR (veronese d n u) y| + |dotR (veronese d n u) (a - y)|) * (2 * γ) :=
    mul_le_mul_of_nonneg_right htri h2γ.le
  have hB : |dotR (veronese d n u) y| * (2 * γ)
      ≤ rNorm (veronese d n u) * rNorm y / 2 := by
    linarith [hCSy]
  have hC : |dotR (veronese d n u) (a - y)| * (2 * γ) ≤ rNorm (veronese d n u) * (2 * γ) :=
    mul_le_mul_of_nonneg_right hCSa h2γ.le
  have hD : rNorm (veronese d n u) * rNorm y / 2 + rNorm (veronese d n u) * (2 * γ)
      ≤ rNorm (veronese d n u) * rNorm a := by
    have hh := mul_le_mul_of_nonneg_left hmain hν
    linarith [hh]
  linarith [hA, hB, hC, hD]

theorem tau_prop_scale (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) :
    (∀ (a y : Mon d n → ℝ) (γ : ℝ), 0 < γ → 8 * γ ≤ rNorm a → rNorm (y - a) ≤ 1 →
        tauArch d n y (2 * γ) ≤ 2 * tauArch d n a γ) ∧
    (∀ (a : Mon d n → ℝ) (γ t : ℝ), 0 < t → tauArch d n (t • a) γ = tauArch d n a γ) ∧
    (∀ (a : Mon d n → ℝ) (t : ℝ), 0 < t → (IPt d n (t • a) ↔ IPt d n a)) := by
  have hball := tau_ball_volume (n + 1)
  refine ⟨?_, ?_, ?_⟩
  · intro a y γ hγ h8 h1
    -- compare the volumes of the two threshold sets
    have hvol : (volume {u : Fin (n + 1) → ℝ | rNorm u ≤ 1 ∧
            y ∈ Cgam (veronese d n u) (2 * γ)}).toReal
        ≤ (volume {u : Fin (n + 1) → ℝ | rNorm u ≤ 1 ∧
            a ∈ Cgam (veronese d n u) γ}).toReal := by
      by_cases h12 : (1 / 2 : ℝ) ≤ γ
      · -- `γ ≥ 1/2 ≥ 1/4`: the second set contains the first
        refine ENNReal.toReal_mono ?_ (measure_mono ?_)
        · refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_) hball)
          intro u hu
          exact hu.1
        · intro u hu
          exact ⟨hu.1, Cgam_perturb_mem a y γ hγ (by linarith) h8 h1 u hu.2⟩
      · -- `γ ≤ 1/2`: the second set is the whole unit ball
        have hγ2 : γ ≤ 1 / 2 := le_of_lt (not_le.mp h12)
        have hfull : {u : Fin (n + 1) → ℝ | rNorm u ≤ 1 ∧ a ∈ Cgam (veronese d n u) γ}
            = {u : Fin (n + 1) → ℝ | rNorm u ≤ 1} := by
          ext u
          refine ⟨fun hu => hu.1, fun hu => ⟨hu, Cgam_full_of_le_half a hγ hγ2 u⟩⟩
        rw [hfull]
        exact ENNReal.toReal_mono (ne_of_lt hball) (measure_mono fun u hu => hu.1)
    rw [tauArch, tauArch]
    have hmul := mul_le_mul_of_nonneg_left hvol (by linarith : (0 : ℝ) ≤ 2 * γ)
    rw [show (2 : ℝ) * (γ * (volume {u : Fin (n + 1) → ℝ | rNorm u ≤ 1 ∧
          a ∈ Cgam (veronese d n u) γ}).toReal)
        = (2 * γ) * (volume {u : Fin (n + 1) → ℝ | rNorm u ≤ 1 ∧
          a ∈ Cgam (veronese d n u) γ}).toReal by ring]
    exact hmul
  · intro a γ t ht
    -- `a ↦ t • a` does not change the threshold set when `t > 0`
    have hset : {u : Fin (n + 1) → ℝ | rNorm u ≤ 1 ∧ t • a ∈ Cgam (veronese d n u) γ}
        = {u : Fin (n + 1) → ℝ | rNorm u ≤ 1 ∧ a ∈ Cgam (veronese d n u) γ} := by
      ext u
      refine ⟨fun hu => ⟨hu.1, ?_⟩, fun hu => ⟨hu.1, ?_⟩⟩
      · have h' : |dotR (veronese d n u) (t • a)|
            ≤ rNorm (veronese d n u) * rNorm (t • a) / (2 * γ) := hu.2
        rw [dotR_smul_right, rNorm_smul_of_pos t a ht, abs_mul, abs_of_pos ht] at h'
        show |dotR (veronese d n u) a| ≤ rNorm (veronese d n u) * rNorm a / (2 * γ)
        have heq : rNorm (veronese d n u) * (t * rNorm a) / (2 * γ)
            = t * (rNorm (veronese d n u) * rNorm a / (2 * γ)) := by ring
        rw [heq] at h'
        exact le_of_mul_le_mul_left h' ht
      · have h : |dotR (veronese d n u) a| ≤ rNorm (veronese d n u) * rNorm a / (2 * γ) := hu.2
        have h2 : t * |dotR (veronese d n u) a|
            ≤ t * (rNorm (veronese d n u) * rNorm a / (2 * γ)) :=
          mul_le_mul_of_nonneg_left h ht.le
        show |dotR (veronese d n u) (t • a)| ≤ rNorm (veronese d n u) * rNorm (t • a) / (2 * γ)
        rw [dotR_smul_right, rNorm_smul_of_pos t a ht, abs_mul, abs_of_pos ht]
        rw [show rNorm (veronese d n u) * (t * rNorm a) / (2 * γ)
            = t * (rNorm (veronese d n u) * rNorm a / (2 * γ)) by ring]
        exact h2
    rw [tauArch, tauArch, hset]
  · intro a t ht
    -- `f_{t•a} = t · f_a`, so the zero set on the unit sphere is unchanged for `t > 0`
    constructor
    · rintro ⟨x, hx, hf⟩
      exact ⟨x, hx, by
        have h := formEvalR_smul d n a x t
        rw [h] at hf
        exact (mul_eq_zero.mp hf).resolve_left ht.ne'⟩
    · rintro ⟨x, hx, hf⟩
      exact ⟨x, hx, by rw [formEvalR_smul, hf, mul_zero]⟩

end Work.HP
