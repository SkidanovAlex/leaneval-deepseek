import Mathlib
import Submission.Work.Diff.Alg.Pinch.Chat
import Submission.Work.Diff.Alg.Pinch.Strict
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Ccone_transversal_a_aux
import Submission.Work.Diff.Alg.Pinch.inPIC2_comp_bound
import Submission.Work.Diff.Alg.Pinch.inPIC2_metric_basic
import Submission.Work.Diff.Alg.Pinch.Chat_err_comp_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Brendle–Schoen cones `Ĉ(s)` are asymptotic to the ray `ℝ · Iso`

This file proves that the one-parameter family `Chat n s = Ĉ(s)` of `O(n)`-invariant cones of
algebraic curvature tensors (Brendle–Schoen §3) collapses onto the ray `ℝ · Iso n` as `s → ∞`,
*quantitatively in the norm*: there is a positive function `θ` with `θ s → 0` such that every
`R ∈ Ĉ(s)` is within relative distance `θ s` of the ray:

`Metric.infDist R (Set.range fun μ : ℝ => μ • Iso n) ≤ θ s * ‖R‖`.

For `s > 1/2` the cone is `Ĉ(s) = ℓ_{s,1/2}(D(p))` and the Böhm–Wilking transform splits as

`ℓ_{s,1/2}(R') = (R' + (1/2)·Ric₀(R') ∧ id) + (2s·scalAlg R'/n) · Iso n`,

(`ell_half_eq`, using `id ∧ id = 2 Iso`).  The first summand `E` is the "error" tensor: its
components are bounded by `C₁ · scalAlg R'` for a universal constant `C₁` (`Chat_err_comp_bound`),
so `‖E‖ ≤ C₁ · scalAlg R'` for the sup-norm on `Curv4 n`.  The `Iso` coefficient is
`2s·scalAlg R'/n`, whence

`infDist R (ℝ·Iso) ≤ ‖E‖ ≤ C₁ σ`  and  `‖R‖ ≥ (2s/n)·‖Iso‖·σ - C₁ σ ≥ (2s/n - C₁)·σ`,

with `σ = scalAlg R' ≥ 0` (`inPIC2_metric_basic`).  Dividing, the relative distance is at most
`C₁ / (2s/n - C₁)`, which tends to `0` — the explicit `θ` below is `D/s` for `s ≥ S₀` and `1`
otherwise (for `s` in the bounded range only the trivial bound `infDist ≤ ‖R‖` is used).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Elementary sup-norm facts on `Curv4 n` -/

/-- A bound on all components of a `4`-index array bounds its (sup-)norm. -/
private lemma norm_le_of_comp (f : Curv4 n) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ i j k l, |f i j k l| ≤ r) : ‖f‖ ≤ r := by
  refine (pi_norm_le_iff_of_nonneg hr).2 fun i => ?_
  refine (pi_norm_le_iff_of_nonneg hr).2 fun j => ?_
  refine (pi_norm_le_iff_of_nonneg hr).2 fun k => ?_
  refine (pi_norm_le_iff_of_nonneg hr).2 fun l => ?_
  rw [Real.norm_eq_abs]
  exact h i j k l

/-- The (sup-)norm bounds every component. -/
private lemma norm_comp_le (f : Curv4 n) (i j k l : Fin n) : |f i j k l| ≤ ‖f‖ := by
  have h1 : ‖f i j k l‖ ≤ ‖f i j k‖ := norm_le_pi_norm (f i j k) l
  have h2 : ‖f i j k‖ ≤ ‖f i j‖ := norm_le_pi_norm (f i j) k
  have h3 : ‖f i j‖ ≤ ‖f i‖ := norm_le_pi_norm (f i) j
  have h4 : ‖f i‖ ≤ ‖f‖ := norm_le_pi_norm f i
  rw [Real.norm_eq_abs] at h1
  linarith

/-- Triangle inequality in the form `‖Y‖ - ‖E‖ ≤ ‖E + Y‖`. -/
private lemma norm_sub_norm_le_norm_add (E Y : Curv4 n) : ‖Y‖ - ‖E‖ ≤ ‖E + Y‖ := by
  have h := abs_norm_sub_norm_le E (-Y)
  rw [norm_neg, sub_neg_eq_add] at h
  have h2 : |‖E‖ - ‖Y‖| = |‖Y‖ - ‖E‖| := abs_sub_comm _ _
  rw [h2] at h
  linarith [le_abs_self (‖Y‖ - ‖E‖)]

/-- The round sphere has sup-norm at least `1` (for `n ≥ 2`): the component `Iso n 0 1 0 1` is `1`. -/
private lemma one_le_norm_Iso (hn : 2 ≤ n) : 1 ≤ ‖Iso n‖ := by
  set i : Fin n := ⟨0, by omega⟩ with hi
  set j : Fin n := ⟨1, by omega⟩ with hj
  have h0 : i ≠ j := by
    intro hc
    have : (i : ℕ) = (j : ℕ) := congrArg Fin.val hc
    simp [hi, hj] at this
  have hval : Iso n i j i j = 1 := by
    rw [Iso_eq_id2]
    simp [id2, h0, Ne.symm h0]
  have h1 : ‖Iso n i j i j‖ ≤ ‖Iso n i j i‖ := norm_le_pi_norm (Iso n i j i) j
  have h2 : ‖Iso n i j i‖ ≤ ‖Iso n i j‖ := norm_le_pi_norm (Iso n i j) i
  have h3 : ‖Iso n i j‖ ≤ ‖Iso n i‖ := norm_le_pi_norm (Iso n i) j
  have h4 : ‖Iso n i‖ ≤ ‖Iso n‖ := norm_le_pi_norm (Iso n) i
  rw [Real.norm_eq_abs, hval, abs_one] at h1
  linarith

/-- The Böhm–Wilking transform `ℓ_{a,1/2}` splits off its `Iso`-component. -/
private lemma ell_half_eq (a : ℝ) (R : Curv4 n) :
    ell a (1 / 2) R
      = (R + (1 / 2 : ℝ) • knProd (ric0 R) (id2 n)) + (2 * a * scalAlg R / (n : ℝ)) • Iso n := by
  have h : 2 * a * scalAlg R / (n : ℝ) = a / (n : ℝ) * scalAlg R * 2 := by ring
  rw [ell, knProd_id2_id2, smul_smul, ← h]

/-- The distance to the ray `ℝ · Iso n` is at most the distance to any of its points. -/
private lemma ray_infDist_le (R : Curv4 n) (lam : ℝ) :
    Metric.infDist R (Set.range fun μ : ℝ => μ • Iso n) ≤ ‖R - lam • Iso n‖ := by
  have hmem : (lam • Iso n) ∈ Set.range fun μ : ℝ => μ • Iso n := ⟨lam, rfl⟩
  simpa only [dist_eq_norm] using Metric.infDist_le_dist_of_mem (x := R) hmem

/-- Trivial bound: the distance to the ray is at most `‖R‖` (the ray contains `0`). -/
private lemma ray_infDist_le_norm (R : Curv4 n) :
    Metric.infDist R (Set.range fun μ : ℝ => μ • Iso n) ≤ ‖R‖ := by
  have hmem : (0 : Curv4 n) ∈ Set.range fun μ : ℝ => μ • Iso n := ⟨0, by simp⟩
  simpa only [dist_eq_norm, sub_zero] using Metric.infDist_le_dist_of_mem (x := R) hmem

/-- The scalar inequality behind the relative-distance bound. -/
private lemma arith_aux {c σ s D : ℝ} (hc : 0 ≤ c) (hσ : 0 ≤ σ) (hs : 0 < s)
    (hn : (0 : ℝ) < (n : ℝ)) (hD : D = (c + 1) * ((n : ℝ) + 1))
    (hsbig : c * (c + 1) * ((n : ℝ) + 1) + 1 ≤ s) :
    c * σ ≤ (D / s) * ((2 * s / (n : ℝ) - c) * σ) := by
  have hDc : D * c ≤ s * (c + 2) := by
    rw [hD]
    nlinarith [hsbig, hc, hs]
  have hA : c + 2 ≤ 2 * D / (n : ℝ) - c := by
    rw [le_sub_iff_add_le, le_div_iff₀ hn, hD]
    nlinarith [hc]
  have hmul : (c + 2) * s ≤ (2 * D / (n : ℝ) - c) * s :=
    mul_le_mul_of_nonneg_right hA (le_of_lt hs)
  have hstep : c * s + D * c ≤ 2 * D * s / (n : ℝ) := by
    have hexp : (2 * D / (n : ℝ) - c) * s = 2 * D * s / (n : ℝ) - c * s := by ring
    rw [hexp] at hmul
    linarith
  have hcle : c ≤ (D / s) * (2 * s / (n : ℝ) - c) := by
    have hdiv : (D / s) * (2 * s / (n : ℝ) - c) = (2 * D * s / (n : ℝ) - D * c) / s := by
      field_simp
    rw [hdiv, le_div_iff₀ hs]
    linarith
  calc c * σ ≤ ((D / s) * (2 * s / (n : ℝ) - c)) * σ := mul_le_mul_of_nonneg_right hcle hσ
    _ = (D / s) * ((2 * s / (n : ℝ) - c) * σ) := by ring

theorem Chat_ray_thin (n : ℕ) (hn : 2 ≤ n) :
    ∃ θ : ℝ → ℝ, (∀ s : ℝ, 0 < s → 0 < θ s) ∧
      (∀ δ : ℝ, 0 < δ → ∃ S : ℝ, ∀ s : ℝ, S ≤ s → θ s ≤ δ) ∧
      ∀ s : ℝ, 0 < s → ∀ R : Submission.Diff.Alg.Curv4 n, R ∈ Work.Diff.Alg.Pinch.Chat n s →
        Metric.infDist R (Set.range fun μ : ℝ => μ • Submission.Diff.Alg.Iso n) ≤ θ s * ‖R‖ := by
  obtain ⟨C₁, hC₁0, hcomp⟩ := Chat_err_comp_bound n
  have hscal0 : ∀ R : Curv4 n, InPIC2 R → 0 ≤ scalAlg R :=
    fun R hR => (inPIC2_metric_basic n).2.2 R hR
  set c : ℝ := C₁ with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact hC₁0
  set D : ℝ := (c + 1) * ((n : ℝ) + 1) with hD
  have hDpos : 0 < D := by
    rw [hD]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [hc0]
  set S₀ : ℝ := D * D + 2 with hS₀
  have hS₀D : D ≤ S₀ := by rw [hS₀]; nlinarith [hDpos]
  have hS₀big : c * (c + 1) * ((n : ℝ) + 1) + 1 ≤ S₀ := by
    rw [hS₀, hD]
    nlinarith [hc0]
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  set θ : ℝ → ℝ := (fun s : ℝ => if S₀ ≤ s then D / s else 1) with hθ
  have hθapply : ∀ s : ℝ, θ s = if S₀ ≤ s then D / s else 1 := fun s => by rw [hθ]
  refine ⟨θ, ?_, ?_, ?_⟩
  · intro s hs
    rw [hθapply s]
    by_cases h : S₀ ≤ s
    · rw [ite_eq_left h]; exact div_pos hDpos hs
    · rw [ite_eq_right h]; norm_num
  · intro δ hδ
    refine ⟨max S₀ (D / δ + 1), ?_⟩
    intro s hsle
    rw [hθapply s]
    have hsS₀ : S₀ ≤ s := le_trans (le_max_left _ _) hsle
    rw [ite_eq_left hsS₀]
    have hsDs : D / δ < s := by
      have h2 : D / δ + 1 ≤ s := le_trans (le_max_right _ _) hsle
      linarith
    have hs0 : 0 < s := by
      have hS0pos : 0 < S₀ := by rw [hS₀]; nlinarith [hDpos]
      linarith
    rw [div_le_iff₀ hs0]
    have := (div_lt_iff₀ hδ).mp hsDs
    linarith
  · intro s hs R hR
    rw [hθapply s]
    by_cases hSs : S₀ ≤ s
    · rw [ite_eq_left hSs]
      have hs12 : ¬ s ≤ 1 / 2 := by
        have hS1 : (1 : ℝ) ≤ S₀ := by rw [hS₀]; nlinarith [hDpos]
        linarith
      rw [Chat, ite_eq_right hs12] at hR
      simp only [Ccone, Set.mem_image] at hR
      obtain ⟨R', hR'mem, hR'eq⟩ := hR
      obtain ⟨_hAlg, hPIC, _hRic⟩ := hR'mem
      set σ : ℝ := scalAlg R' with hσ
      have hσ0 : 0 ≤ σ := by rw [hσ]; exact hscal0 R' hPIC
      set E : Curv4 n := R' + (1 / 2 : ℝ) • knProd (ric0 R') (id2 n) with hE
      have hcompE : ∀ i j k l, |E i j k l| ≤ c * σ := by
        intro i j k l
        have h := hcomp R' hPIC i j k l
        rw [hE, hc, hσ]
        exact h
      have hEnorm : ‖E‖ ≤ c * σ := norm_le_of_comp E (mul_nonneg hc0 hσ0) hcompE
      have hdecomp : R = E + (2 * s * σ / (n : ℝ)) • Iso n := by
        rw [← hR'eq, ell_half_eq]
      have hlam0 : 0 ≤ 2 * s * σ / (n : ℝ) :=
        div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hs)) hσ0) (le_of_lt hn0)
      have hnormR : (2 * s * σ / (n : ℝ)) * ‖Iso n‖ - ‖E‖ ≤ ‖R‖ := by
        have h := norm_sub_norm_le_norm_add E ((2 * s * σ / (n : ℝ)) • Iso n)
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam0] at h
        rw [hdecomp]
        exact h
      have hIso1 : 1 ≤ ‖Iso n‖ := one_le_norm_Iso hn
      have hlin : (2 * s / (n : ℝ) - c) * σ ≤ ‖R‖ := by
        have h1 : (2 * s * σ / (n : ℝ)) * 1 - c * σ ≤ (2 * s * σ / (n : ℝ)) * ‖Iso n‖ - ‖E‖ := by
          have := mul_le_mul_of_nonneg_left hIso1 hlam0
          linarith
        have h2 := le_trans h1 hnormR
        have he : (2 * s * σ / (n : ℝ)) * 1 - c * σ = (2 * s / (n : ℝ) - c) * σ := by ring
        rwa [he] at h2
      have hkey : c * σ ≤ (D / s) * ‖R‖ := by
        have h3 : c * σ ≤ (D / s) * ((2 * s / (n : ℝ) - c) * σ) :=
          arith_aux (n := n) hc0 hσ0 hs hn0 hD (le_trans hS₀big hSs)
        have h4 : (D / s) * ((2 * s / (n : ℝ) - c) * σ) ≤ (D / s) * ‖R‖ :=
          mul_le_mul_of_nonneg_left hlin (by positivity)
        linarith
      have hinf : Metric.infDist R (Set.range fun μ : ℝ => μ • Iso n) ≤ c * σ := by
        have h := ray_infDist_le R (2 * s * σ / (n : ℝ))
        have hsub : R - (2 * s * σ / (n : ℝ)) • Iso n = E := by
          rw [hdecomp]; abel
        rw [hsub] at h
        linarith
      linarith
    · rw [ite_eq_right hSs]
      calc Metric.infDist R (Set.range fun μ : ℝ => μ • Iso n) ≤ ‖R‖ := ray_infDist_le_norm R
        _ = 1 * ‖R‖ := by ring

end Work.Diff.Alg.Pinch
