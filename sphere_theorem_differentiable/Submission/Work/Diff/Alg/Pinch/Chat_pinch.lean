import Mathlib
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Strict
import Submission.Work.Diff.Alg.Pinch.Chat
import Submission.Work.Diff.Alg.Pinch.Ccone_transversal_a_aux
import Submission.Work.Diff.Alg.Pinch.inPIC2_metric_basic
import Submission.Work.Diff.Alg.q2p_secK_Iso
import Submission.Work.Diff.Alg.Pinch.Chat_err_comp_bound
import Submission.Work.Diff.Alg.Pinch.secK_bound_of_comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Ĉ(s)` pinches as `s → ∞`

The Brendle–Schoen family `Chat n s = Ĉ(s)` (`Submission.Work.Diff.Alg.Pinch.Chat`) of
`O(n)`-invariant cones of algebraic curvature tensors shrinks to the ray `ℝ₊ · Iso` as
`s → ∞`.  Concretely: for every `δ < 1` there is `s` such that every non-zero element of
`Ĉ(s)` is `δ`-pinched.

For `s > 1/2`, `Ĉ(s) = ℓ_{s,1/2}(D(p))`, and for `R ∈ D(p)` the Böhm–Wilking transform splits as

`ℓ_{s,1/2}(R) = (R + (1/2)·ric₀(R) ∧ id) + (2 s · scalAlg R / n) · Iso n`,

using `id ∧ id = 2 Iso` and `ric₀(Iso) = 0`.  The first summand is the "error" tensor: its
components are bounded by `C · scalAlg R` (`Chat_err_comp_bound`, from the component bound
`|Rᵢⱼₖₗ| ≤ 2 scalAlg R` for `InPIC2` tensors), hence its sectional curvatures are bounded by
`C' · scalAlg R` (`secK_bound_of_comp`).  Since `InPIC2` forces `scalAlg R ≥ 0`, while the round
sphere has all sectional curvatures `1`, division by the (large) `Iso` coefficient shows that all
sectional curvatures of `ℓ_{s,1/2}(R)` are within `C'/s` of each other: the pinching ratio
`min/max` tends to `1` as `s → ∞`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Multilinearity of `secK` in the tensor -/

private lemma Chat_secK_add (A B : Curv4 n) (u v : Fin n → ℝ) :
    secK (A + B) u v = secK A u v + secK B u v := by
  simp only [secK, Cone.R4_add_tensor]

private lemma Chat_secK_smul (t : ℝ) (A : Curv4 n) (u v : Fin n → ℝ) :
    secK (t • A) u v = t * secK A u v := by
  simp only [secK, Cone.R4_smul_tensor]

/-- The round sphere has sectional curvature `1` on every orthonormal pair. -/
private lemma Chat_secK_Iso_of_ON {u v : Fin n → ℝ} (h : IsONPair u v) :
    secK (Iso n) u v = 1 :=
  Work.Diff.Alg.q2p_secK_Iso h

/-- The Böhm–Wilking transform `ℓ_{a,1/2}` applied to `R`, split off its `Iso`-component. -/
private lemma Chat_ell_half_eq (a : ℝ) (R : Curv4 n) :
    ell a (1 / 2) R
      = (R + (1 / 2 : ℝ) • knProd (ric0 R) (id2 n)) + (2 * a * scalAlg R / (n : ℝ)) • Iso n := by
  have h : 2 * a * scalAlg R / (n : ℝ) = a / (n : ℝ) * scalAlg R * 2 := by ring
  rw [ell, knProd_id2_id2, smul_smul, ← h]

theorem Chat_pinch (n : ℕ) (hn : 2 ≤ n) :
    ∀ δ : ℝ, δ < 1 → ∃ s : ℝ, 0 < s ∧ ∀ R ∈ Work.Diff.Alg.Pinch.Chat n s,
      R ≠ 0 → Submission.Diff.Alg.IsPinchedAlg δ R := by
  intro δ hδ
  obtain ⟨C₁, hC₁0, hcomp⟩ := Chat_err_comp_bound n
  obtain ⟨Cn, hCn0, hsec⟩ := secK_bound_of_comp n
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  -- the constant `K` bounding `|secK E|` by `K · scalAlg R'`
  set K : ℝ := Cn * C₁ with hK
  have hK0 : 0 ≤ K := by rw [hK]; exact mul_nonneg hCn0 hC₁0
  have h1d : 0 < 1 - δ := by linarith
  -- `S` is chosen so that `2 S/n ≥ K` and `(1 - δ) · 2 S / n ≥ (1 + δ) K`
  set S : ℝ := max 1 (max ((n : ℝ) * K) ((n : ℝ) * (1 + δ) * K / (2 * (1 - δ)) + 1)) with hS
  have hS1 : (1 : ℝ) ≤ S := by rw [hS]; exact le_max_left _ _
  have hSge : (n : ℝ) * K ≤ S := by
    rw [hS]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hSge2 : (n : ℝ) * (1 + δ) * K / (2 * (1 - δ)) + 1 ≤ S := by
    rw [hS]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨S, by linarith, ?_⟩
  intro R hR _
  have hS12 : ¬ S ≤ 1 / 2 := by linarith
  rw [Chat, ite_eq_right hS12] at hR
  simp only [Ccone, Set.mem_image] at hR
  obtain ⟨R', hR'mem, hR'eq⟩ := hR
  obtain ⟨hAlg, hPIC, hRic⟩ := hR'mem
  -- the scalar curvature of `R'` and the `Iso`-free part of `ℓ_{S,1/2}(R')`
  set σ : ℝ := scalAlg R' with hσ
  have hσ0 : 0 ≤ σ := by rw [hσ]; exact (inPIC2_metric_basic n).2.2 R' hPIC
  set E : Curv4 n := R' + (1 / 2 : ℝ) • knProd (ric0 R') (id2 n) with hE
  set L : ℝ := 2 * S / (n : ℝ) with hL
  have hcompE : ∀ i j k l : Fin n, |E i j k l| ≤ C₁ * σ := by
    intro i j k l
    rw [hE, hσ]
    exact hcomp R' hPIC i j k l
  have hsecE : ∀ u v : Fin n → ℝ, IsONPair u v → |secK E u v| ≤ K * σ := by
    intro u v huv
    have h := hsec E σ C₁ hC₁0 hσ0 hcompE u v huv
    rw [hK]
    exact h
  have hEll : ell S (1 / 2) R' = E + (L * σ) • Iso n := by
    have hcoeff : 2 * S * scalAlg R' / (n : ℝ) = L * σ := by rw [hL, hσ]; ring
    rw [Chat_ell_half_eq S R', ← hE, hcoeff]
  have hRdecomp : R = E + (L * σ) • Iso n := by rw [← hR'eq, hEll]
  -- the two conditions on `S`
  have hcond1 : K ≤ L := by
    rw [hL, le_div_iff₀ hn0]
    nlinarith [hSge, hS1, hK0]
  have hcond2 : (1 + δ) * K ≤ (1 - δ) * L := by
    have hden : (0 : ℝ) < 2 * (1 - δ) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hSge2 hden.le
    have hsimp : 2 * (1 - δ) * ((n : ℝ) * (1 + δ) * K / (2 * (1 - δ)) + 1)
        = (n : ℝ) * (1 + δ) * K + 2 * (1 - δ) := by
      field_simp
    rw [hsimp] at hmul
    have hdiv : (1 - δ) * L = (1 - δ) * (2 * S) / (n : ℝ) := by rw [hL]; ring
    rw [hdiv, le_div_iff₀ hn0]
    nlinarith [hmul, hden.le]
  -- the pinching inequality
  intro u v u' v' huv huv'
  have e1 : secK R u v = secK E u v + L * σ := by
    rw [hRdecomp, Chat_secK_add, Chat_secK_smul, Chat_secK_Iso_of_ON huv]
    ring
  have e2 : secK R u' v' = secK E u' v' + L * σ := by
    rw [hRdecomp, Chat_secK_add, Chat_secK_smul, Chat_secK_Iso_of_ON huv']
    ring
  have low : (L - K) * σ ≤ secK R u v := by
    rw [e1]; have := (abs_le.mp (hsecE u v huv)).1; linarith
  have up : secK R u' v' ≤ (L + K) * σ := by
    rw [e2]; have := (abs_le.mp (hsecE u' v' huv')).2; linarith
  have low' : (L - K) * σ ≤ secK R u' v' := by
    rw [e2]; have := (abs_le.mp (hsecE u' v' huv')).1; linarith
  have hLK0 : 0 ≤ (L - K) * σ := mul_nonneg (by linarith) hσ0
  rcases lt_or_ge δ 0 with hδneg | hδ0
  · -- `δ < 0`: both curvatures are `≥ 0` and `δ·(≥ 0) ≤ 0`
    have hnonneg : 0 ≤ secK R u' v' := le_trans hLK0 low'
    have h1 : δ * secK R u' v' ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hδneg.le hnonneg
    have h2 : 0 ≤ secK R u v := le_trans hLK0 low
    linarith
  · -- `δ ≥ 0`: `δ (L + K) σ ≤ (L - K) σ` is exactly `(1 - δ) L ≥ (1 + δ) K`
    have hmid : δ * ((L + K) * σ) ≤ (L - K) * σ := by
      have hkey : δ * (L + K) ≤ L - K := by nlinarith [hcond2]
      calc δ * ((L + K) * σ) = (δ * (L + K)) * σ := by ring
        _ ≤ (L - K) * σ := mul_le_mul_of_nonneg_right hkey hσ0
    calc δ * secK R u' v' ≤ δ * ((L + K) * σ) := mul_le_mul_of_nonneg_left up hδ0
      _ ≤ (L - K) * σ := hmid
      _ ≤ secK R u v := low

end Work.Diff.Alg.Pinch
