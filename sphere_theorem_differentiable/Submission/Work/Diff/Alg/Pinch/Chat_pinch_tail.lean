import Mathlib
import Submission.Work.Diff.Alg.Pinch.Chat
import Submission.Work.Diff.Alg.Pinch.Chat_pinch
import Submission.Work.Diff.Alg.Pinch.Defs
import Submission.Work.Diff.Alg.Pinch.Chat_err_comp_bound
import Submission.Work.Diff.Alg.Pinch.secK_bound_of_comp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Ĉ(s)` pinches uniformly on the tail `s ≥ s₁`

`Work.Diff.Alg.Pinch.Chat_pinch` shows that for each `δ < 1` there is *one* `S > 0` such that
every non-zero element of `Ĉ(S)` is `δ`-pinched.  What the downstream maximum principle argument
needs is the stronger *tail* statement: there is `s₁ ≥ 1` with the property holding for **all**
`s ≥ s₁`.  No monotonicity of `s ↦ Ĉ(s)` is available (`Chat_mono` is false, see
`Chat_mono_counterexample`), so the statement is proved by re-running the estimate of
`Chat_pinch` with `S` replaced by an arbitrary `s ≥ s₁`.

Recall the mechanism of that estimate: for `s > 1/2` one has `Ĉ(s) = ℓ_{s,1/2}(D(p))` and
`ℓ_{s,1/2}(R') = E + (2s·scalAlg R'/n)·Iso n` with `E := R' + (1/2)·Ric₀(R') ∧ id`.  For
`R' ∈ D(p)` the tensor `E` has scalar-curvature-controlled components, hence sectional curvatures
bounded by `K·scalAlg R'`, while `scalAlg R' ≥ 0`.  Therefore every sectional curvature of
`ℓ_{s,1/2}(R')` lies in `[(2s/n - K)·scalAlg R', (2s/n + K)·scalAlg R']`, and
`δ·(upper) ≤ lower` is implied by the two scalar inequalities `K ≤ 2s/n` and
`(1+δ)K ≤ (1-δ)·2s/n`, both of which hold as soon as `s` is large.  None of this uses the
particular value of `p` other than through membership of `R'` in `D(p)`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Multilinearity of `secK` in the tensor (file-local copies) -/

private lemma ChatTail_secK_add (A B : Curv4 n) (u v : Fin n → ℝ) :
    secK (A + B) u v = secK A u v + secK B u v := by
  simp only [secK, Cone.R4_add_tensor]

private lemma ChatTail_secK_smul (t : ℝ) (A : Curv4 n) (u v : Fin n → ℝ) :
    secK (t • A) u v = t * secK A u v := by
  simp only [secK, Cone.R4_smul_tensor]

/-- The round sphere has sectional curvature `1` on every orthonormal pair. -/
private lemma ChatTail_secK_Iso_of_ON {u v : Fin n → ℝ} (h : IsONPair u v) :
    secK (Iso n) u v = 1 :=
  Work.Diff.Alg.q2p_secK_Iso h

/-- The Böhm–Wilking transform `ℓ_{a,1/2}` applied to `R`, split off its `Iso`-component. -/
private lemma ChatTail_ell_half_eq (a : ℝ) (R : Curv4 n) :
    ell a (1 / 2) R
      = (R + (1 / 2 : ℝ) • knProd (ric0 R) (id2 n)) + (2 * a * scalAlg R / (n : ℝ)) • Iso n := by
  have h : 2 * a * scalAlg R / (n : ℝ) = a / (n : ℝ) * scalAlg R * 2 := by ring
  rw [ell, knProd_id2_id2, smul_smul, ← h]

/-- **Brendle–Schoen Prop. 15 (iii), tail form.**  For every `δ < 1` the whole tail
`Ĉ(s) \ {0}`, `s ≥ s₁`, consists of `δ`-pinched algebraic curvature tensors (i.e. every sectional
curvature is at least `δ` times every other one). -/
theorem Chat_pinch_tail (n : ℕ) (hn : 2 ≤ n) :
    ∀ δ : ℝ, δ < 1 → ∃ s₁ : ℝ, 1 ≤ s₁ ∧ ∀ s : ℝ, s₁ ≤ s →
      ∀ R ∈ Work.Diff.Alg.Pinch.Chat n s, R ≠ 0 → Submission.Diff.Alg.IsPinchedAlg δ R := by
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
  -- `s₁` is chosen so that `2 s/n ≥ K` and `(1 - δ) · 2 s / n ≥ (1 + δ) K` for all `s ≥ s₁`
  set s₁ : ℝ := max 1 (max ((n : ℝ) * K) ((n : ℝ) * (1 + δ) * K / (2 * (1 - δ)) + 1)) with hs₁
  have hs₁1 : (1 : ℝ) ≤ s₁ := by rw [hs₁]; exact le_max_left _ _
  have hs₁ge : (n : ℝ) * K ≤ s₁ := by
    rw [hs₁]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hs₁ge2 : (n : ℝ) * (1 + δ) * K / (2 * (1 - δ)) + 1 ≤ s₁ := by
    rw [hs₁]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨s₁, hs₁1, ?_⟩
  intro s hs R hR _
  have hs1 : (1 : ℝ) ≤ s := le_trans hs₁1 hs
  have hsge : (n : ℝ) * K ≤ s := le_trans hs₁ge hs
  have hsge2 : (n : ℝ) * (1 + δ) * K / (2 * (1 - δ)) + 1 ≤ s := le_trans hs₁ge2 hs
  have hs12 : ¬ s ≤ 1 / 2 := by linarith
  rw [Chat, ite_eq_right hs12] at hR
  simp only [Ccone, Set.mem_image] at hR
  obtain ⟨R', hR'mem, hR'eq⟩ := hR
  obtain ⟨hAlg, hPIC, hRic⟩ := hR'mem
  -- the scalar curvature of `R'` and the `Iso`-free part of `ℓ_{s,1/2}(R')`
  set σ : ℝ := scalAlg R' with hσ
  have hσ0 : 0 ≤ σ := by rw [hσ]; exact (inPIC2_metric_basic n).2.2 R' hPIC
  set E : Curv4 n := R' + (1 / 2 : ℝ) • knProd (ric0 R') (id2 n) with hE
  set L : ℝ := 2 * s / (n : ℝ) with hL
  have hcompE : ∀ i j k l : Fin n, |E i j k l| ≤ C₁ * σ := by
    intro i j k l
    rw [hE, hσ]
    exact hcomp R' hPIC i j k l
  have hsecE : ∀ u v : Fin n → ℝ, IsONPair u v → |secK E u v| ≤ K * σ := by
    intro u v huv
    have h := hsec E σ C₁ hC₁0 hσ0 hcompE u v huv
    rw [hK]
    exact h
  have hEll : ell s (1 / 2) R' = E + (L * σ) • Iso n := by
    have hcoeff : 2 * s * scalAlg R' / (n : ℝ) = L * σ := by rw [hL, hσ]; ring
    rw [ChatTail_ell_half_eq s R', ← hE, hcoeff]
  have hRdecomp : R = E + (L * σ) • Iso n := by rw [← hR'eq, hEll]
  -- the two conditions on `s`
  have hcond1 : K ≤ L := by
    rw [hL, le_div_iff₀ hn0]
    nlinarith [hsge, hs1, hK0]
  have hcond2 : (1 + δ) * K ≤ (1 - δ) * L := by
    have hden : (0 : ℝ) < 2 * (1 - δ) := by linarith
    have hmul := mul_le_mul_of_nonneg_left hsge2 hden.le
    have hsimp : 2 * (1 - δ) * ((n : ℝ) * (1 + δ) * K / (2 * (1 - δ)) + 1)
        = (n : ℝ) * (1 + δ) * K + 2 * (1 - δ) := by
      field_simp
    rw [hsimp] at hmul
    have hdiv : (1 - δ) * L = (1 - δ) * (2 * s) / (n : ℝ) := by rw [hL]; ring
    rw [hdiv, le_div_iff₀ hn0]
    nlinarith [hmul, hden.le]
  -- the pinching inequality
  intro u v u' v' huv huv'
  have e1 : secK R u v = secK E u v + L * σ := by
    rw [hRdecomp, ChatTail_secK_add, ChatTail_secK_smul, ChatTail_secK_Iso_of_ON huv]
    ring
  have e2 : secK R u' v' = secK E u' v' + L * σ := by
    rw [hRdecomp, ChatTail_secK_add, ChatTail_secK_smul, ChatTail_secK_Iso_of_ON huv']
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
