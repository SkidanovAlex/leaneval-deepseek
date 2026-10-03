import Mathlib
import Submission.Work.Peluse.Holds.LadderP
import Submission.Work.Peluse.Pel51.badP_regime_one
import Submission.Work.Peluse.Pel51.badP_regime_two
import Submission.Work.Peluse.Pel51.boxNorm_two_ge_of_one_two_dirs
import Submission.Work.Peluse.Pel51.dirBound
import Submission.Work.Peluse.Pel51.arithHelp

/-!
# `lemma51P 2 → lemma51P 1`: Peluse's Lemma 5.1 at level `1` from level `2`

**Read `Submission/Work/Peluse/Pel51/defs.lean` first** — it records the mechanism and why this
removes the analytic heart `LadderP.lemma54P` (P1) from the critical path of the node
`Work.Peluse.ucontrol_of_concat`.

The level raising `levelRaiseAppendBd` (the Gowers–Cauchy–Schwarz step, whose direction bound is
needed only on the *appended* direction) shows that the level-`2` box-norm average at the padded
direction family `(b₀, b₁)` dominates the level-`1` average at `b₀`, at the price of an absolute
constant `(1/(4*Cw))^{1/4}` (the ambient window is enlarged from `symIcc N` to `symIcc (Cw*N)`, and
the box norm rescales exactly by `|S|`).  Choosing the padding `b₁` and the level-`2` exceptional
parameter `ε₂` according to the two regimes of the bad set (`badP_regime_one`, `badP_regime_two`)
supplies every hypothesis of `lemma51P 2`, and the conclusion transfers because the conclusion of
`lemma51P` is level-independent.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.Pel51

open Work.Peluse

open Work.Peluse.LadderP (lemma51P)

/-- The body of `lemma51P 2` after unfolding the existential over `s', e, C`, with the bad set
written as `badP 2` (definitionally the `filter` of the frozen statement). -/
def L2Clause (B₀ : ℕ) (s' e : ℕ) (C₂ : ℝ) : Prop :=
  ∀ (c : ℤ) (M₁ M₂ N D : ℕ) (b : Fin 2 → ℤ) (γ η ε : ℝ) (f : ℤ → ℂ),
    0 < c → 2 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → ((M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ)) → 1 ≤ D →
    (∀ i : Fin 2, |b i| ≤ ((B₀ : ℕ) : ℤ) * (M₁ : ℤ)) →
    SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
    0 < γ → γ ≤ 1 → 0 < η → η ≤ C₂ * γ ^ e → 0 ≤ ε → ε ≤ C₂ * γ ^ e →
    (D : ℝ) ≤ C₂ * (γ * η) ^ e * ((M₁ : ℝ) * (M₂ : ℝ)) →
    ((M₁ : ℝ) * (M₂ : ℝ)) ^ e ≤ C₂ * (γ * η * (D : ℝ)) ^ e * (M₂ : ℝ) →
    ((badP 2 M₁ b η).card : ℝ) ≤ ε * (M₁ : ℝ) →
    γ ≤ LadderQ.boxAvgA 2 c M₁ M₂ b N f →
    C₂ * γ ^ e ≤ uNorm s' (arithIcc c D) (symIcc N) f

/-- **The padded box-norm average inequality**: the level-`2` average at the family padded from
`b` by `b'` dominates the level-`1` average at `b`, with the absolute constant
`(1/(4*Cw))^{1/4}`, provided the *appended* direction `b' 1` stays inside `[-Cw*N, Cw*N]`. -/
theorem boxAvgA_one_le_two {Cw : ℕ} (hCw : 1 ≤ Cw) (c : ℤ) (hc : 0 < c) (M₁ M₂ N : ℕ)
    (b : Fin 1 → ℤ) (b' : Fin 2 → ℤ) {f : ℤ → ℂ} (hM2 : 2 ≤ M₂) (hN : 1 ≤ N)
    (hb0 : b' 0 = b 0) (hsup : SupportIn f N)
    (hbd : ∀ a ∈ Finset.Icc 1 M₁, ∀ z : ℤ, z ∈ arithIcc (c * ((a : ℤ) + b' 1)) M₂ →
      |z| ≤ ((Cw : ℕ) : ℤ) * (N : ℤ)) :
    ((1 : ℝ) / (4 * (Cw : ℝ))) ^ (1 / 4 : ℝ)
        * LadderQ.boxAvgA 1 c M₁ M₂ b N f
      ≤ LadderQ.boxAvgA 2 c M₁ M₂ b' N f := by
  have hM2' : 1 ≤ M₂ := le_trans (by norm_num) hM2
  have hbd' : ∀ a ∈ Finset.Icc 1 M₁, ∀ z : ℤ, z ∈ arithIcc (c * ((a : ℤ) + b' 1)) M₂ →
      |z| ≤ ((Cw * N : ℕ) : ℤ) := by
    intro a ha z hz
    have h2 : (((Cw : ℕ)) : ℤ) * (N : ℤ) = ((Cw * N : ℕ) : ℤ) := by push_cast; ring
    exact le_trans (hbd a ha z hz) (le_of_eq h2)
  rw [LadderQ.boxAvgA, LadderQ.boxAvgA]
  have hmul : ((1 : ℝ) / (4 * (Cw : ℝ))) ^ (1 / 4 : ℝ)
        * (((M₁ : ℝ))⁻¹ * ∑ a ∈ Finset.Icc 1 M₁,
            boxNorm 1 (fun i : Fin 1 => arithIcc (c * ((a : ℤ) + b i)) M₂) (symIcc N) f)
      = ((M₁ : ℝ))⁻¹ * (((1 : ℝ) / (4 * (Cw : ℝ))) ^ (1 / 4 : ℝ)
          * ∑ a ∈ Finset.Icc 1 M₁,
            boxNorm 1 (fun i : Fin 1 => arithIcc (c * ((a : ℤ) + b i)) M₂) (symIcc N) f) := by
    ring
  rw [hmul, Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine Finset.sum_le_sum (fun a ha => ?_)
  have hQ0 : (fun i : Fin 1 => arithIcc (c * ((a : ℤ) + b i)) M₂)
      = (fun _ : Fin 1 => arithIcc (c * ((a : ℤ) + b 0)) M₂) := by
    funext i
    rw [Subsingleton.elim i 0]
  have hfam : (fun i : Fin 2 => arithIcc (c * ((a : ℤ) + b' i)) M₂)
      = (fun i : Fin 2 => if i = 0 then arithIcc (c * ((a : ℤ) + b 0)) M₂
          else arithIcc (c * ((a : ℤ) + b' 1)) M₂) := by
    funext i
    by_cases hi : i = 0
    · rw [if_pos hi, hi, hb0]
    · rw [if_neg hi]
      congr 1
      have h2 : i = 1 := by
        ext
        have := i.isLt
        omega
      rw [h2]
  rw [hQ0, hfam]
  exact boxNorm_two_ge_of_one_two_dirs (Cw := Cw) hCw
    (arithIcc_nonempty (d := c * ((a : ℤ) + b 0)) hM2')
    (arithIcc_nonempty (d := c * ((a : ℤ) + b' 1)) hM2')
    hN (hbd' a ha) hsup

/-- **The shared core of the transfer.**  Given the level-`2` clause at `(B₀+1, s', e₂, C₂)`, the
level-`1` datum, and the regime-specific padding data (`b'`, `ε₂`, the direction bound, the padded
bad-set bound and the level-`2` `ε`-bound), produce the level-`1` conclusion. -/
theorem transfer_core {B₀ : ℕ} {s' e₂ : ℕ} {C₂ : ℝ} {c₀ C : ℝ}
    (h2' : L2Clause (B₀ + 1) s' e₂ C₂)
    (hc₀0 : 0 < c₀) (hc₀1 : c₀ ≤ 1) (hC₂0 : 0 < C₂) (hCC : C ≤ C₂ * c₀ ^ e₂)
    {c : ℤ} {M₁ M₂ N D : ℕ} {b : Fin 1 → ℤ} {b' : Fin 2 → ℤ} {γ η ε₂ : ℝ} {f : ℤ → ℂ}
    {Cw : ℕ} (hCw : 1 ≤ Cw) (hc₀eq : c₀ = ((1 : ℝ) / (4 * (Cw : ℝ))) ^ (1 / 4 : ℝ))
    (hc : 0 < c) (hM2 : 2 ≤ M₂) (hM2M1 : M₂ ≤ M₁) (hN : 1 ≤ N)
    (hNM : (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ)) (hD : 1 ≤ D)
    (hb0 : b' 0 = b 0)
    (hbb' : ∀ i : Fin 2, |b' i| ≤ (((B₀ + 1 : ℕ)) : ℤ) * (M₁ : ℤ))
    (hsup : SupportIn f N) (hbdd : ∀ x : ℤ, ‖f x‖ ≤ 1)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hη0 : 0 < η)
    (hηC : η ≤ C * γ ^ e₂) (hε₂0 : 0 ≤ ε₂) (hε₂C : ε₂ ≤ C₂ * c₀ ^ e₂ * γ ^ e₂)
    (hDC : (D : ℝ) ≤ C * (γ * η) ^ e₂ * ((M₁ : ℝ) * (M₂ : ℝ)))
    (hDND : ((M₁ : ℝ) * (M₂ : ℝ)) ^ e₂ ≤ C * (γ * η * (D : ℝ)) ^ e₂ * (M₂ : ℝ))
    (hdir : ∀ a ∈ Finset.Icc 1 M₁, ∀ z : ℤ, z ∈ arithIcc (c * ((a : ℤ) + b' 1)) M₂ →
      |z| ≤ ((Cw : ℕ) : ℤ) * (N : ℤ))
    (hcard2 : ((badP 2 M₁ b' η).card : ℝ) ≤ ε₂ * (M₁ : ℝ))
    (hbox : γ ≤ LadderQ.boxAvgA 1 c M₁ M₂ b N f) :
    C * γ ^ e₂ ≤ uNorm s' (arithIcc c D) (symIcc N) f := by
  -- the padded level-two box average dominates `c₀ * γ`
  have hstep := boxAvgA_one_le_two (Cw := Cw) hCw c hc M₁ M₂ N b b' hM2 hN hb0 hsup hdir
  rw [← hc₀eq] at hstep
  have hbox2 : c₀ * γ ≤ LadderQ.boxAvgA 2 c M₁ M₂ b' N f :=
    le_trans (mul_le_mul_of_nonneg_left hbox (le_of_lt hc₀0)) hstep
  -- arithmetic
  have hγ₂pos : 0 < c₀ * γ := mul_pos hc₀0 hγ0
  have hγ₂1 : c₀ * γ ≤ 1 := by nlinarith [hc₀1, hγ0, hγ1]
  have hγe : 0 ≤ γ ^ e₂ := pow_nonneg (le_of_lt hγ0) e₂
  have hη2 : η ≤ C₂ * (c₀ * γ) ^ e₂ := by
    have h1 : C₂ * (c₀ * γ) ^ e₂ = (C₂ * c₀ ^ e₂) * γ ^ e₂ := by rw [mul_pow]; ring
    rw [h1]
    exact le_trans hηC (mul_le_mul_of_nonneg_right hCC hγe)
  have hε2 : ε₂ ≤ C₂ * (c₀ * γ) ^ e₂ := by
    have h1 : C₂ * (c₀ * γ) ^ e₂ = (C₂ * c₀ ^ e₂) * γ ^ e₂ := by rw [mul_pow]; ring
    rw [h1]
    exact hε₂C
  have hDC2 : (D : ℝ) ≤ C₂ * ((c₀ * γ) * η) ^ e₂ * ((M₁ : ℝ) * (M₂ : ℝ)) := by
    have h1 : ((c₀ * γ) * η) ^ e₂ = c₀ ^ e₂ * (γ * η) ^ e₂ := by
      rw [show (c₀ * γ) * η = c₀ * (γ * η) by ring, mul_pow]
    calc (D : ℝ) ≤ C * (γ * η) ^ e₂ * ((M₁ : ℝ) * (M₂ : ℝ)) := hDC
      _ = C * ((γ * η) ^ e₂ * ((M₁ : ℝ) * (M₂ : ℝ))) := by ring
      _ ≤ (C₂ * c₀ ^ e₂) * ((γ * η) ^ e₂ * ((M₁ : ℝ) * (M₂ : ℝ))) :=
          mul_le_mul_of_nonneg_right hCC (by positivity)
      _ = C₂ * ((c₀ * γ) * η) ^ e₂ * ((M₁ : ℝ) * (M₂ : ℝ)) := by rw [h1]; ring
  have hDND2 : ((M₁ : ℝ) * (M₂ : ℝ)) ^ e₂ ≤
      C₂ * ((c₀ * γ) * η * (D : ℝ)) ^ e₂ * (M₂ : ℝ) := by
    have h1 : ((c₀ * γ) * η * (D : ℝ)) ^ e₂ = c₀ ^ e₂ * (γ * η * (D : ℝ)) ^ e₂ := by
      rw [show (c₀ * γ) * η * (D : ℝ) = c₀ * (γ * η * (D : ℝ)) by ring, mul_pow]
    calc ((M₁ : ℝ) * (M₂ : ℝ)) ^ e₂ ≤ C * (γ * η * (D : ℝ)) ^ e₂ * (M₂ : ℝ) := hDND
      _ = C * ((γ * η * (D : ℝ)) ^ e₂ * (M₂ : ℝ)) := by ring
      _ ≤ (C₂ * c₀ ^ e₂) * ((γ * η * (D : ℝ)) ^ e₂ * (M₂ : ℝ)) :=
          mul_le_mul_of_nonneg_right hCC (by positivity)
      _ = C₂ * ((c₀ * γ) * η * (D : ℝ)) ^ e₂ * (M₂ : ℝ) := by rw [h1]; ring
  -- apply the level-two clause
  have hmain := h2' c M₁ M₂ N D b' (c₀ * γ) η ε₂ f hc hM2 hM2M1 hN hNM hD hbb' hsup hbdd
    hγ₂pos hγ₂1 hη0 hη2 hε₂0 hε2 hDC2 hDND2 hcard2 hbox2
  -- conclude, absorbing `c₀^{e₂}`
  have hgoal : C * γ ^ e₂ ≤ C₂ * (c₀ * γ) ^ e₂ := by
    rw [mul_pow]
    calc C * γ ^ e₂ ≤ (C₂ * c₀ ^ e₂) * γ ^ e₂ := mul_le_mul_of_nonneg_right hCC hγe
      _ = C₂ * (c₀ ^ e₂ * γ ^ e₂) := by ring
  exact le_trans hgoal hmain

/-- **Peluse's Lemma 5.1 at level `1` follows from level `2`.**

This is the theorem that removes `LadderP.lemma54P` (P1, the analytic heart of the ladder) from the
critical path: `lemma51P_all` then needs only P2 and P3. -/
theorem lemma51P_one_of_two (h2 : lemma51P 2) : lemma51P 1 := by
  intro B₀
  obtain ⟨s', hs'1, e₂, he₂1, C₂, hC₂pos, hC₂le1, hmain⟩ := h2 (B₀ + 1)
  have h2' : L2Clause (B₀ + 1) s' e₂ C₂ := hmain
  have hCw1 : 1 ≤ B₀ + 2 := by omega
  set c₀ : ℝ := ((1 : ℝ) / (4 * (((B₀ + 2 : ℕ)) : ℝ))) ^ (1 / 4 : ℝ) with hc₀def
  have hc₀0 : 0 < c₀ := by rw [hc₀def]; positivity
  have hbase1 : (1 : ℝ) / (4 * (((B₀ + 2 : ℕ)) : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have h4 : (1 : ℝ) ≤ (((B₀ + 2 : ℕ)) : ℝ) := by exact_mod_cast (by omega : 1 ≤ B₀ + 2)
    nlinarith [h4]
  have hbase0 : (0 : ℝ) ≤ (1 : ℝ) / (4 * (((B₀ + 2 : ℕ)) : ℝ)) := by positivity
  have hc₀1 : c₀ ≤ 1 := by
    rw [hc₀def]
    exact Real.rpow_le_one hbase0 hbase1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hc₀eq : c₀ = ((1 : ℝ) / (4 * (((B₀ + 2 : ℕ)) : ℝ))) ^ (1 / 4 : ℝ) := hc₀def
  set C : ℝ := min 1 (min (C₂ * c₀ ^ e₂) (C₂ * c₀ ^ e₂ / (2 * ((B₀ : ℝ) + 1)))) with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    exact lt_min one_pos (lt_min (by positivity) (by positivity))
  have hCle1 : C ≤ 1 := by rw [hCdef]; exact min_le_left _ _
  have hCC : C ≤ C₂ * c₀ ^ e₂ := by
    rw [hCdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hCC2 : C ≤ C₂ * c₀ ^ e₂ / (2 * ((B₀ : ℝ) + 1)) := by
    rw [hCdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨s', hs'1, e₂, he₂1, C, hCpos, hCle1, ?_⟩
  intro c M₁ M₂ N D b γ η ε f hc hM2 hM2M1 hN hNM hD hb hsup hbdd hγ0 hγ1 hη0 hηC hε0 hεC
    hDC hDND hcard hbox
  have hM1 : 1 ≤ M₁ := le_trans (by omega) hM2M1
  have hM₁pos : (0 : ℝ) < (M₁ : ℝ) := by positivity
  have hcard1 : ((badP 1 M₁ b η).card : ℝ) ≤ ε * (M₁ : ℝ) := hcard
  have hb_eq : (fun _ : Fin 1 => b 0) = b := by
    funext i
    exact (congrArg b (Subsingleton.elim i 0)).symm
  have hb0 : |b 0| ≤ (B₀ : ℤ) * (M₁ : ℤ) := hb 0
  have hη1 : η ≤ 1 := eta_le_one hγ0 hγ1 hCle1 hηC
  have hcM₁M₂ : c * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ) := by
    have hcpos : (0 : ℝ) < (c : ℝ) := by exact_mod_cast hc
    have h1 : (c : ℝ) * ((M₁ : ℝ) * (M₂ : ℝ)) ≤ (c : ℝ) * ((N : ℝ) / (c : ℝ)) :=
      mul_le_mul_of_nonneg_left hNM (le_of_lt hcpos)
    have h2 : (c : ℝ) * ((N : ℝ) / (c : ℝ)) = (N : ℝ) := by
      rw [div_eq_mul_inv, ← mul_assoc, mul_comm (c : ℝ) (N : ℝ), mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hcpos), mul_one]
    rw [h2] at h1
    have h1' : (c : ℝ) * (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) := by
      have h3 : (c : ℝ) * (M₁ : ℝ) * (M₂ : ℝ) = (c : ℝ) * ((M₁ : ℝ) * (M₂ : ℝ)) := by ring
      rw [h3]; exact h1
    exact_mod_cast h1'
  have hb1 : |b 0| ≤ (((B₀ + 1 : ℕ)) : ℤ) * (M₁ : ℤ) := abs_le_succ_mul hb0
  have hb2 : |b 0 + 1| ≤ (((B₀ + 1 : ℕ)) : ℤ) * (M₁ : ℤ) := abs_add_one_le_succ_mul hM1 hb0
  by_cases hreg : η * (M₁ : ℝ) * ((B₀ : ℝ) + 1) ≤ 1
  · -- Regime 1: pad by `b 0`; the bad sets are comparable with the same parameters
    have hb0' : (fun _ : Fin 2 => b 0) 0 = b 0 := rfl
    have hbb' : ∀ i : Fin 2, |(fun _ : Fin 2 => b 0) i| ≤ (((B₀ + 1 : ℕ)) : ℤ) * (M₁ : ℤ) :=
      fun _ => hb1
    have hsz := dirBound (B := B₀ + 1) hc hcM₁M₂ hb1
    have hdir : ∀ a ∈ Finset.Icc 1 M₁, ∀ z : ℤ,
        z ∈ arithIcc (c * ((a : ℤ) + (fun _ : Fin 2 => b 0) 1)) M₂ →
        |z| ≤ ((B₀ + 2 : ℕ) : ℤ) * (N : ℤ) := by
      intro a ha z hz
      have h1 : |z| ≤ ((((B₀ + 1) + 1 : ℕ)) : ℤ) * (N : ℤ) :=
        le_trans (abs_le_of_mem_arithIcc hz) (hsz a ha)
      rw [cast_two B₀ N] at h1
      exact h1
    have hcard2 : ((badP 2 M₁ (fun _ : Fin 2 => b 0) η).card : ℝ) ≤ ε * (M₁ : ℝ) := by
      have h := badP_regime_one M₁ (b 0) η B₀ hη0 hη1 hreg hb0
      have hcast : ((badP 2 M₁ (fun _ : Fin 2 => b 0) η).card : ℝ)
          ≤ ((badP 1 M₁ (fun _ : Fin 1 => b 0) η).card : ℝ) := by exact_mod_cast h
      rw [hb_eq] at hcast
      exact le_trans hcast hcard1
    have hε₂C : ε ≤ C₂ * c₀ ^ e₂ * γ ^ e₂ :=
      le_trans hεC (mul_le_mul_of_nonneg_right hCC (pow_nonneg (le_of_lt hγ0) e₂))
    exact transfer_core (B₀ := B₀) (s' := s') (e₂ := e₂) (C₂ := C₂) (c₀ := c₀) (C := C)
      h2' hc₀0 hc₀1 hC₂pos hCC (Cw := B₀ + 2) hCw1 hc₀eq (b' := fun _ : Fin 2 => b 0)
      hc hM2 hM2M1 hN hNM hD hb0' hbb' hsup hbdd hγ0 hγ1 hη0 hηC hε0 hε₂C hDC hDND hdir hcard2
      hbox
  · -- Regime 2: pad by `b 0 + 1`; one extra bad point, absorbed by `ε + 1/M₁`
    push_neg at hreg
    have hb0' : (fun i : Fin 2 => if i = 0 then b 0 else b 0 + 1) 0 = b 0 := by
      change (if (0 : Fin 2) = 0 then b 0 else b 0 + 1) = b 0
      rw [if_pos rfl]
    have hbb' : ∀ i : Fin 2, |(fun i : Fin 2 => if i = 0 then b 0 else b 0 + 1) i|
        ≤ (((B₀ + 1 : ℕ)) : ℤ) * (M₁ : ℤ) := by
      intro i
      change |(if i = 0 then b 0 else b 0 + 1)| ≤ (((B₀ + 1 : ℕ)) : ℤ) * (M₁ : ℤ)
      by_cases hi : i = 0
      · rw [if_pos hi]; exact hb1
      · rw [if_neg hi]; exact hb2
    have hsz := dirBound (B := B₀ + 1) hc hcM₁M₂ hb2
    have hdir : ∀ a ∈ Finset.Icc 1 M₁, ∀ z : ℤ,
        z ∈ arithIcc (c * ((a : ℤ) + (fun i : Fin 2 => if i = 0 then b 0 else b 0 + 1) 1)) M₂ →
        |z| ≤ ((B₀ + 2 : ℕ) : ℤ) * (N : ℤ) := by
      intro a ha z hz
      have h1 : |z| ≤ ((((B₀ + 1) + 1 : ℕ)) : ℤ) * (N : ℤ) :=
        le_trans (abs_le_of_mem_arithIcc hz) (hsz a ha)
      rw [cast_two B₀ N] at h1
      exact h1
    have hε₂0 : 0 ≤ ε + 1 / (M₁ : ℝ) := by positivity
    have hε₂C : ε + 1 / (M₁ : ℝ) ≤ C₂ * c₀ ^ e₂ * γ ^ e₂ :=
      eps_add_inv_le (B₀ := B₀) (M₁ := M₁) (e₂ := e₂) (C₂ := C₂) (c₀ := c₀) (C := C)
        (γ := γ) (η := η) (ε := ε) hM1 hC₂pos hc₀0 hγ0 hγ1 hηC hεC hCC2 hreg
    have hcard2 : ((badP 2 M₁ (fun i : Fin 2 => if i = 0 then b 0 else b 0 + 1) η).card : ℝ)
        ≤ (ε + 1 / (M₁ : ℝ)) * (M₁ : ℝ) := by
      have h := badP_regime_two M₁ (b 0) η hη0 hη1
      have hcast : ((badP 2 M₁ (fun i : Fin 2 => if i = 0 then b 0 else b 0 + 1) η).card : ℝ)
          ≤ ((badP 1 M₁ (fun _ : Fin 1 => b 0) η).card : ℝ) + 1 := by exact_mod_cast h
      rw [hb_eq] at hcast
      have h₁ : 1 ≤ 1 / (M₁ : ℝ) * (M₁ : ℝ) := by
        rw [div_mul_cancel₀ _ (ne_of_gt hM₁pos)]
      have h₃ : ε * (M₁ : ℝ) + 1 / (M₁ : ℝ) * (M₁ : ℝ) = (ε + 1 / (M₁ : ℝ)) * (M₁ : ℝ) := by
        rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hM₁pos)]
      calc ((badP 2 M₁ (fun i : Fin 2 => if i = 0 then b 0 else b 0 + 1) η).card : ℝ)
          ≤ ((badP 1 M₁ b η).card : ℝ) + 1 := hcast
        _ ≤ ε * (M₁ : ℝ) + 1 / (M₁ : ℝ) * (M₁ : ℝ) := add_le_add hcard1 h₁
        _ = (ε + 1 / (M₁ : ℝ)) * (M₁ : ℝ) := h₃
    exact transfer_core (B₀ := B₀) (s' := s') (e₂ := e₂) (C₂ := C₂) (c₀ := c₀) (C := C)
      h2' hc₀0 hc₀1 hC₂pos hCC (Cw := B₀ + 2) hCw1 hc₀eq
      (b' := fun i : Fin 2 => if i = 0 then b 0 else b 0 + 1)
      hc hM2 hM2M1 hN hNM hD hb0' hbb' hsup hbdd hγ0 hγ1 hη0 hηC hε₂0 hε₂C hDC hDND hdir hcard2
      hbox

end Work.Peluse.Pel51
