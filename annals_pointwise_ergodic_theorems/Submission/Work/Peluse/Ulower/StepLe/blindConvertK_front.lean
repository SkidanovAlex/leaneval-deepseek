/-
# The front end of `Work.Peluse.Ulower.StepLe.blindConvertK`

The aggregate of `blindConvertK` (the averaged squared correlations of the level-`σ` cube terms of
`dualFn N P f₀ f₁` at the phases `β`), the pointwise bound `X ≤ ((2B+1)/B)²` on its summands, and
the Markov (popularity) extraction of a dense level set `H₁` on which the correlations are large.

This is steps 1–2 of the route in `NOTES_blindConvertK_SESSION.md`.

## The route (recap)

`blindConvertK` needs, from `γ ≤ aggr`, a dense `H₁` with per-element correlations, then the
interchange (Peluse's Lemma 7.4 / `StepLe/denseAvgInterchangeSharp`), then the major-arc pinning
and the low-rank inversion (`StepLe/blindConvertK_lowrank`).  This file provides `aggr`, its
summands, and the Markov step.
-/

import Mathlib
import Submission.Work.Peluse.Ulower.supportIn_tsum_le
import Submission.Work.Peluse.Ulower.windowAggregate
import Submission.Work.Peluse.Ulower.deficit_v2
import Submission.Work.Peluse.Ulower.supportIn_off_Icc

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.Ulower.StepLe

noncomputable section

/-- The summands of the aggregate of `blindConvertK`: the squared modulus of the `B⁻¹`-normalised
correlation of the level-`σ` cube term of `F` at the pair `(u,v)`, with phase `β u v`. -/
def cubeCorr (σ B : ℕ) (F : ℤ → ℂ)
    (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (u v : Fin σ → ℤ) : ℝ :=
  ‖((B : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v F x *
    Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))‖ ^ 2

/-- The aggregate of `blindConvertK`. -/
def aggr (σ D B : ℕ) (F : ℤ → ℂ)
    (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) : ℝ :=
  ((Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹ *
    ((Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D)).card : ℝ)⁻¹ *
    ∑ u ∈ Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D),
      ∑ v ∈ Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D),
        cubeCorr σ B F β u v

/-- The phase factor `e(θx) = exp(2πiθx)` has modulus one. -/
lemma norm_exp_two_pi_I_mul (θ : ℝ) (x : ℤ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * θ * (x : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have hre : (2 * Real.pi * Complex.I * θ * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  rw [hre, Real.exp_zero]

/-- **The pointwise bound.**  For a `1`-bounded `F` supported in `[-S,S]` with `S + σD ≤ B` and
directions `(u,v)` in `[1,D]^σ`, the summand of the aggregate is at most `((2B+1)/B)²`. -/
theorem cubeCorr_le {σ B D S : ℕ} {F : ℤ → ℂ}
    (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (u v : Fin σ → ℤ)
    (hB : 1 ≤ B) (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1) (hFs : Work.Peluse.SupportIn F S)
    (hSB : S + σ * D ≤ B) (hv : ∀ i : Fin σ, (v i).natAbs ≤ D) :
    cubeCorr σ B F β u v ≤ (((2 * B + 1 : ℕ) : ℝ) / (B : ℝ)) ^ 2 := by
  classical
  have hterm1 : ∀ x : ℤ, ‖Work.Peluse.cubeTerm u v F x‖ ≤ 1 := by
    intro x
    simpa [Work.Peluse.cubeTerm] using Work.Peluse.Ulower.norm_cubeTerm_le hF1 u v x
  have hsupp : Work.Peluse.SupportIn (Work.Peluse.cubeTerm u v F) (S + σ * D) :=
    Work.Peluse.Ulower.supportIn_cubeTerm hFs hv
  have htsum : (∑' x : ℤ, ‖Work.Peluse.cubeTerm u v F x‖) ≤ ((2 * (S + σ * D) + 1 : ℕ) : ℝ) :=
    Work.Peluse.Ulower.supportIn_tsum_le hsupp hterm1
  -- summability of the norms of the summand
  have hsumm : Summable (fun x : ℤ => ‖Work.Peluse.cubeTerm u v F x *
      Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))‖) := by
    apply summable_of_ne_finset_zero
      (s := Finset.Icc (-(((S + σ * D) : ℕ) : ℤ)) (((S + σ * D) : ℕ) : ℤ))
    intro x hx
    have hx0 : Work.Peluse.cubeTerm u v F x = 0 := by
      apply Work.Peluse.Ulower.supportIn_off_Icc hsupp x
      simpa using hx
    rw [hx0, zero_mul, norm_zero]
  have hnorm : ‖∑' x : ℤ, Work.Peluse.cubeTerm u v F x *
        Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))‖
      ≤ ((2 * (S + σ * D) + 1 : ℕ) : ℝ) := by
    have h := norm_tsum_le_tsum_norm hsumm
    have hcongr : (∑' x : ℤ, ‖Work.Peluse.cubeTerm u v F x *
          Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))‖)
        = ∑' x : ℤ, ‖Work.Peluse.cubeTerm u v F x‖ :=
      tsum_congr (fun x => by rw [norm_mul, norm_exp_two_pi_I_mul (β u v) x, mul_one])
    rw [hcongr] at h
    exact h.trans htsum
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hstep : ‖((B : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v F x *
        Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))‖
      ≤ (((2 * (S + σ * D) + 1 : ℕ) : ℝ) / (B : ℝ)) := by
    rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hnorm (le_of_lt hBpos)
  have hmono : (((2 * (S + σ * D) + 1 : ℕ) : ℝ) / (B : ℝ))
      ≤ (((2 * B + 1 : ℕ) : ℝ) / (B : ℝ)) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt hBpos)
    have h2 : ((2 * (S + σ * D) + 1 : ℕ) : ℝ) ≤ ((2 * B + 1 : ℕ) : ℝ) := by
      have : 2 * (S + σ * D) + 1 ≤ 2 * B + 1 := by omega
      exact_mod_cast this
    exact h2
  have hnn : (0 : ℝ) ≤ (((2 * B + 1 : ℕ) : ℝ) / (B : ℝ)) := by positivity
  have hle : ‖((B : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v F x *
        Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))‖
      ≤ (((2 * B + 1 : ℕ) : ℝ) / (B : ℝ)) := hstep.trans hmono
  calc cubeCorr σ B F β u v
      = ‖((B : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v F x *
          Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))‖ ^ 2 := rfl
    _ ≤ ((((2 * B + 1 : ℕ) : ℝ) / (B : ℝ))) ^ 2 := by
        exact sq_le_sq' (by linarith [norm_nonneg (((B : ℂ))⁻¹ * ∑' x : ℤ, Work.Peluse.cubeTerm u v F x *
          Complex.exp (2 * Real.pi * Complex.I * (β u v : ℂ) * (x : ℂ))), hnn]) hle

/-- The full box of pairs of shift vectors. -/
def pairBox (σ D : ℕ) : Finset ((Fin σ → ℤ) × (Fin σ → ℤ)) :=
  (Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D)) ×ˢ
    (Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D))

lemma pairBox_card (σ D : ℕ) : (pairBox σ D).card =
    (Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D)).card ^ 2 := by
  rw [pairBox, Finset.card_product, sq]

/-- Membership in the pair box gives the coordinate bounds. -/
lemma mem_pairBox {σ D : ℕ} {p : (Fin σ → ℤ) × (Fin σ → ℤ)} (hp : p ∈ pairBox σ D) :
    (∀ i : Fin σ, p.1 i ∈ Work.Peluse.arithIcc 1 D) ∧
      (∀ i : Fin σ, p.2 i ∈ Work.Peluse.arithIcc 1 D) := by
  rw [pairBox, Finset.mem_product] at hp
  exact ⟨Fintype.mem_piFinset.mp hp.1, Fintype.mem_piFinset.mp hp.2⟩

lemma natAbs_le_of_mem_arithIcc_one {D : ℕ} {a : ℤ} (h : a ∈ Work.Peluse.arithIcc 1 D) :
    a.natAbs ≤ D := by
  have h1 : a ≤ (D : ℤ) := (Work.Peluse.Ulower.mem_arithIcc_one.mp h).2
  have h2 : (-(D : ℤ)) ≤ a := by
    have h0 := (Work.Peluse.Ulower.mem_arithIcc_one.mp h).1
    omega
  have h3 : |a| ≤ (D : ℤ) := abs_le.mpr ⟨h2, h1⟩
  rw [Int.abs_eq_natAbs] at h3
  exact_mod_cast h3

/-- The aggregate as a sum over the pair box. -/
lemma aggr_eq (σ D B : ℕ) (F : ℤ → ℂ)
    (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) :
    aggr σ D B F β = ((pairBox σ D).card : ℝ)⁻¹ *
      ∑ p ∈ pairBox σ D, cubeCorr σ B F β p.1 p.2 := by
  rw [aggr, pairBox, Finset.card_product]
  rw [Finset.sum_product]
  simp only
  have hcast : (((Fintype.piFinset fun x : Fin σ => Work.Peluse.arithIcc 1 D).card *
      (Fintype.piFinset fun x : Fin σ => Work.Peluse.arithIcc 1 D).card : ℕ) : ℝ)
      = ((Fintype.piFinset fun x : Fin σ => Work.Peluse.arithIcc 1 D).card : ℝ) *
        ((Fintype.piFinset fun x : Fin σ => Work.Peluse.arithIcc 1 D).card : ℝ) := by
    push_cast; ring
  rw [hcast]
  field_simp

/-- **Markov (popularity) extraction.**  From `γ ≤ aggr` we get a sub-family `H` of the pair box of
density `≥ γ/(2C)` on which every summand is at least `γ/2`, where `C = ((2B+1)/B)²` is the
pointwise bound of `cubeCorr_le`. -/
theorem markov {σ B D S : ℕ} {F : ℤ → ℂ}
    (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ) (hB : 1 ≤ B) (hD : 1 ≤ D)
    (hF1 : ∀ x : ℤ, ‖F x‖ ≤ 1) (hFs : Work.Peluse.SupportIn F S)
    (hSB : S + σ * D ≤ B) {γ : ℝ} (hγ : 0 < γ) (haggr : γ ≤ aggr σ D B F β) :
    ∃ H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ)),
      H ⊆ pairBox σ D ∧
      (γ / (2 * (((2 * B + 1 : ℕ) : ℝ) / (B : ℝ)) ^ 2)) * ((pairBox σ D).card : ℝ) ≤
        (H.card : ℝ) ∧
      ∀ p ∈ H, γ / 2 ≤ cubeCorr σ B F β p.1 p.2 := by
  classical
  set P : Finset ((Fin σ → ℤ) × (Fin σ → ℤ)) := pairBox σ D with hP
  set h : ℝ := (((2 * B + 1 : ℕ) : ℝ) / (B : ℝ)) ^ 2 with hh
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hh0 : 0 < h := by rw [hh]; exact pow_pos (by positivity) 2
  -- the pointwise bound
  have hX : ∀ p ∈ P, cubeCorr σ B F β p.1 p.2 ≤ h := by
    intro p hp
    obtain ⟨hu, hv⟩ := mem_pairBox (hP ▸ hp)
    exact cubeCorr_le β p.1 p.2 hB hF1 hFs hSB
      (fun i => natAbs_le_of_mem_arithIcc_one (hv i))
  -- `P` is nonempty
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hone : (fun _ : Fin σ => (1 : ℤ)) ∈
      Fintype.piFinset (fun _ : Fin σ => Work.Peluse.arithIcc 1 D) := by
    refine Fintype.mem_piFinset.mpr (fun _ => ?_)
    rw [Work.Peluse.Ulower.mem_arithIcc_one]
    exact ⟨le_refl 1, by exact_mod_cast hD⟩
  have hPpos : (0 : ℝ) < (P.card : ℝ) := by
    rw [hP, pairBox]
    have hc : 0 < ((Fintype.piFinset fun _ : Fin σ => Work.Peluse.arithIcc 1 D) ×ˢ
        (Fintype.piFinset fun _ : Fin σ => Work.Peluse.arithIcc 1 D)).card := by
      refine Finset.card_pos.mpr ⟨(fun _ => 1, fun _ => 1), ?_⟩
      rw [Finset.mem_product]
      exact ⟨hone, hone⟩
    exact_mod_cast hc
  -- the aggregate lower bound, expanded
  have ha : γ * (P.card : ℝ) ≤ ∑ p ∈ P, cubeCorr σ B F β p.1 p.2 := by
    have h1 := haggr
    rw [aggr_eq] at h1
    have h2 : ((pairBox σ D).card : ℝ)⁻¹ *
          ∑ p ∈ pairBox σ D, cubeCorr σ B F β p.1 p.2
        = ((P.card : ℝ))⁻¹ * ∑ p ∈ P, cubeCorr σ B F β p.1 p.2 := by rw [hP]
    rw [h2] at h1
    rw [inv_mul_eq_div, le_div_iff₀ hPpos] at h1
    linarith
  -- Markov
  set H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ)) :=
    P.filter (fun p => γ / 2 ≤ cubeCorr σ B F β p.1 p.2) with hH
  have hHsub : H ⊆ P := by rw [hH]; exact Finset.filter_subset _ _
  have hHlvl : ∀ p ∈ H, γ / 2 ≤ cubeCorr σ B F β p.1 p.2 := by
    intro p hp; rw [hH] at hp; exact (Finset.mem_filter.mp hp).2
  -- the two pieces of the sum over `P`
  have hsplit : ∑ p ∈ P, cubeCorr σ B F β p.1 p.2
      = ∑ p ∈ H, cubeCorr σ B F β p.1 p.2
        + ∑ p ∈ P.filter (fun p => ¬ (γ / 2 ≤ cubeCorr σ B F β p.1 p.2)),
            cubeCorr σ B F β p.1 p.2 := by
    rw [hH]
    exact (Finset.sum_filter_add_sum_filter_not P _ _).symm
  have hcomp : ∑ p ∈ P.filter (fun p => ¬ (γ / 2 ≤ cubeCorr σ B F β p.1 p.2)),
        cubeCorr σ B F β p.1 p.2 ≤ (γ / 2) * (P.card : ℝ) := by
    have h1 : ∀ p ∈ P.filter (fun p => ¬ (γ / 2 ≤ cubeCorr σ B F β p.1 p.2)),
        cubeCorr σ B F β p.1 p.2 ≤ γ / 2 := by
      intro p hp
      rw [Finset.mem_filter] at hp
      exact le_of_lt (lt_of_not_ge hp.2)
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by linarith [hγ])
    exact_mod_cast Finset.card_filter_le _ _
  have hHbig : (γ / 2) * (P.card : ℝ) ≤ ∑ p ∈ H, cubeCorr σ B F β p.1 p.2 := by
    have := ha
    rw [hsplit] at this
    linarith
  have hHsmall : ∑ p ∈ H, cubeCorr σ B F β p.1 p.2 ≤ h * (H.card : ℝ) := by
    refine (Finset.sum_le_sum (fun p hp => hX p (hHsub hp))).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hfinal : (γ / 2) * (P.card : ℝ) ≤ h * (H.card : ℝ) := hHbig.trans hHsmall
  refine ⟨H, ?_, ?_, hHlvl⟩
  · rw [hP]; exact hHsub
  · have hkey : (γ / 2) * ((pairBox σ D).card : ℝ)
        ≤ (((2 * B + 1 : ℕ) : ℝ) / (B : ℝ)) ^ 2 * (H.card : ℝ) := by
      rw [hP] at hfinal
      rw [hh] at hfinal
      exact hfinal
    have hCpos : (0 : ℝ) < 2 * (((2 * B + 1 : ℕ) : ℝ) / (B : ℝ)) ^ 2 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ hCpos]
    nlinarith [hkey]

/-- **Popularity (Markov) step, abstract form.**  From an average lower bound `ℓ` on a family of
nonnegative quantities bounded by `C`, extract a sub-family of density `≥ ℓ/(2C)` on which every
value is at least `ℓ/2`.  (This is step 4 of the route: the inner correlations of the interchange
output, extracted to a dense `H₂ ⊆ Θ_σ(H₁)`.) -/
theorem popularity {ι : Type} [DecidableEq ι] (Θ : Finset ι) (Ψ : ι → ℝ) {ℓ C : ℝ}
    (hC : 0 < C) (hℓ : 0 < ℓ) (hbound : ∀ k ∈ Θ, Ψ k ≤ C)
    (havg : ℓ ≤ ((Θ.card : ℝ))⁻¹ * ∑ k ∈ Θ, Ψ k) :
    ∃ H : Finset ι, H ⊆ Θ ∧ (ℓ / (2 * C)) * (Θ.card : ℝ) ≤ (H.card : ℝ) ∧
      ∀ k ∈ H, ℓ / 2 ≤ Ψ k := by
  classical
  set H : Finset ι := Θ.filter (fun k => ℓ / 2 ≤ Ψ k) with hH
  have hHsub : H ⊆ Θ := by rw [hH]; exact Finset.filter_subset _ _
  have hHlvl : ∀ k ∈ H, ℓ / 2 ≤ Ψ k := by
    intro k hk; rw [hH] at hk; exact (Finset.mem_filter.mp hk).2
  have hΘpos : (0 : ℝ) < (Θ.card : ℝ) := by
    rcases Θ.eq_empty_or_nonempty with h | h
    · rw [h] at havg; simp at havg; linarith
    · exact_mod_cast Finset.card_pos.mpr h
  have hsum : ℓ * (Θ.card : ℝ) ≤ ∑ k ∈ Θ, Ψ k := by
    rw [inv_mul_eq_div, le_div_iff₀ hΘpos] at havg; linarith
  have hsplit : ∑ k ∈ Θ, Ψ k = ∑ k ∈ H, Ψ k
      + ∑ k ∈ Θ.filter (fun k => ¬ (ℓ / 2 ≤ Ψ k)), Ψ k := by
    rw [hH]; exact (Finset.sum_filter_add_sum_filter_not Θ _ _).symm
  have hcomp : ∑ k ∈ Θ.filter (fun k => ¬ (ℓ / 2 ≤ Ψ k)), Ψ k ≤ (ℓ / 2) * (Θ.card : ℝ) := by
    have h1 : ∀ k ∈ Θ.filter (fun k => ¬ (ℓ / 2 ≤ Ψ k)), Ψ k ≤ ℓ / 2 := by
      intro k hk; rw [Finset.mem_filter] at hk; exact le_of_lt (lt_of_not_ge hk.2)
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    exact_mod_cast Finset.card_filter_le _ _
  have hbig : (ℓ / 2) * (Θ.card : ℝ) ≤ ∑ k ∈ H, Ψ k := by
    have := hsum
    rw [hsplit] at this
    linarith
  have hHsmall : ∑ k ∈ H, Ψ k ≤ C * (H.card : ℝ) := by
    refine (Finset.sum_le_sum (fun k hk => hbound k (hHsub hk))).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  refine ⟨H, hHsub, ?_, hHlvl⟩
  have hfinal : (ℓ / 2) * (Θ.card : ℝ) ≤ C * (H.card : ℝ) := hbig.trans hHsmall
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith : (0:ℝ) < 2 * C)]
  nlinarith [hfinal]

end

end Work.Peluse.Ulower.StepLe
