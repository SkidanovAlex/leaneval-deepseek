import Mathlib
import Submission.Work.Peluse.Ulower.stepBasic
import Submission.Work.Peluse.Ulower.dualFn_norm_le_one

/-!
# The architecture of the degree-lowering assembly

This module contains the *bookkeeping* half of `Work.Peluse.Ulower.degree_lowering_v2`:

* `StepLe P` — the interface of one application of Peluse's Lemma 3.9 in the dense normalisation
  (the single step `t → t-1` at the fixed direction set `arithIcc 1 D` and the fixed support box);
* `iterate_steps` — the iteration of the step from level `s` down to level `2`, which produces the
  bound `c · θ^A · (D/Ns)^B ≤ boxNormPow 2 …` with explicit exponents;
* the real-arithmetic lemmas used to convert that constant-laden bound into the target's
  `(δ · D/Ns)^K ≤ boxNormPow 2 …` (given the a priori sharpness bound `δ ≤ 1 - u·(D/Ns)`).
-/

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

/-- **The single-step interface of the degree-lowering chain.**  One application of Peluse's
Lemma 3.9 in the dense normalisation: from a lower bound `θ` for the level-`t` box-norm power of the
dual function at the *dense* direction set `arithIcc 1 D` and the support box `symIcc B` one obtains
a lower bound `c · θ^p · (D/Ns)^q` for the level-`(t-1)` box-norm power at the same direction set and
box, with constants depending only on `P` and `t`. -/
def StepLe (P : Polynomial ℤ) (K : ℝ) : Prop :=
  ∀ t : ℕ, 3 ≤ t → ∃ p q : ℕ, 1 ≤ p ∧ 1 ≤ q ∧ ∃ c : ℝ, 0 < c ∧
    ∀ (B Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (θ : ℝ),
      2 ≤ P.natDegree → 1 ≤ N → 1 ≤ Ns → Scaled Ns N P.natDegree → N ≤ Ns →
      1 ≤ D → (D : ℝ) ≤ K * (Ns : ℝ) → SupportIn f₀ Ns → SupportIn f₁ Ns →
      (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
      dSup P Ns N + 2 * (t - 2) * D ≤ B →
      0 < θ → θ ≤ 1 →
      θ ≤ boxNormPow t (fun _ : Fin t => arithIcc 1 D) (symIcc B) (dualFn N P f₀ f₁) →
      c * θ ^ p * ((D : ℝ) / (Ns : ℝ)) ^ q ≤
        boxNormPow (t - 1) (fun _ : Fin (t - 1) => arithIcc 1 D) (symIcc B)
          (dualFn N P f₀ f₁)

/-- The dual function is `1`-bounded and vanishes off `symIcc B` as soon as `B ≥ dSup P Ns N`. -/
lemma dualFn_data {P : Polynomial ℤ} {Ns N B : ℕ} (hN : 1 ≤ N) (hNNs : N ≤ Ns)
    (hB : dSup P Ns N ≤ B) {f₀ f₁ : ℤ → ℂ} (hs0 : SupportIn f₀ Ns) (hs1 : SupportIn f₁ Ns)
    (hb0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (hb1 : ∀ x : ℤ, ‖f₁ x‖ ≤ 1) :
    (∀ x : ℤ, ‖dualFn N P f₀ f₁ x‖ ≤ 1) ∧
      (∀ x : ℤ, x ∉ symIcc B → dualFn N P f₀ f₁ x = 0) := by
  refine ⟨dualFn_norm_le_one hN P f₀ f₁ hb0 hb1, fun x hx => ?_⟩
  have hsupp := Tools.dualFn_supportIn (N := Ns) (M := N) (by omega) P f₀ f₁ hs0 hs1 hNNs
  refine hsupp x ?_
  have hx' : B < x.natAbs := by
    rw [mem_symIcc_iff] at hx
    omega
  omega

/-- The level-`t` box-norm power of the dual function is at most `1`. -/
lemma boxNormPow_dualFn_le_one {P : Polynomial ℤ} {Ns N B t : ℕ} (hN : 1 ≤ N) (hNNs : N ≤ Ns)
    (hB : dSup P Ns N ≤ B) {f₀ f₁ : ℤ → ℂ} (hs0 : SupportIn f₀ Ns) (hs1 : SupportIn f₁ Ns)
    (hb0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (hb1 : ∀ x : ℤ, ‖f₁ x‖ ≤ 1) :
    boxNormPow t (fun _ : Fin t => arithIcc 1 (1 : ℕ)) (symIcc B) (dualFn N P f₀ f₁) ≤ 1 := by
  obtain ⟨hb, hsupp⟩ := dualFn_data hN hNNs hB hs0 hs1 hb0 hb1
  simpa using boxNormPow_le_of_bound (fun _ : Fin t => arithIcc 1 (1 : ℕ)) (symIcc B)
    zero_le_one hb hsupp

/-- **The iteration of the chain.**  Applying `StepLe` repeatedly from level `s` down to level `2`
produces a lower bound with explicit exponents `A`, `B'` and constant `c > 0`. -/
theorem iterate_steps {P : Polynomial ℤ} {K : ℝ} (hK : 0 < K) (hstep : StepLe P K)
    (htop : 2 ≤ P.natDegree) (s : ℕ) (hs : 2 ≤ s) :
    ∃ A B : ℕ, 1 ≤ A ∧ 1 ≤ B ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (Bx Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (θ : ℝ),
        1 ≤ N → 1 ≤ Ns → Scaled Ns N P.natDegree → N ≤ Ns →
        1 ≤ D → (D : ℝ) ≤ K * (Ns : ℝ) → SupportIn f₀ Ns → SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        dSup P Ns N + 2 * (s - 2) * D ≤ Bx →
        0 < θ → θ ≤ 1 →
        θ ≤ boxNormPow s (fun _ : Fin s => arithIcc 1 D) (symIcc Bx) (dualFn N P f₀ f₁) →
        c * θ ^ A * ((D : ℝ) / (Ns : ℝ)) ^ B ≤
          boxNormPow 2 (fun _ : Fin 2 => arithIcc 1 D) (symIcc Bx) (dualFn N P f₀ f₁) := by
  have key : ∀ (m t : ℕ), t + m = s → 2 ≤ t →
      ∃ A B : ℕ, 1 ≤ A ∧ 1 ≤ B ∧ ∃ c : ℝ, 0 < c ∧
        ∀ (Bx Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (θ : ℝ),
          1 ≤ N → 1 ≤ Ns → Scaled Ns N P.natDegree → N ≤ Ns →
          1 ≤ D → (D : ℝ) ≤ K * (Ns : ℝ) → SupportIn f₀ Ns → SupportIn f₁ Ns →
          (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
          dSup P Ns N + 2 * (s - 2) * D ≤ Bx →
          0 < θ → θ ≤ 1 →
          θ ≤ boxNormPow s (fun _ : Fin s => arithIcc 1 D) (symIcc Bx) (dualFn N P f₀ f₁) →
          c * θ ^ A * ((D : ℝ) / (Ns : ℝ)) ^ B ≤
            boxNormPow t (fun _ : Fin t => arithIcc 1 D) (symIcc Bx) (dualFn N P f₀ f₁) := by
    intro m
    induction m with
    | zero =>
        intro t hts ht2
        have hts' : t = s := by omega
        subst hts'
        refine ⟨1, 1, le_refl 1, le_refl 1, min 1 K⁻¹, by positivity, ?_⟩
        intro Bx Ns N D f₀ f₁ θ hN hNs hSc hNNs hD hDK hs0 hs1 hb0 hb1 hB hθ0 hθ1 hbox
        have hNspos : (0 : ℝ) < (Ns : ℝ) := by exact_mod_cast hNs
        have hq0 : (0 : ℝ) ≤ (D : ℝ) / (Ns : ℝ) := by positivity
        have hqK : (D : ℝ) / (Ns : ℝ) ≤ K := by
          rw [div_le_iff₀ hNspos]; linarith
        have hfac : min 1 K⁻¹ * ((D : ℝ) / (Ns : ℝ)) ≤ 1 := by
          have h1 : K⁻¹ * ((D : ℝ)/(Ns : ℝ)) ≤ 1 := by
            have h2 : K⁻¹ * ((D : ℝ)/(Ns : ℝ)) ≤ K⁻¹ * K :=
              mul_le_mul_of_nonneg_left hqK (inv_nonneg.mpr hK.le)
            rwa [inv_mul_cancel₀ (ne_of_gt hK)] at h2
          nlinarith [hq0, h1, min_le_right (1 : ℝ) K⁻¹]
        have hpow : min 1 K⁻¹ * θ ^ 1 * ((D : ℝ) / (Ns : ℝ)) ^ 1 ≤ θ := by
          rw [pow_one, pow_one]
          nlinarith [hθ0, hfac]
        exact le_trans hpow hbox
    | succ m ih =>
        intro t hts ht2
        have ht1 : t + 1 + m = s := by omega
        obtain ⟨A₁, B₁, hA₁, hB₁, c₁, hc₁pos, hbody⟩ := ih (t + 1) ht1 (by omega)
        obtain ⟨p, q, hp, hq, c₂, hc₂pos, hstep'⟩ := hstep (t + 1) (by omega)
        refine ⟨A₁ * p, B₁ * p + q,
          Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), by omega,
          c₂ * c₁ ^ p, by positivity, ?_⟩
        intro Bx Ns N D f₀ f₁ θ hN hNs hSc hNNs hD hDK hs0 hs1 hb0 hb1 hB hθ0 hθ1 hbox
        have hbound₁ := hbody Bx Ns N D f₀ f₁ θ hN hNs hSc hNNs hD hDK
          hs0 hs1 hb0 hb1 hB hθ0 hθ1 hbox
        have hBge : dSup P Ns N ≤ Bx := le_trans (Nat.le_add_right _ _) hB
        obtain ⟨hbF, hsuppF⟩ := dualFn_data hN hNNs hBge hs0 hs1 hb0 hb1
        have hle1' : boxNormPow (t + 1) (fun _ : Fin (t + 1) => arithIcc 1 D) (symIcc Bx)
            (dualFn N P f₀ f₁) ≤ 1 := by
          simpa using boxNormPow_le_of_bound (fun _ : Fin (t + 1) => arithIcc 1 D) (symIcc Bx)
            zero_le_one hbF hsuppF
        have hθ'0 : 0 < c₁ * θ ^ A₁ * ((D : ℝ)/(Ns : ℝ)) ^ B₁ := by positivity
        have hθ'1 : c₁ * θ ^ A₁ * ((D : ℝ)/(Ns : ℝ)) ^ B₁ ≤ 1 := le_trans hbound₁ hle1'
        have hBstep : dSup P Ns N + 2 * ((t + 1) - 2) * D ≤ Bx := by
          have h1 : (t + 1) - 2 ≤ s - 2 := by omega
          have h2 : 2 * ((t + 1) - 2) * D ≤ 2 * (s - 2) * D :=
            Nat.mul_le_mul_right D (Nat.mul_le_mul_left 2 h1)
          omega
        have hbound₂ := hstep' Bx Ns N D f₀ f₁
          (c₁ * θ ^ A₁ * ((D : ℝ)/(Ns : ℝ)) ^ B₁)
          htop hN hNs hSc hNNs hD hDK hs0 hs1 hb0 hb1 hBstep hθ'0 hθ'1 hbound₁
        have hkey : c₂ * (c₁ * θ ^ A₁ * ((D : ℝ)/(Ns : ℝ)) ^ B₁) ^ p *
            ((D : ℝ)/(Ns : ℝ)) ^ q
            = (c₂ * c₁ ^ p) * θ ^ (A₁ * p) * ((D : ℝ)/(Ns : ℝ)) ^ (B₁ * p + q) := by
          rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
          rw [show c₂ * (c₁ ^ p * θ ^ (A₁ * p) * ((D : ℝ)/(Ns : ℝ)) ^ (B₁ * p)) *
                ((D : ℝ)/(Ns : ℝ)) ^ q
              = c₂ * (c₁ ^ p * θ ^ (A₁ * p)) *
                (((D : ℝ)/(Ns : ℝ)) ^ (B₁ * p) * ((D : ℝ)/(Ns : ℝ)) ^ q) from by ring]
          rw [← pow_add]
          ring
        rw [← hkey]
        exact hbound₂
  exact key (s - 2) 2 (by omega) (by omega)

/-! ## Real arithmetic: absorbing the constant of the chain -/

/-- If `δ ≤ 1 - u·δ'` with `δ' ∈ [0,1]`, then `δ·δ'` is bounded away from `1`: it is at most
`1 - u` (when `2u ≤ 1`, the maximum of `t(1-ut)` on `[0,1]` is at `t = 1`) or at most `1/(4u)`
(otherwise, the maximum of the parabola). -/
lemma prod_le_of_le_one_sub {δ δ' u : ℝ} (hδ'0 : 0 ≤ δ') (hδ'1 : δ' ≤ 1)
    (hu : 0 < u) (h : δ ≤ 1 - u * δ') :
    δ * δ' ≤ if 2 * u ≤ 1 then 1 - u else 1 / (4 * u) := by
  have h1 : δ * δ' ≤ δ' * (1 - u * δ') := by nlinarith
  by_cases hc : 2 * u ≤ 1
  · rw [if_pos hc]
    have hprod : (0 : ℝ) ≤ (1 - δ') * (1 - u * (1 + δ')) := by
      refine mul_nonneg (by linarith) ?_
      nlinarith
    nlinarith
  · rw [if_neg hc]
    have hkey : 4 * u * (δ' * (1 - u * δ')) ≤ 1 := by
      nlinarith [sq_nonneg (1 - 2 * u * δ')]
    rw [le_div_iff₀ (by linarith : (0:ℝ) < 4 * u)]
    nlinarith

end

end Work.Peluse.Ulower
