import Mathlib
import Submission.Work.Peluse.UlowerA.Defs
import Submission.Work.Peluse.Ulower.finalTarget
import Submission.Work.Peluse.Ulower.steple_aux

/-!
# The `A`-relaxed degree-lowering chain

This module re-runs the bookkeeping of `Work.Peluse.Ulower.degree_lowering_v2`
(`Ulower/assemble.lean`, `Ulower/chain.lean`, `Ulower/finalTarget.lean`) with the balanced scale
relation `Scaled Ns N d` (`N^d/2 ≤ Ns ≤ 2 N^d`) replaced everywhere by the single numerical
hypothesis `dSup P Ns N + 1 ≤ C · Ns` of `Work.Peluse.UlowerA.Basic`
(`dSup_add_one_le_of_unbal` derives it from the unbalanced relation `N^d ≤ A·Ns`).

The only mathematical uses of `Scaled` in the chain are

* `dSup_div_add_one_le` (in `levelTwoExtract` and in the final comparison), and
* the *passing* of the hypothesis through `StepLe`/`iterate_steps`/`chain_bound`,

so the substitution is faithful; the constants become `C`-dependent, which is allowed because in the
target `K` is chosen after `A` and `C := 2 + coeffSum P * A` is a function of `A`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial

namespace Work.Peluse.UlowerA

noncomputable section

open Work.Peluse
open Work.Peluse.Ulower

/-- **The single-step interface of the degree-lowering chain.**  One application of Peluse's
Lemma 3.9 in the dense normalisation: from a lower bound `θ` for the level-`t` box-norm power of the
dual function at the *dense* direction set `arithIcc 1 D` and the support box `symIcc B` one obtains
a lower bound `c · θ^p · (D/Ns)^q` for the level-`(t-1)` box-norm power at the same direction set and
box, with constants depending only on `P` and `t`. -/
def StepLeA (P : Polynomial ℤ) (C : ℕ) (K : ℝ) : Prop :=
  ∀ t : ℕ, 3 ≤ t → ∃ p q : ℕ, 1 ≤ p ∧ 1 ≤ q ∧ ∃ c : ℝ, 0 < c ∧
    ∀ (B Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (θ : ℝ),
      2 ≤ P.natDegree → 1 ≤ C → 1 ≤ N → 1 ≤ Ns →
        UnbalScale P C Ns N → N ≤ Ns →
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
theorem iterate_stepsA {P : Polynomial ℤ} {C : ℕ} (hC : 1 ≤ C) {K : ℝ} (hK : 0 < K)
    (hstep : StepLeA P C K)
    (htop : 2 ≤ P.natDegree) (s : ℕ) (hs : 2 ≤ s) :
    ∃ A B : ℕ, 1 ≤ A ∧ 1 ≤ B ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (Bx Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (θ : ℝ),
        1 ≤ N → 1 ≤ Ns → UnbalScale P C Ns N → N ≤ Ns →
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
          1 ≤ N → 1 ≤ Ns → UnbalScale P C Ns N → N ≤ Ns →
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
          htop hC hN hNs hSc hNNs hD hDK hs0 hs1 hb0 hb1 hBstep hθ'0 hθ'1 hbound₁
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



theorem chain_boundA {P : Polynomial ℤ} {C : ℕ} (hC : 1 ≤ C) {K : ℝ} (hK : 0 < K)
    (hKc : |(((P.leadingCoeff : ℤ)) : ℝ)| ≤ K) (hstep : StepLeA P C K) (htop : 2 ≤ P.natDegree)
    (s : ℕ) (hs : 2 ≤ s) :
    ∃ A B : ℕ, 1 ≤ A ∧ 1 ≤ B ∧ ∃ c : ℝ, 0 < c ∧
      ∀ (Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ : ℝ),
        2 ≤ P.natDegree → 1 ≤ N → 1 ≤ Ns → UnbalScale P C Ns N → N ≤ Ns →
        1 ≤ D → (D : ℝ) ≤ (Ns : ℝ) → SupportIn f₀ Ns → SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) → 0 < δ → δ ≤ 1 →
        δ ≤ uNormPow s (arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N))
              (dualFn N P f₀ f₁) →
        c * δ ^ A * ((D : ℝ) / (Ns : ℝ)) ^ B ≤
          uNormPow 2 (arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N))
            (dualFn N P f₀ f₁) := by
  have hc₀ : P.leadingCoeff ≠ 0 := by
    intro h
    have hP : P = 0 := Polynomial.leadingCoeff_eq_zero.mp h
    rw [hP] at htop
    simp at htop
  by_cases hs2 : s = 2
  · subst hs2
    refine ⟨1, 1, le_refl 1, le_refl 1, 1, one_pos, ?_⟩
    intro Ns N D f₀ f₁ δ hd hN hNs hSc hNNs hD hDNs hsp0 hsp1 hb0 hb1 hδ0 hδ1 hbox
    have hNs' : (0 : ℝ) < (Ns : ℝ) := by exact_mod_cast hNs
    have hq : (D : ℝ) / (Ns : ℝ) ≤ 1 := by
      rw [div_le_one hNs']; exact_mod_cast hDNs
    have h1 : (1 : ℝ) * δ ^ 1 * ((D : ℝ)/(Ns:ℝ))^1 ≤ δ := by
      rw [pow_one, pow_one, one_mul]
      nlinarith [hδ0, hq]
    exact le_trans h1 hbox
  · have hs3 : 3 ≤ s := by omega
    obtain ⟨A, Bv, hA, hBv, cc₂, hcc₂pos, hbody⟩ := iterate_stepsA hC hK hstep htop s hs
    obtain ⟨C₁, hC₁pos, hC₁u⟩ := sparse_to_dense_uniform (t := s) hs P.leadingCoeff hc₀
    set κ : ℝ := 1 / (1 + 2 * ((s - 2 : ℕ) : ℝ) * ((P.leadingCoeff.natAbs : ℕ) : ℝ)) with hκ
    have hκpos : 0 < κ := by
      rw [hκ]
      exact div_pos one_pos (by positivity)
    have habs : (0 : ℝ) < |(((P.leadingCoeff : ℤ)) : ℝ)| :=
      abs_pos.mpr (by exact_mod_cast hc₀)
    refine ⟨A, Bv, hA, hBv, cc₂ * (κ * C₁) ^ A * |(((P.leadingCoeff : ℤ)) : ℝ)| ^ Bv / 4,
      div_pos (mul_pos (mul_pos hcc₂pos (pow_pos (mul_pos hκpos hC₁pos) A)) (pow_pos habs Bv))
        (by norm_num), ?_⟩
    intro Ns N D f₀ f₁ δ hd hN hNs hSc hNNs hD hDNs hsp0 hsp1 hb0 hb1 hδ0 hδ1 hbox
    set Dd : ℕ := P.leadingCoeff.natAbs * D with hDd
    set Bx : ℕ := dSup P Ns N + 2 * (s - 2) * Dd with hBx
    set F : ℤ → ℂ := dualFn N P f₀ f₁ with hF
    set CL : ℝ := ((symIcc (dSup P Ns N)).card : ℝ) with hCL
    set CB : ℝ := ((symIcc Bx).card : ℝ) with hCB
    have hCLpos : 0 < CL := by
      rw [hCL]; exact_mod_cast Finset.card_pos.mpr ⟨0, by simp [symIcc]⟩
    have hCBpos : 0 < CB := by
      rw [hCB]; exact_mod_cast Finset.card_pos.mpr ⟨0, by simp [symIcc]⟩
    have hDd1 : 1 ≤ Dd := by
      rw [hDd]; exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    have hB1 : 1 ≤ Bx := by
      rw [hBx]
      have h1 : 1 ≤ dSup P Ns N := by
        have : Ns ≤ dSup P Ns N := Nat.le_add_right _ _
        omega
      exact le_trans h1 (Nat.le_add_right _ _)
    have hDdB : Dd ≤ Bx := by
      rw [hBx]
      have h2 : (1 : ℕ) * Dd ≤ 2 * (s - 2) * Dd := by
        have : 1 ≤ 2 * (s - 2) := by omega
        exact Nat.mul_le_mul_right Dd this
      exact le_trans (by simpa using h2) (Nat.le_add_left _ _)
    obtain ⟨hbF, hsuppB⟩ := dualFn_data hN hNNs (le_refl (dSup P Ns N)) hsp0 hsp1 hb0 hb1
    have hsuppL : ∀ x : ℤ, x ∉ symIcc (dSup P Ns N) → F x = 0 := by
      intro x hx
      rw [hF]
      exact hsuppB x (fun h => hx (by rw [mem_symIcc_iff] at h ⊢; omega))
    have hbF' : ∀ x : ℤ, ‖F x‖ ≤ 1 := by intro x; rw [hF]; exact hbF x
    have hsuppB' : ∀ x : ℤ, x ∉ symIcc Bx → F x = 0 := by
      intro x hx
      exact hsuppL x (fun h => hx (by rw [mem_symIcc_iff] at h ⊢; omega))
    have hC₁ := hC₁u D hD (dSup P Ns N) F hbF' hsuppL
    have hboxL : δ ≤ boxNormPow s (fun _ : Fin s => arithIcc P.leadingCoeff D)
        (symIcc (dSup P Ns N)) F := by
      have h1 := hbox
      rw [hF] at h1
      simpa only [uNormPow] using h1
    have hdenseL : C₁ * δ ≤ boxNormPow s (fun _ : Fin s => arithIcc 1 Dd)
        (symIcc (dSup P Ns N)) F := by
      have h := mul_le_mul_of_nonneg_left hboxL hC₁pos.le
      rw [hDd]
      exact le_trans h hC₁
    have hcardCL : CL = 2 * (((dSup P Ns N) : ℕ) : ℝ) + 1 := by
      rw [hCL, card_symIcc]; push_cast; ring
    have hcardCB : CB = 2 * ((Bx : ℕ) : ℝ) + 1 := by
      rw [hCB, card_symIcc]; push_cast; ring
    have hDs : Dd ≤ P.leadingCoeff.natAbs * dSup P Ns N := by
      rw [hDd]
      exact Nat.mul_le_mul_left _ (le_trans (by exact_mod_cast hDNs) (Nat.le_add_right _ _))
    have hCBle : CB ≤ CL * (1 + 2 * ((s - 2 : ℕ) : ℝ) * ((P.leadingCoeff.natAbs : ℕ) : ℝ)) := by
      rw [hcardCL, hcardCB, hBx]
      push_cast
      have h1 : ((Dd : ℕ) : ℝ) ≤ ((P.leadingCoeff.natAbs : ℕ) : ℝ) * ((dSup P Ns N : ℕ) : ℝ) := by
        exact_mod_cast hDs
      have h2 : (0 : ℝ) ≤ ((dSup P Ns N : ℕ) : ℝ) := by positivity
      nlinarith [h1, h2]
    have hratio_ge : κ ≤ CL / CB := by
      rw [hκ, le_div_iff₀ hCBpos]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity :
        (0:ℝ) < 1 + 2 * ((s - 2 : ℕ) : ℝ) * ((P.leadingCoeff.natAbs : ℕ) : ℝ))]
      simpa using hCBle
    have hboxB : CL / CB * (C₁ * δ) ≤
        boxNormPow s (fun _ : Fin s => arithIcc 1 Dd) (symIcc Bx) F := by
      have h := boxNormPow_eq_mul_card s (fun _ : Fin s => arithIcc 1 Dd)
        (symIcc Bx) (symIcc (dSup P Ns N)) F (by simp [symIcc])
      rw [← hCL, ← hCB] at h
      rw [h]
      exact mul_le_mul_of_nonneg_left hdenseL (div_nonneg hCLpos.le hCBpos.le)
    have hθbox : κ * (C₁ * δ) ≤ boxNormPow s (fun _ : Fin s => arithIcc 1 Dd) (symIcc Bx) F :=
      le_trans (mul_le_mul_of_nonneg_right hratio_ge (mul_nonneg hC₁pos.le hδ0.le)) hboxB
    have hθ0 : 0 < κ * (C₁ * δ) := mul_pos hκpos (mul_pos hC₁pos hδ0)
    have hθ1 : κ * (C₁ * δ) ≤ 1 := by
      refine le_trans hθbox ?_
      simpa using boxNormPow_le_of_bound (fun _ : Fin s => arithIcc 1 Dd) (symIcc Bx)
        zero_le_one hbF' hsuppB'
    have hcast : ((Dd : ℕ) : ℝ) = |(((P.leadingCoeff : ℤ)) : ℝ)| * (D : ℝ) := by
      rw [hDd, Nat.cast_mul, natAbs_cast_real]
    have hratio : ((Dd : ℕ) : ℝ) ≤ K * (Ns : ℝ) := by
      rw [hcast]
      have hDle : (D : ℝ) ≤ (Ns : ℝ) := by exact_mod_cast hDNs
      have hD0 : (0 : ℝ) ≤ (D : ℝ) := by positivity
      nlinarith [hKc, hDle, hD0, hK.le]
    have hbound := hbody Bx Ns N Dd f₀ f₁ (κ * (C₁ * δ))
      hN hNs hSc hNNs hDd1 hratio hsp0 hsp1 hb0 hb1 (by rw [hBx]) hθ0 hθ1 hθbox
    have hcDB : (D : ℝ) * |(((P.leadingCoeff : ℤ)) : ℝ)| ≤ (Bx : ℝ) := by
      have h2 : ((Dd : ℕ) : ℝ) ≤ (Bx : ℝ) := by exact_mod_cast hDdB
      linarith [hcast, h2]
    have hspB : SupportIn F Bx := by
      intro x hx
      exact hsuppB' x (by rw [mem_symIcc_iff]; omega)
    have hC₃ := dense_le_apBoxNorm (c := P.leadingCoeff) (D := D) (N := Bx) hc₀ hD hB1 hcDB
      hbF' hspB
    have hshrink : boxNormPow 2 (fun _ : Fin 2 => arithIcc P.leadingCoeff D) (symIcc Bx) F ≤
        boxNormPow 2 (fun _ : Fin 2 => arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N)) F := by
      refine boxNormPow_le_of_subset _ ?_ (by simp [symIcc]) F
      intro x hx
      rw [symIcc, Finset.mem_Icc] at hx
      rw [symIcc, Finset.mem_Icc]
      omega
    have hgoal : cc₂ * (κ * C₁) ^ A * |(((P.leadingCoeff : ℤ)) : ℝ)| ^ Bv / 4 *
          δ ^ A * ((D : ℝ) / (Ns : ℝ)) ^ Bv
        = (1 / 4) * (cc₂ * (κ * (C₁ * δ)) ^ A * (((Dd : ℕ) : ℝ) / (Ns : ℝ)) ^ Bv) := by
      have h1 : (κ * (C₁ * δ)) ^ A = (κ * C₁) ^ A * δ ^ A := by
        rw [show κ * (C₁ * δ) = κ * C₁ * δ from by ring, mul_pow]
      have h2 : (((Dd : ℕ) : ℝ) / (Ns : ℝ)) ^ Bv =
          |(((P.leadingCoeff : ℤ)) : ℝ)| ^ Bv * ((D : ℝ) / (Ns : ℝ)) ^ Bv := by
        rw [hcast]
        rw [show |(((P.leadingCoeff : ℤ)) : ℝ)| * (D : ℝ) / (Ns : ℝ) =
            |(((P.leadingCoeff : ℤ)) : ℝ)| * ((D : ℝ) / (Ns : ℝ)) from by ring, mul_pow]
      rw [h2, h1]
      ring
    rw [hgoal]
    exact le_trans (mul_le_mul_of_nonneg_left hbound (by norm_num)) (le_trans hC₃ hshrink)


/-- **The target statement in the `A`-relaxed scale, given the `A`-version of the single-step
interface.** -/
theorem degree_lowering_A_of_step {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (hstep : ∀ C : ℕ, 1 ≤ C → StepLeA P C (max 1 |(((P.leadingCoeff : ℤ)) : ℝ)|)) :
    ∀ A : ℕ, 1 ≤ A → ∀ s : ℕ, 2 ≤ s → ∃ K : ℕ, 1 ≤ K ∧
      ∀ (Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ : ℝ),
        2 ≤ P.natDegree → 1 ≤ N → 1 ≤ Ns → 1 ≤ D →
        (N : ℝ) ≤ (Ns : ℝ) →
        (N : ℝ) ^ P.natDegree ≤ (A : ℝ) * (Ns : ℝ) →
        (Ns : ℝ) ≤ (A : ℝ) * (N : ℝ) ^ P.natDegree →
        (D : ℝ) ≤ (Ns : ℝ) →
        SupportIn f₀ Ns → SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        0 < δ → δ ≤ 1 →
        δ ≤ uNormPow s (arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N))
              (dualFn N P f₀ f₁) →
        (δ * ((D : ℝ) / (Ns : ℝ))) ^ K ≤
          uNormPow 2 (arithIcc P.leadingCoeff D) (symIcc (dSup P Ns N))
            (dualFn N P f₀ f₁) := by
  intro A hA s hs
  set C : ℕ := max (2 + coeffSum P * A) A with hCdef
  have hC1 : 1 ≤ C := by rw [hCdef]; omega
  have htop : 2 ≤ P.natDegree := hd
  set K₀ : ℝ := max 1 |(((P.leadingCoeff : ℤ)) : ℝ)| with hK₀def
  have hKpos : 0 < K₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hKc : |(((P.leadingCoeff : ℤ)) : ℝ)| ≤ K₀ := le_max_right _ _
  have hlc0 : P.leadingCoeff ≠ 0 := by
    intro h
    have hP : P = 0 := Polynomial.leadingCoeff_eq_zero.mp h
    rw [hP] at htop
    simp at htop
  by_cases hs2 : s = 2
  · subst hs2
    refine ⟨1, le_refl 1, ?_⟩
    intro Ns N D f₀ f₁ δ hd' hN hNs hD hNle hNpow hpowN hDNs hs0 hs1 hb0 hb1 hδ0 hδ1 hbox
    have hNspos : (0 : ℝ) < (Ns : ℝ) := by exact_mod_cast hNs
    have hq : (D : ℝ) / (Ns : ℝ) ≤ 1 := by rw [div_le_one hNspos]; exact_mod_cast hDNs
    have h1 : (δ * ((D : ℝ) / (Ns : ℝ))) ^ 1 ≤ δ := by
      rw [pow_one]; nlinarith [hδ0, hq]
    refine le_trans h1 ?_
    simpa only [uNormPow] using hbox
  · have hs3 : 3 ≤ s := by omega
    obtain ⟨Ae, Be, hAe, hBe, c, hcpos, hchain⟩ := chain_boundA hC1 hKpos hKc (hstep C hC1) htop s hs
    -- the uniform constant of the sharpness estimate
    set C_P : ℝ := 2 * ((C : ℕ) : ℝ) with hC_P
    have hC_Ppos : 0 < C_P := by
      rw [hC_P]; positivity
    set c₂ : ℝ := ((s : ℕ) : ℝ) * |(((P.leadingCoeff : ℤ)) : ℝ)| / (4 * 2 ^ s * C_P) with hc₂
    have hc₂pos : 0 < c₂ := by
      rw [hc₂]
      have h1 : (0 : ℝ) < |(((P.leadingCoeff : ℤ)) : ℝ)| :=
        abs_pos.mpr (by exact_mod_cast hlc0)
      positivity
    set r : ℝ := max (if 2 * c₂ ≤ 1 then 1 - c₂ else 1 / (4 * c₂)) (1 - 1 / 2 ^ s) with hr
    have h2spos : (0 : ℝ) < 2 ^ s := by positivity
    have hr0 : 0 ≤ r := by
      rw [hr]
      refine le_max_of_le_left ?_
      by_cases hc : 2 * c₂ ≤ 1
      · rw [if_pos hc]; linarith
      · rw [if_neg hc]; positivity
    have hr1 : r < 1 := by
      rw [hr]
      refine max_lt ?_ ?_
      · by_cases hc : 2 * c₂ ≤ 1
        · rw [if_pos hc]; linarith
        · rw [if_neg hc]
          rw [div_lt_one (by linarith : (0 : ℝ) < 4 * c₂)]
          linarith
      · have h2s : (1 : ℝ) < 2 ^ s := one_lt_pow₀ one_lt_two (by omega)
        have hpos : (0 : ℝ) < 1 / 2 ^ s := by positivity
        linarith
    obtain ⟨Kc, hKc1, hKcuniv⟩ := final_compare_uniform (C := c) (r := r) hcpos hr0 hr1 Ae Be
    refine ⟨max 4 Kc, le_trans (by norm_num : 1 ≤ 4) (le_max_left 4 Kc), ?_⟩
    intro Ns N D f₀ f₁ δ hd' hN hNs hD hNle hNpow hpowN hDNs hs0 hs1 hb0 hb1 hδ0 hδ1 hbox
    have hscale1 : dSup P Ns N + 1 ≤ C * Ns := by
      rw [hCdef]
      exact le_trans (dSup_add_one_le_of_unbal hA hN hNs hNpow)
        (Nat.mul_le_mul_right Ns (le_max_left _ _))
    have hscale2 : (Ns : ℝ) ≤ (C : ℝ) * (N : ℝ) ^ P.natDegree := by
      rw [hCdef]
      have hA' : (A : ℝ) ≤ ((max (2 + Work.Peluse.Ulower.coeffSum P * A) A : ℕ) : ℝ) := by
        exact_mod_cast (le_max_right (2 + Work.Peluse.Ulower.coeffSum P * A) A)
      calc (Ns : ℝ) ≤ (A : ℝ) * (N : ℝ) ^ P.natDegree := hpowN
        _ ≤ ((max (2 + Work.Peluse.Ulower.coeffSum P * A) A : ℕ) : ℝ) *
              (N : ℝ) ^ P.natDegree := mul_le_mul_of_nonneg_right hA' (by positivity)
    have hscale : UnbalScale P C Ns N := ⟨hscale1, hscale2⟩
    have hNNs : N ≤ Ns := by exact_mod_cast hNle
    set F : ℤ → ℂ := dualFn N P f₀ f₁ with hF
    have hbF : ∀ x : ℤ, ‖F x‖ ≤ 1 := by
      intro x; rw [hF]; exact dualFn_norm_le_one hN P f₀ f₁ hb0 hb1 x
    have hsupF : ∀ x : ℤ, x ∉ symIcc (dSup P Ns N) → F x = 0 := by
      intro x hx
      rw [hF]
      exact Tools.dualFn_supportIn (by omega) P f₀ f₁ hs0 hs1 hNNs x (lt_natAbs_of_notMem_symIcc hx)
    have hNspos : (0 : ℝ) < (Ns : ℝ) := by exact_mod_cast hNs
    have hδ'0 : (0 : ℝ) ≤ (D : ℝ) / (Ns : ℝ) := by positivity
    have hδ'1 : (D : ℝ) / (Ns : ℝ) ≤ 1 := by rw [div_le_one hNspos]; exact_mod_cast hDNs
    by_cases hD1 : D = 1
    · -- #### the singleton case
      subst hD1
      have hbox' : δ ≤ uNormPow s ({P.leadingCoeff} : Finset ℤ) (symIcc (dSup P Ns N)) F := by
        have h := hbox
        rw [arithIcc_one_eq_singleton] at h
        rw [hF] at h
        exact h
      have hmono : uNormPow s ({P.leadingCoeff} : Finset ℤ) (symIcc (dSup P Ns N)) F ≤
          uNormPow 2 ({P.leadingCoeff} : Finset ℤ) (symIcc (dSup P Ns N)) F :=
        uNormPow_singleton_le_two hs hsupF hbF
      have hδ22 : δ ≤ uNormPow 2 ({P.leadingCoeff} : Finset ℤ) (symIcc (dSup P Ns N)) F :=
        le_trans hbox' hmono
      set d1 : ℝ := (((1 : ℕ)) : ℝ) / (Ns : ℝ) with hd1
      have hd1le : d1 ≤ 1 := by
        rw [hd1, div_le_one hNspos]; exact_mod_cast hNs
      have hd1nn : 0 ≤ d1 := by rw [hd1]; positivity
      have hfac1 : δ * d1 ≤ 1 := by
        calc δ * d1 ≤ 1 * 1 := mul_le_mul hδ1 hd1le hd1nn (by norm_num)
          _ = 1 := by ring
      have hnn : (0 : ℝ) ≤ δ * d1 := by positivity
      have hexp : 1 ≤ max 4 Kc := le_trans (by norm_num : 1 ≤ 4) (le_max_left 4 Kc)
      have hK1 : (δ * d1) ^ max 4 Kc ≤ δ * d1 := by
        simpa using pow_le_pow_of_le_one hnn hfac1 hexp
      have hδle : δ * d1 ≤ δ := by
        calc δ * d1 ≤ δ * 1 := mul_le_mul_of_nonneg_left hd1le hδ0.le
          _ = δ := by ring
      have hfin := le_trans (le_trans hK1 hδle) hδ22
      simpa [arithIcc_one_eq_singleton, hF] using hfin
    · have hD2 : 2 ≤ D := by omega
      -- #### the sharpness bound
      have hsharp := boxNormPow_le_one_sub (t := s) (by omega) (c₀ := P.leadingCoeff) hlc0
        (D := D) hD2 (L := dSup P Ns N) (F := F) hbF hsupF
      have hboxb : δ ≤ boxNormPow s (fun _ : Fin s => arithIcc P.leadingCoeff D)
          (symIcc (dSup P Ns N)) F := by
        have h := hbox
        rw [hF] at h
        simpa only [uNormPow] using h
      have hδsharp : δ ≤ 1 - min ((((s : ℕ) : ℝ) * |(((P.leadingCoeff : ℤ)) : ℝ)| * (D : ℝ)) /
          (4 * 2 ^ s * (((2 * dSup P Ns N + 1 : ℕ)) : ℝ))) (1 / 2 ^ s) := le_trans hboxb hsharp
      -- the uniform bound on the denominator
      have hdSupBound : (((2 * dSup P Ns N + 1 : ℕ)) : ℝ) ≤ C_P * (Ns : ℝ) := by
        have h'' : ((dSup P Ns N : ℕ) : ℝ) + 1 ≤ (C : ℝ) * (Ns : ℝ) := by
          exact_mod_cast hscale.1
        rw [hC_P]
        push_cast
        linarith
      have hdenle : 4 * 2 ^ s * (((2 * dSup P Ns N + 1 : ℕ)) : ℝ) ≤
          (4 * 2 ^ s * C_P) * (Ns : ℝ) := by
        nlinarith [hdSupBound, pow_pos (by norm_num : (0 : ℝ) < 2) s]
      have hnum : (0 : ℝ) ≤ ((s : ℕ) : ℝ) * |(((P.leadingCoeff : ℤ)) : ℝ)| * (D : ℝ) := by
        positivity
      have hdenpos : (0 : ℝ) < 4 * 2 ^ s * (((2 * dSup P Ns N + 1 : ℕ)) : ℝ) := by
        have : (0 : ℝ) < (((2 * dSup P Ns N + 1 : ℕ)) : ℝ) := by positivity
        positivity
      -- `c₂ · δ' ≤` the min-argument
      have hc₂δ' : c₂ * ((D : ℝ) / (Ns : ℝ)) ≤
          (((s : ℕ) : ℝ) * |(((P.leadingCoeff : ℤ)) : ℝ)| * (D : ℝ)) /
            (4 * 2 ^ s * (((2 * dSup P Ns N + 1 : ℕ)) : ℝ)) := by
        have hNne : (Ns : ℝ) ≠ 0 := ne_of_gt hNspos
        have hCne : 4 * 2 ^ s * C_P ≠ 0 := ne_of_gt (by positivity : (0 : ℝ) < 4 * 2 ^ s * C_P)
        have hleft : c₂ * ((D : ℝ) / (Ns : ℝ)) =
            (((s : ℕ) : ℝ) * |(((P.leadingCoeff : ℤ)) : ℝ)| * (D : ℝ)) /
              ((4 * 2 ^ s * C_P) * (Ns : ℝ)) := by
          rw [hc₂, div_mul_div_eq' _ _ _ _ hCne hNne]
        rw [hleft]
        exact div_le_div_of_nonneg_left hnum hdenpos hdenle
      have hδsharp' : δ ≤ 1 - min (c₂ * ((D : ℝ) / (Ns : ℝ))) (1 / 2 ^ s) := by
        refine le_trans hδsharp ?_
        have hmin : min (c₂ * ((D : ℝ) / (Ns : ℝ))) (1 / 2 ^ s) ≤
            min ((((s : ℕ) : ℝ) * |(((P.leadingCoeff : ℤ)) : ℝ)| * (D : ℝ)) /
              (4 * 2 ^ s * (((2 * dSup P Ns N + 1 : ℕ)) : ℝ))) (1 / 2 ^ s) :=
          min_le_min hc₂δ' le_rfl
        linarith
      -- the uniform `r`
      have hδδ'r : δ * ((D : ℝ) / (Ns : ℝ)) ≤ r := by
        by_cases hle : c₂ * ((D : ℝ) / (Ns : ℝ)) ≤ 1 / 2 ^ s
        · have hmin : min (c₂ * ((D : ℝ) / (Ns : ℝ))) (1 / 2 ^ s) = c₂ * ((D : ℝ) / (Ns : ℝ)) :=
            min_eq_left hle
          rw [hmin] at hδsharp'
          have := prod_le_of_le_one_sub (δ := δ) (δ' := (D : ℝ) / (Ns : ℝ)) (u := c₂)
            hδ'0 hδ'1 hc₂pos hδsharp'
          rw [hr]
          exact le_trans this (le_max_left _ _)
        · have hle' : (1 : ℝ) / 2 ^ s ≤ c₂ * ((D : ℝ) / (Ns : ℝ)) := le_of_lt (not_le.mp hle)
          have hmin : min (c₂ * ((D : ℝ) / (Ns : ℝ))) (1 / 2 ^ s) = 1 / 2 ^ s := min_eq_right hle'
          rw [hmin] at hδsharp'
          rw [hr]
          refine le_trans ?_ (le_max_right _ _)
          have hp : (0 : ℝ) ≤ 1 - 1 / 2 ^ s := by linarith
          calc δ * ((D : ℝ) / (Ns : ℝ)) ≤ (1 - 1 / 2 ^ s) * 1 := by
                exact mul_le_mul hδsharp' hδ'1 hδ'0 hp
            _ = 1 - 1 / 2 ^ s := by ring
      have hKc2 := hKcuniv (δ := δ) (δ' := (D : ℝ) / (Ns : ℝ)) hδ0.le hδ1 hδ'0 hδ'1 hδδ'r
      have hchain' := hchain Ns N D f₀ f₁ δ hd' hN hNs hscale hNNs hD hDNs hs0 hs1 hb0 hb1 hδ0 hδ1 hbox
      have hfac : δ * ((D : ℝ) / (Ns : ℝ)) ≤ 1 := by nlinarith [hδ0, hδ1, hδ'0, hδ'1]
      have hnn : (0 : ℝ) ≤ δ * ((D : ℝ) / (Ns : ℝ)) := by positivity
      exact le_trans (pow_le_pow_of_le_one hnn hfac (le_max_right 4 Kc))
        (le_trans hKc2 hchain')



end

end Work.Peluse.UlowerA
