import Mathlib
import Submission.Work.Peluse.LadderA.symmWindowSplit
import Submission.Work.Peluse.LadderA.symmShiftBound

/-!
# The *symmetric* form of Peluse's Theorem 3.5

`Work.Peluse.UControl.PeluseConcatFixed` states Peluse's concatenation theorem
(arXiv:1909.00309, Theorem 3.5) with the average over the *one-sided* parameter range
`a ∈ [M₂] = {1, …, M₂}`.  The ladder of §5 (Lemma 5.7, the source of
`Work.Peluse.C46.PeluseLadderA`) averages over the *symmetric* parameter box
`((-M₂, M₂) ∩ ℤ)` instead, and it is the symmetric form that the ladder's peel step consumes.

This file derives the symmetric form from the one-sided one.  The only point is the trivial one:
the symmetric window `{1-M₂, …, M₂-1}` is the union of the two translates `{1-M₂, …, 0}` and
`{0, …, M₂-1}` of `[M₂]`, which overlap in the single point `0`; hence, writing
`G α = ‖f‖_{□^s_{(cα+d_i)[M₁]}([-N,N])}` and `W = ∑_{α ∈ (-M₂,M₂)} G α`,

  `∑_{a ∈ [M₂]} G (a - M₂) + ∑_{a ∈ [M₂]} G (a - 1) = W + G 0 ≥ W ≥ (2M₂-1) δ`,

so one of the two translates averages to at least `δ (2M₂-1)/(2M₂) ≥ δ/2`.  Each translate is an
`[M₂]`-average of box norms of the form `(c a + d_i)[M₁]` with a shift family `d_i - c·M₂`
respectively `d_i - c` (the shift bound is absorbed into `C + 1`), i.e. exactly the hypotheses of
`PeluseConcatFixed` at the parameter `δ/2` and with the identical conclusion window
`c[⌊δ'M₁M₂⌋]`.  The factor `2` is absorbed into the existential constants `A` (made large) and `C'`
(made small), so the witnesses still depend only on `(C, s)`.

Auxiliary lemmas (proved in the sibling modules imported above):

* `Work.Peluse.LadderA.symmWindowSplit` — the window split `W + G 0 ≥ (2M₂-1)δ ⟹ ∃` translate with
  average `≥ δ/2`;
* `Work.Peluse.LadderA.symmShiftBound` — the shifted shift family still satisfies the increase of
  the shift constant from `C` to `C + 1`.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderA

theorem concatFixed_symm (h : Work.Peluse.UControl.PeluseConcatFixed) :
    ∀ C : ℕ, ∀ s : ℕ, 1 ≤ s →
      ∃ s' : ℕ, 1 ≤ s' ∧ ∃ C' : ℝ, 0 < C' ∧ ∃ A : ℝ, 1 ≤ A ∧ ∃ K : ℕ, 1 ≤ K ∧
      ∀ (c : ℤ), 0 < c →
      ∀ (N M₁ M₂ : ℕ) (d : Fin s → ℤ) (δ δ' : ℝ) (f : ℤ → ℂ),
        1 ≤ M₂ → M₂ ≤ M₁ → 1 ≤ N → (M₁ : ℝ) * (M₂ : ℝ) ≤ (N : ℝ) / (c : ℝ) →
        (∀ i : Fin s, |d i| ≤ (C : ℤ) * (N : ℤ) / (M₁ : ℤ)) →
        Work.Peluse.SupportIn f N → (∀ x : ℤ, ‖f x‖ ≤ 1) →
        0 < δ → δ ≤ 1 → 0 < δ' → A * δ' ≤ δ ^ K → A ≤ (M₂ : ℝ) * (δ * δ') ^ K →
        δ ≤ (((Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)).card : ℝ))⁻¹ *
              ∑ a ∈ Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ),
                Work.Peluse.boxNorm s (fun i : Fin s => Work.Peluse.arithIcc (c * a + d i) M₁)
                  (Work.Peluse.symIcc N) f →
        C' * (δ * δ') ^ K ≤
          Work.Peluse.uNorm s' (Work.Peluse.arithIcc c (⌊δ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat)
            (Work.Peluse.symIcc N) f := by
  intro C s hs
  -- the witnesses of the one-sided statement, at the shift constant `C + 1`
  obtain ⟨s', hs'1, C₀, _hC₀, A₀, hA₀, K, hK, himpl⟩ := h (C + 1) s hs
  -- our witnesses: the *same* `s'` and `K`, the constant `A` enlarged by `2^K` and `C'` shrunk
  refine ⟨s', hs'1, C₀ / (2:ℝ)^K, ?_, A₀ * (2:ℝ)^K, ?_, K, hK, ?_⟩
  · positivity
  · have h2 : (0:ℝ) < (2:ℝ)^K := by positivity
    have h1 : (1:ℝ) ≤ (2:ℝ)^K := one_le_pow₀ (show (1:ℝ) ≤ 2 by norm_num)
    nlinarith [hA₀]
  · intro c hc N M₁ M₂ d δ δ' f h1M₂ hM₂M₁ hN hscale hd hsupp hbdd hδ0 hδ1 hδ'0 hAδ' hAne hsym
    have h2 : (0:ℝ) < (2:ℝ)^K := by positivity
    -- the enlarged `A` gives `A₀ δ' ≤ (δ/2)^K`
    have hhalf : A₀ * δ' ≤ (δ/2)^K := by
      have key : A₀ * δ' * (2:ℝ)^K ≤ δ^K := by
        calc A₀ * δ' * (2:ℝ)^K = (A₀ * (2:ℝ)^K) * δ' := by ring
          _ ≤ δ^K := hAδ'
      rw [div_pow]
      exact (le_div_iff₀ h2).mpr key
    -- and `A₀ ≤ M₂ ((δ/2) δ')^K`
    have hAne' : A₀ ≤ (M₂:ℝ) * ((δ/2) * δ')^K := by
      have hpow : ((δ/2) * δ')^K = (δ * δ')^K / (2:ℝ)^K := by
        rw [show (δ/2) * δ' = (δ * δ') / 2 by ring, div_pow]
      rw [hpow]
      have hM : (M₂:ℝ) * ((δ*δ')^K / (2:ℝ)^K) = (M₂:ℝ) * (δ*δ')^K / (2:ℝ)^K := by ring
      rw [hM]
      exact (le_div_iff₀ h2).mpr hAne
    -- the symmetric average splits into two one-sided windows, one of which averages `≥ δ/2`
    have hsplit := symmWindowSplit c h1M₂ d (Work.Peluse.symIcc N) f hδ0 hsym
    -- the conclusion's constant is exactly the one-sided statement's constant at `δ/2`
    have hkey : (C₀ / (2:ℝ)^K) * (δ * δ')^K = C₀ * ((δ/2) * δ')^K := by
      rw [show (δ/2) * δ' = (δ * δ') / 2 by ring, div_pow]
      ring
    rcases hsplit with hcase | hcase
    · have hshift : ∀ i : Fin s,
          |(fun i : Fin s => d i - c * (M₂:ℤ)) i| ≤ ((C+1:ℕ):ℤ) * (N:ℤ) / (M₁:ℤ) :=
        (symmShiftBound hc h1M₂ hM₂M₁ hscale d hd).1
      have hconc := himpl c hc N M₁ M₂ (fun i : Fin s => d i - c * (M₂:ℤ)) (δ/2) δ' f
        h1M₂ hM₂M₁ hN hscale hshift hsupp hbdd (by positivity) (by linarith) hδ'0 hhalf hAne' hcase
      rw [hkey]
      exact hconc
    · have hshift : ∀ i : Fin s,
          |(fun i : Fin s => d i - c) i| ≤ ((C+1:ℕ):ℤ) * (N:ℤ) / (M₁:ℤ) :=
        (symmShiftBound hc h1M₂ hM₂M₁ hscale d hd).2
      have hconc := himpl c hc N M₁ M₂ (fun i : Fin s => d i - c) (δ/2) δ' f
        h1M₂ hM₂M₁ hN hscale hshift hsupp hbdd (by positivity) (by linarith) hδ'0 hhalf hAne' hcase
      rw [hkey]
      exact hconc

end Work.Peluse.LadderA
