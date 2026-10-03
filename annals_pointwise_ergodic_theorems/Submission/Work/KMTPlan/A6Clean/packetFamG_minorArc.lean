/-
# The §8 `g`-side packet family is minor arc at height `l₂ - 1`

This is the `g`-side twin of `Work.KMTPlan.A6Clean.packetFamF_minorArc`: if the lift family `W`
is supported on the arithmetic frequencies of **exact** Ionescu--Wainger height `2^{l₂}`
(`W α = 0` for `α ∉ (ℚ/ℤ)_{l₂} = (ℚ/ℤ)_{≤l₂} \ (ℚ/ℤ)_{≤l₂-1}`), then every slice of the packet
family

  `θ ↦ 1_{goodScale} · ∑_{β ∈ (ℚ/ℤ)_{≤l₂}} e(-θ.val · β) · W β X`

has its `ℤ/Qℤ`-spectrum (the discrete Fourier transform) supported at height `≥ l₂`, i.e. it
satisfies the Ionescu--Wainger minor-arc condition `MdlIwMinorArc ρ (l₂-1) Q` at height `l₂ - 1`
(with `Q = arithQ ρ (max l₁ l₂)` the common denominator of `(ℚ/ℤ)_{≤ max l₁ l₂}`).

The mathematics is again the orthogonality of the `ℤ/Qℤ`-characters (proved in the `f`-side
module and reused here): the DFT of the packet slice at a frequency `ξ` is
`Q · ∑_{β ∈ A, β = -ξ/Q} W β X`, and `-ξ/Q ∈ (ℚ/ℤ)_{≤l₂-1}` whenever `ξ` has height `< l₂` --
where `W` vanishes.
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.packetFamF_minorArc

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6Clean

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

theorem packetFamG_minorArc (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) [NeZero (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))]
    (W : Work.Analysis.IonescuWainger.Circle → ℝ → ℂ)
    (hW : ∀ α, α ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ → W α = 0)
    (n : ℕ) (X : ℝ) :
    Work.KMTPlan.A6.MdlIwMinorArc ρ (l₂ - 1)
      (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
      (Work.KMTPlan.A6Clean.packetFamG ρ a l₁ l₂ k₁ k₂ (fun _ => W) n X) := by
  intro ξ hξ
  -- The orthogonality sum: at an arithmetic frequency of *exact* height `l₂` and a low frequency
  -- `ξ`, the `θ`-sum vanishes.
  have hSzero : ∀ α : Circ, α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ →
      α ∉ Work.Analysis.IonescuWainger.iwArithFreqs ρ (l₂ - 1) →
      (∑ j : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
        ZMod.stdAddChar (-(j * ξ)) * (fourier (T := 1) (-(j.val : ℤ)) α : ℂ)) = 0 := by
    intro α hα hαnot
    -- `α` is a `Q`-torsion point, hence `α = toAddCircle i` for some `i : ZMod Q`.
    have hQα : (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) • α = 0 :=
      Work.KMTAreas.A7.arithQ_nsmul_eq_zero
        (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 (le_max_right l₁ l₂) hα)
    obtain ⟨i, hi⟩ := exists_toAddCircle_eq_of_nsmul_eq_zero hQα
    -- `i + ξ = 0` would put `α = -toAddCircle ξ` at the low height `l₂ - 1`.
    have hne : i + ξ ≠ 0 := by
      intro h0
      apply hαnot
      have hneg : (ZMod.toAddCircle i : AddCircle (1 : ℝ)) =
          -(ZMod.toAddCircle ξ : AddCircle (1 : ℝ)) := by
        rw [← map_neg, ZMod.toAddCircle_inj, ← add_eq_zero_iff_eq_neg]
        exact h0
      rw [hi] at hneg
      rw [hneg]
      exact iwArithFreqs_neg (toAddCircle_mem_iwArithFreqs hξ)
    rw [show (∑ j : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
          ZMod.stdAddChar (-(j * ξ)) * (fourier (T := 1) (-(j.val : ℤ)) α : ℂ))
        = ∑ j : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
          ZMod.stdAddChar (-(j * ξ)) *
            (fourier (T := 1) (-(j.val : ℤ)) (ZMod.toAddCircle i) : ℂ) from
        Finset.sum_congr rfl (fun j _ => by rw [← hi])]
    rw [sum_stdAddChar_mul_fourier_toAddCircle i ξ, if_neg hne]
  rw [ZMod.dft_apply]
  by_cases hg : Work.KMTPlan.A6.goodScale (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
      (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) (Nat.floor (a n))
  · simp only [packetFamG_apply, if_pos hg]
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun α hα => ?_)
    by_cases hw : W α X = 0
    · simp [hw]
    · -- otherwise `α` lies in the exact-height set, and the `θ`-sum vanishes by `hSzero`
      have hαnew : α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₂ := by
        by_contra hcon
        exact hw (congrFun (hW α hcon) X)
      have hαnot : α ∉ Work.Analysis.IonescuWainger.iwArithFreqs ρ (l₂ - 1) :=
        (Finset.mem_sdiff.mp hαnew).2
      have hfac : (∑ j : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
            ZMod.stdAddChar (-(j * ξ)) • ((fourier (T := 1) (-(j.val : ℤ)) α : ℂ) * W α X))
          = (∑ j : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
              ZMod.stdAddChar (-(j * ξ)) * (fourier (T := 1) (-(j.val : ℤ)) α : ℂ)) * W α X := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [smul_eq_mul, mul_assoc]
      rw [hfac, hSzero α hα hαnot, zero_mul]
  · simp only [packetFamG_apply, if_neg hg]
    simp

end Work.KMTPlan.A6Clean
