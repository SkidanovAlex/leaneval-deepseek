/-
# The §8 packet family is minor arc at height `l₁ - 1`

Krause--Mirek--Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial
averages*, Annals 195 (2022).  This file proves

`Work.KMTPlan.A6Clean.packetFamF_minorArc`:

if the lift family `W` is supported on the arithmetic frequencies of **exact** Ionescu--Wainger
height `2^{l₁}` (`W α = 0` for `α ∉ (ℚ/ℤ)_{l₁} = (ℚ/ℤ)_{≤l₁} \ (ℚ/ℤ)_{≤l₁-1}`), then every slice
of the packet family

  `θ ↦ ∑_{α ∈ (ℚ/ℤ)_{≤l₁}} e(-θ.val · α) · W α X`

has its `ℤ/Qℤ`-spectrum (the discrete Fourier transform) supported at height `≥ l₁`, i.e. it
satisfies the Ionescu--Wainger minor-arc condition `MdlIwMinorArc ρ (l₁-1) Q` at height `l₁ - 1`
(`Q = arithQ ρ (max l₁ l₂)` is the common denominator of `(ℚ/ℤ)_{≤ max l₁ l₂}`).

The mathematics is the orthogonality of the `ℤ/Qℤ`-characters: the DFT of the packet slice at a
frequency `ξ` is `Q · ∑_{α ∈ A, α = -ξ/Q} W α X`, and `-ξ/Q ∈ (ℚ/ℤ)_{≤l₁-1}` whenever `ξ` has
height `< l₁` -- where `W` vanishes.  The two auxiliary lemmas below are the analytic/algebraic
content: `exists_toAddCircle_eq_of_nsmul_eq_zero` (the image of `ZMod.toAddCircle` is the
`Q`-torsion of the circle) and `sum_stdAddChar_mul_fourier_toAddCircle` (the orthogonality sum).
-/
import Mathlib
import Submission.Work.KMTPlan.A6Clean.AdelicPacketFam

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6Clean

open Finset

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-- **The image of `ZMod.toAddCircle` is exactly the `Q`-torsion of the circle.**  Every element
of `ℝ/ℤ` killed by `Q` is `i/Q mod 1` for a unique `i : ZMod Q`. -/
theorem exists_toAddCircle_eq_of_nsmul_eq_zero {Q : ℕ} [NeZero Q] {α : AddCircle (1 : ℝ)}
    (hα : (Q : ℕ) • α = 0) : ∃ i : ZMod Q, (ZMod.toAddCircle i : AddCircle (1 : ℝ)) = α := by
  obtain ⟨x, hx⟩ : ∃ x : ℝ, (x : AddCircle (1 : ℝ)) = α :=
    ⟨Quotient.out α, QuotientAddGroup.out_eq' α⟩
  rw [← hx] at hα
  rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at hα
  obtain ⟨m, hm⟩ := hα
  rw [zsmul_one, nsmul_eq_mul] at hm
  refine ⟨(m : ZMod Q), ?_⟩
  rw [ZMod.toAddCircle_intCast, ← hx]
  congr 1
  have hQ : (Q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  rw [hm]
  field_simp

/-- **Orthogonality of the `ℤ/Q`-characters against the Fourier modes of the circle.**  For
`i, ξ : ℤ/Qℤ`,

  `∑_θ e(-θξ/Q) · e(-θ · i/Q) = Q` if `i + ξ = 0` and `0` otherwise. -/
theorem sum_stdAddChar_mul_fourier_toAddCircle {Q : ℕ} [NeZero Q] (i ξ : ZMod Q) :
    ∑ θ : ZMod Q, (ZMod.stdAddChar (-(θ * ξ)) *
        (fourier (T := 1) (-(θ.val : ℤ)) (ZMod.toAddCircle i) : ℂ))
      = if i + ξ = 0 then (Q : ℂ) else 0 := by
  have hterm : ∀ θ : ZMod Q, (ZMod.stdAddChar (-(θ * ξ)) *
      (fourier (T := 1) (-(θ.val : ℤ)) (ZMod.toAddCircle i) : ℂ))
      = ZMod.stdAddChar (θ * (-ξ - i)) := by
    intro θ
    rw [← Work.KMTPlan.A6.StdAddCharFourier i (-(θ.val : ℤ))]
    have hv : ((-(θ.val : ℤ) : ℤ) : ZMod Q) = -θ := by
      rw [Int.cast_neg, Int.cast_natCast, ZMod.natCast_zmod_val]
    rw [hv, ← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [hterm]
  rw [AddChar.sum_mulShift (-ξ - i) (ZMod.isPrimitive_stdAddChar Q), ZMod.card Q]
  have hneg : (-ξ - i = 0) ↔ (i + ξ = 0) := by
    rw [show -ξ - i = -(i + ξ) by abel]
    exact neg_eq_zero
  push_cast
  by_cases h : i + ξ = 0
  · rw [if_pos (hneg.mpr h), if_pos h]
  · rw [if_neg (fun hh => h (hneg.mp hh)), if_neg h]

/-- Negation preserves the Ionescu--Wainger arithmetic frequency set `(ℚ/ℤ)_{≤l}` (it is a union
of torsion subgroups). -/
theorem iwArithFreqs_neg {ρ : ℝ} {l : ℕ} {α : Circ}
    (h : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l) :
    -α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l := by
  obtain ⟨q, hq, hqα⟩ := Work.Analysis.IonescuWainger.mem_iwArithFreqs.mp h
  exact Work.Analysis.IonescuWainger.mem_iwArithFreqs.mpr ⟨q, hq, by rw [smul_neg, hqα, neg_zero]⟩

/-- A `ℤ/Qℤ`-element of Ionescu--Wainger height `< l₁` corresponds (via `ZMod.toAddCircle`) to a
point of `(ℚ/ℤ)_{≤l₁-1}`. -/
theorem toAddCircle_mem_iwArithFreqs {ρ : ℝ} {l Q : ℕ} [NeZero Q] {ξ : ZMod Q}
    (hξ : ξ ∈ Work.KMTPlan.A6.iwLowFreqs ρ l Q) :
    (ZMod.toAddCircle ξ : Circ) ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l := by
  rw [Work.KMTPlan.A6.iwLowFreqs, Finset.mem_filter] at hξ
  obtain ⟨q, hq, hqξ⟩ := hξ.2
  exact Work.Analysis.IonescuWainger.mem_iwArithFreqs.mpr ⟨q, hq, by
    rw [← map_nsmul (ZMod.toAddCircle (N := Q)) q ξ, hqξ, map_zero]⟩

theorem packetFamF_minorArc (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) [NeZero (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))]
    (W : Work.Analysis.IonescuWainger.Circle → ℝ → ℂ)
    (hW : ∀ α, α ∉ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ → W α = 0)
    (n : ℕ) (X : ℝ) :
    Work.KMTPlan.A6.MdlIwMinorArc ρ (l₁ - 1)
      (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂))
      (Work.KMTPlan.A6Clean.packetFamF ρ a l₁ l₂ k₁ k₂ (fun _ => W) n X) := by
  intro ξ hξ
  -- The orthogonality sum: at an arithmetic frequency of *exact* height `l₁` and a low frequency
  -- `ξ`, the `θ`-sum vanishes.
  have hSzero : ∀ α : Circ, α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ →
      α ∉ Work.Analysis.IonescuWainger.iwArithFreqs ρ (l₁ - 1) →
      (∑ j : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
        ZMod.stdAddChar (-(j * ξ)) * (fourier (T := 1) (-(j.val : ℤ)) α : ℂ)) = 0 := by
    intro α hα hαnot
    -- `α` is a `Q`-torsion point, hence `α = toAddCircle i` for some `i : ZMod Q`.
    have hQα : (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) • α = 0 :=
      Work.KMTAreas.A7.arithQ_nsmul_eq_zero
        (Work.Analysis.IonescuWainger.iwArithFreqs_mono hρ hρ1 (le_max_left l₁ l₂) hα)
    obtain ⟨i, hi⟩ := exists_toAddCircle_eq_of_nsmul_eq_zero hQα
    -- `i + ξ = 0` would put `α = -toAddCircle ξ` at the low height `l₁ - 1`.
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
  · simp only [packetFamF_apply, if_pos hg]
    simp only [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero (fun α hα => ?_)
    by_cases hw : W α X = 0
    · simp [hw]
    · -- otherwise `α` lies in the exact-height set, and the `θ`-sum vanishes by `hSzero`
      have hαnew : α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l₁ := by
        by_contra hcon
        exact hw (congrFun (hW α hcon) X)
      have hαnot : α ∉ Work.Analysis.IonescuWainger.iwArithFreqs ρ (l₁ - 1) :=
        (Finset.mem_sdiff.mp hαnew).2
      have hfac : (∑ j : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
            ZMod.stdAddChar (-(j * ξ)) • ((fourier (T := 1) (-(j.val : ℤ)) α : ℂ) * W α X))
          = (∑ j : ZMod (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
              ZMod.stdAddChar (-(j * ξ)) * (fourier (T := 1) (-(j.val : ℤ)) α : ℂ)) * W α X := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [smul_eq_mul, mul_assoc]
      rw [hfac, hSzero α hα hαnot, zero_mul]
  · simp only [packetFamF_apply, if_neg hg]
    simp

end Work.KMTPlan.A6Clean
