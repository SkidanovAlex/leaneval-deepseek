/-
# Step 7 capstone (EKL Lemma 4.5, the shape actually consumed downstream)

`step7_measure` produces a set `P ⊆ [0,T]` of density `≥ (1-9ε)T` consisting of times `τ`
with `φ_τ z ∈ X₂` and `φ_{v(τ)} z ∈ 𝒳(ρ)`, where `v(τ) = (θ + (2-η)τ)/2`.  This file turns
that density information into a *point* of `P` satisfying the conclusion of EKL Lemma 4.5:

  `BadAt (ν_{φ_τ z}) ρ (exp (θ - η τ))`,  i.e.  `ν_x([-ρS,ρS]) < ½ ν_x([-S,S])` with
  `S = S(τ) = e^{θ-ητ}`  (EKL (e:introduceS)),

together with `τ ∈ [0,T]` and `φ_τ z ∈ X₂`.

The two ingredients are combined at the found time `τ`:

* arithmetic (`step7_arith`): the "intermediate" time `w = (θ-ητ)/2` is nonnegative and
  `τ + w = v(τ)`, so by the flow law `hcomp` the point `y := φ_w (φ_τ z)` is `φ_{v(τ)} z`,
  which lies in `𝒳(ρ)`; and `S = e^{θ-ητ} ≥ 1` (here `θ ≥ 4T ≥ ητ`).
* scaling transfer (`step7_transfer_nopos`, delegated and verified in
  `Submission/Work/EKLC8Core/step7_transfer_nopos.lean` — the positivity of `ρ` is never used
  by `step7_transfer`, and the abstract hypotheses of the capstone do not provide it):
  `hscale` at `σ = ρ` gives
  `ν_y([-ρ,ρ]) · ν_x([-S,S]) = ν_x([-ρS,ρS]) · ν_y([-1,1])`, and `ν_y([-1,1]) = 1`, so
  `ν_y([-ρ,ρ]) < ½ = ½ ν_y([-1,1])` transfers to `ν_x([-ρS,ρS]) < ½ ν_x([-S,S])`.

The existence of the time `τ` is `step7_density_nonempty`
(`Submission/Work/EKLC8Core/step7_density_nonempty.lean`): `(1-9ε)T > 0` because `ε ≤ 1/100`,
and a set whose `vol` is positive is nonempty.
-/
import Mathlib
import Submission.Work.EKLC8Core.Vol
import Submission.Work.EKLC8Core.step7_measure
import Submission.Work.EKLC8Core.step7_transfer
import Submission.Work.EKLC8Core.step7_transfer_nopos
import Submission.Work.EKLC8Core.step7_arith
import Submission.Work.EKLC8Core.step7_density_nonempty

noncomputable section

namespace Work.EKLC8Core

open MeasureTheory

/-- **Step 7 capstone.**  From the density hypotheses of EKL Lemma 4.5 — `Q₁` covers all but
`εT` of `[0,T]`, `Q₂` covers all but `4εT` of `[0,4T]` — there is a time `τ ∈ [0,T]` with
`φ_τ z ∈ X₂` and `BadAt (ν_{φ_τ z}) ρ (e^{θ-ητ})`.

The density `(1-9ε)T > 0` (here `ε ≤ 1/100`) makes `P ∩ [0,T]` nonempty; at a point of it the
scaling hypothesis `hscale` (which is (F1), `φ_w x = φ_{v(τ)} z`, after `phi_conj_u`) transports
`φ_{v(τ)} z ∈ 𝒳(ρ)` to the conclusion. -/
theorem step7_capstone {Ω : Type*} (Φ : ℝ → Ω → Ω) (ν : Ω → MeasureTheory.Measure ℝ)
    {T θ ε η ρ : ℝ} (hT : 0 < T) (hθ : 4 * T ≤ θ) (hθ' : θ ≤ 6 * T)
    (hε : 0 < ε) (hε' : ε ≤ 1 / 100) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {z : Ω}
    {Xtwo Xrho : Set Ω}
    (hQ₁m : MeasurableSet {τ : ℝ | Φ τ z ∈ Xtwo})
    (hQ₂m : MeasurableSet {v : ℝ | Φ v z ∈ Xrho})
    (hQ₁ : (1 - ε) * T ≤ vol ({τ : ℝ | Φ τ z ∈ Xtwo} ∩ Set.Icc 0 T))
    (hQ₂ : (1 - ε) * (4 * T) ≤ vol ({v : ℝ | Φ v z ∈ Xrho} ∩ Set.Icc 0 (4 * T)))
    (hcomp : ∀ τ w : ℝ, Φ w (Φ τ z) = Φ (τ + w) z)
    (hXrho : ∀ v : ℝ, Φ v z ∈ Xrho → InXrho (ν (Φ v z)) ρ)
    (hnorm : ∀ x : Ω, (ν x).real (Set.Icc (-1) 1) = 1)
    (hfin : ∀ x : Ω, ∀ S : ℝ, 0 < S → ν x (Set.Icc (-S) S) ≠ ⊤)
    (hscale : ∀ τ ∈ Set.Icc 0 T, ∀ σ : ℝ,
      (ν (Φ ((θ - η * τ) / 2) (Φ τ z))).real (Set.Icc (-σ) σ)
          * (ν (Φ τ z)).real (Set.Icc (-(Real.exp (θ - η * τ))) (Real.exp (θ - η * τ)))
        = (ν (Φ τ z)).real
            (Set.Icc (-(σ * Real.exp (θ - η * τ))) (σ * Real.exp (θ - η * τ)))
          * (ν (Φ ((θ - η * τ) / 2) (Φ τ z))).real (Set.Icc (-1) 1)) :
    ∃ τ ∈ Set.Icc 0 T, Φ τ z ∈ Xtwo ∧
      BadAt (ν (Φ τ z)) ρ (Real.exp (θ - η * τ)) := by
  -- The set of "good" times produced by `step7_measure`.
  set A : Set ℝ := {τ : ℝ | Φ τ z ∈ Xtwo ∧ Φ ((θ + (2 - η) * τ) / 2) z ∈ Xrho} with hA
  have hB : (1 - 9 * ε) * T ≤ vol (A ∩ Set.Icc 0 T) := by
    have h0 := step7_measure (Q₁ := {τ : ℝ | Φ τ z ∈ Xtwo})
      (Q₂ := {v : ℝ | Φ v z ∈ Xrho}) hT hθ hθ' hε hε' hη0 hη1 hQ₁m hQ₂m hQ₁ hQ₂
    have hset : {τ : ℝ | τ ∈ {τ : ℝ | Φ τ z ∈ Xtwo}
        ∧ (θ + (2 - η) * τ) / 2 ∈ {v : ℝ | Φ v z ∈ Xrho}} = A := by
      ext τ; simp [hA]
    rwa [hset] at h0
  -- Its density is positive, so `A ∩ [0,T]` is nonempty.
  have hne : (A ∩ Set.Icc 0 T).Nonempty :=
    step7_density_nonempty hT hε (by nlinarith [hε']) hB
  obtain ⟨τ, hτ⟩ := hne
  rw [Set.mem_inter_iff] at hτ
  obtain ⟨hτA, hτIcc⟩ := hτ
  rw [hA] at hτA
  obtain ⟨hτXtwo, hτQ₂⟩ := hτA
  refine ⟨τ, hτIcc, hτXtwo, ?_⟩
  -- Arithmetic: `w := (θ-ητ)/2 ≥ 0` and `τ + w = (θ+(2-η)τ)/2`.
  have hτ0 : 0 ≤ τ := hτIcc.1
  have hτ1 : τ ≤ T := hτIcc.2
  obtain ⟨-, hsum, -, -⟩ := step7_arith hT hθ hθ' hτ0 hτ1 hη0 hη1
  -- The intermediate point `y := φ_w (φ_τ z)` is `φ_{v(τ)} z`, hence lies in `𝒳(ρ)`.
  have hΦ : Φ ((θ - η * τ) / 2) (Φ τ z) = Φ ((θ + (2 - η) * τ) / 2) z := by
    rw [hcomp τ ((θ - η * τ) / 2), hsum]
  have hbad1 : BadAt (ν (Φ ((θ - η * τ) / 2) (Φ τ z))) ρ 1 := by
    have h := hXrho ((θ + (2 - η) * τ) / 2) hτQ₂
    rwa [← hΦ] at h
  -- `S := e^{θ-ητ} ≥ 1`.
  have hS1 : 1 ≤ Real.exp (θ - η * τ) := by
    refine Real.one_le_exp ?_
    have hητ : η * τ ≤ T := by
      have hm := mul_le_mul hη1 hτ1 hτ0 (by norm_num : (0 : ℝ) ≤ 1)
      simpa using hm
    linarith
  -- Transfer the badness from `y` back to `x = φ_τ z` at scale `S`.
  exact step7_transfer_nopos (ν₀ := ν (Φ τ z))
    (ν₁ := ν (Φ ((θ - η * τ) / 2) (Φ τ z))) (ρ := ρ) (S := Real.exp (θ - η * τ))
    hS1 (hnorm (Φ τ z)) (hnorm _) (hfin (Φ τ z) _ (Real.exp_pos _))
    (hscale τ hτIcc) hbad1

end Work.EKLC8Core
