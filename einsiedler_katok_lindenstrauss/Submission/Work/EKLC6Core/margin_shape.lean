import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.contract_rate
import Submission.Work.EKLC6Core.shape_pastSig_eq
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLC6Core.atom_iSup_comap_iterate_eq

/-!
# `Work.EKLC6Core.margin_shape` — the atoms of the descending plaque algebra are open plaques

Let `U ≤ SL₃(ℝ)` be horospherical, `a = aDiag t`, and let `M` be a σ-algebra whose atoms at the
points `aⁿ x` of the orbit of `x` are *plaques*: relatively open, bounded, and containing balls of
the appropriate radius.

**The margin hypothesis.**  The naive hope that the atom of `x` in `A = ⨆ₙ a⁻ⁿ M` is simply the
atom of `x` in `M` is false: the atom of `A` is the intersection `⋂ₙ θₙ⁻¹(Sₙ)` of the transported
plaque conditions `Sₙ = shape M U (aⁿ x)`, and an intersection of relatively open sets need not be
open.  What makes it open is a *margin* of the right size: if

  `Uball U (c μⁿ) ⊆ shape M U (aⁿ x)`   for all `n ≥ N`,

with `μ` strictly larger than the contraction rate `λ` of `a` on `U`, then every `u` in the
finitely many low-level constraints is bounded by `ρ ≤ c`, and hence its conjugates
`θₙ(u) = aⁿ u a⁻ⁿ` are squeezed into `Uball U (ρ λⁿ) ⊆ Uball U (c μⁿ) ⊆ Sₙ` for **all** `n ≥ N` —
so the remaining constraints are automatic and the shape is a *finite* intersection of relatively
open sets, hence relatively open.

This is the missing half of Pisa 7.38: the paper's shells give the margin at the rate `λⁿ` (which
only implies the "sandwich" of Definition 7.25), while the *same* thin-boundary estimate gives it
at any rate `μⁿ` with `μ ∈ (λ,1)` — and *that* is what makes the atoms open plaques.
-/

open MeasureTheory Topology Filter
open scoped ENNReal

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **The nesting lemma.**  If along the orbit the `M`-shapes are relatively open, bounded by
`Uball U ρ`, and contain the balls `Uball U (c μⁿ)` for all `n ≥ N`, with `0 < ρ ≤ c` and
`0 ≤ λ < μ < 1` where `λ` is a contraction rate for `aDiag t` on `U`, then the shape of the atom
of `x` in the descending σ-algebra `⨆ₙ comap ((aDiag t ·)^[n]) M` is relatively open in `U`. -/
theorem isOpen_shape_pastSig_of_margin {U : Subgroup SL3} {t : Fin 3 → ℝ} (hU : IsHoro U)
    {lam mu : ℝ} (hlam0 : 0 ≤ lam) (hlammu : lam < mu) (hmu1 : mu < 1)
    {M : MeasurableSpace X3} {x : X3} {c ρ : ℝ} (hc : 0 < c) (hρ : 0 < ρ)
    {N : ℕ}
    (hrate : ∀ n : ℕ, ∀ u : SL3, u ∈ U → u ∈ Work.EKLComp.Uball U ρ →
        aDiag t ^ n * u * (aDiag t ^ n)⁻¹ ∈ Work.EKLComp.Uball U (ρ * lam ^ n))
    (hopen : ∀ n : ℕ, ∃ W : Set SL3, IsOpen W ∧
        shape M U (((fun y : X3 => aDiag t • y)^[n]) x) = W ∩ (U : Set SL3))
    (hbdd : shape M U x ⊆ Work.EKLComp.Uball U ρ)
    (hmargin : ∀ n : ℕ, N ≤ n → Work.EKLComp.Uball U (c * mu ^ n)
        ⊆ shape M U (((fun y : X3 => aDiag t • y)^[n]) x)) :
    ∃ W : Set SL3, IsOpen W ∧
      shape (⨆ n : ℕ, MeasurableSpace.comap ((fun y : X3 => aDiag t • y)^[n]) M) U x
        = W ∩ (U : Set SL3) := by
  classical
  choose W hWopen hWeq using hopen
  have hmu0 : 0 < mu := lt_of_le_of_lt hlam0 hlammu
  have hratio : lam / mu < 1 := (div_lt_one hmu0).mpr hlammu
  have hratio0 : 0 ≤ lam / mu := div_nonneg hlam0 (le_of_lt hmu0)
  have hlim : Filter.Tendsto (fun n : ℕ => (lam / mu) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratio0 hratio
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ρ * (lam / mu) ^ n ≤ c := by
    have h1 : ∀ᶠ n : ℕ in Filter.atTop, (lam / mu) ^ n < c / ρ :=
      hlim.eventually (isOpen_Iio.mem_nhds (div_pos hc hρ))
    filter_upwards [h1] with n hn
    rw [lt_div_iff₀ hρ] at hn
    linarith
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hev
  set K : ℕ := max N N₁ + 1 with hKdef
  have hKpos : 0 < K := by omega
  refine ⟨⋂ n ∈ Finset.range K, {g : SL3 | aDiag t ^ n * g * (aDiag t ^ n)⁻¹ ∈ W n},
    isOpen_biInter_finset (fun n _ => (hWopen n).preimage (by fun_prop)), ?_⟩
  rw [shape_pastSig_eq hU x]
  ext u
  constructor
  · rintro ⟨huU, hu⟩
    refine ⟨?_, huU⟩
    refine Set.mem_biInter ?_
    intro n hn
    have h := hu n
    rw [hWeq n] at h
    exact h.1
  · rintro ⟨huO, huU⟩
    rw [Set.mem_iInter₂] at huO
    refine ⟨huU, fun n => ?_⟩
    rw [hWeq n]
    refine ⟨?_, conj_pow_mem_U hU huU n⟩
    by_cases hn : n < K
    · exact huO n (Finset.mem_range.mpr hn)
    · push Not at hn
      -- `u` itself lies in the level-0 plaque, hence in `Uball U ρ`
      have huBall : u ∈ Work.EKLComp.Uball U ρ := by
        have h0 := huO 0 (Finset.mem_range.mpr hKpos)
        have h0' : u ∈ W 0 := by simpa using h0
        have hthis : u ∈ shape M U (((fun y : X3 => aDiag t • y)^[0]) x) := by
          rw [hWeq 0]
          exact ⟨h0', huU⟩
        rw [Function.iterate_zero_apply] at hthis
        exact hbdd hthis
      have hstep := hrate n u huU huBall
      have hle : ρ * lam ^ n ≤ c * mu ^ n := by
        have h1 : ρ * (lam / mu) ^ n * mu ^ n ≤ c * mu ^ n :=
          mul_le_mul_of_nonneg_right (hN₁ n (by omega)) (pow_nonneg (le_of_lt hmu0) n)
        have h2 : ρ * (lam / mu) ^ n * mu ^ n = ρ * lam ^ n := by
          rw [mul_assoc, div_pow, div_mul_cancel₀ _ (pow_ne_zero n (ne_of_gt hmu0))]
        rwa [h2] at h1
      have hmem : aDiag t ^ n * u * (aDiag t ^ n)⁻¹
          ∈ shape M U (((fun y : X3 => aDiag t • y)^[n]) x) :=
        hmargin n (by omega) (Work.EKLComp.Uball_mono hle hstep)
      rw [hWeq n] at hmem
      exact hmem.1

end Work.EKLC6Core
