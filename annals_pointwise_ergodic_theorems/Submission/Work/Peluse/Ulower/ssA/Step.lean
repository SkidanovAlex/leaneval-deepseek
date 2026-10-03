import Mathlib
import Submission.Work.Peluse.Ulower.lemma75_control
import Submission.Work.Peluse.UlowerA.ChainA
import Submission.Work.Peluse.UlowerA.levelTwoExtractA
import Submission.Work.Peluse.Ulower.ssA.BlindConvert

/-!
# The assembly of the single degree-lowering step (`Work.Peluse.Ulower.steple_of`)

From the three named pieces

* `Work.Peluse.Ulower.StepLe.levelTwoExtract` (the level-`2` extraction: the box-norm bound gives
  phases `β` with a large *chirped* aggregate),
* `Work.Peluse.Ulower.StepLe.blindConvertK` (the crux: the chirped aggregate plus the major-arc
  hypothesis `h2` produce a **blind** family `ψ` with a large aggregate),
* `Work.Peluse.Ulower.lemma75_control` (Peluse's Lemma 7.5 for blind phases),

we obtain the single-step interface `Work.Peluse.Ulower.StepLe P K`.
The assembly is bookkeeping only.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Ulower

noncomputable section

open Work.Peluse

theorem ssStepAux {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree) (h1 : PeluseU2Inverse)
    (h2 : PeluseMajorArc P) :
    ∀ C : ℕ, 1 ≤ C → Work.Peluse.UlowerA.StepLeA P C
      (max 1 |(((P.leadingCoeff : ℤ)) : ℝ)|) := by
  intro C hC t ht
  obtain ⟨σ, rfl⟩ : ∃ σ, t = σ + 2 := ⟨t - 2, by omega⟩
  have hσ : 1 ≤ σ := by omega
  obtain ⟨cL, hcL, pL, qL, hpL, hqL, hL⟩ :=
    Work.Peluse.UlowerA.levelTwoExtractA hd h1 (max 1 |(((P.leadingCoeff : ℤ)) : ℝ)|)
      (le_max_left _ _) σ hσ C hC
  obtain ⟨cB, hcB, KB, hKB, hB⟩ :=
    Work.Peluse.Ulower.SsA.ssBlindConvert hd h2 (max 1 |(((P.leadingCoeff : ℤ)) : ℝ)|)
      (le_max_left _ _) C hC σ hσ
  obtain ⟨K75, hK75, c75, hc75, h75⟩ := lemma75_control σ hσ
  have hpL0 : 0 < pL := by omega
  have hqL0 : 0 < qL := by omega
  have hKB0 : 0 < KB := by omega
  have hK750 : 0 < K75 := by omega
  refine ⟨pL * KB * K75, qL * (KB * K75) + KB * K75, ?_, ?_,
    c75 * cB ^ K75 * cL ^ (KB * K75), by positivity, ?_⟩
  · have h : 0 < pL * KB * K75 := by positivity
    omega
  · have h : 0 < qL * (KB * K75) + KB * K75 := by positivity
    omega
  intro B Ns N D f₀ f₁ θ hd' hC' hN hNs hSc hNNs hD hDK hs0 hs1 hb0 hb1 hBd hθ0 hθ1 hbox
  have hsc1 : Work.Peluse.dSup P Ns N + 1 ≤ C * Ns := by
    have h := hSc
    simp only [Work.Peluse.UlowerA.UnbalScale] at h
    exact h.1
  obtain ⟨β, hβ⟩ := hL B Ns N D f₀ f₁ θ hN hNs hsc1 hNNs hD hDK hs0 hs1 hb0 hb1 hBd hθ0 hθ1 hbox
  set γ : ℝ := cL * θ ^ pL * ((D : ℝ) / (Ns : ℝ)) ^ qL with hγdef
  have hγ0 : 0 < γ := by rw [hγdef]; positivity
  obtain ⟨ψ, hψblind, hψ⟩ :=
    hB B Ns N D f₀ f₁ θ γ β hN hNs hSc hNNs hD hDK hs0 hs1 hb0 hb1 hBd hθ0 hθ1 hbox hγ0 hβ
  -- the two scale facts relating `B` to `dSup` and to `D`
  have hdsup_le : dSup P Ns N ≤ B := le_trans (Nat.le_add_right _ _) hBd
  have hB1 : 1 ≤ B := by
    have h1' : 1 ≤ dSup P Ns N := by
      rw [dSup]
      exact le_trans hNs (Nat.le_add_right _ _)
    exact le_trans h1' hdsup_le
  have hDB : D ≤ B := by
    have h2sD : D ≤ 2 * σ * D := by
      have h1 : 1 ≤ 2 * σ := by
        have : 1 ≤ σ := hσ
        omega
      calc D = 1 * D := (one_mul D).symm
        _ ≤ (2 * σ) * D := Nat.mul_le_mul_right D h1
    exact le_trans h2sD (le_trans (Nat.le_add_left _ _) hBd)
  have hDleB : (D : ℝ) ≤ (B : ℝ) := by exact_mod_cast hDB
  have hf1 : ∀ x : ℤ, ‖dualFn N P f₀ f₁ x‖ ≤ 1 := dualFn_norm_le_one hN P f₀ f₁ hb0 hb1
  have hFsup : SupportIn (dualFn N P f₀ f₁) B :=
    (Tools.dualFn_supportIn (N := Ns) (M := N) hN P f₀ f₁ hs0 hs1 hNNs).mono hdsup_le
  -- convert the aggregate produced by `blindConvertK2` into the normalisation of `lemma75_control`
  have haggr : cB * (γ * ((D : ℝ) / (Ns : ℝ))) ^ KB ≤
      ((Fintype.piFinset (fun _ : Fin σ => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹ *
      ((Fintype.piFinset (fun _ : Fin σ => Finset.Icc (1 : ℤ) (D : ℤ))).card : ℝ)⁻¹ *
      ∑ u ∈ Fintype.piFinset (fun _ : Fin σ => Finset.Icc (1 : ℤ) (D : ℤ)),
        ∑ v ∈ Fintype.piFinset (fun _ : Fin σ => Finset.Icc (1 : ℤ) (D : ℤ)),
          ‖((B : ℂ))⁻¹ * ∑' x : ℤ,
            cubeTerm u v (dualFn N P f₀ f₁) x *
              Complex.exp (2 * Real.pi * Complex.I * (∑ i : Fin σ, ψ i u v) * (x : ℝ))‖ ^ 2 := by
    simpa only [arithIcc_one_eq D, Complex.ofReal_intCast, ← Complex.ofReal_sum] using hψ
  have hfinal := h75 B D (dualFn N P f₀ f₁) ψ hB1 hD hDleB hf1 hFsup hψblind
    (cB * (γ * ((D : ℝ) / (Ns : ℝ))) ^ KB) (by positivity) haggr
  have harith : c75 * (cB * (γ * ((D : ℝ) / (Ns : ℝ))) ^ KB) ^ K75 =
      c75 * cB ^ K75 * cL ^ (KB * K75) * θ ^ (pL * KB * K75) *
        ((D : ℝ) / (Ns : ℝ)) ^ (qL * (KB * K75) + KB * K75) := by
    rw [hγdef]
    simp only [mul_pow, pow_mul, mul_assoc, pow_add]
  rw [← harith]
  exact hfinal

end

end Work.Peluse.Ulower


namespace Work.Peluse.UlowerA

/-- **The single degree-lowering step with the unbalanced scale relation.**

`Work.Peluse.Ulower.steple_of` with the balanced hypothesis `Scaled Ns N P.natDegree` replaced by
`UnbalScale P C Ns N`; the constants of the step may depend on `C` (which is why `C` is quantified
before the existential `c`).  The proof is the proof of `steple_of` with the two chain pieces
replaced by their `A`-versions and the extra `.1` projection of the scale hypothesis. -/
theorem ssStepA {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree) (h1 : Work.Peluse.PeluseU2Inverse)
    (h2 : Work.Peluse.PeluseMajorArc P) :
    ∀ C : ℕ, 1 ≤ C → StepLeA P C (max 1 |(((P.leadingCoeff : ℤ)) : ℝ)|) :=
  Work.Peluse.Ulower.ssStepAux hd h1 h2

end Work.Peluse.UlowerA
