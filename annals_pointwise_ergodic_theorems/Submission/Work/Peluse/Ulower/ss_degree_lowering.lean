import Mathlib
import Submission.Work.Peluse.Ulower.lemma74_doubling
import Submission.Work.Peluse.Pairing.boxSumPow_neg_directions
import Submission.Work.Peluse.Ulower.StepLe.levelTwoExtract
import Submission.Work.Peluse.Ulower.ss75.lemma75GCS
import Submission.Work.Peluse.Ulower.StepLe.blindConvertK2
import Submission.Work.Peluse.Ulower.finalTarget

namespace Work.Peluse.Ulower

open Work.Peluse

/-- **The single degree-lowering step** (Peluse's Lemma 3.9, one step, dense normalisation),
assembled from three chapters:

* `StepLe.levelTwoExtract` (PROVED sorry-free: the peel + Markov + `U²`-inverse extraction of the
  chirped cube-term aggregate at phases `β`, with a quantitative lower bound
  `cL * θ^pL * (D/Ns)^qL`);
* `StepLe.blindConvertK2` (the middle step, with the `(D/Ns)`-loss of Peluse's §§7-8 route: Lemma 7.4
  + the major-arc hypothesis `h2` + the pigeonhole/coboundary construction produce a **blind**
  family `ψ` whose aggregate is at least `cB (γ D/Ns)^KB`);
* `ss75.lemma75GCS` (Peluse's Lemma 7.5: a large aggregate at a blind phase forces the
  level-`(σ+1)` box norm of the dual function up).

The assembly is pure bookkeeping (the same recipe as `Work.Peluse.Ulower.steple_of`); the `(D/Ns)`
losses only raise the exponents of the conclusion. -/
theorem steple_of_ss {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree) (h1 : PeluseU2Inverse)
    (h2 : PeluseMajorArc P) :
    StepLe P (max 1 |(((P.leadingCoeff : ℤ)) : ℝ)|) := by
  intro t ht
  obtain ⟨σ, rfl⟩ : ∃ σ, t = σ + 2 := ⟨t - 2, by omega⟩
  have hσ : 1 ≤ σ := by omega
  set K₀ : ℝ := max 1 |(((P.leadingCoeff : ℤ)) : ℝ)| with hK₀def
  have hK₀1 : 1 ≤ K₀ := le_max_left _ _
  obtain ⟨cL, hcL, pL, qL, hpL, hqL, hL⟩ := StepLe.levelTwoExtract hd h1 K₀ hK₀1 σ hσ
  obtain ⟨cB, hcB, KB, hKB, hB⟩ := StepLe.blindConvertK2 hd h2 K₀ hK₀1 σ hσ
  obtain ⟨K75, hK75, c75, hc75, h75⟩ := ss75.lemma75GCS σ hσ
  have hpL0 : 0 < pL := by omega
  have hqL0 : 0 < qL := by omega
  have hKB0 : 0 < KB := by omega
  have hK750 : 0 < K75 := by omega
  refine ⟨pL * KB * K75, (qL + 1) * KB * K75, ?_, ?_,
    c75 * cB ^ K75 * cL ^ (KB * K75), by positivity, ?_⟩
  · have h : 0 < pL * KB * K75 := by positivity
    omega
  · have h : 0 < (qL + 1) * KB * K75 := by positivity
    omega
  intro B Ns N D f₀ f₁ θ hd' hN hNs hSc hNNs hD hDK hs0 hs1 hb0 hb1 hBd hθ0 hθ1 hbox
  obtain ⟨β, hβ⟩ := hL B Ns N D f₀ f₁ θ hN hNs hSc hNNs hD hDK hs0 hs1 hb0 hb1 hBd hθ0 hθ1 hbox
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
  -- convert the aggregate produced by the middle step into the normalisation of `ss75`
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
        ((D : ℝ) / (Ns : ℝ)) ^ ((qL + 1) * KB * K75) := by
    rw [hγdef]
    simp only [mul_pow, pow_mul]
    ring_nf
  rw [← harith]
  exact hfinal

theorem ss_degree_lowering {P : Polynomial ℤ} (hd : 2 ≤ P.natDegree)
    (h1 : Work.Peluse.PeluseU2Inverse) (h2 : Work.Peluse.PeluseMajorArc P) :
    ∀ s : ℕ, 2 ≤ s → ∃ K : ℕ, 1 ≤ K ∧
      ∀ (Ns N D : ℕ) (f₀ f₁ : ℤ → ℂ) (δ : ℝ),
        2 ≤ P.natDegree → 1 ≤ N → 1 ≤ Ns → Work.Peluse.Scaled Ns N P.natDegree → N ≤ Ns →
        1 ≤ D → (D : ℝ) ≤ (Ns : ℝ) →
        Work.Peluse.SupportIn f₀ Ns → Work.Peluse.SupportIn f₁ Ns →
        (∀ x : ℤ, ‖f₀ x‖ ≤ 1) → (∀ x : ℤ, ‖f₁ x‖ ≤ 1) →
        0 < δ → δ ≤ 1 →
        δ ≤ Work.Peluse.uNormPow s (Work.Peluse.arithIcc P.leadingCoeff D)
          (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)) (Work.Peluse.dualFn N P f₀ f₁) →
        (δ * ((D : ℝ) / (Ns : ℝ))) ^ K ≤
          Work.Peluse.uNormPow 2 (Work.Peluse.arithIcc P.leadingCoeff D)
            (Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)) (Work.Peluse.dualFn N P f₀ f₁) :=
  degree_lowering_v2_of_step hd (steple_of_ss hd h1 h2)

end Work.Peluse.Ulower
