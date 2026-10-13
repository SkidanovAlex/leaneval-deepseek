import Mathlib
import Submission.Work.DSM5c.Lp.chartDToLp_exists
import Submission.Work.DSM5c.Lp.chartCmpRingHom_eq_zero_iff
import Submission.Work.DSM5c.Lp.ChartLpR

/-!
# DSM5c/Lp — the coefficient comparison `D_S ⧸ (p) → R_S ⧸ (φ_S(ϖ♭)^p)`

The mod-`p` comparison `Work.DSM5c.Lp.chartCmpRingHom` (the `0`-th Witt coordinate) has kernel
`(p) · ⊤` and is surjective; it therefore descends to a `W`-linear map

  `chartCmpMap S : D_S ⧸ (p)·⊤ → R_S ⧸ (φ_S(ϖ♭)^p)`.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.DSM5c.Lp

universe a

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

variable {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W] [Fact ¬IsUnit (p : W)]
  [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type a} [DecidableEq ι]

/-- **`chartCmpRingHom` kills the image of `p`.** -/
theorem chartCmpRingHom_algebraMap_p (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) :
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
    chartCmpRingHom Q hθ t tr htr0 htr j₀ e S
      (algebraMap W (untiltOf (tiltChart Q t tr htr0 htr j₀ e S)
        (chartPhi Q t tr htr0 htr j₀ e S)) (p : W)) = 0 := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
  have h1 : WittVector.fontaineTheta (p := p) (R := W)
      (p : WittVector p (PreTilt W p)) = (p : W) := map_natCast _ _
  have h2 : WittVector.map (chartPhi Q t tr htr0 htr j₀ e S)
      (p : WittVector p (PreTilt W p)) =
        (p : WittVector p (tiltChart Q t tr htr0 htr j₀ e S)) := map_natCast _ _
  have hmkp : algebraMap W (untiltOf (tiltChart Q t tr htr0 htr j₀ e S)
      (chartPhi Q t tr htr0 htr j₀ e S)) (p : W) =
      Ideal.Quotient.mk (chartUntiltIdeal Q hθ t tr htr0 htr j₀ e S)
        (p : WittVector p (tiltChart Q t tr htr0 htr j₀ e S)) := by
    change untiltOf.algebraMap hθ (chartPhi Q t tr htr0 htr j₀ e S) (p : W) =
      untiltOf.mk (p := p) (W := W) (chartPhi Q t tr htr0 htr j₀ e S)
        (p : WittVector p (tiltChart Q t tr htr0 htr j₀ e S))
    rw [← h2, ← h1]
    exact untiltOf.algebraMap_fontaineTheta (p := p) (W := W) hθ
      (chartPhi Q t tr htr0 htr j₀ e S) (p : WittVector p (PreTilt W p))
  rw [hmkp, chartCmpRingHom_mk, WittVector.constantCoeff, map_natCast,
    chart_p_eq_zero Q t tr htr0 htr j₀ e S]
  exact map_zero _

/-- The submodule `(p) · ⊤` is contained in the kernel of the comparison. -/
theorem chartDpTop_le_ker (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) :
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
    letI := chartLAlg Q t tr htr0 htr j₀ e S
    chartDpTop Q hθ t tr htr0 htr j₀ e S ≤
      LinearMap.ker (chartCmpLinear Q hθ t tr htr0 htr j₀ e S) := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
  letI := chartLAlg Q t tr htr0 htr j₀ e S
  intro x hx
  rw [LinearMap.mem_ker]
  rw [mem_span_singleton_smul_top_iff (p : W) x] at hx
  rw [mem_span_singleton_iff] at hx
  obtain ⟨y, hy⟩ := hx
  have hp0 : chartCmpRingHom Q hθ t tr htr0 htr j₀ e S
      (algebraMap W (untiltOf (tiltChart Q t tr htr0 htr j₀ e S)
        (chartPhi Q t tr htr0 htr j₀ e S)) (p : W)) = 0 :=
    chartCmpRingHom_algebraMap_p Q hθ t tr htr0 htr j₀ e S
  rw [← hy]
  show chartCmpRingHom Q hθ t tr htr0 htr j₀ e S
    (algebraMap W (untiltOf (tiltChart Q t tr htr0 htr j₀ e S)
      (chartPhi Q t tr htr0 htr j₀ e S)) (p : W) * y) = 0
  rw [map_mul, hp0, zero_mul]

/-- **The coefficient comparison `D_S ⧸ (p)·⊤ → R_S ⧸ (φ_S(ϖ♭)^p)`.** -/
noncomputable def chartCmpMap (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) :
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
    letI := chartLAlg Q t tr htr0 htr j₀ e S
    (untiltOf (tiltChart Q t tr htr0 htr j₀ e S)
        (chartPhi Q t tr htr0 htr j₀ e S) ⧸ chartDpTop Q hθ t tr htr0 htr j₀ e S) →ₗ[W]
      (tiltChart Q t tr htr0 htr j₀ e S ⧸ chartLIdeal Q t tr htr0 htr j₀ e S) := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
  letI := chartLAlg Q t tr htr0 htr j₀ e S
  exact (chartDpTop Q hθ t tr htr0 htr j₀ e S).liftQ
    (chartCmpLinear Q hθ t tr htr0 htr j₀ e S)
    (chartDpTop_le_ker Q hθ t tr htr0 htr j₀ e S)

/-- The defining property of the coefficient comparison on classes. -/
theorem chartCmpMap_mk (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι)
    (d : untiltOf (tiltChart Q t tr htr0 htr j₀ e S) (chartPhi Q t tr htr0 htr j₀ e S)) :
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
    letI := chartLAlg Q t tr htr0 htr j₀ e S
    chartCmpMap Q hθ t tr htr0 htr j₀ e S (Submodule.Quotient.mk d) =
      chartCmpRingHom Q hθ t tr htr0 htr j₀ e S d := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
  letI := chartLAlg Q t tr htr0 htr j₀ e S
  show ((chartDpTop Q hθ t tr htr0 htr j₀ e S).liftQ
    (chartCmpLinear Q hθ t tr htr0 htr j₀ e S)
    (chartDpTop_le_ker Q hθ t tr htr0 htr j₀ e S))
    (Submodule.Quotient.mk d) = chartCmpRingHom Q hθ t tr htr0 htr j₀ e S d
  rw [Submodule.liftQ_apply]
  rfl

/-- **Naturality of the comparison with respect to the chart restrictions.** -/
theorem chartCmpRingHom_naturality (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) {S T : Finset ι} (h : S ⊆ T)
    (d : untiltOf (tiltChart Q t tr htr0 htr j₀ e S) (chartPhi Q t tr htr0 htr j₀ e S)) :
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e T
    chartLMap Q t tr htr0 htr j₀ e h
        (chartCmpRingHom Q hθ t tr htr0 htr j₀ e S d) =
      chartCmpRingHom Q hθ t tr htr0 htr j₀ e T
        (chartDMap Q hθ t tr htr0 htr j₀ e h d) := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e T
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective
    (I := chartUntiltIdeal Q hθ t tr htr0 htr j₀ e S) d
  have hdm : chartDMap Q hθ t tr htr0 htr j₀ e h
      (Ideal.Quotient.mk (chartUntiltIdeal Q hθ t tr htr0 htr j₀ e S) y) =
      Ideal.Quotient.mk (chartUntiltIdeal Q hθ t tr htr0 htr j₀ e T)
        (WittVector.map (tiltChartRes Q t tr htr0 htr j₀ e h) y) := by
    show untiltOf.map (chartPhi Q t tr htr0 htr j₀ e S) (chartPhi Q t tr htr0 htr j₀ e T)
      (tiltChartRes Q t tr htr0 htr j₀ e h)
      (RingHom.ext fun r => tiltChartRes_algebraMap Q t tr htr0 htr j₀ e h r)
      (untiltOf.mk (p := p) (W := W) (chartPhi Q t tr htr0 htr j₀ e S) y) = _
    rw [untiltOf.map_apply]
    rfl
  rw [hdm, chartCmpRingHom_mk, chartLMap_mk, chartCmpRingHom_mk,
    wittVector_constantCoeff_map]

/-- The comparison is surjective (it is `chartCmpLinear` modulo `(p) · ⊤`). -/
theorem chartCmpMap_surjective (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) :
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
    letI := chartLAlg Q t tr htr0 htr j₀ e S
    Function.Surjective (chartCmpMap Q hθ t tr htr0 htr j₀ e S) := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
  letI := chartLAlg Q t tr htr0 htr j₀ e S
  intro y
  obtain ⟨d, hd⟩ := chartCmpLinear_surjective Q hθ t tr htr0 htr j₀ e S y
  exact ⟨Submodule.Quotient.mk d, by rw [chartCmpMap_mk]; exact hd⟩

/-- The comparison is injective. -/
theorem chartCmpMap_injective (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) :
    letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
    letI := chartLAlg Q t tr htr0 htr j₀ e S
    Function.Injective (chartCmpMap Q hθ t tr htr0 htr j₀ e S) := by
  letI := chartDAlg Q hθ t tr htr0 htr j₀ e S
  letI := chartLAlg Q t tr htr0 htr j₀ e S
  intro a b hab
  obtain ⟨d, rfl⟩ := Submodule.Quotient.mk_surjective (chartDpTop Q hθ t tr htr0 htr j₀ e S) a
  obtain ⟨d', rfl⟩ := Submodule.Quotient.mk_surjective (chartDpTop Q hθ t tr htr0 htr j₀ e S) b
  rw [chartCmpMap_mk, chartCmpMap_mk] at hab
  rw [Submodule.Quotient.eq]
  by_cases hsub : Subsingleton (tiltChart Q t tr htr0 htr j₀ e S)
  · haveI : Subsingleton (WittVector p (tiltChart Q t tr htr0 htr j₀ e S)) :=
      ⟨fun x y => WittVector.ext fun n => Subsingleton.elim _ _⟩
    haveI hD : Subsingleton (untiltOf (tiltChart Q t tr htr0 htr j₀ e S)
        (chartPhi Q t tr htr0 htr j₀ e S)) :=
      ⟨fun x y => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [Subsingleton.elim a b]⟩
    have hdd : d - d' = 0 := Subsingleton.elim _ _
    rw [hdd]
    exact Submodule.zero_mem _
  · haveI : CharP (tiltChart Q t tr htr0 htr j₀ e S) p := by
      have hdvd : ringChar (tiltChart Q t tr htr0 htr j₀ e S) ∣ p :=
        ringChar.dvd (chart_p_eq_zero Q t tr htr0 htr j₀ e S)
      rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd with h1 | hp
      · exact absurd (ringChar.ringChar_eq_one.mp h1) hsub
      · exact ringChar.of_eq hp
    haveI : PerfectRing (tiltChart Q t tr htr0 htr j₀ e S) p :=
      Work.DSM5c.Charts.perfChartRing_perfect p (chartTiltGen Q t tr htr0 htr j₀ e) S
    have h1 : chartCmpRingHom Q hθ t tr htr0 htr j₀ e S (d - d') = 0 := by
      rw [map_sub, hab, sub_self]
    rw [chartCmpRingHom_eq_zero_iff Q hθ t tr htr0 htr j₀ e S] at h1
    exact h1

end Work.DSM5c.Lp
