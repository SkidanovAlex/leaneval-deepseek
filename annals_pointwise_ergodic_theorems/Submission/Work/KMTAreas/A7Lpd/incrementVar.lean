import Mathlib
import Submission.Work.KMTAreas.A7.varEst_of_narrow_symbols_twoEndpoints
import Submission.Work.KMTAreas.A7.isLqMultiplierBound_of_mikhlin
import Submission.Work.KMTAreas.A7.lacunaryBumpExponent
import Submission.Work.KMTAreas.A7.lacunaryModulatedDiffs_mikhlin
import Submission.Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Lpd

open MeasureTheory Finset
open scoped ENNReal NNReal BigOperators
open Work.KMTAreas.A7
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier

noncomputable section

/-! ## The annulus symbol family -/

/-- `Ψ_{m₀,n} = η_{≤-(m₀+n+1)} - η_{≤-(m₀+n)}`, the symbol of the `n`-th increment of the dyadic
Ionescu--Wainger family. -/
def annSch (m₀ n : ℕ) : SchwartzMap ℝ ℂ :=
  etaCutSchwartz (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ))))
    - etaCutSchwartz (-((m₀ : ℤ) + ((n : ℕ) : ℤ)))

@[simp] lemma annSch_coe (m₀ n : ℕ) :
    (annSch m₀ n : ℝ → ℂ) = fun ξ : ℝ =>
      etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) ξ
        - etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) ξ := by
  funext ξ
  simp [annSch]

/-! ## Elementary bridges -/

/-- `η_{≤k}(ξ) = η(2^{-k} ξ)`. -/
lemma etaCut_kmtEta_eq (k : ℤ) (ξ : ℝ) :
    etaCut Work.KMTContract.kmtEta k ξ = Work.KMTContract.kmtEta ((2 : ℝ) ^ (-k) * ξ) := by
  rw [Work.Analysis.IonescuWainger.etaCut, div_eq_mul_inv, ← zpow_neg, mul_comm]

/-- `η_{≤-(j:ℤ)}(ξ) = η(2^j ξ)` for a natural `j`. -/
lemma etaCut_kmtEta_nat (j : ℕ) (ξ : ℝ) :
    etaCut Work.KMTContract.kmtEta (-(j : ℤ)) ξ = Work.KMTContract.kmtEta ((2 : ℝ) ^ j * ξ) := by
  rw [etaCut_kmtEta_eq, neg_neg, zpow_natCast]

lemma ee_zero : ee (0 : ℝ) = 1 := by simp [ee]

/-- The good-major-arcs condition is monotone in its constant. -/
lemma goodMajorArcs_mono {ρ C₁ C₂ : ℝ} {l : ℕ} {k : ℤ} (h : C₁ ≤ C₂)
    (hk : GoodMajorArcs ρ C₂ l k) : GoodMajorArcs ρ C₁ l k := by
  rw [Work.Analysis.IonescuWainger.GoodMajorArcs] at hk ⊢
  have h2 : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  nlinarith

/-- Monotonicity of `IsLqMultiplierBound` in the constant. -/
lemma isLqMultiplierBound_mono {q : ENNReal} {φ : ℝ → ℂ} {M M' : NNReal}
    (h : Work.Analysis.IWMultiplier.IsLqMultiplierBound q φ M) (hle : M ≤ M') :
    Work.Analysis.IWMultiplier.IsLqMultiplierBound q φ M' := by
  intro f
  refine le_trans (h f) ?_
  refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) zero_le
  exact_mod_cast hle

/-! ## The uniform Mikhlin bound for the signed sums of the annulus symbols -/

/-- **The signed sums of the annulus symbols satisfy the Mikhlin conditions**, with a constant
independent of the base level `m₀`, of the finite set `U` of scales, of the sign pattern `ω` and
of the number of scales.  The symbol is the *lacunary difference* of the cutoff
(`Work.KMTAreas.A7.lacunaryModulatedDiffs_mikhlin` with modulation `λ = 0`), and the coefficients
`1_{n ∈ U} ω n` are bounded by `1`. -/
lemma mikhlinBound_annulus :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (m₀ : ℕ) (U : Finset ℕ) (ω : ℕ → Bool),
      Work.KMTAreas.A7.MikhlinBound (fun ξ : ℝ => ∑ n ∈ U,
        (if ω n then (1 : ℂ) else -1) *
          (etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) ξ
            - etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) ξ)) A := by
  obtain ⟨Cc, hCc0, hCc⟩ :=
    Work.KMTAreas.A7.lacunaryModulatedDiffs_mikhlin (Lam := 2) (del := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (Φ := Work.KMTContract.kmtEta)
      (Work.KMTAreas.A7.contDiff_kmtEta 2)
      (fun u hu => Work.KMTContract.kmtEta_zero hu)
      (fun u hu => by
        rw [Work.KMTContract.kmtEta_one hu,
          Work.KMTContract.kmtEta_one (by norm_num : |(0 : ℝ)| ≤ 1 / 2)])
  refine ⟨Cc, hCc0, ?_⟩
  intro m₀ U ω
  have hσpos : ∀ n : ℕ, (0 : ℝ) < (2 : ℝ) ^ (m₀ + n) := fun n => by positivity
  have hσstep : ∀ n : ℕ, (2 : ℝ) ^ (m₀ + (n + 1)) ≥ 2 * (2 : ℝ) ^ (m₀ + n) := by
    intro n
    rw [show m₀ + (n + 1) = (m₀ + n) + 1 from by omega, pow_succ]
    exact le_of_eq (by ring)
  have heps : ∀ n : ℕ, ‖(if n ∈ U then (if ω n then (1 : ℂ) else -1) else 0)‖ ≤ 1 := by
    intro n
    by_cases hn : n ∈ U
    · rw [if_pos hn]
      by_cases hω : ω n <;> simp [hω]
    · rw [if_neg hn]; simp
  have hmain := hCc (cbar := (0 : ℝ)) (le_refl 0) (sigma := fun n => (2 : ℝ) ^ (m₀ + n))
    hσpos hσstep (lam := fun _ => (0 : ℝ)) (by intro n; simp) (by intro n; simp)
    (U.sup id + 1) (fun n => if n ∈ U then (if ω n then (1 : ℂ) else -1) else 0) heps
  rw [show Cc * (1 + 0) ^ 2 = Cc from by ring] at hmain
  simp only [zero_mul, ee_zero, mul_one] at hmain
  have hsub : U ⊆ Finset.range (U.sup id + 1) := fun n hn =>
    Finset.mem_range.mpr (lt_of_le_of_lt (Finset.le_sup (f := id) hn) (Nat.lt_succ_self _))
  have heq : (fun ξ : ℝ => ∑ n ∈ Finset.range (U.sup id + 1),
        (if n ∈ U then (if ω n then (1 : ℂ) else -1) else 0) *
          (Work.KMTContract.kmtEta ((2 : ℝ) ^ (m₀ + (n + 1)) * ξ)
            - Work.KMTContract.kmtEta ((2 : ℝ) ^ (m₀ + n) * ξ)))
      = (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) ξ
            - etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) ξ)) := by
    funext ξ
    rw [(Finset.sum_subset hsub (by
      intro x hx hxU
      rw [if_neg hxU, zero_mul])).symm]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    rw [if_pos hn]
    congr 1
    rw [← etaCut_kmtEta_nat (m₀ + (n + 1)) ξ, ← etaCut_kmtEta_nat (m₀ + n) ξ]
    push_cast
    ring
  rwa [heq] at hmain

/-! ## The signed sums as `L^q` multipliers -/

/-- **The signed sums of the annulus symbols are `L^q` Fourier multipliers** with a constant
independent of `m₀`, `U` and `ω`: this is `isLqMultiplierBound_of_mikhlin` applied to the uniform
Mikhlin bound `mikhlinBound_annulus`. -/
lemma isLqMultiplierBound_annulus (q : ℝ) (hq : 1 < q) :
    ∃ M : NNReal, 0 < M ∧ ∀ (m₀ : ℕ) (U : Finset ℕ) (ω : ℕ → Bool),
      Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal q)
        (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (annSch m₀ n : ℝ → ℂ) ξ) M := by
  obtain ⟨A, hA0, hA⟩ := mikhlinBound_annulus
  obtain ⟨Cq, hCqpos, hCqm⟩ := Work.KMTAreas.A7.isLqMultiplierBound_of_mikhlin q hq
  refine ⟨max (Real.toNNReal (Cq * A)) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro m₀ U ω
  have hsym : (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
        (annSch m₀ n : ℝ → ℂ) ξ)
      = (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) *
          (etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) ξ
            - etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) ξ)) := by
    funext ξ
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [annSch_coe]
  have hmikh : Work.KMTAreas.A7.MikhlinBound (fun ξ : ℝ => ∑ n ∈ U,
      (if ω n then (1 : ℂ) else -1) *
        (etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) ξ
          - etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) ξ)) A := by
    have h := hA m₀ U ω
    rwa [← hsym] at h
  have hcd_eta : ∀ k : ℤ, ContDiff ℝ 2 (etaCut Work.KMTContract.kmtEta k) := by
    intro k
    have h1 : ContDiff ℝ 2 (fun ξ : ℝ => ξ / (2 : ℝ) ^ k) := by fun_prop
    have h2 : ContDiff ℝ 2 Work.KMTContract.kmtEta := Work.KMTAreas.A7.contDiff_kmtEta 2
    have h3 : ContDiff ℝ 2 (etaCut Work.KMTContract.kmtEta k) := h2.comp h1
    exact h3
  have hcd : ContDiff ℝ 2 (fun ξ : ℝ => ∑ n ∈ U,
      (if ω n then (1 : ℂ) else -1) *
        (etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) ξ
          - etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) ξ)) := by
    refine ContDiff.sum (fun n _ => ?_)
    exact contDiff_const.mul ((hcd_eta _).sub (hcd_eta _))
  have hb := (hCqm hcd hmikh).1
  rw [← hsym] at hb
  exact isLqMultiplierBound_mono hb (le_max_left _ _)

/-! ## The increments of the dyadic Ionescu--Wainger family, for bounded input -/

/-- For **bounded** input the projection with the annulus symbol
`Ψ_{m₀,n} = η_{≤-(m₀+n+1)} - η_{≤-(m₀+n)}` is the difference of the two IW projections.  This is
the linearity of `iwConv` in the symbol (`Work.KMTAreas.A7.iwConv_sub_of_bounded`) applied to the
periodisation identity `Work.KMTAreas.A7.periodize_sub_etaCut`, together with the `ℓ¹`-ness of the
kernels (`Work.KMTAreas.A7.summable_iwKernel_etaCut`). -/
lemma Tle_annSch_eq (ρ : ℝ) (l m₀ n : ℕ) (f : ℤ → ℂ) {B : ℝ}
    (hB : ∀ m : ℤ, ‖f m‖ ≤ B) :
    Tle ρ l (annSch m₀ n : ℝ → ℂ) f
      = fun x : ℤ => Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
          - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x := by
  have hInt1 : Integrable (iwSymbolSet (iwArithFreqs ρ l)
      (periodize (etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))))))
      circleMeasure := by
    have h := Work.KMTAreas.integrable_iwSymbolSet_periodize (iwArithFreqs ρ l)
      (etaCutSchwartz (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))))
    simpa only [etaCutSchwartz_coe] using h
  have hInt2 : Integrable (iwSymbolSet (iwArithFreqs ρ l)
      (periodize (etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + ((n : ℕ) : ℤ))))))
      circleMeasure := by
    have h := Work.KMTAreas.integrable_iwSymbolSet_periodize (iwArithFreqs ρ l)
      (etaCutSchwartz (-((m₀ : ℤ) + ((n : ℕ) : ℤ))))
    simpa only [etaCutSchwartz_coe] using h
  have hmain := Work.KMTAreas.A7.iwConv_sub_of_bounded (A := iwArithFreqs ρ l)
    (Φ := periodize (etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ))))))
    (Ψ := periodize (etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + ((n : ℕ) : ℤ)))))
    (f := f) hB hInt1 hInt2
    (Work.KMTAreas.A7.summable_iwKernel_etaCut ρ l _)
    (Work.KMTAreas.A7.summable_iwKernel_etaCut ρ l _)
  have hgoal : Tle ρ l (annSch m₀ n : ℝ → ℂ) f
      = iwConv (iwArithFreqs ρ l)
          (periodize (etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))))
            - periodize (etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + ((n : ℕ) : ℤ))))) f := by
    rw [Tle, annSch_coe, Work.KMTAreas.A7.periodize_sub_etaCut]
  rw [hgoal, hmain]
  rfl

/-
# Variational estimate for the increments of the dyadic Ionescu--Wainger family

For `0 < ρ ≤ 1`, `2 < r`, `1 < p < ∞` there are `Cρ > 0` and `C > 0` such that for all `l`, `m₀`
with `GoodMajorArcs ρ Cρ l (-(m₀))` and all `f : ℤ → ℂ`,

  `‖ V^r_k ( kmtProj ρ l (-(m₀+k+1)) f − kmtProj ρ l (-(m₀+k)) f ) ‖_{ℓᵖ(ℤ)} ≤ C (1+l) ‖f‖_{ℓᵖ}`,

uniformly in `m₀` and `l`.

ROUTE. The increment is the Ionescu--Wainger projection `Tle ρ l (Ψ_k)` of the annulus symbol
`Ψ_k = etaCut kmtEta (-(m₀+k+1)) - etaCut kmtEta (-(m₀+k))`, i.e.
`Ψ_k(ξ) = η(ξ·2^{m₀+k+1}) - η(ξ·2^{m₀+k}) = φ(2^{m₀+k}ξ)` for the fixed annulus bump
`φ(u) = η(2u) - η(u)` (supported in `1/2 ≤ |u| ≤ 1`).  The symbols `Ψ_k` have disjointly supported
lacunary (ratio 2) annuli, so every signed sum `Σ_{k∈U} ω_k Ψ_k` satisfies the Mikhlin conditions
with a constant independent of `U`, `ω`, `l`, `m₀` (proved here as `mikhlinBound_annulus`, via
`Work.KMTAreas.A7.lacunaryModulatedDiffs_mikhlin`), whence
`IsLqMultiplierBound q` for `q ∈ {2, 2k₀}`; the separate lemma `Work.KMTAreas.A7Lpd.mikhlinAnnulus`
states the same bound in its original shape.  `Work.KMTAreas.A7.varEst_of_narrow_symbols_twoEndpoints`
applied with `k := -(m₀)`, `Φ := annSch m₀` and `M` the uniform multiplier constant then delivers
the inequality (its narrowness hypothesis holds because `realArc (-(m₀+k+1)) ⊆ realArc (-(m₀))`).
The identification of `Tle ρ l (annSch m₀ k) f` with the difference of the two projections is
`Tle_annSch_eq`.

BOOKKEEPING. The master result needs `2^k < 1/2` at `k = -(m₀)`, i.e. `m₀ ≥ 2`; enlarging `Cρ` to
`max Cρ 2` makes the finitely many levels `m₀ ≤ 1` vacuous.
-/
theorem incrementVar (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (l : ℕ) (m₀ : ℕ) (f : ℤ → ℂ),
        Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun k : ℕ => Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((k + 1 : ℕ) : ℤ)))) f x
              - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((k : ℕ) : ℤ))) f x)) p
          MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (C * (1 + (l : ℝ))) *
            MeasureTheory.eLpNorm f p MeasureTheory.Measure.count := by
  -- ## the endpoint exponent `k₀ ≥ 2` covering `p` and its Hölder dual
  have hq1 : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top (ne_of_lt hptop)).mpr hp
  obtain ⟨k₀, hk₀, hpk, hpk'⟩ := Work.KMTAreas.A7.exists_endpoint_exponent p.toReal hq1
  -- ## the narrow-symbol variational estimate
  obtain ⟨Cρv, hCρvp, Kv, hKvp, hvar⟩ :=
    Work.KMTAreas.A7.varEst_of_narrow_symbols_twoEndpoints ρ hρ hρ1 r hr p hp hptop k₀ hk₀
      hpk hpk'
  -- ## the two multiplier endpoints
  have h2k : (1 : ℝ) < 2 * (k₀ : ℝ) := by
    have h2 : (2 : ℝ) ≤ (k₀ : ℝ) := by exact_mod_cast hk₀
    linarith
  obtain ⟨M2, hM2pos, hM2⟩ := isLqMultiplierBound_annulus 2 (by norm_num)
  obtain ⟨Mk, hMkpos, hMk⟩ := isLqMultiplierBound_annulus (2 * (k₀ : ℝ)) h2k
  have hMpos : (0 : NNReal) < max M2 Mk := lt_of_lt_of_le hM2pos (le_max_left M2 Mk)
  have hCpos : (0 : ℝ) < Kv * ((max M2 Mk : NNReal) : ℝ) := by
    refine mul_pos hKvp ?_
    exact_mod_cast hMpos
  refine ⟨max Cρv 2, lt_max_of_lt_right (by norm_num : (0 : ℝ) < 2),
    Kv * ((max M2 Mk : NNReal) : ℝ), hCpos, ?_⟩
  intro l m₀ f hgood
  -- ## the good-arc hypothesis at the variational estimate's constant
  have hgoodv : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρv l (-(m₀ : ℤ)) :=
    goodMajorArcs_mono (le_max_left Cρv (2 : ℝ)) hgood
  -- ## `Cρ ≥ 2` forces `m₀ ≥ 2`
  have hm02 : 2 ≤ m₀ := by
    have h := hgood
    rw [Work.Analysis.IonescuWainger.GoodMajorArcs] at h
    have h' : -(m₀ : ℝ) ≤ -max Cρv 2 * (2 : ℝ) ^ (ρ * (l : ℝ)) := by simpa using h
    have h2 : (2 : ℝ) ≤ max Cρv 2 := le_max_right Cρv (2 : ℝ)
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (ρ * (l : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have hge1 : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hle : -(m₀ : ℝ) ≤ -2 := by nlinarith [h', h2, hpos, hge1]
    have h2' : (2 : ℝ) ≤ (m₀ : ℝ) := by linarith
    exact_mod_cast h2'
  have hk : (2 : ℝ) ^ (-(m₀ : ℤ)) < 1 / 2 := by
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ m₀ := by
      calc (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        _ ≤ (2 : ℝ) ^ m₀ := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hm02
    rw [zpow_neg, zpow_natCast, inv_eq_one_div]
    have hle : 1 / (2 : ℝ) ^ m₀ ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) h4
    linarith
  -- ## narrowness of the annulus family
  have hnarrow : ∀ n ξ, (annSch m₀ n : ℝ → ℂ) ξ ≠ 0 →
      ξ ∈ Work.Analysis.IonescuWainger.realArc (-(m₀ : ℤ)) := by
    intro n ξ hξ
    simp only [annSch_coe] at hξ
    have hcases : etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) ξ ≠ 0 ∨
        etaCut Work.KMTContract.kmtEta (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) ξ ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hξ (by rw [hcon.1, hcon.2]; ring)
    rcases hcases with h1 | h2
    · exact realArc_mono (by omega) (etaCut_ne_zero_mem_realArc _ h1)
    · exact realArc_mono (by omega) (etaCut_ne_zero_mem_realArc _ h2)
  -- ## the multiplier hypothesis
  have hMult : ∀ (U : Finset ℕ) (ω : ℕ → Bool),
      Work.Analysis.IWMultiplier.IsLqMultiplierBound 2
        (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (annSch m₀ n : ℝ → ℂ) ξ)
          (max M2 Mk) ∧
      Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal (2 * (k₀ : ℝ)))
        (fun ξ : ℝ => ∑ n ∈ U, (if ω n then (1 : ℂ) else -1) * (annSch m₀ n : ℝ → ℂ) ξ)
          (max M2 Mk) := by
    intro U ω
    refine ⟨?_, isLqMultiplierBound_mono (hMk m₀ U ω) (le_max_right M2 Mk)⟩
    have h := isLqMultiplierBound_mono (hM2 m₀ U ω) (le_max_left M2 Mk)
    simpa only [show ENNReal.ofReal (2 : ℝ) = (2 : ENNReal) from by norm_num] using h
  -- ## the two cases (finitely many scales / bounded input)
  by_cases hftop : MeasureTheory.eLpNorm f p MeasureTheory.Measure.count = ⊤
  · have hR : ENNReal.ofReal (Kv * ((max M2 Mk : NNReal) : ℝ) * (1 + (l : ℝ))) *
        MeasureTheory.eLpNorm f p MeasureTheory.Measure.count = ⊤ := by
      rw [hftop]
      exact ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hCpos (by positivity)))
    rw [hR]
    exact le_top
  · obtain ⟨B, hB⟩ := Work.KMTAreas.A7.bounded_of_eLpNorm_count_lt_top (p := p)
      (ne_of_gt (lt_trans zero_lt_one hp)) (lt_top_iff_ne_top.mpr hftop)
    have hfam : ∀ n : ℕ, Tle ρ l (annSch m₀ n : ℝ → ℂ) f =
        fun x : ℤ => Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
          - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x :=
      fun n => Tle_annSch_eq ρ l m₀ n f hB
    have hfun : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun k : ℕ => Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((k + 1 : ℕ) : ℤ)))) f x
            - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((k : ℕ) : ℤ))) f x))
        = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => Tle ρ l (annSch m₀ n : ℝ → ℂ) f x)) := by
      funext x
      congr 1
      funext k
      exact (congrFun (hfam k) x).symm
    rw [hfun]
    refine (hvar l (-(m₀ : ℤ)) hgoodv hk (max M2 Mk) hMpos (annSch m₀) hnarrow hMult f).trans ?_
    refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_of_eq ?_)) zero_le
    ring

/-! ## The target -/


end

end Work.KMTAreas.A7Lpd
