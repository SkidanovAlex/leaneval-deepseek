/-
# The `ℓ^q` bounds for the Ionescu--Wainger projections (paper Lemma `iw-prop`(i))

This file assembles the boundedness half of Lemma `iw-prop` of Krause--Mirek--Tao for the
concrete Ionescu--Wainger projections `kmtProj ρ l k = Π_{≤l,≤k}` of the KMT contract:

`GoodMajorArcs ρ Cρ l k → ‖kmtProj ρ l k f‖_{ℓ^q} ≤ C_{ρ,q} ⟨l⟩ ‖f‖_{ℓ^q}`  (`1 < q < ∞`).

The input is *only* area `A1`, i.e. the Ionescu--Wainger multiplier theorem at the even exponents
(`IWMultiplierBoundStatement_even`) together with its proved consequences:

* the `q = 2` case (`IWMultiplierBound_q2_vector`, proved),
* Riesz--Thorin interpolation (`IWLqBound_interpolation`, proved) for the exponents `q ≥ 2`,
* duality (`IWLqBound_of_dual`, proved) for the exponents `1 < q < 2`, using that the KMT
  symbol `periodize (etaCut kmtEta k)` is real-valued (`star_periodize_etaCut`),
* the crude multiplier bound for the rescaled cutoffs (`A7/EtaMult.lean`, supplied here as the
  hypothesis `hMbound`).

The intermediate statement for the exponents `q ≥ 2` is isolated as `GeTwoBounds`; it is proved in
`A7/EtaProjGeTwo.lean`.  The last section extends the (finitely supported) `IWLqBound` to all
functions in `ℓ^p`, by Fatou along the truncations `truncZ K f`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Basic
import Submission.Work.KMTContract.kmtKernel_decay
import Submission.Work.KMTContract.kmtProj_tendsto_truncZ
import Submission.Commons.Analysis.Hilbert.discrete_hilbert_transform_lp
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7

open MeasureTheory Filter
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-- **The `q ≥ 2` half of the projection bounds**, in the shape produced from area `A1` by
`EtaProjGeTwo`: for every exponent `q ≥ 2` and every `ρ ∈ (0,1]` there is `Cρ` (the constant of
the non-aliasing/good-major-arcs statement of `A1`) and a constant `C` such that the IW projection
symbol is an `ℓ^q` multiplier with constant `C ⟨l⟩` on good major arcs. -/
def GeTwoBounds : Prop :=
  ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (q : ENNReal), 2 ≤ q → q ≠ ⊤ →
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k →
        IWLqBound (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k)) q
          (C * angleBracket l)

/-- **The exponents `1 < q < 2`, by duality.**  The bound at `q` follows from the bound at the
Hölder dual exponent `q' = q/(q-1) > 2` by `IWLqBound_of_dual`, because the KMT symbol is
real-valued, so that the conjugate symbol is the symbol itself. -/
theorem iwLqBound_etaCut_ofreal_lt_two (hG : GeTwoBounds) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {p : ℝ} (hp1 : 1 < p) (hp2 : p < 2) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k →
        IWLqBound (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))
          (ENNReal.ofReal p) (C * angleBracket l) := by
  set p' : ℝ := p / (p - 1) with hp'def
  have hp1pos : (0 : ℝ) < p - 1 := by linarith
  have hp'2 : 2 ≤ p' := by
    rw [hp'def, le_div_iff₀ hp1pos]; linarith
  have hp'pos : 0 < p' := lt_of_lt_of_le (by norm_num) hp'2
  obtain ⟨Cρ, hCρ, C, hC, hbnd⟩ :=
    hG ρ hρ hρ1 (ENNReal.ofReal p')
      (by rw [← ENNReal.ofReal_ofNat]; exact ENNReal.ofReal_le_ofReal hp'2)
      ENNReal.ofReal_ne_top
  refine ⟨Cρ, hCρ, C, hC, fun l k hgood => ?_⟩
  have hb := hbnd l k hgood
  have hdual := IWLqBound_of_dual (iwArithFreqs ρ l)
    (periodize (etaCut Work.KMTContract.kmtEta k)) hb
    (by rw [ENNReal.toReal_ofReal hp'pos.le]; linarith)
  have hsym : (fun ξ => star (periodize (etaCut Work.KMTContract.kmtEta k) ξ))
      = periodize (etaCut Work.KMTContract.kmtEta k) := by
    funext ξ
    exact star_periodize_etaCut k ξ
  have hexp : ENNReal.ofReal
        ((ENNReal.ofReal p').toReal / ((ENNReal.ofReal p').toReal - 1))
      = ENNReal.ofReal p := by
    rw [ENNReal.toReal_ofReal hp'pos.le, hp'def]
    congr 1
    field_simp
    ring
  rwa [hsym, hexp] at hdual

/-- **The `ℓ^q` bound for the KMT projection symbol at every real exponent `p > 1`**, on good
major arcs, from the `q ≥ 2` bounds. -/
theorem iwLqBound_etaCut_ofreal (hG : GeTwoBounds) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    {p : ℝ} (hp1 : 1 < p) :
    ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ Cρ l k →
        IWLqBound (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))
          (ENNReal.ofReal p) (C * angleBracket l) := by
  rcases le_or_gt 2 p with hp | hp
  · obtain ⟨Cρ, hCρ, C, hC, hbnd⟩ :=
      hG ρ hρ hρ1 (ENNReal.ofReal p)
        (by rw [← ENNReal.ofReal_ofNat]; exact ENNReal.ofReal_le_ofReal hp)
        ENNReal.ofReal_ne_top
    exact ⟨Cρ, hCρ, C, hC, hbnd⟩
  · exact iwLqBound_etaCut_ofreal_lt_two hG hρ hρ1 hp1 hp

/-! ## From finitely supported to all `ℓ^p` functions -/

/-- A finitely supported sequence has finite support. -/
theorem finite_support_of_finSupp {f : ℤ → ℂ} (h : Work.Analysis.InverseTheory.FinSupp f) :
    (Function.support f).Finite := by
  obtain ⟨s, hs⟩ := h
  exact s.finite_toSet.subset (fun x hx => by
    by_contra hxs
    exact hx (hs x hxs))

/-- **Extension of the `IWLqBound` to all of `ℓ^p`.**  Since the truncations `truncZ K f` are
finitely supported and converge pointwise to `f`, Fatou's lemma
(`Commons.Analysis.Hilbert.eLpNorm_le_liminf_of_tendsto`) together with the uniform bound for the
truncations gives the bound for arbitrary `f`. -/
theorem eLpNorm_kmtProj_le_of_IWLqBound {ρ : ℝ} (l : ℕ) (k : ℤ) {p : ℝ} (hp1 : 1 < p)
    {C : NNReal} (hC : 0 < C)
    (hb : IWLqBound (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))
      (ENNReal.ofReal p) C) :
    ∀ f : ℤ → ℂ, eLpNorm (Work.KMTContract.kmtProj ρ l k f) (ENNReal.ofReal p) Measure.count
      ≤ ENNReal.ofReal (C : ℝ) * eLpNorm f (ENNReal.ofReal p) Measure.count := by
  intro f
  by_cases hfin : eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) = ⊤
  · rw [hfin, ENNReal.mul_top (ENNReal.ofReal_ne_zero_iff.mpr (by positivity))]
    exact le_top
  · have hflt : eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) < ⊤ :=
      lt_top_iff_ne_top.mpr hfin
    have hfmem : MemLp f (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
      (MeasureTheory.memLp_iff.mpr (hflt))
    have hle : ∀ K : ℕ,
        eLpNorm (Work.KMTContract.kmtProj ρ l k (Work.KMTContract.truncZ K f))
            (ENNReal.ofReal p) (Measure.count : Measure ℤ)
          ≤ ENNReal.ofReal (C : ℝ) * eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) := by
      intro K
      refine (hb ℂ (Work.KMTContract.truncZ K f)
        (finite_support_of_finSupp (Work.KMTContract.finsupp_truncZ K f))).trans ?_
      have hpt : ∀ x : ℤ, ‖Work.KMTContract.truncZ K f x‖ ≤ ‖f x‖ := by
        intro x
        by_cases hx : |x| ≤ (K : ℤ)
        · rw [Work.KMTContract.truncZ_of_le hx]
        · rw [Work.KMTContract.truncZ_of_gt (not_le.mp hx), norm_zero]
          positivity
      exact mul_le_mul_right (eLpNorm_mono (hf := by pw_aesm) hpt) _
    have hlim : ∀ x : ℤ, Tendsto (fun K : ℕ => Work.KMTContract.kmtProj ρ l k
        (Work.KMTContract.truncZ K f) x) atTop (nhds (Work.KMTContract.kmtProj ρ l k f x)) :=
      fun x => Work.KMTContract.kmtProj_tendsto_truncZ ρ l k
        (Work.KMTContract.kmtKernel_decay ρ l k)
        (by rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff (lt_trans zero_lt_one hp1)]
            exact hp1) hfmem x
    refine (Commons.Analysis.Hilbert.eLpNorm_le_liminf_of_tendsto
      (p := p) (by linarith) hlim).trans ?_
    have hconst : Filter.liminf (fun _ : ℕ => ENNReal.ofReal (C : ℝ)
        * eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ)) atTop
        = ENNReal.ofReal (C : ℝ) * eLpNorm f (ENNReal.ofReal p) (Measure.count : Measure ℤ) :=
      Filter.liminf_const _
    have hmono : Filter.liminf (fun K : ℕ => eLpNorm (Work.KMTContract.kmtProj ρ l k
          (Work.KMTContract.truncZ K f)) (ENNReal.ofReal p) (Measure.count : Measure ℤ)) atTop
        ≤ Filter.liminf (fun _ : ℕ => ENNReal.ofReal (C : ℝ) * eLpNorm f (ENNReal.ofReal p)
          (Measure.count : Measure ℤ)) atTop :=
      Filter.liminf_le_liminf (Filter.eventually_atTop.mpr ⟨0, fun K _ => hle K⟩)
    rw [hconst] at hmono
    exact hmono

end Work.KMTAreas.A7
