import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.OpArcLinear

namespace Work.BourgainPlan.KPWW

open MeasureTheory
open scoped ENNReal BigOperators lp Topology
open Work.BourgainPlan.IonescuWainger

/-! ## Auxiliary lemmas for the density/Fatou extension

The main theorem below extends an `ℓᵖ` bound for the arc multiplier `Op_{φ;E}` from finitely
supported sequences to all of `ℓ²(ℤ)`.  The auxiliary lemmas gathered here are the standard
ingredients of that argument (they are the ones used for the analogous extension of Tao's `(A6)`
estimate in `Submission/Work/IonescuWainger/main_real_l2.lean`):

* `inner_lpSMul_star'` — the adjunction identity `⟪A, Ψ • B⟫ = ⟪star Ψ • A, B⟫` for the `L^∞`
  multiplier;
* `arcTruncFinsupp` — the truncation `f · 1_s` of a sequence to a finite set `s`, with its basic
  properties (coefficients, domination, Hilbert-basis expansion);
* `tendsto_arcTruncFinsupp_lp` — the truncations converge to `f` in `ℓ²(ℤ)`;
* `tendsto_ftLp_of_lp_tendsto` — the `ℓ²(ℤ) ≅ L²(𝕋)` dictionary `ftLp` is continuous;
* `tendsto_opArc_arcTruncFinsupp` — hence `Op_{φ;E} f_N (n) → Op_{φ;E} f (n)` for every `n`, since
  the coefficient is an `ℓ²`-inner product with the e n;
* `eLpNorm_count_eq_tsum_ofReal` / `eLpNorm_count_rpow_eq_tsum` — the conversion between `eLpNorm`
  against the counting measure and the `ℓᵖ`-sum of the coefficients.
-/

/-- **Adjunction for the `L^∞`-multiplier**: for `Ψ ∈ L^∞` and `A, B ∈ L²`,
`⟪A, Ψ • B⟫ = ⟪star Ψ • A, B⟫`. -/
private theorem inner_lpSMul_star' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (Ψ : Lp ℂ ⊤ μ) (A B : Lp ℂ 2 μ) :
    inner ℂ A (Ψ • B : Lp ℂ 2 μ) = inner ℂ (star Ψ • A : Lp ℂ 2 μ) B := by
  rw [L2.inner_def, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) Ψ B,
    Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2) (star Ψ) A, Lp.coeFn_star Ψ]
    with ξ h1 h2 h3
  rw [h1, h2]
  simp only [smul_eq_mul, Pi.mul_apply]
  rw [h3]
  simp only [starRingEnd_apply, Pi.star_apply, RCLike.inner_apply, star_mul, star_star]
  ring

/-- Evaluation of the arc multiplier at `n` as an `ℓ²`-inner product against a *fixed* vector:
`Op_{φ;E} f (n) = ⟪star Φ • e_n, 𝓕f⟫` where `Φ = Σ_{β ∈ E} φ(· - β)` is the arc symbol. -/
private theorem opArc_apply_eq_inner' (φ : AddCircle (1 : ℝ) → ℂ)
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset (AddCircle (1 : ℝ))) (f : ℤ → ℂ) (hf : Memℓp f 2) (n : ℤ) :
    opArc φ hφ E f hf n
      = inner ℂ (star (arcSymbolLp φ hφ E) • fourierBasis (T := 1) n) (ftLp f hf) := by
  rw [opArc, opMul_apply, opMulLp, inner_lpSMul_star']

/-- The truncation of `f : ℤ → ℂ` to a finite set `s`, as a finitely supported sequence. -/
private noncomputable def arcTruncFinsupp (f : ℤ → ℂ) (s : Finset ℤ) : ℤ →₀ ℂ :=
  Finsupp.onFinset s (fun n => if n ∈ s then f n else 0)
    (fun n hn => by by_contra h; exact hn (by simp [h]))

private theorem arcTruncFinsupp_apply (f : ℤ → ℂ) (s : Finset ℤ) (n : ℤ) :
    arcTruncFinsupp f s n = if n ∈ s then f n else 0 := by
  rw [arcTruncFinsupp, Finsupp.onFinset_apply]

private theorem norm_arcTruncFinsupp_le (f : ℤ → ℂ) (s : Finset ℤ) (n : ℤ) :
    ‖arcTruncFinsupp f s n‖ ≤ ‖f n‖ := by
  rw [arcTruncFinsupp_apply]; split <;> simp

/-- The truncation of `f` to the finite set `s`, viewed in `ℓ²(ℤ)`, is the finitely supported
partial sum `Σ_{i ∈ s} f i · e_i` of the Hilbert-basis expansion of `f`. -/
private theorem coe_arcTruncFinsupp_eq_sum_single (f : ℤ → ℂ) (s : Finset ℤ) :
    (⟨⇑(arcTruncFinsupp f s), memℓp_finsupp _⟩ : lp (fun _ : ℤ => ℂ) 2)
      = ∑ i ∈ s, lp.single 2 i (f i) := by
  apply lp.ext
  funext n
  simp only [lp.coeFn_sum]
  rw [arcTruncFinsupp_apply]
  simp only [Finset.sum_apply, lp.single_apply, Pi.single_apply, Finset.sum_ite_eq]

/-- **The truncations of `f ∈ ℓ²(ℤ)` converge to `f` in `ℓ²`.** -/
private theorem tendsto_arcTruncFinsupp_lp (f : ℤ → ℂ) (hf : Memℓp f 2) :
    Filter.Tendsto (fun N : ℕ =>
        (⟨⇑(arcTruncFinsupp f (Finset.Icc (-(N : ℤ)) N)), memℓp_finsupp _⟩
          : lp (fun _ : ℤ => ℂ) 2)) Filter.atTop (𝓝 ⟨f, hf⟩) := by
  have hcof : Filter.Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) N) Filter.atTop
      (Filter.atTop : Filter (Finset ℤ)) := by
    rw [Filter.tendsto_atTop]
    intro t
    rw [Filter.eventually_atTop]
    refine ⟨t.sup (fun n => n.natAbs), fun N hN n hn => ?_⟩
    rw [Finset.mem_Icc]
    have h1 : n.natAbs ≤ t.sup (fun n => n.natAbs) := Finset.le_sup hn
    have h2 : n.natAbs ≤ N := le_trans h1 hN
    have h2' : (n.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast h2
    refine ⟨?_, ?_⟩
    · have h5 : -n ≤ (n.natAbs : ℤ) := by
        have := Int.le_natAbs (a := -n)
        rwa [Int.natAbs_neg] at this
      linarith
    · exact Int.le_natAbs.trans h2'
  have hsingle : HasSum (fun i : ℤ => lp.single 2 i (f i)) (⟨f, hf⟩ : lp (fun _ : ℤ => ℂ) 2) :=
    lp.hasSum_single (p := 2) (by norm_num) ⟨f, hf⟩
  have h1 : Filter.Tendsto (fun s : Finset ℤ => ∑ i ∈ s, lp.single 2 i (f i)) Filter.atTop
      (𝓝 (⟨f, hf⟩ : lp (fun _ : ℤ => ℂ) 2)) := by
    simpa only [HasSum, SummationFilter.unconditional_filter] using hsingle
  exact (h1.comp hcof).congr' (Filter.Eventually.of_forall fun N =>
    (coe_arcTruncFinsupp_eq_sum_single f _).symm)

/-- `ftLp` is continuous on `ℓ²`: the `ℓ² ≅ L²` dictionary commutes with limits. -/
private theorem tendsto_ftLp_of_lp_tendsto {g : ℕ → ℤ → ℂ} {gg : ∀ N, Memℓp (g N) 2} {h : ℤ → ℂ}
    (hh : Memℓp h 2)
    (hconv : Filter.Tendsto (fun N => (⟨g N, gg N⟩ : lp (fun _ : ℤ => ℂ) 2)) Filter.atTop
      (𝓝 (⟨h, hh⟩ : lp (fun _ : ℤ => ℂ) 2))) :
    Filter.Tendsto (fun N => ftLp (g N) (gg N)) Filter.atTop (𝓝 (ftLp h hh)) := by
  have hcomp : Filter.Tendsto ((fourierBasis (T := 1)).repr.symm ∘ fun N =>
      (⟨g N, gg N⟩ : lp (fun _ : ℤ => ℂ) 2)) Filter.atTop
      (𝓝 ((fourierBasis (T := 1)).repr.symm (⟨h, hh⟩ : lp (fun _ : ℤ => ℂ) 2))) :=
    ((fourierBasis (T := 1)).repr.symm.continuous.tendsto _).comp hconv
  have hfun : (fun N => ftLp (g N) (gg N)) = ((fourierBasis (T := 1)).repr.symm ∘ fun N =>
      (⟨g N, gg N⟩ : lp (fun _ : ℤ => ℂ) 2)) := rfl
  rw [hfun, show ftLp h hh = (fourierBasis (T := 1)).repr.symm (⟨h, hh⟩ :
    lp (fun _ : ℤ => ℂ) 2) from rfl]
  exact hcomp

/-- **Pointwise convergence of the arc multiplier along the truncations.**  Since `Op_{φ;E} f (n)`
is an `ℓ²`-inner product with a fixed vector (`opArc_apply_eq_inner'`) and `ftLp` is an isometry
equivalence, `f ↦ Op_{φ;E} f (n)` is continuous on `ℓ²`; the truncations converge to `f` in `ℓ²`. -/
private theorem tendsto_opArc_arcTruncFinsupp {f : ℤ → ℂ} (hf : Memℓp f 2)
    (φ : AddCircle (1 : ℝ) → ℂ)
    (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1))) (E : Finset (AddCircle (1 : ℝ)))
    (n : ℤ) :
    Filter.Tendsto (fun N : ℕ => opArc φ hφ E
        (⇑(arcTruncFinsupp f (Finset.Icc (-(N : ℤ)) N))) (memℓp_finsupp _) n) Filter.atTop
      (𝓝 (opArc φ hφ E f hf n)) := by
  have hc : Filter.Tendsto (fun N : ℕ =>
      ftLp (⇑(arcTruncFinsupp f (Finset.Icc (-(N : ℤ)) N))) (memℓp_finsupp _)) Filter.atTop
        (𝓝 (ftLp f hf)) :=
    tendsto_ftLp_of_lp_tendsto hf (tendsto_arcTruncFinsupp_lp f hf)
  have h2 : Filter.Tendsto (fun N : ℕ =>
      inner ℂ (star (arcSymbolLp φ hφ E) • fourierBasis (T := 1) n)
        (ftLp (⇑(arcTruncFinsupp f (Finset.Icc (-(N : ℤ)) N))) (memℓp_finsupp _))) Filter.atTop
      (𝓝 (inner ℂ (star (arcSymbolLp φ hφ E) • fourierBasis (T := 1) n)
        (ftLp f hf))) :=
    tendsto_const_nhds.inner hc
  rw [opArc_apply_eq_inner' φ hφ E f hf n]
  exact h2.congr (fun N =>
    (opArc_apply_eq_inner' φ hφ E _ (memℓp_finsupp _) n).symm)

/-- `eLpNorm` against the counting measure on `ℤ` as a (possibly infinite) `ℓ^q` sum. -/
private lemma eLpNorm_count_eq_tsum_ofReal (X : ℤ → ℂ) {q : ℝ} (hq : 0 < q) :
    eLpNorm X (ENNReal.ofReal q) Measure.count
      = (∑' n : ℤ, ENNReal.ofReal (‖X n‖ ^ q)) ^ (1 / q) := by
  rw [MeasureTheory.eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top
    MeasureTheory.AEStronglyMeasurable.of_discrete,
    MeasureTheory.eLpNorm', ENNReal.toReal_ofReal hq.le, MeasureTheory.lintegral_count]
  congr 1
  apply tsum_congr
  intro n
  rw [show ‖X n‖ₑ = ENNReal.ofReal ‖X n‖ by simp [enorm_eq_nnnorm],
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq.le]

/-- The `q`-th power of the `eLpNorm` against the counting measure is the `ℓ^q`-sum. -/
private lemma eLpNorm_count_rpow_eq_tsum (X : ℤ → ℂ) {q : ℝ} (hq : 0 < q) :
    (eLpNorm X (ENNReal.ofReal q) Measure.count) ^ q
      = ∑' n : ℤ, ENNReal.ofReal (‖X n‖ ^ q) := by
  rw [eLpNorm_count_eq_tsum_ofReal X hq, ← ENNReal.rpow_mul, one_div_mul_cancel (ne_of_gt hq),
    ENNReal.rpow_one]

/-- **Extension of an `ℓᵖ` bound for the arc multiplier from finitely supported sequences to all of
`ℓ²(ℤ)`.**  If `opArc φ hφ E` satisfies an `ℓᵖ` bound with constant `M` on finitely supported
sequences, then it satisfies the same bound on every `f` with `Memℓp f 2`.  This is the last step of
every interpolation argument for `opArc` (Riesz–Thorin is only available for finitely supported
inputs).

Route.  Let `f ∈ ℓ²(ℤ)` and `f_K := f · 1_{[-K,K]}` (a finitely supported sequence).  Then
(i) `f_K → f` in `ℓ²`, and (ii) `opArc` is continuous on `ℓ²`: by `ftLp_opMul`,
`ftLp (opArc φ hφ E f hf) = arcSymbolLp φ hφ E • ftLp f`, so for `u, v ∈ ℓ²`
`‖ftLp (opArc u) - ftLp (opArc v)‖ ≤ ‖arcSymbolLp φ hφ E‖ * ‖u - v‖_{ℓ²}`
(`Lp.norm_smul_le` together with `ftLp_add`, `ftLp_smul`, `ftLp_congr_memℓp` and the fact that
`ftLp` is an isometry, `HilbertBasis.repr.symm`).  Hence `opArc f_K → opArc f` in `ℓ²`, and since
`‖x m‖ ≤ ‖x‖_{ℓ²}` (`lp.norm_apply_le_norm`) this is *uniform* convergence, so
`opArc f_K m → opArc f m` for every `m : ℤ`.

Then for every finite window `W` of `ℤ` and every `K`,
`∑_{m ∈ W} ‖opArc f_K m‖ₑ^p ≤ eLpNorm (opArc f_K) p ^ p ≤ (ofReal M)^p * eLpNorm f_K p ^ p
 ≤ (ofReal M)^p * ∫⁻ m, ‖f m‖ₑ^p ∂count`,
and letting `K → ∞` (finite sum, each term converges; `0 < p`) gives the same inequality with
`opArc f`.  Finally take the supremum over `W`: `∫⁻ m, ‖opArc f m‖ₑ^p ∂count
= ⨆ W, ∑_{m ∈ W} ‖opArc f m‖ₑ^p` by `MeasureTheory.lintegral_count` and
`ENNReal.tsum_eq_iSup_sum`, and rewrite the two `eLpNorm`s back with
`MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal` plus `ENNReal.mul_rpow`, `ENNReal.rpow_mul`
(the conversion for the finsupp side is `Work.BourgainPlan.Maximal.eLpNorm_count_eq_ofReal_sum` in
`Submission.Work.BourgainPlan.Maximal.ellp_interpolation`). -/
theorem eLpNorm_opArc_le_of_finsupp {p : ℝ} (hp : 0 < p) {M : ℝ} (hM : 0 ≤ M)
    (φ : AddCircle (1 : ℝ) → ℂ) (hφ : MemLp φ ⊤ (AddCircle.haarAddCircle (T := 1)))
    (E : Finset (AddCircle (1 : ℝ)))
    (hfin : ∀ g : ℤ →₀ ℂ,
        MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArcLM φ hφ E g)
            (ENNReal.ofReal p) MeasureTheory.Measure.count
          ≤ ENNReal.ofReal M
              * MeasureTheory.eLpNorm (g : ℤ → ℂ) (ENNReal.ofReal p) MeasureTheory.Measure.count)
    (f : ℤ → ℂ) (hf : Memℓp f 2) :
    MeasureTheory.eLpNorm (Work.BourgainPlan.IonescuWainger.opArc φ hφ E f hf)
        (ENNReal.ofReal p) MeasureTheory.Measure.count
      ≤ ENNReal.ofReal M * MeasureTheory.eLpNorm f (ENNReal.ofReal p) MeasureTheory.Measure.count := by
  have _hMuse : (0 : ℝ) ≤ M := hM
  -- (i) pointwise convergence of the `ℝ≥0∞`-valued averages along the truncations
  have hPhi : ∀ n : ℤ, Filter.Tendsto (fun N : ℕ => ENNReal.ofReal
      (‖opArc φ hφ E (⇑(arcTruncFinsupp f (Finset.Icc (-(N : ℤ)) N))) (memℓp_finsupp _) n‖ ^ p))
      Filter.atTop (𝓝 (ENNReal.ofReal (‖opArc φ hφ E f hf n‖ ^ p))) := by
    intro n
    have hc : Continuous fun z : ℂ => ENNReal.ofReal (‖z‖ ^ p) := by
      have h1 : Continuous fun z : ℂ => (ENNReal.ofReal ‖z‖) ^ p :=
        ENNReal.continuous_rpow_const.comp (ENNReal.continuous_ofReal.comp continuous_norm)
      exact h1.congr fun z => ENNReal.ofReal_rpow_of_nonneg (norm_nonneg z) hp.le
    exact hc.continuousAt.tendsto.comp (tendsto_opArc_arcTruncFinsupp hf φ hφ E n)
  -- (ii) the bound for every finite window of frequencies
  have hwin : ∀ s0 : Finset ℤ, ∑ n ∈ s0, ENNReal.ofReal (‖opArc φ hφ E f hf n‖ ^ p)
      ≤ (ENNReal.ofReal M) ^ p * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p) := by
    intro s0
    have hconv : Filter.Tendsto (fun N : ℕ => ∑ n ∈ s0, ENNReal.ofReal
        (‖opArc φ hφ E (⇑(arcTruncFinsupp f (Finset.Icc (-(N : ℤ)) N)))
          (memℓp_finsupp _) n‖ ^ p))
        Filter.atTop (𝓝 (∑ n ∈ s0, ENNReal.ofReal (‖opArc φ hφ E f hf n‖ ^ p))) :=
      tendsto_finsetSum s0 (fun n _ => hPhi n)
    refine le_of_tendsto' hconv (fun N => ?_)
    calc ∑ n ∈ s0, ENNReal.ofReal (‖opArc φ hφ E
            (⇑(arcTruncFinsupp f (Finset.Icc (-(N : ℤ)) N))) (memℓp_finsupp _) n‖ ^ p)
        ≤ ∑' n : ℤ, ENNReal.ofReal (‖opArc φ hφ E
            (⇑(arcTruncFinsupp f (Finset.Icc (-(N : ℤ)) N))) (memℓp_finsupp _) n‖ ^ p) :=
          ENNReal.sum_le_tsum s0
      _ = (eLpNorm (opArc φ hφ E (⇑(arcTruncFinsupp f (Finset.Icc (-(N : ℤ)) N)))
            (memℓp_finsupp _)) (ENNReal.ofReal p) Measure.count) ^ p :=
          (eLpNorm_count_rpow_eq_tsum _ hp).symm
      _ = (eLpNorm (opArcLM φ hφ E (arcTruncFinsupp f (Finset.Icc (-(N : ℤ)) N)))
            (ENNReal.ofReal p) Measure.count) ^ p := rfl
      _ ≤ (ENNReal.ofReal M * eLpNorm (⇑(arcTruncFinsupp f (Finset.Icc (-(N : ℤ)) N)))
            (ENNReal.ofReal p) Measure.count) ^ p :=
          ENNReal.rpow_le_rpow (hfin _) hp.le
      _ = (ENNReal.ofReal M) ^ p * ∑' n : ℤ, ENNReal.ofReal
            (‖arcTruncFinsupp f (Finset.Icc (-(N : ℤ)) N) n‖ ^ p) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le, eLpNorm_count_rpow_eq_tsum _ hp]
      _ ≤ (ENNReal.ofReal M) ^ p * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine ENNReal.tsum_le_tsum (fun n => ENNReal.ofReal_le_ofReal ?_)
          exact Real.rpow_le_rpow (norm_nonneg _) (norm_arcTruncFinsupp_le f _ n) hp.le
  -- (iii) supremum over the windows
  have hcore : ∑' n : ℤ, ENNReal.ofReal (‖opArc φ hφ E f hf n‖ ^ p)
      ≤ (ENNReal.ofReal M) ^ p * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p) := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_le hwin
  -- (iv) rewriting both `eLpNorm`s and taking the `p`-th root
  rw [eLpNorm_count_eq_tsum_ofReal (opArc φ hφ E f hf) hp, eLpNorm_count_eq_tsum_ofReal f hp]
  calc (∑' n : ℤ, ENNReal.ofReal (‖opArc φ hφ E f hf n‖ ^ p)) ^ (1 / p)
      ≤ ((ENNReal.ofReal M) ^ p * ∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p)) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hcore (by positivity)
    _ = ENNReal.ofReal M * (∑' n : ℤ, ENNReal.ofReal (‖f n‖ ^ p)) ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
          mul_one_div_cancel (ne_of_gt hp), ENNReal.rpow_one]

end Work.BourgainPlan.KPWW
