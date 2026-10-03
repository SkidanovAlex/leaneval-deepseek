import Mathlib
import Submission.Work.A3.Basic
import Submission.Work.A3.hausdorffYoung
import Submission.Work.A3.eLpNorm_volume_Icc
import Submission.Work.A3.polyImproving_of_finsupp
import Submission.Work.A3Fix.DeepFinal
import Submission.Commons.Analysis.Hilbert.discrete_hilbert_transform_lp

/-!
# Area A3 of the KMT contract: `ℓ^p`-improving for the polynomial average

`Work.KMTContract.AreaA3` is `∀ Q : ℤ[X], 2 ≤ Q.natDegree → PolyImproving Q`, i.e.
Krause–Mirek–Tao, Proposition `lp-improv`, in the form "for *some* `p < 2`": there are `1 < p < 2`
and `C > 0` with

`‖A_N f‖_{ℓ²} ≤ C · N^{d(1/2 - 1/p)} · ‖f‖_{ℓ^p}`,  `A_N f(x) = N⁻¹ ∑_{n≤N} f(x - Q(n))`,  `d = deg Q`,

for all `N ≥ 1` and all `f`.

## The route (`Submission/Work/A3/Defs.lean` has the details)

Take the **arithmetic** input `Work.A3.PolyEnergyBound Q`: for some `s ≥ 2` and `C > 0`,

`E_s(N) := #{(n⃗,m⃗) ∈ [1,N]^s × [1,N]^s : ∑ᵢQ(nᵢ) = ∑ⱼQ(mⱼ)} ≤ C^{2s} N^{2s-d}`

for all `N ≥ 1`.  This is the `2s`-th moment (`Work.A3.moment_identity`):

`∫₀¹ ‖m_N(θ)‖^{2s} dθ = N^{-2s} E_s(N)`,  `m_N(θ) = N⁻¹ ∑_{n≤N} e(-2πi θ Q(n))`.

Set `p := 2s/(s+1)`, so `1/p = 1/2 + 1/(2s)` and `d(1/2 - 1/p) = -d/(2s)`.  For finitely
supported `f` the assembly is then

`‖A_N f‖_{ℓ²}² = ∑_x ‖A_N f x‖²` (counting measure)
`= ∫₀¹ ‖𝓕(A_N f)‖²` (`Work.A3.parseval_finsupp`)
`= ∫₀¹ ‖m_N · f̂‖²` (`Work.A3.fhat_conv`)
`≤ (∫₀¹‖m_N‖^{2s})^{1/s} (∫₀¹‖f̂‖^{p'})^{(s-1)/s}` (Hölder, `p' = 2s/(s-1)`)
`≤ (C²N^{-d/s}) · ‖f‖_{ℓ^p}²` (`Work.A3.moment_identity` + the energy bound,
and Hausdorff–Young `Work.A3.hausdorffYoung` for `(∫₀¹‖f̂‖^{p'})^{1/p'} ≤ ‖f‖_{ℓ^p}`),

hence `‖A_N f‖_{ℓ²} ≤ C N^{-d/(2s)} ‖f‖_{ℓ^p} = C N^{d(1/2-1/p)} ‖f‖_{ℓ^p}`.  The passage from
finitely supported to all `f` is `Work.A3.polyImproving_of_finsupp` (truncation + Fatou).

**Status.**  The frequency chain above is **proved** (below, in `polyImproving_of_energyBound`):
it uses only `Work.A3.parseval_finsupp`, `Work.A3.fhat_conv`, `Work.A3.moment_identity`,
`Work.A3.eLpNorm_volume_Icc`, `Work.A3.hausdorffYoung` (Hausdorff--Young on `ℤ`) and
`Commons.Analysis.Hilbert.eLpNorm_count_eq_ofReal`, together with the elementary `Nˢ`-lower
bound on the energy (`pow_le_polyEnergy`, which shows that a witness `s` of `PolyEnergyBound`
automatically satisfies `deg Q ≤ 2s`).

Hence **`Work.KMTAreas.area_A3` rests on the single arithmetic input `Work.A3.polyEnergy_bound`**
(the sharp mean value estimate `E_s(N) ≤ C^{2s}N^{2s-d}`, i.e. the Hardy--Littlewood circle
method for one polynomial equation).  The circle-method pieces are being formalised in parallel
in `Submission/Work/A3/`: `weyl_poly` (Weyl's inequality, the minor arcs),
`completeSum_power_saving` (the saving for complete sums), `singInt_bound` (the singular
integral), and the major/minor arc contributions from which `polyEnergy_bound` is assembled.
The vocabulary in which these are stated is `Submission/Work/A3/Circle.lean`
(`expSum`, `completeSum`, `singInt`, `majorArcSet`), and `Work.A3.integral_norm_expSum_pow`
identifies the `2s`-th moment of `expSum` with `polyEnergy Q s N`.
-/


set_option autoImplicit false

namespace Work.KMTAreas

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Elementary ingredients of the frequency chain -/

/-- The multiplier `θ ↦ m_N(θ)` of the averaging operator is continuous. -/
private lemma continuous_kmtMul (Q : ℤ[X]) (N : ℕ) : Continuous (fun θ : ℝ => Work.A3.kmtMul Q N θ) := by
  unfold Work.A3.kmtMul
  fun_prop

/-- The Fourier transform `θ ↦ f̂(θ)` of a finitely supported function is continuous. -/
private lemma continuous_kmtFhat {f : ℤ → ℂ} {t : Finset ℤ} (ht : ∀ x ∉ t, f x = 0) :
    Continuous (fun θ : ℝ => Work.A3.kmtFhat f θ) := by
  have h : (fun θ : ℝ => Work.A3.kmtFhat f θ)
      = fun θ : ℝ => ∑ x ∈ t, f x * Complex.exp (-(2 * Real.pi * Complex.I * ((x : ℝ) * θ))) := by
    funext θ; exact Work.A3.kmtFhat_eq_sum ht θ
  rw [h]; fun_prop

/-- The *diagonal* lower bound for the energy: the `N^s` pairs `(v, v)` of equal `s`-tuples always
have equal `Q`-sums, so `N^s ≤ polyEnergy Q s N`.  (This is the elementary half of the sharpness
of `PolyEnergyBound`.) -/
private lemma pow_le_polyEnergy (Q : ℤ[X]) (s N : ℕ) : N^s ≤ Work.A3.polyEnergy Q s N := by
  classical
  have hinj : Function.Injective (fun v : Fin s → ℤ => (v, v)) := fun a b h => (Prod.mk.inj h).1
  have hsub : (Fintype.piFinset (fun _ : Fin s => Finset.Icc (1:ℤ) (N:ℤ))).image (fun v => (v,v))
      ⊆ ((Fintype.piFinset (fun _ : Fin s => Finset.Icc (1:ℤ) (N:ℤ))).product
          (Fintype.piFinset (fun _ : Fin s => Finset.Icc (1:ℤ) (N:ℤ)))).filter
          (fun p => (∑ i, Q.eval (p.1 i)) = (∑ i, Q.eval (p.2 i))) := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hv, hv⟩, rfl⟩
  calc N^s = (Fintype.piFinset (fun _ : Fin s => Finset.Icc (1:ℤ) (N:ℤ))).card := by
        rw [Fintype.card_piFinset]; simp [Finset.prod_const, Int.card_Icc]
    _ = _ := by rw [Finset.card_image_of_injective _ hinj]
    _ ≤ _ := Finset.card_le_card hsub

/-- `(x^2)^s = x^(2s)` for `x ≥ 0` and a natural `s` (in the `ℝ`-power notation). -/
private lemma rpow_sq_nat (x : ℝ) (hx : 0 ≤ x) (s : ℕ) : (x^2)^(s:ℝ) = x^(2*s) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_natCast x (2*s), ← Real.rpow_mul hx]
  congr 1; push_cast; ring

/-- `(x^2)^(s/(s-1)) = x^(2s/(s-1))` for `x ≥ 0`. -/
private lemma rpow_sq_div (x : ℝ) (hx : 0 ≤ x) (s : ℕ) :
    (x^2)^((s:ℝ)/((s:ℝ)-1)) = x^(2*(s:ℝ)/((s:ℝ)-1)) := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx]
  congr 1; ring

/-- **The reduction of Area A3 to the arithmetic energy bound.**  If `PolyEnergyBound Q` holds
(for some `s ≥ 2` and `C`), then `PolyImproving Q` holds with `p = 2s/(s+1)` and the same
constant `C`. -/
theorem polyImproving_of_energyBound (Q : ℤ[X]) (h : Work.A3.PolyEnergyBound Q) :
    Work.KMTContract.PolyImproving Q := by
  obtain ⟨s, hs2, C, hCpos, hCB⟩ := h
  have hsR : (0:ℝ) < (s:ℝ) := by positivity
  have hsR1 : (1:ℝ) < (s:ℝ) := by exact_mod_cast (by omega : 1 < s)
  set p : ℝ := (2*(s:ℝ))/((s:ℝ)+1) with hpdef
  have hp1 : 1 < p := by
    rw [hpdef, lt_div_iff₀ (by positivity)]; linarith
  have hp2 : p < 2 := by
    rw [hpdef, div_lt_iff₀ (by positivity)]; linarith
  have hp0 : 0 < p := lt_trans zero_lt_one hp1
  have hpexp : (Q.natDegree : ℝ) * (1/2 - 1/p) = -((Q.natDegree : ℝ))/(2*(s:ℝ)) := by
    rw [hpdef]; field_simp; ring
  refine ⟨p, hp1, hp2, C, hCpos, ?_⟩
  -- the extension from finitely supported `f` to all `f`
  refine Work.A3.polyImproving_of_finsupp Q p hp1 hp2 (C : ℝ≥0∞) ?_ ?_ ?_
  · simp [hCpos.ne']
  · exact ENNReal.coe_ne_top
  -- the finite-support frequency chain
  intro N hN f hf
  obtain ⟨t, ht⟩ := hf
  -- we may assume `2s ≥ deg Q` (otherwise `PolyEnergyBound` fails for large `N`, by the
  -- diagonal lower bound on the energy)
  have hsd : Q.natDegree ≤ 2*s := by
    by_contra hcon
    have hzero : 2*s - Q.natDegree = 0 := by omega
    have hb : ∀ M : ℕ, 1 ≤ M → (Work.A3.polyEnergy Q s M : ℝ) ≤ (C:ℝ)^(2*s) := by
      intro M hM
      have hh := hCB M hM
      rw [hzero] at hh
      simpa using hh
    obtain ⟨M, hM1⟩ := exists_nat_gt (max 1 ((C:ℝ)^2 + 1))
    have hM0 : 1 ≤ M := by
      have h1 : (1:ℝ) < (M:ℝ) := lt_of_le_of_lt (le_max_left _ _) hM1
      exact_mod_cast (by linarith : (1:ℝ) ≤ (M:ℝ))
    have hlow : (M:ℝ)^s ≤ (Work.A3.polyEnergy Q s M : ℝ) := by exact_mod_cast pow_le_polyEnergy Q s M
    have hup := hb M hM0
    have hCs : ((C:ℝ)^2)^s = (C:ℝ)^(2*s) := by rw [← pow_mul]
    have hle : (M:ℝ) ≤ (C:ℝ)^2 := by
      refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by omega : s ≠ 0)).mp ?_
      rw [hCs]; exact le_trans hlow hup
    have hgt : (C:ℝ)^2 + 1 < (M:ℝ) := lt_of_le_of_lt (le_max_right _ _) hM1
    linarith
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hN0
  set A : ℤ → ℂ := fun x => (N:ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f (x - Polynomial.eval (n:ℤ) Q) with hA
  set T : Finset ℤ := (Finset.Icc 1 N).biUnion (fun n => t.image (fun x => x + Polynomial.eval (n:ℤ) Q)) with hT
  have hAsupp : ∀ x ∉ T, A x = 0 := by
    intro x hx
    show (N : ℂ)⁻¹ * (∑ n ∈ Finset.Icc 1 N, f (x - Polynomial.eval (n:ℤ) Q)) = 0
    have h0 : ∑ n ∈ Finset.Icc 1 N, f (x - Polynomial.eval (n:ℤ) Q) = 0 := by
      refine Finset.sum_eq_zero (fun n hn => ?_)
      refine ht _ (fun hmem => hx ?_)
      rw [hT, Finset.mem_biUnion]
      exact ⟨n, hn, Finset.mem_image.mpr ⟨x - Polynomial.eval (n:ℤ) Q, hmem, by ring⟩⟩
    rw [h0, mul_zero]
  have hconv : ∀ θ, Work.A3.kmtFhat A θ = Work.A3.kmtMul Q N θ * Work.A3.kmtFhat f θ := by
    intro θ
    show Work.A3.kmtFhat (fun x => (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f (x - Polynomial.eval (n : ℤ) Q)) θ = _
    exact Work.A3.fhat_conv Q N f ⟨t, ht⟩ hN θ
  -- the `L^{2s}` bound on the multiplier (Plancherel + the energy bound)
  have hmom : (∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtMul Q N θ‖^(2*s))^(1/(s:ℝ))
      ≤ (C:ℝ)^2 * (N:ℝ)^(-((Q.natDegree:ℝ)/(s:ℝ))) := by
    have key : ∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtMul Q N θ‖^(2*s)
        ≤ (C:ℝ)^(2*s) * (N:ℝ)^(-(Q.natDegree:ℝ)) := by
      have hCB' := hCB N hN
      rw [Work.A3.moment_identity Q N s hN]
      have hNs : (N:ℝ)^(2*s - Q.natDegree) = (N:ℝ)^(2*s) * ((N:ℝ)^(Q.natDegree))⁻¹ := by
        rw [pow_sub₀ (N:ℝ) hNne hsd]
      rw [hNs] at hCB'
      have hneg : (N:ℝ)^(-(Q.natDegree:ℝ)) = ((N:ℝ)^(Q.natDegree))⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hN0), Real.rpow_natCast]
      rw [hneg]
      calc ((N:ℝ)^(2*s))⁻¹ * (Work.A3.polyEnergy Q s N : ℝ)
          ≤ ((N:ℝ)^(2*s))⁻¹ * ((C:ℝ)^(2*s) * ((N:ℝ)^(2*s) * ((N:ℝ)^(Q.natDegree))⁻¹)) :=
            mul_le_mul_of_nonneg_left hCB' (by positivity)
        _ = (C:ℝ)^(2*s) * ((N:ℝ)^(Q.natDegree))⁻¹ := by
            field_simp
    have hnonneg : (0:ℝ) ≤ ∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtMul Q N θ‖^(2*s) :=
      setIntegral_nonneg measurableSet_Icc (fun θ _ => by positivity)
    calc (∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtMul Q N θ‖^(2*s))^(1/(s:ℝ))
        ≤ ((C:ℝ)^(2*s) * (N:ℝ)^(-(Q.natDegree:ℝ)))^(1/(s:ℝ)) :=
          Real.rpow_le_rpow hnonneg key (by positivity)
      _ = (C:ℝ)^2 * (N:ℝ)^(-((Q.natDegree:ℝ)/(s:ℝ))) := by
          rw [← Real.rpow_natCast (C:ℝ) (2*s),
              Real.mul_rpow (by positivity) (by positivity),
              ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
          have e1 : ((2*s : ℕ) : ℝ)*(1/(s:ℝ)) = 2 := by push_cast; field_simp
          have e2 : (-((Q.natDegree:ℝ)))*(1/(s:ℝ)) = -((Q.natDegree:ℝ)/(s:ℝ)) := by field_simp
          rw [e1, e2]
          norm_num
  -- the `L^{2s/(s-1)}` bound on `f̂` (Hausdorff--Young)
  have hHY : (∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtFhat f θ‖^(2*(s:ℝ)/((s:ℝ)-1)))^(((s:ℝ)-1)/(s:ℝ))
      ≤ (∑' x:ℤ, ‖f x‖^p)^(2/p) := by
    have hpp_eq : p/(p-1) = 2*(s:ℝ)/((s:ℝ)-1) := by rw [hpdef]; field_simp; ring
    have hpp_pos : 0 < p/(p-1) := by positivity
    have hsumf : Summable (fun x : ℤ => ‖f x‖ ^ p) := Work.A3.summable_norm_rpow_of_finsupp ht hp0
    have hnormf : eLpNorm f (ENNReal.ofReal p) Measure.count
        = ENNReal.ofReal ((∑' x : ℤ, ‖f x‖ ^ p) ^ (1/p)) :=
      Commons.Analysis.Hilbert.eLpNorm_count_eq_ofReal f hp0 hsumf
    have hcont : Continuous (fun θ : ℝ => ‖Work.A3.kmtFhat f θ‖ ^ (p/(p-1))) :=
      (continuous_kmtFhat ht).norm.rpow_const (fun _ => Or.inr hpp_pos.le)
    have hInt : Integrable (fun θ : ℝ => ‖Work.A3.kmtFhat f θ‖ ^ (p/(p-1))) Work.A3.kmtNu :=
      Integrable.of_bound hcont.aestronglyMeasurable ((∑ x ∈ t, ‖f x‖)^(p/(p-1))) (by
        filter_upwards with θ
        rw [Real.norm_of_nonneg (by positivity)]
        exact Real.rpow_le_rpow (norm_nonneg _) (Work.A3.norm_kmtFhat_le ht θ) hpp_pos.le)
    have hLY : eLpNorm (Work.A3.kmtFhat f) (ENNReal.ofReal (p/(p-1))) Work.A3.kmtNu
        = ENNReal.ofReal ((∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtFhat f θ‖^(p/(p-1)))^(1/(p/(p-1)))) :=
      Work.A3.eLpNorm_volume_Icc (Work.A3.kmtFhat f) (p/(p-1)) hpp_pos hInt
        (continuous_kmtFhat ht).aestronglyMeasurable
    have hHYP : eLpNorm (Work.A3.kmtFhat f) (ENNReal.ofReal (p/(p-1))) Work.A3.kmtNu
        ≤ eLpNorm f (ENNReal.ofReal p) Measure.count := by
      have h := Work.A3.hausdorffYoung p hp1 hp2.le t f
      have hfe : (fun x : ℤ => if x ∈ t then f x else 0) = f := by
        funext x; by_cases hx : x ∈ t
        · simp [hx]
        · simp [hx, ht x hx]
      simpa [hfe] using h
    have hAB : (∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtFhat f θ‖^(p/(p-1)))^(1/(p/(p-1)))
        ≤ (∑' x : ℤ, ‖f x‖^p)^(1/p) := by
      have h := hHYP
      rw [hLY, hnormf] at h
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h
    have h2 := Real.rpow_le_rpow (by positivity) hAB (by norm_num : (0:ℝ) ≤ 2)
    have e1 : (∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtFhat f θ‖^(p/(p-1)))^(((s:ℝ)-1)/(s:ℝ))
        = ((∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtFhat f θ‖^(p/(p-1)))^(1/(p/(p-1))))^(2:ℝ) := by
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      rw [hpp_eq]
      field_simp
    have e2 : ((∑' x : ℤ, ‖f x‖^p)^(1/p))^(2:ℝ) = (∑' x : ℤ, ‖f x‖^p)^(2/p) := by
      rw [← Real.rpow_mul (by positivity)]
      congr 1
      field_simp
    calc (∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtFhat f θ‖^(2*(s:ℝ)/((s:ℝ)-1)))^(((s:ℝ)-1)/(s:ℝ))
        = (∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtFhat f θ‖^(p/(p-1)))^(((s:ℝ)-1)/(s:ℝ)) := by
          rw [hpp_eq]
      _ = ((∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtFhat f θ‖^(p/(p-1)))^(1/(p/(p-1))))^(2:ℝ) := e1
      _ ≤ ((∑' x : ℤ, ‖f x‖^p)^(1/p))^(2:ℝ) := h2
      _ = (∑' x : ℤ, ‖f x‖^p)^(2/p) := e2
  -- Hölder
  have hholder' : ∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtMul Q N θ‖^2 * ‖Work.A3.kmtFhat f θ‖^2
      ≤ (∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtMul Q N θ‖^(2*s))^(1/(s:ℝ))
        * (∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtFhat f θ‖^(2*(s:ℝ)/((s:ℝ)-1)))^(((s:ℝ)-1)/(s:ℝ)) := by
    set qq : ℝ := (s:ℝ)/((s:ℝ)-1) with hqq
    have hqq_conj : (s:ℝ).HolderConjugate qq := Real.HolderConjugate.conjExponent hsR1
    have hmeas1 : AEStronglyMeasurable (fun θ : ℝ => ‖Work.A3.kmtMul Q N θ‖ ^ 2) Work.A3.kmtNu :=
      ((continuous_kmtMul Q N).norm.pow 2).aestronglyMeasurable
    have hmeas2 : AEStronglyMeasurable (fun θ : ℝ => ‖Work.A3.kmtFhat f θ‖ ^ 2) Work.A3.kmtNu :=
      ((continuous_kmtFhat ht).norm.pow 2).aestronglyMeasurable
    have hmem1 : MemLp (fun θ : ℝ => ‖Work.A3.kmtMul Q N θ‖ ^ 2) (ENNReal.ofReal (s:ℝ)) Work.A3.kmtNu := by
      refine MemLp.of_bound hmeas1 1 ?_
      filter_upwards with θ
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_one₀ (norm_nonneg _) (Work.A3.norm_kmtMul_le Q N hN θ)
    have hmem2 : MemLp (fun θ : ℝ => ‖Work.A3.kmtFhat f θ‖ ^ 2) (ENNReal.ofReal qq) Work.A3.kmtNu := by
      refine MemLp.of_bound hmeas2 ((∑ x ∈ t, ‖f x‖)^2) ?_
      filter_upwards with θ
      rw [Real.norm_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) (Work.A3.norm_kmtFhat_le ht θ) 2
    have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := Work.A3.kmtNu) (p := (s:ℝ)) (q := qq)
      hqq_conj (Filter.Eventually.of_forall (fun θ => by positivity))
      (Filter.Eventually.of_forall (fun θ => by positivity)) hmem1 hmem2
    have hqq3 : 1/qq = ((s:ℝ)-1)/(s:ℝ) := by rw [hqq]; field_simp
    have h1 : (∫ θ in Set.Icc (0:ℝ) 1, (‖Work.A3.kmtMul Q N θ‖^2)^(s:ℝ))
        = (∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtMul Q N θ‖^(2*s)) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => rpow_sq_nat _ (norm_nonneg _) s))
    have h2 : (∫ θ in Set.Icc (0:ℝ) 1, (‖Work.A3.kmtFhat f θ‖^2)^qq)
        = (∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtFhat f θ‖^(2*(s:ℝ)/((s:ℝ)-1))) :=
      integral_congr_ae (Filter.Eventually.of_forall (fun θ => rpow_sq_div _ (norm_nonneg _) s))
    rw [h1, h2, hqq3] at hholder
    exact hholder
  -- the endgame
  have hE : ∑' x:ℤ, ‖A x‖^2 = ∫ θ in Set.Icc (0:ℝ) 1, ‖Work.A3.kmtMul Q N θ‖^2 * ‖Work.A3.kmtFhat f θ‖^2 := by
    rw [← Work.A3.parseval_finsupp A ⟨T, hAsupp⟩]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [hconv θ, norm_mul, mul_pow]
  have hreal : (∑' x : ℤ, ‖A x‖ ^ 2) ^ (1/2:ℝ)
      ≤ (C:ℝ) * (N:ℝ)^(-((Q.natDegree:ℝ)/(2*(s:ℝ)))) * (∑' x : ℤ, ‖f x‖ ^ p) ^ (1/p) := by
    have hmid : (∑' x : ℤ, ‖A x‖ ^ 2)
        ≤ (C:ℝ)^2 * (N:ℝ)^(-((Q.natDegree:ℝ)/(s:ℝ))) * (∑' x : ℤ, ‖f x‖ ^ p) ^ (2/p) := by
      rw [hE]
      exact hholder'.trans (mul_le_mul hmom hHY (Real.rpow_nonneg (by positivity) _) (by positivity))
    have hnn : (0:ℝ) ≤ ∑' x : ℤ, ‖A x‖ ^ 2 := tsum_nonneg (fun x => by positivity)
    calc (∑' x : ℤ, ‖A x‖ ^ 2) ^ (1/2:ℝ)
        ≤ ((C:ℝ)^2 * (N:ℝ)^(-((Q.natDegree:ℝ)/(s:ℝ))) * (∑' x : ℤ, ‖f x‖ ^ p) ^ (2/p)) ^ (1/2:ℝ) :=
          Real.rpow_le_rpow hnn hmid (by norm_num)
      _ = (C:ℝ) * (N:ℝ)^(-((Q.natDegree:ℝ)/(2*(s:ℝ)))) * (∑' x : ℤ, ‖f x‖ ^ p) ^ (1/p) := by
          have hCc : ((C:ℝ)^2)^(1/2:ℝ) = (C:ℝ) := by
            rw [← Real.sqrt_eq_rpow]
            exact Real.sqrt_sq (le_of_lt hCpos)
          have hNn : ((N:ℝ)^(-((Q.natDegree:ℝ)/(s:ℝ))))^(1/2:ℝ)
              = (N:ℝ)^(-((Q.natDegree:ℝ)/(2*(s:ℝ)))) := by
            rw [← Real.rpow_mul (by positivity)]
            congr 1
            field_simp
          have hSs : ((∑' x : ℤ, ‖f x‖^p)^(2/p))^(1/2:ℝ) = (∑' x : ℤ, ‖f x‖^p)^(1/p) := by
            rw [← Real.rpow_mul (by positivity)]
            congr 1
            field_simp
          rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
            hCc, hNn, hSs]
  -- convert back to `eLpNorm`
  have hsumA : Summable (fun x : ℤ => ‖A x‖ ^ (2:ℝ)) :=
    Work.A3.summable_norm_rpow_of_finsupp hAsupp (by norm_num)
  have hnormA : eLpNorm A 2 Measure.count
      = ENNReal.ofReal ((∑' x : ℤ, ‖A x‖ ^ 2) ^ (1/2:ℝ)) := by
    have h := Commons.Analysis.Hilbert.eLpNorm_count_eq_ofReal A (p := 2) (by norm_num) hsumA
    simpa using h
  have hsumf : Summable (fun x : ℤ => ‖f x‖ ^ p) := Work.A3.summable_norm_rpow_of_finsupp ht hp0
  have hnormf : eLpNorm f (ENNReal.ofReal p) Measure.count
      = ENNReal.ofReal ((∑' x : ℤ, ‖f x‖ ^ p) ^ (1/p)) :=
    Commons.Analysis.Hilbert.eLpNorm_count_eq_ofReal f hp0 hsumf
  have hexp2 : -((Q.natDegree:ℝ)/(2*(s:ℝ))) = (Q.natDegree:ℝ) * (1/2 - 1/p) := by
    rw [hpexp]; ring
  rw [hnormA, hnormf]
  refine (ENNReal.ofReal_le_ofReal hreal).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity), hexp2,
    ENNReal.ofReal_coe_nnreal]

/-- **Area A3** of the KMT contract, from the arithmetic energy bound. -/
theorem area_A3 : Work.KMTContract.AreaA3 := fun Q hd =>
  polyImproving_of_energyBound Q (Work.A3.polyEnergy_bound_complete Q hd)

end

end Work.KMTAreas
