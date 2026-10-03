import Mathlib
import Submission.Work.KMTAreas.A7Hi.LowpassDefs
import Submission.Work.KMTAreas.A7.periodizeEqSelfOfMemRealArc
import Submission.Work.KMTAreas.A7Hi.tsum_conv_conv
import Submission.Work.KMTAreas.A5.fourierCoeff_mul_eq_tsum_conv
import Submission.Work.KMTAreas.A7.variationalNorm_mul_le
import Submission.Work.KMTAreas.A7G.plainBumpVarG
import Submission.Work.KMTAreas.A7Lpd.supChainSq

/-!
## The nesting of the Ionescu--Wainger projections `kmtProj ρ l` at two different heights

This file carries the target `Work.KMTAreas.A7G.chainPartLowpass` together with the
**nesting plank** it needs (see `NOTES_chainPartLowpass_SESSION_A7G.md` §2, §8, §9).

`kmtProj ρ l k` is the IW projection with symbol `Φ_k = periodize (etaCut kmtEta k)`, i.e.
`Σ_{α ∈ (ℚ/ℤ)_{≤l}} η((ξ-α)/2^k)`.  The classical Littlewood--Paley nesting
`etaCut_mul` (`η_{≤k}·η_{≤k'} = η_{≤k'}` for `k' < k`) upgrades to the *IW symbols* because the
cross terms `α ≠ β` vanish exactly by the non-aliasing of the frequency set, which is what
`iwSymbolSet_mul` provides.  Concretely we prove

`iwSymbolSet A Φ_k * iwSymbolSet A Φ_{k'} = iwSymbolSet A Φ_{k'}`   (`k' < k`, `NonAliasing k A`),

whence (with `iwConv_comp`) `kmtProj ρ l k ∘ kmtProj ρ l k' = kmtProj ρ l k'` for the two heights,
and in particular the increments `kmtProj ρ l (-(m₀+m+1)) f - kmtProj ρ l (-(m₀+m)) f` are
mutually orthogonal in `ℓ²`, as are the block sums along any chain.  This corrects
`NOTES_A7Hi2_chainLe_ANALYSIS.md` §5/§6, which recorded the nesting as unavailable.
-/

open Work.Analysis.IonescuWainger

namespace Work.KMTAreas.A7G

/-- The support of the cutoff `η_{≤k}`: `|x| ≤ 2^k` whenever it does not vanish. -/
theorem etaCut_kmtEta_support (k : ℤ) {x : ℝ}
    (h : etaCut Work.KMTContract.kmtEta k x ≠ 0) : |x| ≤ (2 : ℝ) ^ k := by
  simp only [etaCut] at h
  by_contra hc
  have hpos : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  have h1 : 1 < |x / (2 : ℝ) ^ k| := by
    rw [abs_div, abs_of_pos hpos, one_lt_div hpos]
    exact not_le.mp hc
  exact h (Work.KMTContract.kmtEta_zero h1.le)

/-- The periodised cutoff is supported in the arc `ℝ_{≤k}`. -/
theorem supportedInArc_periodize_etaCut (k : ℤ) :
    SupportedInArc k (periodize (etaCut Work.KMTContract.kmtEta k)) := by
  intro ξ hξ
  by_cases hk : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ k
  · refine ⟨Work.KMTAreas.A7.lift ξ, ?_, Work.KMTAreas.A7.lift_coe ξ⟩
    rw [realArc, Set.mem_Icc]
    have hmem := Work.KMTAreas.A7.lift_mem ξ
    rw [Set.mem_Ico] at hmem
    exact ⟨by linarith [hmem.1, hk], by linarith [hmem.2, hk]⟩
  · have hw : (2 : ℝ) ^ k < 1 / 2 := not_le.mp hk
    have hφ : ∀ x : ℝ, etaCut Work.KMTContract.kmtEta k x ≠ 0 → |x| ≤ (2 : ℝ) ^ k :=
      fun x hx => etaCut_kmtEta_support k hx
    refine ⟨Work.KMTAreas.A7.lift ξ, ?_, Work.KMTAreas.A7.lift_coe ξ⟩
    rw [realArc, Set.mem_Icc]
    have h : |Work.KMTAreas.A7.lift ξ| ≤ (2 : ℝ) ^ k :=
      hφ _ (by rwa [Work.KMTAreas.A7.periodize_eq_lift hw hφ] at hξ)
    exact ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩

/-- **The periodised Littlewood--Paley nesting**: `Φ_k · Φ_{k'} = Φ_{k'}` for `k' < k`, where
`Φ_k = periodize (etaCut kmtEta k)`. -/
theorem periodize_etaCut_mul_eq {k k' : ℤ} (hk' : k' < k) (hk : (2 : ℝ) ^ k ≤ 1 / 4) :
    periodize (etaCut Work.KMTContract.kmtEta k)
      * periodize (etaCut Work.KMTContract.kmtEta k') =
    periodize (etaCut Work.KMTContract.kmtEta k') := by
  have hk'_quarter : (2 : ℝ) ^ k' ≤ 1 / 4 := by
    have h1 : (2 : ℝ) ^ k' ≤ (2 : ℝ) ^ (k - 1) :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have h2 : (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k / 2 := by
      rw [zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]; ring
    rw [h2] at h1
    linarith
  have hsupp_k : ∀ x : ℝ, etaCut Work.KMTContract.kmtEta k x ≠ 0 → x ∈ realArc k := by
    intro x hx
    rw [realArc, Set.mem_Icc]
    have h := etaCut_kmtEta_support k hx
    exact ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩
  have hsupp_k' : ∀ x : ℝ, etaCut Work.KMTContract.kmtEta k' x ≠ 0 → x ∈ realArc k' := by
    intro x hx
    rw [realArc, Set.mem_Icc]
    have h := etaCut_kmtEta_support k' hx
    exact ⟨(abs_le.mp h).1, (abs_le.mp h).2⟩
  funext ξ
  simp only [Pi.mul_apply]
  by_cases h : periodize (etaCut Work.KMTContract.kmtEta k') ξ = 0
  · rw [h, mul_zero]
  · obtain ⟨x, hx, hxc⟩ := supportedInArc_periodize_etaCut k' ξ h
    have hx' : x ∈ realArc k := realArc_mono hk'.le hx
    have h1 : periodize (etaCut Work.KMTContract.kmtEta k) ξ
        = etaCut Work.KMTContract.kmtEta k x := by
      rw [← hxc]
      exact Work.KMTAreas.A7.periodizeEqSelfOfMemRealArc hk hsupp_k hx'
    have h2 : periodize (etaCut Work.KMTContract.kmtEta k') ξ
        = etaCut Work.KMTContract.kmtEta k' x := by
      rw [← hxc]
      exact Work.KMTAreas.A7.periodizeEqSelfOfMemRealArc hk'_quarter hsupp_k' hx
    rw [h1, h2]
    exact congrFun (etaCut_mul
      (η := Work.KMTContract.kmtEta)
      (fun x hx => Work.KMTContract.kmtEta_one hx)
      (fun x hx => Work.KMTContract.kmtEta_zero hx.le) hk') x

/-- Non-aliasing is monotone in the scale: finer arcs are easier. -/
theorem nonAliasing_mono {k k' : ℤ} (hk : k' ≤ k) {A : Finset Work.Analysis.IonescuWainger.Circle}
    (hA : NonAliasing k A) : NonAliasing k' A := by
  intro α hα β hβ θ hθ θ' hθ' heq
  exact hA α hα β hβ θ (realArc_mono hk hθ) θ' (realArc_mono hk hθ') heq

/-- **The nesting of the Ionescu--Wainger symbols at two different heights**: for `k' < k` and a
non-aliasing frequency set `A` at the *coarser* scale `k`,
`Σ_{α∈A} η_{≤k}(·-α) · Σ_{α∈A} η_{≤k'}(·-α) = Σ_{α∈A} η_{≤k'}(·-α)`.  This is the symbol form of
`kmtProj ρ l k ∘ kmtProj ρ l k' = kmtProj ρ l k'`. -/
theorem iwSymbolSet_periodize_etaCut_mul (ρ : ℝ) (l : ℕ) {k k' : ℤ} (hk' : k' < k)
    (hk : (2 : ℝ) ^ k ≤ 1 / 4)
    (hA : NonAliasing k (iwArithFreqs ρ l)) :
    iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))
      * iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k'))
    = iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k')) := by
  have hsym : periodize (etaCut Work.KMTContract.kmtEta k')
        * periodize (etaCut Work.KMTContract.kmtEta k)
      = periodize (etaCut Work.KMTContract.kmtEta k') := by
    rw [mul_comm]
    exact periodize_etaCut_mul_eq hk' hk
  have h := iwSymbolSet_mul (A := iwArithFreqs ρ l) (k := k') (k' := k) hk'.le
    (nonAliasing_mono hk'.le hA) hA
    (supportedInArc_periodize_etaCut k') (supportedInArc_periodize_etaCut k)
  rw [mul_comm (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k)))
        (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k'))),
    ← h, hsym]

/-- **The composition of two IW convolutions, AXIOM-CLEAN.**  This re-proves
`Work.KMTAreas.A7Hi.iwConv_comp` from the sorry-free coefficient engine
`A5.fourierCoeff_mul_eq_tsum_conv` (the paper's convolution theorem for Fourier coefficients of a
product, for `MemLp 2` factors with summable coefficients of one factor), together with the
reassociation `A7Hi.tsum_conv_conv`.  Unlike `iwConv_comp`, this statement has **no** `sorryAx` in
its proof closure. -/
theorem iwConv_comp_clean (A : Finset Work.Analysis.IonescuWainger.Circle)
    (Ψ₁ Ψ₂ Ψ₃ : Work.Analysis.IonescuWainger.Circle → ℂ)
    (h1 : MeasureTheory.MemLp (iwSymbolSet A Ψ₁) ⊤ circleMeasure)
    (h2 : MeasureTheory.MemLp (iwSymbolSet A Ψ₂) ⊤ circleMeasure)
    (hs1 : Summable (fun j : ℤ => fourierCoeff (iwSymbolSet A Ψ₁) j))
    (hs2 : Summable (fun j : ℤ => fourierCoeff (iwSymbolSet A Ψ₂) j))
    (hgate : ∀ ζ : Work.Analysis.IonescuWainger.Circle,
      iwSymbolSet A Ψ₁ ζ * iwSymbolSet A Ψ₂ ζ = iwSymbolSet A Ψ₃ ζ)
    (f : ℤ → ℂ) {B : ℝ} (hf : ∀ y : ℤ, ‖f y‖ ≤ B) :
    Work.Analysis.IWMultiplier.iwConv A Ψ₁ (Work.Analysis.IWMultiplier.iwConv A Ψ₂ f)
      = Work.Analysis.IWMultiplier.iwConv A Ψ₃ f := by
  have h12 : MeasureTheory.MemLp (iwSymbolSet A Ψ₁) 2 circleMeasure :=
    h1.mono_exponent le_top
  have h22 : MeasureTheory.MemLp (iwSymbolSet A Ψ₂) 2 circleMeasure :=
    h2.mono_exponent le_top
  have hK : ∀ m : ℤ, (∑' j : ℤ, fourierCoeff (iwSymbolSet A Ψ₁) j
        * fourierCoeff (iwSymbolSet A Ψ₂) (m - j)) = fourierCoeff (iwSymbolSet A Ψ₃) m := by
    intro m
    rw [← Work.KMTAreas.A5.fourierCoeff_mul_eq_tsum_conv h12 h22 hs1.norm m]
    have hcongr : fourierCoeff (fun ξ : Work.Analysis.IonescuWainger.Circle =>
        iwSymbolSet A Ψ₁ ξ * iwSymbolSet A Ψ₂ ξ) m
        = fourierCoeff (iwSymbolSet A Ψ₃) m := by
      simp only [fourierCoeff]
      exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ξ => by
        simp only [Pi.smul_apply]
        rw [hgate ξ]))
    exact hcongr
  funext n
  simp only [Work.Analysis.IWMultiplier.iwConv_apply, Work.Analysis.IWMultiplier.iwKernel,
    smul_eq_mul]
  change (∑' j : ℤ, fourierCoeff (iwSymbolSet A Ψ₁) j
        * (∑' i : ℤ, fourierCoeff (iwSymbolSet A Ψ₂) i * f (n - j - i)))
      = ∑' m : ℤ, fourierCoeff (iwSymbolSet A Ψ₃) m * f (n - m)
  rw [Work.KMTAreas.A7Hi.tsum_conv_conv (a := fun j : ℤ => fourierCoeff (iwSymbolSet A Ψ₁) j)
    (b := fun i : ℤ => fourierCoeff (iwSymbolSet A Ψ₂) i) (u := f) (C := B) hs1.norm hs2.norm hf n]
  exact tsum_congr (fun m => by rw [hK m])

/-- **The `kmtProj`-level nesting of the IW projections at two different heights, AXIOM-CLEAN.**
For `k' < k` (`k` the *coarser* cutoff), `kmtProj ρ l k ∘ kmtProj ρ l k' = kmtProj ρ l k'`: the
coarser projection is the identity on the range of the finer one.  Proved from
`iwConv_comp_clean` with `hgate := iwSymbolSet_periodize_etaCut_mul`, so its proof closure is free
of `sorryAx` (`#print axioms` reports `[propext, Classical.choice, Quot.sound]`). -/
theorem kmtProj_comp (ρ : ℝ) (l : ℕ) {k k' : ℤ} (hk' : k' < k) (hk : (2 : ℝ) ^ k ≤ 1 / 4)
    (hA : NonAliasing k (iwArithFreqs ρ l))
    (h1 : MeasureTheory.MemLp
      (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k)))
      ⊤ circleMeasure)
    (h2 : MeasureTheory.MemLp
      (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k')))
      ⊤ circleMeasure)
    (hs1 : Summable (fun j : ℤ => fourierCoeff
      (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))) j))
    (hs2 : Summable (fun j : ℤ => fourierCoeff
      (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k'))) j))
    (f : ℤ → ℂ) {B : ℝ} (hf : ∀ y : ℤ, ‖f y‖ ≤ B) :
    Work.KMTContract.kmtProj ρ l k (Work.KMTContract.kmtProj ρ l k' f)
      = Work.KMTContract.kmtProj ρ l k' f := by
  simpa only [Work.KMTContract.kmtProj] using
    iwConv_comp_clean (A := iwArithFreqs ρ l)
      (Ψ₁ := periodize (etaCut Work.KMTContract.kmtEta k))
      (Ψ₂ := periodize (etaCut Work.KMTContract.kmtEta k'))
      (Ψ₃ := periodize (etaCut Work.KMTContract.kmtEta k'))
      h1 h2 hs1 hs2
      (fun ζ => congrFun (iwSymbolSet_periodize_etaCut_mul ρ l hk' hk hA) ζ) f hf

/-- **The nesting at consecutive scales.**  With `T_m := kmtProj ρ l (-(m₀+m))`, the coarser
projection is the identity on the range of the finer one: `T_m ∘ T_{m'} = T_{m'}` for `m < m'`
(equivalently `T_m T_{m'} = T_{max(m,m')}`, since the two multipliers also commute — see
`iwOpSet_etaCut_comp` and the note in Notes §11).  This is `kmtProj_comp` reindexed by
`k := -(m₀+m)`, `k' := -(m₀+m')`, with `2^k ≤ 1/4` coming from `2 ≤ m₀ + m`. -/
theorem kmtProj_comp_consecutive (ρ : ℝ) (l : ℕ) (m₀ : ℕ) (hm₀ : 2 ≤ m₀) {m m' : ℕ}
    (hmm : m < m') (hA : NonAliasing (-(m₀ + m : ℤ)) (iwArithFreqs ρ l))
    (h1 : MeasureTheory.MemLp (iwSymbolSet (iwArithFreqs ρ l)
      (periodize (etaCut Work.KMTContract.kmtEta (-(m₀ + m : ℤ))))) ⊤ circleMeasure)
    (h2 : MeasureTheory.MemLp (iwSymbolSet (iwArithFreqs ρ l)
      (periodize (etaCut Work.KMTContract.kmtEta (-(m₀ + m' : ℤ))))) ⊤ circleMeasure)
    (hs1 : Summable (fun j : ℤ => fourierCoeff (iwSymbolSet (iwArithFreqs ρ l)
      (periodize (etaCut Work.KMTContract.kmtEta (-(m₀ + m : ℤ))))) j))
    (hs2 : Summable (fun j : ℤ => fourierCoeff (iwSymbolSet (iwArithFreqs ρ l)
      (periodize (etaCut Work.KMTContract.kmtEta (-(m₀ + m' : ℤ))))) j))
    (f : ℤ → ℂ) {B : ℝ} (hf : ∀ y : ℤ, ‖f y‖ ≤ B) :
    Work.KMTContract.kmtProj ρ l (-(m₀ + m : ℤ))
        (Work.KMTContract.kmtProj ρ l (-(m₀ + m' : ℤ)) f)
      = Work.KMTContract.kmtProj ρ l (-(m₀ + m' : ℤ)) f := by
  have hk : (2 : ℝ) ^ (-(m₀ + m : ℤ)) ≤ 1 / 4 := by
    have h2' : (-(m₀ + m : ℤ)) ≤ (-2 : ℤ) := by omega
    calc (2 : ℝ) ^ (-(m₀ + m : ℤ)) ≤ (2 : ℝ) ^ (-2 : ℤ) :=
          zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) h2'
      _ = 1 / 4 := by norm_num
  refine kmtProj_comp ρ l (k := -(m₀ + m : ℤ)) (k' := -(m₀ + m' : ℤ)) ?_ hk hA h1 h2 hs1 hs2 f hf
  omega

end Work.KMTAreas.A7G

namespace Work.KMTAreas.A7G


/-! ## The reduction of the target to the forward variational bound

The target `chainPartLowpass` is equivalent to the *forward* variational estimate

`‖ V^r_m (kmtProj ρ l (-(m₀+m)) g) ‖_{ℓᵖ} ≤ C ‖g‖_{ℓᵖ}`   (`C` independent of `l`, `m₀`),

provided the walk is *nested at the base level `1`* (`T_m ∘ T_1 = T_m` for `m ≥ 1` and
`T_0 ∘ T_1 = T_1`).  The point of the base level `1` (rather than `0`) is that the walk of
`f` and the walk of `T_1 f` then agree off the single index `0`, so they differ by a *one-point*
perturbation of size `‖T_0 f - T_1 f‖`, which is dominated by the square function. -/

/-- `lpf` at the base level `m₀ + j` and the index `n` is `lpf` at the base level `m₀` and the
index `n + j`. -/
theorem lpf_add_base (ρ : ℝ) (l m₀ j n : ℕ) (f : ℤ → ℂ) :
    Work.KMTAreas.A7Hi.lpf ρ l (m₀ + j) n f = Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + j) f := by
  simp only [Work.KMTAreas.A7Hi.lpf]
  congr 1
  push_cast
  ring

/-- The band-pass square function of the base level `m₀ + j` is dominated by that of the base
level `m₀`: its family of increments is a subfamily. -/
theorem sqFun_add_base_le (ρ : ℝ) (l m₀ j : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    Work.KMTAreas.A7Hi.sqFun ρ l (m₀ + j) f x ≤ Work.KMTAreas.A7Hi.sqFun ρ l m₀ f x := by
  unfold Work.KMTAreas.A7Hi.sqFun
  refine ENNReal.rpow_le_rpow ?_ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hshift : (fun n : ℕ => ‖Work.KMTAreas.A7Hi.lpf ρ l (m₀ + j) (n + 1) f x
        - Work.KMTAreas.A7Hi.lpf ρ l (m₀ + j) n f x‖ₑ ^ (2 : ℝ))
      = fun n : ℕ => (fun m : ℕ => ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (m + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ m f x‖ₑ ^ (2 : ℝ)) (n + j) := by
    funext n
    rw [lpf_add_base ρ l m₀ j (n + 1), lpf_add_base ρ l m₀ j n,
      show (n + 1) + j = n + j + 1 from by omega]
  rw [hshift]
  exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun n : ℕ => n + j)
    (fun a b hab => Nat.add_right_cancel hab)
    (fun m : ℕ => ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (m + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ m f x‖ₑ ^ (2 : ℝ))

/-- The `0`-th increment of the low-pass walk is dominated by the band-pass square function. -/
theorem enorm_zero_increment_le_sqFun (ρ : ℝ) (l m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x‖ₑ
      ≤ Work.KMTAreas.A7Hi.sqFun ρ l m₀ f x := by
  have hneg : Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x
      = -(Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x) := by ring
  have hsub : ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x‖ₑ
      = ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x‖ₑ := by
    rw [hneg, enorm_neg]
  rw [hsub]
  unfold Work.KMTAreas.A7Hi.sqFun
  have hterm : ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x‖ₑ
        ^ (2 : ℝ) ≤ ∑' n : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) f x
      - Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x‖ₑ ^ (2 : ℝ) :=
    ENNReal.le_tsum (f := fun n : ℕ => ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) f x
      - Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x‖ₑ ^ (2 : ℝ)) (0 : ℕ)
  calc ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x‖ₑ
      = (‖Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x‖ₑ
            ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) :=
        (ENNReal.rpow_rpow_inv (by norm_num)
          ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 0 f x‖ₑ).symm
    _ ≤ (∑' n : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) :=
        ENNReal.rpow_le_rpow hterm (by norm_num)
    _ = (∑' n : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← one_div]

/-- `C X + 2 Y ≤ B (X + Y)` when `C ≤ B` and `2 ≤ B`. -/
theorem ennr_two_le {C B : ℝ} (hCB : C ≤ B) (h2B : (2 : ℝ) ≤ B) (X Y : ENNReal) :
    ENNReal.ofReal C * X + 2 * Y ≤ ENNReal.ofReal B * (X + Y) := by
  have h2eq : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
  have h2 : (2 : ENNReal) ≤ ENNReal.ofReal B := by
    rw [h2eq]
    exact ENNReal.ofReal_le_ofReal h2B
  rw [mul_add]
  exact add_le_add (mul_le_mul_left (ENNReal.ofReal_le_ofReal hCB) X) (mul_le_mul_left h2 Y)

/-- `B (X + Y) + 4 X ≤ B' (X + Y)` when `B + 4 ≤ B'`. -/
theorem ennr_four_le {B B' : ℝ} (hB : 0 ≤ B) (hBB' : B + 4 ≤ B') (X Y : ENNReal) :
    ENNReal.ofReal B * (X + Y) + 4 * X ≤ ENNReal.ofReal B' * (X + Y) := by
  have h4eq : (4 : ENNReal) = ENNReal.ofReal 4 := by norm_num
  have h4 : (4 : ENNReal) ≤ ENNReal.ofReal B' := by
    rw [h4eq]
    exact ENNReal.ofReal_le_ofReal (le_trans (by linarith : (4 : ℝ) ≤ B + 4) hBB')
  have hXY : X ≤ X + Y :=
    le_trans (le_of_eq (add_zero X).symm) (add_le_add le_rfl zero_le)
  calc ENNReal.ofReal B * (X + Y) + 4 * X
      ≤ ENNReal.ofReal B * (X + Y) + ENNReal.ofReal 4 * (X + Y) := by
        refine add_le_add le_rfl ?_
        rw [h4eq]
        exact mul_le_mul_right hXY (ENNReal.ofReal 4)
    _ = (ENNReal.ofReal B + ENNReal.ofReal 4) * (X + Y) := (add_mul _ _ _).symm
    _ = ENNReal.ofReal (B + 4) * (X + Y) := by
        rw [← ENNReal.ofReal_add hB (by norm_num)]
    _ ≤ ENNReal.ofReal B' * (X + Y) := mul_le_mul_left (ENNReal.ofReal_le_ofReal hBB') (X + Y)

/-- The `1`-st increment of the low-pass walk is dominated by the square function. -/
theorem enorm_one_increment_le_sqFun (ρ : ℝ) (l m₀ : ℕ) (f : ℤ → ℂ) (x : ℤ) :
    ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 2 f x‖ₑ
      ≤ Work.KMTAreas.A7Hi.sqFun ρ l m₀ f x := by
  have hneg : Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 2 f x
      = -(Work.KMTAreas.A7Hi.lpf ρ l m₀ 2 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x) := by ring
  have hsub : ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 2 f x‖ₑ
      = ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ 2 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x‖ₑ := by
    rw [hneg, enorm_neg]
  rw [hsub]
  unfold Work.KMTAreas.A7Hi.sqFun
  have hterm : ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ 2 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x‖ₑ
        ^ (2 : ℝ) ≤ ∑' n : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) f x
      - Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x‖ₑ ^ (2 : ℝ) :=
    ENNReal.le_tsum (f := fun n : ℕ => ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) f x
      - Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x‖ₑ ^ (2 : ℝ)) (1 : ℕ)
  calc ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ 2 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x‖ₑ
      = (‖Work.KMTAreas.A7Hi.lpf ρ l m₀ 2 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x‖ₑ
            ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) :=
        (ENNReal.rpow_rpow_inv (by norm_num)
          ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ 2 f x - Work.KMTAreas.A7Hi.lpf ρ l m₀ 1 f x‖ₑ).symm
    _ ≤ (∑' n : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) :=
        ENNReal.rpow_le_rpow hterm (by norm_num)
    _ = (∑' n : ℕ, ‖Work.KMTAreas.A7Hi.lpf ρ l m₀ (n + 1) f x
          - Work.KMTAreas.A7Hi.lpf ρ l m₀ n f x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [← one_div]

/-- `C X + D Y ≤ B (X + Y)` for real coefficients with `C, D ≤ B`. -/
theorem ennr_coeff_le {C D B : ℝ} (hC : C ≤ B) (hD : D ≤ B) (X Y : ENNReal) :
    ENNReal.ofReal C * X + ENNReal.ofReal D * Y ≤ ENNReal.ofReal B * (X + Y) := by
  rw [mul_add]
  exact add_le_add (mul_le_mul_left (ENNReal.ofReal_le_ofReal hC) X)
    (mul_le_mul_left (ENNReal.ofReal_le_ofReal hD) Y)

/-- `2 Y + 2 (C Y) = ofReal (2 (1 + C)) Y` for `C ≥ 0`. -/
theorem two_mul_add_ofReal_mul (C : ℝ) (hC : 0 ≤ C) (Y : ENNReal) :
    (2 : ENNReal) * Y + 2 * (ENNReal.ofReal C * Y)
      = ENNReal.ofReal (2 * (1 + C)) * Y := by
  have hsum : (2 : ENNReal) + 2 * ENNReal.ofReal C = ENNReal.ofReal (2 * (1 + C)) := by
    have h2 : (2 : ENNReal) = ENNReal.ofReal 2 := by norm_num
    calc (2 : ENNReal) + 2 * ENNReal.ofReal C
        = ENNReal.ofReal 2 + ENNReal.ofReal 2 * ENNReal.ofReal C := by rw [h2]
      _ = ENNReal.ofReal 2 + ENNReal.ofReal (2 * C) := by
            rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = ENNReal.ofReal (2 + 2 * C) := by
            rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 2) (by linarith)]
      _ = ENNReal.ofReal (2 * (1 + C)) := by
            congr 1
            ring
  calc (2 : ENNReal) * Y + 2 * (ENNReal.ofReal C * Y)
      = (2 : ENNReal) * Y + (2 * ENNReal.ofReal C) * Y := by rw [mul_assoc]
    _ = ((2 : ENNReal) + 2 * ENNReal.ofReal C) * Y := (add_mul _ _ _).symm
    _ = ENNReal.ofReal (2 * (1 + C)) * Y := by rw [hsum]

theorem chainPartLowpass (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
    (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Cρ : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (l : ℕ) (m₀ : ℕ),
      Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l (-(m₀ : ℤ)) → ∀ f : ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.chainPart r
          (fun n : ℕ => Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x))
        p MeasureTheory.Measure.count
        ≤ ENNReal.ofReal B *
          (MeasureTheory.eLpNorm (fun x : ℤ => Work.KMTAreas.A7Hi.supPart r
              (fun n : ℕ => Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x))
            p MeasureTheory.Measure.count
           + MeasureTheory.eLpNorm (fun x : ℤ => (∑' n : ℕ,
                ‖Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + (((n + 1 : ℕ) : ℤ)))) f x
                  - Work.KMTContract.kmtProj ρ l (-((m₀ : ℤ) + ((n : ℕ) : ℤ))) f x‖ₑ ^ (2 : ℝ))
                ^ (1 / 2 : ℝ)) p MeasureTheory.Measure.count) := by sorry

end Work.KMTAreas.A7G
