/-
# The Bessel inequality for the §5 frequency pieces (`Work.KMTPlan.A6.besselF`)

This file proves the Bessel (almost-orthogonality) inequality for the §5 frequency pieces
`Fpiece (kmtPj ρ) 0 l₁ k₁ N f` of Krause--Mirek--Tao, in the "tail" form used by the §5
assembly: for a lacunary sequence `a` and a finite set `s` of indices satisfying
`logN (⌊a n⌋) ≥ max(l₁,k₁) + C 2^{ρl₁}`, the squared `ℓ²` norms of the pieces at the lacunary
scales `N = ⌊a n⌋` satisfy

  `∑_{n ∈ s} ‖F^{0,l₁,k₁}_{⌊a n⌋} f‖₂² ≤ B(Λ)² ‖f‖₂²`,

with a constant `B` depending only on the lacunarity `Λ`.

## The mechanism

The piece at scale `N` is the Fourier multiplier with the *shell* symbol
`DiSym ρ l₁ (k₁ - logN N)` (`BesselDefs.lean`): the Littlewood--Paley difference
`η_{≤k} - η_{≤k-1}` spread over the arithmetic frequencies `(ℚ/ℤ)_{l₁}` of height exactly `l₁`.
By Plancherel,

  `∑_{n∈s} ‖F_n f‖₂² = ∫⁻ ξ, (∑_{n∈s} ‖DiSym ρ l₁ (k₁ - logN ⌊a n⌋) ξ‖²) ‖𝓕f ξ‖²`,

and the pointwise factor is bounded by `2 · M(Λ)`, where `M(Λ)` bounds the number of lacunary
scales `⌊a n⌋` falling in a single dyadic window `[2^m, 2^{m+1})` (`lacunaryLevel`):

* at a fixed frequency `ξ`, the shells are non-zero at at most two scale *values* (the scales are
  separately non-aliasing, `DiSym_support` + `shellData_eq`, so two contributing scales force the
  same arithmetic frequency and the same distance `|θ|`, which is contained in at most two
  multiplicative annuli), and
* each scale value occurs at most `M(Λ)` times in `s` (lacunarity).

## Main tools used

* `DiSym_support`, `DiSym_norm_le`, `shellData_eq` — the structure of the shell symbol;
* `multiplierOfPlancherel` — Plancherel for the IW multiplier with a given symbol;
* `lacunaryLevel` — the counting of lacunary scales in a dyadic window;
* `finsetSum_sq_le_liminf` — the Fatou step passing from the truncated (`truncZ`) pieces to `f`;
* `Work.KMTAreas.A7.FpieceEqTm_of_bounded` — the identification of the piece with the multiplier.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.lacunaryLevel
import Submission.Work.KMTPlan.A6.multiplierOfPlancherel
import Submission.Work.KMTPlan.A6.finsetSum_sq_le_liminf
import Submission.Work.KMTPlan.A6.DiSym_support
import Submission.Work.KMTPlan.A6.DiSym_norm_le
import Submission.Work.KMTPlan.A6.shellData_eq
import Submission.Work.KMTContract.kmtProj_tendsto_truncZ
import Submission.Work.KMTAreas.A7.FpieceEqTm
import Submission.Port.Aesm

set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

noncomputable section

/-! ## Elementary API -/

/-- Non-aliasing is monotone in the frequency set. -/
theorem besselF_nonAliasing_mono {k : ℤ} {A B : Finset (AddCircle (1:ℝ))} (h : NonAliasing k A)
    (hBA : B ⊆ A) : NonAliasing k B :=
  fun α hα β hβ θ hθ θ' hθ' heq => h α (hBA hα) β (hBA hβ) θ hθ θ' hθ' heq

/-- The shell symbol `DiSym ρ l k` is bounded (hence in `L^∞` of the circle). -/
theorem besselF_DiSym_memLp (ρ : ℝ) (l : ℕ) (k : ℤ) : MemLp (DiSym ρ l k) ⊤ circleMeasure := by
  have h1 := Work.KMTAreas.A7.memLp_periodize_etaCut k
  have h2 := Work.KMTAreas.A7.memLp_periodize_etaCut (k - 1)
  exact Work.Analysis.IWMultiplier.memLp_iwSymbolSet _ (h1.sub h2)

/-- The `lintegral` of a finite sum of a.e.-measurable `ℝ≥0∞`-valued functions is the sum of the
`lintegral`s. -/
theorem besselF_lintegral_finsetSum_aemeasurable {ι α : Type*} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) {f : ι → α → ℝ≥0∞} (hf : ∀ i ∈ s, AEMeasurable (f i) μ) :
    ∫⁻ a, ∑ i ∈ s, f i a ∂μ = ∑ i ∈ s, ∫⁻ a, f i a ∂μ := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      have hfi : AEMeasurable (f i) μ := hf i (Finset.mem_insert_self i s)
      have hfs : ∀ j ∈ s, AEMeasurable (f j) μ := fun j hj => hf j (Finset.mem_insert_of_mem hj)
      calc ∫⁻ a, ∑ j ∈ insert i s, f j a ∂μ
          = ∫⁻ a, (f i a + ∑ j ∈ s, f j a) ∂μ :=
            lintegral_congr (fun a => Finset.sum_insert hi)
        _ = (∫⁻ a, f i a ∂μ) + (∫⁻ a, ∑ j ∈ s, f j a ∂μ) := lintegral_add_left' hfi _
        _ = (∫⁻ a, f i a ∂μ) + ∑ j ∈ s, ∫⁻ a, f j a ∂μ := by rw [ih hfs]
        _ = ∑ j ∈ insert i s, ∫⁻ a, f j a ∂μ := by rw [Finset.sum_insert hi]

/-- `eLpNorm` of an `L²` class is the `ℝ≥0∞`-norm of the representative. -/
theorem besselF_eLpNorm_coeFn_Lp_two {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (h : Lp ℂ 2 μ) : eLpNorm (⇑h) 2 μ = ENNReal.ofReal ‖h‖ := by
  rw [MeasureTheory.Lp.norm_def, ENNReal.ofReal_toReal]
  exact (ne_top_of_lt h.property)

/-- The square of the `L²` seminorm is the `lintegral` of the squared extended norm. -/
theorem besselF_eLpNorm_sq_lintegral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (g : α → ℂ) (hg : AEStronglyMeasurable g μ := by pw_aesm) :
    (eLpNorm g 2 μ) ^ (2:ℕ) = ∫⁻ ξ, ‖g ξ‖ₑ ^ (2:ℕ) ∂μ := by
  rw [← ENNReal.rpow_natCast]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := hg) (by norm_num) (by norm_num)]
  rw [show ENNReal.toReal (2:ℝ≥0∞) = (2:ℝ) from by norm_num]
  rw [← ENNReal.rpow_mul, show (1 / (2:ℝ)) * ((2:ℕ):ℝ) = 1 by norm_num, ENNReal.rpow_one]
  exact lintegral_congr (fun ξ => by
    rw [show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast])

/-- **Plancherel for the Fourier transform of `ℤ`**: the squared `ℓ²` norm of `F` is the
`lintegral` of the squared modulus of its Fourier transform on the circle. -/
theorem besselF_fourierZ_sq_lintegral (F : L2Z) :
    (eLpNorm (⇑F) 2 Measure.count) ^ (2 : ℕ)
      = ∫⁻ ξ, ‖(fourierZ F) ξ‖ₑ ^ (2 : ℕ) ∂ circleMeasure := by
  have h1 : eLpNorm (⇑F) 2 Measure.count = ENNReal.ofReal ‖F‖ :=
    Work.Analysis.IWMultiplier.eLpNorm_two_count_eq_ofReal_lpNorm (⇑F) (lp.memℓp F)
  have h2 : eLpNorm (⇑(fourierZ F)) 2 circleMeasure = ENNReal.ofReal ‖F‖ := by
    rw [besselF_eLpNorm_coeFn_Lp_two (fourierZ F), (fourierZ.norm_map F)]
  rw [h1.trans h2.symm, besselF_eLpNorm_sq_lintegral _ (Lp.aestronglyMeasurable _)]

/-! ## The pointwise multiplicity bound -/

/-- **The pointwise multiplicity bound.**  At a fixed frequency `ξ`, at most two scale *values*
can contribute to a family of Littlewood--Paley shells whose scales are `≤ K` and separately
non-aliasing, and each scale value can occur at most `M` times.  Hence the sum of the squares of
the symbol values is at most `2M`. -/
theorem besselF_pointwise_le {A : Finset (AddCircle (1:ℝ))} {K : ℤ}
    (hNA : ∀ k : ℤ, k ≤ K → NonAliasing k A)
    {s : Finset ℕ} {c : ℕ → ℤ} (hc : ∀ n ∈ s, c n ≤ K)
    {M : ℕ} (hcount : ∀ m : ℤ, (s.filter (fun n => c n = m)).card ≤ M)
    {ξ : AddCircle (1:ℝ)} {w : ℕ → ℂ}
    (hsup : ∀ n ∈ s, w n ≠ 0 → ∃ α ∈ A, ∃ θ : ℝ, (θ : AddCircle (1:ℝ)) = ξ - α ∧
        (2:ℝ)^(c n - 2) < |θ| ∧ |θ| < (2:ℝ)^(c n))
    (hb : ∀ n ∈ s, ‖w n‖ ≤ 1) :
    ∑ n ∈ s, ‖w n‖ₑ ^ (2 : ℕ) ≤ ((2 * M : ℕ) : ℝ≥0∞) := by
  classical
  set S : Finset ℕ := s.filter (fun n => w n ≠ 0) with hS
  have hsum : ∑ n ∈ s, ‖w n‖ₑ ^ (2 : ℕ) = ∑ n ∈ S, ‖w n‖ₑ ^ (2 : ℕ) := by
    rw [hS]
    exact (Finset.sum_filter_of_ne (p := fun n => w n ≠ 0)
      (f := fun n => ‖w n‖ₑ ^ (2 : ℕ)) (fun x _ hx => by
        intro hw0; rw [hw0] at hx; simp at hx)).symm
  have hle : ∑ n ∈ S, ‖w n‖ₑ ^ (2 : ℕ) ≤ ((S.card : ℕ) : ℝ≥0∞) := by
    calc ∑ n ∈ S, ‖w n‖ₑ ^ (2 : ℕ) ≤ ∑ _n ∈ S, (1 : ℝ≥0∞) := by
          refine Finset.sum_le_sum (fun n hn => ?_)
          have h1 : ‖w n‖ₑ ≤ (1 : ℝ≥0∞) := by
            rw [← ofReal_norm,
              show (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) from by norm_num]
            exact ENNReal.ofReal_le_ofReal (hb n (Finset.mem_filter.mp hn).1)
          calc ‖w n‖ₑ ^ (2 : ℕ) ≤ 1 ^ (2 : ℕ) := ENNReal.pow_le_pow_left h1
            _ = 1 := one_pow 2
      _ = ((S.card : ℕ) : ℝ≥0∞) := by simp
  have hcard : S.card ≤ 2 * M := by
    rcases S.eq_empty_or_nonempty with hemp | hne
    · rw [hemp]; simp
    · obtain ⟨n₀, hn₀, hmin⟩ := Finset.exists_min_image S c hne
      have hn₀s : n₀ ∈ s := (Finset.mem_filter.mp hn₀).1
      have hw₀ : w n₀ ≠ 0 := (Finset.mem_filter.mp hn₀).2
      have hsub : S ⊆ (s.filter (fun n => c n = c n₀))
          ∪ (s.filter (fun n => c n = c n₀ + 1)) := by
        intro n hn
        have hns : n ∈ s := (Finset.mem_filter.mp hn).1
        have hwn : w n ≠ 0 := (Finset.mem_filter.mp hn).2
        have h1 : c n₀ ≤ c n := hmin n hn
        have h2 : c n ≤ c n₀ + 1 := by
          by_contra hcon
          push_neg at hcon
          have hge : c n₀ + 2 ≤ c n := by omega
          obtain ⟨α₀, hα₀, θ₀, hθ₀⟩ := hsup n₀ hn₀s hw₀
          obtain ⟨α₁, hα₁, θ₁, hθ₁⟩ := hsup n hns hwn
          obtain ⟨hθ₀lo, hθ₀hi⟩ := hθ₀.2
          obtain ⟨hθ₁lo, hθ₁hi⟩ := hθ₁.2
          set x : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val with hxdef
          have hxξ : ((x : ℝ) : AddCircle (1:ℝ)) = ξ := AddCircle.coe_equivIco
          have hξ₀ : α₀ + (θ₀ : AddCircle (1:ℝ)) = (x : AddCircle (1:ℝ)) := by
            rw [hxξ, hθ₀.1]; abel
          have hξ₁ : α₁ + (θ₁ : AddCircle (1:ℝ)) = (x : AddCircle (1:ℝ)) := by
            rw [hxξ, hθ₁.1]; abel
          obtain ⟨heqα, heqθ⟩ := shellData_eq (hNA K le_rfl) (hc n₀ hn₀s) (hc n hns)
            hα₀ hα₁ hθ₀lo hθ₀hi hθ₁lo hθ₁hi hξ₀ hξ₁
          have hlt : (2:ℝ)^(c n - 2) < (2:ℝ)^(c n₀) := by
            calc (2:ℝ)^(c n - 2) < |θ₁| := hθ₁lo
              _ = |θ₀| := by rw [heqθ]
              _ < (2:ℝ)^(c n₀) := hθ₀hi
          have hmono : (2:ℝ)^(c n₀) ≤ (2:ℝ)^(c n - 2) :=
            zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by omega)
          linarith
        rcases lt_or_eq_of_le h1 with hlt | heq
        · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨hns, by omega⟩))
        · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨hns, heq.symm⟩))
      calc S.card ≤ ((s.filter (fun n => c n = c n₀))
              ∪ (s.filter (fun n => c n = c n₀ + 1))).card := Finset.card_le_card hsub
        _ ≤ (s.filter (fun n => c n = c n₀)).card
              + (s.filter (fun n => c n = c n₀ + 1)).card := Finset.card_union_le _ _
        _ ≤ M + M := by
            have h₁ := hcount (c n₀)
            have h₂ := hcount (c n₀ + 1)
            omega
        _ = 2 * M := by ring
  calc ∑ n ∈ s, ‖w n‖ₑ ^ (2 : ℕ) = ∑ n ∈ S, ‖w n‖ₑ ^ (2 : ℕ) := hsum
    _ ≤ ((S.card : ℕ) : ℝ≥0∞) := hle
    _ ≤ ((2 * M : ℕ) : ℝ≥0∞) := by exact_mod_cast hcard

/-! ## The identification of the piece with the IW multiplier -/

/-- **The §5 frequency piece is the Ionescu--Wainger multiplier with symbol `DiSym`**, for
finitely supported (hence bounded) input. -/
theorem besselF_piece_id (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l₁ k₁ : ℕ} (hk₁ : 1 ≤ k₁)
    {f : ℤ → ℂ} (hf : (Function.support f).Finite)
    (F : L2Z) (hF : ⇑F = f) (N : ℕ) :
    Work.Analysis.EndVar.Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁ : ℤ) N f
      = ⇑(multiplierOf (DiSym ρ l₁ ((k₁ : ℤ) - Work.Analysis.EndVar.logN N))
          (besselF_DiSym_memLp ρ l₁ _) F) := by
  have hb : ∀ m : ℤ, ‖f m‖ ≤ ∑ j ∈ hf.toFinset, ‖f j‖ := by
    intro m
    by_cases hm : m ∈ hf.toFinset
    · exact Finset.single_le_sum (fun _ _ => norm_nonneg _) hm
    · have h0 : f m = 0 := by
        by_contra hne
        exact hm (hf.mem_toFinset.mpr hne)
      rw [h0, norm_zero]
      exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  rw [Work.KMTAreas.A7.FpieceEqTm_of_bounded hρ hρ1 l₁ k₁ N f hb]
  have hsym : Work.KMTAreas.A7.pieceSymF k₁ N
      = fun θ : ℝ => etaCut Work.KMTContract.kmtEta ((k₁:ℤ) - Work.Analysis.EndVar.logN N) θ
          - etaCut Work.KMTContract.kmtEta ((k₁:ℤ) - Work.Analysis.EndVar.logN N - 1) θ := by
    funext θ
    simp only [Work.KMTAreas.A7.pieceSymF, if_neg (by omega : ¬ k₁ = 0)]
    ring_nf
  rw [Work.KMTAreas.A7.Tm, hsym, Work.KMTAreas.A7.periodize_sub_etaCut]
  exact (Work.Analysis.IWMultiplier.iwConv_eq_iwOpSet (kmtSet ρ l₁)
    (periodize (etaCut Work.KMTContract.kmtEta ((k₁:ℤ) - Work.Analysis.EndVar.logN N))
      - periodize (etaCut Work.KMTContract.kmtEta ((k₁:ℤ) - Work.Analysis.EndVar.logN N - 1)))
    (besselF_DiSym_memLp ρ l₁ _) f hf F hF).symm

/-! ## The Bessel inequality -/

/-- **The Bessel inequality for finitely supported `f`.** -/
theorem besselF_finsupp (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l₁ k₁ : ℕ} (hk₁ : 1 ≤ k₁)
    {a : ℕ → ℝ≥0} {K : ℤ} {s : Finset ℕ} {f : ℤ → ℂ} (hf : (Function.support f).Finite)
    (hNA : ∀ k : ℤ, k ≤ K → NonAliasing k (iwArithFreqs ρ l₁))
    (hK2 : (2:ℝ)^(K+1) < 1)
    (hc : ∀ n ∈ s, ((k₁:ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ K)
    {M : ℕ} (hcount : ∀ m : ℤ,
        (s.filter (fun n => (k₁:ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)) = m)).card ≤ M) :
    ∑ n ∈ s, (eLpNorm (Work.Analysis.EndVar.Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁:ℤ)
        (Nat.floor (a n)) f) 2 Measure.count) ^ (2:ℕ)
      ≤ ((2 * M : ℕ) : ℝ≥0∞) * (eLpNorm f 2 Measure.count) ^ (2:ℕ) := by
  classical
  set F : L2Z := ⟨f, Work.Analysis.IWMultiplier.memLp_of_finiteSupport f hf⟩ with hFdef
  have hF : ⇑F = f := rfl
  have key : ∀ n ∈ s, (eLpNorm (Work.Analysis.EndVar.Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁:ℤ)
        (Nat.floor (a n)) f) 2 Measure.count) ^ (2:ℕ)
      = ∫⁻ ξ, ‖DiSym ρ l₁ ((k₁:ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) ξ‖ₑ ^ (2:ℕ)
          * ‖(fourierZ F) ξ‖ₑ ^ (2:ℕ) ∂circleMeasure := by
    intro n hn
    have hm := besselF_DiSym_memLp ρ l₁ ((k₁:ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)))
    rw [besselF_piece_id ρ hρ hρ1 hk₁ hf F hF (Nat.floor (a n))]
    exact multiplierOfPlancherel _ hm F
  have hscale : ∀ n ∈ s, (2:ℝ)^(((k₁:ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) + 1) < 1 := by
    intro n hn
    exact lt_of_le_of_lt
      (zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) (by have := hc n hn; omega)) hK2
  have hAEM2 : AEMeasurable (fun ξ : AddCircle (1:ℝ) =>
      ‖(fourierZ F) ξ‖ₑ ^ (2:ℕ)) circleMeasure :=
    ((MeasureTheory.Lp.stronglyMeasurable (fourierZ F)).measurable.enorm).aemeasurable.pow_const 2
  have hAEM : ∀ n : ℕ, AEMeasurable (fun ξ : AddCircle (1:ℝ) =>
      ‖DiSym ρ l₁ ((k₁:ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) ξ‖ₑ ^ (2:ℕ)
        * ‖(fourierZ F) ξ‖ₑ ^ (2:ℕ)) circleMeasure := by
    intro n
    exact (((besselF_DiSym_memLp ρ l₁ _).aestronglyMeasurable.aemeasurable.enorm).pow_const 2).mul hAEM2
  have hpt : ∀ ξ : AddCircle (1:ℝ),
      ∑ n ∈ s, ‖DiSym ρ l₁ ((k₁:ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) ξ‖ₑ ^ (2:ℕ)
        ≤ ((2*M : ℕ) : ℝ≥0∞) := by
    intro ξ
    refine besselF_pointwise_le (K := K) (ξ := ξ) hNA hc hcount ?_ ?_
    · intro n hn hne
      obtain ⟨α, hα, θ, hθ⟩ := DiSym_support ρ l₁ _ (hscale n hn) hne
      exact ⟨α, kmtSet_subset ρ l₁ hα, θ, hθ⟩
    · intro n hn
      exact DiSym_norm_le ρ l₁ _ (hscale n hn)
        (besselF_nonAliasing_mono (hNA _ (hc n hn)) (kmtSet_subset ρ l₁)) ξ
  calc ∑ n ∈ s, (eLpNorm (Work.Analysis.EndVar.Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁:ℤ)
          (Nat.floor (a n)) f) 2 Measure.count) ^ (2:ℕ)
      = ∑ n ∈ s, ∫⁻ ξ, ‖DiSym ρ l₁ ((k₁:ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) ξ‖ₑ ^ (2:ℕ)
          * ‖(fourierZ F) ξ‖ₑ ^ (2:ℕ) ∂circleMeasure :=
        Finset.sum_congr rfl key
    _ = ∫⁻ ξ, ∑ n ∈ s, ‖DiSym ρ l₁ ((k₁:ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) ξ‖ₑ ^ (2:ℕ)
          * ‖(fourierZ F) ξ‖ₑ ^ (2:ℕ) ∂circleMeasure :=
        (besselF_lintegral_finsetSum_aemeasurable s (fun n _ => hAEM n)).symm
    _ = ∫⁻ ξ, (∑ n ∈ s, ‖DiSym ρ l₁ ((k₁:ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) ξ‖ₑ ^ (2:ℕ))
          * ‖(fourierZ F) ξ‖ₑ ^ (2:ℕ) ∂circleMeasure := by
        refine lintegral_congr (fun ξ => ?_)
        rw [Finset.sum_mul]
    _ ≤ ∫⁻ ξ, ((2*M : ℕ) : ℝ≥0∞) * ‖(fourierZ F) ξ‖ₑ ^ (2:ℕ)
          ∂circleMeasure := by
        refine lintegral_mono_ae (Filter.Eventually.of_forall (fun ξ => ?_))
        exact mul_le_mul_of_nonneg_right (hpt ξ) bot_le
    _ = ((2*M : ℕ) : ℝ≥0∞) * ∫⁻ ξ, ‖(fourierZ F) ξ‖ₑ ^ (2:ℕ)
          ∂circleMeasure := lintegral_const_mul'' _ hAEM2
    _ = ((2*M : ℕ) : ℝ≥0∞) * (eLpNorm f 2 Measure.count) ^ (2:ℕ) := by
        rw [besselF_fourierZ_sq_lintegral F]

/-- **The Bessel inequality for general `f ∈ ℓ²`**, by Fatou along the truncations `truncZ K f`. -/
theorem besselF_general (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l₁ k₁ : ℕ} (hk₁ : 1 ≤ k₁)
    {a : ℕ → ℝ≥0} {K : ℤ} {s : Finset ℕ} {f : ℤ → ℂ} (hf : MemLp f 2 Measure.count)
    (hNA : ∀ k : ℤ, k ≤ K → NonAliasing k (iwArithFreqs ρ l₁))
    (hK2 : (2:ℝ)^(K+1) < 1)
    (hc : ∀ n ∈ s, ((k₁:ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ K)
    {M : ℕ} (hcount : ∀ m : ℤ,
        (s.filter (fun n => (k₁:ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)) = m)).card ≤ M) :
    ∑ n ∈ s, (eLpNorm (Work.Analysis.EndVar.Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁:ℤ)
        (Nat.floor (a n)) f) 2 Measure.count) ^ (2:ℕ)
      ≤ ((2 * M : ℕ) : ℝ≥0∞) * (eLpNorm f 2 Measure.count) ^ (2:ℕ) := by
  have hkmt : ∀ (l : ℕ) (c : ℤ) (x : ℤ), Filter.Tendsto (fun K' : ℕ =>
      Work.KMTContract.kmtProj ρ l c (Work.KMTContract.truncZ K' f) x) Filter.atTop
      (nhds (Work.KMTContract.kmtProj ρ l c f x)) := fun l c x =>
    Work.KMTContract.kmtProj_tendsto_truncZ ρ l c (Work.KMTContract.kmtKernel_decay ρ l c)
      (by norm_num) hf x
  have hpiece : ∀ (l : ℕ) (c : ℤ) (x : ℤ), Filter.Tendsto (fun K' : ℕ =>
      Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c
        (Work.KMTContract.truncZ K' f) x) Filter.atTop
      (nhds (Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c f x)) := by
    intro l c x
    by_cases hl : l = 0
    · subst hl
      have h0 : Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) 0 c
          = Work.KMTContract.kmtProj ρ 0 c := by
        funext g n
        simp [Work.Analysis.EndVar.piExact, Work.KMTContract.kmtPj_proj]
      rw [h0]
      exact hkmt 0 c x
    · have h0 : Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l c
          = fun g => Work.KMTContract.kmtProj ρ l c g - Work.KMTContract.kmtProj ρ (l - 1) c g := by
        funext g n
        simp [Work.Analysis.EndVar.piExact, if_neg hl, Work.KMTContract.kmtPj_proj]
      rw [h0]
      exact (hkmt l c x).sub (hkmt (l - 1) c x)
  have hFp : ∀ (N : ℕ) (g : ℤ → ℂ), Work.Analysis.EndVar.Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁:ℤ) N g
      = Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l₁ (-(Work.Analysis.EndVar.logN N) + (k₁:ℤ)) g
        - Work.Analysis.EndVar.piExact (Work.KMTContract.kmtPj ρ) l₁
            (-(Work.Analysis.EndVar.logN N) + ((k₁:ℤ) - 1)) g := by
    intro N g
    simp only [Work.Analysis.EndVar.Fpiece, Work.Analysis.EndVar.piece]
    split_ifs with h
    · exact absurd h (by omega)
    · rfl
  have hlim : ∀ n ∈ s, ∀ x : ℤ, Filter.Tendsto (fun K' : ℕ =>
      Work.Analysis.EndVar.Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁:ℤ)
        (Nat.floor (a n)) (Work.KMTContract.truncZ K' f) x) Filter.atTop
      (nhds (Work.Analysis.EndVar.Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁:ℤ)
        (Nat.floor (a n)) f x)) := by
    intro n hn x
    have h := (hpiece l₁ (-(Work.Analysis.EndVar.logN (Nat.floor (a n))) + (k₁:ℤ)) x).sub
      (hpiece l₁ (-(Work.Analysis.EndVar.logN (Nat.floor (a n))) + ((k₁:ℤ) - 1)) x)
    simpa only [hFp, Pi.sub_apply] using h
  refine (finsetSum_sq_le_liminf hlim).trans ?_
  refine Filter.liminf_le_of_frequently_le'
    (Filter.Eventually.frequently (Filter.eventually_atTop.mpr ⟨0, fun K' _ => ?_⟩))
  have hfsupp : (Function.support (Work.KMTContract.truncZ K' f)).Finite := by
    refine Set.Finite.subset (Set.finite_Icc (-(K':ℤ)) (K':ℤ)) (fun x hx => ?_)
    simp only [Function.mem_support] at hx
    rw [Set.mem_Icc]
    by_contra hcon
    rw [not_and_or] at hcon
    exact hx (Work.KMTContract.truncZ_of_gt (by
      rcases hcon with h | h
      · rw [not_le] at h
        exact lt_of_lt_of_le (by omega) (neg_le_abs x)
      · rw [not_le] at h
        exact lt_of_lt_of_le h (le_abs_self x)))
  refine (besselF_finsupp ρ hρ hρ1 hk₁ (f := Work.KMTContract.truncZ K' f)
    hfsupp hNA hK2 hc hcount).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (bot_le)
  have hpt : ∀ x : ℤ, ‖Work.KMTContract.truncZ K' f x‖ ≤ ‖f x‖ := by
    intro x
    by_cases hx : |x| ≤ (K' : ℤ)
    · rw [Work.KMTContract.truncZ_of_le hx]
    · rw [Work.KMTContract.truncZ_of_gt (not_le.mp hx), norm_zero]; positivity
  exact ENNReal.pow_le_pow_left (eLpNorm_mono (hf := by pw_aesm) hpt)

/-! ## The main statement -/

theorem besselF (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ (B : ℝ≥0 → ℝ≥0) (C : ℝ), 0 < C ∧
      ∀ (l₁ k₁ : ℕ), 1 ≤ k₁ → ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0),
      1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      ∀ (s : Finset ℕ) (f : ℤ → ℂ), MemLp f 2 Measure.count →
      (∀ n ∈ s, ((max l₁ k₁ : ℕ) : ℝ) + C * (2 : ℝ) ^ (ρ * (l₁ : ℝ)) ≤
          ((Work.Analysis.EndVar.logN (Nat.floor (a n)) : ℤ) : ℝ)) →
      ∑ n ∈ s, (eLpNorm (Work.Analysis.EndVar.Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁ : ℤ)
            (Nat.floor (a n)) f) 2 Measure.count) ^ (2 : ℕ)
        ≤ ((B Λ : ℝ≥0) : ℝ≥0∞) ^ (2 : ℕ) * (eLpNorm f 2 Measure.count) ^ (2 : ℕ) := by
  obtain ⟨Cρ, _hCρpos, hNA₁⟩ := exists_goodMajorArcs_nonAliasing hρ
  obtain ⟨M, hM⟩ := lacunaryLevel
  refine ⟨fun Λ => ((2 * M Λ + 1 : ℕ) : ℝ≥0), max Cρ 2, by positivity, ?_⟩
  intro l₁ k₁ hk₁ a Λ hΛ ha ha1 s f hf htail
  set Cc : ℝ := max Cρ 2 with hCc
  have hCc2 : 2 ≤ Cc := by rw [hCc]; exact le_max_right _ _
  have hCcρ : Cρ ≤ Cc := by rw [hCc]; exact le_max_left _ _
  set K : ℤ := ⌊-(Cc * (2:ℝ)^(ρ * (l₁:ℝ)))⌋ with hK
  have hgood : ∀ k : ℤ, k ≤ K → GoodMajorArcs ρ Cc l₁ k := by
    intro k hk
    have h1 : (k:ℝ) ≤ (K:ℝ) := by exact_mod_cast hk
    have h2 : (K:ℝ) ≤ -Cc * (2:ℝ)^(ρ*(l₁:ℝ)) := by
      rw [hK]
      have := Int.floor_le (-(Cc * (2:ℝ)^(ρ*(l₁:ℝ))))
      linarith
    exact le_trans h1 h2
  have hNA : ∀ k : ℤ, k ≤ K → NonAliasing k (iwArithFreqs ρ l₁) := by
    intro k hk
    refine hNA₁ l₁ k ?_
    have h := hgood k hk
    have hle : -Cc * (2:ℝ)^(ρ*(l₁:ℝ)) ≤ -Cρ * (2:ℝ)^(ρ*(l₁:ℝ)) := by
      have hpos : (0:ℝ) ≤ (2:ℝ)^(ρ*(l₁:ℝ)) := by positivity
      nlinarith [hCcρ, hpos]
    exact le_trans h hle
  have hK2 : (2:ℝ)^(K+1) < 1 :=
    Work.Analysis.IWMultiplier.two_pow_succ_lt_one_of_goodMajorArcs (hgood K le_rfl) hCc2 hρ
  have hc : ∀ n ∈ s, ((k₁:ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ K := by
    intro n hn
    refine Int.le_floor.mpr ?_
    have ht := htail n hn
    rw [Int.cast_sub, Int.cast_natCast]
    have hmax : ((k₁:ℕ):ℝ) ≤ ((max l₁ k₁ : ℕ) : ℝ) := by exact_mod_cast le_max_right l₁ k₁
    linarith
  have hcount : ∀ m : ℤ, (s.filter (fun n =>
      (k₁:ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)) = m)).card ≤ M Λ := by
    intro m
    have hfil : (s.filter (fun n =>
        (k₁:ℤ) - Work.Analysis.EndVar.logN (Nat.floor (a n)) = m))
        = (s.filter (fun n => Work.Analysis.EndVar.logN (Nat.floor (a n)) = (k₁:ℤ) - m)) := by
      ext n
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by omega⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by omega⟩
    rw [hfil]
    exact hM a Λ hΛ ha ha1 ((k₁:ℤ) - m) s
  refine (besselF_general ρ hρ hρ1 hk₁ hf hNA hK2 hc hcount).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ bot_le
  have hnat : 2 * M Λ ≤ (2 * M Λ + 1)^2 := by nlinarith
  have hcoe : ((2 * M Λ : ℕ) : ℝ≥0∞) ≤ ((2 * M Λ + 1 : ℕ) : ℝ≥0∞) ^ (2:ℕ) := by
    rw [show (((2 * M Λ + 1 : ℕ) : ℝ≥0∞)) ^ (2:ℕ) = (((2 * M Λ + 1)^2 : ℕ) : ℝ≥0∞) from by
      push_cast; ring]
    exact_mod_cast hnat
  have hB : ((((2 * M Λ + 1 : ℕ) : ℝ≥0)) : ℝ≥0∞) = ((2 * M Λ + 1 : ℕ) : ℝ≥0∞) := by
    push_cast; rfl
  rw [hB]
  exact hcoe

end

end Work.KMTPlan.A6
