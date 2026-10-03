/-
# The `S`-average step of Proposition `lip-2`, general form (`Work.KMTAreas.A4.lip2GenSavg`)

Krause--Mirek--Tao, §5.2.  The main-case expansion of Proposition `lip-2` writes the pairing of
the second dual function `Ã*_N(h,g) = AhalfTranspose N P h g` with a function `F` whose
`ℤ`-Fourier transform is supported in a single arc of radius `1/(2M)` around `γ` as

  `⟨Ã*_N(h,g), F⟩ = ∑_s lip2Inner s`,   `lip2Inner s = ∑_y h y · F (y+s) · lip2Avg N P M γ g s y`

(`Work.KMTAreas.A4.lip2WindowExpansion`).  If the pairing is large (`≥ ε N^d`) and the tail of the
`s`-sum beyond `|s| ≤ S` is at most half of it, then some *single* shift `|s| ≤ S` already carries
a large part of the pairing.  Cauchy--Schwarz in `y` and the `ℓ²`-Plancherel identity for the
windowed average (`Work.KMTAreas.A4.lip2PlancherelIcc`) convert that into the lower bound

  `ε² N^{2d+2} ≤ C · S² · ‖F‖_∞ · ‖F‖_{ℓ¹} · ∫₀¹ ‖kmtFhat g t‖² ‖winSumIcc M γ t P s a b‖²`

with `a = N/2+1`, `b = N`; here `C = 36` works.  This is the input of the `Ω`-mass / inverse Weyl
steps of `Work.KMTAreas.A4.lip2Main`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2InnerSummable
import Submission.Work.KMTAreas.A4.sqTsumMulLe

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-! ## The reindexing of the summation interval `Ioc (N/2) N` -/

/-- The integers `N/2 + 1 ≤ n ≤ N` are exactly the images of the naturals `N/2 < n ≤ N`. -/
theorem Icc_eq_image_Ioc (N : ℕ) :
    Finset.Icc ((N / 2 + 1 : ℕ) : ℤ) (N : ℤ)
      = (Finset.Ioc (N / 2) N).image (fun n : ℕ => (n : ℤ)) := by
  ext x
  simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_Ioc]
  constructor
  · rintro ⟨h1, h2⟩
    have hx0 : 0 ≤ x := by
      have h0 : (0 : ℤ) ≤ ((N / 2 + 1 : ℕ) : ℤ) := by positivity
      linarith
    refine ⟨x.toNat, ⟨?_, ?_⟩, Int.toNat_of_nonneg hx0⟩
    · have h3 : ((N / 2 : ℕ) : ℤ) + 1 ≤ x := by
        have h4 : ((N / 2 + 1 : ℕ) : ℤ) = ((N / 2 : ℕ) : ℤ) + 1 := by push_cast; ring
        linarith
      have h5 : ((N / 2 : ℕ) : ℤ) < (x.toNat : ℤ) := by
        rw [Int.toNat_of_nonneg hx0]; linarith
      exact_mod_cast h5
    · have h5 : (x.toNat : ℤ) ≤ (N : ℤ) := by
        rw [Int.toNat_of_nonneg hx0]; linarith
      exact_mod_cast h5
  · rintro ⟨n, ⟨hn1, hn2⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · have h : N / 2 + 1 ≤ n := hn1
      exact_mod_cast h
    · exact_mod_cast hn2

/-- The reindexing of a sum over the upper half of the shifts. -/
theorem sum_Icc_eq_sum_Ioc (N : ℕ) (φ : ℤ → ℂ) :
    (∑ n ∈ Finset.Icc ((N / 2 + 1 : ℕ) : ℤ) (N : ℤ), φ n)
      = ∑ n ∈ Finset.Ioc (N / 2) N, φ (n : ℤ) := by
  rw [Icc_eq_image_Ioc N]
  exact Finset.sum_image (f := φ) (g := fun n : ℕ => (n : ℤ))
    (Set.injOn_of_injective (fun a b h => Int.ofNat.inj h))

/-! ## Summability of the windowed average -/

/-- The windowed average `lip2Avg N P M γ g s` is absolutely summable in `y` as soon as `g` is. -/
theorem summable_lip2Avg {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) {M : ℝ} (γ : FreqCircle)
    {g : ℤ → ℂ} (hg : Summable fun y : ℤ => ‖g y‖) (s : ℤ) :
    Summable fun y : ℤ => ‖lip2Avg N P M γ g s y‖ := by
  set V : ℤ → ℝ := fun y => ∑ n ∈ Finset.Ioc (N / 2) N,
      ‖win M γ ((n : ℤ) - s)‖ * ‖g (y + P.eval (n : ℤ))‖ with hVdef
  have hVsumm : Summable V := by
    rw [hVdef]
    refine summable_sum (s := Finset.Ioc (N / 2) N)
      (f := fun n : ℕ => fun y : ℤ => ‖win M γ ((n : ℤ) - s)‖ * ‖g (y + P.eval (n : ℤ))‖)
      (fun n _ => ?_)
    exact (hg.comp_injective (fun a b hab => by omega)).mul_left _
  have hNinv : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hNinv1 : (N : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity : (0 : ℝ) < (N : ℝ))]
    exact_mod_cast hN
  refine Summable.of_nonneg_of_le (fun y => norm_nonneg _) (fun y => ?_) hVsumm
  rw [lip2Avg, norm_mul, hNinv]
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ioc (N / 2) N,
        win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))‖
      ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          ‖win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          ‖win M γ ((n : ℤ) - s)‖ * ‖g (y + P.eval (n : ℤ))‖ := by
        congr 1
        exact Finset.sum_congr rfl (fun n _ => norm_mul _ _)
    _ ≤ 1 * ∑ n ∈ Finset.Ioc (N / 2) N,
          ‖win M γ ((n : ℤ) - s)‖ * ‖g (y + P.eval (n : ℤ))‖ := by
        refine mul_le_mul_of_nonneg_right hNinv1 ?_
        exact Finset.sum_nonneg (fun n _ => by positivity)
    _ = V y := by simp only [hVdef, one_mul]

/-- The squared windowed average is absolutely summable in `y`. -/
theorem summable_lip2Avg_sq {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) {M : ℝ} (γ : FreqCircle)
    {g : ℤ → ℂ} (hg : Summable fun y : ℤ => ‖g y‖) (hgb : ∀ y : ℤ, ‖g y‖ ≤ 1) (s : ℤ) :
    Summable fun y : ℤ => ‖lip2Avg N P M γ g s y‖ ^ 2 := by
  set V : ℤ → ℝ := fun y => ∑ n ∈ Finset.Ioc (N / 2) N,
      ‖win M γ ((n : ℤ) - s)‖ * ‖g (y + P.eval (n : ℤ))‖ with hVdef
  have hVsumm : Summable V := by
    rw [hVdef]
    refine summable_sum (s := Finset.Ioc (N / 2) N)
      (f := fun n : ℕ => fun y : ℤ => ‖win M γ ((n : ℤ) - s)‖ * ‖g (y + P.eval (n : ℤ))‖)
      (fun n _ => ?_)
    exact (hg.comp_injective (fun a b hab => by omega)).mul_left _
  set Wc : ℝ := ∑ n ∈ Finset.Ioc (N / 2) N, ‖win M γ ((n : ℤ) - s)‖ with hWcdef
  have hWc0 : 0 ≤ Wc := by
    rw [hWcdef]; exact Finset.sum_nonneg (fun n _ => norm_nonneg _)
  have hVle : ∀ y : ℤ, V y ≤ Wc := by
    intro y
    simp only [hVdef, hWcdef]
    refine Finset.sum_le_sum (fun n _ => ?_)
    exact mul_le_of_le_one_right (norm_nonneg _) (hgb _)
  have havg : ∀ y : ℤ, ‖lip2Avg N P M γ g s y‖ ≤ V y := by
    intro y
    have hNinv : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    have hNinv1 : (N : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity : (0 : ℝ) < (N : ℝ))]
      exact_mod_cast hN
    rw [lip2Avg, norm_mul, hNinv]
    calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ioc (N / 2) N,
          win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))‖
        ≤ (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            ‖win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ))‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
            ‖win M γ ((n : ℤ) - s)‖ * ‖g (y + P.eval (n : ℤ))‖ := by
          congr 1
          exact Finset.sum_congr rfl (fun n _ => norm_mul _ _)
      _ ≤ 1 * ∑ n ∈ Finset.Ioc (N / 2) N,
            ‖win M γ ((n : ℤ) - s)‖ * ‖g (y + P.eval (n : ℤ))‖ := by
          refine mul_le_mul_of_nonneg_right hNinv1 ?_
          exact Finset.sum_nonneg (fun n _ => by positivity)
      _ = V y := by simp only [hVdef, one_mul]
  refine Summable.of_nonneg_of_le (fun y => by positivity) (fun y => ?_) (hVsumm.mul_left Wc)
  calc ‖lip2Avg N P M γ g s y‖ ^ 2
      = ‖lip2Avg N P M γ g s y‖ * ‖lip2Avg N P M γ g s y‖ := by ring
    _ ≤ Wc * V y := mul_le_mul ((havg y).trans (hVle y)) (havg y) (norm_nonneg _) hWc0

/-! ## The pigeonhole over the shifts

(An in-file copy of `Work.KMTAreas.A4.existsShiftLeOfTail`, whose module does not currently
compile; the statement is identical.)
-/

/-- If `f ≥ 0` is summable on `ℤ`, its total mass is at least `A`, and the mass of the part
where `S < |s|` is at most `A/2`, then some `s` with `|s| ≤ S` carries mass at least
`A/(2*(2*S+1))`. -/
theorem lip2GenSavg_pivot (f : ℤ → ℝ) {S A : ℝ} (hS : 0 ≤ S) (hf : Summable f)
    (hf0 : ∀ s : ℤ, 0 ≤ f s) (hA : A ≤ ∑' s : ℤ, f s)
    (htail : (∑' s : ℤ, if S < |(s : ℝ)| then f s else 0) ≤ A / 2) :
    ∃ s : ℤ, |(s : ℝ)| ≤ S ∧ A / (2 * (2 * S + 1)) ≤ f s := by
  by_cases hA0 : A ≤ 0
  · refine ⟨0, by simpa using hS, ?_⟩
    have hden : (0 : ℝ) < 2 * (2 * S + 1) := by linarith
    have hle : A / (2 * (2 * S + 1)) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hA0 hden.le
    linarith [hf0 0]
  · have hApos : 0 < A := not_le.mp hA0
    have hden : (0 : ℝ) < 2 * (2 * S + 1) := by linarith
    have hc : (0 : ℝ) < A / (2 * (2 * S + 1)) := div_pos hApos hden
    by_contra hcon
    rw [not_exists] at hcon
    have hlt : ∀ s : ℤ, |(s : ℝ)| ≤ S → f s < A / (2 * (2 * S + 1)) := by
      intro s hs
      by_contra hle
      exact hcon s ⟨hs, not_lt.mp hle⟩
    have hgs : Summable (fun s : ℤ => if S < |(s : ℝ)| then f s else 0) := by
      apply Summable.of_nonneg_of_le (f := f)
      · intro s; split <;> simp [hf0 s]
      · intro s; split <;> simp [hf0 s]
      · exact hf
    have hhs : Summable (fun s : ℤ => if |(s : ℝ)| ≤ S then f s else 0) := by
      apply Summable.of_nonneg_of_le (f := f)
      · intro s; split <;> simp [hf0 s]
      · intro s; split <;> simp [hf0 s]
      · exact hf
    have hfh : (fun s : ℤ => f s) =
        fun s : ℤ =>
          (if S < |(s : ℝ)| then f s else 0) + (if |(s : ℝ)| ≤ S then f s else 0) := by
      funext s
      by_cases hs : S < |(s : ℝ)|
      · rw [if_pos hs, if_neg (not_le.mpr hs), add_zero]
      · rw [if_neg hs, if_pos (not_lt.mp hs), zero_add]
    have htsum : (∑' s : ℤ, f s) =
        (∑' s : ℤ, (if S < |(s : ℝ)| then f s else 0)) +
        (∑' s : ℤ, (if |(s : ℝ)| ≤ S then f s else 0)) := by
      rw [hfh]
      exact Summable.tsum_add hgs hhs
    have hhalf : A / 2 ≤ ∑' s : ℤ, (if |(s : ℝ)| ≤ S then f s else 0) := by
      linarith [hA, htail, htsum]
    set F : Finset ℤ := Finset.Icc (-⌊S⌋) ⌊S⌋ with hF
    have hn : 0 ≤ ⌊S⌋ := Int.floor_nonneg.mpr hS
    have hmemF_all : ∀ s : ℤ, |(s : ℝ)| ≤ S → s ∈ F := by
      intro s hs
      rw [hF, Finset.mem_Icc]
      refine ⟨?_, ?_⟩
      · have h1 : (-s : ℤ) ≤ ⌊S⌋ := by
          rw [Int.le_floor]
          push_cast
          linarith [(abs_le.mp hs).1]
        linarith
      · exact Int.le_floor.mpr (abs_le.mp hs).2
    have hmemF : ∀ s : ℤ, s ∈ F → |(s : ℝ)| ≤ S := by
      intro s hs
      rw [hF, Finset.mem_Icc] at hs
      obtain ⟨h1, h2⟩ := hs
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have h1' : (-s : ℤ) ≤ ⌊S⌋ := by linarith
        have h := Int.le_floor.mp h1'
        push_cast at h
        linarith
      · exact Int.le_floor.mp h2
    have hsum_eq : (∑' s : ℤ, (if |(s : ℝ)| ≤ S then f s else 0)) = Finset.sum F f := by
      have hsupp : ∀ b : ℤ, b ∉ F → (if |(b : ℝ)| ≤ S then f b else 0) = 0 := by
        intro b hb
        rw [if_neg]
        intro hle
        exact hb (hmemF_all b hle)
      rw [tsum_eq_sum (s := F) hsupp]
      exact Finset.sum_congr rfl (fun s hs => by rw [if_pos (hmemF s hs)])
    have hhalf' : A / 2 ≤ Finset.sum F f := by
      rw [← hsum_eq]
      exact hhalf
    have hcardZ : (F.card : ℤ) = 2 * ⌊S⌋ + 1 := by
      rw [hF]
      rw [Int.card_Icc_of_le (-⌊S⌋) ⌊S⌋ (by linarith)]
      ring
    have hcard_le : (F.card : ℝ) ≤ 2 * S + 1 := by
      have hcast : (F.card : ℝ) = 2 * (⌊S⌋ : ℝ) + 1 := by
        have := congrArg (fun z : ℤ => (z : ℝ)) hcardZ
        push_cast at this
        simpa using this
      have hfl := Int.floor_le S
      linarith
    have hlt_sum : Finset.sum F f < A / 2 := by
      have hstep : Finset.sum F f < Finset.sum F (fun _ => A / (2 * (2 * S + 1))) := by
        apply Finset.sum_lt_sum
        · intro s hs
          exact le_of_lt (hlt s (hmemF s hs))
        · refine ⟨0, ?_, ?_⟩
          · rw [hF, Finset.mem_Icc]
            exact ⟨by linarith, hn⟩
          · exact hlt 0 (by simpa using hS)
      calc Finset.sum F f < Finset.sum F (fun _ => A / (2 * (2 * S + 1))) := hstep
        _ = (F.card : ℝ) * (A / (2 * (2 * S + 1))) := by
              rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 * S + 1) * (A / (2 * (2 * S + 1))) :=
              mul_le_mul_of_nonneg_right hcard_le hc.le
        _ = A / 2 := by
              have hne : (2 * (2 * S + 1)) ≠ 0 := ne_of_gt hden
              field_simp
    linarith

/-! ## The target -/

theorem lip2GenSavg : ∃ C : ℝ, 0 < C ∧ ∀ {N : ℕ}, 1 ≤ N → ∀ (P : Polynomial ℤ) {M : ℝ}, 2 ≤ M → ∀ {γ : Work.Analysis.InverseTheory.FreqCircle} {F : ℤ → ℂ}, Summable (fun x : ℤ => ‖F x‖) → Work.Analysis.InverseTheory.FourierSupportIn F (Work.KMTAreas.A4.arcSet γ (1 / (2 * M))) → ∀ {g h : ℤ → ℂ}, (∀ y : ℤ, ‖g y‖ ≤ 1) → (∀ y : ℤ, ‖h y‖ ≤ 1) → Summable (fun y : ℤ => ‖g y‖) → Summable (fun y : ℤ => ‖h y‖) → ∀ {BF lF ε S : ℝ}, 0 < BF → 0 ≤ lF → (∀ x : ℤ, ‖F x‖ ≤ BF) → (∑' x : ℤ, ‖F x‖) ≤ lF → 1 ≤ S → (N : ℝ) ≤ S → ε * (N : ℝ) ^ P.natDegree ≤ ‖Work.Analysis.InverseTheory.bilinPair (Work.Analysis.InverseTheory.AhalfTranspose N P h g) F‖ → (∑' s : ℤ, (if S < |(s : ℝ)| then ‖∑' y : ℤ, h y * F (y + s) * Work.KMTAreas.A4.lip2Avg N P M γ g s y‖ else 0)) ≤ ε * (N : ℝ) ^ P.natDegree / 2 → ∃ s : ℤ, |(s : ℝ)| ≤ S ∧ ε ^ 2 * (N : ℝ) ^ (2 * P.natDegree + 2) ≤ C * S ^ 2 * BF * lF * ∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2 * ‖Work.KMTAreas.A4.winSumIcc M γ t P s ((N / 2 + 1 : ℕ) : ℤ) (N : ℤ)‖ ^ 2 := by
  refine ⟨36, by norm_num, ?_⟩
  intro N hN P M hM γ F hFsum hFsupp g h hgb hhb hgsum hhsum BF lF ε S hBF hlF hFb hF1 hS1 hNS hcorr htail
  classical
  have hM1 : (1 : ℝ) ≤ M := by linarith
  have hInner : Summable fun s : ℤ => ‖lip2Inner N P M γ F g h s‖ :=
    lip2InnerSummable hN P hM1 hFsum hgsum hhsum hgb hhb
  have htail' : (∑' s : ℤ, (if S < |(s : ℝ)| then ‖lip2Inner N P M γ F g h s‖ else 0))
      ≤ ε * (N : ℝ) ^ P.natDegree / 2 := by
    simpa only [lip2Inner] using htail
  have hA0 : 0 ≤ ε * (N : ℝ) ^ P.natDegree := by
    have h1 : 0 ≤ (∑' s : ℤ, (if S < |(s : ℝ)| then ‖lip2Inner N P M γ F g h s‖ else 0)) :=
      tsum_nonneg (fun s => by split_ifs <;> positivity)
    linarith
  have hexp : bilinPair (AhalfTranspose N P h g) F
      = ∑' s : ℤ, lip2Inner N P M γ F g h s := by
    rw [lip2WindowExpansion hN P hM hFsum hFsupp hgsum hhsum]
    simp only [lip2Inner]
  have hfull : ε * (N : ℝ) ^ P.natDegree ≤ ∑' s : ℤ, ‖lip2Inner N P M γ F g h s‖ := by
    calc ε * (N : ℝ) ^ P.natDegree
        ≤ ‖bilinPair (AhalfTranspose N P h g) F‖ := hcorr
      _ = ‖∑' s : ℤ, lip2Inner N P M γ F g h s‖ := by rw [hexp]
      _ ≤ ∑' s : ℤ, ‖lip2Inner N P M γ F g h s‖ := norm_tsum_le_tsum_norm hInner
  obtain ⟨s, hsS, hsA⟩ := lip2GenSavg_pivot (fun s : ℤ => ‖lip2Inner N P M γ F g h s‖)
    (by linarith : (0 : ℝ) ≤ S) hInner (fun s => norm_nonneg _) hfull htail'
  refine ⟨s, hsS, ?_⟩
  have hNne : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
    exact ne_of_gt this
  set TT : ℤ → ℂ := fun y => ∑ n ∈ Finset.Ioc (N / 2) N,
      win M γ ((n : ℤ) - s) * g (y + P.eval (n : ℤ)) with hTTdef
  have hTTeq : ∀ y : ℤ, TT y = ∑ n ∈ Finset.Icc ((N / 2 + 1 : ℕ) : ℤ) (N : ℤ),
      win M γ (n - s) * g (y + P.eval n) := by
    intro y
    rw [hTTdef]
    exact (sum_Icc_eq_sum_Ioc N (fun n : ℤ => win M γ (n - s) * g (y + P.eval n))).symm
  have hg2 : Summable fun x : ℤ => ‖g x‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_) hgsum
    calc ‖g x‖ ^ 2 = ‖g x‖ * ‖g x‖ := by ring
      _ ≤ 1 * ‖g x‖ := mul_le_mul_of_nonneg_right (hgb x) (norm_nonneg _)
      _ = ‖g x‖ := one_mul _
  have hpl := lip2PlancherelIcc g hgsum hg2 P hM γ s ((N / 2 + 1 : ℕ) : ℤ) (N : ℤ)
  set Ibnd : ℝ := ∫ t in (0 : ℝ)..1, ‖Work.A3.kmtFhat g t‖ ^ 2 *
      ‖winSumIcc M γ t P s ((N / 2 + 1 : ℕ) : ℤ) (N : ℤ)‖ ^ 2 with hIbdef
  have hTTsum : (∑' y : ℤ, ‖TT y‖ ^ 2) = Ibnd := by
    rw [← hpl]
    refine tsum_congr (fun y => ?_)
    rw [hTTeq y]
  have hlipTT : ∀ y : ℤ, lip2Avg N P M γ g s y = (((N : ℝ)⁻¹ : ℝ) : ℂ) * TT y := by
    intro y
    rw [hTTdef]
    rfl
  have hnl : ‖(((N : ℝ)⁻¹ : ℝ) : ℂ)‖ = (N : ℝ)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hScaleC : (∑' y : ℤ, ‖lip2Avg N P M γ g s y‖ ^ 2)
      = ((N : ℝ)⁻¹) ^ 2 * (∑' y : ℤ, ‖TT y‖ ^ 2) := by
    rw [show (∑' y : ℤ, ‖lip2Avg N P M γ g s y‖ ^ 2)
        = ∑' y : ℤ, ((N : ℝ)⁻¹) ^ 2 * ‖TT y‖ ^ 2 from
      tsum_congr (fun y => by rw [hlipTT y, norm_mul, hnl, mul_pow])]
    exact tsum_mul_left
  have hPlanch : (∑' y : ℤ, ‖lip2Avg N P M γ g s y‖ ^ 2) * (N : ℝ) ^ 2 = Ibnd := by
    have hNinv2 : ((N : ℝ)⁻¹) ^ 2 * (N : ℝ) ^ 2 = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hNne, one_pow]
    calc (∑' y : ℤ, ‖lip2Avg N P M γ g s y‖ ^ 2) * (N : ℝ) ^ 2
        = ((N : ℝ)⁻¹) ^ 2 * (∑' y : ℤ, ‖TT y‖ ^ 2) * (N : ℝ) ^ 2 := by rw [hScaleC]
      _ = ((N : ℝ)⁻¹) ^ 2 * (N : ℝ) ^ 2 * (∑' y : ℤ, ‖TT y‖ ^ 2) := by ring
      _ = (∑' y : ℤ, ‖TT y‖ ^ 2) := by rw [hNinv2, one_mul]
      _ = Ibnd := hTTsum
  set SF : ℝ := ∑' y : ℤ, ‖F (y + s)‖ ^ 2 with hSFdef
  set SC : ℝ := ∑' y : ℤ, ‖lip2Avg N P M γ g s y‖ ^ 2 with hSCdef
  have hshiftF : Summable fun y : ℤ => ‖F (y + s)‖ :=
    hFsum.comp_injective (fun a b hab => by omega)
  have hSigmaF2 : Summable fun y : ℤ => ‖F (y + s)‖ ^ 2 := by
    refine Summable.of_nonneg_of_le (fun y => by positivity) (fun y => ?_) (hshiftF.mul_left BF)
    calc ‖F (y + s)‖ ^ 2 = ‖F (y + s)‖ * ‖F (y + s)‖ := by ring
      _ ≤ BF * ‖F (y + s)‖ := mul_le_mul_of_nonneg_right (hFb (y + s)) (norm_nonneg _)
  have hSigmaC2 : Summable fun y : ℤ => ‖lip2Avg N P M γ g s y‖ ^ 2 :=
    summable_lip2Avg_sq hN P γ hgsum hgb s
  have hSFle : SF ≤ BF * lF := by
    have hle : ∀ y : ℤ, ‖F (y + s)‖ ^ 2 ≤ BF * ‖F (y + s)‖ := fun y => by
      calc ‖F (y + s)‖ ^ 2 = ‖F (y + s)‖ * ‖F (y + s)‖ := by ring
        _ ≤ BF * ‖F (y + s)‖ := mul_le_mul_of_nonneg_right (hFb (y + s)) (norm_nonneg _)
    have h1 : (∑' y : ℤ, ‖F (y + s)‖ ^ 2) ≤ ∑' y : ℤ, BF * ‖F (y + s)‖ :=
      Summable.tsum_le_tsum hle hSigmaF2 (hshiftF.mul_left BF)
    have h2 : (∑' y : ℤ, BF * ‖F (y + s)‖) = BF * ∑' y : ℤ, ‖F (y + s)‖ :=
      tsum_mul_left
    have h3 : (∑' y : ℤ, ‖F (y + s)‖) = ∑' x : ℤ, ‖F x‖ :=
      Equiv.tsum_eq (Equiv.addRight s) (fun x : ℤ => ‖F x‖)
    rw [hSFdef]
    calc (∑' y : ℤ, ‖F (y + s)‖ ^ 2) ≤ BF * ∑' y : ℤ, ‖F (y + s)‖ := h1.trans h2.le
      _ = BF * ∑' x : ℤ, ‖F x‖ := by rw [h3]
      _ ≤ BF * lF := mul_le_mul_of_nonneg_left hF1 hBF.le
  have hSCnn : 0 ≤ SC := by rw [hSCdef]; exact tsum_nonneg (fun y => by positivity)
  have hCS : ‖lip2Inner N P M γ F g h s‖ ^ 2 ≤ SF * SC := by
    have hInnerEq : lip2Inner N P M γ F g h s
        = ∑' y : ℤ, h y * F (y + s) * lip2Avg N P M γ g s y := rfl
    have hab : ∀ y : ℤ, ‖h y * F (y + s) * lip2Avg N P M γ g s y‖
        ≤ ‖F (y + s)‖ * ‖lip2Avg N P M γ g s y‖ := by
      intro y
      rw [norm_mul, norm_mul]
      calc ‖h y‖ * ‖F (y + s)‖ * ‖lip2Avg N P M γ g s y‖
          ≤ 1 * ‖F (y + s)‖ * ‖lip2Avg N P M γ g s y‖ := by
            gcongr
            exact hhb y
        _ = ‖F (y + s)‖ * ‖lip2Avg N P M γ g s y‖ := by ring
    have hAC : Summable fun y : ℤ => ‖F (y + s)‖ * ‖lip2Avg N P M γ g s y‖ := by
      refine Summable.of_nonneg_of_le (fun y => mul_nonneg (norm_nonneg _) (norm_nonneg _))
        (fun y => ?_) (hSigmaF2.add hSigmaC2)
      have h1 := norm_nonneg (F (y + s))
      have h2 := norm_nonneg (lip2Avg N P M γ g s y)
      nlinarith [sq_nonneg (‖F (y + s)‖ - ‖lip2Avg N P M γ g s y‖)]
    have hnormSumm : Summable fun y : ℤ => ‖h y * F (y + s) * lip2Avg N P M γ g s y‖ :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hab hAC
    have hbound : ‖∑' y : ℤ, h y * F (y + s) * lip2Avg N P M γ g s y‖
        ≤ ∑' y : ℤ, ‖F (y + s)‖ * ‖lip2Avg N P M γ g s y‖ :=
      (norm_tsum_le_tsum_norm hnormSumm).trans
        (Summable.tsum_le_tsum hab hnormSumm hAC)
    have hcs := sqTsumMulLe (fun y : ℤ => ‖F (y + s)‖)
      (fun y : ℤ => ‖lip2Avg N P M γ g s y‖)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hSigmaF2 hSigmaC2
    rw [hInnerEq]
    exact (pow_le_pow_left₀ (norm_nonneg _) hbound 2).trans (by
      simpa only [hSFdef, hSCdef] using hcs)
  have hDpos : (0 : ℝ) < 4 * (2 * S + 1) ^ 2 := by
    have h2 : (0 : ℝ) < 2 * S + 1 := by linarith
    positivity
  have hAdiv : 0 ≤ ε * (N : ℝ) ^ P.natDegree / (2 * (2 * S + 1)) :=
    div_nonneg hA0 (by linarith)
  have hmain : (ε * (N : ℝ) ^ P.natDegree / (2 * (2 * S + 1))) ^ 2
      ≤ (BF * lF) * SC :=
    (le_trans (pow_le_pow_left₀ hAdiv hsA 2) hCS).trans
      (by simpa only [hSFdef] using mul_le_mul_of_nonneg_right hSFle hSCnn)
  have hmain2 : (ε * (N : ℝ) ^ P.natDegree) ^ 2 * (N : ℝ) ^ 2
      ≤ 4 * (2 * S + 1) ^ 2 * (BF * lF * Ibnd) := by
    have hm := mul_le_mul_of_nonneg_right hmain (by positivity : (0 : ℝ) ≤ (N : ℝ) ^ 2)
    have hL : (ε * (N : ℝ) ^ P.natDegree / (2 * (2 * S + 1))) ^ 2 * (N : ℝ) ^ 2
        = (ε * (N : ℝ) ^ P.natDegree) ^ 2 * (N : ℝ) ^ 2 / (4 * (2 * S + 1) ^ 2) := by
      rw [div_pow]; ring
    rw [hL] at hm
    rw [show (BF * lF) * SC * (N : ℝ) ^ 2 = BF * lF * Ibnd from by
      rw [hSCdef, mul_assoc, hPlanch]] at hm
    rw [div_le_iff₀ hDpos] at hm
    rw [mul_comm (BF * lF * Ibnd) (4 * (2 * S + 1) ^ 2)] at hm
    exact hm
  have hDle : 4 * (2 * S + 1) ^ 2 ≤ 36 * S ^ 2 := by nlinarith [hS1]
  have hIbnd0 : 0 ≤ Ibnd := by rw [← hPlanch]; positivity
  have hfinal : (ε * (N : ℝ) ^ P.natDegree) ^ 2 * (N : ℝ) ^ 2
      ≤ 36 * S ^ 2 * BF * lF * Ibnd := by
    have hnn : 0 ≤ BF * lF * Ibnd := by
      have : (0 : ℝ) ≤ BF * lF := mul_nonneg hBF.le hlF
      positivity
    calc (ε * (N : ℝ) ^ P.natDegree) ^ 2 * (N : ℝ) ^ 2
        ≤ 4 * (2 * S + 1) ^ 2 * (BF * lF * Ibnd) := hmain2
      _ ≤ 36 * S ^ 2 * (BF * lF * Ibnd) := mul_le_mul_of_nonneg_right hDle hnn
      _ = 36 * S ^ 2 * BF * lF * Ibnd := by ring
  have hAeq : ε ^ 2 * (N : ℝ) ^ (2 * P.natDegree + 2)
      = (ε * (N : ℝ) ^ P.natDegree) ^ 2 * (N : ℝ) ^ 2 := by
    have hexp : 2 * P.natDegree + 2 = P.natDegree * 2 + 2 := by ring
    rw [hexp, pow_add, pow_mul, mul_pow]
    ring
  rw [hAeq]
  exact hfinal

end Work.KMTAreas.A4
