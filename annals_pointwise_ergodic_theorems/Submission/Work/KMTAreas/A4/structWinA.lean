/-
# Corollary `struct` at the window `A`, from `LipWinA` (§5 of Krause--Mirek--Tao)

This module closes the last bookkeeping step of the window-parameterised §5.1 chain of
`A4/improvOneZDefs.lean`: Proposition `lip` at the window `A` (`LipWinA P A`, i.e. `LipOutputTailA`
for every `rho` in `(0,1]` with one pair of constants) implies Corollary `struct` at the window `A`
(`StructWinA P A`).

The argument is the Hahn--Banach step of Corollary `struct` (`A4/StructCor.lean`,
`A4/structA.lean`), with the truncation window `B = A N^d` of the test function fed to
Proposition `lip` equal to the window at which `LipOutputTailA` measures the spatial tail.  The
point is that `LipOutputTailA` has a support-radius parameter `N0` free in `[N^d/A, A N^d]`
independently of the tail window `A N^d`, so we may take `N0 := floor (A N^d)`, which contains
`N0 + N` (because `N0 + N` is an integer with `N0 + N <= A N^d`) and the support of the truncation;
the truncation error then lives exactly on the tail of `LipOutputTailA`, and the transposition
identity `bilinPair (AhalfZ N P (1_{A N^d} . star o f) g) h = inner f (AhalfTranspose N P h g)`
holds because `AhalfTranspose N P h g` is supported in `N0 + N <= A N^d`.

Note the factor `A` inside `StructPhiA` is harmless: `A >= 1`, so every bound of
`LipOutputTailA` (which is stated without the factor `A`) implies the corresponding bound of
`StructPhiA` (which is stated with it), and the constants `C, K` pass through unchanged.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.improvOneZDefs
import Submission.Work.KMTAreas.A4.structATail

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory
open Work.Analysis.IonescuWainger (L2Z)

theorem structWinA (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (A : ℝ) (hA : 1 ≤ A) (hLip : Work.KMTAreas.A4.LipWinA P A) : Work.KMTAreas.A4.StructWinA P A := by
  obtain ⟨C, K, hC, hK, hLip⟩ := hLip
  refine ⟨C, K, hC, hK, ?_⟩
  intro ρ hρ hρ1 δ N N₀ g h hN hδ0 hδ1 hN0lo hN0hi hgs hhs hg1 hh1
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNdpos : (0 : ℝ) < (N : ℝ) ^ P.natDegree := pow_pos hNpos _
  have hApos : 0 < δ * (N : ℝ) ^ P.natDegree := mul_pos hδ0 hNdpos
  have hδKpos : 0 < δ ^ K := Real.rpow_pos_of_pos hδ0 K
  have hBpos : 0 < δ ^ K * (N : ℝ) ^ P.natDegree / 4 := by positivity
  have hδK : 0 < δ ^ K * (N : ℝ) ^ P.natDegree := mul_pos hδKpos hNdpos
  have hCinv : 0 ≤ C * δ⁻¹ ^ K :=
    le_of_lt (mul_pos hC (Real.rpow_pos_of_pos (inv_pos.mpr hδ0) K))
  -- ## The Hahn--Banach hypothesis of Corollary `struct`
  have hHahn : ∀ f : L2Z, (∀ x : ℤ, ‖f x‖ ≤ 1) →
      δ * (N : ℝ) ^ P.natDegree < ‖inner ℂ f (ahalfStarL2 N P h g N₀ hhs hgs)‖ →
      ∃ φ ∈ StructPhiA P ρ A C K δ N,
        δ ^ K * (N : ℝ) ^ P.natDegree / 4 < ‖inner ℂ f φ‖ := by
    intro f hf1 hfbig
    set B : ℝ := A * (N : ℝ) ^ P.natDegree with hBdef
    have hBpos' : 0 < B := by rw [hBdef]; positivity
    have hN0NleM : N₀ + N ≤ Nat.floor B := by
      rw [hBdef]
      refine Nat.le_floor ?_
      push_cast
      exact hN0hi
    have hN0leM : N₀ ≤ Nat.floor B := le_trans (Nat.le_add_right N₀ N) hN0NleM
    have hN0leM' : (N₀ : ℝ) ≤ ((Nat.floor B : ℕ) : ℝ) := by exact_mod_cast hN0leM
    have hMlo : (N : ℝ) ^ P.natDegree / A ≤ ((Nat.floor B : ℕ) : ℝ) := by
      linarith [hN0lo, hN0leM']
    have hMhi : ((Nat.floor B : ℕ) : ℝ) ≤ A * (N : ℝ) ^ P.natDegree := by
      have h := Nat.floor_le hBpos'.le
      rw [hBdef] at h
      exact h
    -- the transposition identity
    have hkey : δ * (N : ℝ) ^ P.natDegree
        ≤ ‖bilinPair (AhalfZ N P (lipInputW P B (fun x : ℤ => f x)) g) h‖ := by
      rw [bilinPair_lipInputW_eq_inner hBpos'.le hN0NleM hgs hhs]
      exact le_of_lt hfbig
    obtain ⟨F, l, k, hF1, hFsum, hFl1, hFtail, hFsupp, hFl, hFk, hFcorr⟩ :=
      hLip ρ hρ hρ1 N (Nat.floor B) δ (lipInputW P B (fun x : ℤ => f x)) g h
        hN hδ0 hδ1 hMlo hMhi (supportIn_lipInputW P B _)
        (hgs.mono hN0leM) (hhs.mono hN0leM)
        (norm_lipInputW_le_one P B hf1) hg1 hh1 hkey
    set φ : L2Z := ⟨F, memℓp_of_l1 hCinv hFsum hF1⟩ with hφ
    have hφapply : ∀ x : ℤ, φ x = F x := fun x => rfl
    -- the factor `A >= 1` converts the bounds of `LipOutputTailA` into those of `StructPhiA`
    have hle1 : C * δ⁻¹ ^ K ≤ C * A * δ⁻¹ ^ K := by
      calc C * δ⁻¹ ^ K ≤ C * δ⁻¹ ^ K * A := le_mul_of_one_le_right hCinv hA
        _ = C * A * δ⁻¹ ^ K := by ring
    have hle1div : C * δ⁻¹ ^ K / (N : ℝ) ≤ C * A * δ⁻¹ ^ K / (N : ℝ) :=
      div_le_div_of_nonneg_right hle1 (le_of_lt hNpos)
    refine ⟨φ, ?_, ?_⟩
    · refine ⟨fun x => (hF1 x).trans hle1, ?_, ?_, ⟨l, k, ?_, hFl.trans hle1, hFk.trans hle1div⟩⟩
      · simpa only [hφapply] using hFsum
      · have hstep : C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree
            ≤ C * A * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree := by
          calc C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree
              = (C * δ⁻¹ ^ K) * (N : ℝ) ^ P.natDegree := by ring
            _ ≤ (C * A * δ⁻¹ ^ K) * (N : ℝ) ^ P.natDegree :=
                mul_le_mul_of_nonneg_right hle1 (le_of_lt hNdpos)
            _ = C * A * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree := by ring
        simpa only [hφapply] using hFl1.trans hstep
      · simpa only [hφapply] using hFsupp
    · -- the correlation
      set S : ℤ → ℂ := fun x => star (f x) - lipInputW P B (fun x : ℤ => f x) x with hS
      have hbS : ∀ x : ℤ, ‖S x‖ ≤ 2 := by
        intro x
        rw [hS]
        calc ‖star (f x) - lipInputW P B (fun x : ℤ => f x) x‖
            ≤ ‖star (f x)‖ + ‖lipInputW P B (fun x : ℤ => f x) x‖ := norm_sub_le _ _
          _ ≤ 1 + 1 := by
              rw [norm_star]
              exact add_le_add (hf1 x) (norm_lipInputW_le_one P B hf1 x)
          _ = 2 := by norm_num
      have hsumS : Summable fun x : ℤ => F x * S x := by
        refine Summable.of_norm ?_
        refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) (hFsum.mul_left 2)
        rw [norm_mul]
        simpa [mul_comm] using mul_le_mul_of_nonneg_right (hbS x) (norm_nonneg (F x))
      have hsumA : Summable fun x : ℤ => F x * lipInputW P B (fun x : ℤ => f x) x := by
        refine Summable.of_norm ?_
        refine Summable.of_nonneg_of_le (fun x => norm_nonneg _) (fun x => ?_) (hFsum.mul_left 1)
        rw [norm_mul]
        simpa [mul_comm] using
          mul_le_mul_of_nonneg_right (norm_lipInputW_le_one P B hf1 x) (norm_nonneg (F x))
      have hinner : inner ℂ f φ = ∑' x : ℤ, F x * star (f x) := by
        rw [lp.inner_eq_tsum]
        refine tsum_congr fun x => ?_
        rw [RCLike.inner_apply, starRingEnd_apply, hφapply]
      have hpair : bilinPair (lipInputW P B (fun x : ℤ => f x)) F
          = ∑' x : ℤ, F x * lipInputW P B (fun x : ℤ => f x) x := by
        simp only [bilinPair]
        exact tsum_congr fun x => mul_comm _ _
      have hsplit : (∑' x : ℤ, F x * star (f x))
          = bilinPair (lipInputW P B (fun x : ℤ => f x)) F + ∑' x : ℤ, F x * S x := by
        rw [hpair, ← hsumA.tsum_add hsumS]
        refine tsum_congr fun x => ?_
        rw [hS]; ring
      have htail : ‖∑' x : ℤ, F x * S x‖
          ≤ ∑' x : ℤ, (if B < (x.natAbs : ℝ) then ‖F x‖ else 0) := by
        rw [hS]
        exact norm_tsum_mul_sub_lipInputW_le (P := P) (B := B) (F := F) hf1 hFsum
      have hFtail' : ∑' x : ℤ, (if B < (x.natAbs : ℝ) then ‖F x‖ else 0)
          ≤ δ ^ K * (N : ℝ) ^ P.natDegree / 2 := by
        rw [hBdef]
        exact hFtail
      have hmain : ‖inner ℂ f φ‖
          ≥ ‖bilinPair (lipInputW P B (fun x : ℤ => f x)) F‖ - ‖∑' x : ℤ, F x * S x‖ := by
        rw [hinner, hsplit]
        have h2 : ‖bilinPair (lipInputW P B (fun x : ℤ => f x)) F‖
            ≤ ‖bilinPair (lipInputW P B (fun x : ℤ => f x)) F + ∑' x : ℤ, F x * S x‖
              + ‖∑' x : ℤ, F x * S x‖ := by
          have := norm_add_le (bilinPair (lipInputW P B (fun x : ℤ => f x)) F
            + ∑' x : ℤ, F x * S x) (-(∑' x : ℤ, F x * S x))
          simpa using this
        linarith
      linarith [hFcorr, htail.trans hFtail', hmain, hδK]
  -- ## The decomposition (Lemma `hahn`)
  obtain ⟨ι, hι, s, φ, lam, w, E₁, E₂, hφ, hlam, hw, hwsum, hE₁, hE₂, hdecomp⟩ :=
    hahn_decomposition hApos hBpos (ahalfStarL2 N P h g N₀ hhs hgs)
      (StructPhiA P ρ A C K δ N) hHahn hδ0
  refine ⟨ι, hι, s, φ, lam, w, E₁, E₂, hφ, ?_, hw, hwsum, hE₁, hE₂, ?_⟩
  · -- the coefficient bound `A / B = 4 δ^{1-K}`
    intro i hi
    have hδinv : δ⁻¹ ^ (K - 1) = δ ^ (1 - K) := by
      rw [Real.inv_rpow hδ0.le, ← Real.rpow_neg hδ0.le]
      congr 1
      ring
    refine (hlam i hi).trans (le_of_eq ?_)
    rw [hδinv]
    rw [show (4 : ℝ) * δ ^ (1 - K) = 4 * (δ / δ ^ K) from by
      rw [Real.rpow_sub hδ0, Real.rpow_one]]
    field_simp
  · -- read off the pointwise identity
    intro x
    have hx := congrFun (congrArg (fun z : L2Z => (z : ℤ → ℂ)) hdecomp) x
    simp only [ahalfStarL2_apply, lp.coeFn_add, Pi.add_apply] at hx
    rw [hx]

end Work.KMTAreas.A4
