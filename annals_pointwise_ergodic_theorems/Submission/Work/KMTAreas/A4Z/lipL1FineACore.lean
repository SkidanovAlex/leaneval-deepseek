/-
# Area A4Z: the free-window fine inverse theorem (`LipL1FineA`) -- shared vocabulary and the
small-`N` branch

`Work.KMTAreas.A4.lipL1Fine` proves the *pinned* fine inverse theorem `LipL1Fine P`
(window `N₀ ∈ [N^d/2, 2 N^d]`, the `A = 2` case of `LipL1FineA`).  The §5.2 chain of the
Krause--Mirek--Tao paper needs the free-window form `LipL1FineA P` (constants may depend on `A`),
exactly as for Proposition `lip` (`A4/peluseLipL1TailA.lean` vs `A4/peluseLipL1Tail.lean`).

The proof of `LipL1FineA` splits into the two branches of the Peluse dichotomy, as everywhere else
in this area:

* **the small-`N` branch** (`N ≤ C δ^{-K}`): the transposed dual function `Ã_N^*(h,g)` works.  It
  is proved here as `Work.KMTAreas.A4Z.lipL1FineA_caseA`;
* **the large-`N` branch** (`C δ^{-K} < N`): the §5.1 smoothing construction with the progression
  average of `f`; the statement of that branch is the `def` `LipL1FineABigN` below (and it is the
  piece delegated to `Submission/Work/KMTAreas/A4Z/lipL1FineACaseB.lean`).

The two branches were merged *inside one proof* in `A4/lipL1Fine.lean`; here they are separated so
that each has its own constants, exactly as `A4/lipL1TailCaseBA` was separated from
`A4/peluseLipL1TailA`.  The only difference between the free-window branch and the pinned one is
the mass bound `2 (N₀ + q N') + 1 ≤ K' δ^{-u} N^d`: with `N₀ ≤ A N^d` one takes `K' ≥ 2A + 2`
instead of `K' ≥ 5`.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2GenDefs
import Submission.Work.KMTAreas.A4.lipL1Fine

set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 20000

open scoped BigOperators FourierTransform
open MeasureTheory

namespace Work.KMTAreas.A4Z

open Work.KMTAreas.A4 Work.Analysis.InverseTheory

/-! ## The large-`N` branch

Same conclusion as `Work.KMTAreas.A4.LipL1FineA`, with the extra hypothesis `C δ^{-K} < N` on the
constants of the branch. -/

/-- **The large-`N` branch of the free-window fine inverse theorem.**  There are constants
`C, K > 0` (depending on `A`, `P` and the Schwartz function of `A4/lipSchwartzExists`, but not on
`ρ`) such that whenever `N > C δ^{-K}` and the hypotheses of `LipL1FineA` hold, the dual function
`F` can be taken to be `λ • smoothOp (lipWeight ψ ε N') G q`, whose Fourier transform is supported
in the union of the `q ≲ δ^{-K}` arcs of radius `2^k ≲ δ^{-K}/N` around the `q`-torsion
frequencies (`A4.lipWeightFourierSupportFine`). -/
def LipL1FineABigN (P : Polynomial ℤ) : Prop :=
  ∀ (A : ℝ), 1 ≤ A → ∃ C K : ℝ, 0 < C ∧ 0 < K ∧
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
      (N : ℝ) ^ P.natDegree / A ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
      SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
      δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
      C * δ⁻¹ ^ K < N →
      ∃ (F : ℤ → ℂ) (k : ℤ) (𝔸 : Finset FreqCircle),
        (∀ x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K) ∧
        Summable (fun x : ℤ => ‖F x‖) ∧
        (∑' x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
        FourierSupportIn F (⋃ α ∈ (𝔸 : Set FreqCircle), arcSet α ((2 : ℝ) ^ k)) ∧
        (𝔸.card : ℝ) ≤ C * δ⁻¹ ^ K ∧
        (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ) ∧
        δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair f F‖

/-! ## The small-`N` branch -/

/-- **The small-`N` branch of the free-window fine inverse theorem.**  For any `C ≥ 2A + 5` and
`K ≥ 1`, if `N ≤ C δ^{-K}` then the transposed dual function `Ã_N^*(h,g)` scaled by `C/(2A+5)`
witnesses the conclusion with the constants `C, K`, the single arc `{0}` (of radius `1`, which is
the whole frequency circle) and `k = 0`. -/
theorem lipL1FineA_caseA (P : Polynomial ℤ) (hP : 2 ≤ P.natDegree) (A C K : ℝ) (hA : 1 ≤ A)
    (hC : 2 * A + 5 ≤ C) (hK : 1 ≤ K) :
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 →
    ∀ (N N₀ : ℕ) (δ : ℝ) (f g h : ℤ → ℂ), 1 ≤ N → 0 < δ → δ ≤ 1 →
      (N : ℝ) ^ P.natDegree / A ≤ (N₀ : ℝ) → (N₀ : ℝ) ≤ A * (N : ℝ) ^ P.natDegree →
      SupportIn f N₀ → SupportIn g N₀ → SupportIn h N₀ →
      (∀ x : ℤ, ‖f x‖ ≤ 1) → (∀ x : ℤ, ‖g x‖ ≤ 1) → (∀ x : ℤ, ‖h x‖ ≤ 1) →
      δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair (AhalfZ N P f g) h‖ →
      (N : ℝ) ≤ C * δ⁻¹ ^ K →
      ∃ (F : ℤ → ℂ) (k : ℤ) (𝔸 : Finset FreqCircle),
        (∀ x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K) ∧
        Summable (fun x : ℤ => ‖F x‖) ∧
        (∑' x : ℤ, ‖F x‖ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) ∧
        FourierSupportIn F (⋃ α ∈ (𝔸 : Set FreqCircle), arcSet α ((2 : ℝ) ^ k)) ∧
        (𝔸.card : ℝ) ≤ C * δ⁻¹ ^ K ∧
        (2 : ℝ) ^ k ≤ C * δ⁻¹ ^ K / (N : ℝ) ∧
        δ ^ K * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair f F‖ := by
  intro ρ hρpos hρle N N₀ δ f g h hN hδpos hδle _hN₀lo hN₀hi hfs hgs hhs hfb hgb hhb hcorr hsmall
  have hD1 : 1 ≤ δ⁻¹ := (one_le_inv₀ hδpos).mpr hδle
  have hDpos : 0 < δ⁻¹ := inv_pos.mpr hδpos
  have hCpos : 0 < C := lt_of_lt_of_le (by linarith : (0 : ℝ) < 2 * A + 5) hC
  set Cw : ℝ := 2 * A + 5 with hCwdef
  have hCwpos : 0 < Cw := by rw [hCwdef]; linarith
  have hCw1 : 1 ≤ Cw := by rw [hCwdef]; linarith
  have hCwC : Cw ≤ C := by rw [hCwdef]; exact hC
  set F₀ : ℤ → ℂ := AhalfTranspose N P h g with hF₀def
  have hF₀sup : ∀ x : ℤ, ‖F₀ x‖ ≤ 1 := fun x => lipNormAhalfTranspose hN P hhb hgb x
  have hF₀supp : SupportIn F₀ (N₀ + N) := lipSupportAhalfTranspose P hhs
  have hF₀one : ellOne F₀ ≤ 2 * ((N₀ + N : ℕ) : ℝ) + 1 := by
    simpa using ellOne_le_of_supportIn F₀ (N₀ + N) hF₀supp hF₀sup
  have hF₀summ : Summable fun x : ℤ => ‖F₀ x‖ := by
    refine summable_of_ne_finset_zero
      (s := Finset.Icc (-(((N₀ + N : ℕ) : ℤ))) (((N₀ + N : ℕ) : ℤ))) fun x hx => ?_
    have hx' : (N₀ + N) < x.natAbs := by
      simp only [Finset.mem_Icc, not_and_or, not_le] at hx
      rcases hx with hh | hh <;> omega
    rw [hF₀supp x hx', norm_zero]
  have hF₀corr : δ * (N : ℝ) ^ P.natDegree ≤ ‖bilinPair f F₀‖ := by
    have h1 : bilinPair f F₀ = bilinPair (AhalfZ N P f g) h := by
      rw [show bilinPair f F₀ = bilinPair F₀ f from lipBilinPairComm f F₀, hF₀def]
      exact (bilinPair_AhalfZ_eq_transpose (FinSupp.of_supportIn hfs)
        (FinSupp.of_supportIn hgs) (FinSupp.of_supportIn hhs) N P).symm
    rw [h1]; exact hcorr
  have hlam₀ : ‖(((C / Cw : ℝ)) : ℂ)‖ = C / Cw := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hD3 : (1 : ℝ) ≤ δ⁻¹ ^ K := Real.one_le_rpow hD1 (by linarith : (0 : ℝ) ≤ K)
  set 𝔸₀ : Finset FreqCircle := {0} with hA₀def
  refine ⟨(((C / Cw : ℝ)) : ℂ) • F₀, 0, 𝔸₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [Pi.smul_apply, norm_smul, hlam₀]
    have h2 : ‖F₀ x‖ ≤ 1 := hF₀sup x
    have h4 : C / Cw * ‖F₀ x‖ ≤ C / Cw := by
      simpa using mul_le_mul_of_nonneg_left h2 (by positivity)
    have h5 : C / Cw ≤ C := by
      rw [div_le_iff₀ hCwpos]
      nlinarith [hCw1, hCpos.le]
    calc C / Cw * ‖F₀ x‖ ≤ C / Cw := h4
      _ ≤ C := h5
      _ ≤ C * δ⁻¹ ^ K := by
          simpa using mul_le_mul_of_nonneg_left hD3 hCpos.le
  · show Summable fun x : ℤ => ‖(((C / Cw : ℝ)) : ℂ) • F₀ x‖
    have hsum' : (fun x : ℤ => ‖(((C / Cw : ℝ)) : ℂ) • F₀ x‖)
        = fun x : ℤ => (C / Cw) * ‖F₀ x‖ := by
      funext x
      rw [norm_smul, hlam₀]
    rw [hsum']
    exact hF₀summ.mul_left (C / Cw)
  · show ellOne ((((C / Cw : ℝ)) : ℂ) • F₀) ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree
    rw [lipEllOneSmul, hlam₀]
    have hNd1 : (1 : ℝ) ≤ (N : ℝ) ^ P.natDegree := one_le_pow₀ (by exact_mod_cast hN)
    have hNle : (N : ℝ) ≤ (N : ℝ) ^ P.natDegree := by
      have h2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by
        nlinarith [show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN]
      have h3 : (N : ℝ) ^ 2 ≤ (N : ℝ) ^ P.natDegree :=
        pow_le_pow_right₀ (by exact_mod_cast hN) (by omega)
      linarith
    have hM : 2 * ((N₀ + N : ℕ) : ℝ) + 1 ≤ Cw * (N : ℝ) ^ P.natDegree := by
      push_cast
      rw [hCwdef]
      nlinarith [hN₀hi, hNle, hNd1, hA]
    calc C / Cw * ellOne F₀ ≤ C / Cw * (2 * ((N₀ + N : ℕ) : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hF₀one (by positivity)
      _ ≤ C / Cw * (Cw * (N : ℝ) ^ P.natDegree) :=
          mul_le_mul_of_nonneg_left hM (by positivity)
      _ = C * (N : ℝ) ^ P.natDegree := by
          rw [← mul_assoc, div_mul_cancel₀ C hCwpos.ne']
      _ ≤ C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree := by
          have hp : (0 : ℝ) ≤ (N : ℝ) ^ P.natDegree := by positivity
          calc C * (N : ℝ) ^ P.natDegree
              ≤ C * (δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree) :=
                mul_le_mul_of_nonneg_left (by
                  simpa using mul_le_mul_of_nonneg_right hD3 hp) hCpos.le
            _ = C * δ⁻¹ ^ K * (N : ℝ) ^ P.natDegree := by ring
  · have hUniv : (⋃ α ∈ (𝔸₀ : Set FreqCircle), arcSet α ((2 : ℝ) ^ (0 : ℤ))) = Set.univ := by
      refine Set.eq_univ_of_forall fun γ => ?_
      refine Set.mem_biUnion (x := (0 : FreqCircle)) ?_ ?_
      · rw [hA₀def]
        exact Finset.mem_coe.mpr (Finset.mem_singleton_self (0 : FreqCircle))
      · rw [show ((2 : ℝ) ^ (0 : ℤ)) = 1 by norm_num, lipArcSet_zero_one]
        exact Set.mem_univ γ
    rw [hUniv]
    intro ξ hξ
    exact absurd (Set.mem_univ ξ) hξ
  · have h6 : (1 : ℝ) ≤ C * δ⁻¹ ^ K := by
      have h7 : (7 : ℝ) ≤ C := by linarith
      nlinarith [h7, hD3]
    rw [hA₀def, Finset.card_singleton]
    simpa using h6
  · have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have h1 : (2 : ℝ) ^ (0 : ℤ) = 1 := by norm_num
    rw [h1, one_le_div hNpos]
    exact hsmall
  · show δ ^ K * (N : ℝ) ^ P.natDegree
      ≤ ‖bilinPair f ((((C / Cw : ℝ)) : ℂ) • F₀)‖
    rw [lipBilinPairSmul, norm_mul, hlam₀]
    have h6 : δ ^ K ≤ δ := by
      have h := Real.rpow_le_rpow_of_exponent_ge hδpos hδle hK
      simpa using h
    have hNd0 : 0 < (N : ℝ) ^ P.natDegree := by positivity
    calc δ ^ K * (N : ℝ) ^ P.natDegree
        ≤ δ * (N : ℝ) ^ P.natDegree := mul_le_mul_of_nonneg_right h6 hNd0.le
      _ ≤ (C / Cw) * (δ * (N : ℝ) ^ P.natDegree) := by
          have h7 : (1 : ℝ) ≤ C / Cw := by
            rw [le_div_iff₀ hCwpos]
            linarith [hCwC]
          exact le_trans (le_of_eq (one_mul _).symm)
            (mul_le_mul_of_nonneg_right h7 (by positivity))
      _ ≤ (C / Cw) * ‖bilinPair f F₀‖ :=
          mul_le_mul_of_nonneg_left hF₀corr (by positivity)

end Work.KMTAreas.A4Z
