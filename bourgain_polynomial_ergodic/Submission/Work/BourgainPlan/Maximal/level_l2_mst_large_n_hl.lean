import Mathlib
import Submission.Work.BourgainPlan.Maximal.poly_sup_le_finset_hlMax
import Submission.Work.BourgainPlan.Maximal.exists_sign_shift_nonneg

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped ENNReal BigOperators

open Commons.Analysis.Maximal (hlMax)

/-- The average over the dilate `(0, 2^n]` is at most the supremum over `N ∈ ℕ` of the averages
over `(0, N+1]` (take `N = 2^n - 1`). -/
lemma dilation_le_iSup_two_pow (F : ℝ → ℝ≥0∞) (n : ℕ) :
    ∫⁻ s in Set.Ioc (0:ℝ) 1, F ((2:ℝ)^n * s)
      ≤ ⨆ N : ℕ, ∫⁻ s in Set.Ioc (0:ℝ) 1, F (((N + 1 : ℕ) : ℝ) * s) := by
  have h2 : 1 ≤ (2:ℕ)^n := Nat.one_le_two_pow
  refine le_iSup_of_le (2^n - 1) ?_
  have hcast : (((2^n - 1 + 1 : ℕ)) : ℝ) = (2:ℝ)^n := by
    rw [Nat.sub_add_cancel h2]
    push_cast
    norm_num
  rw [hcast]

/-- **The `-` form at dilation `2^n`.**  If `q : ℝ[X]` is nonconstant and nonnegative on
`[0,∞)`, the averages `∫⁻ s in (0,1], ψ (x - q (2^n s))` are dominated, uniformly in `n`, by a
constant times a finite sum of Hardy–Littlewood maximal functions of `ψ`.  This is
`poly_sup_ge_one_le_hlMax` with the index set `{N+1}` replaced by the dyadic set `{2^n}`. -/
lemma poly_exp_minus_le_hlMax {q : Polynomial ℝ} (hdeg : 1 ≤ q.natDegree)
    (hqnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ q.eval x) :
    ∃ K : ℝ, 0 < K ∧ ∃ T : Finset ℝ, ∀ (n : ℕ) (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
      ∫⁻ s in Set.Ioc (0:ℝ) 1, ψ (x - q.eval ((2:ℝ)^n * s))
        ≤ ENNReal.ofReal K * ∑ c ∈ T, hlMax ψ (x - c) := by
  obtain ⟨K, hK, T, hT⟩ := poly_sup_ge_one_le_hlMax hdeg hqnn
  refine ⟨K, hK, T, fun n ψ hψ x => ?_⟩
  exact le_trans (dilation_le_iSup_two_pow (fun u : ℝ => ψ (x - q.eval u)) n) (hT ψ hψ x)

/-- **The `+` form at dilation `2^n`.**  Same statement as `poly_exp_minus_le_hlMax` with the
sign of the argument of `ψ` reversed, obtained by reflecting `ψ`: with `ψ̃ y = ψ (-y)` and
`hlMax ψ̃ y = hlMax ψ (-y)` (lemma `hlMax_reflect`) the `-` form applied to `ψ̃` at the point
`-x` is exactly the `+` form for `ψ` at `x`. -/
lemma poly_exp_plus_le_hlMax {q : Polynomial ℝ} (hdeg : 1 ≤ q.natDegree)
    (hqnn : ∀ x : ℝ, 0 ≤ x → 0 ≤ q.eval x) :
    ∃ K : ℝ, 0 < K ∧ ∃ T : Finset ℝ, ∀ (n : ℕ) (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
      ∫⁻ s in Set.Ioc (0:ℝ) 1, ψ (x + q.eval ((2:ℝ)^n * s))
        ≤ ENNReal.ofReal K * ∑ c ∈ T, hlMax ψ (x - c) := by
  obtain ⟨K, hK, T, hT⟩ := poly_exp_minus_le_hlMax hdeg hqnn
  refine ⟨K, hK, T.image (fun c => -c), fun n ψ hψ x => ?_⟩
  have hmeas : Measurable (fun z : ℝ => ψ (-z)) := hψ.comp measurable_neg
  have h := hT n (fun z : ℝ => ψ (-z)) hmeas (-x)
  have hL : (∫⁻ s in Set.Ioc (0:ℝ) 1, (fun z : ℝ => ψ (-z)) (-x - q.eval ((2:ℝ)^n * s)))
      = ∫⁻ s in Set.Ioc (0:ℝ) 1, ψ (x + q.eval ((2:ℝ)^n * s)) := by
    refine lintegral_congr fun s => ?_
    congr 1
    ring_nf
  have hR : (∑ c ∈ T, hlMax (fun z : ℝ => ψ (-z)) (-x - c))
      = ∑ c' ∈ T.image (fun c => -c), hlMax ψ (x - c') := by
    rw [Finset.sum_image (g := fun c => -c) (f := fun c' => hlMax ψ (x - c'))]
    · refine Finset.sum_congr rfl fun c _ => ?_
      rw [hlMax_reflect]
      congr 1
      ring_nf
    · exact fun a _ b _ hab => neg_injective hab
  rw [hL, hR] at h
  exact h

/-- **HL-domination of the polynomial-curve averages, `+P` form, dilation `2^n`.**  For `P : ℤ[X]` of degree `≥ 2` there are `K > 0` and a finite set `T ⊆ ℝ` such that for EVERY `n : ℕ`, every measurable `ψ : ℝ → ℝ≥0∞` and every `x : ℝ`,
`∫⁻ s in (0,1], ψ (x + P (2^n s)) ≤ K · Σ_{c ∈ T} hlMax ψ (x - c)`.
PROOF PLAN: apply the existing `poly_sup_ge_one_le_hlMax` (in `Maximal/poly_sup_le_finset_hlMax.lean`), which gives `⨆ N, ∫⁻ s in (0,1], ψ (x - q ((N+1)s)) ≤ K Σ_{c∈T} hlMax ψ (x-c)` for `q` nonconstant and nonnegative on `[0,∞)`, to `q' := ε·q + M` where `ε = sign(lead q)` and `M` makes `q' ≥ 0` on `[0,∞)` (such `M` exists since `q` is bounded above or below according to the sign of its leading coefficient; use the behaviour at `+∞` and `isCompact_Icc.exists_isMinOn` on a compact initial segment).  The shift `M` moves the argument by a constant; the case `ε = -1` gives the `+` form directly and the case `ε = +1` is reduced to `ε = -1` by reflecting `ψ` (`ψ̃ y := ψ (-y)`, using `hlMax_reflect` from `poly_dilation_lp.lean`). -/
theorem level_l2_mst_large_n_hl (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) :
    ∃ K : ℝ, 0 < K ∧ ∃ T : Finset ℝ, ∀ (n : ℕ) (ψ : ℝ → ℝ≥0∞), Measurable ψ → ∀ x : ℝ,
      ∫⁻ s in Set.Ioc (0:ℝ) 1,
          ψ (x + (P.map (Int.castRingHom ℝ)).eval ((2:ℝ)^n * s))
        ≤ ENNReal.ofReal K * ∑ c ∈ T, Commons.Analysis.Maximal.hlMax ψ (x - c) := by
  have hqdeg2 : 2 ≤ (P.map (Int.castRingHom ℝ)).natDegree := by
    rw [Polynomial.natDegree_map_eq_of_injective (f := Int.castRingHom ℝ) Int.cast_injective]
    exact hd
  have hqdeg : 1 ≤ (P.map (Int.castRingHom ℝ)).natDegree := by omega
  obtain ⟨ε, hε, M, _hM0, hMnn, hMdeg⟩ :=
    exists_sign_shift_nonneg (P.map (Int.castRingHom ℝ)) hqdeg
  have hreval : ∀ u : ℝ,
      (Polynomial.C ε * (P.map (Int.castRingHom ℝ)) + Polynomial.C M).eval u
        = ε * (P.map (Int.castRingHom ℝ)).eval u + M := by
    intro u; simp
  rcases hε with hε1 | hεm1
  · -- `ε = +1`: the `+` form of `poly_exp_plus_le_hlMax` applies to `q + M`
    obtain ⟨K, hK, T, hT⟩ := poly_exp_plus_le_hlMax hMdeg hMnn
    refine ⟨K, hK, T.image (fun c => c + M), ?_⟩
    intro n ψ hψ x
    have h := hT n ψ hψ (x - M)
    have hL : (∫⁻ s in Set.Ioc (0:ℝ) 1,
          ψ ((x - M) + (Polynomial.C ε * (P.map (Int.castRingHom ℝ)) + Polynomial.C M).eval
            ((2:ℝ)^n * s)))
        = ∫⁻ s in Set.Ioc (0:ℝ) 1,
            ψ (x + (P.map (Int.castRingHom ℝ)).eval ((2:ℝ)^n * s)) := by
      refine lintegral_congr fun s => ?_
      congr 1
      rw [hreval, hε1]
      ring
    have hR : (∑ c ∈ T, hlMax ψ ((x - M) - c))
        = ∑ c' ∈ T.image (fun c => c + M), hlMax ψ (x - c') := by
      rw [Finset.sum_image (g := fun c => c + M) (f := fun c' => hlMax ψ (x - c'))]
      · refine Finset.sum_congr rfl fun c _ => ?_
        congr 1
        ring
      · exact fun a _ b _ hab => by linarith
    rw [hL, hR] at h
    exact h
  · -- `ε = -1`: the `-` form of `poly_exp_minus_le_hlMax` applies to `-q + M`
    obtain ⟨K, hK, T, hT⟩ := poly_exp_minus_le_hlMax hMdeg hMnn
    refine ⟨K, hK, T.image (fun c => c - M), ?_⟩
    intro n ψ hψ x
    have h := hT n ψ hψ (x + M)
    have hL : (∫⁻ s in Set.Ioc (0:ℝ) 1,
          ψ ((x + M) - (Polynomial.C ε * (P.map (Int.castRingHom ℝ)) + Polynomial.C M).eval
            ((2:ℝ)^n * s)))
        = ∫⁻ s in Set.Ioc (0:ℝ) 1,
            ψ (x + (P.map (Int.castRingHom ℝ)).eval ((2:ℝ)^n * s)) := by
      refine lintegral_congr fun s => ?_
      congr 1
      rw [hreval, hεm1]
      ring
    have hR : (∑ c ∈ T, hlMax ψ ((x + M) - c))
        = ∑ c' ∈ T.image (fun c => c - M), hlMax ψ (x - c') := by
      rw [Finset.sum_image (g := fun c => c - M) (f := fun c' => hlMax ψ (x - c'))]
      · refine Finset.sum_congr rfl fun c _ => ?_
        congr 1
        ring
      · exact fun a _ b _ hab => by linarith
    rw [hL, hR] at h
    exact h

end Work.BourgainPlan.Maximal
