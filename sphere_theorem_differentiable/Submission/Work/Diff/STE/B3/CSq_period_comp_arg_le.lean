/-
# The chart-transfer estimate: `Hˢ` of a composite `f · (u ∘ T)` is controlled by `Hˢ` of `u`

This is the linchpin of Layer B3 (see `DESIGN.md`, SESSION 8): the cross-chart components of the
Friedrichs mollifier `J ρ ε` are sums of terms `(smooth) · (u ∘ T)` where `T` is a *chart
transition* (a smooth diffeomorphism of a neighbourhood of the support) and `u` is a component of
the section.  Every estimate on `J` therefore needs

  `CSq s (fourierCoeff (periodisation of z ↦ f z * u (T z))) ≤ C (1 + CSq s (fourierCoeff u))`.

The proof composes the three proved layers:

* `CSq_period_le_integral_deriv` : `CSq s (fourierCoeff (per φ)) ≤ C Σ_{|α| ≤ s} ∫ ‖∂^α φ‖²`;
* `integral_pd_comp_le` : the chain rule with a *single* composition plus the change of variables
  `y = T z`, which gives `∫ ‖∂^α (f · (u ∘ T))‖² ≤ C (B² + Σ_{|β| ≤ |α|} ∫_{cube} ‖∂^β u‖²)`;
* `pdVec_integral_le_CSq` : `∫_{cube} ‖∂^β u‖² ≤ C CSq s (fourierCoeff u)` for `|β| ≤ s`.

The sup bound `B` for `u` is supplied by the Sobolev embedding
`Work.Diff.STE.norm_seriesFun_le` (hence the hypothesis `card ι < 2 s`).
-/
import Mathlib
import Submission.Work.Diff.STE.B3.pdVec_integral_le_CSq
import Submission.Work.Diff.STE.B3.CSq_period_le_integral_deriv
import Submission.Work.Diff.STE.B3.integral_pd_comp_le
import Submission.Work.Diff.STE.norm_seriesFun_le
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory BigOperators

set_option maxHeartbeats 1000000

namespace Work.Diff.STE.B3

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The chart-transfer estimate.**  For a smooth `T` which is a diffeomorphism on a neighbourhood
`U` of the support of the smooth, compactly supported `f`, and for a smooth `1`-periodic `u`, the
`Hˢ` norm of the periodisation of `z ↦ f z * u (T z)` is controlled by `1 + Hˢ(u)`. -/
theorem CSq_period_comp_arg_le (s : ℕ) (hs : Fintype.card ι < 2 * s)
    (T : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfsupp : Function.support f ⊆
      Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (U : Set (ι → ℝ)) (hU : IsOpen U) (hUf : tsupport f ⊆ U)
    (hinj : Set.InjOn T U) (hdet : ∀ z ∈ U, (fderiv ℝ T z).det ≠ 0)
    (u : (ι → ℝ) → ℂ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hup : Periodic1 u) :
    ∃ C : ℝ, 0 ≤ C ∧
      CSq s (fourierCoeff (fun z => ∑' m : ι → ℤ,
          f (z + iVec m) * u (T (z + iVec m))))
        ≤ C * (1 + CSq s (fourierCoeff u)) := by
  classical
  obtain ⟨C0, hC0nn, hC0b⟩ := CSq_period_le_integral_deriv (ι := ι) s
  obtain ⟨C1, hC1nn, hC1b⟩ := pdVec_integral_le_CSq (ι := ι) s
  obtain ⟨C2, hC2nn, hC2b⟩ := norm_seriesFun_le (ι := ι) s hs
  choose Cd hCdnn hCdb using fun (m : ℕ) (l : Fin m → ι) =>
    integral_pd_comp_le (ι := ι) T hT f hf hfsupp U hU hUf hinj hdet m l
  -- the composite `φ` and the two hypotheses of `CSq_period_le_integral_deriv`
  set φ : (ι → ℝ) → ℂ := fun z => f z * u (T z) with hφdef
  have hφsm : ContDiff ℝ (⊤ : ℕ∞) φ := hf.mul (hu.comp hT)
  have hφsupp : Function.support φ ⊆
      Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    refine hfsupp (fun h0 => hz ?_)
    show f z * u (T z) = 0
    rw [h0, zero_mul]
  have hC3b := hC0b φ hφsm hφsupp
  -- the sup bound on `u`
  have hsumu : Summable (fun k : ι → ℤ => (wt k) ^ s * ‖fourierCoeff u k‖ ^ 2) :=
    summable_weighted_fourierCoeff_of_contDiff u hu hup s
  set B0 : ℝ := C2 * Real.sqrt (CSq s (fourierCoeff u)) with hB0def
  have hCSqunn : 0 ≤ CSq s (fourierCoeff u) := CSq_nonneg s _
  have hsup : ∀ x, ‖u x‖ ≤ B0 := by
    intro x
    rw [← flat.seriesFun_fourierCoeff u hu hup x]
    exact hC2b _ hsumu x
  have hB0sq : B0 ^ 2 = C2 ^ 2 * CSq s (fourierCoeff u) := by
    rw [hB0def, mul_pow, Real.sq_sqrt hCSqunn]
  -- the constants attached to the (finitely many) multi-indices
  set N2 : ℝ := ∑ m ∈ Finset.range (s + 1), ∑ _l : Fin m → ι, (1 : ℝ) with hN2def
  set N3 : ℝ := ∑ m ∈ Finset.range (s + 1), ∑ l : Fin m → ι, Cd m l with hN3def
  have hN2nn : 0 ≤ N2 := by
    rw [hN2def]
    exact Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun _ _ => by norm_num
  have hN3nn : 0 ≤ N3 := by
    rw [hN3def]
    exact Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun l _ => hCdnn m l
  -- the `∫_{cube}` version of the right-hand side of the transfer
  set S : ℝ := ∑ j ∈ Finset.range (s + 1), ∑ l' : Fin j → ι,
    ∫ x in unitCube (ι := ι), ‖pdVec j l' u x‖ ^ 2 with hSdef
  -- the bound on each individual `∫ ‖∂^α φ‖²`
  have hkey : ∀ (m : ℕ) (hm : m ≤ s) (l : Fin m → ι),
      ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2 ≤ Cd m l * (B0 ^ 2 + S) := by
    intro m hm l
    have h1 := hCdb m l u B0 hu hup hsup
    have h2 : (∑ j ∈ Finset.range (m + 1), ∑ l' : Fin j → ι,
        ∫ x in unitCube (ι := ι), ‖pdVec j l' u x‖ ^ 2) ≤ S := by
      rw [hSdef]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro j hj
        rw [Finset.mem_range] at hj ⊢
        omega
      · intro j _ _
        exact Finset.sum_nonneg fun l' _ => integral_nonneg fun x => sq_nonneg _
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCdnn m l)
    linarith
  -- the sum over all multi-indices of length `≤ s`
  have hsum1 : (∑ m ∈ Finset.range (s + 1), ∑ l : Fin m → ι,
      ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2) ≤ N3 * (B0 ^ 2 + S) := by
    calc (∑ m ∈ Finset.range (s + 1), ∑ l : Fin m → ι,
          ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2)
        ≤ ∑ m ∈ Finset.range (s + 1), ∑ l : Fin m → ι, Cd m l * (B0 ^ 2 + S) :=
          Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun l _ =>
            hkey m (by have := Finset.mem_range.mp hm; omega) l
      _ = N3 * (B0 ^ 2 + S) := by
          rw [hN3def, Finset.sum_mul]
          exact Finset.sum_congr rfl fun m _ => by rw [Finset.sum_mul]
  -- the `∫_{cube}` bounds at the top order
  have hsum2 : S ≤ N2 * (C1 * CSq s (fourierCoeff u)) := by
    calc S = ∑ j ∈ Finset.range (s + 1), ∑ l' : Fin j → ι,
          ∫ x in unitCube (ι := ι), ‖pdVec j l' u x‖ ^ 2 := hSdef
      _ ≤ ∑ j ∈ Finset.range (s + 1), ∑ l' : Fin j → ι,
            C1 * CSq s (fourierCoeff u) :=
          Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun l' _ =>
            hC1b u hu hup j (by have := Finset.mem_range.mp hj; omega) l'
      _ = N2 * (C1 * CSq s (fourierCoeff u)) := by
          rw [hN2def, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun l' _ => by ring
  -- assemble
  have hK : 0 ≤ C2 ^ 2 + N2 * C1 := add_nonneg (sq_nonneg C2) (mul_nonneg hN2nn hC1nn)
  refine ⟨C0 * (N3 + 1) * (C2 ^ 2 + N2 * C1 + 1),
    mul_nonneg (mul_nonneg hC0nn (by linarith))
      (by linarith [hK]), ?_⟩
  have hCSq' : CSq s (fourierCoeff (fun z => ∑' m : ι → ℤ,
      f (z + iVec m) * u (T (z + iVec m))))
      = CSq s (fourierCoeff (fun z => ∑' m : ι → ℤ, φ (z + iVec m))) := by
    rw [hφdef]
  rw [hCSq']
  refine (hC3b.trans ?_)
  have hBS : B0 ^ 2 + S ≤ (C2 ^ 2 + N2 * C1) * CSq s (fourierCoeff u) := by
    calc B0 ^ 2 + S
        ≤ C2 ^ 2 * CSq s (fourierCoeff u) + N2 * (C1 * CSq s (fourierCoeff u)) := by
          rw [hB0sq]
          exact add_le_add (le_refl _) hsum2
      _ = (C2 ^ 2 + N2 * C1) * CSq s (fourierCoeff u) := by ring
  have hmain : (∑ m ∈ Finset.range (s + 1), ∑ l : Fin m → ι,
      ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2)
      ≤ (N3 + 1) * (C2 ^ 2 + N2 * C1 + 1) * (1 + CSq s (fourierCoeff u)) := by
    refine hsum1.trans ?_
    have hN3' : N3 * (B0 ^ 2 + S)
        ≤ N3 * ((C2 ^ 2 + N2 * C1) * CSq s (fourierCoeff u)) :=
      mul_le_mul_of_nonneg_left hBS hN3nn
    refine hN3'.trans ?_
    have hstep : N3 * ((C2 ^ 2 + N2 * C1) * CSq s (fourierCoeff u))
        ≤ (N3 + 1) * (C2 ^ 2 + N2 * C1 + 1) * (1 + CSq s (fourierCoeff u)) := by
      have hA1 : N3 ≤ N3 + 1 := by linarith
      have hA2 : C2 ^ 2 + N2 * C1 ≤ C2 ^ 2 + N2 * C1 + 1 := by linarith
      have hA3 : CSq s (fourierCoeff u) ≤ 1 + CSq s (fourierCoeff u) := by linarith
      have hB1 : 0 ≤ (N3 + 1) * (C2 ^ 2 + N2 * C1 + 1) :=
        mul_nonneg (by linarith) (by linarith)
      calc N3 * ((C2 ^ 2 + N2 * C1) * CSq s (fourierCoeff u))
          = (N3 * (C2 ^ 2 + N2 * C1)) * CSq s (fourierCoeff u) := by ring
        _ ≤ ((N3 + 1) * (C2 ^ 2 + N2 * C1 + 1)) * (1 + CSq s (fourierCoeff u)) := by
            refine mul_le_mul ?_ hA3 hCSqunn hB1
            exact mul_le_mul hA1 hA2 hK (by linarith)
        _ = (N3 + 1) * (C2 ^ 2 + N2 * C1 + 1) * (1 + CSq s (fourierCoeff u)) := by ring
    exact hstep
  calc C0 * (∑ m ∈ Finset.range (s + 1), ∑ l : Fin m → ι,
        ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2)
      ≤ C0 * ((N3 + 1) * (C2 ^ 2 + N2 * C1 + 1) * (1 + CSq s (fourierCoeff u))) :=
        mul_le_mul_of_nonneg_left hmain hC0nn
    _ = C0 * (N3 + 1) * (C2 ^ 2 + N2 * C1 + 1) * (1 + CSq s (fourierCoeff u)) := by ring

end

end Work.Diff.STE.B3
