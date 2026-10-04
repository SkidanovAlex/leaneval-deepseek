import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.periodization_contDiff_periodic
import Submission.Work.Diff.STE.continuous_pdVec
import Submission.Work.Diff.STE.B3.CSq_period_comp_arg_le
import Submission.Work.Diff.STE.B3.CSq_period_comp_arg_le_of_isOpen
import Submission.Work.Diff.STE.B3.integral_pd_comp_le
import Submission.Work.Diff.STE.B3.pdVec_integral_le_CSq
import Submission.Work.Diff.STE.B3.CSq_period_le_integral_deriv
import Submission.Work.Diff.STE.B3.pdVecMulCompExpansion
import Submission.Work.Diff.STE.B3.integralCompPeriodicLe
import Submission.Work.Diff.STE.B3.integral_pd_comp_le_nodim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory BigOperators

set_option maxHeartbeats 1000000

namespace Work.Diff.STE.B3

noncomputable section

/-- **The globally smooth chart-transfer estimate, with no restriction on `card ι` against `2 s`.**

This is `Work.Diff.STE.B3.CSq_period_comp_arg_le_uniform` with the sup bound on `u` removed: the
Sobolev embedding `Work.Diff.STE.norm_seriesFun_le` (and hence the hypothesis `Fintype.card ι < 2 * s`)
is not needed, because the order-`0` summand of the chain-rule expansion is controlled by the
change-of-variables estimate `Work.Diff.STE.B3.integralCompPeriodicLe`, which needs no sup bound —
that is exactly the content of `integral_pd_comp_le_nodim`. -/
theorem CSq_period_comp_arg_le_nodim_global {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ)
    (T : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfsupp : Function.support f ⊆ Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (U : Set (ι → ℝ)) (hU : IsOpen U) (hUf : tsupport f ⊆ U)
    (hinj : Set.InjOn T U) (hdet : ∀ z ∈ U, (fderiv ℝ T z).det ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z => ∑' k : ι → ℤ,
        f (z + Work.Diff.STE.iVec k) * u (T (z + Work.Diff.STE.iVec k))))
        ≤ C * (1 + Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff u)) := by
  classical
  obtain ⟨C0, hC0nn, hC0b⟩ := CSq_period_le_integral_deriv (ι := ι) s
  obtain ⟨C1, hC1nn, hC1b⟩ := pdVec_integral_le_CSq (ι := ι) s
  choose Cd hCdnn hCdb using fun (m : ℕ) (l : Fin m → ι) =>
    integral_pd_comp_le_nodim (ι := ι) T hT f hf hfsupp U hU hUf hinj hdet m l
  set N2 : ℝ := ∑ m ∈ Finset.range (s + 1), ∑ _l : Fin m → ι, (1 : ℝ) with hN2def
  set N3 : ℝ := ∑ m ∈ Finset.range (s + 1), ∑ l : Fin m → ι, Cd m l with hN3def
  have hN2nn : 0 ≤ N2 := by
    rw [hN2def]
    exact Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun _ _ => by norm_num
  have hN3nn : 0 ≤ N3 := by
    rw [hN3def]
    exact Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun l _ => hCdnn m l
  refine ⟨C0 * N3 * (N2 * C1),
    mul_nonneg (mul_nonneg hC0nn hN3nn) (mul_nonneg hN2nn hC1nn), ?_⟩
  intro u hu hup
  set φ : (ι → ℝ) → ℂ := fun z => f z * u (T z) with hφdef
  have hφsm : ContDiff ℝ (⊤ : ℕ∞) φ := hf.mul (hu.comp hT)
  have hφsupp : Function.support φ ⊆
      Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro z hz
    refine hfsupp (fun h0 => hz ?_)
    show f z * u (T z) = 0
    rw [h0, zero_mul]
  have hC3b := hC0b φ hφsm hφsupp
  set S : ℝ := ∑ j ∈ Finset.range (s + 1), ∑ l' : Fin j → ι,
    ∫ x in unitCube (ι := ι), ‖pdVec j l' u x‖ ^ 2 with hSdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun l' _ => integral_nonneg fun x => sq_nonneg _
  have hkey : ∀ (m : ℕ) (hm : m ≤ s) (l : Fin m → ι),
      ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2 ≤ Cd m l * S := by
    intro m hm l
    have h1 := hCdb m l u hu hup
    have h2 : (∑ j ∈ Finset.range (m + 1), ∑ l' : Fin j → ι,
        ∫ x in unitCube (ι := ι), ‖pdVec j l' u x‖ ^ 2) ≤ S := by
      rw [hSdef]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro j hj
        rw [Finset.mem_range] at hj ⊢
        omega
      · intro j _ _
        exact Finset.sum_nonneg fun l' _ => integral_nonneg fun x => sq_nonneg _
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (hCdnn m l))
  have hsum1 : (∑ m ∈ Finset.range (s + 1), ∑ l : Fin m → ι,
      ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2) ≤ N3 * S := by
    calc (∑ m ∈ Finset.range (s + 1), ∑ l : Fin m → ι,
          ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2)
        ≤ ∑ m ∈ Finset.range (s + 1), ∑ l : Fin m → ι, Cd m l * S :=
          Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun l _ =>
            hkey m (by have := Finset.mem_range.mp hm; omega) l
      _ = N3 * S := by
          rw [hN3def, Finset.sum_mul]
          exact Finset.sum_congr rfl fun m _ => by rw [Finset.sum_mul]
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
  have hCSq' : CSq s (fourierCoeff (fun z => ∑' m : ι → ℤ,
      f (z + iVec m) * u (T (z + iVec m))))
      = CSq s (fourierCoeff (fun z => ∑' m : ι → ℤ, φ (z + iVec m))) := by
    rw [hφdef]
  rw [hCSq']
  refine hC3b.trans ?_
  have hCSqnn : 0 ≤ CSq s (fourierCoeff u) := CSq_nonneg s _
  calc C0 * (∑ m ∈ Finset.range (s + 1), ∑ l : Fin m → ι,
        ∫ x : ι → ℝ, ‖pdVec m l φ x‖ ^ 2)
      ≤ C0 * (N3 * S) := mul_le_mul_of_nonneg_left hsum1 hC0nn
    _ ≤ C0 * (N3 * (N2 * (C1 * CSq s (fourierCoeff u)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsum2 hN3nn) hC0nn
    _ = C0 * N3 * (N2 * C1) * CSq s (fourierCoeff u) := by ring
    _ ≤ C0 * N3 * (N2 * C1) * (1 + CSq s (fourierCoeff u)) :=
        mul_le_mul_of_nonneg_left (by linarith)
          (mul_nonneg (mul_nonneg hC0nn hN3nn) (mul_nonneg hN2nn hC1nn))

/-- **The chart-transfer estimate on `Hˢ`, with NO restriction on `card ι` against `2 s`.**

`Work.Diff.STE.B3.CSq_period_comp_arg_le_of_isOpen` proves exactly this estimate but only under
the extra hypothesis `Fintype.card ι < 2 * s`, because its proof bounds `u` in sup norm via the
Sobolev embedding `Work.Diff.STE.norm_seriesFun_le`, which is available only in that range
(`s > card ι / 2`).  That restriction is an artefact of the *proof*: the sup bound enters only
through the `B^2` summand of `Work.Diff.STE.B3.integral_pd_comp_le` (whose conclusion is
`∫ ‖∂^m (f · u ∘ T)‖² ≤ C * (B^2 + H)`, `H = Σ_{j ≤ m} Σ_{l'} ∫_{unitCube} ‖∂^{l'} u‖²`), and the
order-`0` terms of the chain-rule expansion (`ord i = 0`, i.e. `u` itself, produced by
`Work.Diff.STE.B3.pdVecMulCompExpansion`) are controlled by the change-of-variables result
`Work.Diff.STE.B3.integralCompPeriodicLe`, which needs no sup bound.

Route (this file may contain any auxiliary results it needs; the final declaration must be as
below):

1. Copy `Work.Diff.STE.B3.integral_pd_comp_le` and state the conclusion *without* the `B`:
   `∃ C ≥ 0, ∀ u, ContDiff ℝ ⊤ u → Periodic1 u →
      ∫ z, ‖pdVec m l (fun z => f z * u (T z)) z‖^2
        ≤ C * ∑ j ∈ range (m+1), ∑ l' : Fin j → ι, ∫ x in unitCube, ‖pdVec j l' u x‖^2`.
   The proof of the library result already reaches `M * (Cj * H)` (`step1` … `step6` followed by
   `mul_le_mul_of_nonneg_left step6 hMnn`); only the final arithmetic step `hMH` — the one that
   introduces `B` — is dropped.  `C = max 1 (M * Cj)` works.
2. Copy `Work.Diff.STE.B3.CSq_period_comp_arg_le` and drop the sup bound `B0` (hence
   `norm_seriesFun_le` and the hypothesis `hs`): with `S = Σ_{j ≤ s} Σ_{l'} ∫_{unitCube} ‖∂^{l'} u‖²`
   one gets `CSq s (fourierCoeff (per (f · (u ∘ T)))) ≤ C0 * N3 * S` and
   `S ≤ N2 * C1 * CSq s (fourierCoeff u)` from `pdVec_integral_le_CSq`.
3. The `of_isOpen` version: copy `Work.Diff.STE.B3.CSq_period_comp_arg_le_of_isOpen`, which
   regularises `T` (only smooth on the open `U`) to `z ↦ φ z • T z` by
   `Work.Diff.STE.B3.exists_bump_open_nhds` (already proved) and then applies the globally smooth
   version of step 2; the two periodisations agree because `f (z + m) ≠ 0` forces
   `z + m ∈ tsupport f ⊆ V`, where `φ = 1`.

Intended full name: `Work.Diff.STE.B3.CSq_period_comp_arg_le_nodim_of_isOpen`
(namespace `Work.Diff.STE.B3`); the auxiliary results may live in the same file under any names. -/
theorem CSq_period_comp_arg_le_nodim_of_isOpen {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ℕ) (T : (ι → ℝ) → (ι → ℝ))
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfsupp : Function.support f ⊆
      Set.pi Set.univ (fun _ : ι => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)))
    (hK : IsCompact (tsupport f))
    (U : Set (ι → ℝ)) (hU : IsOpen U) (hUf : tsupport f ⊆ U)
    (hT : ∀ z ∈ U, ContDiffAt ℝ (⊤ : ℕ∞) T z)
    (hinj : Set.InjOn T U)
    (hdet : ∀ z ∈ U, (fderiv ℝ T z).det ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : (ι → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun z => ∑' m : ι → ℤ,
        f (z + Work.Diff.STE.iVec m) * u (T (z + Work.Diff.STE.iVec m))))
        ≤ C * (1 + Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff u)) := by
  classical
  -- `T` is `C^∞` on the whole open set `U` (the hypothesis is pointwise)
  have hTon : ContDiffOn ℝ (⊤ : ℕ∞) T U := fun z hz => (hT z hz).contDiffWithinAt
  -- a bump `φ`, equal to `1` on an open neighbourhood `V` of `tsupport f` contained in `U`,
  -- which regularises `T` to a globally smooth `x ↦ φ x • T x`
  obtain ⟨φ, V, hφsm, hVopen, hKV, hVU, hφone, hφsupp, hφTsm⟩ :=
    exists_bump_open_nhds (tsupport f) U hK hU hUf T hTon
  -- on the *open* set `V` the regularised map agrees with `T`, so it inherits injectivity
  have hinj' : Set.InjOn (fun z => φ z • T z) V := by
    intro x hx y hy hxy
    refine hinj (hVU hx) (hVU hy) ?_
    have h1 : φ x • T x = φ y • T y := hxy
    simpa only [hφone x hx, hφone y hy, one_smul] using h1
  -- and the invertibility of the Jacobian
  have hdet' : ∀ z ∈ V, (fderiv ℝ (fun z => φ z • T z) z).det ≠ 0 := by
    intro z hz
    have hev : (fun w => φ w • T w) =ᶠ[nhds z] T := by
      filter_upwards [hVopen.mem_nhds hz] with w hw
      rw [hφone w hw, one_smul]
    rw [hev.fderiv_eq]
    exact hdet z (hVU hz)
  obtain ⟨C, hCnn, hCb⟩ :=
    CSq_period_comp_arg_le_nodim_global (ι := ι) s (fun z => φ z • T z) hφTsm f hf hfsupp
      V hVopen hKV hinj' hdet'
  refine ⟨C, hCnn, fun u hu hup => ?_⟩
  -- the two periodisations agree term by term, because `f (z + m) ≠ 0` forces
  -- `z + m ∈ Function.support f ⊆ tsupport f ⊆ V`, where `T` and `φ • T` coincide
  have hfun : (fun z : ι → ℝ => ∑' m : ι → ℤ,
        f (z + Work.Diff.STE.iVec m) * u (T (z + Work.Diff.STE.iVec m)))
      = (fun z : ι → ℝ => ∑' m : ι → ℤ,
        f (z + Work.Diff.STE.iVec m)
          * u (φ (z + Work.Diff.STE.iVec m) • T (z + Work.Diff.STE.iVec m))) := by
    funext z
    refine tsum_congr fun m => ?_
    by_cases hfm : f (z + Work.Diff.STE.iVec m) = 0
    · rw [hfm, zero_mul, zero_mul]
    · have hmem : z + Work.Diff.STE.iVec m ∈ tsupport f :=
        subset_tsupport f (Function.mem_support.mpr hfm)
      rw [show φ (z + Work.Diff.STE.iVec m) = 1 from hφone _ (hKV hmem), one_smul]
  rw [hfun]
  exact hCb u hu hup

end

end Work.Diff.STE.B3
