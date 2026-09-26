/-
# Two-variable moderate growth on `ℍ × ℍ`

The dominator for the CKMRV contour integral

  `t ↦ K(τ, it) e^{-πr²t}`

has to be *locally uniform in `τ`* and *polynomial in `t`*, so what is needed about the kernel
is not merely moderate growth in each variable separately (which is what
`Work.Kernels.KernelGrowth` provides, with constants depending on the other variable), but a
bound of the shape

  `‖F τ z‖ ≤ α * (scale τ)^N * (scale z)^M`

with constants independent of `τ` and `z`.  This file introduces that class and its calculus.

## Main definitions

* `Work.Asymptotics.ModerateGrowth2 F` : two-variable moderate growth of `F : ℍ → ℍ → ℂ`.

## Main results

* the closure of `ModerateGrowth2` under constants, addition, negation, subtraction,
  multiplication, scalar multiples, finite sums and products, and powers;
* `Work.Asymptotics.ModerateGrowth2.of_fst`, `of_snd` : one-variable moderate growth of a
  factor gives two-variable moderate growth of the corresponding product;
* `Work.Asymptotics.ModerateGrowth2.of_fst_InP`, `of_snd_InP` : the same starting from `𝒫`.

The concrete kernel instances (`Work.Asymptotics.KfunClear_mg2`,
`Work.Asymptotics.KhatClear_mg2`) and the resulting pointwise divisor bound
(`Work.Asymptotics.norm_Kfun_le_of_divisor`) are the interface used by
`Work.Asymptotics.Holomorphy`.
-/
import Mathlib
import Submission.Work.Kernels.All

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix MeasureTheory
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels

/-- **Two-variable moderate growth** on `ℍ × ℍ`: the bound
`‖F τ z‖ ≤ α * (scale τ)^N * (scale z)^M` with `α, N, M ≥ 0`. -/
def ModerateGrowth2 (F : ℍ → ℍ → ℂ) : Prop :=
  ∃ α N M : ℝ, 0 ≤ α ∧ 0 ≤ N ∧ 0 ≤ M ∧
    ∀ τ z : ℍ, ‖F τ z‖ ≤ α * (scale τ) ^ N * (scale z) ^ M

namespace ModerateGrowth2

variable {F G : ℍ → ℍ → ℂ}

lemma const (c : ℂ) : ModerateGrowth2 (fun _ _ : ℍ => c) :=
  ⟨‖c‖, 0, 0, norm_nonneg c, le_rfl, le_rfl, fun τ z => by
    simp only [Real.rpow_zero, mul_one]
    linarith [norm_nonneg c]⟩

lemma zero : ModerateGrowth2 (fun _ _ : ℍ => (0 : ℂ)) := const 0

lemma one : ModerateGrowth2 (fun _ _ : ℍ => (1 : ℂ)) := const 1

lemma add (hF : ModerateGrowth2 F) (hG : ModerateGrowth2 G) :
    ModerateGrowth2 (fun τ z => F τ z + G τ z) := by
  obtain ⟨α, N, M, hα, hN, hM, hF⟩ := hF
  obtain ⟨α', N', M', hα', hN', hM', hG⟩ := hG
  refine ⟨α + α', max N N', max M M', by positivity, le_max_of_le_left hN,
    le_max_of_le_left hM, fun τ z => ?_⟩
  have hτ1 : (scale τ) ^ N ≤ (scale τ) ^ (max N N') :=
    Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) (le_max_left N N')
  have hτ2 : (scale τ) ^ N' ≤ (scale τ) ^ (max N N') :=
    Real.rpow_le_rpow_of_exponent_le (one_le_scale τ) (le_max_right N N')
  have hz1 : (scale z) ^ M ≤ (scale z) ^ (max M M') :=
    Real.rpow_le_rpow_of_exponent_le (one_le_scale z) (le_max_left M M')
  have hz2 : (scale z) ^ M' ≤ (scale z) ^ (max M M') :=
    Real.rpow_le_rpow_of_exponent_le (one_le_scale z) (le_max_right M M')
  have hτs : (0:ℝ) ≤ (scale τ) ^ (max N N') := Real.rpow_nonneg (scale_pos τ).le _
  have hzs : (0:ℝ) ≤ (scale z) ^ (max M M') := Real.rpow_nonneg (scale_pos z).le _
  have h1 : α * (scale τ) ^ N * (scale z) ^ M
      ≤ α * (scale τ) ^ (max N N') * (scale z) ^ (max M M') := by
    have : α * (scale τ) ^ N ≤ α * (scale τ) ^ (max N N') :=
      mul_le_mul_of_nonneg_left hτ1 hα
    calc α * (scale τ) ^ N * (scale z) ^ M
        ≤ α * (scale τ) ^ (max N N') * (scale z) ^ M := by
          exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (scale_pos z).le M)
      _ ≤ α * (scale τ) ^ (max N N') * (scale z) ^ (max M M') :=
          mul_le_mul_of_nonneg_left hz1 (by positivity)
  have h2 : α' * (scale τ) ^ N' * (scale z) ^ M'
      ≤ α' * (scale τ) ^ (max N N') * (scale z) ^ (max M M') := by
    have : α' * (scale τ) ^ N' ≤ α' * (scale τ) ^ (max N N') :=
      mul_le_mul_of_nonneg_left hτ2 hα'
    calc α' * (scale τ) ^ N' * (scale z) ^ M'
        ≤ α' * (scale τ) ^ (max N N') * (scale z) ^ M' := by
          exact mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (scale_pos z).le M')
      _ ≤ α' * (scale τ) ^ (max N N') * (scale z) ^ (max M M') :=
          mul_le_mul_of_nonneg_left hz2 (by positivity)
  calc ‖F τ z + G τ z‖ ≤ ‖F τ z‖ + ‖G τ z‖ := norm_add_le _ _
    _ ≤ α * (scale τ) ^ N * (scale z) ^ M + α' * (scale τ) ^ N' * (scale z) ^ M' :=
        add_le_add (hF τ z) (hG τ z)
    _ ≤ (α + α') * (scale τ) ^ (max N N') * (scale z) ^ (max M M') := by
        rw [add_mul, add_mul]; exact add_le_add h1 h2

lemma neg (hF : ModerateGrowth2 F) : ModerateGrowth2 (fun τ z => -F τ z) := by
  obtain ⟨α, N, M, hα, hN, hM, hF⟩ := hF
  exact ⟨α, N, M, hα, hN, hM, fun τ z => by simpa using hF τ z⟩

lemma sub (hF : ModerateGrowth2 F) (hG : ModerateGrowth2 G) :
    ModerateGrowth2 (fun τ z => F τ z - G τ z) := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

lemma const_mul (c : ℂ) (hF : ModerateGrowth2 F) :
    ModerateGrowth2 (fun τ z => c * F τ z) := by
  obtain ⟨α, N, M, hα, hN, hM, hF⟩ := hF
  refine ⟨‖c‖ * α, N, M, by positivity, hN, hM, fun τ z => ?_⟩
  rw [norm_mul]
  calc ‖c‖ * ‖F τ z‖ ≤ ‖c‖ * (α * (scale τ) ^ N * (scale z) ^ M) :=
        mul_le_mul_of_nonneg_left (hF τ z) (norm_nonneg c)
    _ = ‖c‖ * α * (scale τ) ^ N * (scale z) ^ M := by ring

lemma mul (hF : ModerateGrowth2 F) (hG : ModerateGrowth2 G) :
    ModerateGrowth2 (fun τ z => F τ z * G τ z) := by
  obtain ⟨α, N, M, hα, hN, hM, hF⟩ := hF
  obtain ⟨α', N', M', hα', hN', hM', hG⟩ := hG
  refine ⟨α * α', N + N', M + M', by positivity, by positivity, by positivity, fun τ z => ?_⟩
  rw [norm_mul, Real.rpow_add (scale_pos τ), Real.rpow_add (scale_pos z)]
  have h1 := hF τ z
  have h2 := hG τ z
  have hτN : (0:ℝ) ≤ (scale τ) ^ N := Real.rpow_nonneg (scale_pos τ).le N
  have hτN' : (0:ℝ) ≤ (scale τ) ^ N' := Real.rpow_nonneg (scale_pos τ).le N'
  have hzM : (0:ℝ) ≤ (scale z) ^ M := Real.rpow_nonneg (scale_pos z).le M
  have hzM' : (0:ℝ) ≤ (scale z) ^ M' := Real.rpow_nonneg (scale_pos z).le M'
  calc ‖F τ z‖ * ‖G τ z‖
      ≤ (α * (scale τ) ^ N * (scale z) ^ M) * (α' * (scale τ) ^ N' * (scale z) ^ M') :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = α * α' * ((scale τ) ^ N * (scale τ) ^ N') * ((scale z) ^ M * (scale z) ^ M') := by ring

lemma sum {ι : Type*} (s : Finset ι) (h : ∀ i ∈ s, ModerateGrowth2 (fun τ z => F τ z))
    {g : ι → ℍ → ℍ → ℂ} (hg : ∀ i ∈ s, ModerateGrowth2 (g i)) :
    ModerateGrowth2 (fun τ z => ∑ i ∈ s, g i τ z) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (zero : ModerateGrowth2 (fun _ _ : ℍ => (0 : ℂ)))
  | insert i s hi ih =>
      have hsplit : (fun τ z => ∑ x ∈ insert i s, g x τ z)
          = fun τ z => g i τ z + ∑ x ∈ s, g x τ z := by
        funext τ z; rw [Finset.sum_insert hi]
      rw [hsplit]
      exact (hg i (Finset.mem_insert_self i s)).add
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
          (fun j hj => hg j (Finset.mem_insert_of_mem hj)))

lemma of_fst {f : ℍ → ℂ} (h : ModerateGrowthOn Set.univ f) :
    ModerateGrowth2 (fun τ _ : ℍ => f τ) := by
  obtain ⟨α, N, hα, hN, h⟩ := (moderateGrowthOn_iff_scale Set.univ f).mp h
  refine ⟨α, N, 0, hα, hN, le_rfl, fun τ z => ?_⟩
  simpa [Real.rpow_zero] using h τ (Set.mem_univ τ)

lemma of_snd {f : ℍ → ℂ} (h : ModerateGrowthOn Set.univ f) :
    ModerateGrowth2 (fun _ z : ℍ => f z) := by
  obtain ⟨α, N, hα, hN, h⟩ := (moderateGrowthOn_iff_scale Set.univ f).mp h
  refine ⟨α, 0, N, hα, le_rfl, hN, fun τ z => ?_⟩
  simpa [Real.rpow_zero] using h z (Set.mem_univ z)

lemma of_fst_InP {f : ℍ → ℂ} (h : InP f) : ModerateGrowth2 (fun τ _ : ℍ => f τ) :=
  of_fst h.2

lemma of_snd_InP {f : ℍ → ℂ} (h : InP f) : ModerateGrowth2 (fun _ z : ℍ => f z) :=
  of_snd h.2

end ModerateGrowth2

end Work.Asymptotics
