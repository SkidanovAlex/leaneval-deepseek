import Mathlib
import Submission.Work.Diff.STE.B3.LowJetDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold Bundle Topology BigOperators Matrix
open Bundle

namespace Work.Diff.STE.B3

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

theorem Mf_sandwich
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (lam K : ℝ) (hlam : 0 < lam) (hK : 0 < K)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
    (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
    (z : Fin (Module.finrank ℝ E) → ℝ) (hz : ‖z‖ ≤ 2 * D.σ j) :
    (∀ a b, Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b
        = Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z b a) ∧
    (∀ x : Fin (Module.finrank ℝ E) → ℝ,
        lam * ‖x‖ ^ 2 ≤ ∑ a, ∑ b,
          x a * Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b * x b) ∧
    (∀ a b, |Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b| ≤ K) ∧
    (Matrix.of (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z)).det ≠ 0 := by
  classical
  set xp : M := D.pt j z with hxp
  set Ea : Fin (Module.finrank ℝ E) → TangentSpace I xp := fun a => D.e j a xp with hEa
  have hmn : ∀ a b, Mf (I := I) (M := M) D h j z a b = h xp (Ea a) (Ea b) := fun a b => rfl
  have hON : ∀ a b : Fin (Module.finrank ℝ E),
      g₀.inner xp (Ea a) (Ea b) = if a = b then 1 else 0 := D.heON j z hz
  -- the nonnegativity of the diagonal of `h` at `xp`
  have hnn : ∀ w : TangentSpace I xp, 0 ≤ h xp w w := by
    intro w
    have hg : 0 ≤ g₀.inner xp w w := by
      rcases eq_or_ne w 0 with rfl | hw
      · simp
      · exact le_of_lt (g₀.pos xp w hw)
    exact le_trans (mul_nonneg hlam.le hg) (hell xp w)
  -- the bilinear expansion of the quadratic form of `h` in the frame
  have hform : ∀ (B : TangentSpace I xp →L[ℝ] TangentSpace I xp →L[ℝ] ℝ)
      (ξ : Fin (Module.finrank ℝ E) → ℝ),
      B (∑ a, ξ a • Ea a) (∑ b, ξ b • Ea b)
        = ∑ a, ∑ b, ξ a * B (Ea a) (Ea b) * ξ b := by
    intro B ξ
    simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  -- the `g₀`-square of the same vector
  have hgsq : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
      g₀.inner xp (∑ a, ξ a • Ea a) (∑ b, ξ b • Ea b) = ∑ a, (ξ a) ^ 2 := by
    intro ξ
    simp only [map_sum, sum_apply, map_smul, smul_apply, smul_eq_mul, hON, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single a]
    · rw [if_pos rfl]; ring
    · intro b _ hb
      rw [if_neg (Ne.symm hb)]; ring
    · intro ha; exact absurd (Finset.mem_univ a) ha
  -- the sup-norm / Euclidean-square comparison
  have hnorm : ∀ ξ : Fin (Module.finrank ℝ E) → ℝ, ‖ξ‖ ^ 2 ≤ ∑ a, (ξ a) ^ 2 := by
    intro ξ
    by_cases hn : Nonempty (Fin (Module.finrank ℝ E))
    · haveI := hn
      obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image
        (Finset.univ : Finset (Fin (Module.finrank ℝ E))) (fun i => |ξ i|) Finset.univ_nonempty
      have hle : ‖ξ‖ ≤ |ξ i₀| := by
        rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
        intro i
        rw [Real.norm_eq_abs]
        exact hi₀ i (Finset.mem_univ i)
      have hge : |ξ i₀| ≤ ‖ξ‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm ξ i₀
      have heq : ‖ξ‖ = |ξ i₀| := le_antisymm hle hge
      rw [heq, sq_abs]
      exact Finset.single_le_sum (fun i _ => sq_nonneg (ξ i)) (Finset.mem_univ i₀)
    · rw [not_nonempty_iff] at hn
      haveI : IsEmpty (Fin (Module.finrank ℝ E)) := hn
      have h0 : ξ = 0 := funext fun i => isEmptyElim i
      rw [h0]
      simp
  -- ## 1. symmetry
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b
    rw [hmn a b, hmn b a]
    exact hsym xp (Ea a) (Ea b)
  -- ## 2. ellipticity
  · intro ξ
    simp only [hmn]
    rw [← hform (h xp) ξ]
    calc lam * ‖ξ‖ ^ 2 ≤ lam * ∑ a, (ξ a) ^ 2 := mul_le_mul_of_nonneg_left (hnorm ξ) hlam.le
      _ = lam * g₀.inner xp (∑ a, ξ a • Ea a) (∑ b, ξ b • Ea b) := by rw [hgsq ξ]
      _ ≤ h xp (∑ a, ξ a • Ea a) (∑ b, ξ b • Ea b) := hell xp _
  -- ## 3. the entrywise bound
  · intro a b
    have hpp : h xp (Ea a + Ea b) (Ea a + Ea b)
        = h xp (Ea a) (Ea a) + 2 * h xp (Ea a) (Ea b) + h xp (Ea b) (Ea b) := by
      simp only [map_add, add_apply]
      rw [hsym xp (Ea b) (Ea a)]
      ring
    have hmm : h xp (Ea a - Ea b) (Ea a - Ea b)
        = h xp (Ea a) (Ea a) - 2 * h xp (Ea a) (Ea b) + h xp (Ea b) (Ea b) := by
      simp only [map_sub, sub_apply]
      rw [hsym xp (Ea b) (Ea a)]
      ring
    have h1 : -2 * h xp (Ea a) (Ea b) ≤ h xp (Ea a) (Ea a) + h xp (Ea b) (Ea b) := by
      have := hnn (Ea a + Ea b); rw [hpp] at this; linarith
    have h2 : 2 * h xp (Ea a) (Ea b) ≤ h xp (Ea a) (Ea a) + h xp (Ea b) (Ea b) := by
      have := hnn (Ea a - Ea b); rw [hmm] at this; linarith
    have habs : 2 * |h xp (Ea a) (Ea b)|
        ≤ h xp (Ea a) (Ea a) + h xp (Ea b) (Ea b) := by
      have h3 : |2 * h xp (Ea a) (Ea b)|
          ≤ h xp (Ea a) (Ea a) + h xp (Ea b) (Ea b) := by
        rw [abs_le]; exact ⟨by linarith, h2⟩
      simpa [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using h3
    have hdiag : h xp (Ea a) (Ea a) + h xp (Ea b) (Ea b) ≤ 2 * K := by
      have h1 := hub xp (Ea a); have h2 := hub xp (Ea b)
      rw [hON a a, if_pos rfl, mul_one] at h1
      rw [hON b b, if_pos rfl, mul_one] at h2
      linarith
    rw [hmn a b]
    linarith [abs_nonneg (h xp (Ea a) (Ea b))]
  -- ## 4. the determinant
  · have hker : ∀ v : Fin (Module.finrank ℝ E) → ℝ,
        Matrix.of (Mf (I := I) (M := M) D h j z) *ᵥ v = 0 → v = 0 := by
      intro v hv
      have hker_a : ∀ a : Fin (Module.finrank ℝ E),
          (∑ b, Mf (I := I) (M := M) D h j z a b * v b) = 0 := by
        intro a
        have h := congrFun hv a
        simpa [Matrix.mulVec, dotProduct, Matrix.of_apply] using h
      have hzero : (∑ a, ∑ b, v a * ((h xp) (Ea a)) (Ea b) * v b) = 0 := by
        have hsum : (∑ a, ∑ b, v a * ((h xp) (Ea a)) (Ea b) * v b)
            = ∑ a, v a * (∑ b, Mf (I := I) (M := M) D h j z a b * v b) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [hmn a b]; ring
        rw [hsum]
        simp [hker_a]
      have hb : lam * (∑ a, (v a) ^ 2) ≤ 0 := by
        have hge := hell xp (∑ a, v a • Ea a)
        rw [hgsq v, hform (h xp) v] at hge
        rw [hzero] at hge
        exact hge
      have hv0 : ‖v‖ = 0 := by
        have h2 : lam * ‖v‖ ^ 2 ≤ lam * ∑ a, (v a) ^ 2 :=
          mul_le_mul_of_nonneg_left (hnorm v) hlam.le
        have h3 : lam * ‖v‖ ^ 2 ≤ 0 := le_trans h2 hb
        have h4 : ‖v‖ * ‖v‖ ≤ 0 := by nlinarith [h3, hlam]
        have h5 : 0 ≤ ‖v‖ * ‖v‖ := mul_self_nonneg _
        exact mul_self_eq_zero.mp (le_antisymm h4 h5)
      exact norm_eq_zero.mp hv0
    have hinj : Function.Injective (Matrix.of (Mf (I := I) (M := M) D h j z)).mulVec := by
      intro v w hvw
      have h0 : Matrix.of (Mf (I := I) (M := M) D h j z) *ᵥ (v - w) = 0 := by
        rw [Matrix.mulVec_sub, hvw, sub_self]
      have := hker (v - w) h0
      simpa [sub_eq_zero] using this
    have hu : IsUnit (Matrix.of (Mf (I := I) (M := M) D h j z)) :=
      Matrix.mulVec_injective_iff_isUnit.mp hinj
    have hu2 : IsUnit (Matrix.of (Mf (I := I) (M := M) D h j z)).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp hu
    exact isUnit_iff_ne_zero.mp hu2

end Work.Diff.STE.B3
