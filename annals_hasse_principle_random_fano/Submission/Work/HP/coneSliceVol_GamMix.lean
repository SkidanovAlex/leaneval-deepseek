import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.Vero.span_realify_latOrth_inf
import Submission.Work.HP.HP3.DotLinDefs
import Submission.Work.HP.BCS.Setup

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000
open Finset MeasureTheory
open scoped RealInnerProductSpace

namespace Work.HP

/-! ## `toE`, `toEr` and elementary facts -/

section toEBasics
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] lemma toE_zero_csg : toE (0 : ι → ℝ) = 0 := by
  rw [toE]; exact WithLp.toLp_zero 2

lemma toE_smul_fun_csg (c : ℝ) (v : ι → ℝ) : toE (fun m => c * v m) = c • toE v := by
  have h : (fun m => c * v m) = c • v := by
    funext m; simp [Pi.smul_apply, smul_eq_mul]
  rw [h, toE, WithLp.toLp_smul]
  rfl

/-- `toE` as an `ℝ`-linear equivalence. -/
def toEEquiv_csg : (ι → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ ι :=
  (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm

lemma toEEquiv_csg_apply (v : ι → ℝ) : toEEquiv_csg v = toE v := by
  rw [toEEquiv_csg, WithLp.linearEquiv_symm_apply]; rfl

/-- `toE` as an `ℝ`-linear map. -/
def toELin_csg : (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι := toEEquiv_csg.toLinearMap

@[simp] lemma toELin_csg_apply (v : ι → ℝ) : toELin_csg v = toE v := toEEquiv_csg_apply v

lemma toELin_csg_image (S : Set (ι → ℝ)) : toELin_csg '' S = toE '' S := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, toELin_csg_apply y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (toELin_csg_apply y).symm⟩

lemma toE_ofLp_csg (t : EuclideanSpace ℝ ι) : toE t.ofLp = t :=
  WithLp.toLp_ofLp 2 t

lemma dotLin_eq_linearCombination_csg (c : ι → ℤ) :
    dotLin c = Fintype.linearCombination ℝ (fun i => (c i : ℝ)) := by
  apply LinearMap.ext
  intro u
  rw [dotLin_apply, Fintype.linearCombination_apply]
  exact Finset.sum_congr rfl (fun i _ => by rw [smul_eq_mul]; exact mul_comm _ _)

lemma toEr_intCast_smul_csg (Q : ℤ) (a : ι → ℤ) : toEr (Q • a) = (Q : ℝ) • toEr a := by
  have h1 : toR (Q • a) = (Q : ℝ) • toR a := by
    funext i
    simp [toR, Pi.smul_apply, smul_eq_mul]
  rw [toEr, toEr, h1, toE, WithLp.toLp_smul]
  rfl

end toEBasics

/-! ## The real span of `latOrth c` is the kernel of `t ↦ ⟪c,t⟫` -/

section latOrthKer
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma spanE_latOrth_ker_csg (c : ι → ℤ) :
    spanE (latOrth c) = LinearMap.ker (innerLin (toE (toR c))) := by
  -- In `ℝ^ι`: the real span of `latOrth c` is the kernel of `dotLin c`.
  have h1 : Submodule.span ℝ (intCastPi '' (latOrth c : Set (ι → ℤ)))
      = LinearMap.ker (dotLin c) := by
    rw [dotLin_eq_linearCombination_csg c]
    simpa only [inf_idem, Submodule.map_coe] using (Vero.span_realify_latOrth_inf c c)
  -- The two functionals agree under `toE`.
  have hcomm : ∀ y : ι → ℝ, innerLin (toE (toR c)) (toELin_csg y) = dotLin c y := by
    intro y
    rw [toELin_csg_apply]
    change inner ℝ (toE (toR c)) (toE y) = dotLin c y
    rw [BCS.inner_toE_toE, dotLin_apply]
    exact Finset.sum_congr rfl (fun i _ => by simp [toR, mul_comm])
  have hset : toEr '' (latOrth c : Set (ι → ℤ))
      = toE '' (intCastPi '' (latOrth c : Set (ι → ℤ))) := by
    ext z
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨intCastPi v, ⟨v, hv, rfl⟩, rfl⟩
    · rintro ⟨y, ⟨v, hv, rfl⟩, hy⟩
      exact ⟨v, hv, hy⟩
  have h2 : spanE (latOrth c) = Submodule.map toELin_csg (LinearMap.ker (dotLin c)) := by
    rw [spanE, hset, ← toELin_csg_image (intCastPi '' (latOrth c : Set (ι → ℤ)))]
    rw [show Submodule.span ℝ (toELin_csg '' (intCastPi '' (latOrth c : Set (ι → ℤ))))
        = Submodule.map toELin_csg
            (Submodule.span ℝ (intCastPi '' (latOrth c : Set (ι → ℤ)))) from
      (Submodule.map_span toELin_csg (intCastPi '' (latOrth c : Set (ι → ℤ)))).symm]
    rw [h1]
  have h3 : Submodule.map toELin_csg (LinearMap.ker (dotLin c))
      = LinearMap.ker (innerLin (toE (toR c))) := by
    ext t
    constructor
    · rintro ⟨y, hy, rfl⟩
      change dotLin c y = 0 at hy
      change innerLin (toE (toR c)) (toELin_csg y) = 0
      rw [hcomm y, hy]
    · intro ht
      change innerLin (toE (toR c)) t = 0 at ht
      refine ⟨t.ofLp, ?_, ?_⟩
      · change dotLin c t.ofLp = 0
        have hL : toELin_csg t.ofLp = t := by rw [toELin_csg_apply, toE_ofLp_csg]
        have key := hcomm t.ofLp
        rw [hL] at key
        exact key.symm.trans ht
      · rw [toELin_csg_apply, toE_ofLp_csg]
  rw [h2, h3]

end latOrthKer

/-! ## The `Γ^mix` lattice spans the same hyperplane as `Λ_{ν(x)}` -/

section gamMix
variable {d n : ℕ} [DecidableEq (Mon d n)]

lemma spanE_GamMix_eq_spanE_latOrth_csg
    (x y : Fin (n + 1) → ℤ) (Q : ℕ) (hQ : 1 ≤ Q) :
    spanE (GamMix d n x y Q) = spanE (latOrth (veronese d n x)) := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_mono (Set.image_mono ?_)
    show (GamMix d n x y Q : Set (Mon d n → ℤ)) ⊆ latOrth (veronese d n x)
    rw [GamMix]
    exact inf_le_left
  · rw [spanE, spanE, Submodule.span_le]
    rintro z ⟨a, ha, rfl⟩
    have hQa : ((Q : ℤ) • a) ∈ GamMix d n x y Q := by
      rw [GamMix, Submodule.mem_inf]
      refine ⟨?_, ?_⟩
      · change (Fintype.linearCombination ℤ (veronese d n x)) a = 0 at ha
        change (Fintype.linearCombination ℤ (veronese d n x)) ((Q : ℤ) • a) = 0
        rw [map_smul, ha, smul_zero]
      · rw [latMod, Submodule.mem_comap, map_smul]
        refine Submodule.mem_span_singleton.mpr
          ⟨(Fintype.linearCombination ℤ (veronese d n y)) a, ?_⟩
        simp [mul_comm]
    have hmem : toEr ((Q : ℤ) • a)
        ∈ Submodule.span ℝ (toEr '' (GamMix d n x y Q : Set (Mon d n → ℤ))) :=
      Submodule.subset_span ⟨_, hQa, rfl⟩
    rw [toEr_intCast_smul_csg] at hmem
    have hQne : (Q : ℝ) ≠ 0 := by
      have h : Q ≠ 0 := by omega
      exact_mod_cast h
    have hrew : toEr a = (Q : ℝ)⁻¹ • ((Q : ℝ) • toEr a) := by
      rw [smul_smul, inv_mul_cancel₀ hQne, one_smul]
    rw [hrew]
    exact Submodule.smul_mem _ _ hmem

end gamMix

/-! ## The rescaling identity for the cone slice -/

lemma slice_cone_iff_csg {ι : Type*} [Fintype ι] (w t : EuclideanSpace ℝ ι) (α : ℝ)
    (hα : 0 < α) :
    |inner ℝ w t| ≤ ‖w‖ * ‖t‖ / (2 * α) ↔ |inner ℝ ((2 * α / ‖w‖) • w) t| ≤ ‖t‖ := by
  rw [real_inner_smul_left, abs_mul]
  have hc : 0 ≤ 2 * α / ‖w‖ := div_nonneg (by linarith) (norm_nonneg w)
  rw [abs_of_nonneg hc]
  rcases eq_or_ne ‖w‖ 0 with hw | hw
  · have hw0 : w = 0 := norm_eq_zero.mp hw
    rw [hw0]; simp
  · have h2α : (0 : ℝ) < 2 * α := by linarith
    have h2αne : 2 * α ≠ 0 := ne_of_gt h2α
    constructor
    · intro h
      have h2 : (2 * α / ‖w‖) * |inner ℝ w t|
          ≤ (2 * α / ‖w‖) * (‖w‖ * ‖t‖ / (2 * α)) :=
        mul_le_mul_of_nonneg_left h hc
      have heq : (2 * α / ‖w‖) * (‖w‖ * ‖t‖ / (2 * α)) = ‖t‖ := by
        field_simp
      rwa [heq] at h2
    · intro h
      have hw2α : (0 : ℝ) ≤ ‖w‖ / (2 * α) := div_nonneg (norm_nonneg w) h2α.le
      have h2 : (‖w‖ / (2 * α)) * ((2 * α / ‖w‖) * |inner ℝ w t|)
          ≤ (‖w‖ / (2 * α)) * ‖t‖ :=
        mul_le_mul_of_nonneg_left h hw2α
      have heq : (‖w‖ / (2 * α)) * ((2 * α / ‖w‖) * |inner ℝ w t|) = |inner ℝ w t| := by
        field_simp
      have heq2 : (‖w‖ / (2 * α)) * ‖t‖ = ‖w‖ * ‖t‖ / (2 * α) := by ring
      rwa [heq, heq2] at h2

/-! ## The target -/

theorem coneSliceVol_GamMix (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d)
    (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (Q : ℕ) (hQ : 1 ≤ Q) (α : ℝ) (hα : 0 < α) :
    coneSliceVol (GamMix d n x y Q) (toR (veronese d n y)) 0 α
      = IcVol (toE (toR (veronese d n x)))
          (toE (fun m => (2 * α / ‖toE (toR (veronese d n y))‖) * toR (veronese d n y) m)) := by
  have hV : spanE (GamMix d n x y Q)
      = LinearMap.ker (innerLin (toE (toR (veronese d n x)))) := by
    rw [spanE_GamMix_eq_spanE_latOrth_csg x y Q hQ]
    exact spanE_latOrth_ker_csg (veronese d n x)
  have key : ∀ t : EuclideanSpace ℝ (Mon d n),
      (|inner ℝ (toE (toR (veronese d n y))) t|
          ≤ ‖toE (toR (veronese d n y))‖ * ‖t‖ / (2 * α) ∧
        |inner ℝ (toE (0 : Mon d n → ℝ)) t| ≤ ‖toE (0 : Mon d n → ℝ)‖ * ‖t‖ / (2 * α) ∧
          ‖t‖ ≤ 1)
      ↔ (|inner ℝ (toE (fun m =>
              (2 * α / ‖toE (toR (veronese d n y))‖) * toR (veronese d n y) m)) t| ≤ ‖t‖ ∧
          ‖t‖ ≤ 1) := by
    intro t
    rw [toE_smul_fun_csg]
    constructor
    · rintro ⟨h1, _, h3⟩
      exact ⟨(slice_cone_iff_csg (toE (toR (veronese d n y))) t α hα).mp h1, h3⟩
    · rintro ⟨h1, h3⟩
      exact ⟨(slice_cone_iff_csg (toE (toR (veronese d n y))) t α hα).mpr h1, by simp, h3⟩
  simp only [coneSliceVol, IcVol]
  rw [hV]
  apply congrArg (subVol (LinearMap.ker (innerLin (toE (toR (veronese d n x))))))
  ext t
  simp only [Set.mem_ofPred_eq]
  exact key t

end Work.HP
