import Mathlib
import Submission.Work.SSGRoute.PTW.logSectionDefs
import Submission.Work.SSGRoute.PTW.norm_completion_infinitePlace_surjective
import Submission.Work.SSGRoute.PTW.prod_exp_pow_mult_eq_exp_sum
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The content `C_K →* ℝˣ` is onto the positive reals up to `p`-th roots

For a number field `K` the *content* (idèle norm) `|·| : C_K →* ℝˣ` takes values in the positive
units, and conversely every positive real unit is the content of an idèle class: an idèle which is
`1` at every finite place and whose archimedean components are positive reals with the prescribed
norms has content the product `∏_w exp (b w) ^ (mult w) = exp (∑_w mult w * b w)`, and given a
positive unit `r` one chooses `b` supported at a single infinite place with `∑_w mult w * b w =
log r`.

Hence the image of the content is exactly the group `ℝ_{>0}` of positive units, which is
`p`-divisible: `exp (log r / p)` is a positive `p`-th root of `r`.  Consequently every content in
`C_K` is a `p`-th power of a content, which is the statement proved here.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped NumberField RestrictedProduct
open NumberField

noncomputable section

namespace Work.SSGRoute.PTW

open NK.GlobalCFT

/-- **The content of an idèle is positive.**  The content is the finitary product of the local
absolute values, all of which are positive units (`Units.mk0` of a norm, or a power of one); the
product is therefore positive. -/
theorem idele_abs_pos (K : Type) [Field K] [NumberField K] (x : Idele K) :
    0 < ((Idele.abs K x : ℝˣ) : ℝ) := by
  have hf : Function.HasFiniteMulSupport (fun v : Place K => Idele.localAbs K v (x v)) := by
    have h := Idele.localAbs_eq_one_eventually x
    rw [Filter.eventually_cofinite] at h
    simpa [Function.HasFiniteMulSupport, Function.mulSupport] using h
  have hmem : Idele.abs K x ∈ Units.posSubgroup ℝ := by
    rw [Idele.abs_apply, finprod_eq_prod _ hf]
    refine Subgroup.prod_mem _ (fun v _ => ?_)
    rcases v with w | q
    · rw [Idele.localAbs_ofInfinite, Units.mem_posSubgroup, Units.val_pow_eq_pow_val, Units.val_mk0]
      exact pow_pos (norm_pos_iff.mpr (Units.ne_zero _)) _
    · rw [Idele.localAbs_ofFinite, Units.mem_posSubgroup, Units.val_mk0]
      exact norm_pos_iff.mpr (Units.ne_zero _)
  exact (Units.mem_posSubgroup _).mp hmem

/-- **The positive units of `ℝ` are `p`-divisible**: a positive real has a positive `p`-th root
`exp (log r / p)`. -/
theorem pos_units_pow_surjective (p : ℕ) (hp : p ≠ 0) (r : ℝˣ) (hr : 0 < (r : ℝ)) :
    ∃ s : ℝˣ, 0 < (s : ℝ) ∧ s ^ p = r := by
  refine ⟨Units.mk0 (Real.exp (Real.log (r : ℝ) / p)) (Real.exp_ne_zero _), ?_, ?_⟩
  · rw [Units.val_mk0]
    exact Real.exp_pos _
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, ← Real.exp_nat_mul]
    have hp' : ((p : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr hp
    have h : ((p : ℝ)) * (Real.log (r : ℝ) / p) = Real.log (r : ℝ) := by
      field_simp
    rw [h, Real.exp_log hr]

/-- **The content map is onto the positive units.**  Given a positive unit `r` choose an infinite
place `w₀` and the function `b` which is `log r / mult w₀` at `w₀` and `0` elsewhere; the idèle
which is `1` at every finite place and has archimedean components of norm `exp (b w)` has content
`exp (∑_w mult w * b w) = exp (log r) = r`. -/
theorem idele_abs_surjective_pos (K : Type) [Field K] [NumberField K] (r : ℝˣ)
    (hr : 0 < (r : ℝ)) :
    ∃ a : Idele K, Idele.abs K a = r := by
  classical
  -- an infinite place exists because `K` is a number field
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (NumberField.InfinitePlace K))
  -- concentrate the content at `w₀`
  set b : NumberField.InfinitePlace K → ℝ :=
    fun w => if w = w₀ then Real.log (r : ℝ) / (w₀.mult : ℝ) else 0 with hb_def
  have hb : ∑ w, ((w.mult : ℕ) : ℝ) * b w = Real.log (r : ℝ) := by
    rw [Finset.sum_eq_single w₀]
    · rw [hb_def]
      simp only [if_true]
      field_simp
    · intro w _ hw
      rw [hb_def]
      simp only [if_neg hw, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ w₀) h
  -- the archimedean components: units of norm `exp (b w)`
  choose t ht using fun w => norm_completion_infinitePlace_surjective K w (b w)
  let f : (v : Place K) → (Place.localField K v)ˣ :=
    fun v => match v with
      | Sum.inl w => t w
      | Sum.inr _ => 1
  have hff : ∀ᶠ v in Filter.cofinite, f v ∈ Place.localUnits K v :=
    Filter.Eventually.of_forall fun v => by
      rcases v with w | q
      · exact trivial
      · exact Subgroup.one_mem _
  let a : Idele K := ⟨f, hff⟩
  have hval : ∀ w : NumberField.InfinitePlace K,
      ‖(a (Place.ofInfinite w) : w.Completion)‖ = Real.exp (b w) := by
    intro w
    show ‖(f (Place.ofInfinite w) : w.Completion)‖ = Real.exp (b w)
    exact ht w
  refine ⟨a, ?_⟩
  apply Units.ext
  rw [IdeleClassGroup.abs_val_eq_prod_of_localUnits (S := ∅) (x := a)]
  · rw [Finset.prod_empty, one_mul]
    rw [show (∏ w : NumberField.InfinitePlace K,
        ‖(a (Place.ofInfinite w) : w.Completion)‖ ^ w.mult) =
        ∏ w : NumberField.InfinitePlace K, Real.exp (b w) ^ w.mult from
      Finset.prod_congr rfl fun w _ => by rw [hval w]]
    rw [prod_exp_pow_mult_eq_exp_sum K b, hb, Real.exp_log hr]
  · intro q _
    show f (Place.ofFinite q) ∈ Place.localUnits K (Place.ofFinite q)
    exact Subgroup.one_mem _

theorem abs_ideleClassGroup_pow_surjective (K : Type) [Field K] [NumberField K] (p : ℕ) (hp : p ≠ 0)
    (x : NK.GlobalCFT.IdeleClassGroup K) :
    ∃ y : NK.GlobalCFT.IdeleClassGroup K,
      (NK.GlobalCFT.IdeleClassGroup.abs K y) ^ p = NK.GlobalCFT.IdeleClassGroup.abs K x := by
  -- the content of `x` is a positive unit
  have hxpos : 0 < ((IdeleClassGroup.abs K x : ℝˣ) : ℝ) := by
    obtain ⟨a, rfl⟩ := IdeleClassGroup.mk_surjective K x
    rw [IdeleClassGroup.abs_mk]
    exact idele_abs_pos K a
  -- a positive `p`-th root of it, and a class realising that root as a content
  obtain ⟨s, hspos, hs⟩ := pos_units_pow_surjective p hp (IdeleClassGroup.abs K x) hxpos
  obtain ⟨a, ha⟩ := idele_abs_surjective_pos K s hspos
  exact ⟨IdeleClassGroup.mk K a, by rw [IdeleClassGroup.abs_mk, ha, hs]⟩

end Work.SSGRoute.PTW
