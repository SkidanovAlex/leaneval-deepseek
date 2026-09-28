import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.rNorm_smul

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Finset
open scoped BigOperators

namespace Work.HP.MDEstimates

variable {ι : Type*} [Fintype ι]

/-- The self dot product of a nonzero integer vector is positive. -/
lemma dotZ_self_pos {v : ι → ℤ} (hv : v ≠ 0) : 0 < dotZ v v := by
  rw [dotZ_apply]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  exact Finset.sum_pos' (fun j _ => mul_self_nonneg (v j))
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

/-- Scaling an integer vector scales the Euclidean norm by the absolute value of the scalar. -/
lemma eNorm_smul_int (m : ℤ) (v : ι → ℤ) : eNorm (m • v) = |(m : ℝ)| * eNorm v := by
  have h : toR (m • v) = (m : ℝ) • toR v := by
    funext i
    simp only [toR, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have h2 : eNorm (m • v) = rNorm ((m : ℝ) • toR v) := by
    rw [show eNorm (m • v) = rNorm (toR (m • v)) from rfl, h]
  rw [h2, rNorm_smul]
  rfl

omit [Fintype ι] in
/-- The `ℤ`-span of a nonzero vector of a sublattice of `ℤ^ι` has rank one. -/
lemma finrank_span_singleton_sub (L : Submodule ℤ (ι → ℤ)) {v : L} (hv : v ≠ 0) :
    Module.finrank ℤ ↥(ℤ ∙ v) = 1 := by
  have hinj : Function.Injective (LinearMap.toSpanSingleton ℤ L v) := by
    intro m n hmn
    have hmn' : m • v = n • v := hmn
    have hzero : (m - n) • v = 0 := by rw [sub_smul, hmn', sub_self]
    have hvec : (m - n) • (v : ι → ℤ) = 0 := by
      have hz := congrArg (fun w : L => (w : ι → ℤ)) hzero
      simpa using hz
    have hv0 : (v : ι → ℤ) ≠ 0 := fun h => hv (Subtype.ext h)
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    have hco : ((m - n) * (v : ι → ℤ) i) = 0 := by
      have := congrFun hvec i
      simpa [Pi.smul_apply, smul_eq_mul] using this
    rcases mul_eq_zero.mp hco with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hi
  have he := (LinearEquiv.ofInjective (LinearMap.toSpanSingleton ℤ L v) hinj).trans
      (LinearEquiv.ofEq _ _ (LinearMap.range_toSpanSingleton v))
  rw [← he.finrank_eq]
  exact Module.finrank_self ℤ

/-- **Kernel computation.** If `u` is a shortest nonzero vector of the lattice `L` and
`x ∈ L` is killed by the scaled projection `projScale u`, then `x` is an integer multiple of `u`. -/
lemma projScale_eq_zero_imp (L : Submodule ℤ (ι → ℤ)) {u : ι → ℤ} (hu : u ∈ L) (hu0 : u ≠ 0)
    (hshort : ∀ v ∈ L, v ≠ 0 → eNorm u ≤ eNorm v)
    {x : ι → ℤ} (hxL : x ∈ L) (hx : projScale u x = 0) :
    ∃ m : ℤ, x = m • u := by
  have hdu : 0 < dotZ u u := dotZ_self_pos hu0
  have hmain : (dotZ u u) • x = (dotZ x u) • u := sub_eq_zero.mp hx
  have hqr : dotZ u u * (dotZ x u / dotZ u u) + (dotZ x u % dotZ u u) = dotZ x u :=
    Int.mul_ediv_add_emod (dotZ x u) (dotZ u u)
  have hr0 : 0 ≤ dotZ x u % dotZ u u := Int.emod_nonneg _ (ne_of_gt hdu)
  have hrd : dotZ x u % dotZ u u < dotZ u u := Int.emod_lt_of_pos _ hdu
  have hyL : x - (dotZ x u / dotZ u u) • u ∈ L :=
    L.sub_mem hxL (L.smul_mem (dotZ x u / dotZ u u) hu)
  have h2 : (dotZ u u) • (x - (dotZ x u / dotZ u u) • u) = (dotZ x u % dotZ u u) • u := by
    have hdq : (dotZ u u) • ((dotZ x u / dotZ u u) • u)
        = (dotZ u u * (dotZ x u / dotZ u u)) • u := by rw [smul_smul]
    have hcr : dotZ x u - dotZ u u * (dotZ x u / dotZ u u) = dotZ x u % dotZ u u := by omega
    rw [smul_sub, hdq, hmain, ← sub_smul, hcr]
  by_cases hy : x - (dotZ x u / dotZ u u) • u = 0
  · exact ⟨dotZ x u / dotZ u u, sub_eq_zero.mp hy⟩
  · exfalso
    have hny : 0 < eNorm (x - (dotZ x u / dotZ u u) • u) := eNorm_pos_of_ne_zero hy
    have hru : 0 < eNorm u := eNorm_pos_of_ne_zero hu0
    have hdpos : (0 : ℝ) < ((dotZ u u : ℤ) : ℝ) := by exact_mod_cast hdu
    have hne : ((dotZ u u : ℤ) : ℝ) * eNorm (x - (dotZ x u / dotZ u u) • u)
        = ((dotZ x u % dotZ u u : ℤ) : ℝ) * eNorm u := by
      have h := congrArg eNorm h2
      rw [eNorm_smul_int, eNorm_smul_int] at h
      rw [abs_of_pos hdpos,
        abs_of_nonneg (show (0 : ℝ) ≤ ((dotZ x u % dotZ u u : ℤ) : ℝ) from Int.cast_nonneg hr0)] at h
      exact h
    have hle : ((dotZ x u % dotZ u u : ℤ) : ℝ) ≤ ((dotZ u u : ℤ) : ℝ) - 1 := by
      have h1 : (dotZ x u % dotZ u u : ℤ) ≤ dotZ u u - 1 := by omega
      have h2' : ((dotZ x u % dotZ u u : ℤ) : ℝ) ≤ ((dotZ u u - 1 : ℤ) : ℝ) := by
        exact_mod_cast h1
      have h3 : ((dotZ u u - 1 : ℤ) : ℝ) = ((dotZ u u : ℤ) : ℝ) - 1 := by push_cast; ring
      linarith [h2', h3]
    have hlt : ((dotZ u u : ℤ) : ℝ) * eNorm (x - (dotZ x u / dotZ u u) • u)
        < ((dotZ u u : ℤ) : ℝ) * eNorm u := by
      rw [hne]
      calc ((dotZ x u % dotZ u u : ℤ) : ℝ) * eNorm u
          ≤ (((dotZ u u : ℤ) : ℝ) - 1) * eNorm u := mul_le_mul_of_nonneg_right hle hru.le
        _ < ((dotZ u u : ℤ) : ℝ) * eNorm u := by
            refine mul_lt_mul_of_pos_right ?_ hru
            linarith
    have hylt : eNorm (x - (dotZ x u / dotZ u u) • u) < eNorm u :=
      lt_of_mul_lt_mul_left hlt hdpos.le
    have := hshort _ hyL hy
    linarith

variable [DecidableEq ι]

theorem rk_projScale {ι : Type*} [Fintype ι] [DecidableEq ι]
    (L : Submodule ℤ (ι → ℤ)) (u : ι → ℤ) (hu : u ∈ L) (hu0 : u ≠ 0)
    (hshort : ∀ v ∈ L, v ≠ 0 → Work.HP.eNorm u ≤ Work.HP.eNorm v) :
    Work.HP.rk (Submodule.map (Work.HP.projScale u) L) = Work.HP.rk L - 1 := by
  classical
  set f : L →ₗ[ℤ] (ι → ℤ) := (projScale u).comp L.subtype with hf
  have hrange : f.range = Submodule.map (projScale u) L := by
    ext y
    rw [LinearMap.mem_range, Submodule.mem_map]
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, z.2, hz⟩
    · rintro ⟨z, hzL, hz⟩
      exact ⟨⟨z, hzL⟩, hz⟩
  have hu_ker : (⟨u, hu⟩ : L) ∈ f.ker := by
    rw [LinearMap.mem_ker]
    show projScale u u = 0
    simp
  have hker : f.ker = Submodule.span ℤ {⟨u, hu⟩} := by
    refine le_antisymm ?_ ?_
    · intro z hz
      have hz' : projScale u (z : ι → ℤ) = 0 := LinearMap.mem_ker.mp hz
      obtain ⟨m, hm⟩ := projScale_eq_zero_imp L hu hu0 hshort z.2 hz'
      refine Submodule.mem_span_singleton.mpr ⟨m, ?_⟩
      exact Subtype.ext (by simpa using hm.symm)
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      exact hu_ker
  have hfin_ker : Module.finrank ℤ ↥(f.ker) = 1 := by
    rw [hker]
    exact finrank_span_singleton_sub L (v := (⟨u, hu⟩ : L))
      (fun h => hu0 (by simpa using congrArg Subtype.val h))
  have hq : Module.finrank ℤ (L ⧸ f.ker) = Module.finrank ℤ ↥(f.range) :=
    (LinearMap.quotKerEquivRange f).finrank_eq
  have hrn := Submodule.finrank_quotient_add_finrank (R := ℤ) (M := L) f.ker
  rw [hq, hfin_ker] at hrn
  rw [rk, rk, ← hrange]
  omega

end Work.HP.MDEstimates
