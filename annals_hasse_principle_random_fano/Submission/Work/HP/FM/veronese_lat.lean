import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.Lat.detL_span_gram
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.FM.detL_sup_orthogonal
import Submission.Work.HP.FM.detL_LM

/-!
# `veronese_lat`

Two facts about the Veronese map `ν_{d,n}` of `Submission/Work/HP/Defs.lean`.

* **Lattice fact.**  For a primitive exponent vector `c : Mon d n → ℤ`, the orthogonal lattice
  `Λ_c = {y : Mon d n → ℤ // ⟨c,y⟩ = 0}` is a rank-`(N-1)` sublattice of `ℤ^N`, `N = N_{d,n}`,
  with covolume `‖c‖`.  Proof: for primitive `c` the lattice `LM c = {y : ‖c‖² ∣ ⟨c,y⟩}` decomposes
  as the orthogonal direct sum `Λ_c ⊔ ℤc`; covolume is multiplicative on such sums
  (`Work.HP.FM.detL_sup_orthogonal`), `detL (ℤc) = ‖c‖` and `detL (LM c) = sqN c = ‖c‖²`
  (`Work.HP.FM.detL_LM`); cancelling `‖c‖ > 0` gives the claim.

* **Norm fact.**  `‖ν_{d,n}(x)‖ ≍ ‖x‖^d`, i.e. `Work.HP.eNorm_veronese_bounds`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open Work.HP

namespace Work.HP.FM

/-! ## Elementary lattice identities for `latOrth c` -/

section lattice
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For primitive `c` the congruence lattice `LM c = {y : ‖c‖² ∣ ⟨c,y⟩}` is the sum of the
orthogonal lattice `Λ_c = {y : ⟨c,y⟩ = 0}` and `ℤc`. -/
theorem sup_span_latOrth_eq_LM (c : ι → ℤ) :
    latOrth c ⊔ Submodule.span ℤ {c} = LM c := by
  apply le_antisymm
  · exact sup_le (latOrth_le_LM c) (span_singleton_le_LM c)
  · intro y hy
    rw [mem_LM] at hy
    obtain ⟨k, hk⟩ := hy
    refine Submodule.mem_sup.mpr ⟨y + (-k) • c, ?_, k • c,
      Submodule.smul_mem _ k (Submodule.subset_span (Set.mem_singleton c)), ?_⟩
    · rw [mem_latOrth, pdot_add_left, pdot_smul_left, hk, sqN_cast_eq_pdot]
      ring
    · ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring

/-- `Λ_c ∩ ℤc = 0` for primitive `c`. -/
theorem inf_span_latOrth_eq_bot (c : ι → ℤ) (hc : IsPrim c) :
    latOrth c ⊓ Submodule.span ℤ {c} = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_inf, mem_latOrth, Submodule.mem_span_singleton] at hy
  obtain ⟨hy1, k, hk⟩ := hy
  rw [← hk, pdot_smul_left, ← sqN_cast_eq_pdot] at hy1
  have hk0 : k = 0 :=
    (mul_eq_zero.mp hy1).resolve_right (by exact_mod_cast ne_of_gt (sqN_pos hc))
  rw [← hk, hk0, zero_smul]

/-- `Λ_c` is orthogonal to `ℤc`. -/
theorem dot_latOrth_span (c : ι → ℤ) :
    ∀ x ∈ latOrth c, ∀ y ∈ Submodule.span ℤ {c}, ∑ i, x i * y i = 0 := by
  intro x hx y hy
  rw [mem_latOrth] at hx
  rw [Submodule.mem_span_singleton] at hy
  obtain ⟨k, hk⟩ := hy
  rw [← hk]
  calc ∑ i, x i * (k • c) i = pdot x (k • c) := rfl
    _ = k * pdot x c := pdot_smul_right k x c
    _ = 0 := by rw [hx, mul_zero]

/-- The covolume of the rank-one lattice `ℤc` is `‖c‖`. -/
theorem detL_span_singleton (c : ι → ℤ) (hc : c ≠ 0) :
    detL (Submodule.span ℤ {c}) = eNorm c := by
  have hf : LinearIndependent ℤ (fun _ : Fin 1 => c) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hg0 : g 0 • c = 0 := by
      simpa only [Fin.sum_univ_one] using hg
    have hzero : g 0 = 0 := (smul_eq_zero.mp hg0).resolve_right hc
    have hi : i = 0 := Subsingleton.elim i 0
    rw [hi]; exact hzero
  have hrange : Set.range (fun _ : Fin 1 => c) = ({c} : Set (ι → ℤ)) := by
    ext x
    simp only [Set.mem_range, Set.mem_singleton_iff]
    exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩
  rw [← hrange, Work.HP.Lat.detL_span_gram 1 (fun _ : Fin 1 => c) hf, Matrix.det_fin_one]
  rw [eNorm]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by ring

end lattice

/-! ## The covolume of `Λ_c` -/

section main
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- For primitive `c : ι → ℤ`, the orthogonal lattice `Λ_c = {y : ⟨c,y⟩ = 0}` has covolume `‖c‖`
in its real span. -/
theorem detL_latOrth_of_prim (c : ι → ℤ) (hc : IsPrim c) :
    detL (latOrth c) = eNorm c := by
  have hc0 : c ≠ 0 := isPrim_ne_zero hc
  have hkey : detL (LM c) = detL (latOrth c) * detL (Submodule.span ℤ {c}) := by
    rw [← sup_span_latOrth_eq_LM c]
    exact detL_sup_orthogonal (latOrth c) (Submodule.span ℤ {c})
      (inf_span_latOrth_eq_bot c hc) (dot_latOrth_span c)
  rw [detL_LM c hc, detL_span_singleton c hc0] at hkey
  have hepos : 0 < eNorm c := eNorm_pos_of_ne_zero hc0
  have h2 : detL (latOrth c) * eNorm c = eNorm c * eNorm c := by
    rw [← hkey, ← eNorm_sq_eq_sqN]
    ring
  exact mul_right_cancel₀ (ne_of_gt hepos) h2

end main

/-! ## The theorem -/

theorem veronese_lat (d n : ℕ) (hd : 1 ≤ d) :
    (∀ c : Mon d n → ℤ, IsPrim c → detL (latOrth c) = eNorm c) ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ x : Fin (n + 1) → ℤ,
      c₁ * eNorm x ^ d ≤ eNorm (veronese d n x) ∧
        eNorm (veronese d n x) ≤ c₂ * eNorm x ^ d) :=
  ⟨fun _ hc => detL_latOrth_of_prim _ hc, eNorm_veronese_bounds d n hd⟩

end Work.HP.FM
