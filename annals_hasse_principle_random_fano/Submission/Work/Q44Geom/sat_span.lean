import Mathlib
import Submission.Work.Q44Geom.Setup
import Submission.Work.HP.PairsAux

/-!
# `Work.Q44Geom.sat_span`

For a primitive (saturated) sublattice `L ⊆ ℤ^5`, an integral vector `v` lies in `L` iff its
rational image lies in the `ℚ`-span `ratSpan L` of `L`.

The substance is the standard "clearing denominators" statement: `toRatLM v ∈ ratSpan L` holds
iff some nonzero integer multiple of `v` lies in `L`; primitivity then removes the multiple.
-/

set_option autoImplicit false
noncomputable section

namespace Work.Q44Geom

/-- The coefficientwise coercion `ℤ^5 → ℚ^5` is injective. -/
theorem toRatLM_injective : Function.Injective (toRatLM : (Fin 5 → ℤ) →ₗ[ℤ] (Fin 5 → ℚ)) := by
  intro u v h
  funext i
  have hi : ((u i : ℤ) : ℚ) = ((v i : ℤ) : ℚ) := congrFun h i
  exact_mod_cast hi

/-- `ratSpan L` is the `ℚ`-span of the image of `L` under `toRatLM`. -/
theorem ratSpan_eq (L : Submodule ℤ (Fin 5 → ℤ)) :
    ratSpan L = Submodule.span ℚ (Submodule.map toRatLM L : Set (Fin 5 → ℚ)) := by
  have h : Set.range (fun v : L => toRatLM (v : Fin 5 → ℤ))
      = (Submodule.map toRatLM L : Set (Fin 5 → ℚ)) := by
    ext x
    simp only [Set.mem_range, SetLike.mem_coe, Submodule.mem_map]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨(w : Fin 5 → ℤ), w.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  unfold ratSpan
  rw [h]

/-- Clearing denominators: an element of the `ℚ`-span of the image of `L` has a nonzero
integer multiple lying in the image of `L`. -/
theorem mem_span_map (L : Submodule ℤ (Fin 5 → ℤ)) {x : Fin 5 → ℚ}
    (hx : x ∈ Submodule.span ℚ (Submodule.map toRatLM L : Set (Fin 5 → ℚ))) :
    ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ Submodule.map toRatLM L := by
  refine Submodule.span_induction
    (p := fun x _ => ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ Submodule.map toRatLM L) ?_ ?_ ?_ ?_ hx
  · intro x hx
    exact ⟨1, one_ne_zero, by simpa using hx⟩
  · exact ⟨1, one_ne_zero, by rw [one_smul]; exact Submodule.zero_mem _⟩
  · intro x y hx hy ihx ihy
    obtain ⟨n1, hn1, h1⟩ := ihx
    obtain ⟨n2, hn2, h2⟩ := ihy
    refine ⟨n1 * n2, mul_ne_zero hn1 hn2, ?_⟩
    have heq : (n1 * n2) • (x + y) = n2 • (n1 • x) + n1 • (n2 • y) := by
      rw [smul_add]
      congr 1
      · rw [mul_smul, smul_comm]
      · rw [mul_smul]
    rw [heq]
    exact Submodule.add_mem _ (Submodule.smul_mem _ n2 h1) (Submodule.smul_mem _ n1 h2)
  · intro a x hx ihx
    obtain ⟨n, hn, h⟩ := ihx
    refine ⟨(a.den : ℤ) * n, mul_ne_zero ?_ hn, ?_⟩
    · exact_mod_cast Rat.den_nz a
    · have hden : (a.den : ℚ) * a = (a.num : ℚ) := by
        have hh := Rat.num_div_den a
        field_simp at hh
        linarith
      have h2 : (a.den : ℤ) • (a • x) = a.num • x := by
        rw [← Int.cast_smul_eq_zsmul ℚ (a.den : ℤ) (a • x)]
        push_cast
        rw [smul_smul, hden, Int.cast_smul_eq_zsmul ℚ a.num x]
      have h3 : ((a.den : ℤ) * n) • (a • x) = a.num • (n • x) := by
        rw [mul_smul, smul_comm (a.den : ℤ) n (a • x), h2, smul_comm n a.num x]
      rw [h3]
      exact Submodule.smul_mem _ a.num h

/-- `x ∈ ratSpan L` iff some nonzero integer multiple of `x` lies in the image of `L`. -/
theorem mem_ratSpan_iff' (L : Submodule ℤ (Fin 5 → ℤ)) (x : Fin 5 → ℚ) :
    x ∈ ratSpan L ↔ ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ Submodule.map toRatLM L := by
  rw [ratSpan_eq]
  refine ⟨mem_span_map L, ?_⟩
  rintro ⟨n, hn, hmem⟩
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hsp : n • x ∈ Submodule.span ℚ (Submodule.map toRatLM L : Set (Fin 5 → ℚ)) :=
    Submodule.subset_span (s := (Submodule.map toRatLM L : Set (Fin 5 → ℚ))) hmem
  have hx : x = ((n : ℚ)⁻¹) • (n • x) := by
    rw [← Int.cast_smul_eq_zsmul ℚ n x, smul_smul, inv_mul_cancel₀ hnq, one_smul]
  rw [hx]
  exact Submodule.smul_mem _ _ hsp

/-- An integral `v` lies in the rational span of `L` iff some nonzero integer multiple of `v`
lies in `L`. -/
theorem mem_ratSpan_iff (L : Submodule ℤ (Fin 5 → ℤ)) (v : Fin 5 → ℤ) :
    toRatLM v ∈ ratSpan L ↔ ∃ n : ℤ, n ≠ 0 ∧ n • v ∈ L := by
  rw [mem_ratSpan_iff']
  constructor
  · rintro ⟨n, hn, hmem⟩
    rw [Submodule.mem_map] at hmem
    obtain ⟨m, hmL, hm⟩ := hmem
    have hm2 : m = n • v :=
      toRatLM_injective (hm.trans (toRatLM.map_smul n v).symm)
    exact ⟨n, hn, by rw [← hm2]; exact hmL⟩
  · rintro ⟨n, hn, hmem⟩
    refine ⟨n, hn, ?_⟩
    rw [Submodule.mem_map]
    exact ⟨n • v, hmem, toRatLM.map_smul n v⟩

theorem sat_span (L : Submodule ℤ (Fin 5 → ℤ)) (hL : Work.HP.IsPrimLat L) (v : Fin 5 → ℤ) :
    v ∈ L ↔ Work.Q44Geom.toRatLM v ∈ Work.Q44Geom.ratSpan L := by
  rw [mem_ratSpan_iff]
  constructor
  · intro hv; exact ⟨1, one_ne_zero, by simpa using hv⟩
  · rintro ⟨n, hn, hmem⟩
    exact hL v n hn hmem

end Work.Q44Geom
