import Mathlib

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace Work.ThomBordism

theorem exists_smul_extends_of_finite_quotient {Z : Type*} [AddCommGroup Z] [Module ℤ Z]
    (B : Submodule ℤ Z) (hfin : Module.Finite ℤ (Z ⧸ B)) (f : ↥B →ₗ[ℤ] ℤ) :
    ∃ N : ℕ, 0 < N ∧ ∃ g : Z →ₗ[ℤ] ℤ, ∀ b : ↥B, g ↑b = (N : ℤ) • f b := by
  classical
  letI instZ : Module ℤ Z := inferInstance
  -- Step 1: extend `f` to a ℤ-linear map `Z → ℚ` (ℚ is injective as a ℤ-module, being divisible).
  have hBaer : Module.Baer ℤ ℚ := Module.Baer.of_divisible ℚ
  obtain ⟨F, hF⟩ := Module.Baer.extension_property_addMonoidHom (Q := ℚ) (M := ↥B) (N := Z)
    hBaer (Submodule.subtype B).toAddMonoidHom (Submodule.subtype_injective B)
    ((Int.castAddHom ℚ).comp f.toAddMonoidHom)
  have hFb : ∀ b : ↥B, F ↑b = ((f b : ℤ) : ℚ) := fun b => by
    have := DFunLike.congr_fun hF b
    simpa using this
  have hFsmulA : ∀ (m : ℤ) (x : Z), F (instZ.smul m x) = m • F x := fun m x => by
    rw [int_smul_eq_zsmul instZ m x, map_zsmul]
  -- Step 2: a finite set of elements of `Z` whose images generate `Z ⧸ B`.
  obtain ⟨S, hS⟩ := hfin.fg_top
  have hmod : Submodule.Quotient.module B = AddCommGroup.toIntModule (Z ⧸ B) := Subsingleton.elim _ _
  rw [← hmod] at hS
  obtain ⟨n, sf, hsf⟩ := S.finite_toSet.fin_embedding
  choose w hw using fun i : Fin n => Submodule.mkQ_surjective B (sf i)
  have hr : (Submodule.mkQ B) '' Set.range w = Set.range sf := by
    rw [← Set.range_comp, show (Submodule.mkQ B) ∘ w = sf from funext hw]
  have hgen : B ⊔ Submodule.span ℤ (Set.range w) = ⊤ := by
    letI : Module ℤ (Z ⧸ B) := Submodule.Quotient.module B
    have h := Submodule.comap_map_eq (Submodule.mkQ B) (Submodule.span ℤ (Set.range w))
    rw [Submodule.ker_mkQ, Submodule.map_span, hr, hsf, hS, Submodule.comap_top] at h
    rw [sup_comm, ← h]
  -- Step 3: kill the denominators of `F` on the chosen generators.
  let N : ℕ := ∏ i : Fin n, (F (w i)).den
  have hNpos : 0 < N := by
    dsimp only [N]
    exact Finset.prod_pos fun i _ => (F (w i)).den_pos
  have hNw : ∀ i : Fin n,
      (N : ℤ) • F (w i) = (((∏ j ∈ Finset.univ.erase i, (F (w j)).den : ℕ) : ℤ) * (F (w i)).num : ℚ) := by
    intro i
    have hsplit : N = (∏ j ∈ Finset.univ.erase i, (F (w j)).den) * (F (w i)).den := by
      dsimp only [N]
      exact (Finset.prod_erase_mul Finset.univ (fun j => (F (w j)).den) (Finset.mem_univ i)).symm
    have h1 : ((N : ℤ) : ℚ) = (((∏ j ∈ Finset.univ.erase i, (F (w j)).den : ℕ) : ℤ) : ℚ) *
        (((F (w i)).den : ℕ) : ℚ) := by
      rw [hsplit]; push_cast; try ring
    rw [zsmul_eq_mul, h1, mul_assoc, Rat.den_mul_eq_num]
  have key : ∀ x : Z, ∃ m : ℤ, ((m : ℚ) = (N : ℤ) • F x) := by
    intro x
    have hx : x ∈ B ⊔ Submodule.span ℤ (Set.range w) := by rw [hgen]; trivial
    obtain ⟨b, hb, y, hy, hxy⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hy
    have hFy : F y = ∑ i, c i • F (w i) := by
      rw [← hc, map_sum]
      exact Finset.sum_congr rfl fun i _ => hFsmulA (c i) (w i)
    have hx' : (N : ℤ) • F x = ((N : ℤ) * f ⟨b, hb⟩ : ℚ) +
        ∑ i, c i • ((((∏ j ∈ Finset.univ.erase i, (F (w j)).den : ℕ) : ℤ) * (F (w i)).num : ℤ) : ℚ) := by
      rw [← hxy, map_add, smul_add]
      congr 1
      · rw [hFb ⟨b, hb⟩, zsmul_eq_mul]
      · rw [hFy, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_smul, mul_comm (N : ℤ) (c i), ← smul_smul, hNw i]
        push_cast
        try ring
    refine ⟨(N : ℤ) * f ⟨b, hb⟩ +
        ∑ i, c i * ((∏ j ∈ Finset.univ.erase i, (F (w j)).den : ℕ) : ℤ) * (F (w i)).num, ?_⟩
    rw [hx', Int.cast_add, Int.cast_sum]
    congr 1
    · push_cast; try ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      rw [zsmul_eq_mul]
      try ring
  -- Step 4: package `N • F` as an integer-valued linear map.
  have hex : ∀ x : Z, ∃ m : ℤ, ((m : ℚ) = (N : ℤ) • F x) := key
  refine ⟨N, hNpos, ?_⟩
  let gfun : Z → ℤ := fun x => (hex x).choose
  have hgfun : ∀ x : Z, ((gfun x : ℤ) : ℚ) = (N : ℤ) • F x := fun x => (hex x).choose_spec
  have hgz : gfun 0 = 0 := by
    apply Int.cast_injective (α := ℚ)
    rw [hgfun, map_zero, smul_zero, Int.cast_zero]
  have hgadd : ∀ x y : Z, gfun (x + y) = gfun x + gfun y := by
    intro x y
    apply Int.cast_injective (α := ℚ)
    rw [Int.cast_add, hgfun, hgfun, hgfun, map_add, smul_add]
  let gadd : Z →+ ℤ := { toFun := gfun, map_zero' := hgz, map_add' := hgadd }
  have hgsmul : ∀ (m : ℤ) (x : Z), gfun (instZ.smul m x) = m • gfun x := fun m x => by
    rw [int_smul_eq_zsmul instZ m x]
    exact map_zsmul gadd m x
  refine ⟨{ toFun := gfun, map_add' := hgadd, map_smul' := fun m x => hgsmul m x }, fun b => ?_⟩
  apply Int.cast_injective (α := ℚ)
  change ((gfun ↑b : ℤ) : ℚ) = (((N : ℤ) • f b : ℤ) : ℚ)
  rw [hgfun, hFb b, zsmul_eq_mul, zsmul_eq_mul, Int.cast_mul]
  try simp only [Int.cast_natCast]
  try ring

end Work.ThomBordism
