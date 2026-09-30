/-
# The coefficient-sum retraction of the closed cell is a quasi-isomorphism

For a `PolyCW` `P` and a cell `e`, the order complex of the closed cell `Iic e` is a cone (with
apex the cell `e` itself), so its chain complex `leSubCx P e` is homotopy equivalent to `ℤ`
concentrated in degree `0`.  The chain contraction is an explicit cone homotopy
`H_k = (-1)^k • coneLM_e`, and it exhibits the coefficient-sum retraction
`leSubRetr P e : leSubCx P e ⟶ unitCx 0` as one half of a homotopy equivalence.

This file proves the two chain-level identities that make the contraction work — the cone
identity of `Work.Subdivision.D_coneLM` made into a degreewise statement on the closed cell
(`D_coneLM_leSub`, `D_coneLM_leSub_zero`) — and deduces `QuasiIso (leSubRetr P e)`.
-/
import Mathlib
import Submission.Work.MbarHomology.Local.StageCx

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

universe u

set_option allowUnsafeReducibility true


namespace Work.Subdivision

open CategoryTheory

noncomputable section

namespace PolyCW

attribute [local reducible] sdChain sdS sdSMod icF ioF leSubCx ltSubCx
  SubData.chain SubData.sub SubData.dL SubData.quot SubData.quotOf unitCx unitMod

variable (P : PolyCW.{u})

/-! ### The cone preserves the chains of a closed cell -/

/-- The cone on a simplex with all vertices `≤ e` is supported on the closed cell of `e`. -/
theorem coneLM_single_mem_leSub (e : P.Cell) (k : ℕ) (σ : Simplex P.Cell k)
    (hσ : ∀ i, σ i ≤ e) :
    coneLM P e k (Finsupp.single σ (1 : ℤ)) ∈ leSub P e (k + 1) := by
  by_cases h : ∀ i, σ i < e
  · rw [coneLM_single P e k σ h]
    exact sdElem_mem_leSub P (fun i => by
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · rw [Simplex.snoc_apply_castSucc]; exact hσ j
      · rw [Simplex.snoc_apply_last])
  · have h1 : coneLM P e k (Finsupp.single σ (1 : ℤ)) = 0 := by
      simp only [coneLM, Finsupp.linearCombination_single, one_smul, dite_eq_right h]
    rw [h1]
    exact Submodule.zero_mem _

/-- The cone preserves the `k`-chains supported on the closed cell of `e`. -/
theorem coneLM_mem_leSub_of_mem (e : P.Cell) (k : ℕ) {x : chainMod P.Cell k} (hx : x ∈ leSub P e k) :
    coneLM P e k x ∈ leSub P e (k + 1) := by
  have hle : Submodule.span ℤ {y : chainMod P.Cell k | ∃ σ, (∀ i, σ i ≤ e) ∧ y = Finsupp.single σ 1} ≤
      Submodule.comap (coneLM P e k) (leSub P e (k + 1)) := by
    rw [Submodule.span_le]
    rintro y ⟨σ, hσ, rfl⟩
    exact coneLM_single_mem_leSub P e k σ hσ
  exact hle hx

/-- The cone preserves the chains of the closed cell, in the form used by `leSubCx`. -/
theorem coneLM_mem_sdSMod_icF (e : P.Cell) (k : ℕ) {x : (sdChain P).X k}
    (hx : x ∈ sdSMod P (icF P e) k) : coneLM P e k x ∈ sdSMod P (icF P e) (k + 1) := by
  rw [sdSMod_icF P e k] at hx
  rw [sdSMod_icF P e (k + 1)]
  exact coneLM_mem_leSub_of_mem P e k hx

/-! ### The top vertex of a simplex of the closed cell -/

/-- A simplex of the closed cell of `e` whose last vertex is `e` is the cone, with apex `e`,
on its last face. -/
theorem snoc_face_last (e : P.Cell) (k : ℕ) (σ : Simplex P.Cell (k + 1)) (hσ : ∀ i, σ i ≤ e)
    (he : σ (Fin.last (k + 1)) = e) (h' : ∀ i, (Simplex.face (Fin.last (k + 1)) σ) i < e) :
    Simplex.snoc (Simplex.face (Fin.last (k + 1)) σ) e h' = σ := by
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Simplex.snoc_apply_castSucc, Simplex.face_apply, Fin.succAbove_last_apply]
  · rw [Simplex.snoc_apply_last, he]

/-- If the closed cell of `e` contains a vertex equal to `e`, then `e` is the last vertex. -/
theorem eq_last_of_eq {e : P.Cell} {k : ℕ} {σ : Simplex P.Cell (k + 1)} (hσ : ∀ i, σ i ≤ e)
    {i : Fin (k + 2)} (hi : σ i = e) : σ (Fin.last (k + 1)) = e := by
  rcases eq_or_lt_of_le (Fin.le_last i) with h | h
  · rw [← h, hi]
  · have hlt := σ.strictMono h
    rw [hi] at hlt
    exact absurd (lt_of_lt_of_le hlt (hσ _)) (lt_irrefl e)

/-- The differential of a simplex of the closed cell whose last vertex is `e`, coned back with the
apex `e`, is the simplex itself: only the last face survives the cone. -/
theorem coneLM_D_single_of_last (e : P.Cell) (m : ℕ) (σ : Simplex P.Cell (m + 1))
    (hσ : ∀ i, σ i ≤ e) (hlast : σ (Fin.last (m + 1)) = e) :
    coneLM P e m (D (α := P.Cell) m (Finsupp.single σ (1 : ℤ)))
      = (-1 : ℤ) ^ (m + 1) • Finsupp.single σ (1 : ℤ) := by
  rw [D_single, map_sum]
  simp only [map_smul]
  rw [Fin.sum_univ_castSucc]
  have h' : ∀ i : Fin (m + 1), (Simplex.face (Fin.last (m + 1)) σ) i < e := by
    intro i
    rw [Simplex.face_apply, Fin.succAbove_last_apply]
    refine lt_of_le_of_ne (hσ i.castSucc) (fun hc => ?_)
    have hlt := σ.strictMono (Fin.castSucc_lt_last i)
    rw [hc, hlast] at hlt
    exact lt_irrefl e hlt
  have hzero : ∀ j : Fin (m + 1),
      coneLM P e m (Finsupp.single (Simplex.face (Fin.castSucc j) σ) (1 : ℤ)) = 0 := by
    intro j
    have hcont : ∃ i, (Simplex.face (Fin.castSucc j) σ) i = e := by
      refine ⟨Fin.last m, ?_⟩
      rw [Simplex.face_apply, Fin.succAbove_ne_last_last (Fin.ne_of_lt (Fin.castSucc_lt_last j)),
        hlast]
    obtain ⟨i, hi⟩ := hcont
    have hnot : ¬ (∀ i, (Simplex.face (Fin.castSucc j) σ) i < e) := by
      intro hh
      have h1 := hh i
      rw [hi] at h1
      exact lt_irrefl e h1
    simp only [coneLM, Finsupp.linearCombination_single, one_smul, dite_eq_right hnot]
  simp only [hzero, smul_zero, Finset.sum_const_zero, zero_add]
  rw [coneLM_single P e m (Simplex.face (Fin.last (m + 1)) σ) h',
    show Simplex.snoc (Simplex.face (Fin.last (m + 1)) σ) e h' = σ from
      snoc_face_last P e m σ hσ hlast h', Fin.val_last]

/-! ### The cone identity on the closed cell

The two identities below are the degreewise form of `Work.Subdivision.D_coneLM` (and of
`D_coneLM_zero` in degree `0`) restricted to the chains of the closed cell of `e`.  They say that
the degreewise family `H_k = (-1)^k • coneLM_e` is a chain contraction of the order complex of
`Iic e`. -/

/-- The cone identity in degree `m + 1` on a single simplex of the closed cell. -/
theorem D_coneLM_leSub_single (e : P.Cell) (m : ℕ) (σ : Simplex P.Cell (m + 1))
    (hσ : ∀ i, σ i ≤ e) :
    (-1 : ℤ) ^ (m + 1) • D (α := P.Cell) (m + 1) (coneLM P e (m + 1) (Finsupp.single σ (1 : ℤ)))
        + (-1 : ℤ) ^ m • coneLM P e m (D (α := P.Cell) m (Finsupp.single σ (1 : ℤ)))
      = -(Finsupp.single σ (1 : ℤ) : chainMod P.Cell (m + 1)) := by
  by_cases h : ∀ i, σ i < e
  · rw [D_coneLM P e m (Finsupp.single σ (1 : ℤ)) (single_mem_belowSub P h)]
    rw [smul_add, smul_smul]
    have h1 : (-1 : ℤ) ^ (m + 1) + (-1 : ℤ) ^ m = 0 := by ring
    have h2 : (-1 : ℤ) ^ (m + 1) * (-1 : ℤ) ^ (m + 2) = -1 := by
      rw [← pow_add, show m + 1 + (m + 2) = 2 * (m + 1) + 1 by ring, pow_succ, pow_mul]
      norm_num
    have hcombine : (-1 : ℤ) ^ (m + 1) • coneLM P e m (D (α := P.Cell) m (Finsupp.single σ (1 : ℤ)))
        + (-1 : ℤ) ^ m • coneLM P e m (D (α := P.Cell) m (Finsupp.single σ (1 : ℤ))) = 0 := by
      rw [← add_smul, h1, zero_smul]
    rw [h2, add_assoc,
      add_comm ((-1 : ℤ) • (Finsupp.single σ (1 : ℤ) : chainMod P.Cell (m + 1))), ← add_assoc,
      hcombine, zero_add]
    simp
  · obtain ⟨i, hi⟩ : ∃ i, σ i = e := by
      obtain ⟨i, hi⟩ := not_forall.mp h
      exact ⟨i, eq_of_le_of_not_lt (hσ i) hi⟩
    have hlast : σ (Fin.last (m + 1)) = e := eq_last_of_eq (P := P) hσ hi
    have hz : coneLM P e (m + 1) (Finsupp.single σ (1 : ℤ)) = 0 := by
      simp only [coneLM, Finsupp.linearCombination_single, one_smul, dite_eq_right h]
    rw [hz, map_zero, smul_zero, zero_add, coneLM_D_single_of_last P e m σ hσ hlast, smul_smul]
    have h1 : (-1 : ℤ) ^ m * (-1 : ℤ) ^ (m + 1) = -1 := by
      rw [← pow_add, show m + (m + 1) = 2 * m + 1 by ring, pow_succ, pow_mul]
      norm_num
    rw [h1]
    simp

/-- The cone identity in degree `m + 1` on the closed cell of `e`. -/
theorem D_coneLM_leSub (e : P.Cell) (m : ℕ) {x : chainMod P.Cell (m + 1)}
    (hx : x ∈ leSub P e (m + 1)) :
    (-1 : ℤ) ^ (m + 1) • D (α := P.Cell) (m + 1) (coneLM P e (m + 1) x)
        + (-1 : ℤ) ^ m • coneLM P e m (D (α := P.Cell) m x) = -x := by
  set L : chainMod P.Cell (m + 1) →ₗ[ℤ] chainMod P.Cell (m + 1) :=
    (-1 : ℤ) ^ (m + 1) • (D (α := P.Cell) (m + 1)).comp (coneLM P e (m + 1))
      + (-1 : ℤ) ^ m • (coneLM P e m).comp (D (α := P.Cell) m) + LinearMap.id with hL
  have hgen : ∀ σ : Simplex P.Cell (m + 1), (∀ i, σ i ≤ e) → L (Finsupp.single σ (1 : ℤ)) = 0 := by
    intro σ hσ
    rw [hL]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply]
    rw [D_coneLM_leSub_single P e m σ hσ]
    abel
  have hker : Submodule.span ℤ {z : chainMod P.Cell (m + 1) |
      ∃ σ, (∀ i, σ i ≤ e) ∧ z = Finsupp.single σ 1} ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro z ⟨σ, hσ, rfl⟩
    simpa using hgen σ hσ
  have h0 : L x = 0 := by simpa using hker hx
  rw [hL] at h0
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.id_apply]
    at h0
  exact (add_eq_zero_iff_eq_neg.mp h0)

/-- The cone identity in degree `0` on a single vertex of the closed cell. -/
theorem D_coneLM_leSub_zero_single (e : P.Cell) (σ : Simplex P.Cell 0) (hσ : ∀ i, σ i ≤ e) :
    D (α := P.Cell) 0 (coneLM P e 0 (Finsupp.single σ (1 : ℤ))) =
      coeffSum (Finsupp.single σ (1 : ℤ)) • Finsupp.single (Simplex.vertex e) (1 : ℤ)
        - Finsupp.single σ (1 : ℤ) := by
  have hσ0 : σ = Simplex.vertex (σ 0) := by
    ext i
    fin_cases i
    rfl
  rcases lt_or_eq_of_le (hσ 0) with h | h
  · have hmem : (Finsupp.single σ (1 : ℤ) : chainMod P.Cell 0) ∈ belowSub P e 0 := by
      refine single_mem_belowSub P (fun i => ?_)
      fin_cases i
      exact h
    rw [D_coneLM_zero P e _ hmem]
    abel
  · have hve : σ = Simplex.vertex e := by rw [hσ0, h]
    have hz : coneLM P e 0 (Finsupp.single σ (1 : ℤ)) = 0 := by
      have hnot : ¬ (∀ i : Fin 1, σ i < e) := by
        intro hh
        have h1 := hh 0
        rw [h] at h1
        exact lt_irrefl e h1
      simp only [coneLM, Finsupp.linearCombination_single, one_smul, dite_eq_right hnot]
    rw [hz, map_zero, hve]
    simp

/-- The cone identity in degree `0` on the closed cell of `e`. -/
theorem D_coneLM_leSub_zero (e : P.Cell) {x : chainMod P.Cell 0} (hx : x ∈ leSub P e 0) :
    D (α := P.Cell) 0 (coneLM P e 0 x) =
      coeffSum x • Finsupp.single (Simplex.vertex e) (1 : ℤ) - x := by
  set L : chainMod P.Cell 0 →ₗ[ℤ] chainMod P.Cell 0 :=
    (D (α := P.Cell) 0).comp (coneLM P e 0)
      - (coeffSum (α := P.Cell)).smulRight (Finsupp.single (Simplex.vertex e) (1 : ℤ))
      + LinearMap.id with hL
  have hgen : ∀ σ : Simplex P.Cell 0, (∀ i, σ i ≤ e) → L (Finsupp.single σ (1 : ℤ)) = 0 := by
    intro σ hσ
    rw [hL]
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
      LinearMap.comp_apply, LinearMap.id_apply]
    rw [D_coneLM_leSub_zero_single P e σ hσ]
    abel
  have hker : Submodule.span ℤ {z : chainMod P.Cell 0 |
      ∃ σ, (∀ i, σ i ≤ e) ∧ z = Finsupp.single σ 1} ≤ LinearMap.ker L := by
    rw [Submodule.span_le]
    rintro z ⟨σ, hσ, rfl⟩
    simpa using hgen σ hσ
  have h0 : L x = 0 := by simpa using hker hx
  rw [hL] at h0
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smulRight_apply,
    LinearMap.comp_apply, LinearMap.id_apply] at h0
  have h1 : D (α := P.Cell) 0 (coneLM P e 0 x)
      - coeffSum x • Finsupp.single (Simplex.vertex e) (1 : ℤ) = -x :=
    add_eq_zero_iff_eq_neg.mp h0
  rw [sub_eq_iff_eq_add] at h1
  rw [h1, add_comm]
  simp [sub_eq_add_neg]

/-! ### The cone contraction -/

/-- The `k`-th component of the cone contraction of the closed cell of `e`, as a linear map of the
chains of the closed cell. -/
noncomputable def leSubConeMap (e : P.Cell) (k : ℕ) :
    ↥(sdSMod P (icF P e) k) →ₗ[ℤ] ↥(sdSMod P (icF P e) (k + 1)) :=
  LinearMap.restrict (p := sdSMod P (icF P e) k) (q := sdSMod P (icF P e) (k + 1))
    (f := ((-1 : ℤ) ^ k) • coneLM P e k) (fun x hx => by
      rw [LinearMap.smul_apply]
      exact Submodule.smul_mem _ _ (coneLM_mem_sdSMod_icF P e k hx))

@[simp] theorem leSubConeMap_coe (e : P.Cell) (k : ℕ)
    (x : ↥(sdSMod P (icF P e) k)) :
    (leSubConeMap P e k x : (sdChain P).X (k + 1)) =
      (-1 : ℤ) ^ k • coneLM P e k (x : (sdChain P).X k) := rfl

/-- The `k`-th component of the cone contraction, as a morphism of the chain complex of the
closed cell of `e`. -/
noncomputable def leSubCone (e : P.Cell) (k : ℕ) :
    (leSubCx P e).X k ⟶ (leSubCx P e).X (k + 1) :=
  ModuleCat.ofHom (leSubConeMap P e k)

theorem leSubCone_hom (e : P.Cell) (k : ℕ) :
    (leSubCone P e k).hom = leSubConeMap P e k := rfl

/-- The degreewise family of the cone contraction, with the zero maps off the diagonal `j = i + 1`. -/
noncomputable def leSubHomFam (e : P.Cell) :
    ∀ i j, (leSubCx P e).X i ⟶ (leSubCx P e).X j :=
  fun i j => if h : j = i + 1 then leSubCone P e i ≫ eqToHom (by rw [h]) else 0

theorem leSubHomFam_succ (e : P.Cell) (i : ℕ) :
    leSubHomFam P e i (i + 1) = leSubCone P e i := by
  unfold leSubHomFam
  rw [dite_eq_left rfl, eqToHom_refl, Category.comp_id]

theorem leSubHomFam_rel_zero (e : P.Cell) (i j : ℕ)
    (h : ¬ (ComplexShape.down ℕ).Rel j i) : leSubHomFam P e i j = 0 := by
  unfold leSubHomFam
  exact dite_eq_right (fun hji => h (by rw [ComplexShape.down_Rel]; exact hji.symm))

/-! ### The homotopy inverse of the coefficient sum -/

/-- The `0`-simplex at `e` lies in the chains of the closed cell of `e`. -/
theorem sdElem_vertex_mem_icF (e : P.Cell) :
    sdElem P (Simplex.vertex e) ∈ sdSMod P (icF P e) 0 :=
  sdElem_mem_sdSMod P (icF P e) 0 (Simplex.vertex e) (fun _ => by simp [icF])

/-- The `0`-simplex at `e`, as a chain of the closed cell of `e`. -/
noncomputable def leSubVertex (e : P.Cell) : ↥(sdSMod P (icF P e) 0) :=
  ⟨sdElem P (Simplex.vertex e), sdElem_vertex_mem_icF P e⟩

/-- The inverse of the coefficient sum on the closed cell of `e`: the generator of `unitCx 0` is
sent to the `0`-simplex at `e`. -/
noncomputable def leSubVertLin (e : P.Cell) : ULift.{u} ℤ →ₗ[ℤ] ↥(sdSMod P (icF P e) 0) :=
  (LinearMap.toSpanSingleton ℤ ↥(sdSMod P (icF P e) 0) (leSubVertex P e)).comp
    (ULift.moduleEquiv (R := ℤ) (M := ℤ)).toLinearMap

@[simp] theorem leSubVertLin_apply (e : P.Cell) (z : ULift.{u} ℤ) :
    leSubVertLin P e z = (ULift.down z) • leSubVertex P e := by
  show ((LinearMap.toSpanSingleton ℤ ↥(sdSMod P (icF P e) 0) (leSubVertex P e)).comp
    (ULift.moduleEquiv (R := ℤ) (M := ℤ)).toLinearMap) z = _
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ULift.moduleEquiv_apply,
    LinearMap.toSpanSingleton_apply]

noncomputable def leSubVert (e : P.Cell) : unitMod.{u} ⟶ (leSubCx P e).X 0 :=
  ModuleCat.ofHom (leSubVertLin P e)

@[simp] theorem leSubVert_apply (e : P.Cell) (z : ULift.{u} ℤ) :
    leSubVert P e z = (ULift.down z) • leSubVertex P e := by
  show ModuleCat.Hom.hom (ModuleCat.ofHom (leSubVertLin P e)) z = _
  rw [ModuleCat.hom_ofHom]
  exact leSubVertLin_apply P e z

/-- The homotopy inverse of `leSubRetr P e`. -/
noncomputable def leSubInv (e : P.Cell) : unitCx 0 ⟶ leSubCx P e :=
  (ChainComplex.fromSingle₀Equiv (leSubCx P e) unitMod).symm (leSubVert P e)

@[simp] theorem leSubInv_f_zero (e : P.Cell) :
    (leSubInv P e).f 0 = (leSubVert P e : unitMod.{u} ⟶ (leSubCx P e).X 0) :=
  ChainComplex.fromSingle₀Equiv_symm_apply_f_zero (leSubVert P e)

@[simp] theorem leSubInv_f_succ (e : P.Cell) (n : ℕ) : (leSubInv P e).f (n + 1) = 0 :=
  ChainComplex.fromSingle₀Equiv_symm_apply_f_succ (leSubVert P e) n

theorem leSubCoeff_apply (e : P.Cell) (x : ↥(sdSMod P (icF P e) 0)) :
    leSubCoeff P e x = ULift.up (coeffSum (α := P.Cell)
      ((Submodule.subtype (sdSMod P (icF P e) 0)) x)) := rfl

@[simp] theorem leSubRetr_f_zero (e : P.Cell) :
    (leSubRetr P e).f 0
      = (ModuleCat.ofHom (leSubCoeff P e) : (leSubCx P e).X 0 ⟶ (unitCx 0).X 0) := by
  simp only [leSubRetr, HomologicalComplex.mkHomToSingle_f, ChainComplex.single₀ObjXSelf,
    Iso.refl_inv]
  exact Category.comp_id _

/-- The coefficient sum retracts the inclusion of the `0`-simplex at `e`. -/
theorem leSubInv_comp_leSubRetr (e : P.Cell) :
    leSubInv P e ≫ leSubRetr P e = 𝟙 (unitCx 0) := by
  refine HomologicalComplex.to_single_hom_ext ?_
  rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, leSubInv_f_zero, leSubRetr_f_zero]
  show leSubVert P e ≫ ModuleCat.ofHom (leSubCoeff P e) = 𝟙 unitMod.{u}
  refine ModuleCat.hom_ext (LinearMap.ext fun z => ?_)
  rw [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply]
  show leSubCoeff P e (leSubVert P e z) = z
  rw [leSubVert_apply, map_smul, leSubCoeff_apply]
  simp only [Submodule.subtype_apply]
  have hc : coeffSum (α := P.Cell) (leSubVertex P e).1 = 1 := by
    show coeffSum (α := P.Cell) (sdElem P (Simplex.vertex e)) = 1
    exact coeffSum_single _
  rw [hc]
  exact ULift.ext (by simp)

/-! ### The two homotopy identities on the closed cell -/

/-- The coefficient sum on the chains of the closed cell, as a linear map. -/
noncomputable def subCoeffSum (e : P.Cell) : ↥(sdSMod P (icF P e) 0) →ₗ[ℤ] ℤ :=
  (coeffSum (α := P.Cell)).comp (Submodule.subtype (sdSMod P (icF P e) 0))

theorem subCoeffSum_apply (e : P.Cell) (x : ↥(sdSMod P (icF P e) 0)) :
    subCoeffSum P e x = coeffSum (α := P.Cell) (Submodule.subtype _ x) := rfl

/-- The degree `0` homotopy identity: the cone on a `0`-chain of the closed cell is a chain
whose boundary is the coefficient sum minus the chain itself. -/
theorem leSubCone_dL_zero (e : P.Cell) :
    ((sdS P (icF P e)).dL 0).comp (leSubConeMap P e 0)
      = (leSubVertLin P e).comp (leSubCoeff P e) - LinearMap.id := by
  have hx : ∀ x : ↥(sdSMod P (icF P e) 0), (x : (sdChain P).X 0) ∈ leSub P e 0 := by
    intro x
    rw [← sdSMod_icF P e 0]
    exact x.2
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.id_apply]
  apply Subtype.ext
  rw [Submodule.coe_sub]
  have h1 : (↑(((sdS P (icF P e)).dL 0) (leSubConeMap P e 0 x)) : (sdChain P).X 0)
      = D (α := P.Cell) 0 (coneLM P e 0 (x : (sdChain P).X 0)) := by
    rw [SubData.dL_apply, sdChain_d, ModuleCat.hom_ofHom, leSubConeMap_coe, pow_zero, one_smul]
  have h2 : (↑(leSubVertLin P e (leSubCoeff P e x)) : (sdChain P).X 0)
      = coeffSum (α := P.Cell) (x : (sdChain P).X 0) • sdElem P (Simplex.vertex e) := by
    rw [leSubVertLin_apply, Submodule.coe_smul, leSubCoeff_apply, ULift.down_up,
      Submodule.subtype_apply]
    rfl
  rw [h1, h2, D_coneLM_leSub_zero P e (hx x)]
  rfl

/-- The degree `m + 1` homotopy identity on the closed cell of `e`. -/
theorem leSubCone_dL_succ (e : P.Cell) (m : ℕ) :
    (leSubConeMap P e m).comp ((sdS P (icF P e)).dL m)
        + ((sdS P (icF P e)).dL (m + 1)).comp (leSubConeMap P e (m + 1))
      = -LinearMap.id := by
  have hx : ∀ x : ↥(sdSMod P (icF P e) (m + 1)),
      (x : (sdChain P).X (m + 1)) ∈ leSub P e (m + 1) := by
    intro x
    rw [← sdSMod_icF P e (m + 1)]
    exact x.2
  refine LinearMap.ext fun x => ?_
  simp only [LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply, LinearMap.id_apply]
  have h1 : (↑(leSubConeMap P e m (((sdS P (icF P e)).dL m) x)) : (sdChain P).X (m + 1))
      = (-1 : ℤ) ^ m • coneLM P e m (D (α := P.Cell) m (x : (sdChain P).X (m + 1))) := by
    rw [leSubConeMap_coe, SubData.dL_apply, sdChain_d, ModuleCat.hom_ofHom]
  have h2 : (↑(((sdS P (icF P e)).dL (m + 1)) (leSubConeMap P e (m + 1) x)) :
        (sdChain P).X (m + 1))
      = (-1 : ℤ) ^ (m + 1) • D (α := P.Cell) (m + 1)
          (coneLM P e (m + 1) (x : (sdChain P).X (m + 1))) := by
    rw [SubData.dL_apply, sdChain_d, ModuleCat.hom_ofHom, leSubConeMap_coe, map_smul]
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_neg, h1, h2]
  simpa [add_comm] using D_coneLM_leSub P e m (hx x)


/-! ### The homotopy identity

We now assemble the two linear-map identities above into the statement that the family
`leSubHomFam` is a chain homotopy from `leSubRetr ≫ leSubInv` to the identity of `leSubCx P e`.
-/

/-- The differential of the closed cell of `e`, as an explicit morphism. -/
theorem leSubCx_d_eq (e : P.Cell) (k : ℕ) :
    (leSubCx P e).d (k + 1) k = ModuleCat.ofHom ((sdS P (icF P e)).dL k) :=
  SubData.chain_d (sdS P (icF P e)) k

/-- The cone contraction, as an explicit morphism. -/
theorem leSubCone_eq (e : P.Cell) (k : ℕ) :
    leSubCone P e k = ModuleCat.ofHom (leSubConeMap P e k) := rfl

/-- The degree `0` component of the homotopy inverse. -/
theorem leSubInv_f_zero_eq (e : P.Cell) :
    (leSubInv P e).f 0 = ModuleCat.ofHom (leSubVertLin P e) := by
  rw [leSubInv_f_zero]
  rfl

/-- The degree `0` component of `leSubRetr ≫ leSubInv`. -/
theorem leSubRetr_comp_leSubInv_f_zero (e : P.Cell) :
    ((leSubRetr P e ≫ leSubInv P e).f 0)
      = ModuleCat.ofHom ((leSubVertLin P e).comp (leSubCoeff P e)) := by
  rw [HomologicalComplex.comp_f, leSubRetr_f_zero, leSubInv_f_zero]
  rw [show leSubVert P e = ModuleCat.ofHom (leSubVertLin P e) from rfl]
  exact (ModuleCat.ofHom_comp (leSubCoeff P e) (leSubVertLin P e)).symm

/-- **The chain homotopy identity**: the family `leSubHomFam` is a chain homotopy from
`leSubRetr ≫ leSubInv` to the identity of the chain complex of the closed cell of `e`. -/
theorem nullHomotopicMap_eq (e : P.Cell) :
    Homotopy.nullHomotopicMap (leSubHomFam P e)
      = leSubRetr P e ≫ leSubInv P e - 𝟙 (leSubCx P e) := by
  refine HomologicalComplex.hom_ext _ _ (fun k => ?_)
  rcases k with _ | m
  · rw [Homotopy.nullHomotopicMap_f_of_not_rel_left (k₁ := 1) (k₀ := 0)
      ((ComplexShape.down_Rel ℕ 1 0).mpr rfl) (fun l => by rw [ComplexShape.down_Rel]; omega)
      (leSubHomFam P e)]
    rw [leSubHomFam_succ, leSubCone_eq, leSubCx_d_eq, ← ModuleCat.ofHom_comp,
      leSubCone_dL_zero]
    rw [show (leSubRetr P e ≫ leSubInv P e - 𝟙 (leSubCx P e)).f 0
        = (leSubRetr P e ≫ leSubInv P e).f 0 - 𝟙 ((leSubCx P e).X 0) from rfl]
    rw [leSubRetr_comp_leSubInv_f_zero]
    refine ModuleCat.hom_ext ?_
    rw [ModuleCat.hom_sub, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_id]
  · rw [Homotopy.nullHomotopicMap_f (k₂ := m + 2) (k₁ := m + 1) (k₀ := m)
      ((ComplexShape.down_Rel ℕ (m + 2) (m + 1)).mpr rfl)
      ((ComplexShape.down_Rel ℕ (m + 1) m).mpr rfl) (leSubHomFam P e)]
    rw [leSubHomFam_succ, leSubHomFam_succ, leSubCone_eq, leSubCone_eq, leSubCx_d_eq,
      leSubCx_d_eq, ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_add,
      leSubCone_dL_succ (e := e) (m := m)]
    rw [show (leSubRetr P e ≫ leSubInv P e - 𝟙 (leSubCx P e)).f (m + 1)
        = (leSubRetr P e ≫ leSubInv P e).f (m + 1) - 𝟙 ((leSubCx P e).X (m + 1)) from rfl]
    rw [HomologicalComplex.comp_f, leSubInv_f_succ, Limits.comp_zero, zero_sub]
    refine ModuleCat.hom_ext ?_
    rw [ModuleCat.hom_ofHom, ModuleCat.hom_neg, ModuleCat.hom_id]

/-- The cone contraction exhibits `leSubRetr ≫ leSubInv` as homotopic to the identity of the
chain complex of the closed cell of `e`. -/
noncomputable def leSubHomotopy (e : P.Cell) :
    Homotopy (leSubRetr P e ≫ leSubInv P e) (𝟙 (leSubCx P e)) := by
  have h : Homotopy (leSubRetr P e ≫ leSubInv P e - 𝟙 (leSubCx P e)) 0 :=
    nullHomotopicMap_eq P e ▸
      Homotopy.nullHomotopy (leSubHomFam P e) (leSubHomFam_rel_zero P e)
  exact (Homotopy.equivSubZero).symm h

/-- **The coefficient-sum retraction is a homotopy equivalence** between the chain complex of the
closed cell of `e` and `ℤ` concentrated in degree `0`. -/
noncomputable def leSubHomotopyEquiv (e : P.Cell) :
    HomotopyEquiv (leSubCx P e) (unitCx 0) where
  hom := leSubRetr P e
  inv := leSubInv P e
  homotopyHomInvId := leSubHomotopy P e
  homotopyInvHomId := Homotopy.ofEq (leSubInv_comp_leSubRetr P e)

end PolyCW

end

end Work.Subdivision

namespace Work.MbarHomology.Local

open CategoryTheory

/-- **The coefficient-sum retraction of the closed cell of a cell is a quasi-isomorphism.** -/
theorem leSubRetr_quasiIso (P : Work.Subdivision.PolyCW.{u}) (e : P.Cell) :
    QuasiIso (Work.Subdivision.PolyCW.leSubRetr P e) := by
  refine ⟨fun i => (quasiIsoAt_iff_isIso_homologyMap _ i).mpr ?_⟩
  exact Iso.isIso_hom ((Work.Subdivision.PolyCW.leSubHomotopyEquiv P e).toHomologyIso i)

end Work.MbarHomology.Local
