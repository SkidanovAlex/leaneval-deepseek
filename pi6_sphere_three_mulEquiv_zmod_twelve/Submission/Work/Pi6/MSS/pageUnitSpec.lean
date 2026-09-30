import Mathlib
import Submission.Work.Pi6.MSS.e2Aux
import Submission.Work.Pi6.MSS.AssembleCore
import Submission.Work.Pi6.MSS.SerreCF
import Submission.Work.Pi6.MSS.mssMulCompat
import Submission.Work.Pi6.MSS.mssMulLeib
import Submission.Work.Cohomology.cupUnit

/-!
# The unit of the `E_2` page of the Serre spectral sequence

The cohomology class of the augmentation `unitCochain 𝕜 (sSing E)` (the `0`-cochain which is `1`
on every vertex) lies in `Z_2^0 ⊆ C^0(E;𝕜)` — its coboundary vanishes — and its class in the
`E_2` page `pEraw 𝕜 (serreCF 𝕜 E B p) 2 0 0` is the two-sided multiplicative unit for the page
product `mssMul`, i.e. the unit of the cohomology ring `H^*(E;𝕜)`.

This is `mssPageUnit 𝕜 E B p` (`Submission/Work/Pi6/MSS/e2Aux.lean`), the input needed by the
fibre edge / Künneth compatibility of the multiplicative Serre spectral sequence: the class of the
augmentation is the unit of `E_2^{0,0}` (so that the edge maps `H^*(B) → E_2^{*,0}` and
`H^*(F) → E_2^{0,*}` are unital).

The proof reduces the page product, via `mssMul_apply_enn` and `pd_mul_nat`/`pd_mulZ_val`, to the
cup product of representatives, and then uses the unit laws `cupUnit` for the Alexander–Whitney
product.  The index bookkeeping (the bidegree `(0,0) + b = b` and the filtration degree
`0 + s = s`) is handled by the `xcast` toolkit below.
-/

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## The transport toolkit for `W.xcast` -/

/-- `W.xcast` depends on the equality only through its endpoints. -/
lemma pageUnit_xcast_congr {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜} {a b : ℕ} (h h' : a = b) :
    W.xcast h = W.xcast h' := by rw [Subsingleton.elim h h']

/-- Transporting back along a `W.xcast` is the identity. -/
lemma pageUnit_xcast_symm_xcast {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜} {a b : ℕ} (h : a = b)
    (y : W.C.X a) : W.xcast h.symm (W.xcast h y) = y := by
  have h1 : W.xcast h.symm (W.xcast h y) = W.xcast (h.trans h.symm) y := by
    rw [← LinearMap.comp_apply, CohFilt.xcast_trans]
  rw [h1, pageUnit_xcast_congr (h := h.trans h.symm) (h' := rfl), CohFilt.xcast_rfl]
  rfl

/-- `W.xcast` is the transport `h ▸ ·` of an element along the degree equality. -/
lemma pageUnit_xcast_eq_cast {𝕜 : Type} [Field 𝕜] {W : CohFilt 𝕜} {a b : ℕ} (h : a = b)
    (y : W.C.X a) : W.xcast h y = h ▸ y := by cases h; rw [CohFilt.xcast_rfl]; rfl

/-! ## The two unit laws at the level of a filtered cochain complex -/

/-- **Left unit law.**  If `u` is the class of a `0`-cocycle `c₀` which is a left unit for the
product of the cochain complex (after the degree identification `0 + n = n`), then `u` is a left
unit for the product on `E_2`. -/
theorem pageUnit_mssMul_unit_left {𝕜 : Type} [Field 𝕜] (W : CohFilt 𝕜)
    (b : ℤ × ℤ) (hb : Enn b) (h : ((0:ℤ),(0:ℤ)) + b = b)
    (u : pEraw 𝕜 W 2 0 0) (x : pEraw 𝕜 W 2 (EI b) (EN b))
    (c₀ : W.C.X 0) (hc₀ : c₀ ∈ pZ 𝕜 W 2 0 0)
    (hu : u = Submodule.mkQ ((pDen 𝕜 W 2 (EI ((0:ℤ),(0:ℤ))) (EN ((0:ℤ),(0:ℤ)))).comap
            (pZ 𝕜 W 2 (EI ((0:ℤ),(0:ℤ))) (EN ((0:ℤ),(0:ℤ)))).subtype) ⟨c₀, hc₀⟩)
    (hunit : ∀ (n : ℕ) (y : W.C.X n), W.xcast (Nat.zero_add n) (W.mul 0 n c₀ y) = y) :
    mssMul 𝕜 W 2 ((0:ℤ),(0:ℤ)) b b h u x = x := by
  rw [mssMul_apply_enn (a := ((0:ℤ),(0:ℤ))) (b := b) (c := b)
    (ha := ⟨le_refl 0, le_refl 0⟩) (hb := hb) (h := h)]
  rw [pEcast_hom_apply_comp]
  obtain ⟨x', rfl⟩ := Submodule.mkQ_surjective
    ((pDen 𝕜 W 2 (EI b) (EN b)).comap (pZ 𝕜 W 2 (EI b) (EN b)).subtype) x
  rw [hu]
  rw [pd_mul_nat 2 (EI ((0:ℤ),(0:ℤ))) (EN ((0:ℤ),(0:ℤ))) (EI b) (EN b) ⟨c₀, hc₀⟩ x']
  set HE := (EI_add ⟨le_refl 0, le_refl 0⟩ hb).trans (congrArg EI h) with hHE
  set KE := (EN_add ⟨le_refl 0, le_refl 0⟩ hb).trans (congrArg EN h) with hKE
  rw [pd_pEcast_mkQ' (h := HE) (h' := KE)]
  apply pd_mkQ_congr
  show W.xcast KE ((pd_mulZ 2 (EI ((0:ℤ),(0:ℤ))) (EN ((0:ℤ),(0:ℤ))) (EI b) (EN b) ⟨c₀, hc₀⟩ x').1
    : W.C.X (EN ((0:ℤ),(0:ℤ)) + EN b)) = x'.1
  have hz : (pd_mulZ 2 (EI ((0:ℤ),(0:ℤ))) (EN ((0:ℤ),(0:ℤ))) (EI b) (EN b) ⟨c₀, hc₀⟩ x').1
      = W.xcast (Nat.zero_add (EN b)).symm x'.1 := by
    calc (pd_mulZ 2 (EI ((0:ℤ),(0:ℤ))) (EN ((0:ℤ),(0:ℤ))) (EI b) (EN b) ⟨c₀, hc₀⟩ x').1
        = W.xcast (Nat.zero_add (EN b)).symm
            (W.xcast (Nat.zero_add (EN b)) (W.mul 0 (EN b) c₀ x'.1)) :=
          (pageUnit_xcast_symm_xcast (h := Nat.zero_add (EN b))
            (y := W.mul 0 (EN b) c₀ x'.1)).symm
      _ = W.xcast (Nat.zero_add (EN b)).symm x'.1 := by rw [hunit (EN b) x'.1]
  rw [hz]
  have h4 : W.xcast KE (W.xcast (Nat.zero_add (EN b)).symm x'.1) = x'.1 := by
    have h1 : W.xcast KE (W.xcast (Nat.zero_add (EN b)).symm x'.1)
        = W.xcast ((Nat.zero_add (EN b)).symm.trans KE) x'.1 := by
      rw [← LinearMap.comp_apply, CohFilt.xcast_trans]
    rw [h1, pageUnit_xcast_congr (h := (Nat.zero_add (EN b)).symm.trans KE) (h' := rfl),
      CohFilt.xcast_rfl]
    rfl
  exact h4

/-- **Right unit law.**  If `u` is the class of a `0`-cocycle `c₀` which is a right unit for the
product of the cochain complex, then `u` is a right unit for the product on `E_2`. -/
theorem pageUnit_mssMul_unit_right {𝕜 : Type} [Field 𝕜] (W : CohFilt 𝕜)
    (b : ℤ × ℤ) (hb : Enn b) (h : b + ((0:ℤ),(0:ℤ)) = b)
    (u : pEraw 𝕜 W 2 0 0) (x : pEraw 𝕜 W 2 (EI b) (EN b))
    (c₀ : W.C.X 0) (hc₀ : c₀ ∈ pZ 𝕜 W 2 0 0)
    (hu : u = Submodule.mkQ ((pDen 𝕜 W 2 (EI ((0:ℤ),(0:ℤ))) (EN ((0:ℤ),(0:ℤ)))).comap
            (pZ 𝕜 W 2 (EI ((0:ℤ),(0:ℤ))) (EN ((0:ℤ),(0:ℤ)))).subtype) ⟨c₀, hc₀⟩)
    (hunitR : ∀ (n : ℕ) (y : W.C.X n), W.mul n 0 y c₀ = y) :
    mssMul 𝕜 W 2 b ((0:ℤ),(0:ℤ)) b h x u = x := by
  rw [mssMul_apply_enn (a := b) (b := ((0:ℤ),(0:ℤ))) (c := b)
    (ha := hb) (hb := ⟨le_refl 0, le_refl 0⟩) (h := h)]
  rw [pEcast_hom_apply_comp]
  obtain ⟨x', rfl⟩ := Submodule.mkQ_surjective
    ((pDen 𝕜 W 2 (EI b) (EN b)).comap (pZ 𝕜 W 2 (EI b) (EN b)).subtype) x
  rw [hu]
  rw [pd_mul_nat 2 (EI b) (EN b) (EI ((0:ℤ),(0:ℤ))) (EN ((0:ℤ),(0:ℤ))) x' ⟨c₀, hc₀⟩]
  set HE := (EI_add hb ⟨le_refl 0, le_refl 0⟩).trans (congrArg EI h) with hHE
  set KE := (EN_add hb ⟨le_refl 0, le_refl 0⟩).trans (congrArg EN h) with hKE
  rw [pd_pEcast_mkQ' (h := HE) (h' := KE)]
  apply pd_mkQ_congr
  show W.xcast KE ((pd_mulZ 2 (EI b) (EN b) (EI ((0:ℤ),(0:ℤ))) (EN ((0:ℤ),(0:ℤ))) x' ⟨c₀, hc₀⟩).1
      : W.C.X (EN b + EN ((0:ℤ),(0:ℤ)))) = x'.1
  have hz : (pd_mulZ 2 (EI b) (EN b) (EI ((0:ℤ),(0:ℤ))) (EN ((0:ℤ),(0:ℤ))) x' ⟨c₀, hc₀⟩).1
      = x'.1 := by
    rw [pd_mulZ_val]
    exact hunitR (EN b) x'.1
  rw [hz]
  have h4 : W.xcast KE x'.1 = x'.1 := by
    rw [pageUnit_xcast_congr (h := KE) (h' := (rfl : EN b = EN b)), CohFilt.xcast_rfl]
    rfl
  exact h4

/-! ## The unit of the `E_2` page -/

theorem pageUnitSpec (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B))
    (h : Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E) ∈
      Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 0) :
    Work.Pi6.MSS.mssPageUnit 𝕜 E B p
      (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 0).comap
          (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 0).subtype)
        ⟨Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E), h⟩) := by
  constructor
  · intro s q x
    refine pageUnit_mssMul_unit_left (𝕜 := 𝕜) (W := Work.Pi6.MSS.serreCF 𝕜 E B p)
      ((s:ℤ),(q:ℤ)) (Work.Pi6.MSS.Enn_pair s q) (by ext <;> simp)
      (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 0).comap
          (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 0).subtype)
        ⟨Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E), h⟩)
      x (Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E)) h rfl ?_
    intro n y
    have h1 := (Work.Cohomology.cupUnit 𝕜 (Work.SSS.sSing E) y).1
    rw [pageUnit_xcast_eq_cast]
    change (Nat.zero_add n) ▸ (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E)
      (Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E)) y) = y
    exact h1
  · intro s q x
    refine pageUnit_mssMul_unit_right (𝕜 := 𝕜) (W := Work.Pi6.MSS.serreCF 𝕜 E B p)
      ((s:ℤ),(q:ℤ)) (Work.Pi6.MSS.Enn_pair s q) (by ext <;> simp)
      (Submodule.mkQ ((Work.Pi6.MSS.pDen 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 0).comap
          (Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 2 0 0).subtype)
        ⟨Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E), h⟩)
      x (Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E)) h rfl ?_
    intro n y
    change (Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) y
      (Work.Cohomology.unitCochain 𝕜 (Work.SSS.sSing E))) = y
    exact (Work.Cohomology.cupUnit 𝕜 (Work.SSS.sSing E) y).2

end

end Work.Pi6.MSS
