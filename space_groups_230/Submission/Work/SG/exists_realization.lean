import Mathlib
import Submission.Work.SG.Defs
import Submission.Work.SG.realize_defs
import Submission.Work.SG.weyl_orthogonalize
import Submission.Work.SG.gOf_mul
import Submission.Work.SG.conj_gOf_apply
import Submission.Work.SG.isDiscrete_idxFun
import Submission.Work.SG.cocompact_idxFun

/-! # Realisation of an integral datum `(P, τ)`

`exists_realization`: every integral point group equipped with a cocycle is realised, up to
conjugation by an affine map of positive determinant, by a crystallographic group of Euclidean
motions.  Route: conjugate `P` into `O(3)` by the symmetric square root `M` of `∑ AᵀA`
(`weyl_orthogonalize`), build the motions `x ↦ M A M⁻¹ x + M (τ A + n)`, and conjugate back by
`x ↦ M⁻¹ x`. -/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem
open Matrix

/-! ### Auxiliary lemmas -/

/-- An integral point group is closed under inverses. -/
lemma inv_mem_of_isIntPointGroup {P : Set IMat} (hP : IsIntPointGroup P) {A : IMat} (hA : A ∈ P) :
    A⁻¹ ∈ P := by
  have hunit : IsUnit A.det := hP.2.2.2 A hA
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hunit
  set s := hP.1.toFinset with hs
  have hsub : s.image (fun B => B * A) ⊆ s := by
    intro B hB
    obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hB
    rw [hs, Set.Finite.mem_toFinset] at hC ⊢
    exact hP.2.2.1 C hC A hA
  have hinj : Function.Injective (fun B : IMat => B * A) := by
    intro B C hBC
    have hBC' : B * A = C * A := hBC
    calc B = B * A * A⁻¹ := by rw [mul_assoc, hAA, mul_one]
      _ = C * A * A⁻¹ := by rw [hBC']
      _ = C := by rw [mul_assoc, hAA, mul_one]
  have hcard : (s.image (fun B => B * A)).card = s.card :=
    Finset.card_image_of_injective s hinj
  have heq : s.image (fun B => B * A) = s :=
    Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
  have h1mem : (1 : IMat) ∈ s.image (fun B => B * A) := by
    rw [heq, hs, Set.Finite.mem_toFinset]
    exact hP.2.1
  obtain ⟨B, hB, hBA⟩ := Finset.mem_image.mp h1mem
  have hBA' : B * A = 1 := hBA
  have hBP : B ∈ P := by simpa [hs, Set.Finite.mem_toFinset] using hB
  have hB' : B = A⁻¹ := by
    calc B = B * (A * A⁻¹) := by rw [hAA, mul_one]
      _ = (B * A) * A⁻¹ := by rw [mul_assoc]
      _ = A⁻¹ := by rw [hBA', one_mul]
  subst hB'
  exact hBP

/-- A chosen integral correction in the cocycle relation. -/
noncomputable def cocycleVec {P : Set IMat} {τ : IMat → Fin 3 → ℝ} (hτ : IsIntCocycle P τ)
    (A : IMat) (hA : A ∈ P) (B : IMat) (hB : B ∈ P) : Fin 3 → ℤ :=
  Classical.choose (hτ A hA B hB)

lemma cocycleVec_spec {P : Set IMat} {τ : IMat → Fin 3 → ℝ} (hτ : IsIntCocycle P τ)
    {A : IMat} (hA : A ∈ P) {B : IMat} (hB : B ∈ P) :
    τ (A * B) = τ A + Matrix.mulVec (realMat A) (τ B) + intVec (cocycleVec hτ A hA B hB) :=
  Classical.choose_spec (hτ A hA B hB)

/-- `τ 1` is an integral vector. -/
lemma exists_intVec_tau_one {P : Set IMat} {τ : IMat → Fin 3 → ℝ} (hP : IsIntPointGroup P)
    (hτ : IsIntCocycle P τ) : ∃ n₀ : Fin 3 → ℤ, τ 1 = intVec n₀ := by
  obtain ⟨n, hn⟩ := hτ 1 hP.2.1 1 hP.2.1
  refine ⟨-n, ?_⟩
  have h3 : τ 1 + (τ 1 + intVec n) = τ 1 + (0 : Fin 3 → ℝ) := by
    rw [add_zero]
    simpa only [add_assoc, mul_one, map_intCast_one, Matrix.one_mulVec] using hn.symm
  have hzero : τ 1 + intVec n = 0 := add_left_cancel h3
  have h4 : τ 1 = -(intVec n) := eq_neg_of_add_eq_zero_left hzero
  rw [h4, intVec_neg_rz]

/-- Conjugating an integer matrix by `M`, then by `M` on the right, simplifies. -/
lemma oConj_mul (M : RMat) (hMl : M⁻¹ * M = 1) (A B : IMat) :
    oConj M A * oConj M B = oConj M (A * B) := by
  simp only [oConj, realMat_mul, mul_assoc]
  rw [← mul_assoc M⁻¹ M (realMat B * M⁻¹), hMl, one_mul]

lemma oConj_mul_M (M : RMat) (hMl : M⁻¹ * M = 1) (A : IMat) : oConj M A * M = M * realMat A := by
  simp only [oConj]
  rw [mul_assoc, hMl, mul_one]

lemma inv_mulVec_M (M : RMat) (hMl : M⁻¹ * M = 1) (v : Fin 3 → ℝ) : M⁻¹ *ᵥ (M *ᵥ v) = v := by
  rw [mulVec_mulVec, hMl, Matrix.one_mulVec]

theorem exists_realization {P : Set IMat} {τ : IMat → Fin 3 → ℝ} (hP : IsIntPointGroup P)
    (hτ : IsIntCocycle P τ) :
    ∃ G : CrystallographicGroup 3, ∃ φ : AffineGroup 3, 0 < (φ.linear.det : ℝ) ∧
      conjSet φ (affImage G.1) = sgSet P τ := by
  classical
  have hP1 : (1 : IMat) ∈ P := hP.2.1
  have hPmul : ∀ A ∈ P, ∀ B ∈ P, A * B ∈ P := hP.2.2.1
  have hPunit : ∀ A ∈ P, IsUnit A.det := hP.2.2.2
  -- the real image of `P`
  set Pf : Finset RMat := hP.1.toFinset.image realMat with hPfdef
  have hPf1 : (1 : RMat) ∈ Pf := by
    rw [hPfdef, Finset.mem_image]
    refine ⟨1, ?_, ?_⟩
    · rw [Set.Finite.mem_toFinset]; exact hP1
    · simp
  have hPfmul : ∀ A ∈ Pf, ∀ B ∈ Pf, A * B ∈ Pf := by
    intro A hA B hB
    rw [hPfdef] at hA hB ⊢
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hB
    have haP : a ∈ P := by simpa using ha
    have hbP : b ∈ P := by simpa using hb
    rw [← realMat_mul, Finset.mem_image]
    refine ⟨a * b, ?_, rfl⟩
    rw [Set.Finite.mem_toFinset]
    exact hPmul a haP b hbP
  have hPfun : ∀ A ∈ Pf, A.det ≠ 0 := by
    intro A hA
    rw [hPfdef] at hA
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hA
    have haP : a ∈ P := by simpa using ha
    rw [realMat_det]
    exact fun h => (hPunit a haP).ne_zero (by exact_mod_cast h)
  obtain ⟨M, hMsym, hMM, hMdetpos, horthPf⟩ := weyl_orthogonalize Pf hPf1 hPfmul hPfun
  have hMdet0 : M.det ≠ 0 := ne_of_gt hMdetpos
  have hMr : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hMdet0)
  have hMl : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hMdet0)
  have horth : ∀ A ∈ P, Matrix.transpose (oConj M A) * (oConj M A) = 1 := by
    intro A hA
    have hmem : realMat A ∈ Pf := by
      rw [hPfdef, Finset.mem_image]; exact ⟨A, by simpa using hA, rfl⟩
    simpa [oConj] using horthPf (realMat A) hmem
  -- `τ 1` is integral
  obtain ⟨n₀, hn₀⟩ := exists_intVec_tau_one hP hτ
  -- the realising set of motions
  set S : Set (EuclideanIsom 3) := Set.range (idxFun M P τ horth) with hSdef
  have hSmem : ∀ g : EuclideanIsom 3, g ∈ S ↔ ∃ i : IMat × (Fin 3 → ℤ),
      idxFun M P τ horth i = g := fun g => Set.mem_range
  have honeS : (1 : EuclideanIsom 3) ∈ S := by
    refine ⟨(1, -n₀), ?_⟩
    refine AffineIsometryEquiv.ext fun x => ?_
    rw [idxFun_apply M P τ horth hP1, oConj_one M hMr]
    have hτ1 : τ 1 + intVec (-n₀) = 0 := by
      rw [hn₀, ← intVec_add_rz]
      simp
    rw [hτ1, Matrix.one_mulVec, Matrix.mulVec_zero, WithLp.toLp_zero, add_zero,
      WithLp.toLp_ofLp, AffineIsometryEquiv.coe_one]
    rfl
  have hmulS : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := by
    rintro a ⟨⟨A, n⟩, rfl⟩ b ⟨⟨C, m⟩, rfl⟩
    by_cases hA : A ∈ P
    · by_cases hC : C ∈ P
      · exact ⟨(A * C, A.mulVec m + n - cocycleVec hτ A hA C hC),
          by rw [idxFun_eq_gOf M P τ horth hA, idxFun_eq_gOf M P τ horth hC,
            idxFun_eq_gOf M P τ horth (hPmul A hA C hC),
            gOf_mul M hMdet0 (cocycleVec_spec hτ hA hC) n m
              (horth (A * C) (hPmul A hA C hC)) (horth A hA) (horth C hC)]⟩
      · exact ⟨(A, n), by rw [idxFun_of_notMem M P τ horth hC m, mul_one]⟩
    · exact ⟨(C, m), by rw [idxFun_of_notMem M P τ horth hA n, one_mul]⟩
  have hinvS : ∀ a ∈ S, a⁻¹ ∈ S := by
    rintro a ⟨⟨A, n⟩, rfl⟩
    by_cases hA : A ∈ P
    · set B : IMat := A⁻¹ with hBdef
      have hBmem : B ∈ P := by
        rw [hBdef]; exact inv_mem_of_isIntPointGroup hP hA
      have hBA : B * A = 1 := by rw [hBdef]; exact Matrix.nonsing_inv_mul A (hPunit A hA)
      set k : Fin 3 → ℤ := cocycleVec hτ B hBmem A hA with hkdef
      have hk : τ (B * A) = τ B + Matrix.mulVec (realMat B) (τ A) + intVec k :=
        cocycleVec_spec hτ hBmem hA
      set n' : Fin 3 → ℤ := -(B.mulVec n) - (n₀ - k) with hn'def
      have hmul1 : idxFun M P τ horth (B, n') * idxFun M P τ horth (A, n) = 1 := by
        rw [idxFun_eq_gOf M P τ horth hBmem, idxFun_eq_gOf M P τ horth hA,
          gOf_mul M hMdet0 hk n' n (horth (B * A) (hPmul B hBmem A hA)) (horth B hBmem)
            (horth A hA)]
        have hidx : B.mulVec n + n' - k = -n₀ := by
          rw [hn'def]; abel
        rw [hidx]
        refine AffineIsometryEquiv.ext fun x => ?_
        rw [gOf_apply, hBA]
        have hτ1 : τ 1 + intVec (-n₀) = 0 := by
          rw [hn₀, ← intVec_add_rz]; simp
        rw [hτ1, oConj_one M hMr, Matrix.one_mulVec, Matrix.mulVec_zero, WithLp.toLp_zero,
          add_zero, WithLp.toLp_ofLp, AffineIsometryEquiv.coe_one]
        rfl
      exact ⟨(B, n'), (inv_eq_of_mul_eq_one_left hmul1).symm⟩
    · refine ⟨(A, n), ?_⟩
      rw [idxFun_of_notMem M P τ horth hA n, inv_one]
  let Gsub : Subgroup (EuclideanIsom 3) :=
    { carrier := S
      mul_mem' := fun ha hb => hmulS _ ha _ hb
      one_mem' := honeS
      inv_mem' := fun ha => hinvS _ ha }
  have hGmem : ∀ g : EuclideanIsom 3, g ∈ Gsub ↔ ∃ i : IMat × (Fin 3 → ℤ),
      idxFun M P τ horth i = g := by
    intro g
    change g ∈ S ↔ ∃ i, idxFun M P τ horth i = g
    exact Set.mem_range
  refine ⟨⟨Gsub, ?_⟩, affInvLin M hMdet0, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x ε hε
      refine (isDiscrete_idxFun M hMdet0 P hP.1 τ horth x ε hε).subset ?_
      rintro g ⟨hg, hd⟩
      exact ⟨(hGmem g).mp hg, hd⟩
    · obtain ⟨v, hv, hg⟩ := cocompact_idxFun M hMdet0 P hP1 τ horth n₀ hn₀
      exact ⟨v, hv, fun i => by
        obtain ⟨g, hgs, htr⟩ := hg i
        exact ⟨g, (hGmem g).mpr hgs, htr⟩⟩
  · rw [affInvLin_det M hMdet0]; exact inv_pos.mpr hMdetpos
  · apply Set.Subset.antisymm
    · rintro h ⟨g, hg, rfl⟩
      obtain ⟨γ, hγG, rfl⟩ := hg
      obtain ⟨i, rfl⟩ := (hGmem γ).mp hγG
      obtain ⟨A, n⟩ := i
      by_cases hA : A ∈ P
      · refine ⟨A, hA, n, fun x => ?_⟩
        rw [idxFun_eq_gOf M P τ horth hA, add_assoc]
        exact conj_gOf_apply M hMdet0 A (horth A hA) (τ A + intVec n) x
      · refine ⟨1, hP1, -n₀, fun x => ?_⟩
        rw [idxFun_of_notMem M P τ horth hA n]
        have h1 : (1 : EuclideanIsom 3).toAffineEquiv = (1 : AffineGroup 3) := rfl
        rw [h1, mul_one, mul_inv_cancel]
        have hτ1 : τ 1 + intVec (-n₀) = 0 := by
          rw [hn₀, ← intVec_add_rz]; simp
        rw [AffineEquiv.coe_one, map_intCast_one, Matrix.one_mulVec, add_assoc, hτ1,
          add_zero, WithLp.toLp_ofLp]
        rfl
    · rintro h ⟨A, hA, n, hform⟩
      refine ⟨(idxFun M P τ horth (A, n)).toAffineEquiv,
        ⟨idxFun M P τ horth (A, n), (hGmem _).mpr ⟨(A, n), rfl⟩, rfl⟩, ?_⟩
      refine AffineEquiv.ext fun x => ?_
      rw [hform x, idxFun_eq_gOf M P τ horth hA, add_assoc]
      exact (conj_gOf_apply M hMdet0 A (horth A hA) (τ A + intVec n) x).symm

end Work.SG
