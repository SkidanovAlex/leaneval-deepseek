import Mathlib
import Submission.Work.Section3.RkFinModel.Defs
import Submission.Work.Section3.RkFinModel.StackDefs
import Submission.Work.Section3.RkFinModel.smul_eq_zero_of_tmulM_eq_zero
import Submission.Work.Section3.RkFinModel.phi_mkQ_eq_sum
import Submission.Work.Section3.RkFinModel.exists_addHom_cokerMat_map
import Submission.Work.Section3.RkFinModel.rank_diff_of_coker_stacked
import Submission.Work.ORHughesFree.Epic.DimTheory
import Submission.Work.ORHughesFree.Epic.LiDim.RowSpaceToolkit
import Submission.Work.ORHughesFree.DivisionRank.rk_idempotent_add_compl
import Submission.Work.ORHughesFree.NaturalExtension.naturalExtension_unique

universe u

namespace Work.Section3

open Matrix Work.ORHughesFree
open Work.ORHughesFree.Epic (rowMulLin cokerMat)
open Work.ORHughesFree.Epic.LiDim (matOf rowMulLin_matOf rowMulLin_single)

/-- If `e * s = s` and `e = s * c` for some `c`, then the `1 × 1` matrix of `s` and that of `e`
have the same rank for every Sylvester rank function.  Both inequalities are instances of
`rk (A * B) ≤ rk A`: `oneByOne s = oneByOne e * oneByOne s` and
`oneByOne e = oneByOne s * oneByOne c`. -/
theorem rk_oneByOne_eq_of_mul_eq {S : Type u} [Ring S] {e s : S} (hes : e * s = s)
    (hge : ∃ c : S, e = s * c) (ρ : SylvesterRank S) :
    ρ.rk 1 1 (oneByOne s) = ρ.rk 1 1 (oneByOne e) := by
  obtain ⟨c, hc⟩ := hge
  refine le_antisymm ?_ ?_
  · have h1 : (oneByOne s : Matrix (Fin 1) (Fin 1) S) = oneByOne e * oneByOne s := by
      rw [NaturalExtension.oneByOne_mul, hes]
    rw [h1]
    exact ρ.rk_mul_le_left _ _
  · have h2 : (oneByOne e : Matrix (Fin 1) (Fin 1) S) = oneByOne s * oneByOne c := by
      rw [NaturalExtension.oneByOne_mul, hc]
    rw [h2]
    exact ρ.rk_mul_le_left _ _

/-- For an idempotent `e`, the rank of `e` is `1` minus the rank of `1 - e`; this is the case
`n = 1` of `Work.ORHughesFree.DivisionRank.rk_idempotent_add_compl`. -/
theorem one_sub_rk_oneByOne_one_sub {S : Type u} [Ring S] {e : S} (he : e * e = e)
    (ρ : SylvesterRank S) :
    ρ.rk 1 1 (oneByOne e) = 1 - ρ.rk 1 1 (oneByOne (1 - e)) := by
  have h : (oneByOne e : Matrix (Fin 1) (Fin 1) S) * oneByOne e = oneByOne e := by
    rw [NaturalExtension.oneByOne_mul, he]
  have h2 : (1 : Matrix (Fin 1) (Fin 1) S) - oneByOne e = oneByOne (1 - e) := by
    ext i j
    fin_cases i; fin_cases j
    simp [oneByOne, Matrix.sub_apply]
  have hrk := Work.ORHughesFree.DivisionRank.rk_idempotent_add_compl ρ (oneByOne e) h
  rw [h2] at hrk
  norm_num at hrk
  linarith

theorem rank_diff_of_fp_model_elementwise {R S : Type u} [Ring R] [Ring S]
    [Work.ORHughesFree.VonNeumannRegularRing S]
    (f : R →+* S) {s e : S} (he : e * e = e) (hes : e * s = s) (hge : ∃ c : S, e = s * c)
    {L : Type u} [AddCommGroup L] [Module R L] [Module.FinitePresentation R L]
    (φ : L →+ S) (hφ : ∀ (a : R) (l : L), φ (a • l) = f a * φ l) (r : L) (hr : φ r = s)
    (hz : Work.Section3.RkFinModel.BalancedTensorMod.tmulM f (1 - e) r = 0) :
    ∃ (m₁ m₂ n : ℕ) (A₁ : Matrix (Fin m₁) (Fin n) R) (A₂ : Matrix (Fin m₂) (Fin n) R),
      ∀ (ρ : Work.ORHughesFree.SylvesterRank S),
        ρ.rk 1 1 (Work.ORHughesFree.oneByOne s)
          = ρ.rk m₂ n (A₂.map f) - ρ.rk m₁ n (A₁.map f) := by
  classical
  -- a finite presentation of `L`, encoded by a matrix `M`
  obtain ⟨n, a, fL, g, hfL, hex⟩ := Module.FinitePresentation.exists_fin' R L
  have hker : LinearMap.range g = LinearMap.ker fL := (LinearMap.exact_iff.mp hex).symm
  set M : Matrix (Fin a) (Fin n) R := matOf g with hM
  have hMrow : rowMulLin M = g := rowMulLin_matOf g
  have hMker : LinearMap.range (rowMulLin M) = LinearMap.ker fL := by rw [hMrow, hker]
  set eL : cokerMat M ≃ₗ[R] L :=
    (Submodule.quotEquivOfEq _ _ hMker).trans (fL.quotKerEquivOfSurjective hfL) with heL
  obtain ⟨v, hv⟩ := hfL r
  have hv' : eL (Submodule.mkQ (LinearMap.range (rowMulLin M)) v) = r := by
    rw [heL]
    simp only [LinearEquiv.trans_apply, Submodule.mkQ_apply, Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivOfSurjective_apply_mk, hv]
  -- the row `u = f ∘ v` and the functional `w`
  let u : Fin n → S := fun j => f (v j)
  let w : Fin n → S := fun j => φ (eL (Submodule.mkQ (LinearMap.range (rowMulLin M))
    (Pi.single j 1)))
  have hphi : ∀ x : Fin n → R,
      φ (eL (Submodule.mkQ (LinearMap.range (rowMulLin M)) x)) = ∑ j, f (x j) * w j := by
    intro x
    have h := RkFinModel.phi_mkQ_eq_sum f M eL φ hφ x
    simpa only [w] using h
  -- `w` annihilates the rows of `M.map f`
  have hwann : ∀ i : Fin a, ∑ j, (M.map f) i j * w j = 0 := by
    intro i
    have hMi : M i ∈ LinearMap.range (rowMulLin M) :=
      ⟨Pi.single i 1, rowMulLin_single M i⟩
    have h0 : Submodule.mkQ (LinearMap.range (rowMulLin M)) (M i) = 0 := by
      rw [← LinearMap.mem_ker, Submodule.ker_mkQ]
      exact hMi
    have h := hphi (M i)
    rw [h0, map_zero, map_zero] at h
    simpa only [Matrix.map_apply] using h.symm
  -- and `w` detects `s` on `u`
  have huw : ∑ j, u j * w j = s := by
    have h := hphi v
    rw [hv', hr] at h
    simpa only [u] using h.symm
  -- the vanishing `(1 - e) • u ∈ rowspace (M.map f)`
  obtain ⟨ψ, hψ, hψv⟩ := RkFinModel.exists_addHom_cokerMat_map (R := R) (S := S) f M eL
  have hz' : (1 - e) • ψ r = 0 :=
    RkFinModel.smul_eq_zero_of_tmulM_eq_zero (R := R) (S := S) f ψ hψ hz
  have hψr : ψ r = Submodule.mkQ (LinearMap.range (rowMulLin (M.map f))) u := by
    rw [← hv']
    simpa only [u] using hψv v
  have hPu : (1 - e) • u ∈ LinearMap.range (rowMulLin (M.map f)) := by
    have h : Submodule.mkQ (LinearMap.range (rowMulLin (M.map f))) ((1 - e) • u) = 0 := by
      rw [map_smul, ← hψr, hz']
    rw [← LinearMap.mem_ker, Submodule.ker_mkQ] at h
    exact h
  -- the rank computation
  refine ⟨a, a + 1, n, M, stacked M v, fun ρ => ?_⟩
  have hD := RkFinModel.rank_diff_of_coker_stacked (S := S) (A := M.map f) (u := u) (w := w)
    hge hwann huw hPu ρ
  have hmap : stacked (M.map f) u = (stacked M v).map f := by
    rw [show u = (fun j => f (v j)) from rfl, stacked_map]
  have hD' : ρ.rk (a + 1) n ((stacked M v).map f) - ρ.rk a n (M.map f)
      = 1 - ρ.rk 1 1 (oneByOne (1 - e)) := by
    rw [← hmap]; exact hD
  have hse : ρ.rk 1 1 (oneByOne s) = ρ.rk 1 1 (oneByOne e) :=
    rk_oneByOne_eq_of_mul_eq hes hge ρ
  have hec : ρ.rk 1 1 (oneByOne e) = 1 - ρ.rk 1 1 (oneByOne (1 - e)) :=
    one_sub_rk_oneByOne_one_sub he ρ
  linarith

end Work.Section3
