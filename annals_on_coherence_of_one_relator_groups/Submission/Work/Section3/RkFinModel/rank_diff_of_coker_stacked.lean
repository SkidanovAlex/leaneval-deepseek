import Mathlib
import Submission.Work.Section3.RkFinModel.StackDefs
import Submission.Work.ORHughesFree.Epic.fpDim_eq_of_presentation
import Submission.Work.ORHughesFree.Epic.LiDim.fpDim_prod
import Submission.Work.ORHughesFree.Epic.finitePresentation_cokerMat
import Submission.Work.ORHughesFree.DivisionRank.rk_idempotent_add_compl
import Submission.Work.ORHughesFree.StarRegular.vonNeumannRegularRing_matrix
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.Section3.rdim_sup_add_of_disjoint
import Submission.Work.Section3.rk_add_of_orthogonal_idempotent
import Submission.Work.Section3.oneByOne_le_rdim_span
import Submission.Work.Section3.rdim_span_le_oneByOne
import Submission.Work.Section3.rank_oneByOne_eq_of_span_eq
import Submission.Work.Section3.RkFinModel.rkcs_one_sub_mul_s_eq_zero
import Submission.Work.Section3.RkFinModel.rkcs_oneByOne_le_rdim_span_sub_proj
import Submission.Work.Section3.RkFinModel.rkcs_rdim_span_sub_proj_le_oneByOne
import Submission.Work.Section3.RkFinModel.rkcs_range_inf_span_sub_proj_eq_bot
import Submission.Work.Section3.RkFinModel.rkcs_range_sup_span_eq_range_sup_span_sub_proj

set_option autoImplicit false
set_option maxHeartbeats 1000000

-- The default-instance search for the (rectangular) product of matrices would otherwise pick
-- the `CStarMatrix` copy of `Matrix`.
attribute [default_instance 200] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

universe u

namespace Work.Section3.RkFinModel

open Matrix Work.ORHughesFree Work.ORHughesFree.NaturalExtension
open Work.ORHughesFree.Epic (rowMulLin)

theorem rank_diff_of_coker_stacked {S : Type u} [Ring S] [Work.ORHughesFree.VonNeumannRegularRing S]
    {a n : ℕ} (A : Matrix (Fin a) (Fin n) S) (u w : Fin n → S) {e s : S}
    (hge : ∃ c : S, e = s * c)
    (hw : ∀ i : Fin a, ∑ j, A i j * w j = 0) (huw : ∑ j, u j * w j = s)
    (hPu : (1 - e) • u ∈ LinearMap.range (Work.ORHughesFree.Epic.rowMulLin A))
    (ρ : Work.ORHughesFree.SylvesterRank S) :
    ρ.rk (a + 1) n (Work.Section3.stacked A u) - ρ.rk a n A
      = 1 - ρ.rk 1 1 (Work.ORHughesFree.oneByOne (1 - e)) := by
  classical
  obtain ⟨c, hc⟩ := hge
  -- The linear functional `θ y = ∑ j, y j * w j`, which kills the row space of `A`.
  let θ : (Fin n → S) →ₗ[S] (Fin 1 → S) :=
    { toFun := fun y => fun _ => ∑ j, y j * w j
      map_add' := by
        intro y y'
        funext i
        simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro c' y
        funext i
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [mul_assoc] }
  have hθu : θ u = fun _ => s := by
    funext i
    exact huw
  have hθrow : ∀ i : Fin a, θ (fun j => A i j) = 0 := by
    intro i
    funext k
    simpa [θ] using hw i
  have hθ0 : ∀ y ∈ LinearMap.range (rowMulLin A), θ y = 0 := by
    intro y hy
    have hy' : y ∈ Submodule.span S (Set.range (fun i : Fin a => fun j : Fin n => A i j)) := by
      rwa [range_rowMulLin_eq_span_range] at hy
    refine Submodule.span_induction (p := fun z _ => θ z = 0) ?_ ?_ ?_ ?_ hy'
    · rintro z ⟨i, rfl⟩
      exact hθrow i
    · simp
    · intro x y _ _ hx hy
      rw [map_add, hx, hy, add_zero]
    · intro b x _ hx
      rw [map_smul, hx, smul_zero]
  -- `(1 - e) * s = 0`, hence `e` is idempotent.
  have h1s : (1 - e) * s = 0 :=
    rkcs_one_sub_mul_s_eq_zero A u w hw huw hPu
  have hes : e * s = s := by
    have h := h1s
    rw [sub_mul, one_mul] at h
    exact (sub_eq_zero.mp h).symm
  have hscs : s * c * s = s := by rw [← hc, hes]
  have hee : e * e = e := by
    have h1 : (s * c) * (s * c) = ((s * c) * s) * c := (mul_assoc (s * c) s c).symm
    have h2 : ((s * c) * s) * c = s * c := by rw [hscs]
    calc e * e = (s * c) * (s * c) := by rw [hc]
      _ = ((s * c) * s) * c := h1
      _ = s * c := h2
      _ = e := hc.symm
  -- The idempotent projection `E` onto the row space of `A`.
  obtain ⟨E, hE, hErange0⟩ :=
    Work.ORHughesFree.StarRegular.exists_idempotent_range_span_aux
      (fun i : Fin a => fun j : Fin n => A i j)
  have hErange : LinearMap.range E = LinearMap.range (rowMulLin A) := by
    rw [hErange0, range_rowMulLin_eq_span_range]
  have hEfix : ∀ x ∈ LinearMap.range E, E x = x := by
    intro x hx
    obtain ⟨y, hy⟩ := hx
    calc E x = E (E y) := by rw [hy]
      _ = (E * E) y := by rw [Module.End.mul_apply]
      _ = E y := by rw [hE]
      _ = x := hy
  -- The component `u' = u - E u` of `u` orthogonal to the row space of `A`.
  set u' : Fin n → S := u - E u with hu'
  have hpe : (1 - e) • u ∈ LinearMap.range E := by rw [hErange]; exact hPu
  have hθ0E : ∀ y ∈ LinearMap.range E, θ y = 0 := by
    intro y hy
    exact hθ0 y (by rw [← hErange]; exact hy)
  have hEsub : E u' = 0 := by
    have hfix : E (E u) = E u := hEfix (E u) (LinearMap.mem_range_self E u)
    rw [hu', map_sub, hfix, sub_self]
  -- The rank of the span of `u'` is the rank of `oneByOne e`.
  have hrdim : rdim ρ (Submodule.span S ({u'} : Set (Fin n → S)))
      = ρ.rk 1 1 (oneByOne e) := by
    refine le_antisymm ?_ ?_
    · exact rkcs_rdim_span_sub_proj_le_oneByOne ρ E hE u hee hpe
    · exact rkcs_oneByOne_le_rdim_span_sub_proj ρ E u θ hθ0E hθu ⟨c, hc⟩
  -- `range E` and `span {u'}` are complementary.
  have hdisj : LinearMap.range E ⊓ Submodule.span S ({u'} : Set (Fin n → S)) = ⊥ :=
    rkcs_range_inf_span_sub_proj_eq_bot E hE u
  have hsup : LinearMap.range E ⊔ Submodule.span S ({u} : Set (Fin n → S))
      = LinearMap.range E ⊔ Submodule.span S ({u'} : Set (Fin n → S)) :=
    rkcs_range_sup_span_eq_range_sup_span_sub_proj E u
  have hFG : (LinearMap.range E ⊔ Submodule.span S ({u'} : Set (Fin n → S))).FG := by
    have h1 : (LinearMap.range (rowMulLin A)).FG := by
      rw [range_rowMulLin_eq_span_range]
      exact Submodule.fg_span (Set.finite_range _)
    have h2 : (Submodule.span S ({u'} : Set (Fin n → S))).FG :=
      Submodule.fg_span (Set.finite_singleton u')
    rw [hErange]
    exact h1.sup h2
  have hadd := rdim_sup_add_of_disjoint ρ hFG hdisj
  -- Ranks of `A` and of `stacked A u`.
  have hrankA : ρ.rk a n A = rdim ρ (LinearMap.range (rowMulLin A)) := by
    rw [← rdim_eq_rk_rows ρ A, range_rowMulLin_eq_span_range]
  have hspanS : Submodule.span S (Set.range (fun i : Fin (a + 1) => fun j : Fin n =>
      stacked A u i j)) = LinearMap.range (rowMulLin (stacked A u)) :=
    (range_rowMulLin_eq_span_range (stacked A u)).symm
  have hrankSt : ρ.rk (a + 1) n (stacked A u)
      = rdim ρ (LinearMap.range E ⊔ Submodule.span S ({u} : Set (Fin n → S))) := by
    rw [← rdim_eq_rk_rows ρ (stacked A u), hspanS, range_rowMulLin_stacked, ← hErange]
  have hkey : ρ.rk (a + 1) n (stacked A u) - ρ.rk a n A = ρ.rk 1 1 (oneByOne e) := by
    rw [hrankSt, hrankA, hsup, hadd, hErange, hrdim]
    ring
  -- `ρ e + ρ (1 - e) = 1`.
  have hcompl : 1 - ρ.rk 1 1 (oneByOne (1 - e)) = ρ.rk 1 1 (oneByOne e) := by
    have hp : oneByOne e * oneByOne e = oneByOne e := by
      rw [← oneByOne_mul, hee]
    have h := Work.ORHughesFree.DivisionRank.rk_idempotent_add_compl ρ (oneByOne e) hp
    have h1 : (1 : Matrix (Fin 1) (Fin 1) S) - oneByOne e = oneByOne (1 - e) := by
      ext i j
      fin_cases i; fin_cases j
      simp [oneByOne]
    rw [h1] at h
    push_cast at h
    linarith
  linarith [hkey, hcompl]

end Work.Section3.RkFinModel
