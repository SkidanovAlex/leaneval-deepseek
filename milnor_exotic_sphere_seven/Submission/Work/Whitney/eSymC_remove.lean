import Mathlib
import Submission.Work.Whitney.cruxDefs
import Submission.Work.Gen.eSymClass
import Submission.Work.Gen.crx.Core
import Submission.Work.Whitney.convSeries_unit_right
import Submission.Work.Whitney.convSeries_twoTerm_geo
import Submission.Work.Whitney.convSeries_comm

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# Removing one variable from the elementary symmetric class

`Work.Gen.eSymC n t k` is the `k`-th elementary symmetric class of a family `t : Fin n → H²(P;ℤ)`,
i.e. the `k`-th coefficient of `∏_i (1 + t_i u)`.  This module proves the *removal* identity: the
convolution of the elementary symmetric series of a family of `N` degree-`2` classes with the
(truncated) geometric series of `-t k` deletes the `k`-th entry:

  `convSeries (fun m => eSymC N t m) (zPow ((-1) • t k)) (N-1) = eSymC (N-1) (t∘skipIdx) (N-1)`.

The proof is the telescoping `∏_i (1 + t_i u) · (1 + t_k u)⁻¹ = ∏_{i ≠ k} (1 + t_i u)`: the
`(1 + t_k u)`-factor is split off from `eSymC` (`Work.Gen.eSymC_eq_shiftSeries`) and cancelled
against the geometric series (`Work.Whitney.convSeries_twoTerm_geo`).  The induction on the number
of variables peels the *last* index, so the case `k = Fin.last _` is immediate and the remaining
case is reduced to the induction hypothesis via the associativity and commutativity of the
convolution.
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {P : Type} [TopologicalSpace P]

/-! ## The cancellation of the two-term series by the geometric series -/

/-- **Absorbing the `(1 + a t)`-factor**: `F ⌣ ((1 + a t)·(1 + a t)⁻¹) = F`. -/
theorem convSeries_twoTerm_geo_unit_right (F : (i : ℕ) → Coh ℤ (2 * i) P) (a : Coh ℤ 2 P)
    (m : ℕ) :
    Work.LerayHirsch.convSeries F
        (Work.LerayHirsch.convSeries (ChernRel.twoTermSeries a) (ChernRel.geoSeriesOf a)) m
      = F m :=
  convSeries_unit_right F _
    (convSeries_twoTerm_geo_zero a)
    (fun j hj => by
      obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
      exact convSeries_twoTerm_geo_succ a m) m

/-! ## The shift series is the convolution with `1 + a t` -/

/-- **The shift of a series is its convolution with the two-term series `1 + a t`**. -/
theorem shiftSeries_eq_convSeries_twoTerm_aux (F : (i : ℕ) → Coh ℤ (2 * i) P)
    (a : Coh ℤ 2 P) (m : ℕ) :
    Gen.shiftSeries F a m
      = Work.LerayHirsch.convSeries F (ChernRel.twoTermSeries a) m := by
  induction m with
  | zero =>
      rw [Gen.shiftSeries_zero,
        Gen.convSeries_zero F (ChernRel.twoTermSeries a) (ChernRel.twoTermSeries_zero a)]
  | succ m ih =>
      rw [Gen.shiftSeries_succ, Work.LerayHirsch.convSeries, Finset.sum_range_succ,
        Finset.sum_range_succ]
      have hzero : (∑ i ∈ Finset.range m,
          Work.LerayHirsch.convTerm F (ChernRel.twoTermSeries a) (m + 1) i) = 0 := by
        refine Finset.sum_eq_zero fun i hi => ?_
        have hi1 : i < m := Finset.mem_range.mp hi
        have h2 : 2 ≤ m + 1 - i := by omega
        rw [Work.LerayHirsch.convTerm_pos (by omega : i ≤ m + 1),
          ChernRel.twoTermSeries_of_two_le a h2, Work.Cohomology.cupH'_zero_right]
        exact ChernRel.cohTransport_zero _
      have htop : Work.LerayHirsch.convTerm F (ChernRel.twoTermSeries a) (m + 1) (m + 1)
          = F (m + 1) := by
        have hsub : m + 1 - (m + 1) = 0 := Nat.sub_self _
        have hS : ChernRel.twoTermSeries a (m + 1 - (m + 1))
            = cohTransport (congrArg (fun t : ℕ => 2 * t) hsub).symm
                (ChernRel.twoTermSeries a 0) :=
          ChernRel.series_cast_symm (ChernRel.twoTermSeries a) hsub
        rw [Work.LerayHirsch.convTerm_pos (le_refl (m + 1)), hS, ChernRel.twoTermSeries_zero,
          Work.LerayHirsch.cupH'_cast_right, Work.Cohomology.cupH'_one_right]
        simp only [Work.Whitney.cohTransport_trans]
        exact (Work.LerayHirsch.cohTransport_congr_proof _ rfl).trans
          (Work.Thom.cohTransport_rfl _)
      have hmid : Work.LerayHirsch.convTerm F (ChernRel.twoTermSeries a) (m + 1) m
          = cohTransport (by omega : 2 * (1 + m) = 2 * (m + 1))
              (Work.Whitney.cupChern 1 m a (F m)) := by
        have hm : m ≤ m + 1 := by omega
        have hsub : m + 1 - m = 1 := by omega
        have hS : ChernRel.twoTermSeries a (m + 1 - m)
            = cohTransport (congrArg (fun t : ℕ => 2 * t) hsub).symm
                (ChernRel.twoTermSeries a 1) :=
          ChernRel.series_cast_symm (ChernRel.twoTermSeries a) hsub
        rw [ChernRel.convTerm_eq_cupChern (x := F) (y := ChernRel.twoTermSeries a)
            (k := m + 1) (i := m) hm,
          hS, ChernRel.twoTermSeries_one, Gen.cupChern_cast_right,
          ChernRel.cupChern_comm m 1 (F m) a]
        simp only [Work.Whitney.cohTransport_trans]
      rw [hzero, zero_add, htop, hmid]
      exact add_comm _ _

/-! ## The pinned `snoc` of a family -/

/-- The family `F` with the class `a` appended: a version of `Fin.snoc` with the fibre type pinned
(to avoid the higher-order unification of the dependent fibre type). -/
def snocFam {n : ℕ} (F : Fin n → Coh ℤ 2 P) (a : Coh ℤ 2 P) : Fin (n + 1) → Coh ℤ 2 P :=
  Fin.snoc F a

theorem snocFam_castSucc {n : ℕ} (F : Fin n → Coh ℤ 2 P) (a : Coh ℤ 2 P) (i : Fin n) :
    snocFam F a (Fin.castSucc i) = F i := by
  change Fin.snoc (α := fun _ => Coh ℤ 2 P) F a (Fin.castSucc i) = F i
  rw [Fin.snoc_castSucc]

theorem snocFam_last {n : ℕ} (F : Fin n → Coh ℤ 2 P) (a : Coh ℤ 2 P) :
    snocFam F a (Fin.last n) = a := by
  change Fin.snoc (α := fun _ => Coh ℤ 2 P) F a (Fin.last n) = a
  rw [Fin.snoc_last]

/-! ## Splitting off the last variable -/

/-- **The `k = Fin.last` case of the removal identity**: split off the last variable and cancel it
against the geometric series. -/
theorem eSymC_remove_last (n : ℕ) (t : Fin (n + 1) → Coh ℤ 2 P) (m : ℕ) :
    Work.LerayHirsch.convSeries (fun m => Gen.eSymC (P := P) (n + 1) t m)
        (ChernRel.geoSeriesOf (t (Fin.last n))) m
      = Gen.eSymC (P := P) n (fun i => t (Fin.castSucc i)) m := by
  rw [Gen.eSymC_eq_shiftSeries t]
  rw [show Work.LerayHirsch.convSeries
        (Gen.shiftSeries (fun m => Gen.eSymC (P := P) n (fun i => t (Fin.castSucc i)) m)
          (t (Fin.last n))) (ChernRel.geoSeriesOf (t (Fin.last n))) m
      = Work.LerayHirsch.convSeries
          (Work.LerayHirsch.convSeries
            (fun m => Gen.eSymC (P := P) n (fun i => t (Fin.castSucc i)) m)
            (ChernRel.twoTermSeries (t (Fin.last n))))
          (ChernRel.geoSeriesOf (t (Fin.last n))) m from
    congrArg (fun F => Work.LerayHirsch.convSeries F
        (ChernRel.geoSeriesOf (t (Fin.last n))) m)
      (funext fun m' => shiftSeries_eq_convSeries_twoTerm_aux _ (t (Fin.last n)) m')]
  rw [Work.LerayHirsch.convSeries_assoc, convSeries_twoTerm_geo_unit_right]

/-- **Splitting off the last variable**: `eSymC (n+1) (snocFam F a)` is the convolution of the
series `eSymC n F` with `1 + a t`. -/
theorem eSymC_snoc_eq (n : ℕ) (F : Fin n → Coh ℤ 2 P) (a : Coh ℤ 2 P) (m : ℕ) :
    Gen.eSymC (P := P) (n + 1) (snocFam F a) m
      = Work.LerayHirsch.convSeries (fun m => Gen.eSymC (P := P) n F m)
          (ChernRel.twoTermSeries a) m := by
  have h1 : (fun k => Gen.eSymC (P := P) (n + 1) (snocFam F a) k)
      = Gen.shiftSeries (fun k => Gen.eSymC (P := P) n F k) a := by
    rw [Gen.eSymC_eq_shiftSeries (snocFam F a)]
    have hfam : (fun k =>
          Gen.eSymC (P := P) n (fun i => snocFam F a (Fin.castSucc i)) k)
        = (fun k => Gen.eSymC (P := P) n F k) := by
      funext k
      exact Gen.eSymC_congr (fun i => snocFam_castSucc F a i) k
    rw [hfam, snocFam_last F a]
  rw [show Gen.eSymC (P := P) (n + 1) (snocFam F a) m
      = Gen.shiftSeries (fun k => Gen.eSymC (P := P) n F k) a m from congrFun h1 m]
  exact shiftSeries_eq_convSeries_twoTerm_aux (fun k => Gen.eSymC (P := P) n F k) a m

/-- **The family of a `castSucc`-deletion is the `snoc` of the smaller deletion**: deleting the
index `Fin.castSucc k'` from `t` leaves the family obtained by deleting `k'` from `t ∘ castSucc`,
followed by `t (Fin.last _)`. -/
theorem succAbove_castSucc_family (n : ℕ) (t : Fin (n + 2) → Coh ℤ 2 P) (k' : Fin (n + 1)) :
    (fun i : Fin (n + 1) => t ((Fin.castSucc k').succAbove i))
      = snocFam (fun i : Fin n => t (Fin.castSucc (k'.succAbove i))) (t (Fin.last (n + 1))) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | hi
  · rw [Fin.castSucc_succAbove_castSucc, snocFam_castSucc]
  · subst hi
    rw [Fin.succAbove_ne_last_last (Fin.ne_of_lt (by simp)), snocFam_last]

/-! ## The induction -/

/-- The `k = Fin.castSucc k'` case of the removal identity, reduced to the induction hypothesis. -/
theorem eSymC_remove_castSucc (n : ℕ) (t : Fin (n + 2) → Coh ℤ 2 P) (k' : Fin (n + 1))
    (m : ℕ)
    (ih : ∀ (t : Fin (n + 1) → Coh ℤ 2 P) (k : Fin (n + 1)) (m : ℕ),
      Work.LerayHirsch.convSeries (fun m => Gen.eSymC (P := P) (n + 1) t m)
          (ChernRel.geoSeriesOf (t k)) m
        = Gen.eSymC (P := P) n (fun i => t (k.succAbove i)) m) :
    Work.LerayHirsch.convSeries (fun m => Gen.eSymC (P := P) (n + 2) t m)
        (ChernRel.geoSeriesOf (t (Fin.castSucc k'))) m
      = Gen.eSymC (P := P) (n + 1) (fun i => t ((Fin.castSucc k').succAbove i)) m := by
  rw [Gen.eSymC_eq_shiftSeries t]
  rw [show Work.LerayHirsch.convSeries
        (Gen.shiftSeries (fun m => Gen.eSymC (P := P) (n + 1) (fun i => t (Fin.castSucc i)) m)
          (t (Fin.last (n + 1)))) (ChernRel.geoSeriesOf (t (Fin.castSucc k'))) m
      = Work.LerayHirsch.convSeries
          (Work.LerayHirsch.convSeries
            (fun m => Gen.eSymC (P := P) (n + 1) (fun i => t (Fin.castSucc i)) m)
            (ChernRel.twoTermSeries (t (Fin.last (n + 1)))))
          (ChernRel.geoSeriesOf (t (Fin.castSucc k'))) m from
    congrArg (fun F => Work.LerayHirsch.convSeries F
        (ChernRel.geoSeriesOf (t (Fin.castSucc k'))) m)
      (funext fun m' => shiftSeries_eq_convSeries_twoTerm_aux _ (t (Fin.last (n + 1))) m')]
  rw [Work.LerayHirsch.convSeries_assoc]
  rw [show Work.LerayHirsch.convSeries (ChernRel.twoTermSeries (t (Fin.last (n + 1))))
        (ChernRel.geoSeriesOf (t (Fin.castSucc k')))
      = Work.LerayHirsch.convSeries (ChernRel.geoSeriesOf (t (Fin.castSucc k')))
        (ChernRel.twoTermSeries (t (Fin.last (n + 1)))) from
    funext fun j => convSeries_comm _ _ j]
  rw [← Work.LerayHirsch.convSeries_assoc]
  have hih : Work.LerayHirsch.convSeries
        (fun m => Gen.eSymC (P := P) (n + 1) (fun i => t (Fin.castSucc i)) m)
        (ChernRel.geoSeriesOf (t (Fin.castSucc k')))
      = (fun m => Gen.eSymC (P := P) n (fun i => t (Fin.castSucc (k'.succAbove i))) m) := by
    funext j
    exact ih (fun i => t (Fin.castSucc i)) k' j
  rw [hih, ← eSymC_snoc_eq n (fun i => t (Fin.castSucc (k'.succAbove i)))
    (t (Fin.last (n + 1))) m]
  exact Gen.eSymC_congr
    (fun i => congrFun (succAbove_castSucc_family n t k').symm i) m

/-- **The removal identity**, for a family of `n+1` classes, by induction on `n`. -/
theorem eSymC_remove_aux (n : ℕ) (t : Fin (n + 1) → Coh ℤ 2 P) (k : Fin (n + 1)) (m : ℕ) :
    Work.LerayHirsch.convSeries (fun m => Gen.eSymC (P := P) (n + 1) t m)
        (ChernRel.geoSeriesOf (t k)) m
      = Gen.eSymC (P := P) n (fun i => t (k.succAbove i)) m := by
  induction n generalizing m with
  | zero =>
      have hk : k = Fin.last 0 := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      subst hk
      have hR : Gen.eSymC (P := P) 0 (fun i => t ((Fin.last 0).succAbove i)) m
          = Gen.eSymC (P := P) 0 (fun i => t (Fin.castSucc i)) m :=
        Gen.eSymC_congr (fun i => congrArg t (Fin.succAbove_last_apply i)) m
      rw [hR]
      exact eSymC_remove_last 0 t m
  | succ n ih =>
      rcases Fin.eq_castSucc_or_eq_last k with ⟨k', rfl⟩ | hk
      · exact eSymC_remove_castSucc n t k' m ih
      · subst hk
        have hR : Gen.eSymC (P := P) (n + 1) (fun i => t ((Fin.last (n + 1)).succAbove i)) m
            = Gen.eSymC (P := P) (n + 1) (fun i => t (Fin.castSucc i)) m :=
          Gen.eSymC_congr (fun i => congrArg t (Fin.succAbove_last_apply i)) m
        rw [hR]
        exact eSymC_remove_last (n + 1) t m

end

/-! ## The target: removing one variable -/

/-- **Removing one variable from the elementary symmetric class.**  Convolving the series of
elementary symmetric classes of the family `u : Fin N → H²(P;ℤ)` with the (truncated) geometric
series of `-u k` deletes the `k`-th variable. -/
theorem eSymC_remove {P : Type} [TopologicalSpace P] {N : ℕ} (hN : 1 ≤ N)
    (u : Fin N → Work.Thom.Coh ℤ 2 P) (k : Fin N) :
    Work.LerayHirsch.convSeries (fun m => Work.Gen.eSymC (P := P) N u m)
        (fun m => Work.Whitney.ChernRel.zPow ((-1 : ℤ) • u k) m) (N - 1)
      = Work.Gen.eSymC (P := P) (N - 1) (u ∘ Work.Whitney.skipIdx hN k) (N - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hneg : (-1 : ℤ) • (u k) = -(u k) := by
    rw [← int_smul_eq_zsmul (inferInstance : Module ℤ (Coh ℤ 2 P)) (-1) (u k)]
    exact neg_one_smul ℤ (u k)
  have hzk : ChernRel.zPow ((-1 : ℤ) • u k) = ChernRel.geoSeriesOf (u k) := by
    rw [hneg]
    exact Gen.zPow_neg (u k)
  rw [hzk]
  exact (eSymC_remove_aux n u k n).trans (Gen.eSymC_congr (fun i => rfl) n)

end Work.Whitney
