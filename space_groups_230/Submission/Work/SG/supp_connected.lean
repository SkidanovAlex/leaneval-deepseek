import Mathlib
import Submission.Work.SG.SellingDefs
import Submission.Work.SG.disconn_subset
import Submission.Work.SG.sb_subset_sum_ne_zero

namespace Work.SG

/-! ### Bilinearity of `bf` over finite sums

These are the only extra facts about `bf` needed below; `SellingDefs` already provides
additivity in the second argument (`bf_add_right`) and symmetry (`bf_comm`). -/

private theorem bf_zero_left (Q : IMat) (v : IVec) : bf Q (0 : IVec) v = 0 := by
  simp [bf]

private theorem bf_add_left (Q : IMat) (u u' v : IVec) :
    bf Q (u + u') v = bf Q u v + bf Q u' v := by
  simp only [bf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem bf_zero_right (Q : IMat) (u : IVec) : bf Q u (0 : IVec) = 0 := by
  simp [bf]

private theorem bf_sum_left (Q : IMat) (s : Finset (Fin 4)) (u : Fin 4 → IVec) (y : IVec) :
    bf Q (∑ m ∈ s, u m) y = ∑ m ∈ s, bf Q (u m) y := by
  classical
  induction s using Finset.induction with
  | empty => simp [bf_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bf_add_left, ih]

private theorem bf_sum_right (Q : IMat) (u : IVec) (s : Finset (Fin 4)) (v : Fin 4 → IVec) :
    bf Q u (∑ m ∈ s, v m) = ∑ m ∈ s, bf Q u (v m) := by
  classical
  induction s using Finset.induction with
  | empty => simp [bf_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, bf_add_right, ih]

private theorem bf_sum_sum (Q : IMat) (s t : Finset (Fin 4)) (u v : Fin 4 → IVec) :
    bf Q (∑ m ∈ s, u m) (∑ m ∈ t, v m) = ∑ m ∈ s, ∑ n ∈ t, bf Q (u m) (v n) := by
  rw [bf_sum_left]
  exact Finset.sum_congr rfl fun m _ => bf_sum_right Q (u m) t v

/-- The support graph of a superbase of a positive definite form is connected.

Route: if `E := suppGraph Q W` were disconnected there is a nonempty proper `S : Finset (Fin 4)`
with no crossing edge; then for `i ∈ S`, `j ∉ S` one has `bf Q (sb W i) (sb W j) ≥ 0`, and
summing gives `bf Q x y ≥ 0` with `x = ∑_{i∈S} sb W i`, `y = ∑_{j∉S} sb W j`.  But `x = -y`
(`sb_sum_zero`) and `y ≠ 0` (a proper nonempty subcollection of a superbase of a unimodular matrix
is nonzero), so `bf Q x y = -qf Q y < 0` by `hpd` — contradiction.  Use `bf_comm`, `bf_linComb4`
(or a version for the sums over `S`) and `sb_sum_zero`. -/
theorem supp_connected (Q W : IMat) (hsym : Q.transpose = Q) (hW : IsUnit W.det)
    (hpd : ∀ v : IVec, v ≠ 0 → 0 < qf Q v) : IsConnGraph (suppGraph Q W) := by
  classical
  by_contra hconn
  obtain ⟨S, hSne, hSprop, hcross⟩ := disconn_subset (suppGraph Q W) hconn
  -- `S` is nonempty and proper, so its complement is too.
  have hScne : (Finset.univ \ S).Nonempty := by
    rw [Finset.sdiff_nonempty]
    intro hsub
    exact hSprop (Finset.eq_univ_of_forall fun x => hsub (Finset.mem_univ x))
  have hScprop : (Finset.univ \ S) ≠ Finset.univ := by
    intro h
    obtain ⟨i, hi⟩ := hSne
    have : i ∈ Finset.univ \ S := by rw [h]; exact Finset.mem_univ i
    exact (Finset.mem_sdiff.mp this).2 hi
  -- The two subcollection sums add up to the full superbase sum, which vanishes.
  have hxy : (∑ m ∈ S, sb W m) + (∑ m ∈ Finset.univ \ S, sb W m) = 0 := by
    have hsum : (∑ m ∈ Finset.univ \ S, sb W m) + (∑ m ∈ S, sb W m) = 0 := by
      rw [Finset.sum_sdiff (Finset.subset_univ S)]
      simpa using sb_sum_zero W
    rw [add_comm]
    exact hsum
  -- No crossing edge means every cross term is nonnegative.
  have hnonneg : ∀ i ∈ S, ∀ j ∈ Finset.univ \ S, 0 ≤ bf Q (sb W i) (sb W j) := by
    intro i hi j hj
    have hjS : j ∉ S := (Finset.mem_sdiff.mp hj).2
    obtain ⟨h1, h2⟩ := hcross i hi j hjS
    have h1' : ¬ (i < j ∧ bf Q (sb W i) (sb W j) < 0) := fun h => h1 (mem_suppGraph.mpr h)
    have h2' : ¬ (j < i ∧ bf Q (sb W j) (sb W i) < 0) := fun h => h2 (mem_suppGraph.mpr h)
    have hij : i ≠ j := fun h => hjS (h ▸ hi)
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact not_lt.mp (fun hbf => h1' ⟨hlt, hbf⟩)
    · have hji : 0 ≤ bf Q (sb W j) (sb W i) := not_lt.mp (fun hbf => h2' ⟨hlt, hbf⟩)
      rwa [bf_comm Q hsym (sb W j) (sb W i)] at hji
  have hy : (∑ m ∈ Finset.univ \ S, sb W m) ≠ 0 :=
    sb_subset_sum_ne_zero W (Finset.univ \ S) hScne hScprop hW
  have hqfpos : 0 < qf Q (∑ m ∈ Finset.univ \ S, sb W m) := hpd _ hy
  have hbf_ge : 0 ≤ bf Q (∑ m ∈ S, sb W m) (∑ m ∈ Finset.univ \ S, sb W m) := by
    rw [bf_sum_sum]
    exact Finset.sum_nonneg fun i hi => Finset.sum_nonneg fun j hj => hnonneg i hi j hj
  have hbf_lt : bf Q (∑ m ∈ S, sb W m) (∑ m ∈ Finset.univ \ S, sb W m) < 0 := by
    have hx : (∑ m ∈ S, sb W m) = -(∑ m ∈ Finset.univ \ S, sb W m) :=
      eq_neg_of_add_eq_zero_left hxy
    rw [hx, bf_neg_left]
    simpa [qf] using hqfpos
  exact absurd hbf_lt (not_lt.mpr hbf_ge)

end Work.SG
