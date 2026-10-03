import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.indicator_sigmaStrataFinset_incl_excl

namespace Work.KMTAreas

open Work.BourgainPlan.IonescuWainger

/-- **The primitive point `1/Q_A` lies in Tao's stratum `Σ_A`.**

For a finite set `A` of integers `≥ 2`, the point `1/Q_A = 1/∏_{q ∈ A} q` of the circle is a point
of the *exact* denominator stratum `Σ_A = 𝕋[Q_A] \ ⋃_{B ⊊ A} 𝕋[Q_B]`: it is a `Q_A`-torsion point,
and it is not `Q_B`-torsion for any proper subset `B ⊊ A`, because `Q_A = Q_{A \ B} · Q_B` with
`Q_{A \ B} ≥ 2`, so `Q_A ∤ Q_B`.

(No coprimality of the elements of `A` is needed; `Q_A ≠ Q_B` for `B ⊊ A` already follows from all
the elements being `≥ 2`.) -/
theorem arcPt_one_mem_sigmaStrataFinset {A : Finset ℕ} (h2 : ∀ a ∈ A, 2 ≤ a) :
    Work.BourgainPlan.IonescuWainger.arcPt (Work.BourgainPlan.IonescuWainger.QA A) 1 ∈
      Work.BourgainPlan.IonescuWainger.sigmaStrataFinset A := by
  classical
  rw [mem_sigmaStrataFinset]
  refine ⟨?_, ?_⟩
  · -- `1/Q_A ∈ Σ_{⊆ A}`: list it by its residue modulo `Q_A`
    have hQne : QA A ≠ 0 := QA_ne_zero_of_two_le h2
    have hQneZ : (QA A : ℤ) ≠ 0 := by exact_mod_cast hQne
    have hQpos : (0 : ℤ) < (QA A : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hQne
    have hnonneg : 0 ≤ (1 : ℤ) % (QA A : ℤ) := Int.emod_nonneg 1 hQneZ
    refine Finset.mem_image.mpr ⟨((1 : ℤ) % (QA A : ℤ)).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]
      rw [Int.toNat_lt hnonneg]
      exact Int.emod_lt_of_pos 1 hQpos
    · exact arcPt_emod_toNat hQne 1
  · -- and it is in no strictly smaller torsion subgroup `Σ_{⊆ B}`, `B ⊊ A`
    intro B hB hmem
    obtain ⟨hBne, hBsub⟩ := Finset.mem_erase.mp hB
    rw [Finset.mem_powerset] at hBsub
    obtain ⟨a, -, hae⟩ := Finset.mem_image.mp hmem
    have hQBpos : 0 < QA B := Finset.prod_pos fun q hq => by
      have := h2 q (hBsub hq); omega
    have hQBne : QA B ≠ 0 := hQBpos.ne'
    -- `Q_B · (1/Q_A) = 0`, whence `Q_A ∣ Q_B`
    have hzero : (QA B : ℤ) • arcPt (QA A) 1 = 0 := by
      rw [← hae]
      exact zsmul_arcPt_eq_zero hQBne dvd_rfl
    have hconv : (QA B : ℤ) • arcPt (QA A) 1 = arcPt (QA A) (QA B : ℤ) := by
      rw [zsmul_arcPt, arcPt]
      congr 1
      push_cast
      ring
    have hdvdZ : (QA A : ℤ) ∣ (QA B : ℤ) :=
      (arcPt_eq_zero_iff_dvd (QA_ne_zero_of_two_le h2) (QA B : ℤ)).mp (hconv ▸ hzero)
    have hle : QA A ≤ QA B :=
      Nat.le_of_dvd hQBpos (Int.natCast_dvd_natCast.mp hdvdZ)
    -- but `B ⊊ A` gives `Q_A = Q_{A\B} · Q_B` with `Q_{A\B} ≥ 2 > 1`, so `Q_A > Q_B`
    have hdisj : Disjoint (A \ B) B := by
      rw [Finset.disjoint_left]
      intro x hx hxB
      exact (Finset.mem_sdiff.mp hx).2 hxB
    have hsplit : QA A = QA (A \ B) * QA B := by
      have hunion : A \ B ∪ B = A := Finset.sdiff_union_of_subset hBsub
      conv_lhs => rw [← hunion]
      exact QA_union hdisj
    have hne_empty : A \ B ≠ ∅ := fun h =>
      hBne (Finset.Subset.antisymm hBsub (Finset.sdiff_eq_empty_iff_subset.mp h))
    obtain ⟨q, hqAB⟩ := Finset.nonempty_iff_ne_empty.mpr hne_empty
    have hqA : q ∈ A := (Finset.mem_sdiff.mp hqAB).1
    have hQdiffpos : 0 < QA (A \ B) := Finset.prod_pos fun x hx => by
      have := h2 x (Finset.mem_sdiff.mp hx).1; omega
    have h2le : 2 ≤ QA (A \ B) :=
      le_trans (h2 q hqA) (Nat.le_of_dvd hQdiffpos (Finset.dvd_prod_of_mem (fun x => x) hqAB))
    have hcontra : 2 * QA B ≤ QA B :=
      calc 2 * QA B ≤ QA (A \ B) * QA B := Nat.mul_le_mul_right _ h2le
        _ = QA A := hsplit.symm
        _ ≤ QA B := hle
    omega

end Work.KMTAreas
