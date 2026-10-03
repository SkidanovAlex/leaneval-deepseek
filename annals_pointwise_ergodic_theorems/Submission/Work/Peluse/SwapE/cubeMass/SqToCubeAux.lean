import Submission.Work.Peluse.SwapE.cubeMass.Split
import Submission.Work.Peluse.SwapE.cubeMass.fiberSum
import Submission.Work.Peluse.SwapE.cubeMass.sumTdirCons
import Submission.Work.Peluse.SwapE.cubeMass.fejerId
import Submission.Work.Peluse.SwapE.cubeMass.fejerCS
import Submission.Work.Peluse.SwapE.cubeMass.massSq_le
import Submission.Work.Peluse.PET.boxNormPow_scale_transfer

/-!
# `massSq ⟹ boxNormPow`: auxiliary lemmas

Support lemmas for `SqToCube.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace Work.Peluse.SwapE

noncomputable section

open Work.Peluse

/-- The cube term `aN t f u` is supported where `f` is. -/
lemma aN_supportIn {t : ℕ} {f : ℤ → ℂ} {N : ℕ} (hf : SupportIn f N) (u : Fin t → ℤ) :
    SupportIn (aN t f u) N :=
  fun z hz =>
    aN_eq_zero_of_notMem_symIcc hf u (fun h => absurd (natAbs_le_of_mem_symIcc h) (by omega))

/-- The slot box is contained in the difference set `Tdir`. -/
lemma massBox_subset_Tdir (d H M : ℕ) :
    massBox d H M ⊆ Tdir (massBoxCard H M) d := by
  intro n hn
  rw [mem_Tdir]
  intro i
  have hn' : ∀ j : Fin d, n j ∈ Finset.Icc (-(massHalf H M)) (massHalf H M) := by
    simpa only [massBox, Fintype.mem_piFinset] using hn
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp (hn' i)
  have key : (massBoxCard H M : ℤ) - 1 = 2 * massHalf H M := by
    unfold massBoxCard massHalf; push_cast; ring
  have hnn : 0 ≤ massHalf H M := by unfold massHalf; positivity
  rw [mem_sCard]
  constructor <;> omega

/-- On the slot box the multiplicity `Wt` dominates `(Card/2)^d`. -/
lemma pow_half_card_le_Wt {d H M : ℕ} {n : Fin d → ℤ} (hn : n ∈ massBox d H M) :
    (((massBoxCard H M : ℝ)) / 2) ^ d ≤ ((Wt (massBoxCard H M) d n : ℕ) : ℝ) := by
  set l : ℕ := H * M with hl
  have hCard : massBoxCard H M = 4 * l + 1 := by rw [hl]; unfold massBoxCard; ring
  have hhalf : massHalf H M = ((2 * l : ℕ) : ℤ) := by
    rw [hl]; unfold massHalf; push_cast; ring
  have hb : ∀ i : Fin d, 2 * l + 1 ≤ Ncard (massBoxCard H M) (n i) := by
    intro i
    simp only [massBox, Fintype.mem_piFinset, Finset.mem_Icc] at hn
    obtain ⟨h1, h2⟩ := hn i
    rw [hhalf] at h1 h2
    simp only [Ncard]
    have h3 : (n i).natAbs ≤ 2 * l := by
      have h4 : |n i| ≤ ((2 * l : ℕ) : ℤ) := abs_le.mpr ⟨h1, h2⟩
      have h5 : (((n i).natAbs : ℕ) : ℤ) = |n i| := Int.natCast_natAbs _
      have h6 : (((n i).natAbs : ℕ) : ℤ) ≤ ((2 * l : ℕ) : ℤ) := by rw [h5]; exact h4
      exact_mod_cast h6
    rw [hCard]
    omega
  have hprod : (2 * l + 1) ^ d ≤ Wt (massBoxCard H M) d n := by
    have h := Finset.prod_le_prod₀ (s := Finset.univ)
      (f := fun _ : Fin d => 2 * l + 1) (g := fun i : Fin d => Ncard (massBoxCard H M) (n i))
      (fun i _ => Nat.zero_le _) (fun i _ => hb i)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
    exact h
  have hcast : (((2 * l + 1 : ℕ)) : ℝ) ^ d ≤ ((Wt (massBoxCard H M) d n : ℕ) : ℝ) := by
    exact_mod_cast hprod
  have hbase : ((massBoxCard H M : ℝ)) / 2 ≤ ((2 * l + 1 : ℕ) : ℝ) := by
    rw [hCard]; push_cast; linarith
  calc (((massBoxCard H M : ℝ)) / 2) ^ d
      ≤ ((((2 * l + 1 : ℕ)) : ℝ)) ^ d := pow_le_pow_left₀ (by positivity) hbase d
    _ ≤ ((Wt (massBoxCard H M) d n : ℕ) : ℝ) := hcast

/-- The `δ`-slot sum of the cube term:
`SN n = ∑_{δ ∈ sCard} Ncard δ · Re (Wf (d+1) f (Fin.cons δ n))`. -/
def SNb (Card d : ℕ) (f : ℤ → ℂ) (n : Fin d → ℤ) : ℝ :=
  ∑ δ ∈ sCard Card,
    ((Ncard Card δ : ℕ) : ℝ) * (Work.Peluse.Concat.Wf (d + 1)
      (fun _ : Fin (d + 1) → Bool => f) (Fin.cons δ n)).re

end

end Work.Peluse.SwapE
