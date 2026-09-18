import Mathlib
import Submission.Work.MassTransferenceAlt.Tree.Data
import Submission.Work.MassTransferenceAlt.Tree.vfChildrenGe

namespace Work.MassTransferenceAlt.Tree

open Work.MassTransferenceAlt

/-- **The basic mass estimate.**  The mass of every node is at most `1 / η` times its
`f`-volume.  This is the invariant (e:027) of Beresnevich–Velani, proved by induction on
the level using the mass conservation `vfChildrenGe` for the inductive step and
`TreeData.root_mass` for the first level. -/
lemma MassLe (d : ℝ) (hd0 : 0 < d) (hd1 : d < 1) (c ρ : ℕ → ℝ) (η : ℝ) (hη : 0 < η)
    (T : Work.MassTransferenceAlt.TreeData d c ρ η) (n : ℕ) (i : ℕ) (hi : i ∈ T.lev n) :
    Work.MassTransferenceAlt.Mass d c ρ η T n (some i)
      ≤ Work.MassTransferenceAlt.vf d ρ i / η := by
  classical
  have key : ∀ n (i : ℕ), i ∈ T.lev n → Mass d c ρ η T n (some i) ≤ vf d ρ i / η := by
    intro n
    induction n with
    | zero =>
      intro i hi
      have hS : 0 < ∑ j ∈ T.lev 0, vf d ρ j := lt_of_lt_of_le hη T.root_mass
      have hpos : 0 ≤ vf d ρ i := (vf_pos (T.good 0 i hi).1).le
      have hinv : (∑ j ∈ T.lev 0, vf d ρ j)⁻¹ ≤ η⁻¹ := (inv_le_inv₀ hS hη).mpr T.root_mass
      rw [show Mass d c ρ η T 0 (some i) = vf d ρ i / (∑ j ∈ T.lev 0, vf d ρ j) from by
        simp [Mass, hi]]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv hpos
    | succ n ih =>
      intro i hi
      obtain ⟨B, hB, hpar⟩ := T.par_mem n i hi
      rw [show Mass d c ρ η T (n+1) (some i) =
          (vf d ρ i / (∑ j ∈ (T.lev (n+1)).filter (fun j => T.par (n+1) j = T.par (n+1) i), vf d ρ j))
            * Mass d c ρ η T n (T.par (n+1) i) from by simp [Mass, hi]]
      rw [hpar]
      have hSge : vf d ρ B ≤ ∑ j ∈ (T.lev (n+1)).filter (fun j => T.par (n+1) j = some B), vf d ρ j :=
        vfChildrenGe d hd0 hd1 c ρ η T n B hB
      have hSpos : 0 < ∑ j ∈ (T.lev (n+1)).filter (fun j => T.par (n+1) j = some B), vf d ρ j :=
        lt_of_lt_of_le (vf_pos (T.good n B hB).1) hSge
      have hratio : vf d ρ B / (∑ j ∈ (T.lev (n+1)).filter (fun j => T.par (n+1) j = some B), vf d ρ j) ≤ 1 :=
        (div_le_one₀ hSpos).mpr hSge
      calc (vf d ρ i / (∑ j ∈ (T.lev (n+1)).filter (fun j => T.par (n+1) j = some B), vf d ρ j)) * Mass d c ρ η T n (some B)
          ≤ (vf d ρ i / (∑ j ∈ (T.lev (n+1)).filter (fun j => T.par (n+1) j = some B), vf d ρ j)) * (vf d ρ B / η) :=
            mul_le_mul_of_nonneg_left (ih B hB) (div_nonneg (vf_pos (T.good (n+1) i hi).1).le hSpos.le)
        _ = (vf d ρ i / η) * (vf d ρ B / (∑ j ∈ (T.lev (n+1)).filter (fun j => T.par (n+1) j = some B), vf d ρ j)) := by ring
        _ ≤ (vf d ρ i / η) * 1 := mul_le_mul_of_nonneg_left hratio (div_nonneg (vf_pos (T.good (n+1) i hi).1).le hη.le)
        _ = vf d ρ i / η := by ring
  exact key n i hi

end Work.MassTransferenceAlt.Tree
