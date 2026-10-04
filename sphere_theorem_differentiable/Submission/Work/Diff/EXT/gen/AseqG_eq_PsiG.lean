import Mathlib
import Submission.Work.Diff.EXT.gen.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The recursion for the splicing argument (generic, local form)

`AseqG Φ a j = ∂ₜ^j (Φ(·,Ja))` is expressed, on a set `S` which is open in the time direction and
consists of points where `a` solves the equation, through the universal function `PsiG Φ j` applied
to the spatial `2`-jets of `a, AseqG Φ a 0, …, AseqG Φ a (j-1)`.

This is the generic/local version of `Work.Diff.EXT.Aseq_eq_Psi` of
`Submission/Work/Diff/EXT/pde_splice.lean`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
open scoped ContDiff Topology
open Filter

namespace Work.Diff.EXT.gen

open Work.Diff.EXT (sJetG tderivG AseqG SeqG PsiG JG)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The recursion.**  On a set `S` of `(t,x)` which is open in the time direction above each of
its points, and on which `a` solves `∂ₜa = Φ(·,Ja)`, the iterated time derivative
`Aseq Φ a j = ∂ₜ^j(Φ(·,Ja))` of the right hand side is the universal function `PsiG Φ j` applied to
the spatial `2`-jets of `a, AseqG Φ a 0, …, AseqG Φ a (j-1)`. -/
theorem AseqG_eq_PsiG (Φ : E × JG E F → F)
    {a : ℝ × E → F} {S V : Set (ℝ × E)} (hV : IsOpen V) (hSV : S ⊆ V)
    (hS : ∀ z ∈ S, S ∈ nhds z)
    (hPDE : ∀ z ∈ S, deriv (fun s => a (s, z.2)) z.1 = Φ (z.2, sJetG a z))
    (hseq : ∀ i : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (SeqG Φ a i) V)
    (hjet : ∀ i : ℕ, ContDiffOn ℝ (⊤ : ℕ∞) (sJetG (SeqG Φ a i)) V)
    (hpsi : ∀ j : ℕ, ContDiff ℝ (⊤ : ℕ∞) (PsiG Φ j))
    (hclair : ∀ (g : ℝ × E → F), ContDiffOn ℝ (⊤ : ℕ∞) g V →
      ∀ z ∈ V, deriv (fun s => sJetG g (s, z.2)) z.1 = sJetG (tderivG g) z)
    (j : ℕ) : ∀ z ∈ S,
      AseqG Φ a j z = PsiG Φ j (z.2, fun i : Fin (j + 1) => sJetG (SeqG Φ a i) z) := by
  induction j with
  | zero =>
    intro z hz
    simp [AseqG, PsiG, SeqG]
  | succ j ih =>
    intro z hz
    rw [show AseqG Φ a (j + 1) z = deriv (fun s => AseqG Φ a j (s, z.2)) z.1 from rfl]
    have hev : (fun s : ℝ => AseqG Φ a j (s, z.2)) =ᶠ[nhds z.1]
        (fun s : ℝ => PsiG Φ j (z.2, fun i : Fin (j + 1) => sJetG (SeqG Φ a i) (s, z.2))) := by
      filter_upwards [slice_mem_nhds_of_mem_nhds (hS z hz)] with s hs
      exact ih (s, z.2) hs
    rw [hev.deriv_eq]
    rw [deriv_psi_comp (Ψ := PsiG Φ j) (hΨ := hpsi j)
      (g := fun i : Fin (j + 1) => sJetG (SeqG Φ a i)) (z := z)
      (hg := fun i => (hjet i).contDiffAt (hV.mem_nhds (hSV hz)))]
    have hdir : (fun i : Fin (j + 1) => deriv (fun s => sJetG (SeqG Φ a i) (s, z.2)) z.1)
        = (fun i : Fin (j + 1) => sJetG (SeqG Φ a (i.val + 1)) z) := by
      funext i
      rw [hclair (SeqG Φ a i) (hseq i) z (hSV hz)]
      induction i using Fin.cases with
      | zero =>
        have hev0 : tderivG a =ᶠ[nhds z] AseqG Φ a 0 := by
          filter_upwards [hS z hz] with w hw
          exact hPDE w hw
        exact sJetG_congr hev0
      | succ k => rfl
    rw [hdir, PsiG_succ, pair_single_sum, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.val_castSucc, Fin.val_succ]

end Work.Diff.EXT.gen
