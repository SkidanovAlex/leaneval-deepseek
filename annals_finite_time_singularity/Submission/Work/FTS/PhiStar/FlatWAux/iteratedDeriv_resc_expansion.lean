import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.PhiStar.FlatWAux.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.Expansion
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.FlatWAux.ModeRescaledSmooth
import Submission.Work.FTS.PhiStar.FlatWAux.RadGreenPhiAjFlat
import Submission.Work.FTS.VocabO

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped ContDiff

namespace Work.FTS.PhiStar.FlatWAux

/-- The rescaled function `y ↦ (y+1)/y · f y` is `C^k` at every `z > 0` at which `f` is. -/
private lemma contDiffAt_rescale_mul {f : ℝ → ℝ} {k : ℕ} {z : ℝ} (hz : 0 < z)
    (hf : ContDiffAt ℝ (k : ℕ∞ω) f z) :
    ContDiffAt ℝ (k : ℕ∞ω) (fun y : ℝ => (y + 1) / y * f y) z := by
  have hfac : ContDiffAt ℝ (k : ℕ∞ω) (fun y : ℝ => (y + 1) / y) z :=
    ((contDiffAt_id.add (contDiffAt_const (c := (1 : ℝ)))).div contDiffAt_id
      (by simpa using ne_of_gt hz))
  exact hfac.mul hf

/-- Pointwise distribution of the rescaling factor `(y+1)/y` over a finite sum plus one extra
term. -/
private lemma rescale_mul_sum_add {ι : Type*} (s : Finset ι) (c : ι → ℝ) (A : ι → ℝ → ℝ)
    (C : ℝ) (U : ℝ → ℝ) (y : ℝ) :
    (y + 1) / y * ((∑ i ∈ s, c i * A i y) + C * U y)
      = (∑ i ∈ s, c i * ((y + 1) / y * A i y)) + C * ((y + 1) / y * U y) := by
  rw [mul_add, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by ring)
  · ring

/-- The `k`-th iterated derivative of a finite sum plus one extra term, provided all the summands
are `C^k` at the point. -/
private lemma iteratedDeriv_sum_add_const_mul {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (g : ℝ → ℝ) (k : ℕ) {z : ℝ}
    (hf : ∀ i ∈ s, ContDiffAt ℝ (k : ℕ∞ω) (f i) z) (hg : ContDiffAt ℝ (k : ℕ∞ω) g z) :
    iteratedDeriv k (fun y : ℝ => (∑ i ∈ s, f i y) + g y) z
      = (∑ i ∈ s, iteratedDeriv k (f i) z) + iteratedDeriv k g z := by
  rw [iteratedDeriv_fun_add (ContDiffAt.sum hf) hg, iteratedDeriv_fun_sum hf]

theorem iteratedDeriv_resc_expansion (α : ℝ) (m : ℕ) (hm : 1 ≤ m) (k : ℕ) {z : ℝ} (hz : 0 < z)
    (hexp : ∀ z' : ℝ, 0 < z' →
      Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) z'
        = (∑ j ∈ Finset.range Work.FTS.PhiStar.FlatWAux.J,
              (α ^ j / (Work.FTS.PhiStar.Radial.lamR m) ^ (j + 1))
                * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) z')
          + (α ^ Work.FTS.PhiStar.FlatWAux.J
              / (Work.FTS.PhiStar.Radial.lamR m) ^ Work.FTS.PhiStar.FlatWAux.J)
              * Work.FTS.PhiStar.Radial.radGreen α m
                  (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                    (Work.FTS.VocabO.phiA α)) z') :
    iteratedDeriv k (fun y => (y + 1) / y
        * Work.FTS.PhiStar.Radial.radGreen α m (Work.FTS.VocabO.phiA α) y) z
      = (∑ j ∈ Finset.range Work.FTS.PhiStar.FlatWAux.J,
            (α ^ j / (Work.FTS.PhiStar.Radial.lamR m) ^ (j + 1))
              * iteratedDeriv k (fun y => (y + 1) / y
                  * Work.FTS.PhiStar.FlatWAux.Ajit α j (Work.FTS.VocabO.phiA α) y) z)
        + (α ^ Work.FTS.PhiStar.FlatWAux.J
            / (Work.FTS.PhiStar.Radial.lamR m) ^ Work.FTS.PhiStar.FlatWAux.J)
            * iteratedDeriv k (fun y => (y + 1) / y
                * Work.FTS.PhiStar.Radial.radGreen α m
                    (Work.FTS.PhiStar.FlatWAux.Ajit α Work.FTS.PhiStar.FlatWAux.J
                      (Work.FTS.VocabO.phiA α)) y) z := by
  -- `hexp` identifies the two functions on the open set `(0,∞)`, on which the `k`-th iterated
  -- derivative is therefore the same at every positive point.
  have hEqOn : Set.EqOn
      (fun y : ℝ => (y + 1) / y * Radial.radGreen α m (VocabO.phiA α) y)
      (fun y : ℝ => (y + 1) / y
        * ((∑ j ∈ Finset.range J,
              (α ^ j / (Radial.lamR m) ^ (j + 1)) * Ajit α j (VocabO.phiA α) y)
          + (α ^ J / (Radial.lamR m) ^ J)
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y)) (Set.Ioi 0) := by
    intro y hy
    simp only [hexp y hy]
  rw [hEqOn.iteratedDeriv_of_isOpen isOpen_Ioi k hz]
  -- distribute the rescaling factor `(y+1)/y` over the sum and over the extra term
  have hdist : (fun y : ℝ => (y + 1) / y
        * ((∑ j ∈ Finset.range J,
              (α ^ j / (Radial.lamR m) ^ (j + 1)) * Ajit α j (VocabO.phiA α) y)
          + (α ^ J / (Radial.lamR m) ^ J)
              * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y))
      = fun y : ℝ => (∑ j ∈ Finset.range J,
            (α ^ j / (Radial.lamR m) ^ (j + 1)) * ((y + 1) / y * Ajit α j (VocabO.phiA α) y))
          + (α ^ J / (Radial.lamR m) ^ J)
              * ((y + 1) / y * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) := by
    funext y
    exact rescale_mul_sum_add (Finset.range J)
      (fun j => α ^ j / (Radial.lamR m) ^ (j + 1)) (fun j => Ajit α j (VocabO.phiA α))
      (α ^ J / (Radial.lamR m) ^ J)
      (fun y => Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y) y
  rw [hdist]
  -- the `k`-th iterated derivative distributes over the finite sum and pulls out the constants
  rw [iteratedDeriv_sum_add_const_mul (Finset.range J)
    (fun j y => (α ^ j / (Radial.lamR m) ^ (j + 1)) * ((y + 1) / y * Ajit α j (VocabO.phiA α) y))
    (fun y => (α ^ J / (Radial.lamR m) ^ J)
      * ((y + 1) / y * Radial.radGreen α m (Ajit α J (VocabO.phiA α)) y)) k
    (fun j _ => (contDiffAt_const (c := α ^ j / (Radial.lamR m) ^ (j + 1))).mul
      (contDiffAt_rescale_mul hz
        ((contDiffOn_Ajit_phiA α j k).contDiffAt (IsOpen.mem_nhds isOpen_Ioi hz))))
    ((contDiffAt_const (c := α ^ J / (Radial.lamR m) ^ J)).mul
      (contDiffAt_rescale_mul hz
        ((contDiffOn_radGreen α m k (contDiffOn_Ajit_phiA α J k)).contDiffAt
          (IsOpen.mem_nhds isOpen_Ioi hz))))]
  simp only [iteratedDeriv_const_mul_field]

end Work.FTS.PhiStar.FlatWAux
