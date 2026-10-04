import Mathlib
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.Evol.Calc
import Submission.Work.Diff.Evol.Deps
import Submission.Work.Diff.GE.dRmPhi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Evol

open Finset Submission.Diff

set_option maxHeartbeats 1600000

/-- **`Qhat` as the sum of the curvature-action terms.**  For a `g`-orthonormal frame `e` at `x`,

`Qhat (rmFrame g x e) i j k l = ∑_m [ rmP g x (rmVec (lcOf g) x (e m) (e i) (e j)) (e m) (e k) (e l)
   + rmP g x (e j) (rmVec (lcOf g) x (e m) (e i) (e m)) (e k) (e l)
   + rmP g x (e j) (e m) (rmVec (lcOf g) x (e m) (e i) (e k)) (e l)
   + rmP g x (e j) (e m) (e k) (rmVec (lcOf g) x (e m) (e i) (e l)) ]
 + ∑_m [ the same four terms with `i` and `j` interchanged in the first slot pair ].`

`Qhat` is the explicit 8-term array of `Submission/Work/Diff/Evol/Calc.lean`; `rmP g x a b c d = ⟪R(a,b)d, c⟫`
and `rmFrame g x e i j k l = rmP g x (e i) (e j) (e k) (e l)`.  Both reviewers verified the statement
index-by-index against the definitions.  The proof is finite index algebra: expand
`rmVec (lcOf g) x u v w = ∑_a rmP g x u v w (e a) • e a` using `Work.Diff.GE.sum_smul_inner_eq_self`
(in an orthonormal frame `⟪R(u,v)w, e_a⟫ = rmP g x u v w (e a)`), use multilinearity of `rmP` in each
slot (`rmP_sum_fst`, `rmP_sum_snd` in `Submission/Work/Diff/GE/dRmPhi.lean`, and for slots 3, 4 the pair
symmetry of `rmP` together with those), the frame relations `g.inner x (e m) (e p) = if m = p then 1 else 0`
from `he`, and normalise both sides with `Finset.sum_congr`, `Finset.sum_comm`, `Finset.mul_sum`,
`mul_ite`, `ring`.  Do NOT simplify the terms containing `rmVec (lcOf g) x (e m) (e i) (e m)`: that vector
is NOT zero in general (it is `R(e_m,e_i)e_m`). -/
theorem Qhat_curvAction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (((⊤ : ℕ∞) : WithTop ℕ∞)) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x) (he : Submission.Diff.IsONFrame g x e)
    (i j k l : Fin (Module.finrank ℝ E)) :
    Work.Diff.Evol.Qhat (Submission.Diff.rmFrame g x e) i j k l
      = (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
          (fun m => Submission.Diff.rmP g x
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e i) (e j)) (e m) (e k) (e l)
            + Submission.Diff.rmP g x (e j)
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e i) (e m)) (e k) (e l)
            + Submission.Diff.rmP g x (e j) (e m)
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e i) (e k)) (e l)
            + Submission.Diff.rmP g x (e j) (e m) (e k)
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e i) (e l)))
        + (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sum
          (fun m => Submission.Diff.rmP g x
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e j) (e m)) (e i) (e k) (e l)
            + Submission.Diff.rmP g x (e m)
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e j) (e i)) (e k) (e l)
            + Submission.Diff.rmP g x (e m) (e i)
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e j) (e k)) (e l)
            + Submission.Diff.rmP g x (e m) (e i) (e k)
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e j) (e l))) := by
  classical
  -- the frame is nonempty (the index `i` inhabits it), so the expansion lemma applies
  have hn : 0 < Module.finrank ℝ E := by have := i.isLt; omega
  -- `∑_a ⟪v, e_a⟫ · R(e_a, ·, ·, ·)` assembled back into `R(v, ·, ·, ·)`, one slot at a time
  have slot1 : ∀ (v b c d : TangentSpace I x),
      ∑ a, g.inner x v (e a) * Submission.Diff.rmP g x (e a) b c d = Submission.Diff.rmP g x v b c d := by
    intro v b c d
    rw [← Work.Diff.GE.rmP_sum_fst hLC g x Finset.univ (fun a => g.inner x v (e a)) (fun a => e a) b c d,
        Work.Diff.GE.sum_smul_inner_eq_self g x hn e he v]
  have slot2 : ∀ (b v c d : TangentSpace I x),
      ∑ a, g.inner x v (e a) * Submission.Diff.rmP g x b (e a) c d = Submission.Diff.rmP g x b v c d := by
    intro b v c d
    rw [← Work.Diff.GE.rmP_sum_snd hLC g x Finset.univ (fun a => g.inner x v (e a)) (fun a => e a) b c d,
        Work.Diff.GE.sum_smul_inner_eq_self g x hn e he v]
  have slot3 : ∀ (b c v d : TangentSpace I x),
      ∑ a, g.inner x v (e a) * Submission.Diff.rmP g x b c (e a) d = Submission.Diff.rmP g x b c v d := by
    intro b c v d
    rw [← Work.Diff.GE.rmP_sum_thd hLC g x Finset.univ (fun a => g.inner x v (e a)) (fun a => e a) b c d,
        Work.Diff.GE.sum_smul_inner_eq_self g x hn e he v]
  have slot4 : ∀ (b c d v : TangentSpace I x),
      ∑ a, g.inner x v (e a) * Submission.Diff.rmP g x b c d (e a) = Submission.Diff.rmP g x b c d v := by
    intro b c d v
    rw [← Work.Diff.GE.rmP_sum_fth hLC g x Finset.univ (fun a => g.inner x v (e a)) (fun a => e a) b c d,
        Work.Diff.GE.sum_smul_inner_eq_self g x hn e he v]
  -- unfold `Qhat` into the eight-term array and merge the two outer sums
  rw [Work.Diff.Evol.Qhat]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  -- each `rmP (rmVec …)` term is the corresponding sum over `a` of frame components
  have e1 : Submission.Diff.rmP g x
        (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e i) (e j)) (e m) (e k) (e l)
      = ∑ a, Submission.Diff.rmFrame g x e m i a j * Submission.Diff.rmFrame g x e a m k l := by
    rw [← slot1 (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e i) (e j)) (e m) (e k) (e l)]
    exact Finset.sum_congr rfl (fun a _ => rfl)
  have e2 : Submission.Diff.rmP g x (e j)
        (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e i) (e m)) (e k) (e l)
      = ∑ a, Submission.Diff.rmFrame g x e m i a m * Submission.Diff.rmFrame g x e j a k l := by
    rw [← slot2 (e j) (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e i) (e m)) (e k) (e l)]
    exact Finset.sum_congr rfl (fun a _ => rfl)
  have e3 : Submission.Diff.rmP g x (e j) (e m)
        (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e i) (e k)) (e l)
      = ∑ a, Submission.Diff.rmFrame g x e m i a k * Submission.Diff.rmFrame g x e j m a l := by
    rw [← slot3 (e j) (e m) (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e i) (e k)) (e l)]
    exact Finset.sum_congr rfl (fun a _ => rfl)
  have e4 : Submission.Diff.rmP g x (e j) (e m) (e k)
        (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e i) (e l))
      = ∑ a, Submission.Diff.rmFrame g x e m i a l * Submission.Diff.rmFrame g x e j m k a := by
    rw [← slot4 (e j) (e m) (e k) (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e i) (e l))]
    exact Finset.sum_congr rfl (fun a _ => rfl)
  have e5 : Submission.Diff.rmP g x
        (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e j) (e m)) (e i) (e k) (e l)
      = ∑ a, Submission.Diff.rmFrame g x e m j a m * Submission.Diff.rmFrame g x e a i k l := by
    rw [← slot1 (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e j) (e m)) (e i) (e k) (e l)]
    exact Finset.sum_congr rfl (fun a _ => rfl)
  have e6 : Submission.Diff.rmP g x (e m)
        (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e j) (e i)) (e k) (e l)
      = ∑ a, Submission.Diff.rmFrame g x e m j a i * Submission.Diff.rmFrame g x e m a k l := by
    rw [← slot2 (e m) (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e j) (e i)) (e k) (e l)]
    exact Finset.sum_congr rfl (fun a _ => rfl)
  have e7 : Submission.Diff.rmP g x (e m) (e i)
        (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e j) (e k)) (e l)
      = ∑ a, Submission.Diff.rmFrame g x e m j a k * Submission.Diff.rmFrame g x e m i a l := by
    rw [← slot3 (e m) (e i) (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e j) (e k)) (e l)]
    exact Finset.sum_congr rfl (fun a _ => rfl)
  have e8 : Submission.Diff.rmP g x (e m) (e i) (e k)
        (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e j) (e l))
      = ∑ a, Submission.Diff.rmFrame g x e m j a l * Submission.Diff.rmFrame g x e m i k a := by
    rw [← slot4 (e m) (e i) (e k) (Submission.Diff.rmVec (Submission.Diff.lcOf g) x (e m) (e j) (e l))]
    exact Finset.sum_congr rfl (fun a _ => rfl)
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  -- distribute the finite sums and compare the two eight-term arrays termwise
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

end Work.Diff.Evol
