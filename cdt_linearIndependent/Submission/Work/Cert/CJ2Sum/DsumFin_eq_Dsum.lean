import Mathlib
import Submission.Work.Cert.CJ2.Gen

namespace Work.Cert.CJ2Sum

open Work.Cert.CJ2

/-- Reading a `cons` list at a successor index. -/
private lemma get_cons_succ' (x : ℤ × ℤ) (t : List (ℤ × ℤ)) (i : Fin t.length) :
    (x :: t).get i.succ = t.get i := by simp

/-- A list sum rewritten as a sum over `Fin l.length`. -/
private lemma sum_map_get (t : List (ℤ × ℤ)) (g : ℤ × ℤ → ℤ) :
    (t.map g).sum = ∑ j : Fin t.length, g (t.get j) := by
  conv_lhs => rw [← List.ofFn_get t]
  rw [List.map_ofFn, List.sum_ofFn]
  simp [Function.comp]

/-- The `cons` recursion of `DsumFin`, matching `Dsum_cons`. -/
private lemma DsumFin_cons (x : ℤ × ℤ) (t : List (ℤ × ℤ)) :
    DsumFin (x :: t)
      = x.2 * x.2 * x.1 + 2 * x.2 * ((t.map (fun y => y.2 * max x.1 y.1)).sum) + DsumFin t := by
  conv_lhs => simp only [DsumFin]
  simp only [List.length_cons, Fin.sum_univ_succ, List.get_cons_zero, get_cons_succ']
  rw [Finset.sum_add_distrib]
  have hA : (∑ x_1 : Fin t.length, x.2 * (t.get x_1).2 * max x.1 (t.get x_1).1)
      = x.2 * (∑ x_1 : Fin t.length, (t.get x_1).2 * max x.1 (t.get x_1).1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hB : (∑ x_1 : Fin t.length, (t.get x_1).2 * x.2 * max (t.get x_1).1 x.1)
      = (∑ x_1 : Fin t.length, x.2 * (t.get x_1).2 * max x.1 (t.get x_1).1) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [max_comm (t.get i).1 x.1]
    ring
  rw [hB, hA]
  rw [sum_map_get]
  rw [max_self]
  rw [show DsumFin t
        = (∑ x : Fin t.length, ∑ x_1 : Fin t.length,
              (t.get x).2 * (t.get x_1).2 * max (t.get x).1 (t.get x_1).1) from rfl]
  ring

theorem DsumFin_eq_Dsum (l : List (ℤ × ℤ)) :
    Work.Cert.CJ2.DsumFin l = Work.Cert.CJ2.Dsum l := by
  induction l with
  | nil => simp [DsumFin]
  | cons x t ih => rw [DsumFin_cons, Dsum_cons, ih]

end Work.Cert.CJ2Sum
