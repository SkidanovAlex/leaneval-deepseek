/-
  Degree bound for the padded semi-Pfaffian set `padStrat p q d X`.

  `padStrat p q d X` inserts `d` coordinates (pinned to `0`) between the base and the fibre
  coordinates of `X`; its basic sets are obtained from those of `X` by pulling the atoms back
  along the injection `midInj p d q` and adjoining the `d` pinning equations.

  The pulling back is a polynomial *renaming* (`EAPoly.extend`), which does not change the atom
  degree (`Work.WilE8.Extend.atomDeg_extend`), while each pinning equation is a single variable,
  hence an atom of degree `2 = 1 + 1`.  So every basic set of `padStrat p q d X` has degree at
  most `B.deg + 2 * d`, and summing over the (equally many) basic sets gives the bound
  `X.deg + 2 * d * X.basics.length`.
-/
import Mathlib
import Submission.Work.WilE7.PadDefs
import Submission.Work.WilE8.Extend.semipf_deg_extend

open WilkiesDesign WilkiesDesign.E

namespace Work.WilE7.PadAux

/-- Sums of the shape `∑ (f a + c)` are `∑ f a` plus `c` times the length. -/
lemma sum_map_deg_add {α : Type*} (l : List α) (f : α → ℕ) (c : ℕ) :
    (l.map (fun a => f a + c)).sum = (l.map f).sum + c * l.length := by
  induction l with
  | nil => simp
  | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- A pinning equation is a variable, so its atom degree is `1 + 1 = 2`. -/
lemma atomDeg_pinAt (p q d r : ℕ) (a : Fin d) : atomDeg (pinAt p d q r a) = 2 := by
  simp [atomDeg, pinAt]

/-- The `d` pinning equations contribute exactly `2 * d` to the degree. -/
lemma pins_map_atomDeg (p q d r : ℕ) : ((pins p d q r).map atomDeg).sum = 2 * d := by
  have h : (pins p d q r).map atomDeg = (List.finRange d).map (fun _ => 2) := by
    rw [pins, List.map_map]
    exact List.map_congr_left (l := List.finRange d) (fun a _ => atomDeg_pinAt p q d r a)
  rw [h, List.map_const', List.sum_replicate, List.length_finRange, Nat.nsmul_eq_mul]
  ring

/-- The degree of the basic set of `padStrat p q d X` built from the basic set `B` of `X` is
`B.deg + 2 * d`: the pullback along `midInj` changes no atom degree and the `d` pinning
equations contribute `2` each. -/
lemma basic_deg_padStrat_basic (p q d : ℕ) (X : SemiPf (p + q)) (B : Basic (p + q) X.r) :
    (⟨B.eqs.map (Work.WilE8.EAPoly.extend (midInj p d q)) ++ pins p d q X.r,
      B.pos.map (Work.WilE8.EAPoly.extend (midInj p d q))⟩ : Basic (p + (d + q)) X.r).deg
      = B.deg + 2 * d := by
  have heq : (B.eqs.map (Work.WilE8.EAPoly.extend (midInj p d q))).map atomDeg
      = B.eqs.map atomDeg := by
    rw [List.map_map]
    exact List.map_congr_left (l := B.eqs) (fun Q _ =>
      Work.WilE8.Extend.atomDeg_extend (midInj_injective p d q) Q)
  have hpos : (B.pos.map (Work.WilE8.EAPoly.extend (midInj p d q))).map atomDeg
      = B.pos.map atomDeg := by
    rw [List.map_map]
    exact List.map_congr_left (l := B.pos) (fun Q _ =>
      Work.WilE8.Extend.atomDeg_extend (midInj_injective p d q) Q)
  simp only [Basic.deg, List.map_append, List.sum_append]
  rw [heq, hpos, pins_map_atomDeg p q d X.r]
  omega

/-- **Degree of the padded stratum.**  Padding `X : SemiPf (p + q)` with `d` coordinates pinned
to zero raises the degree by at most `2 * d` per basic set. -/
theorem padStrat_deg (p q d : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)) :
    (Work.WilE7.padStrat p q d X).deg ≤ X.deg + 2 * d * X.basics.length := by
  have heq : (X.basics.map (fun B =>
        (⟨B.eqs.map (Work.WilE8.EAPoly.extend (midInj p d q)) ++ pins p d q X.r,
          B.pos.map (Work.WilE8.EAPoly.extend (midInj p d q))⟩ : Basic (p + (d + q)) X.r))).map
        Basic.deg
      = X.basics.map (fun B => B.deg + 2 * d) := by
    rw [List.map_map]
    exact List.map_congr_left (l := X.basics) (fun B _ => basic_deg_padStrat_basic p q d X B)
  have h₂ : (X.basics.map (fun B => B.deg + 2 * d)).sum
      = X.deg + 2 * d * X.basics.length := by
    rw [sum_map_deg_add X.basics Basic.deg (2 * d), SemiPf.deg]
  have hdeg : (Work.WilE7.padStrat p q d X).deg
      = (X.basics.map (fun B => B.deg + 2 * d)).sum := by
    simp only [SemiPf.deg, Work.WilE7.padStrat_basics]
    exact congrArg List.sum heq
  rw [hdeg, h₂]

end Work.WilE7.PadAux
