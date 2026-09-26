import Mathlib
import Submission.Work.PTCert.LetterCore
import Submission.Work.PTCert.QAdjOpDefs
import Submission.Work.PTCert.QEdges_toFinset
import Submission.Work.PTCert.QEdges_nodup
import Submission.Work.PTCert.edgePair_injective
import Submission.Work.PTCert.adj_iff_shares
import Submission.Work.PTCert.op_iff_not_shares

/-!
# Splitting the `Adj + k·Op` form onto the edge sets

`QAdjOp r kop mu` is defined as a double sum over the *list* `QEdges r` of edges of the
simplex, with weight `0` on the diagonal, `1` on adjacent pairs and `kop` on opposite
pairs.  The certificate comparison writes the very same form as
`∑_{x ∈ Psub r r} c_{x.1} c_{x.2} + kop * ∑_{x ∈ Qsub r r} c_{x.1} c_{x.2}`.

This file proves the two agree.  The work splits into

* converting the nested `List.sum`s into nested `Finset.sum`s over `(QEdges r).toFinset`
  (`QEdges_nodup`) and then reindexing along the bijection `edgePair : Edge r ≃ QEdges r`
  (`QEdges_toFinset`, `edgePair_injective`);
* the pointwise weight identity `[e = f]·0 + (…)·(1 | kop) = [Adj]·1 + kop·[Op]`, which is
  the trichotomy of `Edge` (`adj_iff_shares`, `op_iff_not_shares`);
* turning the `Finset`-filtered sums over `Psub r r`/`Qsub r r` into iterated sums.
-/

namespace Work.PTCert

open Submission.PTCert
open Submission.RouteB
open Submission.RouteB.Edge

/-- `(if c then 0 else w * x * y) = ((if c then 0 else w) * x) * y`. -/
private lemma ite_zero_mul (c : Prop) [Decidable c] (w x y : ℚ) :
    (if c then (0:ℚ) else w * x * y) = (if c then 0 else w) * x * y := by
  by_cases h : c <;> simp [h]

/-- `((if c then 1 else 0) * z) = (if c then z else 0)`. -/
private lemma ite_one_mul (c : Prop) [Decidable c] (z : ℚ) :
    (if c then (1:ℚ) else 0) * z = if c then z else 0 := by
  by_cases h : c <;> simp [h]

/-- The weight carried by a pair of edges in `QAdjOp` is `1` when they are adjacent, `kop`
when they are opposite, and `0` when they coincide. -/
private lemma weight_eq (r : ℕ) (kop : ℚ) (p q : Edge r) :
    (if edgePair p = edgePair q then (0:ℚ) else
      (if (edgePair p).1 = (edgePair q).1 ∨ (edgePair p).1 = (edgePair q).2 ∨
          (edgePair p).2 = (edgePair q).1 ∨ (edgePair p).2 = (edgePair q).2
        then (1:ℚ) else kop))
      = (if Edge.Adj p q then 1 else 0) +
        kop * (if Edge.Op p q then 1 else 0) := by
  by_cases hpq : p = q
  · subst hpq
    have hadj : ¬ Edge.Adj p p := fun h => h.1 rfl
    have hop : ¬ Edge.Op p p := Edge.op_irrefl p
    rw [if_pos rfl, if_neg hadj, if_neg hop]
    ring
  · have hne : ¬ (edgePair p = edgePair q) := fun h => hpq (edgePair_injective r h)
    rw [if_neg hne]
    rcases Edge.trichotomy hpq with hA | hO
    · have hsh : (edgePair p).1 = (edgePair q).1 ∨ (edgePair p).1 = (edgePair q).2 ∨
            (edgePair p).2 = (edgePair q).1 ∨ (edgePair p).2 = (edgePair q).2 :=
        (shares_iff _ _).mp ((adj_iff_shares r p q).mp hA).2
      have hno : ¬ Edge.Op p q := fun h => hA.2 h
      rw [if_pos hsh, if_pos hA, if_neg hno]
      ring
    · have hsh : ¬ ((edgePair p).1 = (edgePair q).1 ∨ (edgePair p).1 = (edgePair q).2 ∨
            (edgePair p).2 = (edgePair q).1 ∨ (edgePair p).2 = (edgePair q).2) :=
        fun h => (op_iff_not_shares r p q).mp hO ((shares_iff _ _).mpr h)
      have hna : ¬ Edge.Adj p q := fun h => h.2 hO
      rw [if_neg hsh, if_neg hna, if_pos hO]
      ring

/-- Reindexing a sum over the edge list along `edgePair`. -/
private lemma QEdges_list_sum (r : ℕ) (F : ℕ × ℕ → ℚ) :
    (∑ e ∈ (QEdges r).toFinset, F e) = ∑ p : Edge r, F (edgePair p) := by
  rw [QEdges_toFinset, Finset.sum_image (fun x _ y _ h => edgePair_injective r h)]

/-- The nested `List.sum` of `QAdjOp` as a nested `Finset.sum` over `Edge r`. -/
private lemma QEdges_double_sum (r : ℕ) (G : ℕ × ℕ → ℕ × ℕ → ℚ) :
    ((QEdges r).map (fun e => ((QEdges r).map (fun f => G e f)).sum)).sum
      = ∑ p : Edge r, ∑ q : Edge r, G (edgePair p) (edgePair q) := by
  rw [← List.sum_toFinset (fun e => ((QEdges r).map (fun f => G e f)).sum) (QEdges_nodup r)]
  have h1 : ∀ e ∈ (QEdges r).toFinset,
      ((QEdges r).map (fun f => G e f)).sum = ∑ f ∈ (QEdges r).toFinset, G e f :=
    fun e _ => by rw [← List.sum_toFinset (fun f => G e f) (QEdges_nodup r)]
  rw [Finset.sum_congr rfl h1]
  rw [show (∑ e ∈ (QEdges r).toFinset, ∑ f ∈ (QEdges r).toFinset, G e f)
      = (∑ e ∈ (QEdges r).toFinset, ∑ q : Edge r, G e (edgePair q)) from
      Finset.sum_congr rfl (fun e _ => QEdges_list_sum r (fun q => G e q))]
  exact QEdges_list_sum r (fun p => ∑ q : Edge r, G p (edgePair q))

/-- `Psub r r` is the set of adjacent ordered pairs of edges. -/
private lemma Psub_self_filter (r : ℕ) :
    Edge.Psub r r =
      Finset.univ.filter (fun x : Edge r × Edge r =>
        Edge.Adj x.1 x.2) := by
  ext x
  rw [Edge.mem_Psub_self, Finset.mem_filter]
  simp

/-- `Qsub r r` is the set of opposite ordered pairs of edges. -/
private lemma Qsub_self_filter (r : ℕ) :
    Edge.Qsub r r =
      Finset.univ.filter (fun x : Edge r × Edge r =>
        Edge.Op x.1 x.2) := by
  ext x
  rw [Edge.mem_Qsub_self, Finset.mem_filter]
  simp

theorem QAdjOpSplit (r : ℕ) (kop mu : ℚ) (a b : ℕ) :
    Submission.PTCert.QAdjOp r kop mu a b =
      (∑ x ∈ Submission.RouteB.Edge.Psub r r,
          Submission.PTCert.cEdge r (Submission.PTCert.edgePair x.1) a *
            Submission.PTCert.cEdge r (Submission.PTCert.edgePair x.2) b)
      + kop * (∑ x ∈ Submission.RouteB.Edge.Qsub r r,
          Submission.PTCert.cEdge r (Submission.PTCert.edgePair x.1) a *
            Submission.PTCert.cEdge r (Submission.PTCert.edgePair x.2) b)
      - mu * ((if a = 0 then Submission.PTCert.cDelta r b else 0) +
          (if b = 0 then Submission.PTCert.cDelta r a else 0)) / 2 := by
  rw [QAdjOp_eq_QEdges]
  -- pointwise: the list weight equals `Adj`-weight plus `kop` times `Op`-weight
  have hW : ∀ p q : Edge r,
      (if edgePair p = edgePair q then (0:ℚ) else
        (if (edgePair p).1 = (edgePair q).1 ∨ (edgePair p).1 = (edgePair q).2 ∨
            (edgePair p).2 = (edgePair q).1 ∨ (edgePair p).2 = (edgePair q).2
          then (1:ℚ) else kop) *
            cEdge r (edgePair p) a * cEdge r (edgePair q) b)
      = (if Edge.Adj p q then 1 else 0) *
          (cEdge r (edgePair p) a * cEdge r (edgePair q) b)
        + kop * ((if Edge.Op p q then 1 else 0) *
          (cEdge r (edgePair p) a * cEdge r (edgePair q) b)) := by
    intro p q
    rw [ite_zero_mul, weight_eq]
    ring
  have hmain : ((QEdges r).map (fun e => ((QEdges r).map (fun f =>
        if e = f then 0 else
          (if e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2 then 1 else kop) *
            cEdge r e a * cEdge r f b)).sum)).sum
      = (∑ x ∈ Submission.RouteB.Edge.Psub r r,
          cEdge r (edgePair x.1) a * cEdge r (edgePair x.2) b)
        + kop * (∑ x ∈ Submission.RouteB.Edge.Qsub r r,
          cEdge r (edgePair x.1) a * cEdge r (edgePair x.2) b) := by
    rw [QEdges_double_sum r (fun e f => if e = f then 0 else
          (if e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2 then 1 else kop) *
            cEdge r e a * cEdge r f b)]
    -- split the weight into its adjacent and opposite parts
    have hmid : (∑ p : Edge r, ∑ q : Edge r,
          (if edgePair p = edgePair q then (0:ℚ) else
            (if (edgePair p).1 = (edgePair q).1 ∨ (edgePair p).1 = (edgePair q).2 ∨
                (edgePair p).2 = (edgePair q).1 ∨ (edgePair p).2 = (edgePair q).2
              then (1:ℚ) else kop) *
                cEdge r (edgePair p) a * cEdge r (edgePair q) b))
        = (∑ p : Edge r, ∑ q : Edge r,
              (if Edge.Adj p q then 1 else 0) *
                (cEdge r (edgePair p) a * cEdge r (edgePair q) b))
          + kop * (∑ p : Edge r, ∑ q : Edge r,
              (if Edge.Op p q then 1 else 0) *
                (cEdge r (edgePair p) a * cEdge r (edgePair q) b)) := by
      calc (∑ p : Edge r, ∑ q : Edge r,
            (if edgePair p = edgePair q then (0:ℚ) else
              (if (edgePair p).1 = (edgePair q).1 ∨ (edgePair p).1 = (edgePair q).2 ∨
                  (edgePair p).2 = (edgePair q).1 ∨ (edgePair p).2 = (edgePair q).2
                then (1:ℚ) else kop) *
                  cEdge r (edgePair p) a * cEdge r (edgePair q) b))
          = ∑ p : Edge r, ((∑ q : Edge r,
                (if Edge.Adj p q then 1 else 0) *
                  (cEdge r (edgePair p) a * cEdge r (edgePair q) b))
              + kop * (∑ q : Edge r,
                (if Edge.Op p q then 1 else 0) *
                  (cEdge r (edgePair p) a * cEdge r (edgePair q) b))) := by
            apply Finset.sum_congr rfl
            intro p _
            rw [Finset.sum_congr rfl (fun q _ => hW p q), Finset.sum_add_distrib,
              ← Finset.mul_sum]
        _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hmid]
    have hP : (∑ p : Edge r, ∑ q : Edge r,
          (if Edge.Adj p q then 1 else 0) *
            (cEdge r (edgePair p) a * cEdge r (edgePair q) b))
        = ∑ x ∈ Submission.RouteB.Edge.Psub r r,
            cEdge r (edgePair x.1) a * cEdge r (edgePair x.2) b := by
      rw [Psub_self_filter, Finset.sum_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
      exact ite_one_mul _ _
    have hQ : (∑ p : Edge r, ∑ q : Edge r,
          (if Edge.Op p q then 1 else 0) *
            (cEdge r (edgePair p) a * cEdge r (edgePair q) b))
        = ∑ x ∈ Submission.RouteB.Edge.Qsub r r,
            cEdge r (edgePair x.1) a * cEdge r (edgePair x.2) b := by
      rw [Qsub_self_filter, Finset.sum_filter, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
      exact ite_one_mul _ _
    rw [hP, hQ]
  rw [hmain]

end Work.PTCert
