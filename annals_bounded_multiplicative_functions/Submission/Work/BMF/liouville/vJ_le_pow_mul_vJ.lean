import Mathlib
import Submission.Work.BMF.vkford_defs
import Submission.Work.BMF.recursion.struct
import Submission.Work.BMF.recursion.Jdiff_le_zero
import Submission.Work.BMF.recursion.headtail_factor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Reduction of the Vinogradov count to fewer variables

`vJ s k X ≤ X^{2(s-s')} · vJ s' k X` for `s' ≤ s`.

Splitting a pair of `s`-tuples into its first `s'` coordinates ("head") and the remaining
`s - s'` coordinates ("tail"), a matching pair is the same thing as a pair of head tuples whose
moment vector differs by the moment vector of the tail pair (with a sign).  Summing over the tail
pair `q` — there are only `X^{2(s-s')}` of them — the number of head pairs matching a fixed tail
pair is `Jdiff s' k X (powerSums q.2 - powerSums q.1)`, and each of these is at most
`Jdiff s' k X 0 = vJ s' k X` by the "diagonal dominates" lemma `Jdiff_le_zero` (Cauchy–Schwarz on
the fibres of the moment map).
-/

open scoped BigOperators

namespace Work.BMF.liouville

open Work.BMF.recursion

/-- `Jdiff m k X 0` is `vJ m k X`: both count the pairs of `m`-tuples with equal moment vectors. -/
lemma Jdiff_zero_eq_vJ (m k X : ℕ) : ((Jdiff m k X 0 : ℕ) : ℝ) = Work.BMF.vJ m k X := by
  have hset : (Finset.univ.filter (fun p : PairSpace m X =>
        Submission.Vinogradov.powerSums k p.1 - Submission.Vinogradov.powerSums k p.2 = 0))
      = solSet m k X := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, solSet, sub_eq_zero]
    exact Submission.Vinogradov.powerSums_eq_iff_matches p.1 p.2
  rw [Jdiff, hset]
  exact (J_eq_solSet m k X).symm

/-- Splitting the moment vector of a tuple into the moment vectors of its head and its tail
(for an arbitrary degree bound `k` of the moment vector). -/
lemma powerSums_zipT_general {k s' s X : ℕ} (h : s' ≤ s) (q : Tup s' X × Tup (s - s') X) :
    Submission.Vinogradov.powerSums k (zipT h q)
      = Submission.Vinogradov.powerSums k q.1 + Submission.Vinogradov.powerSums k q.2 := by
  rw [powerSums_eq_sum_mom1 (k := k) (x := zipT h q),
      powerSums_eq_sum_mom1 (k := k) (x := q.1),
      powerSums_eq_sum_mom1 (k := k) (x := q.2),
      sum_split_fin (k := s') (S := s) h (fun i : Fin s => mom1 k ((zipT h q i).1))]
  congr 1
  · exact Finset.sum_congr rfl (fun i _ => by rw [zipT_apply_hIdx])
  · exact Finset.sum_congr rfl (fun r _ => by rw [zipT_apply_tIdx])

lemma powerSums_split {k s' s X : ℕ} (h : s' ≤ s) (x : Tup s X) :
    Submission.Vinogradov.powerSums k x
      = Submission.Vinogradov.powerSums k (hdT h x) + Submission.Vinogradov.powerSums k (tlT h x) := by
  conv_lhs => rw [← zipT_hdT_tlT (Q := X) h x]
  exact powerSums_zipT_general h (hdT h x, tlT h x)

/-- Matching is equality of moment vectors, for the recursion's `Matches`. -/
lemma matches_iff_moment_eq {s k X : ℕ} (p : PairSpace s X) :
    Matches s k X p ↔ Submission.Vinogradov.powerSums k p.1 = Submission.Vinogradov.powerSums k p.2 :=
  (Submission.Vinogradov.powerSums_eq_iff_matches p.1 p.2).symm

/-- **Reduction of the Vinogradov count**: `J_{s,k}(X) ≤ X^{2(s-s')} J_{s',k}(X)` for `s' ≤ s`. -/
theorem vJ_le_pow_mul_vJ (s s' k X : ℕ) (h : s' ≤ s) :
    Work.BMF.vJ s k X ≤ (X : ℝ) ^ (2 * (s - s')) * Work.BMF.vJ s' k X := by
  classical
  -- The matching condition, rewritten in terms of head and tail moment vectors.
  have hkey : ∀ p : PairSpace s X,
      Matches s k X p ↔
        Submission.Vinogradov.powerSums k (hdT h p.1) - Submission.Vinogradov.powerSums k (hdT h p.2)
          = Submission.Vinogradov.powerSums k (tlT h p.2)
            - Submission.Vinogradov.powerSums k (tlT h p.1) := by
    intro p
    rw [matches_iff_moment_eq p, powerSums_split (k := k) h p.1, powerSums_split (k := k) h p.2]
    set A := Submission.Vinogradov.powerSums k (hdT h p.1) with hA
    set B := Submission.Vinogradov.powerSums k (hdT h p.2) with hB
    set U := Submission.Vinogradov.powerSums k (tlT h p.1) with hU
    set V := Submission.Vinogradov.powerSums k (tlT h p.2) with hV
    constructor
    · intro h1
      have h2 : A + U - (B + V) = 0 := by rw [h1]; abel
      have h3 : (A - B) - (V - U) = (A + U) - (B + V) := by abel
      rwa [← sub_eq_zero (a := A - B) (b := V - U), h3]
    · intro h1
      have h2 : (A - B) - (V - U) = 0 := by rw [h1]; abel
      have h3 : (A + U) - (B + V) = (A - B) - (V - U) := by abel
      rwa [← sub_eq_zero (a := A + U) (b := B + V), h3]
  -- Fibre decomposition over the tail pair.
  have hcard : (solSet s k X).card =
      ∑ q : PairSpace (s - s') X,
        ((solSet s k X).filter (fun p => (tlT h p.1, tlT h p.2) = q)).card := by
    have h1 := Finset.card_eq_sum_card_fiberwise (s := solSet s k X)
      (t := (Finset.univ : Finset (PairSpace (s - s') X)))
      (f := fun p : PairSpace s X => (tlT h p.1, tlT h p.2))
      (fun p _ => Finset.mem_univ _)
    rw [h1]
  -- Each fibre is a `Jdiff` count of the head pairs.
  have hfib : ∀ q : PairSpace (s - s') X,
      ((solSet s k X).filter (fun p => (tlT h p.1, tlT h p.2) = q)).card
        = Jdiff s' k X (Submission.Vinogradov.powerSums k q.2
            - Submission.Vinogradov.powerSums k q.1) := by
    intro q
    have hbij : ((solSet s k X).filter (fun p => (tlT h p.1, tlT h p.2) = q)).card
        = ((Finset.univ : Finset (PairSpace s' X)).filter
            (fun r => Submission.Vinogradov.powerSums k r.1 - Submission.Vinogradov.powerSums k r.2
              = Submission.Vinogradov.powerSums k q.2
                - Submission.Vinogradov.powerSums k q.1)).card := by
      refine Finset.card_bij (fun p _ => (hdT h p.1, hdT h p.2)) ?_ ?_ ?_
      · -- maps into the `Jdiff` set
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hmat, hTq⟩ := hp
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        have hmem : Matches s k X p := by
          simpa only [solSet, Finset.mem_filter, Finset.mem_univ, true_and] using hmat
        have hcond := (hkey p).mp hmem
        rw [hcond]
        have ht1 : tlT h p.1 = q.1 := congrArg Prod.fst hTq
        have ht2 : tlT h p.2 = q.2 := congrArg Prod.snd hTq
        rw [ht1, ht2]
      · -- injective
        intro p hp p' hp' heq
        rw [Finset.mem_filter] at hp hp'
        obtain ⟨-, hTq⟩ := hp
        obtain ⟨-, hTq'⟩ := hp'
        have h1 : hdT h p.1 = hdT h p'.1 := congrArg Prod.fst heq
        have h2 : hdT h p.2 = hdT h p'.2 := congrArg Prod.snd heq
        have ht1 : tlT h p.1 = tlT h p'.1 := by
          have a : tlT h p.1 = q.1 := congrArg Prod.fst hTq
          have b : tlT h p'.1 = q.1 := congrArg Prod.fst hTq'
          rw [a, b]
        have ht2 : tlT h p.2 = tlT h p'.2 := by
          have a : tlT h p.2 = q.2 := congrArg Prod.snd hTq
          have b : tlT h p'.2 = q.2 := congrArg Prod.snd hTq'
          rw [a, b]
        have hx : p.1 = p'.1 := by
          rw [← zipT_hdT_tlT (Q := X) h p.1, ← zipT_hdT_tlT (Q := X) h p'.1, h1, ht1]
        have hy : p.2 = p'.2 := by
          rw [← zipT_hdT_tlT (Q := X) h p.2, ← zipT_hdT_tlT (Q := X) h p'.2, h2, ht2]
        exact Prod.ext hx hy
      · -- surjective
        intro r hr
        rw [Finset.mem_filter] at hr
        obtain ⟨-, hrcond⟩ := hr
        refine ⟨(zipT h (r.1, q.1), zipT h (r.2, q.2)), ?_, ?_⟩
        · rw [Finset.mem_filter]
          refine ⟨?_, ?_⟩
          · rw [solSet, Finset.mem_filter]
            refine ⟨Finset.mem_univ _, (hkey _).mpr ?_⟩
            rw [hdT_zipT, hdT_zipT, tlT_zipT, tlT_zipT]
            exact hrcond
          · simp only [tlT_zipT]
        · rw [hdT_zipT, hdT_zipT]
    rw [hbij]
    rfl
  calc Work.BMF.vJ s k X
      = ((solSet s k X).card : ℝ) := J_eq_solSet s k X
    _ = ∑ q : PairSpace (s - s') X,
          (((solSet s k X).filter (fun p => (tlT h p.1, tlT h p.2) = q)).card : ℝ) := by
        rw [hcard]; push_cast; rfl
    _ = ∑ q : PairSpace (s - s') X,
          ((Jdiff s' k X (Submission.Vinogradov.powerSums k q.2
            - Submission.Vinogradov.powerSums k q.1) : ℕ) : ℝ) :=
        Finset.sum_congr rfl (fun q _ => by rw [hfib q])
    _ ≤ ∑ _q : PairSpace (s - s') X, (Work.BMF.vJ s' k X) := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        have h1 : ((Jdiff s' k X (Submission.Vinogradov.powerSums k q.2
            - Submission.Vinogradov.powerSums k q.1) : ℕ) : ℝ)
            ≤ ((Jdiff s' k X 0 : ℕ) : ℝ) := by
          exact_mod_cast Jdiff_le_zero s' k X (Submission.Vinogradov.powerSums k q.2
            - Submission.Vinogradov.powerSums k q.1)
        rwa [Jdiff_zero_eq_vJ] at h1
    _ = ((X : ℝ) ^ (s - s')) ^ 2 * Work.BMF.vJ s' k X := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 1
        rw [Submission.Vinogradov.univ_card]
        push_cast
        ring
    _ = (X : ℝ) ^ (2 * (s - s')) * Work.BMF.vJ s' k X := by
        rw [pow_two, ← pow_add]
        ring_nf

end Work.BMF.liouville
