import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseRowQ2.maskSharpCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.mc_split` — the lattice split `Mc = ChatᵀChat + Tail`

The mask row applies the matrix `Mc N i j = χ̂²(vec (K i − K j))` to the masked vector
`w = wfun … u`.  By definition of the Schwartz-tail matrix

    `Tail N i j = Mc N i j − ∑ k : Lab N, Chat N k i * Chat N k j`

the quadratic form of `Mc` splits *exactly* into the squared norm of `Cw` (`bfun`) plus
the quadratic form of `Tail`:

    `∑_ij w i · w j · Mc i j = ∑_k (∑_i w i · Chat k i)² + ∑_ij w i · w j · Tail i j`.

Nothing analytic enters: it is the finite-sum reshuffle
`wᵢwⱼ Σ_k Chat k i Chat k j = Σ_k (wᵢChat k i)(wⱼChat k j)` followed by the exchange of the
three finite sums.  The lemma below is stated for an arbitrary weight `w`; the requested
theorem `mc_split` is its instance `w = wfun … u`.
-/

namespace Work.BoseRowQ2

open Work.BoseBoxFock

/-- `Mc = ChatᵀChat + Tail`, rearranged from the definition of `Tail`. -/
lemma Mc_eq_chatTchat_add_Tail (N : ℕ) (i j : Lab N) :
    Mc N i j = (∑ k : Lab N, Chat N k i * Chat N k j) + Tail N i j := by
  simp only [Tail]
  ring

/-- The `ChatᵀChat` part of the `Mc`-form is the squared `ℓ²`-norm of `Cw`. -/
lemma chatTchat_quad_eq (N : ℕ) (w : Lab N → ℝ) :
    (∑ i : Lab N, ∑ j : Lab N, w i * w j * (∑ k : Lab N, Chat N k i * Chat N k j))
      = ∑ k : Lab N, (∑ i : Lab N, w i * Chat N k i) ^ 2 := by
  have ht : ∀ i j : Lab N, w i * w j * (∑ k : Lab N, Chat N k i * Chat N k j)
      = ∑ k : Lab N, (w i * Chat N k i) * (w j * Chat N k j) := by
    intro i j
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  calc (∑ i : Lab N, ∑ j : Lab N, w i * w j * (∑ k : Lab N, Chat N k i * Chat N k j))
      = ∑ i : Lab N, ∑ j : Lab N, ∑ k : Lab N, (w i * Chat N k i) * (w j * Chat N k j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ht i j
    _ = ∑ k : Lab N, ∑ i : Lab N, ∑ j : Lab N, (w i * Chat N k i) * (w j * Chat N k j) :=
        triple_sum_comm _
    _ = ∑ k : Lab N, (∑ i : Lab N, w i * Chat N k i) ^ 2 :=
        Finset.sum_congr rfl fun k _ =>
          (sq_eq_sum_sum_sq (fun i : Lab N => w i * Chat N k i)).symm

/-- **The `Mc`-form splits as `ChatᵀChat + Tail`**: the lattice Parseval split of the mask row
for an arbitrary weight `w`. -/
lemma mcQuadSplit (N : ℕ) (w : Lab N → ℝ) :
    (∑ i : Lab N, ∑ j : Lab N, w i * w j * Mc N i j)
      = (∑ k : Lab N, (∑ i : Lab N, w i * Chat N k i) ^ 2)
        + ∑ i : Lab N, ∑ j : Lab N, w i * w j * Tail N i j := by
  have h1 : (∑ i : Lab N, ∑ j : Lab N, w i * w j * Mc N i j)
      = (∑ i : Lab N, ∑ j : Lab N, w i * w j * (∑ k : Lab N, Chat N k i * Chat N k j))
        + ∑ i : Lab N, ∑ j : Lab N, w i * w j * Tail N i j := by
    have h2 : ∀ i : Lab N, (∑ j : Lab N, w i * w j * Mc N i j)
        = (∑ j : Lab N, w i * w j * (∑ k : Lab N, Chat N k i * Chat N k j))
          + ∑ j : Lab N, w i * w j * Tail N i j := by
      intro i
      have h3 : (∑ j : Lab N, w i * w j * Mc N i j)
          = ∑ j : Lab N, (w i * w j * (∑ k : Lab N, Chat N k i * Chat N k j)
              + w i * w j * Tail N i j) :=
        Finset.sum_congr rfl fun j _ => by
          rw [Mc_eq_chatTchat_add_Tail N i j]; ring
      rw [h3, Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun i _ => h2 i, Finset.sum_add_distrib]
  calc (∑ i : Lab N, ∑ j : Lab N, w i * w j * Mc N i j)
      = (∑ i : Lab N, ∑ j : Lab N, w i * w j * (∑ k : Lab N, Chat N k i * Chat N k j))
        + ∑ i : Lab N, ∑ j : Lab N, w i * w j * Tail N i j := h1
    _ = (∑ k : Lab N, (∑ i : Lab N, w i * Chat N k i) ^ 2)
        + ∑ i : Lab N, ∑ j : Lab N, w i * w j * Tail N i j := by
          rw [chatTchat_quad_eq]

theorem mc_split {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut}
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ) (μ : ℝ) (u : Fin (HM μ).m → ℝ) :
    (∑ i : Work.BoseBoxFock.Lab (HM μ).N, ∑ j : Work.BoseBoxFock.Lab (HM μ).N,
        Work.BoseRowQ2.wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i
          * Work.BoseRowQ2.wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u j
          * Work.BoseRowQ2.Mc (HM μ).N i j)
      = (∑ k : Work.BoseBoxFock.Lab (HM μ).N,
          (Work.BoseRowQ2.bfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u k) ^ 2)
        + ∑ i : Work.BoseBoxFock.Lab (HM μ).N, ∑ j : Work.BoseBoxFock.Lab (HM μ).N,
            Work.BoseRowQ2.wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u i
              * Work.BoseRowQ2.wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u j
              * Work.BoseRowQ2.Tail (HM μ).N i j := by
  simpa only [bfun] using
    mcQuadSplit (HM μ).N (wfun (v := v) (h := h) (fc := fc) (fu := fu) HM μ u)

end Work.BoseRowQ2
