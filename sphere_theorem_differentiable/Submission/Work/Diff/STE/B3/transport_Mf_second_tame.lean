import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_tame_leibniz

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

set_option maxHeartbeats 4000000

/-! ## Germ invariance of the partial derivatives `pdR`

`pdR c f z = fderiv ℝ f z (Pi.single c 1)` depends only on the germ of `f` at `z`, and so does the
second derivative `pdR c (pdR d ·) z` (the second order version is reduced to the first by shrinking
to the open neighbourhood on which the two functions agree). -/

lemma pdR_congr_tame {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ}
    (hh : f =ᶠ[nhds z] g) (c : Fin n) :
    Work.Diff.STE.pdR c f z = Work.Diff.STE.pdR c g z := by
  rw [Work.Diff.STE.pdR, Work.Diff.STE.pdR, hh.fderiv_eq]

lemma pdR2_congr_tame {n : ℕ} {f g : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ}
    (hh : f =ᶠ[nhds z] g) (c d : Fin n) :
    Work.Diff.STE.pdR c (Work.Diff.STE.pdR d f) z
      = Work.Diff.STE.pdR c (Work.Diff.STE.pdR d g) z := by
  obtain ⟨t, ht_sub, ht_open, hzt⟩ := _root_.mem_nhds_iff.mp hh
  refine pdR_congr_tame ?_ c
  refine Filter.mem_of_superset (ht_open.mem_nhds hzt) ?_
  intro y hy
  exact pdR_congr_tame (Filter.eventually_of_mem (ht_open.mem_nhds hy)
    (fun w hw => ht_sub hw)) d

/-- **The second derivative of the frame-change identity, in germ form.**

If `Mf a b` agrees with `Σ_{ik} Ff a i · Gf i k · Ff b k` near `z`, and the two factor families are
`C²` at `z`, then `∂_c∂_d Mf a b` is the second derivative of that finite sum, which the linearity of
`pdR` over finite sums and the nine-term Leibniz rule for a triple product
(`Work.Diff.STE.B3.pdR2_triple_at`) expand; the eight terms not containing `∂_c∂_d Gf` are collected
in `eightTerm`, leaving the isolated term `Σ_{ik} Ff a i · ∂_c∂_d Gf i k · Ff b k`. -/
theorem transport_Mf_second_tame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (a b : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hEq : (fun w : Fin (Module.finrank ℝ E) → ℝ => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j w a b)
      =ᶠ[nhds z] (fun w : Fin (Module.finrank ℝ E) → ℝ =>
        ∑ i, ∑ k, Work.Diff.STE.B3.Ff (I := I) (M := M) D j w a i
          * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j w i k
          * Work.Diff.STE.B3.Ff (I := I) (M := M) D j w b k))
    (hFa : ∀ i : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ 2 (fun w => Work.Diff.STE.B3.Ff (I := I) (M := M) D j w a i) z)
    (hFb : ∀ k : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ 2 (fun w => Work.Diff.STE.B3.Ff (I := I) (M := M) D j w b k) z)
    (hG : ∀ i k : Fin (Module.finrank ℝ E),
      ContDiffAt ℝ 2 (fun w => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j w i k) z)
    (c d : Fin (Module.finrank ℝ E)) :
    Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
        (fun w : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.STE.B3.Mf (I := I) (M := M) D h j w a b)) z
      = (∑ i, ∑ k, Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
          * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
              (fun w => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j w i k)) z
          * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k)
        + Work.Diff.STE.B3.eightTerm (I := I) (M := M) D h j z c d a b := by
  rw [pdR2_congr_tame hEq c d]
  -- smoothness of the inner sums, to pull `∂_c∂_d` out of the two finite sums
  have hpartial : ∀ i : Fin (Module.finrank ℝ E), ContDiffAt ℝ 2
      (fun y : Fin (Module.finrank ℝ E) → ℝ => ∑ k,
        Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i
          * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k
          * Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k) z := by
    intro i
    refine ContDiffAt.sum (fun k _ => ?_)
    exact ContDiffAt.mul (ContDiffAt.mul (hFa i) (hG i k)) (hFb k)
  rw [pdR2_fun_sum_at c d hpartial]
  rw [Finset.sum_congr rfl (fun i _ => pdR2_fun_sum_at c d
    (fun k => ContDiffAt.mul (ContDiffAt.mul (hFa i) (hG i k)) (hFb k)))]
  -- the nine-term Leibniz rule for each summand, with `∂_c∂_d Gf` isolated
  have hpoint : ∀ (i k : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i
            * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k
            * Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k)) z
        = Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
            * (Work.Diff.STE.pdR c (Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k)) z)
            * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k
          + ( Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
                (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i)) z
                * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k
                * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k
            + Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i) z
                * Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k) z
                * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k
            + Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i) z
                * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k
                * Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k) z
            + Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i) z
                * Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k) z
                * Work.Diff.STE.B3.Ff (I := I) (M := M) D j z b k
            + Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Work.Diff.STE.B3.Ff (I := I) (M := M) D j y a i) z
                * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k
                * Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k) z
            + Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
                * Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k) z
                * Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k) z
            + Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
                * Work.Diff.STE.pdR d (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y i k) z
                * Work.Diff.STE.pdR c (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k) z
            + Work.Diff.STE.B3.Ff (I := I) (M := M) D j z a i
                * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k
                * Work.Diff.STE.pdR c (Work.Diff.STE.pdR d
                  (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                    Work.Diff.STE.B3.Ff (I := I) (M := M) D j y b k)) z ) := by
    intro i k
    rw [Work.Diff.STE.B3.pdR2_triple_at c d (hFa i) (hG i k) (hFb k)]
    ring
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => hpoint i k))]
  simp only [Finset.sum_add_distrib, Work.Diff.STE.B3.eightTerm]

end Work.Diff.STE.B3
