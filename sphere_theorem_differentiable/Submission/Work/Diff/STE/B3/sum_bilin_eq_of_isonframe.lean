import Mathlib
import Submission.Work.EXT.sum_inner_smul_eq_self_of_isONFrame

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-! ## Frame independence of the full contraction of a tensor built from two bilinear forms

For two bilinear forms `B, B'` on a finite dimensional real inner product space `V` and two
orthonormal frames `e, e'` of `V` (both indexed by `Fin (finrank ℝ E)`, where the tangent space is
the model space `E`), the double sum
`∑ a, ∑ b, B (e a) (e b) * B' (e a) (e b)`
is independent of the frame: it is the contraction of `B ⊗ B'` in the pattern `(a,b,a,b)`.

The proof only uses the expansion of vectors in an orthonormal frame
(`Work.EXT.sum_inner_smul_eq_self_of_isONFrame`, i.e. the coefficients `g.inner x v (e i)` give
`∑ i, g.inner x v (e i) • e i = v`, hence, dually, `∑ i, g.inner x u (e i) * g.inner x v (e i)
= g.inner x u v`), applied in the two slot pairs separately:

* `hstep1` shows that for a FIXED first-slot vector, summing the second slot over the frame `e'`
  agrees with summing it over the frame `e` (it uses the expansion of `e' b` in the frame `e` and
  `hL1fun`, the Riesz/Parseval statement for a functional `φ`: `∑ a, g.inner x (e' a) (e c) *
  φ (e' a) = φ (e c)`, a consequence of expanding `e c` in the frame `e'`);
* `hstep2` shows the same for the FIRST slot, with the second slot fixed in the frame `e`
  (`hL1bil` is the two-variable form of the same Parseval identity).

Both changes together turn `∑ a ∑ b B (e' a) (e' b) B' (e' a) (e' b)` into
`∑ a ∑ b B (e a) (e b) B' (e a) (e b)`.

(The intermediate sums are all over `Fin (Module.finrank ℝ E)`; no symmetry of `B` or `B'` is
used, and the statement holds for arbitrary bilinear forms. The two frames are two orthonormal
bases of the same space, so the change-of-frame matrix is orthogonal, which is exactly the content
of `hL1fun`/`hL1bil`.) -/

theorem sum_bilin_eq_of_isonframe
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (g : Submission.Diff.SMet I M) (p : M)
    (e e' : Fin (Module.finrank ℝ E) → TangentSpace I p)
    (he : Submission.Diff.IsONFrame g p e) (he' : Submission.Diff.IsONFrame g p e')
    (B B' : TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) :
    (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        B (e a) (e b) * B' (e a) (e b))
      = (∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        B (e' a) (e' b) * B' (e' a) (e' b)) := by
  classical
  -- The change-of-frame identity, functional form: the coefficients of a vector in an
  -- orthonormal frame pair against a functional behave like a projection.
  have hL1fun : ∀ (f f' : Fin (Module.finrank ℝ E) → TangentSpace I p)
      (hf : Submission.Diff.IsONFrame g p f) (hf' : Submission.Diff.IsONFrame g p f')
      (φ : TangentSpace I p →L[ℝ] ℝ) (c : Fin (Module.finrank ℝ E)),
      ∑ a, g.inner p (f' a) (f c) * φ (f' a) = φ (f c) := by
    intro f f' hf hf' φ c
    calc ∑ a, g.inner p (f' a) (f c) * φ (f' a)
        = ∑ a, g.inner p (f c) (f' a) * φ (f' a) := by
            apply Finset.sum_congr rfl; intro a _
            rw [g.symm p (f' a) (f c)]
      _ = ∑ a, φ (g.inner p (f c) (f' a) • f' a) := by
            apply Finset.sum_congr rfl; intro a _
            rw [map_smul, smul_eq_mul]
      _ = φ (∑ a, g.inner p (f c) (f' a) • f' a) := by rw [map_sum]
      _ = φ (f c) := by rw [Work.EXT.sum_inner_smul_eq_self_of_isONFrame g p f' hf' (f c)]
  -- The same identity with a bilinear form in place of a functional in the second factor.
  have hL1bil : ∀ (f f' : Fin (Module.finrank ℝ E) → TangentSpace I p)
      (hf : Submission.Diff.IsONFrame g p f) (hf' : Submission.Diff.IsONFrame g p f')
      (C : TangentSpace I p →L[ℝ] TangentSpace I p →L[ℝ] ℝ) (c d : Fin (Module.finrank ℝ E)),
      ∑ a, g.inner p (f' a) (f c) * C (f' a) (f d) = C (f c) (f d) := by
    intro f f' hf hf' C c d
    have hC : C (f c) (f d) = ∑ a, g.inner p (f' a) (f c) * C (f' a) (f d) := by
      have h1 : C (f c) = ∑ a, g.inner p (f c) (f' a) • C (f' a) := by
        conv_lhs => rw [← Work.EXT.sum_inner_smul_eq_self_of_isONFrame g p f' hf' (f c)]
        rw [map_sum]
        apply Finset.sum_congr rfl; intro a _
        rw [map_smul]
      rw [h1, sum_apply]
      apply Finset.sum_congr rfl; intro a _
      rw [smul_apply, smul_eq_mul, g.symm p (f c) (f' a)]
    exact hC.symm
  -- Expansion of the second factor in the frame `e`.
  have hevB' : ∀ a b : Fin (Module.finrank ℝ E),
      B' (e' a) (e' b) = ∑ d, g.inner p (e' b) (e d) * B' (e' a) (e d) := by
    intro a b
    conv_lhs => rw [← Work.EXT.sum_inner_smul_eq_self_of_isONFrame g p e he (e' b)]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [map_smul, smul_eq_mul]
  -- Expansion of the first factor (`B`) in the frame `e`.
  have hevB : ∀ a d : Fin (Module.finrank ℝ E),
      B (e' a) (e d) = ∑ c, g.inner p (e' a) (e c) * B (e c) (e d) := by
    intro a d
    have h1 : B (e' a) = ∑ c, g.inner p (e' a) (e c) • B (e c) := by
      conv_lhs => rw [← Work.EXT.sum_inner_smul_eq_self_of_isONFrame g p e he (e' a)]
      rw [map_sum]
      apply Finset.sum_congr rfl; intro c _
      rw [map_smul]
    rw [h1, sum_apply]
    apply Finset.sum_congr rfl; intro c _
    rw [smul_apply, smul_eq_mul]
  -- Summing the second slot over the frame `e'` or the frame `e` gives the same result.
  have hstep1 : ∀ a : Fin (Module.finrank ℝ E),
      (∑ b, B (e' a) (e' b) * B' (e' a) (e' b)) = ∑ d, B (e' a) (e d) * B' (e' a) (e d) := by
    intro a
    calc ∑ b, B (e' a) (e' b) * B' (e' a) (e' b)
        = ∑ b, B (e' a) (e' b) * (∑ d, g.inner p (e' b) (e d) * B' (e' a) (e d)) := by
            apply Finset.sum_congr rfl; intro b _; rw [hevB' a b]
      _ = ∑ b, ∑ d, B (e' a) (e' b) * (g.inner p (e' b) (e d) * B' (e' a) (e d)) := by
            apply Finset.sum_congr rfl; intro b _; rw [Finset.mul_sum]
      _ = ∑ d, ∑ b, B (e' a) (e' b) * (g.inner p (e' b) (e d) * B' (e' a) (e d)) :=
            Finset.sum_comm
      _ = ∑ d, B' (e' a) (e d) * (∑ b, g.inner p (e' b) (e d) * B (e' a) (e' b)) := by
            apply Finset.sum_congr rfl; intro d _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro b _
            ring
      _ = ∑ d, B' (e' a) (e d) * B (e' a) (e d) := by
            apply Finset.sum_congr rfl; intro d _
            rw [hL1fun e e' he he' (B (e' a)) d]
      _ = ∑ d, B (e' a) (e d) * B' (e' a) (e d) := by
            apply Finset.sum_congr rfl; intro d _; ring
  -- Summing the first slot over the frame `e'` or the frame `e` gives the same result.
  have hstep2 : (∑ a, ∑ d, B (e' a) (e d) * B' (e' a) (e d))
      = ∑ c, ∑ d, B (e c) (e d) * B' (e c) (e d) := by
    calc ∑ a, ∑ d, B (e' a) (e d) * B' (e' a) (e d)
        = ∑ a, ∑ d, (∑ c, g.inner p (e' a) (e c) * B (e c) (e d)) * B' (e' a) (e d) := by
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro d _
            rw [hevB a d]
      _ = ∑ a, ∑ d, ∑ c, (g.inner p (e' a) (e c) * B (e c) (e d)) * B' (e' a) (e d) := by
            apply Finset.sum_congr rfl; intro a _
            apply Finset.sum_congr rfl; intro d _
            rw [Finset.sum_mul]
      _ = ∑ a, ∑ c, ∑ d, (g.inner p (e' a) (e c) * B (e c) (e d)) * B' (e' a) (e d) := by
            apply Finset.sum_congr rfl; intro a _
            exact Finset.sum_comm
      _ = ∑ c, ∑ a, ∑ d, (g.inner p (e' a) (e c) * B (e c) (e d)) * B' (e' a) (e d) :=
            Finset.sum_comm
      _ = ∑ c, ∑ d, ∑ a, (g.inner p (e' a) (e c) * B (e c) (e d)) * B' (e' a) (e d) := by
            apply Finset.sum_congr rfl; intro c _
            exact Finset.sum_comm
      _ = ∑ c, ∑ d, B (e c) (e d) * (∑ a, g.inner p (e' a) (e c) * B' (e' a) (e d)) := by
            apply Finset.sum_congr rfl; intro c _
            apply Finset.sum_congr rfl; intro d _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro a _
            ring
      _ = ∑ c, ∑ d, B (e c) (e d) * B' (e c) (e d) := by
            apply Finset.sum_congr rfl; intro c _
            apply Finset.sum_congr rfl; intro d _
            rw [hL1bil e e' he he' B' c d]
  -- Assembly.
  refine (show (∑ a, ∑ b, B (e' a) (e' b) * B' (e' a) (e' b))
      = ∑ a, ∑ b, B (e a) (e b) * B' (e a) (e b) from ?_).symm
  calc ∑ a, ∑ b, B (e' a) (e' b) * B' (e' a) (e' b)
      = ∑ a, ∑ d, B (e' a) (e d) * B' (e' a) (e d) :=
          Finset.sum_congr rfl (fun a _ => hstep1 a)
    _ = ∑ c, ∑ d, B (e c) (e d) * B' (e c) (e d) := hstep2
    _ = ∑ a, ∑ b, B (e a) (e b) * B' (e a) (e b) := rfl

end Work.Diff.STE.B3
