import Mathlib
import Submission.Work.Diff.Alg.Pinch.Linv
import Submission.Work.Diff.Alg.q2p_defs
import Submission.Work.Diff.Alg.Pinch.inPIC2_cone_basic
import Submission.Work.Diff.Alg.Pinch.Phi_wedge
import Submission.Work.Diff.Alg.Pinch.ChatT_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

open Submission.Diff.Alg Work.Diff.Alg.Q2P Work.Diff.Alg.Q2PR

theorem ChatT_one_step_pic (n : ℕ) {S X : Submission.Diff.Alg.Curv4 n}
    (hS : Submission.Diff.Alg.IsAlgCurv S) (hX : Submission.Diff.Alg.IsAlgCurv X)
    (hP : Submission.Diff.Alg.InPIC2 S)
    (hstrict : ∀ x y z w : Fin n → ℝ,
      Work.Diff.Alg.Q2P.EFun S x y z w = 0 →
      Work.Diff.Alg.Q2P.EFun (Submission.Diff.Alg.Iso n) x y z w ≠ 0 →
      0 < Work.Diff.Alg.Q2P.EFun X x y z w) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, 0 < s → s ≤ ε →
      ∃ δ : ℝ, 0 < δ ∧ Submission.Diff.Alg.InPIC2 (S + s • X - δ • Submission.Diff.Alg.Iso n) := by
  -- The two pointwise inputs of the compact margin lemma, restricted to the compact set `ChatT_K`
  -- of `cHerm`-orthonormal pairs of complex vectors.
  have hA : ∀ p ∈ ChatT_K n, 0 ≤ EFunC S p.1 p.2 :=
    fun p _ => ChatT_inPIC2_EFunC hP p.1 p.2
  have hAB : ∀ p ∈ ChatT_K n, EFunC S p.1 p.2 = 0 → 0 < EFunC X p.1 p.2 := by
    intro p hp h0
    refine ChatT_strict_EFunC hstrict h0 ?_
    rw [ChatT_K_isZeroFree hp]
    exact one_ne_zero
  obtain ⟨ε, hε0, hε⟩ := ChatT_compact_eps_delta (ChatT_K_compact n)
    (ChatT_continuous_EFunC S).continuousOn (ChatT_continuous_EFunC X).continuousOn hA hAB
  refine ⟨ε, hε0, fun s hs0 hse => ?_⟩
  obtain ⟨δ, hδ0, hδ⟩ := hε s hs0 hse
  refine ⟨δ, hδ0, ?_⟩
  rw [Work.Diff.Alg.Q2P.inPIC2_iff_c]
  intro ζ η
  rw [ChatT_EFunC_lin]
  -- Degenerate case: the first vector vanishes.
  by_cases hζ0 : ζ = 0
  · rw [hζ0, ChatT_EFunC_zero_left, ChatT_EFunC_zero_left, ChatT_EFunC_zero_left]
    simp
  · -- Project the second vector on the `cHerm`-orthogonal complement of the first.
    have hζζ : cHerm ζ ζ ≠ 0 := by
      rw [cHerm_self]
      exact_mod_cast (ChatT_cNSq_pos.mpr hζ0).ne'
    set η' : Fin n → ℂ := η - (cHerm η ζ / cHerm ζ ζ) • ζ with hη'def
    have horth : cHerm η' ζ = 0 := by
      rw [hη'def]
      exact ChatT_cHerm_proj hζζ
    have hproj : ∀ R : Curv4 n, IsAlgCurv R → EFunC R ζ η = EFunC R ζ η' := by
      intro R hR
      rw [hη'def]
      exact (ChatT_EFunC_sub_smul R hR ζ η (cHerm η ζ / cHerm ζ ζ)).symm
    by_cases hη'0 : η' = 0
    · -- Degenerate case: the pair is complex dependent, so all three forms vanish.
      have hz : ∀ R : Curv4 n, IsAlgCurv R → EFunC R ζ η = 0 := by
        intro R hR
        rw [hproj R hR, hη'0, ChatT_EFunC_zero_right]
      rw [hz S hS, hz X hX, hz (Iso n) (ChatT_iso_isAlgCurv n)]
      simp
    · -- Non-degenerate case: rescale to a point of `ChatT_K` and use the margin bound.
      have horth' : cHerm ζ η' = 0 := by
        rw [Q2PR.cHerm_conj_symm, horth]
        simp
      obtain ⟨t, t', u, v, ht, ht', hu, hv, huv, hzu, hzv⟩ := ChatT_normalize hζ0 hη'0 horth'
      have hpK : (u, v) ∈ ChatT_K n := ⟨hu, hv, huv⟩
      have hδuv : δ ≤ EFunC S u v + s * EFunC X u v := hδ (u, v) hpK
      have hIuv : EFunC (Iso n) u v = 1 := ChatT_EFunC_iso_eq_one hu hv huv
      have hSsc : EFunC S ζ η = t * t' * EFunC S u v := by
        rw [hproj S hS, hzu, hzv]
        exact ChatT_EFunC_sqrt_smul S hS u v ht.le ht'.le
      have hXsc : EFunC X ζ η = t * t' * EFunC X u v := by
        rw [hproj X hX, hzu, hzv]
        exact ChatT_EFunC_sqrt_smul X hX u v ht.le ht'.le
      have hIsc : EFunC (Iso n) ζ η = t * t' * EFunC (Iso n) u v := by
        rw [hproj (Iso n) (ChatT_iso_isAlgCurv n), hzu, hzv]
        exact ChatT_EFunC_sqrt_smul (Iso n) (ChatT_iso_isAlgCurv n) u v ht.le ht'.le
      rw [hSsc, hXsc, hIsc, hIuv]
      have hfac : t * t' * EFunC S u v + s * (t * t' * EFunC X u v) - δ * (t * t' * 1)
          = t * t' * (EFunC S u v + s * EFunC X u v - δ) := by ring
      rw [hfac]
      exact mul_nonneg (mul_nonneg ht.le ht'.le) (by linarith [hδuv])

end Work.Diff.Alg.Pinch
