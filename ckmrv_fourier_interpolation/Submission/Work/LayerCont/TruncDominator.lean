import Mathlib
import Submission.Work.LayerCont.CuspExpansionKernelClosure
import Submission.Work.LayerCont.GapBoundKaxis

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.LayerCont

open UpperHalfPlane MeasureTheory Filter
open scoped Topology

/-- The truncated window `[1,T]` with the removed interval `(t₀-A, t₀+A)`: the region of
`(τ,t)` on which the *trunc* cusp expansion is needed.  Unlike `Work.LayerCont.gapSet` it carries
no guard: on the retained set `E = Ici 1 \ Ioo (t₀-A) (t₀+A)` the contour point is clean by
hypothesis, which is all the compactness argument needs. -/
def truncWin (K : Set UpperHalfPlane) (T t₀ A : ℝ) : Set (UpperHalfPlane × ℝ) :=
  K ×ˢ (Set.Icc (1 : ℝ) T \ Set.Ioo (t₀ - A) (t₀ + A))

/-- `truncWin` is compact. -/
theorem isCompact_truncWin {K : Set UpperHalfPlane} (hK : IsCompact K) (T t₀ A : ℝ) :
    IsCompact (truncWin K T t₀ A) := by
  have hc : IsCompact (Set.Icc (1 : ℝ) T \ Set.Ioo (t₀ - A) (t₀ + A)) :=
    isCompact_Icc.inter_right (isOpen_Ioo.isClosed_compl)
  exact hK.prod hc

/-- **Two-variable continuity of the kernel on `truncWin`**, with cleanliness assumed exactly on
the retained set. -/
theorem continuousOn_truncWin (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} {T t₀ A : ℝ}
    (hclean : ∀ (τ : UpperHalfPlane), τ ∈ K → ∀ t : ℝ,
      t ∈ Set.Ici (1 : ℝ) \ Set.Ioo (t₀ - A) (t₀ + A) →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (axisPt t)) :
    ContinuousOn (fun p : UpperHalfPlane × ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) p.1 p.2) (truncWin K T t₀ A) := by
  have hΨ : Continuous (fun p : UpperHalfPlane × ℝ => (p.1, axisPt p.2)) :=
    continuous_fst.prodMk (continuous_axisPt.comp continuous_snd)
  have hA : Continuous (fun p : UpperHalfPlane × ℝ =>
      Work.Asymptotics.AfunFun ℓ d p.1 (axisPt p.2)) :=
    Continuous.comp (f := fun p : UpperHalfPlane × ℝ => (p.1, axisPt p.2))
      (g := fun q : UpperHalfPlane × UpperHalfPlane => Work.Asymptotics.AfunFun ℓ d q.1 q.2)
      (Work.Asymptotics.continuous_AfunFun ℓ d) hΨ
  have hj1 : Continuous (fun p : UpperHalfPlane × ℝ => Work.Kernels.jInvariantFun p.1) :=
    Continuous.comp (f := fun p : UpperHalfPlane × ℝ => p.1)
      (g := fun τ : UpperHalfPlane => Work.Kernels.jInvariantFun τ)
      Work.Asymptotics.continuous_jInvariantFun' continuous_fst
  have hj2 : Continuous (fun p : UpperHalfPlane × ℝ => Work.Kernels.jInvariantFun (axisPt p.2)) :=
    Continuous.comp (f := fun p : UpperHalfPlane × ℝ => axisPt p.2)
      (g := fun τ : UpperHalfPlane => Work.Kernels.jInvariantFun τ)
      Work.Asymptotics.continuous_jInvariantFun'
      (continuous_axisPt.comp continuous_snd)
  have hj : Continuous (fun p : UpperHalfPlane × ℝ =>
      Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun (axisPt p.2)) := hj1.sub hj2
  have hne : ∀ p ∈ truncWin K T t₀ A,
      Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun (axisPt p.2) ≠ 0 := by
    intro p hp
    exact sub_ne_zero.mpr (hclean p.1 hp.1 p.2 ⟨hp.2.1.1, hp.2.2⟩)
  have hdiv : ContinuousOn (fun p : UpperHalfPlane × ℝ =>
      Work.Asymptotics.AfunFun ℓ d p.1 (axisPt p.2)
        / (Work.Kernels.jInvariantFun p.1 - Work.Kernels.jInvariantFun (axisPt p.2)))
      (truncWin K T t₀ A) :=
    hA.continuousOn.div hj.continuousOn hne
  have hKfun : ContinuousOn (fun p : UpperHalfPlane × ℝ =>
      Work.Kernels.Kfun ℓ d p.1 (axisPt p.2)) (truncWin K T t₀ A) := by
    refine hdiv.congr (fun p hp => ?_)
    rw [eq_div_iff (hne p hp)]
    exact Work.Asymptotics.Kfun_mul_slope_eq_AfunFun ℓ d hd p.1 (axisPt p.2)
      (sub_ne_zero.mp (hne p hp))
  have hEqOn : Set.EqOn
      (fun p : UpperHalfPlane × ℝ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) p.1 p.2)
      (fun p : UpperHalfPlane × ℝ => Work.Kernels.Kfun ℓ d p.1 (axisPt p.2))
      (truncWin K T t₀ A) := by
    intro p hp
    simp only [Work.Kernels.Kaxis,
      dif_pos (show (0 : ℝ) < p.2 by linarith [hp.2.1.1])]
    rw [axisPt_eq_imagAxis hp.2.1.1]
  exact hKfun.congr hEqOn

/-- **The trunc cusp dominator: the guarded expansion on the retained set `E`.**

For any compact `K`, with cleanliness on `E = Ici 1 \ Ioo (t₀-A) (t₀+A)` (the hypothesis the
differentiation-under-the-integral-sign argument carries), the difference `Kaxis - Aexp` is
bounded by `C (1+t)^M e^{-π(t-T₀)}` uniformly over `K × E`.

Proof: the small-`t` half is the compactness bound on `truncWin K T t₀ A` (with `T` the internal
cut of `kernel_axis_bound`) plus `Aexp_compact_bound`; the large-`t` half is `kernel_axis_bound`,
which needs only compactness. -/
theorem TruncCuspDominator (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) {t₀ A : ℝ}
    (hclean : ∀ (τ : UpperHalfPlane), τ ∈ K → ∀ (s : ℝ) (hs : 0 < s),
      s ∈ Set.Ici (1 : ℝ) \ Set.Ioo (t₀ - A) (t₀ + A) →
      Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis s hs)) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → t ∈ Set.Ici (1 : ℝ) \ Set.Ioo (t₀ - A) (t₀ + A) →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  obtain ⟨Ck, Mk, Tk, hCk, hMk, hTk, hkb⟩ := Work.Asymptotics.kernel_axis_bound ℓ d hd hK
  set T : ℝ := max Tk 1 with hTdef
  have hTpos : 0 < T := lt_max_of_lt_left hTk
  have hTk_le : Tk ≤ T := le_max_left _ _
  -- the small-`t` half on the compact window
  obtain ⟨Cg, hgb⟩ := (isCompact_truncWin hK T t₀ A).exists_bound_of_continuousOn
    (continuousOn_truncWin ℓ d hd (K := K) (T := T) (t₀ := t₀) (A := A)
      (fun τ hτ t ht => by
        rw [axisPt_eq_imagAxis (le_trans (by norm_num) ht.1)]
        exact hclean τ hτ t (lt_of_lt_of_le one_pos (le_trans (by norm_num) ht.1)) ht))
  obtain ⟨Cae, hCae, hae⟩ := Aexp_compact_bound ℓ d hd hK (T := T)
  refine ⟨max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1, max Mk 0, T,
    by positivity, le_max_right _ _, hTpos.le, fun τ t hτ htE => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := htE.1
  rcases le_or_gt t T with htT | htT
  · have hKb : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ Cg :=
      hgb (τ, t) ⟨hτ, ⟨⟨ht1, htT⟩, htE.2⟩⟩
    have hAb : ‖Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ Cae :=
      hae τ hτ t (by rw [abs_of_nonneg (by linarith)]; exact htT)
    have hsum : ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖ ≤ Cg + Cae :=
      le_trans (norm_sub_le _ _) (add_le_add hKb hAb)
    have hw : (1 : ℝ) ≤ 1 + t := by linarith
    have h1' : (1 : ℝ) ≤ (1 + t) ^ max Mk 0 := Real.one_le_rpow hw (le_max_right _ _)
    have h2' : (1 : ℝ) ≤ Real.exp (-(Real.pi * (t - T))) := by
      rw [Real.one_le_exp_iff]; nlinarith [Real.pi_pos]
    have hA0 : (0 : ℝ) ≤ (1 + t) ^ max Mk 0 := Real.rpow_nonneg (by linarith) _
    have hB0 : (0 : ℝ) ≤ Real.exp (-(Real.pi * (t - T))) := (Real.exp_pos _).le
    have hCC : Cg + Cae ≤ max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1 := by
      linarith [le_max_left (Cg + Cae) (Ck * Real.exp (-(Real.pi * T)))]
    have hone : (1 : ℝ) ≤ (1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - T))) := by
      nlinarith [h1', h2', hA0, hB0]
    refine le_trans hsum ?_
    calc Cg + Cae ≤ (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * 1 := by
          rw [mul_one]; exact hCC
      _ ≤ (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1)
            * ((1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - T)))) :=
          mul_le_mul_of_nonneg_left hone (by positivity)
      _ = (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * (1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - T))) := by ring
  · have htT' : T ≤ t := le_of_lt htT
    have hb := hkb τ hτ t (le_trans hTk_le htT')
    have hw : (1 : ℝ) ≤ 1 + t := by linarith
    have hpM : (1 + t) ^ Mk ≤ (1 + t) ^ max Mk 0 :=
      Real.rpow_le_rpow_of_exponent_le hw (le_max_left _ _)
    have hY : (0 : ℝ) ≤ Real.exp (-(Real.pi * (t - T))) := (Real.exp_pos _).le
    have hX : (0 : ℝ) ≤ (1 + t) ^ max Mk 0 := Real.rpow_nonneg (by linarith) _
    have hsplit : Real.exp (-(Real.pi * t))
        = Real.exp (-(Real.pi * T)) * Real.exp (-(Real.pi * (t - T))) := by
      rw [← Real.exp_add]; congr 1; ring
    have hCkC : Ck * Real.exp (-(Real.pi * T)) ≤
        max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1 := by
      linarith [le_max_right (Cg + Cae) (Ck * Real.exp (-(Real.pi * T)))]
    have step2 : Ck * (1 + t) ^ Mk * (Real.exp (-(Real.pi * T))
          * Real.exp (-(Real.pi * (t - T))))
        ≤ Ck * (1 + t) ^ max Mk 0 * (Real.exp (-(Real.pi * T))
          * Real.exp (-(Real.pi * (t - T)))) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpM hCk.le)
        (mul_nonneg (Real.exp_pos _).le hY)
    have step3 : Ck * (1 + t) ^ max Mk 0 * (Real.exp (-(Real.pi * T))
          * Real.exp (-(Real.pi * (t - T))))
        = (Ck * Real.exp (-(Real.pi * T))) * ((1 + t) ^ max Mk 0
          * Real.exp (-(Real.pi * (t - T)))) := by ring
    have step4 : (Ck * Real.exp (-(Real.pi * T))) * ((1 + t) ^ max Mk 0
          * Real.exp (-(Real.pi * (t - T))))
        ≤ (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * ((1 + t) ^ max Mk 0
          * Real.exp (-(Real.pi * (t - T)))) :=
      mul_le_mul_of_nonneg_right hCkC (mul_nonneg hX hY)
    have step5 : (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * ((1 + t) ^ max Mk 0
          * Real.exp (-(Real.pi * (t - T))))
        = (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * (1 + t) ^ max Mk 0
          * Real.exp (-(Real.pi * (t - T))) := by ring
    refine le_trans hb ?_
    calc Ck * (1 + t) ^ Mk * Real.exp (-(Real.pi * t))
        = Ck * (1 + t) ^ Mk * (Real.exp (-(Real.pi * T))
            * Real.exp (-(Real.pi * (t - T)))) := by rw [hsplit]
      _ ≤ Ck * (1 + t) ^ max Mk 0 * (Real.exp (-(Real.pi * T))
            * Real.exp (-(Real.pi * (t - T)))) := step2
      _ = (Ck * Real.exp (-(Real.pi * T))) * ((1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - T)))) := step3
      _ ≤ (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * ((1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - T)))) := step4
      _ = (max (Cg + Cae) (Ck * Real.exp (-(Real.pi * T))) + 1) * (1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - T))) := step5

end Work.LayerCont
