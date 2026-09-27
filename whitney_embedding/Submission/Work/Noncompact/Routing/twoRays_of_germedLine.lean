import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.germGlue

namespace Work.Noncompact.Routing

open Set Topology Function
open Work.Noncompact.CompressionTube
open scoped Manifold ContDiff

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (MC n) smoothOrder M] [T2Space M]

/-- If `a : ℝ → ℝ` is differentiable at `x` with injective derivative and `f : ℝ → M` has injective
derivative at `a x`, then the reparametrised curve `s ↦ f (a s)` has injective derivative at `x`. -/
lemma injective_mfderiv_reparam {f : ℝ → M} {a : ℝ → ℝ} {x : ℝ}
    (hfd : MDifferentiableAt MCreal (MC n) f (a x))
    (had : MDifferentiableAt MCreal MCreal a x)
    (hac : Function.Injective (mfderiv MCreal MCreal a x))
    (hf : Function.Injective (mfderiv MCreal (MC n) f (a x))) :
    Function.Injective (mfderiv MCreal (MC n) (fun s : ℝ => f (a s)) x) := by
  have hL : mfderiv MCreal (MC n) (fun s : ℝ => f (a s)) x
      = (mfderiv MCreal (MC n) f (a x)).comp (mfderiv MCreal MCreal a x) := by
    rw [show (fun s : ℝ => f (a s)) = f ∘ a from rfl, mfderiv_comp x hfd had]
  rw [hL, ContinuousLinearMap.coe_comp]
  exact Function.Injective.comp hf hac

/-- The derivative of the translation `s ↦ s + c` of `ℝ` is injective. -/
lemma injective_mfderiv_add_const (c x : ℝ) :
    Function.Injective (mfderiv MCreal MCreal (fun s : ℝ => s + c) x) := by
  have heq : (fun s : ℝ => s + c) =ᶠ[𝓝 x] (fun s : ℝ => s - (-c)) := by
    filter_upwards with s
    ring
  rw [heq.mfderiv_eq]
  exact injective_mfderiv_sub (-c) x

/-- **From a proper embedded line with a two-sided straight germ to the two rays.**
Let `γ : ℝ → M` be a `C^∞` injective proper immersion with `γ 1 = b ∈ W`, whose germ at `b` is the
two-sided straight line `t ↦ c.symm (c b + t • w)` (for `|t| ≤ e`).  Then the two halves of `γ`
realise the two opposite one-sided rays required by the routing target: `r t = γ (t + 1)` and
`r' t = γ (1 - t)`. -/
theorem twoRays_of_germedLine {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder M] [T2Space M]
    {W : Set M} {b : M} {γ : ℝ → M}
    (hγ : ContMDiff Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n)
      Work.Noncompact.CompressionTube.smoothOrder γ)
    (hinj : Function.Injective γ)
    (hprop : IsProperMap γ)
    (himm : ∀ t : ℝ, Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
      (Work.Noncompact.CompressionTube.MC n) γ t))
    (hγ1 : γ 1 = b)
    (hW : Set.range γ ⊆ W)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    {w : EuclideanSpace ℝ (Fin n)} {e : ℝ} (he : 0 < e) (hbc : b ∈ c.source)
    (hgerm : ∀ t : ℝ, |t| ≤ e → γ (1 + t) = c.symm (c b + t • w)) :
    ∃ r r' : ℝ → M,
      ContMDiffOn Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder r (Set.Ici (0:ℝ)) ∧
      ContMDiffOn Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n)
        Work.Noncompact.CompressionTube.smoothOrder r' (Set.Ici (0:ℝ)) ∧
      r 0 = b ∧ r' 0 = b ∧
      Set.InjOn r (Set.Ici (0:ℝ)) ∧ Set.InjOn r' (Set.Ici (0:ℝ)) ∧
      IsProperMap (fun t : Set.Ici (0:ℝ) => r t) ∧
      IsProperMap (fun t : Set.Ici (0:ℝ) => r' t) ∧
      (∀ t : ℝ, 0 < t → Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) r t)) ∧
      (∀ t : ℝ, 0 < t → Function.Injective (mfderiv Work.Noncompact.CompressionTube.MCreal
        (Work.Noncompact.CompressionTube.MC n) r' t)) ∧
      (∀ x : M, x ∈ r '' Set.Ici (0:ℝ) → x ∈ r' '' Set.Ici (0:ℝ) → x = b) ∧
      r '' Set.Ici (0:ℝ) ⊆ W ∧ r' '' Set.Ici (0:ℝ) ⊆ W ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → r t = c.symm (c b + t • w)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → r' t = c.symm (c b + t • (-w))) := by
  classical
  -- the two affine reparametrisations of `ℝ`
  have hshiftS : ContMDiff MCreal MCreal smoothOrder (fun s : ℝ => s + 1) :=
    contMDiff_id.add contMDiff_const
  have hshiftT : ContMDiff MCreal MCreal smoothOrder (fun s : ℝ => 1 - s) :=
    contMDiff_const.sub contMDiff_id
  refine ⟨fun t : ℝ => γ (t + 1), fun t : ℝ => γ (1 - t),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `r` is smooth on `[0,∞)`
    exact (hγ.comp hshiftS).contMDiffOn
  · -- `r'` is smooth on `[0,∞)`
    exact (hγ.comp hshiftT).contMDiffOn
  · -- `r 0 = b`
    show γ (0 + 1) = b
    simpa using hγ1
  · -- `r' 0 = b`
    show γ (1 - 0) = b
    simpa using hγ1
  · -- `r` is injective on `[0,∞)`
    intro s _ t _ hst
    exact add_right_cancel (hinj hst)
  · -- `r'` is injective on `[0,∞)`
    intro s _ t _ hst
    have h := hinj hst
    linarith
  · -- `r` is proper on `[0,∞)`
    have hcomp : IsProperMap (fun s : ℝ => γ (s + 1)) :=
      hprop.comp (Homeomorph.addRight (1:ℝ)).isProperMap
    exact hcomp.restrict isClosed_Ici
  · -- `r'` is proper on `[0,∞)`
    have hcomp : IsProperMap (fun s : ℝ => γ (1 - s)) :=
      hprop.comp ((Homeomorph.neg ℝ).trans (Homeomorph.addLeft (1:ℝ))).isProperMap
    exact hcomp.restrict isClosed_Ici
  · -- `r` is an immersion on `(0,∞)`
    intro t _
    exact injective_mfderiv_reparam (f := γ) (a := fun s : ℝ => s + 1) (x := t)
      (hγ.contMDiffAt.mdifferentiableAt (by simp))
      ((hshiftS.contMDiffAt (x := t)).mdifferentiableAt (by simp))
      (injective_mfderiv_add_const 1 t)
      (himm (t + 1))
  · -- `r'` is an immersion on `(0,∞)`
    intro t _
    exact injective_mfderiv_reparam (f := γ) (a := fun s : ℝ => 1 - s) (x := t)
      (hγ.contMDiffAt.mdifferentiableAt (by simp))
      ((hshiftT.contMDiffAt (x := t)).mdifferentiableAt (by simp))
      (injective_mfderiv_const_sub 1 t)
      (himm (1 - t))
  · -- the two rays meet only at `b`
    intro x hx hx'
    rcases hx with ⟨s, hs, hsx⟩
    rcases hx' with ⟨s', hs', hs'x⟩
    have h1 : γ (s + 1) = x := hsx
    have h2 : γ (1 - s') = x := hs'x
    have h : s + 1 = 1 - s' := by
      apply hinj
      rw [h1, h2]
    have hseq : s = 0 := by
      have hs0 : (0:ℝ) ≤ s := hs
      have hs'0 : (0:ℝ) ≤ s' := hs'
      linarith
    rw [← hsx, hseq]
    show γ (0 + 1) = b
    simpa using hγ1
  · -- `r '' [0,∞) ⊆ W`
    rintro x ⟨t, _, rfl⟩
    exact hW ⟨t + 1, rfl⟩
  · -- `r' '' [0,∞) ⊆ W`
    rintro x ⟨t, _, rfl⟩
    exact hW ⟨1 - t, rfl⟩
  · -- the germ of `r` at `0`
    intro t h0 he'
    have ht : |t| ≤ e := by rwa [abs_of_nonneg h0]
    have h := hgerm t ht
    show γ (t + 1) = c.symm (c b + t • w)
    rw [show t + 1 = 1 + t from by ring]
    exact h
  · -- the germ of `r'` at `0`
    intro t h0 he'
    have ht : |-t| ≤ e := by rw [abs_neg, abs_of_nonneg h0]; exact he'
    have h := hgerm (-t) ht
    show γ (1 - t) = c.symm (c b + t • (-w))
    rw [show (1:ℝ) - t = 1 + (-t) from by ring, h]
    have hw : (-t) • w = t • (-w) := by rw [neg_smul, smul_neg]
    rw [hw]

end

end Work.Noncompact.Routing
