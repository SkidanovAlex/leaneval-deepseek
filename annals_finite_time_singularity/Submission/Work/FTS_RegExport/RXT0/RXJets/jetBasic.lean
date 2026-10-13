import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS_RegExport.RXT0.RXJets.slabDefs
import Submission.Work.FTS_RegExport.RXT.Sys.CoeffCore
import Submission.Work.FTS.LocData.DthIter_Gam_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT0.RXJets.jetBasic` — the elementary `mixed`-jet facts

This file proves the standing "basic jet" conjunction consumed by the coefficient-jet
statements of the `RXJets` chapter:

* the `mixed`-jets (`D_z^kD_θ^l`) of a function constant in `(z,θ)` vanish unless `k = l = 0`
  (and then equal the constant), together with the joint continuity of that family on the
  slab `slb S` when the constant is allowed to depend on `τ`;
* the `C²`-regularity on `(0,π/2)` of the two angular profiles `c2m` and `sin²`;
* the continuity of the angular iterates `D_θ^l b` (`l ≤ 2`) of a `C²` function `b` of `θ`
  alone (via the one-variable operator `dthU φ = sin(2·)·φ'`);
* the joint continuity on `slb S` of the `mixed`-jets of a *radial* datum `c·a(z,τ)` and of a
  *separable* datum `a(z,τ)·b(θ)`, in terms of the joint continuity of the `D_z`-jets of `a`
  and the continuity of the `θ`-iterates of `b`.
-/

noncomputable section

open scoped Real Topology ContDiff
open Set Filter

namespace Work.FTS_RegExport.RXT0.RXJets

set_option autoImplicit false

/-! ## §1 `mixed`-jets of constants -/

/-- The `mixed`-jets of a constant function: only the `(0,0)`-jet survives. -/
theorem jetMixedConst (c : ℝ) (k l : ℕ) :
    Work.Spaces.mixed k l (fun _ _ : ℝ => c) = fun _ _ => if k = 0 ∧ l = 0 then c else 0 := by
  rw [Work.Spaces.mixed, Work.FTS_RegExport.RXT.Sys.DthIter_const_fun c l,
    Work.FTS_RegExport.RXT.Sys.DzIter_const_fun (if l = 0 then c else 0) k]
  funext z θ
  by_cases hk : k = 0 <;> by_cases hl : l = 0 <;> simp [hk, hl]

/-- **Joint continuity of the `mixed`-jets of a `τ`-dependent constant.**  If `c` is continuous
on `[0,S]`, then `p ↦ D_z^kD_θ^l (fun _ _ => c p.2.2)` is continuous on the slab `slb S`. -/
theorem jetContOnMixedConst {S : ℝ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Icc 0 S))
    (k l : ℕ) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun _ _ : ℝ => c p.2.2) p.1 p.2.1) (slb S) := by
  have hfun : (fun p : ℝ × ℝ × ℝ =>
      Work.Spaces.mixed k l (fun _ _ : ℝ => c p.2.2) p.1 p.2.1)
      = fun p : ℝ × ℝ × ℝ => if k = 0 ∧ l = 0 then c p.2.2 else 0 := by
    funext p
    rw [jetMixedConst]
  rw [hfun]
  by_cases h : k = 0 ∧ l = 0
  · have h2 : (fun p : ℝ × ℝ × ℝ => if k = 0 ∧ l = 0 then c p.2.2 else (0 : ℝ))
        = fun p : ℝ × ℝ × ℝ => c p.2.2 := by
      funext p; simp [h]
    rw [h2]
    have h3 : Continuous fun p : ℝ × ℝ × ℝ => p.2.2 := by fun_prop
    have := hc.comp h3.continuousOn mapsTo_slab_τ
    simpa [Function.comp_def] using this
  · have h2 : (fun p : ℝ × ℝ × ℝ => if k = 0 ∧ l = 0 then c p.2.2 else (0 : ℝ))
        = fun _ : ℝ × ℝ × ℝ => (0 : ℝ) := by
      funext p; simp [h]
    rw [h2]
    exact continuousOn_const

/-! ## §2 The two angular profiles are `C²` -/

/-- `c2m` is `C²` on the open angular interval. -/
theorem jetContDiffOnC2m :
    ContDiffOn ℝ 2 Work.Construction.c2m (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  Work.FTS_RegExport.RXT.contDiffOn_c2m

/-- `sin²` is `C²` on the open angular interval. -/
theorem jetContDiffOnSinsq :
    ContDiffOn ℝ 2 (fun θ : ℝ => Real.sin θ ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
  (Real.contDiff_sin.contDiffOn).pow 2

/-! ## §3 Continuity of the angular iterates of a `C²` angular datum

The two-variable operator `D_θ = sin(2θ)·∂_θ` agrees on a function of `θ` alone with the
one-variable operator `Spaces.dthU φ = sin(2·)·φ'` (`Work.FTS.LocData.DthIter_rad_eq`), and
`dthU` lowers the `C^n`-order by one.  Hence for `l ≤ 2` the iterate `D_θ^l b` is continuous
on `(0,π/2)` as soon as `b` is `C²` there. -/

/-- **Continuity of the angular iterates** `D_θ^l b`, `l ≤ 2`, for a `C²` angular datum `b`. -/
theorem jetContOnDthIterAng {b : ℝ → ℝ}
    (hb : ContDiffOn ℝ 2 b (Set.Ioo (0 : ℝ) (Real.pi / 2))) (l : ℕ) (hl : l ≤ 2) :
    ContinuousOn (fun θ => Work.Spaces.DthIter l (fun _ θ' => b θ') 0 θ)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
  have hs : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  have hrepr : (fun θ => Work.Spaces.DthIter l (fun _ θ' => b θ') 0 θ)
      = Work.Spaces.dthU^[l] b :=
    funext fun θ => Work.FTS.LocData.DthIter_rad_eq l b 0 θ
  rw [hrepr]
  have hd1 : ContDiffOn ℝ 1 (deriv b) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hb.deriv_of_isOpen hs (m := (1 : ℕ∞ω)) (by norm_num)
  have hderivb : ContinuousOn (deriv b) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hb.continuousOn_deriv_of_isOpen hs (by norm_num)
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by fun_prop
  interval_cases l
  · show ContinuousOn (Work.Spaces.dthU^[0] b) (Set.Ioo (0 : ℝ) (Real.pi / 2))
    rw [Function.iterate_zero]
    exact hb.continuousOn
  · show ContinuousOn (Work.Spaces.dthU^[1] b) (Set.Ioo (0 : ℝ) (Real.pi / 2))
    rw [Function.iterate_one]
    have h : Work.Spaces.dthU b = fun θ : ℝ => Real.sin (2 * θ) * deriv b θ :=
      funext fun θ => Work.Spaces.dthU_apply b θ
    rw [h]
    exact hsin.mul hderivb
  · show ContinuousOn (Work.Spaces.dthU^[2] b) (Set.Ioo (0 : ℝ) (Real.pi / 2))
    rw [show Work.Spaces.dthU^[2] b = Work.Spaces.dthU (Work.Spaces.dthU^[1] b) from rfl,
      Function.iterate_one]
    have hsin1 : ContDiffOn ℝ 1 (fun θ : ℝ => Real.sin (2 * θ))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      (Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)).contDiffOn
    have hC1 : ContDiffOn ℝ 1 (Work.Spaces.dthU b) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
      have h := hsin1.mul hd1
      refine h.congr fun θ _ => ?_
      rw [Work.Spaces.dthU_apply]
    have hderivdth : ContinuousOn (deriv (Work.Spaces.dthU b))
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      hC1.continuousOn_deriv_of_isOpen hs (by norm_num)
    have h : Work.Spaces.dthU (Work.Spaces.dthU b)
        = fun θ : ℝ => Real.sin (2 * θ) * deriv (Work.Spaces.dthU b) θ :=
      funext fun θ => Work.Spaces.dthU_apply (Work.Spaces.dthU b) θ
    rw [h]
    exact hsin.mul hderivdth

/-! ## §4 The `mixed`-jets of a separable datum -/

/-- The `θ`-iterated operator commutes with multiplication by a `z`-only factor. -/
theorem jetDthIterMulLeftZ (i : ℕ) (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter i (fun z θ => c z * g z θ)
      = fun z θ => c z * Work.Spaces.DthIter i g z θ := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [Work.Spaces.DthIter_succ, ih, Work.Spaces.DthIter_succ]
      funext z θ
      simp only [Work.Spaces.Dth, Work.Spaces.pth]
      rw [deriv_const_mul_field]
      ring

/-- `D_θ^i` of a function of `θ` alone does not depend on the radial variable. -/
theorem jetDthIterZIndep (G : ℝ → ℝ) :
    ∀ (i : ℕ) (z z' θ : ℝ),
      Work.Spaces.DthIter i (fun _ θ' => G θ') z θ
        = Work.Spaces.DthIter i (fun _ θ' => G θ') z' θ := by
  intro i
  induction i with
  | zero => intro z z' θ; rfl
  | succ i ih =>
      intro z z' θ
      show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z θ') θ
        = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z' θ') θ
      rw [show (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z θ')
          = (fun θ' => Work.Spaces.DthIter i (fun _ θ' => G θ') z' θ')
          from funext (fun θ' => ih z z' θ')]

/-- The `z`-iterated operator commutes with multiplication by a `θ`-only factor. -/
theorem jetDzIterMulThetaFactor (j : ℕ) (A : ℝ → ℝ) (B : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter j (fun z θ => A θ * B z θ)
      = fun z θ => A θ * Work.Spaces.DzIter j B z θ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Work.Spaces.DzIter_succ, ih, Work.Spaces.DzIter_succ]
      funext z θ
      simp only [Work.Spaces.Dz, Work.Spaces.pz]
      rw [deriv_const_mul_field]
      ring

/-- **The `mixed`-jets of a separable datum `h(z)·G(θ)` split** into the product of the radial
jet `D_z^j h` (the one-variable operator `DzdIter`) and the angular jet `D_θ^i G`. -/
theorem jetMixedSep (h : ℝ → ℝ) (G : ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => h z * G θ) z θ
      = Work.Elliptic.DzdIter j h z * Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ := by
  rw [Work.Spaces.mixed, jetDthIterMulLeftZ i h (fun _ θ' => G θ')]
  rw [show (fun z θ => h z * Work.Spaces.DthIter i (fun _ θ' => G θ') z θ)
      = fun z θ => Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ * h z from by
    funext z θ
    rw [mul_comm, jetDthIterZIndep G i z 0 θ]]
  rw [jetDzIterMulThetaFactor j (fun θ => Work.Spaces.DthIter i (fun _ θ' => G θ') 0 θ)
    (fun z _ => h z)]
  simp only
  rw [Work.Elliptic.DzIter_rad h j z θ, mul_comm]

/-- **The `mixed`-jets of a radial datum** `h(z)` vanish as soon as one `θ`-derivative is
taken. -/
theorem jetMixedRadial (h : ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z _ => h z) z θ
      = if i = 0 then Work.Elliptic.DzdIter j h z else 0 := by
  by_cases hi : i = 0
  · subst hi
    rw [Work.Spaces.mixed, Work.Spaces.DthIter_zero]
    simp only [↓reduceIte]
    exact Work.Elliptic.DzIter_rad h j z θ
  · have hi1 : 1 ≤ i := by omega
    rw [Work.Spaces.mixed, if_neg hi]
    exact congrFun (congrFun (Work.Elliptic.mixed_rad_eq_zero h hi1) z) θ

/-- Pointwise linearity of `mixed` in a constant factor. -/
theorem jetMixedConstMulPt (c : ℝ) (f : ℝ → ℝ → ℝ) (j i : ℕ) (z θ : ℝ) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ = c * Work.Spaces.mixed j i f z θ := by
  rw [Work.FTS_RegExport.RXT.Sys.coeff_mixed_const_mul]

/-- The `D_z`-jets of the radial datum, as a function on the slab. -/
theorem jetContOnDzdIterProj {S : ℝ} {a : ℝ → ℝ → ℝ} {k : ℕ}
    (ha : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.DzdIter k (fun z => a z p.2) p.1)
      (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) S)) :
    ContinuousOn (fun p : ℝ × ℝ × ℝ =>
      Work.Elliptic.DzdIter k (fun z => a z p.2.2) p.1) (slb S) := by
  have hφ : Continuous (fun p : ℝ × ℝ × ℝ => (p.1, p.2.2)) := by fun_prop
  have := ha.comp hφ.continuousOn mapsTo_slab_zτ
  simpa [Function.comp_def] using this

/-! ## §5 The basic jet conjunction -/

theorem jetBasic :
    (∀ (c : ℝ) (k l : ℕ), Work.Spaces.mixed k l (fun _ _ : ℝ => c)
        = fun _ _ => if k = 0 ∧ l = 0 then c else 0) ∧
    (∀ {S : ℝ} {c : ℝ → ℝ}, ContinuousOn c (Set.Icc 0 S) → ∀ (k l : ℕ),
      ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed k l (fun _ _ : ℝ => c p.2.2) p.1 p.2.1)
        (Work.FTS_RegExport.RXT0.RXJets.slb S)) ∧
    ContDiffOn ℝ 2 Work.Construction.c2m (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
    ContDiffOn ℝ 2 (fun θ : ℝ => Real.sin θ ^ 2) (Set.Ioo (0 : ℝ) (Real.pi / 2)) ∧
    (∀ {b : ℝ → ℝ}, ContDiffOn ℝ 2 b (Set.Ioo (0 : ℝ) (Real.pi / 2)) → ∀ (l : ℕ), l ≤ 2 →
      ContinuousOn (fun θ => Work.Spaces.DthIter l (fun _ θ' => b θ') 0 θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2))) ∧
    (∀ {S c : ℝ} {a : ℝ → ℝ → ℝ} {k l : ℕ},
      ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.DzdIter k (fun z => a z p.2) p.1)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) S) → k + l ≤ 2 →
      ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed k l (fun z θ => c * a z p.2.2) p.1 p.2.1)
        (Work.FTS_RegExport.RXT0.RXJets.slb S)) ∧
    (∀ {S : ℝ} {a : ℝ → ℝ → ℝ} {b : ℝ → ℝ} {k l : ℕ},
      ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.DzdIter k (fun z => a z p.2) p.1)
        (Set.Ioi (0 : ℝ) ×ˢ Set.Icc (0 : ℝ) S) →
      ContinuousOn (fun θ => Work.Spaces.DthIter l (fun _ θ' => b θ') 0 θ)
        (Set.Ioo (0 : ℝ) (Real.pi / 2)) →
      ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.mixed k l (fun z θ => a z p.2.2 * b θ) p.1 p.2.1)
        (Work.FTS_RegExport.RXT0.RXJets.slb S)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact jetMixedConst
  · intro S c hc k l
    exact jetContOnMixedConst hc k l
  · exact jetContDiffOnC2m
  · exact jetContDiffOnSinsq
  · intro b hb l hl
    exact jetContOnDthIterAng hb l hl
  · intro S c a k l ha hkl
    have hfun : (fun p : ℝ × ℝ × ℝ =>
          Work.Spaces.mixed k l (fun z θ => c * a z p.2.2) p.1 p.2.1)
        = fun p : ℝ × ℝ × ℝ =>
          c * (if l = 0 then Work.Elliptic.DzdIter k (fun z => a z p.2.2) p.1 else 0) := by
      funext p
      rw [jetMixedConstMulPt c (fun z θ => a z p.2.2) k l p.1 p.2.1]
      congr 1
      exact jetMixedRadial (fun z => a z p.2.2) k l p.1 p.2.1
    rw [hfun]
    by_cases hl : l = 0
    · have h2 : (fun p : ℝ × ℝ × ℝ =>
          c * (if l = 0 then Work.Elliptic.DzdIter k (fun z => a z p.2.2) p.1 else (0 : ℝ)))
          = fun p : ℝ × ℝ × ℝ =>
            c * Work.Elliptic.DzdIter k (fun z => a z p.2.2) p.1 := by
        funext p; rw [if_pos hl]
      rw [h2]
      exact (jetContOnDzdIterProj ha).const_mul c
    · have h2 : (fun p : ℝ × ℝ × ℝ =>
          c * (if l = 0 then Work.Elliptic.DzdIter k (fun z => a z p.2.2) p.1 else (0 : ℝ)))
          = fun _ : ℝ × ℝ × ℝ => (0 : ℝ) := by
        funext p; rw [if_neg hl]; ring
      rw [h2]
      exact continuousOn_const
  · intro S a b k l ha hb
    have hfun : (fun p : ℝ × ℝ × ℝ =>
          Work.Spaces.mixed k l (fun z θ => a z p.2.2 * b θ) p.1 p.2.1)
        = fun p : ℝ × ℝ × ℝ =>
          Work.Elliptic.DzdIter k (fun z => a z p.2.2) p.1
            * Work.Spaces.DthIter l (fun _ θ' => b θ') 0 p.2.1 := by
      funext p
      exact jetMixedSep (fun z => a z p.2.2) b k l p.1 p.2.1
    rw [hfun]
    have h2 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        Work.Spaces.DthIter l (fun _ θ' => b θ') 0 p.2.1) (slb S) := by
      have hθ : Continuous (fun p : ℝ × ℝ × ℝ => p.2.1) := by fun_prop
      have := hb.comp hθ.continuousOn (mapsTo_slab_θ (S := S))
      simpa [Function.comp_def] using this
    exact (jetContOnDzdIterProj ha).mul h2

end Work.FTS_RegExport.RXT0.RXJets
