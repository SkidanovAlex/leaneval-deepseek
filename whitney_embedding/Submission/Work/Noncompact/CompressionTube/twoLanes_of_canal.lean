import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation
import Submission.Work.Noncompact.CompressionTube.LaneData
import Submission.Work.Noncompact.CompressionTube.affineReparam
import Submission.Work.Noncompact.CompressionTube.exists_straightened_chart_twoSided
import Submission.Work.Noncompact.CompressionTube.line_of_two_oneSided_rays
import Submission.Work.Noncompact.CompressionTube.immersedArcWithGerm
import Submission.Work.Noncompact.CompressionTube.SpineDefs
import Submission.Work.Noncompact.CompressionTube.LineBuild.nested_canals
import Submission.Work.Noncompact.Routing.junction_facts
import Submission.Work.Noncompact.Routing.seed_shell

/-!
# The two lanes of a canal, from a proper immersed line

This file proves `Work.Noncompact.CompressionTube.twoLanes_of_canal`.  The route is:

* from the nested-canal datum (`exists_nested_canals`) and the spine seeds `q b (lev b + i)` one
  gets two escaping rays `r`, `r'` from `b` inside the canal `W b` with *opposite* straight chart
  germs at `b` (`Work.Noncompact.Routing.twoRays_of_canal`);
* gluing the two rays at `b` gives a globally smooth injective proper immersion
  `γ : ℝ → M` with `γ 1 = b` and `Set.range γ ⊆ W b` (`line_of_two_oneSided_rays`);
* **the last mile** (this file): a proper immersed line through `b` inside `W` produces the two
  lanes.  The pieces of the two lanes are the restrictions of `γ` to the unit intervals on either
  side of `1`, reparametrised affinely (`affineReparam`); the straight germs at the junctions come
  from the two-sided straightening of `γ` (`exists_straightened_chart_twoSided`, exported here as
  `straightenAt` at an arbitrary parameter); the separation of the pieces, the escaping property
  and the injectivity are immediate from the injectivity and properness of `γ`.

That last step is the point of the file: `TwoLanes` asks for *germ-matched immersed pieces*, and a
single globally smooth immersed line supplies them with no further geometry at all.
-/

namespace Work.Noncompact.CompressionTube

open Set Topology Function
open scoped Manifold ContDiff _root_.Topology

noncomputable section

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (MC n) smoothOrder M] [T2Space M] [SecondCountableTopology M]

/-! ## Straightening a globally smooth immersed curve at an arbitrary parameter -/

/-- **Straightening at an arbitrary parameter.**  The two-sided straightening
`exists_straightened_chart_twoSided` is stated at the parameter `1`; applied to the affine
reparametrisation `t ↦ γ (t + (k - 1))` (whose germ at `1` is the germ of `γ` at `k`) it gives the
straightening at any parameter `k` with injective derivative. -/
theorem straightenAt {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    (himm : ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) γ t)) (k : ℝ) :
    ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (w : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e ∧ w ≠ 0 ∧
      c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ γ k ∈ c.source ∧
      ∀ t : ℝ, |t - k| ≤ e → γ t ∈ c.source ∧ c (γ t) = c (γ k) + (t - k) • w := by
  have hαsm : ContMDiff MCreal (MC n) smoothOrder (fun u : ℝ => γ (1 * u + (k - 1))) :=
    contMDiff_comp_affine hγ 1 (k - 1)
  have hαimm : Function.Injective
      (mfderiv MCreal (MC n) (fun u : ℝ => γ (1 * u + (k - 1))) 1) :=
    injective_mfderiv_comp_affine hγ himm (a := 1) (b := k - 1) one_ne_zero 1
  obtain ⟨c, w, e, he, hw, hc, hsrc, hstr⟩ :=
    exists_straightened_chart_twoSided hαsm hαimm
  have hα1 : γ k = (fun u : ℝ => γ (1 * u + (k - 1))) 1 := by
    show γ k = γ (1 * 1 + (k - 1))
    congr 1
    ring
  refine ⟨c, w, e, he, hw, hc, ?_, ?_⟩
  · rw [hα1]
    exact hsrc
  · intro t ht
    have ht' : |(t - k + 1) - 1| ≤ e := by
      rw [show (t - k + 1) - 1 = t - k from by ring]
      exact ht
    obtain ⟨hmem, heq⟩ := hstr (t - k + 1) ht'
    have hg : γ t = (fun u : ℝ => γ (1 * u + (k - 1))) (t - k + 1) := by
      show γ t = γ (1 * (t - k + 1) + (k - 1))
      congr 1
      ring
    rw [show (t - k + 1) - 1 = t - k from by ring] at heq
    refine ⟨?_, ?_⟩
    · rw [hg]
      exact hmem
    · rw [hg, hα1]
      exact heq

lemma gl_line_map_injective {V : EuclideanSpace ℝ (Fin n)} (hV : V ≠ 0) :
    Function.Injective (fun t : ℝ => t • V) := by
  intro a b hab
  have hab' : a • V = b • V := hab
  have h : (a - b) • V = 0 := by rw [sub_smul, hab', sub_self]
  rcases smul_eq_zero.mp h with h1 | h2
  · linarith
  · exact absurd h2 hV

/-- The derivative of `t ↦ t • V` is injective when `V ≠ 0`. -/
lemma gl_smulRight_one_injective {V : EuclideanSpace ℝ (Fin n)} (hV : V ≠ 0) :
    Function.Injective ((1 : ℝ →L[ℝ] ℝ).smulRight V) := by
  intro a b hab
  have hab' : a • V = b • V := by simpa using hab
  have h2 : (a - b) • V = 0 := by rw [sub_smul, hab', sub_self]
  rcases smul_eq_zero.mp h2 with h' | h'
  · exact sub_eq_zero.mp h'
  · exact absurd h' hV

/-- **A straight chart line is smooth and an immersion at its base point.**  For a chart `c` in the
maximal atlas, a base point `p ∈ c.source` and a nonzero direction `V`, the curve
`t ↦ c.symm (c p + t • V)` is `C^∞` on a neighbourhood `T ∋ 0` of `0` and its `mfderiv` at `0` is
injective. -/
theorem gl_chartLine_data {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))}
    (hc : c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M) {p : M} (hp : p ∈ c.source)
    {V : EuclideanSpace ℝ (Fin n)} (hV : V ≠ 0) :
    ∃ T : Set ℝ, IsOpen T ∧ (0:ℝ) ∈ T ∧
      ContMDiffOn MCreal (MC n) smoothOrder (fun t : ℝ => c.symm (c p + t • V)) T ∧
      Function.Injective (mfderiv MCreal (MC n) (fun t : ℝ => c.symm (c p + t • V)) 0) := by
  have hso : smoothOrder ≠ (0 : WithTop ℕ∞) := by simp [smoothOrder]
  have hcs : ContMDiffOn (MC n) (MC n) smoothOrder (⇑c.symm) c.target :=
    contMDiffOn_symm_of_mem_maximalAtlas hc
  obtain ⟨ρ, hρ0, hρ⟩ := Metric.isOpen_iff.mp c.open_target (c p) (c.map_source hp)
  have hVpos : 0 < ‖V‖ := norm_pos_iff.mpr hV
  have hrad : 0 < ρ / (2 * ‖V‖) := by positivity
  have hmemT : ∀ t : ℝ, |t| < ρ / (2 * ‖V‖) → c p + t • V ∈ c.target := by
    intro t ht
    apply hρ
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    have h2 : ρ / (2 * ‖V‖) * (2 * ‖V‖) = ρ := div_mul_cancel₀ ρ (by positivity)
    nlinarith [ht, h2, hVpos]
  have hg : ContMDiff MCreal (MC n) smoothOrder (fun s : ℝ => c p + s • V) := by
    rw [MCreal, MC, smoothOrder, contMDiff_iff_contDiff]
    fun_prop
  refine ⟨Set.Ioo (-(ρ / (2 * ‖V‖))) (ρ / (2 * ‖V‖)), isOpen_Ioo, ⟨by linarith, hrad⟩, ?_, ?_⟩
  · exact hcs.comp hg.contMDiffOn (fun s hs => hmemT s (by rw [abs_lt]; exact hs))
  · have hmem0 : c p + (0:ℝ) • V ∈ c.target := by
      rw [zero_smul, add_zero]; exact c.map_source hp
    have hmdg : MDifferentiableAt MCreal (MC n) (fun s : ℝ => c p + s • V) 0 :=
      hg.contMDiffAt.mdifferentiableAt hso
    have hmdcs : MDifferentiableAt (MC n) (MC n) c.symm ((fun s : ℝ => c p + s • V) 0) :=
      (hcs.contMDiffAt (c.open_target.mem_nhds hmem0)).mdifferentiableAt hso
    have hcomp : mfderiv MCreal (MC n) (c.symm ∘ (fun s : ℝ => c p + s • V)) 0
        = (mfderiv (MC n) (MC n) c.symm ((fun s : ℝ => c p + s • V) 0)).comp
          (mfderiv MCreal (MC n) (fun s : ℝ => c p + s • V) 0) :=
      mfderiv_comp (I := MCreal) (I' := MC n) (I'' := MC n)
        (f := fun s : ℝ => c p + s • V) (g := c.symm) 0 hmdcs hmdg
    have hinj_symm : Function.Injective (mfderiv (MC n) (MC n) c.symm
        ((fun s : ℝ => c p + s • V) 0)) := by
      let Φ : PartialDiffeomorph (MC n) (MC n) (EuclideanSpace ℝ (Fin n)) M smoothOrder :=
        { toPartialEquiv := c.symm.toPartialEquiv
          open_source := c.open_target
          open_target := c.open_source
          contMDiffOn_toFun := hcs
          contMDiffOn_invFun := contMDiffOn_of_mem_maximalAtlas hc }
      have hIso : IsLocalDiffeomorphAt (MC n) (MC n) smoothOrder (⇑c.symm)
          ((fun s : ℝ => c p + s • V) 0) :=
        PartialDiffeomorph.isLocalDiffeomorphAt _ _ _ Φ hmem0
      rw [← IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv_coe hIso hso]
      exact (IsLocalDiffeomorphAt.mfderivToContinuousLinearEquiv hIso hso).injective
    have hinj_g : Function.Injective (mfderiv MCreal (MC n) (fun s : ℝ => c p + s • V) 0) := by
      have h_eq : mfderiv MCreal (MC n) (fun s : ℝ => c p + s • V) 0
          = fderiv ℝ (fun s : ℝ => c p + s • V) 0 := mfderiv_eq_fderiv
      have hfd : fderiv ℝ (fun s : ℝ => c p + s • V) 0 = (1 : ℝ →L[ℝ] ℝ).smulRight V := by
        rw [fderiv_const_add, fderiv_smul_const differentiableAt_id]
        show (fderiv ℝ id 0).smulRight V = (1 : ℝ →L[ℝ] ℝ).smulRight V
        rw [fderiv_id]
        rfl
      rw [h_eq, hfd]
      exact gl_smulRight_one_injective hV
    change Function.Injective (mfderiv MCreal (MC n) (c.symm ∘ (fun s : ℝ => c p + s • V)) 0)
    rw [hcomp]
    intro a b hab
    exact hinj_g (hinj_symm hab)

/-- **The gluing lemma.**  Two escaping rays `r`, `r'` from a common base point `b`, whose ranges
meet only at `b` and which agree on `[0,e]` with the *same* straight chart line through `b` in the
*opposite* directions, glue into an injective proper immersion `γ` of `ℝ` with `γ 1 = b`.

Only the behaviour of the rays on `[0,∞)` is used: `γ t = r' (1 - t)` for `t ≤ 1` and
`γ t = r (t - 1)` for `t ≥ 1`.  This is
`CompressionTube.line_of_two_oneSided_rays` with the two immersion hypotheses relaxed from `0 ≤ t`
to `0 < t` (they are only ever used at strictly positive arguments). -/
theorem line_of_two_germed_rays_pos {b : M} {r r' : ℝ → M}
    (hr : ContMDiffOn MCreal (MC n) smoothOrder r (Set.Ici (0:ℝ)))
    (hr' : ContMDiffOn MCreal (MC n) smoothOrder r' (Set.Ici (0:ℝ)))
    (hrb : r 0 = b) (hr'b : r' 0 = b)
    (hrinj : Set.InjOn r (Set.Ici (0:ℝ))) (hr'inj : Set.InjOn r' (Set.Ici (0:ℝ)))
    (hmeet : ∀ x : M, x ∈ r '' Set.Ici (0:ℝ) → x ∈ r' '' Set.Ici (0:ℝ) → x = b)
    (hrp : IsProperMap (fun t : Set.Ici (0:ℝ) => r t))
    (hr'p : IsProperMap (fun t : Set.Ici (0:ℝ) => r' t))
    (himm : ∀ t : ℝ, 0 < t → Function.Injective (mfderiv MCreal (MC n) r t))
    (himm' : ∀ t : ℝ, 0 < t → Function.Injective (mfderiv MCreal (MC n) r' t))
    (hger : ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
        (w : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e ∧ w ≠ 0 ∧
      c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ b ∈ c.source ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → r t = c.symm (c b + t • w)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ e → r' t = c.symm (c b + t • (-w)))) :
    ∃ γ : ℝ → M, ContMDiff MCreal (MC n) smoothOrder γ ∧ Function.Injective γ ∧
      IsProperMap γ ∧ (∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) γ t)) ∧
      γ 1 = b ∧ Set.range γ ⊆ r '' Set.Ici (0:ℝ) ∪ r' '' Set.Ici (0:ℝ) := by
  classical
  obtain ⟨c, w, e, he, hw, hc, hbc, hrg, hr'g⟩ := hger
  set γ : ℝ → M := fun t => if t ≤ 1 then r' (1 - t) else r (t - 1) with hγdef
  have hγeq : ∀ t : ℝ, γ t = (if t ≤ 1 then r' (1 - t) else r (t - 1)) := fun t => rfl
  have hγ1 : γ 1 = b := by rw [hγeq]; simp only [le_refl, if_true, sub_self]; exact hr'b
  have hleft : ∀ u : ℝ, 1 - e ≤ u → u ≤ 1 → r' (1 - u) = c.symm (c b + (u - 1) • w) := by
    intro u h1 h2
    have h0 : (0:ℝ) ≤ 1 - u := by linarith
    have h3 : 1 - u ≤ e := by linarith
    rw [hr'g (1 - u) h0 h3]
    have : (1 - u) • (-w) = (u - 1) • w := by
      rw [smul_neg, ← neg_smul]
      congr 1
      ring
    rw [this]
  have hright : ∀ u : ℝ, 1 ≤ u → u ≤ 1 + e → r (u - 1) = c.symm (c b + (u - 1) • w) := by
    intro u h1 h2
    exact hrg (u - 1) (by linarith) (by linarith)
  -- smoothness
  have hsm : ContMDiff MCreal (MC n) smoothOrder γ := by
    intro t
    by_cases ht : t < 1
    · have heq : γ =ᶠ[𝓝 t] (fun s : ℝ => r' (1 - s)) := by
        filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
        rw [hγeq]; exact if_pos (le_of_lt hs)
      refine ((hr'.contMDiffAt (Ici_mem_nhds (by linarith : (0:ℝ) < 1 - t))).comp t
        (contMDiff_const.sub contMDiff_id).contMDiffAt).congr_of_eventuallyEq heq
    · by_cases ht1 : t = 1
      · subst ht1
        have hglue := contMDiffAt_glue_same_germ (n := n) (c := c) hc hbc (w := w)
          (A := fun s : ℝ => r' (1 - s)) (B := fun s : ℝ => r (s - 1)) (τ := 1) (δ := e) he
          (fun u h1 h2 => hleft u h1 h2) (fun u h1 h2 => hright u h1 h2)
        refine hglue.congr_of_eventuallyEq ?_
        filter_upwards with s
        rw [hγeq]
      · have ht' : 1 < t := lt_of_le_of_ne (not_lt.mp ht) (Ne.symm ht1)
        have heq : γ =ᶠ[𝓝 t] (fun s : ℝ => r (s - 1)) := by
          filter_upwards [isOpen_Ioi.mem_nhds ht'] with s hs
          rw [hγeq]; exact if_neg (not_le.mpr hs)
        refine ((hr.contMDiffAt (Ici_mem_nhds (by linarith : (0:ℝ) < t - 1))).comp t
          (contMDiff_id.sub contMDiff_const).contMDiffAt).congr_of_eventuallyEq heq
  -- injectivity
  have hinj : Function.Injective γ := by
    intro s t hst
    by_cases hs1 : s ≤ 1
    · have hm1 : (1 - s) ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
      by_cases ht1 : t ≤ 1
      · have hm2 : (1 - t) ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
        rw [hγeq, if_pos hs1, hγeq, if_pos ht1] at hst
        have := hr'inj hm1 hm2 hst
        linarith
      · exfalso
        rw [hγeq, if_pos hs1, hγeq, if_neg ht1] at hst
        have hm3 : (t - 1) ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
        have hb : r' (1 - s) = b :=
          hmeet (r' (1 - s)) ⟨t - 1, hm3, hst.symm⟩ ⟨1 - s, hm1, rfl⟩
        have h0 : (0:ℝ) ∈ Set.Ici (0:ℝ) := by simp
        have h1 : 1 - s = 0 := hr'inj hm1 h0 (by rw [hb, hr'b])
        have h2 : r (t - 1) = b := by rw [← hst, hb]
        have h3 : t - 1 = 0 := hrinj hm3 h0 (by rw [h2, hrb])
        linarith
    · have hs1' : 1 < s := lt_of_not_ge hs1
      have hm1 : (s - 1) ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
      by_cases ht1 : t ≤ 1
      · exfalso
        rw [hγeq, if_neg hs1, hγeq, if_pos ht1] at hst
        have hm2 : (1 - t) ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
        have hb : r (s - 1) = b :=
          hmeet (r (s - 1)) ⟨s - 1, hm1, rfl⟩ ⟨1 - t, hm2, hst.symm⟩
        have h0 : (0:ℝ) ∈ Set.Ici (0:ℝ) := by simp
        have h3 : s - 1 = 0 := hrinj hm1 h0 (by rw [hb, hrb])
        have h1 : r' (1 - t) = b := by rw [← hst, hb]
        have h2 : 1 - t = 0 := hr'inj hm2 h0 (by rw [h1, hr'b])
        linarith
      · have hm2 : (t - 1) ∈ Set.Ici (0:ℝ) := by simp only [Set.mem_Ici]; linarith
        rw [hγeq, if_neg hs1, hγeq, if_neg ht1] at hst
        have := hrinj hm1 hm2 hst
        linarith
  -- the straight chart line through `b` in direction `w` is a smooth immersion at `0`
  obtain ⟨T, hTopen, hT0, hTsm, hTimm⟩ := gl_chartLine_data (n := n) hc hbc hw
  -- reparametrisation lemma for the derivative
  have hReparam : ∀ (f : ℝ → M) (a : ℝ → ℝ) (x : ℝ),
      MDifferentiableAt MCreal (MC n) f (a x) → MDifferentiableAt MCreal MCreal a x →
      Function.Injective (mfderiv MCreal MCreal a x) →
      Function.Injective (mfderiv MCreal (MC n) f (a x)) →
      Function.Injective (mfderiv MCreal (MC n) (fun s : ℝ => f (a s)) x) := by
    intro f a x hfd had hac hf
    have hL : mfderiv MCreal (MC n) (fun s : ℝ => f (a s)) x
        = (mfderiv MCreal (MC n) f (a x)).comp (mfderiv MCreal MCreal a x) := by
      rw [show (fun s : ℝ => f (a s)) = f ∘ a from rfl, mfderiv_comp x hfd had]
    rw [hL, ContinuousLinearMap.coe_comp]
    exact Function.Injective.comp hf hac
  -- immersion
  have himmγ : ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) γ t) := by
    intro t
    by_cases ht : t < 1
    · have heq : γ =ᶠ[𝓝 t] (fun s : ℝ => r' (1 - s)) := by
        filter_upwards [isOpen_Iio.mem_nhds ht] with s hs
        rw [hγeq]; exact if_pos (le_of_lt hs)
      rw [heq.mfderiv_eq]
      exact hReparam r' (fun s : ℝ => 1 - s) t
        ((hr'.contMDiffAt (n := ∞) (Ici_mem_nhds (by linarith : (0:ℝ) < 1 - t))).mdifferentiableAt (by simp))
        (((contMDiff_const.sub contMDiff_id).contMDiffAt (n := ∞)).mdifferentiableAt (by simp))
        (injective_mfderiv_const_sub 1 t)
        (himm' (1 - t) (by linarith))
    · by_cases ht1 : t = 1
      · subst ht1
        have heq : γ =ᶠ[𝓝 (1:ℝ)] (fun s : ℝ => c.symm (c b + (s - 1) • w)) := by
          have hδ : (0:ℝ) < min e 1 := lt_min he one_pos
          filter_upwards [isOpen_Ioo.mem_nhds (show (1:ℝ) ∈ Set.Ioo (1 - min e 1) (1 + min e 1)
            from ⟨by linarith, by linarith⟩)] with s hs
          rw [hγeq]
          by_cases hs1 : s ≤ 1
          · rw [if_pos hs1]
            exact hleft s (by have := min_le_left e 1; linarith [hs.1, this]) hs1
          · rw [if_neg hs1]
            exact hright s (le_of_lt (lt_of_not_ge hs1))
              (by have := min_le_left e 1; linarith [hs.2, this])
        rw [heq.mfderiv_eq]
        exact hReparam (fun u : ℝ => c.symm (c b + u • w)) (fun s : ℝ => s - 1) 1
          (by rw [show (1:ℝ) - 1 = 0 from by norm_num]
              exact (hTsm.contMDiffAt (hTopen.mem_nhds hT0)).mdifferentiableAt (by simp))
          (((contMDiff_id.sub contMDiff_const).contMDiffAt (n := ∞)).mdifferentiableAt (by simp))
          (injective_mfderiv_sub 1 1)
          (by rw [show (1:ℝ) - 1 = 0 from by norm_num]; exact hTimm)
      · have ht' : 1 < t := lt_of_le_of_ne (not_lt.mp ht) (Ne.symm ht1)
        have heq : γ =ᶠ[𝓝 t] (fun s : ℝ => r (s - 1)) := by
          filter_upwards [isOpen_Ioi.mem_nhds ht'] with s hs
          rw [hγeq]; exact if_neg (not_le.mpr hs)
        rw [heq.mfderiv_eq]
        exact hReparam r (fun s : ℝ => s - 1) t
          ((hr.contMDiffAt (n := ∞) (Ici_mem_nhds (by linarith : (0:ℝ) < t - 1))).mdifferentiableAt (by simp))
          (((contMDiff_id.sub contMDiff_const).contMDiffAt (n := ∞)).mdifferentiableAt (by simp))
          (injective_mfderiv_sub 1 t)
          (himm (t - 1) (by linarith))
  -- properness
  have hprop : IsProperMap γ := by
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hsm.continuous, ?_⟩
    intro K hK
    have hA : IsCompact ((fun t : Set.Ici (0:ℝ) => r t) ⁻¹' K) := hrp.isCompact_preimage hK
    have hB : IsCompact ((fun t : Set.Ici (0:ℝ) => r' t) ⁻¹' K) := hr'p.isCompact_preimage hK
    have hsub : γ ⁻¹' K ⊆
        (fun u : ℝ => 1 + u) '' (Subtype.val '' ((fun t : Set.Ici (0:ℝ) => r t) ⁻¹' K)) ∪
        (fun u : ℝ => 1 - u) '' (Subtype.val '' ((fun t : Set.Ici (0:ℝ) => r' t) ⁻¹' K)) := by
      intro t ht
      simp only [mem_preimage] at ht
      rw [hγeq] at ht
      by_cases ht1 : t ≤ 1
      · rw [if_pos ht1] at ht
        exact Or.inr ⟨1 - t, ⟨⟨1 - t, by simp only [Set.mem_Ici]; linarith⟩, by simpa using ht, rfl⟩, by ring⟩
      · rw [if_neg ht1] at ht
        exact Or.inl ⟨t - 1, ⟨⟨t - 1, by simp only [Set.mem_Ici]; linarith⟩, by simpa using ht, rfl⟩, by ring⟩
    refine IsCompact.of_isClosed_subset ?_ (hK.isClosed.preimage hsm.continuous) hsub
    exact ((hA.image continuous_subtype_val).image (continuous_const.add continuous_id)).union
      ((hB.image continuous_subtype_val).image (continuous_const.sub continuous_id))
  refine ⟨γ, hsm, hinj, hprop, himmγ, hγ1, ?_⟩
  intro y hy
  rw [Set.mem_range] at hy
  obtain ⟨t, rfl⟩ := hy
  rw [hγeq]
  by_cases ht1 : t ≤ 1
  · rw [if_pos ht1]
    exact Or.inr ⟨1 - t, by simp only [Set.mem_Ici]; linarith, rfl⟩
  · rw [if_neg ht1]
    exact Or.inl ⟨t - 1, by simp only [Set.mem_Ici]; linarith, rfl⟩


def piecePos (γ : ℝ → M) (i : ℕ) : ℝ → M := fun t => γ (1 * t + (1 + (i : ℝ)))

/-- the negative piece `i`: `γ` on `[1-i-1, 1-i]` traversed backwards. -/
def pieceNeg (γ : ℝ → M) (i : ℕ) : ℝ → M := fun t => γ ((-1) * t + (1 - (i : ℝ)))

lemma piecePos_zero (γ : ℝ → M) (i : ℕ) : piecePos γ i 0 = γ (1 + (i:ℝ)) := by
  simp [piecePos]

lemma piecePos_one (γ : ℝ → M) (i : ℕ) : piecePos γ i 1 = γ (2 + (i:ℝ)) := by
  simp only [piecePos, mul_one]
  congr 1
  ring

lemma pieceNeg_zero (γ : ℝ → M) (i : ℕ) : pieceNeg γ i 0 = γ (1 - (i:ℝ)) := by
  simp [pieceNeg]

lemma pieceNeg_one (γ : ℝ → M) (i : ℕ) : pieceNeg γ i 1 = γ (-(i:ℝ)) := by
  simp only [pieceNeg, mul_one, mul_neg, one_mul]
  congr 1
  ring

lemma contMDiff_piecePos {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ) (i : ℕ) :
    ContMDiff MCreal (MC n) smoothOrder (piecePos γ i) :=
  contMDiff_comp_affine hγ 1 (1 + (i:ℝ))

lemma contMDiff_pieceNeg {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ) (i : ℕ) :
    ContMDiff MCreal (MC n) smoothOrder (pieceNeg γ i) :=
  contMDiff_comp_affine hγ (-1) (1 - (i:ℝ))

lemma imm_piecePos {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    (himm : ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) γ t)) (i : ℕ) :
    ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) (piecePos γ i) t) :=
  injective_mfderiv_comp_affine hγ himm (a := 1) (b := 1 + (i:ℝ)) one_ne_zero

lemma imm_pieceNeg {γ : ℝ → M} (hγ : ContMDiff MCreal (MC n) smoothOrder γ)
    (himm : ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) γ t)) (i : ℕ) :
    ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) (pieceNeg γ i) t) :=
  injective_mfderiv_comp_affine hγ himm (a := -1) (b := 1 - (i:ℝ)) (by norm_num)

lemma injOn_piecePos {γ : ℝ → M} (hγinj : Function.Injective γ) (i : ℕ) :
    Set.InjOn (piecePos γ i) (Set.Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  have h : 1 * x + (1 + (i:ℝ)) = 1 * y + (1 + (i:ℝ)) := hγinj hxy
  linarith

lemma injOn_pieceNeg {γ : ℝ → M} (hγinj : Function.Injective γ) (i : ℕ) :
    Set.InjOn (pieceNeg γ i) (Set.Icc (0:ℝ) 1) := by
  intro x hx y hy hxy
  have h : (-1) * x + (1 - (i:ℝ)) = (-1) * y + (1 - (i:ℝ)) := hγinj hxy
  linarith

/-- Extent arithmetic helper: `min e 1 ≤ e` and both windows fit. -/
lemma min_le' {e : ℝ} (he : 0 < e) : 0 < min e 1 := lt_min he one_pos

variable {b : M} {W : Set M}

/-! ### The germ forms of the pieces -/

lemma piecePos_form_out {γ : ℝ → M} (i : ℕ)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {w : EuclideanSpace ℝ (Fin n)}
    {e : ℝ}
    (hstr : ∀ t : ℝ, |t - (2 + (i:ℝ))| ≤ e →
      γ t ∈ c.source ∧ c (γ t) = c (γ (2 + (i:ℝ))) + (t - (2 + (i:ℝ))) • w) :
    ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 → piecePos γ i t = c.symm (c (piecePos γ i 1) + (t - 1) • w) := by
  intro t ht1 ht2
  have hcoef : (1 * t + (1 + (i:ℝ))) - (2 + (i:ℝ)) = t - 1 := by ring
  have hs : |(1 * t + (1 + (i:ℝ))) - (2 + (i:ℝ))| ≤ e := by
    rw [hcoef, abs_of_nonpos (by linarith)]
    linarith
  obtain ⟨hmem, hc⟩ := hstr _ hs
  calc piecePos γ i t = γ (1 * t + (1 + (i:ℝ))) := rfl
    _ = c.symm (c (γ (1 * t + (1 + (i:ℝ))))) := (c.left_inv hmem).symm
    _ = c.symm (c (γ (2 + (i:ℝ))) + (t - 1) • w) := by rw [hc, hcoef]
    _ = c.symm (c (piecePos γ i 1) + (t - 1) • w) := by rw [piecePos_one]

lemma piecePos_form_in {γ : ℝ → M} (i : ℕ)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {w : EuclideanSpace ℝ (Fin n)}
    {e : ℝ}
    (hstr : ∀ t : ℝ, |t - (2 + (i:ℝ))| ≤ e →
      γ t ∈ c.source ∧ c (γ t) = c (γ (2 + (i:ℝ))) + (t - (2 + (i:ℝ))) • w) :
    ∀ u : ℝ, 0 ≤ u → u ≤ e → piecePos γ (i+1) u = c.symm (c (piecePos γ (i+1) 0) + u • w) := by
  intro u hu0 hue
  have hcoef : (1 * u + (1 + ((i+1:ℕ):ℝ))) - (2 + (i:ℝ)) = u := by push_cast; ring
  have h0 : piecePos γ (i+1) 0 = γ (2 + (i:ℝ)) := by
    rw [piecePos_zero]
    congr 1
    push_cast
    ring
  have hs : |(1 * u + (1 + ((i+1:ℕ):ℝ))) - (2 + (i:ℝ))| ≤ e := by
    rw [hcoef, abs_of_nonneg hu0]
    exact hue
  obtain ⟨hmem, hc⟩ := hstr _ hs
  calc piecePos γ (i+1) u = γ (1 * u + (1 + ((i+1:ℕ):ℝ))) := rfl
    _ = c.symm (c (γ (1 * u + (1 + ((i+1:ℕ):ℝ))))) := (c.left_inv hmem).symm
    _ = c.symm (c (γ (2 + (i:ℝ))) + u • w) := by rw [hc, hcoef]
    _ = c.symm (c (piecePos γ (i+1) 0) + u • w) := by rw [h0]

lemma pieceNeg_form_out {γ : ℝ → M} (i : ℕ)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {w : EuclideanSpace ℝ (Fin n)}
    {e : ℝ}
    (hstr : ∀ t : ℝ, |t - (-(i:ℝ))| ≤ e →
      γ t ∈ c.source ∧ c (γ t) = c (γ (-(i:ℝ))) + (t - (-(i:ℝ))) • w) :
    ∀ t : ℝ, 1 - e ≤ t → t ≤ 1 →
      pieceNeg γ i t = c.symm (c (pieceNeg γ i 1) + (t - 1) • (-w)) := by
  intro t ht1 ht2
  have hcoef : ((-1) * t + (1 - (i:ℝ))) - (-(i:ℝ)) = 1 - t := by ring
  have hs : |((-1) * t + (1 - (i:ℝ))) - (-(i:ℝ))| ≤ e := by
    rw [hcoef, abs_of_nonneg (by linarith)]
    linarith
  obtain ⟨hmem, hc⟩ := hstr _ hs
  calc pieceNeg γ i t = γ ((-1) * t + (1 - (i:ℝ))) := rfl
    _ = c.symm (c (γ ((-1) * t + (1 - (i:ℝ))))) := (c.left_inv hmem).symm
    _ = c.symm (c (γ (-(i:ℝ))) + (1 - t) • w) := by rw [hc, hcoef]
    _ = c.symm (c (γ (-(i:ℝ))) + (t - 1) • (-w)) := by
      rw [show (1 - t) • w = (t - 1) • (-w) from by
        rw [show (1 - t) = -(t - 1) from by ring, neg_smul, smul_neg]]
    _ = c.symm (c (pieceNeg γ i 1) + (t - 1) • (-w)) := by rw [pieceNeg_one]

lemma pieceNeg_form_in {γ : ℝ → M} (i : ℕ)
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {w : EuclideanSpace ℝ (Fin n)}
    {e : ℝ}
    (hstr : ∀ t : ℝ, |t - (-(i:ℝ))| ≤ e →
      γ t ∈ c.source ∧ c (γ t) = c (γ (-(i:ℝ))) + (t - (-(i:ℝ))) • w) :
    ∀ u : ℝ, 0 ≤ u → u ≤ e →
      pieceNeg γ (i+1) u = c.symm (c (pieceNeg γ (i+1) 0) + u • (-w)) := by
  intro u hu0 hue
  have hcoef : ((-1) * u + (1 - ((i+1:ℕ):ℝ))) - (-(i:ℝ)) = -u := by push_cast; ring
  have h0 : pieceNeg γ (i+1) 0 = γ (-(i:ℝ)) := by
    rw [pieceNeg_zero]
    congr 1
    push_cast
    ring
  have hs : |((-1) * u + (1 - ((i+1:ℕ):ℝ))) - (-(i:ℝ))| ≤ e := by
    rw [hcoef, abs_neg, abs_of_nonneg hu0]
    exact hue
  obtain ⟨hmem, hc⟩ := hstr _ hs
  calc pieceNeg γ (i+1) u = γ ((-1) * u + (1 - ((i+1:ℕ):ℝ))) := rfl
    _ = c.symm (c (γ ((-1) * u + (1 - ((i+1:ℕ):ℝ))))) := (c.left_inv hmem).symm
    _ = c.symm (c (γ (-(i:ℝ))) + (-u) • w) := by rw [hc, hcoef]
    _ = c.symm (c (γ (-(i:ℝ))) + u • (-w)) := by rw [neg_smul, smul_neg]
    _ = c.symm (c (pieceNeg γ (i+1) 0) + u • (-w)) := by rw [h0]

/-! ### The base germ forms -/

lemma piecePos_base {γ : ℝ → M} {b : M}
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {w : EuclideanSpace ℝ (Fin n)}
    {e : ℝ} (hstr : ∀ t : ℝ, |t - 1| ≤ e → γ t ∈ c.source ∧ c (γ t) = c b + (t - 1) • w) :
    ∀ u : ℝ, 0 ≤ u → u ≤ e → piecePos γ 0 u = c.symm (c b + u • w) := by
  intro u hu0 hue
  have hcoef : (1 * u + (1 + ((0:ℕ):ℝ))) - 1 = u := by push_cast; ring
  have hs : |(1 * u + (1 + ((0:ℕ):ℝ))) - 1| ≤ e := by
    rw [hcoef, abs_of_nonneg hu0]
    exact hue
  obtain ⟨hmem, hc⟩ := hstr _ hs
  calc piecePos γ 0 u = γ (1 * u + (1 + ((0:ℕ):ℝ))) := rfl
    _ = c.symm (c (γ (1 * u + (1 + ((0:ℕ):ℝ))))) := (c.left_inv hmem).symm
    _ = c.symm (c b + u • w) := by rw [hc, hcoef]

lemma pieceNeg_base {γ : ℝ → M} {b : M}
    {c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n))} {w : EuclideanSpace ℝ (Fin n)}
    {e : ℝ} (hstr : ∀ t : ℝ, |t - 1| ≤ e → γ t ∈ c.source ∧ c (γ t) = c b + (t - 1) • w) :
    ∀ u : ℝ, 0 ≤ u → u ≤ e → pieceNeg γ 0 u = c.symm (c b + u • (-w)) := by
  intro u hu0 hue
  have hcoef : (1 - u) - 1 = -u := by ring
  have hs : |(1 - u) - 1| ≤ e := by
    rw [hcoef, abs_neg, abs_of_nonneg hu0]
    exact hue
  obtain ⟨hmem, hc⟩ := hstr _ hs
  calc pieceNeg γ 0 u = γ ((-1) * u + (1 - ((0:ℕ):ℝ))) := rfl
    _ = γ (1 - u) := by rw [show (-1) * u + (1 - ((0:ℕ):ℝ)) = 1 - u from by push_cast; ring]
    _ = c.symm (c (γ (1 - u))) := (c.left_inv hmem).symm
    _ = c.symm (c b + (-u) • w) := by rw [hc, hcoef]
    _ = c.symm (c b + u • (-w)) := by rw [neg_smul, smul_neg]

/-- **Two lanes from a proper immersed line through `b`.** -/
theorem twoLanes_of_line (hbW : b ∈ W) {γ : ℝ → M}
    (hγsm : ContMDiff MCreal (MC n) smoothOrder γ) (hγinj : Function.Injective γ)
    (hγprop : IsProperMap γ)
    (himm : ∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) γ t))
    (hγ1 : γ 1 = b) (hγrange : Set.range γ ⊆ W) :
    Nonempty (TwoLanes n M b W) := by
  classical
  -- ## the base straightening at `b = γ 1`
  obtain ⟨c₀, w₀, e₀, he₀, hw₀, hc₀, -, hstr₀raw⟩ := straightenAt hγsm himm 1
  have hstr₀ : ∀ t : ℝ, |t - 1| ≤ e₀ →
      γ t ∈ c₀.source ∧ c₀ (γ t) = c₀ b + (t - 1) • w₀ := by
    intro t ht
    have h := hstr₀raw t ht
    rwa [hγ1] at h
  -- ## the straightenings at the junctions of the two lanes
  have hP : ∀ i : ℕ, ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (w : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e ∧ w ≠ 0 ∧
      c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ γ (2 + (i:ℝ)) ∈ c.source ∧
      ∀ t : ℝ, |t - (2 + (i:ℝ))| ≤ e →
        γ t ∈ c.source ∧ c (γ t) = c (γ (2 + (i:ℝ))) + (t - (2 + (i:ℝ))) • w := by
    intro i
    exact straightenAt hγsm himm (2 + (i:ℝ))
  choose cP wP eP heP hwP hcP hsrcP hstrP using hP
  have hM : ∀ i : ℕ, ∃ (c : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n)))
      (w : EuclideanSpace ℝ (Fin n)) (e : ℝ), 0 < e ∧ w ≠ 0 ∧
      c ∈ IsManifold.maximalAtlas (MC n) smoothOrder M ∧ γ (-(i:ℝ)) ∈ c.source ∧
      ∀ t : ℝ, |t - (-(i:ℝ))| ≤ e →
        γ t ∈ c.source ∧ c (γ t) = c (γ (-(i:ℝ))) + (t - (-(i:ℝ))) • w := by
    intro i
    exact straightenAt hγsm himm (-(i:ℝ))
  choose cM wM eM heM hwM hcM hsrcM hstrM using hM
  -- ## the escape bound from properness
  have hbound : ∀ K : Set M, IsCompact K → ∃ R : ℝ, 0 ≤ R ∧ ∀ t : ℝ, γ t ∈ K → |t| ≤ R := by
    intro K hK
    have hcomp : IsCompact (γ ⁻¹' K) := hγprop.isCompact_preimage hK
    rcases (γ ⁻¹' K).eq_empty_or_nonempty with hem | ⟨t₀, ht₀⟩
    · exact ⟨0, le_rfl, fun t ht => absurd (hem ▸ ht) (Set.notMem_empty t)⟩
    · obtain ⟨C, hC⟩ := Metric.isBounded_iff.mp hcomp.isBounded
      have hC0 : 0 ≤ C := le_trans dist_nonneg (hC ht₀ ht₀)
      refine ⟨C + |t₀|, by positivity, fun t ht => ?_⟩
      have h1 : dist t t₀ ≤ C := hC ht ht₀
      rw [Real.dist_eq] at h1
      have h2 : |t| ≤ |t - t₀| + |t₀| := by
        have h := abs_sub_abs_le_abs_sub t t₀
        linarith
      linarith
  -- ## the positive lane
  let hLp : Lane n M :=
    { P := piecePos γ
      hsm := fun i => contMDiff_piecePos hγsm i
      himm := fun i t _ => imm_piecePos hγsm himm i t
      hinj := fun i => injOn_piecePos hγinj i
      hjun := by
        intro i
        rw [piecePos_one, piecePos_zero]
        congr 1
        push_cast
        ring
      hgerm := by
        intro i
        refine ⟨cP i, wP i, eP i, heP i, hcP i, ?_, ?_, ?_⟩
        · rw [piecePos_one]
          exact hsrcP i
        · intro t ht1 ht2
          exact piecePos_form_out i (hstrP i) t ht1 ht2
        · intro t ht1 ht2
          exact piecePos_form_in i (hstrP i) t ht1 ht2
      hsep := by
        intro i j hij
        rintro x ⟨⟨s, hs, hxs⟩, ⟨t, ht, hxt⟩⟩
        have h1 : piecePos γ i s = piecePos γ j t := by rw [hxs, hxt]
        have h2 : 1 * s + (1 + (i:ℝ)) = 1 * t + (1 + (j:ℝ)) := hγinj h1
        have hi : (i:ℝ) + 1 ≤ (j:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
        have hsi : s + (i:ℝ) = t + (j:ℝ) := by linarith
        have hs1 : s ≤ 1 := hs.2
        have ht0 : 0 ≤ t := ht.1
        have hle : (i:ℝ) + 1 ≤ s + (i:ℝ) := by
          calc (i:ℝ) + 1 ≤ (j:ℝ) := hi
            _ ≤ t + (j:ℝ) := by linarith
            _ = s + (i:ℝ) := hsi.symm
        have hseq : s = 1 := by linarith
        rw [Set.mem_singleton_iff, ← hxs]
        rw [show piecePos γ i s = γ (1 * s + (1 + (i:ℝ))) from rfl,
          show piecePos γ i 1 = γ (1 * 1 + (1 + (i:ℝ))) from rfl, hseq]
      hesc := by
        intro K hK
        obtain ⟨R, hR0, hR⟩ := hbound K hK
        refine ⟨⌈R⌉₊ + 2, fun i hi => ?_⟩
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨⟨s, hs, rfl⟩, hxK⟩
        have h1 : |1 * s + (1 + (i:ℝ))| ≤ R := hR _ hxK
        have h2 : (1:ℝ) + (i:ℝ) ≤ 1 * s + (1 + (i:ℝ)) := by nlinarith [hs.1]
        have h3 : ((⌈R⌉₊ : ℝ)) + 2 ≤ (i:ℝ) := by exact_mod_cast hi
        have h4 : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
        have h5 := abs_le.mp h1
        linarith [h5.2]
      c₀ := c₀
      u₀ := w₀
      e₀ := min e₀ 1
      he₀ := lt_min he₀ one_pos
      he₀1 := min_le_right _ _
      hu₀ := hw₀
      hc₀ := hc₀
      hsrc₀ := by
        have h := (hstr₀ 1 (by rw [sub_self, abs_zero]; exact he₀.le)).1
        rw [hγ1] at h
        have h0 : piecePos γ 0 0 = b := by
          rw [show piecePos γ 0 0 = γ (1 * 0 + (1 + ((0:ℕ):ℝ))) from rfl]
          norm_num
          exact hγ1
        rwa [h0]
      hgerm₀ := by
        intro t ht0 hte
        have h := piecePos_base (b := b) hstr₀ t ht0 (le_trans hte (min_le_left e₀ 1))
        rw [h]
        have h0 : piecePos γ 0 0 = b := by
          rw [show piecePos γ 0 0 = γ (1 * 0 + (1 + ((0:ℕ):ℝ))) from rfl]
          norm_num
          exact hγ1
        rw [h0] }
  -- ## the negative lane
  let hLm : Lane n M :=
    { P := pieceNeg γ
      hsm := fun i => contMDiff_pieceNeg hγsm i
      himm := fun i t _ => imm_pieceNeg hγsm himm i t
      hinj := fun i => injOn_pieceNeg hγinj i
      hjun := by
        intro i
        rw [pieceNeg_one, pieceNeg_zero]
        congr 1
        push_cast
        ring
      hgerm := by
        intro i
        refine ⟨cM i, -(wM i), eM i, heM i, hcM i, ?_, ?_, ?_⟩
        · rw [pieceNeg_one]
          exact hsrcM i
        · intro t ht1 ht2
          exact pieceNeg_form_out i (hstrM i) t ht1 ht2
        · intro t ht1 ht2
          exact pieceNeg_form_in i (hstrM i) t ht1 ht2
      hsep := by
        intro i j hij
        rintro x ⟨⟨s, hs, hxs⟩, ⟨t, ht, hxt⟩⟩
        have h1 : pieceNeg γ i s = pieceNeg γ j t := by rw [hxs, hxt]
        have h2 : (-1) * s + (1 - (i:ℝ)) = (-1) * t + (1 - (j:ℝ)) := hγinj h1
        have hi : (i:ℝ) + 1 ≤ (j:ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
        have hsi : t + (j:ℝ) = s + (i:ℝ) := by linarith
        have hs1 : s ≤ 1 := hs.2
        have ht0 : 0 ≤ t := ht.1
        have hle : (i:ℝ) + 1 ≤ t + (j:ℝ) := by
          calc (i:ℝ) + 1 ≤ (j:ℝ) := hi
            _ ≤ t + (j:ℝ) := by linarith
        have hseq : s = 1 := by linarith
        rw [Set.mem_singleton_iff, ← hxs]
        rw [show pieceNeg γ i s = γ ((-1) * s + (1 - (i:ℝ))) from rfl,
          show pieceNeg γ i 1 = γ ((-1) * 1 + (1 - (i:ℝ))) from rfl, hseq]
      hesc := by
        intro K hK
        obtain ⟨R, hR0, hR⟩ := hbound K hK
        refine ⟨⌈R⌉₊ + 2, fun i hi => ?_⟩
        rw [Set.eq_empty_iff_forall_notMem]
        rintro x ⟨⟨s, hs, rfl⟩, hxK⟩
        have h1 : |(-1) * s + (1 - (i:ℝ))| ≤ R := hR _ hxK
        have h2 : s - 1 + (i:ℝ) ≤ |(-1) * s + (1 - (i:ℝ))| := by
          rw [show (-1) * s + (1 - (i:ℝ)) = -(s - 1 + (i:ℝ)) from by ring, abs_neg]
          exact le_abs_self _
        have h3 : (i:ℝ) - 1 ≤ s - 1 + (i:ℝ) := by linarith [hs.1]
        have h4 : ((⌈R⌉₊ : ℝ)) + 2 ≤ (i:ℝ) := by exact_mod_cast hi
        have h5 : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
        linarith
      c₀ := c₀
      u₀ := -w₀
      e₀ := min e₀ 1
      he₀ := lt_min he₀ one_pos
      he₀1 := min_le_right _ _
      hu₀ := neg_ne_zero.mpr hw₀
      hc₀ := hc₀
      hsrc₀ := by
        have h := (hstr₀ 1 (by rw [sub_self, abs_zero]; exact he₀.le)).1
        rw [hγ1] at h
        have h0 : pieceNeg γ 0 0 = b := by
          rw [show pieceNeg γ 0 0 = γ ((-1) * 0 + (1 - ((0:ℕ):ℝ))) from rfl]
          norm_num
          exact hγ1
        rwa [h0]
      hgerm₀ := by
        intro t ht0 hte
        have h := pieceNeg_base (b := b) hstr₀ t ht0 (le_trans hte (min_le_left e₀ 1))
        rw [h]
        have h0 : pieceNeg γ 0 0 = b := by
          rw [show pieceNeg γ 0 0 = γ ((-1) * 0 + (1 - ((0:ℕ):ℝ))) from rfl]
          norm_num
          exact hγ1
        rw [h0] }
  -- ## the assembly
  have hcp : hLp.c₀ = c₀ := rfl
  have hcm : hLm.c₀ = c₀ := rfl
  have hup : hLp.u₀ = w₀ := rfl
  have hum : hLm.u₀ = -w₀ := rfl
  refine ⟨hLp, hLm, hbW, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change piecePos γ 0 0 = b
    rw [show piecePos γ 0 0 = γ (1 * 0 + (1 + ((0:ℕ):ℝ))) from rfl]
    norm_num
    exact hγ1
  · change pieceNeg γ 0 0 = b
    rw [show pieceNeg γ 0 0 = γ ((-1) * 0 + (1 - ((0:ℕ):ℝ))) from rfl]
    norm_num
    exact hγ1
  · rfl
  · rfl
  · intro i
    change piecePos γ i '' Set.Icc (0:ℝ) 1 ⊆ W
    rintro x ⟨t, ht, rfl⟩
    exact hγrange ⟨1 * t + (1 + (i:ℝ)), rfl⟩
  · intro i
    change pieceNeg γ i '' Set.Icc (0:ℝ) 1 ⊆ W
    rintro x ⟨t, ht, rfl⟩
    exact hγrange ⟨(-1) * t + (1 - (i:ℝ)), rfl⟩
  · change (⋃ i, piecePos γ i '' Set.Icc (0:ℝ) 1) ∩ (⋃ j, pieceNeg γ j '' Set.Icc (0:ℝ) 1)
      ⊆ {b}
    rintro x ⟨hxp, hxm⟩
    rw [Set.mem_iUnion] at hxp hxm
    obtain ⟨i, s, hs, hxs⟩ := hxp
    obtain ⟨j, t, ht, hxt⟩ := hxm
    have h1 : piecePos γ i s = pieceNeg γ j t := by rw [hxs, hxt]
    have h2 : 1 * s + (1 + (i:ℝ)) = (-1) * t + (1 - (j:ℝ)) := hγinj h1
    have hi0 : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
    have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    have h3 : s = 0 := by linarith [hs.1, hs.2, ht.1, ht.2, hi0, hj0]
    have h4 : (i:ℝ) = 0 := by linarith [hs.1, hs.2, ht.1, ht.2, hi0, hj0]
    rw [Set.mem_singleton_iff, ← hxs]
    rw [show piecePos γ i s = γ (1 * s + (1 + (i:ℝ))) from rfl, h3, h4]
    norm_num
    exact hγ1

end

end Work.Noncompact.CompressionTube
