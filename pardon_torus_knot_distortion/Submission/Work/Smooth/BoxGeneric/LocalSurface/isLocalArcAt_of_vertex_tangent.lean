import Mathlib
import Submission.Work.Smooth.BoxGeneric.Defs
import Submission.Work.Smooth.BoxGeneric.Vertex.aeNoVertex_of_ae_centre
import Submission.Work.Smooth.BoxGeneric.Case.exists_active_signed_of_not_vertex
import Submission.Work.Smooth.Morse.All
import Submission.Work.Smooth.BoxGeneric.LocalArc.exists_root_of_mono
import Submission.Work.Smooth.BoxGeneric.LocalArc.sign_and_mono_of_deriv_bounds
import Submission.Work.Smooth.BoxGeneric.LocalArc.local_arc_of_max_of_tangential
import Submission.Work.Smooth.BoxGeneric.LocalSurface.boxNorm_param_eq_max
import Submission.Work.Smooth.BoxGeneric.LocalSurface.fderiv_pullback_faceLin_apply_vertexDir

/-!
# The box-norm level set is locally an arc at a *tangential* vertex

The fourth and last local model of the box-norm chapter, complementing
`LocalSurface/isLocalArcAt_of_uniqueActiveFace` (a single tight face),
`LocalSurface/isLocalArcAt_of_corner` (a transverse corner) and
`LocalSurface/isLocalArcAt_of_tangentialCorner` (a tangential corner).

Let `y = boxVertex c σ ε s` be a *vertex* of the box `PBox s c σ` (all three faces tight, sign
pattern `ε i = ±1`) lying on the surface `F = ψ(standard torus)`, and suppose that the vertex-ray
direction `vertexDir σ ε` — the direction in which all three face functions increase at unit speed,
`faceLin c σ i (ε i) (y + t • vertexDir σ ε) = s + t` — is **tangent** to `F` at `y`
(`htan`), i.e. lies in the image of `d (param ψ)` at a parameter `p` over `y`.

In coordinates adapted to the vertex, the box sphere near `y` is the corner cone
`C = {v | max_i v_i = 0}`; the tangency hypothesis says that the tangent plane `T` of `F` at `y`
contains the diagonal `(1,1,1)`, so `- (1,1,1)` lies in the *interior* of the negative orthant and
`T ∩ {v ≤ 0}` is a genuine sector, `T ∩ C` the union of its two boundary rays.  The level set
`F ∩ {boxNorm c σ · = s}` is therefore locally a "V" through `y`.

Formally the three pulled-back signed faces `F i = pullback ψ (faceLin c σ i (ε i)) - s` are `C¹`,
vanish at `p`, and have derivative `1` in the common direction `r` (`htan`); the zero set of the
maximum of three such functions is locally an arc (`LocalArc.local_arc_of_max_three`, the lower
envelope of the three level curves), the box norm agrees with the maximum of the three signed faces
near the vertex (`LocalSurface.boxNorm_param_eq_max`), and pushing the arc forward along the locally
injective parametrisation gives the local arc of the surface level set.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

namespace Work.Smooth.BoxGeneric.LocalSurface

/-- Every linear functional on `ℝ × ℝ` is `z ↦ L (1,0) * z.1 + L (0,1) * z.2`. -/
private lemma linear_apply_eq (L : (ℝ × ℝ) →L[ℝ] ℝ) (z : ℝ × ℝ) :
    L z = L (1, 0) * z.1 + L (0, 1) * z.2 := by
  have hz : z = z.1 • ((1, 0) : ℝ × ℝ) + z.2 • ((0, 1) : ℝ × ℝ) := by ext <;> simp
  conv_lhs => rw [hz]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **The implicit function of a `C¹` function with positive `x`-derivative at the origin.** -/
private theorem exists_root_local {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ 1 F) (hF0 : F 0 = 0)
    (ha : 0 < fderiv ℝ F 0 (1, 0)) :
    ∃ Rx : ℝ, ∃ Ry : ℝ, ∃ ψ : ℝ → ℝ,
      0 < Rx ∧ 0 < Ry ∧ ψ 0 = 0 ∧ ContinuousOn ψ (Set.Ioo (-Ry) Ry) ∧
      (∀ y : ℝ, |y| ≤ Ry → |ψ y| ≤ Rx ∧ F (ψ y, y) = 0) ∧
      (∀ x y : ℝ, |x| ≤ Rx → |y| ≤ Ry → (F (x, y) ≤ 0 ↔ x ≤ ψ y)) ∧
      (∀ x y : ℝ, |x| ≤ Rx → |y| ≤ Ry → (F (x, y) = 0 ↔ x = ψ y)) := by
  set a : ℝ := fderiv ℝ F 0 (1, 0) with hadef
  set b : ℝ := fderiv ℝ F 0 (0, 1) with hbdef
  have ha' : 0 < a := ha
  have hder : ∀ z : ℝ × ℝ, fderiv ℝ F 0 z = a * z.1 + b * z.2 := by
    intro z
    rw [hadef, hbdef]
    exact linear_apply_eq _ z
  have hcont : Continuous (fderiv ℝ F) := hF.continuous_fderiv (by norm_num)
  have hev : {q : ℝ × ℝ | fderiv ℝ F q ∈ Metric.ball (fderiv ℝ F 0) (a / 4)} ∈ nhds (0 : ℝ × ℝ) :=
    hcont.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by linarith)))
  obtain ⟨δc, hδcpos, hδc⟩ := Metric.mem_nhds_iff.mp hev
  set Rx : ℝ := δc / 2 with hRxdef
  have hRxpos : 0 < Rx := by rw [hRxdef]; linarith
  have hclose : ∀ q : ℝ × ℝ, ‖q‖ ≤ Rx → ‖fderiv ℝ F q - fderiv ℝ F 0‖ ≤ a / 4 := by
    intro q hq
    have hq' : q ∈ Metric.ball (0 : ℝ × ℝ) δc := by
      rw [Metric.mem_ball, dist_zero_right]
      rw [hRxdef] at hq
      linarith
    have h := hδc hq'
    simp only [Set.mem_ofPred_eq] at h
    rw [Metric.mem_ball, dist_eq_norm] at h
    exact le_of_lt h
  set Ry : ℝ := min Rx ((3 * a / 4) * Rx / (|b| + 1)) with hRydef
  have hRypos : 0 < Ry := by
    rw [hRydef]
    exact lt_min hRxpos (by positivity)
  have hRyRx : Ry ≤ Rx := by rw [hRydef]; exact min_le_left _ _
  have hbnd : |b| * Ry < (3 * a / 4) * Rx := by
    have h1 : Ry ≤ (3 * a / 4) * Rx / (|b| + 1) := by rw [hRydef]; exact min_le_right _ _
    have h2 : 0 < |b| + 1 := by positivity
    have h3 : |b| / (|b| + 1) < 1 := by
      rw [div_lt_one h2]
      linarith [abs_nonneg b]
    calc |b| * Ry ≤ |b| * ((3 * a / 4) * Rx / (|b| + 1)) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg b)
      _ = (|b| / (|b| + 1)) * ((3 * a / 4) * Rx) := by ring
      _ < 1 * ((3 * a / 4) * Rx) := by
          exact mul_lt_mul_of_pos_right h3 (by positivity)
      _ = (3 * a / 4) * Rx := one_mul _
  obtain ⟨hsign, hmono⟩ := Work.Smooth.BoxGeneric.LocalArc.sign_and_mono_of_deriv_bounds hF hF0 ha' hRxpos hRypos hRyRx hder hbnd hclose
  obtain ⟨ψ, hψ0, hψcont, hroot, hle, heq⟩ :=
    Work.Smooth.BoxGeneric.LocalArc.exists_root_of_mono hF.continuous hRxpos hRypos hF0 (fun y hy => (hsign y hy).1)
      (fun y hy => (hsign y hy).2) hmono
  exact ⟨Rx, Ry, ψ, hRxpos, hRypos, hψ0, hψcont, hroot, hle, heq⟩

/-- A nonzero vector of `ℝ × ℝ` can be completed to a basis. -/
private theorem exists_bijective_linear_of_ne_zero {r : ℝ × ℝ} (hr : r ≠ 0) :
    ∃ M : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ), Function.Bijective M ∧ M (1, 0) = r := by
  let w : ℝ × ℝ := if r.2 = 0 then (0, 1) else (1, 0)
  let M : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) :=
    (LinearMap.fst ℝ ℝ ℝ).smulRight r + (LinearMap.snd ℝ ℝ ℝ).smulRight w
  have hM : ∀ z : ℝ × ℝ, M z = z.1 • r + z.2 • w := by
    intro z
    simp [M, LinearMap.smulRight_apply]
  have hM10 : M (1, 0) = r := by
    rw [hM]; simp
  have hinj : Function.Injective M := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro z hz
    rw [LinearMap.mem_ker] at hz
    have hz' : z.1 • r + z.2 • w = 0 := by rw [← hM z]; exact hz
    have h1 : z.1 * r.1 + z.2 * w.1 = 0 := by
      have hh := congrArg Prod.fst hz'
      simpa [Prod.fst_add, Prod.smul_fst, smul_eq_mul] using hh
    have h2 : z.1 * r.2 + z.2 * w.2 = 0 := by
      have hh := congrArg Prod.snd hz'
      simpa [Prod.snd_add, Prod.smul_snd, smul_eq_mul] using hh
    by_cases h0 : r.2 = 0
    · have hw : w = (0, 1) := by simp [w, h0]
      rw [hw] at h1 h2
      simp only at h1 h2
      simp at h1 h2
      have hr1 : r.1 ≠ 0 := by
        intro hh
        exact hr (by ext <;> simp [hh, h0])
      have hz1 : z.1 = 0 := by
        rcases h1 with h | h
        · exact h
        · exact absurd h hr1
      have hz2 : z.2 = 0 := by
        rw [h0] at h2
        simpa using h2
      ext <;> simp [hz1, hz2]
    · have hw : w = (1, 0) := by simp [w, h0]
      rw [hw] at h1 h2
      simp only at h1 h2
      simp at h1 h2
      have hz1 : z.1 = 0 := by
        rcases h2 with h | h
        · exact h
        · exact absurd h h0
      have hz2 : z.2 = 0 := by
        rw [hz1] at h1
        simpa using h1
      ext <;> simp [hz1, hz2]
  have hsurj : Function.Surjective M :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) (V := ℝ × ℝ) (V₂ := ℝ × ℝ)
      rfl).mp hinj
  exact ⟨M, ⟨hinj, hsurj⟩, hM10⟩

private lemma max_max_eq_zero_iff {A B C : ℝ} :
    max (max A B) C = 0 ↔ A ≤ 0 ∧ B ≤ 0 ∧ C ≤ 0 ∧ (A = 0 ∨ B = 0 ∨ C = 0) := by
  constructor
  · intro h
    have hC : C ≤ 0 := le_trans (le_max_right _ _) (le_of_eq h)
    have hAB : max A B ≤ 0 := le_trans (le_max_left _ _) (le_of_eq h)
    have hA : A ≤ 0 := le_trans (le_max_left _ _) hAB
    have hB : B ≤ 0 := le_trans (le_max_right _ _) hAB
    refine ⟨hA, hB, hC, ?_⟩
    have h2 := (Work.Smooth.BoxGeneric.LocalArc.max_eq_zero_iff (a := max A B) (b := C)).mp h
    rcases h2.2.2 with h' | h'
    · rcases (Work.Smooth.BoxGeneric.LocalArc.max_eq_zero_iff (a := A) (b := B)).mp h' with ⟨-, -, h'' | h''⟩
      · exact Or.inl h''
      · exact Or.inr (Or.inl h'')
    · exact Or.inr (Or.inr h')
  · rintro ⟨hA, hB, hC, h⟩
    have h1 : max (max A B) C ≤ 0 := max_le (max_le hA hB) hC
    have h2 : 0 ≤ max (max A B) C := by
      rcases h with h | h | h
      · rw [h]
        exact le_trans (le_max_left (0 : ℝ) B) (le_max_left (max (0 : ℝ) B) C)
      · rw [h]
        exact le_trans (le_max_right A (0 : ℝ)) (le_max_left (max A (0 : ℝ)) C)
      · rw [h]
        exact le_max_right (max A B) (0 : ℝ)
    linarith



set_option linter.unusedVariables false

/-- Shrink the parameter interval so that `|ψ y| ≤ R` there. -/
private lemma shrink_psi {ψ : ℝ → ℝ} {Ry : ℝ} (hRy : 0 < Ry)
    (hcont : ContinuousOn ψ (Set.Ioo (-Ry) Ry)) (h0 : ψ 0 = 0) {R : ℝ} (hR : 0 < R) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ Ry ∧ ∀ y : ℝ, |y| ≤ δ → |ψ y| ≤ R := by
  have hmem : Set.Ioo (-Ry) Ry ∈ nhds (0 : ℝ) :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hcat : ContinuousAt ψ 0 := hcont.continuousAt hmem
  have hev : {y : ℝ | ψ y ∈ Metric.ball (ψ 0) R} ∈ nhds (0 : ℝ) :=
    hcat (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hR))
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨min δ₁ Ry / 2, by positivity, by linarith [min_le_right δ₁ Ry], ?_⟩
  intro y hy
  have hy1 : y ∈ Metric.ball (0 : ℝ) δ₁ := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    have h3 : min δ₁ Ry / 2 < δ₁ := by
      have h4 : min δ₁ Ry ≤ δ₁ := min_le_left _ _
      linarith
    linarith
  have h := hδ₁ hy1
  simp only [Set.mem_ofPred_eq] at h
  rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, h0, sub_zero] at h
  exact le_of_lt h


private theorem local_arc_of_max_three_proved {f g h : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hh : ContDiff ℝ 1 h) {p : ℝ × ℝ} (hfp : f p = 0) (hgp : g p = 0) (hhp : h p = 0)
    {r : ℝ × ℝ} (hr : r ≠ 0) (hdf : 0 < fderiv ℝ f p r) (hdg : 0 < fderiv ℝ g p r)
    (hdh : 0 < fderiv ℝ h p r) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ ρ : ℝ → ℝ × ℝ, ρ 0 = p ∧
      ContinuousOn ρ (Set.Ioo (-1 : ℝ) 1) ∧ Set.InjOn ρ (Set.Ioo (-1 : ℝ) 1) ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1, max (max (f (ρ t)) (g (ρ t))) (h (ρ t)) = 0) ∧
      (∀ q : ℝ × ℝ, max (max (f q) (g q)) (h q) = 0 → ‖q - p‖ < ε →
        ∃ t ∈ Set.Ioo (-1 : ℝ) 1, ρ t = q) := by
  classical
  obtain ⟨M, hMbij, hM10⟩ := exists_bijective_linear_of_ne_zero (r := r) hr
  have hMinj : Function.Injective M := hMbij.1
  have hMsurj : Function.Surjective M := hMbij.2
  set Mc : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := LinearMap.toContinuousLinearMap M with hMcdef
  have hMc : ∀ z : ℝ × ℝ, Mc z = M z := fun z => rfl
  set f' : ℝ × ℝ → ℝ := fun z => f (p + Mc z) with hf'def
  set g' : ℝ × ℝ → ℝ := fun z => g (p + Mc z) with hg'def
  set h' : ℝ × ℝ → ℝ := fun z => h (p + Mc z) with hh'def
  have hf'cd : ContDiff ℝ 1 f' := by rw [hf'def]; fun_prop
  have hg'cd : ContDiff ℝ 1 g' := by rw [hg'def]; fun_prop
  have hh'cd : ContDiff ℝ 1 h' := by rw [hh'def]; fun_prop
  have hf'0 : f' 0 = 0 := by
    rw [hf'def]
    show f (p + Mc 0) = 0
    rw [hMc, map_zero, add_zero]
    exact hfp
  have hg'0 : g' 0 = 0 := by
    rw [hg'def]
    show g (p + Mc 0) = 0
    rw [hMc, map_zero, add_zero]
    exact hgp
  have hh'0 : h' 0 = 0 := by
    rw [hh'def]
    show h (p + Mc 0) = 0
    rw [hMc, map_zero, add_zero]
    exact hhp
  have hf'd : 0 < fderiv ℝ f' 0 (1, 0) := by
    rw [hf'def, Work.Smooth.BoxGeneric.LocalArc.fderiv_comp_const_add_linear f hf p Mc]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hMc, hM10]
    exact hdf
  have hg'd : 0 < fderiv ℝ g' 0 (1, 0) := by
    rw [hg'def, Work.Smooth.BoxGeneric.LocalArc.fderiv_comp_const_add_linear g hg p Mc]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hMc, hM10]
    exact hdg
  have hh'd : 0 < fderiv ℝ h' 0 (1, 0) := by
    rw [hh'def, Work.Smooth.BoxGeneric.LocalArc.fderiv_comp_const_add_linear h hh p Mc]
    simp only [ContinuousLinearMap.comp_apply]
    rw [hMc, hM10]
    exact hdh
  obtain ⟨Rxf, Ryf, ψf, hRxfpos, hRyfpos, hψf0, hψfcont, hfroot, hfle, hfeq⟩ :=
    exists_root_local hf'cd hf'0 hf'd
  obtain ⟨Rxg, Ryg, ψg, hRxgpos, hRygpos, hψg0, hψgcont, hgroot, hgle, hgeq⟩ :=
    exists_root_local hg'cd hg'0 hg'd
  obtain ⟨Rxh, Ryh, ψh, hRxhpos, hRyhpos, hψh0, hψhcont, hhroot, hhle, hheq⟩ :=
    exists_root_local hh'cd hh'0 hh'd
  set R : ℝ := min (min Rxf Rxg) Rxh with hRdef
  have hRpos : 0 < R := lt_min (lt_min hRxfpos hRxgpos) hRxhpos
  have hR_le_f : R ≤ Rxf := le_trans (min_le_left _ _) (min_le_left _ _)
  have hR_le_g : R ≤ Rxg := le_trans (min_le_left _ _) (min_le_right _ _)
  have hR_le_h : R ≤ Rxh := min_le_right _ _
  obtain ⟨δf, hδfpos, hδfRy, hδf⟩ := shrink_psi hRyfpos hψfcont hψf0 hRpos
  obtain ⟨δg, hδgpos, hδgRy, hδg⟩ := shrink_psi hRygpos hψgcont hψg0 hRpos
  obtain ⟨δh, hδhpos, hδhRy, hδh⟩ := shrink_psi hRyhpos hψhcont hψh0 hRpos
  set Ry : ℝ := min (min (min Ryf Ryg) Ryh) (min (min δf δg) δh) with hRydef
  have hRypos : 0 < Ry := lt_min (lt_min (lt_min hRyfpos hRygpos) hRyhpos)
    (lt_min (lt_min hδfpos hδgpos) hδhpos)
  have hRy_le_f : Ry ≤ Ryf := by
    rw [hRydef]
    calc min (min (min Ryf Ryg) Ryh) (min (min δf δg) δh)
        ≤ min (min Ryf Ryg) Ryh := min_le_left _ _
      _ ≤ min Ryf Ryg := min_le_left _ _
      _ ≤ Ryf := min_le_left _ _
  have hRy_le_g : Ry ≤ Ryg := by
    rw [hRydef]
    calc min (min (min Ryf Ryg) Ryh) (min (min δf δg) δh)
        ≤ min (min Ryf Ryg) Ryh := min_le_left _ _
      _ ≤ min Ryf Ryg := min_le_left _ _
      _ ≤ Ryg := min_le_right _ _
  have hRy_le_h : Ry ≤ Ryh := by
    rw [hRydef]
    calc min (min (min Ryf Ryg) Ryh) (min (min δf δg) δh)
        ≤ min (min Ryf Ryg) Ryh := min_le_left _ _
      _ ≤ Ryh := min_le_right _ _
  have hRy_le_δf : Ry ≤ δf := by
    rw [hRydef]
    calc min (min (min Ryf Ryg) Ryh) (min (min δf δg) δh)
        ≤ min (min δf δg) δh := min_le_right _ _
      _ ≤ min δf δg := min_le_left _ _
      _ ≤ δf := min_le_left _ _
  have hRy_le_δg : Ry ≤ δg := by
    rw [hRydef]
    calc min (min (min Ryf Ryg) Ryh) (min (min δf δg) δh)
        ≤ min (min δf δg) δh := min_le_right _ _
      _ ≤ min δf δg := min_le_left _ _
      _ ≤ δg := min_le_right _ _
  have hRy_le_δh : Ry ≤ δh := by
    rw [hRydef]
    calc min (min (min Ryf Ryg) Ryh) (min (min δf δg) δh)
        ≤ min (min δf δg) δh := min_le_right _ _
      _ ≤ δh := min_le_right _ _
  set ψ : ℝ → ℝ := fun y => min (min (ψf y) (ψg y)) (ψh y) with hψdef
  have hψ0 : ψ 0 = 0 := by rw [hψdef]; simp [hψf0, hψg0, hψh0]
  have hψ_le_f : ∀ y : ℝ, ψ y ≤ ψf y := fun y => by
    rw [hψdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hψ_le_g : ∀ y : ℝ, ψ y ≤ ψg y := fun y => by
    rw [hψdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hψ_le_h : ∀ y : ℝ, ψ y ≤ ψh y := fun y => by rw [hψdef]; exact min_le_right _ _
  have hψ_attained : ∀ y : ℝ, ψ y = ψf y ∨ ψ y = ψg y ∨ ψ y = ψh y := by
    intro y
    rw [hψdef]
    simp only
    rcases min_choice (min (ψf y) (ψg y)) (ψh y) with h1 | h1
    · rw [h1]
      rcases min_choice (ψf y) (ψg y) with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr h1)
  set Me : (ℝ × ℝ) ≃ₗ[ℝ] (ℝ × ℝ) := LinearEquiv.ofBijective M ⟨hMinj, hMsurj⟩ with hMedef
  set Mi : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) := Me.symm.toLinearMap with hMidef
  have hMi_apply : ∀ u : ℝ × ℝ, Mi u = Me.symm u := fun u => rfl
  have hM_Mi : ∀ u : ℝ × ℝ, M (Mi u) = u := fun u => by
    rw [hMi_apply]; exact Me.apply_symm_apply u
  have hMicont : Continuous Mi := LinearMap.continuous_of_finiteDimensional Mi
  obtain ⟨ε, hεpos, hε⟩ := Metric.continuous_iff.mp hMicont 0 (min R Ry) (lt_min hRpos hRypos)
  set ρ : ℝ → ℝ × ℝ := fun t => p + Mc (ψ (Ry * t), Ry * t) with hρdef
  have hρ_eq : ∀ t : ℝ, ρ t = p + Mc (ψ (Ry * t), Ry * t) := fun t => by rw [hρdef]
  have hρ_f : ∀ t : ℝ, f (ρ t) = f' (ψ (Ry * t), Ry * t) := fun t => by
    simp only [hρ_eq, hf'def, hMc]
  have hρ_g : ∀ t : ℝ, g (ρ t) = g' (ψ (Ry * t), Ry * t) := fun t => by
    simp only [hρ_eq, hg'def, hMc]
  have hρ_h : ∀ t : ℝ, h (ρ t) = h' (ψ (Ry * t), Ry * t) := fun t => by
    simp only [hρ_eq, hh'def, hMc]
  refine ⟨ε, hεpos, ρ, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hρ_eq, mul_zero, hψ0, hMc]
    rw [show ((0 : ℝ), (0 : ℝ)) = (0 : ℝ × ℝ) from rfl, map_zero, add_zero]
  · -- continuity of the arc
    have hmapf : Set.MapsTo (fun t : ℝ => Ry * t) (Set.Ioo (-1 : ℝ) 1) (Set.Ioo (-Ryf) Ryf) := by
      intro t ht
      rw [Set.mem_Ioo] at ht ⊢
      have h : Ry * t < Ryf := lt_of_lt_of_le (by nlinarith [ht.2, hRypos]) hRy_le_f
      constructor <;> nlinarith [ht.1, ht.2, hRypos, h]
    have hmapg : Set.MapsTo (fun t : ℝ => Ry * t) (Set.Ioo (-1 : ℝ) 1) (Set.Ioo (-Ryg) Ryg) := by
      intro t ht
      rw [Set.mem_Ioo] at ht ⊢
      have h : Ry * t < Ryg := lt_of_lt_of_le (by nlinarith [ht.2, hRypos]) hRy_le_g
      constructor <;> nlinarith [ht.1, ht.2, hRypos, h]
    have hmaph : Set.MapsTo (fun t : ℝ => Ry * t) (Set.Ioo (-1 : ℝ) 1) (Set.Ioo (-Ryh) Ryh) := by
      intro t ht
      rw [Set.mem_Ioo] at ht ⊢
      have h : Ry * t < Ryh := lt_of_lt_of_le (by nlinarith [ht.2, hRypos]) hRy_le_h
      constructor <;> nlinarith [ht.1, ht.2, hRypos, h]
    have hcf : ContinuousOn (fun t : ℝ => ψf (Ry * t)) (Set.Ioo (-1 : ℝ) 1) :=
      hψfcont.comp (continuous_const.mul continuous_id).continuousOn hmapf
    have hcg : ContinuousOn (fun t : ℝ => ψg (Ry * t)) (Set.Ioo (-1 : ℝ) 1) :=
      hψgcont.comp (continuous_const.mul continuous_id).continuousOn hmapg
    have hch : ContinuousOn (fun t : ℝ => ψh (Ry * t)) (Set.Ioo (-1 : ℝ) 1) :=
      hψhcont.comp (continuous_const.mul continuous_id).continuousOn hmaph
    have htriple : ContinuousOn (fun t : ℝ => (ψf (Ry * t), ψg (Ry * t), ψh (Ry * t)))
        (Set.Ioo (-1 : ℝ) 1) := hcf.prodMk (hcg.prodMk hch)
    have hminc : Continuous (fun p : ℝ × ℝ × ℝ => min (min p.1 p.2.1) p.2.2) := by fun_prop
    have hcm : ContinuousOn (fun t : ℝ => min (min (ψf (Ry * t)) (ψg (Ry * t))) (ψh (Ry * t)))
        (Set.Ioo (-1 : ℝ) 1) := hminc.comp_continuousOn htriple
    have hpair : ContinuousOn
        (fun t : ℝ => (min (min (ψf (Ry * t)) (ψg (Ry * t))) (ψh (Ry * t)), Ry * t))
        (Set.Ioo (-1 : ℝ) 1) := hcm.prodMk (continuous_const.mul continuous_id).continuousOn
    have hres : ContinuousOn (fun t : ℝ => p + Mc ((min (min (ψf (Ry * t)) (ψg (Ry * t)))
        (ψh (Ry * t))), Ry * t)) (Set.Ioo (-1 : ℝ) 1) :=
      (continuous_const.add Mc.continuous).continuousOn.comp hpair (Set.mapsTo_univ _ _)
    refine hres.congr ?_
    intro t ht
    rw [hρ_eq, hψdef]
  · -- injectivity of the arc
    intro t1 ht1 t2 ht2 heq
    rw [hρ_eq, hρ_eq] at heq
    have h1 : Mc (ψ (Ry * t1), Ry * t1) = Mc (ψ (Ry * t2), Ry * t2) := add_left_cancel heq
    rw [hMc] at h1
    have h2 : (ψ (Ry * t1), Ry * t1) = (ψ (Ry * t2), Ry * t2) := hMinj h1
    exact mul_left_cancel₀ (ne_of_gt hRypos) (congrArg Prod.snd h2)
  · -- the arc lies in the zero set of the maximum
    intro t ht
    have hyt : |Ry * t| < Ry := by
      rw [Set.mem_Ioo] at ht
      rw [abs_mul, abs_of_pos hRypos]
      have h1 : |t| < 1 := abs_lt.mpr ht
      nlinarith
    have hψR : |ψ (Ry * t)| ≤ R := by
      rw [hψdef]
      exact Work.Smooth.BoxGeneric.LocalArc.abs_min_le (Work.Smooth.BoxGeneric.LocalArc.abs_min_le (hδf _ (le_trans (le_of_lt hyt) hRy_le_δf))
        (hδg _ (le_trans (le_of_lt hyt) hRy_le_δg)))
        (hδh _ (le_trans (le_of_lt hyt) hRy_le_δh))
    have hle_f : |Ry * t| ≤ Ryf := le_trans (le_of_lt hyt) hRy_le_f
    have hle_g : |Ry * t| ≤ Ryg := le_trans (le_of_lt hyt) hRy_le_g
    have hle_h : |Ry * t| ≤ Ryh := le_trans (le_of_lt hyt) hRy_le_h
    have hxf : |ψ (Ry * t)| ≤ Rxf := le_trans hψR hR_le_f
    have hxg : |ψ (Ry * t)| ≤ Rxg := le_trans hψR hR_le_g
    have hxh : |ψ (Ry * t)| ≤ Rxh := le_trans hψR hR_le_h
    rw [hρ_f t, hρ_g t, hρ_h t, max_max_eq_zero_iff]
    refine ⟨(hfle _ _ hxf hle_f).mpr (hψ_le_f _), (hgle _ _ hxg hle_g).mpr (hψ_le_g _),
      (hhle _ _ hxh hle_h).mpr (hψ_le_h _), ?_⟩
    rcases hψ_attained (Ry * t) with h | h | h
    · exact Or.inl ((hfeq _ _ hxf hle_f).mpr h)
    · exact Or.inr (Or.inl ((hgeq _ _ hxg hle_g).mpr h))
    · exact Or.inr (Or.inr ((hheq _ _ hxh hle_h).mpr h))
  · -- the arc covers the zero set near `p`
    intro q hq hqε
    rw [max_max_eq_zero_iff] at hq
    obtain ⟨hqf, hqg, hqh, hqsome⟩ := hq
    set z : ℝ × ℝ := Mi (q - p) with hzdef
    have hMz : M z = q - p := hM_Mi (q - p)
    have hqz : q = p + M z := by rw [hMz]; abel
    have hzn : ‖z‖ < min R Ry := by
      have h := hε (q - p) (by rw [dist_eq_norm, sub_zero]; exact hqε)
      rw [dist_eq_norm, map_zero, sub_zero] at h
      simpa [hzdef] using h
    have hz1n : |z.1| ≤ ‖z‖ := by
      rw [Prod.norm_def, Real.norm_eq_abs]
      exact le_max_left _ _
    have hz2n : |z.2| ≤ ‖z‖ := by
      rw [Prod.norm_def, Real.norm_eq_abs]
      exact le_max_right _ _
    have hz1R : |z.1| < R := lt_of_le_of_lt hz1n (lt_of_lt_of_le hzn (min_le_left _ _))
    have hz2Ry : |z.2| < Ry := lt_of_le_of_lt hz2n (lt_of_lt_of_le hzn (min_le_right _ _))
    have hz1f : |z.1| ≤ Rxf := le_trans (le_of_lt hz1R) hR_le_f
    have hz1g : |z.1| ≤ Rxg := le_trans (le_of_lt hz1R) hR_le_g
    have hz1h : |z.1| ≤ Rxh := le_trans (le_of_lt hz1R) hR_le_h
    have hz2f : |z.2| ≤ Ryf := le_trans (le_of_lt hz2Ry) hRy_le_f
    have hz2g : |z.2| ≤ Ryg := le_trans (le_of_lt hz2Ry) hRy_le_g
    have hz2h : |z.2| ≤ Ryh := le_trans (le_of_lt hz2Ry) hRy_le_h
    have ef : f q = f' z := by simp only [hqz, hf'def, hMc]
    have eg : g q = g' z := by simp only [hqz, hg'def, hMc]
    have eh : h q = h' z := by simp only [hqz, hh'def, hMc]
    rw [ef] at hqf
    rw [eg] at hqg
    rw [eh] at hqh
    rw [ef, eg, eh] at hqsome
    have h1 : z.1 ≤ ψf z.2 := (hfle z.1 z.2 hz1f hz2f).mp hqf
    have h2 : z.1 ≤ ψg z.2 := (hgle z.1 z.2 hz1g hz2g).mp hqg
    have h3 : z.1 ≤ ψh z.2 := (hhle z.1 z.2 hz1h hz2h).mp hqh
    have h4 : ψ z.2 ≤ z.1 := by
      rcases hqsome with h | h | h
      · rw [(hfeq z.1 z.2 hz1f hz2f).mp h]
        exact hψ_le_f z.2
      · rw [(hgeq z.1 z.2 hz1g hz2g).mp h]
        exact hψ_le_g z.2
      · rw [(hheq z.1 z.2 hz1h hz2h).mp h]
        exact hψ_le_h z.2
    have h5 : z.1 = ψ z.2 := by
      have hle : z.1 ≤ ψ z.2 := by
        rw [hψdef]
        exact le_min (le_min h1 h2) h3
      exact le_antisymm hle h4
    refine ⟨z.2 / Ry, ?_, ?_⟩
    · rw [Set.mem_Ioo]
      constructor
      · rw [lt_div_iff₀ hRypos]
        linarith [(abs_lt.mp hz2Ry).1]
      · rw [div_lt_one hRypos]
        exact (abs_lt.mp hz2Ry).2
    · rw [hρ_eq, mul_div_cancel₀ z.2 (ne_of_gt hRypos), ← h5, hMc]
      show p + M z = q
      rw [hMz]
      abel



/-- The `i`-th signed face of the vertex's sign pattern, evaluated at the vertex, is the level. -/
private theorem faceLin_boxVertex (c : R3) (σ : Equiv.Perm (Fin 3)) {ε : Fin 3 → ℝ}
    (hε : ∀ i : Fin 3, ε i = 1 ∨ ε i = -1) (s : ℝ) (i : Fin 3) :
    Work.Smooth.BoxGeneric.faceLin c σ i (ε i) (Work.Smooth.BoxGeneric.boxVertex c σ ε s) = s := by
  have hb : Submission.boxSide i ≠ 0 := ne_of_gt (Submission.boxSide_pos i)
  rw [Work.Smooth.BoxGeneric.faceLin_apply, Work.Smooth.BoxGeneric.signedFace_apply,
    Work.Smooth.BoxGeneric.boxVertex_apply]
  rcases hε i with h | h
  · rw [h, add_sub_cancel_left]
    simp only [one_mul]
    rw [mul_comm (Submission.boxSide i) s, mul_div_cancel_right₀ s hb]
  · rw [h, show c (σ i) + -1 * Submission.boxSide i * s - c (σ i)
        = -(Submission.boxSide i * s) by ring, neg_div, mul_comm (Submission.boxSide i) s,
      mul_div_cancel_right₀ s hb]
    ring

/-- The vertex-ray direction of the box with sign pattern `ε i = ±1` is nonzero. -/
private theorem vertexDir_ne_zero (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → ℝ)
    (hε : ∀ i : Fin 3, ε i = 1 ∨ ε i = -1) :
    Work.Smooth.BoxGeneric.Vertex.vertexDir σ ε ≠ 0 := by
  intro h0
  have h2 := congrArg (fun v : R3 => v (σ 0)) h0
  rw [Work.Smooth.BoxGeneric.Vertex.vertexDir_apply, Equiv.symm_apply_apply] at h2
  simp at h2
  have hb : Submission.boxSide (0 : Fin 3) ≠ 0 := ne_of_gt (Submission.boxSide_pos 0)
  rcases hε 0 with h | h <;> rw [h] at h2 <;> simp_all

theorem isLocalArcAt_of_vertex_tangent {ψ : Submission.Diffeo} {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)} {s : ℝ} {ε : Fin 3 → ℝ} (hs : 0 < s) (hε : ∀ i : Fin 3, ε i = 1 ∨ ε i = -1) (hy : Work.Smooth.BoxGeneric.boxVertex c σ ε s ∈ (Work.Smooth.Morse.torus ψ).carrier) (hreg : ∀ i : Fin 3, ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = Work.Smooth.BoxGeneric.boxVertex c σ ε s ∧ fderiv ℝ (Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i (ε i))) p ≠ 0) (htan : ∃ p : ℝ × ℝ, Work.Smooth.Morse.param ψ p = Work.Smooth.BoxGeneric.boxVertex c σ ε s ∧ ∃ r : ℝ × ℝ, fderiv ℝ (Work.Smooth.Morse.param ψ) p r = Work.Smooth.BoxGeneric.Vertex.vertexDir σ ε) : ∃ U : Set LeanEval.KnotTheory.PardonDistortion.R3, Work.SurgeryInvariance.IsOpenInCarrier (Work.Smooth.Morse.torus ψ) U ∧ Work.Smooth.BoxGeneric.boxVertex c σ ε s ∈ U ∧ ∃ (I : Set ℝ) (s₀ : ℝ) (ρ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3), IsOpen I ∧ s₀ ∈ I ∧ ContinuousOn ρ I ∧ ρ s₀ = Work.Smooth.BoxGeneric.boxVertex c σ ε s ∧ Set.InjOn ρ I ∧ (∀ t ∈ I, ρ t ∈ Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s) ∧ (∀ z, z ∈ Work.Smooth.Morse.levelSet ψ (Submission.boxNorm c σ) s → z ∈ U → ∃ t ∈ I, ρ t = z) := by
  classical
  -- a parameter over the vertex and the tangent direction of the vertex ray
  obtain ⟨p, hp, r, hr⟩ := htan
  have hrne : r ≠ 0 := by
    intro h0
    have h1 : Work.Smooth.BoxGeneric.Vertex.vertexDir σ ε = 0 := by
      rw [← hr, h0, map_zero]
    exact vertexDir_ne_zero σ ε hε h1
  -- the three pulled-back signed faces, shifted to vanish at `p`
  let F : Fin 3 → ℝ × ℝ → ℝ := fun i q =>
    Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ i (ε i)) q - s
  have hFcd : ∀ i : Fin 3, ContDiff ℝ 1 (F i) := fun i =>
    ((Work.Smooth.BoxGeneric.pullback_faceLin_contDiff ψ c σ i (ε i)).sub contDiff_const).of_le
      (by simp)
  have hFp : ∀ i : Fin 3, F i p = 0 := fun i => by
    show Work.Smooth.BoxGeneric.faceLin c σ i (ε i) (Work.Smooth.Morse.param ψ p) - s = 0
    rw [hp, faceLin_boxVertex c σ hε s i, sub_self]
  have hFd : ∀ i : Fin 3, fderiv ℝ (F i) p r = 1 := fun i => by
    have h := fderiv_pullback_faceLin_apply_vertexDir (ψ := ψ) (c := c) (σ := σ) (ε := ε) (s := s)
      hp hr i (hε i)
    show fderiv ℝ (fun q => Work.Smooth.Morse.pullback ψ
      (Work.Smooth.BoxGeneric.faceLin c σ i (ε i)) q - s) p r = 1
    rw [fderiv_sub_const, h]
  -- the arc of the zero set of the maximum of the three faces, in the parameter plane
  obtain ⟨εa, hεapos, ρa, hρa0, hρacont, hρainj, hρalev, hρacov⟩ :=
    local_arc_of_max_three_proved (f := F 0) (g := F 1) (h := F 2)
      (hFcd 0) (hFcd 1) (hFcd 2) (hFp 0) (hFp 1) (hFp 2) hrne
      (by rw [hFd 0]; norm_num) (by rw [hFd 1]; norm_num) (by rw [hFd 2]; norm_num)
  -- near the vertex the box norm is the maximum of the three signed faces
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := Metric.mem_nhds_iff.mp
    (boxNorm_param_eq_max (ψ := ψ) (c := c) (σ := σ) (ε := ε) (s := s) hs hε hp)
  have hkey : ∀ q : ℝ × ℝ, q ∈ Metric.ball p δ₁ →
      (Submission.boxNorm c σ (Work.Smooth.Morse.param ψ q) = s ↔
        max (max (F 0 q) (F 1 q)) (F 2 q) = 0) := by
    intro q hq
    rw [hδ₁ hq]
    have e0 : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 0 (ε 0)) q
        = F 0 q + s := by
      show Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 0 (ε 0)) q
        = Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 0 (ε 0)) q - s + s
      ring
    have e1 : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 1 (ε 1)) q
        = F 1 q + s := by
      show Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 1 (ε 1)) q
        = Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 1 (ε 1)) q - s + s
      ring
    have e2 : Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 2 (ε 2)) q
        = F 2 q + s := by
      show Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 2 (ε 2)) q
        = Work.Smooth.Morse.pullback ψ (Work.Smooth.BoxGeneric.faceLin c σ 2 (ε 2)) q - s + s
      ring
    rw [e0, e1, e2, max_add_add_right, max_add_add_right]
    constructor <;> intro h <;> linarith
  -- a ball on which the parametrisation is injective
  obtain ⟨εp, hεppos, hεpinj⟩ := Work.Smooth.Morse.Surface.param_local_injective ψ p
  set δ : ℝ := min (min εa εp) δ₁ with hδdef
  have hδpos : 0 < δ := lt_min (lt_min hεapos hεppos) hδ₁pos
  have hδεa : δ ≤ εa := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδεp : δ ≤ εp := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδδ₁ : δ ≤ δ₁ := min_le_right _ _
  refine ⟨Work.Smooth.Morse.param ψ '' Metric.ball p δ,
    Work.Smooth.Morse.Surface.isOpenInCarrier_image_of_isOpen ψ Metric.isOpen_ball,
    ⟨p, Metric.mem_ball_self hδpos, hp⟩,
    Set.Ioo (-1 : ℝ) 1 ∩ ρa ⁻¹' Metric.ball p δ, 0, fun t => Work.Smooth.Morse.param ψ (ρa t),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the arc's interval is open
    exact hρacont.isOpen_inter_preimage isOpen_Ioo Metric.isOpen_ball
  · -- it contains the base parameter
    refine ⟨by norm_num, ?_⟩
    show ρa 0 ∈ Metric.ball p δ
    rw [hρa0]
    exact Metric.mem_ball_self hδpos
  · -- the arc of the surface is continuous
    exact (Work.Smooth.Morse.param_continuous ψ).continuousOn.comp
      (hρacont.mono inter_subset_left) (Set.mapsTo_univ _ _)
  · -- and passes through the vertex
    show Work.Smooth.Morse.param ψ (ρa 0) = Work.Smooth.BoxGeneric.boxVertex c σ ε s
    rw [hρa0, hp]
  · -- it is injective, because both the arc and the parametrisation are
    intro t1 ht1 t2 ht2 heq
    simp only [Set.mem_inter_iff, Set.mem_preimage] at ht1 ht2
    have h1 : ρa t1 ∈ Metric.ball p εp := Metric.ball_subset_ball hδεp ht1.2
    have h2 : ρa t2 ∈ Metric.ball p εp := Metric.ball_subset_ball hδεp ht2.2
    exact hρainj ht1.1 ht2.1 (hεpinj h1 h2 heq)
  · -- the arc lies in the box-norm level set
    intro t ht
    simp only [Set.mem_inter_iff, Set.mem_preimage] at ht
    rw [Work.Smooth.Morse.mem_levelSet]
    exact ⟨Work.Smooth.Morse.param_mem ψ (ρa t),
      (hkey (ρa t) (Metric.ball_subset_ball hδδ₁ ht.2)).mpr (hρalev t ht.1)⟩
  · -- and it exhausts the level set in the neighbourhood
    intro z hz hzU
    rw [Work.Smooth.Morse.mem_levelSet] at hz
    obtain ⟨-, hzbox⟩ := hz
    obtain ⟨q, hqB, hqz⟩ := hzU
    have hqδa : ‖q - p‖ < εa := by
      have hqd : dist q p < δ := Metric.mem_ball.mp hqB
      rw [dist_eq_norm] at hqd
      exact lt_of_lt_of_le hqd hδεa
    have hmax : max (max (F 0 q) (F 1 q)) (F 2 q) = 0 :=
      (hkey q (Metric.ball_subset_ball hδδ₁ hqB)).mp (by rw [hqz]; exact hzbox)
    obtain ⟨t, htI, htq⟩ := hρacov q hmax hqδa
    refine ⟨t, ?_, ?_⟩
    · simp only [Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨htI, by rw [htq]; exact hqB⟩
    · show Work.Smooth.Morse.param ψ (ρa t) = z
      rw [htq, hqz]

end Work.Smooth.BoxGeneric.LocalSurface
