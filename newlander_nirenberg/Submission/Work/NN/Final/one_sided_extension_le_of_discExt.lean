/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The one-sided `C^{k,α}` extension on polydiscs, from the one-variable disc extension

This file proves `Work.NN.Final.one_sided_extension_le_of_discExt`: the coordinate-by-coordinate
assembly which deduces the extension of a `C^∞` function on the polydisc `pd n ρ 1` (with finite
`C^{k,α}` norm) to a `C^k` function on the larger polydisc `pd n ρ c` (`c > 1`), from the
one-variable disc-extension property `DiscExt α c` (which extends along one complex coordinate,
with an arbitrary open parameter region, from radius `1` to radius `c`, with a `C^{k,α}` bound
uniform in the function).

The proof proceeds coordinate by coordinate in the order `0, 1, …, n-1`.  With
`mu i j = c * ρ j` for `j < i` and `mu i j = ρ j` for `j ≥ i`, the intermediate regions are the
polydiscs `polydisc 0 (mu i)`; at step `i` the `i`-th coordinate is extended from radius `ρ i` to
radius `c * ρ i`, the other coordinates being the parameters.  The function is moved between the
"tuple" space `Fin n → ℂ` and the "parameters times disc" space `({j // j ≠ i} → ℂ) × ℂ` by the
mutually inverse continuous linear maps `insert` and `delete`; both have operator norm `≤ 1`,
which is what makes the `C^{k,α}` bounds transport with no loss (the only loss comes from the disc
extension itself, once per coordinate).
-/
import Mathlib
import Submission.Work.NN.Final.Defs
import Submission.Work.NN.Final.DiscExtDefs
import Submission.Work.NN.Final.holderNorm_comp_linear
import Submission.Work.CR.Flat.Holder.holderNorm_comp_le

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set Metric

namespace Work.NN.Final

open Work.CR.Flat

/-! ## 1. Pulling the `C^{k,α}` norm back along a continuous linear map

Companions of `Work.CR.Flat.Holder.comp_linear_le` (which handles `L ∘ u`), and the
generalisation of `Work.NN.Final.holderNorm_comp_linear` (stated there for `Fin n → ℂ`): for a
continuous linear map `Φ` and `u` of class `C^k` on an open set `t`,

  `‖u ∘ Φ‖_{C^{k,α}(Φ ⁻¹' t)} ≤ C · ‖u‖_{C^{k,α}(t)}`,

with `C = max 1 (‖Φ‖ ^ (k + α))`.  In particular the estimate holds with constant `1` when
`‖Φ‖ ≤ 1`. -/

theorem holderNorm_comp_continuousLinearMap_le' {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) {α : ℝ} (hα : 0 < α)
    (Φ : E →L[ℝ] F) {t : Set F} (ht : IsOpen t) {u : F → ℂ} (hu : ContDiffOn ℝ k u t) :
    Work.CR.Flat.holderNorm k α (fun x => u (Φ x)) (Φ ⁻¹' t)
      ≤ ENNReal.ofReal (max 1 (‖Φ‖ ^ ((k : ℝ) + α))) * Work.CR.Flat.holderNorm k α u t := by
  have hsd : UniqueDiffOn ℝ t := ht.uniqueDiffOn
  have hpd : UniqueDiffOn ℝ (Φ ⁻¹' t) := (ht.preimage Φ.continuous).uniqueDiffOn
  rw [Work.CR.Flat.holderNorm, Work.CR.Flat.holderNorm, Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hik' : (i : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hik
  have hfac1 : ENNReal.ofReal (‖Φ‖ ^ i) ≤ ENNReal.ofReal (max 1 (‖Φ‖ ^ ((k : ℝ) + α))) :=
    ENNReal.ofReal_le_ofReal (rpow_nat_pow_le_max (norm_nonneg Φ) hα.le hik)
  have hfac2 : ENNReal.ofReal (‖Φ‖ ^ ((i : ℝ) + α))
      ≤ ENNReal.ofReal (max 1 (‖Φ‖ ^ ((k : ℝ) + α))) :=
    ENNReal.ofReal_le_ofReal (rpow_add_le_max (norm_nonneg Φ) hα.le hik)
  rw [mul_add]
  exact add_le_add
    (le_trans (iterDerivNorm_comp_right_le Φ i (k : WithTop ℕ∞) hu hsd hpd hik')
      (mul_le_mul_left hfac1 _))
    (le_trans (holderSeminorm_comp_right_le Φ i (k : WithTop ℕ∞) hα hu hsd hpd hik')
      (mul_le_mul_left hfac2 _))

theorem holderNorm_comp_continuousLinearMap_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) {α : ℝ} (hα : 0 < α)
    (Φ : E →L[ℝ] F) :
    ∃ C : ℝ, 0 < C ∧ ∀ {t : Set F}, IsOpen t → ∀ u : F → ℂ, ContDiffOn ℝ k u t →
      Work.CR.Flat.holderNorm k α (fun x => u (Φ x)) (Φ ⁻¹' t)
        ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm k α u t :=
  ⟨max 1 (‖Φ‖ ^ ((k : ℝ) + α)), lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun {_t : Set F} ht u hu => holderNorm_comp_continuousLinearMap_le' k hα Φ ht hu⟩

/-- **Norm non-increasing pullback.**  If `‖Φ‖ ≤ 1` then pulling back by `Φ` does not increase the
`C^{k,α}` norm on the preimage of an open set. -/
theorem holderNorm_comp_continuousLinearMap_le_of_norm_le_one {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {k : ℕ} {α : ℝ} (hα : 0 < α) (Φ : E →L[ℝ] F) (hΦ : ‖Φ‖ ≤ 1) {t : Set F} (ht : IsOpen t)
    {u : F → ℂ} (hu : ContDiffOn ℝ k u t) :
    Work.CR.Flat.holderNorm k α (fun x => u (Φ x)) (Φ ⁻¹' t)
      ≤ Work.CR.Flat.holderNorm k α u t := by
  refine (holderNorm_comp_continuousLinearMap_le' k hα Φ ht hu).trans ?_
  have h1 : ‖Φ‖ ^ ((k : ℝ) + α) ≤ 1 :=
    Real.rpow_le_one (norm_nonneg Φ) hΦ (by positivity)
  have hC1 : max 1 (‖Φ‖ ^ ((k : ℝ) + α)) ≤ 1 := max_le le_rfl h1
  calc ENNReal.ofReal (max 1 (‖Φ‖ ^ ((k : ℝ) + α))) * Work.CR.Flat.holderNorm k α u t
      ≤ 1 * Work.CR.Flat.holderNorm k α u t :=
        mul_le_mul_left ((ENNReal.ofReal_le_one).mpr hC1) _
    _ = Work.CR.Flat.holderNorm k α u t := one_mul _

/-! ## 1b. Lowering the universe of the disc-extension hypothesis

`DiscExt` quantifies over spaces in an arbitrary universe `Type u`, while the polydisc `Fin n → ℂ`
lives in `Type 0`; inside the proof we apply the hypothesis to the type `ULift X`, which is a space
of type `Type u` when `X : Type 0`, and transport the statement back along the linear isometry
`ULift X ≃ X`.  This is what makes `DiscExt.down` below possible. -/

lemma mem_ball_zero_iff {z : ℂ} {r : ℝ} : z ∈ Metric.ball (0 : ℂ) r ↔ ‖z‖ < r := by
  rw [Metric.mem_ball, dist_eq_norm, sub_zero]

universe u

/-- **The disc extension at universe level `0`.**  From `DiscExt.{u} α c` (spaces in `Type u`) one
gets the same statement for spaces in `Type 0`, by transporting along `ULift`. -/
theorem discExt_lift {α c : ℝ} (hα0 : 0 < α) (hD : DiscExt.{u} α c) (X : Type)
    [NormedAddCommGroup X] [NormedSpace ℝ X] :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (U : Set X) (g : X × ℂ → ℂ), IsOpen U →
        (∀ m : ℕ, m ≤ k → ContDiffOn ℝ m g (U ×ˢ Metric.ball (0 : ℂ) 1)) →
        Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) 1) ≠ ⊤ →
        ∃ G : X × ℂ → ℂ,
          ContDiffOn ℝ (k : WithTop ENat) G (U ×ˢ Metric.ball (0 : ℂ) c) ∧
          (∀ p : X × ℂ, p.1 ∈ U → ‖p.2‖ < 1 → G p = g p) ∧
          Work.CR.Flat.holderNorm k α G (U ×ˢ Metric.ball (0 : ℂ) c)
            ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) 1) := by
  obtain ⟨D, hDpos, hDspec⟩ := hD (ULift.{u, 0} X)
  let e : ULift.{u, 0} X ≃ₗᵢ[ℝ] X := Work.CR.Flat.Holder.uliftLIE X
  let Ψ : ULift.{u, 0} X × ℂ →L[ℝ] X × ℂ :=
    ((e : ULift.{u, 0} X →L[ℝ] X).comp (ContinuousLinearMap.fst ℝ (ULift.{u, 0} X) ℂ)).prod
      (ContinuousLinearMap.snd ℝ (ULift.{u, 0} X) ℂ)
  let Θ : X × ℂ →L[ℝ] ULift.{u, 0} X × ℂ :=
    ((e.symm : X →L[ℝ] ULift.{u, 0} X).comp (ContinuousLinearMap.fst ℝ X ℂ)).prod
      (ContinuousLinearMap.snd ℝ X ℂ)
  have hΨapp : ∀ p : ULift.{u, 0} X × ℂ, Ψ p = (e p.1, p.2) := by intro p; simp [Ψ]
  have hΘapp : ∀ p : X × ℂ, Θ p = (e.symm p.1, p.2) := by intro p; simp [Θ]
  have hΨnorm : ‖Ψ‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
    rw [one_mul, hΨapp p, Prod.norm_def, Prod.norm_def]
    exact le_of_eq (by rw [LinearIsometryEquiv.norm_map])
  have hΘnorm : ‖Θ‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
    rw [one_mul, hΘapp p, Prod.norm_def, Prod.norm_def]
    exact le_of_eq (by rw [LinearIsometryEquiv.norm_map])
  refine ⟨D, hDpos, ?_⟩
  intro k U g hU hgsm hgfin
  have hU'open : IsOpen ((⇑e) ⁻¹' U) := hU.preimage e.continuous
  have hΨpre : Ψ ⁻¹' (U ×ˢ Metric.ball (0 : ℂ) 1) = (⇑e ⁻¹' U) ×ˢ Metric.ball (0 : ℂ) 1 := by
    ext p; simp [hΨapp]
  have hg'sm : ∀ m : ℕ, m ≤ k →
      ContDiffOn ℝ m (fun p : ULift.{u, 0} X × ℂ => g (Ψ p))
        ((⇑e ⁻¹' U) ×ˢ Metric.ball (0 : ℂ) 1) := by
    intro m hm
    have h1 := ContDiffOn.comp_continuousLinearMap (g := Ψ) (hgsm m hm)
    rwa [hΨpre] at h1
  have hg'le : Work.CR.Flat.holderNorm k α (fun p : ULift.{u, 0} X × ℂ => g (Ψ p))
        ((⇑e ⁻¹' U) ×ˢ Metric.ball (0 : ℂ) 1)
      ≤ Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) 1) := by
    have h1 := holderNorm_comp_continuousLinearMap_le_of_norm_le_one hα0 Ψ hΨnorm
      (hU.prod Metric.isOpen_ball) (hgsm k le_rfl)
    rwa [hΨpre] at h1
  have hg'fin : Work.CR.Flat.holderNorm k α (fun p : ULift.{u, 0} X × ℂ => g (Ψ p))
      ((⇑e ⁻¹' U) ×ˢ Metric.ball (0 : ℂ) 1) ≠ ⊤ := ne_top_of_le_ne_top hgfin hg'le
  obtain ⟨G', hG'sm, hG'ag, hG'norm⟩ :=
    hDspec k ((⇑e) ⁻¹' U) (fun p : ULift.{u, 0} X × ℂ => g (Ψ p)) hU'open hg'sm hg'fin
  have hΘpre : Θ ⁻¹' ((⇑e ⁻¹' U) ×ˢ Metric.ball (0 : ℂ) c) = U ×ˢ Metric.ball (0 : ℂ) c := by
    ext p
    simp only [Set.mem_preimage, Set.mem_prod, hΘapp p]
    rw [e.apply_symm_apply]
  have hΨΘ : ∀ p : X × ℂ, Ψ (Θ p) = p := by
    intro p
    rw [hΨapp, hΘapp]
    simp
  refine ⟨fun p => G' (Θ p), ?_, ?_, ?_⟩
  · have h1 := ContDiffOn.comp_continuousLinearMap (g := Θ) hG'sm
    rwa [hΘpre] at h1
  · intro p hpU hpz
    have hmem : Θ p ∈ (⇑e ⁻¹' U) ×ˢ Metric.ball (0 : ℂ) 1 := by
      refine ⟨?_, ?_⟩
      · rw [Set.mem_preimage, hΘapp]
        simpa using hpU
      · rw [hΘapp]
        simpa [Metric.mem_ball, dist_eq_norm] using hpz
    have h1 : G' (Θ p) = g (Ψ (Θ p)) := hG'ag _ hmem.1 (mem_ball_zero_iff.mp hmem.2)
    rwa [hΨΘ] at h1
  · have h1 := holderNorm_comp_continuousLinearMap_le_of_norm_le_one hα0 Θ hΘnorm
      (hU'open.prod Metric.isOpen_ball) hG'sm
    rw [hΘpre] at h1
    calc Work.CR.Flat.holderNorm k α (fun p : X × ℂ => G' (Θ p)) (U ×ˢ Metric.ball (0 : ℂ) c)
        ≤ Work.CR.Flat.holderNorm k α G' ((⇑e ⁻¹' U) ×ˢ Metric.ball (0 : ℂ) c) := h1
      _ ≤ ENNReal.ofReal (D k) * Work.CR.Flat.holderNorm k α
            (fun p : ULift.{u, 0} X × ℂ => g (Ψ p)) ((⇑e ⁻¹' U) ×ˢ Metric.ball (0 : ℂ) 1) :=
          hG'norm
      _ ≤ ENNReal.ofReal (D k) * Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) 1) :=
          mul_le_mul_right hg'le _

/-- `DiscExt` is downward closed in the universe: the level-`u` statement gives the level-`0`
statement. -/
theorem DiscExt.down {α c : ℝ} (hα0 : 0 < α) (hD : DiscExt.{u} α c) : DiscExt.{0} α c :=
  fun X _ _ => discExt_lift hα0 hD X

/-! ## 2. Rescaling the disc variable -/

/-- The rescaling `(z, w) ↦ (z, r • w)` of the disc variable, as a continuous linear map. -/
def scaleDiscLM (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] (r : ℝ) :
    X × ℂ →L[ℝ] X × ℂ :=
  (ContinuousLinearMap.fst ℝ X ℂ).prod (r • ContinuousLinearMap.snd ℝ X ℂ)

@[simp] lemma scaleDiscLM_apply {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (r : ℝ)
    (p : X × ℂ) : scaleDiscLM X r p = (p.1, r • p.2) := by
  simp [scaleDiscLM]

lemma norm_scaleDiscLM_le {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (r : ℝ)
    (hr : 0 ≤ r) (p : X × ℂ) : ‖scaleDiscLM X r p‖ ≤ max 1 r * ‖p‖ := by
  rw [scaleDiscLM_apply, Prod.norm_def, Prod.norm_def, norm_smul, Real.norm_of_nonneg hr]
  refine max_le ?_ ?_
  · calc ‖p.1‖ ≤ ‖p‖ := norm_fst_le p
      _ ≤ max 1 r * ‖p‖ := le_mul_of_one_le_left (norm_nonneg p) (le_max_left 1 r)
  · calc r * ‖p.2‖ ≤ r * ‖p‖ := mul_le_mul_of_nonneg_left (norm_snd_le p) hr
      _ ≤ max 1 r * ‖p‖ := mul_le_mul_of_nonneg_right (le_max_right 1 r) (norm_nonneg p)

lemma scaleDiscLM_preimage_ball {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {U : Set X} {r : ℝ} (hr : 0 < r) :
    scaleDiscLM X r ⁻¹' (U ×ˢ Metric.ball (0 : ℂ) r) = U ×ˢ Metric.ball (0 : ℂ) 1 := by
  ext p
  simp only [Set.mem_preimage, Set.mem_prod, Metric.mem_ball, dist_eq_norm, sub_zero,
    scaleDiscLM_apply, norm_smul, Real.norm_of_nonneg hr.le]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (mul_lt_mul_iff_right₀ hr).mp (by simpa using h2)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by simpa using (mul_lt_mul_iff_right₀ hr).mpr h2⟩

lemma scaleDiscLM_inv_preimage_ball {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {U : Set X} {r c : ℝ} (hr : 0 < r) :
    scaleDiscLM X r⁻¹ ⁻¹' (U ×ˢ Metric.ball (0 : ℂ) c) = U ×ˢ Metric.ball (0 : ℂ) (c * r) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_prod, Metric.mem_ball, dist_eq_norm, sub_zero,
    scaleDiscLM_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h3 : r⁻¹ * ‖p.2‖ * r < c * r := mul_lt_mul_of_pos_right h2 hr
    rwa [mul_comm (r⁻¹ * ‖p.2‖) r, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hr), one_mul] at h3
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have h4 : r⁻¹ * (c * r) = c := by
      rw [mul_comm c r, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hr), one_mul]
    have h3 : r⁻¹ * ‖p.2‖ < r⁻¹ * (c * r) := mul_lt_mul_of_pos_left h2 (inv_pos.mpr hr)
    rwa [h4] at h3

/-- **The one-variable disc extension at an arbitrary radius.**  `DiscExt α c` extends from
`U ×ˢ ball 0 1` to `U ×ˢ ball 0 c`; rescaling the disc variable gives the same statement with
`1` replaced by any `r > 0`, the constant depending on `r`. -/
theorem scaledDiscExt {α : ℝ} (hα0 : 0 < α) {c : ℝ} (hD : DiscExt.{0} α c) {r : ℝ} (hr : 0 < r)
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℝ X] :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (U : Set X) (g : X × ℂ → ℂ), IsOpen U →
        (∀ m : ℕ, m ≤ k → ContDiffOn ℝ m g (U ×ˢ Metric.ball (0 : ℂ) r)) →
        Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) r) ≠ ⊤ →
        ∃ G : X × ℂ → ℂ,
          ContDiffOn ℝ (k : WithTop ENat) G (U ×ˢ Metric.ball (0 : ℂ) (c * r)) ∧
          (∀ p : X × ℂ, p.1 ∈ U → ‖p.2‖ < r → G p = g p) ∧
          Work.CR.Flat.holderNorm k α G (U ×ˢ Metric.ball (0 : ℂ) (c * r))
            ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) r) := by
  have hr' : 0 < r⁻¹ := inv_pos.mpr hr
  obtain ⟨D, hDpos, hDspec⟩ := hD X
  choose A hApos hAspec using fun k : ℕ =>
    holderNorm_comp_continuousLinearMap_le k hα0 (scaleDiscLM X r)
  choose B hBpos hBspec using fun k : ℕ =>
    holderNorm_comp_continuousLinearMap_le k hα0 (scaleDiscLM X r⁻¹)
  refine ⟨fun k => B k * (D k * A k), fun k => mul_pos (hBpos k) (mul_pos (hDpos k) (hApos k)), ?_⟩
  intro k U g hU hgsm hgfin
  have hSpre := scaleDiscLM_preimage_ball (X := X) (U := U) hr
  have hTpre := scaleDiscLM_inv_preimage_ball (X := X) (U := U) (c := c) hr
  have hg'sm : ∀ m : ℕ, m ≤ k →
      ContDiffOn ℝ m (fun p : X × ℂ => g (scaleDiscLM X r p)) (U ×ˢ Metric.ball (0 : ℂ) 1) := by
    intro m hm
    have h1 := ContDiffOn.comp_continuousLinearMap (g := scaleDiscLM X r) (hgsm m hm)
    rwa [hSpre] at h1
  have hg'le : Work.CR.Flat.holderNorm k α (fun p : X × ℂ => g (scaleDiscLM X r p))
        (U ×ˢ Metric.ball (0 : ℂ) 1)
      ≤ ENNReal.ofReal (A k) * Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) r) := by
    have h1 := hAspec k (hU.prod Metric.isOpen_ball) g (hgsm k le_rfl)
    rwa [hSpre] at h1
  have hg'fin : Work.CR.Flat.holderNorm k α (fun p : X × ℂ => g (scaleDiscLM X r p))
      (U ×ˢ Metric.ball (0 : ℂ) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hgfin) hg'le
  obtain ⟨G', hG'sm, hG'ag, hG'norm⟩ :=
    hDspec k U (fun p : X × ℂ => g (scaleDiscLM X r p)) hU hg'sm hg'fin
  refine ⟨fun p => G' (scaleDiscLM X r⁻¹ p), ?_, ?_, ?_⟩
  · have h1 := ContDiffOn.comp_continuousLinearMap (g := scaleDiscLM X r⁻¹) hG'sm
    rwa [hTpre] at h1
  · intro p hpU hpr
    have hTmem : scaleDiscLM X r⁻¹ p ∈ U ×ˢ Metric.ball (0 : ℂ) 1 := by
      refine ⟨hpU, ?_⟩
      rw [Metric.mem_ball, dist_eq_norm, sub_zero, scaleDiscLM_apply, norm_smul,
        Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
      have hlt : r⁻¹ * ‖p.2‖ < 1 := by
        have h := mul_lt_mul_of_pos_left hpr hr'
        rwa [inv_mul_cancel₀ (ne_of_gt hr)] at h
      linarith
    have h1 : G' (scaleDiscLM X r⁻¹ p) = g (scaleDiscLM X r (scaleDiscLM X r⁻¹ p)) :=
      hG'ag _ hTmem.1 (mem_ball_zero_iff.mp hTmem.2)
    have hST : scaleDiscLM X r (scaleDiscLM X r⁻¹ p) = p := by
      rw [scaleDiscLM_apply, scaleDiscLM_apply]
      refine Prod.ext rfl ?_
      show r • (r⁻¹ • p.2) = p.2
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
    rwa [hST] at h1
  · have h1 := hBspec k (hU.prod Metric.isOpen_ball) G' hG'sm
    rw [hTpre] at h1
    calc Work.CR.Flat.holderNorm k α (fun p : X × ℂ => G' (scaleDiscLM X r⁻¹ p))
          (U ×ˢ Metric.ball (0 : ℂ) (c * r))
        ≤ ENNReal.ofReal (B k) * Work.CR.Flat.holderNorm k α G' (U ×ˢ Metric.ball (0 : ℂ) c) := h1
      _ ≤ ENNReal.ofReal (B k) * (ENNReal.ofReal (D k) *
            Work.CR.Flat.holderNorm k α (fun p : X × ℂ => g (scaleDiscLM X r p))
              (U ×ˢ Metric.ball (0 : ℂ) 1)) := mul_le_mul_right hG'norm _
      _ ≤ ENNReal.ofReal (B k) * (ENNReal.ofReal (D k) * (ENNReal.ofReal (A k) *
            Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) r))) :=
          mul_le_mul_right (mul_le_mul_right hg'le _) _
      _ = ENNReal.ofReal (B k * (D k * A k)) *
            Work.CR.Flat.holderNorm k α g (U ×ˢ Metric.ball (0 : ℂ) r) := by
          have e1 : ENNReal.ofReal (B k * (D k * A k))
              = ENNReal.ofReal (B k) * ENNReal.ofReal (D k * A k) :=
            ENNReal.ofReal_mul (hBpos k).le
          have e2 : ENNReal.ofReal (D k * A k)
              = ENNReal.ofReal (D k) * ENNReal.ofReal (A k) :=
            ENNReal.ofReal_mul (hDpos k).le
          rw [e1, e2]; ring

/-! ## 3. The insertion and deletion maps

`insert` inserts the second component of a pair as the `i`-th coordinate of a tuple, and `delete`
removes the `i`-th coordinate.  They are mutually inverse and both have operator norm `≤ 1`. -/

section InsertDelete

variable {n : ℕ}

/-- Insert the value in the extra coordinate at position `i`. -/
def insertLM (i : Fin n) :
    (({j : Fin n // j ≠ i} → ℂ) × ℂ) →ₗ[ℝ] (Fin n → ℂ) where
  toFun p := fun j => if h : j = i then p.2 else p.1 ⟨j, h⟩
  map_add' p q := by
    funext j
    by_cases h : j = i <;> simp [h]
  map_smul' a p := by
    funext j
    by_cases h : j = i <;> simp [h]

/-- Delete the `i`-th coordinate of a tuple. -/
def deleteLM (i : Fin n) : (Fin n → ℂ) →ₗ[ℝ] (({j : Fin n // j ≠ i} → ℂ) × ℂ) where
  toFun z := (fun j => z j.1, z i)
  map_add' p q := by
    refine Prod.ext ?_ ?_
    · funext j; rfl
    · rfl
  map_smul' a p := by
    refine Prod.ext ?_ ?_
    · funext j; rfl
    · rfl

@[simp] lemma insertLM_apply (i : Fin n) (p : ({j : Fin n // j ≠ i} → ℂ) × ℂ) :
    insertLM i p = fun j => if h : j = i then p.2 else p.1 ⟨j, h⟩ := rfl

@[simp] lemma deleteLM_apply (i : Fin n) (z : Fin n → ℂ) :
    deleteLM i z = (fun j => z j.1, z i) := rfl

@[simp] lemma insertLM_apply_same (i : Fin n) (p : ({j : Fin n // j ≠ i} → ℂ) × ℂ) :
    insertLM i p i = p.2 := by
  show (dite (i = i) (fun _ => p.2) (fun h => p.1 ⟨i, h⟩)) = p.2
  rw [dif_pos rfl]

@[simp] lemma insertLM_apply_of_ne (i : Fin n) (p : ({j : Fin n // j ≠ i} → ℂ) × ℂ)
    {j : Fin n} (h : j ≠ i) : insertLM i p j = p.1 ⟨j, h⟩ := by
  show (dite (j = i) (fun _ => p.2) (fun h' => p.1 ⟨j, h'⟩)) = p.1 ⟨j, h⟩
  rw [dif_neg h]

@[simp] lemma deleteLM_apply_fst (i : Fin n) (z : Fin n → ℂ) (j : {j : Fin n // j ≠ i}) :
    (deleteLM i z).1 j = z j.1 := rfl

@[simp] lemma deleteLM_apply_snd (i : Fin n) (z : Fin n → ℂ) : (deleteLM i z).2 = z i := rfl

lemma norm_insertLM_le (i : Fin n) (p : ({j : Fin n // j ≠ i} → ℂ) × ℂ) :
    ‖insertLM i p‖ ≤ ‖p‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg p)).mpr fun j => ?_
  by_cases h : j = i
  · rw [show insertLM i p j = p.2 from by simp [insertLM, h]]
    exact norm_snd_le p
  · rw [show insertLM i p j = p.1 ⟨j, h⟩ from by simp [insertLM, h]]
    exact le_trans (norm_le_pi_norm _ _) (norm_fst_le p)

lemma norm_deleteLM_le (i : Fin n) (z : Fin n → ℂ) : ‖deleteLM i z‖ ≤ ‖z‖ := by
  rw [deleteLM_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr fun j => ?_
    exact norm_le_pi_norm z j.1
  · exact norm_le_pi_norm z i

/-- The insertion map as a continuous linear map. -/
def insertCLM (i : Fin n) :
    (({j : Fin n // j ≠ i} → ℂ) × ℂ) →L[ℝ] (Fin n → ℂ) :=
  (insertLM i).mkContinuous 1 (fun p => by rw [one_mul]; exact norm_insertLM_le i p)

/-- The deletion map as a continuous linear map. -/
def deleteCLM (i : Fin n) :
    (Fin n → ℂ) →L[ℝ] (({j : Fin n // j ≠ i} → ℂ) × ℂ) :=
  (deleteLM i).mkContinuous 1 (fun z => by rw [one_mul]; exact norm_deleteLM_le i z)

lemma norm_insertCLM_le_one (i : Fin n) : ‖insertCLM i‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le (insertLM i) zero_le_one fun p => by
    rw [one_mul]; exact norm_insertLM_le i p

lemma norm_deleteCLM_le_one (i : Fin n) : ‖deleteCLM i‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le (deleteLM i) zero_le_one fun z => by
    rw [one_mul]; exact norm_deleteLM_le i z

@[simp] lemma insertCLM_apply (i : Fin n) (p : ({j : Fin n // j ≠ i} → ℂ) × ℂ) :
    insertCLM i p = insertLM i p := rfl

@[simp] lemma deleteCLM_apply (i : Fin n) (z : Fin n → ℂ) :
    deleteCLM i z = deleteLM i z := rfl

lemma insertLM_deleteLM (i : Fin n) (z : Fin n → ℂ) : insertLM i (deleteLM i z) = z := by
  funext j
  by_cases h : j = i
  · subst h; simp [insertLM, deleteLM]
  · simp [insertLM, deleteLM, h]

lemma deleteLM_insertLM (i : Fin n) (p : ({j : Fin n // j ≠ i} → ℂ) × ℂ) :
    deleteLM i (insertLM i p) = p := by
  refine Prod.ext ?_ ?_
  · funext j
    show insertLM i p j.1 = p.1 j
    simp [insertLM, j.2]
  · show insertLM i p i = p.2
    simp [insertLM]

lemma insertCLM_deleteCLM (i : Fin n) (z : Fin n → ℂ) : insertCLM i (deleteCLM i z) = z := by
  rw [insertCLM_apply, deleteCLM_apply, insertLM_deleteLM]

/-- Membership of the polydisc in terms of the coordinate norms. -/
lemma mem_polydisc_iff {n : ℕ} {σ : Fin n → ℝ} {z : Fin n → ℂ} :
    z ∈ polydisc 0 σ ↔ ∀ j, ‖z j‖ < σ j := by
  simp only [mem_polydisc, Pi.zero_apply, sub_zero]

/-- The preimage of a polydisc under the insertion map. -/
lemma insertCLM_preimage_polydisc (i : Fin n) (σ : Fin n → ℝ) :
    insertCLM i ⁻¹' (polydisc 0 σ)
      = {p : ({j : Fin n // j ≠ i} → ℂ) × ℂ | (∀ j, ‖p.1 j‖ < σ j.1) ∧ ‖p.2‖ < σ i} := by
  ext p
  rw [Set.mem_preimage, mem_polydisc_iff, Set.mem_ofPred_eq]
  constructor
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · have hh := h j.1
      rw [insertCLM_apply, insertLM_apply_of_ne i p j.2] at hh
      exact hh
    · have hh := h i
      rw [insertCLM_apply, insertLM_apply_same] at hh
      exact hh
  · rintro ⟨h1, h2⟩ j
    by_cases h : j = i
    · subst h
      rw [insertCLM_apply, insertLM_apply_same]
      exact h2
    · rw [insertCLM_apply, insertLM_apply_of_ne i p h]
      exact h1 ⟨j, h⟩

/-- The preimage of the product of the parameter region and a disc under the deletion map. -/
lemma deleteCLM_preimage_prod (i : Fin n) (σ : Fin n → ℝ) (r : ℝ) :
    deleteCLM i ⁻¹'
        ({w : {j : Fin n // j ≠ i} → ℂ | ∀ j, ‖w j‖ < σ j.1} ×ˢ Metric.ball (0 : ℂ) r)
      = polydisc 0 (Function.update σ i r) := by
  ext z
  rw [Set.mem_preimage, Set.mem_prod, Set.mem_ofPred_eq, mem_polydisc_iff, Metric.mem_ball,
    dist_eq_norm, sub_zero, deleteCLM_apply, deleteLM_apply]
  show ((∀ j : {j : Fin n // j ≠ i}, ‖z j.1‖ < σ j.1) ∧ ‖z i‖ < r) ↔
      (∀ j : Fin n, ‖z j‖ < Function.update σ i r j)
  constructor
  · rintro ⟨h1, h2⟩ j
    rw [Function.update_apply]
    by_cases h : j = i
    · subst h
      rw [if_pos rfl]; exact h2
    · rw [if_neg h]; exact h1 ⟨j, h⟩
  · intro h
    refine ⟨fun j => ?_, ?_⟩
    · have hh := h j.1
      rwa [Function.update_of_ne j.2] at hh
    · have hh := h i
      rwa [Function.update_apply, if_pos rfl] at hh

end InsertDelete

/-- The intermediate multiradii: the coordinates `< i` have already been scaled up by `c`. -/
def interRadii {n : ℕ} (ρ : Fin n → ℝ) (c : ℝ) (i : ℕ) : Fin n → ℝ :=
  fun j => if (j : ℕ) < i then c * ρ j else ρ j

@[simp] lemma interRadii_apply {n : ℕ} (ρ : Fin n → ℝ) (c : ℝ) (i : ℕ) (j : Fin n) :
    interRadii ρ c i j = if (j : ℕ) < i then c * ρ j else ρ j := rfl

/-! ## 4. One coordinate step -/

/-- **One step of the coordinate-by-coordinate extension.**  The `i`-th coordinate is extended
from radius `σ i` to radius `c * σ i`; all other radii are unchanged.  The constant depends only on
the radii (through the disc extension at radius `σ i`) and on the order. -/
theorem exists_extension_coord {n : ℕ} (i : Fin n) {α : ℝ} (hα0 : 0 < α) {c : ℝ}
    (hD : DiscExt.{0} α c) {σ : Fin n → ℝ} (hσ : 0 < σ i) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (f : (Fin n → ℂ) → ℂ),
        (∀ m : ℕ, m ≤ k → ContDiffOn ℝ m f (polydisc 0 σ)) →
        Work.CR.Flat.holderNorm k α f (polydisc 0 σ) ≠ ⊤ →
        ∃ f' : (Fin n → ℂ) → ℂ,
          ContDiffOn ℝ (k : WithTop ENat) f' (polydisc 0 (Function.update σ i (c * σ i))) ∧
          (∀ z ∈ polydisc 0 σ, f' z = f z) ∧
          Work.CR.Flat.holderNorm k α f' (polydisc 0 (Function.update σ i (c * σ i)))
            ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α f (polydisc 0 σ) := by
  obtain ⟨D, hDpos, hDspec⟩ :=
    scaledDiscExt (X := {j : Fin n // j ≠ i} → ℂ) hα0 hD hσ
  refine ⟨D, hDpos, ?_⟩
  intro k f hf hffin
  set U : Set ({j : Fin n // j ≠ i} → ℂ) := {w | ∀ j, ‖w j‖ < σ j.1} with hUdef
  have hUopen : IsOpen U := by
    have hUeq : U = ⋂ j, {w : {j : Fin n // j ≠ i} → ℂ | ‖w j‖ < σ j.1} := by
      ext w; simp [hUdef]
    rw [hUeq]
    exact isOpen_iInter_of_finite fun j =>
      isOpen_lt (continuous_apply j |>.norm) continuous_const
  have hUball : insertCLM i ⁻¹' (polydisc 0 σ) = U ×ˢ Metric.ball (0 : ℂ) (σ i) := by
    rw [insertCLM_preimage_polydisc]
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Metric.mem_ball, dist_eq_norm, sub_zero, hUdef]
  have hgsm : ∀ m : ℕ, m ≤ k →
      ContDiffOn ℝ m (fun p : ({j : Fin n // j ≠ i} → ℂ) × ℂ => f (insertCLM i p))
        (U ×ˢ Metric.ball (0 : ℂ) (σ i)) := by
    intro m hm
    have h1 := ContDiffOn.comp_continuousLinearMap (g := insertCLM i) (hf m hm)
    rwa [hUball] at h1
  have hgle : Work.CR.Flat.holderNorm k α
        (fun p : ({j : Fin n // j ≠ i} → ℂ) × ℂ => f (insertCLM i p))
        (U ×ˢ Metric.ball (0 : ℂ) (σ i))
      ≤ Work.CR.Flat.holderNorm k α f (polydisc 0 σ) := by
    have h1 := holderNorm_comp_continuousLinearMap_le_of_norm_le_one hα0 (insertCLM i)
      (norm_insertCLM_le_one i) (isOpen_polydisc 0 σ) (hf k le_rfl)
    rwa [hUball] at h1
  have hgfin : Work.CR.Flat.holderNorm k α
      (fun p : ({j : Fin n // j ≠ i} → ℂ) × ℂ => f (insertCLM i p))
      (U ×ˢ Metric.ball (0 : ℂ) (σ i)) ≠ ⊤ := ne_top_of_le_ne_top hffin hgle
  obtain ⟨G, hGsm, hGag, hGnorm⟩ :=
    hDspec k U (fun p : ({j : Fin n // j ≠ i} → ℂ) × ℂ => f (insertCLM i p)) hUopen hgsm hgfin
  refine ⟨fun z => G (deleteCLM i z), ?_, ?_, ?_⟩
  · have h1 := ContDiffOn.comp_continuousLinearMap (g := deleteCLM i) hGsm
    rw [hUdef] at h1
    rwa [deleteCLM_preimage_prod] at h1
  · intro z hz
    have hmem : deleteCLM i z ∈ U ×ˢ Metric.ball (0 : ℂ) (σ i) := by
      rw [← hUball, Set.mem_preimage, insertCLM_deleteCLM]
      exact hz
    have h2 : ‖(deleteCLM i z).2‖ < σ i := by
      have h3 := hmem.2
      rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at h3
    have h1 : G (deleteCLM i z) = f (insertCLM i (deleteCLM i z)) := hGag _ hmem.1 h2
    rwa [insertCLM_deleteCLM] at h1
  · have h1 := holderNorm_comp_continuousLinearMap_le_of_norm_le_one hα0 (deleteCLM i)
      (norm_deleteCLM_le_one i) (hUopen.prod Metric.isOpen_ball) hGsm
    rw [hUdef] at h1
    rw [deleteCLM_preimage_prod] at h1
    calc Work.CR.Flat.holderNorm k α (fun z => G (deleteCLM i z))
          (polydisc 0 (Function.update σ i (c * σ i)))
        ≤ Work.CR.Flat.holderNorm k α G (U ×ˢ Metric.ball (0 : ℂ) (c * σ i)) := h1
      _ ≤ ENNReal.ofReal (D k) * Work.CR.Flat.holderNorm k α
            (fun p : ({j : Fin n // j ≠ i} → ℂ) × ℂ => f (insertCLM i p))
            (U ×ˢ Metric.ball (0 : ℂ) (σ i)) := hGnorm
      _ ≤ ENNReal.ofReal (D k) * Work.CR.Flat.holderNorm k α f (polydisc 0 σ) :=
          mul_le_mul_right hgle _

/-! ## 5. The assembly -/

theorem one_sided_extension_le_of_discExt {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {c : ℝ}
    (hc : 1 < c) (hD : Work.NN.Final.DiscExt α c) :
    ∀ (n : ℕ) (ρ : Fin n → ℝ), (∀ j, 0 < ρ j) →
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (v : (Fin n → ℂ) → ℂ),
        (∀ m : ℕ, ContDiffOn ℝ m v (Work.NN.Final.pd n ρ 1)) →
        Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1) ≠ ⊤ →
        ∃ vtilde : (Fin n → ℂ) → ℂ,
          ContDiffOn ℝ (k : WithTop ENat) vtilde (Work.NN.Final.pd n ρ c) ∧
          (∀ z ∈ Work.NN.Final.pd n ρ 1, vtilde z = v z) ∧
          Work.CR.Flat.holderNorm k α vtilde (Work.NN.Final.pd n ρ c)
            ≤ ENNReal.ofReal (C k) * Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1) := by
  intro n ρ hρ
  have hD0 : DiscExt.{0} α c := hD.down hα0
  have hmu0_pd : polydisc 0 (interRadii ρ c 0) = Work.NN.Final.pd n ρ 1 := by
    have h1 : interRadii ρ c 0 = fun j => 1 * ρ j := by
      funext j
      rw [interRadii_apply, if_neg (Nat.not_lt_zero _), one_mul]
    rw [h1]; rfl
  have hmun_pd : polydisc 0 (interRadii ρ c n) = Work.NN.Final.pd n ρ c := by
    have h1 : interRadii ρ c n = fun j => c * ρ j := by
      funext j
      rw [interRadii_apply, if_pos j.isLt]
    rw [h1]; rfl
  have hmono : ∀ {i i' : ℕ}, i ≤ i' →
      polydisc 0 (interRadii ρ c i) ⊆ polydisc 0 (interRadii ρ c i') := by
    intro i i' hii'
    refine polydisc_mono fun j => ?_
    rw [interRadii_apply, interRadii_apply]
    by_cases h : (j : ℕ) < i
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h]
      by_cases h2 : (j : ℕ) < i'
      · rw [if_pos h2]
        exact le_mul_of_one_le_left (le_of_lt (hρ j)) (le_of_lt hc)
      · rw [if_neg h2]
  have hsucc : ∀ (i : ℕ) (hi : i < n),
      interRadii ρ c (i + 1) =
        Function.update (interRadii ρ c i) ⟨i, hi⟩ (c * interRadii ρ c i ⟨i, hi⟩) := by
    intro i hi
    funext j
    rw [interRadii_apply, Function.update_apply]
    by_cases h : j = ⟨i, hi⟩
    · subst h
      rw [if_pos (by simp), if_pos rfl]
      congr 1
      rw [interRadii_apply, Fin.val_mk, if_neg (lt_irrefl i)]
    · rw [if_neg h, interRadii_apply]
      have hj : (j : ℕ) ≠ i := fun hh => h (Fin.ext hh)
      by_cases h2 : (j : ℕ) < i
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]
  have hσi : ∀ i : Fin n, 0 < interRadii ρ c i i := by
    intro i
    rw [interRadii_apply, if_neg (lt_irrefl _)]
    exact hρ i
  have key : ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (v : (Fin n → ℂ) → ℂ),
      (∀ m : ℕ, ContDiffOn ℝ m v (Work.NN.Final.pd n ρ 1)) →
      Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1) ≠ ⊤ →
      ∃ vtilde : (Fin n → ℂ) → ℂ,
        ContDiffOn ℝ (k : WithTop ENat) vtilde (Work.NN.Final.pd n ρ c) ∧
        (∀ z ∈ Work.NN.Final.pd n ρ 1, vtilde z = v z) ∧
        Work.CR.Flat.holderNorm k α vtilde (Work.NN.Final.pd n ρ c)
          ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm k α v (Work.NN.Final.pd n ρ 1) := by
    intro k
    choose E hEpos hEspec using fun i : Fin n =>
      exists_extension_coord (i := i) hα0 hD0 (σ := interRadii ρ c i) (hσi i)
    set D : ℝ := (∑ i : Fin n, E i k) + 1 with hDdef
    have hsum0 : 0 ≤ ∑ i : Fin n, E i k := Finset.sum_nonneg fun i _ => (hEpos i k).le
    have hDpos : 0 < D := by rw [hDdef]; linarith
    have hEle : ∀ i : Fin n, E i k ≤ D := by
      intro i
      have h1 : E i k ≤ ∑ j : Fin n, E j k :=
        Finset.single_le_sum (fun j _ => (hEpos j k).le) (Finset.mem_univ i)
      rw [hDdef]; linarith
    refine ⟨D ^ n, pow_pos hDpos n, fun v hv hvfin => ?_⟩
    have hv' : ∀ m : ℕ, m ≤ k → ContDiffOn ℝ m v (polydisc 0 (interRadii ρ c 0)) := by
      intro m hm
      rw [hmu0_pd]
      exact hv m
    have hvfin' : Work.CR.Flat.holderNorm k α v (polydisc 0 (interRadii ρ c 0)) ≠ ⊤ := by
      rw [hmu0_pd]; exact hvfin
    have aux : ∀ i ≤ n, ∃ (f : (Fin n → ℂ) → ℂ),
        ContDiffOn ℝ (k : WithTop ENat) f (polydisc 0 (interRadii ρ c i)) ∧
        (∀ z ∈ polydisc 0 (interRadii ρ c 0), f z = v z) ∧
        Work.CR.Flat.holderNorm k α f (polydisc 0 (interRadii ρ c i))
          ≤ ENNReal.ofReal (D ^ i) *
            Work.CR.Flat.holderNorm k α v (polydisc 0 (interRadii ρ c 0)) := by
      intro i
      induction i with
      | zero =>
          intro _
          exact ⟨v, hv' k le_rfl, fun z hz => rfl, by
            rw [pow_zero, ENNReal.ofReal_one, one_mul]⟩
      | succ i ih =>
          intro hk1
          have hi_lt : i < n := Nat.lt_of_succ_le hk1
          have hk : i ≤ n := Nat.le_of_lt hi_lt
          obtain ⟨f, hfsm, hfag, hfnorm⟩ := ih hk
          have hfne : Work.CR.Flat.holderNorm k α f (polydisc 0 (interRadii ρ c i)) ≠ ⊤ :=
            ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hvfin') hfnorm
          obtain ⟨f', hf'sm, hf'ag, hf'norm⟩ :=
            hEspec ⟨i, hi_lt⟩ k f (fun m hm => hfsm.of_le (by exact_mod_cast hm)) hfne
          refine ⟨f', ?_, ?_, ?_⟩
          · rw [hsucc i hi_lt]; exact hf'sm
          · intro z hz
            rw [hf'ag z (hmono (Nat.zero_le i) hz), hfag z hz]
          · rw [hsucc i hi_lt]
            calc Work.CR.Flat.holderNorm k α f'
                  (polydisc 0 (Function.update (interRadii ρ c i) ⟨i, hi_lt⟩
                    (c * interRadii ρ c i ⟨i, hi_lt⟩)))
                ≤ ENNReal.ofReal (E ⟨i, hi_lt⟩ k) *
                    Work.CR.Flat.holderNorm k α f (polydisc 0 (interRadii ρ c i)) := hf'norm
              _ ≤ ENNReal.ofReal D * (ENNReal.ofReal (D ^ i) *
                    Work.CR.Flat.holderNorm k α v (polydisc 0 (interRadii ρ c 0))) :=
                  mul_le_mul' (ENNReal.ofReal_le_ofReal (hEle ⟨i, hi_lt⟩)) hfnorm
              _ = ENNReal.ofReal (D ^ (i + 1)) *
                    Work.CR.Flat.holderNorm k α v (polydisc 0 (interRadii ρ c 0)) := by
                  rw [pow_succ', ENNReal.ofReal_mul hDpos.le]
                  ring
    obtain ⟨f, hfsm, hfag, hfnorm⟩ := aux n le_rfl
    exact ⟨f, by rwa [hmun_pd] at hfsm,
      fun z hz => hfag z (by rwa [← hmu0_pd] at hz),
      by rwa [hmun_pd, hmu0_pd] at hfnorm⟩
  choose C hCpos hCspec using key
  exact ⟨C, hCpos, hCspec⟩

end Work.NN.Final
