import Mathlib
import Submission.Work.Noncompact.CompressionTube.Notation

/-!
# The model hairpin in a tube

This file proves `Work.Drive.Rays.hairpinOfRayTube`: a smooth, injective, proper immersion
`γ : ℝ → M` through a point `b` inside a set `W`, obtained by pushing the **model hairpin**

  `u ↦ (((2 / π) * arctan u) • e₁, u²)`

of the half-strip `{‖p.1‖ ≤ 1, 0 ≤ p.2}` through a map `Ψ : ℝ^{n-1} × ℝ → M` which is injective and
an immersion on that half-strip, maps it into `W`, sends `(0,0)` to `b` and escapes to `+∞` in the
second coordinate.

The hairpin lives in the half-strip, is injective, is an immersion (`u ≠ 0` is handled by the second
coordinate `u²`, `u = 0` by the first coordinate whose derivative `(2/π) • e₁` is nonzero), and its
second coordinate escapes both ways, which makes the composite proper.

## Main declarations

* `modelHairpin`: the model hairpin curve;
* `contMDiff_modelHairpin`, `modelHairpin_injective`, `modelHairpin_comp_sub_mfderiv_injective`: the
  regularity, injectivity and immersion properties;
* `norm_fst_modelHairpin_le`: it lands in the half-strip;
* `hairpinOfRayTube`: the theorem.
-/

namespace Work.Drive.Rays

open scoped Manifold ContDiff
open Work.Noncompact.CompressionTube

noncomputable section

/-! ### Two elementary facts about derivatives -/

/-- A continuous linear map out of `ℝ` that does not vanish at `1` is injective. -/
lemma injective_of_apply_one_ne_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : ℝ →L[ℝ] F) (h : L 1 ≠ 0) : Function.Injective L := by
  have hkey : ∀ v : ℝ, L v = v • L 1 := fun v => by
    calc L v = L ((v : ℝ) • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
      _ = v • L 1 := by rw [map_smul]
  intro a b hab
  rw [hkey a, hkey b] at hab
  have h3 : (a - b) • L 1 = 0 := by rw [sub_smul, hab, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · exact sub_eq_zero.mp h4
  · exact absurd h4 h

/-- A scalar function with nonzero derivative at a point has injective `fderiv` there. -/
lemma injective_fderiv_of_deriv_ne {f : ℝ → ℝ} {u : ℝ} (h : deriv f u ≠ 0) :
    Function.Injective (fderiv ℝ f u) := by
  refine injective_of_apply_one_ne_zero (fderiv ℝ f u) ?_
  rwa [fderiv_apply_one_eq_deriv]

/-- A product of continuous linear maps is injective as soon as its first factor is. -/
lemma injective_prod_left {M₁ M₂ M₃ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁]
    [Module ℝ M₁] [TopologicalSpace M₂] [AddCommMonoid M₂] [Module ℝ M₂]
    [TopologicalSpace M₃] [AddCommMonoid M₃] [Module ℝ M₃]
    {L₁ : M₁ →L[ℝ] M₂} {L₂ : M₁ →L[ℝ] M₃} (h : Function.Injective L₁) :
    Function.Injective (L₁.prod L₂) := fun _ _ hab => h (congrArg Prod.fst hab)

/-- A product of continuous linear maps is injective as soon as its second factor is. -/
lemma injective_prod_right {M₁ M₂ M₃ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁]
    [Module ℝ M₁] [TopologicalSpace M₂] [AddCommMonoid M₂] [Module ℝ M₂]
    [TopologicalSpace M₃] [AddCommMonoid M₃] [Module ℝ M₃]
    {L₁ : M₁ →L[ℝ] M₂} {L₂ : M₁ →L[ℝ] M₃} (h : Function.Injective L₂) :
    Function.Injective (L₁.prod L₂) := fun _ _ hab => h (congrArg Prod.snd hab)

/-- The product model of `ℝ^{n-1} × ℝ` is the self model of the product space. -/
lemma mcprod_eq_self (n : ℕ) :
    MCprod n = 𝓘(ℝ, EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := by
  rw [modelWithCornersSelf_prod]

/-! ### The model hairpin -/

/-- **The model hairpin**: `u ↦ ((δ * arctan u) • e, u ^ 2)`. -/
def modelHairpin {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (δ : ℝ) (e : F) :
    ℝ → F × ℝ := fun u => ((δ * Real.arctan u) • e, u ^ 2)

@[simp] lemma modelHairpin_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (δ : ℝ) (e : F) (u : ℝ) : modelHairpin δ e u = ((δ * Real.arctan u) • e, u ^ 2) := rfl

/-- The bound `|(2/π) * arctan u| ≤ 1` which keeps the hairpin in the half-strip. -/
lemma abs_two_div_pi_mul_arctan_le (u : ℝ) : |(2 / Real.pi) * Real.arctan u| ≤ 1 := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 / Real.pi)]
  have h2 : |Real.arctan u| ≤ Real.pi / 2 :=
    abs_le.mpr ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan u),
      le_of_lt (Real.arctan_lt_pi_div_two u)⟩
  calc (2 / Real.pi) * |Real.arctan u| ≤ (2 / Real.pi) * (Real.pi / 2) := by gcongr
    _ = 1 := by field_simp

/-- The model hairpin stays in the strip `{‖·‖ ≤ 1, 0 ≤ ·}` as soon as `e` is a unit vector. -/
lemma norm_fst_modelHairpin_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {e : F} (he : ‖e‖ = 1) (u : ℝ) : ‖(modelHairpin (2 / Real.pi) e u).1‖ ≤ 1 := by
  rw [modelHairpin, norm_smul, Real.norm_eq_abs, he, mul_one]
  exact abs_two_div_pi_mul_arctan_le u

lemma snd_modelHairpin_nonneg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (δ : ℝ) (e : F) (u : ℝ) : 0 ≤ (modelHairpin δ e u).2 := by
  rw [modelHairpin]; positivity

/-- **Smoothness of the model hairpin.** -/
lemma contMDiff_modelHairpin {n : ℕ} (δ : ℝ) (e : EuclideanSpace ℝ (Fin (n - 1))) :
    ContMDiff MCreal (MCprod n) smoothOrder (modelHairpin δ e) := by
  rw [mcprod_eq_self n, contMDiff_iff_contDiff]
  refine ContDiff.prodMk ?_ ?_
  · exact ContDiff.smul_const
      (contDiff_const.mul (Real.contDiff_arctan (n := smoothOrder))) e
  · exact contDiff_id.pow 2

/-- **Smoothness of a translated model hairpin.** -/
lemma contMDiff_modelHairpin_comp_sub {n : ℕ} (δ : ℝ)
    (e : EuclideanSpace ℝ (Fin (n - 1))) (c : ℝ) :
    ContMDiff MCreal (MCprod n) smoothOrder (fun t : ℝ => modelHairpin δ e (t - c)) := by
  rw [mcprod_eq_self n, contMDiff_iff_contDiff]
  refine ContDiff.prodMk ?_ ?_
  · exact ContDiff.smul_const (contDiff_const.mul
      ((Real.contDiff_arctan (n := smoothOrder)).comp (contDiff_id.sub contDiff_const))) e
  · exact (contDiff_id.sub contDiff_const).pow 2

/-- **Injectivity of the model hairpin** (δ and e nonzero).

The second coordinate `u ^ 2` only determines `u` up to sign; the first coordinate, odd in `u`
through `arctan`, then forces `u = 0` in the negative case. -/
lemma modelHairpin_injective {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {δ : ℝ} (hδ : δ ≠ 0) {e : F} (he : e ≠ 0) : Function.Injective (modelHairpin δ e) := by
  intro u v huv
  have h2 : u ^ 2 = v ^ 2 := by simpa using congrArg Prod.snd huv
  have h1 : δ * Real.arctan u = δ * Real.arctan v := by
    refine (smul_left_inj he).mp ?_
    simpa using congrArg Prod.fst huv
  have hv : Real.arctan u = Real.arctan v := mul_left_cancel₀ hδ h1
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
  · exact h
  · rw [h, Real.arctan_neg] at hv
    have hz : Real.arctan v = 0 := by linarith
    have hv0 : v = 0 := Real.arctan_injective (by rw [hz, Real.arctan_zero])
    rw [h, hv0, neg_zero]

/-- Injectivity of a translated model hairpin. -/
lemma modelHairpin_comp_sub_injective {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {δ : ℝ} (hδ : δ ≠ 0) {e : F} (he : e ≠ 0) (c : ℝ) :
    Function.Injective (fun t : ℝ => modelHairpin δ e (t - c)) := by
  intro t t' htt'
  have h : t - c = t' - c := modelHairpin_injective hδ he htt'
  linarith

/-- The `fderiv` of a translated model hairpin, split into its two components. -/
lemma fderiv_modelHairpin_comp_sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (δ : ℝ) (e : F) (c t : ℝ) :
    fderiv ℝ (fun s : ℝ => modelHairpin δ e (s - c)) t
      = (fderiv ℝ (fun s : ℝ => (δ * Real.arctan (s - c)) • e) t).prod
        (fderiv ℝ (fun s : ℝ => (s - c) ^ 2) t) := by
  have h1 : ContDiff ℝ smoothOrder (fun s : ℝ => (δ * Real.arctan (s - c)) • e) :=
    ContDiff.smul_const (contDiff_const.mul
      ((Real.contDiff_arctan (n := smoothOrder)).comp (contDiff_id.sub contDiff_const))) e
  have h2 : ContDiff ℝ smoothOrder (fun s : ℝ => (s - c) ^ 2) :=
    (contDiff_id.sub contDiff_const).pow 2
  refine DifferentiableAt.fderiv_prodMk ?_ ?_
  · exact (h1.differentiable (by simp [smoothOrder])).differentiableAt
  · exact (h2.differentiable (by simp [smoothOrder])).differentiableAt

/-- **The translated model hairpin is an immersion.**  At `t = c` the derivative is
`(2/π)•e ≠ 0` in the first coordinate, at `t ≠ c` the second coordinate `(t-c)²` has nonzero
derivative `2(t-c)`. -/
lemma modelHairpin_comp_sub_mfderiv_injective {n : ℕ} {δ : ℝ} (hδ : δ ≠ 0)
    {e : EuclideanSpace ℝ (Fin (n - 1))} (he : e ≠ 0) (c : ℝ) :
    ∀ t : ℝ,
      Function.Injective (mfderiv MCreal (MCprod n) (fun t : ℝ => modelHairpin δ e (t - c)) t) := by
  intro t
  rw [mcprod_eq_self n, mfderiv_eq_fderiv, fderiv_modelHairpin_comp_sub δ e c t]
  change Function.Injective
    ((fderiv ℝ (fun s : ℝ => (δ * Real.arctan (s - c)) • e) t).prod
      (fderiv ℝ (fun s : ℝ => (s - c) ^ 2) t))
  by_cases htc : t = c
  · rw [htc]
    refine injective_prod_left ?_
    refine injective_of_apply_one_ne_zero _ ?_
    rw [fderiv_apply_one_eq_deriv, deriv_smul_const]
    · rw [show deriv (fun s : ℝ => δ * Real.arctan (s - c)) c = δ by simp]
      exact smul_ne_zero hδ he
    · have h : ContDiff ℝ smoothOrder (fun s : ℝ => δ * Real.arctan (s - c)) :=
        contDiff_const.mul
          ((Real.contDiff_arctan (n := smoothOrder)).comp (contDiff_id.sub contDiff_const))
      exact (h.differentiable (by simp [smoothOrder])).differentiableAt
  · refine injective_prod_right ?_
    refine injective_fderiv_of_deriv_ne ?_
    rw [show deriv (fun s : ℝ => (s - c) ^ 2) t = 2 * (t - c) by simp]
    exact mul_ne_zero two_ne_zero (sub_ne_zero.mpr htc)

end

open scoped Manifold ContDiff in
open Work.Noncompact.CompressionTube in
/-- **The model hairpin in a tube.**  Given a smooth map `Ψ : ℝ^{n-1} × ℝ → M` which is injective
and an immersion on the half-strip `{‖p.1‖ ≤ 1, 0 ≤ p.2}`, maps that half-strip into the set `W`,
sends `(0,0)` to `b` and escapes to `+∞` in the second coordinate, there is a smooth, injective,
proper, immersed line `γ : ℝ → M` with `γ 1 = b` and `Set.range γ ⊆ W`.

PROOF.  Take `e₁ := (EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin (n-1)))` (nonzero
since `n ≥ 2`), `ψ u := u / Real.sqrt (1 + u^2)` (or `Real.tanh`; smooth, `ψ 0 = 0`, `|ψ| ≤ 1`,
`ψ` injective with `deriv ψ 0 ≠ 0`), `δ := 1/2`, and
`h u := (((δ * ψ u) • e₁), u^2) : ℝ^{n-1} × ℝ`.  Set `γ t := Ψ (h (t - 1))`.  Then:
* `h` is smooth, `h 0 = (0, 0)`, hence `γ 1 = Ψ (0,0) = b`;
* `h` maps into the half-strip: `‖(h u).1‖ ≤ 1/2 ≤ 1`, `(h u).2 = u^2 ≥ 0`;
* `h` is injective: `(h u).2 = (h u').2` gives `u' = ±u`, and the first coordinate (via `ψ`
  injective and odd-ish) gives `u = u'`;
* `h` is an immersion: `fderiv ℝ h u = (·) • ((δ * deriv ψ u) • e₁, 2 * u)` is nonzero
  (`u ≠ 0` gives the second component; `u = 0` gives `δ • e₁` in the first, since `deriv ψ 0 = 1`);
* `γ` is `C^∞` (chain rule along `h`), injective (from `hΨinj`), an immersion (chain rule +
  `hΨimm`), has image in `W` (from `hΨW`), and is proper: for compact `K` take `S` from `hΨesc`;
  if `γ t ∈ K` then `Ψ (h (t-1)) ∈ K` with `‖(h (t-1)).1‖ ≤ 1`, which forces `(t-1)^2 < S`
  (when `S ≤ 0` this is immediate: then already `Ψ (h (t-1)) ∉ K`), so `γ ⁻¹' K` is closed and
  bounded, hence compact. -/
theorem hairpinOfRayTube {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (MC n) smoothOrder M]
    [T2Space M] [SecondCountableTopology M]
    {W : Set M} {b : M}
    {Ψ : EuclideanSpace ℝ (Fin (n - 1)) × ℝ → M}
    (hΨsm : ContMDiff (MCprod n) (MC n) smoothOrder Ψ)
    (hΨ0 : Ψ ((0 : EuclideanSpace ℝ (Fin (n - 1))), 0) = b)
    (hΨinj : Set.InjOn Ψ {p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ | ‖p.1‖ ≤ 1 ∧ 0 ≤ p.2})
    (hΨimm : ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 → 0 ≤ p.2 →
      Function.Injective (mfderiv (MCprod n) (MC n) Ψ p))
    (hΨW : ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ, ‖p.1‖ ≤ 1 → 0 ≤ p.2 → Ψ p ∈ W)
    (hΨesc : ∀ K : Set M, IsCompact K → ∃ S : ℝ, ∀ p : EuclideanSpace ℝ (Fin (n - 1)) × ℝ,
      ‖p.1‖ ≤ 1 → S ≤ p.2 → Ψ p ∉ K) :
    ∃ γ : ℝ → M, γ 1 = b ∧ ContMDiff MCreal (MC n) smoothOrder γ ∧ Function.Injective γ ∧
      IsProperMap γ ∧ (∀ t : ℝ, Function.Injective (mfderiv MCreal (MC n) γ t)) ∧
      Set.range γ ⊆ W := by
  classical
  -- the unit direction of the strip, and the model hairpin through `(0, 0)`
  set i : Fin (n - 1) := ⟨0, by omega⟩ with hi
  set e : EuclideanSpace ℝ (Fin (n - 1)) := EuclideanSpace.single i (1 : ℝ) with he
  have he_norm : ‖e‖ = 1 := by rw [he]; simpa using EuclideanSpace.norm_single i (1 : ℝ)
  have he_ne : e ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at he_norm
    norm_num at he_norm
  have hδ_ne : (2 / Real.pi : ℝ) ≠ 0 := by positivity
  -- the hairpin curve, shifted so that `1 ↦ (0,0)`
  set H : ℝ → EuclideanSpace ℝ (Fin (n - 1)) × ℝ :=
    fun t => modelHairpin (2 / Real.pi) e (t - 1) with hH
  have hHsm : ContMDiff MCreal (MCprod n) smoothOrder H := by
    rw [hH]; exact contMDiff_modelHairpin_comp_sub (2 / Real.pi) e 1
  have hHinj : Function.Injective H := by
    rw [hH]; exact modelHairpin_comp_sub_injective hδ_ne he_ne 1
  have hHimm : ∀ t : ℝ, Function.Injective (mfderiv MCreal (MCprod n) H t) := by
    rw [hH]; exact modelHairpin_comp_sub_mfderiv_injective hδ_ne he_ne 1
  have hHmem : ∀ t : ℝ, ‖(H t).1‖ ≤ 1 ∧ 0 ≤ (H t).2 := by
    intro t
    rw [hH]
    exact ⟨norm_fst_modelHairpin_le he_norm (t - 1), snd_modelHairpin_nonneg _ _ _⟩
  have hH1 : H 1 = ((0 : EuclideanSpace ℝ (Fin (n - 1))), 0) := by
    rw [hH]
    simp [modelHairpin]
  have hΨmd : ∀ t : ℝ, MDifferentiableAt (MCprod n) (MC n) Ψ (H t) := fun t =>
    (hΨsm.contMDiffAt (x := H t)).mdifferentiableAt (by simp [smoothOrder])
  have hHmd : ∀ t : ℝ, MDifferentiableAt MCreal (MCprod n) H t := fun t =>
    (hHsm.contMDiffAt (x := t)).mdifferentiableAt (by simp [smoothOrder])
  refine ⟨fun t : ℝ => Ψ (H t), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change Ψ (H 1) = b
    rw [hH1]; exact hΨ0
  · exact hΨsm.comp hHsm
  · intro t t' htt'
    exact hHinj (hΨinj (hHmem t) (hHmem t') htt')
  · -- properness: the preimage of a compact set is closed and bounded
    have hcont : Continuous (fun t : ℝ => Ψ (H t)) := (hΨsm.comp hHsm).continuous
    rw [isProperMap_iff_isCompact_preimage]
    refine ⟨hcont, ?_⟩
    intro K hK
    obtain ⟨S, hS⟩ := hΨesc K hK
    by_cases hS0 : S ≤ 0
    · have hempty : (fun t : ℝ => Ψ (H t)) ⁻¹' K = ∅ := by
        ext t
        constructor
        · intro ht
          exact hS (H t) (hHmem t).1 (le_trans hS0 (hHmem t).2) ht
        · intro h
          exact absurd h (Set.notMem_empty t)
      rw [hempty]
      exact isCompact_empty
    · push Not at hS0
      refine IsCompact.of_isClosed_subset
        (s := Set.Icc (1 - Real.sqrt S) (1 + Real.sqrt S)) isCompact_Icc
        (hK.isClosed.preimage hcont) ?_
      intro t ht
      have h2 : (H t).2 = (t - 1) ^ 2 := by rw [hH]; simp [modelHairpin]
      have hlt : (t - 1) ^ 2 < S := by
        by_contra hcon
        push Not at hcon
        exact hS (H t) (hHmem t).1 (by rw [h2]; exact hcon) ht
      have hsq : (t - 1) ^ 2 < (Real.sqrt S) ^ 2 := by rwa [Real.sq_sqrt hS0.le]
      have habs : |t - 1| < Real.sqrt S := by
        rw [sq_lt_sq] at hsq
        rwa [abs_of_nonneg (Real.sqrt_nonneg S)] at hsq
      have habs' := abs_lt.mp habs
      exact ⟨by linarith [habs'.1], by linarith [habs'.2]⟩
  · -- the chain rule and the immersion property of `Ψ` on the half-strip
    intro t
    have hchain : mfderiv MCreal (MC n) (fun t : ℝ => Ψ (H t)) t
        = (mfderiv (MCprod n) (MC n) Ψ (H t)).comp (mfderiv MCreal (MCprod n) H t) :=
      mfderiv_comp (I := MCreal) (I' := MCprod n) (I'' := MC n) (x := t)
        (g := Ψ) (f := H) (hΨmd t) (hHmd t)
    rw [hchain]
    intro a b hab
    exact hHimm t (hΨimm (H t) (hHmem t).1 (hHmem t).2 hab)
  · intro y hy
    obtain ⟨t, rfl⟩ := hy
    exact hΨW (H t) (hHmem t).1 (hHmem t).2

end Work.Drive.Rays
