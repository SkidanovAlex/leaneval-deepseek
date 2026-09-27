/-
# The stabiliser of a parabolic fixed point preserves the horospheres there

For a lattice `Γ ≤ PO(n,1)`, a parabolic fixed point `ξ` (i.e. `ξ ∈ parFixed Γ`) and an element
`γ ∈ Γ` with `bd γ ξ = ξ`, the Busemann cocycle of `γ` at `ξ` vanishes: `bCocy γ ξ = 0`.  This is
the hypothesis `hvan` that the whole cusp/geometric-finiteness development consumes.

## The argument

`ξ ∈ parFixed Γ` supplies a parabolic `δ ∈ Γ` with `bd δ ξ = ξ`, and `bCocy_parabolic` gives
`bCocy δ ξ = 0`, i.e. `δ` preserves the horosphere levels at `ξ`.

Assume `bCocy γ ξ ≠ 0`.  Replacing `γ` by `γ⁻¹` if necessary we may suppose that the level
scaling `ℓ = lev ξ (γ • 0)` of `γ` at `ξ` is `> 1`.  The horospheres of `ξ` are flat and the
action of an element fixing `ξ` on them is affine in the flat coordinate; the flat map of `γ` is a
similarity

`φ y = ℓ⁻¹ • (A y) + t`,

so it is a strict contraction of the complete space `ξ^⊥` with ratio `ℓ⁻¹ < 1`; hence `φ` has a
fixed point `y∞` and `‖φ^[k] z - y∞‖ = (ℓ^k)⁻¹ ‖z - y∞‖`.

The flat map of `δ` is an isometry `ψ` of `ξ^⊥`.  The conjugates `ν_k = γ^k δ γ⁻ᵏ ∈ Γ` fix `ξ`,
preserve the levels (`lev ξ (ν_k • 0) = 1`), and their flat map is `φ^[k] ∘ ψ ∘ φ^[-k]`, so that

`‖yc ξ (ν_k • 0) - y∞‖ ≤ ‖y∞‖ + ‖ψ y∞ - y∞‖`

uniformly in `k`.  Hence `hdist 0 (ν_k • 0)` is uniformly bounded and `finite_nearStab` (with the
discreteness of `Γ`) makes `{ν_k}` finite.  If `ν_k = ν_l` with `k < l`, then `δ` commutes with
`γ^{l-k}`; commuting with a power of `γ` forces `ψ y∞ = y∞`, so `δ` fixes the point
`hptOf ξ y∞ 1`, contradicting the parabolicity of `δ`.  So the `ν_k` are pairwise distinct -- an
infinite subset of a finite set, the contradiction.

## The flat calculus

`Work.Mostow.flatSmulLevelIndep` (the flat action in the level), `Work.Mostow.flatSmulDist` (its
similarity property) and `Work.Mostow.flatContractionFixed` (the fixed point of the contraction,
with its exact iterate bounds) supply the three inputs of the engine `no_growing`.
-/
import Mathlib
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.hptOf_level
import Submission.Work.Mostow.hptOf_yc
import Submission.Work.Mostow.hptOf_hdist
import Submission.Work.Mostow.levYcFormula
import Submission.Work.Mostow.flatActBasic
import Submission.Work.Mostow.BusemannRay
import Submission.Work.Mostow.finite_nearStab
import Submission.Work.Mostow.flatSmulLevelIndep
import Submission.Work.Mostow.flatSmulDist
import Submission.Work.Mostow.flatContractionFixed

set_option maxHeartbeats 1000000

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

noncomputable section

variable {n : ℕ}

/-! ## Elementary facts about parabolic isometries

These two lemmas are proved in `geomFiniteStabHorosphere`; they are reproduced here so that this
file does not have to depend on a module that other agents are still working in. -/

lemma abs_hdist_sub_le_sh (hI : HypIsometryProp n) (u v w : E n) :
    |hdist u w - hdist v w| ≤ hdist u v := by
  have hsym : ∀ a b : E n, hdist a b = hdist b a := hI.2.1
  have htri : ∀ a b c : E n, hdist a c ≤ hdist a b + hdist b c := hI.2.2.2.1
  have h1 : hdist u w ≤ hdist u v + hdist v w := htri u v w
  have h2 : hdist v w ≤ hdist v u + hdist u w := htri v u w
  rw [hsym v u] at h2
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

lemma busemann_lipschitz_sh (hI : HypIsometryProp n) (ξ : E n) (hξ : ξ ∈ Sph n) (u v : E n) :
    |busemann ξ u - busemann ξ v| ≤ hdist u v := by
  have h1 : Filter.Tendsto (fun t : ℝ => hdist u (Real.sinh t • ξ) - t) Filter.atTop
      (nhds (busemann ξ u)) := BusemannRay n ξ hξ u
  have h2 : Filter.Tendsto (fun t : ℝ => hdist v (Real.sinh t • ξ) - t) Filter.atTop
      (nhds (busemann ξ v)) := BusemannRay n ξ hξ v
  have h3 : Filter.Tendsto
      (fun t : ℝ => (hdist u (Real.sinh t • ξ) - t) - (hdist v (Real.sinh t • ξ) - t))
      Filter.atTop (nhds (busemann ξ u - busemann ξ v)) := h1.sub h2
  have h3' : Filter.Tendsto (fun t : ℝ => hdist u (Real.sinh t • ξ) - hdist v (Real.sinh t • ξ))
      Filter.atTop (nhds (busemann ξ u - busemann ξ v)) := by
    refine Filter.Tendsto.congr (fun t => ?_) h3
    ring
  have h4 : Filter.Tendsto (fun t : ℝ => |hdist u (Real.sinh t • ξ) - hdist v (Real.sinh t • ξ)|)
      Filter.atTop (nhds |busemann ξ u - busemann ξ v|) := h3'.abs
  have h5 : ∀ t : ℝ,
      |hdist u (Real.sinh t • ξ) - hdist v (Real.sinh t • ξ)| ≤ hdist u v :=
    fun t => abs_hdist_sub_le_sh hI u v _
  exact le_of_tendsto h4 (Filter.Eventually.of_forall h5)

/-- A parabolic element fixing a boundary point preserves every horosphere there. -/
theorem bCocy_parabolic_sh (hA : POActionProp n) (hI : HypIsometryProp n)
    (g : PO n 1) (hg : IsParabolic g) (ξ : E n) (hξ : ξ ∈ Sph n) (hgξ : bd g ξ = ξ) :
    bCocy g ξ = 0 := by
  have hbus : ∀ (g : PO n 1) (ξ u : E n), ξ ∈ Sph n →
      busemann (bd g ξ) (g • u) = busemann ξ u + busemann (bd g ξ) (g • 0) :=
    hI.2.2.2.2.2.2.2.2.2.2.2.2
  have hsym : ∀ a b : E n, hdist a b = hdist b a := hI.2.1
  have hkey : ∀ u : E n, bCocy g ξ = busemann ξ (g • u) - busemann ξ u := by
    intro u
    have h := hbus g ξ u hξ
    rw [hgξ] at h
    simp only [bCocy, hgξ]
    linarith
  have hbdd : ∀ u : E n, |bCocy g ξ| ≤ hdist (g • u) u := by
    intro u
    rw [hkey u]
    exact busemann_lipschitz_sh hI ξ hξ (g • u) u
  by_contra hne
  have hpos : 0 < |bCocy g ξ| := abs_pos.2 hne
  obtain ⟨u, hu⟩ := hg.2 |bCocy g ξ| hpos
  have h := hbdd u
  have h2 : hdist (g • u) u = hdist u (g • u) := hsym (g • u) u
  linarith

/-! ## The flat action of an element fixing a boundary point -/

/-- The flat (horospherical) action of `g` on `ξ^⊥`, read at the level-one horosphere of `ξ`. -/
noncomputable def fmap (ξ : E n) (g : PO n 1) : E n → E n :=
  fun y => yc ξ (g • hptOf ξ y (1 : ℝ))

@[simp] theorem fmap_apply (ξ : E n) (g : PO n 1) (y : E n) :
    fmap ξ g y = yc ξ (g • hptOf ξ y (1 : ℝ)) := rfl

theorem fmap_mem {ξ : E n} (hξ : ξ ∈ Sph n) (g : PO n 1) (y : E n) :
    inner ℝ (fmap ξ g y) ξ = 0 := by
  rw [fmap_apply]
  exact yc_inner_orth hξ

theorem hptOf_zero_one_stabHorosphere (ξ : E n) : hptOf ξ (0 : E n) (1 : ℝ) = 0 := by
  simp [hptOf]

/-- The triangle inequality in the form used below. -/
theorem norm_le_norm_sub_add_sh (a b : E n) : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
  have h := norm_add_le (a - b) b
  rwa [sub_add_cancel] at h

/-- Powers of an element fixing `ξ` fix `ξ`. -/
theorem bd_pow_fixed_sh (hA : POBasic n) (g : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n)
    (hg : bd g ξ = ξ) : ∀ k : ℕ, bd (g ^ k) ξ = ξ := by
  intro k
  induction k with
  | zero => simpa using hA.bd_one ξ hξ
  | succ k ih => rw [pow_succ', hA.bd_mul g (g ^ k) ξ hξ, ih, hg]

/-- The level of a product at a fixed boundary point. -/
theorem lev_smul_zero_mul_sh (hA : POBasic n) (hI : HypIsoData n) {ξ : E n} (hξ : ξ ∈ Sph n)
    (a b : PO n 1) (ha : bd a ξ = ξ) (hb : bd b ξ = ξ) :
    lev ξ ((a * b) • (0 : E n)) = lev ξ (b • (0 : E n)) * lev ξ (a • (0 : E n)) := by
  rw [hA.mul_smul, lev_smul_self hI hA ξ hξ a (b • (0 : E n)) ha]

/-- The level of the inverse at a fixed boundary point. -/
theorem lev_inv_smul_zero_sh (hA : POBasic n) (hI : HypIsoData n) {ξ : E n} (hξ : ξ ∈ Sph n)
    (g : PO n 1) (hg : bd g ξ = ξ) :
    lev ξ (g⁻¹ • (0 : E n)) = (lev ξ (g • (0 : E n)))⁻¹ := by
  have hgi : bd g⁻¹ ξ = ξ := bd_inv_of hξ hA hg
  have h1 := lev_smul_zero_mul_sh hA hI hξ g⁻¹ g hgi hg
  rw [inv_mul_cancel, hA.one_smul] at h1
  have h0 : lev ξ (0 : E n) = 1 := by simp [lev, tpart]
  rw [h0] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

/-- The level of `g • 0` at a fixed boundary point is the exponential of the Busemann cocycle. -/
theorem lev_smul_zero_eq_exp_sh (hI : HypIsoData n) {ξ : E n} (hξ : ξ ∈ Sph n) (g : PO n 1)
    (hg : bd g ξ = ξ) : lev ξ (g • (0 : E n)) = Real.exp (bCocy g ξ) := by
  rw [lev_eq_exp hξ]
  simp only [bCocy, hg]

/-- The flat action of a product: `fmap` is functorial on the stabiliser of `ξ`. -/
theorem fmap_comp (hA : POActionProp n) (hI : HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n)
    (g h : PO n 1) (hg : bd g ξ = ξ) (hh : bd h ξ = ξ)
    (haff : ∀ (y : E n), inner ℝ y ξ = 0 → ∀ (E₁ E₂ : ℝ), 0 < E₁ → 0 < E₂ →
      yc ξ (g • hptOf ξ y E₁) = yc ξ (g • hptOf ξ y E₂))
    (y : E n) (hy : inner ℝ y ξ = 0) :
    fmap ξ (g * h) y = fmap ξ g (fmap ξ h y) := by
  have hpb := POBasic.ofProp hA
  have hlevu : 0 < lev ξ (h • hptOf ξ y (1 : ℝ)) := lev_pos ξ hξ _
  rw [fmap_apply (ξ := ξ) (g := g * h) (y := y), hpb.mul_smul,
    fmap_apply (ξ := ξ) (g := g) (y := fmap ξ h y), fmap_apply (ξ := ξ) (g := h) (y := y)]
  conv_lhs => rw [← hptOf_yc ξ hξ (lev ξ (h • hptOf ξ y (1 : ℝ))) hlevu
      (h • hptOf ξ y (1 : ℝ)) rfl]
  exact haff (yc ξ (h • hptOf ξ y (1 : ℝ))) (yc_inner_orth hξ)
    (lev ξ (h • hptOf ξ y (1 : ℝ))) 1 hlevu one_pos

/-- The flat action of the identity is the identity. -/
theorem fmap_one (hA : POActionProp n) {ξ : E n} (hξ : ξ ∈ Sph n) (y : E n)
    (hy : inner ℝ y ξ = 0) : fmap ξ (1 : PO n 1) y = y := by
  rw [fmap_apply, (POBasic.ofProp hA).one_smul]
  exact (hptOf_level ξ hξ 1 one_pos y hy).2

/-- Iterates of a fixed point. -/
theorem iterate_fix_eq_sh {α : Type*} (f : α → α) {a : α} (h : f a = a) :
    ∀ k : ℕ, f^[k] a = a := by
  intro k
  induction k with
  | zero => rw [Function.iterate_zero_apply]
  | succ k ih => rw [Function.iterate_succ_apply', ih, h]

/-- The flat action of a power of `g` is the iterate of the flat action of `g`. -/
theorem fmap_pow (hA : POActionProp n) (hI : HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n)
    (g : PO n 1) (hg : bd g ξ = ξ)
    (haff : ∀ (y : E n), inner ℝ y ξ = 0 → ∀ (E₁ E₂ : ℝ), 0 < E₁ → 0 < E₂ →
      yc ξ (g • hptOf ξ y E₁) = yc ξ (g • hptOf ξ y E₂))
    (y : E n) (hy : inner ℝ y ξ = 0) :
    ∀ k : ℕ, fmap ξ (g ^ k) y = (fmap ξ g)^[k] y := by
  intro k
  induction k with
  | zero =>
      rw [pow_zero, Function.iterate_zero_apply]
      exact fmap_one hA hξ y hy
  | succ k ih =>
      have hgk : bd (g ^ k) ξ = ξ := bd_pow_fixed_sh (POBasic.ofProp hA) g hξ hg k
      rw [pow_succ', fmap_comp hA hI hξ g (g ^ k) hg hgk haff y hy, ih,
        Function.iterate_succ_apply']

/-- Conjugating a power: extraction of the commutator. -/
theorem comm_of_conj_eq_pow {G : Type*} [Group G] (a b : G) {k m : ℕ}
    (h : a ^ k * b * (a ^ k)⁻¹ = a ^ (k + m) * b * (a ^ (k + m))⁻¹) :
    b * a ^ m = a ^ m * b := by
  have hR : a ^ (k + m) * b * (a ^ (k + m))⁻¹
      = a ^ k * (a ^ m * b * (a ^ m)⁻¹) * (a ^ k)⁻¹ := by
    rw [pow_add, mul_inv_rev]
    simp only [mul_assoc]
  rw [hR] at h
  have h2 : b * (a ^ k)⁻¹ = (a ^ m * b * (a ^ m)⁻¹) * (a ^ k)⁻¹ := by
    have h' : a ^ k * (b * (a ^ k)⁻¹)
        = a ^ k * ((a ^ m * b * (a ^ m)⁻¹) * (a ^ k)⁻¹) := by
      simpa only [← mul_assoc] using h
    exact mul_left_cancel h'
  have h3 : b = a ^ m * b * (a ^ m)⁻¹ := mul_right_cancel h2
  have h4 : b * a ^ m = (a ^ m * b * (a ^ m)⁻¹) * a ^ m :=
    congrArg (fun t => t * a ^ m) h3
  rw [h4, mul_assoc, inv_mul_cancel, mul_one]

/-! ## The flat calculus inputs -/

/-- The similarity property of the flat action, in the shape used by the engine. -/
theorem fmap_scaling (hA : POActionProp n) (hI : HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n) :
    ∀ (g : PO n 1), bd g ξ = ξ → ∀ (y y' : E n), inner ℝ y ξ = 0 → inner ℝ y' ξ = 0 →
      ‖fmap ξ g y - fmap ξ g y'‖ = (lev ξ (g • (0 : E n)))⁻¹ * ‖y - y'‖ := by
  intro g hg y y' hy hy'
  have h := flatSmulDist hA hI hξ g hg y y' hy hy' (1 : ℝ) one_pos
  simpa only [fmap_apply] using h

/-- The level-independence of the flat action, in the shape used by the engine. -/
theorem fmap_level_indep (hA : POActionProp n) (hI : HypIsometryProp n) {ξ : E n}
    (hξ : ξ ∈ Sph n) :
    ∀ (g : PO n 1), bd g ξ = ξ → ∀ (y : E n), inner ℝ y ξ = 0 →
      ∀ (E₁ E₂ : ℝ), 0 < E₁ → 0 < E₂ →
        yc ξ (g • hptOf ξ y E₁) = yc ξ (g • hptOf ξ y E₂) :=
  fun g hg y hy E₁ E₂ h₁ h₂ => flatSmulLevelIndep hA hI hξ g hg y hy E₁ E₂ h₁ h₂

/-- The fixed point of the flat contraction of an expanding element, with its iterate bounds. -/
theorem flat_fix_of (hA : POActionProp n) (hI : HypIsometryProp n) {ξ : E n} (hξ : ξ ∈ Sph n)
    (g : PO n 1) (hg : bd g ξ = ξ) (hℓ : 1 < lev ξ (g • (0 : E n))) :
    ∃ yinf : E n, inner ℝ yinf ξ = 0 ∧ fmap ξ g yinf = yinf ∧
      ∀ (z : E n), inner ℝ z ξ = 0 → ∀ k : ℕ,
        ‖(fmap ξ g)^[k] z - yinf‖ = ((lev ξ (g • (0 : E n))) ^ k)⁻¹ * ‖z - yinf‖ := by
  have hsc : ∀ (y y' : E n), inner ℝ y ξ = 0 → inner ℝ y' ξ = 0 →
      ‖yc ξ (g • hptOf ξ y (1 : ℝ)) - yc ξ (g • hptOf ξ y' (1 : ℝ))‖
        = (lev ξ (g • (0 : E n)))⁻¹ * ‖y - y'‖ :=
    fun y y' hy hy' => flatSmulDist hA hI hξ g hg y y' hy hy' (1 : ℝ) one_pos
  obtain ⟨yinf, hymem, hyfix, hyiter⟩ := flatContractionFixed hI hξ g hg hℓ hsc
  refine ⟨yinf, hymem, ?_, ?_⟩
  · exact hyfix
  · intro z hz k
    exact hyiter z hz k

/-! ## The engine -/

/-- **The engine.**  A discrete subgroup cannot contain both a parabolic element fixing `ξ` and an
element fixing `ξ` whose horospherical level at `ξ` grows. -/
theorem no_growing (hA : POActionProp n) (hI : HypIsometryProp n)
    (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    (ξ : E n) (hξ : ξ ∈ Sph n) (Gd Gg : PO n 1)
    (hδpar : IsParabolic Gd) (hδξ : bd Gd ξ = ξ) (hγξ : bd Gg ξ = ξ)
    (hℓG : 1 < lev ξ (Gg • (0 : E n)))
    (hfixG : ∃ yinf : E n, inner ℝ yinf ξ = 0 ∧ fmap ξ Gg yinf = yinf ∧
      ∀ (z : E n), inner ℝ z ξ = 0 → ∀ k : ℕ,
        ‖(fmap ξ Gg)^[k] z - yinf‖ = ((lev ξ (Gg • (0 : E n))) ^ k)⁻¹ * ‖z - yinf‖)
    (hνmem : ∀ k : ℕ, Gg ^ k * Gd * (Gg ^ k)⁻¹ ∈ Γ)
    (hscale : ∀ (g : PO n 1), bd g ξ = ξ → ∀ (y y' : E n), inner ℝ y ξ = 0 →
      inner ℝ y' ξ = 0 →
      ‖fmap ξ g y - fmap ξ g y'‖ = (lev ξ (g • (0 : E n)))⁻¹ * ‖y - y'‖)
    (haff : ∀ (g : PO n 1), bd g ξ = ξ → ∀ (y : E n), inner ℝ y ξ = 0 →
      ∀ (E₁ E₂ : ℝ), 0 < E₁ → 0 < E₂ →
        yc ξ (g • hptOf ξ y E₁) = yc ξ (g • hptOf ξ y E₂)) : False := by
  have hpb := POBasic.ofProp hA
  have hid := HypIsoData.ofProp hI
  obtain ⟨yinf, hyinf_mem, hyinf_fix, hyinf_iter⟩ := hfixG
  set ℓ : ℝ := lev ξ (Gg • (0 : E n)) with hℓdef
  have hℓpos : 0 < ℓ := lev_pos ξ hξ _
  have hℓ1 : 1 < ℓ := by rw [hℓdef]; exact hℓG
  -- the level scaling of `δ` is `1`
  have hδlev : lev ξ (Gd • (0 : E n)) = 1 := by
    rw [lev_smul_zero_eq_exp_sh hid hξ Gd hδξ,
      bCocy_parabolic_sh hA hI Gd hδpar ξ hξ hδξ, Real.exp_zero]
  -- the level scaling of `γ⁻¹` is `ℓ⁻¹`
  have hγilev : lev ξ (Gg⁻¹ • (0 : E n)) = ℓ⁻¹ := by
    rw [lev_inv_smul_zero_sh hpb hid hξ Gg hγξ, ← hℓdef]
  -- the similarity properties of the three flat maps
  have hscaleg : ∀ (y y' : E n), inner ℝ y ξ = 0 → inner ℝ y' ξ = 0 →
      ‖fmap ξ Gg y - fmap ξ Gg y'‖ = ℓ⁻¹ * ‖y - y'‖ := by
    intro y y' hy hy'
    have h := hscale Gg hγξ y y' hy hy'
    rwa [← hℓdef] at h
  have hscaled : ∀ (y y' : E n), inner ℝ y ξ = 0 → inner ℝ y' ξ = 0 →
      ‖fmap ξ Gd y - fmap ξ Gd y'‖ = ‖y - y'‖ := by
    intro y y' hy hy'
    have h := hscale Gd hδξ y y' hy hy'
    rwa [hδlev, inv_one, one_mul] at h
  have hscalei : ∀ (y y' : E n), inner ℝ y ξ = 0 → inner ℝ y' ξ = 0 →
      ‖fmap ξ Gg⁻¹ y - fmap ξ Gg⁻¹ y'‖ = ℓ * ‖y - y'‖ := by
    intro y y' hy hy'
    have h := hscale Gg⁻¹ (bd_inv_of hξ hpb hγξ) y y' hy hy'
    rwa [hγilev, inv_inv] at h
  -- the fixed point is unique, on the nose
  have hinj : ∀ z : E n, inner ℝ z ξ = 0 → fmap ξ Gg z = yinf → z = yinf := by
    intro z hz hzφ
    have h := hscaleg z yinf hz hyinf_mem
    rw [hzφ, hyinf_fix, sub_self, norm_zero] at h
    have hpos : 0 < ℓ⁻¹ := inv_pos.mpr hℓpos
    have hzero : ‖z - yinf‖ = 0 := by
      rcases mul_eq_zero.mp h.symm with h' | h'
      · exact absurd h' (ne_of_gt hpos)
      · exact h'
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  have hzero_of_scale : ∀ x : E n, ‖x‖ = ℓ⁻¹ * ‖x‖ → x = 0 := by
    intro x hx
    have hlt : ℓ⁻¹ < 1 := inv_lt_one_of_one_lt₀ hℓ1
    by_contra hne
    have hpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (fun h0 => hne (norm_eq_zero.mp h0.symm))
    nlinarith [hx]
  have hzero_of_scale_pow : ∀ (x : E n) (j : ℕ), j ≠ 0 → ‖x‖ = (ℓ ^ j)⁻¹ * ‖x‖ → x = 0 := by
    intro x j hj hx
    have hlt : (ℓ ^ j)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hℓ1 hj)
    by_contra hne
    have hpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg _) (fun h0 => hne (norm_eq_zero.mp h0.symm))
    nlinarith [hx]
  have hfix_unique : ∀ z : E n, inner ℝ z ξ = 0 → fmap ξ Gg z = z → z = yinf := by
    intro z hz hzf
    have h := hscaleg z yinf hz hyinf_mem
    rw [hzf, hyinf_fix] at h
    exact sub_eq_zero.mp (hzero_of_scale (z - yinf) h)
  -- the fixed point is fixed by the flat map of `γ⁻¹`
  have hyi_fix : fmap ξ Gg⁻¹ yinf = yinf := by
    have hcomp := fmap_comp hA hI hξ Gg Gg⁻¹ hγξ (bd_inv_of hξ hpb hγξ)
      (haff Gg hγξ) yinf hyinf_mem
    rw [mul_inv_cancel, fmap_one hA hξ yinf hyinf_mem] at hcomp
    exact hinj (fmap ξ Gg⁻¹ yinf) (fmap_mem hξ Gg⁻¹ yinf) hcomp.symm
  -- the orbit of `0` under the inverse flat map expands geometrically
  have hgen : ∀ j : ℕ, ∀ w : E n, inner ℝ w ξ = 0 →
      (‖(fmap ξ Gg⁻¹)^[j] w - yinf‖ = ℓ ^ j * ‖w - yinf‖) ∧
        inner ℝ ((fmap ξ Gg⁻¹)^[j] w) ξ = 0 := by
    intro j
    induction j with
    | zero =>
        intro w hw
        refine ⟨?_, ?_⟩
        · rw [Function.iterate_zero_apply, pow_zero, one_mul]
        · simpa using hw
    | succ j ih =>
        intro w hw
        obtain ⟨ihv, ihm⟩ := ih w hw
        have hmem' : inner ℝ (fmap ξ Gg⁻¹ ((fmap ξ Gg⁻¹)^[j] w)) ξ = 0 :=
          fmap_mem hξ Gg⁻¹ ((fmap ξ Gg⁻¹)^[j] w)
        have key := hscalei ((fmap ξ Gg⁻¹)^[j] w) yinf ihm hyinf_mem
        rw [hyi_fix] at key
        refine ⟨?_, ?_⟩
        · rw [Function.iterate_succ_apply', key, ihv, pow_succ]
          ring
        · rw [Function.iterate_succ_apply']
          exact hmem'
  have hAraise : ∀ k : ℕ, ‖(fmap ξ Gg⁻¹)^[k] (0 : E n) - yinf‖ = ℓ ^ k * ‖yinf‖ := by
    intro k
    obtain ⟨h1, -⟩ := hgen k (0 : E n) (by simp)
    rw [h1, zero_sub, norm_neg]
  -- the uniform bound on the flat coordinates of the conjugates
  set C0 : ℝ := ‖fmap ξ Gd yinf - yinf‖ with hC0def
  have hC0nn : 0 ≤ C0 := by rw [hC0def]; exact norm_nonneg _
  let ν : ℕ → Γ := fun k => ⟨Gg ^ k * Gd * (Gg ^ k)⁻¹, hνmem k⟩
  have hνcoe : ∀ k : ℕ, ((ν k : Γ) : PO n 1) = Gg ^ k * Gd * (Gg ^ k)⁻¹ := fun k => rfl
  have hged : ∀ a : E n, inner ℝ a ξ = 0 → ‖fmap ξ Gd a - yinf‖ ≤ ‖a - yinf‖ + C0 := by
    intro a ha
    calc ‖fmap ξ Gd a - yinf‖
        ≤ ‖fmap ξ Gd a - fmap ξ Gd yinf‖ + ‖fmap ξ Gd yinf - yinf‖ := by
          have h := dist_triangle (fmap ξ Gd a) (fmap ξ Gd yinf) yinf
          simpa only [dist_eq_norm] using h
      _ = ‖a - yinf‖ + C0 := by rw [hscaled a yinf ha hyinf_mem, hC0def]
  have hbound : ∀ k : ℕ, ‖yc ξ ((ν k : PO n 1) • (0 : E n))‖ ≤ C0 + 2 * ‖yinf‖ := by
    intro k
    have hgk : bd (Gg ^ k) ξ = ξ := bd_pow_fixed_sh hpb Gg hξ hγξ k
    have hgik : bd (Gg⁻¹ ^ k) ξ = ξ := bd_pow_fixed_sh hpb Gg⁻¹ hξ (bd_inv_of hξ hpb hγξ) k
    have hGdGk : bd (Gd * Gg⁻¹ ^ k) ξ = ξ := by
      rw [hpb.bd_mul Gd (Gg⁻¹ ^ k) ξ hξ, hgik, hδξ]
    have hval : yc ξ ((ν k : PO n 1) • (0 : E n)) = (fmap ξ (ν k : PO n 1)) (0 : E n) := by
      rw [fmap_apply, hptOf_zero_one_stabHorosphere]
    rw [hval]
    have hcompl : (fmap ξ (ν k : PO n 1)) (0 : E n)
        = (fmap ξ Gg)^[k] (fmap ξ Gd ((fmap ξ Gg⁻¹)^[k] (0 : E n))) := by
      show (fmap ξ (Gg ^ k * Gd * (Gg ^ k)⁻¹)) (0 : E n) = _
      rw [← inv_pow Gg k, mul_assoc]
      rw [fmap_comp hA hI hξ (Gg ^ k) (Gd * Gg⁻¹ ^ k) hgk hGdGk
        (haff (Gg ^ k) hgk) (0 : E n) (by simp)]
      rw [fmap_comp hA hI hξ Gd (Gg⁻¹ ^ k) hδξ hgik (haff Gd hδξ) (0 : E n) (by simp)]
      rw [fmap_pow hA hI hξ Gg hγξ (haff Gg hγξ)
          (fmap ξ Gd (fmap ξ (Gg⁻¹ ^ k) (0 : E n))) (fmap_mem hξ Gd _) k,
        fmap_pow hA hI hξ Gg⁻¹ (bd_inv_of hξ hpb hγξ) (haff Gg⁻¹ (bd_inv_of hξ hpb hγξ))
          (0 : E n) (by simp) k]
    rw [hcompl]
    have hAk : inner ℝ ((fmap ξ Gg⁻¹)^[k] (0 : E n)) ξ = 0 :=
      (hgen k (0 : E n) (by simp)).2
    have hstep1 := hyinf_iter (fmap ξ Gd ((fmap ξ Gg⁻¹)^[k] (0 : E n)))
      (fmap_mem hξ Gd _) k
    have hstep2 : ‖fmap ξ Gd ((fmap ξ Gg⁻¹)^[k] (0 : E n)) - yinf‖
        ≤ ‖(fmap ξ Gg⁻¹)^[k] (0 : E n) - yinf‖ + C0 := hged _ hAk
    have hstep3 : ‖(fmap ξ Gg⁻¹)^[k] (0 : E n) - yinf‖ = ℓ ^ k * ‖yinf‖ := hAraise k
    have hk_le : (ℓ ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (le_of_lt hℓ1))
    have hpowpos : 0 < ℓ ^ k := pow_pos hℓpos k
    have hmul : (ℓ ^ k)⁻¹ * (ℓ ^ k * ‖yinf‖ + C0) = ‖yinf‖ + (ℓ ^ k)⁻¹ * C0 := by
      rw [mul_add, inv_mul_cancel_left₀ (ne_of_gt hpowpos) ‖yinf‖]
    have hstep4 : (ℓ ^ k)⁻¹ * ‖fmap ξ Gd ((fmap ξ Gg⁻¹)^[k] (0 : E n)) - yinf‖
        ≤ C0 + ‖yinf‖ := by
      calc (ℓ ^ k)⁻¹ * ‖fmap ξ Gd ((fmap ξ Gg⁻¹)^[k] (0 : E n)) - yinf‖
          ≤ (ℓ ^ k)⁻¹ * (‖(fmap ξ Gg⁻¹)^[k] (0 : E n) - yinf‖ + C0) :=
            mul_le_mul_of_nonneg_left hstep2 (inv_nonneg.mpr (le_of_lt hpowpos))
        _ = (ℓ ^ k)⁻¹ * (ℓ ^ k * ‖yinf‖ + C0) := by rw [hstep3]
        _ = ‖yinf‖ + (ℓ ^ k)⁻¹ * C0 := hmul
        _ ≤ C0 + ‖yinf‖ := by
            have h1 : (ℓ ^ k)⁻¹ * C0 ≤ C0 := by
              calc (ℓ ^ k)⁻¹ * C0 ≤ 1 * C0 := mul_le_mul_of_nonneg_right hk_le hC0nn
                _ = C0 := one_mul C0
            linarith [h1]
    calc ‖(fmap ξ Gg)^[k] (fmap ξ Gd ((fmap ξ Gg⁻¹)^[k] (0 : E n)))‖
        ≤ ‖(fmap ξ Gg)^[k] (fmap ξ Gd ((fmap ξ Gg⁻¹)^[k] (0 : E n))) - yinf‖ + ‖yinf‖ :=
          norm_le_norm_sub_add_sh ((fmap ξ Gg)^[k] (fmap ξ Gd ((fmap ξ Gg⁻¹)^[k] (0 : E n)))) yinf
      _ = (ℓ ^ k)⁻¹ * ‖fmap ξ Gd ((fmap ξ Gg⁻¹)^[k] (0 : E n)) - yinf‖ + ‖yinf‖ := by
          rw [hstep1]
      _ ≤ C0 + 2 * ‖yinf‖ := by
          have h := add_le_add_right hstep4 ‖yinf‖
          linarith [h]
  -- the conjugates preserve the levels
  have hνlev : ∀ k : ℕ, lev ξ ((ν k : PO n 1) • (0 : E n)) = 1 := by
    intro k
    have hgk : bd (Gg ^ k) ξ = ξ := bd_pow_fixed_sh hpb Gg hξ hγξ k
    have hgki : bd ((Gg ^ k)⁻¹) ξ = ξ := bd_inv_of hξ hpb hgk
    have hGdgk : bd (Gg ^ k * Gd) ξ = ξ := by
      rw [hpb.bd_mul (Gg ^ k) Gd ξ hξ, hδξ, hgk]
    have h1 := lev_smul_zero_mul_sh hpb hid hξ (Gg ^ k * Gd) ((Gg ^ k)⁻¹) hGdgk hgki
    have h2 := lev_smul_zero_mul_sh hpb hid hξ (Gg ^ k) Gd hgk hδξ
    have h3 := lev_inv_smul_zero_sh hpb hid hξ (Gg ^ k) hgk
    rw [h2, hδlev, one_mul, h3] at h1
    rw [h1, inv_mul_cancel₀ (ne_of_gt (lev_pos ξ hξ (Gg ^ k • (0 : E n))))]
  -- the conjugates lie in a bounded region
  have hνbound : ∀ k : ℕ, hdist (0 : E n) ((ν k : PO n 1) • (0 : E n))
      ≤ Real.arcosh (1 + (C0 + 2 * ‖yinf‖) ^ 2 / 2) := by
    intro k
    rw [hdist_zero_eq_yc hξ (hνlev k)]
    rw [Real.arcosh_le_arcosh (by positivity) (by positivity)]
    have hb := hbound k
    have hsq : ‖yc ξ ((ν k : PO n 1) • (0 : E n))‖ ^ 2 ≤ (C0 + 2 * ‖yinf‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hb 2
    linarith [hsq]
  have hfin : (Set.range ν).Finite := by
    have hS := finite_nearStab (POBasic.ofProp hA) (HypIsoData.ofProp hI) hdisc
      (Real.arcosh (1 + (C0 + 2 * ‖yinf‖) ^ 2 / 2))
    refine hS.subset ?_
    rintro _ ⟨k, rfl⟩
    exact hνbound k
  -- distinctness of the conjugates
  have hcontr : ∀ k l : ℕ, k < l → ν k = ν l → False := by
    intro k l hkl heq
    set m : ℕ := l - k with hmdef
    have hml : m ≠ 0 := by omega
    have hlk : l = k + m := by omega
    have heq2 : Gg ^ k * Gd * (Gg ^ k)⁻¹ = Gg ^ l * Gd * (Gg ^ l)⁻¹ := by
      have h1 : ((ν k : Γ) : PO n 1) = ((ν l : Γ) : PO n 1) := by rw [heq]
      rwa [hνcoe k, hνcoe l] at h1
    rw [hlk] at heq2
    have hcomm : Gd * Gg ^ m = Gg ^ m * Gd := comm_of_conj_eq_pow Gg Gd heq2
    have hGgm : bd (Gg ^ m) ξ = ξ := bd_pow_fixed_sh hpb Gg hξ hγξ m
    have hf1 : fmap ξ (Gg ^ m) yinf = yinf := by
      rw [fmap_pow hA hI hξ Gg hγξ (haff Gg hγξ) yinf hyinf_mem m]
      exact iterate_fix_eq_sh (fmap ξ Gg) hyinf_fix m
    have hψfix : (fmap ξ Gg)^[m] (fmap ξ Gd yinf) = fmap ξ Gd yinf := by
      have h1 : (fmap ξ Gg)^[m] (fmap ξ Gd yinf)
          = fmap ξ (Gg ^ m) (fmap ξ Gd yinf) :=
        ((fmap_pow hA hI hξ Gg hγξ (haff Gg hγξ) (fmap ξ Gd yinf)
          (fmap_mem hξ Gd yinf)) m).symm
      have h2 : fmap ξ (Gg ^ m) (fmap ξ Gd yinf) = fmap ξ (Gg ^ m * Gd) yinf :=
        (fmap_comp hA hI hξ (Gg ^ m) Gd hGgm hδξ (haff (Gg ^ m) hGgm) yinf hyinf_mem).symm
      have h3 : fmap ξ (Gg ^ m * Gd) yinf = fmap ξ (Gd * Gg ^ m) yinf := by rw [← hcomm]
      have h4 : fmap ξ (Gd * Gg ^ m) yinf = fmap ξ Gd (fmap ξ (Gg ^ m) yinf) :=
        fmap_comp hA hI hξ Gd (Gg ^ m) hδξ hGgm (haff Gd hδξ) yinf hyinf_mem
      calc (fmap ξ Gg)^[m] (fmap ξ Gd yinf)
          = fmap ξ (Gg ^ m) (fmap ξ Gd yinf) := h1
        _ = fmap ξ (Gg ^ m * Gd) yinf := h2
        _ = fmap ξ (Gd * Gg ^ m) yinf := h3
        _ = fmap ξ Gd (fmap ξ (Gg ^ m) yinf) := h4
        _ = fmap ξ Gd yinf := by rw [hf1]
    have h := hyinf_iter (fmap ξ Gd yinf) (fmap_mem hξ Gd yinf) m
    rw [hψfix] at h
    have hvec : fmap ξ Gd yinf - yinf = 0 := hzero_of_scale_pow _ m hml h
    have hψy : fmap ξ Gd yinf = yinf := sub_eq_zero.mp hvec
    -- hence `δ` fixes the point of level one and flat coordinate `yinf`
    set u : E n := hptOf ξ yinf (1 : ℝ) with hudef
    have hulev : lev ξ u = 1 := (hptOf_level ξ hξ 1 one_pos yinf hyinf_mem).1
    have hδulev : lev ξ (Gd • u) = 1 := by
      rw [lev_smul_self hid hpb ξ hξ Gd u hδξ, hulev, hδlev, mul_one]
    have hδuyc : yc ξ (Gd • u) = yinf := by
      have h' := hψy
      rw [fmap_apply, ← hudef] at h'
      exact h'
    have hfixu : Gd • u = u := by
      have h1 : hptOf ξ (yc ξ (Gd • u)) (lev ξ (Gd • u)) = Gd • u :=
        hptOf_yc ξ hξ _ (lev_pos ξ hξ _) _ rfl
      rw [hδuyc, hδulev, ← hudef] at h1
      exact h1.symm
    exact hδpar.1 u hfixu
  have hνinj : Function.Injective ν := by
    intro k l hkl
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hcontr k l h hkl
    · exact hcontr l k h hkl.symm
  exact (Set.infinite_range_of_injective hνinj) hfin

theorem stabHorosphere (n : ℕ) (hn : 2 ≤ n) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (hBb : ∀ m, Submission.Mostow.BieberbachProp m)
    (Γ : Subgroup (LeanEval.Geometry.MostowRigidity.PO n 1)) (hΓ : Submission.Mostow.HypLattice Γ)
    (γ : Γ) (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Work.Mostow.parFixed Γ)
    (hγ : Submission.Mostow.bd (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = ξ) :
    Work.Mostow.bCocy (γ : LeanEval.Geometry.MostowRigidity.PO n 1) ξ = 0 := by
  obtain ⟨hξS, δ, hδpar, hδξ⟩ := hξ
  by_contra hc
  have hdisc : IsDiscrete (SetLike.coe Γ) := hΓ.1
  have hscale := fmap_scaling hA hI hξS
  have haff := fmap_level_indep hA hI hξS
  rcases lt_trichotomy (bCocy (γ : PO n 1) ξ) 0 with hlt | heq | hgt
  · -- replace `γ` by `γ⁻¹`
    have hbc_inv : bCocy ((γ⁻¹ : Γ) : PO n 1) ξ = -bCocy (γ : PO n 1) ξ := by
      have h1 := bCocy_mul hA hI ((γ⁻¹ : Γ) : PO n 1) (γ : PO n 1) ξ hξS
      rw [← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, bCocy_one hA hI ξ hξS,
        hγ] at h1
      linarith
    have hγiξ : bd ((γ⁻¹ : Γ) : PO n 1) ξ = ξ := bd_inv_of hξS (POBasic.ofProp hA) hγ
    have hℓ : 1 < lev ξ (((γ⁻¹ : Γ) : PO n 1) • (0 : E n)) := by
      rw [lev_smul_zero_eq_exp_sh (HypIsoData.ofProp hI) hξS _ hγiξ, hbc_inv,
        Real.one_lt_exp_iff]
      linarith
    obtain ⟨yinf, hyinf_mem, hyinf_fix, hyinf_iter⟩ :=
      flat_fix_of hA hI hξS (((γ⁻¹ : Γ) : PO n 1)) hγiξ hℓ
    refine no_growing hA hI Γ hdisc ξ hξS (δ : PO n 1) (((γ⁻¹ : Γ) : PO n 1))
      hδpar hδξ hγiξ hℓ ⟨yinf, hyinf_mem, hyinf_fix, hyinf_iter⟩ ?_ hscale haff
    intro k
    have h1 : ((γ : PO n 1)⁻¹) ^ k ∈ Γ := pow_mem (inv_mem γ.2) k
    exact mul_mem (mul_mem h1 δ.2) (inv_mem h1)
  · exact hc heq
  · have hℓ : 1 < lev ξ ((γ : PO n 1) • (0 : E n)) := by
      rw [lev_smul_zero_eq_exp_sh (HypIsoData.ofProp hI) hξS (γ : PO n 1) hγ,
        Real.one_lt_exp_iff]
      exact hgt
    obtain ⟨yinf, hyinf_mem, hyinf_fix, hyinf_iter⟩ :=
      flat_fix_of hA hI hξS (γ : PO n 1) hγ hℓ
    refine no_growing hA hI Γ hdisc ξ hξS (δ : PO n 1) (γ : PO n 1)
      hδpar hδξ hγ hℓ ⟨yinf, hyinf_mem, hyinf_fix, hyinf_iter⟩ ?_ hscale haff
    intro k
    exact mul_mem (mul_mem (pow_mem γ.2 k) δ.2) (inv_mem (pow_mem γ.2 k))

end

