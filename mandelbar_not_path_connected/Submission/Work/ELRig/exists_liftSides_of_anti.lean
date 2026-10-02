import Mathlib
import Submission.Work.ELRig.Inputs
import Submission.Work.ELRig.exists_liftSidesV2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `ELRig.exists_liftSides_of_anti`

`Work.ELRig.exists_liftSidesV2` constructs the plane topology `Work.EL.LiftSides` of the three
regions `U`, `M`, `L` from curve data alone: continuity, strictly increasing real part,
`1`-periodicity, and the two sign conditions "`γ₁` above the real axis" / "`γ₂` below the real
axis" on the left half plane `{Re < -R}`.

Here the two sign conditions are *derived* from the hypotheses that are natural for the two root
ray tails:

* `hanti` : `γ₂` is the reflection of `γ₁` under the anti-holomorphic involution `ι w = w̄ + ½`
  (this is the anti-symmetry of the two rays of the root portrait);
* `hreal` : the real axis below the level `-R` carries no point of either curve.

The argument is elementary.  Each curve is the graph of a continuous height function `hgt` over
the real axis (`Work.ELRig.CCurve`).  The anti-symmetry gives the pointwise relation
`hgt₂ (x + ½) = -hgt₁ x` (`hgt_anti`), whence the heights of the two curves are *opposite* on the
left half plane.  The zero-freeness of the heights on `(-∞,-R)` (`hreal`, `hgt_ne_zero_of_lt`)
together with the preconnectedness of `(-∞,-R)` makes the sign of `hgt₁` constant there
(`hgt_sign_const`); there are thus two cases.

* If `hgt₁ > 0` on the left half plane then `γ₁` is above and `γ₂` below the real axis and the two
  sign conditions of `exists_liftSidesV2` hold directly.
* If `hgt₁ < 0` then the roles are exchanged: `γ₂` is above and `γ₁` below.  Applying
  `exists_liftSidesV2` to the *swapped* pair of curves and swapping `U` and `L` in the resulting
  structure (`LiftSides_reindex`) gives the required `LiftSides`.
-/

open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELRig

open Complex

/-! ## The reflection `ι w = w̄ + ½` -/

theorem star_add_half_re (w : ℂ) : (star w + 1/2 : ℂ).re = w.re + 1/2 := by simp

theorem star_add_half_im (w : ℂ) : (star w + 1/2 : ℂ).im = -w.im := by simp

/-! ## The two height functions are anti-symmetric -/

/-- **Anti-symmetry of the heights.**  If the range of `γ₂` is the reflection of the range of
`γ₁` under `ι w = w̄ + ½`, then the height functions of the two curves are related by
`hgt₂ (x + ½) = -hgt₁ x`. -/
theorem hgt_anti {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂)
    (hanti : Set.range γ₂ = (fun w : ℂ => star w + 1/2) '' Set.range γ₁) (x : ℝ) :
    C₂.hgt (x + 1/2) = -C₁.hgt x := by
  have hmem₁ : ((x : ℂ) + (C₁.hgt x : ℂ) * I) ∈ Set.range γ₁ :=
    (C₁.mem_range_iff _).mpr (by simp)
  have hmem₂ : star ((x : ℂ) + (C₁.hgt x : ℂ) * I) + 1/2 ∈ Set.range γ₂ := by
    rw [hanti]
    exact ⟨_, hmem₁, rfl⟩
  have h := (C₂.mem_range_iff _).mp hmem₂
  have hre : (star ((x : ℂ) + (C₁.hgt x : ℂ) * I) + 1/2 : ℂ).re = x + 1/2 := by
    rw [star_add_half_re]; simp
  have him : (star ((x : ℂ) + (C₁.hgt x : ℂ) * I) + 1/2 : ℂ).im = -C₁.hgt x := by
    rw [star_add_half_im]; simp
  rw [hre, him] at h
  exact h.symm

/-! ## The sign of a curve on the left half plane -/

/-- A curve which meets the real axis nowhere below the level `-R` has a zero-free height
function there. -/
theorem hgt_ne_zero_of_lt {γ : ℝ → ℂ} (C : CCurve γ) {R : ℝ}
    (hreal : ∀ x : ℝ, x < -R → (x : ℂ) ∉ Set.range γ) {x : ℝ} (hx : x < -R) :
    C.hgt x ≠ 0 := by
  intro h
  exact hreal x hx ((C.mem_range_iff (x : ℂ)).mpr (by simpa using h.symm))

/-- A curve which meets the real axis nowhere below the level `-R` lies entirely above or
entirely below the real axis on the left half plane. -/
theorem hgt_sign_const {γ : ℝ → ℂ} (C : CCurve γ) {R : ℝ}
    (hreal : ∀ x : ℝ, x < -R → (x : ℂ) ∉ Set.range γ) :
    (∀ x : ℝ, x < -R → 0 < C.hgt x) ∨ (∀ x : ℝ, x < -R → C.hgt x < 0) := by
  have hd : Disjoint {x : ℝ | 0 < C.hgt x} {x : ℝ | C.hgt x < 0} := by
    rw [Set.disjoint_left]
    intro x h1 h2
    change 0 < C.hgt x at h1
    change C.hgt x < 0 at h2
    linarith
  have hcov : Set.Iio (-R) ⊆ {x : ℝ | 0 < C.hgt x} ∪ {x : ℝ | C.hgt x < 0} := by
    intro x hx
    rcases lt_trichotomy (C.hgt x) 0 with h | h | h
    · exact Or.inr h
    · exact absurd h (hgt_ne_zero_of_lt C hreal hx)
    · exact Or.inl h
  rcases preconnected_subset_of_disjoint_open (isPreconnected_Iio (a := -R))
      (isOpen_lt continuous_const C.hgt_cont) (isOpen_lt C.hgt_cont continuous_const)
      hd hcov with h | h
  · exact Or.inl fun x hx => h hx
  · exact Or.inr fun x hx => h hx

/-- A positive height function means that the curve lies above the real axis. -/
theorem im_pos_of_hgt_pos {γ : ℝ → ℂ} (C : CCurve γ) {R : ℝ}
    (h : ∀ x : ℝ, x < -R → 0 < C.hgt x) {s : ℝ} (hs : (γ s).re < -R) : 0 < (γ s).im := by
  have hmem : γ s ∈ Set.range γ := ⟨s, rfl⟩
  have h2 := (C.mem_range_iff (γ s)).mp hmem
  rw [h2]
  exact h _ hs

/-- A negative height function means that the curve lies below the real axis. -/
theorem im_neg_of_hgt_neg {γ : ℝ → ℂ} (C : CCurve γ) {R : ℝ}
    (h : ∀ x : ℝ, x < -R → C.hgt x < 0) {s : ℝ} (hs : (γ s).re < -R) : (γ s).im < 0 := by
  have hmem : γ s ∈ Set.range γ := ⟨s, rfl⟩
  have h2 := (C.mem_range_iff (γ s)).mp hmem
  rw [h2]
  exact h _ hs

/-- The height of `γ₂` is negative on the left half plane as soon as the height of `γ₁` is
positive there (the anti-symmetry shifts the argument by `½`, which keeps it in `(-∞,-R)`). -/
theorem hgt_neg_of_hgt_pos {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂)
    (hanti : Set.range γ₂ = (fun w : ℂ => star w + 1/2) '' Set.range γ₁) {R : ℝ}
    (hpos : ∀ x : ℝ, x < -R → 0 < C₁.hgt x) {x : ℝ} (hx : x < -R) : C₂.hgt x < 0 := by
  have hlt : x - 1/2 < -R := by linarith
  have hrel := hgt_anti C₁ C₂ hanti (x - 1/2)
  rw [show x - 1/2 + 1/2 = x by ring] at hrel
  have h1 : 0 < C₁.hgt (x - 1/2) := hpos _ hlt
  rw [hrel]
  linarith

/-- The height of `γ₂` is positive on the left half plane as soon as the height of `γ₁` is
negative there. -/
theorem hgt_pos_of_hgt_neg {γ₁ γ₂ : ℝ → ℂ} (C₁ : CCurve γ₁) (C₂ : CCurve γ₂)
    (hanti : Set.range γ₂ = (fun w : ℂ => star w + 1/2) '' Set.range γ₁) {R : ℝ}
    (hneg : ∀ x : ℝ, x < -R → C₁.hgt x < 0) {x : ℝ} (hx : x < -R) : 0 < C₂.hgt x := by
  have hlt : x - 1/2 < -R := by linarith
  have hrel := hgt_anti C₁ C₂ hanti (x - 1/2)
  rw [show x - 1/2 + 1/2 = x by ring] at hrel
  have h1 : C₁.hgt (x - 1/2) < 0 := hneg _ hlt
  rw [hrel]
  linarith

/-! ## Reindexing the two curves -/

/-- Every field of the plane-topology structure `Work.EL.LiftSides` is symmetric in the two
curves: the regions themselves do not change when `γ₁` and `γ₂` are exchanged, only the order of
the two terms of the union `Set.range γ₁ ∪ Set.range γ₂` does. -/
def LiftSides_reindex {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {z₁ : ℂ} {R R₀ : ℝ}
    {γ₁ γ₂ : ℝ → ℂ} (L : Work.EL.LiftSides hN z₁ γ₁ γ₂ R R₀) :
    Work.EL.LiftSides hN z₁ γ₂ γ₁ R R₀ :=
  { hRR₀ := L.hRR₀
    U := L.U
    M := L.M
    L := L.L
    U_sub := L.U_sub
    M_sub := L.M_sub
    L_sub := L.L_sub
    U_off := by rw [Set.union_comm]; exact L.U_off
    M_off := by rw [Set.union_comm]; exact L.M_off
    L_off := by rw [Set.union_comm]; exact L.L_off
    U_conn := L.U_conn
    M_conn := L.M_conn
    L_conn := L.L_conn
    U_disj_M := L.U_disj_M
    U_disj_L := L.U_disj_L
    M_disj_L := L.M_disj_L
    cover := by
      intro w hw
      have h := L.cover hw
      simp only [Set.mem_union] at h ⊢
      tauto
    real_mem_M := L.real_mem_M
    decomp := by
      intro S hpre hsub hdisj
      exact L.decomp S hpre hsub (by rw [Set.union_comm]; exact hdisj)
    top_mem_U := L.top_mem_U
    bottom_mem_L := L.bottom_mem_L }

/-! ## The target lemma -/

theorem exists_liftSides_of_anti {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ} {z₁ : ℂ}
    {R R₀ : ℝ} (hRR₀ : R₀ < R) {γ₁ γ₂ : ℝ → ℂ}
    (hcont₁ : Continuous γ₁) (hcont₂ : Continuous γ₂)
    (hmono₁ : StrictMono fun s : ℝ => (γ₁ s).re)
    (hmono₂ : StrictMono fun s : ℝ => (γ₂ s).re)
    (hper₁ : ∀ s : ℝ, γ₁ (s + 1) = γ₁ s + 1)
    (hper₂ : ∀ s : ℝ, γ₂ (s + 1) = γ₂ s + 1)
    (hanti : Set.range γ₂ = (fun w : ℂ => star w + 1 / 2) '' Set.range γ₁)
    (hreal : ∀ x : ℝ, x < -R → (x : ℂ) ∉ Set.range γ₁ ∪ Set.range γ₂) :
    Nonempty (Work.EL.LiftSides hN z₁ γ₁ γ₂ R R₀) := by
  let C₁ : CCurve γ₁ := ⟨hcont₁, hmono₁, hper₁⟩
  let C₂ : CCurve γ₂ := ⟨hcont₂, hmono₂, hper₂⟩
  have hreal₁ : ∀ x : ℝ, x < -R → (x : ℂ) ∉ Set.range γ₁ :=
    fun x hx hmem => hreal x hx (Or.inl hmem)
  rcases hgt_sign_const C₁ hreal₁ with hpos | hneg
  · -- `γ₁` is above, `γ₂` below the real axis
    have habove₁ : ∀ s : ℝ, (γ₁ s).re < -R → 0 < (γ₁ s).im :=
      fun s hs => im_pos_of_hgt_pos C₁ hpos hs
    have hbelow₂ : ∀ s : ℝ, (γ₂ s).re < -R → (γ₂ s).im < 0 := by
      intro s hs
      have hmem : γ₂ s ∈ Set.range γ₂ := ⟨s, rfl⟩
      have h2 := (C₂.mem_range_iff (γ₂ s)).mp hmem
      rw [h2]
      exact hgt_neg_of_hgt_pos C₁ C₂ hanti hpos hs
    exact exists_liftSidesV2 hRR₀ hcont₁ hcont₂ hmono₁ hmono₂ hper₁ hper₂ habove₁ hbelow₂
  · -- `γ₂` is above, `γ₁` below the real axis
    have habove₂ : ∀ s : ℝ, (γ₂ s).re < -R → 0 < (γ₂ s).im := by
      intro s hs
      have hmem : γ₂ s ∈ Set.range γ₂ := ⟨s, rfl⟩
      have h2 := (C₂.mem_range_iff (γ₂ s)).mp hmem
      rw [h2]
      exact hgt_pos_of_hgt_neg C₁ C₂ hanti hneg hs
    have hbelow₁ : ∀ s : ℝ, (γ₁ s).re < -R → (γ₁ s).im < 0 :=
      fun s hs => im_neg_of_hgt_neg C₁ hneg hs
    obtain ⟨L⟩ := exists_liftSidesV2 (γ₁ := γ₂) (γ₂ := γ₁) hRR₀ hcont₂ hcont₁ hmono₂ hmono₁
      hper₂ hper₁ habove₂ hbelow₁
    exact ⟨LiftSides_reindex L⟩

end Work.ELRig
