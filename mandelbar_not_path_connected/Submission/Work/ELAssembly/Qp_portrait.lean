/-
# `Qp_portrait`: the exact orbit portrait at the levels of the `z₁`-nest

The `z₁`-nest of the equator-leak argument is the chain of co-landing pairs `Qp n` of rays
(angles `βₙ'` and `βₙ + 1`, i.e. `bAng' n` and `bAng n + 1`) whose level-`(n+1)` pair is
mapped onto the level-`n` pair by `F c = (T_c)^{10}` (`Work.ELNest.Qp_shift`):

    F c ((Qp (n+1)).y) = (Qp n).y,

with the level-`0` pair sitting one `F`-step below the fourth iterate of the parabolic point,

    F c ((Qp 0).y) = (T_c)^4 z₁.

This file proves that the **exact orbit portrait** at every landing point `(Qp n).y` is the
certified pair of angles:

    for θ ∈ [0,1),   θ lands at (Qp n).y   ⟺   θ = βₙ' = bAng' n  or  θ = βₙ = bAng n.

(Note that the second stored angle of the pair is `bAng n + 1`, which is the same external ray
as `bAng n`: rays are `1`-periodic in the angle, `Work.ELTop.rayPt_add_int`.)

## The mechanism

The whole content is the one-step **descent of the portrait** across `T_c`: if the point `y` has
the exact two-ray portrait `{u, v}` (`u ≠ v`) and `y'` is a preimage of `y` at which the two
angles `u'`, `v'` are known to land with `T u' = u`, `T v' = v`, then the portrait at `y'` is
exactly `{u', v'}`.  Indeed, any ray landing at `y'` maps to a ray landing at `y`, hence its
image angle is `T θ = u` or `T θ = v`; and the orbit-portrait count `PortraitCount` (the
injectivity of `T` on the landing angles of a preimage of a two-ray point) identifies that angle
with `u'` resp. `v'`.  Ten such descents (`k = 10`) give the base level from `hbasep`, and each
further descent gives the next level of the nest.

Everything is done in the `Work.EL` vocabulary (`Work.EL.LandsN d.hN`), the orbit-portrait
count `hcount : Work.ELPull.PortraitCount (hNcanOf d)` being transported across the adapter
`Work.PortraitCount.landsN_elDynB`.

The only arithmetic inputs are the congruences of the certified angles (`Work.ELNest.bAng`,
`Work.ELNest.T_iterate_bAng`) and the two level-`0` congruences

    T^[10] β₀' = 821/1023 = T^[4] α₁,       T^[10] β₀ = 326/1023 = T^[4] α₂.
-/
import Mathlib
import Submission.Work.ELAssembly.Defs
import Submission.Work.ELAssembly.Instantiate
import Submission.Work.ELAssembly.card_le_two_of_iterate
import Submission.Work.ELNest.Defs
import Submission.Work.ELNest.Qp_shift
import Submission.Work.ELNest.T_iterate_bAng
import Submission.Work.ELTop.landsN_map
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.SeedDyn.Portrait

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ}

/-! ## 1. Elementary angle facts -/

/-- The angle-doubling map always produces an angle of `[0, 1)`. -/
theorem Qpportrait_T_mem_Ico (θ : ℝ) : Work.EL.T θ ∈ Set.Ico 0 1 := by
  rw [Work.EL.T]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- Rays are `1`-periodic in the angle, so the landing relation is invariant under
`θ ↦ θ + k` (`k : ℤ`). -/
theorem Qpportrait_landsN_add_int (d : Work.EL.RootParabolic c) (θ : ℝ) (y : ℂ) (k : ℤ) :
    (Work.EL.LandsN d.hN (θ + k) y ↔ Work.EL.LandsN d.hN θ y) := by
  have hfun : (fun t : ℝ => Work.EL.rayPt d.hN (θ + (k : ℝ)) t)
      = fun t : ℝ => Work.EL.rayPt d.hN θ t := by
    funext t
    exact Work.ELTop.rayPt_add_int d.hN θ t k
  simp only [Work.EL.LandsN, hfun]

/-- The case `k = 1` of `Qpportrait_landsN_add_int`: the landing relation depends on the angle
only modulo `1`. -/
theorem Qpportrait_landsN_add_one (d : Work.EL.RootParabolic c) (θ : ℝ) (y : ℂ) :
    (Work.EL.LandsN d.hN (θ + 1) y ↔ Work.EL.LandsN d.hN θ y) := by
  simpa using (Qpportrait_landsN_add_int d θ y 1)

/-- `Work.EL.F c = (T_c)^[10]`, the tenth iterate of the antiholomorphic quadratic map. -/
theorem Qpportrait_elF_eq_tantibar (c : ℂ) : Work.EL.F c = (Tantibar c)^[10] := by
  rw [Work.EL.F, Work.ELNest.Tsq_eq_comp, ← Function.iterate_mul]

/-- The two nest angles at a level are distinct: `bAng n` accumulates at `α₁` from below,
`bAng' n` at `α₂` from above, and `α₁ < α₂`. -/
theorem Qpportrait_bAng_ne_bAng' (n : ℕ) :
    Work.ELNest.bAng n ≠ Work.ELNest.bAng' n := by
  have h1 := Work.ELNest.bAng_le_alpha1 n
  have h2 := Work.ELNest.alpha2_le_bAng' n
  have h3 : Work.ELNest.alpha1 < Work.ELNest.alpha2 := by
    norm_num [Work.ELNest.alpha1, Work.ELNest.alpha2]
  intro h
  rw [h] at h1
  linarith

/-! ## 2. The level-`0` arithmetic of the nest angles -/

/-- `T^[4] α₁ = 821/1023` (the first angle of the root portrait at `(T_c)^4 z₁`). -/
theorem Qpportrait_T4_alpha1 : Work.EL.T^[4] Work.EL.alpha1 = 821 / 1023 := by
  have h4 : Work.EL.T^[4] Work.EL.alpha1 = Int.fract ((16 : ℝ) * Work.EL.alpha1) := by
    have h := Work.ELNest.T_iterate_succ 3 Work.EL.alpha1
    norm_num at h
    exact h
  rw [h4]
  have hb : (16 : ℝ) * Work.EL.alpha1 = 821 / 1023 + 5 := by
    norm_num [Work.EL.alpha1]
  rw [hb, Int.fract_eq_iff]
  exact ⟨by norm_num, by norm_num, 5, by push_cast; ring⟩

/-- `T^[4] α₂ = 326/1023` (the second angle of the root portrait at `(T_c)^4 z₁`). -/
theorem Qpportrait_T4_alpha2 : Work.EL.T^[4] Work.EL.alpha2 = 326 / 1023 := by
  have h4 : Work.EL.T^[4] Work.EL.alpha2 = Int.fract ((16 : ℝ) * Work.EL.alpha2) := by
    have h := Work.ELNest.T_iterate_succ 3 Work.EL.alpha2
    norm_num at h
    exact h
  rw [h4]
  have hb : (16 : ℝ) * Work.EL.alpha2 = 326 / 1023 + 6 := by
    norm_num [Work.EL.alpha2]
  rw [hb, Int.fract_eq_iff]
  exact ⟨by norm_num, by norm_num, 6, by push_cast; ring⟩

/-- `T^[10] β₀' = 821/1023 = T^[4] α₁`: the level-`0` angle `bAng' 0` of the nest is a tenth
preimage angle of the first root-portrait angle at `(T_c)^4 z₁`. -/
theorem Qpportrait_T10_bAng'_zero :
    Work.EL.T^[10] (Work.ELNest.bAng' 0) = Work.EL.T^[4] Work.EL.alpha1 := by
  rw [Qpportrait_T4_alpha1, Work.ELNest.T_iterate_ten]
  have hb : (1024 : ℝ) * Work.ELNest.bAng' 0 = 821 / 1023 + 404 := by
    rw [Work.ELNest.bAng']
    norm_num [Work.ELNest.alpha2, Work.ELNest.beta0']
  rw [hb, Int.fract_eq_iff]
  exact ⟨by norm_num, by norm_num, 404, by push_cast; ring⟩

/-- `T^[10] β₀ = 326/1023 = T^[4] α₂`: the level-`0` angle `bAng 0` of the nest is a tenth
preimage angle of the second root-portrait angle at `(T_c)^4 z₁`. -/
theorem Qpportrait_T10_bAng_zero :
    Work.EL.T^[10] (Work.ELNest.bAng 0) = Work.EL.T^[4] Work.EL.alpha2 := by
  rw [Qpportrait_T4_alpha2, Work.ELNest.T_iterate_ten]
  have hb : (1024 : ℝ) * Work.ELNest.bAng 0 = 326 / 1023 + 371 := by
    rw [Work.ELNest.bAng]
    norm_num [Work.EL.alpha1, Work.ELNest.beta0]
  rw [hb, Int.fract_eq_iff]
  exact ⟨by norm_num, by norm_num, 371, by push_cast; ring⟩

/-! ## 3. Landing of the nest angles at the nest points -/

/-- The first certified angle of the level-`n` pair lands at `(Qp n).y`. -/
theorem Qpportrait_lands_bAng' (d : Work.EL.RootParabolic c) (N : NestPairs d) (n : ℕ) :
    Work.EL.LandsN d.hN (Work.ELNest.bAng' n) ((N.Qp n).y) := by
  rw [← N.Qpa n]
  exact (N.Qp n).lands_a

/-- The second certified angle of the level-`n` pair lands at `(Qp n).y`.  The pair stores the
angle `bAng n + 1`, which is the same ray as `bAng n`. -/
theorem Qpportrait_lands_bAng (d : Work.EL.RootParabolic c) (N : NestPairs d) (n : ℕ) :
    Work.EL.LandsN d.hN (Work.ELNest.bAng n) ((N.Qp n).y) := by
  have h := (N.Qp n).lands_b
  rw [N.Qpb n] at h
  exact (Qpportrait_landsN_add_one d (Work.ELNest.bAng n) _).mp h

/-! ## 4. The orbit-portrait count in the `Work.EL` vocabulary -/

/-- `Work.ELPull.PortraitCount` for the canonical `ELPull` datum `hNcanOf d`, read in the
`Work.EL` flavour of `d.hN`: at a preimage `y'` of a point `y` with an exact two-ray portrait,
the doubling map `T` is injective on the landing angles of `y'`. -/
theorem Qpportrait_portraitCount_el (d : Work.EL.RootParabolic c)
    (hcount : Work.ELPull.PortraitCount (hNcanOf d)) :
    ∀ (y y' : ℂ), Tantibar c y' = y →
      (∃ u v : ℝ, u ∈ Set.Ico 0 1 ∧ v ∈ Set.Ico 0 1 ∧ u ≠ v ∧
        ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → (Work.EL.LandsN d.hN θ y ↔ θ = u ∨ θ = v)) →
      ∀ θ' θ'' : ℝ, θ' ∈ Set.Ico 0 1 → θ'' ∈ Set.Ico 0 1 →
        Work.EL.LandsN d.hN θ' y' → Work.EL.LandsN d.hN θ'' y' →
        Work.EL.T θ' = Work.EL.T θ'' → θ' = θ'' := by
  intro y y' hy htw θ' θ'' hθ' hθ'' hl' hl'' hT
  have hcount' : Work.ELPull.PortraitCount (Work.PortraitCount.elDynB d) := hcount
  obtain ⟨u, v, hu, hv, huv, hport⟩ := htw
  have hcan := fun (θ : ℝ) (z : ℂ) => Work.PortraitCount.landsN_elDynB d θ z
  refine hcount' y y' hy ⟨u, v, hu, hv, huv, ?_⟩ θ' θ'' hθ' hθ'' ?_ ?_ hT
  · intro θ hθ
    exact (hcan θ y).trans (hport θ hθ)
  · exact (hcan θ' y').mpr hl'
  · exact (hcan θ'' y').mpr hl''

/-! ## 5. One step of the portrait descent -/

/-- **One descent step.**  If `y` has the exact two-ray portrait `{u, v}` and `y'` is a
preimage of `y` at which the angles `u'`, `v'` land with `T u' = u`, `T v' = v`, then the
portrait at `y'` is exactly `{u', v'}`. -/
theorem Qpportrait_step (d : Work.EL.RootParabolic c)
    (hcount : Work.ELPull.PortraitCount (hNcanOf d))
    {y y' : ℂ} (hy : Tantibar c y' = y)
    {u v u' v' : ℝ} (hu : u ∈ Set.Ico 0 1) (hv : v ∈ Set.Ico 0 1) (huv : u ≠ v)
    (hport : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → (Work.EL.LandsN d.hN θ y ↔ θ = u ∨ θ = v))
    (hu' : u' ∈ Set.Ico 0 1) (hv' : v' ∈ Set.Ico 0 1)
    (hTu : Work.EL.T u' = u) (hTv : Work.EL.T v' = v)
    (hlu : Work.EL.LandsN d.hN u' y') (hlv : Work.EL.LandsN d.hN v' y') :
    ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → (Work.EL.LandsN d.hN θ y' ↔ θ = u' ∨ θ = v') := by
  intro θ hθ
  constructor
  · intro hland
    have hTθ : Work.EL.T θ ∈ Set.Ico 0 1 := Qpportrait_T_mem_Ico θ
    have hlands : Work.EL.LandsN d.hN (Work.EL.T θ) y := by
      have h := Work.ELTop.landsN_map d.hN d.bottcher hland
      rwa [hy] at h
    have hcount' := Qpportrait_portraitCount_el d hcount y y' hy ⟨u, v, hu, hv, huv, hport⟩
    rcases (hport (Work.EL.T θ) hTθ).mp hlands with h | h
    · left
      exact hcount' θ u' hθ hu' hland hlu (by rw [h, hTu])
    · right
      exact hcount' θ v' hθ hv' hland hlv (by rw [h, hTv])
  · rintro (rfl | rfl)
    · exact hlu
    · exact hlv

/-! ## 6. The portrait descent over ten steps -/

/-- **The portrait descends along `(T_c)^[k]`.**  If the point `y = (T_c)^[k] z` has the exact
two-ray portrait `{u, v}` (`u ≠ v`) and `p`, `q` are angles of `[0,1)` landing at `z` with
`T^[k] p = u`, `T^[k] q = v`, then the portrait at `z` is exactly `{p, q}`.

The proof is the backward induction on the intermediate points `z_j = (T_c)^[j] z`
(`j = k, k-1, …, 0`): at each stage the portrait at `z_{j+1}` is the pair
`{T^[j+1] p, T^[j+1] q}` and `Qpportrait_step` carries it down to `z_j`.  The angles
`T^[j] p`, `T^[j] q` lie in `[0,1)` automatically (the angle map always produces a fractional
part), and they are distinct at every stage because `T^[k-j]` carries them to `u ≠ v`. -/
theorem Qpportrait_descent (d : Work.EL.RootParabolic c)
    (hcount : Work.ELPull.PortraitCount (hNcanOf d))
    {k : ℕ} {y z : ℂ} (hTz : (Tantibar c)^[k] z = y)
    {u v : ℝ} (hu : u ∈ Set.Ico 0 1) (hv : v ∈ Set.Ico 0 1) (huv : u ≠ v)
    (hport : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → (Work.EL.LandsN d.hN θ y ↔ θ = u ∨ θ = v))
    {p q : ℝ} (hp : p ∈ Set.Ico 0 1) (hq : q ∈ Set.Ico 0 1)
    (hTp : Work.EL.T^[k] p = u) (hTq : Work.EL.T^[k] q = v)
    (hlp : Work.EL.LandsN d.hN p z) (hlq : Work.EL.LandsN d.hN q z) :
    ∀ θ : ℝ, θ ∈ Set.Ico 0 1 → (Work.EL.LandsN d.hN θ z ↔ θ = p ∨ θ = q) := by
  -- the intermediate angles lie in `[0,1)`
  have hPIco : ∀ j : ℕ, Work.EL.T^[j] p ∈ Set.Ico 0 1 := by
    intro j
    induction j with
    | zero => simpa using hp
    | succ j ih => rw [Function.iterate_succ_apply']; exact Qpportrait_T_mem_Ico _
  have hQIco : ∀ j : ℕ, Work.EL.T^[j] q ∈ Set.Ico 0 1 := by
    intro j
    induction j with
    | zero => simpa using hq
    | succ j ih => rw [Function.iterate_succ_apply']; exact Qpportrait_T_mem_Ico _
  -- and they stay distinct (they are carried to `u ≠ v` by `T^[k-j]`)
  have hne : ∀ j : ℕ, j ≤ k → Work.EL.T^[j] p ≠ Work.EL.T^[j] q := by
    intro j hj heq
    have h1 : Work.EL.T^[k] p = Work.EL.T^[k - j] (Work.EL.T^[j] p) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hj]
    have h2 : Work.EL.T^[k] q = Work.EL.T^[k - j] (Work.EL.T^[j] q) := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel hj]
    have huv' : u = v := by
      rw [← hTp, h1, heq, ← h2, hTq]
    exact huv huv'
  -- the two rays of the nest keep landing at the iterated points of `z`
  have hland : ∀ j : ℕ, Work.EL.LandsN d.hN (Work.EL.T^[j] p) ((Tantibar c)^[j] z) ∧
      Work.EL.LandsN d.hN (Work.EL.T^[j] q) ((Tantibar c)^[j] z) := by
    intro j
    induction j with
    | zero => simpa using ⟨hlp, hlq⟩
    | succ j ih =>
        refine ⟨?_, ?_⟩
        · rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
          exact Work.ELTop.landsN_map d.hN d.bottcher ih.1
        · rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
          exact Work.ELTop.landsN_map d.hN d.bottcher ih.2
  -- the backward induction on the intermediate points
  have key : ∀ m : ℕ, m ≤ k → ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ ((Tantibar c)^[k - m] z) ↔
        θ = Work.EL.T^[k - m] p ∨ θ = Work.EL.T^[k - m] q) := by
    intro m
    induction m with
    | zero =>
        intro _ θ hθ
        have hy : (Tantibar c)^[k - 0] z = y := hTz
        have hTu' : Work.EL.T^[k - 0] p = u := hTp
        have hTv' : Work.EL.T^[k - 0] q = v := hTq
        rw [hy, hport θ hθ, ← hTu', ← hTv']
    | succ m ih =>
        intro hm θ hθ
        set j : ℕ := k - (m + 1) with hj
        have hkj : k - m = j + 1 := by omega
        have hportj : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
            (Work.EL.LandsN d.hN θ ((Tantibar c)^[j + 1] z) ↔
              θ = Work.EL.T^[j + 1] p ∨ θ = Work.EL.T^[j + 1] q) := by
          intro θ hθ
          exact (hkj ▸ ih (by omega)) θ hθ
        exact Qpportrait_step d hcount
          (y := (Tantibar c)^[j + 1] z) (y' := (Tantibar c)^[j] z)
          (u := Work.EL.T^[j + 1] p) (v := Work.EL.T^[j + 1] q)
          (u' := Work.EL.T^[j] p) (v' := Work.EL.T^[j] q)
          (Function.iterate_succ_apply' _ j z).symm
          (hPIco (j + 1)) (hQIco (j + 1))
          (hne (j + 1) (by omega)) hportj
          (hPIco j) (hQIco j)
          (Function.iterate_succ_apply' _ j p).symm
          (Function.iterate_succ_apply' _ j q).symm
          (hland j).1 (hland j).2 θ hθ
  intro θ hθ
  have h := key k le_rfl θ hθ
  simpa using h

/-! ## 7. The portrait of the `z₁`-nest -/

theorem Qp_portrait {c : ℂ} (d : Work.EL.RootParabolic c) (N : Work.ELAssembly.NestPairs d)
    (hcount : Work.ELPull.PortraitCount (Work.ELAssembly.hNcanOf d))
    (hbasep : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ (((LeanEval.ComplexAnalysis.Tantibar c)^[4]) d.z₁) ↔
        θ = (Work.EL.T^[4]) Work.EL.alpha1 ∨ θ = (Work.EL.T^[4]) Work.EL.alpha2))
    (hshift : ∀ n : ℕ, Work.EL.F c ((N.Qp (n + 1)).y) = (N.Qp n).y)
    (hbase : Work.EL.F c ((N.Qp 0).y) = ((LeanEval.ComplexAnalysis.Tantibar c)^[4]) d.z₁)
    (n : ℕ) :
    ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ (N.Qp n).y ↔
        θ = Work.ELNest.bAng n ∨ θ = Work.ELNest.bAng' n) := by
  have hF : ∀ z : ℂ, Work.EL.F c z = (Tantibar c)^[10] z := fun z => by
    rw [Qpportrait_elF_eq_tantibar c]
  -- the level-`0` portrait, ten descents below the portrait at `(T_c)^4 z₁`
  have hbase0 : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ ((N.Qp 0).y) ↔
        θ = Work.ELNest.bAng' 0 ∨ θ = Work.ELNest.bAng 0) := by
    refine Qpportrait_descent d hcount
      (k := 10) (y := ((Tantibar c)^[4]) d.z₁) (z := (N.Qp 0).y)
      (hTz := ?_) (u := Work.EL.T^[4] Work.EL.alpha1) (v := Work.EL.T^[4] Work.EL.alpha2)
      (hu := ?_) (hv := ?_) (huv := ?_) (hport := ?_)
      (p := Work.ELNest.bAng' 0) (q := Work.ELNest.bAng 0) (hp := ?_) (hq := ?_)
      (hTp := Qpportrait_T10_bAng'_zero) (hTq := Qpportrait_T10_bAng_zero)
      (hlp := Qpportrait_lands_bAng' d N 0) (hlq := Qpportrait_lands_bAng d N 0)
    · simpa [hF] using hbase
    · rw [Qpportrait_T4_alpha1]; norm_num
    · rw [Qpportrait_T4_alpha2]; norm_num
    · rw [Qpportrait_T4_alpha1, Qpportrait_T4_alpha2]; norm_num
    · exact hbasep
    · exact ⟨(Work.ELNest.bAng'_pos 0).le, Work.ELNest.bAng'_lt_one 0⟩
    · exact ⟨(Work.ELNest.bAng_pos 0).le, Work.ELNest.bAng_lt_one 0⟩
  -- one level of the nest, from the previous one
  have hstep : ∀ n : ℕ,
      (∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
        (Work.EL.LandsN d.hN θ ((N.Qp n).y) ↔
          θ = Work.ELNest.bAng' n ∨ θ = Work.ELNest.bAng n)) →
      ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
        (Work.EL.LandsN d.hN θ ((N.Qp (n + 1)).y) ↔
          θ = Work.ELNest.bAng' (n + 1) ∨ θ = Work.ELNest.bAng (n + 1)) := by
    intro n ih
    refine Qpportrait_descent d hcount
      (k := 10) (y := (N.Qp n).y) (z := (N.Qp (n + 1)).y)
      (hTz := ?_) (u := Work.ELNest.bAng' n) (v := Work.ELNest.bAng n)
      (hu := ?_) (hv := ?_) (huv := ?_) (hport := ih)
      (p := Work.ELNest.bAng' (n + 1)) (q := Work.ELNest.bAng (n + 1))
      (hp := ?_) (hq := ?_)
      (hTp := (Work.ELNest.T_iterate_bAng n).2) (hTq := (Work.ELNest.T_iterate_bAng n).1)
      (hlp := Qpportrait_lands_bAng' d N (n + 1)) (hlq := Qpportrait_lands_bAng d N (n + 1))
    · simpa [hF] using hshift n
    · exact ⟨(Work.ELNest.bAng'_pos n).le, Work.ELNest.bAng'_lt_one n⟩
    · exact ⟨(Work.ELNest.bAng_pos n).le, Work.ELNest.bAng_lt_one n⟩
    · exact (Qpportrait_bAng_ne_bAng' n).symm
    · exact ⟨(Work.ELNest.bAng'_pos (n + 1)).le, Work.ELNest.bAng'_lt_one (n + 1)⟩
    · exact ⟨(Work.ELNest.bAng_pos (n + 1)).le, Work.ELNest.bAng_lt_one (n + 1)⟩
  have hP : ∀ n : ℕ, ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ ((N.Qp n).y) ↔
        θ = Work.ELNest.bAng' n ∨ θ = Work.ELNest.bAng n) := by
    intro n
    induction n with
    | zero => exact hbase0
    | succ n ih => exact hstep n ih
  intro θ hθ
  exact (hP n θ hθ).trans or_comm

end Work.ELAssembly
