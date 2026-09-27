import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.Geo.Prism.Defs
import Submission.Work.Geo.Prism.Stretch
import Submission.Work.Geo.Prism.Theta
import Submission.Work.Geo.Prism.Tube.exists_tube
import Submission.Work.Geo.Prism.Push.prismPushFun_continuous
import Submission.Work.Geo.Prism.Push.prismPushInvFun_continuous

/-!
# G1: `prism_push` (Newman §1 Lemma 2 + Theorem 1, Case 1)

The explicit stretching homeomorphism of the prism `Pr a b = E a × E b × ℝ` along the `t`
direction, with thickness taper `lam η y = max 0 (1 - ‖y‖/η)` and *continuous* length
`len F φ γ z = max 0 (γ z - φ z)` on `F` and `0` off `F`.

Everything happens at `y = 0`: the homeomorphism maps the "floor slab"
`{φ z ≤ t ≤ φ z + δ}` at `y = 0`, which lies in `U`, onto the whole prism
`{φ z ≤ t ≤ γ z}`, while it is the identity outside the compact tube
`C = {‖y‖ ≤ η} × {z ∈ F, φ z ≤ t ≤ γ z + δ} ⊆ W`.

* `prismPushFun`, `prismPushInvFun` (in `Defs.lean`) are the explicit formulae;
  `Work.Geo.Prism.Push.prismPushFun_continuous`, `...prismPushInvFun_continuous` (`Push/`)
  give the continuity of the two maps and
  `Work.Geo.Prism.Push.prismPushInvFun_prismPushFun`, `...prismPushFun_prismPushInvFun`
  the two inverse laws, so the two formulae form a homeomorphism of `Pr a b`.
-/

open Set Metric
open scoped Topology
open Classical

namespace Work.Geo.Prism

/-! ### The parameters `lam` and `len` -/

theorem lam_nonneg {a : ℕ} (η : ℝ) (y : PL.E a) : 0 ≤ lam η y := le_max_left _ _

theorem lam_le_one {a : ℕ} {η : ℝ} (hη : 0 < η) (y : PL.E a) : lam η y ≤ 1 := by
  refine max_le (by norm_num) ?_
  have : 0 ≤ ‖y‖ / η := div_nonneg (norm_nonneg y) (le_of_lt hη)
  linarith

theorem lam_eq_zero {a : ℕ} {η : ℝ} (hη : 0 < η) {y : PL.E a} (hy : η ≤ ‖y‖) : lam η y = 0 := by
  refine max_eq_left ?_
  have h : 1 ≤ ‖y‖ / η := by
    rw [le_div_iff₀ hη]
    simpa using hy
  linarith

theorem lam_zero_right {a : ℕ} {η : ℝ} (_hη : 0 < η) : lam η (0 : PL.E a) = 1 := by
  unfold lam
  rw [norm_zero, zero_div, sub_zero, max_eq_right (by norm_num)]

theorem len_nonneg {b : ℕ} (F : Set (PL.E b)) (φ γ : PL.E b → ℝ) (z : PL.E b) :
    0 ≤ len F φ γ z := by
  unfold len
  split_ifs with hz
  · exact le_max_left _ _
  · exact le_rfl

theorem len_eq {b : ℕ} {F : Set (PL.E b)} {φ γ : PL.E b → ℝ} {z : PL.E b} (hz : z ∈ F)
    (h : φ z ≤ γ z) : len F φ γ z = γ z - φ z := by
  unfold len
  rw [ite_eq_left hz, max_eq_right (by linarith)]

theorem len_eq_zero {b : ℕ} {F : Set (PL.E b)} {φ γ : PL.E b → ℝ} {z : PL.E b} (hz : z ∉ F) :
    len F φ γ z = 0 := by
  unfold len
  rw [ite_eq_right hz]

theorem dist_fst_pair {b : ℕ} (z : PL.E b) (t t' : ℝ) : dist (z, t) (z, t') = |t - t'| := by
  rw [Prod.dist_eq, dist_self, Real.dist_eq, max_eq_right (abs_nonneg _)]

/-! ### G1 -/

/-- **G1 `prism_push`** (blueprint §2, Newman §1 Lemma 2 + Theorem 1 Case 1, compact form).
Let `F` be compact, `φ ≤ γ` continuous and equal on `frontier F`; let `U` contain the floor
graph over `F` and `W` contain the prism over `F`.  Then there is a homeomorphism `h` of
`Pr a b = E a × E b × ℝ` which is the identity off a compact subset of `W`, fixes every
point with `z ∉ F` or `t ≤ φ z`, preserves the `y` and `z` coordinates, and moves `U` over
the whole prism over `F`. -/
theorem prism_push {a b : ℕ} (F : Set (PL.E b)) (hF : IsCompact F) (φ γ : PL.E b → ℝ)
    (hφ : Continuous φ) (hγ : Continuous γ) (hle : ∀ z ∈ F, φ z ≤ γ z)
    (hfr : ∀ z ∈ frontier F, φ z = γ z)
    (U W : Set (Pr a b)) (hU : IsOpen U) (hW : IsOpen W)
    (hbase : ∀ z ∈ F, ((0 : PL.E a), z, φ z) ∈ U)
    (hS : ∀ z ∈ F, ∀ t, φ z ≤ t → t ≤ γ z → ((0 : PL.E a), z, t) ∈ W) :
    ∃ h : Pr a b ≃ₜ Pr a b, PL.CSupp h W ∧
      (∀ y z t, (z ∉ F ∨ t ≤ φ z) → h (y, z, t) = (y, z, t)) ∧
      (∀ y z t, (h (y, z, t)).1 = y ∧ (h (y, z, t)).2.1 = z) ∧
      (∀ z ∈ F, ∀ t, φ z ≤ t → t ≤ γ z → ((0 : PL.E a), z, t) ∈ h '' U) := by
  have hFcl : IsClosed F := hF.isClosed
  -- ## step 0: two parametrisations of the slab over `F`
  have hmemS : ∀ z t', z ∈ F → φ z ≤ t' → t' ≤ γ z →
      (z, t') ∈ ((fun p : PL.E b × ℝ => (p.1, φ p.1 + p.2 * (γ p.1 - φ p.1))) ''
        (F ×ˢ Icc (0 : ℝ) 1)) := by
    intro z t' hz h1 h2
    rw [Set.mem_image]
    by_cases h0 : γ z - φ z = 0
    · have hval : φ (z, 0).1 + (z, 0).2 * (γ (z, 0).1 - φ (z, 0).1) = φ z := by simp
      refine ⟨(z, 0), ⟨hz, ⟨le_rfl, zero_le_one⟩⟩, Prod.ext rfl ?_⟩
      rw [hval]
      exact le_antisymm h1 (by linarith)
    · have hpos : 0 < γ z - φ z := by
        have : 0 ≤ γ z - φ z := by linarith [hle z hz]
        exact lt_of_le_of_ne this (Ne.symm h0)
      refine ⟨(z, (t' - φ z) / (γ z - φ z)), ⟨hz, ⟨?_, ?_⟩⟩, ?_⟩
      · exact div_nonneg (by linarith) hpos.le
      · rw [div_le_one hpos]; linarith
      · refine Prod.ext rfl ?_
        field_simp
        ring
  -- ## step 1: the tube constants
  have key : ∃ η δ : ℝ, 0 < η ∧ 0 < δ ∧
      (∀ y z t, ‖y‖ ≤ η → z ∈ F → φ z ≤ t → t ≤ φ z + δ → (y, z, t) ∈ U) ∧
      (∀ y z t, ‖y‖ ≤ η → z ∈ F → φ z ≤ t → t ≤ γ z + δ → (y, z, t) ∈ W) := by
    rcases F.eq_empty_or_nonempty with h | hne
    · exact ⟨1, 1, one_pos, one_pos,
        (by intro y z t _ hz; exact absurd hz (by simp [h])),
        (by intro y z t _ hz; exact absurd hz (by simp [h]))⟩
    · -- the floor graph over `F`
      have hKg : IsCompact ((fun z : PL.E b => (z, φ z)) '' F) :=
        hF.image (continuous_id.prodMk hφ)
      have hKgU : ({0} : Set (PL.E a)) ×ˢ ((fun z : PL.E b => (z, φ z)) '' F) ⊆ U := by
        rintro ⟨y, q⟩ ⟨hy, hq⟩
        obtain ⟨z, hz, rfl⟩ := hq
        have hy' : y = 0 := Set.mem_singleton_iff.mp hy
        rw [hy']
        simpa using hbase z hz
      obtain ⟨η₁, ρ₁, hη₁, hρ₁, hU₁⟩ := Tube.exists_tube (a := a) hKg hU hKgU
      -- the prism (closed slab) over `F`
      have hKs : IsCompact ((fun p : PL.E b × ℝ => (p.1, φ p.1 + p.2 * (γ p.1 - φ p.1))) ''
          (F ×ˢ Icc (0 : ℝ) 1)) :=
        (hF.prod isCompact_Icc).image (by fun_prop)
      have hKsW : ({0} : Set (PL.E a)) ×ˢ ((fun p : PL.E b × ℝ =>
          (p.1, φ p.1 + p.2 * (γ p.1 - φ p.1))) '' (F ×ˢ Icc (0 : ℝ) 1)) ⊆ W := by
        rintro ⟨y, q⟩ ⟨hy, p, hp, rfl⟩
        obtain ⟨hz, hu⟩ := hp
        rw [mem_Icc] at hu
        have hy' : y = 0 := Set.mem_singleton_iff.mp hy
        rw [hy']
        exact hS p.1 hz _ (by nlinarith [hu.1, hle p.1 hz])
          (by nlinarith [hu.2, hle p.1 hz])
      obtain ⟨η₂, ρ₂, hη₂, hρ₂, hW₂⟩ := Tube.exists_tube (a := a) hKs hW hKsW
      refine ⟨min η₁ η₂, min ρ₁ ρ₂, lt_min hη₁ hη₂, lt_min hρ₁ hρ₂, ?_, ?_⟩
      · intro y z t hy hz h1 h2
        have hy₁ : ‖y‖ ≤ η₁ := le_trans hy (min_le_left η₁ η₂)
        refine hU₁ ⟨hy₁, (z, φ z), ⟨z, hz, rfl⟩, ?_⟩
        rw [dist_fst_pair, abs_of_nonneg (by linarith)]
        linarith [min_le_left ρ₁ ρ₂]
      · intro y z t hy hz h1 h2
        have hy₂ : ‖y‖ ≤ η₂ := le_trans hy (min_le_right η₁ η₂)
        have hmem : (z, min t (γ z)) ∈ ((fun p : PL.E b × ℝ =>
            (p.1, φ p.1 + p.2 * (γ p.1 - φ p.1))) '' (F ×ˢ Icc (0 : ℝ) 1)) :=
          hmemS z (min t (γ z)) hz (le_min h1 (hle z hz)) (min_le_right _ _)
        refine hW₂ ⟨hy₂, (z, min t (γ z)), hmem, ?_⟩
        rw [dist_fst_pair]
        by_cases h : t ≤ γ z
        · rw [min_eq_left h, sub_self, abs_zero]
          exact hρ₂.le
        · rw [min_eq_right (le_of_lt (lt_of_not_ge h)), abs_of_nonneg (by linarith)]
          linarith [min_le_right ρ₁ ρ₂]
  obtain ⟨η, δ, hη, hδ, hfloor, hslab⟩ := key
  -- ## step 2: the homeomorphism
  let hPrism : Pr a b ≃ₜ Pr a b :=
    { toFun := prismPushFun (a := a) F φ γ η δ
      invFun := prismPushInvFun (a := a) F φ γ η δ
      left_inv := fun x => Push.prismPushInvFun_prismPushFun F φ γ hδ x
      right_inv := fun x => Push.prismPushFun_prismPushInvFun F φ γ hδ x
      continuous_toFun := Push.prismPushFun_continuous hFcl hφ hγ hfr hη hδ
      continuous_invFun := Push.prismPushInvFun_continuous hFcl hφ hγ hfr hη hδ }
  have hPrism_apply : ∀ x : Pr a b, hPrism x = prismPushFun (a := a) F φ γ η δ x :=
    fun x => rfl
  -- ## step 3: the support
  set C : Set (Pr a b) :=
    {x | ‖x.1‖ ≤ η ∧ x.2.1 ∈ F ∧ φ x.2.1 ≤ x.2.2 ∧ x.2.2 ≤ γ x.2.1 + δ} with hCdef
  have hmemImage : ∀ z t, z ∈ F → φ z ≤ t → t ≤ γ z + δ →
      (z, t) ∈ ((fun p : PL.E b × ℝ => (p.1, φ p.1 + p.2 * (γ p.1 + δ - φ p.1))) ''
        (F ×ˢ Icc (0 : ℝ) 1)) := by
    intro z t hz h1 h2
    rw [Set.mem_image]
    by_cases h0 : γ z + δ - φ z = 0
    · refine ⟨(z, 0), ⟨hz, ⟨le_rfl, zero_le_one⟩⟩, ?_⟩
      rw [zero_mul, add_zero]
      exact Prod.ext rfl (le_antisymm h1 (by linarith))
    · have hpos : 0 < γ z + δ - φ z := by
        have : 0 ≤ γ z + δ - φ z := by linarith [hle z hz]
        exact lt_of_le_of_ne this (Ne.symm h0)
      refine ⟨(z, (t - φ z) / (γ z + δ - φ z)), ⟨hz, ⟨?_, ?_⟩⟩, ?_⟩
      · exact div_nonneg (by linarith) hpos.le
      · rw [div_le_one hpos]; linarith
      · refine Prod.ext rfl ?_
        field_simp
        ring
  have hCeq : C = closedBall (0 : PL.E a) η ×ˢ ((fun p : PL.E b × ℝ =>
      (p.1, φ p.1 + p.2 * (γ p.1 + δ - φ p.1))) '' (F ×ˢ Icc (0 : ℝ) 1)) := by
    ext x
    obtain ⟨y, z, t⟩ := x
    constructor
    · intro hx
      obtain ⟨hy, hz, h1, h2⟩ := hx
      refine ⟨?_, hmemImage z t hz h1 h2⟩
      rw [mem_closedBall, dist_zero_right]
      exact hy
    · rintro ⟨hy, p, hp, hpx⟩
      rw [hCdef]
      obtain ⟨hz, hu⟩ := hp
      rw [mem_Icc] at hu
      have hy' : ‖y‖ ≤ η := by
        rw [mem_closedBall, dist_zero_right] at hy
        exact hy
      obtain ⟨hz1, ht1⟩ := Prod.ext_iff.mp hpx.symm
      subst hz1
      subst ht1
      have hL0 : 0 ≤ γ p.1 + δ - φ p.1 := by linarith [hle p.1 hz]
      exact ⟨hy', hz, by nlinarith, by nlinarith⟩
  have hCmem : ∀ y z t, ‖y‖ ≤ η → z ∈ F → φ z ≤ t → t ≤ γ z + δ → (y, z, t) ∈ C := by
    intro y z t hy hz h1 h2
    rw [hCeq]
    refine ⟨?_, hmemImage z t hz h1 h2⟩
    rw [mem_closedBall, dist_zero_right]
    exact hy
  refine ⟨hPrism, ?_, ?_, ?_, ?_⟩
  · -- compactly supported inside `W`
    refine ⟨C, ?_, ?_, ?_⟩
    · rw [hCeq]
      exact (isCompact_closedBall (0 : PL.E a) η).prod
        ((hF.prod isCompact_Icc).image (by fun_prop))
    · intro x hx
      obtain ⟨hy, hz, h1, h2⟩ := hx
      exact hslab x.1 x.2.1 x.2.2 hy hz h1 h2
    · intro x hx
      obtain ⟨y, z, t⟩ := x
      rw [hPrism_apply]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      change prismTheta (φ z) (lam η y * len F φ γ z) δ t = t
      by_cases hz : z ∈ F
      · by_cases hy : ‖y‖ ≤ η
        · by_cases h1 : φ z ≤ t
          · have h2 : γ z + δ < t := by
              by_contra hcon
              exact hx (hCmem y z t hy hz h1 (le_of_not_gt hcon))
            refine prismTheta_self_of_ge (mul_nonneg (lam_nonneg η y) (len_nonneg F φ γ z)) hδ ?_
            have hL0 : 0 ≤ γ z - φ z := by linarith [hle z hz]
            have hprod : lam η y * len F φ γ z ≤ γ z - φ z := by
              rw [len_eq hz (hle z hz)]
              calc lam η y * (γ z - φ z) ≤ 1 * (γ z - φ z) :=
                    mul_le_mul_of_nonneg_right (lam_le_one hη y) hL0
                _ = γ z - φ z := one_mul _
            linarith [min_le_left δ (lam η y * len F φ γ z)]
          · exact prismTheta_self_of_le (mul_nonneg (lam_nonneg η y) (len_nonneg F φ γ z))
              (le_of_lt hδ) (le_of_lt (lt_of_not_ge h1))
        · rw [lam_eq_zero hη (le_of_lt (lt_of_not_ge hy)), zero_mul, prismTheta_zero (le_of_lt hδ)]
      · rw [len_eq_zero hz, mul_zero, prismTheta_zero (le_of_lt hδ)]
  · -- fixes `z ∉ F` and `t ≤ φ z`
    intro y z t h
    rw [hPrism_apply]
    refine Prod.ext rfl (Prod.ext rfl ?_)
    change prismTheta (φ z) (lam η y * len F φ γ z) δ t = t
    rcases h with hz | h1
    · rw [len_eq_zero hz, mul_zero, prismTheta_zero (le_of_lt hδ)]
    · exact prismTheta_self_of_le (mul_nonneg (lam_nonneg η y) (len_nonneg F φ γ z))
        (le_of_lt hδ) h1
  · -- the coordinates `y`, `z` are preserved
    intro y z t
    rw [hPrism_apply]
    exact ⟨rfl, rfl⟩
  · -- the engulfing
    intro z hz t h1 h2
    have hL0 : 0 ≤ γ z - φ z := by linarith [hle z hz]
    have hlen : len F φ γ z = γ z - φ z := len_eq hz (hle z hz)
    obtain ⟨t', ht', hθ⟩ := exists_prismTheta_eq (s := φ z) (ℓ := γ z - φ z) (δ := δ) hL0 hδ
      (by rw [mem_Icc]; exact ⟨h1, by linarith⟩)
    refine ⟨((0 : PL.E a), z, t'), hfloor 0 z t' (by simpa using hη.le) hz ht'.1 ?_, ?_⟩
    · calc t' ≤ φ z + min δ (γ z - φ z) := ht'.2
        _ ≤ φ z + δ := by linarith [min_le_left δ (γ z - φ z)]
    · rw [hPrism_apply]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      change prismTheta (φ z) (lam η (0 : PL.E a) * len F φ γ z) δ t' = t
      rw [lam_zero_right hη, one_mul, hlen, hθ]

end Work.Geo.Prism
