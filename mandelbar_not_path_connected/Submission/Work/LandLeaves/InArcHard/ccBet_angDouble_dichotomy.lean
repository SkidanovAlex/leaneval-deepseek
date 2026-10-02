/-
# The dichotomy of the cyclic order of the `2k`-fold angle map at a repelling periodic point

`Work.LandLeaves.InArcHard.ccBet_angDouble_dichotomy` is the *sign-free* form of the cyclic-order
preservation of the `2k`-fold angle map `σ = (angDouble)^[2k] = θ ↦ Int.fract (4^k θ)` on the
type of a repelling periodic point `y` of the tricorn: either `σ` preserves the cyclic betweenness
`ccBet` on the type, or it reverses it, *with one and the same orientation for all triples*.

The sign itself is not determined here; the geometric input is the sign-free "sector transfer" of
the second return map `τ = (T_c)^{2k}`, isolated in the sibling module
`Submission.Work.LandLeaves.InArcHard.sectorTransfer`:

> near `y`, `τ` carries the far side of a co-landing pair into the far side of the pair of the
> image angles.

Given that transfer, the argument is elementary:

* for a pair `(u,v)` of type angles and a third type angle `w` with `ccBet u v w`, the angle–side
  dictionary (`paramRay_subset_pairSide_of_ccBet`) puts the whole ray `R_w` in the far side of
  `(u,v)`;
* the transfer puts the image ray `R_{σw}` (more precisely its tail near `y`, which is the image
  of the tail of `R_w`) in the far side of `(σu,σv)`;
* since a ray is preconnected and disjoint from the pair curve, its *whole* image lies in that
  far side, and the converse half of the angle–side dictionary
  (`ccBet_of_paramRay_subset_pairSide`, applied to the normalised image pair) gives `ccBet σu σv σw`.

The pair `(u,v)` is normalised by an integral shift of the second angle, and so is the image pair;
`ccBet` and `pairSide` are both insensitive to such shifts.
-/
import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.ccBet_v2_defs
import Submission.Work.LandLeaves.gmLocalOrder
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.LandLeaves.InArcHard.sectorTransfer
import Submission.Work.LandLeaves.ccBet_arcArith
import Submission.Work.LandLeaves.pairSide_nesting_farArc
import Submission.Work.LandLeaves.rayPt_iterate_angDouble
import Submission.Work.LandLeaves.exists_local_repelling_branch
import Submission.Work.ELTop.All
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.ELTop.paramRay_disjoint
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.TopJordan.Main
import Submission.Work.FSeed.Rays.landsAt_periodic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves.InArcHard

open Classical Filter
open scoped Topology

noncomputable section

variable {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}

/-- The `Work.EL` landing statement attached to a `rayAccum` singleton at `y`. -/
theorem landsN_of_rayAccum'' (hφ : Work.ParamRays.IsDynBottcher c φ) {θ : ℝ}
    (h : Work.Landing.rayAccum c φ θ = {y}) :
    Work.EL.LandsN (Work.LandLeaves.dynBNakane hφ) θ y :=
  (Work.ELTop.landsN_iff_landsAt (Work.LandLeaves.dynBNakane hφ) hφ θ y).mpr
    (Work.LandLeaves.landsAt_of_rayAccum hφ h)

/-! ## Angle arithmetic and the invariance of the far side under integral shifts -/

/-- `ccBet` is insensitive to an integral shift of its second argument. -/
theorem ccBet_shift_mid (a b x : ℝ) (m : ℤ) :
    Work.LandLeaves.ccBet a (b + (m : ℝ)) x ↔ Work.LandLeaves.ccBet a b x := by
  unfold Work.LandLeaves.ccBet
  rw [show b + (m : ℝ) - a = (b - a) + (m : ℝ) by ring, Int.fract_add_intCast]

/-- The `2k`-fold angle map is insensitive to integral shifts of its argument. -/
theorem angDouble_iterate_two_mul_add_int' {k : ℕ} (hk : 0 < k) (θ : ℝ) (m : ℤ) :
    (Work.Landing.angDouble)^[2 * k] (θ + (m : ℝ)) = (Work.Landing.angDouble)^[2 * k] θ := by
  rw [Work.LandLeaves.angDouble_iterate_two_mul hk (θ + (m : ℝ)),
    Work.LandLeaves.angDouble_iterate_two_mul hk θ,
    show (4 : ℝ) ^ k * (θ + (m : ℝ))
        = (4 : ℝ) ^ k * θ + ((((4 : ℕ) ^ k) * m : ℤ) : ℝ) by push_cast; ring,
    Int.fract_add_intCast]

/-- The far side of a pair of rays only depends on its two angles modulo `1`. -/
theorem side_add_int (hN : Work.EL.DynB c φ) (A B : ℝ) (m : ℤ) :
    Work.EL.RawPair.side hN (⟨A, B + (m : ℝ), y⟩ : Work.EL.RawPair)
      = Work.EL.RawPair.side hN (⟨A, B, y⟩ : Work.EL.RawPair) := by
  have hcurve : Work.EL.RawPair.curve hN (⟨A, B + (m : ℝ), y⟩ : Work.EL.RawPair)
      = Work.EL.RawPair.curve hN (⟨A, B, y⟩ : Work.EL.RawPair) := by
    have hpar : Work.EL.paramRay hN (B + (m : ℝ)) = Work.EL.paramRay hN B :=
      Work.ELTop.paramRay_add_int hN B m
    show Work.EL.paramRay hN A ∪ {y} ∪ Work.EL.paramRay hN (B + (m : ℝ))
        = Work.EL.paramRay hN A ∪ {y} ∪ Work.EL.paramRay hN B
    rw [hpar]
  have harc : Work.EL.arcLen A (B + (m : ℝ)) = Work.EL.arcLen A B := by
    unfold Work.EL.arcLen
    rw [show B + (m : ℝ) - A = (B - A) + (m : ℝ) by ring, Int.fract_add_intCast]
  show connectedComponentIn (Work.EL.RawPair.curve hN (⟨A, B + (m : ℝ), y⟩ : Work.EL.RawPair))ᶜ
      (Work.EL.rayPt hN (A + Work.EL.arcLen A (B + (m : ℝ)) / 2) 2)
    = connectedComponentIn (Work.EL.RawPair.curve hN (⟨A, B, y⟩ : Work.EL.RawPair))ᶜ
      (Work.EL.rayPt hN (A + Work.EL.arcLen A B / 2) 2)
  rw [hcurve, harc]

/-! ## Non-degeneracy of the image pair -/

/-- **The `2k`-fold angle map is injective modulo `1` on the type of `y`.**  If two angles `p`,
`q` whose rays both land at the repelling periodic point `y` are incongruent modulo `1`, then so
are their images. -/
theorem image_fract_ne_zero {p q : ℝ} (hφ : Work.ParamRays.IsDynBottcher c φ)
    (hrep : Work.Landing.IsRepelling c k y)
    (hp : Work.Landing.rayAccum c φ p = {y}) (hq : Work.Landing.rayAccum c φ q = {y})
    (hnd : Int.fract (q - p) ≠ 0) :
    Int.fract ((Work.Landing.angDouble)^[2 * k] q - (Work.Landing.angDouble)^[2 * k] p) ≠ 0 := by
  intro h0
  have hk : 0 < k := hrep.1.1
  obtain ⟨m, hm⟩ := Int.fract_eq_zero_iff.mp h0
  have hkey : ∃ m' : ℤ, (4 : ℝ) ^ k * q = (4 : ℝ) ^ k * p + (m' : ℝ) := by
    refine ⟨m + ⌊(4 : ℝ) ^ k * q⌋ - ⌊(4 : ℝ) ^ k * p⌋, ?_⟩
    have f1 : (4 : ℝ) ^ k * p - Int.fract ((4 : ℝ) ^ k * p) = (⌊(4 : ℝ) ^ k * p⌋ : ℝ) :=
      Int.self_sub_fract _
    have f2 : (4 : ℝ) ^ k * q - Int.fract ((4 : ℝ) ^ k * q) = (⌊(4 : ℝ) ^ k * q⌋ : ℝ) :=
      Int.self_sub_fract _
    rw [← Work.LandLeaves.angDouble_iterate_two_mul hk q] at f2
    rw [← Work.LandLeaves.angDouble_iterate_two_mul hk p] at f1
    push_cast
    linarith
  obtain ⟨mm, hmm⟩ :=
    Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq hφ hrep hq hp hkey
  have hmm' : q - p = (mm : ℝ) := by linarith
  rw [hmm', Int.fract_intCast] at hnd
  exact hnd rfl

/-! ## The forward orientation, from the sector transfer -/

/-- **Cyclic-order preservation of the `2k`-fold angle map, given the sector transfer.**

If the second return map carries the far side of a co-landing pair near `y` into the far side of
the pair of the image angles (`Work.LandLeaves.InArcHard.sectorTransfer`), then the `2k`-fold
angle map preserves the cyclic betweenness on the type of `y`. -/
theorem ccBet_angDouble_of_sectorTransfer (hφ : Work.ParamRays.IsDynBottcher c φ)
    (hrep : Work.Landing.IsRepelling c k y)
    {a b x : ℝ} (ha : Work.Landing.rayAccum c φ a = {y})
    (hb : Work.Landing.rayAccum c φ b = {y}) (hx : Work.Landing.rayAccum c φ x = {y})
    (hab : Work.LandLeaves.ccBet a b x) :
    Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b) ((Work.Landing.angDouble)^[2 * k] x) := by
  have hk : 0 < k := hrep.1.1
  -- the non-degeneracies of the source triple
  have hp : 0 < Int.fract (b - a) := lt_trans hab.1 hab.2
  have hxapos : 0 < Int.fract (x - a) := hab.1
  have hxbpos : 0 < Int.fract (x - b) := by
    have h := Work.LandLeaves.fract_arc_eq a b x hab
    linarith [Int.fract_lt_one (b - a)]
  -- normalise the source pair
  set b' : ℝ := a + Int.fract (b - a) with hb'def
  have hb'eq : b = b' + (⌊b - a⌋ : ℝ) := by
    have h1 := Int.fract_add_floor (b - a); rw [hb'def]; linarith
  have hlt1 : a < b' := by rw [hb'def]; linarith
  have hlt2 : b' < a + 1 := by rw [hb'def]; linarith [Int.fract_lt_one (b - a)]
  have hnd : Int.fract (b' - a) ≠ 0 := by
    have h : b' - a = Int.fract (b - a) := by rw [hb'def]; ring
    rw [h, Int.fract_fract]; exact ne_of_gt hp
  have hacc_b' : Work.Landing.rayAccum c φ b' = {y} := by
    have hb'' : Work.Landing.rayAccum c φ (b' + (⌊b - a⌋ : ℝ)) = {y} := by
      rw [← hb'eq]; exact hb
    rwa [Work.FSeed.rayAccum_add_int c φ b' ⌊b - a⌋] at hb''
  have hcc : Work.LandLeaves.ccBet a b' x := by
    have h : Work.LandLeaves.ccBet a (b' + (⌊b - a⌋ : ℝ)) x := by rw [← hb'eq]; exact hab
    exact (ccBet_shift_mid a b' x ⌊b - a⌋).mp h
  -- the angle map is injective modulo `1` on the type
  have hσb_eq : (Work.Landing.angDouble)^[2 * k] b' = (Work.Landing.angDouble)^[2 * k] b := by
    have h : b' = b + ((-⌊b - a⌋ : ℤ) : ℝ) := by
      push_cast
      linarith [hb'eq]
    rw [h, angDouble_iterate_two_mul_add_int' hk b (-⌊b - a⌋)]
  have hnd_ab : Int.fract ((Work.Landing.angDouble)^[2 * k] b - (Work.Landing.angDouble)^[2 * k] a)
      ≠ 0 := image_fract_ne_zero hφ hrep ha hb (ne_of_gt hp)
  have hnd_ax : Int.fract ((Work.Landing.angDouble)^[2 * k] x - (Work.Landing.angDouble)^[2 * k] a)
      ≠ 0 := image_fract_ne_zero hφ hrep ha hx (ne_of_gt hxapos)
  have hnd_bx : Int.fract ((Work.Landing.angDouble)^[2 * k] x - (Work.Landing.angDouble)^[2 * k] b)
      ≠ 0 := image_fract_ne_zero hφ hrep hb hx (ne_of_gt hxbpos)
  have hnd_ax' : Int.fract ((Work.Landing.angDouble)^[2 * k] x
      - (Work.Landing.angDouble)^[2 * k] a) ≠ 0 := hnd_ax
  have hnd_bx' : Int.fract ((Work.Landing.angDouble)^[2 * k] x
      - (Work.Landing.angDouble)^[2 * k] b') ≠ 0 := by
    rw [hσb_eq]; exact hnd_bx
  have hnd_ab' : Int.fract ((Work.Landing.angDouble)^[2 * k] b'
      - (Work.Landing.angDouble)^[2 * k] a) ≠ 0 := by
    rw [hσb_eq]; exact hnd_ab
  -- the transfer
  set hN : Work.EL.DynB c φ := Work.LandLeaves.dynBNakane hφ with hNdef
  obtain ⟨ε, hεpos, htr⟩ := sectorTransfer hφ hrep ha hacc_b' hnd
  -- the source ray lies in the far side of the source pair
  have hsub : Work.EL.paramRay hN x ⊆
      Work.EL.pairSide (Work.LandLeaves.mkPair hN (landsN_of_rayAccum'' hφ ha)
        (landsN_of_rayAccum'' hφ hacc_b')) :=
    Work.LandLeaves.paramRay_subset_pairSide_of_ccBet hN (landsN_of_rayAccum'' hφ ha)
      (landsN_of_rayAccum'' hφ hacc_b') hlt1 hlt2 hcc
  -- a point of the source ray close to `y`
  have hxN : Work.EL.LandsN hN x y := landsN_of_rayAccum'' hφ hx
  haveI : (nhdsWithin (1 : ℝ) (Set.Ioi 1)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hev : ∀ᶠ t in nhdsWithin (1 : ℝ) (Set.Ioi 1), (1 < t) ∧ ‖Work.EL.rayPt hN x t - y‖ < ε := by
    filter_upwards [self_mem_nhdsWithin, hxN.eventually (Metric.ball_mem_nhds y hεpos)]
      with t ht hb
    exact ⟨ht, by simpa [Metric.mem_ball, dist_eq_norm] using hb⟩
  obtain ⟨t, ht1, htε⟩ := hev.exists
  have hzmem : Work.EL.rayPt hN x t ∈
      Work.EL.pairSide (Work.LandLeaves.mkPair hN (landsN_of_rayAccum'' hφ ha)
        (landsN_of_rayAccum'' hφ hacc_b')) :=
    hsub (Work.EL.rayPt_mem_paramRay hN ht1)
  have himg := htr (Work.EL.rayPt hN x t) hzmem htε
  rw [← Work.LandLeaves.rayPt_iterate_angDouble hN hφ ht1] at himg
  -- the image ray is disjoint from the image pair curve
  have hray_curve : Work.EL.paramRay hN ((Work.Landing.angDouble)^[2 * k] x) ⊆
      (Work.EL.pairCurve (Work.LandLeaves.mkPair hN
        (landsN_of_rayAccum'' hφ (Work.LandLeaves.rayAccum_angDouble_singleton' hφ hrep ha))
        (landsN_of_rayAccum'' hφ
          (Work.LandLeaves.rayAccum_angDouble_singleton' hφ hrep hacc_b'))))ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff, Work.EL.mem_pairCurve_iff]
    push_neg
    refine ⟨?_, ?_, ?_⟩
    · intro hza
      have hne : ∀ m : ℤ, (Work.Landing.angDouble)^[2 * k] a
          ≠ (Work.Landing.angDouble)^[2 * k] x + m := by
        intro m hm
        refine hnd_ax' ?_
        have hneg : (Work.Landing.angDouble)^[2 * k] x - (Work.Landing.angDouble)^[2 * k] a
            = ((-m : ℤ) : ℝ) := by push_cast; linarith
        rw [hneg, Int.fract_intCast]
      exact Set.disjoint_left.mp (Work.ELTop.paramRay_disjoint hN hne) hz hza
    · intro hzy
      have hyK : y ∈ Work.EL.K c := Work.ELTop.landsN_mem_K hN hxN
      exact (Work.EL.paramRay_subset_compl hN _ hz) (by rw [hzy]; exact hyK)
    · intro hzb
      have hne : ∀ m : ℤ, (Work.Landing.angDouble)^[2 * k] b'
          ≠ (Work.Landing.angDouble)^[2 * k] x + m := by
        intro m hm
        refine hnd_bx' ?_
        have hneg : (Work.Landing.angDouble)^[2 * k] x - (Work.Landing.angDouble)^[2 * k] b'
            = ((-m : ℤ) : ℝ) := by push_cast; linarith
        rw [hneg, Int.fract_intCast]
      exact Set.disjoint_left.mp (Work.ELTop.paramRay_disjoint hN hne) hz hzb
  -- hence the whole image ray lies in the far side of the image pair
  have htpow : 1 < t ^ (4 ^ k : ℕ) := one_lt_pow₀ ht1 (by positivity)
  have hray : Work.EL.paramRay hN ((Work.Landing.angDouble)^[2 * k] x) ⊆
      Work.EL.pairSide (Work.LandLeaves.mkPair hN
        (landsN_of_rayAccum'' hφ (Work.LandLeaves.rayAccum_angDouble_singleton' hφ hrep ha))
        (landsN_of_rayAccum'' hφ
          (Work.LandLeaves.rayAccum_angDouble_singleton' hφ hrep hacc_b'))) := by
    have hside : Work.EL.pairSide (Work.LandLeaves.mkPair hN
          (landsN_of_rayAccum'' hφ (Work.LandLeaves.rayAccum_angDouble_singleton' hφ hrep ha))
          (landsN_of_rayAccum'' hφ
            (Work.LandLeaves.rayAccum_angDouble_singleton' hφ hrep hacc_b')))
        = connectedComponentIn (Work.EL.pairCurve (Work.LandLeaves.mkPair hN
            (landsN_of_rayAccum'' hφ (Work.LandLeaves.rayAccum_angDouble_singleton' hφ hrep ha))
            (landsN_of_rayAccum'' hφ
              (Work.LandLeaves.rayAccum_angDouble_singleton' hφ hrep hacc_b'))))ᶜ
          (Work.EL.rayPt hN ((Work.Landing.angDouble)^[2 * k] x) (t ^ (4 ^ k : ℕ))) :=
      connectedComponentIn_eq himg
    intro z hz
    rw [hside]
    exact IsPreconnected.subset_connectedComponentIn
      (Work.ELTop.isPreconnected_paramRay hN ((Work.Landing.angDouble)^[2 * k] x))
      (Work.EL.rayPt_mem_paramRay hN htpow) hray_curve hz
  -- normalise the image pair
  have himgpos : 0 < Int.fract ((Work.Landing.angDouble)^[2 * k] b'
      - (Work.Landing.angDouble)^[2 * k] a) :=
    lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hnd_ab')
  set mb : ℤ := -⌊(Work.Landing.angDouble)^[2 * k] b' - (Work.Landing.angDouble)^[2 * k] a⌋ with hmb
  have hnorm1 : (Work.Landing.angDouble)^[2 * k] a
      < (Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ) := by
    have h := Int.fract_add_floor ((Work.Landing.angDouble)^[2 * k] b'
      - (Work.Landing.angDouble)^[2 * k] a)
    rw [hmb]; push_cast; linarith
  have hnorm2 : (Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ)
      < (Work.Landing.angDouble)^[2 * k] a + 1 := by
    have h := Int.fract_add_floor ((Work.Landing.angDouble)^[2 * k] b'
      - (Work.Landing.angDouble)^[2 * k] a)
    have hlt := Int.fract_lt_one ((Work.Landing.angDouble)^[2 * k] b'
      - (Work.Landing.angDouble)^[2 * k] a)
    rw [hmb]; push_cast; linarith
  -- the same far side, expressed with the shifted image angle
  have hray_raw : Work.EL.paramRay hN ((Work.Landing.angDouble)^[2 * k] x) ⊆
      Work.EL.RawPair.side hN (⟨(Work.Landing.angDouble)^[2 * k] a,
        (Work.Landing.angDouble)^[2 * k] b', y⟩ : Work.EL.RawPair) := by
    simpa [Work.EL.pairSide_eq, Work.LandLeaves.mkPair] using hray
  have hray_norm : Work.EL.paramRay hN ((Work.Landing.angDouble)^[2 * k] x) ⊆
      Work.EL.RawPair.side hN (⟨(Work.Landing.angDouble)^[2 * k] a,
        (Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ), y⟩ : Work.EL.RawPair) := by
    rw [side_add_int (y := y) hN ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b') mb]
    exact hray_raw
  -- the angle–side dictionary, converse direction, for the normalised image pair
  have hsgN : Work.EL.LandsN hN ((Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ)) y := by
    have hacc : Work.Landing.rayAccum c φ ((Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ))
        = {y} := by
      rw [Work.FSeed.rayAccum_add_int]
      exact Work.LandLeaves.rayAccum_angDouble_singleton' hφ hrep hacc_b'
    exact (Work.ELTop.landsN_iff_landsAt hN hφ _ y).mpr
      (Work.LandLeaves.landsAt_of_rayAccum hφ hacc)
  have hσaN : Work.EL.LandsN hN ((Work.Landing.angDouble)^[2 * k] a) y :=
    landsN_of_rayAccum'' hφ (Work.LandLeaves.rayAccum_angDouble_singleton' hφ hrep ha)
  have hσxN : Work.EL.LandsN hN ((Work.Landing.angDouble)^[2 * k] x) y :=
    landsN_of_rayAccum'' hφ (Work.LandLeaves.rayAccum_angDouble_singleton' hφ hrep hx)
  have hnd_bx'' : Int.fract ((Work.Landing.angDouble)^[2 * k] x
      - ((Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ))) ≠ 0 := by
    rw [show (Work.Landing.angDouble)^[2 * k] x
          - ((Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ))
        = ((Work.Landing.angDouble)^[2 * k] x - (Work.Landing.angDouble)^[2 * k] b')
          + ((-mb : ℤ) : ℝ) by push_cast; ring, Int.fract_add_intCast]
    exact hnd_bx'
  have hnd_ab'' : Int.fract (((Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ))
      - (Work.Landing.angDouble)^[2 * k] a) ≠ 0 := by
    rw [show ((Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ))
          - (Work.Landing.angDouble)^[2 * k] a
        = ((Work.Landing.angDouble)^[2 * k] b' - (Work.Landing.angDouble)^[2 * k] a)
          + (mb : ℝ) by ring, Int.fract_add_intCast]
    exact hnd_ab'
  have hcc' : Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b' + (mb : ℝ)) ((Work.Landing.angDouble)^[2 * k] x) :=
    Work.LandLeaves.ccBet_of_paramRay_subset_pairSide hN Work.TopJordan.jordanForm hσaN hsgN
      hσxN hnorm1 hnorm2 hnd_ax' hnd_bx'' hnd_ab''
      (by simpa [Work.EL.pairSide_eq, Work.LandLeaves.mkPair] using hray_norm)
  -- undo the two normalisations
  have hcc'' : Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b') ((Work.Landing.angDouble)^[2 * k] x) :=
    (ccBet_shift_mid ((Work.Landing.angDouble)^[2 * k] a) ((Work.Landing.angDouble)^[2 * k] b')
      ((Work.Landing.angDouble)^[2 * k] x) mb).mp hcc'
  rw [hσb_eq] at hcc''
  exact hcc''

/-! ## The dichotomy -/

theorem ccBet_angDouble_dichotomy {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y) :
    (∀ a b x : ℝ, Work.Landing.rayAccum c φ a = {y} → Work.Landing.rayAccum c φ b = {y} →
        Work.Landing.rayAccum c φ x = {y} → Work.LandLeaves.ccBet a b x →
        Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
          ((Work.Landing.angDouble)^[2 * k] b) ((Work.Landing.angDouble)^[2 * k] x)) ∨
    (∀ a b x : ℝ, Work.Landing.rayAccum c φ a = {y} → Work.Landing.rayAccum c φ b = {y} →
        Work.Landing.rayAccum c φ x = {y} → Work.LandLeaves.ccBet a b x →
        Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] b)
          ((Work.Landing.angDouble)^[2 * k] a) ((Work.Landing.angDouble)^[2 * k] x)) :=
  Or.inl fun a b x ha hb hx hab => ccBet_angDouble_of_sectorTransfer hφ hrep ha hb hx hab

end

end Work.LandLeaves.InArcHard
