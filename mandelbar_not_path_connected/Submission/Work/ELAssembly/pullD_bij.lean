import Mathlib
import Submission.Work.ELAssembly.landsN_add_int
import Submission.Work.ELAssembly.PullInputs
import Submission.Work.ELAssembly.bijOn_of_isCoveringMapOn_of_fibre
import Submission.Work.ELAssembly.pot_iterate
import Submission.Work.ELAssembly.pullD_pair
import Submission.Work.ELAssembly.D_adm_of
import Submission.Work.ELTop.polyCurve_isJordan
import Submission.Work.ELTop.RegionBasics
import Submission.Work.ELTop.isOpen_polyRegion
import Submission.Work.ELTop.isClosed_polyCurve
import Submission.Work.ELTop.seed_mem_polyRegion
import Submission.Work.ELTop.mem_polyRegion_iff_of_notMem_K
import Submission.Work.ELTop.polyRegion_eq_inter_pairSideNear
import Submission.Work.ELTop.rayPiece_eq_image
import Submission.Work.ELTop.landsN_map
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELTop.rayPt_inj
import Submission.Work.Top.rayPt_injOn
import Submission.Work.ELPull.isCoveringMapOn_tsqIterate
import Submission.Work.ELPull.critValues_tsqIterate
import Submission.Work.ELRig.rayPt_iterate
import Submission.Work.ELRig.rayTail_lift
import Submission.Work.Top.extAngle_rayPt
import Submission.Work.Top.mem_paramRay_extAngle
import Submission.Work.Top.extAngle_of_mem_paramRay
import Submission.Work.TopJordan.Jordan
import Submission.Work.ELNest.armChain_nest

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELAssembly

open Classical Filter Set
open scoped Topology

noncomputable section

open LeanEval.ComplexAnalysis (Tantibar)

variable {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {N : NestPairs d}

/-- The three level-`n` pairs of the `b₂`-nest as a list. -/
abbrev Dps (N : NestPairs d) (n : ℕ) : List (Work.EL.CoPair d.hN) := [N.Za n, N.Zb n, N.Zc n]

/-! ## Elementary arithmetic of the levels `Dlev L n` -/

/-- `Dlev L m > 0` for `L > 1`. -/
lemma Dlev_pos {L : ℝ} (hL : 1 < L) (m : ℕ) : 0 < Work.ELNest.Dlev L m :=
  Real.rpow_pos_of_pos (by linarith) _

/-- `Dlev L m > 1` for `L > 1`. -/
lemma one_lt_Dlev {L : ℝ} (hL : 1 < L) (m : ℕ) : 1 < Work.ELNest.Dlev L m :=
  Real.one_lt_rpow hL (by positivity)

/-- `log (Dlev L m) = (1/64^m) * log L`. -/
lemma log_Dlev {L : ℝ} (hL : 1 < L) (m : ℕ) :
    Real.log (Work.ELNest.Dlev L m) = (1 / (64 : ℝ) ^ m) * Real.log L := by
  rw [Work.ELNest.Dlev, Real.log_rpow (by linarith : (0:ℝ) < L)]

/-- `64 * log (Dlev L (n+1)) = log (Dlev L n)`. -/
lemma log_Dlev_succ {L : ℝ} (hL : 1 < L) (n : ℕ) :
    64 * Real.log (Work.ELNest.Dlev L (n + 1)) = Real.log (Work.ELNest.Dlev L n) := by
  rw [log_Dlev hL, log_Dlev hL, pow_succ]
  field_simp

/-- `(Dlev L (n+1)) ^ 64 = Dlev L n`. -/
lemma Dlev_pow {L : ℝ} (hL : 1 < L) (n : ℕ) :
    (Work.ELNest.Dlev L (n + 1)) ^ (64 : ℕ) = Work.ELNest.Dlev L n := by
  have hL0 : (0:ℝ) < L := by linarith
  rw [Work.ELNest.Dlev, Work.ELNest.Dlev, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hL0)]
  congr 1
  rw [pow_succ]
  field_simp
  norm_num

/-- The potential is multiplied by `64` under `F6 = f_c^6`. -/
lemma pot_F6 (d : Work.EL.RootParabolic c) (z : ℂ) :
    Work.EL.pot d.hN (Work.ELNest.F6 c z) = 64 * Work.EL.pot d.hN z := by
  have h := Work.ELAssembly.pot_iterate d 6 z
  rw [Work.ELNest.F6_eq_tantibar]
  simp only [h]
  norm_num

/-- `F6 = f_c^6` is the sixth iterate of `Tantibar c`. -/
lemma F6_apply (z : ℂ) : Work.ELNest.F6 c z = (Tantibar c)^[6] z := by
  rw [Work.ELNest.F6_eq_tantibar]

/-- `T^[6] θ = fract (64 θ)` lies in `[0,1)`. -/
lemma T6_mem_Ico (θ : ℝ) : (Work.EL.T)^[6] θ ∈ Set.Ico (0 : ℝ) 1 := by
  rw [T_iterate_six]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- `T^[6]` commutes with integer shifts of the angle. -/
lemma T6_add_int (θ : ℝ) (k : ℤ) : (Work.EL.T)^[6] (θ + k) = (Work.EL.T)^[6] θ := by
  rw [T_iterate_six, T_iterate_six,
    show 64 * (θ + (k : ℝ)) = 64 * θ + ((64 * k : ℤ) : ℝ) by push_cast; ring,
    Int.fract_add_intCast]

/-! ## The boundary angles of the two polygons -/

/-- The boundary angles of the level-`(n+1)` `b₂`-polygon are carried by `T^[6]` to the
corresponding boundary angles of the level-`n` polygon. -/
lemma T6_angle_of_mem {n : ℕ} {P' : Work.EL.CoPair d.hN} (hP' : P' ∈ Dps N (n + 1)) :
    ∃ Q ∈ Dps N n, (∃ k : ℤ, (Work.EL.T)^[6] P'.a = Q.a + k) ∧
      (∃ k : ℤ, (Work.EL.T)^[6] P'.b = Q.b + k) := by
  have hpair := pullD_pair n
  simp only [Dps, List.mem_cons, List.mem_nil_iff, or_false] at hP'
  rcases hP' with rfl | rfl | rfl
  · refine ⟨N.Za n, by simp [Dps], ⟨0, ?_⟩, ⟨0, ?_⟩⟩
    · rw [N.Zaa (n + 1), N.Zaa n]; simpa using hpair.1
    · rw [N.Zab (n + 1), N.Zab n]; simpa using hpair.2.1
  · refine ⟨N.Zb n, by simp [Dps], ⟨0, ?_⟩, ⟨0, ?_⟩⟩
    · rw [N.Zba (n + 1), N.Zba n]; simpa using hpair.2.2.1
    · rw [N.Zbb (n + 1), N.Zbb n]; simpa using hpair.2.2.2.1
  · refine ⟨N.Zc n, by simp [Dps], ⟨0, ?_⟩, ⟨-1, ?_⟩⟩
    · rw [N.Zca (n + 1), N.Zca n]; simpa using hpair.2.2.2.2.1
    · rw [N.Zcb (n + 1), N.Zcb n]
      have h6 := T6_add_int (Work.ELNest.armC2 (n + 1)) 1
      rw [show Work.ELNest.armC2 (n + 1) + 1 = Work.ELNest.armC2 (n + 1) + (1 : ℤ) by
        push_cast; ring, h6, hpair.2.2.2.2.2]
      push_cast
      ring

/-- Landing is natural under the iterates of `Tantibar c`. -/
lemma landsN_iterate_map (d : Work.EL.RootParabolic c) {θ : ℝ} {y : ℂ} (n : ℕ)
    (h : Work.EL.LandsN d.hN θ y) :
    Work.EL.LandsN d.hN ((Work.EL.T)^[n] θ) ((Tantibar c)^[n] y) := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact Work.ELTop.landsN_map d.hN d.bottcher ih

/-- `LandsN` depends on the angle only modulo `ℤ` (the bundle form of
`Work.ELAssembly.landsN_add_int`, which lives in its own module). -/
lemma pullD_landsN_add_int (d : Work.EL.RootParabolic c) (θ : ℝ) (k : ℤ) (y : ℂ) :
    Work.EL.LandsN d.hN (θ + k) y ↔ Work.EL.LandsN d.hN θ y :=
  landsN_add_int d.hN θ k y

/-- The ray pieces depend on the angle only modulo `ℤ`. -/
lemma rayPiece_add_int (d : Work.EL.RootParabolic c) (β : ℝ) (k : ℤ) (t₀ R : ℝ) :
    Work.EL.rayPiece d.hN (β + k) t₀ R = Work.EL.rayPiece d.hN β t₀ R := by
  ext z
  rw [Work.ELTop.mem_rayPiece_iff, Work.ELTop.mem_rayPiece_iff]
  have hray : z ∈ Work.EL.paramRay d.hN (β + k) ↔ z ∈ Work.EL.paramRay d.hN β := by
    rw [Work.Top.NakaneData.mem_paramRay_iff, Work.Top.NakaneData.mem_paramRay_iff]
    constructor
    · rintro ⟨h1, t, ht, h2⟩
      refine ⟨h1, t, ht, ?_⟩
      have h3 : Work.Top.NakaneData.rayPoint (β + k) t = Work.Top.NakaneData.rayPoint β t :=
        Work.ELRig.rayPoint_add_int β t k
      rw [h3] at h2; exact h2
    · rintro ⟨h1, t, ht, h2⟩
      refine ⟨h1, t, ht, ?_⟩
      rw [Work.ELRig.rayPoint_add_int β t k]
      exact h2
  rw [hray]

/-! ## The off-`K` part of the image condition -/

/-- The ray point of angle `θ` at level `t` is carried by `F6 = f_c^6` to the ray point of
angle `T^[6] θ` at level `t ^ 64`. -/
lemma F6_rayPt (d : Work.EL.RootParabolic c) {θ t : ℝ} (ht : 1 < t) :
    Work.ELNest.F6 c (Work.EL.rayPt d.hN θ t)
      = Work.EL.rayPt d.hN ((Work.EL.T)^[6] θ) (t ^ (64 : ℕ)) := by
  rw [Work.ELNest.F6_eq_tantibar, Work.ELRig.rayPt_iterate_antibar d.hN d.bottcher ht 6]
  norm_num

/-- The image of a ray piece under `F6`: the ray point of angle `θ` at level `t` is carried to
the ray point of angle `T^[6] θ` at level `t ^ 64`. -/
lemma F6_rayPiece_subset (d : Work.EL.RootParabolic c) {β R' : ℝ} (hR' : 1 < R') :
    Work.ELNest.F6 c '' Work.EL.rayPiece d.hN β 0 R'
      ⊆ Work.EL.rayPiece d.hN ((Work.EL.T)^[6] β) 0 (R' ^ (64 : ℕ)) := by
  rintro z ⟨x, hx, rfl⟩
  rw [Work.ELTop.mem_rayPiece_iff] at hx ⊢
  obtain ⟨hxray, -, hxR⟩ := hx
  rw [Work.Top.NakaneData.mem_paramRay_iff] at hxray
  obtain ⟨hxK, t, ht, hxt⟩ := hxray
  have hΦ : Work.EL.dynPhi c d.φ x = Work.EL.dynPhi c d.φ (Work.EL.rayPt d.hN β t) := by
    rw [Work.Top.NakaneData.Phi_rayPt d.hN ht]; exact hxt
  have hxt' : x = Work.EL.rayPt d.hN β t :=
    Work.Top.NakaneData.injOn_Phi d.hN hxK (Work.EL.rayPt_notMem_K d.hN ht) hΦ
  have hpot : Work.EL.pot d.hN x = Real.log t := by
    rw [hxt', Work.EL.pot_rayPt d.hN ht]
  have htR' : t ≤ R' := by
    have h := hxR; rw [hpot] at h
    exact (Real.log_le_log_iff (by linarith) (by linarith)).mp h
  have hFt : Work.ELNest.F6 c x = Work.EL.rayPt d.hN ((Work.EL.T)^[6] β) (t ^ (64 : ℕ)) := by
    rw [hxt', Work.ELNest.F6_eq_tantibar,
      Work.ELRig.rayPt_iterate_antibar d.hN d.bottcher ht 6]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [hFt]
    exact Work.EL.rayPt_mem_paramRay d.hN (one_lt_pow₀ ht (by norm_num))
  · rw [pot_F6, hpot]
    have : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
    linarith
  · have hlog : Real.log t ≤ Real.log R' := Real.log_le_log (by linarith) htR'
    rw [pot_F6, hpot, Real.log_pow]
    exact mul_le_mul_of_nonneg_left hlog (by norm_num)

/-- **The image condition off the filled Julia set.**  If `x` lies in the level-`(n+1)` region
and not in `K c`, then `f_c^6 x` lies in the level-`n` region. -/
lemma F6_mem_Dregion_of_notMem_K (I : DPullInputs c d L N)
    (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible (Dps N n)) (n : ℕ) {x : ℂ}
    (hxU : x ∈ Work.EL.polyRegion (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1)))
    (hxK : x ∉ Work.EL.K c) :
    Work.ELNest.F6 c x ∈ Work.EL.polyRegion (Dps N n) (Work.ELNest.Dlev L n) := by
  have hR : 1 < Work.ELNest.Dlev L n := one_lt_Dlev I.hL n
  have hR' : 1 < Work.ELNest.Dlev L (n + 1) := one_lt_Dlev I.hL (n + 1)
  have hC : Work.Top.IsJordanCurve (Work.EL.polyCurve (Dps N n) (Work.ELNest.Dlev L n)) :=
    Work.ELTop.polyCurve_isJordan d.hN _ (hadm n) hR
  have hC' : Work.Top.IsJordanCurve
      (Work.EL.polyCurve (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1))) :=
    Work.ELTop.polyCurve_isJordan d.hN _ (hadm (n + 1)) hR'
  obtain ⟨harc, hpot⟩ := (Work.ELTop.mem_polyRegion_iff_of_notMem_K d.hN Work.TopJordan.jordanForm
    (Dps N (n + 1)) (hadm (n + 1)) hR' hC' hxK).mp hxU
  -- `F6 x ∉ K c`
  have hxesc : Work.ParamRays.Escaping c x :=
    (Work.ParamRays.escaping_iff_not_bounded c x).mpr hxK
  have hFK : Work.ELNest.F6 c x ∉ Work.EL.K c := by
    rw [F6_apply]
    exact (Work.ParamRays.escaping_iff_not_bounded c _).mp (hxesc.iterate 6)
  -- the angle of `F6 x` is `T^[6]` of the angle of `x`
  set θ : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) x with hθ
  have hang : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (Work.ELNest.F6 c x)
      = (Work.EL.T)^[6] θ := by
    have ht : 1 < Real.exp (Work.EL.pot d.hN x) := Work.ELTop.one_lt_exp_pot d.hN hxK
    have h1 : Work.ELNest.F6 c x
        = Work.EL.rayPt d.hN ((Work.EL.T)^[6] θ)
            ((Real.exp (Work.EL.pot d.hN x)) ^ (64 : ℕ)) := by
      conv_lhs => rw [show x = Work.EL.rayPt d.hN θ (Real.exp (Work.EL.pot d.hN x)) from by
        rw [hθ]
        exact (Work.ELTop.rayPt_extAngle_exp_pot d.hN hxK).symm]
      exact F6_rayPt d ht
    rw [h1]
    exact Work.Top.extAngle_rayPt d.hN (T6_mem_Ico θ).1 (T6_mem_Ico θ).2
      (one_lt_pow₀ ht (by norm_num))
  refine (Work.ELTop.mem_polyRegion_iff_of_notMem_K d.hN Work.TopJordan.jordanForm
    (Dps N n) (hadm n) hR hC hFK).mpr ⟨?_, ?_⟩
  · intro P hP
    rw [hang]
    exact I.arc n θ (by intro P' hP'; exact harc P' hP') P hP
  · rw [pot_F6]
    calc 64 * Work.EL.pot d.hN x < 64 * Real.log (Work.ELNest.Dlev L (n + 1)) := by
          linarith
      _ = Real.log (Work.ELNest.Dlev L n) := log_Dlev_succ I.hL n

end

end Work.ELAssembly

namespace Work.ELAssembly

open Classical Filter Set
open scoped Topology

noncomputable section

open LeanEval.ComplexAnalysis (Tantibar)

variable {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {N : NestPairs d}

/-- `F6` maps the filled Julia set into itself. -/
lemma F6_mem_K {x : ℂ} (hx : x ∈ Work.EL.K c) : Work.ELNest.F6 c x ∈ Work.EL.K c := by
  rw [F6_apply]
  exact Work.ParamRays.BoundedOrbit.shift hx 6

/-- The reference angle `midNear` of the level-`n` `b₂`-polygon lies in `[0,1)`. -/
lemma midNear_Dps_mem_Ico (n : ℕ) : Work.EL.midNear (Dps N n) ∈ Set.Ico (0 : ℝ) 1 := by
  have hy : 0 < ((64:ℝ)^n)⁻¹ := by positivity
  have hy1 : ((64:ℝ)^n)⁻¹ ≤ 1 := inv_pow_64_le_one n
  have hA2 : 0 ≤ Work.ELNest.armA2 n ∧ Work.ELNest.armA2 n < 1 := by
    rw [Work.ELNest.armA2_closed n]
    exact ⟨by nlinarith [hy, hy1], by nlinarith [hy, hy1]⟩
  have hB1 : 0 ≤ Work.ELNest.armB1 n ∧ Work.ELNest.armB1 n < 1 := by
    rw [Work.ELNest.armB1_closed n]
    exact ⟨by nlinarith [hy, hy1], by nlinarith [hy, hy1]⟩
  have hAB : Work.ELNest.armA2 n < Work.ELNest.armB1 n := (arm_angles_lt n).2.1
  have hdiff : (0:ℝ) < Work.ELNest.armB1 n - Work.ELNest.armA2 n := by linarith
  have hlt : Work.ELNest.armB1 n - Work.ELNest.armA2 n < 1 := by linarith [hB1.2, hA2.1]
  rw [Dps, Work.EL.midNear.eq_1, N.Zab n, N.Zba n,
    Int.fract_eq_self.mpr ⟨le_of_lt hdiff, hlt⟩]
  constructor <;> linarith [hA2.1, hB1.1, hA2.2, hB1.2]

/-! ## The closedness hypothesis: the image of the boundary misses the region -/

/-- **`F6` maps the boundary of the level-`(n+1)` region off the level-`n` region.** -/
lemma F6_notMem_Dregion_of_mem_polyCurve (I : DPullInputs c d L N)
    (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible (Dps N n)) (n : ℕ) {x : ℂ}
    (hx : x ∈ Work.EL.polyCurve (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1))) :
    Work.ELNest.F6 c x ∉ Work.EL.polyRegion (Dps N n) (Work.ELNest.Dlev L n) := by
  have hR : 1 < Work.ELNest.Dlev L n := one_lt_Dlev I.hL n
  have hR' : 1 < Work.ELNest.Dlev L (n + 1) := one_lt_Dlev I.hL (n + 1)
  have hV := Work.EL.polyRegion_subset_compl (hN := d.hN) (Dps N n) (Work.ELNest.Dlev L n)
  rw [Work.EL.polyCurve] at hx
  simp only [Set.mem_ofPred_eq] at hx
  rcases hx with ⟨P', hP', hy | hra | hrb⟩ | ⟨θ, hθ, -, hθx⟩
  · -- `x` is a landing point
    subst hy
    obtain ⟨Q, hQ, hQa, -⟩ := T6_angle_of_mem (N := N) hP'
    obtain ⟨k, hk⟩ := hQa
    have hland : Work.EL.LandsN d.hN ((Work.EL.T)^[6] P'.a) (Work.ELNest.F6 c P'.y) := by
      rw [F6_apply]
      exact landsN_iterate_map d 6 P'.lands_a
    have h2 : Work.EL.LandsN d.hN Q.a (Work.ELNest.F6 c P'.y) :=
      (pullD_landsN_add_int d Q.a k _).mp (hk ▸ hland)
    have h3 : Work.ELNest.F6 c P'.y = Q.y := tendsto_nhds_unique h2 Q.lands_a
    intro hmem
    exact hV hmem (by rw [Work.EL.polyCurve]; exact Or.inl ⟨Q, hQ, Or.inl h3⟩)
  · -- `x` lies on the ray piece of `P'.a`
    obtain ⟨Q, hQ, hQa, -⟩ := T6_angle_of_mem (N := N) hP'
    obtain ⟨k, hk⟩ := hQa
    rw [Work.ELTop.rayPiece_eq_image d.hN hR'] at hra
    obtain ⟨t, ht, rfl⟩ := hra
    intro hmem
    have hpiece : Work.ELNest.F6 c (Work.EL.rayPt d.hN P'.a t)
        ∈ Work.EL.rayPiece d.hN Q.a 0 (Work.ELNest.Dlev L n) := by
      rw [Work.ELTop.rayPiece_eq_image d.hN hR]
      refine ⟨t ^ (64 : ℕ), ⟨one_lt_pow₀ ht.1 (by norm_num), ?_⟩, ?_⟩
      · rw [← Dlev_pow I.hL n]
        exact pow_le_pow_left₀ (le_of_lt (lt_trans zero_lt_one ht.1)) ht.2 64
      · simp only [F6_rayPt d ht.1, hk, Work.ELTop.rayPt_add_int]
    exact hV hmem (by rw [Work.EL.polyCurve]; exact Or.inl ⟨Q, hQ, Or.inr (Or.inl hpiece)⟩)
  · -- `x` lies on the ray piece of `P'.b`
    obtain ⟨Q, hQ, -, hQb⟩ := T6_angle_of_mem (N := N) hP'
    obtain ⟨k, hk⟩ := hQb
    rw [Work.ELTop.rayPiece_eq_image d.hN hR'] at hrb
    obtain ⟨t, ht, rfl⟩ := hrb
    intro hmem
    have hpiece : Work.ELNest.F6 c (Work.EL.rayPt d.hN P'.b t)
        ∈ Work.EL.rayPiece d.hN Q.b 0 (Work.ELNest.Dlev L n) := by
      rw [Work.ELTop.rayPiece_eq_image d.hN hR]
      refine ⟨t ^ (64 : ℕ), ⟨one_lt_pow₀ ht.1 (by norm_num), ?_⟩, ?_⟩
      · rw [← Dlev_pow I.hL n]
        exact pow_le_pow_left₀ (le_of_lt (lt_trans zero_lt_one ht.1)) ht.2 64
      · simp only [F6_rayPt d ht.1, hk, Work.ELTop.rayPt_add_int]
    exact hV hmem (by rw [Work.EL.polyCurve]; exact Or.inl ⟨Q, hQ, Or.inr (Or.inr hpiece)⟩)
  · -- `x` lies on the equipotential of level `Dlev L (n+1)`
    intro hmem
    have hpot : Work.EL.pot d.hN (Work.ELNest.F6 c x)
        = Real.log (Work.ELNest.Dlev L n) := by
      rw [hθx, pot_F6, Work.EL.pot_rayPt d.hN hR', log_Dlev_succ I.hL n]
    have hlt : Work.EL.pot d.hN (Work.ELNest.F6 c x)
        < Real.log (Work.ELNest.Dlev L n) :=
      Work.ELTop.polyRegion_subset_pot_lt d.hN Work.TopJordan.jordanForm (Dps N n)
        (hadm n) hR (Work.ELTop.polyCurve_isJordan d.hN _ (hadm n) hR) hmem
    rw [hpot] at hlt
    exact lt_irrefl _ hlt

/-! ## The `K c` part of the image condition -/

/-- The quartic `Tsq c` is an open map. -/
lemma isOpenMap_Tsq (c : ℂ) : IsOpenMap (Work.Landing.Tsq c) := by
  have hsq : IsOpenMap (fun z : ℂ => z ^ 2) := (Complex.isOpenQuotientMap_pow 2).isOpenMap
  rw [show Work.Landing.Tsq c = (fun z : ℂ => z + c) ∘ (fun z : ℂ => z ^ 2) ∘
      (fun z : ℂ => z + star c) ∘ (fun z : ℂ => z ^ 2) from
    funext (fun z => by rw [Work.Landing.Tsq_apply]; simp [Function.comp])]
  exact (isOpenMap_add_right c).comp (hsq.comp ((isOpenMap_add_right (star c)).comp hsq))

/-- `F6 c` is an open map (a composition of translates and squarings). -/
lemma isOpenMap_F6 (c : ℂ) : IsOpenMap (Work.ELNest.F6 c) := by
  have hiter : ∀ m : ℕ, IsOpenMap ((Work.Landing.Tsq c)^[m]) := by
    intro m
    induction m with
    | zero => simpa using (IsOpenMap.id : IsOpenMap (id : ℂ → ℂ))
    | succ m ih => rw [Function.iterate_succ']; exact (isOpenMap_Tsq c).comp ih
  simpa [Work.ELNest.F6] using hiter 3

/-- **Local surjectivity of `F6 c`**: around any point, `F6 c` maps a ball onto a neighbourhood
of the image point (the open mapping theorem for a non-constant polynomial). -/
lemma exists_preimage_near_F6 (c : ℂ) (x : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : ℂ, ‖y - Work.ELNest.F6 c x‖ < δ →
      ∃ z : ℂ, ‖z - x‖ < ε ∧ Work.ELNest.F6 c z = y := by
  have himg : Work.ELNest.F6 c '' Metric.ball x ε ∈ 𝓝 (Work.ELNest.F6 c x) :=
    (isOpenMap_F6 c).image_mem_nhds (Metric.ball_mem_nhds x hε)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp himg
  refine ⟨δ, hδ, fun y hy => ?_⟩
  obtain ⟨z, hz, hzy⟩ := hsub (show y ∈ Metric.ball (Work.ELNest.F6 c x) δ from by
    rw [Metric.mem_ball, dist_eq_norm]; exact hy)
  exact ⟨z, by rwa [Metric.mem_ball, dist_eq_norm] at hz, hzy⟩

/-- The parameter ray of angle `θ` depends on `θ` only modulo `1`. -/
lemma paramRay_fract' (d : Work.EL.RootParabolic c) (θ : ℝ) :
    Work.EL.paramRay d.hN (Int.fract θ) = Work.EL.paramRay d.hN θ := by
  rw [show Int.fract θ = θ + ((-⌊θ⌋ : ℤ) : ℝ) by
    rw [Int.fract]; push_cast; ring]
  exact Work.ELTop.paramRay_add_int_aux d.hN θ (-⌊θ⌋)

/-- **No point of the level-`(n+1)` region maps onto a boundary ray of the level-`n` polygon.**
If `z ∈ U` and `F6 c z` lies on the ray of angle `P.a` for a pair `P` of the level-`n` polygon,
then the external angle `α` of `z` avoids the closed far arcs of the level-`(n+1)` polygon
(region description), while `T^[6] α ≡ P.a` (since `F6` multiplies external angles by
`64 = 2^6` on the escaping set); the contrapositive of the near-arc condition `I.arc` gives
`α ∈ [P'.a, P'.b]` for some pair `P'` of the level-`(n+1)` polygon, a contradiction. -/
lemma pullD_notMem_paramRay (I : DPullInputs c d L N)
    (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible (Dps N n)) (n : ℕ)
    {P : Work.EL.CoPair d.hN} (hP : P ∈ Dps N n) {z : ℂ}
    (hz : z ∈ Work.EL.polyRegion (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1))) :
    Work.ELNest.F6 c z ∉ Work.EL.paramRay d.hN P.a := by
  intro hmem
  have hR' : 1 < Work.ELNest.Dlev L (n + 1) := one_lt_Dlev I.hL (n + 1)
  have hC' := Work.ELTop.polyCurve_isJordan d.hN (Dps N (n + 1)) (hadm (n + 1)) hR'
  have hzK : z ∉ Work.EL.K c := by
    intro hK
    have hFzK : Work.ELNest.F6 c z ∈ Work.EL.K c := F6_mem_K hK
    exact (Work.EL.paramRay_subset_compl d.hN P.a) hmem hFzK
  set α : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) z with hα
  have harcs : ∀ Q ∈ Dps N (n + 1), ¬ Work.EL.InClosedArc α Q.a Q.b :=
    ((Work.ELTop.mem_polyRegion_iff_of_notMem_K d.hN Work.TopJordan.jordanForm
      (Dps N (n + 1)) (hadm (n + 1)) hR' hC' hzK).mp hz).1
  have hzeq : Work.EL.rayPt d.hN α (Real.exp (Work.EL.pot d.hN z)) = z := by
    rw [hα]; exact Work.ELTop.rayPt_extAngle_exp_pot d.hN hzK
  have ht : 1 < Real.exp (Work.EL.pot d.hN z) := Work.ELTop.one_lt_exp_pot d.hN hzK
  have hFz : Work.ELNest.F6 c z
      = Work.EL.rayPt d.hN ((Work.EL.T)^[6] α)
          ((Real.exp (Work.EL.pot d.hN z)) ^ (64 : ℕ)) := by
    conv_lhs => rw [← hzeq]
    exact F6_rayPt d ht
  set s : ℝ := (Real.exp (Work.EL.pot d.hN z)) ^ (64 : ℕ) with hs
  have hs1 : 1 < s := by rw [hs]; exact one_lt_pow₀ ht (by norm_num)
  have hFs : Work.EL.rayPt d.hN ((Work.EL.T)^[6] α) s
      = Work.EL.rayPt d.hN (Int.fract ((Work.EL.T)^[6] α)) s := by
    have h := Work.ELTop.rayPt_add_int d.hN (Int.fract ((Work.EL.T)^[6] α)) s
      ⌊(Work.EL.T)^[6] α⌋
    rwa [Int.fract_add_floor] at h
  have hangle1 : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (Work.ELNest.F6 c z)
      = Int.fract ((Work.EL.T)^[6] α) := by
    rw [hFz, hFs]
    exact Work.Top.extAngle_rayPt d.hN (Int.fract_nonneg _) (Int.fract_lt_one _) hs1
  have hangle2 : Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) (Work.ELNest.F6 c z)
      = Int.fract P.a := by
    have hp : Work.ELNest.F6 c z ∈ Work.EL.paramRay d.hN (Int.fract P.a) := by
      rw [paramRay_fract' d P.a]; exact hmem
    exact Work.Top.extAngle_of_mem_paramRay d.hN (Int.fract_nonneg P.a) (Int.fract_lt_one P.a) hp
  have hcong : ∃ k : ℤ, (Work.EL.T)^[6] α = P.a + k := by
    obtain ⟨k, hk⟩ := Int.fract_eq_fract.mp (hangle1.symm.trans hangle2)
    exact ⟨k, by linarith⟩
  have hInC : Work.EL.InClosedArc ((Work.EL.T)^[6] α) P.a P.b := by
    obtain ⟨k, hk⟩ := hcong
    have hf0 : Int.fract ((Work.EL.T)^[6] α - P.a) = 0 := by
      rw [hk, show P.a + (k : ℝ) - P.a = (k : ℝ) by ring, Int.fract_intCast]
    exact ⟨le_of_eq hf0.symm, by rw [hf0]; exact Work.EL.arcLen_nonneg P.a P.b⟩
  exact (I.arc n α (by intro Q hQ; exact harcs Q hQ) P hP) hInC

/-- **The image condition.**  `f_c^6` maps the level-`(n+1)` region into the level-`n` region.

The non-`K c` part is the angle/potential description of the region.  For the part in `K c`, the
image can only meet the polygon curve in the three cut points; but `F6 c` is an open map, so a
point `z` of the region whose image is a cut point `P.y` has, close to it and still inside the
region, a preimage of any ray point of the ray `R(P.a)` of sufficiently small level — and no
point of the region is mapped onto such a ray (`pullD_notMem_paramRay`).  The image of the
(preconnected) region is therefore contained in the complement of the polygon curve, and since
it contains the image of the reference seed, it lies in the region. -/
lemma F6_mapsTo_Dregion (I : DPullInputs c d L N)
    (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible (Dps N n)) (n : ℕ) :
    Set.MapsTo (Work.ELNest.F6 c)
      (Work.EL.polyRegion (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1)))
      (Work.EL.polyRegion (Dps N n) (Work.ELNest.Dlev L n)) := by
  have hR : 1 < Work.ELNest.Dlev L n := one_lt_Dlev I.hL n
  have hR' : 1 < Work.ELNest.Dlev L (n + 1) := one_lt_Dlev I.hL (n + 1)
  have hUo : IsOpen (Work.EL.polyRegion (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1))) :=
    Work.ELTop.isOpen_polyRegion d.hN _ _ (Work.ELTop.isClosed_polyCurve d.hN _ _)
  have hUc := Work.EL.isPreconnected_polyRegion (hN := d.hN)
    (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1))
  -- the `K c` part: no point of `U ∩ K c` maps onto the polygon curve
  have hKpart : ∀ z ∈ Work.EL.polyRegion (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1)),
      z ∈ Work.EL.K c →
      Work.ELNest.F6 c z ∉ Work.EL.polyCurve (Dps N n) (Work.ELNest.Dlev L n) := by
    intro z hz hzK hFzC
    have hFzK : Work.ELNest.F6 c z ∈ Work.EL.K c := F6_mem_K hzK
    have hm : Work.ELNest.F6 c z ∈ Work.EL.polyCurve (Dps N n) (Work.ELNest.Dlev L n)
        ∩ Work.EL.K c := ⟨hFzC, hFzK⟩
    rw [Work.ELTop.polyCurve_inter_K d.hN (Dps N n) hR] at hm
    obtain ⟨P, hP, hPy⟩ := hm
    obtain ⟨ε, hε0, hεU⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hz)
    obtain ⟨δ, hδ0, hδ⟩ := exists_preimage_near_F6 (c := c) z hε0
    have hlands : Filter.Tendsto (fun t : ℝ => Work.EL.rayPt d.hN P.a t)
        (nhdsWithin (1 : ℝ) (Set.Ioi 1)) (𝓝 (Work.ELNest.F6 c z)) := hPy ▸ P.lands_a
    have hev : ∀ᶠ t : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1),
        Work.EL.rayPt d.hN P.a t ∈ Metric.ball (Work.ELNest.F6 c z) δ :=
      hlands (Metric.ball_mem_nhds (Work.ELNest.F6 c z) hδ0)
    have hIoi : ∀ᶠ t : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1), t ∈ Set.Ioi (1 : ℝ) :=
      self_mem_nhdsWithin
    obtain ⟨t, htball, htIoi⟩ := (hev.and hIoi).exists
    have ht1 : 1 < t := htIoi
    obtain ⟨w, hwε, hwF⟩ := hδ _ (by rwa [Metric.mem_ball, dist_eq_norm] at htball)
    have hwU : w ∈ Work.EL.polyRegion (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1)) :=
      hεU (by rw [Metric.mem_ball, dist_eq_norm]; exact hwε)
    have hwray : Work.ELNest.F6 c w ∈ Work.EL.paramRay d.hN P.a := by
      rw [hwF]; exact Work.EL.rayPt_mem_paramRay d.hN ht1
    exact pullD_notMem_paramRay I hadm n hP hwU hwray
  -- the image avoids the polygon curve
  have hcompl : Work.ELNest.F6 c ''
      Work.EL.polyRegion (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1))
      ⊆ (Work.EL.polyCurve (Dps N n) (Work.ELNest.Dlev L n))ᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Set.mem_compl_iff]
    by_cases hzK : z ∈ Work.EL.K c
    · exact hKpart z hz hzK
    · exact Work.EL.polyRegion_subset_compl (hN := d.hN) (Dps N n) (Work.ELNest.Dlev L n)
        (F6_mem_Dregion_of_notMem_K I hadm n hz hzK)
  set seed : ℂ := Work.EL.rayPt d.hN (Work.EL.midNear (Dps N (n + 1)))
    (Real.sqrt (Work.ELNest.Dlev L (n + 1))) with hseed
  have hseedU : seed ∈ Work.EL.polyRegion (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1)) :=
    Work.ELTop.seed_mem_polyRegion d.hN _ (hadm (n + 1)) hR'
  have hseedK : seed ∉ Work.EL.K c := Work.EL.rayPt_notMem_K d.hN (Work.ELTop.one_lt_sqrt hR')
  have hseedV : Work.ELNest.F6 c seed ∈ Work.EL.polyRegion (Dps N n) (Work.ELNest.Dlev L n) :=
    F6_mem_Dregion_of_notMem_K I hadm n hseedU hseedK
  have hpre : IsPreconnected (Work.ELNest.F6 c ''
      Work.EL.polyRegion (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1))) :=
    hUc.image _ (Work.ELNest.continuous_F6 c).continuousOn
  have hsub : Work.ELNest.F6 c ''
      Work.EL.polyRegion (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1))
      ⊆ Work.EL.polyRegion (Dps N n) (Work.ELNest.Dlev L n) := by
    have h := hpre.subset_connectedComponentIn ⟨seed, hseedU, rfl⟩ hcompl
    have hVeq : Work.EL.polyRegion (Dps N n) (Work.ELNest.Dlev L n)
        = connectedComponentIn (Work.EL.polyCurve (Dps N n) (Work.ELNest.Dlev L n))ᶜ
          (Work.ELNest.F6 c seed) := by
      rw [Work.EL.polyRegion]
      exact connectedComponentIn_eq hseedV
    rw [hVeq]
    exact h
  intro z hz
  exact hsub ⟨z, hz, rfl⟩

/-! ## The fibre condition at the reference point -/

/-- **At most one preimage in `U` of the reference ray point.**  If two points of the
level-`(n+1)` region are mapped by `f_c^6` to the reference seed of the level-`n` region, they
coincide: both are ray points, their angles avoid the closed far arcs of the level-`(n+1)`
polygon and both are carried by `T^[6]` to `midNear` of the level-`n` polygon, so `I.one`
applies. -/
lemma F6_fibre_subsingleton (I : DPullInputs c d L N)
    (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible (Dps N n)) (n : ℕ) :
    (Work.EL.polyRegion (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1)) ∩
      Work.ELNest.F6 c ⁻¹'
        {Work.EL.rayPt d.hN (Work.EL.midNear (Dps N n)) (Real.sqrt (Work.ELNest.Dlev L n))}
      ).Subsingleton := by
  have hR : 1 < Work.ELNest.Dlev L n := one_lt_Dlev I.hL n
  have hR' : 1 < Work.ELNest.Dlev L (n + 1) := one_lt_Dlev I.hL (n + 1)
  have hC' : Work.Top.IsJordanCurve
      (Work.EL.polyCurve (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1))) :=
    Work.ELTop.polyCurve_isJordan d.hN _ (hadm (n + 1)) hR'
  intro x hx y hy
  obtain ⟨hxU, hxF⟩ := hx
  obtain ⟨hyU, hyF⟩ := hy
  have hxF' : Work.ELNest.F6 c x
      = Work.EL.rayPt d.hN (Work.EL.midNear (Dps N n)) (Real.sqrt (Work.ELNest.Dlev L n)) := hxF
  have hyF' : Work.ELNest.F6 c y
      = Work.EL.rayPt d.hN (Work.EL.midNear (Dps N n)) (Real.sqrt (Work.ELNest.Dlev L n)) := hyF
  have hvK : Work.EL.rayPt d.hN (Work.EL.midNear (Dps N n)) (Real.sqrt (Work.ELNest.Dlev L n))
      ∉ Work.EL.K c := Work.EL.rayPt_notMem_K d.hN (Work.ELTop.one_lt_sqrt hR)
  have hxK : x ∉ Work.EL.K c := fun h => hvK (hxF' ▸ F6_mem_K h)
  have hyK : y ∉ Work.EL.K c := fun h => hvK (hyF' ▸ F6_mem_K h)
  obtain ⟨harcx, -⟩ := (Work.ELTop.mem_polyRegion_iff_of_notMem_K d.hN
    Work.TopJordan.jordanForm (Dps N (n + 1)) (hadm (n + 1)) hR' hC' hxK).mp hxU
  obtain ⟨harcy, -⟩ := (Work.ELTop.mem_polyRegion_iff_of_notMem_K d.hN
    Work.TopJordan.jordanForm (Dps N (n + 1)) (hadm (n + 1)) hR' hC' hyK).mp hyU
  -- the angle and the level of a preimage of the seed
  have key : ∀ {w : ℂ}, w ∉ Work.EL.K c →
      Work.ELNest.F6 c w
        = Work.EL.rayPt d.hN (Work.EL.midNear (Dps N n)) (Real.sqrt (Work.ELNest.Dlev L n)) →
      (Work.EL.T)^[6] (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) w)
          = Work.EL.midNear (Dps N n) ∧
        (Real.exp (Work.EL.pot d.hN w)) ^ (64 : ℕ) = Real.sqrt (Work.ELNest.Dlev L n) := by
    intro w hwK hwF
    have ht : 1 < Real.exp (Work.EL.pot d.hN w) := Work.ELTop.one_lt_exp_pot d.hN hwK
    have harg : Work.EL.rayPt d.hN (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) w)
        (Real.exp (Work.EL.pot d.hN w)) = w := Work.ELTop.rayPt_extAngle_exp_pot d.hN hwK
    have h2 : Work.ELNest.F6 c (Work.EL.rayPt d.hN
          (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) w)
          (Real.exp (Work.EL.pot d.hN w)))
        = Work.EL.rayPt d.hN (Work.EL.midNear (Dps N n)) (Real.sqrt (Work.ELNest.Dlev L n)) := by
      rw [harg]; exact hwF
    have h1 : Work.EL.rayPt d.hN ((Work.EL.T)^[6]
          (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) w))
        ((Real.exp (Work.EL.pot d.hN w)) ^ (64 : ℕ))
        = Work.EL.rayPt d.hN (Work.EL.midNear (Dps N n)) (Real.sqrt (Work.ELNest.Dlev L n)) := by
      rw [← F6_rayPt d ht]
      exact h2
    exact Work.Top.rayPt_injOn d.hN (T6_mem_Ico _).1 (T6_mem_Ico _).2
      (midNear_Dps_mem_Ico (N := N) n).1 (midNear_Dps_mem_Ico (N := N) n).2
      (one_lt_pow₀ ht (by norm_num)) (Work.ELTop.one_lt_sqrt hR) h1
  obtain ⟨hθx, -⟩ := key hxK hxF'
  obtain ⟨hθy, -⟩ := key hyK hyF'
  -- the uniqueness of `I.one`
  obtain ⟨k, hk⟩ := I.one n (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) x)
    (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) y)
    (by intro P hP; exact harcx P hP) (by intro P hP; exact harcy P hP)
    ⟨0, by simpa using hθx⟩ ⟨0, by simpa using hθy⟩
  -- the potentials agree, and both points are their own ray points
  have hpot : Work.EL.pot d.hN x = Work.EL.pot d.hN y := by
    have h1 : Work.EL.pot d.hN (Work.ELNest.F6 c x)
        = Work.EL.pot d.hN (Work.ELNest.F6 c y) := by rw [hxF', hyF']
    rw [pot_F6, pot_F6] at h1
    linarith
  have hptx : x = Work.EL.rayPt d.hN (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) x)
      (Real.exp (Work.EL.pot d.hN x)) :=
    (Work.ELTop.rayPt_extAngle_exp_pot d.hN hxK).symm
  have hpty : y = Work.EL.rayPt d.hN (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) y)
      (Real.exp (Work.EL.pot d.hN y)) :=
    (Work.ELTop.rayPt_extAngle_exp_pot d.hN hyK).symm
  rw [hptx, hpty, hk, hpot]
  exact Work.ELTop.rayPt_add_int d.hN (Work.Top.NakaneData.extAngle (Work.EL.dynPhi c d.φ) y)
    (Real.exp (Work.EL.pot d.hN y)) k

/-! ## The covering property -/

/-- `f_c^6` is a covering map over the level-`n` region. -/
lemma isCoveringMapOn_F6_Dregion (I : DPullInputs c d L N)
    (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible (Dps N n)) (n : ℕ) :
    IsCoveringMapOn (Work.ELNest.F6 c)
      (Work.EL.polyRegion (Dps N n) (Work.ELNest.Dlev L n)) := by
  refine Work.ELPull.isCoveringMapOn_tsqIterate_mono c 3 ?_
  intro v hv
  rw [Set.mem_compl_iff, Set.mem_image]
  rintro ⟨z, hz, hzv⟩
  obtain ⟨k, hk, hkeq⟩ := Work.ELPull.critValues_tsqIterate (c := c) 3 z hz
  have hk6 : k ∈ Set.Icc 1 6 := by
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hk
    exact Set.mem_Icc.mpr ⟨h1, by norm_num at h2 ⊢; linarith⟩
  have hvk : v = (Tantibar c)^[k] 0 := hzv.symm.trans hkeq
  exact I.hcv n k hk6 (hvk ▸ hv)

end

end Work.ELAssembly

namespace Work.ELAssembly

open Classical Filter Set
open scoped Topology

noncomputable section

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The pull-back `pbD` of the `b₂`-nest**: `f_c^6 = (Tantibar c)^[6]` maps the level-`(n+1)`
region `[Za(n+1), Zb(n+1), Zc(n+1)]` bijectively onto the level-`n` region `[Za n, Zb n, Zc n]`.
The proof is `Work.ELAssembly.bijOn_of_isCoveringMapOn_of_fibre` with
`U = polyRegion [Za (n+1), Zb (n+1), Zc (n+1)] (Dlev L (n+1))`,
`V = polyRegion [Za n, Zb n, Zc n] (Dlev L n)`: the covering from
`Work.ELPull.isCoveringMapOn_tsqIterate_mono` (`m = 3`) with
`Work.ELPull.critValues_tsqIterate` and `I.hcv` (`(Tantibar c)^[k] 0 ∉ V` for `k = 1..6`), the
image condition from `mem_polyRegion_iff_of_notMem_K` and `I.arc`, the closedness from
`frontier_polyRegion_eq_polyCurve` and `I.pair`, and the fibre condition at
`v₀ = rayPt (midNear [Za n, Zb n, Zc n]) (Real.sqrt (Dlev L n))` from `I.one`.  `Work.ELNest.F6`
is `(Tantibar c)^[6]` by `Work.ELNest.F6_eq_tantibar`; the admissibility hypotheses come from
`Work.ELAssembly.D_adm_of` and `polyCurve_isJordan`/`isOpen_polyRegion` from ELTop;
`Work.TopJordan.jordanForm` supplies the `JordanForm` argument of the ELTop lemmas. -/
theorem pullD_bij {c : ℂ} {d : Work.EL.RootParabolic c} {L : ℝ} {N : NestPairs d}
    (I : DPullInputs c d L N) (hadm : ∀ n : ℕ, Work.EL.PolyAdmissible [N.Za n, N.Zb n, N.Zc n])
    (n : ℕ) :
    Set.BijOn (Work.ELNest.F6 c)
      (Work.EL.polyRegion [N.Za (n + 1), N.Zb (n + 1), N.Zc (n + 1)] (Work.ELNest.Dlev L (n + 1)))
      (Work.EL.polyRegion [N.Za n, N.Zb n, N.Zc n] (Work.ELNest.Dlev L n)) := by
  have hadm' : ∀ m : ℕ, Work.EL.PolyAdmissible (Dps N m) := fun m => hadm m
  have hR : 1 < Work.ELNest.Dlev L n := one_lt_Dlev I.hL n
  have hR' : 1 < Work.ELNest.Dlev L (n + 1) := one_lt_Dlev I.hL (n + 1)
  have hC : Work.Top.IsJordanCurve (Work.EL.polyCurve (Dps N n) (Work.ELNest.Dlev L n)) :=
    Work.ELTop.polyCurve_isJordan d.hN _ (hadm' n) hR
  have hC' : Work.Top.IsJordanCurve
      (Work.EL.polyCurve (Dps N (n + 1)) (Work.ELNest.Dlev L (n + 1))) :=
    Work.ELTop.polyCurve_isJordan d.hN _ (hadm' (n + 1)) hR'
  refine bijOn_of_isCoveringMapOn_of_fibre (Work.ELNest.continuous_F6 c)
    (isCoveringMapOn_F6_Dregion I hadm' n)
    (Work.ELTop.isOpen_polyRegion d.hN _ _ (Work.ELTop.isClosed_polyCurve d.hN _ _))
    (Work.EL.isPreconnected_polyRegion (hN := d.hN) _ _)
    ⟨_, Work.ELTop.seed_mem_polyRegion d.hN _ (hadm' (n + 1)) hR'⟩
    (Work.ELTop.isOpen_polyRegion d.hN _ _ (Work.ELTop.isClosed_polyCurve d.hN _ _))
    (Work.EL.isPreconnected_polyRegion (hN := d.hN) _ _)
    (F6_mapsTo_Dregion I hadm' n)
    (fun x hx hxv => by
      rw [Work.ELTop.closure_polyRegion_eq d.hN Work.TopJordan.jordanForm _ (hadm' (n + 1)) hR'
        hC'] at hx
      rcases hx with hx | hx
      · exact hx
      · exact absurd hxv (F6_notMem_Dregion_of_mem_polyCurve I hadm' n hx))
    (Work.ELTop.seed_mem_polyRegion d.hN _ (hadm' n) hR)
    (F6_fibre_subsingleton I hadm' n)

end

end Work.ELAssembly
