/-
# `polyPullback`: the region pull-back bijection of the EL area

The `m`-th iterate of `Tsq c = (Tantibar c)^[2]` maps the ray region of `ps'` at level
`R ^ (1/4^m)` bijectively onto the ray region of `ps` at level `R`.

The proof goes through the covering map `(Tsq c)^[m]` on the `ps`-region (valid because the
critical orbit avoids it, `hcv`), the boundary correspondence supplied by the rational
combinatorics (`hcomb`, `hy`) and the simply-connectedness of the target (`hsc`).
-/
import Mathlib
import Submission.Work.ELPull.Defs
import Submission.Work.ELPull.isCoveringMapOn_tsqIterate
import Submission.Work.ELPull.critValues_tsqIterate
import Submission.Work.ELTop.landsN_map
import Submission.Work.ELTop.rayPiece_eq_image
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ParamRays.DynBottcher

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section
set_option linter.unusedVariables false
open Classical Set Function Filter
open scoped Topology

namespace Work.ELPull

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## 1. The Böttcher input carried by `DynB c`

`Work.ELPull.DynB c` is the Nakane data for the *canonical* Böttcher function
`Work.ParamRays.dynPhi c`.  Since that function is junk (`0` everywhere) unless a Böttcher
coordinate exists, the existence of `DynB c` forces `Work.ParamRays.DynBottcherExists c`. -/

theorem pp_dynBottcherExists_of_dynB {c : ℂ} (hN : DynB c) :
    Work.ParamRays.DynBottcherExists c := by
  by_contra hne
  have hphi0 : Work.ParamRays.dynPhi c = fun _ => (0 : ℂ) := by
    funext z
    rw [Work.ParamRays.dynPhi, Work.ParamRays.dynPhiOf, dif_neg hne]
    split <;> rfl
  rcases Set.eq_empty_or_nonempty ((K c)ᶜ) with hem | ⟨z, hz⟩
  · have h2e : (1 : ℝ) < ‖(2 : ℂ)‖ := by norm_num
    have hnot : ∀ w : ℂ, w ∉ (K c)ᶜ := Set.eq_empty_iff_forall_notMem.mp hem
    exact hnot _ (hN.e.symm ⟨(2 : ℂ), h2e⟩).2
  · have h1 : Work.ParamRays.dynPhi c z =
        ((hN.e ⟨z, hz⟩ : Work.Top.exteriorDisc) : ℂ) := hN.he ⟨z, hz⟩
    have h3 : ((hN.e ⟨z, hz⟩ : Work.Top.exteriorDisc) : ℂ) = 0 := by
      rw [← h1]
      exact congrFun hphi0 z
    have h2 : (1 : ℝ) < ‖((hN.e ⟨z, hz⟩ : Work.Top.exteriorDisc) : ℂ)‖ := (hN.e ⟨z, hz⟩).2
    rw [h3, norm_zero] at h2
    linarith

/-- The Böttcher coordinate is available: every `DynB c` supplies it. -/
theorem isDynBottcher_dynPhiOf_of_dynB {c : ℂ} (hN : DynB c) :
    Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
  Work.ParamRays.isDynBottcher_dynPhiOf (pp_dynBottcherExists_of_dynB hN)

/-! ## 2. Angles: the action of `Tsq c` is `θ ↦ 4 θ mod 1` -/

/-- `Int.fract` is multiplicative in an integer factor applied to a fractional part. -/
theorem fract_mul_intCast_fract (z : ℤ) (x : ℝ) :
    Int.fract ((z : ℝ) * Int.fract x) = Int.fract ((z : ℝ) * x) := by
  have h : (z : ℝ) * Int.fract x = (z : ℝ) * x - ((z * ⌊x⌋ : ℤ) : ℝ) := by
    rw [← Int.self_sub_floor x]
    push_cast
    ring
  rw [h, Int.fract_sub_intCast]

theorem fract_four_mul_fract (x : ℝ) :
    Int.fract (4 * Int.fract x) = Int.fract (4 * x) := by
  simpa using fract_mul_intCast_fract (4 : ℤ) x

/-- `Tsq c` acts on angles by `θ ↦ 4 θ mod 1`: `T (T θ) = fract (4 θ)`. -/
theorem T_two_fract (x : ℝ) : T (T x) = Int.fract (4 * x) := by
  rw [T_def, T_def]
  have h : (-2 : ℝ) * Int.fract (-2 * x)
      = (-2 : ℝ) * (-2 * x) - (((-2 : ℤ) * ⌊-2 * x⌋ : ℤ) : ℝ) := by
    rw [← Int.self_sub_floor (-2 * x)]
    push_cast
    ring
  rw [h, Int.fract_sub_intCast]
  congr 1
  ring

theorem angMul_zero (θ : ℝ) : angMul 0 θ = Int.fract θ := by
  rw [angMul]
  norm_num

theorem angMul_one (θ : ℝ) : angMul 1 θ = Int.fract (4 * θ) := by
  rw [angMul]
  norm_num

/-- The angle map of `Tsq c` multiplies the angle-map iterate: `angMul 1 (angMul m θ) = angMul (m+1) θ`. -/
theorem angMul_one_angMul (m : ℕ) (θ : ℝ) : angMul 1 (angMul m θ) = angMul (m + 1) θ := by
  rw [angMul_one, angMul, angMul]
  rw [fract_four_mul_fract ((4 : ℝ) ^ m * θ)]
  congr 1
  rw [pow_succ]
  ring

/-! ## 3. Ray points move with `Tsq c` -/

/-- `rayPt` is one-periodic in the angle. -/
theorem rayPt_add_one_int {c : ℂ} (hN : DynB c) (θ t : ℝ) (k : ℤ) :
    hN.rayPt (θ + k) t = hN.rayPt θ t :=
  Work.ELTop.rayPt_add_int hN θ t k

theorem rayPt_fract {c : ℂ} (hN : DynB c) (θ t : ℝ) :
    hN.rayPt (Int.fract θ) t = hN.rayPt θ t := by
  conv_rhs => rw [← Int.fract_add_floor θ]
  exact (rayPt_add_one_int hN (Int.fract θ) t ⌊θ⌋).symm

/-- `Tantibar c` moves the ray points: the angle doubles (negatively) and the level squares. -/
theorem pp_rayPt_Tantibar {c : ℂ} (hN : DynB c)
    (hB : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c)) {θ s : ℝ} (hs : 1 < s) :
    Tantibar c (hN.rayPt θ s) = hN.rayPt (T θ) (s ^ 2) :=
  (Work.ELTop.rayPt_T hN hB hs).symm

/-- **The ray point moves with `Tsq c`**: `Tsq c` sends the ray point of angle `ψ` at level `t`
to the ray point of angle `4 ψ mod 1` at level `t ^ 4`. -/
theorem Tsq_rayPt {c : ℂ} (hN : DynB c)
    (hB : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c)) {ψ t : ℝ} (ht : 1 < t) :
    Work.Landing.Tsq c (hN.rayPt ψ t) = hN.rayPt (angMul 1 ψ) (t ^ 4) := by
  rw [Tsq_eq_iterate, show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_succ_apply',
    Function.iterate_one]
  rw [pp_rayPt_Tantibar hN hB ht]
  have ht2 : (1 : ℝ) < t ^ 2 := by nlinarith
  rw [pp_rayPt_Tantibar hN hB ht2]
  rw [T_two_fract, angMul_one]
  congr 1
  ring

/-- The ray point of angle `θ` at level `s` moves with the `m`-th iterate of `Tsq c`: the angle
becomes `angMul m θ` and the level `s ^ 4^m`. -/
theorem rayPt_Tsq_iterate {c : ℂ} (hN : DynB c)
    (hB : Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c)) (m : ℕ) {θ s : ℝ}
    (hs : 1 < s) :
    (Work.Landing.Tsq c)^[m] (hN.rayPt θ s) = hN.rayPt (angMul m θ) (s ^ (4 ^ m)) := by
  induction m with
  | zero =>
    rw [Function.iterate_zero_apply, angMul_zero]
    norm_num
    exact (rayPt_fract hN θ s).symm
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    have hs' : (1 : ℝ) < s ^ 4 ^ m := one_lt_pow₀ hs (pow_ne_zero m (by norm_num))
    rw [Tsq_rayPt hN hB (ψ := angMul m θ) (t := s ^ 4 ^ m) hs', angMul_one_angMul]
    congr 1
    rw [← pow_mul, pow_succ]

/-! ## 4. The boundary correspondence `f '' polyCurve ps' R' ⊆ polyCurve ps R` -/

/-- `(Tsq c)^[m]` is the `2 m`-th iterate of `Tantibar c`. -/
theorem Tsq_iterate_eq_Tantibar (c : ℂ) (m : ℕ) :
    (Work.Landing.Tsq c)^[m] = (Tantibar c)^[2 * m] := by
  have h : Work.Landing.Tsq c = (Tantibar c)^[2] := funext (Tsq_eq_iterate c)
  rw [h, ← Function.iterate_mul]

/-- `(R ^ (1/4^m)) ^ (4^m) = R` for `R > 0`. -/
theorem rpow_div_pow_mul {R : ℝ} (hR : 0 < R) (m : ℕ) :
    (R ^ ((1 : ℝ) / 4 ^ m)) ^ (4 ^ m : ℕ) = R := by
  rw [← Real.rpow_natCast (R ^ ((1 : ℝ) / 4 ^ m)) (4 ^ m),
    ← Real.rpow_mul (le_of_lt hR)]
  have hne : ((4 : ℝ) ^ m) ≠ 0 := by positivity
  rw [show (1 : ℝ) / 4 ^ m * ((4 ^ m : ℕ) : ℝ) = 1 from by
    rw [Nat.cast_pow, Nat.cast_ofNat, div_mul_cancel₀ _ hne]]
  exact Real.rpow_one R

/-- The `4^m`-th power map carries the levels `Ioc 1 (R ^ (1/4^m))` onto `Ioc 1 R`. -/
theorem image_pow_Ioc {R : ℝ} (hR : 1 < R) (m : ℕ) :
    (fun t : ℝ => t ^ (4 ^ m : ℕ)) '' Set.Ioc 1 (R ^ ((1 : ℝ) / 4 ^ m)) = Set.Ioc 1 R := by
  ext y
  constructor
  · rintro ⟨t, ⟨ht1, htR⟩, rfl⟩
    refine ⟨one_lt_pow₀ ht1 (pow_ne_zero m (by norm_num)), ?_⟩
    calc t ^ (4 ^ m : ℕ) ≤ (R ^ ((1 : ℝ) / 4 ^ m)) ^ (4 ^ m : ℕ) :=
          pow_le_pow_left₀ (le_of_lt (lt_trans zero_lt_one ht1)) htR _
      _ = R := rpow_div_pow_mul (lt_trans zero_lt_one hR) m
  · rintro ⟨hy1, hyR⟩
    refine ⟨y ^ ((1 : ℝ) / 4 ^ m), ⟨?_, ?_⟩, ?_⟩
    · exact Real.one_lt_rpow hy1 (by positivity)
    · exact Real.rpow_le_rpow (le_of_lt (lt_trans zero_lt_one hy1)) hyR (by positivity)
    · show (y ^ ((1 : ℝ) / 4 ^ m)) ^ (4 ^ m : ℕ) = y
      rw [← Real.rpow_natCast (y ^ ((1 : ℝ) / 4 ^ m)) (4 ^ m),
        ← Real.rpow_mul (le_of_lt (lt_trans zero_lt_one hy1))]
      have hne : ((4 : ℝ) ^ m) ≠ 0 := by positivity
      rw [show (1 : ℝ) / 4 ^ m * ((4 ^ m : ℕ) : ℝ) = 1 from by
        rw [Nat.cast_pow, Nat.cast_ofNat, div_mul_cancel₀ _ hne]]
      exact Real.rpow_one y

/-- The ray piece is the image of the interval `(1, R]` under the ray point. -/
theorem rayPiece_eq_image {c : ℂ} (hN : DynB c) {β R : ℝ} (hR : 1 < R) :
    hN.rayPiece β 0 R = (fun t : ℝ => hN.rayPt β t) '' Set.Ioc 1 R :=
  Work.ELTop.rayPiece_eq_image hN hR

/-- **Ray pieces are preserved (up to the angle map) by `(Tsq c)^[m]`.** -/
theorem image_rayPiece {c : ℂ} (hN : DynB c) (m : ℕ) {β R : ℝ} (hR : 1 < R) :
    (Work.Landing.Tsq c)^[m] '' hN.rayPiece β 0 (R ^ ((1 : ℝ) / 4 ^ m))
      = hN.rayPiece (angMul m β) 0 R := by
  have hB := isDynBottcher_dynPhiOf_of_dynB hN
  have hR' : (1 : ℝ) < R ^ ((1 : ℝ) / 4 ^ m) := Real.one_lt_rpow hR (by positivity)
  rw [rayPiece_eq_image hN hR', rayPiece_eq_image hN hR, ← Set.image_comp]
  rw [show ((Work.Landing.Tsq c)^[m] ∘ fun t : ℝ => hN.rayPt β t)
        '' Set.Ioc 1 (R ^ ((1 : ℝ) / 4 ^ m))
      = (fun t : ℝ => hN.rayPt (angMul m β) (t ^ (4 ^ m : ℕ)))
        '' Set.Ioc 1 (R ^ ((1 : ℝ) / 4 ^ m)) from
    Set.image_congr fun t ht => rayPt_Tsq_iterate hN hB m (θ := β) ht.1]
  rw [show (fun t : ℝ => hN.rayPt (angMul m β) (t ^ (4 ^ m : ℕ)))
        = (fun u : ℝ => hN.rayPt (angMul m β) u) ∘ fun t : ℝ => t ^ (4 ^ m : ℕ) from rfl,
    Set.image_comp, image_pow_Ioc hR m]

/-- `ccwLift b a - b = arcLen b a`. -/
theorem ccwLift_sub (b a : ℝ) : ccwLift b a - b = arcLen b a := by
  have h1 : arcLen b a = ⌈b - a⌉ - (b - a) := by
    rw [arcLen]
    have h2 : a - b = (⌈b - a⌉ - (b - a)) - (⌈b - a⌉ : ℤ) := by ring
    rw [h2, Int.fract_sub_intCast, Int.fract_eq_self.mpr]
    refine ⟨by linarith [Int.le_ceil (b - a)], ?_⟩
    have hc := (Int.le_ceil_iff (z := ⌈b - a⌉) (a := b - a)).mp le_rfl
    linarith
  rw [h1, ccwLift]
  ring

/-- A point of the open interval `(a,b)` lies in the arc when `b - a = arcLen a b`. -/
theorem InArc_of_mem_Ioo {θ a b : ℝ} (h : θ ∈ Set.Ioo a b) (hlen : b - a = arcLen a b) :
    InArc θ a b := by
  have h1 : 0 < θ - a := by linarith [h.1]
  have hb1 : b - a < 1 := by rw [hlen]; exact Int.fract_lt_one (b - a)
  have h2 : θ - a < 1 := by linarith [h.2]
  have h3 : Int.fract (θ - a) = θ - a := Int.fract_eq_self.mpr ⟨le_of_lt h1, h2⟩
  rw [InArc, h3, ← hlen]
  exact ⟨h1, by linarith [h.2]⟩

/-- Unwrapping an integer from below the arc. -/
theorem sub_floor_eq (y a : ℝ) : y - (⌊y - a⌋ : ℤ) = a + Int.fract (y - a) := by
  rw [← Int.self_sub_floor (y - a)]
  ring

/-- A point of an arc, unwrapped, differs from an interval point by an integer. -/
theorem InArc.exists_sub_mem_Ioo {y a b : ℝ} (h : InArc y a b) (hlen : b - a = arcLen a b) :
    ∃ k : ℤ, y - k ∈ Set.Ioo a b := by
  refine ⟨⌊y - a⌋, ?_, ?_⟩
  · rw [sub_floor_eq]; linarith [h.1]
  · have h' : Int.fract (y - a) < b - a := hlen.symm ▸ h.2
    rw [sub_floor_eq]; linarith

/-! ### Membership in `polyCurve` -/

theorem mem_polyCurve_vertex {c : ℂ} {hN : DynB c} {ps : List (CoPair hN)} {R : ℝ}
    {P : CoPair hN} (hP : P ∈ ps) : P.y ∈ polyCurve hN ps R := by
  rw [polyCurve, Set.mem_union]
  refine Or.inl ?_
  rw [Set.mem_iUnion]
  refine ⟨P, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hP, ?_⟩
  rw [Set.mem_union, Set.mem_union]
  exact Or.inl (Or.inl (Set.mem_singleton P.y))

theorem mem_polyCurve_rayPiece_a {c : ℂ} {hN : DynB c} {ps : List (CoPair hN)} {R : ℝ}
    {P : CoPair hN} (hP : P ∈ ps) {z : ℂ} (hz : z ∈ hN.rayPiece P.a 0 R) :
    z ∈ polyCurve hN ps R := by
  rw [polyCurve, Set.mem_union]
  refine Or.inl ?_
  rw [Set.mem_iUnion]
  refine ⟨P, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hP, ?_⟩
  rw [Set.mem_union, Set.mem_union]
  exact Or.inl (Or.inr hz)

theorem mem_polyCurve_rayPiece_b {c : ℂ} {hN : DynB c} {ps : List (CoPair hN)} {R : ℝ}
    {P : CoPair hN} (hP : P ∈ ps) {z : ℂ} (hz : z ∈ hN.rayPiece P.b 0 R) :
    z ∈ polyCurve hN ps R := by
  rw [polyCurve, Set.mem_union]
  refine Or.inl ?_
  rw [Set.mem_iUnion]
  refine ⟨P, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hP, ?_⟩
  rw [Set.mem_union, Set.mem_union]
  exact Or.inr hz

theorem mem_polyCurve_eqArc {c : ℂ} {hN : DynB c} {ps : List (CoPair hN)} {R : ℝ}
    {i : Fin ps.length} {z : ℂ}
    (hz : z ∈ hN.eqArc (nearArc ps i).1 (nearArc ps i).2 R) : z ∈ polyCurve hN ps R := by
  rw [polyCurve, Set.mem_union]
  refine Or.inr ?_
  rw [Set.mem_iUnion]
  exact ⟨i, hz⟩

/-- The ray point of a level-`R` ray lies in the corresponding ray piece. -/
theorem rayPt_mem_rayPiece {c : ℂ} (hN : DynB c) {β R : ℝ} (hR : 1 < R) :
    hN.rayPt β R ∈ hN.rayPiece β 0 R := by
  rw [rayPiece_eq_image hN hR]
  exact ⟨R, ⟨hR, le_rfl⟩, rfl⟩

/-! ### The boundary correspondence -/

/-- `arcLen` is insensitive to wrapping the upper endpoint with `ccwLift`. -/
theorem arcLen_ccwLift (b a : ℝ) : arcLen b (ccwLift b a) = arcLen b a := by
  show Int.fract (ccwLift b a - b) = arcLen b a
  rw [ccwLift_sub b a]
  exact Int.fract_fract (a - b)

/-- The unwrapped length of a near arc. -/
theorem nearArc_len {c : ℂ} {hN : DynB c} (ps : List (CoPair hN)) (i : Fin ps.length) :
    (nearArc ps i).2 - (nearArc ps i).1 = arcLen (nearArc ps i).1 (nearArc ps i).2 := by
  show ccwLift (ps.get i).b (ps.get (nextIdx i)).a - (ps.get i).b
    = arcLen (ps.get i).b (ccwLift (ps.get i).b (ps.get (nextIdx i)).a)
  rw [ccwLift_sub, arcLen_ccwLift]

/-- **The boundary of the `ps'`-polygon maps into the boundary of the `ps`-polygon.** -/
theorem image_polyCurve_subset {c : ℂ} (hN : DynB c) (m : ℕ) (ps ps' : List (CoPair hN))
    (R : ℝ) (hR : 1 < R) (hcomb : NearArcsCover hN ps ps' m)
    (hy : ∀ i : Fin ps'.length, ∃ j : Fin ps.length,
      (Tantibar c)^[2 * m] (ps'.get i).y = (ps.get j).y) :
    (Work.Landing.Tsq c)^[m] '' polyCurve hN ps' (R ^ ((1 : ℝ) / 4 ^ m))
      ⊆ polyCurve hN ps R := by
  have hB := isDynBottcher_dynPhiOf_of_dynB hN
  have hR0 : (0 : ℝ) < R := lt_trans zero_lt_one hR
  have hR' : (1 : ℝ) < R ^ ((1 : ℝ) / 4 ^ m) := Real.one_lt_rpow hR (by positivity)
  intro z hz
  obtain ⟨w, hw, rfl⟩ := hz
  simp only [polyCurve, Set.mem_union, Set.mem_iUnion, Set.mem_singleton_iff] at hw
  rcases hw with ⟨P', hP'mem, hw⟩ | ⟨i, hw⟩
  · -- a vertex or a ray piece of the `ps'`-polygon
    rcases hw with (hw | hw) | hw
    · -- the landing point `P'.y` of a `ps'`-pair
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hP'mem
      obtain ⟨j, hj⟩ := hy i
      rw [hw, ← hi, Tsq_iterate_eq_Tantibar c m, hj]
      exact mem_polyCurve_vertex (List.get_mem ps j)
    · -- the ray piece at `P'.a`
        obtain ⟨P, hPmem, hPab⟩ := hcomb.pair P' hP'mem
        have hmem : (Work.Landing.Tsq c)^[m] w ∈ hN.rayPiece (angMul m P'.a) 0 R := by
          rw [← image_rayPiece hN m hR]
          exact ⟨w, hw, rfl⟩
        rw [hPab.1, rayPiece_fract_eq hN] at hmem
        exact mem_polyCurve_rayPiece_a hPmem hmem
    · -- the ray piece at `P'.b`
      obtain ⟨P, hPmem, hPab⟩ := hcomb.pair P' hP'mem
      have hmem : (Work.Landing.Tsq c)^[m] w ∈ hN.rayPiece (angMul m P'.b) 0 R := by
        rw [← image_rayPiece hN m hR]
        exact ⟨w, hw, rfl⟩
      rw [hPab.2, rayPiece_fract_eq hN] at hmem
      exact mem_polyCurve_rayPiece_b hPmem hmem
  · -- an equipotential arc between the two endpoints of a near arc of `ps'`
    obtain ⟨s, hs⟩ := Set.mem_range.mp hw
    obtain ⟨j, hj⟩ := hcomb.arc i
    have hs1 : (nearArc ps' i).1 ≤ (s : ℝ) := (Set.mem_Icc.mp s.2).1
    have hs2 : (s : ℝ) ≤ (nearArc ps' i).2 := (Set.mem_Icc.mp s.2).2
    rcases lt_or_eq_of_le hs1 with hlt1 | heq1
    · rcases lt_or_eq_of_le hs2 with hlt2 | heq2
      · -- an interior point of the arc: the angle map matches the near arcs
        have hIn : InArc (s : ℝ) (nearArc ps' i).1 (nearArc ps' i).2 :=
          InArc_of_mem_Ioo ⟨hlt1, hlt2⟩ (nearArc_len ps' i)
        have hIn' : InArc (angMul m (s : ℝ)) (nearArc ps j).1 (nearArc ps j).2 :=
          (hj (s : ℝ) hIn)
        obtain ⟨k, hk⟩ := InArc.exists_sub_mem_Ioo hIn' (nearArc_len ps j)
        have h1 : (Work.Landing.Tsq c)^[m] w = hN.rayPt (angMul m (s : ℝ)) R := by
          rw [← hs, rayPt_Tsq_iterate hN hB m hR', rpow_div_pow_mul hR0 m]
        rw [h1, show angMul m (s : ℝ) = (angMul m (s : ℝ) - k) + k from by ring,
          rayPt_add_one_int hN]
        exact mem_polyCurve_eqArc (ps := ps) (R := R)
          ⟨⟨angMul m (s : ℝ) - k, le_of_lt hk.1, le_of_lt hk.2⟩, rfl⟩
      · -- the upper endpoint of the near arc
        have hw' : w = hN.rayPt (ps'.get (nextIdx i)).a (R ^ ((1 : ℝ) / 4 ^ m)) := by
          rw [← hs, heq2]
          show hN.rayPt (ccwLift (ps'.get i).b (ps'.get (nextIdx i)).a)
            (R ^ ((1 : ℝ) / 4 ^ m)) = _
          rw [ccwLift]
          exact rayPt_add_one_int hN _ _ ⌈(ps'.get i).b - (ps'.get (nextIdx i)).a⌉
        obtain ⟨P, hPmem, hPab⟩ := hcomb.pair (ps'.get (nextIdx i)) (List.get_mem ps' (nextIdx i))
        rw [hw', rayPt_Tsq_iterate hN hB m hR', rpow_div_pow_mul hR0 m, hPab.1,
          rayPt_fract_eq hN _ _ hR]
        exact mem_polyCurve_rayPiece_a hPmem (rayPt_mem_rayPiece hN hR)
    · -- the lower endpoint of the near arc
      have hw' : w = hN.rayPt (ps'.get i).b (R ^ ((1 : ℝ) / 4 ^ m)) := by
        rw [← hs]
        exact congrArg (fun θ => hN.rayPt θ (R ^ ((1 : ℝ) / 4 ^ m))) heq1.symm
      obtain ⟨P, hPmem, hPab⟩ := hcomb.pair (ps'.get i) (List.get_mem ps' i)
      rw [hw', rayPt_Tsq_iterate hN hB m hR', rpow_div_pow_mul hR0 m, hPab.2,
        rayPt_fract_eq hN _ _ hR]
      exact mem_polyCurve_rayPiece_b hPmem (rayPt_mem_rayPiece hN hR)

/-- The polygon region lies in the complement of the polygon boundary. -/
theorem polyRegion_subset_compl {c : ℂ} (hN : DynB c) (ps : List (CoPair hN)) (R : ℝ) :
    polyRegion hN ps R ⊆ (polyCurve hN ps R)ᶜ := by
  rw [polyRegion]
  exact connectedComponentIn_subset _ _

/-! ## 5. The target theorem -/

theorem polyPullback {c : ℂ} (hN : DynB c) (m : ℕ) (ps ps' : List (CoPair hN)) (R : ℝ)
    (hR : 1 < R) (hA : PolyAdmissible hN ps) (hA' : PolyAdmissible hN ps')
    (hcv : ∀ k ∈ Finset.Icc 1 (2 * m),
      (LeanEval.ComplexAnalysis.Tantibar c)^[k] 0 ∉ polyRegion hN ps R)
    (hcomb : NearArcsCover hN ps ps' m)
    (hy : ∀ i : Fin ps'.length, ∃ j : Fin ps.length,
      (LeanEval.ComplexAnalysis.Tantibar c)^[2 * m] (ps'.get i).y = (ps.get j).y)
    (hopen : IsOpen (polyRegion hN ps R))
    (hopen' : IsOpen (polyRegion hN ps' (R ^ ((1 : ℝ) / 4 ^ m))))
    (hsc : IsSimplyConnected (polyRegion hN ps R))
    (hne : (polyRegion hN ps' (R ^ ((1 : ℝ) / 4 ^ m))).Nonempty)
    (hmap : Set.MapsTo ((Work.Landing.Tsq c)^[m])
      (polyRegion hN ps' (R ^ ((1 : ℝ) / 4 ^ m))) (polyRegion hN ps R)) :
    Set.BijOn ((Work.Landing.Tsq c)^[m])
      (polyRegion hN ps' (R ^ ((1 : ℝ) / 4 ^ m))) (polyRegion hN ps R) := by
  -- the critical orbit avoiding the `ps`-region makes the iterate a covering map there
  have hcov : IsCoveringMapOn ((Work.Landing.Tsq c)^[m]) (polyRegion hN ps R) := by
    refine isCoveringMapOn_tsqIterate_mono c m ?_
    intro v hv
    rw [Set.mem_compl_iff]
    rintro ⟨z, hz, hzv⟩
    obtain ⟨k, hk, hkz⟩ := critValues_tsqIterate (c := c) m z hz
    exact hcv k hk (hkz.symm.trans hzv ▸ hv)
  set U : Set ℂ := polyRegion hN ps' (R ^ ((1 : ℝ) / 4 ^ m)) with hU
  set V : Set ℂ := polyRegion hN ps R with hV
  set f : ℂ → ℂ := (Work.Landing.Tsq c)^[m] with hf
  have hUopen : IsOpen U := by rw [hU]; exact hopen'
  have hVopen : IsOpen V := by rw [hV]; exact hopen
  have hVsc : IsSimplyConnected V := by rw [hV]; exact hsc
  have hUne : U.Nonempty := by rw [hU]; exact hne
  have hmap' : Set.MapsTo f U V := by rw [hf, hU, hV]; exact hmap
  have hcov' : IsCoveringMapOn f V := by rw [hf, hV]; exact hcov
  have hUpre : IsPreconnected U := by rw [hU]; exact isPreconnected_connectedComponentIn
  have hUcompl : U ⊆ (polyCurve hN ps' (R ^ ((1 : ℝ) / 4 ^ m)))ᶜ := by
    rw [hU]; exact polyRegion_subset_compl hN ps' _
  have hVcompl : V ⊆ (polyCurve hN ps R)ᶜ := by rw [hV]; exact polyRegion_subset_compl hN ps R
  have hbound : f '' (polyCurve hN ps' (R ^ ((1 : ℝ) / 4 ^ m))) ⊆ polyCurve hN ps R := by
    rw [hf]; exact image_polyCurve_subset hN m ps ps' R hR hcomb hy
  haveI : SimplyConnectedSpace ↥V := hVsc
  haveI : LocallyPathConnectedSpace ↥V := hVopen.locallyPathConnectedSpace
  have hsurj : Set.SurjOn f U V := by
    have hUnec := hUne
    obtain ⟨u₀, hu₀⟩ := hUnec
    have hfu₀ : f u₀ ∈ V := hmap' hu₀
    -- lift the identity of `V` through the covering, from the preimage point `u₀`
    obtain ⟨F, ⟨hF₀, hF_lift⟩, -⟩ := hcov'.existsUnique_continuousMap_lifts
      ⟨fun v : ↥V => (v : ℂ), continuous_subtype_val⟩
      (a₀ := (⟨f u₀, hfu₀⟩ : ↥V)) (e₀ := u₀) rfl (fun v => v.2)
    have hFv : ∀ v : ↥V, f (F v) = (v : ℂ) := by
      intro v
      have h := congrFun hF_lift v
      simpa using h
    have hrangeV : f '' Set.range F = V := by
      refine Set.Subset.antisymm ?_ ?_
      · rintro y ⟨x, ⟨v, rfl⟩, rfl⟩
        rw [hFv v]
        exact v.2
      · intro y hy
        exact ⟨F ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, hFv ⟨y, hy⟩⟩
    have hno : f '' (polyCurve hN ps' (R ^ ((1 : ℝ) / 4 ^ m))) ∩ V = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hy1, hy2⟩
      exact (hVcompl hy2) (hbound hy1)
    have hScompl : Set.range F ⊆ (polyCurve hN ps' (R ^ ((1 : ℝ) / 4 ^ m)))ᶜ := by
      intro x hx
      rw [Set.mem_compl_iff]
      intro hxc
      have hmem : f x ∈ f '' (polyCurve hN ps' (R ^ ((1 : ℝ) / 4 ^ m))) ∩ V :=
        ⟨⟨x, hxc, rfl⟩, by rw [← hrangeV]; exact ⟨x, hx, rfl⟩⟩
      rw [hno] at hmem
      exact Set.notMem_empty (f x) hmem
    have hunion : IsPreconnected (U ∪ Set.range F) :=
      hUpre.union u₀ hu₀ ⟨⟨f u₀, hfu₀⟩, hF₀⟩ (isPreconnected_range F.continuous)
    have hbase : hN.rayPt (firstNearMid ps') (Real.sqrt (R ^ ((1 : ℝ) / 4 ^ m)))
        ∈ (polyCurve hN ps' (R ^ ((1 : ℝ) / 4 ^ m)))ᶜ := by
      by_contra hcon
      rw [hU, polyRegion, connectedComponentIn_eq_empty hcon] at hUne
      exact Set.not_nonempty_empty hUne
    have hrange_in_U : Set.range F ⊆ U := by
      have hb : hN.rayPt (firstNearMid ps') (Real.sqrt (R ^ ((1 : ℝ) / 4 ^ m)))
          ∈ U ∪ Set.range F := Or.inl (by
        rw [hU, polyRegion]
        exact mem_connectedComponentIn hbase)
      have hsub : U ∪ Set.range F ⊆ U := by
        have h2 : U ∪ Set.range F ⊆ polyRegion hN ps' (R ^ ((1 : ℝ) / 4 ^ m)) :=
          hunion.subset_connectedComponentIn hb (Set.union_subset hUcompl hScompl)
        rw [← hU] at h2
        exact h2
      exact Set.subset_union_right.trans hsub
    intro y hy
    exact ⟨F ⟨y, hy⟩, hrange_in_U ⟨⟨y, hy⟩, rfl⟩, hFv ⟨y, hy⟩⟩
  have hinj : Set.InjOn f U := by
    intro u₁ hu₁ u₂ hu₂ heq
    have hpre : u₁ ∈ f ⁻¹' V := hmap' hu₁
    have hpre₂ : u₂ ∈ f ⁻¹' V := hmap' hu₂
    have hcov'' : IsCoveringMap (V.restrictPreimage f) := hcov'.isCoveringMap_restrictPreimage
    -- the section of the covering over `V` through `u₁`
    set u₁' : ↥(f ⁻¹' V) := ⟨u₁, hpre⟩ with hu₁'
    obtain ⟨s, ⟨hs₀, hs_lift⟩, -⟩ := hcov''.existsUnique_continuousMap_lifts
      (ContinuousMap.id ↥V) (⟨f u₁, hmap' hu₁⟩ : ↥V) u₁' (Subtype.ext rfl)
    have hs_lift' : ∀ v : ↥V, V.restrictPreimage f (s v) = v := by
      intro v
      have h := congrFun hs_lift v
      simpa using h
    have hp₁ : V.restrictPreimage f u₁' = (⟨f u₁, hmap' hu₁⟩ : ↥V) := Subtype.ext rfl
    have hp₂ : V.restrictPreimage f (⟨u₂, hpre₂⟩ : ↥(f ⁻¹' V))
        = V.restrictPreimage f u₁' := Subtype.ext heq.symm
    -- the component of `f ⁻¹' V` through `u₁`, as a subset of the preimage
    set C' : Set ↥(f ⁻¹' V) := Subtype.val ⁻¹' connectedComponentIn (f ⁻¹' V) u₁ with hC'
    have hC'pre : IsPreconnected C' := by
      rw [hC', connectedComponentIn_eq_image hpre,
        Set.preimage_image_eq _ Subtype.val_injective]
      exact isPreconnected_connectedComponent
    have hu₂C' : (⟨u₂, hpre₂⟩ : ↥(f ⁻¹' V)) ∈ C' := by
      rw [hC', Set.mem_preimage]
      exact hUpre.subset_connectedComponentIn hu₁ (fun x hx => hmap' hx) hu₂
    have hEqOn : C'.EqOn (fun e : ↥(f ⁻¹' V) => e) fun e => s (V.restrictPreimage f e) := by
      refine hcov''.eqOn_of_comp_eqOn (a := u₁') hC'pre continuous_id.continuousOn ?_ ?_ ?_ ?_
      · exact (s.continuous.comp hcov''.continuous).continuousOn
      · intro e _
        exact (hs_lift' (V.restrictPreimage f e)).symm
      · rw [hC', Set.mem_preimage]
        exact mem_connectedComponentIn hpre
      · rw [hp₁]
        exact hs₀.symm
    have halu₂ : (⟨u₂, hpre₂⟩ : ↥(f ⁻¹' V))
        = s (V.restrictPreimage f ⟨u₂, hpre₂⟩) := by
      simpa only [] using hEqOn hu₂C'
    rw [hp₂, hp₁, hs₀] at halu₂
    exact (Subtype.ext_iff.mp halu₂).symm
  exact ⟨hmap', hinj, hsurj⟩

end Work.ELPull