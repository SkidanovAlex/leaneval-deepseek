import Mathlib
import Submission.Work.SeedSimple2.Defs
import Submission.Work.SeedSimple2.COP.mem_pairSide_iff_InArc
import Submission.Work.SeedSimple2.COP.fract_mul_injOn
import Submission.Work.SeedSimple2.COP.F_basics
import Submission.Work.SeedSimple2.COP.landsN_pow
import Submission.Work.ELTop.paramRay_disjoint
import Submission.Work.ELTop.RigInput
import Submission.Work.ELRig.rayPt_iterate
import Submission.Work.ELTop.rayPt_add_int

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedSimple2.COP

/-- Two angles `a, b` of the representative interval `[0,1)` which are congruent modulo `1` are
equal: if `a = b + k` for `k : ℤ` then `k = 0`. -/
private theorem eq_of_eq_add_int_of_mem_Ico {a b : ℝ} (ha : a ∈ Set.Ico (0:ℝ) 1)
    (hb : b ∈ Set.Ico (0:ℝ) 1) {k : ℤ} (hk : a = b + k) : a = b := by
  have hlt : (k:ℝ) < 1 := by linarith [ha.2, hb.1, hk]
  have hgt : -1 < (k:ℝ) := by linarith [hb.2, ha.1, hk]
  have hk0 : k = 0 := by
    have h1 : k < 1 := by exact_mod_cast hlt
    have h2 : -1 < k := by exact_mod_cast hgt
    omega
  rw [hk0, Int.cast_zero, add_zero] at hk
  exact hk

/-- Two distinct angles of the representative interval `[0,1)` are not congruent modulo `1`:
the cyclic arc between them is nondegenerate. -/
private theorem arcLen_ne_zero_of_ne {a b : ℝ} (ha : a ∈ Set.Ico (0:ℝ) 1)
    (hb : b ∈ Set.Ico (0:ℝ) 1) (h : a ≠ b) : Work.EL.arcLen a b ≠ 0 := by
  intro h0
  rw [Work.EL.arcLen] at h0
  obtain ⟨k, hk⟩ := Set.mem_range.mp (Int.fract_eq_zero_iff.mp h0)
  have hk' : (k : ℝ) = b - a := hk
  have h2 : -(1:ℝ) < (k:ℝ) ∧ (k:ℝ) < 1 := by
    constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, hk']
  have h3 : (-1 : ℤ) < k := by exact_mod_cast h2.1
  have h4 : k < (1 : ℤ) := by exact_mod_cast h2.2
  have h5 : k = 0 := by omega
  rw [h5] at hk'
  push_cast at hk'
  exact h (by linarith)

/-- **`L7` with the conclusion of `L6` as an explicit hypothesis** (`NOTES_LEAD_mandelbar_rn0.md` §2, `L7`; `COP/NOTES_COP.md` §4).

For three distinct landing angles `x, a, e` of the parabolic point `z₁` (with `a, e ≠ 0`), the cyclic arc membership of `x` in `(a,e)` is equivalent to that of `Int.fract (1024 * x)` in `(Int.fract (1024 * a), Int.fract (1024 * e))`.  The hypothesis `hcop` is the (universally quantified) conclusion of `Work.SeedSimple2.COP.cop_sides d hJ`;  the wrapper `Work.SeedSimple2.COP.cop_angles` instantiates it.

Proof design.  Put `Fa := Int.fract (1024 * a)`, `Fe := Int.fract (1024 * e)`,
`Q := { toRawPair := ⟨a, e, d.z₁⟩, lands_a := ha.2, lands_b := he.2 }` and
`Q' := { toRawPair := ⟨Fa, Fe, d.z₁⟩, lands_a := ..., lands_b := ... }`, the landings of `Fa`, `Fe` being `Work.SeedSimple2.landsN_T_iterate d 10 ha.2` / `he.2` followed by `Work.SeedSimple2.landsN_add_int` and `(Tantibar c)^[10] z₁ = d.z₁` (`d.per_half` twice).  Get `PairSides` for both from `Work.ELTop.pairSides d.hN hJ Q hnd` / `Q' hnd'`, where `hnd : Work.EL.arcLen Q.a Q.b ≠ 0` (`hae` with `a, e ∈ Set.Ico 0 1`) and `hnd' : Work.EL.arcLen Q'.a Q'.b ≠ 0` (from `Work.SeedSimple2.COP.fract_mul_injOn d ha he` applied to `hae`).  Apply `hcop Q Q' rfl rfl (Ioo from `ha0`) (Ioo from `he0`) hae ⟨-⌊1024*a⌋, ...⟩ ⟨-⌊1024*e⌋, ...⟩ hnd'` to the witness `z := Work.EL.rayPt d.hN x s` with `s ∈ (1,s₁)` so that `z ∈ Metric.ball d.z₁ ε` (`hx.2`);  `z ∉ Work.EL.pairCurve Q` because `Work.ELTop.paramRay_disjoint d.hN` forces `x ≡ a` or `x ≡ e` mod `1` otherwise (`hxa`, `hxe`, all in `[0,1)`), and `Work.EL.F c z ∈ Work.EL.paramRay d.hN (Int.fract (1024 * x))` (`Work.ELRig.rayPt_iterate`, `Work.ELTop.rayPt_add_int`) is off `Work.EL.pairCurve Q'` by `fract_mul_injOn`.  Finish with `Work.SeedSimple2.COP.mem_pairSide_iff_InArc` on `Q` at `z` and on `Q'` at `Work.EL.F c z`. -/
theorem cop_angles_of_sides {c : ℂ} (d : Work.EL.RootParabolic c) (hJ : Work.Top.JordanForm)
    (hcop : ∀ (Q Q' : Work.EL.CoPair d.hN), Q.y = d.z₁ → Q'.y = d.z₁ →
      Q.a ∈ Set.Ioo (0:ℝ) 1 → Q.b ∈ Set.Ioo (0:ℝ) 1 → Q.a ≠ Q.b →
      (∃ k : ℤ, Q'.a = 1024 * Q.a + k) → (∃ k : ℤ, Q'.b = 1024 * Q.b + k) →
      Work.EL.arcLen Q'.a Q'.b ≠ 0 →
      ∃ ε > 0, ∀ z : ℂ, z ∈ Metric.ball d.z₁ ε → z ∉ Work.EL.pairCurve Q →
        (z ∈ Work.EL.pairSide Q ↔ Work.EL.F c z ∈ Work.EL.pairSide Q'))
    {x a e : ℝ} (hx : x ∈ Work.SeedSimple2.LandAngles d.hN d.z₁)
    (ha : a ∈ Work.SeedSimple2.LandAngles d.hN d.z₁)
    (he : e ∈ Work.SeedSimple2.LandAngles d.hN d.z₁)
    (ha0 : a ≠ 0) (he0 : e ≠ 0) (hxa : x ≠ a) (hxe : x ≠ e) (hae : a ≠ e) :
    Work.EL.InArc x a e ↔
      Work.EL.InArc (Int.fract (1024 * x)) (Int.fract (1024 * a)) (Int.fract (1024 * e)) := by
  have hxIco : x ∈ Set.Ico (0:ℝ) 1 := hx.1
  have hxland : Work.EL.LandsN d.hN x d.z₁ := hx.2
  have haIco : a ∈ Set.Ico (0:ℝ) 1 := ha.1
  have haland : Work.EL.LandsN d.hN a d.z₁ := ha.2
  have heIco : e ∈ Set.Ico (0:ℝ) 1 := he.1
  have heland : Work.EL.LandsN d.hN e d.z₁ := he.2
  -- the two endpoints `a`, `e` lie in `(0,1)`
  have haIoo : a ∈ Set.Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne haIco.1 (Ne.symm ha0), haIco.2⟩
  have heIoo : e ∈ Set.Ioo (0:ℝ) 1 := ⟨lt_of_le_of_ne heIco.1 (Ne.symm he0), heIco.2⟩
  -- the `F`-images of the angles lie in `[0,1)`
  have hFaIco : Int.fract (1024 * a) ∈ Set.Ico (0:ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hFeIco : Int.fract (1024 * e) ∈ Set.Ico (0:ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  have hFxIco : Int.fract (1024 * x) ∈ Set.Ico (0:ℝ) 1 :=
    ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  -- `F` is injective on the four relevant landing angles
  have hFa_ne_Fe : Int.fract (1024 * a) ≠ Int.fract (1024 * e) :=
    fun h => hae (fract_mul_injOn d ha he h)
  have hFx_ne_Fa : Int.fract (1024 * x) ≠ Int.fract (1024 * a) :=
    fun h => hxa (fract_mul_injOn d hx ha h)
  have hFx_ne_Fe : Int.fract (1024 * x) ≠ Int.fract (1024 * e) :=
    fun h => hxe (fract_mul_injOn d hx he h)
  -- the `F`-images of `a` and `e` are again landing angles
  have hFa_land : Work.EL.LandsN d.hN (Int.fract (1024 * a)) d.z₁ := by
    have h := (landsN_pow d ha 1).2
    simpa using h
  have hFe_land : Work.EL.LandsN d.hN (Int.fract (1024 * e)) d.z₁ := by
    have h := (landsN_pow d he 1).2
    simpa using h
  -- the two co-landing pairs
  set Q : Work.EL.CoPair d.hN :=
    { toRawPair := ⟨a, e, d.z₁⟩, lands_a := haland, lands_b := heland } with hQ
  set Q' : Work.EL.CoPair d.hN :=
    { toRawPair := ⟨Int.fract (1024 * a), Int.fract (1024 * e), d.z₁⟩,
      lands_a := hFa_land, lands_b := hFe_land } with hQ'
  -- non-degeneracy of the two pairs
  have hnd : Work.EL.arcLen Q.a Q.b ≠ 0 := arcLen_ne_zero_of_ne haIco heIco hae
  have hnd' : Work.EL.arcLen Q'.a Q'.b ≠ 0 := arcLen_ne_zero_of_ne hFaIco hFeIco hFa_ne_Fe
  -- two-sidedness of the two pairs
  have hSQ : Work.EL.PairSides d.hN Q := Work.ELTop.pairSides d.hN hJ Q hnd
  have hSQ' : Work.EL.PairSides d.hN Q' := Work.ELTop.pairSides d.hN hJ Q' hnd'
  -- the angle-congruence side conditions of `mem_pairSide_iff_InArc`
  have hQab : ∀ k : ℤ, Q.b ≠ Q.a + k :=
    fun k hk => (Ne.symm hae) (eq_of_eq_add_int_of_mem_Ico heIco haIco hk)
  have hQθa : ∀ k : ℤ, x ≠ Q.a + k :=
    fun k hk => hxa (eq_of_eq_add_int_of_mem_Ico hxIco haIco hk)
  have hQθb : ∀ k : ℤ, x ≠ Q.b + k :=
    fun k hk => hxe (eq_of_eq_add_int_of_mem_Ico hxIco heIco hk)
  have hQ'ab : ∀ k : ℤ, Q'.b ≠ Q'.a + k :=
    fun k hk => hFa_ne_Fe.symm (eq_of_eq_add_int_of_mem_Ico hFeIco hFaIco hk)
  have hQ'θa : ∀ k : ℤ, Int.fract (1024 * x) ≠ Q'.a + k :=
    fun k hk => hFx_ne_Fa (eq_of_eq_add_int_of_mem_Ico hFxIco hFaIco hk)
  have hQ'θb : ∀ k : ℤ, Int.fract (1024 * x) ≠ Q'.b + k :=
    fun k hk => hFx_ne_Fe (eq_of_eq_add_int_of_mem_Ico hFxIco hFeIco hk)
  -- the two pairs are related by the angle map of `F`
  have ha' : ∃ k : ℤ, Q'.a = 1024 * Q.a + k := by
    refine ⟨-⌊1024 * a⌋, ?_⟩
    have h := Int.fract_add_floor (1024 * a)
    push_cast
    linarith
  have hb' : ∃ k : ℤ, Q'.b = 1024 * Q.b + k := by
    refine ⟨-⌊1024 * e⌋, ?_⟩
    have h := Int.fract_add_floor (1024 * e)
    push_cast
    linarith
  -- `L6`
  obtain ⟨ε, hεpos, hball⟩ := hcop Q Q' rfl rfl haIoo heIoo hae ha' hb' hnd'
  -- a witness on the ray of `x`, of small level
  obtain ⟨s₀, hs₀, hnear⟩ := exists_level_ball_of_landsN d.hN hxland hεpos
  set s : ℝ := (1 + s₀) / 2 with hsdef
  have hs1 : 1 < s := by rw [hsdef]; linarith
  have hss : s < s₀ := by rw [hsdef]; linarith
  have hzball : Work.EL.rayPt d.hN x s ∈ Metric.ball d.z₁ ε := hnear s ⟨hs1, hss⟩
  have hzmem : Work.EL.rayPt d.hN x s ∈ Work.EL.paramRay d.hN x :=
    Work.EL.rayPt_mem_paramRay d.hN hs1
  -- the witness is off the pair curve of `Q`
  have hzX : Work.EL.rayPt d.hN x s ∉ Work.EL.pairCurve Q := by
    intro hmem
    rw [Work.EL.mem_pairCurve_iff] at hmem
    rcases hmem with h | h | h
    · exact (Set.disjoint_left.mp (Work.ELTop.paramRay_disjoint d.hN hQθa) h) hzmem
    · have hzK : Work.EL.rayPt d.hN x s ∉ Work.EL.K c := Work.EL.rayPt_notMem_K d.hN hs1
      exact hzK (by rw [h]; exact Work.ELTop.landsN_mem_K d.hN haland)
    · exact (Set.disjoint_left.mp (Work.ELTop.paramRay_disjoint d.hN hQθb) h) hzmem
  -- the image of the witness lies on the ray of `Int.fract (1024 * x)`
  have hFzmem : Work.EL.F c (Work.EL.rayPt d.hN x s) ∈
      Work.EL.paramRay d.hN (Int.fract (1024 * x)) := by
    rw [Work.ELRig.rayPt_iterate d.hN d.bottcher hs1]
    obtain ⟨m, hm⟩ := Work.ELRig.T_iterate_eq_add_int x 10
    have hm1024 : (Work.EL.T^[10]) x = 1024 * x + (m : ℝ) := by
      have hh : ((-2:ℝ)^10) = 1024 := by norm_num
      rw [hh] at hm; exact hm
    have hsplit : 1024 * x + (m : ℝ)
        = Int.fract (1024 * x) + ((⌊1024 * x⌋ + m : ℤ) : ℝ) := by
      have hfl := Int.fract_add_floor (1024 * x)
      push_cast
      linarith
    rw [hm1024, hsplit,
      Work.ELTop.rayPt_add_int d.hN (Int.fract (1024 * x)) (s ^ (1024:ℕ))
        (⌊1024 * x⌋ + m)]
    exact Work.EL.rayPt_mem_paramRay d.hN (one_lt_pow₀ hs1 (by norm_num))
  -- read the sides off the angles
  have h1 : Work.EL.rayPt d.hN x s ∈ Work.EL.pairSide Q ↔ Work.EL.InArc x Q.a Q.b :=
    mem_pairSide_iff_InArc d.hN Q hSQ hQab hQθa hQθb hzmem
  have h2 : Work.EL.F c (Work.EL.rayPt d.hN x s) ∈ Work.EL.pairSide Q' ↔
      Work.EL.InArc (Int.fract (1024 * x)) Q'.a Q'.b :=
    mem_pairSide_iff_InArc d.hN Q' hSQ' hQ'ab hQ'θa hQ'θb hFzmem
  have hkey := hball (Work.EL.rayPt d.hN x s) hzball hzX
  exact h1.symm.trans (hkey.trans h2)

end Work.SeedSimple2.COP
