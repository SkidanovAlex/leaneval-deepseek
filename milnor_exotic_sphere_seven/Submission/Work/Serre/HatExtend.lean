import Mathlib
import Submission.Work.Serre.E2bDefs
import Submission.Work.RatHurewicz.DomeMap
import Submission.Work.ThomBordism.TwoSet.ConeDescent

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The hat extension lemma of E2(b): the explicit "dome" construction
-/

open scoped Topology unitInterval
open Work.Stems.Cubical

namespace Work.Serre

noncomputable section

open Work.ThomBordism.TwoSet (rad bpt rad_nonneg rad_le_one rad_le rad_boundary_eq_one
  continuous_rad bpt_mem_boundary bpt_eq_self_of_mem_boundary)
open Work.RatHurewicz (domeR domeR_pos domeR_le_one domeR_ge_half domeR_eq_half domeR_eq
  domeSpace domeTime domeSpace_coe domeTime_coe continuous_domeSpace continuous_domeTime
  domScale domScale_coe domScale_rad continuous_domeR domeR_eq_one_iff)

/-- The **hat parametrisation** `hatPsi : Iⁿ → LSet n ⊆ Iⁿ × I`, the "flipped dome map":
`y ↦ (domeSpace y, 2 * domeR y - 1)`. -/
noncomputable def hatPsi {n : ℕ} (hn : 1 ≤ n) (y : IC n) : IC n × unitInterval :=
  (domeSpace hn y, ⟨2 * domeR hn y - 1, by
    have h1 := domeR_ge_half hn y; have h2 := domeR_le_one hn y
    constructor <;> linarith⟩)

@[simp] theorem hatPsi_fst {n : ℕ} (hn : 1 ≤ n) (y : IC n) : (hatPsi hn y).1 = domeSpace hn y := rfl

@[simp] theorem hatPsi_snd_coe {n : ℕ} (hn : 1 ≤ n) (y : IC n) :
    ((hatPsi hn y).2 : ℝ) = 2 * domeR hn y - 1 := rfl

theorem continuous_hatPsi {n : ℕ} (hn : 1 ≤ n) : Continuous (hatPsi hn) := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_domeSpace hn
  · refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul (continuous_domeR hn)).sub continuous_const

/-- `hatPsi` maps the boundary of the cube to the outer boundary of the hat. -/
theorem hatPsi_of_mem_boundary {n : ℕ} (hn : 1 ≤ n) {y : IC n}
    (hy : y ∈ Cube.boundary (Fin n)) : hatPsi hn y = (y, 1) := by
  have hrad : rad hn y = 1 := rad_boundary_eq_one hn hy
  have hR : domeR hn y = 1 := domeR_eq_one_iff hn y |>.mpr hrad
  refine Prod.ext ?_ ?_
  · funext i
    apply Subtype.ext
    rw [hatPsi_fst, domeSpace_coe, hR, div_one]
    ring
  · apply Subtype.ext
    rw [hatPsi_snd_coe, hR]; norm_num

/-- `hatPsi` lands in the hat. -/
theorem hatPsi_mem_hat {n : ℕ} (hn : 1 ≤ n) (y : IC n) :
    hatPsi hn y ∈ Work.StemsB.LSet n := by
  by_cases hr : rad hn y ≤ 1 / 2
  · left
    have hR : domeR hn y = 1 / 2 := domeR_eq_half hr
    have h2 : ((hatPsi hn y).2 : ℝ) = 0 := by rw [hatPsi_snd_coe, hR]; norm_num
    exact Subtype.ext h2
  · right
    have hR : domeR hn y = rad hn y := domeR_eq (le_of_not_ge hr)
    have hne : rad hn y ≠ 0 := by linarith
    have hb : bpt hn y ∈ Cube.boundary (Fin n) := bpt_mem_boundary hn y hne
    have hspace : domeSpace hn y = bpt hn y := by
      funext i
      apply Subtype.ext
      rw [domeSpace_coe, hR, Work.ThomBordism.TwoSet.bpt_coe]
      rfl
    rw [hatPsi_fst, hspace]
    exact hb

/-- **Surjectivity of `hatPsi` onto the hat.** -/
theorem hatPsi_surj {n : ℕ} (hn : 1 ≤ n) {q : IC n × unitInterval}
    (hq : q ∈ Work.StemsB.LSet n) : ∃ y : IC n, hatPsi hn y = q := by
  rcases hq with h0 | hb
  · -- the bottom face: the "cap" parametrisation of the inner region
    refine ⟨domScale (1/2) (by norm_num) (by norm_num) q.1, ?_⟩
    have hrad : rad hn (domScale (1/2) (by norm_num) (by norm_num) q.1) ≤ 1 / 2 := by
      rw [domScale_rad hn, mul_comm]
      calc rad hn q.1 * (1 / 2) ≤ 1 * (1 / 2) :=
            mul_le_mul_of_nonneg_right (rad_le_one hn q.1) (by norm_num)
        _ = 1 / 2 := by norm_num
    have hR := domeR_eq_half hrad
    refine Prod.ext ?_ ?_
    · funext i
      apply Subtype.ext
      rw [hatPsi_fst, domeSpace_coe, hR, domScale_coe]
      field_simp
      ring
    · apply Subtype.ext
      rw [hatPsi_snd_coe, hR, h0]
      norm_num
  · -- the lateral boundary: the radial regime
    obtain ⟨i, hi⟩ := hb
    have hrad : rad hn q.1 = 1 := rad_boundary_eq_one hn ⟨i, hi⟩
    have hq0 : (0:ℝ) ≤ q.2 := q.2.2.1
    have hq1 : (q.2 : ℝ) ≤ 1 := q.2.2.2
    refine ⟨domScale ((1 + (q.2 : ℝ)) / 2) (by linarith) (by linarith) q.1, ?_⟩
    have hrad2 : rad hn (domScale ((1 + (q.2 : ℝ)) / 2) (by linarith) (by linarith) q.1)
        = (1 + (q.2 : ℝ)) / 2 := by
      rw [domScale_rad hn, hrad, mul_one]
    have hge : 1 / 2 ≤ (1 + (q.2 : ℝ)) / 2 := by linarith
    have hR : domeR hn (domScale ((1 + (q.2 : ℝ)) / 2) (by linarith) (by linarith) q.1)
        = (1 + (q.2 : ℝ)) / 2 := by
      rw [domeR_eq (by rw [hrad2]; exact hge), hrad2]
    refine Prod.ext ?_ ?_
    · funext j
      apply Subtype.ext
      rw [hatPsi_fst, domeSpace_coe, hR, domScale_coe]
      field_simp
      ring
    · apply Subtype.ext
      rw [hatPsi_snd_coe, hR]
      ring

/-- `domScale` is continuous in the point. -/
theorem continuous_domScale {m : ℕ} {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    Continuous (fun v : Fin m → unitInterval => domScale ρ h0 h1 v) := by
  refine continuous_pi (fun i => ?_)
  rw [show (fun v : Fin m → unitInterval => domScale ρ h0 h1 v i)
      = fun v => (⟨1 / 2 + ρ * ((v i : ℝ) - 1 / 2),
          (domScale ρ h0 h1 v i).2⟩ : unitInterval) from rfl]
  exact Continuous.subtype_mk (continuous_const.add (continuous_const.mul
    ((continuous_subtype_val.comp (continuous_apply i)).sub continuous_const))) _

/-- The convex combination of two points of a cube, with coordinates in `[0,1]`. -/
noncomputable def convComb {m : ℕ} (t : unitInterval) (A B : Fin m → unitInterval) :
    Fin m → unitInterval :=
  fun i => ⟨(1 - (t : ℝ)) * (A i : ℝ) + (t : ℝ) * (B i : ℝ), by
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have ha := (A i).2
    have hb := (B i).2
    constructor <;> nlinarith [ha.1, ha.2, hb.1, hb.2]⟩

@[simp] theorem convComb_coe {m : ℕ} (t : unitInterval) (A B : Fin m → unitInterval) (i : Fin m) :
    ((convComb t A B i : unitInterval) : ℝ)
      = (1 - (t : ℝ)) * (A i : ℝ) + (t : ℝ) * (B i : ℝ) := rfl

theorem continuous_convComb {m : ℕ} :
    Continuous (fun p : unitInterval × ((Fin m → unitInterval) × (Fin m → unitInterval)) =>
      convComb p.1 p.2.1 p.2.2) := by
  refine continuous_pi (fun i => ?_)
  rw [show (fun p : unitInterval × ((Fin m → unitInterval) × (Fin m → unitInterval)) =>
        convComb p.1 p.2.1 p.2.2 i)
      = fun p => (⟨(1 - (p.1 : ℝ)) * ((p.2.1 i : unitInterval) : ℝ)
          + (p.1 : ℝ) * ((p.2.2 i : unitInterval) : ℝ),
          (convComb p.1 p.2.1 p.2.2 i).2⟩ : unitInterval) from rfl]
  refine Continuous.subtype_mk (f := fun p : unitInterval ×
      ((Fin m → unitInterval) × (Fin m → unitInterval)) =>
      (1 - (p.1 : ℝ)) * ((p.2.1 i : unitInterval) : ℝ)
        + (p.1 : ℝ) * ((p.2.2 i : unitInterval) : ℝ)) ?_ _
  fun_prop

/-- The **spread** `Theta : Iⁿ × I → Iⁿ × I`. -/
noncomputable def Theta {n : ℕ} (hn : 1 ≤ n) (p : IC n × unitInterval) : IC n × unitInterval :=
  (convComb p.2 (domScale (1/2) (by norm_num) (by norm_num) p.1) (domeSpace hn p.1),
    p.2 * domeTime hn p.1)

@[simp] theorem Theta_fst_coe {n : ℕ} (hn : 1 ≤ n) (p : IC n × unitInterval) (i : Fin n) :
    (((Theta hn p).1 i : unitInterval) : ℝ)
      = (1 - (p.2 : ℝ)) * ((domScale (1/2) (by norm_num) (by norm_num) p.1) i : ℝ)
        + (p.2 : ℝ) * ((domeSpace hn p.1) i : ℝ) := rfl

@[simp] theorem Theta_snd_coe {n : ℕ} (hn : 1 ≤ n) (p : IC n × unitInterval) :
    (((Theta hn p).2 : unitInterval) : ℝ) = (p.2 : ℝ) * (domeTime hn p.1 : ℝ) := rfl

theorem continuous_Theta {n : ℕ} (hn : 1 ≤ n) : Continuous (Theta hn) := by
  refine Continuous.prodMk ?_ ?_
  · exact continuous_convComb.comp (continuous_snd.prodMk
      ((continuous_domScale (by norm_num) (by norm_num)).comp continuous_fst |>.prodMk
        ((continuous_domeSpace hn).comp continuous_fst)))
  · exact continuous_snd.mul ((continuous_domeTime hn).comp continuous_fst)

/-- `domeSpace` fixes the boundary of the cube. -/
theorem domeSpace_eq_self_of_mem_boundary {n : ℕ} (hn : 1 ≤ n) {u : IC n}
    (hu : u ∈ Cube.boundary (Fin n)) : domeSpace hn u = u := by
  have hR : domeR hn u = 1 := (domeR_eq_one_iff hn u).mpr (rad_boundary_eq_one hn hu)
  funext i
  apply Subtype.ext
  rw [domeSpace_coe, hR, div_one]
  ring

/-- `domeTime` vanishes on the boundary of the cube. -/
theorem domeTime_eq_zero_of_mem_boundary {n : ℕ} (hn : 1 ≤ n) {u : IC n}
    (hu : u ∈ Cube.boundary (Fin n)) : domeTime hn u = 0 := by
  have hR : domeR hn u = 1 := (domeR_eq_one_iff hn u).mpr (rad_boundary_eq_one hn hu)
  apply Subtype.ext
  rw [domeTime_coe, hR]
  norm_num

/-- `domeSpace` lands on the boundary of the cube in the radial regime. -/
theorem domeSpace_mem_boundary {n : ℕ} (hn : 1 ≤ n) {y : IC n} (h : 1 / 2 ≤ rad hn y) :
    domeSpace hn y ∈ Cube.boundary (Fin n) := by
  have hR : domeR hn y = rad hn y := domeR_eq h
  have hne : rad hn y ≠ 0 := by linarith
  have hb : bpt hn y ∈ Cube.boundary (Fin n) := bpt_mem_boundary hn y hne
  have hspace : domeSpace hn y = bpt hn y := by
    funext i
    apply Subtype.ext
    rw [domeSpace_coe, hR, Work.ThomBordism.TwoSet.bpt_coe]
    rfl
  rwa [hspace]

/-- The values of the spread on the hat are prescribed by `hatPsi`. -/
theorem Theta_psi {n : ℕ} (hn : 1 ≤ n) (y : IC n) : Theta hn (hatPsi hn y) = (y, 0) := by
  by_cases hr : rad hn y ≤ 1 / 2
  · -- the "cap" regime: `hatPsi y = (2 y - 1/2, 0)`
    have hR : domeR hn y = 1 / 2 := domeR_eq_half hr
    have hds : ∀ i : Fin n,
        ((domScale (1/2) (by norm_num) (by norm_num) (domeSpace hn y) i : unitInterval) : ℝ)
          = y i := by
      intro i
      rw [domScale_coe, domeSpace_coe, hR]
      field_simp
      ring
    refine Prod.ext ?_ ?_
    · funext i
      apply Subtype.ext
      rw [Theta_fst_coe]
      simp only [hatPsi_fst, hatPsi_snd_coe, hR]
      norm_num
      rw [hds i]
    · apply Subtype.ext
      rw [Theta_snd_coe]
      simp only [hatPsi_fst, hatPsi_snd_coe, hR]
      norm_num
  · -- the radial regime
    have hr' : 1 / 2 ≤ rad hn y := le_of_not_ge hr
    have hR : domeR hn y = rad hn y := domeR_eq hr'
    have hbnd : domeSpace hn y ∈ Cube.boundary (Fin n) := domeSpace_mem_boundary hn hr'
    have hidem : domeSpace hn (domeSpace hn y) = domeSpace hn y :=
      domeSpace_eq_self_of_mem_boundary hn hbnd
    have hzero : domeTime hn (domeSpace hn y) = 0 :=
      domeTime_eq_zero_of_mem_boundary hn hbnd
    -- the coordinate formulas
    have hbptR : ∀ i : Fin n, ((domeSpace hn y i : unitInterval) : ℝ)
        = 1 / 2 + ((y i : ℝ) - 1 / 2) / rad hn y := by
      intro i
      rw [domeSpace_coe, hR]
    have hradpos : 0 < rad hn y := by linarith
    refine Prod.ext ?_ ?_
    · funext i
      apply Subtype.ext
      rw [Theta_fst_coe]
      simp only [hatPsi_fst, hatPsi_snd_coe, hR, hidem]
      rw [domScale_coe, hbptR i]
      field_simp
      ring
    · apply Subtype.ext
      rw [Theta_snd_coe]
      simp only [hatPsi_fst, hatPsi_snd_coe, hR, hidem, hzero]
      push_cast
      ring

/-- The values of the spread on the top face lie in the "compression region"
`(∂Iⁿ × I) ∪ (Iⁿ × {1})`. -/
theorem Theta_top {n : ℕ} (hn : 1 ≤ n) (x : IC n) :
    (Theta hn (x, 1)).1 ∈ Cube.boundary (Fin n) ∨ (Theta hn (x, 1)).2 = 1 := by
  by_cases hR : domeR hn x = 1 / 2
  · -- the cap regime: the spread fixes the top face
    right
    have hdt : domeTime hn x = 1 := by
      apply Subtype.ext
      rw [domeTime_coe, hR]; norm_num
    show (Theta hn (x, 1)).2 = 1
    rw [show (Theta hn (x, 1)).2 = (1 : unitInterval) * domeTime hn x from rfl, one_mul, hdt]
  · left
    have hge : 1 / 2 < domeR hn x := lt_of_le_of_ne (domeR_ge_half hn x) (Ne.symm hR)
    have hrad : 1 / 2 < rad hn x := by
      rcases le_or_gt (rad hn x) (1 / 2) with h | h
      · rw [domeR_eq_half h] at hge; linarith
      · exact h
    have hbnd : domeSpace hn x ∈ Cube.boundary (Fin n) := domeSpace_mem_boundary hn (le_of_lt hrad)
    have htwo : (Theta hn (x, 1)).1 = domeSpace hn x := by
      funext i
      apply Subtype.ext
      rw [Theta_fst_coe]
      norm_num
    rw [htwo]
    exact hbnd

/-- **The hat extension lemma.**  If `CompressRel X A n` holds (`n ≥ 1`), then every continuous map
`f` on the hat `LSet n = (Iⁿ × {0}) ∪ (∂Iⁿ × I)` which carries the outer boundary
`hatBdry n = ∂Iⁿ × {1}` into `A` extends to a map `G : Iⁿ × I → X` with `G = f` on the hat and
`G (Iⁿ × {1}) ⊆ A`. -/
theorem hatExtend {X : Type} [TopologicalSpace X] {A : Set X} {n : ℕ} (hn : 1 ≤ n)
    (hc : Work.RatHurewicz.CompressRel X A n)
    (f : ContinuousMap (↥(Work.StemsB.LSet n)) X)
    (hf : ∀ q : ↥(Work.StemsB.LSet n),
      (q : IC n × unitInterval) ∈ Work.Serre.hatBdry n → f q ∈ A) :
    ∃ G : ContinuousMap (IC n × unitInterval) X,
      (∀ q : ↥(Work.StemsB.LSet n), G (q : IC n × unitInterval) = f q) ∧
      (∀ x : IC n, G (x, 1) ∈ A) := by
  -- the parametrisation of the hat, as a map into the hat
  have hmem : ∀ y : IC n, hatPsi hn y ∈ Work.StemsB.LSet n := fun y => hatPsi_mem_hat hn y
  let psiHat : C(IC n, ↥(Work.StemsB.LSet n)) :=
    ⟨fun y => ⟨hatPsi hn y, hmem y⟩, Continuous.subtype_mk (continuous_hatPsi hn) _⟩
  have hpsiHat : ∀ y : IC n, (psiHat y : IC n × unitInterval) = hatPsi hn y := fun y => rfl
  -- the induced map of the bottom face
  let g : C(IC n, X) := f.comp psiHat
  have hg_apply : ∀ y : IC n, g y = f ⟨hatPsi hn y, hmem y⟩ := fun y => rfl
  -- its boundary lies in `A`
  have hgb : ∀ y : IC n, y ∈ Cube.boundary (Fin n) → g y ∈ A := by
    intro y hy
    refine hf ⟨hatPsi hn y, hmem y⟩ ?_
    have h1 : (hatPsi hn y).1 = y := by rw [hatPsi_of_mem_boundary hn hy]
    have h2 : (hatPsi hn y).2 = 1 := by rw [hatPsi_of_mem_boundary hn hy]
    exact ⟨by rw [h1]; exact hy, h2⟩
  obtain ⟨K, hK0, hKb, hK1⟩ := hc g hgb
  refine ⟨K.comp ⟨Theta hn, continuous_Theta hn⟩, ?_, ?_⟩
  · intro q
    obtain ⟨y, hy⟩ := hatPsi_surj hn q.2
    have hsub : (⟨hatPsi hn y, hmem y⟩ : ↥(Work.StemsB.LSet n)) = q := Subtype.ext hy
    have hq : (q : IC n × unitInterval) = hatPsi hn y := hy.symm
    show K (Theta hn (q : IC n × unitInterval)) = f q
    rw [hq, Theta_psi hn y, hK0 y, hg_apply y, hsub]
  · intro x
    show K (Theta hn (x, 1)) ∈ A
    have hpair : Theta hn (x, 1) = ((Theta hn (x, 1)).1, (Theta hn (x, 1)).2) := rfl
    rcases Theta_top hn x with h | h
    · rw [hpair, hKb _ h _]
      exact hgb _ h
    · have hpair' : Theta hn (x, 1) = ((Theta hn (x, 1)).1, 1) := Prod.ext rfl h
      rw [hpair']
      exact hK1 _

end

end Work.Serre
