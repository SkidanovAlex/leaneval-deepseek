import Mathlib
import Submission.Work.StemsB.Fibrations
import Submission.Work.StemsB.exists_lift_rel
import Submission.Work.RatHurewicz.DomeMap
import Submission.Work.ThomBordism.TwoSet.ConeDescent
import Submission.Work.Serre.SweepDefs
import Submission.Work.Serre.sweepCube_bdry
import Submission.Work.RatHurewicz.retract_stdSimplex_cube

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Homotopic lifts of joined fibres

The main statement of this file is `Work.Serre.homotopicLiftsOfJoinedFibre`: for a Serre fibration
`p : E → B`, an `n`-simplex `σ` of the base and two lifts `l₁`, `l₂` of `σ` which are joined in the
fibre of `p` over a point `v` of the simplex, and such that the higher homotopy groups of that
fibre vanish up to degree `n`, there is a homotopy over `σ` from `l₁` to `l₂`.

The proof is the classical obstruction-theoretic one, carried out here for the standard simplex
rather than for a relative CW complex:

* the prism `Δⁿ × I` is a cone (with cone point the "vertical" segment over `v`) over the space
  `∂Δⁿ × I`; the prescribed data (on the two ends `Δⁿ × {0}`, `Δⁿ × {1}` and on the segment over
  `v`) lies on the "sub-cone" over the boundary of that test space;
* the lift is produced by the *sweep* `Work.Serre.Sweep` (proved for `∂Iⁿ` by the relative cube
  homotopy lifting property `Work.StemsB.exists_lift_rel`),
* and then read back on `Δⁿ × I` along the rays from `v`, using the coning lemma
  `Work.ThomBordism.TwoSet.ConeDescent` (whose "radius" structure is reproved here for an arbitrary
  point `v` of the cube in `vRad`/`vBpt`).
-/

open scoped Topology

namespace Work.Serre

noncomputable section

/-! ## A radial structure on the cube centred at an arbitrary point

For `v : Fin n → I` and `x : Fin n → I`, `vRad v x ∈ [0,1]` is the "coordinate radial" distance from
`v` to `x`: the largest `ρ` such that the point `v + ρ • (x - v)` (taken coordinatewise) still lies
in the cube when scaled *from* `x` *towards* `v`...  Concretely, `vRad` is the maximum over the
coordinates `i` of the "coordinate radius"
`max ((x i - v i)/(1 - v i)) ((v i - x i)/(v i))` (a term being omitted when the denominator
vanishes, which is exactly when the corresponding direction leaves the cube immediately).

The two properties used below are `vRad_eq_zero_iff` (`vRad v x = 0 ↔ x = v`) and
`vBpt_spec` (`v + vRad v x • (vBpt v x - v) = x` with `vBpt v x ∈ ∂Iⁿ`). -/

variable {n : ℕ}

/-- The `i`-th coordinate radius of `x` with respect to `v` (a nonnegative real number). -/
noncomputable def vRadC (v : Fin n → unitInterval) (x : Fin n → unitInterval) (i : Fin n) : ℝ :=
  max (if (v i : ℝ) < 1 then ((x i : ℝ) - (v i : ℝ)) / (1 - (v i : ℝ)) else 0)
      (if 0 < (v i : ℝ) then ((v i : ℝ) - (x i : ℝ)) / (v i : ℝ) else 0)

theorem vRadC_nonneg (v x : Fin n → unitInterval) (i : Fin n) : 0 ≤ vRadC v x i := by
  rw [vRadC]
  rcases le_total ((v i : ℝ)) ((x i : ℝ)) with h | h
  · refine le_max_of_le_left ?_
    by_cases h1 : (v i : ℝ) < 1
    · rw [if_pos h1]
      exact div_nonneg (by linarith) (by linarith)
    · rw [if_neg h1] <;> try norm_num
  · refine le_max_of_le_right ?_
    by_cases hv : 0 < (v i : ℝ)
    · rw [if_pos hv]
      exact div_nonneg (by linarith) (le_of_lt hv)
    · rw [if_neg hv] <;> try exact le_refl 0

theorem vRadC_le_one (v x : Fin n → unitInterval) (i : Fin n) : vRadC v x i ≤ 1 := by
  rw [vRadC]
  refine max_le ?_ ?_
  · by_cases h : (v i : ℝ) < 1
    · rw [if_pos h]
      have hx : (x i : ℝ) ≤ 1 := (x i).2.2
      rw [div_le_one (by linarith)]
      linarith
    · rw [if_neg h]; norm_num
  · by_cases h : 0 < (v i : ℝ)
    · rw [if_pos h]
      have hx : (0 : ℝ) ≤ (x i : ℝ) := (x i).2.1
      rw [div_le_one h]
      linarith
    · rw [if_neg h]; norm_num

theorem continuous_vRadC (v : Fin n → unitInterval) (i : Fin n) :
    Continuous (fun x : Fin n → unitInterval => vRadC v x i) := by
  unfold vRadC
  by_cases h1 : (v i : ℝ) < 1 <;> by_cases h2 : 0 < (v i : ℝ)
  · simp only [if_pos h1, if_pos h2]
    exact ((by fun_prop : Continuous fun x : Fin n → unitInterval =>
        ((x i : ℝ) - (v i : ℝ)) / (1 - (v i : ℝ)))).max
      (by fun_prop : Continuous fun x : Fin n → unitInterval =>
        ((v i : ℝ) - (x i : ℝ)) / (v i : ℝ))
  · simp only [if_pos h1, if_neg h2]
    exact (by fun_prop : Continuous fun x : Fin n → unitInterval =>
        ((x i : ℝ) - (v i : ℝ)) / (1 - (v i : ℝ))).max continuous_const
  · simp only [if_neg h1, if_pos h2]
    exact continuous_const.max (by fun_prop : Continuous fun x : Fin n → unitInterval =>
        ((v i : ℝ) - (x i : ℝ)) / (v i : ℝ))
  · simp only [if_neg h1, if_neg h2]
    exact continuous_const.max continuous_const


/-- The coordinate radial distance of `x` from `v`. -/
noncomputable def vRad (hn : 1 ≤ n) (v : Fin n → unitInterval) (x : Fin n → unitInterval) : ℝ :=
  (Finset.univ : Finset (Fin n)).sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => vRadC v x i)

theorem vRadC_le_vRad (hn : 1 ≤ n) (v x : Fin n → unitInterval) (i : Fin n) :
    vRadC v x i ≤ vRad hn v x :=
  Finset.le_sup' _ (Finset.mem_univ i)

theorem vRad_nonneg (hn : 1 ≤ n) (v x : Fin n → unitInterval) : 0 ≤ vRad hn v x := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => vRadC v x i)
  rw [vRad, hi]
  exact vRadC_nonneg v x i

theorem vRad_le_one (hn : 1 ≤ n) (v x : Fin n → unitInterval) : vRad hn v x ≤ 1 :=
  Finset.sup'_le _ _ (fun i _ => vRadC_le_one v x i)

theorem continuous_vRad (hn : 1 ≤ n) (v : Fin n → unitInterval) :
    Continuous (vRad hn v) :=
  Continuous.finset_sup'_apply (s := Finset.univ) (f := fun i x => vRadC v x i)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i _ => continuous_vRadC v i)

theorem vRad_eq_zero_iff (hn : 1 ≤ n) (v : Fin n → unitInterval) (x : Fin n → unitInterval) :
    vRad hn v x = 0 ↔ x = v := by
  constructor
  · intro h
    funext i
    have h1 : vRadC v x i = 0 := le_antisymm (h ▸ vRadC_le_vRad hn v x i) (vRadC_nonneg v x i)
    apply Subtype.ext
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hv : 0 < (v i : ℝ) := lt_of_le_of_lt (x i).2.1 hlt
      have hc : ((v i : ℝ) - (x i : ℝ)) / (v i : ℝ) ≤ vRadC v x i := by
        unfold vRadC; rw [if_pos hv]; exact le_max_right _ _
      have : 0 < ((v i : ℝ) - (x i : ℝ)) / (v i : ℝ) := div_pos (by linarith) hv
      rw [h1] at hc; linarith
    · have hv : (v i : ℝ) < 1 := lt_of_lt_of_le hgt (x i).2.2
      have hc : ((x i : ℝ) - (v i : ℝ)) / (1 - (v i : ℝ)) ≤ vRadC v x i := by
        unfold vRadC; rw [if_pos hv]; exact le_max_left _ _
      have : 0 < ((x i : ℝ) - (v i : ℝ)) / (1 - (v i : ℝ)) := div_pos (by linarith) (by linarith)
      rw [h1] at hc; linarith
  · intro hxv
    rw [hxv]
    refine le_antisymm ?_ (vRad_nonneg hn v v)
    rw [vRad]
    refine Finset.sup'_le _ _ (fun i _ => ?_)
    unfold vRadC
    have h1 : ((v i : ℝ) - (v i : ℝ)) / (1 - (v i : ℝ)) = 0 := by ring
    have h2 : ((v i : ℝ) - (v i : ℝ)) / (v i : ℝ) = 0 := by ring
    have key : (if (v i : ℝ) < 1 then ((v i : ℝ) - (v i : ℝ)) / (1 - (v i : ℝ)) else 0) = 0 := by
      by_cases hc : (v i : ℝ) < 1
      · rw [if_pos hc, h1]
      · rw [if_neg hc]
    have key2 : (if 0 < (v i : ℝ) then ((v i : ℝ) - (v i : ℝ)) / (v i : ℝ) else 0) = 0 := by
      by_cases hd : 0 < (v i : ℝ)
      · rw [if_pos hd, h2]
      · rw [if_neg hd]
    rw [key, key2]
    simp

theorem vRad_pos (hn : 1 ≤ n) {v x : Fin n → unitInterval} (hx : x ≠ v) : 0 < vRad hn v x :=
  lt_of_le_of_ne (vRad_nonneg hn v x) (fun h => hx ((vRad_eq_zero_iff hn v x).mp h.symm))

theorem vBpt_coord_mem (hn : 1 ≤ n) (v x : Fin n → unitInterval) (i : Fin n) :
    ((v i : ℝ) + ((x i : ℝ) - (v i : ℝ)) / vRad hn v x) ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hρ : vRad hn v x = 0
  · have hxv : x = v := (vRad_eq_zero_iff hn v x).mp hρ
    rw [hρ, hxv]
    constructor <;> simp [(v i).2.1, (v i).2.2]
  · have hρpos : 0 < vRad hn v x :=
      lt_of_le_of_ne (vRad_nonneg hn v x) (Ne.symm hρ)
    have hle : vRadC v x i ≤ vRad hn v x := vRadC_le_vRad hn v x i
    constructor
    · by_cases h : (x i : ℝ) ≤ (v i : ℝ)
      · by_cases hv : 0 < (v i : ℝ)
        · have hb : ((v i : ℝ) - (x i : ℝ)) / (v i : ℝ) ≤ vRadC v x i := by
            unfold vRadC; rw [if_pos hv]; exact le_max_right _ _
          have h1 : (v i : ℝ) - (x i : ℝ) ≤ vRad hn v x * (v i : ℝ) :=
            (div_le_iff₀ hv).mp (le_trans hb hle)
          have h3 : -(v i : ℝ) ≤ ((x i : ℝ) - (v i : ℝ)) / vRad hn v x := by
            rw [le_div_iff₀ hρpos]; linarith
          have hv' : (0 : ℝ) ≤ (v i : ℝ) := (v i).2.1
          linarith
        · have hv0 : (v i : ℝ) = 0 := le_antisymm (not_lt.mp hv) (v i).2.1
          have hx0 : (x i : ℝ) = 0 := le_antisymm (by linarith [h, hv0]) (x i).2.1
          rw [hv0, hx0]
          simp
      · push_neg at h
        have h3 : 0 ≤ ((x i : ℝ) - (v i : ℝ)) / vRad hn v x :=
          div_nonneg (by linarith) (le_of_lt hρpos)
        have hv' : (0 : ℝ) ≤ (v i : ℝ) := (v i).2.1
        linarith
    · by_cases h : (v i : ℝ) ≤ (x i : ℝ)
      · by_cases hv : (v i : ℝ) < 1
        · have hb : ((x i : ℝ) - (v i : ℝ)) / (1 - (v i : ℝ)) ≤ vRadC v x i := by
            unfold vRadC; rw [if_pos hv]; exact le_max_left _ _
          have h1 : (x i : ℝ) - (v i : ℝ) ≤ vRad hn v x * (1 - (v i : ℝ)) :=
            (div_le_iff₀ (by linarith)).mp (le_trans hb hle)
          have h3 : ((x i : ℝ) - (v i : ℝ)) / vRad hn v x ≤ 1 - (v i : ℝ) := by
            rw [div_le_iff₀ hρpos]; linarith
          have hv' : (v i : ℝ) ≤ 1 := (v i).2.2
          linarith
        · have hv1 : (v i : ℝ) = 1 := le_antisymm (v i).2.2 (not_lt.mp hv)
          have hx1 : (x i : ℝ) = 1 := le_antisymm (x i).2.2 (by linarith [h, hv1])
          rw [hv1, hx1]
          simp
      · push_neg at h
        have h3 : ((x i : ℝ) - (v i : ℝ)) / vRad hn v x ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hρpos)
        have hv' : (v i : ℝ) ≤ 1 := (v i).2.2
        linarith

/-- The boundary point obtained from `x` by pushing radially away from `v`. -/
noncomputable def vBpt (hn : 1 ≤ n) (v : Fin n → unitInterval) (x : Fin n → unitInterval) :
    Fin n → unitInterval :=
  fun i => ⟨(v i : ℝ) + ((x i : ℝ) - (v i : ℝ)) / vRad hn v x, vBpt_coord_mem hn v x i⟩

theorem vBpt_spec (hn : 1 ≤ n) (v x : Fin n → unitInterval) (hx : vRad hn v x ≠ 0) :
    ∀ i : Fin n, ((v i : ℝ) + vRad hn v x * (((vBpt hn v x) i : ℝ) - (v i : ℝ)) = (x i : ℝ)) := by
  intro i
  have h : ((vBpt hn v x) i : ℝ) = (v i : ℝ) + ((x i : ℝ) - (v i : ℝ)) / vRad hn v x := rfl
  rw [h]
  field_simp
  ring


theorem vBpt_mem_boundary (hn : 1 ≤ n) (v x : Fin n → unitInterval) (hx : vRad hn v x ≠ 0) :
    vBpt hn v x ∈ Cube.boundary (Fin n) := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ)
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩ (fun i => vRadC v x i)
  have hρpos : 0 < vRad hn v x := lt_of_le_of_ne (vRad_nonneg hn v x) (Ne.symm hx)
  refine ⟨i, ?_⟩
  set A : ℝ := (if (v i : ℝ) < 1 then ((x i : ℝ) - (v i : ℝ)) / (1 - (v i : ℝ)) else 0) with hA
  set B : ℝ := (if 0 < (v i : ℝ) then ((v i : ℝ) - (x i : ℝ)) / (v i : ℝ) else 0) with hB
  have hC : vRadC v x i = max A B := rfl
  have hρ : vRad hn v x = max A B := by rw [← hC]; exact hi
  have hcoord : ((vBpt hn v x) i : ℝ) = (v i : ℝ) + ((x i : ℝ) - (v i : ℝ)) / vRad hn v x := rfl
  rcases le_total B A with h | h
  · have hAeq : A = vRad hn v x := by rw [hρ, max_eq_left h]
    have hAne : A ≠ 0 := by rw [hAeq]; exact ne_of_gt hρpos
    have hv1 : (v i : ℝ) < 1 := by
      by_contra hc
      rw [hA, if_neg hc] at hAne
      exact hAne rfl
    have hval : ((x i : ℝ) - (v i : ℝ)) / (1 - (v i : ℝ)) = vRad hn v x := by
      rw [← hAeq, hA, if_pos hv1]
    right
    apply Subtype.ext
    rw [hcoord]
    have hxsub : (x i : ℝ) - (v i : ℝ) = vRad hn v x * (1 - (v i : ℝ)) := by
      have hne : (1 : ℝ) - (v i : ℝ) ≠ 0 := by linarith
      rw [← hval, div_mul_cancel₀ _ hne]
    rw [hxsub]
    field_simp
    norm_num
  · have hBeq : B = vRad hn v x := by rw [hρ, max_eq_right h]
    have hBne : B ≠ 0 := by rw [hBeq]; exact ne_of_gt hρpos
    have hv0 : 0 < (v i : ℝ) := by
      by_contra hc
      rw [hB, if_neg hc] at hBne
      exact hBne rfl
    have hval : ((v i : ℝ) - (x i : ℝ)) / (v i : ℝ) = vRad hn v x := by
      rw [← hBeq, hB, if_pos hv0]
    left
    apply Subtype.ext
    rw [hcoord]
    have hxsub : (v i : ℝ) - (x i : ℝ) = vRad hn v x * (v i : ℝ) := by
      rw [← hval, div_mul_cancel₀ _ (ne_of_gt hv0)]
    rw [show (x i : ℝ) = (v i : ℝ) - vRad hn v x * (v i : ℝ) from by linarith]
    field_simp
    norm_num

theorem continuous_vBpt (hn : 1 ≤ n) (v : Fin n → unitInterval) :
    Continuous (fun q : {x : Fin n → unitInterval // vRad hn v x ≠ 0} => vBpt hn v q.1) := by
  refine continuous_pi (fun i => ?_)
  have hfun : (fun q : {x : Fin n → unitInterval // vRad hn v x ≠ 0} => vBpt hn v q.1 i)
      = fun q => (⟨(v i : ℝ) + ((q.1 i : ℝ) - (v i : ℝ)) / vRad hn v q.1,
          vBpt_coord_mem hn v q.1 i⟩ : unitInterval) := rfl
  rw [hfun]
  refine Continuous.subtype_mk ?_ _
  have hden : Continuous fun q : {x : Fin n → unitInterval // vRad hn v x ≠ 0} =>
      vRad hn v q.1 := (continuous_vRad hn v).comp continuous_subtype_val
  have hnum : Continuous fun q : {x : Fin n → unitInterval // vRad hn v x ≠ 0} =>
      ((q.1 i : unitInterval) : ℝ) :=
    (continuous_subtype_val : Continuous fun z : unitInterval => (z : ℝ)).comp
      ((continuous_apply i).comp continuous_subtype_val)
  exact continuous_const.add ((hnum.sub continuous_const).div hden (fun q => q.2))

/-- **Coning off a homotopy ending at a constant, for the radial structure centred at an arbitrary
point `v` of the cube.**  If `H : ∂Iⁿ × I → Y` is a homotopy with `H (·, 1)` constantly `y₀`, then
the "cone formula" `x ↦ H (vBpt x, 1 - vRad x)` is continuous on the cube; its value at `v` is
`y₀`, and away from `v` it is the stated formula. -/
theorem vConeDescent (hn : 1 ≤ n) {Y : Type} [TopologicalSpace Y] {v : Fin n → unitInterval}
    {y₀ : Y} (H : C(↥(Cube.boundary (Fin n)) × unitInterval, Y))
    (hH : ∀ z : ↥(Cube.boundary (Fin n)), H (z, 1) = y₀) :
    ∃ Ψ : C(Fin n → unitInterval, Y), Ψ v = y₀ ∧
      ∀ (x : Fin n → unitInterval) (hx : vRad hn v x ≠ 0),
      Ψ x = H (⟨vBpt hn v x, vBpt_mem_boundary hn v x hx⟩,
        ⟨1 - vRad hn v x, ⟨by have h1 := vRad_le_one hn v x; linarith,
          by have h0 := vRad_nonneg hn v x; linarith⟩⟩) := by
  classical
  have hmem : ∀ x : Fin n → unitInterval, vRad hn v x ≠ 0 →
      (1 - vRad hn v x : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
    intro x hx
    have h0 := vRad_nonneg hn v x
    have h1 := vRad_le_one hn v x
    exact ⟨by linarith, by linarith⟩
  let Ψfun : (Fin n → unitInterval) → Y := fun x =>
    if h : vRad hn v x = 0 then y₀
    else H (⟨vBpt hn v x, vBpt_mem_boundary hn v x h⟩, ⟨1 - vRad hn v x, hmem x h⟩)
  have hopen : IsOpen {x : Fin n → unitInterval | vRad hn v x ≠ 0} :=
    (isOpen_ne (x := (0:ℝ))).preimage (continuous_vRad hn v)
  let gamma : {x : Fin n → unitInterval // vRad hn v x ≠ 0} →
      ({x : Fin n → unitInterval // x ∈ Cube.boundary (Fin n)} × unitInterval) :=
    fun q => (⟨vBpt hn v q.1, vBpt_mem_boundary hn v q.1 q.2⟩, ⟨1 - vRad hn v q.1, hmem q.1 q.2⟩)
  have hgamma : Continuous gamma := by
    refine Continuous.prodMk ?_ ?_
    · refine continuous_induced_rng.mpr ?_
      show Continuous fun q : {x : Fin n → unitInterval // vRad hn v x ≠ 0} => vBpt hn v q.1
      exact continuous_vBpt hn v
    · refine continuous_induced_rng.mpr ?_
      show Continuous fun q : {x : Fin n → unitInterval // vRad hn v x ≠ 0} =>
        (1 - vRad hn v q.1 : ℝ)
      exact continuous_const.sub ((continuous_vRad hn v).comp continuous_subtype_val)
  have hcontOn : ContinuousOn Ψfun {x : Fin n → unitInterval | vRad hn v x ≠ 0} := by
    rw [continuousOn_iff_continuous_domRestrict]
    have h2 : ∀ q : {x : Fin n → unitInterval // vRad hn v x ≠ 0}, Ψfun q.1 = H (gamma q) := by
      intro q
      simp only [Ψfun, dif_neg q.2]
      rfl
    exact (H.continuous.comp hgamma).congr (fun q => (h2 q).symm)
  have hcont_off : ∀ x, vRad hn v x ≠ 0 → ContinuousAt Ψfun x := fun x hx =>
    hcontOn.continuousAt (hopen.mem_nhds hx)
  have hvcen : vRad hn v v = 0 := (vRad_eq_zero_iff hn v v).mpr rfl
  have hcen0 : Ψfun v = y₀ := by
    simp only [Ψfun]; rw [dif_pos hvcen]
  have hcont_cen : ContinuousAt Ψfun v := by
    rw [ContinuousAt, hcen0, Filter.tendsto_def]
    intro V hV
    obtain ⟨s₀, hs₀, hV'⟩ := Work.ThomBordism.TwoSet.uniform_conv hn H hH V hV
    have h1s : (0:ℝ) < 1 - s₀ := by linarith
    have hnb : ({x : Fin n → unitInterval | vRad hn v x < 1 - s₀}) ∈ 𝓝 v := by
      refine IsOpen.mem_nhds (isOpen_lt (continuous_vRad hn v) continuous_const) ?_
      show vRad hn v v < 1 - s₀
      rw [hvcen]; exact h1s
    refine Filter.mem_of_superset hnb ?_
    intro x hx
    show Ψfun x ∈ V
    by_cases h0 : vRad hn v x = 0
    · have hxc : Ψfun x = y₀ := by simp only [Ψfun]; rw [dif_pos h0]
      rw [hxc]
      exact mem_of_mem_nhds hV
    · have hsp : s₀ < (1 - vRad hn v x) := by
        have hx' : vRad hn v x < 1 - s₀ := hx
        linarith
      have := hV' ⟨vBpt hn v x, vBpt_mem_boundary hn v x h0⟩ ⟨1 - vRad hn v x, hmem x h0⟩ hsp
      simpa only [Ψfun, dif_neg h0] using this
  have hΨcont : Continuous Ψfun := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : vRad hn v x = 0
    · rw [(vRad_eq_zero_iff hn v x).mp hx]
      exact hcont_cen
    · exact hcont_off x hx
  refine ⟨⟨Ψfun, hΨcont⟩, hcen0, fun x hx => ?_⟩
  show (if h : vRad hn v x = 0 then y₀
    else H (⟨vBpt hn v x, vBpt_mem_boundary hn v x h⟩, ⟨1 - vRad hn v x, hmem x h⟩)) = _
  rw [dif_neg hx]

/-- Scaling a point of the cube towards `v` by `s ∈ [0,1]`. -/
noncomputable def vScale (v : Fin n → unitInterval) (s : unitInterval)
    (z : Fin n → unitInterval) : Fin n → unitInterval :=
  fun i => ⟨(v i : ℝ) + (s : ℝ) * ((z i : ℝ) - (v i : ℝ)), by
    have hz := (z i).2
    have hv := (v i).2
    have hs := (s : unitInterval).2
    constructor <;> nlinarith [hz.1, hz.2, hv.1, hv.2, hs.1, hs.2]⟩

theorem vScale_coe (v : Fin n → unitInterval) (s : unitInterval) (z : Fin n → unitInterval)
    (i : Fin n) :
    ((vScale v s z i : unitInterval) : ℝ) = (v i : ℝ) + (s : ℝ) * ((z i : ℝ) - (v i : ℝ)) :=
  rfl

theorem vScale_zero (v : Fin n → unitInterval) (z : Fin n → unitInterval) : vScale v 0 z = v := by
  funext i
  apply Subtype.ext
  rw [vScale_coe, show ((0 : unitInterval) : ℝ) = 0 from rfl]
  ring

theorem vScale_one (v : Fin n → unitInterval) (z : Fin n → unitInterval) : vScale v 1 z = z := by
  funext i
  apply Subtype.ext
  rw [vScale_coe, show ((1 : unitInterval) : ℝ) = 1 from rfl]
  ring

theorem continuous_vScale (v : Fin n → unitInterval) :
    Continuous (fun p : unitInterval × (Fin n → unitInterval) => vScale v p.1 p.2) := by
  refine continuous_pi (fun i => ?_)
  refine Continuous.subtype_mk ?_ _
  have h1 : Continuous fun p : unitInterval × (Fin n → unitInterval) => ((p.1 : unitInterval) : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have h2 : Continuous fun p : unitInterval × (Fin n → unitInterval) =>
      ((p.2 i : unitInterval) : ℝ) :=
    (continuous_subtype_val : Continuous fun z : unitInterval => (z : ℝ)).comp
      ((continuous_apply i).comp continuous_snd)
  exact continuous_const.add (h1.mul (h2.sub continuous_const))

theorem continuous_vScale_right (hn : 1 ≤ n) (v x : Fin n → unitInterval) (hx : vRad hn v x ≠ 0) :
    vScale v ⟨vRad hn v x, ⟨vRad_nonneg hn v x, vRad_le_one hn v x⟩⟩ (vBpt hn v x) = x := by
  funext i
  apply Subtype.ext
  rw [vScale_coe]
  exact vBpt_spec hn v x hx i

/-- The reflection `u ↦ 1 - u` of the unit interval. -/
noncomputable def unitRefl (u : unitInterval) : unitInterval :=
  ⟨1 - (u : ℝ), ⟨by have := u.2.2; linarith, by have := u.2.1; linarith⟩⟩

theorem unitRefl_coe (u : unitInterval) : ((unitRefl u : unitInterval) : ℝ) = 1 - (u : ℝ) := rfl

theorem unitRefl_zero : unitRefl 0 = 1 := by
  apply Subtype.ext
  rw [unitRefl_coe]
  norm_num

theorem unitRefl_one : unitRefl 1 = 0 := by
  apply Subtype.ext
  rw [unitRefl_coe]
  norm_num

theorem unitRefl_invol (u : unitInterval) : unitRefl (unitRefl u) = u := by
  apply Subtype.ext
  rw [unitRefl_coe, unitRefl_coe]
  norm_num

theorem unitRefl_sub_one (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    unitRefl ⟨1 - a, ⟨by linarith, by linarith⟩⟩ = ⟨a, ⟨h0, h1⟩⟩ := by
  apply Subtype.ext
  rw [unitRefl_coe]
  norm_num

theorem continuous_unitRefl : Continuous unitRefl := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_const.sub continuous_subtype_val

section Cube

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- **The cube form of the main statement.**  For a Serre fibration `p`, a base map
`sg : Iⁿ → B`, two lifts `l₁`, `l₂` of `sg` which are joined in the fibre over `v`, and the sweep
property of the boundary test space, there is a homotopy over `sg` from `l₁` to `l₂`.

The parametrisation `(z,s) ↦ vScale v s z` identifies the cube with the "prism" `∂Iⁿ × I`; the
prescribed data (two ends and the segment over `v`, i.e. the joinedness) becomes an instance of
`Work.Serre.Sweep` on `∂Iⁿ × I × I`, whose output is read back along the rays from `v` by
`vConeDescent`. -/
theorem exists_homotopy_cube (p : C(E, B)) (n : ℕ)
    (hSweep : Sweep (↥(Cube.boundary (Fin n))) E B p)
    (sg : C(Fin n → unitInterval, B))
    (l₁ l₂ : C(Fin n → unitInterval, E))
    (h₁ : p.comp l₁ = sg) (h₂ : p.comp l₂ = sg)
    (v : Fin n → unitInterval)
    (hjoin : Joined (⟨l₁ v, by rw [Set.mem_preimage]; exact congrFun (congrArg DFunLike.coe h₁) v⟩ :
        ↥(p ⁻¹' {sg v}))
      (⟨l₂ v, by rw [Set.mem_preimage]; exact congrFun (congrArg DFunLike.coe h₂) v⟩ :
        ↥(p ⁻¹' {sg v}))) :
    ∃ H : C((Fin n → unitInterval) × unitInterval, E),
      (∀ y, H (y, 0) = l₁ y) ∧ (∀ y, H (y, 1) = l₂ y) ∧
      p.comp H = sg.comp (ContinuousMap.fst :
        C((Fin n → unitInterval) × unitInterval, Fin n → unitInterval)) := by
  classical
  let γ : Path _ _ := hjoin.somePath
  let γE : C(unitInterval, E) := ⟨fun t => (γ t : E), continuous_subtype_val.comp γ.continuous⟩
  have hγE0 : γE 0 = l₁ v := congrArg Subtype.val γ.source'
  have hγE1 : γE 1 = l₂ v := congrArg Subtype.val γ.target'
  have hγp : ∀ t : unitInterval, p (γE t) = sg v := fun t => (γ t).2
  by_cases hn0 : n = 0
  · -- ## the case `n = 0`: the whole domain is prescribed
    haveI : IsEmpty (Fin n) := by rw [hn0]; infer_instance
    haveI : Subsingleton (Fin n → unitInterval) :=
      ⟨fun f g => funext fun i => (IsEmpty.false i).elim⟩
    refine ⟨⟨fun q => γE q.2, γE.continuous.comp continuous_snd⟩, ?_, ?_, ?_⟩
    · intro y
      have hy : y = v := Subsingleton.elim y v
      rw [hy]
      show γE 0 = l₁ v
      rw [hγE0]
    · intro y
      have hy : y = v := Subsingleton.elim y v
      rw [hy]
      show γE 1 = l₂ v
      rw [hγE1]
    · ext q
      have hy : q.1 = v := Subsingleton.elim q.1 v
      show p (γE q.2) = sg q.1
      rw [hy]
      exact hγp q.2
  · -- ## the main case `n ≥ 1`
    have hn : 1 ≤ n := Nat.pos_of_ne_zero hn0
    -- the parametrisation of the cube by the prism over its boundary
    let Ψ₁ : C((Fin n → unitInterval) × unitInterval, Fin n → unitInterval) :=
      ⟨fun q => vScale v q.2 q.1,
        (continuous_vScale v).comp (continuous_snd.prodMk continuous_fst)⟩
    have hΨ₁ : ∀ (z : Fin n → unitInterval) (s : unitInterval), Ψ₁ (z, s) = vScale v s z :=
      fun z s => rfl
    let ψ : C(↥(Cube.boundary (Fin n)) × unitInterval, (Fin n → unitInterval) × unitInterval) :=
      ⟨fun q => (q.1.1, q.2),
        (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd⟩
    have hψ : ∀ (z : ↥(Cube.boundary (Fin n))) (s : unitInterval),
        ψ (z, s) = (z.1, s) := fun z s => rfl
    let Θ : C(↥(Cube.boundary (Fin n)) × unitInterval, Fin n → unitInterval) := Ψ₁.comp ψ
    have hΘ : ∀ (z : ↥(Cube.boundary (Fin n))) (s : unitInterval),
        Θ (z, s) = vScale v s z.1 := by
      intro z s
      show Ψ₁ (ψ (z, s)) = vScale v s z.1
      rw [hψ, hΨ₁]
    -- the base map and the prescribed lifts on the prism
    have hcontQs : Continuous fun q : ↥(Cube.boundary (Fin n)) × unitInterval × unitInterval =>
        (q.1, q.2.1) :=
      continuous_fst.prodMk (continuous_fst.comp continuous_snd)
    let Hbase : C(↥(Cube.boundary (Fin n)) × unitInterval × unitInterval, B) :=
      ⟨fun q => sg (Θ (q.1, q.2.1)), sg.continuous.comp (Θ.continuous.comp hcontQs)⟩
    have hHbase : ∀ (z : ↥(Cube.boundary (Fin n))) (s t : unitInterval),
        Hbase (z, s, t) = sg (vScale v s z.1) := by
      intro z s t
      show sg (Θ (z, s)) = sg (vScale v s z.1)
      rw [hΘ]
    let f₀ : C(↥(Cube.boundary (Fin n)) × unitInterval, E) :=
      ⟨fun q => γE q.2, γE.continuous.comp continuous_snd⟩
    let f₁ : C(↥(Cube.boundary (Fin n)) × unitInterval, E) :=
      ⟨fun q => l₁ (Θ q), l₁.continuous.comp Θ.continuous⟩
    let f₂ : C(↥(Cube.boundary (Fin n)) × unitInterval, E) :=
      ⟨fun q => l₂ (Θ q), l₂.continuous.comp Θ.continuous⟩
    have hf₀ : p.comp f₀ = Hbase.comp ⟨fun q : ↥(Cube.boundary (Fin n)) × unitInterval =>
        (q.1, 0, q.2), continuous_fst.prodMk (continuous_const.prodMk continuous_snd)⟩ := by
      ext q
      show p (γE q.2) = Hbase (q.1, 0, q.2)
      rw [hγp q.2, hHbase q.1 0 q.2, vScale_zero]
    have hf₁ : p.comp f₁ = Hbase.comp ⟨fun q : ↥(Cube.boundary (Fin n)) × unitInterval =>
        (q.1, q.2, 0), continuous_fst.prodMk (continuous_snd.prodMk continuous_const)⟩ := by
      ext q
      show p (l₁ (Θ (q.1, q.2))) = Hbase (q.1, q.2, 0)
      rw [show p (l₁ (Θ (q.1, q.2))) = sg (Θ (q.1, q.2)) from
        congrFun (congrArg DFunLike.coe h₁) (Θ (q.1, q.2))]
      rw [hHbase q.1 q.2 0, hΘ]
    have hf₂ : p.comp f₂ = Hbase.comp ⟨fun q : ↥(Cube.boundary (Fin n)) × unitInterval =>
        (q.1, q.2, 1), continuous_fst.prodMk (continuous_snd.prodMk continuous_const)⟩ := by
      ext q
      show p (l₂ (Θ (q.1, q.2))) = Hbase (q.1, q.2, 1)
      rw [show p (l₂ (Θ (q.1, q.2))) = sg (Θ (q.1, q.2)) from
        congrFun (congrArg DFunLike.coe h₂) (Θ (q.1, q.2))]
      rw [hHbase q.1 q.2 1, hΘ]
    have hc₀ : ∀ z : ↥(Cube.boundary (Fin n)), f₀ (z, 0) = f₁ (z, 0) := by
      intro z
      show γE 0 = l₁ (Θ (z, 0))
      rw [hγE0, hΘ, vScale_zero]
    have hc₁ : ∀ z : ↥(Cube.boundary (Fin n)), f₀ (z, 1) = f₂ (z, 0) := by
      intro z
      show γE 1 = l₂ (Θ (z, 0))
      rw [hγE1, hΘ, vScale_zero]
    obtain ⟨G, hG, hG₀, hG₁, hG₂⟩ := hSweep Hbase f₀ hf₀ f₁ hf₁ f₂ hf₂ hc₀ hc₁
    -- * the coning: curry the prism lift (with the `s`-coordinate reversed)
    have hcontGcur : Continuous fun q : (↥(Cube.boundary (Fin n)) × unitInterval) × unitInterval =>
        (q.1.1, unitRefl q.1.2, q.2) := by
      have hz : Continuous fun q : (↥(Cube.boundary (Fin n)) × unitInterval) × unitInterval =>
          (q.1.1 : ↥(Cube.boundary (Fin n))) := by fun_prop
      have hu : Continuous fun q : (↥(Cube.boundary (Fin n)) × unitInterval) × unitInterval =>
          (q.1.2 : unitInterval) := by fun_prop
      have ht : Continuous fun q : (↥(Cube.boundary (Fin n)) × unitInterval) × unitInterval =>
          (q.2 : unitInterval) := by fun_prop
      exact hz.prodMk ((continuous_unitRefl.comp hu).prodMk ht)
    let Gcur : C((↥(Cube.boundary (Fin n)) × unitInterval) × unitInterval, E) :=
      ⟨fun q => G (q.1.1, unitRefl q.1.2, q.2), G.continuous.comp hcontGcur⟩
    have hGcur : ∀ (z : ↥(Cube.boundary (Fin n))) (u t : unitInterval),
        Gcur ((z, u), t) = G (z, unitRefl u, t) := fun z u t => rfl
    let Hcurl : C(↥(Cube.boundary (Fin n)) × unitInterval, C(unitInterval, E)) := Gcur.curry
    have hHcurl_one : ∀ z : ↥(Cube.boundary (Fin n)), Hcurl (z, 1) = γE := by
      intro z
      ext t
      rw [ContinuousMap.curry_apply]
      show G (z, unitRefl 1, t) = γE t
      rw [unitRefl_one, hG₀ z t]
      rfl
    obtain ⟨Ψ, hΨv, hΨ⟩ := vConeDescent hn Hcurl hHcurl_one
    -- * the descended homotopy
    have hcontH : Continuous fun q : (Fin n → unitInterval) × unitInterval => Ψ q.1 q.2 :=
      continuous_eval.comp ((Ψ.continuous.comp continuous_fst).prodMk continuous_snd)
    let H : C((Fin n → unitInterval) × unitInterval, E) := ⟨fun q => Ψ q.1 q.2, hcontH⟩
    have hHv : ∀ t : unitInterval, H (v, t) = γE t := by
      intro t
      show Ψ v t = γE t
      rw [hΨv]
    have hval : ∀ (x : Fin n → unitInterval) (hx : vRad hn v x ≠ 0) (t : unitInterval),
        H (x, t) = G (⟨vBpt hn v x, vBpt_mem_boundary hn v x hx⟩,
          ⟨vRad hn v x, ⟨vRad_nonneg hn v x, vRad_le_one hn v x⟩⟩, t) := by
      intro x hx t
      have h1 : Ψ x = Hcurl (⟨vBpt hn v x, vBpt_mem_boundary hn v x hx⟩,
          ⟨1 - vRad hn v x, ⟨by have h2 := vRad_le_one hn v x; linarith,
            by have h0 := vRad_nonneg hn v x; linarith⟩⟩) := hΨ x hx
      have h2 : Hcurl (⟨vBpt hn v x, vBpt_mem_boundary hn v x hx⟩,
          ⟨1 - vRad hn v x, ⟨by linarith [vRad_le_one hn v x],
            by linarith [vRad_nonneg hn v x]⟩⟩)
          = ⟨fun t' => G (⟨vBpt hn v x, vBpt_mem_boundary hn v x hx⟩,
              ⟨vRad hn v x, ⟨vRad_nonneg hn v x, vRad_le_one hn v x⟩⟩, t'), by fun_prop⟩ := by
        ext t'
        rw [ContinuousMap.curry_apply]
        show G (⟨vBpt hn v x, _⟩, unitRefl ⟨1 - vRad hn v x, _⟩, t') = _
        rw [unitRefl_sub_one (vRad hn v x) (vRad_nonneg hn v x) (vRad_le_one hn v x)]
        rfl
      show Ψ x t = _
      rw [h1, h2]
      rfl
    refine ⟨H, ?_, ?_, ?_⟩
    · intro y
      by_cases hy : vRad hn v y = 0
      · have hyv : y = v := (vRad_eq_zero_iff hn v y).mp hy
        rw [hyv, hHv 0, hγE0]
      · rw [hval y hy 0, hG₁]
        change l₁ (Θ (⟨vBpt hn v y, vBpt_mem_boundary hn v y hy⟩,
          ⟨vRad hn v y, ⟨vRad_nonneg hn v y, vRad_le_one hn v y⟩⟩)) = l₁ y
        rw [hΘ]
        exact congrArg l₁ (continuous_vScale_right hn v y hy)
    · intro y
      by_cases hy : vRad hn v y = 0
      · have hyv : y = v := (vRad_eq_zero_iff hn v y).mp hy
        rw [hyv, hHv 1, hγE1]
      · rw [hval y hy 1, hG₂]
        change l₂ (Θ (⟨vBpt hn v y, vBpt_mem_boundary hn v y hy⟩,
          ⟨vRad hn v y, ⟨vRad_nonneg hn v y, vRad_le_one hn v y⟩⟩)) = l₂ y
        rw [hΘ]
        exact congrArg l₂ (continuous_vScale_right hn v y hy)
    · ext q
      show p (H (q.1, q.2)) = sg q.1
      by_cases hy : vRad hn v q.1 = 0
      · have hyv : q.1 = v := (vRad_eq_zero_iff hn v q.1).mp hy
        rw [hyv]
        show p (Ψ v q.2) = sg v
        rw [hΨv]
        exact hγp q.2
      · rw [hval q.1 hy q.2]
        rw [show p (G (⟨vBpt hn v q.1, vBpt_mem_boundary hn v q.1 hy⟩,
            ⟨vRad hn v q.1, ⟨vRad_nonneg hn v q.1, vRad_le_one hn v q.1⟩⟩, q.2))
            = Hbase (⟨vBpt hn v q.1, vBpt_mem_boundary hn v q.1 hy⟩,
              ⟨vRad hn v q.1, ⟨vRad_nonneg hn v q.1, vRad_le_one hn v q.1⟩⟩, q.2) from
          congrFun (congrArg DFunLike.coe hG) (⟨vBpt hn v q.1, vBpt_mem_boundary hn v q.1 hy⟩,
            ⟨vRad hn v q.1, ⟨vRad_nonneg hn v q.1, vRad_le_one hn v q.1⟩⟩, q.2)]
        rw [hHbase]
        exact congrArg sg (continuous_vScale_right hn v q.1 hy)

end Cube

/-- **Homotopic lifts of joined fibres.**  Let `p : E → B` be a Serre fibration, let `σ` be an
`n`-simplex of `B`, and let `l₁`, `l₂` be two lifts of `σ` to `E` whose values at a point `v` of
the simplex are joined by a path in the fibre `p ⁻¹' {σ v}`.  If the fibre `p ⁻¹' {σ v}` has
vanishing homotopy groups in degrees `1, …, n`, then `l₁` and `l₂` are homotopic over `σ` (i.e. by
a homotopy whose base projection is the constant homotopy at `σ`).

The proof transports the statement to the cube via the retraction
`Work.RatHurewicz.retract_stdSimplex_cube` and applies the cube form `exists_homotopy_cube`. -/
theorem homotopicLiftsOfJoinedFibre {E B : Type} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (hp : Work.StemsB.IsSerreFibration p) (n : ℕ)
    (σ : C(↥(stdSimplex ℝ (Fin (n+1))), B))
    (l₁ l₂ : C(↥(stdSimplex ℝ (Fin (n+1))), E))
    (h₁ : p.comp l₁ = σ) (h₂ : p.comp l₂ = σ)
    (v : ↥(stdSimplex ℝ (Fin (n+1))))
    (hjoin : Joined (⟨l₁ v, by rw [Set.mem_preimage]; exact congrFun (congrArg DFunLike.coe h₁) v⟩ :
        ↥(p ⁻¹' {σ v}))
      (⟨l₂ v, by rw [Set.mem_preimage]; exact congrFun (congrArg DFunLike.coe h₂) v⟩ :
        ↥(p ⁻¹' {σ v})))
    (htriv : ∀ (i : ℕ), 1 ≤ i → i ≤ n → ∀ x : ↥(p ⁻¹' {σ v}),
      Subsingleton (HomotopyGroup (Fin i) (↥(p ⁻¹' {σ v})) x)) :
    ∃ H : C(↥(stdSimplex ℝ (Fin (n+1))) × unitInterval, E),
      (∀ y, H (y, 0) = l₁ y) ∧ (∀ y, H (y, 1) = l₂ y) ∧
      p.comp H = σ.comp (ContinuousMap.fst : C(↥(stdSimplex ℝ (Fin (n+1))) × unitInterval, ↥(stdSimplex ℝ (Fin (n+1))))) := by
  -- The standard simplex is a retract of the cube `I^{n+1}`.
  obtain ⟨i, r, hri⟩ := Work.RatHurewicz.retract_stdSimplex_cube n
  have hri' : ∀ x, r (i x) = x := fun x => congrFun (congrArg DFunLike.coe hri) x
  -- The three-face lifting property of the boundary of the cube, for a Serre fibration.
  have hSweep : Sweep (↥(Cube.boundary (Fin (n + 1)))) E B p :=
    (Work.Serre.sweepCube_bdry p hp).2 (n + 1)
  -- The two fibre points over `σ v`, joined by hypothesis.
  let a₁ : ↥(p ⁻¹' ({σ v} : Set B)) :=
    ⟨l₁ v, by rw [Set.mem_preimage]; exact congrFun (congrArg DFunLike.coe h₁) v⟩
  let a₂ : ↥(p ⁻¹' ({σ v} : Set B)) :=
    ⟨l₂ v, by rw [Set.mem_preimage]; exact congrFun (congrArg DFunLike.coe h₂) v⟩
  have hjoin₂ : Joined a₁ a₂ := hjoin
  -- The corresponding fibre points over `(σ ∘ r) (i v)`, where the cube data lives.
  let b₁ : ↥(p ⁻¹' ({σ (r (i v))} : Set B)) :=
    ⟨(l₁.comp r) (i v), by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact congrFun (congrArg DFunLike.coe h₁) (r (i v))⟩
  let b₂ : ↥(p ⁻¹' ({σ (r (i v))} : Set B)) :=
    ⟨(l₂.comp r) (i v), by
      rw [Set.mem_preimage, Set.mem_singleton_iff]
      exact congrFun (congrArg DFunLike.coe h₂) (r (i v))⟩
  -- `r (i v) = v`, so the two fibres have the same underlying points: the identity of `E` induces
  -- a continuous map between them, along which the joinedness transports.
  have hfib : ∀ x : ↥(p ⁻¹' ({σ v} : Set B)), p x.1 = σ v := fun x => by
    have hx := x.2
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    exact hx
  have hFprop : ∀ x : ↥(p ⁻¹' ({σ v} : Set B)), x.1 ∈ p ⁻¹' ({σ (r (i v))} : Set B) := fun x => by
    rw [Set.mem_preimage, Set.mem_singleton_iff]
    rw [hri' v]
    exact hfib x
  let Ffun : ↥(p ⁻¹' ({σ v} : Set B)) → ↥(p ⁻¹' ({σ (r (i v))} : Set B)) :=
    fun x => ⟨x.1, hFprop x⟩
  have hFcont : Continuous Ffun :=
    Continuous.subtype_mk continuous_subtype_val hFprop
  have hjoin' : Joined b₁ b₂ := by
    have hba : b₁ = Ffun a₁ := by
      apply Subtype.ext
      show l₁ (r (i v)) = l₁ v
      rw [hri' v]
    have hbb : b₂ = Ffun a₂ := by
      apply Subtype.ext
      show l₂ (r (i v)) = l₂ v
      rw [hri' v]
    exact ⟨Path.cast ((hjoin₂.map hFcont).somePath) hba hbb⟩
  -- The two lifts of `σ ∘ r`.
  have h₁' : p.comp (l₁.comp r) = σ.comp r := by rw [← ContinuousMap.comp_assoc, h₁]
  have h₂' : p.comp (l₂.comp r) = σ.comp r := by rw [← ContinuousMap.comp_assoc, h₂]
  -- Apply the cube form.
  obtain ⟨H', hH'₀, hH'₁, hH'p⟩ :=
    exists_homotopy_cube p (n + 1) hSweep (σ.comp r) (l₁.comp r) (l₂.comp r) h₁' h₂' (i v)
      hjoin'
  -- Transport the homotopy back along the retraction.
  let ψ : C(↥(stdSimplex ℝ (Fin (n+1))) × unitInterval,
      (Fin (n + 1) → unitInterval) × unitInterval) :=
    ⟨fun q => (i q.1, q.2), (i.continuous.comp continuous_fst).prodMk continuous_snd⟩
  let H : C(↥(stdSimplex ℝ (Fin (n+1))) × unitInterval, E) := H'.comp ψ
  refine ⟨H, ?_, ?_, ?_⟩
  · intro y
    show H' (i y, 0) = l₁ y
    rw [hH'₀ (i y), ContinuousMap.comp_apply]
    exact congrArg l₁ (hri' y)
  · intro y
    show H' (i y, 1) = l₂ y
    rw [hH'₁ (i y), ContinuousMap.comp_apply]
    exact congrArg l₂ (hri' y)
  · ext q
    have h₁q : (p.comp H') (i q.1, q.2) =
        ((σ.comp r).comp ContinuousMap.fst) (i q.1, q.2) :=
      congrFun (congrArg DFunLike.coe hH'p) (i q.1, q.2)
    have h₂q : ((σ.comp r).comp ContinuousMap.fst) (i q.1, q.2) = σ q.1 := by
      show σ (r (i q.1)) = σ q.1
      rw [hri' q.1]
    show (p.comp H') (i q.1, q.2) = σ q.1
    rw [h₁q, h₂q]

end

end Work.Serre
