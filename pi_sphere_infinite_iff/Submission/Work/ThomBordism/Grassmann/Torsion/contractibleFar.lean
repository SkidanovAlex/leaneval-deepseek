import Mathlib
import Submission.Work.ThomBordism.Grassmann.Torsion.ModelGeom

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

/-!
# The "far" part of the Thom space is contractible

`Work.ThomBordism.Grassmann.Torsion.far k m 1 = {∞} ∪ {p | 1 < fibN p}` is an open
neighbourhood of the point at infinity of the Thom space `TP k m = OnePoint (TM k m)`.

**The contraction is the radial push to infinity.**  Write `x = some p` with `fibN p > 1` and let
`s : [0,1]`: push `p` radially outwards by the factor `(1-s)⁻¹ ≥ 1`, i.e. send it to
`⟨p.1, (1-s)⁻¹ • p.2⟩`, which still has `fibN > 1`; at `s = 1` every point has reached `∞` (and `∞`
itself is fixed throughout).

The only continuity obligation is at `s = 1`: a basic neighbourhood of `∞` is the complement of a
compact `K ⊆ TM k m`, and since `fibN` is proper (`{fibN ≤ M}` is compact for every `M`,
`isCompact_fibN_le`) and homogeneous (`fibN_smul`), the push of a point with `fibN` large enough
automatically leaves `K`.

This is the `contractibleFar` input of the comparison `H^n(X) ≅ H^n(X, far 1)` of the Thom-space
torsion chapter (see `Submission/Work/ThomBordism/Grassmann/Torsion/PLAN_ROUND3.md`).
-/

open scoped Topology

namespace Work.ThomBordism.Grassmann.Torsion

open Work.ThomBordism.Grassmann

noncomputable section

variable {k m : ℕ}

/-- The **radial push to infinity** on the Thom space `TP k m`, as a function of the homotopy
parameter `s` and the point: `∞ ↦ ∞`, and `some p ↦ some ⟨p.1, (1-s)⁻¹ • p.2⟩` for `s ≠ 1`, while
`s = 1` collapses everything to `∞`. -/
def pushF (k m : ℕ) (s : unitInterval) (x : TP k m) : TP k m :=
  match x with
  | none => OnePoint.infty
  | some p => if (s : ℝ) = 1 then OnePoint.infty
      else OnePoint.some (⟨p.1, (1 - (s : ℝ))⁻¹ • p.2⟩ : TM k m)

@[simp] theorem pushF_infty (k m : ℕ) (s : unitInterval) :
    pushF k m s OnePoint.infty = OnePoint.infty := rfl

theorem pushF_some (k m : ℕ) (s : unitInterval) (p : TM k m) :
    pushF k m s (OnePoint.some p) =
      (if (s : ℝ) = 1 then OnePoint.infty
       else OnePoint.some (⟨p.1, (1 - (s : ℝ))⁻¹ • p.2⟩ : TM k m)) := rfl

theorem pushF_zero (k m : ℕ) (x : TP k m) : pushF k m 0 x = x := by
  refine OnePoint.rec ?_ ?_ x
  · rw [pushF_infty]
  · intro p
    rw [pushF_some, if_neg (by simp)]
    simp

theorem pushF_one (k m : ℕ) (x : TP k m) : pushF k m 1 x = OnePoint.infty := by
  refine OnePoint.rec ?_ ?_ x
  · rw [pushF_infty]
  · intro p
    rw [pushF_some, if_pos (by simp)]

/-! ## Continuity of the coefficient functions -/

/-- `r ↦ 2 * fibN r.1` is continuous on the total space. -/
theorem continuous_two_mul_fibN (k m : ℕ) :
    Continuous (fun r : TM k m × unitInterval => (2 : ℝ) * fibN k m r.1) := by
  have h1 : Continuous (fun r : TM k m × unitInterval => fibN k m r.1) :=
    (fibN_continuous k m).comp (f := fun r : TM k m × unitInterval => r.1) continuous_fst
  exact h1.const_mul 2

/-- `r ↦ (1 - r.2) * C` is continuous on the total space, for every constant `C`. -/
theorem continuous_one_sub_snd_mul (k m : ℕ) (C : ℝ) :
    Continuous (fun r : TM k m × unitInterval => (1 - (r.2 : ℝ)) * C) := by
  have h1 : Continuous (fun r : TM k m × unitInterval => (1 - (r.2 : ℝ))) :=
    continuous_const.sub (continuous_subtype_val.comp continuous_snd)
  exact h1.mul_const C

/-- **The push stays in `far 1`**: if `fibN p > 1` then the radial push of `some p` by the factor
`(1-s)⁻¹ ≥ 1` again has `fibN > 1`, and `∞` is fixed. -/
theorem mem_far_pushF (k m : ℕ) {x : TP k m} (hx : x ∈ far k m 1) (s : unitInterval) :
    pushF k m s x ∈ far k m 1 := by
  rcases hx with ⟨p, hp, rfl⟩ | rfl
  · have hp' : 1 < fibN k m p := hp
    rw [pushF_some]
    by_cases h1 : (s : ℝ) = 1
    · rw [if_pos h1]
      exact Or.inr rfl
    · rw [if_neg h1]
      have hlt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 h1
      have hpos : 0 < 1 - (s : ℝ) := by linarith
      have hle : 1 ≤ (1 - (s : ℝ))⁻¹ := by
        rw [one_le_inv₀ hpos]; linarith [s.2.1]
      refine Or.inl ⟨⟨p.1, (1 - (s : ℝ))⁻¹ • p.2⟩, ?_, rfl⟩
      show 1 < fibN k m (⟨p.1, (1 - (s : ℝ))⁻¹ • p.2⟩ : TM k m)
      rw [fibN_smul k m (le_trans zero_le_one hle) p]
      have h2 : fibN k m p ≤ (1 - (s : ℝ))⁻¹ * fibN k m p :=
        le_mul_of_one_le_left (fibN_nonneg k m p) hle
      linarith
  · rw [pushF_infty]
    exact Or.inr rfl

/-! ## Continuity of the push at infinity -/

/-- **Joint continuity of the push at `(∞, s)`**, for every `s`.  A basic neighbourhood of `∞` is
the complement of a compact `K ⊆ TM k m`; choosing `M` with `fibN ≤ M` on `K` (compactness) and
using that the push factor is `≥ 1`, the push of a point with `fibN > max M 0` stays outside `K`. -/
theorem continuousAt_pushF_infty (k m : ℕ) (s : unitInterval) :
    ContinuousAt (fun r : TP k m × unitInterval => pushF k m r.2 r.1) (OnePoint.infty, s) := by
  rw [ContinuousAt, pushF_infty]
  change Filter.map (fun r : TP k m × unitInterval => pushF k m r.2 r.1)
      (𝓝 (OnePoint.infty, s)) ≤ 𝓝 (OnePoint.infty : TP k m)
  rw [OnePoint.le_nhds_infty]
  intro K _ hKcp
  rw [Filter.mem_map]
  obtain ⟨M, hM⟩ := exists_fibN_bound_of_compact k m K hKcp
  let M' : ℝ := max M 0
  have hKM : ∀ p ∈ K, fibN k m p ≤ M' :=
    fun p hp => le_trans (hM p hp) (le_max_left _ _)
  have hU : (OnePoint.some '' {p : TM k m | fibN k m p ≤ M'}ᶜ ∪ {OnePoint.infty}) ∈
      𝓝 (OnePoint.infty : TP k m) :=
    OnePoint.hasBasis_nhds_infty.mem_iff.mpr
      ⟨_, ⟨isClosed_le (fibN_continuous k m) continuous_const, isCompact_fibN_le k m M'⟩,
        subset_rfl⟩
  have hprod : ((OnePoint.some '' {p : TM k m | fibN k m p ≤ M'}ᶜ ∪ {OnePoint.infty}) ×ˢ
      (Set.univ : Set unitInterval)) ∈ 𝓝 ((OnePoint.infty, s) : TP k m × unitInterval) := by
    rw [nhds_prod_eq]
    exact Filter.prod_mem_prod hU Filter.univ_mem
  refine Filter.mem_of_superset hprod ?_
  rintro ⟨x, s'⟩ ⟨hx, -⟩
  show pushF k m s' x ∈ OnePoint.some '' Kᶜ ∪ {OnePoint.infty}
  rcases hx with ⟨p, hp, rfl⟩ | hx
  · have hp' : M' < fibN k m p := by
      simpa only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] using hp
    by_cases h1 : (s' : ℝ) = 1
    · rw [pushF_some, if_pos h1]
      exact Or.inr rfl
    · have hlt : (s' : ℝ) < 1 := lt_of_le_of_ne s'.2.2 h1
      have hpos : 0 < 1 - (s' : ℝ) := by linarith
      have hle : 1 ≤ (1 - (s' : ℝ))⁻¹ := by
        rw [one_le_inv₀ hpos]; linarith [s'.2.1]
      rw [pushF_some, if_neg h1]
      refine Or.inl ⟨⟨p.1, (1 - (s' : ℝ))⁻¹ • p.2⟩, ?_, rfl⟩
      intro hmemK
      have hMK : fibN k m (⟨p.1, (1 - (s' : ℝ))⁻¹ • p.2⟩ : TM k m) ≤ M' := hKM _ hmemK
      rw [fibN_smul k m (le_trans zero_le_one hle) p] at hMK
      have h2 : fibN k m p ≤ (1 - (s' : ℝ))⁻¹ * fibN k m p :=
        le_mul_of_one_le_left (fibN_nonneg k m p) hle
      linarith
  · obtain rfl : x = OnePoint.infty := by simpa using hx
    rw [pushF_infty]
    exact Or.inr rfl

/-! ## Continuity of the push at a finite point

The two cases are `s ≠ 1`, where the push agrees near `(p,s)` with the manifestly continuous
expression `r ↦ some ⟨r.1.1, (1-r.2)⁻¹ • r.1.2⟩` (the coefficient is patched at `(1+(s:ℝ))/2` so
that it is globally continuous), and `s = 1`, where the value is `∞` and is the limit of the push
because `(1-s)⁻¹ fibN` tends to infinity. -/

/-- The chart computation at `s ≠ 1`. -/
theorem continuousAt_pushF_chart_ne (k m : ℕ) (p : TM k m) (s : unitInterval)
    (h1 : ¬ (s : ℝ) = 1) :
    ContinuousAt (fun r : TM k m × unitInterval => pushF k m r.2 (OnePoint.some r.1)) (p, s) := by
  set a : ℝ := (1 + (s : ℝ)) / 2 with ha
  have hlt : (s : ℝ) < 1 := lt_of_le_of_ne s.2.2 h1
  have ha1 : a < 1 := by rw [ha]; linarith
  have hsa : (s : ℝ) < a := by rw [ha]; linarith
  have hinv : Continuous (fun r : TM k m × unitInterval => (1 - min (r.2 : ℝ) a)⁻¹) := by
    refine Continuous.inv₀ ?_ ?_
    · exact continuous_const.sub
        ((continuous_subtype_val.comp continuous_snd).min continuous_const)
    · intro r
      have hmin : min (r.2 : ℝ) a ≤ a := min_le_right _ _
      intro h0
      linarith
  have hbase : Continuous (fun r : TM k m × unitInterval =>
      (⟨r.1.1, (1 - min (r.2 : ℝ) a)⁻¹ • r.1.2⟩ : TM k m)) :=
    Work.Thom.continuous_smul_section (tautologicalBundle k m)
      ⟨fun r => r.1, continuous_fst⟩ ⟨_, hinv⟩
  have hG : ContinuousAt (fun r : TM k m × unitInterval =>
      OnePoint.some (⟨r.1.1, (1 - min (r.2 : ℝ) a)⁻¹ • r.1.2⟩ : TM k m)) (p, s) :=
    OnePoint.continuous_coe.continuousAt.comp hbase.continuousAt
  refine hG.congr ?_
  have hmem : {r : TM k m × unitInterval | (r.2 : ℝ) < a} ∈ 𝓝 (p, s) :=
    ((isOpen_lt continuous_subtype_val continuous_const).preimage continuous_snd).mem_nhds hsa
  filter_upwards [hmem] with r hr
  have hr1 : (r.2 : ℝ) ≠ 1 := by linarith
  rw [pushF_some, if_neg hr1, min_eq_left (le_of_lt hr)]

/-- The chart computation at `s = 1`. -/
theorem continuousAt_pushF_chart_one (k m : ℕ) (p : TM k m) (hp : fibN k m p ≠ 0)
    (s : unitInterval) (h1 : (s : ℝ) = 1) :
    ContinuousAt (fun r : TM k m × unitInterval => pushF k m r.2 (OnePoint.some r.1)) (p, s) := by
  have hval : pushF k m s (OnePoint.some p) = OnePoint.infty := by
    rw [pushF_some, if_pos h1]
  rw [ContinuousAt, hval]
  change Filter.map (fun r : TM k m × unitInterval => pushF k m r.2 (OnePoint.some r.1))
      (𝓝 (p, s)) ≤ 𝓝 (OnePoint.infty : TP k m)
  rw [OnePoint.le_nhds_infty]
  intro K _ hKcp
  rw [Filter.mem_map]
  obtain ⟨M, hM⟩ := exists_fibN_bound_of_compact k m K hKcp
  let M' : ℝ := max M 0
  have hM'M : M ≤ M' := le_max_left _ _
  have hM'0 : 0 ≤ M' := le_max_right _ _
  have hKsub : K ⊆ {q : TM k m | fibN k m q ≤ M'} := fun q hq => le_trans (hM q hq) hM'M
  have hp_pos : 0 < fibN k m p := lt_of_le_of_ne (fibN_nonneg k m p) (Ne.symm hp)
  have hA : {r : TM k m × unitInterval | fibN k m p < 2 * fibN k m r.1} ∈ 𝓝 (p, s) := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (continuous_const : Continuous fun _ : TM k m × unitInterval => fibN k m p)
        (continuous_two_mul_fibN k m)
    · change fibN k m p < 2 * fibN k m p
      linarith
  have hB : {r : TM k m × unitInterval |
      (1 - (r.2 : ℝ)) * (2 * (M' + 1)) < fibN k m p} ∈ 𝓝 (p, s) := by
    apply IsOpen.mem_nhds
    · exact isOpen_lt (continuous_one_sub_snd_mul k m (2 * (M' + 1)))
        (continuous_const : Continuous fun _ : TM k m × unitInterval => fibN k m p)
    · change (1 - (s : ℝ)) * (2 * (M' + 1)) < fibN k m p
      rw [h1, sub_self, zero_mul]
      exact hp_pos
  refine Filter.mem_of_superset (Filter.inter_mem hA hB) ?_
  rintro ⟨u, s'⟩ ⟨hu, hs'⟩
  change fibN k m p < 2 * fibN k m u at hu
  change (1 - (s' : ℝ)) * (2 * (M' + 1)) < fibN k m p at hs'
  show pushF k m s' (OnePoint.some u) ∈ OnePoint.some '' Kᶜ ∪ {OnePoint.infty}
  by_cases h2 : (s' : ℝ) = 1
  · rw [pushF_some, if_pos h2]
    exact Or.inr rfl
  · have hlt : (s' : ℝ) < 1 := lt_of_le_of_ne s'.2.2 h2
    have hpos : 0 < 1 - (s' : ℝ) := by linarith
    have hpos2 : (0 : ℝ) < 2 * (M' + 1) := by linarith
    have hpos3 : (0 : ℝ) < (1 - (s' : ℝ))⁻¹ := inv_pos.mpr hpos
    rw [pushF_some, if_neg h2]
    refine Or.inl ⟨⟨u.1, (1 - (s' : ℝ))⁻¹ • u.2⟩, ?_, rfl⟩
    intro hmemK
    have hMK : fibN k m (⟨u.1, (1 - (s' : ℝ))⁻¹ • u.2⟩ : TM k m) ≤ M' := hKsub hmemK
    rw [fibN_smul k m (le_of_lt hpos3) u] at hMK
    have hgt : M' < (1 - (s' : ℝ))⁻¹ * fibN k m u := by
      rw [inv_mul_eq_div, lt_div_iff₀ hpos]
      nlinarith [hu, hs', hpos, hpos2]
    linarith

/-- Continuity of the push at `(some p, s)`, for every `p` with `fibN p ≠ 0` and every `s`: the
chart `(u,s) ↦ (some u, s)` is an open embedding, so it suffices to prove the two chart
computations. -/
theorem continuousAt_pushF_some (k m : ℕ) (p : TM k m) (hp : fibN k m p ≠ 0)
    (s : unitInterval) :
    ContinuousAt (fun r : TP k m × unitInterval => pushF k m r.2 r.1) (OnePoint.some p, s) := by
  have hchart : Topology.IsOpenEmbedding
      (fun r : TM k m × unitInterval => (OnePoint.some r.1, r.2)) :=
    (OnePoint.isOpenEmbedding_coe (X := TM k m)).prodMap Topology.IsOpenEmbedding.id
  have hcomp : ContinuousAt
      (fun r : TM k m × unitInterval => pushF k m r.2 (OnePoint.some r.1)) (p, s) := by
    by_cases h1 : (s : ℝ) = 1
    · exact continuousAt_pushF_chart_one k m p hp s h1
    · exact continuousAt_pushF_chart_ne k m p s h1
  refine (hchart.continuousAt_iff (x := (p, s))
    (g := fun r : TP k m × unitInterval => pushF k m r.2 r.1)).mp ?_
  show ContinuousAt (fun r : TM k m × unitInterval => pushF k m r.2 (OnePoint.some r.1)) (p, s)
  exact hcomp

/-! ## The contraction -/

/-- The push restricted to `far 1` is continuous. -/
theorem continuous_pushF_far (k m : ℕ) :
    Continuous fun q : ↥(far k m 1) × unitInterval => pushF k m q.2 q.1.1 := by
  rw [continuous_iff_continuousAt]
  intro q
  have hincl : ContinuousAt (fun q : ↥(far k m 1) × unitInterval => (q.1.1, q.2)) q :=
    ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousAt
  have hbase : ContinuousAt (fun r : TP k m × unitInterval => pushF k m r.2 r.1) (q.1.1, q.2) := by
    rcases q.1.2 with ⟨p, hp, hxp⟩ | h
    · have hp' : 1 < fibN k m p := hp
      rw [show q.1.1 = OnePoint.some p from hxp.symm]
      exact continuousAt_pushF_some k m p (ne_of_gt (lt_trans one_pos hp')) q.2
    · rw [show q.1.1 = OnePoint.infty from h]
      exact continuousAt_pushF_infty k m q.2
  exact ContinuousAt.comp (f := fun q : ↥(far k m 1) × unitInterval => (q.1.1, q.2))
    (g := fun r : TP k m × unitInterval => pushF k m r.2 r.1) hbase hincl

/-- **`far 1` is contractible**: the radial push to infinity contracts it to `∞`. -/
theorem contractibleFar (k m : ℕ) :
    ContractibleSpace ↥(Work.ThomBordism.Grassmann.Torsion.far k m 1) := by
  have hcont : Continuous fun q : ↥(far k m 1) × unitInterval => pushF k m q.2 q.1.1 :=
    continuous_pushF_far k m
  let hpush : C(unitInterval × ↥(far k m 1), ↥(far k m 1)) :=
    ⟨fun q => ⟨pushF k m q.1 q.2.1, mem_far_pushF k m q.2.2 q.1⟩,
      (hcont.comp continuous_swap).subtype_mk (fun q => mem_far_pushF k m q.2.2 q.1)⟩
  refine (contractible_iff_id_nullhomotopic _).mpr
    ⟨⟨OnePoint.infty, infty_mem_far k m 1⟩, ⟨⟨hpush, ?_, ?_⟩⟩⟩
  · intro x
    apply Subtype.ext
    dsimp only [hpush]
    simp only [ContinuousMap.id_apply]
    exact pushF_zero k m x.1
  · intro x
    apply Subtype.ext
    dsimp only [hpush]
    simp only [ContinuousMap.const_apply]
    exact pushF_one k m x.1

end

end Work.ThomBordism.Grassmann.Torsion
