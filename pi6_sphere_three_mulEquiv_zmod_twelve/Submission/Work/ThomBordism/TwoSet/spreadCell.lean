import Mathlib
import Submission.Work.ThomBordism.TwoSet.SpreadCont
import Submission.Work.ThomBordism.TwoSet.SpreadDefs
import Submission.Work.ThomBordism.TwoSet.Cells
import Submission.Work.ThomBordism.TwoSet.clampCell_mem_cOf
import Submission.Work.ThomBordism.TwoSet.Cutoff

/-!
# Spreading a homotopy of a grid cell over the cube

`spreadCell`: given a map `g : I^j → X` and a homotopy `H` of `g|cellSet c` relative to the
relative boundary of the cell `c`, there is a homotopy `G` of `g` which agrees with `H` on
`cellSet c`, is constant on `{nuOf c = 0}`, and whose values at time `1` are values of `H`
(when the flow has arrived) or of `g` on the segment from `x` to the clamp of `x` onto `c`.

The construction is the one of `SpreadDefs`: the "spreading retraction"
`spreadMap c hN : I^j × I → (I^j × {0}) ∪ (cellSet c × I)` retracts the cylinder onto the set on
which the homotopy is known; the glued map is then continuous by the closed cover
`{pushAmount = 0} ∪ {spreadPt ∈ cellSet c}` (on the intersection `pushI = 0`, so the two branches agree
by `hH0`).
-/

set_option maxHeartbeats 1000000

open scoped Topology unitInterval

namespace Work.ThomBordism.TwoSet

variable {j N : ℕ}

/-! ### `cellSet c` is closed -/

theorem isClosed_cellSet' (c : CellIdx j N) : IsClosed (cellSet c) := by
  have hfun : ∀ i : Fin j, Continuous fun x : IC j => ((x i : unitInterval) : ℝ) :=
    fun i => continuous_subtype_val.comp (continuous_apply i)
  have h : cellSet c = ⋂ i, {x : IC j |
      ((x i : unitInterval) : ℝ) ∈ Set.Icc ((c.lo i : ℝ) / N) ((c.hi i : ℝ) / N)} := by
    ext x
    simp only [mem_cellSet, Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_Icc]
  rw [h]
  exact isClosed_iInter fun i => isClosed_Icc.preimage (hfun i)

/-! ### The push time and the spreading point, as functions on `I^j × I` -/

/-- The push time of the spreading retraction, as a function of the pair `(x, τ)`. -/
noncomputable def spT (c : CellIdx j N) (p : IC j × I) : ℝ := pushAmount c p.1 p.2

@[simp] theorem spT_apply (c : CellIdx j N) (p : IC j × I) : spT c p = pushAmount c p.1 p.2 := rfl

/-- The point reached by the spreading flow, as a function of the pair `(x, τ)`. -/
noncomputable def spPt (c : CellIdx j N) (hN : 1 ≤ N) (p : IC j × I) : IC j :=
  spreadPt c hN p.1 p.2

@[simp] theorem spPt_apply (c : CellIdx j N) (hN : 1 ≤ N) (p : IC j × I) :
    spPt c hN p = spreadPt c hN p.1 p.2 := rfl

/-- The push time, as an element of `I`, as a function of the pair `(x, τ)`. -/
noncomputable def spI (c : CellIdx j N) (p : IC j × I) : I := pushI c p.1 p.2

@[simp] theorem spI_apply (c : CellIdx j N) (p : IC j × I) : spI c p = pushI c p.1 p.2 := rfl

theorem continuous_spT (c : CellIdx j N) : Continuous (spT c) :=
  continuous_subtype_val.comp (continuous_pushI c)

theorem continuous_spPt (c : CellIdx j N) (hN : 1 ≤ N) : Continuous (spPt c hN) :=
  continuous_spreadPt c hN

theorem continuous_spI (c : CellIdx j N) : Continuous (spI c) :=
  continuous_pushI c

/-! ### Elementary properties of the push time -/

theorem pushT_at_zero (c : CellIdx j N) (x : IC j) : pushAmount c x 0 = 0 := by
  rw [pushAmount, show (((0 : I) : ℝ)) = 0 from rfl, zero_mul, zero_sub]
  exact max_eq_left (by linarith [rOf_nonneg c x])

theorem pushT_at_one (c : CellIdx j N) (x : IC j) :
    pushAmount c x 1 = max 0 (nuOf c x - rOf c x) := by
  rw [pushAmount, show (((1 : I) : ℝ)) = 1 from rfl, one_mul]

theorem pushT_at_one_eq_zero_of_ge (c : CellIdx j N) {x : IC j} (h : nuOf c x ≤ rOf c x) :
    pushAmount c x 1 = 0 := by
  rw [pushT_at_one, max_eq_left (sub_nonpos.mpr h)]

theorem pushT_at_one_pos_of_lt (c : CellIdx j N) {x : IC j} (h : rOf c x < nuOf c x) :
    0 < pushAmount c x 1 := by
  rw [pushT_at_one]
  exact lt_max_iff.mpr (Or.inr (by linarith))

theorem pushT_eq_zero_of_nuOf_eq_zero (c : CellIdx j N) {x : IC j} (τ : I)
    (h : nuOf c x = 0) : pushAmount c x τ = 0 := by
  rw [pushAmount, h, mul_zero, zero_sub]
  exact max_eq_left (by linarith [rOf_nonneg c x])

theorem pushI_eq_zero_iff (c : CellIdx j N) (x : IC j) (τ : I) :
    pushI c x τ = 0 ↔ pushAmount c x τ = 0 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-! ### The same, in the `(x, τ)` pair notation -/

theorem spT_nonneg (c : CellIdx j N) (p : IC j × I) : 0 ≤ spT c p := by
  rw [spT_apply]; exact pushT_nonneg c p.1 p.2

theorem spT_eq_zero_iff (c : CellIdx j N) (p : IC j × I) :
    spT c p = 0 ↔ (p.2 : ℝ) * nuOf c p.1 ≤ rOf c p.1 := by
  rw [spT_apply, pushAmount, max_eq_left_iff]
  constructor <;> intro h <;> linarith

theorem spI_eq_zero_iff (c : CellIdx j N) (p : IC j × I) : spI c p = 0 ↔ spT c p = 0 := by
  rw [spI_apply, spT_apply]
  exact pushI_eq_zero_iff c p.1 p.2

theorem spT_at_zero (c : CellIdx j N) (x : IC j) : spT c (x, 0) = 0 := by
  rw [spT_apply]; exact pushT_at_zero c x

theorem spT_at_one_eq_zero_of_ge (c : CellIdx j N) {x : IC j} (h : nuOf c x ≤ rOf c x) :
    spT c (x, 1) = 0 := by
  rw [spT_apply]; exact pushT_at_one_eq_zero_of_ge c h

theorem spT_at_one_pos_of_lt (c : CellIdx j N) {x : IC j} (h : rOf c x < nuOf c x) :
    0 < spT c (x, 1) := by
  rw [spT_apply]; exact pushT_at_one_pos_of_lt c h

theorem spT_eq_zero_of_nuOf_eq_zero (c : CellIdx j N) {x : IC j} (τ : I)
    (h : nuOf c x = 0) : spT c (x, τ) = 0 := by
  rw [spT_apply]; exact pushT_eq_zero_of_nuOf_eq_zero c τ h

theorem spreadPt_at_zero (c : CellIdx j N) (hN : 1 ≤ N) (x : IC j) :
    spreadPt c hN x 0 = x :=
  congrArg Prod.fst (spreadMap_zero c hN x)

theorem spreadPt_at_self (c : CellIdx j N) (hN : 1 ≤ N) {z : IC j} (hz : z ∈ cellSet c)
    (τ : I) : spreadPt c hN z τ = z :=
  congrArg Prod.fst (spreadMap_self c hN hz τ)

theorem pushI_at_self (c : CellIdx j N) (hN : 1 ≤ N) {z : IC j} (hz : z ∈ cellSet c) (τ : I) :
    pushI c z τ = τ :=
  congrArg Prod.snd (spreadMap_self c hN hz τ)

theorem spPt_at_self (c : CellIdx j N) (hN : 1 ≤ N) {z : IC j} (hz : z ∈ cellSet c) (τ : I) :
    spPt c hN (z, τ) = z := by
  rw [spPt_apply]; exact spreadPt_at_self c hN hz τ

theorem spI_at_self (c : CellIdx j N) (hN : 1 ≤ N) {z : IC j} (hz : z ∈ cellSet c) (τ : I) :
    spI c (z, τ) = τ := by
  rw [spI_apply]; exact pushI_at_self c hN hz τ

theorem spPt_mem_of_pos (c : CellIdx j N) (hN : 1 ≤ N) {p : IC j × I} (h : 0 < spT c p) :
    spPt c hN p ∈ cellSet c := by
  have h' : 0 < pushAmount c p.1 p.2 := by rwa [spT_apply] at h
  rw [spPt_apply]
  exact spreadPt_mem_of_pushT_pos c hN h'

/-! ### The clamped point lies in the minimal cell of a nearby point -/

theorem cellDist_lt_quarter_of_nuOf_pos (c : CellIdx j N) {x : IC j} (h : 0 < nuOf c x) :
    cellDist c x < 1/4 := by
  have hr : rOf c x < 1/4 := (nuOf_pos_iff c x).mp h
  rcases min_choice (1 : ℝ) (cellDist c x) with hc | hc
  · rw [rOf, hc] at hr; norm_num at hr
  · rwa [rOf, hc] at hr

/-- On the support of `nuOf c` every coordinate of `x` is within `1/4` (in `N`-scaled units) of
the coordinate interval of `c`. -/
theorem close_of_nuOf_pos (c : CellIdx j N) {x : IC j} (h : 0 < nuOf c x) :
    ∀ i : Fin j, (c.lo i : ℝ) - 1/4 < (N : ℝ) * (x i : ℝ) ∧
      (N : ℝ) * (x i : ℝ) < (c.hi i : ℝ) + 1/4 := by
  intro i
  have hcd := cellDist_lt_quarter_of_nuOf_pos c h
  have h1 := cellDistCoord_le_cellDist c i x
  have h2 := cellDistCoord_le c i x
  have h3 := cellDistCoord_le' c i x
  exact ⟨by linarith, by linarith⟩

/-! ### The glued map -/

/-- The membership proof of the spreading point used in the glued map. -/
theorem glueMem (c : CellIdx j N) (hN : 1 ≤ N) (x : IC j) (τ : I) (h : pushAmount c x τ ≠ 0) :
    spreadPt c hN x τ ∈ cellSet c :=
  spreadPt_mem_of_pushT_pos c hN (lt_of_le_of_ne (pushT_nonneg c x τ) (Ne.symm h))

/-- The glued map on the cylinder, in `(x, τ)` coordinates: outside the support it is
`g ∘ spreadPt`, and where the flow has arrived it is `H` at the spreading point and the push
time. -/
noncomputable def spreadGlue {X : Type*} [TopologicalSpace X] (c : CellIdx j N) (hN : 1 ≤ N)
    (g : C(IC j, X)) (H : C(cellSet c × I, X)) (x : IC j) (τ : I) : X :=
  if hp : pushAmount c x τ = 0 then g (spreadPt c hN x τ)
  else H (⟨spreadPt c hN x τ, glueMem c hN x τ hp⟩, pushI c x τ)

theorem continuous_spreadGlue {X : Type*} [TopologicalSpace X] (c : CellIdx j N) (hN : 1 ≤ N)
    (g : C(IC j, X)) (H : C(cellSet c × I, X))
    (hH0 : ∀ z : cellSet c, H (z, 0) = g z) :
    Continuous fun p : IC j × I => spreadGlue c hN g H p.1 p.2 := by
  have hS : IsClosed {p : IC j × I | spT c p = 0} :=
    isClosed_eq (continuous_spT c) continuous_const
  have hT : IsClosed {p : IC j × I | spPt c hN p ∈ cellSet c} :=
    (isClosed_cellSet' c).preimage (continuous_spPt c hN)
  have hcover : {p : IC j × I | spT c p = 0} ∪ {p : IC j × I | spPt c hN p ∈ cellSet c}
      = Set.univ := by
    ext p
    simp only [Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    rcases eq_or_lt_of_le (spT_nonneg c p) with h | h
    · exact Or.inl h.symm
    · exact Or.inr (spPt_mem_of_pos c hN h)
  have hScont : ContinuousOn (fun p : IC j × I => spreadGlue c hN g H p.1 p.2)
      {p : IC j × I | spT c p = 0} := by
    have h1 : ContinuousOn (fun p : IC j × I => g (spreadPt c hN p.1 p.2))
        {p : IC j × I | spT c p = 0} :=
      (g.continuous.comp (continuous_spreadPt c hN)).continuousOn
    refine h1.congr ?_
    intro p hp
    have hp' : pushAmount c p.1 p.2 = 0 := hp
    show spreadGlue c hN g H p.1 p.2 = g (spreadPt c hN p.1 p.2)
    rw [spreadGlue, dif_pos hp']
  have hTcont : ContinuousOn (fun p : IC j × I => spreadGlue c hN g H p.1 p.2)
      {p : IC j × I | spPt c hN p ∈ cellSet c} := by
    rw [continuousOn_iff_continuous_domRestrict]
    let F : C(↥{p : IC j × I | spPt c hN p ∈ cellSet c}, X) :=
      ⟨fun q => H (⟨spreadPt c hN q.1.1 q.1.2, q.2⟩, pushI c q.1.1 q.1.2), by
        refine H.continuous.comp ?_
        exact Continuous.prodMk
          (Continuous.subtype_mk ((continuous_spreadPt c hN).comp continuous_subtype_val)
            (fun q => q.2))
          ((continuous_pushI c).comp continuous_subtype_val)⟩
    refine F.continuous.congr ?_
    intro q
    show H (⟨spreadPt c hN q.1.1 q.1.2, q.2⟩, pushI c q.1.1 q.1.2)
        = spreadGlue c hN g H q.1.1 q.1.2
    rw [spreadGlue]
    by_cases h0 : pushAmount c q.1.1 q.1.2 = 0
    · rw [dif_pos h0]
      show H (⟨spreadPt c hN q.1.1 q.1.2, q.2⟩, pushI c q.1.1 q.1.2)
          = g (spreadPt c hN q.1.1 q.1.2)
      have hs : pushI c q.1.1 q.1.2 = 0 := Subtype.ext h0
      rw [hs]
      exact hH0 ⟨spreadPt c hN q.1.1 q.1.2, q.2⟩
    · rw [dif_neg h0]
  have h1 := ContinuousOn.union_of_isClosed hScont hTcont hS hT
  rwa [hcover, continuousOn_univ] at h1

/-! ### The spreading lemma -/

theorem spreadCell {X : Type*} [TopologicalSpace X] {j N : ℕ} (c : Work.ThomBordism.TwoSet.CellIdx j N) (hN : 1 ≤ N)
    (g : C(Work.ThomBordism.TwoSet.IC j, X))
    (H : C(Work.ThomBordism.TwoSet.cellSet c × unitInterval, X))
    (hH0 : ∀ z : Work.ThomBordism.TwoSet.cellSet c, H (z, 0) = g z)
    (hHbd : ∀ (z : Work.ThomBordism.TwoSet.cellSet c), ((z : Work.ThomBordism.TwoSet.IC j) ∈ Work.ThomBordism.TwoSet.cellRelbd c) → ∀ t, H (z, t) = g z) :
    ∃ G : C(Work.ThomBordism.TwoSet.IC j × unitInterval, X),
      (∀ x, G ((x, 0) : Work.ThomBordism.TwoSet.IC j × unitInterval) = g x) ∧
      (∀ (z : Work.ThomBordism.TwoSet.cellSet c) t, G ((z : Work.ThomBordism.TwoSet.IC j), t) = H (z, t)) ∧
      (∀ x, Work.ThomBordism.TwoSet.nuOf c x = 0 → ∀ t, G (x, t) = g x) ∧
      (∀ x, x ∉ Work.ThomBordism.TwoSet.cellSet c → 0 < Work.ThomBordism.TwoSet.nuOf c x →
        Work.ThomBordism.TwoSet.rOf c x ≤ Work.ThomBordism.TwoSet.nuOf c x →
        ∃ (z : Work.ThomBordism.TwoSet.IC j) (hz : z ∈ Work.ThomBordism.TwoSet.cellSet c) (s : unitInterval),
          G (x, 1) = H (⟨z, hz⟩, s)) ∧
      (∀ x, x ∉ Work.ThomBordism.TwoSet.cellSet c → 0 < Work.ThomBordism.TwoSet.nuOf c x →
        Work.ThomBordism.TwoSet.rOf c x ≤ Work.ThomBordism.TwoSet.nuOf c x →
        Work.ThomBordism.TwoSet.clampCell c hN x ∈ Work.ThomBordism.TwoSet.cellRelbd c →
        G (x, 1) = g (Work.ThomBordism.TwoSet.clampCell c hN x)) ∧
      (∀ x, x ∉ Work.ThomBordism.TwoSet.cellSet c → 0 < Work.ThomBordism.TwoSet.nuOf c x →
        Work.ThomBordism.TwoSet.nuOf c x < Work.ThomBordism.TwoSet.rOf c x →
        ∃ y : Work.ThomBordism.TwoSet.IC j,
          y ∈ Work.ThomBordism.TwoSet.cellSet (Work.ThomBordism.TwoSet.cOf N x) ∧ G (x, 1) = g y) := by
  classical
  have hcont : Continuous fun p : IC j × unitInterval => spreadGlue c hN g H p.1 p.2 :=
    continuous_spreadGlue c hN g H hH0
  refine ⟨⟨fun p : IC j × unitInterval => spreadGlue c hN g H p.1 p.2, hcont⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    show spreadGlue c hN g H x 0 = g x
    rw [spreadGlue, dif_pos (pushT_at_zero c x), spreadPt_at_zero c hN x]
  · intro z t
    show spreadGlue c hN g H (z : IC j) t = H (z, t)
    by_cases h0 : pushAmount c (z : IC j) t = 0
    · have ht : t = 0 := by
        have h1 : pushI c (z : IC j) t = 0 := Subtype.ext h0
        rwa [pushI_at_self c hN z.2 t] at h1
      rw [spreadGlue, dif_pos h0, spreadPt_at_self c hN z.2 t, ht, hH0 z]
    · rw [spreadGlue, dif_neg h0, pushI_at_self c hN z.2 t]
      exact congrArg H (Prod.ext (Subtype.ext (spreadPt_at_self c hN z.2 t)) rfl)
  · intro x hx t
    show spreadGlue c hN g H x t = g x
    rw [spreadGlue, dif_pos (pushT_eq_zero_of_nuOf_eq_zero c t hx),
      spreadPt_eq_self_of_nuOf_eq_zero c hN t hx]
  · intro x hx hpos hle
    by_cases hlt : rOf c x < nuOf c x
    · have hp : 0 < pushAmount c x 1 := pushT_at_one_pos_of_lt c hlt
      refine ⟨spreadPt c hN x 1, spreadPt_mem_of_pushT_pos c hN hp, pushI c x 1, ?_⟩
      show spreadGlue c hN g H x 1
          = H (⟨spreadPt c hN x 1, spreadPt_mem_of_pushT_pos c hN hp⟩, pushI c x 1)
      rw [spreadGlue, dif_neg (ne_of_gt hp)]
    · have hp : pushAmount c x 1 = 0 := pushT_at_one_eq_zero_of_ge c (le_of_not_gt hlt)
      refine ⟨clampCell c hN x, clampCell_mem c hN x, 0, ?_⟩
      show spreadGlue c hN g H x 1 = H (⟨clampCell c hN x, clampCell_mem c hN x⟩, 0)
      rw [spreadGlue, dif_pos hp,
        spreadPt_eq_clamp_of_le c hN (by
          rw [show (((1 : I) : ℝ)) = 1 from rfl, one_mul]; exact hle)]
      exact (hH0 ⟨clampCell c hN x, clampCell_mem c hN x⟩).symm
  · intro x hx hpos hle hbd
    by_cases hlt : rOf c x < nuOf c x
    · have hp : 0 < pushAmount c x 1 := pushT_at_one_pos_of_lt c hlt
      have hcl : spreadPt c hN x 1 = clampCell c hN x :=
        spreadPt_eq_clamp_of_le c hN (by
          rw [show (((1 : I) : ℝ)) = 1 from rfl, one_mul]; exact hle)
      show spreadGlue c hN g H x 1 = g (clampCell c hN x)
      rw [spreadGlue, dif_neg (ne_of_gt hp)]
      have hsub : (⟨spreadPt c hN x 1, glueMem c hN x 1 (ne_of_gt hp)⟩ : cellSet c)
          = ⟨clampCell c hN x, clampCell_mem c hN x⟩ := Subtype.ext hcl
      have hpair : ((⟨spreadPt c hN x 1, glueMem c hN x 1 (ne_of_gt hp)⟩ : cellSet c),
            pushI c x 1)
          = (⟨clampCell c hN x, clampCell_mem c hN x⟩, pushI c x 1) := Prod.ext hsub rfl
      exact (congrArg H hpair).trans
        (hHbd ⟨clampCell c hN x, clampCell_mem c hN x⟩ hbd (pushI c x 1))
    · have hp : pushAmount c x 1 = 0 := pushT_at_one_eq_zero_of_ge c (le_of_not_gt hlt)
      show spreadGlue c hN g H x 1 = g (clampCell c hN x)
      rw [spreadGlue, dif_pos hp,
        spreadPt_eq_clamp_of_le c hN (by
          rw [show (((1 : I) : ℝ)) = 1 from rfl, one_mul]; exact hle)]
  · intro x hx hpos hlt
    have hp : pushAmount c x 1 = 0 := pushT_at_one_eq_zero_of_ge c (le_of_lt hlt)
    refine ⟨spreadPt c hN x 1, ?_, ?_⟩
    · rw [spreadPt_one_of_lt c hN hlt]
      exact segMap_mem_cellSet (mem_cOf N hN x)
        (clampCell_mem_cOf hN c (close_of_nuOf_pos c hpos)) _
    · show spreadGlue c hN g H x 1 = g (spreadPt c hN x 1)
      rw [spreadGlue, dif_pos hp, spreadPt_one_of_lt c hN hlt]

end Work.ThomBordism.TwoSet
