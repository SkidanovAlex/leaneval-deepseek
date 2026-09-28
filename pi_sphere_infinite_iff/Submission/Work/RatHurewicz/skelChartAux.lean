import Mathlib
import Submission.Work.RatHurewicz.cellFacts
import Submission.Work.RatHurewicz.AvoidOrigin.Class

/-!
# Auxiliary lemmas for the chart of an open cell of the cycle model

* `Work.RatHurewicz.isClosed_rawWeight_le'` and `isOpen_rawWeight_ge'`: the weight function
  `rawWeight D : Raw D → ℕ` is upper semicontinuous (the sets `{rawWeight ≤ m}` are closed).
* `Work.RatHurewicz.continuous_transportPt`: the transport map of a stratum
  `y ↦ transportPt y _ τ _` is continuous in the point.
* `Work.RatHurewicz.rawBall`: the set of points of the `j`-th copy of the simplex at distance
  `< δ` from `y`; it is open in `Raw D` (`isOpen_rawBall`).
-/

open scoped Topology Simplicial unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {n : ℕ}

/-! ## 1. The weight is upper semicontinuous on `Raw` -/

theorem isClosed_ptSupport_card_le (m : ℕ) :
    IsClosed (setOf (fun x : stdSimplex ℝ (Fin (n + 2)) => (ptSupport x).card ≤ m)) := by
  have hkey : setOf (fun x : stdSimplex ℝ (Fin (n + 2)) => (ptSupport x).card ≤ m)
      = ⋂ T : {T : Finset (Fin (n + 2)) // m + 1 ≤ T.card},
          setOf (fun x : stdSimplex ℝ (Fin (n + 2)) =>
            ∏ t ∈ (T.1 : Finset (Fin (n + 2))), (x : Fin (n + 2) → ℝ) t = 0) := by
    ext x
    rw [Set.mem_iInter]
    constructor
    · intro hx T
      have hnotsub : ¬ ((T.1 : Finset (Fin (n + 2))) ⊆ ptSupport x) := by
        intro hsub
        have h1 : (T.1 : Finset (Fin (n + 2))).card ≤ (ptSupport x).card :=
          Finset.card_le_card hsub
        have h2 : m + 1 ≤ (T.1 : Finset (Fin (n + 2))).card := T.2
        have h3 : (ptSupport x).card ≤ m := hx
        omega
      obtain ⟨t, ht, htn⟩ := Finset.not_subset.mp hnotsub
      refine Finset.prod_eq_zero ht ?_
      rw [mem_ptSupport] at htn
      exact not_not.mp htn
    · intro hx
      by_contra hcon
      have hcon' : ¬ ((ptSupport x).card ≤ m) := hcon
      have hle : m + 1 ≤ (ptSupport x).card := by omega
      have hT : (∏ t ∈ ptSupport x, (x : Fin (n + 2) → ℝ) t) = 0 := hx ⟨ptSupport x, hle⟩
      have hne : (∏ t ∈ ptSupport x, (x : Fin (n + 2) → ℝ) t) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun t ht => mem_ptSupport.mp ht
      exact hne hT
  rw [hkey]
  exact isClosed_iInter fun T => isClosed_eq
    (continuous_finsetProd _ fun t _ =>
      (continuous_apply t).comp continuous_subtype_val) continuous_const

theorem isClosed_rawWeight_le' (D : MData X n x₀) (m : ℕ) :
    IsClosed (setOf (fun a : Raw D => rawWeight D a ≤ m)) := by
  rw [isClosed_sum_iff]
  constructor
  · have hpre : Sum.inl ⁻¹' setOf (fun a : Raw D => rawWeight D a ≤ m)
        = setOf (fun p : Sigma (fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))) =>
            (ptSupport p.2).card ≤ m) := rfl
    rw [hpre, isClosed_sigma_iff]
    intro i
    exact isClosed_ptSupport_card_le m
  · have hpre : Sum.inr ⁻¹' setOf (fun a : Raw D => rawWeight D a ≤ m)
        = setOf (fun _ : Sigma (fun _ : D.Idx => unitInterval) => 1 ≤ m) := rfl
    rw [hpre]
    have hconst : setOf (fun _ : Sigma (fun _ : D.Idx => unitInterval) => 1 ≤ m)
        = (fun _ : Sigma (fun _ : D.Idx => unitInterval) => m) ⁻¹' Set.Ici 1 := rfl
    rw [hconst]
    exact isClosed_Ici.preimage continuous_const

theorem isOpen_rawWeight_ge' (D : MData X n x₀) (m : ℕ) :
    IsOpen (setOf (fun a : Raw D => m ≤ rawWeight D a)) := by
  cases m with
  | zero =>
    have : setOf (fun a : Raw D => 0 ≤ rawWeight D a) = Set.univ :=
      Set.eq_univ_iff_forall.mpr fun a => Nat.zero_le _
    rw [this]; exact isOpen_univ
  | succ k =>
    have h : setOf (fun a : Raw D => k + 1 ≤ rawWeight D a)
        = ((rawWeight D) ⁻¹' setOf (fun x : ℕ => x ≤ k))ᶜ := by
      ext a
      show (k + 1 ≤ rawWeight D a) ↔ ¬ (rawWeight D a ≤ k)
      omega
    rw [h]
    exact (isClosed_rawWeight_le' D k).isOpen_compl

/-! ## 2. The transport map of a stratum and the balls of `Raw` -/

/-- The transport map of a stratum is continuous in the point. -/
theorem continuous_transportPt {T : Finset (Fin (n + 2))} {τ : {t // t ∈ T} → Fin (n + 2)}
    (hτ : Function.Injective τ) :
    Continuous (fun y : {y : stdSimplex ℝ (Fin (n + 2)) // ptSupport y = T} =>
      (transportPt y.1 y.2 τ hτ : Fin (n + 2) → ℝ)) := by
  refine continuous_pi fun w => ?_
  simp only [transportPt_apply]
  refine continuous_finset_sum _ fun t _ => ?_
  by_cases ht : τ t = w
  · simp only [ht, if_true]
    exact (continuous_apply (t : Fin (n + 2))).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  · simp only [ht, if_false]
    exact continuous_const

/-- The transport of a point of the stratum `T` depends on the support proof only through the
point. -/
theorem transportPt_congr {T : Finset (Fin (n + 2))} (x : stdSimplex ℝ (Fin (n + 2)))
    (h1 h2 : ptSupport x = T) (τ : {t // t ∈ T} → Fin (n + 2))
    (hτ1 hτ2 : Function.Injective τ) :
    transportPt x h1 τ hτ1 = transportPt x h2 τ hτ2 := by
  refine Subtype.ext (funext fun w => ?_)
  show (transportPt x h1 τ hτ1 : Fin (n + 2) → ℝ) w
    = (transportPt x h2 τ hτ2 : Fin (n + 2) → ℝ) w
  rfl

/-- A raw point whose weight is not `1` lies in a copy of the simplex. -/
theorem exists_eq_inl_of_rawWeight_ne_one {D : MData X n x₀} {a : Raw D}
    (h : rawWeight D a ≠ 1) : ∃ (j : D.Idx) (y : stdSimplex ℝ (Fin (n + 2))),
      a = Sum.inl (⟨j, y⟩ : Sigma fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))) := by
  cases a with
  | inl p => exact ⟨p.1, p.2, rfl⟩
  | inr p => exact absurd (rawWeight_inr D p.1 p.2) h

/-- The points of the `j`-th copy of the simplex at distance `< δ` from `y`, as a subset of
`Raw D`. -/
def rawBall (D : MData X n x₀) (j : D.Idx) (y : stdSimplex ℝ (Fin (n + 2))) (δ : ℝ) :
    Set (Raw D) :=
  Sum.inl '' setOf (fun p : Sigma (fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2))) =>
    p.1 = j ∧ dist (p.2 : stdSimplex ℝ (Fin (n + 2))) y < δ)

theorem mem_rawBall {D : MData X n x₀} {j : D.Idx} {y : stdSimplex ℝ (Fin (n + 2))}
    {δ : ℝ} {p : Sigma (fun _ : D.Idx => stdSimplex ℝ (Fin (n + 2)))} :
    Sum.inl p ∈ rawBall D j y δ ↔ p.1 = j ∧ dist (p.2 : stdSimplex ℝ (Fin (n + 2))) y < δ := by
  rw [rawBall]
  constructor
  · rintro ⟨q, ⟨hq1, hq2⟩, hqp⟩
    have hpq : q = p := Sum.inl.inj hqp
    rw [← hpq]
    exact ⟨hq1, hq2⟩
  · intro h
    exact ⟨p, h, rfl⟩

theorem isOpen_rawBall (D : MData X n x₀) (j : D.Idx) (y : stdSimplex ℝ (Fin (n + 2)))
    (δ : ℝ) : IsOpen (rawBall D j y δ) := by
  rw [rawBall, isOpen_sum_iff]
  constructor
  · rw [Sum.inl_injective.preimage_image, isOpen_sigma_iff]
    intro j'
    by_cases hj' : j' = j
    · rw [hj']
      have hball : (Sigma.mk j ⁻¹' setOf (fun p : Sigma (fun _ : D.Idx =>
          stdSimplex ℝ (Fin (n + 2))) => p.1 = j ∧
            dist (p.2 : stdSimplex ℝ (Fin (n + 2))) y < δ)) = Metric.ball y δ := by
        ext z
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Metric.mem_ball]
        exact ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
      rw [hball]
      exact Metric.isOpen_ball
    · have hem : (Sigma.mk j' ⁻¹' setOf (fun p : Sigma (fun _ : D.Idx =>
          stdSimplex ℝ (Fin (n + 2))) => p.1 = j ∧
            dist (p.2 : stdSimplex ℝ (Fin (n + 2))) y < δ)) = ∅ := by
        ext z
        simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hj' h.1
      rw [hem]
      exact isOpen_empty
  · have hem : Sum.inr ⁻¹' (Sum.inl '' setOf (fun p : Sigma (fun _ : D.Idx =>
        stdSimplex ℝ (Fin (n + 2))) => p.1 = j ∧
          dist (p.2 : stdSimplex ℝ (Fin (n + 2))) y < δ)) =
        (∅ : Set (Sigma (fun _ : D.Idx => unitInterval))) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      rintro ⟨p, -, hp⟩
      exact Sum.inl_ne_inr hp
    rw [hem]
    exact isOpen_empty

end

end Work.RatHurewicz
