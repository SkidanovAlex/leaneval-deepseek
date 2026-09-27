import Mathlib
import Submission.Work.EKLComp.MaxLeafDefs
import Submission.Work.EKLComp.MaxLeafAux
import Submission.Work.EKLComp.besicovitch_maximal
import Submission.Work.EKLContract.Lemmas.Box1_Uij
import Submission.Work.EKLContract.Lemmas.Uij_range
import Submission.Work.EKLContract.Lemmas.isHoro_Uij
import Submission.Work.EKLContract.Lemmas.mkX_mul

/-!
# `Work.EKLComp.atom_bad_bound`

The one-leaf Besicovitch maximal inequality behind the maximal inequality for leafwise
measures (EKL (10), L06 Thm A.1).

Fix a plaque algebra `(Z, m)` for the root group `U = U_ij` and a point `x ∈ Z ∩ X'`.
Writing `u(t) = u_ij(t)` and `λ = (ν x).map (g ↦ g_{ij})` for the leafwise measure `ν x`
read in the root coordinate, a point `y = u(a) • x` of the leaf which is bad at scale `q`
for the *leafwise measure at `y`* is exactly a "bad centre `a` at scale `q`" for `λ`:

  `ofReal α * λ (closedBall a q)  <  ∫⁻ t in closedBall a q, ofReal (f (u(t) • x)) ∂λ`.

The geometric hypothesis `hYball` (the `U`-ball of radius `r̄` around a bad point `y` stays in
the atom of `y`, hence in the atom of `x`) guarantees that the bad balls of radius `< r̄` stay
inside the shape of `x`, so that the one-dimensional Besicovitch covering theorem — as an
abstract hypothesis `hcover` — can be applied on the shape and produces the bound.
-/

namespace Work.EKLComp

open MeasureTheory
open Work.EKLContract
open scoped ENNReal

noncomputable section

variable {i j : Fin 3}

/-! ## 1. Coordinates on the root group `U_ij` -/

/-- The `(i,j)`-entry of a matrix, used as the coordinate of the root group `U_ij`. -/
abbrev lcoord (i j : Fin 3) (g : SL3) : ℝ := (g : Matrix (Fin 3) (Fin 3) ℝ) i j

/-- The one-parameter root group `U_ij ≅ ℝ` as a map `ℝ → SL₃(ℝ)`. -/
abbrev rmap {i j : Fin 3} (hij : i ≠ j) (t : ℝ) : SL3 := uij hij t

theorem rmap_mem (hij : i ≠ j) (t : ℝ) : rmap hij t ∈ (Uij hij : Set SL3) :=
  (Lemmas.mem_Uij_iff hij _).mpr ⟨t, rfl⟩

theorem lcoord_rmap (hij : i ≠ j) (t : ℝ) : lcoord i j (rmap hij t) = t :=
  Lemmas.uij_apply_self hij t

theorem rmap_lcoord (hij : i ≠ j) {g : SL3} (hg : g ∈ Uij hij) : rmap hij (lcoord i j g) = g :=
  (eq_uij_entry hij hg).symm

theorem rmap_add (hij : i ≠ j) (a b : ℝ) : rmap hij (a + b) = rmap hij a * rmap hij b := by
  show Matrix.SpecialLinearGroup.transvection hij (a + b)
      = Matrix.SpecialLinearGroup.transvection hij a
        * Matrix.SpecialLinearGroup.transvection hij b
  exact Matrix.SpecialLinearGroup.transvection_add hij a b

theorem rmap_injective (hij : i ≠ j) : Function.Injective (rmap hij) := uij_injective hij

/-- Right multiplication of an element of `U_ij` by `u_ij(σ)`, in the root coordinate. -/
theorem lcoord_mul_rmap (hij : i ≠ j) {g : SL3} (hg : g ∈ Uij hij) (σ : ℝ) :
    lcoord i j (g * rmap hij σ) = lcoord i j g + σ := by
  obtain ⟨s, hs⟩ := (Lemmas.mem_Uij_iff hij g).mp hg
  rw [← hs, show rmap hij s * rmap hij σ = rmap hij (s + σ) from (rmap_add hij s σ).symm,
    lcoord_rmap hij (s + σ), lcoord_rmap hij s]

/-- The coordinate `(i,j)` identifies `U_ij` with `ℝ`: preimages of sets are images of the
transvection parametrisation. -/
theorem preimage_lcoord_image (hij : i ≠ j) (A : Set ℝ) :
    lcoord i j ⁻¹' A ∩ (Uij hij : Set SL3) = rmap hij '' A := by
  ext g
  constructor
  · rintro ⟨hgA, hgU⟩
    exact ⟨lcoord i j g, hgA, (eq_uij_entry hij hgU).symm⟩
  · rintro ⟨t, htA, rfl⟩
    refine ⟨?_, rmap_mem hij t⟩
    show lcoord i j (rmap hij t) ∈ A
    rwa [lcoord_rmap hij t]

/-! ## 2. The root-group balls -/

theorem mem_ballU_rmap (hij : i ≠ j) (R s : ℝ) :
    rmap hij s ∈ (ballU hij R : Set SL3) ↔ |s| ≤ R := by
  constructor
  · rintro ⟨t, ht, hts⟩
    have h1 : t = s := rmap_injective hij hts
    subst h1
    exact abs_le.mpr ⟨ht.1, ht.2⟩
  · intro hs
    exact ⟨s, abs_le.mp hs, rfl⟩

theorem mem_ballU_lcoord (hij : i ≠ j) {g : SL3} (hg : g ∈ Uij hij) (R : ℝ) :
    g ∈ (ballU hij R : Set SL3) ↔ |lcoord i j g| ≤ R := by
  conv_lhs => rw [← rmap_lcoord hij hg]
  exact mem_ballU_rmap hij R (lcoord i j g)

theorem measurableSet_ballU (hij : i ≠ j) (R : ℝ) :
    MeasurableSet (ballU hij R : Set SL3) :=
  (isCompact_Icc.image (Lemmas.horoUij_cont hij)).isClosed.measurableSet

theorem measurableSet_Uij (hij : i ≠ j) :
    MeasurableSet ((Uij hij : Subgroup SL3) : Set SL3) :=
  (Lemmas.horoUij_isClosed hij).measurableSet

/-- The set of `g` with `g * u_ij(-σ) ∈ B(0,q)` is the transvection image of `[σ-q, σ+q]`. -/
theorem preimage_mul_rmap_neg_ballU (hij : i ≠ j) (σ q : ℝ) :
    (fun g : SL3 => g * rmap hij (-σ)) ⁻¹' (ballU hij q : Set SL3)
      = rmap hij '' Metric.closedBall σ q := by
  ext g
  rw [Set.mem_preimage]
  constructor
  · intro hg
    have hU : g * rmap hij (-σ) ∈ (Uij hij : Set SL3) := by
      obtain ⟨t, -, hgt⟩ := hg
      rw [← hgt]
      exact rmap_mem hij t
    have hgU : g ∈ (Uij hij : Set SL3) := by
      have h2 : (g * rmap hij (-σ)) * (rmap hij (-σ))⁻¹ ∈ (Uij hij : Set SL3) :=
        (Uij hij).mul_mem hU ((Uij hij).inv_mem (rmap_mem hij (-σ)))
      simpa [mul_assoc] using h2
    have h4 : |lcoord i j g + (-σ)| ≤ q := by
      rw [← lcoord_mul_rmap hij hgU (-σ)]
      exact (mem_ballU_lcoord hij hU q).mp hg
    refine ⟨lcoord i j g, ?_, rmap_lcoord hij hgU⟩
    rw [Metric.mem_closedBall, Real.dist_eq, sub_eq_add_neg]
    exact h4
  · rintro ⟨t, ht, rfl⟩
    rw [Metric.mem_closedBall, Real.dist_eq, sub_eq_add_neg] at ht
    show rmap hij t * rmap hij (-σ) ∈ (ballU hij q : Set SL3)
    rw [← rmap_add hij t (-σ), mem_ballU_rmap hij q (t + (-σ))]
    exact ht

/-- Within `U_ij`, membership in `g * u_ij(-a) ∈ B(0,q)` is `lcoord g ∈ [a-q, a+q]`. -/
theorem mul_rmap_neg_mem_ballU (hij : i ≠ j) {g : SL3} (hg : g ∈ Uij hij) (a q : ℝ) :
    g * rmap hij (-a) ∈ (ballU hij q : Set SL3) ↔ lcoord i j g ∈ Metric.closedBall a q := by
  have h1 : g * rmap hij (-a) ∈ (Uij hij : Set SL3) :=
    (Uij hij).mul_mem hg (rmap_mem hij (-a))
  rw [mem_ballU_lcoord hij h1 q, lcoord_mul_rmap hij hg (-a),
    Metric.mem_closedBall, Real.dist_eq, sub_eq_add_neg]

/-! ## 3. Measurability -/

theorem measurable_lcoord (i j : Fin 3) : Measurable (lcoord i j) := by
  have hrow : Continuous fun A : SL3 => A i :=
    Matrix.SpecialLinearGroup.continuous_apply _ continuous_id i
  exact ((continuous_apply j).comp hrow).measurable

theorem measurable_rmap (hij : i ≠ j) : Measurable (rmap hij) :=
  (Lemmas.horoUij_cont hij).measurable

theorem measurable_smul_x (x : X3) : Measurable fun g : SL3 => g • x := by
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective x
  rw [show (fun g : SL3 => g • (QuotientGroup.mk g₀ : X3)) = fun g : SL3 => mkX (g * g₀) from by
    funext g; exact (Lemmas.mkX_mul g g₀).symm]
  exact (QuotientGroup.continuous_mk.measurable).comp (continuous_mul_const g₀).measurable

theorem measurable_rmap_smul_x (hij : i ≠ j) (x : X3) :
    Measurable fun t : ℝ => rmap hij t • x :=
  (measurable_smul_x x).comp (measurable_rmap hij)

theorem measurableSet_shape (hij : i ≠ j) (m : MeasurableSpace X3) (Z : Set X3)
    (hplaque : IsPlaqueAlgebra (Uij hij) Z m) {x : X3} (hx : x ∈ Z) :
    MeasurableSet (shape m (Uij hij) x) := by
  obtain ⟨O, hO, hshape⟩ := (hplaque.2.2.2 x hx).2.2.1
  rw [hshape]
  exact hO.measurableSet.inter (measurableSet_Uij hij)

theorem measurableEmbedding_rmap (hij : i ≠ j) : MeasurableEmbedding (rmap hij) := by
  refine MeasurableEmbedding.of_measurable_inverse (g := fun g : SL3 => lcoord i j g) ?_ ?_ ?_ ?_
  · exact measurable_rmap hij
  · rw [← Lemmas.Uij_range hij]
    exact (Lemmas.horoUij_isClosed hij).measurableSet
  · exact measurable_lcoord i j
  · intro t
    exact lcoord_rmap hij t

theorem measurableSet_shape_coord (hij : i ≠ j) (m : MeasurableSpace X3) (Z : Set X3)
    (hplaque : IsPlaqueAlgebra (Uij hij) Z m) {x : X3} (hx : x ∈ Z) :
    MeasurableSet {t : ℝ | rmap hij t ∈ shape m (Uij hij) x} := by
  obtain ⟨O, hO, hshape⟩ := (hplaque.2.2.2 x hx).2.2.1
  have hset : {t : ℝ | rmap hij t ∈ shape m (Uij hij) x} = rmap hij ⁻¹' O := by
    ext t
    constructor
    · intro h
      rw [Set.mem_preimage]
      rw [hshape] at h
      exact h.1
    · intro h
      rw [Set.mem_preimage] at h
      rw [hshape]
      exact ⟨h, rmap_mem hij t⟩
  rw [hset]
  exact ((Lemmas.horoUij_cont hij).isOpen_preimage O hO).measurableSet


/-! ## 4. The leafwise measure read in the root coordinate -/

/-- The measure `ν x` of the transvection image of a measurable set, computed with the
coordinate measure `(ν x).map (g ↦ g_{ij})`.  No null set is lost because `ν x` is carried by
`U_ij`. -/
theorem lcoord_map_apply (hij : i ≠ j) (νm : Measure SL3)
    (hcar : νm ((Uij hij : Subgroup SL3) : Set SL3)ᶜ = 0) {B : Set ℝ} (hB : MeasurableSet B) :
    (νm.map (lcoord i j)) B = νm (rmap hij '' B) := by
  have hae : ∀ᵐ g ∂νm, g ∈ (Uij hij : Set SL3) := by
    rw [ae_iff]; exact hcar
  have hrestr : νm.restrict ((Uij hij : Subgroup SL3) : Set SL3) = νm :=
    Measure.restrict_eq_self_of_ae_mem hae
  rw [Measure.map_apply_of_aemeasurable (measurable_lcoord i j).aemeasurable hB]
  calc νm (lcoord i j ⁻¹' B)
      = (νm.restrict ((Uij hij : Subgroup SL3) : Set SL3)) (lcoord i j ⁻¹' B) := by rw [hrestr]
    _ = νm ((lcoord i j ⁻¹' B) ∩ ((Uij hij : Subgroup SL3) : Set SL3)) :=
          Measure.restrict_apply' (measurableSet_Uij hij)
    _ = νm (rmap hij '' B) := by rw [preimage_lcoord_image hij B]

/-- The coordinate measure dominates `νm` on transvection images of arbitrary sets. -/
theorem le_lcoord_apply (hij : i ≠ j) (νm : Measure SL3) (A : Set ℝ) :
    νm (rmap hij '' A) ≤ (νm.map (lcoord i j)) A := by
  calc νm (rmap hij '' A)
      = νm (lcoord i j ⁻¹' A ∩ (Uij hij : Set SL3)) := by rw [preimage_lcoord_image hij A]
    _ ≤ νm (lcoord i j ⁻¹' A) := measure_mono Set.inter_subset_left
    _ ≤ (νm.map (lcoord i j)) A := Measure.le_map_apply (measurable_lcoord i j).aemeasurable A

/-- Change of variables for the coordinate measure on a measurable set of parameters. -/
theorem lintegral_lcoord (hij : i ≠ j) (νm : Measure SL3)
    (hcar : νm ((Uij hij : Subgroup SL3) : Set SL3)ᶜ = 0) {A : Set ℝ} (hA : MeasurableSet A)
    {H : ℝ → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ t in A, H t ∂(νm.map (lcoord i j))
      = ∫⁻ g in (rmap hij '' A), H (lcoord i j g) ∂νm := by
  classical
  have hA' : MeasurableSet (rmap hij '' A) :=
    (measurableEmbedding_rmap hij).measurableSet_image.mpr hA
  rw [← lintegral_indicator hA H, ← lintegral_indicator hA' (fun g => H (lcoord i j g))]
  rw [lintegral_map (hH.indicator hA) (measurable_lcoord i j)]
  apply lintegral_congr_ae
  have hae : ∀ᵐ g ∂νm, g ∈ (Uij hij : Set SL3) := by
    rw [ae_iff]; exact hcar
  filter_upwards [hae] with g hg
  have hiff : lcoord i j g ∈ A ↔ g ∈ rmap hij '' A := by
    rw [← preimage_lcoord_image hij A]
    exact ⟨fun h => ⟨h, hg⟩, fun h => h.1⟩
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hc : lcoord i j g ∈ A
  · rw [if_pos hc, if_pos (hiff.mp hc)]
  · rw [if_neg hc, if_neg (fun h => hc (hiff.mpr h))]

/-! ## 5. The elementary leaf identity -/

/-- Translating a point of the leaf: `(g u(-a)) • (u(a) • x) = u(lcoord g) • x` for
`g ∈ U_ij`. -/
theorem mul_rmap_neg_smul (hij : i ≠ j) {g : SL3} (hg : g ∈ Uij hij) (a : ℝ) (x : X3) :
    (g * rmap hij (-a)) • (rmap hij a • x) = rmap hij (lcoord i j g) • x := by
  have hg' : g = rmap hij (lcoord i j g) := (rmap_lcoord hij hg).symm
  conv_lhs => rw [hg']
  rw [← mul_smul, ← rmap_add hij (lcoord i j g) (-a),
      ← rmap_add hij (lcoord i j g + -a) a,
      show (lcoord i j g + -a) + a = lcoord i j g from by ring]

/-! ## 6. Badness of a leaf point is badness of a centre for the coordinate measure -/

/-- **The transfer lemma.**  If `y = u(a) • x` lies in `X'` and is bad at scale `q` for the
leafwise measure `ν y`, then the parameter `a` is a bad centre at scale `q` for the coordinate
measure `(ν x).map (g ↦ g_{ij})`. -/
theorem bad_transfer (hij : i ≠ j) (μ : Measure X3) (ν : X3 → Measure SL3) (X' : Set X3)
    (hν : IsLeafwise μ (Uij hij) ν X') (f : X3 → ℝ) (hf : Measurable f) (α a q : ℝ) (x : X3)
    (hxX : x ∈ X') (haX : rmap hij a • x ∈ X')
    (hbad : BadENN i j hij ν f (rmap hij a • x) α q) :
    ENNReal.ofReal α * ((ν x).map (lcoord i j)) (Metric.closedBall a q)
      < ∫⁻ t in Metric.closedBall a q, ENNReal.ofReal (f (rmap hij t • x))
          ∂((ν x).map (lcoord i j)) := by
  classical
  have hcar : ν x ((Uij hij : Subgroup SL3) : Set SL3)ᶜ = 0 := hν.carried x hxX
  have hCmeas : MeasurableSet (Metric.closedBall a q : Set ℝ) :=
    Metric.isClosed_closedBall.measurableSet
  have hBmeas : MeasurableSet (ballU hij q : Set SL3) := measurableSet_ballU hij q
  have hneg : rmap hij (-a) ∈ (Uij hij : Set SL3) := rmap_mem hij (-a)
  have hsm : rmap hij (-a) • (rmap hij a • x) = x := by
    rw [← mul_smul, ← rmap_add hij (-a) a, neg_add_cancel]
    rw [show rmap hij (0 : ℝ) = (1 : SL3) from Lemmas.horoUij_zero hij, one_smul]
  obtain ⟨c, hc0, hctop, hc⟩ :=
    hν.equivariant (rmap hij a • x) haX (rmap hij (-a)) hneg (by rw [hsm]; exact hxX)
  rw [hsm] at hc
  have hLHS : ν (rmap hij a • x) (ballU hij q)
      = c * ((ν x).map (lcoord i j)) (Metric.closedBall a q) := by
    rw [hc, Measure.smul_apply, smul_eq_mul, Measure.map_apply_of_aemeasurable
        ((continuous_mul_const (rmap hij (-a))).measurable).aemeasurable hBmeas,
      preimage_mul_rmap_neg_ballU hij a q, ← lcoord_map_apply hij (ν x) hcar hCmeas]
  have hRHS : ∫⁻ g in ballU hij q, ENNReal.ofReal (f (g • (rmap hij a • x)))
        ∂(ν (rmap hij a • x))
      = c * ∫⁻ t in Metric.closedBall a q, ENNReal.ofReal (f (rmap hij t • x))
          ∂((ν x).map (lcoord i j)) := by
    rw [hc, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
    congr 1
    have hK : Measurable fun g : SL3 => ENNReal.ofReal (f (g • (rmap hij a • x))) :=
      ENNReal.measurable_ofReal.comp (hf.comp (measurable_smul_x _))
    have hY : Measurable fun t : ℝ => ENNReal.ofReal (f (rmap hij t • x)) :=
      ENNReal.measurable_ofReal.comp (hf.comp (measurable_rmap_smul_x hij x))
    rw [← lintegral_indicator hBmeas (fun g : SL3 => ENNReal.ofReal (f (g • (rmap hij a • x)))),
      ← lintegral_indicator hCmeas (fun t : ℝ => ENNReal.ofReal (f (rmap hij t • x)))]
    conv_rhs => rw [lintegral_map (hY.indicator hCmeas) (measurable_lcoord i j)]
    rw [lintegral_map (hK.indicator hBmeas) (continuous_mul_const (rmap hij (-a))).measurable]
    apply lintegral_congr_ae
    have hae : ∀ᵐ g ∂(ν x), g ∈ (Uij hij : Set SL3) := by
      rw [ae_iff]; exact hcar
    filter_upwards [hae] with g hg
    have hiff := mul_rmap_neg_mem_ballU hij hg a q
    have hval : ENNReal.ofReal (f ((g * rmap hij (-a)) • (rmap hij a • x)))
        = ENNReal.ofReal (f (rmap hij (lcoord i j g) • x)) := by
      rw [mul_rmap_neg_smul hij hg a x]
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hcond : g * rmap hij (-a) ∈ (ballU hij q : Set SL3)
    · rw [if_pos hcond, if_pos (hiff.mp hcond), hval]
    · rw [if_neg hcond, if_neg (fun h => hcond (hiff.mpr h))]
  have h := hbad
  unfold BadENN at h
  rw [hLHS, hRHS] at h
  have h' : (ENNReal.ofReal α * ((ν x).map (lcoord i j)) (Metric.closedBall a q)) * c
      < (∫⁻ t in Metric.closedBall a q, ENNReal.ofReal (f (rmap hij t • x))
            ∂((ν x).map (lcoord i j))) * c := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using h
  exact (ENNReal.mul_lt_mul_iff_left hc0 hctop).mp h'


/-! ## 7. The main lemma -/

theorem atom_bad_bound (N : ℕ)
    (hcover : ∀ (A : Set ℝ) (r : A → ℝ), (∀ a, 0 < r a) → (∃ ρ : ℝ, ∀ a, r a ≤ ρ) →
      ∃ s : Fin N → Set A,
        (∀ i, (s i).PairwiseDisjoint fun a => Metric.closedBall (a : ℝ) (r a)) ∧
        A ⊆ ⋃ i, ⋃ a ∈ s i, Metric.ball (a : ℝ) (r a))
    (i j : Fin 3) (hij : i ≠ j) (μ : MeasureTheory.Measure Work.EKLContract.X3)
    [MeasureTheory.IsProbabilityMeasure μ]
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3)
    (X' : Set Work.EKLContract.X3)
    (hν : Work.EKLContract.IsLeafwise μ (Work.EKLContract.Uij hij) ν X')
    (f : Work.EKLContract.X3 → ℝ) (hf : Measurable f) (α rbar : ℝ) (hr : 0 < rbar)
    (m : MeasurableSpace Work.EKLContract.X3) (Z : Set Work.EKLContract.X3)
    (hZfree : Z ⊆ Work.EKLComp.Free i j hij)
    (hplaque : Work.EKLContract.IsPlaqueAlgebra (Work.EKLContract.Uij hij) Z m)
    (Y : Set Work.EKLContract.X3) (hY : Y ⊆ X' ∩ Work.EKLComp.Free i j hij)
    (hYbad : ∀ y ∈ Y, ∃ q : ℚ, 0 < q ∧ (q : ℝ) < rbar ∧
      Work.EKLComp.BadENN i j hij ν f y α (q : ℝ))
    (hYball : ∀ y ∈ Y, ∀ u ∈ (Work.EKLContract.ballU hij rbar : Set Work.EKLContract.SL3),
      u • y ∈ Work.EKLContract.atom m y)
    (x : Work.EKLContract.X3) (hxZ : x ∈ Z) (hxX : x ∈ X') :
    ENNReal.ofReal α * ν x {u : Work.EKLContract.SL3 |
        u ∈ Work.EKLContract.shape m (Work.EKLContract.Uij hij) x ∧ u • x ∈ Y}
      ≤ (N : ENNReal) * ∫⁻ u in Work.EKLContract.shape m (Work.EKLContract.Uij hij) x,
          ENNReal.ofReal (f (u • x)) ∂(ν x) := by
  classical
  have hcar : ν x ((Uij hij : Subgroup SL3) : Set SL3)ᶜ = 0 := hν.carried x hxX
  set S : Set SL3 := shape m (Uij hij) x with hS
  set T : Set ℝ := {t : ℝ | rmap hij t ∈ S} with hT
  set A : Set ℝ := {t : ℝ | rmap hij t ∈ S ∧ rmap hij t • x ∈ Y} with hAdef
  have hSmeas : MeasurableSet S := measurableSet_shape hij m Z hplaque hxZ
  have hTmeas : MeasurableSet T := measurableSet_shape_coord hij m Z hplaque hxZ
  have hA_sub_T : A ⊆ T := fun t ht => ht.1
  have hS_eq : S = rmap hij '' T := by
    ext u
    constructor
    · intro hu
      refine ⟨lcoord i j u, ?_, rmap_lcoord hij hu.1⟩
      show rmap hij (lcoord i j u) ∈ S
      rw [rmap_lcoord hij hu.1]
      exact hu
    · rintro ⟨t, ht, rfl⟩
      exact ht
  have hE_eq : {u : SL3 | u ∈ S ∧ u • x ∈ Y} = rmap hij '' A := by
    ext u
    constructor
    · rintro ⟨huS, huY⟩
      refine ⟨lcoord i j u, ⟨?_, ?_⟩, rmap_lcoord hij huS.1⟩
      · show rmap hij (lcoord i j u) ∈ S
        rw [rmap_lcoord hij huS.1]; exact huS
      · show rmap hij (lcoord i j u) • x ∈ Y
        rw [rmap_lcoord hij huS.1]; exact huY
    · rintro ⟨t, ⟨htT, htY⟩, rfl⟩
      exact ⟨htT, htY⟩
  -- the rational bad radius of a bad point of the leaf
  let r : ℝ → ℝ := fun t => if h : ∃ q : ℚ, 0 < q ∧ (q : ℝ) < rbar ∧
      BadENN i j hij ν f (rmap hij t • x) α (q : ℝ) then ((h.choose : ℚ) : ℝ) else 1
  have hr_pos : ∀ t ∈ A, 0 < r t := by
    intro t ht
    have hex : ∃ q : ℚ, 0 < q ∧ (q : ℝ) < rbar ∧
        BadENN i j hij ν f (rmap hij t • x) α (q : ℝ) := hYbad _ ht.2
    change 0 < (if h : ∃ q : ℚ, 0 < q ∧ (q : ℝ) < rbar ∧
      BadENN i j hij ν f (rmap hij t • x) α (q : ℝ) then ((h.choose : ℚ) : ℝ) else 1)
    rw [dif_pos hex]
    exact_mod_cast hex.choose_spec.1
  have hr_lt : ∀ t ∈ A, r t < rbar := by
    intro t ht
    have hex : ∃ q : ℚ, 0 < q ∧ (q : ℝ) < rbar ∧
        BadENN i j hij ν f (rmap hij t • x) α (q : ℝ) := hYbad _ ht.2
    change (if h : ∃ q : ℚ, 0 < q ∧ (q : ℝ) < rbar ∧
      BadENN i j hij ν f (rmap hij t • x) α (q : ℝ) then ((h.choose : ℚ) : ℝ) else 1) < rbar
    rw [dif_pos hex]
    exact_mod_cast hex.choose_spec.2.1
  have hr_bad : ∀ t ∈ A, BadENN i j hij ν f (rmap hij t • x) α (r t) := by
    intro t ht
    have hex : ∃ q : ℚ, 0 < q ∧ (q : ℝ) < rbar ∧
        BadENN i j hij ν f (rmap hij t • x) α (q : ℝ) := hYbad _ ht.2
    change BadENN i j hij ν f (rmap hij t • x) α
      (if h : ∃ q : ℚ, 0 < q ∧ (q : ℝ) < rbar ∧
        BadENN i j hij ν f (rmap hij t • x) α (q : ℝ) then ((h.choose : ℚ) : ℝ) else 1)
    rw [dif_pos hex]
    exact hex.choose_spec.2.2
  -- the radius balls stay inside the shape
  have hsub : ∀ t ∈ A, Metric.closedBall t (r t) ⊆ T := by
    intro t ht s hs
    have h1 : |s - t| ≤ r t := by
      have h1' := Metric.mem_closedBall.mp hs
      rwa [Real.dist_eq] at h1'
    have h2 : |s - t| ≤ rbar := le_trans h1 (le_of_lt (hr_lt t ht))
    have h3 : rmap hij (s - t) ∈ (ballU hij rbar : Set SL3) :=
      (mem_ballU_rmap hij rbar (s - t)).mpr h2
    have h4 : rmap hij (s - t) • (rmap hij t • x) ∈ atom m (rmap hij t • x) :=
      hYball _ ht.2 _ h3
    have h5 : atom m (rmap hij t • x) = atom m x := atom_eq_of_mem__MaxLeafAux ht.1.2
    rw [h5] at h4
    have h6 : rmap hij (s - t) • (rmap hij t • x) = rmap hij s • x := by
      rw [← mul_smul, ← rmap_add hij (s - t) t, sub_add_cancel]
    rw [h6] at h4
    exact ⟨rmap_mem hij s, h4⟩
  set lam : Measure ℝ := (ν x).map (lcoord i j) with hlam
  have hH : Measurable fun t : ℝ => ENNReal.ofReal (f (rmap hij t • x)) :=
    ENNReal.measurable_ofReal.comp (hf.comp (measurable_rmap_smul_x hij x))
  have hStepA : ν x (rmap hij '' A) ≤ (lam.restrict T) A := by
    have h1 : ν x (rmap hij '' A) ≤ lam A := le_lcoord_apply hij (ν x) A
    have h2 : (lam.restrict T) A = lam A := by
      rw [Measure.restrict_apply' hTmeas, Set.inter_eq_left.mpr hA_sub_T]
    rw [h2]; exact h1
  have hbadT : ∀ t ∈ A, ENNReal.ofReal α * (lam.restrict T) (Metric.closedBall t (r t))
      < ∫⁻ s in Metric.closedBall t (r t), ENNReal.ofReal (f (rmap hij s • x))
          ∂(lam.restrict T) := by
    intro t ht
    have hb := bad_transfer hij μ ν X' hν f hf α t (r t) x hxX (hY ht.2).1 (hr_bad t ht)
    have hBt : Metric.closedBall t (r t) ⊆ T := hsub t ht
    calc ENNReal.ofReal α * (lam.restrict T) (Metric.closedBall t (r t))
        = ENNReal.ofReal α * lam (Metric.closedBall t (r t)) := by
          rw [Measure.restrict_apply' hTmeas, Set.inter_eq_left.mpr hBt]
      _ < ∫⁻ s in Metric.closedBall t (r t), ENNReal.ofReal (f (rmap hij s • x)) ∂lam := hb
      _ = ∫⁻ s in Metric.closedBall t (r t), ENNReal.ofReal (f (rmap hij s • x))
            ∂(lam.restrict T) := by
          rw [Measure.restrict_restrict (μ := lam) Metric.isClosed_closedBall.measurableSet,
            Set.inter_eq_left.mpr hBt]
  have hbc := besicovitch_maximal N hcover (lam.restrict T)
      (fun t : ℝ => ENNReal.ofReal (f (rmap hij t • x))) (ENNReal.ofReal α) A r hr_pos
      ⟨rbar, fun t ht => le_of_lt (hr_lt t ht)⟩ hbadT
  have htr : ∫⁻ t, ENNReal.ofReal (f (rmap hij t • x)) ∂(lam.restrict T)
      = ∫⁻ u in S, ENNReal.ofReal (f (u • x)) ∂(ν x) := by
    rw [lintegral_lcoord hij (ν x) hcar hTmeas hH, ← hS_eq]
    rw [← lintegral_indicator hSmeas
          (fun u : SL3 => ENNReal.ofReal (f (rmap hij (lcoord i j u) • x))),
      ← lintegral_indicator hSmeas (fun u : SL3 => ENNReal.ofReal (f (u • x)))]
    apply lintegral_congr
    intro u
    by_cases hu : u ∈ S
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu]
      have : rmap hij (lcoord i j u) • x = u • x := by rw [rmap_lcoord hij hu.1]
      rw [this]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu]
  rw [htr] at hbc
  calc ENNReal.ofReal α * ν x {u : SL3 | u ∈ S ∧ u • x ∈ Y}
      = ENNReal.ofReal α * ν x (rmap hij '' A) := by rw [hE_eq]
    _ ≤ ENNReal.ofReal α * (lam.restrict T) A :=
          mul_le_mul_of_nonneg_left hStepA zero_le
    _ ≤ (N : ENNReal) * ∫⁻ u in S, ENNReal.ofReal (f (u • x)) ∂(ν x) := hbc

end

end Work.EKLComp
