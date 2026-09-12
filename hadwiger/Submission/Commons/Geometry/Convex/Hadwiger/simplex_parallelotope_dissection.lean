import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Commons.Analysis.Convex.convHull_zero_range

open Set Finset
open scoped BigOperators

namespace Commons.Geometry.Convex.Hadwiger

set_option linter.unusedVariables false in
noncomputable section

/-! # Dissection of a parallelotope into a simplex, its reflection, and a middle body

Helper coordinate facts for the theorem `simplex_parallelotope_dissection`.
All statements here are about the plain function space `Fin n → ℝ` (the
coordinate copy of the model space) unless explicitly about
`EuclideanSpace ℝ (Fin n)`. -/

abbrev CFun (n : ℕ) := Fin n → ℝ

/-- The all-ones coordinate vector. -/
def coordOne (n : ℕ) : CFun n := fun _ => 1

/-- The unit coordinate box `[0,1]ⁿ`. -/
def coordBox (n : ℕ) : Set (CFun n) := {t | ∀ i : Fin n, t i ∈ Set.Icc (0 : ℝ) 1}

/-- The coordinate simplex with vertices `0` and the standard basis vectors. -/
def coordSimplex (n : ℕ) : Set (CFun n) :=
  {t | (∀ i : Fin n, 0 ≤ t i) ∧ (∑ i : Fin n, t i) ≤ 1}

/-- The middle coordinate body `1 ≤ ∑ t ≤ n - 1` inside the box. -/
def coordMid (n : ℕ) : Set (CFun n) :=
  {t | (∀ i : Fin n, t i ∈ Set.Icc (0 : ℝ) 1) ∧ (1 : ℝ) ≤ ∑ i : Fin n, t i ∧
    ∑ i : Fin n, t i ≤ (n : ℝ) - 1}

/-- Coordinate reflection `t ↦ 1 - t`. -/
def coordReflect (n : ℕ) (t : CFun n) : CFun n := fun i => 1 - t i

lemma sumOne (n : ℕ) : (∑ i : Fin n, (1 : ℝ)) = (n : ℝ) := by
  simp

lemma sumCoordReflect (n : ℕ) (t : CFun n) :
    (∑ i : Fin n, coordReflect n t i) = (n : ℝ) - ∑ i : Fin n, t i := by
  dsimp [coordReflect]
  calc
    (∑ i : Fin n, ((1 : ℝ) - t i)) = (∑ i : Fin n, (1 : ℝ)) - ∑ i : Fin n, t i := by
      exact Finset.sum_sub_distrib (s := (Finset.univ : Finset (Fin n)))
        (f := fun _ : Fin n => (1 : ℝ)) (g := t)
    _ = (n : ℝ) - ∑ i : Fin n, t i := by rw [sumOne]

lemma coordReflect_involutive (n : ℕ) (t : CFun n) : coordReflect n (coordReflect n t) = t := by
  funext i
  dsimp [coordReflect]
  ring

lemma coordSimplex_subset_coordBox (n : ℕ) : coordSimplex n ⊆ coordBox n := by
  intro t ht i
  have h0 : 0 ≤ t i := ht.1 i
  have hle : t i ≤ 1 := by
    calc
      t i ≤ ∑ j : Fin n, t j := Finset.single_le_sum (fun j hj => ht.1 j) (Finset.mem_univ i)
      _ ≤ 1 := ht.2
  exact ⟨h0, hle⟩

lemma coordReflect_mem_coordBox_of_mem_coordSimplex (n : ℕ) {s : CFun n}
    (hs : s ∈ coordSimplex n) : coordReflect n s ∈ coordBox n := by
  intro i
  have hb := coordSimplex_subset_coordBox n hs i
  constructor <;> dsimp [coordReflect]
  · linarith [hb.2]
  · linarith [hb.1]

lemma coordReflect_coordSimplex_subset_coordBox (n : ℕ) :
    coordReflect n '' coordSimplex n ⊆ coordBox n := by
  rintro t ⟨s, hs, rfl⟩
  exact coordReflect_mem_coordBox_of_mem_coordSimplex n hs

lemma coordBox_eq_union (n : ℕ) :
    coordBox n = (coordSimplex n ∪ coordMid n) ∪ coordReflect n '' coordSimplex n := by
  ext t
  constructor
  · intro ht
    by_cases h1 : (∑ i : Fin n, t i) ≤ 1
    · left; left
      exact ⟨fun i => (ht i).1, h1⟩
    · by_cases h2 : (∑ i : Fin n, t i) ≤ (n : ℝ) - 1
      · left; right
        exact ⟨ht, le_of_lt (not_le.mp h1), h2⟩
      · right
        refine ⟨coordReflect n t, ?_, coordReflect_involutive n t⟩
        · constructor
          · intro i
            dsimp [coordReflect]
            linarith [(ht i).2]
          · rw [sumCoordReflect]
            have hlt : (n : ℝ) - 1 < ∑ i : Fin n, t i := not_le.mp h2
            linarith
  · rintro ((hS | hM) | hR)
    · exact coordSimplex_subset_coordBox n hS
    · exact hM.1
    · exact coordReflect_coordSimplex_subset_coordBox n hR

lemma coordReflect_mem_coordBox_of_mem_coordBox (n : ℕ) {t : CFun n} (ht : t ∈ coordBox n) :
    coordReflect n t ∈ coordBox n := by
  intro i
  have hb := ht i
  constructor <;> dsimp [coordReflect]
  · linarith [hb.2]
  · linarith [hb.1]

lemma coordReflect_mem_coordMid_of_mem (n : ℕ) {t : CFun n} (ht : t ∈ coordMid n) :
    coordReflect n t ∈ coordMid n := by
  refine ⟨?_, ?_⟩
  · exact coordReflect_mem_coordBox_of_mem_coordBox n ht.1
  · constructor
    · rw [sumCoordReflect]
      linarith [ht.2.2]
    · rw [sumCoordReflect]
      linarith [ht.2.1]

lemma coordMid_eq_reflect (n : ℕ) : coordReflect n '' coordMid n = coordMid n := by
  ext t
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact coordReflect_mem_coordMid_of_mem n hs
  · intro ht
    refine ⟨coordReflect n t, coordReflect_mem_coordMid_of_mem n ht, coordReflect_involutive n t⟩

lemma mem_reflectSimplex_iff (n : ℕ) {t : CFun n} :
    t ∈ coordReflect n '' coordSimplex n ↔
      (∀ i : Fin n, t i ∈ Set.Icc (0 : ℝ) 1) ∧ (n : ℝ) - 1 ≤ ∑ i : Fin n, t i := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    constructor
    · exact coordReflect_mem_coordBox_of_mem_coordSimplex n hs
    · rw [sumCoordReflect]
      linarith [hs.2]
  · intro ht
    refine ⟨coordReflect n t, ?_, coordReflect_involutive n t⟩
    constructor
    · intro i
      dsimp [coordReflect]
      linarith [(ht.1 i).2]
    · rw [sumCoordReflect]
      linarith [ht.2]

/-- `coordSimplex ∩ coordMid` lies in the hyperplane `{Σt = 1}`. -/
lemma coordSimplex_inter_coordMid_subset_sum_one (n : ℕ) :
    coordSimplex n ∩ coordMid n ⊆ {t : CFun n | (∑ i : Fin n, t i) = 1} := by
  rintro t ht
  have hle : (∑ i : Fin n, t i) ≤ 1 := ht.1.2
  have hge : (1 : ℝ) ≤ ∑ i : Fin n, t i := ht.2.2.1
  exact le_antisymm hle hge

/-- `coordMid ∩ (reflection of coordSimplex)` lies in the hyperplane `{Σt = n - 1}`. -/
lemma coordMid_inter_reflectSimplex_subset_sum (n : ℕ) :
    coordMid n ∩ (coordReflect n '' coordSimplex n) ⊆
      {t : CFun n | (∑ i : Fin n, t i) = (n : ℝ) - 1} := by
  rintro t ht
  have hle : (∑ i : Fin n, t i) ≤ (n : ℝ) - 1 := ht.1.2.2
  have hge : (n : ℝ) - 1 ≤ ∑ i : Fin n, t i := (mem_reflectSimplex_iff n).1 ht.2 |>.2
  exact le_antisymm hle hge

/-- `coordSimplex ∩ (reflection of coordSimplex)` lies in the hyperplane `{Σt = 1}`. -/
lemma coordSimplex_inter_reflectSimplex_subset_sum_one (n : ℕ) (hn : 2 ≤ n) :
    coordSimplex n ∩ (coordReflect n '' coordSimplex n) ⊆
      {t : CFun n | (∑ i : Fin n, t i) = 1} := by
  rintro t ht
  have hle : (∑ i : Fin n, t i) ≤ 1 := ht.1.2
  have hge' : (n : ℝ) - 1 ≤ ∑ i : Fin n, t i := (mem_reflectSimplex_iff n).1 ht.2 |>.2
  have hge : (1 : ℝ) ≤ ∑ i : Fin n, t i := by
    have hnreal : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn' : (1 : ℝ) ≤ (n : ℝ) - 1 := by linarith
    linarith
  exact le_antisymm hle hge

end

/-- `coordBox` as a product of intervals. -/
lemma coordBox_eq_pi (n : ℕ) : coordBox n = Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
  ext t
  constructor
  · intro ht i hi
    exact ht i
  · intro ht i
    exact ht i (by simp)

lemma convex_coordBox (n : ℕ) : Convex ℝ (coordBox n) := by
  rw [coordBox_eq_pi]
  exact convex_pi (fun i hi => convex_Icc (0 : ℝ) 1)

lemma isCompact_coordBox (n : ℕ) : IsCompact (coordBox n) := by
  rw [coordBox_eq_pi]
  exact isCompact_univ_pi (fun i => isCompact_Icc)

lemma isClosed_coordBox (n : ℕ) : IsClosed (coordBox n) :=
  (isCompact_coordBox n).isClosed

lemma coordBox_nonempty (n : ℕ) : (coordBox n).Nonempty := by
  refine ⟨0, ?_⟩
  intro i
  constructor <;> norm_num

lemma continuous_coordSum (n : ℕ) : Continuous (fun t : CFun n => ∑ i : Fin n, t i) := by
  fun_prop

lemma isClosed_sum_le (n : ℕ) : IsClosed {t : CFun n | (∑ i : Fin n, t i) ≤ 1} := by
  exact isClosed_le (continuous_coordSum n) continuous_const

lemma isClosed_coordNonneg (n : ℕ) : IsClosed {t : CFun n | ∀ i : Fin n, 0 ≤ t i} := by
  rw [show {t : CFun n | ∀ i : Fin n, 0 ≤ t i} = ⋂ i : Fin n, {t : CFun n | 0 ≤ t i} by
    ext t
    simp]
  exact isClosed_iInter (fun i => isClosed_le continuous_const (continuous_apply i))

lemma coordSimplex_eq_inter (n : ℕ) :
    coordSimplex n = {t : CFun n | ∀ i : Fin n, 0 ≤ t i} ∩
      {t : CFun n | (∑ i : Fin n, t i) ≤ 1} := by
  ext t
  constructor
  · intro ht
    exact ⟨ht.1, ht.2⟩
  · intro ht
    exact ht

lemma isClosed_coordSimplex (n : ℕ) : IsClosed (coordSimplex n) := by
  rw [coordSimplex_eq_inter]
  exact (isClosed_coordNonneg n).inter (isClosed_sum_le n)

lemma isCompact_coordSimplex (n : ℕ) : IsCompact (coordSimplex n) := by
  refine IsCompact.of_isClosed_subset (isCompact_coordBox n) (isClosed_coordSimplex n) ?_
  exact coordSimplex_subset_coordBox n

lemma coordSimplex_nonempty (n : ℕ) : (coordSimplex n).Nonempty := by
  refine ⟨0, ?_⟩
  constructor
  · intro i
    norm_num
  · simp

lemma convex_coordSimplex (n : ℕ) : Convex ℝ (coordSimplex n) := by
  intro a ha b hb u v hu hv huv
  constructor
  · intro i
    have h1 := ha.1 i
    have h2 := hb.1 i
    have : 0 ≤ (u • a + v • b) i := by
      simp [Pi.add_apply, Pi.smul_apply]
      nlinarith [mul_nonneg hu h1, mul_nonneg hv h2]
    simpa using this
  · have hsum : (∑ i : Fin n, (u • a + v • b) i) =
        u * (∑ i : Fin n, a i) + v * (∑ i : Fin n, b i) := by
      simp [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib]
      rw [Finset.mul_sum]
      rw [Finset.mul_sum]
    rw [hsum]
    nlinarith [hu, hv, huv, ha.2, hb.2]

lemma coordMid_eq_inter (n : ℕ) :
    coordMid n = coordBox n ∩ {t : CFun n | (1 : ℝ) ≤ ∑ i : Fin n, t i} ∩
      {t : CFun n | (∑ i : Fin n, t i) ≤ (n : ℝ) - 1} := by
  ext t
  constructor
  · intro ht
    exact ⟨⟨ht.1, ht.2.1⟩, ht.2.2⟩
  · intro ht
    exact ⟨ht.1.1, ht.1.2, ht.2⟩

lemma isClosed_coordMid (n : ℕ) : IsClosed (coordMid n) := by
  rw [coordMid_eq_inter]
  refine ((isClosed_coordBox n).inter ?_).inter ?_
  · exact isClosed_le continuous_const (continuous_coordSum n)
  · exact isClosed_le (continuous_coordSum n) continuous_const

lemma isCompact_coordMid (n : ℕ) : IsCompact (coordMid n) := by
  refine IsCompact.of_isClosed_subset (isCompact_coordBox n) (isClosed_coordMid n) ?_
  intro t ht
  rw [coordMid_eq_inter] at ht
  exact ht.1.1

lemma coordMid_subset_coordBox (n : ℕ) : coordMid n ⊆ coordBox n := by
  intro t ht
  rw [coordMid_eq_inter] at ht
  exact ht.1.1

lemma coordMid_nonempty (n : ℕ) (hn : 2 ≤ n) : (coordMid n).Nonempty := by
  refine ⟨fun _ => (1 : ℝ) / 2, ?_⟩
  constructor
  · intro i
    constructor <;> norm_num
  · constructor
    · have hsum : (∑ i : Fin n, (1 : ℝ) / 2) = (n : ℝ) / 2 := by
        simp
        ring
      rw [hsum]
      have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    · have hsum : (∑ i : Fin n, (1 : ℝ) / 2) = (n : ℝ) / 2 := by
        simp
        ring
      rw [hsum]
      have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith

lemma convex_coordMid (n : ℕ) : Convex ℝ (coordMid n) := by
  intro a ha b hb u v hu hv huv
  constructor
  · intro i
    have h1 := ha.1 i
    have h2 := hb.1 i
    have hle1 : u * a i ≤ u * 1 := mul_le_mul_of_nonneg_left h1.2 hu
    have hle2 : v * b i ≤ v * 1 := mul_le_mul_of_nonneg_left h2.2 hv
    have hval : (u • a + v • b) i = u * a i + v * b i := by
      simp [Pi.add_apply, Pi.smul_apply]
    rw [hval]
    constructor
    · nlinarith [mul_nonneg hu h1.1, mul_nonneg hv h2.1]
    · nlinarith [hle1, hle2, huv]
  · constructor
    · have hsum : (∑ i : Fin n, (u • a + v • b) i) =
          u * (∑ i : Fin n, a i) + v * (∑ i : Fin n, b i) := by
        simp [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib]
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
      rw [hsum]
      nlinarith [hu, hv, ha.2.1, hb.2.1]
    · have hsum : (∑ i : Fin n, (u • a + v • b) i) =
          u * (∑ i : Fin n, a i) + v * (∑ i : Fin n, b i) := by
        simp [Pi.add_apply, Pi.smul_apply, Finset.sum_add_distrib]
        rw [Finset.mul_sum]
        rw [Finset.mul_sum]
      rw [hsum]
      nlinarith [hu, hv, ha.2.2, hb.2.2]

/-- The hyperplane `{Σt = c}` in `CFun n` has empty interior (as soon as `n ≥ 1`). -/
lemma interior_sum_eq_empty (n : ℕ) (hn : 0 < n) (c : ℝ) :
    interior {t : CFun n | (∑ i : Fin n, t i) = c} = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨x, hx⟩
  let H : Set (CFun n) := {t | (∑ i : Fin n, t i) = c}
  let a : Fin n := ⟨0, hn⟩
  let e : CFun n := Pi.single a (1 : ℝ)
  let γ : ℝ → CFun n := fun u => x + u • e
  have hsum_e : (∑ i : Fin n, e i) = 1 := by
    dsimp [e]
    simp
  have hγ_cont : Continuous γ := by
    dsimp [γ]
    fun_prop
  have hUopen : IsOpen (interior H) := isOpen_interior
  have hpre : IsOpen (γ ⁻¹' (interior H)) := hUopen.preimage hγ_cont
  have h0mem : (0 : ℝ) ∈ γ ⁻¹' (interior H) := by
    dsimp [γ]
    simpa using hx
  rcases (Metric.isOpen_iff.mp hpre (0 : ℝ) h0mem) with ⟨ε, hε, hball⟩
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  have hε2ball : ε / 2 ∈ Metric.ball (0 : ℝ) ε := by
    rw [Metric.mem_ball, Real.dist_0_eq_abs]
    rw [abs_of_nonneg (by linarith : 0 ≤ ε / 2)]
    linarith
  have hγmem : γ (ε / 2) ∈ interior H := hball hε2ball
  have hγH : γ (ε / 2) ∈ H := interior_subset hγmem
  have hxH : x ∈ H := interior_subset hx
  have hsum_γ : (∑ i : Fin n, (γ (ε / 2)) i) = (∑ i : Fin n, x i) + (ε / 2) * (∑ i : Fin n, e i) := by
    dsimp [γ]
    rw [Finset.sum_add_distrib]
    rw [Finset.mul_sum]
  have hcontr1 : (∑ i : Fin n, (γ (ε / 2)) i) = c := hγH
  have hcontr2 : (∑ i : Fin n, (γ (ε / 2)) i) = c + ε / 2 := by
    rw [hsum_γ]
    rw [hsum_e]
    rw [hxH]
    ring
  linarith

/-- Any set contained in the hyperplane `{Σt = c}` has empty interior. -/
lemma interior_eq_empty_of_subset_sum_eq (n : ℕ) (hn : 0 < n) (c : ℝ)
    {X : Set (CFun n)} (hX : X ⊆ {t : CFun n | (∑ i : Fin n, t i) = c}) : interior X = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty]
  rintro ⟨x, hx⟩
  have hx' : x ∈ interior {t : CFun n | (∑ i : Fin n, t i) = c} := interior_mono hX hx
  have hempty : interior {t : CFun n | (∑ i : Fin n, t i) = c} = ∅ := interior_sum_eq_empty n hn c
  rw [hempty] at hx'
  simpa using hx'

lemma interior_coordSimplex_inter_coordMid_eq_empty (n : ℕ) (hn : 2 ≤ n) :
    interior (coordSimplex n ∩ coordMid n) = ∅ := by
  exact interior_eq_empty_of_subset_sum_eq n (by omega) 1 (coordSimplex_inter_coordMid_subset_sum_one n)

lemma interior_coordMid_inter_reflectSimplex_eq_empty (n : ℕ) (hn : 2 ≤ n) :
    interior (coordMid n ∩ (coordReflect n '' coordSimplex n)) = ∅ := by
  exact interior_eq_empty_of_subset_sum_eq n (by omega) ((n : ℝ) - 1)
    (coordMid_inter_reflectSimplex_subset_sum n)

lemma interior_coordSimplex_inter_reflectSimplex_eq_empty (n : ℕ) (hn : 2 ≤ n) :
    interior (coordSimplex n ∩ (coordReflect n '' coordSimplex n)) = ∅ := by
  exact interior_eq_empty_of_subset_sum_eq n (by omega) 1
    (coordSimplex_inter_reflectSimplex_subset_sum_one n hn)


abbrev EAmb (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The coordinate box as a convex body. -/
def coordBodyBox (n : ℕ) : ConvexBody (CFun n) :=
  ⟨coordBox n, convex_coordBox n, isCompact_coordBox n, coordBox_nonempty n⟩

/-- The coordinate simplex as a convex body. -/
def coordBodySimplex (n : ℕ) : ConvexBody (CFun n) :=
  ⟨coordSimplex n, convex_coordSimplex n, isCompact_coordSimplex n, coordSimplex_nonempty n⟩

/-- The middle coordinate body as a convex body (`2 ≤ n`). -/
def coordBodyMid (n : ℕ) (hn : 2 ≤ n) : ConvexBody (CFun n) :=
  ⟨coordMid n, convex_coordMid n, isCompact_coordMid n, coordMid_nonempty n hn⟩

/-- The convex hull of `{0} ∪ range u` as a convex body. -/
def hullBody (n : ℕ) (u : Fin n → EAmb n) : ConvexBody (EAmb n) :=
  ⟨convexHull ℝ (({0} ∪ Set.range u) : Set (EAmb n)),
   convex_convexHull ℝ (({0} ∪ Set.range u) : Set (EAmb n)),
   Set.Finite.isCompact_convexHull ℝ
     ((Set.finite_singleton (0 : EAmb n)).union (Set.finite_range u)),
   convexHull_nonempty_iff.mpr ⟨0, by simp⟩⟩

/-- The image of a convex body under a linear equivalence between finite-dimensional spaces. -/
def imageConvexBody {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V ≃ₗ[ℝ] W) (K : ConvexBody V) : ConvexBody W :=
  ⟨L '' (K : Set V), K.convex.linear_image (L : V →ₗ[ℝ] W),
   K.isCompact.image (LinearMap.continuous_of_finiteDimensional (L : V →ₗ[ℝ] W)),
   Set.image_nonempty.mpr K.nonempty⟩

@[simp]
lemma imageConvexBody_coe {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V ≃ₗ[ℝ] W) (K : ConvexBody V) :
    (imageConvexBody L K : Set W) = L '' (K : Set V) := rfl

/-- The translate of a convex body by `t`. -/
def translateConvexBody {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ConvexBody V) (t : V) : ConvexBody V :=
  ⟨(fun x : V => t + x) '' (K : Set V), K.convex.translate t,
   K.isCompact.image (continuous_const.add continuous_id),
   Set.image_nonempty.mpr K.nonempty⟩

@[simp]
lemma translateConvexBody_coe {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ConvexBody V) (t : V) :
    (translateConvexBody K t : Set V) = (fun x : V => t + x) '' (K : Set V) := rfl

/-- The negation of a convex body. -/
def negConvexBody {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ConvexBody V) : ConvexBody V :=
  ⟨-(K : Set V), K.convex.neg, K.isCompact.neg, by
     rcases K.nonempty with ⟨x, hx⟩
     refine ⟨-x, ?_⟩
     rw [Set.mem_neg]
     simpa using hx⟩

@[simp]
lemma negConvexBody_coe {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (K : ConvexBody V) : (negConvexBody K : Set V) = -(K : Set V) := rfl

/-- Interior commutes with images under linear equivalences (finite-dimensional). -/
lemma interior_image_linearEquiv {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    (L : V ≃ₗ[ℝ] W) (s : Set V) : interior (L '' s) = L '' interior s := by
  let H : V ≃ₜ W := L.toAffineEquiv.toHomeomorphOfFiniteDimensional
  have hHfun : (H : V → W) = L := by simp [H]
  have h := Homeomorph.image_interior H s
  rw [hHfun] at h
  exact h.symm

/-- `{v + z | z ∈ -K} = {-y + v | y ∈ K}`: translation-after-negation is reflection. -/
lemma translate_neg_eq_reflect {V : Type*} [NormedAddCommGroup V] (K : Set V) (v : V) :
    (fun x : V => v + x) '' (-K) = (fun y : V => -y + v) '' K := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : -z ∈ K := by simpa [Set.mem_neg] using hz
    refine ⟨-z, hz', ?_⟩
    abel
  · rintro ⟨y, hy, rfl⟩
    refine ⟨-y, ?_, ?_⟩
    · simpa [Set.mem_neg] using hy
    · abel



/-- A linear equivalence maps the reflection of a coordinate set correctly:
`v - Φ s = Φ (1 - s)` pointwise, so reflecting the image equals the image of
the reflected coordinates. -/
lemma reflect_image_eq_image_coordReflect (n : ℕ) (Φ : CFun n ≃ₗ[ℝ] EAmb n)
    (v : EAmb n) (hone : Φ (coordOne n) = v) (S : Set (CFun n)) :
    (fun y : EAmb n => -y + v) '' (Φ '' S) = Φ '' (coordReflect n '' S) := by
  have hcore : ∀ s : CFun n, Φ (coordReflect n s) = -(Φ s) + v := by
    intro s
    have hsplit : coordReflect n s = -s + coordOne n := by
      funext i
      dsimp [coordReflect, coordOne]
      ring
    calc
      Φ (coordReflect n s) = Φ (-s + coordOne n) := by rw [hsplit]
      _ = Φ (-s) + Φ (coordOne n) := by
        exact ((Φ : CFun n →ₗ[ℝ] EAmb n).map_add (-s) (coordOne n))
      _ = -(Φ s) + Φ (coordOne n) := by
        congr 1
        exact ((Φ : CFun n →ₗ[ℝ] EAmb n).map_neg s)
      _ = -(Φ s) + v := by rw [hone]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨s, hs, rfl⟩
    refine ⟨coordReflect n s, ⟨s, hs, rfl⟩, ?_⟩
    exact hcore s
  · rintro ⟨t, ht, rfl⟩
    rcases ht with ⟨s, hs, rfl⟩
    refine ⟨Φ s, ⟨s, hs, rfl⟩, ?_⟩
    exact (hcore s).symm

theorem simplex_parallelotope_dissection (n : ℕ) (hn : 2 ≤ n)
    (u : Fin n → EuclideanSpace ℝ (Fin n)) (hu : LinearIndependent ℝ u) :
    ∃ P Δ Q R : ConvexBody (EuclideanSpace ℝ (Fin n)),
      ∃ v : EuclideanSpace ℝ (Fin n),
        (v = ∑ i : Fin n, u i) ∧
        (P : Set (EuclideanSpace ℝ (Fin n))) =
          {x | ∃ t : Fin n → ℝ, (∀ i : Fin n, t i ∈ Set.Icc (0 : ℝ) 1) ∧
            x = ∑ i : Fin n, t i • u i} ∧
        (Δ : Set (EuclideanSpace ℝ (Fin n))) =
          convexHull ℝ (({0} ∪ Set.range u) : Set (EuclideanSpace ℝ (Fin n))) ∧
        (Q : Set (EuclideanSpace ℝ (Fin n))) =
          {x | ∃ t : Fin n → ℝ, (∀ i : Fin n, t i ∈ Set.Icc (0 : ℝ) 1) ∧
            (1 : ℝ) ≤ ∑ i : Fin n, t i ∧ ∑ i : Fin n, t i ≤ (n : ℝ) - 1 ∧
            x = ∑ i : Fin n, t i • u i} ∧
        (R : Set (EuclideanSpace ℝ (Fin n))) =
          (fun y : EuclideanSpace ℝ (Fin n) => -y + v) '' (Δ : Set (EuclideanSpace ℝ (Fin n))) ∧
        (Q : Set (EuclideanSpace ℝ (Fin n))) =
          (fun y : EuclideanSpace ℝ (Fin n) => -y + v) '' (Q : Set (EuclideanSpace ℝ (Fin n))) ∧
        (P : Set (EuclideanSpace ℝ (Fin n))) =
          (Δ : Set (EuclideanSpace ℝ (Fin n))) ∪ (Q : Set (EuclideanSpace ℝ (Fin n))) ∪
            (R : Set (EuclideanSpace ℝ (Fin n))) ∧
        interior ((Δ : Set (EuclideanSpace ℝ (Fin n))) ∩ (Q : Set (EuclideanSpace ℝ (Fin n)))) = ∅ ∧
        interior ((Q : Set (EuclideanSpace ℝ (Fin n))) ∩ (R : Set (EuclideanSpace ℝ (Fin n)))) = ∅ ∧
        interior ((Δ : Set (EuclideanSpace ℝ (Fin n))) ∩ (R : Set (EuclideanSpace ℝ (Fin n)))) = ∅ := by
  classical
  haveI : Nonempty (Fin n) := ⟨0, by omega⟩
  let bU : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
    basisOfLinearIndependentOfCardEqFinrank hu (by simp)
  let Φ : CFun n ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := bU.equivFun.symm
  have hbU : (bU : Fin n → EuclideanSpace ℝ (Fin n)) = u := by
    simp [bU]
  have hΦfun_pt : ∀ t : CFun n, Φ t = ∑ i : Fin n, t i • u i := by
    intro t
    calc
      Φ t = bU.equivFun.symm t := rfl
      _ = ∑ i : Fin n, t i • bU i := by simp
      _ = ∑ i : Fin n, t i • u i := by rw [hbU]
  let v : EuclideanSpace ℝ (Fin n) := ∑ i : Fin n, u i
  have hΦone : Φ (coordOne n) = v := by
    rw [hΦfun_pt]
    simp [coordOne, v]
  let P : ConvexBody (EuclideanSpace ℝ (Fin n)) := imageConvexBody Φ (coordBodyBox n)
  let Q : ConvexBody (EuclideanSpace ℝ (Fin n)) := imageConvexBody Φ (coordBodyMid n hn)
  let Δ : ConvexBody (EuclideanSpace ℝ (Fin n)) := hullBody n u
  let R : ConvexBody (EuclideanSpace ℝ (Fin n)) := translateConvexBody (negConvexBody Δ) v
  have hPset : (P : Set (EuclideanSpace ℝ (Fin n))) = Φ '' (coordBox n) := by
    simp [P, imageConvexBody, coordBodyBox]
  have hQset : (Q : Set (EuclideanSpace ℝ (Fin n))) = Φ '' (coordMid n) := by
    simp [Q, imageConvexBody, coordBodyMid]
  have hΔdef : (Δ : Set (EuclideanSpace ℝ (Fin n))) =
      convexHull ℝ (({0} ∪ Set.range u) : Set (EuclideanSpace ℝ (Fin n))) := by
    simp [Δ, hullBody]
  have hΔset : (Δ : Set (EuclideanSpace ℝ (Fin n))) = Φ '' (coordSimplex n) := by
    calc
      (Δ : Set (EuclideanSpace ℝ (Fin n)))
          = convexHull ℝ (({0} ∪ Set.range u) : Set (EuclideanSpace ℝ (Fin n))) := hΔdef
      _ = {x : EuclideanSpace ℝ (Fin n) | ∃ t : Fin n → ℝ,
            (∀ i : Fin n, 0 ≤ t i) ∧ (∑ i : Fin n, t i) ≤ 1 ∧
            x = ∑ i : Fin n, t i • u i} :=
            Commons.Analysis.Convex.convHull_zero_range u
      _ = Φ '' (coordSimplex n) := by
        ext x
        constructor
        · rintro ⟨t, ht0, hts, hx⟩
          refine ⟨t, ⟨ht0, hts⟩, ?_⟩
          rw [hx]
          exact hΦfun_pt t
        · rintro ⟨t, ht, hx⟩
          refine ⟨t, ht.1, ht.2, ?_⟩
          rw [← hx]
          exact hΦfun_pt t
  have hRset : (R : Set (EuclideanSpace ℝ (Fin n))) =
      (fun y : EuclideanSpace ℝ (Fin n) => -y + v) '' (Δ : Set (EuclideanSpace ℝ (Fin n))) := by
    change ((translateConvexBody (negConvexBody Δ) v) : Set (EuclideanSpace ℝ (Fin n))) =
      (fun y : EuclideanSpace ℝ (Fin n) => -y + v) '' (Δ : Set (EuclideanSpace ℝ (Fin n)))
    rw [translateConvexBody_coe, negConvexBody_coe]
    exact translate_neg_eq_reflect (Δ : Set (EuclideanSpace ℝ (Fin n))) v
  have hRset2 : (R : Set (EuclideanSpace ℝ (Fin n))) =
      Φ '' (coordReflect n '' coordSimplex n) := by
    calc
      (R : Set (EuclideanSpace ℝ (Fin n))) =
          (fun y : EuclideanSpace ℝ (Fin n) => -y + v) '' (Δ : Set (EuclideanSpace ℝ (Fin n))) := hRset
      _ = (fun y : EuclideanSpace ℝ (Fin n) => -y + v) '' (Φ '' (coordSimplex n)) := by
        rw [hΔset]
      _ = Φ '' (coordReflect n '' coordSimplex n) :=
        reflect_image_eq_image_coordReflect n Φ v hΦone (coordSimplex n)
  have hPformula : (P : Set (EuclideanSpace ℝ (Fin n))) =
      {x | ∃ t : Fin n → ℝ, (∀ i : Fin n, t i ∈ Set.Icc (0 : ℝ) 1) ∧
        x = ∑ i : Fin n, t i • u i} := by
    rw [hPset]
    ext x
    constructor
    · rintro ⟨t, ht, hx⟩
      refine ⟨t, ht, ?_⟩
      rw [← hx]
      exact hΦfun_pt t
    · rintro ⟨t, ht, hx⟩
      refine ⟨t, ht, ?_⟩
      rw [hx]
      exact hΦfun_pt t
  have hQformula : (Q : Set (EuclideanSpace ℝ (Fin n))) =
      {x | ∃ t : Fin n → ℝ, (∀ i : Fin n, t i ∈ Set.Icc (0 : ℝ) 1) ∧
        (1 : ℝ) ≤ ∑ i : Fin n, t i ∧ ∑ i : Fin n, t i ≤ (n : ℝ) - 1 ∧
        x = ∑ i : Fin n, t i • u i} := by
    rw [hQset]
    ext x
    constructor
    · rintro ⟨t, ht, hx⟩
      refine ⟨t, ht.1, ht.2.1, ht.2.2, ?_⟩
      rw [← hx]
      exact hΦfun_pt t
    · rintro ⟨t, htb, hle, hge, hx⟩
      refine ⟨t, ⟨htb, hle, hge⟩, ?_⟩
      rw [hx]
      exact hΦfun_pt t
  have hQrefl : (Q : Set (EuclideanSpace ℝ (Fin n))) =
      (fun y : EuclideanSpace ℝ (Fin n) => -y + v) '' (Q : Set (EuclideanSpace ℝ (Fin n))) := by
    calc
      (Q : Set (EuclideanSpace ℝ (Fin n))) = Φ '' (coordMid n) := hQset
      _ = (fun y : EuclideanSpace ℝ (Fin n) => -y + v) '' (Φ '' (coordMid n)) := by
        rw [reflect_image_eq_image_coordReflect n Φ v hΦone (coordMid n)]
        rw [coordMid_eq_reflect n]
  have hPunion : (P : Set (EuclideanSpace ℝ (Fin n))) =
      ((Δ : Set (EuclideanSpace ℝ (Fin n))) ∪ (Q : Set (EuclideanSpace ℝ (Fin n)))) ∪
        (R : Set (EuclideanSpace ℝ (Fin n))) := by
    calc
      (P : Set (EuclideanSpace ℝ (Fin n))) = Φ '' (coordBox n) := hPset
      _ = Φ '' (((coordSimplex n) ∪ coordMid n) ∪ (coordReflect n '' coordSimplex n)) := by
        rw [coordBox_eq_union n]
      _ = ((Φ '' (coordSimplex n)) ∪ (Φ '' (coordMid n))) ∪
          (Φ '' (coordReflect n '' coordSimplex n)) := by
        rw [Set.image_union]
        rw [Set.image_union]
      _ = ((Δ : Set (EuclideanSpace ℝ (Fin n))) ∪ (Q : Set (EuclideanSpace ℝ (Fin n)))) ∪
          (R : Set (EuclideanSpace ℝ (Fin n))) := by
        rw [hΔset]
        rw [hQset]
        rw [hRset2]
  have hintΔQ : interior ((Δ : Set (EuclideanSpace ℝ (Fin n))) ∩
      (Q : Set (EuclideanSpace ℝ (Fin n)))) = ∅ := by
    calc
      interior ((Δ : Set (EuclideanSpace ℝ (Fin n))) ∩ (Q : Set (EuclideanSpace ℝ (Fin n))))
          = interior ((Φ '' (coordSimplex n)) ∩ (Φ '' (coordMid n))) := by
            rw [hΔset, hQset]
      _ = interior (Φ '' ((coordSimplex n) ∩ (coordMid n))) := by
            rw [Set.image_inter Φ.injective]
      _ = Φ '' interior ((coordSimplex n) ∩ (coordMid n)) :=
            interior_image_linearEquiv Φ ((coordSimplex n) ∩ (coordMid n))
      _ = Φ '' (∅ : Set (CFun n)) := by
            rw [interior_coordSimplex_inter_coordMid_eq_empty n hn]
      _ = ∅ := by simp
  have hintQR : interior ((Q : Set (EuclideanSpace ℝ (Fin n))) ∩
      (R : Set (EuclideanSpace ℝ (Fin n)))) = ∅ := by
    calc
      interior ((Q : Set (EuclideanSpace ℝ (Fin n))) ∩ (R : Set (EuclideanSpace ℝ (Fin n))))
          = interior ((Φ '' (coordMid n)) ∩ (Φ '' (coordReflect n '' coordSimplex n))) := by
            rw [hQset, hRset2]
      _ = interior (Φ '' ((coordMid n) ∩ (coordReflect n '' coordSimplex n))) := by
            rw [Set.image_inter Φ.injective]
      _ = Φ '' interior ((coordMid n) ∩ (coordReflect n '' coordSimplex n)) :=
            interior_image_linearEquiv Φ ((coordMid n) ∩ (coordReflect n '' coordSimplex n))
      _ = Φ '' (∅ : Set (CFun n)) := by
            rw [interior_coordMid_inter_reflectSimplex_eq_empty n hn]
      _ = ∅ := by simp
  have hintΔR : interior ((Δ : Set (EuclideanSpace ℝ (Fin n))) ∩
      (R : Set (EuclideanSpace ℝ (Fin n)))) = ∅ := by
    calc
      interior ((Δ : Set (EuclideanSpace ℝ (Fin n))) ∩ (R : Set (EuclideanSpace ℝ (Fin n))))
          = interior ((Φ '' (coordSimplex n)) ∩ (Φ '' (coordReflect n '' coordSimplex n))) := by
            rw [hΔset, hRset2]
      _ = interior (Φ '' ((coordSimplex n) ∩ (coordReflect n '' coordSimplex n))) := by
            rw [Set.image_inter Φ.injective]
      _ = Φ '' interior ((coordSimplex n) ∩ (coordReflect n '' coordSimplex n)) :=
            interior_image_linearEquiv Φ ((coordSimplex n) ∩ (coordReflect n '' coordSimplex n))
      _ = Φ '' (∅ : Set (CFun n)) := by
            rw [interior_coordSimplex_inter_reflectSimplex_eq_empty n hn]
      _ = ∅ := by simp
  refine ⟨P, Δ, Q, R, v, rfl, hPformula, hΔdef, hQformula, hRset, hQrefl, hPunion,
    hintΔQ, hintQR, hintΔR⟩

end Commons.Geometry.Convex.Hadwiger