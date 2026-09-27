import Mathlib
import Submission.Work.EKLRelCross.LeafCtor
import Submission.Work.EKLRelCross.LeafMeasDefs
import Submission.Work.EKLRelCross.leafwise_base_fields_free
import Submission.Work.EKLC7.LeafwiseGeom
import Submission.Work.EKLComp.LeafAux
import Submission.Work.EKLRelCross.condExpKernel_atom_ratio
import Submission.Work.EKLRelCross.measurableSet_orbImg
import Submission.Work.EKLRelCross.pushOrbit_smul_map

/-!
# `Work.EKLRelCross.leafwise_equivariant_field_free`

The `equivariant` field (EKL (3), Pisa 6.3(iii)) for the family `nuFull` constructed in
`LeafCtor.lean`: for a.e. `x` and every `u ∈ U` with `u • x` still in the good set, the leafwise
measure at `u • x` is the right `u`-translate of the leafwise measure at `x`, up to a non-zero
finite constant.

The proof follows Pisa's proof of 6.3(iii).  If `x` and `u • x` lie in the same atom of the
plaque algebra of level `k` (which happens for all large `k`), the conditional measures at the
two points *coincide*, so pushing them to `U` gives measures that differ by the push-forward
along the right translation `g ↦ g * u`; the residual constant comes from the two different
normalisations (`Box1 U` at `x` versus `Box1 U · u` at `u • x`).  The independence of the
resulting constant of the chosen level is the proportionality of conditional measures of two
plaque algebras (Pisa 5.17 + 6.17, the hypothesis `ProporPiece`), and the positivity of the
normalisations is Pisa 6.20 (`PosPiece`).
-/

open MeasureTheory
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-! ## 1.  The annuli `piece U k` -/

private theorem Ucl_mono {U : Subgroup SL3} {r r' : ℝ} (h : r ≤ r') : Ucl U r ⊆ Ucl U r' :=
  fun g hg => ⟨hg.1, fun i j => le_trans (hg.2 i j) h⟩

theorem piece_subset_Ucl (U : Subgroup SL3) (k : ℕ) : piece U k ⊆ Ucl U ((k : ℝ) + 1) := by
  cases k with
  | zero =>
    intro g hg
    have h01 : (((0 : ℕ) : ℝ) + 1) = (1 : ℝ) := by norm_num
    rw [h01]
    exact hg
  | succ j =>
    intro g hg
    have hg' : g ∈ Ucl U ((j : ℝ) + 2) \ Ucl U ((j : ℝ) + 1) := by
      simpa only [piece] using hg
    have hcast : (((j + 1 : ℕ) : ℝ) + 1) = (j : ℝ) + 2 := by push_cast; ring
    rw [hcast]
    exact hg'.1

theorem Ucl_subset_V {U : Subgroup SL3} {r r' : ℝ} (h : r < r') : Ucl U r ⊆ V r' :=
  fun _ hg _ _ => lt_of_le_of_lt (hg.2 _ _) h

theorem piece_subset_V (U : Subgroup SL3) (k : ℕ) : piece U k ⊆ V ((k : ℝ) + 2) :=
  fun _ hg => Ucl_subset_V (by linarith) (piece_subset_Ucl U k hg)

private theorem Box1_subset_V (U : Subgroup SL3) : Box1 U ⊆ V 2 := by
  intro g hg
  rw [Box1_eq_Ucl] at hg
  exact Ucl_subset_V (by norm_num) hg

theorem V_half_inter_subset_Box1 (U : Subgroup SL3) : V (1 / 2) ∩ (U : Set SL3) ⊆ Box1 U := by
  intro g hg
  rw [Box1_eq_Ucl]
  exact ⟨hg.2, fun i j => le_of_lt (lt_trans (hg.1 i j) (by norm_num))⟩

theorem piece_disjoint {U : Subgroup SL3} {i j : ℕ} (hij : i < j) :
    Disjoint (piece U i) (piece U j) := by
  rw [Set.disjoint_left]
  intro g hgi hgj
  have h1 : g ∈ Ucl U ((i : ℝ) + 1) := piece_subset_Ucl U i hgi
  have h2 : g ∈ Ucl U (j : ℝ) :=
    Ucl_mono (by exact_mod_cast (Nat.succ_le_of_lt hij)) h1
  have h3 : g ∈ (Ucl U (j : ℝ))ᶜ :=
    piece_subset_compl_Ucl (U := U) (k := j) (by omega) hgj
  exact h3 h2

theorem iUnion_piece (U : Subgroup SL3) : (⋃ k : ℕ, piece U k) = (U : Set SL3) := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun k => piece_subset_U U k) ?_
  have hmono : ∀ n : ℕ, Ucl U ((n : ℝ) + 1) ⊆ (⋃ k : ℕ, piece U k) := by
    intro n
    induction n with
    | zero =>
      intro y hy
      exact Set.mem_iUnion.mpr ⟨0, by simpa [piece] using hy⟩
    | succ m ih =>
      intro y hy
      rw [show (((Nat.succ m : ℕ) : ℝ) + 1) = (m : ℝ) + 2 from by push_cast; ring] at hy
      by_cases h : y ∈ Ucl U ((m : ℝ) + 1)
      · exact ih h
      · refine Set.mem_iUnion.mpr ⟨m + 1, ?_⟩
        show y ∈ Ucl U ((m : ℝ) + 2) \ Ucl U ((m : ℝ) + 1)
        exact ⟨hy, h⟩
  intro g hg
  set R : ℝ := (Finset.univ : Finset (Fin 3 × Fin 3)).sup' Finset.univ_nonempty
    (fun p => |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) with hR
  have hbound : ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ R := by
    intro i j
    rw [hR]
    exact Finset.le_sup' (f := fun p : Fin 3 × Fin 3 =>
      |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) (Finset.mem_univ (i, j))
  refine hmono (Nat.ceil R) ⟨hg, fun i j => ?_⟩
  have h2 : R ≤ ((Nat.ceil R : ℕ) : ℝ) := Nat.le_ceil R
  have h3 : ((Nat.ceil R : ℕ) : ℝ) ≤ ((Nat.ceil R : ℕ) : ℝ) + 1 := by linarith
  exact le_trans (hbound i j) (le_trans h2 h3)

/-- The image of two disjoint sets under the orbit map at a point with free `U`-orbit is
disjoint. -/
theorem orbImg_disjoint {U : Subgroup SL3} {x : X3}
    (hinj : Function.Injective (fun u : U => (u : SL3) • x)) {B₁ B₂ : Set SL3}
    (h : Disjoint B₁ B₂) : Disjoint (orbImg U x B₁) (orbImg U x B₂) := by
  rw [Set.disjoint_left]
  rintro y ⟨b₁, ⟨hb₁, hb₁U⟩, rfl⟩ ⟨b₂, ⟨hb₂, hb₂U⟩, heq⟩
  have hsub : (⟨b₁, hb₁U⟩ : U) = ⟨b₂, hb₂U⟩ := hinj (by simpa using heq.symm)
  have : b₁ = b₂ := congrArg (fun u : U => (u : SL3)) hsub
  subst this
  exact (Set.disjoint_left.mp h hb₁) hb₂

theorem orbImg_inter_U (U : Subgroup SL3) (x : X3) (B : Set SL3) :
    orbImg U x B = orbImg U x (B ∩ (U : Set SL3)) := by
  simp only [orbImg, Set.inter_assoc, Set.inter_self]

theorem orbImg_inter_image {U : Subgroup SL3} {x : X3}
    (hinj : Function.Injective (fun u : U => (u : SL3) • x)) (B C : Set SL3) :
    orbImg U x B ∩ orbImg U x C = orbImg U x (B ∩ C) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro y ⟨⟨b₁, ⟨hb₁, hb₁U⟩, rfl⟩, ⟨b₂, ⟨hb₂, hb₂U⟩, heq⟩⟩
    have hsub : (⟨b₁, hb₁U⟩ : U) = ⟨b₂, hb₂U⟩ := hinj (by simpa using heq.symm)
    have hb : b₁ = b₂ := congrArg (fun u : U => (u : SL3)) hsub
    subst hb
    exact ⟨b₁, ⟨⟨hb₁, hb₂⟩, hb₁U⟩, rfl⟩
  · rintro y ⟨b, ⟨⟨hbB, hbC⟩, hbU⟩, rfl⟩
    exact ⟨⟨b, ⟨hbB, hbU⟩, rfl⟩, ⟨b, ⟨hbC, hbU⟩, rfl⟩⟩


/-! ## 2.  Conditional level measures -/

/-- `nuLevel` evaluated on a Borel set: it is the ratio of the conditional kernel masses of the
orbit images. -/
theorem nuLevel_apply {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    [StandardBorelSpace X3] {μ : Measure X3} [IsProbabilityMeasure μ]
    {Z : ℕ → Set X3} {m : ℕ → MeasurableSpace X3} {G : ℕ → Set X3} {z : X3}
    (hinj : Function.Injective (fun u : U => (u : SL3) • z))
    {B : Set SL3} (hB : MeasurableSet B) :
    nuLevel U μ Z m G z B = refKernel μ Z m G z (orbImg U z B) *
      (refKernel μ Z m G z (orbImg U z (Box1 U)))⁻¹ := by
  have hB1 : MeasurableSet (Box1 U) := lbf_measurableSet_Box1 hUcl
  have h1 : refPush U μ Z m G z (Box1 U) = refKernel μ Z m G z (orbImg U z (Box1 U)) := by
    rw [refPush, pushOrbit_apply_of_injective hUcl hinj _ hB1]
    simp only [orbImg]
  have h2 : refPush U μ Z m G z B = refKernel μ Z m G z (orbImg U z B) := by
    rw [refPush, pushOrbit_apply_of_injective hUcl hinj _ hB]
    simp only [orbImg]
  rw [nuLevel, Measure.smul_apply, smul_eq_mul, h1, h2, mul_comm]

/-- The orbit image of a set contained in a shape is contained in the atom. -/
theorem orbImg_subset_atom {U : Subgroup SL3} {m : MeasurableSpace X3} {x : X3}
    {S : Set SL3} (h : S ∩ (U : Set SL3) ⊆ shape m U x) : orbImg U x S ⊆ atom m x := by
  rintro y hy
  rw [orbImg, Set.mem_image] at hy
  obtain ⟨g, hg, rfl⟩ := hy
  exact (h hg).2

/-- If `κ₂ = c · κ₁` on `a` and both `s`, `s₁` are inside `a`, then the ratios of the two masses
agree for `κ₁` and `κ₂`. -/
theorem ratio_eq_of_propor {κ₁ κ₂ : Measure X3} {a : Set X3}
    (h : Work.EKLComp.Propor (κ₁.restrict a) (κ₂.restrict a)) {s s₁ : Set X3}
    (hs : MeasurableSet s) (hs₁ : MeasurableSet s₁) (hsa : s ⊆ a) (hs₁a : s₁ ⊆ a) :
    κ₁ s * (κ₁ s₁)⁻¹ = κ₂ s * (κ₂ s₁)⁻¹ := by
  obtain ⟨c, hc0, hct, hc⟩ := h
  have e1 : κ₂ s = c * κ₁ s := by
    have hcong := congrArg (fun ρ : Measure X3 => ρ s) hc
    rwa [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs,
      Measure.restrict_apply hs, Set.inter_comm, Set.inter_eq_right.mpr hsa] at hcong
  have e2 : κ₂ s₁ = c * κ₁ s₁ := by
    have hcong := congrArg (fun ρ : Measure X3 => ρ s₁) hc
    rwa [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hs₁,
      Measure.restrict_apply hs₁, Set.inter_comm, Set.inter_eq_right.mpr hs₁a] at hcong
  rw [e1, e2, ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), mul_comm c (κ₁ s),
    mul_assoc (κ₁ s) c (c⁻¹ * (κ₁ s₁)⁻¹), ← mul_assoc c c⁻¹ ((κ₁ s₁)⁻¹),
    ENNReal.mul_inv_cancel hc0 hct, one_mul]

/-- **Independence of the level.**  For two plaque algebras at the same point `x` whose
conditional measures are proportional on the common atom, the normalised level measures agree on
any Borel set contained in the intersection of the two shapes. -/
theorem level_ratio_eq {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    {μ : Measure X3} [IsProbabilityMeasure μ] [StandardBorelSpace X3]
    {Z₁ Z₂ : Set X3} {a₁ a₂ : Work.EKLComp.SigAlg} {x : X3}
    (hinj : Function.Injective (fun u : U => (u : SL3) • x))
    (hpropor : Work.EKLComp.ProporOn (ProbabilityTheory.condExpKernel (μ.restrict Z₁) a₁.m x)
      (ProbabilityTheory.condExpKernel (μ.restrict Z₂) a₂.m x) (atom a₁.m x ∩ atom a₂.m x))
    {S S₁ : Set SL3} (hS : MeasurableSet S) (hS₁ : MeasurableSet S₁)
    (hSsub : S ⊆ shape a₁.m U x ∩ shape a₂.m U x)
    (hS₁sub : S₁ ⊆ shape a₁.m U x ∩ shape a₂.m U x) :
    ProbabilityTheory.condExpKernel (μ.restrict Z₁) a₁.m x (orbImg U x S) *
        (ProbabilityTheory.condExpKernel (μ.restrict Z₁) a₁.m x (orbImg U x S₁))⁻¹ =
      ProbabilityTheory.condExpKernel (μ.restrict Z₂) a₂.m x (orbImg U x S) *
        (ProbabilityTheory.condExpKernel (μ.restrict Z₂) a₂.m x (orbImg U x S₁))⁻¹ := by
  refine ratio_eq_of_propor hpropor (measurableSet_orbImg hUcl hinj hS)
    (measurableSet_orbImg hUcl hinj hS₁) ?_ ?_
  · exact Set.subset_inter (orbImg_subset_atom fun g hg => (hSsub hg.1).1)
      (orbImg_subset_atom fun g hg => (hSsub hg.1).2)
  · exact Set.subset_inter (orbImg_subset_atom fun g hg => (hS₁sub hg.1).1)
      (orbImg_subset_atom fun g hg => (hS₁sub hg.1).2)

/-- Monotonicity of the displacement boxes. -/
theorem V_mono' {r r' : ℝ} (h : r ≤ r') : V r ⊆ V r' :=
  fun _ hg _ _ => lt_of_lt_of_le (hg _ _) h

theorem Ucl_subset_V_of_le {U : Subgroup SL3} {r r' : ℝ} (h : r < r') : Ucl U r ⊆ V r' :=
  fun _ hg _ _ => lt_of_le_of_lt (hg.2 _ _) h

/-! ## 3.  The level formula on bounded sets -/

/-- **The level formula.**  On a bounded Borel set `A ⊆ U`, the patched measure `nuFull x`
coincides with the normalised conditional measure of the plaque algebra of level `K`, for every
level `K` which is large enough (relative to the radius of `A`). -/
theorem nuFull_apply_bounded {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    {μ : Measure X3} [IsProbabilityMeasure μ] [StandardBorelSpace X3] (D : FlowerData U μ)
    {x : X3} (hinj : Function.Injective (fun u : U => (u : SL3) • x))
    (hcover : ∀ k : ℕ, x ∈ D.G k (sel (D.G k) x))
    (hpropor : ∀ (k i k' i' : ℕ), x ∈ D.Z k i → x ∈ D.Z k' i' →
      Work.EKLComp.ProporOn (ProbabilityTheory.condExpKernel (μ.restrict (D.Z k i)) (D.m k i) x)
        (ProbabilityTheory.condExpKernel (μ.restrict (D.Z k' i')) (D.m k' i') x)
        (atom (D.m k i) x ∩ atom (D.m k' i') x))
    {K N : ℕ} (hKN : N + 5 ≤ K) {A : Set SL3} (hA : MeasurableSet A)
    (hAU : A ⊆ (U : Set SL3)) (hAb : A ⊆ Ucl U (N : ℝ)) :
    nuFull U μ D.Z D.m D.G x A =
      refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x A) *
        (refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x (Box1 U)))⁻¹ := by
  classical
  have hKj : ∀ j : ℕ, j ≤ N → (((j : ℕ) : ℝ) + 2) ≤ ((K : ℕ) : ℝ) + 3 := by
    intro j hj
    have h1 : (j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hj
    have h2 : (N : ℝ) + 5 ≤ (K : ℝ) := by exact_mod_cast hKN
    linarith
  rw [nuFull, Measure.sum_apply _ hA]
  have hzero : ∀ j ∉ Finset.range (N + 1),
      ((nuLevel U μ (D.Z j) (D.m j) (D.G j) x).restrict (piece U j)) A = 0 := by
    intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    rw [Measure.restrict_apply hA]
    have hempty : A ∩ piece U j = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hyA, hyj⟩
      have h1 : y ∈ Ucl U (N : ℝ) := hAb hyA
      have h2 : y ∈ (Ucl U (j : ℝ))ᶜ :=
        piece_subset_compl_Ucl (U := U) (k := j) (by omega) hyj
      exact h2 (Ucl_mono (by exact_mod_cast (by omega : N ≤ j)) h1)
    rw [hempty, measure_empty]
  rw [tsum_eq_sum hzero]
  have hterm : ∀ j ∈ Finset.range (N + 1),
      ((nuLevel U μ (D.Z j) (D.m j) (D.G j) x).restrict (piece U j)) A =
        refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x (A ∩ piece U j)) *
          (refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x (Box1 U)))⁻¹ := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have hpiece : MeasurableSet (piece U j) := lbf_measurableSet_piece hUcl j
    rw [Measure.restrict_apply hA, nuLevel_apply hUcl hinj (hA.inter hpiece)]
    have hxZj : x ∈ D.Z j (sel (D.G j) x) := D.sub j _ (hcover j)
    have hxZK : x ∈ D.Z K (sel (D.G K) x) := D.sub K _ (hcover K)
    have hVj : A ∩ piece U j ⊆ V (((j : ℕ) : ℝ) + 3) ∩ (U : Set SL3) := by
      rintro y ⟨hyA, hyj⟩
      exact ⟨V_mono' (by linarith) (piece_subset_V U j hyj), piece_subset_U U j hyj⟩
    have hVK : A ∩ piece U j ⊆ V (((K : ℕ) : ℝ) + 3) ∩ (U : Set SL3) := by
      rintro y ⟨hyA, hyj⟩
      have hNK : (N : ℝ) + 1 ≤ (K : ℝ) + 3 := by
        have h2 : (N : ℝ) + 5 ≤ (K : ℝ) := by exact_mod_cast hKN
        linarith
      have h1 : y ∈ V (((N : ℕ) : ℝ) + 1) :=
        Ucl_subset_V_of_le (by linarith) (hAb hyA)
      exact ⟨V_mono' hNK h1, piece_subset_U U j hyj⟩
    have hB1j : Box1 U ⊆ V (((j : ℕ) : ℝ) + 3) ∩ (U : Set SL3) := by
      intro y hy
      exact ⟨V_mono' (by linarith) (Box1_subset_V U hy), by rw [Box1_eq_Ucl] at hy; exact hy.1⟩
    have hB1K : Box1 U ⊆ V (((K : ℕ) : ℝ) + 3) ∩ (U : Set SL3) := by
      intro y hy
      exact ⟨V_mono' (by linarith) (Box1_subset_V U hy),
        by rw [Box1_eq_Ucl] at hy; exact hy.1⟩
    have hshapes : A ∩ piece U j ⊆
        shape (D.m j (sel (D.G j) x)) U x ∩ shape (D.m K (sel (D.G K) x)) U x :=
      Set.subset_inter (hVj.trans (D.shape_sub j (sel (D.G j) x) x (hcover j)))
        (hVK.trans (D.shape_sub K (sel (D.G K) x) x (hcover K)))
    have hshapes1 : Box1 U ⊆
        shape (D.m j (sel (D.G j) x)) U x ∩ shape (D.m K (sel (D.G K) x)) U x :=
      Set.subset_inter (hB1j.trans (D.shape_sub j (sel (D.G j) x) x (hcover j)))
        (hB1K.trans (D.shape_sub K (sel (D.G K) x) x (hcover K)))
    have hpr := hpropor j (sel (D.G j) x) K (sel (D.G K) x) hxZj hxZK
    exact level_ratio_eq hUcl hinj hpr (hA.inter hpiece) (lbf_measurableSet_Box1 hUcl)
      hshapes hshapes1
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  have hdisp : Set.PairwiseDisjoint (((Finset.range (N + 1) : Finset ℕ)) : Set ℕ)
      (fun j => orbImg U x (A ∩ piece U j)) := by
    intro j hj j' hj' hjj'
    simp only [Finset.mem_coe, Finset.mem_range] at hj hj'
    refine orbImg_disjoint hinj ?_
    rw [Set.disjoint_left]
    rintro y ⟨hyA, hyj⟩ ⟨-, hyj'⟩
    rcases lt_or_gt_of_ne hjj' with h | h
    · exact Set.disjoint_left.mp (piece_disjoint h) hyj hyj'
    · exact Set.disjoint_left.mp (piece_disjoint h) hyj' hyj
  have hmeas : ∀ j ∈ Finset.range (N + 1), MeasurableSet (orbImg U x (A ∩ piece U j)) :=
    fun j _ => measurableSet_orbImg hUcl hinj (hA.inter (lbf_measurableSet_piece hUcl j))
  rw [← measure_biUnion_finset hdisp hmeas]
  have hunion : (⋃ j ∈ Finset.range (N + 1), orbImg U x (A ∩ piece U j)) = orbImg U x A := by
    rw [show (⋃ j ∈ Finset.range (N + 1), orbImg U x (A ∩ piece U j))
        = orbImg U x (⋃ j ∈ Finset.range (N + 1), (A ∩ piece U j)) from by
      simp only [orbImg, Set.iUnion_inter, Set.image_iUnion]]
    congr 1
    refine Set.Subset.antisymm ?_ ?_
    · exact Set.iUnion_subset fun j => Set.iUnion_subset fun _ => Set.inter_subset_left
    · intro y hy
      simp only [Set.mem_iUnion]
      have hyU : y ∈ (U : Set SL3) := hAU hy
      obtain ⟨j, hj⟩ : ∃ j, y ∈ piece U j := by
        have h : y ∈ ⋃ k, piece U k := by rw [iUnion_piece]; exact hyU
        exact Set.mem_iUnion.mp h
      have hjle : j ≤ N := by
        by_contra hcon
        have hcon' : N < j := by omega
        have h1 : y ∈ Ucl U (N : ℝ) := hAb hy
        have h2 : y ∈ (Ucl U (j : ℝ))ᶜ := piece_subset_compl_Ucl (U := U) (by omega) hj
        exact h2 (Ucl_mono (by exact_mod_cast le_of_lt hcon') h1)
      exact ⟨j, Finset.mem_range.mpr (by omega), hy, hj⟩
  rw [hunion]

/-! ## 4.  An entrywise estimate for products -/

/-- Right multiplication by a fixed `u` maps the entrywise box of radius `r` around `1` into an
explicitly bounded entrywise box. -/
theorem exists_bound_mul {u : SL3} (r : ℝ) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : SL3,
      (∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ r) →
      ∀ i j, |((g * u : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C := by
  classical
  set M : ℝ := (Finset.univ : Finset (Fin 3 × Fin 3)).sup' Finset.univ_nonempty
    (fun p => |(u : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) with hMdef
  set C₀ : ℝ := (Finset.univ : Finset (Fin 3 × Fin 3)).sup' Finset.univ_nonempty
    (fun p => |(u : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) with hC₀def
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact le_trans (abs_nonneg _) (Finset.le_sup' (s := Finset.univ)
      (f := fun p : Fin 3 × Fin 3 => |(u : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|)
      (Finset.mem_univ (0, 0)))
  have hM : ∀ i j, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ M := by
    intro i j
    rw [hMdef]
    exact Finset.le_sup' (s := Finset.univ)
      (f := fun p : Fin 3 × Fin 3 => |(u : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|)
      (Finset.mem_univ (i, j))
  have hC₀ : ∀ i j, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C₀ := by
    intro i j
    rw [hC₀def]
    exact Finset.le_sup' (s := Finset.univ)
      (f := fun p : Fin 3 × Fin 3 => |(u : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) (Finset.mem_univ (i, j))
  refine ⟨C₀ + 3 * r * M, ?_, ?_⟩
  · have : 0 ≤ 3 * r * M := by positivity
    have hC₀nn : 0 ≤ C₀ := le_trans (abs_nonneg _) (hC₀ 0 0)
    linarith
  · intro g hg i j
    have hsplit : (((g * u : SL3)) : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
        = (∑ l : Fin 3, ((g : Matrix (Fin 3) (Fin 3) ℝ) i l
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i l) * (u : Matrix (Fin 3) (Fin 3) ℝ) l j)
          + ((u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) := by
      rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply]
      have h1 : ∑ l : Fin 3, (1 : Matrix (Fin 3) (Fin 3) ℝ) i l
          * (u : Matrix (Fin 3) (Fin 3) ℝ) l j = (u : Matrix (Fin 3) (Fin 3) ℝ) i j := by
        simp [Matrix.one_apply]
      simp only [sub_mul, Finset.sum_sub_distrib]
      rw [h1]
      ring
    rw [hsplit]
    refine le_trans (abs_add_le _ _) ?_
    have hsum : |∑ l : Fin 3, ((g : Matrix (Fin 3) (Fin 3) ℝ) i l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i l) * (u : Matrix (Fin 3) (Fin 3) ℝ) l j| ≤ 3 * r * M := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      rw [show (∑ l : Fin 3, |((g : Matrix (Fin 3) (Fin 3) ℝ) i l
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i l) * (u : Matrix (Fin 3) (Fin 3) ℝ) l j|)
          = ∑ l : Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) i l
              - (1 : Matrix (Fin 3) (Fin 3) ℝ) i l| * |(u : Matrix (Fin 3) (Fin 3) ℝ) l j|
        from by simp only [abs_mul]]
      calc ∑ l : Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) i l
              - (1 : Matrix (Fin 3) (Fin 3) ℝ) i l| * |(u : Matrix (Fin 3) (Fin 3) ℝ) l j|
          ≤ ∑ _l : Fin 3, r * M := by
            refine Finset.sum_le_sum fun l _ => ?_
            exact mul_le_mul (hg i l) (hM l j) (abs_nonneg _) hr
        _ = 3 * r * M := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
    linarith [hsum, hC₀ i j]

/-! ## 5.  The good points -/

/-- The index selected by `sel` contains the point, whenever some index does. -/
theorem sel_mem {G : ℕ → Set X3} {x : X3} (h : ∃ k, x ∈ G k) : x ∈ G (sel G x) := by
  classical
  rw [sel]
  rw [dif_pos h]
  exact Nat.find_spec h

/-- The pointwise conditions satisfied almost everywhere, and used at the good points. -/
def GoodAt (U : Subgroup SL3) (μ : Measure X3) [IsFiniteMeasure μ]
    (D : FlowerData U μ) (z : X3) : Prop :=
  Function.Injective (fun u : U => (u : SL3) • z) ∧
  (∀ k : ℕ, z ∈ D.G k (sel (D.G k) z)) ∧
  (∀ s : Set X3, IsOpen s → z ∈ s → 0 < μ s) ∧
  (∀ (k i k' i' : ℕ), z ∈ D.Z k i → z ∈ D.Z k' i' →
    Work.EKLComp.ProporOn (ProbabilityTheory.condExpKernel (μ.restrict (D.Z k i)) (D.m k i) z)
      (ProbabilityTheory.condExpKernel (μ.restrict (D.Z k' i')) (D.m k' i') z)
      (atom (D.m k i) z ∩ atom (D.m k' i') z)) ∧
  (∀ k : ℕ, (∃ i : ℕ, z ∈ D.G k i) →
    0 < refKernel μ (D.Z k) (D.m k) (D.G k) z (orbImg U z (V (1 / 2))))

theorem ae_goodAt {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    {μ : Measure X3} [IsProbabilityMeasure μ] [StandardBorelSpace X3] (D : FlowerData U μ)
    (hfree : ∀ᵐ x ∂μ, Function.Injective (fun u : U => (u : SL3) • x))
    (hprop : ProporPiece U μ) (hpos : PosPiece U μ) :
    ∀ᵐ z ∂μ, GoodAt U μ D z := by
  classical
  -- (2) the bases cover a.e.
  have hcov : ∀ᵐ z ∂μ, ∀ k : ℕ, z ∈ D.G k (sel (D.G k) z) := by
    refine MeasureTheory.ae_all_iff.mpr fun k => ?_
    have h1 : ∀ᵐ z ∂μ, z ∈ ⋃ i, D.G k i := by
      have h := (MeasureTheory.measure_eq_zero_iff_ae_notMem (μ := μ)).mp (D.cover k)
      filter_upwards [h] with z hz
      simpa using hz
    filter_upwards [h1] with z hz
    exact sel_mem (Set.mem_iUnion.mp hz)
  -- (3) positivity of open neighbourhoods
  have hopen : ∀ᵐ z ∂μ, ∀ s : Set X3, IsOpen s → z ∈ s → 0 < μ s :=
    Work.EKLC7.ae_isOpen_pos (μ := μ)
  -- (4) proportionality of conditional measures of two plaque algebras
  have hpr : ∀ᵐ z ∂μ, ∀ (k i k' i' : ℕ), z ∈ D.Z k i → z ∈ D.Z k' i' →
      Work.EKLComp.ProporOn (ProbabilityTheory.condExpKernel (μ.restrict (D.Z k i)) (D.m k i) z)
        (ProbabilityTheory.condExpKernel (μ.restrict (D.Z k' i')) (D.m k' i') z)
        (atom (D.m k i) z ∩ atom (D.m k' i') z) := by
    refine MeasureTheory.ae_all_iff.mpr fun k => ?_
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    refine MeasureTheory.ae_all_iff.mpr fun k' => ?_
    refine MeasureTheory.ae_all_iff.mpr fun i' => ?_
    filter_upwards [hprop (D.Z k i) (D.Z k' i') ⟨D.m k i⟩ ⟨D.m k' i'⟩
      (D.isPlaque k i) (D.isPlaque k' i')] with a ha
    intro h1 h2
    exact ha ⟨h1, h2⟩
  -- (5) positivity of the conditional measure of the unit ball
  have hpk : ∀ᵐ z ∂μ, ∀ k : ℕ, (∃ i : ℕ, z ∈ D.G k i) →
      0 < refKernel μ (D.Z k) (D.m k) (D.G k) z (orbImg U z (V (1 / 2))) := by
    refine MeasureTheory.ae_all_iff.mpr fun k => ?_
    have hZmeas : ∀ i : ℕ, MeasurableSet (D.Z k i) := fun i =>
      (D.isPlaque k i).1 _ (D.isPlaque k i).2.2.1
    have hbad : μ (⋃ i, (D.Z k i ∩ {z : X3 | ¬ (0 < ProbabilityTheory.condExpKernel
        (μ.restrict (D.Z k i)) (D.m k i) z
        ((fun g : SL3 => g • z) '' (V (1 / 2) ∩ (U : Set SL3))))})) = 0 := by
      refine MeasureTheory.measure_iUnion_null fun i => ?_
      have hO : IsOpen (V (1 / 2)) := (Work.EKLContract.Lemmas.V_open_one (1 / 2) (by norm_num)).1
      have h1O : (1 : SL3) ∈ V (1 / 2) :=
        (Work.EKLContract.Lemmas.V_open_one (1 / 2) (by norm_num)).2
      have hae := hpos (D.Z k i) ⟨D.m k i⟩ (D.isPlaque k i) (V (1 / 2)) hO h1O
      have hzero : (μ.restrict (D.Z k i)) {z : X3 | ¬ (0 < ProbabilityTheory.condExpKernel
          (μ.restrict (D.Z k i)) (D.m k i) z
          ((fun g : SL3 => g • z) '' (V (1 / 2) ∩ (U : Set SL3))))} = 0 := by
        simpa using (MeasureTheory.ae_iff.mp hae)
      rw [MeasureTheory.Measure.restrict_apply' (hZmeas i)] at hzero
      rw [Set.inter_comm]
      exact hzero
    have h1 : ∀ᵐ z ∂μ, z ∉ ⋃ i, (D.Z k i ∩ {z : X3 | ¬ (0 < ProbabilityTheory.condExpKernel
        (μ.restrict (D.Z k i)) (D.m k i) z
        ((fun g : SL3 => g • z) '' (V (1 / 2) ∩ (U : Set SL3))))}) :=
      (MeasureTheory.measure_eq_zero_iff_ae_notMem (μ := μ)).mp hbad
    filter_upwards [h1] with z hz hG
    obtain ⟨i, hi⟩ := hG
    have hi0 : z ∈ D.G k (sel (D.G k) z) := sel_mem ⟨i, hi⟩
    have hne : ¬ (¬ (0 < ProbabilityTheory.condExpKernel (μ.restrict (D.Z k (sel (D.G k) z)))
        (D.m k (sel (D.G k) z)) z
        ((fun g : SL3 => g • z) '' (V (1 / 2) ∩ (U : Set SL3))))) := by
      intro hcon
      exact hz (Set.mem_iUnion.mpr ⟨sel (D.G k) z,
        ⟨D.sub k _ hi0, hcon⟩⟩)
    have hfin : 0 < ProbabilityTheory.condExpKernel (μ.restrict (D.Z k (sel (D.G k) z)))
        (D.m k (sel (D.G k) z)) z
        ((fun g : SL3 => g • z) '' (V (1 / 2) ∩ (U : Set SL3))) := not_not.mp hne
    simpa only [refKernel, orbImg] using hfin
  filter_upwards [hfree, hcov, hopen, hpr, hpk] with z h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

/-! ## 6.  The comparison at `u • x` -/

theorem measurableSet_mul_image {u : SL3} {E : Set SL3} (hE : MeasurableSet E) :
    MeasurableSet ((fun g : SL3 => g * u) '' E) := by
  have h : (fun g : SL3 => g * u) '' E = (fun g : SL3 => g * u⁻¹) ⁻¹' E := by
    ext z
    constructor
    · rintro ⟨e, he, rfl⟩
      show (e * u) * u⁻¹ ∈ E
      rw [mul_assoc, mul_inv_cancel, mul_one]
      exact he
    · intro hz
      exact ⟨z * u⁻¹, hz, by show (z * u⁻¹) * u = z; group⟩
  rw [h]
  exact hE.preimage (by fun_prop)

theorem orbImg_mul_inv_image (U : Subgroup SL3) {u : U} {x : X3} (E : Set SL3) :
    orbImg U ((u : SL3) • x) ((fun g : SL3 => g * (u : SL3)⁻¹) '' E) = orbImg U x E := by
  ext z
  rw [mem_orbImg, mem_orbImg]
  constructor
  · rintro ⟨g, ⟨e, he, rfl⟩, hgU, hgz⟩
    have heU : e ∈ U := by
      have h1 : e = (e * (u : SL3)⁻¹) * (u : SL3) := by group
      rw [h1]
      exact U.mul_mem hgU u.2
    refine ⟨e, he, heU, ?_⟩
    have h2 : (e * (u : SL3)⁻¹) • ((u : SL3) • x) = e • x := by
      have hscal : (e * (u : SL3)⁻¹) * (u : SL3) = e := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
      rw [← mul_smul, hscal]
    rw [← hgz, h2]
  · rintro ⟨e, he, heU, hez⟩
    refine ⟨e * (u : SL3)⁻¹, ⟨e, he, rfl⟩, U.mul_mem heU (U.inv_mem u.2), ?_⟩
    have h2 : (e * (u : SL3)⁻¹) • ((u : SL3) • x) = e • x := by
      have hscal : (e * (u : SL3)⁻¹) * (u : SL3) = e := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
      rw [← mul_smul, hscal]
    rw [h2, hez]

theorem orbImg_Box1_mul (U : Subgroup SL3) {u : U} {x : X3} :
    orbImg U ((u : SL3) • x) (Box1 U) =
      orbImg U x ((fun g : SL3 => g * (u : SL3)) '' (Box1 U)) := by
  ext z
  rw [mem_orbImg, mem_orbImg]
  constructor
  · rintro ⟨b, hb, hbU, hbz⟩
    refine ⟨b * (u : SL3), ⟨b, hb, rfl⟩, U.mul_mem (by rw [Box1_eq_Ucl] at hb; exact hb.1) u.2, ?_⟩
    rw [mul_smul, hbz]
  · rintro ⟨g, ⟨b, hb, rfl⟩, -, hgz⟩
    refine ⟨b, hb, by rw [Box1_eq_Ucl] at hb; exact hb.1, ?_⟩
    rw [← hgz, mul_smul]

/-- Membership in the shape at `u • x` for the plaque algebra of `x`'s atom. -/
theorem mem_shape_smul {U : Subgroup SL3} {m : MeasurableSpace X3} {x : X3} {u : U}
    (h : (u : SL3) • x ∈ atom m x) {g : SL3} :
    g ∈ shape m U ((u : SL3) • x) ↔ g * (u : SL3) ∈ shape m U x := by
  constructor
  · rintro ⟨hgU, hgatom⟩
    refine ⟨U.mul_mem hgU u.2, ?_⟩
    rw [Work.EKLComp.atom_eq_of_mem m h] at hgatom
    rwa [← mul_smul] at hgatom
  · rintro ⟨hguU, hguatom⟩
    have hgU : g ∈ U := by
      have h1 : g = (g * (u : SL3)) * (u : SL3)⁻¹ := by group
      rw [h1]
      exact U.mul_mem hguU (U.inv_mem u.2)
    refine ⟨hgU, ?_⟩
    show g • ((u : SL3) • x) ∈ atom m ((u : SL3) • x)
    rw [Work.EKLComp.atom_eq_of_mem m h]
    rwa [← mul_smul]

/-- The level is large enough (for a fixed `u`) to make all the containments used in the
comparison work. -/
def LevelBig (U : Subgroup SL3) (u : SL3) (K : ℕ) : Prop :=
  u ∈ V ((K : ℝ) + 3) ∧
  (∀ g ∈ Box1 U, g * u ∈ V ((K : ℝ) + 3)) ∧
  (∀ w ∈ V (1 / 2) ∩ (U : Set SL3), w * u ∈ V ((K : ℝ) + 3))

theorem LevelBig.mono {U : Subgroup SL3} {u : SL3} {K K' : ℕ} (h : LevelBig U u K) (hKK' : K ≤ K') :
    LevelBig U u K' := by
  obtain ⟨h1, h2, h3⟩ := h
  have hcast : (K : ℝ) ≤ (K' : ℝ) := by exact_mod_cast hKK'
  have hV : V ((K : ℝ) + 3) ⊆ V ((K' : ℝ) + 3) := V_mono' (by linarith)
  exact ⟨hV h1, fun g hg => hV (h2 g hg), fun w hw => hV (h3 w hw)⟩

theorem exists_levelBig (U : Subgroup SL3) (u : SL3) : ∃ K : ℕ, LevelBig U u K := by
  obtain ⟨C₁, -, hC₁⟩ := exists_bound_mul (u := u) 1 (by norm_num)
  obtain ⟨C₂, -, hC₂⟩ := exists_bound_mul (u := u) (1 / 2) (by norm_num)
  obtain ⟨C₀, hC₀⟩ : ∃ C : ℝ, ∀ i j, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C :=
    ⟨(Finset.univ : Finset (Fin 3 × Fin 3)).sup' Finset.univ_nonempty
      (fun p => |(u : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|),
      fun i j => Finset.le_sup' (s := Finset.univ)
        (f := fun p : Fin 3 × Fin 3 => |(u : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) (Finset.mem_univ (i, j))⟩
  set Kc : ℕ := Nat.ceil (max C₀ (max C₁ C₂)) with hKc
  have hC₀le : C₀ ≤ (Kc : ℝ) := by
    rw [hKc]
    exact le_trans (le_max_left _ _) (Nat.le_ceil _)
  have hC₁le : C₁ ≤ (Kc : ℝ) := by
    rw [hKc]
    exact le_trans (le_trans (le_max_left C₁ C₂) (le_max_right C₀ (max C₁ C₂))) (Nat.le_ceil _)
  have hC₂le : C₂ ≤ (Kc : ℝ) := by
    rw [hKc]
    exact le_trans (le_trans (le_max_right C₁ C₂) (le_max_right C₀ (max C₁ C₂))) (Nat.le_ceil _)
  refine ⟨Kc, ?_, ?_, ?_⟩
  · intro i j
    exact lt_of_le_of_lt (hC₀ i j) (by linarith)
  · intro g hg i j
    refine lt_of_le_of_lt (hC₁ g (fun i j => ?_) i j) (by linarith)
    rw [Box1_eq_Ucl] at hg
    exact hg.2 i j
  · intro w hw i j
    refine lt_of_le_of_lt (hC₂ w (fun i j => ?_) i j) (by linarith)
    exact le_of_lt (hw.1 i j)

/-- **The comparison of the level-`K` measures at `u • x`.**  For a good point `x` and `u ∈ U`,
the normalised level-`K` measure at `u • x` (with `u • x`'s own index) and the same measure at
`x` (with `x`'s index, transported to `u • x` through the common atom) have the same ratio on the
two orbit images. -/
theorem transfer_ratio {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    {μ : Measure X3} [IsProbabilityMeasure μ] [StandardBorelSpace X3] (D : FlowerData U μ)
    {x : X3} (u : U) (hxG : GoodAt U μ D x) (hyG : GoodAt U μ D ((u : SL3) • x))
    {K : ℕ} (hK : LevelBig U (u : SL3) K)
    {E : Set SL3} (hE : MeasurableSet E)
    (hEx : E ⊆ shape (D.m K (sel (D.G K) x)) U x)
    (hEy : (fun g : SL3 => g * (u : SL3)⁻¹) '' E
      ⊆ shape (D.m K (sel (D.G K) ((u : SL3) • x))) U ((u : SL3) • x)) :
    (refKernel μ (D.Z K) (D.m K) (D.G K) ((u : SL3) • x)
        (orbImg U ((u : SL3) • x) ((fun g : SL3 => g * (u : SL3)⁻¹) '' E)) *
      (refKernel μ (D.Z K) (D.m K) (D.G K) ((u : SL3) • x)
        (orbImg U ((u : SL3) • x) (Box1 U)))⁻¹) =
    (refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x E) *
      (refKernel μ (D.Z K) (D.m K) (D.G K) x
        (orbImg U x ((fun g : SL3 => g * (u : SL3)) '' (Box1 U))))⁻¹) := by
  classical
  -- `u • x` lies in the atom of `x`
  have hatom : (u : SL3) • x ∈ atom (D.m K (sel (D.G K) x)) x :=
    (D.shape_sub K (sel (D.G K) x) x (hxG.2.1 K) ⟨hK.1, u.2⟩).2
  -- the same-atom identity for the conditional kernel
  have hκ : ProbabilityTheory.condExpKernel (μ.restrict (D.Z K (sel (D.G K) x)))
        (D.m K (sel (D.G K) x)) ((u : SL3) • x)
      = ProbabilityTheory.condExpKernel (μ.restrict (D.Z K (sel (D.G K) x)))
        (D.m K (sel (D.G K) x)) x :=
    (Work.EKLComp.kernel_atom_const (𝔪 := ⟨D.m K (sel (D.G K) x)⟩) hatom).symm
  have hZy : (u : SL3) • x ∈ D.Z K (sel (D.G K) x) :=
    ((D.isPlaque K (sel (D.G K) x)).2.2.2 x (D.sub K _ (hxG.2.1 K))).1 hatom
  have hZy' : (u : SL3) • x ∈ D.Z K (sel (D.G K) ((u : SL3) • x)) :=
    D.sub K _ (hyG.2.1 K)
  have hpr := hyG.2.2.2.1 K (sel (D.G K) x) K (sel (D.G K) ((u : SL3) • x)) hZy hZy'
  have hratio := level_ratio_eq (U := U) hUcl (μ := μ)
    (Z₁ := D.Z K (sel (D.G K) x)) (Z₂ := D.Z K (sel (D.G K) ((u : SL3) • x)))
    (a₁ := ⟨D.m K (sel (D.G K) x)⟩) (a₂ := ⟨D.m K (sel (D.G K) ((u : SL3) • x))⟩)
    (x := (u : SL3) • x) (S := (fun g : SL3 => g * (u : SL3)⁻¹) '' E) (S₁ := Box1 U)
    hyG.1 hpr (measurableSet_mul_image hE) (lbf_measurableSet_Box1 hUcl) ?_ ?_
  · rw [orbImg_mul_inv_image U E, orbImg_Box1_mul U] at hratio
    rw [hκ] at hratio
    rw [orbImg_mul_inv_image U E, orbImg_Box1_mul U]
    simp only [refKernel]
    exact hratio.symm
  · refine Set.subset_inter ?_ hEy
    rintro s ⟨e, he, rfl⟩
    rw [mem_shape_smul (m := D.m K (sel (D.G K) x)) hatom]
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hEx he
  · refine Set.subset_inter ?_ (Set.Subset.trans ?_ (D.shape_sub K (sel (D.G K) ((u : SL3) • x))
      ((u : SL3) • x) (hyG.2.1 K)))
    · intro b hb
      rw [mem_shape_smul (m := D.m K (sel (D.G K) x)) hatom]
      exact (D.shape_sub K (sel (D.G K) x) x (hxG.2.1 K))
        ⟨hK.2.1 b hb, U.mul_mem (by rw [Box1_eq_Ucl] at hb; exact hb.1) u.2⟩
    · intro b hb
      exact ⟨V_mono' (by have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K; linarith)
        (Box1_subset_V U hb),
        by rw [Box1_eq_Ucl] at hb; exact hb.1⟩

/-- Positivity transfers from `κ₂` to `κ₁` when the two are proportional on a set containing
`S`. -/
theorem ne_zero_of_propor {κ₁ κ₂ : Measure X3} {a S : Set X3}
    (h : Work.EKLComp.Propor (κ₁.restrict a) (κ₂.restrict a))
    (hS : MeasurableSet S) (hSa : S ⊆ a) (h2 : κ₂ S ≠ 0) : κ₁ S ≠ 0 := by
  obtain ⟨c, hc0, hct, hc⟩ := h
  have hcong := congrArg (fun ρ : Measure X3 => ρ S) hc
  rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hS, Measure.restrict_apply hS,
    Set.inter_eq_left.mpr hSa] at hcong
  intro h0
  rw [h0, mul_zero] at hcong
  exact h2 hcong

/-- Positivity of the conditional measure of the plaque `B₁ u` at `u • x`, transported to
`x`'s index. -/
theorem kernel_pos_mul_Box1 {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    {μ : Measure X3} [IsProbabilityMeasure μ] [StandardBorelSpace X3] (D : FlowerData U μ)
    {x : X3} (u : U) (hxG : GoodAt U μ D x) (hyG : GoodAt U μ D ((u : SL3) • x))
    {K : ℕ} (hK : LevelBig U (u : SL3) K) :
    0 < refKernel μ (D.Z K) (D.m K) (D.G K) x
      (orbImg U x ((fun g : SL3 => g * (u : SL3)) '' (Box1 U))) := by
  classical
  have hatom : (u : SL3) • x ∈ atom (D.m K (sel (D.G K) x)) x :=
    (D.shape_sub K (sel (D.G K) x) x (hxG.2.1 K) ⟨hK.1, u.2⟩).2
  have hκ : ProbabilityTheory.condExpKernel (μ.restrict (D.Z K (sel (D.G K) x)))
        (D.m K (sel (D.G K) x)) ((u : SL3) • x)
      = ProbabilityTheory.condExpKernel (μ.restrict (D.Z K (sel (D.G K) x)))
        (D.m K (sel (D.G K) x)) x :=
    (Work.EKLComp.kernel_atom_const (𝔪 := ⟨D.m K (sel (D.G K) x)⟩) hatom).symm
  have hZy : (u : SL3) • x ∈ D.Z K (sel (D.G K) x) :=
    ((D.isPlaque K (sel (D.G K) x)).2.2.2 x (D.sub K _ (hxG.2.1 K))).1 hatom
  have hZy' : (u : SL3) • x ∈ D.Z K (sel (D.G K) ((u : SL3) • x)) :=
    D.sub K _ (hyG.2.1 K)
  have hpr := hyG.2.2.2.1 K (sel (D.G K) x) K (sel (D.G K) ((u : SL3) • x)) hZy hZy'
  -- the plaque is inside the common atom
  have hsub : orbImg U ((u : SL3) • x) (V (1 / 2)) ⊆
      atom (D.m K (sel (D.G K) x)) ((u : SL3) • x)
        ∩ atom (D.m K (sel (D.G K) ((u : SL3) • x))) ((u : SL3) • x) := by
    refine Set.subset_inter ?_ ?_
    · refine orbImg_subset_atom ?_
      intro w hw
      rw [mem_shape_smul (m := D.m K (sel (D.G K) x)) hatom]
      exact (D.shape_sub K (sel (D.G K) x) x (hxG.2.1 K)) ⟨hK.2.2 w hw, U.mul_mem hw.2 u.2⟩
    · refine orbImg_subset_atom ?_
      intro w hw
      exact (D.shape_sub K (sel (D.G K) ((u : SL3) • x)) ((u : SL3) • x) (hyG.2.1 K))
        ⟨V_mono' (by have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K; linarith) hw.1, hw.2⟩
  have hVmeas : MeasurableSet (orbImg U ((u : SL3) • x) (V (1 / 2))) :=
    measurableSet_orbImg hUcl hyG.1
      ((Work.EKLContract.Lemmas.V_open_one (1 / 2) (by norm_num)).1.measurableSet)
  -- positivity at `y` for `y`'s own index, transferred through the proportionality
  have hpos' : 0 < ProbabilityTheory.condExpKernel
      (μ.restrict (D.Z K (sel (D.G K) ((u : SL3) • x))))
      (D.m K (sel (D.G K) ((u : SL3) • x))) ((u : SL3) • x)
      (orbImg U ((u : SL3) • x) (V (1 / 2))) :=
    hyG.2.2.2.2 K ⟨sel (D.G K) ((u : SL3) • x), hyG.2.1 K⟩
  have hne : ProbabilityTheory.condExpKernel (μ.restrict (D.Z K (sel (D.G K) x)))
      (D.m K (sel (D.G K) x)) x (orbImg U ((u : SL3) • x) (V (1 / 2))) ≠ 0 := by
    rw [← hκ]
    exact ne_zero_of_propor hpr hVmeas hsub (ne_of_gt hpos')
  have hsub2 : orbImg U ((u : SL3) • x) (V (1 / 2))
      ⊆ orbImg U x ((fun g : SL3 => g * (u : SL3)) '' (Box1 U)) := by
    intro z hz
    rw [mem_orbImg] at hz ⊢
    obtain ⟨w, hw, hwU, hwz⟩ := hz
    refine ⟨w * (u : SL3), ⟨w, V_half_inter_subset_Box1 U ⟨hw, hwU⟩, rfl⟩, ?_, ?_⟩
    · exact U.mul_mem hwU u.2
    · rw [mul_smul]; exact hwz
  exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hne) (measure_mono hsub2)

/-! ## 7.  The comparison lemma and the main theorem -/

theorem kernel_univ (U : Subgroup SL3) (μ : Measure X3) [IsFiniteMeasure μ]
    [StandardBorelSpace X3] (Z : ℕ → Set X3) (m : ℕ → MeasurableSpace X3)
    (G : ℕ → Set X3) (z : X3) : refKernel μ Z m G z Set.univ = 1 := by
  rw [refKernel]
  exact (ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure z).measure_univ

/-- The counting identity `(r / q) * (p / r) = p / q`. -/
theorem ennreal_div_swap (p q r : ENNReal) (hr0 : r ≠ 0) (hrt : r ≠ ⊤) :
    (r * q⁻¹) * (p * r⁻¹) = p * q⁻¹ := by
  rw [← div_eq_mul_inv (a := r) (b := q), ← div_eq_mul_inv (a := p) (b := r),
    ← ENNReal.mul_div_mul_comm (a := r) (b := p) (c := q) (d := r) (Or.inr hrt) (Or.inr hr0),
    mul_comm q r, ENNReal.mul_div_mul_left p q hr0 hrt, div_eq_mul_inv]

theorem iUnion_Ucl (U : Subgroup SL3) : (⋃ n : ℕ, Ucl U (n : ℝ)) = (U : Set SL3) := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun n => fun g hg => hg.1) ?_
  intro g hg
  set R : ℝ := (Finset.univ : Finset (Fin 3 × Fin 3)).sup' Finset.univ_nonempty
    (fun p => |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) with hR
  refine Set.mem_iUnion.mpr ⟨Nat.ceil R, ⟨hg, fun i j => ?_⟩⟩
  exact le_trans (Finset.le_sup' (s := Finset.univ)
    (f := fun p : Fin 3 × Fin 3 => |(g : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) p.1 p.2|) (Finset.mem_univ (i, j))) (Nat.le_ceil R)

/-- The constant of the comparison does not depend on the level. -/
theorem level_const_eq {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    {μ : Measure X3} [IsProbabilityMeasure μ] [StandardBorelSpace X3] (D : FlowerData U μ)
    {x : X3} (u : U) (hxG : GoodAt U μ D x) {K K' : ℕ}
    (hK : LevelBig U (u : SL3) K) (hK' : LevelBig U (u : SL3) K') :
    refKernel μ (D.Z K) (D.m K) (D.G K) x
        (orbImg U x ((fun g : SL3 => g * (u : SL3)) '' (Box1 U))) *
      (refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x (Box1 U)))⁻¹ =
    refKernel μ (D.Z K') (D.m K') (D.G K') x
        (orbImg U x ((fun g : SL3 => g * (u : SL3)) '' (Box1 U))) *
      (refKernel μ (D.Z K') (D.m K') (D.G K') x (orbImg U x (Box1 U)))⁻¹ := by
  classical
  -- the shape containments
  have hsh : ∀ (L : ℕ), LevelBig U (u : SL3) L →
      (fun g : SL3 => g * (u : SL3)) '' (Box1 U)
        ⊆ shape (D.m L (sel (D.G L) x)) U x := by
    intro L hL g hg
    obtain ⟨b, hb, rfl⟩ := hg
    exact (D.shape_sub L (sel (D.G L) x) x (hxG.2.1 L)) ⟨hL.2.1 b hb,
      U.mul_mem (by rw [Box1_eq_Ucl] at hb; exact hb.1) u.2⟩
  have hsh1 : ∀ (L : ℕ), (Box1 U) ⊆ shape (D.m L (sel (D.G L) x)) U x := by
    intro L g hg
    exact (D.shape_sub L (sel (D.G L) x) x (hxG.2.1 L))
      ⟨V_mono' (by have h0 : (0 : ℝ) ≤ (L : ℝ) := Nat.cast_nonneg L; linarith)
        (Box1_subset_V U hg), by rw [Box1_eq_Ucl] at hg; exact hg.1⟩
  have hpr := hxG.2.2.2.1 K (sel (D.G K) x) K' (sel (D.G K') x)
    (D.sub K _ (hxG.2.1 K)) (D.sub K' _ (hxG.2.1 K'))
  have hratio := level_ratio_eq (U := U) hUcl (μ := μ)
    (Z₁ := D.Z K (sel (D.G K) x)) (Z₂ := D.Z K' (sel (D.G K') x))
    (a₁ := ⟨D.m K (sel (D.G K) x)⟩) (a₂ := ⟨D.m K' (sel (D.G K') x)⟩)
    (x := x) (S := (fun g : SL3 => g * (u : SL3)) '' (Box1 U)) (S₁ := Box1 U)
    hxG.1 hpr (measurableSet_mul_image (lbf_measurableSet_Box1 hUcl))
    (lbf_measurableSet_Box1 hUcl)
    (fun g hg => ⟨hsh K hK hg, hsh K' hK' hg⟩)
    (fun g hg => ⟨hsh1 K hg, hsh1 K' hg⟩)
  simpa only [refKernel] using hratio

/-- **The comparison for a bounded Borel set.** -/
theorem nuFull_smul_bounded {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    {μ : Measure X3} [IsProbabilityMeasure μ] [StandardBorelSpace X3] (D : FlowerData U μ)
    {x : X3} (u : U) (hxG : GoodAt U μ D x) (hyG : GoodAt U μ D ((u : SL3) • x))
    {M K : ℕ} (hKM : M + 5 ≤ K) (hK : LevelBig U (u : SL3) K)
    {E : Set SL3} (hE : MeasurableSet E) (hEU : E ⊆ (U : Set SL3))
    (hEM : E ⊆ Ucl U (M : ℝ))
    (hEu : (fun g : SL3 => g * (u : SL3)⁻¹) '' E ⊆ (U : Set SL3))
    (hEuM : (fun g : SL3 => g * (u : SL3)⁻¹) '' E ⊆ Ucl U (M : ℝ)) :
    nuFull U μ D.Z D.m D.G x E =
      (refKernel μ (D.Z K) (D.m K) (D.G K) x
          (orbImg U x ((fun g : SL3 => g * (u : SL3)) '' (Box1 U))) *
        (refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x (Box1 U)))⁻¹) *
      nuFull U μ D.Z D.m D.G ((u : SL3) • x) ((fun g : SL3 => g * (u : SL3)⁻¹) '' E) := by
  classical
  have hx := nuFull_apply_bounded (U := U) hUcl D (K := K) (N := M) hxG.1 hxG.2.1 hxG.2.2.2.1
    hKM hE hEU hEM
  have hy := nuFull_apply_bounded (U := U) hUcl (x := (u : SL3) • x) D (K := K) (N := M)
    hyG.1 hyG.2.1 hyG.2.2.2.1 hKM (measurableSet_mul_image hE) hEu hEuM
  have hMK : (M : ℝ) + 1 ≤ (K : ℝ) + 3 := by
    have h : (M : ℝ) + 5 ≤ (K : ℝ) := by exact_mod_cast hKM
    linarith
  have hEx : E ⊆ shape (D.m K (sel (D.G K) x)) U x := by
    refine Set.Subset.trans ?_ (D.shape_sub K (sel (D.G K) x) x (hxG.2.1 K))
    intro g hg
    exact ⟨V_mono' hMK (Ucl_subset_V_of_le (by linarith) (hEM hg)), hEU hg⟩
  have hEy : (fun g : SL3 => g * (u : SL3)⁻¹) '' E
      ⊆ shape (D.m K (sel (D.G K) ((u : SL3) • x))) U ((u : SL3) • x) := by
    refine Set.Subset.trans ?_ (D.shape_sub K (sel (D.G K) ((u : SL3) • x)) ((u : SL3) • x)
      (hyG.2.1 K))
    intro g hg
    exact ⟨V_mono' hMK (Ucl_subset_V_of_le (by linarith) (hEuM hg)), hEu hg⟩
  have htr := transfer_ratio hUcl D u hxG hyG hK hE hEx hEy
  have hrne : refKernel μ (D.Z K) (D.m K) (D.G K) x
      (orbImg U x ((fun g : SL3 => g * (u : SL3)) '' (Box1 U))) ≠ 0 :=
    ne_of_gt (kernel_pos_mul_Box1 hUcl D u hxG hyG hK)
  have hrtop : refKernel μ (D.Z K) (D.m K) (D.G K) x
      (orbImg U x ((fun g : SL3 => g * (u : SL3)) '' (Box1 U))) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ _)) ?_)
    rw [refKernel]
    rw [(ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure x).measure_univ]
    exact ENNReal.one_lt_top
  rw [hx, hy.trans htr]
  exact (ennreal_div_swap _ _ _ hrne hrtop).symm

/-- The preimage of a set under right translation by `u` is the image under right translation
by `u⁻¹`. -/
theorem preimage_mul_eq_image_mul_inv (u : SL3) (A : Set SL3) :
    (fun g : SL3 => g * u) ⁻¹' A = (fun g : SL3 => g * u⁻¹) '' A := by
  ext z
  constructor
  · intro hz
    exact ⟨z * u, hz, by show (z * u) * u⁻¹ = z; rw [mul_assoc, mul_inv_cancel, mul_one]⟩
  · rintro ⟨a, ha, rfl⟩
    show (a * u⁻¹) * u ∈ A
    rw [mul_assoc, inv_mul_cancel, mul_one]
    exact ha

/-- The main theorem: the equivariance field. -/
theorem leafwise_equivariant_field_free {U : Subgroup Work.EKLContract.SL3}
    (hUcl : IsClosed (U : Set Work.EKLContract.SL3))
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    [StandardBorelSpace Work.EKLContract.X3] (D : Work.EKLRelCross.FlowerData U μ)
    (hprop : Work.EKLRelCross.ProporPiece U μ) (hpos : Work.EKLRelCross.PosPiece U μ)
    (hfree : ∀ᵐ x ∂μ, Function.Injective (fun u : U => (u : Work.EKLContract.SL3) • x)) :
    ∃ X' : Set Work.EKLContract.X3, MeasurableSet X' ∧ μ X'ᶜ = 0 ∧
      (∀ x ∈ X', Function.Injective (fun u : U => (u : Work.EKLContract.SL3) • x)) ∧
      ∀ x ∈ X', ∀ u ∈ U, u • x ∈ X' → ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
        Work.EKLRelCross.nuFull U μ D.Z D.m D.G x =
          c • (Work.EKLRelCross.nuFull U μ D.Z D.m D.G (u • x)).map (fun g => g * u) := by
  classical
  have hgood : ∀ᵐ z ∂μ, GoodAt U μ D z := ae_goodAt hUcl D hfree hprop hpos
  have hBad : μ {z : X3 | ¬ GoodAt U μ D z} = 0 := MeasureTheory.ae_iff.mp hgood
  have hX' : ∀ z : X3, z ∈ (toMeasurable μ {z : X3 | ¬ GoodAt U μ D z})ᶜ → GoodAt U μ D z :=
    fun z hz => not_not.mp fun h => hz (subset_toMeasurable μ _ h)
  refine ⟨(toMeasurable μ {z : X3 | ¬ GoodAt U μ D z})ᶜ,
    (measurableSet_toMeasurable μ _).compl, ?_, ?_, ?_⟩
  · rw [compl_compl, MeasureTheory.measure_toMeasurable, hBad]
  · intro x hx
    exact (hX' x hx).1
  · intro x hx u hu hyx
    set u₀ : U := ⟨u, hu⟩ with hu₀def
    have hu₀ : (u₀ : SL3) = u := rfl
    rw [← hu₀] at hyx ⊢
    have hxG : GoodAt U μ D x := hX' x hx
    have hyG : GoodAt U μ D ((u₀ : SL3) • x) := hX' ((u₀ : SL3) • x) hyx
    obtain ⟨Kc, hKc⟩ := exists_levelBig U ((u₀ : SL3))
    set c : ENNReal := refKernel μ (D.Z Kc) (D.m Kc) (D.G Kc) x
        (orbImg U x ((fun g : SL3 => g * (u₀ : SL3)) '' (Box1 U))) *
      (refKernel μ (D.Z Kc) (D.m Kc) (D.G Kc) x (orbImg U x (Box1 U)))⁻¹ with hcdef
    have hnum_ne : refKernel μ (D.Z Kc) (D.m Kc) (D.G Kc) x
        (orbImg U x ((fun g : SL3 => g * (u₀ : SL3)) '' (Box1 U))) ≠ 0 :=
      ne_of_gt (kernel_pos_mul_Box1 hUcl D u₀ hxG hyG hKc)
    have hbox_sub : orbImg U x (V (1 / 2)) ⊆ orbImg U x (Box1 U) := by
      intro z hz
      rw [mem_orbImg] at hz ⊢
      obtain ⟨w, hw, hwU, rfl⟩ := hz
      exact ⟨w, V_half_inter_subset_Box1 U ⟨hw, hwU⟩, hwU, rfl⟩
    have hden_ne : refKernel μ (D.Z Kc) (D.m Kc) (D.G Kc) x (orbImg U x (Box1 U)) ≠ 0 := by
      have hpos' : 0 < refKernel μ (D.Z Kc) (D.m Kc) (D.G Kc) x (orbImg U x (V (1 / 2))) :=
        hxG.2.2.2.2 Kc ⟨sel (D.G Kc) x, hxG.2.1 Kc⟩
      exact ne_of_gt (lt_of_lt_of_le hpos' (measure_mono hbox_sub))
    have hden_lt : refKernel μ (D.Z Kc) (D.m Kc) (D.G Kc) x (orbImg U x (Box1 U)) ≠ ⊤ := by
      refine ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ _)) ?_)
      rw [refKernel, (ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure x).measure_univ]
      exact ENNReal.one_lt_top
    have hnum_lt : refKernel μ (D.Z Kc) (D.m Kc) (D.G Kc) x
        (orbImg U x ((fun g : SL3 => g * (u₀ : SL3)) '' (Box1 U))) ≠ ⊤ := by
      refine ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ _)) ?_)
      rw [refKernel, (ProbabilityTheory.IsMarkovKernel.isProbabilityMeasure x).measure_univ]
      exact ENNReal.one_lt_top
    refine ⟨c, ?_, ?_, ?_⟩
    · rw [hcdef]
      exact ne_of_gt (ENNReal.mul_pos hnum_ne (ENNReal.inv_ne_zero.mpr hden_lt))
    · rw [hcdef]
      intro h0
      rcases ENNReal.mul_eq_top.mp h0 with ⟨-, hb⟩ | ⟨ha, -⟩
      · exact hden_ne (ENNReal.inv_eq_top.mp hb)
      · exact hnum_lt ha
    · refine Measure.ext fun A hA => ?_
      -- the per-set comparison for bounded Borel sets
      choose Cb hCb using fun N : ℕ =>
        exists_bound_mul (u := (u₀ : SL3)⁻¹) (r := (N : ℝ)) (Nat.cast_nonneg N)
      have hbdd : ∀ (M : ℕ) (E : Set SL3), MeasurableSet E → E ⊆ (U : Set SL3) →
          E ⊆ Ucl U (M : ℝ) →
          (fun g : SL3 => g * (u₀ : SL3)⁻¹) '' E ⊆ (U : Set SL3) →
          (fun g : SL3 => g * (u₀ : SL3)⁻¹) '' E ⊆ Ucl U (M : ℝ) →
          nuFull U μ D.Z D.m D.G x E =
            c * nuFull U μ D.Z D.m D.G ((u₀ : SL3) • x)
              ((fun g : SL3 => g * (u₀ : SL3)⁻¹) '' E) := by
        intro M E hE hEU hEM hEu hEuM
        have hbig : LevelBig U ((u₀ : SL3)) (max Kc (M + 5)) := LevelBig.mono hKc (le_max_left _ _)
        have hKM : M + 5 ≤ max Kc (M + 5) := le_max_right _ _
        have hmain := nuFull_smul_bounded hUcl D u₀ hxG hyG hKM hbig hE hEU hEM hEu hEuM
        have hconst : (refKernel μ (D.Z (max Kc (M + 5))) (D.m (max Kc (M + 5)))
              (D.G (max Kc (M + 5))) x
              (orbImg U x ((fun g : SL3 => g * (u₀ : SL3)) '' (Box1 U))) *
            (refKernel μ (D.Z (max Kc (M + 5))) (D.m (max Kc (M + 5)))
              (D.G (max Kc (M + 5))) x (orbImg U x (Box1 U)))⁻¹) = c := by
          rw [hcdef]
          exact level_const_eq hUcl D u₀ hxG hbig hKc
        rw [hmain, hconst]
      -- the constant `M` is carried by `U`
      set M₀ : Measure SL3 := (nuFull U μ D.Z D.m D.G ((u₀ : SL3) • x)).map
        (fun g => g * (u₀ : SL3)) with hM₀def
      have hM₀carried : M₀ ((U : Set SL3)ᶜ) = 0 := by
        rw [hM₀def, Measure.map_apply (measurable_mul_const (u₀ : SL3)) hUcl.measurableSet.compl]
        have hset : (fun g : SL3 => g * (u₀ : SL3)) ⁻¹' ((U : Set SL3)ᶜ) = (U : Set SL3)ᶜ := by
          ext z
          simp only [Set.mem_preimage, Set.mem_compl_iff]
          constructor
          · intro hz hzU
            exact hz (U.mul_mem hzU u₀.2)
          · intro hz hzU'
            exact hz (by
              have h1 : z = (z * (u₀ : SL3)) * (u₀ : SL3)⁻¹ := by group
              rw [h1]
              exact U.mul_mem hzU' (U.inv_mem u₀.2))
        rw [hset]
        exact lbf_nuFull_carried hUcl μ D.Z D.m D.G ((u₀ : SL3) • x)
      -- the approximating sequence
      set f : ℕ → Set SL3 := fun N => A ∩ (U : Set SL3) ∩ Ucl U ((N : ℕ) : ℝ) with hfdef
      have hfmeas : ∀ N, MeasurableSet (f N) := fun N =>
        (hA.inter hUcl.measurableSet).inter (lbf_measurableSet_Ucl hUcl _)
      have hmono : Monotone f := fun i j hij z hz =>
        ⟨hz.1, Ucl_mono (by exact_mod_cast hij) hz.2⟩
      have hfU : ∀ N, f N ⊆ (U : Set SL3) := fun N z hz => hz.1.2
      have hUf : (⋃ N, f N) = A ∩ (U : Set SL3) := by
        ext z
        simp only [Set.mem_iUnion, hfdef, Set.mem_inter_iff]
        constructor
        · rintro ⟨N, ⟨⟨hzA, hzU⟩, -⟩⟩
          exact ⟨hzA, hzU⟩
        · rintro ⟨hzA, hzU⟩
          obtain ⟨N, hzN⟩ := Set.mem_iUnion.mp (by rw [iUnion_Ucl]; exact hzU)
          exact ⟨N, ⟨⟨hzA, hzU⟩, hzN⟩⟩
      have hνxcar : (nuFull U μ D.Z D.m D.G x) A
          = (nuFull U μ D.Z D.m D.G x) (A ∩ (U : Set SL3)) := by
        have h0 : (nuFull U μ D.Z D.m D.G x) ((U : Set SL3)ᶜ) = 0 :=
          lbf_nuFull_carried hUcl μ D.Z D.m D.G x
        have hdecomp := MeasureTheory.measure_inter_add_sdiff
          (μ := nuFull U μ D.Z D.m D.G x) A hUcl.measurableSet
        have hdiff : (nuFull U μ D.Z D.m D.G x) (A \ (U : Set SL3)) = 0 :=
          le_antisymm (le_trans (measure_mono fun z hz => hz.2) (le_of_eq h0)) bot_le
        calc (nuFull U μ D.Z D.m D.G x) A
            = (nuFull U μ D.Z D.m D.G x) (A ∩ (U : Set SL3))
              + (nuFull U μ D.Z D.m D.G x) (A \ (U : Set SL3)) := hdecomp.symm
          _ = (nuFull U μ D.Z D.m D.G x) (A ∩ (U : Set SL3)) := by rw [hdiff, add_zero]
      have hMA : M₀ A = M₀ (A ∩ (U : Set SL3)) := by
        have hdecomp := MeasureTheory.measure_inter_add_sdiff (μ := M₀) A hUcl.measurableSet
        have hdiff : M₀ (A \ (U : Set SL3)) = 0 :=
          le_antisymm (le_trans (measure_mono fun z hz => hz.2) (le_of_eq hM₀carried)) bot_le
        calc M₀ A = M₀ (A ∩ (U : Set SL3)) + M₀ (A \ (U : Set SL3)) := hdecomp.symm
          _ = M₀ (A ∩ (U : Set SL3)) := by rw [hdiff, add_zero]
      have hMA2 : M₀ (A ∩ (U : Set SL3)) = ⨆ N, M₀ (f N) := by
        rw [← hmono.measure_iUnion, hUf]
      have hstep : ∀ N, (nuFull U μ D.Z D.m D.G x) (f N) = c * M₀ (f N) := by
        intro N
        have hfN : f N ⊆ Ucl U ((max N (Nat.ceil (Cb N) + 1) : ℕ) : ℝ) := fun z hz =>
          Ucl_mono (by exact_mod_cast le_max_left N _) hz.2
        have hfuN : (fun g : SL3 => g * (u₀ : SL3)⁻¹) '' (f N)
            ⊆ Ucl U ((max N (Nat.ceil (Cb N) + 1) : ℕ) : ℝ) := by
          intro z hz
          obtain ⟨e, he, rfl⟩ := hz
          refine ⟨U.mul_mem (he.1.2) (U.inv_mem u₀.2), fun i j => ?_⟩
          refine le_trans ((hCb N).2 e (fun i j => (he.2).2 i j) i j) ?_
          have h3 : Cb N ≤ ((Nat.ceil (Cb N) + 1 : ℕ) : ℝ) := by
            push_cast
            linarith [Nat.le_ceil (Cb N)]
          have h4 : ((Nat.ceil (Cb N) + 1 : ℕ) : ℝ)
              ≤ ((max N (Nat.ceil (Cb N) + 1) : ℕ) : ℝ) := by
            exact_mod_cast le_max_right N _
          linarith
        have h := hbdd (max N (Nat.ceil (Cb N) + 1)) (f N) (hfmeas N) (hfU N) hfN
          (fun z hz => by
            obtain ⟨e, he, rfl⟩ := hz
            exact U.mul_mem (hfU N he) (U.inv_mem u₀.2)) hfuN
        rw [h, hM₀def,
          Measure.map_apply (measurable_mul_const (u₀ : SL3)) (hfmeas N),
          preimage_mul_eq_image_mul_inv]
      calc (nuFull U μ D.Z D.m D.G x) A
          = (nuFull U μ D.Z D.m D.G x) (A ∩ (U : Set SL3)) := hνxcar
        _ = ⨆ N, (nuFull U μ D.Z D.m D.G x) (f N) := by
            rw [← hmono.measure_iUnion, hUf]
        _ = ⨆ N, c * M₀ (f N) := iSup_congr fun N => hstep N
        _ = c * ⨆ N, M₀ (f N) := (ENNReal.mul_iSup c _).symm
        _ = c * M₀ A := by rw [← hMA2, ← hMA]
        _ = (c • M₀) A := by rw [Measure.smul_apply, smul_eq_mul]

end Work.EKLRelCross
