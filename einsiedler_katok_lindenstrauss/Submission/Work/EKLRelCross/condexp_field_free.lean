import Mathlib
import Submission.Work.EKLRelCross.LeafCtor
import Submission.Work.EKLRelCross.leafwise_base_fields_free
import Submission.Work.EKLRelCross.measurableSet_orbImg
import Submission.Work.EKLRelCross.pushOrbit_apply_of_injective
import Submission.Work.EKLComp.condExpKernel_atom
import Submission.Work.EKLComp.exists_leafCoord
import Submission.Work.EKLRelCross.cfree_integral_pushOrbit_restrict

/-!
# `Work.EKLRelCross.condexp_field_free`

The `condexp` field (Eisa, Pisa 6.3(iv)) for the patched family `nuFull` of `LeafCtor.lean`.

The file is self-contained: the auxiliary lemmas `cfree_*` below are a copy of the annulus
bookkeeping and of the patching identity `cfree_nuFull_apply_bounded` (which evaluates the sum
defining `nuFull` on a bounded Borel set) with names prefixed to avoid clashing with the
`leafwise_equivariant_field_free` development.
-/

open MeasureTheory
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-! ## 1.  Annuli and elementary containments -/

theorem cfree_Ucl_mono {U : Subgroup SL3} {r r' : ℝ} (h : r ≤ r') : Ucl U r ⊆ Ucl U r' :=
  fun g hg => ⟨hg.1, fun i j => le_trans (hg.2 i j) h⟩

theorem cfree_piece_subset_Ucl (U : Subgroup SL3) (k : ℕ) : piece U k ⊆ Ucl U ((k : ℝ) + 1) := by
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

theorem cfree_Ucl_subset_V {U : Subgroup SL3} {r r' : ℝ} (h : r < r') : Ucl U r ⊆ V r' :=
  fun _ hg _ _ => lt_of_le_of_lt (hg.2 _ _) h

theorem cfree_piece_subset_V (U : Subgroup SL3) (k : ℕ) : piece U k ⊆ V ((k : ℝ) + 2) :=
  fun _ hg => cfree_Ucl_subset_V (by linarith) (cfree_piece_subset_Ucl U k hg)

theorem cfree_Box1_subset_V (U : Subgroup SL3) : Box1 U ⊆ V 2 := by
  intro g hg
  rw [Box1_eq_Ucl] at hg
  exact cfree_Ucl_subset_V (by norm_num) hg

theorem cfree_V_half_inter_subset_Box1 (U : Subgroup SL3) : V (1 / 2) ∩ (U : Set SL3) ⊆ Box1 U := by
  intro g hg
  rw [Box1_eq_Ucl]
  exact ⟨hg.2, fun i j => le_of_lt (lt_trans (hg.1 i j) (by norm_num))⟩

theorem cfree_piece_disjoint {U : Subgroup SL3} {i j : ℕ} (hij : i < j) :
    Disjoint (piece U i) (piece U j) := by
  rw [Set.disjoint_left]
  intro g hgi hgj
  have h1 : g ∈ Ucl U ((i : ℝ) + 1) := cfree_piece_subset_Ucl U i hgi
  have h2 : g ∈ Ucl U (j : ℝ) :=
    cfree_Ucl_mono (by exact_mod_cast (Nat.succ_le_of_lt hij)) h1
  have h3 : g ∈ (Ucl U (j : ℝ))ᶜ :=
    piece_subset_compl_Ucl (U := U) (k := j) (by omega) hgj
  exact h3 h2

theorem cfree_iUnion_piece (U : Subgroup SL3) : (⋃ k : ℕ, piece U k) = (U : Set SL3) := by
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
theorem cfree_orbImg_disjoint {U : Subgroup SL3} {x : X3}
    (hinj : Function.Injective (fun u : U => (u : SL3) • x)) {B₁ B₂ : Set SL3}
    (h : Disjoint B₁ B₂) : Disjoint (orbImg U x B₁) (orbImg U x B₂) := by
  rw [Set.disjoint_left]
  rintro y ⟨b₁, ⟨hb₁, hb₁U⟩, rfl⟩ ⟨b₂, ⟨hb₂, hb₂U⟩, heq⟩
  have hsub : (⟨b₁, hb₁U⟩ : U) = ⟨b₂, hb₂U⟩ := hinj (by simpa using heq.symm)
  have : b₁ = b₂ := congrArg (fun u : U => (u : SL3)) hsub
  subst this
  exact (Set.disjoint_left.mp h hb₁) hb₂

theorem cfree_orbImg_inter_U (U : Subgroup SL3) (x : X3) (B : Set SL3) :
    orbImg U x B = orbImg U x (B ∩ (U : Set SL3)) := by
  simp only [orbImg, Set.inter_assoc, Set.inter_self]

theorem cfree_orbImg_inter_image {U : Subgroup SL3} {x : X3}
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
theorem cfree_nuLevel_apply {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
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
theorem cfree_orbImg_subset_atom {U : Subgroup SL3} {m : MeasurableSpace X3} {x : X3}
    {S : Set SL3} (h : S ∩ (U : Set SL3) ⊆ shape m U x) : orbImg U x S ⊆ atom m x := by
  rintro y hy
  rw [orbImg, Set.mem_image] at hy
  obtain ⟨g, hg, rfl⟩ := hy
  exact (h hg).2

/-- If `κ₂ = c · κ₁` on `a` and both `s`, `s₁` are inside `a`, then the ratios of the two masses
agree for `κ₁` and `κ₂`. -/
theorem cfree_ratio_eq_of_propor {κ₁ κ₂ : Measure X3} {a : Set X3}
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
theorem cfree_level_ratio_eq {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
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
  refine cfree_ratio_eq_of_propor hpropor (measurableSet_orbImg hUcl hinj hS)
    (measurableSet_orbImg hUcl hinj hS₁) ?_ ?_
  · exact Set.subset_inter (cfree_orbImg_subset_atom fun g hg => (hSsub hg.1).1)
      (cfree_orbImg_subset_atom fun g hg => (hSsub hg.1).2)
  · exact Set.subset_inter (cfree_orbImg_subset_atom fun g hg => (hS₁sub hg.1).1)
      (cfree_orbImg_subset_atom fun g hg => (hS₁sub hg.1).2)

/-- Monotonicity of the displacement boxes. -/
theorem cfree_V_mono' {r r' : ℝ} (h : r ≤ r') : V r ⊆ V r' :=
  fun _ hg _ _ => lt_of_lt_of_le (hg _ _) h

theorem cfree_Ucl_subset_V_of_le {U : Subgroup SL3} {r r' : ℝ} (h : r < r') : Ucl U r ⊆ V r' :=
  fun _ hg _ _ => lt_of_le_of_lt (hg.2 _ _) h

/-! ## 3.  The level formula on bounded sets -/

/-- **The level formula.**  On a bounded Borel set `A ⊆ U`, the patched measure `nuFull x`
coincides with the normalised conditional measure of the plaque algebra of level `K`, for every
level `K` which is large enough (relative to the radius of `A`). -/
theorem cfree_nuFull_apply_bounded {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
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
      exact h2 (cfree_Ucl_mono (by exact_mod_cast (by omega : N ≤ j)) h1)
    rw [hempty, measure_empty]
  rw [tsum_eq_sum hzero]
  have hterm : ∀ j ∈ Finset.range (N + 1),
      ((nuLevel U μ (D.Z j) (D.m j) (D.G j) x).restrict (piece U j)) A =
        refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x (A ∩ piece U j)) *
          (refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x (Box1 U)))⁻¹ := by
    intro j hj
    simp only [Finset.mem_range] at hj
    have hpiece : MeasurableSet (piece U j) := lbf_measurableSet_piece hUcl j
    rw [Measure.restrict_apply hA, cfree_nuLevel_apply hUcl hinj (hA.inter hpiece)]
    have hxZj : x ∈ D.Z j (sel (D.G j) x) := D.sub j _ (hcover j)
    have hxZK : x ∈ D.Z K (sel (D.G K) x) := D.sub K _ (hcover K)
    have hVj : A ∩ piece U j ⊆ V (((j : ℕ) : ℝ) + 3) ∩ (U : Set SL3) := by
      rintro y ⟨hyA, hyj⟩
      exact ⟨cfree_V_mono' (by linarith) (cfree_piece_subset_V U j hyj), piece_subset_U U j hyj⟩
    have hVK : A ∩ piece U j ⊆ V (((K : ℕ) : ℝ) + 3) ∩ (U : Set SL3) := by
      rintro y ⟨hyA, hyj⟩
      have hNK : (N : ℝ) + 1 ≤ (K : ℝ) + 3 := by
        have h2 : (N : ℝ) + 5 ≤ (K : ℝ) := by exact_mod_cast hKN
        linarith
      have h1 : y ∈ V (((N : ℕ) : ℝ) + 1) :=
        cfree_Ucl_subset_V_of_le (by linarith) (hAb hyA)
      exact ⟨cfree_V_mono' hNK h1, piece_subset_U U j hyj⟩
    have hB1j : Box1 U ⊆ V (((j : ℕ) : ℝ) + 3) ∩ (U : Set SL3) := by
      intro y hy
      exact ⟨cfree_V_mono' (by linarith) (cfree_Box1_subset_V U hy), by rw [Box1_eq_Ucl] at hy; exact hy.1⟩
    have hB1K : Box1 U ⊆ V (((K : ℕ) : ℝ) + 3) ∩ (U : Set SL3) := by
      intro y hy
      exact ⟨cfree_V_mono' (by linarith) (cfree_Box1_subset_V U hy),
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
    exact cfree_level_ratio_eq hUcl hinj hpr (hA.inter hpiece) (lbf_measurableSet_Box1 hUcl)
      hshapes hshapes1
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  have hdisp : Set.PairwiseDisjoint (((Finset.range (N + 1) : Finset ℕ)) : Set ℕ)
      (fun j => orbImg U x (A ∩ piece U j)) := by
    intro j hj j' hj' hjj'
    simp only [Finset.mem_coe, Finset.mem_range] at hj hj'
    refine cfree_orbImg_disjoint hinj ?_
    rw [Set.disjoint_left]
    rintro y ⟨hyA, hyj⟩ ⟨-, hyj'⟩
    rcases lt_or_gt_of_ne hjj' with h | h
    · exact Set.disjoint_left.mp (cfree_piece_disjoint h) hyj hyj'
    · exact Set.disjoint_left.mp (cfree_piece_disjoint h) hyj' hyj
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
        have h : y ∈ ⋃ k, piece U k := by rw [cfree_iUnion_piece]; exact hyU
        exact Set.mem_iUnion.mp h
      have hjle : j ≤ N := by
        by_contra hcon
        have hcon' : N < j := by omega
        have h1 : y ∈ Ucl U (N : ℝ) := hAb hy
        have h2 : y ∈ (Ucl U (j : ℝ))ᶜ := piece_subset_compl_Ucl (U := U) (by omega) hj
        exact h2 (cfree_Ucl_mono (by exact_mod_cast le_of_lt hcon') h1)
      exact ⟨j, Finset.mem_range.mpr (by omega), hy, hj⟩
  rw [hunion]
/-! ## 1b.  The selected index -/

/-- The index selected by `sel` contains the point, whenever some index does. -/
theorem cfree_sel_mem {G : ℕ → Set X3} {x : X3} (h : ∃ k, x ∈ G k) : x ∈ G (sel G x) := by
  classical
  rw [sel]
  rw [dif_pos h]
  exact Nat.find_spec h

theorem cfree_pointwise (U : Subgroup SL3) (hUcl : IsClosed (U : Set SL3))
    {μ : Measure X3} [IsProbabilityMeasure μ] (D : FlowerData U μ)
    (hprop : ProporPiece U μ) (hpos : PosPiece U μ)
    (hfree : ∀ᵐ x ∂μ, Function.Injective (fun u : U => (u : SL3) • x))
    (Z : Set X3) (𝔪 : Work.EKLComp.SigAlg) (hplaq : IsPlaqueAlgebra U Z 𝔪.m)
    (f : X3 → ℝ) (hf : Measurable[instMeasurableSpaceX3] f) (hC : ∃ C, ∀ y, |f y| ≤ C) :
    ∀ᵐ x ∂(μ.restrict Z),
      MeasureTheory.condExp 𝔪.m (μ.restrict Z) f x =
        (∫ u in shape 𝔪.m U x, f (u • x) ∂(nuFull U μ D.Z D.m D.G x)) /
          ((nuFull U μ D.Z D.m D.G x) (shape 𝔪.m U x)).toReal := by
  classical
  have hZmeas : MeasurableSet Z := hplaq.1 Z hplaq.2.2.1
  have hcov : ∀ᵐ z ∂μ, ∀ k : ℕ, z ∈ D.G k (sel (D.G k) z) := by
    refine MeasureTheory.ae_all_iff.mpr fun k => ?_
    have h1 : ∀ᵐ z ∂μ, z ∈ ⋃ i, D.G k i := by
      have h := (MeasureTheory.measure_eq_zero_iff_ae_notMem (μ := μ)).mp (D.cover k)
      filter_upwards [h] with z hz
      simpa using hz
    filter_upwards [h1] with z hz
    exact cfree_sel_mem (Set.mem_iUnion.mp hz)
  have hpr : ∀ᵐ z ∂μ, ∀ (k i k' i' : ℕ), z ∈ D.Z k i → z ∈ D.Z k' i' →
      Work.EKLComp.ProporOn (ProbabilityTheory.condExpKernel (μ.restrict (D.Z k i)) (D.m k i) z)
        (ProbabilityTheory.condExpKernel (μ.restrict (D.Z k' i')) (D.m k' i') z)
        (atom (D.m k i) z ∩ atom (D.m k' i') z) := by
    refine MeasureTheory.ae_all_iff.mpr fun k => ?_
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    refine MeasureTheory.ae_all_iff.mpr fun k' => ?_
    refine MeasureTheory.ae_all_iff.mpr fun i' => ?_
    filter_upwards [hprop (D.Z k i) (D.Z k' i') ⟨D.m k i⟩ ⟨D.m k' i'⟩
      (D.isPlaque k i) (D.isPlaque k' i')] with z hz
    intro hzi hzi'
    exact hz ⟨hzi, hzi'⟩
  have hpk : ∀ᵐ z ∂μ, ∀ k : ℕ, (∃ i : ℕ, z ∈ D.G k i) →
      0 < refKernel μ (D.Z k) (D.m k) (D.G k) z (orbImg U z (V (1 / 2))) := by
    refine MeasureTheory.ae_all_iff.mpr fun k => ?_
    have hZk : ∀ i : ℕ, MeasurableSet (D.Z k i) := fun i =>
      (D.isPlaque k i).1 _ (D.isPlaque k i).2.2.1
    have hbad : μ (⋃ i, (D.Z k i ∩ {z : X3 | ¬ (0 < ProbabilityTheory.condExpKernel
        (μ.restrict (D.Z k i)) (D.m k i) z
        ((fun g : SL3 => g • z) '' (V (1 / 2) ∩ (U : Set SL3))))})) = 0 := by
      refine MeasureTheory.measure_iUnion_null fun i => ?_
      have hO : IsOpen (V (1 / 2)) :=
        (Work.EKLContract.Lemmas.V_open_one (1 / 2) (by norm_num)).1
      have h1O : (1 : SL3) ∈ V (1 / 2) :=
        (Work.EKLContract.Lemmas.V_open_one (1 / 2) (by norm_num)).2
      have hae := hpos (D.Z k i) ⟨D.m k i⟩ (D.isPlaque k i) (V (1 / 2)) hO h1O
      have hzero : (μ.restrict (D.Z k i)) {z : X3 | ¬ (0 < ProbabilityTheory.condExpKernel
          (μ.restrict (D.Z k i)) (D.m k i) z
          ((fun g : SL3 => g • z) '' (V (1 / 2) ∩ (U : Set SL3))))} = 0 := by
        simpa using (MeasureTheory.ae_iff.mp hae)
      rw [MeasureTheory.Measure.restrict_apply' (hZk i)] at hzero
      rw [Set.inter_comm]
      exact hzero
    have h1 : ∀ᵐ z ∂μ, z ∉ ⋃ i, (D.Z k i ∩ {z : X3 | ¬ (0 < ProbabilityTheory.condExpKernel
        (μ.restrict (D.Z k i)) (D.m k i) z
        ((fun g : SL3 => g • z) '' (V (1 / 2) ∩ (U : Set SL3))))}) :=
      (MeasureTheory.measure_eq_zero_iff_ae_notMem (μ := μ)).mp hbad
    filter_upwards [h1] with z hz hG
    obtain ⟨i, hi⟩ := hG
    have hi0 : z ∈ D.G k (sel (D.G k) z) := cfree_sel_mem ⟨i, hi⟩
    have hne : ¬ (¬ (0 < ProbabilityTheory.condExpKernel (μ.restrict (D.Z k (sel (D.G k) z)))
        (D.m k (sel (D.G k) z)) z
        ((fun g : SL3 => g • z) '' (V (1 / 2) ∩ (U : Set SL3))))) := by
      intro hcon
      exact hz (Set.mem_iUnion.mpr ⟨sel (D.G k) z, ⟨D.sub k _ hi0, hcon⟩⟩)
    have hfin : 0 < ProbabilityTheory.condExpKernel (μ.restrict (D.Z k (sel (D.G k) z)))
        (D.m k (sel (D.G k) z)) z
        ((fun g : SL3 => g • z) '' (V (1 / 2) ∩ (U : Set SL3))) := not_not.mp hne
    simpa only [refKernel, orbImg] using hfin
  have hpair : ∀ᵐ z ∂μ, ∀ (k i : ℕ), z ∈ D.Z k i → z ∈ Z →
      Work.EKLComp.ProporOn (ProbabilityTheory.condExpKernel (μ.restrict (D.Z k i)) (D.m k i) z)
        (ProbabilityTheory.condExpKernel (μ.restrict Z) 𝔪.m z)
        (atom (D.m k i) z ∩ atom 𝔪.m z) := by
    refine MeasureTheory.ae_all_iff.mpr fun k => ?_
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    filter_upwards [hprop (D.Z k i) Z ⟨D.m k i⟩ 𝔪 (D.isPlaque k i) hplaq] with z hz
    exact fun hzi hzZ => hz ⟨hzi, hzZ⟩
  have hgood : ∀ᵐ z ∂μ,
      Function.Injective (fun u : U => (u : SL3) • z) ∧
      (∀ k : ℕ, z ∈ D.G k (sel (D.G k) z)) ∧
      (∀ (k i k' i' : ℕ), z ∈ D.Z k i → z ∈ D.Z k' i' →
        Work.EKLComp.ProporOn (ProbabilityTheory.condExpKernel (μ.restrict (D.Z k i)) (D.m k i) z)
          (ProbabilityTheory.condExpKernel (μ.restrict (D.Z k' i')) (D.m k' i') z)
          (atom (D.m k i) z ∩ atom (D.m k' i') z)) ∧
      (∀ k : ℕ, (∃ i : ℕ, z ∈ D.G k i) →
        0 < refKernel μ (D.Z k) (D.m k) (D.G k) z (orbImg U z (V (1 / 2)))) := by
    filter_upwards [hfree, hcov, hpr, hpk] with z h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hatom : ∀ᵐ z ∂(μ.restrict Z),
      ProbabilityTheory.condExpKernel (μ.restrict Z) 𝔪.m z (atom 𝔪.m z) = 1 :=
    Work.EKLComp.condExpKernel_atom 𝔪 hplaq.1 hplaq.2.1 (μ.restrict Z)
  have hfint : MeasureTheory.Integrable f (μ.restrict Z) := by
    obtain ⟨C, hCb⟩ := hC
    refine MeasureTheory.Integrable.of_bound hf.aestronglyMeasurable C ?_
    filter_upwards with y
    rw [Real.norm_eq_abs]
    exact hCb y
  have hcex : ∀ᵐ z ∂(μ.restrict Z),
      MeasureTheory.condExp 𝔪.m (μ.restrict Z) f z
        = ∫ y, f y ∂(ProbabilityTheory.condExpKernel (μ.restrict Z) 𝔪.m z) :=
    ProbabilityTheory.condExp_ae_eq_integral_condExpKernel hplaq.1 hfint
  have hmemZ : ∀ᵐ z ∂(μ.restrict Z), z ∈ Z :=
    MeasureTheory.self_mem_ae_restrict hZmeas
  have hgoodR := MeasureTheory.ae_restrict_of_ae (s := Z) hgood
  have hpairR := MeasureTheory.ae_restrict_of_ae (s := Z) hpair
  filter_upwards [hgoodR, hpairR, hatom, hmemZ, hcex] with x hxG hxP hxA hxZ hxce
  obtain ⟨hinjx, hcoverx, hproporx, hposx⟩ := hxG
  obtain ⟨Csh, hCsh⟩ := (hplaq.2.2.2 x hxZ).2.2.2
  set N : ℕ := Nat.ceil Csh + 1 with hN
  have hshapeUcl : shape 𝔪.m U x ⊆ Ucl U (N : ℝ) := by
    intro u hu
    refine ⟨hu.1, fun i j => ?_⟩
    have h1 : |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ Csh := hCsh u hu i j
    have h2 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
      rw [Matrix.one_apply]; split <;> simp
    have h3 : |(u : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
        ≤ |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le ((u : Matrix (Fin 3) (Fin 3) ℝ) i j)
        (-(1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
    have h4 : Csh + 1 ≤ (N : ℝ) := by
      have hle := Nat.le_ceil Csh
      have hN' : (N : ℝ) = (Nat.ceil Csh : ℝ) + 1 := by rw [hN]; push_cast; ring
      linarith
    linarith
  set K : ℕ := N + 5 with hK
  have hKN : N + 5 ≤ K := le_of_eq hK.symm
  have hKcast : (K : ℝ) = (N : ℝ) + 5 := by rw [hK]; push_cast; ring
  have hshapeK : shape 𝔪.m U x ⊆ shape (D.m K (sel (D.G K) x)) U x := by
    refine Set.Subset.trans ?_ (D.shape_sub K (sel (D.G K) x) x (hcoverx K))
    have hVK : shape 𝔪.m U x ⊆ V ((K : ℝ) + 3) :=
      Set.Subset.trans hshapeUcl (Set.Subset.trans
        (cfree_Ucl_subset_V (U := U) (show (N : ℝ) < (N : ℝ) + 1 by linarith))
        (cfree_V_mono' (show (N : ℝ) + 1 ≤ (K : ℝ) + 3 by rw [hKcast]; linarith)))
    exact Set.subset_inter hVK (fun u hu => hu.1)
  have hatom_orb : atom 𝔪.m x = orbImg U x (shape 𝔪.m U x) := by
    refine Set.Subset.antisymm ?_ ?_
    · intro y hy
      obtain ⟨u, huU, rfl⟩ := (hplaq.2.2.2 x hxZ).2.1 hy
      exact ⟨u, ⟨⟨huU, hy⟩, huU⟩, rfl⟩
    · rintro y ⟨u, ⟨hu, -⟩, rfl⟩
      exact hu.2
  have hatomSub : atom 𝔪.m x ⊆ atom (D.m K (sel (D.G K) x)) x := by
    rw [hatom_orb]
    rintro y ⟨u, ⟨hu, huU⟩, rfl⟩
    exact (hshapeK hu).2
  have hprx : Work.EKLComp.ProporOn
      (ProbabilityTheory.condExpKernel (μ.restrict (D.Z K (sel (D.G K) x)))
        (D.m K (sel (D.G K) x)) x)
      (ProbabilityTheory.condExpKernel (μ.restrict Z) 𝔪.m x) (atom 𝔪.m x) := by
    have h := hxP K (sel (D.G K) x) (D.sub K _ (hcoverx K)) hxZ
    rwa [Set.inter_eq_right.mpr hatomSub] at h
  obtain ⟨lam, hlam0, hlamt, hlam⟩ := hprx
  have hkRestr : (refKernel μ (D.Z K) (D.m K) (D.G K) x).restrict (atom 𝔪.m x)
      = lam⁻¹ • (ProbabilityTheory.condExpKernel (μ.restrict Z) 𝔪.m x).restrict (atom 𝔪.m x) := by
    have h1 : refKernel μ (D.Z K) (D.m K) (D.G K) x
        = ProbabilityTheory.condExpKernel (μ.restrict (D.Z K (sel (D.G K) x)))
            (D.m K (sel (D.G K) x)) x := rfl
    rw [h1, hlam, smul_smul, ENNReal.inv_mul_cancel hlam0 hlamt, one_smul]
  have hatomMeas : MeasurableSet (atom 𝔪.m x) :=
    Work.EKLComp.measurableSet_atom_of_countablyGen 𝔪 hplaq.1 hplaq.2.1 x
  have hkA : refKernel μ (D.Z K) (D.m K) (D.G K) x (atom 𝔪.m x) = lam⁻¹ := by
    have h := congrArg (fun ν : Measure X3 => ν (atom 𝔪.m x)) hkRestr
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hatomMeas, Set.inter_self,
      Measure.restrict_apply hatomMeas, Set.inter_self, hxA, mul_one] at h
    exact h
  have hBoxsub : orbImg U x (V (1 / 2)) ⊆ orbImg U x (Box1 U) := by
    rw [cfree_orbImg_inter_U]
    exact orbImg_mono U x (cfree_V_half_inter_subset_Box1 U)
  have hane0 : refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x (Box1 U)) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (hposx K ⟨sel (D.G K) x, hcoverx K⟩) (measure_mono hBoxsub))
  have hanetop : refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x (Box1 U)) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (measure_mono (Set.subset_univ _)) ?_)
    have huniv : refKernel μ (D.Z K) (D.m K) (D.G K) x Set.univ = 1 := by
      have h1 : refKernel μ (D.Z K) (D.m K) (D.G K) x
          = ProbabilityTheory.condExpKernel (μ.restrict (D.Z K (sel (D.G K) x)))
              (D.m K (sel (D.G K) x)) x := rfl
      rw [h1, MeasureTheory.measure_univ]
    rw [huniv]; norm_num
  have hAshape : MeasurableSet (shape 𝔪.m U x) := by
    obtain ⟨O, hO, hOeq⟩ := (hplaq.2.2.2 x hxZ).2.2.1
    rw [hOeq]
    exact hO.measurableSet.inter hUcl.measurableSet
  haveI : MeasureTheory.IsFiniteMeasure (refKernel μ (D.Z K) (D.m K) (D.G K) x) := by
    have h1 : refKernel μ (D.Z K) (D.m K) (D.G K) x
        = ProbabilityTheory.condExpKernel (μ.restrict (D.Z K (sel (D.G K) x)))
            (D.m K (sel (D.G K) x)) x := rfl
    rw [h1]; infer_instance
  have hRes : (nuFull U μ D.Z D.m D.G x).restrict (shape 𝔪.m U x)
      = (refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x (Box1 U)))⁻¹
        • (pushOrbit U x (refKernel μ (D.Z K) (D.m K) (D.G K) x)).restrict (shape 𝔪.m U x) := by
    refine Measure.ext fun E hE => ?_
    rw [Measure.restrict_apply hE, Measure.smul_apply, Measure.restrict_apply hE, smul_eq_mul]
    have hEA : MeasurableSet (E ∩ shape 𝔪.m U x) := hE.inter hAshape
    have hEAU : E ∩ shape 𝔪.m U x ⊆ (U : Set SL3) := fun y hy => hy.2.1
    have hEAb : E ∩ shape 𝔪.m U x ⊆ Ucl U (N : ℝ) := fun y hy => hshapeUcl hy.2
    have hlev := cfree_nuFull_apply_bounded (U := U) hUcl (μ := μ) (D := D) (x := x)
      hinjx hcoverx hproporx hKN hEA hEAU hEAb
    have hpush : (pushOrbit U x (refKernel μ (D.Z K) (D.m K) (D.G K) x)) (E ∩ shape 𝔪.m U x)
        = refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x (E ∩ shape 𝔪.m U x)) :=
      pushOrbit_apply_of_injective hUcl hinjx _ hEA
    rw [hlev, hpush, mul_comm]
  have hInt1 : (∫ u in shape 𝔪.m U x, f (u • x) ∂(nuFull U μ D.Z D.m D.G x))
      = (refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x (Box1 U)))⁻¹.toReal
        * (∫ u in shape 𝔪.m U x, f (u • x)
            ∂(pushOrbit U x (refKernel μ (D.Z K) (D.m K) (D.G K) x))) := by
    rw [hRes, MeasureTheory.integral_smul_measure, smul_eq_mul]
  have hOrb : orbImg U x (shape 𝔪.m U x) = atom 𝔪.m x := hatom_orb.symm
  have hInt2 : (∫ u in shape 𝔪.m U x, f (u • x)
        ∂(pushOrbit U x (refKernel μ (D.Z K) (D.m K) (D.G K) x)))
      = ∫ y in atom 𝔪.m x, f y ∂(refKernel μ (D.Z K) (D.m K) (D.G K) x) := by
    rw [← hOrb]
    exact cfree_integral_pushOrbit_restrict hUcl hinjx hAshape hf hC
  have hRestrictKernel : (ProbabilityTheory.condExpKernel (μ.restrict Z) 𝔪.m x).restrict
        (atom 𝔪.m x)
      = ProbabilityTheory.condExpKernel (μ.restrict Z) 𝔪.m x := by
    rw [MeasureTheory.Measure.restrict_congr_set (show (atom 𝔪.m x)
      =ᵐ[ProbabilityTheory.condExpKernel (μ.restrict Z) 𝔪.m x] Set.univ from ?_),
      MeasureTheory.Measure.restrict_univ]
    rw [MeasureTheory.ae_eq_set]
    constructor
    · rw [show (atom 𝔪.m x \ Set.univ) = (∅ : Set X3) from Set.sdiff_univ _, measure_empty]
    · rw [show (Set.univ \ atom 𝔪.m x) = (atom 𝔪.m x)ᶜ from (Set.compl_eq_univ_sdiff _).symm,
        MeasureTheory.measure_compl hatomMeas (by rw [hxA]; exact ENNReal.one_ne_top), hxA,
        MeasureTheory.measure_univ, tsub_self]
  have hInt3 : (∫ y in atom 𝔪.m x, f y ∂(refKernel μ (D.Z K) (D.m K) (D.G K) x))
      = lam⁻¹.toReal
        * ∫ y, f y ∂(ProbabilityTheory.condExpKernel (μ.restrict Z) 𝔪.m x) := by
    rw [show (∫ y in atom 𝔪.m x, f y ∂(refKernel μ (D.Z K) (D.m K) (D.G K) x))
        = ∫ y, f y ∂((refKernel μ (D.Z K) (D.m K) (D.G K) x).restrict (atom 𝔪.m x)) from rfl,
      hkRestr, MeasureTheory.integral_smul_measure, smul_eq_mul, hRestrictKernel]
  have hnuA : nuFull U μ D.Z D.m D.G x (shape 𝔪.m U x)
      = (refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x (Box1 U)))⁻¹ * lam⁻¹ := by
    have hlev := cfree_nuFull_apply_bounded (U := U) hUcl (μ := μ) (D := D) (x := x)
      hinjx hcoverx hproporx hKN hAshape (fun y hy => hy.1) hshapeUcl
    rw [hlev, hOrb, hkA, mul_comm]
  rw [hxce, hInt1, hInt2, hInt3, hnuA, ENNReal.toReal_mul]
  have ha0 : (refKernel μ (D.Z K) (D.m K) (D.G K) x (orbImg U x (Box1 U)))⁻¹.toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨ENNReal.inv_ne_zero.mpr hanetop, ENNReal.inv_ne_top.mpr hane0⟩
  have hb0 : lam⁻¹.toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨ENNReal.inv_ne_zero.mpr hlamt, ENNReal.inv_ne_top.mpr hlam0⟩
  rw [eq_div_iff (mul_ne_zero ha0 hb0)]
  ring

theorem condexp_field_free (U : Subgroup Work.EKLContract.SL3)
    (hUcl : IsClosed (U : Set Work.EKLContract.SL3))
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    (D : Work.EKLRelCross.FlowerData U μ)
    (hprop : Work.EKLRelCross.ProporPiece U μ)
    (hpos : Work.EKLRelCross.PosPiece U μ)
    (hfree : ∀ᵐ x ∂μ, Function.Injective (fun u : U => (u : Work.EKLContract.SL3) • x)) :
    Work.EKLRelCross.CondExpField U μ D.Z D.m D.G := by
  intro Z m hplaq f hf hC
  exact cfree_pointwise U hUcl D hprop hpos hfree Z ⟨m⟩ hplaq f hf hC

end Work.EKLRelCross
