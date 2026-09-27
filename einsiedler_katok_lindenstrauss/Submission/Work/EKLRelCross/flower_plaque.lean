import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.flower_balls
import Submission.Work.EKLRelCross.flower
import Submission.Work.EKLRelCross.flowerSet_borel
import Submission.Work.EKLRelCross.atom_flower_local
import Submission.Work.EKLRelCross.flower_plaqueAlgebra_bdd
import Submission.Work.EKLRelCross.CrossSectionSetup
import Submission.Work.EKLRelCross.exists_shrink_nhds
import Submission.Work.EKLRelCross.freeSet_borel
import Submission.Work.EKLRelCross.FlowerLocalAux.inj_nhds_local
import Submission.Work.EKLProd.inv_entries_bound

/-!
# `Work.EKLRelCross.flower_plaque` — the local flower (Pisa 6.7–6.15)

For a horospherical subgroup `U ≤ SL₃(ℝ)`, a point `x₀` with free `U`-orbit and `R > 0` there are
`Z, m, G, O` with `O` open containing `x₀`, `G` Borel with `G ⊆ Z`, `(Z, m)` a plaque algebra,
`x₀ ∈ G`, `O ∩ {U-free points} ⊆ G`, and `V R ∩ U ⊆ shape m U x` for every `x ∈ G`.

The construction combines the workspace's Pisa 6.7/6.8 lemmas (`exists_shrink_nhds`,
`FlowerLocalAux.inj_nhds_local`), the abstract cross-section (`exists_borel_crossSection`), the
flower σ-algebra (`flower`, `atom_flower_local`, `flowerSet_borel`) and the free locus
(`freeSet_borel`).  The plaque algebra statement `flower_plaqueAlgebra_bdd` is applied to the
free part of the cross-section at the shrink scale, so that only free points enter `Z`; the shape
at `x = v • z` is then `{u ∈ U | u * v ∈ V δ}`, which contains `V R ∩ U` for every point of the
base `O ∩ free` because the cross-section parameter `v` is bounded by the collar constant.
-/

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-! ## Ball arithmetic for the open balls `V` -/

lemma flp_V_mono {a b : ℝ} (h : a ≤ b) : (V a : Set SL3) ⊆ V b :=
  fun _ hg i j => lt_of_lt_of_le (hg i j) h

lemma flp_V_mul_V {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (V a : Set SL3) * V b ⊆ V (a + b + 3 * a * b) := by
  rintro _ ⟨A, hA, B, hB, rfl⟩
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact entries_mul_sub_one_le i j hA hB ha hb

lemma flp_Ucl_mono {U : Subgroup SL3} {a b : ℝ} (h : a ≤ b) : (Ucl U a : Set SL3) ⊆ Ucl U b :=
  fun _ hg => ⟨hg.1, fun i j => le_trans (hg.2 i j) h⟩

lemma flp_Ucl_mul_mem {U : Subgroup SL3} {a b c : ℝ}
    (hab : 3 * (a + 1) * (b + 1) + (a + 1) + (b + 1) ≤ c)
    {g h : SL3} (hg : g ∈ Ucl U a) (hh : h ∈ Ucl U b) : g * h ∈ Ucl U c := by
  refine ⟨U.mul_mem hg.1 hh.1, fun i j => ?_⟩
  have hA : ∀ k l, |((g : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < a + 1 := by
    intro k l
    have h := hg.2 k l
    rw [abs_le] at h; rw [abs_lt]; constructor <;> linarith [h.1, h.2]
  have hB : ∀ k l, |((h : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l
      - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < b + 1 := by
    intro k l
    have h := hh.2 k l
    rw [abs_le] at h; rw [abs_lt]; constructor <;> linarith [h.1, h.2]
  have hA0 : 0 ≤ a + 1 := le_of_lt (lt_of_le_of_lt (abs_nonneg _) (hA 0 0))
  have hB0 : 0 ≤ b + 1 := le_of_lt (lt_of_le_of_lt (abs_nonneg _) (hB 0 0))
  have hmain := entries_mul_sub_one_le (A := ((g : SL3) : Matrix (Fin 3) (Fin 3) ℝ))
    (B := ((h : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j hA hB hA0 hB0
  rw [Matrix.SpecialLinearGroup.coe_mul]
  linarith

lemma flp_abs_one_entry (i j : Fin 3) : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
  rw [Matrix.one_apply]; split_ifs <;> simp

/-- Entries of the inverse of an element of `V δ` are bounded. -/
lemma flp_inv_V_entry {δ : ℝ} (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : SL3, g ∈ V δ → ∀ i j, |(g⁻¹) i j| ≤ C := by
  obtain ⟨C, hC⟩ := Work.EKLProd.inv_entries_bound δ hδ
  exact ⟨max C 0, le_max_right _ _, fun g hg i j => le_trans (hC g hg i j) (le_max_left _ _)⟩

/-- The two product bounds for the flower: `(V δ)⁻¹ · V δ ⊆ V b` and `(V δ)⁻¹`-products. -/
lemma flp_V_inv_mul {δ : ℝ} (hδ : 0 < δ) :
    ∃ b : ℝ, 0 < b ∧ (∀ a : SL3, a ∈ V δ → ∀ c : SL3, c ∈ V δ → a⁻¹ * c ∈ V b) ∧
      (∀ a : SL3, a⁻¹ ∈ V δ → ∀ c : SL3, c ∈ V δ → a * c ∈ V b) := by
  obtain ⟨C, hC0, hC⟩ := flp_inv_V_entry hδ
  have hC2 : (0:ℝ) < C + 2 := by linarith
  refine ⟨(C + 2) + δ + 3 * (C + 2) * δ + 1, by positivity, ?_, ?_⟩
  · intro a ha c hc i j
    have h1 : ∀ k l, |((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < C + 2 := by
      intro k l
      have h := hC a ha k l
      rw [abs_le] at h; rw [abs_lt]
      constructor <;> linarith [h.1, h.2, abs_le.mp (flp_abs_one_entry k l)]
    have h3 : ∀ k l, |((c : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < δ := fun k l => hc k l
    have hmain := entries_mul_sub_one_le (A := ((a⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ))
      (B := ((c : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j h1 h3 (le_of_lt hC2) (le_of_lt hδ)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    linarith
  · intro a ha c hc i j
    have h1 : ∀ k l, |((a : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < C + 2 := by
      intro k l
      have h : |(((a⁻¹)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ C := hC a⁻¹ ha k l
      rw [inv_inv] at h
      rw [abs_le] at h; rw [abs_lt]
      constructor <;> linarith [h.1, h.2, abs_le.mp (flp_abs_one_entry k l)]
    have h3 : ∀ k l, |((c : SL3) : Matrix (Fin 3) (Fin 3) ℝ) k l
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| < δ := fun k l => hc k l
    have hmain := entries_mul_sub_one_le (A := ((a : SL3) : Matrix (Fin 3) (Fin 3) ℝ))
      (B := ((c : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j h1 h3 (le_of_lt hC2) (le_of_lt hδ)
    rw [Matrix.SpecialLinearGroup.coe_mul]
    linarith

/-! ## The shape of the flower at a plaque point -/

theorem flp_shape {U : Subgroup SL3} {C : Set X3} {b δ : ℝ}
    (hCS : ∀ z ∈ C, ∀ u ∈ U, u ∈ V b → u • z ∈ C → u = 1) (hδ : 0 < δ)
    (hprod : ∀ w ∈ U, w ∈ Vinv δ → ∀ u ∈ U, u ∈ V δ → w * u ∈ V b)
    {W : ℕ → Set X3} (hW0 : W 0 = Set.univ)
    (hsep : ∀ z ∈ C, ∀ z' ∈ C, (∀ n, z ∈ W n ↔ z' ∈ W n) → z = z')
    {v : SL3} (hv : v ∈ V δ) (hvU : v ∈ U) {z : X3} (hz : z ∈ C)
    (hzfree : ∀ u ∈ U, u • z = z → u = 1) {x : X3} (hx : x = v • z) :
    shape (flowerSigma U δ C W) U x = {u : SL3 | u ∈ U ∧ u * v ∈ V δ} := by
  subst hx
  have hatom : atom (flowerSigma U δ C W) (v • z)
      = (fun u : SL3 => u • z) '' (V δ ∩ (U : Set SL3)) :=
    atom_flower_local hCS hδ hprod hW0 hsep hv hvU hz rfl
  rw [shape, hatom]
  ext u
  constructor
  · rintro ⟨huU, hu⟩
    obtain ⟨w', ⟨hw'V, hw'U⟩, hw'eq⟩ := hu
    have hfix : (w'⁻¹ * (u * v)) • z = z := by
      rw [mul_smul, mul_smul, ← hw'eq, inv_smul_smul]
    have hUmem : w'⁻¹ * (u * v) ∈ U := U.mul_mem (U.inv_mem hw'U) (U.mul_mem huU hvU)
    have hone : w'⁻¹ * (u * v) = 1 := hzfree _ hUmem hfix
    have hone' : u * v = w' := (inv_mul_eq_one.mp hone).symm
    exact ⟨huU, by rw [hone']; exact hw'V⟩
  · rintro ⟨huU, huv⟩
    exact ⟨huU, ⟨u * v, ⟨huv, U.mul_mem huU hvU⟩, mul_smul u v z⟩⟩

/-! ## The local flower -/

theorem flower_local_exists (h2 : Work.EKLContract.P_X3) {U : Subgroup SL3}
    (hU : Work.EKLContract.IsHoro U) (x0 : X3)
    (hfree : ∀ u₁ ∈ U, ∀ u₂ ∈ U, u₁ • x0 = u₂ • x0 → u₁ = u₂)
    (R : ℝ) (hR : 0 < R) :
    ∃ (Z : Set X3) (m : MeasurableSpace X3) (G O : Set X3),
      IsOpen O ∧ x0 ∈ O ∧ @MeasurableSet X3 instMeasurableSpaceX3 G ∧ G ⊆ Z ∧
      IsPlaqueAlgebra U Z m ∧ x0 ∈ G ∧
      O ∩ {x | ∀ u ∈ U, u • x = x → u = 1} ⊆ G ∧
      ∀ x ∈ G, V R ∩ (U : Set SL3) ⊆ shape m U x := by
  classical
  have hUcl : IsClosed (U : Set SL3) := hU.1
  -- (0) the collar bound for `Ucl U 2 ⊆ V 3`
  obtain ⟨C₂, hC₂pos, hC₂⟩ : ∃ C : ℝ, 0 < C ∧ ∀ g : SL3, g ∈ Ucl U 2 → ∀ i j, |(g⁻¹) i j| ≤ C := by
    obtain ⟨C, hC⟩ := Work.EKLProd.inv_entries_bound 3 (by norm_num)
    have hC1 : (0:ℝ) < C + 1 := by
      have h := hC (1 : SL3) ((Work.EKLContract.Lemmas.V_open_one 3 (by norm_num)).2) 0 0
      rw [inv_one] at h
      have h2 : |((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) 0 0| = 1 := by
        rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]; simp
      rw [h2] at h
      linarith
    refine ⟨C + 1, hC1, fun g hg i j => ?_⟩
    have hg3 : g ∈ V 3 := fun i j => by
      have h := abs_le.mp (hg.2 i j)
      exact abs_lt.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
    linarith [hC g hg3 i j]
  let S : ℝ := C₂ + 2
  have hSpos : 0 < S := by simp only [S]; linarith
  let δ : ℝ := R + S + 3 * R * S + 1
  have hδ : 0 < δ := by simp only [δ]; positivity
  have hRSδ : R + S + 3 * R * S < δ := by simp only [δ]; linarith
  obtain ⟨Bv, hBvpos, hBv1, hBv2⟩ := flp_V_inv_mul hδ
  let R₀ : ℝ := Bv + 10 * C₂ + 100
  have hR₀pos : 0 < R₀ := by simp only [R₀]; linarith [hBvpos, hC₂pos]
  have hBvle : Bv ≤ R₀ := by simp only [R₀]; linarith [hC₂pos]
  have h10C₂le : 10 * C₂ + 40 ≤ R₀ := by simp only [R₀]; linarith [hBvpos, hC₂pos]
  have h40le : (40:ℝ) ≤ R₀ := by simp only [R₀]; linarith [hBvpos, hC₂pos]
  have hC₂2le : C₂ + 2 ≤ R₀ := by simp only [R₀]; linarith [hBvpos, hC₂pos]
  -- (1) the compact neighbourhoods
  obtain ⟨E₁, hE₁c, hE₁int, hE₁⟩ := exists_shrink_nhds hUcl x0 hfree (R := R₀) (le_of_lt hR₀pos)
  obtain ⟨E₂, hE₂c, hE₂int, hE₂⟩ := FlowerLocalAux.inj_nhds_local hUcl x0 hfree (R := 2)
  let E : Set X3 := E₁ ∩ E₂
  have hEc : IsCompact E := hE₁c.inter hE₂c
  have hEint : x0 ∈ interior E := by
    rw [show interior E = interior E₁ ∩ interior E₂ from interior_inter]
    exact ⟨hE₁int, hE₂int⟩
  -- (2) the cross-section
  haveI : Nonempty X3 := ⟨x0⟩
  letI : MetricSpace X3 := TopologicalSpace.metrizableSpaceMetric X3
  have h1U2 : (1 : SL3) ∈ Ucl U 2 := by
    refine ⟨U.one_mem, fun i j => ?_⟩
    rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply]
    split_ifs <;> norm_num
  have h2R₀ : (2:ℝ) ≤ R₀ := by linarith [h40le]
  have hInva : ∀ g : SL3, g ∈ Ucl U 2 → g⁻¹ ∈ Ucl U (C₂ + 1) := by
    intro g hg
    refine ⟨U.inv_mem hg.1, fun i j => ?_⟩
    have h := abs_le.mp (hC₂ g hg i j)
    have h2 := abs_le.mp (flp_abs_one_entry i j)
    rw [abs_le]
    constructor <;> linarith [h.1, h.2, h2.1, h2.2]
  obtain ⟨C, hCsub, hCmeas, hcross⟩ :=
    exists_borel_crossSection (B := Ucl U 2) (A := Ucl U R₀) (E := E)
      hEc (TopologicalSpace.denseSeq X3) (TopologicalSpace.denseRange_denseSeq X3)
      (isCompact_Ucl hUcl 2) (isCompact_Ucl hUcl R₀) h1U2
      (fun g hg => flp_Ucl_mono h2R₀ hg)
      (fun g hg => flp_Ucl_mono (by linarith [hC₂pos]) (hInva g hg))
      (fun g hg g' hg' => flp_Ucl_mul_mem (by linarith [h40le]) hg hg')
      (fun g hg g' hg' => flp_Ucl_mul_mem (by linarith [h10C₂le]) hg (hInva g' hg'))
      (fun x hx x' hx' u hu u' hu' heq => by
        have h := hE₁ x hx.1 x' hx'.1 u hu u' hu' heq
        exact ⟨flp_Ucl_mono (by norm_num) h.1, flp_Ucl_mono (by norm_num) h.2⟩)
      (fun x hx u hu u' hu' heq => hE₂ x hx.2 u hu u' hu' heq)
  -- (3) the cross-section property at scale `R₀`
  have hCS_A : ∀ z ∈ C, ∀ u ∈ U, u ∈ Ucl U R₀ → u • z ∈ C → u = 1 := by
    intro z hzC u huU huA huzC
    have huzE : u • z ∈ E := hCsub huzC
    have hzE : z ∈ E := hCsub hzC
    have h1A : (1 : SL3) ∈ Ucl U R₀ := by
      refine ⟨U.one_mem, fun i j => ?_⟩
      have h1 : ((1 : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
          = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := rfl
      rw [h1, sub_self, abs_zero]
      exact le_of_lt hR₀pos
    have hsh := hE₁ (u • z) huzE.1 z hzE.1 1 h1A u huA (by rw [one_smul])
    have hu1 : u ∈ Ucl U 1 := by simpa using hsh.1
    obtain ⟨w, hw, huniq⟩ := hcross z hzE
    refine (huniq u ⟨flp_Ucl_mono (by norm_num) hu1, huzC⟩).trans ?_
    exact ((huniq 1 ⟨flp_Ucl_mono (by norm_num) h1U2, by rw [one_smul]; exact hzC⟩)).symm
  -- (4) a countable basis of open sets separating the points of `C`
  obtain ⟨basis, hbas⟩ := TopologicalSpace.exists_seq_basis X3
  let W : ℕ → Set X3 := fun n => match n with | 0 => Set.univ | (k + 1) => basis k
  have hW0 : W 0 = Set.univ := rfl
  have hWopen : ∀ n, IsOpen (W n) := by
    intro n
    match n with
    | 0 => exact isOpen_univ
    | (k + 1) => exact hbas.isOpen (Set.mem_range_self k)
  have hWgen : borel X3 = MeasurableSpace.generateFrom (Set.range W) := by
    rw [hbas.borel_eq_generateFrom]
    apply le_antisymm
    · exact MeasurableSpace.generateFrom_mono (by rintro s ⟨k, rfl⟩; exact ⟨k + 1, rfl⟩)
    · refine MeasurableSpace.generateFrom_le ?_
      intro s hs
      rcases hs with ⟨n, rfl⟩
      match n with
      | 0 => exact MeasurableSet.univ
      | (k + 1) => exact MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self k)
  have hsep : ∀ z ∈ C, ∀ z' ∈ C, (∀ n, z ∈ W n ↔ z' ∈ W n) → z = z' := by
    intro z hz z' hz' hpat
    by_contra hne
    have hopen : IsOpen (({z'} : Set X3))ᶜ := isClosed_singleton.isOpen_compl
    have hzmem : z ∈ (({z'} : Set X3))ᶜ := hne
    obtain ⟨t, htmem, hzt, htsub⟩ := hbas.exists_subset_of_mem_open hzmem hopen
    obtain ⟨k, rfl⟩ := htmem
    have hz'not : z' ∉ basis k := fun h => htsub h (Set.mem_singleton z')
    exact hz'not ((hpat (k + 1)).mp hzt)
  -- (5) the scaled cross-section properties used by the flower construction
  have hCSV : ∀ z ∈ C, ∀ u ∈ U, u ∈ V R₀ → u • z ∈ C → u = 1 :=
    fun z hz u huU huV huzC =>
      hCS_A z hz u huU ⟨huU, fun i j => le_of_lt (huV i j)⟩ huzC
  have hprodV : ∀ w ∈ U, w ∈ Vinv δ → ∀ u ∈ U, u ∈ V δ → w * u ∈ V R₀ :=
    fun w _ hwVinv u _ huV => flp_V_mono hBvle (hBv2 w (mem_Vinv_iff.mp hwVinv) u huV)
  have hprod2V : ∀ a ∈ U, a ∈ V δ → ∀ c ∈ U, c ∈ V δ → a⁻¹ * c ∈ V R₀ :=
    fun a _ haV c _ hcV => flp_V_mono hBvle (hBv1 a haV c hcV)
  -- (6) the plaque algebra formed by the free points of the cross-section
  have hpa : IsPlaqueAlgebra U
      (⋃ c ∈ C ∩ {x : X3 | ∀ u ∈ U, u • x = x → u = 1}, atom (flowerSigma U δ C W) c)
      (flowerSigma U δ C W) :=
    flower_plaqueAlgebra_bdd h2 hUcl hCmeas (b := R₀) hCSV (δ := δ) hδ hprodV hprod2V
      hW0 hWopen hWgen hsep
  -- (7) the free locus
  have hFmeas : MeasurableSet {x : X3 | ∀ u ∈ U, u • x = x → u = 1} := freeSet_borel hUcl
  refine ⟨_, _, interior E ∩ {x : X3 | ∀ u ∈ U, u • x = x → u = 1}, interior E, isOpen_interior,
    hEint, ?_, ?_, hpa, ?_, ?_, ?_⟩
  · exact isOpen_interior.measurableSet.inter hFmeas
  · -- the base is contained in the plaque algebra
    rintro x ⟨hxO, hxfree⟩
    have hxE : x ∈ E := interior_subset hxO
    obtain ⟨t, ⟨ht2, htxC⟩, htuniq⟩ := hcross x hxE
    set z : X3 := t • x with hzdef
    have hzC : z ∈ C := htxC
    have hzfree : ∀ u ∈ U, u • z = z → u = 1 := by
      intro u huU huz
      have hfix : (t⁻¹ * u * t) • x = x := by
        rw [mul_smul, mul_smul, ← hzdef, huz, hzdef, inv_smul_smul]
      have hmemU : t⁻¹ * u * t ∈ U := U.mul_mem (U.mul_mem (U.inv_mem ht2.1) huU) ht2.1
      have h1 : t⁻¹ * u * t = 1 := hxfree _ hmemU hfix
      calc u = t * (t⁻¹ * u * t) * t⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have htinvV : t⁻¹ ∈ V δ := by
      intro i j
      have h := abs_le.mp (hC₂ t ht2 i j)
      have h2 := abs_le.mp (flp_abs_one_entry i j)
      have h3 : |(t⁻¹) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C₂ + 1 := by
        rw [abs_le]; constructor <;> linarith [h.1, h.2, h2.1, h2.2]
      have h4 : C₂ + 1 < δ := by
        have hRSnn : 0 ≤ R * S := mul_nonneg (le_of_lt hR) (le_of_lt hSpos)
        simp only [δ, S] at *
        nlinarith [hRSnn, hC₂pos]
      linarith [h3, h4]
    have hatomz : atom (flowerSigma U δ C W) z
        = (fun u : SL3 => u • z) '' (V δ ∩ (U : Set SL3)) :=
      atom_flower_local hCSV hδ hprodV hW0 hsep (v := (1 : SL3))
        ((Work.EKLContract.Lemmas.V_open_one δ hδ).2) U.one_mem hzC (by rw [one_smul])
    refine Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨⟨hzC, hzfree⟩, ?_⟩⟩
    rw [hatomz]
    exact ⟨t⁻¹, ⟨htinvV, U.inv_mem ht2.1⟩, by
      show t⁻¹ • z = x
      rw [hzdef, ← mul_smul, inv_mul_cancel, one_smul]⟩
  · -- `x₀` lies in the base
    exact ⟨hEint, fun u huU hu => hfree u huU 1 U.one_mem (by rw [hu, one_smul])⟩
  · -- the base is the trace of the open set on the free locus
    intro x hx
    exact hx
  · -- the shape contains the `R`-plaque at every point of the base
    intro x ⟨hxO, hxfree⟩
    have hxE : x ∈ E := interior_subset hxO
    obtain ⟨t, ⟨ht2, htxC⟩, htuniq⟩ := hcross x hxE
    set z : X3 := t • x with hzdef
    have hzC : z ∈ C := htxC
    have hzfree : ∀ u ∈ U, u • z = z → u = 1 := by
      intro u huU huz
      have hfix : (t⁻¹ * u * t) • x = x := by
        rw [mul_smul, mul_smul, ← hzdef, huz, hzdef, inv_smul_smul]
      have hmemU : t⁻¹ * u * t ∈ U := U.mul_mem (U.mul_mem (U.inv_mem ht2.1) huU) ht2.1
      have h1 : t⁻¹ * u * t = 1 := hxfree _ hmemU hfix
      calc u = t * (t⁻¹ * u * t) * t⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have htinvV : t⁻¹ ∈ V δ := by
      intro i j
      have h := abs_le.mp (hC₂ t ht2 i j)
      have h2 := abs_le.mp (flp_abs_one_entry i j)
      have h3 : |(t⁻¹) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C₂ + 1 := by
        rw [abs_le]; constructor <;> linarith [h.1, h.2, h2.1, h2.2]
      have h4 : C₂ + 1 < δ := by
        have hRSnn : 0 ≤ R * S := mul_nonneg (le_of_lt hR) (le_of_lt hSpos)
        simp only [δ, S] at *
        nlinarith [hRSnn, hC₂pos]
      linarith [h3, h4]
    have htinvS : t⁻¹ ∈ V S := by
      intro i j
      have h := abs_le.mp (hC₂ t ht2 i j)
      have h2 := abs_le.mp (flp_abs_one_entry i j)
      have h3 : |(t⁻¹) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C₂ + 1 := by
        rw [abs_le]; constructor <;> linarith [h.1, h.2, h2.1, h2.2]
      simp only [S] at h3 ⊢; linarith
    have hxeq : x = t⁻¹ • z := by rw [hzdef, ← mul_smul, inv_mul_cancel, one_smul]
    have hshape := flp_shape (U := U) (C := C) (W := W) (b := R₀) (δ := δ) hCSV hδ hprodV
      hW0 hsep htinvV (U.inv_mem ht2.1) hzC hzfree hxeq
    rw [hshape]
    rintro u ⟨huV, huU⟩
    refine ⟨huU, ?_⟩
    exact flp_V_mono hRSδ.le
      (flp_V_mul_V (le_of_lt hR) (le_of_lt hSpos) ⟨u, huV, t⁻¹, htinvS, rfl⟩)

end Work.EKLRelCross
