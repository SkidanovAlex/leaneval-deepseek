import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.flower
import Submission.Work.EKLRelCross.atom_flower
import Submission.Work.EKLRelCross.meas_free_atoms
import Submission.Work.EKLRelCross.shape_plaque_bdd
import Submission.Work.EKLProd.inv_entries_bound
import Submission.Work.EKLProd.plaque_shape_mass
import Submission.Work.EKLComp.X3Background

set_option linter.unusedVariables false
set_option maxHeartbeats 800000

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-! ## 1. Arithmetic of the closed displacement balls `Ucl`

`Ucl U r = {g ∈ U | ∀ i j, |g i j - 1 i j| ≤ r}` is the closed entrywise ball of radius `r`
(`Submission/Work/EKLRelCross/LeafBasic.lean`).  We need two facts:

* `Ucl U a * Ucl U b ⊆ Ucl U (a + b + 3ab)` (multiplicativity, with the factor `3 = card (Fin 3)`);
* for `g ∈ V a ∩ U` we have `g⁻¹ ∈ Ucl U (2 (1+a)² + 1)` (the entries of `g⁻¹` are the `2 × 2`
  minors of `g`, bounded by `2 (1+a)²`, plus `1` on the diagonal),

and the consequence that `((V δ)⁻¹ ∩ U) · (V δ ∩ U) ⊆ Ucl U ρ` whenever
`2 (1+δ)² + 1 + δ + 3 (2 (1+δ)² + 1) δ ≤ ρ` — this is what makes the *bounded* cross-section
property (`hCS`, formulated with the closed ball `Ucl U ρ`) available for the products that occur
in the uniqueness argument for the base point of the collar.
-/

/-- The crude norm constant for the inverse of an element of `V a`: `2 (1+a)² + 1`. -/
def fbLam (a : ℝ) : ℝ := 2 * (1 + a) ^ 2 + 1

lemma fbLam_pos (a : ℝ) : 0 < fbLam a := by
  have : (0 : ℝ) ≤ 2 * (1 + a) ^ 2 := by positivity
  simp only [fbLam]; linarith

lemma fb_Ucl_mono {U : Subgroup SL3} {a b : ℝ} (h : a ≤ b) : Ucl U a ⊆ Ucl U b :=
  fun _ hg => ⟨hg.1, fun i j => le_trans (hg.2 i j) h⟩

/-- An element of `Ucl U a` is entrywise within `b` of the identity, for `a < b`. -/
lemma fb_Ucl_subset_V {U : Subgroup SL3} {a b : ℝ} (h : a < b) : Ucl U a ⊆ V b :=
  fun _ hg i j => lt_of_le_of_lt (hg.2 i j) h

/-- **Multiplicativity of the closed balls**: `Ucl U a * Ucl U b ⊆ Ucl U (a + b + 3 a b)`. -/
lemma fb_mul_mem_Ucl {U : Subgroup SL3} {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {x y : SL3}
    (hx : x ∈ Ucl U a) (hy : y ∈ Ucl U b) : x * y ∈ Ucl U (a + b + 3 * a * b) := by
  refine ⟨U.mul_mem hx.1 hy.1, fun i j => ?_⟩
  have hx' : ∀ k l, |(x : Matrix (Fin 3) (Fin 3) ℝ) k l - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ a :=
    fun k l => hx.2 k l
  have hy' : ∀ k l, |(y : Matrix (Fin 3) (Fin 3) ℝ) k l - (1 : Matrix (Fin 3) (Fin 3) ℝ) k l| ≤ b :=
    fun k l => hy.2 k l
  have hid : ((x * y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1
      = ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)
        + ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) + ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]; noncomm_ring
  have hA : |((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| ≤ a := hx' i j
  have hB : |((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| ≤ b := hy' i j
  have hprod : |(((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j|
      ≤ 3 * (a * b) := by
    rw [Matrix.mul_apply]
    calc |∑ k : Fin 3, ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i k * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) k j|
        ≤ ∑ k : Fin 3, |((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i k
            * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) k j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin 3, |((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i k|
            * |((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) k j| := by simp [abs_mul]
      _ ≤ ∑ _k : Fin 3, a * b :=
          Finset.sum_le_sum (fun k _ => mul_le_mul (hx' i k) (hy' k j) (abs_nonneg _) ha)
      _ = 3 * (a * b) := by simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  have hsum : |(((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j
        + ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| ≤ 3 * (a * b) + a := by
    have h := abs_add_le ((((x : Matrix (Fin 3) (Fin 3) ℝ) - 1)
      * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j) (((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j)
    linarith
  have hmain : |(((x * y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| ≤ 3 * (a * b) + a + b := by
    rw [hid, Matrix.add_apply, Matrix.add_apply]
    calc |((((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j
            + ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j + ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j)|
        ≤ |(((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) * ((y : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j
            + ((x : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j|
          + |((y : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j| := abs_add_le _ _
      _ ≤ (3 * (a * b) + a) + b := add_le_add hsum hB
      _ = 3 * (a * b) + a + b := by ring
  rw [show ((x * y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      = (((x * y : SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1) i j from rfl]
  linarith

/-- **The inverse of a small displacement is a bounded displacement**: for `g ∈ V a ∩ U` we have
`g⁻¹ ∈ Ucl U (2 (1+a)² + 1)`. -/
lemma fb_inv_mem_Ucl {U : Subgroup SL3} {a : ℝ} (ha : 0 < a) {g : SL3} (hg : g ∈ V a)
    (hgU : g ∈ U) : g⁻¹ ∈ Ucl U (fbLam a) := by
  refine ⟨U.inv_mem hgU, fun i j => ?_⟩
  have hcoe : ((g⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) = (g : Matrix (Fin 3) (Fin 3) ℝ).adjugate :=
    Matrix.SpecialLinearGroup.coe_inv g
  rw [hcoe, Matrix.one_apply]
  have hb : |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i j| ≤ 2 * (1 + a) ^ 2 :=
    Work.EKLProd.abs_adjugate_entry_le (by linarith)
      (fun p q => Work.EKLProd.mem_V_entries_le hg p q) i j
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    calc |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i i - 1|
        ≤ |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i i| + |(1 : ℝ)| := abs_sub _ _
      _ = |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i i| + 1 := by rw [abs_one]
      _ ≤ 2 * (1 + a) ^ 2 + 1 := by linarith
      _ = fbLam a := by simp only [fbLam]
  · rw [if_neg hij]
    calc |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i j - 0|
        = |(g : Matrix (Fin 3) (Fin 3) ℝ).adjugate i j| := by rw [sub_zero]
      _ ≤ 2 * (1 + a) ^ 2 := hb
      _ ≤ 2 * (1 + a) ^ 2 + 1 := by linarith
      _ = fbLam a := by simp only [fbLam]

/-- **The products that occur in the collar lie in a bounded ball**: if `w ∈ (V δ)⁻¹ ∩ U` and
`u ∈ V δ ∩ U`, then `w * u ∈ Ucl U ρ` as soon as `ρ ≥ 2 (1+δ)² + 1 + δ + 3 (2 (1+δ)² + 1) δ`. -/
lemma fb_Vinv_mul_V_mem_Ucl {U : Subgroup SL3} {δ ρ : ℝ} (hδ : 0 < δ)
    (hΛ : fbLam δ + δ + 3 * fbLam δ * δ ≤ ρ) {w u : SL3}
    (hw : w ∈ Vinv δ ∩ (U : Set SL3)) (hu : u ∈ V δ ∩ (U : Set SL3)) :
    w * u ∈ Ucl U ρ := by
  have hwUcl : w ∈ Ucl U (fbLam δ) := by
    have h := fb_inv_mem_Ucl hδ (g := w⁻¹) hw.1 (U.inv_mem hw.2)
    rwa [inv_inv] at h
  have huUcl : u ∈ Ucl U δ := ⟨hu.2, fun i j => le_of_lt (hu.1 i j)⟩
  exact fb_Ucl_mono hΛ (fb_mul_mem_Ucl (fbLam_pos δ).le (le_of_lt hδ) hwUcl huUcl)

/-! ## 2. The flower membership of a plaque point -/

/-- **The flower membership of a plaque point** (bounded form).  If `u ∈ V δ ∩ U` and `c ∈ C`,
then `u • c` lies in the flower set `flowerSet U δ C W` exactly when `c ∈ W`: the cross-section
property, applied to the *bounded* product `w * u ∈ Ucl U ρ`, forces the translating element to
be trivial. -/
lemma fb_flowerSet_mem_iff {U : Subgroup SL3} {C W : Set X3} {δ ρ : ℝ}
    (hCS : ∀ c ∈ C, ∀ u ∈ U, u ∈ Ucl U ρ → u • c ∈ C → u = 1)
    (hδ : 0 < δ) (hΛ : fbLam δ + δ + 3 * fbLam δ * δ ≤ ρ)
    {u : SL3} (hu : u ∈ V δ ∩ (U : Set SL3)) {c : X3} (hc : c ∈ C) :
    u • c ∈ flowerSet U δ C W ↔ c ∈ W := by
  constructor
  · rintro ⟨w, ⟨hw, hwU⟩, hwy⟩
    have hmemC : (w * u) • c ∈ C := by rw [mul_smul]; exact hwy.1
    have h1 : w * u = 1 :=
      hCS c hc (w * u) (U.mul_mem hwU hu.2)
        (fb_Vinv_mul_V_mem_Ucl hδ hΛ ⟨hw, hwU⟩ hu) hmemC
    have htriv : w • (u • c) = c := by rw [← mul_smul, h1, one_smul]
    rw [htriv] at hwy
    exact hwy.2
  · intro hcW
    refine ⟨u⁻¹, ⟨?_, U.inv_mem hu.2⟩, ?_⟩
    · show (u⁻¹)⁻¹ ∈ V δ
      rw [inv_inv]
      exact hu.1
    · show u⁻¹ • (u • c) ∈ C ∩ W
      have htriv : u⁻¹ • (u • c) = c := by rw [← mul_smul, inv_mul_cancel, one_smul]
      rw [htriv]
      exact ⟨hc, hcW⟩

/-- **The atoms of the flower σ-algebra are the pattern classes of the family `W`.**  For
`c ∈ C`, a point `y` lies in the atom of `c` exactly when `y` and `c` have the same `W`-pattern. -/
lemma fb_mem_atom_iff_pattern {U : Subgroup SL3} {C : Set X3} {δ ρ : ℝ} {W : ℕ → Set X3}
    (hCS : ∀ c ∈ C, ∀ u ∈ U, u ∈ Ucl U ρ → u • c ∈ C → u = 1)
    (hδ : 0 < δ) (hΛ : fbLam δ + δ + 3 * fbLam δ * δ ≤ ρ)
    {c : X3} (hc : c ∈ C) (y : X3) :
    y ∈ atom (flowerSigma U δ C W) c ↔ ∀ n, (y ∈ flowerSet U δ C (W n) ↔ c ∈ W n) := by
  have h1 : (1 : SL3) ∈ V δ ∩ (U : Set SL3) :=
    ⟨(Work.EKLContract.Lemmas.V_open_one δ hδ).2, U.one_mem⟩
  rw [show flowerSigma U δ C W
      = MeasurableSpace.generateFrom (Set.range (fun n => flowerSet U δ C (W n))) from rfl,
    mem_atom_iff_pattern]
  constructor
  · intro h n
    exact (h _ ⟨n, rfl⟩).trans (by simpa only [one_smul] using fb_flowerSet_mem_iff hCS hδ hΛ h1 hc)
  · intro h A hA
    obtain ⟨n, rfl⟩ := hA
    exact (h n).trans (by simpa only [one_smul] using
      (fb_flowerSet_mem_iff hCS hδ hΛ h1 hc).symm)

/-! ## 3. The atom of the flower σ-algebra at a plaque point -/

/-- **The atom of the flower σ-algebra at a plaque point is the plaque** (bounded form): for
`v ∈ V δ ∩ U` and `c ∈ C`,
`atom (flowerSigma U δ C W) (v • c) = (V δ ∩ U) • c`, provided `W 0 = X₃` and `W` separates the
points of `C`. -/
theorem fb_atom_eq_plaque {U : Subgroup SL3} {C : Set X3} {δ ρ : ℝ}
    (hCS : ∀ c ∈ C, ∀ u ∈ U, u ∈ Ucl U ρ → u • c ∈ C → u = 1)
    {W : ℕ → Set X3} (hW0 : W 0 = Set.univ)
    (hsep : ∀ b ∈ C, ∀ b' ∈ C, (∀ n, b ∈ W n ↔ b' ∈ W n) → b = b')
    (hδ : 0 < δ) (hΛ : fbLam δ + δ + 3 * fbLam δ * δ ≤ ρ)
    {v : SL3} (hv : v ∈ V δ) (hvU : v ∈ U) {b : X3} (hb : b ∈ C) :
    atom (flowerSigma U δ C W) (v • b)
      = (fun u : SL3 => u • b) '' (V δ ∩ (U : Set SL3)) := by
  have key : ∀ y : X3, y ∈ atom (flowerSigma U δ C W) (v • b)
      ↔ ∀ n, y ∈ flowerSet U δ C (W n) ↔ b ∈ W n := by
    intro y
    rw [show flowerSigma U δ C W
        = MeasurableSpace.generateFrom (Set.range (fun n => flowerSet U δ C (W n))) from rfl,
      mem_atom_iff_pattern]
    constructor
    · intro h n
      exact (h _ ⟨n, rfl⟩).trans (fb_flowerSet_mem_iff hCS hδ hΛ ⟨hv, hvU⟩ hb)
    · intro h A hA
      obtain ⟨n, rfl⟩ := hA
      exact (h n).trans (fb_flowerSet_mem_iff hCS hδ hΛ ⟨hv, hvU⟩ hb).symm
  ext y
  constructor
  · intro hy
    rw [key] at hy
    have hy0 : y ∈ flowerSet U δ C (W 0) := by rw [hy 0, hW0]; trivial
    obtain ⟨w, ⟨hw, hwU⟩, hwy⟩ := hy0
    set b' : X3 := w • y with hb'def
    have hb'C : b' ∈ C := by rw [hb'def]; exact hwy.1
    have hy_eq : y = w⁻¹ • b' := by rw [hb'def, ← mul_smul, inv_mul_cancel, one_smul]
    have hpat' : ∀ n, y ∈ flowerSet U δ C (W n) ↔ b' ∈ W n := by
      intro n
      rw [hy_eq]
      exact fb_flowerSet_mem_iff hCS hδ hΛ ⟨hw, U.inv_mem hwU⟩ hb'C
    have hb'b : b' = b := hsep b' hb'C b hb (fun n => (hpat' n).symm.trans (hy n))
    refine ⟨w⁻¹, ⟨hw, U.inv_mem hwU⟩, ?_⟩
    rw [← hb'b]
    exact hy_eq.symm
  · rintro ⟨u, ⟨hu, huU⟩, rfl⟩
    rw [key]
    intro n
    exact fb_flowerSet_mem_iff hCS hδ hΛ ⟨hu, huU⟩ hb

/-- A point of the atom of `c` has the same atom as `c` (for the flower σ-algebra). -/
lemma fb_atom_eq_of_mem_atom {U : Subgroup SL3} {C : Set X3} {δ : ℝ} {W : ℕ → Set X3} {c x : X3}
    (hx : x ∈ atom (flowerSigma U δ C W) c) :
    atom (flowerSigma U δ C W) x = atom (flowerSigma U δ C W) c := by
  rw [show flowerSigma U δ C W
      = MeasurableSpace.generateFrom (Set.range (fun n => flowerSet U δ C (W n))) from rfl] at hx ⊢
  exact atom_generateFrom_eq_of_mem hx

/-! ## 4. The flower set is Borel -/

/-- **The flower set is Borel** (bounded cross-section form).  `flowerSet U δ C W` is the image of
the Borel set `(V δ ∩ U) × (C ∩ W)` under the continuous action map, which is injective there by
the bounded cross-section property, so Lusin–Souslin applies. -/
theorem fb_flowerSet_borel {U : Subgroup SL3} (hUcl : IsClosed (U : Set SL3))
    {C W : Set X3} (hC : MeasurableSet C) (hW : MeasurableSet W) {δ ρ : ℝ}
    (hsep : ∀ v ∈ V δ ∩ (U : Set SL3), ∀ v' ∈ V δ ∩ (U : Set SL3), v⁻¹ * v' ∈ Ucl U ρ)
    (hCS : ∀ c ∈ C, ∀ u ∈ U, u ∈ Ucl U ρ → u • c ∈ C → u = 1) :
    MeasurableSet (flowerSet U δ C W) := by
  rw [flowerSet_eq_image]
  haveI : PolishSpace SL3 := Work.EKLContract.Lemmas.polishSpace_specialLinearGroup
  haveI : PolishSpace X3 := Work.EKLComp.X3Background.2.2.2.1
  refine MeasurableSet.image_of_continuousOn_injOn ?_ continuous_smul.continuousOn ?_
  · exact ((isOpen_V δ).measurableSet.inter hUcl.measurableSet).prod (hC.inter hW)
  · rintro ⟨v, x⟩ ⟨hv, hx⟩ ⟨v', x'⟩ ⟨hv', hx'⟩ heq
    change v • x = v' • x' at heq
    obtain ⟨hvV, hvU⟩ := hv
    obtain ⟨hv'V, hv'U⟩ := hv'
    obtain ⟨hxC, -⟩ := hx
    obtain ⟨hx'C, -⟩ := hx'
    have hmul : (v⁻¹ * v') • x' = x := by rw [mul_smul, ← heq, inv_smul_smul]
    have hmemC : (v⁻¹ * v') • x' ∈ C := by rw [hmul]; exact hxC
    have hone : v⁻¹ * v' = 1 :=
      hCS x' hx'C (v⁻¹ * v') (U.mul_mem (U.inv_mem hvU) hv'U)
        (hsep v ⟨hvV, hvU⟩ v' ⟨hv'V, hv'U⟩) hmemC
    have hvv : v = v' := inv_mul_eq_one.mp hone
    have hxx : x = x' := by
      rw [← hvv] at heq
      exact smul_left_cancel v heq
    rw [hvv, hxx]

/-- The flower σ-algebra of a *bounded* cross-section is a plaque algebra, on the part of its collar that is based at free points. Here `Ucl U r = {g ∈ U | ∀ i j, |g i j - 1 i j| ≤ r}` is the closed displacement ball, `flowerSet U δ C W = {x | ∃ v, v⁻¹ ∈ V δ, v ∈ U, v • x ∈ C ∩ W}` and `flowerSigma U δ C W` is the σ-algebra generated by `n ↦ flowerSet U δ C (W n)`. Route: on the collar the atoms of `flowerSigma` are the plaques `(V δ ∩ U) • c` (this is `Work.EKLRelCross.atom_flower`, whose hypothesis is the cross-section property, needed only for the bounded elements arising as products `w * u` with `w ∈ (V δ)⁻¹`, `u ∈ V δ` — for which the bound `Λ := 2 (1+δ)² + 1 + δ + 3 (2 (1+δ)² + 1) δ` suffices since `(V δ)⁻¹ ⊆ Ucl U (2 (1+δ)² + 1)` and `Ucl · Ucl ⊆ Ucl (a + b + 3ab)`), the collar is `m`-measurable (it is the generator `n = 0`), and the free-based part of the collar is `m`-measurable because it is the preimage of the Borel set `C ∩ {free}` under the base map of the collar, whose coordinates `{x ∈ collar | base x ∈ W n} = flowerSet U δ C (W n)` are generators (using the `atom_flower` pattern computation `y ∈ atom (v • c) ↔ ∀ n, y ∈ flowerSet U δ C (W n) ↔ c ∈ W n`). The shape at `x = v • c` is `{g ∈ SL3 | g * v ∈ V δ} ∩ U`, which is open and entrywise bounded (as `u = (u v) * v⁻¹` with `u v ∈ V δ` and the adjugate bound for `v⁻¹`); the equality needs that the base `c` has a free `U`-orbit (a stabiliser element would translate the shape). -/
theorem flower_plaque_bdd {U : Subgroup Work.EKLContract.SL3} (hUcl : IsClosed (U : Set Work.EKLContract.SL3)) {C : Set Work.EKLContract.X3} {δ ρ : ℝ} (hδ : 0 < δ) (hΛ : 2 * (1 + δ) ^ 2 + 1 + δ + 3 * (2 * (1 + δ) ^ 2 + 1) * δ ≤ ρ) (hCS : ∀ c ∈ C, ∀ u ∈ U, u ∈ Work.EKLRelCross.Ucl U ρ → u • c ∈ C → u = 1) (hCmeas : MeasurableSet C) {W : ℕ → Set Work.EKLContract.X3} (hW0 : W 0 = Set.univ) (hWmeas : ∀ n, MeasurableSet (W n)) (hWgen : borel Work.EKLContract.X3 = MeasurableSpace.generateFrom (Set.range W)) (hWsep : ∀ x ∈ C, ∀ y ∈ C, (∀ n, x ∈ W n ↔ y ∈ W n) → x = y) (hFree : MeasurableSet {x : Work.EKLContract.X3 | ∀ u ∈ U, u • x = x → u = 1}) : Work.EKLContract.IsPlaqueAlgebra U (⋃ c ∈ (C ∩ {x : Work.EKLContract.X3 | ∀ u ∈ U, u • x = x → u = 1}), Work.EKLContract.atom (Work.EKLRelCross.flowerSigma U δ C W) c) (Work.EKLRelCross.flowerSigma U δ C W) := by 
  classical
  -- the constant `Λ` of the statement is `fbLam δ + δ + 3 (fbLam δ) δ`
  have hΛ' : fbLam δ + δ + 3 * fbLam δ * δ ≤ ρ := by simpa only [fbLam] using hΛ
  -- the products occurring in the collar lie in the bounded ball `Ucl U ρ`
  have hsepρ : ∀ v ∈ V δ ∩ (U : Set SL3), ∀ v' ∈ V δ ∩ (U : Set SL3), v⁻¹ * v' ∈ Ucl U ρ := by
    intro v hv v' hv'
    refine fb_Vinv_mul_V_mem_Ucl hδ hΛ' ⟨?_, U.inv_mem hv.2⟩ hv'
    rw [mem_Vinv_iff, inv_inv]
    exact hv.1
  -- each generator of the flower σ-algebra is Borel, so `m ≤ borel X₃`
  have hsub : flowerSigma U δ C W ≤ borel X3 := by
    refine MeasurableSpace.generateFrom_le fun t ht => ?_
    obtain ⟨n, rfl⟩ := ht
    exact fb_flowerSet_borel hUcl hCmeas (hWmeas n) hsepρ hCS
  -- the atoms of `m` at points of `C` are the pattern classes of `W`
  have hpat : ∀ c ∈ C, ∀ y : X3,
      y ∈ atom (flowerSigma U δ C W) c ↔ ∀ n, (y ∈ flowerSet U δ C (W n) ↔ c ∈ W n) :=
    fun c hc y => fb_mem_atom_iff_pattern hCS hδ hΛ' hc y
  -- the base point in `C` is unique
  have huniq : ∀ x : X3, (∃ c ∈ C, x ∈ atom (flowerSigma U δ C W) c) →
      ∃! c, c ∈ C ∧ x ∈ atom (flowerSigma U δ C W) c := by
    rintro x ⟨c, hcC, hxc⟩
    refine ⟨c, ⟨hcC, hxc⟩, ?_⟩
    rintro c' ⟨hc'C, hxc'⟩
    exact (hWsep c hcC c' hc'C (fun n =>
      ((hpat c hcC x).mp hxc n).symm.trans ((hpat c' hc'C x).mp hxc' n))).symm
  -- the free-based part of the collar is `m`-measurable
  have hZmeas := meas_free_atoms (U := U) (C := C) (δ := δ) (W := W)
    hW0 hWgen hsub hCmeas hFree hpat huniq
  refine ⟨hsub, ⟨Set.range (fun n => flowerSet U δ C (W n)), Set.countable_range _, rfl⟩,
    hZmeas, ?_⟩
  intro x hxZ
  rw [Set.mem_iUnion₂] at hxZ
  obtain ⟨c, hcCF, hxc⟩ := hxZ
  obtain ⟨hcC, hcF⟩ := hcCF
  -- the atom of `c` is the plaque through `c`
  have hatomc : atom (flowerSigma U δ C W) c
      = (fun u : SL3 => u • c) '' (V δ ∩ (U : Set SL3)) := by
    have h := fb_atom_eq_plaque (U := U) (C := C) (δ := δ) (ρ := ρ) hCS hW0 hWsep hδ hΛ'
      (v := (1 : SL3)) (Work.EKLContract.Lemmas.V_open_one δ hδ).2 U.one_mem (b := c) hcC
    simpa only [one_smul] using h
  -- `x` is a plaque translate of `c`
  have hxplaque : x ∈ (fun u : SL3 => u • c) '' (V δ ∩ (U : Set SL3)) := by
    rw [← hatomc]; exact hxc
  obtain ⟨v, ⟨hvV, hvU⟩, hvx⟩ := hxplaque
  have hvxc : v • c = x := hvx
  -- the atom of `x` is the same plaque
  have hatomx : atom (flowerSigma U δ C W) x
      = (fun u : SL3 => u • c) '' (V δ ∩ (U : Set SL3)) := by
    rw [fb_atom_eq_of_mem_atom hxc, hatomc]
  -- the shape at `x = v • c` and its entrywise bound
  have hshape := shape_plaque_bdd (U := U) (C := C) (δ := δ) (W := W) (c := c)
    hcF (v := v) hvV hvU hatomc
  rw [hvxc] at hshape
  refine ⟨?_, ?_, hshape.1, hshape.2⟩
  · intro y hy
    refine Set.mem_iUnion₂.mpr ⟨c, ⟨hcC, hcF⟩, ?_⟩
    rw [← fb_atom_eq_of_mem_atom hxc]
    exact hy
  · intro y hy
    rw [hatomx] at hy
    obtain ⟨u, ⟨huV, huU⟩, huy⟩ := hy
    refine ⟨u * v⁻¹, U.mul_mem huU (U.inv_mem hvU), ?_⟩
    show (u * v⁻¹) • x = y
    rw [← huy, mul_smul, ← hvxc, inv_smul_smul]


end Work.EKLRelCross
