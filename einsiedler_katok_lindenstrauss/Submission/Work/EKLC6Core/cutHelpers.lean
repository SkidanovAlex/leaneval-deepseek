import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLContract.Interfaces
import Submission.Work.EKLContract.Lemmas.V_open_one
import Submission.Work.EKLContract.Lemmas.mkX_mul
import Submission.Work.EKLComp.LeafDefs
import Submission.Work.EKLC6Core.atom_iSup_comap_iterate_eq

/-!
# `Work.EKLC6Core.cutHelpers` — the descending σ-algebra and the atom-transfer package

Vocabulary for the cut-based proof of `Work.EKLC6Core.exists_desc_subordinate`:

* `descSig t M = ⨆ₙ comap ((aDiag t ·)^[n]) M` — the *descending* σ-algebra of the target (`A`),
  with its elementary properties: `M ≤ descSig t M` (level `0`), `descSig t M ≤ borel` for
  `M ≤ borel`, countable generation, `atom (descSig t M) x ⊆ atom M x`, and the descent
  `comap (aDiag t ·) (descSig t M) ≤ descSig t M`;
* the *atom-transfer package*: the shape is a right translate along an atom
  (`shape_eq_translate_of_atom_eq_c`), hence relative openness of the shape
  (`exists_isOpen_shape_of_forall_exists_atom_eq_c`), the orbit clause
  (`atom_subset_orb_of_forall_exists_atom_eq_c`) and the entrywise bound
  (`exists_bound_shape_of_forall_exists_atom_eq_c`) are inherited by any `A`-saturated set all of
  whose atoms meet a good set.
-/

open MeasureTheory Set Topology Filter
open scoped ENNReal Pointwise

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **The descending σ-algebra** of the diagonal flow: `⨆ₙ comap ((aDiag t ·)^[n]) M`. -/
def descSig (t : Fin 3 → ℝ) (M : MeasurableSpace X3) : MeasurableSpace X3 :=
  ⨆ n : ℕ, MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n]) M

/-- The level-`0` term: `M ≤ descSig t M`. -/
theorem le_descSig (t : Fin 3 → ℝ) (M : MeasurableSpace X3) : M ≤ descSig t M := by
  have h := le_iSup (fun n : ℕ =>
    MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n]) M) 0
  rw [Function.iterate_zero, MeasurableSpace.comap_id] at h
  exact h

/-- The atoms of the descending σ-algebra are contained in those of `M`. -/
theorem atom_descSig_le (t : Fin 3 → ℝ) (M : MeasurableSpace X3) (y : X3) :
    atom (descSig t M) y ⊆ atom M y := by
  intro z hz
  rw [Work.EKLContract.atom, Set.mem_sInter] at hz ⊢
  intro s hs
  exact hz s ⟨le_descSig t M s hs.1, hs.2⟩

/-- `atom (descSig t M) x = {y | ∀ n, ((aDiag t ·)^[n]) y ∈ atom M (((aDiag t ·)^[n]) x)}`. -/
theorem atom_descSig_eq (t : Fin 3 → ℝ) (M : MeasurableSpace X3) (x : X3) :
    atom (descSig t M) x =
      {y : X3 | ∀ n : ℕ, ((fun z : X3 => aDiag t • z)^[n]) y
        ∈ atom M (((fun z : X3 => aDiag t • z)^[n]) x)} := by
  rw [descSig]
  exact atom_iSup_comap_iterate_eq M (fun x : X3 => aDiag t • x) x

/-- The pullback of the Borel σ-algebra of `X₃` along an iterate of the diagonal flow is
contained in the Borel σ-algebra.  (No `MeasurableSpace` variable is in scope here, so that
instance search does not capture it.) -/
theorem comap_iterate_le_borel (t : Fin 3 → ℝ) (n : ℕ) :
    MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n]) (borel X3) ≤ borel X3 := by
  intro s hs
  rw [MeasurableSpace.measurableSet_comap] at hs
  obtain ⟨t', ht', rfl⟩ := hs
  exact ht'.preimage (((continuous_const_smul (aDiag t)).iterate n).measurable)

/-- The descending σ-algebra is contained in the Borel σ-algebra when `M` is. -/
theorem descSig_le_borel {t : Fin 3 → ℝ} (M : MeasurableSpace X3) (hM : M ≤ borel X3) :
    descSig t M ≤ borel X3 :=
  iSup_le fun n => (MeasurableSpace.comap_mono hM).trans (comap_iterate_le_borel t n)

/-- The descent: `comap (aDiag t ·) (descSig t M) ≤ descSig t M`. -/
theorem comap_descSig_le (t : Fin 3 → ℝ) (M : MeasurableSpace X3) :
    MeasurableSpace.comap (fun x : X3 => aDiag t • x) (descSig t M) ≤ descSig t M := by
  rw [descSig, MeasurableSpace.comap_iSup]
  refine iSup_le fun n => ?_
  rw [MeasurableSpace.comap_comp]
  rw [← Function.iterate_succ]
  exact le_iSup (fun n : ℕ =>
    MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n]) M) (n + 1)

/-- **Countable generation** of the descending σ-algebra. -/
theorem descSig_countably_generated {t : Fin 3 → ℝ} {M : MeasurableSpace X3}
    {b : Set (Set X3)} (hb : b.Countable) (hMb : M = MeasurableSpace.generateFrom b) :
    ∃ b' : Set (Set X3), b'.Countable ∧ descSig t M = MeasurableSpace.generateFrom b' := by
  classical
  obtain ⟨b₀, hb₀⟩ := (hb.union (Set.countable_singleton (Set.univ))).exists_eq_range
    ⟨Set.univ, Or.inr rfl⟩
  have hgeneq : MeasurableSpace.generateFrom (Set.range b₀) = MeasurableSpace.generateFrom b := by
    have h1 : MeasurableSpace.generateFrom (b ∪ {Set.univ}) = MeasurableSpace.generateFrom b := by
      rw [Set.union_singleton, MeasurableSpace.generateFrom_insert_univ]
    rw [← hb₀, h1]
  refine ⟨Set.range (fun p : ℕ × ℕ =>
    ((fun x : X3 => aDiag t • x)^[p.1]) ⁻¹' (b₀ p.2)), Set.countable_range _, ?_⟩
  rw [descSig, hMb, ← hgeneq]
  refine le_antisymm (iSup_le fun n => ?_) ?_
  · rw [MeasurableSpace.comap_generateFrom]
    refine MeasurableSpace.generateFrom_mono ?_
    rintro s ⟨t', ht', rfl⟩
    obtain ⟨m, rfl⟩ := ht'
    exact ⟨(n, m), rfl⟩
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨p, rfl⟩
    exact le_iSup (fun n : ℕ => MeasurableSpace.comap ((fun x : X3 => aDiag t • x)^[n])
      (MeasurableSpace.generateFrom (Set.range b₀))) p.1 _
      (MeasurableSpace.measurableSet_comap.mpr
        ⟨b₀ p.2, MeasurableSpace.measurableSet_generateFrom ⟨p.2, rfl⟩, rfl⟩)

/-! ## The atom-transfer package -/

/-- `x ∈ atom A x`. -/
theorem mem_atom_self_c (A : MeasurableSpace X3) (x : X3) : x ∈ atom A x := by
  rw [Work.EKLContract.atom, Set.mem_sInter]
  exact fun s hs => hs.2

/-- Points of an atom have the same atom. -/
theorem atom_eq_of_mem_atom_c {A : MeasurableSpace X3} {x y : X3} (hy : y ∈ atom A x) :
    atom A y = atom A x := by
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    rw [Work.EKLContract.atom, Set.mem_sInter] at hz ⊢
    intro s hs
    exact hz s ⟨hs.1, hy s hs⟩
  · intro z hz
    rw [Work.EKLContract.atom, Set.mem_sInter] at hz ⊢
    intro s hs
    have hxs : x ∈ s := by
      by_contra hcon
      exact (hy sᶜ ⟨hs.1.compl, hcon⟩) hs.2
    exact hz s ⟨hs.1, hxs⟩

/-- The shape of an atom is computed by right translation along the atom. -/
theorem shape_eq_translate_of_atom_eq_c {A : MeasurableSpace X3} {U : Subgroup SL3}
    {x : X3} {u : SL3} (hu : u ∈ U) (hatom : atom A (u • x) = atom A x) :
    shape A U (u • x) = (fun s : SL3 => s * u⁻¹) '' shape A U x := by
  ext s
  constructor
  · rintro ⟨hsU, hsA⟩
    refine ⟨s * u, ⟨?_, ?_⟩, by group⟩
    · exact U.mul_mem hsU hu
    · have h1 : (s * u) • x = s • (u • x) := by rw [mul_smul]
      rw [h1, ← hatom]
      exact hsA
  · rintro ⟨a, ⟨haU, haA⟩, rfl⟩
    refine ⟨U.mul_mem haU (U.inv_mem hu), ?_⟩
    have h1 : (a * u⁻¹) • (u • x) = a • x := by rw [mul_smul, inv_smul_smul]
    rw [h1]
    simpa [hatom] using haA

/-- **Relative openness of the shape is an atom property.** -/
theorem exists_isOpen_shape_of_mem_atom_c {A : MeasurableSpace X3} {U : Subgroup SL3} {x : X3}
    {u : SL3} (hu : u ∈ U) (hatom : atom A (u • x) = atom A x)
    (h : ∃ O : Set SL3, IsOpen O ∧ shape A U x = O ∩ (U : Set SL3)) :
    ∃ O : Set SL3, IsOpen O ∧ shape A U (u • x) = O ∩ (U : Set SL3) := by
  obtain ⟨O, hO, hEq⟩ := h
  refine ⟨{s : SL3 | s * u ∈ O}, hO.preimage (by fun_prop), ?_⟩
  rw [shape_eq_translate_of_atom_eq_c hu hatom, hEq]
  ext s
  constructor
  · rintro ⟨a, ⟨haO, haU⟩, rfl⟩
    exact ⟨by simpa using haO, U.mul_mem haU (U.inv_mem hu)⟩
  · rintro ⟨hsO, hsU⟩
    refine ⟨s * u, ⟨hsO, U.mul_mem hsU hu⟩, ?_⟩
    group

/-- **Inheritance of the openness of the shape.** -/
theorem exists_isOpen_shape_of_forall_exists_atom_eq_c {A : MeasurableSpace X3}
    {U : Subgroup SL3} {Z H : Set X3} (hatom : ∀ x ∈ Z, ∃ y ∈ H, atom A x = atom A y)
    (horb : ∀ y ∈ H, atom A y ⊆ (fun u : SL3 => u • y) '' (U : Set SL3))
    (hopen : ∀ y ∈ H, ∃ O : Set SL3, IsOpen O ∧ shape A U y = O ∩ (U : Set SL3)) :
    ∀ x ∈ Z, ∃ O : Set SL3, IsOpen O ∧ shape A U x = O ∩ (U : Set SL3) := by
  intro x hx
  obtain ⟨y, hyH, hxy⟩ := hatom x hx
  have hxatom : x ∈ atom A y := by rw [← hxy]; exact mem_atom_self_c A x
  obtain ⟨u, huU, hux⟩ := horb y hyH hxatom
  subst hux
  exact exists_isOpen_shape_of_mem_atom_c huU (atom_eq_of_mem_atom_c hxatom) (hopen y hyH)

/-- **Inheritance of the orbit clause.** -/
theorem atom_subset_orb_of_forall_exists_atom_eq_c {A : MeasurableSpace X3} {U : Subgroup SL3}
    {Z H : Set X3} (hatom : ∀ x ∈ Z, ∃ y ∈ H, atom A x = atom A y)
    (horb : ∀ y ∈ H, atom A y ⊆ (fun u : SL3 => u • y) '' (U : Set SL3)) :
    ∀ x ∈ Z, atom A x ⊆ (fun u : SL3 => u • x) '' (U : Set SL3) := by
  intro x hx z hz
  obtain ⟨y, hyH, hxy⟩ := hatom x hx
  have hxatom : x ∈ atom A y := by rw [← hxy]; exact mem_atom_self_c A x
  obtain ⟨u, huU, hux⟩ := horb y hyH hxatom
  have hzy : z ∈ atom A y := by rw [← hxy]; exact hz
  obtain ⟨w, hwU, hwz⟩ := horb y hyH hzy
  refine ⟨w * u⁻¹, U.mul_mem hwU (U.inv_mem huU), ?_⟩
  show (w * u⁻¹) • x = z
  rw [← hux, mul_smul, inv_smul_smul]
  exact hwz

/-- Entries of a product are bounded by `3 * sA * sB`. -/
theorem mul_entries_le_c {A B : Matrix (Fin 3) (Fin 3) ℝ} (i j : Fin 3) {sA sB : ℝ}
    (hA : ∀ k l, |A k l| ≤ sA) (hB : ∀ k l, |B k l| ≤ sB) (hsA : 0 ≤ sA) (hsB : 0 ≤ sB) :
    |(A * B) i j| ≤ 3 * sA * sB := by
  rw [Matrix.mul_apply]
  calc |∑ k : Fin 3, A i k * B k j| ≤ ∑ k : Fin 3, |A i k * B k j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k : Fin 3, |A i k| * |B k j| := by simp [abs_mul]
    _ ≤ ∑ _k : Fin 3, sA * sB :=
        Finset.sum_le_sum (fun k _ => mul_le_mul (hA i k) (hB k j) (abs_nonneg _) hsA)
    _ = 3 * (sA * sB) := by simp [Finset.sum_const, Fintype.card_fin]
    _ = 3 * sA * sB := by ring

/-- **Inheritance of the entrywise bound on the shape.** -/
theorem exists_bound_shape_of_forall_exists_atom_eq_c {A : MeasurableSpace X3}
    {U : Subgroup SL3} {Z H : Set X3} {ρ : ℝ}
    (hatom : ∀ x ∈ Z, ∃ y ∈ H, ∃ u ∈ Work.EKLComp.Uball U ρ, x = u • y ∧ atom A x = atom A y)
    (hbd : ∀ y ∈ H, ∃ C : ℝ, ∀ v ∈ shape A U y, ∀ i j, |(v : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C)
    {D : ℝ} (hD : ∀ g ∈ Work.EKLComp.Uball U ρ, ∀ i j,
      |(((g⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j| ≤ D) (hD0 : 0 ≤ D) :
    ∀ x ∈ Z, ∃ C : ℝ, ∀ v ∈ shape A U x, ∀ i j,
      |(v : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C := by
  intro x hx
  obtain ⟨y, hyH, u, huU, hux, hatomeq⟩ := hatom x hx
  obtain ⟨C, hC⟩ := hbd y hyH
  refine ⟨3 * C * D, fun v hv i j => ?_⟩
  subst hux
  rw [shape_eq_translate_of_atom_eq_c huU.1 hatomeq] at hv
  obtain ⟨v', hv', rfl⟩ := hv
  have hcoe : (((v' * u⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ))
      = ((v' : SL3) : Matrix (Fin 3) (Fin 3) ℝ) * ((u⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
    rw [Matrix.SpecialLinearGroup.coe_mul]
  rw [hcoe]
  exact mul_entries_le_c i j (fun k l => hC v' hv' k l)
    (fun k l => hD u huU k l) (le_trans (abs_nonneg _) (hC v' hv' 0 0)) hD0

/-- `atom m x = (fun u => u • x) '' shape m U x` when the atom lies in the `U`-orbit of `x`. -/
theorem atom_eq_smul_shape_c {m : MeasurableSpace X3} {U : Subgroup SL3} {x : X3}
    (h : atom m x ⊆ (fun u : SL3 => u • x) '' (U : Set SL3)) :
    atom m x = (fun u : SL3 => u • x) '' shape m U x := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro z hz
    obtain ⟨u, huU, rfl⟩ := h hz
    exact ⟨u, ⟨huU, hz⟩, rfl⟩
  · rintro z ⟨u, ⟨huU, hu⟩, rfl⟩
    exact hu

end Work.EKLC6Core
