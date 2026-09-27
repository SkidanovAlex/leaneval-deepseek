import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.exists_gen_partition
import Submission.Work.EKLC6Core.atom_iSup_comap_iterate_eq
import Submission.Work.EKLC6Core.ae_ball_in_atom
import Submission.Work.EKLC6Core.uminus_isHoro
import Submission.Work.EKLC6Core.contraction_rate_uminus
import Submission.Work.EKLContract.Interfaces

/-!
# `Work.EKLC6Core.coding_calculus` — the atom/shape calculus of a coding partition

For a countable partition `P : ℕ → Set X₃` of `X₃` and `t : Fin 3 → ℝ`, this module computes the
atoms and shapes of the *past* σ-algebra

`pastSigma t P = ⨆ n, comap ((aDiag t ·)^[n]) σ(P)`

in terms of the *codes* of the points (see the individual docstrings).  The main results are the
code formula for the atom, the *lower bound* `plaque_subset_atom_of_cell_open` (Pisa 7.48a), the
saturation of the coding property by atoms, and the assembly
`exists_coding_partition_of_null_atom_set`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-! ## The cell of a point -/

/-- The index of the cell of `x` (junk value `0` if `x` lies in no cell). -/
noncomputable def cellIdx (P : ℕ → Set X3) (x : X3) : ℕ := by
  classical
  exact if h : ∃ n, x ∈ P n then h.choose else 0

/-- The cell of `x` for a partition `P`. -/
noncomputable def cellOf (P : ℕ → Set X3) (x : X3) : Set X3 := P (cellIdx P x)

theorem mem_cellOf {P : ℕ → Set X3} (hcov : (⋃ n, P n) = Set.univ) (x : X3) :
    x ∈ cellOf P x := by
  classical
  have h : x ∈ (⋃ n, P n) := by rw [hcov]; exact Set.mem_univ x
  have h' : ∃ n, x ∈ P n := by simpa using h
  simp only [cellOf, cellIdx, dif_pos h']
  exact h'.choose_spec

theorem cellOf_eq_of_mem {P : ℕ → Set X3} (hdisj : ∀ m n, m ≠ n → Disjoint (P m) (P n))
    {x : X3} {n : ℕ} (hx : x ∈ P n) : cellOf P x = P n := by
  classical
  have h : ∃ k, x ∈ P k := ⟨n, hx⟩
  simp only [cellOf, cellIdx, dif_pos h]
  by_cases hnk : h.choose = n
  · rw [hnk]
  · exact absurd h.choose_spec (fun hc => Set.disjoint_left.mp (hdisj h.choose n hnk) hc hx)

/-- **The atom of a cell** for a partition: the `σ(P)`-atom of a point is its cell. -/
theorem atom_generateFrom_range_of_cell {P : ℕ → Set X3}
    (hdisj : ∀ m n, m ≠ n → Disjoint (P m) (P n)) (hcov : (⋃ n, P n) = Set.univ) {x : X3} :
    atom (MeasurableSpace.generateFrom (Set.range P)) x = cellOf P x := by
  classical
  set m := MeasurableSpace.generateFrom (Set.range P) with hm
  obtain ⟨k, hk⟩ : ∃ k, x ∈ P k := by
    have h : x ∈ (⋃ n, P n) := by rw [hcov]; exact Set.mem_univ x
    simpa using h
  have hmem : ∀ n, MeasurableSet[m] (P n) := fun n =>
    MeasurableSpace.measurableSet_generateFrom ⟨n, rfl⟩
  have hcell : cellOf P x = P k := cellOf_eq_of_mem hdisj hk
  rw [hcell]
  refine Set.Subset.antisymm (Set.sInter_subset_of_mem ⟨hmem k, hk⟩) ?_
  intro y hy
  have hprof : ∀ n, (y ∈ P n ↔ x ∈ P n) := by
    intro n
    constructor
    · intro hyn
      by_contra hxn
      exact Set.disjoint_left.mp (hdisj n k (by rintro rfl; exact hxn hk)) hyn hy
    · intro hxn
      by_contra hyn'
      exact Set.disjoint_left.mp (hdisj n k (by rintro rfl; exact hyn' hy)) hxn hk
  have hiff : ∀ s, MeasurableSet[m] s → (x ∈ s ↔ y ∈ s) := by
    intro s hs
    induction s, hs using MeasurableSpace.generateFrom_induction (C := Set.range P) with
    | hC t ht _ => obtain ⟨n, rfl⟩ := ht; exact (hprof n).symm
    | empty => simp
    | compl t ht ih => simpa [Set.mem_compl_iff] using ih.not
    | iUnion f hf ihf => simp only [Set.mem_iUnion]; exact exists_congr fun n => ihf n
  exact Set.mem_sInter.mpr fun s hs => (hiff s hs.1).mp hs.2

/-! ## The atom and shape of the past σ-algebra, in terms of cells -/

/-- **The atom of the past σ-algebra is a code class**: every iterate lies in the cell of the
corresponding iterate of `x`. -/
theorem atom_pastSigma_eq_cellOf {t : Fin 3 → ℝ} {P : ℕ → Set X3}
    (hdisj : ∀ m n, m ≠ n → Disjoint (P m) (P n)) (hcov : (⋃ n, P n) = Set.univ) (x : X3) :
    atom (pastSigma t P) x =
      ⋂ k : ℕ, ((fun y : X3 => aDiag t • y)^[k]) ⁻¹'
        cellOf P (((fun y : X3 => aDiag t • y)^[k]) x) := by
  rw [pastSigma, atom_iSup_comap_iterate_eq]
  ext y
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
  constructor
  · intro h k
    simpa only [atom_generateFrom_range_of_cell hdisj hcov] using h k
  · intro h k
    simpa only [atom_generateFrom_range_of_cell hdisj hcov] using h k

/-- Membership in the past atom, in code form. -/
theorem mem_atom_pastSigma_iff_cellOf {t : Fin 3 → ℝ} {P : ℕ → Set X3}
    (hdisj : ∀ m n, m ≠ n → Disjoint (P m) (P n)) (hcov : (⋃ n, P n) = Set.univ)
    {x y : X3} :
    y ∈ atom (pastSigma t P) x ↔
      ∀ k, ((fun z : X3 => aDiag t • z)^[k]) y ∈
        cellOf P (((fun z : X3 => aDiag t • z)^[k]) x) := by
  rw [atom_pastSigma_eq_cellOf hdisj hcov]
  simp [Set.mem_iInter, Set.mem_preimage]

/-- The shape of the past σ-algebra, in code form. -/
theorem shape_pastSigma_eq_cellOf {t : Fin 3 → ℝ} {P : ℕ → Set X3}
    (hdisj : ∀ m n, m ≠ n → Disjoint (P m) (P n)) (hcov : (⋃ n, P n) = Set.univ) (x : X3) :
    shape (pastSigma t P) (Uminus t) x =
      {u : SL3 | u ∈ Uminus t ∧ ∀ k,
        ((fun z : X3 => aDiag t • z)^[k]) (u • x) ∈
          cellOf P (((fun z : X3 => aDiag t • z)^[k]) x)} := by
  ext u
  simp only [shape, Set.mem_ofPred_eq, mem_atom_pastSigma_iff_cellOf hdisj hcov]

/-- **Descent**: the iterate of an atom is contained in the atom of the iterate. -/
theorem mem_atom_pastSigma_iterate {t : Fin 3 → ℝ} {P : ℕ → Set X3}
    (hdisj : ∀ m n, m ≠ n → Disjoint (P m) (P n)) (hcov : (⋃ n, P n) = Set.univ)
    {x y : X3} (hy : y ∈ atom (pastSigma t P) x) (k : ℕ) :
    ((fun z : X3 => aDiag t • z)^[k]) y ∈
      atom (pastSigma t P) (((fun z : X3 => aDiag t • z)^[k]) x) := by
  rw [mem_atom_pastSigma_iff_cellOf hdisj hcov] at hy ⊢
  intro j
  simp only [← Function.iterate_add_apply]
  exact hy (j + k)

/-! ## Conjugation by the flow -/

/-- The flow normalises `Uminus t`: conjugation by any power of `aDiag t` preserves `Uminus t`. -/
theorem conj_pow_mem_uminus (t : Fin 3 → ℝ) {u : SL3} (hu : u ∈ Uminus t) (k : ℕ) :
    aDiag t ^ k * u * (aDiag t ^ k)⁻¹ ∈ Uminus t := by
  have hU := (uminus_isHoro t).1
  induction k with
  | zero => simpa using hu
  | succ m ih =>
    rw [pow_succ']
    have key : aDiag t * aDiag t ^ m * u * (aDiag t * aDiag t ^ m)⁻¹
        = aDiag t * (aDiag t ^ m * u * (aDiag t ^ m)⁻¹) * (aDiag t)⁻¹ := by group
    rw [key]
    exact hU.2.1 t _ ih

/-- **Contraction inside `Uminus t`**: conjugation by `aDiag t ^ k` maps `V ρ ∩ Uminus t` into
itself. -/
theorem conj_pow_mem_V (t : Fin 3 → ℝ) {k : ℕ} {ρ : ℝ} (hρ : 0 < ρ) {u : SL3}
    (hu : u ∈ Uminus t) (huρ : u ∈ V ρ) :
    aDiag t ^ k * u * (aDiag t ^ k)⁻¹ ∈ V ρ := by
  obtain ⟨α, hα, h⟩ := contraction_rate_uminus t
  refine V_mono ?_ (h k ρ hρ u hu huρ)
  have h1 : Real.exp (-(α * (k : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : (0:ℝ) ≤ α * (k:ℝ) := by positivity
    linarith
  exact mul_le_of_le_one_left (le_of_lt hρ) h1

/-! ## The lower bound (Pisa 7.48a) -/

/-- **The lower bound from leaf-open cells.**  If for every `k` the cell of the `k`-th iterate
of `x` contains the whole `V δ ∩ Uminus t`-plaque of that iterate, then the whole plaquette
`(V δ ∩ Uminus t) • x` is contained in the atom of `x` in the past σ-algebra. -/
theorem plaque_subset_atom_of_cell_open {t : Fin 3 → ℝ} {P : ℕ → Set X3}
    (hdisj : ∀ m n, m ≠ n → Disjoint (P m) (P n)) (hcov : (⋃ n, P n) = Set.univ)
    {x : X3} {δ : ℝ} (hδ : 0 < δ)
    (hcell : ∀ k, ∀ v : SL3, v ∈ Uminus t → v ∈ V δ →
      v • (((fun z : X3 => aDiag t • z)^[k]) x) ∈
        cellOf P (((fun z : X3 => aDiag t • z)^[k]) x)) :
    ∀ v : SL3, v ∈ Uminus t → v ∈ V δ → v • x ∈ atom (pastSigma t P) x := by
  intro v hvU hvδ
  rw [mem_atom_pastSigma_iff_cellOf hdisj hcov]
  intro k
  rw [orbit_smul_eq t k v x]
  exact hcell k _ (conj_pow_mem_uminus t hvU k) (conj_pow_mem_V t hδ hvU hvδ)

/-! ## Boundedness of the shape and the coding points -/

/-- **The shape is entrywise bounded** as soon as the leaf-pieces of the cell are. -/
theorem entries_bound_of_cell_bound {t : Fin 3 → ℝ} {P : ℕ → Set X3}
    (hdisj : ∀ m n, m ≠ n → Disjoint (P m) (P n)) (hcov : (⋃ n, P n) = Set.univ)
    {x : X3} {n : ℕ} (hx : x ∈ P n) {C : ℝ}
    (hC : ∀ z ∈ P n, ∀ u : SL3, u ∈ Uminus t → u • z ∈ P n → ∀ i j, |u i j| ≤ C) :
    ∀ u ∈ shape (pastSigma t P) (Uminus t) x, ∀ i j, |u i j| ≤ C := by
  intro u hu i j
  obtain ⟨huU, huatom⟩ := hu
  have hle : MeasurableSpace.generateFrom (Set.range P) ≤ pastSigma t P := by
    rw [pastSigma]
    simpa using le_iSup (fun n : ℕ => MeasurableSpace.comap
      ((fun x : X3 => aDiag t • x)^[n]) (MeasurableSpace.generateFrom (Set.range P))) 0
  have hmem : MeasurableSet[pastSigma t P] (P n) :=
    hle (P n) (MeasurableSpace.measurableSet_generateFrom
      (show P n ∈ Set.range P from ⟨n, rfl⟩))
  have hcell : atom (pastSigma t P) x ⊆ P n := Set.sInter_subset_of_mem ⟨hmem, hx⟩
  exact hC x hx u huU (hcell huatom) i j

/-- **The coding point property**: the atom is contained in the `Uminus t`-leaf of `x`, it has a
relatively open shape, and the shapes of all points of the atom are uniformly entrywise
bounded.  (The uniform form of the bound makes the property saturated by atoms,
`isCodingPoint_saturates`.) -/
def IsCodingPoint (t : Fin 3 → ℝ) (m : MeasurableSpace X3) (x : X3) : Prop :=
  (atom m x ⊆ (fun u : SL3 => u • x) '' (Uminus t : Set SL3)) ∧
  (∃ O : Set SL3, IsOpen O ∧ shape m (Uminus t) x = O ∩ (Uminus t : Set SL3)) ∧
  (∃ C : ℝ, ∀ y ∈ atom m x, ∀ u ∈ shape m (Uminus t) y, ∀ i j, |u i j| ≤ C)

/-- Membership in an atom is an equivalence relation on atoms. -/
theorem atom_eq_of_mem_atom {m : MeasurableSpace X3} {x y : X3} (hy : y ∈ atom m x) :
    atom m y = atom m x := by
  have hxy : ∀ s : Set X3, MeasurableSet[m] s → (x ∈ s ↔ y ∈ s) := mem_atom_iff.mp hy
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    rw [mem_atom_iff] at hz ⊢
    intro s hs
    exact (hxy s hs).trans (hz s hs)
  · intro z hz
    rw [mem_atom_iff] at hz ⊢
    intro s hs
    exact (hxy s hs).symm.trans (hz s hs)

/-- **The coding property is saturated by atoms**: every point of the atom of a coding point is
a coding point. -/
theorem isCodingPoint_saturates {t : Fin 3 → ℝ} {m : MeasurableSpace X3} {x : X3}
    (h : IsCodingPoint t m x) : atom m x ⊆ {y | IsCodingPoint t m y} := by
  intro y hy
  obtain ⟨horb, hO, hC⟩ := h
  obtain ⟨O, hOopen, hOshape⟩ := hO
  obtain ⟨C, hCb⟩ := hC
  obtain ⟨u, huU, huy⟩ := horb hy
  have hatom : atom m y = atom m x := atom_eq_of_mem_atom hy
  have hleaf : (fun u : SL3 => u • x) '' (Uminus t : Set SL3)
      = (fun u : SL3 => u • y) '' (Uminus t : Set SL3) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w * u⁻¹, (Uminus t).mul_mem hw ((Uminus t).inv_mem huU), ?_⟩
      show (w * u⁻¹) • y = w • x
      rw [huy.symm, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
    · rintro ⟨w, hw, rfl⟩
      refine ⟨w * u, (Uminus t).mul_mem hw huU, ?_⟩
      show (w * u) • x = w • y
      rw [huy.symm, mul_smul]
  have hshape : shape m (Uminus t) y
      = (fun s : SL3 => s * u⁻¹) '' (shape m (Uminus t) x) := by
    ext v
    constructor
    · intro hv
      rw [shape, Set.mem_ofPred_eq] at hv
      obtain ⟨hvU, hvatom⟩ := hv
      refine ⟨v * u, ⟨(Uminus t).mul_mem hvU huU, ?_⟩, by simp⟩
      rw [hatom] at hvatom
      rw [show (v * u) • x = v • y from by rw [← huy, mul_smul]]
      exact hvatom
    · rintro ⟨s, hs, rfl⟩
      rw [shape, Set.mem_ofPred_eq] at hs ⊢
      obtain ⟨hsU, hsatom⟩ := hs
      refine ⟨(Uminus t).mul_mem hsU ((Uminus t).inv_mem huU), ?_⟩
      have hsy : (s * u⁻¹) • y = s • x := by
        rw [← huy, ← mul_smul, mul_assoc, inv_mul_cancel, mul_one]
      rw [hsy, hatom]
      exact hsatom
  refine ⟨?_, ?_, ?_⟩
  · rw [hatom, ← hleaf]
    exact horb
  · refine ⟨{g : SL3 | g * u ∈ O}, hOopen.preimage (by fun_prop), ?_⟩
    rw [hshape, hOshape]
    ext v
    constructor
    · rintro ⟨w, ⟨hwO, hwU⟩, hwv⟩
      refine ⟨?_, ?_⟩
      · show v * u ∈ O
        have hvu : v * u = w := by rw [← hwv]; simp
        rw [hvu]
        exact hwO
      · rw [← hwv]
        exact (Uminus t).mul_mem hwU ((Uminus t).inv_mem huU)
    · rintro ⟨hvuO, hvU⟩
      exact ⟨v * u, ⟨by simpa using hvuO, (Uminus t).mul_mem hvU huU⟩, by simp⟩
  · exact ⟨C, fun z hz w hw i j => hCb z (hatom ▸ hz) w hw i j⟩


/-! ## The assembly: refining by the orbit-avoidance set -/

/-- The set of points whose whole forward orbit avoids `N`. -/
def orbitAvoids (t : Fin 3 → ℝ) (N : Set X3) : Set X3 :=
  {x | ∀ k : ℕ, ((fun z : X3 => aDiag t • z)^[k]) x ∉ N}

theorem orbitAvoids_subset_compl (t : Fin 3 → ℝ) (N : Set X3) :
    orbitAvoids t N ⊆ Nᶜ := by
  intro x hx
  simpa using hx 0

theorem compl_orbitAvoids (t : Fin 3 → ℝ) (N : Set X3) :
    (orbitAvoids t N)ᶜ
      = ⋃ k : ℕ, ((fun z : X3 => aDiag t • z)^[k]) ⁻¹' N := by
  ext x
  simp only [Set.mem_compl_iff, orbitAvoids, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage,
    not_forall, not_not]

theorem measurableSet_orbitAvoids (t : Fin 3 → ℝ) {N : Set X3} (hN : MeasurableSet N) :
    MeasurableSet (orbitAvoids t N) := by
  have hcont : ∀ k : ℕ, Measurable ((fun z : X3 => aDiag t • z)^[k]) := fun k =>
    ((continuous_const_smul (aDiag t)).iterate k).measurable
  have : orbitAvoids t N = (⋃ k : ℕ, ((fun z : X3 => aDiag t • z)^[k]) ⁻¹' N)ᶜ := by
    rw [← compl_orbitAvoids, compl_compl]
  rw [this]
  exact (MeasurableSet.iUnion fun k => hN.preimage (hcont k)).compl

/-- The refinement of a partition by the pair `(B, Bᶜ)`, `B = orbitAvoids t N`: the index
`Nat.pair n 0` carries `P n ∩ B`, the index `Nat.pair n 1` carries `P n \ B`, and every other
index the empty set. -/
def refineByOrbitAvoids (t : Fin 3 → ℝ) (P : ℕ → Set X3) (N : Set X3) : ℕ → Set X3 :=
  fun k => if (Nat.unpair k).2 = 0 then (P (Nat.unpair k).1 ∩ orbitAvoids t N) else (if (Nat.unpair k).2 = 1 then (P (Nat.unpair k).1 \ orbitAvoids t N) else ∅)

theorem refine_apply_zero {t : Fin 3 → ℝ} {P : ℕ → Set X3} {N : Set X3} (n : ℕ) :
    refineByOrbitAvoids t P N (Nat.pair n 0) = P n ∩ orbitAvoids t N := by
  have h1 : (Nat.unpair (Nat.pair n 0)).1 = n := by rw [Nat.unpair_pair]
  have h2 : (Nat.unpair (Nat.pair n 0)).2 = 0 := by rw [Nat.unpair_pair]
  simp only [refineByOrbitAvoids, h1, h2, ↓reduceIte]

theorem refine_apply_one {t : Fin 3 → ℝ} {P : ℕ → Set X3} {N : Set X3} (n : ℕ) :
    refineByOrbitAvoids t P N (Nat.pair n 1) = P n \ orbitAvoids t N := by
  have h1 : (Nat.unpair (Nat.pair n 1)).1 = n := by rw [Nat.unpair_pair]
  have h2 : (Nat.unpair (Nat.pair n 1)).2 = 1 := by rw [Nat.unpair_pair]
  simp only [refineByOrbitAvoids, h1, h2, if_neg (by norm_num : ¬ (1:ℕ) = 0), ↓reduceIte]

theorem refine_apply_other {t : Fin 3 → ℝ} {P : ℕ → Set X3} {N : Set X3} {n j : ℕ}
    (h0 : j ≠ 0) (h1 : j ≠ 1) : refineByOrbitAvoids t P N (Nat.pair n j) = ∅ := by
  have h1' : (Nat.unpair (Nat.pair n j)).1 = n := by rw [Nat.unpair_pair]
  have h2' : (Nat.unpair (Nat.pair n j)).2 = j := by rw [Nat.unpair_pair]
  simp only [refineByOrbitAvoids, h1', h2', if_neg h0, if_neg h1]

theorem refine_apply_of_zero {t : Fin 3 → ℝ} {P : ℕ → Set X3} {N : Set X3} {k : ℕ}
    (h : (Nat.unpair k).2 = 0) :
    refineByOrbitAvoids t P N k = P (Nat.unpair k).1 ∩ orbitAvoids t N := by
  simp only [refineByOrbitAvoids, h, ↓reduceIte]

theorem refine_apply_of_one {t : Fin 3 → ℝ} {P : ℕ → Set X3} {N : Set X3} {k : ℕ}
    (h : (Nat.unpair k).2 = 1) :
    refineByOrbitAvoids t P N k = P (Nat.unpair k).1 \ orbitAvoids t N := by
  simp only [refineByOrbitAvoids, h, if_neg (by norm_num : ¬ (1:ℕ) = 0), ↓reduceIte]

theorem refine_apply_of_other {t : Fin 3 → ℝ} {P : ℕ → Set X3} {N : Set X3} {k : ℕ}
    (h0 : (Nat.unpair k).2 ≠ 0) (h1 : (Nat.unpair k).2 ≠ 1) :
    refineByOrbitAvoids t P N k = ∅ := by
  simp only [refineByOrbitAvoids, if_neg h0, if_neg h1]

theorem measurableSet_refineByOrbitAvoids {t : Fin 3 → ℝ} {P : ℕ → Set X3} {N : Set X3}
    (hmeas : ∀ n, MeasurableSet (P n)) (hN : MeasurableSet N) :
    ∀ k, MeasurableSet (refineByOrbitAvoids t P N k) := by
  intro k
  have hB : MeasurableSet (orbitAvoids t N) := measurableSet_orbitAvoids t hN
  have h2 : (Nat.unpair k).2 = 0 ∨ (Nat.unpair k).2 = 1 ∨ ((Nat.unpair k).2 ≠ 0 ∧
      (Nat.unpair k).2 ≠ 1) := by omega
  rcases h2 with h2 | h2 | h2
  · rw [refine_apply_of_zero h2]
    exact (hmeas _).inter hB
  · rw [refine_apply_of_one h2]
    exact (hmeas _).diff hB
  · rw [refine_apply_of_other h2.1 h2.2]
    exact MeasurableSet.empty

theorem iUnion_refineByOrbitAvoids {t : Fin 3 → ℝ} {P : ℕ → Set X3} {N : Set X3}
    (hcov : (⋃ n, P n) = Set.univ) :
    (⋃ k, refineByOrbitAvoids t P N k) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro x
  obtain ⟨n, hxn⟩ : ∃ n, x ∈ P n := by
    have h : x ∈ (⋃ n, P n) := by rw [hcov]; exact Set.mem_univ x
    simpa using h
  by_cases hx : x ∈ orbitAvoids t N
  · refine Set.mem_iUnion.mpr ⟨Nat.pair n 0, ?_⟩
    rw [refine_apply_zero]
    exact ⟨hxn, hx⟩
  · refine Set.mem_iUnion.mpr ⟨Nat.pair n 1, ?_⟩
    rw [refine_apply_one]
    exact ⟨hxn, hx⟩

theorem disjoint_refineByOrbitAvoids {t : Fin 3 → ℝ} {P : ℕ → Set X3} {N : Set X3}
    (hdisj : ∀ m n, m ≠ n → Disjoint (P m) (P n)) :
    ∀ m n, m ≠ n → Disjoint (refineByOrbitAvoids t P N m) (refineByOrbitAvoids t P N n) := by
  intro m n hmn
  by_cases hm0 : (Nat.unpair m).2 = 0
  · by_cases hn0 : (Nat.unpair n).2 = 0
    · have h1 : (Nat.unpair m).1 ≠ (Nat.unpair n).1 := by
        intro h
        exact hmn (by rw [← Nat.pair_unpair m, ← Nat.pair_unpair n, h, hm0, hn0])
      rw [refine_apply_of_zero hm0, refine_apply_of_zero hn0, Set.disjoint_left]
      intro a ha ha'
      exact Set.disjoint_left.mp (hdisj _ _ h1) ha.1 ha'.1
    · by_cases hn1 : (Nat.unpair n).2 = 1
      · rw [refine_apply_of_zero hm0, refine_apply_of_one hn1, Set.disjoint_left]
        intro a ha ha'
        exact ha'.2 ha.2
      · rw [refine_apply_of_zero hm0, refine_apply_of_other hn0 hn1]
        simp
  · by_cases hm1 : (Nat.unpair m).2 = 1
    · by_cases hn0 : (Nat.unpair n).2 = 0
      · rw [refine_apply_of_one hm1, refine_apply_of_zero hn0, Set.disjoint_left]
        intro a ha ha'
        exact ha.2 ha'.2
      · by_cases hn1 : (Nat.unpair n).2 = 1
        · have h1 : (Nat.unpair m).1 ≠ (Nat.unpair n).1 := by
            intro h
            exact hmn (by rw [← Nat.pair_unpair m, ← Nat.pair_unpair n, h, hm1, hn1])
          rw [refine_apply_of_one hm1, refine_apply_of_one hn1, Set.disjoint_left]
          intro a ha ha'
          exact Set.disjoint_left.mp (hdisj _ _ h1) ha.1 ha'.1
        · rw [refine_apply_of_one hm1, refine_apply_of_other hn0 hn1]
          simp
    · rw [refine_apply_of_other hm0 hm1]
      simp

theorem cellOf_refine_eq {t : Fin 3 → ℝ} {P : ℕ → Set X3} {N : Set X3}
    (hdisj : ∀ m n, m ≠ n → Disjoint (P m) (P n)) (hcov : (⋃ n, P n) = Set.univ)
    {x : X3} (hx : x ∈ orbitAvoids t N) :
    cellOf (refineByOrbitAvoids t P N) x = cellOf P x ∩ orbitAvoids t N := by
  have hk : x ∈ refineByOrbitAvoids t P N (Nat.pair (cellIdx P x) 0) := by
    rw [refine_apply_zero]
    exact ⟨mem_cellOf hcov x, hx⟩
  rw [cellOf_eq_of_mem (disjoint_refineByOrbitAvoids hdisj) hk, refine_apply_zero]
  rfl

theorem iterate_mem_orbitAvoids {t : Fin 3 → ℝ} {N : Set X3} {x : X3}
    (hx : x ∈ orbitAvoids t N) (j : ℕ) :
    ((fun z : X3 => aDiag t • z)^[j]) x ∈ orbitAvoids t N := by
  rw [orbitAvoids] at hx ⊢
  intro m
  rw [← Function.iterate_add_apply]
  exact hx (m + j)

theorem atom_refine_eq {t : Fin 3 → ℝ} {P : ℕ → Set X3} {N : Set X3}
    (hdisj : ∀ m n, m ≠ n → Disjoint (P m) (P n)) (hcov : (⋃ n, P n) = Set.univ)
    (hsub : ∀ x : X3, x ∉ N → atom (pastSigma t P) x ⊆ Nᶜ)
    {x : X3} (hx : x ∈ orbitAvoids t N) :
    atom (pastSigma t (refineByOrbitAvoids t P N)) x = atom (pastSigma t P) x := by
  have hdisj' := disjoint_refineByOrbitAvoids (t := t) (N := N) hdisj
  have hcov' := iUnion_refineByOrbitAvoids (t := t) (N := N) hcov
  refine Set.Subset.antisymm ?_ ?_
  · intro y hy
    rw [mem_atom_pastSigma_iff_cellOf hdisj hcov]
    intro j
    have h1 := (mem_atom_pastSigma_iff_cellOf hdisj' hcov').mp hy j
    rw [cellOf_refine_eq hdisj hcov (iterate_mem_orbitAvoids hx j)] at h1
    exact h1.1
  · intro y hy
    rw [mem_atom_pastSigma_iff_cellOf hdisj' hcov']
    intro j
    have h1 := (mem_atom_pastSigma_iff_cellOf hdisj hcov).mp hy j
    rw [cellOf_refine_eq hdisj hcov (iterate_mem_orbitAvoids hx j)]
    refine ⟨h1, ?_⟩
    rw [orbitAvoids]
    intro m
    have h5 : ((fun z : X3 => aDiag t • z)^[m]) (((fun z : X3 => aDiag t • z)^[j]) y) ∈
        atom (pastSigma t P) (((fun z : X3 => aDiag t • z)^[m + j]) x) := by
      have h6 : ((fun z : X3 => aDiag t • z)^[m]) (((fun z : X3 => aDiag t • z)^[j]) y)
          = ((fun z : X3 => aDiag t • z)^[m + j]) y :=
        (Function.iterate_add_apply (fun z : X3 => aDiag t • z) m j y).symm
      rw [h6]
      exact mem_atom_pastSigma_iterate hdisj hcov hy (m + j)
    have h4 : ((fun z : X3 => aDiag t • z)^[m + j]) x ∉ N := hx (m + j)
    exact hsub _ h4 h5

/-- **The assembly.**  Let `P` be a countable partition of `X₃`, `N` a null measurable set which is
a union of atoms of `pastSigma t P` (`hsub`) and outside which every point is a coding point
(`hgood`).  Then there is a partition `P'` and a set of indices `S` whose union is conull and
consists of coding points: take the refinement of `P` by the pair `(B, Bᶜ)`, where `B` is the set
of points whose whole orbit avoids `N`, and `S` the cells contained in `B`.  The refinement does
not change the past σ-algebra at the points of `B` (`atom_refine_eq`), and `B` is conull because
the orbit of a.e. point avoids the null set `N`. -/
theorem exists_coding_partition_of_null_atom_set
    {μ : Measure X3} [IsProbabilityMeasure μ] {t : Fin 3 → ℝ}
    {P : ℕ → Set X3} (hmeas : ∀ n, MeasurableSet (P n))
    (hdisj : ∀ m n, m ≠ n → Disjoint (P m) (P n)) (hcov : (⋃ n, P n) = Set.univ)
    (hmp : MeasurePreserving (fun x : X3 => aDiag t • x) μ μ)
    {N : Set X3} (hNmeas : MeasurableSet N) (hNnull : μ N = 0)
    (hsub : ∀ x : X3, x ∉ N → atom (pastSigma t P) x ⊆ Nᶜ)
    (hgood : ∀ x : X3, x ∉ N → IsCodingPoint t (pastSigma t P) x) :
    ∃ (P' : ℕ → Set X3) (S : Set ℕ),
      (∀ n, MeasurableSet (P' n)) ∧ (∀ m n, m ≠ n → Disjoint (P' m) (P' n)) ∧
      (⋃ n, P' n) = Set.univ ∧ μ (⋃ n ∈ S, P' n)ᶜ = 0 ∧
      (∀ x ∈ ⋃ n ∈ S, P' n, IsCodingPoint t (pastSigma t P') x) := by
  have hS : (⋃ k ∈ {k | refineByOrbitAvoids t P N k ⊆ orbitAvoids t N},
      refineByOrbitAvoids t P N k) = orbitAvoids t N := by
    refine Set.Subset.antisymm ?_ ?_
    · intro x hx
      obtain ⟨k, hxk⟩ := Set.mem_iUnion.mp hx
      obtain ⟨hkS, hxv⟩ := Set.mem_iUnion.mp hxk
      exact hkS hxv
    · intro x hx
      obtain ⟨n, hxn⟩ : ∃ n, x ∈ P n := by
        have h : x ∈ (⋃ n, P n) := by rw [hcov]; exact Set.mem_univ x
        simpa using h
      refine Set.mem_iUnion.mpr ⟨Nat.pair n 0, ?_⟩
      refine Set.mem_iUnion.mpr ⟨?_, ?_⟩
      · show refineByOrbitAvoids t P N (Nat.pair n 0) ⊆ orbitAvoids t N
        rw [refine_apply_zero]
        exact Set.inter_subset_right
      · rw [refine_apply_zero]
        exact ⟨hxn, hx⟩
  refine ⟨refineByOrbitAvoids t P N, {k | refineByOrbitAvoids t P N k ⊆ orbitAvoids t N},
    measurableSet_refineByOrbitAvoids hmeas hNmeas, disjoint_refineByOrbitAvoids hdisj,
    iUnion_refineByOrbitAvoids hcov, ?_, ?_⟩
  · rw [hS, compl_orbitAvoids]
    refine measure_iUnion_null fun k => ?_
    rw [(hmp.iterate k).measure_preimage hNmeas.nullMeasurableSet]
    exact hNnull
  · intro x hxS
    have hxB : x ∈ orbitAvoids t N := by rw [← hS]; exact hxS
    have hxN : x ∉ N := fun h => orbitAvoids_subset_compl t N hxB h
    have hatom := atom_refine_eq hdisj hcov hsub hxB
    obtain ⟨horb, hO, hC⟩ := hgood x hxN
    refine ⟨?_, ?_, ?_⟩
    · rw [hatom]
      exact horb
    · obtain ⟨O, hOopen, hOshape⟩ := hO
      exact ⟨O, hOopen, by rw [shape, hatom]; exact hOshape⟩
    · obtain ⟨C, hCb⟩ := hC
      refine ⟨C, fun y hy u hu i j => ?_⟩
      have hyP : y ∈ atom (pastSigma t P) x := by rwa [hatom] at hy
      have hyB : y ∈ orbitAvoids t N := by
        intro m
        have h3 : ((fun z : X3 => aDiag t • z)^[m]) y ∈
            atom (pastSigma t P) (((fun z : X3 => aDiag t • z)^[m]) x) :=
          mem_atom_pastSigma_iterate hdisj hcov hyP m
        exact hsub _ (hxB m) h3
      have hatomy : atom (pastSigma t (refineByOrbitAvoids t P N)) y
          = atom (pastSigma t P) y := atom_refine_eq hdisj hcov hsub hyB
      have hsh : shape (pastSigma t (refineByOrbitAvoids t P N)) (Uminus t) y
          = shape (pastSigma t P) (Uminus t) y := by
        simp only [shape, Set.mem_ofPred_eq, Set.mem_setOf_eq, hatomy]
      rw [hsh] at hu
      exact hCb y hyP u hu i j
