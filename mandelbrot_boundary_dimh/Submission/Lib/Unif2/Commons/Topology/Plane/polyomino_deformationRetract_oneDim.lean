import Mathlib
import Submission.Lib.Unif2.Commons.Topology.Plane.exists_fold_unitSq
import Submission.Lib.Unif2.Commons.Topology.Plane.exists_cwComplex_of_finset_segments
import Submission.Lib.Unif2.Commons.Topology.Plane.exists_homotopyEquiv_subgraph_oneDimCW_of_dyadic_subcomplex

open Set
open scoped Topology

noncomputable section

namespace Commons.Topology.Plane

abbrev uI : Set ℝ := Set.Icc (0 : ℝ) 1

/-- The closed unit square of the integer lattice at `p`. -/
def unitSqAt (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | (p.1 : ℝ) ≤ z.re ∧ z.re ≤ (p.1 : ℝ) + 1 ∧
           (p.2 : ℝ) ≤ z.im ∧ z.im ≤ (p.2 : ℝ) + 1}

/-- The open unit square of the integer lattice at `p`. -/
def openSqAt (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | (p.1 : ℝ) < z.re ∧ z.re < (p.1 : ℝ) + 1 ∧
           (p.2 : ℝ) < z.im ∧ z.im < (p.2 : ℝ) + 1}

/-- The open top edge of the unit square at `p`. -/
def openTopAt (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | (p.1 : ℝ) < z.re ∧ z.re < (p.1 : ℝ) + 1 ∧ z.im = (p.2 : ℝ) + 1}

/-- The `U`-shaped part (left, right and bottom edges) of the unit square at `p`. -/
def spineCore (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | (z.re = (p.1 : ℝ) ∧ (p.2 : ℝ) ≤ z.im ∧ z.im ≤ (p.2 : ℝ) + 1) ∨
           (z.re = (p.1 : ℝ) + 1 ∧ (p.2 : ℝ) ≤ z.im ∧ z.im ≤ (p.2 : ℝ) + 1) ∨
           (z.im = (p.2 : ℝ) ∧ (p.1 : ℝ) ≤ z.re ∧ z.re ≤ (p.1 : ℝ) + 1)}

/-- The part of the square at `p` that is removed by the folding step. -/
def badSet (p : ℤ × ℤ) : Set ℂ := openSqAt p ∪ openTopAt p

/-- The tall rectangle of the folding step at `p`. -/
def tallRect (p : ℤ × ℤ) : Set ℂ :=
  {z : ℂ | (p.1 : ℝ) < z.re ∧ z.re < (p.1 : ℝ) + 1 ∧
           (p.2 : ℝ) < z.im ∧ z.im < (p.2 : ℝ) + 2}

/-- The "spine" associated to the processed squares `A`: the union of the squares in `S` with the
interior and open top edge of every square of `A` removed. -/
def spineSet (S A : Finset (ℤ × ℤ)) : Set ℂ :=
  (⋃ p ∈ S, unitSqAt p) \ (⋃ p ∈ A, badSet p)

lemma mem_unitSqAt {p : ℤ × ℤ} {z : ℂ} :
    z ∈ unitSqAt p ↔ (p.1 : ℝ) ≤ z.re ∧ z.re ≤ (p.1 : ℝ) + 1 ∧
      (p.2 : ℝ) ≤ z.im ∧ z.im ≤ (p.2 : ℝ) + 1 := by
  simp [unitSqAt]

lemma mem_openSqAt {p : ℤ × ℤ} {z : ℂ} :
    z ∈ openSqAt p ↔ (p.1 : ℝ) < z.re ∧ z.re < (p.1 : ℝ) + 1 ∧
      (p.2 : ℝ) < z.im ∧ z.im < (p.2 : ℝ) + 1 := by
  simp [openSqAt]

lemma mem_openTopAt {p : ℤ × ℤ} {z : ℂ} :
    z ∈ openTopAt p ↔ (p.1 : ℝ) < z.re ∧ z.re < (p.1 : ℝ) + 1 ∧ z.im = (p.2 : ℝ) + 1 := by
  simp [openTopAt]

lemma mem_spineCore {p : ℤ × ℤ} {z : ℂ} :
    z ∈ spineCore p ↔
      (z.re = (p.1 : ℝ) ∧ (p.2 : ℝ) ≤ z.im ∧ z.im ≤ (p.2 : ℝ) + 1) ∨
      (z.re = (p.1 : ℝ) + 1 ∧ (p.2 : ℝ) ≤ z.im ∧ z.im ≤ (p.2 : ℝ) + 1) ∨
      (z.im = (p.2 : ℝ) ∧ (p.1 : ℝ) ≤ z.re ∧ z.re ≤ (p.1 : ℝ) + 1) := by
  simp [spineCore]

lemma mem_tallRect {p : ℤ × ℤ} {z : ℂ} :
    z ∈ tallRect p ↔ (p.1 : ℝ) < z.re ∧ z.re < (p.1 : ℝ) + 1 ∧
      (p.2 : ℝ) < z.im ∧ z.im < (p.2 : ℝ) + 2 := by
  simp [tallRect]

lemma mem_foldUnitSq {u : ℂ} :
    u ∈ foldUnitSq ↔ 0 ≤ u.re ∧ u.re ≤ 1 ∧ 0 ≤ u.im ∧ u.im ≤ 1 := by
  simp [foldUnitSq]

lemma mem_foldUnitSqU {u : ℂ} :
    u ∈ foldUnitSqU ↔ (u.re = 0 ∧ 0 ≤ u.im ∧ u.im ≤ 1) ∨
      (u.re = 1 ∧ 0 ≤ u.im ∧ u.im ≤ 1) ∨ (u.im = 0 ∧ 0 ≤ u.re ∧ u.re ≤ 1) := by
  simp [foldUnitSqU]

/-- The lattice point `p` as a complex number. -/
def pc (p : ℤ × ℤ) : ℂ := (p.1 : ℂ) + (p.2 : ℂ) * Complex.I

lemma pc_re (p : ℤ × ℤ) : (pc p).re = (p.1 : ℝ) := by simp [pc]
lemma pc_im (p : ℤ × ℤ) : (pc p).im = (p.2 : ℝ) := by simp [pc]

lemma sub_pc_add (p : ℤ × ℤ) (u : ℂ) : pc p + u - pc p = u := by ring

lemma add_sub_pc (p : ℤ × ℤ) (z : ℂ) : pc p + (z - pc p) = z := by ring

lemma unitSqAt_eq_image (p : ℤ × ℤ) :
    unitSqAt p = (fun z : ℂ => pc p + z) '' foldUnitSq := by
  ext z
  constructor
  · intro hz
    rw [mem_unitSqAt] at hz
    refine ⟨z - pc p, ?_, ?_⟩
    · rw [mem_foldUnitSq, Complex.sub_re, Complex.sub_im, pc_re, pc_im]
      exact ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2.1],
        by linarith [hz.2.2.2]⟩
    · show pc p + (z - pc p) = z; ring
  · rintro ⟨u, hu, rfl⟩
    rw [mem_unitSqAt, mem_foldUnitSq] at *
    rw [Complex.add_re, Complex.add_im, pc_re, pc_im]
    exact ⟨by linarith [hu.1], by linarith [hu.2.1], by linarith [hu.2.2.1],
      by linarith [hu.2.2.2]⟩

lemma spineCore_eq_image (p : ℤ × ℤ) :
    spineCore p = (fun z : ℂ => pc p + z) '' foldUnitSqU := by
  ext z
  constructor
  · intro hz
    rw [mem_spineCore] at hz
    refine ⟨z - pc p, ?_, ?_⟩
    · rw [mem_foldUnitSqU, Complex.sub_re, Complex.sub_im, pc_re, pc_im]
      rcases hz with ⟨hre, hlo, hhi⟩ | ⟨hre, hlo, hhi⟩ | ⟨him, hlo, hhi⟩
      · left; exact ⟨by linarith, by linarith, by linarith⟩
      · right; left; exact ⟨by linarith, by linarith, by linarith⟩
      · right; right; exact ⟨by linarith, by linarith, by linarith⟩
    · show pc p + (z - pc p) = z; ring
  · rintro ⟨u, hu, rfl⟩
    rw [mem_spineCore, mem_foldUnitSqU] at *
    rw [Complex.add_re, Complex.add_im, pc_re, pc_im]
    rcases hu with ⟨hre, hlo, hhi⟩ | ⟨hre, hlo, hhi⟩ | ⟨him, hlo, hhi⟩
    · left; exact ⟨by linarith, by linarith, by linarith⟩
    · right; left; exact ⟨by linarith, by linarith, by linarith⟩
    · right; right; exact ⟨by linarith, by linarith, by linarith⟩

/-- The data of one folding step of a unit lattice square: a (global) map `φ` folding the square
onto its `U`-shaped part, and a homotopy `H` deforming the identity to `φ`, fixing the `U` and
the complement of the square. -/
structure FoldData (p : ℤ × ℤ) where
  φ : ℂ → ℂ
  H : ℂ × ↥uI → ℂ
  contφ : ContinuousOn φ (unitSqAt p)
  contH : ContinuousOn H (unitSqAt p ×ˢ Set.univ)
  Hmem : ∀ z ∈ unitSqAt p, ∀ t : ↥uI, H (z, t) ∈ unitSqAt p
  H0 : ∀ z ∈ unitSqAt p, H (z, (0 : ↥uI)) = z
  H1 : ∀ z ∈ unitSqAt p, H (z, (1 : ↥uI)) = φ z
  φmem : ∀ z ∈ unitSqAt p, φ z ∈ spineCore p
  φfix : ∀ z ∈ spineCore p, φ z = z
  φout : ∀ z ∉ unitSqAt p, φ z = z
  Hfix : ∀ z ∈ spineCore p, ∀ t : ↥uI, H (z, t) = z
  Hout : ∀ z ∉ unitSqAt p, ∀ t : ↥uI, H (z, t) = z

lemma mem_foldUnitSq_sub {p : ℤ × ℤ} {z : ℂ} (hz : z ∈ unitSqAt p) :
    z - pc p ∈ foldUnitSq := by
  rw [mem_unitSqAt] at hz
  rw [mem_foldUnitSq, Complex.sub_re, Complex.sub_im, pc_re, pc_im]
  exact ⟨by linarith [hz.1], by linarith [hz.2.1], by linarith [hz.2.2.1],
    by linarith [hz.2.2.2]⟩

lemma add_pc_mem_unitSqAt {p : ℤ × ℤ} {u : ℂ} (hu : u ∈ foldUnitSq) :
    pc p + u ∈ unitSqAt p := by
  rw [mem_foldUnitSq] at hu
  rw [mem_unitSqAt, Complex.add_re, Complex.add_im, pc_re, pc_im]
  exact ⟨by linarith [hu.1], by linarith [hu.2.1], by linarith [hu.2.2.1],
    by linarith [hu.2.2.2]⟩

lemma mem_unitSqAt_of_sub_mem {p : ℤ × ℤ} {z : ℂ} (h : z - pc p ∈ foldUnitSq) :
    z ∈ unitSqAt p := by
  have := add_pc_mem_unitSqAt (p := p) h
  rwa [add_sub_pc] at this

/-- A folding step for the square at `p`, obtained from the fold of the standard unit square by
translation. -/
noncomputable def foldDataOfUnit (p : ℤ × ℤ) (φ : ℂ → ℂ) (H : ℂ × ↥uI → ℂ)
    (hcontφ : ContinuousOn φ foldUnitSq) (hcontH : ContinuousOn H (foldUnitSq ×ˢ Set.univ))
    (hHmem : ∀ z ∈ foldUnitSq, ∀ t : ↥uI, H (z, t) ∈ foldUnitSq)
    (hH0 : ∀ z ∈ foldUnitSq, H (z, (0 : ↥uI)) = z)
    (hH1 : ∀ z ∈ foldUnitSq, H (z, (1 : ↥uI)) = φ z)
    (hφmem : ∀ z ∈ foldUnitSq, φ z ∈ foldUnitSqU)
    (hφfix : ∀ z ∈ foldUnitSqU, φ z = z)
    (hφout : ∀ z ∉ foldUnitSq, φ z = z)
    (hHfix : ∀ z ∈ foldUnitSqU, ∀ t : ↥uI, H (z, t) = z)
    (hHout : ∀ z ∉ foldUnitSq, ∀ t : ↥uI, H (z, t) = z) : FoldData p where
  φ := fun z => pc p + φ (z - pc p)
  H := fun q => pc p + H (q.1 - pc p, q.2)
  contφ := by
    have h1 : ContinuousOn (fun z : ℂ => z - pc p) (unitSqAt p) :=
      (continuous_id.sub continuous_const).continuousOn
    exact continuous_const.continuousOn.add
      (hcontφ.comp h1 (fun z hz => mem_foldUnitSq_sub hz))
  contH := by
    have h1 : ContinuousOn (fun q : ℂ × ↥uI => (q.1 - pc p, q.2))
        (unitSqAt p ×ˢ (Set.univ : Set ↥uI)) :=
      ((continuous_fst.sub continuous_const).prodMk continuous_snd).continuousOn
    have h2 : MapsTo (fun q : ℂ × ↥uI => (q.1 - pc p, q.2))
        (unitSqAt p ×ˢ (Set.univ : Set ↥uI)) (foldUnitSq ×ˢ (Set.univ : Set ↥uI)) := by
      rintro ⟨z, t⟩ ⟨hz, -⟩
      exact ⟨mem_foldUnitSq_sub hz, Set.mem_univ _⟩
    exact continuous_const.continuousOn.add (hcontH.comp h1 h2)
  Hmem := by
    intro z hz t
    exact add_pc_mem_unitSqAt (hHmem (z - pc p) (mem_foldUnitSq_sub hz) t)
  H0 := by
    intro z hz
    rw [hH0 (z - pc p) (mem_foldUnitSq_sub hz), add_sub_pc]
  H1 := by
    intro z hz
    rw [hH1 (z - pc p) (mem_foldUnitSq_sub hz)]
  φmem := by
    intro z hz
    rw [spineCore_eq_image]
    exact ⟨φ (z - pc p), hφmem (z - pc p) (mem_foldUnitSq_sub hz), rfl⟩
  φfix := by
    intro z hz
    rw [spineCore_eq_image] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    rw [sub_pc_add, hφfix u hu]
  φout := by
    intro z hz
    have hz' : z - pc p ∉ foldUnitSq := fun h => hz (mem_unitSqAt_of_sub_mem h)
    rw [hφout _ hz', add_sub_pc]
  Hfix := by
    intro z hz t
    rw [spineCore_eq_image] at hz
    obtain ⟨u, hu, rfl⟩ := hz
    rw [sub_pc_add, hHfix u hu t]
  Hout := by
    intro z hz t
    have hz' : z - pc p ∉ foldUnitSq := fun h => hz (mem_unitSqAt_of_sub_mem h)
    rw [hHout _ hz' t, add_sub_pc]

theorem exists_foldData (p : ℤ × ℤ) : Nonempty (FoldData p) := by
  obtain ⟨φ, H, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
    Commons.Topology.Plane.exists_fold_unitSq
  exact ⟨foldDataOfUnit p φ H h1 h2 h3 h4 h5 h6 h7 h8 h9 h10⟩

/-- The ambient region of the polyomino: the union of all the lattice squares. -/
abbrev polyK (S : Finset (ℤ × ℤ)) : Set ℂ := ⋃ p ∈ S, unitSqAt p

/-- Clamping a real number to the unit interval. -/
def clamp01 (r : ℝ) : ↥uI :=
  ⟨max 0 (min r 1), le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩

lemma clamp01_coe (r : ℝ) : (clamp01 r : ℝ) = max 0 (min r 1) := rfl

lemma continuous_clamp01 : Continuous clamp01 := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_const.max (continuous_id.min continuous_const)

lemma clamp01_of_mem {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) : (clamp01 r : ℝ) = r := by
  rw [clamp01_coe, min_eq_left h1, max_eq_right h0]

lemma clamp01_one : clamp01 1 = (1 : ↥uI) := Subtype.ext (by rw [clamp01_of_mem] <;> norm_num)

lemma clamp01_zero : clamp01 0 = (0 : ↥uI) := Subtype.ext (by rw [clamp01_of_mem] <;> norm_num)

lemma spineSet_empty (S : Finset (ℤ × ℤ)) : spineSet S ∅ = polyK S := by
  rw [spineSet]
  simp

lemma spineCore_subset_unitSqAt (p : ℤ × ℤ) : spineCore p ⊆ unitSqAt p := by
  intro z hz
  rw [mem_spineCore] at hz
  rw [mem_unitSqAt]
  rcases hz with ⟨hre, hlo, hhi⟩ | ⟨hre, hlo, hhi⟩ | ⟨him, hlo, hhi⟩
  · exact ⟨le_of_eq hre.symm, by linarith [hre], hlo, hhi⟩
  · exact ⟨by linarith [hre], le_of_eq hre, hlo, hhi⟩
  · exact ⟨hlo, hhi, le_of_eq him.symm, by linarith [him]⟩

lemma spineCore_disjoint_badSet (p : ℤ × ℤ) :
    ∀ z ∈ spineCore p, z ∉ badSet p := by
  intro z hz hb
  rw [mem_spineCore] at hz
  rw [badSet, mem_union] at hb
  rcases hb with hb | hb
  · rw [mem_openSqAt] at hb
    rcases hz with ⟨hre, -, -⟩ | ⟨hre, -, -⟩ | ⟨him, -, -⟩
    · linarith [hre, hb.1]
    · linarith [hre, hb.2.1]
    · linarith [him, hb.2.2.1]
  · rw [mem_openTopAt] at hb
    rcases hz with ⟨hre, -, -⟩ | ⟨hre, -, -⟩ | ⟨him, -, -⟩
    · linarith [hre, hb.1]
    · linarith [hre, hb.2.1]
    · linarith [him, hb.2.2]

/-! ## Geometry of the lattice squares -/

lemma isClosed_unitSqAt (p : ℤ × ℤ) : IsClosed (unitSqAt p) := by
  have h : unitSqAt p = (fun z : ℂ => (z.re, z.im)) ⁻¹'
      (Set.Icc (p.1 : ℝ) ((p.1 : ℝ) + 1) ×ˢ Set.Icc (p.2 : ℝ) ((p.2 : ℝ) + 1)) := by
    ext z
    simp only [unitSqAt, mem_ofPred_eq, mem_preimage, mem_prod, mem_Icc]
    tauto
  rw [h]
  exact (isClosed_Icc.prod isClosed_Icc).preimage (by fun_prop)

lemma isOpen_tallRect (p : ℤ × ℤ) : IsOpen (tallRect p) := by
  have h : tallRect p = (fun z : ℂ => (z.re, z.im)) ⁻¹'
      (Set.Ioo (p.1 : ℝ) ((p.1 : ℝ) + 1) ×ˢ Set.Ioo (p.2 : ℝ) ((p.2 : ℝ) + 2)) := by
    ext z
    simp only [tallRect, mem_ofPred_eq, mem_preimage, mem_prod, mem_Ioo]
    tauto
  rw [h]
  exact (isOpen_Ioo.prod isOpen_Ioo).preimage (by fun_prop)

lemma openSqAt_subset_unitSqAt (p : ℤ × ℤ) : openSqAt p ⊆ unitSqAt p := by
  intro z hz
  rw [mem_openSqAt] at hz
  rw [mem_unitSqAt]
  exact ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩

lemma openTopAt_subset_unitSqAt (p : ℤ × ℤ) : openTopAt p ⊆ unitSqAt p := by
  intro z hz
  rw [mem_openTopAt] at hz
  rw [mem_unitSqAt]
  exact ⟨hz.1.le, hz.2.1.le, by linarith [hz.2.2], le_of_eq hz.2.2⟩

lemma badSet_subset_unitSqAt (p : ℤ × ℤ) : badSet p ⊆ unitSqAt p := by
  rintro z (hz | hz)
  · exact openSqAt_subset_unitSqAt p hz
  · exact openTopAt_subset_unitSqAt p hz

lemma openSqAt_subset_tallRect (p : ℤ × ℤ) : openSqAt p ⊆ tallRect p := by
  intro z hz
  rw [mem_openSqAt] at hz
  rw [mem_tallRect]
  exact ⟨hz.1, hz.2.1, hz.2.2.1, by linarith [hz.2.2.2]⟩

lemma openTopAt_subset_tallRect (p : ℤ × ℤ) : openTopAt p ⊆ tallRect p := by
  intro z hz
  rw [mem_openTopAt] at hz
  rw [mem_tallRect]
  exact ⟨hz.1, hz.2.1, by linarith [hz.2.2], by linarith [hz.2.2]⟩

lemma badSet_subset_tallRect (p : ℤ × ℤ) : badSet p ⊆ tallRect p := by
  intro z hz
  rw [badSet, mem_union] at hz
  rcases hz with hz | hz
  · exact openSqAt_subset_tallRect p hz
  · exact openTopAt_subset_tallRect p hz


/-- A unit lattice square meeting the open tall rectangle of `p` is the square at `p` or the one
directly above it. -/
lemma index_of_mem_unitSqAt_tallRect {p q : ℤ × ℤ} {z : ℂ}
    (hq : z ∈ unitSqAt q) (hN : z ∈ tallRect p) :
    q.1 = p.1 ∧ (q.2 = p.2 ∨ q.2 = p.2 + 1) := by
  rw [mem_unitSqAt] at hq
  rw [mem_tallRect] at hN
  have h1 : q.1 ≤ p.1 := by
    have h : (q.1 : ℝ) < (p.1 : ℝ) + 1 := by linarith [hq.1, hN.2.1]
    have h' : q.1 < p.1 + 1 := by exact_mod_cast h
    omega
  have h2 : p.1 ≤ q.1 := by
    have h : (p.1 : ℝ) < (q.1 : ℝ) + 1 := by linarith [hN.1, hq.2.1]
    have h' : p.1 < q.1 + 1 := by exact_mod_cast h
    omega
  have h3 : q.2 ≤ p.2 + 1 := by
    have h : (q.2 : ℝ) < (p.2 : ℝ) + 2 := by linarith [hq.2.2.1, hN.2.2.2]
    have h' : q.2 < p.2 + 2 := by exact_mod_cast h
    omega
  have h4 : p.2 ≤ q.2 := by
    have h : (p.2 : ℝ) < (q.2 : ℝ) + 1 := by linarith [hN.2.2.1, hq.2.2.2]
    have h' : p.2 < q.2 + 1 := by exact_mod_cast h
    omega
  exact ⟨by omega, by omega⟩

/-- A point of the spine lying in the tall rectangle of `p` must lie in the square at `p`, provided
that the square above `p` has been processed whenever it belongs to `S`. -/
lemma mem_unitSqAt_of_mem_spineSet_tallRect {S A : Finset (ℤ × ℤ)} {p : ℤ × ℤ} {z : ℂ}
    (hup : (p.1, p.2 + 1) ∈ S → (p.1, p.2 + 1) ∈ A)
    (hz : z ∈ spineSet S A) (hN : z ∈ tallRect p) : z ∈ unitSqAt p := by
  obtain ⟨hzK, hznot⟩ := hz
  obtain ⟨q, hqS, hzq⟩ := mem_iUnion₂.mp hzK
  obtain ⟨hq1, hq2 | hq2⟩ := index_of_mem_unitSqAt_tallRect hzq hN
  · rw [Prod.ext hq1 hq2] at hzq; exact hzq
  · rw [mem_tallRect] at hN
    by_cases him : z.im ≤ (p.2 : ℝ) + 1
    · rw [mem_unitSqAt]
      exact ⟨hN.1.le, hN.2.1.le, hN.2.2.1.le, him⟩
    · exfalso
      push Not at him
      have hqE : q = (p.1, p.2 + 1) := Prod.ext hq1 hq2
      have hqS' : (p.1, p.2 + 1) ∈ S := hqE ▸ hqS
      have hqA : q ∈ A := hqE.symm ▸ hup hqS'
      have hqmem : z ∈ unitSqAt q := hzq
      rw [mem_unitSqAt] at hqmem
      have hcast1 : (q.1 : ℝ) = (p.1 : ℝ) := by exact_mod_cast hq1
      have hcast2 : (q.2 : ℝ) = (p.2 : ℝ) + 1 := by
        rw [hq2]; push_cast; ring
      have hbad : z ∈ badSet q := by
        rcases lt_or_eq_of_le hqmem.2.2.2 with hlt | heq
        · left
          rw [mem_openSqAt]
          exact ⟨by linarith [hN.1, hcast1], by linarith [hN.2.1, hcast1],
            by linarith [hN.2.2.1, hcast2], hlt⟩
        · right
          rw [mem_openTopAt]
          exact ⟨by linarith [hN.1, hcast1], by linarith [hN.2.1, hcast1], heq⟩
      exact hznot (mem_iUnion₂.mpr ⟨q, hqA, hbad⟩)

lemma openSqAt_inter_unitSqAt {p q : ℤ × ℤ} {z : ℂ}
    (hq : z ∈ openSqAt q) (hp : z ∈ unitSqAt p) : q = p := by
  rw [mem_openSqAt] at hq
  rw [mem_unitSqAt] at hp
  have h1 : q.1 ≤ p.1 := by
    have h : (q.1 : ℝ) < (p.1 : ℝ) + 1 := by linarith [hq.1, hp.2.1]
    have h' : q.1 < p.1 + 1 := by exact_mod_cast h
    omega
  have h2 : p.1 ≤ q.1 := by
    have h : (p.1 : ℝ) < (q.1 : ℝ) + 1 := by linarith [hp.1, hq.2.1]
    have h' : p.1 < q.1 + 1 := by exact_mod_cast h
    omega
  have h3 : q.2 ≤ p.2 := by
    have h : (q.2 : ℝ) < (p.2 : ℝ) + 1 := by linarith [hq.2.2.1, hp.2.2.2]
    have h' : q.2 < p.2 + 1 := by exact_mod_cast h
    omega
  have h4 : p.2 ≤ q.2 := by
    have h : (p.2 : ℝ) < (q.2 : ℝ) + 1 := by linarith [hp.2.2.1, hq.2.2.2]
    have h' : p.2 < q.2 + 1 := by exact_mod_cast h
    omega
  exact Prod.ext (by omega) (by omega)

lemma openTopAt_inter_unitSqAt {p q : ℤ × ℤ} {z : ℂ}
    (hq : z ∈ openTopAt q) (hp : z ∈ unitSqAt p) : q = p ∨ q = (p.1, p.2 - 1) := by
  rw [mem_openTopAt] at hq
  rw [mem_unitSqAt] at hp
  have hq1 : q.1 = p.1 := by
    have ha : (q.1 : ℝ) < (p.1 : ℝ) + 1 := by linarith [hq.1, hp.2.1]
    have hb : (p.1 : ℝ) < (q.1 : ℝ) + 1 := by linarith [hp.1, hq.2.1]
    have ha' : q.1 < p.1 + 1 := by exact_mod_cast ha
    have hb' : p.1 < q.1 + 1 := by exact_mod_cast hb
    omega
  have h5 : p.2 ≤ q.2 + 1 := by
    have h : (p.2 : ℝ) ≤ (q.2 : ℝ) + 1 := by linarith [hp.2.2.1, hq.2.2]
    exact_mod_cast h
  have h6 : q.2 ≤ p.2 := by
    have h : (q.2 : ℝ) + 1 ≤ (p.2 : ℝ) + 1 := by linarith [hq.2.2, hp.2.2.2]
    have h' : q.2 + 1 ≤ p.2 + 1 := by exact_mod_cast h
    omega
  rcases eq_or_lt_of_le h5 with h | h
  · exact Or.inr (Prod.ext hq1 (by omega))
  · exact Or.inl (Prod.ext hq1 (by omega))

lemma badSet_inter_unitSqAt_eq_empty {p q : ℤ × ℤ} (h1 : q ≠ p) (h2 : q ≠ (p.1, p.2 - 1)) :
    badSet q ∩ unitSqAt p = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  rintro z ⟨hz | hz, hzp⟩
  · exact h1 (openSqAt_inter_unitSqAt hz hzp)
  · rcases openTopAt_inter_unitSqAt hz hzp with h | h
    · exact h1 h
    · exact h2 h

/-- A point of the square at `p` that is not removed lies in the `U`-shaped core. -/
lemma mem_spineCore_of_mem_unitSqAt_of_notMem_badSet {p : ℤ × ℤ} {z : ℂ}
    (hz : z ∈ unitSqAt p) (h : z ∉ badSet p) : z ∈ spineCore p := by
  rw [mem_unitSqAt] at hz
  rw [badSet, mem_union, not_or] at h
  obtain ⟨h1, h2⟩ := h
  rw [mem_openSqAt] at h1
  rw [mem_openTopAt] at h2
  rw [mem_spineCore]
  have key : z.re = (p.1 : ℝ) ∨ z.re = (p.1 : ℝ) + 1 ∨ z.im = (p.2 : ℝ) := by
    by_contra hc
    push Not at hc
    obtain ⟨hne1, hne2, hne3⟩ := hc
    have hlt1 : (p.1 : ℝ) < z.re := lt_of_le_of_ne hz.1 (Ne.symm hne1)
    have hlt2 : z.re < (p.1 : ℝ) + 1 := lt_of_le_of_ne hz.2.1 hne2
    have hlt3 : (p.2 : ℝ) < z.im := lt_of_le_of_ne hz.2.2.1 (Ne.symm hne3)
    rcases lt_or_eq_of_le hz.2.2.2 with h4 | h4
    · exact h1 ⟨hlt1, hlt2, hlt3, h4⟩
    · exact h2 ⟨hlt1, hlt2, h4⟩
  rcases key with h | h | h
  · exact Or.inl ⟨h, hz.2.2.1, hz.2.2.2⟩
  · exact Or.inr (Or.inl ⟨h, hz.2.2.1, hz.2.2.2⟩)
  · exact Or.inr (Or.inr ⟨h, hz.1, hz.2.1⟩)

/-! ## The spine sets -/

lemma spineSet_insert_eq (S A : Finset (ℤ × ℤ)) (p : ℤ × ℤ) :
    spineSet S (insert p A) = spineSet S A \ badSet p := by
  ext z
  simp only [spineSet, mem_sdiff, mem_iUnion, Finset.mem_insert]
  constructor
  · rintro ⟨hzK, hznot⟩
    refine ⟨⟨hzK, ?_⟩, ?_⟩
    · rintro ⟨q, hq, hzq⟩
      exact hznot ⟨q, Or.inr hq, hzq⟩
    · rintro hp
      exact hznot ⟨p, Or.inl rfl, hp⟩
  · rintro ⟨⟨hzK, hznotA⟩, hzp⟩
    refine ⟨hzK, ?_⟩
    rintro ⟨q, hq, hzq⟩
    rcases hq with hqe | hqA
    · rw [hqe] at hzq
      exact hzp hzq
    · exact hznotA ⟨q, hqA, hzq⟩

lemma spineSet_subset_union (S A : Finset (ℤ × ℤ)) :
    spineSet S A ⊆ ⋃ p ∈ S, unitSqAt p := fun _ hz => hz.1

lemma spineSet_antitone (S : Finset (ℤ × ℤ)) {A B : Finset (ℤ × ℤ)} (h : A ⊆ B) :
    spineSet S B ⊆ spineSet S A := by
  rintro z ⟨hzK, hzB⟩
  refine ⟨hzK, ?_⟩
  rw [mem_iUnion₂] at hzB ⊢
  rintro ⟨q, hqA, hzq⟩
  exact hzB ⟨q, h hqA, hzq⟩


/-! ## One step of the folding cascade -/

/-- The data produced by one step of the folding cascade: a deformation retraction of the current
spine into the spine with one more square removed. -/
structure PolyStepData (S A : Finset (ℤ × ℤ)) (p : ℤ × ℤ) where
  ρ : ContinuousMap (↥(spineSet S A) × ↥uI) ↥(polyK S)
  ρ0 : ∀ x : ↥(spineSet S A), ((ρ (x, (0 : ↥uI)) : ↥(polyK S)) : ℂ) = (x : ℂ)
  ρ1 : ∀ x : ↥(spineSet S A), ((ρ (x, (1 : ↥uI)) : ↥(polyK S)) : ℂ) ∈ spineSet S (insert p A)
  ρfixed : ∀ x : ↥(spineSet S A), ((x : ℂ)) ∈ spineSet S (insert p A) → ∀ t : ↥uI,
    ((ρ (x, t) : ↥(polyK S)) : ℂ) = (x : ℂ)

def stepDataOf (S A : Finset (ℤ × ℤ)) (p : ℤ × ℤ) (fd : FoldData p)
    (hpS : p ∈ S) (hpA : p ∉ A)
    (hval : ∀ q ∈ A, (q.1, q.2 + 1) ∈ S → (q.1, q.2 + 1) ∈ A)
    (hup : (p.1, p.2 + 1) ∈ S → (p.1, p.2 + 1) ∈ A) : PolyStepData S A p := by
  classical
  have hdn : (p.1, p.2 - 1) ∉ A := by
    intro hmem
    have hEq : ((p.1, p.2 - 1).1, (p.1, p.2 - 1).2 + 1) = p := Prod.ext rfl (by simp)
    have hps : ((p.1, p.2 - 1).1, (p.1, p.2 - 1).2 + 1) ∈ S := by rw [hEq]; exact hpS
    have hmem' := hval (p.1, p.2 - 1) hmem hps
    rw [hEq] at hmem'
    exact hpA hmem'
  have hnotRemoved : ∀ q ∈ A, ∀ z : ℂ, z ∈ unitSqAt p → z ∉ badSet q := by
    intro q hqA z hzp hzq
    have h1 : q ≠ p := fun h => hpA (h ▸ hqA)
    have h2 : q ≠ (p.1, p.2 - 1) := fun h => hdn (h ▸ hqA)
    have : z ∈ badSet q ∩ unitSqAt p := ⟨hzq, hzp⟩
    rw [badSet_inter_unitSqAt_eq_empty h1 h2] at this
    exact this
  have hmemH : ∀ z ∈ spineSet S A, ∀ t : ↥uI, fd.H (z, t) ∈ spineSet S A := by
    intro z hz t
    by_cases hzp : z ∈ unitSqAt p
    · refine ⟨?_, ?_⟩
      · rw [mem_iUnion₂]
        exact ⟨p, hpS, fd.Hmem z hzp t⟩
      · rw [mem_iUnion₂]
        rintro ⟨q, hqA, hzq⟩
        exact hnotRemoved q hqA _ (fd.Hmem z hzp t) hzq
    · rw [fd.Hout z hzp t]
      exact hz
  have hcont : Continuous (fun q : ↥(spineSet S A) × ↥uI => fd.H (q.1, q.2)) := by
    have hC1 : IsClosed {q : ↥(spineSet S A) × ↥uI | (q.1 : ℂ) ∈ unitSqAt p} :=
      IsClosed.preimage (continuous_subtype_val.comp continuous_fst) (isClosed_unitSqAt p)
    have hC2 : IsClosed {q : ↥(spineSet S A) × ↥uI | (q.1 : ℂ) ∉ tallRect p} :=
      IsClosed.preimage (continuous_subtype_val.comp continuous_fst)
        (isOpen_tallRect p).isClosed_compl
    have hcover : {q : ↥(spineSet S A) × ↥uI | (q.1 : ℂ) ∈ unitSqAt p} ∪
        {q : ↥(spineSet S A) × ↥uI | (q.1 : ℂ) ∉ tallRect p} = univ := by
      ext q
      simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]
      by_cases h : (q.1 : ℂ) ∈ tallRect p
      · exact Or.inl (mem_unitSqAt_of_mem_spineSet_tallRect hup q.1.2 h)
      · exact Or.inr h
    have h1 : ContinuousOn (fun q : ↥(spineSet S A) × ↥uI => fd.H (q.1, q.2))
        {q | (q.1 : ℂ) ∈ unitSqAt p} := by
      refine fd.contH.comp ?_ ?_
      · exact ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd).continuousOn
      · intro q hq; exact ⟨hq, mem_univ _⟩
    have heq2 : ∀ q ∈ {q : ↥(spineSet S A) × ↥uI | (q.1 : ℂ) ∉ tallRect p},
        fd.H (q.1, q.2) = (q.1 : ℂ) := by
      intro q hq
      by_cases h : (q.1 : ℂ) ∈ unitSqAt p
      · exact fd.Hfix _ (mem_spineCore_of_mem_unitSqAt_of_notMem_badSet h
          (fun hb => hq (badSet_subset_tallRect p hb))) q.2
      · exact fd.Hout _ h q.2
    have h2 : ContinuousOn (fun q : ↥(spineSet S A) × ↥uI => fd.H (q.1, q.2))
        {q | (q.1 : ℂ) ∉ tallRect p} :=
      ContinuousOn.congr ((continuous_subtype_val.comp continuous_fst).continuousOn) heq2
    have huni := h1.union_of_isClosed h2 hC1 hC2
    rw [hcover, continuousOn_univ] at huni
    exact huni
  refine ⟨⟨fun q => ⟨fd.H (q.1, q.2), spineSet_subset_union S A (hmemH q.1 q.1.2 q.2)⟩,
    Continuous.subtype_mk hcont _⟩, ?_, ?_, ?_⟩
  · intro x
    change fd.H ((x : ℂ), (0 : ↥uI)) = (x : ℂ)
    by_cases h : (x : ℂ) ∈ unitSqAt p
    · rw [fd.H0 _ h]
    · rw [fd.Hout _ h]
  · intro x
    change fd.H ((x : ℂ), (1 : ↥uI)) ∈ spineSet S (insert p A)
    by_cases h : (x : ℂ) ∈ unitSqAt p
    · rw [fd.H1 _ h]
      refine ⟨?_, ?_⟩
      · rw [mem_iUnion₂]
        exact ⟨p, hpS, spineCore_subset_unitSqAt p (fd.φmem _ h)⟩
      · rw [mem_iUnion₂]
        rintro ⟨q, hq, hzq⟩
        rcases Finset.mem_insert.mp hq with hqe | hqA
        · rw [hqe] at hzq
          exact spineCore_disjoint_badSet p (fd.φ (x : ℂ)) (fd.φmem _ h) hzq
        · exact hnotRemoved q hqA _ (spineCore_subset_unitSqAt p (fd.φmem _ h)) hzq
    · rw [fd.Hout _ h]
      obtain ⟨hK, hnotA⟩ := x.2
      refine ⟨hK, ?_⟩
      rw [mem_iUnion₂] at hnotA ⊢
      rintro ⟨q, hq, hzq⟩
      rcases Finset.mem_insert.mp hq with hqe | hqA
      · rw [hqe] at hzq
        exact h (badSet_subset_unitSqAt p hzq)
      · exact hnotA ⟨q, hqA, hzq⟩
  · intro x hx t
    change fd.H ((x : ℂ), t) = (x : ℂ)
    obtain ⟨hK, hnotA⟩ := hx
    rw [mem_iUnion₂] at hnotA
    by_cases h : (x : ℂ) ∈ unitSqAt p
    · exact fd.Hfix _ (mem_spineCore_of_mem_unitSqAt_of_notMem_badSet h
        (fun hb => hnotA ⟨p, Finset.mem_insert_self p A, hb⟩)) t
    · exact fd.Hout _ h t


/-! ## The folding cascade -/

/-- The order in which the squares are folded: larger `im` first, then smaller `re`. -/
def polySqKey (p : ℤ × ℤ) : Lex (ℤ × ℤ) := toLex (-p.2, p.1)

lemma sqKey_lt_down (p : ℤ × ℤ) : polySqKey p < polySqKey (p.1, p.2 - 1) := by
  simp only [polySqKey, Prod.Lex.toLex_lt_toLex]
  omega

/-- The polyomino deformation retracts onto the spine obtained by folding all its squares. -/
theorem exists_spine_retraction (S : Finset (ℤ × ℤ)) :
    ∃ Φ : ContinuousMap (↥(polyK S) × ↥uI) ↥(polyK S),
      (∀ x : ↥(polyK S), ((Φ (x, (0 : ↥uI)) : ↥(polyK S)) : ℂ) = (x : ℂ)) ∧
      (∀ x : ↥(polyK S), ((Φ (x, (1 : ↥uI)) : ↥(polyK S)) : ℂ) ∈ spineSet S S) ∧
      (∀ x : ↥(polyK S), ((x : ℂ)) ∈ spineSet S S → ∀ t : ↥uI,
        ((Φ (x, t) : ↥(polyK S)) : ℂ) = (x : ℂ)) := by
  classical
  have main : ∀ n : ℕ, ∀ A : Finset (ℤ × ℤ), A ⊆ S →
      (∀ q ∈ A, (q.1, q.2 + 1) ∈ S → (q.1, q.2 + 1) ∈ A) → A.card = n →
      ∃ Φ : ContinuousMap (↥(polyK S) × ↥uI) ↥(polyK S),
        (∀ x : ↥(polyK S), ((Φ (x, (0 : ↥uI)) : ↥(polyK S)) : ℂ) = (x : ℂ)) ∧
        (∀ x : ↥(polyK S), ((Φ (x, (1 : ↥uI)) : ↥(polyK S)) : ℂ) ∈ spineSet S A) ∧
        (∀ x : ↥(polyK S), ((x : ℂ)) ∈ spineSet S A → ∀ t : ↥uI,
          ((Φ (x, t) : ↥(polyK S)) : ℂ) = (x : ℂ)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro A hAS hval hcard
      rcases Finset.eq_empty_or_nonempty A with hemp | hne
      · rw [hemp]
        refine ⟨⟨fun q => q.1, continuous_fst⟩, ?_, ?_, ?_⟩
        · intro x; rfl
        · intro x
          rw [spineSet_empty]
          change (x : ℂ) ∈ polyK S
          exact x.2
        · intro x hx t; rfl
      · obtain ⟨p, hpA, hpmax⟩ := Finset.exists_max_image A polySqKey hne
        have hpS : p ∈ S := hAS hpA
        have hpErase : p ∉ A.erase p := Finset.notMem_erase p A
        have hEqA : insert p (A.erase p) = A := Finset.insert_erase hpA
        have hA' : A.erase p ⊆ S := fun q hq => hAS (Finset.mem_of_mem_erase hq)
        have hval' : ∀ q ∈ A.erase p, (q.1, q.2 + 1) ∈ S → (q.1, q.2 + 1) ∈ A.erase p := by
          intro q hq hqS
          have hqA : q ∈ A := Finset.mem_of_mem_erase hq
          have hmem : (q.1, q.2 + 1) ∈ A := hval q hqA hqS
          refine Finset.mem_erase.mpr ⟨?_, hmem⟩
          intro hpe
          have hqeq : q = (p.1, p.2 - 1) := by
            have h1 : q.1 = p.1 := by rw [← hpe]
            have h2 : q.2 + 1 = p.2 := by rw [← hpe]
            exact Prod.ext h1 (by omega)
          have hlt : polySqKey p < polySqKey q := by rw [hqeq]; exact sqKey_lt_down p
          exact absurd (hpmax q hqA) (not_le.mpr hlt)
        have hup' : (p.1, p.2 + 1) ∈ S → (p.1, p.2 + 1) ∈ A.erase p := by
          intro hpup
          have hmem : (p.1, p.2 + 1) ∈ A := hval p hpA hpup
          refine Finset.mem_erase.mpr ⟨?_, hmem⟩
          intro hpe
          have h2 : p.2 + 1 = p.2 := by
            have := congrArg Prod.snd hpe
            simpa only [Prod.snd] using this
          omega
        have hcard' : (A.erase p).card < n := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem hpA
        obtain ⟨Φ', hΦ'0, hΦ'1, hΦ'fix⟩ := ih (A.erase p).card hcard' (A.erase p) hA' hval' rfl
        obtain ⟨fd⟩ := exists_foldData p
        let sd := stepDataOf S (A.erase p) p fd hpS hpErase hval' hup'
        let Gfun : ↥(polyK S) → ↥(spineSet S (A.erase p)) :=
          fun x => ⟨((Φ' (x, (1 : ↥uI))) : ℂ), hΦ'1 x⟩
        have hGcont : Continuous Gfun :=
          Continuous.subtype_mk (f := fun x : ↥(polyK S) => ((Φ' (x, (1 : ↥uI))) : ℂ))
            (continuous_subtype_val.comp
              ((Φ'.continuous).comp (continuous_id.prodMk continuous_const)))
            (fun x => hΦ'1 x)
        let G : ContinuousMap (↥(polyK S)) (↥(spineSet S (A.erase p))) := ⟨Gfun, hGcont⟩
        let Φ : ↥(polyK S) × ↥uI → ↥(polyK S) := fun q =>
          if (q.2 : ℝ) ≤ 1/2 then Φ' (q.1, clamp01 (2 * (q.2 : ℝ)))
          else sd.ρ (G q.1, clamp01 (2 * (q.2 : ℝ) - 1))
        have hΦle : ∀ q : ↥(polyK S) × ↥uI, (q.2 : ℝ) ≤ 1/2 →
            Φ q = Φ' (q.1, clamp01 (2 * (q.2 : ℝ))) := by
          intro q hq; simp only [Φ]; rw [if_pos hq]
        have hΦgt : ∀ q : ↥(polyK S) × ↥uI, ¬ (q.2 : ℝ) ≤ 1/2 →
            Φ q = sd.ρ (G q.1, clamp01 (2 * (q.2 : ℝ) - 1)) := by
          intro q hq; simp only [Φ]; rw [if_neg hq]
        have hcont1 : Continuous (fun q : ↥(polyK S) × ↥uI =>
            Φ' (q.1, clamp01 (2 * (q.2 : ℝ)))) :=
          Φ'.continuous.comp (continuous_fst.prodMk (continuous_clamp01.comp
            (continuous_const.mul (continuous_subtype_val.comp continuous_snd))))
        have hcont2 : Continuous (fun q : ↥(polyK S) × ↥uI =>
            sd.ρ (G q.1, clamp01 (2 * (q.2 : ℝ) - 1))) :=
          sd.ρ.continuous.comp (((G.continuous).comp continuous_fst).prodMk (continuous_clamp01.comp
            ((continuous_const.mul (continuous_subtype_val.comp continuous_snd)).sub
              continuous_const)))
        have hagree : ∀ q : ↥(polyK S) × ↥uI, (q.2 : ℝ) = 1/2 →
            Φ' (q.1, clamp01 (2 * (q.2 : ℝ))) =
              sd.ρ (G q.1, clamp01 (2 * (q.2 : ℝ) - 1)) := by
          intro q hq
          rw [show (2 * (q.2 : ℝ) - 1) = 0 by rw [hq]; norm_num, clamp01_zero]
          rw [show (2 * (q.2 : ℝ)) = 1 by rw [hq]; norm_num, clamp01_one]
          refine Subtype.ext ?_
          rw [sd.ρ0 (G q.1)]
          rfl
        have hΦcont : Continuous Φ :=
          continuous_if_le (f := fun q : ↥(polyK S) × ↥uI => (q.2 : ℝ))
            (g := fun _ => (1/2 : ℝ))
            (f' := fun q => Φ' (q.1, clamp01 (2 * (q.2 : ℝ))))
            (g' := fun q => sd.ρ (G q.1, clamp01 (2 * (q.2 : ℝ) - 1)))
            (by fun_prop) (by fun_prop) hcont1.continuousOn hcont2.continuousOn hagree
        have hΦ0 : ∀ x : ↥(polyK S), ((Φ (x, (0 : ↥uI)) : ↥(polyK S)) : ℂ) = (x : ℂ) := by
          intro x
          rw [hΦle (x, (0 : ↥uI)) (by norm_num)]
          have hcl : clamp01 (2 * (((0 : ↥uI) : ℝ))) = (0 : ↥uI) := Subtype.ext (by
            rw [clamp01_of_mem] <;> norm_num)
          rw [hcl]
          exact hΦ'0 x
        have hΦ1 : ∀ x : ↥(polyK S),
            ((Φ (x, (1 : ↥uI)) : ↥(polyK S)) : ℂ) ∈ spineSet S A := by
          intro x
          rw [hΦgt (x, (1 : ↥uI)) (by norm_num)]
          have hcl : clamp01 (2 * (((1 : ↥uI) : ℝ)) - 1) = (1 : ↥uI) := Subtype.ext (by
            rw [clamp01_of_mem] <;> norm_num)
          rw [hcl]
          have := sd.ρ1 (G x)
          rwa [hEqA] at this
        have hΦfix : ∀ x : ↥(polyK S), ((x : ℂ)) ∈ spineSet S A → ∀ t : ↥uI,
            ((Φ (x, t) : ↥(polyK S)) : ℂ) = (x : ℂ) := by
          intro x hx t
          have hx' : (x : ℂ) ∈ spineSet S (insert p (A.erase p)) := by rw [hEqA]; exact hx
          have hxE : (x : ℂ) ∈ spineSet S (A.erase p) :=
            spineSet_antitone S (Finset.subset_insert p (A.erase p)) hx'
          by_cases ht : (t : ℝ) ≤ 1/2
          · rw [hΦle (x, t) ht]
            exact hΦ'fix x hxE _
          · rw [hΦgt (x, t) ht]
            have hGx : ((G x : ↥(spineSet S (A.erase p))) : ℂ) = (x : ℂ) :=
              hΦ'fix x hxE (1 : ↥uI)
            have hmem : ((G x : ↥(spineSet S (A.erase p))) : ℂ) ∈
                spineSet S (insert p (A.erase p)) := by
              rw [hGx]; exact hx'
            rw [sd.ρfixed (G x) hmem, hGx]
        exact ⟨⟨Φ, hΦcont⟩, hΦ0, hΦ1, hΦfix⟩
  exact main S.card S (Finset.Subset.refl S) (fun q hq hqS => hqS) rfl


/-! ## The spine as a finite union of segments -/

/-- The lattice vertices of the spine: the corners of the squares. -/
def spineVerticesZ (S : Finset (ℤ × ℤ)) : Finset (ℤ × ℤ) :=
  S.biUnion fun p =>
    {(p.1, p.2), (p.1 + 1, p.2), (p.1, p.2 + 1), (p.1 + 1, p.2 + 1)}

/-- The lattice edges of the spine: the vertical edges of the squares, together with the bottom
edges of the squares that have no square directly below them. -/
def spineEdgesZ (S : Finset (ℤ × ℤ)) : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
  (S.biUnion fun p =>
      {((p.1, p.2), (p.1, p.2 + 1)), ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1))})
    ∪ ((S.filter fun p => (p.1, p.2 - 1) ∉ S).image fun p => ((p.1, p.2), (p.1 + 1, p.2)))

/-- The vertices of the spine, as complex numbers. -/
def spineVerts (S : Finset (ℤ × ℤ)) : Finset ℂ := (spineVerticesZ S).image pc

/-- The edges of the spine, as pairs of complex numbers. -/
def spineEdges (S : Finset (ℤ × ℤ)) : Finset (ℂ × ℂ) :=
  (spineEdgesZ S).image fun e => (pc e.1, pc e.2)

lemma pc_injective : Function.Injective pc := by
  intro a b h
  have h1 : (a.1 : ℝ) = (b.1 : ℝ) := by rw [← pc_re a, ← pc_re b, h]
  have h2 : (a.2 : ℝ) = (b.2 : ℝ) := by rw [← pc_im a, ← pc_im b, h]
  exact Prod.ext (by exact_mod_cast h1) (by exact_mod_cast h2)

lemma mem_spineVerticesZ {S : Finset (ℤ × ℤ)} {q : ℤ × ℤ} :
    q ∈ spineVerticesZ S ↔ ∃ p ∈ S, q = (p.1, p.2) ∨ q = (p.1 + 1, p.2) ∨
      q = (p.1, p.2 + 1) ∨ q = (p.1 + 1, p.2 + 1) := by
  simp only [spineVerticesZ, Finset.mem_biUnion, Finset.mem_insert, Finset.mem_singleton]

lemma mem_spineVerts {S : Finset (ℤ × ℤ)} {q : ℤ × ℤ} :
    pc q ∈ spineVerts S ↔ ∃ p ∈ S, q = (p.1, p.2) ∨ q = (p.1 + 1, p.2) ∨
      q = (p.1, p.2 + 1) ∨ q = (p.1 + 1, p.2 + 1) := by
  rw [spineVerts, Finset.mem_image]
  constructor
  · rintro ⟨q', hq', hqq'⟩
    obtain ⟨p, hp, h⟩ := mem_spineVerticesZ.mp hq'
    exact ⟨p, hp, by rw [← pc_injective hqq']; exact h⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨q, mem_spineVerticesZ.mpr ⟨p, hp, h⟩, rfl⟩

lemma mem_spineEdgesZ {S : Finset (ℤ × ℤ)} {e : (ℤ × ℤ) × (ℤ × ℤ)} :
    e ∈ spineEdgesZ S ↔
      (∃ p ∈ S, e = ((p.1, p.2), (p.1, p.2 + 1)) ∨ e = ((p.1 + 1, p.2), (p.1 + 1, p.2 + 1))) ∨
      (∃ p ∈ S, (p.1, p.2 - 1) ∉ S ∧ e = ((p.1, p.2), (p.1 + 1, p.2))) := by
  simp only [spineEdgesZ, Finset.mem_union, Finset.mem_biUnion, Finset.mem_insert,
    Finset.mem_singleton, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩)
    · rcases h with h | h
      · exact Or.inl ⟨p, hp, Or.inl h⟩
      · exact Or.inl ⟨p, hp, Or.inr h⟩
    · exact Or.inr ⟨p, hp.1, hp.2, h.symm⟩
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, hsub, h⟩)
    · rcases h with h | h
      · exact Or.inl ⟨p, hp, Or.inl h⟩
      · exact Or.inl ⟨p, hp, Or.inr h⟩
    · exact Or.inr ⟨p, ⟨hp, hsub⟩, h.symm⟩

lemma mem_spineEdges {S : Finset (ℤ × ℤ)} {e : ℂ × ℂ} :
    e ∈ spineEdges S ↔
      (∃ p ∈ S, e = (pc (p.1, p.2), pc (p.1, p.2 + 1)) ∨
        e = (pc (p.1 + 1, p.2), pc (p.1 + 1, p.2 + 1))) ∨
      (∃ p ∈ S, (p.1, p.2 - 1) ∉ S ∧ e = (pc (p.1, p.2), pc (p.1 + 1, p.2))) := by
  rw [spineEdges, Finset.mem_image]
  constructor
  · rintro ⟨e', he', heq⟩
    rcases mem_spineEdgesZ.mp he' with ⟨p, hp, h | h⟩ | ⟨p, hp, hsub, h⟩
    · refine Or.inl ⟨p, hp, Or.inl ?_⟩
      rw [h] at heq; exact heq.symm
    · refine Or.inl ⟨p, hp, Or.inr ?_⟩
      rw [h] at heq; exact heq.symm
    · refine Or.inr ⟨p, hp, hsub, ?_⟩
      rw [h] at heq; exact heq.symm
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, hsub, h⟩)
    · rcases h with h | h
      · refine ⟨((p.1, p.2), (p.1, p.2 + 1)), mem_spineEdgesZ.mpr (Or.inl ⟨p, hp, Or.inl rfl⟩), ?_⟩
        rw [h]
      · refine ⟨((p.1 + 1, p.2), (p.1 + 1, p.2 + 1)),
            mem_spineEdgesZ.mpr (Or.inl ⟨p, hp, Or.inr rfl⟩), ?_⟩
        rw [h]
    · refine ⟨((p.1, p.2), (p.1 + 1, p.2)), mem_spineEdgesZ.mpr (Or.inr ⟨p, hp, hsub, rfl⟩), ?_⟩
      rw [h]


/-! ## Segments along the lattice -/

lemma lineMap_v_re (x y : ℤ) (t : ℝ) :
    ((1 - t) • pc (x, y) + t • pc (x, y + 1)).re = (x : ℝ) := by
  simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    pc_re, pc_im, zero_mul]
  ring

lemma lineMap_v_im (x y : ℤ) (t : ℝ) :
    ((1 - t) • pc (x, y) + t • pc (x, y + 1)).im = (y : ℝ) + t := by
  simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    pc_re, pc_im, zero_mul]
  push_cast
  ring

lemma lineMap_h_re (x y : ℤ) (t : ℝ) :
    ((1 - t) • pc (x, y) + t • pc (x + 1, y)).re = (x : ℝ) + t := by
  simp only [Complex.real_smul, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    pc_re, pc_im, zero_mul]
  push_cast
  ring

lemma lineMap_h_im (x y : ℤ) (t : ℝ) :
    ((1 - t) • pc (x, y) + t • pc (x + 1, y)).im = (y : ℝ) := by
  simp only [Complex.real_smul, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    pc_re, pc_im, zero_mul]
  ring

/-- The vertical unit segment is the set of points with the given real part and imaginary part in
the corresponding unit interval. -/
lemma polySeg_vertical (x y : ℤ) :
    segment ℝ (pc (x, y)) (pc (x, y + 1)) =
      {z : ℂ | z.re = (x : ℝ) ∧ (y : ℝ) ≤ z.im ∧ z.im ≤ (y : ℝ) + 1} := by
  ext z
  rw [segment_eq_image_lineMap (𝕜 := ℝ)]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [AffineMap.lineMap_apply_module]
    exact ⟨lineMap_v_re x y t, by rw [lineMap_v_im]; linarith [ht.1],
      by rw [lineMap_v_im]; linarith [ht.2]⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨z.im - (y : ℝ), ⟨by linarith, by linarith⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module]
    apply Complex.ext
    · rw [lineMap_v_re, h1]
    · rw [lineMap_v_im]; ring

/-- The horizontal unit segment is the set of points with the given imaginary part and real part
in the corresponding unit interval. -/
lemma polySeg_horizontal (x y : ℤ) :
    segment ℝ (pc (x, y)) (pc (x + 1, y)) =
      {z : ℂ | z.im = (y : ℝ) ∧ (x : ℝ) ≤ z.re ∧ z.re ≤ (x : ℝ) + 1} := by
  ext z
  rw [segment_eq_image_lineMap (𝕜 := ℝ)]
  constructor
  · rintro ⟨t, ht, rfl⟩
    rw [AffineMap.lineMap_apply_module]
    exact ⟨lineMap_h_im x y t, by rw [lineMap_h_re]; linarith [ht.1],
      by rw [lineMap_h_re]; linarith [ht.2]⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨z.re - (x : ℝ), ⟨by linarith, by linarith⟩, ?_⟩
    rw [AffineMap.lineMap_apply_module]
    apply Complex.ext
    · rw [lineMap_h_re]; ring
    · rw [lineMap_h_im, h1]


/-! ## The spine set as the union of its vertices and edges -/

lemma notMem_openSqAt_of_re_int {q : ℤ × ℤ} {z : ℂ} (h : ∃ n : ℤ, z.re = (n : ℝ)) :
    z ∉ openSqAt q := by
  obtain ⟨n, hn⟩ := h
  intro hb
  rw [mem_openSqAt] at hb
  have h1 : (q.1 : ℝ) < (n : ℝ) := by rw [← hn]; exact hb.1
  have h2 : (n : ℝ) < (q.1 : ℝ) + 1 := by rw [← hn]; exact hb.2.1
  have h1' : q.1 < n := by exact_mod_cast h1
  have h2' : n < q.1 + 1 := by exact_mod_cast h2
  omega

lemma notMem_openTopAt_of_re_int {q : ℤ × ℤ} {z : ℂ} (h : ∃ n : ℤ, z.re = (n : ℝ)) :
    z ∉ openTopAt q := by
  obtain ⟨n, hn⟩ := h
  intro hb
  rw [mem_openTopAt] at hb
  have h1 : (q.1 : ℝ) < (n : ℝ) := by rw [← hn]; exact hb.1
  have h2 : (n : ℝ) < (q.1 : ℝ) + 1 := by rw [← hn]; exact hb.2.1
  have h1' : q.1 < n := by exact_mod_cast h1
  have h2' : n < q.1 + 1 := by exact_mod_cast h2
  omega

lemma notMem_openSqAt_of_im_int {q : ℤ × ℤ} {z : ℂ} (h : ∃ n : ℤ, z.im = (n : ℝ)) :
    z ∉ openSqAt q := by
  obtain ⟨n, hn⟩ := h
  intro hb
  rw [mem_openSqAt] at hb
  have h1 : (q.2 : ℝ) < (n : ℝ) := by rw [← hn]; exact hb.2.2.1
  have h2 : (n : ℝ) < (q.2 : ℝ) + 1 := by rw [← hn]; exact hb.2.2.2
  have h1' : q.2 < n := by exact_mod_cast h1
  have h2' : n < q.2 + 1 := by exact_mod_cast h2
  omega

lemma notMem_badSet_of_re_int {q : ℤ × ℤ} {z : ℂ} (h : ∃ n : ℤ, z.re = (n : ℝ)) :
    z ∉ badSet q := by
  rw [badSet, mem_union, not_or]
  exact ⟨notMem_openSqAt_of_re_int h, notMem_openTopAt_of_re_int h⟩

lemma mem_spineSet_of_re_int {S : Finset (ℤ × ℤ)} {z : ℂ} {p : ℤ × ℤ} (hp : p ∈ S)
    (hre : z.re = (p.1 : ℝ) ∨ z.re = ((p.1 + 1 : ℤ) : ℝ))
    (him : (p.2 : ℝ) ≤ z.im ∧ z.im ≤ (p.2 : ℝ) + 1) : z ∈ spineSet S S := by
  have hre1 : z.re = (p.1 : ℝ) ∨ z.re = (p.1 : ℝ) + 1 := by
    rcases hre with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h]; push_cast; ring)
  refine ⟨?_, ?_⟩
  · rw [mem_iUnion₂]
    refine ⟨p, hp, ?_⟩
    rw [mem_unitSqAt]
    refine ⟨?_, ?_, him.1, him.2⟩
    · rcases hre1 with h | h
      · rw [h]
      · linarith
    · rcases hre1 with h | h
      · linarith
      · rw [h]
  · rw [mem_iUnion₂]
    rintro ⟨q, -, hb⟩
    rcases hre with h | h
    · exact notMem_badSet_of_re_int (q := q) ⟨p.1, h⟩ hb
    · exact notMem_badSet_of_re_int (q := q) ⟨p.1 + 1, h⟩ hb

lemma mem_spineSet_of_im_int {S : Finset (ℤ × ℤ)} {z : ℂ} {p : ℤ × ℤ} (hp : p ∈ S)
    (hbelow : (p.1, p.2 - 1) ∉ S) (him : z.im = (p.2 : ℝ))
    (hre : (p.1 : ℝ) ≤ z.re ∧ z.re ≤ (p.1 : ℝ) + 1) : z ∈ spineSet S S := by
  refine ⟨?_, ?_⟩
  · rw [mem_iUnion₂]
    refine ⟨p, hp, ?_⟩
    rw [mem_unitSqAt]
    exact ⟨hre.1, hre.2, by rw [him], by rw [him]; linarith⟩
  · rw [mem_iUnion₂]
    rintro ⟨q, hq, hb⟩
    rw [badSet, mem_union] at hb
    rcases hb with hb | hb
    · exact notMem_openSqAt_of_im_int (q := q) ⟨p.2, him⟩ hb
    · rw [mem_openTopAt] at hb
      have hq2 : q.2 = p.2 - 1 := by
        have h : (q.2 : ℝ) + 1 = (p.2 : ℝ) := by rw [← hb.2.2, him]
        have h' : q.2 + 1 = p.2 := by exact_mod_cast h
        omega
      have hq1 : q.1 = p.1 := by
        have h1 : (q.1 : ℝ) < (p.1 : ℝ) + 1 := by linarith [hb.1, hre.2]
        have h2 : (p.1 : ℝ) < (q.1 : ℝ) + 1 := by linarith [hre.1, hb.2.1]
        have h1' : q.1 < p.1 + 1 := by exact_mod_cast h1
        have h2' : p.1 < q.1 + 1 := by exact_mod_cast h2
        omega
      exact hbelow (by rw [← hq1, ← hq2]; exact hq)

lemma pc_mem_spineSet_of_vertex {S : Finset (ℤ × ℤ)} {q : ℤ × ℤ}
    (hq : ∃ p ∈ S, q = (p.1, p.2) ∨ q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1) ∨
      q = (p.1 + 1, p.2 + 1)) : pc q ∈ spineSet S S := by
  obtain ⟨p, hp, h | h | h | h⟩ := hq
  · refine ⟨?_, ?_⟩
    · rw [mem_iUnion₂]
      refine ⟨p, hp, ?_⟩
      rw [mem_unitSqAt, h, pc_re, pc_im]
      exact ⟨le_refl _, by norm_num, le_refl _, by norm_num⟩
    · rw [mem_iUnion₂]
      rintro ⟨q', -, hb⟩
      exact notMem_badSet_of_re_int (q := q') ⟨q.1, pc_re q⟩ hb
  · refine ⟨?_, ?_⟩
    · rw [mem_iUnion₂]
      refine ⟨p, hp, ?_⟩
      rw [mem_unitSqAt, h, pc_re, pc_im]
      push_cast
      exact ⟨by norm_num, le_refl _, le_refl _, by norm_num⟩
    · rw [mem_iUnion₂]
      rintro ⟨q', -, hb⟩
      exact notMem_badSet_of_re_int (q := q') ⟨q.1, pc_re q⟩ hb
  · refine ⟨?_, ?_⟩
    · rw [mem_iUnion₂]
      refine ⟨p, hp, ?_⟩
      rw [mem_unitSqAt, h, pc_re, pc_im]
      push_cast
      exact ⟨le_refl _, by norm_num, by norm_num, le_refl _⟩
    · rw [mem_iUnion₂]
      rintro ⟨q', -, hb⟩
      exact notMem_badSet_of_re_int (q := q') ⟨q.1, pc_re q⟩ hb
  · refine ⟨?_, ?_⟩
    · rw [mem_iUnion₂]
      refine ⟨p, hp, ?_⟩
      rw [mem_unitSqAt, h, pc_re, pc_im]
      push_cast
      exact ⟨by norm_num, le_refl _, by norm_num, le_refl _⟩
    · rw [mem_iUnion₂]
      rintro ⟨q', -, hb⟩
      exact notMem_badSet_of_re_int (q := q') ⟨q.1, pc_re q⟩ hb

theorem spineSet_eq_segments (S : Finset (ℤ × ℤ)) :
    (spineVerts S : Set ℂ) ∪ (⋃ e ∈ spineEdges S, segment ℝ e.1 e.2) = spineSet S S := by
  refine subset_antisymm ?_ ?_
  · rintro z (hz | hz)
    · rw [Finset.mem_coe] at hz
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hz
      exact pc_mem_spineSet_of_vertex (mem_spineVerticesZ.mp hq)
    · rw [mem_iUnion₂] at hz
      obtain ⟨e, he, hze⟩ := hz
      rcases mem_spineEdges.mp he with ⟨p, hp, h | h⟩ | ⟨p, hp, hsub, h⟩
      · rw [h] at hze
        rw [polySeg_vertical] at hze
        exact mem_spineSet_of_re_int hp (Or.inl hze.1) ⟨hze.2.1, hze.2.2⟩
      · rw [h] at hze
        rw [polySeg_vertical] at hze
        exact mem_spineSet_of_re_int hp (Or.inr hze.1) ⟨hze.2.1, hze.2.2⟩
      · rw [h] at hze
        rw [polySeg_horizontal] at hze
        exact mem_spineSet_of_im_int hp hsub hze.1 ⟨hze.2.1, hze.2.2⟩
  · intro z hz
    obtain ⟨hzK, hznot⟩ := hz
    rw [mem_iUnion₂] at hzK
    obtain ⟨p, hp, hzp⟩ := hzK
    have hbad : z ∉ badSet p := fun hb => hznot (mem_iUnion₂.mpr ⟨p, hp, hb⟩)
    have hcore := mem_spineCore_of_mem_unitSqAt_of_notMem_badSet hzp hbad
    rcases hcore with ⟨hre, hlo, hhi⟩ | ⟨hre, hlo, hhi⟩ | ⟨him, hlo, hhi⟩
    · right
      rw [mem_iUnion₂]
      refine ⟨(pc (p.1, p.2), pc (p.1, p.2 + 1)),
        mem_spineEdges.mpr (Or.inl ⟨p, hp, Or.inl rfl⟩), ?_⟩
      rw [polySeg_vertical]
      exact ⟨hre, hlo, hhi⟩
    · right
      rw [mem_iUnion₂]
      refine ⟨(pc (p.1 + 1, p.2), pc (p.1 + 1, p.2 + 1)),
        mem_spineEdges.mpr (Or.inl ⟨p, hp, Or.inr rfl⟩), ?_⟩
      rw [polySeg_vertical]
      refine ⟨?_, hlo, hhi⟩
      rw [hre]; push_cast; ring
    · by_cases hbelow : (p.1, p.2 - 1) ∈ S
      · left
        have hnotop : z ∉ openTopAt (p.1, p.2 - 1) := fun hb =>
          hznot (mem_iUnion₂.mpr ⟨(p.1, p.2 - 1), hbelow, by rw [badSet]; exact Or.inr hb⟩)
        rw [mem_openTopAt] at hnotop
        have hC : z.im = (((p.2 - 1 : ℤ)) : ℝ) + 1 := by
          rw [him]; push_cast; ring
        have hAB : ¬((p.1 : ℝ) < z.re ∧ z.re < (p.1 : ℝ) + 1) :=
          fun h => hnotop ⟨h.1, h.2, hC⟩
        rcases not_and_or.mp hAB with h | h
        · rw [not_lt] at h
          rw [Finset.mem_coe, spineVerts, Finset.mem_image]
          refine ⟨(p.1, p.2), mem_spineVerticesZ.mpr ⟨p, hp, Or.inl rfl⟩, ?_⟩
          apply Complex.ext
          · rw [pc_re]; exact (le_antisymm h hlo).symm
          · rw [pc_im]; exact him.symm
        · rw [not_lt] at h
          rw [Finset.mem_coe, spineVerts, Finset.mem_image]
          refine ⟨(p.1 + 1, p.2), mem_spineVerticesZ.mpr ⟨p, hp, Or.inr (Or.inl rfl)⟩, ?_⟩
          apply Complex.ext
          · rw [pc_re]; push_cast; exact (le_antisymm hhi h).symm
          · rw [pc_im]; exact him.symm
      · right
        rw [mem_iUnion₂]
        refine ⟨(pc (p.1, p.2), pc (p.1 + 1, p.2)),
          mem_spineEdges.mpr (Or.inr ⟨p, hp, hbelow, rfl⟩), ?_⟩
        rw [polySeg_horizontal]
        exact ⟨him, hlo, hhi⟩


/-! ## Disjointness of the unit lattice segments -/

lemma eq_or_eq_of_mem_unit_intervals {a b : ℤ} {x : ℝ} (h1 : (a : ℝ) ≤ x)
    (h2 : x ≤ (a : ℝ) + 1) (h3 : (b : ℝ) ≤ x) (h4 : x ≤ (b : ℝ) + 1) (hne : a ≠ b) :
    (x = (a : ℝ) + 1 ∧ b = a + 1) ∨ (x = (b : ℝ) + 1 ∧ a = b + 1) := by
  rcases lt_or_gt_of_ne hne with h | h
  · have hb : (a : ℝ) + 1 ≤ (b : ℝ) := by
      have h' : a + 1 ≤ b := by omega
      exact_mod_cast h'
    have hx : x = (a : ℝ) + 1 := le_antisymm h2 (by linarith)
    have hb2 : (b : ℝ) ≤ (a : ℝ) + 1 := by rw [← hx]; exact h3
    exact Or.inl ⟨hx, by exact_mod_cast (le_antisymm hb2 hb)⟩
  · have hb : (b : ℝ) + 1 ≤ (a : ℝ) := by
      have h' : b + 1 ≤ a := by omega
      exact_mod_cast h'
    have hx : x = (b : ℝ) + 1 := le_antisymm h4 (by linarith)
    have hb2 : (a : ℝ) ≤ (b : ℝ) + 1 := by rw [← hx]; exact h1
    exact Or.inr ⟨hx, by exact_mod_cast (le_antisymm hb2 hb)⟩

/-- Two distinct unit lattice segments meet only in common endpoints. -/
lemma unit_segment_meet {u v u' v' : ℤ × ℤ}
    (h : v = (u.1, u.2 + 1) ∨ v = (u.1 + 1, u.2))
    (h' : v' = (u'.1, u'.2 + 1) ∨ v' = (u'.1 + 1, u'.2))
    (hne : ¬(u = u' ∧ v = v')) :
    segment ℝ (pc u) (pc v) ∩ segment ℝ (pc u') (pc v') ⊆
      ({pc u, pc v} : Set ℂ) ∩ ({pc u', pc v'} : Set ℂ) := by
  intro z hz
  obtain ⟨hz1, hz2⟩ := hz
  rcases h with hv | hv <;> rcases h' with hv' | hv'
  · -- both edges vertical
    rw [hv, polySeg_vertical] at hz1
    rw [hv', polySeg_vertical] at hz2
    obtain ⟨hre1, hlo1, hhi1⟩ := hz1
    obtain ⟨hre2, hlo2, hhi2⟩ := hz2
    have h1 : u.1 = u'.1 := by
      have hh : (u.1 : ℝ) = (u'.1 : ℝ) := hre1.symm.trans hre2
      exact_mod_cast hh
    by_cases h2 : u.2 = u'.2
    · exact absurd ⟨Prod.ext h1 h2, by rw [hv, hv', h1, h2]⟩ hne
    · obtain ⟨hx, hb⟩ | ⟨hx, hb⟩ := eq_or_eq_of_mem_unit_intervals hlo1 hhi1 hlo2 hhi2 h2
      · have hb' : (u'.2 : ℝ) = (u.2 : ℝ) + 1 := by rw [hb]; push_cast; ring
        have hA : z ∈ ({pc u, pc v} : Set ℂ) := by
          refine Or.inr ?_
          rw [hv]
          apply Complex.ext
          · rw [pc_re]; exact hre1
          · rw [pc_im]; push_cast; exact hx
        have hB : z ∈ ({pc u', pc v'} : Set ℂ) := by
          refine Or.inl ?_
          apply Complex.ext
          · rw [pc_re]; rw [← h1]; exact hre1
          · rw [pc_im]; rw [hb']; exact hx
        exact ⟨hA, hB⟩
      · have hb' : (u.2 : ℝ) = (u'.2 : ℝ) + 1 := by rw [hb]; push_cast; ring
        have hA : z ∈ ({pc u, pc v} : Set ℂ) := by
          refine Or.inl ?_
          apply Complex.ext
          · rw [pc_re]; exact hre1
          · rw [pc_im]; rw [hb']; exact hx
        have hB : z ∈ ({pc u', pc v'} : Set ℂ) := by
          refine Or.inr ?_
          rw [hv']
          apply Complex.ext
          · rw [pc_re]; exact hre2
          · rw [pc_im]; push_cast; exact hx
        exact ⟨hA, hB⟩
  · -- first edge vertical, second horizontal
    rw [hv, polySeg_vertical] at hz1
    rw [hv', polySeg_horizontal] at hz2
    obtain ⟨hre1, hlo1, hhi1⟩ := hz1
    obtain ⟨him2, hlo2, hhi2⟩ := hz2
    have h2 : u'.2 = u.2 ∨ u'.2 = u.2 + 1 := by
      have ha : (u.2 : ℝ) ≤ (u'.2 : ℝ) := by rw [← him2]; exact hlo1
      have hb : (u'.2 : ℝ) ≤ (u.2 : ℝ) + 1 := by rw [← him2]; exact hhi1
      have ha' : u.2 ≤ u'.2 := by exact_mod_cast ha
      have hb' : u'.2 ≤ u.2 + 1 := by exact_mod_cast hb
      omega
    have h3 : u.1 = u'.1 ∨ u.1 = u'.1 + 1 := by
      have ha : (u'.1 : ℝ) ≤ (u.1 : ℝ) := by rw [← hre1]; exact hlo2
      have hb : (u.1 : ℝ) ≤ (u'.1 : ℝ) + 1 := by rw [← hre1]; exact hhi2
      have ha' : u'.1 ≤ u.1 := by exact_mod_cast ha
      have hb' : u.1 ≤ u'.1 + 1 := by exact_mod_cast hb
      omega
    have hA : z ∈ ({pc u, pc v} : Set ℂ) := by
      rcases h2 with h2 | h2
      · refine Or.inl ?_
        apply Complex.ext
        · rw [pc_re]; exact hre1
        · rw [pc_im]; rw [← h2]; exact him2
      · have h2' : (u'.2 : ℝ) = (u.2 : ℝ) + 1 := by rw [h2]; push_cast; ring
        refine Or.inr ?_
        rw [hv]
        apply Complex.ext
        · rw [pc_re]; exact hre1
        · rw [pc_im]; push_cast; rw [← h2']; exact him2
    have hB : z ∈ ({pc u', pc v'} : Set ℂ) := by
      rcases h3 with h3 | h3
      · refine Or.inl ?_
        apply Complex.ext
        · rw [pc_re]; rw [← h3]; exact hre1
        · rw [pc_im]; exact him2
      · have h3' : (u.1 : ℝ) = (u'.1 : ℝ) + 1 := by rw [h3]; push_cast; ring
        refine Or.inr ?_
        rw [hv']
        apply Complex.ext
        · rw [pc_re]; push_cast; rw [← h3']; exact hre1
        · rw [pc_im]; exact him2
    exact ⟨hA, hB⟩
  · -- first edge horizontal, second vertical
    rw [hv, polySeg_horizontal] at hz1
    rw [hv', polySeg_vertical] at hz2
    obtain ⟨him1, hlo1, hhi1⟩ := hz1
    obtain ⟨hre2, hlo2, hhi2⟩ := hz2
    have h2 : u.2 = u'.2 ∨ u.2 = u'.2 + 1 := by
      have ha : (u'.2 : ℝ) ≤ (u.2 : ℝ) := by rw [← him1]; exact hlo2
      have hb : (u.2 : ℝ) ≤ (u'.2 : ℝ) + 1 := by rw [← him1]; exact hhi2
      have ha' : u'.2 ≤ u.2 := by exact_mod_cast ha
      have hb' : u.2 ≤ u'.2 + 1 := by exact_mod_cast hb
      omega
    have h3 : u'.1 = u.1 ∨ u'.1 = u.1 + 1 := by
      have ha : (u.1 : ℝ) ≤ (u'.1 : ℝ) := by rw [← hre2]; exact hlo1
      have hb : (u'.1 : ℝ) ≤ (u.1 : ℝ) + 1 := by rw [← hre2]; exact hhi1
      have ha' : u.1 ≤ u'.1 := by exact_mod_cast ha
      have hb' : u'.1 ≤ u.1 + 1 := by exact_mod_cast hb
      omega
    have hA : z ∈ ({pc u, pc v} : Set ℂ) := by
      rcases h3 with h3 | h3
      · refine Or.inl ?_
        apply Complex.ext
        · rw [pc_re]; rw [← h3]; exact hre2
        · rw [pc_im]; exact him1
      · have h3' : (u'.1 : ℝ) = (u.1 : ℝ) + 1 := by rw [h3]; push_cast; ring
        refine Or.inr ?_
        rw [hv]
        apply Complex.ext
        · rw [pc_re]; push_cast; rw [← h3']; exact hre2
        · rw [pc_im]; exact him1
    have hB : z ∈ ({pc u', pc v'} : Set ℂ) := by
      rcases h2 with h2 | h2
      · refine Or.inl ?_
        apply Complex.ext
        · rw [pc_re]; exact hre2
        · rw [pc_im]; rw [← h2]; exact him1
      · have h2' : (u.2 : ℝ) = (u'.2 : ℝ) + 1 := by rw [h2]; push_cast; ring
        refine Or.inr ?_
        rw [hv']
        apply Complex.ext
        · rw [pc_re]; exact hre2
        · rw [pc_im]; push_cast; rw [← h2']; exact him1
    exact ⟨hA, hB⟩
  · -- both edges horizontal
    rw [hv, polySeg_horizontal] at hz1
    rw [hv', polySeg_horizontal] at hz2
    obtain ⟨him1, hlo1, hhi1⟩ := hz1
    obtain ⟨him2, hlo2, hhi2⟩ := hz2
    have h1 : u.2 = u'.2 := by
      have hh : (u.2 : ℝ) = (u'.2 : ℝ) := him1.symm.trans him2
      exact_mod_cast hh
    by_cases h2 : u.1 = u'.1
    · exact absurd ⟨Prod.ext h2 h1, by rw [hv, hv', h2, h1]⟩ hne
    · obtain ⟨hx, hb⟩ | ⟨hx, hb⟩ := eq_or_eq_of_mem_unit_intervals hlo1 hhi1 hlo2 hhi2 h2
      · have hb' : (u'.1 : ℝ) = (u.1 : ℝ) + 1 := by rw [hb]; push_cast; ring
        have hA : z ∈ ({pc u, pc v} : Set ℂ) := by
          refine Or.inr ?_
          rw [hv]
          apply Complex.ext
          · rw [pc_re]; push_cast; exact hx
          · rw [pc_im]; exact him1
        have hB : z ∈ ({pc u', pc v'} : Set ℂ) := by
          refine Or.inl ?_
          apply Complex.ext
          · rw [pc_re]; rw [hb']; exact hx
          · rw [pc_im]; rw [← h1]; exact him1
        exact ⟨hA, hB⟩
      · have hb' : (u.1 : ℝ) = (u'.1 : ℝ) + 1 := by rw [hb]; push_cast; ring
        have hA : z ∈ ({pc u, pc v} : Set ℂ) := by
          refine Or.inl ?_
          apply Complex.ext
          · rw [pc_re]; rw [hb']; exact hx
          · rw [pc_im]; rw [h1]; exact him2
        have hB : z ∈ ({pc u', pc v'} : Set ℂ) := by
          refine Or.inr ?_
          rw [hv']
          apply Complex.ext
          · rw [pc_re]; push_cast; exact hx
          · rw [pc_im]; exact him2
        exact ⟨hA, hB⟩


lemma spineEdges_endpoints (S : Finset (ℤ × ℤ)) {e : ℂ × ℂ} (he : e ∈ spineEdges S) :
    e.1 ∈ spineVerts S ∧ e.2 ∈ spineVerts S := by
  rcases mem_spineEdges.mp he with ⟨p, hp, h | h⟩ | ⟨p, hp, hsub, h⟩
  · rw [h]
    exact ⟨(mem_spineVerts (q := (p.1, p.2))).mpr ⟨p, hp, Or.inl rfl⟩,
      (mem_spineVerts (q := (p.1, p.2 + 1))).mpr ⟨p, hp, Or.inr (Or.inr (Or.inl rfl))⟩⟩
  · rw [h]
    exact ⟨(mem_spineVerts (q := (p.1 + 1, p.2))).mpr ⟨p, hp, Or.inr (Or.inl rfl)⟩,
      (mem_spineVerts (q := (p.1 + 1, p.2 + 1))).mpr ⟨p, hp, Or.inr (Or.inr (Or.inr rfl))⟩⟩
  · rw [h]
    exact ⟨(mem_spineVerts (q := (p.1, p.2))).mpr ⟨p, hp, Or.inl rfl⟩,
      (mem_spineVerts (q := (p.1 + 1, p.2))).mpr ⟨p, hp, Or.inr (Or.inl rfl)⟩⟩

lemma spineEdges_ne (S : Finset (ℤ × ℤ)) {e : ℂ × ℂ} (he : e ∈ spineEdges S) :
    e.1 ≠ e.2 := by
  rcases mem_spineEdges.mp he with ⟨p, hp, h | h⟩ | ⟨p, hp, hsub, h⟩
  · rw [h]
    intro hc
    have h2 : p.2 = p.2 + 1 := congrArg Prod.snd (pc_injective hc)
    omega
  · rw [h]
    intro hc
    have h2 : p.2 = p.2 + 1 := congrArg Prod.snd (pc_injective hc)
    omega
  · rw [h]
    intro hc
    have h2 : p.1 = p.1 + 1 := congrArg Prod.fst (pc_injective hc)
    omega

lemma spineEdges_disjoint (S : Finset (ℤ × ℤ)) {e e' : ℂ × ℂ} (he : e ∈ spineEdges S)
    (he' : e' ∈ spineEdges S) (hne : e ≠ e') :
    segment ℝ e.1 e.2 ∩ segment ℝ e'.1 e'.2 ⊆
      ({e.1, e.2} : Set ℂ) ∩ ({e'.1, e'.2} : Set ℂ) := by
  rw [spineEdges] at he he'
  obtain ⟨e₀, he₀, rfl⟩ := Finset.mem_image.mp he
  obtain ⟨e₁, he₁, he₁eq⟩ := Finset.mem_image.mp he'
  have htype₀ : e₀.2 = (e₀.1.1, e₀.1.2 + 1) ∨ e₀.2 = (e₀.1.1 + 1, e₀.1.2) := by
    rcases mem_spineEdgesZ.mp he₀ with ⟨p, hp, h | h⟩ | ⟨p, hp, hsub, h⟩
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr rfl
  have htype₁ : e₁.2 = (e₁.1.1, e₁.1.2 + 1) ∨ e₁.2 = (e₁.1.1 + 1, e₁.1.2) := by
    rcases mem_spineEdgesZ.mp he₁ with ⟨p, hp, h | h⟩ | ⟨p, hp, hsub, h⟩
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inl rfl
    · rw [h]; exact Or.inr rfl
  have hne' : ¬(e₀.1 = e₁.1 ∧ e₀.2 = e₁.2) := by
    intro hc
    apply hne
    rw [← he₁eq]
    exact Prod.ext (congrArg pc hc.1) (congrArg pc hc.2)
  rw [← he₁eq]
  exact unit_segment_meet htype₀ htype₁ hne'

lemma isClosed_polyK (S : Finset (ℤ × ℤ)) : IsClosed (polyK S) := by
  rw [polyK]
  exact isClosed_biUnion_finset (fun p _ => isClosed_unitSqAt p)

theorem polyomino_deformationRetract_oneDim (S : Finset (ℤ × ℤ)) :
    let K : Set ℂ := ⋃ p ∈ S, {z : ℂ | (p.1 : ℝ) ≤ z.re ∧ z.re ≤ (p.1 : ℝ) + 1 ∧
      (p.2 : ℝ) ≤ z.im ∧ z.im ≤ (p.2 : ℝ) + 1}
    ∃ (G : Set K) (hC : @Topology.CWComplex K _ G)
      (ρ : ContinuousMap (↥K × Set.Icc (0:ℝ) 1) ↥K),
      (∀ m : ℕ, 2 ≤ m → IsEmpty (@Topology.CWComplex.cell K _ G hC m)) ∧
      (∀ x, ρ (x, 0) = x) ∧
      (∀ x, ((ρ (x, 1) : ↥K) : ℂ) ∈ Subtype.val '' G) ∧
      (∀ x, ((x : ↥K) : ℂ) ∈ Subtype.val '' G → ∀ t, ρ (x, t) = x) := by
  classical
  dsimp only
  -- the CW structure on the spine
  obtain ⟨hCseg, hcellseg⟩ := exists_cwComplex_of_finset_segments (spineVerts S) (spineEdges S)
    (fun e he => spineEdges_endpoints S he) (fun e he => spineEdges_ne S he)
    (fun e he e' he' hne => spineEdges_disjoint S he he' hne)
  have hsub : ((spineVerts S : Set ℂ) ∪ (⋃ e ∈ spineEdges S, segment ℝ e.1 e.2)) ⊆ polyK S := by
    rw [spineSet_eq_segments S]
    exact spineSet_subset_union S S
  obtain ⟨hC', hcell'⟩ := exists_cwComplex_subtype_of_subset hsub (isClosed_polyK S) hCseg
  -- the deformation retraction
  obtain ⟨Φ, hΦ0, hΦ1, hΦfix⟩ := exists_spine_retraction S
  refine ⟨{z : ↥(polyK S) |
      (z : ℂ) ∈ (spineVerts S : Set ℂ) ∪ (⋃ e ∈ spineEdges S, segment ℝ e.1 e.2)},
    hC', Φ, ?_, ?_, ?_, ?_⟩
  · intro m hm
    exact hcell' m (hcellseg m hm)
  · intro x
    exact Subtype.ext (hΦ0 x)
  · intro x
    exact ⟨Φ (x, (1 : ↥uI)), by rw [spineSet_eq_segments S]; exact hΦ1 x, rfl⟩
  · intro x hx t
    obtain ⟨g, hg, hgx⟩ := hx
    have hg' : (g : ℂ) ∈ spineSet S S := by rw [← spineSet_eq_segments S]; exact hg
    have hxg : x = g := Subtype.ext hgx.symm
    rw [hxg]
    exact Subtype.ext (hΦfix g hg' t)

end Commons.Topology.Plane

end
