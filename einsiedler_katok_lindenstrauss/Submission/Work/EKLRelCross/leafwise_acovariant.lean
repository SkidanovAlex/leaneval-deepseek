import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.covariant_shape
import Submission.Work.EKLRelCross.acexp_flower
import Submission.Work.EKLRelCross.leafwise_luzin
import Submission.Work.EKLRelCross.per_t_covariance
import Submission.Work.EKLRelCross.covariance_bad_measurable

/-!
# `Work.EKLRelCross.leafwise_acovariant` — (U7) of the frozen EKL contract

The `A`-covariance of a leafwise-measure system (EKL (4), Pisa 7.16/7.17), the second half of
the frozen contract `P_Leafwise`.

`IsLeafwise` does *not* relate `ν x` to `ν (aDiag t • x)`; the bridge is EKL (4) = Pisa 7.16:

* for **each fixed** `t`, the covariance holds for `μ`-a.e. `x`.  Pisa 7.17 gives it on the
  *shape* of a plaque algebra (`Work.EKLRelCross.covariant_shape`), because `aDiag t` normalises
  `U` and hence transports plaque algebras (`MSAlg.translate`, `isPlaqueAlgebra_translate` below);
  a flower family (Pisa 6.15) whose atoms contain arbitrarily large plaques
  (`Work.EKLRelCross.acexp_flower`) upgrades it to the full measure identity
  (`Work.EKLRelCross.per_t_covariance`, delegated);
* the exceptional `μ`-null set in Pisa 7.16 depends on `t`, whereas the contract asks for a
  *single* conull `X''`.  This is the Fubini upgrade proved here: the set of bad pairs
  `(x, t)` is measurable (`Work.EKLRelCross.covariance_bad_measurable`, delegated) and has null
  sections, hence is null for `μ ⊗ Leb`; the covariance constants compose along the flow
  (`Cov_comp`), so at a pair `(x, t)` with `x, aDiag t • x` in the a.e.-in-`t` set one composes the
  covariances at `(x, t + s)` and `(aDiag t • x, s)` for a suitable `s`
  (`acov_all_t_of_per_t`), cancelling the push-forward by the conjugation by `aDiag s`.

`leafwise_acovariant_of_pieces` is the resulting assembly, and `leafwise_acovariant` is the
frozen contract clause (U7).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract

set_option warn.classDefReducibility false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

/-! ## A wrapper for σ-algebras on `X₃`

A σ-algebra occurring as a local hypothesis of a statement is wrapped, because Lean's type class
search prefers such a hypothesis over the global instance when it looks for an instance of
`MeasurableSpace X₃` (the capture hazard recorded in `EKLContract/NOTES.md`). -/

/-- Wrapper for a σ-algebra on `X₃`. -/
structure MSAlg where
  m : MeasurableSpace X3

/-- The σ-algebra transported along `Φ y = aDiag t • y`, cut to `Φ ⁻¹' Z`. -/
def MSAlg.translate (S : MSAlg) (t : Fin 3 → ℝ) (Z : Set X3) : MSAlg :=
  ⟨MeasurableSpace.comap (fun y : X3 => aDiag t • y) S.m ⊔
    MeasurableSpace.generateFrom {(fun y : X3 => aDiag t • y) ⁻¹' Z}⟩

/-! ## Elementary algebra of the diagonal flow -/

/-- `(aDiag t)⁻¹ = aDiag (-t)`. -/
theorem aDiag_inv_aDiag (t : Fin 3 → ℝ) : (aDiag t)⁻¹ = aDiag (-t) :=
  inv_eq_of_mul_eq_one_left (by rw [aDiag_add, neg_add_cancel, aDiag_zero])

theorem aDiag_smul_cancel (t : Fin 3 → ℝ) (y : X3) : aDiag (-t) • (aDiag t • y) = y := by
  rw [aDiag_smul_mul, neg_add_cancel, aDiag_zero, one_smul]

theorem aDiag_smul_cancel' (t : Fin 3 → ℝ) (y : X3) : aDiag t • (aDiag (-t) • y) = y := by
  rw [aDiag_smul_mul, add_neg_cancel, aDiag_zero, one_smul]

/-- A single term of a sum of nonnegative reals is at most the sum. -/
theorem le_sum_univ {ι : Type*} [Fintype ι] {f : ι → ℝ} (h : ∀ i, 0 ≤ f i) (i : ι) :
    f i ≤ ∑ j, f j :=
  Finset.single_le_sum (f := f) (fun j _ => h j) (Finset.mem_univ i)

/-- The entry formula for conjugation by a diagonal matrix. -/
theorem aDiag_conj_entry (t : Fin 3 → ℝ) (w : SL3) (i j : Fin 3) :
    ((aDiag t * w * (aDiag t)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j =
      Real.exp (t i - t j) * (((w : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j) := by
  have hcoe : ((aDiag t * w * (aDiag t)⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) =
      (Matrix.diagonal (fun i => Real.exp (t i - (∑ j, t j) / 3))) *
        ((w : SL3) : Matrix (Fin 3) (Fin 3) ℝ) *
        (Matrix.diagonal (fun i => Real.exp ((-t) i - (∑ j, (-t) j) / 3))) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, aDiag_inv_aDiag]
    rfl
  rw [hcoe, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have h1 : ((-t) j - (∑ k, (-t) k) / 3) = -(t j - (∑ k, t k) / 3) := by
    simp only [Pi.neg_apply, Finset.sum_neg_distrib]
    ring
  rw [h1]
  set x : ℝ := ((w : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j with hx
  have h2 : Real.exp (t i - (∑ k, t k) / 3) * (x * Real.exp (-(t j - (∑ k, t k) / 3)))
      = Real.exp (t i - (∑ k, t k) / 3) * Real.exp (-(t j - (∑ k, t k) / 3)) * x := by ring
  rw [mul_assoc, h2, ← Real.exp_add]
  congr 1
  ring

/-- The image of a set of matrices under conjugation by `aDiag t`. -/
def conjD (t : Fin 3 → ℝ) (S : Set SL3) : Set SL3 :=
  (fun g => aDiag t * g * (aDiag t)⁻¹) '' S

theorem mem_conjD {t : Fin 3 → ℝ} {S : Set SL3} {g : SL3} :
    g ∈ conjD t S ↔ aDiag (-t) * g * (aDiag (-t))⁻¹ ∈ S := by
  rw [conjD, Set.mem_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have h1 : aDiag (-t) * (aDiag t * w * (aDiag t)⁻¹) * (aDiag (-t))⁻¹ = w := by
      rw [← aDiag_inv_aDiag (t := t)]; group
    rw [h1]; exact hw
  · intro hg
    refine ⟨aDiag (-t) * g * (aDiag (-t))⁻¹, hg, ?_⟩
    rw [← aDiag_inv_aDiag (t := t)]; group

theorem conjD_subset {t : Fin 3 → ℝ} {S T : Set SL3} (h : S ⊆ T) : conjD t S ⊆ conjD t T :=
  fun g ⟨w, hw, hgw⟩ => ⟨w, h hw, hgw⟩

/-- Conjugating a bounded set of matrices keeps it bounded. -/
theorem conjD_entries_le {t : Fin 3 → ℝ} {S : Set SL3} {C : ℝ}
    (hS : S.Nonempty) (h : ∀ g ∈ S, ∀ i j, |g i j| ≤ C) :
    ∃ C' : ℝ, ∀ g ∈ conjD t S, ∀ i j, |g i j| ≤ C' := by
  classical
  obtain ⟨w₀, hw₀⟩ := hS
  refine ⟨C * (∑ i : Fin 3, ∑ j : Fin 3, |Real.exp (t i - t j)|), ?_⟩
  rintro g ⟨w, hw, rfl⟩ i j
  rw [aDiag_conj_entry, abs_mul]
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (h w₀ hw₀ 0 0)
  have hE1 : |Real.exp (t i - t j)| ≤ ∑ j' : Fin 3, |Real.exp (t i - t j')| :=
    le_sum_univ (f := fun j' : Fin 3 => |Real.exp (t i - t j')|) (fun _ => abs_nonneg _) j
  have hE2 : (∑ j' : Fin 3, |Real.exp (t i - t j')|) ≤
      ∑ i' : Fin 3, ∑ j' : Fin 3, |Real.exp (t i' - t j')| :=
    le_sum_univ (f := fun i' : Fin 3 => ∑ j' : Fin 3, |Real.exp (t i' - t j')|)
      (fun _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) i
  have hE := le_trans hE1 hE2
  calc |Real.exp (t i - t j)| * |((w : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j|
      ≤ |Real.exp (t i - t j)| * C := mul_le_mul_of_nonneg_left (h w hw i j) (abs_nonneg _)
    _ ≤ (∑ i : Fin 3, ∑ j : Fin 3, |Real.exp (t i - t j)|) * C :=
        mul_le_mul_of_nonneg_right hE hC0
    _ = C * (∑ i : Fin 3, ∑ j : Fin 3, |Real.exp (t i - t j)|) := by ring

/-- The set of matrices `g` with `aDiag t * g * (aDiag t)⁻¹ ∈ O` is open for `O` open. -/
theorem isOpen_conjD_preimage {t : Fin 3 → ℝ} {O : Set SL3} (hO : IsOpen O) :
    IsOpen {g : SL3 | aDiag t * g * (aDiag t)⁻¹ ∈ O} :=
  hO.preimage (((continuous_const.mul continuous_id).mul continuous_const))

/-! ## The transport of plaque algebras -/

/-- A set measurable for a sub-σ-algebra of the Borel one is Borel. -/
theorem measurableSet_of_le_borel {S : MSAlg} (h : S.m ≤ borel X3) {s : Set X3}
    (hs : MeasurableSet[S.m] s) : MeasurableSet s :=
  MeasurableSpace.le_def.mp h s hs

/-- The transported σ-algebra is contained in the Borel σ-algebra. -/
theorem translate_le {t : Fin 3 → ℝ} {Z : Set X3} {S : MSAlg} {b : Set (Set X3)}
    (hbm : S.m = MeasurableSpace.generateFrom b)
    (hb : ∀ B ∈ b, MeasurableSet[borel X3] B)
    (hZ : MeasurableSet[borel X3] Z) :
    (S.translate t Z).m ≤ borel X3 := by
  rw [MSAlg.translate, hbm, MeasurableSpace.comap_generateFrom,
    MeasurableSpace.generateFrom_sup_generateFrom]
  refine MeasurableSpace.generateFrom_le ?_
  rintro A (⟨B, hB, rfl⟩ | hA)
  · exact hb B hB |>.preimage (continuous_const_smul _).measurable
  · rw [Set.mem_singleton_iff] at hA
    rw [hA]
    exact hZ.preimage (continuous_const_smul _).measurable

/-- The transported σ-algebra is countably generated. -/
theorem translate_countablyGenerated {t : Fin 3 → ℝ} {Z : Set X3} {S : MSAlg}
    (h : ∃ b : Set (Set X3), b.Countable ∧ S.m = MeasurableSpace.generateFrom b) :
    ∃ b : Set (Set X3), b.Countable ∧ (S.translate t Z).m = MeasurableSpace.generateFrom b := by
  obtain ⟨b, hbc, hbm⟩ := h
  refine ⟨(Set.image (Set.preimage (fun y : X3 => aDiag t • y)) b) ∪
    {((fun y : X3 => aDiag t • y) ⁻¹' Z)}, ?_, ?_⟩
  · exact hbc.image (Set.preimage (fun y : X3 => aDiag t • y)) |>.union (Set.countable_singleton _)
  · rw [MSAlg.translate, hbm, MeasurableSpace.comap_generateFrom,
      MeasurableSpace.generateFrom_sup_generateFrom]

theorem measurableSet_translateZ {t : Fin 3 → ℝ} {Z : Set X3} {S : MSAlg} :
    MeasurableSet[(S.translate t Z).m] ((fun y : X3 => aDiag t • y) ⁻¹' Z) :=
  MeasurableSpace.le_def.mp le_sup_right _ (MeasurableSpace.measurableSet_generateFrom (Set.mem_singleton _))


/-- The atom of the transported σ-algebra at a point of the transported set. -/
theorem atom_translate {t : Fin 3 → ℝ} {Z : Set X3} {S : MSAlg} {b : Set (Set X3)}
    (hbm : S.m = MeasurableSpace.generateFrom b) {x : X3}
    (hx : x ∈ (fun y : X3 => aDiag t • y) ⁻¹' Z)
    (hsub : atom S.m (aDiag t • x) ⊆ Z) :
    atom (S.translate t Z).m x = (fun y : X3 => aDiag t • y) ⁻¹' (atom S.m (aDiag t • x)) := by
  have hgen : (S.translate t Z).m = MeasurableSpace.generateFrom
      ((Set.image (Set.preimage (fun y : X3 => aDiag t • y)) b) ∪
        {((fun y : X3 => aDiag t • y) ⁻¹' Z)}) := by
    rw [MSAlg.translate, hbm, MeasurableSpace.comap_generateFrom,
      MeasurableSpace.generateFrom_sup_generateFrom]
  have hxmem : aDiag t • x ∈ Z := hx
  ext y
  have key : (y ∈ atom (S.translate t Z).m x) ↔
      ∀ A ∈ (Set.image (Set.preimage (fun y : X3 => aDiag t • y)) b) ∪
        {((fun y : X3 => aDiag t • y) ⁻¹' Z)}, (y ∈ A ↔ x ∈ A) := by
    rw [hgen, mem_atom_iff_pattern]
  have key2 : ((fun y : X3 => aDiag t • y) y ∈ atom S.m ((fun y : X3 => aDiag t • y) x)) ↔
      ∀ B ∈ b, ((fun y : X3 => aDiag t • y) y ∈ B ↔ (fun y : X3 => aDiag t • y) x ∈ B) := by
    rw [hbm, mem_atom_iff_pattern]
  simp only [Set.mem_preimage]
  rw [key, key2]
  constructor
  · intro h B hB
    exact h (Set.preimage ((fun y : X3 => aDiag t • y)) B) (Set.mem_union_left _ ⟨B, hB, rfl⟩)
  · intro h A hA
    rw [Set.mem_union, Set.mem_image, Set.mem_singleton_iff] at hA
    rcases hA with ⟨B, hB, rfl⟩ | hA
    · exact h B hB
    · rw [hA]
      exact ⟨fun _ => hxmem, fun _ => hsub (by rw [hbm, mem_atom_iff_pattern]; exact h)⟩

/-- Conjugation by `aDiag t` is compatible with intersecting a set with `U`. -/
theorem conjD_inter_U {U : Subgroup SL3} (hU : IsHoro U) (t : Fin 3 → ℝ) (O : Set SL3) :
    conjD t (O ∩ (U : Set SL3)) = conjD t O ∩ (U : Set SL3) := by
  ext g
  simp only [Set.mem_inter_iff]
  constructor
  · rintro ⟨v, ⟨hvO, hvU⟩, rfl⟩
    exact ⟨⟨v, hvO, rfl⟩, hU.2.1 t v hvU⟩
  · rintro ⟨⟨v, hvO, rfl⟩, hgU⟩
    have hvU : v ∈ U := by
      have h := hU.2.1 (-t) (aDiag t * v * (aDiag t)⁻¹) hgU
      have heq : aDiag (-t) * (aDiag t * v * (aDiag t)⁻¹) * (aDiag (-t))⁻¹ = v := by
        rw [← aDiag_inv_aDiag t]
        group
      rwa [heq] at h
    exact ⟨v, ⟨hvO, hvU⟩, rfl⟩

/-- The transport of shapes. -/
private theorem shape_translate_aux {t : Fin 3 → ℝ} {Z : Set X3} {S : MSAlg} {U : Subgroup SL3}
    (hU : IsHoro U) {b : Set (Set X3)} (hbm : S.m = MeasurableSpace.generateFrom b) {x : X3}
    (hx : x ∈ (fun y : X3 => aDiag t • y) ⁻¹' Z)
    (hsub : atom S.m (aDiag t • x) ⊆ Z) :
    shape (S.translate t Z).m U x = conjD (-t) (shape S.m U (aDiag t • x)) := by
  have hatom := atom_translate hbm hx hsub
  ext u
  rw [shape, shape, mem_conjD]
  simp only [Set.mem_ofPred_eq, neg_neg]
  constructor
  · rintro ⟨huU, hu⟩
    rw [hatom, Set.mem_preimage] at hu
    refine ⟨hU.2.1 t u huU, ?_⟩
    have heq : (aDiag t * u * (aDiag t)⁻¹) • (aDiag t • x) = aDiag t • (u • x) := by
      rw [mul_smul, mul_smul, inv_smul_smul]
    rw [heq]
    exact hu
  · rintro ⟨hvU, hv⟩
    refine ⟨?_, ?_⟩
    · have h := hU.2.1 (-t) _ hvU
      have heq : aDiag (-t) * (aDiag t * u * (aDiag t)⁻¹) * (aDiag (-t))⁻¹ = u := by
        rw [← aDiag_inv_aDiag t]
        group
      rwa [heq] at h
    · rw [hatom, Set.mem_preimage]
      have heq : (aDiag t * u * (aDiag t)⁻¹) • (aDiag t • x) = aDiag t • (u • x) := by
        rw [mul_smul, mul_smul, inv_smul_smul]
      rw [heq] at hv
      exact hv

/-- **The transport of plaque algebras** (Pisa 7.17, first sentence). -/
theorem isPlaqueAlgebra_translate {U : Subgroup SL3} (hU : IsHoro U) (t : Fin 3 → ℝ)
    {Z : Set X3} {S : MSAlg} (h : IsPlaqueAlgebra U Z S.m) :
    IsPlaqueAlgebra U ((fun y : X3 => aDiag t • y) ⁻¹' Z) (S.translate t Z).m := by
  obtain ⟨hmle, ⟨b, hbc, hbm⟩, hZ, hcl⟩ := h
  have hZbor : MeasurableSet Z := MeasurableSpace.le_def.mp hmle Z hZ
  have hb : ∀ B ∈ b, MeasurableSet B := fun B hB =>
    MeasurableSpace.le_def.mp hmle B (hbm.symm ▸ MeasurableSpace.measurableSet_generateFrom hB)
  refine ⟨translate_le hbm hb hZbor, translate_countablyGenerated ⟨b, hbc, hbm⟩,
    measurableSet_translateZ, ?_⟩
  intro x hx
  have hxZ : aDiag t • x ∈ Z := hx
  have hsub : atom S.m (aDiag t • x) ⊆ Z := (hcl (aDiag t • x) hxZ).1
  have hatom := atom_translate hbm hx hsub
  have hshape := shape_translate_aux hU hbm hx hsub
  obtain ⟨hsubZ, horb, ⟨O, hOopen, hOshape⟩, ⟨C, hCbound⟩⟩ := hcl (aDiag t • x) hxZ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hatom]
    intro y hy
    exact hsubZ hy
  · rw [hatom]
    rintro y hy
    rw [Set.mem_preimage] at hy
    obtain ⟨v, hvU, hv⟩ := horb hy
    refine ⟨aDiag (-t) * v * aDiag t, ?_, ?_⟩
    · have hh := hU.2.1 (-t) v hvU
      simpa [aDiag_inv_aDiag] using hh
    · show (aDiag (-t) * v * aDiag t) • x = y
      have h1 : (aDiag (-t) * v * aDiag t) • x = aDiag (-t) • (v • (aDiag t • x)) := by
        rw [mul_smul, mul_smul]
      calc (aDiag (-t) * v * aDiag t) • x
          = aDiag (-t) • (v • (aDiag t • x)) := h1
        _ = aDiag (-t) • (aDiag t • y) := congrArg (fun z => aDiag (-t) • z) hv
        _ = y := aDiag_smul_cancel t y
  · refine ⟨conjD (-t) O, ?_, ?_⟩
    · have hcO : conjD (-t) O = {g : SL3 | aDiag t * g * (aDiag t)⁻¹ ∈ O} := by
        ext g
        rw [mem_conjD]
        simp
      rw [hcO]
      exact isOpen_conjD_preimage hOopen
    · rw [hshape, hOshape, conjD_inter_U hU (-t) O]
  · have hne : (shape S.m U (aDiag t • x)).Nonempty :=
      ⟨1, ⟨U.one_mem, by
        rw [one_smul]
        exact Set.mem_sInter.mpr (fun s hs => hs.2)⟩⟩
    obtain ⟨C', hC'⟩ := conjD_entries_le (t := -t) hne hCbound
    exact ⟨C', fun u hu i j => hC' u (hshape ▸ hu) i j⟩

/-! ## Pieces of the assembly -/

/-- If the atom at `y` contains the `R`-plaque of `y`, then the `R`-plaque is a subset of the
shape at `y`. -/
theorem V_subset_shape_of_plaque_subset {U : Subgroup SL3} {m : MeasurableSpace X3} {y : X3}
    {R : ℝ} (h : (fun u : SL3 => u • y) '' (V R ∩ (U : Set SL3)) ⊆ atom m y) :
    V R ∩ (U : Set SL3) ⊆ shape m U y := by
  rintro u ⟨huV, huU⟩
  refine ⟨huU, ?_⟩
  have hmem : u • y ∈ (fun u : SL3 => u • y) '' (V R ∩ (U : Set SL3)) :=
    ⟨u, ⟨huV, huU⟩, rfl⟩
  exact h hmem

/-- The union of the `V n ∩ U` over `n ∈ ℕ` is all of `U`. -/
theorem iUnion_V_inter_eq (U : Subgroup SL3) : (⋃ n : ℕ, V (n : ℝ) ∩ (U : Set SL3)) = U := by
  ext u
  constructor
  · intro hu
    rw [Set.mem_iUnion] at hu
    obtain ⟨n, hn⟩ := hu
    exact hn.2
  · intro hu
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ i j,
        |((u : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < (N : ℝ) := by
      refine ⟨Nat.ceil (∑ i : Fin 3, ∑ j : Fin 3,
        |((u : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j|) + 2, ?_⟩
      intro i j
      have hS : |((u : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤
          ∑ i : Fin 3, ∑ j : Fin 3, |((u : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
        le_trans (le_sum_univ (f := fun j' : Fin 3 =>
            |((u : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j'|) (fun _ => abs_nonneg _) j)
          (le_sum_univ (f := fun i' : Fin 3 =>
            ∑ j' : Fin 3, |((u : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i' j'|)
            (fun _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) i)
      have hceil : (∑ i : Fin 3, ∑ j : Fin 3, |((u : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j|)
          ≤ ((Nat.ceil (∑ i : Fin 3, ∑ j : Fin 3,
            |((u : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j|) : ℕ) : ℝ) := Nat.le_ceil _
      have h3 : |((u : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
          - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          ≤ |((u : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j|
            + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
        simpa [sub_eq_add_neg] using abs_add_le (((u : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j)
          (-(1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
      have h4 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
        rw [Matrix.one_apply]; split <;> simp
      push_cast
      linarith
    rw [Set.mem_iUnion]
    exact ⟨N, hN, hu⟩

/-- `t ↦ aDiag t` is continuous. -/
theorem continuous_aDiag' : Continuous (fun t : Fin 3 → ℝ => aDiag t) := by
  have h : Continuous (fun t : Fin 3 → ℝ =>
      ((aDiag t : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) := by
    simp only [toMat_aDiag]
    fun_prop
  exact Continuous.subtype_mk h (fun t => (aDiag t).2)

/-- Joint measurability of the diagonal flow on `X₃`. -/
theorem measurable_aDiag_smul :
    Measurable (fun p : X3 × (Fin 3 → ℝ) => aDiag p.2 • p.1) :=
  ((continuous_smul (M := SL3) (X := X3)).comp
    ((continuous_aDiag'.comp continuous_snd).prodMk continuous_fst)).measurable

/-- The covariance predicate. -/
def Cov (ν : X3 → Measure SL3) (s : Fin 3 → ℝ) (x : X3) : Prop :=
  ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
    ν (aDiag s • x) = c • (ν x).map (fun g : SL3 => aDiag s * g * (aDiag s)⁻¹)

theorem measurable_conjA (s : Fin 3 → ℝ) :
    Measurable (fun g : SL3 => aDiag s * g * (aDiag s)⁻¹) :=
  ((continuous_const.mul continuous_id).mul continuous_const).measurable

theorem conjA_conjA (u v : Fin 3 → ℝ) :
    (fun g : SL3 => aDiag v * (aDiag u * g * (aDiag u)⁻¹) * (aDiag v)⁻¹) =
      fun g : SL3 => aDiag (v + u) * g * (aDiag (v + u))⁻¹ := by
  funext g
  rw [← aDiag_add (s := v) (t := u)]
  group

theorem conjA_comp_t (t s : Fin 3 → ℝ) :
    (fun g : SL3 => aDiag (-s) * (aDiag (t + s) * g * (aDiag (t + s))⁻¹) * (aDiag (-s))⁻¹)
      = fun g : SL3 => aDiag t * g * (aDiag t)⁻¹ := by
  rw [conjA_conjA (t + s) (-s), show -s + (t + s) = t by abel]

theorem conjA_comp_id (s : Fin 3 → ℝ) :
    (fun g : SL3 => aDiag (-s) * (aDiag s * g * (aDiag s)⁻¹) * (aDiag (-s))⁻¹) = id := by
  rw [conjA_conjA s (-s), show -s + s = (0 : Fin 3 → ℝ) by abel, aDiag_zero]
  funext g
  simp

theorem ennreal_arith {a b c d : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ⊤) (h : a * b = c * d) :
    d = (a * c⁻¹) * b := by
  have h2 : c⁻¹ * c = 1 := ENNReal.inv_mul_cancel hc0 hctop
  calc d = c⁻¹ * (c * d) := by rw [← mul_assoc, h2, one_mul]
    _ = c⁻¹ * (a * b) := by rw [h]
    _ = (a * c⁻¹) * b := by rw [← mul_assoc, mul_comm c⁻¹ a, mul_assoc]

theorem Cov_comp {ν : X3 → Measure SL3} {t s : Fin 3 → ℝ} {x : X3}
    (h₁ : Cov ν (t + s) x) (h₂ : Cov ν s (aDiag t • x)) : Cov ν t x := by
  obtain ⟨c₁, hc₁₀, hc₁top, h₁⟩ := h₁
  obtain ⟨c₂, hc₂₀, hc₂top, h₂⟩ := h₂
  have hφ : Measurable (fun g : SL3 => aDiag (-s) * g * (aDiag (-s))⁻¹) := measurable_conjA _
  have hpt : aDiag (t + s) • x = aDiag s • (aDiag t • x) := by
    rw [add_comm t s, aDiag_smul_mul]
  have hkey : c₁ • (ν x).map (fun g : SL3 => aDiag (t + s) * g * (aDiag (t + s))⁻¹)
      = c₂ • (ν (aDiag t • x)).map (fun g : SL3 => aDiag s * g * (aDiag s)⁻¹) := by
    rw [← h₁, hpt, h₂]
  have hpush := congrArg (fun ρ : Measure SL3 =>
    ρ.map (fun g : SL3 => aDiag (-s) * g * (aDiag (-s))⁻¹)) hkey
  have hmap1 : (c₁ • (ν x).map (fun g : SL3 => aDiag (t + s) * g * (aDiag (t + s))⁻¹)).map
        (fun g : SL3 => aDiag (-s) * g * (aDiag (-s))⁻¹)
      = c₁ • (ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) := by
    rw [Measure.map_smul, Measure.map_map hφ (measurable_conjA _),
      show ((fun g : SL3 => aDiag (-s) * g * (aDiag (-s))⁻¹) ∘
        (fun g : SL3 => aDiag (t + s) * g * (aDiag (t + s))⁻¹))
        = fun g : SL3 => aDiag t * g * (aDiag t)⁻¹ from conjA_comp_t t s] <;> try fun_prop
  have hmap2 : (c₂ • (ν (aDiag t • x)).map (fun g : SL3 => aDiag s * g * (aDiag s)⁻¹)).map
        (fun g : SL3 => aDiag (-s) * g * (aDiag (-s))⁻¹)
      = c₂ • ν (aDiag t • x) := by
    rw [Measure.map_smul, Measure.map_map hφ (measurable_conjA _),
      show ((fun g : SL3 => aDiag (-s) * g * (aDiag (-s))⁻¹) ∘
        (fun g : SL3 => aDiag s * g * (aDiag s)⁻¹)) = id from conjA_comp_id s, Measure.map_id] <;> try fun_prop
  rw [hmap1, hmap2] at hpush
  refine ⟨c₁ * c₂⁻¹, mul_ne_zero hc₁₀ (ENNReal.inv_ne_zero.mpr hc₂top),
    ENNReal.mul_ne_top hc₁top (ENNReal.inv_ne_top.mpr hc₂₀), ?_⟩
  refine MeasureTheory.Measure.ext fun C hC => ?_
  have h := congrArg (fun ρ : Measure SL3 => ρ C) hpush
  simp only [Measure.smul_apply, smul_eq_mul] at h
  exact ennreal_arith hc₂₀ hc₂top h


/-- **Fubini upgrade.**  Given the per-parameter covariance a.e. in `x` for every `t`, there is a
single conull set on which the covariance holds for all `t` at once. -/
theorem acov_all_t_of_per_t {μ : Measure X3} [IsProbabilityMeasure μ]
    {ν : X3 → Measure SL3} {X' : Set X3} (hX'meas : MeasurableSet X')
    (hX'null : μ X'ᶜ = 0) (F : Set X3) (hFmeas : MeasurableSet F) (hFnull : μ Fᶜ = 0)
    (hbad : MeasurableSet {p : X3 × (Fin 3 → ℝ) | p.1 ∈ X' ∧ aDiag p.2 • p.1 ∈ X' ∧ ¬ Cov ν p.2 p.1})
    (hper : ∀ t : Fin 3 → ℝ, ∀ᵐ x ∂μ,
      (x ∈ X' ∧ aDiag t • x ∈ X' ∧ x ∈ F ∧ aDiag t • x ∈ F) → Cov ν t x)
    (hA : IsAInvariant μ) :
    ∃ X'' ⊆ X', MeasurableSet X'' ∧ μ X''ᶜ = 0 ∧
      ∀ (t : Fin 3 → ℝ) (x : X3), x ∈ X'' → aDiag t • x ∈ X'' → Cov ν t x := by
  classical
  have hact : Measurable (fun p : X3 × (Fin 3 → ℝ) => aDiag p.2 • p.1) := measurable_aDiag_smul
  let S : Set (X3 × (Fin 3 → ℝ)) := {p | p.1 ∈ X' ∧ aDiag p.2 • p.1 ∈ X' ∧ ¬ Cov ν p.2 p.1}
  let V : Set (X3 × (Fin 3 → ℝ)) := {p | aDiag p.2 • p.1 ∉ X'}
  have hSmeas : MeasurableSet S := by simpa only [S] using hbad
  have hVmeas : MeasurableSet V := by
    have h : V = (fun p : X3 × (Fin 3 → ℝ) => aDiag p.2 • p.1) ⁻¹' X'ᶜ := rfl
    rw [h]; exact hact hX'meas.compl
  -- the flow visits a conull set at almost every time
  have hvisit : ∀ s : Fin 3 → ℝ, ∀ T : Set X3, MeasurableSet T → μ Tᶜ = 0 →
      μ {x : X3 | aDiag s • x ∉ T} = 0 := fun s T hT hTc => by
    have hmp : MeasurePreserving (fun x : X3 => aDiag s • x) μ μ := hA s
    have h1 : (fun x : X3 => aDiag s • x) ⁻¹' Tᶜ = {x : X3 | aDiag s • x ∉ T} := rfl
    rw [← h1, ← Measure.map_apply hmp.measurable hT.compl, hmp.map_eq]
    exact hTc
  have hsecV : ∀ s : Fin 3 → ℝ, μ {x : X3 | (x, s) ∈ V} = 0 := fun s => by
    have h := hvisit s X' hX'meas hX'null
    simpa only [V, Set.mem_ofPred_eq] using h
  have hsecS : ∀ s : Fin 3 → ℝ, μ {x : X3 | (x, s) ∈ S} = 0 := fun s => by
    have hAz : μ {x : X3 | ¬ ((x ∈ X' ∧ aDiag s • x ∈ X' ∧ x ∈ F ∧ aDiag s • x ∈ F) →
        Cov ν s x)} = 0 := MeasureTheory.ae_iff.mp (hper s)
    have hnull : μ ({x : X3 | ¬ ((x ∈ X' ∧ aDiag s • x ∈ X' ∧ x ∈ F ∧ aDiag s • x ∈ F) →
        Cov ν s x)} ∪ (Fᶜ ∪ {x : X3 | aDiag s • x ∉ F})) = 0 :=
      measure_union_null hAz (measure_union_null hFnull (hvisit s F hFmeas hFnull))
    refine measure_mono_null ?_ hnull
    · intro x hx
      simp only [S, Set.mem_ofPred_eq, Set.mem_union] at hx ⊢
      by_cases hF1 : x ∈ F
      · by_cases hF2 : aDiag s • x ∈ F
        · refine Or.inl ?_
          rw [Classical.not_imp]
          exact ⟨⟨hx.1, hx.2.1, hF1, hF2⟩, hx.2.2⟩
        · exact Or.inr (Or.inr hF2)
      · exact Or.inr (Or.inl hF1)
  -- Fubini
  have hSprod : μ.prod volume S = 0 := by
    rw [Measure.prod_apply_symm hSmeas]
    have h : (fun s : Fin 3 → ℝ => μ ((fun x : X3 => (x, s)) ⁻¹' S)) = fun _ => 0 := by
      funext s; exact hsecS s
    rw [h, lintegral_zero]
  have hVprod : μ.prod volume V = 0 := by
    rw [Measure.prod_apply_symm hVmeas]
    have h : (fun s : Fin 3 → ℝ => μ ((fun x : X3 => (x, s)) ⁻¹' V)) = fun _ => 0 := by
      funext s; exact hsecV s
    rw [h, lintegral_zero]
  have haeS : ∀ᵐ x ∂μ, ∀ᵐ s ∂volume, (x, s) ∉ S :=
    (Measure.ae_prod_iff_ae_ae hSmeas.compl).mp
      (MeasureTheory.ae_iff.mpr (by simpa using hSprod))
  have haeV : ∀ᵐ x ∂μ, ∀ᵐ s ∂volume, (x, s) ∉ V :=
    (Measure.ae_prod_iff_ae_ae hVmeas.compl).mp
      (MeasureTheory.ae_iff.mpr (by simpa using hVprod))
  have hX'ae : ∀ᵐ x ∂μ, x ∈ X' :=
    MeasureTheory.ae_iff.mpr (show μ {a : X3 | ¬ a ∈ X'} = 0 from hX'null)
  have hFae : ∀ᵐ x ∂μ, x ∈ F :=
    MeasureTheory.ae_iff.mpr (show μ {a : X3 | ¬ a ∈ F} = 0 from hFnull)
  -- the conull set of points on which the flow touches `X'` at almost every time
  let A₁ : Set X3 := {x | volume (Prod.mk x ⁻¹' S) = 0}
  let A₂ : Set X3 := {x | volume (Prod.mk x ⁻¹' V) = 0}
  have hA₁meas : MeasurableSet A₁ := by
    have h := (measurable_measure_prodMk_left (ν := (volume : Measure (Fin 3 → ℝ))) hSmeas)
      (measurableSet_singleton (0 : ℝ≥0∞))
    change MeasurableSet {x : X3 | volume (Prod.mk x ⁻¹' S) = 0}
    exact h
  have hA₂meas : MeasurableSet A₂ := by
    have h := (measurable_measure_prodMk_left (ν := (volume : Measure (Fin 3 → ℝ))) hVmeas)
      (measurableSet_singleton (0 : ℝ≥0∞))
    change MeasurableSet {x : X3 | volume (Prod.mk x ⁻¹' V) = 0}
    exact h
  have hsetS : ∀ x : X3, {a : Fin 3 → ℝ | ¬ (x, a) ∉ S} = Prod.mk x ⁻¹' S := by
    intro x; ext a; simp
  have hsetV : ∀ x : X3, {a : Fin 3 → ℝ | ¬ (x, a) ∉ V} = Prod.mk x ⁻¹' V := by
    intro x; ext a; simp
  have hA₁ae : ∀ᵐ x ∂μ, x ∈ A₁ := by
    filter_upwards [haeS] with x hx
    change volume (Prod.mk x ⁻¹' S) = 0
    rw [← hsetS x]
    exact MeasureTheory.ae_iff.mp hx
  have hA₂ae : ∀ᵐ x ∂μ, x ∈ A₂ := by
    filter_upwards [haeV] with x hx
    change volume (Prod.mk x ⁻¹' V) = 0
    rw [← hsetV x]
    exact MeasureTheory.ae_iff.mp hx
  let Q : X3 → Prop := fun x => x ∈ X' ∧ x ∈ F ∧ x ∈ A₁ ∧ x ∈ A₂
  have hQae : ∀ᵐ x ∂μ, Q x := by
    filter_upwards [hX'ae, hFae, hA₁ae, hA₂ae] with x h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  have hQnull : μ {x | ¬ Q x} = 0 := MeasureTheory.ae_iff.mp hQae
  refine ⟨(MeasureTheory.toMeasurable μ {x | ¬ Q x})ᶜ, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hQx : Q x := by
      by_contra h
      exact hx (MeasureTheory.subset_toMeasurable μ {x | ¬ Q x} h)
    exact hQx.1
  · exact (MeasureTheory.measurableSet_toMeasurable μ {x | ¬ Q x}).compl
  · rw [compl_compl, MeasureTheory.measure_toMeasurable]
    exact hQnull
  · intro t x hx hx2
    have hQx : Q x := by
      by_contra h
      exact hx (MeasureTheory.subset_toMeasurable μ {x | ¬ Q x} h)
    have hQy : Q (aDiag t • x) := by
      by_contra h
      exact hx2 (MeasureTheory.subset_toMeasurable μ {x | ¬ Q x} h)
    obtain ⟨hxX', hxF, hxA₁, hxA₂⟩ := hQx
    obtain ⟨hyX', hyF, hyA₁, hyA₂⟩ := hQy
    -- translate the a.e. statements to the shifted parameter
    have hshift : ∀ (y : X3), volume (Prod.mk y ⁻¹' S) = 0 →
        ∀ᵐ s ∂volume, (y, t + s) ∉ S := fun y hy => by
      have h : ∀ᵐ s ∂volume, (y, s) ∉ S := by
        refine MeasureTheory.ae_iff.mpr ?_
        rw [hsetS y]; exact hy
      have hmp : MeasurePreserving (fun s : Fin 3 → ℝ => s + t) volume volume :=
        ⟨measurable_id.add_const t, map_add_right_eq_self volume t⟩
      filter_upwards [hmp.quasiMeasurePreserving.ae h] with s hs
      simpa only [add_comm] using hs
    have hshiftV : ∀ (y : X3), volume (Prod.mk y ⁻¹' V) = 0 →
        ∀ᵐ s ∂volume, (y, t + s) ∉ V := fun y hy => by
      have h : ∀ᵐ s ∂volume, (y, s) ∉ V := by
        refine MeasureTheory.ae_iff.mpr ?_
        rw [hsetV y]; exact hy
      have hmp : MeasurePreserving (fun s : Fin 3 → ℝ => s + t) volume volume :=
        ⟨measurable_id.add_const t, map_add_right_eq_self volume t⟩
      filter_upwards [hmp.quasiMeasurePreserving.ae h] with s hs
      simpa only [add_comm] using hs
    have h1 : ∀ᵐ s ∂volume, (x, t + s) ∉ S := hshift x hxA₁
    have h2 : ∀ᵐ s ∂volume, (aDiag t • x, s) ∉ S := by
      refine MeasureTheory.ae_iff.mpr ?_
      rw [hsetS (aDiag t • x)]
      exact hyA₁
    have h3 : ∀ᵐ s ∂volume, (x, t + s) ∉ V := hshiftV x hxA₂
    have h4 : ∀ᵐ s ∂volume, (aDiag t • x, s) ∉ V := by
      refine MeasureTheory.ae_iff.mpr ?_
      rw [hsetV (aDiag t • x)]
      exact hyA₂
    obtain ⟨s, ⟨hs1, hs2⟩, hs3, hs4⟩ := ((h1.and h2).and (h3.and h4)).exists
    have hv1 : aDiag (t + s) • x ∈ X' := by
      by_contra h
      exact hs3 (by simpa only [V, Set.mem_ofPred_eq] using h)
    have hv2 : aDiag s • (aDiag t • x) ∈ X' := by
      by_contra h
      exact hs4 (by simpa only [V, Set.mem_ofPred_eq] using h)
    have hc1 : Cov ν (t + s) x := by
      by_contra h
      exact hs1 ⟨hxX', hv1, h⟩
    have hc2 : Cov ν s (aDiag t • x) := by
      by_contra h
      exact hs2 ⟨hyX', hv2, h⟩
    exact Cov_comp hc1 hc2


/-! ## The assembly: (U7) from the two pieces

`Work.EKLRelCross.per_t_covariance` (the covariance for each fixed `t`, a.e. in `x`, the flower
argument of Pisa 7.17) and `Work.EKLRelCross.covariance_bad_measurable` (measurability of the bad
set) feed the Fubini upgrade `acov_all_t_of_per_t` above. -/

theorem leafwise_acovariant_of_pieces {μ : Measure X3} [IsProbabilityMeasure μ]
    (U : Subgroup SL3) (hU : IsHoro U)
    (ν : X3 → Measure SL3) (X' : Set X3) (hL : IsLeafwise μ U ν X')
    (hfree : ∀ᵐ x ∂μ, ∀ u ∈ U, u • x = x → u = 1)
    (hbad : MeasurableSet {p : X3 × (Fin 3 → ℝ) | p.1 ∈ X' ∧ aDiag p.2 • p.1 ∈ X' ∧
      ¬ ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
        ν (aDiag p.2 • p.1) = c • (ν p.1).map (fun g : SL3 => aDiag p.2 * g * (aDiag p.2)⁻¹)})
    (hper : ∀ t : Fin 3 → ℝ, ∀ᵐ x ∂μ,
      (x ∈ X' ∧ aDiag t • x ∈ X' ∧ (∀ u ∈ U, u • x = x → u = 1) ∧
        (∀ u ∈ U, u • (aDiag t • x) = aDiag t • x → u = 1)) →
      ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
        ν (aDiag t • x) = c • (ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹))
    (hAinv : IsAInvariant μ) :
    ∃ X'' ⊆ X', MeasurableSet X'' ∧ μ X''ᶜ = 0 ∧
      ∀ (t : Fin 3 → ℝ) (x : X3), x ∈ X'' → aDiag t • x ∈ X'' →
        ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
          ν (aDiag t • x) = c • (ν x).map (fun g : SL3 => aDiag t * g * (aDiag t)⁻¹) := by
  classical
  -- a measurable conull set contained in the set of free points
  set N : Set X3 := {x | ¬ (∀ u ∈ U, u • x = x → u = 1)} with hNdef
  have hNnull : μ N = 0 := MeasureTheory.ae_iff.mp hfree
  set F : Set X3 := (MeasureTheory.toMeasurable μ N)ᶜ with hFdef
  have hFmeas : MeasurableSet F := (MeasureTheory.measurableSet_toMeasurable μ N).compl
  have hFnull : μ Fᶜ = 0 := by
    rw [hFdef, compl_compl]
    exact (MeasureTheory.measure_toMeasurable (μ := μ) N).trans hNnull
  have hFsub : F ⊆ {x | ∀ u ∈ U, u • x = x → u = 1} := by
    intro x hx
    by_contra hxN
    exact hx (MeasureTheory.subset_toMeasurable μ N (by simpa [hNdef] using hxN))
  have hbadCov : MeasurableSet {p : X3 × (Fin 3 → ℝ) | p.1 ∈ X' ∧ aDiag p.2 • p.1 ∈ X' ∧
      ¬ Cov ν p.2 p.1} := hbad
  have hperF : ∀ t : Fin 3 → ℝ, ∀ᵐ x ∂μ,
      (x ∈ X' ∧ aDiag t • x ∈ X' ∧ x ∈ F ∧ aDiag t • x ∈ F) → Cov ν t x := by
    intro t
    filter_upwards [hper t] with x hx
    rintro ⟨h1, h2, h3, h4⟩
    exact hx ⟨h1, h2, hFsub h3, hFsub h4⟩
  exact acov_all_t_of_per_t hL.meas_dom hL.conull F hFmeas hFnull hbadCov hperF hAinv

/-! ## The target -/

theorem leafwise_acovariant (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3) (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    Work.EKLContract.IsAInvariant μ → ∃ X'' ⊆ X', MeasurableSet X'' ∧ μ X''ᶜ = 0 ∧
        ∀ (t : Fin 3 → ℝ) (x : Work.EKLContract.X3), x ∈ X'' → Work.EKLContract.aDiag t • x ∈ X'' →
          ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
            ν (Work.EKLContract.aDiag t • x) = c • (ν x).map (fun g => Work.EKLContract.aDiag t * g * (Work.EKLContract.aDiag t)⁻¹) := by
  intro hAinv
  exact leafwise_acovariant_of_pieces (μ := μ) U hU ν X' hL
    (ae_free_orbit h2 μ U hU t0 ht0 hcontr)
    (covariance_bad_measurable hU hL)
    (fun t => per_t_covariance hU hL hAinv (ae_free_orbit h2 μ U hU t0 ht0 hcontr) t)
    hAinv

end Work.EKLRelCross
