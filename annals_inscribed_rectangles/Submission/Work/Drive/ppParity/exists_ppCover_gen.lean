import Mathlib
import Submission.Work.Drive.ppParity.StripDefs
import Submission.Work.Drive.ppResident_piece

namespace Work.Drive.ppParity

open Manifold Set

set_option backward.isDefEq.respectTransparency false

noncomputable section

theorem exists_ppCover_gen
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M} {w : ℝ → ℝ}
    (hEc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) =>
      E (Work.Drive.ftS z) (Work.Drive.ftU z)))
    (hE'c : Continuous (fun z : EuclideanSpace ℝ (Fin 9) =>
      E' (Work.Drive.ftS z) (Work.Drive.ftU z)))
    (hVc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => V (Work.Drive.ftY z)))
    (hWc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => W (Work.Drive.ftZ z)))
    (hΞc : Continuous (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (hw : Continuous w) (hΞ0 : ∀ p : M, Ξ 0 p = p)
    {K : Set (EuclideanSpace ℝ (Fin 9))} (hK : IsCompact K)
    {δ : ℝ} (hKcover : ∀ x ∈ Submission.Drive.unitBox 8, δ ≤ Work.Drive.ftS x →
      Work.Drive.ftS x ≤ 1 - δ → x ∈ interior K) :
    ∃ (ι : Type) (_ : Fintype ι) (x : ι → EuclideanSpace ℝ (Fin 9))
      (K' : ι → Set (EuclideanSpace ℝ (Fin 9))) (δ' : ι → ℝ),
      (∀ i, IsCompact (K' i)) ∧ (∀ i, 0 < δ' i) ∧
      (∀ i, x i ∈ Work.Drive.ppMeet E E' V W) ∧ (∀ i, K' i ⊆ K) ∧
      (∀ (i : ι) (τ : EuclideanSpace ℝ (Fin 8)) (y : EuclideanSpace ℝ (Fin 9)),
        ‖τ‖ < δ' i → y ∈ K' i →
        y ∈ Work.Drive.ppRegion (E (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i)))
          (E' (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i)))
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E)
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E') V W) ∧
      (∀ y ∈ Submission.Drive.unitBox 8, δ ≤ Work.Drive.ftS y → Work.Drive.ftS y ≤ 1 - δ →
        y ∈ Work.Drive.ppMeet E E' V W → ∃ i, y ∈ interior (K' i)) := by
  classical
  have hftS : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => Work.Drive.ftS z) := by
    show Continuous (fun z : EuclideanSpace ℝ (Fin 9) => z 0)
    fun_prop
  set S : Set (EuclideanSpace ℝ (Fin 9)) := {y | y ∈ Submission.Drive.unitBox 8 ∧
    y ∈ Work.Drive.ppMeet E E' V W ∧ δ ≤ Work.Drive.ftS y ∧ Work.Drive.ftS y ≤ 1 - δ}
    with hSdef
  have hScl : IsClosed S := by
    have heq : S = {y : EuclideanSpace ℝ (Fin 9) | y ∈ Submission.Drive.unitBox 8} ∩
        ({y | E (Work.Drive.ftS y) (Work.Drive.ftU y) = V (Work.Drive.ftY y)} ∩
          {y | E' (Work.Drive.ftS y) (Work.Drive.ftU y) = W (Work.Drive.ftZ y)}) ∩
        {y | δ ≤ Work.Drive.ftS y} ∩ {y | Work.Drive.ftS y ≤ 1 - δ} := by
      ext y
      simp only [hSdef, Set.mem_setOf_eq, Set.mem_inter_iff, Work.Drive.ppMeet]
      tauto
    rw [heq]
    exact (((isClosed_unitBox 8).inter
      ((isClosed_eq hEc hVc).inter (isClosed_eq hE'c hWc))).inter
      (isClosed_le continuous_const hftS)).inter (isClosed_le hftS continuous_const)
  have hScomp : IsCompact S :=
    (isCompact_unitBox 8).of_isClosed_subset hScl (fun y hy => hy.1)
  have hpiece : ∀ y : S, ∃ (K' : Set (EuclideanSpace ℝ (Fin 9))) (δ' : ℝ), IsCompact K' ∧ 0 < δ' ∧
      (y : EuclideanSpace ℝ (Fin 9)) ∈ interior K' ∧ K' ⊆ K ∧
      (∀ (τ : EuclideanSpace ℝ (Fin 8)) (z : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ' → z ∈ K' →
        z ∈ Work.Drive.ppRegion (E (Work.Drive.ftS y.1) (Work.Drive.ftU y.1))
          (E' (Work.Drive.ftS y.1) (Work.Drive.ftU y.1))
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E)
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E') V W) := by
    intro y
    obtain ⟨hybox, hym, hys1, hys2⟩ : (y : EuclideanSpace ℝ (Fin 9)) ∈ Submission.Drive.unitBox 8 ∧
        (y : EuclideanSpace ℝ (Fin 9)) ∈ Work.Drive.ppMeet E E' V W ∧
        δ ≤ Work.Drive.ftS y ∧ Work.Drive.ftS y ≤ 1 - δ := y.2
    obtain ⟨K₀, δ₀, hK₀, hδ₀, hy₀, hres₀⟩ :=
      ppResident_piece hEc hE'c hVc hWc hym Ξ hΞc hΞ0 w hw
    refine ⟨K₀ ∩ K, δ₀, hK₀.inter hK, hδ₀, ?_, Set.inter_subset_right, ?_⟩
    · have hyK : (y : EuclideanSpace ℝ (Fin 9)) ∈ interior K := hKcover y.1 hybox hys1 hys2
      rw [interior_inter]
      exact ⟨hy₀, hyK⟩
    · intro τ z hτ hz
      exact hres₀ τ z hτ hz.1
  choose K' δ' hK'c hδ'pos hK'int hK'sub hK'res using hpiece
  have hcov : S ⊆ ⋃ y : S, interior (K' y) :=
    fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hK'int ⟨y, hy⟩⟩
  obtain ⟨t, ht⟩ := hScomp.elim_finite_subcover (fun y : S => interior (K' y))
    (fun _ => isOpen_interior) hcov
  refine ⟨{y : S // y ∈ (t : Set S)}, (t.finite_toSet.fintype), fun i => (i.1 : S).1,
    fun i => K' i.1, fun i => δ' i.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun i => hK'c i.1
  · exact fun i => hδ'pos i.1
  · intro i
    obtain ⟨-, hym, -, -⟩ : (i.1 : S).1 ∈ Submission.Drive.unitBox 8 ∧
        (i.1 : S).1 ∈ Work.Drive.ppMeet E E' V W ∧ δ ≤ Work.Drive.ftS (i.1 : S).1 ∧
        Work.Drive.ftS (i.1 : S).1 ≤ 1 - δ := (i.1 : S).2
    exact hym
  · exact fun i => hK'sub i.1
  · exact fun i => hK'res i.1
  · intro y hybox hys1 hys2 hym
    have hyS : y ∈ S := ⟨hybox, hym, hys1, hys2⟩
    obtain ⟨i, hi, hiy⟩ := Set.mem_iUnion₂.mp (ht hyS)
    exact ⟨⟨i, hi⟩, hiy⟩

end

end Work.Drive.ppParity
