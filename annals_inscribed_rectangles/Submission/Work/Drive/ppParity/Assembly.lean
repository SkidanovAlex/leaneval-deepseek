import Mathlib
import Submission.Work.Drive.ppParity.Contain
import Submission.Work.Drive.ppParity.Inter
import Submission.Work.Drive.ppParity.Richness
import Submission.Work.Drive.ppResident_piece
import Submission.Work.Drive.PPRegAt_chart_indep
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.piece_data_pp

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# **S3**: `Work.Drive.exists_ppReg_shift` — the intrinsic pair Sard with the collars

The capstone of the lead's S3 (`NOTES_LEAD_residency.md`): for the *intrinsically perturbed* pair family
`Et τ = Ξ (w · • unpackFst τ) ∘ E`, `Et' τ = Ξ (w · • unpackSnd τ) ∘ E'` there is an arbitrarily small
parameter `τ` at which the pair map is *regular at every meet in the nine-box* (`PPRegAt`), with the two
end collars of the weight handled by the base regularity `hregBase` (where the perturbation is inactive).

The proof is the assembly of the bricks of `ppParity/`:

* `ppResident_piece` (the per-piece chart residency) → a finite cover of the slab part of the base locus
  (shrunk into `K`, where `w ≠ 0`);
* `piece_data_pp` per piece (the localized parametric Sard, with `hsurj` from the richness
  `surjective_fderiv_ppDiff_shift`);
* `pp_dense_iInter_of_dense_ball` (one common parameter for finitely many pieces, each good set open by
  `ppGoodSet_open` and dense near `0`);
* `eventually_ppMeet_subset_of_isOpen` (the perturbed locus stays in the union of the pieces' interiors
  and the open collar);
* `PPRegAt_ppShift_of_collar` (the collar), and `PPRegAt_chart_indep` (the conversion of the piece's
  chartered conclusion to the self-centred `PPRegAt`).

**Collar conventions (repaired — see `S3_ppParity_STATUS.md` §2).**  The weight vanishes on the *open*
collars (`hwleft : s < δ → w s = 0`), the *closed* slab lies in the *interior* of `K`
(`hKcover : … → x ∈ interior K`), and `w` does not vanish on `K` (`hwne`); these three are jointly
satisfiable (e.g. `w s = 0` for `s ≤ δ`, `w s ≠ 0` for `s ∈ (δ, 1)`), unlike the closed-collar
convention of `Work.Drive.exists_even_colCount_add2_of_shift_collar`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set Filter

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

variable {Q : ℂ → CappingSpace}

/-- The composed chains are smooth. -/
lemma contMDiff_composed_of {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {F : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    (hF : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry F)) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => F (ftS z) (ftU z)) := by
  have h1 : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => (ftS z, ftU z)) := by
    refine contMDiff_iff_contDiff.mpr ?_
    refine ContDiff.prodMk ?_ ?_
    · show ContDiff ℝ Ctop (fun z : EuclideanSpace ℝ (Fin 9) => z 0)
      fun_prop
    · show ContDiff ℝ Ctop (fun z : EuclideanSpace ℝ (Fin 9) =>
        WithLp.toLp 2 (fun i : Fin 2 => z ⟨1 + i.val, by omega⟩))
      fun_prop
  have h := hF.comp h1
  simpa only [Function.comp_def, Function.uncurry] using h



/-- The composed sweep chains are smooth. -/
lemma contMDiff_comp_ftY {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {G : EuclideanSpace ℝ (Fin 3) → M}
    (hG : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) G) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => G (ftY z)) := by
  refine hG.comp ?_
  show ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : EuclideanSpace ℝ (Fin 9) =>
      WithLp.toLp 2 (fun i : Fin 3 => z ⟨3 + i.val, by omega⟩))
  exact contMDiff_iff_contDiff.mpr (by
    show ContDiff ℝ Ctop (fun z : EuclideanSpace ℝ (Fin 9) =>
      WithLp.toLp 2 (fun i : Fin 3 => z ⟨3 + i.val, by omega⟩))
    fun_prop)

/-- The composed sweep chains are smooth (second block). -/
lemma contMDiff_comp_ftZ {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {G : EuclideanSpace ℝ (Fin 3) → M}
    (hG : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) G) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : EuclideanSpace ℝ (Fin 9) => G (ftZ z)) := by
  refine hG.comp ?_
  show ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun z : EuclideanSpace ℝ (Fin 9) =>
      WithLp.toLp 2 (fun i : Fin 3 => z ⟨6 + i.val, by omega⟩))
  exact contMDiff_iff_contDiff.mpr (by
    show ContDiff ℝ Ctop (fun z : EuclideanSpace ℝ (Fin 9) =>
      WithLp.toLp 2 (fun i : Fin 3 => z ⟨6 + i.val, by omega⟩))
    fun_prop)

/-- **The finite chart-per-piece cover of S3**: compact neighbourhoods (inside `K`, where the weight is
nonzero) with a radius on which the two charts taken at the *base values* contain all perturbed values,
covering the closed-slab part of the base pair locus. -/
theorem exists_ppCover
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {V W : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace} {w : ℝ → ℝ}
    (hEc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => E (ftS z) (ftU z)))
    (hE'c : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => E' (ftS z) (ftU z)))
    (hVc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => V (ftY z)))
    (hWc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => W (ftZ z)))
    (hΞc : Continuous (fun q : EuclideanSpace ℝ (Fin 4) × CappingSpace => Ξ q.1 q.2))
    (hw : Continuous w) (hΞ0 : ∀ p : CappingSpace, Ξ 0 p = p)
    {K : Set (EuclideanSpace ℝ (Fin 9))} (hK : IsCompact K)
    (hwne : ∀ x ∈ K, w (ftS x) ≠ 0)
    {δ : ℝ} (hKcover : ∀ x ∈ Submission.Drive.unitBox 8, δ ≤ ftS x → ftS x ≤ 1 - δ →
      x ∈ interior K) :
    ∃ (ι : Type) (_ : Fintype ι) (x : ι → EuclideanSpace ℝ (Fin 9))
      (K' : ι → Set (EuclideanSpace ℝ (Fin 9))) (δ' : ι → ℝ),
      (∀ i, IsCompact (K' i)) ∧ (∀ i, 0 < δ' i) ∧
      (∀ i, x i ∈ ppMeet E E' V W) ∧ (∀ i, K' i ⊆ K) ∧
      (∀ (i : ι) (τ : EuclideanSpace ℝ (Fin 8)) (y : EuclideanSpace ℝ (Fin 9)),
        ‖τ‖ < δ' i → y ∈ K' i →
        y ∈ ppRegion (E (ftS (x i)) (ftU (x i))) (E' (ftS (x i)) (ftU (x i)))
          (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W) ∧
      (∀ y ∈ Submission.Drive.unitBox 8, δ ≤ ftS y → ftS y ≤ 1 - δ →
        y ∈ ppMeet E E' V W → ∃ i, y ∈ interior (K' i)) := by
  classical
  have hftS : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => ftS z) := by
    show Continuous (fun z : EuclideanSpace ℝ (Fin 9) => z 0)
    fun_prop
  set S : Set (EuclideanSpace ℝ (Fin 9)) := {y | y ∈ Submission.Drive.unitBox 8 ∧
    y ∈ ppMeet E E' V W ∧ δ ≤ ftS y ∧ ftS y ≤ 1 - δ} with hSdef
  have hScl : IsClosed S := by
    have heq : S = {y : EuclideanSpace ℝ (Fin 9) | y ∈ Submission.Drive.unitBox 8} ∩
        ({y | E (ftS y) (ftU y) = V (ftY y)} ∩ {y | E' (ftS y) (ftU y) = W (ftZ y)}) ∩
        {y | δ ≤ ftS y} ∩ {y | ftS y ≤ 1 - δ} := by
      ext y
      simp only [hSdef, Set.mem_setOf_eq, Set.mem_inter_iff, ppMeet]
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
        z ∈ ppRegion (E (ftS y.1) (ftU y.1)) (E' (ftS y.1) (ftU y.1))
          (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W) := by
    intro y
    obtain ⟨hybox, hym, hys1, hys2⟩ : (y : EuclideanSpace ℝ (Fin 9)) ∈ Submission.Drive.unitBox 8 ∧
        (y : EuclideanSpace ℝ (Fin 9)) ∈ ppMeet E E' V W ∧ δ ≤ ftS y ∧ ftS y ≤ 1 - δ := y.2
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
        (i.1 : S).1 ∈ ppMeet E E' V W ∧ δ ≤ ftS (i.1 : S).1 ∧
        ftS (i.1 : S).1 ≤ 1 - δ := (i.1 : S).2
    exact hym
  · exact fun i => hK'sub i.1
  · exact fun i => hK'res i.1
  · intro y hybox hys1 hys2 hym
    have hyS : y ∈ S := ⟨hybox, hym, hys1, hys2⟩
    obtain ⟨i, hi, hiy⟩ := Set.mem_iUnion₂.mp (ht hyS)
    exact ⟨⟨i, hi⟩, hiy⟩

/-- **S3: the intrinsic pair Sard with the two collars.** -/
theorem exists_ppReg_shift_of_pieces
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {V W : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace} {w : ℝ → ℝ}
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hΞ : ChartPert Q 4 Ξ)
    (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K)
    (hwne : ∀ x ∈ K, w (ftS x) ≠ 0)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hKcover : ∀ x ∈ Submission.Drive.unitBox 8, δ ≤ ftS x → ftS x ≤ 1 - δ →
      x ∈ interior K)
    (hwleft : ∀ s : ℝ, s < δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ < s → w s = 0)
    (hregBase : ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      ppMeet E E' V W x → PPRegAt E E' V W x)
    (hpd : ∀ (p p' : CappingSpace) (K' : Set (EuclideanSpace ℝ (Fin 9))) (δ' : ℝ),
      IsCompact K' → 0 < δ' →
      (∀ (τ : EuclideanSpace ℝ (Fin 8)) (y : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ' → y ∈ K' →
        y ∈ ppRegion p p' (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W) →
      (∀ (τ : EuclideanSpace ℝ (Fin 8)) (y : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ' → y ∈ K' →
        ppDiff p p' (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W y = 0 →
        Function.Surjective (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin 8) =>
          ppDiff p p' (ppShift Ξ w (unpackFst τ') E) (ppShift Ξ w (unpackSnd τ') E') V W y) τ)) →
      ∃ (ρ : ℝ) (Ψ : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) →
          EuclideanSpace ℝ (Fin 8)),
        0 < ρ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
        IsOpen {τ : EuclideanSpace ℝ (Fin 8) | ppGoodSet Ψ K' τ} ∧
        (∀ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < ρ → ppGoodSet Ψ K' τ →
          PPChartGood p p' E E' V W Ξ w τ K') ∧
        (∀ τ₀ : EuclideanSpace ℝ (Fin 8), ‖τ₀‖ < ρ → ∀ ε' : ℝ, 0 < ε' →
          ∃ τ : EuclideanSpace ℝ (Fin 8), ‖τ - τ₀‖ < ε' ∧ ‖τ‖ < ρ ∧ ppGoodSet Ψ K' τ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < ε ∧
      ∀ x ∈ Submission.Drive.unitBox 8,
        ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W x →
        PPRegAt (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W x := by
  classical
  -- ## 0. continuity bookkeeping
  have hEc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => E (ftS z) (ftU z)) :=
    (contMDiff_composed_of hE).continuous
  have hE'c : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => E' (ftS z) (ftU z)) :=
    (contMDiff_composed_of hE').continuous
  have hftS : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => ftS z) := by
    show Continuous (fun z : EuclideanSpace ℝ (Fin 9) => z 0)
    fun_prop
  have hftY : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => ftY z) := by
    show Continuous (fun z : EuclideanSpace ℝ (Fin 9) =>
      WithLp.toLp 2 (fun i : Fin 3 => z ⟨3 + i.val, by omega⟩))
    fun_prop
  have hftZ : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => ftZ z) := by
    show Continuous (fun z : EuclideanSpace ℝ (Fin 9) =>
      WithLp.toLp 2 (fun i : Fin 3 => z ⟨6 + i.val, by omega⟩))
    fun_prop
  have hVc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => V (ftY z)) :=
    hV.continuous.comp hftY
  have hWc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => W (ftZ z)) :=
    hW.continuous.comp hftZ
  have hΞc : Continuous (fun q : EuclideanSpace ℝ (Fin 4) × CappingSpace => Ξ q.1 q.2) :=
    hΞ.2.1.continuous
  have hPc : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      ppShift Ξ w (unpackFst q.1) E (ftS q.2) (ftU q.2)) := by
    show Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      Ξ (w (ftS q.2) • unpackFst q.1) (E (ftS q.2) (ftU q.2)))
    refine hΞc.comp (Continuous.prodMk ?_ ?_)
    · exact (hw.continuous.comp (hftS.comp continuous_snd)).smul
        (unpackFst.continuous.comp continuous_fst)
    · exact hEc.comp continuous_snd
  have hPc' : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      ppShift Ξ w (unpackSnd q.1) E' (ftS q.2) (ftU q.2)) := by
    show Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      Ξ (w (ftS q.2) • unpackSnd q.1) (E' (ftS q.2) (ftU q.2)))
    refine hΞc.comp (Continuous.prodMk ?_ ?_)
    · exact (hw.continuous.comp (hftS.comp continuous_snd)).smul
        (unpackSnd.continuous.comp continuous_fst)
    · exact hE'c.comp continuous_snd
  have hVc2 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      V (ftY q.2)) := hVc.comp continuous_snd
  have hWc2 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      W (ftZ q.2)) := hWc.comp continuous_snd
  -- ## 1. the finite cover
  obtain ⟨ι, hι, x, K', δ', hK'c, hδ'pos, hxm, hK'sub, hres, hcover⟩ :=
    exists_ppCover hEc hE'c hVc hWc hΞc hw.continuous hΞ.1 hK hwne hKcover
  letI : Fintype ι := hι
  -- ## 2. the per-piece localized Sard
  have hpd : ∀ i : ι, ∃ (ρ : ℝ) (Ψ : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) →
      EuclideanSpace ℝ (Fin 8)), 0 < ρ ∧ ContDiff ℝ Ctop Ψ ∧
      IsOpen {τ : EuclideanSpace ℝ (Fin 8) | ppGoodSet Ψ (K' i) τ} ∧
      (∀ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < ρ → ppGoodSet Ψ (K' i) τ →
        PPChartGood (E (ftS (x i)) (ftU (x i))) (E' (ftS (x i)) (ftU (x i))) E E' V W Ξ w τ (K' i)) ∧
      (∀ τ₀ : EuclideanSpace ℝ (Fin 8), ‖τ₀‖ < ρ → ∀ ε' : ℝ, 0 < ε' →
        ∃ τ : EuclideanSpace ℝ (Fin 8), ‖τ - τ₀‖ < ε' ∧ ‖τ‖ < ρ ∧ ppGoodSet Ψ (K' i) τ) := by
    intro i
    exact hpd _ _ _ _ (hK'c i) (hδ'pos i) (fun τ y hτ hy => hres i τ y hτ hy)
      (fun τ y hτ hy hzero =>
        surjective_fderiv_ppDiff_shift (Ξ := Ξ) hΞ w τ y (E (ftS (x i)) (ftU (x i)))
          (E' (ftS (x i)) (ftU (x i))) (hres i τ y hτ hy).1 (hres i τ y hτ hy).2.2.1
          (hwne y (hK'sub i hy)))
  choose ρ Ψ hρpos hΨsm hΨopen htrans hdense using hpd
  -- ## 3. one common parameter
  obtain ⟨ρ₀, hρ₀pos, hρ₀le⟩ := exists_pos_le_all ρ hρpos
  obtain ⟨δ'₀, hδ'₀pos, hδ'₀le⟩ := exists_pos_le_all δ' hδ'pos
  set U : Set (EuclideanSpace ℝ (Fin 9)) := (⋃ i, interior (K' i)) ∪
    {y : EuclideanSpace ℝ (Fin 9) | ftS y < δ ∨ 1 - δ < ftS y} with hUdef
  have hUopen : IsOpen U := by
    refine IsOpen.union (isOpen_iUnion fun i => isOpen_interior) ?_
    exact (isOpen_lt hftS continuous_const).union (isOpen_lt continuous_const hftS)
  have hUbase : ∀ y ∈ Submission.Drive.unitBox 8, y ∈ ppMeet E E' V W → y ∈ U := by
    intro y hy hyM
    rw [hUdef]
    by_cases hc : ftS y < δ ∨ 1 - δ < ftS y
    · exact Or.inr hc
    · push_neg at hc
      have hmem : y ∈ ⋃ i, interior (K' i) := Set.mem_iUnion.mpr (hcover y hy hc.1 hc.2 hyM)
      exact Or.inl hmem
  have hev := eventually_ppMeet_subset_of_isOpen (Ξ := Ξ) hPc hPc' hVc2 hWc2 hΞ.1 hw.continuous
    hUopen hUbase
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < δ₀ → ∀ y ∈ Submission.Drive.unitBox 8,
        y ∈ ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W →
        y ∈ U := by
    rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hev
    obtain ⟨δ₀, hδ₀pos, hsub⟩ := hev
    exact ⟨δ₀, hδ₀pos, fun τ hτ y hy hM =>
      hsub (by rwa [Metric.mem_ball, dist_zero_right]) y hy hM⟩
  set Sg : ι → Set (EuclideanSpace ℝ (Fin 8)) :=
    fun i => {τ | ‖τ‖ < ρ i ∧ ppGoodSet (Ψ i) (K' i) τ} with hSgdef
  have hSgopen : ∀ i, IsOpen (Sg i) := by
    intro i
    exact (isOpen_lt continuous_norm continuous_const).inter (hΨopen i)
  have hSgdense : ∀ i, Metric.ball 0 ρ₀ ⊆ closure (Sg i) := by
    intro i τ₀ hτ₀
    rw [Metric.mem_closure_iff]
    intro ε' hε'
    have hτ₀ρ : ‖τ₀‖ < ρ i :=
      lt_of_lt_of_le (by rwa [Metric.mem_ball, dist_zero_right] at hτ₀) (hρ₀le i)
    obtain ⟨τ, hclose, hτρ, hgood⟩ := hdense i τ₀ hτ₀ρ (ε' / 2) (by linarith)
    refine ⟨τ, ⟨hτρ, hgood⟩, ?_⟩
    rw [dist_eq_norm]
    linarith [hclose, norm_sub_rev τ τ₀]
  have hdenseint := pp_dense_iInter_of_dense_ball Sg ρ₀ hSgopen hSgdense
  set R : ℝ := min ε (min ρ₀ (min δ₀ δ'₀)) with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    exact lt_min hε (lt_min hρ₀pos (lt_min hδ₀pos hδ'₀pos))
  have hRε : R ≤ ε := by rw [hRdef]; exact min_le_left _ _
  have hRρ : R ≤ ρ₀ := by
    rw [hRdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hRδ : R ≤ δ₀ := by
    rw [hRdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRδ' : R ≤ δ'₀ := by
    rw [hRdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have h0mem : (0 : EuclideanSpace ℝ (Fin 8)) ∈ Metric.ball 0 ρ₀ := by
    rw [Metric.mem_ball, dist_self]; exact hρ₀pos
  obtain ⟨τ, hτint, hτR⟩ := Metric.mem_closure_iff.mp (hdenseint h0mem) R hRpos
  have hτR' : ‖τ‖ < R := by simpa [dist_eq_norm] using hτR
  have hτS : ∀ i, τ ∈ Sg i := fun i => Set.mem_iInter.mp hτint i
  refine ⟨τ, lt_of_lt_of_le hτR' hRε, ?_⟩
  -- ## 4. the conclusion
  intro y hy hyM
  by_cases hcol : ftS y < δ ∨ 1 - δ < ftS y
  · exact PPRegAt_ppShift_of_collar hΞ.1 hwleft hwright τ E E' V W hregBase y hy hcol hyM
  · push_neg at hcol
    have hyU := hδ₀sub τ (lt_of_lt_of_le hτR' hRδ) y hy hyM
    rcases hyU with hyU | hyU
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyU
      have hτi : ‖τ‖ < δ' i := lt_of_lt_of_le hτR' (le_trans hRδ' (hδ'₀le i))
      have hcall := htrans i τ (hτS i).1 (hτS i).2
      have hEtsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
          (fun z : EuclideanSpace ℝ (Fin 9) => ppShift Ξ w (unpackFst τ) E (ftS z) (ftU z)) := by
        show ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
          (fun z : EuclideanSpace ℝ (Fin 9) =>
            Ξ (w (ftS z) • unpackFst τ) (E (ftS z) (ftU z)))
        refine hΞ.2.1.comp (ContMDiff.prodMk ?_ ?_)
        · rw [contMDiff_iff_contDiff]
          exact ContDiff.smul (hw.comp (by
            show ContDiff ℝ Ctop (fun z : EuclideanSpace ℝ (Fin 9) => z 0)
            fun_prop)) contDiff_const
        · exact contMDiff_composed_of hE
      have hEt'sm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
          (fun z : EuclideanSpace ℝ (Fin 9) => ppShift Ξ w (unpackSnd τ) E' (ftS z) (ftU z)) := by
        show ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
          (fun z : EuclideanSpace ℝ (Fin 9) =>
            Ξ (w (ftS z) • unpackSnd τ) (E' (ftS z) (ftU z)))
        refine hΞ.2.1.comp (ContMDiff.prodMk ?_ ?_)
        · rw [contMDiff_iff_contDiff]
          exact ContDiff.smul (hw.comp (by
            show ContDiff ℝ Ctop (fun z : EuclideanSpace ℝ (Fin 9) => z 0)
            fun_prop)) contDiff_const
        · exact contMDiff_composed_of hE'
      have hmeetP : y ∈ ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W :=
        hyM
      have hsplit : y ∈ Submission.Drive.unitBox 8 ∧
          ppShift Ξ w (unpackFst τ) E (ftS y) (ftU y) = V (ftY y) ∧
          ppShift Ξ w (unpackSnd τ) E' (ftS y) (ftU y) = W (ftZ y) := hmeetP
      obtain ⟨hm1, hm2, hm3⟩ := hsplit
      have hresSelf : y ∈ ppRegion
          (ppShift Ξ w (unpackFst τ) E (ftS y) (ftU y))
          (ppShift Ξ w (unpackSnd τ) E' (ftS y) (ftU y))
          (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W := by
        have h1 : ppShift Ξ w (unpackFst τ) E (ftS y) (ftU y) ∈
            (chr (ppShift Ξ w (unpackFst τ) E (ftS y) (ftU y))).source := mem_chart_source _ _
        have h2 : ppShift Ξ w (unpackSnd τ) E' (ftS y) (ftU y) ∈
            (chr (ppShift Ξ w (unpackSnd τ) E' (ftS y) (ftU y))).source := mem_chart_source _ _
        exact ⟨h1, by rw [← hm2]; exact h1, h2, by rw [← hm3]; exact h2⟩
      have hresPiece : y ∈ ppRegion (E (ftS (x i)) (ftU (x i))) (E' (ftS (x i)) (ftU (x i)))
          (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W :=
        hres i τ y hτi (interior_subset hi)
      obtain ⟨hreg, hface⟩ := PPRegAt_chart_indep hEtsm hEt'sm
        (contMDiff_comp_ftY hV) (contMDiff_comp_ftZ hW) hmeetP hresSelf hresPiece
      have hzero : ppDiff (E (ftS (x i)) (ftU (x i))) (E' (ftS (x i)) (ftU (x i)))
          (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W y = 0 := by
        have hZ : ppDiff (E (ftS (x i)) (ftU (x i))) (E' (ftS (x i)) (ftU (x i)))
            (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W y
            = pair44 (0 : EuclideanSpace ℝ (Fin 4)) (0 : EuclideanSpace ℝ (Fin 4)) := by
          simp only [ppDiff, hm2, hm3, sub_self]
        rw [hZ]
        apply WithLp.ofLp_injective 2
        funext k
        fin_cases k <;> simp [pair44]
      refine ⟨(hreg).mpr (hcall.1 y (interior_subset hi) hy hzero), ?_⟩
      intro hbdry
      obtain ⟨j, hjface, hjint, hjsurj⟩ := hcall.2 y (interior_subset hi) hy hzero hbdry
      exact ⟨j, hjface, hjint, (hface j hjface).mpr hjsurj⟩
    · rcases hyU with h | h
      · exact absurd h (not_lt.mpr hcol.1)
      · exact absurd h (not_lt.mpr hcol.2)


/-- **S3 (final form): the intrinsic pair Sard with the two collars.**  Same statement as
`exists_ppReg_shift_of_pieces`, with the per-piece localized Sard `Work.Drive.piece_data_pp` supplied
internally in place of the hypothesis `hpd`. -/
theorem exists_ppReg_shift
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace}
    {V W : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    {Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace} {w : ℝ → ℝ}
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hΞ : ChartPert Q 4 Ξ)
    (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K)
    (hwne : ∀ x ∈ K, w (ftS x) ≠ 0)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hKcover : ∀ x ∈ Submission.Drive.unitBox 8, δ ≤ ftS x → ftS x ≤ 1 - δ →
      x ∈ interior K)
    (hwleft : ∀ s : ℝ, s < δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ < s → w s = 0)
    (hregBase : ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      ppMeet E E' V W x → PPRegAt E E' V W x)
    (hpd : ∀ (p p' : CappingSpace) (K' : Set (EuclideanSpace ℝ (Fin 9))) (δ' : ℝ),
      IsCompact K' → 0 < δ' →
      (∀ (τ : EuclideanSpace ℝ (Fin 8)) (y : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ' → y ∈ K' →
        y ∈ ppRegion p p' (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W) →
      (∀ (τ : EuclideanSpace ℝ (Fin 8)) (y : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ' → y ∈ K' →
        ppDiff p p' (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W y = 0 →
        Function.Surjective (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin 8) =>
          ppDiff p p' (ppShift Ξ w (unpackFst τ') E) (ppShift Ξ w (unpackSnd τ') E') V W y) τ)) →
      ∃ (ρ : ℝ) (Ψ : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) →
          EuclideanSpace ℝ (Fin 8)),
        0 < ρ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
        IsOpen {τ : EuclideanSpace ℝ (Fin 8) | ppGoodSet Ψ K' τ} ∧
        (∀ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < ρ → ppGoodSet Ψ K' τ →
          PPChartGood p p' E E' V W Ξ w τ K') ∧
        (∀ τ₀ : EuclideanSpace ℝ (Fin 8), ‖τ₀‖ < ρ → ∀ ε' : ℝ, 0 < ε' →
          ∃ τ : EuclideanSpace ℝ (Fin 8), ‖τ - τ₀‖ < ε' ∧ ‖τ‖ < ρ ∧ ppGoodSet Ψ K' τ))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < ε ∧
      ∀ x ∈ Submission.Drive.unitBox 8,
        ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W x →
        PPRegAt (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W x :=
  exists_ppReg_shift_of_pieces hE hE' hV hW hw hΞ K hK hwne hδ hKcover hwleft hwright hregBase
    (fun p p' K' δ' hK' hδ' hres hsurj =>
      piece_data_pp Ξ hΞ.2.1 w hw hE hE' hV hW p p' K' δ' hK' hδ' hres hsurj) ε hε

end

end Work.Drive
