import Mathlib
import Submission.Work.Drive.ppParity.StripDefs
import Submission.Work.Drive.ppParity.Assembly
import Submission.Work.Drive.ppParity.PPRegAt_ppShift_of_w_eq_zero
import Submission.Work.Drive.ppIntrinsic.PPRegAt_ppShift_of_collarBoundary
import Submission.Work.Drive.ppParity.exists_ppCover_gen
import Submission.Work.Drive.ppParity.surjective_fderiv_ppDiff_shift_gen

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


/-!
# S3 in the **repaired collar convention**, for a general smooth `4`-manifold `M`

**Why this file exists.**  The lemma `Work.Drive.ppParity.exists_ppReg_shift_strip_of_pieces` was
requested with the hypothesis

> `hΞsurj : ∀ t p, Function.Surjective (mfderiv ℝ ℝ (modelWithCornersSelf ℝ (ℝ^4)) (ℝ^4) (fun t' => Ξ t' p) t)`

which does **not typecheck**: `mfderiv` takes its two `ModelWithCorners` arguments first, so `ℝ` in
that position is a type error (a `Type` where a `ModelWithCorners` is expected).  Hence no proof of the
requested statement can exist; the statement has to be read as

> `hΞsurj : ∀ t p, Function.Surjective (mfderiv (modelWithCornersSelf ℝ (ℝ^4)) (modelWithCornersSelf ℝ (ℝ^4)) (fun t' => Ξ t' p) t)`

which is exactly the third conjunct of `Work.Drive.ChartPert` (with `CappingSpace` replaced by `M`),
i.e. unambiguously what was meant.  This module contains the *same theorem*, with that one repair made,
under the name `exists_ppReg_shift_strip_of_pieces_fixed`; it is sorry-free and axiom-clean.  The
requested file `exists_ppReg_shift_strip_of_pieces.lean` contains the same proof under the requested
name (again with the single repair).

The proof is the three-region case analysis of `PPPARITY_COLLAR_DEFECT.md` §2bis:
* `ftS x < δ ∨ 1 - δ < ftS x` — the perturbation is inactive as a germ, `PPRegAt_ppShift_of_collar`;
* `ftS x = δ ∨ ftS x = 1 - δ` — the collar *lines*: `ppIntrinsic.PPRegAt_ppShift_of_collarBoundary`;
* `δ < ftS x < 1 - δ` — the active strip: the piece of the finite cover plus `PieceDataStrip` and
  `PPRegAt_chart_indep`.
-/

namespace Work.Drive.ppParity

open scoped Manifold ContDiff Topology
open Manifold Set Filter

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable section

local notation "Ctop" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- **S3 (repaired, general `M`, per-piece Sard as hypothesis).** -/
theorem exists_ppReg_shift_strip_of_pieces_fixed
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞ0 : ∀ p : M, Ξ 0 p = p)
    (hΞsm : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (hΞsurj : ∀ (t : EuclideanSpace ℝ (Fin 4)) (p : M),
      Function.Surjective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
        (fun t' : EuclideanSpace ℝ (Fin 4) => Ξ t' p) t))
    (w : ℝ → ℝ) (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w) {δ : ℝ}
    (hδ : 0 ≤ δ)
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
    (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K)
    (hwne : ∀ x ∈ K, δ < Work.Drive.ftS x → Work.Drive.ftS x < 1 - δ →
      w (Work.Drive.ftS x) ≠ 0)
    (hKcover : ∀ x ∈ Submission.Drive.unitBox 8, δ ≤ Work.Drive.ftS x →
      Work.Drive.ftS x ≤ 1 - δ → x ∈ interior K)
    (hwleft : ∀ s : ℝ, s ≤ δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ ≤ s → w s = 0)
    (hregBase : ∀ x ∈ Submission.Drive.unitBox 8,
      (Work.Drive.ftS x ≤ δ ∨ 1 - δ ≤ Work.Drive.ftS x) →
      Work.Drive.ppMeet E E' V W x → Work.Drive.PPRegAt E E' V W x)
    (hpdrel : ∀ p p' : M, Work.Drive.PieceDataStrip δ p p' E E' V W Ξ w)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < ε ∧
      ∀ x ∈ Submission.Drive.unitBox 8,
        Work.Drive.ppMeet (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E)
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E') V W x →
        Work.Drive.PPRegAt (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E)
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E') V W x := by
  classical
  -- ## 0. continuity bookkeeping
  have hEc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) =>
      E (Work.Drive.ftS z) (Work.Drive.ftU z)) :=
    (Work.Drive.contMDiff_composed_of hE).continuous
  have hE'c : Continuous (fun z : EuclideanSpace ℝ (Fin 9) =>
      E' (Work.Drive.ftS z) (Work.Drive.ftU z)) :=
    (Work.Drive.contMDiff_composed_of hE').continuous
  have hftS : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => Work.Drive.ftS z) := by
    show Continuous (fun z : EuclideanSpace ℝ (Fin 9) => z 0)
    fun_prop
  have hftY : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => Work.Drive.ftY z) := by
    show Continuous (fun z : EuclideanSpace ℝ (Fin 9) =>
      WithLp.toLp 2 (fun i : Fin 3 => z ⟨3 + i.val, by omega⟩))
    fun_prop
  have hftZ : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => Work.Drive.ftZ z) := by
    show Continuous (fun z : EuclideanSpace ℝ (Fin 9) =>
      WithLp.toLp 2 (fun i : Fin 3 => z ⟨6 + i.val, by omega⟩))
    fun_prop
  have hVc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => V (Work.Drive.ftY z)) :=
    hV.continuous.comp hftY
  have hWc : Continuous (fun z : EuclideanSpace ℝ (Fin 9) => W (Work.Drive.ftZ z)) :=
    hW.continuous.comp hftZ
  have hΞc : Continuous (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2) := hΞsm.continuous
  have hPc : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      Work.Drive.ppShift Ξ w (Work.Drive.unpackFst q.1) E
        (Work.Drive.ftS q.2) (Work.Drive.ftU q.2)) := by
    show Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      Ξ (w (Work.Drive.ftS q.2) • Work.Drive.unpackFst q.1)
        (E (Work.Drive.ftS q.2) (Work.Drive.ftU q.2)))
    refine hΞc.comp (Continuous.prodMk ?_ ?_)
    · exact (hw.continuous.comp (hftS.comp continuous_snd)).smul
        (Work.Drive.unpackFst.continuous.comp continuous_fst)
    · exact hEc.comp continuous_snd
  have hPc' : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd q.1) E'
        (Work.Drive.ftS q.2) (Work.Drive.ftU q.2)) := by
    show Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      Ξ (w (Work.Drive.ftS q.2) • Work.Drive.unpackSnd q.1)
        (E' (Work.Drive.ftS q.2) (Work.Drive.ftU q.2)))
    refine hΞc.comp (Continuous.prodMk ?_ ?_)
    · exact (hw.continuous.comp (hftS.comp continuous_snd)).smul
        (Work.Drive.unpackSnd.continuous.comp continuous_fst)
    · exact hE'c.comp continuous_snd
  have hVc2 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      V (Work.Drive.ftY q.2)) := hVc.comp continuous_snd
  have hWc2 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
      W (Work.Drive.ftZ q.2)) := hWc.comp continuous_snd
  -- ## 1. the finite cover of the closed-slab part of the base pair locus
  obtain ⟨ι, hι, x, K', δ', hK'c, hδ'pos, hxm, hK'sub, hres, hcover⟩ : ∃ (ι : Type)
      (_ : Fintype ι) (x : ι → EuclideanSpace ℝ (Fin 9))
      (K' : ι → Set (EuclideanSpace ℝ (Fin 9))) (δ' : ι → ℝ),
      (∀ i, IsCompact (K' i)) ∧ (∀ i, 0 < δ' i) ∧
      (∀ i, x i ∈ Work.Drive.ppMeet E E' V W) ∧ (∀ i, K' i ⊆ K) ∧
      (∀ (i : ι) (τ : EuclideanSpace ℝ (Fin 8)) (y : EuclideanSpace ℝ (Fin 9)),
        ‖τ‖ < δ' i → y ∈ K' i →
        y ∈ Work.Drive.ppRegion (E (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i)))
          (E' (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i)))
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E)
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E') V W) ∧
      (∀ y ∈ Submission.Drive.unitBox 8, δ ≤ Work.Drive.ftS y →
        Work.Drive.ftS y ≤ 1 - δ →
        y ∈ Work.Drive.ppMeet E E' V W → ∃ i, y ∈ interior (K' i)) := by
    exact exists_ppCover_gen (Ξ := Ξ) hEc hE'c hVc hWc hΞc hw.continuous hΞ0 hK hKcover
  letI : Fintype ι := hι
  -- ## 2. the per-piece localized Sard, from `hpdrel`
  have hpd : ∀ i : ι, ∃ (ρ : ℝ) (Ψ : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) →
      EuclideanSpace ℝ (Fin 8)), 0 < ρ ∧ ContDiff ℝ Ctop Ψ ∧
      IsOpen {τ : EuclideanSpace ℝ (Fin 8) |
        Work.Drive.ppGoodSet Ψ (K' i) τ} ∧
      (∀ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < ρ → Work.Drive.ppGoodSet Ψ (K' i) τ →
        Work.Drive.PPChartGoodStrip δ (E (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i)))
          (E' (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i))) E E' V W Ξ w τ (K' i)) ∧
      (∀ τ₀ : EuclideanSpace ℝ (Fin 8), ‖τ₀‖ < ρ → ∀ ε' : ℝ, 0 < ε' →
        ∃ τ : EuclideanSpace ℝ (Fin 8), ‖τ - τ₀‖ < ε' ∧ ‖τ‖ < ρ ∧
          Work.Drive.ppGoodSet Ψ (K' i) τ) := by
    intro i
    exact hpdrel (E (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i)))
      (E' (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i))) (K' i) (δ' i) (hK'c i) (hδ'pos i)
      (fun τ y hτ hy => hres i τ y hτ hy)
      (fun τ y hτ hy hzero hs1 hs2 => by
        -- `Work.Drive.ppParity.surjective_fderiv_ppDiff_shift_gen` (delegated, in flight)
        exact surjective_fderiv_ppDiff_shift_gen hΞsm hΞsurj w τ y
          (E (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i)))
          (E' (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i)))
          (hres i τ y hτ hy).1 (hres i τ y hτ hy).2.2.1
          (hwne y (hK'sub i hy) hs1 hs2))
  choose ρ Ψ hρpos hΨsm hΨopen htrans hdense using hpd
  -- ## 3. the collar-boundary radius
  obtain ⟨η, hηpos, hηprop⟩ : ∃ η : ℝ, 0 < η ∧
      ∀ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < η →
        ∀ x ∈ Work.Drive.ppMeet (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
            (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W,
          (Work.Drive.ftS x = δ ∨ Work.Drive.ftS x = 1 - δ) →
          Work.Drive.PPRegAt (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst t) E)
            (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd t) E') V W x :=
    Work.Drive.ppIntrinsic.PPRegAt_ppShift_of_collarBoundary Ξ hΞ0 hΞsm E E' V W hE hE' hV hW hw
      hwleft hwright (fun x hm hc => hregBase x (Work.Drive.mem_ppMeet.mp hm).1 hc hm)
  -- ## 4. one common parameter: the finitely many piece good sets
  obtain ⟨ρ₀, hρ₀pos, hρ₀le⟩ := Work.Drive.exists_pos_le_all ρ hρpos
  obtain ⟨δ'₀, hδ'₀pos, hδ'₀le⟩ := Work.Drive.exists_pos_le_all δ' hδ'pos
  set U : Set (EuclideanSpace ℝ (Fin 9)) := (⋃ i, interior (K' i)) ∪
    {y : EuclideanSpace ℝ (Fin 9) | Work.Drive.ftS y < δ ∨ 1 - δ < Work.Drive.ftS y}
    with hUdef
  have hUopen : IsOpen U := by
    refine IsOpen.union (isOpen_iUnion fun i => isOpen_interior) ?_
    exact (isOpen_lt hftS continuous_const).union (isOpen_lt continuous_const hftS)
  have hUbase : ∀ y ∈ Submission.Drive.unitBox 8, y ∈ Work.Drive.ppMeet E E' V W → y ∈ U := by
    intro y hy hyM
    by_cases hc : Work.Drive.ftS y < δ ∨ 1 - δ < Work.Drive.ftS y
    · exact Or.inr hc
    · push_neg at hc
      exact Or.inl (Set.mem_iUnion.mpr (hcover y hy hc.1 hc.2 hyM))
  have hev := Work.Drive.eventually_ppMeet_subset_of_isOpen (Ξ := Ξ) hPc hPc' hVc2 hWc2 hΞ0
    hw.continuous hUopen hUbase
  obtain ⟨δ₀, hδ₀pos, hδ₀sub⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < δ₀ → ∀ y ∈ Submission.Drive.unitBox 8,
        y ∈ Work.Drive.ppMeet (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E)
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E') V W →
        y ∈ U := by
    rw [Filter.eventually_iff, Metric.mem_nhds_iff] at hev
    obtain ⟨δ₀, hδ₀pos, hsub⟩ := hev
    exact ⟨δ₀, hδ₀pos, fun τ hτ y hy hM =>
      hsub (by rwa [Metric.mem_ball, dist_zero_right]) y hy hM⟩
  set Sg : ι → Set (EuclideanSpace ℝ (Fin 8)) :=
    fun i => {τ | ‖τ‖ < ρ i ∧ Work.Drive.ppGoodSet (Ψ i) (K' i) τ} with hSgdef
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
  have hdenseint := Work.Drive.pp_dense_iInter_of_dense_ball Sg ρ₀ hSgopen hSgdense
  set R : ℝ := min ε (min η (min ρ₀ (min δ₀ δ'₀))) with hRdef
  have hRpos : 0 < R := by
    rw [hRdef]
    exact lt_min hε (lt_min hηpos (lt_min hρ₀pos (lt_min hδ₀pos hδ'₀pos)))
  have hRε : R ≤ ε := by rw [hRdef]; exact min_le_left _ _
  have hRη : R ≤ η := by
    rw [hRdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hRρ : R ≤ ρ₀ := by
    rw [hRdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRδ : R ≤ δ₀ := by
    rw [hRdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hRδ' : R ≤ δ'₀ := by
    rw [hRdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _)))
  have h0mem : (0 : EuclideanSpace ℝ (Fin 8)) ∈ Metric.ball 0 ρ₀ := by
    rw [Metric.mem_ball, dist_self]; exact hρ₀pos
  obtain ⟨τ, hτint, hτR⟩ := Metric.mem_closure_iff.mp (hdenseint h0mem) R hRpos
  have hτR' : ‖τ‖ < R := by simpa [dist_eq_norm] using hτR
  have hτS : ∀ i, τ ∈ Sg i := fun i => Set.mem_iInter.mp hτint i
  refine ⟨τ, lt_of_lt_of_le hτR' hRε, ?_⟩
  -- ## 5. the three regions
  intro y hy hyM
  by_cases hcol : Work.Drive.ftS y < δ ∨ 1 - δ < Work.Drive.ftS y
  · -- the open collar: the perturbation is inactive as a germ
    exact Work.Drive.PPRegAt_ppShift_of_collar hΞ0 (fun s hs => hwleft s hs.le)
      (fun s hs => hwright s hs.le) τ E E' V W
      (fun x hx hxc hxm => hregBase x hx (hxc.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)) hxm)
      y hy hcol hyM
  · push_neg at hcol
    by_cases hline : Work.Drive.ftS y = δ ∨ Work.Drive.ftS y = 1 - δ
    · -- the collar lines
      exact hηprop τ (lt_of_lt_of_le hτR' hRη) y hyM hline
    · push_neg at hline
      have hs1 : δ < Work.Drive.ftS y := lt_of_le_of_ne hcol.1 (Ne.symm hline.1)
      have hs2 : Work.Drive.ftS y < 1 - δ := lt_of_le_of_ne hcol.2 hline.2
      -- ## 5b. the active strip: the piece data
      have hyU' : y ∈ U := hδ₀sub τ (lt_of_lt_of_le hτR' hRδ) y hy hyM
      have hnotcollar : ¬ (Work.Drive.ftS y < δ ∨ 1 - δ < Work.Drive.ftS y) :=
        fun h => h.elim (fun h1 => absurd h1 (not_lt.mpr hcol.1))
          (fun h2 => absurd h2 (not_lt.mpr hcol.2))
      have hyU : y ∈ ⋃ i, interior (K' i) := by
        rw [hUdef, Set.mem_union] at hyU'
        exact hyU'.elim id (fun h =>
          absurd (by simpa only [Set.mem_setOf_eq] using h) hnotcollar)
      · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyU
        have hτi : ‖τ‖ < δ' i := lt_of_lt_of_le hτR' (le_trans hRδ' (hδ'₀le i))
        have hcall := htrans i τ (hτS i).1 (hτS i).2
        have hEtsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
            (fun z : EuclideanSpace ℝ (Fin 9) =>
              Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E
                (Work.Drive.ftS z) (Work.Drive.ftU z)) :=
          Work.Drive.contMDiff_composed_of (Work.Drive.contMDiff_ppShift Ξ hΞsm hw
            (Work.Drive.unpackFst τ) E hE)
        have hEt'sm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
            (fun z : EuclideanSpace ℝ (Fin 9) =>
              Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E'
                (Work.Drive.ftS z) (Work.Drive.ftU z)) :=
          Work.Drive.contMDiff_composed_of (Work.Drive.contMDiff_ppShift Ξ hΞsm hw
            (Work.Drive.unpackSnd τ) E' hE')
        obtain ⟨hm1, hm2, hm3⟩ := Work.Drive.mem_ppMeet.mp hyM
        have hresSelf : y ∈ Work.Drive.ppRegion
            (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E
              (Work.Drive.ftS y) (Work.Drive.ftU y))
            (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E'
              (Work.Drive.ftS y) (Work.Drive.ftU y))
            (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E)
            (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E') V W := by
          have h1 : Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E
              (Work.Drive.ftS y) (Work.Drive.ftU y) ∈
              (Work.Drive.chr (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E
                (Work.Drive.ftS y) (Work.Drive.ftU y))).source := mem_chart_source _ _
          have h2 : Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E'
              (Work.Drive.ftS y) (Work.Drive.ftU y) ∈
              (Work.Drive.chr (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E'
                (Work.Drive.ftS y) (Work.Drive.ftU y))).source := mem_chart_source _ _
          exact ⟨h1, by rw [← hm2]; exact h1, h2, by rw [← hm3]; exact h2⟩
        have hresPiece : y ∈ Work.Drive.ppRegion
            (E (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i)))
            (E' (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i)))
            (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E)
            (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E') V W :=
          hres i τ y hτi (interior_subset hi)
        obtain ⟨hreg, hface⟩ := Work.Drive.PPRegAt_chart_indep hEtsm hEt'sm
          (Work.Drive.contMDiff_comp_ftY hV) (Work.Drive.contMDiff_comp_ftZ hW)
          hyM hresSelf hresPiece
        have hzero : Work.Drive.ppDiff (E (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i)))
            (E' (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i)))
            (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E)
            (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E') V W y = 0 := by
          have hZ : Work.Drive.ppDiff (E (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i)))
              (E' (Work.Drive.ftS (x i)) (Work.Drive.ftU (x i)))
              (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E)
              (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E') V W y
              = pair44 (0 : EuclideanSpace ℝ (Fin 4)) (0 : EuclideanSpace ℝ (Fin 4)) := by
            simp only [Work.Drive.ppDiff, hm2, hm3, sub_self]
          rw [hZ]
          apply WithLp.ofLp_injective 2
          funext k
          fin_cases k <;> simp [pair44]
        refine ⟨(hreg).mpr (hcall.1 y (interior_subset hi) hy hs1 hs2 hzero), ?_⟩
        intro hbdry
        obtain ⟨j, hjface, hjint, hjsurj⟩ := hcall.2 y (interior_subset hi) hy hs1 hs2 hzero hbdry
        exact ⟨j, hjface, hjint, (hface j hjface).mpr hjsurj⟩

end

end Work.Drive.ppParity
