import Mathlib
import Submission.Work.Drive.ppParity.Good
import Submission.Work.Drive.ppParity.Richness
import Submission.Work.Drive.exists_forall_good_face_and_notMem_family
import Submission.Work.Drive.exists_meet3Data_of_good_family
import Submission.Work.Drive.ppBdry.Basic
import Submission.Work.Drive.ppParity.contDiffAt_ppDiff_family2

/-!
# The piece data of the localized pair Sard

This is the pair analogue of the private `Work.Drive.piece_data` of
`Submission/Work/Drive/localSard.lean`: for one chart pair `(p, p')`, one compact set `K` and a
radius `δ` on which the charts contain all four values, there is a globally smooth cut-off pair
system `Ψ` whose good parameters on `K` are

* *dense* near every parameter of the ball of radius `ρ = δ/8` (the parametric Sard of
  `Work.Drive.exists_forall_good_face_and_notMem_family`, applied to the shifted cut-off system), and
* *contained* in the intrinsic good parameters of the pair family on `K` (the cut-off derivative
  identity at a zero).

The proof is the S3 port prescribed by `Submission/Work/Drive/NOTES_LEAD_residency.md`: the cut-off
`(γ, β)` of `Work.Drive.exists_meet3Data_of_good_family`, with `chartDiff3` replaced by `ppDiff` and
`GoodSet`/`GoodChart` by `ppGoodSet`/`PPChartGood`.

Contents, in order:

1. `Work.Drive.ppFam` — the charted pair family as a function of the parameter;
2. the two coordinate facts of the nine-box (`continuous_ftS` … `contDiff_ftSU`);
3. the cut-off existence `exists_cutoff_tsupport_subset` (a copy of the private helper of
   `Work.Drive.exists_meet3Data_of_good_family`) and the `tsupport`-vanishing lemma;
4. the block/coordinate dictionary of the nine-box (`bIdx_eq_iff`, `mem_Ioo_of_mem_unitBox_of_notFace`,
   `forall_ne_bIdx_of_block`);
5. the cut-off calculus at a zero (`hasFDerivAt_cutoff_snd`, `hasFDerivAt_cutoff_fst`): if the cut-off
   equals `1` at the point and the map vanishes there, then the derivative of the product is that of
   the map;
6. `Work.Drive.contDiff_ppCut` — global smoothness of `Ψ = (γ ∘ fst) * (β ∘ snd) • ppFam`, from the
   joint smoothness `Work.Drive.ppParity.contDiffAt_ppDiff_family2` of the pair family on the
   residency region;
7. `Work.Drive.PPChartGood_of_ppGoodSet` — the transfer from the block form of the good set to the
   coordinate form `PPChartGood`;
8. the target `Work.Drive.piece_data_pp`.

Only the delegated input `Work.Drive.ppParity.contDiffAt_ppDiff_family2` (`Submission/Work/Drive/ppParity/contDiffAt_ppDiff_family2.lean`,
proved) is used from outside; the density clause is the parametric Sard
`Work.Drive.exists_forall_good_face_and_notMem_family` applied to the *translated* cut-off system
`q ↦ Ψ (τ₀ + q.1, q.2)`, whose `hsurj` hypothesis is supplied by the hypothesis `hsurj` of the target
through `hasFDerivAt_cutoff_fst` and the chain rule.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set

set_option maxHeartbeats 1000000

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## 1. The pair family of the localized pair Sard -/

/-- **The charted pair family of the pair Sard at the parameter `τ`**: the pair difference map of the
two intrinsically perturbed `(s, u)`-chains and the two sweep chains, in the chart pair `(p, p')`. -/
def ppFam (p p' : M) (Ξ : EuclideanSpace ℝ (Fin 4) → M → M) (w : ℝ → ℝ)
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M) (V W : EuclideanSpace ℝ (Fin 3) → M)
    (τ : EuclideanSpace ℝ (Fin 8)) (y : EuclideanSpace ℝ (Fin 9)) : EuclideanSpace ℝ (Fin 8) :=
  ppDiff p p' (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W y


/-! ## 2. The coordinate maps of the nine-box -/

lemma continuous_ftS : Continuous (fun x : EuclideanSpace ℝ (Fin 9) => ftS x) := by
  show Continuous (fun x : EuclideanSpace ℝ (Fin 9) => x 0)
  fun_prop

lemma continuous_ftU : Continuous (fun x : EuclideanSpace ℝ (Fin 9) => ftU x) := by
  show Continuous (fun x : EuclideanSpace ℝ (Fin 9) =>
    WithLp.toLp 2 (fun i : Fin 2 => x ⟨1 + i.val, by omega⟩))
  fun_prop

lemma continuous_ftY : Continuous (fun x : EuclideanSpace ℝ (Fin 9) => ftY x) := by
  show Continuous (fun x : EuclideanSpace ℝ (Fin 9) =>
    WithLp.toLp 2 (fun i : Fin 3 => x ⟨3 + i.val, by omega⟩))
  fun_prop

lemma continuous_ftZ : Continuous (fun x : EuclideanSpace ℝ (Fin 9) => ftZ x) := by
  show Continuous (fun x : EuclideanSpace ℝ (Fin 9) =>
    WithLp.toLp 2 (fun i : Fin 3 => x ⟨6 + i.val, by omega⟩))
  fun_prop

lemma continuous_ftSU : Continuous (fun x : EuclideanSpace ℝ (Fin 9) => (ftS x, ftU x)) :=
  continuous_ftS.prodMk continuous_ftU

lemma contDiff_ftSU : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun x : EuclideanSpace ℝ (Fin 9) => (ftS x, ftU x)) := by
  refine ContDiff.prodMk ?_ ?_
  · show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : EuclideanSpace ℝ (Fin 9) => x 0)
    fun_prop
  · show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : EuclideanSpace ℝ (Fin 9) =>
      WithLp.toLp 2 (fun i : Fin 2 => x ⟨1 + i.val, by omega⟩))
    fun_prop

/-! ## 2b. Two small inputs of the argument -/

/-- The order `⊤` is not zero. -/
lemma top_ne_zero_order : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- **A smooth function that is `1` on a compact set and supported in an open set containing it.** -/
lemma exists_cutoff_tsupport_subset {n : ℕ} {K V : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧
      (∀ x ∈ K, f x = 1) ∧ tsupport f ⊆ V := by
  classical
  have hpt : ∀ x : K, ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (x : EuclideanSpace ℝ (Fin n)) (2 * r) ⊆ V := by
    intro x
    obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (hKV x.2))
    refine ⟨r / 4, by linarith, ?_⟩
    intro z hz
    apply hrsub
    rw [Metric.mem_ball]
    have h := Metric.mem_closedBall.mp hz
    linarith
  choose r hrpos hrsub using hpt
  have hbump : ∀ x : K, ∃ b : ContDiffBump (x : EuclideanSpace ℝ (Fin n)),
      b.rIn = r x ∧ b.rOut = 2 * r x := fun x =>
    ⟨⟨r x, 2 * r x, hrpos x, by linarith [hrpos x]⟩, rfl, rfl⟩
  choose b hb1 hb2 using hbump
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => Metric.ball (x : EuclideanSpace ℝ (Fin n)) (r x))
    (fun _ => Metric.isOpen_ball)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hrpos ⟨x, hx⟩)⟩)
  refine ⟨fun y => 1 - ∏ x ∈ s, (1 - b x y), ?_, ?_, ?_⟩
  · have hcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun y : EuclideanSpace ℝ (Fin n) => ∏ x ∈ s, (1 - b x y)) :=
      contDiff_prod (𝕜 := ℝ) (𝔸' := ℝ)
        (fun x _ => contDiff_const.sub (b x).contDiff)
    exact contDiff_const.sub hcont
  · intro y hy
    obtain ⟨x, hxs, hxy⟩ := Set.mem_iUnion₂.mp (hs hy)
    have hbx : b x y = 1 := by
      refine (b x).one_of_mem_closedBall ?_
      rw [hb1 x, Metric.mem_closedBall]
      exact le_of_lt (Metric.mem_ball.mp hxy)
    have hz : (1 - b x y) = 0 := by rw [hbx]; ring
    show 1 - ∏ x ∈ s, (1 - b x y) = 1
    rw [Finset.prod_eq_zero hxs hz]
    ring
  · have hsupp : Function.support (fun y => 1 - ∏ x ∈ s, (1 - b x y)) ⊆
        ⋃ x ∈ s, tsupport (⇑(b x)) := by
      intro y hy
      by_contra hcon
      have h1 : (∏ x ∈ s, (1 - b x y)) = 1 :=
        Finset.prod_eq_one (fun x hx => by
          have hb0 : b x y = 0 := by
            by_contra hne
            exact hcon (Set.mem_iUnion₂.mpr ⟨x, hx, subset_tsupport _ hne⟩)
          rw [hb0]; ring)
      simp only [Function.mem_support, ne_eq] at hy
      exact hy (by rw [h1]; ring)
    have hclosed : IsClosed (⋃ x ∈ s, tsupport (⇑(b x))) :=
      isClosed_biUnion_finset (fun x _ => isClosed_tsupport _)
    calc tsupport (fun y => 1 - ∏ x ∈ s, (1 - b x y))
        = closure (Function.support (fun y => 1 - ∏ x ∈ s, (1 - b x y))) := rfl
      _ ⊆ closure (⋃ x ∈ s, tsupport (⇑(b x))) := closure_mono hsupp
      _ = ⋃ x ∈ s, tsupport (⇑(b x)) := hclosed.closure_eq
      _ ⊆ V := by
          rintro z hz
          obtain ⟨x, hxs, hxz⟩ := Set.mem_iUnion₂.mp hz
          exact hrsub x (by rw [(b x).tsupport_eq, hb2 x] at hxz; exact hxz)

/-- A point outside the topological support of `f` has a neighbourhood on which `f` vanishes. -/
lemma eventually_eq_zero_of_notMem_tsupport {X Y : Type*} [TopologicalSpace X] [Zero Y]
    {f : X → Y} {x : X} (h : x ∉ tsupport f) : ∀ᶠ y in 𝓝 x, f y = 0 := by
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  refine Filter.mem_of_superset (hopen.mem_nhds (by simpa using h)) ?_
  intro y hy
  by_contra hne
  exact hy (subset_tsupport f hne)

/-! ## 3. The block/coordinate dictionary of the nine-box -/

/-- The block index of the nine-box is injective in both arguments. -/
lemma bIdx_eq_iff {k k' i i' : Fin 3} : bIdx k i = bIdx k' i' ↔ k = k' ∧ i = i' := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [bIdx_val, bIdx_val] at hv
    have hk : k.val < 3 := k.isLt
    have hk' : k'.val < 3 := k'.isLt
    have hi : i.val < 3 := i.isLt
    have hi' : i'.val < 3 := i'.isLt
    constructor <;> (apply Fin.ext; omega)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A box coordinate that is not on a face is strictly interior. -/
lemma mem_Ioo_of_mem_unitBox_of_notFace {y : EuclideanSpace ℝ (Fin 9)}
    (hy : y ∈ Submission.Drive.unitBox 8) {i : Fin 9}
    (h : ¬ (y i = 0 ∨ y i = 1)) : y i ∈ Set.Ioo (0 : ℝ) 1 := by
  have hI := hy i
  simp only [not_or] at h
  exact ⟨lt_of_le_of_ne hI.1 (Ne.symm h.1), lt_of_le_of_ne hI.2 h.2⟩

/-- **The block form of "strictly interior in every coordinate except one" implies the coordinate
form.** -/
lemma forall_ne_bIdx_of_block {y : EuclideanSpace ℝ (Fin 9)} {k i : Fin 3}
    (h1 : ∀ j : Fin 3, j ≠ i → y (bIdx k j) ∈ Set.Ioo (0 : ℝ) 1)
    (h2 : ∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, y (bIdx k' j) ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ m : Fin 9, m ≠ bIdx k i → y m ∈ Set.Ioo (0 : ℝ) 1 := by
  intro m hm
  obtain ⟨k', i', rfl⟩ := exists_bIdx_eq m
  by_cases hkk : k' = k
  · subst hkk
    exact h1 i' (fun hii => hm (by rw [hii]))
  · exact h2 k' hkk i'

/-! ## 4. Cut-off calculus at a zero -/

/-- **The derivative in the `y`-variable of a cut-off multiple of a smooth map at a zero.** -/
lemma hasFDerivAt_cutoff_snd {F : EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8)}
    {γ : EuclideanSpace ℝ (Fin 8) → ℝ} {β : EuclideanSpace ℝ (Fin 9) → ℝ}
    {τ : EuclideanSpace ℝ (Fin 8)} {y : EuclideanSpace ℝ (Fin 9)}
    (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hF : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F y)
    (hγτ : γ τ = 1) (hβy : β y = 1) (hFy : F y = 0) :
    HasFDerivAt (fun y' : EuclideanSpace ℝ (Fin 9) => (γ τ * β y') • F y') (fderiv ℝ F y) y := by
  have hβd : HasFDerivAt β (fderiv ℝ β y) y :=
    (hβ.contDiffAt.differentiableAt top_ne_zero_order).hasFDerivAt
  have hc : HasFDerivAt (fun _ : EuclideanSpace ℝ (Fin 9) => γ τ)
      (0 : EuclideanSpace ℝ (Fin 9) →L[ℝ] ℝ) y := hasFDerivAt_const _ _
  have hβa : HasFDerivAt (fun y' : EuclideanSpace ℝ (Fin 9) => γ τ * β y')
      ((γ τ) • fderiv ℝ β y + β y • (0 : EuclideanSpace ℝ (Fin 9) →L[ℝ] ℝ)) y := hc.mul hβd
  have hFa : HasFDerivAt F (fderiv ℝ F y) y :=
    (hF.differentiableAt top_ne_zero_order).hasFDerivAt
  have h := hβa.smul hFa
  have h1 : (γ τ * β y) • fderiv ℝ F y
      + ((γ τ) • fderiv ℝ β y + β y • (0 : EuclideanSpace ℝ (Fin 9) →L[ℝ] ℝ)).smulRight (F y)
      = fderiv ℝ F y := by
    rw [hγτ, hβy, hFy, ContinuousLinearMap.smulRight_zero]
    simp
  rw [h1] at h
  exact h

/-- **The derivative in the `τ`-variable of a cut-off multiple of a smooth map at a zero.** -/
lemma hasFDerivAt_cutoff_fst {F : EuclideanSpace ℝ (Fin 8) → EuclideanSpace ℝ (Fin 8)}
    {γ : EuclideanSpace ℝ (Fin 8) → ℝ} {β : EuclideanSpace ℝ (Fin 9) → ℝ}
    {τ : EuclideanSpace ℝ (Fin 8)} {y : EuclideanSpace ℝ (Fin 9)}
    (hγ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hF : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F τ)
    (hγτ : γ τ = 1) (hβy : β y = 1) (hFy : F τ = 0) :
    HasFDerivAt (fun τ' : EuclideanSpace ℝ (Fin 8) => (γ τ' * β y) • F τ') (fderiv ℝ F τ) τ := by
  have hγd : HasFDerivAt γ (fderiv ℝ γ τ) τ :=
    (hγ.contDiffAt.differentiableAt top_ne_zero_order).hasFDerivAt
  have hc : HasFDerivAt (fun _ : EuclideanSpace ℝ (Fin 8) => β y)
      (0 : EuclideanSpace ℝ (Fin 8) →L[ℝ] ℝ) τ := hasFDerivAt_const _ _
  have hγa : HasFDerivAt (fun τ' : EuclideanSpace ℝ (Fin 8) => γ τ' * β y)
      (γ τ • (0 : EuclideanSpace ℝ (Fin 8) →L[ℝ] ℝ) + β y • fderiv ℝ γ τ) τ := hγd.mul hc
  have hFa : HasFDerivAt F (fderiv ℝ F τ) τ :=
    (hF.differentiableAt top_ne_zero_order).hasFDerivAt
  have h := hγa.smul hFa
  have h1 : (γ τ * β y) • fderiv ℝ F τ
      + (γ τ • (0 : EuclideanSpace ℝ (Fin 8) →L[ℝ] ℝ) + β y • fderiv ℝ γ τ).smulRight (F τ)
      = fderiv ℝ F τ := by
    rw [hγτ, hβy, hFy, ContinuousLinearMap.smulRight_zero]
    simp
  rw [h1] at h
  exact h


/-! ## 5. Smoothness of the cut-off pair system -/

/-- **The cut-off pair system is globally smooth**: the product of the two cut-offs with the pair
family is `C^∞` as soon as the pair family is smooth on `U ×ˢ S` (which contains the topological
support of the product). -/
lemma contDiff_ppCut
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞsm : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (w : ℝ → ℝ) (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (V W : EuclideanSpace ℝ (Fin 3) → M)
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (p p' : M)
    {γ : EuclideanSpace ℝ (Fin 8) → ℝ} (hγ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {β : EuclideanSpace ℝ (Fin 9) → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    {U : Set (EuclideanSpace ℝ (Fin 8))} {S : Set (EuclideanSpace ℝ (Fin 9))}
    (hUV : U ×ˢ S ⊆ {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
      q.2 ∈ ppRegion p p' (ppShift Ξ w (unpackFst q.1) E) (ppShift Ξ w (unpackSnd q.1) E') V W})
    (hγsupp : tsupport γ ⊆ U) (hβsupp : tsupport β ⊆ S) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
        (γ q.1 * β q.2) • ppFam p p' Ξ w E E' V W q.1 q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  by_cases hγ0 : q₀.1 ∈ tsupport γ
  · by_cases hβ0 : q₀.2 ∈ tsupport β
    · have hreg := hUV ⟨hγsupp hγ0, hβsupp hβ0⟩
      have hχ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
            ppFam p p' Ξ w E E' V W q.1 q.2) q₀ := by
        simpa only [ppFam] using
          ppParity.contDiffAt_ppDiff_family2 (Ξ := Ξ) hΞsm w hw hE hE' hV hW p p' q₀.1 (y₀ := q₀.2) hreg
      have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => γ q.1 * β q.2) q₀ :=
        (hγ.contDiffAt.comp q₀ contDiffAt_fst).mul (hβ.contDiffAt.comp q₀ contDiffAt_snd)
      exact hg.smul hχ
    · refine (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin 8)))).congr_of_eventuallyEq ?_
      filter_upwards [(continuous_snd.tendsto q₀).eventually
        (eventually_eq_zero_of_notMem_tsupport hβ0)] with q hq
      show (γ q.1 * β q.2) • ppFam p p' Ξ w E E' V W q.1 q.2 = 0
      rw [hq, mul_zero, zero_smul]
  · refine (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin 8)))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_fst.tendsto q₀).eventually
      (eventually_eq_zero_of_notMem_tsupport hγ0)] with q hq
    show (γ q.1 * β q.2) • ppFam p p' Ξ w E E' V W q.1 q.2 = 0
    rw [hq, zero_mul, zero_smul]

/-! ## 6. The transfer: a good parameter of the cut-off system is a good parameter of the pair
family -/

/-- **The coordinate form of the good set is implied by the block form**, on the cut-off system. -/
lemma PPChartGood_of_ppGoodSet
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M) (w : ℝ → ℝ)
    (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M) (V W : EuclideanSpace ℝ (Fin 3) → M)
    (p p' : M) (τ : EuclideanSpace ℝ (Fin 8)) (K : Set (EuclideanSpace ℝ (Fin 9)))
    {Ψ : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8)}
    (hgood : ppGoodSet Ψ K τ)
    (hfac : ∀ y ∈ K, Ψ (τ, y) = ppFam p p' Ξ w E E' V W τ y)
    (hder : ∀ y ∈ K, Ψ (τ, y) = 0 →
      fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) => Ψ (τ, y')) y
        = fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) => ppFam p p' Ξ w E E' V W τ y') y) :
    PPChartGood p p' E E' V W Ξ w τ K := by
  constructor
  · intro y hyK hybox h0
    have hΨ0 : Ψ (τ, y) = 0 := by rw [hfac y hyK]; simpa only [ppFam] using h0
    have h := hgood.1 y hyK hybox hΨ0
    rw [hder y hyK hΨ0] at h
    simpa only [ppFam] using h
  · intro y hyK hybox h0 hybdry
    have hΨ0 : Ψ (τ, y) = 0 := by rw [hfac y hyK]; simpa only [ppFam] using h0
    obtain ⟨k, i, hbi, hin, hin', hsurj⟩ := hgood.2 y hyK hybox hΨ0 hybdry
    refine ⟨bIdx k i, hbi, forall_ne_bIdx_of_block hin hin', ?_⟩
    rw [hder y hyK hΨ0] at hsurj
    simpa only [ppFam] using hsurj

/-! ## 7. The target -/

theorem piece_data_pp
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞsm : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (w : ℝ → ℝ) (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
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
    (p p' : M) (K : Set (EuclideanSpace ℝ (Fin 9))) (δ : ℝ) (hK : IsCompact K) (hδ : 0 < δ)
    (hres : ∀ (τ : EuclideanSpace ℝ (Fin 8)) (y : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ → y ∈ K →
      y ∈ Work.Drive.ppRegion p p' (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E)
        (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E') V W)
    (hsurj : ∀ (τ : EuclideanSpace ℝ (Fin 8)) (y : EuclideanSpace ℝ (Fin 9)), ‖τ‖ < δ → y ∈ K →
      Work.Drive.ppDiff p p' (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ) E)
        (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ) E') V W y = 0 →
      Function.Surjective (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin 8) =>
        Work.Drive.ppDiff p p' (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ') E)
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ') E') V W y) τ)) :
    ∃ (ρ : ℝ)
      (Ψ : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8)),
      0 < ρ ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ ∧
      IsOpen {τ : EuclideanSpace ℝ (Fin 8) | Work.Drive.ppGoodSet Ψ K τ} ∧
      (∀ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < ρ → Work.Drive.ppGoodSet Ψ K τ →
        Work.Drive.PPChartGood p p' E E' V W Ξ w τ K) ∧
      (∀ τ₀ : EuclideanSpace ℝ (Fin 8), ‖τ₀‖ < ρ → ∀ ε : ℝ, 0 < ε →
        ∃ τ : EuclideanSpace ℝ (Fin 8), ‖τ - τ₀‖ < ε ∧ ‖τ‖ < ρ ∧ Work.Drive.ppGoodSet Ψ K τ) := by
  classical
  set ρ : ℝ := δ / 8 with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; linarith
  -- ## Step 1: the region on which the four values lie in the two chart sources
  set Wres : Set (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9)) :=
    {q | q.2 ∈ ppRegion p p' (ppShift Ξ w (unpackFst q.1) E)
      (ppShift Ξ w (unpackSnd q.1) E') V W} with hWresdef
  have hWres_open : IsOpen Wres := by
    have hcont1 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
        ppShift Ξ w (unpackFst q.1) E (ftS q.2) (ftU q.2)) := by
      have hΞc : Continuous (fun r : EuclideanSpace ℝ (Fin 4) × M => Ξ r.1 r.2) :=
        hΞsm.continuous
      have hftSU : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
          (ftS q.2, ftU q.2)) := continuous_ftSU.comp continuous_snd
      have h1 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
          w (ftS q.2) • unpackFst q.1) := by
        have hw' : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
            w (ftS q.2)) := hw.continuous.comp (continuous_ftS.comp continuous_snd)
        exact hw'.smul (unpackFst.continuous.comp continuous_fst)
      have h2 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
          E (ftS q.2) (ftU q.2)) :=
        hE.continuous.comp hftSU
      have h := hΞc.comp (h1.prodMk h2)
      simpa only [Function.comp_def, ppShift] using h
    have hcont2 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
        V (ftY q.2)) := by
      exact hV.continuous.comp (continuous_ftY.comp continuous_snd)
    have hcont3 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
        ppShift Ξ w (unpackSnd q.1) E' (ftS q.2) (ftU q.2)) := by
      have hΞc : Continuous (fun r : EuclideanSpace ℝ (Fin 4) × M => Ξ r.1 r.2) :=
        hΞsm.continuous
      have hftSU : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
          (ftS q.2, ftU q.2)) := continuous_ftSU.comp continuous_snd
      have h1 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
          w (ftS q.2) • unpackSnd q.1) := by
        have hw' : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
            w (ftS q.2)) := hw.continuous.comp (continuous_ftS.comp continuous_snd)
        exact hw'.smul (unpackSnd.continuous.comp continuous_fst)
      have h2 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
          E' (ftS q.2) (ftU q.2)) :=
        hE'.continuous.comp hftSU
      have h := hΞc.comp (h1.prodMk h2)
      simpa only [Function.comp_def, ppShift] using h
    have hcont4 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
        W (ftZ q.2)) := by
      exact hW.continuous.comp (continuous_ftZ.comp continuous_snd)
    have hS1 : IsOpen {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        ppShift Ξ w (unpackFst q.1) E (ftS q.2) (ftU q.2) ∈ (chr p).source} :=
      hcont1.isOpen_preimage _ (chr p).open_source
    have hS2 : IsOpen {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        V (ftY q.2) ∈ (chr p).source} :=
      hcont2.isOpen_preimage _ (chr p).open_source
    have hS3 : IsOpen {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        ppShift Ξ w (unpackSnd q.1) E' (ftS q.2) (ftU q.2) ∈ (chr p').source} :=
      hcont3.isOpen_preimage _ (chr p').open_source
    have hS4 : IsOpen {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        W (ftZ q.2) ∈ (chr p').source} :=
      hcont4.isOpen_preimage _ (chr p').open_source
    have hEq : Wres = {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        ppShift Ξ w (unpackFst q.1) E (ftS q.2) (ftU q.2) ∈ (chr p).source} ∩
        ({q | V (ftY q.2) ∈ (chr p).source} ∩
        ({q | ppShift Ξ w (unpackSnd q.1) E' (ftS q.2) (ftU q.2) ∈ (chr p').source} ∩
        {q | W (ftZ q.2) ∈ (chr p').source})) := by
      rw [hWresdef]
      ext q
      simp only [ppRegion, Set.mem_ofPred_eq, Set.mem_inter_iff]
    rw [hEq]
    exact hS1.inter (hS2.inter (hS3.inter hS4))
  have hWres_sub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 8)) (δ / 4) ×ˢ K ⊆ Wres := by
    rintro ⟨τ, y⟩ ⟨hτ, hy⟩
    exact hres τ y (by
      have h := Metric.mem_closedBall.mp hτ
      rw [dist_zero_right] at h
      linarith) hy
  -- ## Step 2: the two cut-off functions
  obtain ⟨U, S, hUopen, hSopen, hUsub, hSsub, hUS⟩ :=
    generalized_tube_lemma (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 8)) (δ / 4))
      hK hWres_open hWres_sub
  obtain ⟨γ, hγsm, hγone, hγsupp⟩ :=
    exists_cutoff_tsupport_subset (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 8)) (δ / 4))
      hUopen hUsub
  obtain ⟨β, hβsm, hβone, hβsupp⟩ := exists_cutoff_tsupport_subset hK hSopen hSsub
  -- ## Step 3: the cut-off pair system
  set Ψ : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8) :=
    fun q => (γ q.1 * β q.2) • ppFam p p' Ξ w E E' V W q.1 q.2 with hΨdef
  have hΨsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ψ := by
    rw [hΨdef]
    exact contDiff_ppCut (Ξ := Ξ) hΞsm w hw E E' hE hE' V W hV hW p p' hγsm hβsm hUS hγsupp hβsupp
  have hΨopen : IsOpen {τ : EuclideanSpace ℝ (Fin 8) | ppGoodSet Ψ K τ} :=
    ppGoodSet_open Ψ hΨsm K hK
  refine ⟨ρ, Ψ, hρpos, hΨsm, hΨopen, ?_, ?_⟩
  · -- ## Step 4: a good parameter of `Ψ` is a good parameter of the pair family
    intro τ hτρ hgood
    have hτδ : ‖τ‖ < δ := by rw [hρdef] at hτρ; linarith
    have hγτ : γ τ = 1 := hγone τ (by
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [hρdef] at hτρ
      linarith)
    refine PPChartGood_of_ppGoodSet (Ξ := Ξ) (w := w) (E := E) (E' := E') (V := V) (W := W)
      (p := p) (p' := p') (τ := τ) (K := K) hgood ?_ ?_
    · intro y hyK
      have hβy : β y = 1 := hβone y hyK
      show (γ τ * β y) • ppFam p p' Ξ w E E' V W τ y = ppFam p p' Ξ w E E' V W τ y
      rw [hγτ, hβy, one_mul, one_smul]
    · intro y hyK hΨ0
      have hβy : β y = 1 := hβone y hyK
      have hF0 : ppFam p p' Ξ w E E' V W τ y = 0 := by
        have h : (γ τ * β y) • ppFam p p' Ξ w E E' V W τ y = 0 := hΨ0
        rwa [hγτ, hβy, one_mul, one_smul] at h
      have hFh : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun y' : EuclideanSpace ℝ (Fin 9) => ppFam p p' Ξ w E E' V W τ y') y := by
        have hreg : y ∈ ppRegion p p' (ppShift Ξ w (unpackFst τ) E)
            (ppShift Ξ w (unpackSnd τ) E') V W := hres τ y hτδ hyK
        have hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
              ppFam p p' Ξ w E E' V W q.1 q.2) (τ, y) := by
          simpa only [ppFam] using
            ppParity.contDiffAt_ppDiff_family2 (Ξ := Ξ) hΞsm w hw hE hE' hV hW p p' τ (y₀ := y) hreg
        exact hG.comp y (contDiffAt_const.prodMk contDiffAt_id)
      have h := hasFDerivAt_cutoff_snd (γ := γ) (β := β) hβsm hFh hγτ hβy hF0
      exact h.fderiv
  · -- ## Step 5: the density clause
    intro τ₀ hτ₀ ε hε
    set ε₀ : ℝ := min ε (min (ρ - ‖τ₀‖) (δ / 4 - ‖τ₀‖)) / 2 with hε₀def
    have hδ4 : 0 < δ / 4 - ‖τ₀‖ := by rw [hρdef] at hτ₀; linarith
    have hρm : 0 < ρ - ‖τ₀‖ := by linarith
    have hmin : 0 < min ε (min (ρ - ‖τ₀‖) (δ / 4 - ‖τ₀‖)) := lt_min hε (lt_min hρm hδ4)
    have hε₀pos : 0 < ε₀ := by rw [hε₀def]; exact div_pos hmin (by norm_num)
    have hε₀ε : ε₀ ≤ ε := by
      have h := min_le_left ε (min (ρ - ‖τ₀‖) (δ / 4 - ‖τ₀‖))
      rw [hε₀def]; linarith
    have hε₀δ4 : ε₀ ≤ (δ / 4 - ‖τ₀‖) / 2 := by
      have h := le_trans (min_le_right ε (min (ρ - ‖τ₀‖) (δ / 4 - ‖τ₀‖)))
        (min_le_right (ρ - ‖τ₀‖) (δ / 4 - ‖τ₀‖))
      rw [hε₀def]
      exact div_le_div_of_nonneg_right h (by norm_num)
    have hε₀ρ : ε₀ ≤ (ρ - ‖τ₀‖) / 2 := by
      have h := le_trans (min_le_right ε (min (ρ - ‖τ₀‖) (δ / 4 - ‖τ₀‖)))
        (min_le_left (ρ - ‖τ₀‖) (δ / 4 - ‖τ₀‖))
      rw [hε₀def]
      exact div_le_div_of_nonneg_right h (by norm_num)
    have hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => Ψ (τ₀ + q.1, q.2)) := by
      have hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => (τ₀ + q.1, q.2)) :=
        ((contDiff_const (c := τ₀)).add contDiff_fst).prodMk contDiff_snd
      have h := hΨsm.comp hφ
      simpa only [Function.comp_def] using h
    have hsurjΦ : ∀ (s : EuclideanSpace ℝ (Fin 8)) (z : EuclideanSpace ℝ (Fin 9)), ‖s‖ < ε₀ →
        (z ∈ K ∨ ∃ t : TFid, z ∈ (fun l : TFdir t => TFbase t + (l : Amb 8)) '' (TFcov K t)) →
        (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => Ψ (τ₀ + q.1, q.2))
            (s, z) = 0 →
        Function.Surjective (fderiv ℝ (fun s' : EuclideanSpace ℝ (Fin 8) =>
          (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
            Ψ (τ₀ + q.1, q.2)) (s', z)) s) := by
      intro s z hs hzdisj hzero
      have hzK : z ∈ K := hzdisj.elim id (fun h => by
        obtain ⟨t, l, hl, hlz⟩ := h
        rw [← hlz]
        exact hl)
      have hst4 : ‖τ₀ + s‖ < δ / 4 := by
        have h1 : ‖τ₀ + s‖ ≤ ‖τ₀‖ + ‖s‖ := norm_add_le _ _
        linarith
      have hst : ‖τ₀ + s‖ < δ := by linarith
      have hγτ : γ (τ₀ + s) = 1 := hγone _ (by
        rw [Metric.mem_closedBall, dist_zero_right]; linarith)
      have hβz : β z = 1 := hβone z hzK
      have hF0 : ppFam p p' Ξ w E E' V W (τ₀ + s) z = 0 := by
        have h : (γ (τ₀ + s) * β z) • ppFam p p' Ξ w E E' V W (τ₀ + s) z = 0 := hzero
        rwa [hγτ, hβz, one_mul, one_smul] at h
      have hreg : z ∈ ppRegion p p' (ppShift Ξ w (unpackFst (τ₀ + s)) E)
          (ppShift Ξ w (unpackSnd (τ₀ + s)) E') V W := hres (τ₀ + s) z hst hzK
      have hFh : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun τ' : EuclideanSpace ℝ (Fin 8) => ppFam p p' Ξ w E E' V W τ' z) (τ₀ + s) := by
        have hG : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
              ppFam p p' Ξ w E E' V W q.1 q.2) (τ₀ + s, z) := by
          simpa only [ppFam] using
            ppParity.contDiffAt_ppDiff_family2 (Ξ := Ξ) hΞsm w hw hE hE' hV hW p p' (τ₀ + s) (y₀ := z) hreg
        have hf : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
            (fun τ' : EuclideanSpace ℝ (Fin 8) => (τ', z)) (τ₀ + s) :=
          contDiffAt_id.prodMk contDiffAt_const
        have hcomp := hG.comp (τ₀ + s) hf
        have hfun : ((fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
              ppFam p p' Ξ w E E' V W q.1 q.2) ∘
              (fun τ' : EuclideanSpace ℝ (Fin 8) => (τ', z)))
            = fun τ' : EuclideanSpace ℝ (Fin 8) => ppFam p p' Ξ w E E' V W τ' z := by
          funext τ'
          rfl
        rwa [hfun] at hcomp
      have hd : HasFDerivAt (fun τ' : EuclideanSpace ℝ (Fin 8) =>
          (γ τ' * β z) • ppFam p p' Ξ w E E' V W τ' z)
          (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin 8) => ppFam p p' Ξ w E E' V W τ' z)
            (τ₀ + s)) (τ₀ + s) :=
        hasFDerivAt_cutoff_fst (γ := γ) (β := β) hγsm hFh hγτ hβz hF0
      have hshift : HasFDerivAt (fun s' : EuclideanSpace ℝ (Fin 8) => τ₀ + s')
          (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 8))) s := by
        simpa using (hasFDerivAt_id (x := s)).const_add τ₀
      have hcomp := hd.comp s hshift
      have hcomp' : HasFDerivAt ((fun τ' : EuclideanSpace ℝ (Fin 8) =>
            (γ τ' * β z) • ppFam p p' Ξ w E E' V W τ' z) ∘ (fun s' : EuclideanSpace ℝ (Fin 8) => τ₀ + s'))
          (fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin 8) => ppFam p p' Ξ w E E' V W τ' z)
              (τ₀ + s)) s := by
        simpa only [ContinuousLinearMap.comp_id] using hcomp
      have hgoal : fderiv ℝ (fun s' : EuclideanSpace ℝ (Fin 8) =>
            (fun τ' : EuclideanSpace ℝ (Fin 8) =>
              (γ τ' * β z) • ppFam p p' Ξ w E E' V W τ' z) (τ₀ + s')) s
          = fderiv ℝ (fun τ' : EuclideanSpace ℝ (Fin 8) => ppFam p p' Ξ w E E' V W τ' z)
              (τ₀ + s) := hcomp'.fderiv
      have hgood : Function.Surjective (fderiv ℝ (fun s' : EuclideanSpace ℝ (Fin 8) =>
          (fun τ' : EuclideanSpace ℝ (Fin 8) =>
            (γ τ' * β z) • ppFam p p' Ξ w E E' V W τ' z) (τ₀ + s')) s) :=
        hgoal ▸ hsurj (τ₀ + s) z hst hzK hF0
      exact hgood
    obtain ⟨s, hslt, hsgood, hsface, hsavoid⟩ :=
      exists_forall_good_face_and_notMem_family 8 8 K hK TFid (fun t : TFid => ↥(TFdir t))
        (fun t => TFdir_finrank_lt t) (fun t => fun l : TFdir t => TFbase t + (l : Amb 8))
        (fun t => contDiff_TFparam t) (fun t => TFcov K t) (fun t => TFcov_isCompact K hK t)
        (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => Ψ (τ₀ + q.1, q.2))
        hΦsm ε₀ hε₀pos hsurjΦ
    refine ⟨τ₀ + s, ?_, ?_, ?_⟩
    · have h : ‖τ₀ + s - τ₀‖ = ‖s‖ := by rw [add_sub_cancel_left]
      rw [h]
      exact lt_of_lt_of_le hslt hε₀ε
    · have h1 : ‖τ₀ + s‖ ≤ ‖τ₀‖ + ‖s‖ := norm_add_le _ _
      have h2 : ‖s‖ < ε₀ := hslt
      have h3 : ‖τ₀‖ + ε₀ < ρ := by linarith
      linarith
    · constructor
      · intro y hyK hybox hΨ0
        have h0 : (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
            Ψ (τ₀ + q.1, q.2)) (s, y) = 0 := hΨ0
        exact hsgood y hyK h0
      · intro y hyK hybox hΨ0 hybdry
        have h0 : (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
            Ψ (τ₀ + q.1, q.2)) (s, y) = 0 := hΨ0
        have hnotwo : ¬ (∃ i j : Fin 9, i ≠ j ∧ (y i = 0 ∨ y i = 1) ∧ (y j = 0 ∨ y j = 1)) := by
          rintro ⟨i, j, hij, hi, hj⟩
          obtain ⟨t', l, hl, hlz⟩ := TFcov_cover K hyK ⟨i, j, hij, hi, hj⟩
          have hne := hsavoid t' l hl
          rw [show TFbase t' + (l : Amb 8) = y from hlz] at hne
          exact hne h0
        obtain ⟨j₀, hj₀⟩ := hybdry.2
        let k : Fin 3 := ⟨j₀.val / 3, by omega⟩
        let i : Fin 3 := ⟨j₀.val % 3, by omega⟩
        have hk : bIdx k i = j₀ := by
          ext
          rw [bIdx_val]
          show j₀.val % 3 + 3 * (j₀.val / 3) = j₀.val
          exact Nat.mod_add_div j₀.val 3
        have hkval : (bIdx k i).val = j₀.val := by rw [hk]
        have hnotface : ∀ m : Fin 9, m ≠ j₀ → ¬ (y m = 0 ∨ y m = 1) := by
          intro m hm hf
          exact hnotwo ⟨j₀, m, fun h => hm h.symm, hj₀, hf⟩
        have hface0 : Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v j₀ = 0} =>
            fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) =>
              (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
                Ψ (τ₀ + q.1, q.2)) (s, y')) y v.1) := hsface j₀ y hyK h0 hj₀
        refine ⟨k, i, ?_, ?_, ?_, ?_⟩
        · rw [hk]; exact hj₀
        · intro j hji
          have hm : bIdx k j ≠ j₀ := by
            intro hcon
            have h2 : bIdx k j = bIdx k i := by rw [hcon, hk]
            exact hji (bIdx_eq_iff.mp h2).2
          exact mem_Ioo_of_mem_unitBox_of_notFace hybox (hnotface _ hm)
        · intro k' hk' j
          have hm : bIdx k' j ≠ j₀ := by
            intro hcon
            have h2 : bIdx k' j = bIdx k i := by rw [hcon, hk]
            exact hk' (bIdx_eq_iff.mp h2).1
          exact mem_Ioo_of_mem_unitBox_of_notFace hybox (hnotface _ hm)
        · have hgoal : Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) //
              v (bIdx k i) = 0} =>
                fderiv ℝ (fun y' : EuclideanSpace ℝ (Fin 9) =>
                  (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
                    Ψ (τ₀ + q.1, q.2)) (s, y')) y v.1) := by
            rw [hk]
            exact hface0
          exact hgoal

end

end Work.Drive