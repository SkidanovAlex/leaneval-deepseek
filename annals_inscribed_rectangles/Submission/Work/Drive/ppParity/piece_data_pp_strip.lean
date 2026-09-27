/-
# The piece data of the repaired (collar-line-safe) localized pair Sard

This is the per-piece bundle `Work.Drive.PieceDataStrip` of the *repaired* S3
(`Submission/Work/Drive/PPPARITY_COLLAR_DEFECT.md` §§2–3bis): the piece analogue of the (repaired)
assembly of the intrinsic pair Sard, in which the parameter-surjectivity input is available only at
the pair-map zeros whose family parameter lies in the **active strip** `δ < ftS · < 1 - δ` (where the
weight does not vanish), while the zeros in the closed collar `ftS · ≤ δ` or `1 - δ ≤ ftS ·` are
*honest* meets of the base family whose regularity is the hypothesis `hregBase`, never a conclusion of
the Sard.

The proof is the port of `Submission/Work/Drive/piece_data_pp.lean` prescribed by
`ppParity/StripDefs.lean`: the same cut-off pair system `Ψ = (γ ∘ fst) (β ∘ snd) • ppFam`, the same
tube-lemma construction of the two cut-offs, but the merged genericity theorem is the *relaxed* one
`Work.Drive.ppParity.exists_forall_good_face_and_notMem_family_rel`, applied with

* `S := {z | δ < ftS z ∧ ftS z < 1 - δ}` (the active strip),
* the compact set `K ∩ unitBox 8` (so that `hregBase` applies at every collar point),
* the **non-degenerate two-face pieces** `PTcov K t` of the nine-box (points with two distinct
  coordinates on the box boundary), restricted to `K ∩ unitBox 8` — this is what makes the avoidance
  hypothesis `havoid` of the relaxed Sard provable: a two-face point of the box that is an honest meet
  of the collar cannot exist, because `PPRegAt` at a meet forces the point to lie on exactly *one*
  face.

At a collar zero the relaxed Sard consumes the off-`S` regularity `hregOff`, which is supplied by
`hregBase` through the two collar transfers of the lane:
`Work.Drive.PPRegAt_ppShift_of_collar` (open collar, germ equality) and
`Work.Drive.ppIntrinsic.PPRegAt_ppShift_of_collarBoundary` (the two collar lines, compactness), here
packaged as `ppRegAt_ppShift_of_closedCollar`, plus the chart-independence
`Work.Drive.PPRegAt_chart_indep` and the cut-off derivative identity `hasFDerivAt_cutoff_snd`.
-/
import Mathlib
import Submission.Work.Drive.ppParity.StripDefs
import Submission.Work.Drive.ppParity.exists_forall_good_face_and_notMem_family_rel
import Submission.Work.Drive.piece_data_pp
import Submission.Work.Drive.ppIntrinsic.PPRegAt_ppShift_of_collarBoundary

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `EuclideanSpace ℝ (Fin n)` or products of them
detours through `PolynormableSpace.continuousSMul` and exhausts the synthesis budget. -/
private local instance (priority := high) normedSpace_continuousSMul_real_v434 {E : Type*}
    [SeminormedAddCommGroup E] [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul


namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set Filter

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

local notation "C∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-! ## 1. The non-degenerate two-face pieces of the nine-box -/

/-- A **non-degenerate** two-face index: two distinct coordinates of the nine-box together with the
two face values.  (The `TFid` of `Work.Drive.exists_meet3Data_of_good_family` allows the degenerate
pairs `i = j`, which are junk directions; here they are excluded once and for all, so that every piece
point carries two distinct boundary coordinates.) -/
abbrev PTid : Type := {p : Fin 9 × Fin 9 // p.1 ≠ p.2} × Bool × Bool

/-- The direction space of a two-face piece: the directions vanishing in the two face coordinates. -/
def PTdir (t : PTid) : Submodule ℝ (Amb 8) := AvoidLowDim.pairDir t.1.1.1 t.1.1.2

/-- The base point of a two-face piece: the two face coordinates at the face values, all others `0`. -/
def PTbase (t : PTid) : Amb 8 := AvoidLowDim.faceBase t.1.1.1 t.1.1.2 t.2.1 t.2.2

/-- The parametrisation of a two-face piece. -/
def PTmap (t : PTid) : PTdir t → Amb 8 := fun l => PTbase t + (l : Amb 8)

/-- The parameter set of the two-face piece of `K`. -/
def PTcov (K : Set (Amb 8)) (t : PTid) : Set (PTdir t) := {l | PTmap t l ∈ K}

lemma mem_PTcov {K : Set (Amb 8)} {t : PTid} {l : PTdir t} : l ∈ PTcov K t ↔ PTmap t l ∈ K :=
  Iff.rfl

/-- The direction space of a non-degenerate two-face index is the one of the corresponding (possibly
degenerate) `TFid`; in particular it has dimension `< 8`. -/
lemma PTdir_finrank_lt (t : PTid) : Module.finrank ℝ (PTdir t) < 8 := by
  have h : TFdir ((t.1.1.1, t.1.1.2), (t.2.1, t.2.2)) = PTdir t := by
    rw [TFdir, PTdir]
    simp [t.1.2]
  rw [← h]
  exact TFdir_finrank_lt _

lemma PTcov_isCompact (K : Set (Amb 8)) (hK : IsCompact K) (t : PTid) :
    IsCompact (PTcov K t) := by
  have hcont : Continuous fun l : PTdir t => PTbase t + (l : Amb 8) :=
    continuous_const.add (Submodule.subtypeL (PTdir t)).continuous
  have hclosed : IsClosed (PTcov K t) := hK.isClosed.preimage hcont
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  have hbdd : Bornology.IsBounded (PTcov K t) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C + ‖PTbase t‖, fun l hl => ?_⟩
    have hl' : PTbase t + (l : Amb 8) ∈ K := hl
    calc ‖l‖ = ‖(l : Amb 8)‖ := rfl
      _ = ‖(PTbase t + (l : Amb 8)) - PTbase t‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖PTbase t + (l : Amb 8)‖ + ‖PTbase t‖ := norm_sub_le _ _
      _ ≤ C + ‖PTbase t‖ := by linarith [hC _ hl']
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩

lemma contDiff_PTparam (t : PTid) :
    ContDiff ℝ C∞ fun l : PTdir t => PTbase t + (l : Amb 8) :=
  contDiff_const.add (Submodule.subtypeL (PTdir t)).contDiff

/-- **Every piece point carries two distinct boundary coordinates.** -/
lemma PTpiece_two_faces (t : PTid) (l : PTdir t) :
    ∃ a b : Fin 9, a ≠ b ∧ (PTmap t l a = 0 ∨ PTmap t l a = 1) ∧
      (PTmap t l b = 0 ∨ PTmap t l b = 1) := by
  refine ⟨t.1.1.1, t.1.1.2, t.1.2, ?_, ?_⟩
  · have hl0 : (l : Amb 8) t.1.1.1 = 0 := by
      have h : (l : Amb 8) ∈ AvoidLowDim.pairDir t.1.1.1 t.1.1.2 := l.2
      rw [AvoidLowDim.mem_pairDir] at h
      exact h.1
    have hb : PTbase t t.1.1.1 = AvoidLowDim.faceVal t.2.1 := by
      rw [PTbase]; exact AvoidLowDim.faceBase_apply_fst t.1.1.1 t.1.1.2 t.2.1 t.2.2
    have hsum : PTmap t l t.1.1.1 = PTbase t t.1.1.1 + (l : Amb 8) t.1.1.1 := by
      rw [PTmap, PiLp.add_apply]
    rw [hsum, hl0, add_zero, hb]
    cases t.2.1 <;> simp [AvoidLowDim.faceVal]
  · have hl0 : (l : Amb 8) t.1.1.2 = 0 := by
      have h : (l : Amb 8) ∈ AvoidLowDim.pairDir t.1.1.1 t.1.1.2 := l.2
      rw [AvoidLowDim.mem_pairDir] at h
      exact h.2
    have hb : PTbase t t.1.1.2 = AvoidLowDim.faceVal t.2.2 := by
      rw [PTbase]
      exact AvoidLowDim.faceBase_apply_snd (Ne.symm (t.1.2)) t.2.1 t.2.2
    have hsum : PTmap t l t.1.1.2 = PTbase t t.1.1.2 + (l : Amb 8) t.1.1.2 := by
      rw [PTmap, PiLp.add_apply]
    rw [hsum, hl0, add_zero, hb]
    cases t.2.2 <;> simp [AvoidLowDim.faceVal]

/-- **Every point of `K` lying on two distinct coordinate faces lies on a piece of `K`.** -/
lemma PTcov_cover (K : Set (Amb 8)) {y : Amb 8} (hy : y ∈ K)
    (h2 : ∃ i j : Fin 9, i ≠ j ∧ (y i = 0 ∨ y i = 1) ∧ (y j = 0 ∨ y j = 1)) :
    ∃ (t : PTid) (l : PTdir t), l ∈ PTcov K t ∧ PTmap t l = y := by
  obtain ⟨i, j, hij, hi, hj⟩ := h2
  have hci : AvoidLowDim.faceVal (decide (y i = 1)) = y i := AvoidLowDim.faceVal_decide (y i) hi
  have hcj : AvoidLowDim.faceVal (decide (y j = 1)) = y j := AvoidLowDim.faceVal_decide (y j) hj
  set t : PTid := (⟨(i, j), hij⟩, (decide (y i = 1), decide (y j = 1))) with ht
  have hbase : PTbase t = AvoidLowDim.faceBase i j (decide (y i = 1)) (decide (y j = 1)) := by
    rw [PTbase, ht]
  have hdir : PTdir t = AvoidLowDim.pairDir i j := by
    rw [PTdir, ht]
  have hmem : y - PTbase t ∈ PTdir t := by
    rw [hdir, AvoidLowDim.mem_pairDir]
    constructor
    · rw [PiLp.sub_apply, hbase, AvoidLowDim.faceBase_apply_fst, hci, sub_self]
    · rw [PiLp.sub_apply, hbase, AvoidLowDim.faceBase_apply_snd hij.symm, hcj, sub_self]
  refine ⟨t, ⟨y - PTbase t, hmem⟩, ?_, ?_⟩
  · show PTbase t + ((⟨y - PTbase t, hmem⟩ : PTdir t) : Amb 8) ∈ K
    rw [add_sub_cancel]
    exact hy
  · show PTbase t + ((⟨y - PTbase t, hmem⟩ : PTdir t) : Amb 8) = y
    rw [add_sub_cancel]

/-! ## 2. From a zero of the shifted pair map to an honest meet -/

/-- `pair44` vanishes exactly when both components do (a local copy, to avoid importing
`ppBdry/LocalGraph`). -/
lemma pair44_eq_zero_iff_local (a b : EuclideanSpace ℝ (Fin 4)) :
    pair44 a b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    constructor
    · ext j
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 8) => v (Fin.castAdd 4 j)) h
      simpa using this
    · ext j
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 8) => v (Fin.natAdd 4 j)) h
      simpa using this
  · rintro ⟨rfl, rfl⟩
    ext i
    fin_cases i <;> simp [pair44]

/-- **A zero of the cut-off system at a point where the weight vanishes is an honest meet.** -/
lemma ppMeet_of_ppFam_eq_zero
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ M]
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M} (hΞ0 : ∀ p : M, Ξ 0 p = p) {w : ℝ → ℝ}
    {p p' : M} {τ : EuclideanSpace ℝ (Fin 8)} {z : EuclideanSpace ℝ (Fin 9)}
    (hzbox : z ∈ Submission.Drive.unitBox 8)
    (hws : w (ftS z) = 0)
    (hres : z ∈ ppRegion p p' (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W)
    (h0 : ppFam p p' Ξ w E E' V W τ z = 0) :
    z ∈ ppMeet E E' V W := by
  obtain ⟨h1, h2, h3, h4⟩ := hres
  have h0' : ppDiff p p' (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W z = 0 :=
    h0
  obtain ⟨hfst, hsnd⟩ := pair44_eq_zero_iff_local _ _ |>.mp h0'
  have hA : ppShift Ξ w (unpackFst τ) E (ftS z) (ftU z) = V (ftY z) :=
    (chr p).injOn h1 h2 (sub_eq_zero.mp hfst)
  have hB : ppShift Ξ w (unpackSnd τ) E' (ftS z) (ftU z) = W (ftZ z) :=
    (chr p').injOn h3 h4 (sub_eq_zero.mp hsnd)
  rw [ppShift_eq_of_eq_zero hΞ0 hws (ftU z)] at hA
  rw [ppShift_eq_of_eq_zero hΞ0 hws (ftU z)] at hB
  exact ⟨hzbox, hA, hB⟩

/-! ## 3. The composed chains are smooth -/

/-- The `(s,u)`-chain of a family, composed with the two box coordinates `(ftS, ftU)`, is smooth. -/
lemma contMDiff_ftSU_chain
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ M]
    {E : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ (Function.uncurry E)) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞
      (fun z : EuclideanSpace ℝ (Fin 9) => E (ftS z) (ftU z)) := by
  have h1 : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2))) C∞
      (fun z : EuclideanSpace ℝ (Fin 9) => (ftS z, ftU z)) := by
    refine contMDiff_iff_contDiff.mpr ?_
    refine ContDiff.prodMk ?_ ?_
    · show ContDiff ℝ C∞ (fun z : EuclideanSpace ℝ (Fin 9) => z 0)
      fun_prop
    · show ContDiff ℝ C∞ (fun z : EuclideanSpace ℝ (Fin 9) =>
        WithLp.toLp 2 (fun i : Fin 2 => z ⟨1 + i.val, by omega⟩))
      fun_prop
  have h := hE.comp h1
  simpa only [Function.comp_def, Function.uncurry] using h

/-! ## 4. The transfer on the closed collar -/

/-- **The regularity transfer on the whole closed collar.**  `PPRegAt` of the base family at a meet of
the closed collar transfers to the shifted family: on the *open* collars by the germ equality
`PPRegAt_ppShift_of_collar`, on the two *lines* `ftS · ∈ {δ, 1 - δ}` by the compactness statement
`ppIntrinsic.PPRegAt_ppShift_of_collarBoundary` (whose radius is `η`). -/
lemma ppRegAt_ppShift_of_closedCollar
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ M]
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M} (hΞ0 : ∀ p : M, Ξ 0 p = p)
    (hΞsm : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    {w : ℝ → ℝ} (hw : ContDiff ℝ C∞ w)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ W)
    {δ : ℝ} (hwleft : ∀ s : ℝ, s ≤ δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ ≤ s → w s = 0)
    (hregBase : ∀ x ∈ Submission.Drive.unitBox 8,
      (ftS x ≤ δ ∨ 1 - δ ≤ ftS x) → ppMeet E E' V W x → PPRegAt E E' V W x)
    {η : ℝ} (hη : ∀ t : EuclideanSpace ℝ (Fin 8), ‖t‖ < η →
      ∀ x ∈ ppMeet (ppShift Ξ w (unpackFst t) E) (ppShift Ξ w (unpackSnd t) E') V W,
        (ftS x = δ ∨ ftS x = 1 - δ) →
        PPRegAt (ppShift Ξ w (unpackFst t) E) (ppShift Ξ w (unpackSnd t) E') V W x)
    (τ : EuclideanSpace ℝ (Fin 8)) (hτη : ‖τ‖ < η) {z : EuclideanSpace ℝ (Fin 9)}
    (hzbox : z ∈ Submission.Drive.unitBox 8) (hcol : ftS z ≤ δ ∨ 1 - δ ≤ ftS z)
    (hmeet : z ∈ ppMeet E E' V W) :
    PPRegAt (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W z := by
  have hstrict_left : ∀ s : ℝ, s < δ → w s = 0 := fun s hs => hwleft s (le_of_lt hs)
  have hstrict_right : ∀ s : ℝ, 1 - δ < s → w s = 0 := fun s hs => hwright s (le_of_lt hs)
  have hregBase' : ∀ x ∈ Submission.Drive.unitBox 8, (ftS x < δ ∨ 1 - δ < ftS x) →
      ppMeet E E' V W x → PPRegAt E E' V W x := by
    intro x hx hc hh
    exact hregBase x hx (hc.elim (fun h => Or.inl (le_of_lt h)) fun h => Or.inr (le_of_lt h)) hh
  have hregBase'' : ∀ x ∈ ppMeet E E' V W, (ftS x ≤ δ ∨ 1 - δ ≤ ftS x) → PPRegAt E E' V W x :=
    fun x hx hc => hregBase x hx.1 hc hx
  have key : (ftS z = δ ∨ ftS z = 1 - δ) → w (ftS z) = 0 →
      PPRegAt (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W z := by
    intro hcline hw0
    have hsh : z ∈ ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W :=
      (ppIntrinsic.ppMeet_ppShift_iff_of_closedCollar hΞ0 hwleft hwright τ E E' V W hcline).mpr
        hmeet
    exact hη τ hτη z hsh hcline
  rcases hcol with hc | hc
  · by_cases heq : ftS z = δ
    · exact key (Or.inl heq) (hwleft _ hc)
    · have hlt : ftS z < δ := lt_of_le_of_ne hc heq
      have hmem : z ∈ ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W :=
        (ppMeet_ppShift_iff hΞ0 hstrict_left hstrict_right τ E E' V W (Or.inl hlt)).mpr hmeet
      exact PPRegAt_ppShift_of_collar (Ξ := Ξ) hΞ0 hstrict_left hstrict_right τ E E' V W
        hregBase' z hzbox (Or.inl hlt) hmem
  · by_cases heq : ftS z = 1 - δ
    · exact key (Or.inr heq) (hwright _ hc)
    · have hlt : 1 - δ < ftS z := lt_of_le_of_ne hc (Ne.symm heq)
      have hmem : z ∈ ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W :=
        (ppMeet_ppShift_iff hΞ0 hstrict_left hstrict_right τ E E' V W (Or.inr hlt)).mpr hmeet
      exact PPRegAt_ppShift_of_collar (Ξ := Ξ) hΞ0 hstrict_left hstrict_right τ E E' V W
        hregBase' z hzbox (Or.inr hlt) hmem

/-! ## 5. The raw regularity clauses of the cut-off system at an inactive zero -/

/-- **The two (unstructured) clauses of `ppGoodSet` for the cut-off system at a zero at which the
shifted family is regular.**  The derivative of the cut-off system at a zero equals that of the shifted
pair map (`hasFDerivAt_cutoff_snd`), and chart-independence converts the self-centred `PPRegAt` of the
shifted family into the charted derivative of the pair map in the fixed chart pair `(p, p')`. -/
lemma ppGoodSet_raw_of_PPRegAt_shift
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ M]
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M} {w : ℝ → ℝ}
    (hΞsm : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (hw : ContDiff ℝ C∞ w)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ W)
    {p p' : M} {τ : EuclideanSpace ℝ (Fin 8)} {γ : EuclideanSpace ℝ (Fin 8) → ℝ}
    {β : EuclideanSpace ℝ (Fin 9) → ℝ}
    {z : EuclideanSpace ℝ (Fin 9)}
    (hβsm : ContDiff ℝ C∞ β) (hγτ : γ τ = 1) (hβz : β z = 1)
    (hFh : ContDiffAt ℝ C∞ (fun y' => ppFam p p' Ξ w E E' V W τ y') z)
    (hF0 : ppFam p p' Ξ w E E' V W τ z = 0)
    (hmeet : z ∈ ppMeet (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W)
    (hresτ : z ∈ ppRegion p p' (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W)
    (hreg : PPRegAt (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W z) :
    Function.Surjective
        (fderiv ℝ (fun y' => (γ τ * β y') • ppFam p p' Ξ w E E' V W τ y') z) ∧
      (∀ j : Fin 9, (z j = 0 ∨ z j = 1) →
        Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v j = 0} =>
          fderiv ℝ (fun y' => (γ τ * β y') • ppFam p p' Ξ w E E' V W τ y') z v.1)) := by
  have hder : fderiv ℝ (fun y' => (γ τ * β y') • ppFam p p' Ξ w E E' V W τ y') z
      = fderiv ℝ (fun y' => ppFam p p' Ξ w E E' V W τ y') z :=
    (hasFDerivAt_cutoff_snd (γ := γ) (β := β) hβsm hFh hγτ hβz hF0).fderiv
  have hEs : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞
      (fun z : EuclideanSpace ℝ (Fin 9) => ppShift Ξ w (unpackFst τ) E (ftS z) (ftU z)) :=
    ppIntrinsic.contMDiff_chain_shift Ξ hΞsm hw (unpackFst τ) E hE
  have hE's : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞
      (fun z : EuclideanSpace ℝ (Fin 9) => ppShift Ξ w (unpackSnd τ) E' (ftS z) (ftU z)) :=
    ppIntrinsic.contMDiff_chain_shift Ξ hΞsm hw (unpackSnd τ) E' hE'
  have hVs : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞
      (fun z : EuclideanSpace ℝ (Fin 9) => V (ftY z)) := ppIntrinsic.contMDiff_V_ftY V hV
  have hWs : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 9)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞
      (fun z : EuclideanSpace ℝ (Fin 9) => W (ftZ z)) := ppIntrinsic.contMDiff_W_ftZ W hW
  have hresSelf : z ∈ ppRegion (ppShift Ξ w (unpackFst τ) E (ftS z) (ftU z))
      (ppShift Ξ w (unpackSnd τ) E' (ftS z) (ftU z))
      (ppShift Ξ w (unpackFst τ) E) (ppShift Ξ w (unpackSnd τ) E') V W :=
    ⟨mem_chart_source _ _, by rw [← hmeet.2.1]; exact mem_chart_source _ _,
      mem_chart_source _ _, by rw [← hmeet.2.2]; exact mem_chart_source _ _⟩
  have hci := PPRegAt_chart_indep hEs hE's hVs hWs hmeet hresτ hresSelf
  constructor
  · have h := hci.1.mpr hreg.1
    rw [hder]
    exact h
  · intro j hj
    have hbdry : z ∈ Submission.Drive.unitBoxBdry 8 := ⟨hmeet.1, ⟨j, hj⟩⟩
    obtain ⟨i₀, hi₀, hrest, hface⟩ := hreg.2 hbdry
    by_cases hji : j = i₀
    · subst hji
      have h := (hci.2 j hi₀).mpr hface
      rw [hder]
      exact h
    · exact absurd (hrest j hji) (by rintro ⟨h1, h2⟩; rcases hj with h | h <;> linarith)

/-! ## 6. The restricted conclusion and the target -/

/-- The charted good set of `K ∩ unitBox 8` implies the *strip-restricted* charted good set of `K`. -/
lemma PPChartGoodStrip_of_PPChartGood
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) C∞ M]
    {δ : ℝ} {p p' : M} {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    {V W : EuclideanSpace ℝ (Fin 3) → M} {Ξ : EuclideanSpace ℝ (Fin 4) → M → M} {w : ℝ → ℝ}
    {τ : EuclideanSpace ℝ (Fin 8)} {K : Set (EuclideanSpace ℝ (Fin 9))}
    (h : PPChartGood p p' E E' V W Ξ w τ (K ∩ Submission.Drive.unitBox 8)) :
    PPChartGoodStrip δ p p' E E' V W Ξ w τ K := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨fun y hy hybox _ _ h0 => h1 y ⟨hy, hybox⟩ hybox h0,
    fun y hy hybox _ _ h0 hb => h2 y ⟨hy, hybox⟩ hybox h0 hb⟩

end

end Work.Drive

namespace Work.Drive.ppParity

open scoped Manifold ContDiff Topology
open Manifold Set Filter

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

local notation "C∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

theorem piece_data_pp_strip
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞsm : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (hΞ0 : ∀ p : M, Ξ 0 p = p)
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
    (hwleft : ∀ s : ℝ, s ≤ δ → w s = 0) (hwright : ∀ s : ℝ, 1 - δ ≤ s → w s = 0)
    (hregBase : ∀ x ∈ Submission.Drive.unitBox 8,
      (Work.Drive.ftS x ≤ δ ∨ 1 - δ ≤ Work.Drive.ftS x) →
      Work.Drive.ppMeet E E' V W x → Work.Drive.PPRegAt E E' V W x) :
    ∀ p p' : M, Work.Drive.PieceDataStrip δ p p' E E' V W Ξ w := by
  intro p p'
  intro K δ' hK hδ'pos hres hsurj
  classical
  -- ## 0. The compact set `K₁ = K ∩ unitBox 8` and the collar-boundary radius
  set K₁ : Set (EuclideanSpace ℝ (Fin 9)) := K ∩ Submission.Drive.unitBox 8 with hK₁def
  have hK₁comp : IsCompact K₁ := hK.inter_right (isClosed_unitBox 8)
  have hK₁K : K₁ ⊆ K := Set.inter_subset_left
  obtain ⟨η, hηpos, hηprop⟩ := ppIntrinsic.PPRegAt_ppShift_of_collarBoundary (Ξ := Ξ) hΞ0 hΞsm
    E E' V W hE hE' hV hW hw hwleft hwright (fun x hx hc => hregBase x hx.1 hc hx)
  set ρ : ℝ := min (δ' / 8) η with hρdef
  have hρpos : 0 < ρ := lt_min (by linarith) hηpos
  have hρδ' : ρ ≤ δ' / 8 := min_le_left _ _
  have hρη : ρ ≤ η := min_le_right _ _
  -- ## 1. The chart-residency region and the tube lemma
  set Wres : Set (EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9)) :=
    {q | q.2 ∈ ppRegion p p' (ppShift Ξ w (unpackFst q.1) E)
      (ppShift Ξ w (unpackSnd q.1) E') V W} with hWresdef
  have hWres_open : IsOpen Wres := by
    have hcont1 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
        ppShift Ξ w (unpackFst q.1) E (ftS q.2) (ftU q.2)) := by
      have hΞc : Continuous (fun r : EuclideanSpace ℝ (Fin 4) × M => Ξ r.1 r.2) :=
        hΞsm.continuous
      have hftSU : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
          (ftS q.2, ftU q.2)) := Work.Drive.contDiff_ftSU.continuous.comp continuous_snd
      have h1 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
          w (ftS q.2) • unpackFst q.1) := by
        have hw' : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
            w (ftS q.2)) := hw.continuous.comp (Work.Drive.continuous_ftS.comp continuous_snd)
        exact hw'.smul (unpackFst.continuous.comp continuous_fst)
      have h2 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
          E (ftS q.2) (ftU q.2)) := hE.continuous.comp hftSU
      have h := hΞc.comp (h1.prodMk h2)
      simpa only [Function.comp_def, ppShift] using h
    have hcont2 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
        V (ftY q.2)) := hV.continuous.comp (Work.Drive.continuous_ftY.comp continuous_snd)
    have hcont3 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
        ppShift Ξ w (unpackSnd q.1) E' (ftS q.2) (ftU q.2)) := by
      have hΞc : Continuous (fun r : EuclideanSpace ℝ (Fin 4) × M => Ξ r.1 r.2) :=
        hΞsm.continuous
      have hftSU : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
          (ftS q.2, ftU q.2)) := Work.Drive.contDiff_ftSU.continuous.comp continuous_snd
      have h1 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
          w (ftS q.2) • unpackSnd q.1) := by
        have hw' : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
            w (ftS q.2)) := hw.continuous.comp (Work.Drive.continuous_ftS.comp continuous_snd)
        exact hw'.smul (unpackSnd.continuous.comp continuous_fst)
      have h2 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
          E' (ftS q.2) (ftU q.2)) := hE'.continuous.comp hftSU
      have h := hΞc.comp (h1.prodMk h2)
      simpa only [Function.comp_def, ppShift] using h
    have hcont4 : Continuous (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
        W (ftZ q.2)) := hW.continuous.comp (Work.Drive.continuous_ftZ.comp continuous_snd)
    have hS1 : IsOpen {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        ppShift Ξ w (unpackFst q.1) E (ftS q.2) (ftU q.2) ∈ (chr p).source} :=
      hcont1.isOpen_preimage _ (chr p).open_source
    have hS2 : IsOpen {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        V (ftY q.2) ∈ (chr p).source} := hcont2.isOpen_preimage _ (chr p).open_source
    have hS3 : IsOpen {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        ppShift Ξ w (unpackSnd q.1) E' (ftS q.2) (ftU q.2) ∈ (chr p').source} :=
      hcont3.isOpen_preimage _ (chr p').open_source
    have hS4 : IsOpen {q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) |
        W (ftZ q.2) ∈ (chr p').source} := hcont4.isOpen_preimage _ (chr p').open_source
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
  have hWres_sub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 8)) (δ' / 4) ×ˢ K₁ ⊆ Wres := by
    rintro ⟨τ, y⟩ ⟨hτ, hy⟩
    exact hres τ y (by
      have h := Metric.mem_closedBall.mp hτ
      rw [dist_zero_right] at h
      linarith) (hK₁K hy)
  obtain ⟨U, S, hUopen, hSopen, hUsub, hSsub, hUS⟩ :=
    generalized_tube_lemma (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 8)) (δ' / 4))
      hK₁comp hWres_open hWres_sub
  obtain ⟨γ, hγsm, hγone, hγsupp⟩ := exists_cutoff_tsupport_subset
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 8)) (δ' / 4)) hUopen hUsub
  obtain ⟨β, hβsm, hβone, hβsupp⟩ := exists_cutoff_tsupport_subset hK₁comp hSopen hSsub
  -- ## 2. The cut-off pair system
  set Ψ : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) → EuclideanSpace ℝ (Fin 8) :=
    fun q => (γ q.1 * β q.2) • ppFam p p' Ξ w E E' V W q.1 q.2 with hΨdef
  have hΨsm : ContDiff ℝ C∞ Ψ := by
    rw [hΨdef]
    exact contDiff_ppCut (Ξ := Ξ) hΞsm w hw E E' hE hE' V W hV hW p p' hγsm hβsm hUS hγsupp hβsupp
  have hΨopen : IsOpen {τ : EuclideanSpace ℝ (Fin 8) | ppGoodSet Ψ K τ} :=
    ppGoodSet_open Ψ hΨsm K hK
  have hγ1 : ∀ τ : EuclideanSpace ℝ (Fin 8), ‖τ‖ < δ' / 4 → γ τ = 1 := fun τ hτ =>
    hγone τ (by rw [Metric.mem_closedBall, dist_zero_right]; linarith)
  refine ⟨ρ, Ψ, hρpos, hΨsm, hΨopen, ?_, ?_⟩
  · -- ## 3. The pointwise clause
    intro τ hτρ hgood
    have hτδ' : ‖τ‖ < δ' := by linarith
    have hτ4 : ‖τ‖ < δ' / 4 := by linarith
    have hγτ : γ τ = 1 := hγ1 τ hτ4
    have hgood₁ : ppGoodSet Ψ K₁ τ :=
      ⟨fun y hy hybox => hgood.1 y hy.1 hybox, fun y hy hybox h0 hb => hgood.2 y hy.1 hybox h0 hb⟩
    refine PPChartGoodStrip_of_PPChartGood (p := p) (p' := p') (E := E) (E' := E') (V := V)
      (W := W) (Ξ := Ξ) (w := w) (τ := τ) (K := K) (δ := δ) ?_
    refine PPChartGood_of_ppGoodSet (Ξ := Ξ) (w := w) (E := E) (E' := E') (V := V) (W := W)
      (p := p) (p' := p') (τ := τ) (K := K₁) hgood₁ ?_ ?_
    · intro y hyK
      have hβy : β y = 1 := hβone y hyK
      show (γ τ * β y) • ppFam p p' Ξ w E E' V W τ y = ppFam p p' Ξ w E E' V W τ y
      rw [hγτ, hβy, one_mul, one_smul]
    · intro y hyK hΨ0
      have hβy : β y = 1 := hβone y hyK
      have hF0 : ppFam p p' Ξ w E E' V W τ y = 0 := by
        have h : (γ τ * β y) • ppFam p p' Ξ w E E' V W τ y = 0 := hΨ0
        rwa [hγτ, hβy, one_mul, one_smul] at h
      have hreg : y ∈ ppRegion p p' (ppShift Ξ w (unpackFst τ) E)
          (ppShift Ξ w (unpackSnd τ) E') V W := hres τ y hτδ' hyK.1
      have hFh : ContDiffAt ℝ C∞ (fun y' => ppFam p p' Ξ w E E' V W τ y') y := by
        have hG : ContDiffAt ℝ C∞ (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
            ppFam p p' Ξ w E E' V W q.1 q.2) (τ, y) := by
          simpa only [ppFam] using
            ppParity.contDiffAt_ppDiff_family2 (Ξ := Ξ) hΞsm w hw hE hE' hV hW p p' τ (y₀ := y) hreg
        exact hG.comp y (contDiffAt_const.prodMk contDiffAt_id)
      exact (hasFDerivAt_cutoff_snd (γ := γ) (β := β) hβsm hFh hγτ hβy hF0).fderiv
  · -- ## 4. The density clause
    intro τ₀ hτ₀ ε' hε'
    have hρm : 0 < ρ - ‖τ₀‖ := by linarith
    set ε₀ : ℝ := min ε' (ρ - ‖τ₀‖) / 2 with hε₀def
    have hε₀pos : 0 < ε₀ := by
      rw [hε₀def]
      have h := lt_min hε' hρm
      linarith
    have hε₀ε' : ε₀ < ε' := by
      have h1 : min ε' (ρ - ‖τ₀‖) ≤ ε' := min_le_left _ _
      rw [hε₀def]
      linarith
    have hε₀ρ : ε₀ < ρ - ‖τ₀‖ := by
      have h1 : min ε' (ρ - ‖τ₀‖) ≤ ρ - ‖τ₀‖ := min_le_right _ _
      rw [hε₀def]
      linarith
    have hΦsm : ContDiff ℝ C∞
        (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => Ψ (τ₀ + q.1, q.2)) := by
      have hφ : ContDiff ℝ C∞ (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
          (τ₀ + q.1, q.2)) := ((contDiff_const (c := τ₀)).add contDiff_fst).prodMk contDiff_snd
      have h := hΨsm.comp hφ
      simpa only [Function.comp_def] using h
    set Sset : Set (EuclideanSpace ℝ (Fin 9)) := {z | δ < ftS z ∧ ftS z < 1 - δ} with hSsetdef
    -- ### 4a. The parameter-surjectivity on the active strip
    have hsurjΦ : ∀ (s : EuclideanSpace ℝ (Fin 8)) (z : EuclideanSpace ℝ (Fin 9)),
        ‖s‖ < ε₀ → (z ∈ K₁ ∨ ∃ t : PTid, z ∈ PTmap t '' PTcov K₁ t) →
        (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => Ψ (τ₀ + q.1, q.2))
            (s, z) = 0 → z ∈ Sset →
        Function.Surjective (fderiv ℝ (fun s' : EuclideanSpace ℝ (Fin 8) =>
          (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
            Ψ (τ₀ + q.1, q.2)) (s', z)) s) := by
      intro s z hs hzdisj hzero hzS
      have hzK₁ : z ∈ K₁ := hzdisj.elim id (fun h => by
        obtain ⟨t, l, hl, hlz⟩ := h; rw [← hlz]; exact hl)
      have hzK : z ∈ K := hK₁K hzK₁
      have hzS' : δ < ftS z ∧ ftS z < 1 - δ := by
        have h := hzS
        rw [hSsetdef] at h
        simpa only [Set.mem_setOf_eq] using h
      have hst4 : ‖τ₀ + s‖ < δ' / 4 := by
        have h1 : ‖τ₀ + s‖ ≤ ‖τ₀‖ + ‖s‖ := norm_add_le _ _
        linarith
      have hst : ‖τ₀ + s‖ < δ' := by linarith
      have hγτ : γ (τ₀ + s) = 1 := hγ1 _ hst4
      have hβz : β z = 1 := hβone z hzK₁
      have hF0 : ppFam p p' Ξ w E E' V W (τ₀ + s) z = 0 := by
        have h : (γ (τ₀ + s) * β z) • ppFam p p' Ξ w E E' V W (τ₀ + s) z = 0 := hzero
        rwa [hγτ, hβz, one_mul, one_smul] at h
      have hreg : z ∈ ppRegion p p' (ppShift Ξ w (unpackFst (τ₀ + s)) E)
          (ppShift Ξ w (unpackSnd (τ₀ + s)) E') V W := hres (τ₀ + s) z hst hzK
      have hFh : ContDiffAt ℝ C∞
          (fun τ' : EuclideanSpace ℝ (Fin 8) => ppFam p p' Ξ w E E' V W τ' z) (τ₀ + s) := by
        have hG : ContDiffAt ℝ C∞ (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
            ppFam p p' Ξ w E E' V W q.1 q.2) (τ₀ + s, z) := by
          simpa only [ppFam] using
            ppParity.contDiffAt_ppDiff_family2 (Ξ := Ξ) hΞsm w hw hE hE' hV hW p p' (τ₀ + s)
              (y₀ := z) hreg
        have hf : ContDiffAt ℝ C∞ (fun τ' : EuclideanSpace ℝ (Fin 8) => (τ', z)) (τ₀ + s) :=
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
            (γ τ' * β z) • ppFam p p' Ξ w E E' V W τ' z) ∘
            (fun s' : EuclideanSpace ℝ (Fin 8) => τ₀ + s'))
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
        hgoal ▸ hsurj (τ₀ + s) z hst hzK hF0 hzS'.1 hzS'.2
      exact hgood
    -- ### 4b. The off-strip regularity
    have hregOff : ∀ (s : EuclideanSpace ℝ (Fin 8)) (z : EuclideanSpace ℝ (Fin 9)),
        ‖s‖ < ε₀ → (z ∈ K₁ ∨ ∃ t : PTid, z ∈ PTmap t '' PTcov K₁ t) →
        (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => Ψ (τ₀ + q.1, q.2))
            (s, z) = 0 → z ∉ Sset →
        Function.Surjective (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
          (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
            Ψ (τ₀ + q.1, q.2)) (s, z')) z) ∧
        (∀ j : Fin 9, (z j = 0 ∨ z j = 1) →
          Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v j = 0} =>
            fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
              (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
                Ψ (τ₀ + q.1, q.2)) (s, z')) z v.1)) := by
      intro s z hs hzdisj hzero hzS
      have hzK₁ : z ∈ K₁ := hzdisj.elim id (fun h => by
        obtain ⟨t, l, hl, hlz⟩ := h; rw [← hlz]; exact hl)
      have hzK : z ∈ K := hK₁K hzK₁
      have hzbox : z ∈ Submission.Drive.unitBox 8 := hzK₁.2
      have hst4 : ‖τ₀ + s‖ < δ' / 4 := by
        have h1 : ‖τ₀ + s‖ ≤ ‖τ₀‖ + ‖s‖ := norm_add_le _ _
        linarith
      have hst : ‖τ₀ + s‖ < δ' := by linarith
      have hτρ : ‖τ₀ + s‖ < ρ := by
        have h1 : ‖τ₀ + s‖ ≤ ‖τ₀‖ + ‖s‖ := norm_add_le _ _
        linarith
      have hγτ : γ (τ₀ + s) = 1 := hγ1 _ hst4
      have hβz : β z = 1 := hβone z hzK₁
      have hF0 : ppFam p p' Ξ w E E' V W (τ₀ + s) z = 0 := by
        have h : (γ (τ₀ + s) * β z) • ppFam p p' Ξ w E E' V W (τ₀ + s) z = 0 := hzero
        rwa [hγτ, hβz, one_mul, one_smul] at h
      have hznotS : ¬ (δ < ftS z ∧ ftS z < 1 - δ) := by
        intro h
        exact hzS (by rw [hSsetdef]; exact h)
      have hcoll : ftS z ≤ δ ∨ 1 - δ ≤ ftS z := by
        by_contra h
        push_neg at h
        exact hznotS h
      have hw0 : w (ftS z) = 0 := hcoll.elim (fun h => hwleft _ h) fun h => hwright _ h
      have hmeet : z ∈ ppMeet E E' V W :=
        ppMeet_of_ppFam_eq_zero (Ξ := Ξ) hΞ0 hzbox hw0 (hres (τ₀ + s) z hst hzK) hF0
      have hregshift : PPRegAt (ppShift Ξ w (unpackFst (τ₀ + s)) E)
          (ppShift Ξ w (unpackSnd (τ₀ + s)) E') V W z :=
        ppRegAt_ppShift_of_closedCollar (Ξ := Ξ) hΞ0 hΞsm hw hE hE' hV hW hwleft hwright
          hregBase hηprop (τ₀ + s) (lt_of_lt_of_le hτρ hρη) hzbox hcoll hmeet
      have hmeetshift : z ∈ ppMeet (ppShift Ξ w (unpackFst (τ₀ + s)) E)
          (ppShift Ξ w (unpackSnd (τ₀ + s)) E') V W :=
        ⟨hzbox, by rw [ppShift_eq_of_eq_zero hΞ0 hw0 (ftU z)]; exact hmeet.2.1,
          by rw [ppShift_eq_of_eq_zero hΞ0 hw0 (ftU z)]; exact hmeet.2.2⟩
      have hresτ : z ∈ ppRegion p p' (ppShift Ξ w (unpackFst (τ₀ + s)) E)
          (ppShift Ξ w (unpackSnd (τ₀ + s)) E') V W := hres (τ₀ + s) z hst hzK
      have hFh : ContDiffAt ℝ C∞
          (fun y' => ppFam p p' Ξ w E E' V W (τ₀ + s) y') z := by
        have hG : ContDiffAt ℝ C∞ (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
            ppFam p p' Ξ w E E' V W q.1 q.2) (τ₀ + s, z) := by
          simpa only [ppFam] using
            ppParity.contDiffAt_ppDiff_family2 (Ξ := Ξ) hΞsm w hw hE hE' hV hW p p' (τ₀ + s)
              (y₀ := z) hresτ
        exact hG.comp z (contDiffAt_const.prodMk contDiffAt_id)
      exact ppGoodSet_raw_of_PPRegAt_shift (Ξ := Ξ) (w := w) hΞsm hw hE hE' hV hW
        (p := p) (p' := p') (τ := τ₀ + s) (γ := γ) (β := β) (z := z)
        hβsm hγτ hβz hFh hF0 hmeetshift hresτ hregshift
    -- ### 4c. The avoidance off the active strip
    have havoid : ∀ (s : EuclideanSpace ℝ (Fin 8)) (t : PTid) (l : PTdir t),
        ‖s‖ < ε₀ → l ∈ PTcov K₁ t → PTmap t l ∉ Sset →
        (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => Ψ (τ₀ + q.1, q.2))
          (s, PTmap t l) ≠ 0 := by
      intro s t l hs hl hlS hzero
      have hzK₁ : PTmap t l ∈ K₁ := hl
      have hzbox : PTmap t l ∈ Submission.Drive.unitBox 8 := hzK₁.2
      have hst4 : ‖τ₀ + s‖ < δ' / 4 := by
        have h1 : ‖τ₀ + s‖ ≤ ‖τ₀‖ + ‖s‖ := norm_add_le _ _
        linarith
      have hst : ‖τ₀ + s‖ < δ' := by linarith
      have hγτ : γ (τ₀ + s) = 1 := hγ1 _ hst4
      have hβz : β (PTmap t l) = 1 := hβone _ hzK₁
      have hF0 : ppFam p p' Ξ w E E' V W (τ₀ + s) (PTmap t l) = 0 := by
        have h : (γ (τ₀ + s) * β (PTmap t l)) • ppFam p p' Ξ w E E' V W (τ₀ + s) (PTmap t l) = 0 :=
          hzero
        rwa [hγτ, hβz, one_mul, one_smul] at h
      have hznotS : ¬ (δ < ftS (PTmap t l) ∧ ftS (PTmap t l) < 1 - δ) := by
        intro h
        exact hlS (by rw [hSsetdef]; exact h)
      have hcoll : ftS (PTmap t l) ≤ δ ∨ 1 - δ ≤ ftS (PTmap t l) := by
        by_contra h
        push_neg at h
        exact hznotS h
      have hw0 : w (ftS (PTmap t l)) = 0 := hcoll.elim (fun h => hwleft _ h) fun h => hwright _ h
      have hmeet : PTmap t l ∈ ppMeet E E' V W :=
        ppMeet_of_ppFam_eq_zero (Ξ := Ξ) hΞ0 hzbox hw0 (hres (τ₀ + s) _ hst (hK₁K hzK₁)) hF0
      have hreg : PPRegAt E E' V W (PTmap t l) := hregBase _ hzbox hcoll hmeet
      obtain ⟨a, b, hab, ha, hb⟩ := PTpiece_two_faces t l
      obtain ⟨i₀, hi₀, hrest, -⟩ := hreg.2 ⟨hzbox, ⟨a, ha⟩⟩
      rcases eq_or_ne a i₀ with h | h
      · subst h
        obtain ⟨h1, h2⟩ := hrest b (fun hb' => hab hb'.symm)
        rcases hb with hb | hb <;> linarith
      · obtain ⟨h1, h2⟩ := hrest a h
        rcases ha with ha | ha <;> linarith
    -- ### 4d. The relaxed Sard
    obtain ⟨s, hslt, hsgood, hsface, hsavoid⟩ :=
      exists_forall_good_face_and_notMem_family_rel 8 8 K₁ hK₁comp PTid
        (fun t : PTid => ↥(PTdir t)) (fun t => PTdir_finrank_lt t) (fun t => PTmap t)
        (fun t => contDiff_PTparam t) (fun t => PTcov K₁ t)
        (fun t => PTcov_isCompact K₁ hK₁comp t)
        (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) => Ψ (τ₀ + q.1, q.2))
        hΦsm Sset ε₀ hε₀pos hsurjΦ hregOff havoid
    refine ⟨τ₀ + s, ?_, ?_, ?_⟩
    · rw [add_sub_cancel_left]
      exact lt_of_lt_of_le hslt (le_of_lt hε₀ε')
    · have h1 : ‖τ₀ + s‖ ≤ ‖τ₀‖ + ‖s‖ := norm_add_le _ _
      linarith
    · -- ### 4e. The good parameter
      constructor
      · intro y hyK hybox h0
        exact hsgood y ⟨hyK, hybox⟩ h0
      · intro y hyK hybox h0 hybdry
        have hyK₁ : y ∈ K₁ := ⟨hyK, hybox⟩
        obtain ⟨j₀, hj₀⟩ := hybdry.2
        have hnotwo : ∀ m : Fin 9, m ≠ j₀ → ¬ (y m = 0 ∨ y m = 1) := by
          intro m hm hfm
          obtain ⟨t, l, hl, hlz⟩ :=
            PTcov_cover K₁ hyK₁ ⟨j₀, m, fun h => hm h.symm, hj₀, hfm⟩
          have hne := hsavoid t l hl
          rw [hlz] at hne
          exact hne h0
        let k : Fin 3 := ⟨j₀.val / 3, by omega⟩
        let i : Fin 3 := ⟨j₀.val % 3, by omega⟩
        have hk : bIdx k i = j₀ := by
          ext
          rw [Work.Drive.bIdx_val]
          show j₀.val % 3 + 3 * (j₀.val / 3) = j₀.val
          exact Nat.mod_add_div j₀.val 3
        refine ⟨k, i, ?_, ?_, ?_, ?_⟩
        · rw [hk]; exact hj₀
        · intro j hji
          have hm : bIdx k j ≠ j₀ := by
            intro hcon
            have h2 : bIdx k j = bIdx k i := by rw [hcon, hk]
            exact hji (bIdx_eq_iff.mp h2).2
          exact mem_Ioo_of_mem_unitBox_of_notFace hybox (hnotwo _ hm)
        · intro k' hk' j
          have hm : bIdx k' j ≠ j₀ := by
            intro hcon
            have h2 : bIdx k' j = bIdx k i := by rw [hcon, hk]
            exact hk' (bIdx_eq_iff.mp h2).1
          exact mem_Ioo_of_mem_unitBox_of_notFace hybox (hnotwo _ hm)
        · have hface := hsface j₀ y hyK₁ h0 hj₀
          rw [hk]
          exact hface

end Work.Drive.ppParity
