import Mathlib
import Submission.Work.WilG4c.StepLipHighAux
import Submission.Work.WilG4c.YPullback
import Submission.Work.WilG4c.BadLocusThin
import Submission.Work.WilG1.Cell.generic_continuity
import Submission.Work.WilG1.Cell.smooth_k_cover
import Submission.Work.WilkG4c.RowJumpPropagation
import Submission.Work.WilG1.Cell.Junk.disc_mem
import Submission.Work.WilG4c.C1BadLocusMemPB2
import Submission.Work.WilG4c.ReidxPullGraphMem
import Submission.Work.WilG4c.ReidxPullContDiffAt
import Submission.Work.WilG4c.graphOfCompGen
import Submission.Work.WilG4c.sliceGraph_mem_gen
import Submission.Work.WilG4c.JointC1LocMem
import Submission.Work.WilG4c.DefinableSection
import Submission.Work.WilCruxN.GraphFreeClean

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG
open Work.WilkG4c

/-! ## The slice-Lipschitz bound

The hypothesis `hψnm` bounds the order-`1` jet of every `u`-slice of the joint function of the
pullback family by `1`; since the cube is convex and the slices are `C¹` (`hψsm` with `r ≥ 1`),
each slice is `1`-Lipschitz.  This is the input of the jump-propagation argument. -/

theorem convex_openCube_clean (n : ℕ) : Convex ℝ (openCube n) := by
  intro x hx y hy a b ha hb hab i
  have hxi : (0:ℝ) < x i ∧ x i < 1 := hx i
  have hyi : (0:ℝ) < y i ∧ y i < 1 := hy i
  have hsum : a * x i + b * y i = (a • x + b • y) i := by simp [Pi.add_apply, Pi.smul_apply]
  rw [← hsum]
  constructor
  · rcases eq_or_lt_of_le ha with h | h
    · subst h
      have hb1 : b = 1 := by linarith
      subst hb1
      simpa using hyi.1
    · nlinarith [hxi.1, hyi.1, hb]
  · rcases eq_or_lt_of_le hb with h | h
    · subst h
      have ha1 : a = 1 := by linarith
      subst ha1
      simpa using hxi.2
    · nlinarith [hxi.2, hyi.2, ha]

/-- **The slices of the pullback family are `1`-Lipschitz on the cube.** -/
theorem slice_lipschitz {p n k r : ℕ} (hr : 1 ≤ r)
    (F : Family k p (n + 1)) (ψ : ChartTuple (p + 1) n) (i : Fin k)
    (hψsm : ∀ l : Fin p → ℝ, ∀ x ∈ I,
      ContDiffOn ℝ r (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
        (openCube n))
    (hψnm : ∀ l : Fin p → ℝ, ∀ x ∈ I, ∀ m, m ≤ r →
      ∀ t ∈ openCube n,
        ‖iteratedFDeriv ℝ m (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t))) t‖ ≤ 1)
    {l : Fin p → ℝ} {x : ℝ} (hx : x ∈ I) {u u' : Fin n → ℝ}
    (hu : u ∈ openCube n) (hu' : u' ∈ openCube n) :
    |famFunHat (yPullback F ψ i) (xPt l x u) - famFunHat (yPullback F ψ i) (xPt l x u')|
      ≤ dist u u' := by
  classical
  set φ : (Fin n → ℝ) → ℝ :=
    fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)) with hφdef
  have hC1 : ContDiffOn ℝ 1 φ (openCube n) :=
    ContDiffOn.of_le (hψsm l x hx) (by exact_mod_cast hr)
  have hbnd : ∀ t ∈ openCube n, ‖fderiv ℝ φ t‖ ≤ 1 := by
    intro t ht
    have h1 : ‖iteratedFDeriv ℝ 1 φ t‖ ≤ 1 := by
      have h2 := hψnm l x hx 1 hr t ht
      simpa only [hφdef] using h2
    rwa [norm_iteratedFDeriv_one] at h1
  have hdiff : ∀ t ∈ openCube n, DifferentiableAt ℝ φ t := by
    intro t ht
    exact (hC1.differentiableOn (by norm_num)).differentiableAt
      ((Work.WilkG4c.isOpen_openCube n).mem_nhds ht)
  have hmain : ‖φ u' - φ u‖ ≤ 1 * ‖u' - u‖ :=
    (convex_openCube_clean n).norm_image_sub_le_of_norm_fderiv_le hdiff hbnd hu hu'
  have hval : ∀ t : Fin n → ℝ, φ t = famFunHat (yPullback F ψ i) (xPt l x t) := by
    intro t
    rw [hφdef, famFunHat_xPt, yPullback_cons]
  have h3 : ‖u' - u‖ = dist u u' := by rw [norm_sub_rev, dist_eq_norm]
  calc |famFunHat (yPullback F ψ i) (xPt l x u) - famFunHat (yPullback F ψ i) (xPt l x u')|
      = ‖φ u' - φ u‖ := by rw [hval u, hval u', Real.norm_eq_abs, abs_sub_comm]
    _ ≤ 1 * dist u u' := by rw [← h3]; exact hmain
    _ = dist u u' := by ring

/-- **The `C1All`-complement is exactly the projection of the joint non-`C¹` locus.**

Since the `C¹`-locus of a function is open, `xPt l x y` lies in its interior exactly when the
joint function `famFunHat g` is `C¹` there; hence `w ∉ C1All g` says precisely that *some* cube
point of the fibre is a non-`C¹` point. -/
theorem c1AllCompl_eq_proj {p n : ℕ} (g : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) :
    {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I ∧ w ∉ C1All g}
      = {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I ∧ ∃ y ∈ openCube n,
          ¬ ContDiffAt ℝ 1 (famFunHat g)
            (xPt (fun i : Fin p => w (Fin.castSucc i)) (w (Fin.last p)) y)} := by
  classical
  ext w
  have hS : interior {z : Fin (p + (n + 1)) → ℝ | ContDiffAt ℝ 1 (famFunHat g) z}
      = {z : Fin (p + (n + 1)) → ℝ | ContDiffAt ℝ 1 (famFunHat g) z} :=
    (isOpen_contDiffAt_set (famFunHat g)).interior_eq
  have hiff : (w ∈ C1All g) ↔ ∀ y ∈ openCube n, ContDiffAt ℝ 1 (famFunHat g)
      (xPt (fun i : Fin p => w (Fin.castSucc i)) (w (Fin.last p)) y) := by
    simp only [C1All, Set.mem_ofPred_eq]
    constructor
    · intro h y hy
      have hmem : xPt (fun i : Fin p => w (Fin.castSucc i)) (w (Fin.last p)) y ∈
          {z : Fin (p + (n + 1)) → ℝ | ContDiffAt ℝ 1 (famFunHat g) z} :=
        hS ▸ (h y hy)
      simpa only [Set.mem_ofPred_eq] using hmem
    · intro h y hy
      have hmem : xPt (fun i : Fin p => w (Fin.castSucc i)) (w (Fin.last p)) y ∈
          interior {z : Fin (p + (n + 1)) → ℝ | ContDiffAt ℝ 1 (famFunHat g) z} :=
        hS.symm ▸ (h y hy)
      exact hmem
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hx, hnot⟩
    refine ⟨hx, ?_⟩
    by_contra hcon
    push_neg at hcon
    exact hnot (hiff.mpr hcon)
  · rintro ⟨hx, y, hy, hbad⟩
    refine ⟨hx, ?_⟩
    intro hmem
    exact hbad (hiff.mp hmem y hy)

/-! ## The reindexed pullback

Read the pullback family as a family whose parameter block is `(l,x)` and whose variable block is
`y`, as in `WilG4c.C1AllComplThinPB2`.  We record the two facts the crux consumes: the slice
`C¹`-regularity (from `hψsm`) and the slice Lipschitz bound (from `hψnm` via `slice_lipschitz`). -/

/-- The `y`-pullback with the distinguished `x` coordinate moved into the parameter block. -/
def reidxPull {k p n : ℕ} (F : Family k p (n + 1)) (ψ : ChartTuple (p + 1) n) (i : Fin k) :
    (Fin (p + 1) → ℝ) → (Fin n → ℝ) → ℝ :=
  fun w y => F i (fun j : Fin p => w (Fin.castSucc j))
    (Fin.cons (w (Fin.last p))
      (fun j : Fin n => ψ j (Fin.snoc (fun j' : Fin p => w (Fin.castSucc j')) (w (Fin.last p))) y))

/-- Reading `reidxPull` at a glued point recovers the family member. -/
theorem reidxPull_append {k p n : ℕ} (F : Family k p (n + 1)) (ψ : ChartTuple (p + 1) n)
    (i : Fin k) (w : Fin (p + 1) → ℝ) (y : Fin n → ℝ) :
    reidxPull F ψ i w y = famFun (reidxPull F ψ i) (Fin.append w y) := by
  simp only [famFun, reidxPull, Fin.append_left, Fin.append_right]

/-- The joint function of `yPullback` at `xPt l x y` is `reidxPull` at `Fin.snoc l x`. -/
theorem reidxPull_xPt {k p n : ℕ} (F : Family k p (n + 1)) (ψ : ChartTuple (p + 1) n)
    (i : Fin k) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    famFunHat (yPullback F ψ i) (xPt l x y) = reidxPull F ψ i (Fin.snoc l x) y := by
  rw [famFunHat_xPt, yPullback, pullbackMap, reidxPull]
  simp only [Fin.cons_zero, Fin.tail_cons]
  have hinit : (fun j' : Fin p => (Fin.snoc l x : Fin (p + 1) → ℝ) (Fin.castSucc j')) = l := by
    funext j'; rw [Fin.snoc_castSucc]
  rw [hinit, Fin.snoc_last]

/-- The composite form, with the glued point split as `Fin.append`. -/
theorem reidxPull_famFunHat {k p n : ℕ} (F : Family k p (n + 1)) (ψ : ChartTuple (p + 1) n)
    (i : Fin k) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    famFunHat (yPullback F ψ i) (xPt l x y)
      = famFun (reidxPull F ψ i) (Fin.append (Fin.snoc l x) y) := by
  rw [reidxPull_xPt, reidxPull_append]

/-- The slices of the reindexed pullback are `C¹` on the cube over the slab. -/
theorem reidxPull_slice_c1 {k p n r : ℕ} (hr : 1 ≤ r)
    (F : Family k p (n + 1)) (ψ : ChartTuple (p + 1) n) (i : Fin k)
    (hψsm : ∀ l : Fin p → ℝ, ∀ x ∈ I,
      ContDiffOn ℝ r (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
        (openCube n)) :
    ∀ w ∈ {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I},
      ContDiffOn ℝ 1 (reidxPull F ψ i w) (openCube n) := by
  intro w hw
  have h := hψsm (fun j : Fin p => w (Fin.castSucc j)) (w (Fin.last p)) hw
  have h1 : ContDiffOn ℝ 1 (fun t => F i (fun j : Fin p => w (Fin.castSucc j))
      (Fin.cons (w (Fin.last p))
        (fun j : Fin n => ψ j (Fin.snoc (fun j' : Fin p => w (Fin.castSucc j')) (w (Fin.last p))) t)))
      (openCube n) := ContDiffOn.of_le h (by exact_mod_cast hr)
  rw [show reidxPull F ψ i w = (fun t => F i (fun j : Fin p => w (Fin.castSucc j))
      (Fin.cons (w (Fin.last p))
        (fun j : Fin n => ψ j (Fin.snoc (fun j' : Fin p => w (Fin.castSucc j')) (w (Fin.last p))) t)))
      from rfl]
  exact h1

/-- The slices of the reindexed pullback are `1`-Lipschitz on the cube, for parameters in the
slab (where `hψnm` applies). -/
theorem reidxPull_lip {k p n r : ℕ} (hr : 1 ≤ r)
    (F : Family k p (n + 1)) (ψ : ChartTuple (p + 1) n) (i : Fin k)
    (hψsm : ∀ l : Fin p → ℝ, ∀ x ∈ I,
      ContDiffOn ℝ r (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
        (openCube n))
    (hψnm : ∀ l : Fin p → ℝ, ∀ x ∈ I, ∀ m, m ≤ r →
      ∀ t ∈ openCube n,
        ‖iteratedFDeriv ℝ m (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t))) t‖ ≤ 1)
    (w : Fin (p + 1) → ℝ) (hw : w (Fin.last p) ∈ I) :
    ∀ y ∈ openCube n, ∀ y' ∈ openCube n,
      |reidxPull F ψ i w y - reidxPull F ψ i w y'| ≤ dist y y' := by
  intro y hy y' hy'
  have hw' : (Fin.snoc (fun j : Fin p => w (Fin.castSucc j)) (w (Fin.last p)) : Fin (p + 1) → ℝ)
      = w := Fin.snoc_init_self w
  have h := slice_lipschitz hr F ψ i hψsm hψnm
    (l := fun j : Fin p => w (Fin.castSucc j)) (x := w (Fin.last p)) hw hy hy'
  have h' := h
  simp only [reidxPull_famFunHat F ψ i (fun j : Fin p => w (Fin.castSucc j)) (w (Fin.last p)) y,
    reidxPull_famFunHat F ψ i (fun j : Fin p => w (Fin.castSucc j)) (w (Fin.last p)) y'] at h'
  rw [hw'] at h'
  rw [reidxPull_append F ψ i w y, reidxPull_append F ψ i w y']
  exact h'

/-! ## The composition lemma for the section

If `g` is a definable function on `ℝ^{m+N}` and the components of a section `γ` are definable,
then the composite `w ↦ g (Fin.append w (γ w))` is definable.  This is the rectangular
composition lemma `graphOfCompGen` plus the observation that the components of the affinely
reindexed section are either coordinates or components of `γ`. -/

theorem append_section_graph {m N F D F' D' : ℕ} (S : WilkiesDesign.SOMin)
    (g : (Fin (m + N) → ℝ) → ℝ)
    (hg : WilkiesDesign.graphOf g ∈ S.Ω F D (m + N + 1))
    (γ : (Fin m → ℝ) → (Fin N → ℝ))
    (hγ : ∀ j : Fin N, WilkiesDesign.graphOf (fun w : Fin m → ℝ => γ w j) ∈ S.Ω F' D' (m + 1)) :
    ∃ (F'' D'' : ℕ), WilkiesDesign.graphOf (fun w : Fin m → ℝ =>
      g (Fin.append w (γ w))) ∈ S.Ω F'' D'' (m + 1) := by
  obtain ⟨C₁, C₂, H⟩ := Work.WilG4c.graphOfCompGen S (m + N) m
  refine ⟨F + max (m + 1) F' + C₁, D + (m + N) * max 1 D' + C₂, ?_⟩
  refine H F (max (m + 1) F') D (max 1 D') g (fun w => Fin.append w (γ w)) hg ?_
  intro j
  refine Fin.addCases (fun i => ?_) (fun j' => ?_) j
  · have hh : (fun w : Fin m → ℝ => (Fin.append w (γ w)) (Fin.castAdd N i))
        = (fun w : Fin m → ℝ => w i) := by
      funext w; rw [Fin.append_left]
    rw [hh]
    exact Work.WilG1.Omega.mono (Work.WilG4c.graphOf_coord_mem (S := S) (m := m) i)
      (le_max_left _ _) (le_max_left _ _)
  · have hh : (fun w : Fin m → ℝ => (Fin.append w (γ w)) (Fin.natAdd m j'))
        = (fun w : Fin m → ℝ => γ w j') := by
      funext w; rw [Fin.append_right]
    rw [hh]
    exact Work.WilG1.Omega.mono (hγ j') (le_max_right _ _) (le_max_right _ _)

/-- The slab `{w | w (last p) ∈ I}` is open. -/
theorem slab_isOpen_clean (p : ℕ) : IsOpen {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I} := by
  have h : {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I}
      = (fun w : Fin (p + 1) → ℝ => w (Fin.last p)) ⁻¹' (Set.Ioo (0 : ℝ) 1) := by
    ext w; simp [I]
  rw [h]
  exact isOpen_Ioo.preimage (continuous_apply _)

/-- **The `C1All`-complement of the pullback, read through the reindexing.** -/
theorem c1AllCompl_eq_reidx {k p n : ℕ} (F : Family k p (n + 1)) (ψ : ChartTuple (p + 1) n)
    (i : Fin k) :
    {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I ∧ w ∉ C1All (yPullback F ψ i)}
      = {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I ∧ ∃ y ∈ openCube n,
          ¬ ContDiffAt ℝ 1 (famFun (reidxPull F ψ i)) (Fin.append w y)} := by
  rw [c1AllCompl_eq_proj (p := p) (n := n) (yPullback F ψ i)]
  ext w
  constructor
  · rintro ⟨hw, y, hy, hbad⟩
    exact ⟨hw, y, hy, fun hc => hbad ((Work.WilG4c.ReidxPullContDiffAt F ψ i w y).mpr hc)⟩
  · rintro ⟨hw, y, hy, hbad⟩
    exact ⟨hw, y, hy, fun hc => hbad ((Work.WilG4c.ReidxPullContDiffAt F ψ i w y).mp hc)⟩

/-- **T0 (the G4c crux) in the form without a `SharpDeriv` hypothesis.**

The parameter set of a definable family `g` with `C¹` fibre slices on an open `U` has empty
interior as soon as *some* fibre point over a `U`-point fails to be a `C¹` point of the joint
function.  This is the same statement as `Work.WilCrux.BadProjThinAssembly` minus `hder`; the
route through `Work.WilCruxN.GraphFreeClean` (which itself uses only
`Work.WilG4c.C1BadLocusMemPB2` for the `Ω`-definability of the joint non-`C¹` locus, and
`Work.WilG4c.DefinableSection` for the section) never invokes sharp derivatives, so the extra
hypothesis is unnecessary here.

Proof: `Z := {z | ¬ ContDiffAt ℝ 1 (famFun g) z}` is `Ω`-definable; if the bad parameter set had
nonempty interior, an open ball of bad parameters would satisfy the "fatness" hypothesis of
`DefinableSection`, giving a continuous section `γ` on a nonempty open `O` with
`(w, γ w) ∈ Z`; `GraphFreeClean` contradicts that. -/
private theorem badProjThin_cd (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) {m N F D : ℕ}
    (g : (Fin m → ℝ) → (Fin N → ℝ) → ℝ)
    (hg : WilkiesDesign.CG.famGraph g ∈ S.Ω F D (m + N + 1))
    (W : Set (Fin m → ℝ)) (hW : IsOpen W) (U : Set (Fin N → ℝ)) (hU : IsOpen U)
    (hsm : ∀ w ∈ W, ContDiffOn ℝ 1 (g w) U) :
    interior {w : Fin m → ℝ | w ∈ W ∧ ∃ y ∈ U,
      ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun g) (Fin.append w y)} = ∅ := by
  obtain ⟨aL, bL, hL⟩ := Work.WilG4c.JointC1LocMem S hcd m N F
  have hLmem : {z : Fin (m + N) → ℝ | ContDiffAt ℝ 1 (Work.WilG4c.famFun g) z}
      ∈ S.Ω aL (bL.eval D) (m + N) := hL D g hg
  set Z : Set (Fin (m + N) → ℝ) := {z | ContDiffAt ℝ 1 (Work.WilG4c.famFun g) z}ᶜ with hZdef
  have hZmem : Z ∈ S.Ω (aL + 1) (bL.eval D) (m + N) := by
    rw [hZdef]
    exact S.compl hLmem
  have hmemZ : ∀ (w : Fin m → ℝ) (y : Fin N → ℝ),
      Fin.append w y ∈ Z ↔ ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun g) (Fin.append w y) := by
    intro w y
    simp only [hZdef, Set.mem_compl_iff, Set.mem_setOf_eq]
  by_contra hne
  -- a ball of bad parameters
  have hne' : (interior {w : Fin m → ℝ | w ∈ W ∧ ∃ y ∈ U,
      ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun g) (Fin.append w y)}).Nonempty :=
    Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨w₀, hw₀int⟩ := hne'
  have hw₀B : w₀ ∈ {w : Fin m → ℝ | w ∈ W ∧ ∃ y ∈ U,
      ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun g) (Fin.append w y)} := interior_subset hw₀int
  obtain ⟨hw₀W, -⟩ := hw₀B
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isOpen_interior w₀ hw₀int
  -- every parameter in the ball carries a `Z`-point over `U`
  have hhyp : ∃ w : Fin m → ℝ, w ∈ W ∧ ∃ r : ℝ, 0 < r ∧ ∀ w' : Fin m → ℝ, w' ∈ W →
      dist w' w < r → ∃ y : Fin N → ℝ, y ∈ U ∧ Fin.append w' y ∈ Z := by
    refine ⟨w₀, hw₀W, r, hr, ?_⟩
    intro w' _ hd
    have hw'B : w' ∈ {w : Fin m → ℝ | w ∈ W ∧ ∃ y ∈ U,
        ¬ ContDiffAt ℝ 1 (Work.WilG4c.famFun g) (Fin.append w y)} :=
      interior_subset (hball (Metric.mem_ball.mpr hd))
    obtain ⟨-, y, hyU, hybad⟩ := hw'B
    exact ⟨y, hyU, (hmemZ w' y).mpr hybad⟩
  -- definable choice produces a continuous bad sheet over an open set
  obtain ⟨O, γ, hOopen, hOne, hOW, hγcont, hγU, hγZ⟩ :=
    Work.WilG4c.DefinableSection S hcd m N (aL + 1) (bL.eval D) Z hZmem W hW U hU hhyp
  -- which the "no bad sheet" crux excludes
  exact Work.WilCruxN.GraphFreeClean S hcd m N F D g hg W hW U hU hsm O hOopen hOne hOW γ
    hγcont hγU (fun w hw => (hmemZ w (γ w)).mp (hγZ w hw))

theorem C1AllComplThinClean (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    (p n k r : ℕ) (hr : 1 ≤ r)
    (F : Work.WilkG4c.Family k p (n + 1)) (ψ : Work.WilkG4c.ChartTuple (p + 1) n)
    (i : Fin k) (F0 Dg aψ Dgψ : ℕ)
    (hG : WilkiesDesign.CG.famGraph (F i) ∈ S.Ω F0 Dg (p + (n + 1) + 1))
    (hψg : ∀ j, WilkiesDesign.CG.famGraph (ψ j) ∈ S.Ω aψ Dgψ ((p + 1) + n + 1))
    (hψcube : ∀ l : Fin p → ℝ, ∀ x ∈ Work.WilkG4c.I, ∀ t ∈ WilkiesDesign.openCube n,
      (fun j => ψ j (Fin.snoc l x) t) ∈ WilkiesDesign.openCube n)
    (hψsm : ∀ l : Fin p → ℝ, ∀ x ∈ Work.WilkG4c.I,
      ContDiffOn ℝ r (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t)))
        (WilkiesDesign.openCube n))
    (hψnm : ∀ l : Fin p → ℝ, ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r →
      ∀ t ∈ WilkiesDesign.openCube n,
        ‖iteratedFDeriv ℝ m (fun t => F i l (Fin.cons x (fun j => ψ j (Fin.snoc l x) t))) t‖ ≤ 1) :
    interior {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ Work.WilkG4c.I ∧
      w ∉ Work.WilkG4c.C1All (Work.WilkG4c.yPullback F ψ i)} = ∅ := by
  classical
  -- the reindexing of the pullback as a `(p+1)`-parameter, `n`-cube family
  obtain ⟨F1, D1, hG1⟩ := Work.WilG4c.ReidxPullGraphMem S p n k F0 Dg aψ Dgψ F ψ i hG hψg
  rw [c1AllCompl_eq_reidx F ψ i]
  -- the crux: the parameter projection of the joint non-`C¹` locus is thin
  exact badProjThin_cd S hcd (reidxPull F ψ i) hG1
    {w : Fin (p + 1) → ℝ | w (Fin.last p) ∈ I} (slab_isOpen_clean p)
    (openCube n) (Work.WilkG4c.isOpen_openCube n) (reidxPull_slice_c1 hr F ψ i hψsm)

end Work.WilG4c
