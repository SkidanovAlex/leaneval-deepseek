/-
  Work.WilCrux.PDPDefs — vocabulary and `Ω`/analysis lemmas for node N4c
  (`Work.WilCrux.ParamDerivPointwise`).

  Contents: the "hat" family `Ĝ = G - G · 0`, the gain loci `pdpE`, the accumulation sets
  `pdpAcc`, the identification `pdp_hat_eq` of the raw parameter partial with `∂_{w_i} famFun Ĝ`
  on the `C¹`-locus of the sheet, the `Ω`-definability of the gain loci (`pdp_gainSet_mem`) and
  the mean-value bounds `pdp_lip_of_bound`.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.WilG4c.StepCleanDefs
import Submission.Work.WilG4b.ESet_mem
import Submission.Work.WilG4a.affine_comb_graph_mem
import Submission.Work.WilG1.Main
import Submission.Work.WilG1.Cell.thin_closure
import Submission.Work.WilG5.Basic
import Submission.Work.WilG4c.BadLocusThin
import Submission.Work.WilCrux.OmegaModulus
import Submission.Work.WilCrux.BaireDefinableCover
import Submission.Work.WilCrux.fibreFderivFamFun
import Submission.Work.WilCrux.SphereChoice
import Submission.Work.WilCrux.UnifMonotonePieces
import Submission.Work.WilCrux.PathGainBound
import Submission.Work.WilCrux.flatGraphMem
import Submission.Work.WilCrux.Clean.SheetHatGraphMem
import Submission.Work.WilCrux.Clean.MonotonePiecesOnLine
import Submission.Work.WilCruxN.DerivGraphClean
import Submission.Work.WilCruxN.MonotonePiecesOnLineClean
import Submission.Work.WilCrux.Clean.AccSetMem

namespace Work.WilCruxN

open Work.WilCrux

open WilkiesDesign WilkiesDesign.CG

/-! ## 0. Vocabulary -/

/-- `Ĝ w z = G w z - G w 0`; the sheet value is subtracted so that `Ĝ w 0 = 0`. -/
def pdpHat {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) :
    (Fin a → ℝ) → (Fin b → ℝ) → ℝ :=
  fun w z => G w z - G w 0

@[simp] theorem pdpHat_apply {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w : Fin a → ℝ) (z : Fin b → ℝ) : pdpHat G w z = G w z - G w 0 := rfl

@[simp] theorem pdpHat_zero {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (w : Fin a → ℝ) : pdpHat G w 0 = 0 := by simp [pdpHat]

/-- The set of parameters admitting witnesses in `E` of arbitrarily small punctured radius. -/
def pdpAcc {a b : ℕ} (E : Set (Fin (a + b) → ℝ)) : Set (Fin a → ℝ) :=
  {w | ∀ δ : ℝ, 0 < δ → ∃ z : Fin b → ℝ, 0 < ‖z‖ ∧ ‖z‖ < δ ∧ Fin.append w z ∈ E}

/-- The positive-gain locus of a definable family in `(w,z)`-space: the `C¹`-locus where the
parameter partial `∂_{w_i}` of the joint function is at least `η`. -/
def pdpE {a b : ℕ} (F : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (i : Fin a) (η : ℝ) :
    Set (Fin (a + b) → ℝ) :=
  {u | ∃ v : ℝ, Fin.snoc u v ∈ Work.WilG4b.derivGraph (Work.WilG4c.famFun F)
      (Fin.castAdd b i) ∧ η ≤ v}

/-- The projection of `ℝ^{a+b}` onto its parameter block `ℝ^a`. -/
def pdpWtake (a b : ℕ) : (Fin (a + b) → ℝ) →L[ℝ] (Fin a → ℝ) :=
  ContinuousLinearMap.pi (fun i : Fin a => ContinuousLinearMap.proj (Fin.castAdd b i))

theorem pdpWtake_apply (a b : ℕ) (u : Fin (a + b) → ℝ) :
    pdpWtake a b u = fun i => u (Fin.castAdd b i) := by
  funext i
  rw [pdpWtake]
  simp [ContinuousLinearMap.pi_apply]

theorem pdpWtake_append (a b : ℕ) (w : Fin a → ℝ) (z : Fin b → ℝ) :
    pdpWtake a b (Fin.append w z) = w := by
  funext i
  rw [pdpWtake_apply]
  exact Fin.append_left _ _ i

/-! ## 1. Elementary API for the loci -/

/-- On the `C¹`-locus, `c1Loc` is just the `C¹`-locus. -/
theorem pdp_c1Loc_iff {n : ℕ} {f : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} :
    x ∈ Work.WilG4b.c1Loc f ↔ ContDiffAt ℝ 1 f x := by
  have hopen : IsOpen {z : Fin n → ℝ | ContDiffAt ℝ 1 f z} :=
    Work.WilkG4c.isOpen_contDiffAt_set (k := 1) f
  rw [Work.WilG4b.c1Loc, hopen.interior_eq]
  exact Iff.rfl

theorem pdp_c1Loc_neg {n : ℕ} (g : (Fin n → ℝ) → ℝ) :
    Work.WilG4b.c1Loc (fun x => -g x) = Work.WilG4b.c1Loc g := by
  ext x
  rw [pdp_c1Loc_iff, pdp_c1Loc_iff]
  exact ⟨fun h => by simpa using h.neg, fun h => h.neg⟩

theorem pdp_dDir_neg {n : ℕ} (g : (Fin n → ℝ) → ℝ) (i : Fin n) (u : Fin n → ℝ) :
    Work.WilG4b.dDir (fun x => -g x) i u = -Work.WilG4b.dDir g i u := by
  have h : (fun x => -g x) = -g := rfl
  rw [h, Work.WilG4b.dDir, Work.WilG4b.dDir, fderiv_neg]
  rfl

theorem pdp_mem_derivGraph {n : ℕ} {f : (Fin n → ℝ) → ℝ} {i : Fin n} {u : Fin n → ℝ}
    {v : ℝ} :
    Fin.snoc u v ∈ Work.WilG4b.derivGraph f i ↔
      u ∈ Work.WilG4b.c1Loc f ∧ v = Work.WilG4b.dDir f i u := by
  rw [Work.WilG4b.derivGraph]
  simp only [Set.mem_ofPred_eq, Fin.init_snoc, Fin.snoc_last]

theorem pdpE_mem {a b : ℕ} {F : (Fin a → ℝ) → (Fin b → ℝ) → ℝ} {i : Fin a} {η : ℝ}
    {u : Fin (a + b) → ℝ} :
    u ∈ pdpE F i η ↔
      u ∈ Work.WilG4b.c1Loc (Work.WilG4c.famFun F) ∧
        η ≤ Work.WilG4b.dDir (Work.WilG4c.famFun F) (Fin.castAdd b i) u := by
  constructor
  · rintro ⟨v, hv, hη⟩
    rw [pdp_mem_derivGraph] at hv
    exact ⟨hv.1, hv.2 ▸ hη⟩
  · rintro ⟨hc, hη⟩
    exact ⟨_, pdp_mem_derivGraph.mpr ⟨hc, rfl⟩, hη⟩

/-- The parameter direction `e_i` inside `ℝ^{a+b}` is `Fin.append (Pi.single i 1) 0`. -/
theorem pdp_single_castAdd {a b : ℕ} (i : Fin a) :
    (Pi.single (Fin.castAdd b i) (1 : ℝ) : Fin (a + b) → ℝ)
      = Fin.append (Pi.single i 1) (0 : Fin b → ℝ) := by
  funext k
  refine Fin.addCases (fun i' => ?_) (fun j => ?_) k
  · rw [Fin.append_left]
    by_cases h : i' = i
    · subst h; simp
    · have hne : Fin.castAdd b i' ≠ Fin.castAdd b i := by
        intro hh; exact h (Fin.ext (by simpa using congrArg Fin.val hh))
      simp [h, hne]
  · rw [Fin.append_right]
    have hne : Fin.natAdd a j ≠ Fin.castAdd b i := by
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at this
      omega
    simp [hne]

/-! ## 2. The `ε`-`δ` form of the punctured limit -/

theorem pdp_tendsto_punctured_iff {b : ℕ} (g : (Fin b → ℝ) → ℝ) :
    Filter.Tendsto g (nhdsWithin (0 : Fin b → ℝ) {(0 : Fin b → ℝ)}ᶜ) (nhds 0) ↔
      ∀ ε > 0, ∃ δ > 0, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < δ → |g z| < ε := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    have h1 : ∀ᶠ z in nhds (0 : Fin b → ℝ),
        z ∈ ({(0 : Fin b → ℝ)}ᶜ : Set (Fin b → ℝ)) → dist (g z) 0 < ε :=
      eventually_nhdsWithin_iff.mp (h ε hε)
    obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp h1
    refine ⟨δ, hδ, fun z hz hzδ => ?_⟩
    have h2 := hδ' (show dist z (0 : Fin b → ℝ) < δ by simpa [dist_eq_norm] using hzδ)
      (by simpa using hz)
    simpa [Real.dist_eq] using h2
  · intro h ε hε
    obtain ⟨δ, hδ, hδ'⟩ := h ε hε
    rw [eventually_nhdsWithin_iff]
    refine Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun z hz hz0 => ?_⟩
    have h2 := hδ' z (by simpa using hz0) (by simpa [dist_eq_norm] using hz)
    simpa [Real.dist_eq] using h2

theorem pdp_not_tendsto_punctured_iff {b : ℕ} (g : (Fin b → ℝ) → ℝ) :
    ¬ Filter.Tendsto g (nhdsWithin (0 : Fin b → ℝ) {(0 : Fin b → ℝ)}ᶜ) (nhds 0) ↔
      ∃ ε > 0, ∀ δ > 0, ∃ z : Fin b → ℝ, z ≠ 0 ∧ ‖z‖ < δ ∧ ε ≤ |g z| := by
  rw [pdp_tendsto_punctured_iff]
  constructor
  · intro h
    push_neg at h
    exact h
  · rintro ⟨ε, hε, hδ⟩ h'
    obtain ⟨δ, hδpos, hδ'⟩ := h' ε hε
    obtain ⟨z, hz0, hzδ, hzε⟩ := hδ δ hδpos
    exact absurd (hδ' z hz0 hzδ) (not_lt.mpr hzε)

/-! ## 3. The identification of the raw parameter partial with `∂_{w_i} famFun Ĝ` -/

/-- On the `C¹`-locus of the sheet function, the raw expression
`∂_{w_i} famFun G (w,z) - ∂_i a(w)` is the parameter partial of the "hat" family `Ĝ`, provided
`z ≠ 0` and `‖z‖ < r0` (so that `famFun G` is `C¹` at `(w,z)`). -/
theorem pdp_hat_eq {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (i : Fin a)
    (Q0 : Set (Fin a → ℝ)) (r0 : ℝ)
    (hoff : ∀ w ∈ Q0, ∀ z : Fin b → ℝ, z ≠ 0 → ‖z‖ < r0 →
      ContDiffAt ℝ 1 (Work.WilG4c.famFun G) (Fin.append w z))
    {w : Fin a → ℝ} (hw : w ∈ Q0)
    (ha : ContDiffAt ℝ 1 (fun w' => G w' 0) w)
    {z : Fin b → ℝ} (hz : z ≠ 0) (hzr : ‖z‖ < r0) :
    Fin.append w z ∈ Work.WilG4b.c1Loc (Work.WilG4c.famFun (pdpHat G)) ∧
      fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append (Pi.single i 1) 0)
        - fderiv ℝ (fun w' => G w' 0) w (Pi.single i 1)
        = Work.WilG4b.dDir (Work.WilG4c.famFun (pdpHat G)) (Fin.castAdd b i)
            (Fin.append w z) := by
  classical
  set π : (Fin (a + b) → ℝ) →L[ℝ] (Fin a → ℝ) := pdpWtake a b with hπdef
  have hπ : ∀ u : Fin (a + b) → ℝ, π u = fun i => u (Fin.castAdd b i) :=
    fun u => pdpWtake_apply a b u
  have hπ_app : π (Fin.append w z) = w := pdpWtake_append a b w z
  set Ψ : (Fin (a + b) → ℝ) → ℝ := fun u => (fun w' => G w' 0) (π u) with hΨdef
  have hhat : Work.WilG4c.famFun (pdpHat G) = Work.WilG4c.famFun G - Ψ := by
    funext u
    simp only [hΨdef, hπ, Pi.sub_apply, pdpHat, Work.WilG4c.famFun]
  have hdiffG : DifferentiableAt ℝ (Work.WilG4c.famFun G) (Fin.append w z) :=
    (hoff w hw z hz hzr).differentiableAt_one
  have ha' : DifferentiableAt ℝ (fun w' => G w' 0) (π (Fin.append w z)) := by
    rw [hπ_app]; exact ha.differentiableAt_one
  have hdiffΨ : DifferentiableAt ℝ Ψ (Fin.append w z) := by
    have h := ha'.comp (Fin.append w z) π.differentiableAt
    simpa [hΨdef, Function.comp_def] using h
  have hc1π : ContDiffAt ℝ 1 (fun u : Fin (a + b) → ℝ => π u) (Fin.append w z) :=
    π.contDiff.contDiffAt
  have ha'' : ContDiffAt ℝ 1 (fun w' => G w' 0) (π (Fin.append w z)) := by
    rw [hπ_app]; exact ha
  have hc1Ψ : ContDiffAt ℝ 1 Ψ (Fin.append w z) := by
    have h := ha''.comp (Fin.append w z) hc1π
    simpa [hΨdef, Function.comp_def] using h
  have hfderivΨ : fderiv ℝ Ψ (Fin.append w z)
      = (fderiv ℝ (fun w' => G w' 0) w).comp π := by
    have h1 : Ψ = (fun w' => G w' 0) ∘ (fun u : Fin (a + b) → ℝ => π u) := rfl
    rw [h1, fderiv_comp (x := Fin.append w z) ha' π.differentiableAt,
      ContinuousLinearMap.fderiv, hπ_app]
  refine ⟨pdp_c1Loc_iff.mpr ?_, ?_⟩
  · rw [hhat]
    exact (hoff w hw z hz hzr).sub hc1Ψ
  · have key : fderiv ℝ (Work.WilG4c.famFun (pdpHat G)) (Fin.append w z)
          (Fin.append (Pi.single i 1) 0)
        = fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append (Pi.single i 1) 0)
          - fderiv ℝ (fun w' => G w' 0) w (Pi.single i 1) := by
      rw [hhat, fderiv_sub hdiffG hdiffΨ, hfderivΨ]
      show fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append (Pi.single i 1) 0)
          - ((fderiv ℝ (fun w' => G w' 0) w).comp π) (Fin.append (Pi.single i 1) 0)
        = fderiv ℝ (Work.WilG4c.famFun G) (Fin.append w z) (Fin.append (Pi.single i 1) 0)
          - fderiv ℝ (fun w' => G w' 0) w (Pi.single i 1)
      congr 1
      rw [ContinuousLinearMap.comp_apply, hπ]
      congr 1
      funext i'
      rw [Fin.append_left]
    simp only [Work.WilG4b.dDir]
    rw [pdp_single_castAdd i, ← key]

/-! ## 4. `Ω`-definability of the gain loci -/

theorem pdp_gainSet_mem (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) {a b F D : ℕ}
    (Fam : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hF : WilkiesDesign.CG.famGraph Fam ∈ S.Ω F D (a + b + 1)) (i : Fin a) :
    ∃ F' D' : ℕ, ∀ η : ℝ, pdpE Fam i η ∈ S.Ω F' D' (a + b) := by
  obtain ⟨A, B, hb⟩ := Work.WilCruxN.derivGraph_mem_clean S hcd (F0 := F) (D := D)
    (Work.WilG4c.famFun Fam) (Fin.castAdd b i)
    (by rw [Work.WilG4c.graphOf_famFun]; exact hF)
  set Dg : ℕ := Polynomial.eval D B with hDg
  have hdg : Work.WilG4b.derivGraph (Work.WilG4c.famFun Fam) (Fin.castAdd b i) ∈
      S.Ω A Dg (a + b + 1) := by
    rw [hDg]
    exact hb
  refine ⟨max A (4 * (a + b + 1) + 16) + 2, Dg + 4, fun η => ?_⟩
  have hge : {z : Fin (a + b + 1) → ℝ | η ≤ z (Fin.last (a + b))} ∈
      S.Ω (4 * (a + b + 1) + 16) ((Polynomial.C 4).eval Dg) (a + b + 1) := by
    simpa using Work.WilG5.leSet_mem (S := S) (Fin.last (a + b)) η
  have hdg' : Work.WilG4b.derivGraph (Work.WilG4c.famFun Fam) (Fin.castAdd b i) ∈
      S.Ω A ((Polynomial.C Dg).eval Dg) (a + b + 1) := by
    simpa using hdg
  have hI := Work.WilG1.Omega.inter₂ hdg' hge
  have hP := S.proj hI
  have hdeg : (Polynomial.eval Dg (Polynomial.C Dg + Polynomial.C 4)) = Dg + 4 := by
    simp
  rw [hdeg] at hP
  have hset : pdpE Fam i η = WilkiesDesign.projLast
      (Work.WilG4b.derivGraph (Work.WilG4c.famFun Fam) (Fin.castAdd b i) ∩
        {z : Fin (a + b + 1) → ℝ | η ≤ z (Fin.last (a + b))}) := by
    ext u
    simp only [pdpE, WilkiesDesign.projLast, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_setOf_eq, Fin.snoc_last]
  rw [hset]
  exact Work.WilG1.Omega.mono hP (by omega) le_rfl

/-- Negating a definable family preserves `Ω`-definability of its graph. -/
theorem pdp_negGraph_mem (S : WilkiesDesign.SOMin) {a b F D : ℕ}
    (Fam : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hF : WilkiesDesign.CG.famGraph Fam ∈ S.Ω F D (a + b + 1)) :
    ∃ F' D' : ℕ, WilkiesDesign.CG.famGraph (fun w z => -(Fam w z)) ∈ S.Ω F' D' (a + b + 1) := by
  obtain ⟨A, B, hb⟩ := Work.WilG4a.affine_comb_graph_mem S (a + b) F
  have hlo : WilkiesDesign.graphOf (fun u : Fin (a + b) → ℝ => Work.WilG4c.famFun Fam u) ∈
      S.Ω F D (a + b + 1) := by
    rw [Work.WilG4c.graphOf_famFun]; exact hF
  have hres := hb D 1 hlo hlo (0 : ℝ) (-1) 0
  refine ⟨A, MvPolynomial.eval ![D, 1] B, ?_⟩
  have hfun : (fun l : Fin (a + b) → ℝ =>
        (0 : ℝ) + (-1) * Work.WilG4c.famFun Fam l + 0 * Work.WilG4c.famFun Fam l)
      = Work.WilG4c.famFun (fun w z => -(Fam w z)) := by
    funext l
    simp only [Work.WilG4c.famFun, zero_mul, add_zero]
    ring
  rwa [hfun] at hres

/-! ## 5. Mean-value bounds from a derivative bound -/

/-- If the slice `G w` has derivative bounded by `M` on the closed `τ`-ball, then it is
`M`-Lipschitz there and `|G w z - G w 0| ≤ M‖z‖`. -/
theorem pdp_lip_of_bound {a b : ℕ} (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ) (w : Fin a → ℝ)
    {τ M : ℝ} (hτ : 0 ≤ τ) (hM : 0 ≤ M)
    (hdiff : ∀ z ∈ Metric.closedBall (0 : Fin b → ℝ) τ, DifferentiableAt ℝ (G w) z)
    (hbound : ∀ z ∈ Metric.closedBall (0 : Fin b → ℝ) τ, ‖fderiv ℝ (G w) z‖ ≤ M) :
    (∀ z z' : Fin b → ℝ, ‖z‖ ≤ τ → ‖z'‖ ≤ τ → |G w z - G w z'| ≤ M * ‖z - z'‖) ∧
      (∀ z : Fin b → ℝ, ‖z‖ ≤ τ → |G w z - G w 0| ≤ M * ‖z‖) := by
  have hmem : ∀ z : Fin b → ℝ, ‖z‖ ≤ τ → z ∈ Metric.closedBall (0 : Fin b → ℝ) τ := by
    intro z hz
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  constructor
  · intro z z' hz hz'
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := G w) (C := M)
      (fun x hx => hdiff x hx) (fun x hx => hbound x hx) (convex_closedBall (0 : Fin b → ℝ) τ)
      (hmem z hz) (hmem z' hz')
    simpa [Real.norm_eq_abs, abs_sub_comm, norm_sub_rev] using h
  · intro z hz
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := G w) (C := M)
      (fun x hx => hdiff x hx) (fun x hx => hbound x hx) (convex_closedBall (0 : Fin b → ℝ) τ)
      (hmem 0 (by simpa using hτ)) (hmem z hz)
    simpa [Real.norm_eq_abs] using h

/-! ## 6. Bookkeeping for `Ω`-unions with explicit numerals -/

theorem pdp_union_mem {S : WilkiesDesign.SOMin} {n : ℕ} {X Y : Set (Fin n → ℝ)}
    {F₁ D₁ F₂ D₂ : ℕ} (h1 : X ∈ S.Ω F₁ D₁ n) (h2 : Y ∈ S.Ω F₂ D₂ n) :
    X ∪ Y ∈ S.Ω (max F₁ F₂) (D₁ + D₂) n := by
  have h1' : X ∈ S.Ω (max F₁ F₂) D₁ n := Work.WilG1.Omega.mono h1 (le_max_left _ _) le_rfl
  have h2' : Y ∈ S.Ω (max F₁ F₂) D₂ n := Work.WilG1.Omega.mono h2 (le_max_right _ _) le_rfl
  have h := S.union (F := max F₁ F₂) (n := n) (k := 2)
    (D := fun i : Fin 2 => if i = 0 then D₁ else D₂)
    (A := fun i : Fin 2 => if i = 0 then X else Y)
    (by intro i; fin_cases i
        · simpa using h1'
        · simpa using h2')
  rw [Fin.sum_univ_two] at h
  rwa [Work.WilG1.Omega.iUnion_fin_two X Y] at h


/-- TEMPORARY STUB — to be replaced by `Work.WilCrux.flatGraphMem`. -/
theorem pdp_flatGraph_stub (S : WilkiesDesign.SOMin) {a b F D : ℕ}
    (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1)) :
    ∃ F' D' : ℕ, WilkiesDesign.graphOf (fun w : Fin a → ℝ => G w 0) ∈ S.Ω F' D' (a + 1) :=
  flatGraphMem S G hG

/-- TEMPORARY STUB — to be replaced by `Work.WilCrux.Clean.AccSetMem`. -/
theorem pdp_accSet_stub (S : WilkiesDesign.SOMin) {a b F D : ℕ} (E : Set (Fin (a + b) → ℝ))
    (hE : E ∈ S.Ω F D (a + b)) :
    ∃ F' D' : ℕ, pdpAcc E ∈ S.Ω F' D' a :=
  Work.WilCrux.Clean.AccSetMem S E hE

/-- TEMPORARY STUB — to be replaced by `Work.WilCrux.Clean.MonotonePiecesOnLine`. -/
theorem pdp_monoPieces_stub {n : ℕ} (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    (F D : ℕ) (i : Fin n) :
    ∃ K : ℕ, ∀ (H : (Fin n → ℝ) → ℝ), WilkiesDesign.graphOf H ∈ S.Ω F D (n + 1) →
      ∀ (w₁ : Fin n → ℝ), ∃ brk : Finset ℝ, brk.card ≤ K ∧
        (∀ s : ℝ, s ∉ brk → DifferentiableAt ℝ (fun t : ℝ => H (w₁ + t • Pi.single i 1)) s) ∧
        ∀ s t : ℝ, s < t → (∀ u ∈ Set.Ioo s t, u ∉ brk) →
          MonotoneOn (fun t : ℝ => H (w₁ + t • Pi.single i 1)) (Set.Ioo s t) ∨
          AntitoneOn (fun t : ℝ => H (w₁ + t • Pi.single i 1)) (Set.Ioo s t) :=
  Work.WilCruxN.MonotonePiecesOnLine S hcd i

/-- TEMPORARY STUB — to be replaced by `Work.WilCrux.Clean.SheetHatGraphMem`. -/
theorem pdp_sheetHat_stub (S : WilkiesDesign.SOMin) {a b F D F₁ D₁ : ℕ}
    (G : (Fin a → ℝ) → (Fin b → ℝ) → ℝ)
    (hG : WilkiesDesign.CG.famGraph G ∈ S.Ω F D (a + b + 1))
    (ha : WilkiesDesign.graphOf (fun w : Fin a → ℝ => G w 0) ∈ S.Ω F₁ D₁ (a + 1)) :
    ∃ F₂ D₂ : ℕ, WilkiesDesign.CG.famGraph
      (fun (w : Fin a → ℝ) (z : Fin b → ℝ) => G w z - G w 0)
        ∈ S.Ω F₂ D₂ (a + b + 1) :=
  Work.WilCrux.Clean.SheetHatGraphMem S G hG ha

