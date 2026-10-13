/-
  WilG4a — auxiliary lemmas for the `n = 1` "full `C¹`" family lemma
  (`Work.WilG4a.lipschitz_charts`).

  This module collects the self-contained bookkeeping used by the assembly in
  `Submission/Work/WilG4a/lipschitz_charts.lean`:

  * the two-way correspondence between the slices of a family member at a point `z` and the
    slices of the uncurried graph (`sliceFun_snoc`, `sliceDiff_snoc`), and the identity member
    (`sliceFun_id`, `isSliceDeriv_id`, `graphFam_id`, `identity_graph_mem`);

  * injectivity of the dominating member of a good cell on a fibre (`goodCell_injOn`) and
    uniqueness of the point of a fibre realising a prescribed value of the dominating member
    (`chart1_uniq_of_dichotomy`);

  * the polynomial bookkeeping absorbing the substitution `D ↦ max D 1` that is needed because
    the enlarged family contains the identity member, of degree one
    (`mvpoly_eval_nat_mono`, `exists_degree_bound`, `mvpoly_eval_real_bound`);

  * the one-variable generic smoothness input — the `k = 1` case of
    `WilkiesDesign.CG.G1_generic_smooth` — in the forms `oneDim_nonC1_finite` (finiteness of the
    non-`C¹` locus of a definable `g : ℝ → ℝ`) and `slice_smooth_input` (the same statement for
    functions on `Fin 1 → ℝ`), together with its consequence `sliceTame_oneDim`: the one-variable
    tameness `SliceTame` of the slices, which is the hypothesis of the cell decomposition
    `lipschitz_decomp`.

  The last block is the only place where the one-dimensional theory of the structure enters the
  `n = 1` family lemma.
-/
import Mathlib
import Submission.Work.WilG4a.LipChartsDefs
import Submission.Work.WilG4a.lipschitz_slice_tame
import Submission.Work.WilG4a.lipschitz_onevar_bound
import Submission.Work.WilG4a.oneDim_C1_finite
import Submission.Work.WilG1.Thin.sliceGraph_mem

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesConjecture WilkiesDesign

variable {p : ℕ}


/-! ## 5. Auxiliary facts about the slices, the identity and the degree bookkeeping -/

theorem update_snoc_last {p : ℕ} (l : Fin p → ℝ) (x y : ℝ) :
    Function.update (Fin.snoc l x : Fin (p+1) → ℝ) (Fin.last p) y = Fin.snoc l y := by
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [Function.update_of_ne (by simp [Fin.castSucc_ne_last])]; simp
  · simp

theorem sliceFun_snoc {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) (x : ℝ) :
    sliceFun f (Fin.snoc l x) = fun y : ℝ => f l y := by
  funext y
  rw [sliceFun, update_snoc_last, famFun]
  simp [Fin.snoc_last]

theorem sliceDiff_snoc {p : ℕ} (f : (Fin p → ℝ) → ℝ → ℝ) (l : Fin p → ℝ) (x : ℝ) :
    Fin.snoc l x ∈ sliceDiff f ↔ DifferentiableAt ℝ (fun y : ℝ => f l y) x := by
  simp only [sliceDiff, Set.mem_ofPred_eq, sliceFun_snoc, Fin.snoc_last]

theorem sliceFun_id {p : ℕ} (z : Fin (p+1) → ℝ) :
    sliceFun (fun (_ : Fin p → ℝ) (x : ℝ) => x) z = fun y : ℝ => y := by
  funext y
  simp [sliceFun, famFun]

theorem isSliceDeriv_id {p : ℕ} (z : Fin (p+1) → ℝ) :
    IsSliceDeriv (fun (_ : Fin p → ℝ) (x : ℝ) => x) z 1 := by
  show HasDerivAt (sliceFun (fun _ x => x) z) 1 (z (Fin.last p))
  rw [sliceFun_id]
  exact hasDerivAt_id (z (Fin.last p))

theorem xDeriv_eq_of_isSliceDeriv {p : ℕ} {f : (Fin p → ℝ) → ℝ → ℝ} {z : Fin (p+1) → ℝ}
    {s : ℝ} (h : IsSliceDeriv f z s) : xDeriv f z = s := h.deriv

/-- The identity member of the enlarged family has non-vanishing (indeed unit) slice
derivative, so on any cell dominated by `F i₁` the member `F i₁` has non-vanishing
derivative. -/
theorem ne_zero_of_domSet_id {p : ℕ} {f : (Fin p → ℝ) → ℝ → ℝ} {z : Fin (p+1) → ℝ}
    (hz : z ∈ domSet (fun (_ : Fin p → ℝ) (x : ℝ) => x) f) : xDeriv f z ≠ 0 := by
  obtain ⟨s, t, hs, ht, hle⟩ := hz
  have hs1 : s = 1 := ((isSliceDeriv_id z).unique hs).symm
  have ht' : xDeriv f z = t := xDeriv_eq_of_isSliceDeriv ht
  rw [hs1, abs_one] at hle
  rw [ht']
  intro h0
  rw [h0, abs_zero] at hle
  exact absurd hle (by norm_num)

/-- In a good cell, the dominating member is injective on every fibre. -/
theorem goodCell_injOn {k : ℕ} {F : Fin k → (Fin p → ℝ) → ℝ → ℝ} {κ : Set (Fin (p+1) → ℝ)}
    {i₁ : Fin k} (hgood : GoodCell k F κ i₁) (l : Fin p → ℝ) :
    Set.InjOn (fun x => F i₁ l x) (fibre κ l) := by
  rcases hgood.2.2.2.2 l with hsub | ⟨a, b, hab⟩
  · intro x₁ h₁ x₂ h₂ _
    exact hsub h₁ h₂
  · have key : ∀ y ∈ Set.Ioo a b, Fin.snoc l y ∈ κ := by
      intro y hy
      have h : y ∈ fibre κ l := hab ▸ hy
      exact h
    have hcont : ContinuousOn (fun x => F i₁ l x) (Set.Ioo a b) := by
      have hd : DifferentiableOn ℝ (fun x => F i₁ l x) (Set.Ioo a b) := fun y hy => by
        have h := hgood.1 i₁ (key y hy)
        rw [sliceDiff_snoc] at h
        exact h.differentiableWithinAt
      exact hd.continuousOn
    rcases hgood.2.2.2.1 with hpos | hneg
    · have hmono : StrictMonoOn (fun x => F i₁ l x) (Set.Ioo a b) := by
        refine strictMonoOn_of_deriv_pos (convex_Ioo a b) hcont ?_
        intro y hy
        rw [interior_Ioo] at hy
        obtain ⟨s, hs, hspos⟩ := hpos (key y hy)
        have hs' : deriv (fun x => F i₁ l x) y = s := by
          have h := hs
          simp only [IsSliceDeriv] at h
          rw [sliceFun_snoc, Fin.snoc_last] at h
          exact h.deriv
        rw [hs']; exact hspos
      intro x₁ h₁ x₂ h₂ h
      exact hmono.injOn (hab ▸ h₁) (hab ▸ h₂) h
    · have hanti : StrictAntiOn (fun x => F i₁ l x) (Set.Ioo a b) := by
        refine strictAntiOn_of_deriv_neg (convex_Ioo a b) hcont ?_
        intro y hy
        rw [interior_Ioo] at hy
        obtain ⟨s, hs, hsneg⟩ := hneg (key y hy)
        have hs' : deriv (fun x => F i₁ l x) y = s := by
          have h := hs
          simp only [IsSliceDeriv] at h
          rw [sliceFun_snoc, Fin.snoc_last] at h
          exact h.deriv
        rw [hs']; exact hsneg
      intro x₁ h₁ x₂ h₂ h
      exact hanti.injOn (hab ▸ h₁) (hab ▸ h₂) h

/-- Uniqueness of the point of the fibre realising a prescribed value of the dominating
member, in either branch of the dichotomy of `lipschitz_decomp`. -/
theorem chart1_uniq_of_dichotomy {k : ℕ} {F : Fin k → (Fin p → ℝ) → ℝ → ℝ}
    {κ : Set (Fin (p+1) → ℝ)} {i₁ : Fin k}
    (hdich : GoodCell k F κ i₁ ∨ ∀ l, (fibre κ l).Subsingleton) :
    ∀ (l : Fin p → ℝ) (t y₁ y₂ : ℝ), Fin.snoc l y₁ ∈ κ →
      F i₁ l y₁ = Aend κ (F i₁) l + (Bend κ (F i₁) l - Aend κ (F i₁) l) * t →
      Fin.snoc l y₂ ∈ κ →
      F i₁ l y₂ = Aend κ (F i₁) l + (Bend κ (F i₁) l - Aend κ (F i₁) l) * t → y₁ = y₂ := by
  rcases hdich with hgood | hpt
  · intro l t y₁ y₂ h₁ e₁ h₂ e₂
    refine goodCell_injOn hgood l h₁ h₂ ?_
    show F i₁ l y₁ = F i₁ l y₂
    rw [e₁, e₂]
  · intro l t y₁ y₂ h₁ _ h₂ _
    exact hpt l h₁ h₂

/-! ### The identity component of the enlarged family -/

theorem graphFam_id (p : ℕ) :
    graphFam (fun (_ : Fin p → ℝ) (x : ℝ) => x) =
      {z : Fin (p+2) → ℝ | z (Fin.last (p+1)) = z (Fin.castSucc (Fin.last p))} := by
  ext z
  rw [mem_graphFam]
  simp

theorem identity_graph_mem (S : SOMin) (p F0 D : ℕ) (hF : p + 2 ≤ F0) (hD : 1 ≤ D) :
    graphFam (fun (_ : Fin p → ℝ) (x : ℝ) => x) ∈ S.Ω F0 D (p + 1 + 1) := by
  have hP : (MvPolynomial.X (Fin.last (p+1)) -
      MvPolynomial.X (Fin.castSucc (Fin.last p)) : MvPolynomial (Fin (p+2)) ℝ).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
    rw [max_le_iff]
    constructor <;> rw [MvPolynomial.totalDegree_X]
  have h := S.hyp (p+2) (MvPolynomial.X (Fin.last (p+1)) -
      MvPolynomial.X (Fin.castSucc (Fin.last p)) : MvPolynomial (Fin (p+2)) ℝ)
  rw [graphFam_id]
  have hset : {z : Fin (p+2) → ℝ | MvPolynomial.eval z (MvPolynomial.X (Fin.last (p+1)) -
      MvPolynomial.X (Fin.castSucc (Fin.last p)) : MvPolynomial (Fin (p+2)) ℝ) = 0} =
      {z : Fin (p+2) → ℝ | z (Fin.last (p+1)) = z (Fin.castSucc (Fin.last p))} := by
    ext z; simp [sub_eq_zero]
  rw [← hset]
  exact Work.WilG1.Omega.mono h hF (le_trans hP hD)

/-! ### Degree bookkeeping for the final bounds -/

theorem mvpoly_eval_nat_mono (b : MvPolynomial (Fin 2) ℕ) {D D' r : ℕ} (h : D ≤ D') :
    MvPolynomial.eval ![D, r] b ≤ MvPolynomial.eval ![D', r] b := by
  induction b using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add]; exact add_le_add hp hq
  | mul_X p i hp =>
      rw [map_mul, MvPolynomial.eval_X, map_mul, MvPolynomial.eval_X]
      have hi : ![D, r] i ≤ ![D', r] i := by fin_cases i <;> simp [h]
      exact Nat.mul_le_mul hp hi

/-- A single degree polynomial bounding both `b₁` and `b₂` at `![max D 1, 1]` in terms of
`![D, 1]`. -/
theorem exists_degree_bound (b₁ b₂ : MvPolynomial (Fin 2) ℕ) :
    ∃ b : MvPolynomial (Fin 2) ℕ, ∀ D : ℕ,
      MvPolynomial.eval ![max D 1, 1] b₁ ≤ MvPolynomial.eval ![D, 1] b ∧
      MvPolynomial.eval ![max D 1, 1] b₂ ≤ MvPolynomial.eval ![D, 1] b := by
  refine ⟨b₁ + b₂ + MvPolynomial.C ((b₁ + b₂).eval ![1,1]), fun D => ?_⟩
  have hmax : max D 1 = D ∨ max D 1 = 1 := by omega
  constructor
  · rcases hmax with h | h
    · rw [h, map_add, map_add, map_add]
      exact le_add_of_le_of_nonneg (le_add_of_nonneg_right (Nat.zero_le _)) (Nat.zero_le _)
    · rw [h, map_add, map_add, map_add]
      simp only [MvPolynomial.eval_C]
      omega
  · rcases hmax with h | h
    · rw [h, map_add, map_add, map_add]
      exact le_add_of_le_of_nonneg (le_add_of_nonneg_left (Nat.zero_le _)) (Nat.zero_le _)
    · rw [h, map_add, map_add, map_add]
      simp only [MvPolynomial.eval_C]
      omega

/-- **A count bound uniform in the degree.**  Replacing the degree variable `D` by
`max D 1` (needed because the enlarged family contains the identity, of degree `1`) can be
absorbed into a single polynomial, at the cost of a crude coefficient bound.  This is
`Work.WilG4a.lipschitz_onevar_bound` (module `Submission.Work.WilG4a.lipschitz_onevar_bound`),
which is stated exactly in this form. -/
theorem mvpoly_eval_real_bound (c : MvPolynomial (Fin 3) ℝ) :
    ∃ c' : MvPolynomial (Fin 3) ℝ, ∀ D k : ℕ,
      MvPolynomial.eval ![(max D 1 : ℝ), (1 : ℝ), (k : ℝ)] c ≤
        MvPolynomial.eval ![(D : ℝ), (1 : ℝ), (k : ℝ)] c' :=
  Work.WilG4a.lipschitz_onevar_bound c

/-! ### The `n = 1` generic smoothness input, and the tameness of the slices

`SliceTame` (the hypothesis of `lipschitz_decomp`) is the fibre-wise form of the one-variable
generic smoothness theorem: for every `Ω`-definable family member `f` and every parameter `l`,
the set of `x` at which the slice `y ↦ f l y` is not `C¹` has empty interior.  It is obtained
from the `k = 1` case of `WilkiesDesign.CG.G1_generic_smooth`, namely the statement that the
non-`C¹` locus of an `Ω`-definable one-variable function is *finite* — which is proved in the
sibling module `Submission.Work.WilG4a.oneDim_nonCk_finite` as `Work.WilG4a.nonC1_locus_finite`.
A finite set has empty interior, and the one-dimensional statement is transported to
`Fin 1 → ℝ` and then to the slices exactly as in `lipschitz_slice_tame`. -/

/-- **The one-variable generic smoothness input** (`k = 1`): the non-`C¹` locus of an
`Ω`-definable one-variable function is finite.  This is `Work.WilG4a.oneDim_C1_finite`
(module `Submission.Work.WilG4a.oneDim_C1_finite`), proved from the `Ω`-definability of the
derivative graph (`derivGraph_mem`), the one-dimensional thinness of the non-differentiability
locus (`nondiff_interval_free`) and the finiteness of the discontinuity locus
(`cont_off_finite`).  The `SharpDeriv` argument is not needed for the `k = 1` case. -/
theorem oneDim_nonC1_finite (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) {F D : ℕ}
    (g : ℝ → ℝ) (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) :
    {x : ℝ | ¬ ContDiffAt ℝ 1 g x}.Finite :=
  Work.WilG4a.oneDim_C1_finite S hcd g hg

/-- A finite subset of `ℝ` has empty interior. -/
theorem interior_eq_empty_of_finite {s : Set ℝ} (h : s.Finite) : interior s = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro x hx
  rw [mem_interior_iff_mem_nhds] at hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hx
  have hinf : (Set.Ioo (x - ε) (x + ε)).Infinite := Set.Ioo_infinite (by linarith)
  refine hinf (h.subset ?_)
  intro y hy
  refine hball ?_
  rw [Metric.mem_ball, Real.dist_eq, abs_lt]
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- The `Fin 1 → ℝ` form of the one-variable generic smoothness input. -/
theorem slice_smooth_input (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) :
    ∀ {F D : ℕ} (H : (Fin 1 → ℝ) → ℝ), graphOf H ∈ S.Ω F D 2 →
      interior {u : Fin 1 → ℝ | ¬ ContDiffAt ℝ 1 H u} = ∅ := by
  intro F D H hH
  set G : ℝ → ℝ := fun x => H (fun _ : Fin 1 => x) with hG
  have hGfun : (fun x : Fin 1 → ℝ => G (x 0)) = H := by
    funext x
    have hx : (fun _ : Fin 1 => x 0) = x := by
      funext i
      rw [Subsingleton.elim i 0]
    simp only [hG]
    rw [hx]
  have hGmem : graphOf (fun x : Fin 1 → ℝ => G (x 0)) ∈ S.Ω F D 2 := by
    rw [hGfun]; exact hH
  have hempty : interior {x : ℝ | ¬ ContDiffAt ℝ 1 G x} = ∅ :=
    interior_eq_empty_of_finite (oneDim_nonC1_finite S hcd hder G hGmem)
  rw [Set.eq_empty_iff_forall_notMem] at hempty ⊢
  intro u hu
  rw [mem_interior_iff_mem_nhds] at hu
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hu
  have huconst : u = fun _ : Fin 1 => u 0 := by
    funext i
    rw [Subsingleton.elim i 0]
  refine hempty (u 0) ?_
  rw [mem_interior_iff_mem_nhds]
  refine Metric.mem_nhds_iff.mpr ⟨ε, hε, fun v hv => ?_⟩
  have hmem_ball : (fun _ : Fin 1 => v) ∈ Metric.ball u ε := by
    rw [Metric.mem_ball, huconst, dist_fin1_eq]
    exact hv
  have hbad : ¬ ContDiffAt ℝ 1 H (fun _ : Fin 1 => v) := hball hmem_ball
  intro hcdG
  have hproj : ContDiffAt ℝ 1 (fun w : Fin 1 → ℝ => w 0) (fun _ : Fin 1 => v) :=
    contDiffAt_apply ℝ ℝ (0 : Fin 1) (fun _ : Fin 1 => v)
  have hcomp : ContDiffAt ℝ 1 (G ∘ fun w : Fin 1 → ℝ => w 0) (fun _ : Fin 1 => v) :=
    ContDiffAt.comp (fun _ : Fin 1 => v) hcdG hproj
  exact hbad (by rw [← hGfun]; exact hcomp)

/-- The one-variable tameness of the slices, from the `Fin 1 → ℝ` generic smoothness input:
this is the proof of `lipschitz_slice_tame` with the input used only at arity one. -/
theorem sliceTame_of_oneDim (S : WilkiesDesign.SOMin) (p F0 : ℕ)
    (hsm : ∀ {F D : ℕ} (g : (Fin 1 → ℝ) → ℝ), WilkiesDesign.graphOf g ∈ S.Ω F D 2 →
        interior {z : Fin 1 → ℝ | ¬ ContDiffAt ℝ 1 g z} = ∅) :
    Work.WilG4a.SliceTame S p F0 := by
  intro D f hf l
  obtain ⟨a, b, hmem⟩ := Work.WilG1.Thin.sliceGraph_mem (S := S) (p := p) (F := F0) (D := D)
    (fun z : Fin (p + 1) → ℝ => f (fun i => z (Fin.castSucc i)) (z (Fin.last p))) hf l
  have hfun : (fun u : Fin 1 → ℝ => (fun z : Fin (p + 1) → ℝ =>
        f (fun i => z (Fin.castSucc i)) (z (Fin.last p))) (Fin.snoc l (u 0)))
      = fun u : Fin 1 → ℝ => f l (u 0) := by
    funext u
    simp [Fin.snoc_castSucc, Fin.snoc_last]
  have hmem' : WilkiesDesign.graphOf (fun u : Fin 1 → ℝ => f l (u 0)) ∈ S.Ω a (b.eval D) 2 := by
    rwa [hfun] at hmem
  have hempty := hsm (fun u : Fin 1 → ℝ => f l (u 0)) hmem'
  change interior {x : ℝ | ¬ SliceSmooth (f l) x} = ∅
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
  have hsub : Metric.ball (fun _ : Fin 1 => x) ε ⊆
      {z : Fin 1 → ℝ | ¬ ContDiffAt ℝ 1 (fun u : Fin 1 → ℝ => f l (u 0)) z} := by
    intro z hz hcd
    rw [Metric.mem_ball, dist_fin1_eq, Real.dist_eq] at hz
    have hmem_ball : z 0 ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq]
      exact hz
    exact (interior_subset (hball hmem_ball)) (sliceSmooth_of_contDiffAt_fin1 z hcd)
  have hmem_int : (fun _ : Fin 1 => x) ∈ interior
      {z : Fin 1 → ℝ | ¬ ContDiffAt ℝ 1 (fun u : Fin 1 → ℝ => f l (u 0)) z} := by
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (Metric.ball_mem_nhds _ hε) hsub
  rw [hempty] at hmem_int
  exact hmem_int

/-- **The tameness of the slices**, from the `k = 1` generic smoothness theorem. -/
theorem sliceTame_oneDim (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (p F0 : ℕ) :
    Work.WilG4a.SliceTame S p F0 :=
  sliceTame_of_oneDim S p F0 (slice_smooth_input S hcd hder)

end Work.WilG4a
