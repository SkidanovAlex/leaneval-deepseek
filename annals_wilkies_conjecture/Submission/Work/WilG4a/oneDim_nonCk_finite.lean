/-
  WilG4a / `oneDim_nonCk_finite`.

  For a function `g : ℝ → ℝ` whose graph is `Ω F D 2`-definable in a sharply o-minimal
  structure (with sharp cell decomposition and sharp derivatives), the set of points at which
  `g` fails to be `C^k` is finite, for every `k : ℕ`.

  * `k = 0`: an `Ω`-definable function is continuous off a finite set (`cont_off_finite`), and
    `C^0` at a point means continuity on a neighbourhood, so the complement of the `C^0`-locus
    is contained in the closure of the discontinuity set, which is finite.
  * `nondiff_locus_finite`: the non-differentiability locus is `Ω`-definable
    (`diffLocus_mem`); it contains no non-degenerate interval, since on an interval of
    continuity it would be an interval of non-differentiability, contradicting
    `nondiff_interval_free`.
  * `nonC1_locus_finite` (`k = 1`): a point at which `g` is differentiable but not `C¹` is
    either non-differentiable, or `deriv g` extended by zero off the differentiability locus is
    discontinuous there.  Both capturing sets are finite.
  * the induction step `k → k - 1`: the graph of the derivative over the `C¹`-locus is
    `Ω`-definable (sharp derivatives); a point of the `C¹`-locus at which the extension-by-zero
    of `deriv g` off that locus is `C^{k-1}` is `C^k` for `g`.
-/
import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG1.Basic
import Submission.Work.WilG1.Calc.finite_of_interior_empty
import Submission.Work.WilG1.Calc.lt_mem
import Submission.Work.WilG1.Calc.pos_mem
import Submission.Work.WilG1.Calc.supBall_mem
import Submission.Work.WilG1.Analysis.no_strictLocalMax_interval
import Submission.Work.WilG4b.infinite_contains_Ioo
import Submission.Work.WilG4b.thrSet_mem
import Submission.Work.WilG4b.posPoly_mem
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.sharpCD_fintype
import Submission.Work.WilG4a.isCell_fiber
import Submission.Work.WilG4a.cont_off_finite
import Submission.Work.WilG4a.nondiff_interval_free
import Submission.Work.WilG4a.diffLocus_mem
import Submission.Work.WilG4a.extDeriv_graph_mem
import Submission.Work.WilG4a.extDeriv1_graph_mem

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesDesign WilkiesConjecture
open Work.WilG1 Work.WilG4b
open Filter
open scoped Topology

/-! ## 1. Two extensions of `deriv g` by zero -/

/-- `deriv g`, extended by `0` off the differentiability locus of `g`. -/
noncomputable def extDeriv (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => if DifferentiableAt ℝ g x then deriv g x else 0

/-- `deriv g`, extended by `0` off the `C¹`-locus of `g`. -/
noncomputable def extDeriv1 (g : ℝ → ℝ) : ℝ → ℝ :=
  fun x => if ContDiffAt ℝ 1 g x then deriv g x else 0

/-! ## 2. Elementary transfers between `ℝ` and `Fin 1 → ℝ` -/

lemma liftR_compl' (A : Set ℝ) : (liftR A)ᶜ = liftR Aᶜ := by
  ext z
  simp [liftR]

lemma finite_liftR_iff (A : Set ℝ) : (liftR A).Finite ↔ A.Finite := by
  constructor
  · intro h
    have hinj : Set.InjOn (fun z : Fin 1 → ℝ => z 0) (liftR A) := by
      intro u _ v _ huv
      funext i
      rw [Subsingleton.elim i 0]
      exact huv
    have himg : (fun z : Fin 1 → ℝ => z 0) '' liftR A = A := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hx
        exact ⟨fun _ => x, hx, rfl⟩
    rw [← himg]
    exact h.image _
  · intro h
    have himg : (fun x : ℝ => fun _ : Fin 1 => x) '' A = liftR A := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hz
        exact ⟨z 0, hz, by funext i; rw [Subsingleton.elim i 0]⟩
    rw [← himg]
    exact h.image _

/-- The interior of the lift of a set of reals is the preimage of the interior. -/
lemma interior_liftR_eq (A : Set ℝ) :
    interior (liftR A) = (Homeomorph.funUnique (Fin 1) ℝ) ⁻¹' interior A := by
  have h3 : (Homeomorph.funUnique (Fin 1) ℝ) '' liftR A = A := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [liftR, Homeomorph.funUnique_apply] using hy
    · intro hz
      exact ⟨fun _ => z, by simpa [liftR] using hz,
        by simp [Homeomorph.funUnique_apply]⟩
  have h2 := Homeomorph.image_interior (Homeomorph.funUnique (Fin 1) ℝ) (liftR A)
  rw [h3] at h2
  rw [← h2, Set.preimage_image_eq _ (Homeomorph.injective _)]

/-- Membership in the interior of a lift. -/
lemma mem_interior_liftR_iff {A : Set ℝ} {z : Fin 1 → ℝ} :
    z ∈ interior (liftR A) ↔ z 0 ∈ interior A := by
  rw [interior_liftR_eq]
  exact Iff.of_eq (by rfl)

/-- The interior of the lift of a set of reals is empty iff the interior of the set is. -/
lemma interior_liftR_eq_empty_iff (A : Set ℝ) : interior (liftR A) = ∅ ↔ interior A = ∅ := by
  rw [interior_liftR_eq]
  constructor
  · intro h
    rw [Set.eq_empty_iff_forall_notMem] at h ⊢
    intro y hy
    obtain ⟨x, hx⟩ := (Homeomorph.surjective (Homeomorph.funUnique (Fin 1) ℝ)) y
    refine h x ?_
    show (Homeomorph.funUnique (Fin 1) ℝ) x ∈ interior A
    rw [hx]
    exact hy
  · intro h
    rw [h, Set.preimage_empty]

/-- A point of the interior of a set of reals has a non-degenerate interval inside the set. -/
lemma exists_Ioo_subset_of_mem_interior {A : Set ℝ} {z : ℝ} (hz : z ∈ interior A) :
    ∃ c d : ℝ, c < d ∧ Set.Ioo c d ⊆ A := by
  rw [mem_interior_iff_mem_nhds] at hz
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hz
  refine ⟨z - ε, z + ε, by linarith, fun t ht => ?_⟩
  refine hsub ?_
  rw [Set.mem_Ioo] at ht
  rw [Metric.mem_ball, Real.dist_eq]
  rw [abs_lt]
  constructor <;> linarith [ht.1, ht.2]

/-- A finite set not containing `x` can be avoided on an interval around `x`. -/
lemma exists_Ioo_disjoint_finite {S : Set ℝ} (hS : S.Finite) {x : ℝ} (hx : x ∉ S) :
    ∃ η : ℝ, 0 < η ∧ Set.Ioo (x - η) (x + η) ∩ S = ∅ := by
  have hopen : IsOpen Sᶜ := hS.isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds hx)
  refine ⟨ε / 2, by linarith, ?_⟩
  rw [Set.eq_empty_iff_forall_notMem]
  intro t ht
  rw [Set.mem_inter_iff] at ht
  refine (hball ?_) ht.2
  rw [Set.mem_Ioo] at ht
  rw [Metric.mem_ball, Real.dist_eq]
  rw [abs_lt]
  constructor <;> linarith [ht.1.1, ht.1.2]

/-! ## 3. Auxiliary facts about `Fin 1`/`Fin 2` and the family notation -/

lemma fin_last_zero : (Fin.last 0 : Fin 1) = 0 := Fin.ext rfl

lemma fin_castSucc_zero_two : (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 := Fin.ext rfl

lemma xDir_zero : xDir 0 = (0 : Fin 1) := by
  simp only [xDir, fin_last_zero]

/-- The constant family over `Fin 0` reads as `thrDinG`. -/
lemma famFun_const (g : ℝ → ℝ) :
    famFun (fun _ : Fin 0 → ℝ => fun y => g y) = thrDinG g := by
  funext z
  simp only [famFun, thrDinG]
  rw [fin_last_zero]

lemma graphFam_const (g : ℝ → ℝ) :
    graphFam (fun _ : Fin 0 → ℝ => fun y => g y)
      = graphOf (fun x : Fin 1 → ℝ => g (x 0)) := by
  rw [← graphOf_famFun, famFun_const]
  rfl

/-- The `C¹`-locus of the constant family is the lift of the `C¹`-locus of `g`. -/
lemma smoothLocus_zero_eq (g : ℝ → ℝ) :
    smoothLocus (fun _ : Fin 0 → ℝ => fun y => g y) 1
      = liftR {x : ℝ | ContDiffAt ℝ 1 g x} := by
  have h1 : smoothLocus (fun _ : Fin 0 → ℝ => fun y => g y) 1
      = interior {x : Fin 1 → ℝ | ContDiffAt ℝ 1 (thrDinG g) x} := by
    simp only [smoothLocus, famFun_const, Nat.cast_one]
  ext z
  rw [h1, thrMem_interior_c1 g z]
  rfl

/-! ## 4. The `Ω`-membership of the two extensions -/

/-- The graph of `extDeriv g` is `Ω`-definable (uses the delegated `extDeriv_graph_mem`). -/
lemma extDeriv_graph_mem' (S : SOMin) (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (g : ℝ → ℝ),
      graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2 →
      graphOf (fun x : Fin 1 → ℝ => extDeriv g (x 0)) ∈ S.Ω a (b.eval D) 2 := by
  obtain ⟨a, b, h⟩ := Work.WilG4a.extDeriv_graph_mem S F
  refine ⟨a, b, fun D g hg => ?_⟩
  have hset : graphOf (fun x : Fin 1 → ℝ => extDeriv g (x 0)) =
      ({z : Fin 2 → ℝ | DifferentiableAt ℝ g (z 0) ∧ z 1 = deriv g (z 0)} ∪
        {z : Fin 2 → ℝ | ¬ DifferentiableAt ℝ g (z 0) ∧ z 1 = 0}) := by
    ext z
    have hinit : (Fin.init z) 0 = z 0 := by simp [Fin.init, fin_castSucc_zero_two]
    simp only [graphOf, Set.mem_ofPred_eq, Set.mem_union, extDeriv, hinit]
    by_cases hd : DifferentiableAt ℝ g (z 0)
    · simp [hd]
    · simp [hd]
  rw [hset]
  exact h D g hg

/-- The graph of `extDeriv1 g` is `Ω`-definable (uses the delegated `extDeriv1_graph_mem`). -/
lemma extDeriv1_graph_mem' (S : SOMin) (hder : S.SharpDeriv) (F : ℕ) :
    ∃ (a : ℕ) (b : Polynomial ℕ), ∀ (D : ℕ) (g : ℝ → ℝ),
      graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2 →
      graphOf (fun x : Fin 1 → ℝ => extDeriv1 g (x 0)) ∈ S.Ω a (b.eval D) 2 := by
  obtain ⟨a, b, h⟩ := Work.WilG4a.extDeriv1_graph_mem S hder F
  refine ⟨a, b, fun D g hg => ?_⟩
  have hset : graphOf (fun x : Fin 1 → ℝ => extDeriv1 g (x 0)) =
      (({z : Fin 2 → ℝ | DifferentiableAt ℝ g (z 0) ∧ z 1 = deriv g (z 0)} ∩
        {z : Fin 2 → ℝ | ContDiffAt ℝ 1 g (z 0)}) ∪
        {z : Fin 2 → ℝ | ¬ ContDiffAt ℝ 1 g (z 0) ∧ z 1 = 0}) := by
    ext z
    have hinit : (Fin.init z) 0 = z 0 := by simp [Fin.init, fin_castSucc_zero_two]
    simp only [graphOf, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff, extDeriv1, hinit]
    by_cases h : ContDiffAt ℝ 1 g (z 0)
    · have hd : DifferentiableAt ℝ g (z 0) := h.differentiableAt_one
      simp [h, hd]
    · simp [h]
  rw [hset]
  exact h D g hg

/-! ## 5. The non-differentiability locus is finite -/

theorem nondiff_locus_finite (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) {F D : ℕ}
    (g : ℝ → ℝ) (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) :
    {x : ℝ | ¬ DifferentiableAt ℝ g x}.Finite := by
  classical
  obtain ⟨a₁, b₁, hD⟩ := diffLocus_mem S F
  have hDloc : liftR {x : ℝ | DifferentiableAt ℝ g x} ∈ S.Ω a₁ (b₁.eval D) 1 := (hD D g hg).1
  have hNmem : liftR {x : ℝ | ¬ DifferentiableAt ℝ g x} ∈ S.Ω (a₁ + 1) (b₁.eval D) 1 := by
    have h := S.compl hDloc
    rw [liftR_compl'] at h
    exact h
  have hno : interior (liftR {x : ℝ | ¬ DifferentiableAt ℝ g x}) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rw [mem_interior_liftR_iff] at hz
    obtain ⟨c, d, hcd', hsub⟩ := exists_Ioo_subset_of_mem_interior hz
    have hcont_fin : {x : ℝ | ¬ ContinuousAt g x}.Finite := cont_off_finite S hcd g hg
    have hex : ∃ x₀ : ℝ, x₀ ∈ Set.Ioo c d ∧ ContinuousAt g x₀ := by
      by_contra hcon
      push_neg at hcon
      have hsub' : Set.Ioo c d ⊆ {x : ℝ | ¬ ContinuousAt g x} := fun x hx => hcon x hx
      exact (Set.Ioo_infinite hcd') (hcont_fin.subset hsub')
    obtain ⟨x₀, hx₀Ioo, hx₀cont⟩ := hex
    have hx₀c : x₀ ∈ Set.Ioo c d := hx₀Ioo
    obtain ⟨η, hη, hηsub⟩ :=
      exists_Ioo_disjoint_finite hcont_fin (by simpa only [Set.mem_ofPred_eq, not_not] using hx₀cont)
    have hmaxlt : max c (x₀ - η) < min d (x₀ + η) := by
      have hmax : max c (x₀ - η) < x₀ := max_lt hx₀c.1 (by linarith [hη])
      have hmin : x₀ ≤ min d (x₀ + η) := le_min hx₀c.2.le (by linarith [hη])
      exact lt_of_lt_of_le hmax hmin
    refine @nondiff_interval_free S F D g hg (max c (x₀ - η)) (min d (x₀ + η)) hmaxlt
      (fun t ht => ?_) (fun t ht => ?_)
    · by_contra htc
      have hS : t ∈ {x : ℝ | ¬ ContinuousAt g x} := by simpa only [Set.mem_ofPred_eq] using htc
      have hI : t ∈ Set.Ioo (x₀ - η) (x₀ + η) :=
        ⟨lt_of_le_of_lt (le_max_right _ _) ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
      exact absurd (show t ∈ Set.Ioo (x₀ - η) (x₀ + η) ∩ {x : ℝ | ¬ ContinuousAt g x}
        from ⟨hI, hS⟩) (by rw [hηsub]; exact Set.notMem_empty t)
    · exact hsub ⟨lt_of_le_of_lt (le_max_left _ _) ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hfinl : (liftR {x : ℝ | ¬ DifferentiableAt ℝ g x}).Finite :=
    Work.WilG1.Calc.finite_of_interior_empty hNmem hno
  exact (finite_liftR_iff _).mp hfinl

/-! ## 6. The `k = 1` case -/

theorem nonC1_locus_finite (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) {F D : ℕ}
    (g : ℝ → ℝ) (hg : graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) :
    {x : ℝ | ¬ ContDiffAt ℝ 1 g x}.Finite := by
  classical
  have hNfin : {x : ℝ | ¬ DifferentiableAt ℝ g x}.Finite :=
    nondiff_locus_finite S hcd hder g hg
  obtain ⟨a, b, hΨmem⟩ := extDeriv_graph_mem' S F
  have hΨfin : {x : ℝ | ¬ ContinuousAt (extDeriv g) x}.Finite :=
    cont_off_finite S hcd (extDeriv g) (hΨmem D g hg)
  refine Set.Finite.subset (hNfin.union hΨfin) ?_
  intro x hx
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  obtain ⟨hxN, hxΨ⟩ := hcon
  have hxnot : x ∉ ({x : ℝ | ¬ DifferentiableAt ℝ g x} ∪
      {x : ℝ | ¬ ContinuousAt (extDeriv g) x}) := by
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hxN hxΨ ⊢
    exact ⟨hxN, hxΨ⟩
  obtain ⟨η, hη, hηsub⟩ := exists_Ioo_disjoint_finite (hNfin.union hΨfin) hxnot
  set I : Set ℝ := Set.Ioo (x - η) (x + η) with hI
  have hIopen : IsOpen I := isOpen_Ioo
  have hIx : x ∈ I := ⟨by linarith, by linarith⟩
  have hdisj : ∀ y ∈ I, DifferentiableAt ℝ g y ∧ ContinuousAt (extDeriv g) y := by
    intro y hy
    have hyout : y ∉ ({x : ℝ | ¬ DifferentiableAt ℝ g x} ∪
        {x : ℝ | ¬ ContinuousAt (extDeriv g) x}) := by
      intro hc
      exact absurd (show y ∈ I ∩ ({x : ℝ | ¬ DifferentiableAt ℝ g x} ∪
        {x : ℝ | ¬ ContinuousAt (extDeriv g) x}) from ⟨hy, hc⟩)
        (by rw [hηsub]; exact Set.notMem_empty y)
    rw [Set.mem_union, not_or] at hyout
    exact ⟨by simpa only [Set.mem_ofPred_eq, not_not] using hyout.1,
      by simpa only [Set.mem_ofPred_eq, not_not] using hyout.2⟩
  have hdiff : DifferentiableOn ℝ g I := fun y hy => (hdisj y hy).1.differentiableWithinAt
  have hcont : ContinuousOn (deriv g) I := by
    intro y hy
    have heq : deriv g =ᶠ[𝓝 y] extDeriv g := by
      filter_upwards [hIopen.mem_nhds hy] with z hz
      simp only [extDeriv, (hdisj z hz).1, if_true]
    exact ((hdisj y hy).2.congr_of_eventuallyEq heq).continuousWithinAt
  have hcdOn : ContDiffOn ℝ 1 g I := by
    rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hIopen]
    exact ⟨hdiff, fun h => absurd h (by simp), by rwa [contDiffOn_zero]⟩
  exact hx (hcdOn.contDiffAt (hIopen.mem_nhds hIx))

/-! ## 7. The induction -/

theorem nonCk_locus_finite (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) :
    ∀ (k : ℕ) (F D : ℕ) (g : ℝ → ℝ),
      graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2 →
      {x : ℝ | ¬ ContDiffAt ℝ k g x}.Finite := by
  classical
  intro k
  induction k with
  | zero =>
      intro F D g hg
      have hfin : {x : ℝ | ¬ ContinuousAt g x}.Finite := cont_off_finite S hcd g hg
      have hcl : closure {x : ℝ | ¬ ContinuousAt g x} = {x : ℝ | ¬ ContinuousAt g x} :=
        hfin.isClosed.closure_eq
      refine hfin.subset ?_
      intro x hx
      rw [← hcl]
      by_contra hcon
      have hopen : IsOpen (closure {x : ℝ | ¬ ContinuousAt g x})ᶜ := isClosed_closure.isOpen_compl
      have hmem : (closure {x : ℝ | ¬ ContinuousAt g x})ᶜ ∈ 𝓝 x := hopen.mem_nhds hcon
      have hcont : ContinuousOn g (closure {x : ℝ | ¬ ContinuousAt g x})ᶜ := by
        intro y hy
        have hyc : ContinuousAt g y := by
          by_contra hyc
          exact hy (subset_closure (by simpa only [Set.mem_ofPred_eq] using hyc))
        exact (hyc.continuousWithinAt).mono (Set.subset_univ _)
      exact hx ((contDiffAt_zero (𝕜 := ℝ) (f := g) (x := x)).mpr ⟨_, hmem, hcont⟩)
  | succ j ih =>
      intro F D g hg
      rcases Nat.eq_zero_or_pos j with hj | hj
      · subst hj
        simpa using nonC1_locus_finite S hcd hder g hg
      · obtain ⟨a, b, hΨmem⟩ := extDeriv1_graph_mem' S hder F
        have hΨg : graphOf (fun x : Fin 1 → ℝ => extDeriv1 g (x 0)) ∈ S.Ω a (b.eval D) 2 :=
          hΨmem D g hg
        have hB1 : {x : ℝ | ¬ ContDiffAt ℝ 1 g x}.Finite :=
          nonC1_locus_finite S hcd hder g hg
        have hBj : {x : ℝ | ¬ ContDiffAt ℝ j (extDeriv1 g) x}.Finite := ih a (b.eval D) _ hΨg
        refine Set.Finite.subset (hB1.union hBj) ?_
        intro x hx
        by_contra hcon
        rw [Set.mem_union, not_or] at hcon
        obtain ⟨hx1, hxj⟩ := hcon
        have hc1 : ContDiffAt ℝ 1 g x := by
          simpa only [Set.mem_ofPred_eq, not_not] using hx1
        have hcj : ContDiffAt ℝ j (extDeriv1 g) x := by
          simpa only [Set.mem_ofPred_eq, not_not] using hxj
        obtain ⟨u, hu, huC⟩ := hcj.contDiffOn le_rfl (fun h => absurd h (by simp))
        obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hu
        obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp (hc1.eventually (by simp))
        set ρ : ℝ := min (ε / 2) (δ / 2) with hρ
        have hρpos : 0 < ρ := lt_min (by linarith) (by linarith)
        set J : Set ℝ := Set.Ioo (x - ρ) (x + ρ) with hJ
        have hJopen : IsOpen J := isOpen_Ioo
        have hJx : x ∈ J := ⟨by linarith, by linarith⟩
        have hJε : J ⊆ Metric.ball x ε := by
          intro y hy
          rw [Set.mem_Ioo] at hy
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          rw [hρ] at hy
          constructor <;> linarith [hy.1, hy.2, min_le_left (ε / 2) (δ / 2)]
        have hJδ : J ⊆ Metric.ball x δ := by
          intro y hy
          rw [Set.mem_Ioo] at hy
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          rw [hρ] at hy
          constructor <;> linarith [hy.1, hy.2, min_le_right (ε / 2) (δ / 2)]
        have hJc1 : ∀ y ∈ J, ContDiffAt ℝ 1 g y := fun y hy => hδsub (hJδ hy)
        have hdiffJ : DifferentiableOn ℝ g J :=
          fun y hy => (hJc1 y hy).differentiableAt_one.differentiableWithinAt
        have hderivCj : ContDiffOn ℝ j (deriv g) J :=
          (huC.mono (fun y hy => hball (hJε hy))).congr (fun y hy => by
            simp only [extDeriv1, hJc1 y hy, if_true])
        have hcdOn : ContDiffOn ℝ ((j : WithTop ℕ∞) + 1) g J := by
          rw [contDiffOn_succ_iff_deriv_of_isOpen (n := (j : ℕ)) hJopen]
          exact ⟨hdiffJ, fun h => absurd h (by simp), hderivCj⟩
        refine hx ?_
        have hthis := hcdOn.contDiffAt (hJopen.mem_nhds hJx)
        simpa only [Nat.cast_add, Nat.cast_one] using hthis

/-! ## 8. The target -/

theorem oneDim_nonCk_finite (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    {F D : ℕ} (g : ℝ → ℝ)
    (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) (k : ℕ) :
    {x : ℝ | ¬ ContDiffAt ℝ k g x}.Finite :=
  nonCk_locus_finite S hcd hder k F D g hg

end Work.WilG4a
