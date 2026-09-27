import Mathlib
import Submission.Work.Drive.Whitney.radialFrameLadder
import Submission.Work.Whitney.CutPush.local_frame

/-!
# A smooth orthonormal frame of a smooth idempotent family on a disk

`Work.Drive.Whitney.diskFrame`: given a smooth family `P : ℝ → ℝ → E →L[ℝ] E` of *idempotents*
(`P a b * P a b = P a b`) of constant rank `k`, there is a radius `R > 0` and a family
`c : (ℝ × ℝ) → Fin k → E` of orthonormal `k`-frames which is `C^∞` on the closed disk
`{x | ‖x‖ ≤ R}` and whose span at `x` is exactly `range (P x.1 x.2)`.

This is the elementary "local step" for the radial ladder of
`Submission/Work/Drive/Whitney/radialFrameLadder.lean`: take an orthonormal `k`-frame `b` of the
range at the origin and read the family `x ↦ (P x.1 x.2) b`; by continuity of `P` this family stays
close to the orthonormal family `b` near the origin, hence stays linearly independent
(`Work.Whitney.CutPush.linearIndependent_of_near_orthonormal`), and Gram–Schmidt normalisation of a
smooth linearly independent family is smooth
(`contDiffOn_gramSchmidtNormed_gen` below), orthonormal, and spans the same subspace — which has
rank `k`, so it is `range (P x.1 x.2)`.

## Contents
* `exists_orthonormal_frame_of_submodule` — an orthonormal `k`-frame of a `k`-dimensional submodule.
* `contDiffOn_gramSchmidt_gen`, `contDiffOn_gramSchmidtNormed_gen` — smoothness of Gram–Schmidt on a
  set, for a family indexed by an arbitrary real normed space.
* `diskFrame` — the target.
-/

open scoped ContDiff

namespace Work.Drive.Whitney

/-! ### An orthonormal frame of a finite-dimensional submodule -/

/-- **An orthonormal `k`-frame of a `k`-dimensional submodule** of a finite-dimensional real inner
product space. -/
theorem exists_orthonormal_frame_of_submodule {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    (k : ℕ) (V : Submodule ℝ E) (hV : Module.finrank ℝ V = k) :
    ∃ b : Fin k → E, Orthonormal ℝ b ∧ Submodule.span ℝ (Set.range b) = V := by
  classical
  have hcard : Module.finrank ℝ V = Fintype.card (Fin k) := by rw [Fintype.card_fin, hV]
  have hvac : Orthonormal ℝ ((∅ : Set (Fin k)).domRestrict (fun _ : Fin k => (0 : V))) :=
    Orthonormal.of_isEmpty _
  obtain ⟨b, -⟩ := Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    (𝕜 := ℝ) (E := V) (ι := Fin k) (v := fun _ : Fin k => (0 : V)) (s := ∅) hcard hvac
  refine ⟨fun i => (b i : E), ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro i j
    simpa using (orthonormal_iff_ite.mp b.orthonormal i j)
  · refine le_antisymm ?_ ?_
    · intro x hx
      refine Submodule.span_le.mpr ?_ hx
      rintro y ⟨i, rfl⟩
      exact (b i).2
    · intro x hx
      have hrepr : x = ∑ i, (b.repr ⟨x, hx⟩).ofLp i • (b i : E) := by
        have h := b.sum_repr (⟨x, hx⟩ : V)
        simpa using congrArg (fun w : V => (w : E)) h.symm
      rw [hrepr]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-! ### Gram–Schmidt smoothness on a set, over an arbitrary real normed domain -/

/-- **Gram–Schmidt smoothness on a set.**  The domain of the family is an arbitrary real normed
space `Z` and the hypothesis is only a *pointwise* linear independence on the set `Z ⊇ W`. -/
theorem contDiffOn_gramSchmidt_gen {k : ℕ} {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (v : Z → Fin k → E) (W : Set Z)
    (hv : ∀ i : Fin k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Z => v z i) W)
    (hli : ∀ z ∈ W, LinearIndependent ℝ (v z)) (n : Fin k) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Z => InnerProductSpace.gramSchmidt ℝ (v z) n) W := by
  have key : ∀ m : ℕ, ∀ hm : m < k,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : Z => InnerProductSpace.gramSchmidt ℝ (v z) ⟨m, hm⟩) W := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have hstep : (fun z : Z => InnerProductSpace.gramSchmidt ℝ (v z) ⟨m, hm⟩)
          = fun z : Z => v z ⟨m, hm⟩ - ∑ i ∈ Finset.Iio (⟨m, hm⟩ : Fin k),
              (inner ℝ (InnerProductSpace.gramSchmidt ℝ (v z) i) (v z ⟨m, hm⟩)
                / (‖InnerProductSpace.gramSchmidt ℝ (v z) i‖ : ℝ) ^ 2)
              • InnerProductSpace.gramSchmidt ℝ (v z) i := by
        funext z
        rw [eq_sub_iff_add_eq]
        exact (InnerProductSpace.gramSchmidt_def'' ℝ (v z) ⟨m, hm⟩).symm
      rw [hstep]
      refine (hv ⟨m, hm⟩).sub ?_
      refine ContDiffOn.sum fun i hi => ?_
      have hi' : (i : ℕ) < m := by
        have h : i < (⟨m, hm⟩ : Fin k) := Finset.mem_Iio.mp hi
        exact h
      have hig : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : Z => InnerProductSpace.gramSchmidt ℝ (v z) i) W :=
        ih (i : ℕ) hi' i.isLt
      have hne : ∀ z ∈ W, InnerProductSpace.gramSchmidt ℝ (v z) i ≠ 0 :=
        fun z hz => InnerProductSpace.gramSchmidt_ne_zero i (hli z hz)
      have hden : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : Z => (‖InnerProductSpace.gramSchmidt ℝ (v z) i‖ : ℝ) ^ 2) W :=
        (ContDiffOn.norm ℝ hig hne).pow 2
      have hnum : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun z : Z => inner ℝ (InnerProductSpace.gramSchmidt ℝ (v z) i) (v z ⟨m, hm⟩)) W :=
        (((isBoundedBilinearMap_inner (𝕜 := ℝ) (E := E)).contDiff.contDiffOn).comp
          (hig.prodMk (hv ⟨m, hm⟩)) (Set.mapsTo_univ _ _))
      have hden_ne : ∀ z ∈ W, (‖InnerProductSpace.gramSchmidt ℝ (v z) i‖ : ℝ) ^ 2 ≠ 0 :=
        fun z hz => pow_ne_zero 2 (by exact_mod_cast norm_ne_zero_iff.mpr (hne z hz))
      exact (hnum.div hden hden_ne).smul hig
  exact key n.val n.isLt

/-- **Normalised Gram–Schmidt smoothness on a set**, over an arbitrary real normed domain. -/
theorem contDiffOn_gramSchmidtNormed_gen {k : ℕ} {Z : Type*} [NormedAddCommGroup Z]
    [NormedSpace ℝ Z]
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E]
    (v : Z → Fin k → E) (W : Set Z)
    (hv : ∀ i : Fin k, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Z => v z i) W)
    (hli : ∀ z ∈ W, LinearIndependent ℝ (v z)) (n : Fin k) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Z => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (v z) n) W := by
  have hgs := contDiffOn_gramSchmidt_gen v W hv hli n
  have hne : ∀ z ∈ W, InnerProductSpace.gramSchmidt ℝ (v z) n ≠ 0 :=
    fun z hz => InnerProductSpace.gramSchmidt_ne_zero n (hli z hz)
  have hnorm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Z => ‖InnerProductSpace.gramSchmidt ℝ (v z) n‖) W :=
    ContDiffOn.norm ℝ hgs hne
  have hinv := hnorm.inv fun z hz => norm_ne_zero_iff.mpr (hne z hz)
  have hfun : (fun z : Z => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (v z) n)
      = fun z : Z => (‖InnerProductSpace.gramSchmidt ℝ (v z) n‖)⁻¹
          • InnerProductSpace.gramSchmidt ℝ (v z) n := by
    funext z
    simp [InnerProductSpace.gramSchmidtNormed]
  rw [hfun]
  exact hinv.smul hgs

/-! ### Idempotents fix their range -/

/-- **An idempotent continuous linear operator fixes every point of its range.** -/
theorem idem_apply_eq_self {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : F →L[ℝ] F) (hf : f * f = f) {z : F} (hz : z ∈ LinearMap.range f.toLinearMap) :
    f z = z := by
  obtain ⟨y, hy⟩ := hz
  have h := congrArg (fun g : F →L[ℝ] F => g y) hf
  rw [mul_apply_eq_comp] at h
  rw [← hy]
  exact h

/-! ### The target -/

/-- **A smooth orthonormal frame of a smooth idempotent family on a disk.**  If
`P : ℝ → ℝ → E →L[ℝ] E` is jointly `C^∞` as a function of `((a,b), y)` and every `P a b` is an
idempotent of rank `k`, then there are `R > 0` and a `C^∞` family `c` of orthonormal `k`-frames on
the closed disk `{x | ‖x‖ ≤ R}` with `span (c x) = range (P x.1 x.2)` for every `x` in the disk. -/
theorem diskFrame {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [FiniteDimensional ℝ E] {k : ℕ}
    (P : ℝ → ℝ → E →L[ℝ] E)
    (hP : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : (ℝ × ℝ) × E => P p.1.1 p.1.2 p.2))
    (hidem : ∀ a b, P a b * P a b = P a b)
    (hrank : ∀ a b, Module.finrank ℝ (LinearMap.range (P a b).toLinearMap) = k) :
    ∃ R : ℝ, 0 < R ∧ ∃ c : (ℝ × ℝ) → Fin k → E,
      (∀ i, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ => c x i)
        {x : ℝ × ℝ | ‖x‖ ≤ R}) ∧
      (∀ x : ℝ × ℝ, ‖x‖ ≤ R → Orthonormal ℝ (c x)) ∧
      (∀ x : ℝ × ℝ, ‖x‖ ≤ R → Submodule.span ℝ (Set.range (c x))
        = LinearMap.range (P x.1 x.2).toLinearMap) := by
  classical
  -- A reference orthonormal `k`-frame of the range at the origin.
  obtain ⟨b, hb_orth, hb_span⟩ :=
    exists_orthonormal_frame_of_submodule k (LinearMap.range (P 0 0).toLinearMap) (hrank 0 0)
  -- The operator-valued family is smooth, hence continuous.
  have hop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ × ℝ => P x.1 x.2) := by
    rw [contDiff_clm_apply_iff]
    intro y
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ × ℝ => ((x, y) : (ℝ × ℝ) × E)) :=
      contDiff_id.prodMk contDiff_const
    exact hP.comp h2
  have hcont0 : ContinuousAt (fun x : ℝ × ℝ => P x.1 x.2) 0 := hop.continuous.continuousAt
  -- The "closeness" constant and radius.
  set ε : ℝ := 1 / ((k : ℝ) + 1) with hεdef
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hεk : ε * (k : ℝ) < 1 := by
    rw [hεdef, div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont0 ε hεpos
  -- The transported family stays close to `b` on the disk of radius `δ`.
  have hclose : ∀ x : ℝ × ℝ, ‖x‖ ≤ δ / 2 → ∀ l : Fin k,
      ‖P x.1 x.2 (b l) - b l‖ ≤ ε := by
    intro x hx l
    have hmem : b l ∈ LinearMap.range (P 0 0).toLinearMap := by
      rw [← hb_span]; exact Submodule.subset_span ⟨l, rfl⟩
    have hb0 : P 0 0 (b l) = b l := idem_apply_eq_self (P 0 0) (hidem 0 0) hmem
    have hxd : dist x (0 : ℝ × ℝ) < δ := by
      rw [dist_zero_right]; linarith
    have hε' : ‖P x.1 x.2 - P 0 0‖ < ε := by
      have h := hδ hxd
      rwa [dist_eq_norm] at h
    calc ‖P x.1 x.2 (b l) - b l‖
        = ‖P x.1 x.2 (b l) - P 0 0 (b l)‖ := by rw [hb0]
      _ = ‖(P x.1 x.2 - P 0 0) (b l)‖ := by rw [sub_apply]
      _ ≤ ‖P x.1 x.2 - P 0 0‖ * ‖b l‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖P x.1 x.2 - P 0 0‖ := by rw [hb_orth.norm_eq_one l, mul_one]
      _ ≤ ε := le_of_lt hε'
  -- Hence the transported family is linearly independent on the disk.
  have hind : ∀ x : ℝ × ℝ, ‖x‖ ≤ δ / 2 → LinearIndependent ℝ (fun l => P x.1 x.2 (b l)) :=
    fun x hx =>
      Work.Whitney.CutPush.linearIndependent_of_near_orthonormal hb_orth hεk (hclose x hx)
  -- The Gram–Schmidt normalisation of the transported family.
  have hsm : ∀ l : Fin k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ × ℝ => P x.1 x.2 (b l)) := by
    intro l
    have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : ℝ × ℝ => ((x, b l) : (ℝ × ℝ) × E)) :=
      contDiff_id.prodMk contDiff_const
    exact hP.comp h2
  refine ⟨δ / 2, by positivity,
    fun x j => InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (fun l => P x.1 x.2 (b l)) j,
    ?_, ?_, ?_⟩
  · intro j
    refine contDiffOn_gramSchmidtNormed_gen (fun x : ℝ × ℝ => fun l => P x.1 x.2 (b l))
      {x : ℝ × ℝ | ‖x‖ ≤ δ / 2} ?_ ?_ j
    · intro l
      exact (hsm l).contDiffOn
    · intro x hx
      exact hind x hx
  · intro x hx
    exact InnerProductSpace.gramSchmidtNormed_orthonormal (hind x hx)
  · intro x hx
    have hspan1 : Submodule.span ℝ (Set.range (fun j : Fin k =>
          InnerProductSpace.gramSchmidtNormed (𝕜 := ℝ) (fun l => P x.1 x.2 (b l)) j))
        = Submodule.span ℝ (Set.range (fun l : Fin k => P x.1 x.2 (b l))) := by
      have hA := InnerProductSpace.span_gramSchmidtNormed (𝕜 := ℝ)
        (fun l : Fin k => P x.1 x.2 (b l)) Set.univ
      have hB := InnerProductSpace.span_gramSchmidt (𝕜 := ℝ) (fun l : Fin k => P x.1 x.2 (b l))
      simp only [Set.image_univ] at hA
      rw [hA, hB]
    rw [hspan1]
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨l, rfl⟩
      exact LinearMap.mem_range.mpr ⟨b l, rfl⟩
    · rw [finrank_span_eq_card (hind x hx), hrank x.1 x.2, Fintype.card_fin]

end Work.Drive.Whitney
