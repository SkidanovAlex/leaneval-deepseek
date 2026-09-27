import Mathlib
import Submission.Work.Drive.exists_forall_good_face_and_notMem_family
import Submission.Work.Drive.avoidLowDim
import Submission.Work.Drive.faceHyp_direction_of_good_family
import Submission.Work.Drive.transHyp_of_good_family
import Submission.Work.Drive.TParity.Basic

/-!
# The genericity assembly of the triple-intersection data

`Work.Drive.exists_meet3Data_of_good_family` is the design-facing assembly of the counting route:
from a *rich* smooth family `G` of triples of `3`-chains in a smooth `4`-manifold (the parametric
Sard hypothesis `hsurj`, together with the uniform chart containment `hcontain`), it produces a
parameter `t` of norm `< ε` such that on a compact set `K` of the nine-box

* every triple point of `G t` in `K` is transversal (`Work.Drive.TripleTransverse`), and
* every boundary triple point of `G t` in `K` lies on *exactly one* face coordinate, of the form
  `bIdx k i`, the other eight coordinates being strictly interior, and the triple intersection
  crosses that face in a common direction `v` of the three chains with `(v k) i ≠ 0`.

This is `TParity.transHyp (G t) ∧ TParity.faceHyp (G t)` restricted to `K` — the complete input of
the counting engine on the compact set the design chooses to contain the perturbed triple locus.

The proof is the cut-off/globalisation of `Work.Drive.transHyp_of_good_family` and
`Work.Drive.faceHyp_direction_of_good_family`, followed by a single application of the *merged*
genericity theorem `Work.Drive.exists_forall_good_face_and_notMem_family` (transversal surjectivity +
face-restricted surjectivity + avoidance of the two-face skeleton, all at one parameter):

* the cut-offs `γ` (parameter) and `β` (space) and the squeeze map `σ` turn the parameter-restricted
  hypotheses into global ones for `Ψ (s, z) = (γ (σ s) * β z) • chartDiff3 p (G (σ s)) z`, which
  equals `chartDiff3 p (G (σ s)) z` for `z ∈ K`;
* the merged theorem is applied with the *two-face pieces* of `K` as the lower-dimensional family
  (`TFid`, `TFdir`, `TFbase`, `TFcov` below: for a pair of coordinates `(i,j)`, `i ≠ j`, the
  direction space `{z | z i = 0 ∧ z j = 0}` has dimension `7 < 8`), so that its avoidance clause
  covers exactly the pairs of face coordinates;
* the avoidance clause gives "at most one face coordinate", the box boundary gives "at least one",
  and the face-restricted surjectivity clause plus `Work.Drive.exists_commonDir_of_faceSurjective`
  gives the crossing direction at that one face;
* the transversal surjectivity clause, transferred to `chartDiff3`, gives `TParity.transHyp` through
  `Work.Drive.TParity.chartDiff3_tan3_surjective_iff`.

The auxiliary lemmas at the top of the file are verbatim copies of the private helpers of the two
files above (they are `private` there, hence not importable). -/

set_option maxHeartbeats 1000000

namespace Work.Drive

open scoped Manifold ContDiff Topology BigOperators
open Manifold Set Metric Filter

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## Auxiliary lemmas

These are the cut-off, reparametrisation and smoothness lemmas of
`Work.Drive.transHyp_of_good_family` / `Work.Drive.faceHyp_direction_of_good_family`. -/

/-- The differentiability order `⊤` is not zero. -/
private lemma top_ne_zero_order : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)

/-- **A smooth function that is `1` on a compact set and supported in an open set containing it.** -/
private lemma exists_cutoff_tsupport_subset {n : ℕ} {K V : Set (EuclideanSpace ℝ (Fin n))}
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

/-- **A smooth bounded map whose derivative is surjective everywhere.** -/
private lemma exists_squeeze_map (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ σ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) σ ∧
      (∀ s, ‖σ s‖ ≤ δ) ∧
      (∀ s, Function.Surjective (fderiv ℝ σ s)) := by
  set c : ℝ := δ / (Real.pi * ((m : ℝ) + 1)) with hc
  have hcpos : 0 < c := by rw [hc]; positivity
  refine ⟨fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i)), ?_, ?_, ?_⟩
  · rw [contDiff_piLp]
    intro i
    exact (contDiff_const.mul
      (Real.contDiff_arctan.comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).contDiff))
  · intro s
    have hb : ∀ i : Fin m,
        ‖(fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i))) s i‖ ^ 2
          ≤ (c * (Real.pi / 2)) ^ 2 := by
      intro i
      have h1 : |Real.arctan (s i)| ≤ Real.pi / 2 :=
        abs_le.mpr ⟨le_of_lt (Real.neg_pi_div_two_lt_arctan _),
          le_of_lt (Real.arctan_lt_pi_div_two _)⟩
      have h2 : |c * Real.arctan (s i)| ≤ c * (Real.pi / 2) := by
        rw [abs_mul, abs_of_nonneg hcpos.le]
        exact mul_le_mul_of_nonneg_left h1 hcpos.le
      have h3 : ‖(fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i))) s i‖ ^ 2
          = (c * Real.arctan (s i)) ^ 2 := by
        simp only [Real.norm_eq_abs]
        rw [sq_abs]
      rw [h3]
      calc (c * Real.arctan (s i)) ^ 2 = |c * Real.arctan (s i)| ^ 2 := by rw [sq_abs]
        _ ≤ (c * (Real.pi / 2)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
    have hsq : ‖(fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i))) s‖ ^ 2 ≤ δ ^ 2 := by
      rw [PiLp.norm_sq_eq_of_L2 (ι := Fin m) (β := fun _ : Fin m => ℝ)]
      calc ∑ i : Fin m, ‖(fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i))) s i‖ ^ 2
          ≤ ∑ _i : Fin m, (c * (Real.pi / 2)) ^ 2 := Finset.sum_le_sum (fun i _ => hb i)
        _ = (m : ℝ) * (c * (Real.pi / 2)) ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ δ ^ 2 := by
              rw [hc]
              have h2 : (0 : ℝ) < Real.pi * ((m : ℝ) + 1) := by positivity
              field_simp
              nlinarith [sq_nonneg ((m : ℝ) + 1), hδ]
    nlinarith [norm_nonneg ((fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i))) s),
      hδ, hsq]
  · intro s
    have hτ : HasFDerivAt
        (fun s' : EuclideanSpace ℝ (Fin m) => fun i : Fin m => c * Real.arctan (s' i))
        (ContinuousLinearMap.pi (fun i : Fin m =>
          (c * (1 + (s i) ^ 2)⁻¹) • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i))) s := by
      rw [hasFDerivAt_pi]
      intro i
      have h := (Real.hasDerivAt_arctan (s i)).comp_hasFDerivAt s
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i).hasFDerivAt
      have h2 : HasFDerivAt (fun s' : EuclideanSpace ℝ (Fin m) => c * Real.arctan (s' i))
          (c • ((1 / (1 + (s i) ^ 2)) • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i))) s :=
        (h.const_smul c).congr_of_eventuallyEq (by
          filter_upwards with x
          rfl)
      rw [smul_smul, one_div] at h2
      exact h2
    have hσ : HasFDerivAt (fun s => WithLp.toLp 2 (fun i => c * Real.arctan (s i)))
        (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm :
          (Fin m → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin m)).comp
          (ContinuousLinearMap.pi fun i : Fin m =>
            (c * (1 + (s i) ^ 2)⁻¹) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i)) s :=
      (PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (fun i : Fin m => c * Real.arctan (s i))).comp s hτ
    rw [hσ.fderiv]
    have hdτsurj : Function.Surjective (ContinuousLinearMap.pi (fun i : Fin m =>
        (c * (1 + (s i) ^ 2)⁻¹) • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) i))) := by
      intro w
      refine ⟨WithLp.toLp 2 (fun i => w i / (c * (1 + (s i) ^ 2)⁻¹)), ?_⟩
      funext i
      simp only [ContinuousLinearMap.pi_apply, smul_apply, PiLp.proj_apply]
      have hne : c * (1 + (s i) ^ 2)⁻¹ ≠ 0 := by
        have h2 : 0 < 1 + (s i) ^ 2 := by positivity
        positivity
      rw [smul_eq_mul]
      field_simp
    intro w
    obtain ⟨u, hu⟩ := hdτsurj w.ofLp
    refine ⟨u, ?_⟩
    rw [ContinuousLinearMap.comp_apply, hu]
    exact WithLp.toLp_ofLp 2 w

/-- If `f` is injective and `f ∘ g` is surjective, then `g` is surjective. -/
private lemma surjective_of_comp_injective {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : F →L[ℝ] G} (hf : Function.Injective f) {g : E →L[ℝ] F}
    (h : Function.Surjective (f.comp g)) : Function.Surjective g := by
  intro w
  obtain ⟨v, hv⟩ := h (f w)
  refine ⟨v, hf ?_⟩
  rw [ContinuousLinearMap.comp_apply] at hv
  exact hv

/-- A point outside the topological support of `f` has a neighbourhood on which `f` vanishes. -/
private lemma eventually_eq_zero_of_notMem_tsupport {X Y : Type*} [TopologicalSpace X] [Zero Y]
    {f : X → Y} {x : X} (h : x ∉ tsupport f) : ∀ᶠ y in 𝓝 x, f y = 0 := by
  have hopen : IsOpen (tsupport f)ᶜ := (isClosed_tsupport f).isOpen_compl
  refine Filter.mem_of_superset (hopen.mem_nhds (by simpa using h)) ?_
  intro y hy
  by_contra hne
  exact hy (subset_tsupport f hne)

/-- **Smoothness of the cut-off charted difference map.** -/
private lemma contDiff_cutoff_chartDiff3 (m : ℕ)
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2))
    (p : M) {γ : EuclideanSpace ℝ (Fin m) → ℝ} (hγ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {β : EuclideanSpace ℝ (Fin 9) → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    {U : Set (EuclideanSpace ℝ (Fin m))} {V : Set (EuclideanSpace ℝ (Fin 9))}
    (hUV : U ×ˢ V ⊆ {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
      ∀ k : Fin 3, G q.1 k (TParity.bPartC k q.2) ∈ (chr p).source})
    (hγsupp : tsupport γ ⊆ U) (hβsupp : tsupport β ⊆ V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        (γ q.1 * β q.2) • TParity.chartDiff3 p (G q.1) q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  by_cases hγ0 : q₀.1 ∈ tsupport γ
  · by_cases hβ0 : q₀.2 ∈ tsupport β
    · have hreg : ∀ k : Fin 3, G q₀.1 k (TParity.bPartC k q₀.2) ∈ (chr p).source :=
        hUV ⟨hγsupp hγ0, hβsupp hβ0⟩
      have hχ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
            TParity.chartDiff3 p (G q.1) q.2) q₀ :=
        contDiffAt_chartDiff3_family_fin m G hG p q₀.1 hreg
      have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) => γ q.1 * β q.2) q₀ :=
        (hγ.contDiffAt.comp q₀ contDiffAt_fst).mul
          (hβ.contDiffAt.comp q₀ contDiffAt_snd)
      exact hg.smul hχ
    · refine (contDiffAt_const (c := (0 : Tgt 8))).congr_of_eventuallyEq ?_
      filter_upwards [(continuous_snd.tendsto q₀).eventually
        (eventually_eq_zero_of_notMem_tsupport hβ0)] with q hq
      rw [hq, mul_zero, zero_smul]
  · refine (contDiffAt_const (c := (0 : Tgt 8))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_fst.tendsto q₀).eventually
      (eventually_eq_zero_of_notMem_tsupport hγ0)] with q hq
    rw [hq, zero_mul, zero_smul]

/-- **Smoothness in the target variable of a single chain of the family.** -/
private lemma contMDiff_fixed_param (m : ℕ)
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2))
    (t : EuclideanSpace ℝ (Fin m)) (k : Fin 3) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (G t k) := by
  have hconst : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : EuclideanSpace ℝ (Fin 3) => (t, (0 : EuclideanSpace ℝ (Fin 3)))) :=
    contMDiff_const
  have hinr : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 3) => ((0 : EuclideanSpace ℝ (Fin m)), y)) :=
    (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 3))).contMDiff
  have hcomp := (hG k).comp (hconst.add hinr)
  simpa only [Function.comp_def, Pi.add_apply, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]
    using hcomp

/-- Transporting face-restricted surjectivity across an equality of the linear maps and of the face
coordinate. -/
private lemma faceSurj_congr {A B : EuclideanSpace ℝ (Fin 9) →L[ℝ] EuclideanSpace ℝ (Fin 8)}
    (hAB : A = B) {j j' : Fin 9} (hj : j = j')
    (h : Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v j = 0} => A v.1)) :
    Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v j' = 0} => B v.1) := by
  cases hAB
  cases hj
  exact h

/-- **The derivative of the cut-off family at a box point.**  At a point `y` of the compact set on
which the space cut-off equals `1` and at a zero of the charted difference map, the derivative of
`z' ↦ (γ s * β z') • chartDiff3 p (G s) z'` is the derivative of `chartDiff3` itself: the
product-rule term involving `β` carries the factor `chartDiff3 p (G s) y = 0`. -/
private lemma fderiv_cutoff_eq (m : ℕ) {s : EuclideanSpace ℝ (Fin m)}
    {y : EuclideanSpace ℝ (Fin 9)}
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2))
    (p : M) {γ : EuclideanSpace ℝ (Fin m) → ℝ} (hγ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγv : γ s = 1)
    {β : EuclideanSpace ℝ (Fin 9) → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    (hβv : β y = 1)
    (hreg : y ∈ TParity.region3 p (G s)) (hzy : TParity.chartDiff3 p (G s) y = 0) :
    fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        (γ s * β z') • TParity.chartDiff3 p (G s) z') y
      = fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G s) z') y := by
  have hχat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G q.1) q.2) (s, y) :=
    contDiffAt_chartDiff3_family_fin m G hG p s hreg
  have hχp : HasFDerivAt (fun z' : EuclideanSpace ℝ (Fin 9) =>
      TParity.chartDiff3 p (G s) z')
      (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G s) z') y) y :=
    (hχat.comp y (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
      top_ne_zero_order |>.hasFDerivAt
  have hγβp : HasFDerivAt (fun z' : EuclideanSpace ℝ (Fin 9) => γ s * β z')
      (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) => γ s * β z') y) y :=
    ((contDiffAt_const.mul hβ.contDiffAt).differentiableAt
      top_ne_zero_order).hasFDerivAt
  have hsmul := hγβp.smul hχp
  have h1 : (γ s * β y) • (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G s) z') y)
      + (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) => γ s * β z') y).smulRight
          (TParity.chartDiff3 p (G s) y)
      = fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G s) z') y := by
    rw [hγv, hβv, one_mul, hzy]
    simp
  rw [h1] at hsmul
  exact hsmul.fderiv

/-! ## The two-face pieces of a compact set of the nine-box

The merged genericity theorem is applied with the *two-face skeleton* of the compact set `K` as the
lower-dimensional family: for a pair of coordinates `(i,j)`, `i ≠ j`, and the two face values, the
piece is `{y ∈ K | y i, y j ∈ {0,1}}`, parametrised by the directions `l` with `y = base + l` in
`K`, where `base` is the point with `0`/`1` in the two coordinates and `0` elsewhere.  The direction
space `{l | l i = 0 ∧ l j = 0}` has dimension `7 < 8`. -/

/-- The index type of the two-face pieces: a pair of coordinates of the nine-box together with the
two face values. -/
abbrev TFid := AvoidLowDim.FaceIdx

/-- The direction space of a two-face piece: for `i ≠ j`, the points whose `i`-th and `j`-th
coordinates vanish; the junk pairs `i = j` carry `⊥`. -/
def TFdir (t : TFid) : Submodule ℝ (Amb 8) :=
  if t.1.1 = t.1.2 then ⊥ else AvoidLowDim.pairDir t.1.1 t.1.2

/-- The base point of a two-face piece. -/
def TFbase (t : TFid) : Amb 8 :=
  AvoidLowDim.faceBase t.1.1 t.1.2 t.2.1 t.2.2

/-- The parameter set of the two-face piece of `K`: the directions `l` with base `+ l` in `K`. -/
def TFcov (K : Set (Amb 8)) (t : TFid) : Set (TFdir t) :=
  {l | TFbase t + (l : Amb 8) ∈ K}

private lemma coordFun_ker_finrank (i : Fin 9) :
    Module.finrank ℝ ((AvoidLowDim.coordFun i).ker) = 8 := by
  have hsurji : Function.Surjective (AvoidLowDim.coordFun i) := by
    intro r
    exact ⟨WithLp.toLp 2 (Pi.single i r), by simp [AvoidLowDim.coordFun_apply]⟩
  have h := LinearMap.finrank_range_add_finrank_ker (AvoidLowDim.coordFun i : Amb 8 →ₗ[ℝ] ℝ)
  rw [LinearMap.range_eq_top.mpr hsurji, finrank_top, Module.finrank_self,
    finrank_euclideanSpace_fin] at h
  omega

private lemma pairDir_finrank_lt {i j : Fin 9} (hij : i ≠ j) :
    Module.finrank ℝ (AvoidLowDim.pairDir i j) < 8 := by
  have hle : AvoidLowDim.pairDir i j ≤ (AvoidLowDim.coordFun i).ker := inf_le_left
  have hzk : (WithLp.toLp 2 (Pi.single j 1) : Amb 8) i = 0 := by
    rw [WithLp.ofLp_toLp, Pi.single_eq_of_ne hij]
  have hzj : (WithLp.toLp 2 (Pi.single j 1) : Amb 8) j = 1 := by
    rw [WithLp.ofLp_toLp, Pi.single_eq_same]
  have hzker : (WithLp.toLp 2 (Pi.single j 1) : Amb 8) ∈ (AvoidLowDim.coordFun i).ker := by
    rw [LinearMap.mem_ker]
    change AvoidLowDim.coordFun i (WithLp.toLp 2 (Pi.single j 1) : Amb 8) = 0
    rw [AvoidLowDim.coordFun_apply]; exact hzk
  have hznot : (WithLp.toLp 2 (Pi.single j 1) : Amb 8) ∉ AvoidLowDim.pairDir i j := by
    rw [AvoidLowDim.mem_pairDir]
    exact fun h => by rw [hzj] at h; exact one_ne_zero h.2
  have hne : AvoidLowDim.pairDir i j ≠ (AvoidLowDim.coordFun i).ker :=
    fun hcon => hznot (by rw [hcon]; exact hzker)
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank ℝ (AvoidLowDim.pairDir i j) ≠
      Module.finrank ℝ ((AvoidLowDim.coordFun i).ker) := by
    intro hcon
    exact hne (Submodule.eq_of_le_of_finrank_eq hle hcon)
  rw [coordFun_ker_finrank i] at h1 h2
  omega

lemma TFdir_finrank_lt (t : TFid) : Module.finrank ℝ (TFdir t) < 8 := by
  by_cases hij : t.1.1 = t.1.2
  · have hbot : TFdir t = ⊥ := by rw [TFdir]; simp [hij]
    rw [hbot]; simp
  · have hpair : TFdir t = AvoidLowDim.pairDir t.1.1 t.1.2 := by rw [TFdir]; simp [hij]
    rw [hpair]; exact pairDir_finrank_lt hij

lemma TFcov_isCompact (K : Set (Amb 8)) (hK : IsCompact K) (t : TFid) :
    IsCompact (TFcov K t) := by
  have hcont : Continuous (fun l : TFdir t => TFbase t + (l : Amb 8)) :=
    continuous_const.add (Submodule.subtypeL (TFdir t)).continuous
  have hclosed : IsClosed (TFcov K t) := hK.isClosed.preimage hcont
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  have hbdd : Bornology.IsBounded (TFcov K t) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C + ‖TFbase t‖, fun l hl => ?_⟩
    have hl' : TFbase t + (l : Amb 8) ∈ K := hl
    calc ‖l‖ = ‖(l : Amb 8)‖ := rfl
      _ = ‖(TFbase t + (l : Amb 8)) - TFbase t‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖TFbase t + (l : Amb 8)‖ + ‖TFbase t‖ := norm_sub_le _ _
      _ ≤ C + ‖TFbase t‖ := by linarith [hC _ hl']
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩

lemma contDiff_TFparam (t : TFid) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun l : TFdir t => TFbase t + (l : Amb 8)) :=
  contDiff_const.add (Submodule.subtypeL (TFdir t)).contDiff

/-- Every point of `K` lying on two (distinct) coordinate faces lies on one of the two-face pieces
of `K`. -/
lemma TFcov_cover (K : Set (Amb 8)) {y : Amb 8} (hy : y ∈ K)
    (h2 : ∃ i j : Fin 9, i ≠ j ∧ (y i = 0 ∨ y i = 1) ∧ (y j = 0 ∨ y j = 1)) :
    ∃ t : TFid, ∃ l : TFdir t, l ∈ TFcov K t ∧ TFbase t + (l : Amb 8) = y := by
  obtain ⟨i, j, hij, hi, hj⟩ := h2
  have hci : AvoidLowDim.faceVal (decide (y i = 1)) = y i := AvoidLowDim.faceVal_decide (y i) hi
  have hcj : AvoidLowDim.faceVal (decide (y j = 1)) = y j := AvoidLowDim.faceVal_decide (y j) hj
  set t : TFid := ((i, j), (decide (y i = 1), decide (y j = 1))) with ht
  have hbase : TFbase t = AvoidLowDim.faceBase i j (decide (y i = 1)) (decide (y j = 1)) := by
    rw [TFbase, ht]
  have hdir : TFdir t = AvoidLowDim.pairDir i j := by rw [TFdir, ht]; simp [hij]
  have hmem : y - TFbase t ∈ TFdir t := by
    rw [hdir, AvoidLowDim.mem_pairDir]
    constructor
    · rw [PiLp.sub_apply, hbase, AvoidLowDim.faceBase_apply_fst, hci, sub_self]
    · rw [PiLp.sub_apply, hbase, AvoidLowDim.faceBase_apply_snd hij.symm, hcj, sub_self]
  refine ⟨t, ⟨y - TFbase t, hmem⟩, ?_, ?_⟩
  · show TFbase t + ((⟨y - TFbase t, hmem⟩ : TFdir t) : Amb 8) ∈ K
    rw [add_sub_cancel]; exact hy
  · show TFbase t + ((⟨y - TFbase t, hmem⟩ : TFdir t) : Amb 8) = y
    rw [add_sub_cancel]

theorem exists_meet3Data_of_good_family (m : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2))
    (p : M) (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε)
    (hcontain : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)),
      ‖t‖ < ε → y ∈ K → ∀ k : Fin 3,
        G t k (Work.Drive.TParity.bPartC k y) ∈ (Work.Drive.chr p).source)
    (hsurj : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)),
      ‖t‖ < ε → y ∈ K → Work.Drive.TParity.chartDiff3 p (G t) y = 0 →
      Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.TParity.chartDiff3 p (G t') y) t)) :
    ∃ t : EuclideanSpace ℝ (Fin m), ‖t‖ < ε ∧
      (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 →
        Work.Drive.TParity.meet3 (G t) y →
        Work.Drive.TripleTransverse (Work.Drive.TParity.md3 (G t) 0 y)
          (Work.Drive.TParity.md3 (G t) 1 y) (Work.Drive.TParity.md3 (G t) 2 y)) ∧
      (∀ y ∈ K, y ∈ Submission.Drive.unitBox 8 →
        Work.Drive.TParity.meet3 (G t) y → y ∈ Submission.Drive.unitBoxBdry 8 →
        ∃ (k : Fin 3) (i : Fin 3),
          (y (Work.Drive.bIdx k i) = 0 ∨ y (Work.Drive.bIdx k i) = 1) ∧
          (∀ j : Fin 3, j ≠ i → y (Work.Drive.bIdx k j) ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ k' : Fin 3, k' ≠ k → ∀ j : Fin 3, y (Work.Drive.bIdx k' j) ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
            Work.Drive.TripleCommonDir (Work.Drive.TParity.md3 (G t) 0 y)
              (Work.Drive.TParity.md3 (G t) 1 y) (Work.Drive.TParity.md3 (G t) 2 y) v ∧
            (v k) i ≠ 0) := by
  classical
  -- ## Step 0: the chart containment region, which is open
  have hcontfam : ∀ k : Fin 3, Continuous
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        G q.1 k (TParity.bPartC k q.2)) := fun k =>
    (hG k).continuous.comp
      (continuous_fst.prodMk ((TParity.bPartC k).continuous.comp continuous_snd))
  set W : Set (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9)) :=
    {q | ∀ k : Fin 3, G q.1 k (TParity.bPartC k q.2) ∈ (chr p).source} with hW
  have hWopen : IsOpen W := by
    have h : W = ⋂ k : Fin 3, {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) |
        G q.1 k (TParity.bPartC k q.2) ∈ (chr p).source} := by
      rw [hW]; ext q; simp
    rw [h]
    exact isOpen_iInter_of_finite fun k => (hcontfam k).isOpen_preimage _ (chr p).open_source
  have hWsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (ε / 4) ×ˢ K ⊆ W := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    refine hcontain t y ?_ hy
    have h := Metric.mem_closedBall.mp ht
    rw [dist_zero_right] at h
    linarith
  -- ## Step 1: the tube lemma separates the parameter and the space variable
  obtain ⟨U, V, hUopen, hVopen, hUsub, hVsub, hUV⟩ :=
    generalized_tube_lemma (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) (ε / 4))
      hK hWopen hWsub
  -- ## Step 2: the cut-off functions
  obtain ⟨γ, hγsmooth, hγone, hγsupp⟩ :=
    exists_cutoff_tsupport_subset (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) (ε / 4))
      (hUopen.inter Metric.isOpen_ball) (fun x hx => ⟨hUsub hx, by
        rw [Metric.mem_ball, dist_zero_right]
        have h := Metric.mem_closedBall.mp hx
        rw [dist_zero_right] at h
        linarith⟩)
  obtain ⟨β, hβsmooth, hβone, hβsupp⟩ := exists_cutoff_tsupport_subset hK hVopen hVsub
  -- ## Step 3: the bounded reparametrisation
  obtain ⟨σ, hσsmooth, hσbound, hσsurj⟩ :=
    exists_squeeze_map (m := m) (δ := ε / 4) (by linarith)
  -- ## Step 4: smoothness of the cut-off family and of its pull-back
  have hΦsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        (γ q.1 * β q.2) • TParity.chartDiff3 p (G q.1) q.2) :=
    contDiff_cutoff_chartDiff3 m G hG p hγsmooth hβsmooth hUV
      (hγsupp.trans Set.inter_subset_left) hβsupp
  have hΨsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        (γ (σ q.1) * β q.2) • TParity.chartDiff3 p (G (σ q.1)) q.2) := by
    have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) => (σ q.1, q.2)) :=
      (hσsmooth.comp contDiff_fst).prodMk contDiff_snd
    simpa only [Function.comp_def] using hΦsmooth.comp hpair
  -- ## Step 5: the parametric-Sard hypothesis of the merged theorem
  have hsurjΨ : ∀ (s : EuclideanSpace ℝ (Fin m)) (z : EuclideanSpace ℝ (Fin 9)), ‖s‖ < ε →
      (z ∈ K ∨ ∃ i : TFid,
        z ∈ (fun l : TFdir i => TFbase i + (l : Amb 8)) '' (TFcov K i)) →
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        (γ (σ q.1) * β q.2) • TParity.chartDiff3 p (G (σ q.1)) q.2) (s, z) = 0 →
      Function.Surjective (fderiv ℝ (fun s' : EuclideanSpace ℝ (Fin m) =>
        (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
          (γ (σ q.1) * β q.2) • TParity.chartDiff3 p (G (σ q.1)) q.2) (s', z)) s) := by
    intro s z _ hzdisj hzero
    have hz : z ∈ K := hzdisj.elim id (fun h => by
      obtain ⟨i, l, hl, hlz⟩ := h
      rw [← hlz]
      exact hl)
    have hσb : ‖σ s‖ ≤ ε / 4 := hσbound s
    have hσlt : ‖σ s‖ < ε := by linarith
    have hγv : γ (σ s) = 1 :=
      hγone (σ s) (by rw [Metric.mem_closedBall, dist_zero_right]; exact hσb)
    have hβv : β z = 1 := hβone z hz
    have hχ0 : TParity.chartDiff3 p (G (σ s)) z = 0 := by
      have h : (γ (σ s) * β z) • TParity.chartDiff3 p (G (σ s)) z = 0 := hzero
      rw [hγv, hβv, one_mul, one_smul] at h
      exact h
    have hreg : ∀ k : Fin 3, G (σ s) k (TParity.bPartC k z) ∈ (chr p).source :=
      hcontain (σ s) z hσlt hz
    have hχat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
          TParity.chartDiff3 p (G q.1) q.2) (σ s, z) :=
      contDiffAt_chartDiff3_family_fin m G hG p (σ s) hreg
    have hχp : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) =>
        TParity.chartDiff3 p (G t') z)
        (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
          TParity.chartDiff3 p (G t') z) (σ s)) (σ s) := by
      have h := (hχat.comp (σ s) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
        top_ne_zero_order
      exact h.hasFDerivAt
    have hγβp : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β z)
        (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β z) (σ s)) (σ s) :=
      ((hγsmooth.contDiffAt.mul contDiffAt_const).differentiableAt
        top_ne_zero_order).hasFDerivAt
    have hsmul : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) =>
        (γ t' * β z) • TParity.chartDiff3 p (G t') z)
        ((γ (σ s) * β z) • (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
            TParity.chartDiff3 p (G t') z) (σ s))
          + (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β z) (σ s)).smulRight
              (TParity.chartDiff3 p (G (σ s)) z)) (σ s) :=
      hγβp.smul hχp
    have hderiv : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) =>
        (γ t' * β z) • TParity.chartDiff3 p (G t') z)
        (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
          TParity.chartDiff3 p (G t') z) (σ s)) (σ s) := by
      have h1 : (γ (σ s) * β z) • (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
            TParity.chartDiff3 p (G t') z) (σ s))
          + (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β z) (σ s)).smulRight
              (TParity.chartDiff3 p (G (σ s)) z)
          = fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
            TParity.chartDiff3 p (G t') z) (σ s) := by
        rw [hγv, hβv, one_mul, hχ0]
        simp
      rw [h1] at hsmul
      exact hsmul
    have hchain : HasFDerivAt (fun s' : EuclideanSpace ℝ (Fin m) =>
        (γ (σ s') * β z) • TParity.chartDiff3 p (G (σ s')) z)
        ((fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
          TParity.chartDiff3 p (G t') z) (σ s)).comp (fderiv ℝ σ s)) s := by
      simpa only [Function.comp_def] using hderiv.comp s
        (((hσsmooth.differentiable (top_ne_zero_order)).differentiableAt).hasFDerivAt)
    rw [hchain.fderiv]
    exact (hsurj (σ s) z hσlt hz hχ0).comp (hσsurj s)
  -- ## Step 6: the merged genericity theorem, with the two-face skeleton of `K`
  obtain ⟨s, -, hsgood, hsface, hsavoid⟩ :=
    exists_forall_good_face_and_notMem_family m 8 K hK TFid
      (fun t : TFid => ↥(TFdir t)) (fun t => TFdir_finrank_lt t)
      (fun t : TFid => fun l : TFdir t => TFbase t + (l : Amb 8))
      (fun t => contDiff_TFparam t)
      (fun t : TFid => TFcov K t) (fun t => TFcov_isCompact K hK t)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        (γ (σ q.1) * β q.2) • TParity.chartDiff3 p (G (σ q.1)) q.2)
      hΨsmooth ε hε hsurjΨ
  -- ## Step 7: transfer the three clauses back to `chartDiff3 p (G (σ s))`
  refine ⟨σ s, by linarith [hσbound s], ?_, ?_⟩
  · -- ### the transversality clause
    intro y hyK hybox hmeet
    have hσlt : ‖σ s‖ < ε := by linarith [hσbound s]
    have hγv : γ (σ s) = 1 :=
      hγone (σ s) (by rw [Metric.mem_closedBall, dist_zero_right]; exact hσbound s)
    have hβv : β y = 1 := hβone y hyK
    have hreg : y ∈ TParity.region3 p (G (σ s)) := hcontain (σ s) y hσlt hyK
    have hzy : TParity.chartDiff3 p (G (σ s)) y = 0 :=
      (TParity.chartDiff3_eq_zero_iff hreg).mpr hmeet
    have hΨ0 : (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        (γ (σ q.1) * β q.2) • TParity.chartDiff3 p (G (σ q.1)) q.2) (s, y) = 0 := by
      show (γ (σ s) * β y) • TParity.chartDiff3 p (G (σ s)) y = 0
      rw [hγv, hβv, one_mul, hzy, smul_zero]
    have hgood : Function.Surjective (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        (γ (σ s) * β z') • TParity.chartDiff3 p (G (σ s)) z') y) :=
      hsgood y hyK hΨ0
    have hfderiv : fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
          (γ (σ s) * β z') • TParity.chartDiff3 p (G (σ s)) z') y
        = fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
          TParity.chartDiff3 p (G (σ s)) z') y :=
      fderiv_cutoff_eq m G hG p hγsmooth hγv hβsmooth hβv hreg hzy
    have hsurj_y : Function.Surjective (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G (σ s)) z') y) := hfderiv ▸ hgood
    have hDt : ∀ k : Fin 3, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (G (σ s) k) := fun k => contMDiff_fixed_param m G hG (σ s) k
    have htan : Function.Surjective (TParity.tan3 p (G (σ s)) y) :=
      surjective_of_comp_injective TParity.chartDiff3_pUpCLM_injective (by
        rw [← (TParity.hasFDerivAt_chartDiff3 p (G (σ s)) hDt hreg).fderiv]
        exact hsurj_y)
    exact (TParity.chartDiff3_tan3_surjective_iff p (G (σ s)) hreg
      ((TParity.chartDiff3_eq_zero_iff hreg).mp hzy)).mp htan
  · -- ### the face clause: exactly one face coordinate, and the crossing direction there
    intro y hyK hybox hmeet hybdry
    have hσlt : ‖σ s‖ < ε := by linarith [hσbound s]
    have hγv : γ (σ s) = 1 :=
      hγone (σ s) (by rw [Metric.mem_closedBall, dist_zero_right]; exact hσbound s)
    have hβv : β y = 1 := hβone y hyK
    have hreg : y ∈ TParity.region3 p (G (σ s)) := hcontain (σ s) y hσlt hyK
    have hzy : TParity.chartDiff3 p (G (σ s)) y = 0 :=
      (TParity.chartDiff3_eq_zero_iff hreg).mpr hmeet
    have hΨ0 : (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        (γ (σ q.1) * β q.2) • TParity.chartDiff3 p (G (σ q.1)) q.2) (s, y) = 0 := by
      show (γ (σ s) * β y) • TParity.chartDiff3 p (G (σ s)) y = 0
      rw [hγv, hβv, one_mul, hzy, smul_zero]
    have hDt : ∀ k : Fin 3, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (G (σ s) k) := fun k => contMDiff_fixed_param m G hG (σ s) k
    have hfderiv : fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
          (γ (σ s) * β z') • TParity.chartDiff3 p (G (σ s)) z') y
        = fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
          TParity.chartDiff3 p (G (σ s)) z') y :=
      fderiv_cutoff_eq m G hG p hγsmooth hγv hβsmooth hβv hreg hzy
    have hsurj_y : Function.Surjective (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G (σ s)) z') y) := by
      have hgood : Function.Surjective (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
          (γ (σ s) * β z') • TParity.chartDiff3 p (G (σ s)) z') y) :=
        hsgood y hyK hΨ0
      exact hfderiv ▸ hgood
    -- ### the avoidance clause: at most one face coordinate
    have hnotwo : ¬ (∃ i j : Fin 9, i ≠ j ∧ (y i = 0 ∨ y i = 1) ∧ (y j = 0 ∨ y j = 1)) := by
      rintro ⟨i, j, hij, hi, hj⟩
      obtain ⟨t', l, hl, hlz⟩ := TFcov_cover K hyK ⟨i, j, hij, hi, hj⟩
      have hne := hsavoid t' l hl
      have hne' : (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
          (γ (σ q.1) * β q.2) • TParity.chartDiff3 p (G (σ q.1)) q.2)
          (s, TFbase t' + (l : Amb 8)) ≠ 0 := hne
      rw [show TFbase t' + (l : Amb 8) = y from hlz] at hne'
      exact hne' hΨ0
    -- ### the box boundary names a face coordinate, and it is the unique one
    obtain ⟨j0, hj0⟩ := hybdry.2
    let k : Fin 3 := ⟨j0.val / 3, by omega⟩
    let i : Fin 3 := ⟨j0.val % 3, by omega⟩
    have hk : bIdx k i = j0 := by
      ext
      rw [bIdx_val]
      show j0.val % 3 + 3 * (j0.val / 3) = j0.val
      exact Nat.mod_add_div j0.val 3
    have hkey : ∀ m : Fin 9, y m ∈ Set.Icc (0 : ℝ) 1 → ¬ (y m = 0 ∨ y m = 1) →
        y m ∈ Set.Ioo (0 : ℝ) 1 := by
      intro m hm hnot
      obtain ⟨h0, h1⟩ := hm
      simp only [not_or] at hnot
      exact ⟨lt_of_le_of_ne h0 (Ne.symm hnot.1), lt_of_le_of_ne h1 hnot.2⟩
    -- the face-restricted surjectivity of the merged theorem, at the (unique) face coordinate
    have hface0 : Function.Surjective (fun v : {v : EuclideanSpace ℝ (Fin 9) // v j0 = 0} =>
        fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
          (γ (σ s) * β z') • TParity.chartDiff3 p (G (σ s)) z') y v.1) :=
      hsface j0 y hyK hΨ0 hj0
    have hface : Function.Surjective (fun w : {w : EuclideanSpace ℝ (Fin 9) //
        w (bIdx k i) = 0} =>
        fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
          TParity.chartDiff3 p (G (σ s)) z') y w.1) :=
      faceSurj_congr hfderiv hk.symm hface0
    obtain ⟨v, hv, hvi⟩ :=
      exists_commonDir_of_faceSurjective p (G (σ s)) hDt hreg hmeet hsurj_y hface
    refine ⟨k, i, ?_, ?_, ?_, v, hv, hvi⟩
    · show y (bIdx k i) = 0 ∨ y (bIdx k i) = 1
      rw [hk]; exact hj0
    · intro j' hj'
      have hne : bIdx k j' ≠ j0 := by
        rw [← hk]
        exact fun h => hj' (bIdx_injective k h)
      have hnot : ¬ (y (bIdx k j') = 0 ∨ y (bIdx k j') = 1) :=
        fun h => hnotwo ⟨bIdx k j', j0, hne, h, hj0⟩
      exact hkey (bIdx k j') (hybox _) hnot
    · intro k' hk' j'
      have hne : bIdx k' j' ≠ j0 := by
        rw [← hk]
        exact bIdx_disjoint hk' j' i
      have hnot : ¬ (y (bIdx k' j') = 0 ∨ y (bIdx k' j') = 1) :=
        fun h => hnotwo ⟨bIdx k' j', j0, hne, h, hj0⟩
      exact hkey (bIdx k' j') (hybox _) hnot

end

end Work.Drive
