import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TParity.ChartDeriv
import Submission.Work.Drive.chartDiff3_surjective_iff_tripleTransverse
import Submission.Work.Drive.exists_forall_good_on_compact_face
import Submission.Work.Drive.contDiffAt_chartDiff3_family_fin

set_option maxHeartbeats 1000000

namespace Work.Drive

open scoped Manifold ContDiff Topology BigOperators
open Manifold Set Metric Filter

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The differentiability order `⊤` is not zero. -/
private lemma top_ne_zero_order : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
  rw [ne_eq, ← WithTop.coe_zero]
  intro h
  exact ENat.top_ne_zero (WithTop.coe_injective h)


/-! ## Auxiliary lemmas -/

/-- **A smooth function that is `1` on a compact set and supported in an open set containing it.**

This is the standard cut-off construction, obtained by gluing finitely many `ContDiffBump`s:
cover `K` by finitely many closed balls whose `2`-balls lie in `V`, and put
`f = 1 - ∏ (1 - bᵢ)`.  The conclusion is stated for the *topological* support, which is what the
smoothness argument needs (it gives that `f` vanishes on a neighbourhood of the complement of `V`). -/
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

/-- **A smooth bounded map whose derivative is surjective everywhere.**

For any `δ > 0` there is a smooth `σ : ℝ^m → ℝ^m` with `‖σ s‖ ≤ δ` for all `s` and
`fderiv σ s` surjective for all `s`: take the coordinatewise `δ`-scaled `arctan`.  This is the
reparametrisation that converts a hypothesis valid only for parameters of norm `< ε` into one valid
for all parameters. -/
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

/-- **Smoothness of the cut-off charted difference map.**  If the three values of `G` lie in the
source of the chart at `p` throughout `U × V`, and `γ`, `β` are smooth functions with topological
supports in `U` and `V`, then `(t,y) ↦ γ t * β y • chartDiff3 p (G t) y` is globally `C^∞` (it is
`chartDiff3` on `supp γ × supp β` and vanishes elsewhere). -/
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
    · refine (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin 8)))).congr_of_eventuallyEq ?_
      filter_upwards [(continuous_snd.tendsto q₀).eventually
        (eventually_eq_zero_of_notMem_tsupport hβ0)] with q hq
      rw [hq, mul_zero, zero_smul]
  · refine (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin 8)))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_fst.tendsto q₀).eventually
      (eventually_eq_zero_of_notMem_tsupport hγ0)] with q hq
    rw [hq, zero_mul, zero_smul]

omit [T2Space M] [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
  ((⊤ : ℕ∞) : WithTop ℕ∞) M] in
/-- **Smoothness in the target variable of a single chain of the family.**  Fixing the family
parameter, each chain is a smooth map `ℝ³ → M`. -/
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

/-- **The engine's transversality hypothesis, produced by parametric Sard instead of by `hc`/`hV`.**

Let `M` be a smooth `4`-manifold (for the counting route: the capping space), let `G : ℝ^m → Fin 3 → ℝ³ → M` be a smooth family of triples of `3`-chains (the perturbation family, centred at the unperturbed configuration `G 0`), let `p : M` be a chart and `K` a compact set of the nine-box `Amb 8 = ℝ⁹`.  Suppose

* the three values stay in the chart source **uniformly** on parameters of norm `< ε` and points of `K` (`hcontain`), and
* at every zero in `K` of the charted difference map `chartDiff3 p (G t)`, the parameter-derivative is surjective for `‖t‖ < ε` (`hsurj`: the perturbation family moves the charted values onto the whole tangent space — the *rich family* condition);

then there are parameters `t` of norm `< ε` at which the charted difference map's zeros in `K` are *transversal*, in the exact form the counting engine consumes:

> `TripleTransverse (md3 (G t) 0 y) (md3 (G t) 1 y) (md3 (G t) 2 y)` at every `y ∈ K` with `chartDiff3 p (G t) y = 0`.

Ingredients (all on disk): the charted difference map `Work.Drive.TParity.chartDiff3` and its derivative (`TParity/ChartDeriv.lean`, in particular `chartDiff3_eq_zero_iff`, `hasFDerivAt_chartDiff3` and the `Amb 8` form of the bridge), the bridge `Work.Drive.chartDiff3_surjective_iff_tripleTransverse` (charted surjectivity **iff** `TripleTransverse` of the intrinsic `md3`s at a coincidence point), and the compact-set parametric-Sard result `Work.Drive.exists_forall_good_on_compact_face`.

Proof route, with the two technical points the reviewers flagged.  (1) *Cut-off and global smoothness*: by `hcontain` and compactness there is a neighbourhood `U ⊇ K` on which, for all `‖t‖ < ε`, the three values are honest; take a smooth cut-off `β` with `β = 1` on `K` and support in `U` (`Work.Drive.TParity.exists_chartDiff3_extension` supplies such truncations pointwise; glue finitely many over `K`) and put `Φ (t, y) := β y • chartDiff3 p (G t) y`.  `Φ` is globally `C^∞` in `(t,y)` (smoothness of `chartDiff3` on `U` from `Work.Drive.contDiffAt_chartDiff3_family_fin` plus a pointwise-`ContDiffAt` argument), and on `K` it equals `chartDiff3`, so its zeros in `K` *and their derivatives* (the product-rule term `chartDiff3 (t,y) • dβ y` vanishes at a zero) coincide with those of `chartDiff3`.  (2) *Parameter range*: `Work.Drive.exists_forall_good_on_compact_face` requires the surjectivity hypothesis for **all** parameters, whereas `hsurj` only provides it for `‖t‖ < ε`; remedy this by reparametrising, e.g. `σ s := (ε/2) • s / (1 + ‖s‖)`, whose derivative is invertible everywhere, so that `t = σ s` ranges over the ball and the surjectivity at `s` follows from `hsurj` at `σ s` composed with the inverse of `dσ s` (and `‖σ s‖ < ε` for all `s`).  Then the Sard result gives `s` with `‖s‖ < ε` (hence `t := σ s` with `‖t‖ < ε`) at which `fderiv_y Φ (t, ·)` is onto at every zero in `K`; transferring back along `K` and applying the bridge (with `chartDiff3_eq_zero_iff` for the coincidence) gives the conclusion.

The conclusion is deliberately restricted to the zeros *in* `K`: that the perturbed triple locus stays inside `K` (equivalently inside one chart region, which `hcontain` also needs) is a separate *open* condition in the parameter, obtained from the tube result `Work.Drive.exists_prod_nhds_subset_of_isCompact`.  With it, the conclusion is exactly `Work.Drive.TParity.transHyp (G t)` on `K`.

Non-vacuous: `hsurj` is satisfiable whenever the family has at least `8` independent directions (for the design: the `3` class directions and the `1` level direction of each of the three chains), and `hcontain` holds for `K` inside one chart region and `ε` small. -/
theorem transHyp_of_good_family (m : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (G : EuclideanSpace ℝ (Fin m) → Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ∀ k : Fin 3, ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 k q.2))
    (p : M) (K : Set (EuclideanSpace ℝ (Fin 9))) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε)
    (hcontain : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)),
      ‖t‖ < ε → y ∈ K → ∀ k : Fin 3,
        G t k (Work.Drive.TParity.bPartC k y) ∈ (Work.Drive.chr p).source)
    (hsurj : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin 9)),
      ‖t‖ < ε → y ∈ K → Work.Drive.TParity.chartDiff3 p (G t) y = 0 →
      Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.TParity.chartDiff3 p (G t') y) t)) :
    ∃ t : EuclideanSpace ℝ (Fin m), ‖t‖ < ε ∧
      ∀ y ∈ K, Work.Drive.TParity.chartDiff3 p (G t) y = 0 →
        Work.Drive.TripleTransverse
          (Work.Drive.TParity.md3 (G t) 0 y)
          (Work.Drive.TParity.md3 (G t) 1 y)
          (Work.Drive.TParity.md3 (G t) 2 y) := by
  classical
  -- ## Step 0: the containment region `W`, which is open
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
  -- ## Step 2: the two cut-off functions
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
  -- ## Step 5: the surjectivity hypothesis of the Sard theorem
  have hsurjΨ : ∀ (s : EuclideanSpace ℝ (Fin m)) (z : EuclideanSpace ℝ (Fin 9)), z ∈ K →
      (γ (σ s) * β z) • TParity.chartDiff3 p (G (σ s)) z = 0 →
      Function.Surjective (fderiv ℝ (fun s' : EuclideanSpace ℝ (Fin m) =>
        (γ (σ s') * β z) • TParity.chartDiff3 p (G (σ s')) z) s) := by
    intro s z hz hzero
    have hσb : ‖σ s‖ ≤ ε / 4 := hσbound s
    have hσlt : ‖σ s‖ < ε := by linarith
    have hγv : γ (σ s) = 1 :=
      hγone (σ s) (by rw [Metric.mem_closedBall, dist_zero_right]; exact hσb)
    have hβv : β z = 1 := hβone z hz
    have hχ0 : TParity.chartDiff3 p (G (σ s)) z = 0 := by
      have h := hzero
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
        (top_ne_zero_order)).hasFDerivAt
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
  -- ## Step 6: parametric Sard
  obtain ⟨s, -, hsgood, -⟩ :=
    exists_forall_good_on_compact_face m 8 K hK 1 (by norm_num)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        (γ (σ q.1) * β q.2) • TParity.chartDiff3 p (G (σ q.1)) q.2)
      hΨsmooth hsurjΨ
  -- ## Step 7: transfer the conclusion back
  refine ⟨σ s, by linarith [hσbound s], ?_⟩
  intro y hyK hzy
  have hσlt : ‖σ s‖ < ε := by linarith [hσbound s]
  have hγv : γ (σ s) = 1 :=
    hγone (σ s) (by rw [Metric.mem_closedBall, dist_zero_right]; exact hσbound s)
  have hβv : β y = 1 := hβone y hyK
  have hΨ0 : (γ (σ s) * β y) • TParity.chartDiff3 p (G (σ s)) y = 0 := by
    rw [hγv, hβv, one_mul, hzy, smul_zero]
  have hgood := hsgood y hyK hΨ0
  have hreg : ∀ k : Fin 3, G (σ s) k (TParity.bPartC k y) ∈ (chr p).source :=
    hcontain (σ s) y hσlt hyK
  have hχat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G q.1) q.2) (σ s, y) :=
    contDiffAt_chartDiff3_family_fin m G hG p (σ s) hreg
  have hχp : HasFDerivAt (fun z' : EuclideanSpace ℝ (Fin 9) =>
      TParity.chartDiff3 p (G (σ s)) z')
      (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G (σ s)) z') y) y :=
    (hχat.comp y (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
      (top_ne_zero_order) |>.hasFDerivAt
  have hγβp : HasFDerivAt (fun z' : EuclideanSpace ℝ (Fin 9) => γ (σ s) * β z')
      (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) => γ (σ s) * β z') y) y :=
    ((contDiffAt_const.mul hβsmooth.contDiffAt).differentiableAt
      (top_ne_zero_order)).hasFDerivAt
  have hsmul := hγβp.smul hχp
  have h1 : (γ (σ s) * β y) • (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G (σ s)) z') y)
      + (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) => γ (σ s) * β z') y).smulRight
          (TParity.chartDiff3 p (G (σ s)) y)
      = fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G (σ s)) z') y := by
    rw [hγv, hβv, one_mul, hzy]
    simp
  rw [h1] at hsmul
  have hfderiv : fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
      (γ (σ s) * β z') • TParity.chartDiff3 p (G (σ s)) z') y
      = fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
        TParity.chartDiff3 p (G (σ s)) z') y := hsmul.fderiv
  have hsurj_y : Function.Surjective (fderiv ℝ (fun z' : EuclideanSpace ℝ (Fin 9) =>
      TParity.chartDiff3 p (G (σ s)) z') y) := hfderiv ▸ hgood
  have hDt : ∀ k : Fin 3, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (G (σ s) k) :=
    fun k => contMDiff_fixed_param m G hG (σ s) k
  have hxreg : (y : EuclideanSpace ℝ (Fin 9)) ∈ TParity.region3 p (G (σ s)) := hreg
  have htan : Function.Surjective (TParity.tan3 p (G (σ s)) y) :=
    surjective_of_comp_injective TParity.chartDiff3_pUpCLM_injective (by
      rw [← (TParity.hasFDerivAt_chartDiff3 p (G (σ s)) hDt hxreg).fderiv]
      exact hsurj_y)
  exact (TParity.chartDiff3_tan3_surjective_iff p (G (σ s)) hxreg
    ((TParity.chartDiff3_eq_zero_iff hxreg).mp hzy)).mp htan

end

end Work.Drive
