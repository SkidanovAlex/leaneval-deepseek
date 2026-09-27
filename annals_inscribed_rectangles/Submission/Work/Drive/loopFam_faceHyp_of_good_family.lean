import Mathlib
import Submission.Work.Drive.ChartBridge
import Submission.Work.Drive.regular_of_transverse
import Submission.Work.Drive.faceHyp_direction_of_good_family
import Submission.Work.Drive.exists_forall_good_face_and_notMem_family
import Submission.Work.Drive.contDiffAt_chartDiff_family_fin
import Submission.Work.Drive.cofactor_restrict_surjective
import Submission.Work.Drive.cofactorVec_mem_ker

/-!
# The face hypothesis of the loop family from a good family

`Work.Drive.loopFam_faceHyp_of_good_family` is the 2-chain (`ℝ²`-curve versus `ℝ³`-curve) analogue
of the genericity assembly `Work.Drive.exists_meet3Data_of_good_family`: from a *rich* smooth family
`G` of `3`-chains in a smooth `4`-manifold (the parametric-Sard hypothesis `hsurj`, together with the
uniform chart containment `hcontain` around a fixed smooth `2`-chain `D`), it produces a parameter
`t` of norm `< ε` such that, on a compact set `K` of the five-box, at every intersection point
`D (sqPart y) = G t (cbPart y)` lying in the unit box:

* at most one coordinate of `y` is on a face of the box (no pair of coordinates in `{0,1}`), and
* if a coordinate `i` is on the face, then the two derivatives `mfderiv D` and `mfderiv (G t)` have a
  common direction whose `i`-th coordinate does not vanish — i.e. the intersection crosses the face
  transversally.

The proof is the cut-off/globalisation pattern of `Work.Drive.transHyp_of_good_family` and
`Work.Drive.faceHyp_direction_of_good_family`, followed by a single application of the *merged*
genericity theorem `Work.Drive.exists_forall_good_face_and_notMem_family` (transversal surjectivity +
face-restricted surjectivity + avoidance of the two-face skeleton, all at one parameter); the
avoidance of the two-face skeleton is expressed through the affine pieces `Fbase4 t + l` of `K`
whose direction space `Fdir4 t = {l | l i = 0 ∧ l j = 0}` has dimension `3 < 4`.
-/

namespace Work.Drive

open scoped Manifold ContDiff Topology
open Manifold Set Metric Filter

set_option maxHeartbeats 1000000

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
    ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## Auxiliary lemmas

These are the cut-off, reparametrisation and composition lemmas of
`Work.Drive.transHyp_of_good_family` / `Work.Drive.faceHyp_direction_of_good_family` (private
there, hence copied here). -/

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

/-- The two block projections are inverse to `mkPart`. -/
private lemma mkPart_sqPart_cbPart (x : Work.Drive.Amb 4) :
    Work.Drive.mkPart (Work.Drive.sqPart x) (Work.Drive.cbPart x) = x := by
  ext i
  revert i
  refine Fin.addCases (m := 2) (n := 3)
    (motive := fun i => Work.Drive.mkPart (Work.Drive.sqPart x) (Work.Drive.cbPart x) i = x i) ?_ ?_
  · intro i
    simp [Work.Drive.mkPart, Work.Drive.sqPart, Work.Drive.sqIdx, Fin.addCases_left]
  · intro j
    simp [Work.Drive.mkPart, Work.Drive.cbPart, Work.Drive.cbIdx, Fin.addCases_right]

/-! ## The two-face pieces of a compact set of the five-box

The merged genericity theorem is applied with the *two-face skeleton* of the compact set `K` as the
lower-dimensional family: for a pair of coordinates `(i,j)`, `i ≠ j`, and the two face values, the
piece is `{y ∈ K | y i, y j ∈ {0,1}}`, parametrised by the directions `l` with `y = base + l` in
`K`, where `base` is the point with `0`/`1` in the two coordinates and `0` elsewhere.  The direction
space `{l | l i = 0 ∧ l j = 0}` has dimension `3 < 4`. -/

/-- The `i`-th coordinate functional on the five-box. -/
def coordFun4 (i : Fin 5) : Amb 4 →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 5 => ℝ) i

lemma coordFun4_apply (i : Fin 5) (x : Amb 4) : coordFun4 i x = x i := by
  simp [coordFun4, PiLp.proj_apply]

/-- The direction space of the pair of coordinates `(i,j)`: the points whose `i`-th and `j`-th
coordinates vanish.  This is the `3`-dimensional piece underlying the two-face set of `(i,j)`. -/
def pairDir4 (i j : Fin 5) : Submodule ℝ (Amb 4) := (coordFun4 i).ker ⊓ (coordFun4 j).ker

lemma mem_pairDir4 {i j : Fin 5} {z : Amb 4} : z ∈ pairDir4 i j ↔ z i = 0 ∧ z j = 0 := by
  simp [pairDir4, coordFun4_apply]

/-- The base point of the face pair `(i,j)` with face values `b₁`, `b₂`. -/
def faceBase4 (i j : Fin 5) (b₁ b₂ : Bool) : Amb 4 :=
  WithLp.toLp 2
    (fun k : Fin 5 => if k = i then AvoidLowDim.faceVal b₁
      else if k = j then AvoidLowDim.faceVal b₂ else 0)

lemma faceBase4_apply_fst (i j : Fin 5) (b₁ b₂ : Bool) :
    faceBase4 i j b₁ b₂ i = AvoidLowDim.faceVal b₁ := by
  simp [faceBase4, WithLp.ofLp_toLp]

lemma faceBase4_apply_snd {i j : Fin 5} (h : j ≠ i) (b₁ b₂ : Bool) :
    faceBase4 i j b₁ b₂ j = AvoidLowDim.faceVal b₂ := by
  simp [faceBase4, WithLp.ofLp_toLp, h]

/-- The index type of the two-face pieces: a pair of *distinct* coordinates of the five-box together
with the two face values. -/
abbrev FaceIdx4 := {p : Fin 5 × Fin 5 // p.1 ≠ p.2} × Bool × Bool

/-- The direction space of a two-face piece. -/
def Fdir4 (t : FaceIdx4) : Submodule ℝ (Amb 4) := pairDir4 t.1.1.1 t.1.1.2

/-- The base point of a two-face piece. -/
def Fbase4 (t : FaceIdx4) : Amb 4 := faceBase4 t.1.1.1 t.1.1.2 t.2.1 t.2.2

/-- The parameter set of the two-face piece of `K`: the directions `l` with base `+ l` in `K`. -/
def Fcov4 (K : Set (Amb 4)) (t : FaceIdx4) : Set (Fdir4 t) :=
  {l | Fbase4 t + (l : Amb 4) ∈ K}

private lemma coordFun4_ker_finrank (i : Fin 5) :
    Module.finrank ℝ ((coordFun4 i).ker) = 4 := by
  have hsurji : Function.Surjective (coordFun4 i) := by
    intro r
    exact ⟨WithLp.toLp 2 (Pi.single i r), by simp [coordFun4_apply]⟩
  have h := LinearMap.finrank_range_add_finrank_ker (coordFun4 i : Amb 4 →ₗ[ℝ] ℝ)
  rw [LinearMap.range_eq_top.mpr hsurji, finrank_top, Module.finrank_self,
    finrank_euclideanSpace_fin] at h
  omega

private lemma pairDir4_finrank_lt {i j : Fin 5} (hij : i ≠ j) :
    Module.finrank ℝ (pairDir4 i j) < 4 := by
  have hle : pairDir4 i j ≤ (coordFun4 i).ker := inf_le_left
  set e : Amb 4 := WithLp.toLp 2 (fun k : Fin 5 => if k = j then (1 : ℝ) else 0) with he
  have hei : e i = 0 := by rw [he]; simp [hij]
  have hej : e j = 1 := by rw [he]; simp
  have hzker : e ∈ (coordFun4 i).ker := by
    rw [LinearMap.mem_ker]
    change coordFun4 i e = 0
    rw [coordFun4_apply]; exact hei
  have hznot : e ∉ pairDir4 i j := by
    rw [mem_pairDir4]
    exact fun h => by rw [hej] at h; exact one_ne_zero h.2
  have hne : pairDir4 i j ≠ (coordFun4 i).ker :=
    fun hcon => hznot (by rw [hcon]; exact hzker)
  have h1 := Submodule.finrank_mono hle
  have h2 : Module.finrank ℝ (pairDir4 i j) ≠
      Module.finrank ℝ ((coordFun4 i).ker) := by
    intro hcon
    exact hne (Submodule.eq_of_le_of_finrank_eq hle hcon)
  rw [coordFun4_ker_finrank i] at h1 h2
  omega

lemma Fdir4_finrank_lt (t : FaceIdx4) : Module.finrank ℝ (Fdir4 t) < 4 :=
  pairDir4_finrank_lt t.1.2

lemma Fcov4_isCompact (K : Set (Amb 4)) (hK : IsCompact K) (t : FaceIdx4) :
    IsCompact (Fcov4 K t) := by
  have hcont : Continuous (fun l : Fdir4 t => Fbase4 t + (l : Amb 4)) :=
    continuous_const.add (Submodule.subtypeL (Fdir4 t)).continuous
  have hclosed : IsClosed (Fcov4 K t) := hK.isClosed.preimage hcont
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
  have hbdd : Bornology.IsBounded (Fcov4 K t) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨C + ‖Fbase4 t‖, fun l hl => ?_⟩
    have hl' : Fbase4 t + (l : Amb 4) ∈ K := hl
    calc ‖l‖ = ‖(l : Amb 4)‖ := rfl
      _ = ‖(Fbase4 t + (l : Amb 4)) - Fbase4 t‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖Fbase4 t + (l : Amb 4)‖ + ‖Fbase4 t‖ := norm_sub_le _ _
      _ ≤ C + ‖Fbase4 t‖ := by linarith [hC _ hl']
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbdd⟩

lemma contDiff_Fparam4 (t : FaceIdx4) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun l : Fdir4 t => Fbase4 t + (l : Amb 4)) :=
  contDiff_const.add (Submodule.subtypeL (Fdir4 t)).contDiff

/-- Every point of `K` lying on two (distinct) coordinate faces lies on one of the two-face pieces
of `K`. -/
lemma Fcov4_cover (K : Set (Amb 4)) {y : Amb 4} (hy : y ∈ K)
    (h2 : ∃ i j : Fin 5, i ≠ j ∧ (y i = 0 ∨ y i = 1) ∧ (y j = 0 ∨ y j = 1)) :
    ∃ t : FaceIdx4, ∃ l : Fdir4 t, l ∈ Fcov4 K t ∧ Fbase4 t + (l : Amb 4) = y := by
  obtain ⟨i, j, hij, hi, hj⟩ := h2
  have hci : AvoidLowDim.faceVal (decide (y i = 1)) = y i := AvoidLowDim.faceVal_decide (y i) hi
  have hcj : AvoidLowDim.faceVal (decide (y j = 1)) = y j := AvoidLowDim.faceVal_decide (y j) hj
  set t : FaceIdx4 := (⟨(i, j), hij⟩, (decide (y i = 1), decide (y j = 1))) with ht
  have hbase : Fbase4 t = faceBase4 i j (decide (y i = 1)) (decide (y j = 1)) := by
    rw [Fbase4, ht]
  have hdir : Fdir4 t = pairDir4 i j := by rw [Fdir4, ht]
  have hmem : y - Fbase4 t ∈ Fdir4 t := by
    rw [hdir, mem_pairDir4]
    constructor
    · rw [PiLp.sub_apply, hbase, faceBase4_apply_fst, hci, sub_self]
    · rw [PiLp.sub_apply, hbase, faceBase4_apply_snd hij.symm, hcj, sub_self]
  refine ⟨t, ⟨y - Fbase4 t, hmem⟩, ?_, ?_⟩
  · show Fbase4 t + ((⟨y - Fbase4 t, hmem⟩ : Fdir4 t) : Amb 4) ∈ K
    rw [add_sub_cancel]; exact hy
  · show Fbase4 t + ((⟨y - Fbase4 t, hmem⟩ : Fdir4 t) : Amb 4) = y
    rw [add_sub_cancel]

/-- Smoothness in the target variable of the single chain `G t` of the family. -/
private lemma contMDiff_fixed_param_loop (m : ℕ)
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 q.2))
    (t : EuclideanSpace ℝ (Fin m)) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (G t) := by
  have hconst : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun _ : EuclideanSpace ℝ (Fin 3) => (t, (0 : EuclideanSpace ℝ (Fin 3)))) :=
    contMDiff_const
  have hinr : ContMDiff (𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y : EuclideanSpace ℝ (Fin 3) => ((0 : EuclideanSpace ℝ (Fin m)), y)) :=
    (ContinuousLinearMap.inr ℝ (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin 3))).contMDiff
  have hcomp := hG.comp (hconst.add hinr)
  simpa only [Function.comp_def, Pi.add_apply, Prod.mk_add_mk, add_zero, zero_add, Prod.mk.eta]
    using hcomp


/-- The "square" block projection is continuous. -/
private lemma continuous_sqPart : Continuous (sqPart : Amb 4 → EuclideanSpace ℝ (Fin 2)) := by
  rw [show (sqPart : Amb 4 → EuclideanSpace ℝ (Fin 2)) = ⇑sqPartCLM from
    funext sqPartCLM_eq_sqPart]
  exact sqPartCLM.continuous

/-- The "cube" block projection is continuous. -/
private lemma continuous_cbPart : Continuous (cbPart : Amb 4 → EuclideanSpace ℝ (Fin 3)) := by
  rw [show (cbPart : Amb 4 → EuclideanSpace ℝ (Fin 3)) = ⇑cbPartCLM from
    funext cbPartCLM_eq_cbPart]
  exact cbPartCLM.continuous

/-! ## The cut-off and face-criterion lemmas for the loop family

These are the `2`-chain analogues of the private helpers of
`Work.Drive.exists_meet3Data_of_good_family` (cut-off globalisation and the derivative of the
cut-off family at a zero) and of `Work.Drive.exists_commonDir_of_faceSurjective` (the converse of the
face criterion), proved here directly. -/

private theorem contDiff_cutoff_chartDiff_loop (m : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : EuclideanSpace ℝ (Fin 2) → M)
    (hD : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 q.2))
    (p : M) {γ : EuclideanSpace ℝ (Fin m) → ℝ} (hγ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {β : Work.Drive.Amb 4 → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    {U : Set (EuclideanSpace ℝ (Fin m))} {V : Set (Work.Drive.Amb 4)}
    (hUV : U ×ˢ V ⊆ {q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 |
      D (Work.Drive.sqPart q.2) ∈ (Work.Drive.chr p).source ∧
      G q.1 (Work.Drive.cbPart q.2) ∈ (Work.Drive.chr p).source})
    (hγsupp : tsupport γ ⊆ U) (hβsupp : tsupport β ⊆ V) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 =>
        (γ q.1 * β q.2) • Work.Drive.chartDiff p D (G q.1) q.2) := by
  rw [contDiff_iff_contDiffAt]
  intro q₀
  by_cases hγ0 : q₀.1 ∈ tsupport γ
  · by_cases hβ0 : q₀.2 ∈ tsupport β
    · have hreg : D (Work.Drive.sqPart q₀.2) ∈ (Work.Drive.chr p).source ∧
          G q₀.1 (Work.Drive.cbPart q₀.2) ∈ (Work.Drive.chr p).source :=
        hUV ⟨hγsupp hγ0, hβsupp hβ0⟩
      have hχ : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 =>
            Work.Drive.chartDiff p D (G q.1) q.2) q₀ :=
        contDiffAt_chartDiff_family_fin m D hD G hG p q₀.1 hreg
      have hg : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 => γ q.1 * β q.2) q₀ :=
        (hγ.contDiffAt.comp q₀ contDiffAt_fst).mul
          (hβ.contDiffAt.comp q₀ contDiffAt_snd)
      exact hg.smul hχ
    · refine (contDiffAt_const (c := (0 : Work.Drive.Tgt 4))).congr_of_eventuallyEq ?_
      filter_upwards [(continuous_snd.tendsto q₀).eventually
        (eventually_eq_zero_of_notMem_tsupport hβ0)] with q hq
      rw [hq, mul_zero, zero_smul]
  · refine (contDiffAt_const (c := (0 : Work.Drive.Tgt 4))).congr_of_eventuallyEq ?_
    filter_upwards [(continuous_fst.tendsto q₀).eventually
      (eventually_eq_zero_of_notMem_tsupport hγ0)] with q hq
    rw [hq, zero_mul, zero_smul]

private theorem fderiv_cutoff_chartDiff_eq_loop (m : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : EuclideanSpace ℝ (Fin 2) → M)
    (hD : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 q.2))
    (p : M) {s : EuclideanSpace ℝ (Fin m)} {γ : EuclideanSpace ℝ (Fin m) → ℝ}
    (hγ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (hγv : γ s = 1)
    {β : Work.Drive.Amb 4 → ℝ} (hβ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) β)
    {y : Work.Drive.Amb 4} (hβv : β y = 1)
    (hcont : y ∈ Work.Drive.chartRegion p D (G s)) (hzy : Work.Drive.chartDiff p D (G s) y = 0) :
    fderiv ℝ (fun z' : Work.Drive.Amb 4 =>
        (γ s * β z') • Work.Drive.chartDiff p D (G s) z') y
      = fderiv ℝ (fun z' : Work.Drive.Amb 4 => Work.Drive.chartDiff p D (G s) z') y := by
  have hχat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 =>
        Work.Drive.chartDiff p D (G q.1) q.2) (s, y) :=
    contDiffAt_chartDiff_family_fin m D hD G hG p s hcont
  have hχp : HasFDerivAt (fun z' : Work.Drive.Amb 4 =>
      Work.Drive.chartDiff p D (G s) z')
      (fderiv ℝ (fun z' : Work.Drive.Amb 4 =>
        Work.Drive.chartDiff p D (G s) z') y) y :=
    (hχat.comp y (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt
      top_ne_zero_order |>.hasFDerivAt
  have hγβp : HasFDerivAt (fun z' : Work.Drive.Amb 4 => γ s * β z')
      (fderiv ℝ (fun z' : Work.Drive.Amb 4 => γ s * β z') y) y :=
    ((contDiffAt_const.mul hβ.contDiffAt).differentiableAt
      top_ne_zero_order).hasFDerivAt
  have hsmul := hγβp.smul hχp
  have h1 : (γ s * β y) • (fderiv ℝ (fun z' : Work.Drive.Amb 4 =>
        Work.Drive.chartDiff p D (G s) z') y)
      + (fderiv ℝ (fun z' : Work.Drive.Amb 4 => γ s * β z') y).smulRight
          (Work.Drive.chartDiff p D (G s) y)
      = fderiv ℝ (fun z' : Work.Drive.Amb 4 =>
        Work.Drive.chartDiff p D (G s) z') y := by
    rw [hγv, hβv, one_mul, hzy]
    simp
  rw [h1] at hsmul
  exact hsmul.fderiv

private theorem exists_sigma_tau_of_faceSurjective_loop {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (p : M) (D : EuclideanSpace ℝ (Fin 2) → M) (N : EuclideanSpace ℝ (Fin 3) → M)
    (hD : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (hN : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) N)
    {y : Work.Drive.Amb 4} (hy : y ∈ Work.Drive.chartRegion p D N)
    (heq : D (Work.Drive.sqPart y) = N (Work.Drive.cbPart y))
    {i : Fin 5}
    (hsurj : Function.Surjective (fderiv ℝ (Work.Drive.chartDiff p D N) y))
    (hface : Function.Surjective (fun v : {v : Work.Drive.Amb 4 // v i = 0} =>
      fderiv ℝ (Work.Drive.chartDiff p D N) y v.1)) :
    ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
      mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) D (Work.Drive.sqPart y) σ
        = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
            (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) N (Work.Drive.cbPart y) τ ∧
      Work.Drive.mkPart σ τ i ≠ 0 := by
  set T : Work.Drive.Amb 4 →L[ℝ] Work.Drive.Tgt 4 :=
    fderiv ℝ (Work.Drive.chartDiff p D N) y with hT
  have hcof : Work.Drive.cofactorVec T i ≠ 0 :=
    (Work.Drive.surjective_domRestrict_iff_cofactorVec_ne_zero T hsurj i).mp hface
  have hker : T (Work.Drive.cofactorVec T) = 0 := Work.Drive.cofactorVec_mem_ker T
  refine ⟨Work.Drive.sqPart (Work.Drive.cofactorVec T),
    Work.Drive.cbPart (Work.Drive.cofactorVec T), ?_, ?_⟩
  · have hmk : Work.Drive.mkPart (Work.Drive.sqPart (Work.Drive.cofactorVec T))
        (Work.Drive.cbPart (Work.Drive.cofactorVec T)) = Work.Drive.cofactorVec T :=
      mkPart_sqPart_cbPart _
    have hf := Work.Drive.chartDiff_fderiv_mkPart p D N hD hN hy
      (Work.Drive.sqPart (Work.Drive.cofactorVec T))
      (Work.Drive.cbPart (Work.Drive.cofactorVec T))
    have hAB : tangentCoordChange (𝓡 4) (D (Work.Drive.sqPart y)) p
          (D (Work.Drive.sqPart y))
          (mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart y) (Work.Drive.sqPart (Work.Drive.cofactorVec T)))
        - tangentCoordChange (𝓡 4) (N (Work.Drive.cbPart y)) p
          (N (Work.Drive.cbPart y))
          (mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart y)
            (Work.Drive.cbPart (Work.Drive.cofactorVec T))) = 0 := by
      rw [← hf, hmk, ← hT]
      exact hker
    have htceq : tangentCoordChange (𝓡 4) (D (Work.Drive.sqPart y)) p
          (D (Work.Drive.sqPart y))
        = tangentCoordChange (𝓡 4) (N (Work.Drive.cbPart y)) p
          (N (Work.Drive.cbPart y)) := by
      rw [← heq]
    have hsrc1 : D (Work.Drive.sqPart y) ∈
        (extChartAt (𝓡 4) (D (Work.Drive.sqPart y))).source :=
      mem_extChartAt_source (I := 𝓡 4) (D (Work.Drive.sqPart y))
    have hsrc2 : D (Work.Drive.sqPart y) ∈ (extChartAt (𝓡 4) p).source := by
      rw [extChartAt_source]
      exact hy.1
    have hinj : Function.Injective (tangentCoordChange (𝓡 4)
        (D (Work.Drive.sqPart y)) p (D (Work.Drive.sqPart y))) :=
      tangentCoordChange_injective ⟨hsrc1, hsrc2⟩
    have h3 : tangentCoordChange (𝓡 4) (D (Work.Drive.sqPart y)) p
          (D (Work.Drive.sqPart y))
          (mfderiv (𝓡 2) (𝓡 4) D (Work.Drive.sqPart y)
            (Work.Drive.sqPart (Work.Drive.cofactorVec T)))
        = tangentCoordChange (𝓡 4) (D (Work.Drive.sqPart y)) p
          (D (Work.Drive.sqPart y))
          (mfderiv (𝓡 3) (𝓡 4) N (Work.Drive.cbPart y)
            (Work.Drive.cbPart (Work.Drive.cofactorVec T))) := by
      have h := sub_eq_zero.mp hAB
      rw [← htceq] at h
      exact h
    exact hinj h3
  · rw [mkPart_sqPart_cbPart]
    exact hcof

/-! ## The main theorem -/

/-- **The face hypothesis of the loop family from a good family.**  See the module docstring. -/
theorem loopFam_faceHyp_of_good_family (m : ℕ) {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : EuclideanSpace ℝ (Fin 2) → M)
    (hD : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) D)
    (G : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 3) → M)
    (hG : ContMDiff
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin 3) => G q.1 q.2))
    (p : M) (K : Set (Work.Drive.Amb 4)) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε)
    (hcontain : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : Work.Drive.Amb 4), ‖t‖ < ε → y ∈ K →
      G t (Work.Drive.cbPart y) ∈ (Work.Drive.chr p).source ∧
      D (Work.Drive.sqPart y) ∈ (Work.Drive.chr p).source)
    (hsurj : ∀ (t : EuclideanSpace ℝ (Fin m)) (y : Work.Drive.Amb 4), ‖t‖ < ε → y ∈ K →
      Work.Drive.chartDiff p D (G t) y = 0 →
      Function.Surjective (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.chartDiff p D (G t') y) t)) :
    ∃ t : EuclideanSpace ℝ (Fin m), ‖t‖ < ε ∧
      (∀ y : Work.Drive.Amb 4, y ∈ K → D (Work.Drive.sqPart y) = G t (Work.Drive.cbPart y) →
        y ∈ Submission.Drive.unitBox 4 →
        ¬ (∃ i j : Fin 5, i ≠ j ∧ (y i = 0 ∨ y i = 1) ∧ (y j = 0 ∨ y j = 1))) ∧
      (∀ y : Work.Drive.Amb 4, y ∈ K → D (Work.Drive.sqPart y) = G t (Work.Drive.cbPart y) →
        y ∈ Submission.Drive.unitBox 4 → ∀ i : Fin 5, (y i = 0 ∨ y i = 1) →
        (∀ j : Fin 5, j ≠ i → y j ∈ Set.Ioo (0 : ℝ) 1) →
        ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
          mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
              (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) D (Work.Drive.sqPart y) σ
            = mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
                (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) (G t)
                (Work.Drive.cbPart y) τ ∧
          Work.Drive.mkPart σ τ i ≠ 0) := by
  classical
  -- ## Step 0: the chart containment region of the family is open and contains `ball 0 (ε/4) × K`
  have hcontcb : Continuous (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 =>
      G q.1 (Work.Drive.cbPart q.2)) :=
    hG.continuous.comp
      (continuous_fst.prodMk (continuous_cbPart.comp continuous_snd))
  have hcontsq : Continuous (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 =>
      D (Work.Drive.sqPart q.2)) :=
    hD.continuous.comp (continuous_sqPart.comp continuous_snd)
  set W : Set (EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4) :=
    {q | D (Work.Drive.sqPart q.2) ∈ (Work.Drive.chr p).source ∧
      G q.1 (Work.Drive.cbPart q.2) ∈ (Work.Drive.chr p).source} with hW
  have hWopen : IsOpen W :=
    (hcontsq.isOpen_preimage _ (Work.Drive.chr p).open_source).inter
      (hcontcb.isOpen_preimage _ (Work.Drive.chr p).open_source)
  have hWsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) (ε / 4) ×ˢ K ⊆ W := by
    rintro ⟨t, y⟩ ⟨ht, hy⟩
    have ht' : ‖t‖ < ε := by
      have h := Metric.mem_closedBall.mp ht
      rw [dist_zero_right] at h
      linarith
    exact ⟨(hcontain t y ht' hy).2, (hcontain t y ht' hy).1⟩
  -- ## Step 1: the tube lemma separates the parameter and the space variable
  obtain ⟨U, V, hUopen, hVopen, hUsub, hVsub, hUV⟩ :=
    generalized_tube_lemma (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin m)) (ε / 4)) hK
      hWopen hWsub
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
  obtain ⟨sq, hsqsmooth, hsqbound, hsqsurj⟩ :=
    exists_squeeze_map (m := m) (δ := ε / 4) (by linarith)
  -- ## Step 4: smoothness of the cut-off family and of its pull-back
  have hΦsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 =>
        (γ q.1 * β q.2) • Work.Drive.chartDiff p D (G q.1) q.2) :=
    contDiff_cutoff_chartDiff_loop m D hD G hG p hγsmooth hβsmooth hUV
      (hγsupp.trans Set.inter_subset_left) hβsupp
  have hΨsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 =>
        (γ (sq q.1) * β q.2) • Work.Drive.chartDiff p D (G (sq q.1)) q.2) := by
    have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 => (sq q.1, q.2)) :=
      (hsqsmooth.comp contDiff_fst).prodMk contDiff_snd
    simpa only [Function.comp_def] using hΦsmooth.comp hpair
  -- ## Step 5: the parametric-Sard hypothesis of the merged theorem
  have hsurjΨ : ∀ (s : EuclideanSpace ℝ (Fin m)) (z : Work.Drive.Amb 4), ‖s‖ < ε →
      (z ∈ K ∨ ∃ i : FaceIdx4,
        z ∈ (fun l : Fdir4 i => Fbase4 i + (l : Work.Drive.Amb 4)) '' (Fcov4 K i)) →
      (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 =>
        (γ (sq q.1) * β q.2) • Work.Drive.chartDiff p D (G (sq q.1)) q.2) (s, z) = 0 →
      Function.Surjective (fderiv ℝ (fun s' : EuclideanSpace ℝ (Fin m) =>
        (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 =>
          (γ (sq q.1) * β q.2) • Work.Drive.chartDiff p D (G (sq q.1)) q.2) (s', z)) s) := by
    intro s z _ hzdisj hzero
    have hz : z ∈ K := hzdisj.elim id (fun h => by
      obtain ⟨i, l, hl, hlz⟩ := h
      rw [← hlz]
      exact hl)
    have hsqb : ‖sq s‖ ≤ ε / 4 := hsqbound s
    have hslt : ‖sq s‖ < ε := by linarith
    have hγv : γ (sq s) = 1 :=
      hγone (sq s) (by rw [Metric.mem_closedBall, dist_zero_right]; exact hsqb)
    have hβv : β z = 1 := hβone z hz
    have hχ0 : Work.Drive.chartDiff p D (G (sq s)) z = 0 := by
      have h : (γ (sq s) * β z) • Work.Drive.chartDiff p D (G (sq s)) z = 0 := hzero
      rw [hγv, hβv, one_mul, one_smul] at h
      exact h
    have hreg : D (Work.Drive.sqPart z) ∈ (Work.Drive.chr p).source ∧
        G (sq s) (Work.Drive.cbPart z) ∈ (Work.Drive.chr p).source :=
      ⟨(hcontain (sq s) z hslt hz).2, (hcontain (sq s) z hslt hz).1⟩
    have hχat : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 =>
          Work.Drive.chartDiff p D (G q.1) q.2) (sq s, z) :=
      contDiffAt_chartDiff_family_fin m D hD G hG p (sq s) hreg
    have hχp : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) =>
        Work.Drive.chartDiff p D (G t') z)
        (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
          Work.Drive.chartDiff p D (G t') z) (sq s)) (sq s) := by
      have h := (hχat.comp (sq s) (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
        top_ne_zero_order
      exact h.hasFDerivAt
    have hγβp : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β z)
        (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β z) (sq s)) (sq s) :=
      ((hγsmooth.contDiffAt.mul contDiffAt_const).differentiableAt top_ne_zero_order).hasFDerivAt
    have hsmul : HasFDerivAt (fun t' : EuclideanSpace ℝ (Fin m) =>
        (γ t' * β z) • Work.Drive.chartDiff p D (G t') z)
        ((γ (sq s) * β z) • (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
            Work.Drive.chartDiff p D (G t') z) (sq s))
          + (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β z) (sq s)).smulRight
              (Work.Drive.chartDiff p D (G (sq s)) z)) (sq s) :=
      hγβp.smul hχp
    have h1 : (γ (sq s) * β z) • (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
            Work.Drive.chartDiff p D (G t') z) (sq s))
          + (fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) => γ t' * β z) (sq s)).smulRight
              (Work.Drive.chartDiff p D (G (sq s)) z)
          = fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
            Work.Drive.chartDiff p D (G t') z) (sq s) := by
      rw [hγv, hβv, one_mul, hχ0]
      simp
    rw [h1] at hsmul
    have hchain : HasFDerivAt (fun s' : EuclideanSpace ℝ (Fin m) =>
        (γ (sq s') * β z) • Work.Drive.chartDiff p D (G (sq s')) z)
        ((fderiv ℝ (fun t' : EuclideanSpace ℝ (Fin m) =>
          Work.Drive.chartDiff p D (G t') z) (sq s)).comp (fderiv ℝ sq s)) s := by
      simpa only [Function.comp_def] using hsmul.comp s
        (((hsqsmooth.differentiable (top_ne_zero_order))).differentiableAt).hasFDerivAt
    rw [hchain.fderiv]
    exact (hsurj (sq s) z hslt hz hχ0).comp (hsqsurj s)
  -- ## Step 6: the merged genericity theorem, with the two-face skeleton of `K`
  obtain ⟨s, _hsnorm, hsgood, hsface, hsavoid⟩ :=
    exists_forall_good_face_and_notMem_family m 4 K hK FaceIdx4
      (fun t : FaceIdx4 => ↥(Fdir4 t)) (fun t => Fdir4_finrank_lt t)
      (fun t : FaceIdx4 => fun l : Fdir4 t => Fbase4 t + (l : Work.Drive.Amb 4))
      (fun t => contDiff_Fparam4 t)
      (fun t : FaceIdx4 => Fcov4 K t) (fun t => Fcov4_isCompact K hK t)
      (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 =>
        (γ (sq q.1) * β q.2) • Work.Drive.chartDiff p D (G (sq q.1)) q.2)
      hΨsmooth ε hε hsurjΨ
  -- ## Step 7: transfer the three clauses back to the chosen parameter `sq s`
  have hslt : ‖sq s‖ < ε := by linarith [hsqbound s]
  have hγv : γ (sq s) = 1 :=
    hγone (sq s) (by rw [Metric.mem_closedBall, dist_zero_right]; exact hsqbound s)
  have hΨzero : ∀ y : Work.Drive.Amb 4, y ∈ K →
      D (Work.Drive.sqPart y) = G (sq s) (Work.Drive.cbPart y) →
      (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 =>
        (γ (sq q.1) * β q.2) • Work.Drive.chartDiff p D (G (sq q.1)) q.2) (s, y) = 0 := by
    intro y hyK heq
    have hcont : y ∈ Work.Drive.chartRegion p D (G (sq s)) :=
      ⟨(hcontain (sq s) y hslt hyK).2, (hcontain (sq s) y hslt hyK).1⟩
    have hzy : Work.Drive.chartDiff p D (G (sq s)) y = 0 :=
      (Work.Drive.chartDiff_eq_zero_iff hcont).mpr heq
    show (γ (sq s) * β y) • Work.Drive.chartDiff p D (G (sq s)) y = 0
    rw [hγv, hβone y hyK, one_mul, hzy, smul_zero]
  refine ⟨sq s, hslt, ?_, ?_⟩
  · -- ### the avoidance clause: no two face coordinates
    intro y hyK heq _hybox h2
    obtain ⟨t', l, hl, hlz⟩ := Fcov4_cover K hyK h2
    have hne := hsavoid t' l hl
    have hne' : (fun q : EuclideanSpace ℝ (Fin m) × Work.Drive.Amb 4 =>
        (γ (sq q.1) * β q.2) • Work.Drive.chartDiff p D (G (sq q.1)) q.2)
        (s, Fbase4 t' + (l : Work.Drive.Amb 4)) ≠ 0 := hne
    rw [show Fbase4 t' + (l : Work.Drive.Amb 4) = y from hlz] at hne'
    exact hne' (hΨzero y hyK heq)
  · -- ### the face clause: the crossing direction
    intro y hyK heq _hybox i hyi _hinter
    have hcont : y ∈ Work.Drive.chartRegion p D (G (sq s)) :=
      ⟨(hcontain (sq s) y hslt hyK).2, (hcontain (sq s) y hslt hyK).1⟩
    have hzy : Work.Drive.chartDiff p D (G (sq s)) y = 0 :=
      (Work.Drive.chartDiff_eq_zero_iff hcont).mpr heq
    have hΨ0 := hΨzero y hyK heq
    have hgood : Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb 4 =>
        (γ (sq s) * β z') • Work.Drive.chartDiff p D (G (sq s)) z') y) :=
      hsgood y hyK hΨ0
    have hfderiv : fderiv ℝ (fun z' : Work.Drive.Amb 4 =>
          (γ (sq s) * β z') • Work.Drive.chartDiff p D (G (sq s)) z') y
        = fderiv ℝ (fun z' : Work.Drive.Amb 4 =>
          Work.Drive.chartDiff p D (G (sq s)) z') y :=
      fderiv_cutoff_chartDiff_eq_loop m D hD G hG p hγsmooth hγv hβsmooth (hβone y hyK) hcont hzy
    have hsurjy : Function.Surjective (fderiv ℝ (fun z' : Work.Drive.Amb 4 =>
        Work.Drive.chartDiff p D (G (sq s)) z') y) := by
      rw [hfderiv] at hgood
      exact hgood
    have hface0 : Function.Surjective (fun v : {v : Work.Drive.Amb 4 // v i = 0} =>
        fderiv ℝ (fun z' : Work.Drive.Amb 4 =>
          (γ (sq s) * β z') • Work.Drive.chartDiff p D (G (sq s)) z') y v.1) :=
      hsface i y hyK hΨ0 hyi
    have hface : Function.Surjective (fun v : {v : Work.Drive.Amb 4 // v i = 0} =>
        fderiv ℝ (fun z' : Work.Drive.Amb 4 =>
          Work.Drive.chartDiff p D (G (sq s)) z') y v.1) := by
      rw [hfderiv] at hface0
      exact hface0
    exact exists_sigma_tau_of_faceSurjective_loop p D (G (sq s)) hD
      (contMDiff_fixed_param_loop m G hG (sq s)) hcont heq hsurjy hface


end

end Work.Drive
