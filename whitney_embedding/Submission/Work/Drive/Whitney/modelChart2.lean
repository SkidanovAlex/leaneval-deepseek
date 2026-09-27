import Mathlib
import Submission.Work.Drive.Whitney.modelChart
import Submission.Work.Drive.Whitney.modelChartOoT2
import Submission.Work.Drive.PushDisc.landingAssembly

/-!
# The model chart of the Whitney move, MARK II: the corrected isolation clause

`Work.Drive.Whitney.ModelChartData` (like its ancestors `SheetChart`/`SheetSetup`) carries the
*global isolation clause*

    hs : ∀ ξ, |ξ.1| < 3/2 → ‖ξ.2.2.2‖ < 1 → Θ ξ ∈ f '' M → ξ ∈ sheetA ∪ sheetB c

which says that the whole model slab contains no image point off the two model sheets.  **That
clause is false**, and it is false for a counting reason that no amount of geometric input can
repair: for `q` in the punctured slab (`q.2 ≠ 0`) every `y : M` with `base y = q`, where
`base y := ((Φ (f y)).1, (Φ (f y)).2.2.2)`, lies in the slab, hence on `sheetA ∪ sheetB`; the sheet
`sheetA` is impossible at `q.2 ≠ 0`, so the point is on the graph, and the sheet chart `σ` puts the
fibre of `base` over `q` inside `{σ q}` — one preimage.  But `base : M → ℝ^n` is a smooth map from
a closed `n`-manifold and `ℝ^n` is contractible, so every regular value of `base` has an even number
of preimages (degree `0`); a regular value in the open punctured slab then gives a contradiction.
(The counting half — `base ⁻¹ {q} = {σ q}` — is *proved* for the ancestors in
`Drive/Whitney/sheetSetupAll.lean` and recorded in
`Drive/Whitney/NOTES_sheetSetupAll_S3_TARGET_FALSE.md`.)

This module replaces the clause by the one the assembly *actually uses*, namely that the *pushed*
sheet misses `f '' M`.  Everything the push needs is then local along the two arcs, and the content
of the geometric input becomes exactly the classical two-sheet normal form:

* `U₁`: a tube around the first arc whose image lies in `sheetA` and is *thin* in the `u`-coordinate;
* the second arc's patch `σ '' reg` mapping onto the graph `{(x, c x, 0, v)}`;
* the *separation* `δ`: the image of the complement of the two patches stays at distance `≥ δ` from
  the graph patch (automatic by compactness, since `f '' M` is closed and the two patches are
  disjoint from the rest — this is a *provable* clause, see `Drive/Whitney/separation2.lean`);
* a *bounded* push `b`, of amplitude `< δ`, and bigger than the tube thickness at the two corners.

The push of this module is the *u*-shear `ψ (x,y,u,v) = (x, y, u - b x * l (‖v‖²), v)` — an explicit
global `C^∞` diffeomorphism.  Because the displacement is bounded by `δ` and is nonzero at the
corners, the pushed sheet misses `f '' M`: the patch case is killed by "the push is active", the
first-tube case by the thinness (the pushed points with `y = 0` force `c x = 0`, hence `x = ±1`,
where the displacement exceeds the tube's thickness), and the rest by the separation.

## Main results

* `Work.Drive.Whitney.mpsiU`, `msigmaU`, `mpsiU_*`: the model move and its calculus.
* `Work.Drive.Whitney.frontier_subset_Oo2`: the `Oo` clause of the model chart, with the *specific*
  open set `{|x| > 5/4} ∪ {1/2 < ‖v‖²}`, adapted to the `u`-shear.
* `Work.Drive.Whitney.ModelChartData2`: the corrected geometric input.
* `Work.Drive.Whitney.hasAmbientPushData_of_modelChartData2`: the assembly.
* `Work.Drive.Whitney.hasPushSignedSmooth_of_modelChartDataAll2`: the target from the quantified
  geometric input.
-/

namespace Work.Drive.Whitney

open scoped Manifold ContDiff
open Set Metric

variable {k : ℕ}

/-- The scalar bump of the model move: `l 0 = 1`, `l t = 0` for `t ≥ 1/2`, `0 ≤ l ≤ 1`. -/
noncomputable def modelL (t : ℝ) : ℝ := Real.smoothTransition (1 - 2 * t)

theorem modelL_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) modelL :=
  (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
    (contDiff_const.sub (contDiff_const.mul contDiff_id))

theorem modelL_zero : modelL 0 = 1 :=
  Real.smoothTransition.one_of_one_le (by norm_num [modelL])

theorem modelL_eq_zero {t : ℝ} (ht : 1 / 2 ≤ t) : modelL t = 0 :=
  Real.smoothTransition.zero_of_nonpos (show 1 - 2 * t ≤ 0 by linarith)

theorem modelL_nonneg (t : ℝ) : 0 ≤ modelL t := Real.smoothTransition.nonneg _

theorem modelL_le_one (t : ℝ) : modelL t ≤ 1 := Real.smoothTransition.le_one _

/-- The open base region of the finger: `|x| < 3/2`, `‖v‖ < 1`. -/
def reg2 (k : ℕ) : Set (ℝ × EuclideanSpace ℝ (Fin k)) := {p | |p.1| < 3 / 2 ∧ ‖p.2‖ < 1}

/-- Its closure, described concretely. -/
def reg2c (k : ℕ) : Set (ℝ × EuclideanSpace ℝ (Fin k)) := {p | |p.1| ≤ 3 / 2 ∧ ‖p.2‖ ≤ 1}

theorem reg2_subset_reg2c : reg2 k ⊆ reg2c k :=
  fun p hp => ⟨le_of_lt hp.1, le_of_lt hp.2⟩

theorem isOpen_reg2 : IsOpen (reg2 k) :=
  isOpen_lt continuous_fst.abs continuous_const |>.inter
    (isOpen_lt (continuous_snd.norm) continuous_const)

theorem mem_reg2_m1 : ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) ∈ reg2 k :=
  ⟨by norm_num [reg2], by simp⟩

theorem mem_reg2_1 : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) ∈ reg2 k :=
  ⟨by norm_num [reg2], by simp⟩

/-- **The model move of MARK II: the `u`-shear.** -/
noncomputable def mpsiU (b : ℝ → EuclideanSpace ℝ (Fin k)) (ξ : Mdl k) : Mdl k :=
  (ξ.1, ξ.2.1, ξ.2.2.1 - modelL (‖ξ.2.2.2‖ ^ 2) • b ξ.1, ξ.2.2.2)

/-- Its inverse. -/
noncomputable def msigmaU (b : ℝ → EuclideanSpace ℝ (Fin k)) (ξ : Mdl k) : Mdl k :=
  (ξ.1, ξ.2.1, ξ.2.2.1 + modelL (‖ξ.2.2.2‖ ^ 2) • b ξ.1, ξ.2.2.2)

theorem mpsiU_contDiff (b : ℝ → EuclideanSpace ℝ (Fin k))
    (hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mpsiU b) := by
  have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mdl k => z.2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp contDiff_snd)
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mdl k => z.2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mdl k => z.1) := contDiff_fst
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mdl k => z.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hnorm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mdl k => ‖z.2.2.2‖ ^ 2) :=
    ContDiff.norm_sq ℝ h4
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mdl k => modelL (‖z.2.2.2‖ ^ 2)) := modelL_contDiff.comp hnorm
  have hb1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mdl k => b z.1) := hb.comp h1
  have hsub : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mdl k => z.2.2.1 - modelL (‖z.2.2.2‖ ^ 2) • b z.1) := h3.sub (hL.smul hb1)
  exact h1.prodMk (h2.prodMk (hsub.prodMk h4))

theorem msigmaU_contDiff (b : ℝ → EuclideanSpace ℝ (Fin k))
    (hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (msigmaU b) := by
  have h4 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mdl k => z.2.2.2) :=
    contDiff_snd.comp (contDiff_snd.comp contDiff_snd)
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mdl k => z.2.2.1) :=
    contDiff_fst.comp (contDiff_snd.comp contDiff_snd)
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mdl k => z.1) := contDiff_fst
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mdl k => z.2.1) :=
    contDiff_fst.comp contDiff_snd
  have hnorm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mdl k => ‖z.2.2.2‖ ^ 2) :=
    ContDiff.norm_sq ℝ h4
  have hL : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mdl k => modelL (‖z.2.2.2‖ ^ 2)) := modelL_contDiff.comp hnorm
  have hb1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Mdl k => b z.1) := hb.comp h1
  have hadd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Mdl k => z.2.2.1 + modelL (‖z.2.2.2‖ ^ 2) • b z.1) := h3.add (hL.smul hb1)
  exact h1.prodMk (h2.prodMk (hadd.prodMk h4))

theorem msigmaU_mpsiU (b : ℝ → EuclideanSpace ℝ (Fin k)) (ξ : Mdl k) :
    msigmaU b (mpsiU b ξ) = ξ := by
  simp [mpsiU, msigmaU, sub_add_cancel]

theorem mpsiU_msigmaU (b : ℝ → EuclideanSpace ℝ (Fin k)) (ξ : Mdl k) :
    mpsiU b (msigmaU b ξ) = ξ := by
  simp [mpsiU, msigmaU, add_sub_cancel_right]

theorem mpsiU_eq_self_iff (b : ℝ → EuclideanSpace ℝ (Fin k)) (ξ : Mdl k) :
    mpsiU b ξ = ξ ↔ modelL (‖ξ.2.2.2‖ ^ 2) • b ξ.1 = 0 := by
  constructor
  · intro h
    have h3 : ξ.2.2.1 - modelL (‖ξ.2.2.2‖ ^ 2) • b ξ.1 = ξ.2.2.1 := by
      simpa [mpsiU] using congrArg (fun w : Mdl k => w.2.2.1) h
    exact sub_eq_self.mp h3
  · intro h
    show (ξ.1, ξ.2.1, ξ.2.2.1 - modelL (‖ξ.2.2.2‖ ^ 2) • b ξ.1, ξ.2.2.2) =
      (ξ.1, ξ.2.1, ξ.2.2.1, ξ.2.2.2)
    rw [h, sub_zero]

/-- The explicit formula of the `u`-shear on the graph of `c`. -/
theorem mpsiU_graph (b : ℝ → EuclideanSpace ℝ (Fin k)) (c : ℝ → ℝ) (x : ℝ)
    (v : EuclideanSpace ℝ (Fin k)) :
    mpsiU b (x, c x, 0, v) = (x, c x, -(modelL (‖v‖ ^ 2) • b x), v) := by
  simp [mpsiU]

end Work.Drive.Whitney

namespace Work.Drive.Whitney

open scoped Manifold ContDiff
open Set Metric

variable {k : ℕ}

theorem smul_eq_zero_of_norm_mul_eq_zero {v : EuclideanSpace ℝ (Fin k)} {t : ℝ}
    (h : ‖v‖ * t = 0) : t • v = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · rw [norm_eq_zero.mp h, smul_zero]
  · rw [h, zero_smul]

theorem norm_neg_smul_zero (b : ℝ → EuclideanSpace ℝ (Fin k)) (x : ℝ) :
    ‖-(modelL (‖(0 : EuclideanSpace ℝ (Fin k))‖ ^ 2) • b x)‖ = ‖b x‖ := by
  rw [norm_neg, norm_smul, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), modelL_zero,
    Real.norm_eq_abs, abs_one, one_mul]

theorem mpsiU_sub_graph_norm (b : ℝ → EuclideanSpace ℝ (Fin k)) (c : ℝ → ℝ)
    (p : ℝ × EuclideanSpace ℝ (Fin k)) :
    ‖mpsiU b (p.1, c p.1, 0, p.2) - (p.1, c p.1, 0, p.2)‖ ≤ ‖b p.1‖ := by
  have hdiff : (mpsiU b (p.1, c p.1, 0, p.2) - (p.1, c p.1, 0, p.2) : Mdl k)
      = (0, (0 : ℝ), -(modelL (‖p.2‖ ^ 2) • b p.1), (0 : EuclideanSpace ℝ (Fin k))) := by
    simp [mpsiU]
  have h3 : ‖(-(modelL (‖p.2‖ ^ 2) • b p.1) : EuclideanSpace ℝ (Fin k))‖ ≤ ‖b p.1‖ := by
    rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_nonneg (modelL_nonneg _)]
    calc modelL (‖p.2‖ ^ 2) * ‖b p.1‖ ≤ 1 * ‖b p.1‖ :=
          mul_le_mul_of_nonneg_right (modelL_le_one _) (norm_nonneg _)
      _ = ‖b p.1‖ := one_mul _
  rw [hdiff]
  simp only [Prod.norm_def, norm_zero]
  refine max_le (norm_nonneg _) (max_le (norm_nonneg _) (max_le h3 (norm_nonneg _)))

end Work.Drive.Whitney

namespace Work.Drive.Whitney

open scoped Manifold ContDiff
open Set Metric

/-! ## The corrected geometric input -/

variable {k : ℕ}

/-- The closed base region equals the closure of the open one. -/
theorem closure_reg2 : closure (reg2 (k := k)) = reg2c (k := k) := by
  refine subset_antisymm ?_ ?_
  · refine closure_minimal (fun p hp => ⟨le_of_lt hp.1, le_of_lt hp.2⟩) ?_
    exact IsClosed.inter (isClosed_le continuous_fst.abs continuous_const)
      (isClosed_le continuous_snd.norm continuous_const)
  · intro p hp
    rw [Metric.mem_closure_iff]
    intro e he
    have hpos : 0 < ‖p‖ + 1 := by positivity
    set t : ℝ := min (e / 2 / (‖p‖ + 1)) (1 / 2) with ht
    have htpos : 0 < t := by
      rw [ht]; exact lt_min (by positivity) (by norm_num)
    have htle12 : t ≤ 1 / 2 := by rw [ht]; exact min_le_right _ _
    have htle : t * (‖p‖ + 1) ≤ e / 2 := by
      rw [ht]
      calc min (e / 2 / (‖p‖ + 1)) (1 / 2) * (‖p‖ + 1)
          ≤ (e / 2 / (‖p‖ + 1)) * (‖p‖ + 1) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ = e / 2 := by field_simp
    refine ⟨(1 - t) • p, ?_, ?_⟩
    · constructor
      · show |((1 - t) • p).1| < 3 / 2
        rw [Prod.smul_fst, smul_eq_mul, abs_mul, abs_of_pos (by linarith [htle12] : (0:ℝ) < 1 - t)]
        nlinarith [hp.1, abs_nonneg p.1, htpos, htle12]
      · show ‖((1 - t) • p).2‖ < 1
        rw [Prod.smul_snd, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by linarith [htle12] : (0:ℝ) < 1 - t)]
        nlinarith [hp.2, norm_nonneg p.2, htpos, htle12]
    · rw [dist_eq_norm]
      have h1 : p - (1 - t) • p = t • p := by
        have h2 := sub_smul (1 : ℝ) (1 - t) p
        rw [one_smul, show (1 : ℝ) - (1 - t) = t by ring] at h2
        exact h2.symm
      rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      nlinarith [norm_nonneg p, htle, he]

/-- **The corrected model chart of the Whitney move.**  All the geometric content of the Whitney
move beyond the model shear: a global `C^∞` diffeomorphism `Φ` (inverse `Θ`) of `ℝ^{2n}` onto the
model `ℝ × ℝ × E × E` (`k = n - 1`), a chart `σ` of the second arc on a region `regσ ⊇ closure reg2`
whose image is the *graph* `{(x, c x, 0, v)}`, a tube `U₁` around the first arc whose image is a thin
piece of `sheetA`, an amplitude function `b` and the *separation* `δ`.

Unlike `ModelChartData` there is **no global isolation clause**: the only requirement on the image
of `f` away from the two patches is the separation `hsepδ`, and the pushed sheet is kept inside the
`δ`-neighbourhood of the graph by the amplitude bound `hbbd`.  The separation is *automatic* — the
two compact sets it separates are disjoint by `hclean`/`hsep` (see `separation2.lean`) — and the
amplitude `b` is a free bump of small norm. -/
structure ModelChartData2 (n : ℕ) {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M) where
  /-- the model dimension `k = n - 1` -/
  k : ℕ
  hk : n = k + 1
  /-- the height function of the second sheet -/
  c : ℝ → ℝ
  hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c
  hc1 : c 1 = 0
  hcm1 : c (-1) = 0
  /-- the two double points are the only points of the spine meeting `sheetA` -/
  hczero : ∀ x : ℝ, |x| < 3 / 2 → c x = 0 → x = 1 ∨ x = -1
  /-- the amplitude of the push -/
  b : ℝ → EuclideanSpace ℝ (Fin k)
  hb : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) b
  hbsupp : ∀ x : ℝ, 5 / 4 ≤ |x| → b x = 0
  /-- the tube thickness -/
  ε : ℝ
  hε : 0 < ε
  hb1 : ε < ‖b 1‖
  hbm1 : ε < ‖b (-1)‖
  /-- the separation -/
  δ : ℝ
  hδ : 0 < δ
  hbbd : ∀ x : ℝ, ‖b x‖ < δ
  /-- the chart of the ambient onto the model -/
  Φ : EuclideanSpace ℝ (Fin (2 * n)) → Mdl k
  Θ : Mdl k → EuclideanSpace ℝ (Fin (2 * n))
  hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
  hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ
  hΘΦ : ∀ y, Θ (Φ y) = y
  hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ
  /-- the chart of the second sheet along its arc -/
  regσ : Set (ℝ × EuclideanSpace ℝ (Fin k))
  hregσo : IsOpen regσ
  hregsub : closure (reg2 (k := k)) ⊆ regσ
  σ : ℝ × EuclideanSpace ℝ (Fin k) → M
  hσc : Continuous σ
  hσ : ∀ p ∈ regσ, f (σ p) = Θ (p.1, c p.1, 0, p.2)
  hp₂ : σ ((-1 : ℝ), 0) = p₂
  hq₂ : σ ((1 : ℝ), 0) = q₂
  hW₀o : IsOpen (σ '' reg2 (k := k))
  hW₀σo : IsOpen (σ '' regσ)
  hW₀W : σ '' regσ ⊆ W
  hpatch₁ : p₁ ∉ σ '' regσ
  hpatch₃ : q₁ ∉ σ '' regσ
  /-- the tube of the first sheet -/
  U₁ : Set M
  hU₁o : IsOpen U₁
  hU₁p₁ : p₁ ∈ U₁
  hU₁q₁ : q₁ ∈ U₁
  hU₁A : ∀ y ∈ U₁, Φ (f y) ∈ sheetA
  hU₁thin : ∀ y ∈ U₁, ‖(Φ (f y)).2.2.1‖ < ε
  /-- **the separation**: outside the two patches, the image stays at distance `≥ δ` from the graph
  patch over the closure of the finger's base region. -/
  hsepδ : ∀ y : M, y ∉ U₁ → y ∉ σ '' regσ → ∀ p ∈ closure (reg2 (k := k)),
    δ ≤ ‖Φ (f y) - (p.1, c p.1, 0, p.2)‖

/-- **The assembly: the corrected model chart gives the clause set of the Whitney move.** -/
theorem hasAmbientPushData_of_modelChartData2 {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (D : ModelChartData2 n f W p₁ p₂ q₁ q₂) :
    Work.Whitney.HasAmbientPushData f W p₁ p₂ q₁ q₂ := by
  classical
  obtain ⟨k, hk, c, hc, hc1, hcm1, hczero, b, hb, hbsupp, ε, hε, hb1, hbm1, δ, hδ, hbbd,
    Φ, Θ, hΦsm, hΘsm, hΘΦ, hΦΘ, regσ, hregσo, hregsub, σ, hσc, hσ, hp₂, hq₂, hW₀o, hW₀σo,
    hW₀W, hpatch₁, hpatch₃, U₁, hU₁o, hU₁p₁, hU₁q₁, hU₁A, hU₁thin, hsepδ⟩ := D
  let W₀ : Set M := σ '' (reg2 k)
  let ψ : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun y => Θ (mpsiU b (Φ y))
  let Sig : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun y => Θ (msigmaU b (Φ y))
  have hΘinj : Function.Injective Θ := fun a b hab => by
    have h := congrArg Φ hab
    rwa [hΦΘ, hΦΘ] at h
  have hσ' : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), |p.1| ≤ 3 / 2 → ‖p.2‖ ≤ 1 →
      f (σ p) = Θ (p.1, c p.1, 0, p.2) :=
    fun p h1 h2 => hσ p (hregsub (by rw [closure_reg2]; exact ⟨h1, h2⟩))
  -- the two corner values
  have hleft : f p₂ = Θ (modelLeft (k := k)) := by
    rw [← hp₂, hσ' ((-1 : ℝ), 0) (by norm_num) (by simp)]
    simp [modelLeft, hcm1]
  have hright : f q₂ = Θ (modelRight (k := k)) := by
    rw [← hq₂, hσ' ((1 : ℝ), 0) (by norm_num) (by simp)]
    simp [modelRight, hc1]
  -- the finger and its two double points
  have hp₂W₀ : p₂ ∈ W₀ := ⟨_, mem_reg2_m1, hp₂⟩
  have hq₂W₀ : q₂ ∈ W₀ := ⟨_, mem_reg2_1, hq₂⟩
  have hsub : reg2 k ⊆ regσ := fun x hx => hregsub (subset_closure hx)
  have hW₀W' : W₀ ⊆ W := Set.Subset.trans (Set.image_mono hsub) hW₀W
  have hp₁W₀ : p₁ ∉ W₀ := fun h => hpatch₁ (Set.image_mono hsub h)
  have hq₁W₀ : q₁ ∉ W₀ := fun h => hpatch₃ (Set.image_mono hsub h)
  -- the fixed set `O`
  obtain ⟨Oo, hOoo, hOozero, hOofront⟩ :=
    modelChartOo_of_t2 f c (fun x => ‖b x‖) modelL (5 / 4) (1 / 2) Φ Θ hΘΦ hΦΘ hΘsm.continuous
      σ hσc hσ' hW₀o (by norm_num) (by norm_num)
      (fun x hx => by rw [hbsupp x (le_of_lt hx), norm_zero])
      (fun t ht => modelL_eq_zero (by linarith))
  let O : Set (EuclideanSpace ℝ (Fin (2 * n))) := Θ '' Oo
  have hOo' : IsOpen O := by
    have hset : O = Φ ⁻¹' Oo := by
      ext y
      constructor
      · rintro ⟨ξ, hξ, rfl⟩
        simpa [hΦΘ] using hξ
      · intro hy
        exact ⟨Φ y, hy, hΘΦ y⟩
    rw [hset]
    exact hOoo.preimage hΦsm.continuous
  have hOid : ∀ y ∈ O, ψ y = y := by
    rintro y ⟨ξ, hξO, rfl⟩
    have hzero : modelL (‖ξ.2.2.2‖ ^ 2) • b ξ.1 = (0 : EuclideanSpace ℝ (Fin k)) :=
      smul_eq_zero_of_norm_mul_eq_zero (hOozero ξ hξO)
    have hfix : mpsiU b ξ = ξ := (mpsiU_eq_self_iff b ξ).mpr hzero
    show Θ (mpsiU b (Φ (Θ ξ))) = Θ ξ
    rw [hΦΘ, hfix]
  -- smoothness and the inverse laws
  have hψsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) ψ :=
    (hΘsm.comp ((mpsiU_contDiff b hb).comp hΦsm)).contMDiff
  have hSigsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) Sig :=
    (hΘsm.comp ((msigmaU_contDiff b hb).comp hΦsm)).contMDiff
  have hσψ : ∀ y, Sig (ψ y) = y := by
    intro y
    show Θ (msigmaU b (Φ (Θ (mpsiU b (Φ y))))) = y
    rw [hΦΘ, msigmaU_mpsiU, hΘΦ]
  have hψσ : ∀ y, ψ (Sig y) = y := by
    intro y
    show Θ (mpsiU b (Φ (Θ (msigmaU b (Φ y))))) = y
    rw [hΦΘ, mpsiU_msigmaU, hΘΦ]
  -- the landing clause: the pushed sheet misses the image
  have hland : ∀ x ∈ W₀, ψ (f x) ≠ f x →
      ψ (f x) ∈ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ := by
    intro x hxW₀ hmov
    obtain ⟨p, hpreg, hpx⟩ := hxW₀
    refine Or.inr ?_
    rintro ⟨y, -, hy⟩
    have hpσ : p ∈ regσ := hregsub (subset_closure hpreg)
    have hξ : Φ (f x) = (p.1, c p.1, 0, p.2) := by
      rw [← hpx, hσ p hpσ, hΦΘ]
    have hξ' : mpsiU b (Φ (f x))
        = (p.1, c p.1, -(modelL (‖p.2‖ ^ 2) • b p.1), p.2) := by
      rw [hξ, mpsiU_graph]
    have hΦy : Φ (f y) = mpsiU b (Φ (f x)) := by
      have h := congrArg Φ hy
      rwa [hΦΘ] at h
    have hact : modelL (‖p.2‖ ^ 2) • b p.1 ≠ 0 := by
      intro h0
      have hfix : mpsiU b (Φ (f x)) = Φ (f x) := by
        rw [hξ', hξ]
        simp [h0]
      exact hmov (by show Θ (mpsiU b (Φ (f x))) = f x; rw [hfix, hΘΦ])
    by_cases hy₁ : y ∈ U₁
    · -- case 1: the point is in the first tube
      have hmemA : mpsiU b (Φ (f x)) ∈ sheetA := by
        rw [← hΦy]; exact hU₁A y hy₁
      rw [hξ'] at hmemA
      obtain ⟨hy0, hv0⟩ := hmemA
      have hnorm : ‖(mpsiU b (Φ (f x))).2.2.1‖ < ε := by
        rw [← hΦy]; exact hU₁thin y hy₁
      rw [hξ'] at hnorm
      rcases hczero p.1 hpreg.1 hy0 with h | h
      · rw [h, hv0] at hnorm
        rw [norm_neg_smul_zero b 1] at hnorm
        linarith [hb1, hnorm]
      · rw [h, hv0] at hnorm
        rw [norm_neg_smul_zero b (-1)] at hnorm
        linarith [hbm1, hnorm]
    · by_cases hy₂ : y ∈ σ '' regσ
      · -- case 2: the point is in the second patch
        obtain ⟨q, hq, hqy⟩ := hy₂
        have hgraph : Φ (f y) = (q.1, c q.1, 0, q.2) := by
          rw [← hqy, hσ q hq, hΦΘ]
        have hEq : (p.1, c p.1, -(modelL (‖p.2‖ ^ 2) • b p.1), p.2)
            = (q.1, c q.1, 0, q.2) := by
          rw [← hξ', ← hΦy, hgraph]
        have h3 : -(modelL (‖p.2‖ ^ 2) • b p.1) = (0 : EuclideanSpace ℝ (Fin k)) := by
          have := congrArg (fun ξ : Mdl k => ξ.2.2.1) hEq
          simpa using this
        exact hact (neg_eq_zero.mp h3)
      · -- case 3: outside both patches, the separation applies
        have hsp := hsepδ y hy₁ hy₂ p (subset_closure hpreg)
        have hEq : Φ (f y) = (p.1, c p.1, -(modelL (‖p.2‖ ^ 2) • b p.1), p.2) := by
          rw [hΦy, hξ']
        rw [hEq] at hsp
        have hdist : ‖(p.1, c p.1, -(modelL (‖p.2‖ ^ 2) • b p.1), p.2)
            - (p.1, c p.1, 0, p.2)‖ ≤ ‖b p.1‖ := by
          rw [← hξ', hξ]
          exact mpsiU_sub_graph_norm b c p
        linarith [hbbd p.1, hsp, hdist]
  -- the two double values are not attained
  have hnonat : ∀ x ∈ W₀, ψ (f x) ≠ f p₂ ∧ ψ (f x) ≠ f q₂ := by
    rintro x ⟨p, hpreg, hpx⟩
    have hpσ : p ∈ regσ := hregsub (subset_closure hpreg)
    have hξ : Φ (f x) = (p.1, c p.1, 0, p.2) := by
      rw [← hpx, hσ p hpσ, hΦΘ]
    have hξ' : mpsiU b (Φ (f x))
        = (p.1, c p.1, -(modelL (‖p.2‖ ^ 2) • b p.1), p.2) := by
      rw [hξ, mpsiU_graph]
    constructor
    · intro hcon
      have h1 : mpsiU b (Φ (f x)) = modelLeft (k := k) := by
        apply hΘinj
        rw [← hleft]
        exact hcon
      rw [hξ'] at h1
      have h3 : -(modelL (‖p.2‖ ^ 2) • b p.1) = (0 : EuclideanSpace ℝ (Fin k)) :=
        congrArg (fun ξ : Mdl k => ξ.2.2.1) h1
      have h4 : p.1 = (-1 : ℝ) := by
        have := congrArg (fun ξ : Mdl k => ξ.1) h1
        simpa [modelLeft] using this
      have h5 : p.2 = (0 : EuclideanSpace ℝ (Fin k)) := by
        have := congrArg (fun ξ : Mdl k => ξ.2.2.2) h1
        simpa [modelLeft] using this
      rw [h4, h5] at h3
      have hb0 : b (-1) = 0 := by
        have := neg_eq_zero.mp h3
        simpa [modelL_zero] using this
      rw [hb0, norm_zero] at hbm1
      linarith [hε, hbm1]
    · intro hcon
      have h1 : mpsiU b (Φ (f x)) = modelRight (k := k) := by
        apply hΘinj
        rw [← hright]
        exact hcon
      rw [hξ'] at h1
      have h3 : -(modelL (‖p.2‖ ^ 2) • b p.1) = (0 : EuclideanSpace ℝ (Fin k)) :=
        congrArg (fun ξ : Mdl k => ξ.2.2.1) h1
      have h4 : p.1 = (1 : ℝ) := by
        have := congrArg (fun ξ : Mdl k => ξ.1) h1
        simpa [modelRight] using this
      have h5 : p.2 = (0 : EuclideanSpace ℝ (Fin k)) := by
        have := congrArg (fun ξ : Mdl k => ξ.2.2.2) h1
        simpa [modelRight] using this
      rw [h4, h5] at h3
      have hb0 : b 1 = 0 := by
        have := neg_eq_zero.mp h3
        simpa [modelL_zero] using this
      rw [hb0, norm_zero] at hb1
      linarith [hε, hb1]
  exact Work.Drive.PushDisc.hasAmbientPushData_of_landing f W p₁ p₂ q₁ q₂ hfp hfq hclean hsep
    W₀ hW₀o hW₀W' hp₂W₀ hq₂W₀ hp₁W₀ hq₁W₀ O hOo' hOofront ψ Sig hOid hσψ hψσ hψsm hSigsm
    hland hnonat

end Work.Drive.Whitney


namespace Work.Drive.Whitney

open scoped Manifold ContDiff
open Set Metric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [CompactSpace M] [SecondCountableTopology M]

/-- **The corrected geometric input, quantified over the target's hypotheses.**  This is the single
remaining obligation of the compact `n ≥ 3` case on this route: the two-sheet normal form along the
bigon (the images of two adjacent tubes are a plane piece and a graph piece over a common base),
together with the numbers `ε, δ` and the amplitude `b`, all of which are *free* once the normal form
is available (`δ` by compactness in `separation2.lean`, `b` by a smooth bump of small norm). -/
def ModelChartDataAll2 (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M)
    (hW₁ : p₁ ∈ W) (hW₂ : p₂ ∈ W) (hW₃ : q₁ ∈ W) (hW₄ : q₂ ∈ W)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (htransP : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤)
    (htransQ : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).range = ⊤)
    (γ₁ γ₂ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγ₁smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₂ t))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsign : Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂),
    Nonempty (ModelChartData2 n f W p₁ p₂ q₁ q₂)

/-- **The target from the corrected model chart.** -/
theorem hasPushSignedSmooth_of_modelChartDataAll2 (h : ModelChartDataAll2 n M) :
    Work.Drive.HasPushSignedSmooth n M := by
  intro hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁ hp₁q₂
    hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hγW₁ hγW₂
    hγ₁inj hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm hγ₂imm hγdisj hγend hsign
  obtain ⟨D⟩ := h hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁
    hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm hγ₂imm hγdisj hγend hsign
  exact hasAmbientPushData_of_modelChartData2 f W p₁ p₂ q₁ q₂ hfp hfq hp₁p₂ hq₁q₂ hclean hsep D

end Work.Drive.Whitney


