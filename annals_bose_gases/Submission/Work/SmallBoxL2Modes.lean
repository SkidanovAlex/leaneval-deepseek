import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import ChallengeDeps
import Submission.CentreBox
import Submission.Work.SmallBoxFourierBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Session-233 — the L²(acube)-Hilbert layer, step 1: the box-Neumann modes
as `Lp ℝ 2` elements

The D1 finiteness of the box-discrete weighted kinetic (`tBmode(s,c,f) :=
Σ_k boxModeCoeff s c k · |c_k(f)|²`) needs Bessel `Σ_k |c_k|² ≤ ‖f‖²` for
the normalised `boxNeumann3` cosine family over the box — the L²(acube)
Hilbert-space layer.  Step 1 (this module): make each mode an element of the
real Hilbert space `Lp ℝ 2 (boxVol s)` (`boxVol s := volume.restrict
(acube s)`), with its `MemLp` certificate:

  * `boxVol s` — the box-restricted volume measure;
  * `acube_lt_top_all` — `volume (acube ℓ) < ∞` for EVERY side (empty cube
    when `ℓ < 0`), so `boxVol_finite` gives `[IsFiniteMeasure (boxVol s)]`
    globally (no side-positivity threading);
  * `boxNeumann3_abs_le_one` — `|mode| ≤ 1` pointwise (product of three
    `|cos| ≤ 1` factors, `Finset.abs_prod` + `prod_le_prod₀`);
  * `boxMode_memLp` — the `MemLp (2)` certificate (continuous ⇒
    AEStronglyMeasurable; `|mode| ≤ 1` on the finite box via
    `MemLp.of_bound`);
  * `boxModeLp s k : Lp ℝ 2 (boxVol s)` — the mode as the Hilbert-space
    element (`MemLp.toLp`).

The real L² Hilbert instance is Mathlib's `L2.innerProductSpace`
(`InnerProductSpace ℝ (Lp ℝ 2 μ)`); the probes at the end verify it.
  * `boxInner_eq_boxIntegral` — `⟪boxModeLp s k, boxModeLp s k'⟫ = ∫_{boxVol s}
    mode_k·mode_k'` (via `L2.inner_def` + `MemLp.coeFn_toLp` +
    `Real.inner_apply`).

  * `piOptionEquivProd_apply_meas` (@[simp]) — the E2 interface lemma:
    `⇑(MeasurableEquiv.piOptionEquivProd (fun _ => ℝ)) f = (fun i => f
    (some i), f none)`; **`piFin3Split_apply`** (`piFin3Split w = (fun i =>
    w i.succ, w 0)`) and **`piFin3Split_symm_apply_zero/_succ`**
    (`(piFin3Split.symm p) 0 = p.2`, `(piFin3Split.symm p) i.succ = p.1 i`)
    — the coordinate-action keystones of leg-2 step 2 (`integral_prod_mul`).
  * **`piFin2Split_symm_apply_one`** and **`pi2_separable`** — the
    Fin-2 pi-separable factorization `∫ t : Fin 2 → ℝ, ∏_i h_i (t i)
    ∂(pi Fin 2 ν) = (∫h₀)·(∫h₁)` (`Fin.prod_univ_two` + the symm
    rewrites + `integral_prod_mul`; the Fin-1 collapse via the `piUnique`
    eval-rewrite + `integral_map` + `piFin1_collapse_measure`).
  * **`piFin3Split_prod_fac`** (the pointwise product split under the
    inverse split: `∏_j g_j ((piFin3Split.symm p) j) = g₀(p.2) · ∏_i
    g_{i.succ}(p.1 i)`; `Fin.prod_univ_succ` + `congr 1` closes with the
    @[simp] symm lemmas) and **`pi3_separable_peel`** — the leg-2 peel:
    `∫ w, ∏_j g_j(w j) ∂(pi Fin 3 ν) = (∫ t : Fin 2 → ℝ, ∏_i g_{i.succ}(t i)
    ∂(pi Fin 2 ν))·(∫ r, g₀ r ∂ν)` (via `(prod).map split.symm = pi Fin 3`
    from `piFin3Split_measure` + `Measure.map_map` + `simp`; `integral_map`
    with the w-continuity AEStronglyMeasurable; `integral_prod_mul` peels).
  * `finSucc0_symm_none` / `finSucc0_symm_some` — the inverse action of
    `e := finSuccEquiv' (0 : Fin 3)`: `e.symm none = 0`, `e.symm (some i) =
    i.succ` (@[simp]; via `Equiv.symm_apply_eq` + `finSuccEquiv'_at`/
    `finSuccEquiv'_succAbove` + `Fin.succAbove_zero`).
  * `cgEuc3_coord` — `(cgEuc3 w) j = w j` (the `toLp` coordinate
    preservation); `acube_pi_separable_integral` — leg 1 of the
    factorization: `∫ z in acube s, ∏_j g_j (z j)` over `boxVol s` equals
    the same integral over the `Measure.pi` of restricted interval measures
    (`acube_restrict_eq_map` + `acubeF_restrict_eq_pi` + `integral_map` +
    coordinate preservation).    * `piFin3Split` (the `Fin 3 ≃ (Fin 2 → ℝ) × ℝ` MeasurableEquiv
    via `finSuccEquiv' 0` + `piCongrLeft` + `piOptionEquivProd`) and
    **`piFin3Split_measure`** — the spine: `(Measure.pi (fun _ : Fin 3 =>
    ν)).map (⇑piFin3Split) = (Measure.pi (fun _ : Fin 2 => ν)).prod ν`
    (via `Measure.pi_map_piCongrLeft` + `Measure.pi_map_piOptionEquivProd`
    + `Measure.map_map`).  Legs 2–3 (pi-separable → ∏ interval
    integrals over Fin 3; Icc ↔ intervalIntegral) remain.

Next steps (recorded): the box-inner-product values
`⟪boxModeLp s k, boxModeLp s k'⟫` = `∫ over acube s of mode·mode'` via the
closed orthogonality/normalisation of `SmallBoxFourierBasis`, then the
orthonormal `Fin 3 → ℕ`-indexed family instance, then Mathlib's Bessel.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section
open MeasureTheory Metric
open scoped ContDiff Topology Real BigOperators ENNReal
namespace Submission
open _root_.BoseGases
namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- the box-restricted volume (the `L²(acube s)` ambient measure). -/
abbrev boxVol (s : ℝ) : Measure ℝ³ := (volume : Measure ℝ³).restrict (acube s)

/-- the centred cube has finite volume for every side (empty for `s < 0`). -/
lemma acube_lt_top_all (ℓ : ℝ) : (volume : Measure ℝ³) (acube ℓ) < (∞ : ℝ≥0∞) := by
  by_cases h : 0 ≤ ℓ
  · simpa using (acube_lt_top ℓ h)
  · have hℓ : ℓ < 0 := lt_of_not_ge h
    have hvol : (volume : Measure ℝ³) (acube ℓ) = 0 := by
      have hle : (volume : Measure ℝ³) (acube ℓ) ≤ 0 := by
        have hss : acube ℓ ⊆ (∅ : Set ℝ³) := by
          intro z hz
          have hz0 : z.ofLp 0 ∈ Set.Icc ((-ℓ) / 2) (ℓ / 2) := hz 0
          rw [Set.mem_Icc] at hz0
          nlinarith [hℓ]
        have hm := measure_mono (μ := (volume : Measure ℝ³)) hss
        simpa using hm
      exact le_antisymm hle (zero_le : 0 ≤ ((volume : Measure ℝ³) (acube ℓ)))
    rw [hvol]
    simp

/-- every box-restricted volume is finite. -/
instance boxVol_finite (s : ℝ) : IsFiniteMeasure (boxVol s) :=
  (MeasureTheory.isFiniteMeasure_restrict).2 (ne_of_lt (acube_lt_top_all s))

/-- `|mode| ≤ 1` pointwise (product of three cosines). -/
lemma boxNeumann3_abs_le_one {ℓ : ℝ} (k : Fin 3 → ℕ) (z : ℝ³) : |boxNeumann3 ℓ k z| ≤ 1 := by
  dsimp [boxNeumann3]
  rw [Finset.abs_prod]
  calc
    (∏ j : Fin 3, |boxNeumann ℓ (k j) (z j)|) ≤ ∏ _j : Fin 3, (1 : ℝ) := by
        refine Finset.prod_le_prod₀ ?_ ?_
        · intro j hj
          exact abs_nonneg _
        · intro j hj
          dsimp [boxNeumann]
          exact Real.abs_cos_le_one _
    _ = 1 := by simp

/-- **the MemLp certificate** for the mode over the box: continuous
(AEStronglyMeasurable) + bounded by `1` on the finite-volume box
(`MemLp.of_bound`). -/
lemma boxMode_memLp (s : ℝ) (k : Fin 3 → ℕ) :
    MemLp (fun z : ℝ³ => boxNeumann3 s k z) (2 : ℝ≥0∞) (boxVol s) := by
  have hf : AEStronglyMeasurable (fun z : ℝ³ => boxNeumann3 s k z) (boxVol s) := by
    exact (by unfold boxNeumann3 boxNeumann; fun_prop : Continuous fun z : ℝ³ => boxNeumann3 s k z).aestronglyMeasurable
  exact MemLp.of_bound (p := (2 : ℝ≥0∞)) hf (C := 1) (by
    filter_upwards with z
    exact boxNeumann3_abs_le_one k z)

/-- **the box-Neumann mode as an element of `Lp ℝ 2 (boxVol s)`** — the first
L²(acube)-Hilbert building block. -/
def boxModeLp (s : ℝ) (k : Fin 3 → ℕ) : Lp ℝ 2 (boxVol s) :=
  MemLp.toLp (fun z : ℝ³ => boxNeumann3 s k z) (boxMode_memLp s k)

/-- probe: the real L² Hilbert instance exists on the mode space. -/
example (s : ℝ) : InnerProductSpace ℝ (Lp ℝ 2 (boxVol s)) := by
  infer_instance

/-- probe: the mode is an element of the real Hilbert space. -/
example (s : ℝ) (k : Fin 3 → ℕ) : Lp ℝ 2 (boxVol s) := boxModeLp s k


/-- **inner-product integral identity**: the real L² inner product of two
box-Neumann modes equals the box integral of their pointwise product —
`⟪boxModeLp s k, boxModeLp s k'⟫ = ∫_{acube s} mode_k·mode_k'` (via
`L2.inner_def` + the a.e.-agreement `MemLp.coeFn_toLp`). -/
lemma boxInner_eq_boxIntegral (s : ℝ) (k k' : Fin 3 → ℕ) :
    inner ℝ (boxModeLp s k) (boxModeLp s k') =
      ∫ z : ℝ³, boxNeumann3 s k z * boxNeumann3 s k' z ∂(boxVol s) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have hk : ((boxModeLp s k : ℝ³ → ℝ)) =ᵐ[boxVol s] (fun z : ℝ³ => boxNeumann3 s k z) := by
    dsimp [boxModeLp]
    simpa using (MemLp.coeFn_toLp (boxMode_memLp s k))
  have hk' : ((boxModeLp s k' : ℝ³ → ℝ)) =ᵐ[boxVol s] (fun z : ℝ³ => boxNeumann3 s k' z) := by
    dsimp [boxModeLp]
    simpa using (MemLp.coeFn_toLp (boxMode_memLp s k'))
  filter_upwards [hk, hk'] with z hzk hzk'
  rw [hzk, hzk', Real.inner_apply]



/-- cgEuc3 preserves coordinates: `(cgEuc3 w) j = w j`. -/
lemma cgEuc3_coord (w : Fin 3 → ℝ) (j : Fin 3) : (cgEuc3 w) j = w j := by
  simp [cgEuc3]

/-- **leg 1 of the factorization**: the `acube`-volume integral of a
coordinate-product equals its integral over the pi-product of restricted
interval measures (via `acube_restrict_eq_map` + `acubeF_restrict_eq_pi` +
`integral_map` + the coordinate preservation of `cgEuc3`). -/
lemma acube_pi_separable_integral (s : ℝ) (g : Fin 3 → ℝ → ℝ)
    (hg : ∀ j : Fin 3, Continuous (g j)) :
    (∫ z : ℝ³, ∏ j : Fin 3, g j (z j) ∂((volume : Measure ℝ³).restrict (acube s)))
      = ∫ w : Fin 3 → ℝ, ∏ j : Fin 3, g j (w j)
          ∂(Measure.pi (fun _ : Fin 3 => (volume : Measure ℝ).restrict (Set.Icc (-s / 2) (s / 2)))) := by
  rw [acube_restrict_eq_map]
  rw [acubeF_restrict_eq_pi]
  rw [MeasureTheory.integral_map]
  · apply integral_congr_ae
    filter_upwards with x
    refine Finset.prod_congr rfl ?_
    intro j hj
    exact congrArg (g j) (cgEuc3_coord x j)
  · exact cgEuc3.measurable.aemeasurable
  · have hc : Continuous (fun z : ℝ³ => ∏ j : Fin 3, g j (z j)) := by
      have hc' : Continuous (fun z : ℝ³ => ∏ j ∈ (Finset.univ : Finset (Fin 3)), g j (z j)) := by
        refine continuous_finsetProd (s := (Finset.univ : Finset (Fin 3))) ?_
        intro j hj
        exact (hg j).comp (by fun_prop : Continuous fun a : ℝ³ => a j)
      simpa using hc'
    exact hc.aestronglyMeasurable



noncomputable def piFin3Split : (Fin 3 → ℝ) ≃ᵐ ((Fin 2 → ℝ) × ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Option (Fin 2) => ℝ) (finSuccEquiv' (0 : Fin 3))).trans
    (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ))



/-- **the measure spine**: pushing the constant pi-measure over `Fin 3`
along `piFin3Split` gives the binary product of the `Fin 2`-pi with the
single-coordinate measure. -/
lemma piFin3Split_measure (ν : Measure ℝ) [SigmaFinite ν] :
    (Measure.pi (fun _ : Fin 3 => ν)).map (⇑piFin3Split)
      = (Measure.pi (fun _ : Fin 2 => ν)).prod ν := by
  let E1 : (Fin 3 → ℝ) ≃ᵐ (Option (Fin 2) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Option (Fin 2) => ℝ) (finSuccEquiv' (0 : Fin 3))
  let E2 : (Option (Fin 2) → ℝ) ≃ᵐ ((Fin 2 → ℝ) × ℝ) :=
    MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)
  have h1 := Measure.pi_map_piCongrLeft (e := finSuccEquiv' (0 : Fin 3))
    (μ := fun _ : Option (Fin 2) => ν)
  have h2raw := Measure.pi_map_piOptionEquivProd (μ := fun _ : Option (Fin 2) => ν)
  have h2 : (Measure.pi (fun _ : Option (Fin 2) => ν)).map (⇑E2)
      = (Measure.pi (fun i : Fin 2 => ν)).prod ν := by
    rw [← h2raw]
    rw [Measure.map_map E2.measurable E2.symm.measurable]
    simp
  calc
    (Measure.pi (fun _ : Fin 3 => ν)).map (⇑piFin3Split)
        = ((Measure.pi (fun _ : Fin 3 => ν)).map (⇑E1)).map (⇑E2) := by
            rw [Measure.map_map E2.measurable E1.measurable]
            rfl
    _ = (Measure.pi (fun _ : Option (Fin 2) => ν)).map (⇑E2) := by rw [h1]
    _ = (Measure.pi (fun i : Fin 2 => ν)).prod ν := h2



@[simp] lemma finSucc0_symm_none : (finSuccEquiv' (0 : Fin 3)).symm none = (0 : Fin 3) := by
  exact (Equiv.symm_apply_eq (finSuccEquiv' (0 : Fin 3))).2 (finSuccEquiv'_at (0 : Fin 3)).symm

@[simp] lemma finSucc0_symm_some (i : Fin 2) : (finSuccEquiv' (0 : Fin 3)).symm (some i) = i.succ := by
  have h0 : (0 : Fin 3).succAbove i = i.succ := by
    simp
  rw [← h0]
  exact (Equiv.symm_apply_eq (finSuccEquiv' (0 : Fin 3))).2 (finSuccEquiv'_succAbove (0 : Fin 3) i)



@[simp] lemma piOptionEquivProd_apply_meas (f : Option (Fin 2) → ℝ) :
    (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)) f
      = ((fun i : Fin 2 => f (some i)), f none) := by
  simp only [MeasurableEquiv.piOptionEquivProd, MeasurableEquiv.trans_apply]
  have hA : ((Equiv.piCongrLeft (fun _ : Option (Fin 2) => ℝ) (Equiv.optionEquivSumPUnit (Fin 2)).symm).symm) f
      = fun s : Sum (Fin 2) PUnit => f ((Equiv.optionEquivSumPUnit (Fin 2)).symm s) := by
    funext s
    rw [Equiv.piCongrLeft_symm_apply]
  -- change the two INNER MeasurableEquiv apps to their Equiv forms, keep the outer
  change ((MeasurableEquiv.refl (Fin 2 → ℝ)).prodCongr (MeasurableEquiv.piUnique (fun _ : PUnit => ℝ)))
      ((Equiv.sumPiEquivProdPi (fun _ : Sum (Fin 2) PUnit => ℝ))
        ((Equiv.piCongrLeft (fun _ : Option (Fin 2) => ℝ) (Equiv.optionEquivSumPUnit (Fin 2)).symm).symm f))
      = ((fun i : Fin 2 => f (some i)), f none)
  rw [hA]
  rw [Equiv.sumPiEquivProdPi_apply]
  -- outer (refl.prodCongr piUnique) applied to the pair (a, h): collapses h at default
  -- a = fun i => f (e.symm (inl i)) = fun i => f (some i); h default = f (e.symm (inr default)) = f none
  simp [MeasurableEquiv.prodCongr, MeasurableEquiv.piUnique_apply, Equiv.optionEquivSumPUnit]


lemma piFin3Split_apply (w : Fin 3 → ℝ) :
    piFin3Split w = ((fun i : Fin 2 => w i.succ), w 0) := by
  change (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ))
      ((MeasurableEquiv.piCongrLeft (fun _ : Option (Fin 2) => ℝ) (finSuccEquiv' (0 : Fin 3))) w)
      = ((fun i : Fin 2 => w i.succ), w 0)
  have hE1 : (MeasurableEquiv.piCongrLeft (fun _ : Option (Fin 2) => ℝ) (finSuccEquiv' (0 : Fin 3))) w
      = fun a : Option (Fin 2) => w ((finSuccEquiv' (0 : Fin 3)).symm a) := by
    funext a
    change (Equiv.piCongrLeft (fun _ : Option (Fin 2) => ℝ) (finSuccEquiv' (0 : Fin 3))) w a
        = w ((finSuccEquiv' (0 : Fin 3)).symm a)
    rw [Equiv.piCongrLeft_apply]
    simp
  rw [hE1]
  rw [piOptionEquivProd_apply_meas]
  simp


lemma piFin3Split_symm_apply_zero (p : (Fin 2 → ℝ) × ℝ) :
    (piFin3Split.symm p) (0 : Fin 3) = p.2 := by
  have hc : (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ))
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)).symm p) = p :=
    MeasurableEquiv.apply_symm_apply (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)) p
  rw [piOptionEquivProd_apply_meas] at hc
  have hz : (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)).symm p none = p.2 := by
    exact congrArg Prod.snd hc
  -- compute the symm of the composite on coordinate 0
  change (MeasurableEquiv.piCongrLeft (fun _ : Option (Fin 2) => ℝ) (finSuccEquiv' (0 : Fin 3))).symm
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)).symm p) (0 : Fin 3) = p.2
  have hE1 : (MeasurableEquiv.piCongrLeft (fun _ : Option (Fin 2) => ℝ) (finSuccEquiv' (0 : Fin 3))).symm
        ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)).symm p) (0 : Fin 3)
      = (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)).symm p none := by
    change (Equiv.piCongrLeft (fun _ : Option (Fin 2) => ℝ) (finSuccEquiv' (0 : Fin 3))).symm
        ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)).symm p) (0 : Fin 3)
        = (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)).symm p none
    rw [Equiv.piCongrLeft_symm_apply]
    simp
  rw [hE1]
  exact hz

lemma piFin3Split_symm_apply_succ (p : (Fin 2 → ℝ) × ℝ) (i : Fin 2) :
    (piFin3Split.symm p) i.succ = p.1 i := by
  have hc : (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ))
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)).symm p) = p :=
    MeasurableEquiv.apply_symm_apply (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)) p
  rw [piOptionEquivProd_apply_meas] at hc
  have hs : (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)).symm p (some i) = p.1 i := by
    exact congrArg (fun q : (Fin 2 → ℝ) × ℝ => q.1 i) hc
  change (MeasurableEquiv.piCongrLeft (fun _ : Option (Fin 2) => ℝ) (finSuccEquiv' (0 : Fin 3))).symm
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)).symm p) i.succ = p.1 i
  have hE1 : (MeasurableEquiv.piCongrLeft (fun _ : Option (Fin 2) => ℝ) (finSuccEquiv' (0 : Fin 3))).symm
        ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)).symm p) i.succ
      = (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)).symm p (some i) := by
    change (Equiv.piCongrLeft (fun _ : Option (Fin 2) => ℝ) (finSuccEquiv' (0 : Fin 3))).symm
        ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)).symm p) i.succ
        = (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 2) => ℝ)).symm p (some i)
    rw [Equiv.piCongrLeft_symm_apply]
    have hsa := congrFun (Fin.succAbove_zero (n := 2)) i
    have hf : (finSuccEquiv' (0 : Fin 3)) i.succ = some i := by
      rw [show i.succ = (0 : Fin 3).succAbove i by rw [← hsa]]
      exact finSuccEquiv'_succAbove (0 : Fin 3) i
    rw [hf]
  rw [hE1]
  exact hs



lemma piFin3Split_prod_fac (g : Fin 3 → ℝ → ℝ) (p : (Fin 2 → ℝ) × ℝ) :
    (∏ j : Fin 3, g j ((piFin3Split.symm p) j)) = g 0 (p.2) * (∏ i : Fin 2, g i.succ (p.1 i)) := by
  calc
    (∏ j : Fin 3, g j ((piFin3Split.symm p) j))
        = g 0 ((piFin3Split.symm p) (0 : Fin 3)) * (∏ i : Fin 2, g i.succ ((piFin3Split.symm p) i.succ)) := by
            rw [Fin.prod_univ_succ]
    _ = g 0 (p.2) * (∏ i : Fin 2, g i.succ (p.1 i)) := by
            rw [piFin3Split_symm_apply_zero]
            congr 1


lemma pi3_separable_peel (ν : Measure ℝ) [SigmaFinite ν] (g : Fin 3 → ℝ → ℝ)
    (hg : ∀ j : Fin 3, Continuous (g j)) :
    (∫ w : Fin 3 → ℝ, ∏ j : Fin 3, g j (w j) ∂(Measure.pi (fun _ : Fin 3 => ν)))
      = (∫ t : Fin 2 → ℝ, ∏ i : Fin 2, g i.succ (t i) ∂(Measure.pi (fun _ : Fin 2 => ν)))
          * (∫ r : ℝ, g 0 r ∂ν) := by
  have hsplit := piFin3Split_measure ν
  -- (prod).map split.symm = pi Fin 3
  have hs2 : ((Measure.pi (fun _ : Fin 2 => ν)).prod ν).map (⇑piFin3Split.symm)
      = Measure.pi (fun _ : Fin 3 => ν) := by
    rw [← hsplit]
    rw [Measure.map_map piFin3Split.symm.measurable piFin3Split.measurable]
    simp
  -- continuity of the w-integrand (needed for the integral_map AEStronglyMeasurable)
  have hcw : Continuous (fun w : Fin 3 → ℝ => ∏ j : Fin 3, g j (w j)) := by
    refine continuous_finsetProd (s := (Finset.univ : Finset (Fin 3))) ?_
    intro j hj
    exact (hg j).comp (by fun_prop : Continuous fun w : Fin 3 → ℝ => w j)
  calc
    (∫ w : Fin 3 → ℝ, ∏ j : Fin 3, g j (w j) ∂(Measure.pi (fun _ : Fin 3 => ν)))
        = ∫ p : (Fin 2 → ℝ) × ℝ, ∏ j : Fin 3, g j ((piFin3Split.symm p) j)
            ∂((Measure.pi (fun _ : Fin 2 => ν)).prod ν) := by
            rw [← hs2]
            rw [MeasureTheory.integral_map piFin3Split.symm.measurable.aemeasurable hcw.aestronglyMeasurable]
    _ = ∫ p : (Fin 2 → ℝ) × ℝ, (∏ i : Fin 2, g i.succ (p.1 i)) * g 0 (p.2)
            ∂((Measure.pi (fun _ : Fin 2 => ν)).prod ν) := by
            apply integral_congr_ae
            filter_upwards with p
            rw [piFin3Split_prod_fac g p, mul_comm]
    _ = (∫ t : Fin 2 → ℝ, ∏ i : Fin 2, g i.succ (t i) ∂(Measure.pi (fun _ : Fin 2 => ν)))
          * (∫ r : ℝ, g 0 r ∂ν) := by
            exact MeasureTheory.integral_prod_mul
              (μ := Measure.pi (fun _ : Fin 2 => ν)) (ν := ν)
              (f := fun t : Fin 2 → ℝ => ∏ i : Fin 2, g i.succ (t i)) (g := g 0)



noncomputable def piFin2Split : (Fin 2 → ℝ) ≃ᵐ ((Fin 1 → ℝ) × ℝ) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Option (Fin 1) => ℝ) (finSuccEquiv' (0 : Fin 2))).trans
    (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ))

/-- the Fin-2 measure spine. -/
lemma piFin2Split_measure (ν : Measure ℝ) [SigmaFinite ν] :
    (Measure.pi (fun _ : Fin 2 => ν)).map (⇑piFin2Split)
      = (Measure.pi (fun _ : Fin 1 => ν)).prod ν := by
  let E1 : (Fin 2 → ℝ) ≃ᵐ (Option (Fin 1) → ℝ) :=
    MeasurableEquiv.piCongrLeft (fun _ : Option (Fin 1) => ℝ) (finSuccEquiv' (0 : Fin 2))
  let E2 : (Option (Fin 1) → ℝ) ≃ᵐ ((Fin 1 → ℝ) × ℝ) :=
    MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)
  have h1 := Measure.pi_map_piCongrLeft (e := finSuccEquiv' (0 : Fin 2))
    (μ := fun _ : Option (Fin 1) => ν)
  have h2raw := Measure.pi_map_piOptionEquivProd (μ := fun _ : Option (Fin 1) => ν)
  have h2 : (Measure.pi (fun _ : Option (Fin 1) => ν)).map (⇑E2)
      = (Measure.pi (fun i : Fin 1 => ν)).prod ν := by
    rw [← h2raw]
    rw [Measure.map_map E2.measurable E2.symm.measurable]
    simp
  calc
    (Measure.pi (fun _ : Fin 2 => ν)).map (⇑piFin2Split)
        = ((Measure.pi (fun _ : Fin 2 => ν)).map (⇑E1)).map (⇑E2) := by
            rw [Measure.map_map E2.measurable E1.measurable]
            rfl
    _ = (Measure.pi (fun _ : Option (Fin 1) => ν)).map (⇑E2) := by rw [h1]
    _ = (Measure.pi (fun i : Fin 1 => ν)).prod ν := h2

/-- the Fin-1 collapse is measure-preserving: `(pi over Fin 1 ν).map (eval at
0) = ν`. -/
lemma piFin1_collapse_measure (ν : Measure ℝ) :
    (Measure.pi (fun _ : Fin 1 => ν)).map (⇑(MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)))
      = ν := by
  exact (measurePreserving_piUnique (X := fun _ : Fin 1 => ℝ) (μ := fun _ : Fin 1 => ν)).map_eq


/-- **(a)** mapping the split-product measure by `piFin2Split.symm` recovers
the `Fin 2` pi-measure. -/
lemma piFin2Split_measure_symm (ν : Measure ℝ) [SigmaFinite ν] :
    ((Measure.pi (fun _ : Fin 1 => ν)).prod ν).map (⇑piFin2Split.symm)
      = Measure.pi (fun _ : Fin 2 => ν) := by
  have hsplit := piFin2Split_measure ν
  rw [← hsplit]
  rw [Measure.map_map piFin2Split.symm.measurable piFin2Split.measurable]
  simp



/-- **(b)** change of variables: the `Fin 2`-pi integral equals the integral
over the split product of the pulled-back integrand. -/
lemma pi2_change_variables (ν : Measure ℝ) [SigmaFinite ν] (h : Fin 2 → ℝ → ℝ)
    (hh : ∀ i : Fin 2, Continuous (h i)) :
    (∫ w : Fin 2 → ℝ, ∏ i : Fin 2, h i (w i) ∂(Measure.pi (fun _ : Fin 2 => ν)))
      = ∫ p : (Fin 1 → ℝ) × ℝ, ∏ i : Fin 2, h i ((piFin2Split.symm p) i)
          ∂((Measure.pi (fun _ : Fin 1 => ν)).prod ν) := by
  have hcw : Continuous (fun w : Fin 2 → ℝ => ∏ i : Fin 2, h i (w i)) := by
    refine continuous_finsetProd (s := (Finset.univ : Finset (Fin 2))) ?_
    intro i hi
    exact (hh i).comp (by fun_prop : Continuous fun w : Fin 2 → ℝ => w i)
  rw [← piFin2Split_measure_symm ν]
  rw [MeasureTheory.integral_map piFin2Split.symm.measurable.aemeasurable hcw.aestronglyMeasurable]



@[simp] lemma piOptionEquivProd_apply_meas_general {δ : Type*} (f : Option δ → ℝ) :
    (MeasurableEquiv.piOptionEquivProd (fun _ : Option δ => ℝ)) f
      = ((fun i : δ => f (some i)), f none) := by
  simp only [MeasurableEquiv.piOptionEquivProd, MeasurableEquiv.trans_apply]
  have hA : ((Equiv.piCongrLeft (fun _ : Option δ => ℝ) (Equiv.optionEquivSumPUnit δ).symm).symm) f
      = fun s : Sum δ PUnit => f ((Equiv.optionEquivSumPUnit δ).symm s) := by
    funext s
    rw [Equiv.piCongrLeft_symm_apply]
  change ((MeasurableEquiv.refl (δ → ℝ)).prodCongr (MeasurableEquiv.piUnique (fun _ : PUnit => ℝ)))
      ((Equiv.sumPiEquivProdPi (fun _ : Sum δ PUnit => ℝ))
        ((Equiv.piCongrLeft (fun _ : Option δ => ℝ) (Equiv.optionEquivSumPUnit δ).symm).symm f))
      = ((fun i : δ => f (some i)), f none)
  rw [hA]
  rw [Equiv.sumPiEquivProdPi_apply]
  simp [MeasurableEquiv.prodCongr, MeasurableEquiv.piUnique_apply, Equiv.optionEquivSumPUnit]

@[simp] lemma finSucc0'_2_symm_none : (finSuccEquiv' (0 : Fin 2)).symm none = (0 : Fin 2) := by
  exact (Equiv.symm_apply_eq (finSuccEquiv' (0 : Fin 2))).2 (finSuccEquiv'_at (0 : Fin 2)).symm

@[simp] lemma finSucc0'_2_symm_some (i : Fin 1) : (finSuccEquiv' (0 : Fin 2)).symm (some i) = i.succ := by
  have h0 : (0 : Fin 2).succAbove i = i.succ := by
    simp
  rw [← h0]
  exact (Equiv.symm_apply_eq (finSuccEquiv' (0 : Fin 2))).2 (finSuccEquiv'_succAbove (0 : Fin 2) i)

lemma piFin2Split_symm_apply_zero (p : (Fin 1 → ℝ) × ℝ) :
    (piFin2Split.symm p) (0 : Fin 2) = p.2 := by
  have hc : (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ))
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).symm p) = p :=
    MeasurableEquiv.apply_symm_apply (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)) p
  rw [piOptionEquivProd_apply_meas_general] at hc
  have hz : (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).symm p none = p.2 := by
    exact congrArg Prod.snd hc
  change (MeasurableEquiv.piCongrLeft (fun _ : Option (Fin 1) => ℝ) (finSuccEquiv' (0 : Fin 2))).symm
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).symm p) (0 : Fin 2) = p.2
  have hE1 : (MeasurableEquiv.piCongrLeft (fun _ : Option (Fin 1) => ℝ) (finSuccEquiv' (0 : Fin 2))).symm
        ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).symm p) (0 : Fin 2)
      = (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).symm p none := by
    change (Equiv.piCongrLeft (fun _ : Option (Fin 1) => ℝ) (finSuccEquiv' (0 : Fin 2))).symm
        ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).symm p) (0 : Fin 2)
        = (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).symm p none
    rw [Equiv.piCongrLeft_symm_apply]
    simp
  rw [hE1]
  exact hz

lemma piFin2Split_symm_apply_succ (p : (Fin 1 → ℝ) × ℝ) (i : Fin 1) :
    (piFin2Split.symm p) i.succ = p.1 i := by
  have hc : (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ))
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).symm p) = p :=
    MeasurableEquiv.apply_symm_apply (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)) p
  rw [piOptionEquivProd_apply_meas_general] at hc
  have hs : (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).symm p (some i) = p.1 i := by
    exact congrArg (fun q : (Fin 1 → ℝ) × ℝ => q.1 i) hc
  change (MeasurableEquiv.piCongrLeft (fun _ : Option (Fin 1) => ℝ) (finSuccEquiv' (0 : Fin 2))).symm
      ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).symm p) i.succ = p.1 i
  have hE1 : (MeasurableEquiv.piCongrLeft (fun _ : Option (Fin 1) => ℝ) (finSuccEquiv' (0 : Fin 2))).symm
        ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).symm p) i.succ
      = (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).symm p (some i) := by
    change (Equiv.piCongrLeft (fun _ : Option (Fin 1) => ℝ) (finSuccEquiv' (0 : Fin 2))).symm
        ((MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).symm p) i.succ
        = (MeasurableEquiv.piOptionEquivProd (fun _ : Option (Fin 1) => ℝ)).symm p (some i)
    rw [Equiv.piCongrLeft_symm_apply]
    have hsa := congrFun (Fin.succAbove_zero (n := 1)) i
    have hf : (finSuccEquiv' (0 : Fin 2)) i.succ = some i := by
      rw [show i.succ = (0 : Fin 2).succAbove i by rw [← hsa]]
      exact finSuccEquiv'_succAbove (0 : Fin 2) i
    rw [hf]
  rw [hE1]
  exact hs



lemma piFin2Split_symm_apply_one (p : (Fin 1 → ℝ) × ℝ) :
    (piFin2Split.symm p) (1 : Fin 2) = p.1 (0 : Fin 1) := by
  simpa using (piFin2Split_symm_apply_succ p (0 : Fin 1))

/-- **`pi2_separable`**: the Fin-2 pi-separable factorization. -/
lemma pi2_separable (ν : Measure ℝ) [SigmaFinite ν] (h : Fin 2 → ℝ → ℝ)
    (hh : ∀ i : Fin 2, Continuous (h i)) :
    (∫ t : Fin 2 → ℝ, ∏ i : Fin 2, h i (t i) ∂(Measure.pi (fun _ : Fin 2 => ν)))
      = (∫ x : ℝ, h 0 x ∂ν) * (∫ x : ℝ, h 1 x ∂ν) := by
  calc
    (∫ t : Fin 2 → ℝ, ∏ i : Fin 2, h i (t i) ∂(Measure.pi (fun _ : Fin 2 => ν)))
        = ∫ p : (Fin 1 → ℝ) × ℝ, ∏ i : Fin 2, h i ((piFin2Split.symm p) i)
            ∂((Measure.pi (fun _ : Fin 1 => ν)).prod ν) := pi2_change_variables ν h hh
    _ = (∫ u : Fin 1 → ℝ, h 1 (u (0 : Fin 1)) ∂(Measure.pi (fun _ : Fin 1 => ν)))
          * (∫ r : ℝ, h 0 r ∂ν) := by
            have hpt : ∀ p : (Fin 1 → ℝ) × ℝ,
                (∏ i : Fin 2, h i ((piFin2Split.symm p) i)) = h 1 (p.1 (0 : Fin 1)) * h 0 (p.2) := by
              intro p
              rw [Fin.prod_univ_two]
              rw [piFin2Split_symm_apply_zero, piFin2Split_symm_apply_one]
              ring
            rw [← MeasureTheory.integral_prod_mul
              (μ := Measure.pi (fun _ : Fin 1 => ν)) (ν := ν)
              (f := fun u : Fin 1 → ℝ => h 1 (u (0 : Fin 1))) (g := h 0)]
            apply integral_congr_ae
            filter_upwards with p
            rw [hpt p]
    _ = (∫ x : ℝ, h 1 x ∂ν) * (∫ x : ℝ, h 0 x ∂ν) := by
            have hcoll : (∫ u : Fin 1 → ℝ, h 1 (u (0 : Fin 1)) ∂(Measure.pi (fun _ : Fin 1 => ν)))
                = ∫ x : ℝ, h 1 x ∂ν := by
              have hmp := piFin1_collapse_measure ν
              have hrew : (fun u : Fin 1 → ℝ => h 1 (u (0 : Fin 1)))
                  = fun u : Fin 1 → ℝ => h 1 ((MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)) u) := by
                funext u
                congr 1
              rw [hrew]
              rw [← MeasureTheory.integral_map]
              · rw [hmp]
              · exact (MeasurableEquiv.piUnique (fun _ : Fin 1 => ℝ)).measurable.aemeasurable
              · have hc : Continuous (fun y : ℝ => h 1 y) := hh 1
                exact hc.aestronglyMeasurable
            rw [hcoll]
    _ = (∫ x : ℝ, h 0 x ∂ν) * (∫ x : ℝ, h 1 x ∂ν) := by rw [mul_comm]



/-- **`pi3_separable`**: the full Fin-3 pi-separable factorization. -/
lemma pi3_separable (ν : Measure ℝ) [SigmaFinite ν] (g : Fin 3 → ℝ → ℝ)
    (hg : ∀ j : Fin 3, Continuous (g j)) :
    (∫ w : Fin 3 → ℝ, ∏ j : Fin 3, g j (w j) ∂(Measure.pi (fun _ : Fin 3 => ν)))
      = ∏ j : Fin 3, (∫ x : ℝ, g j x ∂ν) := by
  rw [pi3_separable_peel ν g hg]
  -- peel leaves: (∫ t : Fin 2 → ℝ, ∏_i g i.succ (t i) ∂(pi Fin 2 ν)) · (∫ x, g 0 x ∂ν)
  have htail := pi2_separable ν (fun i : Fin 2 => g i.succ) (fun i => hg i.succ)
  -- htail : (∫ t, ∏_i g i.succ(t i)) = (∫x, g (0:Fin2).succ x) * (∫x, g (1:Fin2).succ x)
  rw [htail]
  -- goal: ((∫ g 0.succ)·(∫ g 1.succ))·(∫ g 0) = ∏_{j:Fin 3} ∫ g j
  rw [Fin.prod_univ_succ]
  -- goal: ((∫ g 0.succ)·(∫ g 1.succ))·(∫ g 0) = (∫ g 0) · (∏_{i:Fin 2} ∫ g i.succ)
  rw [Fin.prod_univ_succ]
  rw [Fin.prod_univ_succ]
  simp
  ring





open scoped intervalIntegral in
lemma interval_restrict_integral {a b : ℝ} (h : a ≤ b) (f : ℝ → ℝ) :
    (∫ x : ℝ, f x ∂((volume : Measure ℝ).restrict (Set.Icc a b))) = ∫ x in a..b, f x := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le h]

open scoped intervalIntegral in
/-- **the box factorization**: `∫ z in acube s, ∏_j h_j (z j) =
∏_j (∫ x in (-s/2)..(s/2), h_j x)` for continuous `h_j`, `0 ≤ s`. -/
lemma acube_separable_integral_interval (s : ℝ) (hs : 0 ≤ s) (h : Fin 3 → ℝ → ℝ)
    (hh : ∀ j : Fin 3, Continuous (h j)) :
    (∫ z : ℝ³ in acube s, ∏ j : Fin 3, h j (z j))
      = ∏ j : Fin 3, (∫ x in (-s / 2)..(s / 2), h j x) := by
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc (-s / 2) (s / 2))
  have h1 := acube_pi_separable_integral s h hh
  have hp := pi3_separable ν h hh
  calc
    (∫ z : ℝ³ in acube s, ∏ j : Fin 3, h j (z j))
        = ∫ w : Fin 3 → ℝ, ∏ j : Fin 3, h j (w j) ∂(Measure.pi (fun _ : Fin 3 => ν)) := by
            simpa [ν] using h1
    _ = ∏ j : Fin 3, (∫ x : ℝ, h j x ∂ν) := hp
    _ = ∏ j : Fin 3, (∫ x in (-s / 2)..(s / 2), h j x) := by
            apply Finset.prod_congr rfl
            intro j hj
            dsimp [ν]
            rw [interval_restrict_integral (a := -s / 2) (b := s / 2)
              (h := (by nlinarith [hs] : -s / 2 ≤ s / 2)) (f := h j)]



open scoped intervalIntegral in
/-- **mode inner product = product of 1-D interval integrals**: the L² inner
product of two box modes factors coordinate-by-coordinate. -/
lemma boxInner_eq_prod_interval {s : ℝ} (hs : 0 < s) (k k' : Fin 3 → ℕ) :
    inner ℝ (boxModeLp s k) (boxModeLp s k')
      = ∏ j : Fin 3,
          (∫ x in (-s / 2)..(s / 2), boxNeumann s (k j) x * boxNeumann s (k' j) x) := by
  rw [boxInner_eq_boxIntegral s k k']
  -- pointwise: boxNeumann3 s k z * boxNeumann3 s k' z = ∏_j (u_{k j} z j · u_{k' j} z j)
  have hpt : (fun z : ℝ³ => boxNeumann3 s k z * boxNeumann3 s k' z)
      = fun z : ℝ³ => ∏ j : Fin 3, boxNeumann s (k j) (z j) * boxNeumann s (k' j) (z j) := by
    funext z
    dsimp [boxNeumann3]
    rw [Finset.prod_mul_distrib]
  rw [hpt]
  -- box factorization
  have hfac := acube_separable_integral_interval s (le_of_lt hs)
    (fun j : Fin 3 => fun x : ℝ => boxNeumann s (k j) x * boxNeumann s (k' j) x) (by
      intro j
      exact (by unfold boxNeumann; fun_prop : Continuous fun x : ℝ =>
        boxNeumann s (k j) x * boxNeumann s (k' j) x))
  -- hfac : ∫ z in acube s, ∏_j h_j(z j) = ∏_j ∫ x in -s/2..s/2 h_j x
  -- LHS of goal: ∫ z, mode·mode' ∂boxVol s = ∫ z in acube s, (mode·mode')
  simpa using hfac



open scoped intervalIntegral in
/-- **mode orthogonality**: distinct product modes have zero L² inner
product (a differing coordinate kills the product via the 1-D
orthogonality). -/
lemma boxMode_inner_eq_zero_of_ne {s : ℝ} (hs : 0 < s) {k k' : Fin 3 → ℕ}
    (h : k ≠ k') : inner ℝ (boxModeLp s k) (boxModeLp s k') = 0 := by
  rw [boxInner_eq_prod_interval hs]
  -- pick a coordinate where they differ
  have hdiff : ∃ j : Fin 3, k j ≠ k' j := by
    by_contra hne
    push Not at hne
    apply h
    funext j
    exact hne j
  rcases hdiff with ⟨j0, hj0⟩
  -- product with a zero factor is zero
  refine Finset.prod_eq_zero (Finset.mem_univ j0) ?_
  have hz := boxNeumann_distinct_orthogonal hs hj0
  -- hz : (∫ x in (-(s/2))..(s/2), boxNeumann s (k j0) x * boxNeumann s (k' j0) x) = 0
  -- my factor: ∫ x in (-s/2)..(s/2), ... -- bridge the bound spelling
  rw [show (-s / 2) = (-(s / 2)) by ring]
  exact hz




open scoped intervalIntegral in
/-- **squared mode norm = product of the 1-D squared-mode integrals**:
`inner (boxModeLp s k) (boxModeLp s k) = ∏_j (∫ x in (-s/2)..(s/2), (u_{k j} x)²)`. -/
lemma boxMode_inner_self (s : ℝ) (hs : 0 < s) (k : Fin 3 → ℕ) :
    inner ℝ (boxModeLp s k) (boxModeLp s k)
      = ∏ j : Fin 3,
          (∫ x in (-s / 2)..(s / 2), (boxNeumann s (k j) x) ^ 2) := by
  have hf := boxInner_eq_prod_interval hs k k
  rw [hf]
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hpt : (fun x : ℝ => boxNeumann s (k j) x * boxNeumann s (k j) x)
      = fun x : ℝ => (boxNeumann s (k j) x) ^ 2 := by
    funext x
    rw [← sq]
  rw [hpt]

open scoped intervalIntegral in
/-- **per-coordinate value**: for `1 ≤ m`, `∫ x in (-s/2)..(s/2), u_m² = s/2`
(bridge to `boxNeumann_sq_norm`'s `-(s/2)` spelling). -/
lemma boxNeumann_sq_integral_ge_one {s : ℝ} (hs : 0 < s) {m : ℕ} (hm : 1 ≤ m) :
    (∫ x in (-s / 2)..(s / 2), (boxNeumann s m x) ^ 2) = s / 2 := by
  rw [show (-s / 2) = (-(s / 2)) by ring]
  exact boxNeumann_sq_norm hs hm

open scoped intervalIntegral in
/-- **per-coordinate value**: for `m = 0`, `∫ x in (-s/2)..(s/2), u₀² = s`. -/
lemma boxNeumann_sq_integral_zero {s : ℝ} (hs : 0 < s) :
    (∫ x in (-s / 2)..(s / 2), (boxNeumann s 0 x) ^ 2) = s := by
  rw [show (-s / 2) = (-(s / 2)) by ring]
  exact boxNeumann_sq_norm_zero hs



/-- if `x * x = y` and `x ≠ 0`, then `x⁻¹ * (x⁻¹ * y) = 1`. -/
lemma inv_mul_self_mul_eq_one {x y : ℝ} (hx : x ≠ 0) (hy : x * x = y) :
    x⁻¹ * (x⁻¹ * y) = 1 := by
  rw [← hy]
  field_simp [hx]

/-- per-coordinate squared-norm factor: `s` for the constant mode `0`,
`s/2` for `m ≥ 1`. -/
def coordSqNorm (s : ℝ) (m : ℕ) : ℝ := if m = 0 then s else s / 2

lemma coordSqNorm_pos {s : ℝ} (hs : 0 < s) (m : ℕ) : 0 < coordSqNorm s m := by
  dsimp [coordSqNorm]
  by_cases hm : m = 0
  · rw [if_pos hm]
    exact hs
  · rw [if_neg hm]
    positivity

open scoped intervalIntegral in
/-- **mode squared norm = product of the per-coordinate norms**:
`inner (mode_k)(mode_k) = ∏_j coordSqNorm s (k j)`. -/
lemma boxMode_inner_self_coord {s : ℝ} (hs : 0 < s) (k : Fin 3 → ℕ) :
    inner ℝ (boxModeLp s k) (boxModeLp s k) = ∏ j : Fin 3, coordSqNorm s (k j) := by
  rw [boxMode_inner_self s hs k]
  refine Finset.prod_congr rfl ?_
  intro j hj
  dsimp [coordSqNorm]
  by_cases h0 : k j = 0
  · rw [if_pos h0, h0]
    exact boxNeumann_sq_integral_zero hs
  · rw [if_neg h0]
    have h1 : 1 ≤ k j := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero h0)
    exact boxNeumann_sq_integral_ge_one hs h1

/-- the mode squared norm is positive. -/
lemma boxMode_sqNorm_pos {s : ℝ} (hs : 0 < s) (k : Fin 3 → ℕ) :
    0 < inner ℝ (boxModeLp s k) (boxModeLp s k) := by
  rw [boxMode_inner_self_coord hs k]
  exact Finset.prod_pos (fun j hj => coordSqNorm_pos hs (k j))

/-- the normalised box mode `ê_k` (unit vector of `Lp ℝ 2 (boxVol s)`). -/
def boxModeOrtho (s : ℝ) (hs : 0 < s) (k : Fin 3 → ℕ) : Lp ℝ 2 (boxVol s) :=
  (Real.sqrt (∏ j : Fin 3, coordSqNorm s (k j)))⁻¹ • boxModeLp s k

/-- normalised modes have unit self inner product. -/
lemma boxModeOrtho_inner_self {s : ℝ} (hs : 0 < s) (k : Fin 3 → ℕ) :
    inner ℝ (boxModeOrtho s hs k) (boxModeOrtho s hs k) = 1 := by
  dsimp [boxModeOrtho]
  rw [inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply]
  rw [boxMode_inner_self_coord hs k]
  let Q : ℝ := ∏ j : Fin 3, coordSqNorm s (k j)
  change (Real.sqrt Q)⁻¹ * ((Real.sqrt Q)⁻¹ * Q) = 1
  have hQpos : 0 < Q := by
    dsimp [Q]
    exact Finset.prod_pos (fun j hj => coordSqNorm_pos hs (k j))
  have hQ : 0 ≤ Q := le_of_lt hQpos
  have hsqQ : Real.sqrt Q ≠ 0 := ne_of_gt ((Real.sqrt_pos).2 hQpos)
  have hQQ : Real.sqrt Q * Real.sqrt Q = Q := by
    simpa [pow_two] using (Real.sq_sqrt hQ)
  exact inv_mul_self_mul_eq_one hsqQ hQQ

/-- normalised modes are unit vectors. -/
lemma boxModeOrtho_norm {s : ℝ} (hs : 0 < s) (k : Fin 3 → ℕ) :
    ‖boxModeOrtho s hs k‖ = 1 := by
  have hsq : ‖boxModeOrtho s hs k‖ ^ 2 = 1 := by
    rw [← real_inner_self_eq_norm_sq (boxModeOrtho s hs k)]
    exact boxModeOrtho_inner_self hs k
  rcases (sq_eq_one_iff.mp hsq) with h | h
  · exact h
  · linarith [norm_nonneg (boxModeOrtho s hs k)]

/-- distinct normalised modes are orthogonal. -/
lemma boxModeOrtho_inner_eq_zero_of_ne {s : ℝ} (hs : 0 < s) {k k' : Fin 3 → ℕ}
    (h : k ≠ k') : inner ℝ (boxModeOrtho s hs k) (boxModeOrtho s hs k') = 0 := by
  dsimp [boxModeOrtho]
  rw [inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply]
  rw [boxMode_inner_eq_zero_of_ne hs h]
  ring

/-- the normalised box modes form an orthonormal system. -/
lemma boxModeOrtho_orthonormal {s : ℝ} (hs : 0 < s) : Orthonormal ℝ (boxModeOrtho s hs) := by
  constructor
  · intro k
    exact boxModeOrtho_norm hs k
  · intro k k' hkk'
    exact boxModeOrtho_inner_eq_zero_of_ne hs hkk'

/-- **Bessel for the box modes**: `∑_k |⟨ê_k, f⟩|² ≤ ‖f‖²` for every
`f ∈ L²(acube s)`. -/
lemma boxMode_bessel {s : ℝ} (hs : 0 < s) (f : Lp ℝ 2 (boxVol s)) :
    ∑' k : Fin 3 → ℕ, ‖inner ℝ (boxModeOrtho s hs k) f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  exact Orthonormal.tsum_inner_products_le (𝕜 := ℝ) f
    (hv := boxModeOrtho_orthonormal hs)

end BoseGases
end Submission


