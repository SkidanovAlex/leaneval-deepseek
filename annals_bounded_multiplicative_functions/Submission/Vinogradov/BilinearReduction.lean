/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.GaugeBump


/-!
# Passage from linear to bilinear decoupling (GLYZ §2)

This module starts the formalisation of §2 of Guo–Li–Yung–Zorin-Kranich,
*[A short proof of ℓ² decoupling for the moment curve](https://arxiv.org/abs/1912.09798)*,
the route to BDG Theorem 1.2 recommended in `ROADMAP.lean`.

## The two constants

For `k ≥ 1` let `p_k = k(k+1)` be the critical exponent (`pE k`).  For a complex-valued
function `f` on `E k` we write `lpNorm k p f` for the (extended) `L^p` norm
`eLpNorm f p volume ∈ ℝ≥0∞`.  Working with `ℝ≥0∞`-valued norms is *forced* by the statement
of the decoupling theorem: the tuples `(f_J)` in the paper are only assumed to have
`supp f̂_J ⊆ 𝒰_J`, so the individual `L^{p_k}` norms need not be finite and the inequality is
meant in `[0,∞]`.  (With `ℝ`-valued Bochner integrals the inequality would in fact be
*false*: if some `f_J ∉ L^p` then the right-hand side drops to `0` while the left-hand side
need not.)  This is the single most important convention in this module.

* `DecLin k m C` (GLYZ Definition 1.1): the ℓ²-decoupling inequality at scale `m`, i.e. for
  the `m`-fold partition of `[0,1]` with plates `plate k (1/(2m)) c_j`;
* `DecLinOn k m a s C`: the same inequality for the `m`-fold subdivision of an arbitrary
  interval `[a, a+s]` — the form in which the affine rescaling (GLYZ Lemma 2.3) is used;
* `BilinDec k M C` (GLYZ Definition 2.1): the *symmetric bilinear* constant at scale `1/(4M)`
  for pairs of coarse quarters at distance `≥ 1/4`.

## What is proved here

The affine rescaling **`decLinOn_of_decLin`** (GLYZ Lemma 2.3): the inequality `DecLin k m C`
transfers to *every* interval `[a,a+s]` with the *same* constant `C`.  The proof is the one of
the paper: precompose the frequency datum with `A_I^{-1} = affMap k s a` (that is
`DecouplingClass.isFourierRep_rescale`), which puts `f_J` into the class over
`affMap k s a ⁻¹' 𝒰_J = 𝒰_{J_I}`; the two sides of the inequality then both carry the factor
`|det (affVecLin …)⁻¹|^{1/p}`, which cancels.

## Conventions for the pieces

The piece of index `j : Fin m` is the interval `(j/m, (j+1)/m]` with centre
`pieceCenter m j = (j+1/2)/m`; its plate is `plate k (1/(2m)) (pieceCenter m j)` — the plate
parameter is the **half-length** of the piece, because `Plate.gammaVec_mem_plate` says that
`γ([c-δ, c+δ]) ⊆ plate k δ c`.
-/

noncomputable section
open MeasureTheory Complex Classical Filter
open scoped Real BigOperators Topology RealInnerProductSpace ENNReal NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.style.emptyLine false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Submission.Vinogradov

/-! ## 1. The critical exponent and the `L^p` norm -/

/-- The critical exponent `p_k = k(k+1)` of the Vinogradov system, as an extended exponent. -/
def pE (k : ℕ) : ℝ≥0∞ := ((k * (k + 1) : ℕ) : ℝ≥0)

lemma pE_ne_top (k : ℕ) : pE k ≠ ∞ := ENNReal.coe_ne_top



/-- The extended `L^p` norm of a complex-valued function on `E k`. -/
noncomputable def lpNorm (k : ℕ) (p : ℝ≥0∞) (f : E k → ℂ) : ℝ≥0∞ :=
  eLpNorm f p (volume : Measure (E k))

@[simp] lemma lpNorm_zero (k : ℕ) {p : ℝ≥0∞} : lpNorm k p (fun _ : E k => 0) = 0 := by
  simp [lpNorm]

/-- The `ℓ²` norm of a family of extended nonnegative reals. -/
noncomputable def l2Norm {ι : Type*} [Fintype ι] (a : ι → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ i, a i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-! ## 2. Pieces, plates and the decoupling constants -/

/-- Centre of the `j`-th piece of the `m`-fold partition of `[0,1]`. -/
noncomputable def pieceCenter (m : ℕ) (j : Fin m) : ℝ :=
  (((j : ℕ) : ℝ) + 1 / 2) / m

/-- The frequency plate attached to the `j`-th piece of the `m`-fold partition of `[0,1]`. -/
noncomputable def piecePlate (k m : ℕ) (j : Fin m) : Set (E k) :=
  plate k (1 / (2 * m)) (pieceCenter m j)

/-- **GLYZ Definition 1.1**: the ℓ²-decoupling inequality for the moment curve at scale `m`.
The tuple `f` is indexed by the `m` pieces of `[0,1]` and `f j` is assumed to lie in the class
`𝒞(𝒰_j)` of functions whose Fourier transform is supported in the `j`-th plate. -/
def DecLin (k : ℕ) (m : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ f : Fin m → E k → ℂ,
    (∀ j, IsFourierRep k (piecePlate k m j) (f j)) →
    lpNorm k (pE k) (fun x => ∑ j, f j x) ≤ C * l2Norm (fun j => lpNorm k (pE k) (f j))

/-- Centre of the `j`-th sub-piece of the `a`-th quarter of `[0,1]`, the quarter being
divided into `M` equal pieces. -/
noncomputable def subCenter (M : ℕ) (a : Fin 4) (j : Fin M) : ℝ :=
  ((a : ℕ) : ℝ) / 4 + ((((j : ℕ) : ℝ) + 1 / 2)) / (4 * M)

/-- The frequency plate attached to that sub-piece. -/
noncomputable def subPlate (k M : ℕ) (a : Fin 4) (j : Fin M) : Set (E k) :=
  plate k (1 / (8 * M)) (subCenter M a j)

/-- **GLYZ Definition 2.1**: the symmetric bilinear decoupling constant at scale `1/(4M)`,
in the normalisation in which the first coarse interval is the first quarter of `[0,1]` (the
general pair is reduced to this by the reflection `t ↦ 1 - t`, which preserves the moment
curve's plates).  The second coarse quarter is the `a'`-th one with `a' ≥ 2`, i.e. at distance
`≥ 1/4` from the first. -/
def BilinDec (k M : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ (a' : Fin 4), 2 ≤ (a' : ℕ) →
  ∀ (f f' : Fin M → E k → ℂ),
    (∀ j, IsFourierRep k (subPlate k M 0 j) (f j)) →
    (∀ j, IsFourierRep k (subPlate k M a' j) (f' j)) →
    (∫⁻ x, ((‖(∑ j, f j x)‖₊ : ℝ≥0∞) ^ ((k : ℝ) * ((k : ℝ) + 1) / 2))
        * ((‖(∑ j, f' j x)‖₊ : ℝ≥0∞) ^ ((k : ℝ) * ((k : ℝ) + 1) / 2)))
      ≤ C ^ ((k : ℝ) * ((k : ℝ) + 1))
          * (l2Norm fun j => lpNorm k (pE k) (f j)) ^ ((k : ℝ) * ((k : ℝ) + 1) / 2)
          * (l2Norm fun j => lpNorm k (pE k) (f' j)) ^ ((k : ℝ) * ((k : ℝ) + 1) / 2)

/-! ## 3. Monotonicity -/

lemma DecLin_mono {k m : ℕ} {C C' : ℝ≥0∞} (h : C ≤ C') (hD : DecLin k m C) :
    DecLin k m C' := fun f hf => (hD f hf).trans (mul_le_mul_left h _)

lemma BilinDec_mono {k M : ℕ} {C C' : ℝ≥0∞} (h : C ≤ C') (hD : BilinDec k M C) :
    BilinDec k M C' := by
  intro a' ha' f f' hf hf'
  refine (hD a' ha' f f' hf hf').trans ?_
  refine mul_le_mul_left (mul_le_mul_left
    (ENNReal.rpow_le_rpow h (by positivity)) _) _

/-! ## 4. The class is (a.e.) measurable -/

/-- The represented function is continuous (dominated convergence along the frequency
datum).  In particular every member of the class is a.e.-strongly measurable. -/
lemma IsFourierRep.continuous {k : ℕ} {U : Set (E k)} {f : E k → ℂ}
    (hf : IsFourierRep k U f) : Continuous f := by
  obtain ⟨ι, m, Γ, ν, φ, hν, hφ, hΓ, hmφ, hU, hfd⟩ := hf
  letI : MeasurableSpace ι := m
  haveI : IsFiniteMeasure ν := hν
  rw [show f = repFun k Γ ν φ from funext fun x => (hfd x).trans rfl]
  refine continuous_of_dominated (F := fun (x : E k) (u : ι) => chat k x (Γ u) * φ u)
    (bound := fun u => ‖φ u‖) ?_ ?_ hφ.norm ?_
  · intro x
    exact ((continuous_chat_left k x).measurable.comp hΓ).aestronglyMeasurable |>.mul
      hmφ.aestronglyMeasurable
  · intro x
    filter_upwards with u
    rw [norm_mul, chat_norm, one_mul]
  · filter_upwards with u
    exact (continuous_chat_right k (Γ u)).mul continuous_const

lemma IsFourierRep.aestronglyMeasurable {k : ℕ} {U : Set (E k)} {f : E k → ℂ}
    (hf : IsFourierRep k U f) : AEStronglyMeasurable f volume :=
  hf.continuous.aestronglyMeasurable

/-! ## 5. The determinant of the affine rescaling -/

/-- The affine rescaling map `affVecLin k ρ t₀` is injective for `ρ ≠ 0`. -/
lemma affVecLin_injective (k : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (t₀ : ℝ) :
    Function.Injective (affVecLin k ρ t₀) := by
  intro x y h
  have hzero : affVecLin k ρ t₀ (x - y) = 0 := by rw [map_sub, h, sub_self]
  have h' : ∀ z : E k, ⟪x - y, z⟫ = 0 := by
    intro z
    obtain ⟨w, hw⟩ := (affVecDual_bijective k hρ t₀).2 z
    rw [← hw, ← inner_affVecLin k ρ t₀ (x - y) w, hzero, inner_zero_left]
  exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)).mp (h' (x - y)))

/-- `LinearMap.det (affVecLin k ρ t₀) ≠ 0` for `ρ ≠ 0`. -/
lemma det_affVecLin_ne_zero (k : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (t₀ : ℝ) :
    LinearMap.det (affVecLin k ρ t₀) ≠ 0 := fun h =>
  (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) (LinearMap.ker_eq_bot'.mpr fun x hx =>
    affVecLin_injective k hρ t₀ (by rw [map_zero]; exact hx))

/-- `affMap k ρ t₀` is injective for `ρ ≠ 0`. -/
lemma affMap_injective (k : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (t₀ : ℝ) :
    Function.Injective (affMap k ρ t₀) := by
  intro x y h
  rw [affMap_apply, affMap_apply] at h
  exact (affVecDual_bijective k hρ t₀).1 (add_left_cancel h)

/-- The preimage of a plate centred at `a + (j+1/2)s/M` under `affMap k s a` is the
plate of the `j`-th sub-piece of the standard subdivision. -/
lemma affMap_preimage_piecePlate (k M : ℕ) {a s : ℝ} (hs : s ≠ 0) (j : Fin M) :
    affMap k s a ⁻¹' plate k (s / (2 * M)) (a + (((j : ℕ) : ℝ) + 1 / 2) * s / M)
      = piecePlate k M j := by
  have himg := affMap_image_plate k s a (1 / (2 * M)) (pieceCenter M j)
  have h1 : s / (2 * (M : ℝ)) = s * (1 / (2 * M)) := by ring
  have h2 : a + (((j : ℕ) : ℝ) + 1 / 2) * s / M = s * pieceCenter M j + a := by
    rw [pieceCenter]; ring
  rw [h1, h2, ← himg]
  exact Set.preimage_image_eq _ (affMap_injective k hs a)

/-! ## 6. The change of variables in the extended `L^p` norm -/

/-- Pulling back along an affine rescaling multiplies the extended `L^p` norm by the
`(1/p)`-th power of `|det|⁻¹`; the unimodular phase is irrelevant. -/
lemma eLpNorm_phase_comp_affVecLin (k : ℕ) {p : ℝ≥0∞} (hp : p ≠ ∞)
    {ρ t₀ : ℝ} (hρ : ρ ≠ 0) {g : E k → ℂ} (hg : AEStronglyMeasurable g volume) :
    lpNorm k p (fun x => chat k x (gammaVec k t₀) * g (affVecLin k ρ t₀ x))
      = (ENNReal.ofReal |(LinearMap.det (affVecLin k ρ t₀))⁻¹|) ^ (1 / p).toReal
          * lpNorm k p g := by
  have hdet := det_affVecLin_ne_zero k hρ t₀
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (E k)) hdet
  have hae : AEMeasurable (affVecLin k ρ t₀) volume :=
    (LinearMap.continuous_of_finiteDimensional _).measurable.aemeasurable
  have hg' : AEStronglyMeasurable g (Measure.map (affVecLin k ρ t₀) volume) := by
    rw [hmap]
    exact hg.mono_ac Measure.smul_absolutelyContinuous
  have hstrip : eLpNorm (fun x : E k => chat k x (gammaVec k t₀) * g (affVecLin k ρ t₀ x))
        p volume = eLpNorm (fun x : E k => g (affVecLin k ρ t₀ x)) p volume := by
    rw [← eLpNorm_norm (f := fun x : E k => chat k x (gammaVec k t₀) * g (affVecLin k ρ t₀ x)),
      ← eLpNorm_norm (f := fun x : E k => g (affVecLin k ρ t₀ x))]
    exact eLpNorm_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [norm_mul, chat_norm, one_mul])
    all_goals first
      | exact hg'.comp_aemeasurable hae
      | exact (continuous_chat_right k _).aestronglyMeasurable.mul (hg'.comp_aemeasurable hae)
  have h2 : eLpNorm (fun x : E k => g (affVecLin k ρ t₀ x)) p volume
      = eLpNorm g p (Measure.map (affVecLin k ρ t₀) volume) :=
    (eLpNorm_map_measure hg' hae).symm
  rw [lpNorm, lpNorm, hstrip, h2, hmap, eLpNorm_smul_measure_of_ne_top hp]
  rfl
  exact hg

/-! ## 7. The affine rescaling of the decoupling inequality (GLYZ Lemma 2.3) -/

/-- The ℓ²-decoupling inequality for the `M`-fold subdivision of an arbitrary interval
`[a, a+s]`. -/
def DecLinOn (k M : ℕ) (a s : ℝ) (C : ℝ≥0∞) : Prop :=
  ∀ f : Fin M → E k → ℂ,
    (∀ j : Fin M, IsFourierRep k (plate k (s / (2 * M))
      (a + (((j : ℕ) : ℝ) + 1 / 2) * s / M)) (f j)) →
    lpNorm k (pE k) (fun x => ∑ j, f j x) ≤ C * l2Norm (fun j => lpNorm k (pE k) (f j))

lemma DecLinOn_mono {k M : ℕ} {a s : ℝ} {C C' : ℝ≥0∞} (h : C ≤ C')
    (hD : DecLinOn k M a s C) : DecLinOn k M a s C' :=
  fun f hf => (hD f hf).trans (mul_le_mul_left h _)

/-- The `ℓ²` norm of a constant multiple. -/
lemma l2Norm_mul_const {ι : Type*} [Fintype ι] (c : ℝ≥0∞) (a : ι → ℝ≥0∞) :
    l2Norm (fun i => c * a i) = c * l2Norm a := by
  have hsum : (∑ i, (c * a i) ^ (2 : ℝ)) = c ^ (2 : ℝ) * ∑ i, a i ^ (2 : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  rw [l2Norm, l2Norm, hsum,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.rpow_mul,
    show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one]

/-- The rescaling constant `|det M⁻¹|^{1/p}` is positive. -/
lemma rescaleConst_pos {k : ℕ} {p : ℝ≥0∞} {ρ t₀ : ℝ} (hρ : ρ ≠ 0) :
    0 < (ENNReal.ofReal |(LinearMap.det (affVecLin k ρ t₀))⁻¹|) ^ (1 / p).toReal :=
  ENNReal.rpow_pos
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero (det_affVecLin_ne_zero k hρ t₀))))
    ENNReal.ofReal_ne_top

/-- The rescaling constant `|det M⁻¹|^{1/p}` is finite. -/
lemma rescaleConst_ne_top {k : ℕ} {p : ℝ≥0∞} {ρ t₀ : ℝ} (hρ : ρ ≠ 0) :
    (ENNReal.ofReal |(LinearMap.det (affVecLin k ρ t₀))⁻¹|) ^ (1 / p).toReal ≠ ⊤ := by
  intro h
  rw [ENNReal.rpow_eq_top_iff] at h
  rcases h with ⟨h0, _⟩ | ⟨h1, _⟩
  · exact (ENNReal.ofReal_ne_zero_iff.mpr
      (abs_pos.mpr (inv_ne_zero (det_affVecLin_ne_zero k hρ t₀)))) h0
  · exact ENNReal.ofReal_ne_top h1

/-- **GLYZ Lemma 2.3 (affine rescaling)**: the linear decoupling inequality transfers to the
`M`-fold subdivision of an arbitrary interval `[a, a+s]`, with the same constant. -/
theorem decLinOn_of_decLin {k M : ℕ} {C : ℝ≥0∞} (hC : DecLin k M C)
    {a s : ℝ} (hs : 0 < s) : DecLinOn k M a s C := by
  intro f hf
  set c : ℝ≥0∞ := (ENNReal.ofReal |(LinearMap.det (affVecLin k (1 / s) (-a / s)))⁻¹|)
    ^ (1 / pE k).toReal with hc
  have hc0 : 0 < c := by rw [hc]; exact rescaleConst_pos (by positivity)
  have hctop : c ≠ ⊤ := by rw [hc]; exact rescaleConst_ne_top (by positivity)
  -- the rescaled family
  have hrep : ∀ j : Fin M, IsFourierRep k (piecePlate k M j)
      (fun x : E k => chat k x (gammaVec k (-a / s)) * f j (affVecLin k (1 / s) (-a / s) x)) := by
    intro j
    obtain ⟨ι, m, Γ, ν, φ, hν, hφ, hΓ, hmφ, hU, hfrep⟩ := hf j
    letI : MeasurableSpace ι := m
    have hres := isFourierRep_rescale k (ρ := s) hs.ne' a hν hφ hmφ hΓ hU
    have hfeq : rescaleRep k s a Γ ν φ =
        fun x : E k => chat k x (gammaVec k (-a / s)) * f j (affVecLin k (1 / s) (-a / s) x) := by
      funext x
      rw [rescaleRep_eq,
        show repFun k Γ ν φ = f j from funext fun y => ((hfrep y).trans rfl).symm]
      simp only [one_div]
    rw [← hfeq, ← affMap_preimage_piecePlate k M (a := a) (s := s) hs.ne' j]
    exact hres
  -- the norm identities
  have hnorm : ∀ g : E k → ℂ, AEStronglyMeasurable g volume →
      lpNorm k (pE k) (fun x => chat k x (gammaVec k (-a / s))
        * g (affVecLin k (1 / s) (-a / s) x)) = c * lpNorm k (pE k) g := by
    intro g hg
    have h := eLpNorm_phase_comp_affVecLin k (p := pE k) (pE_ne_top k)
      (ρ := 1 / s) (t₀ := -a / s) (by positivity : (1 / s : ℝ) ≠ 0) hg
    rw [h, hc]
  have hsum : lpNorm k (pE k) (fun x => ∑ j : Fin M,
        (chat k x (gammaVec k (-a / s)) * f j (affVecLin k (1 / s) (-a / s) x)))
      = c * lpNorm k (pE k) (fun x => ∑ j, f j x) := by
    have hcont : Continuous (fun x : E k => ∑ j : Fin M, f j x) :=
      continuous_finsetSum _ fun j _ => (hf j).continuous
    have h0 : (fun x : E k => ∑ j : Fin M,
        (chat k x (gammaVec k (-a / s)) * f j (affVecLin k (1 / s) (-a / s) x)))
        = fun x : E k => chat k x (gammaVec k (-a / s))
            * (∑ j, f j (affVecLin k (1 / s) (-a / s) x)) := by
      funext x
      rw [Finset.mul_sum]
    rw [h0]
    exact hnorm (fun x : E k => ∑ j : Fin M, f j x) hcont.aestronglyMeasurable
  have hl2 : l2Norm (fun j => lpNorm k (pE k) (fun x : E k =>
      chat k x (gammaVec k (-a / s)) * f j (affVecLin k (1 / s) (-a / s) x)))
      = c * l2Norm (fun j => lpNorm k (pE k) (f j)) := by
    have hfun : (fun j => lpNorm k (pE k) (fun x : E k =>
        chat k x (gammaVec k (-a / s)) * f j (affVecLin k (1 / s) (-a / s) x)))
        = fun j => c * lpNorm k (pE k) (f j) := by
      funext j
      exact hnorm (f j) (hf j).aestronglyMeasurable
    rw [hfun, l2Norm_mul_const c (fun j => lpNorm k (pE k) (f j))]
  have happly := hC (fun j => fun x : E k =>
    chat k x (gammaVec k (-a / s)) * f j (affVecLin k (1 / s) (-a / s) x)) hrep
  rw [hsum, hl2] at happly
  have h2 : c * lpNorm k (pE k) (fun x => ∑ j, f j x)
      ≤ c * (C * l2Norm (fun j => lpNorm k (pE k) (f j))) := by
    refine happly.trans (le_of_eq ?_)
    rw [← mul_assoc, mul_comm C c, mul_assoc]
  exact (ENNReal.mul_le_mul_iff_right hc0.ne' hctop).mp h2

/-! ## 8. The change of variables for the `ℝ≥0∞`-valued integral -/

/-- The change of variables formula for the extended integral with respect to a linear map of
nonzero determinant. -/
lemma lintegral_comp_linearMap {k : ℕ} {M : E k →ₗ[ℝ] E k} (hM : LinearMap.det M ≠ 0)
    {h : E k → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ x, h (M x)) = ENNReal.ofReal |(LinearMap.det M)⁻¹| * ∫⁻ x, h x := by
  have hmap := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (E k)) hM
  have hMm : Measurable M := (LinearMap.continuous_of_finiteDimensional M).measurable
  rw [← lintegral_map hh hMm, hmap, lintegral_smul_measure]
  rfl

/-- The change of variables for the bilinear integrand `‖F‖^r ‖G‖^r`. -/
lemma lintegral_pair_comp_linearMap {k : ℕ} {M : E k →ₗ[ℝ] E k} (hM : LinearMap.det M ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) {F G : E k → ℂ} (hF : Continuous F) (hG : Continuous G) :
    (∫⁻ x, ((‖F (M x)‖₊ : ℝ≥0∞) ^ r) * ((‖G (M x)‖₊ : ℝ≥0∞) ^ r))
      = ENNReal.ofReal |(LinearMap.det M)⁻¹|
        * ∫⁻ x, ((‖F x‖₊ : ℝ≥0∞) ^ r) * ((‖G x‖₊ : ℝ≥0∞) ^ r) := by
  refine lintegral_comp_linearMap hM
    (h := fun y : E k => (‖F y‖₊ : ℝ≥0∞) ^ r * (‖G y‖₊ : ℝ≥0∞) ^ r) ?_
  fun_prop

/-! ## 9. Rescaling a family in the class -/

lemma affMap_image_subPlate (k M : ℕ) {h a : ℝ} (hM : M ≠ 0) (j : Fin M) (b : Fin 4) :
    affMap k (4 * h) a '' subPlate k M b j
      = plate k (h / (2 * M))
          (a + (b : ℕ) * h + (((j : ℕ) : ℝ) + 1 / 2) * h / M) := by
  rw [subPlate, affMap_image_plate, subCenter]
  have h1 : 4 * h * (1 / (8 * (M : ℝ))) = h / (2 * (M : ℝ)) := by
    field_simp
    ring
  have h2 : 4 * h * (((b : ℕ) : ℝ) / 4 + (((j : ℕ) : ℝ) + 1 / 2) / (4 * (M : ℝ))) + a
      = a + (b : ℕ) * h + (((j : ℕ) : ℝ) + 1 / 2) * h / M := by
    field_simp
    ring
  rw [h1, h2]

lemma rescale_rep_family {k M : ℕ} {h a : ℝ} (hh : 0 < h) (b : Fin 4)
    {f : Fin M → E k → ℂ} (hM : M ≠ 0)
    (hf : ∀ j : Fin M, IsFourierRep k (plate k (h / (2 * M))
      (a + (b : ℕ) * h + (((j : ℕ) : ℝ) + 1 / 2) * h / M)) (f j)) :
    ∃ G : Fin M → E k → ℂ,
      (∀ j, IsFourierRep k (subPlate k M b j) (G j)) ∧
      (∀ j x, G j x = chat k x (gammaVec k (-a / (4 * h)))
        * f j (affVecLin k (1 / (4 * h)) (-a / (4 * h)) x)) ∧
      (∀ j, lpNorm k (pE k) (G j)
        = (ENNReal.ofReal
            |(LinearMap.det (affVecLin k (1 / (4 * h)) (-a / (4 * h))))⁻¹|) ^ (1 / pE k).toReal
          * lpNorm k (pE k) (f j)) ∧
      (∀ x, (∑ j, G j x) = chat k x (gammaVec k (-a / (4 * h)))
        * (∑ j, f j (affVecLin k (1 / (4 * h)) (-a / (4 * h)) x))) := by
  classical
  have h4h : (4 * h) ≠ 0 := by positivity
  have hunit : (1 / (4 * h)) ≠ 0 := by positivity
  have hf' := hf
  choose ι ms Γ ν φ hdat using hf
  set F : Fin M → E k → ℂ := fun j x => chat k x (gammaVec k (-a / (4 * h)))
    * f j (affVecLin k (1 / (4 * h)) (-a / (4 * h)) x) with hFdef
  have hfeq : ∀ j, @rescaleRep k (4 * h) a (ι j) (ms j) (Γ j) (ν j) (φ j) = F j := by
    intro j
    letI : MeasurableSpace (ι j) := ms j
    funext x
    rw [rescaleRep_eq]
    simp only [hFdef]
    rw [show repFun k (Γ j) (ν j) (φ j) = f j from
      funext fun y => (((hdat j).2.2.2.2.2 y).trans rfl).symm]
    simp only [one_div]
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro j
    letI : MeasurableSpace (ι j) := ms j
    rw [← hfeq j]
    have hres := isFourierRep_rescale k (ρ := 4 * h) h4h a (hdat j).1 (hdat j).2.1
      (hdat j).2.2.2.1 (hdat j).2.2.1 (hdat j).2.2.2.2.1
    rw [← affMap_image_subPlate k M hM j b, Set.preimage_image_eq _ (affMap_injective k h4h a)]
      at hres
    exact hres
  · intro j x; simp only [hFdef]
  · intro j
    letI : MeasurableSpace (ι j) := ms j
    have hcont : AEStronglyMeasurable (f j) volume :=
      (IsFourierRep.continuous (hf' j)).aestronglyMeasurable
    have h := eLpNorm_phase_comp_affVecLin k (p := pE k) (pE_ne_top k)
      (ρ := 1 / (4 * h)) (t₀ := -a / (4 * h)) hunit hcont
    simp only [hFdef]
    rw [h]
  · intro x
    simp only [hFdef]
    rw [Finset.mul_sum]


/-! ## 10. The bilinear constant on an arbitrary pair of coarse intervals -/

/-- The bilinear decoupling inequality for an arbitrary pair of coarse intervals of common
length `h` at distance `d` (the cases `d = h` and `d = 2h` are the ones occurring in the
Whitney decomposition). -/
def BilinDecOn (k M : ℕ) (h a d : ℝ) (C : ℝ≥0∞) : Prop :=
  ∀ (f f' : Fin M → E k → ℂ),
    (∀ j : Fin M, IsFourierRep k (plate k (h / (2 * M))
      (a + (((j : ℕ) : ℝ) + 1 / 2) * h / M)) (f j)) →
    (∀ j : Fin M, IsFourierRep k (plate k (h / (2 * M))
      (a + h + d + (((j : ℕ) : ℝ) + 1 / 2) * h / M)) (f' j)) →
    (∫⁻ x, ((‖(∑ j, f j x)‖₊ : ℝ≥0∞) ^ ((k : ℝ) * ((k : ℝ) + 1) / 2))
        * ((‖(∑ j, f' j x)‖₊ : ℝ≥0∞) ^ ((k : ℝ) * ((k : ℝ) + 1) / 2)))
      ≤ C ^ ((k : ℝ) * ((k : ℝ) + 1))
          * (l2Norm fun j => lpNorm k (pE k) (f j)) ^ ((k : ℝ) * ((k : ℝ) + 1) / 2)
          * (l2Norm fun j => lpNorm k (pE k) (f' j)) ^ ((k : ℝ) * ((k : ℝ) + 1) / 2)

lemma chat_nnnorm (k : ℕ) (x ξ : E k) : ‖chat k x ξ‖₊ = 1 := by
  rw [← NNReal.coe_inj, NNReal.coe_one, coe_nnnorm, chat_norm]

lemma pE_toReal (k : ℕ) : (pE k).toReal = (k : ℝ) * ((k : ℝ) + 1) := by
  rw [pE, ENNReal.coe_toReal]
  push_cast
  ring

lemma pE_ne_zero {k : ℕ} (hk : 1 ≤ k) : pE k ≠ 0 := by
  rw [pE]
  positivity

/-- The rescaling constant raised to the critical half-power. -/
lemma rescaleConst_rpow_half {k : ℕ} (hk : 1 ≤ k) {ρ t₀ : ℝ} :
    ((ENNReal.ofReal |(LinearMap.det (affVecLin k ρ t₀))⁻¹|) ^ (1 / pE k).toReal)
        ^ ((k : ℝ) * ((k : ℝ) + 1) / 2)
      = (ENNReal.ofReal |(LinearMap.det (affVecLin k ρ t₀))⁻¹|) ^ (1 / 2 : ℝ) := by
  rw [← ENNReal.rpow_mul]
  congr 1
  rw [one_div, ENNReal.toReal_inv, pE_toReal]
  field_simp

/-- **GLYZ Lemma 2.3 for the bilinear constant**: the symmetric bilinear decoupling inequality
for the standard quarters implies the same inequality for an arbitrary pair of coarse
intervals of common length `h` at distance `h` or `2h`. -/
theorem bilinDecOn_of_bilinDec {k M : ℕ} (hk : 1 ≤ k) (hM : M ≠ 0) {C : ℝ≥0∞}
    (hC : BilinDec k M C) {h d : ℝ} (hh : 0 < h) (hd : d = h ∨ d = 2 * h) :
    ∀ a : ℝ, BilinDecOn k M h a d C := by
  intro a
  have key : ∀ b : Fin 4, 2 ≤ (b : ℕ) → (b : ℕ) * h = h + d →
      BilinDecOn k M h a d C := by
    intro b hb hrel f f' hf hf'
    have hf0 : ∀ j : Fin M, IsFourierRep k (plate k (h / (2 * M))
        (a + (0 : Fin 4) * h + (((j : ℕ) : ℝ) + 1 / 2) * h / M)) (f j) := by
      intro j; simpa using hf j
    have hfb : ∀ j : Fin M, IsFourierRep k (plate k (h / (2 * M))
        (a + (b : ℕ) * h + (((j : ℕ) : ℝ) + 1 / 2) * h / M)) (f' j) := by
      intro j; rw [hrel]; simpa [add_assoc] using hf' j
    obtain ⟨G, hGrep, hGval, hGnorm, hGsum⟩ := rescale_rep_family hh 0 hM hf0
    obtain ⟨G', hG'rep, hG'val, hG'norm, hG'sum⟩ := rescale_rep_family hh b hM hfb
    have happly := hC b hb G G' hGrep hG'rep
    set Nm : E k →ₗ[ℝ] E k := affVecLin k (1 / (4 * h)) (-a / (4 * h)) with hNm
    have hNdet : LinearMap.det Nm ≠ 0 := det_affVecLin_ne_zero k (by positivity) _
    set A : ℝ≥0∞ := ENNReal.ofReal |(LinearMap.det Nm)⁻¹| with hA
    have hApos : 0 < A := by
      rw [hA]; exact ENNReal.ofReal_pos.mpr (abs_pos.mpr (inv_ne_zero hNdet))
    have hA0 : A ≠ 0 := ne_of_gt hApos
    have hAtop : A ≠ ⊤ := by rw [hA]; exact ENNReal.ofReal_ne_top
    set c : ℝ≥0∞ := A ^ (1 / pE k).toReal with hc
    have hcA : c = (ENNReal.ofReal
        |(LinearMap.det (affVecLin k (1 / (4 * h)) (-a / (4 * h))))⁻¹|) ^ (1 / pE k).toReal := by
      rw [hc, hA, hNm]
    set P : ℝ := (k : ℝ) * ((k : ℝ) + 1) with hP
    set R : ℝ := (k : ℝ) * ((k : ℝ) + 1) / 2 with hR
    have hcontA : Continuous (fun x : E k => ∑ j, f j x) :=
      continuous_finsetSum _ fun j _ => (hf j).continuous
    have hcontB : Continuous (fun x : E k => ∑ j, f' j x) :=
      continuous_finsetSum _ fun j _ => (hf' j).continuous
    have hr : (0 : ℝ) ≤ R := by
      rw [hR]
      have hk' : (0 : ℝ) < k := by exact_mod_cast hk
      positivity
    -- the left-hand side under the change of variables
    have hLHS : (∫⁻ x, ((‖(∑ j, G j x)‖₊ : ℝ≥0∞) ^ R) * ((‖(∑ j, G' j x)‖₊ : ℝ≥0∞) ^ R))
        = A * ∫⁻ x, ((‖(∑ j, f j x)‖₊ : ℝ≥0∞) ^ R)
            * ((‖(∑ j, f' j x)‖₊ : ℝ≥0∞) ^ R) := by
      rw [show (∫⁻ x, ((‖(∑ j, G j x)‖₊ : ℝ≥0∞) ^ R) * ((‖(∑ j, G' j x)‖₊ : ℝ≥0∞) ^ R))
          = ∫⁻ x, ((‖(∑ j, f j (Nm x))‖₊ : ℝ≥0∞) ^ R)
              * ((‖(∑ j, f' j (Nm x))‖₊ : ℝ≥0∞) ^ R) from
        lintegral_congr fun x => by
          rw [hGsum x, hG'sum x, nnnorm_mul, nnnorm_mul, chat_nnnorm, one_mul, one_mul]]
      rw [lintegral_pair_comp_linearMap hNdet hr hcontA hcontB, hA]
    -- the ℓ² norms of the rescaled families
    have hGl2 : l2Norm (fun j => lpNorm k (pE k) (G j))
        = c * l2Norm (fun j => lpNorm k (pE k) (f j)) := by
      rw [show (fun j => lpNorm k (pE k) (G j)) = fun j => c * lpNorm k (pE k) (f j) from
        funext hGnorm]
      exact l2Norm_mul_const c _
    have hG'l2 : l2Norm (fun j => lpNorm k (pE k) (G' j))
        = c * l2Norm (fun j => lpNorm k (pE k) (f' j)) := by
      rw [show (fun j => lpNorm k (pE k) (G' j)) = fun j => c * lpNorm k (pE k) (f' j) from
        funext hG'norm]
      exact l2Norm_mul_const c _
    have hcR : c ^ R = A ^ (1 / 2 : ℝ) := by
      rw [hcA, hR, ← hA]
      exact rescaleConst_rpow_half hk (ρ := 1 / (4 * h)) (t₀ := -a / (4 * h))
    -- combine
    rw [hLHS, hGl2, hG'l2, ENNReal.mul_rpow_of_nonneg _ _ hr, ENNReal.mul_rpow_of_nonneg _ _ hr,
      hcR] at happly
    have hAA : A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ) = A := by
      rw [← ENNReal.rpow_add _ _ hA0 hAtop]
      norm_num
    have hcombine : C ^ P * (A ^ (1 / 2 : ℝ) * (l2Norm fun j => lpNorm k (pE k) (f j)) ^ R)
          * (A ^ (1 / 2 : ℝ) * (l2Norm fun j => lpNorm k (pE k) (f' j)) ^ R)
        = A * (C ^ P * (l2Norm fun j => lpNorm k (pE k) (f j)) ^ R
          * (l2Norm fun j => lpNorm k (pE k) (f' j)) ^ R) := by
      have step : C ^ P * (A ^ (1 / 2 : ℝ) * (l2Norm fun j => lpNorm k (pE k) (f j)) ^ R)
            * (A ^ (1 / 2 : ℝ) * (l2Norm fun j => lpNorm k (pE k) (f' j)) ^ R)
          = (A ^ (1 / 2 : ℝ) * A ^ (1 / 2 : ℝ))
            * (C ^ P * (l2Norm fun j => lpNorm k (pE k) (f j)) ^ R
              * (l2Norm fun j => lpNorm k (pE k) (f' j)) ^ R) := by
        generalize A ^ (1 / 2 : ℝ) = u
        generalize C ^ P = w
        generalize (l2Norm fun j => lpNorm k (pE k) (f j)) ^ R = X
        generalize (l2Norm fun j => lpNorm k (pE k) (f' j)) ^ R = Y
        ring
      rw [step, hAA]
    rw [hcombine] at happly
    exact (ENNReal.mul_le_mul_iff_right hA0 hAtop).mp happly
  rcases hd with rfl | rfl
  · refine key 2 (by norm_num) ?_
    norm_num
    ring
  · refine key 3 (by norm_num) ?_
    norm_num
    ring

end Submission.Vinogradov
