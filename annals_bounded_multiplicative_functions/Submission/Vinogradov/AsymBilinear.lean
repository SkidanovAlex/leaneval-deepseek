/-
Copyright: the formalization team of the Vinogradov mean value theorem project.
-/
import Submission.Vinogradov.LinearFromBilinear

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The asymmetric bilinear decoupling constants (GLYZ §3.1)

This module sets up the **asymmetric bilinear decoupling constants** `B_{l,a,b}(δ)` of
Definition 3.1 of Guo–Li–Yung–Zorin-Kranich, *A short proof of ℓ² decoupling for the moment
curve* (arXiv:1912.09798), in the dyadic-level parametrisation that is convenient for
formalisation:

* `pkExp k = k(k+1)` is the critical exponent `p_k` of the `k`-dimensional moment curve;
* a *coarse* interval is a dyadic piece of level `m`, i.e. the block `blk N m q` of the level-`N`
  pieces (`q : Fin (2^m)`), and the fine pieces are the level-`N` pieces themselves.  The
  paper's `I ∈ P(δ^a)` corresponds to `m = aN`; the hypothesis
  `a ≤ (k-l+1)b/l` of Lemma 3.8 then becomes the *integer* inequality
  `l * m ≤ (k - l + 1) * m'`, with the rounding absorbed by the `δ^{-ε}` losses of §4;
* `convPow k r g Ψ` is the convolution `(|g|^r ∗ Ψ)(x) = ∫⁻ y, ‖g (x-y)‖₊^r * Ψ y`, which is the
  object appearing on the left-hand side of Definition 3.1;
* `AsymDec k l N m m' C` is the assertion that the asymmetric bilinear inequality holds with
  constant `C`, for all pairs `(I, I')` of coarse intervals at distance `≥ 1/4` and all bumps
  `Ψ`, `Ψ'` adapted to their polar plates.

The two analytic inputs already available are the **uncertainty principle**
(`DecouplingClass.IsFourierRep.uncertainty` + `GaugeBump.exists_plate_gauge_bump`) and the
**transversality** of the moment curve (commons `Analysis.MomentCurve.transversality_det`).
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

/-! ## 1. Exponents and the convolved power -/

/-- The critical exponent `p_k = k(k+1)` of the `k`-dimensional moment curve, as a real. -/
def pkExp (k : ℕ) : ℝ := (k : ℝ) * ((k : ℝ) + 1)

/-- The exponent `p_l = l(l+1)` attached to the lower degree `l`. -/
def plExp (l : ℕ) : ℝ := (l : ℝ) * ((l : ℝ) + 1)

lemma pkExp_eq (k : ℕ) : pkExp k = 2 * rExp k := by
  rw [pkExp, rExp]; ring

lemma plExp_nonneg (l : ℕ) : 0 ≤ plExp l := by
  rw [plExp]; positivity

lemma pkExp_nonneg (k : ℕ) : 0 ≤ pkExp k := by
  rw [pkExp]; positivity

lemma pkExp_sub_plExp_nonneg {l k : ℕ} (hl : l ≤ k) : 0 ≤ pkExp k - plExp l := by
  have h : pkExp k - plExp l = ((k:ℝ) - l) * ((k:ℝ) + l + 1) := by
    rw [pkExp, plExp]; ring
  rw [h]
  have h1 : (l:ℝ) ≤ k := by exact_mod_cast hl
  exact mul_nonneg (by linarith) (by positivity)

/-- `(|g|^r ∗ Ψ)(x) = ∫⁻ y, ‖g (x-y)‖₊^r * Ψ y`, the convolved power of Definition 3.1. -/
noncomputable def convPow (k : ℕ) (r : ℝ) (g : E k → ℂ) (Ψ : E k → ℝ≥0∞) (x : E k) : ℝ≥0∞ :=
  ∫⁻ y, ((‖g (x - y)‖₊ : ℝ≥0∞) ^ r) * Ψ y

/-- The level-`m` block with index `q`, as a subset of the level-`N` pieces. -/
def blkFin (N m q : ℕ) : Finset (Fin (2 ^ N)) :=
  Finset.univ.filter (fun i => (i : ℕ) / 2 ^ (N - m) = q)

lemma mem_blkFin {N m q : ℕ} {i : Fin (2 ^ N)} :
    i ∈ blkFin N m q ↔ (i : ℕ) / 2 ^ (N - m) = q := by
  simp [blkFin]

/-- The same block seen as a set of naturals. -/
lemma sum_blkFin_eq {N m q : ℕ} {α : Type*} [AddCommMonoid α] (G : ℕ → α) :
    ∑ i ∈ blkFin N m q, G (i : ℕ) = ∑ i ∈ blk N m q, G i := by
  refine Finset.sum_bij (fun (a : Fin (2 ^ N)) _ => (a : ℕ)) ?_ ?_ ?_ ?_
  · intro a ha
    exact mem_blk.mpr ⟨a.isLt, mem_blkFin.mp ha⟩
  · intro a1 ha1 a2 ha2 heq
    exact Fin.ext heq
  · intro b hb
    exact ⟨⟨b, (mem_blk.mp hb).1⟩, mem_blkFin.mpr (mem_blk.mp hb).2, rfl⟩
  · intro a ha
    rfl

lemma l2Of_blkFin_eq {N m q : ℕ} (C : ℕ → ℝ≥0∞) :
    l2Of (blkFin N m q) (fun i : Fin (2 ^ N) => C (i : ℕ)) = l2Of (blk N m q) C := by
  rw [l2Of, l2Of, sqSum, sqSum, sum_blkFin_eq (fun i => C i ^ (2:ℝ))]

@[simp] lemma convPow_zero (k : ℕ) (r : ℝ) (g : E k → ℂ) (x : E k) :
    convPow k r g (fun _ => 0) x = 0 := by
  simp only [convPow, mul_zero, lintegral_zero]

lemma convPow_mono (k : ℕ) (r : ℝ) (g : E k → ℂ) {Ψ Ψ' : E k → ℝ≥0∞} (h : Ψ ≤ Ψ')
    (x : E k) : convPow k r g Ψ x ≤ convPow k r g Ψ' x :=
  lintegral_mono fun y => mul_le_mul' le_rfl (h y)

/-! ## 2. The canonical gauge bumps of a dyadic plate -/

/-- The fixed dimensional exponent used for the gauge bumps: `A = p_k + k + 1`, which satisfies
`A > k` and `A ≥ k(k+1)/2` for every `k ≥ 1`. -/
def gaugeExp (k : ℕ) : ℝ := pkExp k + (k : ℝ) + 1

lemma gaugeExp_gt {k : ℕ} (hk : 1 ≤ k) : (k : ℝ) < gaugeExp k := by
  rw [gaugeExp, pkExp]
  have : (1:ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

lemma gaugeExp_ge {k : ℕ} (hk : 1 ≤ k) : (k : ℝ) * ((k : ℝ) + 1) / 2 ≤ gaugeExp k := by
  rw [gaugeExp, pkExp]
  have : (0:ℝ) ≤ k := by positivity
  nlinarith

/-- The amplitude constant of the anisotropic bump. -/
noncomputable def gaugeAmp (k : ℕ) (hk : 1 ≤ k) : ℝ :=
  Classical.choose (exists_bump_at_one k hk (gaugeExp k) (gaugeExp_gt hk))

/-- The anisotropic bump itself. -/
noncomputable def gaugePsi (k : ℕ) (hk : 1 ≤ k) : E k → ℂ :=
  Classical.choose (Classical.choose_spec
    (exists_bump_at_one k hk (gaugeExp k) (gaugeExp_gt hk))).2

lemma gaugeAmp_pos (k : ℕ) (hk : 1 ≤ k) : 0 < gaugeAmp k hk :=
  (Classical.choose_spec (exists_bump_at_one k hk (gaugeExp k) (gaugeExp_gt hk))).1

lemma gaugePsi_int (k : ℕ) (hk : 1 ≤ k) : Integrable (gaugePsi k hk) :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_bump_at_one k hk (gaugeExp k) (gaugeExp_gt hk))).2).1

lemma gaugePsi_hat (k : ℕ) (hk : 1 ≤ k) :
    ∀ ξ : E k, (∀ i : Fin k, |ξ i| ≤ 1) → (∫ z, gaugePsi k hk z * chat k (-z) ξ) = 1 :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_bump_at_one k hk (gaugeExp k) (gaugeExp_gt hk))).2).2.1

lemma gaugePsi_decay (k : ℕ) (hk : 1 ≤ k) (x : E k) :
    ‖gaugePsi k hk x‖ ≤ gaugeAmp k hk * (max 1 (gauge k hk x)) ^ (-(gaugeExp k)) :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_bump_at_one k hk (gaugeExp k) (gaugeExp_gt hk))).2).2.2.1 x

lemma gaugePsi_L1 (k : ℕ) (hk : 1 ≤ k) :
    (∫ x, ‖gaugePsi k hk x‖) ≤ gaugeAmp k hk :=
  (Classical.choose_spec (Classical.choose_spec
    (exists_bump_at_one k hk (gaugeExp k) (gaugeExp_gt hk))).2).2.2.2

/-- The gauge bump of the polar plate of `plate k δ c`, as a complex function. -/
noncomputable def platePsi (k : ℕ) (hk : 1 ≤ k) (δ c : ℝ) : E k → ℂ :=
  psiPlate k δ c (gaugePsi k hk)

/-- The gauge bump of the polar plate of `plate k δ c`, as an `ℝ≥0∞`-valued weight. -/
noncomputable def platePhi (k : ℕ) (hk : 1 ≤ k) (δ c : ℝ) : E k → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) x)

lemma platePhi_apply (k : ℕ) (hk : 1 ≤ k) (δ c : ℝ) (x : E k) :
    platePhi k hk δ c x
      = ENNReal.ofReal (phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) x) := rfl

/-- The gauge bump of a plate has Fourier transform `1` on the plate. -/
lemma platePsi_hat (k : ℕ) (hk : 1 ≤ k) {δ c : ℝ} (hδ : 0 < δ) {ξ : E k}
    (hξ : ξ ∈ plate k δ c) : (∫ y, platePsi k hk δ c y * chat k (-y) ξ) = 1 :=
  psiPlate_hat_eq_one k δ c hδ (gaugePsi_int k hk) (gaugePsi_hat k hk) hξ

/-- The modulus of the plate bump is dominated by the polar bump. -/
lemma norm_platePsi_le (k : ℕ) (hk : 1 ≤ k) (δ c : ℝ) (x : E k) :
    ‖platePsi k hk δ c x‖ ≤ phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) x := by
  show ‖psiPlate k δ c (gaugePsi k hk) x‖ ≤ phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) x
  rw [norm_psiPlate, phiPlate]
  have h := gaugePsi_decay k hk (plateGaugeLin k δ c x)
  calc |LinearMap.det (plateGaugeLin k δ c)| * ‖gaugePsi k hk (plateGaugeLin k δ c x)‖
      ≤ |LinearMap.det (plateGaugeLin k δ c)|
          * (gaugeAmp k hk * (max 1 (gauge k hk (plateGaugeLin k δ c x))) ^ (-(gaugeExp k))) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = gaugeAmp k hk * |LinearMap.det (plateGaugeLin k δ c)|
          * (max 1 (gauge k hk (plateGaugeLin k δ c x))) ^ (-(gaugeExp k)) := by ring

/-- The polar bump of a plate is integrable. -/
lemma platePhi_integrable (k : ℕ) (hk : 1 ≤ k) {δ : ℝ} (hδ : δ ≠ 0) (c : ℝ) :
    Integrable (phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk)) :=
  (integrable_comp_plateGaugeLin hδ c
    (integrable_gauge_rpow k hk (gaugeExp_gt hk))).const_mul _

lemma platePhi_nonneg (k : ℕ) (hk : 1 ≤ k) (δ c : ℝ) (x : E k) :
    0 ≤ phiPlate k hk δ c (gaugeExp k) (gaugeAmp k hk) x :=
  phiPlate_nonneg k hk δ c (gaugeExp k) (gaugeAmp k hk) (gaugeAmp_pos k hk).le x

/-! ## 3. The asymmetric bilinear constant -/

/-- The distance condition `dist(I,I') ≥ 1/4` for the coarse intervals of levels `m`, `m'`. -/
def sepLevel (m m' : ℕ) (q : Fin (2 ^ m)) (q' : Fin (2 ^ m')) : Prop :=
  1 / 4 ≤ |pieceCenter (2 ^ m) q - pieceCenter (2 ^ m') q'|
    - 1 / (2:ℝ) ^ (m + 1) - 1 / (2:ℝ) ^ (m' + 1)

/-- The half-width of a plate of level `m`. -/
noncomputable def plateHalf (m : ℕ) : ℝ := 1 / (2:ℝ) ^ (m + 1)

lemma plateHalf_eq (m : ℕ) : plateHalf m = 1 / (2 * ((2 ^ m : ℕ) : ℝ)) := by
  rw [plateHalf, pow_succ]
  push_cast
  ring

/-- The plate of a level-`m` dyadic piece. -/
lemma piecePlate_eq (k m : ℕ) (q : Fin (2 ^ m)) :
    piecePlate k (2 ^ m) q = plate k (plateHalf m) (pieceCenter (2 ^ m) q) := by
  rw [piecePlate, plateHalf_eq]

/-- **GLYZ Definition 3.1** in dyadic-level form: the asymmetric bilinear decoupling inequality
with parameter `l`, coarse levels `m` and `m'` and fine level `N`. -/
def AsymDec (k : ℕ) (hk : 1 ≤ k) (l N m m' : ℕ) (C : ℝ≥0∞) : Prop :=
  ∀ (q : Fin (2 ^ m)) (q' : Fin (2 ^ m')), sepLevel m m' q q' →
  ∀ (f : Fin (2 ^ N) → E k → ℂ),
    (∀ i, IsFourierRep k (piecePlate k (2 ^ N) i) (f i)) →
    (∫⁻ x, convPow k (plExp l) (fun x => ∑ i ∈ blkFin N m q, f i x)
          (platePhi k hk (plateHalf m) (pieceCenter (2 ^ m) q)) x
        * convPow k (pkExp k - plExp l) (fun x => ∑ i ∈ blkFin N m' q', f i x)
          (platePhi k hk (plateHalf m') (pieceCenter (2 ^ m') q')) x)
      ≤ C ^ (pkExp k)
          * (l2Of (blkFin N m q) (fun i => lpNorm k (pE k) (f i))) ^ (plExp l)
          * (l2Of (blkFin N m' q') (fun i => lpNorm k (pE k) (f i))) ^ (pkExp k - plExp l)

lemma AsymDec_mono {k : ℕ} {hk : 1 ≤ k} {l N m m' : ℕ} {C C' : ℝ≥0∞}
    (h : C ≤ C') (hD : AsymDec k hk l N m m' C) : AsymDec k hk l N m m' C' := by
  intro q q' hsep f hf
  refine (hD q q' hsep f hf).trans ?_
  refine mul_le_mul' (mul_le_mul' (ENNReal.rpow_le_rpow h (pkExp_nonneg k)) le_rfl) le_rfl

end Submission.Vinogradov
