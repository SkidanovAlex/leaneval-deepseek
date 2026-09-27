import Mathlib
import Submission.Mostow.Interfaces

/-!
# Bieberbach's first theorem (area `Bb`)

An elementary proof, following P. Buser, *A geometric proof of Bieberbach's theorems on
crystallographic groups*, Enseign. Math. 31 (1985), 137--145.

Every isometry of Euclidean space is affine (Mazur-Ulam): `ρ g x = A_g x + b_g` with `A_g`
orthogonal.  Writing `m(A) = ‖A - 1‖`, the proof shows that no element of a cocompact,
properly discontinuous group of isometries has `0 < m(A_g) < 1/2`; consequently the elements
with `A_g = 1` (pure translations) form a finite index subgroup, and by a pigeonhole argument
(following Buser's ``mini Bieberbach'' lemma) their translation vectors span.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

set_option maxHeartbeats 4000000

noncomputable section

variable {m : ℕ} {G : Type*} [Group G]


/-! ## Plan for Bieberbach's key lemma

The target is

`keyLemma : mOf (linPart ρ g) < 1/2 → linPart ρ g = 1`

for `ρ` a properly discontinuous (`hpd`) and cocompact (`hcoc`) action, *given* Buser's
"mini Bieberbach" lemma `hmini` (proved in this file as `miniLemma`):

`hmini : ∀ u, ‖u‖ = 1 → ∀ ε δ > 0, ∃ g t, 1 ≤ t ∧ mOf (linPart ρ g) ≤ ε ∧ ‖trPart ρ g + t • u‖ ≤ δ t`.

Sketch of the argument (Buser 1985).  Suppose some `g` has `0 < mOf (linPart ρ g) < 1/2`, and
let `α` minimise `‖trPart ρ α‖` over `F0 = {k | 0 < mOf (linPart ρ k) < 1/2}`
(the minimiser exists by `exists_argmin`, using `finite_of_trPart_le`).  Put `A = linPart ρ α`,
`a = trPart ρ α` and `Es = fixSub A` (the fixed subspace, see `mem_fixSub`); `bndFixPerp` gives
`c > 0` with `c‖x‖ ≤ ‖A x - x‖` for `x ∈ Esᗮ`.

Choose a unit vector `u ∈ Esᗮ` and apply `hmini` with a small `eps` (take
`eps = min (c/100) (1/100)`) and `δ = 1/4`; obtain `β` with `b := trPart ρ β` satisfying
`b = -t u + w`, `‖w‖ ≤ t/4`, `t ≥ 1`, and `mOf (linPart ρ β) ≤ eps`.

Let `F = {k | trPart ρ k ≠ 0 ∧ mOf (linPart ρ k) ≤ eps ∧ ‖Es.starProjection (trPart ρ k)‖ <
‖trPart ρ k - Es.starProjection (trPart ρ k)‖}` (note `β ∈ F`), and let `β₀` minimise
`‖trPart ρ β₀‖` on `F` (`exists_argmin` again).  Put `B = linPart ρ β₀`, `b₀ = trPart ρ β₀`,
`γ = α β₀ α⁻¹ β₀⁻¹`, `R = linPart ρ γ = A B A⁻¹ B⁻¹` (use `linPart_mul`, `linPart_inv`) and
`cv = trPart ρ γ`; `trPart_commutator` gives `cv = (A b₀ - R b₀) + (a - A (B (A⁻¹ a)))`, and
`mOf_commutator` gives `mOf R ≤ 2 mOf A mOf B ≤ mOf B ≤ eps`.

Then `r := (b₀ - R b₀) + (a - A (B (A⁻¹ a)))` satisfies `‖r‖ ≤ 2 mOf B ‖b₀‖` (either `B = 1`,
so that `R = 1` and `r = 0`, or `mOf B > 0` and then `β₀ ∈ F0`, so `‖a‖ ≤ ‖b₀‖`).  Writing
`q = b₀ - Es.starProjection b₀` and using `A b₀ - b₀ = A q - q` (as `A` fixes `Es` and preserves
`Esᗮ`) one gets, with `norm_db`/`norm_sq_eq_add_starProjection`,
`‖Es.starProjection (trPart ρ γ)‖ ≤ (c/50)‖b₀‖` (Pythagoras) and
`c‖b₀‖/2 ≤ ‖trPart ρ γ - Es.starProjection (trPart ρ γ)‖`; hence `γ ∈ F`, and finally
`‖trPart ρ γ‖ ≤ mOf A ‖b₀‖ + 2 eps ‖b₀‖ < ‖b₀‖`, contradicting the minimality of `β₀`.
-/

/-! ## The affine decomposition of an isometry of Euclidean space -/

/-- The linear part of the isometry `ρ g`. -/
def linPart (ρ : G →* (E m ≃ᵢ E m)) (g : G) : E m ≃ₗᵢ[ℝ] E m :=
  (ρ g).toRealLinearIsometryEquiv

/-- The translation part of `ρ g`, i.e. the image of the origin. -/
def trPart (ρ : G →* (E m ≃ᵢ E m)) (g : G) : E m := ρ g 0

@[simp] lemma linPart_zero (ρ : G →* (E m ≃ᵢ E m)) (g : G) : linPart ρ g 0 = 0 := by
  rw [linPart, IsometryEquiv.toRealLinearIsometryEquiv_apply]; simp

lemma apply_eq (ρ : G →* (E m ≃ᵢ E m)) (g : G) (x : E m) :
    ρ g x = linPart ρ g x + trPart ρ g := by
  rw [linPart, trPart, IsometryEquiv.toRealLinearIsometryEquiv_apply]; abel

lemma trPart_mul (ρ : G →* (E m ≃ᵢ E m)) (a b : G) :
    trPart ρ (a * b) = linPart ρ a (trPart ρ b) + trPart ρ a := by
  rw [trPart, map_mul, IsometryEquiv.mul_apply, trPart, apply_eq]

lemma linPart_mul (ρ : G →* (E m ≃ᵢ E m)) (a b : G) :
    linPart ρ (a * b) = linPart ρ a * linPart ρ b := by
  apply LinearIsometryEquiv.ext
  intro x
  rw [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply]
  have h := apply_eq ρ (a*b) x
  rw [map_mul, IsometryEquiv.mul_apply, apply_eq ρ b x, apply_eq ρ a, map_add, trPart_mul] at h
  rw [add_assoc] at h
  exact (add_right_cancel h).symm

@[simp] lemma trPart_one (ρ : G →* (E m ≃ᵢ E m)) : trPart ρ 1 = 0 := by
  rw [trPart, map_one]; rfl

@[simp] lemma linPart_one (ρ : G →* (E m ≃ᵢ E m)) : linPart ρ 1 = 1 := by
  apply LinearIsometryEquiv.ext
  intro x
  have h := apply_eq ρ 1 x
  rw [map_one] at h
  simpa using h.symm

lemma linPart_inv (ρ : G →* (E m ≃ᵢ E m)) (g : G) : linPart ρ g⁻¹ = (linPart ρ g)⁻¹ := by
  have h := linPart_mul ρ g g⁻¹
  rw [mul_inv_cancel, linPart_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

lemma trPart_inv (ρ : G →* (E m ≃ᵢ E m)) (g : G) :
    trPart ρ g⁻¹ = - (linPart ρ g⁻¹) (trPart ρ g) := by
  have h := trPart_mul ρ g g⁻¹
  rw [mul_inv_cancel, trPart_one] at h
  have h2 : (linPart ρ g) (trPart ρ g⁻¹) = - trPart ρ g :=
    eq_neg_of_add_eq_zero_left h.symm
  have h3 := congrArg (linPart ρ g⁻¹) h2
  rw [map_neg] at h3
  have h4 : (linPart ρ g⁻¹) ((linPart ρ g) (trPart ρ g⁻¹)) = trPart ρ g⁻¹ := by
    rw [linPart_inv]; simp
  rw [h4] at h3
  exact h3

/-! ## The linear part as an operator, and the rotation displacement `mOf` -/

/-- The linear part of `ρ g` viewed as a continuous linear map. -/
def opOf (A : E m ≃ₗᵢ[ℝ] E m) : E m →L[ℝ] E m :=
  (A.toContinuousLinearEquiv : E m →L[ℝ] E m)

/-- The `rotation displacement` of `A`: `mOf A = ‖A - 1‖` (operator norm). -/
def mOf (A : E m ≃ₗᵢ[ℝ] E m) : ℝ := ‖opOf A - 1‖

lemma opOf_one : opOf (1 : E m ≃ₗᵢ[ℝ] E m) = 1 := by ext x; simp [opOf]

lemma opOf_mul (A B : E m ≃ₗᵢ[ℝ] E m) : opOf (A * B) = opOf A * opOf B := by
  ext x : 1; simp [opOf, LinearIsometryEquiv.mul_def]

lemma opOf_inv_mul (A : E m ≃ₗᵢ[ℝ] E m) : opOf A⁻¹ * opOf A = 1 := by
  ext x : 1; change (A⁻¹) (A x) = x; simp

lemma opOf_mul_inv (A : E m ≃ₗᵢ[ℝ] E m) : opOf A * opOf A⁻¹ = 1 := by
  ext x : 1; change A (A⁻¹ x) = x; simp

lemma norm_opOf_le_one (A : E m ≃ₗᵢ[ℝ] E m) : ‖opOf A‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  simp [opOf, A.norm_map]

lemma mOf_nonneg (A : E m ≃ₗᵢ[ℝ] E m) : 0 ≤ mOf A := norm_nonneg _

@[simp] lemma mOf_one : mOf (1 : E m ≃ₗᵢ[ℝ] E m) = 0 := by
  rw [mOf, opOf_one, sub_self, norm_zero]

lemma mOf_apply (A : E m ≃ₗᵢ[ℝ] E m) (x : E m) : ‖A x - x‖ ≤ mOf A * ‖x‖ := by
  have h : (opOf A - 1) x = A x - x := by simp [opOf]
  rw [← h]; simpa [mOf] using (opOf A - 1).le_opNorm x

lemma mOf_mul_inv_le (A B : E m ≃ₗᵢ[ℝ] E m) : mOf (A * B⁻¹) ≤ ‖opOf A - opOf B‖ := by
  have h : opOf (A * B⁻¹) - 1 = (opOf A - opOf B) * opOf B⁻¹ := by
    rw [opOf_mul, ← opOf_mul_inv B, ← sub_mul]
  change ‖opOf (A * B⁻¹) - 1‖ ≤ ‖opOf A - opOf B‖
  rw [h]
  calc ‖(opOf A - opOf B) * opOf B⁻¹‖ ≤ ‖opOf A - opOf B‖ * ‖opOf B⁻¹‖ := norm_mul_le _ _
    _ ≤ ‖opOf A - opOf B‖ * 1 := by gcongr; exact norm_opOf_le_one _
    _ = ‖opOf A - opOf B‖ := mul_one _

lemma mOf_sub_le (A B : E m ≃ₗᵢ[ℝ] E m) : ‖opOf A - opOf B‖ ≤ mOf A + mOf B := by
  calc ‖opOf A - opOf B‖ = ‖(opOf A - 1) - (opOf B - 1)‖ := by abel
    _ ≤ ‖opOf A - 1‖ + ‖opOf B - 1‖ := norm_sub_le _ _
    _ = mOf A + mOf B := rfl

/-- Buser's commutator estimate: `m([A,B]) ≤ 2 m(A) m(B)`. -/
lemma mOf_commutator (A B : E m ≃ₗᵢ[ℝ] E m) :
    mOf (A * B * A⁻¹ * B⁻¹) ≤ 2 * mOf A * mOf B := by
  have hmul : opOf (A * B * A⁻¹ * B⁻¹) = opOf A * opOf B * opOf A⁻¹ * opOf B⁻¹ := by
    rw [opOf_mul, opOf_mul, opOf_mul]
  have hid : opOf A * opOf B * opOf A⁻¹ * opOf B⁻¹ - 1
      = (opOf A * opOf B - opOf B * opOf A) * (opOf A⁻¹ * opOf B⁻¹) := by
    rw [sub_mul]
    have h4 : (opOf B * opOf A) * (opOf A⁻¹ * opOf B⁻¹) = 1 := by
      rw [← mul_assoc, mul_assoc (opOf B) (opOf A) (opOf A⁻¹), opOf_mul_inv, mul_one,
        opOf_mul_inv]
    rw [h4]; rfl
  have h1 : ‖opOf A * opOf B - opOf B * opOf A‖ ≤ 2 * (mOf A * mOf B) := by
    have he : opOf A * opOf B - opOf B * opOf A
        = (opOf A - 1) * (opOf B - 1) - (opOf B - 1) * (opOf A - 1) := by
      rw [sub_mul, mul_sub, one_mul, mul_one, sub_mul, mul_sub, one_mul, mul_one]; abel
    rw [he]
    calc ‖(opOf A - 1) * (opOf B - 1) - (opOf B - 1) * (opOf A - 1)‖
        ≤ ‖(opOf A - 1) * (opOf B - 1)‖ + ‖(opOf B - 1) * (opOf A - 1)‖ := norm_sub_le _ _
      _ ≤ ‖opOf A - 1‖ * ‖opOf B - 1‖ + ‖opOf B - 1‖ * ‖opOf A - 1‖ := by
          gcongr <;> exact norm_mul_le _ _
      _ = 2 * (mOf A * mOf B) := by simp only [mOf]; ring
  have h2 : ‖opOf A⁻¹ * opOf B⁻¹‖ ≤ 1 := by
    calc ‖opOf A⁻¹ * opOf B⁻¹‖ ≤ ‖opOf A⁻¹‖ * ‖opOf B⁻¹‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := by gcongr <;> exact norm_opOf_le_one _
      _ = 1 := by ring
  change ‖opOf (A * B * A⁻¹ * B⁻¹) - 1‖ ≤ 2 * mOf A * mOf B
  rw [hmul, hid]
  calc ‖(opOf A * opOf B - opOf B * opOf A) * (opOf A⁻¹ * opOf B⁻¹)‖
      ≤ ‖opOf A * opOf B - opOf B * opOf A‖ * ‖opOf A⁻¹ * opOf B⁻¹‖ := norm_mul_le _ _
    _ ≤ (2 * (mOf A * mOf B)) * 1 := by
        refine mul_le_mul h1 h2 (norm_nonneg _) ?_
        nlinarith [mOf_nonneg A, mOf_nonneg B]
    _ = 2 * mOf A * mOf B := by ring

/-! ## Finiteness of the set of elements with bounded translation part -/

/-- Proper discontinuity, read on the translation parts. -/
lemma finite_of_trPart_le (ρ : G →* (E m ≃ᵢ E m))
    (hpd : ∀ K : Set (E m), IsCompact K → {g : G | ((ρ g) '' K ∩ K).Nonempty}.Finite)
    (R : ℝ) : {g : G | ‖trPart ρ g‖ ≤ R}.Finite := by
  refine (hpd (Metric.closedBall 0 R) (isCompact_closedBall _ _)).subset ?_
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg ⊢
  have h0 : (0 : E m) ∈ Metric.closedBall 0 R := by
    rw [Metric.mem_closedBall, dist_self]
    exact le_trans (norm_nonneg _) hg
  exact ⟨trPart ρ g, ⟨⟨0, h0, rfl⟩, Metric.mem_closedBall.mpr (by simpa using hg)⟩⟩

/-! ## The cocompactness constant -/

/-- Cocompactness gives a constant `d` such that, in every direction, elements with
almost exactly `-k` times that direction as translation part exist. -/
lemma exists_translation_bound (ρ : G →* (E m ≃ᵢ E m))
    (hcoc : ∃ K : Set (E m), IsCompact K ∧ ∀ x : E m, ∃ g : G, ρ g x ∈ K) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ (u : E m) (hu : ‖u‖ = 1) (k : ℕ),
      ∃ g : G, ‖trPart ρ g + (k : ℝ) • u‖ ≤ d := by
  obtain ⟨K, hK, hKc⟩ := hcoc
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : E m)
  refine ⟨max r 0, le_max_right _ _, fun u hu k => ?_⟩
  obtain ⟨g, hg⟩ := hKc (-(k : ℝ) • u)
  have hgr : ‖ρ g (-(k : ℝ) • u)‖ ≤ r := by
    have h1 := hr hg
    rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h1
  have happ : ρ g (-(k : ℝ) • u) = trPart ρ g - (linPart ρ g) ((k : ℝ) • u) := by
    rw [apply_eq, neg_smul, map_neg]
    abel
  have hmain : (linPart ρ g⁻¹) (ρ g (-(k:ℝ) • u))
      = -(trPart ρ g⁻¹ + (k:ℝ) • u) := by
    rw [happ, map_sub]
    have h4 : (linPart ρ g⁻¹) (trPart ρ g) = -trPart ρ g⁻¹ := by
      rw [trPart_inv]; simp
    have h3 : (linPart ρ g⁻¹) ((linPart ρ g) ((k:ℝ) • u)) = (k:ℝ) • u := by
      rw [linPart_inv]; simp
    rw [h4, h3]
    abel
  have hnorm : ‖trPart ρ g⁻¹ + (k:ℝ) • u‖ = ‖(linPart ρ g⁻¹) (ρ g (-(k:ℝ) • u))‖ := by
    rw [hmain, norm_neg]
  refine ⟨g⁻¹, ?_⟩
  rw [hnorm, LinearIsometryEquiv.norm_map]
  exact le_trans hgr (le_max_left _ _)
/-! ## The fixed subspace of a rotation -/

/-- The fixed subspace of `A`, i.e. the kernel of `A - 1`. -/
def fixSub (A : E m ≃ₗᵢ[ℝ] E m) : Submodule ℝ (E m) :=
  LinearMap.ker ((opOf A - 1 : E m →L[ℝ] E m) : E m →ₗ[ℝ] E m)

lemma opOf_apply (A : E m ≃ₗᵢ[ℝ] E m) (x : E m) : opOf A x = A x := rfl

lemma mem_fixSub {A : E m ≃ₗᵢ[ℝ] E m} {x : E m} : x ∈ fixSub A ↔ A x = x := by
  simp [fixSub, opOf_apply, sub_eq_zero]

lemma mOf_eq_zero_iff {A : E m ≃ₗᵢ[ℝ] E m} : mOf A = 0 ↔ A = 1 := by
  rw [mOf, norm_eq_zero, sub_eq_zero]
  constructor
  · intro h
    apply LinearIsometryEquiv.ext
    intro x
    have hx : opOf A x = (1 : E m →L[ℝ] E m) x := by rw [h]
    simpa [opOf] using hx
  · intro h; rw [h, opOf_one]

lemma norm_opOf_conj_le (A B : E m ≃ₗᵢ[ℝ] E m) :
    ‖opOf (A * B * A⁻¹) - 1‖ ≤ mOf B := by
  have h : opOf (A * B * A⁻¹) - 1 = (opOf A * (opOf B - 1)) * opOf A⁻¹ := by
    rw [opOf_mul, opOf_mul, mul_sub, mul_one, sub_mul, opOf_mul_inv]
  rw [h]
  calc ‖(opOf A * (opOf B - 1)) * opOf A⁻¹‖
      ≤ ‖opOf A * (opOf B - 1)‖ * ‖opOf A⁻¹‖ := norm_mul_le _ _
    _ ≤ (1 * mOf B) * 1 := by
        have h1 : ‖opOf A * (opOf B - 1)‖ ≤ 1 * mOf B := by
          calc ‖opOf A * (opOf B - 1)‖ ≤ ‖opOf A‖ * ‖opOf B - 1‖ := norm_mul_le _ _
            _ ≤ 1 * ‖opOf B - 1‖ := by gcongr; exact norm_opOf_le_one A
            _ = 1 * mOf B := rfl
        exact mul_le_mul h1 (norm_opOf_le_one A⁻¹) (norm_nonneg _)
          (by nlinarith [mOf_nonneg B])
    _ = mOf B := by ring

/-- Pythagoras for the orthogonal projection. -/
lemma norm_sq_eq_add_starProjection (K : Submodule ℝ (E m)) (x : E m) :
    ‖x‖^2 = ‖K.starProjection x‖^2 + ‖x - K.starProjection x‖^2 := by
  have hinner : inner ℝ (K.starProjection x) (x - K.starProjection x) = 0 := by
    have hq : x - K.starProjection x ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal x
    rw [Submodule.mem_orthogonal] at hq
    exact hq _ (Submodule.starProjection_apply_mem K x)
  have h := (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (K.starProjection x)
    (x - K.starProjection x)).mpr hinner
  have hx : x = K.starProjection x + (x - K.starProjection x) := by abel
  calc ‖x‖^2 = ‖x‖ * ‖x‖ := by ring
    _ = ‖K.starProjection x‖ * ‖K.starProjection x‖
          + ‖x - K.starProjection x‖ * ‖x - K.starProjection x‖ := by
        conv_lhs => rw [hx]
        exact h
    _ = ‖K.starProjection x‖^2 + ‖x - K.starProjection x‖^2 := by ring

/-- If the orthogonal projection is shorter than the complementary part, then the vector is at
most `√2` times the complementary part. -/
lemma norm_le_sqrt_two_mul_sub_starProjection (K : Submodule ℝ (E m)) (x : E m)
    (h : ‖K.starProjection x‖ < ‖x - K.starProjection x‖) :
    ‖x‖ ≤ Real.sqrt 2 * ‖x - K.starProjection x‖ := by
  have hsq := norm_sq_eq_add_starProjection K x
  have h2 : ‖x‖^2 ≤ 2 * ‖x - K.starProjection x‖^2 := by
    nlinarith [hsq, h, norm_nonneg (K.starProjection x), norm_nonneg (x - K.starProjection x)]
  calc ‖x‖ = Real.sqrt (‖x‖^2) := (Real.sqrt_sq (norm_nonneg x)).symm
    _ ≤ Real.sqrt (2 * ‖x - K.starProjection x‖^2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt 2 * ‖x - K.starProjection x‖ := by
        rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_sq (norm_nonneg _)]

/-- An element minimising `‖trPart ρ ·‖` on a nonempty set `F`. -/
lemma exists_argmin (ρ : G →* (E m ≃ᵢ E m))
    (hpd : ∀ K : Set (E m), IsCompact K → {g : G | ((ρ g) '' K ∩ K).Nonempty}.Finite)
    (F : Set G) (k₀ : G) (hk₀ : k₀ ∈ F) :
    ∃ α ∈ F, ∀ k ∈ F, ‖trPart ρ α‖ ≤ ‖trPart ρ k‖ := by
  set S : Set G := {k | k ∈ F ∧ ‖trPart ρ k‖ ≤ ‖trPart ρ k₀‖} with hSdef
  have hSfin : S.Finite := (finite_of_trPart_le ρ hpd ‖trPart ρ k₀‖).subset (fun k hk => hk.2)
  have hSne : S.Nonempty := ⟨k₀, hk₀, le_rfl⟩
  obtain ⟨α, hαS, hαmin⟩ := Finset.exists_min_image hSfin.toFinset (fun k => ‖trPart ρ k‖)
    (hSfin.toFinset_nonempty.mpr hSne)
  rw [Set.Finite.mem_toFinset] at hαS
  refine ⟨α, hαS.1, fun k hk => ?_⟩
  by_cases hk' : ‖trPart ρ k‖ ≤ ‖trPart ρ k₀‖
  · exact hαmin k (by rw [Set.Finite.mem_toFinset]; exact ⟨hk, hk'⟩)
  · exact le_trans hαS.2 (le_of_lt (not_le.mp hk'))

/-- `‖x - starProjection x‖ ≤ ‖x‖`. -/
lemma norm_sub_starProjection_le (K : Submodule ℝ (E m)) (x : E m) :
    ‖x - K.starProjection x‖ ≤ ‖x‖ := by
  have h := norm_sq_eq_add_starProjection K x
  have h2 : ‖x - K.starProjection x‖^2 ≤ ‖x‖^2 := by
    nlinarith [h, sq_nonneg ‖K.starProjection x‖]
  calc ‖x - K.starProjection x‖ = Real.sqrt ((‖x - K.starProjection x‖)^2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖x‖^2) := Real.sqrt_le_sqrt h2
    _ = ‖x‖ := Real.sqrt_sq (norm_nonneg _)

/-- `starProjection` kills the orthogonal complement. -/
lemma starProjection_eq_zero_of_mem_orthogonal (K : Submodule ℝ (E m)) {x : E m}
    (hx : x ∈ Kᗮ) : K.starProjection x = 0 := by
  have h : x ∈ (K.starProjection : E m →ₗ[ℝ] E m).ker := by
    rw [Submodule.ker_starProjection]; exact hx
  exact (LinearMap.mem_ker).mp h

/-- The translation part of a commutator (Buser's formula). -/
lemma trPart_commutator (ρ : G →* (E m ≃ᵢ E m)) (x y : G) :
    trPart ρ (x * y * x⁻¹ * y⁻¹)
      = ((linPart ρ x) (trPart ρ y)
          - (linPart ρ x) ((linPart ρ y)
              ((linPart ρ x)⁻¹ ((linPart ρ y)⁻¹ (trPart ρ y)))))
        + (trPart ρ x - (linPart ρ x) ((linPart ρ y) ((linPart ρ x)⁻¹ (trPart ρ x)))) := by
  have hxy : linPart ρ (x * y) = linPart ρ x * linPart ρ y := linPart_mul ρ x y
  have hxyx : linPart ρ (x * y * x⁻¹) = linPart ρ x * linPart ρ y * (linPart ρ x)⁻¹ := by
    rw [linPart_mul, hxy, linPart_inv]
  rw [trPart_mul, trPart_inv, trPart_mul, trPart_inv, trPart_mul, hxyx, hxy,
    linPart_inv, linPart_inv]
  simp only [LinearIsometryEquiv.mul_def, LinearIsometryEquiv.trans_apply, map_smul,
    neg_smul, one_smul, map_neg, map_add, map_sub]
  abel

/-- On the orthogonal complement of the fixed subspace, `A - 1` is injective. -/
lemma eq_zero_of_mem_orthogonal_of_fixed {A : E m ≃ₗᵢ[ℝ] E m} {x : E m}
    (hx : x ∈ (fixSub A)ᗮ) (hAx : A x = x) : x = 0 := by
  have hfix : x ∈ fixSub A := mem_fixSub.mpr hAx
  have h0 : inner ℝ x x = 0 :=
    (Submodule.mem_orthogonal (fixSub A) x).mp hx x hfix
  exact inner_self_eq_zero.mp h0

/-- On the orthogonal complement of the fixed subspace, `A - 1` is bounded below. -/
lemma bndFixPerp (A : E m ≃ₗᵢ[ℝ] E m) (hA : A ≠ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ (fixSub A)ᗮ, c * ‖x‖ ≤ ‖A x - x‖ := by
  let T : ↥((fixSub A)ᗮ) →ₗ[ℝ] E m :=
    ((opOf A - 1 : E m →L[ℝ] E m) : E m →ₗ[ℝ] E m) ∘ₗ ((fixSub A)ᗮ).subtype
  have hker : LinearMap.ker T = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hAx : A (x : E m) = (x : E m) := by
      have hz : opOf A (x : E m) - (x : E m) = 0 := by simpa [T] using hx
      exact sub_eq_zero.mp hz
    exact Subtype.ext (eq_zero_of_mem_orthogonal_of_fixed x.2 hAx)
  obtain ⟨K, hKpos, hK⟩ := T.exists_antilipschitzWith hker
  have hKposR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  refine ⟨(K : ℝ)⁻¹, inv_pos.mpr hKposR, fun x hx => ?_⟩
  have hbound : ‖x‖ ≤ (K : ℝ) * ‖A x - x‖ := by
    have hlm := hK.le_mul_dist ⟨x, hx⟩ 0
    simpa [T, dist_eq_norm, opOf_apply] using hlm
  calc (K : ℝ)⁻¹ * ‖x‖ ≤ (K : ℝ)⁻¹ * ((K : ℝ) * ‖A x - x‖) := by gcongr
    _ = ‖A x - x‖ := by
        rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hKposR), one_mul]

/-- The set of rotation parts is totally bounded. -/
lemma exists_cover_rotations (η : ℝ) (hη : 0 < η) :
    ∃ F : Finset (E m →L[ℝ] E m), ∀ A : E m ≃ₗᵢ[ℝ] E m, ∃ f ∈ F, ‖opOf A - f‖ < η := by
  have hc : IsCompact (Metric.closedBall (0 : E m →L[ℝ] E m) 1) := isCompact_closedBall _ _
  have hsub : (Set.range fun A : E m ≃ₗᵢ[ℝ] E m => opOf A) ⊆ Metric.closedBall 0 1 := by
    rintro _ ⟨A, rfl⟩
    simpa [Metric.mem_closedBall, dist_eq_norm] using norm_opOf_le_one A
  have hS : TotallyBounded (Set.range fun A : E m ≃ₗᵢ[ℝ] E m => opOf A) :=
    hc.totallyBounded.subset hsub
  obtain ⟨t, htfin, ht⟩ := Metric.totallyBounded_iff.mp hS η hη
  refine ⟨htfin.toFinset, fun A => ?_⟩
  have hmem : opOf A ∈ ⋃ y ∈ t, Metric.ball y η := ht ⟨A, rfl⟩
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨f, hf, hball⟩ := hmem
  exact ⟨f, by rw [Set.Finite.mem_toFinset]; exact hf,
    by simpa [Metric.mem_ball, dist_eq_norm] using hball⟩

/-- Buser's "mini Bieberbach" lemma: in every direction there are elements with arbitrarily
small rotation part and translation part close to `-t` times that direction. -/
theorem miniLemma (ρ : G →* (E m ≃ᵢ E m))
    (hcoc : ∃ K : Set (E m), IsCompact K ∧ ∀ x : E m, ∃ g : G, ρ g x ∈ K)
    (u : E m) (hu : ‖u‖ = 1) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ g : G, ∃ t : ℝ, 1 ≤ t ∧ mOf (linPart ρ g) ≤ ε ∧ ‖trPart ρ g + t • u‖ ≤ δ * t := by
  obtain ⟨d, hd0, hd⟩ := exists_translation_bound ρ hcoc
  set eps : ℝ := min ε (δ/2) with hepsdef
  have hepspos : 0 < eps := lt_min hε (by linarith)
  have hepsε : eps ≤ ε := min_le_left _ _
  have hepsδ : eps ≤ δ/2 := min_le_right _ _
  obtain ⟨F, hF⟩ := exists_cover_rotations (m := m) (eps/2) (by linarith)
  set N : ℕ := F.card with hNdef
  obtain ⟨L : ℕ, hL⟩ := exists_nat_gt ((4*d + 1)/δ)
  have hLpos : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · rw [h] at hL
      have h0 : (0:ℝ) < (4*d+1)/δ := div_pos (by linarith) hδ
      simp only [Nat.cast_zero] at hL
      linarith
    · exact h
  have hLbig : 4*d ≤ δ * L := by
    have h2 : (4*d + 1)/δ * δ < (L:ℝ) * δ := mul_lt_mul_of_pos_right hL hδ
    rw [div_mul_cancel₀ _ (ne_of_gt hδ)] at h2
    linarith
  choose γ hγ using fun k : ℕ => hd u hu k
  have hγprop : ∀ k : ℕ, ‖trPart ρ (γ k) + (k:ℝ) • u‖ ≤ d := hγ
  have hchoice : ∀ i : Fin (N+1), ∃ f : ↥F,
      ‖opOf (linPart ρ (γ (L * 2^(i.val+1)))) - (f : E m →L[ℝ] E m)‖ < eps/2 := by
    intro i
    obtain ⟨f, hf, hlt⟩ := hF (linPart ρ (γ (L * 2^(i.val+1))))
    exact ⟨⟨f, hf⟩, hlt⟩
  choose c hc using hchoice
  have hcard : Fintype.card ↥F < Fintype.card (Fin (N+1)) := by
    rw [Fintype.card_fin, hNdef, Fintype.card_coe]
    exact Nat.lt_succ_self _
  obtain ⟨i₀, j₀, hij, hcij⟩ := Fintype.exists_ne_map_eq_of_card_lt c hcard
  have hval : i₀.val ≠ j₀.val := fun h => hij (Fin.ext h)
  have hex : ∃ p q : Fin (N+1), p.val < q.val ∧
      (c p : E m →L[ℝ] E m) = (c q : E m →L[ℝ] E m) := by
    rcases lt_or_gt_of_ne hval with h | h
    · exact ⟨i₀, j₀, h, congrArg Subtype.val hcij⟩
    · exact ⟨j₀, i₀, h, (congrArg Subtype.val hcij).symm⟩
  obtain ⟨i, j, hij, hcij⟩ := hex
  set a : ℕ := L * 2^(i.val+1) with hadef
  set b : ℕ := L * 2^(j.val+1) with hbdef
  have hpow : 2^(i.val+1) < 2^(j.val+1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hab : a < b := by
    rw [hadef, hbdef]
    exact Nat.mul_lt_mul_of_pos_left hpow hLpos
  have hclose : ‖opOf (linPart ρ (γ a)) - opOf (linPart ρ (γ b))‖ < eps := by
    have h1 : ‖opOf (linPart ρ (γ a)) - (c i : E m →L[ℝ] E m)‖ < eps/2 := hc i
    have h2 : ‖opOf (linPart ρ (γ b)) - (c j : E m →L[ℝ] E m)‖ < eps/2 := hc j
    have h3 : (c i : E m →L[ℝ] E m) = (c j : E m →L[ℝ] E m) := hcij
    have htri : ‖opOf (linPart ρ (γ a)) - opOf (linPart ρ (γ b))‖
        ≤ ‖opOf (linPart ρ (γ a)) - (c i : E m →L[ℝ] E m)‖
          + ‖(c i : E m →L[ℝ] E m) - opOf (linPart ρ (γ b))‖ := by
      have := dist_triangle (opOf (linPart ρ (γ a))) (c i : E m →L[ℝ] E m)
        (opOf (linPart ρ (γ b)))
      simpa [dist_eq_norm] using this
    rw [← h3, norm_sub_rev] at h2
    linarith
  have hpowR : 2 * (2:ℝ)^(i.val+1) ≤ (2:ℝ)^(j.val+1) := by
    have h : i.val + 2 ≤ j.val + 1 := by omega
    calc 2 * (2:ℝ)^(i.val+1) = (2:ℝ)^(i.val+2) := by rw [pow_succ]; ring
      _ ≤ (2:ℝ)^(j.val+1) := pow_le_pow_right₀ (by norm_num) h
  have ha_cast : ((a:ℝ)) = (L:ℝ) * (2:ℝ)^(i.val+1) := by rw [hadef]; push_cast; ring
  have hb_cast : ((b:ℝ)) = (L:ℝ) * (2:ℝ)^(j.val+1) := by rw [hbdef]; push_cast; ring
  have hLnn : (0:ℝ) ≤ (L:ℝ) := Nat.cast_nonneg L
  have haR : 2 * ((a:ℝ)) ≤ (b:ℝ) := by
    rw [ha_cast, hb_cast]
    nlinarith [hpowR, hLnn]
  have ha_ge : (a:ℝ) ≤ (b:ℝ) - (a:ℝ) := by linarith [haR]
  have hLam : (L:ℝ) ≤ (b:ℝ) - (a:ℝ) := by
    have h2 : (2:ℝ)^(j.val+1) - (2:ℝ)^(i.val+1) ≥ 1 := by
      have h3 : (2:ℝ)^(i.val+1) * 2 ≤ (2:ℝ)^(j.val+1) := by linarith [hpowR]
      have h4 : (1:ℝ) ≤ (2:ℝ)^(i.val+1) := one_le_pow₀ (by norm_num)
      linarith [h3, h4]
    rw [ha_cast, hb_cast]
    nlinarith [h2, hLnn]
  have hlam_ge : 4*d ≤ δ * ((b:ℝ) - (a:ℝ)) := by
    nlinarith [hLbig, hLam, hδ.le]
  have hAinv : linPart ρ ((γ a)⁻¹) = (linPart ρ (γ a))⁻¹ := linPart_inv ρ _
  have hA : linPart ρ (γ b * (γ a)⁻¹) = linPart ρ (γ b) * (linPart ρ (γ a))⁻¹ := by
    rw [linPart_mul, hAinv]
  set wa : E m := trPart ρ (γ a) + (a:ℝ) • u with hwadef
  set wb : E m := trPart ρ (γ b) + (b:ℝ) • u with hwbdef
  have hwa : ‖wa‖ ≤ d := hγprop a
  have hwb : ‖wb‖ ≤ d := hγprop b
  have htr : (a:ℝ) • ((linPart ρ (γ b * (γ a)⁻¹)) u - u)
        - (linPart ρ (γ b * (γ a)⁻¹)) wa + wb
      = trPart ρ (γ b * (γ a)⁻¹) + ((b:ℝ) - (a:ℝ)) • u := by
    rw [hwadef, hwbdef, trPart_mul, trPart_inv, hAinv, hA]
    simp only [map_neg, map_add, map_smul, smul_sub, sub_smul, LinearIsometryEquiv.mul_def,
      LinearIsometryEquiv.trans_apply]
    abel
  refine ⟨γ b * (γ a)⁻¹, (b:ℝ) - (a:ℝ), ?_, ?_, ?_⟩
  · have h1 : ((a:ℕ):ℝ) + 1 ≤ ((b:ℕ):ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hab : a + 1 ≤ b)
    linarith
  · rw [hA]
    refine le_trans (mOf_mul_inv_le (linPart ρ (γ b)) (linPart ρ (γ a)))
      (le_trans (le_of_lt ?_) hepsε)
    rwa [norm_sub_rev] at hclose
  · rw [← htr]
    have hmA : mOf (linPart ρ (γ b * (γ a)⁻¹)) < eps := by
      rw [hA]
      refine lt_of_le_of_lt (mOf_mul_inv_le (linPart ρ (γ b)) (linPart ρ (γ a))) ?_
      rwa [norm_sub_rev] at hclose
    have h1 : ‖(a:ℝ) • ((linPart ρ (γ b * (γ a)⁻¹)) u - u)‖ ≤ (a:ℝ) * eps := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg a)]
      have : ‖(linPart ρ (γ b * (γ a)⁻¹)) u - u‖ ≤ eps := by
        refine le_trans (mOf_apply _ u) ?_
        rw [hu, mul_one]
        exact hmA.le
      exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg a)
    have h2 : ‖- (linPart ρ (γ b * (γ a)⁻¹)) wa + wb‖ ≤ 2 * d := by
      have he : - (linPart ρ (γ b * (γ a)⁻¹)) wa + wb
          = wb - (linPart ρ (γ b * (γ a)⁻¹)) wa := by abel
      rw [he]
      calc ‖wb - (linPart ρ (γ b * (γ a)⁻¹)) wa‖
          ≤ ‖wb‖ + ‖(linPart ρ (γ b * (γ a)⁻¹)) wa‖ := norm_sub_le _ _
        _ ≤ d + d := by rw [LinearIsometryEquiv.norm_map]; linarith
        _ = 2 * d := by ring
    have h3 : ‖(a:ℝ) • ((linPart ρ (γ b * (γ a)⁻¹)) u - u)
        - (linPart ρ (γ b * (γ a)⁻¹)) wa + wb‖
        = ‖((a:ℝ) • ((linPart ρ (γ b * (γ a)⁻¹)) u - u))
          + (- (linPart ρ (γ b * (γ a)⁻¹)) wa + wb)‖ := by abel_nf
    rw [h3]
    refine le_trans (norm_add_le _ _) ?_
    have h6 : ((b:ℝ) - (a:ℝ)) * eps + 2 * d ≤ δ * ((b:ℝ) - (a:ℝ)) := by
      have h7 : ((b:ℝ) - (a:ℝ)) * eps ≤ ((b:ℝ) - (a:ℝ)) * (δ/2) :=
        mul_le_mul_of_nonneg_left hepsδ (by linarith)
      have h8 : 2 * d ≤ δ * ((b:ℝ) - (a:ℝ)) / 2 := by linarith [hlam_ge]
      linarith
    have h9 : (a:ℝ) * eps ≤ ((b:ℝ) - (a:ℝ)) * eps :=
      mul_le_mul_of_nonneg_right ha_ge hepspos.le
    linarith

end

end Work.Mostow
