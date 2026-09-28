import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux

/-!
# Setup for `Work.HP.Q44Child.superlattice_count`

Given a rank-`2` primitive lattice `Λ ⊆ ℤ^5` we study the rank-`3` superlattices
`L ⊇ Λ`.  Everything happens in `E5 = EuclideanSpace ℝ (Fin 5)`:

* `toE : ℤ^5 → E5` is the inclusion;
* `Lℝ Λ` is the real span of `Λ`, and `W Λ = (Lℝ Λ)ᗮ` its orthogonal complement;
* `proj Λ` is the orthogonal projection onto `W Λ`;
* `ΓW Λ = π(ℤ^5) ⊆ W Λ` is the projected lattice, which is isomorphic to `ℤ^5/Λ`
  and has covolume `1/detL Λ`.

The counting theorem `superlattice_count` follows by mapping a superlattice `L` to
the generator of the rank-`1` subgroup `π(L) ≤ ΓW Λ`, whose norm is
`detL L / detL Λ ≤ T`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace Work.HP.Q44Child

noncomputable section

open scoped RealInnerProductSpace

/-- `ℝ^5` with the Euclidean (ℓ²) norm. -/
abbrev E5 := EuclideanSpace ℝ (Fin 5)

/-- The tautological inclusion `ℤ^5 → ℝ^5`. -/
def toE : (Fin 5 → ℤ) →ₗ[ℤ] E5 where
  toFun v := WithLp.toLp 2 (fun i => (v i : ℝ))
  map_add' v w := by ext i; simp
  map_smul' m v := by ext i; simp

@[simp] lemma toE_ofLp (v : Fin 5 → ℤ) : (toE v).ofLp = fun i => (v i : ℝ) := rfl

lemma toE_injective : Function.Injective toE := by
  intro v w h
  funext i
  have h2 := congrFun (congrArg WithLp.ofLp h) i
  simpa using h2

@[simp] lemma toE_zero : toE (0 : Fin 5 → ℤ) = 0 := by
  ext i; simp

@[simp] lemma toE_add (v w : Fin 5 → ℤ) : toE (v + w) = toE v + toE w :=
  map_add toE v w

@[simp] lemma toE_smul (m : ℤ) (v : Fin 5 → ℤ) : toE (m • v) = m • toE v :=
  map_smul toE m v

/-- The Euclidean norm of `toE v` is `eNorm v`. -/
lemma norm_toE (v : Fin 5 → ℤ) : ‖toE v‖ = eNorm v := by
  rw [eNorm, PiLp.norm_eq_of_L2]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Real.norm_eq_abs, sq_abs]

lemma toE_sub (v w : Fin 5 → ℤ) : toE (v - w) = toE v - toE w :=
  map_sub toE v w

@[simp] lemma toE_neg (v : Fin 5 → ℤ) : toE (-v) = -toE v :=
  map_neg toE v

@[simp] lemma inner_toE (v w : Fin 5 → ℤ) :
    inner ℝ (toE v) (toE w) = ∑ i, (v i : ℝ) * (w i : ℝ) := by
  rw [PiLp.inner_apply]
  simp only [toE_ofLp, RCLike.inner_apply, conj_trivial, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma norm_toE_sq (v : Fin 5 → ℤ) : ‖toE v‖ ^ 2 = ∑ i, ((v i : ℝ)) ^ 2 := by
  rw [norm_toE, eNorm, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]

@[simp] lemma toE_single (i : Fin 5) :
    toE (Pi.single i (1 : ℤ)) = WithLp.toLp 2 (Pi.single i (1 : ℝ)) := by
  ext j; by_cases h : j = i <;> simp [h]

/-- The realification of a lattice `Λ ⊆ ℤ^5`. -/
def ΛE (Λ : Submodule ℤ (Fin 5 → ℤ)) : Submodule ℤ E5 := Λ.map toE

/-- The real span of a lattice `Λ ⊆ ℤ^5`. -/
def Lℝ (Λ : Submodule ℤ (Fin 5 → ℤ)) : Submodule ℝ E5 :=
  Submodule.span ℝ (ΛE Λ : Set E5)

/-- The orthogonal complement of the real span of `Λ`. -/
def W (Λ : Submodule ℤ (Fin 5 → ℤ)) : Submodule ℝ E5 := (Lℝ Λ)ᗮ

/-- The orthogonal projection onto `W Λ`. -/
def proj (Λ : Submodule ℤ (Fin 5 → ℤ)) : E5 →L[ℝ] E5 := (W Λ).starProjection

lemma proj_mem (Λ : Submodule ℤ (Fin 5 → ℤ)) (x : E5) : proj Λ x ∈ W Λ :=
  Submodule.starProjection_apply_mem (W Λ) x

lemma norm_proj_le (Λ : Submodule ℤ (Fin 5 → ℤ)) (x : E5) : ‖proj Λ x‖ ≤ ‖x‖ :=
  Submodule.norm_starProjection_apply_le (K := W Λ) x

lemma starProjection_eq_zero_iff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : Submodule ℝ E} [K.HasOrthogonalProjection] {v : E} :
    K.starProjection v = 0 ↔ v ∈ Kᗮ := by
  rw [Submodule.starProjection_apply]
  constructor
  · intro h
    exact Submodule.orthogonalProjectionOnto_eq_zero_iff.mp (Subtype.ext (by simpa using h))
  · intro h
    exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr h)

lemma proj_eq_zero_iff (Λ : Submodule ℤ (Fin 5 → ℤ)) (x : E5) :
    proj Λ x = 0 ↔ x ∈ Lℝ Λ := by
  rw [proj, starProjection_eq_zero_iff]
  simp only [W]
  rw [Submodule.orthogonal_orthogonal]

lemma proj_eq_self_iff (Λ : Submodule ℤ (Fin 5 → ℤ)) (x : E5) :
    proj Λ x = x ↔ x ∈ W Λ :=
  Submodule.starProjection_eq_self_iff

lemma proj_idem (Λ : Submodule ℤ (Fin 5 → ℤ)) (x : E5) : proj Λ (proj Λ x) = proj Λ x :=
  (Submodule.starProjection_eq_self_iff.mpr (Submodule.starProjection_apply_mem (W Λ) x))

lemma proj_kills (Λ : Submodule ℤ (Fin 5 → ℤ)) {x : E5} (hx : x ∈ Lℝ Λ) : proj Λ x = 0 :=
  (proj_eq_zero_iff Λ x).mpr hx

lemma proj_kills_toE (Λ : Submodule ℤ (Fin 5 → ℤ)) {v : Fin 5 → ℤ} (hv : v ∈ Λ) :
    proj Λ (toE v) = 0 := by
  refine proj_kills Λ ?_
  exact Submodule.subset_span ⟨v, hv, rfl⟩

/-- The generators `π(e_i)` of the projected lattice. -/
def gen (Λ : Submodule ℤ (Fin 5 → ℤ)) (i : Fin 5) : W Λ :=
  ⟨proj Λ (toE (Pi.single i 1)), proj_mem Λ _⟩

/-- The three indices `2, 3, 4` of `Fin 5`. -/
def idx3 : Fin 3 → Fin 5 := fun j => ⟨j.1 + 2, by have := j.2; omega⟩

/-- The projected images `π (b 2), π (b 3), π (b 4)` of the last three vectors of a basis
`b` of `ℤ^5` whose first two vectors span `Λ`. -/
def Ggen (b : Module.Basis (Fin 5) ℤ (Fin 5 → ℤ)) (Λ : Submodule ℤ (Fin 5 → ℤ)) :
    Fin 3 → W Λ :=
  fun j => ⟨proj Λ (toE (b (idx3 j))), proj_mem Λ _⟩

/-- `Γ Λ = π(ℤ^5)`, as a submodule of `W Λ`. -/
def ΓW (Λ : Submodule ℤ (Fin 5 → ℤ)) : Submodule ℤ (W Λ) :=
  Submodule.span ℤ (Set.range (gen Λ))

/-- The lattice points of `Γ Λ` of norm at most `T`. -/
def uSet (Λ : Submodule ℤ (Fin 5 → ℤ)) (T : ℝ) : Set (W Λ) :=
  {u | u ∈ ΓW Λ ∧ ‖(u : E5)‖ ≤ T}

/-- The set of rank-`3` superlattices of `Λ` of determinant at most `T * detL Λ`. -/
def Sset (Λ : Submodule ℤ (Fin 5 → ℤ)) (T : ℝ) : Set (Submodule ℤ (Fin 5 → ℤ)) :=
  {L | Λ ≤ L ∧ rk L = 3 ∧ detL L ≤ T * detL Λ}

/-- Every point of `ℝ^5` is within `√5/2` of an integral vector. -/
lemma exists_int_close (y : E5) : ∃ m : Fin 5 → ℤ, ‖y - toE m‖ ≤ Real.sqrt 5 / 2 := by
  have h : ∀ i : Fin 5, ∃ m : ℤ, |y.ofLp i - (m : ℝ)| ≤ 1/2 := by
    intro i
    refine ⟨⌊y.ofLp i + 1/2⌋, ?_⟩
    have h1 := Int.floor_le (y.ofLp i + 1/2)
    have h2 := Int.lt_floor_add_one (y.ofLp i + 1/2)
    rw [abs_le]
    constructor <;> linarith
  choose m hm using h
  refine ⟨m, ?_⟩
  rw [PiLp.norm_eq_of_L2]
  have h2 : (∑ i, ‖(y - toE m).ofLp i‖ ^ 2) ≤ 5 * (1/2 : ℝ) ^ 2 := by
    calc (∑ i, ‖(y - toE m).ofLp i‖ ^ 2) ≤ ∑ _i : Fin 5, (1/2 : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [PiLp.sub_apply, toE_ofLp]
          have h3 : |y.ofLp i - ↑(m i)| ^ 2 ≤ (1/2 : ℝ) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hm i) 2
          simpa [Real.norm_eq_abs, sq_abs] using h3
      _ = 5 * (1/2 : ℝ) ^ 2 := by simp
  calc Real.sqrt (∑ i, ‖(y - toE m).ofLp i‖ ^ 2) ≤ Real.sqrt (5 * (1/2 : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt h2
    _ = Real.sqrt 5 / 2 := by
        have h4 : (Real.sqrt 5 / 2) ^ 2 = 5 * (1/2 : ℝ) ^ 2 := by
          rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; norm_num
        rw [← h4, Real.sqrt_sq (by positivity)]

end

end Work.HP.Q44Child
