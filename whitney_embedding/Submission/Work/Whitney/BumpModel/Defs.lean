import Mathlib
import Submission.Work.Whitney.LocalModel

/-!
# Cut-off Whitney models: definitions and elementary properties

We build, for every `δ > 0`, a smooth immersion `β⁺ : ℝⁿ → ℝⁿ × ℝⁿ` which agrees exactly with
the linear inclusion `x ↦ (x, 0)` outside a ball of radius `R ≥ 1`, is `δ`-close to it everywhere,
and has exactly one transverse double point; its mirror `β⁻ = mirrorFun n ∘ β⁺` has the same double
point with the opposite sign.

The building block is the "structure map" of a cut-off function `χ`:
```
structMap χ x = (x - 2 x₀ û(x) e₀, û(x) e₀ + û(x) x₀ (x - x₀ e₀)),   û = χ / (1 + ∑ xᵢ²),
```
which is the linear inclusion where `χ = 0` and equals Whitney's model where `χ = 1`.  Scaling
argument and value by `ρ`, with `χ` supported in a ball of radius `R'' ≥ 1/ρ`, gives `β⁺`; the
deviation from the inclusion is `ρ • (structMap - incl)`, of norm `≤ ρ`.

## Main definitions

* `Work.Whitney.diagLM c` — the diagonal linear map `x ↦ (i ↦ c i * x i)` on `Fin n → ℝ`;
* `Work.Whitney.mirrorLin n` — `mirrorFun n` as a linear map, of determinant `-1`;
* `Work.Whitney.bumpU`, `Work.Whitney.uhat`, `Work.Whitney.structMap`;
* `Work.Whitney.bumpPlus χ ρ`, `Work.Whitney.bumpMinus χ ρ` — the two cut-off models.
-/

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

noncomputable section

variable (n : ℕ) [NeZero n]

/-! ### The diagonal linear map and the mirror -/

/-- The diagonal linear endomorphism of `Fin n → ℝ` with entries `c`. -/
def diagLM (c : Fin n → ℝ) : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  LinearMap.pi fun i => (c i • (1 : ℝ →ₗ[ℝ] ℝ)).comp (LinearMap.proj i)

@[simp] theorem diagLM_apply (c x : Fin n → ℝ) (i : Fin n) : diagLM n c x i = c i * x i := by
  simp [diagLM]

theorem diagLM_det (c : Fin n → ℝ) : LinearMap.det (diagLM n c) = ∏ i, c i := by
  rw [diagLM, LinearMap.det_pi]
  exact Finset.prod_congr rfl fun i _ => by rw [LinearMap.det_ring]; simp

theorem diagLM_injective {c : Fin n → ℝ} (hc : ∀ i, c i ≠ 0) :
    Function.Injective (diagLM n c) := by
  intro x y hxy
  funext i
  have h : c i * x i = c i * y i := by
    have := congrFun hxy i
    simpa using this
  exact mul_left_cancel₀ (hc i) h

theorem diagLM_norm (c x : Fin n → ℝ) (hc : ∀ i, c i = 1 ∨ c i = -1) :
    ‖diagLM n c x‖ = ‖x‖ := by
  rw [Pi.norm_def, Pi.norm_def]
  congr 1
  refine Finset.sup_congr rfl fun i _ => ?_
  rcases hc i with h | h <;> simp [h]

/-- `mirrorFun n` (negation of the first coordinate of the second block) as a linear map. -/
def mirrorLin :
    ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  LinearMap.prodMap LinearMap.id (diagLM n fun i : Fin n => if i = 0 then -1 else 1)

/-- `mirrorLin` is `mirrorFun`. -/
theorem mirrorLin_apply (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    mirrorLin n z = mirrorFun n z := by
  refine Prod.ext ?_ ?_
  · rfl
  · funext i
    by_cases h : i = 0 <;> simp [mirrorLin, mirrorFun, h]

theorem mirrorLin_det : LinearMap.det (mirrorLin n) = -1 := by
  rw [mirrorLin, LinearMap.det_prodMap, LinearMap.det_id, one_mul, diagLM_det]
  rw [Finset.prod_eq_single (0 : Fin n)]
  · simp
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mirrorLin_norm (z : (Fin n → ℝ) × (Fin n → ℝ)) :
    ‖mirrorLin n z‖ = ‖z‖ := by
  rw [mirrorLin, LinearMap.prodMap_apply, Prod.norm_def, Prod.norm_def,
    diagLM_norm n _ _ (fun i => by by_cases h : i = 0 <;> simp [h])]
  simp

theorem mirrorLin_injective : Function.Injective (mirrorLin n) := by
  intro z w h
  have h0 : mirrorLin n (z - w) = 0 := by rw [map_sub, h, sub_self]
  have hz : ‖z - w‖ = 0 := by rw [← mirrorLin_norm n (z - w), h0, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-! ### The model functions -/

/-- The linear inclusion `x ↦ (x, 0)`, as a linear map. -/
def inclLM : (Fin n → ℝ) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) :=
  LinearMap.inl ℝ _ _

@[simp] theorem inclLM_apply (x : Fin n → ℝ) : inclLM n x = inclModel n x := rfl

/-- `u x = 1 + ∑ᵢ xᵢ²`. -/
def bumpU (x : Fin n → ℝ) : ℝ := 1 + ∑ i, x i ^ 2

/-- `û x = χ x / (1 + ∑ᵢ xᵢ²)`. -/
def uhat (χ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : ℝ := χ x / bumpU n x

theorem bumpU_pos (x : Fin n → ℝ) : 0 < bumpU n x := by
  have h : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  simp only [bumpU]; linarith

theorem bumpU_ge_one (x : Fin n → ℝ) : 1 ≤ bumpU n x := by
  have h : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  simp only [bumpU]; linarith

theorem sq_le_sum (x : Fin n → ℝ) (i : Fin n) : x i ^ 2 ≤ ∑ j, x j ^ 2 :=
  Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)

theorem sq_le_bumpU (x : Fin n → ℝ) (i : Fin n) : x i ^ 2 ≤ bumpU n x := by
  have h := sq_le_sum n x i
  simp only [bumpU]; linarith

theorem abs_le_bumpU (x : Fin n → ℝ) (i : Fin n) : |x i| ≤ bumpU n x := by
  have h : |x i| ≤ 1 + x i ^ 2 := by
    nlinarith [sq_nonneg (|x i| - 1), sq_abs (x i), abs_nonneg (x i)]
  have h2 := sq_le_sum n x i
  simp only [bumpU]; linarith

theorem two_abs_le_bumpU (x : Fin n → ℝ) (i : Fin n) : 2 * |x i| ≤ bumpU n x := by
  have h : 2 * |x i| ≤ 1 + x i ^ 2 := by
    nlinarith [sq_nonneg (|x i| - 1), sq_abs (x i), abs_nonneg (x i)]
  have h2 := sq_le_sum n x i
  simp only [bumpU]; linarith

theorem abs_mul_abs_le_bumpU (x : Fin n → ℝ) (i j : Fin n) : |x i * x j| ≤ bumpU n x := by
  have h : 2 * |x i * x j| ≤ x i ^ 2 + x j ^ 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
  have h2 : x i ^ 2 + x j ^ 2 ≤ 2 * bumpU n x := by
    have h3 := sq_le_sum n x i
    have h4 := sq_le_sum n x j
    simp only [bumpU]; linarith
  linarith

theorem contDiff_bumpU : ContDiff ℝ ⊤ (bumpU n) := by
  unfold bumpU
  fun_prop

/-- `‖e₀‖ = 1`. -/
theorem norm_e0 : ‖(e0 n : Fin n → ℝ)‖ = 1 := by
  refine le_antisymm ?_ ?_
  · rw [pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    intro i
    rw [e0, Pi.single_apply]
    by_cases h : i = 0 <;> simp [h]
  · have h := norm_le_pi_norm (e0 n) 0
    rw [e0, Pi.single_eq_same, Real.norm_eq_abs, abs_one] at h
    rw [e0]
    exact h

/-- `‖t • e₀‖ = |t|`. -/
theorem norm_smul_e0 (t : ℝ) : ‖t • (e0 n : Fin n → ℝ)‖ = |t| := by
  rw [norm_smul, norm_e0 n, mul_one, Real.norm_eq_abs]

variable {χ : (Fin n → ℝ) → ℝ}

theorem contDiff_uhat (hχ : ContDiff ℝ ⊤ χ) : ContDiff ℝ ⊤ (uhat n χ) := by
  unfold uhat
  exact hχ.div (contDiff_bumpU n) fun x => ne_of_gt (bumpU_pos n x)

theorem uhat_nonneg (h : ∀ x, 0 ≤ χ x) (x : Fin n → ℝ) : 0 ≤ uhat n χ x :=
  div_nonneg (h x) (le_of_lt (bumpU_pos n x))

theorem uhat_le_one (h : ∀ x, χ x ≤ 1) (x : Fin n → ℝ) : uhat n χ x ≤ 1 := by
  rw [uhat, div_le_one (bumpU_pos n x)]
  exact le_trans (h x) (bumpU_ge_one n x)

theorem uhat_abs_le (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1) (x : Fin n → ℝ) :
    |uhat n χ x| ≤ 1 := by
  rw [abs_of_nonneg (uhat_nonneg n h0 x)]
  exact uhat_le_one n h1 x

theorem abs_chi_le (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1) (x : Fin n → ℝ) : |χ x| ≤ 1 := by
  rw [abs_of_nonneg (h0 x)]; exact h1 x

theorem uhat_abs_le_inv (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1) (x : Fin n → ℝ) :
    |uhat n χ x| ≤ (bumpU n x)⁻¹ := by
  rw [uhat, abs_div, abs_of_nonneg (h0 x), abs_of_nonneg (le_of_lt (bumpU_pos n x))]
  rw [div_le_iff₀ (bumpU_pos n x), inv_mul_cancel₀ (ne_of_gt (bumpU_pos n x))]
  exact h1 x

theorem abs_mul_uhat_le (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1) (x : Fin n → ℝ) :
    |x 0 * uhat n χ x| ≤ 1 := by
  have h3 := uhat_abs_le_inv n h0 h1 x
  have h2 : |x 0| ≤ bumpU n x := abs_le_bumpU n x 0
  have hu : 0 < bumpU n x := bumpU_pos n x
  calc |x 0 * uhat n χ x| = |x 0| * |uhat n χ x| := abs_mul _ _
    _ ≤ |x 0| * (bumpU n x)⁻¹ := by gcongr
    _ ≤ bumpU n x * (bumpU n x)⁻¹ := by gcongr
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hu)

theorem two_abs_mul_uhat_le (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1) (x : Fin n → ℝ) :
    |2 * x 0 * uhat n χ x| ≤ 1 := by
  have h3 := uhat_abs_le_inv n h0 h1 x
  have h2 : 2 * |x 0| ≤ bumpU n x := two_abs_le_bumpU n x 0
  have hu : 0 < bumpU n x := bumpU_pos n x
  rw [show (2 : ℝ) * x 0 * uhat n χ x = 2 * (x 0 * uhat n χ x) by ring, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc 2 * |x 0 * uhat n χ x| = 2 * (|x 0| * |uhat n χ x|) := by rw [abs_mul]
    _ ≤ 2 * (|x 0| * (bumpU n x)⁻¹) := by gcongr
    _ ≤ bumpU n x * (bumpU n x)⁻¹ := by
        rw [show (2 : ℝ) * (|x 0| * (bumpU n x)⁻¹) = (2 * |x 0|) * (bumpU n x)⁻¹ by ring]
        gcongr
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hu)

/-- The structure map attached to a cut-off `χ`; it reduces to the inclusion where `χ = 0`. -/
def structMap (χ : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) : (Fin n → ℝ) × (Fin n → ℝ) :=
  (x - (2 * x 0 * uhat n χ x) • e0 n,
   uhat n χ x • e0 n + (uhat n χ x * x 0) • (x - x 0 • e0 n))

/-- The first cut-off model: `β⁺ x = ρ • structMap χ (ρ⁻¹ • x)`. -/
def bumpPlus (χ : (Fin n → ℝ) → ℝ) (ρ : ℝ) : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  fun x => ρ • structMap n χ (ρ⁻¹ • x)

/-- The second cut-off model: the mirror of `β⁺`. -/
def bumpMinus (χ : (Fin n → ℝ) → ℝ) (ρ : ℝ) : (Fin n → ℝ) → (Fin n → ℝ) × (Fin n → ℝ) :=
  fun x => mirrorFun n (bumpPlus n χ ρ x)

@[simp] theorem structMap_fst (x : Fin n → ℝ) :
    (structMap n χ x).1 = x - (2 * x 0 * uhat n χ x) • e0 n := rfl

@[simp] theorem structMap_snd (x : Fin n → ℝ) :
    (structMap n χ x).2 = uhat n χ x • e0 n + (uhat n χ x * x 0) • (x - x 0 • e0 n) := rfl

@[simp] theorem bumpPlus_apply (ρ : ℝ) (x : Fin n → ℝ) :
    bumpPlus n χ ρ x = ρ • structMap n χ (ρ⁻¹ • x) := rfl

@[simp] theorem bumpMinus_apply (ρ : ℝ) (x : Fin n → ℝ) :
    bumpMinus n χ ρ x = mirrorFun n (bumpPlus n χ ρ x) := rfl

/-- Coordinate description of the structure map. -/
theorem structMap_apply (x : Fin n → ℝ) :
    structMap n χ x =
      ((fun i => if i = 0 then x 0 * (1 - 2 * uhat n χ x) else x i),
       (fun i => if i = 0 then uhat n χ x else uhat n χ x * x 0 * x i)) := by
  refine Prod.ext ?_ ?_ <;> funext i
  · by_cases h : i = 0
    · subst h; simp [structMap, e0] <;> ring
    · simp [structMap, e0, h]
  · by_cases h : i = 0
    · subst h; simp [structMap, e0] <;> ring
    · simp [structMap, e0, h]

/-- The structure map is the inclusion where `χ` vanishes. -/
theorem structMap_eq_incl_of_chi_zero {x : Fin n → ℝ} (h : χ x = 0) :
    structMap n χ x = inclModel n x := by
  have hu : uhat n χ x = 0 := by simp [uhat, h]
  unfold structMap
  rw [hu]
  simp [inclModel]

theorem contDiff_structMap (hχ : ContDiff ℝ ⊤ χ) : ContDiff ℝ ⊤ (structMap n χ) := by
  have h : ContDiff ℝ ⊤ (uhat n χ) := contDiff_uhat n hχ
  unfold structMap
  fun_prop

/-- The deviation of the structure map from the inclusion is at most `1`. -/
theorem structMap_sub_incl_bound (h0 : ∀ x, 0 ≤ χ x) (h1 : ∀ x, χ x ≤ 1) (x : Fin n → ℝ) :
    ‖structMap n χ x - inclModel n x‖ ≤ 1 := by
  have hu : 0 < bumpU n x := bumpU_pos n x
  have hA : |2 * x 0 * uhat n χ x| ≤ 1 := two_abs_mul_uhat_le n h0 h1 x
  have hû : |uhat n χ x| ≤ (bumpU n x)⁻¹ := uhat_abs_le_inv n h0 h1 x
  have hB : |uhat n χ x| ≤ 1 := by
    calc |uhat n χ x| ≤ (bumpU n x)⁻¹ := hû
      _ ≤ 1 := by rw [inv_le_one₀ hu]; exact bumpU_ge_one n x
  rw [Prod.norm_def, max_le_iff]
  refine ⟨?_, ?_⟩
  · have h : (structMap n χ x - inclModel n x).1 = -((2 * x 0 * uhat n χ x) • e0 n) := by
      rw [Prod.fst_sub, structMap_fst, inclModel_fst]; abel
    rw [h, norm_neg, norm_smul, norm_e0 n, mul_one]
    exact hA
  · have h : (structMap n χ x - inclModel n x).2 =
        fun i => if i = 0 then uhat n χ x else uhat n χ x * x 0 * x i := by
      funext i
      rw [Prod.snd_sub, Pi.sub_apply,
        congrFun (congrArg Prod.snd (structMap_apply n (χ := χ) x)) i]
      simp
    rw [h, pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)]
    intro i
    by_cases hi : i = 0
    · subst hi
      simpa using hB
    · rw [if_neg hi, Real.norm_eq_abs]
      have hxij : |x 0 * x i| ≤ bumpU n x := abs_mul_abs_le_bumpU n x 0 i
      calc |uhat n χ x * x 0 * x i| = |uhat n χ x| * |x 0 * x i| := by
            simp only [abs_mul, mul_assoc]
          _ ≤ (bumpU n x)⁻¹ * (bumpU n x) :=
              mul_le_mul hû hxij (abs_nonneg _) (by positivity)
          _ = 1 := inv_mul_cancel₀ (ne_of_gt hu)

end

end Work.Whitney
