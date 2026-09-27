import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.StabHoroForm
import Submission.Work.Mostow.pairStabDefs

/-!
# A space-like unit vector orthogonal to two distinct null vectors

For `n ≥ 2` and two distinct points `a ≠ b` of the boundary sphere `Sph n`, the two null vectors
`θ a = (a,1)` and `θ b = (b,1)` of Minkowski space `ℝ^{Fin n ⊕ Fin 1}` span a nondegenerate plane
of signature `(1,1)`; its orthogonal complement is positive definite of dimension `n - 1 ≥ 1`.
Here we produce a **unit** space-like vector `w` in that complement:

`⟨w, θ a⟩ = ⟨w, θ b⟩ = 0`, `⟨w,w⟩ = 1` (where `⟨·,·⟩ = mform`).

The vector `w` is the normalization of any nonzero vector `z` of the kernel of
`x ↦ (⟨x,θ a⟩, ⟨x,θ b⟩)`; the kernel is nonzero by rank–nullity, and the Minkowski form is
positive definite on it, which we read off from the orthogonal decomposition
`z = π_a z + (⟨z,η_a⟩/2) θ_a` of `StabHoroForm`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-! ## The kernel of the two `mform`-pairings -/

/-- The linear map `x ↦ (⟨x,θ a⟩, ⟨x,θ b⟩)`, whose kernel is the orthogonal complement of the
plane spanned by the two null vectors. -/
def perpMap (a b : E n) : (Fin n ⊕ Fin 1 → ℝ) →ₗ[ℝ] ℝ × ℝ where
  toFun x := (mform x (theta a), mform x (theta b))
  map_add' x y := by simp [mform_add_left]
  map_smul' c x := by simp [mform_smul_left, smul_eq_mul]

lemma finrank_prod_lt (hn : 2 ≤ n) :
    Module.finrank ℝ (ℝ × ℝ) < Module.finrank ℝ (Fin n ⊕ Fin 1 → ℝ) := by
  rw [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card,
      Fintype.card_sum, Fintype.card_fin, Fintype.card_unique]
  omega

/-- Rank–nullity: the kernel is nonzero for `n ≥ 2`. -/
lemma perpMap_ker_ne_bot (hn : 2 ≤ n) (a b : E n) : LinearMap.ker (perpMap a b) ≠ ⊥ :=
  LinearMap.ker_ne_bot_of_finrank_lt (finrank_prod_lt (n := n) hn)

/-! ## Positivity of the form on the kernel -/

/-- Reconstruction of a vector from its spatial and time parts. -/
lemma eq_elim_hspat_htime (x : Fin n ⊕ Fin 1 → ℝ) :
    x = Sum.elim (fun i => hspat x i) (fun _ => htime x) := by
  ext k
  rcases k with i | j
  · rfl
  · obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl

/-- The projection identity `z = π_a z + (⟨z,η_a⟩/2) θ_a` when `⟨z,θ_a⟩ = 0`. -/
lemma eq_horoProj_add {a : E n} {z : Fin n ⊕ Fin 1 → ℝ}
    (hza : mform z (theta a) = 0) :
    z = horoProj a z + (mform z (horoEta a) / 2) • theta a := by
  have h := horoProj_decomp a z
  rw [hza, zero_div, zero_smul, add_zero] at h
  exact h.symm

/-- On the hyperplane `⟨·,θ_a⟩ = 0` the Minkowski form is the Euclidean norm of `π_a`. -/
lemma mform_self_eq_hspat_horoProj {a : E n} (ha : a ∈ Sph n) {z : Fin n ⊕ Fin 1 → ℝ}
    (hza : mform z (theta a) = 0) :
    mform z z = ‖hspat (horoProj a z)‖ ^ 2 := by
  have hdec := eq_horoProj_add hza
  have hss : mform (horoProj a z) (horoProj a z) = ‖hspat (horoProj a z)‖ ^ 2 :=
    mform_eq_norm_sq_of_horoProj a ha (horoProj_idem a ha z)
  conv_lhs => rw [hdec]
  simp only [mform_add_left, mform_add_right, mform_smul_left, mform_smul_right, hss,
    mform_horoProj_theta a ha z, mform_theta_horoProj a ha z, mform_theta_theta_sph a ha]
  ring

/-! ## The main lemma -/

lemma perpNullUnit {n : ℕ} (hn : 2 ≤ n) {a b : Submission.Mostow.E n} (ha : a ∈ Submission.Mostow.Sph n)
    (hb : b ∈ Submission.Mostow.Sph n) (hab : a ≠ b) :
    ∃ w : Fin n ⊕ Fin 1 → ℝ, Work.Mostow.mform w (Work.Mostow.theta a) = 0 ∧
      Work.Mostow.mform w (Work.Mostow.theta b) = 0 ∧ Work.Mostow.mform w w = 1 := by
  obtain ⟨z, hzmem, hzne⟩ := (Submodule.ne_bot_iff _).mp (perpMap_ker_ne_bot hn a b)
  have hzk : perpMap a b z = 0 := (LinearMap.mem_ker).mp hzmem
  have hza : mform z (theta a) = 0 := congrArg Prod.fst hzk
  have hzb : mform z (theta b) = 0 := congrArg Prod.snd hzk
  have ha' : ‖a‖ = 1 := (mem_Sph_iff a).mp ha
  have hb' : ‖b‖ = 1 := (mem_Sph_iff b).mp hb
  -- the two null vectors `θ a` and `θ b` are not orthogonal: `⟨θ a, θ b⟩ = ⟨a,b⟩ - 1 ≠ 0`
  have hθθ : mform (theta a) (theta b) ≠ 0 := by
    rw [mform_theta_theta_pair]
    intro h
    exact hab ((inner_eq_one_iff_of_norm_eq_one ha' hb').mp (sub_eq_zero.mp h))
  -- the form is positive definite on the kernel
  have hkey := mform_self_eq_hspat_horoProj ha hza
  have hnorm_ne : hspat (horoProj a z) ≠ 0 := by
    intro h0
    have hs0 : horoProj a z = 0 := by
      rw [eq_elim_hspat_htime (horoProj a z), h0,
        htime_eq_zero_of_horoProj a ha (horoProj_idem a ha z)]
      ext k
      rcases k with i | j
      · simp
      · simp
    have hzq : z = (mform z (horoEta a) / 2) • theta a := by
      conv_lhs => rw [eq_horoProj_add hza]
      rw [hs0, zero_add]
    have hq : mform z (horoEta a) / 2 = 0 := by
      have h := hzb
      rw [hzq, mform_smul_left] at h
      exact (mul_eq_zero.mp h).resolve_right hθθ
    exact hzne (by conv_lhs => rw [hzq]; rw [hq, zero_smul])
  have hpos : 0 < mform z z := by
    rw [hkey]
    exact pow_pos (norm_pos_iff.mpr hnorm_ne) 2
  -- normalize
  set r : ℝ := Real.sqrt (mform z z) with hrdef
  have hrpos : 0 < r := by rw [hrdef]; exact Real.sqrt_pos.mpr hpos
  have hrne : r ≠ 0 := ne_of_gt hrpos
  have hr2 : r * r = mform z z := by
    rw [hrdef, ← sq, Real.sq_sqrt (le_of_lt hpos)]
  refine ⟨r⁻¹ • z, ?_, ?_, ?_⟩
  · rw [mform_smul_left, hza, mul_zero]
  · rw [mform_smul_left, hzb, mul_zero]
  · rw [mform_smul_left, mform_smul_right, ← hr2]
    field_simp

end

end Work.Mostow
