import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Psi
import Submission.Work.HP.IntForm

/-!
# The cone region and the product-factors bound (node N13)

`Work.HP.coneRegion d n a α T` is the set `{x : ‖x‖ ≤ T, a ∈ 𝒞_{ν(x)}^{(α)}}` (a genuine cone in
`x`, since `ν` is homogeneous of degree `d`), and `Work.HP.coneRegionInt` is its set of integer
points.  Also collected here: the volume formula (`cone_volume`) restated for `coneRegion`, and the
equivalence with `Psi ≤ 0`.
-/

set_option autoImplicit false
noncomputable section
open Filter MeasureTheory Finset
open scoped BigOperators Pointwise

namespace Work.HP

/-- The cone region of radius `T`: the points `x` with `‖x‖ ≤ T` and `a ∈ 𝒞_{ν(x)}^{(α)}`. -/
def coneRegion (d n : ℕ) (a : Mon d n → ℤ) (α T : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {x | rNorm x ≤ T ∧ (toR a) ∈ Cgam (veronese d n x) α}

/-- The integer points of the cone region of radius `T`. -/
def coneRegionInt (d n : ℕ) (a : Mon d n → ℤ) (α T : ℝ) : Set (Fin (n + 1) → ℤ) :=
  {x | eNorm x ≤ T ∧ (toR a) ∈ Cgam (veronese d n (toR x)) α}

/-- `a ∈ 𝒞_{ν(x)}^{(α)}` is equivalent to `Ψ_a^{(α)}(x) ≤ 0`. -/
theorem coneRegion_eq_psi {d n : ℕ} (a : Mon d n → ℤ) {α : ℝ} (hα : 0 < α) (T : ℝ) :
    coneRegion d n a α T = {x | rNorm x ≤ T ∧ Psi d n a α x ≤ 0} := by
  ext x
  simp only [coneRegion, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨h.1, (Psi_nonpos_iff a hα x).mpr h.2⟩,
         fun h => ⟨h.1, (Psi_nonpos_iff a hα x).mp h.2⟩⟩

/-- Volume of the cone region: `vol {x : ‖x‖ ≤ T, a ∈ 𝒞_{ν(x)}^{(α)}} = T^{n+1} τ(a;α)/α`. -/
theorem volume_coneRegion (d n : ℕ) (a : Mon d n → ℤ) {α T : ℝ} (hα : 0 < α) (hT : 0 < T) :
    (volume (coneRegion d n a α T)).toReal = T ^ (n + 1) * tauArch d n (toR a) α / α :=
  cone_volume d n a hα hT

/-- The cone region is a cone: scaling `x` by a positive factor preserves membership. -/
theorem coneRegion_smul_mem {d n : ℕ} (a : Mon d n → ℤ) {α c T : ℝ} (hc : 0 < c)
    {x : Fin (n + 1) → ℝ} (hx : x ∈ coneRegion d n a α T) :
    (fun i => c * x i) ∈ coneRegion d n a α (c * T) := by
  refine ⟨?_, ?_⟩
  · rw [rNorm_const_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left hx.1 hc.le
  · exact (Cgam_veronese_const_mul a hc x).mpr hx.2

/-- The integer points counted by `NVloc`: primitive `v` with `‖v‖ ≤ R`, `W ∣ f_a(v)` and
`a ∈ 𝒞_{ν(v)}^{(α)}` (the index set of the sum in `NVloc`). -/
def primConeSet (d n : ℕ) (a : Mon d n → ℤ) (α R : ℝ) (W : ℕ) : Set (Fin (n + 1) → ℤ) :=
  {v | IsPrim v ∧ eNorm v ≤ R ∧ (W : ℤ) ∣ formEval d n a v ∧
    toR a ∈ Cgam (toR (veronese d n v)) α}

end Work.HP
