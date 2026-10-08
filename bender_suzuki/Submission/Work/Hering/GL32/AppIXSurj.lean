import Mathlib
import Submission.Work.Hering.GL32.AppIXM4
import Submission.Work.Hering.GL32.AppIXP0
import Submission.Work.Hering.GL32.AppIXTheta
import Submission.Work.Hering.GL32.rad_irreducible

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix IX: surjectivity of `combinedMap : W → k × V × V* × M₄`

`W = k[Ω]` is the permutation module of dimension `21` on the `21` pairs of points of `PG(2,2)`,
and `combinedMap = aug.prod (phi.prod (psi.prod theta))` is the product of the four natural maps
onto `k` (dim `1`), `V` (dim `3`), `V*` (dim `3`) and the trace-zero matrices `M₄` (dim `8`).

The proof is a three-step descent: `aug` is onto, `phi` is onto on `ker aug`, `psi` is onto on
`ker aug ∩ ker phi`, and `theta` is onto on `U₃ = ker aug ∩ ker phi ∩ ker psi` (the last step from
the irreducibility of `M₄`, `Work.Hering.GL32.rad_irreducible`).  The explicit vectors come from
three families of elements of `W`:

* `chiX x` : the `3` pairs whose two points sum to `x` (`aug = 1`, `phi = x`, `psi = theta = 0`),
* `chiL s` : the `3` pairs on the line `ker s` (`aug = 1`, `phi = 0`, `psi = s`, `theta = 0`),
* `chiA m z` : the `2` pairs on the line `ker m` containing the point `z` (`aug = 0`, `phi = z`,
  `psi = 0`, `theta = z ⊗ m`),
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Work.Hering.GL32

/-! ## The three families of elements of `W` -/

/-- The `3` pairs of points summing to `x`. -/
noncomputable def chiX (x : F2v) : W := fun p => if psum p = x then 1 else 0

/-- The `3` pairs lying on the line `ker s`. -/
noncomputable def chiL (s : Module.Dual (ZMod 2) F2v) : W := fun p => if pdF p = s then 1 else 0

/-- The `2` pairs on the line `ker m` that contain the point `z`. -/
noncomputable def chiA (m : Module.Dual (ZMod 2) F2v) (z : F2v) : W :=
  fun p => if pdF p = m ∧ psum p ≠ z then 1 else 0

/-- The coordinate functionals. -/
def f₀ : Module.Dual (ZMod 2) F2v := LinearMap.proj 0
def f₁ : Module.Dual (ZMod 2) F2v := LinearMap.proj 1
def f₂ : Module.Dual (ZMod 2) F2v := LinearMap.proj 2

lemma eq_sum_smul_e (v : F2v) : v 0 • e₀ + v 1 • e₁ + v 2 • e₂ = v := by
  funext i; fin_cases i <;> simp [e₀, e₁, e₂]

lemma eq_sum_smul_f (s : Module.Dual (ZMod 2) F2v) : s e₀ • f₀ + s e₁ • f₁ + s e₂ • f₂ = s := by
  apply LinearMap.ext
  intro x
  show (s e₀ • f₀ + s e₁ • f₁ + s e₂ • f₂) x = s x
  conv_rhs => rw [← eq_sum_smul_e x]
  rw [map_add, map_add, map_smul, map_smul, map_smul]
  rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
    LinearMap.smul_apply]
  simp only [f₀, f₁, f₂, LinearMap.proj_apply, e₀, e₁, e₂, Pi.smul_apply, Pi.add_apply,
    smul_eq_mul]
  ring

/-! ## The four steps -/

/-- `aug` is surjective. -/
lemma aug_surj (c : ZMod 2) : ∃ w : W, aug w = c := by
  refine ⟨c • (Pi.single p₀ (1 : ZMod 2)), ?_⟩
  rw [map_smul, aug_single, smul_eq_mul, mul_one]

lemma phi_lift_e₀ : ∃ u : W, aug u = 0 ∧ phi u = e₀ :=
  ⟨chiX (e₀ + e₂) + chiX e₂, by decide, by decide⟩
lemma phi_lift_e₁ : ∃ u : W, aug u = 0 ∧ phi u = e₁ :=
  ⟨chiX (e₀ + e₁) + chiX e₀, by decide, by decide⟩
lemma phi_lift_e₂ : ∃ u : W, aug u = 0 ∧ phi u = e₂ :=
  ⟨chiX (e₀ + e₂) + chiX e₀, by decide, by decide⟩

/-- `phi` is surjective on `ker aug`. -/
lemma phi_ker_aug_surj (v : F2v) : ∃ u : W, aug u = 0 ∧ phi u = v := by
  obtain ⟨u₀, ha₀, h₀⟩ := phi_lift_e₀
  obtain ⟨u₁, ha₁, h₁⟩ := phi_lift_e₁
  obtain ⟨u₂, ha₂, h₂⟩ := phi_lift_e₂
  refine ⟨v 0 • u₀ + v 1 • u₁ + v 2 • u₂, ?_, ?_⟩
  · rw [map_add, map_add, map_smul, map_smul, map_smul, ha₀, ha₁, ha₂]
    simp
  · rw [map_add, map_add, map_smul, map_smul, map_smul, h₀, h₁, h₂]
    exact eq_sum_smul_e v

lemma psi_lift_f₀ : ∃ u : W, aug u = 0 ∧ phi u = 0 ∧ psi u = f₀ :=
  ⟨chiL (f₀ + f₁) + chiL f₁, by decide, by decide, by decide⟩
lemma psi_lift_f₁ : ∃ u : W, aug u = 0 ∧ phi u = 0 ∧ psi u = f₁ :=
  ⟨chiL (f₀ + f₁) + chiL f₀, by decide, by decide, by decide⟩
lemma psi_lift_f₂ : ∃ u : W, aug u = 0 ∧ phi u = 0 ∧ psi u = f₂ :=
  ⟨chiL (f₂ + f₀) + chiL f₀, by decide, by decide, by decide⟩

/-- `psi` is surjective on `ker aug ∩ ker phi`. -/
lemma psi_ker_surj (s : Module.Dual (ZMod 2) F2v) :
    ∃ u : W, aug u = 0 ∧ phi u = 0 ∧ psi u = s := by
  obtain ⟨u₀, ha₀, hp₀, h₀⟩ := psi_lift_f₀
  obtain ⟨u₁, ha₁, hp₁, h₁⟩ := psi_lift_f₁
  obtain ⟨u₂, ha₂, hp₂, h₂⟩ := psi_lift_f₂
  refine ⟨s e₀ • u₀ + s e₁ • u₁ + s e₂ • u₂, ?_, ?_, ?_⟩
  · rw [map_add, map_add, map_smul, map_smul, map_smul, ha₀, ha₁, ha₂]
    simp
  · rw [map_add, map_add, map_smul, map_smul, map_smul, hp₀, hp₁, hp₂]
    simp
  · rw [map_add, map_add, map_smul, map_smul, map_smul, h₀, h₁, h₂]
    exact eq_sum_smul_f s

/-- `U₃ = ker aug ∩ ker phi ∩ ker psi`. -/
noncomputable def U3 : Submodule (ZMod 2) W := LinearMap.ker aug ⊓ LinearMap.ker phi ⊓
  LinearMap.ker psi

lemma mem_U3_iff {u : W} : u ∈ U3 ↔ aug u = 0 ∧ phi u = 0 ∧ psi u = 0 := by
  simp only [U3, Submodule.mem_inf, LinearMap.mem_ker]
  tauto

/-- `U₃` is invariant under the action of `GL(3,2)`. -/
lemma actW_mem_U3 (g : GL32) {u : W} (hu : u ∈ U3) : actW g u ∈ U3 := by
  rw [mem_U3_iff] at hu ⊢
  obtain ⟨h1, h2, h3⟩ := hu
  exact ⟨by rw [aug_actW, h1], by rw [phi_actW, h2, map_zero], by rw [psi_actW, h3, map_zero]⟩

/-- A nonzero element of `U₃` whose image under `theta` is nonzero. -/
lemma theta_lift_witness : ∃ u : W, u ∈ U3 ∧ theta u ≠ 0 := by
  have h1 : aug (chiA f₀ e₂ + chiA f₁ e₂) = 0 := by decide
  have h2 : phi (chiA f₀ e₂ + chiA f₁ e₂) = 0 := by decide
  have h3 : psi (chiA f₀ e₂ + chiA f₁ e₂) = 0 := by decide
  have h4 : theta (chiA f₀ e₂ + chiA f₁ e₂) ≠ 0 := by decide
  exact ⟨_, (mem_U3_iff).mpr ⟨h1, h2, h3⟩, h4⟩

/-- `theta` is surjective on `U₃ = ker aug ∩ ker phi ∩ ker psi`. -/
lemma theta_ker_surj (A : M4) :
    ∃ u : W, aug u = 0 ∧ phi u = 0 ∧ psi u = 0 ∧ theta u = A := by
  obtain ⟨u₀, hu₀, hθ₀⟩ := theta_lift_witness
  -- the image of `U₃` in matrices
  let S : Submodule (ZMod 2) Mat3 := (U3.map theta).map M4.subtype
  have huniq : ∀ x : Mat3, x ∈ S ↔ ∃ u ∈ U3, ((theta u : M4) : Mat3) = x := by
    intro x
    show x ∈ (U3.map theta).map M4.subtype ↔ _
    constructor
    · rintro ⟨B, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨theta u, ⟨u, hu, rfl⟩, rfl⟩
  have hA₀ : ((theta u₀ : M4) : Mat3) ∈ S := (huniq _).mpr ⟨u₀, hu₀, rfl⟩
  have htr : ∀ A ∈ S, A.trace = 0 := by
    intro A hA
    obtain ⟨u, -, rfl⟩ := (huniq A).mp hA
    exact (theta u).2
  have hinv : ∀ (g : GL32) (A : Mat3), A ∈ S →
      (LinearMap.toMatrix' (g : F2v →ₗ[ZMod 2] F2v)) * A *
        (LinearMap.toMatrix' ((g.symm : GL32) : F2v →ₗ[ZMod 2] F2v)) ∈ S := by
    intro g A hA
    obtain ⟨u, hu, rfl⟩ := (huniq A).mp hA
    rw [huniq]
    refine ⟨actW g u, actW_mem_U3 g hu, ?_⟩
    rw [theta_actW g u]
    rfl
  have hne : S ≠ ⊥ := by
    intro hbot
    rw [hbot] at hA₀
    exact hθ₀ (Subtype.ext (by simpa using hA₀))
  rcases rad_irreducible S htr hinv with hbot | htop
  · exact absurd hbot hne
  · obtain ⟨u, hu, huA⟩ := (huniq _).mp (htop ((A : M4) : Mat3) A.2)
    rw [mem_U3_iff] at hu
    exact ⟨u, hu.1, hu.2.1, hu.2.2, Subtype.ext huA⟩

/-- **Surjectivity of the combined map.** -/
theorem combined_surjective : Function.Surjective combinedMap := by
  rintro ⟨c, v, s, A⟩
  obtain ⟨w₁, hw₁⟩ := aug_surj c
  obtain ⟨u₁, ha₁, hφ₁⟩ := phi_ker_aug_surj (v - phi w₁)
  obtain ⟨u₂, ha₂, hp₂, hψ₂⟩ := psi_ker_surj (s - psi w₁ - psi u₁)
  obtain ⟨u₃, ha₃, hp₃, hq₃, hθ₃⟩ := theta_ker_surj (A - theta w₁ - theta u₁ - theta u₂)
  refine ⟨w₁ + u₁ + u₂ + u₃, ?_⟩
  have e1 : aug (w₁ + u₁ + u₂ + u₃) = c := by
    rw [map_add, map_add, map_add, hw₁, ha₁, ha₂, ha₃]
    simp
  have e2 : phi (w₁ + u₁ + u₂ + u₃) = v := by
    rw [map_add, map_add, map_add, hφ₁, hp₂, hp₃]
    abel
  have e3 : psi (w₁ + u₁ + u₂ + u₃) = s := by
    rw [map_add, map_add, map_add, hψ₂, hq₃]
    abel
  have e4 : theta (w₁ + u₁ + u₂ + u₃) = A := by
    rw [map_add, map_add, map_add, hθ₃]
    abel
  simp only [combinedMap, LinearMap.prod_apply]
  exact Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4))

end Work.Hering.GL32
