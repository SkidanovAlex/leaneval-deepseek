import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.linear_char_iff_deg_one
import Submission.Work.BrauerSuzuki.Q8.exists_sylow_element_not_commuting
import Submission.Work.BrauerSuzuki.Q8.Cstar_Nstar_Astar

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8

/-- In any commutative group the commutator `a b a⁻¹ b⁻¹` is trivial. -/
private lemma comm_mul_inv_eq_one {M : Type*} [CommGroup M] (a b : M) :
    a * b * a⁻¹ * b⁻¹ = 1 := by
  rw [mul_assoc a b a⁻¹, mul_comm b a⁻¹, ← mul_assoc a a⁻¹ b, mul_inv_cancel, one_mul,
    mul_inv_cancel]

/-- **Step 9, degree two**: if `S` is a Sylow 2-subgroup which is `Q₈` (generalized quaternion
with `n = 2`) and `x ∈ S` has order `4`, then every irreducible character `χ` of `G` that does
*not* contain `x ^ 2` in its kernel (i.e. `χ (x ^ 2) ≠ χ 1`) has degree at least `2`.

Indeed `x ^ 2` is the unique involution `z = τ ^ 2 = [τ, ρ]` of `S ≅ Q₈`; in particular it is a
commutator of `S`, hence of `G`, so every *linear* character of `G` (i.e. every monoid
homomorphism `G → ℂˣ`) is trivial at `x ^ 2`.  A character of degree `1` would therefore
satisfy `χ (x ^ 2) = χ 1`, contradicting the hypothesis. -/
theorem step9_deg_two {G : Type*} [Group G] [Fintype G] (S : Sylow 2 G)
    (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hx4 : orderOf x = 4) {χ : G → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr G) (hne : χ (x ^ 2) ≠ χ 1) :
    2 ≤ Work.CharCore.irrDeg χ := by
  classical
  by_contra hlt
  -- A character of degree `0 < d` with `¬ 2 ≤ d` has degree `1`, hence is linear.
  have hdeg : Work.CharCore.irrDeg χ = 1 := by
    have := Work.CharCore.irrDeg_pos hχ
    omega
  obtain ⟨φ, hφ⟩ := (Work.CharCore.linear_char_iff_deg_one hχ).mp hdeg
  -- `x` as an element of the Sylow subgroup `S`.
  let y : ↥S := ⟨x, hxS⟩
  have hy4 : orderOf y = 4 := by
    rw [← Subgroup.orderOf_coe y]
    exact hx4
  -- The unique involution of `S ≅ Q₈` is `τ ^ 2 ^ (n-1)`.
  obtain ⟨-, -, -, huniq, -⟩ := Work.BrauerSuzuki.Quaternion.genQuaternionData_basic d
  have hy4' : y ^ 4 = 1 := by rw [← hy4]; exact pow_orderOf_eq_one y
  have hy2sq : (y ^ 2) ^ 2 = 1 := by rw [← pow_mul]; norm_num; exact hy4'
  have hy2ne : y ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hy4] at hdvd
    omega
  have ho2 : orderOf (y ^ 2) = 2 := by
    have hdvd : orderOf (y ^ 2) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2sq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy2ne
    · exact h
  have hy2eq : y ^ 2 = d.tau ^ (2 ^ (d.n - 1)) := huniq (y ^ 2) ho2
  -- The commuting relation `ρ τ⁻¹ ρ⁻¹ = τ`.
  have h1 : d.rho * d.tau⁻¹ * d.rho⁻¹ = d.tau := by
    have h := congr_arg (fun t => t⁻¹) d.rho_conj
    simp only [mul_inv_rev, inv_inv] at h
    rwa [← mul_assoc] at h
  -- `τ ^ 2 ^ (n-1)` is the commutator `[τ, ρ]`.
  have hcomm : d.tau * d.rho * d.tau⁻¹ * d.rho⁻¹ = d.tau ^ (2 ^ (d.n - 1)) := by
    rw [show d.tau * d.rho * d.tau⁻¹ * d.rho⁻¹
          = d.tau * (d.rho * d.tau⁻¹ * d.rho⁻¹) by group, h1]
    have hexp : 2 ^ (d.n - 1) = 2 := by rw [h2]; norm_num
    rw [hexp, ← pow_two]
  -- `x ^ 2` is that involution in `G`.
  have hxz : x ^ 2 = ((d.tau ^ (2 ^ (d.n - 1)) : ↥S) : G) := by
    have h := congrArg (Subtype.val) hy2eq
    simpa [y] using h
  have hx2comm : x ^ 2 = (d.tau : G) * (d.rho : G) * (d.tau : G)⁻¹ * (d.rho : G)⁻¹ := by
    rw [hxz, ← hcomm]
    simp
  -- A homomorphism to the abelian group `ℂˣ` kills the commutator.
  have hphi1 : φ (x ^ 2) = 1 := by
    rw [hx2comm, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact comm_mul_inv_eq_one (φ (d.tau : G)) (φ (d.rho : G))
  have hχeq : χ (x ^ 2) = χ 1 := by
    rw [hφ (x ^ 2), hφ 1, hphi1]
    simp
  exact hne hχeq

end Work.BrauerSuzuki.Q8
