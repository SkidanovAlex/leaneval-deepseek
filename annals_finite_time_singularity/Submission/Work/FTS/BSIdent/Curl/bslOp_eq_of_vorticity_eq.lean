import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.Work.FTS.BSIdent.Curl
import Submission.Work.FTS.BSIdent.Curl.exists_mem_Uax_rho_theta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Real

namespace Work.FTS.BSIdent.Curl

/-- The unit angular vector `e_θ` does not vanish off the axis: it has norm one there. -/
theorem eTheta_ne_zero_of_mem_Uax {x : Work.FTS.BSIdent.R3} (hx : x ∈ Uax) :
    Work.Cyl.eTheta x ≠ 0 := by
  intro h
  have h1 : ‖Work.Cyl.eTheta x‖ = 1 :=
    Work.Cyl.norm_eTheta x (radial_ne_zero_of_mem_Uax hx)
  rw [h, norm_zero] at h1
  exact one_ne_zero h1.symm

/-- **The elliptic law from the curl identity.**  This is the converse of
`Work.FTS.BSIdent.vorticity_psiField_PhiOddSlice_of_pos`: if the vorticity of the stream-function
field of `ψ = ρ²a⁻¹F̂(ρ^p/b, θ)` is the re-signed physical profile `−(a⁻¹·profile p G)·e_θ`
everywhere on `Uax`, then `F` solves the paper's elliptic law with source `F_* + G` on the whole
open quadrant.

The point is that every `(w,θ)` with `w > 0`, `0 < θ < π/2` is the pair
`(ρ(x)^p/b, θ(x))` of some `x ∈ Uax` (`exists_mem_Uax_rho_theta`), and that the curl identity
`vorticity (psiField …) = −(a⁻¹·bslOp p F (ρ^p/b, θ))·e_θ` is available *unconditionally*
(no elliptic law needed) from `vorticity_psiField_scaled` together with the θ>0 branch of the odd
extension; the cancellation of the common scalar `a⁻¹` and of the nonvanishing vector
`e_θ(x)` then identifies `bslOp p F (w,θ)` with `profile p G w θ = F_* + G`. -/
theorem bslOp_eq_of_vorticity_eq {p a b : ℝ} (hp : 0 < p) (ha : 0 < a) (hb : 0 < b)
    {F G : ℝ → ℝ → ℝ}
    (hsm : ∀ w θ, 0 < w → 0 < θ → θ < π / 2 →
      ContDiffAt ℝ 2 (fun q : ℝ × ℝ => F q.1 q.2) (w, θ))
    (hvort : ∀ x ∈ Work.FTS.BSIdent.Uax,
      FiniteTimeSingularity.vorticity (Work.Cyl.psiField (fun r z => Work.Cyl.rhoP r z ^ 2 * a⁻¹ *
        Work.FTS.BSIdent.PhiOddSlice F (Work.Cyl.rhoP r z ^ p / b) (Work.Cyl.thetaP r z))) x
      = -(a⁻¹ * Work.ConstructionInstance.profile p G (Work.Cyl.rho x ^ p / b)
            (Work.Cyl.theta x)) • Work.Cyl.eTheta x) :
    ∀ w θ, 0 < w → 0 < θ → θ < π / 2 → Work.Elliptic.bslOp p F w θ
      = Work.Construction.Fstar p w θ + G w θ := by
  intro w θ hw hθ hθlt
  -- pick a point of `Uax` with polar coordinates `(w b)^{1/p}`, `θ`
  obtain ⟨x, hx, hrho, hth⟩ := exists_mem_Uax_rho_theta hp hb hw hθ hθlt
  have hθpos : 0 < Work.Cyl.theta x := by rw [hth]; exact hθ
  -- the "rhs" of the elliptic law at the unknown point, as a single profile
  set G' : ℝ → ℝ → ℝ :=
    fun w' θ' => Work.Elliptic.bslOp p F w' θ' - Work.Construction.Fstar p w' θ' with hG'def
  have hlaw : ∀ w' θ', 0 < w' → 0 < θ' → θ' < π / 2 →
      Work.Elliptic.bslOp p F w' θ' = Work.Construction.Fstar p w' θ' + G' w' θ' := by
    intro w' θ' _ _ _
    rw [hG'def]
    ring
  -- the curl identity at `x` computed with the *given* profile `G'` (no assumption used:
  -- `hlaw` holds by definition of `G'`)
  have hcurl := Work.FTS.BSIdent.vorticity_psiField_PhiOddSlice_of_pos (p := p) (a := a) (b := b)
    ha hb hlaw hsm hx hθpos
  -- and the curl identity at `x` computed with the *hypothesis* profile `G`
  have hv := hvort x hx
  rw [hcurl, hrho, hth] at hv
  -- cancel the scalar `a⁻¹` and the vector `e_θ(x)`
  have h3 : a⁻¹ * Work.ConstructionInstance.profile p G' w θ
      = a⁻¹ * Work.ConstructionInstance.profile p G w θ := by
    have h2 := (smul_left_injective ℝ (eTheta_ne_zero_of_mem_Uax hx)) hv
    exact neg_inj.mp h2
  have h4 : Work.ConstructionInstance.profile p G' w θ
      = Work.ConstructionInstance.profile p G w θ :=
    mul_left_cancel₀ (inv_ne_zero (ne_of_gt ha)) h3
  -- read both profiles in their `θ ≥ 0` branch
  have h5 : G' w θ = G w θ := by
    rw [Work.ConstructionInstance.profile_of_nonneg (le_of_lt hθ),
        Work.ConstructionInstance.profile_of_nonneg (le_of_lt hθ)] at h4
    simp only [hG'def] at h4
    linarith
  rw [hG'def] at h5
  linarith

end Work.FTS.BSIdent.Curl
