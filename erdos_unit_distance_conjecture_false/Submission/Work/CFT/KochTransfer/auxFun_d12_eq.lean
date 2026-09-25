import Mathlib
import Submission.Work.CFT.KochTransfer.Defs

namespace Work.CFT.KochTransfer

/-- The inflation of the transgression candidate `candidate π σ hσ t` is the coboundary of
`auxFun π σ hσ t`: for every `invariantHoms p π` element `t` and every section `σ` of `π`,
`d₁₂ (auxFun t) = precompFun π (candidate t)` as functions `G × G → 𝔽_p`. -/
theorem auxFun_d12_eq {p : ℕ} {G : Type} [Group G] {Q : Type} [Group Q] (π : G →* Q)
    (σ : Q → G) (hσ : ∀ q, π (σ q) = q) (t : Work.CFT.KochTransfer.invariantHoms p π) :
    (groupCohomology.d₁₂ (Rep.trivial (ZMod p) G (ZMod p))).hom
        (Work.CFT.KochTransfer.auxFun p π σ hσ t) =
      Work.CFT.KochTransfer.precompFun π
        (Work.CFT.KochTransfer.candidate p π σ hσ t) := by
  funext gh
  obtain ⟨g, h⟩ := gh
  -- The element identity: `g h (σ (π g π h))⁻¹` is the product of the `g`-conjugate of
  -- `h (σ (π h))⁻¹`, of `g (σ (π g))⁻¹` and of the factor set `σ (π g) σ (π h) (σ (π g π h))⁻¹`.
  have key : (⟨g * h * (σ (π g * π h))⁻¹, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσ]; simp⟩ : π.ker)
      = conjKer π g ⟨h * (σ (π h))⁻¹, by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hσ]; simp⟩
        * ⟨g * (σ (π g))⁻¹, by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hσ]; simp⟩
        * ⟨σ (π g) * σ (π h) * (σ (π g * π h))⁻¹, by
            rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hσ, hσ, hσ]; simp⟩ := by
    apply Subtype.ext
    show g * h * (σ (π g * π h))⁻¹
        = g * (h * (σ (π h))⁻¹) * g⁻¹ * (g * (σ (π g))⁻¹)
          * (σ (π g) * σ (π h) * (σ (π g * π h))⁻¹)
    group
  have h1 : t ⟨g * h * (σ (π g * π h))⁻¹, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hσ]; simp⟩
      = t (conjKer π g ⟨h * (σ (π h))⁻¹, by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hσ]; simp⟩)
        + t ⟨g * (σ (π g))⁻¹, by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hσ]; simp⟩
        + t ⟨σ (π g) * σ (π h) * (σ (π g * π h))⁻¹, by
            rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hσ, hσ, hσ]; simp⟩ := by
    rw [key, invariantHoms_add, invariantHoms_add]
  simp only [groupCohomology.d₁₂_hom_apply, precompFun_apply, candidate_apply, auxFun_apply,
    map_mul]
  rw [Representation.trivial_apply]
  show t ⟨h * (σ (π h))⁻¹, by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hσ]; simp⟩
      - t ⟨g * h * (σ (π g * π h))⁻¹, by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hσ]; simp⟩
      + t ⟨g * (σ (π g))⁻¹, by
            rw [MonoidHom.mem_ker, map_mul, map_inv, hσ]; simp⟩
    = - t ⟨σ (π g) * σ (π h) * (σ (π g * π h))⁻¹, by
            rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hσ, hσ, hσ]; simp⟩
  rw [h1, invariantHoms_conj]
  abel

end Work.CFT.KochTransfer
