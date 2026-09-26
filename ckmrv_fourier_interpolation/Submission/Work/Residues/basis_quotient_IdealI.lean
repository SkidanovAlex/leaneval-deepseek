import Mathlib
import Submission.Work.Residues.Basic
import Submission.Work.Residues.XiTransfer
import Submission.Work.Modular.finrank_quotient_PSL
import Submission.Work.Modular.quotient_basis

namespace Work.Residues

open Work.Kernels

open scoped MonoidAlgebra MatrixGroups

/-- The transfer `Xi : ℂ[SL(2,ℤ)] →ₐ[ℂ] ℂ[Γ]` is surjective, because `toGamma` is (it is a
quotient map followed by an isomorphism) and `Xi` maps the basis monomials onto the basis
monomials of `ℂ[Γ]`. -/
lemma Xi_surjective' : Function.Surjective Xi := by
  intro y
  induction y using MonoidAlgebra.induction_on with
  | of δ =>
      obtain ⟨γ, rfl⟩ := toGamma_surjective δ
      exact ⟨MonoidAlgebra.of ℂ SL(2, ℤ) γ, Xi_of γ⟩
  | add y z hy hz =>
      obtain ⟨a, ha⟩ := hy
      obtain ⟨b, hb⟩ := hz
      exact ⟨a + b, by rw [map_add, ha, hb]⟩
  | smul c y hy =>
      obtain ⟨a, ha⟩ := hy
      exact ⟨c • a, by rw [map_smul, ha]⟩

/-- The transfer `Xi` carries the right ideal `𝓘 = (T-I)²R + S(T-I)²R` of `R = ℂ[SL(2,ℤ)]`
onto the right ideal `I = (T-I)²ℂ[Γ] + S(T-I)²ℂ[Γ]` of `ℂ[Γ]`. -/
lemma map_Xi_IdealI' : Submodule.map Xi.toLinearMap IdealI = Work.Modular.idealI := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨a, b, rfl⟩ := mem_span2.mp hx
    change Xi ((R_T - 1) ^ 2 * a + R_S * (R_T - 1) ^ 2 * b) ∈ Work.Modular.idealI
    have h1 : Xi ((R_T - 1) ^ 2 * a) = (Work.Modular.tR - 1) ^ 2 * Xi a := by
      rw [map_mul, map_pow, map_sub, Xi_R_T, map_one]
    have h2 : Xi (R_S * (R_T - 1) ^ 2 * b) =
        Work.Modular.sR * (Work.Modular.tR - 1) ^ 2 * Xi b := by
      rw [map_mul, map_mul, map_pow, map_sub, Xi_R_T, Xi_R_S, map_one]
    rw [map_add, h1, h2]
    exact Submodule.add_mem _ (Submodule.subset_span (Or.inl ⟨Xi a, rfl⟩))
      (Submodule.subset_span (Or.inr ⟨Xi b, rfl⟩))
  · refine Submodule.span_le.mpr ?_
    rintro y (⟨r, rfl⟩ | ⟨r, rfl⟩)
    · obtain ⟨a, ha⟩ := Xi_surjective' r
      refine ⟨(R_T - 1) ^ 2 * a, mem_span2.mpr ⟨a, 0, by rw [mul_zero, add_zero]⟩, ?_⟩
      change Xi ((R_T - 1) ^ 2 * a) = _
      rw [map_mul, map_pow, map_sub, Xi_R_T, map_one, ha]
    · obtain ⟨a, ha⟩ := Xi_surjective' r
      refine ⟨R_S * (R_T - 1) ^ 2 * a, mem_span2.mpr ⟨0, a, by rw [mul_zero, zero_add]⟩, ?_⟩
      change Xi (R_S * (R_T - 1) ^ 2 * a) = _
      rw [map_mul, map_mul, map_pow, map_sub, Xi_R_T, Xi_R_S, map_one, ha]

/-- **Paper Proposition 3.8(1)** in the form used by the kernels chapter: for
`R = ℂ[SL(2,ℤ)]` and `𝓘 = (T-I)²R + S(T-I)²R + (z-1)R`, `z = -I`, the images of
`1, T, TS, S, ST, STS` form a basis of `R/𝓘`. -/
theorem basis_quotient_IdealI :
    ∃ b : Module.Basis (Fin 6) ℂ (Work.Kernels.R ⧸ Work.Residues.idealI),
      ∀ i, b i = Submodule.mkQ Work.Residues.idealI (Work.Residues.M6 i) := by
  obtain ⟨bΓ, hbΓ⟩ := Work.Modular.quotient_basis
  -- the transfer is well defined on the quotients
  have hle : idealI ≤ Submodule.comap Xi.toLinearMap Work.Modular.idealI := by
    intro x hx
    rw [Submodule.mem_comap]
    rw [idealI] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    change Xi (y + z) ∈ Work.Modular.idealI
    rw [map_add]
    have hz0 : Xi z = 0 := by
      exact LinearMap.mem_ker.mp (by rw [Xi_ker]; exact hz)
    rw [hz0, add_zero]
    rw [← map_Xi_IdealI']
    exact Submodule.mem_map.mpr ⟨y, hy, rfl⟩
  -- and its kernel is exactly the ideal `𝓘`
  have hker_le : Submodule.comap Xi.toLinearMap Work.Modular.idealI ≤ idealI := by
    intro x hx
    rw [Submodule.mem_comap] at hx
    rw [← map_Xi_IdealI'] at hx
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp hx
    have hxy : x - y ∈ LinearMap.ker Xi.toLinearMap := by
      rw [LinearMap.mem_ker, map_sub, hyx, sub_self]
    rw [Xi_ker] at hxy
    rw [idealI]
    exact Submodule.mem_sup.mpr ⟨y, hy, x - y, hxy, by abel⟩
  -- the induced linear map `R/𝓘 → ℂ[Γ]/I`
  let F : (R ⧸ idealI) →ₗ[ℂ] (Work.Modular.GroupRing ⧸ Work.Modular.idealI) :=
    Submodule.mapQ idealI Work.Modular.idealI Xi.toLinearMap hle
  have hF : ∀ x : R, F (Submodule.mkQ idealI x) =
      Submodule.mkQ Work.Modular.idealI (Xi x) :=
    fun x => Submodule.mapQ_apply idealI Work.Modular.idealI Xi.toLinearMap x
  have hFinj : Function.Injective F := by
    intro a b hab
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective idealI a
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective idealI b
    rw [hF, hF] at hab
    have hmem : x - y ∈ idealI := by
      apply hker_le
      rw [Submodule.mem_comap]
      change Xi (x - y) ∈ Work.Modular.idealI
      have h1 : Submodule.mkQ Work.Modular.idealI (Xi x - Xi y) = 0 := by
        rw [map_sub, hab, sub_self]
      rw [← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
      exact h1
    rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmem
  have hFsurj : Function.Surjective F := by
    intro w
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective Work.Modular.idealI w
    obtain ⟨x, hx⟩ := Xi_surjective' y
    exact ⟨Submodule.mkQ idealI x, by rw [hF, hx]⟩
  let E : (R ⧸ idealI) ≃ₗ[ℂ] (Work.Modular.GroupRing ⧸ Work.Modular.idealI) :=
    LinearEquiv.ofBijective F ⟨hFinj, hFsurj⟩
  have hE : ∀ x : R, E (Submodule.mkQ idealI x) =
      Submodule.mkQ Work.Modular.idealI (Xi x) := fun x => hF x
  have hEM6 : ∀ i : Fin 6, E (Submodule.mkQ idealI (M6 i)) =
      Submodule.mkQ Work.Modular.idealI (Work.Modular.basisElem i) := by
    intro i
    rw [hE, Xi_M6]
  refine ⟨bΓ.map E.symm, fun i => ?_⟩
  rw [Module.Basis.map_apply, hbΓ i, ← hEM6 i, LinearEquiv.symm_apply_apply]

end Work.Residues
