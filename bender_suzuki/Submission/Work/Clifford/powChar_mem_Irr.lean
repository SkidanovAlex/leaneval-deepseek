import Mathlib
import Submission.Work.Clifford.exists_aut_of_isPrimitiveRoot_pow
import Submission.Work.Clifford.galois_char_apply
import Submission.Work.Clifford.CFun
import Submission.Work.Clifford.cfInner_eq_ite_of_mem_Irr
import Submission.Work.Coherence.char_inv_eq_conj
import Submission.Work.Coherence.NormIrr
import Submission.Work.CharCore.Coherence
import Submission.Work.CharCore.isVChar_iff

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.powChar_mem_Irr`

The Frobenius/power twist `χ ↦ (g ↦ χ (g ^ k))` of an irreducible complex character of a
finite group `G` is again irreducible, provided `k` is coprime to `|G|`.

Mathematically this is the classical fact that the power map on character values is given by
the Galois action of `Gal(ℚ(ζ_|G|)/ℚ)`: if `σ : ℂ ≃+* ℂ` is a ring automorphism sending a
primitive `|G|`-th root of unity `ζ` to `ζ ^ k`, then `σ (χ g) = χ (g ^ k)`
(`Work.Clifford.galois_char_apply`), and `g ↦ σ (χ g)` is the character of the Galois twist of
any representation affording `χ`, hence again irreducible.

The two ingredients are therefore

* the existence of `σ` (`Work.Clifford.exists_aut_of_isPrimitiveRoot_pow`, whose hypothesis is
  exactly `k` coprime to the order of `G`), and
* the fact that a Galois twist of an irreducible character is irreducible, proved here:
  twisting the matrix of `ρ g` entrywise by `σ` gives a representation `W'` whose character is
  `g ↦ σ (χ g)`; its norm is `⟨χ, χ⟩ = 1` because `σ` is multiplicative, and a virtual
  character of norm one is `±` an irreducible character, of which only `+` is possible for
  degree reasons.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Classical

namespace Work.Clifford

/-! ### The entrywise `σ`-twist of an endomorphism matrix -/

section TwistEnd

variable {M : Type*} [AddCommGroup M] [Module ℂ M]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The `σ`-twist of an endomorphism, transported to coordinates via a basis `b`: the conjugate
of `f` by the `σ`-semilinear change of scalars, realized on `ι → ℂ` as the entrywise `σ`-image
of the matrix of `f`. -/
noncomputable def pcTwistFun (σ : ℂ ≃+* ℂ) (b : Module.Basis ι ℂ M) (f : M →ₗ[ℂ] M) :
    (ι → ℂ) →ₗ[ℂ] (ι → ℂ) :=
  Matrix.toLin' ((LinearMap.toMatrix b b f).map (σ : ℂ →+* ℂ))

theorem pcTwistFun_one (σ : ℂ ≃+* ℂ) (b : Module.Basis ι ℂ M) :
    pcTwistFun σ b 1 = 1 := by
  rw [pcTwistFun, LinearMap.toMatrix_one,
    Matrix.map_one (σ : ℂ →+* ℂ) (map_zero σ) (map_one σ), Matrix.toLin'_one]
  rfl

theorem pcTwistFun_mul (σ : ℂ ≃+* ℂ) (b : Module.Basis ι ℂ M) (f g : M →ₗ[ℂ] M) :
    pcTwistFun σ b (f * g) = pcTwistFun σ b f * pcTwistFun σ b g := by
  rw [pcTwistFun, pcTwistFun, pcTwistFun, LinearMap.toMatrix_mul, Matrix.map_mul,
    Matrix.toLin'_mul]
  rfl

/-- The `σ`-twist as a monoid homomorphism of endomorphism rings. -/
noncomputable def pcTwistHom (σ : ℂ ≃+* ℂ) (b : Module.Basis ι ℂ M) :
    (M →ₗ[ℂ] M) →* ((ι → ℂ) →ₗ[ℂ] (ι → ℂ)) where
  toFun := pcTwistFun σ b
  map_one' := pcTwistFun_one σ b
  map_mul' := pcTwistFun_mul σ b

@[simp] theorem pcTwistHom_apply (σ : ℂ ≃+* ℂ) (b : Module.Basis ι ℂ M) (f : M →ₗ[ℂ] M) :
    pcTwistHom σ b f = pcTwistFun σ b f := rfl

end TwistEnd

/-! ### The Galois twist of a representation -/

section Main

variable {G : Type*} [Group G] [Fintype G]

/-- Applying a ring automorphism `σ` of `ℂ` entrywise to a matrix representation gives a
representation whose character is `σ` applied to the original character. -/
theorem exists_fdRep_char_galoisTwist (σ : ℂ ≃+* ℂ) (V : FDRep ℂ G) :
    ∃ W' : FDRep ℂ G, W'.character = fun g => σ (V.character g) := by
  classical
  let b := Module.finBasis ℂ ↥V.V
  let ρ' : Representation ℂ G (Fin (Module.finrank ℂ ↥V.V) → ℂ) :=
    (pcTwistHom σ b).comp V.ρ
  refine ⟨FDRep.of ρ', ?_⟩
  have hchar : ∀ g : G, (FDRep.of ρ').character g = σ (V.character g) := by
    intro g
    show LinearMap.trace ℂ (Fin (Module.finrank ℂ ↥V.V) → ℂ) ((FDRep.of ρ').ρ g)
      = σ (V.character g)
    rw [FDRep.of_ρ']
    show LinearMap.trace ℂ (Fin (Module.finrank ℂ ↥V.V) → ℂ)
      (Matrix.toLin' ((LinearMap.toMatrix b b (V.ρ g)).map (σ : ℂ →+* ℂ)))
      = σ (V.character g)
    rw [Matrix.trace_toLin'_eq]
    have h1 : ((LinearMap.toMatrix b b (V.ρ g)).map (σ : ℂ →+* ℂ)).trace
        = (σ : ℂ →+* ℂ) ((LinearMap.toMatrix b b (V.ρ g)).trace) :=
      (AddMonoidHom.map_trace (σ : ℂ →+* ℂ) (LinearMap.toMatrix b b (V.ρ g))).symm
    rw [h1]
    have h2 : (LinearMap.toMatrix b b (V.ρ g)).trace = V.character g :=
      (LinearMap.trace_eq_matrix_trace ℂ b (V.ρ g)).symm
    rw [h2]
    exact congrFun (RingEquiv.coe_toRingHom σ) (V.character g)
  exact funext hchar

/-- **The Galois twist of an irreducible character is irreducible.** -/
theorem galoisTwist_mem_Irr (σ : ℂ ≃+* ℂ) {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    (fun g => σ (χ g)) ∈ Irr G := by
  obtain ⟨V, hV, hVχ⟩ := mem_Irr.mp hχ
  haveI : CategoryTheory.Simple V := hV
  obtain ⟨W', hW'⟩ := exists_fdRep_char_galoisTwist σ V
  have hchar : W'.character = fun g => σ (χ g) := by rw [hW', hVχ]
  -- `W'` is a class function
  have hclass : Work.CharCore.IsClassFun W'.character := fun g h => FDRep.char_conj W' g h
  -- hence a virtual character, since all its multiplicities are dimensions of intertwining spaces
  have hvchar : Work.CharCore.IsVChar W'.character := by
    rw [Work.CharCore.isVChar_iff hclass]
    intro ψ hψ
    obtain ⟨Vψ, hVψ, hVψχ⟩ := (Work.CharCore.mem_Irr_iff_fdrep ψ).mp hψ
    haveI : CategoryTheory.Simple Vψ := hVψ
    refine ⟨(Module.finrank ℂ (Vψ ⟶ W') : ℤ), ?_⟩
    have hstar : ∀ g : G, starRingEnd ℂ (ψ g) = ψ g⁻¹ := by
      intro g
      rw [← hVψχ]
      exact (Work.Coherence.char_inv_eq_conj Vψ g).symm
    have hinner : Work.CharCore.cfInner W'.character ψ
        = (Module.finrank ℂ (Vψ ⟶ W') : ℂ) := by
      rw [Work.CharCore.cfInner_eq_coherence, Work.Coherence.cfInner_apply]
      have hsum : (∑ g : G, W'.character g * starRingEnd ℂ (ψ g))
          = ∑ g : G, W'.character g * Vψ.character g⁻¹ := by
        refine Finset.sum_congr rfl fun g _ => by rw [hstar g, hVψχ]
      rw [hsum, Fintype.card_eq_nat_card]
      exact FDRep.scalar_product_char_eq_finrank_equivariant Vψ W'
    rw [hinner]
    push_cast
    ring
  -- and its norm is `1`
  have hnorm : Work.Coherence.cfInner W'.character W'.character = 1 := by
    have hstarχ : ∀ g : G, starRingEnd ℂ (χ g) = χ g⁻¹ := by
      intro g
      rw [← hVχ]
      exact (Work.Coherence.char_inv_eq_conj V g).symm
    have hkey : (Fintype.card G : ℂ)⁻¹ * (∑ g : G, χ g * χ g⁻¹) = cfInner χ χ := by
      rw [cfInner_apply]
      congr 1
      exact Finset.sum_congr rfl fun g _ => by rw [hstarχ g]
    calc Work.Coherence.cfInner W'.character W'.character
        = (Fintype.card G : ℂ)⁻¹ * ∑ g : G, W'.character g * W'.character g⁻¹ := by
          rw [Work.Coherence.cfInner_apply]
          congr 1
          exact Finset.sum_congr rfl fun g _ => by
            rw [(Work.Coherence.char_inv_eq_conj W' g).symm]
      _ = (Fintype.card G : ℂ)⁻¹ * σ (∑ g : G, χ g * χ g⁻¹) := by
          congr 1
          rw [map_sum]
          exact Finset.sum_congr rfl fun g _ => by rw [hchar, map_mul]
      _ = σ ((Fintype.card G : ℂ)⁻¹ * ∑ g : G, χ g * χ g⁻¹) := by
          rw [map_mul, map_inv₀, map_natCast]
      _ = σ (cfInner χ χ) := by rw [hkey]
      _ = σ 1 := by rw [cfInner_eq_ite_of_mem_Irr hχ hχ]; simp
      _ = 1 := map_one σ
  have hvchar' : Work.Coherence.IsVChar W'.character :=
    (Work.CharCore.IsVChar_iff_coherence W'.character).mp hvchar
  obtain ⟨ψ, hψ, hcase⟩ := Work.Coherence.vchar_norm_one hvchar' hnorm
  obtain ⟨m, hmpos, hm⟩ := Work.Coherence.irr_degree_pos hχ
  have hchar1 : W'.character 1 = (m : ℂ) := by
    rw [congrFun hchar 1, hm, map_natCast]
  rcases hcase with h | h
  · rw [← hchar, h]
    exact hψ
  · exfalso
    obtain ⟨n, hnpos, hn⟩ := Work.Coherence.irr_degree_pos hψ
    have heq : (m : ℂ) = -(n : ℂ) := by
      rw [← hchar1, h]
      show -(ψ 1) = -(n : ℂ)
      rw [hn]
    have hre : (m : ℝ) = -(n : ℝ) := by
      have h' := congrArg Complex.re heq
      simpa using h'
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmpos
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
    linarith

end Main

/-! ### The target -/

/-- The Frobenius twist `powChar k χ` of an irreducible character is irreducible when `k` is
coprime to `|G|`. -/
theorem powChar_mem_Irr {G : Type*} [Group G] [Fintype G] {k : ℕ} (hk : k.Coprime (Nat.card G))
    {χ : G → ℂ} (hχ : χ ∈ Work.Clifford.Irr G) :
    Work.Clifford.powChar k χ ∈ Work.Clifford.Irr G := by
  haveI : NeZero (Nat.card G) := ⟨(Nat.card_pos (α := G)).ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ (Nat.card G)
  have hk' : k.Coprime (Nat.card G) := hk
  obtain ⟨σ, hσ⟩ := exists_aut_of_isPrimitiveRoot_pow (Nat.card_pos (α := G)) hζ hk'
  have hpow : powChar k χ = fun g => σ (χ g) := by
    funext g
    rw [powChar]
    exact (galois_char_apply (Nat.card_pos (α := G)) hζ dvd_rfl σ hσ hχ g).symm
  rw [hpow]
  exact galoisTwist_mem_Irr σ hχ

end Work.Clifford
