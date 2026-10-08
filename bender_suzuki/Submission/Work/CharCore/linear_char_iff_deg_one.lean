import Mathlib
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.irreducible_character_mem_Irr
import Submission.Work.CharCore.exists_irr_of_monoidHom

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.CharCore

theorem linear_char_iff_deg_one {G : Type*} [Group G] [Fintype G] {χ : G → ℂ} (hχ : χ ∈ Irr G) :
    irrDeg χ = 1 ↔ ∃ φ : G →* ℂˣ, ∀ g : G, χ g = (φ g : ℂ) := by
  classical
  constructor
  · intro hdeg
    obtain ⟨N, hN, hNχ⟩ := exists_mem_irrSubmodules_of_mem_Irr hχ
    have hfin : Module.finrank ℂ N = 1 := by
      rw [← irrDeg_eq_finrank hχ hN hNχ]; exact hdeg
    haveI hS : IsSimpleModule (groupAlgebra G) N := isSimpleModule_of_mem_irrSubmodules N hN
    haveI hnt : Nontrivial N := IsSimpleModule.nontrivial (groupAlgebra G) N
    obtain ⟨v, hv⟩ := exists_ne (0 : N)
    have hspan : ∀ w : N, ∃ cc : ℂ, cc • v = w :=
      (finrank_eq_one_iff_of_nonzero' v hv).mp hfin
    -- the scalar by which `g` acts on the line `ℂ • v`
    let c : G → ℂ := fun g => Classical.choose (hspan (submoduleRep N g v))
    have hc : ∀ g, c g • v = submoduleRep N g v := fun g =>
      Classical.choose_spec (hspan (submoduleRep N g v))
    have hscale : ∀ (g : G) (w : N), submoduleRep N g w = c g • w := by
      intro g w
      obtain ⟨d, hd⟩ := hspan w
      calc submoduleRep N g w = submoduleRep N g (d • v) := by rw [hd]
        _ = d • submoduleRep N g v := by rw [map_smul]
        _ = d • (c g • v) := by rw [hc g]
        _ = (d * c g) • v := by rw [smul_smul]
        _ = (c g * d) • v := by rw [mul_comm]
        _ = c g • (d • v) := by rw [smul_smul]
        _ = c g • w := by rw [hd]
    have hc_ne : ∀ g, c g ≠ 0 := by
      intro g hg
      have hzero : submoduleRep N g v = 0 := by rw [← hc g, hg, zero_smul]
      have hbij : Function.Injective ⇑(submoduleRep N g) :=
        (Representation.apply_bijective (submoduleRep N) g).1
      exact hv (hbij (by rw [hzero, map_zero]))
    have hc_one : c 1 = 1 := by
      have h : c 1 • v = (1 : ℂ) • v := by
        rw [hc 1, MonoidHom.map_one]
        simp
      exact smul_left_injective ℂ hv h
    have hc_mul : ∀ g h : G, c (g * h) = c g * c h := by
      intro g h
      apply smul_left_injective ℂ hv
      calc c (g * h) • v = submoduleRep N (g * h) v := hc (g * h)
        _ = submoduleRep N g (submoduleRep N h v) := by rw [map_mul]; rfl
        _ = submoduleRep N g (c h • v) := by rw [hc h]
        _ = c h • submoduleRep N g v := by rw [map_smul]
        _ = c h • (c g • v) := by rw [hc g]
        _ = (c h * c g) • v := by rw [smul_smul]
        _ = (c g * c h) • v := by rw [mul_comm]
    let φ : G →* ℂˣ :=
    { toFun := fun g => Units.mk0 (c g) (hc_ne g)
      map_one' := by
        apply Units.ext
        simp [hc_one]
      map_mul' := by
        intro g h
        apply Units.ext
        simp [hc_mul g h] }
    refine ⟨φ, fun g => ?_⟩
    rw [← hNχ]
    change LinearMap.trace ℂ N (submoduleRep N g) = (φ g : ℂ)
    have hρ : submoduleRep N g = c g • (1 : N →ₗ[ℂ] N) := by
      apply LinearMap.ext
      intro w
      rw [hscale g w]
      rfl
    rw [hρ, map_smul, LinearMap.trace_one, hfin, Nat.cast_one, smul_eq_mul, mul_one]
    exact (Units.val_mk0 (hc_ne g)).symm
  · rintro ⟨φ, hφ⟩
    have h1 : (irrDeg χ : ℂ) = 1 := by
      rw [← irrDeg_spec hχ, hφ 1]
      simp
    exact_mod_cast h1

end Work.CharCore
