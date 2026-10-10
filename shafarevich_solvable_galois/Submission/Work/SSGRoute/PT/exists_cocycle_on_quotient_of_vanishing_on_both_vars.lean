import Mathlib.Tactic.Abel
import Mathlib.Tactic.Group
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Topology.Algebra.Group.Quotient
import Submission.Work.SSGRoute.PT.FixedPointsAction
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Descent of a `2`-cocycle vanishing on `Γ × V` and on `V × Γ`

Let `Γ` be a topological group, `V ⊴ Γ` a normal subgroup and `c` a `2`-cocycle with values in a
`ZMod p`-module `N` which vanishes on `Γ × V` and on `V × Γ`.  Then `c` is right-`V`-invariant in
both variables, takes values in the fixed points `N^V`, and hence descends to a `2`-cocycle `c₀` of
the quotient `Γ ⧸ V` with values in `N^V`:

* `Work.SSGRoute.PT.exists_cocycle_on_quotient_of_vanishing_on_both_vars`.
-/

namespace Work.SSGRoute.PT

open _root_.SSGRoute

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

theorem exists_cocycle_on_quotient_of_vanishing_on_both_vars
    (p : ℕ) [Fact p.Prime] {Γ N : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup N] [Module (ZMod p) N]
    [DistribMulAction Γ N] [SMulCommClass Γ (ZMod p) N] [Finite N]
    (V : Subgroup Γ) (hVn : V.Normal)
    (c : Γ → Γ → N) (hc : SSGRoute.IsCocycle2 (MonoidHom.id Γ) c)
    (hlc : SSGRoute.IsLocConst2 c)
    (hvan1 : ∀ g : Γ, ∀ v ∈ V, c g v = 0) (hvan2 : ∀ v ∈ V, ∀ h : Γ, c v h = 0) :
    ∃ c₀ : (Γ ⧸ V) → (Γ ⧸ V) → ↥(Work.SSGRoute.PT.fixedPoints p N V),
      SSGRoute.IsCocycle2 (MonoidHom.id (Γ ⧸ V)) c₀ ∧
      SSGRoute.IsLocConst2 c₀ ∧
      (∀ g h : Γ, c g h = (c₀ (QuotientGroup.mk' V g) (QuotientGroup.mk' V h) : N)) := by
  classical
  haveI hVnI : V.Normal := hVn
  -- ## right-`V`-invariance in the second variable
  have hinv2 : ∀ g h : Γ, ∀ v ∈ V, c g (h * v) = c g h := by
    intro g h v hv
    have h1 := hc g h v
    simp only [MonoidHom.id_apply] at h1
    rw [hvan1 h v hv, hvan1 (g * h) v hv] at h1
    have h2 : c g (h * v) - c g h = 0 := by simpa using h1
    exact sub_eq_zero.mp h2
  -- ## right-`V`-invariance in the first variable
  have hinv1 : ∀ g h : Γ, ∀ v ∈ V, c (g * v) h = c g h := by
    intro g h v hv
    have h1 := hc g v h
    simp only [MonoidHom.id_apply] at h1
    have h3 : c g (v * h) = c g h := by
      have h2 : v * h = h * (h⁻¹ * v * h) := by group
      rw [h2, hinv2 g h (h⁻¹ * v * h) (by simpa using hVnI.conj_mem v hv h⁻¹)]
    rw [hvan2 v hv h, hvan1 g v hv, h3, smul_zero] at h1
    -- `h1 : 0 - c (g * v) h + c g h - 0 = 0`
    have h4 : c g h - c (g * v) h = 0 := by
      have h1' : c g h - c (g * v) h = 0 - c (g * v) h + c g h - 0 := by abel
      rw [h1']
      exact h1
    exact (sub_eq_zero.mp h4).symm
  -- ## values lie in the fixed points
  have hfix : ∀ g h : Γ, ∀ v ∈ V, v • c g h = c g h := by
    intro g h v hv
    have h1 := hc v g h
    simp only [MonoidHom.id_apply] at h1
    rw [hvan2 v hv (g * h), hvan2 v hv g] at h1
    have h2 : v • c g h - c (v * g) h = 0 := by simpa using h1
    have h2' : c (v * g) h = c g h := by
      have h3 := hinv1 g h (g⁻¹ * v * g) (by simpa using hVnI.conj_mem v hv g⁻¹)
      rwa [show g * (g⁻¹ * v * g) = v * g from by group] at h3
    rw [h2'] at h2
    exact sub_eq_zero.mp h2
  -- ## representatives of the classes are right `V`-translates
  have out_mem_V : ∀ g : Γ, ∃ v ∈ V, Quotient.out (QuotientGroup.mk' V g) = g * v := by
    intro g
    refine ⟨g⁻¹ * Quotient.out (QuotientGroup.mk' V g), ?_, by group⟩
    have h1 : ((Quotient.out (QuotientGroup.mk' V g) : Γ) : Γ ⧸ V) = (g : Γ ⧸ V) := by
      rw [QuotientGroup.out_eq', QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq).mp h1.symm
  have out_eq_c : ∀ g h : Γ,
      c (Quotient.out (QuotientGroup.mk' V g)) (Quotient.out (QuotientGroup.mk' V h)) = c g h := by
    intro g h
    obtain ⟨v, hv, hveq⟩ := out_mem_V g
    obtain ⟨w, hw, hweq⟩ := out_mem_V h
    rw [hveq, hweq, hinv2 (g * v) h w hw, hinv1 g h v hv]
  -- ## the descended cocycle
  let c₀ : (Γ ⧸ V) → (Γ ⧸ V) → ↥(Work.SSGRoute.PT.fixedPoints p N V) :=
    fun q q' => ⟨c (Quotient.out q) (Quotient.out q'), fun v hv => hfix _ _ v hv⟩
  have hc₀mk : ∀ g h : Γ, ((c₀ (QuotientGroup.mk' V g) (QuotientGroup.mk' V h)) : N) = c g h := by
    intro g h
    show c (Quotient.out (QuotientGroup.mk' V g)) (Quotient.out (QuotientGroup.mk' V h)) = c g h
    exact out_eq_c g h
  refine ⟨c₀, ?_, ?_, ?_⟩
  · -- the cocycle identity
    intro q q' q''
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective V q
    obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective V q'
    obtain ⟨g'', rfl⟩ := QuotientGroup.mk'_surjective V q''
    apply Subtype.ext
    simp only [Submodule.coe_sub, Submodule.coe_add, Submodule.coe_zero, MonoidHom.id_apply,
      smul_fixedPoints_coe, quotientActionHom_mk_apply, ← map_mul, hc₀mk]
    exact hc g g' g''
  · -- local constancy
    obtain ⟨U, hUopen, hUinv⟩ := hlc
    have hinvU1 : ∀ (u : Γ), u ∈ U → ∀ g h : Γ, c (g * u) h = c g h := by
      intro u hu g h
      have h1 := hUinv g h u 1 hu U.one_mem
      simpa using h1
    have hinvU2 : ∀ (u : Γ), u ∈ U → ∀ g h : Γ, c g (h * u) = c g h := by
      intro u hu g h
      have h1 := hUinv g h 1 u U.one_mem hu
      simpa using h1
    have hmk : (QuotientGroup.mk' V : Γ → Γ ⧸ V) = QuotientGroup.mk :=
      funext (QuotientGroup.mk'_apply V)
    have hopen : IsOpenMap (QuotientGroup.mk' V) := by
      rw [hmk]
      exact QuotientGroup.isOpenQuotientMap_mk.isOpenMap
    refine ⟨Subgroup.map (QuotientGroup.mk' V) U, ?_, ?_⟩
    · exact hopen U hUopen
    · intro q q' u v hu hv
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective V q
      obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective V q'
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hv
      have hmul1 : QuotientGroup.mk' V g * QuotientGroup.mk' V x
          = QuotientGroup.mk' V (g * x) := by rw [map_mul]
      have hmul2 : QuotientGroup.mk' V g' * QuotientGroup.mk' V y
          = QuotientGroup.mk' V (g' * y) := by rw [map_mul]
      rw [hmul1, hmul2]
      apply Subtype.ext
      rw [hc₀mk (g * x) (g' * y), hc₀mk g g',
        hinvU1 x hx g (g' * y), hinvU2 y hy g g']
  · -- the coercion identity
    intro g h
    exact (hc₀mk g h).symm

end Work.SSGRoute.PT
