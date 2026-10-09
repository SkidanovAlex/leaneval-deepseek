import Mathlib
import Submission.Work.LocalFields.Basic
import Submission.Work.LocalFields.CompletionLocalField
import Submission.Work.LocalFields.LocalFieldAPI
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.LocalFields

open scoped NumberField Valued WithZero

/-- Let `K_v` be the completion of a number field at a finite prime, and let `μ` be a
`ℤᐧ = WithZero (Multiplicative ℤ)`-valued valuation on `K_v` which is trivial on the units
`{x : Valued.v x = 1}`.  If moreover `μ` is *nontrivial on small elements*
(`∃ z ≠ 0, Valued.v z < 1 ∧ μ z < 1`), then `μ` is equivalent to the canonical valuation
`Valued.v`.

Proof sketch: let `π := Work.LocalFields.IsLocalField.uniformizer (k := K_v)`, which is
irreducible, generates `𝔪[K_v]`, and satisfies `Valued.v (π : K_v) < 1`
(`Work.LocalFields.mem_maximalIdeal_iff_v_lt_one`, `maximalIdeal_eq_span_uniformizer`).
By `IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible` (with
`R = 𝒪[K_v]`, `K = K_v`; the `IsFractionRing`/`IsDiscreteValuationRing` instances are available)
every nonzero `x : K_v` is `u • π ^ n` with `u : 𝒪[K_v]ˣ` and `n : ℤ`.  Since `Valued.v u = 1` and
by hypothesis `μ u = 1`, one gets `Valued.v x = (Valued.v π) ^ n` and `μ x = (μ π) ^ n`.

Writing `Valued.v π = WithZero.exp a` and `μ π = WithZero.exp b`, the element `z` of the second
hypothesis gives (with `z = u • π ^ m`) `a * m < 0` and `b * m < 0`, hence `a < 0`, `b < 0`; then
for every `x ≠ 0`, `Valued.v x ≤ 1 ↔ n ≥ 0 ↔ μ x ≤ 1`.  Conclude with
`Valuation.isEquiv_iff_val_le_one` (using `Valued.v 0 = 0 ≤ 1`). -/
theorem isEquiv_valued_of_unit_of_exists {K : Type*} [Field K] [NumberField K]
    (v : Work.LocalFields.FinitePrime K)
    (μ : Valuation (Work.LocalFields.Completion K v) (WithZero (Multiplicative ℤ)))
    (h1 : ∀ x : Work.LocalFields.Completion K v, Valued.v x = 1 → μ x = 1)
    (h2 : ∃ z : Work.LocalFields.Completion K v, z ≠ 0 ∧ Valued.v z < 1 ∧ μ z < 1) :
    μ.IsEquiv (Valued.v (R := Work.LocalFields.Completion K v)) := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  by_cases hx : x = 0
  · subst hx; simp
  -- a uniformizer `π` of `K_v` and its basic valuation properties
  set π : 𝒪[Completion K v] := IsLocalField.uniformizer (k := Completion K v) with hπdef
  have hπirr : Irreducible π := IsLocalField.uniformizer_irreducible (k := Completion K v)
  have hπlt : Valued.v (π : Completion K v) < 1 :=
    (Valuation.integer.integers (Valued.v)).valuation_irreducible_lt_one hπirr
  have hπpos : 0 < Valued.v (π : Completion K v) :=
    (Valuation.integer.integers (Valued.v)).valuation_irreducible_pos hπirr
  have hπne : (π : Completion K v) ≠ 0 := (Valuation.ne_zero_iff (Valued.v)).mp (ne_of_gt hπpos)
  have hμpos : 0 < μ (π : Completion K v) := by
    rw [zero_lt_iff]
    exact (Valuation.ne_zero_iff μ).mpr hπne
  have hunit_v : ∀ u : 𝒪[Completion K v]ˣ,
      Valued.v (algebraMap 𝒪[Completion K v] (Completion K v) (u : 𝒪[Completion K v])) = 1 :=
    fun u => (Valuation.integer.integers (Valued.v)).valuation_unit u
  have hunit_mu : ∀ u : 𝒪[Completion K v]ˣ,
      μ (algebraMap 𝒪[Completion K v] (Completion K v) (u : 𝒪[Completion K v])) = 1 :=
    fun u => h1 _ (hunit_v u)
  -- every nonzero element is `u • π ^ n`, and the two valuations are the corresponding powers
  have key : ∀ y : Completion K v, y ≠ 0 →
      ∃ n : ℤ, Valued.v y = (Valued.v (π : Completion K v))^n ∧
        μ y = (μ (π : Completion K v))^n := by
    intro y hy
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (R := 𝒪[Completion K v]) (K := Completion K v) hπirr hy
    refine ⟨n, ?_, ?_⟩
    · rw [hu, Units.smul_def, Algebra.smul_def, map_mul, hunit_v, one_mul, map_zpow₀]
      rfl
    · rw [hu, Units.smul_def, Algebra.smul_def, map_mul, hunit_mu, one_mul, map_zpow₀]
      rfl
  -- the element `z` of the second hypothesis forces `μ π < 1`
  obtain ⟨z, hz0, hzv, hzμ⟩ := h2
  obtain ⟨m, hzv_eq, hzμ_eq⟩ := key z hz0
  have hmpos : 0 < m := (zpow_lt_one_iff_right_of_lt_one₀ hπpos hπlt).mp (hzv_eq ▸ hzv)
  have hμlt : μ (π : Completion K v) < 1 := by
    by_contra hcon
    have hcon' : 1 ≤ μ (π : Completion K v) := not_lt.mp hcon
    have hle : 1 ≤ (μ (π : Completion K v))^m := one_le_zpow₀ hcon' (le_of_lt hmpos)
    rw [← hzμ_eq] at hle
    exact absurd hle (not_le.mpr hzμ)
  -- conclude
  obtain ⟨n, hvn_eq, hμ_eq⟩ := key x hx
  rw [hμ_eq, hvn_eq, zpow_le_one_iff_right_of_lt_one₀ hμpos hμlt,
      zpow_le_one_iff_right_of_lt_one₀ hπpos hπlt]

end Work.LocalFields
