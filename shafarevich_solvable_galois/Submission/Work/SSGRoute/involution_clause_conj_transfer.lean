import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Submission.Work.SSGRoute.stage_local_shrinking
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-!
# Transfer of a clause-(B) lift along conjugacy of an involution

This file proves `Work.SSGRoute.involution_clause_conj_transfer`.  The mathematical content is
purely group-theoretic: if `c₀, c` are involutions of `G_ℚ` with `c = g c₀ g⁻¹`, `ρ : G_ℚ →* Γ(τ)`
is a homomorphism with `ρ c ≠ 1`, `π : Γ(τ+1) →* Γ(τ)` is the projection, and `l₀` is a lift of `ρ`
over `⟨c₀⟩` (i.e. `π ∘ l₀ = ρ`), then a lift of `ρ` over `⟨c⟩` is obtained by conjugating the image
of `c₀` by any lift `w` of `ρ g`:

  `y := w * l₀ ⟨c₀, ·⟩ * w⁻¹`  satisfies  `y ^ 2 = 1`  and  `π y = ρ c`.

Since `orderOf y ∣ 2 = orderOf c`, the map `c ↦ y` extends to a homomorphism `⟨c⟩ →* Γ(τ+1)`
(`monoidHomOfForallMemZpowers`), and it kills `ker ρ` because `orderOf (ρ c) = 2`.

The abstract statement is `exists_conj_transfer_lift` below; the theorem requested in the assignment
is a three-line instantiation.
-/

open Work.CohomologicalShrinking

/-- **Group-theoretic core.**  Let `ρ : G →* Γ`, `π : N →* Γ`, let `c₀, c` be involutions of `G`
conjugate by `g`, and let `l₀` lift `ρ` over `⟨c₀⟩`.  If `ρ c ≠ 1` and `w ∈ N` lifts `ρ g`, then
conjugating `l₀ ⟨c₀, ·⟩` by `w` gives a homomorphism `⟨c⟩ →* N` which still lifts `ρ` and which
kills `ker ρ`. -/
private theorem exists_conj_transfer_lift {G Γ N : Type*} [Group G] [Group Γ] [Group N]
    (ρ : G →* Γ) (π : N →* Γ)
    (c₀ c g : G) (hc₀ : c₀ ^ 2 = 1) (hc : c ^ 2 = 1) (hg : c = g * c₀ * g⁻¹)
    (hne : ρ c ≠ 1) (w : N) (hw : π w = ρ g)
    (l₀ : ↥(Subgroup.zpowers c₀) →* N) (hl₀ : ∀ σ : ↥(Subgroup.zpowers c₀), π (l₀ σ) = ρ σ) :
    ∃ l : ↥(Subgroup.zpowers c) →* N,
      (∀ σ : ↥(Subgroup.zpowers c), π (l σ) = ρ σ) ∧
      (∀ σ : ↥(Subgroup.zpowers c), ρ σ = 1 → l σ = 1) := by
  -- the conjugated element `y = w * l₀ ⟨c₀, ·⟩ * w⁻¹`
  set a : N := l₀ ⟨c₀, Subgroup.mem_zpowers c₀⟩ with ha
  set y : N := w * a * w⁻¹ with hy
  have ha2 : a ^ 2 = 1 := by
    rw [ha, ← map_pow]
    have h2 : (⟨c₀, Subgroup.mem_zpowers c₀⟩ : ↥(Subgroup.zpowers c₀)) ^ 2 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      simpa using hc₀
    rw [h2, map_one]
  have hyconj : y = MulAut.conj w a := by rw [hy, MulAut.conj_apply]
  have hy2 : y ^ 2 = 1 := by rw [hyconj, ← map_pow, ha2, map_one]
  -- `y` lies over `ρ c`
  have hπy : π y = ρ c := by
    rw [hy, map_mul, map_mul, map_inv, hw, ha, hl₀ ⟨c₀, Subgroup.mem_zpowers c₀⟩]
    rw [← map_inv, ← map_mul, ← map_mul, ← hg]
  -- order bookkeeping
  have hcne : c ≠ 1 := fun h => hne (by rw [h, map_one])
  have hordc : orderOf c = 2 := orderOf_eq_prime (p := 2) hc hcne
  have hρc2 : (ρ c) ^ 2 = 1 := by rw [← map_pow, hc, map_one]
  have hρcord : orderOf (ρ c) = 2 := orderOf_eq_prime (p := 2) hρc2 hne
  have hyord : orderOf y ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hy2
  -- `⟨c, ·⟩` generates `⟨c⟩`
  have hgen : ∀ x : ↥(Subgroup.zpowers c),
      x ∈ Subgroup.zpowers (⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) := by
    intro x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.2
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      simpa using hk⟩
  have hgdvd : orderOf y ∣ orderOf (⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) := by
    rw [Subgroup.orderOf_mk, hordc]
    exact hyord
  -- the homomorphism `⟨c⟩ →* N` determined by `c ↦ y`
  let l : ↥(Subgroup.zpowers c) →* N := monoidHomOfForallMemZpowers hgen hgdvd
  have hl_c : l ⟨c, Subgroup.mem_zpowers c⟩ = y := monoidHomOfForallMemZpowers_apply_gen hgen hgdvd
  refine ⟨l, ?_, ?_⟩
  · intro σ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
    have hσ : σ = (⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hk.symm
    calc π (l σ) = π (l ((⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) ^ k)) := by
          rw [hσ]
      _ = π ((l ⟨c, Subgroup.mem_zpowers c⟩) ^ k) := by rw [map_zpow]
      _ = (π (l ⟨c, Subgroup.mem_zpowers c⟩)) ^ k := by rw [map_zpow]
      _ = (ρ c) ^ k := by rw [hl_c, hπy]
      _ = ρ (c ^ k) := (map_zpow ρ c k).symm
      _ = ρ σ := by rw [hk]
  · intro σ hσ1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp σ.2
    have hσ : σ = (⟨c, Subgroup.mem_zpowers c⟩ : ↥(Subgroup.zpowers c)) ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow]
      exact hk.symm
    have hρk : (ρ c) ^ k = 1 := by
      rw [← map_zpow, hk]
      exact hσ1
    have hk_dvd : ((orderOf (ρ c) : ℕ) : ℤ) ∣ k := orderOf_dvd_iff_zpow_eq_one.mpr hρk
    rw [hρcord] at hk_dvd
    have hcast : ((orderOf y : ℕ) : ℤ) ∣ (2 : ℤ) := by exact_mod_cast hyord
    have hlσ : l σ = y ^ k := by rw [hσ, map_zpow, hl_c]
    rw [hlσ]
    exact orderOf_dvd_iff_zpow_eq_one.mp (dvd_trans hcast hk_dvd)

/-- **Transfer of a clause-(B) lift along conjugacy.**

Let `c₀, c` be involutions of `G_ℚ` with `c = g * c₀ * g⁻¹`, let
`Ψ = (flowGroupMap p G i j Φ).comp φ`, and let `l₀` be a lift of `Ψ` over `⟨c₀⟩`.

Set `w := flowGroupSection p G n i j (Ψ g)` (a lift of `Ψ g` in `Γ_n(τ+1)`) and
`y := w * l₀ ⟨c₀, _⟩ * w⁻¹`.  Then `y ^ 2 = 1` (because `(l₀ ⟨c₀, _⟩) ^ 2 = 1`, as `l₀` is a
homomorphism out of a group of order two — use that `hne` forces `c₀ ≠ 1` and `c ≠ 1`), and
`flowGroupSucc y = flowGroupSucc w * Ψ c₀ * (flowGroupSucc w)⁻¹ = Ψ g * Ψ c₀ * (Ψ g)⁻¹ = Ψ c`
because `flowGroupSucc ∘ φ`-compatible `Ψ` is a homomorphism and `hg` holds; use `hl₀` and
`SSGRoute.liftsFlowAt_iff_flowGroupSucc`.

The homomorphism `l : ↥(Subgroup.zpowers c) →* Γ_n(τ+1)` with `l ⟨c, _⟩ = y` is then obtained from
`orderOf y ∣ orderOf c` (both sides `= 2`: `hne` forces `orderOf (Ψ c) = 2` and `orderOf y ∣ 2`)
by descending `ofAdd k ↦ y ^ k` along `Multiplicative ℤ →* ↥(Subgroup.zpowers c)` with
`QuotientGroup.lift` together with `QuotientGroup.quotientKerEquivOfSurjective` — the construction
used at the end of `Work.SSGRoute.involution_clause_of_two_torsion` in
`Submission/Work/SSGRoute/stage_local_shrinking.lean`; if you need it as a separate statement,
please make it `private` so that it does not clash with other files.

`LiftsFlowAt (l σ) (Ψ σ)` follows from `flowGroupSucc (y ^ k) = (Ψ c) ^ k`.  Kernel-killing: if
`Ψ (c ^ k) = 1` then `(Ψ c) ^ k = 1`, so `2 = orderOf (Ψ c) ∣ k`, and since `orderOf y ∣ 2` we get
`y ^ k = 1`. -/
theorem involution_clause_conj_transfer (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K] [Normal ℚ K] (i j m n : ℕ)
    (φ : SSGRoute.GalQ →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) m i j)
    (Φ : Work.CohomologicalShrinking.OperatorMap (K ≃ₐ[ℚ] K) m n)
    (c₀ c g : SSGRoute.GalQ) (hc₀ : c₀ ^ 2 = 1) (hc : c ^ 2 = 1)
    (hg : c = g * c₀ * g⁻¹)
    (hne : (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) c) ≠ 1)
    (l₀ : ↥(Subgroup.zpowers c₀) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
        (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hl₀ : ∀ σ : ↥(Subgroup.zpowers c₀),
      SSGRoute.LiftsFlowAt (l₀ σ) (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)) :
    ∃ l : ↥(Subgroup.zpowers c) →* Work.CohomologicalShrinking.flowGroup p (K ≃ₐ[ℚ] K) n
          (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2,
      (∀ σ : ↥(Subgroup.zpowers c),
        SSGRoute.LiftsFlowAt (l σ)
          (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ)) ∧
      (∀ σ : ↥(Subgroup.zpowers c),
        (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) σ) = 1 → l σ = 1) := by
  classical
  obtain ⟨l, hl, hkill⟩ :=
    exists_conj_transfer_lift
      (ρ := (Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ)
      (π := flowGroupSucc p (K ≃ₐ[ℚ] K) n i j)
      (hc₀ := hc₀) (hc := hc) (hg := hg) (hne := hne)
      (w := flowGroupSection p (K ≃ₐ[ℚ] K) n i j
        (((Work.CohomologicalShrinking.flowGroupMap p (K ≃ₐ[ℚ] K) i j Φ).comp φ) g))
      (hw := flowGroupSucc_section p (K ≃ₐ[ℚ] K) n i j _)
      (l₀ := l₀)
      (hl₀ := fun σ => (SSGRoute.liftsFlowAt_iff_flowGroupSucc p K n i j (l₀ σ) _).mp (hl₀ σ))
  exact ⟨l,
    fun σ => (SSGRoute.liftsFlowAt_iff_flowGroupSucc p K n i j (l σ) _).mpr (hl σ),
    fun σ hσ => hkill σ hσ⟩

end Work.SSGRoute
