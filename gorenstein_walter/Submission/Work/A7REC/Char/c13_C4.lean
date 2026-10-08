/-
# `A7REC` design pass 13, leaf `C4`: involution-pair counts as inverting-involution counts

`Work.A7REC.C7invPairCount x = #{p : G × G | p.1² = p.2² = 1 ∧ p.1 * p.2 = x}`.  The file
`Submission/Work/A7REC/Char/a7InvolutionCounts.lean` already proves the general bijection
`ncard_pair_eq_ncard_invSet`:

> `C7invPairCount x = (invSet x).ncard`,  `invSet x = {u | orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹ ∧
> orderOf (u * x) = 2}`,

and (in `A7InvCtx`, the local `A₇`-configuration of `z`, `S ≅ D₈`, `U = ⟨σ⟩` of order `3`,
`π ∈ S` of order `4` with `C(π) = ⟨π⟩`) the count `(invSet h.π).ncard = 4`
(`A7InvCtx.ncard_invSet_pi`).

What is left for the two other conjuncts is to *describe the inverting involutions*:

* `invSet h.z = {a | a ∈ C_G(z) ∧ orderOf a = 2} \ {z}` — an involution `u` inverts `z` (of
  order `2`) iff it commutes with `z`; among the involutions of `C_G(z)` it is not `z` itself,
  because `z * z = 1`.  Hence `i(z) = #Inv(C_G(z)) - 1`.
* `invSet (h.z * h.σ) = {a | a ∈ C_G(z) ∧ orderOf a = 2 ∧ aσa⁻¹ = σ⁻¹}` — this is the
  "inverting set" of `zσ`, whose cardinality is the RHS of the third conjunct.  The two
  inclusions use `(zσ)³ = z` (so an element inverting `zσ` inverts `z`, i.e. lies in `C_G(z)`)
  and `(zσ)⁴ = σ` (so it inverts `σ`); conversely `a ∈ C_G(z)` with `a² = 1` inverting `σ`
  inverts `zσ` and `a · zσ` is an involution, because `a zσ a = (zσ)⁻¹`.

The main theorem `c13_C4` combines these descriptions with
`ncard_pair_eq_ncard_invSet`, `A7InvCtx.ncard_invSet_pi` and the elementary cardinality
`(s \ {a}).ncard = s.ncard - 1` of `Set.ncard_sdiff_singleton_of_mem`.
-/
import Mathlib
import Submission.Work.A7REC.Defs
import Submission.Work.A7REC.Char.a7InvolutionCounts
import Submission.Work.A7REC.Char.invertingSetZsigma

namespace Work.A7REC.Char

open Subgroup

/-- The involutions inverting the central involution `z` are exactly the involutions of
`C_G(z)` other than `z` itself.

`invSet x = {u | orderOf u = 2 ∧ u * x * u⁻¹ = x⁻¹ ∧ orderOf (u * x) = 2}`; for `x = z` of
order `2` the condition `u * z * u⁻¹ = z⁻¹ = z` is commutation with `z`, and `u * z` (with `u`,
`z` commuting involutions) is an involution precisely when it is different from `1`, i.e.
`u ≠ z`. -/
theorem invSet_z_eq {G : Type*} [Group G] [Finite G] (h : A7InvCtx G) :
    invSet h.z = {a : G | a ∈ h.C ∧ orderOf a = 2} \ {h.z} := by
  obtain ⟨-, hzz⟩ := orderOf_eq_two_iff'.mp h.hz2
  have hzinv : h.z⁻¹ = h.z := inv_eq_of_mul_eq_one_left hzz
  ext u
  simp only [invSet, Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hu2, hinv, hux⟩
    refine ⟨⟨?_, hu2⟩, ?_⟩
    · rw [A7InvCtx.C, Subgroup.mem_centralizer_iff]
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst hy
      have hh : u * h.z * u⁻¹ = h.z := by rw [hinv, hzinv]
      have h1 : u * h.z = h.z * u := by
        have := congrArg (fun w => w * u) hh
        simpa [mul_assoc] using this
      exact h1.symm
    · intro hu; subst hu
      rw [hzz, orderOf_one] at hux
      norm_num at hux
  · rintro ⟨⟨huC, hu2⟩, huz⟩
    obtain ⟨-, huu⟩ := orderOf_eq_two_iff'.mp hu2
    have hcomm : h.z * u = u * h.z := (Subgroup.mem_centralizer_iff.mp huC) h.z (by simp)
    refine ⟨hu2, ?_, ?_⟩
    · have key : u * h.z * u⁻¹ = h.z := by
        rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [key, hzinv]
    · rw [orderOf_eq_two_iff']
      refine ⟨?_, ?_⟩
      · intro hzu
        apply huz
        have := congrArg (fun w => w * h.z) hzu
        simpa [mul_assoc, hzz, hzinv] using this
      · have h1 : u * h.z * (u * h.z) = 1 := by
          calc u * h.z * (u * h.z) = u * (h.z * u) * h.z := by simp [mul_assoc]
            _ = u * (u * h.z) * h.z := by rw [hcomm]
            _ = (u * u) * (h.z * h.z) := by simp [mul_assoc]
            _ = 1 := by rw [huu, hzz, one_mul]
        simpa using h1

/-- The involutions of `C_G(z)` inverting `σ` are exactly the involutions inverting `z * σ`.

For `a ∈ C_G(z)` of order `2` the two conditions `a (zσ) a⁻¹ = (zσ)⁻¹` and `a σ a⁻¹ = σ⁻¹`
are equivalent (`σ = (zσ)⁴`, and `z` centralises `σ`), and then `a · zσ` is an involution
(`a zσ a = (zσ)⁻¹` because `a² = 1`, and `a zσ ≠ 1` as otherwise `orderOf a = 6`).  In the
other direction an element inverting `zσ` inverts `z = (zσ)³`, hence lies in `C_G(z)`, and
inverts `σ = (zσ)⁴`. -/
theorem invSet_zsigma_eq {G : Type*} [Group G] [Finite G] (h : A7InvCtx G) :
    invSet (h.z * h.σ) = {a : G | a ∈ h.C ∧ orderOf a = 2 ∧ a * h.σ * a⁻¹ = h.σ⁻¹} := by
  obtain ⟨-, hzz⟩ := orderOf_eq_two_iff'.mp h.hz2
  have hzinv : h.z⁻¹ = h.z := inv_eq_of_mul_eq_one_left hzz
  have hz3 : (h.z * h.σ) ^ 3 = h.z := h.iz_zσ_pow_three
  have hz4 : (h.z * h.σ) ^ 4 = h.σ := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hz3, ← mul_assoc, hzz, one_mul]
  have hzσcomm : h.z * h.σ = h.σ * h.z := (h.z_central_in_C h.σ_mem_C).symm
  ext u
  simp only [invSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hu2, huinv, _⟩
    have hconj_z : u * h.z * u⁻¹ = h.z := by
      calc u * h.z * u⁻¹ = u * (h.z * h.σ) ^ 3 * u⁻¹ := by rw [hz3]
        _ = (u * (h.z * h.σ) * u⁻¹) ^ 3 := by rw [conj_pow]
        _ = ((h.z * h.σ)⁻¹) ^ 3 := by rw [huinv]
        _ = ((h.z * h.σ) ^ 3)⁻¹ := by rw [inv_pow]
        _ = h.z⁻¹ := by rw [hz3]
        _ = h.z := hzinv
    have hmem : u ∈ h.C := by
      rw [A7InvCtx.C, Subgroup.mem_centralizer_iff]
      intro y hy
      simp only [Set.mem_singleton_iff] at hy
      subst hy
      have h1 : u * h.z = h.z * u := by
        have := congrArg (fun w => w * u) hconj_z
        simpa [mul_assoc] using this
      exact h1.symm
    have hconj_s : u * h.σ * u⁻¹ = h.σ⁻¹ := by
      calc u * h.σ * u⁻¹ = u * (h.z * h.σ) ^ 4 * u⁻¹ := by rw [hz4]
        _ = (u * (h.z * h.σ) * u⁻¹) ^ 4 := by rw [conj_pow]
        _ = ((h.z * h.σ)⁻¹) ^ 4 := by rw [huinv]
        _ = ((h.z * h.σ) ^ 4)⁻¹ := by rw [inv_pow]
        _ = h.σ⁻¹ := by rw [hz4]
    exact ⟨hmem, hu2, hconj_s⟩
  · rintro ⟨hmem, hu2, hconj_s⟩
    obtain ⟨-, huu⟩ := orderOf_eq_two_iff'.mp hu2
    have hcomm : h.z * u = u * h.z := (Subgroup.mem_centralizer_iff.mp hmem) h.z (by simp)
    have hcomm_s : h.z * h.σ⁻¹ = h.σ⁻¹ * h.z := by
      have h1 : (h.z * h.σ)⁻¹ = (h.σ * h.z)⁻¹ := by rw [hzσcomm]
      rw [mul_inv_rev, mul_inv_rev, hzinv] at h1
      exact h1.symm
    have hzconj : u * h.z * u⁻¹ = h.z := by rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have hzσ_inv : u * (h.z * h.σ) * u⁻¹ = (h.z * h.σ)⁻¹ := by
      rw [mul_inv_rev, hzinv]
      calc u * (h.z * h.σ) * u⁻¹ = (u * h.z * u⁻¹) * (u * h.σ * u⁻¹) := by group
        _ = h.z * h.σ⁻¹ := by rw [hzconj, hconj_s]
        _ = h.σ⁻¹ * h.z := hcomm_s
    refine ⟨hu2, hzσ_inv, ?_⟩
    rw [orderOf_eq_two_iff']
    refine ⟨?_, ?_⟩
    · -- `u * (z * σ) = 1` would force `σ = σ⁻¹`
      intro h1
      have hu_eq : u = (h.z * h.σ)⁻¹ := (inv_eq_of_mul_eq_one_left h1).symm
      have hcomm_s' : h.σ * (h.z * h.σ) = (h.z * h.σ) * h.σ := by
        rw [← mul_assoc, h.z_central_in_C h.σ_mem_C]
      have hleft : (h.z * h.σ)⁻¹ * h.σ * (h.z * h.σ) = h.σ := by
        calc (h.z * h.σ)⁻¹ * h.σ * (h.z * h.σ)
            = (h.z * h.σ)⁻¹ * (h.σ * (h.z * h.σ)) := by group
          _ = (h.z * h.σ)⁻¹ * ((h.z * h.σ) * h.σ) := by rw [hcomm_s']
          _ = h.σ := by group
      have hcon : (h.z * h.σ)⁻¹ * h.σ * ((h.z * h.σ)⁻¹)⁻¹ = h.σ⁻¹ := by
        rw [hu_eq] at hconj_s
        exact hconj_s
      rw [inv_inv, hleft] at hcon
      have hσeq : h.σ = h.σ⁻¹ := hcon
      have hsq2 : h.σ * h.σ = 1 := by
        nth_rewrite 2 [hσeq]
        exact mul_inv_cancel h.σ
      have hdvd : orderOf h.σ ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one, pow_two]
        exact hsq2
      rw [h.orderOf_σ] at hdvd
      norm_num at hdvd
    · have hzσ_inv' : u * (h.z * h.σ) * u = (h.z * h.σ)⁻¹ := by
        have hsplit : u * (h.z * h.σ) = (h.z * h.σ)⁻¹ * u := by
          calc u * (h.z * h.σ) = (u * (h.z * h.σ) * u⁻¹) * u := by group
            _ = (h.z * h.σ)⁻¹ * u := by rw [hzσ_inv]
        rw [hsplit, mul_assoc, huu, mul_one]
      calc u * (h.z * h.σ) * (u * (h.z * h.σ))
          = (u * (h.z * h.σ) * u) * (h.z * h.σ) := by group
        _ = (h.z * h.σ)⁻¹ * (h.z * h.σ) := by rw [hzσ_inv']
        _ = 1 := inv_mul_cancel _

/-- **`C4` of design pass 13.**  Involution-pair counts as inverting-involution counts:
`i(π) = 4` (the reflections of the Sylow `2`-subgroup inverting `π`), `i(z) = #Inv(C_G(z)) - 1`
and `i(zσ) = #{a ∈ Inv(C_G(z)) : a σ a⁻¹ = σ⁻¹}`. -/
theorem c13_C4 (G : Type*) [Group G] [Finite G] (ctx : Work.A7REC.A7RecCtx G) (π σ : G)
    (hσ : σ ∈ ctx.U) (hσ1 : σ ≠ 1) (hπS : π ∈ ctx.Ssub) (hπ4 : orderOf π = 4)
    (hCπ : Subgroup.centralizer ({π} : Set G) = Subgroup.zpowers π) :
    Work.A7REC.C7invPairCount π = 4 ∧
      Work.A7REC.C7invPairCount ctx.z = {a : G | a ∈ ctx.C ∧ orderOf a = 2}.ncard - 1 ∧
      Work.A7REC.C7invPairCount (ctx.z * σ) =
        {a : G | a ∈ ctx.C ∧ orderOf a = 2 ∧ a * σ * a⁻¹ = σ⁻¹}.ncard := by
  -- the local `A₇`-configuration carried by the context
  let h : A7InvCtx G :=
    { S := ctx.S, hSdih := ctx.hSdih, z := ctx.z, hzS := ctx.hzS, hz2 := ctx.hz2,
      U := ctx.U, hU3 := ctx.hUcard, hC := ctx.hCz,
      π := π, hπS := hπS, hπ4 := hπ4, hCπ := hCπ,
      σ := σ, hσU := hσ, hσ1 := hσ1 }
  have HZ : h.z ∈ ({a : G | a ∈ h.C ∧ orderOf a = 2} : Set G) := by
    refine ⟨?_, h.hz2⟩
    rw [A7InvCtx.C, Subgroup.mem_centralizer_singleton_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [ncard_pair_eq_ncard_invSet]
    exact A7InvCtx.ncard_invSet_pi h
  · rw [ncard_pair_eq_ncard_invSet, invSet_z_eq h]
    exact Set.ncard_sdiff_singleton_of_mem HZ
  · rw [ncard_pair_eq_ncard_invSet, show ctx.z * σ = h.z * h.σ from rfl, invSet_zsigma_eq h]

end Work.A7REC.Char
