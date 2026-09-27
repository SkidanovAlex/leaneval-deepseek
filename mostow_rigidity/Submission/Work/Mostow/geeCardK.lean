import Mathlib
import Submission.Work.Mostow.geodDeps
import Submission.Work.Mostow.resStd_hom_discrete
import Submission.Work.Mostow.cardKernelTorus
import Submission.Work.Mostow.tubeIneq
import Submission.Work.Mostow.cardKAux

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

set_option maxHeartbeats 1000000

/-- The rotation displacement `rotN R = ‖R - 1‖` is at most `2`. -/
lemma rotN_le_two (m : ℕ) (R : E m ≃ₗᵢ[ℝ] E m) : rotN R ≤ 2 := by
  have h : rotN R = mOf R := rotN_eq_mOf m R
  rw [h, mOf]
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) (fun x => ?_)
  have hx : (opOf R - 1) x = opOf R x - x := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply]
  rw [hx]
  calc ‖opOf R x - x‖ ≤ ‖opOf R x‖ + ‖x‖ := norm_sub_le _ _
    _ ≤ ‖opOf R‖ * ‖x‖ + ‖x‖ := by
        have h1 := ContinuousLinearMap.le_opNorm (opOf R) x
        linarith
    _ ≤ 1 * ‖x‖ + ‖x‖ := by
        have h1 := mul_le_mul_of_nonneg_right (norm_opOf_le_one R) (norm_nonneg x)
        linarith
    _ = 2 * ‖x‖ := by ring

/-- **Kernel cardinality bound: a `θ`-separated finite subgroup of `O(m)`.**

Route.  `K := {c ∈ Λ // c ∈ centralizer {blk j m 1 R} ∧ resStd j m c = 1}`.  Since `R` is fixed-free,
`Fix (blk j m 1 R) = stdTG j m` (the already proved `Work.Mostow.ti_fixSet_blk` in
`Submission/Work/Mostow/tubeIneq.lean`), so any `c ∈ Λ` commuting with `blk j m 1 R` preserves
`stdTG j m`; with `resStd j m c = 1` it fixes it pointwise, whence `c = blk j m 1 (nrmStd j m c)`
(`Work.Mostow.rhd_stab_eq_blk`, `Work.Mostow.blk_smul_fermi`).  Hence `c ↦ nrmStd j m c` is an
injective homomorphism from `K` onto a finite subgroup of `O(m)`; `K` is finite by
`Work.Mostow.resStd_hom_discrete` (which gives `{c | c ∈ Λ ∧ resStd j m c = 1}` finite).  The
hypothesis becomes: every non-identity element of that finite subgroup has `rotN ≥ θ`.

Count a finite subgroup of `O(m)` with `rotN ≥ θ` off the identity.  Jordan's bound gives an abelian
subgroup `B` of index `≤ J(m)` (finite subgroups of the compact group `O(m)`; cf.
`Work.Mostow.exists_abelian_subgroup_index` in `Submission/Work/Mostow/cardKernelTorus.lean`, or
prove the Jordan bound directly).  A commuting family of rotations sits in a maximal torus of rank
`≤ m/2`, and a `θ`-separated subset of a rank-`r` torus has at most `(1 + 4π/θ)^r ≤ C θ^{-m/2}`
elements (cf. `Work.Mostow.cardKernelTorus`, `Work.Mostow.torusCard_le`,
`Work.Mostow.ftbAbelianCard`, `Work.Mostow.rotPacking`, `Work.Mostow.ncardSeparatedBall`).  Since
`rotN ≤ 2`, the case `θ ≥ 1` needs only `|K| ≤ C`, valid because the order of every finite subgroup
of `O(m)` is bounded in terms of `m`.  The constant `C` may depend on `j, m`. -/
theorem geeCardK (j m : ℕ) (hAj : Submission.Mostow.POActionProp j)
    (hIj : Submission.Mostow.HypIsometryProp j)
    (hA : Submission.Mostow.POActionProp (j + m)) (hI : Submission.Mostow.HypIsometryProp (j + m)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : Subgroup (PO (j + m) 1)) (R : E m ≃ₗᵢ[ℝ] E m) (θ : ℝ),
      IsDiscrete (Λ : Set (PO (j + m) 1)) → blk j m 1 R ∈ Λ →
      (∀ w : E m, R w = w → w = 0) →
      0 < θ → θ ≤ rotN R →
      (∀ c : PO (j + m) 1, c ∈ Λ → c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) →
        resStd j m c = 1 → c ≠ 1 → θ ≤ rotN (nrmStd j m c)) →
      (Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧ c ∈ Subgroup.centralizer {blk j m 1 R} ∧
        resStd j m c = 1} : ENNReal) ≤ ENNReal.ofReal (C * θ ^ (-(m : ℝ) / 2)) := by
  classical
  obtain ⟨J, hJpos, hJ⟩ := cardKernelTorus m
  refine ⟨J * (2 : ℝ) ^ ((m : ℝ) / 2 + 1), by positivity, ?_⟩
  intro Λ R θ hdisc hb hRfree hθ0 hθR hsep
  have hθ2 : θ ≤ 2 := le_trans hθR (rotN_le_two m R)
  -- Every element of the kernel set is a pure block element.
  have hSform : ∀ c : PO (j + m) 1, c ∈ Λ →
      c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) →
      resStd j m c = 1 → c = blk j m 1 (nrmStd j m c) := by
    intro c hcΛ hcC hcS
    have hstab : c ∈ SetStabStd j m :=
      ti_centralizer_mem_SetStabStd j m hAj hIj hA hI R hRfree c hcC
    have h1 := stab_eq_blk j m hAj hIj hA hI c hstab
    rw [hcS] at h1
    exact h1
  -- The image of the kernel set in `O(m)`.
  let T : Set (E m ≃ₗᵢ[ℝ] E m) := nrmStd j m ''
      {c : PO (j + m) 1 | c ∈ Λ ∧ c ∈ Subgroup.centralizer ({blk j m 1 R} : Set (PO (j + m) 1)) ∧
        resStd j m c = 1}
  have hmul_eq : ∀ c d : PO (j + m) 1, c ∈ Λ → d ∈ Λ →
      c ∈ Subgroup.centralizer {blk j m 1 R} → d ∈ Subgroup.centralizer {blk j m 1 R} →
      resStd j m c = 1 → resStd j m d = 1 →
      c * d = blk j m 1 (nrmStd j m c * nrmStd j m d) := by
    intro c d hcΛ hdΛ hcC hdC hcS hdS
    nth_rewrite 1 [hSform c hcΛ hcC hcS]
    nth_rewrite 1 [hSform d hdΛ hdC hdS]
    rw [← (blk_hom j m hAj hIj hA hI).1 (1 : PO j 1) (1 : PO j 1) (nrmStd j m c) (nrmStd j m d),
      one_mul]
  have hTmul : ∀ a ∈ T, ∀ b ∈ T, a * b ∈ T := by
    rintro a ⟨c, ⟨hcΛ, hcC, hcS⟩, rfl⟩ b ⟨d, ⟨hdΛ, hdC, hdS⟩, rfl⟩
    refine ⟨c * d, ⟨Λ.mul_mem hcΛ hdΛ,
      (Subgroup.centralizer {blk j m 1 R}).mul_mem hcC hdC, ?_⟩, ?_⟩
    · rw [hmul_eq c d hcΛ hdΛ hcC hdC hcS hdS, resStd_blk j m hAj hIj hA hI]
    · rw [hmul_eq c d hcΛ hdΛ hcC hdC hcS hdS, nrmStd_blk j m hAj hIj hA hI]
  have hTone : (1 : E m ≃ₗᵢ[ℝ] E m) ∈ T := by
    refine ⟨1, ⟨one_mem Λ, one_mem _, resStd_one j m hAj hIj hA hI⟩, ?_⟩
    exact nrmStd_one j m hAj hIj hA hI
  have hTinv : ∀ a ∈ T, a⁻¹ ∈ T := by
    rintro a ⟨c, ⟨hcΛ, hcC, hcS⟩, rfl⟩
    have hc := hSform c hcΛ hcC hcS
    have hcinv : c⁻¹ = blk j m 1 (nrmStd j m c)⁻¹ := by
      have h2 : blk j m 1 (nrmStd j m c) * blk j m 1 (nrmStd j m c)⁻¹ = 1 := by
        rw [← (blk_hom j m hAj hIj hA hI).1 (1 : PO j 1) (1 : PO j 1) (nrmStd j m c)
          (nrmStd j m c)⁻¹, one_mul, mul_inv_cancel, (blk_hom j m hAj hIj hA hI).2.1]
      have h3 : c * blk j m 1 (nrmStd j m c)⁻¹ = 1 := by
        nth_rewrite 1 [hc]
        exact h2
      exact inv_eq_of_mul_eq_one_right h3
    refine ⟨c⁻¹, ⟨Λ.inv_mem hcΛ, (Subgroup.centralizer {blk j m 1 R}).inv_mem hcC, ?_⟩, ?_⟩
    · rw [hcinv, resStd_blk j m hAj hIj hA hI]
    · rw [hcinv, nrmStd_blk j m hAj hIj hA hI]
  let A : Subgroup (E m ≃ₗᵢ[ℝ] E m) :=
    { carrier := T, mul_mem' := fun ha hb => hTmul _ ha _ hb, one_mem' := hTone,
      inv_mem' := fun ha => hTinv _ ha }
  by_cases hinf : Infinite {c : PO (j + m) 1 // c ∈ Λ ∧
      c ∈ Subgroup.centralizer {blk j m 1 R} ∧ resStd j m c = 1}
  · rw [Nat.card_eq_zero.mpr (Or.inr hinf)]
    simp
  · haveI : Finite {c : PO (j + m) 1 // c ∈ Λ ∧
        c ∈ Subgroup.centralizer {blk j m 1 R} ∧ resStd j m c = 1} :=
      not_infinite_iff_finite.mp hinf
    have hinj : Function.Injective (fun c : {c : PO (j + m) 1 // c ∈ Λ ∧
        c ∈ Subgroup.centralizer {blk j m 1 R} ∧ resStd j m c = 1} =>
        (⟨nrmStd j m (c : PO (j + m) 1),
          show nrmStd j m (c : PO (j + m) 1) ∈ A from
            ⟨(c : PO (j + m) 1), c.2, rfl⟩⟩ : ↥A)) := by
      intro c d hcd
      have h1 : nrmStd j m (c : PO (j + m) 1) = nrmStd j m (d : PO (j + m) 1) :=
        congrArg Subtype.val hcd
      refine Subtype.ext ?_
      have hc := hSform (c : PO (j + m) 1) c.2.1 c.2.2.1 c.2.2.2
      have hd := hSform (d : PO (j + m) 1) d.2.1 d.2.2.1 d.2.2.2
      rw [hc, hd, h1]
    have hsurj : Function.Surjective (fun c : {c : PO (j + m) 1 // c ∈ Λ ∧
        c ∈ Subgroup.centralizer {blk j m 1 R} ∧ resStd j m c = 1} =>
        (⟨nrmStd j m (c : PO (j + m) 1),
          show nrmStd j m (c : PO (j + m) 1) ∈ A from
            ⟨(c : PO (j + m) 1), c.2, rfl⟩⟩ : ↥A)) := by
      rintro ⟨a, ha⟩
      obtain ⟨c, hc, hca⟩ := show ∃ x, x ∈ ({c : PO (j + m) 1 | c ∈ Λ ∧
          c ∈ Subgroup.centralizer {blk j m 1 R} ∧ resStd j m c = 1} : Set _) ∧
          nrmStd j m x = a from ha
      exact ⟨⟨c, hc⟩, Subtype.ext hca⟩
    haveI : Finite ↥A := Finite.of_surjective _ hsurj
    have hcard_eq : Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧
        c ∈ Subgroup.centralizer {blk j m 1 R} ∧ resStd j m c = 1} = Nat.card ↥A := by
      refine le_antisymm ?_ ?_
      · exact Nat.card_le_card_of_injective _ hinj
      · exact Nat.card_le_card_of_surjective _ hsurj
    have hsepA : ∀ a ∈ A, a ≠ 1 → θ ≤ rotN a := by
      intro a ha ha1
      obtain ⟨c, hc, hca⟩ := show ∃ x, x ∈ ({c : PO (j + m) 1 | c ∈ Λ ∧
          c ∈ Subgroup.centralizer {blk j m 1 R} ∧ resStd j m c = 1} : Set _) ∧
          nrmStd j m x = a from ha
      have hcne : (c : PO (j + m) 1) ≠ 1 := by
        intro hc1
        have h2 : nrmStd j m (c : PO (j + m) 1) = 1 :=
          (congrArg (fun g : PO (j + m) 1 => nrmStd j m g) hc1).trans
            (nrmStd_one j m hAj hIj hA hI)
        exact ha1 (hca.symm.trans h2)
      have h := hsep c hc.1 hc.2.1 hc.2.2 hcne
      rwa [hca] at h
    have hKbound := hJ A θ hθ0 hsepA
    have harith : (1 : ℝ) + θ ^ (-(m / 2 : ℕ) : ℤ)
        ≤ (2 : ℝ) ^ ((m : ℝ) / 2 + 1) * θ ^ (-(m : ℝ) / 2) := by
      have hzpow : θ ^ (-(m / 2 : ℕ) : ℤ) = (θ ^ (m / 2 : ℕ))⁻¹ := by
        rw [zpow_neg, zpow_natCast]
      have hcast : (((m / 2 : ℕ) : ℝ)) ≤ (m : ℝ) / 2 := by
        have h : 2 * (m / 2) ≤ m := by omega
        have h' : (2 : ℝ) * ((m / 2 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
        linarith
      have hexp : -(m : ℝ) / 2 ≤ 0 := by
        have h : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        linarith
      rcases le_total θ 1 with hθ1 | hθ1
      · have hpow2 : θ ^ ((m : ℝ) / 2) ≤ θ ^ (((m / 2 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1 hcast
        have hge : θ ^ (-(m / 2 : ℕ) : ℤ) ≤ θ ^ (-(m : ℝ) / 2) := by
          rw [hzpow, ← Real.rpow_natCast θ (m / 2)]
          calc (θ ^ (((m / 2 : ℕ) : ℝ)))⁻¹ ≤ (θ ^ ((m : ℝ) / 2))⁻¹ :=
                inv_anti₀ (Real.rpow_pos_of_pos hθ0 _) hpow2
            _ = θ ^ (-(m : ℝ) / 2) := by
                rw [show -(m : ℝ) / 2 = -((m : ℝ) / 2) by ring, Real.rpow_neg hθ0.le]
        have h1 : (1 : ℝ) ≤ θ ^ (-(m : ℝ) / 2) := by
          have h := Real.rpow_le_rpow_of_exponent_ge hθ0 hθ1 hexp
          simpa using h
        have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ ((m : ℝ) / 2 + 1) := by
          have h := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ 2 by norm_num)
            (show (1 : ℝ) ≤ (m : ℝ) / 2 + 1 by
              have h0 : (0 : ℝ) ≤ (m : ℝ) / 2 := by positivity
              linarith)
          simpa using h
        calc (1 : ℝ) + θ ^ (-(m / 2 : ℕ) : ℤ) ≤ 2 * θ ^ (-(m : ℝ) / 2) := by linarith
          _ ≤ (2 : ℝ) ^ ((m : ℝ) / 2 + 1) * θ ^ (-(m : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hθ0.le _)
      · have hk : (1 : ℝ) ≤ θ ^ (m / 2 : ℕ) := one_le_pow₀ hθ1
        have hle1 : θ ^ (-(m / 2 : ℕ) : ℤ) ≤ 1 := by
          rw [hzpow]
          exact inv_le_one_of_one_le₀ hk
        have hlow : (2 : ℝ) ^ (-(m : ℝ) / 2) ≤ θ ^ (-(m : ℝ) / 2) :=
          Real.rpow_le_rpow_of_nonpos hθ0 hθ2 hexp
        have hkey : (2 : ℝ) ≤ (2 : ℝ) ^ ((m : ℝ) / 2 + 1) * θ ^ (-(m : ℝ) / 2) := by
          have h2 : (2 : ℝ) ^ ((m : ℝ) / 2 + 1) * (2 : ℝ) ^ (-(m : ℝ) / 2) = 2 := by
            rw [← Real.rpow_add (show (0 : ℝ) < 2 by norm_num)]
            have he : (m : ℝ) / 2 + 1 + (-(m : ℝ) / 2) = 1 := by ring
            rw [he, Real.rpow_one]
          calc (2 : ℝ) = (2 : ℝ) ^ ((m : ℝ) / 2 + 1) * (2 : ℝ) ^ (-(m : ℝ) / 2) := h2.symm
            _ ≤ (2 : ℝ) ^ ((m : ℝ) / 2 + 1) * θ ^ (-(m : ℝ) / 2) :=
                mul_le_mul_of_nonneg_left hlow (by positivity)
        calc (1 : ℝ) + θ ^ (-(m / 2 : ℕ) : ℤ) ≤ 1 + 1 := by linarith
          _ = 2 := by norm_num
          _ ≤ (2 : ℝ) ^ ((m : ℝ) / 2 + 1) * θ ^ (-(m : ℝ) / 2) := hkey
    rw [show (Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧
        c ∈ Subgroup.centralizer {blk j m 1 R} ∧ resStd j m c = 1} : ENNReal)
        = ENNReal.ofReal ((Nat.card {c : PO (j + m) 1 // c ∈ Λ ∧
            c ∈ Subgroup.centralizer {blk j m 1 R} ∧ resStd j m c = 1} : ℕ) : ℝ) from
        (ENNReal.ofReal_natCast _).symm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hcard_eq]
    calc (Nat.card ↥A : ℝ) ≤ J * (1 + θ ^ (-(m / 2 : ℕ) : ℤ)) := hKbound
      _ ≤ J * ((2 : ℝ) ^ ((m : ℝ) / 2 + 1) * θ ^ (-(m : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left harith hJpos.le
      _ = J * (2 : ℝ) ^ ((m : ℝ) / 2 + 1) * θ ^ (-(m : ℝ) / 2) := by ring

end Work.Mostow
