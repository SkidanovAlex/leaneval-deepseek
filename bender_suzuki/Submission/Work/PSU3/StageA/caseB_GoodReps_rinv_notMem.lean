import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageA.GoodRepsDef

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

/-- **Peterfalvi II Ch. VI §2 (p. 262):** the representative `r` is not of the form `r · r^{-k}`,
`k ∈ Kset H t`:

  `¬ ∃ k ∈ Kset H t, r * (k⁻¹ * r⁻¹ * k) = r⁻¹`.

The equation is equivalent, after inversion, to `k⁻¹ * r * k = r ^ 2`: conjugating `r` by `k`
sends it to `r²`.  But conjugation preserves the order of an element, whereas `r ∈ Q` with `Q` a
2-group has 2-power order, so `orderOf (r ^ 2) = orderOf r / 2 < orderOf r`.  Contradiction. -/
theorem caseB_GoodReps_rinv_notMem {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G}
    (hS : Work.PSU3.PSU3Hyp H Q t)
    (hr : r ∈ Q) (hr1 : r ≠ 1) (hr2 : r * r ≠ 1) :
    ¬ ∃ k ∈ Work.ThmF.Kset H t, r * (k⁻¹ * r⁻¹ * k) = r⁻¹ := by
  rintro ⟨k, _hkK, hkeq⟩
  -- `Q` is a 2-group, so `orderOf r` is even (indeed a power of `2`).
  have hne : (⟨r, hr⟩ : Q) ≠ 1 := by
    intro h
    exact hr1 (by simpa using congrArg (fun x : Q => (x : G)) h)
  have hdvd : 2 ∣ orderOf r := by
    have hthis := IsPGroup.dvd_orderOf hS.two hne
    simpa using hthis
  -- Inverting `r * (k⁻¹ * r⁻¹ * k) = r⁻¹` gives `k⁻¹ * r * k * r⁻¹ = r`.
  have h3 : k⁻¹ * r * k * r⁻¹ = r := by
    have h := congrArg (fun x : G => x⁻¹) hkeq
    rw [inv_inv] at h
    have e : (r * (k⁻¹ * r⁻¹ * k))⁻¹ = k⁻¹ * r * k * r⁻¹ := by group
    rwa [e] at h
  -- Hence conjugation by `k` sends `r` to `r ^ 2`.
  have hconj : k⁻¹ * r * k = r ^ 2 := by
    calc k⁻¹ * r * k = k⁻¹ * r * k * r⁻¹ * r := by group
      _ = r * r := by rw [h3]
      _ = r ^ 2 := by rw [pow_two]
  -- Conjugation preserves the order of an element.
  have hord1 : orderOf (k⁻¹ * r * k) = orderOf r :=
    SemiconjBy.orderOf_eq k (by simp only [SemiconjBy]; group)
  have hord2 : orderOf (r ^ 2) = orderOf r := by
    rw [← hconj]; exact hord1
  -- But `r ^ 2` has order `orderOf r / 2 < orderOf r`, since `2 ∣ orderOf r`.
  have hval : orderOf (r ^ 2) = orderOf r / 2 := by
    rw [orderOf_pow, Nat.gcd_eq_right hdvd]
  have hlt : orderOf r / 2 < orderOf r := Nat.div_lt_self (orderOf_pos r) (by norm_num)
  have heq : orderOf r = orderOf r / 2 := hord2 ▸ hval
  omega

end Work.PSU3.StageA
