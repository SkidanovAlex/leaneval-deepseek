import Mathlib
import Submission.Work.HP.ConicsDefs
import Submission.Work.HP.conics_nonsquare_card

noncomputable section

namespace Work.HP

open Work.HP.Conics

/-! ## Geometry: sharp conics from anisotropic binary forms -/

/-- For an odd prime `p`, `4 ≠ 0` in `ZMod p`. -/
private theorem conics_four_ne_zero (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (4 : ZMod p) ≠ 0 := by
  have hp' : Nat.Prime p := Fact.out
  have hnat : ((4 : ℕ) : ZMod p) ≠ 0 := by
    intro hd0
    have hd : p ∣ 4 := (CharP.cast_eq_zero_iff (ZMod p) p 4).mp hd0
    have hd2 : p ∣ 2 ^ 2 := by simpa using hd
    have h2 : p ∣ 2 := hp'.dvd_of_dvd_pow hd2
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    have hge : 2 ≤ p := hp'.two_le
    omega
  simpa using hnat

/-- The binary form `αu² + βuv + γv²` over `ZMod p` (`p` an odd prime) has no nontrivial zero
when `α ≠ 0` and the discriminant `β² - 4αγ` is a non-square. -/
private theorem conics_binary_aniso (p : ℕ) [Fact p.Prime] {α β γ : ZMod p}
    (hα : α ≠ 0) (hd : ¬ IsSquare (β ^ 2 - 4 * α * γ)) :
    ∀ u v : ZMod p, α * u ^ 2 + β * (u * v) + γ * v ^ 2 = 0 → u = 0 ∧ v = 0 := by
  intro u v huv
  by_cases hv : v = 0
  · subst hv
    have huv' : α * u ^ 2 = 0 := by simpa using huv
    rcases mul_eq_zero.mp huv' with h | h
    · exact absurd h hα
    · have hu : u = 0 := by
        have h2 : u * u = 0 := by rwa [pow_two] at h
        rcases mul_eq_zero.mp h2 with h' | h' <;> exact h'
      exact ⟨hu, rfl⟩
  · exfalso
    apply hd
    refine ⟨2 * α * (u * v⁻¹) + β, ?_⟩
    have ht : α * (u * v⁻¹) ^ 2 + β * (u * v⁻¹) + γ = 0 := by
      have h2 : (α * u ^ 2 + β * (u * v) + γ * v ^ 2) * v⁻¹ ^ 2 = 0 := by rw [huv, zero_mul]
      have hexp : (α * u ^ 2 + β * (u * v) + γ * v ^ 2) * v⁻¹ ^ 2
          = α * (u * v⁻¹) ^ 2 + β * (u * v⁻¹) + γ := by
        have hv1 : v * v⁻¹ = 1 := mul_inv_cancel₀ hv
        calc (α * u ^ 2 + β * (u * v) + γ * v ^ 2) * v⁻¹ ^ 2
            = α * (u * v⁻¹) ^ 2 + β * (u * (v * v⁻¹) * v⁻¹)
              + γ * ((v * v⁻¹) * (v * v⁻¹)) := by ring
          _ = α * (u * v⁻¹) ^ 2 + β * (u * v⁻¹) + γ := by rw [hv1]; ring
      rwa [hexp] at h2
    have h4 : 4 * α * (α * (u * v⁻¹) ^ 2 + β * (u * v⁻¹) + γ) = 0 := by rw [ht, mul_zero]
    have hzero : β ^ 2 - 4 * α * γ - (2 * α * (u * v⁻¹) + β) * (2 * α * (u * v⁻¹) + β) = 0 := by
      have h5 : β ^ 2 - 4 * α * γ - (2 * α * (u * v⁻¹) + β) * (2 * α * (u * v⁻¹) + β)
          = -(4 * α * (α * (u * v⁻¹) ^ 2 + β * (u * v⁻¹) + γ)) := by ring
      rw [h5, h4, neg_zero]
    exact sub_eq_zero.mp hzero

/-- If `α ≠ 0` and `β² - 4αγ` is a non-square, then the conic with coefficient vector
`mkForm a b α β γ` is sharp along the line through `(1,a,b)`. -/
theorem conics_sharpAt_mkForm (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b α β γ : ZMod p)
    (hα : α ≠ 0) (hd : ¬ IsSquare (β ^ 2 - 4 * α * γ)) :
    Conics.SharpAt (Conics.mkForm a b α β γ) ![1, a, b] := by
  have key := conics_binary_aniso p hα hd
  refine ⟨?_, ?_, ?_⟩
  · intro h0
    have h1 := congrFun h0 0
    simp at h1
  · intro y
    rw [Conics.pol, Conics.qf_mkForm, Conics.qf_mkForm, Conics.qf_mkForm]
    simp [Pi.add_apply]
    ring
  · intro x hx
    rw [Conics.qf_mkForm] at hx
    obtain ⟨hu, hv⟩ := key (x 1 - a * x 0) (x 2 - b * x 0) hx
    rw [sub_eq_zero] at hu hv
    have hx0 : x 0 = (x 0 • (![1, a, b] : Fin 3 → ZMod p)) 0 := by simp [Pi.smul_apply]
    have hx1 : x 1 = (x 0 • (![1, a, b] : Fin 3 → ZMod p)) 1 := by
      have hb : (x 0 • (![1, a, b] : Fin 3 → ZMod p)) 1 = x 0 * a := by simp [Pi.smul_apply]
      rw [hb, hu]; ring
    have hx2 : x 2 = (x 0 • (![1, a, b] : Fin 3 → ZMod p)) 2 := by
      have hb : (x 0 • (![1, a, b] : Fin 3 → ZMod p)) 2 = x 0 * b := by simp [Pi.smul_apply]
      rw [hb, hv]; ring
    refine ⟨x 0, ?_⟩
    funext i
    fin_cases i
    · exact hx0
    · exact hx1
    · exact hx2

/-! ## Counting -/

/-- The number of coefficient triples `(α,β,γ)` with `α ≠ 0` and discriminant `β² - 4αγ` a
non-square is `p(p-1)²/2`. -/
theorem conics_trip_count_aux (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    {q : ZMod p × ZMod p × ZMod p |
        q.1 ≠ 0 ∧ ¬ IsSquare (q.2.1 ^ 2 - 4 * q.1 * q.2.2)}.ncard
      = p * (p - 1) * (p - 1) / 2 := by
  classical
  have hst : {q : ZMod p × ZMod p × ZMod p |
        q.1 ≠ 0 ∧ ¬ IsSquare (q.2.1 ^ 2 - 4 * q.1 * q.2.2)}.ncard
      = {q : ZMod p × ZMod p × ZMod p | q.1 ≠ 0 ∧ ¬ IsSquare q.2.2}.ncard := by
    refine Set.ncard_congr (fun q _ => (q.1, (q.2.1, q.2.1 ^ 2 - 4 * q.1 * q.2.2))) ?_ ?_ ?_
    · rintro ⟨α, β, γ⟩ ⟨h1, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨α, β, γ⟩ ⟨α', β', γ'⟩ ⟨h1, h2⟩ ⟨h1', h2'⟩ heq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, h3⟩ := heq
      have h4 : (4 * α : ZMod p) ≠ 0 := mul_ne_zero (conics_four_ne_zero p hp) h1
      have h4' : 4 * α * γ = 4 * α * γ' := by
        have h6 : (β ^ 2 - 4 * α * γ) - (β ^ 2 - 4 * α * γ') = -(4 * α * γ - 4 * α * γ') := by
          ring
        have h7 : (β ^ 2 - 4 * α * γ) - (β ^ 2 - 4 * α * γ') = 0 := sub_eq_zero.mpr h3
        rw [h6] at h7
        exact sub_eq_zero.mp (neg_eq_zero.mp h7)
      have hγ : γ = γ' := mul_left_cancel₀ h4 h4'
      rw [hγ]
    · rintro ⟨α, β, w⟩ ⟨h1, h2⟩
      have h4 : (4 * α : ZMod p) ≠ 0 := mul_ne_zero (conics_four_ne_zero p hp) h1
      have hdisc : β ^ 2 - 4 * α * ((β ^ 2 - w) / (4 * α)) = w := by
        have hq : 4 * α * ((β ^ 2 - w) / (4 * α)) = β ^ 2 - w := by
          rw [div_eq_mul_inv, ← mul_assoc, mul_comm (4 * α) (β ^ 2 - w), mul_assoc,
            mul_inv_cancel₀ h4, mul_one]
        rw [hq]; ring
      refine ⟨(α, (β, (β ^ 2 - w) / (4 * α))), ?_, ?_⟩
      · show α ≠ 0 ∧ ¬ IsSquare (β ^ 2 - 4 * α * ((β ^ 2 - w) / (4 * α)))
        exact ⟨h1, by rw [hdisc]; exact h2⟩
      · simp [hdisc]
  have ht_eq : {q : ZMod p × ZMod p × ZMod p | q.1 ≠ 0 ∧ ¬ IsSquare q.2.2}
      = ({α : ZMod p | α ≠ 0}
          ×ˢ ((Set.univ : Set (ZMod p)) ×ˢ {w : ZMod p | ¬ IsSquare w})) := by
    ext q
    simp [Set.mem_prod]
  have hA : {α : ZMod p | α ≠ 0}.ncard = p - 1 := by
    have hset : {α : ZMod p | α ≠ 0} = ({0} : Set (ZMod p))ᶜ := by
      ext α; simp
    rw [hset, Set.ncard_compl, Set.ncard_singleton, Nat.card_eq_fintype_card, ZMod.card]
  have hU : (Set.univ : Set (ZMod p)).ncard = p := by
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, ZMod.card]
  have harith : (p - 1) * (p * ((p - 1) / 2)) = p * (p - 1) * (p - 1) / 2 := by
    obtain ⟨k, hk⟩ := Nat.Prime.odd_of_ne_two (Fact.out) hp
    have hp1 : p - 1 = 2 * k := by omega
    have hk2 : (p - 1) / 2 = k := by
      rw [hp1, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
    rw [hk2, hp1]
    rw [show p * (2 * k) * (2 * k) = (2 * k * (p * k)) * 2 by ring]
    exact (Nat.mul_div_cancel _ (by norm_num : 0 < 2)).symm
  rw [hst, ht_eq, Set.ncard_prod, Set.ncard_prod, hA, hU, conics_nonsquare_card p hp]
  exact harith

/-! ## The target -/

/-- The coefficient vector of `α u^2 + β u v + γ v^2` evaluated at
`u = x₁ - a x₀`, `v = x₂ - b x₀`, as a map on coefficient triples. -/
private def conicsTripMap (p : ℕ) (a b : ZMod p) (q : ZMod p × ZMod p × ZMod p) :
    Mon 2 2 → ZMod p :=
  Conics.mkForm a b q.1 q.2.1 q.2.2

private theorem conicsTripMap_injective (p : ℕ) (a b : ZMod p) :
    Function.Injective (conicsTripMap p a b) := by
  intro q q' h
  rcases q with ⟨α, β, γ⟩
  rcases q' with ⟨α', β', γ'⟩
  have h1 : α = α' := by simpa [conicsTripMap] using congrFun h Conics.m11
  have h2 : β = β' := by simpa [conicsTripMap] using congrFun h Conics.m12
  have h3 : γ = γ' := by simpa [conicsTripMap] using congrFun h Conics.m22
  simp only [Prod.mk.injEq]
  exact ⟨h1, h2, h3⟩

/-- `Work.HP.Conics.SharpAt A v` (defined in `Submission/Work/HP/ConicsDefs.lean`) says that
`v ≠ 0`, that `v` lies in the radical of the polar form of `A`, and that the zero set of `A`
is exactly the line `⟨v⟩`.  For `v = (1,a,b)` the number of such forms over `ZMod p`
(`p` an odd prime) is exactly `p(p-1)^2/2`; the stated lower bound is what is needed.

Suggested route.  The map `(α,β,γ) ↦ Work.HP.Conics.mkForm a b α β γ` — the coefficient vector
of `α(x₁-a x₀)² + β(x₁-a x₀)(x₂-b x₀) + γ(x₂-b x₀)²`, already defined in `ConicsDefs`, with
`Work.HP.Conics.qf_mkForm` giving `qf (mkForm a b α β γ) x = q(π x)`, `π x = (x₁-a x₀, x₂-b x₀)`
— is injective (`mkForm_m11/m12/m22` read off `α,β,γ`) and its image lies in the set: `π`
is linear, `π (1,a,b) = 0` so `pol` vanishes on `(1,a,b)`, and `ker π = ⟨(1,a,b)⟩`, so the zero
set is a line exactly when `q(u,v) = αu²+βuv+γv²` has no nontrivial zero.  The number of
anisotropic `(α,β,γ)` is `p(p-1)^2/2`: `q` is isotropic iff `α = 0` or `β²-4αγ` is a nonzero
square, so anisotropic iff `α ≠ 0` and `β²-4αγ` is a non-square; for each `α ≠ 0`, `β` there are
`(p-1)/2` such `γ`.  Hence the cardinality is at least `p(p-1)^2/2`.

Use `Set.ncard` and `p * (p-1) * (p-1) / 2` (Nat division; `p-1` is even). -/
theorem conics_sharp (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b : ZMod p) :
    p * (p - 1) * (p - 1) / 2
      ≤ {A : Mon 2 2 → ZMod p | Work.HP.Conics.SharpAt A ![1, a, b]}.ncard := by
  have hinj := conicsTripMap_injective p a b
  have hsub : conicsTripMap p a b ''
        {q : ZMod p × ZMod p × ZMod p |
          q.1 ≠ 0 ∧ ¬ IsSquare (q.2.1 ^ 2 - 4 * q.1 * q.2.2)}
      ⊆ {A : Mon 2 2 → ZMod p | Work.HP.Conics.SharpAt A ![1, a, b]} := by
    rintro A ⟨q, hq, rfl⟩
    rcases q with ⟨α, β, γ⟩
    obtain ⟨h1, h2⟩ := hq
    simpa [conicsTripMap] using conics_sharpAt_mkForm p hp a b α β γ h1 h2
  calc p * (p - 1) * (p - 1) / 2
      = {q : ZMod p × ZMod p × ZMod p |
          q.1 ≠ 0 ∧ ¬ IsSquare (q.2.1 ^ 2 - 4 * q.1 * q.2.2)}.ncard :=
        (conics_trip_count_aux p hp).symm
    _ = (conicsTripMap p a b ''
          {q : ZMod p × ZMod p × ZMod p |
            q.1 ≠ 0 ∧ ¬ IsSquare (q.2.1 ^ 2 - 4 * q.1 * q.2.2)}).ncard :=
        (Set.ncard_image_of_injective _ hinj).symm
    _ ≤ _ := Set.ncard_le_ncard hsub

end Work.HP
