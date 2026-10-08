import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.SzA

/-- Field core of the fourth case of `orbit_covering`: with `t = b/(a·θa)`, `mu = θ⁻¹(t⁻¹) + 1`
and `(1 + θmu)·t = 1`, the second coordinate of `h_{a⁻¹(1+μ⁻¹)}(a,b)` equals
`μ⁻¹ (θμ)⁻¹ (1+μ)`. -/
private lemma case4_coord2 {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K) {a t mu : K}
    (ha : a ≠ 0) (hmu0 : mu ≠ 0)
    (hkey : (1 + θ mu) * t = 1) :
    a⁻¹ * (1 + mu⁻¹) * θ (a⁻¹ * (1 + mu⁻¹)) * (t * (a * θ a))
      = mu⁻¹ * (θ mu)⁻¹ * (1 + mu) := by
  have hθa : θ a ≠ 0 := fun h => ha (θ.injective (by rw [h, map_zero]))
  have hθmu : θ mu ≠ 0 := fun h => hmu0 (θ.injective (by rw [h, map_zero]))
  have h1θmu : 1 + θ mu ≠ 0 := by
    intro h
    rw [h, zero_mul] at hkey
    exact one_ne_zero hkey.symm
  have ht : t = (1 + θ mu)⁻¹ := eq_inv_of_mul_eq_one_right hkey
  have hθlam : θ (a⁻¹ * (1 + mu⁻¹)) = (θ a)⁻¹ * (1 + (θ mu)⁻¹) := by
    rw [map_mul, map_inv₀, map_add, map_one, map_inv₀]
  rw [hθlam, ht]
  field_simp
  ring

/-- **HB III XI 11.11, orbit form: the torus orbits of `A(K,θ) ∖ {1}` are represented by `(0,1)`, `(1,0)`, `(1,1)` and the `X_μ = (1+μ⁻¹, μ⁻¹(θμ)⁻¹(1+μ))`, `μ ∉ {0,1}`.**

Concretely: under the action `h_λ (a,b) = (λa, λ^{1+θ}b)`, every non-identity element of
`A(K,θ)` can be brought into that list of `q+1` representatives.  This is the partition of `Q^#`
used by HB III XI 11.11–11.13.  The `q-2` elements `X_μ` have invariant `b/(a·θa) = 1/(1+μ^θ)`,
which runs over `K ∖ {0,1}` because `μ ↦ μ^θ` is a bijection of `Kˣ ∖ {1}`; `(1,0)` has
invariant `0`, `(1,1)` has invariant `1`, and `(0,1)` represents the centre (`orbit_invariant`,
already in the workspace, classifies the non-central orbits by that invariant).

Witnesses for the proof: `a = 0`: `λ` with `λ·θλ = b⁻¹` (that is `units_mul_map_surjective θ hodd`
from `suzukiTitsOfFix.lean`); `b = 0`: `λ = a⁻¹`; `b = a·θa`: `λ = a⁻¹` (then
`λ^{1+θ}b = a^{-1-θ}aθa = 1`); otherwise with `t := b/(a·θa)` (so `t ∉ {0,1}`), take
`μ := θ⁻¹(t⁻¹) + 1` and `λ := a⁻¹(1+μ⁻¹)`; the coordinate computation is
`λ·θλ·b = t(1+μ)(1+θμ)/(μ·θμ)` together with `t(1+θμ) = 1`. -/
theorem orbit_covering {K : Type*} [Field K] [CharP K 2] [Finite K] (θ : K ≃+* K)
    (hodd : Odd (orderOf θ)) {a b : K} (hab : (a, b) ≠ (0, 0)) :
    (∃ lam : K, lam ≠ 0 ∧ (⟨lam * a, lam * θ lam * b⟩ : Work.ZassenhausSuzuki.SzA K θ)
      = ⟨0, 1⟩) ∨
    (∃ lam : K, lam ≠ 0 ∧ (⟨lam * a, lam * θ lam * b⟩ : Work.ZassenhausSuzuki.SzA K θ)
      = ⟨1, 0⟩) ∨
    (∃ lam : K, lam ≠ 0 ∧ (⟨lam * a, lam * θ lam * b⟩ : Work.ZassenhausSuzuki.SzA K θ)
      = ⟨1, 1⟩) ∨
    (∃ lam mu : K, lam ≠ 0 ∧ mu ≠ 0 ∧ mu ≠ 1 ∧
      (⟨lam * a, lam * θ lam * b⟩ : Work.ZassenhausSuzuki.SzA K θ) =
        ⟨1 + mu⁻¹, mu⁻¹ * (θ mu)⁻¹ * (1 + mu)⟩) := by
  by_cases ha : a = 0
  · -- Case 1: `a = 0`, `b ≠ 0`; `λ·θλ = b⁻¹` by surjectivity of `x ↦ x·θx` on `Kˣ`.
    have hb : b ≠ 0 := by
      intro hb0
      exact hab (by simp [ha, hb0])
    left
    obtain ⟨u, hu⟩ :=
      Work.ZassenhausSuzuki.units_mul_map_surjective θ hodd (Units.mk0 b⁻¹ (inv_ne_zero hb))
    refine ⟨(u : K), u.ne_zero, ?_⟩
    have hval : (u : K) * θ (u : K) = b⁻¹ := by
      have h := congrArg (fun w : Kˣ => (w : K)) hu
      simpa using h
    ext
    · simp [ha]
    · show (u : K) * θ (u : K) * b = 1
      rw [hval, inv_mul_cancel₀ hb]
  · by_cases hb : b = 0
    · -- Case 2: `b = 0`, `a ≠ 0`; `λ = a⁻¹`.
      right; left
      refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
      ext
      · show a⁻¹ * a = 1
        rw [inv_mul_cancel₀ ha]
      · show a⁻¹ * θ a⁻¹ * b = 0
        rw [hb, mul_zero]
    · by_cases h3 : b = a * θ a
      · -- Case 3: `b = a·θa`, `a ≠ 0`; `λ = a⁻¹`.
        right; right; left
        have hθa : θ a ≠ 0 := fun h => ha (θ.injective (by rw [h, map_zero]))
        refine ⟨a⁻¹, inv_ne_zero ha, ?_⟩
        ext
        · show a⁻¹ * a = 1
          rw [inv_mul_cancel₀ ha]
        · show a⁻¹ * θ a⁻¹ * b = 1
          rw [h3, map_inv₀]
          calc a⁻¹ * (θ a)⁻¹ * (a * θ a) = (a⁻¹ * a) * ((θ a)⁻¹ * θ a) := by ring
            _ = 1 := by rw [inv_mul_cancel₀ ha, inv_mul_cancel₀ hθa, mul_one]
      · -- Case 4: `a ≠ 0`, `b ≠ 0`, `b ≠ a·θa`; `t = b/(a·θa)`, `μ = θ⁻¹(t⁻¹) + 1`,
        -- `λ = a⁻¹(1+μ⁻¹)`.
        right; right; right
        have hθa : θ a ≠ 0 := fun h => ha (θ.injective (by rw [h, map_zero]))
        have haθa : a * θ a ≠ 0 := mul_ne_zero ha hθa
        set t : K := b / (a * θ a) with ht_def
        have ht0 : t ≠ 0 := by rw [ht_def]; exact div_ne_zero hb haθa
        have ht1 : t ≠ 1 := by
          rw [ht_def]
          intro h
          exact h3 ((div_eq_one_iff_eq haθa).mp h)
        have hb_eq : b = t * (a * θ a) := by
          rw [ht_def]
          exact (div_mul_cancel₀ b haθa).symm
        set mu : K := θ.symm t⁻¹ + 1 with hmu_def
        have hmu_plus : mu + 1 = θ.symm t⁻¹ := by
          rw [hmu_def, add_assoc, CharTwo.add_self_eq_zero, add_zero]
        have hθmu_eq : θ mu = t⁻¹ + 1 := by
          rw [hmu_def, map_add, map_one, RingEquiv.apply_symm_apply]
        have hkey : (1 + θ mu) * t = 1 := by
          have h : 1 + θ mu = t⁻¹ := by
            rw [hθmu_eq]
            calc (1 : K) + (t⁻¹ + 1) = (1 + t⁻¹) + 1 := (add_assoc _ _ _).symm
              _ = (t⁻¹ + 1) + 1 := by rw [add_comm (1 : K) t⁻¹]
              _ = t⁻¹ + (1 + 1) := add_assoc _ _ _
              _ = t⁻¹ + 0 := by rw [CharTwo.add_self_eq_zero (1 : K)]
              _ = t⁻¹ := add_zero _
          rw [h, inv_mul_cancel₀ ht0]
        have hμ1ne : θ.symm t⁻¹ ≠ 0 :=
          fun h => inv_ne_zero ht0 (θ.symm.injective (by rw [h, map_zero]))
        have hmu0 : mu ≠ 0 := by
          intro h
          have hx1 : θ.symm t⁻¹ = 1 := by
            rw [hmu_def] at h
            have h' : θ.symm t⁻¹ + (1 + 1) = 0 + 1 := by rw [← add_assoc, h, zero_add]
            rwa [CharTwo.add_self_eq_zero (1 : K), add_zero, zero_add] at h'
          have htinv1 : t⁻¹ = 1 := by
            have := congrArg θ hx1
            rwa [RingEquiv.apply_symm_apply, map_one] at this
          exact ht1 (by rw [← inv_inv t, htinv1, inv_one])
        have hmu1 : mu ≠ 1 := by
          intro h
          rw [hmu_def] at h
          have hx0 : θ.symm t⁻¹ = 0 := by
            have : θ.symm t⁻¹ + 1 = 0 + 1 := by rw [h, zero_add]
            exact add_right_cancel this
          have ht0' : t = 0 := by
            have : t⁻¹ = 0 := by
              have hh := congrArg θ hx0
              simpa using hh
            exact inv_eq_zero.mp this
          exact ht0 ht0'
        have h1muinv : 1 + mu⁻¹ ≠ 0 := by
          have heq : (mu + 1) * mu⁻¹ = 1 + mu⁻¹ := by
            rw [add_mul, one_mul, mul_inv_cancel₀ hmu0]
          rw [← heq]
          exact mul_ne_zero (by rw [hmu_plus]; exact hμ1ne) (inv_ne_zero hmu0)
        refine ⟨a⁻¹ * (1 + mu⁻¹), mu, mul_ne_zero (inv_ne_zero ha) h1muinv,
          hmu0, hmu1, ?_⟩
        ext
        · show a⁻¹ * (1 + mu⁻¹) * a = 1 + mu⁻¹
          calc a⁻¹ * (1 + mu⁻¹) * a = (a⁻¹ * a) * (1 + mu⁻¹) := by ring
            _ = 1 + mu⁻¹ := by rw [inv_mul_cancel₀ ha, one_mul]
        · show a⁻¹ * (1 + mu⁻¹) * θ (a⁻¹ * (1 + mu⁻¹)) * b
              = mu⁻¹ * (θ mu)⁻¹ * (1 + mu)
          rw [hb_eq]
          exact case4_coord2 θ ha hmu0 hkey

end Work.ZassenhausSuzuki.SzA
