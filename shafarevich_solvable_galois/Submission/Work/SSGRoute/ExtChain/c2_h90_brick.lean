import Mathlib
import Submission.Work.SSGRoute.ExtChain.C2Deps
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ExtChain

/-- Hilbert 90 at an involution. Let `τ : K ≃ₐ[k] K` satisfy `τ ^ 2 = 1` and `τ ≠ 1` (so `K / K^τ` is quadratic). A unit `w : Kˣ` of norm `1` for that quadratic extension, i.e. `w * (τ • w) = 1`, is a coboundary: `w = b * (τ • b)⁻¹` for some `b : Kˣ`. (`τ ≠ 1` is needed: for `τ = 1` the hypothesis is `w ^ 2 = 1`, satisfied by `w = -1`, while the conclusion fails.) Dischargeable from Noether's generalisation of Hilbert 90, `NK.GlobalCFT.Inclusion.hilbert90_cocycle`, applied over the fixed field `K^τ`: `Gal(K / K^τ) = ⟨τ⟩` since `τ ^ 2 = 1` and `τ ≠ 1`, and the `1`-cocycle sending `τ` to `w` and `1` to `1` satisfies the cocycle condition exactly because `w * (τ • w) = 1`. -/
theorem c2_h90_brick {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (τ : K ≃ₐ[k] K) (hτ : τ ^ 2 = 1) (hnt : τ ≠ 1)
    (w : Kˣ) (hw : w * (τ • w) = 1) :
    ∃ b : Kˣ, w = b * (τ • b)⁻¹ := by
  classical
  -- `τ (τ x) = x` unwound from `τ ^ 2 = 1`.
  have hττ : ∀ x : K, τ (τ x) = x := by
    intro x
    have h : (τ * τ : K ≃ₐ[k] K) = 1 := by rw [← pow_two]; exact hτ
    have h2 := congrArg (fun (e : K ≃ₐ[k] K) => (e : K → K) x) h
    simpa using h2
  -- The hypothesis, read on the underlying field: `w * τ w = 1`.
  have hwval : (w : K) * τ (w : K) = 1 := by
    have h := congrArg (fun u : Kˣ => (u : K)) hw
    simpa [AlgEquiv.smul_units_def, Units.coe_map] using h
  -- The twisted-trace map `c ↦ c + w * τ c` is not identically zero: if it were,
  -- evaluating at `1` would give `w = -1`, and then `τ = 1`, contradicting `hnt`.
  have hex : ∃ c : K, c + (w : K) * τ c ≠ 0 := by
    by_contra h
    push Not at h
    have hw1 : (w : K) = -1 := by
      have h1 := h 1
      rw [map_one, mul_one] at h1
      exact eq_neg_of_add_eq_zero_right h1
    have hfix : ∀ x : K, τ x = x := by
      intro x
      have h2 := h x
      rw [hw1, neg_one_mul] at h2
      have h3 : x - τ x = 0 := by rw [sub_eq_add_neg]; exact h2
      exact (sub_eq_zero.mp h3).symm
    exact hnt (AlgEquiv.ext (fun x => by simpa using hfix x))
  obtain ⟨c, hc⟩ := hex
  -- The standard Hilbert 90 element: `b = c + w * τ c`, which satisfies `w * τ b = b`.
  refine ⟨Units.mk0 (c + (w : K) * τ c) hc, ?_⟩
  have key : (w : K) * τ (c + (w : K) * τ c) = c + (w : K) * τ c := by
    have e1 : τ (c + (w : K) * τ c) = τ c + τ (w : K) * c := by
      rw [map_add, map_mul, hττ c]
    rw [e1]
    calc (w : K) * (τ c + τ (w : K) * c)
        = (w : K) * τ c + ((w : K) * τ (w : K)) * c := by ring
      _ = (w : K) * τ c + c := by rw [hwval, one_mul]
      _ = c + (w : K) * τ c := by ring
  have htb : τ (c + (w : K) * τ c) ≠ 0 := by
    intro h0
    exact hc (τ.injective (by rw [h0, map_zero]))
  apply Units.ext
  rw [Units.val_mul, Units.val_inv_eq_inv_val, AlgEquiv.smul_units_def, Units.coe_map,
    Units.val_mk0]
  have := (eq_div_iff htb).mpr key
  simpa [div_eq_mul_inv] using this

end Work.SSGRoute.ExtChain
