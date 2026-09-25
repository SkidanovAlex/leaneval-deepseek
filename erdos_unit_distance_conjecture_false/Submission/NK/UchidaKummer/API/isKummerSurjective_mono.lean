import Mathlib
import Submission.NK.UchidaKummer.Defs

namespace NK.UchidaKummer.API

/-- **Monotonicity of the Kummer local surjection in the set of primes.**

If the diagonal map `Kˣ → ∏_{𝔮 ∈ T} K_𝔮ˣ / (K_𝔮ˣ)^ℓ` is surjective, then so is its
restriction to any subset `S ⊆ T`: a prescribed tuple of local `ℓ`-power classes on `S` is
extended by the trivial class off `S`, lifted by surjectivity at `T`, and the resulting global
unit restricts to the prescribed tuple. -/
theorem isKummerSurjective_mono {K : Type*} [Field K] [NumberField K] {ℓ : ℕ}
    {S T : Finset (NK.Chebotarev.PrimeIdeal K)} (hST : ∀ 𝔮 ∈ S, 𝔮 ∈ T)
    (h : NK.UchidaKummer.IsKummerSurjective K ℓ T) :
    NK.UchidaKummer.IsKummerSurjective K ℓ S := by
  intro y
  classical
  let y' : ∀ 𝔮 : T,
      (𝔮.1.adicCompletion K)ˣ ⧸ NK.UchidaKummer.ellPowSubgroup (𝔮.1.adicCompletion K) ℓ :=
    fun 𝔮 => if hq : 𝔮.1 ∈ S then y ⟨𝔮.1, hq⟩ else 1
  obtain ⟨b, hb⟩ := h y'
  refine ⟨b, fun 𝔮 => ?_⟩
  have h1 : 𝔮.1 ∈ T := hST 𝔮.1 𝔮.2
  have h2 := hb ⟨𝔮.1, h1⟩
  simp only [y', dif_pos 𝔮.2] at h2
  exact h2

end NK.UchidaKummer.API
