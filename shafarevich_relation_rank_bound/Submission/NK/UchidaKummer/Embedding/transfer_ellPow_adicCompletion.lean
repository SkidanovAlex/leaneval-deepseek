import Mathlib
import Submission.NK.UchidaKummer.Defs
import Submission.Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
import Submission.Commons.NumberTheory.NumberField.Completion.isScalarTower_adicCompletion
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver

set_option linter.style.haveILetI false

namespace NK.UchidaKummer.Embedding

/-- **Transfer of local `ℓ`-power classes along a prime of local degree one.**

Let `N / L` be a finite extension of number fields, `𝔮` a finite prime of `L` and `𝔭` a prime of
`N` above `𝔮` with `e(𝔭|𝔮) · f(𝔭|𝔮) = 1`.  Then the local extension `N_𝔭 / L_𝔮` has degree one,
so the canonical map `L_𝔮 → N_𝔭` is an isomorphism; consequently an element of `Lˣ` whose image in
`N_𝔭` is an `ℓ`-th power is already an `ℓ`-th power in `L_𝔮`. -/
theorem transfer_ellPow_adicCompletion {L N : Type*} [Field L] [NumberField L] [Field N]
    [NumberField N] [Algebra L N] [FiniteDimensional L N] (ℓ : ℕ)
    (𝔮 : NK.Chebotarev.PrimeIdeal L) (𝔭 : NK.Chebotarev.PrimeIdeal N)
    (h𝔭 : 𝔭.asIdeal.LiesOver 𝔮.asIdeal)
    (hef : NK.UchidaKummer.localDeg 𝔭 𝔮 = 1)
    (b : Lˣ)
    (hb : ∃ c : (𝔭.adicCompletion N)ˣ,
      algebraMap N (𝔭.adicCompletion N) (algebraMap L N (b : L)) = (c : 𝔭.adicCompletion N) ^ ℓ) :
    ∃ c : (𝔮.adicCompletion L)ˣ,
      algebraMap L (𝔮.adicCompletion L) (b : L) = (c : 𝔮.adicCompletion L) ^ ℓ := by
  classical
  obtain ⟨c, hc⟩ := hb
  -- the canonical map `L_𝔮 → N_𝔭` induced by `𝔭 | 𝔮`
  let φ : 𝔮.adicCompletion L →+* 𝔭.adicCompletion N :=
    Commons.RingTheory.Henselian.adicCompletionMap 𝔮 𝔭 h𝔭
  -- `e · f = 1`, so the local degree `[N_𝔭 : L_𝔮]` is `1`
  have hef' : 𝔭.asIdeal.ramificationIdx (NumberField.RingOfIntegers L) *
      𝔭.asIdeal.inertiaDeg (NumberField.RingOfIntegers L) = 1 := by
    simpa [NK.UchidaKummer.localDeg] using hef
  letI : Algebra (𝔮.adicCompletion L) (𝔭.adicCompletion N) := RingHom.toAlgebra φ
  have hfr : Module.finrank (𝔮.adicCompletion L) (𝔭.adicCompletion N) = 1 := by
    rw [← Commons.NumberTheory.NumberField.Completion.finrank_adicCompletion_eq_ramificationIdx_mul_inertiaDeg
      𝔮 𝔭 h𝔭, hef']
  -- a degree-one extension of fields has a bijective structure map
  have hbij := Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfr
  have hsurj : Function.Surjective φ := by
    rw [← RingHom.algebraMap_toAlgebra φ]
    exact hbij.2
  -- `φ` intertwines the two structure maps
  have hφa : φ (algebraMap L (𝔮.adicCompletion L) (b : L)) =
      algebraMap N (𝔭.adicCompletion N) (algebraMap L N (b : L)) := by
    exact Commons.RingTheory.Henselian.adicCompletionMap_apply 𝔮 𝔭 h𝔭 (b : L)
  -- lift the `ℓ`-th root `c` along the surjection `φ`
  obtain ⟨u, hu⟩ := hsurj (c : 𝔭.adicCompletion N)
  have hu0 : u ≠ 0 := by
    intro h0
    have : (c : 𝔭.adicCompletion N) = 0 := by rw [← hu, h0, map_zero]
    exact Units.ne_zero c this
  refine ⟨Units.mk0 u hu0, ?_⟩
  rw [Units.val_mk0]
  have hstep : φ (u ^ ℓ) = φ (algebraMap L (𝔮.adicCompletion L) (b : L)) := by
    rw [map_pow, hu, ← hc]
    exact hφa.symm
  exact (RingHom.injective φ hstep).symm

end NK.UchidaKummer.Embedding
