import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.GaloisField

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.PSU3.StageC

/-- **C0** (`Work.PSU3.StageC.frame_normalize`): re-choosing `zc ↦ zc ∘ (·)^{2^i}` turns a
coarse frame whose `nm` is the `2^{i+1}`-power map into one whose `nm` is the squaring map,
keeping `bar`, `κ`, `ζ` and `Q₀`. -/
theorem frame_normalize {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) {ω : G} (hω : Work.PSU3.OmegaHyp fr ω) (i : ℕ)
    (hi : ∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
      (fr.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ (2 ^ (i + 1)))
    (hω2 : ω ^ 2 = fr.zc (((fr.κ fr.ζ : Work.PSU3.E n) + (fr.κ fr.ζ : Work.PSU3.E n)⁻¹) ^ (2 ^ i))) :
    ∃ fr' : Work.PSU3.CoarseFrame H Q t n, fr'.Q0 = fr.Q0 ∧ Work.PSU3.OmegaHyp fr' ω ∧
      (∀ a : (Work.PSU3.E n)ˣ, σE (a : Work.PSU3.E n) = a →
        (fr'.nm a : Work.PSU3.E n) = (a : Work.PSU3.E n) ^ 2) ∧
      ω ^ 2 = fr'.zc ((fr'.κ fr'.ζ : Work.PSU3.E n) + (fr'.κ fr'.ζ : Work.PSU3.E n)⁻¹) := by
  classical
  -- ### Frobenius-power facts on `E n`
  have hpowfix : ∀ y : E n, σE y = y → σE (y ^ (2 ^ i)) = y ^ (2 ^ i) := by
    intro y hy
    rw [map_pow, hy]
  have hpowinj : Function.Injective (fun y : E n => y ^ (2 ^ i)) := by
    intro x y h
    exact (iterateFrobenius (E n) 2 i).injective h
  -- the map `y ↦ y^{2^i}` is a bijection of the fixed field of `σE`
  have hsurj_fixed : ∀ y₀ : E n, σE y₀ = y₀ → ∃ y : E n, σE y = y ∧ y ^ (2 ^ i) = y₀ := by
    intro y₀ hy₀
    let φ : {y : E n // σE y = y} → {y : E n // σE y = y} :=
      fun y => ⟨y.1 ^ (2 ^ i), hpowfix y.1 y.2⟩
    have hinj : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      exact hpowinj (congrArg Subtype.val hab)
    have hsurj : Function.Surjective φ := (Finite.injective_iff_surjective).mp hinj
    obtain ⟨y, hy⟩ := hsurj ⟨y₀, hy₀⟩
    exact ⟨y.1, y.2, congrArg Subtype.val hy⟩
  -- ### The new coordinates
  let zc' : E n → G := fun y => fr.zc (y ^ (2 ^ i))
  let nm' : (E n)ˣ →* (E n)ˣ := Units.map (frobenius (E n) 2)
  have hzc'_apply : ∀ y : E n, zc' y = fr.zc (y ^ (2 ^ i)) := fun _ => rfl
  have hnm_apply : ∀ a : (E n)ˣ, ((nm' a : (E n)ˣ) : E n) = (a : E n) ^ 2 := fun _ => rfl
  -- ### The renormalised frame
  let fr' : CoarseFrame H Q t n :=
    { fr with
      zc := zc'
      zc_mem := fun y hy => fr.zc_mem (y ^ (2 ^ i)) (hpowfix y hy)
      zc_add := fun y y' hy hy' => by
        rw [hzc'_apply, hzc'_apply, hzc'_apply]
        have hadd : (y + y') ^ (2 ^ i) = y ^ (2 ^ i) + y' ^ (2 ^ i) :=
          map_add (iterateFrobenius (E n) 2 i) y y'
        rw [hadd]
        exact fr.zc_add _ _ (hpowfix y hy) (hpowfix y' hy')
      zc_surj := fun z hz => by
        obtain ⟨y₀, hy₀, hzc⟩ := fr.zc_surj z hz
        obtain ⟨y, hyfix, hypow⟩ := hsurj_fixed y₀ hy₀
        exact ⟨y, hyfix, by rw [hzc'_apply, hypow, hzc]⟩
      zc_inj := fun y y' hy hy' h => by
        rw [hzc'_apply, hzc'_apply] at h
        exact hpowinj (fr.zc_inj (y ^ (2 ^ i)) (y' ^ (2 ^ i))
          (hpowfix y hy) (hpowfix y' hy') h)
      s_struct := by
        rw [hzc'_apply]
        simp only [one_pow]
        exact fr.s_struct
      nm := nm'
      nm_F := fun a ha => by
        rw [hnm_apply a, map_pow, ha]
      act_zc_K := fun d hd y hy => by
        have hkd : σE ((fr.κ d : (E n)ˣ) : E n) = ((fr.κ d : (E n)ˣ) : E n) :=
          (fr.mem_K_iff d).mp hd
        have hnm_eq : (fr.nm (fr.κ d) : E n) = ((nm' (fr.κ d) : (E n)ˣ) : E n) ^ (2 ^ i) := by
          rw [hnm_apply (fr.κ d), hi (fr.κ d) hkd, ← pow_mul]
          congr 1
          rw [pow_succ]
          ring
        have hAB : (fr.nm (fr.κ d) : E n) * y ^ (2 ^ i)
            = (((nm' (fr.κ d) : (E n)ˣ) : E n) * y) ^ (2 ^ i) := by
          rw [mul_pow, ← hnm_eq]
        calc (d : G)⁻¹ * zc' y * d
            = fr.zc ((fr.nm (fr.κ d) : E n) * y ^ (2 ^ i)) := by
              rw [hzc'_apply y]
              exact fr.act_zc_K d hd (y ^ (2 ^ i)) (hpowfix y hy)
          _ = fr.zc ((((nm' (fr.κ d) : (E n)ˣ) : E n) * y) ^ (2 ^ i)) := by rw [hAB]
          _ = zc' (((nm' (fr.κ d) : (E n)ˣ) : E n) * y) := by rw [hzc'_apply]
      act_zc_ζ := fun y hy => by
        rw [hzc'_apply y]
        exact fr.act_zc_ζ (y ^ (2 ^ i)) (hpowfix y hy) }
  refine ⟨fr', rfl, ?_, ?_, ?_⟩
  · -- `OmegaHyp` is unchanged: same `Q₀` and same `ζ`
    have hQ0 : fr'.Q0 = fr.Q0 := rfl
    have hζ : fr'.ζ = fr.ζ := rfl
    simpa only [OmegaHyp, hQ0, hζ] using hω
  · -- `nm` is now the squaring map
    intro a _
    exact hnm_apply a
  · -- the `ω²`-condition with exponent `0`
    have hzc : fr'.zc ((fr'.κ fr'.ζ : E n) + (fr'.κ fr'.ζ : E n)⁻¹)
        = fr.zc (((fr.κ fr.ζ : E n) + (fr.κ fr.ζ : E n)⁻¹) ^ (2 ^ i)) := rfl
    rw [hzc]
    exact hω2

end Work.PSU3.StageC
