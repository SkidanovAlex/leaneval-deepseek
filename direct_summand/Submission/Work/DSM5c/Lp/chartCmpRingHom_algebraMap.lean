import Mathlib
import Submission.Work.DSM5c.Lp.LpDefs

/-!
# The comparator `chartCmpRingHom` is the `W`-algebra structure of the mod-`p` chart

`Work.DSM5c.Lp.chartCmpRingHom Q … S : D_S →+* L_S = R_S ⧸ (φ_S (ϖ♭)^p)` is the `0`-th Witt
coordinate of the chart untilt `D_S = untiltOf R_S φ_S`, and `Work.DSM5c.chartLRingHom Q … S : W →+*
L_S` is the `W`-algebra structure of `L_S` obtained through PB2
(`W → W⧸(p) ≃ W♭⧸(ϖ♭)^p → R_S⧸(φ_S(ϖ♭)^p)`).

This file proves that the two agree:
`chartCmpRingHom ∘ (untiltOf.algebraMap hθ φ_S) = chartLRingHom`.

Both sides send `w = θ_W x` (`x : 𝕎 W♭`, using `hθ`) to the class of `φ_S (constantCoeff x)` in
`L_S`.  On the left this is `chartCmpRingHom_mk`; on the right it is the definition of
`chartLRingHom` together with `WittVector.mk_fontaineTheta`
(`θ_W x ≡ (constantCoeff x)♯ mod p`) and PB2's `Work.DSM5c.pb2Equiv_mk_untilt`.
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000

namespace Work.DSM5c.Lp

universe a

theorem chartCmpRingHom_algebraMap {p : ℕ} [Fact p.Prime] {W : Type a} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type a} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ) (S : Finset ι) (w : W) :
    Work.DSM5c.Lp.chartCmpRingHom Q hθ t tr htr0 htr j₀ e S
        (Work.DSM5c.untiltOf.algebraMap hθ (Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S) w) =
      Work.DSM5c.chartLRingHom Q t tr htr0 htr j₀ e S w := by
  -- Write `w` as `θ_W x` (`hθ`); both sides are then computed from `x : 𝕎 W♭`.
  obtain ⟨x, hx⟩ := hθ w
  rw [← hx]
  rw [Work.DSM5c.untiltOf.algebraMap_fontaineTheta]
  -- Both sides equal the class of `φ_S (constantCoeff x)` in `L_S`.
  trans Ideal.Quotient.mk (Work.DSM5c.chartLIdeal Q t tr htr0 htr j₀ e S)
      (Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S (WittVector.constantCoeff x))
  · -- `chartCmpRingHom` is `constantCoeff`, natural in the Witt-vector map.
    have h1 := Work.DSM5c.Lp.chartCmpRingHom_mk Q hθ t tr htr0 htr j₀ e S
        ((WittVector.map (Work.DSM5c.chartPhi Q t tr htr0 htr j₀ e S)) x)
    rw [Work.DSM5c.wittVector_constantCoeff_map] at h1
    exact h1
  · -- `chartLRingHom` sends `θ_W x` to the class of `φ_S (constantCoeff x)` through PB2.
    have key : (Work.DSM5c.pb2Equiv Q).toRingHom
        ((Ideal.Quotient.mk (Ideal.span {(p : W)})) ((WittVector.fontaineTheta W p) x)) =
        (Ideal.Quotient.mk (Ideal.span {Work.DSM5c.tiltVarpi Q ^ p}))
          (WittVector.constantCoeff x) := by
      -- `mk_fontaineTheta`: `θ_W x ≡ (constantCoeff x)♯ (mod p)`, then PB2.
      rw [WittVector.mk_fontaineTheta, ← PreTilt.mk_untilt_eq_coeff_zero]
      exact Work.DSM5c.pb2Equiv_mk_untilt Q _
    rw [Work.DSM5c.chartLRingHom, RingHom.comp_apply, RingHom.comp_apply, key,
      Ideal.Quotient.lift_mk]
    rfl

end Work.DSM5c.Lp
