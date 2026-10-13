import Mathlib
import Submission.Work.DSM5c.ChartComparison

namespace Work.DSM5c.G2

universe u

theorem kerTheta_decompU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W]
    (Q : DSMap.PerfectoidData p W)
    (hθ : Function.Surjective (WittVector.fontaineTheta (p := p) (R := W)))
    (v : Wˣ) (hv : Q.ϖ 0 ^ p = (p : W) * (v : W))
    (z₀ : WittVector p (PreTilt W p))
    (hz₀ : WittVector.fontaineTheta (p := p) (R := W) z₀ = (v : W))
    {k : WittVector p (PreTilt W p)}
    (hk : WittVector.fontaineTheta (p := p) (R := W) k = 0) :
    ∃ b : PreTilt W p, ∃ u : WittVector p (PreTilt W p),
      WittVector.fontaineTheta (p := p) (R := W) u = 0 ∧
        k = WittVector.teichmuller p b *
              (WittVector.teichmuller p (Work.DSM5c.tiltVarpi Q ^ p) -
                (p : WittVector p (PreTilt W p)) * z₀) +
            (p : WittVector p (PreTilt W p)) * u := by
  have hϖ : PreTilt.untilt (Work.DSM5c.tiltVarpi Q) = Q.ϖ 0 := by
    rw [Work.DSM5c.tiltVarpi_eq_varpiTilt]
    exact Work.DSPB1.varpiTilt_untilt Q
  set ξ : WittVector p (PreTilt W p) :=
    WittVector.teichmuller p (Work.DSM5c.tiltVarpi Q ^ p) -
      (p : WittVector p (PreTilt W p)) * z₀ with hξdef
  -- `k` lies in `(p) ⊔ ker θ` because it lies in `ker θ`
  have hk_mem : k ∈ Ideal.span {(p : WittVector p (PreTilt W p))} ⊔
      RingHom.ker (WittVector.fontaineTheta (p := p) (R := W)) :=
    Submodule.mem_sup.mpr ⟨0, Submodule.zero_mem _, k, RingHom.mem_ker.mpr hk, by simp⟩
  have hcc : WittVector.constantCoeff k ∈ Ideal.span {Work.DSM5c.tiltVarpi Q ^ p} :=
    (Work.DSM5c.mem_span_p_sup_ker_fontaineTheta (W := W) Q hθ k).mp hk_mem
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hcc
  -- the `constantCoeff` of `ξ` is `ϖ♭ ^ p`
  have hccξ : WittVector.constantCoeff ξ = Work.DSM5c.tiltVarpi Q ^ p := by
    rw [hξdef, map_sub, map_mul, Work.DSM5c.constantCoeff_teichmuller',
      Work.DSM5c.constantCoeff_p_eq_zero, zero_mul, sub_zero]
  have hccy : WittVector.constantCoeff (k - WittVector.teichmuller p b * ξ) = 0 := by
    rw [map_sub, map_mul, Work.DSM5c.constantCoeff_teichmuller', hccξ, hb]
    ring
  -- hence `k - [b] ξ ∈ (p)`, say `= p · u`
  have hmem : k - WittVector.teichmuller p b * ξ ∈
      Ideal.span {(p : WittVector p (PreTilt W p))} := by
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    simpa only [WittVector.constantCoeff_apply] using hccy
  obtain ⟨u, hu⟩ := Ideal.mem_span_singleton'.mp hmem
  -- and `θ ξ = 0`
  have hθξ : WittVector.fontaineTheta (p := p) (R := W) ξ = 0 := by
    rw [hξdef, map_sub, map_mul, map_natCast, WittVector.fontaineTheta_teichmuller, hz₀,
      map_pow, hϖ, hv, sub_self]
  have hku : k = WittVector.teichmuller p b * ξ + (p : WittVector p (PreTilt W p)) * u := by
    rw [mul_comm (p : WittVector p (PreTilt W p)) u, hu]
    abel
  -- `θ u = 0`, since `p` is a non-zero-divisor of `W`
  have hθu : WittVector.fontaineTheta (p := p) (R := W) u = 0 := by
    have h0 : (p : W) * WittVector.fontaineTheta (p := p) (R := W) u = 0 := by
      have h := congrArg (WittVector.fontaineTheta (p := p) (R := W)) hku
      rw [hk, map_add, map_mul, map_mul, map_natCast, hθξ, mul_zero, zero_add] at h
      exact h.symm
    exact Q.torsionFree (by simpa using h0)
  exact ⟨b, u, hθu, by rw [hku, hξdef]⟩

end Work.DSM5c.G2
