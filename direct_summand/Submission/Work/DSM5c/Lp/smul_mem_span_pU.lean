import Mathlib
import Submission.Work.DSPB1.All
import Submission.Work.DSM5c.CharP
import Submission.Work.DSM5c.ChartLp

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

namespace Work.DSM5c.Lp

open CategoryTheory DSMap DSMap.Mix DSMap.Mix2

universe u

/-- **The degree-`0` arithmetic of the transport** (`Submission/Work/DSM5c/Lp/probe/Stmts.lean`,
`stmt_smul_mem_span_p`): if `x : W♭ = PreTilt W p` represents `pb2Equiv (mk w)` in `W♭ ⧸ (ϖ♭)^p`
and every `(ϖ♭)^{1/p^k} · x` lies in `((ϖ♭)^p)`, then every `ϖ_k · w` lies in `(p)`.

Route: `pb2Equiv_mk_untilt` plus injectivity of `pb2Equiv` gives `w ≡ ♯x (mod p)`, where
`♯ = PreTilt.untilt` (a *multiplicative* map, `PreTilt.untilt : PreTilt W p →* W`); so
`ϖ_k · w ≡ ♯((ϖ♭)^{1/p^k} · x)` modulo `(p)` (`Work.DSPB1.varpiTiltShift_untilt` gives
`♯(ϖ♭_k) = Q.ϖ k`, `Work.DSPB1.varpiTiltShift_eq_symm` identifies `ϖ♭_k = (frob.symm)^[k] (ϖ♭)`);
and if `(ϖ♭)^{1/p^k} · x ∈ ((ϖ♭)^p)`, say `= (ϖ♭)^p · c`, then applying `♯` gives
`♯(ϖ♭)^p · ♯c = (Q.ϖ 0)^p · ♯c = p · (unit · ♯c) ∈ (p)` using `Q.unit`. -/
theorem smul_mem_span_pU {p : ℕ} [Fact p.Prime] {W : Type u} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W]
    (Q : DSMap.PerfectoidData p W) (w : W) (x : PreTilt W p)
    (hx : Ideal.Quotient.mk (Ideal.span {Work.DSM5c.tiltVarpi Q ^ p}) x =
      Work.DSM5c.pb2Equiv Q (Ideal.Quotient.mk (Ideal.span {(p : W)}) w))
    (h : ∀ k, ((frobeniusEquiv (PreTilt W p) p).symm^[k] (Work.DSM5c.tiltVarpi Q)) * x ∈
      Ideal.span {Work.DSM5c.tiltVarpi Q ^ p}) :
    ∀ k, Q.ϖ k * w ∈ Ideal.span {(p : W)} := by
  -- `pb2Equiv` inverts `♯` mod `p`, so `hx` identifies `w` with `♯x` modulo `(p)`.
  have hmod : Ideal.Quotient.mk (Ideal.span {(p : W)}) (PreTilt.untilt x) =
      Ideal.Quotient.mk (Ideal.span {(p : W)}) w := by
    apply RingEquiv.injective (Work.DSM5c.pb2Equiv Q)
    rw [Work.DSM5c.pb2Equiv_mk_untilt]
    exact hx
  have hmem : w - PreTilt.untilt x ∈ Ideal.span {(p : W)} := by
    have h1 : PreTilt.untilt x - w ∈ Ideal.span {(p : W)} := Ideal.Quotient.eq.mp hmod
    have h2 : w - PreTilt.untilt x = -(PreTilt.untilt x - w) := by ring
    rw [h2]
    exact neg_mem h1
  intro k
  have hu0 : PreTilt.untilt (Work.DSM5c.tiltVarpi Q) = Q.ϖ 0 := by
    rw [Work.DSM5c.tiltVarpi_eq_varpiTilt, Work.DSPB1.varpiTilt_untilt]
  have hu1 : PreTilt.untilt ((frobeniusEquiv (PreTilt W p) p).symm^[k] (Work.DSM5c.tiltVarpi Q))
      = Q.ϖ k := by
    have hshift : (frobeniusEquiv (PreTilt W p) p).symm^[k] (Work.DSM5c.tiltVarpi Q)
        = Work.DSPB1.varpiTiltShift Q k := by
      rw [Work.DSM5c.tiltVarpi_eq_varpiTilt, Work.DSPB1.varpiTiltShift_eq_symm]
    rw [hshift, Work.DSPB1.varpiTiltShift_untilt]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp (h k)
  have hck : Q.ϖ k * PreTilt.untilt x ∈ Ideal.span {(p : W)} := by
    have hun := congrArg PreTilt.untilt hc
    rw [map_mul, map_mul, map_pow, hu1, hu0] at hun
    obtain ⟨u, hu⟩ := Q.unit
    rw [hun, hu, mul_assoc]
    exact Ideal.mem_span_singleton.mpr ⟨↑u * PreTilt.untilt c, rfl⟩
  have hw : Q.ϖ k * w = Q.ϖ k * PreTilt.untilt x + Q.ϖ k * (w - PreTilt.untilt x) := by ring
  rw [hw]
  exact Ideal.add_mem _ hck (Ideal.mul_mem_left _ _ hmem)

end Work.DSM5c.Lp
