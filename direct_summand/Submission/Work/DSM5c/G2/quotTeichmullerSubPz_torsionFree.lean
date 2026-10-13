import Mathlib
import Submission.Work.DSM5c.Untilt.untilt_p_torsionFree

namespace Work.DSM5c.G2

open WittVector

/-- `p`-torsion-freeness of `𝕎 R ⧸ ([c] - p·z)`, i.e. the "ξ-form" of
`Work.DSM5c.Untilt.untilt_p_torsionFree` (`Submission/Work/DSM5c/Untilt/untilt_p_torsionFree.lean`)
generalised from `z = 1` to an arbitrary Witt vector `z`.  Let `A := 𝕎 R`, `ξ := [c] - p·z`, and
suppose `p·y = ξ·a`.  Then `[c]·a = ξ·a + p·z·a = p·(y + z·a) ∈ (p)`, so applying
`WittVector.constantCoeff` (which sends `[c]` to `c` and multiples of `p` to `0`, `R` being of
characteristic `p`) gives `c · constantCoeff a = 0`; as `c` is a non-zero-divisor,
`constantCoeff a = 0`, i.e. `a ∈ (p) = RingHom.ker constantCoeff`
(`WittVector.ker_constantCoeff`); write `a = p·c'`.  Then `p·y = ξ·(p·c') = p·(ξ·c')`, and `𝕎 R` is
`p`-torsion-free (`WittVector.eq_zero_of_p_mul_eq_zero`), so `y = ξ·c' ∈ (ξ)`. -/
theorem quotTeichmullerSubPz_torsionFree {p : ℕ} [Fact p.Prime] {R : Type*}
    [CommRing R] [CharP R p] [PerfectRing R p] (c : R) (hc : ∀ x : R, c * x = 0 → x = 0)
    (z : WittVector p R) :
    IsSMulRegular
      (WittVector p R ⧸ Ideal.span {WittVector.teichmuller p c - (p : WittVector p R) * z})
      (p : WittVector p R ⧸ Ideal.span {WittVector.teichmuller p c - (p : WittVector p R) * z}) := by
  -- it suffices to kill `p`-torsion
  have key : ∀ y : WittVector p R ⧸
        Ideal.span {WittVector.teichmuller p c - (p : WittVector p R) * z},
      (p : WittVector p R ⧸ Ideal.span {WittVector.teichmuller p c - (p : WittVector p R) * z})
        • y = 0 → y = 0 := by
    intro y hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [smul_eq_mul] at hy
    have hpmk :
        (p : WittVector p R ⧸
            Ideal.span {WittVector.teichmuller p c - (p : WittVector p R) * z}) =
          Ideal.Quotient.mk
            (Ideal.span {WittVector.teichmuller p c - (p : WittVector p R) * z})
            (p : WittVector p R) :=
      (map_natCast
        (Ideal.Quotient.mk
          (Ideal.span {WittVector.teichmuller p c - (p : WittVector p R) * z})) p).symm
    rw [hpmk, ← map_mul] at hy
    have hmem : (p : WittVector p R) * x ∈
        Ideal.span {WittVector.teichmuller p c - (p : WittVector p R) * z} :=
      Ideal.Quotient.eq_zero_iff_mem.mp hy
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hmem
    -- `[c]·a = p·(x + z·a)`, hence `a ∈ (p)`
    have hmem_p : a ∈ Ideal.span {(p : WittVector p R)} := by
      refine Work.DSM5c.Untilt.mem_span_p_of_teichmuller_mul_mem c hc ?_
      rw [show WittVector.teichmuller p c * a = (p : WittVector p R) * (x + z * a) from by
        calc WittVector.teichmuller p c * a
            = ((WittVector.teichmuller p c - (p : WittVector p R) * z) +
                (p : WittVector p R) * z) * a := by ring
          _ = (p : WittVector p R) * x + (p : WittVector p R) * (z * a) := by
                rw [add_mul, ha]; ring
          _ = (p : WittVector p R) * (x + z * a) := by ring]
      exact Ideal.mem_span_singleton.mpr ⟨x + z * a, rfl⟩
    obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.mp hmem_p
    -- `p · (x - ξ·c') = 0`, and `𝕎 R` is `p`-torsion-free
    have hx : x = (WittVector.teichmuller p c - (p : WittVector p R) * z) * c' := by
      have h : (p : WittVector p R) * (x -
          (WittVector.teichmuller p c - (p : WittVector p R) * z) * c') = 0 := by
        rw [mul_sub, ha, hc']
        ring
      have h' : (x - (WittVector.teichmuller p c - (p : WittVector p R) * z) * c') *
          (p : WittVector p R) = 0 := by
        simpa [mul_comm] using h
      exact sub_eq_zero.mp
        (WittVector.eq_zero_of_p_mul_eq_zero (p := p) (k := R)
          (x - (WittVector.teichmuller p c - (p : WittVector p R) * z) * c') h')
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton.mpr ⟨c', hx⟩
  -- conclude injectivity from `p`-torsion-freeness
  intro y y' hyy'
  have hyy'' :
      (p : WittVector p R ⧸ Ideal.span {WittVector.teichmuller p c - (p : WittVector p R) * z}) *
          y =
        (p : WittVector p R ⧸ Ideal.span {WittVector.teichmuller p c - (p : WittVector p R) * z}) *
          y' := by
    simpa [smul_eq_mul] using hyy'
  have h0 :
      (p : WittVector p R ⧸ Ideal.span {WittVector.teichmuller p c - (p : WittVector p R) * z}) *
          (y - y') = 0 := by
    rw [mul_sub, hyy'', sub_self]
  exact sub_eq_zero.mp (key (y - y') (by simpa [smul_eq_mul] using h0))

end Work.DSM5c.G2
