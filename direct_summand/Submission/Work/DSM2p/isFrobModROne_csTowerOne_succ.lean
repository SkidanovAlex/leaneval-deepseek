import Mathlib
import Submission.Work.DSM2p.POidRecOne
import Submission.Work.DSM2p.frobSurj_rootClosurePos
import Submission.Work.DSM2p.exists_CSAlgOne_add_varpi_pow_mul_decomp

open scoped Classical

-- The rings `Lam1 A p` and `Lam1Loc A p ϖ` are built from a quotient of an `MvPolynomial` ring
-- and a localization; the default heartbeat budget is not enough for the instance searches below.
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

namespace Work.DSM2p

/-! ## The invariant is preserved by one tower step (one-polynomial case)

This is the one-variable (`Λ = A[T^{1/p^∞}]`) counterpart of
`Work.DSM2p.isFrobModR_csTower_succ` of `POidRecStep.lean`: if `R = csTowerOne F i` is
Frobenius-surjective modulo `ϖ ^ p` (with cofactor in `R`), then so is
`csTowerOne F (i+1)`.

For the generator `w = v * uPiOne m` of the step (with `v ^ (p ^ (m+1)) = ϖ ^ p * e`, `e ∈ R`,
so that `w ^ (p ^ (m+1)) = e`) the induction hypothesis gives `v₁ ∈ R` with
`v₁ ^ p = v - ϖ ^ p * c` and `c' ∈ R` with `(c') ^ p = c - ϖ ^ p * f`.  Put
`z = v₁ * uPiOne (m+1) ∈ R'` (the induction hypothesis is applied at level `m+1` to `v₁`,
using `pow_sub_pow_mem`) and `ε = π_{m+1} ^ (p^(m+1) - 1) * c' ∈ R'`.  Then
`w - (z + ε) ^ p = ϖ ^ p * (π_m ^ (p^(m+1)-1) * f - v⁻¹ * h)`, where `h` is the cross-term
cofactor of `(z, ε)`. -/
theorem isFrobModROne_csTowerOne_succ (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) (i : ℕ)
    (h : IsFrobModROne (p := p) (A := A) (P := P) F (csTowerOne (p := p) (A := A) (P := P) F i)) :
    IsFrobModROne (p := p) (A := A) (P := P) F (csTowerOne (p := p) (A := A) (P := P) F (i + 1)) := by
  obtain ⟨v₀, hv₀⟩ := P.unit
  have hvp : (psiOne (p := p) (A := A) (P := P) 0) ^ p
      ∈ csTowerOne (p := p) (A := A) (P := P) F i :=
    csTowerOne_zero_le (p := p) (A := A) (P := P) F i
      (varpi_pow_mem_CSAlgOne (p := p) (A := A) (P := P) F)
  have hφ : ∀ a : A, AAlgHomLamOne A p (P.ϖ 0) a
      ∈ csTowerOne (p := p) (A := A) (P := P) F i :=
    fun a => csTowerOne_zero_le (p := p) (A := A) (P := P) F i
      (AAlgHomLamOne_mem_CSAlgOne A p (P.ϖ 0) F a)
  have hψ : ∀ n : ℕ, psiOne (p := p) (A := A) (P := P) n
      ∈ csTowerOne (p := p) (A := A) (P := P) F i :=
    fun n => csTowerOne_zero_le (p := p) (A := A) (P := P) F i
      (psiOne_mem_CSAlgOne (p := p) (A := A) (P := P) F n)
  rw [IsFrobModROne, csTowerOne_succ]
  refine sup_le ?_ ?_
  · intro x hx
    rw [mem_frobSubROne]
    obtain ⟨y, hy, c, hc, hxy⟩ := isFrobModROne_cofactor (csTowerOne_zero_le F i) h x hx
    exact ⟨y, le_sup_left (a := csTowerOne (p := p) (A := A) (P := P) F i)
        (b := Subring.closure (csGenOne F (csTowerOne (p := p) (A := A) (P := P) F i))) hy,
      c, le_sup_left (a := csTowerOne (p := p) (A := A) (P := P) F i
            ⊔ Subring.closure (csGenOne F (csTowerOne (p := p) (A := A) (P := P) F i)))
        (b := CSAlgOne A p (P.ϖ 0) F)
        (le_sup_left (a := csTowerOne (p := p) (A := A) (P := P) F i)
          (b := Subring.closure (csGenOne F (csTowerOne (p := p) (A := A) (P := P) F i))) hc),
      hxy⟩
  · refine Subring.closure_le.mpr ?_
    rintro w ⟨v, hv, m, ⟨e, he, hve⟩, rfl⟩
    obtain ⟨v₁, hv₁, c, hc, hvc⟩ := isFrobModROne_cofactor (csTowerOne_zero_le F i) h v hv
    obtain ⟨c', hc', f, hf, hcf⟩ := isFrobModROne_cofactor (csTowerOne_zero_le F i) h c hc
    have hv₁p : v₁ ^ p = v - (psiOne (p := p) (A := A) (P := P) 0) ^ p * c := by
      rw [← hvc]; ring
    have hc'p : c' ^ p = c - (psiOne (p := p) (A := A) (P := P) 0) ^ p * f := by
      rw [← hcf]; ring
    -- `v₁` is admissible at level `m + 1`: `v₁ ^ (p ^ (m+2)) ∈ ϖ ^ p * R`
    have hv₁adm : ∃ e' ∈ csTowerOne (p := p) (A := A) (P := P) F i,
        v₁ ^ (p ^ (m + 2)) = (psiOne (p := p) (A := A) (P := P) 0) ^ p * e' := by
      obtain ⟨h₂, hh₂, hh₂eq⟩ := pow_sub_pow_mem (Fact.out : p.Prime)
        (csTowerOne (p := p) (A := A) (P := P) F i) (m + 1) hv (mul_mem hvp hc)
      have hbin : (v - (psiOne (p := p) (A := A) (P := P) 0) ^ p * c) ^ (p ^ (m + 1))
          = v ^ (p ^ (m + 1))
            - ((psiOne (p := p) (A := A) (P := P) 0) ^ p * c) ^ (p ^ (m + 1))
            + (p : Lam1Loc A p (P.ϖ 0)) * h₂ := by
        rw [← hh₂eq]; ring
      have hX : ((psiOne (p := p) (A := A) (P := P) 0) ^ p * c) ^ (p ^ (m + 1))
          = (psiOne (p := p) (A := A) (P := P) 0) ^ p
            * (((psiOne (p := p) (A := A) (P := P) 0) ^ p) ^ (p ^ (m + 1) - 1)
              * c ^ (p ^ (m + 1))) := by
        have hmul : (psiOne (p := p) (A := A) (P := P) 0) ^ p
              * ((psiOne (p := p) (A := A) (P := P) 0) ^ p) ^ (p ^ (m + 1) - 1)
            = ((psiOne (p := p) (A := A) (P := P) 0) ^ p) ^ (p ^ (m + 1)) := by
          rw [← pow_succ',
            Nat.sub_add_cancel (Nat.one_le_pow (m + 1) p (Fact.out : p.Prime).pos)]
        rw [mul_pow, ← hmul]; ring
      have hp3 : (p : Lam1Loc A p (P.ϖ 0)) * h₂
          = (psiOne (p := p) (A := A) (P := P) 0) ^ p
            * (AAlgHomLamOne A p (P.ϖ 0) (↑(v₀⁻¹) : A) * h₂) := by
        rw [natCast_p_eqOne v₀ hv₀]; ring
      have h3 : v₁ ^ (p ^ (m + 2)) = (v₁ ^ p) ^ (p ^ (m + 1)) := by
        rw [show p ^ (m + 2) = p * p ^ (m + 1) from Nat.pow_succ', pow_mul]
      refine ⟨e - ((psiOne (p := p) (A := A) (P := P) 0) ^ p) ^ (p ^ (m + 1) - 1)
          * c ^ (p ^ (m + 1))
          + AAlgHomLamOne A p (P.ϖ 0) (↑(v₀⁻¹) : A) * h₂, ?_, ?_⟩
      · exact add_mem (sub_mem he (mul_mem (pow_mem hvp _) (pow_mem hc _)))
          (mul_mem (hφ (↑(v₀⁻¹) : A)) hh₂)
      · rw [h3, hv₁p, hbin, hve, hX, hp3]
        ring
    set z : Lam1Loc A p (P.ϖ 0) := v₁ * uPiOne (p := p) (A := A) (P := P) (m + 1)
      with hzdef
    set ε : Lam1Loc A p (P.ϖ 0) :=
      (psiOne (p := p) (A := A) (P := P) (m + 1)) ^ (p ^ (m + 1) - 1) * c' with hεdef
    have hzR : z ∈ csTowerOne (p := p) (A := A) (P := P) F (i + 1) := by
      rw [csTowerOne_succ]
      exact le_sup_right (a := csTowerOne (p := p) (A := A) (P := P) F i)
        (b := Subring.closure (csGenOne F (csTowerOne (p := p) (A := A) (P := P) F i)))
        (Subring.subset_closure ⟨v₁, hv₁, m + 1, hv₁adm, rfl⟩)
    have hεR : ε ∈ csTowerOne (p := p) (A := A) (P := P) F (i + 1) := by
      rw [hεdef, csTowerOne_succ]
      exact mul_mem
        (le_sup_left (a := csTowerOne (p := p) (A := A) (P := P) F i)
          (b := Subring.closure (csGenOne F (csTowerOne (p := p) (A := A) (P := P) F i)))
          (pow_mem (hψ (m + 1)) _))
        (le_sup_left (a := csTowerOne (p := p) (A := A) (P := P) F i)
          (b := Subring.closure (csGenOne F (csTowerOne (p := p) (A := A) (P := P) F i))) hc')
    obtain ⟨h_c, hh_c, hh_ceq⟩ := crossTerm_mem (Fact.out : p.Prime)
      (csTowerOne (p := p) (A := A) (P := P) F (i + 1) ⊔ CSAlgOne A p (P.ϖ 0) F)
      (le_sup_left (a := csTowerOne (p := p) (A := A) (P := P) F (i + 1))
        (b := CSAlgOne A p (P.ϖ 0) F) hzR)
      (le_sup_left (a := csTowerOne (p := p) (A := A) (P := P) F (i + 1))
        (b := CSAlgOne A p (P.ϖ 0) F) hεR)
    refine mem_frobSubROne.mpr ⟨z + ε, add_mem hzR hεR,
      (psiOne (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1) - 1) * f
        - AAlgHomLamOne A p (P.ϖ 0) (↑(v₀⁻¹) : A) * h_c, ?_, ?_⟩
    · refine sub_mem ?_ ?_
      · exact mul_mem (le_sup_right (a := csTowerOne (p := p) (A := A) (P := P) F (i + 1))
          (b := CSAlgOne A p (P.ϖ 0) F)
          (pow_mem (psiOne_mem_CSAlgOne (p := p) (A := A) (P := P) F m) _))
          (le_sup_left (a := csTowerOne (p := p) (A := A) (P := P) F (i + 1))
            (b := CSAlgOne A p (P.ϖ 0) F)
            (csTowerOne_mono F (Nat.le_succ i) hf))
      · exact mul_mem (le_sup_right (a := csTowerOne (p := p) (A := A) (P := P) F (i + 1))
          (b := CSAlgOne A p (P.ϖ 0) F)
          (AAlgHomLamOne_mem_CSAlgOne A p (P.ϖ 0) F _)) hh_c
    · have hz_pow : z ^ p = v * uPiOne (p := p) (A := A) (P := P) m
          - c * (psiOne (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1) - 1) := by
        have h1 : z ^ p = (v - (psiOne (p := p) (A := A) (P := P) 0) ^ p * c)
            * uPiOne (p := p) (A := A) (P := P) m := by
          rw [hzdef, mul_pow, uPiOne_succ_pow m, hv₁p]
        have h2 : (v - (psiOne (p := p) (A := A) (P := P) 0) ^ p * c)
              * uPiOne (p := p) (A := A) (P := P) m
            = v * uPiOne (p := p) (A := A) (P := P) m
              - c * ((psiOne (p := p) (A := A) (P := P) 0) ^ p
                * uPiOne (p := p) (A := A) (P := P) m) := by ring
        rw [h1, h2, varpi_pow_mul_uPiOne m]
      have hε_pow : ε ^ p
          = (psiOne (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1) - 1) * c' ^ p := by
        have hkey : ((psiOne (p := p) (A := A) (P := P) (m + 1)) ^ (p ^ (m + 1) - 1)) ^ p
            = (psiOne (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1) - 1) := by
          rw [← pow_mul, mul_comm, pow_mul, psiOne_succ_pow m]
        rw [hεdef, mul_pow, hkey]
      have hp_eq : (p : Lam1Loc A p (P.ϖ 0)) * h_c
          = (psiOne (p := p) (A := A) (P := P) 0) ^ p
            * (AAlgHomLamOne A p (P.ϖ 0) (↑(v₀⁻¹) : A) * h_c) := by
        rw [natCast_p_eqOne v₀ hv₀]; ring
      have hsum : (z + ε) ^ p = z ^ p + ε ^ p + (p : Lam1Loc A p (P.ϖ 0)) * h_c := by
        linear_combination hh_ceq
      rw [hsum, hz_pow, hε_pow, hc'p, hp_eq]
      ring

end Work.DSM2p
