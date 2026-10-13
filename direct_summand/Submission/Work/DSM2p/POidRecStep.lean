import Submission.Work.DSM2p.POidRec
import Submission.Work.DSM2p.exists_eq_add_varpi_mul_of_pow_mem_CSAlgPos

open scoped Classical

-- The rings `RootAlgPos A p` and `RootAlgLocPos A p ϖ` are built from a quotient of an
-- `MvPolynomial` ring and a localization; the default heartbeat budget is not enough for the
-- instance searches below.
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

namespace Work.DSM2p

universe u

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {P : DSMap.PerfectoidData p A}

/-! ## The invariant is preserved by one tower step -/

/-- **The induction step of `p-oid-rec`.**  If `R = csTower i` is Frobenius-surjective modulo
`ϖ ^ p` (with cofactor in `R`), then so is `csTower (i+1)`.

For the generator `w = v * uPi m` of the step (with `v ^ (p ^ (m+1)) = ϖ ^ p * e`, `e ∈ R`, so
that `w ^ (p ^ (m+1)) = e`) the induction hypothesis gives `v₁ ∈ R` with `v₁ ^ p = v - ϖ ^ p * c`
and `c' ∈ R` with `(c') ^ p = c - ϖ ^ p * f`.  Put `z = v₁ * uPi (m+1) ∈ R'` (the induction
hypothesis is applied at level `m+1` to `v₁`, using `pow_sub_pow_mem`) and
`ε = π_{m+1} ^ (p^(m+1) - 1) * c' ∈ R'`.  Then
`w - (z + ε) ^ p = ϖ ^ p * (π_m ^ (p^(m+1)-1) * f - v⁻¹ * h)`, where `h` is the cross-term
cofactor of `(z, ε)`. -/
theorem isFrobModR_csTower_succ (i : ℕ)
    (h : IsFrobModR (p := p) (A := A) (P := P) (csTower (p := p) (A := A) (P := P) i)) :
    IsFrobModR (p := p) (A := A) (P := P) (csTower (p := p) (A := A) (P := P) (i + 1)) := by
  obtain ⟨v₀, hv₀⟩ := P.unit
  have hvp : (psi (p := p) (A := A) (P := P) 0) ^ p
      ∈ csTower (p := p) (A := A) (P := P) i := csTower_zero_le i varpi_pow_mem_CSAlgPos
  have hφ : ∀ a : A, AAlgHomLocPos A p (P.ϖ 0) a ∈ csTower (p := p) (A := A) (P := P) i :=
    fun a => csTower_zero_le i (AAlgHomLocPos_mem_CSAlgPos A p (P.ϖ 0) a)
  have hψ : ∀ n : ℕ, psi (p := p) (A := A) (P := P) n
      ∈ csTower (p := p) (A := A) (P := P) i :=
    fun n => csTower_zero_le i (psi_mem_CSAlgPos n)
  rw [IsFrobModR, csTower_succ]
  refine sup_le ?_ ?_
  · intro x hx
    rw [mem_frobSubR]
    obtain ⟨y, hy, c, hc, hxy⟩ := isFrobModR_cofactor (csTower_zero_le i) h x hx
    exact ⟨y, le_sup_left (a := csTower (p := p) (A := A) (P := P) i)
        (b := Subring.closure (csGen (csTower (p := p) (A := A) (P := P) i))) hy,
      c, le_sup_left (a := csTower (p := p) (A := A) (P := P) i
            ⊔ Subring.closure (csGen (csTower (p := p) (A := A) (P := P) i)))
        (b := CSAlgPos A p (P.ϖ 0))
        (le_sup_left (a := csTower (p := p) (A := A) (P := P) i)
          (b := Subring.closure (csGen (csTower (p := p) (A := A) (P := P) i))) hc),
      hxy⟩
  · refine Subring.closure_le.mpr ?_
    rintro w ⟨v, hv, m, ⟨e, he, hve⟩, rfl⟩
    obtain ⟨v₁, hv₁, c, hc, hvc⟩ := isFrobModR_cofactor (csTower_zero_le i) h v hv
    obtain ⟨c', hc', f, hf, hcf⟩ := isFrobModR_cofactor (csTower_zero_le i) h c hc
    have hv₁p : v₁ ^ p = v - (psi (p := p) (A := A) (P := P) 0) ^ p * c := by
      rw [← hvc]; ring
    have hc'p : c' ^ p = c - (psi (p := p) (A := A) (P := P) 0) ^ p * f := by
      rw [← hcf]; ring
    -- `v₁` is admissible at level `m + 1`: `v₁ ^ (p ^ (m+2)) ∈ ϖ ^ p * R`
    have hv₁adm : ∃ e' ∈ csTower (p := p) (A := A) (P := P) i,
        v₁ ^ (p ^ (m + 2)) = (psi (p := p) (A := A) (P := P) 0) ^ p * e' := by
      obtain ⟨h₂, hh₂, hh₂eq⟩ := pow_sub_pow_mem (Fact.out : p.Prime)
        (csTower (p := p) (A := A) (P := P) i) (m + 1) hv (mul_mem hvp hc)
      have hbin : (v - (psi (p := p) (A := A) (P := P) 0) ^ p * c) ^ (p ^ (m + 1))
          = v ^ (p ^ (m + 1))
            - ((psi (p := p) (A := A) (P := P) 0) ^ p * c) ^ (p ^ (m + 1))
            + (p : RootAlgLocPos A p (P.ϖ 0)) * h₂ := by
        rw [← hh₂eq]; ring
      have hX : ((psi (p := p) (A := A) (P := P) 0) ^ p * c) ^ (p ^ (m + 1))
          = (psi (p := p) (A := A) (P := P) 0) ^ p
            * (((psi (p := p) (A := A) (P := P) 0) ^ p) ^ (p ^ (m + 1) - 1)
              * c ^ (p ^ (m + 1))) := by
        have hmul : (psi (p := p) (A := A) (P := P) 0) ^ p
              * ((psi (p := p) (A := A) (P := P) 0) ^ p) ^ (p ^ (m + 1) - 1)
            = ((psi (p := p) (A := A) (P := P) 0) ^ p) ^ (p ^ (m + 1)) := by
          rw [← pow_succ',
            Nat.sub_add_cancel (Nat.one_le_pow (m + 1) p (Fact.out : p.Prime).pos)]
        rw [mul_pow, ← hmul]; ring
      have hp3 : (p : RootAlgLocPos A p (P.ϖ 0)) * h₂
          = (psi (p := p) (A := A) (P := P) 0) ^ p
            * (AAlgHomLocPos A p (P.ϖ 0) (↑(v₀⁻¹) : A) * h₂) := by
        rw [natCast_p_eq v₀ hv₀]; ring
      have h3 : v₁ ^ (p ^ (m + 2)) = (v₁ ^ p) ^ (p ^ (m + 1)) := by
        rw [show p ^ (m + 2) = p * p ^ (m + 1) from Nat.pow_succ', pow_mul]
      refine ⟨e - ((psi (p := p) (A := A) (P := P) 0) ^ p) ^ (p ^ (m + 1) - 1)
          * c ^ (p ^ (m + 1))
          + AAlgHomLocPos A p (P.ϖ 0) (↑(v₀⁻¹) : A) * h₂, ?_, ?_⟩
      · exact add_mem (sub_mem he (mul_mem (pow_mem hvp _) (pow_mem hc _)))
          (mul_mem (hφ (↑(v₀⁻¹) : A)) hh₂)
      · rw [h3, hv₁p, hbin, hve, hX, hp3]
        ring
    set z : RootAlgLocPos A p (P.ϖ 0) := v₁ * uPi (p := p) (A := A) (P := P) (m + 1)
      with hzdef
    set ε : RootAlgLocPos A p (P.ϖ 0) :=
      (psi (p := p) (A := A) (P := P) (m + 1)) ^ (p ^ (m + 1) - 1) * c' with hεdef
    have hzR : z ∈ csTower (p := p) (A := A) (P := P) (i + 1) := by
      rw [csTower_succ]
      exact le_sup_right (a := csTower (p := p) (A := A) (P := P) i)
        (b := Subring.closure (csGen (csTower (p := p) (A := A) (P := P) i)))
        (Subring.subset_closure ⟨v₁, hv₁, m + 1, hv₁adm, rfl⟩)
    have hεR : ε ∈ csTower (p := p) (A := A) (P := P) (i + 1) := by
      rw [hεdef, csTower_succ]
      exact mul_mem
        (le_sup_left (a := csTower (p := p) (A := A) (P := P) i)
          (b := Subring.closure (csGen (csTower (p := p) (A := A) (P := P) i)))
          (pow_mem (hψ (m + 1)) _))
        (le_sup_left (a := csTower (p := p) (A := A) (P := P) i)
          (b := Subring.closure (csGen (csTower (p := p) (A := A) (P := P) i))) hc')
    obtain ⟨h_c, hh_c, hh_ceq⟩ := crossTerm_mem (Fact.out : p.Prime)
      (csTower (p := p) (A := A) (P := P) (i + 1) ⊔ CSAlgPos A p (P.ϖ 0))
      (le_sup_left (a := csTower (p := p) (A := A) (P := P) (i + 1))
        (b := CSAlgPos A p (P.ϖ 0)) hzR)
      (le_sup_left (a := csTower (p := p) (A := A) (P := P) (i + 1))
        (b := CSAlgPos A p (P.ϖ 0)) hεR)
    refine mem_frobSubR.mpr ⟨z + ε, add_mem hzR hεR,
      (psi (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1) - 1) * f
        - AAlgHomLocPos A p (P.ϖ 0) (↑(v₀⁻¹) : A) * h_c, ?_, ?_⟩
    · refine sub_mem ?_ ?_
      · exact mul_mem (le_sup_right (a := csTower (p := p) (A := A) (P := P) (i + 1))
          (b := CSAlgPos A p (P.ϖ 0))
          (pow_mem (psi_mem_CSAlgPos (p := p) (A := A) (P := P) m) _))
          (le_sup_left (a := csTower (p := p) (A := A) (P := P) (i + 1))
            (b := CSAlgPos A p (P.ϖ 0))
            (csTower_mono (Nat.le_succ i) hf))
      · exact mul_mem (le_sup_right (a := csTower (p := p) (A := A) (P := P) (i + 1))
          (b := CSAlgPos A p (P.ϖ 0))
          (AAlgHomLocPos_mem_CSAlgPos A p (P.ϖ 0) _)) hh_c
    · have hz_pow : z ^ p = v * uPi (p := p) (A := A) (P := P) m
          - c * (psi (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1) - 1) := by
        have h1 : z ^ p = (v - (psi (p := p) (A := A) (P := P) 0) ^ p * c)
            * uPi (p := p) (A := A) (P := P) m := by
          rw [hzdef, mul_pow, uPi_succ_pow m, hv₁p]
        have h2 : (v - (psi (p := p) (A := A) (P := P) 0) ^ p * c)
              * uPi (p := p) (A := A) (P := P) m
            = v * uPi (p := p) (A := A) (P := P) m
              - c * ((psi (p := p) (A := A) (P := P) 0) ^ p
                * uPi (p := p) (A := A) (P := P) m) := by ring
        rw [h1, h2, varpi_pow_mul_uPi m]
      have hε_pow : ε ^ p
          = (psi (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1) - 1) * c' ^ p := by
        have hkey : ((psi (p := p) (A := A) (P := P) (m + 1)) ^ (p ^ (m + 1) - 1)) ^ p
            = (psi (p := p) (A := A) (P := P) m) ^ (p ^ (m + 1) - 1) := by
          rw [← pow_mul, mul_comm, pow_mul, psi_succ_pow m]
        rw [hεdef, mul_pow, hkey]
      have hp_eq : (p : RootAlgLocPos A p (P.ϖ 0)) * h_c
          = (psi (p := p) (A := A) (P := P) 0) ^ p
            * (AAlgHomLocPos A p (P.ϖ 0) (↑(v₀⁻¹) : A) * h_c) := by
        rw [natCast_p_eq v₀ hv₀]; ring
      have hsum : (z + ε) ^ p = z ^ p + ε ^ p + (p : RootAlgLocPos A p (P.ϖ 0)) * h_c := by
        linear_combination hh_ceq
      rw [hsum, hz_pow, hε_pow, hc'p, hp_eq]
      ring


/-! ## The base case: `A_∞` is Frobenius-surjective modulo `ϖ ^ p` -/

/-- **Base case of `p-oid-rec`.**  The construction ring `A_∞ = CSAlgPos A p ϖ` is
Frobenius-surjective modulo `ϖ ^ p` with cofactor in `A_∞` itself.

Indeed `A_∞ = Λ + ϖ ^ p A_∞` (`exists_rootAlg_add_varpi_pow_mul_decomp`), and the image of
`Λ` is Frobenius-surjective modulo `ϖ ^ p` (`frobSurj_rootClosurePos`). -/
theorem isFrobModR_CSAlgPos :
    IsFrobModR (p := p) (A := A) (P := P) (CSAlgPos A p (P.ϖ 0)) := by
  have hψ : (psi (p := p) (A := A) (P := P) 0) ^ p = iΛT (p := p) (A := A) (P := P)
      (algebraMap A (RootAlgPos A p) (P.ϖ 0 ^ p)) := by
    rw [psi_zero]
    show (AAlgHomLocPos A p (P.ϖ 0) (P.ϖ 0)) ^ p
      = (AAlgHomLocPos A p (P.ϖ 0)) (P.ϖ 0 ^ p)
    exact (map_pow (AAlgHomLocPos A p (P.ϖ 0)) (P.ϖ 0) p).symm
  intro x hx
  obtain ⟨l, y, hy, hxy⟩ := exists_rootAlg_add_varpi_pow_mul_decomp p A (P.ϖ 0) x hx
  obtain ⟨mu, hmu⟩ := frobSurj_rootClosurePos p A P l
  obtain ⟨cc, hcc⟩ := Ideal.mem_span_singleton.mp hmu
  have hϖ : algebraMap A (RootAlgLocPos A p (P.ϖ 0)) (P.ϖ 0)
      = psi (p := p) (A := A) (P := P) 0 :=
    IsScalarTower.algebraMap_apply A (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) (P.ϖ 0)
  rw [hϖ] at hxy
  have hsub : algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) l
        - (algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) mu) ^ p
      = (psi (p := p) (A := A) (P := P) 0) ^ p
        * algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) cc := by
    show iΛT (p := p) (A := A) (P := P) l - (iΛT (p := p) (A := A) (P := P) mu) ^ p
      = (psi (p := p) (A := A) (P := P) 0) ^ p
        * iΛT (p := p) (A := A) (P := P) cc
    have h : iΛT (p := p) (A := A) (P := P) (l - mu ^ p)
        = iΛT (p := p) (A := A) (P := P)
            ((algebraMap A (RootAlgPos A p) (P.ϖ 0 ^ p)) * cc) := by rw [hcc]
    rw [map_sub, map_pow, map_mul] at h
    rw [← hψ] at h
    rw [← h]
  refine mem_frobSubR.mpr ⟨algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) mu,
    iΛT_mem_CSAlgPos mu,
    algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) cc + y,
    add_mem (le_sup_left (a := CSAlgPos A p (P.ϖ 0)) (b := CSAlgPos A p (P.ϖ 0))
      (iΛT_mem_CSAlgPos cc))
      (le_sup_right (a := CSAlgPos A p (P.ϖ 0)) (b := CSAlgPos A p (P.ϖ 0)) hy), ?_⟩
  have hLHS : (algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) l
        + (psi (p := p) (A := A) (P := P) 0) ^ p * y)
      - (algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) mu) ^ p
      = (algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) l
          - (algebraMap (RootAlgPos A p) (RootAlgLocPos A p (P.ϖ 0)) mu) ^ p)
        + (psi (p := p) (A := A) (P := P) 0) ^ p * y := by ring
  rw [hxy, hLHS, hsub]
  ring

theorem isFrobModR_csTower (i : ℕ) :
    IsFrobModR (p := p) (A := A) (P := P) (csTower (p := p) (A := A) (P := P) i) := by
  induction i with
  | zero => exact isFrobModR_CSAlgPos
  | succ k ih => exact isFrobModR_csTower_succ k ih

/-- **`p-oid-rec`, surjectivity half, at every level.**  The union `⋃ Rᵢ` of the tower is
Frobenius-surjective modulo `ϖ ^ p`. -/
theorem isFrobModR_csTowerSup :
    IsFrobModR (p := p) (A := A) (P := P) (csTowerSup (p := p) (A := A) (P := P)) := by
  intro x hx
  obtain ⟨i, hi⟩ := hx
  obtain ⟨y, hy, c, hc, hxy⟩ :=
    mem_frobSubR.mp (isFrobModR_csTower (p := p) (A := A) (P := P) i hi)
  exact mem_frobSubR.mpr ⟨y, le_csTowerSup i hy, c,
    sup_le_sup (le_csTowerSup i) le_rfl hc, hxy⟩

end Work.DSM2p
