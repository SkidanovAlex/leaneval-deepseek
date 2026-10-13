import Mathlib
import Submission.Work.DSM2p.POidRecOne
import Submission.Work.DSM2p.exists_CSAlgOne_add_varpi_pow_mul_decomp
import Submission.Work.DSM2p.LamOne
import Submission.Work.DSM2p.frobSurj_rootClosurePos
import Submission.Work.DSM2p.isFrobModROne_csTowerOne_succ

/-!
# Frobenius-surjectivity modulo `ϖ ^ p` of the Česnavičius–Scholze tower (one polynomial)

This is the one-variable (`Λ = A[T^{1/p^∞}]`, single polynomial `F`) counterpart of
`Work.DSM2p.isFrobModR_csTowerSup` of `POidRecClosed.lean`: the union `⋃ᵢ Rᵢ` of the tower of
`POidRecOne.lean` — `R₀ = A_∞ = CSAlgOne A p ϖ F`, `R_{i+1} = R_i ⊔ closure (csGenOne F R_i)` —
is Frobenius-surjective modulo `ϖ ^ p`, i.e. every `x ∈ ⋃ᵢ Rᵢ` differs from a `p`-th power of
an element of `⋃ᵢ Rᵢ` by a multiple of `ϖ ^ p` whose cofactor lies in `R ⊔ A_∞`.

The proof has the same three layers as the multi-variable development:

* `isFrobModROne_CSAlgOne` — the base case `R₀ = A_∞ = Λ + ϖ ^ p A_∞`
  (`exists_CSAlgOne_add_varpi_pow_mul_decomp`), where `Λ` is Frobenius-surjective modulo
  `(ϖ ^ p)` (`frobSurj_rootClosure`);
* `isFrobModROne_csTowerOne_succ` (in the imported module) — the invariant is preserved by one
  tower step;
* `isFrobModROne_csTowerOne` — induction on the level, and the target
  `isFrobModROne_csTowerSupOne`, in which the level `i` carrying `x` is chosen by `x ∈ ⋃ᵢ Rᵢ`.
-/

open scoped Classical

namespace Work.DSM2p

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 4000000

/-- **Base case.**  `A_∞ = CSAlgOne A p ϖ F = Λ[F(T)/ϖ ^ m | m]` is Frobenius-surjective modulo
`ϖ ^ p`: by `exists_CSAlgOne_add_varpi_pow_mul_decomp` every `x ∈ A_∞` is `λ + ϖ ^ p y` with
`λ ∈ Λ`, `y ∈ A_∞`, and `λ` is a `p`-th power modulo `ϖ ^ p` by `frobSurj_rootClosure`. -/
theorem isFrobModROne_CSAlgOne (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) :
    IsFrobModROne (p := p) (A := A) (P := P) F (CSAlgOne A p (P.ϖ 0) F) := by
  have hψ : (psiOne (p := p) (A := A) (P := P) 0) ^ p
      = iΛTOne A p (P.ϖ 0) (algebraMap A (Lam1 A p) (P.ϖ 0 ^ p)) := by
    rw [psiOne_zero]
    show (AAlgHomLamOne A p (P.ϖ 0) (P.ϖ 0)) ^ p
      = (AAlgHomLamOne A p (P.ϖ 0)) (P.ϖ 0 ^ p)
    exact (map_pow (AAlgHomLamOne A p (P.ϖ 0)) (P.ϖ 0) p).symm
  intro x hx
  obtain ⟨l, y, hy, hxy⟩ := exists_CSAlgOne_add_varpi_pow_mul_decomp p A (P.ϖ 0) F x hx
  obtain ⟨mu, hmu⟩ := frobSurj_rootClosure p A P PUnit l
  obtain ⟨cc, hcc⟩ := Ideal.mem_span_singleton.mp hmu
  have hϖ : algebraMap A (Lam1Loc A p (P.ϖ 0)) (P.ϖ 0)
      = psiOne (p := p) (A := A) (P := P) 0 :=
    IsScalarTower.algebraMap_apply A (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) (P.ϖ 0)
  rw [hϖ] at hxy
  have hsub : algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) l
        - (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) mu) ^ p
      = (psiOne (p := p) (A := A) (P := P) 0) ^ p
        * algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) cc := by
    show iΛTOne A p (P.ϖ 0) l - (iΛTOne A p (P.ϖ 0) mu) ^ p
      = (psiOne (p := p) (A := A) (P := P) 0) ^ p * iΛTOne A p (P.ϖ 0) cc
    have h : iΛTOne A p (P.ϖ 0) (l - mu ^ p)
        = iΛTOne A p (P.ϖ 0) ((algebraMap A (Lam1 A p) (P.ϖ 0 ^ p)) * cc) := by rw [hcc]
    rw [map_sub, map_pow, map_mul] at h
    rw [← hψ] at h
    rw [← h]
  refine mem_frobSubROne.mpr ⟨algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) mu,
    iΛTOne_mem_CSAlgOne A p (P.ϖ 0) F mu,
    algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) cc + y,
    add_mem (le_sup_left (a := CSAlgOne A p (P.ϖ 0) F) (b := CSAlgOne A p (P.ϖ 0) F)
      (iΛTOne_mem_CSAlgOne A p (P.ϖ 0) F cc))
      (le_sup_right (a := CSAlgOne A p (P.ϖ 0) F) (b := CSAlgOne A p (P.ϖ 0) F) hy), ?_⟩
  have hLHS : (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) l
        + (psiOne (p := p) (A := A) (P := P) 0) ^ p * y)
      - (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) mu) ^ p
      = (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) l
          - (algebraMap (Lam1 A p) (Lam1Loc A p (P.ϖ 0)) mu) ^ p)
        + (psiOne (p := p) (A := A) (P := P) 0) ^ p * y := by ring
  rw [hxy, hLHS, hsub]
  ring

/-- **The invariant holds at every level of the tower**, by induction using the base case
`isFrobModROne_CSAlgOne` and the step `isFrobModROne_csTowerOne_succ`. -/
theorem isFrobModROne_csTowerOne (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) (i : ℕ) :
    IsFrobModROne (p := p) (A := A) (P := P) F (csTowerOne (p := p) (A := A) (P := P) F i) := by
  induction i with
  | zero => exact isFrobModROne_CSAlgOne A p P F
  | succ k ih => exact isFrobModROne_csTowerOne_succ A p P F k ih

/-- **`p-oid-rec`, surjectivity half, for the one-polynomial Česnavičius–Scholze tower.**  The
union `⋃ᵢ Rᵢ = csTowerSupOne F` of the tower is Frobenius-surjective modulo `ϖ ^ p`: an element
`x` lies in some level `Rᵢ`, the invariant at level `i` produces `y ∈ Rᵢ` and a cofactor
`c ∈ Rᵢ ⊔ A_∞`, and both are pushed into the union. -/
theorem isFrobModROne_csTowerSupOne (A : Type*) [CommRing A] (p : ℕ) [Fact p.Prime]
    (P : DSMap.PerfectoidData p A) (F : Polynomial A) :
    IsFrobModROne (p := p) (A := A) (P := P) F (csTowerSupOne (p := p) (A := A) (P := P) F) := by
  intro x hx
  obtain ⟨i, hi⟩ := hx
  obtain ⟨y, hy, c, hc, hxy⟩ := mem_frobSubROne.mp (isFrobModROne_csTowerOne A p P F i hi)
  exact mem_frobSubROne.mpr ⟨y, le_csTowerSupOne F i hy, c,
    sup_le_sup (le_csTowerSupOne F i) le_rfl hc, hxy⟩

end Work.DSM2p
