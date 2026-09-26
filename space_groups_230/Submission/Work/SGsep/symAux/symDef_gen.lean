import Mathlib
import Submission.Work.SGsep.symAux.defs

namespace Work.SGsep.symAux

open Work.SG Work.SGsep
open scoped BigOperators

/-- Multiplying the real vector `v / n²` by the real image of an integer matrix `A` is the same
as dividing the image of `v` under `A` by `n²`. -/
theorem toRMat_mulVec_div_sq (A : IMat) (v : IVec) (n : ℕ) :
    (toRMat A).mulVec (fun c => (v c : ℝ) / ((n : ℝ) ^ 2))
      = fun c => ((A.mulVec v c : ℤ) : ℝ) / ((n : ℝ) ^ 2) := by
  have h1 : (fun c => (v c : ℝ) / ((n : ℝ) ^ 2)) = ((n : ℝ) ^ 2)⁻¹ • toRVec v := by
    funext c; simp [toRVec, div_eq_inv_mul]
  rw [h1, Matrix.mulVec_smul, mulVec_toRVec]
  funext c; simp [toRVec, div_eq_inv_mul]

/-- **Integrality of the symmorphy potential `σ = a.sig / n²` at a generator.**

If `τ_k` takes the tabulated value `z_g / n` at the generator `A = GK k g`, and the integer
divisibility `n² ∣ (σ - A σ) - (o·n)·z_g` holds at every coordinate — which is exactly the
condition `Data.SymCert.chk` checks for the *yes* half — then the defect of `o • τ_k`
relative to the potential `σ = a.sig / n²`,

`symDef k a A = (o • τ_k)(A) - (σ - A σ)`,

is an integer vector, i.e. lies in `ℤ³ = zLat`.

Concretely, at coordinate `c` the defect equals `-(q c)`, where `q c` is the integer quotient
of `(a.sig c - (A a.sig) c) - (o·n)·z_g c` by `n²`. -/
theorem symDef_gen (k : Fin 230) (a : Data.SymCert) (g : ℕ) (hn : 0 < nK k)
    (hval : sgTau k (GK k g) = fun c => ((zK k (geni k g)).toFun c : ℝ) / (nK k : ℝ))
    (hdvd : ∀ c : Fin 3, ((nK k : ℤ)) ^ 2 ∣
        (a.sig.toFun c - ((GK k g).mulVec a.sig.toFun) c)
          - (((a.o : ℤ) * (nK k)) * (zK k (geni k g)).toFun c)) :
    symDef k a (GK k g) ∈ zLat := by
  rw [mem_zLat]
  -- write the divisibility hypothesis as an explicit integer quotient `q`
  choose q hq using hdvd
  refine ⟨fun c => -q c, ?_⟩
  funext c
  simp only [toRVec]
  -- coordinate expression for the defect `symDef`, using the tabulated value of `τ_k`
  have hsymdef : ∀ c : Fin 3,
      symDef k a (GK k g) c
        = (a.o : ℝ) * ((zK k (geni k g)).toFun c : ℝ) / (nK k : ℝ)
          - (a.sig.toFun c : ℝ) / (nK k : ℝ)^2
          + ((GK k g).mulVec a.sig.toFun) c / (nK k : ℝ)^2 := by
    intro c
    rw [symDef]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, symSig]
    have hsigeq : (symSig k a : Fin 3 → ℝ)
        = fun i => (a.sig.toFun i : ℝ) / (nK k : ℝ)^2 := rfl
    rw [hsigeq, hval, toRMat_mulVec_div_sq]
    ring
  have hn2 : (nK k : ℝ)^2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hn.ne')
  -- the real numerator `E` of the defect
  set E : ℝ := (a.sig.toFun c : ℝ) - (((GK k g).mulVec a.sig.toFun) c : ℝ)
      - ((a.o : ℝ) * (nK k : ℝ)) * ((zK k (geni k g)).toFun c : ℝ) with hE_def
  -- `n² q = E`, cast from the integer divisibility
  have hcomb : E = (nK k : ℝ)^2 * (q c : ℝ) := by
    have hcast : ((a.sig.toFun c : ℝ) - (((GK k g).mulVec a.sig.toFun) c : ℝ)
        - ((a.o : ℝ) * (nK k : ℝ)) * ((zK k (geni k g)).toFun c : ℝ))
        = (nK k : ℝ)^2 * (q c : ℝ) := by
      have h := congrArg (fun z : ℤ => (z : ℝ)) (hq c)
      push_cast at h
      simpa using h
    rw [hE_def]; exact hcast
  have hlin : (q c : ℝ) = E / (nK k : ℝ)^2 := by
    rw [eq_div_iff hn2, mul_comm]; exact hcomb.symm
  rw [show ((-q c : ℤ) : ℝ) = -(q c : ℝ) by push_cast; ring]
  rw [hlin, hsymdef c, hE_def]
  field_simp
  ring

end Work.SGsep.symAux
