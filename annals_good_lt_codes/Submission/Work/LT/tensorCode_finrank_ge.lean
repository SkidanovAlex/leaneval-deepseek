import Mathlib
import Submission.Work.LT.Defs
import Submission.Work.LT.linearIndependent_kronecker

namespace Work.LT

/-- The Kronecker word `(i,j) ↦ a i * b j` of a codeword `a ∈ CA` and a codeword `b ∈ CB` lies in
the tensor code `CA ⊗ CB`: every row is a scalar multiple of `b`, every column a scalar multiple
of `a`. -/
lemma tensorCode_kron_mem {Δ : ℕ} {CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)}
    (a : CA) (b : CB) :
    (fun ij : Fin Δ × Fin Δ => (a : Fin Δ → ZMod 2) ij.1 * (b : Fin Δ → ZMod 2) ij.2) ∈
      tensorCode CA CB := by
  rw [tensorCode, Submodule.mem_inf]
  constructor
  · rw [Submodule.mem_iInf]
    intro i
    rw [Submodule.mem_comap]
    have hw : (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun j : Fin Δ => (i, j)))
        (fun ij : Fin Δ × Fin Δ => (a : Fin Δ → ZMod 2) ij.1 * (b : Fin Δ → ZMod 2) ij.2)
        = ((a : Fin Δ → ZMod 2) i) • (b : Fin Δ → ZMod 2) := by
      funext j
      rw [LinearMap.funLeft_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
    rw [hw]
    exact Submodule.smul_mem _ _ b.2
  · rw [Submodule.mem_iInf]
    intro j
    rw [Submodule.mem_comap]
    have hw : (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun i : Fin Δ => (i, j)))
        (fun ij : Fin Δ × Fin Δ => (a : Fin Δ → ZMod 2) ij.1 * (b : Fin Δ → ZMod 2) ij.2)
        = ((b : Fin Δ → ZMod 2) j) • (a : Fin Δ → ZMod 2) := by
      funext i
      rw [LinearMap.funLeft_apply]
      simp only [Pi.smul_apply, smul_eq_mul, mul_comm]
    rw [hw]
    exact Submodule.smul_mem _ _ a.2

/-- The tensor code `CA ⊗ CB` (rows in `CB`, columns in `CA`) has dimension at least
`dim CA * dim CB`: the rank-one words `(i,j) ↦ a i * b j` for `a ∈ CA`, `b ∈ CB` lie in it and
are linearly independent. -/
lemma tensorCode_finrank_ge {Δ : ℕ} (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) :
    Module.finrank (ZMod 2) CA * Module.finrank (ZMod 2) CB ≤
      Module.finrank (ZMod 2) (tensorCode CA CB) := by
  let bA : Module.Basis (Fin (Module.finrank (ZMod 2) CA)) (ZMod 2) CA := Module.finBasis (ZMod 2) CA
  let bB : Module.Basis (Fin (Module.finrank (ZMod 2) CB)) (ZMod 2) CB := Module.finBasis (ZMod 2) CB
  have hA : LinearIndependent (ZMod 2) (fun i => ((bA i : CA) : Fin Δ → ZMod 2)) :=
    bA.linearIndependent.map' (Submodule.subtype CA) (Submodule.ker_subtype CA)
  have hB : LinearIndependent (ZMod 2) (fun j => ((bB j : CB) : Fin Δ → ZMod 2)) :=
    bB.linearIndependent.map' (Submodule.subtype CB) (Submodule.ker_subtype CB)
  have hk := linearIndependent_kronecker
    (u := fun i => ((bA i : CA) : Fin Δ → ZMod 2))
    (v := fun j => ((bB j : CB) : Fin Δ → ZMod 2)) hA hB
  let v : Fin (Module.finrank (ZMod 2) CA) × Fin (Module.finrank (ZMod 2) CB) → tensorCode CA CB :=
    fun p => ⟨fun ij : Fin Δ × Fin Δ =>
        (bA p.1 : Fin Δ → ZMod 2) ij.1 * (bB p.2 : Fin Δ → ZMod 2) ij.2,
      tensorCode_kron_mem (bA p.1) (bB p.2)⟩
  have hfun : ((Submodule.subtype (tensorCode CA CB)) ∘ v)
      = (fun p : Fin (Module.finrank (ZMod 2) CA) × Fin (Module.finrank (ZMod 2) CB) =>
          fun ij : Fin Δ × Fin Δ =>
            (bA p.1 : Fin Δ → ZMod 2) ij.1 * (bB p.2 : Fin Δ → ZMod 2) ij.2) := by
    funext p
    rfl
  have hv : LinearIndependent (ZMod 2) v := by
    rw [← hfun] at hk
    exact LinearIndependent.of_comp (Submodule.subtype (tensorCode CA CB)) hk
  have hcard := hv.fintype_card_le_finrank
  simpa [Fintype.card_prod] using hcard

end Work.LT
