import Mathlib
import Submission.Work.LT.Defs

/-! Auxiliary definitions for the relative-property-(T) column lemma
(`Submission/Work/LT/sl3_relT_column.lean`).

We work inside `G = SL₃(ℤ/p)`, with the column subgroup
`U = {u(s,t) = E_ac(s)·E_bc(t) : s,t ∈ ℤ/p} ≅ (ℤ/p)²` and the additive characters
`χ_{u,v}(s,t) = ω^{us+vt}` of `U`, indexed by `(u,v) ∈ (ℤ/p)²`. -/

namespace Work.LT

/-- The additive character `χ_{uv}(st) = ω^{uv.1 * st.1 + uv.2 * st.2}` of `(ℤ/p)²`, with the
character index `uv` first and the group element `st` second. -/
noncomputable def chi (p : ℕ) [NeZero p] (uv st : ZMod p × ZMod p) : ℂ :=
  ZMod.stdAddChar (uv.1 * st.1 + uv.2 * st.2)

/-- The element `u(s,t) = E_ac(s)·E_bc(t)` of the column subgroup `U`. -/
def colU (p : ℕ) (a b c : Fin 3) (st : ZMod p × ZMod p) :
    Matrix.SpecialLinearGroup (Fin 3) (ZMod p) :=
  sl3E p a c st.1 * sl3E p b c st.2

/-- The `χ`-isotypic component of `f` along the column subgroup: the `U`-Fourier coefficient
`(1/p²) ∑_{s,t} conj (χ_{uv}(s,t)) · f (u(s,t) · g)`. -/
noncomputable def fhat (p : ℕ) [NeZero p] (a b c : Fin 3)
    (uv : ZMod p × ZMod p) (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) : ℂ :=
  (∑ st : ZMod p × ZMod p, star (chi p uv st) * f (colU p a b c st * g)) / (p : ℂ) ^ 2

/-- The `U`-average of `f`: `(1/p²) ∑_{s,t} f (u(s,t) · g)`. -/
noncomputable def uavg (p : ℕ) [NeZero p] (a b c : Fin 3)
    (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) : ℂ :=
  (∑ st : ZMod p × ZMod p, f (colU p a b c st * g)) / (p : ℂ) ^ 2

/-- The dual index map for conjugation by `E_ab(k)`: `(u,v) ↦ (u, u k + v)`. -/
def Mab (p : ℕ) (k : ZMod p) (uv : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (uv.1, uv.1 * k + uv.2)

/-- The dual index map for conjugation by `E_ba(k)`: `(u,v) ↦ (u + v k, v)`. -/
def Mba (p : ℕ) (k : ZMod p) (uv : ZMod p × ZMod p) : ZMod p × ZMod p :=
  (uv.1 + uv.2 * k, uv.2)

/-- The `ℓ²`-norm squared of a complex-valued function on a finite type, as a real number. -/
noncomputable def l2sq {X : Type*} [Fintype X] (h : X → ℂ) : ℝ := ∑ x, Complex.normSq (h x)

/-- The `ℓ²`-norm of a complex-valued function on a finite type. -/
noncomputable def l2norm {X : Type*} [Fintype X] (h : X → ℂ) : ℝ := Real.sqrt (l2sq h)


/-- The unnormalised `U`-Fourier coefficient `∑_{s,t} conj (χ_{uv}(s,t)) · f (u(s,t)·g)`
(so that `fhat = fraw / p²`). -/
noncomputable def fraw (p : ℕ) [NeZero p] (a b c : Fin 3)
    (uv : ZMod p × ZMod p) (f : Matrix.SpecialLinearGroup (Fin 3) (ZMod p) → ℂ)
    (g : Matrix.SpecialLinearGroup (Fin 3) (ZMod p)) : ℂ :=
  ∑ st : ZMod p × ZMod p, star (chi p uv st) * f (colU p a b c st * g)

/-- The unnormalised Hermitian pairing `⟪a,b⟫ = ∑ x, conj (a x) * b x` on complex functions. -/
noncomputable def ip {X : Type*} [Fintype X] (a b : X → ℂ) : ℂ := ∑ x, star (a x) * b x

/-- The index map of the dual action of `E_ab(k)`, as a permutation of `(ZMod p)²`. -/
def MabEquiv (p : ℕ) (k : ZMod p) : (ZMod p × ZMod p) ≃ (ZMod p × ZMod p) where
  toFun := Mab p k
  invFun := fun uv => (uv.1, uv.2 - uv.1 * k)
  left_inv := by intro uv; ext <;> simp [Mab]
  right_inv := by intro uv; ext <;> simp [Mab]

/-- The index map of the dual action of `E_ba(k)`, as a permutation of `(ZMod p)²`. -/
def MbaEquiv (p : ℕ) (k : ZMod p) : (ZMod p × ZMod p) ≃ (ZMod p × ZMod p) where
  toFun := Mba p k
  invFun := fun uv => (uv.1 - uv.2 * k, uv.2)
  left_inv := by intro uv; ext <;> simp [Mba]
  right_inv := by intro uv; ext <;> simp [Mba]

end Work.LT
