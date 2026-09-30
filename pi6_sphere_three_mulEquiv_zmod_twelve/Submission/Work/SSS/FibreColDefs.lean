import Mathlib
import Submission.Work.SSS.Packet

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The chain-level model of the left column of the Serre spectral sequence (area SSS)

This file sets up the objects used in the proof of `Work.SSS.fibreCol`: the left-column edge
statement of the convergence of the spectral sequence of a saturated filtration `ξ` of a chain
complex `C` of `ℤ`-modules.

All objects are `ℤ`-submodules of the chains of `C`, of the chains of a filtration term `F_s`, or of
the graded pieces `grF ξ s = F_s/F_{s-1}`.

* `Work.SSS.Fch ξ s n` : the chains of `F_s` in degree `n`, as a submodule of `C_n`.
* `Work.SSS.Zof ξ t`  : the cycles `Z_t(F_0)` of the bottom term, inside `C_t`.
* `Work.SSS.V ξ t s`  : `V_s = ∂(F_s C_{t+1}) ∩ Z_t(F_0)`, the `s`-th step of the left column;
  `V_s/V_{s-1}` is the image of the transgression `d_s`, while
  `E²_{0,t} ≅ Z_t(F_0)/V_1` and `E^∞_{0,t} = Φ_t(0) ≅ Z_t(F_0)/V_{t+1}`.
* `Work.SSS.Zsq ξ s q`, `Work.SSS.Bsq ξ s q` : inside `(F_s/F_{s-1})_{s+q}`, the relative cycles
  whose boundary lifts to `F_{s-2}` and the boundaries coming from `F_{s+1}`; the quotient
  `Zsq/Bsq` is the standard model of `E²_{s,q}` and it injects into `E2 ξ s q`.
* `Work.SSS.Zs ξ t s`, `Work.SSS.Bs ξ t s` : the same objects at total degree `t+1`, for the
  transgression into the left column; `V_s/V_{s-1}` is a quotient of `Zs/Bs`.
-/

set_option autoImplicit false

/- ℤ-modules carry two definitionally distinct `Module ℤ` structures (the structural one and the
canonical one coming from the additive group structure); the canonical one makes the layout of
subtypes and quotients of `ℤ`-modules in this file awkward, so we disable it and use the
structural instances. -/
attribute [-instance] AddCommGroup.toIntModule

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}

/-- The differential `C_a → C_b` of the ambient complex, as a linear map. -/
def dC (C : ChainComplex (ModuleCat ℤ) ℕ) (a b : ℕ) : (C.X a →ₗ[ℤ] C.X b) :=
  (C.d a b).hom

/-- The differential `(F_s)_a → (F_s)_b` of a filtration term, as a linear map. -/
def dFs (ξ : Filtration C) (s a b : ℕ) : ((ξ.F.obj s).X a →ₗ[ℤ] (ξ.F.obj s).X b) :=
  ((ξ.F.obj s).d a b).hom

/-- The linear map `F_{s'} → F_s` for `s' ≤ s`, in degree `n`. -/
def Finc (ξ : Filtration C) (s' s : ℕ) (h : s' ≤ s) (n : ℕ) :
    ((ξ.F.obj s').X n →ₗ[ℤ] (ξ.F.obj s).X n) :=
  ((ξ.F.map (homOfLE h)).f n).hom

/-- The linear map `F_s → C` in degree `n`. -/
def Cincl (ξ : Filtration C) (s n : ℕ) : ((ξ.F.obj s).X n →ₗ[ℤ] C.X n) :=
  ((ξ.incl s).f n).hom

/-- The chains of `F_s` in degree `n`, as a submodule of the chains of `C`. -/
def Fch (ξ : Filtration C) (s n : ℕ) : Submodule ℤ (C.X n) :=
  LinearMap.range (Cincl ξ s n)

@[simp] theorem mem_Fch {ξ : Filtration C} {s n : ℕ} {x : C.X n} :
    x ∈ Fch ξ s n ↔ ∃ y : (ξ.F.obj s).X n, Cincl ξ s n y = x :=
  LinearMap.mem_range

/-- The cycles of `F_0` in degree `t`, inside the chains of `C`.  (`Z_t(F_0)`.) -/
def Zof (ξ : Filtration C) (t : ℕ) : Submodule ℤ (C.X t) :=
  LinearMap.ker (dC C t (t - 1)) ⊓ Fch ξ 0 t

/-- `V_s = ∂(F_sC_{t+1}) ∩ Z_t(F_0)`: the `s`-th step of the left column of the filtration. -/
def V (ξ : Filtration C) (t s : ℕ) : Submodule ℤ (C.X t) :=
  (Submodule.map (dC C (t + 1) t) (Fch ξ s (t + 1))) ⊓ Zof ξ t

/-- The projection `F_s.X n → (grF ξ s).X n = (F_s/F_{s-1})_n`. -/
def projQ (ξ : Filtration C) : (s n : ℕ) → ((ξ.F.obj s).X n →ₗ[ℤ] (grF ξ.F s).X n)
  | 0, _ => 0
  | (s + 1), n => ((cokernel.π (incF ξ.F s)).f n).hom

theorem projQ_succ (ξ : Filtration C) (s n : ℕ) :
    projQ ξ (s + 1) n = ((cokernel.π (incF ξ.F s)).f n).hom := rfl


/-- The chains of `F_s` in degree `n` whose boundary (in `F_s`) lies in `F_0`. -/
def Wrel (ξ : Filtration C) (s n : ℕ) : Submodule ℤ ((ξ.F.obj s).X n) :=
  Submodule.comap (dFs ξ s n (n - 1)) (Submodule.comap (Cincl ξ s (n - 1)) (Fch ξ 0 (n - 1)))

/-! ## The chain-level model of the `E²` page

For `s ≥ 1`, `Zsq ξ s n`, `Bsq ξ s n`, `Zs ξ s n`, `Bs ξ s n` are submodules of the chains
`(F_s/F_{s-1})_n` of the graded piece `grF ξ s` in degree `n`.

* `Zsq`: relative cycles of `F_s` whose boundary lifts to `F_{s-2}` (the model `Z²_{s,n-s}`);
* `Bsq`: the boundaries of chains of `F_{s+1}` that already lie in `F_s` (the model `B²`);
* `Zs` : relative cycles of `F_s` whose boundary lies in `F_0` (so these are cycles of the `E¹`
  row complex, and the transgression `d_s` sends them to the boundary in `Z_t(F_0)`);
* `Bs` : the boundaries of chains of `F_{2s-1}` that already lie in `F_s` (the model `B^s`).
-/

/-- `Zsq ξ s n` is the model `Z²_{s,n-s}`: the classes in `(F_s/F_{s-1})_n` of the chains of `F_s`
whose boundary lifts to `F_{s-2}`. -/
def Zsq (ξ : Filtration C) (s n : ℕ) : Submodule ℤ ((grF ξ.F s).X n) :=
  Submodule.map (projQ ξ s n)
    (Submodule.comap (dFs ξ s n (n - 1))
      (LinearMap.range (Finc ξ (s - 2) s (Nat.sub_le s 2) (n - 1))))

/-- `Bsq ξ s n` is the model `B²_{s,n-s}`: the classes in `(F_s/F_{s-1})_n` of the boundaries of
chains of `F_{s+1}` which already lie in `F_s`. -/
def Bsq (ξ : Filtration C) (s n : ℕ) : Submodule ℤ ((grF ξ.F s).X n) :=
  Submodule.map (projQ ξ s n)
    (Submodule.comap (Finc ξ s (s + 1) (Nat.le_succ s) n)
      (Submodule.map (dFs ξ (s + 1) (n + 1) n)
        (Submodule.comap (dFs ξ (s + 1) (n + 1) n)
          (LinearMap.range (Finc ξ s (s + 1) (Nat.le_succ s) n)))))

/-- `Zs ξ s n` is the model `Z^s_{s,n-s}`: the classes in `(F_s/F_{s-1})_n` of the chains of `F_s`
whose boundary lies in `F_0`. -/
def Zs (ξ : Filtration C) (s n : ℕ) : Submodule ℤ ((grF ξ.F s).X n) :=
  Submodule.map (projQ ξ s n) (Wrel ξ s n)

/-- `Bs ξ s n` is the model `B^s_{s,n-s}`: the classes in `(F_s/F_{s-1})_n` of the boundaries of
chains of `F_{2s-1}` which already lie in `F_s`. -/
def Bs (ξ : Filtration C) (s n : ℕ) : Submodule ℤ ((grF ξ.F s).X n) :=
  Submodule.map (projQ ξ s n)
    (Submodule.comap (Finc ξ s (2 * s - 1) (by omega) n)
      (Submodule.map (dFs ξ (2 * s - 1) (n + 1) n)
        (Submodule.comap (dFs ξ (2 * s - 1) (n + 1) n)
          (LinearMap.range (Finc ξ s (2 * s - 1) (by omega) n)))))

/-! ## `V_{s-1} ⊆ V_s ⊆ Z_t(F_0)` and the model `B`'s as submodules -/

/-- `V_s` as a submodule of `Z_t(F_0)`. -/
def VZ (ξ : Filtration C) (t s : ℕ) : Submodule ℤ ↥(Zof ξ t) :=
  Submodule.comap (Zof ξ t).subtype (V ξ t s)

/-- `V_{s-1}` as a submodule of `V_s`. -/
def VQ (ξ : Filtration C) (t s : ℕ) : Submodule ℤ ↥(V ξ t s) :=
  Submodule.comap (V ξ t s).subtype (V ξ t (s - 1))

/-- `V_{s-1}` as a submodule of `V_s ⊆ Z_t(F_0)`; the quotient `↥(VZ ξ t s) ⧸ VZQ ξ t s` is
`V_s/V_{s-1}`, the image of the transgression `d_s` into the left column. -/
def VZQ (ξ : Filtration C) (t s : ℕ) : Submodule ℤ ↥(VZ ξ t s) :=
  Submodule.comap (VZ ξ t s).subtype (VZ ξ t (s - 1))

/-- `Bsq` as a submodule of the model `Zsq`. -/
def BsqZ (ξ : Filtration C) (s n : ℕ) : Submodule ℤ ↥(Zsq ξ s n) :=
  Submodule.comap (Zsq ξ s n).subtype (Bsq ξ s n)

/-- `Bs` as a submodule of the transgression source `Zs`. -/
def BsZ (ξ : Filtration C) (s n : ℕ) : Submodule ℤ ↥(Zs ξ s n) :=
  Submodule.comap (Zs ξ s n).subtype (Bs ξ s n)


end

end Work.SSS
