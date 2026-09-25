import Mathlib

/-!
# The inhomogeneous cochain complex of continuous functions

For a topological group `Γ` and the discrete coefficient ring `ZMod p`, the *inhomogeneous*
cochain complex of continuous functions is
`ICⁿ(Γ) = { f : (Fin n → Γ) → ZMod p | f continuous }`, with the differential given by the
standard formula for the inhomogeneous cochains of the trivial representation
(`inhomogeneousCochains.d`).

This is the complex whose filtered colimit over the open normal subgroups computes the continuous
cohomology of `Γ` with trivial `𝔽_p` coefficients.

## Main definitions

* `Work.CFTLib.ContCohomology.iCochain p n` — the continuous functions `(Fin n → Γ) → ZMod p`.
* `Work.CFTLib.ContCohomology.iDiff p n` — the differential.
* `Work.CFTLib.ContCohomology.trivRep p Γ` — the trivial `ZMod p`-representation of `Γ`.
-/

noncomputable section

open TopRep

namespace Work.CFTLib.ContCohomology

/-- The trivial `ZMod p`-representation of a topological group `Γ`. -/
abbrev trivRep (p : ℕ) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] :
    TopRep (ZMod p) Γ :=
  TopRep.of (ContRepresentation.trivial (ZMod p) Γ (ZMod p))

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- The map `g ↦ contractNth j (·*·) g` is continuous. -/
lemma continuous_contractNth (n : ℕ) (j : Fin (n+1)) :
    Continuous fun g : Fin (n+1) → Γ => Fin.contractNth j (·*·) g := by
  refine continuous_pi fun k => ?_
  show Continuous fun g : Fin (n+1) → Γ =>
    (if (k:ℕ) < (j:ℕ) then g k.castSucc
      else if (k:ℕ) = (j:ℕ) then g k.castSucc * g k.succ else g k.succ)
  split_ifs
  · exact continuous_apply _
  · exact (continuous_apply _).mul (continuous_apply _)
  · exact continuous_apply _

/-- The continuous map `Fin (n+1) → Γ → Fin n → Γ`, `g ↦ Fin.tail g`. -/
def tailMap (n : ℕ) : C(Fin (n+1) → Γ, Fin n → Γ) :=
  ⟨Fin.tail, continuous_pi fun i => continuous_apply (Fin.succ i)⟩

variable (p : ℕ)

/-- The module of **inhomogeneous `n`-cochains**: continuous functions `(Fin n → Γ) → 𝔽_p`. -/
def iCochain (n : ℕ) : Submodule (ZMod p) ((Fin n → Γ) → ZMod p) where
  carrier := {f | Continuous f}
  zero_mem' := continuous_zero
  add_mem' := by
    intro f₁ f₂ h₁ h₂
    exact h₁.add h₂
  smul_mem' := by
    intro r f h
    exact h.const_smul r

/-- The explicit formula for the inhomogeneous differential. -/
def iDiffFun (n : ℕ) (f : (Fin n → Γ) → ZMod p) : (Fin (n+1) → Γ) → ZMod p :=
  fun g => f (Fin.tail g) +
    ∑ j : Fin (n+1), (-1 : ZMod p) ^ ((j:ℕ)+1) • f (Fin.contractNth j (·*·) g)

@[simp] lemma iDiffFun_apply (n : ℕ) (f : (Fin n → Γ) → ZMod p) (g : Fin (n+1) → Γ) :
    iDiffFun p n f g = f (Fin.tail g) +
      ∑ j : Fin (n+1), (-1 : ZMod p) ^ ((j:ℕ)+1) • f (Fin.contractNth j (·*·) g) := rfl

/-- **The differential of the inhomogeneous complex of continuous functions.** -/
def iDiff (n : ℕ) : ↥(iCochain (Γ := Γ) p n) →ₗ[ZMod p] ↥(iCochain (Γ := Γ) p (n+1)) where
  toFun f := ⟨iDiffFun p n f.1, by
    have h1 : Continuous fun g : Fin (n+1) → Γ => f.1 (Fin.tail g) :=
      f.2.comp (tailMap n).continuous
    have h2 : Continuous fun g : Fin (n+1) → Γ =>
        ∑ j : Fin (n+1), (-1 : ZMod p) ^ ((j:ℕ)+1) • f.1 (Fin.contractNth j (·*·) g) := by
      refine continuous_finsetSum _ fun j _ => ?_
      exact (f.2.comp (continuous_contractNth n j)).const_smul ((-1 : ZMod p) ^ ((j:ℕ)+1))
    exact h1.add h2⟩
  map_add' f g := by
    ext x
    simp only [iDiffFun_apply, Pi.add_apply, Submodule.coe_add, smul_add, Finset.sum_add_distrib]
    ring
  map_smul' r f := by
    ext x
    simp only [iDiffFun_apply, Pi.smul_apply, Submodule.coe_smul, smul_add]
    rw [Finset.smul_sum]
    simp only [RingHom.id_apply]
    ring

@[simp] lemma iDiff_apply (n : ℕ) (f : ↥(iCochain (Γ := Γ) p n)) (g : Fin (n+1) → Γ) :
    (iDiff p n f).1 g = f.1 (Fin.tail g) +
      ∑ j : Fin (n+1), (-1 : ZMod p) ^ ((j:ℕ)+1) • f.1 (Fin.contractNth j (·*·) g) := rfl

/-- The inhomogeneous differential of continuous functions agrees with Mathlib's inhomogeneous
differential of the trivial representation (on the nose). -/
lemma iDiff_eq_d (n : ℕ) (f : ↥(iCochain (Γ := Γ) p n)) :
    (iDiff p n f).1 = (inhomogeneousCochains.d (Rep.trivial (ZMod p) Γ (ZMod p)) n).hom f.1 := by
  funext g
  rw [iDiff_apply, inhomogeneousCochains.d_hom_apply]
  simp only [Fin.tail_def]
  rfl

/-- The differential of the inhomogeneous complex squares to zero (this is inherited from
Mathlib's inhomogeneous cochain complex of the trivial representation). -/
lemma iDiff_comp_iDiff (n : ℕ) (f : ↥(iCochain (Γ := Γ) p n)) :
    iDiff p (n+1) (iDiff p n f) = 0 := by
  apply Subtype.ext
  rw [iDiff_eq_d p (n+1) (iDiff p n f), iDiff_eq_d p n f]
  have h := groupCohomology.inhomogeneousCochains.d_comp_d (k := ZMod p) (G := Γ) n
    (Rep.trivial (ZMod p) Γ (ZMod p))
  have h2 := congrArg (fun ψ => ModuleCat.Hom.hom ψ) h
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h2
  exact congrArg (fun (ψ : ((Fin n → Γ) → ZMod p) →ₗ[ZMod p] ((Fin (n+2) → Γ) → ZMod p)) =>
    ψ f.1) h2

/-- The inhomogeneous complex of continuous functions, as a cochain complex of `ZMod p`-modules. -/
def iComplex : CochainComplex (ModuleCat (ZMod p)) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of (ZMod p) ↥(iCochain (Γ := Γ) p n))
    (fun n => ModuleCat.ofHom (iDiff p n))
    (fun n => by
      ext f x
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
        LinearMap.comp_apply, LinearMap.zero_apply]
      exact congrFun (congrArg Subtype.val (iDiff_comp_iDiff p n f)) x)

end Work.CFTLib.ContCohomology
