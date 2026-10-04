import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Definitions for the splicing lemma for quasilinear parabolic systems

This module collects the objects used in `Submission/Work/Diff/EXT/pde_splice.lean`:

* `SJet n m` — the space of *spatial* `2`-jets of a map `ℝ × ℝⁿ → ℝᵐ` at a point: the value, the
  spatial first derivative and the spatial second derivative.
* `sJet g` — the spatial `2`-jet of `g` as a function of the base point.
* `tderiv g` — the derivative of `g` in the time direction.
* `Aseq Φ a` — the sequence `A₀ = Φ(·,Ju)`, `A_{j+1} = ∂ₜA_j` of time derivatives of the right hand
  side of the equation `∂ₜu = Φ(·,Ju)` evaluated along a function `a`.
* `Seq Φ a` — the sequence `a, A₀, A₁, …`.
* `Psi Φ j` — the universal (recursively defined, `Φ`-dependent, smooth) function expressing
  `∂ₜ^{j}(Φ(·,Ju))` in terms of the spatial `2`-jets of `Ju, J A₀, …, J A_{j-1}`.
-/

namespace Work.Diff.EXT

open scoped ContDiff

/-- The space of *spatial* `2`-jets of a map `ℝ × ℝⁿ → ℝᵐ` at a point. -/
abbrev SJet (n m : ℕ) : Type :=
  (Fin m → ℝ) × ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) ×
    ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))


/-- The jet space is a product of normed spaces.  We register the normed structures explicitly:
`SJet n m` is an abbreviation for a nested product containing second-order continuous linear maps,
and letting typeclass search unfold it on every `fderiv`/`iteratedFDeriv` gives a search explosion.
-/
noncomputable instance instNormedAddCommGroupSJet {n m : ℕ} : NormedAddCommGroup (SJet n m) :=
  inferInstanceAs (NormedAddCommGroup ((Fin m → ℝ) × ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) ×
    ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))))

/-- See `instNormedAddCommGroupSJet`. -/
noncomputable instance instNormedSpaceSJet {n m : ℕ} : NormedSpace ℝ (SJet n m) :=
  inferInstanceAs (NormedSpace ℝ ((Fin m → ℝ) × ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) ×
    ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))))


/-! ### Instances for the jet space

`SJet n m` is an abbreviation for a nested product of continuous linear map spaces.  Letting
typeclass search unfold it when elaborating `deriv`/`fderiv`/`iteratedFDeriv` on jet-valued
functions makes the instance search explode (it explores the ring/module structure of
`E →L F` at length).  We therefore register the normed/algebraic structures of the jet space,
of its two continuous-linear-map components and of their product explicitly and with high
priority, so that typeclass search finds them immediately.

-/
noncomputable instance (priority := 3000) instJetB_AddCommMonoid {n m : ℕ} : AddCommMonoid ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) :=
  inferInstanceAs (AddCommMonoid ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))

noncomputable instance (priority := 3000) instJetB_AddCommGroup {n m : ℕ} : AddCommGroup ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) :=
  inferInstanceAs (AddCommGroup ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))

noncomputable instance (priority := 3000) instJetB_ModuleR {n m : ℕ} : Module ℝ ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) :=
  inferInstanceAs (Module ℝ ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))

noncomputable instance (priority := 3000) instJetB_NormedAddCommGroup {n m : ℕ} : NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) :=
  inferInstanceAs (NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))

noncomputable instance (priority := 3000) instJetB_NormedSpaceR {n m : ℕ} : NormedSpace ℝ ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) :=
  inferInstanceAs (NormedSpace ℝ ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))

noncomputable instance (priority := 3000) instJetC_AddCommMonoid {n m : ℕ} : AddCommMonoid ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ))) :=
  inferInstanceAs (AddCommMonoid ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ))))

noncomputable instance (priority := 3000) instJetC_AddCommGroup {n m : ℕ} : AddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ))) :=
  inferInstanceAs (AddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ))))

noncomputable instance (priority := 3000) instJetC_ModuleR {n m : ℕ} : Module ℝ ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ))) :=
  inferInstanceAs (Module ℝ ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ))))

noncomputable instance (priority := 3000) instJetC_NormedAddCommGroup {n m : ℕ} : NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ))) :=
  inferInstanceAs (NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ))))

noncomputable instance (priority := 3000) instJetC_NormedSpaceR {n m : ℕ} : NormedSpace ℝ ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ))) :=
  inferInstanceAs (NormedSpace ℝ ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ))))

noncomputable instance (priority := 3000) instJetBC_AddCommMonoid {n m : ℕ} : AddCommMonoid (((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) × ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))) :=
  inferInstanceAs (AddCommMonoid (((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) × ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))))

noncomputable instance (priority := 3000) instJetBC_AddCommGroup {n m : ℕ} : AddCommGroup (((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) × ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))) :=
  inferInstanceAs (AddCommGroup (((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) × ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))))

noncomputable instance (priority := 3000) instJetBC_ModuleR {n m : ℕ} : Module ℝ (((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) × ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))) :=
  inferInstanceAs (Module ℝ (((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) × ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))))

noncomputable instance (priority := 3000) instJetBC_NormedAddCommGroup {n m : ℕ} : NormedAddCommGroup (((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) × ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))) :=
  inferInstanceAs (NormedAddCommGroup (((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) × ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))))

noncomputable instance (priority := 3000) instJetBC_NormedSpaceR {n m : ℕ} : NormedSpace ℝ (((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) × ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))) :=
  inferInstanceAs (NormedSpace ℝ (((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)) × ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] (Fin m → ℝ)))))

noncomputable instance (priority := 3000) instSJet_AddCommMonoid {n m : ℕ} : AddCommMonoid (SJet n m) :=
  inferInstanceAs (AddCommMonoid (SJet n m))

noncomputable instance (priority := 3000) instSJet_AddCommGroup {n m : ℕ} : AddCommGroup (SJet n m) :=
  inferInstanceAs (AddCommGroup (SJet n m))

noncomputable instance (priority := 3000) instSJet_ModuleR {n m : ℕ} : Module ℝ (SJet n m) :=
  inferInstanceAs (Module ℝ (SJet n m))

noncomputable instance (priority := 3000) instSJet_NormedAddCommGroup {n m : ℕ} : NormedAddCommGroup (SJet n m) :=
  inferInstanceAs (NormedAddCommGroup (SJet n m))

noncomputable instance (priority := 3000) instSJet_NormedSpaceR {n m : ℕ} : NormedSpace ℝ (SJet n m) :=
  inferInstanceAs (NormedSpace ℝ (SJet n m))

/-- The spatial `2`-jet of a function on `ℝ × ℝⁿ`, as a function of the base point. -/
noncomputable def sJet {n m : ℕ} (g : ℝ × (Fin n → ℝ) → (Fin m → ℝ)) :
    ℝ × (Fin n → ℝ) → SJet n m :=
  fun z => (g z, fderiv ℝ (fun y => g (z.1, y)) z.2,
    fderiv ℝ (fun w => fderiv ℝ (fun y => g (z.1, y)) w) z.2)

/-- The derivative of a function on `ℝ × ℝⁿ` in the time direction. -/
noncomputable def tderiv {n m : ℕ} (g : ℝ × (Fin n → ℝ) → (Fin m → ℝ)) :
    ℝ × (Fin n → ℝ) → (Fin m → ℝ) :=
  fun z => deriv (fun s => g (s, z.2)) z.1

variable {n m : ℕ}

/-- The sequence of time derivatives of the right hand side `Φ(·,Ju)` of the parabolic system
along a function `a`: `Aseq Φ a j` is `∂ₜ^j (Φ(·,J a))`. -/
noncomputable def Aseq (Φ : (Fin n → ℝ) × SJet n m → (Fin m → ℝ))
    (a : ℝ × (Fin n → ℝ) → (Fin m → ℝ)) : ℕ → (ℝ × (Fin n → ℝ) → (Fin m → ℝ))
  | 0 => fun z => Φ (z.2, sJet a z)
  | (j + 1) => tderiv (Aseq Φ a j)

/-- `Seq Φ a 0 = a` and `Seq Φ a (j+1) = Aseq Φ a j`. -/
noncomputable def Seq (Φ : (Fin n → ℝ) × SJet n m → (Fin m → ℝ))
    (a : ℝ × (Fin n → ℝ) → (Fin m → ℝ)) : ℕ → (ℝ × (Fin n → ℝ) → (Fin m → ℝ))
  | 0 => a
  | (j + 1) => Aseq Φ a j

/-- The universal function expressing the time derivative `∂ₜ^j (Φ(·,J u))` through the spatial
`2`-jets of `u, A₀, …, A_{j-1}`.  It is defined by the recursion
`Psi Φ (j+1) (x, ζ) = ∑ᵢ D_{ζᵢ} Psi Φ j (x, ζ₀,…,ζ_{j-1}) (ζ_{i+1})`,
i.e. the derivative of `Psi Φ j` in the direction of the shift `(ζ₁,…,ζ_j)`. -/
noncomputable def Psi (Φ : (Fin n → ℝ) × SJet n m → (Fin m → ℝ)) :
    (j : ℕ) → (Fin n → ℝ) × (Fin (j + 1) → SJet n m) → (Fin m → ℝ)
  | 0 => fun p => Φ (p.1, p.2 0)
  | (j + 1) => fun p =>
      ∑ i : Fin (j + 1),
        (fderiv ℝ (fun q : (Fin n → ℝ) × (Fin (j + 1) → SJet n m) => Psi Φ j q)
          (p.1, fun k => p.2 k.castSucc)) (0, Pi.single i (p.2 i.succ))

end Work.Diff.EXT
