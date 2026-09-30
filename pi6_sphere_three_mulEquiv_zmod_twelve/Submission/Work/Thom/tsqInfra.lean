/-
# Infrastructure for the transgression square

This file collects general-purpose lemmas needed for the proof of
`Work.Thom.transgressionSquare` (the compatibility of the Mayer–Vietoris connecting map with the
cup product with a global class).

It is deliberately independent of the specific bundle `Z` of the transgression square: it provides

* the **degree shift** `shK K p` of a cochain complex: the complex with `(shK K p).X k = K.X (k+p)`,
  realised as the Mathlib *restriction* of `K` along the embedding `up ℕ → up ℕ`, `k ↦ k + p` of
  complex shapes (so that all of Mathlib's restriction/homology machinery applies);
* the induced **shifted short complex** `shS S p` and the fact that a shifted short exact sequence
  is short exact;
* the **degree-`p` naturality of the connecting map** (`shS_delta_naturality`): for a morphism
  `φ : S₁ ⟶ shS S₂ p` of short complexes, the connecting maps of `S₁` and of `S₂` are compatible
  through `φ`; this is the `n`-shifted form of `HomologicalComplex.HomologySequence.δ_naturality`.
-/

import Mathlib

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits

namespace Work.Thom

namespace Tsq

/-! ## The shift of a cochain complex -/

/-- The embedding `up ℕ ↪ up ℕ` of complex shapes given by `k ↦ k + p`. -/
abbrev shEmb (p : ℕ) : ComplexShape.Embedding (ComplexShape.up ℕ) (ComplexShape.up ℕ) :=
  ComplexShape.Embedding.mk' _ _ (fun k => k + p) (fun _ _ h => by simpa using h)
    (by intro i j; rw [ComplexShape.up_Rel, ComplexShape.up_Rel]; omega)

instance shEmbRelIff (p : ℕ) : (shEmb p).IsRelIff :=
  ⟨fun i j h => by
    change (i + p) + 1 = j + p at h
    change (i : ℕ) + 1 = j
    omega⟩

instance shEmbTruncGE (p : ℕ) : (shEmb p).IsTruncGE :=
  ⟨fun {j k'} h => ⟨j + 1, by
    change (j + p) + 1 = k' at h
    change (j + 1) + p = k'
    omega⟩⟩

/-- **The degree shift** of a cochain complex of `ℤ`-modules: the complex with
`(shK K p).X k = K.X (k+p)`.  It is the restriction of `K` along the shape embedding
`shEmb p`. -/
noncomputable abbrev shK (K : CochainComplex (ModuleCat ℤ) ℕ) (p : ℕ) :
    CochainComplex (ModuleCat ℤ) ℕ :=
  K.restriction (shEmb p)

@[simp] theorem shK_X (K : CochainComplex (ModuleCat ℤ) ℕ) (p k : ℕ) :
    (shK K p).X k = K.X (k + p) := rfl

@[simp] theorem shK_d (K : CochainComplex (ModuleCat ℤ) ℕ) (p i j : ℕ) :
    (shK K p).d i j = K.d (i + p) (j + p) := rfl

/-- The morphism induced on the shifts by a morphism of complexes. -/
noncomputable abbrev shMap {K L : CochainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (p : ℕ) :
    shK K p ⟶ shK L p :=
  HomologicalComplex.restrictionMap φ (shEmb p)

theorem shMap_id (K : CochainComplex (ModuleCat ℤ) ℕ) (p : ℕ) :
    shMap (𝟙 K) p = 𝟙 (shK K p) :=
  HomologicalComplex.restrictionMap_id K (shEmb p)

theorem shMap_comp {K L M : CochainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (ψ : L ⟶ M) (p : ℕ) :
    shMap (φ ≫ ψ) p = shMap φ p ≫ shMap ψ p :=
  HomologicalComplex.restrictionMap_comp K M φ ψ (shEmb p)

theorem shMap_zero {K L : CochainComplex (ModuleCat ℤ) ℕ} (p : ℕ) :
    shMap (0 : K ⟶ L) p = 0 := by
  ext i
  rfl

@[simp] theorem shMap_f {K L : CochainComplex (ModuleCat ℤ) ℕ} (φ : K ⟶ L) (p k : ℕ) :
    (shMap φ p).f k = φ.f (k + p) := rfl

/-! ## The shift of a short complex -/

/-- **The degree shift of a short complex** of cochain complexes. -/
noncomputable def shS (S : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ)) (p : ℕ) :
    ShortComplex (CochainComplex (ModuleCat ℤ) ℕ) :=
  ShortComplex.mk (shMap S.f p) (shMap S.g p)
    (by rw [← shMap_comp, S.zero, shMap_zero])

@[simp] theorem shS_X₁ (S : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ)) (p : ℕ) :
    (shS S p).X₁ = shK S.X₁ p := rfl

@[simp] theorem shS_X₂ (S : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ)) (p : ℕ) :
    (shS S p).X₂ = shK S.X₂ p := rfl

@[simp] theorem shS_X₃ (S : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ)) (p : ℕ) :
    (shS S p).X₃ = shK S.X₃ p := rfl

@[simp] theorem shS_f (S : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ)) (p : ℕ) :
    (shS S p).f = shMap S.f p := rfl

@[simp] theorem shS_g (S : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ)) (p : ℕ) :
    (shS S p).g = shMap S.g p := rfl

/-- The degreewise evaluation of the shifted short complex is the evaluation at the shifted
degree. -/
theorem shS_map_eval (S : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ)) (p i : ℕ) :
    (shS S p).map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) i)
      = S.map (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) (i + p)) := rfl

/-- **A shifted short exact sequence is short exact.** -/
theorem shS_shortExact (S : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ)) (hS : S.ShortExact)
    (p : ℕ) : (shS S p).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · refine HomologicalComplex.exact_of_degreewise_exact _ (fun i => ?_)
    rw [shS_map_eval]
    exact ShortComplex.Exact.map hS.exact _
  · refine HomologicalComplex.mono_of_mono_f _ (fun i => ?_)
    change Mono ((S.f).f (i + p))
    haveI := hS.mono_f
    infer_instance
  · refine HomologicalComplex.epi_of_epi_f _ (fun i => ?_)
    change Epi ((S.g).f (i + p))
    haveI := hS.epi_g
    infer_instance

/-! ## The homology of the shift

Mathlib's restriction machinery (`HomologicalComplex.restrictionHomologyIso`) identifies the
homology of `shK K p` with that of `K` in the shifted degree. -/

/-- The shift of the shape is stable under "next". -/
theorem shEmb_f_next (p k : ℕ) : (shEmb p).f (k + 1) = (shEmb p).f k + 1 := by
  change (k + 1) + p = k + p + 1
  omega

/-- **The cycles of the shift**: `(shK K p).cycles j` is `K.cycles (j+p)`, for every `j`. -/
noncomputable def shK_cyclesIso (K : CochainComplex (ModuleCat ℤ) ℕ) (p j : ℕ)
    [K.HasHomology (j + p)] : (shK K p).cycles j ≅ K.cycles (j + p) :=
  K.restrictionCyclesIso (shEmb p) j (j + 1)
    (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel j (j + 1) from rfl))
    (by change (j : ℕ) + p = j + p; rfl)
    (by change (j + 1) + p = (j + 1) + p; rfl)
    (by change (ComplexShape.up ℕ).next (j + p) = (j + 1) + p
        exact ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (j + p) ((j + 1) + p) from by
          change j + p + 1 = (j + 1) + p; omega))

/-- **The opcycles of the shift**, away from the boundary: `(shK K p).opcycles j` is
`K.opcycles (j+p)` for `j ≥ 1`. -/
noncomputable def shK_opcyclesIso (K : CochainComplex (ModuleCat ℤ) ℕ) (p j : ℕ) (hj : 1 ≤ j)
    [K.HasHomology (j + p)] : (shK K p).opcycles j ≅ K.opcycles (j + p) :=
  K.restrictionOpcyclesIso (shEmb p) (j - 1) j
    (ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel (j - 1) j from by
      change (j - 1) + 1 = j; omega))
    (by change j - 1 + p = j + p - 1; omega)
    (by change j + p = j + p; rfl)
    (by change (ComplexShape.up ℕ).prev (j + p) = j + p - 1
        exact ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel (j + p - 1) (j + p) from by
          change (j + p - 1) + 1 = j + p; omega))

/-- **The homology of the shift, in the interior of the complex.**  For `k ≥ 1` the `k`-th homology
of `shK K p` is the `(k+p)`-th homology of `K`, via Mathlib's restriction isomorphism. -/
noncomputable def shK_homologyIso (K : CochainComplex (ModuleCat ℤ) ℕ) (p k : ℕ) (hk : 1 ≤ k)
    [K.HasHomology (k + p)] : (shK K p).homology k ≅ K.homology (k + p) :=
  K.restrictionHomologyIso (shEmb p) (k - 1) k (k + 1)
    (ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel (k - 1) k from by
      change (k - 1) + 1 = k; omega))
    (ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel k (k + 1) from rfl))
    (by change k - 1 + p = k + p - 1; omega)
    (by change k + p = k + p; rfl)
    (by change k + 1 + p = k + 1 + p; rfl)
    (by change (ComplexShape.up ℕ).prev (k + p) = k + p - 1
        exact ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel (k + p - 1) (k + p) from by
          change (k + p - 1) + 1 = k + p; omega))
    (by change (ComplexShape.up ℕ).next (k + p) = k + 1 + p
        exact ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel (k + p) (k + 1 + p) from by
          change k + p + 1 = k + 1 + p; omega))

/-! ## Degree-`p` naturality of the connecting map -/

/-- **The degree-`p` naturality of the connecting map.**  A morphism `φ : S₁ ⟶ shS S₂ p` of short
complexes (i.e. a degree-`p` morphism `S₁ ⟶ S₂`) gives a commuting square between the connecting
maps of `S₁` and of `S₂`, the latter read in the shifted degrees. -/
theorem shS_delta_naturality {S₁ S₂ : ShortComplex (CochainComplex (ModuleCat ℤ) ℕ)}
    (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) (p : ℕ) (φ : S₁ ⟶ shS S₂ p)
    (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    hS₁.δ i j hij ≫ HomologicalComplex.homologyMap φ.τ₁ j
      = HomologicalComplex.homologyMap φ.τ₃ i ≫ (shS_shortExact S₂ hS₂ p).δ i j hij :=
  HomologicalComplex.HomologySequence.δ_naturality φ hS₁ (shS_shortExact S₂ hS₂ p) i j hij

end Tsq

end Work.Thom
